use backend::*;
use lean_vm::*;
use leansig_wrapper::{XmssPublicKey, XmssSignature};
use serde::{Deserialize, Serialize};
use std::io::{self, Write};
use std::time::Instant;
use utils::ansi as s;

use crate::compilation::{get_aggregation_bytecode, init_aggregation_bytecode};
use crate::multi_message_aggregation::{
    MultiMessageAggregateSignature, merge_single_message_aggregates, split_multi_message_aggregate,
    verify_multi_message_aggregate,
};
use crate::signatures_cache::{BENCHMARK_SLOT, get_benchmark_signatures, message_for_benchmark};
use crate::single_message_aggregation::{
    SingleMessageAggregateSignature, aggregate_single_message_signatures, verify_single_message_aggregate,
};

#[derive(Debug, Clone)]
pub struct AggregationTopology {
    pub raw_xmss: usize,
    pub children: Vec<AggregationTopology>,
    pub log_inv_rate: usize,
    pub overlap: usize, // Ignored for leaves.
}

pub fn biggest_leaf(topology: &AggregationTopology) -> Option<AggregationTopology> {
    fn visit(t: &AggregationTopology, best: &mut Option<(usize, usize)>) {
        if t.raw_xmss > 0 && best.is_none_or(|(n, _)| t.raw_xmss > n) {
            *best = Some((t.raw_xmss, t.log_inv_rate));
        }
        for c in &t.children {
            visit(c, best);
        }
    }
    let mut best = None;
    visit(topology, &mut best);
    best.map(|(raw_xmss, log_inv_rate)| AggregationTopology {
        raw_xmss,
        children: vec![],
        log_inv_rate,
        overlap: 0,
    })
}

pub(crate) fn count_signers(topology: &AggregationTopology) -> usize {
    let child_count: usize = topology.children.iter().map(count_signers).sum();
    let n_overlaps = topology.children.len().saturating_sub(1);
    topology.raw_xmss + child_count - topology.overlap * n_overlaps
}

fn count_nodes(topology: &AggregationTopology) -> usize {
    1 + topology.children.iter().map(count_nodes).sum::<usize>()
}

#[derive(Default, Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum NodeKind {
    #[default]
    AggregateSingleMessage,
    MergeSingleMessages,
    SplitMultiMessage,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NodeStats {
    pub time_secs: f64,
    /// 95% confidence interval half-width on `time_secs`. Zero when only one sample was taken.
    #[serde(default)]
    pub time_ci_secs: f64,
    #[serde(default = "default_samples")]
    pub samples: usize,
    pub proof_kib: usize,
    pub cycles: usize,
    pub memory: usize,
    pub poseidons: usize,
    pub dots: usize,
    pub n_xmss: Option<usize>,
    #[serde(default)]
    pub kind: NodeKind,
}

fn default_samples() -> usize {
    1
}

fn t_critical_95(df: usize) -> f64 {
    if df == 0 {
        return f64::INFINITY;
    }
    let z = 1.959964_f64;
    let df = df as f64;
    z + (z.powi(3) + z) / (4.0 * df) + (5.0 * z.powi(5) + 16.0 * z.powi(3) + 3.0 * z) / (96.0 * df.powi(2))
}

/// Returns (mean, 95% CI half-width). Half-width is 0 when n < 2.
fn mean_and_ci(samples: &[f64]) -> (f64, f64) {
    let n = samples.len();
    let mean = samples.iter().sum::<f64>() / n as f64;
    if n < 2 {
        return (mean, 0.0);
    }
    let variance = samples.iter().map(|x| (x - mean).powi(2)).sum::<f64>() / (n - 1) as f64;
    let std_err = variance.sqrt() / (n as f64).sqrt();
    (mean, t_critical_95(n - 1) * std_err)
}

const TIME_COL_WIDTH: usize = 20;
const CI_COL_WIDTH: usize = 8;

fn fmt_throughput_col(n: usize, st: &NodeStats) -> String {
    let throughput = n as f64 / st.time_secs;
    format!(
        "{:>w$}",
        format!("{:.0} XMSS/s - {:.3}s", throughput, st.time_secs),
        w = TIME_COL_WIDTH
    )
}

fn fmt_time_col(st: &NodeStats) -> String {
    format!("{:>w$}", format!("{:.3}s", st.time_secs), w = TIME_COL_WIDTH)
}

fn fmt_ci_col(st: &NodeStats) -> String {
    if st.samples > 1 {
        format!("± {:.1}%", 100.0 * st.time_ci_secs / st.time_secs)
    } else {
        String::new()
    }
}

/// `path` is the topology-relative path from the root (`[]` = root)
#[derive(Clone, Debug, Serialize, Deserialize)]
pub struct NodeReport {
    pub path: Vec<usize>,
    pub stats: NodeStats,
}

/// Per-node metrics in tree-walk order.
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct BenchmarkReport {
    pub nodes: Vec<NodeReport>,
}

impl BenchmarkReport {
    pub fn total_time_secs(&self) -> f64 {
        self.nodes.iter().map(|n| n.stats.time_secs).sum()
    }
}

struct LiveTree {
    descs: Vec<String>,
    plain_lens: Vec<usize>,
    max_plain_len: usize,
    statuses: Vec<Option<NodeStats>>,
    n_nodes: usize,
    silent: bool,
    show_ci_col: bool,
}

impl LiveTree {
    fn new(descs: Vec<String>, plain_lens: Vec<usize>, silent: bool, show_ci_col: bool) -> Self {
        let max_plain_len = plain_lens.iter().copied().max().unwrap_or(0);
        let n_nodes = descs.len();
        Self {
            descs,
            plain_lens,
            max_plain_len,
            statuses: vec![None; n_nodes],
            n_nodes,
            silent,
            show_ci_col,
        }
    }

    fn ci_header_fragment(&self) -> String {
        if self.show_ci_col {
            format!("  {:>w$}", "± %", w = CI_COL_WIDTH)
        } else {
            String::new()
        }
    }

    fn ci_cell(&self, st: &NodeStats) -> String {
        if self.show_ci_col {
            format!("  {}{:>w$}{}", s::PUR, fmt_ci_col(st), s::R, w = CI_COL_WIDTH)
        } else {
            String::new()
        }
    }

    fn header(&self) -> String {
        let pad = self.max_plain_len + 6; // desc + dots + " ▸ "
        let spacer = " ".repeat(pad);
        format!(
            "{}{}{:>w$}  {:>8}{}  {:>10}  {:>10}  {:>10}  {:>10}{}",
            s::D,
            spacer,
            "time",
            "size",
            self.ci_header_fragment(),
            "cycles",
            "memory",
            "poseidons",
            "extension-ops",
            s::R,
            w = TIME_COL_WIDTH,
        )
    }

    fn format_line(&self, i: usize) -> String {
        let desc = &self.descs[i];
        let gap = self.max_plain_len + 2 - self.plain_lens[i];
        let dots = format!("{}{}{}", s::DRK, "·".repeat(gap), s::R);
        match &self.statuses[i] {
            None => desc.to_string(),
            Some(st) => {
                let time_col_text = match st.n_xmss {
                    Some(n) => fmt_throughput_col(n, st),
                    None => fmt_time_col(st),
                };
                let time_col = format!("{}{}{}{}", s::ORG, s::B, time_col_text, s::R);
                format!(
                    "{} {} {}▸{} {}  {}{}{:>4} KiB{}{}  {}{:>10}{}  {}{:>10}{}  {}{:>10}{}  {}{:>10}{}",
                    desc,
                    dots,
                    s::DRK,
                    s::R,
                    time_col,
                    s::CYN,
                    s::B,
                    st.proof_kib,
                    s::R,
                    self.ci_cell(st),
                    s::WHT,
                    pretty_integer(st.cycles),
                    s::R,
                    s::WHT,
                    pretty_integer(st.memory),
                    s::R,
                    s::WHT,
                    pretty_integer(st.poseidons),
                    s::R,
                    s::WHT,
                    pretty_integer(st.dots),
                    s::R,
                )
            }
        }
    }

    fn print_initial(&self) {
        if self.silent {
            return;
        }
        println!("{}", self.header());
        for i in 0..self.n_nodes {
            println!("{}", self.format_line(i));
        }
        println!();
        io::stdout().flush().unwrap();
    }

    fn update_node(&mut self, index: usize, stats: &NodeStats) {
        self.statuses[index] = Some(stats.clone());
        if self.silent {
            return;
        }
        let line = self.format_line(index);
        let up = self.n_nodes + 1 - index;
        print!("\x1b[{}A\r\x1b[2K{}\x1b[{}B\r", up, line, up);
        io::stdout().flush().unwrap();
    }
}

fn print_stage(silent: bool, label: &str, stats: &NodeStats) {
    if silent {
        return;
    }
    let xmss_tag = stats.n_xmss.map(|n| format!(" n_xmss={}", n)).unwrap_or_default();
    println!(
        "{:30} {:>8.3}s {:>5} KiB cycles={:>10}{}",
        label,
        stats.time_secs,
        stats.proof_kib,
        pretty_integer(stats.cycles),
        xmss_tag,
    );
}

#[allow(clippy::too_many_arguments)]
fn build_tree_descs(
    topology: &AggregationTopology,
    prefix: &str,
    child_prefix: &str,
    plain_prefix: &str,
    plain_child_prefix: &str,
    descs: &mut Vec<String>,
    plain_lens: &mut Vec<usize>,
) {
    let n_sigs = count_signers(topology);
    let n_children = topology.children.len();
    let is_leaf = n_children == 0;

    let (icon, icon_color) = if is_leaf { ("◇", s::ORG) } else { ("◆", s::PUR) };
    let reduced = if n_children > 1 {
        topology.overlap * (n_children - 1)
    } else {
        0
    };
    let children_sum: usize = topology.children.iter().map(count_signers).sum();
    let detail = if is_leaf {
        format!("{}{}{}", s::GRN, n_sigs, s::R)
    } else {
        let mut parts: Vec<String> = vec![];
        if children_sum > 0 {
            parts.push(format!("{}{}{}", s::GRN, children_sum, s::R));
        }
        if topology.raw_xmss > 0 {
            parts.push(format!("{}+ {}{}", s::GRN, topology.raw_xmss, s::R));
        }
        if reduced > 0 {
            parts.push(format!("{}- {}{}", s::RED, reduced, s::R));
        }
        parts.join(" ")
    };
    let plain_detail = if is_leaf {
        format!("{}", n_sigs)
    } else {
        let mut parts: Vec<String> = vec![];
        if children_sum > 0 {
            parts.push(format!("{}", children_sum));
        }
        if topology.raw_xmss > 0 {
            parts.push(format!("+ {}", topology.raw_xmss));
        }
        if reduced > 0 {
            parts.push(format!("- {}", reduced));
        }
        parts.join(" ")
    };

    // Children first (above), so leaves print at the top and proving flows top → bottom.
    for (i, child) in topology.children.iter().enumerate() {
        let is_first = i == 0;
        let (p, cp, pp, pcp) = if is_first {
            (
                format!("{}{}┌──▸{} ", child_prefix, s::PUR, s::R),
                format!("{}     ", child_prefix),
                format!("{}┌──▸ ", plain_child_prefix),
                format!("{}     ", plain_child_prefix),
            )
        } else {
            (
                format!("{}{}├──▸{} ", child_prefix, s::PUR, s::R),
                format!("{}{}│   {} ", child_prefix, s::PUR, s::R),
                format!("{}├──▸ ", plain_child_prefix),
                format!("{}│    ", plain_child_prefix),
            )
        };
        build_tree_descs(child, &p, &cp, &pp, &pcp, descs, plain_lens);
    }

    // Then the node itself (below its children).
    let inv_rate = 1 << topology.log_inv_rate;
    let rate_tag = format!(" {}R=1/{}{}", s::D, inv_rate, s::R);
    let plain_rate_tag = format!(" R=1/{}", inv_rate);
    let desc = format!("{}{}{}{} {}{}", prefix, icon_color, icon, s::R, detail, rate_tag,);
    let plain = format!("{}{} {}{}", plain_prefix, icon, plain_detail, plain_rate_tag);
    plain_lens.push(plain.chars().count());
    descs.push(desc);
}

#[allow(clippy::too_many_arguments)]
fn build_aggregation(
    topology: &AggregationTopology,
    display_index: usize,
    nodes: &mut Vec<NodeReport>,
    live_tree: &mut LiveTree,
    path: &mut Vec<usize>,
    pub_keys: &[XmssPublicKey],
    signatures: &[XmssSignature],
    tracing: bool,
    is_root: bool,
    repeat: usize,
) -> SingleMessageAggregateSignature {
    let raw_count = topology.raw_xmss;
    let raw_xmss: Vec<(XmssPublicKey, XmssSignature)> = (0..raw_count)
        .map(|i| (pub_keys[i].clone(), signatures[i].clone()))
        .collect();

    let mut children: Vec<SingleMessageAggregateSignature> = vec![];
    let mut child_start = raw_count;
    let mut child_display_index = display_index;
    for (child_idx, child) in topology.children.iter().enumerate() {
        let child_count = count_signers(child);
        path.push(child_idx);
        let child_sig = build_aggregation(
            child,
            child_display_index,
            nodes,
            live_tree,
            path,
            &pub_keys[child_start..child_start + child_count],
            &signatures[child_start..child_start + child_count],
            tracing,
            false,
            repeat,
        );
        path.pop();
        children.push(child_sig);
        child_display_index += count_nodes(child);
        child_start += child_count;
        if child_idx < topology.children.len() - 1 {
            child_start -= topology.overlap;
        }
    }

    if tracing && is_root {
        utils::init_tracing();
    }

    assert!(repeat > 0);
    let is_leaf = topology.children.is_empty();
    let mut times = Vec::with_capacity(repeat);
    let mut last_result: Option<SingleMessageAggregateSignature> = None;
    let own_display_index = display_index + count_nodes(topology) - 1;
    for _ in 0..repeat {
        #[cfg(not(feature = "standard-alloc"))]
        zk_alloc::begin_phase();

        let time = Instant::now();
        let result = aggregate_single_message_signatures(
            &children,
            raw_xmss.clone(),
            message_for_benchmark(),
            BENCHMARK_SLOT,
            topology.log_inv_rate,
        )
        .unwrap();
        let elapsed = time.elapsed();

        // Clone the outputs out of the arena before the next phase resets its slabs.
        #[cfg(not(feature = "standard-alloc"))]
        let result = {
            zk_alloc::end_phase();
            result.clone()
        };

        times.push(elapsed.as_secs_f64());
        last_result = Some(result);

        if !tracing && repeat > 1 {
            let r = last_result.as_ref().unwrap();
            let meta = r.proof.metadata.as_ref().unwrap();
            let proof_kib = r.proof.proof.proof_size_fe() * F::bits() / (8 * 1024);
            let (mean, ci) = mean_and_ci(&times);
            live_tree.update_node(
                own_display_index,
                &NodeStats {
                    time_secs: mean,
                    time_ci_secs: ci,
                    samples: times.len(),
                    proof_kib,
                    cycles: meta.cycles,
                    memory: meta.memory,
                    poseidons: meta.n_poseidons,
                    dots: meta.n_extension_ops,
                    n_xmss: if is_leaf { Some(topology.raw_xmss) } else { None },
                    kind: NodeKind::AggregateSingleMessage,
                },
            );
        }
    }

    let result = last_result.unwrap();
    let (mean_time, time_ci) = mean_and_ci(&times);
    let meta = result.proof.metadata.as_ref().unwrap();
    let proof_kib = result.proof.proof.proof_size_fe() * F::bits() / (8 * 1024);

    if tracing {
        println!("{}", meta.display());
        if is_leaf {
            println!(
                "{} XMSS/s (avg over {} run{})",
                (topology.raw_xmss as f64 / mean_time).round() as usize,
                repeat,
                if repeat == 1 { "" } else { "s" }
            );
        } else {
            println!(
                "{:.3}s the final aggregation step (avg over {} run{})",
                mean_time,
                repeat,
                if repeat == 1 { "" } else { "s" }
            );
        }
        println!("Proof size: {} KiB", proof_kib);
    }

    let stats = NodeStats {
        time_secs: mean_time,
        time_ci_secs: time_ci,
        samples: repeat,
        proof_kib,
        cycles: meta.cycles,
        memory: meta.memory,
        poseidons: meta.n_poseidons,
        dots: meta.n_extension_ops,
        n_xmss: if is_leaf { Some(topology.raw_xmss) } else { None },
        kind: NodeKind::AggregateSingleMessage,
    };
    if !tracing {
        live_tree.update_node(own_display_index, &stats);
    }
    nodes.push(NodeReport {
        path: path.clone(),
        stats,
    });

    result
}

pub fn run_aggregation_benchmark(
    topology: &AggregationTopology,
    tracing: bool,
    silent: bool,
    repeat: usize,
) -> BenchmarkReport {
    // Tell macOS this is a user-initiated, latency-critical computation and
    // should not be throttled / App-Napped.
    #[cfg(target_os = "macos")]
    let _activity = macos_activity::Activity::begin("lean-multisig benchmark");

    precompute_dft_twiddles::<F>(1 << 24);

    let n_sigs = count_signers(topology);

    let cache = get_benchmark_signatures();
    assert!(cache.len() >= n_sigs);
    let (pub_keys, signatures): (Vec<_>, Vec<_>) = cache[..n_sigs].iter().cloned().unzip();

    init_aggregation_bytecode();

    if !silent {
        println!(
            "Aggregation program: {} instructions\n",
            pretty_integer(get_aggregation_bytecode().unpadded_size)
        );
    }

    // Build display
    let mut descs = vec![];
    let mut plain_lens = vec![];
    build_tree_descs(topology, "  ", "  ", "  ", "  ", &mut descs, &mut plain_lens);
    let mut display = LiveTree::new(descs, plain_lens, silent, repeat > 1);

    if !tracing {
        display.print_initial();
    }

    let mut nodes: Vec<NodeReport> = Vec::new();
    let mut path: Vec<usize> = Vec::new();
    let aggregated = build_aggregation(
        topology,
        0,
        &mut nodes,
        &mut display,
        &mut path,
        &pub_keys,
        &signatures,
        tracing,
        true,
        repeat,
    );

    verify_single_message_aggregate(&aggregated).expect("root single-message proof failed to verify");

    BenchmarkReport { nodes }
}

#[allow(clippy::too_many_arguments)]
fn run_aggregate_single_message(
    children: &[SingleMessageAggregateSignature],
    raw_xmss: Vec<(XmssPublicKey, XmssSignature)>,
    log_inv_rate: usize,
    n_xmss: usize,
    path: Vec<usize>,
    label: &str,
    silent: bool,
    nodes: &mut Vec<NodeReport>,
) -> SingleMessageAggregateSignature {
    let time = Instant::now();

    #[cfg(not(feature = "standard-alloc"))]
    zk_alloc::begin_phase();

    let result = aggregate_single_message_signatures(
        children,
        raw_xmss,
        message_for_benchmark(),
        BENCHMARK_SLOT,
        log_inv_rate,
    )
    .unwrap();

    #[cfg(not(feature = "standard-alloc"))]
    let result = {
        zk_alloc::end_phase();
        result.clone()
    };

    let elapsed = time.elapsed();
    let meta = result.proof.metadata.as_ref().unwrap();
    let proof_kib = result.proof.proof.proof_size_fe() * F::bits() / (8 * 1024);
    let stats = NodeStats {
        time_secs: elapsed.as_secs_f64(),
        time_ci_secs: 0.0,
        samples: 1,
        proof_kib,
        cycles: meta.cycles,
        memory: meta.memory,
        poseidons: meta.n_poseidons,
        dots: meta.n_extension_ops,
        n_xmss: Some(n_xmss),
        kind: NodeKind::AggregateSingleMessage,
    };

    print_stage(silent, label, &stats);
    nodes.push(NodeReport {
        path: path.clone(),
        stats,
    });

    result
}

fn run_merge_many(
    types_1: Vec<SingleMessageAggregateSignature>,
    log_inv_rate: usize,
    path: Vec<usize>,
    label: &str,
    silent: bool,
    nodes: &mut Vec<NodeReport>,
) -> MultiMessageAggregateSignature {
    let time = Instant::now();

    #[cfg(not(feature = "standard-alloc"))]
    zk_alloc::begin_phase();

    let result = merge_single_message_aggregates(types_1, log_inv_rate).unwrap();

    #[cfg(not(feature = "standard-alloc"))]
    let result = {
        zk_alloc::end_phase();
        result.clone()
    };

    let elapsed = time.elapsed();
    let meta = result.proof.metadata.as_ref().unwrap();
    let proof_kib = result.proof.proof.proof_size_fe() * F::bits() / (8 * 1024);
    let stats = NodeStats {
        time_secs: elapsed.as_secs_f64(),
        time_ci_secs: 0.0,
        samples: 1,
        proof_kib,
        cycles: meta.cycles,
        memory: meta.memory,
        poseidons: meta.n_poseidons,
        dots: meta.n_extension_ops,
        n_xmss: None,
        kind: NodeKind::MergeSingleMessages,
    };

    print_stage(silent, label, &stats);
    nodes.push(NodeReport {
        path: path.clone(),
        stats,
    });

    result
}

#[allow(clippy::too_many_arguments)]
fn run_split(
    multi_message: MultiMessageAggregateSignature,
    index: usize,
    log_inv_rate: usize,
    n_xmss: usize,
    path: Vec<usize>,
    label: &str,
    silent: bool,
    nodes: &mut Vec<NodeReport>,
) -> SingleMessageAggregateSignature {
    let time = Instant::now();

    #[cfg(not(feature = "standard-alloc"))]
    zk_alloc::begin_phase();

    let result = split_multi_message_aggregate(multi_message, index, log_inv_rate).unwrap();

    #[cfg(not(feature = "standard-alloc"))]
    let result = {
        zk_alloc::end_phase();
        result.clone()
    };

    let elapsed = time.elapsed();
    let meta = result.proof.metadata.as_ref().unwrap();
    let proof_kib = result.proof.proof.proof_size_fe() * F::bits() / (8 * 1024);
    let stats = NodeStats {
        time_secs: elapsed.as_secs_f64(),
        time_ci_secs: 0.0,
        samples: 1,
        proof_kib,
        cycles: meta.cycles,
        memory: meta.memory,
        poseidons: meta.n_poseidons,
        dots: meta.n_extension_ops,
        n_xmss: Some(n_xmss),
        kind: NodeKind::SplitMultiMessage,
    };

    print_stage(silent, label, &stats);
    nodes.push(NodeReport {
        path: path.clone(),
        stats,
    });

    result
}

fn build_parent_multi_message(
    per_component: usize,
    n_components: usize,
    log_inv_rate: usize,
    nodes: &mut Vec<NodeReport>,
    silent: bool,
) -> MultiMessageAggregateSignature {
    let cache = get_benchmark_signatures();
    assert!(n_components >= 1, "n_components must be >= 1");
    assert!(
        cache.len() >= per_component * n_components,
        "benchmark cache too small: need {} sigs, have {}",
        per_component * n_components,
        cache.len(),
    );

    let mut components: Vec<SingleMessageAggregateSignature> = Vec::with_capacity(n_components);
    for i in 0..n_components {
        let raw_xmss = cache[i * per_component..(i + 1) * per_component].to_vec();
        let result = run_aggregate_single_message(
            &[],
            raw_xmss,
            log_inv_rate,
            per_component,
            vec![0, i],
            &format!("  setup aggregate component {}", i),
            silent,
            nodes,
        );
        components.push(result);
    }

    run_merge_many(
        components,
        log_inv_rate,
        vec![0],
        "  setup merge parent multi-message",
        silent,
        nodes,
    )
}

/// Benchmark `split_multi_message_aggregate` at index 0 of a parent multi-message built from
/// `n_components` single-message's, each aggregated from `per_component` raw XMSS sigs.
pub fn run_split_benchmark(
    per_component: usize,
    n_components: usize,
    log_inv_rate: usize,
    silent: bool,
) -> BenchmarkReport {
    #[cfg(target_os = "macos")]
    let _activity = macos_activity::Activity::begin("lean-multisig benchmark");

    precompute_dft_twiddles::<F>(1 << 24);

    init_aggregation_bytecode();

    if !silent {
        println!(
            "Aggregation program: {} instructions\n",
            pretty_integer(get_aggregation_bytecode().code.len())
        );
    }

    let mut nodes: Vec<NodeReport> = Vec::new();
    let multi_message = build_parent_multi_message(per_component, n_components, log_inv_rate, &mut nodes, silent);
    let split = run_split(
        multi_message,
        0,
        log_inv_rate,
        per_component,
        vec![],
        "  split index 0 (measured)",
        silent,
        &mut nodes,
    );

    verify_single_message_aggregate(&split).expect("split-derived single-message failed to verify");

    BenchmarkReport { nodes }
}

/// Benchmark `merge_single_message_aggregates` over one split-derived single-message and one
/// freshly-aggregated original single-message, both claiming `per_component` signers.
pub fn run_merge_split_and_original_benchmark(
    per_component: usize,
    n_components: usize,
    log_inv_rate: usize,
    silent: bool,
) -> BenchmarkReport {
    #[cfg(target_os = "macos")]
    let _activity = macos_activity::Activity::begin("lean-multisig benchmark");

    precompute_dft_twiddles::<F>(1 << 24);

    init_aggregation_bytecode();

    if !silent {
        println!(
            "Aggregation program: {} instructions\n",
            pretty_integer(get_aggregation_bytecode().code.len())
        );
    }

    let mut nodes: Vec<NodeReport> = Vec::new();
    let multi_message = build_parent_multi_message(per_component, n_components, log_inv_rate, &mut nodes, silent);
    let split = run_split(
        multi_message,
        0,
        log_inv_rate,
        per_component,
        vec![1, 0],
        "  split index 0",
        silent,
        &mut nodes,
    );

    let cache = get_benchmark_signatures();
    let parent_end = per_component * n_components;
    assert!(
        cache.len() >= parent_end + per_component,
        "benchmark cache too small for original component"
    );
    let raw_xmss = cache[parent_end..parent_end + per_component].to_vec();
    let original = run_aggregate_single_message(
        &[],
        raw_xmss,
        log_inv_rate,
        per_component,
        vec![2],
        "  original aggregate",
        silent,
        &mut nodes,
    );

    let merged = run_merge_many(
        vec![split, original],
        log_inv_rate,
        vec![],
        "  merge_many (measured)",
        silent,
        &mut nodes,
    );

    verify_multi_message_aggregate(&merged).expect("merged multi-message failed to verify");

    BenchmarkReport { nodes }
}

/// Benchmark `aggregate_single_message_signatures` over one split-derived single-message (index 0 of a
/// K-component parent multi-message) plus `n_new_leaves` fresh raw XMSS signatures
/// signing the same (message, slot). Output is a single single-message claiming
/// `per_component + n_new_leaves` signers.
pub fn run_merge_split_and_leaves_benchmark(
    per_component: usize,
    n_components: usize,
    n_new_leaves: usize,
    log_inv_rate: usize,
    silent: bool,
) -> BenchmarkReport {
    #[cfg(target_os = "macos")]
    let _activity = macos_activity::Activity::begin("lean-multisig benchmark");

    precompute_dft_twiddles::<F>(1 << 24);

    init_aggregation_bytecode();

    if !silent {
        println!(
            "Aggregation program: {} instructions\n",
            pretty_integer(get_aggregation_bytecode().code.len())
        );
    }

    let mut nodes: Vec<NodeReport> = Vec::new();
    let multi_message = build_parent_multi_message(per_component, n_components, log_inv_rate, &mut nodes, silent);
    let split = run_split(
        multi_message,
        0,
        log_inv_rate,
        per_component,
        vec![1, 0],
        "  split index 0",
        silent,
        &mut nodes,
    );

    let cache = get_benchmark_signatures();
    let parent_end = per_component * n_components;
    assert!(
        cache.len() >= parent_end + n_new_leaves,
        "benchmark cache too small for {} new leaves",
        n_new_leaves
    );
    let new_raw_xmss = cache[parent_end..parent_end + n_new_leaves].to_vec();
    let n_total = per_component + n_new_leaves;

    let combined = run_aggregate_single_message(
        std::slice::from_ref(&split),
        new_raw_xmss,
        log_inv_rate,
        n_total,
        vec![],
        "  aggregate split + new leaves (measured)",
        silent,
        &mut nodes,
    );

    verify_single_message_aggregate(&combined).expect("combined single-message failed to verify");

    BenchmarkReport { nodes }
}

// TODO is there a better fix?
#[cfg(target_os = "macos")]
mod macos_activity {
    use objc2::rc::Retained;
    use objc2::runtime::{NSObjectProtocol, ProtocolObject};
    use objc2_foundation::{NSActivityOptions, NSProcessInfo, NSString};

    pub struct Activity {
        process_info: Retained<NSProcessInfo>,
        token: Retained<ProtocolObject<dyn NSObjectProtocol>>,
    }

    impl Activity {
        pub fn begin(reason: &str) -> Self {
            let process_info = NSProcessInfo::processInfo();
            let reason = NSString::from_str(reason);
            let options = NSActivityOptions::UserInitiated | NSActivityOptions::LatencyCritical;
            let token = process_info.beginActivityWithOptions_reason(options, &reason);
            Self { process_info, token }
        }
    }

    impl Drop for Activity {
        fn drop(&mut self) {
            unsafe { self.process_info.endActivity(&self.token) };
        }
    }
}

#[test]
#[ignore]
fn test_aggregation_throughput_per_num_xmss() {
    let log_inv_rate = 1;
    precompute_dft_twiddles::<F>(1 << 24);
    init_aggregation_bytecode();
    let _ = get_aggregation_bytecode();
    let mut num_xmss_and_time = vec![];
    let mut indexes = vec![];
    for i in 1..100 {
        indexes.push(i * 10);
    }
    for i in 50..100 {
        indexes.push(i * 20);
    }
    for i in 40..60 {
        indexes.push(i * 50);
    }
    for num_xmss in indexes {
        let topology = AggregationTopology {
            raw_xmss: num_xmss,
            children: vec![],
            log_inv_rate,
            overlap: 0,
        };
        let time = run_aggregation_benchmark(&topology, false, true, 1).total_time_secs();
        num_xmss_and_time.push((num_xmss, time));
        println!(
            "{} XMSS -> {} XMSS/s",
            num_xmss,
            (num_xmss as f64 / time).round() as usize
        );

        std::thread::sleep(std::time::Duration::from_millis(1000));

        let mut csv = String::from("num_sigs,throughput (XMSS/s)\n");
        for &(n, t) in &num_xmss_and_time {
            csv.push_str(&format!("{},{:.1}\n", n, n as f64 / t));
        }
        let path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("benchmarks/xmss_throughput.csv");
        std::fs::create_dir_all(path.parent().unwrap()).unwrap();
        std::fs::write(&path, &csv).unwrap();
        println!("\nWrote {}", path.display());
    }
}
