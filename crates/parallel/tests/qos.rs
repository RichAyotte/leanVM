//! The pool honours a requested worker scheduling class, and no dispatch leaves
//! a caller's thread in it. Its own process, since the pool is a process-wide
//! singleton and the request only counts before its first dispatch.

#![cfg(target_os = "linux")]

use std::sync::atomic::{AtomicI32, Ordering};

const SCHED_IDLE: core::ffi::c_int = 5;

unsafe extern "C" {
    fn sched_getscheduler(pid: core::ffi::c_int) -> core::ffi::c_int;
}

/// The scheduling class of the thread `tid` names, or of the caller for 0.
fn policy(tid: core::ffi::c_int) -> core::ffi::c_int {
    // SAFETY: the call only reads, and 0 names the calling thread on Linux.
    unsafe { sched_getscheduler(tid) }
}

/// Every pool worker's class, read off `/proc` rather than out of a task, so
/// what is asserted does not depend on which threads happened to claim one.
fn worker_policies() -> Vec<core::ffi::c_int> {
    let mut found = Vec::new();
    for entry in std::fs::read_dir("/proc/self/task").expect("procfs is mounted") {
        let dir = entry.expect("a task entry").path();
        let comm = std::fs::read_to_string(dir.join("comm")).unwrap_or_default();
        if comm.trim_end().starts_with("parallel-") {
            let tid: core::ffi::c_int = dir
                .file_name()
                .and_then(|n| n.to_str())
                .and_then(|n| n.parse().ok())
                .expect("a task directory is named by its tid");
            found.push(policy(tid));
        }
    }
    found
}

/// A dispatch leaves the calling thread's class alone.
///
/// Worker 0 is the caller's own thread on loan for one dispatch, and on Linux an
/// unprivileged thread cannot leave `SCHED_IDLE` again: `sched_setscheduler`
/// back to `SCHED_OTHER` returns `EPERM` under the default `RLIMIT_NICE`. A
/// class put on that thread would therefore outlive the dispatch for good, and
/// every thread the caller spawned afterwards would inherit it.
#[test]
fn a_dispatch_leaves_the_calling_thread_in_its_own_class() {
    let outside = policy(0);
    assert_ne!(outside, SCHED_IDLE, "the test process starts in the default class");

    parallel::set_worker_qos(parallel::Qos::Utility);

    // Two rounds on threads of their own: the class used to be put on whichever
    // thread reached the pool first and on no other, so one round cannot tell a
    // dispatcher that keeps its class from one that was simply not the first.
    for round in 1..=2 {
        let after = AtomicI32::new(0);
        std::thread::scope(|scope| {
            scope.spawn(|| {
                parallel::for_each(parallel::num_threads(), |_| {});
                after.store(policy(0), Ordering::Release);
            });
        });
        assert_eq!(
            after.load(Ordering::Acquire),
            outside,
            "round {round}: the dispatch left its calling thread in the pool's class"
        );

        let workers = worker_policies();
        assert!(
            !workers.is_empty() && workers.iter().all(|&p| p == SCHED_IDLE),
            "round {round}: the pool's own workers are in the requested class: {workers:?}"
        );
    }
}
