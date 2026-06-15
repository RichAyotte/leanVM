/-
ε₃ measure bounds for `prop:pinbound` / `cond:pinning`: the Good-set failure
probabilities for the slice/cross conditions, assembled from the multivariate
Schwartz–Zippel chain (`SlotProb`) and the cross-form objects (`Pinning`).

Part of the `GoodSetAbsorption` formalization campaign.
-/
import Mathlib
import Zkwhir.Pinning
import Zkwhir.SlotProb

set_option linter.style.header false
set_option linter.unusedSectionVars false

noncomputable section

open scoped ENNReal

namespace ZkWhir

variable (P : Params) (Fq : Type*) [Field Fq] [Fintype Fq] [Algebra (Fp P) Fq]
  (Dom : Finset (Fp P)) [Nonempty {x // x ∈ Dom}] (S : Stmt P Fq)

/-- **`lem:termslice` hypothesis-failure bound** (tex:549): the cross-form's
nonvanishing hypothesis `ŵ(α₀, c*) ≠ 0` fails with probability at most `k₀/q` over
the challenges, whenever the data column `S.w(·, c*)` is not identically zero.
A direct application of the multivariate Schwartz–Zippel chain to `wHat0`. -/
theorem termslice_hyp_failure_le [Nonempty Fq] [DecidableEq Fq] (c0 : Cube P.m)
    (hw : (fun s => S.w (s, c0)) ≠ (0 : Cube P.k₀ → Fq)) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | wHat0 P Fq Dom S ch c0 = 0} ≤
      (P.k₀ : ℝ≥0∞) / Fintype.card Fq := by
  simp_rw [wHat0_eq_mle]
  exact challenge_mle_α_zero_le P Fq Dom hw

/-- **Per-coordinate dual-vanishing bound** (SPREAD measure): for a fixed nonzero
`Fp`-functional `φ` on `Fq`, the coordinate event `φ(α_i) = 0` has probability at
most `p^{d-1}/q = 1/p` over the challenges (the kernel `{a | φ a = 0}` has
`≤ p^{d-1}` elements, `card_filter_dual_zero_le`). This is the per-functional,
per-coordinate input to the SPREAD-failure union bound. -/
theorem challenge_alpha_dual_zero_le [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    (i : Fin P.k₀) (hcard : Fintype.card (Fp P) = P.p)
    {φ : Module.Dual (Fp P) Fq} (hφ : φ ≠ 0) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | φ (ch.α i) = 0} ≤
      (P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) / (fieldCard Fq : ℝ≥0∞) := by
  classical
  refine challenge_α_coord_le P Fq Dom i (fun _ => {a : Fq | φ a = 0}) _ (fun z => ?_)
  refine (uniform_pi_coord_le (ι := Fin P.k₀) i {a : Fq | φ a = 0}
    (P.p ^ (Module.finrank (Fp P) Fq - 1)) (fun s hs => ?_)).trans ?_
  · have hsub : s ⊆ Finset.univ.filter (fun a : Fq => φ a = 0) := by
      intro a ha; rw [Finset.mem_filter]; exact ⟨Finset.mem_univ a, hs a ha⟩
    exact le_trans (Finset.card_le_card hsub) (card_filter_dual_zero_le P Fq hcard hφ)
  · simp [fieldCard]

/-- **Per-functional joint term for the SPREAD measure**: for a fixed nonzero
`Fp`-functional `φ`, the joint event `∀ i, φ(α_i) = 0` has probability at most
`(p^{d-1})^{k₀} / q^{k₀}`. Combines the joint multi-coordinate bound `uniform_pi_all`
(via the challenge marginal `challenge_α_event_le`) with the kernel-card bound
`card_filter_dual_zero_le`. This is each term of the SPREAD-failure union sum. -/
theorem challenge_alpha_all_dual_zero_le [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    (hcard : Fintype.card (Fp P) = P.p) {φ : Module.Dual (Fp P) Fq} (hφ : φ ≠ 0) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ∀ i, φ (ch.α i) = 0} ≤
      (P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) ^ P.k₀ /
        (Fintype.card Fq : ℝ≥0∞) ^ P.k₀ := by
  classical
  refine challenge_α_event_le P Fq Dom (fun α => ∀ i, φ (α i) = 0) _ ?_
  have h := uniform_pi_all (ι := Fin P.k₀) (β := Fq) {a : Fq | φ a = 0}
    (P.p ^ (Module.finrank (Fp P) Fq - 1))
    (fun s hs => (Finset.card_le_card (fun a ha =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ a, hs a ha⟩)).trans
      (card_filter_dual_zero_le P Fq hcard hφ))
  rw [Fintype.card_fin, Nat.cast_pow] at h
  simpa only [Set.mem_setOf_eq] using h

/-- **Tail joint `α`-coordinate dual-vanishing bound** (the tail-SPREAD per-term measure):
a fixed nonzero `Fp`-functional `φ` vanishes on the `k₀ − 1` tail coordinates `α_i`
(`i ≠ 0`) with probability at most `(p^{d-1})^{k₀-1}/q^{k₀-1}` — the joint over the tail
coordinates, via `uniform_pi_subset` and the kernel-card bound `card_filter_dual_zero_le`.
The tail analogue of `challenge_alpha_all_dual_zero_le`, for the head-erased SPREAD. -/
theorem challenge_alpha_tail_dual_zero_le [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    (hcard : Fintype.card (Fp P) = P.p) {φ : Module.Dual (Fp P) Fq} (hφ : φ ≠ 0) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom |
        ∀ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i ≠ ⟨0, P.k₀_pos⟩),
          φ (ch.α i) = 0} ≤
      (P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) ^ (P.k₀ - 1) /
        (Fintype.card Fq : ℝ≥0∞) ^ (P.k₀ - 1) := by
  classical
  refine challenge_α_event_le P Fq Dom
    (fun α => ∀ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i ≠ ⟨0, P.k₀_pos⟩),
      φ (α i) = 0) _ ?_
  have hJcard :
      (Finset.univ.filter (fun i : Fin P.k₀ => i ≠ ⟨0, P.k₀_pos⟩)).card = P.k₀ - 1 := by
    rw [Finset.filter_ne' Finset.univ (⟨0, P.k₀_pos⟩ : Fin P.k₀),
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have h := uniform_pi_subset (ι := Fin P.k₀) (β := Fq)
    (Finset.univ.filter (fun i : Fin P.k₀ => i ≠ ⟨0, P.k₀_pos⟩))
    (fun _ => Finset.univ.filter (fun a : Fq => φ a = 0))
    (P.p ^ (Module.finrank (Fp P) Fq - 1))
    (fun _ _ => card_filter_dual_zero_le P Fq hcard hφ)
  rw [hJcard, Nat.cast_pow] at h
  have hset : {α : Fin P.k₀ → Fq |
        ∀ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i ≠ ⟨0, P.k₀_pos⟩), φ (α i) = 0}
      = {f : Fin P.k₀ → Fq | ∀ j ∈ Finset.univ.filter (fun i : Fin P.k₀ => i ≠ ⟨0, P.k₀_pos⟩),
          f j ∈ Finset.univ.filter (fun a : Fq => φ a = 0)} := by
    ext α
    simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hset]
  exact h

/-- **Each tail-SPREAD-failure union term is bounded** (the tail per-`φ` measure): the
event `{φ` kills every head-erased tail product`}` is contained in `{∀ i ≠ 0, φ(α_i) = 0}`,
because each tail coordinate `α_i` (`i ≠ 0`) is a sum of head-erased tail products
(`alpha_eq_sum_tail`). So its measure is `≤ (p^{d-1})^{k₀-1}/q^{k₀-1}` by
`challenge_alpha_tail_dual_zero_le`. -/
theorem tail_spread_term_le [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    (hcard : Fintype.card (Fp P) = P.p) {φ : Module.Dual (Fp P) Fq} (hφ : φ ≠ 0) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ∀ s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true},
        φ (∏ j ∈ Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀),
          (if s.val j then ch.α j else 1 - ch.α j)) = 0} ≤
      (P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) ^ (P.k₀ - 1) /
        (Fintype.card Fq : ℝ≥0∞) ^ (P.k₀ - 1) := by
  refine le_trans (MeasureTheory.measure_mono ?_)
    (challenge_alpha_tail_dual_zero_le P Fq Dom hcard hφ)
  intro ch hch
  simp only [Set.mem_setOf_eq] at hch ⊢
  intro i hi
  rw [Finset.mem_filter] at hi
  rw [alpha_eq_sum_tail P Fq Dom ch i hi.2, map_sum]
  refine Finset.sum_eq_zero fun s hsmem => ?_
  rw [Finset.mem_filter] at hsmem
  exact hch ⟨s, hsmem.2.2⟩

/-- **Each SPREAD-failure union term is bounded** by the joint coordinate event:
`A_φ = {φ` vanishes on every `êq(α,s)}` is contained in `{∀i φ(α_i)=0}`, because
each `α_i = ∑_{s≥i} êq(α,s)` lies in `span(êq(α,·))` (the change-of-basis
`alphaMonomial_eq_sum_eqPoly`). So `P[A_φ] ≤ (p^{d-1})^{k₀}/q^{k₀}`. -/
theorem spread_term_le [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    (hcard : Fintype.card (Fp P) = P.p) {φ : Module.Dual (Fp P) Fq} (hφ : φ ≠ 0) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ∀ s, φ (eqPoly ch.α s) = 0} ≤
      (P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) ^ P.k₀ /
        (Fintype.card Fq : ℝ≥0∞) ^ P.k₀ := by
  refine le_trans (MeasureTheory.measure_mono ?_)
    (challenge_alpha_all_dual_zero_le P Fq Dom hcard hφ)
  intro ch hch i
  rw [← alphaMonomial_single P Fq Dom ch i, alphaMonomial_eq_sum_eqPoly, map_sum]
  exact Finset.sum_eq_zero fun s _ => hch s

/-- **SPREAD-failure union bound** (the SPREAD measure skeleton): the probability
that the SPREAD span misses `⊤` is at most the sum, over nonzero `Fp`-functionals
`φ` on `Fq` (a finite set), of `P[φ` vanishes on every `êq(α,s)]`. By
`exists_dual_of_not_spread`, every `¬SPREAD` challenge lies in some such `A_φ`; the
union over the finite dual is bounded by the sum (`measure_biUnion_finset_le`). The
remaining work is the per-`φ` term `P[A_φ] ≤ (1/p)^{k₀}` (the joint over the `k₀`
`α`-coordinates), reducible via `challenge_alpha_dual_zero_le` once a multi-coordinate
joint-independence bound is available. -/
theorem spread_failure_le_sum [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    [Fintype (Module.Dual (Fp P) Fq)] :
    (challengePMF P Fq Dom).toOuterMeasure
        {ch : Challenges P Fq Dom |
          Submodule.span (Fp P) (Set.range (eqPoly ch.α)) ≠ ⊤} ≤
      ∑ φ ∈ Finset.univ.filter (fun φ : Module.Dual (Fp P) Fq => φ ≠ 0),
        (challengePMF P Fq Dom).toOuterMeasure
          {ch : Challenges P Fq Dom | ∀ s, φ (eqPoly ch.α s) = 0} := by
  classical
  have hsub : {ch : Challenges P Fq Dom |
        Submodule.span (Fp P) (Set.range (eqPoly ch.α)) ≠ ⊤} ⊆
      ⋃ φ ∈ Finset.univ.filter (fun φ : Module.Dual (Fp P) Fq => φ ≠ 0),
        {ch : Challenges P Fq Dom | ∀ s, φ (eqPoly ch.α s) = 0} := by
    intro ch hch
    obtain ⟨φ, hφ0, hφv⟩ := exists_dual_of_not_spread P Fq Dom ch hch
    exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ φ, hφ0⟩) hφv
  exact (MeasureTheory.measure_mono hsub).trans
    (MeasureTheory.measure_biUnion_finset_le _ _)

/-- **SPREAD failure measure** (`lem:span` measure, assembled): the probability that
the SPREAD span misses `⊤` is at most `#{φ ≠ 0} · (p^{d-1})^{k₀}/q^{k₀}`. Combines the
union bound `spread_failure_le_sum` with the per-term bound `spread_term_le`. Since the
dual has `p^d = q` elements and `(p^{d-1})^{k₀}/q^{k₀} = p^{-k₀}`, this is `≤ p^{d-k₀}`,
small for `k₀ > d` — the SPREAD Good-set failure bound that `lem:span` contributes to ε₃. -/
theorem spread_failure_le [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    [Fintype (Module.Dual (Fp P) Fq)] (hcard : Fintype.card (Fp P) = P.p) :
    (challengePMF P Fq Dom).toOuterMeasure
        {ch : Challenges P Fq Dom |
          Submodule.span (Fp P) (Set.range (eqPoly ch.α)) ≠ ⊤} ≤
      ((Finset.univ.filter (fun φ : Module.Dual (Fp P) Fq => φ ≠ 0)).card : ℝ≥0∞) *
        ((P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) ^ P.k₀ /
          (Fintype.card Fq : ℝ≥0∞) ^ P.k₀) := by
  refine (spread_failure_le_sum P Fq Dom).trans ?_
  calc ∑ φ ∈ Finset.univ.filter (fun φ : Module.Dual (Fp P) Fq => φ ≠ 0),
        (challengePMF P Fq Dom).toOuterMeasure
          {ch : Challenges P Fq Dom | ∀ s, φ (eqPoly ch.α s) = 0}
      ≤ ∑ _φ ∈ Finset.univ.filter (fun φ : Module.Dual (Fp P) Fq => φ ≠ 0),
          ((P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) ^ P.k₀ /
            (Fintype.card Fq : ℝ≥0∞) ^ P.k₀) :=
        Finset.sum_le_sum fun φ hφ =>
          spread_term_le P Fq Dom hcard (Finset.mem_filter.mp hφ).2
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **Uniform-`α` inner bound for `hker`** (fixed `j`, `c`, with `c_{r₀} ≠ 0`): under
a uniform `α`, the probability that `∑_r c_r(α_m^{p^r} − powz_m) = 0` holds at every
coordinate `m > 0` is at most `(p^{d-1}/q)^{|m>0|}`. Combines `uniform_pi_subset`
(joint over the `m>0` coordinates) with the per-coordinate root bound
`hker_root_card_le`. -/
theorem uniform_hker_term [DecidableEq Fq] (powz : Fin P.k₀ → Fq)
    (c : Fin (Module.finrank (Fp P) Fq) → Fq) (r₀ : Fin (Module.finrank (Fp P) Fq))
    (hcr : c r₀ ≠ 0) :
    (PMF.uniformOfFintype (Fin P.k₀ → Fq)).toOuterMeasure
      {α : Fin P.k₀ → Fq | ∀ m : Fin P.k₀, (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m →
        ∑ r, c r * (α m ^ P.p ^ (r : ℕ) - powz m) = 0} ≤
      (P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) ^
          (Finset.univ.filter (fun m : Fin P.k₀ => (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m)).card /
        (Fintype.card Fq : ℝ≥0∞) ^
          (Finset.univ.filter (fun m : Fin P.k₀ => (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m)).card := by
  classical
  have hp1 : 1 < P.p := P.pPrime.one_lt
  have hset : {α : Fin P.k₀ → Fq | ∀ m : Fin P.k₀, (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m →
        ∑ r, c r * (α m ^ P.p ^ (r : ℕ) - powz m) = 0}
      = {α : Fin P.k₀ → Fq | ∀ m ∈ Finset.univ.filter
          (fun m : Fin P.k₀ => (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m),
          α m ∈ Finset.univ.filter
            (fun x : Fq => ∑ r, c r * (x ^ P.p ^ (r : ℕ) - powz m) = 0)} := by
    ext α
    simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hset]
  refine le_of_le_of_eq (uniform_pi_subset _ _ (P.p ^ (Module.finrank (Fp P) Fq - 1))
    (fun m _ => hker_root_card_le hp1 c r₀ hcr (powz m))) ?_
  rw [Nat.cast_pow]

/-- **Per-`(j,c)` term of the `hker` measure** (challenge form): for a fixed node
`j` and coefficient vector `c` with `c_{r₀} ≠ 0`, the probability over the challenges
that `∑_r c_r(α_m^{p^r} − powz_j(m)) = 0` at every `m > 0` is at most
`(p^{d-1}/q)^{|m>0|}`. Lifts `uniform_hker_term` over the challenge measure via the
`z`-dependent marginal `challenge_alpha_joint_le`. -/
theorem challenge_hker_term_le [DecidableEq Fq] (j : Fin 2)
    (c : Fin (Module.finrank (Fp P) Fq) → Fq) (r₀ : Fin (Module.finrank (Fp P) Fq))
    (hcr : c r₀ ≠ 0) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ∀ m : Fin P.k₀, (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m →
        ∑ r, c r * (ch.α m ^ P.p ^ (r : ℕ) - powSeq (ch.z j) P.k₀ m) = 0} ≤
      (P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) ^
          (Finset.univ.filter (fun m : Fin P.k₀ => (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m)).card /
        (Fintype.card Fq : ℝ≥0∞) ^
          (Finset.univ.filter (fun m : Fin P.k₀ => (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m)).card :=
  challenge_alpha_joint_le P Fq Dom
    (fun z => {α : Fin P.k₀ → Fq | ∀ m : Fin P.k₀, (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m →
      ∑ r, c r * (α m ^ P.p ^ (r : ℕ) - powSeq (z j) P.k₀ m) = 0}) _
    (fun z => uniform_hker_term P Fq (powSeq (z j) P.k₀) c r₀ hcr)

/-- **`hker`-failure union skeleton**: the `hker` Good-set failure (∃ node `j` and
nonzero coefficient vector `c` with `c₀ = 0` satisfying the kernel relations at every
`m > 0`) is contained in the union, over the finitely many such `(j,c)` pairs, of the
per-`(j,c)` events, hence bounded by their sum. -/
theorem hker_failure_le_sum [DecidableEq Fq] (hd0 : 0 < extDeg P Fq) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ∃ (j : Fin 2) (c : Fin (extDeg P Fq) → Fq),
        c ⟨0, hd0⟩ = 0 ∧ c ≠ 0 ∧ ∀ m : Fin P.k₀, (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m →
          ∑ r, c r * (ch.α m ^ P.p ^ (r : ℕ) - powSeq (ch.z j) P.k₀ m) = 0} ≤
      ∑ jc ∈ Finset.univ.filter
          (fun jc : Fin 2 × (Fin (extDeg P Fq) → Fq) => jc.2 ⟨0, hd0⟩ = 0 ∧ jc.2 ≠ 0),
        (challengePMF P Fq Dom).toOuterMeasure
          {ch : Challenges P Fq Dom | ∀ m : Fin P.k₀, (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m →
            ∑ r, jc.2 r * (ch.α m ^ P.p ^ (r : ℕ) - powSeq (ch.z jc.1) P.k₀ m) = 0} := by
  classical
  have hsub : {ch : Challenges P Fq Dom | ∃ (j : Fin 2) (c : Fin (extDeg P Fq) → Fq),
        c ⟨0, hd0⟩ = 0 ∧ c ≠ 0 ∧ ∀ m : Fin P.k₀, (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m →
          ∑ r, c r * (ch.α m ^ P.p ^ (r : ℕ) - powSeq (ch.z j) P.k₀ m) = 0} ⊆
      ⋃ jc ∈ Finset.univ.filter
          (fun jc : Fin 2 × (Fin (extDeg P Fq) → Fq) => jc.2 ⟨0, hd0⟩ = 0 ∧ jc.2 ≠ 0),
        {ch : Challenges P Fq Dom | ∀ m : Fin P.k₀, (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m →
          ∑ r, jc.2 r * (ch.α m ^ P.p ^ (r : ℕ) - powSeq (ch.z jc.1) P.k₀ m) = 0} := by
    intro ch hch
    obtain ⟨j, c, hc0, hcne, hcond⟩ := hch
    exact Set.mem_iUnion₂.mpr
      ⟨(j, c), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc0, hcne⟩, hcond⟩
  exact (MeasureTheory.measure_mono hsub).trans
    (MeasureTheory.measure_biUnion_finset_le _ _)

/-- **`hker` failure measure** (`cond:twist` Moore-determinant Good-set bound,
assembled): the `hker` failure probability is at most `#{(j,c) : c₀=0, c≠0} ·
(p^{d-1}/q)^{|m>0|}`. Combines the union skeleton `hker_failure_le_sum` with the
per-`(j,c)` bound `challenge_hker_term_le` (choosing a nonzero coordinate `r₀` of
each `c`). This is the `hker` Good-set contribution to ε₃. -/
theorem hker_failure_le [DecidableEq Fq] (hd0 : 0 < extDeg P Fq) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ∃ (j : Fin 2) (c : Fin (extDeg P Fq) → Fq),
        c ⟨0, hd0⟩ = 0 ∧ c ≠ 0 ∧ ∀ m : Fin P.k₀, (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m →
          ∑ r, c r * (ch.α m ^ P.p ^ (r : ℕ) - powSeq (ch.z j) P.k₀ m) = 0} ≤
      ((Finset.univ.filter
          (fun jc : Fin 2 × (Fin (extDeg P Fq) → Fq) => jc.2 ⟨0, hd0⟩ = 0 ∧ jc.2 ≠ 0)).card : ℝ≥0∞) *
        ((P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) ^
            (Finset.univ.filter (fun m : Fin P.k₀ => (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m)).card /
          (Fintype.card Fq : ℝ≥0∞) ^
            (Finset.univ.filter (fun m : Fin P.k₀ => (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m)).card) := by
  refine (hker_failure_le_sum P Fq Dom hd0).trans ?_
  refine (Finset.sum_le_sum (fun jc hjc => ?_)).trans
    (le_of_eq (by rw [Finset.sum_const, nsmul_eq_mul]))
  obtain ⟨r₀, hr₀⟩ := Function.ne_iff.mp (Finset.mem_filter.mp hjc).2.2
  exact challenge_hker_term_le P Fq Dom jc.1 jc.2 r₀ hr₀

/-- **`cond:twist` Good-set failure measure**: `cond:twist`'s genericity is `hDr ∧
hker` (the Frobenius gap and the Moore-determinant kernel triviality), so its
failure probability is bounded by the union `P[¬hDr] + P[¬hker] ≤ p/q + #{(j,c)}·
(p^{d-1}/q)^{|m>0|}` (`hDr_failure_le` + `hker_failure_le`). The `cond:twist`
contribution to ε₃. -/
theorem condtwist_failure_le [Nonempty Fq] [FiniteDimensional (Fp P) Fq] [DecidableEq Fq]
    (hdp : (extDeg P Fq).Prime) (hcardq : Fintype.card Fq = P.p ^ extDeg P Fq)
    (hd0 : 0 < extDeg P Fq) :
    (challengePMF P Fq Dom).toOuterMeasure
      ({ch : Challenges P Fq Dom | ¬ ∀ (j : Fin 2) (r : Fin (extDeg P Fq)), (r : ℕ) ≠ 0 →
          ch.α ⟨0, P.k₀_pos⟩ ^ P.p ^ (r : ℕ) - ch.α ⟨0, P.k₀_pos⟩ ≠ 0} ∪
        {ch : Challenges P Fq Dom | ∃ (j : Fin 2) (c : Fin (extDeg P Fq) → Fq),
          c ⟨0, hd0⟩ = 0 ∧ c ≠ 0 ∧ ∀ m : Fin P.k₀, (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m →
            ∑ r, c r * (ch.α m ^ P.p ^ (r : ℕ) - powSeq (ch.z j) P.k₀ m) = 0}) ≤
      (P.p : ℝ≥0∞) / (fieldCard Fq : ℝ≥0∞) +
        ((Finset.univ.filter
            (fun jc : Fin 2 × (Fin (extDeg P Fq) → Fq) => jc.2 ⟨0, hd0⟩ = 0 ∧ jc.2 ≠ 0)).card : ℝ≥0∞) *
          ((P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) ^
              (Finset.univ.filter (fun m : Fin P.k₀ => (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m)).card /
            (Fintype.card Fq : ℝ≥0∞) ^
              (Finset.univ.filter (fun m : Fin P.k₀ => (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m)).card) := by
  refine (MeasureTheory.measure_union_le _ _).trans ?_
  gcongr
  · exact hDr_failure_le P Fq Dom hdp hcardq
  · exact hker_failure_le P Fq Dom hd0

/-- **The dual space has `q` elements** (`#Dual = #Fq`): both are `p^d`-element
`Fp`-spaces of the same dimension `d`. Used to simplify the SPREAD measure's
`#{φ≠0}` factor to `≤ q`, giving `P[¬SPREAD] ≤ q·(p^{d-1})^{k₀}/q^{k₀} = p^{d-k₀}`. -/
theorem card_dual_eq [FiniteDimensional (Fp P) Fq]
    [Fintype (Module.Dual (Fp P) Fq)] :
    Fintype.card (Module.Dual (Fp P) Fq) = Fintype.card Fq := by
  rw [Module.card_eq_pow_finrank (K := Fp P) (V := Module.Dual (Fp P) Fq),
    Subspace.dual_finrank_eq, ← Module.card_eq_pow_finrank (K := Fp P) (V := Fq)]

/-- **SPREAD failure measure, clean form**: `P[¬SPREAD] ≤ q·(p^{d-1})^{k₀}/q^{k₀}`,
bounding the `#{φ≠0}` factor of `spread_failure_le` by `#Dual = q` (`card_dual_eq`).
This is the closed `lem:span` Good-set failure contribution to ε₃. -/
theorem spread_failure_le' [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    [Fintype (Module.Dual (Fp P) Fq)] (hcard : Fintype.card (Fp P) = P.p) :
    (challengePMF P Fq Dom).toOuterMeasure
        {ch : Challenges P Fq Dom |
          Submodule.span (Fp P) (Set.range (eqPoly ch.α)) ≠ ⊤} ≤
      (Fintype.card Fq : ℝ≥0∞) *
        ((P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) ^ P.k₀ /
          (Fintype.card Fq : ℝ≥0∞) ^ P.k₀) := by
  refine (spread_failure_le P Fq Dom hcard).trans ?_
  gcongr
  exact (Finset.card_filter_le _ _).trans_eq
    (Finset.card_univ.trans (card_dual_eq P Fq))

/-- **SPREAD + cond:twist combined Good-set failure measure** (ε₃ consolidation):
the union of the SPREAD failure and the cond:twist (`hDr ∧ hker`) failure is bounded
by the sum of their measures (`spread_failure_le'` + `condtwist_failure_le`). Two of
the Good-set conditions whose failure feeds the `prop:pinbound` ε₃ bound. -/
theorem spread_condtwist_failure_le [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    [Fintype (Module.Dual (Fp P) Fq)] [DecidableEq Fq]
    (hcard : Fintype.card (Fp P) = P.p) (hdp : (extDeg P Fq).Prime)
    (hcardq : Fintype.card Fq = P.p ^ extDeg P Fq) (hd0 : 0 < extDeg P Fq) :
    (challengePMF P Fq Dom).toOuterMeasure
      ({ch : Challenges P Fq Dom |
          Submodule.span (Fp P) (Set.range (eqPoly ch.α)) ≠ ⊤} ∪
        ({ch : Challenges P Fq Dom | ¬ ∀ (j : Fin 2) (r : Fin (extDeg P Fq)), (r : ℕ) ≠ 0 →
            ch.α ⟨0, P.k₀_pos⟩ ^ P.p ^ (r : ℕ) - ch.α ⟨0, P.k₀_pos⟩ ≠ 0} ∪
          {ch : Challenges P Fq Dom | ∃ (j : Fin 2) (c : Fin (extDeg P Fq) → Fq),
            c ⟨0, hd0⟩ = 0 ∧ c ≠ 0 ∧ ∀ m : Fin P.k₀, (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m →
              ∑ r, c r * (ch.α m ^ P.p ^ (r : ℕ) - powSeq (ch.z j) P.k₀ m) = 0})) ≤
      (Fintype.card Fq : ℝ≥0∞) *
          ((P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) ^ P.k₀ /
            (Fintype.card Fq : ℝ≥0∞) ^ P.k₀) +
        ((P.p : ℝ≥0∞) / (fieldCard Fq : ℝ≥0∞) +
          ((Finset.univ.filter
              (fun jc : Fin 2 × (Fin (extDeg P Fq) → Fq) => jc.2 ⟨0, hd0⟩ = 0 ∧ jc.2 ≠ 0)).card : ℝ≥0∞) *
            ((P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) ^
                (Finset.univ.filter (fun m : Fin P.k₀ => (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m)).card /
              (Fintype.card Fq : ℝ≥0∞) ^
                (Finset.univ.filter (fun m : Fin P.k₀ => (⟨0, P.k₀_pos⟩ : Fin P.k₀) < m)).card)) := by
  refine (MeasureTheory.measure_union_le _ _).trans ?_
  gcongr
  · exact spread_failure_le' P Fq Dom hcard
  · exact condtwist_failure_le P Fq Dom hdp hcardq hd0

/-- **SPREAD failure measure, cancelled form**: `P[¬SPREAD] ≤ (p^{d-1})^{k₀}/q^{k₀-1}`,
cancelling the `#Dual = q` factor of `spread_failure_le'` against one power of `q`.
The closed `lem:span` ε₃ contribution (`= p^{d-k₀}` since `q = p^d`). -/
theorem spread_failure_le_cancel [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    [Fintype (Module.Dual (Fp P) Fq)] (hcard : Fintype.card (Fp P) = P.p) :
    (challengePMF P Fq Dom).toOuterMeasure
        {ch : Challenges P Fq Dom |
          Submodule.span (Fp P) (Set.range (eqPoly ch.α)) ≠ ⊤} ≤
      (P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) ^ P.k₀ /
        (Fintype.card Fq : ℝ≥0∞) ^ (P.k₀ - 1) := by
  refine (spread_failure_le' P Fq Dom hcard).trans (le_of_eq ?_)
  have hqne : (Fintype.card Fq : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hqtop : (Fintype.card Fq : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [show (Fintype.card Fq : ℝ≥0∞) ^ P.k₀
      = (Fintype.card Fq : ℝ≥0∞) * (Fintype.card Fq : ℝ≥0∞) ^ (P.k₀ - 1) from by
    rw [← pow_succ']; congr 1; have := P.k₀_pos; omega,
    mul_div_assoc', ENNReal.mul_div_mul_left _ _ hqne hqtop]

/-- **`prop:pinbound` ε₃ union bound** (the `Pinning` failure measure): since the
primal construction (`pinning_of_blockFoldSolve`) derives `Pinning` from `R_out`-SPREAD,
`RowSurj`, and `BlockFoldSolve`, and `RowSurj` failure reduces to row-dependence
(`not_rowSurj_subset`), the `Pinning` failure measure is bounded by the sum of the three
component failure measures — the `R_out`-SPREAD (tail-SPREAD), two-point-rank (`ε₂`), and
`cond:cross2` (`BlockFoldSolve`) contributions. The three component bounds are the
remaining `ε₃` measure targets. -/
theorem pinning_failure_le (hmf : MaskFree P Fq S) :
    (challengePMF P Fq Dom).toOuterMeasure {ch | ¬ Pinning P Fq Dom S ch} ≤
      ((challengePMF P Fq Dom).toOuterMeasure
          {ch : Challenges P Fq Dom | ¬ (Submodule.span (Fp P) (Set.range
            (fun s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true} => eqPoly ch.α s.val)) = ⊤)}
        + (challengePMF P Fq Dom).toOuterMeasure
            {ch | ¬ LinearIndependent Fq (rowWeights P Fq Dom ch)})
      + (challengePMF P Fq Dom).toOuterMeasure {ch | ¬ BlockFoldSolve P Fq Dom ch} := by
  refine (MeasureTheory.measure_mono (not_pinning_subset P Fq Dom S hmf)).trans ?_
  refine (MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ le_rfl)
  refine (MeasureTheory.measure_union_le _ _).trans (add_le_add le_rfl ?_)
  exact MeasureTheory.measure_mono (not_rowSurj_subset P Fq Dom)

/-- **The head challenge `α₀` vanishes with probability `≤ 1/q`** (the head factor of the
`R_out`-SPREAD split, `not_Rout_spread_subset`): a single uniform `α`-coordinate equals a
fixed value with probability `1/q`. The degree-1 head event of the `εSPREAD` bound. -/
theorem challenge_alpha0_zero_le :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ch.α ⟨0, P.k₀_pos⟩ = 0} ≤
      (1 : ℝ≥0∞) / (Fintype.card Fq : ℝ≥0∞) := by
  classical
  refine challenge_α_event_le P Fq Dom (fun α => α ⟨0, P.k₀_pos⟩ = 0) _ ?_
  have hset : {α : Fin P.k₀ → Fq | α ⟨0, P.k₀_pos⟩ = 0}
      = {α : Fin P.k₀ → Fq | α ⟨0, P.k₀_pos⟩ ∈ ({0} : Set Fq)} := by
    ext α; simp
  rw [hset]
  refine (uniform_pi_coord_le (⟨0, P.k₀_pos⟩ : Fin P.k₀) ({0} : Set Fq) 1 ?_).trans
    (le_of_eq ?_)
  · intro s hs
    refine (Finset.card_le_card (fun x hx => Finset.mem_singleton.mpr ?_)).trans
      (by simp : ({0} : Finset Fq).card ≤ 1)
    have hx0 := hs x hx
    rwa [Set.mem_singleton_iff] at hx0
  · norm_num

/-- **`BlockFoldSolve` failure measure** (`εBFS`, reduced to `cond:cross2`): by
`not_blockFoldSolve_subset`, the `BlockFoldSolve` failure is covered by `¬NodeHyp` and
`¬CrossSolve`, so its measure is at most `P[¬NodeHyp] + P[¬CrossSolve]`. With `P[¬NodeHyp]`
already bounded (`ε₁`, `nodeHyp_failure_le`), the *only* remaining probability bound in the
entire campaign is `P[¬CrossSolve]` — the `cond:cross2` measure. -/
theorem blockFoldSolve_failure_le (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a) :
    (challengePMF P Fq Dom).toOuterMeasure {ch | ¬ BlockFoldSolve P Fq Dom ch} ≤
      (challengePMF P Fq Dom).toOuterMeasure {ch | ¬ NodeHyp P Fq Dom ch} +
      (challengePMF P Fq Dom).toOuterMeasure {ch | ¬ CrossSolve P Fq Dom ch} :=
  (MeasureTheory.measure_mono (not_blockFoldSolve_subset P Fq Dom hdom hbudget)).trans
    (MeasureTheory.measure_union_le _ _)

/-- **`CrossSolve` failure reduced to the cond:cross2 event measure** (`cond:cross2`, the
final measure target): chaining `not_crossSolve_subset` (`{¬CrossSolve} ⊆ {¬ConfineFoldSurj}`)
with `not_confineFoldSurj_subset` (`⊆` the `cond:cross2` event), the `CrossSolve` failure
measure is bounded by the probability that some nonzero test weight `ψ` has all its per-class
weights `c ↦ tr(ψ_c·êq(α,s))` in `span{confineGen}` — the explicit `M(α)`-rank-deficiency
event. Bounding *this* over `α` (the Schwartz–Zippel rank bound) is the single remaining
probability obligation of the development. -/
theorem crossSolve_failure_le [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] [FiniteDimensional (Fp P) (Cube P.m → Fq)]
    {ιβ : Type*} [Fintype ιβ] (b : Module.Basis ιβ (Fp P) Fq) :
    (challengePMF P Fq Dom).toOuterMeasure {ch | ¬ CrossSolve P Fq Dom ch} ≤
      (challengePMF P Fq Dom).toOuterMeasure
        {ch : Challenges P Fq Dom | ∃ ψ : Cube P.m → Fq, ψ ≠ 0 ∧
          ∀ s, dotFunc (fun c => Algebra.trace (Fp P) Fq (ψ c * eqPoly ch.α s))
            ∈ Submodule.span (Fp P) (Set.range (confineGen P Fq Dom ch b))} :=
  MeasureTheory.measure_mono
    ((not_crossSolve_subset P Fq Dom).trans (not_confineFoldSurj_subset P Fq Dom b))

/-- **Tail-SPREAD failure union bound** (the tail-SPREAD measure skeleton): the probability
that the head-erased tail family misses `⊤` is at most the sum, over nonzero `Fp`-functionals
`φ`, of `P[φ` vanishes on every tail product`]`. By `exists_dual_of_not_tail_spread`, every
`¬tail-SPREAD` challenge lies in some such event; the union over the finite dual is bounded
by the sum. The remaining work is the per-`φ` term (via the tail change-of-basis +
`challenge_alpha_tail_dual_zero_le`). -/
theorem tail_spread_failure_le_sum [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    [Fintype (Module.Dual (Fp P) Fq)] :
    (challengePMF P Fq Dom).toOuterMeasure
        {ch : Challenges P Fq Dom | Submodule.span (Fp P) (Set.range
          (fun s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true} =>
            ∏ i ∈ Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀),
              (if s.val i then ch.α i else 1 - ch.α i))) ≠ ⊤} ≤
      ∑ φ ∈ Finset.univ.filter (fun φ : Module.Dual (Fp P) Fq => φ ≠ 0),
        (challengePMF P Fq Dom).toOuterMeasure
          {ch : Challenges P Fq Dom | ∀ s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true},
            φ (∏ i ∈ Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀),
              (if s.val i then ch.α i else 1 - ch.α i)) = 0} := by
  classical
  have hsub : {ch : Challenges P Fq Dom | Submodule.span (Fp P) (Set.range
        (fun s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true} =>
          ∏ i ∈ Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀),
            (if s.val i then ch.α i else 1 - ch.α i))) ≠ ⊤} ⊆
      ⋃ φ ∈ Finset.univ.filter (fun φ : Module.Dual (Fp P) Fq => φ ≠ 0),
        {ch : Challenges P Fq Dom | ∀ s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true},
          φ (∏ i ∈ Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀),
            (if s.val i then ch.α i else 1 - ch.α i)) = 0} := by
    intro ch hch
    obtain ⟨φ, hφ0, hφv⟩ := exists_dual_of_not_tail_spread P Fq Dom ch hch
    exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ φ, hφ0⟩) hφv
  exact (MeasureTheory.measure_mono hsub).trans
    (MeasureTheory.measure_biUnion_finset_le _ _)

/-- **Tail-SPREAD failure measure** (assembled): the probability that the head-erased
tail family misses `⊤` is at most `#{φ ≠ 0} · (p^{d-1})^{k₀-1}/q^{k₀-1}` — the union bound
`tail_spread_failure_le_sum` combined with the per-`φ` term `tail_spread_term_le`. This is
the remaining `εSPREAD` content; with `Rout_spread_failure_le` it closes the `R_out`-SPREAD
measure entirely. -/
theorem tail_spread_failure_le [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    [Fintype (Module.Dual (Fp P) Fq)] (hcard : Fintype.card (Fp P) = P.p) :
    (challengePMF P Fq Dom).toOuterMeasure
        {ch : Challenges P Fq Dom | Submodule.span (Fp P) (Set.range
          (fun s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true} =>
            ∏ j ∈ Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀),
              (if s.val j then ch.α j else 1 - ch.α j))) ≠ ⊤} ≤
      ((Finset.univ.filter (fun φ : Module.Dual (Fp P) Fq => φ ≠ 0)).card : ℝ≥0∞) *
        ((P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) ^ (P.k₀ - 1) /
          (Fintype.card Fq : ℝ≥0∞) ^ (P.k₀ - 1)) := by
  refine (tail_spread_failure_le_sum P Fq Dom).trans ?_
  calc ∑ φ ∈ Finset.univ.filter (fun φ : Module.Dual (Fp P) Fq => φ ≠ 0),
        (challengePMF P Fq Dom).toOuterMeasure
          {ch : Challenges P Fq Dom | ∀ s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true},
            φ (∏ j ∈ Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀),
              (if s.val j then ch.α j else 1 - ch.α j)) = 0}
      ≤ ∑ _φ ∈ Finset.univ.filter (fun φ : Module.Dual (Fp P) Fq => φ ≠ 0),
          ((P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) ^ (P.k₀ - 1) /
            (Fintype.card Fq : ℝ≥0∞) ^ (P.k₀ - 1)) :=
        Finset.sum_le_sum fun φ hφ =>
          tail_spread_term_le P Fq Dom hcard (Finset.mem_filter.mp hφ).2
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- **`R_out`-SPREAD failure measure** (`εSPREAD` glue): combining the split
`not_Rout_spread_subset` with the head bound `challenge_alpha0_zero_le`, the `R_out`-SPREAD
failure is at most `1/q` (the `α₀ = 0` head event) plus the tail-SPREAD failure. Reduces
`εSPREAD` to the single remaining head-erased tail-SPREAD measure. -/
theorem Rout_spread_failure_le :
    (challengePMF P Fq Dom).toOuterMeasure
        {ch : Challenges P Fq Dom | ¬ (Submodule.span (Fp P) (Set.range
          (fun s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true} => eqPoly ch.α s.val)) = ⊤)} ≤
      (1 : ℝ≥0∞) / (Fintype.card Fq : ℝ≥0∞) +
      (challengePMF P Fq Dom).toOuterMeasure
        {ch : Challenges P Fq Dom | ¬ (Submodule.span (Fp P) (Set.range
          (fun s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true} =>
            ∏ i ∈ Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀),
              (if s.val i then ch.α i else 1 - ch.α i))) = ⊤)} := by
  refine (MeasureTheory.measure_mono (not_Rout_spread_subset P Fq Dom)).trans ?_
  refine (MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ le_rfl)
  exact challenge_alpha0_zero_le P Fq Dom

/-- **`R_out`-SPREAD failure measure, closed form** (`εSPREAD`, fully reduced): combining
`Rout_spread_failure_le` (head split) with the assembled tail bound
`tail_spread_failure_le`, the `R_out`-SPREAD failure has measure at most
`1/q + #{φ≠0}·(p^{d-1})^{k₀-1}/q^{k₀-1}` (no remaining tail hypotheses besides field-card
facts). This fully discharges the `εSPREAD` obligation. -/
theorem Rout_spread_failure_le_closed [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    [Fintype (Module.Dual (Fp P) Fq)] (hcard : Fintype.card (Fp P) = P.p) :
    (challengePMF P Fq Dom).toOuterMeasure
        {ch : Challenges P Fq Dom | ¬ (Submodule.span (Fp P) (Set.range
          (fun s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true} => eqPoly ch.α s.val)) = ⊤)} ≤
      1 / (Fintype.card Fq : ℝ≥0∞) +
        ((Finset.univ.filter (fun φ : Module.Dual (Fp P) Fq => φ ≠ 0)).card : ℝ≥0∞) *
          ((P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) ^ (P.k₀ - 1) /
            (Fintype.card Fq : ℝ≥0∞) ^ (P.k₀ - 1)) :=
  (Rout_spread_failure_le P Fq Dom).trans
    (add_le_add le_rfl (tail_spread_failure_le P Fq Dom hcard))

/-- **Row-dependence failure measure** (`εrow`, the two-point-rank `ε₂` term): composing
`not_rowsLI_subset` with the coupled-genericity bound `coupledGen_failure_le`, the
`rowWeights` linear-dependence event has measure at most `1/q + k₀·d/q` (the `γ = 0` event
plus the `k₀` per-slot determinant events). This is the `εrow` summand of both the
`MaskViewSection` (`ε₂`) and `Pinning` (`ε₃` `RowSurj`-reuse) bounds. -/
theorem rowsLI_failure_le (d : ℕ)
    (hγ : (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ch.γ = 0} ≤ 1 / (fieldCard Fq : ℝ≥0∞))
    (hslot : ∀ m : Fin P.k₀, (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | slotDet Fq P Dom ch m = 0} ≤
        (d : ℝ≥0∞) / (fieldCard Fq : ℝ≥0∞)) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch | ¬ LinearIndependent Fq (rowWeights P Fq Dom ch)} ≤
      1 / (fieldCard Fq : ℝ≥0∞) + (P.k₀ : ℝ≥0∞) * d / (fieldCard Fq : ℝ≥0∞) := by
  refine (MeasureTheory.measure_mono (not_rowsLI_subset P Fq Dom)).trans ?_
  exact coupledGen_failure_le Fq P Dom d hγ hslot

/-- **Row-dependence failure measure, closed form** (`εrow`, fully numeric): plugging the
established `γ = 0` bound (`challenge_gamma_zero_le`) and per-slot determinant bound
(`slotDet_zero_le`) into `rowsLI_failure_le` gives the closed two-point-rank bound
`P[¬rowWeights LI] ≤ 1/q + k₀·(2k₀+1+3·2^{k₀-1})/q` (no remaining measure hypotheses
besides `2 ≠ 0`). This fully discharges the `εrow` obligation. -/
theorem rowsLI_failure_le_closed [Nonempty Fq] (h2 : (2 : Fq) ≠ 0) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch | ¬ LinearIndependent Fq (rowWeights P Fq Dom ch)} ≤
      1 / (fieldCard Fq : ℝ≥0∞) +
        (P.k₀ : ℝ≥0∞) * (2 * P.k₀ + 1 + 3 * 2 ^ (P.k₀ - 1) : ℕ) / (fieldCard Fq : ℝ≥0∞) :=
  rowsLI_failure_le P Fq Dom (2 * P.k₀ + 1 + 3 * 2 ^ (P.k₀ - 1))
    (challenge_gamma_zero_le P Fq Dom) (fun m => slotDet_zero_le P Fq Dom h2 m)

/-- **`GoodSetAbsorption` from the component measure bounds** (the final-assembly
skeleton): combining the node, two-point-rank, `R_out`-SPREAD, and `cond:cross2`
(`BlockFoldSolve`) failure bounds with the absorption assembly
(`goodSetAbsorption_of_bounds`) and the `ε₃` union bound (`pinning_failure_le`),
`GoodSetAbsorption` holds whenever the four component measures sum below `εZK`. This
reduces the whole campaign to its four remaining measure obligations plus the `εZK`
arithmetic — `pinning_of_blockFoldSolve` having discharged all of the linear-algebra
content of `prop:pinbound`/`prop:uniform`. -/
theorem goodSetAbsorption_of_component_bounds [FiniteDimensional (Fp P) Fq]
    (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S) (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (ε₁ εSPREAD εrow εBFS : ℝ≥0∞)
    (hA : (challengePMF P Fq Dom).toOuterMeasure {ch | ¬ NodeHyp P Fq Dom ch} ≤ ε₁)
    (hSPREAD : (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ¬ (Submodule.span (Fp P) (Set.range
        (fun s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true} => eqPoly ch.α s.val)) = ⊤)} ≤ εSPREAD)
    (hrow : (challengePMF P Fq Dom).toOuterMeasure
      {ch | ¬ LinearIndependent Fq (rowWeights P Fq Dom ch)} ≤ εrow)
    (hBFS : (challengePMF P Fq Dom).toOuterMeasure
      {ch | ¬ BlockFoldSolve P Fq Dom ch} ≤ εBFS)
    (hsum : ε₁ + εrow + ((εSPREAD + εrow) + εBFS) ≤ εZK P Fq) :
    GoodSetAbsorption P Fq Dom S := by
  refine goodSetAbsorption_of_bounds P Fq Dom S h2 hmf hdom hbudget ε₁ εrow
    ((εSPREAD + εrow) + εBFS) hA hrow ?_ hsum
  exact (pinning_failure_le P Fq Dom S hmf).trans
    (add_le_add (add_le_add hSPREAD hrow) hBFS)

/-- **`GoodSetAbsorption` from the two genuinely-remaining measures** (final-assembly,
tightened): folding the `R_out`-SPREAD head bound (`Rout_spread_failure_le`) into the
component skeleton, `GoodSetAbsorption` holds given the node measure, the head-erased
tail-SPREAD measure, the two-point-rank measure, and the `cond:cross2` (`BlockFoldSolve`)
measure summing below `εZK`. With `ε₁` (`nodeHyp_failure_le`) and `εrow`
(`rowsLI_failure_le_closed`) already discharged, the campaign's remaining mathematical
content is exactly: the tail-SPREAD measure (`εtail`) and the `cond:cross2` measure
(`εBFS`), plus the `εZK` arithmetic. -/
theorem goodSetAbsorption_of_tail_bounds [FiniteDimensional (Fp P) Fq]
    (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S) (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (ε₁ εtail εrow εBFS : ℝ≥0∞)
    (hA : (challengePMF P Fq Dom).toOuterMeasure {ch | ¬ NodeHyp P Fq Dom ch} ≤ ε₁)
    (htail : (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ¬ (Submodule.span (Fp P) (Set.range
        (fun s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true} =>
          ∏ i ∈ Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀),
            (if s.val i then ch.α i else 1 - ch.α i))) = ⊤)} ≤ εtail)
    (hrow : (challengePMF P Fq Dom).toOuterMeasure
      {ch | ¬ LinearIndependent Fq (rowWeights P Fq Dom ch)} ≤ εrow)
    (hBFS : (challengePMF P Fq Dom).toOuterMeasure
      {ch | ¬ BlockFoldSolve P Fq Dom ch} ≤ εBFS)
    (hsum : ε₁ + εrow +
        (((1 / (Fintype.card Fq : ℝ≥0∞) + εtail) + εrow) + εBFS) ≤ εZK P Fq) :
    GoodSetAbsorption P Fq Dom S := by
  refine goodSetAbsorption_of_component_bounds P Fq Dom S h2 hmf hdom hbudget
    ε₁ (1 / (Fintype.card Fq : ℝ≥0∞) + εtail) εrow εBFS hA ?_ hrow hBFS hsum
  exact (Rout_spread_failure_le P Fq Dom).trans (add_le_add le_rfl htail)

/-- **`GoodSetAbsorption` from the cross-coupling measure** (Phase F, the single-gap form):
folding `blockFoldSolve_failure_le` into the component skeleton, `BlockFoldSolve` failure is
`≤ ε₁ + εCross`, so `GoodSetAbsorption` holds given the node (`ε₁`), `R_out`-SPREAD
(`εSPREAD`), two-point-rank (`εrow`), and **cross-coupling (`εCross`)** measures summing
below `εZK`. With `ε₁`/`εSPREAD`/`εrow` all discharged by closed lemmas
(`nodeHyp_failure_le`, `Rout_spread_failure_le_closed`, `rowsLI_failure_le_closed`), the
*entire* campaign rests on the single `cond:cross2` measure `P[¬CrossSolve] ≤ εCross` plus
the `εZK` arithmetic. -/
theorem goodSetAbsorption_of_crossSolve_bound [FiniteDimensional (Fp P) Fq]
    (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S) (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (ε₁ εSPREAD εrow εCross : ℝ≥0∞)
    (hA : (challengePMF P Fq Dom).toOuterMeasure {ch | ¬ NodeHyp P Fq Dom ch} ≤ ε₁)
    (hSPREAD : (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ¬ (Submodule.span (Fp P) (Set.range
        (fun s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true} => eqPoly ch.α s.val)) = ⊤)} ≤ εSPREAD)
    (hrow : (challengePMF P Fq Dom).toOuterMeasure
      {ch | ¬ LinearIndependent Fq (rowWeights P Fq Dom ch)} ≤ εrow)
    (hcross : (challengePMF P Fq Dom).toOuterMeasure
      {ch | ¬ CrossSolve P Fq Dom ch} ≤ εCross)
    (hsum : ε₁ + εrow + ((εSPREAD + εrow) + (ε₁ + εCross)) ≤ εZK P Fq) :
    GoodSetAbsorption P Fq Dom S := by
  refine goodSetAbsorption_of_component_bounds P Fq Dom S h2 hmf hdom hbudget
    ε₁ εSPREAD εrow (ε₁ + εCross) hA hSPREAD hrow ?_ hsum
  exact (blockFoldSolve_failure_le P Fq Dom hdom hbudget).trans (add_le_add hA hcross)

/-- **`GoodSetAbsorption` from the cond:cross2 event measure** (Phase F, master single-gap
form): composing `goodSetAbsorption_of_crossSolve_bound` with `crossSolve_failure_le`, the
`CrossSolve` measure obligation becomes the explicit `cond:cross2` event measure — the
probability that some nonzero `ψ` has all its per-class weights `c ↦ tr(ψ_c·êq(α,s))` in
`span{confineGen}`. So, modulo the three already-closed measures (`nodeHyp_failure_le`,
`Rout_spread_failure_le_closed`, `rowsLI_failure_le_closed`) and the `εZK` arithmetic, the
**entire** masked-WHIR zero-knowledge proof rests on bounding this one Schwartz–Zippel
rank event over `α`. -/
theorem goodSetAbsorption_of_condCross2_event [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] [FiniteDimensional (Fp P) (Cube P.m → Fq)]
    {ιβ : Type*} [Fintype ιβ] (b : Module.Basis ιβ (Fp P) Fq)
    (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S) (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (ε₁ εSPREAD εrow εCross : ℝ≥0∞)
    (hA : (challengePMF P Fq Dom).toOuterMeasure {ch | ¬ NodeHyp P Fq Dom ch} ≤ ε₁)
    (hSPREAD : (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ¬ (Submodule.span (Fp P) (Set.range
        (fun s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true} => eqPoly ch.α s.val)) = ⊤)} ≤ εSPREAD)
    (hrow : (challengePMF P Fq Dom).toOuterMeasure
      {ch | ¬ LinearIndependent Fq (rowWeights P Fq Dom ch)} ≤ εrow)
    (hcross2 : (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ∃ ψ : Cube P.m → Fq, ψ ≠ 0 ∧
        ∀ s, dotFunc (fun c => Algebra.trace (Fp P) Fq (ψ c * eqPoly ch.α s))
          ∈ Submodule.span (Fp P) (Set.range (confineGen P Fq Dom ch b))} ≤ εCross)
    (hsum : ε₁ + εrow + ((εSPREAD + εrow) + (ε₁ + εCross)) ≤ εZK P Fq) :
    GoodSetAbsorption P Fq Dom S :=
  goodSetAbsorption_of_crossSolve_bound P Fq Dom S h2 hmf hdom hbudget ε₁ εSPREAD εrow εCross
    hA hSPREAD hrow ((crossSolve_failure_le P Fq Dom b).trans hcross2) hsum

/-- **`GoodSetAbsorption` from the shared good set** (Phase F, no double-counting): the good
set is the intersection of node genericity, row independence, `R_out`-SPREAD, and
cross-coupling. On it, `MaskViewSection` holds (`maskViewSection_of_rowSurj` via
`NodeHyp` + `rowsLI`) and `Pinning` holds (`pinning_of_blockFoldSolve` via SPREAD +
`rowsLI`→`RowSurj` + `NodeHyp`+`CrossSolve`→`BlockFoldSolve`) — *reusing the same `NodeHyp`
and `rowWeights` conditions rather than re-charging their measures*. So the complement
measure is the sum of the four failure measures **each counted once**:
`P[¬NodeHyp] + P[¬rowWeights LI] + P[¬R_out-SPREAD] + P[¬CrossSolve] ≤ εZK`. This is the
correct (non-double-counting) `εZK` budget — node ↔ node term, rows ↔ two-point term, SPREAD
↔ spread term, cross ↔ `cond:cross2` term. -/
theorem goodSetAbsorption_of_shared [FiniteDimensional (Fp P) Fq]
    (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S) (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (ε₁ εSPREAD εrow εCross : ℝ≥0∞)
    (hA : (challengePMF P Fq Dom).toOuterMeasure {ch | ¬ NodeHyp P Fq Dom ch} ≤ ε₁)
    (hSPREAD : (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ¬ (Submodule.span (Fp P) (Set.range
        (fun s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true} => eqPoly ch.α s.val)) = ⊤)} ≤ εSPREAD)
    (hrow : (challengePMF P Fq Dom).toOuterMeasure
      {ch | ¬ LinearIndependent Fq (rowWeights P Fq Dom ch)} ≤ εrow)
    (hcross : (challengePMF P Fq Dom).toOuterMeasure
      {ch | ¬ CrossSolve P Fq Dom ch} ≤ εCross)
    (hsum : ε₁ + εrow + εSPREAD + εCross ≤ εZK P Fq) :
    GoodSetAbsorption P Fq Dom S := by
  classical
  refine goodSetAbsorption_of_predicates P Fq Dom S h2 hmf
    {ch : Challenges P Fq Dom | NodeHyp P Fq Dom ch ∧
      LinearIndependent Fq (rowWeights P Fq Dom ch) ∧
      (Submodule.span (Fp P) (Set.range
        (fun s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true} => eqPoly ch.α s.val)) = ⊤) ∧
      CrossSolve P Fq Dom ch} ?_ ?_
  · -- complement measure ≤ sum of the four (each once)
    have hsub : {ch : Challenges P Fq Dom | NodeHyp P Fq Dom ch ∧
        LinearIndependent Fq (rowWeights P Fq Dom ch) ∧
        (Submodule.span (Fp P) (Set.range
          (fun s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true} => eqPoly ch.α s.val)) = ⊤) ∧
        CrossSolve P Fq Dom ch}ᶜ ⊆
        (({ch | ¬ NodeHyp P Fq Dom ch} ∪
          {ch | ¬ LinearIndependent Fq (rowWeights P Fq Dom ch)}) ∪
          {ch : Challenges P Fq Dom | ¬ (Submodule.span (Fp P) (Set.range
            (fun s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true} => eqPoly ch.α s.val)) = ⊤)}) ∪
          {ch | ¬ CrossSolve P Fq Dom ch} := by
      intro ch hch
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or] at hch
      rcases hch with h | h | h | h
      · exact Or.inl (Or.inl (Or.inl h))
      · exact Or.inl (Or.inl (Or.inr h))
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    refine (MeasureTheory.measure_mono hsub).trans ?_
    refine le_trans (MeasureTheory.measure_union_le _ _) ?_
    refine le_trans (add_le_add (MeasureTheory.measure_union_le _ _) le_rfl) ?_
    refine le_trans
      (add_le_add (add_le_add (MeasureTheory.measure_union_le _ _) le_rfl) le_rfl) ?_
    exact le_trans (add_le_add (add_le_add (add_le_add hA hrow) hSPREAD) hcross) hsum
  · intro ch hch
    obtain ⟨hnode, hrowli, hsp, hcr⟩ := hch
    exact ⟨maskViewSection_of_rowSurj P Fq Dom S ch hmf hdom hbudget hnode
        (rowSurj_of_rowsLI P Fq Dom ch hrowli),
      pinning_of_blockFoldSolve P Fq Dom S ch hmf hsp
        (rowSurj_of_rowsLI P Fq Dom ch hrowli)
        (blockFoldSolve_of_nodeHyp_crossSolve P Fq Dom ch hdom hbudget hnode hcr)⟩

end ZkWhir
