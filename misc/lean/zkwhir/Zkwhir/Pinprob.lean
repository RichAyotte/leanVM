/-
ε₃ measure bounds for `prop:pinbound` / `cond:pinning`: the Good-set failure
probabilities for the slice/cross conditions, assembled from the multivariate
Schwartz–Zippel chain (`SlotProb`) and the cross-form objects (`Pinning`).

Part of the `GoodSetAbsorption` formalization campaign.
-/
import Mathlib
import Zkwhir.Pinning
import Zkwhir.SlotProb
import Zkwhir.Span

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

/-- **SPREAD-failure union bound over hyperplanes through `1`** (`lem:span`, Gap A tightening):
restricting the union to functionals that also vanish at `1` (`exists_dual_of_not_spread_at_one`).
This drops the index set from all `q − 1` nonzero duals to the `≈ p^{d-1}` duals on the
hyperplane `{φ : φ 1 = 0}` — a factor-`p` tightening toward the sharp `lem:span` bound (and,
after quotienting by scaling, the `~p^{d-2}` hyperplanes through `1` giving `~p/q`). -/
theorem spread_failure_le_at_one_sum [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    [Fintype (Module.Dual (Fp P) Fq)] :
    (challengePMF P Fq Dom).toOuterMeasure
        {ch : Challenges P Fq Dom |
          Submodule.span (Fp P) (Set.range (eqPoly ch.α)) ≠ ⊤} ≤
      ∑ φ ∈ Finset.univ.filter (fun φ : Module.Dual (Fp P) Fq => φ ≠ 0 ∧ φ 1 = 0),
        (challengePMF P Fq Dom).toOuterMeasure
          {ch : Challenges P Fq Dom | ∀ s, φ (eqPoly ch.α s) = 0} := by
  classical
  have hsub : {ch : Challenges P Fq Dom |
        Submodule.span (Fp P) (Set.range (eqPoly ch.α)) ≠ ⊤} ⊆
      ⋃ φ ∈ Finset.univ.filter (fun φ : Module.Dual (Fp P) Fq => φ ≠ 0 ∧ φ 1 = 0),
        {ch : Challenges P Fq Dom | ∀ s, φ (eqPoly ch.α s) = 0} := by
    intro ch hch
    obtain ⟨φ, hφ0, hφ1, hφv⟩ := exists_dual_of_not_spread_at_one P Fq Dom ch hch
    exact Set.mem_biUnion (Finset.mem_filter.mpr ⟨Finset.mem_univ φ, hφ0, hφ1⟩) hφv
  exact (MeasureTheory.measure_mono hsub).trans
    (MeasureTheory.measure_biUnion_finset_le _ _)

/-- **Hyperplane count** (`lem:span`, Gap A cardinality): the duals vanishing at `1` form the
annihilator of the line `span{1}`, of dimension `d − 1`, so there are at most `p^{d-1}` of
them. This is the cardinality factor for `spread_failure_le_at_one_sum`, replacing the loose
`#Dual = q = p^d` by `p^{d-1}` (a factor `p` toward the sharp `lem:span` bound). -/
theorem card_dual_at_one_le [FiniteDimensional (Fp P) Fq]
    [Fintype (Module.Dual (Fp P) Fq)]
    (hcard : Fintype.card (Fp P) = P.p) :
    (Finset.univ.filter (fun φ : Module.Dual (Fp P) Fq => φ ≠ 0 ∧ φ 1 = 0)).card
      ≤ P.p ^ (Module.finrank (Fp P) Fq - 1) := by
  classical
  set W : Submodule (Fp P) Fq := Submodule.span (Fp P) {(1 : Fq)} with hW
  have hWrank : Module.finrank (Fp P) W = 1 := by
    rw [hW, finrank_span_singleton (one_ne_zero : (1 : Fq) ≠ 0)]
  have hannrank : Module.finrank (Fp P) (W.dualAnnihilator) = Module.finrank (Fp P) Fq - 1 := by
    have hsum := Subspace.finrank_add_finrank_dualAnnihilator_eq W
    omega
  have hcardann : Fintype.card (W.dualAnnihilator) = P.p ^ (Module.finrank (Fp P) Fq - 1) := by
    rw [Module.card_eq_pow_finrank (K := Fp P), hcard, hannrank]
  calc (Finset.univ.filter (fun φ : Module.Dual (Fp P) Fq => φ ≠ 0 ∧ φ 1 = 0)).card
      ≤ (W.dualAnnihilator : Set (Module.Dual (Fp P) Fq)).toFinset.card := by
        apply Finset.card_le_card
        intro φ hφ
        rw [Finset.mem_filter] at hφ
        rw [Set.mem_toFinset, SetLike.mem_coe, Submodule.mem_dualAnnihilator]
        intro w hw
        rw [hW, Submodule.mem_span_singleton] at hw
        obtain ⟨c, rfl⟩ := hw
        rw [map_smul, hφ.2.2, smul_zero]
    _ = P.p ^ (Module.finrank (Fp P) Fq - 1) := by
        rw [Set.toFinset_card]; exact hcardann

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

/-- **SPREAD failure measure, at-one (`lem:span`, Gap A affine count)**: combining the
hyperplane-through-`1` union bound `spread_failure_le_at_one_sum` with the per-term bound
`spread_term_le` and the cardinality `card_dual_at_one_le` (`#{φ≠0 ∣ φ1=0} ≤ p^{d-1}`),
the SPREAD-failure probability is `≤ p^{d-1} · (p^{d-1})^{k₀}/q^{k₀}`. With `q = p^d` this
is `p^{(d-1)(k₀+1) − d·k₀} = p^{d-1-k₀}` — a factor `p` sharper than the all-dual
`spread_failure_le` (which uses `#Dual = q`), since `1 ∈ span(êq(α,·))` always forces the
witnessing dual to lie on the codim-1 hyperplane `{φ 1 = 0}`. -/
theorem spread_failure_le_at_one [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    [Fintype (Module.Dual (Fp P) Fq)] (hcard : Fintype.card (Fp P) = P.p) :
    (challengePMF P Fq Dom).toOuterMeasure
        {ch : Challenges P Fq Dom |
          Submodule.span (Fp P) (Set.range (eqPoly ch.α)) ≠ ⊤} ≤
      (P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) *
        ((P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) ^ P.k₀ /
          (Fintype.card Fq : ℝ≥0∞) ^ P.k₀) := by
  refine (spread_failure_le_at_one_sum P Fq Dom).trans ?_
  calc ∑ φ ∈ Finset.univ.filter (fun φ : Module.Dual (Fp P) Fq => φ ≠ 0 ∧ φ 1 = 0),
        (challengePMF P Fq Dom).toOuterMeasure
          {ch : Challenges P Fq Dom | ∀ s, φ (eqPoly ch.α s) = 0}
      ≤ ∑ _φ ∈ Finset.univ.filter (fun φ : Module.Dual (Fp P) Fq => φ ≠ 0 ∧ φ 1 = 0),
          ((P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) ^ P.k₀ /
            (Fintype.card Fq : ℝ≥0∞) ^ P.k₀) :=
        Finset.sum_le_sum fun φ hφ =>
          spread_term_le P Fq Dom hcard (Finset.mem_filter.mp hφ).2.1
    _ = ((Finset.univ.filter
            (fun φ : Module.Dual (Fp P) Fq => φ ≠ 0 ∧ φ 1 = 0)).card : ℝ≥0∞) *
          ((P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) ^ P.k₀ /
            (Fintype.card Fq : ℝ≥0∞) ^ P.k₀) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) *
          ((P.p ^ (Module.finrank (Fp P) Fq - 1) : ℝ≥0∞) ^ P.k₀ /
            (Fintype.card Fq : ℝ≥0∞) ^ P.k₀) := by
        gcongr
        exact_mod_cast card_dual_at_one_le P Fq hcard

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

/-- **Bridge to `eqSpan` (`lem:span`).** The code's tail-SPREAD span — over the
subtype `{s // s₀ = true}` of the head-erased products `∏_{i≠0}(sᵢ ? αᵢ : 1−αᵢ)` —
coincides with `eqSpan ch.α (univ.erase 0)` (the `def:spread` fold-multiplier family
over all assignments `s : Fin k₀ → Bool`). The `s₀ = true` constraint is irrelevant
since the product omits coordinate `0`, and every assignment is realized by some
subtype element (`update s 0 true`). This lets the sharp `eqSpan_eq_top` criterion
replace the lossy union-over-duals bound. -/
theorem tail_spread_span_eq (ch : Challenges P Fq Dom) :
    Submodule.span (Fp P) (Set.range
        (fun s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true} =>
          ∏ i ∈ Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀),
            (if s.val i then ch.α i else 1 - ch.α i))) =
      eqSpan (K := Fp P) ch.α (Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀)) := by
  unfold eqSpan
  rw [Set.image_univ]
  congr 1
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s.val, rfl⟩
  · rintro ⟨s, rfl⟩
    refine ⟨⟨Function.update s (⟨0, P.k₀_pos⟩ : Fin P.k₀) true, by simp⟩, ?_⟩
    show (∏ i ∈ Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀),
        (if Function.update s (⟨0, P.k₀_pos⟩ : Fin P.k₀) true i then ch.α i else 1 - ch.α i)) = _
    apply Finset.prod_congr rfl
    intro i hi
    simp only [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

open scoped Classical in
/-- **Sharp tail-SPREAD failure criterion** (`lem:span` contrapositive): if the tail
fold-multiplier family fails to span (`¬ eqSpan = ⊤`), then by `eqSpan_eq_top` fewer
than `d − 1` of the `k₀ − 1` tail coordinates lie outside `Fp`. This is the event
whose probability `B (p/q)^e` (binomial tail over the `≥ k₀ − d + 1` coordinates that
must therefore lie *inside* `Fp`) gives the sharp `εSPREAD`, replacing the lossy
union-over-duals bound. -/
theorem tail_spread_fail_outside (hprime : (Module.finrank (Fp P) Fq).Prime)
    (ch : Challenges P Fq Dom)
    (hfail : ¬ (eqSpan (K := Fp P) ch.α
        (Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀)) = ⊤)) :
    ((Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀)).filter
        (fun i => ch.α i ∉ Set.range (algebraMap (Fp P) Fq))).card <
      Module.finrank (Fp P) Fq - 1 := by
  by_contra h
  push_neg at h
  apply hfail
  apply eqSpan_eq_top hprime ch.α
  rw [Finset.filter_congr_decidable] at h ⊢
  exact h

open scoped Classical in
/-- **Sharp tail-SPREAD failure inside-count** (`lem:span`): if the tail family fails to
span, then *at least* `k₀ − d + 1` of the `k₀ − 1` tail coordinates lie inside `Fp`. The
complement count of `tail_spread_fail_outside`, obtained by the filter partition
(`#inside + #outside = k₀ − 1`). This is the event whose probability is the binomial
tail `B (p/q)^e`. -/
theorem tail_spread_fail_inside (hprime : (Module.finrank (Fp P) Fq).Prime)
    (hdk : Module.finrank (Fp P) Fq ≤ P.k₀)
    (ch : Challenges P Fq Dom)
    (hfail : ¬ (eqSpan (K := Fp P) ch.α
        (Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀)) = ⊤)) :
    P.k₀ - Module.finrank (Fp P) Fq + 1 ≤
      ((Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀)).filter
        (fun i => ch.α i ∈ Set.range (algebraMap (Fp P) Fq))).card := by
  have hout := tail_spread_fail_outside P Fq Dom hprime ch hfail
  have hEcard : (Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀)).card = P.k₀ - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hpart := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀))
    (fun i => ch.α i ∈ Set.range (algebraMap (Fp P) Fq))
  have hdp := hprime.two_le
  omega

/-- **Joint prime-field bound over a coordinate subset** (`lem:span` binomial step): under
the challenge distribution, the event that every `α`-coordinate in a fixed set `J` lies in
the prime field `Fp` has probability at most `(p/q)^{|J|}`. Mirrors
`challenge_alpha_tail_dual_zero_le` with the per-coordinate set `{a ∈ Fp}` (`card ≤ p`,
`card_base_range_le`). -/
theorem challenge_alpha_primefield_joint_le (J : Finset (Fin P.k₀)) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ∀ i ∈ J, ch.α i ∈ Set.range (algebraMap (Fp P) Fq)} ≤
      (P.p : ℝ≥0∞) ^ J.card / (Fintype.card Fq : ℝ≥0∞) ^ J.card := by
  classical
  refine challenge_α_event_le P Fq Dom
    (fun α => ∀ i ∈ J, α i ∈ Set.range (algebraMap (Fp P) Fq)) _ ?_
  have h := uniform_pi_subset (ι := Fin P.k₀) (β := Fq) J
    (fun _ => Finset.univ.filter (fun a : Fq => a ∈ Set.range (algebraMap (Fp P) Fq)))
    P.p
    (fun _ _ => card_base_range_le P Fq _ (fun a ha => (Finset.mem_filter.mp ha).2))
  have hset : {α : Fin P.k₀ → Fq | ∀ i ∈ J, α i ∈ Set.range (algebraMap (Fp P) Fq)}
      = {f : Fin P.k₀ → Fq | ∀ j ∈ J,
          f j ∈ Finset.univ.filter (fun a : Fq => a ∈ Set.range (algebraMap (Fp P) Fq))} := by
    ext α
    simp only [Set.mem_setOf_eq, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hset]
  exact h

open scoped Classical in
/-- **Sharp tail-SPREAD failure measure** (`lem:spread`/`lem:span`): the head-erased tail
fold-multiplier family misses `⊤` with probability at most `B · (p/q)^e`, where `e = k₀−d+1`
and `B = C(k₀−1, e)`. By `tail_spread_fail_inside`, failure forces at least `e` of the
`k₀−1` tail coordinates into `Fp`; the event is covered by the `C(k₀−1, e)` choices of which
`e` coordinates, each of probability `(p/q)^e` (`challenge_alpha_primefield_joint_le`). This
is the **sharp** `εSPREAD` matching the trusted `εZK` spread term, replacing the lossy
union-over-duals `tail_spread_failure_le`. -/
theorem tail_spread_failure_le_sharp (hprime : (Module.finrank (Fp P) Fq).Prime)
    (hdk : Module.finrank (Fp P) Fq ≤ P.k₀) :
    (challengePMF P Fq Dom).toOuterMeasure
        {ch : Challenges P Fq Dom | Submodule.span (Fp P) (Set.range
          (fun s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true} =>
            ∏ j ∈ Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀),
              (if s.val j then ch.α j else 1 - ch.α j))) ≠ ⊤} ≤
      (((P.k₀ - 1).choose (P.k₀ - Module.finrank (Fp P) Fq + 1) : ℕ) : ℝ≥0∞) *
        ((P.p : ℝ≥0∞) ^ (P.k₀ - Module.finrank (Fp P) Fq + 1) /
          (Fintype.card Fq : ℝ≥0∞) ^ (P.k₀ - Module.finrank (Fp P) Fq + 1)) := by
  have hEcard : (Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀)).card = P.k₀ - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hsub : {ch : Challenges P Fq Dom | Submodule.span (Fp P) (Set.range
        (fun s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true} =>
          ∏ j ∈ Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀),
            (if s.val j then ch.α j else 1 - ch.α j))) ≠ ⊤} ⊆
      ⋃ J ∈ (Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀)).powersetCard
            (P.k₀ - Module.finrank (Fp P) Fq + 1),
        {ch : Challenges P Fq Dom |
          ∀ i ∈ J, ch.α i ∈ Set.range (algebraMap (Fp P) Fq)} := by
    intro ch hch
    rw [Set.mem_setOf_eq, tail_spread_span_eq P Fq Dom ch] at hch
    obtain ⟨J, hJsub, hJcard⟩ :=
      Finset.exists_subset_card_eq (tail_spread_fail_inside P Fq Dom hprime hdk ch hch)
    refine Set.mem_biUnion (Finset.mem_powersetCard.mpr
      ⟨hJsub.trans (Finset.filter_subset _ _), hJcard⟩) ?_
    intro i hi
    exact (Finset.mem_filter.mp (hJsub hi)).2
  refine (MeasureTheory.measure_mono hsub).trans ?_
  refine (MeasureTheory.measure_biUnion_finset_le _ _).trans ?_
  calc ∑ J ∈ (Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀)).powersetCard
          (P.k₀ - Module.finrank (Fp P) Fq + 1),
        (challengePMF P Fq Dom).toOuterMeasure
          {ch : Challenges P Fq Dom | ∀ i ∈ J, ch.α i ∈ Set.range (algebraMap (Fp P) Fq)}
      ≤ ∑ _J ∈ (Finset.univ.erase (⟨0, P.k₀_pos⟩ : Fin P.k₀)).powersetCard
          (P.k₀ - Module.finrank (Fp P) Fq + 1),
          ((P.p : ℝ≥0∞) ^ (P.k₀ - Module.finrank (Fp P) Fq + 1) /
            (Fintype.card Fq : ℝ≥0∞) ^ (P.k₀ - Module.finrank (Fp P) Fq + 1)) :=
        Finset.sum_le_sum fun J hJ => by
          have h := challenge_alpha_primefield_joint_le P Fq Dom J
          rwa [(Finset.mem_powersetCard.mp hJ).2] at h
    _ = _ := by
        rw [Finset.sum_const, Finset.card_powersetCard, hEcard, nsmul_eq_mul]

open scoped Classical in
/-- **Generic SPREAD-failure measure over a coordinate subset** (`lem:span`/`lem:spread`,
reusable): for *any* coordinate set `J ⊆ Fin k₀`, the `êq`-product family
`∏_{i∈J} (b_i ? α_i : 1−α_i)` fails to span `Fq` over `Fp` with probability at most
`C(|J|, |J|−(d−2)) · (p/q)^{|J|−(d−2)}`. By `eqSpan_eq_top` (`lem:span`), failure forces fewer
than `d−1` of the `J`-coordinates outside `Fp`, i.e. at least `|J|−(d−2)` inside; the event is
covered by the `C(|J|, |J|−(d−2))` choices of which coordinates lie in `Fp`, each of probability
`(p/q)^{…}` (`challenge_alpha_primefield_joint_le`). This is the index-set-generic form of
`tail_spread_failure_le_sharp` — it instantiates to **condition (i) of `lem:fullslice`** (the
`E'(π)` multipliers, `J = {i : m ≤ i < ℓ}`) and to the R_out SPREAD alike. -/
theorem spread_failure_le_subset (hprime : (Module.finrank (Fp P) Fq).Prime)
    (J : Finset (Fin P.k₀)) :
    (challengePMF P Fq Dom).toOuterMeasure
        {ch : Challenges P Fq Dom | eqSpan (K := Fp P) ch.α J ≠ ⊤} ≤
      ((J.card.choose (J.card - (Module.finrank (Fp P) Fq - 2)) : ℕ) : ℝ≥0∞) *
        ((P.p : ℝ≥0∞) ^ (J.card - (Module.finrank (Fp P) Fq - 2)) /
          (Fintype.card Fq : ℝ≥0∞) ^ (J.card - (Module.finrank (Fp P) Fq - 2))) := by
  set e := J.card - (Module.finrank (Fp P) Fq - 2) with he
  have hsub : {ch : Challenges P Fq Dom | eqSpan (K := Fp P) ch.α J ≠ ⊤} ⊆
      ⋃ K ∈ J.powersetCard e,
        {ch : Challenges P Fq Dom | ∀ i ∈ K, ch.α i ∈ Set.range (algebraMap (Fp P) Fq)} := by
    intro ch hch
    have hout : (J.filter (fun a => ¬ (ch.α a ∈ Set.range (algebraMap (Fp P) Fq)))).card
        < Module.finrank (Fp P) Fq - 1 := by
      by_contra h
      push_neg at h
      apply hch
      apply eqSpan_eq_top hprime ch.α J
      rw [Finset.filter_congr_decidable] at h ⊢
      exact h
    have h2 : (J.filter (fun a => ¬ (ch.α a ∈ Set.range (algebraMap (Fp P) Fq)))).card
        = J.card - (J.filter (fun i => ch.α i ∈ Set.range (algebraMap (Fp P) Fq))).card := by
      rw [Finset.filter_not, Finset.card_sdiff,
        Finset.inter_eq_left.mpr (Finset.filter_subset _ _)]
    have hle : (J.filter (fun i => ch.α i ∈ Set.range (algebraMap (Fp P) Fq))).card ≤ J.card :=
      Finset.card_filter_le _ _
    have hdp := hprime.two_le
    have hin : e ≤ (J.filter (fun i => ch.α i ∈ Set.range (algebraMap (Fp P) Fq))).card := by
      rw [he]; omega
    obtain ⟨K, hKsub, hKcard⟩ := Finset.exists_subset_card_eq hin
    refine Set.mem_biUnion (Finset.mem_powersetCard.mpr
      ⟨hKsub.trans (Finset.filter_subset _ _), hKcard⟩) ?_
    intro i hi
    exact (Finset.mem_filter.mp (hKsub hi)).2
  refine (MeasureTheory.measure_mono hsub).trans ?_
  refine (MeasureTheory.measure_biUnion_finset_le _ _).trans ?_
  calc ∑ K ∈ J.powersetCard e,
        (challengePMF P Fq Dom).toOuterMeasure
          {ch : Challenges P Fq Dom | ∀ i ∈ K, ch.α i ∈ Set.range (algebraMap (Fp P) Fq)}
      ≤ ∑ _K ∈ J.powersetCard e,
          ((P.p : ℝ≥0∞) ^ e / (Fintype.card Fq : ℝ≥0∞) ^ e) :=
        Finset.sum_le_sum fun K hK => by
          have h := challenge_alpha_primefield_joint_le P Fq Dom K
          rwa [(Finset.mem_powersetCard.mp hK).2] at h
    _ = _ := by rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]

open scoped Classical in
/-- **Condition (i) span ↔ `eqSpan` bridge** (`lem:fullslice` (i)): the subtype-indexed
`E'(π)` multiplier family of `crossTerm_trace_ne_zero`'s `hspan` (products over
`{i // m ≤ i < ℓ} → Bool`) spans the same submodule as `eqSpan` over the coordinate `Finset`
`{i : m ≤ i < ℓ}`. Reindexing the subtype product to the filtered `Finset` (`Finset.prod_subtype`)
and matching the `π`/`b` Boolean domains (each `J`-product depends only on the restriction). With
`spread_failure_le_subset`, this turns `crossTerm_trace_ne_zero`'s `hspan` hypothesis into the
measurable condition-(i) SPREAD event. -/
theorem hspan_eq_eqSpan (ch : Challenges P Fq Dom) (m ℓ : Fin P.k₀) :
    Submodule.span (Fp P) (Set.range
        (fun π : {i : Fin P.k₀ // m ≤ i ∧ i < ℓ} → Bool =>
          ∏ j : {i : Fin P.k₀ // m ≤ i ∧ i < ℓ},
            if π j then ch.α j.val else 1 - ch.α j.val))
      = eqSpan (K := Fp P) ch.α (Finset.univ.filter (fun i : Fin P.k₀ => m ≤ i ∧ i < ℓ)) := by
  unfold eqSpan
  rw [Set.image_univ]
  congr 1
  ext x
  simp only [Set.mem_range]
  constructor
  · rintro ⟨π, rfl⟩
    refine ⟨fun i => if h : m ≤ i ∧ i < ℓ then π ⟨i, h⟩ else false, ?_⟩
    rw [Finset.prod_subtype (p := fun i : Fin P.k₀ => m ≤ i ∧ i < ℓ)
        (Finset.univ.filter (fun i : Fin P.k₀ => m ≤ i ∧ i < ℓ))
        (fun i => by simp)
        (fun i => if (if h : m ≤ i ∧ i < ℓ then π ⟨i, h⟩ else false) then ch.α i else 1 - ch.α i)]
    apply Finset.prod_congr rfl
    intro j _
    rw [dif_pos j.2, Subtype.coe_eta]
  · rintro ⟨b, rfl⟩
    refine ⟨fun j => b j.val, ?_⟩
    rw [Finset.prod_subtype (p := fun i : Fin P.k₀ => m ≤ i ∧ i < ℓ)
        (Finset.univ.filter (fun i : Fin P.k₀ => m ≤ i ∧ i < ℓ))
        (fun i => by simp)
        (fun i => if b i then ch.α i else 1 - ch.α i)]

open scoped Classical in
/-- **Condition (i) failure measure** (`lem:fullslice` (i), assembled): the probability that the
`E'(π)` multiplier family of `crossTerm_trace_ne_zero`'s `hspan` fails to span `Fq` is at most
`C(|J|, |J|−(d−2)) · (p/q)^{|J|−(d−2)}` with `J = {i : m ≤ i < ℓ}`. Composes the bridge
`hspan_eq_eqSpan` with the generic `spread_failure_le_subset`. This is the condition-(i) term of
`εCross`, supplying the `hspan` hypothesis of `crossTerm_trace_ne_zero` outside a small event. -/
theorem cond_i_failure_le (hprime : (Module.finrank (Fp P) Fq).Prime) (m ℓ : Fin P.k₀) :
    (challengePMF P Fq Dom).toOuterMeasure
        {ch : Challenges P Fq Dom | Submodule.span (Fp P) (Set.range
          (fun π : {i : Fin P.k₀ // m ≤ i ∧ i < ℓ} → Bool =>
            ∏ j : {i : Fin P.k₀ // m ≤ i ∧ i < ℓ},
              if π j then ch.α j.val else 1 - ch.α j.val)) ≠ ⊤} ≤
      (((Finset.univ.filter (fun i : Fin P.k₀ => m ≤ i ∧ i < ℓ)).card.choose
            ((Finset.univ.filter (fun i : Fin P.k₀ => m ≤ i ∧ i < ℓ)).card
              - (Module.finrank (Fp P) Fq - 2)) : ℕ) : ℝ≥0∞) *
        ((P.p : ℝ≥0∞) ^ ((Finset.univ.filter (fun i : Fin P.k₀ => m ≤ i ∧ i < ℓ)).card
              - (Module.finrank (Fp P) Fq - 2)) /
          (Fintype.card Fq : ℝ≥0∞) ^ ((Finset.univ.filter (fun i : Fin P.k₀ => m ≤ i ∧ i < ℓ)).card
              - (Module.finrank (Fp P) Fq - 2))) := by
  have hset : {ch : Challenges P Fq Dom | Submodule.span (Fp P) (Set.range
        (fun π : {i : Fin P.k₀ // m ≤ i ∧ i < ℓ} → Bool =>
          ∏ j : {i : Fin P.k₀ // m ≤ i ∧ i < ℓ},
            if π j then ch.α j.val else 1 - ch.α j.val)) ≠ ⊤}
      = {ch : Challenges P Fq Dom |
          eqSpan (K := Fp P) ch.α
            (Finset.univ.filter (fun i : Fin P.k₀ => m ≤ i ∧ i < ℓ)) ≠ ⊤} := by
    ext ch
    simp only [Set.mem_setOf_eq, hspan_eq_eqSpan P Fq Dom ch m ℓ]
  rw [hset]
  exact spread_failure_le_subset P Fq Dom hprime _

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

/-- **`R_out`-SPREAD failure measure, sharp closed form** (`εSPREAD` = `εZK` spread term):
combining `Rout_spread_failure_le` (head split, `1/q`) with the **sharp** tail bound
`tail_spread_failure_le_sharp` (`B (p/q)^e`), the `R_out`-SPREAD failure has measure at most
`1/q + C(k₀−1, e)·(p/q)^e` with `e = k₀−d+1` — **exactly** the `εZK` spread term
`1/q + B(p/q)^e`. This is the sharp `lem:spread` bound, the production-parameter discharge of
`εSPREAD` (replacing the lossy `Rout_spread_failure_le_closed`). -/
theorem Rout_spread_failure_le_sharp (hprime : (Module.finrank (Fp P) Fq).Prime)
    (hdk : Module.finrank (Fp P) Fq ≤ P.k₀) :
    (challengePMF P Fq Dom).toOuterMeasure
        {ch : Challenges P Fq Dom | ¬ (Submodule.span (Fp P) (Set.range
          (fun s : {s : Cube P.k₀ // s ⟨0, P.k₀_pos⟩ = true} => eqPoly ch.α s.val)) = ⊤)} ≤
      1 / (Fintype.card Fq : ℝ≥0∞) +
        (((P.k₀ - 1).choose (P.k₀ - Module.finrank (Fp P) Fq + 1) : ℕ) : ℝ≥0∞) *
          ((P.p : ℝ≥0∞) ^ (P.k₀ - Module.finrank (Fp P) Fq + 1) /
            (Fintype.card Fq : ℝ≥0∞) ^ (P.k₀ - Module.finrank (Fp P) Fq + 1)) :=
  (Rout_spread_failure_le P Fq Dom).trans
    (add_le_add le_rfl (tail_spread_failure_le_sharp P Fq Dom hprime hdk))

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

/-- **`εrow ≤ d·p/q`** (the hsum crux): under the production-parameter slack condition
`1 + k₀(2k₀+1+3·2^{k₀−1}) ≤ d·p`, the row-dependence bound is at most `d·p/q`. This is the
only nontrivial inequality of the `εZK` hsum: the unused twist+slice slack carries a
coefficient `d` on `p/q` (`twist` contributes `p/q`, `slice` contributes `(d−1)p/q`), which
dominates `εrow`'s `2^{k₀}`-grade looseness when `p` is large (true for KoalaBear:
`1450 ≤ 5p`). -/
theorem rowsLI_bound_le_dp
    (hslack : 1 + P.k₀ * (2 * P.k₀ + 1 + 3 * 2 ^ (P.k₀ - 1)) ≤
        Module.finrank (Fp P) Fq * P.p) :
    (1 : ℝ≥0∞) / (Fintype.card Fq : ℝ≥0∞) +
        (P.k₀ : ℝ≥0∞) * (2 * P.k₀ + 1 + 3 * 2 ^ (P.k₀ - 1) : ℕ) / (Fintype.card Fq : ℝ≥0∞) ≤
      ((Module.finrank (Fp P) Fq * P.p : ℕ) : ℝ≥0∞) / (Fintype.card Fq : ℝ≥0∞) := by
  rw [ENNReal.div_add_div_same]
  gcongr
  exact_mod_cast hslack

set_option maxHeartbeats 1000000 in
/-- **The `εZK` hsum** (Phase F arithmetic): the four sharp component bounds — node
(`nodeHyp_failure_le` = `εZK` node term), row (`rowsLI_failure_le_closed`), sharp SPREAD
(`Rout_spread_failure_le_sharp` = `εZK` spread term), and cross (`= εZK` cross term) — sum
below `εZK`. The node, spread, cross bounds match `εZK`'s terms exactly; `εrow` is absorbed
by the unused twist+slice slack (`≥ d·p/q`, via `rowsLI_bound_le_dp`); the `εZK` two-point
term is pure slack. -/
theorem crossSolve_sharp_hsum
    (hslack : 1 + P.k₀ * (2 * P.k₀ + 1 + 3 * 2 ^ (P.k₀ - 1)) ≤
        Module.finrank (Fp P) Fq * P.p)
    (hd1 : 1 ≤ Module.finrank (Fp P) Fq) :
    (((2 + P.s₁ : ℕ) : ℝ≥0∞) * P.p / Fintype.card Fq +
          (((2 + P.s₁).choose 2 : ℕ) : ℝ≥0∞) *
            ((Module.finrank (Fp P) Fq * 2 ^ P.k₀ : ℕ) : ℝ≥0∞) / Fintype.card Fq)
        + (1 / (fieldCard Fq : ℝ≥0∞) +
            (P.k₀ : ℝ≥0∞) * (2 * P.k₀ + 1 + 3 * 2 ^ (P.k₀ - 1) : ℕ) / (fieldCard Fq : ℝ≥0∞))
        + (1 / (Fintype.card Fq : ℝ≥0∞) +
            (((P.k₀ - 1).choose (P.k₀ - Module.finrank (Fp P) Fq + 1) : ℕ) : ℝ≥0∞) *
              ((P.p : ℝ≥0∞) ^ (P.k₀ - Module.finrank (Fp P) Fq + 1) /
                (Fintype.card Fq : ℝ≥0∞) ^ (P.k₀ - Module.finrank (Fp P) Fq + 1)))
        + ((2 ^ (P.k₀ + 7) : ℕ) : ℝ≥0∞) / (fieldCard Fq : ℝ≥0∞)
      ≤ εZK P Fq := by
  simp only [fieldCard]
  have hdp : ∀ (a c : ℝ≥0∞) (n : ℕ), (a / c) ^ n = a ^ n / c ^ n :=
    fun a c n => by rw [div_eq_mul_inv, mul_pow, div_eq_mul_inv, ENNReal.inv_pow]
  have hrow := rowsLI_bound_le_dp P Fq hslack
  have hnat : Module.finrank (Fp P) Fq * P.p =
      P.p + (Module.finrank (Fp P) Fq - 1) * P.p := by
    rw [Nat.sub_one_mul, Nat.add_sub_cancel' (Nat.le_mul_of_pos_left P.p (by omega))]
  have hsplit : ((Module.finrank (Fp P) Fq * P.p : ℕ) : ℝ≥0∞) / (Fintype.card Fq : ℝ≥0∞)
      = (P.p : ℝ≥0∞) / (Fintype.card Fq : ℝ≥0∞)
        + ((Module.finrank (Fp P) Fq - 1 : ℕ) : ℝ≥0∞) * (P.p : ℝ≥0∞) /
            (Fintype.card Fq : ℝ≥0∞) := by
    rw [ENNReal.div_add_div_same]; congr 1; exact_mod_cast hnat
  -- replace my `p^e/q^e` spread by `(p/q)^e` to match εZK's spread term
  rw [← hdp]
  refine le_trans (b :=
      ((((2 + P.s₁ : ℕ) : ℝ≥0∞) * P.p / Fintype.card Fq +
          (((2 + P.s₁).choose 2 : ℕ) : ℝ≥0∞) *
            ((Module.finrank (Fp P) Fq * 2 ^ P.k₀ : ℕ) : ℝ≥0∞) / Fintype.card Fq)
        + ((Module.finrank (Fp P) Fq * P.p : ℕ) : ℝ≥0∞) / Fintype.card Fq
        + (1 / (Fintype.card Fq : ℝ≥0∞) +
            (((P.k₀ - 1).choose (P.k₀ - Module.finrank (Fp P) Fq + 1) : ℕ) : ℝ≥0∞) *
              ((P.p : ℝ≥0∞) / Fintype.card Fq) ^ (P.k₀ - Module.finrank (Fp P) Fq + 1))
        + ((2 ^ (P.k₀ + 7) : ℕ) : ℝ≥0∞) / (Fintype.card Fq : ℝ≥0∞))) ?_ ?_
  · -- bound `εrow ≤ d·p/q`; node/spread/cross are unchanged
    gcongr
  · -- node/spread/cross match `εZK` exactly; `d·p/q` aligns with twist+slice; rest is slack
    simp only [εZK, fieldCard, extDeg]
    rw [hsplit]
    refine le_trans (le_self_add (b :=
        ((4 * 2 ^ P.k₀ + 2 * P.k₀ : ℕ) : ℝ≥0∞) / Fintype.card Fq
        + 2 * (((P.k₀ - 1).choose (P.k₀ - Module.finrank (Fp P) Fq + 1) : ℕ) : ℝ≥0∞) *
            ((P.p : ℝ≥0∞) ^ (Module.finrank (Fp P) Fq - 2) / Fintype.card Fq) ^
              (P.k₀ - Module.finrank (Fp P) Fq + 1)
        + ((4 * P.k₀ : ℕ) : ℝ≥0∞) / Fintype.card Fq
        + ((2 ^ (P.k₀ + 2) : ℕ) : ℝ≥0∞) / Fintype.card Fq)) (le_of_eq ?_)
    push_cast
    ring

/-- **`GoodSetAbsorption` from the sharp bounds — the campaign reduced to one measure**
(Phase F capstone). Plugging the four *sharp* component bounds (node `= εZK` node term,
row, SPREAD `= εZK` spread term, cross `= εZK` cross term) and the verified hsum
(`crossSolve_sharp_hsum`) into the shared-good-set reduction (`goodSetAbsorption_of_shared`),
`GoodSetAbsorption` holds whenever the single **`cond:cross2` event** has probability at
most `2^{k₀+7}/q`. All other content — the `lem:span` SPREAD bound, the node/row/cross
reductions, the `Pinning`/`MaskViewSection` linear algebra, and the `εZK` arithmetic — is
machine-checked. The sole remaining obligation of the entire masked-WHIR zero-knowledge
proof is the Schwartz–Zippel rank bound `hcross2`. -/
theorem goodSetAbsorption_of_crossSolve_sharp [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] [FiniteDimensional (Fp P) (Cube P.m → Fq)]
    {ιβ : Type*} [Fintype ιβ] (b : Module.Basis ιβ (Fp P) Fq)
    (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S) (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (hprime : (Module.finrank (Fp P) Fq).Prime)
    (hpdvd : (P.p - 1) ∣ (Fintype.card Fq - 1))
    (hcop : Nat.Coprime (2 ^ P.k₀) ((Fintype.card Fq - 1) / (P.p - 1)))
    (hdk : Module.finrank (Fp P) Fq ≤ P.k₀)
    (hslack : 1 + P.k₀ * (2 * P.k₀ + 1 + 3 * 2 ^ (P.k₀ - 1)) ≤
        Module.finrank (Fp P) Fq * P.p)
    (hcross2 : (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ∃ ψ : Cube P.m → Fq, ψ ≠ 0 ∧
        ∀ s, dotFunc (fun c => Algebra.trace (Fp P) Fq (ψ c * eqPoly ch.α s))
          ∈ Submodule.span (Fp P) (Set.range (confineGen P Fq Dom ch b))} ≤
        ((2 ^ (P.k₀ + 7) : ℕ) : ℝ≥0∞) / (fieldCard Fq : ℝ≥0∞)) :
    GoodSetAbsorption P Fq Dom S :=
  goodSetAbsorption_of_shared P Fq Dom S h2 hmf hdom hbudget _ _ _ _
    (nodeHyp_failure_le P Fq Dom hprime hpdvd hcop)
    (Rout_spread_failure_le_sharp P Fq Dom hprime hdk)
    (rowsLI_failure_le_closed P Fq Dom h2)
    ((crossSolve_failure_le P Fq Dom b).trans hcross2)
    (crossSolve_sharp_hsum P Fq hslack hprime.pos)

/-- **Masked WHIR statistical HVZK, conditional on the single `cond:cross2` bound.** The
main theorem `masked_whir_statistical_zk`, with its abstract hypothesis `GoodSetAbsorption`
replaced by the one concrete Schwartz–Zippel rank bound `hcross2` (plus the field/parameter
conditions of the analysis). Every other ingredient is machine-checked; this is the sharpest
honest statement of the result pending the `cond:cross2` determinant bound. -/
theorem masked_whir_statistical_zk_of_crossSolve
    [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] [FiniteDimensional (Fp P) (Cube P.m → Fq)]
    {ιβ : Type*} [Fintype ιβ] (b : Module.Basis ιβ (Fp P) Fq)
    (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S) (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (hprime : (Module.finrank (Fp P) Fq).Prime)
    (hpdvd : (P.p - 1) ∣ (Fintype.card Fq - 1))
    (hcop : Nat.Coprime (2 ^ P.k₀) ((Fintype.card Fq - 1) / (P.p - 1)))
    (hdk : Module.finrank (Fp P) Fq ≤ P.k₀)
    (hslack : 1 + P.k₀ * (2 * P.k₀ + 1 + 3 * 2 ^ (P.k₀ - 1)) ≤
        Module.finrank (Fp P) Fq * P.p)
    (hcross2 : (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ∃ ψ : Cube P.m → Fq, ψ ≠ 0 ∧
        ∀ s, dotFunc (fun c => Algebra.trace (Fp P) Fq (ψ c * eqPoly ch.α s))
          ∈ Submodule.span (Fp P) (Set.range (confineGen P Fq Dom ch b))} ≤
        ((2 ^ (P.k₀ + 7) : ℕ) : ℝ≥0∞) / (fieldCard Fq : ℝ≥0∞))
    (dataStar : DataAssign P) (hStar : Consistent P Fq S dataStar) :
    IsSimulator P Fq Dom S
      (honestTranscript P Fq Dom S dataStar) (εZK P Fq) :=
  masked_whir_statistical_zk P Fq Dom S
    (goodSetAbsorption_of_crossSolve_sharp P Fq Dom S b h2 hmf hdom hbudget
      hprime hpdvd hcop hdk hslack hcross2)
    dataStar hStar

/-- **Product-conditioning bound for a uniform distribution** (the clean joint-SZ tool):
for a uniform draw on `A × B`, if every first-coordinate slice has conditional probability
`≤ c`, then the whole event has probability `≤ c`. (Law of total probability with a uniform
conditional; `#(A×B) = #A·#B` and the `#A` factor cancels.) This conditions out the
non-`α` challenges and reduces the `cond:cross2` measure to a per-slice Schwartz–Zippel
bound. -/
theorem uniform_prod_event_le {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (E : Set (A × B)) (c : ℝ≥0∞)
    (hc : ∀ a, (PMF.uniformOfFintype B).toOuterMeasure {b | (a, b) ∈ E} ≤ c) :
    (PMF.uniformOfFintype (A × B)).toOuterMeasure E ≤ c := by
  classical
  have hAne : (Fintype.card A : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hAtop : (Fintype.card A : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [PMF.toOuterMeasure_apply, tsum_fintype, Fintype.sum_prod_type]
  have hstep : ∀ a : A, ∑ b, E.indicator (PMF.uniformOfFintype (A × B)) (a, b)
      = (Fintype.card A : ℝ≥0∞)⁻¹ *
          (PMF.uniformOfFintype B).toOuterMeasure {b | (a, b) ∈ E} := by
    intro a
    rw [PMF.toOuterMeasure_apply, tsum_fintype, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : (a, b) ∈ E
    · rw [Set.indicator_of_mem hb,
        Set.indicator_of_mem (show b ∈ {b | (a, b) ∈ E} from hb),
        PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply, Fintype.card_prod,
        Nat.cast_mul, ENNReal.mul_inv (Or.inl hAne) (Or.inl hAtop)]
    · rw [Set.indicator_of_notMem hb,
        Set.indicator_of_notMem (show b ∉ {b | (a, b) ∈ E} from hb), mul_zero]
  simp_rw [hstep, ← Finset.mul_sum]
  calc (Fintype.card A : ℝ≥0∞)⁻¹ *
        ∑ a, (PMF.uniformOfFintype B).toOuterMeasure {b | (a, b) ∈ E}
      ≤ (Fintype.card A : ℝ≥0∞)⁻¹ * ∑ _a : A, c := by gcongr with a; exact hc a
    _ = c := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          ENNReal.inv_mul_cancel hAne hAtop, one_mul]

open Matrix in
/-- **Moments and coefficients are equivalent at distinct points** (`lem:fullslice` Step 2,
the Vandermonde fact): for distinct evaluation points `y`, any prescribed moments
`(m_h)` are realized by some coefficients `μ` with `∑_t μ_t · y_t^h = m_h`. (The Vandermonde
matrix is invertible at distinct points.) This is the two-level moment-system ingredient of
the `y`-family argument. -/
theorem exists_moment_coeffs {F : Type*} [Field F] {n : ℕ} (y : Fin n → F)
    (hy : Function.Injective y) (m : Fin n → F) :
    ∃ μ : Fin n → F, ∀ h : Fin n, ∑ t, μ t * y t ^ (h : ℕ) = m h := by
  have hdet : (Matrix.vandermonde y).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hy
  refine ⟨Matrix.vecMul m (Matrix.vandermonde y)⁻¹, fun h => ?_⟩
  have hkey : Matrix.vecMul (Matrix.vecMul m (Matrix.vandermonde y)⁻¹)
      (Matrix.vandermonde y) = m := by
    rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet.isUnit, Matrix.vecMul_one]
  have hh := congrFun hkey h
  simp only [Matrix.vecMul, dotProduct, Matrix.vandermonde_apply] at hh
  exact hh

open Algebra in
/-- **Step 4 core of `lem:fullslice`** (trace nondegeneracy against a spanning set): if a set
`S` of scalars spans `Fq` over `Fp` and `tr(s · v) = 0` for every `s ∈ S`, then `v = 0`.
Combined with the proven `lem:span` (the `E'(π)` multipliers span `Fq`), this is exactly the
deduction `tr∘F_θ = 0 ⟹ γ²·G_θ = 0 ⟹ F_θ ≡ 0` of `lem:fullslice` Step 4. -/
theorem eq_zero_of_trace_mul_span {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {S : Set L}
    (hS : Submodule.span K S = ⊤) {v : L}
    (h : ∀ s ∈ S, Algebra.trace K L (s * v) = 0) : v = 0 := by
  have hφ : ∀ w : L, Algebra.trace K L (w * v) = 0 := by
    have key : ((Algebra.trace K L).comp (LinearMap.mulRight K v)) = 0 := by
      apply LinearMap.ext_on hS
      intro s hs
      simpa using h s hs
    intro w
    have := LinearMap.congr_fun key w
    simpa using this
  refine (traceForm_nondegenerate K L).1 v (fun w => ?_)
  rw [Algebra.traceForm_apply, mul_comm]
  exact hφ w

/-- **`lem:fullslice` Step 4, cell-family conclusion**: given the Step-3 factorization in trace
form — `tr(E'(π) · (γ²·G_θ(a,b,c))) = 0` for every `π` and every cell `(a,b,c)` (from
`tr∘F_θ = 0` and `F_θ[(1,π,a,b,c)] = γ²·E'(π)·G_θ(a,b,c)`) — with the `E'(π)` multipliers spanning
`Fq` over `Fp` (`lem:span`, condition (i)), trace nondegeneracy (`eq_zero_of_trace_mul_span`)
forces `γ²·G_θ(a,b,c) = 0` for **every** cell. Hence `F_θ` vanishes identically on the non-block
mask cells — contradicting `cond:cross2`. This is the final logical step of `lem:fullslice`. -/
theorem step4_gamma2G_zero {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] {ιπ ιabc : Type*}
    (E : ιπ → L) (G : ιabc → L) (mult : L)
    (hspan : Submodule.span K (Set.range E) = ⊤)
    (htr : ∀ (abc : ιabc) (π : ιπ), Algebra.trace K L (E π * (mult * G abc)) = 0) :
    ∀ abc : ιabc, mult * G abc = 0 := fun abc =>
  eq_zero_of_trace_mul_span hspan (by rintro s ⟨π, rfl⟩; exact htr abc π)

/-- **Rank-3 witness for the two-level moment system** (`lem:fullslice` Step 2): at the
specialization `ζ₁ = 0`, the `3 × 3` minor of the moment-coefficient map on `(S¹, R¹, R²)`
has determinant `Π₁²·Π₂·ζ₂(1−ζ₂)`. So the map `(m₀,m₁,m₂) ↦ (S¹,R¹,S²,R²)` has rank `3`
away from the hypersurface `Π₁ = 0 ∨ Π₂ = 0 ∨ ζ₂ ∈ {0,1}` — the explicit non-degeneracy
that the uniform-in-θ representation of Step 2 relies on. -/
theorem momentSystem_minor_det {R : Type*} [CommRing R] (p1 p2 z2 : R) :
    Matrix.det !![p1, -p1, (0 : R); 0, p1, -p1;
        -z2 * (1 - z2) * p2, (1 - 2 * z2 ^ 2) * p2, (2 * z2 - 1) * p2]
      = p1 ^ 2 * p2 * (z2 * (1 - z2)) := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_fin_const, Matrix.cons_val]
  ring

/-- **The `(S, R)` node-coefficient extraction** (`lem:fullslice` Step 2c, algebraic core): the
moment-combination bracket produced by `prefixFactor_evalT_moment` (the `E₀, E₁` coefficients
in the moments `m₀, m₁, m₂`), once the affine slot structure `E₀ = ρ − ζ·τ`,
`E₁ = ρ + (1 − ζ)·τ` of `evalT_mixedPoint_node_decomp` is substituted, collapses *exactly* to
`S·ρ + R·τ` with the paper's coefficients `S = (1−ζ)m₀ + (2ζ−1)m₁` and
`R = −ζ(1−ζ)m₀ + (1−2ζ²)m₁ + (2ζ−1)m₂` (tex `lem:fullslice` (577)–(578)). This is the bridge
from the channel-moment identity to the two-level moment system whose rank-3 nondegeneracy is
`momentSystem_minor_det`. Pure `ring` identity, generic in the node coordinates. -/
theorem momentCombo_node_coeffs {R : Type*} [CommRing R] (rho tau zeta m0 m1 m2 : R) :
    (rho - zeta * tau) * ((1 - zeta) * m0 + (3 * zeta - 2) * m1 - (2 * zeta - 1) * m2)
        + (rho + (1 - zeta) * tau) * ((1 - zeta) * m1 + (2 * zeta - 1) * m2)
      = ((1 - zeta) * m0 + (2 * zeta - 1) * m1) * rho
        + (-zeta * (1 - zeta) * m0 + (1 - 2 * zeta ^ 2) * m1 + (2 * zeta - 1) * m2) * tau := by
  ring

/-- **The rank-3 relation, concretely** (`lem:fullslice` Step 2, the "Solving" mechanism): with
the normalized (per-block prefix `Π^j` divided out) moment outputs `s^j = (1−ζ_j)m₀+(2ζ_j−1)m₁`
and `r^j = −ζ_j(1−ζ_j)m₀+(1−2ζ_j²)m₁+(2ζ_j−1)m₂`, the cross-block combination
`(2ζ₂−1)r¹ − (2ζ₁−1)r²` has `m₂` **eliminated**, and `(ζ₂−ζ₁)` times it equals an explicit
`ζ`-only combination `A'·s¹ + C'·s²` (Cramer over the `2×2` minor of determinant `ζ₂−ζ₁`). This
is the algebraic content of "the level-`k₀` rank-3 relation fixes one combination of
`(S¹,S²)`": once the `R`-values are prescribed, this single relation determines a combination of
the `S`-values, leaving the one free parameter the solve threads. Pure `ring`, generic. -/
theorem rank3_relation {R : Type*} [CommRing R] (z1 z2 m0 m1 m2 : R) :
    (z2 - z1) * ((2 * z2 - 1) * (-z1 * (1 - z1) * m0 + (1 - 2 * z1 ^ 2) * m1 + (2 * z1 - 1) * m2)
        - (2 * z1 - 1) * (-z2 * (1 - z2) * m0 + (1 - 2 * z2 ^ 2) * m1 + (2 * z2 - 1) * m2))
      = ((-(2 * z2 - 1) * (z1 * (1 - z1)) + (2 * z1 - 1) * (z2 * (1 - z2))) * (2 * z2 - 1)
            - ((2 * z2 - 1) * (1 - 2 * z1 ^ 2) - (2 * z1 - 1) * (1 - 2 * z2 ^ 2)) * (1 - z2))
          * ((1 - z1) * m0 + (2 * z1 - 1) * m1)
        + ((1 - z1) * ((2 * z2 - 1) * (1 - 2 * z1 ^ 2) - (2 * z1 - 1) * (1 - 2 * z2 ^ 2))
            - (2 * z1 - 1) * (-(2 * z2 - 1) * (z1 * (1 - z1)) + (2 * z1 - 1) * (z2 * (1 - z2))))
          * ((1 - z2) * m0 + (2 * z2 - 1) * m1) := by
  ring

/-- **The `cond:cross2` witness `2×2` minor, factored** (`lem:fullslice`/`cond:cross2`, the
value-row Schwartz–Zippel witness, `zk_leanVM.tex` line 543 display). At the specialization
`α_i := z₁^{2^{i-1}}` (`i ≥ 2`) the two relevant forms collapse to closed shapes — the cross form
`F₍₁,₀₎(1,(s,c)) = γ²·ν₁₁·(1+g(z₂))·ŵ₀(s,c)` (round-1 cross weights `[Xʳ](X(1−X))` against the
explicit Cramer coefficient `ν₁₁`) and the input-weight form `T_ŵ(1,(s,c)) = α₁(1−α₁)·e_s·A_c`
(class multiplier `α₁·e_s` times the position sum `A_c`). On the two mask cells `u = (s*,c*)`,
`u'' = (s'',c*)` (same position, distinct classes) the `2×2` minor `F(u)·T(u'') − F(u'')·T(u)`
factors as a single product, separating the universally-nonzero analytic prefactor from the
combinatorial bracket. Pure `ring`, generic in the coordinates. -/
theorem crossMinor_factor {R : Type*} [CommRing R]
    (γ ν11 g α1 Ac w0s w0s'' es es'' : R) :
    (γ ^ 2 * ν11 * (1 + g) * w0s) * (α1 * (1 - α1) * es'' * Ac)
        - (γ ^ 2 * ν11 * (1 + g) * w0s'') * (α1 * (1 - α1) * es * Ac)
      = γ ^ 2 * ν11 * (1 + g) * (α1 * (1 - α1)) * Ac * (w0s * es'' - w0s'' * es) := by
  ring

/-- **The witness minor is nonzero** (`cond:cross2` conclusion, the P4 algebraic core): every
factor of the `crossMinor_factor` product is nonzero — the analytic prefactor
`γ²·ν₁₁·(1+g)·α₁(1−α₁)·A_{c*}` (`γ ≠ 0` from the standing conditions; `ν₁₁ = (α₁−z₁)/((2z₁−1)d₁)`
and `1+g(z₂)` nonzero by their closed forms; `α₁(1−α₁) ≠ 0` by condition (ii) at level `1`;
`A_{c*} = ŵ₀(s*,c*) ≠ 0` at `ζ := s*`) and the combinatorial bracket
`ŵ₀(s*,c*)·e_{s''} − ŵ₀(s'',c*)·e_{s*}` (nonzero at `ζ := s''`, where it evaluates to
`ŵ₀(s*,c*) ≠ 0`, via `lem:binpow`). Hence the `2×2` minor is nonzero — exactly the `hminor`
hypothesis `crossForm_ne_zero_of_minor`/`cond_cross2_conclusion` consume. -/
theorem crossMinor_ne_zero {R : Type*} [Field R]
    (γ ν11 g α1 Ac w0s w0s'' es es'' : R)
    (hγ : γ ≠ 0) (hν : ν11 ≠ 0) (hg : (1 : R) + g ≠ 0)
    (hα0 : α1 ≠ 0) (hα1 : (1 : R) - α1 ≠ 0) (hAc : Ac ≠ 0)
    (hbracket : w0s * es'' - w0s'' * es ≠ 0) :
    (γ ^ 2 * ν11 * (1 + g) * w0s) * (α1 * (1 - α1) * es'' * Ac)
        - (γ ^ 2 * ν11 * (1 + g) * w0s'') * (α1 * (1 - α1) * es * Ac) ≠ 0 := by
  rw [crossMinor_factor]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
    (pow_ne_zero 2 hγ) hν) hg) (mul_ne_zero hα0 hα1)) hAc) hbracket

/-- **`ν₁₁` in reduced closed form** (`lem:coupled` (ii), tex:543): the coupled-chains coefficient
`ν₁₁ = λ₁·C₂/(C₂B₁ − B₂C₁)` of `coupled_repr_block1`, once the chain denominator factors as the
diagonal difference `C₂B₁ − B₂C₁ = C₁·C₂·δ₁` (its closed form per `coupled_repr_block1`'s doc),
collapses to `λ₁/(C₁·δ₁)`. The `C₂` factor cancels. With the tex:543 specialization
`C₁ = 2z₁−1`, `λ₁ = α₁−z₁`, `δ₁ = d₁` this is the paper's `ν₁₁ = (α₁−z₁)/((2z₁−1)·d₁)`. -/
theorem nu11_reduced {F : Type*} [Field F] (lam1 C1 C2 δ1 : F) (hC2 : C2 ≠ 0) :
    lam1 * C2 / (C1 * C2 * δ1) = lam1 / (C1 * δ1) := by
  rw [show lam1 * C2 = C2 * lam1 by ring, show C1 * C2 * δ1 = C2 * (C1 * δ1) by ring,
    mul_div_mul_left _ _ hC2]

/-- **`ν₁₁` is nonzero** (`lem:coupled` (ii), the `hν` ingredient of `crossMinor_ne_zero`): in the
reduced closed form `λ₁/(C₁·δ₁)`, with `λ₁ = α₁−z₁ ≠ 0` (condition (ii) at level `1`),
`C₁ = 2z₁−1 ≠ 0` (the staircase pivot), and `δ₁ = d₁ ≠ 0` (the chain diagonal difference,
`α₁ ∉ Fp` via `lem:linearized`), the Cramer coefficient does not vanish. -/
theorem nu11_ne_zero {F : Type*} [Field F] (lam1 C1 δ1 : F)
    (hlam : lam1 ≠ 0) (hC1 : C1 ≠ 0) (hδ : δ1 ≠ 0) :
    lam1 / (C1 * δ1) ≠ 0 :=
  div_ne_zero hlam (mul_ne_zero hC1 hδ)

/-- **The `cond:cross2` analytic prefactor is nonzero** (tex:543, the `hν`/`hg` ingredients of
`crossMinor_ne_zero` assembled): the witness-minor prefactor `ν₁₁·(1+g(z₂))`, with `ν₁₁` in its
reduced closed form `(α₁−z₁)/((2z₁−1)·d₁)` (`nu11_ne_zero`) and `1+g(z₂) = 2z₂(1−z₂)/(2z₂−1)`
(`one_add_gFun`, nonzero off `{0,1}` by `one_add_gFun_ne_zero`), is nonzero precisely under the
standing genericity `α₁ ≠ z₁`, `2z_j ≠ 1`, `z₂ ∉ {0,1}`, `d₁ ≠ 0`. This discharges the analytic
half of the witness minor; the combinatorial bracket is the remaining `lem:binpow` factor. -/
theorem crossPrefactor_ne_zero (z1 z2 lam1 δ1 : Fq) (h2 : (2 : Fq) ≠ 0)
    (hz1 : 2 * z1 - 1 ≠ 0) (hlam : lam1 ≠ 0) (hδ : δ1 ≠ 0)
    (hz2 : 2 * z2 - 1 ≠ 0) (hz20 : z2 ≠ 0) (hz21 : z2 ≠ 1) :
    lam1 / ((2 * z1 - 1) * δ1) * (1 + gFun Fq z2) ≠ 0 :=
  mul_ne_zero (nu11_ne_zero lam1 (2 * z1 - 1) δ1 hlam hz1 hδ)
    (one_add_gFun_ne_zero Fq h2 z2 hz2 hz20 hz21)

/-- **The `cond:cross2` witness bracket is nonzero** (tex:543, `lem:binpow` input — the
combinatorial half of the witness minor, supplying `hbracket` of `crossMinor_ne_zero`). The
paper's bracket `ŵ₀(s*,c*)·e_{s''} − ŵ₀(s'',c*)·e_{s*}`, with the class multipliers
`e_s = êq(ζ, s)` viewed as functions of the moment-class point `ζ`, is a nonzero multilinear MLE:
at the boolean point `ζ := s''` the Kronecker property `eqPoly_boolPoint` gives `e_{s''} = 1` and
`e_{s*} = 0` (since `s* ≠ s''`), so the bracket equals `ŵ₀(s*,c*) ≠ 0` there. Hence the bracket is
not identically zero on the boolean cube — its multilinear-extension table is nonzero, which is
the `T ≠ 0` hypothesis the `lem:binpow` non-vanishing (`cellPoly_combo_ne_zero`) consumes to make
the binary-power substitution `z ↦ bracket(powSeq z)` a nonzero univariate. -/
theorem crossBracket_ne_zero {j : ℕ} (sStar sPP : Cube j) (hne : sStar ≠ sPP)
    (w wPP : Fq) (hw : w ≠ 0) :
    (fun ζ : Cube j => w * eqPoly (fun i => if ζ i then (1 : Fq) else 0) sPP
        - wPP * eqPoly (fun i => if ζ i then (1 : Fq) else 0) sStar) ≠ 0 := by
  intro h
  have hval := congrFun h sPP
  rw [eqPoly_boolPoint, eqPoly_boolPoint, if_pos rfl, if_neg hne] at hval
  simp only [Pi.zero_apply, mul_one, mul_zero, sub_zero] at hval
  exact hw hval

/-- **The witness bracket's multilinear-extension table is nonzero** (tex:543, the `lem:binpow`
table input). The bracket `ŵ₀(s*,c*)·e_{s''} − ŵ₀(s'',c*)·e_{s*}` is the `mle` of the table
`b ↦ ŵ₀(s*,c*)·[b = s''] − ŵ₀(s'',c*)·[b = s*]` over the moment classes; this table is nonzero
because at `b = s''` it equals `ŵ₀(s*,c*) ≠ 0` (the `[b = s*]` term drops, `s* ≠ s''`). This is the
`T ≠ 0` form `cellPoly_combo_ne_zero` consumes directly (vs. the continuous-point form
`crossBracket_ne_zero`). -/
theorem bracketTable_ne_zero {j : ℕ} (sStar sPP : Cube j) (hne : sStar ≠ sPP)
    (w wPP : Fq) (hw : w ≠ 0) :
    (fun b : Cube j => w * (if b = sPP then (1 : Fq) else 0)
        - wPP * (if b = sStar then 1 else 0)) ≠ 0 := by
  intro h
  have hval := congrFun h sPP
  rw [Pi.zero_apply, if_pos rfl, if_neg (fun heq : sPP = sStar => hne heq.symm)] at hval
  simp only [mul_one, mul_zero, sub_zero] at hval
  exact hw hval

/-- **The witness bracket is a nonzero univariate under the binary-power substitution** (tex:543,
`lem:binpow`, the Schwartz–Zippel-ready form). Combining `bracketTable_ne_zero` with
`cellPoly_combo_ne_zero`, the cell-polynomial combination of the bracket table is a nonzero
polynomial; by `mle_powSeq_eq_aeval` it is exactly the binary-power substitution
`z ↦ mle bracketTable (powSeq z)`. So the bracket, restricted to the staircase `ζ_i := z^{2^{i-1}}`,
is a nonzero univariate of degree `< 2^j` (`cellPoly_combo_natDegree_lt`), vanishing at `< 2^j`
points — the SZ input making the witness minor's combinatorial factor nonzero off a small set, and
the last step from `crossBracket_ne_zero` to the scalar `hbracket` of `crossMinor_ne_zero`. -/
theorem bracket_cellPoly_ne_zero {j : ℕ} (sStar sPP : Cube j) (hne : sStar ≠ sPP)
    (w wPP : Fq) (hw : w ≠ 0) :
    (∑ b : Cube j, (w * (if b = sPP then (1 : Fq) else 0) - wPP * (if b = sStar then 1 else 0))
        • cellPoly (R := Fq) b) ≠ 0 := by
  exact cellPoly_combo_ne_zero (bracketTable_ne_zero Fq sStar sPP hne w wPP hw)

/-- **The single-class Lagrange weight along the staircase is the cell polynomial** (the z/zf-block
degree tool): `êq(powSeq w, c) = (cellPoly c).aeval w`, i.e. the binary-power substitution of the
Lagrange weight `êq(·, c)` is the univariate cell polynomial. Specializing `mle_powSeq_eq_aeval`
at the Kronecker table `δ_c` (where `mle δ_c x = êq(x, c)`). Consequence: any entry of `M` whose
challenge-dependence enters through `êq(powSeq(z_j), c)` is a univariate in `z_j` of degree
`< 2^j` (`cellPoly_natDegree_lt`) — the `2^{k₀}`-in-each-`z_j` degree source for the value-row
system (with `j = k₀`). -/
theorem eqPoly_powSeq_eq_aeval_cellPoly {j : ℕ} (c : Cube j) (w : Fq) :
    eqPoly (powSeq w j) c = Polynomial.aeval w (cellPoly (R := Fq) c) := by
  have h := mle_powSeq_eq_aeval (fun b : Cube j => if b = c then (1 : Fq) else 0) w
  have hmle : mle (fun b : Cube j => if b = c then (1 : Fq) else 0) (powSeq w j)
      = eqPoly (powSeq w j) c := by
    unfold mle; simp [mul_ite, Finset.sum_ite_eq']
  have hsum : (∑ b : Cube j, (if b = c then (1 : Fq) else 0) • cellPoly (R := Fq) b)
      = cellPoly c := by
    simp [ite_smul, Finset.sum_ite_eq']
  rw [← hmle, h, hsum]

/-- **The `cond:cross2` witness minor at the paper's explicit factors** (tex:543, the assembled
form): instantiating `crossMinor_ne_zero` with `ν₁₁` in its closed form `λ₁/((2z₁−1)·δ₁)`
(`nu11_ne_zero`) and the coupling `g = gFun z₂` (`one_add_gFun_ne_zero`), the analytic
hypotheses `hν`, `hg` are discharged by the standing genericity, leaving exactly the
SZ-conditional bracket `w0s·es'' − w0s''·es ≠ 0` (supplied off a measure-`< 2^j/q` set by
`bracket_cellPoly_ne_zero`). So under `α₁ ≠ z₁` (`hlam`), `2z_j ≠ 1`, `z₂ ∉ {0,1}`, `δ₁ ≠ 0`,
`γ ≠ 0`, `α₁(1−α₁) ≠ 0`, `A_{c*} ≠ 0`, and a nonzero bracket, the tex:543 minor is nonzero — the
exact `hminor` the cross-form non-degeneracy consumes, now with all analytic factors in closed
form. -/
theorem crossMinor_specialized_ne_zero (z1 z2 lam1 δ1 γ α1 Ac w0s w0s'' es es'' : Fq)
    (h2 : (2 : Fq) ≠ 0) (hγ : γ ≠ 0) (hz1 : 2 * z1 - 1 ≠ 0) (hlam : lam1 ≠ 0) (hδ : δ1 ≠ 0)
    (hz2 : 2 * z2 - 1 ≠ 0) (hz20 : z2 ≠ 0) (hz21 : z2 ≠ 1)
    (hα0 : α1 ≠ 0) (hα1 : (1 : Fq) - α1 ≠ 0) (hAc : Ac ≠ 0)
    (hbracket : w0s * es'' - w0s'' * es ≠ 0) :
    (γ ^ 2 * (lam1 / ((2 * z1 - 1) * δ1)) * (1 + gFun Fq z2) * w0s) * (α1 * (1 - α1) * es'' * Ac)
        - (γ ^ 2 * (lam1 / ((2 * z1 - 1) * δ1)) * (1 + gFun Fq z2) * w0s'')
          * (α1 * (1 - α1) * es * Ac) ≠ 0 :=
  crossMinor_ne_zero γ (lam1 / ((2 * z1 - 1) * δ1)) (gFun Fq z2) α1 Ac w0s w0s'' es es''
    hγ (nu11_ne_zero lam1 (2 * z1 - 1) δ1 hlam hz1 hδ)
    (one_add_gFun_ne_zero Fq h2 z2 hz2 hz20 hz21) hα0 hα1 hAc hbracket

/-- **A `2×2` MvPolynomial minor is nonzero from a single nonzero evaluation** (the P4
polynomial↦scalar bridge): the `2×2` determinant `a*d − c*b` of multivariate polynomials is
nonzero *as a polynomial* whenever there is one point `p` at which the scalar determinant
`(eval p a)·(eval p d) − (eval p c)·(eval p b)` is nonzero. A polynomial that vanishes
identically vanishes at every point, so a single nonzero evaluation certifies non-vanishing.
This is the linear-algebra step turning the scalar witness minor
(`crossMinor_specialized_ne_zero`) into the polynomial-level `hdet` (P4) consumed by
`masked_whir_statistical_zk_of_crossWitness2`. -/
theorem mvpoly_det2_ne_zero {σ : Type*} (a b c d : MvPolynomial σ Fq) (p : σ → Fq)
    (h : MvPolynomial.eval p a * MvPolynomial.eval p d
        - MvPolynomial.eval p c * MvPolynomial.eval p b ≠ 0) :
    a * d - c * b ≠ 0 := by
  intro h0
  apply h
  have he := congrArg (MvPolynomial.eval p) h0
  rwa [map_sub, map_mul, map_mul, map_zero] at he

/-- **P4 (`hdet`) from a specialized witness point** (the `cond:cross2` minor, polynomial form):
the `2×2` minor polynomial `pFu·pTu'' − pTu·pFu''` over any index type is nonzero as a polynomial
as soon as there is one evaluation point `p` at which the four polynomials take the explicit
closed-form values of the `tex:543` minor — `pFu ↦ γ²·ν₁₁·(1+g(z₂))·ŵ₀(s)`,
`pTu ↦ α₁(1−α₁)·e_s·A`, and the primed pair at the second class — under the standing genericity
(`γ ≠ 0`, `2z₁ ≠ 1`, `α₁ ≠ z₁` via `lam1 ≠ 0`, `δ₁ ≠ 0`, `2z₂ ≠ 1`, `z₂ ∉ {0,1}`,
`α₁(1−α₁) ≠ 0`, `A ≠ 0`, and the nonzero combinatorial bracket). Composing `mvpoly_det2_ne_zero`
with the scalar `crossMinor_specialized_ne_zero`, this discharges the entire analytic content of
P4: it reduces the `hdet` hypothesis of `masked_whir_statistical_zk_of_crossWitness2` to
*constructing* the four polynomials and *exhibiting one generic point* matching the closed
forms (e.g. the staircase specialization `α_i := z₁^{2^{i-1}}`). -/
theorem crossWitness2_det_ne_zero_of_point {σ : Type*}
    (pFu pTu pFu'' pTu'' : MvPolynomial σ Fq) (p : σ → Fq)
    (z1 z2 lam1 δ1 γ α1 Ac w0s w0s'' es es'' : Fq)
    (h2 : (2 : Fq) ≠ 0) (hγ : γ ≠ 0) (hz1 : 2 * z1 - 1 ≠ 0) (hlam : lam1 ≠ 0) (hδ : δ1 ≠ 0)
    (hz2 : 2 * z2 - 1 ≠ 0) (hz20 : z2 ≠ 0) (hz21 : z2 ≠ 1)
    (hα0 : α1 ≠ 0) (hα1 : (1 : Fq) - α1 ≠ 0) (hAc : Ac ≠ 0)
    (hbracket : w0s * es'' - w0s'' * es ≠ 0)
    (hFu : MvPolynomial.eval p pFu
        = γ ^ 2 * (lam1 / ((2 * z1 - 1) * δ1)) * (1 + gFun Fq z2) * w0s)
    (hTu : MvPolynomial.eval p pTu = α1 * (1 - α1) * es * Ac)
    (hFu'' : MvPolynomial.eval p pFu''
        = γ ^ 2 * (lam1 / ((2 * z1 - 1) * δ1)) * (1 + gFun Fq z2) * w0s'')
    (hTu'' : MvPolynomial.eval p pTu'' = α1 * (1 - α1) * es'' * Ac) :
    pFu * pTu'' - pTu * pFu'' ≠ 0 := by
  refine mvpoly_det2_ne_zero Fq pFu pFu'' pTu pTu'' p ?_
  rw [hFu, hTu'', hTu, hFu'']
  intro h0
  exact crossMinor_specialized_ne_zero Fq z1 z2 lam1 δ1 γ α1 Ac w0s w0s'' es es''
    h2 hγ hz1 hlam hδ hz2 hz20 hz21 hα0 hα1 hAc hbracket (by linear_combination h0)

/-- **Per-level `S¹`-determination** (`lem:fullslice` Step 2, the threading function `f_ℓ`): under
the rank-3 genericity `C' ≠ 0` (the `s²`-coefficient of `rank3_relation`), the block-2 output
`s² = (1−ζ₂)m₀+(2ζ₂−1)m₁` of any moment image is an explicit **affine function of the other three
outputs** `(s¹, r¹, r²)`. This is the map the free-parameter solve composes across the two levels:
prescribing `(r¹, r²)` and a free `s¹`, the partner `s²` is fixed, so the final matching equation
is affine in the free parameter — solvable when its leading coefficient (condition (iii)) is
nonzero. Solved from `rank3_relation` via `eq_div_iff`. -/
theorem level_s2_determined {F : Type*} [Field F] (z1 z2 m0 m1 m2 : F)
    (hC : (1 - z1) * ((2 * z2 - 1) * (1 - 2 * z1 ^ 2) - (2 * z1 - 1) * (1 - 2 * z2 ^ 2))
        - (2 * z1 - 1) * (-(2 * z2 - 1) * (z1 * (1 - z1)) + (2 * z1 - 1) * (z2 * (1 - z2))) ≠ 0) :
    (1 - z2) * m0 + (2 * z2 - 1) * m1
      = ((z2 - z1) * ((2 * z2 - 1) * (-z1 * (1 - z1) * m0 + (1 - 2 * z1 ^ 2) * m1 + (2 * z1 - 1) * m2)
              - (2 * z1 - 1) * (-z2 * (1 - z2) * m0 + (1 - 2 * z2 ^ 2) * m1 + (2 * z2 - 1) * m2))
          - ((-(2 * z2 - 1) * (z1 * (1 - z1)) + (2 * z1 - 1) * (z2 * (1 - z2))) * (2 * z2 - 1)
                - ((2 * z2 - 1) * (1 - 2 * z1 ^ 2) - (2 * z1 - 1) * (1 - 2 * z2 ^ 2)) * (1 - z2))
              * ((1 - z1) * m0 + (2 * z1 - 1) * m1))
        / ((1 - z1) * ((2 * z2 - 1) * (1 - 2 * z1 ^ 2) - (2 * z1 - 1) * (1 - 2 * z2 ^ 2))
            - (2 * z1 - 1) * (-(2 * z2 - 1) * (z1 * (1 - z1)) + (2 * z1 - 1) * (z2 * (1 - z2)))) := by
  rw [eq_div_iff hC]
  linear_combination rank3_relation z1 z2 m0 m1 m2

/-- **The Step-2 matching identity** (`lem:fullslice` Step 2, the uniform-in-θ representation;
tex (582)–(584)): with the partial telescopes `ρ_{L₂} = ρ_{L₁} + λ_{L₁}·τ_{L₁}` and
`η = ρ_{L₂} + λ_{L₂}·τ_{L₂}` (the top-two-level staircase structure of `eta_telescope`), the three
matching equations `S_{L₁}+S_{L₂}=Θ`, `R_{L₂}=Θ·λ_{L₂}`, `R_{L₁}=λ_{L₁}(Θ−S_{L₂})` make the
two-level node combination `∑ S_ℓ·ρ_ℓ + R_ℓ·τ_ℓ` equal `Θ·η`. The equations at levels below `L₁`
hold automatically (they share the factor `S_{L₁}+S_{L₂}=Θ`), so this is the whole solve: the
representation is **linear in Θ**, hence uniform over every direction `θ`. Generic module
identity; `module` after substituting the equations. -/
theorem matching_identity {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    (rhoL1 tauL1 tauL2 : V) (lamL1 lamL2 SL1 SL2 RL1 RL2 Θ : F)
    (hS : SL1 + SL2 = Θ) (hR2 : RL2 = Θ * lamL2) (hR1 : RL1 = lamL1 * (Θ - SL2)) :
    SL1 • rhoL1 + SL2 • (rhoL1 + lamL1 • tauL1) + RL1 • tauL1 + RL2 • tauL2
      = Θ • (rhoL1 + lamL1 • tauL1 + lamL2 • tauL2) := by
  subst hR1 hR2
  rw [← hS]
  module

/-- **Threading solvability core** (`lem:fullslice` Step 2, the free-parameter solve): once the
`R`-values are prescribed and the free parameter `t = S⁰_{L₂}` chosen, the block-0 matching
equations hold by construction (`S⁰_{L₁} := Θ₀ − t`), and `S¹_{L₁}, S¹_{L₂}` are **affine in `t`**
(via `level_s2_determined`): `S¹_{Lᵢ} = a_{Lᵢ}·t + b_{Lᵢ}`. The *only* remaining constraint, the
block-1 sum `S¹_{L₁} + S¹_{L₂} = Θ₁`, is then one affine equation in `t`, solvable exactly when its
leading coefficient `a_{L₁} + a_{L₂}` (condition (iii)) is nonzero — and the solution
`t = (Θ₁ − (b_{L₁}+b_{L₂}))/(a_{L₁}+a_{L₂})` is **linear in Θ**, the uniform-in-θ representation.
This is the literal "solvable when the leading coefficient ≠ 0" of `lem:fullslice` Step 2. -/
theorem threading_affine_solve {F : Type*} [Field F] (aL1 bL1 aL2 bL2 Θ : F)
    (hlead : aL1 + aL2 ≠ 0) :
    ∃ t : F, (aL1 * t + bL1) + (aL2 * t + bL2) = Θ := by
  refine ⟨(Θ - (bL1 + bL2)) / (aL1 + aL2), ?_⟩
  field_simp
  ring

/-- **Step-2 matching at the pairing level** (`lem:fullslice` Step 2, scalar form): the
`matching_identity` specialized to `V = Fq`, with `ρ₂` the actual `L₂`-node value satisfying the
consecutive step `ρ₂ = ρ₁ + λ₁·τ₁` (`evalT_mixed_rho_step`) and `η` the terminal pairing
(`η = ρ₂ + λ₂·τ₂`, from `eta_pairing_telescope`). Given the matching equations, the two-level node
combination `S_{L₁}ρ₁ + S_{L₂}ρ₂ + R_{L₁}τ₁ + R_{L₂}τ₂` equals `Θ·η`. This is the form the campaign
consumes: `ρ₁, ρ₂, τ₁, τ₂, η` instantiate to the `evalT`-based node pairings, `S, R` to the
`Π`-included `nodeForm` coefficients. -/
theorem matching_identity_scalar (rho1 rho2 tau1 tau2 eta lam1 lam2 SL1 SL2 RL1 RL2 Θ : Fq)
    (hstep : rho2 = rho1 + lam1 * tau1) (hη : eta = rho2 + lam2 * tau2)
    (hS : SL1 + SL2 = Θ) (hR2 : RL2 = Θ * lam2) (hR1 : RL1 = lam1 * (Θ - SL2)) :
    SL1 * rho1 + SL2 * rho2 + RL1 * tau1 + RL2 * tau2 = Θ * eta := by
  subst hstep hη
  have := matching_identity (F := Fq) (V := Fq) rho1 tau1 tau2 lam1 lam2 SL1 SL2 RL1 RL2 Θ
    hS hR2 hR1
  simpa only [smul_eq_mul] using this

/-- **Realization engine** (`lem:fullslice` Step 2, existence): a square matrix with nonzero
determinant realizes any target vector under `mulVec` (it is invertible, so surjective). The
existence half behind the per-level moment solve. -/
theorem exists_mulVec_of_det_ne_zero {F : Type*} [Field F] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) F) (hdet : M.det ≠ 0) (t : Fin n → F) :
    ∃ m, M.mulVec m = t :=
  ⟨M⁻¹.mulVec t, by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet.isUnit, Matrix.one_mulVec]⟩

/-- **Per-level moment realization** (`lem:fullslice` Step 2, the existence half of solvability):
under the rank-3 genericity (the `(S¹,R¹,R²)` moment-coefficient matrix has nonzero determinant —
condition (iii), shown not identically zero by `momentSystem_minor_det`), any target node values
`(s¹, r¹, r²)` are realized by moments `(m₀, m₁, m₂)` via the tex (577)–(578) formulas. Combined
with `matching_identity` (the representation) and `exists_moment_coeffs` (moments↔coefficients),
this furnishes the moments the uniform-in-θ solve requires. -/
theorem exists_level_moments {F : Type*} [Field F] (p1 p2 z1 z2 s1 r1 r2 : F)
    (hdet : Matrix.det !![p1 * (1 - z1), p1 * (2 * z1 - 1), (0 : F);
        p1 * (-z1 * (1 - z1)), p1 * (1 - 2 * z1 ^ 2), p1 * (2 * z1 - 1);
        p2 * (-z2 * (1 - z2)), p2 * (1 - 2 * z2 ^ 2), p2 * (2 * z2 - 1)] ≠ 0) :
    ∃ m0 m1 m2 : F,
      p1 * ((1 - z1) * m0 + (2 * z1 - 1) * m1) = s1 ∧
      p1 * (-z1 * (1 - z1) * m0 + (1 - 2 * z1 ^ 2) * m1 + (2 * z1 - 1) * m2) = r1 ∧
      p2 * (-z2 * (1 - z2) * m0 + (1 - 2 * z2 ^ 2) * m1 + (2 * z2 - 1) * m2) = r2 := by
  set M := !![p1 * (1 - z1), p1 * (2 * z1 - 1), (0 : F);
        p1 * (-z1 * (1 - z1)), p1 * (1 - 2 * z1 ^ 2), p1 * (2 * z1 - 1);
        p2 * (-z2 * (1 - z2)), p2 * (1 - 2 * z2 ^ 2), p2 * (2 * z2 - 1)] with hM
  obtain ⟨m, hm⟩ := exists_mulVec_of_det_ne_zero M hdet ![s1, r1, r2]
  refine ⟨m 0, m 1, m 2, ?_, ?_, ?_⟩
  · have h0 := congrFun hm 0
    simp only [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val, Matrix.of_apply] at h0
    linear_combination h0
  · have h1 := congrFun hm 1
    simp only [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val, Matrix.of_apply] at h1
    linear_combination h1
  · have h2 := congrFun hm 2
    simp only [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.cons_val, Matrix.of_apply] at h2
    linear_combination h2

/-- **Per-block μ-combined channel sum in `S·ρ + R·τ` node form** (`lem:fullslice` Step 2,
fusion): for block `j`, the moment-weighted channel sum (the LHS of `prefixFactor_evalT_moment`)
equals `Π^j · (S^j·ρ^j + R^j·τ^j)`, where `Π^j = ∏_{i<ℓ} eqf(α_i, z_j^{2^{i-1}})`, the moments are
`m₀=∑w, m₁=∑w·pts, m₂=∑w·pts²`, the coefficients `S^j, R^j` are the tex (577)–(578) forms, and the
node coordinates are `ρ^j = E₀+ζ(E₁−E₀)`, `τ^j = E₁−E₀` — which `evalT_mixed_node_rho` /
`evalT_mixed_slot_diff` identify with the canonical staircase functionals. Fuses
`prefixFactor_evalT_moment` with `momentCombo_node_coeffs`; the entry point to the matching
equations of Step 2's uniform-in-θ solve. -/
theorem blockMomentNodeForm (ch : Challenges P Fq Dom) (δ : Cell P → Fp P) (j : Fin 2)
    (ℓ : Fin P.k₀) (w pts : Fin 3 → Fq) :
    (∑ t, w t * (prefixFactor P Fq Dom ch ℓ (pts t) (powSeq (ch.z j) P.k₀) *
        evalT P Fq δ (mixedPoint P Fq Dom ch ℓ (pts t) (powSeq (ch.z j) P.k₀))
          (powSeq (ch.z j ^ 2 ^ P.k₀) P.m))) =
      (∏ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < ℓ),
          eqf Fq (ch.α i) (powSeq (ch.z j) P.k₀ i)) *
        (((1 - powSeq (ch.z j) P.k₀ ℓ) * (∑ t, w t)
              + (2 * powSeq (ch.z j) P.k₀ ℓ - 1) * (∑ t, w t * pts t))
            * (evalT P Fq δ (mixedPoint P Fq Dom ch ℓ 0 (powSeq (ch.z j) P.k₀))
                  (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)
                + powSeq (ch.z j) P.k₀ ℓ *
                  (evalT P Fq δ (mixedPoint P Fq Dom ch ℓ 1 (powSeq (ch.z j) P.k₀))
                      (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)
                    - evalT P Fq δ (mixedPoint P Fq Dom ch ℓ 0 (powSeq (ch.z j) P.k₀))
                      (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)))
          + (-powSeq (ch.z j) P.k₀ ℓ * (1 - powSeq (ch.z j) P.k₀ ℓ) * (∑ t, w t)
              + (1 - 2 * powSeq (ch.z j) P.k₀ ℓ ^ 2) * (∑ t, w t * pts t)
              + (2 * powSeq (ch.z j) P.k₀ ℓ - 1) * (∑ t, w t * pts t ^ 2))
            * (evalT P Fq δ (mixedPoint P Fq Dom ch ℓ 1 (powSeq (ch.z j) P.k₀))
                  (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)
                - evalT P Fq δ (mixedPoint P Fq Dom ch ℓ 0 (powSeq (ch.z j) P.k₀))
                  (powSeq (ch.z j ^ 2 ^ P.k₀) P.m))) := by
  rw [prefixFactor_evalT_moment]
  congr 1
  set E0 := evalT P Fq δ (mixedPoint P Fq Dom ch ℓ 0 (powSeq (ch.z j) P.k₀))
    (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)
  set E1 := evalT P Fq δ (mixedPoint P Fq Dom ch ℓ 1 (powSeq (ch.z j) P.k₀))
    (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)
  linear_combination momentCombo_node_coeffs (E0 + powSeq (ch.z j) P.k₀ ℓ * (E1 - E0))
    (E1 - E0) (powSeq (ch.z j) P.k₀ ℓ) (∑ t, w t) (∑ t, w t * pts t) (∑ t, w t * pts t ^ 2)

/-- **Per-block node form** (`lem:fullslice` Step 2): the `S^j·ρ^j + R^j·τ^j` summand of block `j`
at level `ℓ` (the RHS of `blockMomentNodeForm`, without the `Π^j` prefix folded in). Abbreviation
for the channel identity in node form. -/
noncomputable def nodeForm (ch : Challenges P Fq Dom) (κ : viewKer P Fq Dom S ch) (j : Fin 2)
    (ℓ : Fin P.k₀) (w pts : Fin 3 → Fq) : Fq :=
  (∏ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < ℓ),
      eqf Fq (ch.α i) (powSeq (ch.z j) P.k₀ i)) *
    (((1 - powSeq (ch.z j) P.k₀ ℓ) * (∑ t, w t)
          + (2 * powSeq (ch.z j) P.k₀ ℓ - 1) * (∑ t, w t * pts t))
        * (evalT P Fq (assemble P 0 (-κ.1)) (mixedPoint P Fq Dom ch ℓ 0 (powSeq (ch.z j) P.k₀))
              (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)
            + powSeq (ch.z j) P.k₀ ℓ *
              (evalT P Fq (assemble P 0 (-κ.1)) (mixedPoint P Fq Dom ch ℓ 1 (powSeq (ch.z j) P.k₀))
                  (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)
                - evalT P Fq (assemble P 0 (-κ.1)) (mixedPoint P Fq Dom ch ℓ 0 (powSeq (ch.z j) P.k₀))
                  (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)))
      + (-powSeq (ch.z j) P.k₀ ℓ * (1 - powSeq (ch.z j) P.k₀ ℓ) * (∑ t, w t)
          + (1 - 2 * powSeq (ch.z j) P.k₀ ℓ ^ 2) * (∑ t, w t * pts t)
          + (2 * powSeq (ch.z j) P.k₀ ℓ - 1) * (∑ t, w t * pts t ^ 2))
        * (evalT P Fq (assemble P 0 (-κ.1)) (mixedPoint P Fq Dom ch ℓ 1 (powSeq (ch.z j) P.k₀))
              (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)
            - evalT P Fq (assemble P 0 (-κ.1)) (mixedPoint P Fq Dom ch ℓ 0 (powSeq (ch.z j) P.k₀))
              (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)))

/-- **Single-level channel identity in node form** (`lem:fullslice` Step 2, the per-level input to
matching): combining `channel_moment_of_viewKer` (the vanishing μ-combined channel identity) with
`blockMomentNodeForm` for both blocks, the level-`ℓ` identity reads
`nodeForm⁰ + γ·nodeForm¹ + γ²·∑ w·crossTerm = 0`. The matching equations of Step 2 are read off
this by choosing the moments per level so that `∑_ℓ nodeFormʲ` matches `⟨θⱼηⱼ, V⟩`. -/
theorem channel_moment_node_form (ch : Challenges P Fq Dom) (h2 : (2 : Fq) ≠ 0)
    (hmf : MaskFree P Fq S) (κ : viewKer P Fq Dom S ch) (ℓ : Fin P.k₀) (w pts : Fin 3 → Fq) :
    nodeForm P Fq Dom S ch κ 0 ℓ w pts + ch.γ * nodeForm P Fq Dom S ch κ 1 ℓ w pts
      + ch.γ ^ 2 * (∑ t, w t * crossTerm P Fq Dom S (assemble P 0 (-κ.1)) ch ℓ (pts t)) = 0 := by
  unfold nodeForm
  rw [← blockMomentNodeForm P Fq Dom ch (assemble P 0 (-κ.1)) 0 ℓ w pts,
      ← blockMomentNodeForm P Fq Dom ch (assemble P 0 (-κ.1)) 1 ℓ w pts]
  exact channel_moment_of_viewKer P Fq Dom S ch h2 hmf κ ℓ w pts

/-- **Two-level regrouped channel identity** (`lem:fullslice` Step 2, the matching frame): adding
the `channel_moment_node_form` identities at the two levels `L₁, L₂` (each with its own moment
data `(w, pts)`) and regrouping by block gives
`(∑_ℓ nodeForm⁰_ℓ) + γ·(∑_ℓ nodeForm¹_ℓ) + γ²·(∑_ℓ ∑_t w·crossTerm) = 0`. The per-block sums
`∑_ℓ nodeForm^j_ℓ` are exactly what the matching equations set equal to `⟨θⱼηⱼ, V⟩`; with that
choice, the regrouped identity becomes Step 3's `γ²·(T-combination) = −F_θ(δ_out)`. -/
theorem channel_moment_two_level (ch : Challenges P Fq Dom) (h2 : (2 : Fq) ≠ 0)
    (hmf : MaskFree P Fq S) (κ : viewKer P Fq Dom S ch) (L1 L2 : Fin P.k₀)
    (w1 pts1 w2 pts2 : Fin 3 → Fq) :
    (nodeForm P Fq Dom S ch κ 0 L1 w1 pts1 + nodeForm P Fq Dom S ch κ 0 L2 w2 pts2)
      + ch.γ * (nodeForm P Fq Dom S ch κ 1 L1 w1 pts1 + nodeForm P Fq Dom S ch κ 1 L2 w2 pts2)
      + ch.γ ^ 2 * ((∑ t, w1 t * crossTerm P Fq Dom S (assemble P 0 (-κ.1)) ch L1 (pts1 t))
          + (∑ t, w2 t * crossTerm P Fq Dom S (assemble P 0 (-κ.1)) ch L2 (pts2 t))) = 0 := by
  linear_combination channel_moment_node_form P Fq Dom S ch h2 hmf κ L1 w1 pts1
    + channel_moment_node_form P Fq Dom S ch h2 hmf κ L2 w2 pts2

/-- **The matching application** (`lem:fullslice` Step 2, represented identity per block): when the
two-level `nodeForm` coefficients `(S_{Lᵢ}, R_{Lᵢ})` of block `j` satisfy the matching equations
(`hS, hR2, hR1`), the sum `nodeForm^j_{L₁} + nodeForm^j_{L₂}` equals `Θ·⟨η_j, V⟩` — the terminal
node pairing scaled by `Θ`. This instantiates `matching_identity_scalar` with the campaign
`evalT`-pairings, whose two structural hypotheses are exactly `evalT_mixed_rho_step` (the
consecutive `ρ`-step) and `eta_pairing_step` (the terminal `η`-step). The `hnf` hypotheses record
the `nodeForm = S·ρ + R·τ` decomposition (a `ring` fact once `S, R` are the `Π`-included
coefficients). This is the representation Step 3 feeds into the factorization. -/
theorem nodeForm_sum_matched (ch : Challenges P Fq Dom) (κ : viewKer P Fq Dom S ch) (j : Fin 2)
    (L1 L2 : Fin P.k₀) (hsucc : (L1 : ℕ) + 1 = (L2 : ℕ)) (htop : (L2 : ℕ) + 1 = P.k₀)
    (w1 pts1 w2 pts2 : Fin 3 → Fq) (SL1 SL2 RL1 RL2 Θ : Fq)
    (hnf1 : nodeForm P Fq Dom S ch κ j L1 w1 pts1
        = SL1 * (evalT P Fq (assemble P 0 (-κ.1)) (mixedPoint P Fq Dom ch L1 0 (powSeq (ch.z j) P.k₀))
              (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)
            + powSeq (ch.z j) P.k₀ L1 *
              (evalT P Fq (assemble P 0 (-κ.1)) (mixedPoint P Fq Dom ch L1 1 (powSeq (ch.z j) P.k₀))
                  (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)
                - evalT P Fq (assemble P 0 (-κ.1)) (mixedPoint P Fq Dom ch L1 0 (powSeq (ch.z j) P.k₀))
                  (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)))
          + RL1 * (evalT P Fq (assemble P 0 (-κ.1)) (mixedPoint P Fq Dom ch L1 1 (powSeq (ch.z j) P.k₀))
                (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)
              - evalT P Fq (assemble P 0 (-κ.1)) (mixedPoint P Fq Dom ch L1 0 (powSeq (ch.z j) P.k₀))
                (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)))
    (hnf2 : nodeForm P Fq Dom S ch κ j L2 w2 pts2
        = SL2 * (evalT P Fq (assemble P 0 (-κ.1)) (mixedPoint P Fq Dom ch L2 0 (powSeq (ch.z j) P.k₀))
              (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)
            + powSeq (ch.z j) P.k₀ L2 *
              (evalT P Fq (assemble P 0 (-κ.1)) (mixedPoint P Fq Dom ch L2 1 (powSeq (ch.z j) P.k₀))
                  (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)
                - evalT P Fq (assemble P 0 (-κ.1)) (mixedPoint P Fq Dom ch L2 0 (powSeq (ch.z j) P.k₀))
                  (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)))
          + RL2 * (evalT P Fq (assemble P 0 (-κ.1)) (mixedPoint P Fq Dom ch L2 1 (powSeq (ch.z j) P.k₀))
                (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)
              - evalT P Fq (assemble P 0 (-κ.1)) (mixedPoint P Fq Dom ch L2 0 (powSeq (ch.z j) P.k₀))
                (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)))
    (hS : SL1 + SL2 = Θ) (hR2 : RL2 = Θ * lamData P Fq Dom ch (ch.z j) L2)
    (hR1 : RL1 = lamData P Fq Dom ch (ch.z j) L1 * (Θ - SL2)) :
    nodeForm P Fq Dom S ch κ j L1 w1 pts1 + nodeForm P Fq Dom S ch κ j L2 w2 pts2
      = Θ * (∑ s, eqPoly (ch.α) s *
          mle (fun c => liftT P Fq (assemble P 0 (-κ.1)) (s, c)) (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)) := by
  rw [hnf1, hnf2]
  linear_combination matching_identity_scalar (Fq := Fq)
    (hstep := evalT_mixed_rho_step P Fq Dom ch (assemble P 0 (-κ.1)) j L1 L2 hsucc)
    (hη := eta_pairing_step P Fq Dom ch (assemble P 0 (-κ.1)) j L2 htop)
    (hS := hS) (hR2 := hR2) (hR1 := hR1)

/-- **Cross-level represented identity** (`lem:fullslice` Step 3, entry point): substituting the
two per-block representations (`hrep0, hrep1` from `nodeForm_sum_matched`) into the regrouped
two-level channel identity (`channel_moment_two_level`) yields
`Θ₀·⟨η₀,V⟩ + γ·Θ₁·⟨η₁,V⟩ + γ²·(T-combination) = 0`. Since `⟨θ₁η₁⊕θ₂η₂, V⟩ = −F_θ(δ_out)`, this is
exactly Step 3's `γ²·(T-combination) = −F_θ(δ_out)` — the represented identity that, with the
`crossTerm_combine_factor` factorization, gives `F_θ = γ²·E'(π)·G_θ`. -/
theorem cross_represented (ch : Challenges P Fq Dom) (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S)
    (κ : viewKer P Fq Dom S ch) (L1 L2 : Fin P.k₀) (w1 pts1 w2 pts2 : Fin 3 → Fq)
    (V0 V1 Θ0 Θ1 : Fq)
    (hrep0 : nodeForm P Fq Dom S ch κ 0 L1 w1 pts1 + nodeForm P Fq Dom S ch κ 0 L2 w2 pts2
        = Θ0 * V0)
    (hrep1 : nodeForm P Fq Dom S ch κ 1 L1 w1 pts1 + nodeForm P Fq Dom S ch κ 1 L2 w2 pts2
        = Θ1 * V1) :
    Θ0 * V0 + ch.γ * (Θ1 * V1)
      + ch.γ ^ 2 * ((∑ t, w1 t * crossTerm P Fq Dom S (assemble P 0 (-κ.1)) ch L1 (pts1 t))
          + (∑ t, w2 t * crossTerm P Fq Dom S (assemble P 0 (-κ.1)) ch L2 (pts2 t))) = 0 := by
  rw [← hrep0, ← hrep1]
  exact channel_moment_two_level P Fq Dom S ch h2 hmf κ L1 L2 w1 pts1 w2 pts2

/-- **`êq(α, s)` as a multilinear polynomial in the `α` coordinates** (the building block of the
`cond:cross2` rank-matrix entries `tr(ψ_c · êq(α, s))`). -/
noncomputable def eqMvPoly {R : Type*} [CommRing R] {j : ℕ} (b : Cube j) :
    MvPolynomial (Fin j) R :=
  ∏ i, if b i then MvPolynomial.X i else 1 - MvPolynomial.X i

theorem eqMvPoly_eval {R : Type*} [CommRing R] {j : ℕ} (x : Fin j → R) (b : Cube j) :
    MvPolynomial.eval x (eqMvPoly b) = eqPoly x b := by
  unfold eqMvPoly eqPoly
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hb : b i <;> simp [hb]

/-- `êq` has total degree `≤ j` (a product of `j` affine factors), so any determinant of an
`n × n` matrix of `êq`-built entries has total degree `≤ n · j` (`mvpoly_det_totalDegree_le`). -/
theorem eqMvPoly_totalDegree_le {R : Type*} [CommRing R] [Nontrivial R] {j : ℕ} (b : Cube j) :
    (eqMvPoly (R := R) b).totalDegree ≤ j := by
  unfold eqMvPoly
  refine le_trans (MvPolynomial.totalDegree_finsetProd _ _) ?_
  calc ∑ i, (if b i then (MvPolynomial.X i : MvPolynomial (Fin j) R)
          else 1 - MvPolynomial.X i).totalDegree
      ≤ ∑ _i : Fin j, 1 := Finset.sum_le_sum fun i _ => by
        by_cases hb : b i
        · simp [hb]
        · simp only [hb, if_false]
          refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
          simp
    _ = j := by simp

/-- **The cross fold as a polynomial in the `α` challenges** (`familyFold` with `α`
indeterminate): `δ ↦ (c ↦ ∑_s êq(α,s)·δ(s,c))` lifted to `MvPolynomial`. Evaluating at a
concrete `α` recovers `familyFold`. This is the entry source for the `cond:cross2` rank
matrix `M(α)`. -/
noncomputable def familyFoldMv (δ : Cube P.k₀ → Cube P.m → Fp P) (c : Cube P.m) :
    MvPolynomial (Fin P.k₀) Fq :=
  ∑ s, eqMvPoly s * MvPolynomial.C (algebraMap (Fp P) Fq (δ s c))

theorem familyFoldMv_eval (α : Fin P.k₀ → Fq) (δ : Cube P.k₀ → Cube P.m → Fp P)
    (c : Cube P.m) :
    MvPolynomial.eval α (familyFoldMv P Fq δ c)
      = ∑ s, eqPoly α s * algebraMap (Fp P) Fq (δ s c) := by
  unfold familyFoldMv
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, eqMvPoly_eval, MvPolynomial.eval_C]

/-- The polynomial cross fold has total degree `≤ k₀` (a sum of `êq`-times-constants), so the
`cond:cross2` rank determinant (an `n × n` minor of `M(α)`) has total degree `≤ n · k₀`. -/
theorem familyFoldMv_totalDegree_le (δ : Cube P.k₀ → Cube P.m → Fp P) (c : Cube P.m) :
    (familyFoldMv P Fq δ c).totalDegree ≤ P.k₀ := by
  unfold familyFoldMv
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le fun s _ => ?_)
  refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
  rw [MvPolynomial.totalDegree_C, add_zero]
  exact eqMvPoly_totalDegree_le s

/-- **Uniform is transported to uniform by a bijection.** -/
theorem uniformOfFintype_map_equiv {S T : Type*} [Fintype S] [Fintype T] [Nonempty S]
    [Nonempty T] (e : S ≃ T) : (PMF.uniformOfFintype S).map e = PMF.uniformOfFintype T := by
  classical
  ext t
  rw [PMF.map_apply, PMF.uniformOfFintype_apply,
    tsum_eq_single (e.symm t)
      (fun s hs => if_neg (fun h => hs (by rw [h, Equiv.symm_apply_apply]))),
    if_pos (by rw [Equiv.apply_symm_apply]), PMF.uniformOfFintype_apply, Fintype.card_congr e]

/-- **Product-conditioning bound through an equivalence** (the joint-SZ tool, packaged): for
a uniform draw on a finite type `T ≃ A × B`, if every `A`-slice has conditional probability
`≤ c`, the whole event has probability `≤ c`. Combines `uniformOfFintype_map_equiv`,
`PMF.toOuterMeasure_map_apply`, and `uniform_prod_event_le`. -/
theorem uniform_event_le_of_equiv {T A B : Type*} [Fintype T] [Fintype A] [Fintype B]
    [Nonempty T] [Nonempty A] [Nonempty B] (e : T ≃ A × B) (E : Set T) (c : ℝ≥0∞)
    (hc : ∀ a, (PMF.uniformOfFintype B).toOuterMeasure {b | e.symm (a, b) ∈ E} ≤ c) :
    (PMF.uniformOfFintype T).toOuterMeasure E ≤ c := by
  rw [← uniformOfFintype_map_equiv e.symm, PMF.toOuterMeasure_map_apply]
  exact uniform_prod_event_le (e.symm ⁻¹' E) c hc

/-- The challenge tuple as a (left-nested) product type, for the `Fintype`/uniform structure.
The left-nesting matches the associativity produced by iterating `ENNReal.tsum_prod`. -/
def challengesEquiv :
    Challenges P Fq Dom ≃
      (((((Fin 2 → Fq) × Fq) × (Fin P.k₀ → Fq)) × (Fin P.s₁ → Fq)) ×
        (Fin P.t₀ → {x // x ∈ Dom})) where
  toFun c := ((((c.z, c.γ), c.α), c.zf), c.qs)
  invFun p := ⟨p.1.1.1.1, p.1.1.1.2, p.1.1.2, p.1.2, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Fintype (Challenges P Fq Dom) :=
  Fintype.ofEquiv _ (challengesEquiv P Fq Dom).symm

instance : Nonempty (Challenges P Fq Dom) :=
  ⟨⟨0, 0, 0, 0, fun _ => Classical.arbitrary _⟩⟩

/-- **`challengePMF` is the uniform distribution on the challenge tuple** (the challenges are
independent uniform draws over a product of finite types). Proof: expand the bind chain, factor
the per-coordinate uniform constants out (`ENNReal.tsum_mul_left`), collapse the nested sums
into one over the product (`ENNReal.tsum_prod`), pick the unique nonzero term
(`tsum_eq_single`), and reconcile `#Challenges` with the product cardinality. This is the
foundation for *joint* Schwartz–Zippel over the full challenge space `(z, γ, α, zf, qs)` — the
correct measure tool for the `cond:cross2` event, which depends on all coordinates via
`confineGen` (in contrast to the `α`-only `challenge_α_event_le`). -/
theorem challengePMF_eq_uniform :
    challengePMF P Fq Dom = PMF.uniformOfFintype (Challenges P Fq Dom) := by
  classical
  ext c
  simp only [challengePMF, PMF.bind_apply, PMF.pure_apply, ENNReal.tsum_mul_left,
    PMF.uniformOfFintype_apply]
  rw [← ENNReal.tsum_prod, ← ENNReal.tsum_prod, ← ENNReal.tsum_prod, ← ENNReal.tsum_prod,
    tsum_eq_single (challengesEquiv P Fq Dom c)
      (fun b hb => if_neg (fun h => hb (by subst h; rfl)))]
  simp only [challengesEquiv, Equiv.coe_fn_mk]
  rw [Fintype.card_congr (challengesEquiv P Fq Dom), Fintype.card_prod, Fintype.card_prod,
    Fintype.card_prod, Fintype.card_prod]
  push_cast
  rw [ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
        (Or.inr (by exact_mod_cast Fintype.card_ne_zero)),
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
        (Or.inr (by exact_mod_cast Fintype.card_ne_zero)),
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
        (Or.inr (by exact_mod_cast Fintype.card_ne_zero)),
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _))
        (Or.inr (by exact_mod_cast Fintype.card_ne_zero))]
  ring

/-- **Joint challenge event bound via cardinality** (the correct tool for the `cond:cross2`
measure): since `challengePMF` is uniform on the (finite) challenge tuple, any event whose
finite subsets have at most `k` elements has probability at most `k / #Challenges`. Combined
with *joint* Schwartz–Zippel on the `cond:cross2` rank determinant — a polynomial in *all* the
challenge coordinates — this is the correct path to `hcross2`, superseding the `α`-only
`event_le_of_detPoly`. -/
theorem challenge_event_le_card (E : Set (Challenges P Fq Dom)) (k : ℕ)
    (hk : ∀ s : Finset (Challenges P Fq Dom), (∀ x ∈ s, x ∈ E) → s.card ≤ k) :
    (challengePMF P Fq Dom).toOuterMeasure E ≤ k / Fintype.card (Challenges P Fq Dom) := by
  rw [challengePMF_eq_uniform]
  exact uniform_toOuterMeasure_le E k hk

/-- **Joint challenge index** (`cond:cross2` measure, P1): the `Fq`-valued challenge coordinates
`(z, γ, α, zf)` as one index type. The `cond:cross2` rank determinant is a polynomial over these. -/
abbrev JointIdx : Type := Fin 2 ⊕ Unit ⊕ Fin P.k₀ ⊕ Fin P.s₁

/-- Pack the `Fq`-valued challenge coordinates `(z, γ, α, zf)` into one tuple. -/
def jointPoint (ch : Challenges P Fq Dom) : JointIdx P → Fq
  | Sum.inl j => ch.z j
  | Sum.inr (Sum.inl _) => ch.γ
  | Sum.inr (Sum.inr (Sum.inl i)) => ch.α i
  | Sum.inr (Sum.inr (Sum.inr k)) => ch.zf k

/-- **The `α`-block inclusion** `Fin k₀ ↪ JointIdx`: the third summand, carrying the round-0
folding challenges `α`. The bridge from the `α`-only rank-matrix entries (`familyFoldMv`,
`eqMvPoly`) to the *joint* index type the `cond:cross2` determinant `M` lives over. -/
def alphaIncl : Fin P.k₀ → JointIdx P := fun i => Sum.inr (Sum.inr (Sum.inl i))

/-- `jointPoint ch` restricted to the `α`-block is exactly `ch.α`. -/
theorem jointPoint_comp_alphaIncl (ch : Challenges P Fq Dom) :
    jointPoint P Fq Dom ch ∘ alphaIncl P = ch.α := by
  funext i; rfl

/-- **Evaluating an `α`-renamed polynomial at `jointPoint` is `α`-evaluation** (the joint-matrix
bridge): renaming an `α`-only polynomial into `JointIdx` and evaluating at `jointPoint ch` recovers
its evaluation at `ch.α`. So an `α`-only entry matrix lifted by `rename alphaIncl` evaluates, under
`jointPoint`, exactly as the original `M(α)` — the eval half of turning `familyFoldMv` into joint
matrix entries. -/
theorem eval_jointPoint_rename_alphaIncl (ch : Challenges P Fq Dom)
    (p : MvPolynomial (Fin P.k₀) Fq) :
    MvPolynomial.eval (jointPoint P Fq Dom ch) (MvPolynomial.rename (alphaIncl P) p)
      = MvPolynomial.eval ch.α p := by
  rw [MvPolynomial.eval_rename, jointPoint_comp_alphaIncl]

/-- **Renaming into `JointIdx` does not increase total degree** (the degree half of the joint-matrix
bridge): so the `α`-only degree bounds (`eqMvPoly_totalDegree_le`, `familyFoldMv_totalDegree_le`)
transport to the lifted joint entries, feeding `mvpoly_det_totalDegree_le` for the `n·d ≤ 2^{k₀+7}`
side (P3) of the joint determinant. -/
theorem totalDegree_rename_alphaIncl_le (p : MvPolynomial (Fin P.k₀) Fq) :
    (MvPolynomial.rename (alphaIncl P) p).totalDegree ≤ p.totalDegree :=
  MvPolynomial.totalDegree_rename_le _ _

/-- **The `zf`-block inclusion** `Fin s₁ ↪ JointIdx`: the fourth summand, carrying the
out-of-domain points `zf` on `f̂₁`. The `f̂₁`-answer value rows of `M` (the `confineGen` `zf`
branch) are built over this block. -/
def zfIncl : Fin P.s₁ → JointIdx P := fun k => Sum.inr (Sum.inr (Sum.inr k))

/-- `jointPoint ch` restricted to the `zf`-block is exactly `ch.zf`. -/
theorem jointPoint_comp_zfIncl (ch : Challenges P Fq Dom) :
    jointPoint P Fq Dom ch ∘ zfIncl P = ch.zf := by
  funext k; rfl

/-- Evaluating a `zf`-renamed polynomial at `jointPoint` is `zf`-evaluation (the `zf`-block eval
half of the joint-matrix bridge, analogous to `eval_jointPoint_rename_alphaIncl`). -/
theorem eval_jointPoint_rename_zfIncl (ch : Challenges P Fq Dom)
    (p : MvPolynomial (Fin P.s₁) Fq) :
    MvPolynomial.eval (jointPoint P Fq Dom ch) (MvPolynomial.rename (zfIncl P) p)
      = MvPolynomial.eval ch.zf p := by
  rw [MvPolynomial.eval_rename, jointPoint_comp_zfIncl]

/-- Renaming the `zf`-block into `JointIdx` does not increase total degree. -/
theorem totalDegree_rename_zfIncl_le (p : MvPolynomial (Fin P.s₁) Fq) :
    (MvPolynomial.rename (zfIncl P) p).totalDegree ≤ p.totalDegree :=
  MvPolynomial.totalDegree_rename_le _ _

/-- **The `γ`-block inclusion** `Unit ↪ JointIdx`: the second summand, carrying the batching
challenge `γ`. The cross channel enters `M` with the `γ`/`γ²` weights of `crossForm`. -/
def gammaIncl : Unit → JointIdx P := fun _ => Sum.inr (Sum.inl ())

/-- `jointPoint ch` at the `γ`-block is `ch.γ`. -/
theorem jointPoint_gammaIncl (ch : Challenges P Fq Dom) (u : Unit) :
    jointPoint P Fq Dom ch (gammaIncl P u) = ch.γ := rfl

/-- Evaluating a `γ`-renamed polynomial at `jointPoint` is evaluation at the constant tuple
`fun _ => ch.γ` (the `γ`-block eval half of the joint-matrix bridge). -/
theorem eval_jointPoint_rename_gammaIncl (ch : Challenges P Fq Dom)
    (p : MvPolynomial Unit Fq) :
    MvPolynomial.eval (jointPoint P Fq Dom ch) (MvPolynomial.rename (gammaIncl P) p)
      = MvPolynomial.eval (fun _ => ch.γ) p := by
  rw [MvPolynomial.eval_rename]
  rfl

/-- Renaming the `γ`-block into `JointIdx` does not increase total degree. -/
theorem totalDegree_rename_gammaIncl_le (p : MvPolynomial Unit Fq) :
    (MvPolynomial.rename (gammaIncl P) p).totalDegree ≤ p.totalDegree :=
  MvPolynomial.totalDegree_rename_le _ _

/-- `Challenges ≃ (Fq-coords) × (qs-part)`, isolating the `Fq`-valued challenges from the
`qs ∈ Dom` part (which factors out of the Schwartz–Zippel count). -/
def jointEquiv :
    Challenges P Fq Dom ≃ (JointIdx P → Fq) × (Fin P.t₀ → {x // x ∈ Dom}) where
  toFun ch := (jointPoint P Fq Dom ch, ch.qs)
  invFun p := ⟨fun j => p.1 (Sum.inl j), p.1 (Sum.inr (Sum.inl ())),
    fun i => p.1 (Sum.inr (Sum.inr (Sum.inl i))),
    fun k => p.1 (Sum.inr (Sum.inr (Sum.inr k))), p.2⟩
  left_inv ch := by cases ch; rfl
  right_inv p := by
    obtain ⟨f, qs⟩ := p; simp only [jointPoint]; ext x
    · rcases x with j | u | i | k <;> rfl
    · rfl

open scoped Classical in
/-- **Joint-challenge Schwartz–Zippel measure bound** (`cond:cross2` measure, P1 — the
correct-shape replacement for the `α`-only `event_le_of_detPoly`): any challenge event contained
in the zero-set of a *nonzero* polynomial `detPoly` over the joint `Fq`-coordinates
`(z, γ, α, zf)` has probability at most `totalDegree(detPoly)/q`. Unlike the `α`-only version,
this correctly handles the `cond:cross2` event's dependence on `z/zf/qs` (via `confineGen`): the
SZ count is over the *full* `Fq`-challenge space (`schwartz_zippel_totalDegree` transported via
`rename` through `JointIdx ≃ Fin N`), and the `qs ∈ Dom` factor cancels exactly in
`#{event}/#Challenges`. With `totalDegree ≤ 2^{k₀+7}` this yields the cond:cross2 bound. Reduces
`hcross2` to constructing the rank determinant over `jointPoint`, bounding its degree, and a
non-vanishing witness. -/
theorem event_le_of_jointDetPoly [Nonempty Fq] (E : Set (Challenges P Fq Dom))
    (detPoly : MvPolynomial (JointIdx P) Fq) (hne : detPoly ≠ 0)
    (hsub : E ⊆ {ch : Challenges P Fq Dom |
      MvPolynomial.eval (jointPoint P Fq Dom ch) detPoly = 0}) :
    (challengePMF P Fq Dom).toOuterMeasure E ≤
      (detPoly.totalDegree : ℝ≥0∞) / (Fintype.card Fq : ℝ≥0∞) := by
  classical
  have hqpos : 0 < Fintype.card Fq := Fintype.card_pos
  set N : ℕ := Fintype.card (JointIdx P) with hN
  have hNpos : 0 < N := Fintype.card_pos
  set e : JointIdx P ≃ Fin N := Fintype.equivFin (JointIdx P) with he
  set p' : MvPolynomial (Fin N) Fq := MvPolynomial.rename e detPoly with hp'
  have hp'ne : p' ≠ 0 := fun h0 =>
    hne (MvPolynomial.rename_injective (e : JointIdx P → Fin N) e.injective
      (by rw [← hp', h0, map_zero]))
  have hevalrel : ∀ f : JointIdx P → Fq,
      MvPolynomial.eval (f ∘ e.symm) p' = MvPolynomial.eval f detPoly := by
    intro f
    rw [hp', MvPolynomial.eval_rename, show (f ∘ e.symm) ∘ (e : JointIdx P → Fin N) = f from by
      funext x; simp]
  have hZeq : (Finset.univ.filter
        (fun f : JointIdx P → Fq => MvPolynomial.eval f detPoly = 0)).card
      = (Finset.univ.filter (fun g : Fin N → Fq => MvPolynomial.eval g p' = 0)).card := by
    refine Finset.card_bij (fun f _ => f ∘ e.symm) ?_ ?_ ?_
    · intro f hf
      rw [Finset.mem_filter] at hf ⊢
      exact ⟨Finset.mem_univ _, by rw [hevalrel]; exact hf.2⟩
    · intro f1 _ f2 _ h12
      funext x; have := congrFun h12 (e x); simpa using this
    · intro g hg
      refine ⟨g ∘ e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
      · rw [← hevalrel, show (g ∘ (e : JointIdx P → Fin N)) ∘ e.symm = g from by funext x; simp]
        rw [Finset.mem_filter] at hg; exact hg.2
      · funext x; simp
  have hSZcard : (Finset.univ.filter
      (fun g : Fin N → Fq => MvPolynomial.eval g p' = 0)).card
      ≤ detPoly.totalDegree * (Fintype.card Fq) ^ (N - 1) := by
    have hSZ := MvPolynomial.schwartz_zippel_totalDegree hp'ne (Finset.univ : Finset Fq)
    rw [Finset.card_univ, Fintype.piFinset_univ,
      div_le_div_iff₀ (by positivity) (by positivity)] at hSZ
    have hnat : (Finset.univ.filter
          (fun g : Fin N → Fq => MvPolynomial.eval g p' = 0)).card * Fintype.card Fq
        ≤ p'.totalDegree * Fintype.card Fq ^ N := by exact_mod_cast hSZ
    have hk : Fintype.card Fq ^ N = Fintype.card Fq ^ (N - 1) * Fintype.card Fq := by
      rw [← pow_succ, Nat.sub_add_cancel hNpos]
    rw [hk, ← mul_assoc] at hnat
    exact le_trans (Nat.le_of_mul_le_mul_right hnat hqpos)
      (by gcongr; exact MvPolynomial.totalDegree_rename_le _ _)
  refine (challenge_event_le_card P Fq Dom E
    (detPoly.totalDegree * (Fintype.card Fq) ^ (N - 1) *
      (Fintype.card (Fin P.t₀ → {x // x ∈ Dom}))) (fun s hs => ?_)).trans (le_of_eq ?_)
  · have hinj : Function.Injective (jointEquiv P Fq Dom) := (jointEquiv P Fq Dom).injective
    rw [← Finset.card_image_of_injective s hinj]
    have hsubset : (s.image (jointEquiv P Fq Dom)) ⊆
        (Finset.univ.filter (fun f : JointIdx P → Fq => MvPolynomial.eval f detPoly = 0)) ×ˢ
          (Finset.univ : Finset (Fin P.t₀ → {x // x ∈ Dom})) := by
      intro p hp
      obtain ⟨ch, hch, rfl⟩ := Finset.mem_image.mp hp
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hsub (hs ch hch)⟩, Finset.mem_univ _⟩
    refine (Finset.card_le_card hsubset).trans ?_
    rw [Finset.card_product, Finset.card_univ]
    gcongr
    exact hZeq.le.trans hSZcard
  · rw [Fintype.card_congr (jointEquiv P Fq Dom), Fintype.card_prod,
      show Fintype.card (JointIdx P → Fq) = Fintype.card Fq ^ N from Fintype.card_fun,
      show Fintype.card Fq ^ N = Fintype.card Fq ^ (N - 1) * Fintype.card Fq from by
        rw [← pow_succ, Nat.sub_add_cancel hNpos]]
    have hMne : ((Fintype.card Fq : ℝ≥0∞) ^ (N - 1) *
        (Fintype.card (Fin P.t₀ → {x // x ∈ Dom}) : ℝ≥0∞)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by exact_mod_cast hqpos.ne'))
        (by exact_mod_cast (Fintype.card_pos (α := Fin P.t₀ → {x // x ∈ Dom})).ne')
    have hMtop : ((Fintype.card Fq : ℝ≥0∞) ^ (N - 1) *
        (Fintype.card (Fin P.t₀ → {x // x ∈ Dom}) : ℝ≥0∞)) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
        (ENNReal.natCast_ne_top _)
    rw [show ((detPoly.totalDegree * Fintype.card Fq ^ (N - 1) *
          Fintype.card (Fin P.t₀ → {x // x ∈ Dom}) : ℕ) : ℝ≥0∞)
        = (detPoly.totalDegree : ℝ≥0∞) * ((Fintype.card Fq : ℝ≥0∞) ^ (N - 1) *
          (Fintype.card (Fin P.t₀ → {x // x ∈ Dom}) : ℝ≥0∞)) from by push_cast; ring,
      show ((Fintype.card Fq ^ (N - 1) * Fintype.card Fq *
          Fintype.card (Fin P.t₀ → {x // x ∈ Dom}) : ℕ) : ℝ≥0∞)
        = (Fintype.card Fq : ℝ≥0∞) * ((Fintype.card Fq : ℝ≥0∞) ^ (N - 1) *
          (Fintype.card (Fin P.t₀ → {x // x ∈ Dom}) : ℝ≥0∞)) from by push_cast; ring,
      ENNReal.mul_div_mul_right _ _ hMne hMtop]

/-- The challenge tuple as `Others × α`, isolating the `α` coordinate (others are `z, γ, zf, qs`).
Used to condition the `cond:cross2` measure on the non-`α` challenges. -/
def alphaEquiv :
    Challenges P Fq Dom ≃
      (((Fin 2 → Fq) × Fq × (Fin P.s₁ → Fq) × (Fin P.t₀ → {x // x ∈ Dom})) ×
        (Fin P.k₀ → Fq)) where
  toFun c := ((c.z, c.γ, c.zf, c.qs), c.α)
  invFun p := ⟨p.1.1, p.1.2.1, p.2, p.1.2.2.1, p.1.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **α-conditional reduction of a challenge event** (the correct cond:cross2 measure tool):
if, for *every* fixing of the non-`α` challenges `(z, γ, zf, qs)`, the conditional probability
over a uniform `α` of the event is `≤ c`, then the full challenge probability is `≤ c`. This is
the sound replacement for the α-only `event_le_of_detPoly`: the `cond:cross2` event's
dependence on `z/zf/qs` (via `confineGen`) is handled by conditioning, and what remains per
slice is a Schwartz–Zippel bound over `α` alone. -/
theorem challenge_alpha_marginal_le (E : Set (Challenges P Fq Dom)) (c : ℝ≥0∞)
    (hc : ∀ (z : Fin 2 → Fq) (γ : Fq) (zf : Fin P.s₁ → Fq)
        (qs : Fin P.t₀ → {x // x ∈ Dom}),
      (PMF.uniformOfFintype (Fin P.k₀ → Fq)).toOuterMeasure
        {α | (⟨z, γ, α, zf, qs⟩ : Challenges P Fq Dom) ∈ E} ≤ c) :
    (challengePMF P Fq Dom).toOuterMeasure E ≤ c := by
  rw [challengePMF_eq_uniform]
  refine uniform_event_le_of_equiv (alphaEquiv P Fq Dom) E c (fun a => ?_)
  obtain ⟨z, γ, zf, qs⟩ := a
  exact hc z γ zf qs

/-- **Condition (ii) coordinate-equality bound** (`lem:fullslice` (ii), measure): the event
`α_ℓ = z_j^{2^ℓ}` has probability at most `1/q`. Conditioning on all challenges except `α`
(`challenge_alpha_marginal_le`), the per-slice event fixes the single coordinate `α_ℓ` to the
constant `z_j^{2^ℓ}`, a measure-`1/q` event under the uniform `α` (`uniform_pi_coord_le` with a
singleton). Union over the four `(ℓ, j) ∈ {k₀−1, k₀} × {1, 2}` instances gives the `4/q` budget
of `lem:fullslice` condition (ii). -/
theorem challenge_alpha_eq_powSeq_le (ℓ : Fin P.k₀) (j : Fin 2) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ch.α ℓ = powSeq (ch.z j) P.k₀ ℓ} ≤
      (1 : ℝ≥0∞) / (Fintype.card Fq : ℝ≥0∞) := by
  classical
  refine challenge_alpha_marginal_le P Fq Dom _ _ (fun z γ zf qs => ?_)
  have hset : {α : Fin P.k₀ → Fq |
        (⟨z, γ, α, zf, qs⟩ : Challenges P Fq Dom) ∈
          {ch : Challenges P Fq Dom | ch.α ℓ = powSeq (ch.z j) P.k₀ ℓ}}
      = {α : Fin P.k₀ → Fq | α ℓ ∈ ({powSeq (z j) P.k₀ ℓ} : Set Fq)} := by
    ext α; simp
  rw [hset]
  refine (uniform_pi_coord_le ℓ ({powSeq (z j) P.k₀ ℓ} : Set Fq) 1 ?_).trans
    (le_of_eq (by norm_num))
  intro s hs
  refine (Finset.card_le_card (fun x hx => Finset.mem_singleton.mpr ?_)).trans
    (by simp : ({powSeq (z j) P.k₀ ℓ} : Finset Fq).card ≤ 1)
  have hx0 := hs x hx
  rwa [Set.mem_singleton_iff] at hx0

/-- **Condition (ii) measure, assembled** (`lem:fullslice` (ii)): over any finite set `T` of
`(ℓ, j)` instances, the event "`α_ℓ = z_j^{2^ℓ}` for some `(ℓ, j) ∈ T`" has probability at most
`|T|/q` (union bound over the per-instance `challenge_alpha_eq_powSeq_le`). For the two top levels
and two blocks (`|T| = 4`) this is the `4/q` budget the lemma allots to condition (ii). -/
theorem challenge_alpha_eq_powSeq_union_le (T : Finset (Fin P.k₀ × Fin 2)) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ∃ p ∈ T, ch.α p.1 = powSeq (ch.z p.2) P.k₀ p.1} ≤
      (T.card : ℝ≥0∞) / (Fintype.card Fq : ℝ≥0∞) := by
  have hsub : {ch : Challenges P Fq Dom | ∃ p ∈ T, ch.α p.1 = powSeq (ch.z p.2) P.k₀ p.1}
      = ⋃ p ∈ T, {ch : Challenges P Fq Dom | ch.α p.1 = powSeq (ch.z p.2) P.k₀ p.1} := by
    ext ch; simp
  rw [hsub]
  refine (MeasureTheory.measure_biUnion_finset_le T _).trans ?_
  refine (Finset.sum_le_sum (fun p _ => challenge_alpha_eq_powSeq_le P Fq Dom p.1 p.2)).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one_div]

/-- **Schwartz–Zippel reduction of the `cond:cross2` measure** (wiring Mathlib's
`MvPolynomial.schwartz_zippel_totalDegree` into the campaign). Any challenge event contained
in the zero-set of a *nonzero* polynomial `detPoly` of total degree `≤ 2^{k₀+7}` in the `α`
coordinates has probability at most `2^{k₀+7}/q`. This reduces the sole remaining obligation
`hcross2` to: **constructing the `cond:cross2` rank determinant `detPoly`, bounding its degree,
and exhibiting a non-vanishing witness** (the coupled-chains specialization of `zk_leanVM.tex`
line 529 — the genuine research-level piece). The probability/Schwartz–Zippel infrastructure
is now machine-checked.

**CAVEAT (α-only).** This reduction is Schwartz–Zippel over `α` *alone* (`challenge_α_event_le`),
so it requires the event to lie in the zero-set of a polynomial in `ch.α` *only*. The actual
`cond:cross2` event also depends on `ch.qs`/`ch.z`/`ch.zf` (via `confineGen`), so its `hsub`
hypothesis is likely **unsatisfiable for the true event** by a fixed `α`-polynomial. The
correct reduction needs *joint* Schwartz–Zippel over the full uniform-product challenge space
(`challengePMF` is uniform over `(z, γ, α, zf, qs)`); the sound interface to the remaining
obligation is `goodSetAbsorption_of_crossSolve_sharp` (the cond:cross2 *probability* bound). -/
theorem event_le_of_detPoly [Nonempty Fq] (E : Set (Challenges P Fq Dom))
    (detPoly : MvPolynomial (Fin P.k₀) Fq) (hne : detPoly ≠ 0)
    (hdeg : detPoly.totalDegree ≤ 2 ^ (P.k₀ + 7))
    (hsub : E ⊆ {ch : Challenges P Fq Dom | MvPolynomial.eval ch.α detPoly = 0}) :
    (challengePMF P Fq Dom).toOuterMeasure E ≤
      ((2 ^ (P.k₀ + 7) : ℕ) : ℝ≥0∞) / (fieldCard Fq : ℝ≥0∞) := by
  classical
  refine (MeasureTheory.measure_mono hsub).trans ?_
  refine challenge_α_event_le P Fq Dom (fun α => MvPolynomial.eval α detPoly = 0)
    (((2 ^ (P.k₀ + 7) : ℕ) : ℝ≥0∞) / (fieldCard Fq : ℝ≥0∞)) ?_
  have hqpos : 0 < Fintype.card Fq := Fintype.card_pos
  have hkpos : 0 < P.k₀ := P.k₀_pos
  -- Schwartz–Zippel: the zero-set is small
  have hSZcard : (Finset.univ.filter
      (fun α : Fin P.k₀ → Fq => MvPolynomial.eval α detPoly = 0)).card
      ≤ 2 ^ (P.k₀ + 7) * (Fintype.card Fq) ^ (P.k₀ - 1) := by
    have hSZ := MvPolynomial.schwartz_zippel_totalDegree hne (Finset.univ : Finset Fq)
    rw [Finset.card_univ, Fintype.piFinset_univ,
      div_le_div_iff₀ (by positivity) (by positivity)] at hSZ
    -- `hSZ` in `ℚ≥0` becomes a `ℕ` inequality `N * q ≤ totalDegree * q ^ k₀`
    have hnat : (Finset.univ.filter
          (fun α : Fin P.k₀ → Fq => MvPolynomial.eval α detPoly = 0)).card * Fintype.card Fq
        ≤ detPoly.totalDegree * Fintype.card Fq ^ P.k₀ := by exact_mod_cast hSZ
    have hk₀ : Fintype.card Fq ^ P.k₀ = Fintype.card Fq ^ (P.k₀ - 1) * Fintype.card Fq := by
      rw [← pow_succ, Nat.sub_add_cancel hkpos]
    rw [hk₀, ← mul_assoc] at hnat
    exact le_trans (Nat.le_of_mul_le_mul_right hnat hqpos) (by gcongr)
  refine (uniform_toOuterMeasure_le _ (2 ^ (P.k₀ + 7) * (Fintype.card Fq) ^ (P.k₀ - 1))
    (fun s hs => le_trans (Finset.card_le_card (fun α hα =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ α, hs α hα⟩)) hSZcard)).trans ?_
  rw [fieldCard, Fintype.card_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [show Fintype.card Fq ^ P.k₀ = Fintype.card Fq ^ (P.k₀ - 1) * Fintype.card Fq from by
    rw [← pow_succ, Nat.sub_add_cancel hkpos]]
  push_cast
  rw [mul_comm ((2 : ℝ≥0∞) ^ (P.k₀ + 7)) ((Fintype.card Fq : ℝ≥0∞) ^ (P.k₀ - 1)),
    ENNReal.mul_div_mul_left _ _
      (by exact_mod_cast (pow_pos hqpos (P.k₀ - 1)).ne')
      (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))]

/-- **Masked WHIR statistical HVZK, conditional on the `cond:cross2` determinant.** The main
theorem with its hypothesis reduced — past `GoodSetAbsorption`, past the `cond:cross2`
probability bound — all the way to a **concrete algebraic-geometry statement**: the existence
of a nonzero polynomial `detPoly` of total degree `≤ 2^{k₀+7}` in the `α` challenges whose
zero-set contains the `cond:cross2` rank event. This is the sharpest reduction of the entire
masked-WHIR ZK proof: everything else (the `lem:span` SPREAD bound, node/row/cross reductions,
`Pinning`/`MaskViewSection` linear algebra, the `εZK` arithmetic, and the Schwartz–Zippel
measure step) is machine-checked. The remaining content is exactly the construction of the
coupled-chains rank determinant and its non-vanishing witness (`zk_leanVM.tex` line 529). -/
theorem masked_whir_statistical_zk_of_detPoly
    [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] [FiniteDimensional (Fp P) (Cube P.m → Fq)]
    {ιβ : Type*} [Fintype ιβ] (b : Module.Basis ιβ (Fp P) Fq)
    (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S) (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (hprime : (Module.finrank (Fp P) Fq).Prime)
    (hpdvd : (P.p - 1) ∣ (Fintype.card Fq - 1))
    (hcop : Nat.Coprime (2 ^ P.k₀) ((Fintype.card Fq - 1) / (P.p - 1)))
    (hdk : Module.finrank (Fp P) Fq ≤ P.k₀)
    (hslack : 1 + P.k₀ * (2 * P.k₀ + 1 + 3 * 2 ^ (P.k₀ - 1)) ≤
        Module.finrank (Fp P) Fq * P.p)
    (detPoly : MvPolynomial (Fin P.k₀) Fq) (hne : detPoly ≠ 0)
    (hdeg : detPoly.totalDegree ≤ 2 ^ (P.k₀ + 7))
    (hsub : {ch : Challenges P Fq Dom | ∃ ψ : Cube P.m → Fq, ψ ≠ 0 ∧
        ∀ s, dotFunc (fun c => Algebra.trace (Fp P) Fq (ψ c * eqPoly ch.α s))
          ∈ Submodule.span (Fp P) (Set.range (confineGen P Fq Dom ch b))} ⊆
        {ch : Challenges P Fq Dom | MvPolynomial.eval ch.α detPoly = 0})
    (dataStar : DataAssign P) (hStar : Consistent P Fq S dataStar) :
    IsSimulator P Fq Dom S
      (honestTranscript P Fq Dom S dataStar) (εZK P Fq) :=
  masked_whir_statistical_zk_of_crossSolve P Fq Dom S b h2 hmf hdom hbudget
    hprime hpdvd hcop hdk hslack
    (event_le_of_detPoly P Fq Dom _ detPoly hne hdeg hsub) dataStar hStar

/-- **Masked WHIR statistical HVZK, reduced to the JOINT cond:cross2 determinant** (P5 skeleton —
the *correct-shape* analog of `masked_whir_statistical_zk_of_detPoly`): the main theorem holds
once there is a nonzero polynomial `detPoly` over the joint `Fq`-challenge coordinates
`(z, γ, α, zf)` (`jointPoint`), of total degree `≤ 2^{k₀+7}`, whose zero-set contains the
cond:cross2 rank event. Unlike the `α`-only `_of_detPoly` (whose `hsub` is likely unsatisfiable
because the event depends on `z/zf/qs`), this is the honest reduction: the measure side is fully
discharged by `event_le_of_jointDetPoly`. The remaining content is exactly **constructing the
joint rank determinant `detPoly` (P2), bounding its degree (P3), and the non-vanishing witness
(P4)** — the coupled-chains argument of `zk_leanVM.tex` line 529. -/
theorem masked_whir_statistical_zk_of_jointDetPoly
    [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] [FiniteDimensional (Fp P) (Cube P.m → Fq)]
    {ιβ : Type*} [Fintype ιβ] (b : Module.Basis ιβ (Fp P) Fq)
    (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S) (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (hprime : (Module.finrank (Fp P) Fq).Prime)
    (hpdvd : (P.p - 1) ∣ (Fintype.card Fq - 1))
    (hcop : Nat.Coprime (2 ^ P.k₀) ((Fintype.card Fq - 1) / (P.p - 1)))
    (hdk : Module.finrank (Fp P) Fq ≤ P.k₀)
    (hslack : 1 + P.k₀ * (2 * P.k₀ + 1 + 3 * 2 ^ (P.k₀ - 1)) ≤
        Module.finrank (Fp P) Fq * P.p)
    (detPoly : MvPolynomial (JointIdx P) Fq) (hne : detPoly ≠ 0)
    (hdeg : detPoly.totalDegree ≤ 2 ^ (P.k₀ + 7))
    (hsub : {ch : Challenges P Fq Dom | ∃ ψ : Cube P.m → Fq, ψ ≠ 0 ∧
        ∀ s, dotFunc (fun c => Algebra.trace (Fp P) Fq (ψ c * eqPoly ch.α s))
          ∈ Submodule.span (Fp P) (Set.range (confineGen P Fq Dom ch b))} ⊆
        {ch : Challenges P Fq Dom |
          MvPolynomial.eval (jointPoint P Fq Dom ch) detPoly = 0})
    (dataStar : DataAssign P) (hStar : Consistent P Fq S dataStar) :
    IsSimulator P Fq Dom S
      (honestTranscript P Fq Dom S dataStar) (εZK P Fq) :=
  masked_whir_statistical_zk_of_crossSolve P Fq Dom S b h2 hmf hdom hbudget
    hprime hpdvd hcop hdk hslack
    ((event_le_of_jointDetPoly P Fq Dom _ detPoly hne hsub).trans
      (by simp only [fieldCard]; gcongr)) dataStar hStar

/-- **Total-degree bound for the determinant of an `MvPolynomial` matrix** (reusable): if
every entry of an `n × n` matrix over `MvPolynomial σ R` has total degree `≤ d`, the
determinant has total degree `≤ n · d`. (Each of the `n!` signed terms is a product of `n`
entries.) This is the degree input for the `cond:cross2` rank determinant. -/
theorem mvpoly_det_totalDegree_le {σ R : Type*} [CommRing R] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial σ R)) (d : ℕ)
    (hM : ∀ i j, (M i j).totalDegree ≤ d) :
    M.det.totalDegree ≤ n * d := by
  rw [Matrix.det_apply]
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) (Finset.sup_le fun p _ => ?_)
  refine le_trans (MvPolynomial.totalDegree_smul_le _ _) ?_
  refine le_trans (MvPolynomial.totalDegree_finsetProd _ _) ?_
  calc ∑ i, (M (p i) i).totalDegree ≤ ∑ _i : Fin n, d := Finset.sum_le_sum fun i _ => hM _ _
    _ = n * d := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- **Schwartz–Zippel reduction of the `cond:cross2` measure, matrix form.** The campaign's
`cond:cross2` rank event lies in the zero-set of `M.det` whenever `M : Matrix (Fin n) (Fin n)
(MvPolynomial (Fin k₀) Fq)` is a parametrization (in the `α` challenges) of the rank matrix:
if `M.det ≠ 0`, every entry has degree `≤ d` with `n · d ≤ 2^{k₀+7}`, and the event is
contained in `{(M.map (eval ch.α)).det = 0}`, then the event has measure `≤ 2^{k₀+7}/q`.
This further reduces the sole remaining obligation to **constructing the rank matrix `M`** (the
coupled-chains matrix of `zk_leanVM.tex`) with a non-vanishing-determinant witness. -/
theorem event_le_of_detMatrix [Nonempty Fq] {n : ℕ} (E : Set (Challenges P Fq Dom))
    (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin P.k₀) Fq)) (hne : M.det ≠ 0)
    (d : ℕ) (hM : ∀ i j, (M i j).totalDegree ≤ d) (hnd : n * d ≤ 2 ^ (P.k₀ + 7))
    (hsub : E ⊆ {ch : Challenges P Fq Dom | (M.map (MvPolynomial.eval ch.α)).det = 0}) :
    (challengePMF P Fq Dom).toOuterMeasure E ≤
      ((2 ^ (P.k₀ + 7) : ℕ) : ℝ≥0∞) / (fieldCard Fq : ℝ≥0∞) :=
  event_le_of_detPoly P Fq Dom E M.det hne
    (le_trans (mvpoly_det_totalDegree_le M d hM) hnd)
    (hsub.trans fun ch hch => by
      simp only [Set.mem_setOf_eq] at hch ⊢
      rw [RingHom.map_det]; exact hch)

/-- **P2 rank→determinant step** (`cond:cross2`, the singularity half of the joint-matrix
interface): if every challenge in the event `E` yields a *nonzero* kernel vector of the evaluated
matrix `M.map (eval (jointPoint ch))`, then `E` is contained in that determinant's zero-set — the
exact `hsub` hypothesis of `masked_whir_statistical_zk_of_jointDetMatrix`. This is the clean
linear-algebra reduction of P2: a square matrix over a field is singular **iff** it has a
nontrivial kernel (`Matrix.exists_mulVec_eq_zero_iff`). It isolates the remaining content of P2 to
**C2** — turning the event's bad `ψ` into a kernel vector of `M(ch)` (the value-row rank matrix). -/
theorem jointDet_hsub_of_kernel {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (MvPolynomial (JointIdx P) Fq)) (E : Set (Challenges P Fq Dom))
    (hker : ∀ ch ∈ E, ∃ v : Fin n → Fq, v ≠ 0 ∧
      (M.map (MvPolynomial.eval (jointPoint P Fq Dom ch))).mulVec v = 0) :
    E ⊆ {ch : Challenges P Fq Dom |
        (M.map (MvPolynomial.eval (jointPoint P Fq Dom ch))).det = 0} := by
  intro ch hch
  simp only [Set.mem_setOf_eq]
  exact Matrix.exists_mulVec_eq_zero_iff.mp (hker ch hch)

/-- **Masked WHIR statistical HVZK, conditional on the `cond:cross2` rank matrix.** The main
theorem, reduced to its irreducible algebraic core: the existence of an `n × n` matrix `M`
over `MvPolynomial (Fin k₀) Fq` (the coupled-chains rank matrix in the `α` challenges) with
(i) non-vanishing determinant `M.det ≠ 0` (the genuine research-level witness,
`zk_leanVM.tex` line 529), (ii) per-entry total degree `≤ d` with `n·d ≤ 2^{k₀+7}`, and
(iii) the `cond:cross2` rank event contained in the determinant's specialized zero-set.
Everything else in the masked-WHIR zero-knowledge proof is machine-checked. -/
theorem masked_whir_statistical_zk_of_detMatrix
    [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] [FiniteDimensional (Fp P) (Cube P.m → Fq)]
    {ιβ : Type*} [Fintype ιβ] (b : Module.Basis ιβ (Fp P) Fq)
    (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S) (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (hprime : (Module.finrank (Fp P) Fq).Prime)
    (hpdvd : (P.p - 1) ∣ (Fintype.card Fq - 1))
    (hcop : Nat.Coprime (2 ^ P.k₀) ((Fintype.card Fq - 1) / (P.p - 1)))
    (hdk : Module.finrank (Fp P) Fq ≤ P.k₀)
    (hslack : 1 + P.k₀ * (2 * P.k₀ + 1 + 3 * 2 ^ (P.k₀ - 1)) ≤
        Module.finrank (Fp P) Fq * P.p)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin P.k₀) Fq)) (hne : M.det ≠ 0)
    (d : ℕ) (hM : ∀ i j, (M i j).totalDegree ≤ d) (hnd : n * d ≤ 2 ^ (P.k₀ + 7))
    (hsub : {ch : Challenges P Fq Dom | ∃ ψ : Cube P.m → Fq, ψ ≠ 0 ∧
        ∀ s, dotFunc (fun c => Algebra.trace (Fp P) Fq (ψ c * eqPoly ch.α s))
          ∈ Submodule.span (Fp P) (Set.range (confineGen P Fq Dom ch b))} ⊆
        {ch : Challenges P Fq Dom | (M.map (MvPolynomial.eval ch.α)).det = 0})
    (dataStar : DataAssign P) (hStar : Consistent P Fq S dataStar) :
    IsSimulator P Fq Dom S
      (honestTranscript P Fq Dom S dataStar) (εZK P Fq) :=
  masked_whir_statistical_zk_of_crossSolve P Fq Dom S b h2 hmf hdom hbudget
    hprime hpdvd hcop hdk hslack
    (event_le_of_detMatrix P Fq Dom _ M hne d hM hnd hsub) dataStar hStar

/-- **Masked WHIR statistical HVZK, reduced to the JOINT cond:cross2 rank matrix** (P2/P3 matrix
interface — the correct-shape analog of `masked_whir_statistical_zk_of_detMatrix`). The main
theorem holds given an `n × n` matrix `M` over `MvPolynomial (JointIdx P) Fq` (the coupled-chains
rank matrix in the *joint* challenges `(z,γ,α,zf)`) with: (i) `M.det ≠ 0` — the genuine
research-level non-vanishing witness (P4, `zk_leanVM.tex` line 529); (ii) per-entry total degree
`≤ d` with `n·d ≤ 2^{k₀+7}` (P3, via `mvpoly_det_totalDegree_le`); (iii) the cond:cross2 rank
event contained in `{(M.map (eval (jointPoint ch))).det = 0}` (P2 — rank-deficiency ⟹ det = 0).
The degree bound (P3) is discharged here; the remaining content is exactly constructing `M`
encoding the event (P2) and the determinant non-vanishing (P4). -/
theorem masked_whir_statistical_zk_of_jointDetMatrix
    [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] [FiniteDimensional (Fp P) (Cube P.m → Fq)]
    {ιβ : Type*} [Fintype ιβ] (b : Module.Basis ιβ (Fp P) Fq)
    (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S) (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (hprime : (Module.finrank (Fp P) Fq).Prime)
    (hpdvd : (P.p - 1) ∣ (Fintype.card Fq - 1))
    (hcop : Nat.Coprime (2 ^ P.k₀) ((Fintype.card Fq - 1) / (P.p - 1)))
    (hdk : Module.finrank (Fp P) Fq ≤ P.k₀)
    (hslack : 1 + P.k₀ * (2 * P.k₀ + 1 + 3 * 2 ^ (P.k₀ - 1)) ≤
        Module.finrank (Fp P) Fq * P.p)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) (MvPolynomial (JointIdx P) Fq)) (hne : M.det ≠ 0)
    (d : ℕ) (hM : ∀ i j, (M i j).totalDegree ≤ d) (hnd : n * d ≤ 2 ^ (P.k₀ + 7))
    (hsub : {ch : Challenges P Fq Dom | ∃ ψ : Cube P.m → Fq, ψ ≠ 0 ∧
        ∀ s, dotFunc (fun c => Algebra.trace (Fp P) Fq (ψ c * eqPoly ch.α s))
          ∈ Submodule.span (Fp P) (Set.range (confineGen P Fq Dom ch b))} ⊆
        {ch : Challenges P Fq Dom |
          (M.map (MvPolynomial.eval (jointPoint P Fq Dom ch))).det = 0})
    (dataStar : DataAssign P) (hStar : Consistent P Fq S dataStar) :
    IsSimulator P Fq Dom S
      (honestTranscript P Fq Dom S dataStar) (εZK P Fq) :=
  masked_whir_statistical_zk_of_jointDetPoly P Fq Dom S b h2 hmf hdom hbudget
    hprime hpdvd hcop hdk hslack M.det hne
    (le_trans (mvpoly_det_totalDegree_le M d hM) hnd)
    (hsub.trans fun ch hch => by
      simp only [Set.mem_setOf_eq] at hch ⊢
      rw [RingHom.map_det]; exact hch)
    dataStar hStar

/-- **Masked WHIR statistical HVZK, reduced to the JOINT rank matrix in KERNEL form** (the
sharpest reduction of the entire proof). Same as `masked_whir_statistical_zk_of_jointDetMatrix`
but with P2 stated in its natural **kernel form** (`hker`): for every challenge in the cond:cross2
event, the evaluated matrix `M.map (eval (jointPoint ch))` has a *nonzero* kernel vector. This is
the form C2 actually produces — the event's bad `ψ`, run through the value-row structure, *is* a
kernel vector — and it is converted to the det-zero `hsub` by `jointDet_hsub_of_kernel`
(`Matrix.exists_mulVec_eq_zero_iff`). The entire masked-WHIR ZK proof is now reduced to exactly:
**(P4)** `M.det ≠ 0`, **(P3)** the degree bound `n·d ≤ 2^{k₀+7}`, and **(C2)** the kernel
property — construct the value-row rank matrix `M` and exhibit the bad `ψ` as its kernel vector. -/
theorem masked_whir_statistical_zk_of_jointDetKernel
    [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] [FiniteDimensional (Fp P) (Cube P.m → Fq)]
    {ιβ : Type*} [Fintype ιβ] (b : Module.Basis ιβ (Fp P) Fq)
    (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S) (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (hprime : (Module.finrank (Fp P) Fq).Prime)
    (hpdvd : (P.p - 1) ∣ (Fintype.card Fq - 1))
    (hcop : Nat.Coprime (2 ^ P.k₀) ((Fintype.card Fq - 1) / (P.p - 1)))
    (hdk : Module.finrank (Fp P) Fq ≤ P.k₀)
    (hslack : 1 + P.k₀ * (2 * P.k₀ + 1 + 3 * 2 ^ (P.k₀ - 1)) ≤
        Module.finrank (Fp P) Fq * P.p)
    {n : ℕ} (M : Matrix (Fin n) (Fin n) (MvPolynomial (JointIdx P) Fq)) (hne : M.det ≠ 0)
    (d : ℕ) (hM : ∀ i j, (M i j).totalDegree ≤ d) (hnd : n * d ≤ 2 ^ (P.k₀ + 7))
    (hker : ∀ ch ∈ {ch : Challenges P Fq Dom | ∃ ψ : Cube P.m → Fq, ψ ≠ 0 ∧
        ∀ s, dotFunc (fun c => Algebra.trace (Fp P) Fq (ψ c * eqPoly ch.α s))
          ∈ Submodule.span (Fp P) (Set.range (confineGen P Fq Dom ch b))},
        ∃ v : Fin n → Fq, v ≠ 0 ∧
          (M.map (MvPolynomial.eval (jointPoint P Fq Dom ch))).mulVec v = 0)
    (dataStar : DataAssign P) (hStar : Consistent P Fq S dataStar) :
    IsSimulator P Fq Dom S
      (honestTranscript P Fq Dom S dataStar) (εZK P Fq) :=
  masked_whir_statistical_zk_of_jointDetMatrix P Fq Dom S b h2 hmf hdom hbudget
    hprime hpdvd hcop hdk hslack M hne d hM hnd
    (jointDet_hsub_of_kernel P Fq Dom M _ hker) dataStar hStar

open Matrix in
/-- **Masked WHIR HVZK from a `2×2` cross witness** (the cond:cross2 minor route — collapsing the
joint rank matrix to the explicit `2×2` witness of `zk_leanVM.tex` line 543). It suffices to give
four polynomials `pFu, pTu, pFu'', pTu''` over `JointIdx` — the cross form `F₍₁,₀₎` and the
input-weight form `T_ŵ` evaluated at two mask cells `u, u''` — with: (P4) their `2×2` determinant
`pFu·pTu'' − pTu·pFu'' ≠ 0` (supplied by `crossMinor_specialized_ne_zero`); (P3) each of total
degree `≤ 2^{k₀+6}` (so `2·d ≤ 2^{k₀+7}`); and (C2) on the cond:cross2 event a nonzero direction
`θ` with `θ₀·F + θ₁·T = 0` at *both* cells — the `lem:fullslice` consequence that the bad `ψ`
forces the two cell-forms `Fq`-dependent. This collapses the `n×n` construction to `n = 2`: the
genuine remaining work is exactly these four polynomials, their degrees, and the dependence (C2). -/
theorem masked_whir_statistical_zk_of_crossWitness2
    [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] [FiniteDimensional (Fp P) (Cube P.m → Fq)]
    {ιβ : Type*} [Fintype ιβ] (b : Module.Basis ιβ (Fp P) Fq)
    (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S) (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (hprime : (Module.finrank (Fp P) Fq).Prime)
    (hpdvd : (P.p - 1) ∣ (Fintype.card Fq - 1))
    (hcop : Nat.Coprime (2 ^ P.k₀) ((Fintype.card Fq - 1) / (P.p - 1)))
    (hdk : Module.finrank (Fp P) Fq ≤ P.k₀)
    (hslack : 1 + P.k₀ * (2 * P.k₀ + 1 + 3 * 2 ^ (P.k₀ - 1)) ≤
        Module.finrank (Fp P) Fq * P.p)
    (pFu pTu pFu'' pTu'' : MvPolynomial (JointIdx P) Fq)
    (hdet : pFu * pTu'' - pTu * pFu'' ≠ 0)
    (hdF : pFu.totalDegree ≤ 2 ^ (P.k₀ + 6)) (hdT : pTu.totalDegree ≤ 2 ^ (P.k₀ + 6))
    (hdF' : pFu''.totalDegree ≤ 2 ^ (P.k₀ + 6)) (hdT' : pTu''.totalDegree ≤ 2 ^ (P.k₀ + 6))
    (hker : ∀ ch ∈ {ch : Challenges P Fq Dom | ∃ ψ : Cube P.m → Fq, ψ ≠ 0 ∧
        ∀ s, dotFunc (fun c => Algebra.trace (Fp P) Fq (ψ c * eqPoly ch.α s))
          ∈ Submodule.span (Fp P) (Set.range (confineGen P Fq Dom ch b))},
        ∃ θ : Fin 2 → Fq, θ ≠ 0 ∧
          θ 0 * MvPolynomial.eval (jointPoint P Fq Dom ch) pFu
            + θ 1 * MvPolynomial.eval (jointPoint P Fq Dom ch) pTu = 0 ∧
          θ 0 * MvPolynomial.eval (jointPoint P Fq Dom ch) pFu''
            + θ 1 * MvPolynomial.eval (jointPoint P Fq Dom ch) pTu'' = 0)
    (dataStar : DataAssign P) (hStar : Consistent P Fq S dataStar) :
    IsSimulator P Fq Dom S
      (honestTranscript P Fq Dom S dataStar) (εZK P Fq) := by
  refine masked_whir_statistical_zk_of_jointDetKernel P Fq Dom S b h2 hmf hdom hbudget
    hprime hpdvd hcop hdk hslack (!![pFu, pTu; pFu'', pTu'']) ?_ (2 ^ (P.k₀ + 6)) ?_ ?_ ?_
    dataStar hStar
  · rw [Matrix.det_fin_two]
    simpa using hdet
  · intro i j
    fin_cases i <;> fin_cases j
    · simpa using hdF
    · simpa using hdT
    · simpa using hdF'
    · simpa using hdT'
  · exact le_of_eq (by rw [show P.k₀ + 7 = P.k₀ + 6 + 1 from rfl, pow_succ]; ring)
  · intro ch hch
    obtain ⟨θ, hθ, e0, e1⟩ := hker ch hch
    refine ⟨θ, hθ, ?_⟩
    funext i
    fin_cases i
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply, Fin.isValue,
        Fin.mk_zero, Fin.mk_one]
      linear_combination e0
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply, Matrix.of_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Pi.zero_apply, Fin.isValue,
        Fin.mk_zero, Fin.mk_one]
      linear_combination e1

end ZkWhir
