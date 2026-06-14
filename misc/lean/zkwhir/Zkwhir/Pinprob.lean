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

end ZkWhir
