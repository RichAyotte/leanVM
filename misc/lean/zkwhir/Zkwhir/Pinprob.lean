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

end ZkWhir
