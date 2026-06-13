/-
The per-slot determinant-vanishing probability (ε₂, step e2) and the assembled
coupled-genericity failure bound. `slotDet_factor` splits `slotDet_m` into an
`α`-prefix at `z₀`, an `α`-prefix at `z₁`, and the `z`-coupling `zdet_m`; the
prefix events reuse `alpha_prefix_zero_le`, and `zdet_m` is bounded by
Schwartz–Zippel over `z₁` (with an exceptional set on `z₀^{2^m} ∈ {0,1}`).

Part of the `GoodSetAbsorption` formalization campaign.
-/
import Mathlib
import Zkwhir.Staircase
import Zkwhir.NodeProb

set_option linter.style.header false
set_option linter.unusedSectionVars false

noncomputable section

open scoped ENNReal

namespace ZkWhir

variable (P : Params) (Fq : Type*) [Field Fq] [Fintype Fq] [Nonempty Fq]
  [Algebra (Fp P) Fq] (Dom : Finset (Fp P)) [Nonempty {x // x ∈ Dom}]

/-- **The `zdet` vanishing bound** (`cor:twopointprob`, the `z`-coupling part):
`zdet_m` depends only on `(z₀, z₁)`; for `z₀^{2^m} ∉ {0, 1}` it is a nonzero
degree-`≤ 2·2^m` polynomial in `z₁`, and the exceptional `z₀` set has
`≤ 1 + 2^m` points. Hence `P[zdet_m = 0] ≤ (1 + 3·2^m)/q`. -/
theorem zdet_zero_le (h2 : (2 : Fq) ≠ 0) (m : Fin P.k₀) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | zdet Fq P Dom ch m = 0} ≤
      (↑(1 + 3 * 2 ^ (m : ℕ)) : ℝ≥0∞) / (fieldCard Fq : ℝ≥0∞) := by
  classical
  -- the event depends only on `ch.z`, in eval form
  have hev : {ch : Challenges P Fq Dom | zdet Fq P Dom ch m = 0} =
      {ch : Challenges P Fq Dom | ch.z ∈
        {z : Fin 2 → Fq | Polynomial.eval (z 1)
          (zdetPoly Fq (powSeq (z 0) P.k₀ m) (2 ^ (m : ℕ))) = 0}} := by
    ext ch
    simp only [Set.mem_setOf_eq, zdet_eq_eval]
  rw [hev]
  refine challenge_z_event_le P Fq Dom
    {z : Fin 2 → Fq | Polynomial.eval (z 1)
      (zdetPoly Fq (powSeq (z 0) P.k₀ m) (2 ^ (m : ℕ))) = 0} _ ?_
  simp only [fieldCard]
  set q := Fintype.card Fq
  set μ := (PMF.uniformOfFintype (Fin 2 → Fq)).toOuterMeasure
  -- the three covering events
  set B0 : Set Fq := {a : Fq | powSeq a P.k₀ m = 0} with hB0
  set B1 : Set Fq := {a : Fq | powSeq a P.k₀ m = 1} with hB1
  set Apair : Set (Fq × Fq) :=
    {p : Fq × Fq | powSeq p.1 P.k₀ m ∉ ({0, 1} : Set Fq) ∧
      Polynomial.eval p.2 (zdetPoly Fq (powSeq p.1 P.k₀ m) (2 ^ (m : ℕ))) = 0}
    with hApair
  have hsub :
      {z : Fin 2 → Fq | Polynomial.eval (z 1)
        (zdetPoly Fq (powSeq (z 0) P.k₀ m) (2 ^ (m : ℕ))) = 0} ⊆
      ({z | z 0 ∈ B0} ∪ {z | z 0 ∈ B1}) ∪ {z | (z 0, z 1) ∈ Apair} := by
    intro z hz
    by_cases h0 : powSeq (z 0) P.k₀ m = 0
    · exact Or.inl (Or.inl h0)
    · by_cases h1 : powSeq (z 0) P.k₀ m = 1
      · exact Or.inl (Or.inr h1)
      · refine Or.inr ⟨?_, hz⟩
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨h0, h1⟩
  -- coordinate / pair card bounds
  have hcard0 : ∀ s : Finset Fq, (∀ a ∈ s, a ∈ B0) → s.card ≤ 1 := by
    intro s hs
    have hss : s ⊆ {0} := by
      intro a ha
      have h := hs a ha
      simp only [hB0, Set.mem_setOf_eq, powSeq] at h
      have ha0 : a = 0 := (pow_eq_zero_iff (Nat.two_pow_pos _).ne').mp h
      simp [ha0]
    exact (Finset.card_le_card hss).trans (by simp)
  have hcard1 : ∀ s : Finset Fq, (∀ a ∈ s, a ∈ B1) → s.card ≤ 2 ^ (m : ℕ) := by
    intro s hs
    have hpoly : (Polynomial.X ^ (2 ^ (m : ℕ)) - Polynomial.C 1 : Polynomial Fq) ≠ 0 :=
      Polynomial.X_pow_sub_C_ne_zero (Nat.two_pow_pos _) 1
    have hdeg : (Polynomial.X ^ (2 ^ (m : ℕ)) - Polynomial.C 1 :
        Polynomial Fq).natDegree = 2 ^ (m : ℕ) := Polynomial.natDegree_X_pow_sub_C
    refine (card_roots_le _ hpoly s (fun a ha => ?_)).trans (le_of_eq hdeg)
    have h := hs a ha
    simp only [hB1, Set.mem_setOf_eq, powSeq] at h
    simp [h]
  have hcardpair : ∀ b : Fq,
      (Finset.univ.filter (fun b' => (b, b') ∈ Apair)).card ≤ 2 * 2 ^ (m : ℕ) := by
    intro b
    by_cases hb : powSeq b P.k₀ m ∈ ({0, 1} : Set Fq)
    · have hempty : Finset.univ.filter (fun b' => (b, b') ∈ Apair) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro b' _ hmem
        exact hmem.1 hb
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le _
    · have ha0 : powSeq b P.k₀ m ≠ 0 := fun h => hb (by simp [h])
      have ha1 : powSeq b P.k₀ m ≠ 1 := fun h => hb (by simp [h])
      have hne : zdetPoly Fq (powSeq b P.k₀ m) (2 ^ (m : ℕ)) ≠ 0 :=
        zdetPoly_ne_zero Fq h2 _ _ (Nat.two_pow_pos _) ha0 ha1
      refine (card_roots_le _ hne _ (fun a ha => ?_)).trans
        (zdetPoly_natDegree Fq _ _)
      exact (Finset.mem_filter.mp ha).2.2
  -- assemble the marginal bound
  have hA0 : μ {z : Fin 2 → Fq | z 0 ∈ B0} ≤ ((1 : ℕ) : ℝ≥0∞) / q :=
    uniform_pi_coord_le 0 B0 1 hcard0
  have hA1 : μ {z : Fin 2 → Fq | z 0 ∈ B1} ≤ ((2 ^ (m : ℕ) : ℕ) : ℝ≥0∞) / q :=
    uniform_pi_coord_le 0 B1 (2 ^ (m : ℕ)) hcard1
  have hApairle : μ {z : Fin 2 → Fq | (z 0, z 1) ∈ Apair} ≤
      ((2 * 2 ^ (m : ℕ) : ℕ) : ℝ≥0∞) / q :=
    uniform_pi_pair_le (by decide) Apair (2 * 2 ^ (m : ℕ)) hcardpair
  calc μ {z : Fin 2 → Fq | Polynomial.eval (z 1)
          (zdetPoly Fq (powSeq (z 0) P.k₀ m) (2 ^ (m : ℕ))) = 0}
      ≤ μ (({z | z 0 ∈ B0} ∪ {z | z 0 ∈ B1}) ∪ {z | (z 0, z 1) ∈ Apair}) :=
        MeasureTheory.measure_mono hsub
    _ ≤ μ ({z | z 0 ∈ B0} ∪ {z | z 0 ∈ B1}) +
          μ {z | (z 0, z 1) ∈ Apair} := MeasureTheory.measure_union_le _ _
    _ ≤ (μ {z | z 0 ∈ B0} + μ {z | z 0 ∈ B1}) + μ {z | (z 0, z 1) ∈ Apair} :=
        add_le_add (MeasureTheory.measure_union_le _ _) le_rfl
    _ ≤ (((1 : ℕ) : ℝ≥0∞) / q + ((2 ^ (m : ℕ) : ℕ) : ℝ≥0∞) / q) +
          ((2 * 2 ^ (m : ℕ) : ℕ) : ℝ≥0∞) / q :=
        add_le_add (add_le_add hA0 hA1) hApairle
    _ = (↑(1 + 3 * 2 ^ (m : ℕ)) : ℝ≥0∞) / q := by
        rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same]
        congr 1
        push_cast
        ring

/-- **The per-slot determinant bound** (`cor:twopointprob`): via `slotDet_factor`,
`P[slotDet_m = 0] ≤ k₀/q + k₀/q + (1 + 3·2^m)/q`, relaxed to the uniform
`(2k₀ + 1 + 3·2^{k₀-1})/q` since `m < k₀`. -/
theorem slotDet_zero_le (h2 : (2 : Fq) ≠ 0) (m : Fin P.k₀) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | slotDet Fq P Dom ch m = 0} ≤
      (↑(2 * P.k₀ + 1 + 3 * 2 ^ (P.k₀ - 1)) : ℝ≥0∞) / (fieldCard Fq : ℝ≥0∞) := by
  classical
  have hsub : {ch : Challenges P Fq Dom | slotDet Fq P Dom ch m = 0} ⊆
      ({ch : Challenges P Fq Dom |
          (∏ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < m),
            eqf Fq (ch.α i) (powSeq (ch.z 0) P.k₀ i)) = 0} ∪
        {ch : Challenges P Fq Dom |
          (∏ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < m),
            eqf Fq (ch.α i) (powSeq (ch.z 1) P.k₀ i)) = 0}) ∪
      {ch : Challenges P Fq Dom | zdet Fq P Dom ch m = 0} := by
    intro ch hch
    rw [Set.mem_setOf_eq, slotDet_factor] at hch
    rcases mul_eq_zero.mp hch with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · exact Or.inl (Or.inl h')
      · exact Or.inl (Or.inr h')
    · exact Or.inr h
  have hpre0 := alpha_prefix_zero_le P Fq Dom h2 0 m
  have hpre1 := alpha_prefix_zero_le P Fq Dom h2 1 m
  have hz := zdet_zero_le P Fq Dom h2 m
  have hpow : 2 ^ (m : ℕ) ≤ 2 ^ (P.k₀ - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by have := m.isLt; omega)
  have hnat : P.k₀ + P.k₀ + (1 + 3 * 2 ^ (m : ℕ)) ≤
      2 * P.k₀ + 1 + 3 * 2 ^ (P.k₀ - 1) := by omega
  have hcomb : ((P.k₀ : ℝ≥0∞) / (fieldCard Fq : ℝ≥0∞) +
        (P.k₀ : ℝ≥0∞) / (fieldCard Fq : ℝ≥0∞)) +
        (↑(1 + 3 * 2 ^ (m : ℕ)) : ℝ≥0∞) / (fieldCard Fq : ℝ≥0∞) =
      (↑(P.k₀ + P.k₀ + (1 + 3 * 2 ^ (m : ℕ))) : ℝ≥0∞) / (fieldCard Fq : ℝ≥0∞) := by
    rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same]
    congr 1
    push_cast
    ring
  refine (MeasureTheory.measure_mono hsub).trans ?_
  refine (MeasureTheory.measure_union_le _ _).trans ?_
  refine (add_le_add (MeasureTheory.measure_union_le _ _) le_rfl).trans ?_
  refine (add_le_add (add_le_add hpre0 hpre1) hz).trans ?_
  rw [hcomb]
  gcongr

/-- **The coupled-genericity failure bound** (ε₂, fully discharged): combining
`challenge_gamma_zero_le` and `slotDet_zero_le` through `coupledGen_failure_le`. -/
theorem coupledGen_failure_full (h2 : (2 : Fq) ≠ 0) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ¬ CoupledGen Fq P Dom ch} ≤
      1 / (fieldCard Fq : ℝ≥0∞) +
        (P.k₀ : ℝ≥0∞) * (2 * P.k₀ + 1 + 3 * 2 ^ (P.k₀ - 1) : ℕ) /
          (fieldCard Fq : ℝ≥0∞) :=
  coupledGen_failure_le Fq P Dom (2 * P.k₀ + 1 + 3 * 2 ^ (P.k₀ - 1))
    (challenge_gamma_zero_le P Fq Dom) (fun m => slotDet_zero_le P Fq Dom h2 m)

end ZkWhir
