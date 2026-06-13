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

/-- **Multivariate Schwartz–Zippel for multilinear extensions** (the ε₃ measure
core, absent from Mathlib): a nonzero `mle T` (`T : Cube n → F`) vanishes at most
`n·|F|^{n-1}` points of `F^n`. Induction on `n`: `card_filter_pi_succ` recurses on
the first coordinate, `mle_cons`/`mle_sub` make each fiber affine, and
`card_affine_fiber_le` bounds it — splitting on whether the top half-tables
coincide (degenerate: IH on the lower table; otherwise: IH on their difference). -/
theorem mle_card_zeros_le {F : Type*} [Field F] [Fintype F] [DecidableEq F] :
    ∀ {n : ℕ} (T : Cube n → F), T ≠ 0 →
      (Finset.univ.filter (fun x : Fin n → F => mle T x = 0)).card ≤
        n * Fintype.card F ^ (n - 1) := by
  intro n
  induction n with
  | zero =>
    intro T hT
    have hT0 : T default ≠ 0 := fun hd => hT (funext fun b => by
      rw [Subsingleton.elim b default, Pi.zero_apply]; exact hd)
    haveI : Unique (Cube 0) := Pi.uniqueOfIsEmpty _
    have hne : ∀ x : Fin 0 → F, mle T x ≠ 0 := by
      intro x
      have heq1 : eqPoly x (default : Cube 0) = 1 := by simp [eqPoly]
      have hmle : mle T x = T default := by
        unfold mle
        rw [Finset.sum_eq_single (a := (default : Cube 0))
          (fun b _ hb => absurd (Subsingleton.elim b default) hb)
          (fun h => absurd (Finset.mem_univ default) h), heq1, one_mul]
      rw [hmle]; exact hT0
    have hcard : (Finset.univ.filter (fun x : Fin 0 → F => mle T x = 0)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun x _ => hne x
    rw [hcard]; simp
  | succ n ih =>
    intro T hT
    rw [card_filter_pi_succ]
    have hform : ∀ (xr : Fin n → F) (x0 : F),
        mle T (Fin.cons x0 xr) = mle (fun b => T (Fin.cons false b)) xr
          + x0 * (mle (fun b => T (Fin.cons true b)) xr
                  - mle (fun b => T (Fin.cons false b)) xr) :=
      fun xr x0 => by rw [mle_cons]; ring
    have hfibeq : ∀ xr : Fin n → F,
        (Finset.univ.filter (fun x0 : F => mle T (Fin.cons x0 xr) = 0)) =
          Finset.univ.filter (fun x0 : F =>
            mle (fun b => T (Fin.cons false b)) xr
              + x0 * (mle (fun b => T (Fin.cons true b)) xr
                      - mle (fun b => T (Fin.cons false b)) xr) = 0) :=
      fun xr => Finset.filter_congr fun x0 _ => by rw [hform xr x0]
    by_cases hD : (fun b => T (Fin.cons true b) - T (Fin.cons false b)) = (0 : Cube n → F)
    · have hBz : ∀ xr : Fin n → F,
          mle (fun b => T (Fin.cons true b)) xr
            - mle (fun b => T (Fin.cons false b)) xr = 0 :=
        fun xr => by rw [← mle_sub, hD]; exact mle_zero xr
      have hT0ne : (fun b => T (Fin.cons false b)) ≠ (0 : Cube n → F) := by
        intro h0; apply hT; funext u
        rw [Pi.zero_apply, ← Fin.cons_self_tail u]
        cases hu : u 0 with
        | false => exact congrFun h0 (Fin.tail u)
        | true =>
          rw [sub_eq_zero.mp (congrFun hD (Fin.tail u))]
          exact congrFun h0 (Fin.tail u)
      have hfib : ∀ xr : Fin n → F,
          (Finset.univ.filter (fun x0 : F => mle T (Fin.cons x0 xr) = 0)).card =
            if mle (fun b => T (Fin.cons false b)) xr = 0 then Fintype.card F else 0 := by
        intro xr
        rw [hfibeq xr]
        simp only [hBz xr, mul_zero, add_zero]
        by_cases h : mle (fun b => T (Fin.cons false b)) xr = 0
        · rw [if_pos h, Finset.filter_true_of_mem fun _ _ => h, Finset.card_univ]
        · rw [if_neg h, Finset.filter_false_of_mem fun _ _ => h, Finset.card_empty]
      calc ∑ xr : Fin n → F,
              (Finset.univ.filter (fun x0 : F => mle T (Fin.cons x0 xr) = 0)).card
          = ∑ xr : Fin n → F,
              if mle (fun b => T (Fin.cons false b)) xr = 0 then Fintype.card F else 0 :=
            Finset.sum_congr rfl fun xr _ => hfib xr
        _ = (Finset.univ.filter (fun xr : Fin n → F =>
              mle (fun b => T (Fin.cons false b)) xr = 0)).card * Fintype.card F := by
            rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]
        _ ≤ (n * Fintype.card F ^ (n - 1)) * Fintype.card F :=
            Nat.mul_le_mul_right _ (ih _ hT0ne)
        _ ≤ (n + 1) * Fintype.card F ^ (n + 1 - 1) := by
            have hmul : n * Fintype.card F ^ (n - 1) * Fintype.card F
                = n * Fintype.card F ^ n := by
              rcases n with _ | m
              · simp
              · rw [Nat.succ_sub_one, mul_assoc, ← pow_succ]
            rw [hmul, Nat.add_sub_cancel]
            exact Nat.mul_le_mul_right _ (Nat.le_succ n)
    · have hfib : ∀ xr : Fin n → F,
          (Finset.univ.filter (fun x0 : F => mle T (Fin.cons x0 xr) = 0)).card ≤
            if mle (fun b => T (Fin.cons true b)) xr
                - mle (fun b => T (Fin.cons false b)) xr = 0
              then Fintype.card F else 1 :=
        fun xr => by rw [hfibeq xr]; exact card_affine_fiber_le _ _
      calc ∑ xr : Fin n → F,
              (Finset.univ.filter (fun x0 : F => mle T (Fin.cons x0 xr) = 0)).card
          ≤ ∑ xr : Fin n → F,
              if mle (fun b => T (Fin.cons true b)) xr
                  - mle (fun b => T (Fin.cons false b)) xr = 0
                then Fintype.card F else 1 :=
            Finset.sum_le_sum fun xr _ => hfib xr
        _ = (Finset.univ.filter (fun xr : Fin n → F =>
                mle (fun b => T (Fin.cons true b)) xr
                  - mle (fun b => T (Fin.cons false b)) xr = 0)).card * Fintype.card F
              + (Finset.univ.filter (fun xr : Fin n → F =>
                  ¬ mle (fun b => T (Fin.cons true b)) xr
                    - mle (fun b => T (Fin.cons false b)) xr = 0)).card * 1 := by
            rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul]
        _ ≤ (n * Fintype.card F ^ (n - 1)) * Fintype.card F + Fintype.card F ^ n * 1 := by
            refine Nat.add_le_add (Nat.mul_le_mul_right _ ?_) (Nat.mul_le_mul_right _ ?_)
            · refine le_trans (le_of_eq ?_)
                (ih (fun b => T (Fin.cons true b) - T (Fin.cons false b)) hD)
              congr 1; ext xr; simp only [Finset.mem_filter, mle_sub]
            · refine le_trans (Finset.card_filter_le _ _) (le_of_eq ?_)
              rw [Finset.card_univ]; simp [Fintype.card_pi]
        _ = (n + 1) * Fintype.card F ^ (n + 1 - 1) := by
            have hmul : n * Fintype.card F ^ (n - 1) * Fintype.card F
                = n * Fintype.card F ^ n := by
              rcases n with _ | m
              · simp
              · rw [Nat.succ_sub_one, mul_assoc, ← pow_succ]
            rw [hmul, mul_one, Nat.add_sub_cancel]; ring

end ZkWhir
