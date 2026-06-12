/-
The sumcheck telescoping identity for the round-0 messages of the masked WHIR
opening: `ĥ_{ℓ+1}(0) + ĥ_{ℓ+1}(1) = ĥ_ℓ(α_ℓ)`, with base case
`ĥ_0(0) + ĥ_0(1) = ∑_u T(u)·Ŵ₀(u)`. This is the engine behind the
`(ℓ, y)`-family of channel identities (`lem:fullslice`, Step 1): a
view-invisible perturbation has identically vanishing message polynomials.

Part of the `GoodSetAbsorption` formalization campaign; unwired until green.
-/
import Mathlib
import Zkwhir.Statement

set_option linter.style.header false
set_option linter.unusedSectionVars false

noncomputable section

open scoped ENNReal

namespace ZkWhir

variable (P : Params) (Fq : Type*) [Field Fq] [Fintype Fq]
  [Algebra (Fp P) Fq] (Dom : Finset (Fp P))

variable (S : Stmt P Fq) (T : Cell P → Fp P) (ch : Challenges P Fq Dom)

/-- Partial-evaluation collapse: plugging a boolean into the `X`-slot of level
`ℓ'` equals the level-`ℓ` partial evaluation at `α_ℓ` with the boolean stored
in the suffix. -/
theorem partialEval_boolean_collapse (G : Cell P → Fq) {ℓ ℓ' : Fin P.k₀}
    (hsucc : (ℓ : ℕ) + 1 = (ℓ' : ℕ)) (xb : Bool) (b : Cube P.k₀) (c : Cube P.m) :
    partialEval P Fq Dom ch G ℓ' (if xb then 1 else 0) b c =
      partialEval P Fq Dom ch G ℓ (ch.α ℓ) (Function.update b ℓ' xb) c := by
  unfold partialEval
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rcases Nat.lt_trichotomy (i : ℕ) (ℓ : ℕ) with hi | hi | hi
  · -- `i < ℓ < ℓ'`: the α-factor on both sides
    have h1 : i < ℓ := hi
    have h2 : i < ℓ' := by rw [Fin.lt_def]; omega
    rw [if_pos h2, if_pos h1]
  · -- `i = ℓ`: the level-`ℓ'` prefix α-factor equals the level-`ℓ` `X`-slot at `α ℓ`
    have hieq : i = ℓ := Fin.ext hi
    subst hieq
    have h2 : i < ℓ' := by rw [Fin.lt_def]; omega
    rw [if_pos h2, if_neg (lt_irrefl i), if_pos rfl]
  · -- `i > ℓ`
    have h1 : ¬ i < ℓ := by rw [Fin.lt_def]; omega
    have hne : i ≠ ℓ := Fin.ne_of_val_ne (by omega)
    by_cases h3 : (i : ℕ) = (ℓ' : ℕ)
    · -- `i = ℓ'`: the boolean `X`-slot equals the suffix indicator at the update
      have hieq : i = ℓ' := Fin.ext h3
      subst hieq
      rw [if_neg (lt_irrefl i), if_pos rfl, if_neg h1, if_neg hne,
        Function.update_self]
      cases xb <;> cases hsi : s i <;> simp
    · -- `i > ℓ'`: the suffix indicators agree (the update misses `i`)
      have h4 : ¬ i < ℓ' := by rw [Fin.lt_def]; omega
      have hne' : i ≠ ℓ' := Fin.ne_of_val_ne h3
      rw [if_neg h4, if_neg hne', if_neg h1, if_neg hne,
        Function.update_of_ne hne']

/-- Pairing reindex: a sum over suffixes vanishing up to `ℓ` splits along the
bit at `ℓ' = ℓ + 1` into a sum over suffixes vanishing up to `ℓ'`. -/
theorem sum_suffix_pair {M : Type*} [AddCommMonoid M] {ℓ ℓ' : Fin P.k₀}
    (hsucc : (ℓ : ℕ) + 1 = (ℓ' : ℕ)) (H : Cube P.k₀ → M) :
    ∑ b ∈ Finset.univ.filter
        (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ, b i = false), H b =
      ∑ b ∈ Finset.univ.filter
        (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ', b i = false),
        (H (Function.update b ℓ' false) + H (Function.update b ℓ' true)) := by
  classical
  have hℓℓ' : ℓ < ℓ' := by rw [Fin.lt_def]; omega
  -- members of the finer filter have a `false` bit at `ℓ'`, so the `false`
  -- update is the identity there
  have hupdfalse : ∀ b ∈ Finset.univ.filter
      (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ', b i = false),
      Function.update b ℓ' false = b := by
    intro b hb
    funext i
    by_cases hi : i = ℓ'
    · subst hi
      rw [Function.update_self]
      exact ((Finset.mem_filter.mp hb).2 i (Finset.mem_Iic.mpr le_rfl)).symm
    · rw [Function.update_of_ne hi]
  rw [Finset.sum_add_distrib]
  -- the coarse filter splits along the bit at `ℓ'`
  have hsplit : Finset.univ.filter
      (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ, b i = false) =
      (Finset.univ.filter
        (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ', b i = false)) ∪
      (Finset.univ.filter
        (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ', b i = false)).image
        (fun b => Function.update b ℓ' true) := by
    ext b
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Finset.mem_Iic]
    constructor
    · intro hb
      by_cases hbit : b ℓ' = false
      · left
        intro i hi
        by_cases hi' : i = ℓ'
        · rw [hi']; exact hbit
        · refine hb i ?_
          rw [Fin.le_def] at hi ⊢
          have : (i : ℕ) ≠ (ℓ' : ℕ) := fun h => hi' (Fin.ext h)
          omega
      · right
        refine ⟨Function.update b ℓ' false, fun i hi => ?_, ?_⟩
        · by_cases hi' : i = ℓ'
          · rw [hi', Function.update_self]
          · rw [Function.update_of_ne hi']
            refine hb i ?_
            rw [Fin.le_def] at hi ⊢
            have : (i : ℕ) ≠ (ℓ' : ℕ) := fun h => hi' (Fin.ext h)
            omega
        · funext i
          by_cases hi' : i = ℓ'
          · subst hi'
            rw [Function.update_self]
            cases hbb : b i with
            | false => exact absurd hbb hbit
            | true => rfl
          · rw [Function.update_of_ne hi', Function.update_of_ne hi']
    · intro hb
      rcases hb with hb | ⟨b₀, hb₀, rfl⟩
      · intro i hi
        refine hb i ?_
        rw [Fin.le_def] at hi ⊢
        omega
      · intro i hi
        rw [Fin.le_def] at hi
        have hi' : i ≠ ℓ' := Fin.ne_of_val_ne (by omega)
        rw [Function.update_of_ne hi']
        exact hb₀ i (by rw [Fin.le_def]; omega)
  rw [hsplit, Finset.sum_union ?hdisj, Finset.sum_image ?hinj]
  case hdisj =>
    rw [Finset.disjoint_left]
    intro b hb hb'
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp hb'
    have h1 : Function.update b₀ ℓ' true ℓ' = false :=
      (Finset.mem_filter.mp hb).2 ℓ' (Finset.mem_Iic.mpr le_rfl)
    rw [Function.update_self] at h1
    exact absurd h1 (by simp)
  case hinj =>
    intro b₁ hb₁ b₂ hb₂ heq
    funext i
    by_cases hi : i = ℓ'
    · subst hi
      rw [(Finset.mem_filter.mp (Finset.mem_coe.mp hb₁)).2 i
          (Finset.mem_Iic.mpr le_rfl),
        (Finset.mem_filter.mp (Finset.mem_coe.mp hb₂)).2 i
          (Finset.mem_Iic.mpr le_rfl)]
    · have h := congrFun heq i
      simp only [Function.update_of_ne hi] at h
      exact h
  congr 1
  exact Finset.sum_congr rfl fun b hb => by rw [hupdfalse b hb]

theorem partialEval_zero_collapse (G : Cell P → Fq) {ℓ ℓ' : Fin P.k₀}
    (hsucc : (ℓ : ℕ) + 1 = (ℓ' : ℕ)) (b : Cube P.k₀) (c : Cube P.m) :
    partialEval P Fq Dom ch G ℓ' 0 b c =
      partialEval P Fq Dom ch G ℓ (ch.α ℓ) (Function.update b ℓ' false) c := by
  have h := partialEval_boolean_collapse P Fq Dom ch G hsucc false b c
  simpa using h

theorem partialEval_one_collapse (G : Cell P → Fq) {ℓ ℓ' : Fin P.k₀}
    (hsucc : (ℓ : ℕ) + 1 = (ℓ' : ℕ)) (b : Cube P.k₀) (c : Cube P.m) :
    partialEval P Fq Dom ch G ℓ' 1 b c =
      partialEval P Fq Dom ch G ℓ (ch.α ℓ) (Function.update b ℓ' true) c := by
  have h := partialEval_boolean_collapse P Fq Dom ch G hsucc true b c
  simpa using h

/-- `hPoly` as a sum over the suffix filter. -/
theorem hPoly_eq_filter_sum (ℓ : Fin P.k₀) (X : Fq) :
    hPoly P Fq Dom S T ch ℓ X =
      ∑ b ∈ Finset.univ.filter
        (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ, b i = false),
        ∑ c : Cube P.m,
          partialEval P Fq Dom ch (liftT P Fq T) ℓ X b c *
          partialEval P Fq Dom ch (W₀ P Fq Dom S ch) ℓ X b c := by
  unfold hPoly
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.mul_sum]
  split_ifs with h
  · rw [one_mul]
  · rw [zero_mul]

/-- **Sumcheck telescoping** (`ĥ_{ℓ+1}(0) + ĥ_{ℓ+1}(1) = ĥ_ℓ(α_ℓ)`): the
message-coefficient relation that makes the constant coefficients of a
view-invisible perturbation telescope to zero (`lem:fullslice`, Step 1). -/
theorem hPoly_succ_step {ℓ ℓ' : Fin P.k₀} (hsucc : (ℓ : ℕ) + 1 = (ℓ' : ℕ)) :
    hPoly P Fq Dom S T ch ℓ' 0 + hPoly P Fq Dom S T ch ℓ' 1 =
      hPoly P Fq Dom S T ch ℓ (ch.α ℓ) := by
  rw [hPoly_eq_filter_sum, hPoly_eq_filter_sum, hPoly_eq_filter_sum,
    sum_suffix_pair P hsucc, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [partialEval_zero_collapse P Fq Dom ch _ hsucc,
      partialEval_zero_collapse P Fq Dom ch _ hsucc]
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [partialEval_one_collapse P Fq Dom ch _ hsucc,
      partialEval_one_collapse P Fq Dom ch _ hsucc]

/-- At level `0` the partial evaluation with a boolean `X`-slot is a point
evaluation of the table. -/
theorem partialEval_level_zero (G : Cell P → Fq) (xb : Bool) (b : Cube P.k₀)
    (c : Cube P.m) :
    partialEval P Fq Dom ch G ⟨0, P.k₀_pos⟩ (if xb then 1 else 0) b c =
      G (Function.update b ⟨0, P.k₀_pos⟩ xb, c) := by
  unfold partialEval
  have hprod : ∀ s : Cube P.k₀,
      (∏ i, if i < (⟨0, P.k₀_pos⟩ : Fin P.k₀) then
          (if s i then ch.α i else 1 - ch.α i)
        else if i = ⟨0, P.k₀_pos⟩ then
          (if s i then (if xb then 1 else 0) else 1 - (if xb then 1 else 0))
        else (if s i = b i then 1 else 0)) =
      if s = Function.update b ⟨0, P.k₀_pos⟩ xb then (1 : Fq) else 0 := by
    intro s
    have hfac : ∀ i, (if i < (⟨0, P.k₀_pos⟩ : Fin P.k₀) then
          (if s i then ch.α i else 1 - ch.α i)
        else if i = ⟨0, P.k₀_pos⟩ then
          (if s i then (if xb then 1 else 0) else 1 - (if xb then 1 else 0))
        else (if s i = b i then 1 else 0)) =
        (if s i = Function.update b ⟨0, P.k₀_pos⟩ xb i then (1 : Fq) else 0) := by
      intro i
      have hnot : ¬ i < (⟨0, P.k₀_pos⟩ : Fin P.k₀) := by
        simp [Fin.lt_def]
      rw [if_neg hnot]
      by_cases hi : i = ⟨0, P.k₀_pos⟩
      · rw [if_pos hi, hi, Function.update_self]
        cases xb <;> cases hsi : s (⟨0, P.k₀_pos⟩ : Fin P.k₀) <;> simp
      · rw [if_neg hi, Function.update_of_ne hi]
    rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_boole]
    by_cases hs : s = Function.update b ⟨0, P.k₀_pos⟩ xb
    · rw [if_pos hs, if_pos (fun i _ => congrFun hs i)]
    · rw [if_neg hs, if_neg fun hall => hs (funext fun i => hall i (Finset.mem_univ i))]
  rw [Finset.sum_congr rfl fun s _ => by rw [hprod s]]
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq' Finset.univ (Function.update b ⟨0, P.k₀_pos⟩ xb)
    (fun s => G (s, c)), if_pos (Finset.mem_univ _)]

/-- The full cube splits along the bit at the bottom coordinate over the
bottom suffix filter. -/
theorem sum_cube_split {M : Type*} [AddCommMonoid M] (H : Cube P.k₀ → M) :
    ∑ s : Cube P.k₀, H s =
      ∑ b ∈ Finset.univ.filter
        (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic (⟨0, P.k₀_pos⟩ : Fin P.k₀),
          b i = false),
        (H (Function.update b ⟨0, P.k₀_pos⟩ false) +
         H (Function.update b ⟨0, P.k₀_pos⟩ true)) := by
  classical
  set ℓ₀ : Fin P.k₀ := ⟨0, P.k₀_pos⟩
  have hbot : ∀ j : Fin P.k₀, ℓ₀ ≤ j := fun j => by
    rw [Fin.le_def]; exact Nat.zero_le _
  have hupdfalse : ∀ b ∈ Finset.univ.filter
      (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ₀, b i = false),
      Function.update b ℓ₀ false = b := by
    intro b hb
    funext i
    by_cases hi : i = ℓ₀
    · rw [hi, Function.update_self]
      exact ((Finset.mem_filter.mp hb).2 ℓ₀ (Finset.mem_Iic.mpr le_rfl)).symm
    · rw [Function.update_of_ne hi]
  rw [Finset.sum_add_distrib]
  have hsplit : (Finset.univ : Finset (Cube P.k₀)) =
      (Finset.univ.filter
        (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ₀, b i = false)) ∪
      (Finset.univ.filter
        (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ₀, b i = false)).image
        (fun b => Function.update b ℓ₀ true) := by
    ext b
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image, Finset.mem_Iic, true_iff]
    by_cases hbit : b ℓ₀ = false
    · left
      intro i hi
      have hieq : i = ℓ₀ := le_antisymm hi (hbot i)
      rw [hieq]; exact hbit
    · right
      refine ⟨Function.update b ℓ₀ false, fun i hi => ?_, ?_⟩
      · have hieq : i = ℓ₀ := le_antisymm hi (hbot i)
        rw [hieq, Function.update_self]
      · funext i
        by_cases hi : i = ℓ₀
        · rw [hi, Function.update_self]
          cases hbb : b ℓ₀ with
          | false => exact absurd hbb hbit
          | true => rfl
        · rw [Function.update_of_ne hi, Function.update_of_ne hi]
  conv_lhs => rw [hsplit]
  rw [Finset.sum_union ?hdisj, Finset.sum_image ?hinj]
  case hdisj =>
    rw [Finset.disjoint_left]
    intro b hb hb'
    obtain ⟨b₀, hb₀, rfl⟩ := Finset.mem_image.mp hb'
    have h1 : Function.update b₀ ℓ₀ true ℓ₀ = false :=
      (Finset.mem_filter.mp hb).2 ℓ₀ (Finset.mem_Iic.mpr le_rfl)
    rw [Function.update_self] at h1
    exact absurd h1 (by simp)
  case hinj =>
    intro b₁ hb₁ b₂ hb₂ heq
    funext i
    by_cases hi : i = ℓ₀
    · rw [hi, (Finset.mem_filter.mp (Finset.mem_coe.mp hb₁)).2 ℓ₀
          (Finset.mem_Iic.mpr le_rfl),
        (Finset.mem_filter.mp (Finset.mem_coe.mp hb₂)).2 ℓ₀
          (Finset.mem_Iic.mpr le_rfl)]
    · have h := congrFun heq i
      simp only [Function.update_of_ne hi] at h
      exact h
  congr 1
  exact Finset.sum_congr rfl fun b hb => by rw [hupdfalse b hb]

/-- **Sumcheck base case**: `ĥ_0(0) + ĥ_0(1) = ∑_u T(u)·Ŵ₀(u)`. -/
theorem hPoly_base :
    hPoly P Fq Dom S T ch ⟨0, P.k₀_pos⟩ 0 + hPoly P Fq Dom S T ch ⟨0, P.k₀_pos⟩ 1 =
      ∑ u : Cell P, liftT P Fq T u * W₀ P Fq Dom S ch u := by
  rw [hPoly_eq_filter_sum, hPoly_eq_filter_sum]
  have hzero : ∀ (G : Cell P → Fq) b c,
      partialEval P Fq Dom ch G ⟨0, P.k₀_pos⟩ 0 b c =
        G (Function.update b ⟨0, P.k₀_pos⟩ false, c) := fun G b c => by
    have h := partialEval_level_zero P Fq Dom ch G false b c
    simpa using h
  have hone : ∀ (G : Cell P → Fq) b c,
      partialEval P Fq Dom ch G ⟨0, P.k₀_pos⟩ 1 b c =
        G (Function.update b ⟨0, P.k₀_pos⟩ true, c) := fun G b c => by
    have h := partialEval_level_zero P Fq Dom ch G true b c
    simpa using h
  rw [Fintype.sum_prod_type,
    sum_cube_split P (fun s => ∑ c : Cube P.m,
      liftT P Fq T (s, c) * W₀ P Fq Dom S ch (s, c)),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  · exact Finset.sum_congr rfl fun c _ => by rw [hzero, hzero]
  · exact Finset.sum_congr rfl fun c _ => by rw [hone, hone]

/-- The partial evaluation is affine in the `X`-slot. -/
theorem partialEval_affine (G : Cell P → Fq) (ℓ : Fin P.k₀) (X : Fq)
    (b : Cube P.k₀) (c : Cube P.m) :
    partialEval P Fq Dom ch G ℓ X b c =
      partialEval P Fq Dom ch G ℓ 0 b c +
        X * (partialEval P Fq Dom ch G ℓ 1 b c -
             partialEval P Fq Dom ch G ℓ 0 b c) := by
  unfold partialEval
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  -- pull the `ℓ`-factor out of each product; the rest carries no `X`
  have hpull : ∀ Y : Fq,
      (∏ i, if i < ℓ then (if s i then ch.α i else 1 - ch.α i)
        else if i = ℓ then (if s i then Y else 1 - Y)
        else (if s i = b i then 1 else 0)) =
      (if s ℓ then Y else 1 - Y) *
      ∏ i ∈ Finset.univ.erase ℓ,
        (if i < ℓ then (if s i then ch.α i else 1 - ch.α i)
          else (if s i = b i then 1 else 0)) := by
    intro Y
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ℓ), if_neg (lt_irrefl ℓ),
      if_pos rfl]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    have hne : i ≠ ℓ := (Finset.mem_erase.mp hi).1
    by_cases hlt : i < ℓ
    · rw [if_pos hlt, if_pos hlt]
    · rw [if_neg hlt, if_neg hne, if_neg hlt]
  rw [hpull X, hpull 0, hpull 1]
  cases hsl : s ℓ <;> simp <;> ring

/-- A quadratic vanishing at `0, 1, 2` vanishes identically (`p ≠ 2`). -/
theorem quadratic_zero_of_three {q₀ q₁ q₂ : Fq} (h2 : (2 : Fq) ≠ 0)
    (e0 : q₀ = 0) (e1 : q₀ + q₁ + q₂ = 0) (e2 : q₀ + 2 * q₁ + 4 * q₂ = 0)
    (y : Fq) : q₀ + y * q₁ + y ^ 2 * q₂ = 0 := by
  subst e0
  have hq2 : q₂ = 0 := by
    have h : 2 * q₂ = 0 := by linear_combination e2 - 2 * e1
    exact (mul_eq_zero.mp h).resolve_left h2
  subst hq2
  have hq1 : q₁ = 0 := by linear_combination e1
  subst hq1
  ring

/-- `hPoly` is a quadratic in the evaluation point. -/
theorem hPoly_quadratic (ℓ : Fin P.k₀) :
    ∃ q₀ q₁ q₂ : Fq, ∀ X : Fq,
      hPoly P Fq Dom S T ch ℓ X = q₀ + X * q₁ + X ^ 2 * q₂ := by
  classical
  set A := fun (b : Cube P.k₀) (c : Cube P.m) =>
    partialEval P Fq Dom ch (liftT P Fq T) ℓ 0 b c with hA
  set A' := fun (b : Cube P.k₀) (c : Cube P.m) =>
    partialEval P Fq Dom ch (liftT P Fq T) ℓ 1 b c -
    partialEval P Fq Dom ch (liftT P Fq T) ℓ 0 b c with hA'
  set W := fun (b : Cube P.k₀) (c : Cube P.m) =>
    partialEval P Fq Dom ch (W₀ P Fq Dom S ch) ℓ 0 b c with hW
  set W' := fun (b : Cube P.k₀) (c : Cube P.m) =>
    partialEval P Fq Dom ch (W₀ P Fq Dom S ch) ℓ 1 b c -
    partialEval P Fq Dom ch (W₀ P Fq Dom S ch) ℓ 0 b c with hW'
  refine ⟨∑ b : Cube P.k₀, ∑ c : Cube P.m,
      (if ∀ i ∈ Finset.Iic ℓ, b i = false then 1 else 0) * (A b c * W b c),
    ∑ b : Cube P.k₀, ∑ c : Cube P.m,
      (if ∀ i ∈ Finset.Iic ℓ, b i = false then 1 else 0) *
        (A b c * W' b c + A' b c * W b c),
    ∑ b : Cube P.k₀, ∑ c : Cube P.m,
      (if ∀ i ∈ Finset.Iic ℓ, b i = false then 1 else 0) * (A' b c * W' b c),
    fun X => ?_⟩
  unfold hPoly
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [partialEval_affine P Fq Dom ch (liftT P Fq T) ℓ X b c,
    partialEval_affine P Fq Dom ch (W₀ P Fq Dom S ch) ℓ X b c]
  simp only [hA, hA', hW, hW']
  ring

/-- The message polynomial of an invisible table vanishes at **every**
evaluation point — the engine of the `(ℓ, y)`-family of channel identities
(`lem:fullslice`, Step 1). -/
theorem hPoly_eq_zero_of_invisible (h2 : (2 : Fq) ≠ 0) (Δ : Cell P → Fp P)
    (hinv : Invisible P Fq Dom S ch Δ) (ℓ : Fin P.k₀) (y : Fq) :
    hPoly P Fq Dom S Δ ch ℓ y = 0 := by
  obtain ⟨q₀, q₁, q₂, hq⟩ := hPoly_quadratic P Fq Dom S Δ ch ℓ
  have e0 : q₀ = 0 := by
    have := hinv.msg0 ℓ
    rwa [hq 0, zero_mul, add_zero, zero_pow (by norm_num), zero_mul,
      add_zero] at this
  have e1 : q₀ + q₁ + q₂ = 0 := by
    have h := hinv.msg1 ℓ
    rw [hq 1] at h
    linear_combination h
  have e2 : q₀ + 2 * q₁ + 4 * q₂ = 0 := by
    have h := hinv.msg2 ℓ
    rw [hq 2] at h
    linear_combination h
  have hz := quadratic_zero_of_three Fq h2 e0 e1 e2 y
  rw [hq y]
  linear_combination hz

end ZkWhir
