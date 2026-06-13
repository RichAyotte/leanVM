/-
`cond:twist`: the trace-twist node functional is forced to be untwisted
(multiplication by a scalar), via Ore's theorem (`exists_qpoly_repr`) plus the
Frobenius-staircase rigidity argument.

Developed UNWIRED until it compiles clean.
Part of the `GoodSetAbsorption` formalization campaign.
-/
import Mathlib
import Zkwhir.Statement
import Zkwhir.Linearized
import Zkwhir.StaircaseBridge
import Zkwhir.StaircaseTensor

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.style.show false

namespace ZkWhir

variable {Fq : Type*} [Field Fq] [Fintype Fq] {p : ℕ} [Fact p.Prime] [CharP Fq p]

/-- **Frobenius–`eqPoly` connection**: the `p^r`-power of a Lagrange weight is the
weight at the Frobenius-conjugated point, `êq(x, s)^{p^r} = êq(x^{p^r}, s)`. This
turns `λ_s^{p^r}` into the conjugated extension row `η^{[r]}_s`. -/
theorem eqPoly_pow {j : ℕ} (r : ℕ) (xs : Fin j → Fq) (s : Cube j) :
    (eqPoly xs s) ^ p ^ r = eqPoly (fun i => xs i ^ p ^ r) s := by
  unfold eqPoly
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  split_ifs with h
  · rfl
  · exact Linearized.iterateFrobenius_one_sub r (xs i)

variable {Fp : Type*} [Field Fp] [Fintype Fp] [Algebra Fp Fq] [CharP Fp p]

/-- **The conjugated-row decomposition** (`cond:twist`): an `Fp`-linear map `T`
evaluated along the Lagrange weights `λ_s = êq(α, s)` is the `t`-combination of
the Frobenius-conjugated extension rows `η^{[r]}_s = êq(α^{[r]}, s)`, where `t`
are the q-polynomial coefficients of `T` (Ore's theorem). -/
theorem T_eval_eqPoly {j : ℕ} (hcard : Fintype.card Fp = p) (d : ℕ)
    (hd : Fintype.card Fq = p ^ d) (hdeg : Module.finrank Fp Fq = d)
    (T : Fq →ₗ[Fp] Fq) (α : Fin j → Fq) :
    ∃ t : Fin d → Fq, ∀ s : Cube j,
      T (eqPoly α s) = ∑ r, t r * eqPoly (fun i => α i ^ p ^ r.val) s := by
  obtain ⟨t, ht⟩ := Linearized.exists_qpoly_repr hcard d hd hdeg T
  refine ⟨t, fun s => ?_⟩
  rw [ht (eqPoly α s)]
  exact Finset.sum_congr rfl fun r _ => by rw [eqPoly_pow]

/-! ## Staircase coordinate functionals (`lem:rigidity`)

The `{c_i = vrow(x_i), d = drow}` basis of each slot plane has dual functionals
`γ^c` (the `c`-coordinate, independent of `x`) and `γ^d_x` (the `d`-coordinate).
They read off the staircase coefficients in the rigidity argument. -/

/-- The `c`-coordinate functional: the `vrow`-coefficient of a slot vector
(independent of the base point `x`). -/
def gammaC (w : Bool → Fq) : Fq := w false + w true

/-- The `d`-coordinate functional at base point `x`: the `drow`-coefficient. -/
def gammaD (x : Fq) (w : Bool → Fq) : Fq := w true - x * (w false + w true)

@[simp] theorem gammaC_vrow (x : Fq) : gammaC (vrow x) = 1 := by
  show (1 - x) + x = 1; ring

@[simp] theorem gammaC_drow : gammaC (drow : Bool → Fq) = 0 := by
  show (-1 : Fq) + 1 = 0; ring

@[simp] theorem gammaD_vrow (x : Fq) : gammaD x (vrow x) = 0 := by
  show x - x * ((1 - x) + x) = 0; ring

@[simp] theorem gammaD_drow (x : Fq) : gammaD x (drow : Bool → Fq) = 1 := by
  show (1 : Fq) - x * ((-1) + 1) = 1; ring

/-- `γ^c` is additive (a slot functional). -/
theorem gammaC_add (w w' : Bool → Fq) : gammaC (w + w') = gammaC w + gammaC w' := by
  simp only [gammaC, Pi.add_apply]; ring

/-- `γ^d` is additive. -/
theorem gammaD_add (x : Fq) (w w' : Bool → Fq) :
    gammaD x (w + w') = gammaD x w + gammaD x w' := by
  simp only [gammaD, Pi.add_apply]; ring

/-- `γ^c` is homogeneous over scalars. -/
theorem gammaC_smul (a : Fq) (w : Bool → Fq) : gammaC (a • w) = a * gammaC w := by
  simp only [gammaC, Pi.smul_apply, smul_eq_mul]; ring

/-- `γ^d` is homogeneous over scalars. -/
theorem gammaD_smul (x a : Fq) (w : Bool → Fq) :
    gammaD x (a • w) = a * gammaD x w := by
  simp only [gammaD, Pi.smul_apply, smul_eq_mul]; ring

/-- The slot indicator vector `e_b`. -/
def eBool (b : Bool) : Bool → Fq := fun b' => if b' = b then 1 else 0

/-- Every slot vector is its `e`-basis expansion. -/
theorem bool_basis (w : Bool → Fq) :
    w = (w false) • eBool false + (w true) • eBool true := by
  funext b
  cases b <;> simp [eBool, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem gammaC_linBool (w : Bool → Fq) :
    gammaC w = w false * gammaC (eBool false) + w true * gammaC (eBool true) := by
  conv_lhs => rw [bool_basis w]
  rw [gammaC_add, gammaC_smul, gammaC_smul]

theorem gammaD_linBool (x : Fq) (w : Bool → Fq) :
    gammaD x w = w false * gammaD x (eBool false) + w true * gammaD x (eBool true) := by
  conv_lhs => rw [bool_basis w]
  rw [gammaD_add, gammaD_smul, gammaD_smul]

/-- The tensor coefficient functional for a per-slot family `ψ`: reads the
coefficient of `f` against `⊗_i ψ_i` in the slot bases. -/
def tcoeff {k : ℕ} (ψ : Fin k → (Bool → Fq) → Fq) (f : Cube k → Fq) : Fq :=
  ∑ s : Cube k, (∏ i, ψ i (eBool (s i))) * f s

/-- **The tensor coefficient of a pure tensor factorizes**: `φ_S(⊗ w_i) = ∏_i ψ_i(w_i)`. -/
theorem tcoeff_ptensor {k : ℕ} (ψ : Fin k → (Bool → Fq) → Fq)
    (hlin : ∀ (i : Fin k) (w : Bool → Fq),
      ψ i w = w false * ψ i (eBool false) + w true * ψ i (eBool true))
    (w : Fin k → Bool → Fq) :
    tcoeff ψ (ptensor w) = ∏ i, ψ i (w i) := by
  unfold tcoeff ptensor
  rw [show (∑ s : Cube k, (∏ i, ψ i (eBool (s i))) * ∏ i, w i (s i)) =
      ∑ s : Cube k, ∏ i, (ψ i (eBool (s i)) * w i (s i)) from
    Finset.sum_congr rfl fun s _ => (Finset.prod_mul_distrib).symm]
  rw [sum_cube_prod Fq (fun i b => ψ i (eBool b) * w i b)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hlin i (w i)]; ring

/-- The combined slot vector `c_i + lam·d` written out (a `stairVec` slot for
`i < m`). -/
theorem aVec_eq (x lam : Fq) :
    (fun b => vrow x b + lam * drow b) = vrow x + lam • drow := by
  funext b; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

@[simp] theorem gammaC_aVec (x lam : Fq) :
    gammaC (fun b => vrow x b + lam * drow b) = 1 := by
  rw [aVec_eq, gammaC_add, gammaC_smul, gammaC_vrow, gammaC_drow]; ring

@[simp] theorem gammaD_aVec (x lam : Fq) :
    gammaD x (fun b => vrow x b + lam * drow b) = lam := by
  rw [aVec_eq, gammaD_add, gammaD_smul, gammaD_vrow, gammaD_drow]; ring

/-- The per-slot functional family selecting `γ^d` on the `d`-slots `S` and
`γ^c` elsewhere (the coefficient functional `φ_S`). -/
def dCoeff {k : ℕ} (x : Fin k → Fq) (S : Finset (Fin k)) :
    Fin k → (Bool → Fq) → Fq := fun i => if i ∈ S then gammaD (x i) else gammaC

theorem dCoeff_hlin {k : ℕ} (x : Fin k → Fq) (S : Finset (Fin k)) :
    ∀ (i : Fin k) (w : Bool → Fq),
      dCoeff x S i w =
        w false * dCoeff x S i (eBool false) + w true * dCoeff x S i (eBool true) := by
  intro i w
  unfold dCoeff
  split_ifs
  · exact gammaD_linBool (x i) w
  · exact gammaC_linBool w

/-- **Coefficient of `v^{(r)} = ⊗(c_i + a_i d)`**: `φ_S(v) = ∏_{i∈S} a_i`. -/
theorem tcoeff_vTensor {k : ℕ} (x a : Fin k → Fq) (S : Finset (Fin k)) :
    tcoeff (dCoeff x S)
        (ptensor (fun i => fun b => vrow (x i) b + a i * drow b)) =
      ∏ i ∈ S, a i := by
  rw [tcoeff_ptensor (dCoeff x S) (dCoeff_hlin x S)]
  rw [show (∏ i, dCoeff x S i (fun b => vrow (x i) b + a i * drow b)) =
      ∏ i, (if i ∈ S then a i else 1) from by
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold dCoeff
    split_ifs
    · exact gammaD_aVec (x i) (a i)
    · exact gammaC_aVec (x i) (a i)]
  rw [← Finset.prod_filter]
  congr 1
  ext i; simp

/-- **Coefficient of `ω = ⊗ c_i`**: `φ_S(ω) = 1` if `S = ∅`, else `0`. -/
theorem tcoeff_omegaTensor {k : ℕ} (x : Fin k → Fq) (S : Finset (Fin k)) :
    tcoeff (dCoeff x S) (ptensor (fun i => vrow (x i))) =
      if S = ∅ then 1 else 0 := by
  rw [tcoeff_ptensor (dCoeff x S) (dCoeff_hlin x S)]
  rw [show (∏ i, dCoeff x S i (vrow (x i))) = ∏ i, (if i ∈ S then (0 : Fq) else 1) from by
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold dCoeff
    split_ifs
    · exact gammaD_vrow (x i)
    · exact gammaC_vrow (x i)]
  split_ifs with hS
  · subst hS; simp
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_pos hj])

end ZkWhir
