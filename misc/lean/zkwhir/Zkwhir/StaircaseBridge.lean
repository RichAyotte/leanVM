/-
Bridge from the protocol's Lagrange weights (`eqPoly`, `mixedPoint`) to the
abstract staircase tensors of `Zkwhir.StaircaseTensor`. The key facts:

* `eqPoly p = ptensor (vrow ∘ p)` — a Lagrange weight is the pure tensor of
  the per-slot 2-vectors `vrow t = (1 − t, t)`;
* `{vrow x, drow}` (with `drow = (−1, 1)`) is a basis of `F²` for *every*
  `x` — so the staircase basis hypothesis is unconditional;
* `ptensor` is multilinear in each slot (`ptensor_update_add/smul`).

Together these let `êq(mixedPoint ℓ y z)` be expanded in the `ω/τ` staircase
basis, the input the coupled-chains kernel (`CoupledKer`) consumes.

Part of the `GoodSetAbsorption` formalization campaign; unwired until green.
-/
import Mathlib
import Zkwhir.Statement
import Zkwhir.StaircaseTensor

set_option linter.style.header false

noncomputable section

namespace ZkWhir

variable {F : Type*} [Field F]

/-- The per-slot Lagrange 2-vector `(1 − t, t)`. -/
def vrow (t : F) : Bool → F := fun b => if b then t else 1 - t

/-- The fixed difference vector `(−1, 1)` (slot-independent). -/
def drow : Bool → F := fun b => if b then 1 else -1

/-- A Lagrange weight is the pure tensor of its per-slot 2-vectors. -/
theorem eqPoly_eq_ptensor {j : ℕ} (p : Fin j → F) :
    eqPoly p = ptensor (fun i => vrow (p i)) := by
  funext s
  unfold eqPoly ptensor vrow
  exact Finset.prod_congr rfl fun i _ => by cases s i <;> simp

/-- `{vrow x, drow}` is a basis of `F²`, for every `x`. -/
theorem vrow_basis (x : F) (x' y' : F)
    (h : ∀ b, x' * vrow x b + y' * drow b = 0) : x' = 0 ∧ y' = 0 := by
  have h0 := h false
  have h1 := h true
  simp only [vrow, drow, Bool.false_eq_true, if_false, if_true] at h0 h1
  have hx' : x' = 0 := by linear_combination h0 + h1
  refine ⟨hx', ?_⟩
  rw [hx'] at h1
  simpa using h1

/-- The affine relation `vrow t = vrow x + (t − x) • drow`, slotwise. -/
theorem vrow_affine (t x : F) :
    vrow t = fun b => vrow x b + (t - x) * drow b := by
  funext b
  cases b <;> simp [vrow, drow]

/-- **Slot additivity** of `ptensor`: splitting one slot's vector into a sum
splits the tensor. -/
theorem ptensor_update_add {k : ℕ} (w : Fin k → Bool → F) (ℓ : Fin k)
    (p q : Bool → F) :
    ptensor (Function.update w ℓ (fun b => p b + q b)) =
      ptensor (Function.update w ℓ p) + ptensor (Function.update w ℓ q) := by
  funext s
  simp only [ptensor, Pi.add_apply]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ℓ),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ ℓ),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ ℓ)]
  have herase : ∀ (r : Bool → F),
      ∏ i ∈ Finset.univ.erase ℓ, Function.update w ℓ r i (s i) =
      ∏ i ∈ Finset.univ.erase ℓ, w i (s i) :=
    fun r => Finset.prod_congr rfl fun i hi =>
      by rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [herase p, herase q, herase (fun b => p b + q b),
    Function.update_self, Function.update_self, Function.update_self]
  ring

/-- **Slot homogeneity** of `ptensor`: scaling one slot's vector scales the
tensor. -/
theorem ptensor_update_smul {k : ℕ} (w : Fin k → Bool → F) (ℓ : Fin k)
    (t : F) (r : Bool → F) :
    ptensor (Function.update w ℓ (fun b => t * r b)) =
      t • ptensor (Function.update w ℓ r) := by
  funext s
  simp only [ptensor, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ℓ),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ ℓ)]
  have herase :
      ∏ i ∈ Finset.univ.erase ℓ, Function.update w ℓ (fun b => t * r b) i (s i) =
      ∏ i ∈ Finset.univ.erase ℓ, Function.update w ℓ r i (s i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.mem_erase.mp hi).1,
        Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [herase, Function.update_self, Function.update_self]
  ring

end ZkWhir
