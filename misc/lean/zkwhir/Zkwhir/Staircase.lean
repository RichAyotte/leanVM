/-
Foundations for the staircase independence (`lem:staircase` / `thm:twopoint`):
the Lagrange weight vectors `êq(p, ·)` are tensor products of the 2-vectors
`(1 − pᵢ, pᵢ)` over the coordinates; peeling the top coordinate factors them
through partial evaluation, the engine of the row-independence induction
behind `RowSurj`.

Part of the `GoodSetAbsorption` formalization campaign.
-/
import Mathlib
import Zkwhir.Statement
import Zkwhir.Channel

set_option linter.style.header false
set_option linter.unusedSectionVars false

noncomputable section

namespace ZkWhir

variable (Fq : Type*) [Field Fq] [Fintype Fq]

/-- Peeling the top coordinate of a Lagrange weight: `êq` at a `snoc`-point
and a `snoc`-vertex factors. -/
theorem eqPoly_snoc {R : Type*} [CommRing R] {j : ℕ} (p : Fin j → R) (t : R)
    (s : Cube j) (b : Bool) :
    eqPoly (Fin.snoc p t) (Fin.snoc s b) =
      eqPoly p s * (if b then t else 1 - t) := by
  unfold eqPoly
  rw [Fin.prod_univ_castSucc]
  congr 1
  · exact Finset.prod_congr rfl fun i _ => by
      rw [Fin.snoc_castSucc, Fin.snoc_castSucc]
  · rw [Fin.snoc_last, Fin.snoc_last]

/-- **Partition of unity**: the Lagrange weights at any point sum to `1`. -/
theorem eqPoly_sum_eq_one {j : ℕ} (p : Fin j → Fq) :
    ∑ s : Cube j, eqPoly p s = 1 := by
  refine (sum_cube_prod Fq
    (fun i bit => if bit then p i else 1 - p i)).trans ?_
  refine Finset.prod_eq_one fun i _ => ?_
  simp only [Bool.false_eq_true, if_false, if_true]
  ring

/-- A Lagrange weight vector is never zero. -/
theorem eqPoly_vec_ne_zero {j : ℕ} (p : Fin j → Fq) :
    (fun s : Cube j => eqPoly p s) ≠ 0 := by
  intro h
  have h1 := eqPoly_sum_eq_one Fq p
  rw [show (fun s : Cube j => eqPoly p s) = 0 from h] at h1
  simp at h1

/-- The top-coordinate slice of a `snoc`-point weight vector is a scalar
multiple of the lower weight vector: the tensor factorization that drives
the staircase induction. -/
theorem eqPoly_vec_snoc {j : ℕ} (p : Fin j → Fq) (t : Fq) (b : Bool) :
    (fun s : Cube j => eqPoly (Fin.snoc p t) (Fin.snoc s b)) =
      (if b then t else 1 - t) • (fun s : Cube j => eqPoly p s) := by
  funext s
  rw [Pi.smul_apply, smul_eq_mul, eqPoly_snoc, mul_comm]

end ZkWhir
