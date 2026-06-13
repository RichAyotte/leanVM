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

set_option linter.style.header false
set_option linter.unusedSectionVars false

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

end ZkWhir
