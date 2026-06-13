/-
Linearized (q-)polynomials: every `Fp`-linear endomorphism of a finite field
`Fq = F_{p^d}` is `x ↦ ∑_{r<d} t_r x^{p^r}` for unique `t_r ∈ Fq` (Ore's theorem).
This is the algebraic foundation of `cond:twist` and is not in Mathlib.

Developed UNWIRED (not imported by `Zkwhir.lean`) until it compiles clean.
Part of the `GoodSetAbsorption` formalization campaign.
-/
import Mathlib

set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace ZkWhir.Linearized

open Polynomial

variable {Fp Fq : Type*} [Field Fp] [Field Fq] [Fintype Fp] [Fintype Fq]
  [Algebra Fp Fq] {p : ℕ} [Fact p.Prime] [CharP Fp p]

/-- `frobenius` of `Fq` (the `p`-power map) fixes the image of the base prime
field `Fp` (`card Fp = p`): `(algebraMap a)^p = algebraMap a`, since `a^p = a`. -/
theorem frobenius_algebraMap [CharP Fq p] (hcard : Fintype.card Fp = p) (a : Fp) :
    frobenius Fq p (algebraMap Fp Fq a) = algebraMap Fp Fq a := by
  rw [frobenius_def, ← map_pow, ← hcard, FiniteField.pow_card]

end ZkWhir.Linearized
