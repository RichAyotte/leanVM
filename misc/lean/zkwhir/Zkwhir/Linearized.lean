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

/-- The iterated Frobenius `x ↦ x^{p^r}` fixes the base prime field. -/
theorem iterateFrobenius_algebraMap [CharP Fq p] (hcard : Fintype.card Fp = p)
    (r : ℕ) (a : Fp) :
    iterateFrobenius Fq p r (algebraMap Fp Fq a) = algebraMap Fp Fq a := by
  rw [iterateFrobenius_def, ← map_pow]
  congr 1
  rw [← hcard]
  exact FiniteField.pow_card_pow r a

/-- The iterated Frobenius `x ↦ x^{p^r}` as an `Fp`-linear endomorphism of `Fq`
(it is additive and fixes the base field). -/
def frobLin [CharP Fq p] (hcard : Fintype.card Fp = p) (r : ℕ) : Fq →ₗ[Fp] Fq where
  toFun := iterateFrobenius Fq p r
  map_add' x y := map_add _ _ _
  map_smul' a x := by
    simp only [RingHom.id_apply]
    rw [Algebra.smul_def, map_mul, iterateFrobenius_algebraMap hcard, ← Algebra.smul_def]

@[simp] theorem frobLin_apply [CharP Fq p] (hcard : Fintype.card Fp = p) (r : ℕ)
    (x : Fq) : frobLin hcard r x = x ^ p ^ r := by
  rw [frobLin]; exact iterateFrobenius_def p r x

end ZkWhir.Linearized
