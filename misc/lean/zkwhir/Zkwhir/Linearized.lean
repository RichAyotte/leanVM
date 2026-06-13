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

/-- Freshman's dream for `1 - a`: `(1 - a)^{p^r} = 1 - a^{p^r}` (iterated Frobenius
is a ring hom). The per-factor identity behind `λ_s^{p^r} = eqPoly(α^{[r]}, s)`. -/
theorem iterateFrobenius_one_sub [CharP Fq p] (r : ℕ) (a : Fq) :
    (1 - a) ^ p ^ r = 1 - a ^ p ^ r := by
  have h1 : (1 - a) ^ p ^ r = iterateFrobenius Fq p r (1 - a) := (iterateFrobenius_def p r _).symm
  rw [h1, map_sub, map_one, iterateFrobenius_def]

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

/-- The q-polynomial map: a coefficient tuple `t : Fin d → Fq` to the `Fp`-linear
endomorphism `x ↦ ∑_{r<d} t_r x^{p^r}`. -/
def qpolyMap [CharP Fq p] (hcard : Fintype.card Fp = p) (d : ℕ) :
    (Fin d → Fq) →ₗ[Fp] (Fq →ₗ[Fp] Fq) where
  toFun t := ∑ r, t r • frobLin hcard r.val
  map_add' t t' := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a t := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_assoc, Finset.smul_sum]

theorem qpolyMap_apply [CharP Fq p] (hcard : Fintype.card Fp = p) (d : ℕ)
    (t : Fin d → Fq) (x : Fq) :
    qpolyMap hcard d t x = ∑ r, t r * x ^ p ^ r.val := by
  rw [qpolyMap]
  simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.sum_apply, LinearMap.smul_apply,
    frobLin_apply, smul_eq_mul]

/-- The q-polynomial map is injective: distinct coefficient tuples give distinct
endomorphisms (a nonzero q-polynomial has degree `< |Fq|`, so is not the zero
function). -/
theorem qpolyMap_injective [CharP Fq p] (hcard : Fintype.card Fp = p) (d : ℕ)
    (hd : Fintype.card Fq = p ^ d) :
    Function.Injective (qpolyMap (Fq := Fq) hcard d) := by
  rw [injective_iff_map_eq_zero]
  intro t ht
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have hfun : ∀ x : Fq, ∑ r : Fin d, t r * x ^ p ^ r.val = 0 := fun x => by
    rw [← qpolyMap_apply hcard d t x, ht, LinearMap.zero_apply]
  set Q : Fq[X] := ∑ r : Fin d, C (t r) * X ^ p ^ r.val with hQ
  have hQeval : ∀ x : Fq, eval x Q = 0 := fun x => by
    rw [hQ, eval_finset_sum]
    simp only [eval_mul, eval_C, eval_pow, eval_X]
    exact hfun x
  have hpd : 0 < p ^ d := pow_pos (by omega) d
  have hbound : Q.natDegree ≤ p ^ d - 1 := by
    rw [hQ]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun r _ => ?_)
    calc (C (t r) * X ^ p ^ r.val).natDegree
        ≤ p ^ r.val := le_trans (natDegree_C_mul_le _ _) (le_of_eq (natDegree_X_pow _))
      _ ≤ p ^ d - 1 := by
          have : p ^ r.val < p ^ d := Nat.pow_lt_pow_right hp1 r.2
          omega
  have hQdeg : Q.natDegree < Fintype.card Fq := by rw [hd]; omega
  have hQ0 : Q = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q (f := (id : Fq → Fq))
      Function.injective_id (fun x => hQeval x) hQdeg
  funext r
  have hcoeff : Q.coeff (p ^ r.val) = t r := by
    rw [hQ, Polynomial.finset_sum_coeff, Finset.sum_eq_single r]
    · rw [coeff_C_mul, coeff_X_pow, if_pos rfl, mul_one]
    · intro r' _ hr'
      rw [coeff_C_mul, coeff_X_pow]
      split_ifs with h
      · exact absurd (Fin.ext (Nat.pow_right_injective hp1 h)) (Ne.symm hr')
      · rw [mul_zero]
    · intro h; exact absurd (Finset.mem_univ r) h
  rw [hQ0, coeff_zero] at hcoeff
  exact hcoeff.symm

/-- **Ore's theorem** (linearized/q-polynomial representation): every `Fp`-linear
endomorphism of `Fq = F_{p^d}` is `x ↦ ∑_{r<d} t_r x^{p^r}` for some `t : Fin d → Fq`.
This is the algebraic input to `cond:twist`. -/
theorem exists_qpoly_repr [CharP Fq p] (hcard : Fintype.card Fp = p) (d : ℕ)
    (hd : Fintype.card Fq = p ^ d) (hdeg : Module.finrank Fp Fq = d)
    (T : Fq →ₗ[Fp] Fq) :
    ∃ t : Fin d → Fq, ∀ x, T x = ∑ r, t r * x ^ p ^ r.val := by
  have hfin : Module.finrank Fp (Fin d → Fq) = Module.finrank Fp (Fq →ₗ[Fp] Fq) := by
    rw [Module.finrank_pi_fintype, Module.finrank_linearMap Fp Fp Fq Fq]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, hdeg]
  obtain ⟨t, ht⟩ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp
      (qpolyMap_injective hcard d hd) T
  exact ⟨t, fun x => by rw [← ht, qpolyMap_apply]⟩

end ZkWhir.Linearized
