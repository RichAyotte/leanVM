/-
The `2×2` cross-witness route in determinant-vanishing form.

`masked_whir_statistical_zk_of_crossWitness2` (Pinprob) reduces the whole masked-WHIR
zero-knowledge proof to four polynomials over `JointIdx` with: their `2×2` minor nonzero (P4),
bounded degree (P3), and — on the `cond:cross2` event — a nonzero kernel direction `θ` of the
evaluated `2×2` matrix (C2).

This file makes the `2×2` linear algebra of C2 mechanical: a `2×2` system with vanishing
determinant has an explicit nonzero kernel (`exists_kernel_of_det2_eq_zero`), so the C2
obligation can be discharged in the cleaner *minor-vanishes-on-the-event* form
(`masked_whir_statistical_zk_of_crossWitness2_detVanish`). Together with the P4 reduction
`crossWitness2_det_ne_zero_of_point`, both `2×2` obligations are now mechanical; the residual is
exactly: construct the four polynomials, bound their degrees, and prove the minor polynomial
vanishes on the `cond:cross2` event (the `lem:fullslice`/`lem:noother` forward content).

Part of the `GoodSetAbsorption` formalization campaign.
-/
import Mathlib
import Zkwhir.Pinprob

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

open scoped ENNReal

namespace ZkWhir

variable (P : Params) (Fq : Type*) [Field Fq] [Fintype Fq] [Algebra (Fp P) Fq]
  (Dom : Finset (Fp P)) [Nonempty {x // x ∈ Dom}] (S : Stmt P Fq)

/-- **A `2×2` system with vanishing determinant has a nonzero kernel direction** (the C2
θ-extraction, scalar form): if `a·d − b·c = 0` then there is a nonzero `θ : Fin 2 → Fq` with
`θ₀·a + θ₁·b = 0` and `θ₀·c + θ₁·d = 0`. Explicit kernel: `(b, −a)` when `(a,b) ≠ 0`,
`(d, −c)` when `(a,b) = 0 ≠ (c,d)`, `(1, 0)` otherwise. This is the converse companion of
`mvpoly_det2_ne_zero`: together they bracket the `2×2` linear algebra of the `cond:cross2`
witness, so the `hker` (C2) obligation of `masked_whir_statistical_zk_of_crossWitness2` is
mechanical once the minor polynomial vanishes on the event. -/
theorem exists_kernel_of_det2_eq_zero (a b c d : Fq) (h : a * d - b * c = 0) :
    ∃ θ : Fin 2 → Fq, θ ≠ 0 ∧ θ 0 * a + θ 1 * b = 0 ∧ θ 0 * c + θ 1 * d = 0 := by
  by_cases hab : a = 0 ∧ b = 0
  · obtain ⟨ha, hb⟩ := hab
    by_cases hcd : c = 0 ∧ d = 0
    · obtain ⟨hc, hd⟩ := hcd
      refine ⟨![1, 0], ?_, ?_, ?_⟩
      · intro hcon
        have h00 := congrFun hcon 0
        simp only [Matrix.cons_val_zero, Pi.zero_apply] at h00
        exact one_ne_zero h00
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [ha, hb]; ring
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [hc, hd]; ring
    · refine ⟨![d, -c], ?_, ?_, ?_⟩
      · intro hcon
        apply hcd
        have h0 := congrFun hcon 0
        have h1 := congrFun hcon 1
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
          Pi.zero_apply] at h0 h1
        exact ⟨neg_eq_zero.mp h1, h0⟩
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [ha, hb]; ring
      · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
        ring
  · refine ⟨![b, -a], ?_, ?_, ?_⟩
    · intro hcon
      apply hab
      have h0 := congrFun hcon 0
      have h1 := congrFun hcon 1
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one,
        Pi.zero_apply] at h0 h1
      exact ⟨neg_eq_zero.mp h1, h0⟩
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      ring
    · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      linear_combination -h

/-- **Masked WHIR HVZK from a `2×2` cross witness, det-vanishing (C2) form.** Identical to
`masked_whir_statistical_zk_of_crossWitness2` except the `cond:cross2` obligation (C2) is the
cleaner *minor-vanishes-on-the-event* containment instead of the explicit kernel direction `θ`:
it suffices that on the `cond:cross2` event the minor polynomial `pFu·pTu'' − pTu·pFu''`
evaluates to `0` at `jointPoint ch`. The explicit `θ` is recovered for free by
`exists_kernel_of_det2_eq_zero` (a `2×2` system with zero determinant has a nonzero kernel), so
this is equivalent to the `hker` form while matching the shape the joint Schwartz–Zippel bound
(`event_le_of_jointDetPoly`) consumes. Together with `crossWitness2_det_ne_zero_of_point` (P4),
both `2×2` linear-algebra obligations of the witness are mechanical; the residual is exactly:
construct the four polynomials, bound their degrees (P3), and prove the minor vanishes on the
`cond:cross2` event (the `lem:fullslice`/`lem:noother` forward content). -/
theorem masked_whir_statistical_zk_of_crossWitness2_detVanish
    [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] [FiniteDimensional (Fp P) (Cube P.m → Fq)]
    {ιβ : Type*} [Fintype ιβ] (b : Module.Basis ιβ (Fp P) Fq)
    (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S) (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (hprime : (Module.finrank (Fp P) Fq).Prime)
    (hpdvd : (P.p - 1) ∣ (Fintype.card Fq - 1))
    (hcop : Nat.Coprime (2 ^ P.k₀) ((Fintype.card Fq - 1) / (P.p - 1)))
    (hdk : Module.finrank (Fp P) Fq ≤ P.k₀)
    (hslack : 1 + P.k₀ * (2 * P.k₀ + 1 + 3 * 2 ^ (P.k₀ - 1)) ≤
        Module.finrank (Fp P) Fq * P.p)
    (pFu pTu pFu'' pTu'' : MvPolynomial (JointIdx P) Fq)
    (hdet : pFu * pTu'' - pTu * pFu'' ≠ 0)
    (hdF : pFu.totalDegree ≤ 2 ^ (P.k₀ + 6)) (hdT : pTu.totalDegree ≤ 2 ^ (P.k₀ + 6))
    (hdF' : pFu''.totalDegree ≤ 2 ^ (P.k₀ + 6)) (hdT' : pTu''.totalDegree ≤ 2 ^ (P.k₀ + 6))
    (hvanish : ∀ ch ∈ {ch : Challenges P Fq Dom | ∃ ψ : Cube P.m → Fq, ψ ≠ 0 ∧
        ∀ s, dotFunc (fun c => Algebra.trace (Fp P) Fq (ψ c * eqPoly ch.α s))
          ∈ Submodule.span (Fp P) (Set.range (confineGen P Fq Dom ch b))},
        MvPolynomial.eval (jointPoint P Fq Dom ch) (pFu * pTu'' - pTu * pFu'') = 0)
    (dataStar : DataAssign P) (hStar : Consistent P Fq S dataStar) :
    IsSimulator P Fq Dom S
      (honestTranscript P Fq Dom S dataStar) (εZK P Fq) := by
  refine masked_whir_statistical_zk_of_crossWitness2 P Fq Dom S b h2 hmf hdom hbudget
    hprime hpdvd hcop hdk hslack pFu pTu pFu'' pTu'' hdet hdF hdT hdF' hdT' ?_ dataStar hStar
  intro ch hch
  have hz := hvanish ch hch
  rw [map_sub, map_mul, map_mul] at hz
  exact exists_kernel_of_det2_eq_zero Fq _ _ _ _ hz

end ZkWhir
