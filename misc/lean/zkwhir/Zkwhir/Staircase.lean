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
import Zkwhir.ViewSolve

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

/-! ## Component decoupling for the node-system rows -/

section Decouple

variable (P : Params) [Fintype Fq] [Algebra (Fp P) Fq]
  (Dom : Finset (Fp P)) (ch : Challenges P Fq Dom)

/-- The single-point staircase family: the weight vectors of the first
out-of-domain point and of its mixed points (`lem:staircase`). -/
def stairFamily : (Unit ⊕ Fin P.k₀ × Fin 2) → Cube P.k₀ → Fq
  | Sum.inl _ => fun s => eqPoly (powSeq (ch.z 0) P.k₀) s
  | Sum.inr (ℓ, y) => fun s =>
      eqPoly (mixedPoint P Fq Dom ch ℓ (((y : ℕ) + 1 : ℕ) : Fq)
        (powSeq (ch.z 0) P.k₀)) s

/-- **Component decoupling**: independence of the full two-point row system
follows from independence of the single-point staircase family together with
non-vanishing of the first-channel prefix factors. The second component then
only needs that Lagrange vectors are nonzero. -/
theorem rowsLI_of_stairLI
    (hstair : LinearIndependent Fq (stairFamily Fq P Dom ch))
    (hpre : ∀ (ℓ : Fin P.k₀) (y : Fin 2),
      prefixFactor P Fq Dom ch ℓ (((y : ℕ) + 1 : ℕ) : Fq)
        (powSeq (ch.z 0) P.k₀) ≠ 0) :
    LinearIndependent Fq (rowWeights P Fq Dom ch) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hsum
  -- pointwise component equations
  have happ : ∀ (s : Cube P.k₀) (j' : Fin 2),
      ∑ r, g r * rowWeights P Fq Dom ch r s j' = 0 := by
    intro s j'
    have h := congrFun (congrFun hsum s) j'
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
  -- component 0 is a combination of the staircase family
  have hcomb : ∑ i, (Sum.elim (fun _ : Unit => g (Sum.inl 0))
      (fun ℓy : Fin P.k₀ × Fin 2 => g (Sum.inr ℓy) *
        prefixFactor P Fq Dom ch ℓy.1 (((ℓy.2 : ℕ) + 1 : ℕ) : Fq)
          (powSeq (ch.z 0) P.k₀)) i) • stairFamily Fq P Dom ch i = 0 := by
    funext s
    have h0 := happ s 0
    rw [Fintype.sum_sum_type] at h0 ⊢
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have hinl : ∀ j : Fin 2, g (Sum.inl j) *
        rowWeights P Fq Dom ch (Sum.inl j) s 0 =
        if j = 0 then g (Sum.inl 0) * eqPoly (powSeq (ch.z 0) P.k₀) s
        else 0 := by
      intro j
      by_cases hj : j = 0
      · subst hj
        simp [rowWeights]
      · have : (0 : Fin 2) ≠ j := fun h => hj h.symm
        simp [rowWeights, this, hj]
    have hinr : ∀ ℓy : Fin P.k₀ × Fin 2, g (Sum.inr ℓy) *
        rowWeights P Fq Dom ch (Sum.inr ℓy) s 0 =
        (g (Sum.inr ℓy) *
          prefixFactor P Fq Dom ch ℓy.1 (((ℓy.2 : ℕ) + 1 : ℕ) : Fq)
            (powSeq (ch.z 0) P.k₀)) *
          eqPoly (mixedPoint P Fq Dom ch ℓy.1 (((ℓy.2 : ℕ) + 1 : ℕ) : Fq)
            (powSeq (ch.z 0) P.k₀)) s := by
      intro ℓy
      obtain ⟨ℓ, y⟩ := ℓy
      simp [rowWeights]
      ring
    rw [Finset.sum_congr rfl fun j _ => hinl j,
      Finset.sum_congr rfl fun ℓy _ => hinr ℓy] at h0
    rw [Finset.sum_ite_eq' Finset.univ (0 : Fin 2)
      (fun _ => g (Sum.inl 0) * eqPoly (powSeq (ch.z 0) P.k₀) s),
      if_pos (Finset.mem_univ _)] at h0
    have hstair_inl : ∀ u : Unit, stairFamily Fq P Dom ch (Sum.inl u) =
        fun s => eqPoly (powSeq (ch.z 0) P.k₀) s := fun _ => rfl
    have hstair_inr : ∀ ℓy : Fin P.k₀ × Fin 2,
        stairFamily Fq P Dom ch (Sum.inr ℓy) =
        fun s => eqPoly (mixedPoint P Fq Dom ch ℓy.1
          (((ℓy.2 : ℕ) + 1 : ℕ) : Fq) (powSeq (ch.z 0) P.k₀)) s := by
      intro ℓy
      obtain ⟨ℓ, y⟩ := ℓy
      rfl
    simp only [Sum.elim_inl, Sum.elim_inr, hstair_inl, hstair_inr]
    simpa using h0
  -- the staircase kills component-0 coefficients
  have hkill := Fintype.linearIndependent_iff.mp hstair _ hcomb
  have hg0 : g (Sum.inl 0) = 0 := by
    have := hkill (Sum.inl ())
    simpa using this
  have hgr : ∀ ℓy : Fin P.k₀ × Fin 2, g (Sum.inr ℓy) = 0 := by
    intro ℓy
    have h := hkill (Sum.inr ℓy)
    simp only [Sum.elim_inr] at h
    rcases mul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h (hpre ℓy.1 ℓy.2)
  -- component 1 kills the last coefficient
  have hg1 : g (Sum.inl 1) = 0 := by
    have hvec : (fun s : Cube P.k₀ =>
        eqPoly (powSeq (ch.z 1) P.k₀) s) ≠ 0 :=
      eqPoly_vec_ne_zero Fq _
    have h1 : ∀ s, g (Sum.inl 1) * eqPoly (powSeq (ch.z 1) P.k₀) s = 0 := by
      intro s
      have h := happ s 1
      rw [Fintype.sum_sum_type] at h
      have hinl : ∀ j : Fin 2, g (Sum.inl j) *
          rowWeights P Fq Dom ch (Sum.inl j) s 1 =
          if j = 1 then g (Sum.inl 1) * eqPoly (powSeq (ch.z 1) P.k₀) s
          else 0 := by
        intro j
        by_cases hj : j = 1
        · subst hj
          simp [rowWeights]
        · have : (1 : Fin 2) ≠ j := fun h' => hj h'.symm
          simp [rowWeights, this, hj]
      rw [Finset.sum_congr rfl fun j _ => hinl j,
        Finset.sum_ite_eq' Finset.univ (1 : Fin 2)
          (fun _ => g (Sum.inl 1) * eqPoly (powSeq (ch.z 1) P.k₀) s),
        if_pos (Finset.mem_univ _)] at h
      have hzero : ∑ ℓy : Fin P.k₀ × Fin 2, g (Sum.inr ℓy) *
          rowWeights P Fq Dom ch (Sum.inr ℓy) s 1 = 0 :=
        Finset.sum_eq_zero fun ℓy _ => by rw [hgr ℓy, zero_mul]
      rw [hzero, add_zero] at h
      exact h
    by_contra hne
    apply hvec
    funext s
    have := h1 s
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hne
    · exact h
  -- conclude for every index
  intro r
  rcases r with j | ℓy
  · have : j = 0 ∨ j = 1 := by omega
    rcases this with h | h <;> rw [h]
    · exact hg0
    · exact hg1
  · exact hgr ℓy

end Decouple

end ZkWhir
