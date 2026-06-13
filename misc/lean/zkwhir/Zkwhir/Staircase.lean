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
import Zkwhir.StaircaseBridge

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

variable (P : Params) [Algebra (Fp P) Fq]
  (Dom : Finset (Fp P)) (ch : Challenges P Fq Dom)

/-- The channel weight vector of a slot/eval pair `r = (ℓ, y)` at the point
`z_j`: `prefixFactor · êq(mixed point)` — the per-block component of a
coupled node-system row (`thm:twopoint`). -/
def chanWeight (j : Fin 2) (r : Fin P.k₀ × Fin 2) : Cube P.k₀ → Fq :=
  fun s => prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
      (powSeq (ch.z j) P.k₀) *
    eqPoly (mixedPoint P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
      (powSeq (ch.z j) P.k₀)) s

/-- **`chanWeight` in the `ω/τ` staircase basis**: the per-channel expansion
that the coefficient extraction (via `staircase_indep`) consumes. The prefix
factor scales the whole mixed-point staircase decomposition. -/
theorem chanWeight_staircase (j : Fin 2) (r : Fin P.k₀ × Fin 2) :
    chanWeight Fq P Dom ch j r =
      (prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
          (powSeq (ch.z j) P.k₀)) • eqPoly (powSeq (ch.z j) P.k₀)
      + (∑ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < r.1),
          (prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
              (powSeq (ch.z j) P.k₀) * lamData P Fq Dom ch (ch.z j) i) •
            ptensor (stairVec (czData P Fq (ch.z j)) (fun _ => drow)
              (lamData P Fq Dom ch (ch.z j)) i))
      + (prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
            (powSeq (ch.z j) P.k₀) *
          ((((r.2 : ℕ) + 1 : ℕ) : Fq) - powSeq (ch.z j) P.k₀ r.1)) •
          ptensor (stairVec (czData P Fq (ch.z j)) (fun _ => drow)
            (lamData P Fq Dom ch (ch.z j)) r.1) := by
  have hcw : chanWeight Fq P Dom ch j r =
      (prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
        (powSeq (ch.z j) P.k₀)) •
        eqPoly (mixedPoint P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
          (powSeq (ch.z j) P.k₀)) := by
    funext s; simp [chanWeight, smul_eq_mul]
  rw [hcw, eqPoly_mixedPoint_decomp]
  simp only [smul_add, Finset.smul_sum, smul_smul]

/-- The per-channel `τ`-coefficient at slot `i`: `Pf·λ_i` below the channel's
slot, `Pf·(ŷ − z^{2^ℓ})` at it, zero above. -/
def chanTauW (j : Fin 2) (r : Fin P.k₀ × Fin 2) (i : Fin P.k₀) : Fq :=
  if i < r.1 then
    prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
        (powSeq (ch.z j) P.k₀) * lamData P Fq Dom ch (ch.z j) i
  else if i = r.1 then
    prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
        (powSeq (ch.z j) P.k₀) *
      ((((r.2 : ℕ) + 1 : ℕ) : Fq) - powSeq (ch.z j) P.k₀ r.1)
  else 0

/-- **`chanWeight` as a single per-slot staircase sum**: the form the
coefficient extraction (`staircase_indep`) consumes. -/
theorem chanWeight_staircase_sum (j : Fin 2) (r : Fin P.k₀ × Fin 2) :
    chanWeight Fq P Dom ch j r =
      (prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
          (powSeq (ch.z j) P.k₀)) • eqPoly (powSeq (ch.z j) P.k₀)
      + ∑ i : Fin P.k₀, chanTauW Fq P Dom ch j r i •
          ptensor (stairVec (czData P Fq (ch.z j)) (fun _ => drow)
            (lamData P Fq Dom ch (ch.z j)) i) := by
  rw [chanWeight_staircase]
  have h : (∑ i : Fin P.k₀, chanTauW Fq P Dom ch j r i •
        ptensor (stairVec (czData P Fq (ch.z j)) (fun _ => drow)
          (lamData P Fq Dom ch (ch.z j)) i)) =
      (∑ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < r.1),
          (prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
              (powSeq (ch.z j) P.k₀) * lamData P Fq Dom ch (ch.z j) i) •
            ptensor (stairVec (czData P Fq (ch.z j)) (fun _ => drow)
              (lamData P Fq Dom ch (ch.z j)) i))
      + (prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
            (powSeq (ch.z j) P.k₀) *
          ((((r.2 : ℕ) + 1 : ℕ) : Fq) - powSeq (ch.z j) P.k₀ r.1)) •
          ptensor (stairVec (czData P Fq (ch.z j)) (fun _ => drow)
            (lamData P Fq Dom ch (ch.z j)) r.1) := by
    simp only [chanTauW]
    exact sum_ite_two_collapse r.1
      (fun i => prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
        (powSeq (ch.z j) P.k₀) * lamData P Fq Dom ch (ch.z j) i)
      (prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
          (powSeq (ch.z j) P.k₀) *
        ((((r.2 : ℕ) + 1 : ℕ) : Fq) - powSeq (ch.z j) P.k₀ r.1))
      (fun i => ptensor (stairVec (czData P Fq (ch.z j)) (fun _ => drow)
        (lamData P Fq Dom ch (ch.z j)) i))
  rw [h, add_assoc]

/-- **The block combination in the `ω/τ` basis**: a μ-weighted ood vector plus
a ν-weighted channel sum regroups (via `sum_comm`) into one coefficient per
slot — the form `staircase_indep` consumes. -/
theorem block_combination (j : Fin 2) (μ : Fq) (ν : Fin P.k₀ × Fin 2 → Fq) :
    μ • eqPoly (powSeq (ch.z j) P.k₀) + ∑ r, ν r • chanWeight Fq P Dom ch j r =
      (μ + ∑ r, ν r * prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
          (powSeq (ch.z j) P.k₀)) • eqPoly (powSeq (ch.z j) P.k₀)
      + ∑ i : Fin P.k₀, (∑ r, ν r * chanTauW Fq P Dom ch j r i) •
          ptensor (stairVec (czData P Fq (ch.z j)) (fun _ => drow)
            (lamData P Fq Dom ch (ch.z j)) i) := by
  have hcw : ∀ r : Fin P.k₀ × Fin 2, ν r • chanWeight Fq P Dom ch j r =
      (ν r * prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
          (powSeq (ch.z j) P.k₀)) • eqPoly (powSeq (ch.z j) P.k₀)
      + ∑ i : Fin P.k₀, (ν r * chanTauW Fq P Dom ch j r i) •
          ptensor (stairVec (czData P Fq (ch.z j)) (fun _ => drow)
            (lamData P Fq Dom ch (ch.z j)) i) := by
    intro r
    rw [chanWeight_staircase_sum, smul_add, smul_smul, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
  rw [Finset.sum_congr rfl (fun r _ => hcw r), Finset.sum_add_distrib,
    ← Finset.sum_smul, Finset.sum_comm, ← add_assoc, ← add_smul]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_smul]

/-- **Chain equations for one block** (`lem:chain`): if a block's
μ-and-ν-weighted combination vanishes, then the ω-coefficient and every
τ-coefficient vanish — extracted by `staircase_indep`. -/
theorem block_chain_eqns (j : Fin 2) (μ : Fq) (ν : Fin P.k₀ × Fin 2 → Fq)
    (h : μ • eqPoly (powSeq (ch.z j) P.k₀) +
      ∑ r, ν r • chanWeight Fq P Dom ch j r = 0) :
    (μ + ∑ r, ν r * prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
        (powSeq (ch.z j) P.k₀)) = 0 ∧
    ∀ i, (∑ r, ν r * chanTauW Fq P Dom ch j r i) = 0 := by
  rw [block_combination] at h
  have hez : eqPoly (powSeq (ch.z j) P.k₀) = ptensor (czData P Fq (ch.z j)) := by
    rw [eqPoly_eq_ptensor]; rfl
  rw [hez] at h
  exact staircase_indep (czData P Fq (ch.z j)) (fun _ => drow)
    (lamData P Fq Dom ch (ch.z j))
    (fun i => vrow_basis (powSeq (ch.z j) P.k₀ i)) _ _ h

/-- **Chain coefficient in filter form**: the slot-`m` chain coefficient
splits into the `> m` part (carrying `λ_m`) and the `= m` diagonal part — the
chain-matrix structure (`lem:chain`) the coupled solve operates on. -/
theorem chanTauW_sum_split (j : Fin 2) (ν : Fin P.k₀ × Fin 2 → Fq)
    (m : Fin P.k₀) :
    ∑ r, ν r * chanTauW Fq P Dom ch j r m =
      lamData P Fq Dom ch (ch.z j) m *
        (∑ r ∈ Finset.univ.filter (fun r : Fin P.k₀ × Fin 2 => m < r.1),
          ν r * prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
            (powSeq (ch.z j) P.k₀))
      + ∑ r ∈ Finset.univ.filter (fun r : Fin P.k₀ × Fin 2 => r.1 = m),
          ν r * (prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
              (powSeq (ch.z j) P.k₀) *
            ((((r.2 : ℕ) + 1 : ℕ) : Fq) - powSeq (ch.z j) P.k₀ r.1)) := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun r : Fin P.k₀ × Fin 2 => m < r.1)]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r hr => ?_
    have hlt : m < r.1 := (Finset.mem_filter.mp hr).2
    rw [show chanTauW Fq P Dom ch j r m =
        prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
            (powSeq (ch.z j) P.k₀) * lamData P Fq Dom ch (ch.z j) m from by
      simp [chanTauW, hlt]]
    ring
  · have hstep : ∀ r ∈ Finset.univ.filter
        (fun r : Fin P.k₀ × Fin 2 => ¬ m < r.1),
        ν r * chanTauW Fq P Dom ch j r m =
        if r.1 = m then
          ν r * (prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
              (powSeq (ch.z j) P.k₀) *
            ((((r.2 : ℕ) + 1 : ℕ) : Fq) - powSeq (ch.z j) P.k₀ r.1))
        else 0 := by
      intro r hr
      have hnlt : ¬ m < r.1 := (Finset.mem_filter.mp hr).2
      by_cases hm : r.1 = m
      · rw [if_pos hm,
          show chanTauW Fq P Dom ch j r m =
            prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
                (powSeq (ch.z j) P.k₀) *
              ((((r.2 : ℕ) + 1 : ℕ) : Fq) - powSeq (ch.z j) P.k₀ r.1) from by
          simp [chanTauW, hm]]
      · rw [if_neg hm,
          show chanTauW Fq P Dom ch j r m = 0 from by
            simp only [chanTauW, if_neg hnlt]
            rw [if_neg (fun h => hm h.symm)], mul_zero]
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter, Finset.filter_filter]
    apply Finset.sum_congr _ (fun r _ => rfl)
    ext r
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun ⟨_, h⟩ => h
    · exact fun h => ⟨fun hlt => absurd (h ▸ hlt) (lt_irrefl m), h⟩

/-- The slot-`ℓ` mass for block `j`: the `Pf`-weighted total of the two evals
at slot `ℓ`. -/
def slotMass (j : Fin 2) (ν : Fin P.k₀ × Fin 2 → Fq) (ℓ : Fin P.k₀) : Fq :=
  ∑ y : Fin 2, ν (ℓ, y) *
    prefixFactor P Fq Dom ch ℓ (((y : ℕ) + 1 : ℕ) : Fq) (powSeq (ch.z j) P.k₀)

/-- The `> m` part of a block's chain coefficient regroups into the sum of
slot masses above `m` — the triangular structure of the chain system. -/
theorem slotMass_above (j : Fin 2) (ν : Fin P.k₀ × Fin 2 → Fq)
    (m : Fin P.k₀) :
    (∑ r ∈ Finset.univ.filter (fun r : Fin P.k₀ × Fin 2 => m < r.1),
      ν r * prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
        (powSeq (ch.z j) P.k₀)) =
      ∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin P.k₀ => m < ℓ),
        slotMass Fq P Dom ch j ν ℓ := by
  rw [sum_filter_fst (fun ℓ : Fin P.k₀ => m < ℓ)
    (fun r => ν r * prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
      (powSeq (ch.z j) P.k₀))]
  rfl

/-- The slot-`m` diagonal mass for block `j`: the `Pf·(ŷ − z^{2^m})`-weighted
total of the two evals at slot `m`. -/
def slotDiag (j : Fin 2) (ν : Fin P.k₀ × Fin 2 → Fq) (m : Fin P.k₀) : Fq :=
  ∑ y : Fin 2, ν (m, y) *
    (prefixFactor P Fq Dom ch m (((y : ℕ) + 1 : ℕ) : Fq)
        (powSeq (ch.z j) P.k₀) *
      ((((y : ℕ) + 1 : ℕ) : Fq) - powSeq (ch.z j) P.k₀ m))

/-- The `= m` (diagonal) part of a block's chain coefficient regroups into the
slot-`m` diagonal mass. -/
theorem slotDiag_eq (j : Fin 2) (ν : Fin P.k₀ × Fin 2 → Fq) (m : Fin P.k₀) :
    (∑ r ∈ Finset.univ.filter (fun r : Fin P.k₀ × Fin 2 => r.1 = m),
      ν r * (prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
          (powSeq (ch.z j) P.k₀) *
        ((((r.2 : ℕ) + 1 : ℕ) : Fq) - powSeq (ch.z j) P.k₀ r.1))) =
      slotDiag Fq P Dom ch j ν m := by
  rw [sum_filter_fst (fun ℓ : Fin P.k₀ => ℓ = m)
    (fun r => ν r * (prefixFactor P Fq Dom ch r.1 (((r.2 : ℕ) + 1 : ℕ) : Fq)
        (powSeq (ch.z j) P.k₀) *
      ((((r.2 : ℕ) + 1 : ℕ) : Fq) - powSeq (ch.z j) P.k₀ r.1))),
    Finset.filter_eq' Finset.univ m, if_pos (Finset.mem_univ m),
    Finset.sum_singleton]
  rfl

/-- **A block's chain equation in triangular slot form**: assembling the
filter-form chain coefficient, the slot-mass regroup, and the diagonal
regroup. -/
theorem block_slot_chain (j : Fin 2) (μ : Fq) (ν : Fin P.k₀ × Fin 2 → Fq)
    (h : μ • eqPoly (powSeq (ch.z j) P.k₀) +
      ∑ r, ν r • chanWeight Fq P Dom ch j r = 0) (m : Fin P.k₀) :
    lamData P Fq Dom ch (ch.z j) m *
        (∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin P.k₀ => m < ℓ),
          slotMass Fq P Dom ch j ν ℓ)
      + slotDiag Fq P Dom ch j ν m = 0 := by
  have hc := (block_chain_eqns Fq P Dom ch j μ ν h).2 m
  rw [chanTauW_sum_split, slotMass_above, slotDiag_eq] at hc
  exact hc

/-- **The coupled-chains kernel condition** (`lem:coupled`, consumable form).
A weight family `ν` over the `k₀ × {1,2}` slot/eval pairs that is killed on
*both* blocks — each combined with that block's out-of-domain vector — must
vanish.

This is the genuine two-point hypothesis. Per `rem:identities` the
single-point projection of the rows spans only `k₀ + 1` of the `2k₀ + 1`
needed dimensions, so no single component can be independent on its own: the
coupling through `γ` (the diagonal differences of `lem:coupled`) is what
makes the full `2k₀ + 2` rows independent. -/
def CoupledKer : Prop :=
  ∀ ν : Fin P.k₀ × Fin 2 → Fq,
    (∃ μ₁ : Fq, μ₁ • (fun s => eqPoly (powSeq (ch.z 0) P.k₀) s) +
      ∑ r, ν r • chanWeight Fq P Dom ch 0 r = 0) →
    (∃ μ₂ : Fq, μ₂ • (fun s => eqPoly (powSeq (ch.z 1) P.k₀) s) +
      ∑ r, (ch.γ * ν r) • chanWeight Fq P Dom ch 1 r = 0) →
    ν = 0

/-- **Row independence from the coupled-chains kernel** (`thm:twopoint`,
consumable form): the `2k₀ + 2` node-system rows are linearly independent as
soon as the coupled-chains kernel condition holds. This is the sound
formulation that `coupled_blocks` provides — the two components are *not*
independent separately (`rem:identities`); the `γ`-coupling is essential. -/
theorem rowsLI_of_coupledKer (hker : CoupledKer Fq P Dom ch) :
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
  -- block 0 equation
  have hb0 : (g (Sum.inl 0)) • (fun s => eqPoly (powSeq (ch.z 0) P.k₀) s) +
      ∑ r, (g (Sum.inr r)) • chanWeight Fq P Dom ch 0 r = 0 := by
    funext s
    have h0 := happ s 0
    rw [Fintype.sum_sum_type] at h0
    have hinl : ∀ j : Fin 2, g (Sum.inl j) *
        rowWeights P Fq Dom ch (Sum.inl j) s 0 =
        if j = 0 then g (Sum.inl 0) * eqPoly (powSeq (ch.z 0) P.k₀) s
        else 0 := by
      intro j
      by_cases hj : j = 0
      · subst hj; simp [rowWeights]
      · have : (0 : Fin 2) ≠ j := fun h => hj h.symm
        simp [rowWeights, this, hj]
    have hinr : ∀ r : Fin P.k₀ × Fin 2, g (Sum.inr r) *
        rowWeights P Fq Dom ch (Sum.inr r) s 0 =
        g (Sum.inr r) * chanWeight Fq P Dom ch 0 r s := by
      intro r; obtain ⟨ℓ, y⟩ := r; simp [rowWeights, chanWeight]
    rw [Finset.sum_congr rfl fun j _ => hinl j,
      Finset.sum_congr rfl fun r _ => hinr r,
      Finset.sum_ite_eq' Finset.univ (0 : Fin 2)
        (fun _ => g (Sum.inl 0) * eqPoly (powSeq (ch.z 0) P.k₀) s),
      if_pos (Finset.mem_univ _)] at h0
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      Pi.zero_apply]
    exact h0
  -- block 1 equation
  have hb1 : (g (Sum.inl 1)) • (fun s => eqPoly (powSeq (ch.z 1) P.k₀) s) +
      ∑ r, (ch.γ * g (Sum.inr r)) • chanWeight Fq P Dom ch 1 r = 0 := by
    funext s
    have h1 := happ s 1
    rw [Fintype.sum_sum_type] at h1
    have hinl : ∀ j : Fin 2, g (Sum.inl j) *
        rowWeights P Fq Dom ch (Sum.inl j) s 1 =
        if j = 1 then g (Sum.inl 1) * eqPoly (powSeq (ch.z 1) P.k₀) s
        else 0 := by
      intro j
      by_cases hj : j = 1
      · subst hj; simp [rowWeights]
      · have : (1 : Fin 2) ≠ j := fun h => hj h.symm
        simp [rowWeights, this, hj]
    have hinr : ∀ r : Fin P.k₀ × Fin 2, g (Sum.inr r) *
        rowWeights P Fq Dom ch (Sum.inr r) s 1 =
        (ch.γ * g (Sum.inr r)) * chanWeight Fq P Dom ch 1 r s := by
      intro r; obtain ⟨ℓ, y⟩ := r; simp [rowWeights, chanWeight]; ring
    rw [Finset.sum_congr rfl fun j _ => hinl j,
      Finset.sum_congr rfl fun r _ => hinr r,
      Finset.sum_ite_eq' Finset.univ (1 : Fin 2)
        (fun _ => g (Sum.inl 1) * eqPoly (powSeq (ch.z 1) P.k₀) s),
      if_pos (Finset.mem_univ _)] at h1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
      Pi.zero_apply]
    exact h1
  -- the kernel condition kills the slot coefficients
  have hν : (fun r => g (Sum.inr r)) = 0 :=
    hker _ ⟨g (Sum.inl 0), hb0⟩ ⟨g (Sum.inl 1), hb1⟩
  have hgr : ∀ r, g (Sum.inr r) = 0 := fun r => congrFun hν r
  -- each out-of-domain coefficient then vanishes
  have hg0 : g (Sum.inl 0) = 0 := by
    have hz : g (Sum.inl 0) • (fun s => eqPoly (powSeq (ch.z 0) P.k₀) s) =
        (0 : Cube P.k₀ → Fq) := by
      have hsum0 : (∑ r, (g (Sum.inr r)) • chanWeight Fq P Dom ch 0 r) = 0 :=
        Finset.sum_eq_zero fun r _ => by rw [hgr r, zero_smul]
      rw [hsum0, add_zero] at hb0
      exact hb0
    rcases smul_eq_zero.mp hz with h | h
    · exact h
    · exact absurd h (eqPoly_vec_ne_zero Fq _)
  have hg1 : g (Sum.inl 1) = 0 := by
    have hz : g (Sum.inl 1) • (fun s => eqPoly (powSeq (ch.z 1) P.k₀) s) =
        (0 : Cube P.k₀ → Fq) := by
      have hsum1 : (∑ r, (ch.γ * g (Sum.inr r)) •
          chanWeight Fq P Dom ch 1 r) = 0 :=
        Finset.sum_eq_zero fun r _ => by rw [hgr r, mul_zero, zero_smul]
      rw [hsum1, add_zero] at hb1
      exact hb1
    rcases smul_eq_zero.mp hz with h | h
    · exact h
    · exact absurd h (eqPoly_vec_ne_zero Fq _)
  -- conclude for every index
  intro r
  rcases r with j | r
  · have : j = 0 ∨ j = 1 := by omega
    rcases this with h | h <;> rw [h]
    · exact hg0
    · exact hg1
  · exact hgr r

end Decouple

end ZkWhir
