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

/-- The coupling function `g(x) = (1 − 2x²)/(2x − 1)` of `lem:coupled` /
`cond:cross2` (the chain-pencil ratio `B^{(j)}_ℓ / C^{(j)}_ℓ`). -/
def gFun (x : Fq) : Fq := (1 - 2 * x ^ 2) / (2 * x - 1)

/-- **Closed form `1 + g(x) = 2x(1−x)/(2x−1)`** (the factor in `cond:cross2`'s
nonvanishing minor, tex:535): nonzero precisely when `x ∉ {0, 1}`. -/
theorem one_add_gFun (x : Fq) (hx : 2 * x - 1 ≠ 0) :
    1 + gFun Fq x = 2 * x * (1 - x) / (2 * x - 1) := by
  rw [gFun]; field_simp; ring

/-- The `cond:cross2` minor factor `1 + g(x)` is nonzero when `x ∉ {0, 1}` (and
`2x ≠ 1`, `2 ≠ 0`). -/
theorem one_add_gFun_ne_zero (h2 : (2 : Fq) ≠ 0) (x : Fq) (hx : 2 * x - 1 ≠ 0)
    (hx0 : x ≠ 0) (hx1 : x ≠ 1) : 1 + gFun Fq x ≠ 0 := by
  rw [one_add_gFun Fq x hx]
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero h2 hx0) (sub_ne_zero.mpr (Ne.symm hx1))) hx

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

/-- Peeling the first coordinate of a Lagrange weight: `êq` at a `cons`-point and
a `cons`-vertex factors (the `Fin.cons`/`Equiv.piFinSucc` analog of `eqPoly_snoc`,
for the multivariate Schwartz–Zippel induction). -/
theorem eqPoly_cons {R : Type*} [CommRing R] {j : ℕ} (t : R) (p : Fin j → R)
    (b : Bool) (s : Cube j) :
    eqPoly (Fin.cons t p) (Fin.cons b s) =
      (if b then t else 1 - t) * eqPoly p s := by
  unfold eqPoly
  rw [Fin.prod_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- Splitting a sum over `Cube (j+1)` by the first coordinate (the cube analog of
`Fin.sum_univ_succ`, for the Schwartz–Zippel induction). -/
theorem sum_cube_succ {M : Type*} [AddCommMonoid M] {j : ℕ} (g : Cube (j + 1) → M) :
    ∑ b : Cube (j + 1), g b =
      ∑ b0 : Bool, ∑ brest : Cube j, g (Fin.cons b0 brest) := by
  rw [← (Fin.consEquiv (fun _ : Fin (j + 1) => Bool)).sum_comp g, Fintype.sum_prod_type]
  rfl

/-- **`mle` is affine in the first coordinate** (Schwartz–Zippel induction core):
`mle T (cons t x) = (1−t)·mle T₀ x + t·mle T₁ x`, where `T₀ = T(cons false ·)` and
`T₁ = T(cons true ·)` are the two half-tables. -/
theorem mle_cons {R : Type*} [CommRing R] {j : ℕ} (T : Cube (j + 1) → R) (t : R)
    (x : Fin j → R) :
    mle T (Fin.cons t x) =
      (1 - t) * mle (fun b => T (Fin.cons false b)) x +
        t * mle (fun b => T (Fin.cons true b)) x := by
  unfold mle
  rw [sum_cube_succ (fun b => eqPoly (Fin.cons t x) b * T b), Fintype.sum_bool, add_comm]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun brest _ => ?_
    rw [eqPoly_cons]; simp only [Bool.false_eq_true, if_false]; ring
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun brest _ => ?_
    rw [eqPoly_cons]; simp only [if_true]; ring

/-- `mle` is additive in the table: `mle (T − T') = mle T − mle T'` (the slope of
the `mle_cons` decomposition is `mle (T₁ − T₀)`; needed for the SZ induction). -/
theorem mle_sub {R : Type*} [CommRing R] {j : ℕ} (T T' : Cube j → R) (x : Fin j → R) :
    mle (fun b => T b - T' b) x = mle T x - mle T' x := by
  unfold mle
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- `mle` of the zero table is `0` (the degenerate case of the SZ induction). -/
theorem mle_zero {R : Type*} [CommRing R] {j : ℕ} (x : Fin j → R) :
    mle (0 : Cube j → R) x = 0 := by
  unfold mle
  exact Finset.sum_eq_zero fun b _ => by simp

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

/-- The slot mass expanded over the two evals. -/
theorem slotMass_expand (j : Fin 2) (ν : Fin P.k₀ × Fin 2 → Fq)
    (ℓ : Fin P.k₀) :
    slotMass Fq P Dom ch j ν ℓ =
      ν (ℓ, 0) * prefixFactor P Fq Dom ch ℓ 1 (powSeq (ch.z j) P.k₀)
    + ν (ℓ, 1) * prefixFactor P Fq Dom ch ℓ 2 (powSeq (ch.z j) P.k₀) := by
  unfold slotMass
  rw [Fin.sum_univ_two]
  norm_num

/-- The slot diagonal expanded over the two evals. -/
theorem slotDiag_expand (j : Fin 2) (ν : Fin P.k₀ × Fin 2 → Fq)
    (m : Fin P.k₀) :
    slotDiag Fq P Dom ch j ν m =
      ν (m, 0) * (prefixFactor P Fq Dom ch m 1 (powSeq (ch.z j) P.k₀) *
          (1 - powSeq (ch.z j) P.k₀ m))
    + ν (m, 1) * (prefixFactor P Fq Dom ch m 2 (powSeq (ch.z j) P.k₀) *
          (2 - powSeq (ch.z j) P.k₀ m)) := by
  unfold slotDiag
  rw [Fin.sum_univ_two]
  norm_num

/-- Slot mass is linear in `ν`. -/
theorem slotMass_smul (j : Fin 2) (c : Fq) (ν : Fin P.k₀ × Fin 2 → Fq)
    (ℓ : Fin P.k₀) :
    slotMass Fq P Dom ch j (fun r => c * ν r) ℓ =
      c * slotMass Fq P Dom ch j ν ℓ := by
  unfold slotMass
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- Slot diagonal is linear in `ν`. -/
theorem slotDiag_smul (j : Fin 2) (c : Fq) (ν : Fin P.k₀ × Fin 2 → Fq)
    (m : Fin P.k₀) :
    slotDiag Fq P Dom ch j (fun r => c * ν r) m =
      c * slotDiag Fq P Dom ch j ν m := by
  unfold slotDiag
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

/-- The per-slot 2×2 coupling determinant: the obstruction whose nonvanishing
makes the two blocks pin the slot's two evals to zero. -/
def slotDet (m : Fin P.k₀) : Fq :=
  (prefixFactor P Fq Dom ch m 1 (powSeq (ch.z 0) P.k₀) *
      (1 - powSeq (ch.z 0) P.k₀ m)) *
    (prefixFactor P Fq Dom ch m 2 (powSeq (ch.z 1) P.k₀) *
      (2 - powSeq (ch.z 1) P.k₀ m)) -
  (prefixFactor P Fq Dom ch m 1 (powSeq (ch.z 1) P.k₀) *
      (1 - powSeq (ch.z 1) P.k₀ m)) *
    (prefixFactor P Fq Dom ch m 2 (powSeq (ch.z 0) P.k₀) *
      (2 - powSeq (ch.z 0) P.k₀ m))

/-- The `z`-only part of the coupling determinant (the `α`-prefix divided
out): a polynomial in `z_0, z_1` alone. -/
def zdet (m : Fin P.k₀) : Fq :=
  eqf Fq 1 (powSeq (ch.z 0) P.k₀ m) * (1 - powSeq (ch.z 0) P.k₀ m) *
      (eqf Fq 2 (powSeq (ch.z 1) P.k₀ m) * (2 - powSeq (ch.z 1) P.k₀ m)) -
  eqf Fq 1 (powSeq (ch.z 1) P.k₀ m) * (1 - powSeq (ch.z 1) P.k₀ m) *
      (eqf Fq 2 (powSeq (ch.z 0) P.k₀ m) * (2 - powSeq (ch.z 0) P.k₀ m))

/-- **The `slotDet` factorization**: `slotDet_m = (α-prefix at z₀)·(α-prefix
at z₁)·zdet_m` — separating the prefix vanishing from the `z`-coupling. -/
theorem slotDet_factor [Nonempty {x // x ∈ Dom}] (m : Fin P.k₀) :
    slotDet Fq P Dom ch m =
      (∏ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < m),
          eqf Fq (ch.α i) (powSeq (ch.z 0) P.k₀ i)) *
      (∏ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < m),
          eqf Fq (ch.α i) (powSeq (ch.z 1) P.k₀ i)) *
      zdet Fq P Dom ch m := by
  unfold slotDet zdet
  rw [prefixFactor_eq, prefixFactor_eq, prefixFactor_eq, prefixFactor_eq]
  ring

/-- The `zdet` as a polynomial in `z₁` (with `a = z₀^{2^m}` a parameter and
`e = 2^m`): its roots are the `zdet`-vanishing values of `z₁`. -/
def zdetPoly (a : Fq) (e : ℕ) : Polynomial Fq :=
  Polynomial.C (a * (1 - a)) *
      ((3 * Polynomial.X ^ e - 1) * (2 - Polynomial.X ^ e)) -
    Polynomial.C ((3 * a - 1) * (2 - a)) *
      (Polynomial.X ^ e * (1 - Polynomial.X ^ e))

/-- `zdet_m` is the evaluation of `zdetPoly` at `z₁`. -/
theorem zdet_eq_eval (m : Fin P.k₀) :
    zdet Fq P Dom ch m =
      Polynomial.eval (ch.z 1)
        (zdetPoly Fq (powSeq (ch.z 0) P.k₀ m) (2 ^ (m : ℕ))) := by
  unfold zdet zdetPoly
  simp only [eqf_one, eqf_two, Polynomial.eval_sub, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one, powSeq]
  ring

/-- The constant coefficient of `zdetPoly` is `−2a(1−a)`. -/
theorem zdetPoly_coeff_zero (a : Fq) (e : ℕ) (he : 0 < e) :
    (zdetPoly Fq a e).coeff 0 = -(2 * (a * (1 - a))) := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  unfold zdetPoly
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_ofNat, Polynomial.eval_one, zero_pow he.ne']
  ring

/-- `zdetPoly` is nonzero when `a ∉ {0, 1}` (char ≠ 2): its constant
coefficient is nonzero. -/
theorem zdetPoly_ne_zero (h2 : (2 : Fq) ≠ 0) (a : Fq) (e : ℕ) (he : 0 < e)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1) : zdetPoly Fq a e ≠ 0 := by
  intro h
  have hc := zdetPoly_coeff_zero Fq a e he
  rw [h, Polynomial.coeff_zero] at hc
  have : (2 : Fq) * (a * (1 - a)) = 0 := by linear_combination hc
  rcases mul_eq_zero.mp this with h' | h'
  · exact h2 h'
  · rcases mul_eq_zero.mp h' with h'' | h''
    · exact ha0 h''
    · exact ha1 (sub_eq_zero.mp h'').symm

/-- `zdetPoly` has degree at most `2e`: each summand is a constant times a
product of two factors of degree at most `e`. -/
theorem zdetPoly_natDegree (a : Fq) (e : ℕ) :
    (zdetPoly Fq a e).natDegree ≤ 2 * e := by
  have hXe : (Polynomial.X ^ e : Polynomial Fq).natDegree ≤ e := by
    simp [Polynomial.natDegree_X_pow]
  have hsub : ∀ p q : Polynomial Fq, p.natDegree ≤ e → q.natDegree ≤ e →
      (p - q).natDegree ≤ e := fun p q hp hq =>
    (Polynomial.natDegree_sub_le _ _).trans (max_le hp hq)
  have hf1 : (3 * Polynomial.X ^ e - 1 : Polynomial Fq).natDegree ≤ e :=
    hsub _ _ ((Polynomial.natDegree_mul_le).trans (by simpa using hXe))
      (by simp)
  have hf2 : (2 - Polynomial.X ^ e : Polynomial Fq).natDegree ≤ e :=
    hsub _ _ (by simp) hXe
  have hf4 : (1 - Polynomial.X ^ e : Polynomial Fq).natDegree ≤ e :=
    hsub _ _ (by simp) hXe
  unfold zdetPoly
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    exact (Polynomial.natDegree_mul_le).trans
      (by rw [two_mul]; exact add_le_add hf1 hf2)
  · refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
    exact (Polynomial.natDegree_mul_le).trans
      (by rw [two_mul]; exact add_le_add hXe hf4)

/-- **Per-slot solve**: both blocks' diagonals vanishing at slot `m`, with the
coupling determinant nonzero, pins the slot's two evals to zero. -/
theorem slot_solve (ν : Fin P.k₀ × Fin 2 → Fq) (m : Fin P.k₀)
    (hdet : slotDet Fq P Dom ch m ≠ 0)
    (h0 : slotDiag Fq P Dom ch 0 ν m = 0)
    (h1 : slotDiag Fq P Dom ch 1 ν m = 0) :
    ν (m, 0) = 0 ∧ ν (m, 1) = 0 := by
  rw [slotDiag_expand] at h0 h1
  exact two_by_two_zero hdet h0 h1

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

/-- **Coupled-chains genericity** (the Good-set conditions for `lem:coupled`):
the batching scalar is nonzero and every per-slot coupling determinant is
nonzero. -/
def CoupledGen : Prop :=
  ch.γ ≠ 0 ∧ ∀ m : Fin P.k₀, slotDet Fq P Dom ch m ≠ 0

/-- **The coupled-chains kernel triviality** (`thm:twopoint` / `lem:coupled`):
under the genericity conditions, the coupled-chains kernel is trivial. This is
the two-point full-rank theorem in `CoupledKer` form. -/
theorem coupledKer_of_gen (hgen : CoupledGen Fq P Dom ch) :
    CoupledKer Fq P Dom ch := by
  obtain ⟨hγ, hdet⟩ := hgen
  rintro ν ⟨μ₁, hblock0⟩ ⟨μ₂, hblock1⟩
  -- block 0 chain equations in triangular slot form
  have hbsc0 : ∀ m, lamData P Fq Dom ch (ch.z 0) m *
        (∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin P.k₀ => m < ℓ),
          slotMass Fq P Dom ch 0 ν ℓ) + slotDiag Fq P Dom ch 0 ν m = 0 :=
    block_slot_chain Fq P Dom ch 0 μ₁ ν hblock0
  -- block 1: divide out the nonzero batching scalar `γ`
  have hbsc1 : ∀ m, lamData P Fq Dom ch (ch.z 1) m *
        (∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin P.k₀ => m < ℓ),
          slotMass Fq P Dom ch 1 ν ℓ) + slotDiag Fq P Dom ch 1 ν m = 0 := by
    intro m
    have h := block_slot_chain Fq P Dom ch 1 μ₂ (fun r => ch.γ * ν r) hblock1 m
    have hsm : (∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin P.k₀ => m < ℓ),
        slotMass Fq P Dom ch 1 (fun r => ch.γ * ν r) ℓ) =
        ch.γ * ∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin P.k₀ => m < ℓ),
          slotMass Fq P Dom ch 1 ν ℓ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun ℓ _ => slotMass_smul Fq P Dom ch 1 ch.γ ν ℓ
    rw [hsm, slotDiag_smul] at h
    have hfactor : ch.γ * (lamData P Fq Dom ch (ch.z 1) m *
        (∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin P.k₀ => m < ℓ),
          slotMass Fq P Dom ch 1 ν ℓ) + slotDiag Fq P Dom ch 1 ν m) = 0 := by
      linear_combination h
    exact (mul_eq_zero.mp hfactor).resolve_left hγ
  -- descending step: vanishing above `m` forces vanishing at `m`
  have step : ∀ m : Fin P.k₀,
      (∀ ℓ : Fin P.k₀, m < ℓ → ν (ℓ, 0) = 0 ∧ ν (ℓ, 1) = 0) →
      ν (m, 0) = 0 ∧ ν (m, 1) = 0 := by
    intro m hIH
    have hs0 : (∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin P.k₀ => m < ℓ),
        slotMass Fq P Dom ch 0 ν ℓ) = 0 :=
      Finset.sum_eq_zero fun ℓ hℓ => by
        rw [slotMass_expand, (hIH ℓ (Finset.mem_filter.mp hℓ).2).1,
          (hIH ℓ (Finset.mem_filter.mp hℓ).2).2]; ring
    have hs1 : (∑ ℓ ∈ Finset.univ.filter (fun ℓ : Fin P.k₀ => m < ℓ),
        slotMass Fq P Dom ch 1 ν ℓ) = 0 :=
      Finset.sum_eq_zero fun ℓ hℓ => by
        rw [slotMass_expand, (hIH ℓ (Finset.mem_filter.mp hℓ).2).1,
          (hIH ℓ (Finset.mem_filter.mp hℓ).2).2]; ring
    have hd0 : slotDiag Fq P Dom ch 0 ν m = 0 := by
      have := hbsc0 m; rw [hs0, mul_zero, zero_add] at this; exact this
    have hd1 : slotDiag Fq P Dom ch 1 ν m = 0 := by
      have := hbsc1 m; rw [hs1, mul_zero, zero_add] at this; exact this
    exact slot_solve Fq P Dom ch ν m (hdet m) hd0 hd1
  -- descending strong induction via the Nat measure `k₀ - 1 - m`
  have key : ∀ d : ℕ, ∀ m : Fin P.k₀, P.k₀ - 1 - (m : ℕ) ≤ d →
      ν (m, 0) = 0 ∧ ν (m, 1) = 0 := by
    intro d
    induction d with
    | zero =>
      intro m hm
      refine step m fun ℓ hℓ => ?_
      exfalso
      have hℓlt := ℓ.isLt
      rw [Fin.lt_def] at hℓ
      omega
    | succ d ih =>
      intro m _
      refine step m fun ℓ hℓ => ?_
      refine ih ℓ ?_
      rw [Fin.lt_def] at hℓ
      have hℓlt := ℓ.isLt
      omega
  funext r
  obtain ⟨ℓ, y⟩ := r
  have hk := key P.k₀ ℓ (by have := ℓ.isLt; omega)
  fin_cases y
  · exact hk.1
  · exact hk.2

end Decouple

/-! ## The coupled-genericity failure bound (ε₂, step e skeleton) -/

section CoupledProb

open scoped ENNReal

variable (P : Params) [Algebra (Fp P) Fq] (Dom : Finset (Fp P))
  [Nonempty {x // x ∈ Dom}]

/-- **The coupled-genericity failure bound** (`cor:twopointprob`, assembly):
`P[¬CoupledGen]` is bounded by the `γ = 0` probability plus the sum of the
per-slot determinant-vanishing probabilities. This isolates the remaining
Schwartz–Zippel work to the per-slot and `γ` events. -/
theorem coupledGen_failure_le (d : ℕ)
    (hγ : (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ch.γ = 0} ≤ 1 / (fieldCard Fq : ℝ≥0∞))
    (hslot : ∀ m : Fin P.k₀, (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | slotDet Fq P Dom ch m = 0} ≤
        (d : ℝ≥0∞) / (fieldCard Fq : ℝ≥0∞)) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ¬ CoupledGen Fq P Dom ch} ≤
      1 / (fieldCard Fq : ℝ≥0∞) +
        (P.k₀ : ℝ≥0∞) * d / (fieldCard Fq : ℝ≥0∞) := by
  classical
  have hsub : {ch : Challenges P Fq Dom | ¬ CoupledGen Fq P Dom ch} ⊆
      {ch : Challenges P Fq Dom | ch.γ = 0} ∪
        ⋃ m ∈ (Finset.univ : Finset (Fin P.k₀)),
          {ch : Challenges P Fq Dom | slotDet Fq P Dom ch m = 0} := by
    intro ch hch
    simp only [CoupledGen, Set.mem_setOf_eq, not_and_or, not_forall,
      not_not] at hch
    rcases hch with hγ0 | ⟨m, hm⟩
    · exact Or.inl hγ0
    · exact Or.inr (Set.mem_biUnion (Finset.mem_univ m) hm)
  refine (MeasureTheory.measure_mono hsub).trans ?_
  refine (MeasureTheory.measure_union_le _ _).trans (add_le_add hγ ?_)
  refine (MeasureTheory.measure_biUnion_finset_le _ _).trans ?_
  calc ∑ m : Fin P.k₀, (challengePMF P Fq Dom).toOuterMeasure
        {ch : Challenges P Fq Dom | slotDet Fq P Dom ch m = 0}
      ≤ ∑ _m : Fin P.k₀, (d : ℝ≥0∞) / (fieldCard Fq : ℝ≥0∞) :=
        Finset.sum_le_sum fun m _ => hslot m
    _ = (P.k₀ : ℝ≥0∞) * ((d : ℝ≥0∞) / (fieldCard Fq : ℝ≥0∞)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (P.k₀ : ℝ≥0∞) * d / (fieldCard Fq : ℝ≥0∞) := by rw [mul_div_assoc]

end CoupledProb

/-! ## Threading the coupled-chains core into the absorption bounds (ε₂ e3) -/

section ThreadCoupled

open scoped ENNReal

variable (P : Params) [Algebra (Fp P) Fq] (Dom : Finset (Fp P))
  [Nonempty {x // x ∈ Dom}] (S : Stmt P Fq) [FiniteDimensional (Fp P) Fq]

/-- **ε₂ rewired through the coupled-chains core**: `GoodSetAbsorption` from
the three probability bounds, with the ε₂ obligation stated as the concrete
`P[¬CoupledGen]` rather than the abstract `P[¬ LinearIndependent rowWeights]`
— since `coupledKer_of_gen ∘ rowsLI_of_coupledKer` proves
`CoupledGen → LinearIndependent rowWeights`. -/
theorem goodSetAbsorption_of_coupledBounds
    (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S) (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (ε₁ ε₂ ε₃ : ℝ≥0∞)
    (hA : (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ¬ NodeHyp P Fq Dom ch} ≤ ε₁)
    (hB : (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ¬ CoupledGen Fq P Dom ch} ≤ ε₂)
    (hC : (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ¬ Pinning P Fq Dom S ch} ≤ ε₃)
    (hsum : ε₁ + ε₂ + ε₃ ≤ εZK P Fq) :
    GoodSetAbsorption P Fq Dom S := by
  refine goodSetAbsorption_of_bounds P Fq Dom S h2 hmf hdom hbudget ε₁ ε₂ ε₃
    hA ?_ hC hsum
  refine le_trans (MeasureTheory.measure_mono ?_) hB
  intro ch hch
  simp only [Set.mem_setOf_eq] at hch ⊢
  intro hcg
  exact hch (rowsLI_of_coupledKer Fq P Dom ch (coupledKer_of_gen Fq P Dom ch hcg))

end ThreadCoupled

end ZkWhir
