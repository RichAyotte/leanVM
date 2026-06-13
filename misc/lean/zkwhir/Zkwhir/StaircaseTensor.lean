/-
`lem:staircase` of `zk_leanVM.tex`, abstract tensor form: for per-slot bases
`{c_i, d_i}` of `F²` and scalars `λ_i`, with `a_i := c_i + λ_i d_i`, the
`k + 1` pure tensors

  ω    := c_1 ⊗ ⋯ ⊗ c_k
  τ_m  := a_1 ⊗ ⋯ ⊗ a_{m-1} ⊗ d_m ⊗ c_{m+1} ⊗ ⋯ ⊗ c_k     (1 ≤ m ≤ k)

are linearly independent. Tensors are modelled in `Cube k → F` (the
multilinear-extension space): a pure tensor of per-slot vectors
`w : Fin k → Bool → F` is `s ↦ ∏ i, w i (s i)`.

This is the keystone of the coupled-chains kernel (`thm:twopoint` /
`CoupledKer`). Unconditional — it holds for all values of the variables.

Part of the `GoodSetAbsorption` formalization campaign; unwired until green.
-/
import Mathlib

set_option linter.style.header false

noncomputable section

namespace ZkWhir

variable {F : Type*} [Field F]

/-- A pure tensor of per-slot `F²`-vectors, in the `Cube k → F` model. -/
def ptensor {k : ℕ} (w : Fin k → Bool → F) : (Fin k → Bool) → F :=
  fun s => ∏ i, w i (s i)

/-- Peeling the top slot of a pure tensor. -/
theorem ptensor_snoc {k : ℕ} (w : Fin (k + 1) → Bool → F)
    (s : Fin k → Bool) (b : Bool) :
    ptensor w (Fin.snoc s b) =
      ptensor (fun i => w i.castSucc) s * w (Fin.last k) b := by
  unfold ptensor
  rw [Fin.prod_univ_castSucc]
  congr 1
  · exact Finset.prod_congr rfl fun i _ => by rw [Fin.snoc_castSucc]
  · rw [Fin.snoc_last]

/-- A pure tensor of nonzero per-slot vectors is nonzero. -/
theorem ptensor_ne_zero {k : ℕ} (w : Fin k → Bool → F)
    (hw : ∀ i, w i ≠ 0) : ptensor w ≠ 0 := by
  intro h
  -- choose, per slot, a bit where `w i` is nonzero
  have hbit : ∀ i, ∃ b, w i b ≠ 0 := by
    intro i
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hw i (funext fun b => hcon b)
  choose s hs using hbit
  have : ptensor w s = 0 := by rw [h]; rfl
  rw [ptensor] at this
  exact (Finset.prod_ne_zero_iff.mpr fun i _ => hs i) this

/-- The staircase per-slot data for `τ_m`: slots `< m` carry `a_i`, slot `m`
carries `d_m`, slots `> m` carry `c_i`. -/
def stairVec {k : ℕ} (c d : Fin k → Bool → F) (lam : Fin k → F) (m : Fin k) :
    Fin k → Bool → F :=
  fun i => if i < m then (fun b => c i b + lam i * d i b)
           else if i = m then d i else c i

/-- Collapse a two-branch indicator sum to a filtered sum plus the diagonal
term: `∑_i (if i<ℓ then A i else if i=ℓ then B else 0)·v_i = ∑_{i<ℓ} A_i v_i +
B·v_ℓ`. The regroup primitive for writing a channel's staircase contribution
as a single per-slot sum. -/
theorem sum_ite_two_collapse {k : ℕ} {M : Type*} [AddCommMonoid M] [Module F M]
    (ℓ : Fin k) (A : Fin k → F) (B : F) (v : Fin k → M) :
    ∑ i, (if i < ℓ then A i else if i = ℓ then B else 0) • v i =
      (∑ i ∈ Finset.univ.filter (fun i => i < ℓ), A i • v i) + B • v ℓ := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i < ℓ)
    (fun i => (if i < ℓ then A i else if i = ℓ then B else 0) • v i)]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_pos (Finset.mem_filter.mp hi).2]
  · rw [Finset.sum_eq_single ℓ
      (fun i hi hiℓ => by
        rw [if_neg (Finset.mem_filter.mp hi).2, if_neg hiℓ, zero_smul])
      (fun hℓ => absurd
        (Finset.mem_filter.mpr ⟨Finset.mem_univ ℓ, lt_irrefl ℓ⟩) hℓ)]
    rw [if_neg (lt_irrefl ℓ), if_pos rfl]

/-- Sum a first-component–filtered sum over a product, fiber by fiber:
`∑_{(a,b): P a} f(a,b) = ∑_{a: P a} ∑_b f(a,b)`. The regroup-by-slot
primitive for the coupled-chains triangular system. -/
theorem sum_filter_fst {α β M : Type*} [Fintype α] [Fintype β] [DecidableEq α]
    [AddCommMonoid M] (P : α → Prop) [DecidablePred P] (f : α × β → M) :
    ∑ r ∈ Finset.univ.filter (fun r : α × β => P r.1), f r =
      ∑ a ∈ Finset.univ.filter P, ∑ b : β, f (a, b) := by
  rw [show Finset.univ.filter (fun r : α × β => P r.1) =
      (Finset.univ.filter P) ×ˢ Finset.univ from by
    ext r
    simp [Finset.mem_filter, Finset.mem_product]]
  rw [Finset.sum_product]

/-- **2×2 nonsingular kernel**: a homogeneous 2×2 system with nonzero
determinant has only the zero solution. The per-slot Vandermonde solve of the
coupled chains. -/
theorem two_by_two_zero {a b A0 B0 A1 B1 : F} (hdet : A0 * B1 - A1 * B0 ≠ 0)
    (h0 : a * A0 + b * B0 = 0) (h1 : a * A1 + b * B1 = 0) : a = 0 ∧ b = 0 := by
  refine ⟨?_, ?_⟩
  · have key : a * (A0 * B1 - A1 * B0) = 0 := by
      linear_combination B1 * h0 - B0 * h1
    exact (mul_eq_zero.mp key).resolve_right hdet
  · have key : b * (A0 * B1 - A1 * B0) = 0 := by
      linear_combination A0 * h1 - A1 * h0
    exact (mul_eq_zero.mp key).resolve_right hdet

/-- The all-`a` data `ρ_k = a_1 ⊗ ⋯ ⊗ a_k`. -/
def aVec {k : ℕ} (c d : Fin k → Bool → F) (lam : Fin k → F) : Fin k → Bool → F :=
  fun i b => c i b + lam i * d i b

/-- A basis pair gives a nonzero `a_i`. -/
theorem aVec_ne_zero {k : ℕ} (c d : Fin k → Bool → F) (lam : Fin k → F)
    (hbasis : ∀ (i : Fin k) (x y : F),
      (∀ b, x * c i b + y * d i b = 0) → x = 0 ∧ y = 0) (i : Fin k) :
    aVec c d lam i ≠ 0 := by
  intro h0
  have hz : ∀ b, (1 : F) * c i b + lam i * d i b = 0 := by
    intro b
    have := congrFun h0 b
    simpa [aVec] using this
  exact one_ne_zero (hbasis i 1 (lam i) hz).1

/-- `ρ_k ≠ 0`. -/
theorem ptensor_aVec_ne_zero {k : ℕ} (c d : Fin k → Bool → F) (lam : Fin k → F)
    (hbasis : ∀ (i : Fin k) (x y : F),
      (∀ b, x * c i b + y * d i b = 0) → x = 0 ∧ y = 0) :
    ptensor (aVec c d lam) ≠ 0 :=
  ptensor_ne_zero _ (aVec_ne_zero c d lam hbasis)

/-- Top-slot peeling of `τ_{castSucc m'}`: the top factor is `c_last`. -/
theorem ptensor_stairVec_castSucc {k : ℕ} (c d : Fin (k + 1) → Bool → F)
    (lam : Fin (k + 1) → F) (m' : Fin k) (s : Fin k → Bool) (b : Bool) :
    ptensor (stairVec c d lam m'.castSucc) (Fin.snoc s b) =
      ptensor (stairVec (fun i => c i.castSucc) (fun i => d i.castSucc)
          (fun i => lam i.castSucc) m') s * c (Fin.last k) b := by
  rw [ptensor_snoc]
  congr 1
  · congr 1
    funext i
    show stairVec c d lam m'.castSucc i.castSucc = _
    unfold stairVec
    by_cases h1 : i < m'
    · rw [if_pos (Fin.castSucc_lt_castSucc_iff.mpr h1), if_pos h1]
    · by_cases h2 : i = m'
      · subst h2
        rw [if_neg (by simp), if_pos rfl, if_neg (lt_irrefl _), if_pos rfl]
      · have h3 : ¬ i.castSucc < m'.castSucc := fun h => h1
          (Fin.castSucc_lt_castSucc_iff.mp h)
        have h4 : i.castSucc ≠ m'.castSucc := fun h => h2 (Fin.castSucc_inj.mp h)
        rw [if_neg h3, if_neg h4, if_neg h1, if_neg h2]
  · show stairVec c d lam m'.castSucc (Fin.last k) b = c (Fin.last k) b
    unfold stairVec
    rw [if_neg (asymm (Fin.castSucc_lt_last m')),
      if_neg (fun h => (Fin.castSucc_lt_last m').ne h.symm)]

/-- Top-slot peeling of `τ_last`: the top factor is `d_last`, the rest is
`ρ_k`. -/
theorem ptensor_stairVec_last {k : ℕ} (c d : Fin (k + 1) → Bool → F)
    (lam : Fin (k + 1) → F) (s : Fin k → Bool) (b : Bool) :
    ptensor (stairVec c d lam (Fin.last k)) (Fin.snoc s b) =
      ptensor (aVec (fun i => c i.castSucc) (fun i => d i.castSucc)
          (fun i => lam i.castSucc)) s * d (Fin.last k) b := by
  rw [ptensor_snoc]
  congr 1
  · congr 1
    funext i
    show stairVec c d lam (Fin.last k) i.castSucc = aVec _ _ _ i
    unfold stairVec aVec
    rw [if_pos (Fin.castSucc_lt_last i)]
  · show stairVec c d lam (Fin.last k) (Fin.last k) b = d (Fin.last k) b
    unfold stairVec
    rw [if_neg (lt_irrefl _), if_pos rfl]

/-- **Staircase independence** (`lem:staircase`): for per-slot bases
`{c_i, d_i}` of `F²`, the tensors `ω = ⊗ c_i` and
`τ_m = a_{<m} ⊗ d_m ⊗ c_{>m}` are linearly independent — unconditionally. -/
theorem staircase_indep : ∀ {k : ℕ} (c d : Fin k → Bool → F) (lam : Fin k → F),
    (∀ (i : Fin k) (x y : F), (∀ b, x * c i b + y * d i b = 0) → x = 0 ∧ y = 0) →
    ∀ (μ : F) (ν : Fin k → F),
      μ • ptensor c + ∑ m, ν m • ptensor (stairVec c d lam m) = 0 →
      μ = 0 ∧ ∀ m, ν m = 0 := by
  intro k
  induction k with
  | zero =>
    intro c d lam _ μ ν h
    refine ⟨?_, fun m => m.elim0⟩
    have h1 : μ • ptensor c = 0 := by simpa using h
    have hpt : ptensor c = (fun _ => (1 : F)) := by funext s; simp [ptensor]
    rw [hpt] at h1
    have := congrFun h1 (fun _ => false)
    simpa using this
  | succ k ih =>
    intro c d lam hbasis μ ν h
    set c' := fun i : Fin k => c i.castSucc with hc'
    set d' := fun i : Fin k => d i.castSucc with hd'
    set lam' := fun i : Fin k => lam i.castSucc with hlam'
    have hbasis' : ∀ (i : Fin k) (x y : F),
        (∀ b, x * c' i b + y * d' i b = 0) → x = 0 ∧ y = 0 :=
      fun i => hbasis i.castSucc
    -- the c_last- and d_last-coefficient vectors
    set A : (Fin k → Bool) → F :=
      μ • ptensor c' + ∑ m', ν m'.castSucc • ptensor (stairVec c' d' lam' m')
      with hA
    set B : (Fin k → Bool) → F :=
      ν (Fin.last k) • ptensor (aVec c' d' lam') with hB
    -- pointwise decomposition along the top slot
    have hdecomp : ∀ (s : Fin k → Bool) (b : Bool),
        A s * c (Fin.last k) b + B s * d (Fin.last k) b = 0 := by
      intro s b
      have hb := congrFun h (Fin.snoc s b)
      rw [Fin.sum_univ_castSucc] at hb
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply,
        Pi.zero_apply] at hb
      rw [ptensor_snoc] at hb
      rw [ptensor_stairVec_last c d lam s b] at hb
      have hbsum : ∀ m' : Fin k,
          ν m'.castSucc * ptensor (stairVec c d lam m'.castSucc) (Fin.snoc s b) =
          ν m'.castSucc * (ptensor (stairVec c' d' lam' m') s * c (Fin.last k) b) :=
        fun m' => by rw [ptensor_stairVec_castSucc c d lam m' s b]
      rw [Finset.sum_congr rfl fun m' _ => hbsum m'] at hb
      simp only [← hc', ← hd', ← hlam'] at hb
      rw [hA, hB]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
      have halign : (∑ x : Fin k, ν x.castSucc *
            ptensor (stairVec c' d' lam' x) s) * c (Fin.last k) b =
          ∑ x : Fin k, ν x.castSucc *
            (ptensor (stairVec c' d' lam' x) s * c (Fin.last k) b) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => by ring
      rw [add_mul, halign]
      linear_combination hb
    -- the basis at the top slot kills both coefficients
    have hAB : A = 0 ∧ B = 0 := by
      have hpt : ∀ s, A s = 0 ∧ B s = 0 := by
        intro s
        exact hbasis (Fin.last k) (A s) (B s) (fun b => hdecomp s b)
      exact ⟨funext fun s => (hpt s).1, funext fun s => (hpt s).2⟩
    -- B = 0 ⟹ ν last = 0
    have hνlast : ν (Fin.last k) = 0 := by
      have hB0 : ν (Fin.last k) • ptensor (aVec c' d' lam') = 0 := hAB.2
      rcases smul_eq_zero.mp hB0 with h0 | h0
      · exact h0
      · exact absurd h0 (ptensor_aVec_ne_zero c' d' lam' hbasis')
    -- A = 0 ⟹ inductive hypothesis kills μ and the lower ν
    have hrec := ih c' d' lam' hbasis' μ (fun m' => ν m'.castSucc) hAB.1
    refine ⟨hrec.1, ?_⟩
    intro m
    induction m using Fin.lastCases with
    | last => exact hνlast
    | cast m' => exact hrec.2 m'

end ZkWhir
