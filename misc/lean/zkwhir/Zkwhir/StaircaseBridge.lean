/-
Bridge from the protocol's Lagrange weights (`eqPoly`, `mixedPoint`) to the
abstract staircase tensors of `Zkwhir.StaircaseTensor`. The key facts:

* `eqPoly p = ptensor (vrow ∘ p)` — a Lagrange weight is the pure tensor of
  the per-slot 2-vectors `vrow t = (1 − t, t)`;
* `{vrow x, drow}` (with `drow = (−1, 1)`) is a basis of `F²` for *every*
  `x` — so the staircase basis hypothesis is unconditional;
* `ptensor` is multilinear in each slot (`ptensor_update_add/smul`).

Together these let `êq(mixedPoint ℓ y z)` be expanded in the `ω/τ` staircase
basis, the input the coupled-chains kernel (`CoupledKer`) consumes.

Part of the `GoodSetAbsorption` formalization campaign; unwired until green.
-/
import Mathlib
import Zkwhir.Statement
import Zkwhir.Channel
import Zkwhir.StaircaseTensor

set_option linter.style.header false

noncomputable section

namespace ZkWhir

variable {F : Type*} [Field F]

/-- The per-slot Lagrange 2-vector `(1 − t, t)`. -/
def vrow (t : F) : Bool → F := fun b => if b then t else 1 - t

/-- The fixed difference vector `(−1, 1)` (slot-independent). -/
def drow : Bool → F := fun b => if b then 1 else -1

/-- A Lagrange weight is the pure tensor of its per-slot 2-vectors. -/
theorem eqPoly_eq_ptensor {j : ℕ} (p : Fin j → F) :
    eqPoly p = ptensor (fun i => vrow (p i)) := by
  funext s
  unfold eqPoly ptensor vrow
  exact Finset.prod_congr rfl fun i _ => by cases s i <;> simp

/-- `{vrow x, drow}` is a basis of `F²`, for every `x`. -/
theorem vrow_basis (x : F) (x' y' : F)
    (h : ∀ b, x' * vrow x b + y' * drow b = 0) : x' = 0 ∧ y' = 0 := by
  have h0 := h false
  have h1 := h true
  simp only [vrow, drow, Bool.false_eq_true, if_false, if_true] at h0 h1
  have hx' : x' = 0 := by linear_combination h0 + h1
  refine ⟨hx', ?_⟩
  rw [hx'] at h1
  simpa using h1

/-- The affine relation `vrow t = vrow x + (t − x) • drow`, slotwise. -/
theorem vrow_affine (t x : F) :
    vrow t = fun b => vrow x b + (t - x) * drow b := by
  funext b
  cases b <;> simp [vrow, drow]

/-- **Slot additivity** of `ptensor`: splitting one slot's vector into a sum
splits the tensor. -/
theorem ptensor_update_add {k : ℕ} (w : Fin k → Bool → F) (ℓ : Fin k)
    (p q : Bool → F) :
    ptensor (Function.update w ℓ (fun b => p b + q b)) =
      ptensor (Function.update w ℓ p) + ptensor (Function.update w ℓ q) := by
  funext s
  simp only [ptensor, Pi.add_apply]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ℓ),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ ℓ),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ ℓ)]
  have herase : ∀ (r : Bool → F),
      ∏ i ∈ Finset.univ.erase ℓ, Function.update w ℓ r i (s i) =
      ∏ i ∈ Finset.univ.erase ℓ, w i (s i) :=
    fun r => Finset.prod_congr rfl fun i hi =>
      by rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [herase p, herase q, herase (fun b => p b + q b),
    Function.update_self, Function.update_self, Function.update_self]
  ring

/-- **Slot homogeneity** of `ptensor`: scaling one slot's vector scales the
tensor. -/
theorem ptensor_update_smul {k : ℕ} (w : Fin k → Bool → F) (ℓ : Fin k)
    (t : F) (r : Bool → F) :
    ptensor (Function.update w ℓ (fun b => t * r b)) =
      t • ptensor (Function.update w ℓ r) := by
  funext s
  simp only [ptensor, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ ℓ),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ ℓ)]
  have herase :
      ∏ i ∈ Finset.univ.erase ℓ, Function.update w ℓ (fun b => t * r b) i (s i) =
      ∏ i ∈ Finset.univ.erase ℓ, Function.update w ℓ r i (s i) :=
    Finset.prod_congr rfl fun i hi => by
      rw [Function.update_of_ne (Finset.mem_erase.mp hi).1,
        Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [herase, Function.update_self, Function.update_self]
  ring

/-- `a_i = c_i + λ_i d` with a constant difference vector `d`. -/
def aRow {k : ℕ} (c : Fin k → Bool → F) (d : Bool → F) (lam : Fin k → F)
    (i : Fin k) : Bool → F := fun b => c i b + lam i * d b

/-- `update`-of-`ρ_n` at the new slot `j` (with `(j:ℕ) = n`) is exactly `τ`
at that slot. Parameterized by both the `Nat` threshold and the `Fin` slot so
that it serves the telescoping induction and the mixed-point expansion. -/
theorem update_rhoN_eq_stairVec {k : ℕ} (c : Fin k → Bool → F) (d : Bool → F)
    (lam : Fin k → F) (n : ℕ) (j : Fin k) (hjv : (j : ℕ) = n) :
    Function.update (fun i : Fin k => if (i : ℕ) < n then aRow c d lam i else c i)
      j d = stairVec c (fun _ => d) lam j := by
  funext i
  unfold stairVec aRow
  by_cases hij : i = j
  · subst hij
    rw [Function.update_self, if_neg (lt_irrefl _), if_pos rfl]
  · rw [Function.update_of_ne hij]
    by_cases hlt : i < j
    · rw [if_pos (show (i : ℕ) < n by rw [← hjv]; exact hlt), if_pos hlt]
    · rw [if_neg (show ¬ (i : ℕ) < n by rw [← hjv]; exact fun h => hlt h),
        if_neg hlt, if_neg hij]

/-- **Telescoping**: `ρ_n = ω + ∑_{i < n} λ_i τ_i`. -/
theorem rhoN_telescope {k : ℕ} (c : Fin k → Bool → F) (d : Bool → F)
    (lam : Fin k → F) (n : ℕ) :
    ptensor (fun i : Fin k => if (i : ℕ) < n then aRow c d lam i else c i) =
      ptensor c + ∑ i ∈ Finset.univ.filter (fun i : Fin k => (i : ℕ) < n),
        lam i • ptensor (stairVec c (fun _ => d) lam i) := by
  induction n with
  | zero =>
    have hc : (fun i : Fin k => if (i : ℕ) < 0 then aRow c d lam i else c i)
        = c := by funext i; simp
    rw [hc]
    simp
  | succ n ih =>
    by_cases hn : n < k
    · set j : Fin k := ⟨n, hn⟩ with hj
      have hjv : (j : ℕ) = n := by rw [hj]
      -- the threshold-`n+1` pattern is the threshold-`n` pattern updated at `j`
      have hupd : (fun i : Fin k => if (i : ℕ) < n + 1 then aRow c d lam i
            else c i) =
          Function.update (fun i : Fin k => if (i : ℕ) < n then aRow c d lam i else c i)
            j (aRow c d lam j) := by
        funext i
        by_cases hij : i = j
        · subst hij
          rw [Function.update_self, if_pos (by omega)]
        · rw [Function.update_of_ne hij]
          have hne : (i : ℕ) ≠ n := fun h => hij (Fin.ext (by omega))
          by_cases hlt : (i : ℕ) < n
          · rw [if_pos (by omega), if_pos hlt]
          · rw [if_neg (by omega), if_neg hlt]
      -- `aRow j = (ρ_n at j) + λ_j d` since `ρ_n` carries `c_j` at `j`
      have hbase : (fun i : Fin k => if (i : ℕ) < n then aRow c d lam i
          else c i) j = c j := by
        show (if (j : ℕ) < n then aRow c d lam j else c j) = c j
        rw [if_neg (by omega)]
      have haj : aRow c d lam j =
          (fun b => (fun i : Fin k => if (i : ℕ) < n then aRow c d lam i
            else c i) j b + lam j * d b) := by
        rw [hbase]; rfl
      rw [hupd, haj, ptensor_update_add, Function.update_eq_self,
        ptensor_update_smul, update_rhoN_eq_stairVec c d lam n j hjv, ih]
      -- the filter gains exactly `j`
      have hfilter : Finset.univ.filter (fun i : Fin k => (i : ℕ) < n + 1) =
          insert j (Finset.univ.filter (fun i : Fin k => (i : ℕ) < n)) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_insert]
        constructor
        · intro hi
          rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
          · exact Or.inr h
          · exact Or.inl (Fin.ext (by omega))
        · rintro (h | h)
          · rw [h]; omega
          · omega
      have hjnotin : j ∉ Finset.univ.filter (fun i : Fin k => (i : ℕ) < n) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [hfilter, Finset.sum_insert hjnotin]
      abel
    · -- `n ≥ k`: nothing new below `n + 1`
      have he1 : (fun i : Fin k => if (i : ℕ) < n + 1 then aRow c d lam i
          else c i) = (fun i : Fin k => if (i : ℕ) < n then aRow c d lam i else c i) := by
        funext i
        have hik := i.isLt
        have hiff : ((i : ℕ) < n + 1) ↔ ((i : ℕ) < n) := by omega
        simp only [hiff]
      have he2 : Finset.univ.filter (fun i : Fin k => (i : ℕ) < n + 1) =
          Finset.univ.filter (fun i : Fin k => (i : ℕ) < n) := by
        ext i
        have hik := i.isLt
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        omega
      rw [he1, he2, ih]

/-- **The mixed-point staircase expansion**: replacing slot `ℓ` of `ρ_ℓ` by
`c_ℓ + t·d` adds `t·τ_ℓ`. Combined with telescoping this expands a mixed
Lagrange weight in the `ω/τ` basis. -/
theorem stairMixed_decomp {k : ℕ} (c : Fin k → Bool → F) (d : Bool → F)
    (lam : Fin k → F) (ℓ : Fin k) (t : F) :
    ptensor (fun i : Fin k => if i < ℓ then aRow c d lam i
        else if i = ℓ then (fun b => c ℓ b + t * d b) else c i) =
      ptensor c + (∑ i ∈ Finset.univ.filter (fun i : Fin k => i < ℓ),
        lam i • ptensor (stairVec c (fun _ => d) lam i)) +
      t • ptensor (stairVec c (fun _ => d) lam ℓ) := by
  -- the mixed pattern is `ρ_{ℓ.val}` updated at `ℓ`
  have hupd : (fun i : Fin k => if i < ℓ then aRow c d lam i
        else if i = ℓ then (fun b => c ℓ b + t * d b) else c i) =
      Function.update (fun i : Fin k => if (i : ℕ) < (ℓ : ℕ) then aRow c d lam i
        else c i) ℓ (fun b => c ℓ b + t * d b) := by
    funext i
    by_cases hiℓ : i = ℓ
    · subst hiℓ
      rw [Function.update_self, if_neg (lt_irrefl _), if_pos rfl]
    · rw [Function.update_of_ne hiℓ]
      by_cases hlt : i < ℓ
      · rw [if_pos hlt, if_pos (show (i : ℕ) < (ℓ : ℕ) from hlt)]
      · rw [if_neg hlt, if_neg hiℓ,
          if_neg (show ¬ (i : ℕ) < (ℓ : ℕ) from fun h => hlt h)]
  have hbase : (fun i : Fin k => if (i : ℕ) < (ℓ : ℕ) then aRow c d lam i
      else c i) ℓ = c ℓ := by
    show (if (ℓ : ℕ) < (ℓ : ℕ) then aRow c d lam ℓ else c ℓ) = c ℓ
    rw [if_neg (lt_irrefl _)]
  have hsplit : (fun b => c ℓ b + t * d b) =
      (fun b => (fun i : Fin k => if (i : ℕ) < (ℓ : ℕ) then aRow c d lam i
        else c i) ℓ b + t * d b) := by rw [hbase]
  rw [hupd, hsplit, ptensor_update_add, Function.update_eq_self,
    ptensor_update_smul, update_rhoN_eq_stairVec c d lam (ℓ : ℕ) ℓ rfl,
    rhoN_telescope]
  -- align the `< ℓ` filter (Fin order vs val order)
  have hfeq : Finset.univ.filter (fun i : Fin k => (i : ℕ) < (ℓ : ℕ)) =
      Finset.univ.filter (fun i : Fin k => i < ℓ) := by
    ext i; simp only [Finset.mem_filter, Fin.lt_def]
  rw [hfeq]

/-! ## Instantiation for the protocol mixed points -/

section Protocol

variable (P : Params) (Fq : Type*) [Field Fq] [Fintype Fq]
  [Algebra (Fp P) Fq] (Dom : Finset (Fp P)) (ch : Challenges P Fq Dom)

/-- The `c`-data of the `z`-staircase: `c_i = vrow(z^{2^i})`. -/
def czData (z : Fq) : Fin P.k₀ → Bool → Fq :=
  fun i => vrow (powSeq z P.k₀ i)

/-- The `λ`-data of the `z`-staircase: `λ_i = α_i − z^{2^i}`. -/
def lamData (z : Fq) : Fin P.k₀ → Fq :=
  fun i => ch.α i - powSeq z P.k₀ i

/-- **The mixed-point Lagrange weight in the `ω/τ` staircase basis**: the
concrete instantiation that the coupled-chains kernel consumes. -/
theorem eqPoly_mixedPoint_decomp (ℓ : Fin P.k₀) (y z : Fq) :
    eqPoly (mixedPoint P Fq Dom ch ℓ y (powSeq z P.k₀)) =
      eqPoly (powSeq z P.k₀)
      + (∑ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < ℓ),
          lamData P Fq Dom ch z i •
            ptensor (stairVec (czData P Fq z) (fun _ => drow)
              (lamData P Fq Dom ch z) i))
      + (y - powSeq z P.k₀ ℓ) •
          ptensor (stairVec (czData P Fq z) (fun _ => drow)
            (lamData P Fq Dom ch z) ℓ) := by
  have hcz : ptensor (czData P Fq z) = eqPoly (powSeq z P.k₀) := by
    rw [eqPoly_eq_ptensor]; rfl
  have hfun : (fun i => vrow (mixedPoint P Fq Dom ch ℓ y (powSeq z P.k₀) i)) =
      (fun i : Fin P.k₀ => if i < ℓ then aRow (czData P Fq z) drow
            (lamData P Fq Dom ch z) i
        else if i = ℓ then
          (fun b => czData P Fq z ℓ b + (y - powSeq z P.k₀ ℓ) * drow b)
        else czData P Fq z i) := by
    funext i
    by_cases h1 : i < ℓ
    · rw [show mixedPoint P Fq Dom ch ℓ y (powSeq z P.k₀) i = ch.α i from by
          simp [mixedPoint, h1], if_pos h1]
      unfold aRow czData lamData
      exact vrow_affine (ch.α i) (powSeq z P.k₀ i)
    · by_cases h2 : i = ℓ
      · rw [show mixedPoint P Fq Dom ch ℓ y (powSeq z P.k₀) i = y from by
            simp [mixedPoint, h2], if_neg h1, if_pos h2]
        unfold czData
        exact vrow_affine y (powSeq z P.k₀ ℓ)
      · rw [show mixedPoint P Fq Dom ch ℓ y (powSeq z P.k₀) i = powSeq z P.k₀ i
            from by simp [mixedPoint, h1, h2], if_neg h1, if_neg h2]
        rfl
  rw [eqPoly_eq_ptensor, hfun, stairMixed_decomp, hcz]

end Protocol

end ZkWhir
