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
import Zkwhir.StaircaseBridge
import Zkwhir.StaircaseTensor

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.style.show false

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

/-! ## Staircase coordinate functionals (`lem:rigidity`)

The `{c_i = vrow(x_i), d = drow}` basis of each slot plane has dual functionals
`γ^c` (the `c`-coordinate, independent of `x`) and `γ^d_x` (the `d`-coordinate).
They read off the staircase coefficients in the rigidity argument. -/

/-- The `c`-coordinate functional: the `vrow`-coefficient of a slot vector
(independent of the base point `x`). -/
def gammaC (w : Bool → Fq) : Fq := w false + w true

/-- The `d`-coordinate functional at base point `x`: the `drow`-coefficient. -/
def gammaD (x : Fq) (w : Bool → Fq) : Fq := w true - x * (w false + w true)

@[simp] theorem gammaC_vrow (x : Fq) : gammaC (vrow x) = 1 := by
  show (1 - x) + x = 1; ring

@[simp] theorem gammaC_drow : gammaC (drow : Bool → Fq) = 0 := by
  show (-1 : Fq) + 1 = 0; ring

@[simp] theorem gammaD_vrow (x : Fq) : gammaD x (vrow x) = 0 := by
  show x - x * ((1 - x) + x) = 0; ring

@[simp] theorem gammaD_drow (x : Fq) : gammaD x (drow : Bool → Fq) = 1 := by
  show (1 : Fq) - x * ((-1) + 1) = 1; ring

/-- `γ^c` is additive (a slot functional). -/
theorem gammaC_add (w w' : Bool → Fq) : gammaC (w + w') = gammaC w + gammaC w' := by
  simp only [gammaC, Pi.add_apply]; ring

/-- `γ^d` is additive. -/
theorem gammaD_add (x : Fq) (w w' : Bool → Fq) :
    gammaD x (w + w') = gammaD x w + gammaD x w' := by
  simp only [gammaD, Pi.add_apply]; ring

/-- `γ^c` is homogeneous over scalars. -/
theorem gammaC_smul (a : Fq) (w : Bool → Fq) : gammaC (a • w) = a * gammaC w := by
  simp only [gammaC, Pi.smul_apply, smul_eq_mul]; ring

/-- `γ^d` is homogeneous over scalars. -/
theorem gammaD_smul (x a : Fq) (w : Bool → Fq) :
    gammaD x (a • w) = a * gammaD x w := by
  simp only [gammaD, Pi.smul_apply, smul_eq_mul]; ring

/-- The slot indicator vector `e_b`. -/
def eBool (b : Bool) : Bool → Fq := fun b' => if b' = b then 1 else 0

/-- Every slot vector is its `e`-basis expansion. -/
theorem bool_basis (w : Bool → Fq) :
    w = (w false) • eBool false + (w true) • eBool true := by
  funext b
  cases b <;> simp [eBool, Pi.add_apply, Pi.smul_apply, smul_eq_mul]

theorem gammaC_linBool (w : Bool → Fq) :
    gammaC w = w false * gammaC (eBool false) + w true * gammaC (eBool true) := by
  conv_lhs => rw [bool_basis w]
  rw [gammaC_add, gammaC_smul, gammaC_smul]

theorem gammaD_linBool (x : Fq) (w : Bool → Fq) :
    gammaD x w = w false * gammaD x (eBool false) + w true * gammaD x (eBool true) := by
  conv_lhs => rw [bool_basis w]
  rw [gammaD_add, gammaD_smul, gammaD_smul]

/-- The tensor coefficient functional for a per-slot family `ψ`: reads the
coefficient of `f` against `⊗_i ψ_i` in the slot bases. -/
def tcoeff {k : ℕ} (ψ : Fin k → (Bool → Fq) → Fq) (f : Cube k → Fq) : Fq :=
  ∑ s : Cube k, (∏ i, ψ i (eBool (s i))) * f s

/-- **The tensor coefficient of a pure tensor factorizes**: `φ_S(⊗ w_i) = ∏_i ψ_i(w_i)`. -/
theorem tcoeff_ptensor {k : ℕ} (ψ : Fin k → (Bool → Fq) → Fq)
    (hlin : ∀ (i : Fin k) (w : Bool → Fq),
      ψ i w = w false * ψ i (eBool false) + w true * ψ i (eBool true))
    (w : Fin k → Bool → Fq) :
    tcoeff ψ (ptensor w) = ∏ i, ψ i (w i) := by
  unfold tcoeff ptensor
  rw [show (∑ s : Cube k, (∏ i, ψ i (eBool (s i))) * ∏ i, w i (s i)) =
      ∑ s : Cube k, ∏ i, (ψ i (eBool (s i)) * w i (s i)) from
    Finset.sum_congr rfl fun s _ => (Finset.prod_mul_distrib).symm]
  rw [sum_cube_prod Fq (fun i b => ψ i (eBool b) * w i b)]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hlin i (w i)]; ring

/-- `tcoeff` is additive in the table. -/
theorem tcoeff_add {k : ℕ} (ψ : Fin k → (Bool → Fq) → Fq) (f g : Cube k → Fq) :
    tcoeff ψ (f + g) = tcoeff ψ f + tcoeff ψ g := by
  unfold tcoeff
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by rw [Pi.add_apply]; ring

/-- `tcoeff` is homogeneous in the table. -/
theorem tcoeff_smul {k : ℕ} (ψ : Fin k → (Bool → Fq) → Fq) (c : Fq)
    (f : Cube k → Fq) : tcoeff ψ (c • f) = c * tcoeff ψ f := by
  unfold tcoeff
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by rw [Pi.smul_apply, smul_eq_mul]; ring

/-- `tcoeff` distributes over a finite sum of tables. -/
theorem tcoeff_finsetSum {k : ℕ} (ψ : Fin k → (Bool → Fq) → Fq) {ι : Type*}
    (S : Finset ι) (g : ι → Cube k → Fq) :
    tcoeff ψ (∑ j ∈ S, g j) = ∑ j ∈ S, tcoeff ψ (g j) := by
  classical
  induction S using Finset.induction with
  | empty => simp only [Finset.sum_empty]; unfold tcoeff; simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, tcoeff_add, ih]

/-- The combined slot vector `c_i + lam·d` written out (a `stairVec` slot for
`i < m`). -/
theorem aVec_eq (x lam : Fq) :
    (fun b => vrow x b + lam * drow b) = vrow x + lam • drow := by
  funext b; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

@[simp] theorem gammaC_aVec (x lam : Fq) :
    gammaC (fun b => vrow x b + lam * drow b) = 1 := by
  rw [aVec_eq, gammaC_add, gammaC_smul, gammaC_vrow, gammaC_drow]; ring

@[simp] theorem gammaD_aVec (x lam : Fq) :
    gammaD x (fun b => vrow x b + lam * drow b) = lam := by
  rw [aVec_eq, gammaD_add, gammaD_smul, gammaD_vrow, gammaD_drow]; ring

/-- The per-slot functional family selecting `γ^d` on the `d`-slots `S` and
`γ^c` elsewhere (the coefficient functional `φ_S`). -/
def dCoeff {k : ℕ} (x : Fin k → Fq) (S : Finset (Fin k)) :
    Fin k → (Bool → Fq) → Fq := fun i => if i ∈ S then gammaD (x i) else gammaC

theorem dCoeff_hlin {k : ℕ} (x : Fin k → Fq) (S : Finset (Fin k)) :
    ∀ (i : Fin k) (w : Bool → Fq),
      dCoeff x S i w =
        w false * dCoeff x S i (eBool false) + w true * dCoeff x S i (eBool true) := by
  intro i w
  unfold dCoeff
  split_ifs
  · exact gammaD_linBool (x i) w
  · exact gammaC_linBool w

/-- **Coefficient of `v^{(r)} = ⊗(c_i + a_i d)`**: `φ_S(v) = ∏_{i∈S} a_i`. -/
theorem tcoeff_vTensor {k : ℕ} (x a : Fin k → Fq) (S : Finset (Fin k)) :
    tcoeff (dCoeff x S)
        (ptensor (fun i => fun b => vrow (x i) b + a i * drow b)) =
      ∏ i ∈ S, a i := by
  rw [tcoeff_ptensor (dCoeff x S) (dCoeff_hlin x S)]
  rw [show (∏ i, dCoeff x S i (fun b => vrow (x i) b + a i * drow b)) =
      ∏ i, (if i ∈ S then a i else 1) from by
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold dCoeff
    split_ifs
    · exact gammaD_aVec (x i) (a i)
    · exact gammaC_aVec (x i) (a i)]
  rw [← Finset.prod_filter]
  congr 1
  ext i; simp

/-- **Coefficient of `ω = ⊗ c_i`**: `φ_S(ω) = 1` if `S = ∅`, else `0`. -/
theorem tcoeff_omegaTensor {k : ℕ} (x : Fin k → Fq) (S : Finset (Fin k)) :
    tcoeff (dCoeff x S) (ptensor (fun i => vrow (x i))) =
      if S = ∅ then 1 else 0 := by
  rw [tcoeff_ptensor (dCoeff x S) (dCoeff_hlin x S)]
  rw [show (∏ i, dCoeff x S i (vrow (x i))) = ∏ i, (if i ∈ S then (0 : Fq) else 1) from by
    refine Finset.prod_congr rfl fun i _ => ?_
    unfold dCoeff
    split_ifs
    · exact gammaD_vrow (x i)
    · exact gammaC_vrow (x i)]
  split_ifs with hS
  · subst hS; simp
  · obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    exact Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_pos hj])

/-- **Coefficient of `τ_{m'}` at the singleton `S = {m}`**: `φ_{m}(τ_{m'}) = [m'=m]`. -/
theorem tcoeff_tauTensor_single {k : ℕ} (x lam : Fin k → Fq) (m m' : Fin k) :
    tcoeff (dCoeff x {m})
        (ptensor (stairVec (fun i => vrow (x i)) (fun _ => drow) lam m')) =
      if m' = m then 1 else 0 := by
  rw [tcoeff_ptensor (dCoeff x {m}) (dCoeff_hlin x {m})]
  split_ifs with hmm
  · subst hmm
    refine Finset.prod_eq_one fun i _ => ?_
    by_cases hi : i = m'
    · subst hi
      rw [show stairVec (fun i => vrow (x i)) (fun _ => drow) lam i i = drow from by
        unfold stairVec; rw [if_neg (lt_irrefl i), if_pos rfl]]
      unfold dCoeff; rw [if_pos (Finset.mem_singleton_self i)]; exact gammaD_drow (x i)
    · unfold dCoeff; rw [if_neg (by rw [Finset.mem_singleton]; exact hi)]
      unfold stairVec
      by_cases hilt : i < m'
      · rw [if_pos hilt]; exact gammaC_aVec (x i) (lam i)
      · rw [if_neg hilt, if_neg hi]; exact gammaC_vrow (x i)
  · refine Finset.prod_eq_zero (Finset.mem_univ m') ?_
    rw [show stairVec (fun i => vrow (x i)) (fun _ => drow) lam m' m' = drow from by
      unfold stairVec; rw [if_neg (lt_irrefl m'), if_pos rfl]]
    unfold dCoeff; rw [if_neg (by rw [Finset.mem_singleton]; exact hmm)]
    exact gammaC_drow

/-- **Coefficient of `τ_{m'}` at a pair `S = {a, b}` with `a < b`**:
`φ_{a,b}(τ_{m'}) = lam_a` if `m' = b`, else `0`. -/
theorem tcoeff_tauTensor_pair {k : ℕ} (x lam : Fin k → Fq) (a b m' : Fin k)
    (hab : a < b) :
    tcoeff (dCoeff x {a, b})
        (ptensor (stairVec (fun i => vrow (x i)) (fun _ => drow) lam m')) =
      if m' = b then lam a else 0 := by
  rw [tcoeff_ptensor (dCoeff x {a, b}) (dCoeff_hlin x {a, b})]
  have hbne : a ≠ b := ne_of_lt hab
  split_ifs with hmm
  · subst m'
    rw [show (∏ i, dCoeff x {a, b} i
          (stairVec (fun i => vrow (x i)) (fun _ => drow) lam b i)) =
        ∏ i, (if i = a then lam a else 1) from by
      refine Finset.prod_congr rfl fun i _ => ?_
      by_cases hia : i = a
      · subst hia
        rw [if_pos rfl]
        unfold dCoeff
        rw [if_pos (Finset.mem_insert_self i {b})]
        rw [show stairVec (fun i => vrow (x i)) (fun _ => drow) lam b i =
            (fun bb => vrow (x i) bb + lam i * drow bb) from by
          unfold stairVec; rw [if_pos hab]]
        exact gammaD_aVec (x i) (lam i)
      · rw [if_neg hia]
        by_cases hib : i = b
        · subst hib
          unfold dCoeff
          rw [if_pos (Finset.mem_insert_of_mem (Finset.mem_singleton_self i))]
          rw [show stairVec (fun i => vrow (x i)) (fun _ => drow) lam i i = drow from by
            unfold stairVec; rw [if_neg (lt_irrefl i), if_pos rfl]]
          exact gammaD_drow (x i)
        · unfold dCoeff
          rw [if_neg (by simp [Finset.mem_insert, Finset.mem_singleton, hia, hib])]
          unfold stairVec
          by_cases hilt : i < b
          · rw [if_pos hilt]; exact gammaC_aVec (x i) (lam i)
          · rw [if_neg hilt, if_neg hib]; exact gammaC_vrow (x i)]
    rw [Finset.prod_eq_single a (fun i _ hi => if_neg hi)
      (fun h => absurd (Finset.mem_univ a) h), if_pos rfl]
  · by_cases hma : m' = a
    · subst m'
      refine Finset.prod_eq_zero (Finset.mem_univ b) ?_
      unfold dCoeff
      rw [if_pos (Finset.mem_insert_of_mem (Finset.mem_singleton_self b))]
      rw [show stairVec (fun i => vrow (x i)) (fun _ => drow) lam a b = vrow (x b) from by
        unfold stairVec; rw [if_neg (not_lt.mpr (le_of_lt hab)), if_neg hbne.symm]]
      exact gammaD_vrow (x b)
    · refine Finset.prod_eq_zero (Finset.mem_univ m') ?_
      rw [show stairVec (fun i => vrow (x i)) (fun _ => drow) lam m' m' = drow from by
        unfold stairVec; rw [if_neg (lt_irrefl m'), if_pos rfl]]
      unfold dCoeff
      rw [if_neg (by simp [Finset.mem_insert, Finset.mem_singleton, hma, hmm])]
      exact gammaC_drow

/-- **Rigidity** (`lem:rigidity`): if a combination `∑_r y_r v^{(r)}` of conjugate
staircase tensors lies in the span `{ω, τ_{m'}}` of the base (`lam`) staircase,
then for every slot `m` above `first` the coupled relation holds. This is what
forces `cond:twist`'s trace-twist to be untwisted. -/
theorem rigidity {k : ℕ} (x lam : Fin k → Fq) {R : Type*} [Fintype R]
    (a : R → Fin k → Fq) (y : R → Fq) (first m : Fin k) (hfm : first < m)
    (cω : Fq) (ct : Fin k → Fq)
    (heq : (∑ r, y r • ptensor (fun i => fun b => vrow (x i) b + a r i * drow b)) =
        cω • ptensor (fun i => vrow (x i)) +
          ∑ m', ct m' •
            ptensor (stairVec (fun i => vrow (x i)) (fun _ => drow) lam m')) :
    ∑ r, y r * ((a r first - lam first) * a r m) = 0 := by
  have hfne : first ≠ m := ne_of_lt hfm
  have hsingle : (∑ r, y r * a r m) = ct m := by
    have h := congrArg (tcoeff (dCoeff x {m})) heq
    simp only [tcoeff_finsetSum, tcoeff_add, tcoeff_smul, tcoeff_vTensor,
      tcoeff_omegaTensor, tcoeff_tauTensor_single, Finset.prod_singleton,
      Finset.singleton_ne_empty, if_false, mul_zero, zero_add, mul_ite, mul_one,
      Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    exact h
  have hpair : (∑ r, y r * (a r first * a r m)) = ct m * lam first := by
    have h := congrArg (tcoeff (dCoeff x {first, m})) heq
    simp only [tcoeff_finsetSum, tcoeff_add, tcoeff_smul, tcoeff_vTensor,
      tcoeff_omegaTensor, tcoeff_tauTensor_pair x lam first m _ hfm,
      Finset.prod_pair hfne, Finset.insert_ne_empty, if_false, mul_zero, zero_add,
      mul_ite, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    exact h
  rw [show (∑ r, y r * ((a r first - lam first) * a r m)) =
      (∑ r, y r * (a r first * a r m)) - lam first * (∑ r, y r * a r m) from by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring]
  rw [hpair, hsingle]; ring

/-- **The Lagrange weight in `rigidity`'s `v`-form**: `êq(β, ·)` is the staircase
tensor `⊗(c_i + (β_i − z^{2^{i-1}}) d)` over the `z`-staircase. With `β = α^{[r]}`
this is exactly `rigidity`'s `v^{(r)}` (`x_i = z^{2^{i-1}}`, `a^{(r)}_i = β_i − x_i`). -/
theorem eqPoly_eq_vTensor {k : ℕ} (z : Fq) (β : Fin k → Fq) :
    eqPoly β =
      ptensor (fun i => fun b =>
        vrow (powSeq z k i) b + (β i - powSeq z k i) * drow b) := by
  rw [eqPoly_eq_ptensor]
  congr 1
  funext i
  rw [vrow_affine (β i) (powSeq z k i)]

/-- **`cond:twist`** (assembly): suppose an `Fp`-linear endomorphism `T` of `Fq`,
evaluated along the Lagrange weights `λ_s = êq(α, s)`, lands in the protocol
staircase span `{ω, τ_{m'}}` (the row space, by `lem:nodechannel`). Then — given
the Frobenius staircase matrix `M^{(j)} = (α_m^{p^r} − z^{2^{m}})_{m>0,\,1≤r<d}`
has trivial kernel and the Frobenius gaps `D_r = α_0^{p^r} − α_0` are nonzero for
`1 ≤ r < d` (the Good-set genericity conditions, bounded later in the measure
step) — `T` is forced **untwisted**: `T x = t_0·x` for a scalar `t_0`.

This is the linear-algebra core of `cond:twist`: Ore's theorem
(`exists_qpoly_repr`) writes `T x = ∑_r t_r x^{p^r}`; `eqPoly_eq_vTensor` turns the
`p^r`-conjugate weights into `rigidity`'s staircase `v`-tensors; `rigidity` then
extracts `∑_r t_r D_r·(α_m^{p^r} − z^{2^m}) = 0` for every slot `m > 0`; trivial
kernel forces `t_r D_r = 0`, and `D_r ≠ 0` forces `t_r = 0` for `r ≥ 1`. -/
theorem condTwist {k : ℕ} (hk : 0 < k)
    (hcard : Fintype.card Fp = p) (d : ℕ) (hd0 : 0 < d)
    (hd : Fintype.card Fq = p ^ d) (hdeg : Module.finrank Fp Fq = d)
    (T : Fq →ₗ[Fp] Fq) (z : Fq) (α : Fin k → Fq)
    (cω : Fq) (ct : Fin k → Fq)
    (hrow : (fun s => T (eqPoly α s)) =
        cω • ptensor (fun i => vrow (powSeq z k i)) +
          ∑ m', ct m' • ptensor (stairVec (fun i => vrow (powSeq z k i)) (fun _ => drow)
            (fun i => α i - powSeq z k i) m'))
    (hker : ∀ c : Fin d → Fq, c ⟨0, hd0⟩ = 0 →
        (∀ m : Fin k, (⟨0, hk⟩ : Fin k) < m →
          ∑ r, c r * (α m ^ p ^ (r : ℕ) - powSeq z k m) = 0) → c = 0)
    (hDr : ∀ r : Fin d, (r : ℕ) ≠ 0 →
        α ⟨0, hk⟩ ^ p ^ (r : ℕ) - α ⟨0, hk⟩ ≠ 0) :
    ∃ c : Fq, ∀ x, T x = c * x := by
  -- Ore: q-polynomial coefficients of `T`.
  obtain ⟨t, ht⟩ := Linearized.exists_qpoly_repr hcard d hd hdeg T
  -- `T` along the weights is the `t`-combination of the conjugate weights.
  have hTsum : (fun s => T (eqPoly α s)) =
      ∑ r : Fin d, t r • (eqPoly (fun i => α i ^ p ^ (r : ℕ)) : Cube k → Fq) := by
    funext s
    rw [ht (eqPoly α s)]
    conv_rhs => rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, eqPoly_pow]
  -- Rewrite into `rigidity`'s staircase `v`-form and identify with the row space.
  have heq : (∑ r : Fin d, t r • ptensor (fun i => fun b =>
        vrow (powSeq z k i) b + (α i ^ p ^ (r : ℕ) - powSeq z k i) * drow b)) =
      cω • ptensor (fun i => vrow (powSeq z k i)) +
        ∑ m', ct m' • ptensor (stairVec (fun i => vrow (powSeq z k i)) (fun _ => drow)
          (fun i => α i - powSeq z k i) m') := by
    rw [← hrow, hTsum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [eqPoly_eq_vTensor z (fun i => α i ^ p ^ (r : ℕ))]
  -- `rigidity` per slot `m > 0`, rewritten with the kernel coefficients `c_r = t_r·D_r`.
  have hkereq : ∀ m : Fin k, (⟨0, hk⟩ : Fin k) < m →
      ∑ r : Fin d, (t r * (α ⟨0, hk⟩ ^ p ^ (r : ℕ) - α ⟨0, hk⟩)) *
        (α m ^ p ^ (r : ℕ) - powSeq z k m) = 0 := by
    intro m hm
    have hrig := rigidity (fun i => powSeq z k i) (fun i => α i - powSeq z k i)
      (fun (r : Fin d) i => α i ^ p ^ (r : ℕ) - powSeq z k i) t ⟨0, hk⟩ m hm cω ct heq
    rw [← hrig]
    refine Finset.sum_congr rfl fun r _ => ?_
    show t r * (α ⟨0, hk⟩ ^ p ^ (r : ℕ) - α ⟨0, hk⟩) * (α m ^ p ^ (r : ℕ) - powSeq z k m)
        = t r * (((α ⟨0, hk⟩ ^ p ^ (r : ℕ) - powSeq z k ⟨0, hk⟩)
            - (α ⟨0, hk⟩ - powSeq z k ⟨0, hk⟩)) * (α m ^ p ^ (r : ℕ) - powSeq z k m))
    ring
  -- The coefficient vector `c_r = t_r·D_r` is in the (trivial) kernel, hence zero.
  have hc0 : (fun r : Fin d => t r * (α ⟨0, hk⟩ ^ p ^ (r : ℕ) - α ⟨0, hk⟩)) ⟨0, hd0⟩ = 0 := by
    simp
  have hceq : (fun r : Fin d => t r * (α ⟨0, hk⟩ ^ p ^ (r : ℕ) - α ⟨0, hk⟩)) = 0 :=
    hker _ hc0 hkereq
  -- `D_r ≠ 0` for `r ≥ 1` forces the twist coefficients `t_r = 0`.
  have htr : ∀ r : Fin d, (r : ℕ) ≠ 0 → t r = 0 := by
    intro r hr
    have hzero : t r * (α ⟨0, hk⟩ ^ p ^ (r : ℕ) - α ⟨0, hk⟩) = 0 := by
      have := congrFun hceq r; simpa using this
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h (hDr r hr)
  -- Only the `r = 0` term survives: `T x = t_0·x`.
  refine ⟨t ⟨0, hd0⟩, fun x => ?_⟩
  rw [ht x, Finset.sum_eq_single (⟨0, hd0⟩ : Fin d)]
  · simp
  · intro r _ hr
    have hrne : (r : ℕ) ≠ 0 := fun h => hr (Fin.ext h)
    rw [htr r hrne, zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h

end ZkWhir
