/-
Block geometry (`def:blocks` of `zk_leanVM.tex`): the block positions — the
last `2^a` positions of a class — are exactly the positions whose top `m − a`
coordinates are all set. In particular the block set is *upward closed* in
the coordinatewise order, which is what makes the `êq(pow(x, m), ·)`
expansion upper-triangular over the blocks and lets the per-class CRT solver
(`lem:crt`) realize arbitrary fiber and node evaluations there
(`prop:uniform`, Stage B).

Part of the `GoodSetAbsorption` formalization campaign.
-/
import Mathlib
import Zkwhir.Statement
import Zkwhir.CRT

set_option linter.style.header false
set_option linter.unusedSectionVars false

noncomputable section

namespace ZkWhir

variable (P : Params)

theorem sum_range_two_pow (n : ℕ) :
    ∑ i ∈ Finset.range n, 2 ^ i = 2 ^ n - 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    have h1 : 0 < 2 ^ n := Nat.two_pow_pos n
    have h2 : 2 ^ (n + 1) = 2 ^ n * 2 := pow_succ 2 n
    omega

/-- **Block characterization** (`def:blocks`): a position is in the block iff
its top `m − a` coordinates are all set. -/
theorem isBlockPos_iff (c : Cube P.m) :
    IsBlockPos P c ↔ ∀ i : Fin P.m, P.a ≤ (i : ℕ) → c i = true := by
  classical
  have h1 : ∑ i ∈ Finset.univ.filter (fun i : Fin P.m => c i = true),
      2 ^ (i : ℕ) = posVal c := by
    rw [Finset.sum_filter]
    rfl
  have h2 := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin P.m => c i = true) (fun i => 2 ^ (i : ℕ))
  have h3 : ∑ i : Fin P.m, 2 ^ (i : ℕ) = 2 ^ P.m - 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i)]
    exact sum_range_two_pow P.m
  have hsplit : posVal c + ∑ i ∈ Finset.univ.filter
      (fun i : Fin P.m => ¬ c i = true), 2 ^ (i : ℕ) = 2 ^ P.m - 1 := by
    omega
  have hpow2 : 2 ^ P.a ≤ 2 ^ P.m := Nat.pow_le_pow_right (by norm_num) P.a_le_m
  have hpos : 0 < 2 ^ P.a := Nat.two_pow_pos _
  constructor
  · intro hb i hi
    by_contra hci
    have hmem : i ∈ Finset.univ.filter (fun i : Fin P.m => ¬ c i = true) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hci
    have hone : 2 ^ (i : ℕ) ≤ ∑ i' ∈ Finset.univ.filter
        (fun i' : Fin P.m => ¬ c i' = true), 2 ^ (i' : ℕ) :=
      Finset.single_le_sum (f := fun i' : Fin P.m => 2 ^ (i' : ℕ))
        (fun _ _ => Nat.zero_le _) hmem
    have hpow1 : 2 ^ P.a ≤ 2 ^ (i : ℕ) :=
      Nat.pow_le_pow_right (by norm_num) hi
    have hb' : 2 ^ P.m - 2 ^ P.a ≤ posVal c := hb
    omega
  · intro hbits
    have hsub : Finset.univ.filter (fun i : Fin P.m => ¬ c i = true) ⊆
        Finset.univ.filter (fun i : Fin P.m => (i : ℕ) < P.a) := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      by_contra hlt
      exact hi (hbits i (by omega))
    have hle : ∑ i ∈ Finset.univ.filter (fun i : Fin P.m => ¬ c i = true),
        2 ^ (i : ℕ) ≤
        ∑ i ∈ Finset.univ.filter (fun i : Fin P.m => (i : ℕ) < P.a),
          2 ^ (i : ℕ) :=
      Finset.sum_le_sum_of_subset hsub
    have hlow : ∑ i ∈ Finset.univ.filter (fun i : Fin P.m => (i : ℕ) < P.a),
        2 ^ (i : ℕ) = 2 ^ P.a - 1 := by
      rw [Finset.sum_filter,
        Fin.sum_univ_eq_sum_range (fun j => if j < P.a then 2 ^ j else 0)]
      have hcong : ∀ j ∈ Finset.range P.m,
          (if j < P.a then 2 ^ j else 0) =
          (if j ∈ Finset.range P.a then 2 ^ j else 0) := by
        intro j _
        simp [Finset.mem_range]
      rw [Finset.sum_congr rfl hcong, Finset.sum_ite_mem]
      have hint : Finset.range P.m ∩ Finset.range P.a = Finset.range P.a := by
        rw [Finset.inter_comm]
        refine Finset.inter_eq_left.mpr fun x hx => ?_
        rw [Finset.mem_range] at hx ⊢
        have := P.a_le_m
        omega
      rw [hint, sum_range_two_pow]
    show 2 ^ P.m - 2 ^ P.a ≤ posVal c
    omega

/-- The block set is upward closed in the coordinatewise order. -/
theorem IsBlockPos.mono {c c' : Cube P.m}
    (hcc : ∀ i, c i = true → c' i = true) (hc : IsBlockPos P c) :
    IsBlockPos P c' := by
  rw [isBlockPos_iff] at hc ⊢
  exact fun i hi => hcc i (hc i hi)

/-! ## The numeric value of a position -/

theorem posVal_eq_sum_filter {j : ℕ} (c : Cube j) :
    posVal c =
      ∑ i ∈ Finset.univ.filter (fun i : Fin j => c i = true), 2 ^ (i : ℕ) := by
  rw [Finset.sum_filter]
  rfl

/-- `posVal` is strictly monotone along strict coordinatewise containment. -/
theorem posVal_lt_of_lt {j : ℕ} {c c' : Cube j}
    (hsub : ∀ i, c i = true → c' i = true) (hne : c ≠ c') :
    posVal c < posVal c' := by
  classical
  rw [posVal_eq_sum_filter, posVal_eq_sum_filter]
  have hsubset : Finset.univ.filter (fun i : Fin j => c i = true) ⊆
      Finset.univ.filter (fun i : Fin j => c' i = true) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hsub i hi
  have hwit : ∃ i, c' i = true ∧ ¬ c i = true := by
    by_contra hall
    apply hne
    funext i
    have hi := not_exists.mp hall i
    cases hci : c i with
    | true => exact (hsub i hci).symm
    | false =>
      cases hci' : c' i with
      | false => rfl
      | true => exact absurd ⟨hci', by simp [hci]⟩ hi
  obtain ⟨i, hi', hi⟩ := hwit
  refine Finset.sum_lt_sum_of_subset hsubset (i := i) ?_ ?_
    (Nat.two_pow_pos _) (fun _ _ _ => Nat.zero_le _)
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi'
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hi

/-- Splitting off the lowest coordinate: `posVal (b ∷ c) = b + 2·posVal c`. -/
theorem posVal_cons {j : ℕ} (b : Bool) (c : Cube j) :
    posVal (Fin.cons b c : Cube (j + 1)) =
      (if b then 1 else 0) + 2 * posVal c := by
  unfold posVal
  rw [Fin.sum_univ_succ, Finset.mul_sum]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.val_zero, pow_zero, Fin.val_succ]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hc : c i <;> simp [hc, pow_succ, mul_comm]

/-- The numeric value of a position is below `2^j`. -/
theorem posVal_lt_two_pow {j : ℕ} (c : Cube j) : posVal c < 2 ^ j := by
  have h1 : posVal c ≤ ∑ i : Fin j, 2 ^ (i : ℕ) := by
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hc : c i <;> simp [hc]
  have h2 : ∑ i : Fin j, 2 ^ (i : ℕ) = 2 ^ j - 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i)]
    exact sum_range_two_pow j
  have := Nat.two_pow_pos j
  omega

/-- Every value below `2^j` is the value of a position (binary digits). -/
theorem posVal_surj : ∀ (j k : ℕ), k < 2 ^ j → ∃ c : Cube j, posVal c = k := by
  intro j
  induction j with
  | zero =>
    intro k hk
    have hk0 : k = 0 := by simpa using Nat.lt_one_iff.mp (by simpa using hk)
    exact ⟨fun i => i.elim0, by simp [posVal, hk0]⟩
  | succ j ihj =>
    intro k hk
    have hdm := Nat.div_add_mod k 2
    have hpow : 2 ^ (j + 1) = 2 ^ j * 2 := pow_succ 2 j
    have hdiv : k / 2 < 2 ^ j := by omega
    obtain ⟨c, hc⟩ := ihj (k / 2) hdiv
    rcases Nat.mod_two_eq_zero_or_one k with hm | hm
    · refine ⟨Fin.cons false c, ?_⟩
      rw [posVal_cons, hc]
      simp only [Bool.false_eq_true, if_false]
      omega
    · refine ⟨Fin.cons true c, ?_⟩
      rw [posVal_cons, hc]
      simp only [if_true]
      omega

/-- `posVal` (the binary encoding of a position) is injective on `Cube j`. -/
theorem posVal_injective {j : ℕ} : Function.Injective (posVal : Cube j → ℕ) := by
  set f : Cube j → Fin (2 ^ j) := fun c => ⟨posVal c, posVal_lt_two_pow c⟩ with hf
  have hcard : Fintype.card (Cube j) = Fintype.card (Fin (2 ^ j)) := by
    simp [Cube, Fintype.card_fin, Fintype.card_bool]
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_surjective_and_card f).mpr
      ⟨fun k => by
        obtain ⟨c, hc⟩ := posVal_surj j k.val k.isLt
        exact ⟨c, by simp [hf, Fin.ext_iff, hc]⟩, hcard⟩
  intro a b hab
  exact hbij.injective (Fin.ext hab)

/-- The Lagrange weight commutes with scalar extension. -/
theorem eqPoly_algebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {j : ℕ} (x : Fin j → R) (c : Cube j) :
    eqPoly (fun i => algebraMap R A (x i)) c = algebraMap R A (eqPoly x c) := by
  unfold eqPoly
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hc : c i <;> simp [hc]

/-- The `pow`-point commutes with scalar extension. -/
theorem powSeq_algebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (z : R) (j : ℕ) :
    powSeq (algebraMap R A z) j = fun i => algebraMap R A (powSeq z j i) := by
  funext i
  simp [powSeq]

/-- The multilinear extension is additive in the table. -/
theorem mle_add {R : Type*} [CommRing R] {j : ℕ} (f g : Cube j → R)
    (x : Fin j → R) :
    mle (fun c => f c + g c) x = mle f x + mle g x := by
  unfold mle
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- A base-valued extension evaluated at a base `pow`-point stays in the
base: `mle` commutes with scalar extension. -/
theorem mle_algebraMap {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {j : ℕ} (g : Cube j → R) (x : R) :
    mle (fun c => algebraMap R A (g c)) (powSeq (algebraMap R A x) j) =
      algebraMap R A (mle g (powSeq x j)) := by
  unfold mle
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [powSeq_algebraMap, eqPoly_algebraMap, map_mul]

/-! ## The cell polynomials

`êq(pow(x, j), c)`, as a polynomial in `x`: the univariate face of a position
cell. Its evaluations at the queried points and at the nodes are what the
per-class CRT solver controls. -/

section CellPoly

variable {R : Type*} [CommRing R] {j : ℕ}

open Polynomial

/-- The cell polynomial of the position `c`:
`∏_i (X^(2^i))^(c_i) · (1 − X^(2^i))^(1−c_i)`. -/
noncomputable def cellPoly (c : Cube j) : Polynomial R :=
  ∏ i, if c i then X ^ (2 ^ (i : ℕ)) else 1 - X ^ (2 ^ (i : ℕ))

/-- Evaluating the cell polynomial recovers the Lagrange weight at the
`pow`-point. -/
theorem aeval_cellPoly {A : Type*} [CommRing A] [Algebra R A] (x : A)
    (c : Cube j) :
    aeval x (cellPoly (R := R) c) = eqPoly (powSeq x j) c := by
  unfold cellPoly eqPoly powSeq
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hc : c i
  · rw [if_pos hc, if_pos hc]
    simp
  · rw [if_neg hc, if_neg hc]
    simp

/-- The cell polynomial has degree `< 2^j`. -/
theorem cellPoly_natDegree_lt (c : Cube j) :
    (cellPoly (R := R) c).natDegree < 2 ^ j ∨ cellPoly (R := R) c = 0 := by
  by_cases h0 : (cellPoly (R := R) c) = 0
  · exact Or.inr h0
  refine Or.inl ?_
  have hdeg : (cellPoly (R := R) c).natDegree ≤
      ∑ i : Fin j, 2 ^ (i : ℕ) := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hc : c i
    · rw [if_pos hc]
      exact (Polynomial.natDegree_X_pow_le _)
    · rw [if_neg hc]
      refine (Polynomial.natDegree_sub_le _ _).trans ?_
      simp [Polynomial.natDegree_X_pow_le]
  have htot : ∑ i : Fin j, 2 ^ (i : ℕ) = 2 ^ j - 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i)]
    exact sum_range_two_pow j
  have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
  omega

/-- **Up-set expansion of the cell polynomial**: `cellPoly c` is the signed
sum of the monomials `X^(posVal c')` over the up-set of `c`. Together with
`posVal_lt_of_lt` this makes the cell polynomials of an upward-closed set of
positions unitriangular over the corresponding monomials — the engine of the
block solver (`prop:uniform`, Stage B). -/
theorem cellPoly_eq_sum (c : Cube j) :
    cellPoly (R := R) c =
      ∑ c' ∈ Finset.univ.filter
          (fun c' : Cube j => ∀ i, c i = true → c' i = true),
        (-1 : Polynomial R) ^
            (Finset.univ.filter
              (fun i : Fin j => c' i = true ∧ ¬ c i = true)).card *
          X ^ posVal c' := by
  classical
  have hfac : ∀ i : Fin j,
      (if c i then (X : Polynomial R) ^ (2 ^ (i : ℕ))
        else 1 - X ^ (2 ^ (i : ℕ))) =
      ∑ b ∈ (if c i then ({true} : Finset Bool) else Finset.univ),
        (if b then (if c i then (X : Polynomial R) ^ (2 ^ (i : ℕ))
          else - X ^ (2 ^ (i : ℕ))) else 1) := by
    intro i
    by_cases hc : c i
    · simp [hc]
    · simp [hc, sub_eq_neg_add]
  have hset : Fintype.piFinset
      (fun i => if c i then ({true} : Finset Bool) else Finset.univ) =
      Finset.univ.filter
        (fun c' : Cube j => ∀ i, c i = true → c' i = true) := by
    ext c'
    simp only [Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro h i hci
      have hh := h i
      rw [if_pos hci] at hh
      simpa using hh
    · intro h i
      by_cases hci : c i
      · rw [if_pos hci]
        simp [h i hci]
      · rw [if_neg hci]
        exact Finset.mem_univ _
  calc cellPoly (R := R) c
      = ∏ i, ∑ b ∈ (if c i then ({true} : Finset Bool) else Finset.univ),
          (if b then (if c i then (X : Polynomial R) ^ (2 ^ (i : ℕ))
            else - X ^ (2 ^ (i : ℕ))) else 1) :=
        Finset.prod_congr rfl fun i _ => hfac i
    _ = ∑ c' ∈ Fintype.piFinset
          (fun i => if c i then ({true} : Finset Bool) else Finset.univ),
        ∏ i, (if c' i then (if c i then (X : Polynomial R) ^ (2 ^ (i : ℕ))
          else - X ^ (2 ^ (i : ℕ))) else 1) := Finset.prod_univ_sum _ _
    _ = ∑ c' ∈ Finset.univ.filter
          (fun c' : Cube j => ∀ i, c i = true → c' i = true),
        ∏ i, (if c' i then (if c i then (X : Polynomial R) ^ (2 ^ (i : ℕ))
          else - X ^ (2 ^ (i : ℕ))) else 1) := by rw [hset]
    _ = ∑ c' ∈ Finset.univ.filter
          (fun c' : Cube j => ∀ i, c i = true → c' i = true),
        (-1 : Polynomial R) ^
            (Finset.univ.filter
              (fun i : Fin j => c' i = true ∧ ¬ c i = true)).card *
          X ^ posVal c' := by
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [← Finset.prod_filter]
        have hsplit : ∀ i ∈ Finset.univ.filter (fun i : Fin j => c' i = true),
            (if c i then (X : Polynomial R) ^ (2 ^ (i : ℕ))
              else - X ^ (2 ^ (i : ℕ))) =
            (if c i then (1 : Polynomial R) else -1) * X ^ (2 ^ (i : ℕ)) := by
          intro i _
          by_cases hc : c i <;> simp [hc]
        rw [Finset.prod_congr rfl hsplit, Finset.prod_mul_distrib]
        congr 1
        · rw [Finset.prod_ite (f := fun _ => (1 : Polynomial R))
            (g := fun _ => (-1 : Polynomial R)), Finset.prod_const_one,
            one_mul, Finset.prod_const, Finset.filter_filter]
        · rw [Finset.prod_pow_eq_pow_sum, posVal_eq_sum_filter]

theorem neg_one_pow_mul_X_pow_coeff (e p k : ℕ) :
    ((-1 : Polynomial R) ^ e * X ^ p).coeff k =
      if k = p then (-1 : R) ^ e else 0 := by
  have hC : ((-1 : Polynomial R) ^ e) = C ((-1 : R) ^ e) := by
    rw [map_pow, map_neg, map_one]
  rw [hC, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs <;> simp

/-- The diagonal coefficient of a cell polynomial is `1`. -/
theorem cellPoly_coeff_posVal (c : Cube j) :
    (cellPoly (R := R) c).coeff (posVal c) = 1 := by
  classical
  rw [cellPoly_eq_sum, Polynomial.finsetSum_coeff, Finset.sum_eq_single c]
  · rw [neg_one_pow_mul_X_pow_coeff, if_pos rfl]
    have hcard : (Finset.univ.filter
        (fun i : Fin j => c i = true ∧ ¬ c i = true)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun i _ => fun ⟨h1, h2⟩ => h2 h1
    rw [hcard, pow_zero]
  · intro c' hc' hne
    have hup : ∀ i, c i = true → c' i = true := (Finset.mem_filter.mp hc').2
    have hlt : posVal c < posVal c' := posVal_lt_of_lt hup (Ne.symm hne)
    rw [neg_one_pow_mul_X_pow_coeff, if_neg (by omega)]
  · intro hcm
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun i hi => hi⟩) hcm

/-- Off the `posVal`-values of the up-set, the cell polynomial has no
coefficient. -/
theorem cellPoly_coeff_eq_zero (c : Cube j) (k : ℕ)
    (hk : ∀ c' : Cube j, (∀ i, c i = true → c' i = true) → posVal c' ≠ k) :
    (cellPoly (R := R) c).coeff k = 0 := by
  classical
  rw [cellPoly_eq_sum, Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero fun c' hc' => ?_
  have hup : ∀ i, c i = true → c' i = true := (Finset.mem_filter.mp hc').2
  rw [neg_one_pow_mul_X_pow_coeff, if_neg (fun heq => hk c' hup heq.symm)]

/-- **`lem:binpow` (binary-power non-vanishing).** A nonzero `R`-linear
combination of the cell polynomials is itself nonzero. The lowest-`posVal`
position `b₀` with a nonzero coefficient contributes `T b₀ ≠ 0` to the
`X^(posVal b₀)` coefficient of the combination, and no other position can
reach down to that degree (the up-set expansion only adds higher monomials,
and `posVal` is injective). -/
theorem cellPoly_combo_ne_zero {T : Cube j → R} (hT : T ≠ 0) :
    (∑ b : Cube j, T b • cellPoly (R := R) b) ≠ 0 := by
  classical
  have hne : (Finset.univ.filter (fun b => T b ≠ 0)).Nonempty := by
    rw [Finset.filter_nonempty_iff]
    by_contra h
    push_neg at h
    exact hT (funext fun b => h b (Finset.mem_univ b))
  obtain ⟨b₀, hb₀mem, hb₀min⟩ :=
    Finset.exists_min_image (Finset.univ.filter (fun b => T b ≠ 0)) posVal hne
  have hother : ∀ b ∈ (Finset.univ : Finset (Cube j)), b ≠ b₀ →
      (T b • cellPoly (R := R) b).coeff (posVal b₀) = 0 := by
    intro b _ hbne
    rw [Polynomial.coeff_smul, smul_eq_mul]
    by_cases hTb : T b = 0
    · rw [hTb, zero_mul]
    · have hbmem : b ∈ Finset.univ.filter (fun b => T b ≠ 0) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hTb⟩
      have hge : posVal b₀ ≤ posVal b := hb₀min b hbmem
      have hz : (cellPoly (R := R) b).coeff (posVal b₀) = 0 := by
        apply cellPoly_coeff_eq_zero
        intro c' hup hpv
        have hcb : c' = b₀ := posVal_injective hpv
        subst c'
        have hlt : posVal b < posVal b₀ := posVal_lt_of_lt hup hbne
        omega
      rw [hz, mul_zero]
  have hcoeff : (∑ b : Cube j, T b • cellPoly (R := R) b).coeff (posVal b₀) = T b₀ := by
    rw [Polynomial.finsetSum_coeff,
      Finset.sum_eq_single_of_mem b₀ (Finset.mem_univ b₀) hother,
      Polynomial.coeff_smul, cellPoly_coeff_posVal, smul_eq_mul, mul_one]
  intro hzero
  rw [hzero, Polynomial.coeff_zero] at hcoeff
  exact (Finset.mem_filter.mp hb₀mem).2 hcoeff.symm

/-- The degree half of `lem:binpow`: any `R`-combination of the cell
polynomials has degree below `2^j` (each cell polynomial does). Together with
`cellPoly_combo_ne_zero` this gives the univariate Schwartz–Zippel bound on the
binary-power substitution `z ↦ mle T (powSeq z)`. -/
theorem cellPoly_combo_natDegree_lt (T : Cube j → R) :
    (∑ b : Cube j, T b • cellPoly (R := R) b).natDegree < 2 ^ j := by
  have hpos : 0 < 2 ^ j := Nat.two_pow_pos j
  have hle : (∑ b : Cube j, T b • cellPoly (R := R) b).natDegree ≤ 2 ^ j - 1 := by
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro b _
    refine le_trans (Polynomial.natDegree_smul_le _ _) ?_
    rcases cellPoly_natDegree_lt (R := R) b with hlt | hcz
    · omega
    · rw [hcz, Polynomial.natDegree_zero]; omega
  omega

end CellPoly

/-! ## The block solver (`prop:uniform`, Stage B)

Block-supported value vectors realize *every* polynomial supported on the top
degree window `[2^m − 2^a, 2^m)` — the unitriangular solve along `posVal`. -/

section BlockSolve

variable {R : Type*} [CommRing R]

open Polynomial

theorem exists_block_table_aux (n : ℕ) :
    ∀ h : Polynomial R,
      (∀ k ∈ h.support, 2 ^ P.m - 2 ^ P.a ≤ k ∧ k < 2 ^ P.m) →
      (∀ k ∈ h.support, 2 ^ P.m - k ≤ n) →
      ∃ v : Cube P.m → R, (∀ c, v c ≠ 0 → IsBlockPos P c) ∧
        ∑ c, v c • cellPoly (R := R) c = h := by
  induction n with
  | zero =>
    intro h hw hn
    have h0 : h = 0 := by
      by_contra hne
      obtain ⟨k, hk⟩ := Polynomial.support_nonempty.mpr hne
      have h1 := hw k hk
      have h2 := hn k hk
      omega
    subst h0
    exact ⟨0, fun c hc => absurd rfl hc, by simp⟩
  | succ n ih =>
    intro h hw hn
    by_cases h0 : h = 0
    · subst h0
      exact ⟨0, fun c hc => absurd rfl hc, by simp⟩
    have hne : h.support.Nonempty := Polynomial.support_nonempty.mpr h0
    set k := h.support.min' hne with hkdef
    have hkmem : k ∈ h.support := h.support.min'_mem hne
    obtain ⟨hk1, hk2⟩ := hw k hkmem
    obtain ⟨ck, hckpos⟩ := posVal_surj P.m k hk2
    have hckblock : IsBlockPos P ck := by
      show 2 ^ P.m - 2 ^ P.a ≤ posVal ck
      omega
    set h' : Polynomial R := h - h.coeff k • cellPoly (R := R) ck with hh'
    have hcoeff' : ∀ j', h'.coeff j' =
        h.coeff j' - h.coeff k * (cellPoly (R := R) ck).coeff j' := by
      intro j'
      rw [hh', Polynomial.coeff_sub, Polynomial.coeff_smul, smul_eq_mul]
    have hck_k : (cellPoly (R := R) ck).coeff k = 1 := by
      rw [← hckpos]
      exact cellPoly_coeff_posVal ck
    have hk_zero : h'.coeff k = 0 := by
      rw [hcoeff' k, hck_k, mul_one, sub_self]
    have hsupp' : ∀ j' ∈ h'.support,
        (2 ^ P.m - 2 ^ P.a ≤ j' ∧ j' < 2 ^ P.m) ∧ k < j' := by
      intro j' hj'
      have hco : h'.coeff j' ≠ 0 := Polynomial.mem_support_iff.mp hj'
      have hjk : j' ≠ k := fun heq => hco (heq ▸ hk_zero)
      by_cases hjh : j' ∈ h.support
      · exact ⟨hw j' hjh,
          lt_of_le_of_ne (h.support.min'_le j' hjh) (Ne.symm hjk)⟩
      · have hch : h.coeff j' = 0 := by
          by_contra hcc
          exact hjh (Polynomial.mem_support_iff.mpr hcc)
        have hcp : (cellPoly (R := R) ck).coeff j' ≠ 0 := by
          intro hz
          exact hco (by rw [hcoeff' j', hch, hz, mul_zero, sub_zero])
        have hex : ∃ c', (∀ i, ck i = true → c' i = true) ∧ posVal c' = j' := by
          by_contra hno
          exact hcp (cellPoly_coeff_eq_zero ck j'
            (fun c' hup heq => hno ⟨c', hup, heq⟩))
        obtain ⟨c', hup, hpv⟩ := hex
        have hcne : ck ≠ c' := by
          intro heq
          rw [← heq] at hpv
          apply hjk
          rw [← hpv, hckpos]
        have hlt : posVal ck < posVal c' := posVal_lt_of_lt hup hcne
        have hblk : 2 ^ P.m - 2 ^ P.a ≤ posVal c' :=
          IsBlockPos.mono P hup hckblock
        have hbound := posVal_lt_two_pow c'
        exact ⟨⟨by omega, by omega⟩, by omega⟩
    have hn' : ∀ j' ∈ h'.support, 2 ^ P.m - j' ≤ n := by
      intro j' hj'
      have h1 := (hsupp' j' hj').2
      have h2 := hn k hkmem
      omega
    obtain ⟨v', hv'block, hv'sum⟩ :=
      ih h' (fun j' hj' => (hsupp' j' hj').1) hn'
    refine ⟨v' + fun c => if c = ck then h.coeff k else 0, ?_, ?_⟩
    · intro c hc
      by_cases hcc : c = ck
      · rw [hcc]
        exact hckblock
      · refine hv'block c ?_
        intro hz
        apply hc
        simp [Pi.add_apply, hz, hcc]
    · have hsplit : ∑ c, ((v' + fun c => if c = ck then h.coeff k else 0) c) •
          cellPoly (R := R) c =
          (∑ c, v' c • cellPoly (R := R) c) +
          ∑ c, (if c = ck then h.coeff k else 0) • cellPoly (R := R) c := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Pi.add_apply, add_smul]
      have hper : ∀ c : Cube P.m,
          (if c = ck then h.coeff k else 0) • cellPoly (R := R) c =
          if c = ck then h.coeff k • cellPoly (R := R) c else 0 := by
        intro c
        split_ifs <;> simp
      have hsingle : ∑ c, (if c = ck then h.coeff k else 0) •
          cellPoly (R := R) c = h.coeff k • cellPoly (R := R) ck := by
        rw [Finset.sum_congr rfl fun c _ => hper c,
          Finset.sum_ite_eq' Finset.univ ck
            (fun c => h.coeff k • cellPoly (R := R) c),
          if_pos (Finset.mem_univ _)]
      rw [hsplit, hv'sum, hsingle, hh']
      ring

/-- **The block solver** (`prop:uniform`, Stage B): every polynomial
supported on the top degree window `[2^m − 2^a, 2^m)` is realized by a
block-supported assignment of position cells. -/
theorem exists_block_table (h : Polynomial R)
    (hsupp : ∀ k ∈ h.support, 2 ^ P.m - 2 ^ P.a ≤ k ∧ k < 2 ^ P.m) :
    ∃ v : Cube P.m → R, (∀ c, v c ≠ 0 → IsBlockPos P c) ∧
      ∑ c, v c • cellPoly (R := R) c = h :=
  exists_block_table_aux P (2 ^ P.m) h hsupp fun _ _ => Nat.sub_le _ _

end BlockSolve

/-! ## Per-class block interpolation (`lem:kersurj`, block stage)

Combining the block solver with the CRT interpolant: a block-supported fiber
realizes arbitrary prescribed evaluations at the (nonzero, distinct) queried
points and arbitrary prescribed values at the (non-conjugate, generating)
nodes, within the mask budget `t + d·e ≤ 2^a`. -/

section BlockFiber

variable (Fq : Type*) [Field Fq] [Algebra (Fp P) Fq]
  [FiniteDimensional (Fp P) Fq]

open Polynomial

/-- The multilinear extension of a lifted fiber at a `pow`-point is the
evaluation of its cell polynomial. -/
theorem mle_lift_eq_aeval (v : Cube P.m → Fp P) (x' : Fq) :
    mle (fun c => algebraMap (Fp P) Fq (v c)) (powSeq x' P.m) =
      aeval x' (∑ c, v c • cellPoly (R := Fp P) c) := by
  rw [map_sum]
  unfold mle
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [map_smul, aeval_cellPoly, Algebra.smul_def]
  ring

/-- **Per-class block interpolation**: within the budget `t + d·e ≤ 2^a`, a
block-supported fiber takes arbitrary prescribed values at distinct nonzero
queried points of `F_p` and at pairwise non-conjugate generating nodes of
`F_q`. -/
theorem exists_block_fiber {t e : ℕ} (x : Fin t → Fp P) (ν : Fin e → Fq)
    (hx : Function.Injective x) (hx0 : ∀ i, x i ≠ 0)
    (hν : ∀ j, ν j ∉ Set.range (algebraMap (Fp P) Fq))
    (hgen : ∀ j, (minpoly (Fp P) (ν j)).natDegree = Module.finrank (Fp P) Fq)
    (hconj : ∀ j j', j ≠ j' → minpoly (Fp P) (ν j) ≠ minpoly (Fp P) (ν j'))
    (hbudget : t + Module.finrank (Fp P) Fq * e ≤ 2 ^ P.a)
    (a : Fin t → Fp P) (b : Fin e → Fq) :
    ∃ v : Cube P.m → Fp P, (∀ c, v c ≠ 0 → IsBlockPos P c) ∧
      (∀ i, mle (fun c => algebraMap (Fp P) Fq (v c))
          (powSeq (algebraMap (Fp P) Fq (x i)) P.m) =
        algebraMap (Fp P) Fq (a i)) ∧
      (∀ j, mle (fun c => algebraMap (Fp P) Fq (v c)) (powSeq (ν j) P.m) =
        b j) := by
  classical
  have hν0 : ∀ j, ν j ≠ 0 := fun j h0 => hν j ⟨0, by rw [map_zero, h0]⟩
  obtain ⟨g, hgdeg, hgpts, hgnodes⟩ := exists_interpolant x ν hx hν hgen hconj
    (Nat.two_pow_pos P.a) hbudget
    (fun i => a i / x i ^ (2 ^ P.m - 2 ^ P.a))
    (fun j => b j / ν j ^ (2 ^ P.m - 2 ^ P.a))
  have hsupp : ∀ k ∈ (X ^ (2 ^ P.m - 2 ^ P.a) * g).support,
      2 ^ P.m - 2 ^ P.a ≤ k ∧ k < 2 ^ P.m := by
    intro k hk
    constructor
    · by_contra hlt
      have hdvd : (X : Polynomial (Fp P)) ^ (2 ^ P.m - 2 ^ P.a) ∣
          X ^ (2 ^ P.m - 2 ^ P.a) * g := dvd_mul_right _ _
      exact Polynomial.mem_support_iff.mp hk
        (Polynomial.X_pow_dvd_iff.mp hdvd k (by omega))
    · have h1 : k ≤ (X ^ (2 ^ P.m - 2 ^ P.a) * g).natDegree :=
        Polynomial.le_natDegree_of_mem_supp k hk
      have h2 : (X ^ (2 ^ P.m - 2 ^ P.a) * g).natDegree ≤
          (2 ^ P.m - 2 ^ P.a) + g.natDegree := by
        refine Polynomial.natDegree_mul_le.trans ?_
        rw [Polynomial.natDegree_X_pow]
      have hpow : 2 ^ P.a ≤ 2 ^ P.m :=
        Nat.pow_le_pow_right (by norm_num) P.a_le_m
      omega
  obtain ⟨v, hvblock, hvsum⟩ :=
    exists_block_table P (X ^ (2 ^ P.m - 2 ^ P.a) * g) hsupp
  refine ⟨v, hvblock, ?_, ?_⟩
  · intro i
    rw [mle_lift_eq_aeval P Fq v _, hvsum, map_mul, map_pow,
      Polynomial.aeval_X, Polynomial.aeval_def, Polynomial.eval₂_at_apply,
      hgpts i, ← map_pow, ← map_mul,
      mul_comm (x i ^ (2 ^ P.m - 2 ^ P.a)),
      div_mul_cancel₀ (a i) (pow_ne_zero _ (hx0 i))]
  · intro j
    rw [mle_lift_eq_aeval P Fq v _, hvsum, map_mul, map_pow,
      Polynomial.aeval_X, hgnodes j,
      mul_comm (ν j ^ (2 ^ P.m - 2 ^ P.a)),
      div_mul_cancel₀ (b j) (pow_ne_zero _ (hν0 j))]

end BlockFiber

end ZkWhir
