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

/-- **`eqPoly` commutes with any ring hom** (componentwise): `êq(φ∘x, c) = φ(êq(x,c))`.
Generalises `eqPoly_algebraMap`. With `φ = frobenius` this expresses the Frobenius
power of an eqPoly weight as the eqPoly weight at the conjugate point — the identity
that turns the trace of a channel weight into a sum over conjugate eqPoly weights
(`lem:noother` zf/node Fp-independence). -/
theorem eqPoly_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {j : ℕ} (x : Fin j → R) (c : Cube j) :
    eqPoly (fun i => φ (x i)) c = φ (eqPoly x c) := by
  unfold eqPoly
  rw [map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hc : c i <;> simp [hc]

/-- **The eqPoly weight at a `φ`-conjugate point** (`lem:noother` Frobenius
expansion): for a ring endomorphism `φ` (e.g. Frobenius `x ↦ x^p`), the eqPoly weight
at the conjugate `pow`-point `pow(φ z)` is `φ` applied to the eqPoly weight at
`pow(z)`. With `φ = frobenius^i`, `êq(pow(z^{p^i}), c) = (êq(pow z, c))^{p^i}` — so the
Frobenius powers of a channel weight are eqPoly weights at the conjugate points, the
input to expanding `tr(M·W) = ∑ᵢ M^{p^i}·êq(pow(z^{p^i}),·)`. -/
theorem eqPoly_powSeq_map {R : Type*} [CommRing R] (φ : R →+* R) {j : ℕ} (z : R)
    (c : Cube j) :
    eqPoly (powSeq (φ z) j) c = φ (eqPoly (powSeq z j) c) := by
  rw [show powSeq (φ z) j = fun k => φ (powSeq z j k) from by
    funext k; simp [powSeq, map_pow], eqPoly_map]

/-- **Trace of a channel weight is a sum over conjugate eqPoly weights** (`lem:noother`
linchpin): for a Galois extension `Fq/Fp`, `algebraMap (tr(M·êq(pow z, c))) = ∑_σ
σ(M)·êq(pow(σ z), c)` over the Galois group. Combines `trace_eq_sum_automorphisms`
(`algebraMap(tr x) = ∑_σ σ x`) with `eqPoly_powSeq_map` (`σ(êq(pow z,c)) = êq(pow(σ z),c)`).
So a vanishing channel-trace combination becomes a vanishing combination of eqPoly
weights at the *conjugate* points `σ z` — which the block independence then kills. -/
theorem trace_mul_eqPoly_powSeq {Fp Fq : Type*} [Field Fp] [Field Fq] [Algebra Fp Fq]
    [FiniteDimensional Fp Fq] [IsGalois Fp Fq] {j : ℕ} (M z : Fq) (c : Cube j) :
    algebraMap Fp Fq (Algebra.trace Fp Fq (M * eqPoly (powSeq z j) c))
      = ∑ σ : Fq ≃ₐ[Fp] Fq, σ M * eqPoly (powSeq (σ z) j) c := by
  rw [trace_eq_sum_automorphisms]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul]
  congr 1
  have h := eqPoly_powSeq_map (σ : Fq →+* Fq) z c
  simpa using h.symm

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

/-- **Boolean-cube sum factorizes** (general ring): a sum over the cube of a
coordinatewise product equals the product of per-coordinate two-term sums. -/
theorem sum_cube_prod_gen {R : Type*} [CommRing R] {n : ℕ} (f : Fin n → Bool → R) :
    ∑ s : Cube n, ∏ i, f i (s i) = ∏ i, (f i false + f i true) := by
  classical
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  exact Finset.prod_congr rfl fun i _ => by rw [Fintype.sum_bool]; ring

/-- **Block-filtered cube sum factorizes** (general ring): summing a coordinatewise
product over the affine sub-cube "every coordinate `i ≥ a` is `true`" forces the high
coordinates (`i ≥ a`) to contribute only their `true` value, while the low ones
(`i < a`) still contribute both. This is the block analogue of `sum_cube_prod_gen`,
the factorization underlying the block-restricted eqPoly moment. -/
theorem sum_blockFilter_prod {R : Type*} [CommRing R] {m a : ℕ} (f : Fin m → Bool → R) :
    (∑ c ∈ Finset.univ.filter (fun c : Cube m => ∀ i : Fin m, a ≤ (i : ℕ) → c i = true),
        ∏ i, f i (c i))
      = ∏ i : Fin m, (if a ≤ (i : ℕ) then f i true else f i false + f i true) := by
  classical
  have hset : Finset.univ.filter (fun c : Cube m => ∀ i : Fin m, a ≤ (i : ℕ) → c i = true)
      = Fintype.piFinset (fun i : Fin m =>
          if a ≤ (i : ℕ) then ({true} : Finset Bool) else Finset.univ) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hc i
      by_cases hi : a ≤ (i : ℕ)
      · rw [if_pos hi]; simp [hc i hi]
      · rw [if_neg hi]; exact Finset.mem_univ _
    · intro hc i hi
      have h := hc i
      rw [if_pos hi] at h
      simpa using h
  rw [hset, ← Finset.prod_univ_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : a ≤ (i : ℕ)
  · rw [if_pos hi, if_pos hi, Finset.sum_singleton]
  · rw [if_neg hi, if_neg hi, Fintype.sum_bool]; ring

/-- **High-bit geometric sum**: `∑_{i ≥ a} 2^i = 2^m − 2^a` over `Fin m` (`a ≤ m`).
The exponent the block scaling `∏_{i≥a} pow(z)_i = z^{2^m−2^a}` collapses to. -/
theorem sum_high_two_pow {m a : ℕ} (ham : a ≤ m) :
    ∑ i ∈ Finset.univ.filter (fun i : Fin m => a ≤ (i : ℕ)), 2 ^ (i : ℕ) = 2 ^ m - 2 ^ a := by
  classical
  have htot : ∑ i : Fin m, 2 ^ (i : ℕ) = 2 ^ m - 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => 2 ^ i) m, sum_range_two_pow]
  have hlow : ∑ i ∈ Finset.univ.filter (fun i : Fin m => ¬ a ≤ (i : ℕ)), 2 ^ (i : ℕ)
      = 2 ^ a - 1 := by
    rw [show (Finset.univ.filter (fun i : Fin m => ¬ a ≤ (i : ℕ)))
        = Finset.univ.filter (fun i : Fin m => (i : ℕ) < a) from
      Finset.filter_congr fun i _ => by simp [not_le],
      Finset.sum_filter, Fin.sum_univ_eq_sum_range (fun i => if i < a then 2 ^ i else 0) m,
      ← Finset.sum_filter,
      show (Finset.range m).filter (fun i => i < a) = Finset.range a from by
        ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega]
    exact sum_range_two_pow a
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun i : Fin m => a ≤ (i : ℕ)) (fun i => 2 ^ (i : ℕ))
  have h2 : 2 ^ a ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) ham
  have h3 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  rw [htot, hlow] at hsplit
  omega

/-- **The block-restricted subset-moment** (`lem:noother`, block form): over the
block (high bits `≥ a` fixed true) and for a low subset `T ⊆ {i < a}`, the `T`-moment
of `êq(pow(z,·))` is the scaled monomial `z^{2^m−2^a}·z^{n(T)}`. The scaling
`z^{2^m−2^a}` is the fixed high-bit contribution; the residual `z^{n(T)}` is the
free low-cube moment. So on the block the eqPoly weights are a *shifted* Vandermonde
system in `z`. -/
theorem sum_block_eqPoly_powSeq_mul_subsetIndicator {m a : ℕ} (ham : a ≤ m)
    {R : Type*} [CommRing R] (z : R) (T : Finset (Fin m)) (hT : ∀ i ∈ T, (i : ℕ) < a) :
    (∑ c ∈ Finset.univ.filter (fun c : Cube m => ∀ i : Fin m, a ≤ (i : ℕ) → c i = true),
        eqPoly (powSeq z m) c * ∏ i ∈ T, (if c i then (1 : R) else 0))
      = z ^ (2 ^ m - 2 ^ a) * z ^ (∑ i ∈ T, 2 ^ (i : ℕ)) := by
  classical
  have hsummand : ∀ c : Cube m,
      eqPoly (powSeq z m) c * ∏ i ∈ T, (if c i then (1 : R) else 0)
        = ∏ i, ((if c i then powSeq z m i else 1 - powSeq z m i) *
            (if i ∈ T then (if c i then (1 : R) else 0) else 1)) := by
    intro c
    unfold eqPoly
    rw [show (∏ i ∈ T, (if c i then (1 : R) else 0))
        = ∏ i, (if i ∈ T then (if c i then (1 : R) else 0) else 1) from by
      rw [Finset.prod_ite_mem, Finset.univ_inter], ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl (fun c _ => hsummand c),
    sum_blockFilter_prod (fun i b => (if b then powSeq z m i else 1 - powSeq z m i) *
      (if i ∈ T then (if b then (1 : R) else 0) else 1))]
  rw [show (∏ i : Fin m, (if a ≤ (i : ℕ)
        then ((if (true : Bool) then powSeq z m i else 1 - powSeq z m i) *
              (if i ∈ T then (if (true : Bool) then (1 : R) else 0) else 1))
        else (((if (false : Bool) then powSeq z m i else 1 - powSeq z m i) *
              (if i ∈ T then (if (false : Bool) then (1 : R) else 0) else 1))
            + ((if (true : Bool) then powSeq z m i else 1 - powSeq z m i) *
              (if i ∈ T then (if (true : Bool) then (1 : R) else 0) else 1)))))
      = ∏ i : Fin m, (if (a ≤ (i : ℕ) ∨ i ∈ T) then powSeq z m i else 1) from by
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hai : a ≤ (i : ℕ)
    · have hiT : i ∉ T := fun h => absurd (hT i h) (by omega)
      simp [hai, hiT]
    · by_cases hiT : i ∈ T <;> simp [hai, hiT] <;> try ring]
  rw [← Finset.prod_filter]
  simp only [powSeq]
  rw [Finset.prod_pow_eq_pow_sum, ← pow_add]
  congr 1
  rw [show Finset.univ.filter (fun i : Fin m => a ≤ (i : ℕ) ∨ i ∈ T)
      = (Finset.univ.filter (fun i : Fin m => a ≤ (i : ℕ))) ∪ T from by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]]
  rw [Finset.sum_union (by
    rw [Finset.disjoint_left]
    intro i hi hiT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact absurd (hT i hiT) (by omega)), sum_high_two_pow ham]

/-- **The subset-moment of an eqPoly weight is a monomial** (`lem:noother`
Vandermonde core): pairing the weight `c ↦ êq(x, c)` against the subset indicator
`∏_{i∈T} c_i` yields `∏_{i∈T} x_i`. Equivalently the multilinear extension of the
AND-monomial `∏_{i∈T} c_i` evaluated at `x` is `∏_{i∈T} x_i`. Specialised at the
`pow`-point `x = pow(z, m)` this gives the moment `z^{n(T)}` (`n(T) = ∑_{i∈T} 2^i`),
so the moment vector of `êq(pow(z_t,·))` is the Vandermonde row `(z_t^k)_k` — whence
distinct points give linearly independent queried weights. -/
theorem sum_eqPoly_mul_subsetIndicator {R : Type*} [CommRing R] {j : ℕ}
    (x : Fin j → R) (T : Finset (Fin j)) :
    (∑ c : Cube j, eqPoly x c * ∏ i ∈ T, (if c i then (1 : R) else 0)) = ∏ i ∈ T, x i := by
  classical
  have hsummand : ∀ c : Cube j,
      eqPoly x c * ∏ i ∈ T, (if c i then (1 : R) else 0)
        = ∏ i, ((if c i then x i else 1 - x i) *
            (if i ∈ T then (if c i then (1 : R) else 0) else 1)) := by
    intro c
    unfold eqPoly
    rw [show (∏ i ∈ T, (if c i then (1 : R) else 0))
        = ∏ i, (if i ∈ T then (if c i then (1 : R) else 0) else 1) from by
      rw [Finset.prod_ite_mem, Finset.univ_inter], ← Finset.prod_mul_distrib]
  calc (∑ c : Cube j, eqPoly x c * ∏ i ∈ T, (if c i then (1 : R) else 0))
      = ∑ c : Cube j, ∏ i, ((if c i then x i else 1 - x i) *
          (if i ∈ T then (if c i then (1 : R) else 0) else 1)) :=
        Finset.sum_congr rfl (fun c _ => hsummand c)
    _ = ∏ i, (((if (false : Bool) then x i else 1 - x i) *
            (if i ∈ T then (if (false : Bool) then (1 : R) else 0) else 1))
          + ((if (true : Bool) then x i else 1 - x i) *
            (if i ∈ T then (if (true : Bool) then (1 : R) else 0) else 1))) :=
        sum_cube_prod_gen (fun i b => (if b then x i else 1 - x i) *
          (if i ∈ T then (if b then (1 : R) else 0) else 1))
    _ = ∏ i, (if i ∈ T then x i else 1) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        by_cases hi : i ∈ T <;> simp [hi] <;> try ring
    _ = ∏ i ∈ T, x i := by rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- **The subset-moment at a `pow`-point is `z^{n(T)}`** (`lem:noother` Vandermonde
row): specialising `sum_eqPoly_mul_subsetIndicator` to `x = pow(z, m)` turns the
`T`-moment of `êq(pow(z,·))` into the single power `z^{∑_{i∈T} 2^i}`. As `T` ranges
over all subsets of `Fin m`, the exponent `∑_{i∈T} 2^i` ranges bijectively over
`{0,…,2^m−1}`, so the moment vector of `êq(pow(z,·))` is the Vandermonde row
`(z^k)_{k<2^m}` — the bridge to the Vandermonde nonvanishing for distinct nodes. -/
theorem sum_eqPoly_powSeq_mul_subsetIndicator {R : Type*} [CommRing R] {m : ℕ}
    (z : R) (T : Finset (Fin m)) :
    (∑ c : Cube m, eqPoly (powSeq z m) c * ∏ i ∈ T, (if c i then (1 : R) else 0))
      = z ^ (∑ i ∈ T, 2 ^ (i : ℕ)) := by
  rw [sum_eqPoly_mul_subsetIndicator]
  simp only [powSeq, Finset.prod_pow_eq_pow_sum]

/-- **Vandermonde nonvanishing** (`lem:noother` independence engine): if a weighted
power sum `∑_t a_t·z_t^k` vanishes for every exponent `k < #ι` and the points `z_t`
are distinct, then all weights `a_t` vanish. Proved by Lagrange interpolation: each
`a_s = ∑_t a_t·basis_s(z_t)` (since `basis_s(z_t) = δ_{s,t}`), and expanding the
degree-`<#ι` polynomial `basis_s` in monomials turns this into `∑_k coeff_k·(power
sum)_k = 0`. This is the converse that makes the eqPoly moment vectors a genuine
basis change. -/
theorem vandermonde_coeffs_zero {F : Type*} [Field F] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (z : ι → F) (hz : Function.Injective z) (a : ι → F)
    (h : ∀ k : ℕ, k < Fintype.card ι → ∑ t, a t * z t ^ k = 0) :
    a = 0 := by
  funext s
  show a s = 0
  have hinj : Set.InjOn z (Finset.univ : Finset ι) := hz.injOn
  have hcard : (Lagrange.basis Finset.univ z s).natDegree = Fintype.card ι - 1 := by
    rw [Lagrange.natDegree_basis hinj (Finset.mem_univ s), Finset.card_univ]
  have hbasis : (∑ t, a t * (Lagrange.basis Finset.univ z s).eval (z t))
      = a s * (Lagrange.basis Finset.univ z s).eval (z s) :=
    Finset.sum_eq_single_of_mem s (Finset.mem_univ s) (fun t _ hts => by
      rw [Lagrange.eval_basis_of_ne (Ne.symm hts) (Finset.mem_univ t), mul_zero])
  rw [Lagrange.eval_basis_self hinj (Finset.mem_univ s), mul_one] at hbasis
  rw [← hbasis]
  simp_rw [Polynomial.eval_eq_sum_range, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [show (∑ t, a t * ((Lagrange.basis Finset.univ z s).coeff k * z t ^ k))
      = (Lagrange.basis Finset.univ z s).coeff k * ∑ t, a t * z t ^ k from by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun t _ => by ring]
  have hkc : k < Fintype.card ι := by
    rw [Finset.mem_range, hcard] at hk
    have hpos : 0 < Fintype.card ι := Fintype.card_pos (h := ⟨s⟩)
    omega
  rw [h k hkc, mul_zero]

/-- **Every exponent below `2^m` is a subset-sum** (`lem:noother` exponent
surjectivity): for `k < 2^m` there is a subset `T ⊆ Fin m` with `∑_{i∈T} 2^i = k`
(binary representation). So the exponents `n(T)` of the eqPoly moments range over
all of `{0,…,2^m−1}`, giving every Vandermonde row `(z^k)_{k<2^m}` and hence the
full Vandermonde system once `#ι ≤ 2^m`. -/
theorem exists_subset_sum_two_pow {m k : ℕ} (hk : k < 2 ^ m) :
    ∃ T : Finset (Fin m), ∑ i ∈ T, 2 ^ (i : ℕ) = k := by
  classical
  refine ⟨Finset.univ.filter (fun i : Fin m => k.testBit i), ?_⟩
  rw [Finset.sum_filter,
    Fin.sum_univ_eq_sum_range (fun j => if k.testBit j then 2 ^ j else 0) m,
    ← Finset.sum_filter]
  have hset : (Finset.range m).filter (fun j => k.testBit j) = k.bitIndices.toFinset := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, List.mem_toFinset, Nat.mem_bitIndices]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      by_contra hjm
      push_neg at hjm
      have hf : k.testBit j = false :=
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hk (Nat.pow_le_pow_right (by norm_num) hjm))
      simp [hf] at h
  rw [hset, List.sum_toFinset _ Nat.bitIndices_nodup]
  exact Nat.sum_map_two_pow_bitIndices k

/-- **Low-bit binary representation**: for `k < 2^a` (with `a ≤ m`) there is a subset
`T ⊆ Fin m` supported on the low coordinates (`i < a`) with `∑_{i∈T} 2^i = k`. The
exponent surjectivity over the low cube the block-restricted Vandermonde consumes. -/
theorem exists_low_subset_sum_two_pow {m a : ℕ} (ham : a ≤ m) {k : ℕ} (hk : k < 2 ^ a) :
    ∃ T : Finset (Fin m), (∀ i ∈ T, (i : ℕ) < a) ∧ ∑ i ∈ T, 2 ^ (i : ℕ) = k := by
  obtain ⟨T', hT'⟩ := exists_subset_sum_two_pow (m := a) (k := k) hk
  refine ⟨T'.map (Fin.castLEEmb ham), ?_, ?_⟩
  · intro i hi
    rw [Finset.mem_map] at hi
    obtain ⟨i', _, rfl⟩ := hi
    simpa using i'.isLt
  · rw [Finset.sum_map]
    simpa using hT'

/-- **The `pow`-point eqPoly weights are linearly independent** (`lem:noother`,
full-cube form): if the nodes `z_t` are distinct and there are at most `2^m` of
them, then the weight functions `c ↦ êq(pow(z_t,·), c)` on `Cube m` are linearly
independent — a vanishing `F`-combination forces all coefficients to vanish.
Assembled from the moment identity (`sum_eqPoly_powSeq_mul_subsetIndicator`), the
exponent surjectivity (`exists_subset_sum_two_pow`) and the Vandermonde engine
(`vandermonde_coeffs_zero`): the `T`-moment of the vanishing combination is exactly
the power sum `∑_t a_t·z_t^{n(T)}`, which therefore vanishes for every `k = n(T) <
2^m`, so all `a_t = 0`. This is the channel-independence that makes the confine
slice-coefficients unique (hence `Fp`-linear) and so extractable by the
trace-duality tools. -/
theorem eqPoly_powSeq_linearIndependent {F : Type*} [Field F] {m : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (z : ι → F) (hz : Function.Injective z)
    (hcard : Fintype.card ι ≤ 2 ^ m) (a : ι → F)
    (hsum : ∀ c : Cube m, ∑ t, a t * eqPoly (powSeq (z t) m) c = 0) :
    a = 0 := by
  refine vandermonde_coeffs_zero z hz a (fun k hk => ?_)
  obtain ⟨T, hT⟩ := exists_subset_sum_two_pow (m := m) (k := k) (lt_of_lt_of_le hk hcard)
  have hmom : ∀ t, z t ^ k
      = ∑ c : Cube m, eqPoly (powSeq (z t) m) c * ∏ i ∈ T, (if c i then (1 : F) else 0) := by
    intro t; rw [sum_eqPoly_powSeq_mul_subsetIndicator, hT]
  calc ∑ t, a t * z t ^ k
      = ∑ t, ∑ c : Cube m,
          a t * (eqPoly (powSeq (z t) m) c * ∏ i ∈ T, (if c i then (1 : F) else 0)) := by
        refine Finset.sum_congr rfl fun t _ => ?_
        rw [hmom t, Finset.mul_sum]
    _ = ∑ c : Cube m, ∑ t,
          a t * (eqPoly (powSeq (z t) m) c * ∏ i ∈ T, (if c i then (1 : F) else 0)) :=
        Finset.sum_comm
    _ = ∑ c : Cube m, (∏ i ∈ T, (if c i then (1 : F) else 0)) *
          (∑ t, a t * eqPoly (powSeq (z t) m) c) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun t _ => by ring
    _ = 0 := Finset.sum_eq_zero fun c _ => by rw [hsum c, mul_zero]

/-- **The `pow`-point eqPoly weights are independent over the block** (`lem:noother`,
block form): if the nodes `z_t` are distinct, nonzero, and number at most `2^a`, then
the weight functions `c ↦ êq(pow(z_t,·), c)` *restricted to the block* (high bits
`≥ a` fixed true) are linearly independent. Proof: pairing a vanishing combination
against a low subset indicator `T` and using the block-restricted moment turns it
into the shifted power sum `∑_t (a_t·z_t^{2^m−2^a})·z_t^{n(T)} = 0` for all
`n(T) < 2^a`; Vandermonde forces `a_t·z_t^{2^m−2^a} = 0`, and `z_t ≠ 0` gives
`a_t = 0`. This is the independence over the affine sub-cube that `lem:confine` pins. -/
theorem eqPoly_powSeq_block_linearIndependent {F : Type*} [Field F] {m a : ℕ} (ham : a ≤ m)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (z : ι → F) (hz : Function.Injective z)
    (hz0 : ∀ t, z t ≠ 0) (hcard : Fintype.card ι ≤ 2 ^ a) (coef : ι → F)
    (hsum : ∀ c ∈ Finset.univ.filter (fun c : Cube m => ∀ i : Fin m, a ≤ (i : ℕ) → c i = true),
        ∑ t, coef t * eqPoly (powSeq (z t) m) c = 0) :
    coef = 0 := by
  have hb : (fun t => coef t * z t ^ (2 ^ m - 2 ^ a)) = 0 := by
    refine vandermonde_coeffs_zero z hz _ (fun k hk => ?_)
    obtain ⟨T, hTlow, hTk⟩ := exists_low_subset_sum_two_pow ham (lt_of_lt_of_le hk hcard)
    have hmom : ∀ t, (coef t * z t ^ (2 ^ m - 2 ^ a)) * z t ^ k
        = coef t * (∑ c ∈ Finset.univ.filter
            (fun c : Cube m => ∀ i : Fin m, a ≤ (i : ℕ) → c i = true),
            eqPoly (powSeq (z t) m) c * ∏ i ∈ T, (if c i then (1 : F) else 0)) := by
      intro t
      rw [sum_block_eqPoly_powSeq_mul_subsetIndicator ham (z t) T hTlow, hTk]; ring
    calc ∑ t, (coef t * z t ^ (2 ^ m - 2 ^ a)) * z t ^ k
        = ∑ t, ∑ c ∈ Finset.univ.filter
            (fun c : Cube m => ∀ i : Fin m, a ≤ (i : ℕ) → c i = true),
            coef t * (eqPoly (powSeq (z t) m) c * ∏ i ∈ T, (if c i then (1 : F) else 0)) := by
          refine Finset.sum_congr rfl fun t _ => ?_
          rw [hmom t, Finset.mul_sum]
      _ = ∑ c ∈ Finset.univ.filter
            (fun c : Cube m => ∀ i : Fin m, a ≤ (i : ℕ) → c i = true), ∑ t,
            coef t * (eqPoly (powSeq (z t) m) c * ∏ i ∈ T, (if c i then (1 : F) else 0)) :=
          Finset.sum_comm
      _ = ∑ c ∈ Finset.univ.filter
            (fun c : Cube m => ∀ i : Fin m, a ≤ (i : ℕ) → c i = true),
            (∏ i ∈ T, (if c i then (1 : F) else 0)) *
              (∑ t, coef t * eqPoly (powSeq (z t) m) c) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun t _ => by ring
      _ = 0 := Finset.sum_eq_zero fun c hc => by rw [hsum c hc, mul_zero]
  funext t
  have ht := congrFun hb t
  simp only [Pi.zero_apply] at ht
  rcases mul_eq_zero.mp ht with h | h
  · exact h
  · exact absurd h (pow_ne_zero _ (hz0 t))

/-- **Channel-weight Fp-independence over the block** (`lem:noother`, per weight): if
the conjugates `{σ z : σ ∈ Gal(Fq/Fp)}` are distinct and `z ≠ 0` and there are at most
`2^a` of them, then `tr(M·êq(pow z, c)) = 0` for all block cells `c` forces `M = 0`.
Proof: `trace_mul_eqPoly_powSeq` rewrites the (algebraMap of the) vanishing trace as
`∑_σ σ(M)·êq(pow(σz),c) = 0` over the block; the conjugate points `σz` are distinct +
nonzero, so `eqPoly_powSeq_block_linearIndependent` forces every `σ(M)=0`, in particular
`M = (1)·M = 0`. This is the trace/basis blowup that makes the confine node/zf slice
coefficients unique — resolving the apparent γ=1 obstruction via the Galois conjugates. -/
theorem trace_weight_block_indep {Fp Fq : Type*} [Field Fp] [Field Fq] [Algebra Fp Fq]
    [FiniteDimensional Fp Fq] [IsGalois Fp Fq] {m a : ℕ} (ham : a ≤ m) (M z : Fq) (hz0 : z ≠ 0)
    (hconj : Function.Injective (fun σ : Fq ≃ₐ[Fp] Fq => σ z))
    (hcard : Fintype.card (Fq ≃ₐ[Fp] Fq) ≤ 2 ^ a)
    (hM : ∀ c ∈ Finset.univ.filter (fun c : Cube m => ∀ i : Fin m, a ≤ (i : ℕ) → c i = true),
        Algebra.trace Fp Fq (M * eqPoly (powSeq z m) c) = 0) :
    M = 0 := by
  classical
  have key : ∀ c ∈ Finset.univ.filter (fun c : Cube m => ∀ i : Fin m, a ≤ (i : ℕ) → c i = true),
      ∑ σ : Fq ≃ₐ[Fp] Fq, σ M * eqPoly (powSeq (σ z) m) c = 0 := by
    intro c hc
    rw [← trace_mul_eqPoly_powSeq M z c, hM c hc, map_zero]
  have hcoef := eqPoly_powSeq_block_linearIndependent ham (fun σ : Fq ≃ₐ[Fp] Fq => σ z)
    hconj (fun σ => by simpa using hz0) hcard (fun σ => σ M) key
  have h1 := congrFun hcoef 1
  simpa using h1

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

/-- **Binary-power Schwartz–Zippel bridge.** The binary-power substitution
`z ↦ mle T (powSeq z j)` is the evaluation at `z` of the cell-polynomial
combination `∑ b, T b • cellPoly b`. Combined with `cellPoly_combo_ne_zero`
and `cellPoly_combo_natDegree_lt` this realizes `mle T (powSeq ·)` as a
nonzero univariate polynomial of degree `< 2^j`. -/
theorem mle_powSeq_eq_aeval (T : Cube j → R) (z : R) :
    mle T (powSeq z j) = aeval z (∑ b : Cube j, T b • cellPoly (R := R) b) := by
  rw [map_sum]
  unfold mle
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, aeval_cellPoly, smul_eq_mul]
  ring

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
