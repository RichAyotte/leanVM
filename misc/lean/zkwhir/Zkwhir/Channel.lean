/-
The channel decomposition of the round-0 sumcheck messages (`eq:channel` of
`zk_leanVM.tex`): at every level `ℓ` and every evaluation point `y`, the
message polynomial splits as

  ĥ_ℓ(y) = P¹_ℓ(y)·f̂₀(mixed point of z₁) + γ·P²_ℓ(y)·f̂₀(mixed point of z₂)
           + γ²·(cross term against ŵ),

where the mixed point carries the sumcheck challenges below `ℓ`, the value `y`
at `ℓ`, and the `pow`-coordinates of the out-of-domain point above `ℓ`, and
`P^j_ℓ(y) = ∏_{i<ℓ} eqf(α_i, z_j^{2^i}) · eqf(y, z_j^{2^ℓ})` is a scalar
prefix factor. Combined with `hPoly_eq_zero_of_invisible` this yields the
`(ℓ, y)`-family of channel identities satisfied by every view-invisible
perturbation — the engine of `lem:fullslice`.

Part of the `GoodSetAbsorption` formalization campaign.
-/
import Mathlib
import Zkwhir.Statement
import Zkwhir.Sumcheck

set_option linter.style.header false
set_option linter.unusedSectionVars false

noncomputable section

namespace ZkWhir

variable (P : Params) (Fq : Type*) [Field Fq] [Fintype Fq]
  [Algebra (Fp P) Fq] (Dom : Finset (Fp P)) [Nonempty {x // x ∈ Dom}]

variable (S : Stmt P Fq) (T : Cell P → Fp P) (ch : Challenges P Fq Dom)

/-- The two-point equality kernel `eqf(x, y) = xy + (1−x)(1−y)`: the bilinear
extension of `êq` to a pair of field points. -/
def eqf (x y : Fq) : Fq := x * y + (1 - x) * (1 - y)

/-- `eqf` is affine of degree one in its first argument:
`eqf(x, y) = (2y − 1)·x + (1 − y)`. -/
theorem eqf_affine_left (x y : Fq) : eqf Fq x y = (2 * y - 1) * x + (1 - y) := by
  unfold eqf; ring

/-- `eqf` is affine of degree one in its second argument. -/
theorem eqf_affine_right (x y : Fq) : eqf Fq x y = (2 * x - 1) * y + (1 - x) := by
  unfold eqf; ring

/-- As a polynomial in its first argument, `eqf(·, y)` is nonzero (char ≠ 2):
its two coefficients `(1 − y, 2y − 1)` cannot both vanish. -/
theorem eqf_poly_left_ne_zero (h2 : (2 : Fq) ≠ 0) (y : Fq) :
    (Polynomial.C (1 - y) + Polynomial.C (2 * y - 1) * Polynomial.X :
      Polynomial Fq) ≠ 0 := by
  intro h
  have hco1 : (Polynomial.C (1 - y) +
      Polynomial.C (2 * y - 1) * Polynomial.X : Polynomial Fq).coeff 1 =
      2 * y - 1 := by
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_one,
      mul_one, Polynomial.coeff_C, if_neg (by decide : (1 : ℕ) ≠ 0), zero_add]
  have hco0 : (Polynomial.C (1 - y) +
      Polynomial.C (2 * y - 1) * Polynomial.X : Polynomial Fq).coeff 0 =
      1 - y := by
    rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_zero,
      mul_zero, add_zero, Polynomial.coeff_C, if_pos rfl]
  rw [h, Polynomial.coeff_zero] at hco1 hco0
  exact h2 (by linear_combination -2 * hco1 - 4 * hco0)

/-- `eqf(1, x) = x`. -/
theorem eqf_one (x : Fq) : eqf Fq 1 x = x := by unfold eqf; ring

/-- `eqf(2, x) = 3x − 1`. -/
theorem eqf_two (x : Fq) : eqf Fq 2 x = 3 * x - 1 := by unfold eqf; ring

/-- `eqf(x, y)` is the evaluation at `x` of its degree-≤1 polynomial. -/
theorem eqf_eq_eval (x y : Fq) :
    eqf Fq x y =
      Polynomial.eval x (Polynomial.C (1 - y) +
        Polynomial.C (2 * y - 1) * Polynomial.X) := by
  rw [eqf_affine_left, Polynomial.eval_add, Polynomial.eval_C,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  ring

/-- The `eqf` polynomial in its first argument has degree at most one. -/
theorem eqf_poly_natDegree (y : Fq) :
    (Polynomial.C (1 - y) + Polynomial.C (2 * y - 1) * Polynomial.X :
      Polynomial Fq).natDegree ≤ 1 := by
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · rw [Polynomial.natDegree_C]; exact Nat.zero_le 1
  · exact (Polynomial.natDegree_C_mul_le _ _).trans
      (le_of_eq Polynomial.natDegree_X)

/-- The class part of the round-`ℓ` *mixed point*: the sumcheck challenges
below `ℓ`, the evaluation point `y` at `ℓ`, the coordinates of `x` above. -/
def mixedPoint (ℓ : Fin P.k₀) (y : Fq) (x : Fin P.k₀ → Fq) : Fin P.k₀ → Fq :=
  fun i => if i < ℓ then ch.α i else if i = ℓ then y else x i

/-- The scalar prefix factor `P_ℓ(y)` of a channel with class point `x`:
`∏_{i<ℓ} eqf(α_i, x_i) · eqf(y, x_ℓ)`. -/
def prefixFactor (ℓ : Fin P.k₀) (y : Fq) (x : Fin P.k₀ → Fq) : Fq :=
  ∏ i, if i < ℓ then eqf Fq (ch.α i) (x i)
       else if i = ℓ then eqf Fq y (x i)
       else 1

/-- **Prefix-factor factorization**: `prefixFactor` splits into the product of
the lower `eqf(α_i, x_i)` factors and the slot factor `eqf(y, x_ℓ)`. Exposes
the `α`-prefix and the degree-one `eqf(y, ·)` factor for the `slotDet`
Schwartz–Zippel. -/
theorem prefixFactor_eq (ℓ : Fin P.k₀) (y : Fq) (x : Fin P.k₀ → Fq) :
    prefixFactor P Fq Dom ch ℓ y x =
      (∏ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < ℓ),
        eqf Fq (ch.α i) (x i)) * eqf Fq y (x ℓ) := by
  classical
  unfold prefixFactor
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i : Fin P.k₀ => i < ℓ)]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    rw [if_pos (Finset.mem_filter.mp hi).2]
  · rw [Finset.prod_eq_single ℓ
      (fun i hi hiℓ => by
        rw [if_neg (Finset.mem_filter.mp hi).2, if_neg hiℓ])
      (fun hℓ => absurd
        (Finset.mem_filter.mpr ⟨Finset.mem_univ ℓ, lt_irrefl ℓ⟩) hℓ)]
    rw [if_neg (lt_irrefl ℓ), if_pos rfl]

/-- The Lagrange prefactor of `partialEval`: the weight of the class `s` in
the round-`ℓ` partial evaluation at `X` with suffix `b`. -/
def preFac (ℓ : Fin P.k₀) (X : Fq) (s b : Cube P.k₀) : Fq :=
  ∏ i, if i < ℓ then (if s i then ch.α i else 1 - ch.α i)
       else if i = ℓ then (if s i then X else 1 - X)
       else (if s i = b i then 1 else 0)

/-- The `b`-dependent class factor of the partial evaluation of a tensor
channel with class point `x`. -/
def psiFac (x : Fin P.k₀ → Fq) (ℓ : Fin P.k₀) (X : Fq) (b : Cube P.k₀) : Fq :=
  ∏ i, if i < ℓ then eqf Fq (ch.α i) (x i)
       else if i = ℓ then eqf Fq X (x i)
       else (if b i then x i else 1 - x i)

/-- The cross channel: the component of `ĥ_ℓ` pairing the table against the
input weight `ŵ` (the `γ²`-part of `eq:channel`). -/
def crossTerm (ℓ : Fin P.k₀) (y : Fq) : Fq :=
  ∑ b ∈ Finset.univ.filter
      (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ, b i = false),
    ∑ c : Cube P.m,
      partialEval P Fq Dom ch (liftT P Fq T) ℓ y b c *
        partialEval P Fq Dom ch S.w ℓ y b c

theorem partialEval_eq (G : Cell P → Fq) (ℓ : Fin P.k₀) (X : Fq)
    (b : Cube P.k₀) (c : Cube P.m) :
    partialEval P Fq Dom ch G ℓ X b c =
      ∑ s : Cube P.k₀, preFac P Fq Dom ch ℓ X s b * G (s, c) := rfl

/-- The partial evaluation is `Fq`-homogeneous in the table. -/
theorem partialEval_smul (G : Cell P → Fq) (k : Fq) (ℓ : Fin P.k₀) (X : Fq)
    (b : Cube P.k₀) (c : Cube P.m) :
    partialEval P Fq Dom ch (k • G) ℓ X b c =
      k * partialEval P Fq Dom ch G ℓ X b c := by
  unfold partialEval
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- A sum of products over the cube is the product of per-coordinate sums. -/
theorem sum_cube_prod {n : ℕ} (f : Fin n → Bool → Fq) :
    ∑ s : Cube n, ∏ i, f i (s i) = ∏ i, (f i false + f i true) := by
  classical
  rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum]
  exact Finset.prod_congr rfl fun i _ => by rw [Fintype.sum_bool]; ring

/-- Filtered variant: over suffixes vanishing up to `ℓ`, the coordinates up
to `ℓ` contribute only their `false` value. -/
theorem sum_filter_prod (ℓ : Fin P.k₀) (f : Fin P.k₀ → Bool → Fq) :
    ∑ b ∈ Finset.univ.filter
        (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ, b i = false),
      ∏ i, f i (b i) =
      ∏ i, (if i ≤ ℓ then f i false else f i false + f i true) := by
  classical
  have hset : Finset.univ.filter
      (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ, b i = false) =
      Fintype.piFinset (fun i => if i ≤ ℓ then ({false} : Finset Bool)
        else Finset.univ) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Fintype.mem_piFinset, Finset.mem_Iic]
    constructor
    · intro hb i
      by_cases hi : i ≤ ℓ
      · rw [if_pos hi]
        simp [hb i hi]
      · rw [if_neg hi]
        exact Finset.mem_univ _
    · intro hb i hi
      have h := hb i
      rw [if_pos hi] at h
      simpa using h
  rw [hset, ← Finset.prod_univ_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ≤ ℓ
  · rw [if_pos hi, if_pos hi, Finset.sum_singleton]
  · rw [if_neg hi, if_neg hi, Fintype.sum_bool]
    ring

/-- The partial evaluation of a tensor channel `êq(x, ·) ⊗ w'` splits into
the `b`-dependent class factor and the position value. -/
theorem partialEval_tensor (x : Fin P.k₀ → Fq) (w' : Cube P.m → Fq)
    (ℓ : Fin P.k₀) (X : Fq) (b : Cube P.k₀) (c : Cube P.m) :
    partialEval P Fq Dom ch (fun u => eqPoly x u.1 * w' u.2) ℓ X b c =
      psiFac P Fq Dom ch x ℓ X b * w' c := by
  have hexp : partialEval P Fq Dom ch (fun u => eqPoly x u.1 * w' u.2) ℓ X b c =
      ∑ s : Cube P.k₀, preFac P Fq Dom ch ℓ X s b * (eqPoly x s * w' c) :=
    partialEval_eq P Fq Dom ch _ ℓ X b c
  rw [hexp]
  have hpull : ∑ s : Cube P.k₀,
      preFac P Fq Dom ch ℓ X s b * (eqPoly x s * w' c) =
      (∑ s : Cube P.k₀, preFac P Fq Dom ch ℓ X s b * eqPoly x s) * w' c := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hpull]
  congr 1
  refine (Finset.sum_congr rfl fun s _ => ?_).trans
    ((sum_cube_prod Fq (fun i bit =>
      (if i < ℓ then (if bit then ch.α i else 1 - ch.α i)
        else if i = ℓ then (if bit then X else 1 - X)
        else (if bit = b i then 1 else 0)) *
      (if bit then x i else 1 - x i))).trans ?_)
  · unfold preFac eqPoly
    rw [← Finset.prod_mul_distrib]
  · unfold psiFac
    refine Finset.prod_congr rfl fun i _ => ?_
    rcases lt_trichotomy i ℓ with h | h | h
    · simp only [if_pos h]
      simp [eqf]
      ring
    · subst h
      simp [eqf]
      ring
    · have h2 : ¬ i < ℓ := lt_asymm h
      have h3 : i ≠ ℓ := ne_of_gt h
      simp only [if_neg h2, if_neg h3]
      cases hbi : b i <;> simp

/-- The filtered suffix sum of the `partialEval` prefactors against the
tensor-channel factors collapses to the mixed-point Lagrange weight times the
prefix factor. -/
theorem presum_collapse (x : Fin P.k₀ → Fq) (ℓ : Fin P.k₀) (y : Fq)
    (s : Cube P.k₀) :
    ∑ b ∈ Finset.univ.filter
        (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ, b i = false),
      preFac P Fq Dom ch ℓ y s b * psiFac P Fq Dom ch x ℓ y b =
      eqPoly (mixedPoint P Fq Dom ch ℓ y x) s *
        prefixFactor P Fq Dom ch ℓ y x := by
  classical
  refine (Finset.sum_congr rfl fun b _ => ?_).trans
    ((sum_filter_prod P Fq ℓ (fun i bit =>
      (if i < ℓ then (if s i then ch.α i else 1 - ch.α i)
        else if i = ℓ then (if s i then y else 1 - y)
        else (if s i = bit then 1 else 0)) *
      (if i < ℓ then eqf Fq (ch.α i) (x i)
        else if i = ℓ then eqf Fq y (x i)
        else (if bit then x i else 1 - x i)))).trans ?_)
  · unfold preFac psiFac
    rw [← Finset.prod_mul_distrib]
  · unfold eqPoly mixedPoint prefixFactor
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rcases lt_trichotomy i ℓ with h | h | h
    · simp [h, le_of_lt h]
    · subst h
      simp
    · have h1 : ¬ i ≤ ℓ := not_le.mpr h
      have h2 : ¬ i < ℓ := lt_asymm h
      have h3 : i ≠ ℓ := ne_of_gt h
      simp only [if_neg h1, if_neg h2, if_neg h3]
      cases hsi : s i <;> simp

/-- **Channel collapse**: the filtered round-`ℓ` pairing of an arbitrary
table against a tensor channel equals the channel's prefix factor times the
table's mixed-point evaluation. -/
theorem channel_collapse (G : Cell P → Fq) (x : Fin P.k₀ → Fq)
    (w' : Cube P.m → Fq) (ℓ : Fin P.k₀) (y : Fq) :
    ∑ b ∈ Finset.univ.filter
        (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ, b i = false),
      ∑ c : Cube P.m,
        partialEval P Fq Dom ch G ℓ y b c *
          partialEval P Fq Dom ch (fun u => eqPoly x u.1 * w' u.2) ℓ y b c =
      prefixFactor P Fq Dom ch ℓ y x *
        ∑ s : Cube P.k₀, ∑ c : Cube P.m,
          eqPoly (mixedPoint P Fq Dom ch ℓ y x) s * w' c * G (s, c) := by
  classical
  have hsummand : ∀ (b : Cube P.k₀) (c : Cube P.m),
      partialEval P Fq Dom ch G ℓ y b c *
        partialEval P Fq Dom ch (fun u => eqPoly x u.1 * w' u.2) ℓ y b c =
      ∑ s : Cube P.k₀,
        (preFac P Fq Dom ch ℓ y s b * psiFac P Fq Dom ch x ℓ y b) *
          (w' c * G (s, c)) := by
    intro b c
    rw [partialEval_tensor P Fq Dom ch x w' ℓ y b c,
      partialEval_eq P Fq Dom ch G ℓ y b c, Finset.sum_mul]
    exact Finset.sum_congr rfl fun s _ => by ring
  calc ∑ b ∈ Finset.univ.filter
        (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ, b i = false),
      ∑ c : Cube P.m,
        partialEval P Fq Dom ch G ℓ y b c *
          partialEval P Fq Dom ch (fun u => eqPoly x u.1 * w' u.2) ℓ y b c
      = ∑ b ∈ Finset.univ.filter
            (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ, b i = false),
          ∑ c : Cube P.m, ∑ s : Cube P.k₀,
            (preFac P Fq Dom ch ℓ y s b * psiFac P Fq Dom ch x ℓ y b) *
              (w' c * G (s, c)) :=
        Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun c _ => hsummand b c
    _ = ∑ b ∈ Finset.univ.filter
            (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ, b i = false),
          ∑ s : Cube P.k₀, ∑ c : Cube P.m,
            (preFac P Fq Dom ch ℓ y s b * psiFac P Fq Dom ch x ℓ y b) *
              (w' c * G (s, c)) :=
        Finset.sum_congr rfl fun b _ => Finset.sum_comm
    _ = ∑ s : Cube P.k₀, ∑ b ∈ Finset.univ.filter
            (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ, b i = false),
          ∑ c : Cube P.m,
            (preFac P Fq Dom ch ℓ y s b * psiFac P Fq Dom ch x ℓ y b) *
              (w' c * G (s, c)) := Finset.sum_comm
    _ = ∑ s : Cube P.k₀,
          (∑ b ∈ Finset.univ.filter
              (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ, b i = false),
            preFac P Fq Dom ch ℓ y s b * psiFac P Fq Dom ch x ℓ y b) *
            (∑ c : Cube P.m, w' c * G (s, c)) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun b _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ s : Cube P.k₀,
          (eqPoly (mixedPoint P Fq Dom ch ℓ y x) s *
              prefixFactor P Fq Dom ch ℓ y x) *
            (∑ c : Cube P.m, w' c * G (s, c)) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [presum_collapse P Fq Dom ch x ℓ y s]
    _ = prefixFactor P Fq Dom ch ℓ y x *
          ∑ s : Cube P.k₀, ∑ c : Cube P.m,
            eqPoly (mixedPoint P Fq Dom ch ℓ y x) s * w' c * G (s, c) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring

/-- `evalT` as a double sum over class and position coordinates. -/
theorem evalT_double_sum (ys : Fin P.k₀ → Fq) (xs : Fin P.m → Fq) :
    evalT P Fq T ys xs =
      ∑ s : Cube P.k₀, ∑ c : Cube P.m,
        eqPoly ys s * eqPoly xs c * liftT P Fq T (s, c) := by
  unfold evalT
  rw [Fintype.sum_prod_type]

/-- **The channel decomposition of the sumcheck message** (`eq:channel`):
`ĥ_ℓ(y)` splits into the two out-of-domain channels — each a scalar prefix
factor times a mixed-point evaluation of the committed table — plus `γ²`
times the cross term against the input weight. -/
theorem hPoly_channel (ℓ : Fin P.k₀) (y : Fq) :
    hPoly P Fq Dom S T ch ℓ y =
      prefixFactor P Fq Dom ch ℓ y (powSeq (ch.z 0) P.k₀) *
        evalT P Fq T (mixedPoint P Fq Dom ch ℓ y (powSeq (ch.z 0) P.k₀))
          (powSeq (ch.z 0 ^ 2 ^ P.k₀) P.m) +
      ch.γ * (prefixFactor P Fq Dom ch ℓ y (powSeq (ch.z 1) P.k₀) *
        evalT P Fq T (mixedPoint P Fq Dom ch ℓ y (powSeq (ch.z 1) P.k₀))
          (powSeq (ch.z 1 ^ 2 ^ P.k₀) P.m)) +
      ch.γ ^ 2 * crossTerm P Fq Dom S T ch ℓ y := by
  classical
  have hW : W₀ P Fq Dom S ch =
      (fun u : Cell P => eqPoly (powSeq (ch.z 0) P.k₀) u.1 *
        eqPoly (powSeq (ch.z 0 ^ 2 ^ P.k₀) P.m) u.2) +
      ch.γ • (fun u : Cell P => eqPoly (powSeq (ch.z 1) P.k₀) u.1 *
        eqPoly (powSeq (ch.z 1 ^ 2 ^ P.k₀) P.m) u.2) +
      ch.γ ^ 2 • S.w := by
    funext u
    simp [W₀, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hPoly_eq_filter_sum, hW]
  simp only [partialEval_add, partialEval_smul]
  have hdistrib : ∀ (b : Cube P.k₀) (c : Cube P.m),
      partialEval P Fq Dom ch (liftT P Fq T) ℓ y b c *
        (partialEval P Fq Dom ch (fun u : Cell P =>
            eqPoly (powSeq (ch.z 0) P.k₀) u.1 *
            eqPoly (powSeq (ch.z 0 ^ 2 ^ P.k₀) P.m) u.2) ℓ y b c +
          ch.γ * partialEval P Fq Dom ch (fun u : Cell P =>
            eqPoly (powSeq (ch.z 1) P.k₀) u.1 *
            eqPoly (powSeq (ch.z 1 ^ 2 ^ P.k₀) P.m) u.2) ℓ y b c +
          ch.γ ^ 2 * partialEval P Fq Dom ch S.w ℓ y b c) =
      partialEval P Fq Dom ch (liftT P Fq T) ℓ y b c *
        partialEval P Fq Dom ch (fun u : Cell P =>
          eqPoly (powSeq (ch.z 0) P.k₀) u.1 *
          eqPoly (powSeq (ch.z 0 ^ 2 ^ P.k₀) P.m) u.2) ℓ y b c +
      ch.γ * (partialEval P Fq Dom ch (liftT P Fq T) ℓ y b c *
        partialEval P Fq Dom ch (fun u : Cell P =>
          eqPoly (powSeq (ch.z 1) P.k₀) u.1 *
          eqPoly (powSeq (ch.z 1 ^ 2 ^ P.k₀) P.m) u.2) ℓ y b c) +
      ch.γ ^ 2 * (partialEval P Fq Dom ch (liftT P Fq T) ℓ y b c *
        partialEval P Fq Dom ch S.w ℓ y b c) := fun b c => by ring
  simp only [hdistrib]
  simp only [Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  congr 1
  · congr 1
    · rw [evalT_double_sum P Fq T]
      exact channel_collapse P Fq Dom ch (liftT P Fq T) (powSeq (ch.z 0) P.k₀)
        (eqPoly (powSeq (ch.z 0 ^ 2 ^ P.k₀) P.m)) ℓ y
    · congr 1
      rw [evalT_double_sum P Fq T]
      exact channel_collapse P Fq Dom ch (liftT P Fq T) (powSeq (ch.z 1) P.k₀)
        (eqPoly (powSeq (ch.z 1 ^ 2 ^ P.k₀) P.m)) ℓ y

/-- **The `(ℓ, y)`-family of channel identities** (`lem:fullslice`, Step 1):
for a view-invisible perturbation `Δ`, the channel decomposition of every
message polynomial vanishes identically — at every level and every point. -/
theorem channel_identity_of_invisible (h2 : (2 : Fq) ≠ 0) (Δ : Cell P → Fp P)
    (hinv : Invisible P Fq Dom S ch Δ) (ℓ : Fin P.k₀) (y : Fq) :
    prefixFactor P Fq Dom ch ℓ y (powSeq (ch.z 0) P.k₀) *
      evalT P Fq Δ (mixedPoint P Fq Dom ch ℓ y (powSeq (ch.z 0) P.k₀))
        (powSeq (ch.z 0 ^ 2 ^ P.k₀) P.m) +
    ch.γ * (prefixFactor P Fq Dom ch ℓ y (powSeq (ch.z 1) P.k₀) *
      evalT P Fq Δ (mixedPoint P Fq Dom ch ℓ y (powSeq (ch.z 1) P.k₀))
        (powSeq (ch.z 1 ^ 2 ^ P.k₀) P.m)) +
    ch.γ ^ 2 * crossTerm P Fq Dom S Δ ch ℓ y = 0 := by
  rw [← hPoly_channel P Fq Dom S Δ ch ℓ y]
  exact hPoly_eq_zero_of_invisible P Fq Dom S ch h2 Δ hinv ℓ y

/-! ## Fold-table confinement (`lem:noother`, Step 1)

The transcript exposes the fully folded polynomial `f̂₁`; its multilinear
extension is exactly the `α`-slice of the table's evaluation. Hence for an
invisible perturbation the whole `α`-slice vanishes — every evaluation whose
class part is the sumcheck point is automatically zero, at *every* position
point. -/

/-- The evaluation at class point `α` is the multilinear extension of the
fold. -/
theorem evalT_alpha_eq_mle_fold (xs : Fin P.m → Fq) :
    evalT P Fq T ch.α xs = mle (foldedF₁ P Fq Dom T ch) xs := by
  rw [evalT_double_sum P Fq T ch.α xs]
  unfold mle foldedF₁
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **Fold confinement**: an invisible perturbation has vanishing `α`-slice —
its evaluation at any point whose class part is the sumcheck point is zero. -/
theorem evalT_alpha_eq_zero_of_invisible (Δ : Cell P → Fp P)
    (hinv : Invisible P Fq Dom S ch Δ) (xs : Fin P.m → Fq) :
    evalT P Fq Δ ch.α xs = 0 := by
  rw [evalT_alpha_eq_mle_fold P Fq Dom Δ ch xs, hinv.fold]
  unfold mle
  simp

/-! ## Reduction of invisibility to the view (`lem:reduction` for differences)

The `X = 0` sumcheck values are *determined* by the others through the
telescoping relation and the initial target, so a perturbation is invisible
as soon as the out-of-domain answers, the `X = 1, 2` message values, the
query answers, the fold, and the `ŵ`-pairing all vanish. This is what makes
the view-solving of the mask solver (`prop:uniform`, `lem:kersurj`)
sufficient for full invisibility. -/

/-- **The `X = 0` message values are not free data**: they are forced by the
out-of-domain answers, the `X = 1, 2` values, and the `ŵ`-pairing, through
the telescoping relation — by induction along the rounds. -/
theorem msg0_of_reduced_view (h2 : (2 : Fq) ≠ 0) (Δ : Cell P → Fp P)
    (hood : ∀ j, oodAnswer P Fq Δ (ch.z j) = 0)
    (hmsg1 : ∀ ℓ, hPoly P Fq Dom S Δ ch ℓ 1 = 0)
    (hmsg2 : ∀ ℓ, hPoly P Fq Dom S Δ ch ℓ 2 = 0)
    (hw : ∑ u : Cell P, liftT P Fq Δ u * S.w u = 0) :
    ∀ ℓ, hPoly P Fq Dom S Δ ch ℓ 0 = 0 := by
  have hbase : ∑ u : Cell P, liftT P Fq Δ u * W₀ P Fq Dom S ch u = 0 := by
    have hsplit : ∀ u : Cell P, liftT P Fq Δ u * W₀ P Fq Dom S ch u =
        eqPoly (powSeq (ch.z 0) P.k₀) u.1 *
            eqPoly (powSeq (ch.z 0 ^ 2 ^ P.k₀) P.m) u.2 * liftT P Fq Δ u +
          ch.γ * (eqPoly (powSeq (ch.z 1) P.k₀) u.1 *
            eqPoly (powSeq (ch.z 1 ^ 2 ^ P.k₀) P.m) u.2 * liftT P Fq Δ u) +
          ch.γ ^ 2 * (liftT P Fq Δ u * S.w u) := by
      intro u
      unfold W₀
      ring
    calc ∑ u : Cell P, liftT P Fq Δ u * W₀ P Fq Dom S ch u
        = ∑ u : Cell P, (eqPoly (powSeq (ch.z 0) P.k₀) u.1 *
              eqPoly (powSeq (ch.z 0 ^ 2 ^ P.k₀) P.m) u.2 * liftT P Fq Δ u +
            ch.γ * (eqPoly (powSeq (ch.z 1) P.k₀) u.1 *
              eqPoly (powSeq (ch.z 1 ^ 2 ^ P.k₀) P.m) u.2 * liftT P Fq Δ u) +
            ch.γ ^ 2 * (liftT P Fq Δ u * S.w u)) :=
          Finset.sum_congr rfl fun u _ => hsplit u
      _ = oodAnswer P Fq Δ (ch.z 0) + ch.γ * oodAnswer P Fq Δ (ch.z 1) +
            ch.γ ^ 2 * ∑ u : Cell P, liftT P Fq Δ u * S.w u := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
          rfl
      _ = 0 := by
          rw [hood 0, hood 1, hw]
          ring
  have hmsg0 : ∀ ℓ, hPoly P Fq Dom S Δ ch ℓ 0 = 0 := by
    have key : ∀ n : ℕ, ∀ ℓ : Fin P.k₀, (ℓ : ℕ) = n →
        hPoly P Fq Dom S Δ ch ℓ 0 = 0 := by
      intro n
      induction n with
      | zero =>
        intro ℓ hℓ
        have hℓ0 : ℓ = ⟨0, P.k₀_pos⟩ := Fin.ext hℓ
        rw [hℓ0]
        have hb := hPoly_base P Fq Dom S Δ ch
        rw [hbase] at hb
        have h1 := hmsg1 ⟨0, P.k₀_pos⟩
        linear_combination hb - h1
      | succ n ihn =>
        intro ℓ hℓ
        have hn : n < P.k₀ := by
          have := ℓ.isLt
          omega
        have h0 := ihn ⟨n, hn⟩ rfl
        obtain ⟨q₀, q₁, q₂, hq⟩ := hPoly_quadratic P Fq Dom S Δ ch ⟨n, hn⟩
        have e0 : q₀ = 0 := by
          rw [hq 0] at h0
          linear_combination h0
        have e1 : q₀ + q₁ + q₂ = 0 := by
          have h := hmsg1 ⟨n, hn⟩
          rw [hq 1] at h
          linear_combination h
        have e2 : q₀ + 2 * q₁ + 4 * q₂ = 0 := by
          have h := hmsg2 ⟨n, hn⟩
          rw [hq 2] at h
          linear_combination h
        have hz : hPoly P Fq Dom S Δ ch ⟨n, hn⟩ (ch.α ⟨n, hn⟩) = 0 := by
          rw [hq (ch.α ⟨n, hn⟩)]
          linear_combination quadratic_zero_of_three Fq h2 e0 e1 e2
            (ch.α ⟨n, hn⟩)
        have hsucc : ((⟨n, hn⟩ : Fin P.k₀) : ℕ) + 1 = (ℓ : ℕ) := by
          have hval : ((⟨n, hn⟩ : Fin P.k₀) : ℕ) = n := rfl
          omega
        have hstep := hPoly_succ_step P Fq Dom S Δ ch hsucc
        rw [hz] at hstep
        have h1 := hmsg1 ℓ
        linear_combination hstep - h1
    exact fun ℓ => key (ℓ : ℕ) ℓ rfl
  exact hmsg0

/-- **View reduction**: invisibility from the reduced view — the `msg0`
components come from `msg0_of_reduced_view`. -/
theorem invisible_of_view_vanishing (h2 : (2 : Fq) ≠ 0) (Δ : Cell P → Fp P)
    (hood : ∀ j, oodAnswer P Fq Δ (ch.z j) = 0)
    (hmsg1 : ∀ ℓ, hPoly P Fq Dom S Δ ch ℓ 1 = 0)
    (hmsg2 : ∀ ℓ, hPoly P Fq Dom S Δ ch ℓ 2 = 0)
    (hqa : ∀ t s, queryAnswer P Fq Dom Δ ch t s = 0)
    (hfold : foldedF₁ P Fq Dom Δ ch = 0)
    (hw : ∑ u : Cell P, liftT P Fq Δ u * S.w u = 0) :
    Invisible P Fq Dom S ch Δ :=
  ⟨hood, msg0_of_reduced_view P Fq Dom S ch h2 Δ hood hmsg1 hmsg2 hw,
    hmsg1, hmsg2, hqa, hfold⟩

/-! ## Protocol identities for the mask solver -/

/-- Any evaluation decomposes over the classes: the class weights multiply
the per-class fiber extensions. -/
theorem evalT_eq_sum_classes (ys : Fin P.k₀ → Fq) (xs : Fin P.m → Fq) :
    evalT P Fq T ys xs =
      ∑ s : Cube P.k₀, eqPoly ys s *
        mle (fun c => liftT P Fq T (s, c)) xs := by
  rw [evalT_double_sum P Fq T ys xs]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold mle
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- At the terminal level, evaluating the partial evaluation at the last
challenge folds the table completely. -/
theorem partialEval_terminal (G : Cell P → Fq) {ℓ : Fin P.k₀}
    (hlast : (ℓ : ℕ) + 1 = P.k₀) (b : Cube P.k₀) (c : Cube P.m) :
    partialEval P Fq Dom ch G ℓ (ch.α ℓ) b c =
      ∑ s, eqPoly ch.α s * G (s, c) := by
  unfold partialEval eqPoly
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rcases lt_trichotomy i ℓ with h | h | h
  · rw [if_pos h]
  · subst h
    rw [if_neg (lt_irrefl i), if_pos rfl]
  · exfalso
    have hi := i.isLt
    rw [Fin.lt_def] at h
    omega

/-- **The terminal sumcheck identity**: the last message evaluated at the
last challenge is the pairing of the fold against the folded weight
(`lem:protocoldirs` (iii)). -/
theorem hPoly_terminal {ℓ : Fin P.k₀} (hlast : (ℓ : ℕ) + 1 = P.k₀) :
    hPoly P Fq Dom S T ch ℓ (ch.α ℓ) =
      ∑ c : Cube P.m, foldedF₁ P Fq Dom T ch c *
        ∑ s, eqPoly ch.α s * W₀ P Fq Dom S ch (s, c) := by
  rw [hPoly_eq_filter_sum]
  have hfilt : Finset.univ.filter
      (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ, b i = false) =
      {fun _ => false} := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, Finset.mem_Iic]
    constructor
    · intro hb
      funext i
      refine hb i ?_
      rw [Fin.le_def]
      have := i.isLt
      omega
    · intro hb i _
      rw [hb]
  rw [hfilt, Finset.sum_singleton]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [partialEval_terminal P Fq Dom ch _ hlast,
    partialEval_terminal P Fq Dom ch _ hlast]
  rfl

/-- **`lem:blocks`**: when the input weight vanishes on the masks, its
partial evaluations vanish at every block position — block-supported
perturbations contribute no cross-terms. -/
theorem partialEval_weight_block_eq_zero (hmf : MaskFree P Fq S)
    {c : Cube P.m} (hc : IsBlockPos P c) (ℓ : Fin P.k₀) (X : Fq)
    (b : Cube P.k₀) :
    partialEval P Fq Dom ch S.w ℓ X b c = 0 := by
  unfold partialEval
  refine Finset.sum_eq_zero fun s _ => ?_
  rw [hmf (s, c) (Or.inr hc), mul_zero]

/-- The cross term reads the table only at non-block positions: the
`ŵ`-factor vanishes on the blocks (`lem:blocks`), so block contents are
invisible to it. -/
theorem crossTerm_eq_of_eq_nonblock (hmf : MaskFree P Fq S)
    (T T' : Cell P → Fp P)
    (h : ∀ s (c : Cube P.m), ¬ IsBlockPos P c → T (s, c) = T' (s, c))
    (ℓ : Fin P.k₀) (y : Fq) :
    crossTerm P Fq Dom S T ch ℓ y = crossTerm P Fq Dom S T' ch ℓ y := by
  unfold crossTerm
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
  by_cases hc : IsBlockPos P c
  · rw [partialEval_weight_block_eq_zero P Fq Dom S ch hmf hc, mul_zero,
      mul_zero]
  · congr 1
    unfold partialEval
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show liftT P Fq T (s, c) = liftT P Fq T' (s, c) from by
      unfold liftT
      rw [h s c hc]]

/-- **Fold consistency** (`lem:protocoldirs` (i)): the extension of the fold
is the `λ`-combination of the per-class fiber extensions, at every point. -/
theorem mle_fold_eq_sum_classes (xs : Fin P.m → Fq) :
    mle (foldedF₁ P Fq Dom T ch) xs =
      ∑ s : Cube P.k₀, eqPoly ch.α s *
        mle (fun c => liftT P Fq T (s, c)) xs := by
  rw [← evalT_alpha_eq_mle_fold P Fq Dom T ch xs]
  exact evalT_eq_sum_classes P Fq T ch.α xs

/-- If the three recorded values of every message vanish, the messages
vanish as polynomials — at every evaluation point. -/
theorem hPoly_eq_zero_of_msgs (h2 : (2 : Fq) ≠ 0)
    (hmsg0 : ∀ ℓ, hPoly P Fq Dom S T ch ℓ 0 = 0)
    (hmsg1 : ∀ ℓ, hPoly P Fq Dom S T ch ℓ 1 = 0)
    (hmsg2 : ∀ ℓ, hPoly P Fq Dom S T ch ℓ 2 = 0)
    (ℓ : Fin P.k₀) (y : Fq) :
    hPoly P Fq Dom S T ch ℓ y = 0 := by
  obtain ⟨q₀, q₁, q₂, hq⟩ := hPoly_quadratic P Fq Dom S T ch ℓ
  have e0 : q₀ = 0 := by
    have h := hmsg0 ℓ
    rw [hq 0] at h
    linear_combination h
  have e1 : q₀ + q₁ + q₂ = 0 := by
    have h := hmsg1 ℓ
    rw [hq 1] at h
    linear_combination h
  have e2 : q₀ + 2 * q₁ + 4 * q₂ = 0 := by
    have h := hmsg2 ℓ
    rw [hq 2] at h
    linear_combination h
  rw [hq y]
  linear_combination quadratic_zero_of_three Fq h2 e0 e1 e2 y

/-- The terminal pairing of the fold against the folded weight vanishes once
all messages vanish (`lem:protocoldirs` (iii), difference form). -/
theorem terminal_pairing_eq_zero_of_msgs (h2 : (2 : Fq) ≠ 0)
    (hmsg0 : ∀ ℓ, hPoly P Fq Dom S T ch ℓ 0 = 0)
    (hmsg1 : ∀ ℓ, hPoly P Fq Dom S T ch ℓ 1 = 0)
    (hmsg2 : ∀ ℓ, hPoly P Fq Dom S T ch ℓ 2 = 0) :
    ∑ c : Cube P.m, foldedF₁ P Fq Dom T ch c *
      ∑ s, eqPoly ch.α s * W₀ P Fq Dom S ch (s, c) = 0 := by
  have hk : P.k₀ - 1 < P.k₀ := by
    have := P.k₀_pos
    omega
  have hlast : ((⟨P.k₀ - 1, hk⟩ : Fin P.k₀) : ℕ) + 1 = P.k₀ := by
    show P.k₀ - 1 + 1 = P.k₀
    have := P.k₀_pos
    omega
  rw [← hPoly_terminal P Fq Dom S T ch hlast]
  exact hPoly_eq_zero_of_msgs P Fq Dom S T ch h2 hmsg0 hmsg1 hmsg2 _ _

end ZkWhir
