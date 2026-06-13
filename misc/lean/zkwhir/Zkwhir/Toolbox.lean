/-
Toolbox lemmas of `zk_leanVM.tex` (`sec:toolbox`), formalized. These are the
elementary, WHIR-free engines of the zero-knowledge proof. Everything in this
file is fully proved.

Coordinates for the pencil lemma: a vector of `F^(k×2)` is a function
`Fin k × Bool → F`; `(ℓ, false)` is the paper's coordinate `(ℓ, 1)` and
`(ℓ, true)` is `(ℓ, 2)`.
-/
import Mathlib

set_option linter.style.header false

noncomputable section

namespace ZkWhir

open Submodule

variable {F : Type*} [Field F] {k : ℕ}

/-- **Triangular pencils** (`lem:pencil`). `u ℓ` has leading `1` at
`(ℓ, false)`, diagonal `g ℓ` at `(ℓ, true)`, arbitrary lower terms at
`(i, true)` for `i < ℓ`, and nothing else; likewise `u'` with diagonals `g'`.
If the diagonals differ in every slot, the two spans intersect trivially. -/
theorem pencil_inter_eq_bot (u u' : Fin k → (Fin k × Bool → F)) (g g' : Fin k → F)
    (hu_lead : ∀ ℓ i, u ℓ (i, false) = if i = ℓ then 1 else 0)
    (hu'_lead : ∀ ℓ i, u' ℓ (i, false) = if i = ℓ then 1 else 0)
    (hu_diag : ∀ ℓ, u ℓ (ℓ, true) = g ℓ)
    (hu'_diag : ∀ ℓ, u' ℓ (ℓ, true) = g' ℓ)
    (hu_upper : ∀ ℓ i, ℓ < i → u ℓ (i, true) = 0)
    (hu'_upper : ∀ ℓ i, ℓ < i → u' ℓ (i, true) = 0)
    (hg : ∀ ℓ, g ℓ ≠ g' ℓ) :
    span F (Set.range u) ⊓ span F (Set.range u') = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hx'⟩
  rw [SetLike.mem_coe, mem_span_range_iff_exists_fun] at hx hx'
  obtain ⟨lam, hlam⟩ := hx
  obtain ⟨lam', hlam'⟩ := hx'
  have hsum : ∀ p : Fin k × Bool,
      ∑ ℓ, lam ℓ * u ℓ p = ∑ ℓ, lam' ℓ * u' ℓ p := by
    intro p
    have h := congrFun (hlam.trans hlam'.symm) p
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
  -- Step 1: the two coefficient families agree (the `(j, false)` coordinates).
  have hcoef : ∀ j, lam j = lam' j := by
    intro j
    have h := hsum (j, false)
    simpa [hu_lead, hu'_lead, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq]
      using h
  -- Step 2: all coefficients vanish, by downward induction (the `(j, true)`
  -- coordinates; the diagonals differ).
  have hzero : ∀ n (j : Fin k), k - (j : ℕ) ≤ n → lam j = 0 := by
    intro n
    induction n with
    | zero =>
      intro j hj
      exact absurd hj (by have := j.isLt; omega)
    | succ n ih =>
      intro j _
      have hgt : ∀ i, j < i → lam i = 0 := fun i hi => by
        have hij : (j : ℕ) < (i : ℕ) := hi
        exact ih i (by omega)
      have hL : ∑ ℓ, lam ℓ * u ℓ (j, true) = lam j * g j := by
        rw [Finset.sum_eq_single j]
        · rw [hu_diag]
        · intro b _ hb
          rcases lt_or_gt_of_ne hb with hlt | hgt'
          · rw [hu_upper b j hlt, mul_zero]
          · rw [hgt b hgt', zero_mul]
        · intro habs
          exact absurd (Finset.mem_univ j) habs
      have hR : ∑ ℓ, lam' ℓ * u' ℓ (j, true) = lam j * g' j := by
        rw [Finset.sum_eq_single j]
        · rw [hu'_diag, ← hcoef]
        · intro b _ hb
          rcases lt_or_gt_of_ne hb with hlt | hgt'
          · rw [hu'_upper b j hlt, mul_zero]
          · rw [← hcoef, hgt b hgt', zero_mul]
        · intro habs
          exact absurd (Finset.mem_univ j) habs
      have key : lam j * g j = lam j * g' j :=
        hL.symm.trans ((hsum (j, true)).trans hR)
      have hsub : lam j * (g j - g' j) = 0 := by
        rw [mul_sub, key, sub_self]
      rcases mul_eq_zero.mp hsub with h0 | h0
      · exact h0
      · exact absurd (sub_eq_zero.mp h0) (hg j)
  -- Conclude: `x` is the zero combination.
  have hall : ∀ j, lam j = 0 := fun j => hzero k j (by omega)
  simp only [Submodule.mem_bot]
  rw [← hlam]
  simp [hall]

/-- **Coupled blocks** (`lem:blockrank`). Rows over a two-block column space
`ι₁ ⊕ ι₂`: the rows `(ω₁ ∣ 0)`, `(0 ∣ ω₂)`, and the coupled rows
`(A₁ r ∣ γ • A₂ r)`. If the only `ν` lying in both projected left kernels is
`0` (the second kernel taken for the `γ`-scaled coefficients, as in the
paper's `(μ₂, γν) ∈ K₂`), then a vanishing combination of the rows has all
coefficients zero. -/
theorem coupled_blocks {ι₁ ι₂ ρ : Type*} [Fintype ρ]
    (ω₁ : ι₁ → F) (ω₂ : ι₂ → F) (A₁ : ρ → ι₁ → F) (A₂ : ρ → ι₂ → F)
    (γ : F) (hω₁ : ω₁ ≠ 0) (hω₂ : ω₂ ≠ 0)
    (hker : ∀ ν : ρ → F,
      (∃ μ₁ : F, μ₁ • ω₁ + ∑ r, ν r • A₁ r = 0) →
      (∃ μ₂ : F, μ₂ • ω₂ + ∑ r, (γ * ν r) • A₂ r = 0) → ν = 0)
    (μ₁ μ₂ : F) (ν : ρ → F)
    (h : μ₁ • (Sum.elim ω₁ 0 : ι₁ ⊕ ι₂ → F) + μ₂ • Sum.elim (0 : ι₁ → F) ω₂
        + ∑ r, ν r • Sum.elim (A₁ r) (γ • A₂ r) = 0) :
    μ₁ = 0 ∧ μ₂ = 0 ∧ ν = 0 := by
  -- Restrict the vanishing combination to each block.
  have h₁ : μ₁ • ω₁ + ∑ r, ν r • A₁ r = 0 := by
    funext i
    have h' := congrFun h (Sum.inl i)
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h'
  have h₂ : μ₂ • ω₂ + ∑ r, (γ * ν r) • A₂ r = 0 := by
    funext i
    have h' := congrFun h (Sum.inr i)
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.zero_apply,
      Sum.elim_inr, smul_eq_mul, mul_zero, zero_add] at h' ⊢
    have hsum : ∑ r, ν r * (γ * A₂ r i) = ∑ r, γ * ν r * A₂ r i :=
      Finset.sum_congr rfl fun r _ => by ring
    rw [hsum] at h'
    simpa using h'
  -- The kernel condition kills `ν`, then each `ω`-coefficient.
  have hν : ν = 0 := hker ν ⟨μ₁, h₁⟩ ⟨μ₂, h₂⟩
  have hμ₁ : μ₁ = 0 := by
    have hh : μ₁ • ω₁ = 0 := by simpa [hν] using h₁
    rcases smul_eq_zero.mp hh with h0 | h0
    · exact h0
    · exact absurd h0 hω₁
  have hμ₂ : μ₂ = 0 := by
    have hh : μ₂ • ω₂ = 0 := by simpa [hν] using h₂
    rcases smul_eq_zero.mp hh with h0 | h0
    · exact h0
    · exact absurd h0 hω₂
  exact ⟨hμ₁, hμ₂, hν⟩

/-- **Chain matrices, annihilation** (`lem:chain`): with
`ρ_ℓ = ω + ∑_{i<ℓ} λ_i τ_i`, `row(ℓ,1) = A_ℓ ρ_ℓ + B_ℓ τ_ℓ`, and
`row(ℓ,2) = C_ℓ τ_ℓ`, the kernel vector `κ_ℓ` — coefficient `1` on
`row(ℓ,1)`, `−B_ℓ/C_ℓ` on `row(ℓ,2)`, `−A_ℓ` on `ω`, `−A_ℓ λ_i / C_i` on
`row(i,2)` for `i < ℓ` — annihilates the rows. -/
theorem chain_kernel_annihilates {M : Type*} [AddCommGroup M] [Module F M]
    (ω : M) (τ : Fin k → M) (lam A B C : Fin k → F)
    (hC : ∀ ℓ, C ℓ ≠ 0) (ℓ : Fin k) :
    (A ℓ • (ω + ∑ i ∈ Finset.Iio ℓ, lam i • τ i) + B ℓ • τ ℓ)
      - (B ℓ / C ℓ) • (C ℓ • τ ℓ)
      - A ℓ • ω
      - ∑ i ∈ Finset.Iio ℓ, (A ℓ * lam i / C i) • (C i • τ i) = 0 := by
  have h1 : (B ℓ / C ℓ) * C ℓ = B ℓ := div_mul_cancel₀ _ (hC ℓ)
  have h2 : ∀ i, (A ℓ * lam i / C i) * C i = A ℓ * lam i := fun i =>
    div_mul_cancel₀ _ (hC i)
  simp only [smul_smul, h1, h2, smul_add, Finset.smul_sum]
  abel

/-- **Spanning solvability**: a family that spans the whole module hits every
target by a finite linear combination. This is how the \textsc{spread}
condition (`lem:spread`) is consumed by the mask solver (`prop:uniform`,
Stage A). -/
theorem span_top_solve {ι : Type*} [Fintype ι] {M : Type*} [AddCommGroup M]
    [Module F M] (v : ι → M) (hspan : span F (Set.range v) = ⊤) (t : M) :
    ∃ lam : ι → F, ∑ i, lam i • v i = t := by
  have ht : t ∈ span F (Set.range v) := hspan ▸ mem_top
  rwa [mem_span_range_iff_exists_fun] at ht

/-- `span_top_solve` in algebra form: base-field coefficients hitting an
extension-field target (the masks are `F_p`-valued, the fold is
`F_q`-valued). -/
theorem span_top_solve_algebra {ι : Type*} [Fintype ι] {E : Type*}
    [CommRing E] [Algebra F E] (v : ι → E)
    (hspan : span F (Set.range v) = ⊤) (t : E) :
    ∃ lam : ι → F, ∑ i, algebraMap F E (lam i) * v i = t := by
  obtain ⟨lam, hlam⟩ := span_top_solve v hspan t
  exact ⟨lam, by simpa [Algebra.smul_def] using hlam⟩

/-- **Pointwise base-field solve**: a spanning family over `F` reaches every
target *function* simultaneously, with base-field coefficients chosen per point.
This is how the masks (base-field) realize an arbitrary fold (extension-valued)
position by position. -/
theorem exists_pointwise_span_solution {E : Type*} [CommRing E] [Algebra F E]
    {ι : Type*} [Fintype ι] (g : ι → E)
    (hspan : span F (Set.range g) = ⊤) {κ : Type*} (G : κ → E) :
    ∃ w : ι → κ → F, ∀ c, ∑ i, algebraMap F E (w i c) * g i = G c := by
  choose lam hlam using fun c => span_top_solve_algebra g hspan (G c)
  exact ⟨fun i c => lam c i, fun c => hlam c⟩

/-- **Independence from an invertible minor**: a family of vectors indexed
by coordinates is linearly independent as soon as *some* square selection of
coordinates has invertible determinant. This is how the staircase
independence certificate is consumed. -/
theorem linearIndependent_of_minor {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → κ → F) (g : ι → κ)
    (hdet : IsUnit (Matrix.of (fun i i' : ι => v i (g i'))).det) :
    LinearIndependent F v := by
  refine LinearIndependent.of_comp (LinearMap.funLeft F F g) ?_
  have hrows : LinearIndependent F
      (fun i => (Matrix.of (fun i i' : ι => v i (g i'))) i) :=
    Matrix.linearIndependent_rows_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).mpr hdet)
  exact hrows

/-- **Joint surjectivity from independent functionals**: a finite, linearly
independent family of linear forms reaches every target tuple. This is how
the full row rank of the node system (`thm:twopoint`) is consumed by the
mask solver. -/
theorem exists_preimage_of_linearIndependent_dual {V : Type*} [AddCommGroup V]
    [Module F V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (φ : ι → V →ₗ[F] F) (hli : LinearIndependent F φ) (t : ι → F) :
    ∃ v : V, ∀ i, φ i v = t i := by
  classical
  set Φ : V →ₗ[F] (ι → F) := LinearMap.pi φ with hΦ
  suffices hsurj : Function.Surjective Φ by
    obtain ⟨v, hv⟩ := hsurj t
    exact ⟨v, fun i => congrFun hv i⟩
  rw [← LinearMap.range_eq_top]
  by_contra hne
  obtain ⟨w₀, hw₀⟩ : ∃ w₀, w₀ ∉ LinearMap.range Φ := by
    by_contra hall
    exact hne (top_unique fun w _ =>
      not_not.mp fun hw => hall ⟨w, hw⟩)
  have hmk : (Submodule.Quotient.mk w₀ :
      (ι → F) ⧸ LinearMap.range Φ) ≠ 0 := by
    rw [Ne, Submodule.Quotient.mk_eq_zero]
    exact hw₀
  obtain ⟨ψ', hψ'⟩ : ∃ ψ' : Module.Dual F ((ι → F) ⧸ LinearMap.range Φ),
      ψ' (Submodule.Quotient.mk w₀) ≠ 0 := by
    by_contra hall
    exact hmk ((Module.forall_dual_apply_eq_zero_iff F _).mp
      (fun f => not_not.mp fun hf => hall ⟨f, hf⟩))
  set ψ : (ι → F) →ₗ[F] F := ψ'.comp (LinearMap.range Φ).mkQ with hψdef
  have hψ1 : ψ w₀ ≠ 0 := by
    simpa [hψdef, Submodule.mkQ_apply] using hψ'
  have hψ : ∀ w ∈ LinearMap.range Φ, ψ w = 0 := by
    intro w hw
    have hw0 : (Submodule.Quotient.mk w :
        (ι → F) ⧸ LinearMap.range Φ) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hw
    simp [hψdef, Submodule.mkQ_apply, hw0]
  -- expand `ψ` over coordinates
  have hψw : ∀ w : ι → F, ψ w = ∑ i, w i * ψ (Pi.single i 1) := by
    intro w
    conv_lhs => rw [← Finset.univ_sum_single w]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : Pi.single i (w i) = w i • Pi.single i (1 : F) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [this, map_smul, smul_eq_mul]
  -- the corresponding combination of the functionals vanishes
  have hcomb : ∑ i, ψ (Pi.single i 1) • φ i = 0 := by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply]
    have hv := hψ (Φ v) ⟨v, rfl⟩
    rw [hψw (Φ v)] at hv
    calc ∑ i, ψ (Pi.single i 1) * φ i v
        = ∑ i, Φ v i * ψ (Pi.single i 1) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hΦ, LinearMap.pi_apply, mul_comm]
      _ = 0 := hv
  -- independence kills the coefficients, contradicting `ψ w₀ = 1`
  have hc := linearIndependent_iff'.mp hli Finset.univ
    (fun i => ψ (Pi.single i 1)) hcomb
  have hψ0 : ψ = 0 := by
    apply LinearMap.ext
    intro w
    rw [hψw w, LinearMap.zero_apply]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hc i (Finset.mem_univ i), mul_zero]
  rw [hψ0, LinearMap.zero_apply] at hψ1
  exact hψ1 rfl

/-- **Moments determine coefficients** (Vandermonde): for distinct points
`v : Fin n → F`, every target moment vector `m` is realized by some
coefficients `μ` with `∑ₜ μₜ · vₜ^h = m h`. The engine of the moment systems
in `lem:fullslice`/`lem:noother`. -/
theorem exists_coeffs_of_moments {F : Type*} [Field F] {n : ℕ} (v : Fin n → F)
    (hv : Function.Injective v) (m : Fin n → F) :
    ∃ μ : Fin n → F, ∀ h : Fin n, ∑ t, μ t * v t ^ (h : ℕ) = m h := by
  classical
  set A : Matrix (Fin n) (Fin n) F := (Matrix.vandermonde v).transpose with hA
  have hdet : IsUnit A.det := by
    rw [hA, Matrix.det_transpose]
    exact (Matrix.det_vandermonde_ne_zero_iff.mpr hv).isUnit
  refine ⟨A⁻¹.mulVec m, fun h => ?_⟩
  have hmv : A.mulVec (A⁻¹.mulVec m) = m := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
  have hh : A.mulVec (A⁻¹.mulVec m) h = m h := congrFun hmv h
  rw [← hh]
  show ∑ t, (A⁻¹.mulVec m) t * v t ^ (h : ℕ) =
    ∑ t, A h t * (A⁻¹.mulVec m) t
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hA, Matrix.transpose_apply, Matrix.vandermonde_apply, mul_comm]

/-- **Solving an invertible linear system**: a matrix with a unit determinant
reaches every target under `mulVec`. The linear-algebra core of the (S, R)
moment matching. -/
theorem exists_mulVec_of_isUnit_det {F : Type*} [Field F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (hA : IsUnit A.det) (b : Fin n → F) :
    ∃ x, A.mulVec x = b :=
  ⟨A⁻¹.mulVec b, by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec]⟩

/-- **Membership via the dual annihilator** (finite-dimensional): `x ∈ U` iff
every functional vanishing on `U` vanishes at `x`. The primal↔dual bridge. -/
theorem mem_iff_forall_dualAnnihilator {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (U : Subspace K V) (x : V) :
    x ∈ U ↔ ∀ f ∈ U.dualAnnihilator, f x = 0 := by
  rw [← Submodule.mem_dualCoannihilator,
    Subspace.dualAnnihilator_dualCoannihilator_eq]

/-- **Reaching a target through a linear map** (finite-dimensional codomain):
`y` is in the range of `ψ` iff every functional that kills the whole image of
`ψ` also kills `y`. This is the criterion the primal pinning construction uses:
`−F` is a mask-fold iff every protocol direction (= functional killing all
mask-folds) annihilates `−F`. -/
theorem mem_range_iff_forall_dual {K W V : Type*} [Field K] [AddCommGroup W]
    [Module K W] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ψ : W →ₗ[K] V) (y : V) :
    y ∈ LinearMap.range ψ ↔
      ∀ f : Module.Dual K V, (∀ w, f (ψ w) = 0) → f y = 0 := by
  rw [mem_iff_forall_dualAnnihilator]
  constructor
  · intro h f hf
    exact h f ((Submodule.mem_dualAnnihilator f).mpr
      (fun x hx => by obtain ⟨w, rfl⟩ := LinearMap.mem_range.mp hx; exact hf w))
  · intro h f hf
    exact h f (fun w => (Submodule.mem_dualAnnihilator f).mp hf (ψ w)
      (LinearMap.mem_range.mpr ⟨w, rfl⟩))

/-- **Trace duality** (`lem:traceorth` core): over a finite separable extension,
an element is zero iff all its trace pairings vanish. This identifies the
`Fp`-functionals on `Fq` with `Fq` itself — the step that turns an
`Fq`-pairing condition into the full family of base-field directions. -/
theorem trace_eq_zero_iff {Fp Fq : Type*} [Field Fp] [Field Fq] [Algebra Fp Fq]
    [FiniteDimensional Fp Fq] [Algebra.IsSeparable Fp Fq] (x : Fq) :
    x = 0 ↔ ∀ a : Fq, Algebra.trace Fp Fq (a * x) = 0 := by
  refine ⟨fun hx a => by rw [hx, mul_zero, map_zero], fun h => ?_⟩
  refine (traceForm_nondegenerate Fp Fq).1 x (fun a => ?_)
  rw [Algebra.traceForm_apply, mul_comm]
  exact h a

/-- **A surjective `Fq`-form has nonzero trace** (the Step-4 reduction): if
`L : M → Fq` hits every value, then some `m` has `tr(L m) ≠ 0`. Hence
`tr ∘ L ≠ 0` whenever `L` is surjective — the trace argument reduces to a
spanning statement, no per-direction probability needed. -/
theorem exists_trace_ne_zero_of_surjective {Fp Fq M : Type*} [Field Fp]
    [Field Fq] [Algebra Fp Fq] [FiniteDimensional Fp Fq]
    [Algebra.IsSeparable Fp Fq] (L : M → Fq) (hL : Function.Surjective L) :
    ∃ m, Algebra.trace Fp Fq (L m) ≠ 0 := by
  have htr : ∃ a : Fq, Algebra.trace Fp Fq a ≠ 0 := by
    by_contra h
    push_neg at h
    exact one_ne_zero ((trace_eq_zero_iff (1 : Fq)).mpr
      (fun a => by rw [mul_one]; exact h a))
  obtain ⟨a, ha⟩ := htr
  obtain ⟨m, hm⟩ := hL a
  exact ⟨m, by rw [hm]; exact ha⟩

/-- **Trace-dual nondegeneracy on a product space** (`lem:traceorth` core): a
vector `v` over `Fq` is zero iff its trace pairing against every `w` vanishes.
This identifies `Fp`-functionals on `Fq^ι` with `Fq^ι` itself, the step that
represents an annihilator element as a trace pairing. -/
theorem trace_pairing_eq_zero_iff {Fp Fq : Type*} [Field Fp] [Field Fq]
    [Algebra Fp Fq] [FiniteDimensional Fp Fq] [Algebra.IsSeparable Fp Fq]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (v : ι → Fq) :
    (∀ w : ι → Fq, Algebra.trace Fp Fq (∑ i, v i * w i) = 0) ↔ v = 0 := by
  classical
  constructor
  · intro h
    funext i₀
    rw [Pi.zero_apply, trace_eq_zero_iff (Fp := Fp)]
    intro a
    have hsum := h (Pi.single i₀ a)
    rw [Finset.sum_eq_single i₀
      (fun i _ hi => by rw [Pi.single_eq_of_ne hi, mul_zero])
      (fun hni => absurd (Finset.mem_univ i₀) hni),
      Pi.single_eq_same, mul_comm] at hsum
    exact hsum
  · rintro rfl w; simp

/-- **Trace-dual representation** (`lem:traceorth`): every `Fp`-functional on
`Fq^ι` is the trace pairing against some vector `v`. This lets an annihilator
element be written as a concrete trace pairing. -/
theorem exists_trace_pairing_rep {Fp Fq : Type*} [Field Fp] [Field Fq]
    [Algebra Fp Fq] [FiniteDimensional Fp Fq] [Algebra.IsSeparable Fp Fq]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (φ : Module.Dual Fp (ι → Fq)) :
    ∃ v : ι → Fq, ∀ w : ι → Fq, φ w = Algebra.trace Fp Fq (∑ i, v i * w i) := by
  classical
  let B : LinearMap.BilinForm Fp (ι → Fq) :=
    LinearMap.mk₂ Fp (fun v w => Algebra.trace Fp Fq (∑ i, v i * w i))
      (fun v₁ v₂ w => by
        rw [← map_add]; congr 1; rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply]; ring)
      (fun c v w => by
        rw [← map_smul]; congr 1; rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]; ring)
      (fun v w₁ w₂ => by
        rw [← map_add]; congr 1; rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by rw [Pi.add_apply]; ring)
      (fun c v w => by
        rw [← map_smul]; congr 1; rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => by
          rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]; ring)
  have hB : B.Nondegenerate := by
    refine ⟨fun v hv => (trace_pairing_eq_zero_iff (Fp := Fp) v).mp (fun w => hv w),
      fun w hw => (trace_pairing_eq_zero_iff (Fp := Fp) w).mp (fun v => ?_)⟩
    have hwv := hw v
    rw [show (∑ i, w i * v i) = (∑ i, v i * w i) from
      Finset.sum_congr rfl fun i _ => mul_comm _ _]
    exact hwv
  let e := LinearMap.BilinForm.toDual B hB
  refine ⟨e.symm φ, fun w => ?_⟩
  have key : (e (e.symm φ)) w = φ w := by rw [e.apply_symm_apply]
  rw [← key]
  rfl

/-- **`SPREAD` + trace nondegeneracy** (`lem:confine` wrap-up): if a spanning
family `λs` over `Fp` has `tr(λs i · X) = 0` for every `i`, then `X = 0`. The
multipliers `λ_s = êq(α, s)` span `Fq` over `Fp` (the `SPREAD` condition), so the
vanishing trace pairings extend to all of `Fq` and the trace is nondegenerate. -/
theorem eq_zero_of_trace_pairing_span {Fp Fq : Type*} [Field Fp] [Field Fq]
    [Algebra Fp Fq] [FiniteDimensional Fp Fq] [Algebra.IsSeparable Fp Fq]
    {ι : Type*} (lam : ι → Fq)
    (hspan : Submodule.span Fp (Set.range lam) = ⊤)
    (X : Fq) (h : ∀ i, Algebra.trace Fp Fq (lam i * X) = 0) : X = 0 := by
  rw [trace_eq_zero_iff (Fp := Fp)]
  intro a
  have ha : a ∈ Submodule.span Fp (Set.range lam) := by rw [hspan]; exact Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
  | zero => rw [zero_mul, map_zero]
  | add x y _ _ hx hy => rw [add_mul, map_add, hx, hy, add_zero]
  | smul r x _ hx => rw [smul_mul_assoc, map_smul, hx, smul_zero]

/-- **A functional vanishing on the common kernel lies in the span of the
functionals** (the finite-dimensional annihilator/coannihilator duality;
`lem:confine`/`lem:nodechannel` core). If `f` kills every vector killed by all
of the `g i`, then `f` is a linear combination of the `g i`. -/
theorem mem_span_of_forall_ker {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {ι : Type*} (g : ι → Module.Dual K V)
    (f : Module.Dual K V) (hf : ∀ v, (∀ i, g i v = 0) → f v = 0) :
    f ∈ Submodule.span K (Set.range g) := by
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq
        (W := Submodule.span K (Set.range g)),
    Submodule.mem_dualAnnihilator]
  intro v hv
  rw [Submodule.mem_dualCoannihilator] at hv
  exact hf v fun i => hv (g i) (Submodule.subset_span ⟨i, rfl⟩)

/-- **Trace dual-basis reconstruction** (`lem:traceorth`/slice machinery): any
`x : Fq` is recovered from its trace pairings against an `Fp`-basis `b` of `Fq`
via the trace-form dual basis. The slices `tr(x · b i)` determine `x`. -/
theorem eq_sum_trace_smul_dualBasis {Fp Fq : Type*} [Field Fp] [Field Fq]
    [Algebra Fp Fq] [FiniteDimensional Fp Fq] [Algebra.IsSeparable Fp Fq]
    {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι Fp Fq) (x : Fq) :
    x = ∑ i, Algebra.trace Fp Fq (x * b i) •
      (LinearMap.BilinForm.dualBasis (Algebra.traceForm Fp Fq)
        (traceForm_nondegenerate Fp Fq) b) i := by
  conv_lhs =>
    rw [← Module.Basis.sum_repr (LinearMap.BilinForm.dualBasis
      (Algebra.traceForm Fp Fq) (traceForm_nondegenerate Fp Fq) b) x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply]

/-- **Trace-slice of a pairing** (slice machinery): the trace twist `β` of an
`Fp`-rational trace pairing `∑_c w_c · algebraMap(v_c)` is the `Fp`-pairing of
`v` against the slice vector `c ↦ tr(β · w_c)`. Lets the `Fq`-valued pairing
become a family of `Fp`-functionals (one per `β`). -/
theorem trace_smul_pairing {Fp Fq : Type*} [Field Fp] [Field Fq] [Algebra Fp Fq]
    {ι : Type*} [Fintype ι] (β : Fq) (w : ι → Fq) (v : ι → Fp) :
    Algebra.trace Fp Fq (β * ∑ c, w c * algebraMap Fp Fq (v c)) =
      ∑ c, v c * Algebra.trace Fp Fq (β * w c) := by
  rw [Finset.mul_sum, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [show β * (w c * algebraMap Fp Fq (v c)) = v c • (β * w c) from by
    rw [Algebra.smul_def]; ring, map_smul, smul_eq_mul]

/-- The functional on `ι → R` given by dotting against a vector `a`. -/
def dotFunc {R ι : Type*} [CommRing R] [Fintype ι] (a : ι → R) :
    Module.Dual R (ι → R) := ∑ i, a i • LinearMap.proj i

theorem dotFunc_apply {R ι : Type*} [CommRing R] [Fintype ι] (a v : ι → R) :
    dotFunc a v = ∑ i, a i * v i := by
  unfold dotFunc
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]

/-- `dotFunc` evaluated at the `i`-th indicator recovers `a i`. -/
theorem dotFunc_single {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (a : ι → R) (i : ι) : dotFunc a (Pi.single i 1) = a i := by
  rw [dotFunc_apply, Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, mul_one]
  · intro j _ hj; rw [Pi.single_eq_of_ne hj, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- `dotFunc` is injective: a functional determines its vector. -/
theorem dotFunc_injective {R ι : Type*} [CommRing R] [Fintype ι] :
    Function.Injective (dotFunc (R := R) (ι := ι)) := by
  classical
  intro a a' h
  funext i
  rw [← dotFunc_single a i, ← dotFunc_single a' i, h]

/-- **Slice-kernel characterization**: an `Fq` element is zero iff all its trace
slices against an `Fp`-basis vanish (the `Fq`-condition `= 0` is the conjunction
of `d` `Fp`-conditions). -/
theorem eq_zero_iff_trace_basis {Fp Fq : Type*} [Field Fp] [Field Fq]
    [Algebra Fp Fq] [FiniteDimensional Fp Fq] [Algebra.IsSeparable Fp Fq]
    {ι : Type*} (b : Module.Basis ι Fp Fq) (x : Fq) :
    x = 0 ↔ ∀ i, Algebra.trace Fp Fq (b i * x) = 0 := by
  constructor
  · rintro rfl i; rw [mul_zero, map_zero]
  · intro h; exact eq_zero_of_trace_pairing_span b b.span_eq x h

/-- **Dual-basis combination of a mixed pairing**: an `Fq`-against-`Fp` pairing
`∑_i w_i · v_i` is recovered from its trace slices via the trace dual basis. The
inner pairings `∑_i tr(b_r · w_i) · v_i` are `Fp`-valued. This combines the
per-slice node pairings of `lem:nodechannel` into the full `⟨w, vf_s⟩`. -/
theorem pairing_eq_sum_dualBasis {Fp Fq : Type*} [Field Fp] [Field Fq]
    [Algebra Fp Fq] [FiniteDimensional Fp Fq] [Algebra.IsSeparable Fp Fq]
    {ι : Type*} [Fintype ι] {ιβ : Type*} [Fintype ιβ] [DecidableEq ιβ]
    (b : Module.Basis ιβ Fp Fq) (w : ι → Fq) (v : ι → Fp) :
    (∑ i, w i * algebraMap Fp Fq (v i)) =
      ∑ r, (LinearMap.BilinForm.dualBasis (Algebra.traceForm Fp Fq)
          (traceForm_nondegenerate Fp Fq) b) r *
        algebraMap Fp Fq (∑ i, Algebra.trace Fp Fq (b r * w i) * v i) := by
  have hexpand : (∑ i, w i * algebraMap Fp Fq (v i)) =
      ∑ i, ∑ r, (Algebra.trace Fp Fq (b r * w i) •
        (LinearMap.BilinForm.dualBasis (Algebra.traceForm Fp Fq)
          (traceForm_nondegenerate Fp Fq) b) r) * algebraMap Fp Fq (v i) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_mul]
    congr 1
    conv_lhs => rw [eq_sum_trace_smul_dualBasis b (w i)]
    exact Finset.sum_congr rfl fun r _ => by rw [mul_comm (w i) (b r)]
  rw [hexpand, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mul_assoc, Algebra.smul_def, map_mul (algebraMap Fp Fq)]
  ring

end ZkWhir
