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

end ZkWhir
