/-
The pinning framework (`prop:pinbound`, primal form via the dual bridge): the
view-vanishing mask perturbations and their folds form `Fp`-linear maps; the
primal `Pinning` (∃κ with view 0 and fold = −F) is membership of `−F` in the
range of the fold restricted to view-vanishing masks, which the dual bridge
(`mem_range_iff_forall_dual`) turns into the annihilator statement
`ann(W') = protocol span` of the paper.

This file sets up the linear-algebra scaffold; the annihilator computation
(`lem:fullslice`/`lem:noother`) consumes the slice/moment/trace toolkit.

Part of the `GoodSetAbsorption` formalization campaign.
-/
import Mathlib
import Zkwhir.Statement
import Zkwhir.Toolbox
import Zkwhir.Absorption

set_option linter.style.header false
set_option linter.unusedSectionVars false

noncomputable section

namespace ZkWhir

variable (P : Params) (Fq : Type*) [Field Fq] [Fintype Fq]
  [Algebra (Fp P) Fq] (Dom : Finset (Fp P)) [Nonempty {x // x ∈ Dom}]
  (S : Stmt P Fq) (ch : Challenges P Fq Dom)

/-- `assemble` with zero data is additive in the mask. -/
theorem assemble_zero_add (m₁ m₂ : MaskAssign P) :
    assemble P 0 (m₁ + m₂) = assemble P 0 m₁ + assemble P 0 m₂ := by
  funext u
  rw [Pi.add_apply]
  unfold assemble
  by_cases h : IsMask P u
  · rw [dif_pos h, dif_pos h, dif_pos h, Pi.add_apply]
  · rw [dif_neg h, dif_neg h, dif_neg h]
    simp

/-- `assemble` with zero data is homogeneous in the mask. -/
theorem assemble_zero_smul (c : Fp P) (m : MaskAssign P) :
    assemble P 0 (c • m) = c • assemble P 0 m := by
  funext u
  rw [Pi.smul_apply]
  unfold assemble
  by_cases h : IsMask P u
  · rw [dif_pos h, dif_pos h, Pi.smul_apply]
  · rw [dif_neg h, dif_neg h]
    simp

/-- `foldedF₁` is homogeneous: an `Fp`-scaling of the table becomes the
corresponding `Fp`-scaling (through `algebraMap`) of the fold. -/
theorem foldedF₁_smul (c : Fp P) (T : Cell P → Fp P) :
    foldedF₁ P Fq Dom (c • T) ch = c • foldedF₁ P Fq Dom T ch := by
  funext c'
  unfold foldedF₁
  rw [Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold liftT
  rw [Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def]
  ring

/-- `liftT` is homogeneous over `Fp`. -/
theorem liftT_smul (c : Fp P) (T : Cell P → Fp P) :
    liftT P Fq (c • T) = c • liftT P Fq T := by
  funext u
  simp only [liftT, Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def]

/-- `mle` is homogeneous over `Fp`. -/
theorem mle_smul_fp {j : ℕ} (c : Fp P) (M : Cube j → Fq) (xs : Fin j → Fq) :
    mle (c • M) xs = c • mle M xs := by
  unfold mle
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]; ring

/-- `evalT` is homogeneous over `Fp`. -/
theorem evalT_smul (c : Fp P) (T : Cell P → Fp P) (ys : Fin P.k₀ → Fq)
    (xs : Fin P.m → Fq) :
    evalT P Fq (c • T) ys xs = c • evalT P Fq T ys xs := by
  unfold evalT
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [liftT_smul, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]; ring

/-- `partialEval` is homogeneous over `Fp`. -/
theorem partialEval_smul_fp (c : Fp P) (G : Cell P → Fq) (ℓ : Fin P.k₀) (X : Fq)
    (b : Cube P.k₀) (cc : Cube P.m) :
    partialEval P Fq Dom ch (c • G) ℓ X b cc =
      c • partialEval P Fq Dom ch G ℓ X b cc := by
  unfold partialEval
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]; ring

/-- The out-of-domain answer is homogeneous over `Fp`. -/
theorem oodAnswer_smul (c : Fp P) (T : Cell P → Fp P) (z : Fq) :
    oodAnswer P Fq (c • T) z = c • oodAnswer P Fq T z := by
  unfold oodAnswer; rw [evalT_smul]

/-- The query answer is homogeneous over `Fp`. -/
theorem queryAnswer_smul (c : Fp P) (T : Cell P → Fp P) (t : Fin P.t₀)
    (s : Cube P.k₀) :
    queryAnswer P Fq Dom (c • T) ch t s =
      c • queryAnswer P Fq Dom T ch t s := by
  unfold queryAnswer
  have hfun : (fun cc => liftT P Fq (c • T) (s, cc)) =
      c • (fun cc => liftT P Fq T (s, cc)) := by
    funext cc; rw [liftT_smul]; rfl
  rw [hfun, mle_smul_fp]

/-- The sumcheck message is homogeneous over `Fp` (the weight `W₀` is fixed, so
the perturbation enters linearly). -/
theorem hPoly_smul (c : Fp P) (T : Cell P → Fp P) (ℓ : Fin P.k₀) (X : Fq) :
    hPoly P Fq Dom S (c • T) ch ℓ X = c • hPoly P Fq Dom S T ch ℓ X := by
  unfold hPoly
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun cc _ => ?_
  rw [liftT_smul, partialEval_smul_fp, Algebra.smul_def, Algebra.smul_def]; ring

/-- The folded `f̂₁` out-of-domain answer is homogeneous over `Fp`. -/
theorem mle_foldedF₁_smul (c : Fp P) (T : Cell P → Fp P) (xs : Fin P.m → Fq) :
    mle (foldedF₁ P Fq Dom (c • T) ch) xs = c • mle (foldedF₁ P Fq Dom T ch) xs := by
  rw [foldedF₁_smul, mle_smul_fp]

/-- **The fold map**: the `Fp`-linear map sending a mask `κ` to the fold of the
pure-mask perturbation `assemble 0 (−κ)`. Its range, restricted to the
view-vanishing masks, is the space the primal `Pinning` must hit. -/
def foldMap : MaskAssign P →ₗ[Fp P] (Cube P.m → Fq) where
  toFun κ := foldedF₁ P Fq Dom (assemble P 0 (-κ)) ch
  map_add' κ₁ κ₂ := by
    show foldedF₁ P Fq Dom (assemble P 0 (-(κ₁ + κ₂))) ch =
      foldedF₁ P Fq Dom (assemble P 0 (-κ₁)) ch +
        foldedF₁ P Fq Dom (assemble P 0 (-κ₂)) ch
    rw [neg_add, assemble_zero_add, foldedF₁_add]
  map_smul' c κ := by
    show foldedF₁ P Fq Dom (assemble P 0 (-(c • κ))) ch =
      c • foldedF₁ P Fq Dom (assemble P 0 (-κ)) ch
    rw [← smul_neg, assemble_zero_smul, foldedF₁_smul]

/-! ## The view-vanishing masks as a subspace -/

/-- `mle` is additive. -/
theorem mle_pi_add {j : ℕ} (M₁ M₂ : Cube j → Fq) (xs : Fin j → Fq) :
    mle (M₁ + M₂) xs = mle M₁ xs + mle M₂ xs := by
  unfold mle
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by rw [Pi.add_apply]; ring

/-- Zero data and zero mask assemble to the zero table. -/
theorem assemble_zero_zero : assemble P 0 (0 : MaskAssign P) = 0 := by
  funext u; unfold assemble
  by_cases h : IsMask P u <;> simp [h]

theorem liftT_zero : liftT P Fq (0 : Cell P → Fp P) = 0 := by
  funext u; simp [liftT]

theorem oodAnswer_zero (z : Fq) : oodAnswer P Fq (0 : Cell P → Fp P) z = 0 := by
  unfold oodAnswer evalT; simp [liftT]

theorem foldedF₁_zero : foldedF₁ P Fq Dom (0 : Cell P → Fp P) ch = 0 := by
  funext c'; unfold foldedF₁; simp [liftT]

theorem hPoly_zero (ℓ : Fin P.k₀) (X : Fq) :
    hPoly P Fq Dom S (0 : Cell P → Fp P) ch ℓ X = 0 := by
  unfold hPoly
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun cc _ => ?_
  have hz : partialEval P Fq Dom ch (liftT P Fq (0 : Cell P → Fp P)) ℓ X b cc = 0 := by
    rw [liftT_zero]; unfold partialEval; simp
  rw [hz]; ring

theorem queryAnswer_zero (t : Fin P.t₀) (s : Cube P.k₀) :
    queryAnswer P Fq Dom (0 : Cell P → Fp P) ch t s = 0 := by
  unfold queryAnswer; simp [liftT_zero, mle]

/-- The view of the zero table vanishes. -/
theorem viewVanishes_zero_table : ViewVanishes P Fq Dom S ch 0 :=
  ⟨fun j => oodAnswer_zero P Fq (ch.z j),
   fun ℓ => hPoly_zero P Fq Dom S ch ℓ 1,
   fun ℓ => hPoly_zero P Fq Dom S ch ℓ 2,
   fun t s => queryAnswer_zero P Fq Dom ch t s,
   fun j => by rw [foldedF₁_zero]; unfold mle; simp⟩

/-- **The view-vanishing masks** form an `Fp`-subspace: those `κ` whose
pure-mask perturbation `assemble 0 (−κ)` has vanishing reduced view. The
domain of the pinning fold map `ψ`. -/
def viewKer : Submodule (Fp P) (MaskAssign P) where
  carrier := {κ | ViewVanishes P Fq Dom S ch (assemble P 0 (-κ))}
  zero_mem' := by
    show ViewVanishes P Fq Dom S ch (assemble P 0 (-0))
    rw [neg_zero, assemble_zero_zero]
    exact viewVanishes_zero_table P Fq Dom S ch
  add_mem' := by
    intro κ₁ κ₂ h₁ h₂
    show ViewVanishes P Fq Dom S ch (assemble P 0 (-(κ₁ + κ₂)))
    rw [neg_add, assemble_zero_add]
    exact ⟨fun j => by rw [oodAnswer_add, h₁.ood j, h₂.ood j, add_zero],
      fun ℓ => by rw [hPoly_add, h₁.msg1 ℓ, h₂.msg1 ℓ, add_zero],
      fun ℓ => by rw [hPoly_add, h₁.msg2 ℓ, h₂.msg2 ℓ, add_zero],
      fun t s => by rw [queryAnswer_add, h₁.qa t s, h₂.qa t s, add_zero],
      fun j => by rw [foldedF₁_add, mle_pi_add, h₁.f1ood j, h₂.f1ood j, add_zero]⟩
  smul_mem' := by
    intro c κ h
    show ViewVanishes P Fq Dom S ch (assemble P 0 (-(c • κ)))
    rw [← smul_neg, assemble_zero_smul]
    exact ⟨fun j => by rw [oodAnswer_smul, h.ood j, smul_zero],
      fun ℓ => by rw [hPoly_smul, h.msg1 ℓ, smul_zero],
      fun ℓ => by rw [hPoly_smul, h.msg2 ℓ, smul_zero],
      fun t s => by rw [queryAnswer_smul, h.qa t s, smul_zero],
      fun j => by rw [mle_foldedF₁_smul, h.f1ood j, smul_zero]⟩

/-- Membership in `viewKer` is exactly view-vanishing. -/
theorem mem_viewKer (κ : MaskAssign P) :
    κ ∈ viewKer P Fq Dom S ch ↔
      ViewVanishes P Fq Dom S ch (assemble P 0 (-κ)) := Iff.rfl

/-- **The pinning fold map `ψ`**: the fold map restricted to the view-vanishing
masks. `Pinning` is exactly the statement that `−F` is in its range for every
protocol-killed `F`. -/
def pinFold : viewKer P Fq Dom S ch →ₗ[Fp P] (Cube P.m → Fq) :=
  (foldMap P Fq Dom ch).domRestrict (viewKer P Fq Dom S ch)

/-- **Reduction of `Pinning` to range membership**: if every protocol-killed
`F` has `−F` in the range of `ψ`, then `Pinning` holds. -/
theorem pinning_of_forall_range
    (h : ∀ F : Cube P.m → Fq,
        (∀ t, mle F (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0) →
        (∀ j, mle F (powSeq (ch.zf j) P.m) = 0) →
        ((∑ c, F c * ∑ s, eqPoly ch.α s * W₀ P Fq Dom S ch (s, c)) = 0) →
        (-F) ∈ LinearMap.range (pinFold P Fq Dom S ch)) :
    Pinning P Fq Dom S ch := by
  intro F hq hzf hterm
  obtain ⟨κ, hκ⟩ := h F hq hzf hterm
  refine ⟨κ.1, κ.2, ?_⟩
  rw [show (fun c => -F c) = -F from rfl]
  exact hκ

/-- **The dual form of `Pinning`** (the primal↔dual keystone): `Pinning`
follows once every protocol direction — every functional vanishing on all
view-vanishing mask-folds — also annihilates `−F`. This is the statement
`prop:pinbound` establishes (`ann(W') = protocol span`). -/
theorem pinning_of_dual [FiniteDimensional (Fp P) (Cube P.m → Fq)]
    (h : ∀ F : Cube P.m → Fq,
        (∀ t, mle F (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0) →
        (∀ j, mle F (powSeq (ch.zf j) P.m) = 0) →
        ((∑ c, F c * ∑ s, eqPoly ch.α s * W₀ P Fq Dom S ch (s, c)) = 0) →
        ∀ φ : Module.Dual (Fp P) (Cube P.m → Fq),
          (∀ κ : viewKer P Fq Dom S ch, φ (pinFold P Fq Dom S ch κ) = 0) →
          φ (-F) = 0) :
    Pinning P Fq Dom S ch := by
  apply pinning_of_forall_range
  intro F hq hzf hterm
  rw [mem_range_iff_forall_dual]
  exact h F hq hzf hterm

/-! ## Soundness of the protocol directions (`prop:pinbound`, easy direction)

Every view-vanishing mask-fold lies in the protocol-killed space: the queried
duals, the `f̂₁` out-of-domain duals, and the terminal pairing all annihilate
`range pinFold`. (The hard converse — that these span the whole annihilator —
is the slice argument of `lem:fullslice`/`lem:noother`.) -/

/-- A view-vanishing mask-fold vanishes at the queried points. -/
theorem pinFold_queried_zero (κ : viewKer P Fq Dom S ch) (t : Fin P.t₀) :
    mle (pinFold P Fq Dom S ch κ)
      (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0 := by
  show mle (foldedF₁ P Fq Dom (assemble P 0 (-κ.1)) ch)
    (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0
  rw [mle_fold_eq_sum_classes]
  refine Finset.sum_eq_zero fun s _ => ?_
  have hqa : mle (fun c => liftT P Fq (assemble P 0 (-κ.1)) (s, c))
      (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0 := κ.2.qa t s
  rw [hqa, mul_zero]

/-- A view-vanishing mask-fold vanishes at the `f̂₁` out-of-domain points. -/
theorem pinFold_zf_zero (κ : viewKer P Fq Dom S ch) (j : Fin P.s₁) :
    mle (pinFold P Fq Dom S ch κ) (powSeq (ch.zf j) P.m) = 0 :=
  κ.2.f1ood j

/-- A view-vanishing mask-fold has vanishing terminal pairing against the
`α`-fold of the batched weight. -/
theorem pinFold_terminal_zero (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S)
    (κ : viewKer P Fq Dom S ch) :
    (∑ c, (pinFold P Fq Dom S ch κ) c *
      ∑ s, eqPoly ch.α s * W₀ P Fq Dom S ch (s, c)) = 0 := by
  show (∑ c, foldedF₁ P Fq Dom (assemble P 0 (-κ.1)) ch c *
    ∑ s, eqPoly ch.α s * W₀ P Fq Dom S ch (s, c)) = 0
  have hw : ∑ u, liftT P Fq (assemble P 0 (-κ.1)) u * S.w u = 0 := by
    rw [pairing_assemble P Fq S hmf 0 (-κ.1)]; simp
  have hmsg0 := msg0_of_reduced_view P Fq Dom S ch h2 (assemble P 0 (-κ.1))
    κ.2.ood κ.2.msg1 κ.2.msg2 hw
  exact terminal_pairing_eq_zero_of_msgs P Fq Dom S (assemble P 0 (-κ.1)) ch h2
    hmsg0 κ.2.msg1 κ.2.msg2

end ZkWhir
