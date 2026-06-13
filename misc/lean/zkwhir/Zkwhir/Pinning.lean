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

set_option linter.style.header false
set_option linter.unusedSectionVars false

noncomputable section

namespace ZkWhir

variable (P : Params) (Fq : Type*) [Field Fq] [Fintype Fq]
  [Algebra (Fp P) Fq] (Dom : Finset (Fp P)) [Nonempty {x // x ∈ Dom}]
  (ch : Challenges P Fq Dom)

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

end ZkWhir
