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
