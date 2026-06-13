/-
ε₃ measure bounds for `prop:pinbound` / `cond:pinning`: the Good-set failure
probabilities for the slice/cross conditions, assembled from the multivariate
Schwartz–Zippel chain (`SlotProb`) and the cross-form objects (`Pinning`).

Part of the `GoodSetAbsorption` formalization campaign.
-/
import Mathlib
import Zkwhir.Pinning
import Zkwhir.SlotProb

set_option linter.style.header false
set_option linter.unusedSectionVars false

noncomputable section

open scoped ENNReal

namespace ZkWhir

variable (P : Params) (Fq : Type*) [Field Fq] [Fintype Fq] [Algebra (Fp P) Fq]
  (Dom : Finset (Fp P)) [Nonempty {x // x ∈ Dom}] (S : Stmt P Fq)

/-- **`lem:termslice` hypothesis-failure bound** (tex:549): the cross-form's
nonvanishing hypothesis `ŵ(α₀, c*) ≠ 0` fails with probability at most `k₀/q` over
the challenges, whenever the data column `S.w(·, c*)` is not identically zero.
A direct application of the multivariate Schwartz–Zippel chain to `wHat0`. -/
theorem termslice_hyp_failure_le [Nonempty Fq] [DecidableEq Fq] (c0 : Cube P.m)
    (hw : (fun s => S.w (s, c0)) ≠ (0 : Cube P.k₀ → Fq)) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | wHat0 P Fq Dom S ch c0 = 0} ≤
      (P.k₀ : ℝ≥0∞) / Fintype.card Fq := by
  simp_rw [wHat0_eq_mle]
  exact challenge_mle_α_zero_le P Fq Dom hw

end ZkWhir
