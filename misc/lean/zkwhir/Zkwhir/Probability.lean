/-
Probability toolbox for the zero-knowledge proof: total-variation distance on
`PMF` and its interaction with `bind` and uniform distributions. Everything in
this file is generic (no protocol content) and fully proved.
-/
import Mathlib

set_option linter.style.header false

noncomputable section

open scoped ENNReal

namespace ZkWhir

/-- Total-variation (statistical) distance: `sup_A (P(A) − Q(A)) = ∑ₓ (P x − Q x)⁺`.
Subtraction in `ℝ≥0∞` is truncated, so each summand is a positive part. -/
def statDist {α : Type*} (P Q : PMF α) : ℝ≥0∞ :=
  ∑' x, (P x - Q x)

theorem statDist_self {α : Type*} (P : PMF α) : statDist P P = 0 := by
  simp [statDist]

theorem statDist_le_one {α : Type*} (P Q : PMF α) : statDist P Q ≤ 1 := by
  calc ∑' x, (P x - Q x) ≤ ∑' x, P x := ENNReal.tsum_le_tsum fun _ => tsub_le_self
    _ = 1 := P.tsum_coe

/-- Truncated subtraction of sums is at most the sum of truncated subtractions. -/
theorem tsum_tsub_le_tsum_tsub {ι : Type*} (F G : ι → ℝ≥0∞) :
    (∑' i, F i) - (∑' i, G i) ≤ ∑' i, (F i - G i) := by
  rw [tsub_le_iff_right, ← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum fun i => le_tsub_add

/-- **Conditioning bound.** If two kernels agree on a set `Good`, the
statistical distance of the binds is at most the probability of the
complement. -/
theorem statDist_bind_le_of_eqOn {α β : Type*} (μ : PMF α) (f g : α → PMF β)
    (Good : Set α) (hfg : ∀ a ∈ Good, f a = g a) :
    statDist (μ.bind f) (μ.bind g) ≤ μ.toOuterMeasure Goodᶜ := by
  have h1 : statDist (μ.bind f) (μ.bind g) ≤ ∑' a, μ a * statDist (f a) (g a) := by
    unfold statDist
    calc ∑' x, (μ.bind f x - μ.bind g x)
        ≤ ∑' x, ∑' a, (μ a * f a x - μ a * g a x) := by
          refine ENNReal.tsum_le_tsum fun x => ?_
          rw [PMF.bind_apply, PMF.bind_apply]
          exact tsum_tsub_le_tsum_tsub _ _
      _ = ∑' a, ∑' x, (μ a * f a x - μ a * g a x) := ENNReal.tsum_comm
      _ = ∑' a, μ a * ∑' x, (f a x - g a x) := by
          refine tsum_congr fun a => ?_
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun x => ?_
          exact (ENNReal.mul_sub fun _ _ => PMF.apply_ne_top μ a).symm
  refine h1.trans ?_
  have h2 : ∀ a, μ a * statDist (f a) (g a) ≤ Goodᶜ.indicator (fun b => μ b) a := by
    intro a
    by_cases ha : a ∈ Good
    · rw [hfg a ha, statDist_self, mul_zero]
      exact bot_le
    · rw [Set.indicator_of_mem (Set.mem_compl ha)]
      calc μ a * statDist (f a) (g a) ≤ μ a * 1 := by
            gcongr
            exact statDist_le_one _ _
        _ = μ a := mul_one _
  calc ∑' a, μ a * statDist (f a) (g a)
      ≤ ∑' a, Goodᶜ.indicator (fun b => μ b) a := ENNReal.tsum_le_tsum h2
    _ = μ.toOuterMeasure Goodᶜ := (PMF.toOuterMeasure_apply μ Goodᶜ).symm

/-- Mapping the uniform distribution through a bijection leaves it uniform. -/
theorem map_equiv_uniformOfFintype {α : Type*} [Fintype α] [Nonempty α] (e : α ≃ α) :
    (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype α := by
  apply PMF.ext
  intro b
  rw [PMF.map_apply, PMF.uniformOfFintype_apply]
  rw [tsum_eq_single (e.symm b)]
  · simp [PMF.uniformOfFintype_apply]
  · intro a ha
    have hb : b ≠ e a := fun hb => ha (by simp [hb])
    simp [hb]

end ZkWhir
