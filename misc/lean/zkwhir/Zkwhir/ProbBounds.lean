/-
Probability bounds for the good-set accounting (`cor:restart`): conditional
bounds through `PMF.bind`, counting bounds for uniform sampling, and the
Schwartz–Zippel-type bound for univariate root events. Everything here is
generic (no protocol content) and fully proved.

Part of the `GoodSetAbsorption` formalization campaign.
-/
import Mathlib

set_option linter.style.header false

noncomputable section

open scoped ENNReal

namespace ZkWhir

/-- **Conditional bound through `bind`**: if every conditional law gives the
event probability at most `c`, so does the compound law. -/
theorem toOuterMeasure_bind_le {α β : Type*} (p : PMF α) (f : α → PMF β)
    (E : Set β) (c : ℝ≥0∞) (h : ∀ a, (f a).toOuterMeasure E ≤ c) :
    (p.bind f).toOuterMeasure E ≤ c := by
  rw [PMF.toOuterMeasure_bind_apply]
  calc ∑' a, p a * (f a).toOuterMeasure E
      ≤ ∑' a, p a * c := ENNReal.tsum_le_tsum fun a => by gcongr; exact h a
    _ = (∑' a, p a) * c := ENNReal.tsum_mul_right
    _ = c := by rw [p.tsum_coe, one_mul]

/-- Conditional bound through `bind` when the event is cut out by the first
coordinate: bound by the probability that the prefix is bad, plus a uniform
conditional bound on the good prefixes. -/
theorem toOuterMeasure_bind_le_add {α β : Type*} (p : PMF α) (f : α → PMF β)
    (E : Set β) (A : Set α) (c : ℝ≥0∞)
    (h : ∀ a ∉ A, (f a).toOuterMeasure E ≤ c) :
    (p.bind f).toOuterMeasure E ≤ p.toOuterMeasure A + c := by
  have hle1 : ∀ q : PMF β, q.toOuterMeasure E ≤ 1 := by
    intro q
    rw [PMF.toOuterMeasure_apply]
    calc ∑' b, E.indicator q b ≤ ∑' b, q b :=
        ENNReal.tsum_le_tsum fun b => by by_cases hb : b ∈ E <;> simp [hb]
      _ = 1 := q.tsum_coe
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply]
  calc ∑' a, p a * (f a).toOuterMeasure E
      ≤ ∑' a, (A.indicator (fun b => p b) a + p a * c) := by
        refine ENNReal.tsum_le_tsum fun a => ?_
        by_cases ha : a ∈ A
        · rw [Set.indicator_of_mem ha]
          calc p a * (f a).toOuterMeasure E ≤ p a * 1 := by
                gcongr
                exact hle1 _
            _ = p a := mul_one _
            _ ≤ p a + p a * c := le_add_of_nonneg_right bot_le
        · rw [Set.indicator_of_notMem ha]
          calc p a * (f a).toOuterMeasure E ≤ p a * c := by
                gcongr
                exact h a ha
            _ ≤ 0 + p a * c := (zero_add _).symm.le
      _ = (∑' a, A.indicator (fun b => p b) a) + ∑' a, p a * c :=
        ENNReal.tsum_add
      _ = (∑' a, A.indicator (fun b => p b) a) + c := by
        rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]

/-- A deterministic outcome misses an event it is not in. -/
theorem toOuterMeasure_pure_eq_zero {α : Type*} {a : α} {E : Set α}
    (h : a ∉ E) : (PMF.pure a).toOuterMeasure E = 0 := by
  rw [PMF.toOuterMeasure_pure_apply, if_neg h]

/-- A compound law misses an event that every conditional law misses. -/
theorem toOuterMeasure_bind_eq_zero {α β : Type*} {p : PMF α}
    {f : α → PMF β} {E : Set β}
    (h : ∀ a, (f a).toOuterMeasure E = 0) :
    (p.bind f).toOuterMeasure E = 0 :=
  le_antisymm (toOuterMeasure_bind_le p f E 0 fun a => (h a).le) bot_le

/-- **Counting bound for uniform sampling**: an event with at most `k`
outcomes has probability at most `k / |α|`. -/
theorem uniform_toOuterMeasure_le {α : Type*} [Fintype α] [Nonempty α]
    (E : Set α) (k : ℕ) (hcard : ∀ (s : Finset α), (∀ a ∈ s, a ∈ E) →
      s.card ≤ k) :
    (PMF.uniformOfFintype α).toOuterMeasure E ≤ k / Fintype.card α := by
  classical
  rw [PMF.toOuterMeasure_apply, tsum_fintype]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ E)
    (E.indicator (PMF.uniformOfFintype α))]
  have hzero : ∑ a ∈ Finset.univ.filter (¬ · ∈ E),
      E.indicator (PMF.uniformOfFintype α) a = 0 :=
    Finset.sum_eq_zero fun a ha => Set.indicator_of_notMem
      (Finset.mem_filter.mp ha).2 _
  rw [hzero, add_zero]
  have hval : ∀ a ∈ Finset.univ.filter (· ∈ E),
      E.indicator (PMF.uniformOfFintype α) a =
        (Fintype.card α : ℝ≥0∞)⁻¹ := by
    intro a ha
    rw [Set.indicator_of_mem (Finset.mem_filter.mp ha).2,
      PMF.uniformOfFintype_apply]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul]
  have hk : ((Finset.univ.filter (· ∈ E)).card : ℝ≥0∞) ≤ (k : ℝ≥0∞) := by
    exact_mod_cast hcard _ fun a ha => (Finset.mem_filter.mp ha).2
  calc ((Finset.univ.filter (· ∈ E)).card : ℝ≥0∞) *
        (Fintype.card α : ℝ≥0∞)⁻¹
      ≤ (k : ℝ≥0∞) * (Fintype.card α : ℝ≥0∞)⁻¹ := by gcongr
    _ = (k : ℝ≥0∞) / Fintype.card α := rfl

/-- **Univariate Schwartz–Zippel**: a nonzero polynomial of degree at most
`d` vanishes at a uniform point with probability at most `d / |F|`. -/
theorem uniform_root_bound {F : Type*} [Field F] [Fintype F] [Nonempty F]
    (g : Polynomial F) (hg : g ≠ 0) (d : ℕ) (hd : g.natDegree ≤ d) :
    (PMF.uniformOfFintype F).toOuterMeasure {x | g.eval x = 0} ≤
      d / Fintype.card F := by
  classical
  refine uniform_toOuterMeasure_le _ d fun s hs => ?_
  have hsub : s ⊆ g.roots.toFinset := by
    intro a ha
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hg]
    exact hs a ha
  calc s.card ≤ g.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card g.roots := g.roots.toFinset_card_le
    _ ≤ g.natDegree := g.card_roots'
    _ ≤ d := hd

/-- **Coordinate bound for uniform functions**: under a uniform function
`ι → β`, the event that one fixed coordinate lands in a `k`-element set has
probability at most `k / |β|`. -/
theorem uniform_pi_coord_le {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] [Nonempty β] (i : ι) (B : Set β) [DecidablePred (· ∈ B)]
    (k : ℕ) (hB : B.toFinset.card ≤ k) :
    (PMF.uniformOfFintype (ι → β)).toOuterMeasure {f | f i ∈ B} ≤
      (k : ℝ≥0∞) / Fintype.card β := by
  classical
  have hcount : (Finset.univ.filter (fun f : ι → β => f i ∈ B)).card =
      B.toFinset.card * Fintype.card β ^ (Fintype.card ι - 1) := by
    have hset : Finset.univ.filter (fun f : ι → β => f i ∈ B) =
        Fintype.piFinset (fun j => if j = i then B.toFinset
          else Finset.univ) := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Fintype.mem_piFinset]
      constructor
      · intro hf j
        by_cases hj : j = i
        · subst hj
          rw [if_pos rfl, Set.mem_toFinset]
          exact hf
        · rw [if_neg hj]
          exact Finset.mem_univ _
      · intro hf
        have := hf i
        rw [if_pos rfl, Set.mem_toFinset] at this
        exact this
    rw [hset, Fintype.card_piFinset,
      ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), if_pos rfl]
    have hprod : ∏ j ∈ Finset.univ.erase i,
        (if j = i then B.toFinset else Finset.univ).card =
        Fintype.card β ^ (Fintype.card ι - 1) := by
      rw [Finset.prod_congr rfl (fun j hj => by
        rw [if_neg (Finset.mem_erase.mp hj).1, Finset.card_univ]),
        Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ]
    rw [hprod, mul_comm]
  have hβpos : 0 < Fintype.card β := Fintype.card_pos
  have hιcard : Fintype.card (ι → β) =
      Fintype.card β ^ Fintype.card ι := Fintype.card_fun
  refine (uniform_toOuterMeasure_le _
    (B.toFinset.card * Fintype.card β ^ (Fintype.card ι - 1))
    (fun s hs => ?_)).trans ?_
  · have hsub : s ⊆ Finset.univ.filter (fun f : ι → β => f i ∈ B) :=
      fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ a, hs a ha⟩
    calc s.card ≤ _ := Finset.card_le_card hsub
      _ = _ := hcount
  · rw [hιcard]
    have hi' : Fintype.card ι ≠ 0 := by
      intro hι
      exact ((Fintype.card_eq_zero_iff.mp hι).false i).elim
    have hsplit : Fintype.card β ^ Fintype.card ι =
        Fintype.card β ^ (Fintype.card ι - 1) * Fintype.card β := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hsplit]
    push_cast
    have hq : (Fintype.card β : ℝ≥0∞) ^ (Fintype.card ι - 1) ≠ 0 :=
      pow_ne_zero _ (by exact_mod_cast hβpos.ne')
    have hqtop : (Fintype.card β : ℝ≥0∞) ^ (Fintype.card ι - 1) ≠ ⊤ :=
      ENNReal.pow_ne_top (ENNReal.natCast_ne_top _)
    calc ((B.toFinset.card : ℝ≥0∞) *
          (Fintype.card β : ℝ≥0∞) ^ (Fintype.card ι - 1)) /
          ((Fintype.card β : ℝ≥0∞) ^ (Fintype.card ι - 1) *
            (Fintype.card β : ℝ≥0∞)) =
        (B.toFinset.card : ℝ≥0∞) / (Fintype.card β : ℝ≥0∞) := by
          rw [mul_comm ((Fintype.card β : ℝ≥0∞) ^ (Fintype.card ι - 1))
            (Fintype.card β : ℝ≥0∞)]
          exact ENNReal.mul_div_mul_right _ _ hq hqtop
      _ ≤ (k : ℝ≥0∞) / (Fintype.card β : ℝ≥0∞) := by
          gcongr

end ZkWhir

