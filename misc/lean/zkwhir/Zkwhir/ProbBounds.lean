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
    [Fintype β] [Nonempty β] (i : ι) (B : Set β)
    (k : ℕ) (hB : ∀ s : Finset β, (∀ a ∈ s, a ∈ B) → s.card ≤ k) :
    (PMF.uniformOfFintype (ι → β)).toOuterMeasure {f | f i ∈ B} ≤
      (k : ℝ≥0∞) / Fintype.card β := by
  classical
  set Bf : Finset β := Finset.univ.filter (fun b => b ∈ B) with hBf
  have hBfk : Bf.card ≤ k :=
    hB Bf fun a ha => (Finset.mem_filter.mp ha).2
  have hcount : (Finset.univ.filter (fun f : ι → β => f i ∈ B)).card ≤
      k * Fintype.card β ^ (Fintype.card ι - 1) := by
    have hset : Finset.univ.filter (fun f : ι → β => f i ∈ B) =
        Fintype.piFinset (fun j => if j = i then Bf
          else Finset.univ) := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Fintype.mem_piFinset]
      constructor
      · intro hf j
        by_cases hj : j = i
        · subst hj
          rw [if_pos rfl, hBf, Finset.mem_filter]
          exact ⟨Finset.mem_univ _, hf⟩
        · rw [if_neg hj]
          exact Finset.mem_univ _
      · intro hf
        have h := hf i
        rw [if_pos rfl, hBf, Finset.mem_filter] at h
        exact h.2
    rw [hset, Fintype.card_piFinset,
      ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), if_pos rfl]
    have hprod : ∏ j ∈ Finset.univ.erase i,
        (if j = i then Bf else Finset.univ).card =
        Fintype.card β ^ (Fintype.card ι - 1) := by
      rw [Finset.prod_congr rfl (fun j hj => by
        rw [if_neg (Finset.mem_erase.mp hj).1, Finset.card_univ]),
        Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i),
        Finset.card_univ]
    rw [hprod, mul_comm]
    exact Nat.mul_le_mul_right _ hBfk
  have hβpos : 0 < Fintype.card β := Fintype.card_pos
  have hιcard : Fintype.card (ι → β) =
      Fintype.card β ^ Fintype.card ι := Fintype.card_fun
  refine (uniform_toOuterMeasure_le _
    (k * Fintype.card β ^ (Fintype.card ι - 1))
    (fun s hs => ?_)).trans ?_
  · have hsub : s ⊆ Finset.univ.filter (fun f : ι → β => f i ∈ B) :=
      fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ a, hs a ha⟩
    exact (Finset.card_le_card hsub).trans hcount
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
    calc ((k : ℝ≥0∞) *
          (Fintype.card β : ℝ≥0∞) ^ (Fintype.card ι - 1)) /
          ((Fintype.card β : ℝ≥0∞) ^ (Fintype.card ι - 1) *
            (Fintype.card β : ℝ≥0∞)) =
        (k : ℝ≥0∞) / (Fintype.card β : ℝ≥0∞) := by
          rw [mul_comm ((Fintype.card β : ℝ≥0∞) ^ (Fintype.card ι - 1))
            (Fintype.card β : ℝ≥0∞)]
          exact ENNReal.mul_div_mul_right _ _ hq hqtop
      _ ≤ (k : ℝ≥0∞) / (Fintype.card β : ℝ≥0∞) := le_rfl

/-- **Pair bound for uniform functions**: under a uniform function `ι → β`,
a joint event on two fixed distinct coordinates whose every first-coordinate
fiber has at most `k` outcomes has probability at most `k / |β|`. -/
theorem uniform_pi_pair_le {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] [Nonempty β] [DecidableEq β] {i i' : ι} (hne : i ≠ i')
    (A : Set (β × β)) [DecidablePred (· ∈ A)] (k : ℕ)
    (hA : ∀ b : β, (Finset.univ.filter (fun b' => (b, b') ∈ A)).card ≤ k) :
    (PMF.uniformOfFintype (ι → β)).toOuterMeasure
      {f | (f i, f i') ∈ A} ≤ (k : ℝ≥0∞) / Fintype.card β := by
  classical
  have hn2 : 2 ≤ Fintype.card ι := by
    have : Nontrivial ι := ⟨i, i', hne⟩
    exact Fintype.one_lt_card
  have hβpos : 0 < Fintype.card β := Fintype.card_pos
  -- count the event fiberwise over the first coordinate
  have hcount : (Finset.univ.filter
      (fun f : ι → β => (f i, f i') ∈ A)).card ≤
      Fintype.card β * (k * Fintype.card β ^ (Fintype.card ι - 2)) := by
    rw [Finset.card_eq_sum_card_fiberwise
      (f := fun f : ι → β => f i) (t := Finset.univ)
      (fun f _ => Finset.mem_univ _)]
    refine (Finset.sum_le_card_nsmul _ _
      (k * Fintype.card β ^ (Fintype.card ι - 2)) fun b _ => ?_).trans
      (by rw [Finset.card_univ, smul_eq_mul])
    -- each fiber embeds in a product set
    have hsub : (Finset.univ.filter
        (fun f : ι → β => (f i, f i') ∈ A)).filter
          (fun f => f i = b) ⊆
        Fintype.piFinset (fun j => if j = i then {b}
          else if j = i' then Finset.univ.filter (fun b' => (b, b') ∈ A)
          else Finset.univ) := by
      intro f hf
      obtain ⟨hf1, hf2⟩ := Finset.mem_filter.mp hf
      have hfA : (f i, f i') ∈ A := (Finset.mem_filter.mp hf1).2
      rw [Fintype.mem_piFinset]
      intro j
      by_cases hj : j = i
      · subst hj
        rw [if_pos rfl, Finset.mem_singleton]
        exact hf2
      · rw [if_neg hj]
        by_cases hj' : j = i'
        · subst hj'
          rw [if_pos rfl, Finset.mem_filter]
          rw [hf2] at hfA
          exact ⟨Finset.mem_univ _, hfA⟩
        · rw [if_neg hj']
          exact Finset.mem_univ _
    refine (Finset.card_le_card hsub).trans ?_
    rw [Fintype.card_piFinset,
      ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), if_pos rfl,
      Finset.card_singleton, mul_one]
    have hi'mem : i' ∈ Finset.univ.erase i :=
      Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
    rw [← Finset.prod_erase_mul _ _ hi'mem, if_neg hne.symm, if_pos rfl]
    have hrest : ∏ j ∈ (Finset.univ.erase i).erase i',
        (if j = i then ({b} : Finset β)
          else if j = i' then Finset.univ.filter (fun b' => (b, b') ∈ A)
          else Finset.univ).card = Fintype.card β ^ (Fintype.card ι - 2) := by
      rw [Finset.prod_congr rfl (fun j hj => by
        obtain ⟨hj2, hj1⟩ := Finset.mem_erase.mp hj
        rw [if_neg (Finset.mem_erase.mp hj1).1, if_neg hj2,
          Finset.card_univ]), Finset.prod_const,
        Finset.card_erase_of_mem hi'mem,
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
      all_goals exact congrArg (Fintype.card β ^ ·) (by omega)
    rw [hrest, mul_comm]
    exact Nat.mul_le_mul_right _ (hA b)
  -- convert to the probability bound
  refine (uniform_toOuterMeasure_le _
    (Fintype.card β * (k * Fintype.card β ^ (Fintype.card ι - 2)))
    (fun s hs => ?_)).trans ?_
  · have hsub : s ⊆ Finset.univ.filter
        (fun f : ι → β => (f i, f i') ∈ A) :=
      fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ a, hs a ha⟩
    exact (Finset.card_le_card hsub).trans hcount
  · rw [Fintype.card_fun]
    have hsplit : Fintype.card β ^ Fintype.card ι =
        (Fintype.card β * Fintype.card β ^ (Fintype.card ι - 2)) *
          Fintype.card β := by
      rw [mul_comm (Fintype.card β) _, ← pow_succ, ← pow_succ]
      congr 1
      omega
    rw [hsplit]
    push_cast
    have hq : (Fintype.card β : ℝ≥0∞) *
        (Fintype.card β : ℝ≥0∞) ^ (Fintype.card ι - 2) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast hβpos.ne')
        (pow_ne_zero _ (by exact_mod_cast hβpos.ne'))
    have hqtop : (Fintype.card β : ℝ≥0∞) *
        (Fintype.card β : ℝ≥0∞) ^ (Fintype.card ι - 2) ≠ ⊤ :=
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
        (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
    calc (Fintype.card β : ℝ≥0∞) *
          ((k : ℝ≥0∞) * (Fintype.card β : ℝ≥0∞) ^ (Fintype.card ι - 2)) /
          ((Fintype.card β : ℝ≥0∞) *
            (Fintype.card β : ℝ≥0∞) ^ (Fintype.card ι - 2) *
            (Fintype.card β : ℝ≥0∞)) =
        (k : ℝ≥0∞) * ((Fintype.card β : ℝ≥0∞) *
            (Fintype.card β : ℝ≥0∞) ^ (Fintype.card ι - 2)) /
          ((Fintype.card β : ℝ≥0∞) *
            ((Fintype.card β : ℝ≥0∞) *
              (Fintype.card β : ℝ≥0∞) ^ (Fintype.card ι - 2))) := by
          congr 1 <;> ring
      _ = (k : ℝ≥0∞) / (Fintype.card β : ℝ≥0∞) :=
          ENNReal.mul_div_mul_right _ _ hq hqtop
      _ ≤ (k : ℝ≥0∞) / (Fintype.card β : ℝ≥0∞) := le_rfl

end ZkWhir

