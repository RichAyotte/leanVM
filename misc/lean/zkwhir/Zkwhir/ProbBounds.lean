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

/-- Any finite set of roots of a nonzero polynomial is bounded by its
degree. -/
theorem card_roots_le {F : Type*} [Field F] (g : Polynomial F) (hg : g ≠ 0)
    (s : Finset F) (hs : ∀ a ∈ s, g.eval a = 0) : s.card ≤ g.natDegree := by
  classical
  have hsub : s ⊆ g.roots.toFinset := by
    intro a ha
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hg]
    exact hs a ha
  calc s.card ≤ g.roots.toFinset.card := Finset.card_le_card hsub
    _ ≤ Multiset.card g.roots := g.roots.toFinset_card_le
    _ ≤ g.natDegree := g.card_roots'

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

/-- **Joint bound over all coordinates for uniform functions**: under a uniform
`f : ι → β`, the event that *every* coordinate lands in `B` (with `|B| ≤ k`) has
probability at most `(k / |β|)^{|ι|}`. The event set is the `piFinset` of `B` in
every coordinate, of cardinality `≤ k^{|ι|}`, over `|β|^{|ι|}` total. This is the
multi-coordinate joint-independence bound the SPREAD failure measure needs. -/
theorem uniform_pi_all {ι β : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype β] [Nonempty β] (B : Set β) (k : ℕ)
    (hB : ∀ s : Finset β, (∀ a ∈ s, a ∈ B) → s.card ≤ k) :
    (PMF.uniformOfFintype (ι → β)).toOuterMeasure {f | ∀ i, f i ∈ B} ≤
      (k : ℝ≥0∞) ^ Fintype.card ι / (Fintype.card β : ℝ≥0∞) ^ Fintype.card ι := by
  classical
  set Bf : Finset β := Finset.univ.filter (fun b => b ∈ B) with hBf
  have hBfk : Bf.card ≤ k := hB Bf fun a ha => (Finset.mem_filter.mp ha).2
  have hcount : (Finset.univ.filter (fun f : ι → β => ∀ i, f i ∈ B)).card
      ≤ k ^ Fintype.card ι := by
    have hset : Finset.univ.filter (fun f : ι → β => ∀ i, f i ∈ B)
        = Fintype.piFinset (fun _ => Bf) := by
      ext f
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset,
        hBf]
    rw [hset, Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]
    exact Nat.pow_le_pow_left hBfk _
  refine (uniform_toOuterMeasure_le _ (k ^ Fintype.card ι) (fun s hs => ?_)).trans ?_
  · exact (Finset.card_le_card
      (fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ a, hs a ha⟩)).trans hcount
  · rw [Fintype.card_fun]; push_cast; rfl

/-- **Count of functions hitting per-coordinate sets on a subset** `J`: the number
of `f : ι → β` with `f j ∈ A j` for every `j ∈ J` (each `A j` of size `≤ k`) is at
most `k^{|J|}·|β|^{|ι|−|J|}` (the `piFinset` with `A j` on `J`, all of `β` off `J`).
The Nat count core of the per-coordinate joint measure bound. -/
theorem card_pi_subset_le {ι β : Type*} [Fintype ι] [DecidableEq ι] [Fintype β]
    [DecidableEq β]
    (J : Finset ι) (A : ι → Finset β) (k : ℕ) (hA : ∀ j ∈ J, (A j).card ≤ k) :
    (Finset.univ.filter (fun f : ι → β => ∀ j ∈ J, f j ∈ A j)).card
      ≤ k ^ J.card * Fintype.card β ^ (Fintype.card ι - J.card) := by
  classical
  have hset : Finset.univ.filter (fun f : ι → β => ∀ j ∈ J, f j ∈ A j)
      = Fintype.piFinset (fun j => if j ∈ J then A j else Finset.univ) := by
    ext f
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · intro hf j
      by_cases hj : j ∈ J
      · rw [if_pos hj]; exact hf j hj
      · rw [if_neg hj]; exact Finset.mem_univ _
    · intro hf j hj
      have h := hf j; rwa [if_pos hj] at h
  have hJcard : (Finset.univ.filter (· ∈ J)).card = J.card := by
    congr 1; ext j; simp
  have hNJcard : (Finset.univ.filter (fun j : ι => ¬ j ∈ J)).card
      = Fintype.card ι - J.card := by
    have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := (Finset.univ : Finset ι)) (p := (· ∈ J))
    rw [hJcard, Finset.card_univ] at h
    omega
  rw [hset, Fintype.card_piFinset]
  calc ∏ j, (if j ∈ J then A j else Finset.univ).card
      ≤ ∏ j, (if j ∈ J then k else Fintype.card β) :=
        Finset.prod_le_prod' fun j _ => by
          by_cases hj : j ∈ J
          · simp only [if_pos hj]; exact hA j hj
          · simp [hj]
    _ = k ^ J.card * Fintype.card β ^ (Fintype.card ι - J.card) := by
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, hJcard, hNJcard]

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

/-- **Affine root count** (the inductive core of multivariate Schwartz–Zippel):
an affine function `x ↦ A + x·B` with nonzero slope `B` has at most one root in
`F` (the unique `x = −A/B`). This bounds the per-coordinate root count in the
`SZ` induction that the ε₃ measure bounds require. -/
theorem card_affine_root_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (A B : F) (hB : B ≠ 0) :
    (Finset.univ.filter (fun x : F => A + x * B = 0)).card ≤ 1 := by
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  rw [Finset.mem_filter] at ha hb
  have hab : a * B = b * B := by linear_combination ha.2 - hb.2
  exact mul_right_cancel₀ hB hab

/-- **Fiber count over the first coordinate** (the Schwartz–Zippel induction
recursion): the number of zeros of a predicate on `Fin (n+1) → F` is the sum over
the tail `Fin n → F` of the per-fiber count in the first coordinate `F`. -/
theorem card_filter_pi_succ {F : Type*} [Fintype F] {n : ℕ}
    (P : (Fin (n + 1) → F) → Prop) [DecidablePred P] :
    (Finset.univ.filter P).card =
      ∑ xr : Fin n → F,
        (Finset.univ.filter (fun x0 : F => P (Fin.cons x0 xr))).card := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise (f := fun x => Fin.tail x) (t := Finset.univ)
      (fun a _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun xr _ => ?_
  refine Finset.card_nbij' (fun a => a 0) (fun x0 => Fin.cons x0 xr) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    rw [← ha.2, Fin.cons_self_tail]; exact ha.1
  · intro x0 hx0
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, Fin.tail_cons,
      and_true, true_and] at hx0 ⊢
    exact hx0
  · intro a ha
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at ha
    simp only [← ha.2, Fin.cons_self_tail]
  · intro x0 _
    simp only [Fin.cons_zero]

/-- **Per-fiber count for an affine function** (SZ induction step): the zeros of
`x ↦ A + x·B` number at most `1` when `B ≠ 0`, and at most `|F|` always. -/
theorem card_affine_fiber_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (A B : F) :
    (Finset.univ.filter (fun x : F => A + x * B = 0)).card ≤
      (if B = 0 then Fintype.card F else 1) := by
  by_cases hB : B = 0
  · rw [if_pos hB, ← Finset.card_univ]
    exact Finset.card_filter_le _ _
  · rw [if_neg hB]
    exact card_affine_root_le A B hB

end ZkWhir

