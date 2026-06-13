/-
Node genericity probabilities (`lem:nodeprob`), first pieces: a uniform
element of `F_q` lands in the base field with probability exactly `p/q`.

Part of the `GoodSetAbsorption` formalization campaign.
-/
import Mathlib
import Zkwhir.Statement
import Zkwhir.ProbBounds
import Zkwhir.ViewSolve

set_option linter.style.header false
set_option linter.unusedSectionVars false

noncomputable section

open scoped ENNReal

namespace ZkWhir

variable (P : Params) (Fq : Type*) [Field Fq] [Fintype Fq]
  [Algebra (Fp P) Fq] (Dom : Finset (Fp P)) [Nonempty {x // x ∈ Dom}]

/-! ## Coordinate peeling for the challenge distribution -/

section Peeling

variable [Nonempty Fq]

/-- An event on the commitment out-of-domain points is bounded by its
marginal probability. -/
theorem challenge_z_event_le (A : Set (Fin 2 → Fq)) (c : ℝ≥0∞)
    (hA : (PMF.uniformOfFintype (Fin 2 → Fq)).toOuterMeasure A ≤ c) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ch.z ∈ A} ≤ c := by
  unfold challengePMF
  refine (toOuterMeasure_bind_le_add _ _ _ A 0 ?_).trans ?_
  · intro z hz
    refine le_of_eq (toOuterMeasure_bind_eq_zero fun γ => ?_)
    refine toOuterMeasure_bind_eq_zero fun α => ?_
    refine toOuterMeasure_bind_eq_zero fun zf => ?_
    refine toOuterMeasure_bind_eq_zero fun qs => ?_
    exact toOuterMeasure_pure_eq_zero (by simpa using hz)
  · rw [add_zero]
    exact hA

/-- An event on the `f̂₁` out-of-domain points is bounded by its marginal
probability. -/
theorem challenge_zf_event_le (A : Set (Fin P.s₁ → Fq)) (c : ℝ≥0∞)
    (hA : (PMF.uniformOfFintype (Fin P.s₁ → Fq)).toOuterMeasure A ≤ c) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ch.zf ∈ A} ≤ c := by
  unfold challengePMF
  refine toOuterMeasure_bind_le _ _ _ c fun z => ?_
  refine toOuterMeasure_bind_le _ _ _ c fun γ => ?_
  refine toOuterMeasure_bind_le _ _ _ c fun α => ?_
  refine (toOuterMeasure_bind_le_add _ _ _ A 0 ?_).trans ?_
  · intro zf hzf
    refine le_of_eq (toOuterMeasure_bind_eq_zero fun qs => ?_)
    exact toOuterMeasure_pure_eq_zero (by simpa using hzf)
  · rw [add_zero]
    exact hA

/-- A joint event on the commitment and `f̂₁` out-of-domain points is bounded
by a uniform conditional bound. -/
theorem challenge_z_zf_event_le
    (A : Set ((Fin 2 → Fq) × (Fin P.s₁ → Fq))) (c : ℝ≥0∞)
    (hA : ∀ z, (PMF.uniformOfFintype (Fin P.s₁ → Fq)).toOuterMeasure
      {zf | (z, zf) ∈ A} ≤ c) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | (ch.z, ch.zf) ∈ A} ≤ c := by
  unfold challengePMF
  refine toOuterMeasure_bind_le _ _ _ c fun z => ?_
  refine toOuterMeasure_bind_le _ _ _ c fun γ => ?_
  refine toOuterMeasure_bind_le _ _ _ c fun α => ?_
  refine (toOuterMeasure_bind_le_add _ _ _ {zf | (z, zf) ∈ A} 0 ?_).trans ?_
  · intro zf hzf
    refine le_of_eq (toOuterMeasure_bind_eq_zero fun qs => ?_)
    exact toOuterMeasure_pure_eq_zero (by simpa using hzf)
  · rw [add_zero]
    exact hA z

/-- An event on the batching scalar is bounded by its marginal probability. -/
theorem challenge_γ_event_le (A : Set Fq) (c : ℝ≥0∞)
    (hA : (PMF.uniformOfFintype Fq).toOuterMeasure A ≤ c) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ch.γ ∈ A} ≤ c := by
  unfold challengePMF
  refine toOuterMeasure_bind_le _ _ _ c fun z => ?_
  refine (toOuterMeasure_bind_le_add _ _ _ A 0 ?_).trans ?_
  · intro γ hγ
    refine le_of_eq (toOuterMeasure_bind_eq_zero fun α => ?_)
    refine toOuterMeasure_bind_eq_zero fun zf => ?_
    refine toOuterMeasure_bind_eq_zero fun qs => ?_
    exact toOuterMeasure_pure_eq_zero (by simpa using hγ)
  · rw [add_zero]
    exact hA

/-- **The `γ = 0` bound**: the batching scalar vanishes with probability at
most `1/q`. -/
theorem challenge_gamma_zero_le :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ch.γ = 0} ≤ 1 / (fieldCard Fq : ℝ≥0∞) := by
  have hev : {ch : Challenges P Fq Dom | ch.γ = 0} =
      {ch : Challenges P Fq Dom | ch.γ ∈ ({0} : Set Fq)} := by
    ext ch; simp
  rw [hev]
  refine challenge_γ_event_le P Fq Dom _ _ ?_
  refine (uniform_toOuterMeasure_le ({0} : Set Fq) 1 fun s hs => ?_).trans ?_
  · calc s.card ≤ ({0} : Finset Fq).card :=
          Finset.card_le_card fun a ha =>
            Finset.mem_singleton.mpr (Set.mem_singleton_iff.mp (hs a ha))
      _ = 1 := Finset.card_singleton 0
  · rw [Nat.cast_one]
    rfl

end Peeling

/-- **`eqf(·, y)` has at most one root** (char ≠ 2): it is a degree-≤1
nonzero polynomial. -/
theorem eqf_root_card (h2 : (2 : Fq) ≠ 0) (y : Fq) (s : Finset Fq)
    (hs : ∀ a ∈ s, eqf Fq a y = 0) : s.card ≤ 1 :=
  (card_roots_le _ (eqf_poly_left_ne_zero Fq h2 y) s
    (fun a ha => by rw [← eqf_eq_eval Fq]; exact hs a ha)).trans
    (eqf_poly_natDegree Fq y)

/-- **Coordinate event on the sumcheck challenges**: an event on a single
`α`-coordinate, with a `z`-dependent target set, is bounded by its uniform
marginal. -/
theorem challenge_α_coord_le (i : Fin P.k₀) (B : (Fin 2 → Fq) → Set Fq)
    (c : ℝ≥0∞)
    (hB : ∀ z : Fin 2 → Fq, (PMF.uniformOfFintype (Fin P.k₀ → Fq)).toOuterMeasure
      {α : Fin P.k₀ → Fq | α i ∈ B z} ≤ c) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ch.α i ∈ B ch.z} ≤ c := by
  unfold challengePMF
  refine toOuterMeasure_bind_le _ _ _ c fun z => ?_
  refine toOuterMeasure_bind_le _ _ _ c fun γ => ?_
  refine (toOuterMeasure_bind_le_add _ _ _ {α : Fin P.k₀ → Fq | α i ∈ B z} 0
    ?_).trans ?_
  · intro α hα
    refine le_of_eq (toOuterMeasure_bind_eq_zero fun zf => ?_)
    refine toOuterMeasure_bind_eq_zero fun qs => ?_
    exact toOuterMeasure_pure_eq_zero (by simpa using hα)
  · rw [add_zero]
    exact hB z

/-- **Per-factor α-root bound**: a single `eqf(α_i, z_j^{2^i})` vanishes with
probability at most `1/q`. -/
theorem challenge_alpha_eqf_root_le (h2 : (2 : Fq) ≠ 0) (i : Fin P.k₀)
    (j : Fin 2) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom |
        eqf Fq (ch.α i) (powSeq (ch.z j) P.k₀ i) = 0} ≤
      1 / (fieldCard Fq : ℝ≥0∞) := by
  refine challenge_α_coord_le P Fq Dom i
    (fun z => {a : Fq | eqf Fq a (powSeq (z j) P.k₀ i) = 0}) _ (fun z => ?_)
  refine (uniform_pi_coord_le i {a : Fq | eqf Fq a (powSeq (z j) P.k₀ i) = 0} 1
    (fun s hs => eqf_root_card Fq h2 (powSeq (z j) P.k₀ i) s hs)).trans ?_
  simp [fieldCard]

/-- **α-prefix vanishing bound**: the product of `eqf(α_i, z_j^{2^i})` over
`i < m` vanishes with probability at most `k₀/q`. -/
theorem alpha_prefix_zero_le (h2 : (2 : Fq) ≠ 0) (j : Fin 2) (m : Fin P.k₀) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom |
        (∏ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < m),
          eqf Fq (ch.α i) (powSeq (ch.z j) P.k₀ i)) = 0} ≤
      (P.k₀ : ℝ≥0∞) / (fieldCard Fq : ℝ≥0∞) := by
  classical
  have hsub : {ch : Challenges P Fq Dom |
      (∏ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < m),
        eqf Fq (ch.α i) (powSeq (ch.z j) P.k₀ i)) = 0} ⊆
      ⋃ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < m),
        {ch : Challenges P Fq Dom |
          eqf Fq (ch.α i) (powSeq (ch.z j) P.k₀ i) = 0} := by
    intro ch hch
    simp only [Set.mem_setOf_eq, Finset.prod_eq_zero_iff] at hch
    obtain ⟨i, hi, hi0⟩ := hch
    exact Set.mem_biUnion hi hi0
  refine (MeasureTheory.measure_mono hsub).trans ?_
  refine (MeasureTheory.measure_biUnion_finset_le _ _).trans ?_
  calc ∑ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < m),
        (challengePMF P Fq Dom).toOuterMeasure
          {ch : Challenges P Fq Dom |
            eqf Fq (ch.α i) (powSeq (ch.z j) P.k₀ i) = 0}
      ≤ ∑ _i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < m),
          1 / (fieldCard Fq : ℝ≥0∞) :=
        Finset.sum_le_sum fun i _ => challenge_alpha_eqf_root_le P Fq Dom h2 i j
    _ ≤ ∑ _i : Fin P.k₀, 1 / (fieldCard Fq : ℝ≥0∞) :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
    _ = (P.k₀ : ℝ≥0∞) * (1 / (fieldCard Fq : ℝ≥0∞)) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    _ = (P.k₀ : ℝ≥0∞) / (fieldCard Fq : ℝ≥0∞) := by rw [mul_one_div]

/-- **Exact count of roots of unity in a finite field**:
`#{x : x^m = 1} = gcd(m, q − 1)`. -/
theorem card_pow_eq_one_eq_gcd {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] (m : ℕ) (hm : 0 < m) :
    (Finset.univ.filter (fun x : F => x ^ m = 1)).card =
      Nat.gcd m (Fintype.card F - 1) := by
  classical
  set q1 := Fintype.card F - 1 with hq1
  set n := Nat.gcd m q1 with hn
  have hq1pos : 0 < q1 := by
    have := Fintype.one_lt_card (α := F)
    omega
  have hnpos : 0 < n := Nat.gcd_pos_of_pos_left _ hm
  have hndvd : n ∣ q1 := Nat.gcd_dvd_right _ _
  -- the `m`-th roots of unity are exactly the `n`-th roots of unity
  have hset : Finset.univ.filter (fun x : F => x ^ m = 1) =
      Finset.univ.filter (fun x : F => x ^ n = 1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hx
      have hx0 : x ≠ 0 := by
        intro h0
        rw [h0, zero_pow (by omega)] at hx
        exact zero_ne_one hx
      have hq : x ^ q1 = 1 := FiniteField.pow_card_sub_one_eq_one x hx0
      exact pow_gcd_eq_one.mpr ⟨hx, hq⟩
    · intro hx
      calc x ^ m = (x ^ n) ^ (m / n) := by
            rw [← pow_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)]
        _ = 1 := by rw [hx, one_pow]
  rw [hset]
  -- a primitive `n`-th root of unity from a generator of the units
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hordg : orderOf g = q1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      Fintype.card_units]
  set ζu : Fˣ := g ^ (q1 / n) with hζu
  have hordζu : orderOf ζu = n := by
    rw [hζu, orderOf_pow, hordg]
    have hgcd : Nat.gcd q1 (q1 / n) = q1 / n :=
      Nat.gcd_eq_right (Nat.div_dvd_of_dvd hndvd)
    rw [hgcd, Nat.div_div_self hndvd (by omega)]
  have hordζ : orderOf ((ζu : F)) = n := by
    rw [orderOf_units, hordζu]
  -- upper bound: at most `n` roots of `X^n − 1`
  have hupper : (Finset.univ.filter (fun x : F => x ^ n = 1)).card ≤ n := by
    have hsub : Finset.univ.filter (fun x : F => x ^ n = 1) ⊆
        (Polynomial.nthRoots n (1 : F)).toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hnpos]
      exact (Finset.mem_filter.mp hx).2
    calc (Finset.univ.filter (fun x : F => x ^ n = 1)).card
        ≤ (Polynomial.nthRoots n (1 : F)).toFinset.card :=
          Finset.card_le_card hsub
      _ ≤ Multiset.card (Polynomial.nthRoots n (1 : F)) :=
          (Polynomial.nthRoots n (1 : F)).toFinset_card_le
      _ ≤ n := Polynomial.card_nthRoots n 1
  -- lower bound: the powers of the primitive root
  have hlower : n ≤ (Finset.univ.filter (fun x : F => x ^ n = 1)).card := by
    have hinj : Set.InjOn (fun i => ((ζu : F)) ^ i) (Finset.range n) := by
      intro i hi j hj hij
      simp only [Finset.coe_range, Set.mem_Iio] at hi hj
      exact pow_injOn_Iio_orderOf (by rwa [hordζ]) (by rwa [hordζ]) hij
    have himg : (Finset.range n).image (fun i => ((ζu : F)) ^ i) ⊆
        Finset.univ.filter (fun x : F => x ^ n = 1) := by
      intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← pow_mul, mul_comm, pow_mul, ← hordζ, pow_orderOf_eq_one, one_pow]
    calc n = ((Finset.range n).image (fun i => ((ζu : F)) ^ i)).card := by
          rw [Finset.card_image_of_injOn hinj, Finset.card_range]
      _ ≤ _ := Finset.card_le_card himg
  omega

/-- **The power-map preimage count** (`lem:nodeprob`): when `N ∣ p − 1` and
`N` is coprime to `(q−1)/(p−1)`, exactly `p` elements of `F_q` have their
`N`-th power in the base field. -/
theorem card_pow_mem_base [DecidableEq Fq] (N : ℕ) (hN : 0 < N)
    (hpdvd : (P.p - 1) ∣ (Fintype.card Fq - 1))
    (hcop : Nat.Coprime N ((Fintype.card Fq - 1) / (P.p - 1))) :
    (Finset.univ.filter
      (fun z : Fq => z ^ N ∈ Set.range (algebraMap (Fp P) Fq))).card =
      P.p := by
  classical
  have hp2 := P.pPrime.two_le
  have hp1 : 0 < P.p - 1 := by omega
  set q1 := Fintype.card Fq - 1 with hq1
  set M := q1 / (P.p - 1) with hM
  have hq1M : (P.p - 1) * M = q1 := Nat.mul_div_cancel' hpdvd
  -- the nonzero base elements are exactly the `(p−1)`-th roots of unity
  have hbase : ((Finset.univ.image (algebraMap (Fp P) Fq)).erase 0) =
      Finset.univ.filter (fun x : Fq => x ^ (P.p - 1) = 1) := by
    have hcard1 : (Finset.univ.filter
        (fun x : Fq => x ^ (P.p - 1) = 1)).card = P.p - 1 := by
      rw [card_pow_eq_one_eq_gcd (P.p - 1) hp1, Nat.gcd_eq_left hpdvd]
    have himg : ((Finset.univ.image (algebraMap (Fp P) Fq)).erase 0) ⊆
        Finset.univ.filter (fun x : Fq => x ^ (P.p - 1) = 1) := by
      intro x hx
      obtain ⟨hx0, hxim⟩ := Finset.mem_erase.mp hx
      obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hxim
      have ha0 : a ≠ 0 := by
        intro h0
        rw [h0, map_zero] at ha
        exact hx0 ha.symm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [← ha, ← map_pow, ZMod.pow_card_sub_one_eq_one ha0, map_one]
    have hcard2 : ((Finset.univ.image (algebraMap (Fp P) Fq)).erase 0).card =
        P.p - 1 := by
      rw [Finset.card_erase_of_mem, Finset.card_image_of_injective _
        (algebraMap (Fp P) Fq).injective, Finset.card_univ, ZMod.card]
      exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, map_zero _⟩
    exact Finset.eq_of_subset_of_card_le himg (by omega)
  -- the event splits off zero, then is a root-of-unity condition
  have hsplit : Finset.univ.filter
      (fun z : Fq => z ^ N ∈ Set.range (algebraMap (Fp P) Fq)) =
      insert 0 (Finset.univ.filter
        (fun z : Fq => z ^ (N * (P.p - 1)) = 1)) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · rintro ⟨a, ha⟩
      by_cases hz : z = 0
      · exact Or.inl hz
      right
      have ha0 : a ≠ 0 := by
        intro h0
        rw [h0, map_zero] at ha
        exact pow_ne_zero N hz ha.symm
      rw [pow_mul, ← ha, ← map_pow, ZMod.pow_card_sub_one_eq_one ha0,
        map_one]
    · rintro (hz | hz)
      · exact ⟨0, by rw [map_zero, hz, zero_pow (by omega)]⟩
      · have hroot : z ^ N ∈ Finset.univ.filter
            (fun x : Fq => x ^ (P.p - 1) = 1) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [← pow_mul]
          exact hz
        rw [← hbase] at hroot
        obtain ⟨a, _, ha⟩ := Finset.mem_image.mp
          (Finset.mem_of_mem_erase hroot)
        exact ⟨a, ha⟩
  rw [hsplit, Finset.card_insert_of_notMem, card_pow_eq_one_eq_gcd _
    (by positivity)]
  · rw [← hq1, ← hq1M, mul_comm N (P.p - 1), Nat.gcd_mul_left,
      hcop.gcd_eq_one, mul_one]
    omega
  · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [zero_pow (by positivity)]
    exact zero_ne_one

/-- A uniform element of `F_q` has its `N`-th power in the base field with
probability at most `p/q` — the commitment-node count of `lem:nodeprob`. -/
theorem uniform_pow_mem_base_le [DecidableEq Fq] [Nonempty Fq] (N : ℕ)
    (hN : 0 < N) (hpdvd : (P.p - 1) ∣ (Fintype.card Fq - 1))
    (hcop : Nat.Coprime N ((Fintype.card Fq - 1) / (P.p - 1))) :
    (PMF.uniformOfFintype Fq).toOuterMeasure
      {z : Fq | z ^ N ∈ Set.range (algebraMap (Fp P) Fq)} ≤
      (P.p : ℝ≥0∞) / Fintype.card Fq := by
  refine uniform_toOuterMeasure_le _ P.p fun s hs => ?_
  have hsub : s ⊆ Finset.univ.filter
      (fun z : Fq => z ^ N ∈ Set.range (algebraMap (Fp P) Fq)) :=
    fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ a, hs a ha⟩
  calc s.card ≤ _ := Finset.card_le_card hsub
    _ = P.p := card_pow_mem_base P Fq N hN hpdvd hcop

/-- A uniform element of `F_q` lies in the base field with probability at
most `p/q`. -/
theorem uniform_mem_base_le [Nonempty Fq] :
    (PMF.uniformOfFintype Fq).toOuterMeasure
      {x | x ∈ Set.range (algebraMap (Fp P) Fq)} ≤
      (P.p : ℝ≥0∞) / Fintype.card Fq := by
  classical
  refine uniform_toOuterMeasure_le _ P.p fun s hs => ?_
  have hsub : s ⊆ Finset.univ.image (algebraMap (Fp P) Fq) := by
    intro a ha
    obtain ⟨b, hb⟩ := hs a ha
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, hb⟩
  calc s.card ≤ (Finset.univ.image (algebraMap (Fp P) Fq)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fp P)).card := Finset.card_image_le
    _ = P.p := by
        rw [Finset.card_univ]
        exact ZMod.card P.p

/-- The base-field elements form a `p`-element set. -/
theorem card_base_range_le [DecidableEq Fq] (s : Finset Fq)
    (hs : ∀ a ∈ s, a ∈ Set.range (algebraMap (Fp P) Fq)) :
    s.card ≤ P.p := by
  have hsub : s ⊆ Finset.univ.image (algebraMap (Fp P) Fq) := by
    intro a ha
    obtain ⟨b, hb⟩ := hs a ha
    exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, hb⟩
  calc s.card ≤ (Finset.univ.image (algebraMap (Fp P) Fq)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.univ : Finset (Fp P)).card := Finset.card_image_le
    _ = P.p := by
        rw [Finset.card_univ]
        exact ZMod.card P.p

/-- **Per-node base-field bound** (`lem:nodeprob`, first count): each of the
`2 + s₁` nodes lands in the base field with probability at most `p/q`. -/
theorem challenge_node_in_base_le [Nonempty Fq]
    (hpdvd : (P.p - 1) ∣ (Fintype.card Fq - 1))
    (hcop : Nat.Coprime (2 ^ P.k₀) ((Fintype.card Fq - 1) / (P.p - 1)))
    (j : Fin (2 + P.s₁)) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom |
        nodes P Fq Dom ch j ∈ Set.range (algebraMap (Fp P) Fq)} ≤
      (P.p : ℝ≥0∞) / Fintype.card Fq := by
  classical
  induction j using Fin.addCases with
  | left j₀ =>
    have hev : {ch : Challenges P Fq Dom |
        nodes P Fq Dom ch (Fin.castAdd P.s₁ j₀) ∈
          Set.range (algebraMap (Fp P) Fq)} =
        {ch : Challenges P Fq Dom | ch.z ∈
          {z : Fin 2 → Fq | z j₀ ^ 2 ^ P.k₀ ∈
            Set.range (algebraMap (Fp P) Fq)}} := by
      ext ch
      simp only [Set.mem_setOf_eq, nodes, Fin.append_left]
    rw [hev]
    refine challenge_z_event_le P Fq Dom _ _ ?_
    have hshape : {z : Fin 2 → Fq | z j₀ ^ 2 ^ P.k₀ ∈
        Set.range (algebraMap (Fp P) Fq)} =
        {z : Fin 2 → Fq | z j₀ ∈
          {w : Fq | w ^ 2 ^ P.k₀ ∈ Set.range (algebraMap (Fp P) Fq)}} := by
      ext z
      simp only [Set.mem_setOf_eq]
    rw [hshape]
    refine uniform_pi_coord_le j₀ _ P.p fun s hs => ?_
    have hsub : s ⊆ Finset.univ.filter (fun w : Fq => w ^ 2 ^ P.k₀ ∈
        Set.range (algebraMap (Fp P) Fq)) :=
      fun a ha => Finset.mem_filter.mpr ⟨Finset.mem_univ a, hs a ha⟩
    exact (Finset.card_le_card hsub).trans
      (card_pow_mem_base P Fq _ (Nat.two_pow_pos _) hpdvd hcop).le
  | right j₁ =>
    have hev : {ch : Challenges P Fq Dom |
        nodes P Fq Dom ch (Fin.natAdd 2 j₁) ∈
          Set.range (algebraMap (Fp P) Fq)} =
        {ch : Challenges P Fq Dom | ch.zf ∈
          {zf : Fin P.s₁ → Fq | zf j₁ ∈
            Set.range (algebraMap (Fp P) Fq)}} := by
      ext ch
      simp only [Set.mem_setOf_eq, nodes, Fin.append_right]
    rw [hev]
    refine challenge_zf_event_le P Fq Dom _ _ ?_
    exact uniform_pi_coord_le j₁ _ P.p fun s hs =>
      card_base_range_le P Fq s hs

/-! ## Conjugate node pairs -/

section Conjugacy

variable [Nonempty Fq] [FiniteDimensional (Fp P) Fq]

/-- The mapped minimal polynomial is monic, hence nonzero. -/
theorem minpoly_map_ne_zero (ν : Fq) :
    (minpoly (Fp P) ν).map (algebraMap (Fp P) Fq) ≠ 0 :=
  ((minpoly.monic (IsIntegral.of_finite _ ν)).map _).ne_zero

theorem minpoly_map_natDegree_le (ν : Fq) :
    ((minpoly (Fp P) ν).map (algebraMap (Fp P) Fq)).natDegree ≤
      Module.finrank (Fp P) Fq := by
  rw [(minpoly.monic (IsIntegral.of_finite _ ν)).natDegree_map]
  exact minpoly.natDegree_le ν

/-- Equal minimal polynomials make the second node a root of the first's
mapped minimal polynomial. -/
theorem eval_minpoly_map_eq_zero {ν ν' : Fq}
    (h : minpoly (Fp P) ν = minpoly (Fp P) ν') :
    ((minpoly (Fp P) ν).map (algebraMap (Fp P) Fq)).eval ν' = 0 := by
  have haev := minpoly.aeval (Fp P) ν'
  rw [← h] at haev
  rwa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] at haev

/-- A finite set of points whose `N`-th powers are roots of the mapped
minimal polynomial has at most `d·N` elements. -/
theorem card_pow_conj_le (ν : Fq) (s : Finset Fq)
    (hs : ∀ w' ∈ s, minpoly (Fp P) ν = minpoly (Fp P) (w' ^ 2 ^ P.k₀)) :
    s.card ≤ Module.finrank (Fp P) Fq * 2 ^ P.k₀ := by
  set g := ((minpoly (Fp P) ν).map (algebraMap (Fp P) Fq)).comp
    (Polynomial.X ^ 2 ^ P.k₀) with hg
  have hgmonic : g.Monic :=
    ((minpoly.monic (IsIntegral.of_finite _ ν)).map _).comp
      (Polynomial.monic_X_pow _)
      (by rw [Polynomial.natDegree_X_pow]; positivity)
  have hgdeg : g.natDegree ≤ Module.finrank (Fp P) Fq * 2 ^ P.k₀ := by
    rw [hg, Polynomial.natDegree_comp, Polynomial.natDegree_X_pow]
    exact Nat.mul_le_mul_right _ (minpoly_map_natDegree_le P Fq ν)
  refine (card_roots_le g hgmonic.ne_zero s fun w' hw' => ?_).trans hgdeg
  rw [hg, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X]
  exact eval_minpoly_map_eq_zero P Fq (hs w' hw')

/-- A finite set of roots of the mapped minimal polynomial has at most `d·N`
elements. -/
theorem card_conj_le (ν : Fq) (s : Finset Fq)
    (hs : ∀ w' ∈ s, minpoly (Fp P) ν = minpoly (Fp P) w') :
    s.card ≤ Module.finrank (Fp P) Fq * 2 ^ P.k₀ := by
  have hd : ((minpoly (Fp P) ν).map (algebraMap (Fp P) Fq)).natDegree ≤
      Module.finrank (Fp P) Fq * 2 ^ P.k₀ :=
    (minpoly_map_natDegree_le P Fq ν).trans
      (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
  refine (card_roots_le _ (minpoly_map_ne_zero P Fq ν) s
    fun w' hw' => ?_).trans hd
  exact eval_minpoly_map_eq_zero P Fq (hs w' hw')

/-- **Per-pair conjugacy bound** (`lem:nodeprob`, second count): two distinct
nodes share a minimal polynomial with probability at most `d·2^k₀ / q`. -/
theorem challenge_node_conj_le (j j' : Fin (2 + P.s₁)) (hne : j ≠ j') :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom |
        minpoly (Fp P) (nodes P Fq Dom ch j) =
        minpoly (Fp P) (nodes P Fq Dom ch j')} ≤
      ((Module.finrank (Fp P) Fq * 2 ^ P.k₀ : ℕ) : ℝ≥0∞) /
        Fintype.card Fq := by
  classical
  induction j using Fin.addCases with
  | left j₀ =>
    induction j' using Fin.addCases with
    | left j₀' =>
      have hne' : j₀ ≠ j₀' := fun h => hne (by rw [h])
      have hev : {ch : Challenges P Fq Dom |
          minpoly (Fp P) (nodes P Fq Dom ch (Fin.castAdd P.s₁ j₀)) =
          minpoly (Fp P) (nodes P Fq Dom ch (Fin.castAdd P.s₁ j₀'))} =
          {ch : Challenges P Fq Dom | ch.z ∈
            {z : Fin 2 → Fq | (z j₀, z j₀') ∈
              {ww : Fq × Fq | minpoly (Fp P) (ww.1 ^ 2 ^ P.k₀) =
                minpoly (Fp P) (ww.2 ^ 2 ^ P.k₀)}}} := by
        ext ch
        simp only [Set.mem_setOf_eq, nodes, Fin.append_left]
      rw [hev]
      refine challenge_z_event_le P Fq Dom _ _ ?_
      refine uniform_pi_pair_le hne' _ _ fun w => ?_
      refine card_pow_conj_le P Fq (w ^ 2 ^ P.k₀) _ fun w' hw' => ?_
      exact (Finset.mem_filter.mp hw').2
    | right j₁ =>
      have hev : {ch : Challenges P Fq Dom |
          minpoly (Fp P) (nodes P Fq Dom ch (Fin.castAdd P.s₁ j₀)) =
          minpoly (Fp P) (nodes P Fq Dom ch (Fin.natAdd 2 j₁))} =
          {ch : Challenges P Fq Dom | (ch.z, ch.zf) ∈
            {zzf : (Fin 2 → Fq) × (Fin P.s₁ → Fq) |
              minpoly (Fp P) (zzf.1 j₀ ^ 2 ^ P.k₀) =
              minpoly (Fp P) (zzf.2 j₁)}} := by
        ext ch
        simp only [Set.mem_setOf_eq, nodes, Fin.append_left,
          Fin.append_right]
      rw [hev]
      refine challenge_z_zf_event_le P Fq Dom _ _ fun z => ?_
      refine uniform_pi_coord_le j₁
        {w' : Fq | minpoly (Fp P) (z j₀ ^ 2 ^ P.k₀) = minpoly (Fp P) w'}
        _ fun s hs => ?_
      exact card_conj_le P Fq _ s hs
  | right j₁ =>
    induction j' using Fin.addCases with
    | left j₀' =>
      have hev : {ch : Challenges P Fq Dom |
          minpoly (Fp P) (nodes P Fq Dom ch (Fin.natAdd 2 j₁)) =
          minpoly (Fp P) (nodes P Fq Dom ch (Fin.castAdd P.s₁ j₀'))} =
          {ch : Challenges P Fq Dom | (ch.z, ch.zf) ∈
            {zzf : (Fin 2 → Fq) × (Fin P.s₁ → Fq) |
              minpoly (Fp P) (zzf.1 j₀' ^ 2 ^ P.k₀) =
              minpoly (Fp P) (zzf.2 j₁)}} := by
        ext ch
        simp only [Set.mem_setOf_eq, nodes, Fin.append_left,
          Fin.append_right, eq_comm]
      rw [hev]
      refine challenge_z_zf_event_le P Fq Dom _ _ fun z => ?_
      refine uniform_pi_coord_le j₁
        {w' : Fq | minpoly (Fp P) (z j₀' ^ 2 ^ P.k₀) = minpoly (Fp P) w'}
        _ fun s hs => ?_
      exact card_conj_le P Fq _ s hs
    | right j₁' =>
      have hne' : j₁ ≠ j₁' := fun h => hne (by rw [h])
      have hev : {ch : Challenges P Fq Dom |
          minpoly (Fp P) (nodes P Fq Dom ch (Fin.natAdd 2 j₁)) =
          minpoly (Fp P) (nodes P Fq Dom ch (Fin.natAdd 2 j₁'))} =
          {ch : Challenges P Fq Dom | ch.zf ∈
            {zf : Fin P.s₁ → Fq | (zf j₁, zf j₁') ∈
              {ww : Fq × Fq | minpoly (Fp P) ww.1 =
                minpoly (Fp P) ww.2}}} := by
        ext ch
        simp only [Set.mem_setOf_eq, nodes, Fin.append_right]
      rw [hev]
      refine challenge_zf_event_le P Fq Dom _ _ ?_
      refine uniform_pi_pair_le hne' _ _ fun w => ?_
      refine card_conj_le P Fq w _ fun w' hw' => ?_
      exact (Finset.mem_filter.mp hw').2

end Conjugacy

/-! ## The node-genericity bound -/

/-- The strict upper triangle of `Fin n × Fin n` has `n.choose 2` elements. -/
theorem card_triangle (n : ℕ) :
    (Finset.univ.filter (fun pr : Fin n × Fin n => pr.1 < pr.2)).card =
      n.choose 2 := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := Prod.snd) (t := Finset.univ) (fun pr _ => Finset.mem_univ _)]
  have hfiber : ∀ j' : Fin n,
      ((Finset.univ.filter (fun pr : Fin n × Fin n => pr.1 < pr.2)).filter
        (fun pr => pr.2 = j')).card = (j' : ℕ) := by
    intro j'
    have hset : (Finset.univ.filter
        (fun pr : Fin n × Fin n => pr.1 < pr.2)).filter
          (fun pr => pr.2 = j') =
        (Finset.Iio j').image (fun i => (i, j')) := by
      ext pr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_image, Finset.mem_Iio]
      constructor
      · rintro ⟨h1, h2⟩
        subst h2
        exact ⟨pr.1, h1, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨hi, rfl⟩
    rw [hset, Finset.card_image_of_injective _
      (fun a b hab => (Prod.mk.injEq _ _ _ _).mp hab |>.1),
      Fin.card_Iio]
  rw [Finset.sum_congr rfl fun j' _ => hfiber j',
    Fin.sum_univ_eq_sum_range (fun i => i), Finset.sum_range_id,
    Nat.choose_two_right]

/-! ## Parameter arithmetic

`q = p^d` makes `(p−1) ∣ (q−1)`, and for odd `d` (and odd `p`) the
cofactor `(q−1)/(p−1) = 1 + p + … + p^(d−1)` is odd, hence coprime to
`2^k₀`. Discharges the counting hypotheses from the protocol parameters. -/

theorem geom_sum_mul_eq (p d : ℕ) (hp : 1 ≤ p) :
    (p - 1) * (∑ i ∈ Finset.range d, p ^ i) = p ^ d - 1 := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [Finset.sum_range_succ, Nat.mul_add, ih]
    have h1 : 1 ≤ p ^ d := Nat.one_le_pow _ _ (by omega)
    have h2 : p ^ (d + 1) = p ^ d * p := pow_succ p d
    have h4 : (p - 1) * p ^ d = p ^ d * p - p ^ d := by
      rw [Nat.sub_mul, one_mul, mul_comm]
    have h5 : p ^ d ≤ p ^ d * p := Nat.le_mul_of_pos_right _ (by omega)
    omega

theorem geom_sum_odd (p d : ℕ) (hpodd : Odd p) (hdodd : Odd d) :
    Odd (∑ i ∈ Finset.range d, p ^ i) := by
  rw [Nat.odd_iff, Finset.sum_nat_mod]
  have hmod : (∑ i ∈ Finset.range d, p ^ i % 2) =
      ∑ _i ∈ Finset.range d, 1 := by
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Nat.odd_iff.mp (Odd.pow hpodd)
  rw [hmod, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  exact Nat.odd_iff.mp hdodd

/-- `(p − 1) ∣ (q − 1)` from `q = p^d`. -/
theorem pdvd_of_card
    (hcard : Fintype.card Fq = P.p ^ Module.finrank (Fp P) Fq) :
    (P.p - 1) ∣ (Fintype.card Fq - 1) := by
  have hp := P.pPrime.two_le
  refine ⟨∑ i ∈ Finset.range (Module.finrank (Fp P) Fq), P.p ^ i, ?_⟩
  rw [hcard, ← geom_sum_mul_eq P.p _ (by omega)]

/-- The cofactor `(q−1)/(p−1)` is coprime to `2^k₀` for odd degree. -/
theorem cop_of_card
    (hcard : Fintype.card Fq = P.p ^ Module.finrank (Fp P) Fq)
    (hdvd2 : 2 ^ P.k₀ ∣ P.p - 1)
    (hdodd : Odd (Module.finrank (Fp P) Fq)) :
    Nat.Coprime (2 ^ P.k₀) ((Fintype.card Fq - 1) / (P.p - 1)) := by
  have hp := P.pPrime.two_le
  have hpne2 : P.p ≠ 2 := by
    intro h2
    rw [h2] at hdvd2
    have hle := Nat.le_of_dvd one_pos hdvd2
    have h2k : 2 ^ 1 ≤ 2 ^ P.k₀ :=
      Nat.pow_le_pow_right (by norm_num) P.k₀_pos
    simp at h2k
    omega
  have hpodd : Odd P.p := P.pPrime.odd_of_ne_two hpne2
  have hM : (Fintype.card Fq - 1) / (P.p - 1) =
      ∑ i ∈ Finset.range (Module.finrank (Fp P) Fq), P.p ^ i := by
    refine Nat.div_eq_of_eq_mul_left (by omega) ?_
    rw [hcard, ← geom_sum_mul_eq P.p _ (by omega), mul_comm]
  rw [hM]
  refine Nat.Coprime.pow_left _ (Nat.prime_two.coprime_iff_not_dvd.mpr ?_)
  intro hdvd
  have hodd := Nat.odd_iff.mp
    (geom_sum_odd P.p (Module.finrank (Fp P) Fq) hpodd hdodd)
  omega

/-- **The node-genericity failure bound** (`lem:nodeprob`): the probability
that `NodeHyp` fails is at most `(2+s₁)·p/q + C(2+s₁,2)·d·2^k₀/q`. -/
theorem nodeHyp_failure_le [Nonempty Fq] [FiniteDimensional (Fp P) Fq]
    (hd : (Module.finrank (Fp P) Fq).Prime)
    (hpdvd : (P.p - 1) ∣ (Fintype.card Fq - 1))
    (hcop : Nat.Coprime (2 ^ P.k₀) ((Fintype.card Fq - 1) / (P.p - 1))) :
    (challengePMF P Fq Dom).toOuterMeasure
      {ch : Challenges P Fq Dom | ¬ NodeHyp P Fq Dom ch} ≤
      ((2 + P.s₁ : ℕ) : ℝ≥0∞) * P.p / Fintype.card Fq +
      (((2 + P.s₁).choose 2 : ℕ) : ℝ≥0∞) *
        ((Module.finrank (Fp P) Fq * 2 ^ P.k₀ : ℕ) : ℝ≥0∞) /
        Fintype.card Fq := by
  classical
  -- failure is covered by the elementary events
  have hsubset : {ch : Challenges P Fq Dom | ¬ NodeHyp P Fq Dom ch} ⊆
      (⋃ j ∈ (Finset.univ : Finset (Fin (2 + P.s₁))),
        {ch : Challenges P Fq Dom |
          nodes P Fq Dom ch j ∈ Set.range (algebraMap (Fp P) Fq)}) ∪
      (⋃ pr ∈ Finset.univ.filter
          (fun pr : Fin (2 + P.s₁) × Fin (2 + P.s₁) => pr.1 < pr.2),
        {ch : Challenges P Fq Dom |
          minpoly (Fp P) (nodes P Fq Dom ch pr.1) =
          minpoly (Fp P) (nodes P Fq Dom ch pr.2)}) := by
    intro ch hch
    simp only [Set.mem_setOf_eq] at hch
    by_cases ha : ∀ j, nodes P Fq Dom ch j ∉
        Set.range (algebraMap (Fp P) Fq)
    · by_cases hc : ∀ j j', j ≠ j' →
          minpoly (Fp P) (nodes P Fq Dom ch j) ≠
          minpoly (Fp P) (nodes P Fq Dom ch j')
      · exact absurd (nodeHyp_of_not_in_base P Fq Dom ch hd ha hc) hch
      · push_neg at hc
        obtain ⟨j, j', hjj', hmin⟩ := hc
        refine Set.mem_union_right _ ?_
        rcases lt_or_gt_of_ne hjj' with hlt | hgt
        · exact Set.mem_biUnion (Finset.mem_filter.mpr
            ⟨Finset.mem_univ ((j, j') : _ × _), hlt⟩) hmin
        · exact Set.mem_biUnion (Finset.mem_filter.mpr
            ⟨Finset.mem_univ ((j', j) : _ × _), hgt⟩) hmin.symm
    · push_neg at ha
      obtain ⟨j, hj⟩ := ha
      exact Set.mem_union_left _ (Set.mem_biUnion (Finset.mem_univ j) hj)
  refine (MeasureTheory.measure_mono hsubset).trans ?_
  refine (MeasureTheory.measure_union_le _ _).trans ?_
  have hb1 : (challengePMF P Fq Dom).toOuterMeasure
      (⋃ j ∈ (Finset.univ : Finset (Fin (2 + P.s₁))),
        {ch : Challenges P Fq Dom |
          nodes P Fq Dom ch j ∈ Set.range (algebraMap (Fp P) Fq)}) ≤
      ((2 + P.s₁ : ℕ) : ℝ≥0∞) * P.p / Fintype.card Fq := by
    refine (MeasureTheory.measure_biUnion_finset_le _ _).trans ?_
    calc ∑ j : Fin (2 + P.s₁), (challengePMF P Fq Dom).toOuterMeasure
          {ch : Challenges P Fq Dom |
            nodes P Fq Dom ch j ∈ Set.range (algebraMap (Fp P) Fq)}
        ≤ ∑ _j : Fin (2 + P.s₁), (P.p : ℝ≥0∞) / Fintype.card Fq :=
          Finset.sum_le_sum fun j _ =>
            challenge_node_in_base_le P Fq Dom hpdvd hcop j
      _ = ((2 + P.s₁ : ℕ) : ℝ≥0∞) * ((P.p : ℝ≥0∞) / Fintype.card Fq) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
      _ = ((2 + P.s₁ : ℕ) : ℝ≥0∞) * P.p / Fintype.card Fq := by
          rw [mul_div_assoc]
  have hb2 : (challengePMF P Fq Dom).toOuterMeasure
      (⋃ pr ∈ Finset.univ.filter
          (fun pr : Fin (2 + P.s₁) × Fin (2 + P.s₁) => pr.1 < pr.2),
        {ch : Challenges P Fq Dom |
          minpoly (Fp P) (nodes P Fq Dom ch pr.1) =
          minpoly (Fp P) (nodes P Fq Dom ch pr.2)}) ≤
      (((2 + P.s₁).choose 2 : ℕ) : ℝ≥0∞) *
        ((Module.finrank (Fp P) Fq * 2 ^ P.k₀ : ℕ) : ℝ≥0∞) /
        Fintype.card Fq := by
    refine (MeasureTheory.measure_biUnion_finset_le _ _).trans ?_
    calc ∑ pr ∈ Finset.univ.filter
          (fun pr : Fin (2 + P.s₁) × Fin (2 + P.s₁) => pr.1 < pr.2),
          (challengePMF P Fq Dom).toOuterMeasure
            {ch : Challenges P Fq Dom |
              minpoly (Fp P) (nodes P Fq Dom ch pr.1) =
              minpoly (Fp P) (nodes P Fq Dom ch pr.2)}
        ≤ ∑ pr ∈ Finset.univ.filter
            (fun pr : Fin (2 + P.s₁) × Fin (2 + P.s₁) => pr.1 < pr.2),
            ((Module.finrank (Fp P) Fq * 2 ^ P.k₀ : ℕ) : ℝ≥0∞) /
              Fintype.card Fq :=
          Finset.sum_le_sum fun pr hpr =>
            challenge_node_conj_le P Fq Dom pr.1 pr.2
              (Fin.ne_of_lt (Finset.mem_filter.mp hpr).2)
      _ = (((2 + P.s₁).choose 2 : ℕ) : ℝ≥0∞) *
            (((Module.finrank (Fp P) Fq * 2 ^ P.k₀ : ℕ) : ℝ≥0∞) /
              Fintype.card Fq) := by
          rw [Finset.sum_const, card_triangle, nsmul_eq_mul]
      _ = (((2 + P.s₁).choose 2 : ℕ) : ℝ≥0∞) *
            ((Module.finrank (Fp P) Fq * 2 ^ P.k₀ : ℕ) : ℝ≥0∞) /
            Fintype.card Fq := by
          rw [mul_div_assoc]
  exact add_le_add hb1 hb2

end ZkWhir
