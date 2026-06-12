/-
Node genericity probabilities (`lem:nodeprob`), first pieces: a uniform
element of `F_q` lands in the base field with probability exactly `p/q`.

Part of the `GoodSetAbsorption` formalization campaign.
-/
import Mathlib
import Zkwhir.Statement
import Zkwhir.ProbBounds

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

end Peeling

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

end ZkWhir
