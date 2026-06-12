/-
`lem:crt` of `zk_leanVM.tex`, formalized: over a finite field extension
`L / K`, a polynomial with `K`-coefficients and degree `< N` can take
arbitrary prescribed values at `t` distinct points of `K` and at `e` points of
`L ∖ K` that are pairwise non-conjugate and generate `L`, provided
`t + d·e ≤ N` (`d = [L : K]`).

Design: explicit interpolants (no polynomial quotients). For a point target,
`ℓ_i(X) · ∏_j m_j(X)` scaled; for a node target, `q(X) · ∏_i (X − x_i) ·
∏_{j' ≠ j} m_{j'}(X)` with `q` a `modByMonic`-reduced preimage under
`aeval (ν j)` (surjective since `ν j` generates `L`).

This file is part of the `GoodSetAbsorption` formalization campaign and is
not yet wired into the root module.
-/
import Mathlib

set_option linter.style.header false

noncomputable section

namespace ZkWhir

open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The minimal polynomial of a point outside (the image of) `K` has no roots
in `K`. -/
theorem minpoly_no_root (ν : L) (hν : ν ∉ Set.range (algebraMap K L))
    (r : K) : (minpoly K ν).eval r ≠ 0 := by
  intro hroot
  have hint : IsIntegral K ν := IsIntegral.of_finite K ν
  have hdvd : X - C r ∣ minpoly K ν := dvd_iff_isRoot.mpr hroot
  obtain ⟨c, hc⟩ := hdvd
  rcases (minpoly.irreducible hint).isUnit_or_isUnit hc with h | h
  · exact (Polynomial.not_isUnit_X_sub_C r) h
  · -- `minpoly = (X - C r) * unit`, both monic up to the unit: `ν = r`.
    have hassoc : Associated (X - C r) (minpoly K ν) :=
      ⟨h.unit, by rw [IsUnit.unit_spec]; exact hc.symm⟩
    have heq : X - C r = minpoly K ν :=
      eq_of_monic_of_associated (monic_X_sub_C r) (minpoly.monic hint) hassoc
    have hz : aeval ν (X - C r) = 0 := by rw [heq]; exact minpoly.aeval K ν
    have hsub : ν - algebraMap K L r = 0 := by simpa using hz
    exact hν ⟨r, (sub_eq_zero.mp hsub).symm⟩

/-- A minimal polynomial does not vanish at a point with a *different*
minimal polynomial (non-conjugacy). -/
theorem minpoly_aeval_ne_zero_of_ne (ν ν' : L)
    (hne : minpoly K ν ≠ minpoly K ν') :
    aeval ν' (minpoly K ν) ≠ 0 := by
  intro h0
  have hint : IsIntegral K ν := IsIntegral.of_finite K ν
  have hint' : IsIntegral K ν' := IsIntegral.of_finite K ν'
  obtain ⟨c, hc⟩ := minpoly.dvd K ν' h0
  rcases (minpoly.irreducible hint).isUnit_or_isUnit hc with h | h
  · exact (minpoly.not_isUnit K ν') h
  · have hassoc : Associated (minpoly K ν') (minpoly K ν) :=
      ⟨h.unit, by rw [IsUnit.unit_spec]; exact hc.symm⟩
    exact hne (eq_of_monic_of_associated (minpoly.monic hint')
      (minpoly.monic hint) hassoc).symm

/-- Evaluation at a generator of the extension is surjective. -/
theorem aeval_surjective (ν : L)
    (hgen : (minpoly K ν).natDegree = Module.finrank K L) :
    Function.Surjective (aeval ν : K[X] → L) := by
  intro y
  have hint : IsIntegral K ν := IsIntegral.of_finite K ν
  have htop : Algebra.adjoin K {ν} = ⊤ := by
    have hfr : Module.finrank K (Algebra.adjoin K {ν}) =
        Module.finrank K L := by
      rw [(Algebra.adjoin.powerBasis hint).finrank,
        Algebra.adjoin.powerBasis_dim, hgen]
    rw [← Algebra.toSubmodule_eq_top]
    exact Submodule.eq_top_of_finrank_eq
      ((Algebra.adjoin K {ν}).finrank_toSubmodule.trans hfr)
  have hy : y ∈ (Polynomial.aeval ν : K[X] →ₐ[K] L).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval, htop]
    exact Algebra.mem_top
  obtain ⟨g, hg⟩ := hy
  exact ⟨g, hg⟩

section Interpolants

variable {t e : ℕ} (x : Fin t → K) (ν : Fin e → L)

/-- Point interpolant: `1` at `x i₀`, `0` at the other points and at every
`ν j`, with `K`-coefficients and degree `< t + d·e`. -/
theorem exists_point_interpolant (hx : Function.Injective x)
    (hν : ∀ j, ν j ∉ Set.range (algebraMap K L)) (i₀ : Fin t) :
    ∃ g : K[X], g.natDegree < t + Module.finrank K L * e ∧
      g.eval (x i₀) = 1 ∧ (∀ i, i ≠ i₀ → g.eval (x i) = 0) ∧
      ∀ j, aeval (ν j) g = 0 := by
  classical
  set ℓ : K[X] := ∏ i ∈ Finset.univ.erase i₀, (X - C (x i)) with hℓ
  set M : K[X] := ∏ j, minpoly K (ν j) with hM
  have hMne : ∀ j, minpoly K (ν j) ≠ 0 := fun j =>
    minpoly.ne_zero (IsIntegral.of_finite K (ν j))
  have hℓval : ℓ.eval (x i₀) ≠ 0 := by
    rw [hℓ, eval_prod]
    refine Finset.prod_ne_zero_iff.mpr fun i hi => ?_
    have : x i₀ ≠ x i := fun h => (Finset.mem_erase.mp hi).1 (hx h).symm
    simpa [sub_eq_zero] using this
  have hMval : M.eval (x i₀) ≠ 0 := by
    rw [hM, eval_prod]
    exact Finset.prod_ne_zero_iff.mpr fun j _ => minpoly_no_root (ν j) (hν j) _
  refine ⟨C ((ℓ.eval (x i₀) * M.eval (x i₀))⁻¹) * (ℓ * M), ?_, ?_, ?_, ?_⟩
  · -- degree bound: `(t − 1) + d·e < t + d·e`
    have hℓdeg : ℓ.natDegree = t - 1 := by
      rw [hℓ, natDegree_prod _ _ fun i _ => X_sub_C_ne_zero (x i)]
      simp [Finset.card_erase_of_mem]
    have hMdeg : M.natDegree ≤ Module.finrank K L * e := by
      rw [hM, natDegree_prod _ _ fun j _ => hMne j]
      calc ∑ j, (minpoly K (ν j)).natDegree ≤ ∑ _j : Fin e, Module.finrank K L :=
            Finset.sum_le_sum fun j _ => minpoly.natDegree_le (ν j)
        _ = Module.finrank K L * e := by
            simp [Finset.sum_const, mul_comm]
    have hbound : (C ((ℓ.eval (x i₀) * M.eval (x i₀))⁻¹) * (ℓ * M)).natDegree ≤
        ℓ.natDegree + M.natDegree := by
      refine natDegree_mul_le.trans ?_
      rw [natDegree_C, zero_add]
      exact natDegree_mul_le
    have ht : 0 < t := i₀.pos
    omega
  · -- value 1 at `x i₀`
    have : (ℓ * M).eval (x i₀) = ℓ.eval (x i₀) * M.eval (x i₀) := eval_mul
    simp only [eval_mul, eval_C]
    exact inv_mul_cancel₀ (mul_ne_zero hℓval hMval)
  · -- value 0 at the other points
    intro i hi
    have hzero : ℓ.eval (x i) = 0 := by
      rw [hℓ, eval_prod]
      refine Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩) ?_
      simp
    simp [eval_mul, hzero]
  · -- value 0 at every `ν j`
    intro j
    have hzero : aeval (ν j) M = 0 := by
      rw [hM, map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ j) (minpoly.aeval K (ν j))
    simp [map_mul, hzero]

/-- Node interpolant: `β` at `ν j₀`, `0` at every `x i` and at the other
`ν j`, with `K`-coefficients and degree `< t + d·e`. -/
theorem exists_node_interpolant
    (hν : ∀ j, ν j ∉ Set.range (algebraMap K L))
    (hgen : ∀ j, (minpoly K (ν j)).natDegree = Module.finrank K L)
    (hconj : ∀ j j', j ≠ j' → minpoly K (ν j) ≠ minpoly K (ν j'))
    (j₀ : Fin e) (β : L) :
    ∃ g : K[X], g.natDegree < t + Module.finrank K L * e ∧
      (∀ i, g.eval (x i) = 0) ∧ aeval (ν j₀) g = β ∧
      ∀ j, j ≠ j₀ → aeval (ν j) g = 0 := by
  classical
  set Lp : K[X] := ∏ i, (X - C (x i)) with hLp
  set Mp : K[X] := ∏ j ∈ Finset.univ.erase j₀, minpoly K (ν j) with hMp
  have hMne : ∀ j, minpoly K (ν j) ≠ 0 := fun j =>
    minpoly.ne_zero (IsIntegral.of_finite K (ν j))
  have hLpval : aeval (ν j₀) Lp ≠ 0 := by
    rw [hLp, map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    intro h0
    rw [map_sub, aeval_X, aeval_C] at h0
    exact hν j₀ ⟨x i, (sub_eq_zero.mp h0).symm⟩
  have hMpval : aeval (ν j₀) Mp ≠ 0 := by
    rw [hMp, map_prod]
    refine Finset.prod_ne_zero_iff.mpr fun j hj => ?_
    exact minpoly_aeval_ne_zero_of_ne (ν j) (ν j₀)
      (hconj j j₀ (Finset.mem_erase.mp hj).1)
  have hbase_ne : aeval (ν j₀) (Lp * Mp) ≠ 0 := by
    rw [map_mul]; exact mul_ne_zero hLpval hMpval
  obtain ⟨q₀, hq₀⟩ := aeval_surjective (ν j₀) (hgen j₀)
    (β * (aeval (ν j₀) (Lp * Mp))⁻¹)
  have hm₀monic : (minpoly K (ν j₀)).Monic :=
    minpoly.monic (IsIntegral.of_finite K (ν j₀))
  set q : K[X] := q₀ %ₘ minpoly K (ν j₀) with hqdef
  have hqval : aeval (ν j₀) q = β * (aeval (ν j₀) (Lp * Mp))⁻¹ := by
    rw [hqdef, modByMonic_eq_sub_mul_div, map_sub, map_mul,
      minpoly.aeval, zero_mul, sub_zero, hq₀]
  have hqdeg : q.natDegree < Module.finrank K L := by
    by_cases hq0 : q = 0
    · rw [hq0, natDegree_zero]
      exact Module.finrank_pos
    · have hlt := degree_modByMonic_lt q₀ hm₀monic
      rw [← hqdef] at hlt
      have := natDegree_lt_natDegree hq0 hlt
      rwa [hgen j₀] at this
  refine ⟨q * (Lp * Mp), ?_, ?_, ?_, ?_⟩
  · -- degree: `< d + (t + d(e−1)) = t + d·e`
    have hLpdeg : Lp.natDegree = t := by
      rw [hLp, natDegree_prod _ _ fun i _ => X_sub_C_ne_zero (x i)]
      simp
    have hMpdeg : Mp.natDegree ≤ Module.finrank K L * (e - 1) := by
      rw [hMp, natDegree_prod _ _ fun j _ => hMne j]
      calc ∑ j ∈ Finset.univ.erase j₀, (minpoly K (ν j)).natDegree
          ≤ ∑ _j ∈ Finset.univ.erase j₀, Module.finrank K L :=
            Finset.sum_le_sum fun j _ => minpoly.natDegree_le (ν j)
        _ = Module.finrank K L * (e - 1) := by
            simp [Finset.sum_const, Finset.card_erase_of_mem, mul_comm]
    have hbound : (q * (Lp * Mp)).natDegree ≤
        q.natDegree + (Lp.natDegree + Mp.natDegree) :=
      natDegree_mul_le.trans (by gcongr; exact natDegree_mul_le)
    have he : 0 < e := j₀.pos
    have hd : 0 < Module.finrank K L := Module.finrank_pos
    have hsucc : e - 1 + 1 = e := Nat.succ_pred_eq_of_pos he
    have h1 : Module.finrank K L * (e - 1) + Module.finrank K L =
        Module.finrank K L * e := by
      calc Module.finrank K L * (e - 1) + Module.finrank K L
          = Module.finrank K L * (e - 1 + 1) := by ring
        _ = Module.finrank K L * e := by rw [hsucc]
    omega
  · intro i
    have hzero : Lp.eval (x i) = 0 := by
      rw [hLp, eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    simp [eval_mul, hzero]
  · rw [map_mul, hqval, mul_assoc, inv_mul_cancel₀ hbase_ne, mul_one]
  · intro j hj
    have hzero : aeval (ν j) Mp = 0 := by
      rw [hMp, map_prod]
      exact Finset.prod_eq_zero
        (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩) (minpoly.aeval K (ν j))
    simp [map_mul, hzero]

/-- **`lem:crt`, interpolation form.** A `K`-coefficient polynomial of degree
`< N` can take arbitrary prescribed values at `t` distinct points of `K` and
at `e` pairwise non-conjugate generators of `L`, provided `t + d·e ≤ N`. -/
theorem exists_interpolant (hx : Function.Injective x)
    (hν : ∀ j, ν j ∉ Set.range (algebraMap K L))
    (hgen : ∀ j, (minpoly K (ν j)).natDegree = Module.finrank K L)
    (hconj : ∀ j j', j ≠ j' → minpoly K (ν j) ≠ minpoly K (ν j'))
    {N : ℕ} (hNpos : 0 < N) (hN : t + Module.finrank K L * e ≤ N)
    (a : Fin t → K) (b : Fin e → L) :
    ∃ g : K[X], g.natDegree < N ∧ (∀ i, g.eval (x i) = a i) ∧
      ∀ j, aeval (ν j) g = b j := by
  classical
  choose gp hgpdeg hgp1 hgp0 hgpν using
    fun i₀ => exists_point_interpolant x ν hx hν i₀
  choose gn hgndeg hgn0 hgnval hgnother using
    fun j₀ => exists_node_interpolant x ν hν hgen hconj j₀ (b j₀)
  refine ⟨(∑ i, C (a i) * gp i) + ∑ j, gn j, ?_, ?_, ?_⟩
  · -- degree bound
    have h1 : (∑ i, C (a i) * gp i).natDegree ≤ N - 1 := by
      refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
      have := (natDegree_C_mul_le (a i) (gp i)).trans_lt (hgpdeg i)
      omega
    have h2 : (∑ j, gn j).natDegree ≤ N - 1 := by
      refine natDegree_sum_le_of_forall_le _ _ fun j _ => ?_
      have := hgndeg j
      omega
    have := natDegree_add_le (∑ i, C (a i) * gp i) (∑ j, gn j)
    omega
  · -- values at the points
    intro i
    rw [eval_add, eval_finsetSum, eval_finsetSum]
    rw [Finset.sum_eq_single i
      (fun i' _ hne => by rw [eval_mul, hgp0 i' i (Ne.symm hne), mul_zero])
      (fun habs => absurd (Finset.mem_univ i) habs)]
    rw [eval_mul, eval_C, hgp1 i, mul_one]
    rw [Finset.sum_eq_zero fun j _ => hgn0 j i, add_zero]
  · -- values at the nodes
    intro j
    rw [map_add, map_sum, map_sum]
    rw [Finset.sum_eq_zero fun i _ => by
      rw [map_mul, hgpν i j, mul_zero]]
    rw [Finset.sum_eq_single j
      (fun j' _ hne => hgnother j' j (Ne.symm hne))
      (fun habs => absurd (Finset.mem_univ j) habs)]
    rw [hgnval j, zero_add]

end Interpolants

open IntermediateField in
/-- In a prime-degree extension, every element outside the base field is a
generator: its minimal polynomial has full degree. (The bridge that discharges
`hgen` of `exists_interpolant` at `K = F_p`, `L = F_q`, `d` prime.) -/
theorem minpoly_natDegree_eq_finrank_of_prime
    (hprime : (Module.finrank K L).Prime)
    (ν : L) (hν : ν ∉ Set.range (algebraMap K L)) :
    (minpoly K ν).natDegree = Module.finrank K L := by
  have hint : IsIntegral K ν := IsIntegral.of_finite K ν
  have hadj : Module.finrank K K⟮ν⟯ = (minpoly K ν).natDegree :=
    IntermediateField.adjoin.finrank hint
  have hdvd : Module.finrank K K⟮ν⟯ ∣ Module.finrank K L :=
    ⟨Module.finrank K⟮ν⟯ L, (Module.finrank_mul_finrank K K⟮ν⟯ L).symm⟩
  rcases hprime.eq_one_or_self_of_dvd _ hdvd with h1 | hd
  · exfalso
    have hbot : K⟮ν⟯ = ⊥ := IntermediateField.finrank_eq_one_iff.mp h1
    have : ν ∈ K⟮ν⟯ := IntermediateField.mem_adjoin_simple_self K ν
    rw [hbot, IntermediateField.mem_bot] at this
    exact hν this
  · rw [← hadj, hd]

end ZkWhir
