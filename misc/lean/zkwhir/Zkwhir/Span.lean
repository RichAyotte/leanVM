/-
`lem:span` (multiplicative span) and `lem:stabilizer` (subfield stabilizer) of
`zk_leanVM.tex`, formalized generically over a prime-degree finite field
extension `L / K`.

`lem:stabilizer`: if `V` is a `K`-subspace of `L` with `1 ∈ V` and `V ≠ ⊤`,
then the stabilizer `{x : x·V ⊆ V}` equals `K` (the base field). Consequence:
for `α ∉ K`, `V + α·V ⊋ V`.

`lem:span`: the `K`-span of the products `∏_{i∈S} αᵢ` (`S ⊆ {1..k}`) equals all
of `L` as soon as at least `d − 1` of the `αᵢ` lie outside `K` (`d = [L:K]`).

This is the sharp ingredient behind `lem:spread`: it replaces the lossy
union-over-duals bound (`≈ p²/q`) by the paper's `1/q + B(p/q)^e` bound.

Part of the `GoodSetAbsorption` campaign; not yet wired into the root module.
-/
import Mathlib

set_option linter.style.header false

noncomputable section

open scoped Classical

namespace ZkWhir

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]

/-- The **stabilizer subalgebra** of a `K`-subspace `V ≤ L`: the elements `x`
with `x · V ⊆ V`. It is a `K`-subalgebra of `L` (closed under the field
operations, and contains the image of `K` because `V` is a `K`-submodule). -/
def stabilizerSubalgebra (V : Submodule K L) : Subalgebra K L where
  carrier := {x : L | ∀ v ∈ V, x * v ∈ V}
  mul_mem' := fun {x y} hx hy v hv => by
    have : y * v ∈ V := hy v hv
    simpa [mul_assoc] using hx (y * v) this
  one_mem' := fun v hv => by rw [one_mul]; exact hv
  add_mem' := fun {x y} hx hy v hv => by
    simpa [add_mul] using V.add_mem (hx v hv) (hy v hv)
  zero_mem' := fun v _ => by rw [zero_mul]; exact V.zero_mem
  algebraMap_mem' := fun c v hv => by
    rw [← Algebra.smul_def]; exact V.smul_mem c hv

@[simp]
theorem mem_stabilizerSubalgebra {V : Submodule K L} {x : L} :
    x ∈ stabilizerSubalgebra V ↔ ∀ v ∈ V, x * v ∈ V := Iff.rfl

/-- **`lem:stabilizer` (subfield stabilizer).** In a prime-degree extension
`L / K`, if `V` is a `K`-subspace with `1 ∈ V` and `V ≠ ⊤`, then every element
`x` stabilizing `V` (`x · V ⊆ V`) lies in the base field `K`. -/
theorem mem_range_of_mul_mem (hprime : (Module.finrank K L).Prime)
    {V : Submodule K L} (h1 : (1 : L) ∈ V) (hVne : V ≠ ⊤)
    {x : L} (hx : ∀ v ∈ V, x * v ∈ V) :
    x ∈ Set.range (algebraMap K L) := by
  set S := stabilizerSubalgebra V with hS
  have hxS : x ∈ S := hx
  -- `S` is a subalgebra of the finite (hence algebraic) extension, so it is an
  -- intermediate field with the same carrier.
  have halg : Algebra.IsAlgebraic K S := inferInstance
  set T : IntermediateField K L := halg.toIntermediateField S with hT
  have hmemT : ∀ {y : L}, y ∈ T ↔ y ∈ S := fun {y} => Iff.rfl
  -- `T ≠ ⊤`: otherwise `1 ∈ V` and stabilization force `V = ⊤`.
  have hTne : T ≠ ⊤ := by
    intro htop
    apply hVne
    rw [Submodule.eq_top_iff']
    intro y
    have hyS : y ∈ S := hmemT.mp (htop ▸ IntermediateField.mem_top)
    have := hyS 1 h1
    rwa [mul_one] at this
  -- degree of `T` divides the prime `[L:K]`.
  have hdvd : Module.finrank K T ∣ Module.finrank K L :=
    ⟨Module.finrank T L, (Module.finrank_mul_finrank K T L).symm⟩
  rcases hprime.eq_one_or_self_of_dvd _ hdvd with h1' | hd
  · have hbot : T = ⊥ := IntermediateField.finrank_eq_one_iff.mp h1'
    have hxT : x ∈ T := hmemT.mpr hxS
    rw [hbot, IntermediateField.mem_bot] at hxT
    exact hxT
  · exfalso
    apply hTne
    have hfr : Module.finrank K T.toSubalgebra.toSubmodule = Module.finrank K L := by
      simpa using hd
    have htop : T.toSubalgebra.toSubmodule = ⊤ := Submodule.eq_top_of_finrank_eq hfr
    ext y
    refine ⟨fun _ => IntermediateField.mem_top, fun _ => ?_⟩
    have : y ∈ T.toSubalgebra.toSubmodule := htop ▸ Submodule.mem_top
    exact this

/-- **`lem:stabilizer`, growth form.** For `α ∉ K`, adjoining `α · V` strictly
increases the dimension of a proper `K`-subspace `V ∋ 1`. This is the inductive
step of the multiplicative-span lemma. -/
theorem finrank_lt_sup_map_mulLeft (hprime : (Module.finrank K L).Prime)
    {V : Submodule K L} (h1 : (1 : L) ∈ V) (hVne : V ≠ ⊤)
    {α : L} (hα : α ∉ Set.range (algebraMap K L)) :
    Module.finrank K V <
      Module.finrank K ↥(V ⊔ V.map (LinearMap.mulLeft K α)) := by
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne le_sup_left (fun heq => ?_)
  apply hα
  apply mem_range_of_mul_mem hprime h1 hVne
  intro v hv
  have hWle : V.map (LinearMap.mulLeft K α) ≤ V := sup_eq_left.mp heq.symm
  have hmem : (LinearMap.mulLeft K α) v ∈ V := hWle (Submodule.mem_map_of_mem hv)
  rwa [LinearMap.mulLeft_apply] at hmem

/-! ## Multiplicative span (`lem:span`) -/

variable {ι : Type*} [DecidableEq ι]

/-- The `K`-span of the squarefree monomials `∏_{i ∈ S} αᵢ` over subsets `S ⊆ T`. -/
def monomialSpan (α : ι → L) (T : Finset ι) : Submodule K L :=
  Submodule.span K ((fun S => ∏ i ∈ S, α i) '' (T.powerset : Set (Finset ι)))

omit [FiniteDimensional K L] in
theorem one_mem_monomialSpan (α : ι → L) (T : Finset ι) :
    (1 : L) ∈ monomialSpan (K := K) α T := by
  apply Submodule.subset_span
  exact ⟨∅, by simp, by simp⟩

omit [FiniteDimensional K L] in
/-- **`lem:span` recursion.** Adjoining a fresh index `j` multiplies the previous
monomial span by `αⱼ`: `monomialSpan (insert j T) = monomialSpan T ⊔ αⱼ · monomialSpan T`. -/
theorem monomialSpan_insert (α : ι → L) {j : ι} {T : Finset ι} (hj : j ∉ T) :
    monomialSpan (K := K) α (insert j T) =
      monomialSpan (K := K) α T ⊔
        (monomialSpan (K := K) α T).map (LinearMap.mulLeft K (α j)) := by
  unfold monomialSpan
  rw [Submodule.map_span, ← Submodule.span_union]
  congr 1
  rw [Finset.powerset_insert, Finset.coe_union, Set.image_union, Finset.coe_image]
  simp only [← Set.image_comp]
  congr 1
  apply Set.image_congr
  intro S hS
  simp only [Finset.mem_coe, Finset.mem_powerset] at hS
  have hjS : j ∉ S := fun h => hj (hS h)
  simp only [Function.comp_apply, LinearMap.mulLeft_apply]
  rw [Finset.prod_insert hjS]

omit [FiniteDimensional K L] in
/-- Multiplying a subspace by a base-field element does not enlarge it. -/
theorem map_mulLeft_le_of_mem_range {V : Submodule K L} {x : L}
    (hx : x ∈ Set.range (algebraMap K L)) :
    V.map (LinearMap.mulLeft K x) ≤ V := by
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨c, rfl⟩ := hx
  rw [LinearMap.mulLeft_apply, ← Algebra.smul_def]
  exact V.smul_mem c hv

omit [FiniteDimensional K L] in
theorem monomialSpan_empty (α : ι → L) :
    monomialSpan (K := K) α ∅ = Submodule.span K {(1 : L)} := by
  unfold monomialSpan
  congr 1
  simp

/-- **`lem:span` dimension bound.** Either the monomial span over `T` is already
all of `L`, or its dimension exceeds the number of indices in `T` lying outside
the base field (`1 +` that count). Each outside-`K` index strictly grows the span
(growth form of `lem:stabilizer`); base-field indices leave it unchanged. -/
theorem monomialSpan_dim (hprime : (Module.finrank K L).Prime) (α : ι → L)
    (T : Finset ι) :
    monomialSpan (K := K) α T = ⊤ ∨
      1 + (T.filter (fun i => α i ∉ Set.range (algebraMap K L))).card ≤
        Module.finrank K (monomialSpan (K := K) α T) := by
  induction T using Finset.induction with
  | empty =>
    right
    rw [monomialSpan_empty, finrank_span_singleton (one_ne_zero : (1 : L) ≠ 0),
      Finset.filter_empty, Finset.card_empty]
  | @insert j T hj ih =>
    by_cases hjK : α j ∈ Set.range (algebraMap K L)
    · -- base-field index: span and outside-count unchanged
      have hmap : (monomialSpan (K := K) α T).map (LinearMap.mulLeft K (α j)) ≤
          monomialSpan (K := K) α T := map_mulLeft_le_of_mem_range hjK
      have hsame : monomialSpan (K := K) α (insert j T) = monomialSpan (K := K) α T := by
        rw [monomialSpan_insert α hj, sup_eq_left.mpr hmap]
      rw [hsame, Finset.filter_insert, if_neg (not_not.mpr hjK)]
      exact ih
    · -- outside-`K` index: the count goes up by one
      have hfilt : (insert j T).filter (fun i => α i ∉ Set.range (algebraMap K L)) =
          insert j (T.filter (fun i => α i ∉ Set.range (algebraMap K L))) := by
        rw [Finset.filter_insert, if_pos hjK]
      have hjnotmem : j ∉ T.filter (fun i => α i ∉ Set.range (algebraMap K L)) :=
        fun h => hj (Finset.mem_of_mem_filter _ h)
      have hMSle : monomialSpan (K := K) α T ≤ monomialSpan (K := K) α (insert j T) := by
        rw [monomialSpan_insert α hj]; exact le_sup_left
      rcases ih with htop | hdim
      · left
        rw [eq_top_iff]; exact le_trans (by rw [htop]) hMSle
      · by_cases hMStop : monomialSpan (K := K) α T = ⊤
        · left
          rw [eq_top_iff]; exact le_trans (by rw [hMStop]) hMSle
        · right
          have hgrow : Module.finrank K (monomialSpan (K := K) α T) <
              Module.finrank K ↥(monomialSpan (K := K) α T ⊔
                (monomialSpan (K := K) α T).map (LinearMap.mulLeft K (α j))) :=
            finrank_lt_sup_map_mulLeft hprime (one_mem_monomialSpan α T) hMStop hjK
          rw [monomialSpan_insert α hj, hfilt, Finset.card_insert_of_notMem hjnotmem]
          omega

/-- **`lem:span` (ii).** If at least `d − 1` of the indices in `T` carry values
outside the base field (`d = [L:K]`, prime), the monomial span is all of `L`. -/
theorem monomialSpan_eq_top (hprime : (Module.finrank K L).Prime) (α : ι → L)
    (T : Finset ι)
    (hcard : Module.finrank K L - 1 ≤
        (T.filter (fun i => α i ∉ Set.range (algebraMap K L))).card) :
    monomialSpan (K := K) α T = ⊤ := by
  rcases monomialSpan_dim hprime α T with h | h
  · exact h
  · have hle : Module.finrank K (monomialSpan (K := K) α T) ≤ Module.finrank K L :=
      Submodule.finrank_le _
    exact Submodule.eq_top_of_finrank_eq (le_antisymm hle (by omega))

end ZkWhir
