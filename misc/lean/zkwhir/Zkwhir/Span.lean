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

end ZkWhir
