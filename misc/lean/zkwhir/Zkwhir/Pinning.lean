/-
The pinning framework (`prop:pinbound`, primal form via the dual bridge): the
view-vanishing mask perturbations and their folds form `Fp`-linear maps; the
primal `Pinning` (∃κ with view 0 and fold = −F) is membership of `−F` in the
range of the fold restricted to view-vanishing masks, which the dual bridge
(`mem_range_iff_forall_dual`) turns into the annihilator statement
`ann(W') = protocol span` of the paper.

This file sets up the linear-algebra scaffold; the annihilator computation
(`lem:fullslice`/`lem:noother`) consumes the slice/moment/trace toolkit.

Part of the `GoodSetAbsorption` formalization campaign.
-/
import Mathlib
import Zkwhir.Statement
import Zkwhir.Toolbox
import Zkwhir.Absorption
import Zkwhir.StaircaseBridge
import Zkwhir.Staircase
import Zkwhir.ViewSolve
import Zkwhir.Blocks
import Zkwhir.Twist

set_option linter.style.header false
set_option linter.unusedSectionVars false

noncomputable section

namespace ZkWhir

variable (P : Params) (Fq : Type*) [Field Fq] [Fintype Fq]
  [Algebra (Fp P) Fq] (Dom : Finset (Fp P)) [Nonempty {x // x ∈ Dom}]
  (S : Stmt P Fq) (ch : Challenges P Fq Dom)

/-- `assemble` with zero data is additive in the mask. -/
theorem assemble_zero_add (m₁ m₂ : MaskAssign P) :
    assemble P 0 (m₁ + m₂) = assemble P 0 m₁ + assemble P 0 m₂ := by
  funext u
  rw [Pi.add_apply]
  unfold assemble
  by_cases h : IsMask P u
  · rw [dif_pos h, dif_pos h, dif_pos h, Pi.add_apply]
  · rw [dif_neg h, dif_neg h, dif_neg h]
    simp

/-- `assemble` with zero data is homogeneous in the mask. -/
theorem assemble_zero_smul (c : Fp P) (m : MaskAssign P) :
    assemble P 0 (c • m) = c • assemble P 0 m := by
  funext u
  rw [Pi.smul_apply]
  unfold assemble
  by_cases h : IsMask P u
  · rw [dif_pos h, dif_pos h, Pi.smul_apply]
  · rw [dif_neg h, dif_neg h]
    simp

/-- `foldedF₁` is homogeneous: an `Fp`-scaling of the table becomes the
corresponding `Fp`-scaling (through `algebraMap`) of the fold. -/
theorem foldedF₁_smul (c : Fp P) (T : Cell P → Fp P) :
    foldedF₁ P Fq Dom (c • T) ch = c • foldedF₁ P Fq Dom T ch := by
  funext c'
  unfold foldedF₁
  rw [Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold liftT
  rw [Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def]
  ring

/-- `liftT` is homogeneous over `Fp`. -/
theorem liftT_smul (c : Fp P) (T : Cell P → Fp P) :
    liftT P Fq (c • T) = c • liftT P Fq T := by
  funext u
  simp only [liftT, Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def]

/-- `mle` is homogeneous over `Fp`. -/
theorem mle_smul_fp {j : ℕ} (c : Fp P) (M : Cube j → Fq) (xs : Fin j → Fq) :
    mle (c • M) xs = c • mle M xs := by
  unfold mle
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]; ring

/-- `evalT` is homogeneous over `Fp`. -/
theorem evalT_smul (c : Fp P) (T : Cell P → Fp P) (ys : Fin P.k₀ → Fq)
    (xs : Fin P.m → Fq) :
    evalT P Fq (c • T) ys xs = c • evalT P Fq T ys xs := by
  unfold evalT
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [liftT_smul, Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]; ring

/-- `partialEval` is homogeneous over `Fp`. -/
theorem partialEval_smul_fp (c : Fp P) (G : Cell P → Fq) (ℓ : Fin P.k₀) (X : Fq)
    (b : Cube P.k₀) (cc : Cube P.m) :
    partialEval P Fq Dom ch (c • G) ℓ X b cc =
      c • partialEval P Fq Dom ch G ℓ X b cc := by
  unfold partialEval
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]; ring

/-- The out-of-domain answer is homogeneous over `Fp`. -/
theorem oodAnswer_smul (c : Fp P) (T : Cell P → Fp P) (z : Fq) :
    oodAnswer P Fq (c • T) z = c • oodAnswer P Fq T z := by
  unfold oodAnswer; rw [evalT_smul]

/-- The query answer is homogeneous over `Fp`. -/
theorem queryAnswer_smul (c : Fp P) (T : Cell P → Fp P) (t : Fin P.t₀)
    (s : Cube P.k₀) :
    queryAnswer P Fq Dom (c • T) ch t s =
      c • queryAnswer P Fq Dom T ch t s := by
  unfold queryAnswer
  have hfun : (fun cc => liftT P Fq (c • T) (s, cc)) =
      c • (fun cc => liftT P Fq T (s, cc)) := by
    funext cc; rw [liftT_smul]; rfl
  rw [hfun, mle_smul_fp]

/-- The sumcheck message is homogeneous over `Fp` (the weight `W₀` is fixed, so
the perturbation enters linearly). -/
theorem hPoly_smul (c : Fp P) (T : Cell P → Fp P) (ℓ : Fin P.k₀) (X : Fq) :
    hPoly P Fq Dom S (c • T) ch ℓ X = c • hPoly P Fq Dom S T ch ℓ X := by
  unfold hPoly
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun cc _ => ?_
  rw [liftT_smul, partialEval_smul_fp, Algebra.smul_def, Algebra.smul_def]; ring

/-- The folded `f̂₁` out-of-domain answer is homogeneous over `Fp`. -/
theorem mle_foldedF₁_smul (c : Fp P) (T : Cell P → Fp P) (xs : Fin P.m → Fq) :
    mle (foldedF₁ P Fq Dom (c • T) ch) xs = c • mle (foldedF₁ P Fq Dom T ch) xs := by
  rw [foldedF₁_smul, mle_smul_fp]

/-- **The fold map**: the `Fp`-linear map sending a mask `κ` to the fold of the
pure-mask perturbation `assemble 0 (−κ)`. Its range, restricted to the
view-vanishing masks, is the space the primal `Pinning` must hit. -/
def foldMap : MaskAssign P →ₗ[Fp P] (Cube P.m → Fq) where
  toFun κ := foldedF₁ P Fq Dom (assemble P 0 (-κ)) ch
  map_add' κ₁ κ₂ := by
    show foldedF₁ P Fq Dom (assemble P 0 (-(κ₁ + κ₂))) ch =
      foldedF₁ P Fq Dom (assemble P 0 (-κ₁)) ch +
        foldedF₁ P Fq Dom (assemble P 0 (-κ₂)) ch
    rw [neg_add, assemble_zero_add, foldedF₁_add]
  map_smul' c κ := by
    show foldedF₁ P Fq Dom (assemble P 0 (-(c • κ))) ch =
      c • foldedF₁ P Fq Dom (assemble P 0 (-κ)) ch
    rw [← smul_neg, assemble_zero_smul, foldedF₁_smul]

/-! ## The view-vanishing masks as a subspace -/

/-- `mle` is additive. -/
theorem mle_pi_add {j : ℕ} (M₁ M₂ : Cube j → Fq) (xs : Fin j → Fq) :
    mle (M₁ + M₂) xs = mle M₁ xs + mle M₂ xs := by
  unfold mle
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun b _ => by rw [Pi.add_apply]; ring

/-- The multilinear extension is odd in the table (`mle (-M) = - mle M`): used in
the assembly to transport protocol-killed-ness of `F` to `-F`. -/
theorem mle_pi_neg {j : ℕ} (M : Cube j → Fq) (xs : Fin j → Fq) :
    mle (-M) xs = - mle M xs := by
  unfold mle
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun b _ => by rw [Pi.neg_apply, mul_neg]

/-- Zero data and zero mask assemble to the zero table. -/
theorem assemble_zero_zero : assemble P 0 (0 : MaskAssign P) = 0 := by
  funext u; unfold assemble
  by_cases h : IsMask P u <;> simp [h]

theorem liftT_zero : liftT P Fq (0 : Cell P → Fp P) = 0 := by
  funext u; simp [liftT]

theorem oodAnswer_zero (z : Fq) : oodAnswer P Fq (0 : Cell P → Fp P) z = 0 := by
  unfold oodAnswer evalT; simp [liftT]

theorem foldedF₁_zero : foldedF₁ P Fq Dom (0 : Cell P → Fp P) ch = 0 := by
  funext c'; unfold foldedF₁; simp [liftT]

theorem hPoly_zero (ℓ : Fin P.k₀) (X : Fq) :
    hPoly P Fq Dom S (0 : Cell P → Fp P) ch ℓ X = 0 := by
  unfold hPoly
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun cc _ => ?_
  have hz : partialEval P Fq Dom ch (liftT P Fq (0 : Cell P → Fp P)) ℓ X b cc = 0 := by
    rw [liftT_zero]; unfold partialEval; simp
  rw [hz]; ring

theorem queryAnswer_zero (t : Fin P.t₀) (s : Cube P.k₀) :
    queryAnswer P Fq Dom (0 : Cell P → Fp P) ch t s = 0 := by
  unfold queryAnswer; simp [liftT_zero, mle]

/-- The view of the zero table vanishes. -/
theorem viewVanishes_zero_table : ViewVanishes P Fq Dom S ch 0 :=
  ⟨fun j => oodAnswer_zero P Fq (ch.z j),
   fun ℓ => hPoly_zero P Fq Dom S ch ℓ 1,
   fun ℓ => hPoly_zero P Fq Dom S ch ℓ 2,
   fun t s => queryAnswer_zero P Fq Dom ch t s,
   fun j => by rw [foldedF₁_zero]; unfold mle; simp⟩

/-- **The view-vanishing masks** form an `Fp`-subspace: those `κ` whose
pure-mask perturbation `assemble 0 (−κ)` has vanishing reduced view. The
domain of the pinning fold map `ψ`. -/
def viewKer : Submodule (Fp P) (MaskAssign P) where
  carrier := {κ | ViewVanishes P Fq Dom S ch (assemble P 0 (-κ))}
  zero_mem' := by
    show ViewVanishes P Fq Dom S ch (assemble P 0 (-0))
    rw [neg_zero, assemble_zero_zero]
    exact viewVanishes_zero_table P Fq Dom S ch
  add_mem' := by
    intro κ₁ κ₂ h₁ h₂
    show ViewVanishes P Fq Dom S ch (assemble P 0 (-(κ₁ + κ₂)))
    rw [neg_add, assemble_zero_add]
    exact ⟨fun j => by rw [oodAnswer_add, h₁.ood j, h₂.ood j, add_zero],
      fun ℓ => by rw [hPoly_add, h₁.msg1 ℓ, h₂.msg1 ℓ, add_zero],
      fun ℓ => by rw [hPoly_add, h₁.msg2 ℓ, h₂.msg2 ℓ, add_zero],
      fun t s => by rw [queryAnswer_add, h₁.qa t s, h₂.qa t s, add_zero],
      fun j => by rw [foldedF₁_add, mle_pi_add, h₁.f1ood j, h₂.f1ood j, add_zero]⟩
  smul_mem' := by
    intro c κ h
    show ViewVanishes P Fq Dom S ch (assemble P 0 (-(c • κ)))
    rw [← smul_neg, assemble_zero_smul]
    exact ⟨fun j => by rw [oodAnswer_smul, h.ood j, smul_zero],
      fun ℓ => by rw [hPoly_smul, h.msg1 ℓ, smul_zero],
      fun ℓ => by rw [hPoly_smul, h.msg2 ℓ, smul_zero],
      fun t s => by rw [queryAnswer_smul, h.qa t s, smul_zero],
      fun j => by rw [mle_foldedF₁_smul, h.f1ood j, smul_zero]⟩

/-- Membership in `viewKer` is exactly view-vanishing. -/
theorem mem_viewKer (κ : MaskAssign P) :
    κ ∈ viewKer P Fq Dom S ch ↔
      ViewVanishes P Fq Dom S ch (assemble P 0 (-κ)) := Iff.rfl

/-- **The pinning fold map `ψ`**: the fold map restricted to the view-vanishing
masks. `Pinning` is exactly the statement that `−F` is in its range for every
protocol-killed `F`. -/
def pinFold : viewKer P Fq Dom S ch →ₗ[Fp P] (Cube P.m → Fq) :=
  (foldMap P Fq Dom ch).domRestrict (viewKer P Fq Dom S ch)

/-- **Reduction of `Pinning` to range membership**: if every protocol-killed
`F` has `−F` in the range of `ψ`, then `Pinning` holds. -/
theorem pinning_of_forall_range
    (h : ∀ F : Cube P.m → Fq,
        (∀ t, mle F (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0) →
        (∀ j, mle F (powSeq (ch.zf j) P.m) = 0) →
        ((∑ c, F c * ∑ s, eqPoly ch.α s * W₀ P Fq Dom S ch (s, c)) = 0) →
        (-F) ∈ LinearMap.range (pinFold P Fq Dom S ch)) :
    Pinning P Fq Dom S ch := by
  intro F hq hzf hterm
  obtain ⟨κ, hκ⟩ := h F hq hzf hterm
  refine ⟨κ.1, κ.2, ?_⟩
  rw [show (fun c => -F c) = -F from rfl]
  exact hκ

/-- **The dual form of `Pinning`** (the primal↔dual keystone): `Pinning`
follows once every protocol direction — every functional vanishing on all
view-vanishing mask-folds — also annihilates `−F`. This is the statement
`prop:pinbound` establishes (`ann(W') = protocol span`). -/
theorem pinning_of_dual [FiniteDimensional (Fp P) (Cube P.m → Fq)]
    (h : ∀ F : Cube P.m → Fq,
        (∀ t, mle F (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0) →
        (∀ j, mle F (powSeq (ch.zf j) P.m) = 0) →
        ((∑ c, F c * ∑ s, eqPoly ch.α s * W₀ P Fq Dom S ch (s, c)) = 0) →
        ∀ φ : Module.Dual (Fp P) (Cube P.m → Fq),
          (∀ κ : viewKer P Fq Dom S ch, φ (pinFold P Fq Dom S ch κ) = 0) →
          φ (-F) = 0) :
    Pinning P Fq Dom S ch := by
  apply pinning_of_forall_range
  intro F hq hzf hterm
  rw [mem_range_iff_forall_dual]
  exact h F hq hzf hterm

/-! ## Soundness of the protocol directions (`prop:pinbound`, easy direction)

Every view-vanishing mask-fold lies in the protocol-killed space: the queried
duals, the `f̂₁` out-of-domain duals, and the terminal pairing all annihilate
`range pinFold`. (The hard converse — that these span the whole annihilator —
is the slice argument of `lem:fullslice`/`lem:noother`.) -/

/-- A view-vanishing mask-fold vanishes at the queried points. -/
theorem pinFold_queried_zero (κ : viewKer P Fq Dom S ch) (t : Fin P.t₀) :
    mle (pinFold P Fq Dom S ch κ)
      (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0 := by
  show mle (foldedF₁ P Fq Dom (assemble P 0 (-κ.1)) ch)
    (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0
  rw [mle_fold_eq_sum_classes]
  refine Finset.sum_eq_zero fun s _ => ?_
  have hqa : mle (fun c => liftT P Fq (assemble P 0 (-κ.1)) (s, c))
      (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0 := κ.2.qa t s
  rw [hqa, mul_zero]

/-- A view-vanishing mask-fold vanishes at the `f̂₁` out-of-domain points. -/
theorem pinFold_zf_zero (κ : viewKer P Fq Dom S ch) (j : Fin P.s₁) :
    mle (pinFold P Fq Dom S ch κ) (powSeq (ch.zf j) P.m) = 0 :=
  κ.2.f1ood j

/-- A view-vanishing mask-fold has vanishing terminal pairing against the
`α`-fold of the batched weight. -/
theorem pinFold_terminal_zero (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S)
    (κ : viewKer P Fq Dom S ch) :
    (∑ c, (pinFold P Fq Dom S ch κ) c *
      ∑ s, eqPoly ch.α s * W₀ P Fq Dom S ch (s, c)) = 0 := by
  show (∑ c, foldedF₁ P Fq Dom (assemble P 0 (-κ.1)) ch c *
    ∑ s, eqPoly ch.α s * W₀ P Fq Dom S ch (s, c)) = 0
  have hw : ∑ u, liftT P Fq (assemble P 0 (-κ.1)) u * S.w u = 0 := by
    rw [pairing_assemble P Fq S hmf 0 (-κ.1)]; simp
  have hmsg0 := msg0_of_reduced_view P Fq Dom S ch h2 (assemble P 0 (-κ.1))
    κ.2.ood κ.2.msg1 κ.2.msg2 hw
  exact terminal_pairing_eq_zero_of_msgs P Fq Dom S (assemble P 0 (-κ.1)) ch h2
    hmsg0 κ.2.msg1 κ.2.msg2

/-! ## The `(ℓ, y)`-family for view-vanishing masks (`lem:fullslice` Step 1)

For a view-vanishing mask the sumcheck messages vanish identically, so its
channel decomposition (`hPoly_channel`) gives the `(ℓ, y)`-family of identities
at every point — the input to the moment system of Step 2. This strengthens
`channel_identity_of_invisible` (which assumed full invisibility) to the actual
hypothesis class of the pinning argument. -/
theorem channel_identity_of_viewKer (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S)
    (κ : viewKer P Fq Dom S ch) (ℓ : Fin P.k₀) (y : Fq) :
    prefixFactor P Fq Dom ch ℓ y (powSeq (ch.z 0) P.k₀) *
        evalT P Fq (assemble P 0 (-κ.1))
          (mixedPoint P Fq Dom ch ℓ y (powSeq (ch.z 0) P.k₀))
          (powSeq (ch.z 0 ^ 2 ^ P.k₀) P.m) +
      ch.γ * (prefixFactor P Fq Dom ch ℓ y (powSeq (ch.z 1) P.k₀) *
        evalT P Fq (assemble P 0 (-κ.1))
          (mixedPoint P Fq Dom ch ℓ y (powSeq (ch.z 1) P.k₀))
          (powSeq (ch.z 1 ^ 2 ^ P.k₀) P.m)) +
      ch.γ ^ 2 * crossTerm P Fq Dom S (assemble P 0 (-κ.1)) ch ℓ y = 0 := by
  rw [← hPoly_channel P Fq Dom S (assemble P 0 (-κ.1)) ch ℓ y]
  have hw : ∑ u, liftT P Fq (assemble P 0 (-κ.1)) u * S.w u = 0 := by
    rw [pairing_assemble P Fq S hmf 0 (-κ.1)]; simp
  have hmsg0 := msg0_of_reduced_view P Fq Dom S ch h2 (assemble P 0 (-κ.1))
    κ.2.ood κ.2.msg1 κ.2.msg2 hw
  exact hPoly_eq_zero_of_msgs P Fq Dom S (assemble P 0 (-κ.1)) ch h2
    hmsg0 κ.2.msg1 κ.2.msg2 ℓ y

/-- **The μ-combined `(ℓ, y)`-family** (`lem:fullslice` Step 2, opening): summing
`channel_identity_of_viewKer` against weights `w` over points `pts` keeps the
identity at the level of the three weighted sums. Feeding the first two through
`prefixFactor_evalT_moment` then exposes the moment `(S, R)` representation. -/
theorem channel_moment_of_viewKer (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S)
    (κ : viewKer P Fq Dom S ch) (ℓ : Fin P.k₀) (w pts : Fin 3 → Fq) :
    (∑ t, w t * (prefixFactor P Fq Dom ch ℓ (pts t) (powSeq (ch.z 0) P.k₀) *
        evalT P Fq (assemble P 0 (-κ.1))
          (mixedPoint P Fq Dom ch ℓ (pts t) (powSeq (ch.z 0) P.k₀))
          (powSeq (ch.z 0 ^ 2 ^ P.k₀) P.m))) +
      ch.γ * (∑ t, w t * (prefixFactor P Fq Dom ch ℓ (pts t) (powSeq (ch.z 1) P.k₀) *
        evalT P Fq (assemble P 0 (-κ.1))
          (mixedPoint P Fq Dom ch ℓ (pts t) (powSeq (ch.z 1) P.k₀))
          (powSeq (ch.z 1 ^ 2 ^ P.k₀) P.m))) +
      ch.γ ^ 2 * (∑ t, w t *
        crossTerm P Fq Dom S (assemble P 0 (-κ.1)) ch ℓ (pts t)) = 0 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun t _ => ?_
  linear_combination
    w t * channel_identity_of_viewKer P Fq Dom S ch h2 hmf κ ℓ (pts t)

/-! ## The node-value representation (`lem:fullslice` Step 2c)

The slice value `evalT(mixed_j(ℓ, y))` is the pairing of the node values
`V_{s,j}` against the staircase Lagrange weight, which `eqPoly_mixedPoint_decomp`
expands into the telescoped node `ρ^j_ℓ` plus `(y − ζ_j)·τ^j_ℓ`: this is the
node functional `g^j_ℓ(y)` of the paper, the form the η-matching consumes. -/
theorem evalT_mixedPoint_node_decomp (δ : Cell P → Fp P) (j : Fin 2)
    (ℓ : Fin P.k₀) (y : Fq) :
    evalT P Fq δ (mixedPoint P Fq Dom ch ℓ y (powSeq (ch.z j) P.k₀))
        (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) =
      (∑ s, eqPoly (powSeq (ch.z j) P.k₀) s *
          mle (fun c => liftT P Fq δ (s, c)) (powSeq (ch.z j ^ 2 ^ P.k₀) P.m))
      + (∑ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < ℓ),
          lamData P Fq Dom ch (ch.z j) i *
            (∑ s, ptensor (stairVec (czData P Fq (ch.z j)) (fun _ => drow)
                (lamData P Fq Dom ch (ch.z j)) i) s *
              mle (fun c => liftT P Fq δ (s, c))
                (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)))
      + (y - powSeq (ch.z j) P.k₀ ℓ) *
          (∑ s, ptensor (stairVec (czData P Fq (ch.z j)) (fun _ => drow)
              (lamData P Fq Dom ch (ch.z j)) ℓ) s *
            mle (fun c => liftT P Fq δ (s, c))
              (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)) := by
  rw [evalT_eq_sum_classes]
  trans (∑ s, (eqPoly (powSeq (ch.z j) P.k₀) s
        + (∑ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < ℓ),
            lamData P Fq Dom ch (ch.z j) i *
              ptensor (stairVec (czData P Fq (ch.z j)) (fun _ => drow)
                (lamData P Fq Dom ch (ch.z j)) i) s)
        + (y - powSeq (ch.z j) P.k₀ ℓ) *
            ptensor (stairVec (czData P Fq (ch.z j)) (fun _ => drow)
              (lamData P Fq Dom ch (ch.z j)) ℓ) s)
      * mle (fun c => liftT P Fq δ (s, c)) (powSeq (ch.z j ^ 2 ^ P.k₀) P.m))
  · refine Finset.sum_congr rfl fun s _ => ?_
    congr 1
    have hd := congrFun (eqPoly_mixedPoint_decomp P Fq Dom ch ℓ y (ch.z j)) s
    simpa [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hd
  · simp only [add_mul]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    congr 1
    · congr 1
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring

/-! ## The terminal node and its telescoping (`lem:fullslice` Step 2, η-exit)

The terminal node `η = ρ_{k₀+1}` is the full-`α` Lagrange weight `êq(α, ·)`: each
staircase row `aRow_i = c_i + λ_i·d` telescopes to `vrow(α_i)` by `vrow_affine`.
The exit relation `η = ω + ∑_i λ_i·τ_i` then writes `η` in the `ω/τ` basis — the
target the moment system of Step 2 must reach. -/

/-- Each `z`-staircase row collapses to the full-`α` 2-vector. -/
theorem aRow_czData_eq_vrow_alpha (z : Fq) (i : Fin P.k₀) :
    aRow (czData P Fq z) drow (lamData P Fq Dom ch z) i = vrow (ch.α i) := by
  funext b
  unfold aRow czData lamData
  rw [vrow_affine (ch.α i) (powSeq z P.k₀ i)]

/-- **The η-exit relation**: the terminal node `êq(α, ·)` telescopes through the
`z`-staircase as `ω + ∑_{i} λ_i·τ_i`. -/
theorem eta_telescope (z : Fq) :
    eqPoly (ch.α) = eqPoly (powSeq z P.k₀)
      + ∑ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => (i : ℕ) < P.k₀),
          lamData P Fq Dom ch z i •
            ptensor (stairVec (czData P Fq z) (fun _ => drow)
              (lamData P Fq Dom ch z) i) := by
  have hcz : ptensor (czData P Fq z) = eqPoly (powSeq z P.k₀) := by
    rw [eqPoly_eq_ptensor]; rfl
  have hα : eqPoly (ch.α) =
      ptensor (fun i : Fin P.k₀ =>
        aRow (czData P Fq z) drow (lamData P Fq Dom ch z) i) := by
    rw [eqPoly_eq_ptensor]
    congr 1
    funext i
    rw [aRow_czData_eq_vrow_alpha]
  have hif : (fun i : Fin P.k₀ =>
        if (i : ℕ) < P.k₀ then aRow (czData P Fq z) drow (lamData P Fq Dom ch z) i
        else czData P Fq z i) =
      (fun i : Fin P.k₀ => aRow (czData P Fq z) drow (lamData P Fq Dom ch z) i) := by
    funext i; rw [if_pos i.isLt]
  have h := rhoN_telescope (czData P Fq z) drow (lamData P Fq Dom ch z) P.k₀
  rw [hif] at h
  rw [hα, h, hcz]

/-- The staircase row at an arbitrary point `β` (used for the Frobenius
conjugates `β = α^{[r]}` in `cond:twist`). -/
theorem aRow_czData_eq_vrow (z : Fq) (β : Fin P.k₀ → Fq) (i : Fin P.k₀) :
    aRow (czData P Fq z) drow (fun i => β i - powSeq z P.k₀ i) i = vrow (β i) := by
  funext b
  unfold aRow czData
  rw [vrow_affine (β i) (powSeq z P.k₀ i)]

/-- **The point-telescope** (`cond:twist`): every Lagrange weight `êq(β, ·)`
telescopes through the `z`-staircase as `ω + ∑_i (β_i − z^{2^{i-1}})·τ_i`, with
`τ_i` the staircase row at offset `β − z`. Specializes to `eta_telescope` at
`β = α`, and to the conjugates `β = α^{[r]}` for the rigidity argument. -/
theorem eqPoly_point_telescope (z : Fq) (β : Fin P.k₀ → Fq) :
    eqPoly β = eqPoly (powSeq z P.k₀)
      + ∑ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => (i : ℕ) < P.k₀),
          (β i - powSeq z P.k₀ i) •
            ptensor (stairVec (czData P Fq z) (fun _ => drow)
              (fun i => β i - powSeq z P.k₀ i) i) := by
  have hcz : ptensor (czData P Fq z) = eqPoly (powSeq z P.k₀) := by
    rw [eqPoly_eq_ptensor]; rfl
  have hβ : eqPoly β =
      ptensor (fun i : Fin P.k₀ =>
        aRow (czData P Fq z) drow (fun i => β i - powSeq z P.k₀ i) i) := by
    rw [eqPoly_eq_ptensor]
    congr 1
    funext i
    rw [aRow_czData_eq_vrow]
  have hif : (fun i : Fin P.k₀ =>
        if (i : ℕ) < P.k₀ then
          aRow (czData P Fq z) drow (fun i => β i - powSeq z P.k₀ i) i
        else czData P Fq z i) =
      (fun i : Fin P.k₀ =>
        aRow (czData P Fq z) drow (fun i => β i - powSeq z P.k₀ i) i) := by
    funext i; rw [if_pos i.isLt]
  have h := rhoN_telescope (czData P Fq z) drow
    (fun i => β i - powSeq z P.k₀ i) P.k₀
  rw [hif] at h
  rw [hβ, h, hcz]

/-! ## The node pairing (`lem:fullslice` Step 2, the `⟨·, V⟩` functional)

`nodePair δ j w = ⟨w, V_j⟩` pairs a class-vector against block `j`'s node
values `V_{s,j} = û_s(ν_j)`. It is `Fq`-linear, so the staircase decompositions
(`eqPoly_mixedPoint_decomp`, `eta_telescope`) pass through it: the slice value is
`⟨êq(mixed), V_j⟩` and the terminal node pairing is `⟨êq(α), V_j⟩`. -/

/-- The pairing of a class-vector against block `j`'s node values. -/
def nodePair (δ : Cell P → Fp P) (j : Fin 2) (w : Cube P.k₀ → Fq) : Fq :=
  ∑ s, w s * mle (fun c => liftT P Fq δ (s, c)) (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)

theorem nodePair_add (δ : Cell P → Fp P) (j : Fin 2) (w w' : Cube P.k₀ → Fq) :
    nodePair P Fq Dom ch δ j (w + w') =
      nodePair P Fq Dom ch δ j w + nodePair P Fq Dom ch δ j w' := by
  unfold nodePair
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by rw [Pi.add_apply]; ring

theorem nodePair_smul (δ : Cell P → Fp P) (j : Fin 2) (c : Fq)
    (w : Cube P.k₀ → Fq) :
    nodePair P Fq Dom ch δ j (c • w) = c * nodePair P Fq Dom ch δ j w := by
  unfold nodePair
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by rw [Pi.smul_apply, smul_eq_mul]; ring

theorem nodePair_sum (δ : Cell P → Fp P) (j : Fin 2) {ι : Type*} (t : Finset ι)
    (f : ι → Cube P.k₀ → Fq) :
    nodePair P Fq Dom ch δ j (∑ i ∈ t, f i) =
      ∑ i ∈ t, nodePair P Fq Dom ch δ j (f i) := by
  unfold nodePair
  simp only [Finset.sum_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The slice value is the node pairing of the mixed-point Lagrange weight. -/
theorem evalT_mixed_eq_nodePair (δ : Cell P → Fp P) (j : Fin 2) (ℓ : Fin P.k₀)
    (y : Fq) :
    evalT P Fq δ (mixedPoint P Fq Dom ch ℓ y (powSeq (ch.z j) P.k₀))
        (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) =
      nodePair P Fq Dom ch δ j
        (eqPoly (mixedPoint P Fq Dom ch ℓ y (powSeq (ch.z j) P.k₀))) := by
  rw [evalT_eq_sum_classes]; rfl

/-- **The terminal node pairing telescopes**: `⟨η, V_j⟩ = ⟨êq(powz_j), V_j⟩ +
∑_i λ_i ⟨τ^j_i, V_j⟩` — the `η`-target in node-pairing form. -/
theorem nodePair_eta (δ : Cell P → Fp P) (j : Fin 2) :
    nodePair P Fq Dom ch δ j (eqPoly (ch.α)) =
      nodePair P Fq Dom ch δ j (eqPoly (powSeq (ch.z j) P.k₀))
      + ∑ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => (i : ℕ) < P.k₀),
          lamData P Fq Dom ch (ch.z j) i *
            nodePair P Fq Dom ch δ j
              (ptensor (stairVec (czData P Fq (ch.z j)) (fun _ => drow)
                (lamData P Fq Dom ch (ch.z j)) i)) := by
  rw [eta_telescope P Fq Dom ch (ch.z j), nodePair_add, nodePair_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => nodePair_smul P Fq Dom ch δ j _ _

/-- **The node functional in pairing form** (`lem:fullslice` Step 2c, clean): the
slice value is `⟨ρ^j_ℓ, V_j⟩ + (y − ζ_j)·⟨τ^j_ℓ, V_j⟩`, the affine node
functional `g^j_ℓ(y)`, with `⟨ρ^j_ℓ, V_j⟩` itself telescoped. -/
theorem evalT_mixed_nodePair_decomp (δ : Cell P → Fp P) (j : Fin 2)
    (ℓ : Fin P.k₀) (y : Fq) :
    evalT P Fq δ (mixedPoint P Fq Dom ch ℓ y (powSeq (ch.z j) P.k₀))
        (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) =
      nodePair P Fq Dom ch δ j (eqPoly (powSeq (ch.z j) P.k₀))
      + (∑ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < ℓ),
          lamData P Fq Dom ch (ch.z j) i *
            nodePair P Fq Dom ch δ j
              (ptensor (stairVec (czData P Fq (ch.z j)) (fun _ => drow)
                (lamData P Fq Dom ch (ch.z j)) i)))
      + (y - powSeq (ch.z j) P.k₀ ℓ) *
          nodePair P Fq Dom ch δ j
            (ptensor (stairVec (czData P Fq (ch.z j)) (fun _ => drow)
              (lamData P Fq Dom ch (ch.z j)) ℓ)) := by
  rw [evalT_mixed_eq_nodePair, eqPoly_mixedPoint_decomp, nodePair_add,
    nodePair_add, nodePair_smul, nodePair_sum]
  congr 1
  congr 1
  exact Finset.sum_congr rfl fun i _ => nodePair_smul P Fq Dom ch δ j _ _

/-! ## The (S, R) moment matrix and its minor (`lem:fullslice` Step 2 solve)

The moment-to-`(S, R)` map sends `(m₀, m₁, m₂)` to the staircase coefficients
`S = (1−ζ)m₀ + (2ζ−1)m₁` and `R = −ζ(1−ζ)m₀ + (1−2ζ²)m₁ + (2ζ−1)m₂`. The
η-matching at the top two levels is solvable when the 3×3 minor on
`(S¹, R¹, R²)` is nonzero; specialized at `ζ₁ = 0` it equals `ζ₂(1−ζ₂)`,
witnessing that the minor is not identically zero (the Schwartz–Zippel input to
the slice-condition probability). -/

/-- The `(S, R)` staircase coefficients of a moment vector at slot value `ζ`. -/
def momS (ζ m₀ m₁ : Fq) : Fq := (1 - ζ) * m₀ + (2 * ζ - 1) * m₁

def momR (ζ m₀ m₁ m₂ : Fq) : Fq :=
  -(ζ * (1 - ζ)) * m₀ + (1 - 2 * ζ ^ 2) * m₁ + (2 * ζ - 1) * m₂

/-- **The Step-2 minor at `ζ₁ = 0`** is `ζ₂(1−ζ₂)`: the 3×3 determinant of the
coefficient matrix of `(S¹, R¹, R²)` in `(m₀, m₁, m₂)`, specialized at `ζ₁ = 0`,
is nonzero whenever `ζ₂ ∉ {0, 1}`. -/
theorem moment_minor_det_at_zero (ζ : Fq) :
    Matrix.det !![(1 : Fq), -1, 0;
        0, 1, -1;
        -(ζ * (1 - ζ)), 1 - 2 * ζ ^ 2, 2 * ζ - 1] = ζ * (1 - ζ) := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
    Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- **The Step-2 minor is invertible off the hypersurface** `ζ(1−ζ) = 0`: with
`ζ ∉ {0,1}` the `(S¹,R¹,R²)` coefficient matrix (at `ζ₁ = 0`) has a unit
determinant. -/
theorem moment_minor_isUnit (ζ : Fq) (hζ : ζ * (1 - ζ) ≠ 0) :
    IsUnit (Matrix.det !![(1 : Fq), -1, 0;
        0, 1, -1;
        -(ζ * (1 - ζ)), 1 - 2 * ζ ^ 2, 2 * ζ - 1]) := by
  rw [moment_minor_det_at_zero]
  exact isUnit_iff_ne_zero.mpr hζ

/-- **The `(S,R)` matching system is solvable** (`lem:fullslice` Step 2 solve):
off `ζ(1−ζ) = 0`, every target `(S¹,R¹,R²)` is realized by some moment vector
`(m₀,m₁,m₂)`. The linear-algebra core of the η-match. -/
theorem moment_minor_solvable (ζ : Fq) (hζ : ζ * (1 - ζ) ≠ 0) (b : Fin 3 → Fq) :
    ∃ m : Fin 3 → Fq, (!![(1 : Fq), -1, 0;
        0, 1, -1;
        -(ζ * (1 - ζ)), 1 - 2 * ζ ^ 2, 2 * ζ - 1]).mulVec m = b :=
  exists_mulVec_of_isUnit_det _ (moment_minor_isUnit Fq ζ hζ) b

/-- **The general-challenge `(S,R)` minor factors** (`lem:fullslice` Step 2, the
two-block η-match): the `(S¹,R¹,R²)` coefficient matrix at diagonals `ζ₁` (block 1)
and `ζ₂` (block 2) has determinant `(ζ₁−ζ₂)·(ζ₁+ζ₂−1−2ζ₁ζ₂)`. At `ζ₁ = 0` this is
`ζ₂(1−ζ₂)` (recovering `moment_minor_det_at_zero`), so the minor is a nonzero
polynomial — the Schwartz–Zippel input, and the invertibility certificate for the
η-match solve at general challenges. -/
theorem moment_minor_det_general (ζ₁ ζ₂ : Fq) :
    Matrix.det !![1 - ζ₁, 2 * ζ₁ - 1, 0;
        -(ζ₁ * (1 - ζ₁)), 1 - 2 * ζ₁ ^ 2, 2 * ζ₁ - 1;
        -(ζ₂ * (1 - ζ₂)), 1 - 2 * ζ₂ ^ 2, 2 * ζ₂ - 1] =
      (ζ₁ - ζ₂) * (ζ₁ + ζ₂ - 1 - 2 * ζ₁ * ζ₂) := by
  rw [Matrix.det_fin_three]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.head_fin_const,
    Matrix.cons_val_fin_one, Matrix.empty_val', Matrix.cons_val_two,
    Matrix.tail_cons]
  ring

/-- The general η-match matrix is invertible off its (factored) hypersurface
`ζ₁ = ζ₂` or `ζ₁+ζ₂ = 1+2ζ₁ζ₂` — the invertibility certificate for the solve at
general challenges. -/
theorem moment_minor_general_isUnit (ζ₁ ζ₂ : Fq)
    (h1 : ζ₁ - ζ₂ ≠ 0) (h2 : ζ₁ + ζ₂ - 1 - 2 * ζ₁ * ζ₂ ≠ 0) :
    IsUnit (Matrix.det !![1 - ζ₁, 2 * ζ₁ - 1, 0;
        -(ζ₁ * (1 - ζ₁)), 1 - 2 * ζ₁ ^ 2, 2 * ζ₁ - 1;
        -(ζ₂ * (1 - ζ₂)), 1 - 2 * ζ₂ ^ 2, 2 * ζ₂ - 1]) := by
  rw [moment_minor_det_general]
  exact isUnit_iff_ne_zero.mpr (mul_ne_zero h1 h2)

/-- **The η-match matrix `mulVec` is the `(momS, momR, momR)` map**: the general
matrix applied to a moment vector `m` yields `(momS(ζ₁), momR(ζ₁), momR(ζ₂))` — so
solving `M·m = (S¹,R¹,R²)` (via `exists_points_for_target`) gives moments whose
`momS`/`momR` hit the matched targets. The bridge between the matrix solve and the
`momS`/`momR` appearing in `channel_moment_SR`. -/
theorem moment_minor_mulVec (ζ₁ ζ₂ : Fq) (m : Fin 3 → Fq) :
    (!![1 - ζ₁, 2 * ζ₁ - 1, 0;
        -(ζ₁ * (1 - ζ₁)), 1 - 2 * ζ₁ ^ 2, 2 * ζ₁ - 1;
        -(ζ₂ * (1 - ζ₂)), 1 - 2 * ζ₂ ^ 2, 2 * ζ₂ - 1]).mulVec m =
      ![momS Fq ζ₁ (m 0) (m 1), momR Fq ζ₁ (m 0) (m 1) (m 2),
        momR Fq ζ₂ (m 0) (m 1) (m 2)] := by
  funext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, momS, momR] <;> ring

/-- **Point-coefficients realizing any `(S,R)` target** (`lem:fullslice` Step 2
solve, complete moment-finding): for an invertible coefficient matrix `M` and
distinct evaluation points `y`, every target `b` is realized by a `3`-point
combination `μ` whose moment vector `(∑ₜ μₜ yₜ^h)ₕ` maps to `b` under `M`.
Combines `exists_mulVec_of_isUnit_det` (matrix solve) with
`exists_coeffs_of_moments` (Vandermonde inversion). -/
theorem exists_points_for_target (M : Matrix (Fin 3) (Fin 3) Fq) (hM : IsUnit M.det)
    (y : Fin 3 → Fq) (hy : Function.Injective y) (b : Fin 3 → Fq) :
    ∃ μ : Fin 3 → Fq, M.mulVec (fun h => ∑ t, μ t * y t ^ (h : ℕ)) = b := by
  obtain ⟨m, hm⟩ := exists_mulVec_of_isUnit_det M hM b
  obtain ⟨μ, hμ⟩ := exists_coeffs_of_moments y hy m
  refine ⟨μ, ?_⟩
  have hfun : (fun h : Fin 3 => ∑ t, μ t * y t ^ (h : ℕ)) = m := by
    funext h; exact hμ h
  rw [hfun]; exact hm

/-- **Per-level `(S,R)` moment realization** (`lem:fullslice` Step 2 solve): off
the hypersurface, every target `(S¹,R¹,R²)` is realized by a moment vector `m`
with `momS(ζ₁) = S¹`, `momR(ζ₁) = R¹`, `momR(ζ₂) = R²`. Combines
`exists_points_for_target`, `moment_minor_general_isUnit`, and `moment_minor_mulVec`. -/
theorem exists_moments_realizing_SR (ζ₁ ζ₂ : Fq)
    (h1 : ζ₁ - ζ₂ ≠ 0) (h2 : ζ₁ + ζ₂ - 1 - 2 * ζ₁ * ζ₂ ≠ 0)
    (y : Fin 3 → Fq) (hy : Function.Injective y) (S1 R1 R2 : Fq) :
    ∃ m : Fin 3 → Fq,
      momS Fq ζ₁ (m 0) (m 1) = S1 ∧ momR Fq ζ₁ (m 0) (m 1) (m 2) = R1 ∧
      momR Fq ζ₂ (m 0) (m 1) (m 2) = R2 := by
  obtain ⟨μ, hμ⟩ := exists_points_for_target Fq
    !![1 - ζ₁, 2 * ζ₁ - 1, 0; -(ζ₁ * (1 - ζ₁)), 1 - 2 * ζ₁ ^ 2, 2 * ζ₁ - 1;
       -(ζ₂ * (1 - ζ₂)), 1 - 2 * ζ₂ ^ 2, 2 * ζ₂ - 1]
    (moment_minor_general_isUnit Fq ζ₁ ζ₂ h1 h2) y hy ![S1, R1, R2]
  rw [moment_minor_mulVec] at hμ
  refine ⟨fun h => ∑ t, μ t * y t ^ (h : ℕ), ?_, ?_, ?_⟩
  · simpa using congrFun hμ 0
  · simpa using congrFun hμ 1
  · simpa using congrFun hμ 2

/-- **The η-match combination identity** (`lem:fullslice` Step 2, tex:582–584).
With the matching coefficients `S_lo = Θ − S_hi`, `R_lo = λ_lo·(Θ − S_hi)`,
`R_hi = λ_hi·Θ` at the top two levels (`ρ_hi = ρ_lo + λ_lo·τ_lo`, `η = ρ_hi +
λ_hi·τ_hi`), the two-level node combination equals `Θ·η`. Pure linear algebra —
the `lem:fullslice` analog of `coupled_repr_block1/2`. -/
theorem eta_match_combo {V : Type*} [AddCommGroup V] [Module Fq V]
    (ρlo ρhi τlo τhi η : V) (lamlo lamhi Θ S_hi : Fq)
    (hρ : ρhi = ρlo + lamlo • τlo) (hη : η = ρhi + lamhi • τhi) :
    (Θ - S_hi) • ρlo + (lamlo * (Θ - S_hi)) • τlo + S_hi • ρhi + (lamhi * Θ) • τhi =
      Θ • η := by
  subst hρ hη
  match_scalars <;> ring

/-- **The `S`-coefficient is the moment combination of the `eqf` weight**
(`lem:fullslice` Step 2, tex:577): with moments `m₀ = ∑ μ_t`, `m₁ = ∑ μ_t y_t`,
the `ρ`-coefficient `momS ζ m₀ m₁` equals `∑_t μ_t · êq(y_t, ζ)`, since the
single-coordinate weight `êq(y, ζ) = (1−ζ) + (2ζ−1)y`. -/
theorem momS_moment_combo {n : ℕ} (ζ : Fq) (μ y : Fin n → Fq) :
    momS Fq ζ (∑ t, μ t) (∑ t, μ t * y t) = ∑ t, μ t * eqf Fq (y t) ζ := by
  unfold momS eqf
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- **The `R`-coefficient is the `(y − ζ)`-weighted moment combination**
(`lem:fullslice` Step 2, tex:578): `momR ζ m₀ m₁ m₂ = ∑_t μ_t · êq(y_t, ζ)·(y_t − ζ)`,
the `τ`-coefficient of the `μ`-combination of `g(y) = ρ + (y − ζ)τ`. -/
theorem momR_moment_combo {n : ℕ} (ζ : Fq) (μ y : Fin n → Fq) :
    momR Fq ζ (∑ t, μ t) (∑ t, μ t * y t) (∑ t, μ t * y t ^ 2) =
      ∑ t, μ t * (eqf Fq (y t) ζ * (y t - ζ)) := by
  unfold momR eqf
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

/-! ## The cross-form `F_θ` (`lem:fullslice` Step 3, foundation)

`F_θ(δ) = ∑_j θ_j·⟨η_j, V_j⟩` pairs the extension rows against the
perturbation's node values. Since `η_j = êq(α, ·)`, its block-`j` pairing is the
fold `f̂₁` evaluated at the commitment node `z_j^{2^k₀}`; so `F_θ` is a `θ`-combination
of fold values — the quantity the cross-coupling (`cond:cross2`) and the slice
trace argument (`lem:fullslice` Step 4) constrain. -/

/-- The η-pairing of block `j` is the fold `f̂₁` at the commitment node. -/
theorem nodePair_alpha_eq_fold (δ : Cell P → Fp P) (j : Fin 2) :
    nodePair P Fq Dom ch δ j (eqPoly (ch.α)) =
      mle (foldedF₁ P Fq Dom δ ch) (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) := by
  rw [← evalT_alpha_eq_mle_fold P Fq Dom δ ch, evalT_eq_sum_classes]
  rfl

/-- The telescoped node-pairing `⟨ρ^j_ℓ, V_j⟩`. -/
def nodePairRho (δ : Cell P → Fp P) (j : Fin 2) (ℓ : Fin P.k₀) : Fq :=
  nodePair P Fq Dom ch δ j (eqPoly (powSeq (ch.z j) P.k₀))
  + ∑ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < ℓ),
      lamData P Fq Dom ch (ch.z j) i *
        nodePair P Fq Dom ch δ j
          (ptensor (stairVec (czData P Fq (ch.z j)) (fun _ => drow)
            (lamData P Fq Dom ch (ch.z j)) i))

/-- The slot node-pairing `⟨τ^j_ℓ, V_j⟩`. -/
def nodePairTau (δ : Cell P → Fp P) (j : Fin 2) (ℓ : Fin P.k₀) : Fq :=
  nodePair P Fq Dom ch δ j
    (ptensor (stairVec (czData P Fq (ch.z j)) (fun _ => drow)
      (lamData P Fq Dom ch (ch.z j)) ℓ))

/-- **Inter-level telescoping of the node `ρ`-pairing**: for `m ≤ m'`,
`⟨ρ_{m'}, V⟩ = ⟨ρ_m, V⟩ + ∑_{m ≤ i < m'} λ_i ⟨τ_i, V⟩`. Supplies the `hρ`
hypothesis of `eta_match_combo` (consecutive levels give a single tail term). -/
theorem nodePairRho_diff (δ : Cell P → Fp P) (j : Fin 2) (m m' : Fin P.k₀)
    (hmm : m ≤ m') :
    nodePairRho P Fq Dom ch δ j m' =
      nodePairRho P Fq Dom ch δ j m +
        ∑ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => m ≤ i ∧ i < m'),
          lamData P Fq Dom ch (ch.z j) i * nodePairTau P Fq Dom ch δ j i := by
  unfold nodePairRho nodePairTau
  rw [add_assoc]
  congr 1
  have hsub : (Finset.univ.filter (fun i : Fin P.k₀ => i < m)) ⊆
      Finset.univ.filter (fun i : Fin P.k₀ => i < m') := fun i hi =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      lt_of_lt_of_le (Finset.mem_filter.mp hi).2 hmm⟩
  rw [← Finset.sum_sdiff hsub, add_comm]
  congr 1
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext i
  simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
  tauto

/-- **Consecutive-level `ρ`-pairing relation** (the `hρ` of `eta_match_combo`):
when `m'` is the immediate successor of `m` (no level strictly between),
`⟨ρ_{m'}, V⟩ = ⟨ρ_m, V⟩ + λ_m·⟨τ_m, V⟩`. -/
theorem nodePairRho_succ (δ : Cell P → Fp P) (j : Fin 2) (m m' : Fin P.k₀)
    (hmm : m < m') (hcons : ∀ i : Fin P.k₀, m ≤ i → i < m' → i = m) :
    nodePairRho P Fq Dom ch δ j m' =
      nodePairRho P Fq Dom ch δ j m +
        lamData P Fq Dom ch (ch.z j) m * nodePairTau P Fq Dom ch δ j m := by
  rw [nodePairRho_diff P Fq Dom ch δ j m m' (le_of_lt hmm)]
  congr 1
  have hfilter : Finset.univ.filter (fun i : Fin P.k₀ => m ≤ i ∧ i < m') = {m} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; exact hcons i h1 h2
    · rintro rfl; exact ⟨le_refl _, hmm⟩
  rw [hfilter, Finset.sum_singleton]

/-- **The node functional `g^j_ℓ(y)`** in `ρ/τ` shorthand: `⟨ρ, V⟩ + (y − ζ)·⟨τ, V⟩`. -/
theorem evalT_mixed_rho_tau (δ : Cell P → Fp P) (j : Fin 2) (ℓ : Fin P.k₀)
    (y : Fq) :
    evalT P Fq δ (mixedPoint P Fq Dom ch ℓ y (powSeq (ch.z j) P.k₀))
        (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) =
      nodePairRho P Fq Dom ch δ j ℓ
      + (y - powSeq (ch.z j) P.k₀ ℓ) * nodePairTau P Fq Dom ch δ j ℓ := by
  rw [evalT_mixed_nodePair_decomp]; rfl

/-- **The `(S,R)` decomposition of the `eqf`-weighted moment combination**
(`lem:fullslice` Step 2): the `μ`-combination of the node functionals
`êq(y_t, ζ)·g^j_ℓ(y_t)` (with `g^j_ℓ(y) = ρ + (y−ζ)τ`, `ζ = z_j^{2^{ℓ-1}}`) has
node part `S·ρ^{(j)}_ℓ + R·τ^{(j)}_ℓ`, where `S = momS`, `R = momR` are the moment
coefficients. Combines `evalT_mixed_rho_tau` (slot decomposition of `g`) with
`momS/momR_moment_combo` (moment expansion of the `êq` weight). -/
theorem evalT_eqf_moment_SR {n : ℕ} (δ : Cell P → Fp P) (j : Fin 2) (ℓ : Fin P.k₀)
    (μ y : Fin n → Fq) :
    (∑ t, μ t * (eqf Fq (y t) (powSeq (ch.z j) P.k₀ ℓ) *
        evalT P Fq δ (mixedPoint P Fq Dom ch ℓ (y t) (powSeq (ch.z j) P.k₀))
          (powSeq (ch.z j ^ 2 ^ P.k₀) P.m))) =
      momS Fq (powSeq (ch.z j) P.k₀ ℓ) (∑ t, μ t) (∑ t, μ t * y t) *
          nodePairRho P Fq Dom ch δ j ℓ +
      momR Fq (powSeq (ch.z j) P.k₀ ℓ) (∑ t, μ t) (∑ t, μ t * y t)
          (∑ t, μ t * y t ^ 2) * nodePairTau P Fq Dom ch δ j ℓ := by
  have h1 : ∀ t, evalT P Fq δ (mixedPoint P Fq Dom ch ℓ (y t) (powSeq (ch.z j) P.k₀))
      (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) =
      nodePairRho P Fq Dom ch δ j ℓ +
        (y t - powSeq (ch.z j) P.k₀ ℓ) * nodePairTau P Fq Dom ch δ j ℓ :=
    fun t => evalT_mixed_rho_tau P Fq Dom ch δ j ℓ (y t)
  simp_rw [h1]
  conv_rhs => rw [momS_moment_combo, momR_moment_combo]
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- **The block-`j` moment term is `Π^j·(S·ρ + R·τ)`** (`lem:fullslice` Step 2,
the form `channel_moment_of_viewKer` feeds): factoring `prefixFactor` into the
`α`-prefix `Π^j = ∏_{i<ℓ} êq(α_i, z_j^{2^{i-1}})` and the slot weight `êq(y,ζ)`,
the `w`-moment of the block-`j` `y`-family is the `α`-prefix times the `(S,R)`
node combination. -/
theorem block_moment_SR (δ : Cell P → Fp P) (j : Fin 2) (ℓ : Fin P.k₀)
    (w pts : Fin 3 → Fq) :
    (∑ t, w t * (prefixFactor P Fq Dom ch ℓ (pts t) (powSeq (ch.z j) P.k₀) *
        evalT P Fq δ (mixedPoint P Fq Dom ch ℓ (pts t) (powSeq (ch.z j) P.k₀))
          (powSeq (ch.z j ^ 2 ^ P.k₀) P.m))) =
      (∏ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < ℓ),
          eqf Fq (ch.α i) (powSeq (ch.z j) P.k₀ i)) *
        (momS Fq (powSeq (ch.z j) P.k₀ ℓ) (∑ t, w t) (∑ t, w t * pts t) *
            nodePairRho P Fq Dom ch δ j ℓ +
          momR Fq (powSeq (ch.z j) P.k₀ ℓ) (∑ t, w t) (∑ t, w t * pts t)
              (∑ t, w t * pts t ^ 2) * nodePairTau P Fq Dom ch δ j ℓ) := by
  have hpf : ∀ t, prefixFactor P Fq Dom ch ℓ (pts t) (powSeq (ch.z j) P.k₀) =
      (∏ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < ℓ),
          eqf Fq (ch.α i) (powSeq (ch.z j) P.k₀ i)) *
        eqf Fq (pts t) (powSeq (ch.z j) P.k₀ ℓ) := fun t => prefixFactor_eq P Fq Dom ch ℓ (pts t) _
  simp_rw [hpf]
  conv_rhs => rw [← evalT_eqf_moment_SR P Fq Dom ch δ j ℓ w pts, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

/-- **The full `y`-family moment identity in `(S,R)` form** (`lem:fullslice`
Step 2): for a view-vanishing perturbation, the `w`-moment of the two-block
`y`-family equals `Π^0·(S^0ρ^0+R^0τ^0) + γ·Π^1·(S^1ρ^1+R^1τ^1) + γ²·(cross moment) = 0`.
This is `channel_moment_of_viewKer` rewritten through `block_moment_SR` on each
block — the moment system the η-matching of Step 2 solves. -/
theorem channel_moment_SR (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S)
    (κ : viewKer P Fq Dom S ch) (ℓ : Fin P.k₀) (w pts : Fin 3 → Fq) :
    (∏ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < ℓ),
        eqf Fq (ch.α i) (powSeq (ch.z 0) P.k₀ i)) *
      (momS Fq (powSeq (ch.z 0) P.k₀ ℓ) (∑ t, w t) (∑ t, w t * pts t) *
          nodePairRho P Fq Dom ch (assemble P 0 (-κ.1)) 0 ℓ +
        momR Fq (powSeq (ch.z 0) P.k₀ ℓ) (∑ t, w t) (∑ t, w t * pts t)
            (∑ t, w t * pts t ^ 2) * nodePairTau P Fq Dom ch (assemble P 0 (-κ.1)) 0 ℓ) +
    ch.γ * ((∏ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < ℓ),
        eqf Fq (ch.α i) (powSeq (ch.z 1) P.k₀ i)) *
      (momS Fq (powSeq (ch.z 1) P.k₀ ℓ) (∑ t, w t) (∑ t, w t * pts t) *
          nodePairRho P Fq Dom ch (assemble P 0 (-κ.1)) 1 ℓ +
        momR Fq (powSeq (ch.z 1) P.k₀ ℓ) (∑ t, w t) (∑ t, w t * pts t)
            (∑ t, w t * pts t ^ 2) * nodePairTau P Fq Dom ch (assemble P 0 (-κ.1)) 1 ℓ)) +
    ch.γ ^ 2 * (∑ t, w t *
        crossTerm P Fq Dom S (assemble P 0 (-κ.1)) ch ℓ (pts t)) = 0 := by
  have h := channel_moment_of_viewKer P Fq Dom S ch h2 hmf κ ℓ w pts
  rw [block_moment_SR P Fq Dom ch (assemble P 0 (-κ.1)) 0 ℓ w pts,
    block_moment_SR P Fq Dom ch (assemble P 0 (-κ.1)) 1 ℓ w pts] at h
  exact h

/-- **The cross-form** `F_θ`: the `θ`-weighted pairing of the extension rows
against the perturbation's node values. -/
def crossForm (δ : Cell P → Fp P) (θ : Fin 2 → Fq) : Fq :=
  θ 0 * nodePair P Fq Dom ch δ 0 (eqPoly (ch.α)) +
    θ 1 * nodePair P Fq Dom ch δ 1 (eqPoly (ch.α))

/-- `F_θ` in fold form: a `θ`-combination of the fold at the two commitment
nodes. -/
theorem crossForm_eq_fold (δ : Cell P → Fp P) (θ : Fin 2 → Fq) :
    crossForm P Fq Dom ch δ θ =
      θ 0 * mle (foldedF₁ P Fq Dom δ ch) (powSeq (ch.z 0 ^ 2 ^ P.k₀) P.m) +
        θ 1 * mle (foldedF₁ P Fq Dom δ ch) (powSeq (ch.z 1 ^ 2 ^ P.k₀) P.m) := by
  unfold crossForm
  rw [nodePair_alpha_eq_fold, nodePair_alpha_eq_fold]

/-- `F_θ` is additive in the direction `θ` (`cond:cross2` uses `Fq`-linearity of
`θ ↦ F_θ`, tex:553). -/
theorem crossForm_theta_add (δ : Cell P → Fp P) (θ θ' : Fin 2 → Fq) :
    crossForm P Fq Dom ch δ (θ + θ') =
      crossForm P Fq Dom ch δ θ + crossForm P Fq Dom ch δ θ' := by
  unfold crossForm; simp only [Pi.add_apply]; ring

/-- `F_θ` is homogeneous in the direction `θ` (`cond:cross2` `Fq`-linearity). -/
theorem crossForm_theta_smul (δ : Cell P → Fp P) (a : Fq) (θ : Fin 2 → Fq) :
    crossForm P Fq Dom ch δ (a • θ) = a * crossForm P Fq Dom ch δ θ := by
  unfold crossForm; simp only [Pi.smul_apply, smul_eq_mul]; ring

/-- **The cross form as a node-value pairing** (the `prop:pinbound` assembly
bridge): `F_θ(δ) = ∑_{s,j} θ_j·êq(α,s)·V_{s,j}` where `V_{s,j} = ⟨δ-fiber of class
`s`, node `j`⟩`. This is exactly the form `nodechannel_untwisted` constrains, so
it ties the node-channel output `θ` to the cross form on a perturbation. -/
theorem crossForm_eq_nodeValues (δ : Cell P → Fp P) (θ : Fin 2 → Fq) :
    crossForm P Fq Dom ch δ θ =
      ∑ s, ∑ j, θ j * eqPoly ch.α s *
        mle (fun c => liftT P Fq δ (s, c)) (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) := by
  unfold crossForm nodePair
  simp_rw [Fin.sum_univ_two]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- **The ood row of a perturbation's node values is its ood answer**: the
`z_j`-weighted node value equals `evalT` at the commitment node, i.e. the
out-of-domain answer. So a view-vanishing mask (`oodAnswer = 0`) kills `oodRow` —
but its `msgRow` carries the cross term (the message, not the ood answer, holds
`γ²·crossTerm`), which is why the cross form `F_θ` survives on it. -/
theorem oodRow_nodeValues (δ : Cell P → Fp P) (j : Fin 2) :
    oodRow P Fq Dom ch j
      (fun s j' => mle (fun c => liftT P Fq δ (s, c))
        (powSeq (ch.z j' ^ 2 ^ P.k₀) P.m)) =
      oodAnswer P Fq δ (ch.z j) := by
  unfold oodRow oodAnswer
  rw [evalT_eq_sum_classes]

/-- **The message row of a perturbation's node values, plus the cross term, is
its message** (`hPoly_channel` in node-value form): `msgRow + γ²·crossTerm = hPoly`.
So for a view-vanishing mask (`hPoly = 0`), `msgRow(V) = −γ²·crossTerm` — the cross
form `F_θ` is carried by the message row, not the ood row. -/
theorem msgRow_nodeValues (δ : Cell P → Fp P) (ℓ : Fin P.k₀) (y : Fq) :
    msgRow P Fq Dom ch ℓ y
        (fun s j' => mle (fun c => liftT P Fq δ (s, c))
          (powSeq (ch.z j' ^ 2 ^ P.k₀) P.m))
      + ch.γ ^ 2 * crossTerm P Fq Dom S δ ch ℓ y =
      hPoly P Fq Dom S δ ch ℓ y := by
  unfold msgRow
  rw [hPoly_channel, evalT_eq_sum_classes, evalT_eq_sum_classes]

/-- **A view-vanishing mask's node values kill the ood rows**: since
`oodAnswer = 0` on `viewKer`, `oodRow_j(V(κ)) = 0`. (The message rows, by
contrast, are pinned to `−γ²·crossTerm`.) -/
theorem oodRow_viewKer (κ : viewKer P Fq Dom S ch) (j : Fin 2) :
    oodRow P Fq Dom ch j
      (fun s j' => mle (fun c => liftT P Fq (assemble P 0 (-κ.1)) (s, c))
        (powSeq (ch.z j' ^ 2 ^ P.k₀) P.m)) = 0 := by
  rw [oodRow_nodeValues]; exact κ.2.ood j

/-- **A view-vanishing mask's message row (at `X = 1`) is pinned to the cross
term**: since `hPoly = 0` on `viewKer`, `msgRow_ℓ(V(κ)) = −γ²·crossTerm`. This
exhibits the cross form on the surviving (message) channel — the input to
`lem:noother`'s membership identity. -/
theorem msgRow_viewKer_one (κ : viewKer P Fq Dom S ch) (ℓ : Fin P.k₀) :
    msgRow P Fq Dom ch ℓ 1
        (fun s j' => mle (fun c => liftT P Fq (assemble P 0 (-κ.1)) (s, c))
          (powSeq (ch.z j' ^ 2 ^ P.k₀) P.m)) =
      - (ch.γ ^ 2 * crossTerm P Fq Dom S (assemble P 0 (-κ.1)) ch ℓ 1) := by
  have h := msgRow_nodeValues P Fq Dom S ch (assemble P 0 (-κ.1)) ℓ 1
  rw [κ.2.msg1 ℓ] at h
  exact eq_neg_of_add_eq_zero_left h

/-- **`cond:cross2` injectivity heart (Cramer).** If two mask perturbations
`δ, δ''` give a nonzero `2×2` node-pairing minor, then the only direction `θ`
killing `F_θ` at both is `θ = 0` — i.e. `θ ↦ F_θ` is injective. This is the
abstract content of the cross-form non-degeneracy (tex:529–545): the SZ argument
exhibits such a minor, and this lemma turns it into `F_θ ≠ 0` for every `θ ≠ 0`. -/
theorem crossForm_eq_zero_pair_imp_theta_zero (δ δ'' : Cell P → Fp P)
    (θ : Fin 2 → Fq)
    (hminor :
      nodePair P Fq Dom ch δ 0 (eqPoly ch.α) *
          nodePair P Fq Dom ch δ'' 1 (eqPoly ch.α) -
        nodePair P Fq Dom ch δ 1 (eqPoly ch.α) *
          nodePair P Fq Dom ch δ'' 0 (eqPoly ch.α) ≠ 0)
    (h1 : crossForm P Fq Dom ch δ θ = 0)
    (h2 : crossForm P Fq Dom ch δ'' θ = 0) :
    θ = 0 := by
  unfold crossForm at h1 h2
  set g00 := nodePair P Fq Dom ch δ 0 (eqPoly ch.α) with hg00
  set g01 := nodePair P Fq Dom ch δ 1 (eqPoly ch.α) with hg01
  set g10 := nodePair P Fq Dom ch δ'' 0 (eqPoly ch.α) with hg10
  set g11 := nodePair P Fq Dom ch δ'' 1 (eqPoly ch.α) with hg11
  have hθ0 : θ 0 * (g00 * g11 - g01 * g10) = 0 := by
    linear_combination g11 * h1 - g01 * h2
  have hθ1 : θ 1 * (g00 * g11 - g01 * g10) = 0 := by
    linear_combination g00 * h2 - g10 * h1
  have e0 : θ 0 = 0 := (mul_eq_zero.mp hθ0).resolve_right hminor
  have e1 : θ 1 = 0 := (mul_eq_zero.mp hθ1).resolve_right hminor
  funext i
  fin_cases i
  · exact e0
  · exact e1

/-- **`cond:cross2` conclusion (witnessed form).** A nonzero `2×2` node minor on
two mask cells `δ, δ''` certifies the cross form's non-degeneracy: for every
direction `θ ≠ 0`, `F_θ` is nonzero on at least one of the two cells. This is the
form `prop:pinbound`/`lem:fullslice` consume (`F_θ ≠ 0 ∀ θ ≠ 0`); the value-row
Schwartz–Zippel argument supplies the witness minor (tex:543, via `lem:binpow`). -/
theorem crossForm_ne_zero_of_minor (δ δ'' : Cell P → Fp P) (θ : Fin 2 → Fq)
    (hθ : θ ≠ 0)
    (hminor :
      nodePair P Fq Dom ch δ 0 (eqPoly ch.α) *
          nodePair P Fq Dom ch δ'' 1 (eqPoly ch.α) -
        nodePair P Fq Dom ch δ 1 (eqPoly ch.α) *
          nodePair P Fq Dom ch δ'' 0 (eqPoly ch.α) ≠ 0) :
    crossForm P Fq Dom ch δ θ ≠ 0 ∨ crossForm P Fq Dom ch δ'' θ ≠ 0 := by
  by_contra h
  push_neg at h
  exact hθ (crossForm_eq_zero_pair_imp_theta_zero P Fq Dom ch δ δ'' θ hminor h.1 h.2)

/-- **`cond:cross2` conclusion in the `prop:pinbound` form**: a view-vanishing
witness pair `κ, κ''` with a nonzero `2×2` node minor certifies that, for every
`θ ≠ 0`, the pure node form `∑_j θ_j η_j` is nonzero on some view-vanishing
mask-fold — i.e. it does not lie in `ann(W')`. The value-row Schwartz–Zippel
argument supplies the witness pair; this packages the consequence. -/
theorem cond_cross2_conclusion (κ κ'' : viewKer P Fq Dom S ch)
    (θ : Fin 2 → Fq) (hθ : θ ≠ 0)
    (hminor :
      nodePair P Fq Dom ch (assemble P 0 (-κ.1)) 0 (eqPoly ch.α) *
          nodePair P Fq Dom ch (assemble P 0 (-κ''.1)) 1 (eqPoly ch.α) -
        nodePair P Fq Dom ch (assemble P 0 (-κ.1)) 1 (eqPoly ch.α) *
          nodePair P Fq Dom ch (assemble P 0 (-κ''.1)) 0 (eqPoly ch.α) ≠ 0) :
    ∃ ν : viewKer P Fq Dom S ch,
      crossForm P Fq Dom ch (assemble P 0 (-ν.1)) θ ≠ 0 := by
  rcases crossForm_ne_zero_of_minor P Fq Dom ch (assemble P 0 (-κ.1))
    (assemble P 0 (-κ''.1)) θ hθ hminor with h | h
  · exact ⟨κ, h⟩
  · exact ⟨κ'', h⟩

/-- `nodePair` is additive in the perturbation table. -/
theorem nodePair_add_table (δ δ' : Cell P → Fp P) (j : Fin 2)
    (w : Cube P.k₀ → Fq) :
    nodePair P Fq Dom ch (δ + δ') j w =
      nodePair P Fq Dom ch δ j w + nodePair P Fq Dom ch δ' j w := by
  unfold nodePair
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hm : mle (fun c => liftT P Fq (δ + δ') (s, c))
        (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) =
      mle (fun c => liftT P Fq δ (s, c)) (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) +
        mle (fun c => liftT P Fq δ' (s, c)) (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) := by
    rw [← mle_pi_add]
    congr 1
    funext c
    simp [liftT, Pi.add_apply, map_add]
  rw [hm]; ring

/-- `nodePairTau` is additive in the perturbation table (linearity of the node
functionals in the perturbation — `lem:fullslice` Step 3 applies the represented
identity linearly to `V^δ`). -/
theorem nodePairTau_add_table (δ δ' : Cell P → Fp P) (j : Fin 2) (ℓ : Fin P.k₀) :
    nodePairTau P Fq Dom ch (δ + δ') j ℓ =
      nodePairTau P Fq Dom ch δ j ℓ + nodePairTau P Fq Dom ch δ' j ℓ := by
  unfold nodePairTau
  rw [nodePair_add_table]

/-- `nodePairRho` is additive in the perturbation table. -/
theorem nodePairRho_add_table (δ δ' : Cell P → Fp P) (j : Fin 2) (ℓ : Fin P.k₀) :
    nodePairRho P Fq Dom ch (δ + δ') j ℓ =
      nodePairRho P Fq Dom ch δ j ℓ + nodePairRho P Fq Dom ch δ' j ℓ := by
  unfold nodePairRho
  simp_rw [nodePair_add_table, mul_add]
  rw [Finset.sum_add_distrib]
  ring

/-- **The extension row in the `ρ_ℓ/τ` basis at any level** (`lem:fullslice`
Step 2 input): `η_j = ρ^{(j)}_ℓ + ∑_{i ≥ ℓ} λ^{(j)}_i τ^{(j)}_i`, i.e. the node
value `⟨η_j, V⟩` telescopes to `⟨ρ^{(j)}_ℓ, V⟩` plus the tail of slot pairings.
This is the target the η-matching at the top two levels is solved against. -/
theorem nodePair_eta_rho_tau (δ : Cell P → Fp P) (j : Fin 2) (ℓ : Fin P.k₀) :
    nodePair P Fq Dom ch δ j (eqPoly (ch.α)) =
      nodePairRho P Fq Dom ch δ j ℓ +
        ∑ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => ℓ ≤ i),
          lamData P Fq Dom ch (ch.z j) i * nodePairTau P Fq Dom ch δ j i := by
  rw [nodePair_eta]
  unfold nodePairRho nodePairTau
  have hfull : (Finset.univ.filter (fun i : Fin P.k₀ => (i : ℕ) < P.k₀)) = Finset.univ :=
    Finset.filter_true_of_mem (fun i _ => i.isLt)
  have hge : (Finset.univ.filter (fun i : Fin P.k₀ => ℓ ≤ i)) =
      (Finset.univ.filter (fun i : Fin P.k₀ => ¬ i < ℓ)) := by
    apply Finset.filter_congr; intro i _; simp [not_lt]
  rw [hfull, hge, add_assoc,
    Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin P.k₀ => i < ℓ)]

/-- **The per-block η-match** (`lem:fullslice` Step 2, scalar form): at the top
two levels `lo < hi` (`hi` the maximal level, `lo` its immediate predecessor),
the matched two-level node combination equals `Θ · ⟨η_j, V⟩`. This instantiates
`eta_match_combo` at the actual node-pairings, with `hρ` from `nodePairRho_succ`
and `hη` from `nodePair_eta_rho_tau` (whose tail collapses to a single term since
`hi` is maximal). -/
theorem nodePair_eta_match (δ : Cell P → Fp P) (j : Fin 2) (lo hi : Fin P.k₀)
    (hlohi : lo < hi) (hcons : ∀ i : Fin P.k₀, lo ≤ i → i < hi → i = lo)
    (htop : ∀ i : Fin P.k₀, hi ≤ i → i = hi) (Θ S_hi : Fq) :
    (Θ - S_hi) * nodePairRho P Fq Dom ch δ j lo
      + lamData P Fq Dom ch (ch.z j) lo * (Θ - S_hi) * nodePairTau P Fq Dom ch δ j lo
      + S_hi * nodePairRho P Fq Dom ch δ j hi
      + lamData P Fq Dom ch (ch.z j) hi * Θ * nodePairTau P Fq Dom ch δ j hi =
      Θ * nodePair P Fq Dom ch δ j (eqPoly ch.α) := by
  have hρ : nodePairRho P Fq Dom ch δ j hi =
      nodePairRho P Fq Dom ch δ j lo +
        lamData P Fq Dom ch (ch.z j) lo • nodePairTau P Fq Dom ch δ j lo := by
    rw [nodePairRho_succ P Fq Dom ch δ j lo hi hlohi hcons, smul_eq_mul]
  have hη : nodePair P Fq Dom ch δ j (eqPoly ch.α) =
      nodePairRho P Fq Dom ch δ j hi +
        lamData P Fq Dom ch (ch.z j) hi • nodePairTau P Fq Dom ch δ j hi := by
    rw [nodePair_eta_rho_tau P Fq Dom ch δ j hi]
    congr 1
    have hfilter : Finset.univ.filter (fun i : Fin P.k₀ => hi ≤ i) = {hi} := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · exact fun h => htop i h
      · rintro rfl; exact le_refl _
    rw [hfilter, Finset.sum_singleton, smul_eq_mul]
  have hcombo := eta_match_combo (Fq := Fq) (V := Fq)
    (nodePairRho P Fq Dom ch δ j lo) (nodePairRho P Fq Dom ch δ j hi)
    (nodePairTau P Fq Dom ch δ j lo) (nodePairTau P Fq Dom ch δ j hi)
    (nodePair P Fq Dom ch δ j (eqPoly ch.α))
    (lamData P Fq Dom ch (ch.z j) lo) (lamData P Fq Dom ch (ch.z j) hi) Θ S_hi hρ hη
  simpa [smul_eq_mul] using hcombo

/-- **The two-block η-match for the cross form** (`lem:fullslice` Step 2): the
cross form `F_θ` equals the sum over the two blocks of the matched two-level node
combinations (with per-block free parameters `S_hi0`, `S_hi1` and targets
`Θ_j = θ_j`). This rewrites `crossForm` into the form `channel_moment_SR`'s node
part realizes — the bridge between cond:cross2's `F_θ` and the moment system. -/
theorem crossForm_eta_match (δ : Cell P → Fp P) (θ : Fin 2 → Fq) (lo hi : Fin P.k₀)
    (hlohi : lo < hi) (hcons : ∀ i : Fin P.k₀, lo ≤ i → i < hi → i = lo)
    (htop : ∀ i : Fin P.k₀, hi ≤ i → i = hi) (S_hi0 S_hi1 : Fq) :
    crossForm P Fq Dom ch δ θ =
      ((θ 0 - S_hi0) * nodePairRho P Fq Dom ch δ 0 lo
        + lamData P Fq Dom ch (ch.z 0) lo * (θ 0 - S_hi0) * nodePairTau P Fq Dom ch δ 0 lo
        + S_hi0 * nodePairRho P Fq Dom ch δ 0 hi
        + lamData P Fq Dom ch (ch.z 0) hi * θ 0 * nodePairTau P Fq Dom ch δ 0 hi)
      + ((θ 1 - S_hi1) * nodePairRho P Fq Dom ch δ 1 lo
        + lamData P Fq Dom ch (ch.z 1) lo * (θ 1 - S_hi1) * nodePairTau P Fq Dom ch δ 1 lo
        + S_hi1 * nodePairRho P Fq Dom ch δ 1 hi
        + lamData P Fq Dom ch (ch.z 1) hi * θ 1 * nodePairTau P Fq Dom ch δ 1 hi) := by
  unfold crossForm
  rw [← nodePair_eta_match P Fq Dom ch δ 0 lo hi hlohi hcons htop (θ 0) S_hi0,
    ← nodePair_eta_match P Fq Dom ch δ 1 lo hi hlohi hcons htop (θ 1) S_hi1]

/-- **The cross form in the `ρ/τ` staircase basis** (`lem:fullslice` Step 2/3
interface): `F_θ(δ) = ∑_j θ_j (⟨ρ^{(j)}_ℓ, V⟩ + ∑_{i ≥ ℓ} λ^{(j)}_i ⟨τ^{(j)}_i, V⟩)`,
the form against which the matched moment combination is compared. -/
theorem crossForm_eq_rho_tau (δ : Cell P → Fp P) (θ : Fin 2 → Fq) (ℓ : Fin P.k₀) :
    crossForm P Fq Dom ch δ θ =
      θ 0 * (nodePairRho P Fq Dom ch δ 0 ℓ +
          ∑ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => ℓ ≤ i),
            lamData P Fq Dom ch (ch.z 0) i * nodePairTau P Fq Dom ch δ 0 i) +
      θ 1 * (nodePairRho P Fq Dom ch δ 1 ℓ +
          ∑ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => ℓ ≤ i),
            lamData P Fq Dom ch (ch.z 1) i * nodePairTau P Fq Dom ch δ 1 i) := by
  unfold crossForm
  rw [nodePair_eta_rho_tau P Fq Dom ch δ 0 ℓ, nodePair_eta_rho_tau P Fq Dom ch δ 1 ℓ]

/-- **The cross form is additive in the perturbation table** (`lem:fullslice`
Step 3 / cond:cross2 consequence): `F_θ` is `Fp`-linear in `δ`, so the
`δ_out`-arbitrariness of `lem:kersurj` transfers to the cross form. -/
theorem crossForm_add_table (δ δ' : Cell P → Fp P) (θ : Fin 2 → Fq) :
    crossForm P Fq Dom ch (δ + δ') θ =
      crossForm P Fq Dom ch δ θ + crossForm P Fq Dom ch δ' θ := by
  unfold crossForm
  rw [nodePair_add_table, nodePair_add_table]
  ring

/-- **`lem:fullslice` Step 4 (trace conclusion).** If the cross form factors as
`F(π,v) = γ²·E'(π)·G(v)` (Step 3), the multipliers `E'(π)` span `Fq` over `Fp`
(condition (i)/SPREAD), and `tr ∘ F = 0`, then `F ≡ 0`. Trace duality
(`eq_zero_of_trace_pairing_span`) forces `γ²·G(v) = 0` for every `v`, hence `F`
vanishes identically — the contradiction with `cond:cross2` (`F_θ ≠ 0`). -/
theorem fullslice_step4 [FiniteDimensional (Fp P) Fq] [Algebra.IsSeparable (Fp P) Fq]
    {ιπ ιv : Type*} (E' : ιπ → Fq) (G : ιv → Fq) (γ2 : Fq) (F : ιπ → ιv → Fq)
    (hfact : ∀ π v, F π v = γ2 * E' π * G v)
    (hspan : Submodule.span (Fp P) (Set.range E') = ⊤)
    (htr : ∀ π v, Algebra.trace (Fp P) Fq (F π v) = 0) :
    ∀ π v, F π v = 0 := by
  intro π v
  have hg : γ2 * G v = 0 := by
    refine eq_zero_of_trace_pairing_span E' hspan (γ2 * G v) (fun π' => ?_)
    have hE : E' π' * (γ2 * G v) = F π' v := by rw [hfact]; ring
    rw [hE]; exact htr π' v
  rw [hfact]
  calc γ2 * E' π * G v = E' π * (γ2 * G v) := by ring
    _ = 0 := by rw [hg, mul_zero]

/-- **`lem:fullslice` conclusion (the `prop:pinbound` consumer).** Given the
Step-3 factorization `F = γ²·E'·G`, condition (i)/SPREAD (`E'` spans `Fq` over
`Fp`), and `cond:cross2`'s nonvanishing (`F ≠ 0` somewhere), the `Fp`-form
`tr ∘ F` is nonzero somewhere: `tr ∘ F_θ ≠ 0` for every `θ ≠ 0`. This is the
contrapositive of `fullslice_step4` and is strictly stronger than the
`Fq`-level `F_θ ≠ 0` of `cond:cross2` (tex:604). -/
theorem fullslice_trace_ne_zero [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq]
    {ιπ ιv : Type*} (E' : ιπ → Fq) (G : ιv → Fq) (γ2 : Fq) (F : ιπ → ιv → Fq)
    (hfact : ∀ π v, F π v = γ2 * E' π * G v)
    (hspan : Submodule.span (Fp P) (Set.range E') = ⊤)
    (hne : ∃ π v, F π v ≠ 0) :
    ∃ π v, Algebra.trace (Fp P) Fq (F π v) ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨π, v, hpv⟩ := hne
  exact hpv (fullslice_step4 P Fq E' G γ2 F hfact hspan h π v)

/-- The cross channel is additive in the perturbation table (`crossTerm` pairs
`liftT T` linearly against the fixed input weight `ŵ`): the cross-moment of
`lem:fullslice` Step 3 is `Fp`-linear in the perturbation. -/
theorem crossTerm_add_table (T₁ T₂ : Cell P → Fp P) (ℓ : Fin P.k₀) (y : Fq) :
    crossTerm P Fq Dom S (T₁ + T₂) ch ℓ y =
      crossTerm P Fq Dom S T₁ ch ℓ y + crossTerm P Fq Dom S T₂ ch ℓ y := by
  unfold crossTerm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [liftT_add, partialEval_add]
  ring

/-- The cross channel is `Fp`-homogeneous in the perturbation table (companion to
`crossTerm_add_table`): together they make the cross-moment `Fp`-linear in the
perturbation, transporting `lem:kersurj`'s `δ_out`-arbitrariness to `F_θ`. -/
theorem crossTerm_smul_table (c : Fp P) (T : Cell P → Fp P) (ℓ : Fin P.k₀) (y : Fq) :
    crossTerm P Fq Dom S (c • T) ch ℓ y =
      algebraMap (Fp P) Fq c * crossTerm P Fq Dom S T ch ℓ y := by
  unfold crossTerm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c' _ => ?_
  have hl : liftT P Fq (c • T) = algebraMap (Fp P) Fq c • liftT P Fq T := by
    funext u
    simp [liftT, Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def]
  rw [hl, partialEval_smul]
  ring

/-- **The slot-`ℓ` factor of `preFac` splits off**: `preFac` factors as the
slot weight `êq(X, s_ℓ)` (i.e. `if s_ℓ then X else 1−X`) times the product over
the other coordinates. A building block for the `crossTerm` cell-coefficient
factorization (the `α`-prefix and the slot weight pull out). -/
theorem preFac_factor_at (ℓ : Fin P.k₀) (X : Fq) (s b : Cube P.k₀) :
    preFac P Fq Dom ch ℓ X s b =
      (if s ℓ then X else 1 - X) *
        ∏ i ∈ Finset.univ.erase ℓ,
          (if i < ℓ then (if s i then ch.α i else 1 - ch.α i)
           else if i = ℓ then (if s i then X else 1 - X)
           else (if s i = b i then (1 : Fq) else 0)) := by
  unfold preFac
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ ℓ)]
  congr 1
  simp

/-- **The cross-vector entry** (`cond:cross2`/`lem:fullslice` value-row layer):
`crossTerm` at the single-cell perturbation `(s, c)` is `∑_b preFac(ℓ,y,s,b)·ⓦ(b,c)` —
the coefficient `C_{(s,c)}` of the data cell `(s,c)` in the cross channel. (Safe,
definitional: this defines the cross vectors, independent of the witness
construction.) -/
theorem crossTerm_single_cell (s : Cube P.k₀) (c : Cube P.m) (ℓ : Fin P.k₀) (y : Fq) :
    crossTerm P Fq Dom S (Pi.single (s, c) 1) ch ℓ y =
      ∑ b ∈ Finset.univ.filter (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ, b i = false),
        preFac P Fq Dom ch ℓ y s b * partialEval P Fq Dom ch S.w ℓ y b c := by
  unfold crossTerm
  refine Finset.sum_congr rfl fun b _ => ?_
  have hpe : ∀ c' : Cube P.m,
      partialEval P Fq Dom ch (liftT P Fq (Pi.single (s, c) (1 : Fp P))) ℓ y b c' =
        if c' = c then preFac P Fq Dom ch ℓ y s b else 0 := by
    intro c'
    rw [partialEval_eq]
    by_cases hc' : c' = c
    · subst hc'
      rw [if_pos rfl, Finset.sum_eq_single s]
      · simp [liftT, Pi.single_eq_same]
      · intro s' _ hs's
        have h0 : liftT P Fq (Pi.single (s, c') (1 : Fp P)) (s', c') = 0 := by
          simp [liftT, Pi.single_apply, Prod.ext_iff, hs's]
        rw [h0, mul_zero]
      · intro h; exact absurd (Finset.mem_univ s) h
    · rw [if_neg hc']
      refine Finset.sum_eq_zero fun s' _ => ?_
      have h0 : liftT P Fq (Pi.single (s, c) (1 : Fp P)) (s', c') = 0 := by
        simp [liftT, Pi.single_apply, Prod.ext_iff, hc']
      rw [h0, mul_zero]
  rw [Finset.sum_eq_single c]
  · rw [hpe c, if_pos rfl]
  · intro c' _ hc'c; rw [hpe c', if_neg hc'c, zero_mul]
  · intro h; exact absurd (Finset.mem_univ c) h

/-- **The slot weight factors out of the cross-vector entry**: the `b`-independent
slot factor `êq(y, s_ℓ)` (= `if s_ℓ then y else 1−y`) pulls out of `C_{(s,c)}`,
leaving the `α`-prefix / suffix product paired against `ŵ`. A step toward the
`F_θ = γ²·E'(π)·G_θ` cell-coefficient factorization. -/
theorem crossTerm_single_cell_factor (s : Cube P.k₀) (c : Cube P.m) (ℓ : Fin P.k₀)
    (y : Fq) :
    crossTerm P Fq Dom S (Pi.single (s, c) 1) ch ℓ y =
      (if s ℓ then y else 1 - y) *
        ∑ b ∈ Finset.univ.filter (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ, b i = false),
          (∏ i ∈ Finset.univ.erase ℓ,
              (if i < ℓ then (if s i then ch.α i else 1 - ch.α i)
               else if i = ℓ then (if s i then y else 1 - y)
               else (if s i = b i then (1 : Fq) else 0))) *
            partialEval P Fq Dom ch S.w ℓ y b c := by
  rw [crossTerm_single_cell, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [preFac_factor_at]
  ring

/-- **The suffix-indicator sum collapses to the unique agreeing `b*`**: over the
filter `{b : b_{≤ℓ} = false}`, the suffix indicator `∏_{i>ℓ}(if s_i = b_i then 1
else 0)` is nonzero only at `b* i = if i ≤ ℓ then false else s_i`, so the weighted
sum equals `f b*`. The `b`-collapse at the heart of the `C_u` factorization. -/
theorem sum_filter_suffix_indicator (ℓ : Fin P.k₀) (s : Cube P.k₀) (f : Cube P.k₀ → Fq) :
    ∑ b ∈ Finset.univ.filter (fun b : Cube P.k₀ => ∀ i ∈ Finset.Iic ℓ, b i = false),
      (∏ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => ℓ < i),
        if s i = b i then (1 : Fq) else 0) * f b =
      f (fun i => if i ≤ ℓ then false else s i) := by
  classical
  set b₀ : Cube P.k₀ := fun i => if i ≤ ℓ then false else s i with hb₀
  rw [Finset.sum_eq_single b₀]
  · rw [show (∏ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => ℓ < i),
        if s i = b₀ i then (1 : Fq) else 0) = 1 from ?_, one_mul]
    refine Finset.prod_eq_one fun i hi => ?_
    have hℓi : ℓ < i := (Finset.mem_filter.mp hi).2
    rw [if_pos (show s i = b₀ i by rw [hb₀]; simp [not_le.mpr hℓi])]
  · intro b hb hbne
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hbne
    have hℓi : ℓ < i := by
      by_contra h
      push_neg at h
      have hbf : b i = false := (Finset.mem_filter.mp hb).2 i (Finset.mem_Iic.mpr h)
      apply hi
      rw [hb₀]; simp only [if_pos h]; exact hbf
    have hsb : ¬ s i = b i := by
      rw [hb₀] at hi; simp only [if_neg (not_le.mpr hℓi)] at hi
      exact fun h => hi h.symm
    rw [Finset.prod_eq_zero (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hℓi⟩) (if_neg hsb),
      zero_mul]
  · intro h
    exact absurd (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      fun i hi => by rw [hb₀]; simp [Finset.mem_Iic.mp hi]⟩) h

/-- `nodePair` is homogeneous in the perturbation table over `Fp`. -/
theorem nodePair_smul_table (a : Fp P) (δ : Cell P → Fp P) (j : Fin 2)
    (w : Cube P.k₀ → Fq) :
    nodePair P Fq Dom ch (a • δ) j w = a • nodePair P Fq Dom ch δ j w := by
  unfold nodePair
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hm : mle (fun c => liftT P Fq (a • δ) (s, c))
        (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) =
      a • mle (fun c => liftT P Fq δ (s, c)) (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) := by
    rw [← mle_smul_fp]
    congr 1
    funext c
    simp [liftT, Pi.smul_apply, smul_eq_mul, map_mul, Algebra.smul_def]
  rw [hm, Algebra.smul_def, Algebra.smul_def]; ring

/-- `F_θ` is additive in the perturbation. -/
theorem crossForm_add (δ δ' : Cell P → Fp P) (θ : Fin 2 → Fq) :
    crossForm P Fq Dom ch (δ + δ') θ =
      crossForm P Fq Dom ch δ θ + crossForm P Fq Dom ch δ' θ := by
  unfold crossForm
  rw [nodePair_add_table, nodePair_add_table]; ring

/-- `F_θ` is homogeneous in the perturbation over `Fp`. -/
theorem crossForm_smul (a : Fp P) (δ : Cell P → Fp P) (θ : Fin 2 → Fq) :
    crossForm P Fq Dom ch (a • δ) θ = a • crossForm P Fq Dom ch δ θ := by
  unfold crossForm
  rw [nodePair_smul_table, nodePair_smul_table, Algebra.smul_def,
    Algebra.smul_def, Algebra.smul_def]; ring

/-- **The (S,R) moment form** (`lem:fullslice` Step 2, the node-part of the
moment combination): the `μ`-weighted block-`j` slice term equals the `α`-prefix
times `⟨ρ, V⟩·S + ⟨τ, V⟩·R`, where `S = momS`, `R = momR` are the moment
coefficients. This is what the η-matching equates to `θ_j·⟨η_j, V_j⟩`. -/
theorem prefixFactor_evalT_moment_SR (δ : Cell P → Fp P) (j : Fin 2)
    (ℓ : Fin P.k₀) (w pts : Fin 3 → Fq) :
    (∑ t, w t * (prefixFactor P Fq Dom ch ℓ (pts t) (powSeq (ch.z j) P.k₀) *
        evalT P Fq δ (mixedPoint P Fq Dom ch ℓ (pts t) (powSeq (ch.z j) P.k₀))
          (powSeq (ch.z j ^ 2 ^ P.k₀) P.m))) =
      (∏ i ∈ Finset.univ.filter (fun i : Fin P.k₀ => i < ℓ),
          eqf Fq (ch.α i) (powSeq (ch.z j) P.k₀ i)) *
        (nodePairRho P Fq Dom ch δ j ℓ *
            momS Fq (powSeq (ch.z j) P.k₀ ℓ) (∑ t, w t) (∑ t, w t * pts t)
          + nodePairTau P Fq Dom ch δ j ℓ *
            momR Fq (powSeq (ch.z j) P.k₀ ℓ) (∑ t, w t) (∑ t, w t * pts t)
              (∑ t, w t * pts t ^ 2)) := by
  rw [prefixFactor_evalT_moment, evalT_mixed_rho_tau, evalT_mixed_rho_tau]
  unfold momS momR
  ring

/-- **The raw node-pairing map on masks**: `κ ↦ crossForm(assemble 0 (−κ))`,
the `θ`-weighted fold at the two commitment nodes as a function of the *full*
mask. ⚠ NOTE: this is NOT the paper's `F_θ`. The paper's `F_θ` (`cond:cross2`)
is the form on the *non-block* mask cells obtained from the identity
`∑_j θ_j η_j(V) = −F_θ(δ_out)`, which holds *only for view-vanishing masks*
(`channel_identity_of_viewKer`). Surjectivity of THIS map is the easy
node-pairing nondegeneracy (witnessed by block fibers, where `δ_out = 0`); it
does NOT give `lem:fullslice` Step 4, which lives on the view-vanishing /
non-block-cell domain. Kept as an auxiliary; the real Step 4 goes through the
`y`-family (`channel_moment_of_viewKer`). -/
def crossFormMap (θ : Fin 2 → Fq) : MaskAssign P →ₗ[Fp P] Fq where
  toFun κ := crossForm P Fq Dom ch (assemble P 0 (-κ)) θ
  map_add' κ₁ κ₂ := by
    show crossForm P Fq Dom ch (assemble P 0 (-(κ₁ + κ₂))) θ =
      crossForm P Fq Dom ch (assemble P 0 (-κ₁)) θ +
        crossForm P Fq Dom ch (assemble P 0 (-κ₂)) θ
    rw [neg_add, assemble_zero_add, crossForm_add]
  map_smul' a κ := by
    show crossForm P Fq Dom ch (assemble P 0 (-(a • κ))) θ =
      a • crossForm P Fq Dom ch (assemble P 0 (-κ)) θ
    rw [← smul_neg, assemble_zero_smul, crossForm_smul]

/-- **Node-pairing trace-nondegeneracy** (auxiliary, NOT `lem:fullslice` Step 4):
if the raw node-pairing map for `θ` is surjective, some mask gives a nonzero
trace pairing. ⚠ The witness is a block mask (`δ_out = 0`), so this is the trace
nondegeneracy of the *raw* node pairing over all masks, not the slice statement
`tr∘F_θ ≠ 0` on the non-block cells that `prop:pinbound` consumes. -/
theorem exists_trace_crossForm_ne_zero [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] (θ : Fin 2 → Fq)
    (hsurj : Function.Surjective (crossFormMap P Fq Dom ch θ)) :
    ∃ κ : MaskAssign P,
      Algebra.trace (Fp P) Fq (crossForm P Fq Dom ch (assemble P 0 (-κ)) θ) ≠ 0 :=
  exists_trace_ne_zero_of_surjective (crossFormMap P Fq Dom ch θ) hsurj

/-- Some class has nonzero `α`-Lagrange weight (partition of unity). -/
theorem exists_eqPoly_alpha_ne_zero : ∃ s : Cube P.k₀, eqPoly (ch.α) s ≠ 0 := by
  by_contra h
  push_neg at h
  exact eqPoly_vec_ne_zero Fq (ch.α) (funext fun s => h s)

/-- **`crossFormMap θ` is surjective for `θ ≠ 0`** (raw node-pairing spanning):
placing a single block fiber on a class with nonzero `α`-weight, hitting the
commitment node where `θ` is nonzero, realizes any target. Uses the node
genericity (`NodeHyp`) and the block solver (`exists_block_fiber`). ⚠ The
witness is block-supported, so `δ_out = 0`: this is surjectivity of the raw
node pairing, NOT the non-block-cell form `F_θ` of `cond:cross2`. -/
theorem crossFormMap_surjective [FiniteDimensional (Fp P) Fq]
    (hnode : NodeHyp P Fq Dom ch)
    (hbudget : Module.finrank (Fp P) Fq * 2 ≤ 2 ^ P.a)
    (θ : Fin 2 → Fq) (hθ : θ ≠ 0) :
    Function.Surjective (crossFormMap P Fq Dom ch θ) := by
  classical
  obtain ⟨s, hs⟩ := exists_eqPoly_alpha_ne_zero P Fq Dom ch
  obtain ⟨j₀, hj₀⟩ : ∃ j, θ j ≠ 0 := Function.ne_iff.mp hθ
  set ν : Fin 2 → Fq := fun j => ch.z j ^ 2 ^ P.k₀ with hν_def
  have hcomm : ∀ j : Fin 2, nodes P Fq Dom ch (Fin.castAdd P.s₁ j) = ν j :=
    fun j => Fin.append_left _ _ j
  have hνbase : ∀ j, ν j ∉ Set.range (algebraMap (Fp P) Fq) :=
    fun j => hcomm j ▸ hnode.not_in_base _
  have hνgen : ∀ j, (minpoly (Fp P) (ν j)).natDegree =
      Module.finrank (Fp P) Fq := fun j => hcomm j ▸ hnode.gen _
  have hνconj : ∀ j j', j ≠ j' →
      minpoly (Fp P) (ν j) ≠ minpoly (Fp P) (ν j') := fun j j' hjj' =>
    hcomm j ▸ hcomm j' ▸ hnode.conj _ _ (fun h => hjj' (Fin.castAdd_injective _ _ h))
  intro t
  set b : Fin 2 → Fq :=
    fun j => if j = j₀ then t / (θ j₀ * eqPoly (ch.α) s) else 0 with hb_def
  obtain ⟨v, hvblock, _, hvnode⟩ := exists_block_fiber P Fq
    (fun i : Fin 0 => (0 : Fp P)) ν (fun i => i.elim0) (fun i => i.elim0)
    hνbase hνgen hνconj (by simpa using hbudget) (fun i : Fin 0 => 0) b
  set κ : MaskAssign P := fun u => if u.1.1 = s then -(v u.1.2) else 0 with hκ_def
  have htab : ∀ (s' : Cube P.k₀) (c : Cube P.m),
      assemble P 0 (-κ) (s', c) = if s' = s then v c else 0 := by
    intro s' c
    unfold assemble
    by_cases hm : IsMask P (s', c)
    · rw [dif_pos hm]
      show -(if s' = s then -(v c) else 0) = if s' = s then v c else 0
      by_cases hss : s' = s
      · rw [if_pos hss, if_pos hss, neg_neg]
      · rw [if_neg hss, if_neg hss, neg_zero]
    · rw [dif_neg hm]
      by_cases hss : s' = s
      · rw [if_pos hss]
        have hcnb : ¬ IsBlockPos P c := fun hb => hm (Or.inr hb)
        have hvc : v c = 0 := by by_contra hh; exact hcnb (hvblock c hh)
        rw [hvc]; rfl
      · rw [if_neg hss]; rfl
  have hnp : ∀ j : Fin 2, nodePair P Fq Dom ch (assemble P 0 (-κ)) j
      (eqPoly (ch.α)) = eqPoly (ch.α) s * b j := by
    intro j
    unfold nodePair
    rw [Finset.sum_eq_single s]
    · congr 1
      have hfib : (fun c => liftT P Fq (assemble P 0 (-κ)) (s, c)) =
          fun c => algebraMap (Fp P) Fq (v c) := by
        funext c; unfold liftT; rw [htab s c, if_pos rfl]
      rw [hfib]; exact hvnode j
    · intro s' _ hs's
      have hz : (fun c => liftT P Fq (assemble P 0 (-κ)) (s', c)) =
          (fun _ => (0 : Fq)) := by
        funext c; unfold liftT; rw [htab s' c, if_neg hs's]; simp
      rw [hz]
      have : mle (fun _ : Cube P.m => (0 : Fq)) (powSeq (ν j) P.m) = 0 := by
        unfold mle; simp
      rw [this, mul_zero]
    · intro hns; exact absurd (Finset.mem_univ s) hns
  refine ⟨κ, ?_⟩
  show crossForm P Fq Dom ch (assemble P 0 (-κ)) θ = t
  unfold crossForm
  rw [hnp 0, hnp 1]
  have hbj0 : b j₀ = t / (θ j₀ * eqPoly (ch.α) s) := by rw [hb_def]; simp
  have hsum : (∑ j : Fin 2, θ j * b j) = θ j₀ * b j₀ :=
    Finset.sum_eq_single j₀ (fun j' _ hj' => by rw [hb_def]; simp [hj'])
      (fun h => absurd (Finset.mem_univ j₀) h)
  have key : θ 0 * (eqPoly (ch.α) s * b 0) + θ 1 * (eqPoly (ch.α) s * b 1) =
      eqPoly (ch.α) s * (∑ j : Fin 2, θ j * b j) := by
    rw [Fin.sum_univ_two]; ring
  rw [key, hsum, hbj0]
  field_simp

/-- **Raw node-pairing trace-nondegeneracy from `NodeHyp`** (auxiliary): under
node genericity and the mask budget, the trace of the raw node pairing is
nonzero for every `θ ≠ 0`. ⚠ This is NOT `lem:fullslice` Step 4 (`tr∘F_θ ≠ 0` on
the non-block cells); the witness is a block mask. The real Step 4 must use the
`y`-family representation (`channel_moment_of_viewKer` + `exists_trace_pairing_rep`
+ SPREAD); see the warning on `crossFormMap`. -/
theorem exists_trace_crossForm_ne_zero_of_nodeHyp [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] (hnode : NodeHyp P Fq Dom ch)
    (hbudget : Module.finrank (Fp P) Fq * 2 ≤ 2 ^ P.a) (θ : Fin 2 → Fq)
    (hθ : θ ≠ 0) :
    ∃ κ : MaskAssign P,
      Algebra.trace (Fp P) Fq
        (crossForm P Fq Dom ch (assemble P 0 (-κ)) θ) ≠ 0 :=
  exists_trace_crossForm_ne_zero P Fq Dom ch θ
    (crossFormMap_surjective P Fq Dom ch hnode hbudget θ hθ)

/-! ## The single-class block probe mask (`lem:confine`/`lem:noother`)

The confinement and no-other arguments both use the same probe: a block-supported
fiber `v` placed on the block of a single class `s`, zero elsewhere. When `v`'s
evaluations vanish at the queried points, the two commitment nodes, and the `f̂₁`
nodes, this probe is view-vanishing — so it lies in `viewKer`, and its fold is
the single class-weighted lift `êq(α, s) · v`. This is the reusable keystone the
slice argument repeatedly invokes. -/

/-- The cross-term of the zero table vanishes (block masks contribute none). -/
theorem crossTerm_zero (ℓ : Fin P.k₀) (y : Fq) :
    crossTerm P Fq Dom S (0 : Cell P → Fp P) ch ℓ y = 0 := by
  unfold crossTerm
  refine Finset.sum_eq_zero fun b _ => Finset.sum_eq_zero fun c _ => ?_
  have hpe : partialEval P Fq Dom ch (liftT P Fq (0 : Cell P → Fp P)) ℓ y b c = 0 := by
    rw [liftT_zero]; unfold partialEval; simp
  rw [hpe, zero_mul]

/-- The cross channel distributes over a finite sum of perturbation tables
(`Fp`-linearity in finitary form, from `crossTerm_add_table`/`crossTerm_zero`). -/
theorem crossTerm_sum {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Cell P → Fp P) (ℓ : Fin P.k₀) (y : Fq) :
    crossTerm P Fq Dom S (∑ i ∈ s, f i) ch ℓ y =
      ∑ i ∈ s, crossTerm P Fq Dom S (f i) ch ℓ y := by
  induction s using Finset.induction with
  | empty => simp [crossTerm_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, crossTerm_add_table, ih, Finset.sum_insert ha]

/-- **The value-row decomposition of the cross channel**: `crossTerm` is the
`Fp`-combination `∑_u algebraMap(T u)·C_u` of the cross vectors `C_u =
crossTerm(Pi.single u 1)` (i.e. the data cells pair against the cross channel
through the cross-vector entries). The structural form `cond:cross2`/`lem:fullslice`
use to read off the `C_v` system. -/
theorem crossTerm_eq_sum_cells (T : Cell P → Fp P) (ℓ : Fin P.k₀) (y : Fq) :
    crossTerm P Fq Dom S T ch ℓ y =
      ∑ u : Cell P, algebraMap (Fp P) Fq (T u) *
        crossTerm P Fq Dom S (Pi.single u 1) ch ℓ y := by
  have hT : T = ∑ u : Cell P, T u • Pi.single u (1 : Fp P) := by
    funext v
    simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul, Finset.sum_ite_eq, eq_comm]
  conv_lhs => rw [hT]
  rw [crossTerm_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [crossTerm_smul_table]

/-- **The single-class block probe mask**: place `−v` on the block of class `s`. -/
def blockClassMask (s : Cube P.k₀) (v : Cube P.m → Fp P) : MaskAssign P :=
  fun u => if u.1.1 = s then -(v u.1.2) else 0

/-- The assembled table of the probe: `v` on class `s`, zero elsewhere (using
that `v` is block-supported, so off-block cells carry no data either). -/
theorem assemble_blockClassMask {s : Cube P.k₀} {v : Cube P.m → Fp P}
    (hvblock : ∀ c, v c ≠ 0 → IsBlockPos P c) (s' : Cube P.k₀) (c : Cube P.m) :
    assemble P 0 (- blockClassMask P s v) (s', c) = if s' = s then v c else 0 := by
  unfold assemble
  by_cases hm : IsMask P (s', c)
  · rw [dif_pos hm]
    show -(if s' = s then -(v c) else 0) = if s' = s then v c else 0
    by_cases hss : s' = s
    · rw [if_pos hss, if_pos hss, neg_neg]
    · rw [if_neg hss, if_neg hss, neg_zero]
  · rw [dif_neg hm]
    by_cases hss : s' = s
    · rw [if_pos hss]
      have hcnb : ¬ IsBlockPos P c := fun hb => hm (Or.inr hb)
      have hvc : v c = 0 := by by_contra hh; exact hcnb (hvblock c hh)
      rw [hvc]; rfl
    · rw [if_neg hss]; rfl

/-- The per-class fiber extension of the probe: only class `s` carries `v`. -/
theorem blockClassMask_fiber_mle {s : Cube P.k₀} {v : Cube P.m → Fp P}
    (hvblock : ∀ c, v c ≠ 0 → IsBlockPos P c) (s' : Cube P.k₀)
    (pt : Fin P.m → Fq) :
    mle (fun c => liftT P Fq (assemble P 0 (- blockClassMask P s v)) (s', c)) pt =
      if s' = s then mle (fun c => algebraMap (Fp P) Fq (v c)) pt else 0 := by
  by_cases hss : s' = s
  · rw [if_pos hss]
    congr 1; funext c
    unfold liftT
    rw [assemble_blockClassMask P hvblock s' c, if_pos hss]
  · rw [if_neg hss]
    have hz0 : (fun c => liftT P Fq (assemble P 0 (- blockClassMask P s v)) (s', c)) =
        (fun _ => (0 : Fq)) := by
      funext c; unfold liftT
      rw [assemble_blockClassMask P hvblock s' c, if_neg hss]; simp
    rw [hz0]; unfold mle; simp

/-- The fold of the probe is the single class-weighted lift `êq(α, s) · v`. -/
theorem foldedF₁_blockClassMask {s : Cube P.k₀} {v : Cube P.m → Fp P}
    (hvblock : ∀ c, v c ≠ 0 → IsBlockPos P c) (c : Cube P.m) :
    foldedF₁ P Fq Dom (assemble P 0 (- blockClassMask P s v)) ch c =
      eqPoly ch.α s * algebraMap (Fp P) Fq (v c) := by
  unfold foldedF₁
  rw [Finset.sum_eq_single s]
  · unfold liftT; rw [assemble_blockClassMask P hvblock s c, if_pos rfl]
  · intro s' _ hs's
    unfold liftT; rw [assemble_blockClassMask P hvblock s' c, if_neg hs's]; simp
  · intro h; exact absurd (Finset.mem_univ s) h

/-- **The probe mask is view-vanishing** (`lem:confine`/`lem:noother`): a
block-supported fiber whose evaluations vanish at the queried points, the two
commitment nodes, and the `f̂₁` nodes gives a view-vanishing perturbation. -/
theorem blockClassMask_viewVanishes (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S)
    {s : Cube P.k₀} {v : Cube P.m → Fp P}
    (hvblock : ∀ c, v c ≠ 0 → IsBlockPos P c)
    (hq : ∀ t : Fin P.t₀, mle (fun c => algebraMap (Fp P) Fq (v c))
        (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0)
    (hn : ∀ j : Fin 2, mle (fun c => algebraMap (Fp P) Fq (v c))
        (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) = 0)
    (hz : ∀ j : Fin P.s₁, mle (fun c => algebraMap (Fp P) Fq (v c))
        (powSeq (ch.zf j) P.m) = 0) :
    ViewVanishes P Fq Dom S ch (assemble P 0 (- blockClassMask P s v)) := by
  -- every evaluation at a commitment node vanishes (any class weights)
  have hclass_node : ∀ (ys : Fin P.k₀ → Fq) (j : Fin 2),
      evalT P Fq (assemble P 0 (- blockClassMask P s v)) ys
        (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) = 0 := by
    intro ys j
    rw [evalT_eq_sum_classes]
    refine Finset.sum_eq_zero fun s' _ => ?_
    rw [blockClassMask_fiber_mle P Fq hvblock s']
    by_cases hss : s' = s
    · rw [if_pos hss, hn j, mul_zero]
    · rw [if_neg hss, mul_zero]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- out-of-domain answers
    intro j
    show evalT P Fq (assemble P 0 (- blockClassMask P s v)) (powSeq (ch.z j) P.k₀)
      (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) = 0
    exact hclass_node (powSeq (ch.z j) P.k₀) j
  · -- messages at X = 1
    intro ℓ
    rw [hPoly_channel P Fq Dom S (assemble P 0 (- blockClassMask P s v)) ch ℓ 1,
      hclass_node (mixedPoint P Fq Dom ch ℓ 1 (powSeq (ch.z 0) P.k₀)) 0,
      hclass_node (mixedPoint P Fq Dom ch ℓ 1 (powSeq (ch.z 1) P.k₀)) 1,
      crossTerm_eq_of_eq_nonblock P Fq Dom S ch hmf
        (assemble P 0 (- blockClassMask P s v)) (0 : Cell P → Fp P)
        (fun s' c hc => by
          rw [assemble_blockClassMask P hvblock s' c]
          have hvc : v c = 0 := by by_contra hh; exact hc (hvblock c hh)
          simp [hvc]) ℓ 1,
      crossTerm_zero P Fq Dom S ch ℓ 1]
    ring
  · -- messages at X = 2
    intro ℓ
    rw [hPoly_channel P Fq Dom S (assemble P 0 (- blockClassMask P s v)) ch ℓ 2,
      hclass_node (mixedPoint P Fq Dom ch ℓ 2 (powSeq (ch.z 0) P.k₀)) 0,
      hclass_node (mixedPoint P Fq Dom ch ℓ 2 (powSeq (ch.z 1) P.k₀)) 1,
      crossTerm_eq_of_eq_nonblock P Fq Dom S ch hmf
        (assemble P 0 (- blockClassMask P s v)) (0 : Cell P → Fp P)
        (fun s' c hc => by
          rw [assemble_blockClassMask P hvblock s' c]
          have hvc : v c = 0 := by by_contra hh; exact hc (hvblock c hh)
          simp [hvc]) ℓ 2,
      crossTerm_zero P Fq Dom S ch ℓ 2]
    ring
  · -- per-class query answers
    intro t s'
    show mle (fun c => liftT P Fq (assemble P 0 (- blockClassMask P s v)) (s', c))
      (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0
    rw [blockClassMask_fiber_mle P Fq hvblock s']
    by_cases hss : s' = s
    · rw [if_pos hss]; exact hq t
    · rw [if_neg hss]
  · -- f̂₁ out-of-domain answers
    intro j
    rw [mle_fold_eq_sum_classes P Fq Dom (assemble P 0 (- blockClassMask P s v)) ch]
    refine Finset.sum_eq_zero fun s' _ => ?_
    rw [blockClassMask_fiber_mle P Fq hvblock s']
    by_cases hss : s' = s
    · rw [if_pos hss, hz j, mul_zero]
    · rw [if_neg hss, mul_zero]

/-- **The probe fold lies in `range pinFold`** (`lem:confine`): a block-supported
fiber with vanishing evals folds to the single class-weighted lift, which is a
genuine view-vanishing mask fold. -/
theorem blockClassMask_fold_mem_range (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S)
    {s : Cube P.k₀} {v : Cube P.m → Fp P}
    (hvblock : ∀ c, v c ≠ 0 → IsBlockPos P c)
    (hq : ∀ t : Fin P.t₀, mle (fun c => algebraMap (Fp P) Fq (v c))
        (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0)
    (hn : ∀ j : Fin 2, mle (fun c => algebraMap (Fp P) Fq (v c))
        (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) = 0)
    (hz : ∀ j : Fin P.s₁, mle (fun c => algebraMap (Fp P) Fq (v c))
        (powSeq (ch.zf j) P.m) = 0) :
    (fun c => eqPoly ch.α s * algebraMap (Fp P) Fq (v c)) ∈
      LinearMap.range (pinFold P Fq Dom S ch) := by
  refine ⟨⟨blockClassMask P s v,
    (mem_viewKer P Fq Dom S ch _).mpr
      (blockClassMask_viewVanishes P Fq Dom S ch h2 hmf hvblock hq hn hz)⟩, ?_⟩
  funext c
  show foldedF₁ P Fq Dom (assemble P 0 (- blockClassMask P s v)) ch c = _
  exact foldedF₁_blockClassMask P Fq Dom ch hvblock c

/-- **Confinement pairing** (`lem:confine`, first half): every functional that
annihilates `range pinFold` vanishes on the single class-weighted lift of a
block-supported fiber whose evaluations all vanish. The trace/`SPREAD` wrap-up
turns this into `φ|_blk ∈ span{queried duals, node duals}`. -/
theorem confine_fold_apply_zero (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S)
    {s : Cube P.k₀} {v : Cube P.m → Fp P}
    (hvblock : ∀ c, v c ≠ 0 → IsBlockPos P c)
    (hq : ∀ t : Fin P.t₀, mle (fun c => algebraMap (Fp P) Fq (v c))
        (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0)
    (hn : ∀ j : Fin 2, mle (fun c => algebraMap (Fp P) Fq (v c))
        (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) = 0)
    (hz : ∀ j : Fin P.s₁, mle (fun c => algebraMap (Fp P) Fq (v c))
        (powSeq (ch.zf j) P.m) = 0)
    (φ : Module.Dual (Fp P) (Cube P.m → Fq))
    (hφ : ∀ κ : viewKer P Fq Dom S ch, φ (pinFold P Fq Dom S ch κ) = 0) :
    φ (fun c => eqPoly ch.α s * algebraMap (Fp P) Fq (v c)) = 0 := by
  obtain ⟨κ, hκ⟩ :=
    blockClassMask_fold_mem_range P Fq Dom S ch h2 hmf hvblock hq hn hz
  rw [← hκ]; exact hφ κ

/-- **Confinement, full** (`lem:confine`): a functional `φ` annihilating
`range pinFold` admits a trace-dual vector `w` (`lem:traceorth`) such that its
trace pairing against every block-supported probe fiber `v` with vanishing
evaluations is zero — i.e. `w` (the block representative of `φ`) lies in the
annihilator of the common kernel `K`, hence in the span of the queried-point and
node duals. Combines the probe view-invisibility, the trace-dual representation,
and `SPREAD` (the `êq(α, ·)` weights spanning `Fq` over `Fp`). -/
theorem confine_pairing_zero [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S)
    (hspread : Submodule.span (Fp P) (Set.range (eqPoly ch.α)) = ⊤)
    (φ : Module.Dual (Fp P) (Cube P.m → Fq))
    (hφ : ∀ κ : viewKer P Fq Dom S ch, φ (pinFold P Fq Dom S ch κ) = 0) :
    ∃ w : Cube P.m → Fq,
      (∀ g, φ g = Algebra.trace (Fp P) Fq (∑ c, w c * g c)) ∧
      ∀ (v : Cube P.m → Fp P), (∀ c, v c ≠ 0 → IsBlockPos P c) →
        (∀ t : Fin P.t₀, mle (fun c => algebraMap (Fp P) Fq (v c))
          (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0) →
        (∀ j : Fin 2, mle (fun c => algebraMap (Fp P) Fq (v c))
          (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) = 0) →
        (∀ j : Fin P.s₁, mle (fun c => algebraMap (Fp P) Fq (v c))
          (powSeq (ch.zf j) P.m) = 0) →
        (∑ c, w c * algebraMap (Fp P) Fq (v c)) = 0 := by
  obtain ⟨w, hw⟩ := exists_trace_pairing_rep (Fp := Fp P) (ι := Cube P.m) φ
  refine ⟨w, hw, fun v hvblock hq hn hz => ?_⟩
  refine eq_zero_of_trace_pairing_span (Fp := Fp P) (eqPoly ch.α) hspread _ (fun s => ?_)
  have hap := confine_fold_apply_zero P Fq Dom S ch h2 hmf hvblock hq hn hz φ hφ (s := s)
  rw [hw] at hap
  rw [Finset.mul_sum]
  refine Eq.trans ?_ hap
  congr 1
  exact Finset.sum_congr rfl fun c _ => by ring

/-- `mle` pulls out a constant `Fq` factor. -/
theorem mle_const_mul {j : ℕ} (k : Fq) (g : Cube j → Fq) (x : Fin j → Fq) :
    mle (fun c => k * g c) x = k * mle g x := by
  unfold mle; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- **The confinement kernel `K`** (`lem:confine`): block-supported `Fp`-fibers
whose evaluations vanish at the queried points, the two commitment nodes, and
the `f̂₁` nodes. The probe placing such a fiber on any class is view-vanishing
(`blockClassMask_viewVanishes`), so `confine_pairing_zero` says any
`φ ∈ ann(range pinFold)` trace-pairs to zero against all of `K`. -/
def confineKer : Submodule (Fp P) (Cube P.m → Fp P) where
  carrier := {v |
    (∀ c, v c ≠ 0 → IsBlockPos P c) ∧
    (∀ t : Fin P.t₀, mle (fun c => algebraMap (Fp P) Fq (v c))
      (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0) ∧
    (∀ j : Fin 2, mle (fun c => algebraMap (Fp P) Fq (v c))
      (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) = 0) ∧
    (∀ j : Fin P.s₁, mle (fun c => algebraMap (Fp P) Fq (v c))
      (powSeq (ch.zf j) P.m) = 0)}
  zero_mem' := by
    refine ⟨fun c hc => absurd rfl hc, ?_, ?_, ?_⟩ <;> intro <;> simp [mle]
  add_mem' := by
    rintro v v' ⟨hb, hq, hn, hz⟩ ⟨hb', hq', hn', hz'⟩
    have hadd : (fun c => algebraMap (Fp P) Fq ((v + v') c)) =
        (fun c => algebraMap (Fp P) Fq (v c) + algebraMap (Fp P) Fq (v' c)) := by
      funext c; rw [Pi.add_apply, map_add]
    refine ⟨?_, fun t => ?_, fun j => ?_, fun j => ?_⟩
    · intro c hc
      rw [Pi.add_apply] at hc
      by_cases h : v c = 0
      · rw [h, zero_add] at hc; exact hb' c hc
      · exact hb c h
    · rw [hadd, mle_add, hq t, hq' t, add_zero]
    · rw [hadd, mle_add, hn j, hn' j, add_zero]
    · rw [hadd, mle_add, hz j, hz' j, add_zero]
  smul_mem' := by
    rintro r v ⟨hb, hq, hn, hz⟩
    have hsmul : (fun c => algebraMap (Fp P) Fq ((r • v) c)) =
        (fun c => algebraMap (Fp P) Fq r * algebraMap (Fp P) Fq (v c)) := by
      funext c; rw [Pi.smul_apply, smul_eq_mul, map_mul]
    refine ⟨?_, fun t => ?_, fun j => ?_, fun j => ?_⟩
    · intro c hc
      refine hb c (fun h => hc ?_)
      rw [Pi.smul_apply, smul_eq_mul, h, mul_zero]
    · rw [hsmul, mle_const_mul, hq t, mul_zero]
    · rw [hsmul, mle_const_mul, hn j, mul_zero]
    · rw [hsmul, mle_const_mul, hz j, mul_zero]

/-- Membership in `confineKer` unfolds to the four vanishing conditions. -/
theorem mem_confineKer {v : Cube P.m → Fp P} :
    v ∈ confineKer P Fq Dom ch ↔
      (∀ c, v c ≠ 0 → IsBlockPos P c) ∧
      (∀ t : Fin P.t₀, mle (fun c => algebraMap (Fp P) Fq (v c))
        (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0) ∧
      (∀ j : Fin 2, mle (fun c => algebraMap (Fp P) Fq (v c))
        (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) = 0) ∧
      (∀ j : Fin P.s₁, mle (fun c => algebraMap (Fp P) Fq (v c))
        (powSeq (ch.zf j) P.m) = 0) := Iff.rfl

/-- **Confinement, packaged** (`lem:confine`): the trace-dual `w` of any
`φ ∈ ann(range pinFold)` trace-pairs to zero against every element of the
confinement kernel `K`. -/
theorem confine_trace_pairing_confineKer [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S)
    (hspread : Submodule.span (Fp P) (Set.range (eqPoly ch.α)) = ⊤)
    (φ : Module.Dual (Fp P) (Cube P.m → Fq))
    (hφ : ∀ κ : viewKer P Fq Dom S ch, φ (pinFold P Fq Dom S ch κ) = 0) :
    ∃ w : Cube P.m → Fq,
      (∀ g, φ g = Algebra.trace (Fp P) Fq (∑ c, w c * g c)) ∧
      ∀ v ∈ confineKer P Fq Dom ch,
        (∑ c, w c * algebraMap (Fp P) Fq (v c)) = 0 := by
  obtain ⟨w, hw, hpair⟩ :=
    confine_pairing_zero P Fq Dom S ch h2 hmf hspread φ hφ
  exact ⟨w, hw, fun v hv => hpair v hv.1 hv.2.1 hv.2.2.1 hv.2.2.2⟩

/-- **Slice functional vanishing** (`lem:confine`, slice form): each trace twist
`β` of the trace-dual `w` gives an `Fp`-functional `v ↦ ∑_c v_c · tr(β · w_c)` on
`Cube m → Fp` that vanishes on the confinement kernel. This is the family of
`Fp`-forms that `mem_span_of_forall_ker` confines to the protocol span. -/
theorem confine_sliceVec_vanishes [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S)
    (hspread : Submodule.span (Fp P) (Set.range (eqPoly ch.α)) = ⊤)
    (φ : Module.Dual (Fp P) (Cube P.m → Fq))
    (hφ : ∀ κ : viewKer P Fq Dom S ch, φ (pinFold P Fq Dom S ch κ) = 0) :
    ∃ w : Cube P.m → Fq,
      (∀ g, φ g = Algebra.trace (Fp P) Fq (∑ c, w c * g c)) ∧
      ∀ (β : Fq), ∀ v ∈ confineKer P Fq Dom ch,
        (∑ c, v c * Algebra.trace (Fp P) Fq (β * w c)) = 0 := by
  obtain ⟨w, hw, hpair⟩ :=
    confine_trace_pairing_confineKer P Fq Dom S ch h2 hmf hspread φ hφ
  refine ⟨w, hw, fun β v hv => ?_⟩
  rw [← trace_smul_pairing, hpair v hv, mul_zero, map_zero]

/-- **`confineKer` in `Fp`-functional form** (slice characterization): the
membership conditions become genuine `Fp`-valued linear conditions — the queried
fiber values (`Fp`-rational, via `mle_algebraMap`) and the trace slices of the
node values (via `eq_zero_iff_trace_basis`). This is the form whose common
kernel `mem_span_of_forall_ker` confines `φ` against. -/
theorem mem_confineKer_iff_slices [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] {ιβ : Type*}
    (b : Module.Basis ιβ (Fp P) Fq) {v : Cube P.m → Fp P} :
    v ∈ confineKer P Fq Dom ch ↔
      (∀ c, v c ≠ 0 → IsBlockPos P c) ∧
      (∀ t : Fin P.t₀, mle v (powSeq (ch.qs t : Fp P) P.m) = 0) ∧
      (∀ (j : Fin 2) (i : ιβ), Algebra.trace (Fp P) Fq (b i *
        mle (fun c => algebraMap (Fp P) Fq (v c))
          (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)) = 0) ∧
      (∀ (j : Fin P.s₁) (i : ιβ), Algebra.trace (Fp P) Fq (b i *
        mle (fun c => algebraMap (Fp P) Fq (v c)) (powSeq (ch.zf j) P.m)) = 0) := by
  rw [mem_confineKer]
  constructor
  · rintro ⟨hblk, hq, hn, hz⟩
    refine ⟨hblk, fun t => ?_, fun j i => ?_, fun j i => ?_⟩
    · have hqt := hq t
      rw [mle_algebraMap] at hqt
      exact (map_eq_zero_iff _ (algebraMap (Fp P) Fq).injective).mp hqt
    · rw [hn j, mul_zero, map_zero]
    · rw [hz j, mul_zero, map_zero]
  · rintro ⟨hblk, hq, hn, hz⟩
    refine ⟨hblk, fun t => ?_, fun j => ?_, fun j => ?_⟩
    · rw [mle_algebraMap, hq t, map_zero]
    · exact (eq_zero_iff_trace_basis b _).mpr (hn j)
    · exact (eq_zero_iff_trace_basis b _).mpr (hz j)

/-- **The confinement generator functionals** on `Cube m → Fp`: the non-block
coordinate projections (forcing block-support), the queried-point fiber
evaluations, and the trace slices of the commitment-node and `f̂₁`-node
evaluations. Their common kernel is exactly `confineKer`. -/
def confineGen {ιβ : Type*} [Fintype ιβ] (b : Module.Basis ιβ (Fp P) Fq) :
    (Cube P.m) ⊕ (Fin P.t₀) ⊕ (Fin 2 × ιβ) ⊕ (Fin P.s₁ × ιβ) →
      Module.Dual (Fp P) (Cube P.m → Fp P)
  | Sum.inl c => if IsBlockPos P c then 0 else LinearMap.proj c
  | Sum.inr (Sum.inl t) => dotFunc (fun c => eqPoly (powSeq (ch.qs t : Fp P) P.m) c)
  | Sum.inr (Sum.inr (Sum.inl (j, i))) =>
      dotFunc (fun c => Algebra.trace (Fp P) Fq
        (b i * eqPoly (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) c))
  | Sum.inr (Sum.inr (Sum.inr (k, i))) =>
      dotFunc (fun c => Algebra.trace (Fp P) Fq
        (b i * eqPoly (powSeq (ch.zf k) P.m) c))

/-- **Confinement span membership** (`lem:confine`, slice form, full): for each
trace twist `β`, the slice functional of the trace-dual `w` lies in the span of
the confinement generators. This is `mem_span_of_forall_ker` applied to the
generator family, whose common kernel is `confineKer` (where the slice vanishes
by `confine_sliceVec_vanishes`). -/
theorem confine_slice_in_genSpan [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S)
    (hspread : Submodule.span (Fp P) (Set.range (eqPoly ch.α)) = ⊤)
    {ιβ : Type*} [Fintype ιβ] (b : Module.Basis ιβ (Fp P) Fq)
    (φ : Module.Dual (Fp P) (Cube P.m → Fq))
    (hφ : ∀ κ : viewKer P Fq Dom S ch, φ (pinFold P Fq Dom S ch κ) = 0) :
    ∃ w : Cube P.m → Fq,
      (∀ g, φ g = Algebra.trace (Fp P) Fq (∑ c, w c * g c)) ∧
      ∀ β : Fq, dotFunc (fun c => Algebra.trace (Fp P) Fq (β * w c)) ∈
        Submodule.span (Fp P) (Set.range (confineGen P Fq Dom ch b)) := by
  obtain ⟨w, hw, hslice⟩ :=
    confine_sliceVec_vanishes P Fq Dom S ch h2 hmf hspread φ hφ
  refine ⟨w, hw, fun β => ?_⟩
  apply mem_span_of_forall_ker (confineGen P Fq Dom ch b)
  intro v hv
  have hvker : v ∈ confineKer P Fq Dom ch := by
    rw [mem_confineKer_iff_slices P Fq Dom ch b]
    refine ⟨fun c hc => ?_, fun t => ?_, fun j i => ?_, fun k i => ?_⟩
    · by_contra hblk
      have hgc := hv (Sum.inl c)
      simp only [confineGen, if_neg hblk, LinearMap.proj_apply] at hgc
      exact hc hgc
    · have hgt := hv (Sum.inr (Sum.inl t))
      simp only [confineGen, dotFunc_apply] at hgt
      rw [mle]; exact hgt
    · have hgji := hv (Sum.inr (Sum.inr (Sum.inl (j, i))))
      simp only [confineGen, dotFunc_apply] at hgji
      rw [show mle (fun c => algebraMap (Fp P) Fq (v c))
          (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) =
          ∑ c, eqPoly (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) c * algebraMap (Fp P) Fq (v c)
          from rfl, trace_smul_pairing]
      rw [Finset.sum_congr rfl fun c _ => mul_comm (v c) _]
      exact hgji
    · have hgki := hv (Sum.inr (Sum.inr (Sum.inr (k, i))))
      simp only [confineGen, dotFunc_apply] at hgki
      rw [show mle (fun c => algebraMap (Fp P) Fq (v c)) (powSeq (ch.zf k) P.m) =
          ∑ c, eqPoly (powSeq (ch.zf k) P.m) c * algebraMap (Fp P) Fq (v c)
          from rfl, trace_smul_pairing]
      rw [Finset.sum_congr rfl fun c _ => mul_comm (v c) _]
      exact hgki
  rw [dotFunc_apply, Finset.sum_congr rfl fun c _ => mul_comm _ (v c)]
  exact hslice β v hvker

/-- **Confinement coefficients** (`lem:confine`, explicit form): for each trace
twist `β`, the slice values `tr(β · w_c)` at block positions are an explicit
`Fp`-combination of the queried-fiber and node-slice values. Extracts the span
coefficients of `confine_slice_in_genSpan` and evaluates at block indicators
(where the non-block coordinate generators vanish). -/
theorem confine_slice_coeffs [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S)
    (hspread : Submodule.span (Fp P) (Set.range (eqPoly ch.α)) = ⊤)
    {ιβ : Type*} [Fintype ιβ] [DecidableEq ιβ] (b : Module.Basis ιβ (Fp P) Fq)
    (φ : Module.Dual (Fp P) (Cube P.m → Fq))
    (hφ : ∀ κ : viewKer P Fq Dom S ch, φ (pinFold P Fq Dom S ch κ) = 0) :
    ∃ w : Cube P.m → Fq,
      (∀ g, φ g = Algebra.trace (Fp P) Fq (∑ c, w c * g c)) ∧
      ∀ β : Fq, ∃ (cq : Fin P.t₀ → Fp P) (cn : Fin 2 → ιβ → Fp P)
          (cz : Fin P.s₁ → ιβ → Fp P),
        ∀ c0, IsBlockPos P c0 →
          Algebra.trace (Fp P) Fq (β * w c0) =
            (∑ t, cq t * eqPoly (powSeq (ch.qs t : Fp P) P.m) c0)
            + (∑ j, ∑ i, cn j i * Algebra.trace (Fp P) Fq
                (b i * eqPoly (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) c0))
            + (∑ k, ∑ i, cz k i * Algebra.trace (Fp P) Fq
                (b i * eqPoly (powSeq (ch.zf k) P.m) c0)) := by
  obtain ⟨w, hw, hspan⟩ :=
    confine_slice_in_genSpan P Fq Dom S ch h2 hmf hspread b φ hφ
  refine ⟨w, hw, fun β => ?_⟩
  obtain ⟨c, hc⟩ :=
    (Submodule.mem_span_range_iff_exists_fun (Fp P)).mp (hspan β)
  refine ⟨fun t => c (Sum.inr (Sum.inl t)),
    fun j i => c (Sum.inr (Sum.inr (Sum.inl (j, i)))),
    fun k i => c (Sum.inr (Sum.inr (Sum.inr (k, i)))), fun c0 hc0 => ?_⟩
  have happ := congrFun (congrArg DFunLike.coe hc) (Pi.single c0 1)
  rw [dotFunc_single] at happ
  rw [LinearMap.sum_apply] at happ
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type] at happ
  -- the non-block coordinate part vanishes at the block indicator c0
  have hinl : (∑ x : Cube P.m, (c (Sum.inl x) • confineGen P Fq Dom ch b (Sum.inl x))
      (Pi.single c0 1)) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [LinearMap.smul_apply]
    show c (Sum.inl x) • (if IsBlockPos P x then (0 : Module.Dual (Fp P) (Cube P.m → Fp P))
      else LinearMap.proj x) (Pi.single c0 1) = 0
    by_cases hx : IsBlockPos P x
    · rw [if_pos hx]; simp
    · have hxne : x ≠ c0 := fun heq => hx (by rw [heq]; exact hc0)
      rw [if_neg hx, LinearMap.proj_apply, Pi.single_eq_of_ne hxne, smul_zero]
  -- the queried / node / zf indicator evaluations
  have hq' : (∑ t : Fin P.t₀, (c (Sum.inr (Sum.inl t)) •
        confineGen P Fq Dom ch b (Sum.inr (Sum.inl t))) (Pi.single c0 1)) =
      ∑ t, c (Sum.inr (Sum.inl t)) * eqPoly (powSeq (ch.qs t : Fp P) P.m) c0 := by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [LinearMap.smul_apply]
    show c (Sum.inr (Sum.inl t)) • (dotFunc
      (fun c' => eqPoly (powSeq (ch.qs t : Fp P) P.m) c')) (Pi.single c0 1) = _
    rw [dotFunc_single, smul_eq_mul]
  have hn' : (∑ x : Fin 2 × ιβ, (c (Sum.inr (Sum.inr (Sum.inl x))) •
        confineGen P Fq Dom ch b (Sum.inr (Sum.inr (Sum.inl x)))) (Pi.single c0 1)) =
      ∑ j, ∑ i, c (Sum.inr (Sum.inr (Sum.inl (j, i)))) * Algebra.trace (Fp P) Fq
        (b i * eqPoly (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) c0) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply]
    show c (Sum.inr (Sum.inr (Sum.inl (j, i)))) • (dotFunc
      (fun c' => Algebra.trace (Fp P) Fq
        (b i * eqPoly (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) c'))) (Pi.single c0 1) = _
    rw [dotFunc_single, smul_eq_mul]
  have hz' : (∑ x : Fin P.s₁ × ιβ, (c (Sum.inr (Sum.inr (Sum.inr x))) •
        confineGen P Fq Dom ch b (Sum.inr (Sum.inr (Sum.inr x)))) (Pi.single c0 1)) =
      ∑ k, ∑ i, c (Sum.inr (Sum.inr (Sum.inr (k, i)))) * Algebra.trace (Fp P) Fq
        (b i * eqPoly (powSeq (ch.zf k) P.m) c0) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply]
    show c (Sum.inr (Sum.inr (Sum.inr (k, i)))) • (dotFunc
      (fun c' => Algebra.trace (Fp P) Fq
        (b i * eqPoly (powSeq (ch.zf k) P.m) c'))) (Pi.single c0 1) = _
    rw [dotFunc_single, smul_eq_mul]
  rw [hinl, hq', hn', hz', zero_add] at happ
  rw [← happ]; ring

/-! ## The multi-class node probe (`lem:nodechannel`)

The node-channel argument places a *per-class* block fiber `vf s` on each class
`s` simultaneously, realizing prescribed node values. Its fold is the
`λ`-combination `∑_s λ_s · (lift vf_s)`, and its view vanishes exactly when the
node values lie in the kernel of the node matrix. -/

/-- The multi-class block probe: place `−vf s` on the block of each class `s`. -/
def multiBlockMask (vf : Cube P.k₀ → Cube P.m → Fp P) : MaskAssign P :=
  fun u => -(vf u.1.1 u.1.2)

/-- The assembled table of the multi-class probe is `vf s` on class `s` (using
that each `vf s` is block-supported). -/
theorem assemble_multiBlockMask {vf : Cube P.k₀ → Cube P.m → Fp P}
    (hvf : ∀ s c, vf s c ≠ 0 → IsBlockPos P c) (s : Cube P.k₀) (c : Cube P.m) :
    assemble P 0 (- multiBlockMask P vf) (s, c) = vf s c := by
  unfold assemble
  by_cases hm : IsMask P (s, c)
  · rw [dif_pos hm]; show - -(vf s c) = vf s c; rw [neg_neg]
  · rw [dif_neg hm]
    have hcnb : ¬ IsBlockPos P c := fun hb => hm (Or.inr hb)
    have hvc : vf s c = 0 := by by_contra hh; exact hcnb (hvf s c hh)
    rw [hvc]; rfl

/-- The per-class fiber extension of the multi-class probe. -/
theorem multiBlockMask_fiber_mle {vf : Cube P.k₀ → Cube P.m → Fp P}
    (hvf : ∀ s c, vf s c ≠ 0 → IsBlockPos P c) (s : Cube P.k₀)
    (pt : Fin P.m → Fq) :
    mle (fun c => liftT P Fq (assemble P 0 (- multiBlockMask P vf)) (s, c)) pt =
      mle (fun c => algebraMap (Fp P) Fq (vf s c)) pt := by
  congr 1; funext c; unfold liftT; rw [assemble_multiBlockMask P hvf s c]

/-- The fold of the multi-class probe is the `λ`-combination of the per-class
lifts. -/
theorem foldedF₁_multiBlockMask {vf : Cube P.k₀ → Cube P.m → Fp P}
    (hvf : ∀ s c, vf s c ≠ 0 → IsBlockPos P c) (c : Cube P.m) :
    foldedF₁ P Fq Dom (assemble P 0 (- multiBlockMask P vf)) ch c =
      ∑ s, eqPoly ch.α s * algebraMap (Fp P) Fq (vf s c) := by
  unfold foldedF₁
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold liftT; rw [assemble_multiBlockMask P hvf s c]

/-- **The multi-class node probe is view-vanishing** (`lem:nodechannel`): a
per-class block fiber family with vanishing queried and `f̂₁` evaluations, and
whose commitment-node values lie in the kernel of the node matrix
(`oodRow`/`msgRow`), assembles to a view-vanishing perturbation. -/
theorem multiBlockMask_viewVanishes (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S)
    {vf : Cube P.k₀ → Cube P.m → Fp P}
    (hvf : ∀ s c, vf s c ≠ 0 → IsBlockPos P c)
    (hq : ∀ (s : Cube P.k₀) (t : Fin P.t₀),
      mle (fun c => algebraMap (Fp P) Fq (vf s c))
        (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0)
    (hz : ∀ (s : Cube P.k₀) (k : Fin P.s₁),
      mle (fun c => algebraMap (Fp P) Fq (vf s c)) (powSeq (ch.zf k) P.m) = 0)
    (hood : ∀ j, oodRow P Fq Dom ch j (fun s j =>
      mle (fun c => algebraMap (Fp P) Fq (vf s c))
        (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)) = 0)
    (hmsg1 : ∀ ℓ, msgRow P Fq Dom ch ℓ 1 (fun s j =>
      mle (fun c => algebraMap (Fp P) Fq (vf s c))
        (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)) = 0)
    (hmsg2 : ∀ ℓ, msgRow P Fq Dom ch ℓ 2 (fun s j =>
      mle (fun c => algebraMap (Fp P) Fq (vf s c))
        (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)) = 0) :
    ViewVanishes P Fq Dom S ch (assemble P 0 (- multiBlockMask P vf)) := by
  have hmsg : ∀ (ℓ : Fin P.k₀) (y : Fq),
      hPoly P Fq Dom S (assemble P 0 (- multiBlockMask P vf)) ch ℓ y =
      msgRow P Fq Dom ch ℓ y (fun s j =>
        mle (fun c => algebraMap (Fp P) Fq (vf s c))
          (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)) := by
    intro ℓ y
    rw [hPoly_channel P Fq Dom S (assemble P 0 (- multiBlockMask P vf)) ch ℓ y,
      crossTerm_eq_of_eq_nonblock P Fq Dom S ch hmf
        (assemble P 0 (- multiBlockMask P vf)) (0 : Cell P → Fp P)
        (fun s c hc => by
          rw [assemble_multiBlockMask P hvf s c]
          have hvc : vf s c = 0 := by by_contra hh; exact hc (hvf s c hh)
          simp [hvc]) ℓ y,
      crossTerm_zero P Fq Dom S ch ℓ y, mul_zero, add_zero, msgRow,
      evalT_eq_sum_classes, evalT_eq_sum_classes]
    simp only [multiBlockMask_fiber_mle P Fq hvf]
  refine ⟨fun j => ?_, fun ℓ => ?_, fun ℓ => ?_, fun t s => ?_, fun k => ?_⟩
  · show evalT P Fq (assemble P 0 (- multiBlockMask P vf)) (powSeq (ch.z j) P.k₀)
      (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) = 0
    rw [evalT_eq_sum_classes, ← hood j, oodRow]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [multiBlockMask_fiber_mle P Fq hvf]
  · rw [hmsg ℓ 1]; exact hmsg1 ℓ
  · rw [hmsg ℓ 2]; exact hmsg2 ℓ
  · show mle (fun c => liftT P Fq (assemble P 0 (- multiBlockMask P vf)) (s, c))
      (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0
    rw [multiBlockMask_fiber_mle P Fq hvf]; exact hq s t
  · rw [mle_fold_eq_sum_classes P Fq Dom (assemble P 0 (- multiBlockMask P vf)) ch]
    refine Finset.sum_eq_zero fun s _ => ?_
    rw [multiBlockMask_fiber_mle P Fq hvf, hz s k, mul_zero]

/-- **The node-probe pairing vanishes** (`lem:nodechannel`): for a view-vanishing
multi-class probe, the functional `φ` (trace-dual `w`) pairs to zero, decomposing
as the `λ`-weighted trace sum of the per-class pairings `⟨w, vf_s⟩`. -/
theorem multiBlockMask_pairing_zero
    (φ : Module.Dual (Fp P) (Cube P.m → Fq))
    (hφ : ∀ κ : viewKer P Fq Dom S ch, φ (pinFold P Fq Dom S ch κ) = 0)
    (w : Cube P.m → Fq) (hw : ∀ g, φ g = Algebra.trace (Fp P) Fq (∑ c, w c * g c))
    {vf : Cube P.k₀ → Cube P.m → Fp P}
    (hvf : ∀ s c, vf s c ≠ 0 → IsBlockPos P c)
    (hview : ViewVanishes P Fq Dom S ch (assemble P 0 (- multiBlockMask P vf))) :
    (∑ s, Algebra.trace (Fp P) Fq
      (eqPoly ch.α s * ∑ c, w c * algebraMap (Fp P) Fq (vf s c))) = 0 := by
  have h0 : φ (foldedF₁ P Fq Dom (assemble P 0 (- multiBlockMask P vf)) ch) = 0 := by
    have hmem : multiBlockMask P vf ∈ viewKer P Fq Dom S ch :=
      (mem_viewKer P Fq Dom S ch _).mpr hview
    exact hφ ⟨multiBlockMask P vf, hmem⟩
  rw [hw] at h0
  rw [show (∑ c, w c *
        foldedF₁ P Fq Dom (assemble P 0 (- multiBlockMask P vf)) ch c) =
      ∑ s, eqPoly ch.α s * ∑ c, w c * algebraMap (Fp P) Fq (vf s c) from by
    simp only [foldedF₁_multiBlockMask P Fq Dom ch hvf, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun c _ => by ring] at h0
  rw [map_sum] at h0
  exact h0

/-- **The slice pairing isolates the node coefficients** (`lem:nodechannel`):
pairing the confinement slice values `tr(β·w_c)` against a block fiber `vs` with
vanishing queried and `f̂₁` evaluations kills the queried and `f̂₁` coefficient
families, leaving only the node coefficients `cn` paired with `vs`'s node
values. -/
theorem confine_pairing_node_slice {ιβ : Type*} [Fintype ιβ]
    (b : Module.Basis ιβ (Fp P) Fq) (β : Fq) (w : Cube P.m → Fq)
    (cq : Fin P.t₀ → Fp P) (cn : Fin 2 → ιβ → Fp P) (cz : Fin P.s₁ → ιβ → Fp P)
    (hcoeff : ∀ c0, IsBlockPos P c0 → Algebra.trace (Fp P) Fq (β * w c0) =
        (∑ t, cq t * eqPoly (powSeq (ch.qs t : Fp P) P.m) c0)
        + (∑ j, ∑ i, cn j i * Algebra.trace (Fp P) Fq
            (b i * eqPoly (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) c0))
        + (∑ k, ∑ i, cz k i * Algebra.trace (Fp P) Fq
            (b i * eqPoly (powSeq (ch.zf k) P.m) c0)))
    {vs : Cube P.m → Fp P} (hvblk : ∀ c, vs c ≠ 0 → IsBlockPos P c)
    (hvq : ∀ t, mle vs (powSeq (ch.qs t : Fp P) P.m) = 0)
    (hvz : ∀ k, mle (fun c => algebraMap (Fp P) Fq (vs c)) (powSeq (ch.zf k) P.m) = 0) :
    (∑ c, Algebra.trace (Fp P) Fq (β * w c) * vs c) =
      ∑ j, ∑ i, cn j i * Algebra.trace (Fp P) Fq
        (b i * mle (fun c => algebraMap (Fp P) Fq (vs c))
          (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)) := by
  -- replace each block slice value by its coefficient combination
  rw [show (∑ c, Algebra.trace (Fp P) Fq (β * w c) * vs c) =
      ∑ c, ((∑ t, cq t * eqPoly (powSeq (ch.qs t : Fp P) P.m) c)
        + (∑ j, ∑ i, cn j i * Algebra.trace (Fp P) Fq
            (b i * eqPoly (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) c))
        + (∑ k, ∑ i, cz k i * Algebra.trace (Fp P) Fq
            (b i * eqPoly (powSeq (ch.zf k) P.m) c))) * vs c from ?_]
  · simp only [add_mul]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    -- the queried family vanishes (vs has zero queried evaluation)
    have hA : (∑ c, (∑ t, cq t * eqPoly (powSeq (ch.qs t : Fp P) P.m) c) * vs c) = 0 := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun t _ => ?_
      rw [show (∑ c, cq t * eqPoly (powSeq (ch.qs t : Fp P) P.m) c * vs c) =
          cq t * mle vs (powSeq (ch.qs t : Fp P) P.m) from by
        unfold mle; rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring, hvq t, mul_zero]
    -- the `f̂₁` family vanishes (vs has zero `f̂₁` evaluation)
    have hC : (∑ c, (∑ k, ∑ i, cz k i * Algebra.trace (Fp P) Fq
        (b i * eqPoly (powSeq (ch.zf k) P.m) c)) * vs c) = 0 := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [show (∑ c, cz k i * Algebra.trace (Fp P) Fq
            (b i * eqPoly (powSeq (ch.zf k) P.m) c) * vs c) =
          cz k i * Algebra.trace (Fp P) Fq
            (b i * mle (fun c => algebraMap (Fp P) Fq (vs c)) (powSeq (ch.zf k) P.m))
          from by
        rw [show mle (fun c => algebraMap (Fp P) Fq (vs c)) (powSeq (ch.zf k) P.m) =
            ∑ c, eqPoly (powSeq (ch.zf k) P.m) c * algebraMap (Fp P) Fq (vs c) from rfl,
          trace_smul_pairing, Finset.mul_sum]
        exact Finset.sum_congr rfl fun c _ => by ring, hvz k, mul_zero, map_zero, mul_zero]
    rw [hA, hC, zero_add, add_zero]
    -- the node family survives, paired against the node values
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show mle (fun c => algebraMap (Fp P) Fq (vs c)) (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) =
        ∑ c, eqPoly (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) c * algebraMap (Fp P) Fq (vs c) from rfl,
      trace_smul_pairing, Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  · refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hb : IsBlockPos P c
    · rw [hcoeff c hb]
    · have hvc : vs c = 0 := by by_contra hh; exact hb (hvblk c hh)
      rw [hvc, mul_zero, mul_zero]

/-- **The node probe realizes any node values** (`lem:nodechannel`): under node
genericity and the block budget, for every target `V` there is a per-class block
fiber family with vanishing queried and `f̂₁` evaluations and commitment-node
values exactly `V`. (Mirrors the `maskViewSection` construction, with no data and
no cross-term solving.) -/
theorem exists_nodeProbe [FiniteDimensional (Fp P) Fq] (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (hnode : NodeHyp P Fq Dom ch) (V : Cube P.k₀ → Fin 2 → Fq) :
    ∃ vf : Cube P.k₀ → Cube P.m → Fp P,
      (∀ s c, vf s c ≠ 0 → IsBlockPos P c) ∧
      (∀ s t, mle (fun c => algebraMap (Fp P) Fq (vf s c))
        (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0) ∧
      (∀ s j, mle (fun c => algebraMap (Fp P) Fq (vf s c))
        (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) = V s j) ∧
      (∀ s k, mle (fun c => algebraMap (Fp P) Fq (vf s c))
        (powSeq (ch.zf k) P.m) = 0) := by
  classical
  set Q : Finset (Fp P) :=
    Finset.image (fun t : Fin P.t₀ => (ch.qs t : Fp P)) Finset.univ with hQ
  set x : Fin Q.card → Fp P := fun i => (Q.equivFin.symm i : Fp P) with hx
  have hxinj : Function.Injective x := fun i i' h =>
    (Q.equivFin.symm).injective (Subtype.ext h)
  have hxmem : ∀ i, x i ∈ Q := fun i => (Q.equivFin.symm i).2
  have hx0 : ∀ i, x i ≠ 0 := by
    intro i h0
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp (hxmem i)
    exact hdom (by rw [← h0, ← ht]; exact (ch.qs t).2)
  have hQcard : Q.card ≤ P.t₀ :=
    le_trans Finset.card_image_le (by simp)
  have hbudget' : Q.card + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a := by omega
  have hsolve := fun s : Cube P.k₀ =>
    exists_block_fiber P Fq x (nodes P Fq Dom ch) hxinj hx0
      hnode.not_in_base hnode.gen hnode.conj hbudget'
      (fun _ => (0 : Fp P)) (Fin.append (V s) (fun _ : Fin P.s₁ => (0 : Fq)))
  choose vf hvblock hvq hvν using hsolve
  refine ⟨vf, hvblock, ?_, ?_, ?_⟩
  · intro s t
    obtain ⟨i, hi⟩ : ∃ i, x i = (ch.qs t : Fp P) := by
      have hm : ((ch.qs t : Fp P)) ∈ Q := Finset.mem_image_of_mem _ (Finset.mem_univ t)
      exact ⟨Q.equivFin ⟨_, hm⟩, by rw [hx]; simp⟩
    rw [← hi, hvq s i, map_zero]
  · intro s j
    have h := hvν s (Fin.castAdd P.s₁ j)
    rw [show nodes P Fq Dom ch (Fin.castAdd P.s₁ j) = ch.z j ^ 2 ^ P.k₀ from
      Fin.append_left _ _ j] at h
    rw [h, Fin.append_left]
  · intro s k
    have h := hvν s (Fin.natAdd 2 k)
    rw [show nodes P Fq Dom ch (Fin.natAdd 2 k) = ch.zf k from
      Fin.append_right _ _ k] at h
    rw [h, Fin.append_right]

/-- **A view-vanishing probe for any kernel element** (`lem:nodechannel`): if `V`
lies in the kernel of the node matrix, there is a view-vanishing multi-class
probe realizing exactly the node values `V`. -/
theorem exists_viewVanishing_nodeProbe [FiniteDimensional (Fp P) Fq]
    (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S) (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (hnode : NodeHyp P Fq Dom ch) (V : Cube P.k₀ → Fin 2 → Fq)
    (hood : ∀ j, oodRow P Fq Dom ch j V = 0)
    (hmsg1 : ∀ ℓ, msgRow P Fq Dom ch ℓ 1 V = 0)
    (hmsg2 : ∀ ℓ, msgRow P Fq Dom ch ℓ 2 V = 0) :
    ∃ vf : Cube P.k₀ → Cube P.m → Fp P,
      (∀ s c, vf s c ≠ 0 → IsBlockPos P c) ∧
      ViewVanishes P Fq Dom S ch (assemble P 0 (- multiBlockMask P vf)) ∧
      (∀ s t, mle (fun c => algebraMap (Fp P) Fq (vf s c))
        (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0) ∧
      (∀ s k, mle (fun c => algebraMap (Fp P) Fq (vf s c))
        (powSeq (ch.zf k) P.m) = 0) := by
  obtain ⟨vf, hvblk, hvq, hvn, hvz⟩ :=
    exists_nodeProbe P Fq Dom ch hdom hbudget hnode V
  have hVeq : (fun (s : Cube P.k₀) (j : Fin 2) =>
      mle (fun c => algebraMap (Fp P) Fq (vf s c))
        (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)) = V := by
    funext s j; exact hvn s j
  refine ⟨vf, hvblk,
    multiBlockMask_viewVanishes P Fq Dom S ch h2 hmf hvblk hvq hvz
      (fun j => by rw [hVeq]; exact hood j)
      (fun ℓ => by rw [hVeq]; exact hmsg1 ℓ)
      (fun ℓ => by rw [hVeq]; exact hmsg2 ℓ), hvq, hvz⟩

/-- **Confinement coefficients as functions of the twist** (`lem:nodechannel`
prep): the per-twist coefficient families of `confine_slice_coeffs` chosen
uniformly in `β`, so they can be evaluated at the basis elements `b r`. -/
theorem confine_slice_coeffs_choice [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S)
    (hspread : Submodule.span (Fp P) (Set.range (eqPoly ch.α)) = ⊤)
    {ιβ : Type*} [Fintype ιβ] [DecidableEq ιβ] (b : Module.Basis ιβ (Fp P) Fq)
    (φ : Module.Dual (Fp P) (Cube P.m → Fq))
    (hφ : ∀ κ : viewKer P Fq Dom S ch, φ (pinFold P Fq Dom S ch κ) = 0) :
    ∃ w : Cube P.m → Fq,
      (∀ g, φ g = Algebra.trace (Fp P) Fq (∑ c, w c * g c)) ∧
      ∃ (Cq : Fq → Fin P.t₀ → Fp P) (Cn : Fq → Fin 2 → ιβ → Fp P)
          (Cz : Fq → Fin P.s₁ → ιβ → Fp P),
        ∀ (β : Fq) c0, IsBlockPos P c0 →
          Algebra.trace (Fp P) Fq (β * w c0) =
            (∑ t, Cq β t * eqPoly (powSeq (ch.qs t : Fp P) P.m) c0)
            + (∑ j, ∑ i, Cn β j i * Algebra.trace (Fp P) Fq
                (b i * eqPoly (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) c0))
            + (∑ k, ∑ i, Cz β k i * Algebra.trace (Fp P) Fq
                (b i * eqPoly (powSeq (ch.zf k) P.m) c0)) := by
  obtain ⟨w, hw, hco⟩ :=
    confine_slice_coeffs P Fq Dom S ch h2 hmf hspread b φ hφ
  refine ⟨w, hw, ?_⟩
  choose Cq Cn Cz hC using hco
  exact ⟨Cq, Cn, Cz, hC⟩

/-- **The node-channel pairing identity** (`lem:nodechannel`): for every node
value `V` in the kernel of the node matrix, the `λ`-weighted trace pairing of the
node coefficients against `V` vanishes. This is the linear functional of `V` that
the row-space conclusion (and `cond:twist`) consumes; here `Cn (b r)` are the
confinement node coefficients of the trace-dual `w`. -/
theorem nodechannel_phi_pairing [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S)
    (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (hnode : NodeHyp P Fq Dom ch)
    (hspread : Submodule.span (Fp P) (Set.range (eqPoly ch.α)) = ⊤)
    {ιβ : Type*} [Fintype ιβ] [DecidableEq ιβ] (b : Module.Basis ιβ (Fp P) Fq)
    (φ : Module.Dual (Fp P) (Cube P.m → Fq))
    (hφ : ∀ κ : viewKer P Fq Dom S ch, φ (pinFold P Fq Dom S ch κ) = 0) :
    ∃ w : Cube P.m → Fq,
      (∀ g, φ g = Algebra.trace (Fp P) Fq (∑ c, w c * g c)) ∧
      ∃ Cn : Fq → Fin 2 → ιβ → Fp P,
        ∀ V : Cube P.k₀ → Fin 2 → Fq,
          (∀ j, oodRow P Fq Dom ch j V = 0) →
          (∀ ℓ, msgRow P Fq Dom ch ℓ 1 V = 0) →
          (∀ ℓ, msgRow P Fq Dom ch ℓ 2 V = 0) →
          (∑ s, Algebra.trace (Fp P) Fq (eqPoly ch.α s *
            ∑ r, (LinearMap.BilinForm.dualBasis (Algebra.traceForm (Fp P) Fq)
                (traceForm_nondegenerate (Fp P) Fq) b) r *
              algebraMap (Fp P) Fq (∑ j, ∑ i, Cn (b r) j i *
                Algebra.trace (Fp P) Fq (b i * V s j)))) = 0 := by
  obtain ⟨w, hw, Cq, Cn, Cz, hC⟩ :=
    confine_slice_coeffs_choice P Fq Dom S ch h2 hmf hspread b φ hφ
  refine ⟨w, hw, Cn, fun V hood hmsg1 hmsg2 => ?_⟩
  obtain ⟨vf, hvblk, hvq, hvn, hvz⟩ :=
    exists_nodeProbe P Fq Dom ch hdom hbudget hnode V
  have hVeq : (fun (s : Cube P.k₀) (j : Fin 2) =>
      mle (fun c => algebraMap (Fp P) Fq (vf s c))
        (powSeq (ch.z j ^ 2 ^ P.k₀) P.m)) = V := by
    funext s j; exact hvn s j
  have hview := multiBlockMask_viewVanishes P Fq Dom S ch h2 hmf hvblk hvq hvz
    (fun j => by rw [hVeq]; exact hood j)
    (fun ℓ => by rw [hVeq]; exact hmsg1 ℓ)
    (fun ℓ => by rw [hVeq]; exact hmsg2 ℓ)
  have hvqfp : ∀ s t, mle (vf s) (powSeq (ch.qs t : Fp P) P.m) = 0 := by
    intro s t
    have h := hvq s t
    rw [mle_algebraMap] at h
    exact (map_eq_zero_iff _ (algebraMap (Fp P) Fq).injective).mp h
  rw [← multiBlockMask_pairing_zero P Fq Dom S ch φ hφ w hw hvblk hview]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  rw [pairing_eq_sum_dualBasis b w (vf s)]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  congr 1
  refine congrArg (algebraMap (Fp P) Fq) ?_
  rw [confine_pairing_node_slice P Fq Dom ch b (b r) w (Cq (b r)) (Cn (b r))
    (Cz (b r)) (fun c0 hc0 => hC (b r) c0 hc0) (hvblk s) (hvqfp s) (fun k => hvz s k)]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hvn s j]

/-- The **trace-twist node functional** as an `Fp`-linear map (`cond:twist`'s
`T_j`): `x ↦ ∑_i (∑_r c_{i,r}·tr(x·b'_r))·bvec_i`. Applied at the Lagrange weight
`λ_s = êq(α,s)` it reproduces `lem:nodechannel`'s node functional `B_{s,j}`;
bundled as a `LinearMap` so `condTwist` (which needs an `Fq →ₗ[Fp] Fq`) applies. -/
def nodeTwistMap {ιβ : Type*} [Fintype ιβ] (b' : ιβ → Fq) (bvec : ιβ → Fq)
    (c : ιβ → ιβ → Fp P) : Fq →ₗ[Fp P] Fq :=
  ∑ i, LinearMap.smulRight
    (∑ r, c i r • (Algebra.trace (Fp P) Fq).comp (LinearMap.mulRight (Fp P) (b' r)))
    (bvec i)

theorem nodeTwistMap_apply {ιβ : Type*} [Fintype ιβ] (b' : ιβ → Fq) (bvec : ιβ → Fq)
    (c : ιβ → ιβ → Fp P) (x : Fq) :
    nodeTwistMap P Fq b' bvec c x =
      ∑ i, (∑ r, c i r * Algebra.trace (Fp P) Fq (x * b' r)) • bvec i := by
  unfold nodeTwistMap
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smulRight_apply]
  congr 1
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.mulRight_apply, smul_eq_mul]

/-- **The node functional lies in the row space** (`lem:nodechannel`, full): the
trace-twist node functional `B` derived from `φ` pairs to zero with every kernel
element of the node matrix, i.e. `B` lies in its `Fq`-row space. Combines the
node-channel pairing identity, the trace-twist regrouping, and the `θ`-variation
over the (`Fq`-closed) kernel. -/
theorem nodechannel_rowspace [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S)
    (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (hnode : NodeHyp P Fq Dom ch)
    (hspread : Submodule.span (Fp P) (Set.range (eqPoly ch.α)) = ⊤)
    {ιβ : Type*} [Fintype ιβ] [DecidableEq ιβ] (b : Module.Basis ιβ (Fp P) Fq)
    (φ : Module.Dual (Fp P) (Cube P.m → Fq))
    (hφ : ∀ κ : viewKer P Fq Dom S ch, φ (pinFold P Fq Dom S ch κ) = 0) :
    ∃ T : Fin 2 → (Fq →ₗ[Fp P] Fq),
      ∀ V : Cube P.k₀ → Fin 2 → Fq,
        (∀ j, oodRow P Fq Dom ch j V = 0) →
        (∀ ℓ, msgRow P Fq Dom ch ℓ 1 V = 0) →
        (∀ ℓ, msgRow P Fq Dom ch ℓ 2 V = 0) →
        (∑ s, ∑ j, T j (eqPoly ch.α s) * V s j) = 0 := by
  obtain ⟨w, hw, Cn, hpair⟩ :=
    nodechannel_phi_pairing P Fq Dom S ch h2 hmf hdom hbudget hnode hspread b φ hφ
  set β' := LinearMap.BilinForm.dualBasis (Algebra.traceForm (Fp P) Fq)
    (traceForm_nondegenerate (Fp P) Fq) b with hβ'
  set B : Cube P.k₀ → Fin 2 → Fq := fun s j =>
    ∑ i, (∑ r, Cn (b r) j i * Algebra.trace (Fp P) Fq (eqPoly ch.α s * β' r)) • b i
    with hB
  -- bundle the node functional as the `cond:twist` Fp-linear maps `T_j`
  set Tmap : Fin 2 → (Fq →ₗ[Fp P] Fq) :=
    fun j => nodeTwistMap P Fq β' b (fun i r => Cn (b r) j i) with hTmap
  have hBT : ∀ s j, Tmap j (eqPoly ch.α s) = B s j := by
    intro s j
    simp only [hTmap, nodeTwistMap_apply, hB]
  -- the trace-twist identity, per class
  have hBid : ∀ (V : Cube P.k₀ → Fin 2 → Fq) (s : Cube P.k₀),
      Algebra.trace (Fp P) Fq (eqPoly ch.α s * ∑ r, β' r *
        algebraMap (Fp P) Fq (∑ j, ∑ i, Cn (b r) j i *
          Algebra.trace (Fp P) Fq (b i * V s j))) =
      ∑ j, Algebra.trace (Fp P) Fq (B s j * V s j) := by
    intro V s
    rw [trace_smul_pairing]
    rw [show (∑ r, (∑ j, ∑ i, Cn (b r) j i * Algebra.trace (Fp P) Fq (b i * V s j)) *
          Algebra.trace (Fp P) Fq (eqPoly ch.α s * β' r)) =
        ∑ j, ∑ i, (∑ r, Cn (b r) j i * Algebra.trace (Fp P) Fq (eqPoly ch.α s * β' r)) *
          Algebra.trace (Fp P) Fq (b i * V s j) from by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun r _ => by ring]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hB]
    rw [show Algebra.trace (Fp P) Fq ((∑ i, (∑ r, Cn (b r) j i *
          Algebra.trace (Fp P) Fq (eqPoly ch.α s * β' r)) • b i) * V s j) =
        ∑ i, (∑ r, Cn (b r) j i * Algebra.trace (Fp P) Fq (eqPoly ch.α s * β' r)) *
          Algebra.trace (Fp P) Fq (b i * V s j) from by
      rw [Finset.sum_mul, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_mul_assoc, map_smul, smul_eq_mul]]
  -- summed identity: `∑_s tr(λ_s Φ(V)) = tr(∑_{s,j} B_{s,j} V_{s,j})`
  have hsum : ∀ V : Cube P.k₀ → Fin 2 → Fq,
      (∑ s, Algebra.trace (Fp P) Fq (eqPoly ch.α s * ∑ r, β' r *
        algebraMap (Fp P) Fq (∑ j, ∑ i, Cn (b r) j i *
          Algebra.trace (Fp P) Fq (b i * V s j)))) =
      Algebra.trace (Fp P) Fq (∑ s, ∑ j, B s j * V s j) := by
    intro V
    rw [map_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_sum, hBid V s]
  refine ⟨Tmap, fun V hood hmsg1 hmsg2 => ?_⟩
  rw [show (∑ s, ∑ j, Tmap j (eqPoly ch.α s) * V s j) = ∑ s, ∑ j, B s j * V s j from
    Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => by rw [hBT]]
  rw [trace_eq_zero_iff (Fp := Fp P)]
  intro θ
  -- `θ·V` is again in the kernel (the node matrix is `Fq`-linear)
  have hθood : ∀ j, oodRow P Fq Dom ch j (fun s j => θ * V s j) = 0 := by
    intro j
    rw [show oodRow P Fq Dom ch j (fun s j => θ * V s j) =
        θ * oodRow P Fq Dom ch j V from by
      unfold oodRow; rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring, hood j, mul_zero]
  have hmsgScale : ∀ (ℓ : Fin P.k₀) (y : Fq),
      msgRow P Fq Dom ch ℓ y (fun s j => θ * V s j) =
        θ * msgRow P Fq Dom ch ℓ y V := by
    intro ℓ y
    unfold msgRow
    rw [show (∑ s, eqPoly (mixedPoint P Fq Dom ch ℓ y (powSeq (ch.z 0) P.k₀)) s *
          (θ * V s 0)) =
        θ * ∑ s, eqPoly (mixedPoint P Fq Dom ch ℓ y (powSeq (ch.z 0) P.k₀)) s * V s 0
        from by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring,
      show (∑ s, eqPoly (mixedPoint P Fq Dom ch ℓ y (powSeq (ch.z 1) P.k₀)) s *
          (θ * V s 1)) =
        θ * ∑ s, eqPoly (mixedPoint P Fq Dom ch ℓ y (powSeq (ch.z 1) P.k₀)) s * V s 1
        from by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring]
    ring
  have hθmsg1 : ∀ ℓ, msgRow P Fq Dom ch ℓ 1 (fun s j => θ * V s j) = 0 :=
    fun ℓ => by rw [hmsgScale ℓ 1, hmsg1 ℓ, mul_zero]
  have hθmsg2 : ∀ ℓ, msgRow P Fq Dom ch ℓ 2 (fun s j => θ * V s j) = 0 :=
    fun ℓ => by rw [hmsgScale ℓ 2, hmsg2 ℓ, mul_zero]
  have hp := hpair (fun s j => θ * V s j) hθood hθmsg1 hθmsg2
  rw [hsum (fun s j => θ * V s j)] at hp
  rw [show θ * (∑ s, ∑ j, B s j * V s j) = ∑ s, ∑ j, B s j * (θ * V s j) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring]
  exact hp

/-- The node-matrix rows as vectors over `Cube k₀ × Fin 2` (the `2` ood rows + the
`2·k₀` msg rows at points `y ∈ {1,2}`), for `mem_rowspan_of_pairing_vanishes`. -/
def nodeRowVec : (Fin 2 ⊕ (Fin P.k₀ × Fin 2)) → (Cube P.k₀ × Fin 2 → Fq) := fun a =>
  match a with
  | Sum.inl j => fun p => if p.2 = j then eqPoly (powSeq (ch.z j) P.k₀) p.1 else 0
  | Sum.inr q => fun p =>
      if p.2 = 0 then
        prefixFactor P Fq Dom ch q.1 (![(1 : Fq), 2] q.2) (powSeq (ch.z 0) P.k₀) *
          eqPoly (mixedPoint P Fq Dom ch q.1 (![(1 : Fq), 2] q.2) (powSeq (ch.z 0) P.k₀)) p.1
      else
        ch.γ * (prefixFactor P Fq Dom ch q.1 (![(1 : Fq), 2] q.2) (powSeq (ch.z 1) P.k₀) *
          eqPoly (mixedPoint P Fq Dom ch q.1 (![(1 : Fq), 2] q.2) (powSeq (ch.z 1) P.k₀)) p.1)

/-- Pairing an ood row vector against `V` reproduces `oodRow`. -/
theorem nodeRowVec_inl_pairing (j : Fin 2) (V : Cube P.k₀ × Fin 2 → Fq) :
    (∑ p, nodeRowVec P Fq Dom ch (Sum.inl j) p * V p) =
      oodRow P Fq Dom ch j (fun s j => V (s, j)) := by
  rw [Fintype.sum_prod_type]
  unfold oodRow
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [nodeRowVec]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl]
  · intro j' _ hj'; rw [if_neg hj', zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Pairing a msg row vector against `V` reproduces `msgRow` (at `y ∈ {1,2}`). -/
theorem nodeRowVec_inr_pairing (q : Fin P.k₀ × Fin 2) (V : Cube P.k₀ × Fin 2 → Fq) :
    (∑ p, nodeRowVec P Fq Dom ch (Sum.inr q) p * V p) =
      msgRow P Fq Dom ch q.1 (![(1 : Fq), 2] q.2) (fun s j => V (s, j)) := by
  rw [Fintype.sum_prod_type]
  unfold msgRow
  conv_rhs => rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Fin.sum_univ_two]
  simp only [nodeRowVec, Fin.isValue, ↓reduceIte]
  rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]
  ring

/-- **`lem:nodechannel` → `cond:twist` bridge** (parts (c)): the bundled
trace-twist node functionals `T_j`, evaluated along the Lagrange weights, land in
the staircase span `{ω, τ_{m'}}` (over `z_j`). Combines the row-space duality
(`mem_rowspan_of_pairing_vanishes`) of `nodechannel_rowspace`'s `B ⊥ ker` with the
fact that every node-matrix row lies in the staircase span
(`eqPoly_*_mem_staircaseSpan`). This is exactly `condTwist_span`'s hypothesis. -/
theorem nodechannel_in_staircaseSpan [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S)
    (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (hnode : NodeHyp P Fq Dom ch)
    (hspread : Submodule.span (Fp P) (Set.range (eqPoly ch.α)) = ⊤)
    {ιβ : Type*} [Fintype ιβ] [DecidableEq ιβ] (b : Module.Basis ιβ (Fp P) Fq)
    (φ : Module.Dual (Fp P) (Cube P.m → Fq))
    (hφ : ∀ κ : viewKer P Fq Dom S ch, φ (pinFold P Fq Dom S ch κ) = 0) :
    ∃ T : Fin 2 → (Fq →ₗ[Fp P] Fq),
      (∀ V : Cube P.k₀ → Fin 2 → Fq,
        (∀ j, oodRow P Fq Dom ch j V = 0) →
        (∀ ℓ, msgRow P Fq Dom ch ℓ 1 V = 0) →
        (∀ ℓ, msgRow P Fq Dom ch ℓ 2 V = 0) →
        (∑ s, ∑ j, T j (eqPoly ch.α s) * V s j) = 0) ∧
      ∀ j : Fin 2,
        (fun s => T j (eqPoly ch.α s)) ∈
          Submodule.span Fq (insert (ptensor (czData P Fq (ch.z j)))
            (Set.range (fun m' => ptensor (stairVec (czData P Fq (ch.z j)) (fun _ => drow)
              (lamData P Fq Dom ch (ch.z j)) m')))) := by
  obtain ⟨T, hT⟩ :=
    nodechannel_rowspace P Fq Dom S ch h2 hmf hdom hbudget hnode hspread b φ hφ
  -- the node functional `B' (s,j) = T j (êq α s)` pairs to zero with `ker`
  have hpair : ∀ V : Cube P.k₀ × Fin 2 → Fq,
      (∀ a, ∑ p, nodeRowVec P Fq Dom ch a p * V p = 0) →
      ∑ p, (fun p => T p.2 (eqPoly ch.α p.1)) p * V p = 0 := by
    intro V hV
    rw [Fintype.sum_prod_type]
    refine hT (fun s j => V (s, j)) (fun j => ?_) (fun ℓ => ?_) (fun ℓ => ?_)
    · have h := hV (Sum.inl j); rw [nodeRowVec_inl_pairing] at h; exact h
    · have h := hV (Sum.inr (ℓ, 0)); rw [nodeRowVec_inr_pairing] at h
      simpa only [Matrix.cons_val_zero] using h
    · have h := hV (Sum.inr (ℓ, 1)); rw [nodeRowVec_inr_pairing] at h
      simp only [Matrix.cons_val_one, Matrix.head_cons] at h; exact h
  obtain ⟨c, hc⟩ := mem_rowspan_of_pairing_vanishes (nodeRowVec P Fq Dom ch)
    (fun p => T p.2 (eqPoly ch.α p.1)) hpair
  refine ⟨T, hT, fun j => ?_⟩
  -- write the weight-evaluation as a combination of the row vectors at component `j`
  have hfun : (fun s => T j (eqPoly ch.α s)) =
      ∑ a, c a • (fun s => nodeRowVec P Fq Dom ch a (s, j)) := by
    funext s
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact hc (s, j)
  rw [hfun]
  refine Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ ?_
  cases a with
  | inl j' =>
    by_cases hjj : j = j'
    · subst hjj
      rw [show (fun s => nodeRowVec P Fq Dom ch (Sum.inl j) (s, j)) =
          eqPoly (powSeq (ch.z j) P.k₀) from by
        funext s; dsimp only [nodeRowVec]; rw [if_pos rfl]]
      exact eqPoly_powSeq_mem_staircaseSpan P Fq Dom ch (ch.z j)
    · rw [show (fun s => nodeRowVec P Fq Dom ch (Sum.inl j') (s, j)) = 0 from by
        funext s; simp only [nodeRowVec, Pi.zero_apply]; rw [if_neg hjj]]
      exact Submodule.zero_mem _
  | inr q =>
    obtain ⟨ℓ, yi⟩ := q
    by_cases hj0 : j = 0
    · subst hj0
      rw [show (fun s => nodeRowVec P Fq Dom ch (Sum.inr (ℓ, yi)) (s, (0 : Fin 2))) =
          prefixFactor P Fq Dom ch ℓ (![(1 : Fq), 2] yi) (powSeq (ch.z 0) P.k₀) •
            eqPoly (mixedPoint P Fq Dom ch ℓ (![(1 : Fq), 2] yi) (powSeq (ch.z 0) P.k₀)) from by
        funext s
        simp only [nodeRowVec, Fin.isValue, ↓reduceIte]
        rw [Pi.smul_apply, smul_eq_mul]]
      exact Submodule.smul_mem _ _
        (eqPoly_mixedPoint_mem_staircaseSpan P Fq Dom ch ℓ (![(1 : Fq), 2] yi) (ch.z 0))
    · have hj1 : j = 1 := by omega
      subst hj1
      rw [show (fun s => nodeRowVec P Fq Dom ch (Sum.inr (ℓ, yi)) (s, (1 : Fin 2))) =
          (ch.γ * prefixFactor P Fq Dom ch ℓ (![(1 : Fq), 2] yi) (powSeq (ch.z 1) P.k₀)) •
            eqPoly (mixedPoint P Fq Dom ch ℓ (![(1 : Fq), 2] yi) (powSeq (ch.z 1) P.k₀)) from by
        funext s
        simp only [nodeRowVec, Fin.isValue, ↓reduceIte]
        rw [if_neg (by decide : (1 : Fin 2) ≠ 0), Pi.smul_apply, smul_eq_mul]
        ring]
      exact Submodule.smul_mem _ _
        (eqPoly_mixedPoint_mem_staircaseSpan P Fq Dom ch ℓ (![(1 : Fq), 2] yi) (ch.z 1))

/-- The round-0 (class) fold of the input weight `ŵ = S.w` at position `c`:
`ŵ(α₀, c) = ∑_s êq(α, s)·S.w(s, c)`. This is the `γ²`-component of the terminal
weight `W₀`, whose terminal pairing is the cross form `T_ŵ` of `cond:cross2`. -/
def wHat0 (c : Cube P.m) : Fq := ∑ s, eqPoly ch.α s * S.w (s, c)

/-- `ŵ(α₀, c)` is the multilinear extension (in the class challenge `α`) of the
input weight's `c`-column. This exposes `wHat0` to the multivariate Schwartz–Zippel
chain (`challenge_mle_α_zero_le`), settling `lem:termslice`'s `ŵ(α₀,c*) ≠ 0` bound
(`≤ k₀/q`) whenever the data column `S.w(·,c*)` is not identically zero. -/
theorem wHat0_eq_mle (c : Cube P.m) :
    wHat0 P Fq Dom S ch c = mle (fun s => S.w (s, c)) ch.α := rfl

/-- The **fold-table family** of `lem:noother` Step 1 (tex:616): the slice table
`w_{ℓ,x,t}(c) = ŵ(α_{<ℓ}, x, (t, c))`, the partial evaluation of the input weight
at the round-`ℓ` mixed point. The single-class perturbations invisible to the view
have vanishing pairings against every one of these. -/
def foldTable (ℓ : Fin P.k₀) (x : Fq) (t : Cube P.k₀) (c : Cube P.m) : Fq :=
  partialEval P Fq Dom ch S.w ℓ x t c

/-- **Fold tables are affine in the level point** (`lem:noother`/`lem:fullslice`
slice structure, tex:625): `w_{ℓ,x,t} = p_{ℓ,t} + x·q_{ℓ,t}` with `p = w_{ℓ,0,t}`
and `q = w_{ℓ,1,t} − w_{ℓ,0,t}`. -/
theorem foldTable_affine (ℓ : Fin P.k₀) (x : Fq) (t : Cube P.k₀) (c : Cube P.m) :
    foldTable P Fq Dom S ch ℓ x t c =
      foldTable P Fq Dom S ch ℓ 0 t c +
        x * (foldTable P Fq Dom S ch ℓ 1 t c - foldTable P Fq Dom S ch ℓ 0 t c) := by
  unfold foldTable
  exact partialEval_affine P Fq Dom ch S.w ℓ x t c

/-- **Slice tables are linearly independent when not proportional** (`lem:noother`
hypothesis, tex:607): a nonzero `2×2` minor of the two slice tables
`w_{L,0,·}` and `w_{L,1,·}` forces any pointwise relation
`a·w_{L,0} + b·w_{L,1} = 0` to have `a = b = 0`. -/
theorem foldTable_slice_indep (L : Fin P.k₀) (t t' : Cube P.k₀) (c c' : Cube P.m)
    (hminor : foldTable P Fq Dom S ch L 0 t c * foldTable P Fq Dom S ch L 1 t' c'
        - foldTable P Fq Dom S ch L 0 t' c' * foldTable P Fq Dom S ch L 1 t c ≠ 0)
    {a b : Fq}
    (h : ∀ (t : Cube P.k₀) (c : Cube P.m),
        a * foldTable P Fq Dom S ch L 0 t c + b * foldTable P Fq Dom S ch L 1 t c = 0) :
    a = 0 ∧ b = 0 :=
  two_by_two_zero hminor (h t c) (h t' c')

/-- **`lem:termslice` trace core** (tex:548): the terminal cross form's `Fp`-trace
is nonzero — some class `s` makes `tr(a·γ²·êq(α,s)·ŵ(α₀,c*)) ≠ 0`. Given SPREAD
(the weights `λ_s = êq(α,s)` span `Fq` over `Fp`), `a ≠ 0`, `γ ≠ 0`, and
`ŵ(α₀,c*) ≠ 0`. By `cond:cross2`'s identity `F_{a·θ^term}` has coefficient
`a·γ²·êq(α,s)·ŵ(α₀,c)` at cell `(s,c)`, so this says `tr ∘ F_{a·θ^term} ≠ 0` —
the `Fp`-spanning statement `prop:pinbound` consumes for the terminal direction. -/
theorem termCross_tr_ne_zero [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq]
    (hspread : Submodule.span (Fp P) (Set.range (eqPoly ch.α)) = ⊤)
    (a : Fq) (ha : a ≠ 0) (hγ : ch.γ ≠ 0) (c0 : Cube P.m)
    (hw : wHat0 P Fq Dom S ch c0 ≠ 0) :
    ∃ s, Algebra.trace (Fp P) Fq
      (a * ch.γ ^ 2 * eqPoly ch.α s * wHat0 P Fq Dom S ch c0) ≠ 0 := by
  have hX : a * ch.γ ^ 2 * wHat0 P Fq Dom S ch c0 ≠ 0 :=
    mul_ne_zero (mul_ne_zero ha (pow_ne_zero 2 hγ)) hw
  obtain ⟨s, hs⟩ := exists_trace_ne_zero_of_span (eqPoly ch.α) hspread _ hX
  refine ⟨s, ?_⟩
  rwa [show a * ch.γ ^ 2 * eqPoly ch.α s * wHat0 P Fq Dom S ch c0
      = eqPoly ch.α s * (a * ch.γ ^ 2 * wHat0 P Fq Dom S ch c0) from by ring]

/-- **`W₀` class-fold decomposition** (`cond:cross2` terminal computation, tex:519):
the `α`-fold of the terminal weight splits into the two node parts (weighted by
`A_j = ∑_s êq(α,s)·êq(powz_j,s)` and the commitment-node position MLEs) plus the
`γ²` cross part `ŵ(α₀,c)`. The `γ²`-component is the terminal cross form `T_ŵ`. -/
theorem weight_fold_class_decomp (c : Cube P.m) :
    (∑ s, eqPoly ch.α s * W₀ P Fq Dom S ch (s, c)) =
      (∑ s, eqPoly ch.α s * eqPoly (powSeq (ch.z 0) P.k₀) s) *
          eqPoly (powSeq (ch.z 0 ^ 2 ^ P.k₀) P.m) c
      + ch.γ * ((∑ s, eqPoly ch.α s * eqPoly (powSeq (ch.z 1) P.k₀) s) *
          eqPoly (powSeq (ch.z 1 ^ 2 ^ P.k₀) P.m) c)
      + ch.γ ^ 2 * wHat0 P Fq Dom S ch c := by
  unfold wHat0
  rw [Finset.sum_mul, Finset.sum_mul, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [W₀]
  ring

/-- **Terminal pairing node/cross split** (`cond:cross2`, tex:519-525): the
terminal sumcheck pairing `∑_c f̂₁(c)·(∑_s êq(α,s)·W₀(s,c))` splits into the two
node pairings `A_j·mle(f̂₁)(z_j^{2^{k₀}})` plus the `γ²` cross form
`T_ŵ = ∑_c f̂₁(c)·ŵ(α₀,c)`. The terminal protocol direction carries exactly this
`γ²·T_ŵ`, which is why `F_{θ^term} = γ²·T_ŵ ≠ 0` (`lem:termslice`). -/
theorem terminal_pairing_node_decomp (T : Cell P → Fp P) :
    (∑ c, foldedF₁ P Fq Dom T ch c * ∑ s, eqPoly ch.α s * W₀ P Fq Dom S ch (s, c)) =
      (∑ s, eqPoly ch.α s * eqPoly (powSeq (ch.z 0) P.k₀) s) *
          (∑ c, eqPoly (powSeq (ch.z 0 ^ 2 ^ P.k₀) P.m) c * foldedF₁ P Fq Dom T ch c)
      + ch.γ * ((∑ s, eqPoly ch.α s * eqPoly (powSeq (ch.z 1) P.k₀) s) *
          (∑ c, eqPoly (powSeq (ch.z 1 ^ 2 ^ P.k₀) P.m) c * foldedF₁ P Fq Dom T ch c))
      + ch.γ ^ 2 * (∑ c, foldedF₁ P Fq Dom T ch c * wHat0 P Fq Dom S ch c) := by
  refine Eq.trans (Finset.sum_congr rfl fun c _ => by rw [weight_fold_class_decomp]) ?_
  conv_rhs => rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  ring

/-- **`F_{θ^term} = γ²·T_ŵ`** (`cond:cross2`, tex:525): for a view-vanishing table
(all sumcheck messages zero), the terminal node combination equals `−γ²` times the
terminal cross form `T_ŵ`. So the *pure* node combination `θ^term` is **not** in
`ann(W')` unless `T_ŵ = 0` — the terminal protocol direction supplies the missing
cross form. -/
theorem terminal_node_eq_neg_cross (T : Cell P → Fp P) (h2 : (2 : Fq) ≠ 0)
    (hmsg0 : ∀ ℓ, hPoly P Fq Dom S T ch ℓ 0 = 0)
    (hmsg1 : ∀ ℓ, hPoly P Fq Dom S T ch ℓ 1 = 0)
    (hmsg2 : ∀ ℓ, hPoly P Fq Dom S T ch ℓ 2 = 0) :
    (∑ s, eqPoly ch.α s * eqPoly (powSeq (ch.z 0) P.k₀) s) *
          (∑ c, eqPoly (powSeq (ch.z 0 ^ 2 ^ P.k₀) P.m) c * foldedF₁ P Fq Dom T ch c)
      + ch.γ * ((∑ s, eqPoly ch.α s * eqPoly (powSeq (ch.z 1) P.k₀) s) *
          (∑ c, eqPoly (powSeq (ch.z 1 ^ 2 ^ P.k₀) P.m) c * foldedF₁ P Fq Dom T ch c))
      = -(ch.γ ^ 2 * (∑ c, foldedF₁ P Fq Dom T ch c * wHat0 P Fq Dom S ch c)) := by
  have h := terminal_pairing_eq_zero_of_msgs P Fq Dom S T ch h2 hmsg0 hmsg1 hmsg2
  rw [terminal_pairing_node_decomp] at h
  linear_combination h

/-- **`F_{θ^term} = γ²·T_ŵ` in `crossForm` terms** (`cond:cross2`): for a
view-vanishing table the cross form at the terminal direction
`θ^term = (A₀, γ·A₁)` (`A_j = ∑_s êq(α,s)·êq(powz_j,s)`) equals `−γ²·T_ŵ`, where
`T_ŵ = ∑_c f̂₁(c)·ŵ(α₀,c)`. So the terminal cross form is nonzero iff `T_ŵ ≠ 0`. -/
theorem crossForm_term_eq (T : Cell P → Fp P) (h2 : (2 : Fq) ≠ 0)
    (hmsg0 : ∀ ℓ, hPoly P Fq Dom S T ch ℓ 0 = 0)
    (hmsg1 : ∀ ℓ, hPoly P Fq Dom S T ch ℓ 1 = 0)
    (hmsg2 : ∀ ℓ, hPoly P Fq Dom S T ch ℓ 2 = 0) :
    crossForm P Fq Dom ch T
        ![∑ s, eqPoly ch.α s * eqPoly (powSeq (ch.z 0) P.k₀) s,
          ch.γ * ∑ s, eqPoly ch.α s * eqPoly (powSeq (ch.z 1) P.k₀) s] =
      -(ch.γ ^ 2 * (∑ c, foldedF₁ P Fq Dom T ch c * wHat0 P Fq Dom S ch c)) := by
  rw [crossForm_eq_fold]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, mle]
  linear_combination terminal_node_eq_neg_cross P Fq Dom S ch T h2 hmsg0 hmsg1 hmsg2

/-- **`lem:nodechannel` → `cond:twist`, full bridge** (parts (d)+(e)): the node
functional is forced **untwisted** — there are scalars `θ_j` so the node functional
equals `θ_j · êq(α, ·)` (and still lies in the node-matrix row space). Applies
`condTwist_span` to each bundled `T_j` (whose weights land in the staircase span
by `nodechannel_in_staircaseSpan`); the Good-set genericity (`hker` = `M^{(j)}`
trivial kernel, `hDr` = Frobenius gaps `α₀^{pʳ} − α₀ ≠ 0`) is deferred to the ε₃
measure step. This is the `cond:twist` output consumed by `cond:cross2`. -/
theorem nodechannel_untwisted [FiniteDimensional (Fp P) Fq]
    [Algebra.IsSeparable (Fp P) Fq] [CharP Fq P.p]
    (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S) (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (hnode : NodeHyp P Fq Dom ch)
    (hspread : Submodule.span (Fp P) (Set.range (eqPoly ch.α)) = ⊤)
    {ιβ : Type*} [Fintype ιβ] [DecidableEq ιβ] (b : Module.Basis ιβ (Fp P) Fq)
    (hk : 0 < P.k₀) (hd0 : 0 < extDeg P Fq)
    (hcard : Fintype.card (Fp P) = P.p)
    (hcardq : Fintype.card Fq = P.p ^ extDeg P Fq)
    (hker : ∀ j : Fin 2, ∀ c : Fin (extDeg P Fq) → Fq, c ⟨0, hd0⟩ = 0 →
        (∀ m : Fin P.k₀, (⟨0, hk⟩ : Fin P.k₀) < m →
          ∑ r, c r * (ch.α m ^ P.p ^ (r : ℕ) - powSeq (ch.z j) P.k₀ m) = 0) → c = 0)
    (hDr : ∀ j : Fin 2, ∀ r : Fin (extDeg P Fq), (r : ℕ) ≠ 0 →
        ch.α ⟨0, hk⟩ ^ P.p ^ (r : ℕ) - ch.α ⟨0, hk⟩ ≠ 0)
    (φ : Module.Dual (Fp P) (Cube P.m → Fq))
    (hφ : ∀ κ : viewKer P Fq Dom S ch, φ (pinFold P Fq Dom S ch κ) = 0) :
    ∃ θ : Fin 2 → Fq, ∀ V : Cube P.k₀ → Fin 2 → Fq,
        (∀ j, oodRow P Fq Dom ch j V = 0) →
        (∀ ℓ, msgRow P Fq Dom ch ℓ 1 V = 0) →
        (∀ ℓ, msgRow P Fq Dom ch ℓ 2 V = 0) →
        (∑ s, ∑ j, θ j * eqPoly ch.α s * V s j) = 0 := by
  obtain ⟨T, hT, hspan⟩ :=
    nodechannel_in_staircaseSpan P Fq Dom S ch h2 hmf hdom hbudget hnode hspread b φ hφ
  have hθ : ∀ j : Fin 2, ∃ c : Fq, ∀ x, T j x = c * x := fun j =>
    condTwist_span hk hcard (extDeg P Fq) hd0 hcardq rfl (T j) (ch.z j) ch.α
      (hspan j) (hker j) (hDr j)
  choose θ hθeq using hθ
  refine ⟨θ, fun V hood hmsg1 hmsg2 => ?_⟩
  rw [show (∑ s, ∑ j, θ j * eqPoly ch.α s * V s j) =
      ∑ s, ∑ j, T j (eqPoly ch.α s) * V s j from
    Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => by
      rw [hθeq j (eqPoly ch.α s)]]
  exact hT V hood hmsg1 hmsg2

end ZkWhir
