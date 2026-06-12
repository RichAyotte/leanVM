/-
`prop:uniform`, primal form: solving the masked view. Under the node
genericity package (`lem:nodeprob`), the full row rank of the node system
(`thm:twopoint`), the mask budget, and `MaskFree`, the blocks absorb the
reduced view of every consistency difference: `MaskViewSection` holds.

Construction, per `lem:kersurj`: solve the `2 + 2k₀` node system for the
per-class node evaluations (the cross contributions of the data are fixed —
blocks contribute none, `lem:blocks`); then realize, per class, the required
block fiber by CRT interpolation (`exists_block_fiber`): kill the queried
evaluations, hit the solved commitment-node values, kill the `f̂₁`-node
values.

Part of the `GoodSetAbsorption` formalization campaign.
-/
import Mathlib
import Zkwhir.Statement
import Zkwhir.Sumcheck
import Zkwhir.Channel
import Zkwhir.Blocks
import Zkwhir.Absorption

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

namespace ZkWhir

variable (P : Params) (Fq : Type*) [Field Fq] [Fintype Fq]
  [Algebra (Fp P) Fq] (Dom : Finset (Fp P)) [Nonempty {x // x ∈ Dom}]

variable (S : Stmt P Fq) (ch : Challenges P Fq Dom)

/-- The `2 + s₁` evaluation nodes of the per-class fibers: the two
commitment nodes `z_j^(2^k₀)` followed by the `f̂₁` out-of-domain points. -/
def nodes : Fin (2 + P.s₁) → Fq :=
  Fin.append (fun j : Fin 2 => ch.z j ^ 2 ^ P.k₀) ch.zf

/-- An out-of-domain row of the node system. -/
def oodRow (j : Fin 2) (n : Cube P.k₀ → Fin 2 → Fq) : Fq :=
  ∑ s, eqPoly (powSeq (ch.z j) P.k₀) s * n s j

/-- A message row of the node system, at level `ℓ` and point `y`: the node
part of the channel decomposition (`hPoly_channel`). -/
def msgRow (ℓ : Fin P.k₀) (y : Fq) (n : Cube P.k₀ → Fin 2 → Fq) : Fq :=
  prefixFactor P Fq Dom ch ℓ y (powSeq (ch.z 0) P.k₀) *
    ∑ s, eqPoly (mixedPoint P Fq Dom ch ℓ y (powSeq (ch.z 0) P.k₀)) s *
      n s 0 +
  ch.γ * (prefixFactor P Fq Dom ch ℓ y (powSeq (ch.z 1) P.k₀) *
    ∑ s, eqPoly (mixedPoint P Fq Dom ch ℓ y (powSeq (ch.z 1) P.k₀)) s *
      n s 1)

/-- **Full row rank of the node system** (`thm:twopoint`, consumable form):
the `2 + 2k₀` value rows reach every target. A Good-set predicate at this
stage of the campaign. -/
def RowSurj : Prop :=
  ∀ (tood : Fin 2 → Fq) (tm1 tm2 : Fin P.k₀ → Fq),
    ∃ n : Cube P.k₀ → Fin 2 → Fq,
      (∀ j, oodRow P Fq Dom ch j n = tood j) ∧
      (∀ ℓ, msgRow P Fq Dom ch ℓ 1 n = tm1 ℓ) ∧
      (∀ ℓ, msgRow P Fq Dom ch ℓ 2 n = tm2 ℓ)

/-- The node genericity package (`lem:nodeprob`): the nodes lie outside the
base field, generate the extension, and are pairwise non-conjugate. A
Good-set predicate. -/
structure NodeHyp : Prop where
  not_in_base : ∀ j, nodes P Fq Dom ch j ∉ Set.range (algebraMap (Fp P) Fq)
  gen : ∀ j, (minpoly (Fp P) (nodes P Fq Dom ch j)).natDegree =
    Module.finrank (Fp P) Fq
  conj : ∀ j j', j ≠ j' →
    minpoly (Fp P) (nodes P Fq Dom ch j) ≠
    minpoly (Fp P) (nodes P Fq Dom ch j')

/-- **`prop:uniform`, primal form**: the node and rank conditions, the mask
budget, the nonzero domain, and `MaskFree` make the masked view a section —
every consistency difference's reduced view is absorbed by the blocks. -/
theorem maskViewSection_of_rowSurj [FiniteDimensional (Fp P) Fq]
    (hmf : MaskFree P Fq S) (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (hnode : NodeHyp P Fq Dom ch) (hrow : RowSurj P Fq Dom ch) :
    MaskViewSection P Fq Dom S ch := by
  classical
  intro δ hδ
  -- the deduplicated queried points
  set Q : Finset (Fp P) :=
    Finset.image (fun t : Fin P.t₀ => (ch.qs t : Fp P)) Finset.univ with hQ
  set x : Fin Q.card → Fp P := fun i => (Q.equivFin.symm i : Fp P) with hx
  have hxinj : Function.Injective x := by
    intro i i' h
    exact (Q.equivFin.symm).injective (Subtype.ext h)
  have hxmem : ∀ i, x i ∈ Q := fun i => (Q.equivFin.symm i).2
  have hx0 : ∀ i, x i ≠ 0 := by
    intro i h0
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp (hxmem i)
    apply hdom
    rw [← h0, ← ht]
    exact (ch.qs t).2
  have hQcard : Q.card ≤ P.t₀ := by
    calc Q.card ≤ (Finset.univ : Finset (Fin P.t₀)).card :=
          Finset.card_image_le
      _ = P.t₀ := by simp
  -- the data table with zero masks
  set T₀ : Cell P → Fp P := assemble P δ 0 with hT₀
  -- solve the node system against the cross contributions of the data
  obtain ⟨n, hnood, hnm1, hnm2⟩ := hrow (fun _ => 0)
    (fun ℓ => -(ch.γ ^ 2 * crossTerm P Fq Dom S T₀ ch ℓ 1))
    (fun ℓ => -(ch.γ ^ 2 * crossTerm P Fq Dom S T₀ ch ℓ 2))
  -- per-class block fibers by CRT
  have hbudget' : Q.card + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤
      2 ^ P.a := by omega
  have hsolve := fun s : Cube P.k₀ =>
    exists_block_fiber P Fq x (nodes P Fq Dom ch) hxinj hx0
      hnode.not_in_base hnode.gen hnode.conj hbudget'
      (fun i => - mle (fun c => T₀ (s, c)) (powSeq (x i) P.m))
      (Fin.append
        (fun j' : Fin 2 => n s j' -
          mle (fun c => algebraMap (Fp P) Fq (T₀ (s, c)))
            (powSeq (ch.z j' ^ 2 ^ P.k₀) P.m))
        (fun j' : Fin P.s₁ =>
          - mle (fun c => algebraMap (Fp P) Fq (T₀ (s, c)))
            (powSeq (ch.zf j') P.m)))
  choose v hvblock hvq hvν using hsolve
  set μ : MaskAssign P :=
    fun u => if IsBlockPos P u.1.2 then - v u.1.1 u.1.2 else 0 with hμ
  refine ⟨μ, ?_⟩
  -- the assembled table decomposes as data plus block fibers
  have htab : assemble P δ (-μ) = fun w : Cell P => T₀ w + v w.1 w.2 := by
    funext w
    by_cases hmask : IsMask P w
    · have h0 : T₀ w = 0 := by
        rw [hT₀]
        show (if h : IsMask P w then (0 : MaskAssign P) ⟨w, h⟩
          else δ ⟨w, h⟩) = 0
        rw [dif_pos hmask]
        rfl
      show (if h : IsMask P w then (-μ) ⟨w, h⟩ else δ ⟨w, h⟩) =
        T₀ w + v w.1 w.2
      rw [dif_pos hmask, h0, zero_add]
      show -(μ ⟨w, hmask⟩) = v w.1 w.2
      rw [hμ]
      show -(if IsBlockPos P w.2 then - v w.1 w.2 else 0) = v w.1 w.2
      by_cases hblock : IsBlockPos P w.2
      · rw [if_pos hblock, neg_neg]
      · rw [if_neg hblock, neg_zero]
        have hv0 : v w.1 w.2 = 0 := by
          by_contra hnz
          exact hblock (hvblock w.1 w.2 hnz)
        rw [hv0]
    · have hnb : ¬ IsBlockPos P w.2 := fun hb => hmask (Or.inr hb)
      have hv0 : v w.1 w.2 = 0 := by
        by_contra hnz
        exact hnb (hvblock w.1 w.2 hnz)
      show (if h : IsMask P w then (-μ) ⟨w, h⟩ else δ ⟨w, h⟩) =
        T₀ w + v w.1 w.2
      rw [dif_neg hmask, hv0, add_zero, hT₀]
      show δ ⟨w, hmask⟩ =
        (if h : IsMask P w then (0 : MaskAssign P) ⟨w, h⟩ else δ ⟨w, h⟩)
      rw [dif_neg hmask]
  -- the assembled table agrees with the data off the blocks
  have hagree : ∀ s (c : Cube P.m), ¬ IsBlockPos P c →
      assemble P δ (-μ) (s, c) = T₀ (s, c) := by
    intro s c hc
    have hv0 : v s c = 0 := by
      by_contra hnz
      exact hc (hvblock s c hnz)
    rw [htab]
    simp [hv0]
  -- fiber extensions decompose
  have hfib : ∀ (s : Cube P.k₀) (pt : Fin P.m → Fq),
      mle (fun c => liftT P Fq (assemble P δ (-μ)) (s, c)) pt =
      mle (fun c => algebraMap (Fp P) Fq (T₀ (s, c))) pt +
      mle (fun c => algebraMap (Fp P) Fq (v s c)) pt := by
    intro s pt
    rw [← mle_add]
    congr 1
    funext c
    unfold liftT
    rw [htab]
    simp [map_add]
  -- full-fiber values at the queried points vanish
  have hqfull : ∀ (t : Fin P.t₀) (s : Cube P.k₀),
      queryAnswer P Fq Dom (assemble P δ (-μ)) ch t s = 0 := by
    intro t s
    obtain ⟨i, hi⟩ : ∃ i, x i = (ch.qs t : Fp P) := by
      have hm : ((ch.qs t : Fp P)) ∈ Q :=
        Finset.mem_image_of_mem _ (Finset.mem_univ t)
      refine ⟨Q.equivFin ⟨_, hm⟩, ?_⟩
      rw [hx]
      simp
    show mle (fun c => liftT P Fq (assemble P δ (-μ)) (s, c))
      (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0
    rw [hfib, ← hi, hvq s i, mle_algebraMap, ← map_add]
    simp
  -- full-fiber values at the commitment nodes hit the solved system
  have hnfull : ∀ (s : Cube P.k₀) (j : Fin 2),
      mle (fun c => liftT P Fq (assemble P δ (-μ)) (s, c))
        (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) = n s j := by
    intro s j
    rw [hfib]
    have h := hvν s (Fin.castAdd P.s₁ j)
    rw [Fin.append_left] at h
    rw [show nodes P Fq Dom ch (Fin.castAdd P.s₁ j) = ch.z j ^ 2 ^ P.k₀ from
      Fin.append_left _ _ j] at h
    rw [h]
    ring
  -- full-fiber values at the `f̂₁` nodes vanish
  have hzfull : ∀ (s : Cube P.k₀) (j : Fin P.s₁),
      mle (fun c => liftT P Fq (assemble P δ (-μ)) (s, c))
        (powSeq (ch.zf j) P.m) = 0 := by
    intro s j
    rw [hfib]
    have h := hvν s (Fin.natAdd 2 j)
    rw [Fin.append_right] at h
    rw [show nodes P Fq Dom ch (Fin.natAdd 2 j) = ch.zf j from
      Fin.append_right _ _ j] at h
    rw [h]
    ring
  refine ⟨?_, ?_, ?_, hqfull, ?_⟩
  · -- out-of-domain answers
    intro j
    show evalT P Fq (assemble P δ (-μ)) (powSeq (ch.z j) P.k₀)
      (powSeq (ch.z j ^ 2 ^ P.k₀) P.m) = 0
    rw [evalT_eq_sum_classes]
    simp only [hnfull]
    exact hnood j
  · -- messages at `X = 1`
    intro ℓ
    rw [hPoly_channel P Fq Dom S (assemble P δ (-μ)) ch ℓ 1,
      evalT_eq_sum_classes, evalT_eq_sum_classes,
      crossTerm_eq_of_eq_nonblock P Fq Dom S ch hmf
        (assemble P δ (-μ)) T₀ hagree ℓ 1]
    simp only [hnfull]
    have hm := hnm1 ℓ
    unfold msgRow at hm
    linear_combination hm
  · -- messages at `X = 2`
    intro ℓ
    rw [hPoly_channel P Fq Dom S (assemble P δ (-μ)) ch ℓ 2,
      evalT_eq_sum_classes, evalT_eq_sum_classes,
      crossTerm_eq_of_eq_nonblock P Fq Dom S ch hmf
        (assemble P δ (-μ)) T₀ hagree ℓ 2]
    simp only [hnfull]
    have hm := hnm2 ℓ
    unfold msgRow at hm
    linear_combination hm
  · -- `f̂₁` out-of-domain answers
    intro j
    rw [mle_fold_eq_sum_classes P Fq Dom (assemble P δ (-μ)) ch]
    simp [hzfull]

end ZkWhir
