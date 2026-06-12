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
import Zkwhir.Toolbox
import Zkwhir.Sumcheck
import Zkwhir.Channel
import Zkwhir.Blocks
import Zkwhir.Absorption

set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

noncomputable section

open scoped ENNReal

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

/-- The weight table of the node-system rows: every row functional is the
pairing against its weight vector. The index `y : Fin 2` encodes the
evaluation point `y + 1 ∈ {1, 2}`. -/
def rowWeights : (Fin 2 ⊕ Fin P.k₀ × Fin 2) → Cube P.k₀ → Fin 2 → Fq
  | Sum.inl j => fun s j' =>
      if j' = j then eqPoly (powSeq (ch.z j) P.k₀) s else 0
  | Sum.inr (ℓ, y) => fun s j' =>
      if j' = 0 then
        prefixFactor P Fq Dom ch ℓ (((y : ℕ) + 1 : ℕ) : Fq)
            (powSeq (ch.z 0) P.k₀) *
          eqPoly (mixedPoint P Fq Dom ch ℓ (((y : ℕ) + 1 : ℕ) : Fq)
            (powSeq (ch.z 0) P.k₀)) s
      else
        ch.γ * (prefixFactor P Fq Dom ch ℓ (((y : ℕ) + 1 : ℕ) : Fq)
            (powSeq (ch.z 1) P.k₀) *
          eqPoly (mixedPoint P Fq Dom ch ℓ (((y : ℕ) + 1 : ℕ) : Fq)
            (powSeq (ch.z 1) P.k₀)) s)

/-- **Full row rank from row independence** (`thm:twopoint` ⟹ `RowSurj`):
if the row weight vectors are linearly independent, the node system reaches
every target. -/
theorem rowSurj_of_rowsLI
    (hli : LinearIndependent Fq (rowWeights P Fq Dom ch)) :
    RowSurj P Fq Dom ch := by
  classical
  -- the row functionals
  set φ : (Fin 2 ⊕ Fin P.k₀ × Fin 2) →
      (Cube P.k₀ → Fin 2 → Fq) →ₗ[Fq] Fq := fun r =>
    { toFun := fun n => ∑ s, ∑ j, rowWeights P Fq Dom ch r s j * n s j
      map_add' := by
        intro n n'
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp [Pi.add_apply, mul_add]
      map_smul' := by
        intro a n
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Pi.smul_apply, smul_eq_mul]
        ring } with hφ
  -- evaluating a functional at an indicator reads off a weight entry
  have heval : ∀ (r) (s₀ : Cube P.k₀) (j₀ : Fin 2),
      φ r (fun s' j' => if s' = s₀ ∧ j' = j₀ then 1 else 0) =
        rowWeights P Fq Dom ch r s₀ j₀ := by
    intro r s₀ j₀
    show (∑ s, ∑ j, rowWeights P Fq Dom ch r s j *
      (if s = s₀ ∧ j = j₀ then 1 else 0)) = _
    rw [Finset.sum_eq_single s₀]
    · rw [Finset.sum_eq_single j₀]
      · simp
      · intro j _ hj
        simp [hj]
      · intro h
        exact absurd (Finset.mem_univ j₀) h
    · intro s _ hs
      refine Finset.sum_eq_zero fun j _ => ?_
      simp [hs]
    · intro h
      exact absurd (Finset.mem_univ s₀) h
  -- the functionals inherit independence from the weights
  have hφli : LinearIndependent Fq φ := by
    rw [linearIndependent_iff']
    intro t g hsum r hr
    have hW : ∑ i ∈ t, g i • rowWeights P Fq Dom ch i = 0 := by
      funext s₀ j₀
      have happ := congrArg (fun f : (Cube P.k₀ → Fin 2 → Fq) →ₗ[Fq] Fq =>
        f (fun s' j' => if s' = s₀ ∧ j' = j₀ then 1 else 0)) hsum
      simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
        smul_eq_mul, LinearMap.zero_apply] at happ
      calc (∑ i ∈ t, g i • rowWeights P Fq Dom ch i) s₀ j₀
          = ∑ i ∈ t, g i * rowWeights P Fq Dom ch i s₀ j₀ := by
            simp [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        _ = ∑ i ∈ t, g i * φ i (fun s' j' =>
              if s' = s₀ ∧ j' = j₀ then 1 else 0) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [heval]
        _ = 0 := happ

    exact linearIndependent_iff'.mp hli t g hW r hr
  -- solve
  intro tood tm1 tm2
  obtain ⟨n, hn⟩ := exists_preimage_of_linearIndependent_dual φ hφli
    (Sum.elim tood fun p : Fin P.k₀ × Fin 2 =>
      if p.2 = 0 then tm1 p.1 else tm2 p.1)
  -- the `ood` rows
  have hood_eq : ∀ (j : Fin 2) (n' : Cube P.k₀ → Fin 2 → Fq),
      φ (Sum.inl j) n' = oodRow P Fq Dom ch j n' := by
    intro j n'
    show (∑ s, ∑ j', rowWeights P Fq Dom ch (Sum.inl j) s j' * n' s j') = _
    refine Finset.sum_congr rfl fun s _ => ?_
    show (∑ j', (if j' = j then eqPoly (powSeq (ch.z j) P.k₀) s else 0) *
      n' s j') = _
    rw [Finset.sum_eq_single j]
    · simp
    · intro j' _ hj'
      simp [hj']
    · intro h
      exact absurd (Finset.mem_univ j) h
  -- the message rows
  have hmsg_eq : ∀ (ℓ : Fin P.k₀) (y : Fin 2)
      (n' : Cube P.k₀ → Fin 2 → Fq),
      φ (Sum.inr (ℓ, y)) n' =
        msgRow P Fq Dom ch ℓ (((y : ℕ) + 1 : ℕ) : Fq) n' := by
    intro ℓ y n'
    show (∑ s, ∑ j', rowWeights P Fq Dom ch (Sum.inr (ℓ, y)) s j' *
      n' s j') = _
    unfold msgRow
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Fin.sum_univ_two (f := fun j' =>
      rowWeights P Fq Dom ch (Sum.inr (ℓ, y)) s j' * n' s j')]
    have h0 : rowWeights P Fq Dom ch (Sum.inr (ℓ, y)) s 0 =
        prefixFactor P Fq Dom ch ℓ (((y : ℕ) + 1 : ℕ) : Fq)
            (powSeq (ch.z 0) P.k₀) *
          eqPoly (mixedPoint P Fq Dom ch ℓ (((y : ℕ) + 1 : ℕ) : Fq)
            (powSeq (ch.z 0) P.k₀)) s := by
      simp [rowWeights]
    have h1 : rowWeights P Fq Dom ch (Sum.inr (ℓ, y)) s 1 =
        ch.γ * (prefixFactor P Fq Dom ch ℓ (((y : ℕ) + 1 : ℕ) : Fq)
            (powSeq (ch.z 1) P.k₀) *
          eqPoly (mixedPoint P Fq Dom ch ℓ (((y : ℕ) + 1 : ℕ) : Fq)
            (powSeq (ch.z 1) P.k₀)) s) := by
      simp [rowWeights]
    rw [h0, h1]
    ring
  refine ⟨n, ?_, ?_, ?_⟩
  · intro j
    have h := hn (Sum.inl j)
    rw [hood_eq j n] at h
    simpa using h
  · intro ℓ
    have h := hn (Sum.inr (ℓ, 0))
    rw [hmsg_eq ℓ 0 n] at h
    simpa using h
  · intro ℓ
    have h := hn (Sum.inr (ℓ, 1))
    rw [hmsg_eq ℓ 1 n] at h
    have h2 : (((1 : Fin 2) : ℕ) + 1 : ℕ) = 2 := rfl
    rw [h2] at h
    simpa [one_add_one_eq_two] using h

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

/-- **The good-set assembly**: `GoodSetAbsorption` follows from probability
bounds for the three remaining structural conditions — node genericity, row
independence, and pinning — summing below `εZK`. This isolates the three
probability targets of the campaign exactly. -/
theorem goodSetAbsorption_of_bounds [FiniteDimensional (Fp P) Fq]
    (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S)
    (hdom : (0 : Fp P) ∉ Dom)
    (hbudget : P.t₀ + Module.finrank (Fp P) Fq * (2 + P.s₁) ≤ 2 ^ P.a)
    (ε₁ ε₂ ε₃ : ℝ≥0∞)
    (hA : (challengePMF P Fq Dom).toOuterMeasure
      {ch | ¬ NodeHyp P Fq Dom ch} ≤ ε₁)
    (hB : (challengePMF P Fq Dom).toOuterMeasure
      {ch | ¬ LinearIndependent Fq (rowWeights P Fq Dom ch)} ≤ ε₂)
    (hC : (challengePMF P Fq Dom).toOuterMeasure
      {ch | ¬ Pinning P Fq Dom S ch} ≤ ε₃)
    (hsum : ε₁ + ε₂ + ε₃ ≤ εZK P Fq) :
    GoodSetAbsorption P Fq Dom S := by
  refine goodSetAbsorption_of_predicates P Fq Dom S h2 hmf
    {ch | NodeHyp P Fq Dom ch ∧
      LinearIndependent Fq (rowWeights P Fq Dom ch) ∧
      Pinning P Fq Dom S ch} ?_ ?_
  · have hsubset : {ch : Challenges P Fq Dom | NodeHyp P Fq Dom ch ∧
        LinearIndependent Fq (rowWeights P Fq Dom ch) ∧
        Pinning P Fq Dom S ch}ᶜ ⊆
        ({ch | ¬ NodeHyp P Fq Dom ch} ∪
          {ch | ¬ LinearIndependent Fq (rowWeights P Fq Dom ch)}) ∪
        {ch | ¬ Pinning P Fq Dom S ch} := by
      intro ch hch
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and_or] at hch
      rcases hch with h | h | h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
    calc (challengePMF P Fq Dom).toOuterMeasure _
        ≤ (challengePMF P Fq Dom).toOuterMeasure
          (({ch | ¬ NodeHyp P Fq Dom ch} ∪
            {ch | ¬ LinearIndependent Fq (rowWeights P Fq Dom ch)}) ∪
          {ch | ¬ Pinning P Fq Dom S ch}) :=
          MeasureTheory.measure_mono hsubset
      _ ≤ (challengePMF P Fq Dom).toOuterMeasure
            ({ch | ¬ NodeHyp P Fq Dom ch} ∪
              {ch | ¬ LinearIndependent Fq (rowWeights P Fq Dom ch)}) +
          (challengePMF P Fq Dom).toOuterMeasure
            {ch | ¬ Pinning P Fq Dom S ch} := MeasureTheory.measure_union_le _ _
      _ ≤ ((challengePMF P Fq Dom).toOuterMeasure
            {ch | ¬ NodeHyp P Fq Dom ch} +
          (challengePMF P Fq Dom).toOuterMeasure
            {ch | ¬ LinearIndependent Fq (rowWeights P Fq Dom ch)}) +
          (challengePMF P Fq Dom).toOuterMeasure
            {ch | ¬ Pinning P Fq Dom S ch} := by
          gcongr
          exact MeasureTheory.measure_union_le _ _
      _ ≤ (ε₁ + ε₂) + ε₃ := by gcongr
      _ ≤ εZK P Fq := hsum
  · intro ch hch
    obtain ⟨hnode, hli, hpin⟩ := hch
    exact ⟨maskViewSection_of_rowSurj P Fq Dom S ch hmf hdom hbudget hnode
      (rowSurj_of_rowsLI P Fq Dom ch hli), hpin⟩

end ZkWhir
