/-
The absorption assembly (`thm:simulator`'s engine, in primal form): at
challenges satisfying the two structural predicates — the masked view
section (`prop:uniform`) and pinning (`cond:pinning`, established in the
paper via `lem:fullslice`/`lem:noother`) — every consistency difference of
data assignments is absorbed by a mask shift, invisibly to the transcript.

The construction: match the reduced view of `δ` by a mask `μ₁`
(`MaskViewSection`); the residual fold of `δ − μ₁` is then killed by the
protocol directions (fold consistency, `f̂₁` out-of-domain duals, the
terminal pairing — all proved in `Zkwhir.Channel`), so pinning provides a
view-invisible mask `κ` whose fold cancels it; `μ := μ₁ + κ` absorbs `δ`.

This reduces `GoodSetAbsorption` to producing a good set of challenges on
which the two predicates hold, with the failure probability bounded by
`εZK` (steps 5–6 of the campaign).

Part of the `GoodSetAbsorption` formalization campaign.
-/
import Mathlib
import Zkwhir.Statement
import Zkwhir.Sumcheck
import Zkwhir.Channel

set_option linter.style.header false
set_option linter.unusedSectionVars false

noncomputable section

namespace ZkWhir

variable (P : Params) (Fq : Type*) [Field Fq] [Fintype Fq]
  [Algebra (Fp P) Fq] (Dom : Finset (Fp P)) [Nonempty {x // x ∈ Dom}]

variable (S : Stmt P Fq) (ch : Challenges P Fq Dom)

/-- The *reduced view* of a perturbation vanishes: every transcript
coordinate except the fold itself — out-of-domain answers, all three values
of every sumcheck message, query answers, and the out-of-domain answers on
`f̂₁` (the `L_view` of `sec:simulator`). -/
structure ViewVanishes (Δ : Cell P → Fp P) : Prop where
  ood : ∀ j, oodAnswer P Fq Δ (ch.z j) = 0
  msg1 : ∀ ℓ, hPoly P Fq Dom S Δ ch ℓ 1 = 0
  msg2 : ∀ ℓ, hPoly P Fq Dom S Δ ch ℓ 2 = 0
  qa : ∀ t s, queryAnswer P Fq Dom Δ ch t s = 0
  f1ood : ∀ j, mle (foldedF₁ P Fq Dom Δ ch) (powSeq (ch.zf j) P.m) = 0

/-- **The masked view section** (`prop:uniform`, consumable form): the masks
reach the reduced view of every data assignment. On the good set this holds
via the block solver (`exists_block_fiber`) and the node-matrix rank
(`thm:twopoint`); at this stage of the campaign it is a named Good-set
predicate. -/
def MaskViewSection : Prop :=
  ∀ δ : DataAssign P, ZeroConsistent P Fq S δ → ∃ μ : MaskAssign P,
    ViewVanishes P Fq Dom S ch (assemble P δ (-μ))

/-- **Pinning** (`cond:pinning`, primal form): every fold table killed by
the protocol directions — the queried-point duals, the `f̂₁` out-of-domain
duals, and the terminal pairing against the folded weight — is (up to sign)
the fold of a mask perturbation with vanishing reduced view. This is
`ann(W') = protocol directions`, consumed in the direction the simulator
needs; it is the content of `prop:pinbound` via `lem:fullslice` and
`lem:noother`. -/
def Pinning : Prop :=
  ∀ F : Cube P.m → Fq,
    (∀ t, mle F (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0) →
    (∀ j, mle F (powSeq (ch.zf j) P.m) = 0) →
    (∑ c, F c * ∑ s, eqPoly ch.α s * W₀ P Fq Dom S ch (s, c) = 0) →
    ∃ κ : MaskAssign P,
      ViewVanishes P Fq Dom S ch (assemble P 0 (-κ)) ∧
      foldedF₁ P Fq Dom (assemble P 0 (-κ)) ch = fun c => - F c

/-- The `ŵ`-pairing of an assembled table reads only the data cells. -/
theorem pairing_assemble (hmf : MaskFree P Fq S) (δ : DataAssign P)
    (mask : MaskAssign P) :
    ∑ u : Cell P, liftT P Fq (assemble P δ mask) u * S.w u =
      ∑ u : DataCell P, algebraMap (Fp P) Fq (δ u) * S.w u.1 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun u : Cell P => IsMask P u)
    (fun u => liftT P Fq (assemble P δ mask) u * S.w u)]
  have hmask : ∑ u ∈ Finset.univ.filter (fun u : Cell P => IsMask P u),
      liftT P Fq (assemble P δ mask) u * S.w u = 0 :=
    Finset.sum_eq_zero fun u hu => by
      rw [hmf u (Finset.mem_filter.mp hu).2, mul_zero]
  rw [hmask, zero_add]
  have hsub := Finset.sum_subtype (p := fun u : Cell P => ¬ IsMask P u)
    (F := inferInstance)
    (Finset.univ.filter (fun u : Cell P => ¬ IsMask P u))
    (fun u => by simp)
    (fun u => liftT P Fq (assemble P δ mask) u * S.w u)
  rw [hsub]
  refine Finset.sum_congr rfl fun u _ => ?_
  congr 1
  show algebraMap (Fp P) Fq (assemble P δ mask u.1) =
    algebraMap (Fp P) Fq (δ u)
  congr 1
  unfold assemble
  rw [dif_neg u.2]

/-- **The absorption assembly**: under the two structural predicates, every
consistency difference extends, by a mask correction, to a table invisible
to the transcript — the conclusion `GoodSetAbsorption` demands pointwise on
the good set. -/
theorem absorption_of_predicates (h2 : (2 : Fq) ≠ 0) (hmf : MaskFree P Fq S)
    (hsec : MaskViewSection P Fq Dom S ch) (hpin : Pinning P Fq Dom S ch)
    (δ : DataAssign P) (hδ : ZeroConsistent P Fq S δ) :
    ∃ μ : MaskAssign P, Invisible P Fq Dom S ch (assemble P δ (-μ)) := by
  classical
  obtain ⟨μ₁, hv₁⟩ := hsec δ hδ
  have hw₁ : ∑ u : Cell P, liftT P Fq (assemble P δ (-μ₁)) u * S.w u = 0 := by
    rw [pairing_assemble P Fq S hmf δ (-μ₁)]
    exact hδ.2
  have hmsg0₁ := msg0_of_reduced_view P Fq Dom S ch h2 (assemble P δ (-μ₁))
    hv₁.ood hv₁.msg1 hv₁.msg2 hw₁
  -- the residual fold is killed by the protocol directions
  have hF1 : ∀ t, mle (foldedF₁ P Fq Dom (assemble P δ (-μ₁)) ch)
      (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) = 0 := by
    intro t
    rw [mle_fold_eq_sum_classes P Fq Dom (assemble P δ (-μ₁)) ch]
    refine Finset.sum_eq_zero fun s _ => ?_
    have hq := hv₁.qa t s
    rw [show mle (fun c => liftT P Fq (assemble P δ (-μ₁)) (s, c))
        (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m) =
        queryAnswer P Fq Dom (assemble P δ (-μ₁)) ch t s from rfl, hq,
      mul_zero]
  have hF3 : ∑ c, foldedF₁ P Fq Dom (assemble P δ (-μ₁)) ch c *
      ∑ s, eqPoly ch.α s * W₀ P Fq Dom S ch (s, c) = 0 :=
    terminal_pairing_eq_zero_of_msgs P Fq Dom S (assemble P δ (-μ₁)) ch h2
      hmsg0₁ hv₁.msg1 hv₁.msg2
  obtain ⟨κ, hvκ, hfκ⟩ := hpin (foldedF₁ P Fq Dom (assemble P δ (-μ₁)) ch)
    hF1 hv₁.f1ood hF3
  refine ⟨μ₁ + κ, ?_⟩
  have htab : assemble P δ (-(μ₁ + κ)) =
      assemble P δ (-μ₁) + assemble P 0 (-κ) := by
    funext u
    by_cases h : IsMask P u
    · simp only [assemble, dif_pos h, Pi.add_apply, Pi.neg_apply]
      ring
    · simp only [assemble, dif_neg h, Pi.add_apply, Pi.zero_apply, add_zero]
  rw [htab]
  refine invisible_of_view_vanishing P Fq Dom S ch h2 _ ?_ ?_ ?_ ?_ ?_ ?_
  · intro j
    rw [oodAnswer_add, hv₁.ood j, hvκ.ood j, add_zero]
  · intro ℓ
    rw [hPoly_add, hv₁.msg1 ℓ, hvκ.msg1 ℓ, add_zero]
  · intro ℓ
    rw [hPoly_add, hv₁.msg2 ℓ, hvκ.msg2 ℓ, add_zero]
  · intro t s
    rw [queryAnswer_add, hv₁.qa t s, hvκ.qa t s, add_zero]
  · rw [foldedF₁_add, hfκ]
    funext c
    simp
  · have hsplit : ∀ u : Cell P,
        liftT P Fq (assemble P δ (-μ₁) + assemble P 0 (-κ)) u * S.w u =
        liftT P Fq (assemble P δ (-μ₁)) u * S.w u +
          liftT P Fq (assemble P 0 (-κ)) u * S.w u := by
      intro u
      rw [liftT_add, Pi.add_apply]
      ring
    calc ∑ u : Cell P,
        liftT P Fq (assemble P δ (-μ₁) + assemble P 0 (-κ)) u * S.w u
        = ∑ u : Cell P, (liftT P Fq (assemble P δ (-μ₁)) u * S.w u +
            liftT P Fq (assemble P 0 (-κ)) u * S.w u) :=
          Finset.sum_congr rfl fun u _ => hsplit u
      _ = (∑ u : Cell P, liftT P Fq (assemble P δ (-μ₁)) u * S.w u) +
            ∑ u : Cell P, liftT P Fq (assemble P 0 (-κ)) u * S.w u :=
          Finset.sum_add_distrib
      _ = 0 := by
          rw [pairing_assemble P Fq S hmf δ (-μ₁),
            pairing_assemble P Fq S hmf 0 (-κ), hδ.2]
          simp

/-- The field is not of characteristic two: `2^k₀ ∣ p − 1` with `k₀ > 0`
forces `p` odd, and the base field embeds. Discharges the `h2` hypotheses
from `Hyp.two_pow_dvd`. -/
theorem two_ne_zero_of_two_pow_dvd (hdvd : 2 ^ P.k₀ ∣ P.p - 1) :
    (2 : Fq) ≠ 0 := by
  have hp := P.pPrime
  have hne2 : P.p ≠ 2 := by
    intro h2
    rw [h2] at hdvd
    have hle := Nat.le_of_dvd one_pos hdvd
    have h2k : 2 ^ 1 ≤ 2 ^ P.k₀ :=
      Nat.pow_le_pow_right (by norm_num) P.k₀_pos
    simp at h2k
    omega
  have h2p : (2 : Fp P) ≠ 0 := by
    have hcast : ((2 : ℕ) : ZMod P.p) ≠ 0 := by
      rw [Ne, CharP.cast_eq_zero_iff (ZMod P.p) P.p 2]
      intro hdvd2
      have hle := Nat.le_of_dvd (by norm_num) hdvd2
      have h2le := hp.two_le
      omega
    simpa using hcast
  intro h2q
  apply h2p
  apply (algebraMap (Fp P) Fq).injective
  rw [map_ofNat, map_zero]
  exact h2q

/-- **Step-7 packaging**: a good set on which the two structural predicates
hold, with complement of measure at most `εZK`, yields `GoodSetAbsorption`.
What remains of the campaign is to produce such a set (steps 5–6). -/
theorem goodSetAbsorption_of_predicates (h2 : (2 : Fq) ≠ 0)
    (hmf : MaskFree P Fq S) (Good : Set (Challenges P Fq Dom))
    (hmeas : (challengePMF P Fq Dom).toOuterMeasure Goodᶜ ≤ εZK P Fq)
    (hpred : ∀ ch ∈ Good,
      MaskViewSection P Fq Dom S ch ∧ Pinning P Fq Dom S ch) :
    GoodSetAbsorption P Fq Dom S :=
  ⟨Good, hmeas, fun ch hch δ hδ =>
    absorption_of_predicates P Fq Dom S ch h2 hmf
      (hpred ch hch).1 (hpred ch hch).2 δ hδ⟩

end ZkWhir
