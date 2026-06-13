/-
# Trusted base: zero-knowledge of the masked WHIR opening

Lean 4 statement of the definitions and main theorems of `misc/zk_leanVM.tex`:
the masked WHIR construction (`con:masked`), honest-verifier zero-knowledge
(`def:hvzk`), and the main results (`thm:simulator`, `cor:statzk`, with the
error bound of `cor:restart`).

**Proof status.** This development contains **no `sorry` and no axioms**: the
main theorems (`masked_whir_statistical_zk`, `masked_whir_perfect_on_good_set`)
are unconditionally machine-checked, by a chain that descends through the
probability layer (`Zkwhir.Probability`, fully proved), the mask-shift
bijection, and the linearity of the transcript, down to a single explicit
named hypothesis: `GoodSetAbsorption`, the linear-algebra core of the paper
(`prop:uniform` + `prop:pinbound` + `cor:restart`), **whose proof is complete
in `zk_leanVM.tex`** (via the new `lem:fullslice` and `lem:noother`) and whose
Lean transcription is the remaining formalization work. The definitions and
theorem statements are the trusted base: Lean cannot check that they match the
paper, so they must be audited by humans against `zk_leanVM.tex`.

## Modeling notes (audit checklist)

1. **Transcript.** The transcript contains the verifier challenges, the round-0
   prover messages (out-of-domain answers, sumcheck messages, query answers,
   `f₁` out-of-domain answers), and the *fully folded polynomial* `f̂₁`.
   In the real protocol the prover instead sends the oracle `f₁` and the later
   rounds continue; every later message is a deterministic public function of
   `f̂₁` and of later public coins (`lem:reduction`), so zero-knowledge for the
   transcript below implies zero-knowledge for the full opening. This is the
   one place where a protocol-level fact informs the statement.
2. **Sumcheck messages** are recorded as the evaluations `(ĥ_ℓ 0, ĥ_ℓ 1, ĥ_ℓ 2)`
   of the degree-≤ 2 message polynomial — an invertible re-encoding of its
   three coefficients.
3. **Query answers** are recorded as the per-class evaluations
   `û_s(pow(x, m))`; by locality of the fold these are a public linear
   bijection of the opened values of the fiber of `x` (`sec:setting`).
4. **Challenges** are sampled up front; for a public-coin protocol and honest
   parties this induces the same joint distribution as the interactive
   schedule. Queries are i.i.d. uniform in the domain (duplicates are allowed
   and answered identically).
5. **Coordinates.** A cell is a pair `(s, c)`: `s : Fin k₀ → Bool` the round-0
   coordinates in folding order (`s 0` is folded first) and `c : Fin m → Bool`
   the position coordinates, position coordinate `i` pairing with `x^(2^i)` in
   `pow`-evaluations. `R_out` is the half `s 0 = true`; the blocks are the last
   `2^a` positions of every class (`def:blocks`).
-/
import Mathlib
import Zkwhir.Probability

set_option linter.style.header false

noncomputable section

open scoped ENNReal

namespace ZkWhir

/- `statDist` (total-variation distance) and its lemmas live in
`Zkwhir.Probability`, fully proved. -/

/-! ## Multilinear tables -/

/-- The boolean hypercube with `j` coordinates. -/
abbrev Cube (j : ℕ) := Fin j → Bool

/-- Lagrange weight of the vertex `b` at the point `x`: the paper's `êq(x, b)`. -/
def eqPoly {R : Type*} [CommRing R] {j : ℕ} (x : Fin j → R) (b : Cube j) : R :=
  ∏ i, if b i then x i else 1 - x i

/-- Multilinear extension of a table of values on the hypercube. -/
def mle {R : Type*} [CommRing R] {j : ℕ} (T : Cube j → R) (x : Fin j → R) : R :=
  ∑ b, eqPoly x b * T b

/-- `powSeq z j = (z, z², z⁴, …, z^(2^(j−1)))` — the paper's `pow(z, j)`. -/
def powSeq {R : Type*} [CommRing R] (z : R) (j : ℕ) : Fin j → R :=
  fun i => z ^ (2 ^ (i : ℕ))

/-! ## Parameters and layout (`con:masked`) -/

/-- Protocol parameters; `n = k₀ + m` variables in folding order, and `s₀ = 2`
out-of-domain points at commitment are hardwired (`con:masked`, item 3). -/
structure Params where
  /-- size of the base field -/
  p : ℕ
  pPrime : p.Prime
  /-- number of round-0 (folding) variables -/
  k₀ : ℕ
  /-- number of position variables -/
  m : ℕ
  /-- log₂ of the block size -/
  a : ℕ
  /-- number of round-0 queries -/
  t₀ : ℕ
  /-- number of out-of-domain samples on `f̂₁` -/
  s₁ : ℕ
  k₀_pos : 0 < k₀
  /-- blocks fit inside a class -/
  a_le_m : a ≤ m

variable (P : Params)

instance : Fact P.p.Prime := ⟨P.pPrime⟩

/-- The base field `F_p`. -/
abbrev Fp := ZMod P.p

/-- A cell: class (round-0 coordinates) and position. -/
abbrev Cell := Cube P.k₀ × Cube P.m

/-- Numeric value of a position: coordinate `i` weighs `2^i` (the coordinate
paired with `x^(2^i)` in `pow`-evaluations). -/
def posVal {j : ℕ} (c : Cube j) : ℕ :=
  ∑ i, if c i then 2 ^ (i : ℕ) else 0

/-- Block positions: the last `2^a` positions of a class (`def:blocks`). -/
def IsBlockPos (c : Cube P.m) : Prop :=
  2 ^ P.m - 2 ^ P.a ≤ posVal c

instance : DecidablePred (IsBlockPos P) := fun _ => Nat.decLe _ _

/-- Mask cells (`con:masked`, item 2): `R_out` is the whole half `s 0 = true`,
and `R_in` is the block of every half `s 0 = false` class — equivalently, the
mask cells are the second half together with the last `2^a` positions of every
class. -/
def IsMask (u : Cell P) : Prop :=
  u.1 ⟨0, P.k₀_pos⟩ = true ∨ IsBlockPos P u.2

instance : DecidablePred (IsMask P) := fun u =>
  inferInstanceAs (Decidable (u.1 ⟨0, P.k₀_pos⟩ = true ∨ IsBlockPos P u.2))

/-- Data cells: the stacking and the zero padding (public constraints on them
are part of the statement, below). -/
abbrev DataCell := {u : Cell P // ¬ IsMask P u}

/-- Mask cells, as a type. -/
abbrev MaskCell := {u : Cell P // IsMask P u}

/-- An assignment of the data cells. -/
abbrev DataAssign := DataCell P → Fp P

/-- An assignment of the mask cells. -/
abbrev MaskAssign := MaskCell P → Fp P

/-- The committed table assembled from a data assignment and a mask assignment. -/
def assemble (data : DataAssign P) (mask : MaskAssign P) : Cell P → Fp P :=
  fun u => if h : IsMask P u then mask ⟨u, h⟩ else data ⟨u, h⟩

/-! ## The extension field and the statement -/

variable (Fq : Type*) [Field Fq] [Fintype Fq] [Algebra (Fp P) Fq]

/-- The extension field inherits the characteristic `p` of its prime subfield
`Fp P = ZMod P.p` (the algebra map is injective). This discharges the `CharP Fq p`
side-condition of the linearized-polynomial / `cond:twist` machinery (use via
`haveI := charP_Fq P Fq`). -/
theorem charP_Fq : CharP Fq P.p :=
  (Algebra.charP_iff (Fp P) Fq P.p).mp (ZMod.charP P.p)

/-- `q = |F_q|`. -/
def fieldCard : ℕ := Fintype.card Fq

/-- The extension degree `d = [F_q : F_p]` (`= 5` for KoalaBear). -/
def extDeg : ℕ := Module.finrank (Fp P) Fq

/-- The public statement of one masked opening: the input weight `ŵ` (by its
values on the hypercube), the publicly fixed data cells (public input and zero
padding), and the claimed value `σ`. -/
structure Stmt where
  /-- hypercube values of the input weight `ŵ` -/
  w : Cell P → Fq
  /-- the publicly fixed data cells -/
  pub : Finset (DataCell P)
  /-- their public values -/
  pubVal : DataCell P → Fp P
  /-- the claimed value -/
  σ : Fq

/-- A data assignment is consistent with the statement if it agrees with the
public cells and meets the claimed value `∑_u P[u]·ŵ(u) = σ` (the sum ranges
over the data cells; on mask cells the weight vanishes, see `MaskFree`). -/
def Consistent (S : Stmt P Fq) (data : DataAssign P) : Prop :=
  (∀ u ∈ S.pub, data u = S.pubVal u) ∧
  ∑ u : DataCell P, algebraMap (Fp P) Fq (data u) * S.w u.1 = S.σ

/-- The input weight vanishes on every mask cell ("the masks occupy cells where
every claim weight vanishes", `con:masked`). -/
def MaskFree (S : Stmt P Fq) : Prop :=
  ∀ u : Cell P, IsMask P u → S.w u = 0

/-- A *consistency difference* (`sec:simulator`): it vanishes on the public
cells and has zero weighted sum — the difference of two consistent data
assignments. -/
def ZeroConsistent (S : Stmt P Fq) (δ : DataAssign P) : Prop :=
  (∀ u ∈ S.pub, δ u = 0) ∧
  ∑ u : DataCell P, algebraMap (Fp P) Fq (δ u) * S.w u.1 = 0

/-- The difference of two consistent assignments is a consistency difference. -/
theorem Consistent.sub {S : Stmt P Fq} {data₁ data₂ : DataAssign P}
    (h₁ : Consistent P Fq S data₁) (h₂ : Consistent P Fq S data₂) :
    ZeroConsistent P Fq S (data₁ - data₂) := by
  constructor
  · intro u hu
    simp [Pi.sub_apply, h₁.1 u hu, h₂.1 u hu]
  · simp only [Pi.sub_apply, map_sub, sub_mul]
    rw [Finset.sum_sub_distrib, h₁.2, h₂.2, sub_self]

/-! ## Challenges -/

variable (Dom : Finset (Fp P))

/-- The verifier challenges of the masked opening, in protocol order: the two
commitment out-of-domain points, the batching challenge, the round-0 sumcheck
challenges (folding order), the out-of-domain points on `f̂₁`, and the queries. -/
structure Challenges where
  z : Fin 2 → Fq
  γ : Fq
  α : Fin P.k₀ → Fq
  zf : Fin P.s₁ → Fq
  qs : Fin P.t₀ → {x // x ∈ Dom}

variable [Nonempty {x // x ∈ Dom}]

/-- Uniform, independent challenges (modeling note 4). -/
def challengePMF : PMF (Challenges P Fq Dom) :=
  (PMF.uniformOfFintype (Fin 2 → Fq)).bind fun z =>
  (PMF.uniformOfFintype Fq).bind fun γ =>
  (PMF.uniformOfFintype (Fin P.k₀ → Fq)).bind fun α =>
  (PMF.uniformOfFintype (Fin P.s₁ → Fq)).bind fun zf =>
  (PMF.uniformOfFintype (Fin P.t₀ → {x // x ∈ Dom})).bind fun qs =>
  PMF.pure ⟨z, γ, α, zf, qs⟩

/-! ## The honest prover (`sec:setting`) -/

section Protocol

variable (S : Stmt P Fq) (T : Cell P → Fp P) (ch : Challenges P Fq Dom)

/-- The committed table, lifted to `F_q`. -/
def liftT : Cell P → Fq := fun u => algebraMap (Fp P) Fq (T u)

/-- Multilinear evaluation of the commitment at the point `(ys, xs)`
(class coordinates, position coordinates). -/
def evalT (ys : Fin P.k₀ → Fq) (xs : Fin P.m → Fq) : Fq :=
  ∑ u : Cell P, eqPoly ys u.1 * eqPoly xs u.2 * liftT P Fq T u

/-- Out-of-domain answer at `z`: the evaluation at `pow(z, n)`, which in folding
order is `(pow(z, k₀), pow(z^(2^k₀), m))` (`sec:setting`). -/
def oodAnswer (z : Fq) : Fq :=
  evalT P Fq T (powSeq z P.k₀) (powSeq (z ^ 2 ^ P.k₀) P.m)

/-- The batched weight `Ŵ₀ = êq(pow(z₁, n), ·) + γ·êq(pow(z₂, n), ·) + γ²·ŵ`
on the hypercube (`sec:twopoint`). -/
def W₀ : Cell P → Fq := fun u =>
  eqPoly (powSeq (ch.z 0) P.k₀) u.1 * eqPoly (powSeq (ch.z 0 ^ 2 ^ P.k₀) P.m) u.2
  + ch.γ * (eqPoly (powSeq (ch.z 1) P.k₀) u.1 *
      eqPoly (powSeq (ch.z 1 ^ 2 ^ P.k₀) P.m) u.2)
  + ch.γ ^ 2 * S.w u

/-- Partial evaluation of (the multilinear extension of) a table at the
round-`ℓ` mixed point: class coordinates `< ℓ` carry the sumcheck challenges,
coordinate `ℓ` carries `X`, class coordinates `> ℓ` carry the bits of `b`, and
the position carries the bits of `c`. (`ℓ` is 0-indexed: round `ℓ+1` of the
paper.) -/
def partialEval (G : Cell P → Fq) (ℓ : Fin P.k₀) (X : Fq) (b : Cube P.k₀)
    (c : Cube P.m) : Fq :=
  ∑ s : Cube P.k₀,
    (∏ i, if i < ℓ then (if s i then ch.α i else 1 - ch.α i)
          else if i = ℓ then (if s i then X else 1 - X)
          else (if s i = b i then 1 else 0)) * G (s, c)

/-- The round-`ℓ` sumcheck message polynomial
`ĥ_ℓ(X) = ∑_b f̂₀(α_{<ℓ}, X, b) · Ŵ₀(α_{<ℓ}, X, b)` (`sec:setting`).
The sum over `b : Cube k₀` is restricted to suffixes (`b i = false` for
`i ≤ ℓ`) so that each boolean suffix is counted exactly once. -/
def hPoly (ℓ : Fin P.k₀) (X : Fq) : Fq :=
  ∑ b : Cube P.k₀, ∑ c : Cube P.m,
    (if ∀ i ∈ Finset.Iic ℓ, b i = false then 1 else 0) *
      (partialEval P Fq Dom ch (liftT P Fq T) ℓ X b c *
       partialEval P Fq Dom ch (W₀ P Fq Dom S ch) ℓ X b c)

/-- The round-`ℓ` message: evaluations of `ĥ_ℓ` at `0, 1, 2` (modeling note 2). -/
def scMsg (ℓ : Fin P.k₀) : Fq × Fq × Fq :=
  (hPoly P Fq Dom S T ch ℓ 0, hPoly P Fq Dom S T ch ℓ 1, hPoly P Fq Dom S T ch ℓ 2)

/-- The folded polynomial after round 0: `f̂₁(c) = ∑_s êq(α, s) · f₀(s, c)`
(`sec:setting`). -/
def foldedF₁ : Cube P.m → Fq :=
  fun c => ∑ s, eqPoly ch.α s * liftT P Fq T (s, c)

/-- Out-of-domain answer on `f̂₁` at the point `zf j`. -/
def f₁OodAnswer (j : Fin P.s₁) : Fq :=
  mle (foldedF₁ P Fq Dom T ch) (powSeq (ch.zf j) P.m)

/-- Per-class answer at the query `x`: `û_s(pow(x, m))` (modeling note 3). -/
def queryAnswer (t : Fin P.t₀) (s : Cube P.k₀) : Fq :=
  mle (fun c => liftT P Fq T (s, c))
    (powSeq (algebraMap (Fp P) Fq (ch.qs t : Fp P)) P.m)

/-- The verifier's view of the masked opening (modeling notes 1–3). -/
structure Transcript where
  chal : Challenges P Fq Dom
  ood : Fin 2 → Fq
  msgs : Fin P.k₀ → Fq × Fq × Fq
  f₁Ood : Fin P.s₁ → Fq
  qAns : Fin P.t₀ → Cube P.k₀ → Fq
  f₁ : Cube P.m → Fq

/-- The honest prover's transcript on the committed table `T`, at fixed
challenges. -/
def transcriptOf : Transcript P Fq Dom where
  chal := ch
  ood := fun j => oodAnswer P Fq T (ch.z j)
  msgs := scMsg P Fq Dom S T ch
  f₁Ood := f₁OodAnswer P Fq Dom T ch
  qAns := queryAnswer P Fq Dom T ch
  f₁ := foldedF₁ P Fq Dom T ch

end Protocol

/-! ## The two transcript distributions -/

/-- The transcript distribution at *fixed* challenges: the masks are the only
randomness (`thm:simulator` lives at this level). -/
def transcriptGivenChallenges (S : Stmt P Fq) (data : DataAssign P)
    (ch : Challenges P Fq Dom) : PMF (Transcript P Fq Dom) :=
  (PMF.uniformOfFintype (MaskAssign P)).map fun mask =>
    transcriptOf P Fq Dom S (assemble P data mask) ch

/-- The honest transcript distribution: uniform challenges and uniform masks. -/
def honestTranscript (S : Stmt P Fq) (data : DataAssign P) :
    PMF (Transcript P Fq Dom) :=
  (challengePMF P Fq Dom).bind fun ch =>
    transcriptGivenChallenges P Fq Dom S data ch

/-! ## Linearity of the transcript in the committed table

Every transcript coordinate is additive in `T` (the weight `Ŵ₀` does not
depend on `T`, so even the sumcheck messages are linear). This is the formal
content of "the revealed values are linear forms on the cells" (`sec:setting`). -/

section Linearity

variable (S : Stmt P Fq) (ch : Challenges P Fq Dom)

theorem liftT_add (T₁ T₂ : Cell P → Fp P) :
    liftT P Fq (T₁ + T₂) = liftT P Fq T₁ + liftT P Fq T₂ := by
  funext u
  simp [liftT, Pi.add_apply, map_add]

theorem evalT_add (T₁ T₂ : Cell P → Fp P) (ys : Fin P.k₀ → Fq) (xs : Fin P.m → Fq) :
    evalT P Fq (T₁ + T₂) ys xs = evalT P Fq T₁ ys xs + evalT P Fq T₂ ys xs := by
  simp [evalT, liftT, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem oodAnswer_add (T₁ T₂ : Cell P → Fp P) (z : Fq) :
    oodAnswer P Fq (T₁ + T₂) z = oodAnswer P Fq T₁ z + oodAnswer P Fq T₂ z := by
  unfold oodAnswer
  rw [evalT_add]

theorem partialEval_add (G₁ G₂ : Cell P → Fq) (ℓ : Fin P.k₀) (X : Fq)
    (b : Cube P.k₀) (c : Cube P.m) :
    partialEval P Fq Dom ch (G₁ + G₂) ℓ X b c =
      partialEval P Fq Dom ch G₁ ℓ X b c + partialEval P Fq Dom ch G₂ ℓ X b c := by
  simp [partialEval, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hPoly_add (T₁ T₂ : Cell P → Fp P) (ℓ : Fin P.k₀) (X : Fq) :
    hPoly P Fq Dom S (T₁ + T₂) ch ℓ X =
      hPoly P Fq Dom S T₁ ch ℓ X + hPoly P Fq Dom S T₂ ch ℓ X := by
  simp only [hPoly, liftT_add, partialEval_add, add_mul, mul_add,
    Finset.sum_add_distrib]

theorem foldedF₁_add (T₁ T₂ : Cell P → Fp P) :
    foldedF₁ P Fq Dom (T₁ + T₂) ch =
      foldedF₁ P Fq Dom T₁ ch + foldedF₁ P Fq Dom T₂ ch := by
  funext c
  simp [foldedF₁, liftT, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem queryAnswer_add (T₁ T₂ : Cell P → Fp P) (t : Fin P.t₀) (s : Cube P.k₀) :
    queryAnswer P Fq Dom (T₁ + T₂) ch t s =
      queryAnswer P Fq Dom T₁ ch t s + queryAnswer P Fq Dom T₂ ch t s := by
  simp [queryAnswer, mle, liftT, Pi.add_apply, map_add, mul_add,
    Finset.sum_add_distrib]

/-- A difference table `Δ` is *invisible* at the challenges `ch` if every
transcript coordinate vanishes on it: out-of-domain answers, fresh sumcheck
contributions, query answers, and the fold. This is the formal counterpart of
`Δ ∈ ker(L_view) ∩ (kernel of the fold relation)` from `sec:simulator` —
except that here the *whole* fold must vanish, since the transcript exposes
`f̂₁` in full. -/
structure Invisible (Δ : Cell P → Fp P) : Prop where
  ood : ∀ j, oodAnswer P Fq Δ (ch.z j) = 0
  msg0 : ∀ ℓ, hPoly P Fq Dom S Δ ch ℓ 0 = 0
  msg1 : ∀ ℓ, hPoly P Fq Dom S Δ ch ℓ 1 = 0
  msg2 : ∀ ℓ, hPoly P Fq Dom S Δ ch ℓ 2 = 0
  qa : ∀ t s, queryAnswer P Fq Dom Δ ch t s = 0
  fold : foldedF₁ P Fq Dom Δ ch = 0

/-- Adding an invisible table does not change the transcript. -/
theorem transcriptOf_add_invisible (T Δ : Cell P → Fp P)
    (hinv : Invisible P Fq Dom S ch Δ) :
    transcriptOf P Fq Dom S (T + Δ) ch = transcriptOf P Fq Dom S T ch := by
  unfold transcriptOf
  simp only [Transcript.mk.injEq]
  refine ⟨trivial, ?_, ?_, ?_, ?_, ?_⟩
  · funext j
    rw [oodAnswer_add, hinv.ood j, add_zero]
  · funext ℓ
    unfold scMsg
    rw [hPoly_add, hPoly_add, hPoly_add, hinv.msg0 ℓ, hinv.msg1 ℓ, hinv.msg2 ℓ,
      add_zero, add_zero, add_zero]
  · funext j
    unfold f₁OodAnswer
    rw [foldedF₁_add, hinv.fold, add_zero]
  · funext t s
    rw [queryAnswer_add, hinv.qa t s, add_zero]
  · rw [foldedF₁_add, hinv.fold, add_zero]

/-- If the difference of two assembled tables is invisible, the transcripts
coincide for every mask: the data difference has been absorbed into the mask
shift `μ`. -/
theorem transcriptOf_eq_of_invisible (data₁ data₂ : DataAssign P)
    (μ : MaskAssign P)
    (hinv : Invisible P Fq Dom S ch (assemble P (data₁ - data₂) (-μ))) :
    ∀ mask : MaskAssign P,
      transcriptOf P Fq Dom S (assemble P data₁ mask) ch =
      transcriptOf P Fq Dom S (assemble P data₂ (mask + μ)) ch := by
  intro mask
  have hT : assemble P data₁ mask =
      assemble P data₂ (mask + μ) + assemble P (data₁ - data₂) (-μ) := by
    funext u
    by_cases h : IsMask P u <;>
      simp [assemble, h, Pi.add_apply, Pi.sub_apply, Pi.neg_apply] <;> ring
  rw [hT]
  exact transcriptOf_add_invisible P Fq Dom S ch _ _ hinv

end Linearity

/-! ## The zero-knowledge error (`cor:restart`) -/

/-- The zero-knowledge error: the union bound over degenerate challenges.
Terms, in order: \textsc{spread} (`lem:spread`); the two-point rank conditions
(`cor:twopointprob`); node genericity (`lem:nodeprob`); twist rigidity
(`cor:twistprob`); cross coupling (`cond:cross2`). For KoalaBear parameters
this is `≈ 2^(−122)`. -/
def εZK : ℝ≥0∞ :=
  let p : ℝ≥0∞ := (P.p : ℝ≥0∞)
  let q : ℝ≥0∞ := (fieldCard Fq : ℝ≥0∞)
  let d : ℕ := extDeg P Fq
  let e : ℕ := P.k₀ - d + 1
  let B : ℝ≥0∞ := ((P.k₀ - 1).choose e : ℝ≥0∞)
  -- spread
  (1 / q + B * (p / q) ^ e)
  -- two-point rank
  + ((4 * 2 ^ P.k₀ + 2 * P.k₀ : ℕ) : ℝ≥0∞) / q
  -- node genericity
  + ((2 + P.s₁ : ℕ) : ℝ≥0∞) * p / q
  + (((2 + P.s₁).choose 2 * d * 2 ^ P.k₀ : ℕ) : ℝ≥0∞) / q
  -- twist rigidity
  + (p / q + 2 * B * (p ^ (d - 2) / q) ^ e)
  -- cross coupling
  + ((2 ^ (P.k₀ + 7) : ℕ) : ℝ≥0∞) / q
  -- slice conditions (`lem:fullslice`: SPREAD-2 and the two-level moment
  -- system; `lem:noother`: slice-table independence)
  + ((d - 1 : ℕ) : ℝ≥0∞) * p / q
  + ((4 * P.k₀ : ℕ) : ℝ≥0∞) / q
  + ((2 ^ (P.k₀ + 2) : ℕ) : ℝ≥0∞) / q

/-! ## Main theorems -/

section MainTheorems

variable (S : Stmt P Fq)

/-- `def:hvzk`, specialized to the masked opening: `sim` is an `ε`-simulator if
its output is within statistical distance `ε` of the honest transcript of
*every* consistent data assignment. (The simulator is quantified first: there
is one simulator for all witnesses.) -/
def IsSimulator (sim : PMF (Transcript P Fq Dom)) (ε : ℝ≥0∞) : Prop :=
  ∀ data : DataAssign P, Consistent P Fq S data →
    statDist (honestTranscript P Fq Dom S data) sim ≤ ε

/-- Standing hypotheses of the paper's analysis: the parameter conditions of
`zk_leanVM.tex` (mask budget of `con:masked`; field conditions of
`sec:toolbox`, `lem:spread`, `lem:nodeprob`; queried points are nonzero,
`prop:uniform`; the slice conditions of `lem:fullslice` and `lem:noother`).
These are what the paper proof of `GoodSetAbsorption` consumes; they will
become hypotheses of its Lean proof. -/
structure Hyp : Prop where
  /-- the input weight vanishes on the masks -/
  maskFree : MaskFree P Fq S
  /-- the mask budget `2^a ≥ t₀ + d(s₀ + s₁)` -/
  budget : P.t₀ + extDeg P Fq * (2 + P.s₁) ≤ 2 ^ P.a
  /-- the extension degree is prime -/
  dPrime : (extDeg P Fq).Prime
  /-- the extension degree is odd (`= 5` for KoalaBear). Needed for the
  exact node count of `lem:nodeprob`: the cofactor `(q−1)/(p−1)` must be
  odd — for even degree the set `{z : z^(2^k₀) ∈ F_p}` is strictly larger
  than `p` and the `(s₀+s₁)·p/q` term would not hold. -/
  dOdd : Odd (extDeg P Fq)
  /-- enough folding variables: `k₀ ≥ d` -/
  d_le_k₀ : extDeg P Fq ≤ P.k₀
  /-- `2^k₀` divides `p − 1` -/
  two_pow_dvd : 2 ^ P.k₀ ∣ P.p - 1
  /-- queried points are nonzero -/
  dom_ne_zero : (0 : Fp P) ∉ Dom
  /-- enough folding variables for the slice argument (`lem:fullslice`):
  `k₀ ≥ d + 2` (met exactly by KoalaBear: `7 = 5 + 2`) -/
  d_add_two_le_k₀ : extDeg P Fq + 2 ≤ P.k₀
  /-- the data slices of `ŵ` at the top two class coordinates are not
  proportional (`lem:noother`; rank-one weight data genuinely breaks the
  argument) -/
  slices_indep : ∀ L : Fin P.k₀,
    ((L : ℕ) + 1 = P.k₀ ∨ (L : ℕ) + 2 = P.k₀) →
    ¬ ∃ κ : Fq, ∀ (s : Cube P.k₀) (c : Cube P.m),
      S.w (Function.update s L true, c) = κ * S.w (Function.update s L false, c)

/-- **The good-set absorption property — the single interface to the paper.**
On a good set of challenge tuples of probability at least `1 − εZK`, every
consistency difference of data assignments extends, by a suitable mask
correction `μ`, to a table that is invisible to the transcript.

**Status: proved on paper, transcription pending.** This proposition is
exactly the conjunction of `prop:uniform`, `lem:kersurj`, and `cond:pinning`
via `prop:pinbound` — whose two formerly open steps are now closed by
`lem:fullslice` (the slice statement, via the `(ℓ,y)`-family of channel
identities and the θ-uniform two-level moment representation) and
`lem:noother` (fold-table confinement and point-mass elimination) — together
with the probability accounting of `cor:restart`, all in `zk_leanVM.tex` with
complete proofs. It enters the theorems below as an explicit named hypothesis
rather than a `sorry`, so that everything machine-checked in this development
is unconditionally machine-checked, and the human-audited bridge to the paper
is visible in every statement that uses it. Its Lean proof (CRT, the
staircase/chain machinery of `Zkwhir.Toolbox`, `prop:uniform`, and the
pinning analysis) is the remaining formalization work. -/
def GoodSetAbsorption (S : Stmt P Fq) : Prop :=
  ∃ Good : Set (Challenges P Fq Dom),
    (challengePMF P Fq Dom).toOuterMeasure Goodᶜ ≤ εZK P Fq ∧
    ∀ ch ∈ Good, ∀ δ : DataAssign P, ZeroConsistent P Fq S δ →
      ∃ μ : MaskAssign P,
        Invisible P Fq Dom S ch (assemble P δ (-μ))

/-- On the good set, any consistent data difference can be absorbed into a
shift of the masks without changing the transcript (from `good_set_invisible`
and the transcript linearity of `transcriptOf_eq_of_invisible`). -/
theorem good_set_absorbs (habs : GoodSetAbsorption P Fq Dom S) :
    ∃ Good : Set (Challenges P Fq Dom),
      (challengePMF P Fq Dom).toOuterMeasure Goodᶜ ≤ εZK P Fq ∧
      ∀ ch ∈ Good, ∀ data₁ data₂ : DataAssign P,
        Consistent P Fq S data₁ → Consistent P Fq S data₂ →
          ∃ μshift : MaskAssign P, ∀ mask : MaskAssign P,
            transcriptOf P Fq Dom S (assemble P data₁ mask) ch =
            transcriptOf P Fq Dom S (assemble P data₂ (mask + μshift)) ch := by
  obtain ⟨Good, hGood, hinv⟩ := habs
  refine ⟨Good, hGood, fun ch hch data₁ data₂ h₁ h₂ => ?_⟩
  obtain ⟨μ, hμ⟩ := hinv ch hch (data₁ - data₂) (Consistent.sub P Fq h₁ h₂)
  exact ⟨μ, transcriptOf_eq_of_invisible P Fq Dom S ch data₁ data₂ μ hμ⟩

/-- **Perfect simulation on a good set** (`thm:simulator` + `cor:restart`):
there is a set of challenge tuples, determined by the statement alone, of
probability at least `1 − εZK`, on which the transcript distribution (over the
masks) does not depend on the consistent data assignment at all.

Proof: absorb the data difference into a mask shift (`good_set_absorbs`); the
shift is a bijection of the mask space, and the uniform distribution is
invariant under it. -/
theorem masked_whir_perfect_on_good_set (habs : GoodSetAbsorption P Fq Dom S) :
    ∃ Good : Set (Challenges P Fq Dom),
      (challengePMF P Fq Dom).toOuterMeasure Goodᶜ ≤ εZK P Fq ∧
      ∀ ch ∈ Good, ∀ data₁ data₂ : DataAssign P,
        Consistent P Fq S data₁ → Consistent P Fq S data₂ →
          transcriptGivenChallenges P Fq Dom S data₁ ch =
          transcriptGivenChallenges P Fq Dom S data₂ ch := by
  obtain ⟨Good, hGood, habs⟩ := good_set_absorbs P Fq Dom S habs
  refine ⟨Good, hGood, fun ch hch data₁ data₂ h₁ h₂ => ?_⟩
  obtain ⟨μshift, hshift⟩ := habs ch hch data₁ data₂ h₁ h₂
  unfold transcriptGivenChallenges
  have key : (fun mask => transcriptOf P Fq Dom S (assemble P data₁ mask) ch) =
      (fun mask => transcriptOf P Fq Dom S (assemble P data₂ mask) ch) ∘
        (fun mask => mask + μshift) := by
    funext mask
    exact hshift mask
  rw [key, ← PMF.map_comp]
  congr 1
  exact map_equiv_uniformOfFintype (Equiv.addRight μshift)

/-- **Statistical honest-verifier zero-knowledge** (`thm:main`, `cor:statzk`):
the honest prover run on any consistent data assignment `dataStar` — one is
computable from the statement alone — is an `εZK`-simulator for every
consistent data assignment.

Proof: condition on the good set of `masked_whir_perfect_on_good_set`; on it
the two transcript kernels agree, and the complement has probability at most
`εZK` (`statDist_bind_le_of_eqOn`). -/
theorem masked_whir_statistical_zk (habs : GoodSetAbsorption P Fq Dom S)
    (dataStar : DataAssign P) (hStar : Consistent P Fq S dataStar) :
    IsSimulator P Fq Dom S
      (honestTranscript P Fq Dom S dataStar) (εZK P Fq) := by
  obtain ⟨Good, hGood, heq⟩ := masked_whir_perfect_on_good_set P Fq Dom S habs
  intro data hdata
  unfold honestTranscript
  refine (statDist_bind_le_of_eqOn (challengePMF P Fq Dom)
    (transcriptGivenChallenges P Fq Dom S data)
    (transcriptGivenChallenges P Fq Dom S dataStar) Good ?_).trans hGood
  intro ch hch
  exact heq ch hch data dataStar hdata hStar

end MainTheorems

end ZkWhir
