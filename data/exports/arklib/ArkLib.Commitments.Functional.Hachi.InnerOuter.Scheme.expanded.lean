/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
module

public import ArkLib.Commitments.Ordinary.Ajtai.Simple.Scheme
public import ArkLib.Commitments.Functional.Hachi.Gadget.Core
public import ArkLib.Data.Lattices.CyclotomicRing.NormBounds


-- @@ L12-82 verbatim
/-!
# Inner-Outer Ajtai Commitment Scheme

The Greyhound [NS24] / Hachi [NOZ26] inner-outer commitment composition over the cyclotomic
ring `Rq Φ`:
each message block is gadget-decomposed and inner-committed under `A`; the inner
commitments are gadget-decomposed, flattened, and outer-committed under `B`.

This file defines the scheme itself (public parameters, openings, commit, verify). Perfect
correctness is proved in `InnerOuter/Correctness.lean`, and the weak-binding reduction to
Module-SIS in `InnerOuter/Security.lean`.

## Weak openings

Following Hachi [NOZ26, §4.1], the opening carried by this scheme is a *weak opening*
`(sᵢ, t̂ᵢ, cᵢ)ᵢ`: per block `i` a (gadget-decomposed) message `sᵢ`, an inner decomposition
`t̂ᵢ`, and a *challenge* `cᵢ`. The challenge originates as the verifier's challenge in the
evaluation/opening protocol and is only ever recovered during knowledge extraction; it is not
something the committer chooses. We reflect this in the types: the committer-produced data
`(sᵢ, t̂ᵢ)` is the `Decomp` structure, and an `Opening` extends `Decomp` with the challenge.
The honest committer generates only the `Decomp` (`generateDecomps`); `commitmentScheme` pairs
it with the trivial challenge `cᵢ = 1`, the special case in which weak verification
(`verify_weak`) collapses to the ordinary honest check (`1` is invertible, `‖1‖₁ = 1`, and
`‖1·sᵢ‖ = ‖sᵢ‖`).

`verify_weak` checks, per block: the challenge is nonzero and `ℓ₁`-bounded (`0 < ‖cᵢ‖₁ ≤ κ`),
the scaled message is `ℓ₂²`-short (`‖cᵢ·sᵢ‖₂² ≤ βSq`), and the inner gadget relation
`A sᵢ = G t̂ᵢ` holds; and globally: the flattened inner decomposition is `ℓ∞`-short
(`‖t̂‖∞ ≤ γ`, matching Hachi [NOZ26, §4.1]) and outer-commits to `u`. Because the norms
`Rq.l1Norm`/`vecL2NormSq`/`vecLInftyNorm` are defined over `ZMod q`, `verify_weak` and the
bundled `commitmentScheme` live in the `ZMod q` section.

## The challenge condition `0 < ‖cᵢ‖₁` and invertibility

Hachi's weak opening [NOZ26, §4.1] requires the (extracted) challenge `cᵢ` to be *invertible*
in `Rq Φ` (`c̄ᵢ ∈ R_q^×`). We check the weaker `0 < ‖cᵢ‖₁` (i.e. `cᵢ ≠ 0`) here because
invertibility is not an independent hypothesis: it is a *consequence* of the shortness bound
`‖cᵢ‖₁ ≤ κ` via the Lyubashevsky–Seiler lemma [LS18] (short elements of `Rq Φ` are invertible,
formalized as `isUnit_of_l1Norm_le`). For `q ≡ 5 (mod 8)` and `κ` below the LS18 threshold, any
nonzero `cᵢ` with `‖cᵢ‖₁ ≤ κ` is automatically a unit, so the explicit nonzero check together
with the `ℓ₁` bound already pins down invertibility. The honest challenge `cᵢ = 1` is a unit.

## Deriving the message from a weak opening

A weak opening does not store the message: per Hachi [NOZ26, Eq. (13)] the message block is
*derived* from `sᵢ` by applying the message gadget matrix, `mᵢ = G · sᵢ` (`derivedMessage`).
The bundled `commitmentScheme` therefore verifies an opening against a claimed message `m` by
checking `derivedMessage opening.toDecomp = m` together with `verify_weak`.

## Main definitions

* `PublicParams`: the two Ajtai matrices, inner `A` and outer `B`.
* `Decomp` / `Opening`: the committer-produced decomposition data `(sᵢ, t̂ᵢ)`, and its extension
  with per-block challenges `(cᵢ)` forming a weak opening.
* `Decomposition` / `Decomposition.ofDigits`: the decomposition operations used by the honest
  committer, instantiated with the base-`b` gadget inverse `G⁻¹` at both steps.
* `derivedMessage`: recovers the message block `mᵢ = G · sᵢ` from the decomposition data.
* `generateDecomps` / `commitWithDecomps`: honest decomposition generation and the outer
  commitment computed from it.
* `verify_weak`: the weak-opening verifier (challenge, shortness, and gadget-relation checks).
* `commitmentScheme`: the scheme bundled as a `CommitmentScheme`, with honest challenge
  `cᵢ = 1`.

## References

* [Lyubashevsky, V., and Seiler, G., *Short, Invertible Elements in Partially Splitting
    Cyclotomic Rings*][LS18]
* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/


-- @@ L84-84 verbatim
@[expose] public section


-- @@ L86-87 verbatim
open OracleComp CommitmentScheme CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
  ArkLib.Lattices.Ajtai


-- @@ L89-89 verbatim
namespace ArkLib.Lattices.Ajtai.InnerOuter


-- @@ L91-91 verbatim
section Defs


-- @@ L93-93 verbatim
variable {R : Type} [Field R] [BEq R] [LawfulBEq R] (Φ : CyclotomicModulus R) [IsCyclotomic Φ]

-- @@ L94-94 verbatim
variable {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}


-- @@ L96-100 verbatim
/-- Public parameters: inner Ajtai matrix `A` and outer Ajtai matrix `B`. -/
structure PublicParams (Φ : CyclotomicModulus R)
    (innerRows messageRows messageDigits outerRows blocks innerDigits : Nat) where
  /-- Inner Ajtai matrix `A`. -/
  innerMatrix : Simple.PublicParams Φ innerRows (messageRows * messageDigits)
  
-- @@ L101-102 verbatim
/-- Outer Ajtai matrix `B`. -/
  outerMatrix : Simple.PublicParams Φ outerRows (blocks * (innerRows * innerDigits))


-- @@ L104-110 verbatim
/-- The decomposition data `(sᵢ, t̂ᵢ)ᵢ` underlying an opening, *without* the challenge:
per-block gadget-decomposed messages `(sᵢ)` and inner decompositions `(t̂ᵢ)`. This is what the
honest committer produces (`generateDecomps`); a weak `Opening` extends it with a challenge. -/
structure Decomp (Φ : CyclotomicModulus R)
    (innerRows messageRows messageDigits blocks innerDigits : Nat) where
  /-- Per-block (gadget-decomposed) messages `(sᵢ)`. -/
  message : PolyVec (PolyVec (Rq Φ) (messageRows * messageDigits)) blocks
  
-- @@ L111-112 verbatim
/-- Per-block inner decompositions `(t̂ᵢ)`. -/
  innerDecomp : PolyVec (PolyVec (Rq Φ) (innerRows * innerDigits)) blocks


-- @@ L114-122 verbatim
/-- A Hachi/Greyhound *weak opening* `(sᵢ, t̂ᵢ, cᵢ)ᵢ`: the decomposition data `(sᵢ, t̂ᵢ)`
(`Decomp`) extended with per-block challenges `(cᵢ)`. The challenge originates as the verifier's
challenge during knowledge extraction; in this scheme definition the committer pairs the
decomposition with the trivial challenge `cᵢ = 1` (see `commitmentScheme`). -/
structure Opening (Φ : CyclotomicModulus R)
    (innerRows messageRows messageDigits blocks innerDigits : Nat) extends
    Decomp Φ innerRows messageRows messageDigits blocks innerDigits where
  /-- Per-block challenges `(cᵢ)`. -/
  challenge : PolyVec (Rq Φ) blocks


-- @@ L124-128 verbatim
/-- The decomposition operations used by the honest committer. -/
structure Decomposition (Φ : CyclotomicModulus R)
    (messageRows messageDigits innerRows innerDigits : Nat) where
  /-- Decompose one message block w.r.t. the message gadget. -/
  message : PolyVec (Rq Φ) messageRows → PolyVec (Rq Φ) (messageRows * messageDigits)
  
-- @@ L129-130 verbatim
/-- Decompose one inner commitment w.r.t. the inner gadget. -/
  inner : PolyVec (Rq Φ) innerRows → PolyVec (Rq Φ) (innerRows * innerDigits)


-- @@ L132-139 verbatim
/-- The honest decomposition whose message and inner steps are both the Hachi gadget inverse
`G⁻¹` (`gadgetDecompose`) built from base-`b` digit decompositions. -/
def Decomposition.ofDigits [DecidableEq R] {base : R}
    (ddMsg : DigitDecomposition base messageDigits)
    (ddInner : DigitDecomposition base innerDigits) :
    Decomposition Φ messageRows messageDigits innerRows innerDigits where
  message := gadgetDecompose Φ ddMsg
  inner := gadgetDecompose Φ ddInner


-- @@ L141-143 verbatim
/-- Messages: block vectors over the message row space. -/
abbrev Message (Φ : CyclotomicModulus R) (messageRows blocks : Nat) :=
  PolyVec (PolyVec (Rq Φ) messageRows) blocks


-- @@ L145-146 verbatim
/-- Inner-outer commitments live in the outer row space. -/
abbrev Commitment (Φ : CyclotomicModulus R) (outerRows : Nat) := Simple.Commitment Φ outerRows


-- @@ L148-154 verbatim
/-- The message block derived from the decomposition data: `mᵢ = G · sᵢ`, the message gadget
matrix applied to the per-block decomposition (Hachi [NOZ26, Eq. (13)]). The decomposition does
not store the message; this recovers it. -/
def derivedMessage (base : R)
    (decomp : Decomp Φ innerRows messageRows messageDigits blocks innerDigits) :
    Message Φ messageRows blocks :=
  fun i => Simple.commit Φ (gadgetMatrix Φ base messageRows messageDigits) (decomp.message i)


-- @@ L156-166 verbatim
/-- Honest decomposition generation from the supplied decomposition operations: per-block
messages `sᵢ = G⁻¹(mᵢ)` and inner decompositions `t̂ᵢ = G⁻¹(A sᵢ)`. No challenge is produced
here; the honest committer pairs this with the trivial challenge `cᵢ = 1` in `commitmentScheme`,
under which `verify_weak` reduces to the ordinary honest check. -/
def generateDecomps (decomp : Decomposition Φ messageRows messageDigits innerRows innerDigits)
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (m : Message Φ messageRows blocks) :
    Decomp Φ innerRows messageRows messageDigits blocks innerDigits :=
  let ss := fun i => decomp.message (m i)
  { message := ss
    innerDecomp := fun i => decomp.inner (Simple.commit Φ pp.innerMatrix (ss i)) }


-- @@ L168-173 verbatim
/-- Compute the outer commitment from the decomposition data. -/
def commitWithDecomps
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (decomp : Decomp Φ innerRows messageRows messageDigits blocks innerDigits) :
    Commitment Φ outerRows :=
  Simple.commit Φ pp.outerMatrix (PolyVec.flattenBlocks decomp.innerDecomp)


-- @@ L175-175 verbatim
end Defs


-- @@ L177-180 verbatim
/-! ## Weak verification and the bundled commitment scheme (over `ZMod q`)

The weak verifier and the bundled `CommitmentScheme` are pinned to `R = ZMod q`, since the
short-vector norms `Rq.l1Norm` and `vecL2NormSq` are only defined there. -/


-- @@ L182-182 verbatim
section WeakScheme


-- @@ L184-185 verbatim
variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]

-- @@ L186-186 verbatim
variable {innerRows messageRows messageDigits outerRows blocks innerDigits : Nat}


-- @@ L188-208 verbatim
/-- Verify a Hachi/Greyhound weak opening `(sᵢ, t̂ᵢ, cᵢ)ᵢ` against the outer commitment `u`.

Per block `i`: the challenge is nonzero and `ℓ₁`-short (`0 < ‖cᵢ‖₁ ≤ κ`), the scaled message
is `ℓ₂²`-short (`‖cᵢ·sᵢ‖₂² ≤ βSq`), and the inner gadget relation `A sᵢ = G t̂ᵢ` holds.
Globally: the flattened inner decomposition is `ℓ∞`-short (`‖t̂‖∞ ≤ γ`, as in
Hachi [NOZ26, §4.1]) and outer-commits to `u`.

The nonzero check `0 < ‖cᵢ‖₁` stands in for invertibility of `cᵢ`; the latter follows from the
`ℓ₁` bound by [LS18] (see the module docstring). -/
def verify_weak (base : ZMod q) (βSq γ κ : Nat)
    (pp : PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
    (u : Commitment Φ outerRows)
    (opening : Opening Φ innerRows messageRows messageDigits blocks innerDigits) : Bool :=
  (List.finRange blocks).all (fun i =>
    decide (0 < ‖opening.challenge i‖₁) &&
      decide (‖opening.challenge i‖₁ ≤ κ) &&
      decide (‖opening.challenge i •ᵥ opening.message i‖₂² ≤ βSq) &&
      Simple.verify Φ (gadgetMatrix Φ base innerRows innerDigits)
        (opening.innerDecomp i) (Simple.commit Φ pp.innerMatrix (opening.message i)) ()) &&
    decide (vecLInftyNorm Φ (PolyVec.flattenBlocks opening.innerDecomp) ≤ γ) &&
    Simple.verify Φ pp.outerMatrix (PolyVec.flattenBlocks opening.innerDecomp) u ()


-- @@ L210-212 verbatim
variable
  [SampleableType (Simple.PublicParams Φ innerRows (messageRows * messageDigits))]
  [SampleableType (Simple.PublicParams Φ outerRows (blocks * (innerRows * innerDigits)))]


-- @@ L214-237 verbatim
/-- The inner-outer Ajtai commitment as a `CommitmentScheme`, verified with the Hachi/Greyhound
weak verifier `verify_weak`.

Verification ties the claimed message `m` to the opening by deriving it via the message gadget
matrix (`derivedMessage opening = m`, i.e. `mᵢ = G · sᵢ`) and then running `verify_weak`. The
honest committer produces a weak opening with trivial challenge `cᵢ = 1`. -/
def commitmentScheme (base : ZMod q) (βSq γ κ : Nat)
    (decomp : Decomposition Φ messageRows messageDigits innerRows innerDigits) :
    CommitmentScheme
      (PublicParams Φ innerRows messageRows messageDigits outerRows blocks innerDigits)
      (Message Φ messageRows blocks) (Commitment Φ outerRows)
      (Opening Φ innerRows messageRows messageDigits blocks innerDigits) where
  setup := do
    let A ← $ᵗ (Simple.PublicParams Φ innerRows (messageRows * messageDigits))
    let B ← $ᵗ (Simple.PublicParams Φ outerRows (blocks * (innerRows * innerDigits)))
    pure { innerMatrix := A, outerMatrix := B }
  commit pp m :=
    let decomps := generateDecomps Φ decomp pp m
    pure (commitWithDecomps Φ pp decomps, { toDecomp := decomps, challenge := fun _ => 1 })
    -- dummy challenge value c=1 here
  verify pp m c opening :=
    (List.finRange blocks).all (fun i =>
      decide (derivedMessage Φ base opening.toDecomp i = m i)) &&
      verify_weak Φ base βSq γ κ pp c opening


-- @@ L239-239 verbatim
end WeakScheme


-- @@ L241-241 verbatim
end ArkLib.Lattices.Ajtai.InnerOuter
