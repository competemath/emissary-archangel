/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/
module

public import ArkLib.Data.CodingTheory.InterleavedCode
public import ArkLib.Data.Probability.Notation
public import Mathlib.Probability.Distributions.Uniform


-- @@ L13-50 verbatim
/-!
# Proximity gap fundamental definitions

Define the fundamental definitions for proximity gap properties of generic codes and
module codes over (scalar) rings.

## Main Definitions

### Proximity Gap Definitions
- `proximityMeasure`: Counts vectors close to linear combinations with code `C`
- `proximityGap`: Proximity gap property at distance `d` with cardinality bound
- `δ_ε_proximityGap`: Generic `(δ, ε)`-proximity gap for any collection of sets

### Correlated Agreement Definitions
- `jointAgreement`: Words collectively agree with code `C` on the same coordinate set
- `jointAgreement_iff_jointProximity`: Equivalence between agreement and proximity formulations
- `δ_ε_correlatedAgreementAffineLines`: Correlated agreement for affine lines (2 words)
- `δ_ε_correlatedAgreementCurves`: Correlated agreement for parametrised curves (k words)
- `δ_ε_correlatedAgreementAffineSpaces`: Correlated agreement for affine subspaces (k+1 words)

## TODOs
- weighted correlated agreement
- generalize the CA definitions using proximity generator?

(Mutual correlated agreement lives in `ProximityGenerators.lean` (`IsMCA`/`IsMCAGenerator`/
`mcaError`, module-alphabet general) with preservation lemmas in `MCAGenerator.lean`,
`AffineGenerator.lean` and `TensorGenerator.lean`.)

## References

- [BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed–Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654, version 20210703:203025.

- [DG25] Benjamin E. Diamond and Angus Gruen. “Proximity Gaps in Interleaved Codes”. In: IACR
  Communications in Cryptology 1.4 (Jan. 13, 2025). issn: 3006-5496. doi: 10.62056/a0ljbkrz.

-/


-- @@ L52-52 verbatim
@[expose] public section


-- @@ L54-54 verbatim
namespace ProximityGap


-- @@ L56-56 verbatim
open NNReal Finset Function Code Affine

-- @@ L57-57 verbatim
open scoped ProbabilityTheory BigOperators LinearCode Affine


-- @@ L59-59 verbatim
universe u v w k l


-- @@ L61-61 verbatim
section CoreSecurityDefinitions


-- @@ L63-63 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- @@ L64-65 verbatim
variable {κ : Type k} {ι : Type l} [Fintype κ] [Fintype ι] [Nonempty ι]
-- κ => row indices, ι => column indices

-- @@ L66-67 verbatim
variable {F : Type v} [Ring F] [Fintype F]
-- variable {M : Type} [Fintype M] -- Message space type

-- @@ L68-68 verbatim
variable {A : Type w} [Fintype A] [DecidableEq A] [AddCommMonoid A] [Module F A] -- Alphabet type

-- @@ L69-69 verbatim
variable (C : Set (ι → A))


-- @@ L71-75 verbatim
/-- The proximity measure of two vectors `u` and `v` from a code `C` at distance `d` is the number
  of vectors at distance at most `d` from the linear combination of `u` and `v` with coefficients
  `r` in `F`. -/
noncomputable def proximityMeasure (u v : Word A ι) (d : ℕ) : ℕ :=
  Fintype.card {r : F | Δ₀(r • u + (1 - r) • v, C) ≤ d}


-- @@ L77-84 verbatim
/-- A code `C` exhibits proximity gap at distance `d` and cardinality bound `bound` if for every
  pair of vectors `u` and `v`, whenever the proximity measure for `C u v d` is greater than
  `bound`, then the distance of `[u | v]` from the interleaved code `C ^⊗ 2` is at most `d`. -/
def proximityGap (d : ℕ) (bound : ℕ) : Prop :=
  ∀ u v : Word (A := A) (ι := ι), (proximityMeasure (F := F) C u v d > bound)
    →
    letI : Fintype (C ^⋈ (Fin 2)) := interleavedCodeSet_fintype (C := C)
    (Δ₀(u ⋈₂ v, C ^⋈ (Fin 2)) ≤ d)


-- @@ L86-88 verbatim
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
  {F : Type} [Ring F] [Fintype F]
  {k : ℕ}


-- @@ L90-106 verbatim
/-- Definition 1.1 in [BCIKS20].

Let `P` be a set `P` and `C` a collection of sets. We say that `C` displays a
`(δ, ε)`-proximity gap with respect to `P` and the relative Hamming distance measure
if for every `S ∈ C` exactly one of the following holds:

1. The probability that a randomly sampled element `s` from `S` is `δ`-close to `P` is `1`.
2. The probability that a randomly sampled element `s` from `S` is `δ`-close to `P` is at most
`ε`.

We call `δ` the proximity parameter and `ε` the error parameter. -/
noncomputable def δ_ε_proximityGap {α : Type} [DecidableEq α] [Nonempty α]
  (P : Finset (ι → α)) (C : Set (Finset (ι → α))) (δ ε : ℝ≥0) : Prop :=
  ∀ S ∈ C, ∀ [Nonempty S],
  Xor
  ( Pr_{let x ← $ᵖ S}[δᵣ(x.val, P) ≤ δ] = 1 )
  ( Pr_{let x ← $ᵖ S}[δᵣ(x.val, P) ≤ δ] ≤ ε )


-- @@ L108-117 verbatim
/-- Definition: `(δ, ε)`-correlated agreement for affine lines.
For every pair of words `u₀, u₁`, if the probability that a random affine line `u₀ + z • u₁` is
`δ`-close to `C` exceeds `ε`, then `u₀` and `u₁` have correlated agreement with `C`.
-- **TODO**: prove that `δ_ε_correlatedAgreementAffineLines` implies `δ_ε_proximityGap`
-/
noncomputable def δ_ε_correlatedAgreementAffineLines [Module F A]
    (C : Set (ι → A)) (δ ε : ℝ≥0) : Prop :=
  ∀ (u : WordStack (A := A) (κ := Fin 2) (ι := ι)),
    Pr_{let z ← $ᵖ F}[δᵣ(u 0 + z • u 1, C) ≤ δ] > ε →
    jointAgreement (F := A) (κ := Fin 2) (ι := ι) (C := C) (W := u) (δ := δ)


-- @@ L119-123 verbatim
section MultilinearCA

-- Shadow the section's `[Ring F]` scalars: the multilinear combination `|⨂|` needs a single
-- coherent `CommRing` structure on `F`, and mixing it with the outer `Ring F` binder creates
-- an instance diamond.

-- @@ L124-124 verbatim
variable {F : Type} [CommRing F] [Fintype F]


-- @@ L126-137 verbatim
/-- **[Definition 2.3, DG25]** We say that `C ⊂ F^n` features multilinear correlated agreement
with respect to the proximity parameter `δ` and the error bound `ε`, folding degree `ϑ > 0` if:
∀ word stack `u` of size `2^ϑ`, if the probability that
  (a random multilinear combination of the word stack `u` with randomness `r` is `δ`-close to `C`)
  exceeds `ε`, then the word stack `u` has correlated agreement with `C ^⋈ (2^ϑ)`. -/
def δ_ε_multilinearCorrelatedAgreement [Module F A]
    (C : Set (ι → A)) (ϑ : ℕ) (δ ε : ℝ≥0) : Prop :=
  ∀ (u : WordStack A (Fin (2^ϑ)) ι),
    Pr_{let r ← $ᵖ (Fin ϑ → F)}[ -- This syntax only works with (A : Type 0)
      δᵣ(r |⨂| u, C) ≤ δ
    ] > (ϑ : ℝ≥0) * ε →
    jointAgreement (F := A) (κ := Fin (2 ^ ϑ)) (ι := ι) (C := C) (W := u) (δ := δ)


-- @@ L139-139 verbatim
end MultilinearCA


-- @@ L141-157 verbatim
/-- **`(δ, ε)`-CA for low-degree parameterised (polynomial) curves**: Generalized statement of
**Theorem 1.5, [BCIKS20]**
For `k+1` words `u₀, u₁, ..., uₖ ∈ A^ι` let `curve(u) = {∑_{i ∈ {0, ..., k}}, z^i • u_i | z ∈ 𝔽}`
be a low-degree parameterised polynomial curve. If the probability that a random point in
`curve(u)` is `δ`-close to `C` exceeds `k * ε` (not `(k+1) * ε`), then the words `u₀, ..., uₖ`
have correlated agreement.
**NOTE**: this definition could be converted into the form of Pr_{let r ← $ᵖ F}[...] if we want:
  + consistency with `δ_ε_correlatedAgreementAffineLines`
  + making `A` be of arbitrary type universe (Type*)
  + to be able to support the `proximity generator` notation.
-/
noncomputable def δ_ε_correlatedAgreementCurves {k : ℕ}
    {A : Type 0} [AddCommMonoid A] [Module F A] [Fintype A] [DecidableEq A]
    (C : Set (ι → A)) (δ ε : ℝ≥0) : Prop :=
    ∀ (u : WordStack (A := A) (κ := Fin (k + 1)) (ι := ι)),
    Pr_{let r ← $ᵖ F}[ δᵣ(∑ i : Fin (k + 1), (r ^ (i : ℕ)) • u i, C) ≤ δ ] > k * ε
      → jointAgreement (F := A) (κ := Fin (k + 1)) (ι := ι) (C := C) (W := u) (δ := δ)


-- @@ L159-174 verbatim
/-- **`(δ, ε)`-CA for affine spaces**: Generalized statement of **Theorem 1.6, [BCIKS20]**
For `k+1` words `u₀, u₁, ..., uₖ ∈ A^ι` let `U = u₀ + span{u₁, ..., uₖ} ⊂ A^ι` be an affine subspace
(note that `span` here means linear span, so this formulation is not same as the default
affine span/affine hull). If the probability that a random point in `U` is `δ`-close to `C`
exceeds `ε`, then the words `u₀, u₁, ..., uₖ` have correlated agreement.

This samples uniformly from the generated affine subspace. An equivalent coefficient-sampling
formulation would sample `r : Fin k → F` and test `u₀ + ∑ i, r i • uᵢ₊₁`; proving that
equivalence requires showing the coefficient map has constant-size fibers. -/
noncomputable def δ_ε_correlatedAgreementAffineSpaces
    {A : Type 0} [AddCommGroup A] [Module F A] [Fintype A] [DecidableEq A]
    (C : Set (ι → A)) (δ ε : ℝ≥0) : Prop :=
    ∀ (u : WordStack (A := A) (κ := Fin (k + 1)) (ι := ι)),
    Pr_{let y ← $ᵖ ↥(Affine.affineSubspaceAtOrigin (F := F) (u 0) (Fin.tail u))}[
      δᵣ(y.1, C) ≤ δ] > ε →
    jointAgreement (F := A) (κ := Fin (k + 1)) (ι := ι) (C := C) (W := u) (δ := δ)


-- @@ L176-176 verbatim
end CoreSecurityDefinitions


-- @@ L178-178 verbatim
namespace WeightedAgreement


-- @@ L180-180 verbatim
open NNReal Finset Function

-- @@ L181-181 verbatim
open scoped BigOperators


-- @@ L183-183 verbatim
section


-- @@ L185-185 verbatim
variable {ι : Type} [Fintype ι] [Nonempty ι]

-- @@ L186-186 verbatim
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

-- @@ L187-187 verbatim
variable (μ : ι → Set.Icc (0 : ℚ) 1)


-- @@ L189-191 verbatim
/-- Relative `μ`-agreement between words `u` and `v`. -/
noncomputable def agree (u v : ι → F) : ℝ :=
  1 / (Fintype.card ι) * ∑ i ∈ { i | u i = v i }, (μ i).1


-- @@ L193-197 verbatim
/-- `μ`-agreement between a word and a finite set `V`. -/
noncomputable def agree_set (u : ι → F) (V : Finset (ι → F)) [Nonempty V] : ℝ :=
  (Finset.image (agree μ u) V).max' <| by
    rcases ‹Nonempty V› with ⟨v, hv⟩
    exact ⟨agree μ u v, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩


-- @@ L199-201 verbatim
/-- Weighted size of a subdomain. -/
noncomputable def mu_set (ι' : Finset ι) : ℝ :=
  1 / (Fintype.card ι) * ∑ i ∈ ι', (μ i).1


-- @@ L203-210 verbatim
/-- `μ`-weighted correlated agreement. -/
noncomputable def weightedCorrelatedAgreement
    (C : Set (ι → F)) [Nonempty C] {k : ℕ} (U : Fin k → ι → F) : ℝ :=
  sSup {x |
    ∃ D' ⊆ (Finset.univ (α := ι)),
      x = mu_set μ D' ∧
      ∃ v : Fin k → ι → F, ∀ i, v i ∈ C ∧ ∀ j ∈ D', v i j = U i j
  }


-- @@ L212-212 verbatim
end


-- @@ L214-214 verbatim
end WeightedAgreement


-- @@ L216-216 verbatim
end ProximityGap
