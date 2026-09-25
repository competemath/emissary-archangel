module
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.LinearCode
public import SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniqueness.CodeFromOctadsAux


-- @@ L7-18 verbatim
/-!
# Span of octads in a binary linear code

For a code `C : Code 24`, we consider the indicator words of its octads and the `ZMod 2`-submodule
they span. These objects are used to compare codes that share the same octads, and to transport
this span along coordinate permutations.

## Main definitions
* `octadWordSet`
* `octadSubmodule`
* `permuteLinearEquiv`
-/



-- @@ L21-21 verbatim
namespace SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps.CodeFromOctads


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open LinearCode

-- @@ L26-26 verbatim
open CodeFromOctadsAux


-- @@ L28-28 verbatim
local notation "Word" => BinWord 24


-- @@ L30-32 verbatim
/-- The set of indicator words of octads of a code `C`. -/
@[expose] public def octadWordSet (C : Code 24) : Set Word :=
  {w | ∃ B : Finset (Fin 24), B ∈ octadsFromCode C ∧ w = wordOfFinset (n := 24) B}


-- @@ L34-36 verbatim
/-- The `ZMod 2`-submodule spanned by the octad indicator words of `C`. -/
@[expose] public def octadSubmodule (C : Code 24) : Submodule (ZMod 2) Word :=
  Submodule.span (ZMod 2) (octadWordSet C)


-- @@ L38-46 verbatim
/-- If `B` is an octad coming from `C`, then its indicator word lies in `C`. -/
public lemma wordOfFinset_mem_code_of_mem_octads {C : Code 24} {B : Finset (Fin 24)}
    (hB : B ∈ octadsFromCode C) :
    wordOfFinset (n := 24) B ∈ C := by
  rcases hB with ⟨w, hwC, _hw8, rfl⟩
  -- `w` is uniquely determined by its support.
  have hw : wordOfFinset (n := 24) (support w) = w :=
    (word_eq_wordOfFinset_support (w := w)).symm
  simpa [hw] using hwC


-- @@ L48-54 verbatim
/-- For a linear code, the octad span is contained in the associated submodule. -/
public lemma octadSubmodule_le_codeSubmodule (C : Code 24) (hC : IsLinearCode C) :
    octadSubmodule C ≤ submodule (n := 24) C hC := by
  -- It suffices to show every generator is a codeword.
  refine Submodule.span_le.2 ?_
  rintro w ⟨B, hB, rfl⟩
  exact wordOfFinset_mem_code_of_mem_octads (C := C) hB


-- @@ L56-58 verbatim
/-- Linear equivalence given by permuting coordinates (restricted to length `24`). -/
@[expose] public def permuteLinearEquiv (σ : Equiv (Fin 24) (Fin 24)) : Word ≃ₗ[ZMod 2] Word :=
  LinearEquiv.funCongrLeft (R := ZMod 2) (M := ZMod 2) σ


-- @@ L60-63 verbatim
/-- Evaluation lemma for `permuteLinearEquiv`. -/
@[simp] public lemma permuteLinearEquiv_apply (σ : Equiv (Fin 24) (Fin 24)) (w : Word)
    (i : Fin 24) : permuteLinearEquiv σ w i = w (σ i) := by
  simp [permuteLinearEquiv]


-- @@ L65-70 verbatim
/-- Permuting the indicator word corresponds to mapping the underlying finset. -/
public lemma permuteWord_wordOfFinset (σ : Equiv (Fin 24) (Fin 24)) (B : Finset (Fin 24)) :
    permuteWord (n := 24) σ (wordOfFinset (n := 24) B) =
      wordOfFinset (n := 24) (B.map σ.symm.toEmbedding) := by
  funext i
  simp [permuteWord, wordOfFinset, Finset.mem_map_equiv]


-- @@ L72-72 verbatim
attribute [grind =] permuteWord_wordOfFinset


-- @@ L74-74 verbatim
end


-- @@ L76-76 verbatim
end SpherePacking.Dim24.Uniqueness.BS81.CodingTheory.GolayUniquenessSteps.CodeFromOctads
