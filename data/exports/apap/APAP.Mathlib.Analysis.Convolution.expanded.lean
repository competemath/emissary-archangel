module

public import Mathlib.Algebra.Group.Translate
public import Mathlib.Analysis.Convolution


-- @@ L6-10 verbatim
/-!
# TODO

Extra arguments to `convolution_zero`
-/


-- @@ L12-12 verbatim
public section


-- @@ L14-14 verbatim
open ContinuousLinearMap Function

-- @@ L15-15 verbatim
open scoped Convolution translate


-- @@ L17-17 verbatim
namespace MeasureTheory

-- @@ L18-18 verbatim
variable {𝕜 G E E' F F' F'' E'' : Type*}


-- @@ L20-20 verbatim
section NontriviallyNormedField

-- @@ L21-27 verbatim
variable [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup E'']
  [NormedAddCommGroup F] [NormedAddCommGroup F'] [NormedAddCommGroup F'']
  [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 E'']
  [NormedSpace 𝕜 F] [NormedSpace 𝕜 F'] [NormedSpace 𝕜 F'']
  {f : G → E} {g g' : G → E'} {L : E →L[𝕜] E' →L[𝕜] F}
  [MeasurableSpace G] {μ ν : Measure G} [AddGroup G]


-- @@ L29-30 verbatim
lemma ConvolutionExists.of_finite [Finite G] [MeasurableSingletonClass G] [IsFiniteMeasure μ] :
    ConvolutionExists f g L μ := fun _ ↦ .of_finite


-- @@ L32-32 verbatim
end NontriviallyNormedField


-- @@ L34-34 verbatim
section RCLike

-- @@ L35-37 verbatim
variable [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup E'']
  [NormedAddCommGroup F]

-- @@ L38-38 verbatim
variable [NormedSpace 𝕜 E]

-- @@ L39-39 verbatim
variable [NormedSpace 𝕜 E']

-- @@ L40-40 verbatim
variable [NormedSpace 𝕜 E'']

-- @@ L41-41 verbatim
variable [NormedSpace ℝ F] [NormedSpace 𝕜 F]

-- @@ L42-42 verbatim
variable {n : ℕ∞}

-- @@ L43-43 verbatim
variable [MeasurableSpace G] {μ ν : Measure G}

-- @@ L44-44 verbatim
variable (L : E →L[𝕜] E' →L[𝕜] F)


-- @@ L46-46 verbatim
section Assoc

-- @@ L47-47 verbatim
variable [CompleteSpace F]

-- @@ L48-48 verbatim
variable [NormedAddCommGroup F'] [NormedSpace ℝ F'] [NormedSpace 𝕜 F'] [CompleteSpace F']

-- @@ L49-49 verbatim
variable [NormedAddCommGroup F''] [NormedSpace ℝ F''] [NormedSpace 𝕜 F''] [CompleteSpace F'']

-- @@ L50-50 verbatim
variable {k : G → E''}

-- @@ L51-51 verbatim
variable (L₂ : F →L[𝕜] E'' →L[𝕜] F')

-- @@ L52-52 verbatim
variable (L₃ : E →L[𝕜] F'' →L[𝕜] F')

-- @@ L53-53 verbatim
variable (L₄ : E' →L[𝕜] E'' →L[𝕜] F'')

-- @@ L54-54 verbatim
variable [AddGroup G]

-- @@ L55-55 verbatim
variable [SFinite μ] [SFinite ν] [μ.IsAddRightInvariant] {f g}


-- @@ L57-57 verbatim
variable [MeasurableAdd₂ G] [ν.IsAddRightInvariant] [MeasurableNeg G]


-- @@ L59-68 verbatim
/-- Convolution is associative. This has a weak but inconvenient integrability condition.
See also `MeasureTheory.convolution_assoc`. -/
-- TODO: Rename `convolution_assoc'` to `convolution_assoc_apply'`
theorem convolution_assoc''' (hL : ∀ x y z, L₂ (L x y) z = L₃ x (L₄ y z))
    (hfg : ∀ᵐ y ∂μ, ConvolutionExistsAt f g y L ν)
    (hgk : ∀ᵐ x ∂ν, ConvolutionExistsAt g k x L₄ μ)
    (hi : ∀ x₀,
      Integrable (uncurry fun x y => (L₃ (f y)) ((L₄ (g (x - y))) (k (x₀ - x)))) (μ.prod ν)) :
    (f ⋆[L, ν] g) ⋆[L₂, μ] k = f ⋆[L₃, ν] (g ⋆[L₄, μ] k) :=
  funext fun _ ↦ convolution_assoc' _ _ _ _ hL hfg hgk (hi _)


-- @@ L70-82 verbatim
/-- Convolution is associative. This requires that
* all maps are a.e. strongly measurable w.r.t one of the measures
* `f ⋆[L, ν] g` exists almost everywhere
* `‖g‖ ⋆[μ] ‖k‖` exists almost everywhere
* `‖f‖ ⋆[ν] (‖g‖ ⋆[μ] ‖k‖)` exists at `x₀` -/
-- TODO: Rename `convolution_assoc` to `convolution_assoc_apply`
theorem convolution_assoc'' (hL : ∀ x y z, L₂ (L x y) z = L₃ x (L₄ y z))
    (hf : AEStronglyMeasurable f ν) (hg : AEStronglyMeasurable g μ) (hk : AEStronglyMeasurable k μ)
    (hfg : ∀ᵐ y ∂μ, ConvolutionExistsAt f g y L ν)
    (hgk : ∀ᵐ x ∂ν, ConvolutionExistsAt (‖g ·‖) (‖k ·‖) x (mul ℝ ℝ) μ)
    (hfgk : ConvolutionExists (‖f ·‖) ((‖g ·‖) ⋆[mul ℝ ℝ, μ] (‖k ·‖)) (mul ℝ ℝ) ν) :
    (f ⋆[L, ν] g) ⋆[L₂, μ] k = f ⋆[L₃, ν] (g ⋆[L₄, μ] k) :=
  funext fun _ ↦ convolution_assoc _ _ _ _ hL hf hg hk hfg hgk (hfgk _)


-- @@ L84-84 verbatim
end Assoc


-- @@ L86-86 verbatim
section translate

-- @@ L87-87 verbatim
variable [AddCommGroup G]


-- @@ L89-91 verbatim
@[simp] lemma convolution_translate (a : G) (f : G → E) (g : G → E') :
    f ⋆[L, ν] τ a g = τ a (f ⋆[L, ν] g) := by
  ext b; simp [convolution, sub_right_comm]


-- @@ L93-93 verbatim
variable [MeasurableAdd G] [ν.IsAddRightInvariant]


-- @@ L95-97 verbatim
@[simp] lemma translate_convolution (a : G) (f : G → E) (g : G → E') :
    τ a f ⋆[L, ν] g = τ a (f ⋆[L, ν] g) := by
  ext b; simpa [convolution] using integral_sub_right_eq_self (fun t ↦ L (f t) (g (b - a - t))) a


-- @@ L99-99 verbatim
end translate

-- @@ L100-100 verbatim
end RCLike

-- @@ L101-101 verbatim
end MeasureTheory
