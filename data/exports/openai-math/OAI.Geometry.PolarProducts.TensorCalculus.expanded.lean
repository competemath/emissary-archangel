import OAI.Geometry.PolarProducts.SmoothFlow


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u17 u18 u19 u20 u21 u22


-- @@ L7-7 verbatim
section LowerBoundInline

-- @@ L8-8 verbatim
open Set Filter Function

-- @@ L9-9 verbatim
open scoped Topology ContDiff NNReal

-- @@ L10-10 verbatim
open Set Filter Metric

-- @@ L11-11 verbatim
open scoped Topology ContDiff

-- @@ L12-12 verbatim
open Set Filter Function MeasureTheory Metric

-- @@ L13-13 verbatim
open scoped Topology ContDiff NNReal


-- @@ L15-15 verbatim
open Set Filter Function

-- @@ L16-16 verbatim
open scoped Topology ContDiff


-- @@ L18-18 verbatim
namespace TensorCalculus


-- @@ L20-20 verbatim
variable {E : Type u17} [NormedAddCommGroup E] [NormedSpace ℝ E]


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
local instance oneTensorGroup : NormedAddCommGroup (E →L[ℝ] ℝ) := inferInstance

-- @@ L25-25 verbatim
local instance oneTensorSpace : NormedSpace ℝ (E →L[ℝ] ℝ) := inferInstance

-- @@ L26-26 verbatim
local instance twoTensorGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance

-- @@ L27-27 verbatim
local instance twoTensorSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) := inferInstance


-- @@ L29-30 verbatim
abbrev TwoTensor (E : Type u18) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  E →L[ℝ] E →L[ℝ] ℝ


-- @@ L32-34 verbatim
def evalTensor (a b : E) : TwoTensor E →L[ℝ] ℝ :=
  (ContinuousLinearMap.apply ℝ ℝ b).comp
    (ContinuousLinearMap.apply ℝ (E →L[ℝ] ℝ) a)


-- @@ L36-37 verbatim
@[simp] theorem evalTensor_apply (a b : E) (B : TwoTensor E) :
    evalTensor a b B = B a b := rfl


-- @@ L39-45 verbatim
theorem fderiv_evalTensor {D : Type u19} [NormedAddCommGroup D] [NormedSpace ℝ D]
    {B : D → TwoTensor E} {x : D} (hB : DifferentiableAt ℝ B x)
    (d : D) (a b : E) : fderiv ℝ (fun y => B y a b) x d = fderiv ℝ B x d a b := by
  rw [fderiv_clm_apply (hB.clm_apply (differentiableAt_const a))
    (differentiableAt_const b)]
  rw [fderiv_clm_apply hB (differentiableAt_const a)]
  simp


-- @@ L47-53 verbatim
theorem fderiv_skew {B : E → TwoTensor E} (hB : Differentiable ℝ B)
    (hsk : ∀ x a b, B x a b = -B x b a) (x d a b : E) :
    fderiv ℝ B x d a b = -fderiv ℝ B x d b a := by
  have he : (fun y => B y a b) = fun y => -B y b a := funext (fun y => hsk y a b)
  have he' := congrArg (fun f : E → ℝ => fderiv ℝ f x d) he
  rw [fderiv_fun_neg] at he'
  simpa only [fderiv_evalTensor (hB x), neg_apply] using he'


-- @@ L55-66 verbatim
theorem derivative_kernel {B : E → TwoTensor E} {V : E → E}
    (hB : Differentiable ℝ B) (hV : Differentiable ℝ V)
    (hker : ∀ x, B x (V x) = 0) (x a b : E) :
    B x (fderiv ℝ V x a) b + fderiv ℝ B x a (V x) b = 0 := by
  have hd : HasFDerivAt (fun y => B y (V y))
      ((B x).comp (fderiv ℝ V x) + (fderiv ℝ B x).flip (V x)) x :=
    (hB x).hasFDerivAt.clm_apply (hV x).hasFDerivAt
  have hz : HasFDerivAt (fun y => B y (V y)) 0 x :=
    (hasFDerivAt_const (𝕜 := ℝ) (0 : E →L[ℝ] ℝ) x).congr_of_eventuallyEq
      (Filter.Eventually.of_forall hker)
  have he := congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L a b) (hd.unique hz)
  simpa using he


-- @@ L68-81 verbatim
theorem invariant_of_closed_kernel {B : E → TwoTensor E} {V : E → E}
    (hB : Differentiable ℝ B) (hV : Differentiable ℝ V)
    (hsk : ∀ x a b, B x a b = -B x b a)
    (hclosed : ∀ x a b c, fderiv ℝ B x a b c +
      fderiv ℝ B x b c a + fderiv ℝ B x c a b = 0)
    (hker : ∀ x, B x (V x) = 0) (x a b : E) :
    fderiv ℝ B x (V x) a b + B x (fderiv ℝ V x a) b +
      B x a (fderiv ℝ V x b) = 0 := by
  have h1 := derivative_kernel hB hV hker x a b
  have h2 := derivative_kernel hB hV hker x b a
  have h3 := hclosed x (V x) a b
  have h4 := fderiv_skew hB hsk x a b (V x)
  have h5 := hsk x a (fderiv ℝ V x b)
  linarith


-- @@ L83-90 verbatim
theorem fderiv_skew_at {B : E → TwoTensor E} {x : E} (hB : DifferentiableAt ℝ B x)
    (hsk : ∀ᶠ y in 𝓝 x, ∀ a b, B y a b = -B y b a) (d a b : E) :
    fderiv ℝ B x d a b = -fderiv ℝ B x d b a := by
  have he : (fun y => B y a b) =ᶠ[𝓝 x] (fun y => -B y b a) :=
    hsk.mono (fun y hy => hy a b)
  have he' := congrArg (fun L : E →L[ℝ] ℝ => L d) he.fderiv_eq
  rw [fderiv_fun_neg] at he'
  simpa only [fderiv_evalTensor hB, neg_apply] using he'


-- @@ L92-102 verbatim
theorem derivative_kernel_at {B : E → TwoTensor E} {V : E → E} {x : E}
    (hB : DifferentiableAt ℝ B x) (hV : DifferentiableAt ℝ V x)
    (hker : ∀ᶠ y in 𝓝 x, B y (V y) = 0) (a b : E) :
    B x (fderiv ℝ V x a) b + fderiv ℝ B x a (V x) b = 0 := by
  have hd : HasFDerivAt (fun y => B y (V y))
      ((B x).comp (fderiv ℝ V x) + (fderiv ℝ B x).flip (V x)) x :=
    hB.hasFDerivAt.clm_apply hV.hasFDerivAt
  have hz : HasFDerivAt (fun y => B y (V y)) 0 x :=
    (hasFDerivAt_const (𝕜 := ℝ) (0 : E →L[ℝ] ℝ) x).congr_of_eventuallyEq hker
  have he := congrArg (fun L : E →L[ℝ] E →L[ℝ] ℝ => L a b) (hd.unique hz)
  simpa using he


-- @@ L104-117 verbatim
theorem invariant_of_closed_kernel_at {B : E → TwoTensor E} {V : E → E} {x : E}
    (hB : DifferentiableAt ℝ B x) (hV : DifferentiableAt ℝ V x)
    (hsk : ∀ᶠ y in 𝓝 x, ∀ a b, B y a b = -B y b a)
    (hclosed : ∀ a b c, fderiv ℝ B x a b c +
      fderiv ℝ B x b c a + fderiv ℝ B x c a b = 0)
    (hker : ∀ᶠ y in 𝓝 x, B y (V y) = 0) (a b : E) :
    fderiv ℝ B x (V x) a b + B x (fderiv ℝ V x a) b +
      B x a (fderiv ℝ V x b) = 0 := by
  have h1 := derivative_kernel_at hB hV hker a b
  have h2 := derivative_kernel_at hB hV hker b a
  have h3 := hclosed (V x) a b
  have h4 := fderiv_skew_at hB hsk a b (V x)
  have h5 := (hsk.self_of_nhds) a (fderiv ℝ V x b)
  linarith


-- @@ L119-121 verbatim
def alt : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.id ℝ (E →L[ℝ] E →L[ℝ] ℝ) -
    (ContinuousLinearMap.flipₗᵢ ℝ E E ℝ).toLinearIsometry.toContinuousLinearMap


-- @@ L123-124 verbatim
@[simp] theorem alt_apply (B : TwoTensor E) (a b : E) :
    alt B a b = B a b - B b a := rfl


-- @@ L126-127 verbatim
def exteriorD (γ : E → E →L[ℝ] ℝ) (x : E) : TwoTensor E :=
  alt (fderiv ℝ γ x)


-- @@ L129-130 verbatim
@[simp] theorem exteriorD_apply (γ : E → E →L[ℝ] ℝ) (x a b : E) :
    exteriorD γ x a b = fderiv ℝ γ x a b - fderiv ℝ γ x b a := rfl


-- @@ L132-134 verbatim
theorem exteriorD_skew (γ : E → E →L[ℝ] ℝ) (x a b : E) :
    exteriorD γ x a b = -exteriorD γ x b a := by
  simp only [exteriorD_apply]; ring


-- @@ L136-142 verbatim
theorem fderiv_exteriorD {γ : E → E →L[ℝ] ℝ} {x : E}
    (hγ : DifferentiableAt ℝ (fderiv ℝ γ) x) (d a b : E) :
    fderiv ℝ (exteriorD γ) x d a b =
      fderiv ℝ (fderiv ℝ γ) x d a b - fderiv ℝ (fderiv ℝ γ) x d b a := by
  change fderiv ℝ (alt ∘ fderiv ℝ γ) x d a b = _
  rw [fderiv_comp x (ContinuousLinearMap.differentiableAt (alt (E := E))) hγ]
  simp


-- @@ L144-147 verbatim
theorem contDiff_exteriorD {γ : E → E →L[ℝ] ℝ}
    (hγ : ContDiff ℝ ∞ γ) : ContDiff ℝ ∞ (exteriorD γ) := by
  change ContDiff ℝ ∞ ((alt (E := E)) ∘ fderiv ℝ γ)
  exact (alt (E := E)).contDiff.comp (hγ.fderiv_right (m := ∞) (by simp))


-- @@ L149-163 verbatim
theorem exteriorD_closed {γ : E → E →L[ℝ] ℝ} {x : E}
    (hγ : ContDiffAt ℝ ∞ γ x) (a b c : E) :
    fderiv ℝ (exteriorD γ) x a b c + fderiv ℝ (exteriorD γ) x b c a +
      fderiv ℝ (exteriorD γ) x c a b = 0 := by
  have hd : DifferentiableAt ℝ (fderiv ℝ γ) x :=
    (hγ.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ ∞)).differentiableAt (by simp)
  have hs := hγ.isSymmSndFDerivAt (by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ (⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  simp only [fderiv_exteriorD hd]
  have h1 := congrArg (fun L : E →L[ℝ] ℝ => L c) (hs.eq a b)
  have h2 := congrArg (fun L : E →L[ℝ] ℝ => L a) (hs.eq b c)
  have h3 := congrArg (fun L : E →L[ℝ] ℝ => L b) (hs.eq c a)
  linarith


-- @@ L165-165 verbatim
end

-- @@ L166-166 verbatim
end TensorCalculus


-- @@ L168-168 verbatim
namespace TensorCalculus


-- @@ L170-170 verbatim
open Set Filter Function

-- @@ L171-171 verbatim
open scoped Topology ContDiff


-- @@ L173-175 verbatim
variable {E : Type u20} {F : Type u21} {D : Type u22} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup D] [NormedSpace ℝ D]


-- @@ L177-177 verbatim
noncomputable section


-- @@ L179-180 verbatim
def pullLinear (L : F →L[ℝ] E) (B : TwoTensor E) : TwoTensor F :=
  B.bilinearComp L L


-- @@ L182-183 verbatim
@[simp] theorem pullLinear_apply (L : F →L[ℝ] E) (B : TwoTensor E) (a b : F) :
    pullLinear L B a b = B (L a) (L b) := rfl


-- @@ L185-191 verbatim
theorem contDiffAt_pullLinear (L : F →L[ℝ] E) {B : D → TwoTensor E} {z : D}
    (hB : ContDiffAt ℝ ∞ B z) :
    ContDiffAt ℝ ∞ (fun x => pullLinear L (B x)) z := by
  let P : (E →L[ℝ] ℝ) →L[ℝ] (F →L[ℝ] ℝ) :=
    (ContinuousLinearMap.compL ℝ F E ℝ).flip L
  change ContDiffAt ℝ ∞ (fun x => P.comp ((B x).comp L)) z
  exact contDiffAt_const.clm_comp (hB.clm_comp contDiffAt_const)


-- @@ L193-199 verbatim
theorem fderiv_pullLinear_eval (L : F →L[ℝ] E) {B : D → TwoTensor E} {z : D}
    (hB : DifferentiableAt ℝ B z)
    (hP : DifferentiableAt ℝ (fun x => pullLinear L (B x)) z) (d : D) (a b : F) :
    fderiv ℝ (fun x => pullLinear L (B x)) z d a b =
      fderiv ℝ B z d (L a) (L b) := by
  rw [← fderiv_evalTensor hP, ← fderiv_evalTensor hB]
  rfl


-- @@ L201-218 verbatim
theorem pullLinear_closed (L : F →L[ℝ] E) {B : E → TwoTensor E} {z : F}
    (hB : ContDiffAt ℝ ∞ B (L z))
    (hclosed : ∀ a b c, fderiv ℝ B (L z) a b c +
      fderiv ℝ B (L z) b c a + fderiv ℝ B (L z) c a b = 0) (a b c : F) :
    fderiv ℝ (fun x => pullLinear L (B (L x))) z a b c +
      fderiv ℝ (fun x => pullLinear L (B (L x))) z b c a +
      fderiv ℝ (fun x => pullLinear L (B (L x))) z c a b = 0 := by
  have hs : ContDiffAt ℝ ∞ (fun x => B (L x)) z := hB.comp z L.contDiff.contDiffAt
  have ht := contDiffAt_pullLinear L hs
  have he (d u v : F) :
      fderiv ℝ (fun x => pullLinear L (B (L x))) z d u v =
        fderiv ℝ B (L z) (L d) (L u) (L v) := by
    rw [fderiv_pullLinear_eval L (hs.differentiableAt (by simp))
      (ht.differentiableAt (by simp))]
    rw [fderiv_fun_comp z (hB.differentiableAt (by simp)) L.differentiableAt]
    simp
  simp only [he]
  exact hclosed (L a) (L b) (L c)


-- @@ L220-220 verbatim
end

-- @@ L221-221 verbatim
end TensorCalculus


-- @@ L223-223 verbatim
end LowerBoundInline


-- @@ L225-225 verbatim
end OAI
