import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.Notation
import SphereEversion.Indexing
import SphereEversion.Notations
import SphereEversion.ToMathlib.Analysis.NormedSpace.Misc
import SphereEversion.ToMathlib.Geometry.Manifold.IsManifold.ExtChartAt
import SphereEversion.ToMathlib.Topology.Misc
import SphereEversion.ToMathlib.Topology.Paracompact


-- @@ L13-13 verbatim
noncomputable section


-- @@ L15-15 verbatim
open Set Equiv


-- @@ L17-17 verbatim
open scoped Manifold Topology ContDiff


-- @@ L19-19 verbatim
section General


-- @@ L21-25 verbatim
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type*)
  [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] {H' : Type*} [TopologicalSpace H']
  (I' : ModelWithCorners 𝕜 E' H') (M' : Type*) [TopologicalSpace M'] [ChartedSpace H' M']


-- @@ L27-33 verbatim
structure OpenSmoothEmbedding where
  toFun : M → M'
  invFun : M' → M
  left_inv' : ∀ {x}, invFun (toFun x) = x
  isOpen_range : IsOpen (range toFun)
  contMDiff_to : CMDiff ∞ toFun
  contMDiffOn_inv : CMDiff[range toFun] ∞ invFun


-- @@ L35-37 verbatim
attribute [coe] OpenSmoothEmbedding.toFun

-- Note: this cannot be a `FunLike` instance since `toFun` is not injective in general.

-- @@ L38-39 verbatim
instance : CoeFun (OpenSmoothEmbedding I M I' M') fun _ ↦ M → M' :=
  ⟨OpenSmoothEmbedding.toFun⟩


-- @@ L41-41 verbatim
namespace OpenSmoothEmbedding


-- @@ L43-43 verbatim
variable {I I' M M'}


-- @@ L45-45 verbatim
variable (f : OpenSmoothEmbedding I M I' M')


-- @@ L47-48 verbatim
theorem coe_mk (f g h₁ h₂ h₃ h₄) : ⇑(⟨f, g, h₁, h₂, h₃, h₄⟩ : OpenSmoothEmbedding I M I' M') = f :=
  rfl


-- @@ L50-51 verbatim
@[simp]
theorem left_inv (x : M) : f.invFun (f x) = x := by apply f.left_inv'


-- @@ L53-55 verbatim
@[simp]
theorem invFun_comp_coe : f.invFun ∘ f = id :=
  funext f.left_inv


-- @@ L57-60 verbatim
@[simp]
theorem right_inv {y : M'} (hy : y ∈ range f) : f (f.invFun y) = y := by
  obtain ⟨x, rfl⟩ := hy;
  rw [f.left_inv]


-- @@ L62-63 verbatim
theorem contMDiffAt_inv {y : M'} (hy : y ∈ range f) : CMDiffAt ∞ f.invFun y :=
  (f.contMDiffOn_inv y hy).contMDiffAt <| f.isOpen_range.mem_nhds hy


-- @@ L65-66 verbatim
theorem contMDiffAt_inv' {x : M} : CMDiffAt ∞ f.invFun (f x) :=
  f.contMDiffAt_inv <| mem_range_self x


-- @@ L68-69 verbatim
theorem leftInverse : Function.LeftInverse f.invFun f :=
  left_inv f


-- @@ L71-72 verbatim
theorem injective : Function.Injective f :=
  f.leftInverse.injective


-- @@ L74-75 verbatim
protected theorem continuous : Continuous f :=
  f.contMDiff_to.continuous


-- @@ L77-78 verbatim
theorem isOpenMap : IsOpenMap f :=
  f.leftInverse.isOpenMap f.isOpen_range f.contMDiffOn_inv.continuousOn


-- @@ L80-81 verbatim
theorem coe_comp_invFun_eventuallyEq (x : M) : f ∘ f.invFun =ᶠ[𝓝 (f x)] id :=
  Filter.eventually_of_mem (f.isOpenMap.range_mem_nhds x) fun _ hy ↦ f.right_inv hy


-- @@ L83-83 verbatim
section


-- @@ L85-88 verbatim
variable [IsManifold I ∞ M] [IsManifold I' ∞ M']

/- Note that we are slightly abusing the fact that `TangentSpace I x` and
`TangentSpace I (f.invFun (f x))` are both definitionally `E` below. -/

-- @@ L89-108 verbatim
def fderiv (x : M) : TangentSpace I x ≃L[𝕜] TangentSpace I' (f x) :=
  have h₁ : MDiffAt f.invFun (f x) :=
    ((f.contMDiffOn_inv (f x)
    (mem_range_self x)).mdifferentiableWithinAt (by simp)).mdifferentiableAt
    (f.isOpenMap.range_mem_nhds x)
  have h₂ : MDiffAt f x := f.contMDiff_to.mdifferentiableAt (by simp)
  ContinuousLinearEquiv.equivOfInverse (mfderiv% f x) (mfderiv% f.invFun (f x))
    (by
      intro v
      erw [← ContinuousLinearMap.comp_apply, ← mfderiv_comp x h₁ h₂, f.invFun_comp_coe, mfderiv_id,
        ContinuousLinearMap.coe_id', id])
    (by
      intro v
      have hx : x = f.invFun (f x) := by rw [f.left_inv]
      have hx' : f (f.invFun (f x)) = f x := by rw [f.left_inv]
      rw [hx] at h₂
      erw [hx, hx', ← ContinuousLinearMap.comp_apply, ← mfderiv_comp (f x) h₂ h₁,
        ((hasMFDerivAt_id (f x)).congr_of_eventuallyEq
            (f.coe_comp_invFun_eventuallyEq x)).mfderiv,
        ContinuousLinearMap.coe_id', id])


-- @@ L110-113 verbatim
omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
@[simp]
theorem fderiv_coe (x : M) :
    (f.fderiv x : TangentSpace% x →L[𝕜] TangentSpace% (f x)) = mfderiv% f x := by ext; rfl


-- @@ L115-119 verbatim
omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
@[simp]
theorem fderiv_symm_coe (x : M) :
    ((f.fderiv x).symm : TangentSpace% (f x) →L[𝕜] TangentSpace% x) =
      mfderiv% f.invFun (f x) := by ext; rfl


-- @@ L121-126 verbatim
omit [IsManifold I ∞ M] [IsManifold I' ∞ M'] in
theorem fderiv_symm_coe' {x : M'} (hx : x ∈ range f) :
    ((f.fderiv (f.invFun x)).symm :
        TangentSpace% (f (f.invFun x)) →L[𝕜] TangentSpace% (f.invFun x)) =
      (mfderiv% f.invFun x : TangentSpace% x →L[𝕜] TangentSpace% (f.invFun x)) :=
  by rw [fderiv_symm_coe, f.right_inv hx]


-- @@ L128-128 verbatim
end


-- @@ L130-130 verbatim
open Filter Topology


-- @@ L132-133 verbatim
theorem isOpenEmbedding : IsOpenEmbedding f :=
  .of_continuous_injective_isOpenMap f.continuous f.injective f.isOpenMap


-- @@ L135-136 verbatim
theorem isInducing : IsInducing f :=
  f.isOpenEmbedding.toIsInducing


-- @@ L138-146 expanded
theorem forall_near' {P : M → Prop} {A : Set M'}
    (h : expand_binders% (p => Filter.Eventually p <| 𝓝ˢ (f ⁻¹' A)) m, P m) :
    expand_binders% (p => Filter.Eventually p <| 𝓝ˢ (A ∩ range f)) m', ∀ m, m' = f m → P m :=
  by
  rw [eventually_nhdsSet_iff_forall] at h ⊢
  rintro _ ⟨hfm₀, m₀, rfl⟩
  have : ∀ U ∈ 𝓝 m₀, ∀ᶠ m' in 𝓝 (f m₀), m' ∈ f '' U := fun U U_in ↦ f.isOpenMap.image_mem_nhds U_in
  apply (this _ <| h m₀ hfm₀).mono
  rintro _ ⟨m₀, hm₀, hm₀'⟩ m₁ rfl
  rwa [← f.injective hm₀']


-- @@ L148-152 expanded
theorem eventually_nhdsSet_mono {α : Type*} [TopologicalSpace α] {s t : Set α} {P : α → Prop}
    (h : expand_binders% (p => Filter.Eventually p <| 𝓝ˢ t) x, P x) (h' : s ⊆ t) :
    expand_binders% (p => Filter.Eventually p <| 𝓝ˢ s) x, P x :=
  h.filter_mono
    (nhdsSet_mono h')
      -- TODO: optimize this proof which is probably more complicated than it needs to be


-- @@ L153-174 expanded
theorem forall_near [T2Space M'] {P : M → Prop} {P' : M' → Prop} {K : Set M} (hK : IsCompact K)
    {A : Set M'} (hP : expand_binders% (p => Filter.Eventually p <| 𝓝ˢ (f ⁻¹' A)) m, P m)
    (hP' : expand_binders% (p => Filter.Eventually p <| 𝓝ˢ A) m', m' ∉ f '' K → P' m')
    (hPP' : ∀ m, P m → P' (f m)) : expand_binders% (p => Filter.Eventually p <| 𝓝ˢ A) m', P' m' :=
  by
  rw [show A = A ∩ range f ∪ A ∩ (range f)ᶜ by simp]
  apply Filter.Eventually.union
  · have : expand_binders% (p => Filter.Eventually p <| 𝓝ˢ (A ∩ range f)) m', m' ∈ range f :=
      f.isOpen_range.mem_nhdsSet.mpr inter_subset_right
    apply (this.and <| f.forall_near' hP).mono
    rintro _ ⟨⟨m, rfl⟩, hm⟩
    exact hPP' _ (hm _ rfl)
  · have op : IsOpen ((f '' K)ᶜ) := by
      rw [isOpen_compl_iff]
      exact (hK.image f.continuous).isClosed
    have : A ∩ (range f)ᶜ ⊆ A ∩ (f '' K)ᶜ :=
      inter_subset_inter_right _ (compl_subset_compl.mpr (image_subset_range f K))
    apply eventually_nhdsSet_mono _ this
    rw [eventually_nhdsSet_iff_forall] at hP' ⊢
    rintro x ⟨hx, hx'⟩
    have hx' : ∀ᶠ y in 𝓝 x, y ∈ (f '' K)ᶜ := isOpen_iff_eventually.mp op x hx'
    apply ((hP' x hx).and hx').mono
    rintro y ⟨hy, hy'⟩
    exact hy hy'


-- @@ L176-178 verbatim
variable (I M)

-- unused

-- @@ L179-187 verbatim
/-- The identity map is a smooth open embedding. -/
@[simps]
nonrec def id : OpenSmoothEmbedding I M I M where
  toFun := id
  invFun := id
  left_inv' := rfl
  isOpen_range := IsOpenMap.id.isOpen_range
  contMDiff_to := contMDiff_id
  contMDiffOn_inv := contMDiffOn_id


-- @@ L189-209 verbatim
variable {I M}

/- -- unused
@[simps!]
def comp {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E''] {H'' : Type*}
    [TopologicalSpace H''] {I'' : ModelWithCorners 𝕜 E'' H''} {M'' : Type*} [TopologicalSpace M'']
    [ChartedSpace H'' M''] [SmoothManifoldWithCorners I'' M'']
    (g : OpenSmoothEmbedding I' M' I'' M'') (f : OpenSmoothEmbedding I M I' M') :
    OpenSmoothEmbedding I M I'' M'' where
  toFun := g ∘ f
  invFun := f.invFun ∘ g.invFun
  left_inv' x := by simp only [Function.comp_apply, left_inv]
  isOpen_range := (g.isOpenMap.comp f.isOpenMap).isOpen_range
  smooth_to := g.smooth_to.comp f.smooth_to
  smooth_inv :=
    (f.smooth_inv.comp' g.smooth_inv).mono
      (by
        change range (g ∘ f) ⊆ range g ∩ g.inv_fun ⁻¹' range f
        refine subset_inter_iff.mpr ⟨range_comp_subset_range f g, ?_⟩
        rintro x' ⟨x, rfl⟩
        exact ⟨x, by simp only [left_inv]⟩) -/


-- @@ L211-211 verbatim
end OpenSmoothEmbedding


-- @@ L213-213 verbatim
namespace ContinuousLinearEquiv


-- @@ L215-217 verbatim
variable (e : E ≃L[𝕜] E') [CompleteSpace E] [CompleteSpace E']

-- unused

-- @@ L218-225 verbatim
@[simps]
def toOpenSmoothEmbedding : OpenSmoothEmbedding 𝓘(𝕜, E) E 𝓘(𝕜, E') E' where
  toFun := e
  invFun := e.symm
  left_inv' {x} := e.symm_apply_apply x
  isOpen_range := e.isOpenMap.isOpen_range
  contMDiff_to := (e : E →L[𝕜] E').contMDiff
  contMDiffOn_inv := (e.symm : E' →L[𝕜] E).contMDiff.contMDiffOn


-- @@ L227-227 verbatim
end ContinuousLinearEquiv


-- @@ L229-229 verbatim
end General


-- @@ L231-231 verbatim
section WithoutBoundary


-- @@ L233-233 verbatim
open Metric hiding mem_nhds_iff


-- @@ L235-235 verbatim
open Function


-- @@ L237-237 verbatim
universe u


-- @@ L239-246 verbatim
variable {F H : Type*} (M : Type u) [NormedAddCommGroup F] [NormedSpace ℝ F] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M]
  (IF : ModelWithCorners ℝ F H) [IsManifold IF ∞ M]

/- Clearly should be generalised. Maybe what we really want is a theory of local diffeomorphisms.

Note that the input `f` is morally an `OpenSmoothEmbedding` but stated in terms of `ContDiff`
instead of `ContMDiff`. This is more convenient for our purposes. -/

-- @@ L247-278 verbatim
def openSmoothEmbOfDiffeoSubsetChartTarget (x : M) {f : OpenPartialHomeomorph F F}
    (hf₁ : f.source = univ) (hf₂ : ContDiff ℝ ∞ f) (hf₃ : ContDiffOn ℝ ∞ f.symm f.target)
    (hf₄ : range f ⊆ IF '' (chartAt H x).target) : OpenSmoothEmbedding 𝓘(ℝ, F) F IF M
    where
  toFun := (extChartAt IF x).symm ∘ f
  invFun := f.invFun ∘ extChartAt IF x
  left_inv' {y} := by
    obtain ⟨z, hz, hz'⟩ := hf₄ (mem_range_self y)
    have aux : f.symm (IF z) = y := by rw [hz']; exact f.left_inv (hf₁.symm ▸ mem_univ _)
    simp [← hz', (chartAt H x).right_inv hz, aux]
  isOpen_range :=
    IsOpenMap.isOpen_range fun u hu ↦ by
      have aux : IsOpen (f '' u) := f.isOpen_image_of_subset_source hu (hf₁.symm ▸ subset_univ u)
      convert isOpen_extChartAt_preimage' x aux
      on_goal 1 => rw [image_comp]
      refine
        (extChartAt IF x).symm_image_eq_source_inter_preimage ((image_subset_range f u).trans ?_)
      rw [extChartAt, OpenPartialHomeomorph.extend_target']
      exact hf₄
  contMDiff_to := by
    refine (contMDiffOn_extChartAt_symm x).comp_contMDiff hf₂.contMDiff fun y ↦ ?_
    rw [extChartAt, OpenPartialHomeomorph.extend_target']
    exact hf₄ (mem_range_self y)
  contMDiffOn_inv := by
    rw [← OpenPartialHomeomorph.extend_target'] at hf₄
    have hf' : range ((extChartAt IF x).symm ∘ f) ⊆ extChartAt IF x ⁻¹' f.target := by
      rw [range_comp, ← image_subset_iff, ← f.image_source_eq_target, hf₁, image_univ]
      exact (PartialEquiv.image_symm_image_of_subset_target _ hf₄).subset
    have hf'' : range ((extChartAt IF x).symm ∘ f) ⊆ (chartAt H x).source := by
      rw [← extChartAt_source IF, range_comp, ← PartialEquiv.symm_image_target_eq_source]
      exact (monotone_image hf₄).trans Subset.rfl
    exact hf₃.contMDiffOn.comp (contMDiffOn_extChartAt.mono hf'') hf'


-- @@ L280-285 verbatim
@[simp]
theorem coe_openSmoothEmbOfDiffeoSubsetChartTarget (x : M) {f : OpenPartialHomeomorph F F}
    (hf₁ : f.source = univ) (hf₂ : ContDiff ℝ ∞ f) (hf₃ : ContDiffOn ℝ ∞ f.symm f.target)
    (hf₄ : range f ⊆ IF '' (chartAt H x).target) :
    (openSmoothEmbOfDiffeoSubsetChartTarget M IF x hf₁ hf₂ hf₃ hf₄ : F → M) =
      (extChartAt IF x).symm ∘ f := by simp [openSmoothEmbOfDiffeoSubsetChartTarget]


-- @@ L287-292 verbatim
theorem range_openSmoothEmbOfDiffeoSubsetChartTarget (x : M) {f : OpenPartialHomeomorph F F}
    (hf₁ : f.source = univ) (hf₂ : ContDiff ℝ ∞ f) (hf₃ : ContDiffOn ℝ ∞ f.symm f.target)
    (hf₄ : range f ⊆ IF '' (chartAt H x).target) :
    range (openSmoothEmbOfDiffeoSubsetChartTarget M IF x hf₁ hf₂ hf₃ hf₄) =
      (extChartAt IF x).symm '' range f := by
  rw [coe_openSmoothEmbOfDiffeoSubsetChartTarget, range_comp]


-- @@ L294-294 verbatim
variable {M} (F)

-- @@ L295-295 verbatim
variable [IF.Boundaryless] [FiniteDimensional ℝ F]

-- @@ L296-296 verbatim
variable [T2Space M] [LocallyCompactSpace M] [SigmaCompactSpace M]


-- @@ L298-346 verbatim
theorem nice_atlas' {ι : Type*} {s : ι → Set M} (s_op : ∀ j, IsOpen <| s j)
    (cov : (⋃ j, s j) = univ) (U : Set F) (hU₁ : (0 : F) ∈ U) (hU₂ : IsOpen U) :
    ∃ (ι' : Type u) (t : Set ι') (φ : t → OpenSmoothEmbedding 𝓘(ℝ, F) F IF M),
      t.Countable ∧
        (∀ i, ∃ j, range (φ i) ⊆ s j) ∧
          (LocallyFinite fun i ↦ range (φ i)) ∧ (⋃ i, φ i '' U) = univ := by
  set W : M → ℝ → Set M := fun x r ↦
    (extChartAt IF x).symm ∘ diffeomorphToNhd (extChartAt IF x x) r '' U with W_def
  let B : M → ℝ → Set M := ChartedSpace.ball IF
  let p : M → ℝ → Prop := fun x r ↦
    0 < r ∧ ball (extChartAt IF x x) r ⊆ (extChartAt IF x).target ∧ ∃ j, B x r ⊆ s j
  have hW₀ : ∀ x r, p x r → x ∈ W x r := fun x r h ↦ ⟨0, hU₁, by simp⟩
  have hW₁ : ∀ x r, p x r → IsOpen (W x r) := by
    rintro x r ⟨h₁, h₂, -, -⟩
    simp only [W_def]
    rw [image_comp]
    let V := diffeomorphToNhd (extChartAt IF x x) r '' U
    change IsOpen ((extChartAt IF x).symm '' V)
    have hV₁ : IsOpen V :=
      ((diffeomorphToNhd (extChartAt IF x x) r).isOpen_image_iff_of_subset_source (by simp)).mpr hU₂
    have hV₂ : V ⊆ (extChartAt IF x).target :=
      Subset.trans ((image_subset_range _ _).trans (by simp [h₁])) h₂
    rw [(extChartAt IF x).symm_image_eq_source_inter_preimage hV₂]
    exact isOpen_extChartAt_preimage' x hV₁
  have hB : ∀ x, (𝓝 x).HasBasis (p x) (B x) := fun x ↦
    ChartedSpace.nhds_hasBasis_balls_of_open_cov IF x s_op cov
  obtain ⟨t, ht₁, ht₂, ht₃, ht₄⟩ := exists_countable_locallyFinite_cover surjective_id hW₀ hW₁ hB
  let g : M × ℝ → OpenPartialHomeomorph F F := fun z ↦ diffeomorphToNhd (extChartAt IF z.1 z.1) z.2
  have hg₁ : ∀ z, (g z).source = univ := by simp [g]
  have hg₂ : ∀ z, ContDiff ℝ ∞ (g z) := by simp [g]
  have hg₃ : ∀ z, ContDiffOn ℝ ∞ (g z).symm (g z).target := by simp [g]
  refine ⟨M × ℝ, t,
    fun z ↦ openSmoothEmbOfDiffeoSubsetChartTarget M IF z.1.1 (hg₁ z.1) (hg₂ z.1) (hg₃ z.1) ?_, ht₁,
    fun z ↦ ?_, ?_, ?_⟩
  · obtain ⟨⟨x, r⟩, hxr⟩ := z
    obtain ⟨hr : 0 < r, hr' : ball (extChartAt IF x x) r ⊆ _, -⟩ := ht₂ _ hxr
    simp_rw [g, extChartAt]
    rw [← OpenPartialHomeomorph.extend_target']
    exact (range_diffeomorphToNhd_subset_ball (extChartAt IF x x) hr).trans hr'
  · obtain ⟨⟨x, r⟩, hxr⟩ := z
    obtain ⟨hr : 0 < r, -, j, hj : B x r ⊆ s j⟩ := ht₂ _ hxr
    simp_rw [range_openSmoothEmbOfDiffeoSubsetChartTarget]
    exact ⟨j, (monotone_image (range_diffeomorphToNhd_subset_ball _ hr)).trans hj⟩
  · simp_rw [range_openSmoothEmbOfDiffeoSubsetChartTarget]
    refine ht₄.subset ?_
    rintro ⟨⟨x, r⟩, hxr⟩
    obtain ⟨hr : 0 < r, -, -⟩ := ht₂ _ hxr
    exact monotone_image (range_diffeomorphToNhd_subset_ball _ hr)
  · simpa only [iUnion_coe_set] using! ht₃


-- @@ L348-348 verbatim
variable [Nonempty M]


-- @@ L350-363 verbatim
theorem nice_atlas {ι : Type*} {s : ι → Set M} (s_op : ∀ j, IsOpen <| s j)
    (cov : (⋃ j, s j) = univ) :
    ∃ n, ∃ φ : IndexType n → OpenSmoothEmbedding 𝓘(ℝ, F) F IF M,
        (∀ i, ∃ j, range (φ i) ⊆ s j) ∧
          (LocallyFinite fun i ↦ range (φ i)) ∧ (⋃ i, φ i '' ball 0 1) = univ := by
  obtain ⟨ι', t, φ, h₁, h₂, h₃, h₄⟩ := nice_atlas' F IF s_op cov (ball 0 1) (by simp) isOpen_ball
  have htne : t.Nonempty := by
    by_contra contra
    simp only [iUnion_coe_set, not_nonempty_iff_eq_empty.mp contra, mem_empty_iff_false,
      iUnion_of_empty, iUnion_empty, eq_comm (b := univ), univ_eq_empty_iff] at h₄
    exact not_isEmpty_of_nonempty M h₄
  obtain ⟨n, ⟨fn⟩⟩ := (Set.countable_iff_exists_nonempty_indexType_equiv htne).mp h₁
  refine ⟨n, φ ∘ fn, fun i ↦ h₂ (fn i), h₃.comp_injective fn.injective, ?_⟩
  erw [fn.surjective.iUnion_comp fun i ↦ φ i '' ball 0 1, h₄]


-- @@ L365-365 verbatim
end WithoutBoundary


-- @@ L367-367 verbatim
namespace OpenSmoothEmbedding


-- @@ L369-369 verbatim
section Updating


-- @@ L371-382 verbatim
variable {𝕜 EX EM EY EN EM' X M Y N M' : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EX] [NormedSpace 𝕜 EX] [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  [NormedAddCommGroup EM'] [NormedSpace 𝕜 EM'] [NormedAddCommGroup EY] [NormedSpace 𝕜 EY]
  [NormedAddCommGroup EN] [NormedSpace 𝕜 EN]
  {HX : Type*} [TopologicalSpace HX] {IX : ModelWithCorners 𝕜 EX HX}
  {HY : Type*} [TopologicalSpace HY] {IY : ModelWithCorners 𝕜 EY HY}
  {HM : Type*} [TopologicalSpace HM] {IM : ModelWithCorners 𝕜 EM HM}
  {HM' : Type*} [TopologicalSpace HM'] {IM' : ModelWithCorners 𝕜 EM' HM'}
  {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners 𝕜 EN HN}
  [TopologicalSpace X] [ChartedSpace HX X]
  [TopologicalSpace M] [ChartedSpace HM M]
  [TopologicalSpace M'] [ChartedSpace HM' M']


-- @@ L384-384 verbatim
section NonMetric


-- @@ L386-387 verbatim
variable [TopologicalSpace Y] [ChartedSpace HY Y] [TopologicalSpace N] [ChartedSpace HN N]
  (φ : OpenSmoothEmbedding IX X IM M) (ψ : OpenSmoothEmbedding IY Y IN N) (f : M → N) (g : X → Y)


-- @@ L389-389 verbatim
section


-- @@ L391-391 verbatim
attribute [local instance] Classical.dec


-- @@ L393-395 verbatim
/-- This is definition `def:update` in the blueprint. -/
def update (m : M) : N :=
  if m ∈ range φ then ψ (g (φ.invFun m)) else f m


-- @@ L397-397 verbatim
end


-- @@ L399-400 verbatim
@[simp]
theorem update_of_nmem_range {m : M} (hm : m ∉ range φ) : update φ ψ f g m = f m := if_neg hm


-- @@ L402-404 verbatim
@[simp]
theorem update_of_mem_range {m : M} (hm : m ∈ range φ) : update φ ψ f g m = ψ (g (φ.invFun m)) :=
  if_pos hm


-- @@ L406-408 verbatim
theorem update_apply_embedding (x : X) : update φ ψ f g (φ x) = ψ (g x) := by simp

-- This small auxiliary result is used in the next two lemmas.

-- @@ L409-416 verbatim
theorem nice_update_of_eq_outside_compact_aux {K : Set X} (g : X → Y)
    (hg : ∀ x : X, x ∉ K → f (φ x) = ψ (g x)) {m : M} (hm : m ∉ φ '' K) :
    φ.update ψ f g m = f m := by
  by_cases hm' : m ∈ range φ
  · obtain ⟨x, rfl⟩ := hm'
    replace hm : x ∉ K := by contrapose! hm; exact mem_image_of_mem φ hm
    simp [hg x hm]
  · exact if_neg hm'


-- @@ L418-418 verbatim
open Function


-- @@ L420-443 verbatim
/-- This is lemma `lem:smooth_updating` in the blueprint. -/
theorem contMDiff_update (f : M' → M → N) (g : M' → X → Y) {k : M' → M} {K : Set X}
    (hK : IsClosed (φ '' K)) (hf : CMDiff ∞ (uncurry f))
    (hg : CMDiff ∞ (uncurry g)) (hk : CMDiff ∞ k)
    (hg' : ∀ y x, x ∉ K → f y (φ x) = ψ (g y x)) :
    CMDiff ∞ fun x ↦ update φ ψ (f x) (g x) (k x) := by
  have hK' : ∀ x, k x ∉ φ '' K → update φ ψ (f x) (g x) (k x) = f x (k x) := fun x hx ↦
    nice_update_of_eq_outside_compact_aux φ ψ (f x) (g x) (hg' x) hx
  refine contMDiff_of_locally_contMDiffOn fun x ↦ ?_
  let U := range φ
  let V := (φ '' K)ᶜ
  have h₂ : IsOpen (k ⁻¹' V) := hK.isOpen_compl.preimage hk.continuous
  have h₃ : V ∪ U = univ := by
    rw [← compl_subset_iff_union, compl_compl]
    exact image_subset_range φ K
  have h₄ (x) : k x ∈ U → update φ ψ (f x) (g x) (k x) = (ψ ∘ g x ∘ φ.invFun) (k x) :=
    fun hm ↦ if_pos hm
  by_cases hx : k x ∈ U
  · exact ⟨k ⁻¹' U, φ.isOpen_range.preimage hk.continuous, hx,
      (contMDiffOn_congr h₄).mpr <| ψ.contMDiff_to.comp_contMDiffOn <| hg.comp_contMDiffOn
        (contMDiffOn_id.prodMk <| φ.contMDiffOn_inv.comp hk.contMDiffOn Subset.rfl)⟩
  · refine ⟨k ⁻¹' V, h₂, ?_, (contMDiffOn_congr hK').mpr
      (hf.comp ((contMDiff_id (n := ∞)).prodMk hk)).contMDiffOn⟩
    exact ((Set.ext_iff.mp h₃ (k x)).mpr trivial).resolve_right hx


-- @@ L445-445 verbatim
end NonMetric


-- @@ L447-447 verbatim
section Metric


-- @@ L449-451 verbatim
variable [MetricSpace Y] [ChartedSpace HY Y] [MetricSpace N] [ChartedSpace HN N]
  (φ : OpenSmoothEmbedding IX X IM M)
  (ψ : OpenSmoothEmbedding IY Y IN N) (f : M → N) (g : X → Y)


-- @@ L453-482 verbatim
/-- This is `lem:dist_updating` in the blueprint. -/
theorem dist_update [ProperSpace Y] {K : Set X} (hK : IsCompact K) {P : Type*} [MetricSpace P]
    {KP : Set P} (hKP : IsCompact KP) (f : P → M → N) (hf : Continuous ↿f)
    (hf' : ∀ p, f p '' range φ ⊆ range ψ) {ε : M → ℝ} (hε : ∀ m, 0 < ε m) (hε' : Continuous ε) :
    ∃ η > (0 : ℝ), ∀ g : P → X → Y, ∀ p ∈ KP, ∀ p' ∈ KP, ∀ x ∈ K,
      dist (g p' x) (ψ.invFun (f p (φ x))) < η →
        dist (update φ ψ (f p') (g p') <| φ x) (f p <| φ x) < ε (φ x) := by
  let F : P × X → Y := fun q ↦ (ψ.invFun ∘ f q.1 ∘ φ) q.2
  let K₁ := Metric.cthickening 1 (F '' KP.prod K)
  have hK₁ : IsCompact K₁ := by
    refine Metric.isCompact_of_isClosed_isBounded Metric.isClosed_cthickening
        (Bornology.IsBounded.cthickening <| IsCompact.isBounded <| ?_)
    apply (hKP.prod hK).image
    exact ψ.contMDiffOn_inv.continuousOn.comp_continuous
      (hf.comp <| continuous_fst.prodMk <| φ.continuous.comp continuous_snd) fun q ↦
      hf' q.1 ⟨φ q.2, mem_range_self _, rfl⟩
  have h₁ : UniformContinuousOn ψ K₁ :=
    hK₁.uniformContinuousOn_of_continuous ψ.continuous.continuousOn
  have hεφ : ∀ x ∈ K, 0 < (ε ∘ φ) x := fun x _hx ↦ hε _
  obtain ⟨ε₀, hε₀, hε₀'⟩ := hK.exists_forall_le' (hε'.comp φ.continuous).continuousOn hεφ
  obtain ⟨τ, hτ : 0 < τ, hτ'⟩ := Metric.uniformContinuousOn_iff.mp h₁ ε₀ hε₀
  refine ⟨min τ 1, by simp [hτ], fun g p hp p' _hp' x hx hη ↦ ?_⟩
  obtain ⟨H, H'⟩ := lt_min_iff.mp hη
  apply lt_of_lt_of_le _ (hε₀' x hx); clear hε₀'
  simp only [update_apply_embedding]
  have h₁ : g p' x ∈ K₁ :=
    Metric.mem_cthickening_of_dist_le (g p' x) (F (p, x)) 1 _ ⟨(p, x), ⟨hp, hx⟩, rfl⟩ H'.le
  have h₂ : f p (φ x) ∈ range ψ := hf' p ⟨φ x, mem_range_self _, rfl⟩
  rw [← ψ.right_inv h₂]
  exact hτ' _ h₁ _ (Metric.self_subset_cthickening _ ⟨(p, x), ⟨hp, hx⟩, rfl⟩) H


-- @@ L484-484 verbatim
end Metric


-- @@ L486-486 verbatim
end Updating


-- @@ L488-488 verbatim
end OpenSmoothEmbedding
