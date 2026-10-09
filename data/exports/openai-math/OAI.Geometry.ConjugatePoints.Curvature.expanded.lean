import OAI.Geometry.ConjugatePoints.Index
import OAI.Geometry.ConjugatePoints.CompactMetric


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-10 verbatim
/-!
# Local isometries, warped curvature, and compact curvature estimates.
-/


-- @@ L12-12 verbatim
section

-- @@ L13-13 verbatim
open Set Filter Topology Bundle Manifold IsManifold Matrix MeasureTheory

-- @@ L14-14 verbatim
open scoped ContDiff Matrix.Norms.Elementwise

-- @@ L15-15 verbatim
namespace ThreeManifold.RiemannianCoordinates

-- @@ L16-16 verbatim
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]


-- @@ L18-20 verbatim
def NonpositiveAt (g : SmoothMetric M) (p : M) : Prop :=
  ∀ c : OpenPartialHomeomorph M E3, c ∈ atlas E3 M → p ∈ c.source →
    ∀ u v : E3, chartBilin g c (c p) (curvatureTerm g c (c p) u v v) u ≤ 0


-- @@ L22-26 verbatim
lemma nonpositiveAt_of_nonpositive (g : SmoothMetric M)
    (h : NonpositiveSectionalCurvature g) (p : M) : NonpositiveAt g p := by
  intro c hc hp u v
  rw [← bilin_matrix]
  exact h c hc (c p) (c.map_source hp) u v


-- @@ L28-32 verbatim
lemma inner_self_nonneg (g : SmoothMetric M) (p : M) (v : TangentSpace I3 p) :
    0 ≤ g.inner p v v := by
  by_cases hv : v = 0
  · simp only [hv,map_zero,le_refl]
  · exact (g.pos p v hv).le


-- @@ L34-44 verbatim
lemma indexPairDensity_nonneg_of_nonpositiveAt (g : SmoothMetric M) {γ : ℝ → M}
    (J : ∀ s, TangentSpace I3 (γ s)) {s : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ s) (hn : NonpositiveAt g (γ s)) :
    0 ≤ indexPairDensity g γ J J s := by
  apply sub_nonneg.mpr
  apply le_trans _ (inner_self_nonneg g _ _)
  have hc := chart_mem_atlas E3 (γ s)
  have hsc := mem_chart_source E3 (γ s)
  rw [← metric_field_coordinates g (curvatureAlong g γ J) J hc hsc,
    curvatureAlong_coordinates g J hγ hc hsc]
  exact hn _ hc hsc _ _


-- @@ L46-64 verbatim
theorem nonnegativeIndex_of_passages (g : SmoothMetric M) {O : Set M} (hO : IsOpen O)
    (hn : ∀ p ∉ O, NonpositiveAt g p) {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U)
    (hp : ∀ (J : ∀ s, TangentSpace I3 (γ s)), SmoothFieldOn γ J U →
      HasCompactSupport J → tsupport J ⊆ U → ∀ x ∈ U ∩ γ ⁻¹' O,
      0 ≤ ∫ s in connectedComponentIn (U ∩ γ ⁻¹' O) x, indexPairDensity g γ J J s) :
    NonnegativeIndexOn g γ U := by
  intro J hJ hJc hJU
  apply GlobalAssembly.integral_nonneg_of_passages
    (hγ.continuousOn.isOpen_inter_preimage hU hO)
    (indexPairDensity_integrable g hU hγ hJ hJ hJc hJU) (hp J hJ hJc hJU)
  intro s hs
  by_cases hsU : s ∈ U
  · exact indexPairDensity_nonneg_of_nonpositiveAt g J (hγ.contMDiffAt (hU.mem_nhds hsU))
      (hn (γ s) (fun hsO => hs ⟨hsU,hsO⟩))
  · have hz : indexPairDensity g γ J J s = 0 := by
      by_contra hh
      exact hsU (hJU (indexPairDensity_support g γ J J hh))
    simp only [hz,le_refl]


-- @@ L66-75 verbatim
theorem noConjugatePoints_of_passages (g : SmoothMetric M) {O : Set M} (hO : IsOpen O)
    (hn : ∀ p ∉ O, NonpositiveAt g p)
    (hp : ∀ (U : Set ℝ), IsOpen U → OrdConnected U → ∀ γ : ℝ → M,
      IsGeodesicOn g γ U → ∀ (J : ∀ s, TangentSpace I3 (γ s)), SmoothFieldOn γ J U →
      HasCompactSupport J → tsupport J ⊆ U → ∀ x ∈ U ∩ γ ⁻¹' O,
      0 ≤ ∫ s in connectedComponentIn (U ∩ γ ⁻¹' O) x, indexPairDensity g γ J J s) :
    NoConjugatePoints g := by
  apply noConjugatePoints_of_intrinsic_index
  intro U hU hUc γ hγ
  exact nonnegativeIndex_of_passages g hO hn hU hγ.1 (hp U hU hUc γ hγ)


-- @@ L77-89 verbatim
theorem noConjugatePoints_of_nonpositive (g : SmoothMetric M)
    (hn : NonpositiveSectionalCurvature g) : NoConjugatePoints g := by
  apply noConjugatePoints_of_intrinsic_index
  intro U hU hUc γ hγ J hJ hJc hJU
  apply integral_nonneg
  intro s
  by_cases hs : s ∈ U
  · exact indexPairDensity_nonneg_of_nonpositiveAt g J (hγ.1.contMDiffAt (hU.mem_nhds hs))
      (nonpositiveAt_of_nonpositive g hn (γ s))
  · have hz : indexPairDensity g γ J J s = 0 := by
      by_contra hh
      exact hs (hJU (indexPairDensity_support g γ J J hh))
    simp only [hz,Pi.zero_apply,le_refl]

-- @@ L90-90 verbatim
end ThreeManifold.RiemannianCoordinates

-- @@ L91-91 verbatim
end


-- @@ L93-93 verbatim
section

-- @@ L94-94 verbatim
open Set Filter Topology Bundle Manifold IsManifold Matrix

-- @@ L95-95 verbatim
open scoped ContDiff Matrix.Norms.Elementwise

-- @@ L96-96 verbatim
namespace ThreeManifold.RiemannianCoordinates.LocalMetricIsometry

-- @@ L97-98 verbatim
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]

-- @@ L99-100 verbatim
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)


-- @@ L102-103 verbatim
def mapField (_P : LocalMetricIsometry g h f) (γ : ℝ → M) (J : ∀ s, TangentSpace I3 (γ s)) :
    ∀ s, TangentSpace I3 ((f ∘ γ) s) := fun s => mfderiv I3 I3 f (γ s) (J s)


-- @@ L105-135 verbatim
lemma coordinate_derivative {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 N) {p : M}
    (hp : p ∈ P.domain) (hpc : p ∈ c.source) (hpd : f p ∈ d.source) (u : TangentSpace I3 p) :
    mfderiv I3 I3 d (f p) (mfderiv I3 I3 f p u) =
      fderiv ℝ (d ∘ f ∘ c.symm) (c p) (mfderiv I3 I3 c p u) := by
  have hcs := (mdifferentiable_of_mem_atlas (I := I3) hc).mdifferentiableAt_symm (c.map_source hpc)
  have hfs := (P.smoothAt hp).mdifferentiableAt (by simp)
  have hds := (mdifferentiable_of_mem_atlas (I := I3) hd).mdifferentiableAt hpd
  have he : mfderiv I3 I3 (d ∘ f ∘ c.symm) (c p) =
      (mfderiv I3 I3 d (f p)).comp ((mfderiv I3 I3 f p).comp (mfderiv I3 I3 c.symm (c p))) := by
    rw [mfderiv_comp _ (show MDifferentiableAt I3 I3 d ((f ∘ c.symm) (c p)) by
      simpa only [Function.comp_apply,c.left_inv hpc] using hds)
        ((show MDifferentiableAt I3 I3 f (c.symm (c p)) by
          rw [c.left_inv hpc]; exact hfs).comp _ hcs),
      mfderiv_comp _ (show MDifferentiableAt I3 I3 f (c.symm (c p)) by
          rw [c.left_inv hpc]; exact hfs) hcs]
    let A : M → E3 →L[ℝ] E3 := fun q => mfderiv I3 I3 f q
    let D : N → E3 →L[ℝ] E3 := fun q => mfderiv I3 I3 d q
    let C : E3 →L[ℝ] E3 := mfderiv I3 I3 c.symm (c p)
    change (D (f (c.symm (c p)))).comp ((A (c.symm (c p))).comp C) =
      (D (f p)).comp ((A p).comp C)
    rw [c.left_inv hpc]
  have hi := congrArg (fun L => L u) ((mdifferentiable_of_mem_atlas (I := I3) hc).symm_comp_deriv hpc)
  change mfderiv I3 I3 c.symm (c p) (mfderiv I3 I3 c p u) = u at hi
  have he' := congrArg (fun L => L (mfderiv I3 I3 c p u)) he
  rw [mfderiv_eq_fderiv] at he'
  change fderiv ℝ (d ∘ f ∘ c.symm) (c p) (mfderiv I3 I3 c p u) =
    mfderiv I3 I3 d (f p) (mfderiv I3 I3 f p
      (mfderiv I3 I3 c.symm (c p) (mfderiv I3 I3 c p u))) at he'
  rw [hi] at he'
  exact he'.symm


-- @@ L137-143 verbatim
lemma mapField_coordinates {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 N) {γ : ℝ → M}
    (J : ∀ s, TangentSpace I3 (γ s)) {s : ℝ}
    (hp : γ s ∈ P.domain) (hpc : γ s ∈ c.source) (hpd : f (γ s) ∈ d.source) :
    fieldCoordinates (f ∘ γ) (P.mapField γ J) d s =
      fderiv ℝ (d ∘ f ∘ c.symm) (c (γ s)) (fieldCoordinates γ J c s) :=
  P.coordinate_derivative hc hd hp hpc hpd (J s)


-- @@ L145-149 verbatim
lemma comp_smooth {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hγP : MapsTo γ U P.domain) :
    ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ (f ∘ γ) U := by
  intro s hs
  exact ((P.smoothAt (hγP hs)).comp s (hγ.contMDiffAt (hU.mem_nhds hs))).contMDiffWithinAt


-- @@ L151-176 verbatim
lemma mapField_smooth {γ : ℝ → M} {J : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hγP : MapsTo γ U P.domain)
    (hJ : SmoothFieldOn γ J U) : SmoothFieldOn (f ∘ γ) (P.mapField γ J) U := by
  intro d hd s hs
  let c := chartAt E3 (γ s)
  have hc := chart_mem_atlas E3 (γ s)
  have hsc := mem_chart_source E3 (γ s)
  have hx : c (γ s) ∈ P.coordinateDomain c d := by
    refine ⟨⟨c.map_source hsc,?_⟩,?_⟩
    · change c.symm (c (γ s)) ∈ P.domain
      rw [c.left_inv hsc]
      exact hγP hs.1
    · change f (c.symm (c (γ s))) ∈ d.source
      rw [c.left_inv hsc]
      exact hs.2
  have hh := P.coordinate_smoothAt hc hd hx
  let : NormedAddCommGroup (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedSpace ℝ (E3 →L[ℝ] E3) := ContinuousLinearMap.toNormedSpace
  have hb := (hh.fderiv_right (m := ∞) (by simp)).comp s (curve_coordinates_smoothAt hU hγ hc hs.1 hsc)
  have he : fieldCoordinates (f ∘ γ) (P.mapField γ J) d =ᶠ[𝓝 s]
      (fun r => fderiv ℝ (d ∘ f ∘ c.symm) (c (γ r)) (fieldCoordinates γ J c r)) := by
    filter_upwards [hU.mem_nhds hs.1,
      (hγ.contMDiffAt (hU.mem_nhds hs.1)).continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hsc),
      ((P.comp_smooth hU hγ hγP).contMDiffAt (hU.mem_nhds hs.1)).continuousAt.preimage_mem_nhds (d.open_source.mem_nhds hs.2)] with r hr hrc hrd
    exact P.mapField_coordinates hc hd J (hγP hr) hrc hrd
  exact ((hb.clm_apply (smoothField_coordinatesAt hU hγ hJ hc hs.1 hsc)).congr_of_eventuallyEq he).contDiffWithinAt


-- @@ L178-185 verbatim
lemma coordinateDomain_mem {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3}
    {p : M} (hp : p ∈ P.domain) (hpc : p ∈ c.source) (hpd : f p ∈ d.source) :
    c p ∈ P.coordinateDomain c d := by
  refine ⟨⟨c.map_source hpc,?_⟩,?_⟩
  · change c.symm (c p) ∈ P.domain
    rw [c.left_inv hpc]; exact hp
  · change f (c.symm (c p)) ∈ d.source
    rw [c.left_inv hpc]; exact hpd


-- @@ L187-195 verbatim
lemma coordinate_curve_germ {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3}
    {γ : ℝ → M} {s : ℝ} (hγ : ContinuousAt γ s) (hpc : γ s ∈ c.source) :
    (d ∘ f ∘ γ) =ᶠ[𝓝 s] ((d ∘ f ∘ c.symm) ∘ (c ∘ γ)) := by
  let _ : ChartedSpace E3 M := inferInstance
  let _ : IsManifold I3 ∞ M := inferInstance
  let _ : ChartedSpace E3 N := inferInstance
  let _ : IsManifold I3 ∞ N := inferInstance
  filter_upwards [hγ.preimage_mem_nhds (c.open_source.mem_nhds hpc)] with r hr
  simp only [Function.comp_apply,c.left_inv hr]


-- @@ L197-206 verbatim
lemma mapField_coordinates_germ {c : OpenPartialHomeomorph M E3} {d : OpenPartialHomeomorph N E3}
    (hc : c ∈ atlas E3 M) (hd : d ∈ atlas E3 N) {γ : ℝ → M}
    (J : ∀ s, TangentSpace I3 (γ s)) {s : ℝ} (hγ : ContinuousAt γ s)
    (hp : γ s ∈ P.domain) (hpc : γ s ∈ c.source) (hpd : f (γ s) ∈ d.source) :
    fieldCoordinates (f ∘ γ) (P.mapField γ J) d =ᶠ[𝓝 s]
      (fun r => fderiv ℝ (d ∘ f ∘ c.symm) (c (γ r)) (fieldCoordinates γ J c r)) := by
  filter_upwards [hγ.preimage_mem_nhds (P.isOpen_domain.mem_nhds hp),
    hγ.preimage_mem_nhds (c.open_source.mem_nhds hpc),
    ((P.smoothAt hp).continuousAt.comp hγ).preimage_mem_nhds (d.open_source.mem_nhds hpd)] with r hr hrc hrd
  exact P.mapField_coordinates hc hd J hr hrc hrd


-- @@ L208-237 verbatim
lemma covariantDerivative_map {γ : ℝ → M} {J : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hγP : MapsTo γ U P.domain)
    (hJ : SmoothFieldOn γ J U) {s : ℝ} (hs : s ∈ U) :
    covariantDerivative h (f ∘ γ) (P.mapField γ J) s =
      mfderiv I3 I3 f (γ s) (covariantDerivative g γ J s) := by
  let c := chartAt E3 (γ s)
  let d := chartAt E3 (f (γ s))
  have hc := chart_mem_atlas E3 (γ s)
  have hd := chart_mem_atlas E3 (f (γ s))
  have hpc := mem_chart_source E3 (γ s)
  have hpd := mem_chart_source E3 (f (γ s))
  have hy := P.comp_smooth hU hγ hγP
  have hH := P.mapField_smooth hU hγ hγP hJ
  have hcs := smoothField_coordinatesAt hU hγ hJ hc hs hpc
  have hds := smoothField_coordinatesAt hU hy hH hd hs hpd
  apply (mdifferentiable_of_mem_atlas (I := I3) hd).mfderiv_injective hpd
  change fieldCoordinates (f ∘ γ) (covariantDerivative h (f ∘ γ) (P.mapField γ J)) d s =
    fieldCoordinates (f ∘ γ) (P.mapField γ (covariantDerivative g γ J)) d s
  rw [covariantDerivative_coordinates h (hy.contMDiffAt (hU.mem_nhds hs))
    (hds.differentiableAt (by simp)) hd hpd,
    P.mapField_coordinates hc hd (covariantDerivative g γ J) (hγP hs) hpc hpd,
    covariantDerivative_coordinates g (hγ.contMDiffAt (hU.mem_nhds hs))
      (hcs.differentiableAt (by simp)) hc hpc]
  have he := (P.coordinates hc hd).along hc hd
    ((curve_coordinates_smoothAt hU hγ hc hs hpc).differentiableAt (by simp))
    (hcs.differentiableAt (by simp)) (P.coordinateDomain_mem (hγP hs) hpc hpd)
  refine (along_congr h d (coordinate_curve_germ (f := f) (d := d)
    (hγ.contMDiffAt (hU.mem_nhds hs)).continuousAt hpc)
    (P.mapField_coordinates_germ hc hd J (hγ.contMDiffAt (hU.mem_nhds hs)).continuousAt
      (hγP hs) hpc hpd)).trans he


-- @@ L239-244 verbatim
lemma velocity_map {γ : ℝ → M} {s : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ s) (hp : γ s ∈ P.domain) :
    velocity (f ∘ γ) s = mfderiv I3 I3 f (γ s) (velocity γ s) := by
  have he := mfderiv_comp s ((P.smoothAt hp).mdifferentiableAt (by simp))
    (hγ.mdifferentiableAt (by simp))
  exact congrArg (fun L => L 1) he


-- @@ L246-278 verbatim
lemma curvatureAlong_map {γ : ℝ → M} (J : ∀ s, TangentSpace I3 (γ s)) {s : ℝ}
    (hγ : ContMDiffAt 𝓘(ℝ,ℝ) I3 ∞ γ s) (hp : γ s ∈ P.domain) :
    curvatureAlong h (f ∘ γ) (P.mapField γ J) s =
      mfderiv I3 I3 f (γ s) (curvatureAlong g γ J s) := by
  let c := chartAt E3 (γ s)
  let d := chartAt E3 (f (γ s))
  have hc := chart_mem_atlas E3 (γ s)
  have hd := chart_mem_atlas E3 (f (γ s))
  have hpc := mem_chart_source E3 (γ s)
  have hpd := mem_chart_source E3 (f (γ s))
  have hy := (P.smoothAt hp).comp s hγ
  apply (mdifferentiable_of_mem_atlas (I := I3) hd).mfderiv_injective hpd
  change fieldCoordinates (f ∘ γ) (curvatureAlong h (f ∘ γ) (P.mapField γ J)) d s =
    fieldCoordinates (f ∘ γ) (P.mapField γ (curvatureAlong g γ J)) d s
  rw [curvatureAlong_coordinates h (P.mapField γ J) hy hd hpd,
    P.mapField_coordinates hc hd J hp hpc hpd,
    P.mapField_coordinates hc hd (curvatureAlong g γ J) hp hpc hpd,
    curvatureAlong_coordinates g J hγ hc hpc]
  have hv : deriv (d ∘ (f ∘ γ)) s =
      fderiv ℝ (d ∘ f ∘ c.symm) (c (γ s)) (deriv (c ∘ γ) s) := by
    rw [← velocity_coordinates hy hd hpd,← velocity_coordinates hγ hc hpc]
    change mfderiv I3 I3 d (f (γ s)) (velocity (f ∘ γ) s) = _
    rw [P.velocity_map hγ hp]
    exact P.coordinate_derivative hc hd hp hpc hpd _
  rw [hv]
  have he := (P.coordinates hc hd).curvature hc hd
    (P.coordinateDomain_mem hp hpc hpd) (fieldCoordinates γ J c s)
      (deriv (c ∘ γ) s) (deriv (c ∘ γ) s)
  dsimp only at he
  have hp' : (d ∘ f ∘ c.symm) (c (γ s)) = d (f (γ s)) := by
    simp only [Function.comp_apply,c.left_inv hpc]
  rw [hp'] at he
  exact he


-- @@ L280-299 verbatim
lemma nonpositiveAt (p : M) (hp : p ∈ P.domain) (hn : NonpositiveAt h (f p)) :
    NonpositiveAt g p := by
  intro c hc hpc u v
  let d := chartAt E3 (f p)
  have hd := chart_mem_atlas E3 (f p)
  have hpd := mem_chart_source E3 (f p)
  have hx := P.coordinateDomain_mem hp hpc hpd
  let F := d ∘ f ∘ c.symm
  let A := fderiv ℝ F (c p)
  have hp' : F (c p) = d (f p) := by
    simp only [F,Function.comp_apply,c.left_inv hpc]
  have he := P.coordinate_metric hc hd hx (curvatureTerm g c (c p) u v v) u
  have hR := (P.coordinates hc hd).curvature hc hd hx u v v
  change curvatureTerm h d (F (c p)) (A u) (A v) (A v) =
    A (curvatureTerm g c (c p) u v v) at hR
  change chartBilin g c (c p) (curvatureTerm g c (c p) u v v) u =
    chartBilin h d (F (c p)) (A (curvatureTerm g c (c p) u v v)) (A u) at he
  rw [← hR,hp'] at he
  rw [he]
  exact hn d hd hpd (A u) (A v)


-- @@ L301-312 verbatim
lemma indexPairDensity_map {γ : ℝ → M} {J K : ∀ s, TangentSpace I3 (γ s)} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hγP : MapsTo γ U P.domain)
    (hJ : SmoothFieldOn γ J U) (hK : SmoothFieldOn γ K U) {s : ℝ} (hs : s ∈ U) :
    indexPairDensity h (f ∘ γ) (P.mapField γ J) (P.mapField γ K) s =
      indexPairDensity g γ J K s := by
  unfold indexPairDensity
  rw [P.covariantDerivative_map hU hγ hγP hJ hs,
    P.covariantDerivative_map hU hγ hγP hK hs,
    P.curvatureAlong_map J (hγ.contMDiffAt (hU.mem_nhds hs)) (hγP hs)]
  exact congrArg₂ (· - ·)
    (P.metric _ (hγP hs) (covariantDerivative g γ J s) (covariantDerivative g γ K s)).symm
    (P.metric _ (hγP hs) (curvatureAlong g γ J s) (K s)).symm

-- @@ L313-313 verbatim
end ThreeManifold.RiemannianCoordinates.LocalMetricIsometry


-- @@ L315-315 verbatim
namespace ThreeManifold.RiemannianCoordinates

-- @@ L316-317 verbatim
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]

-- @@ L318-326 verbatim
lemma covariantDerivative_germ (g : SmoothMetric M) {γ : ℝ → M}
    {J K : ∀ s, TangentSpace I3 (γ s)} {s : ℝ} (he : J =ᶠ[𝓝 s] K) :
    covariantDerivative g γ J s = covariantDerivative g γ K s := by
  simp only [covariantDerivative]
  congr 1
  apply along_congr g _ Filter.EventuallyEq.rfl
  filter_upwards [he] with r hr
  unfold fieldCoordinates
  rw [hr]

-- @@ L327-341 verbatim
lemma geodesic_of_acceleration_zero (g : SmoothMetric M) {γ : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U)
    (hz : ∀ s ∈ U, covariantDerivative g γ (velocity γ) s = 0) : IsGeodesicOn g γ U := by
  refine ⟨hγ,?_⟩
  intro c hc s hs hsc
  have he : fieldCoordinates γ (velocity γ) c =ᶠ[𝓝 s] deriv (c ∘ γ) := by
    filter_upwards [hU.mem_nhds hs,
      (hγ.contMDiffAt (hU.mem_nhds hs)).continuousAt.preimage_mem_nhds (c.open_source.mem_nhds hsc)] with r hr hrc
    exact velocity_coordinates (hγ.contMDiffAt (hU.mem_nhds hr)) hc hrc
  rw [← along_congr g c Filter.EventuallyEq.rfl he,
    ← covariantDerivative_coordinates g (hγ.contMDiffAt (hU.mem_nhds hs))
      ((smoothField_coordinatesAt hU hγ (velocity_smooth hU hγ)
        (chart_mem_atlas E3 (γ s)) hs (mem_chart_source E3 (γ s))).differentiableAt (by simp)) hc hsc]
  change mfderiv I3 I3 c (γ s) (covariantDerivative g γ (velocity γ) s) = 0
  rw [hz s hs,map_zero]


-- @@ L343-343 verbatim
namespace LocalMetricIsometry

-- @@ L344-345 verbatim
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)

-- @@ L346-356 verbatim
lemma geodesic_map {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hγ : IsGeodesicOn g γ U) (hγP : MapsTo γ U P.domain) :
    IsGeodesicOn h (f ∘ γ) U := by
  apply geodesic_of_acceleration_zero h hU (P.comp_smooth hU hγ.1 hγP)
  intro s hs
  have he : velocity (f ∘ γ) =ᶠ[𝓝 s] P.mapField γ (velocity γ) := by
    filter_upwards [hU.mem_nhds hs] with r hr
    exact P.velocity_map (hγ.1.contMDiffAt (hU.mem_nhds hr)) (hγP hr)
  rw [covariantDerivative_germ h he,
    P.covariantDerivative_map hU hγ.1 hγP (velocity_smooth hU hγ.1) hs,
    geodesic_acceleration_zero g hU hγ hs,map_zero]

-- @@ L357-357 verbatim
end LocalMetricIsometry

-- @@ L358-358 verbatim
end ThreeManifold.RiemannianCoordinates


-- @@ L360-360 verbatim
namespace ThreeManifold.WarpedCurvature

-- @@ L361-361 verbatim
open Neck RiemannianCoordinates


-- @@ L363-363 verbatim
def diag (a b : ℝ) : TMat := !![a,0;0,b]

-- @@ L364-365 verbatim
lemma diag_transpose (a b : ℝ) : (diag a b)ᵀ = diag a b := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

-- @@ L366-367 verbatim
lemma diag_mul (a b c d : ℝ) : diag a b * diag c d = diag (a*c) (b*d) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [diag,Matrix.mul_apply,Fin.sum_univ_two]

-- @@ L368-370 verbatim
lemma diag_pairing (a b : ℝ) (u v : TVec) : pairing (diag a b) u v = a*u 0*v 0+b*u 1*v 1 := by
  simp [pairing,dotProduct,Matrix.mulVec,Fin.sum_univ_two,diag]
  ring

-- @@ L371-382 verbatim
lemma diag_deriv {a b : ℝ → ℝ} {a' b' s : ℝ}
    (ha : HasDerivAt a a' s) (hb : HasDerivAt b b' s) :
    HasDerivAt (fun t => diag (a t) (b t)) (diag a' b') s := by
  apply hasDerivAt_pi.mpr
  intro i
  apply hasDerivAt_pi.mpr
  intro j
  fin_cases i <;> fin_cases j
  · exact ha
  · exact hasDerivAt_const _ _
  · exact hasDerivAt_const _ _
  · exact hb


-- @@ L384-384 verbatim
def Q (r : ℝ → ℝ) (c t : ℝ) := diag ((r t)^2) (c^2)

-- @@ L385-385 verbatim
def P (r : ℝ → ℝ) (c t : ℝ) := diag ((r t)^2)⁻¹ (c^2)⁻¹

-- @@ L386-386 verbatim
def A (r : ℝ → ℝ) (t : ℝ) := diag (2*r t*deriv r t) 0

-- @@ L387-387 verbatim
def B (r : ℝ → ℝ) (t : ℝ) := diag (2*(deriv r t)^2+2*r t*deriv (deriv r) t) 0

-- @@ L388-392 verbatim
lemma QP (r : ℝ → ℝ) {c t : ℝ} (hr : r t ≠ 0) (hc : c ≠ 0) :
    Q r c t * P r c t = 1 := by
  rw [Q,P,diag_mul]
  simp only [mul_inv_cancel₀ (pow_ne_zero 2 hr),mul_inv_cancel₀ (pow_ne_zero 2 hc)]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [diag]

-- @@ L393-397 verbatim
lemma PQ (r : ℝ → ℝ) {c t : ℝ} (hr : r t ≠ 0) (hc : c ≠ 0) :
    P r c t * Q r c t = 1 := by
  rw [P,Q,diag_mul]
  simp only [inv_mul_cancel₀ (pow_ne_zero 2 hr),inv_mul_cancel₀ (pow_ne_zero 2 hc)]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num [diag]

-- @@ L398-400 verbatim
lemma Q_deriv {r : ℝ → ℝ} (hs : ContDiff ℝ ∞ r) (c t : ℝ) : HasDerivAt (Q r c) (A r t) t := by
  change HasDerivAt (fun s => diag ((r s)^2) (c^2)) (diag (2*r t*deriv r t) 0) t
  simpa only [Pi.pow_apply,Nat.reduceSub,Nat.cast_ofNat,pow_one] using diag_deriv (((hs.differentiable (by simp)) t).hasDerivAt.pow 2) (hasDerivAt_const t (c^2))

-- @@ L401-408 verbatim
lemma A_deriv {r : ℝ → ℝ} (hs : ContDiff ℝ ∞ r) (t : ℝ) : HasDerivAt (A r) (B r t) t := by
  have h := (((hs.differentiable (by simp)) t).hasDerivAt.const_mul 2).mul
    ((((contDiff_infty_iff_deriv.mp hs).2).differentiable (by simp) t).hasDerivAt)
  convert diag_deriv h (hasDerivAt_const t (0:ℝ)) using 1
  · rfl
  · simp only [B]
    congr 1
    ring

-- @@ L409-417 verbatim
lemma P_deriv {r : ℝ → ℝ} (hs : ContDiff ℝ ∞ r) (hr : ∀ t, r t ≠ 0)
    {c : ℝ} (hc : c ≠ 0) (t : ℝ) :
    HasDerivAt (P r c) (-P r c t * A r t * P r c t) t := by
  have hd := diag_deriv ((((hs.differentiable (by simp)) t).hasDerivAt.pow 2).inv (pow_ne_zero 2 (hr t)))
    (hasDerivAt_const t ((c^2)⁻¹))
  have he := inverse_first_jet (Q_deriv hs c t) hd
    (Filter.Eventually.of_forall (fun s => QP r (hr s) hc)) (PQ r (hr t) hc)
  rw [he] at hd
  exact hd


-- @@ L419-430 verbatim
lemma curvature_scalar {r : ℝ → ℝ} {c t : ℝ} (hr : r t ≠ 0) (hc : c ≠ 0)
    (V T : Vec) :
    metric (Q r c t) V (curvatureJet (P r c t) (A r t) (B r t) V T T) =
      -(r t * deriv (deriv r) t) * (V.1*T.2 0-T.1*V.2 0)^2 := by
  have hP : (P r c t)ᵀ = P r c t := diag_transpose _ _
  have hA : (A r t)ᵀ = A r t := diag_transpose _ _
  have hB : (B r t)ᵀ = B r t := diag_transpose _ _
  rw [curvature_contraction (QP r hr hc) hP hA hB]
  simp only [P,A,B,diag_mul,diag_pairing,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,
    zero_mul,add_zero]
  field_simp [hr]
  ring


-- @@ L432-432 verbatim
variable {M : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]

-- @@ L433-440 verbatim
lemma metric_of_block (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3) {x : E3} {Q : TMat}
    (he : metricMatrix g c x = blockMatrix Q) (u v : E3) :
    chartBilin g c x u v = metric Q (splitVector u) (splitVector v) := by
  rw [← bilin_matrix]
  change ∑ i, ∑ j, metricMatrix g c x i j * u i * v j = _
  rw [he]
  simp [blockMatrix,metric,splitVector,pairing,dotProduct,Matrix.mulVec,Fin.sum_univ_three,Fin.sum_univ_two]
  ring


-- @@ L442-451 verbatim
lemma warped_curvature (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    {r : ℝ → ℝ} (hs : ContDiff ℝ ∞ r) (hr : ∀ t, r t ≠ 0) {b : ℝ} (hb : b ≠ 0)
    {x : E3} (hg : metricMatrix g c =ᶠ[𝓝 x] fun y => blockMatrix (Q r b (y 0))) (u v : E3) :
    chartBilin g c x (curvatureTerm g c x u v v) u =
      -(r (x 0)*deriv (deriv r) (x 0))*(u 0*v 1-v 0*u 1)^2 := by
  have hj : ∀ᶠ t in 𝓝 (x 0), HasDerivAt (Q r b) (A r t) t ∧ Q r b t * P r b t = 1 ∧ (A r t)ᵀ = A r t :=
    Filter.Eventually.of_forall (fun t => ⟨Q_deriv hs b t,QP r (hr t) hb,diag_transpose _ _⟩)
  rw [curvatureTerm_product g c hg hj (P_deriv hs hr hb (x 0)) (A_deriv hs (x 0)),
    metric_of_block g c hg.eq_of_nhds,split_join,metric_symm (show (Q r b (x 0))ᵀ = Q r b (x 0) from diag_transpose _ _),curvature_scalar (hr (x 0)) hb]
  rfl

-- @@ L452-458 verbatim
lemma warped_nonpositive (g : SmoothMetric M) (c : OpenPartialHomeomorph M E3)
    {r : ℝ → ℝ} (hs : ContDiff ℝ ∞ r) (hr : ∀ t, 0 < r t) {b : ℝ} (hb : b ≠ 0)
    {x : E3} (hg : metricMatrix g c =ᶠ[𝓝 x] fun y => blockMatrix (Q r b (y 0)))
    (hconv : 0 ≤ deriv (deriv r) (x 0)) (u v : E3) :
    chartBilin g c x (curvatureTerm g c x u v v) u ≤ 0 := by
  rw [warped_curvature g c hs (fun t => (hr t).ne') hb hg]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg (hr _).le hconv)) (sq_nonneg _)

-- @@ L459-459 verbatim
end ThreeManifold.WarpedCurvature

-- @@ L460-460 verbatim
end


-- @@ L462-462 verbatim
section

-- @@ L463-463 verbatim
open Set Filter Topology Bundle Manifold IsManifold

-- @@ L464-464 verbatim
open scoped ContDiff

-- @@ L465-465 verbatim
namespace ThreeManifold.Rechart

-- @@ L466-466 verbatim
open MetricConstruction RiemannianCoordinates

-- @@ L467-468 verbatim
variable {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

-- @@ L469-470 verbatim
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace N] [ChartedSpace F N] [IsManifold 𝓘(ℝ,F) ∞ N]


-- @@ L472-479 verbatim
def realMetric (e : E ≃L[ℝ] E3) (g : Metric (E := E) M) :
    letI := charts (M := M) e
    letI := isManifold (M := M) e
    SmoothMetric M := by
  letI := charts (M := M) e
  letI := isManifold (M := M) e
  exact pullbackHomeomorph g (Homeomorph.refl M)
    (identity_smooth_backward e) (identity_smooth_forward e)


-- @@ L481-489 verbatim
lemma map_smoothAt (e : E ≃L[ℝ] E3) (d : F ≃L[ℝ] E3) {f : M → N} {p : M}
    (hf : ContMDiffAt 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f p) :
    letI := charts (M := M) e
    letI := charts (M := N) d
    ContMDiffAt I3 I3 ∞ f p := by
  let := charts (M := M) e
  let := charts (M := N) d
  exact ((identity_smooth_forward d (f p)).comp p hf).comp p
    (identity_smooth_backward e p)


-- @@ L491-520 verbatim
def realIsometry (e : E ≃L[ℝ] E3) (d : F ≃L[ℝ] E3)
    (g : Metric (E := E) M) (h : Metric (E := F) N) (f : M → N)
    (U : Set M) (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℝ,E) 𝓘(ℝ,F) ∞ f U)
    (hm : ∀ p ∈ U, pullInner (E := E) h f p = g.inner p) :
    letI := charts (M := M) e
    letI := isManifold (M := M) e
    letI := charts (M := N) d
    letI := isManifold (M := N) d
    LocalMetricIsometry (realMetric e g) (realMetric d h) f := by
  letI := charts (M := M) e
  letI := isManifold (M := M) e
  letI := charts (M := N) d
  letI := isManifold (M := N) d
  have hs (p : M) (hp : p ∈ U) := hf.contMDiffAt (hU.mem_nhds hp)
  refine ⟨U,hU,fun p hp => (map_smoothAt e d (hs p hp)).contMDiffWithinAt,?_⟩
  intro p hp u v
  have h₁ := pull_composition h
    ((identity_smooth_backward e p).mdifferentiableAt (by simp))
    ((hs p hp).mdifferentiableAt (by simp))
  have h₂ := pull_composition h
    ((map_smoothAt e d (hs p hp)).mdifferentiableAt (by simp))
    ((identity_smooth_backward d (f p)).mdifferentiableAt (by simp))
  change pullInner (E := E3) h f p =
    pullBilin (E := E3) (F := E) (pullInner (E := E) h f p)
      (mfderiv I3 𝓘(ℝ,E) (id : M → M) p) at h₁
  rw [hm p hp] at h₁
  change pullInner (E := E3) h f p = _ at h₂
  have he := h₁.symm.trans h₂
  exact congrArg (fun b : E3 →L[ℝ] E3 →L[ℝ] ℝ => b u v) he


-- @@ L522-522 verbatim
variable {X : Type} [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]

-- @@ L523-541 verbatim
def realTargetIsometry (d : F ≃L[ℝ] E3)
    (g : SmoothMetric X) (h : Metric (E := F) N) (f : X → N)
    (U : Set X) (hU : IsOpen U)
    (hf : ContMDiffOn I3 𝓘(ℝ,F) ∞ f U)
    (hm : ∀ p ∈ U, pullInner (E := E3) h f p = g.inner p) :
    letI := charts (M := N) d
    letI := isManifold (M := N) d
    LocalMetricIsometry g (realMetric d h) f := by
  letI := charts (M := N) d
  letI := isManifold (M := N) d
  have hs (p : X) (hp : p ∈ U) : ContMDiffAt I3 I3 ∞ f p :=
    (identity_smooth_forward d (f p)).comp p (hf.contMDiffAt (hU.mem_nhds hp))
  refine ⟨U,hU,fun p hp => (hs p hp).contMDiffWithinAt,?_⟩
  intro p hp u v
  have h₂ := pull_composition h ((hs p hp).mdifferentiableAt (by simp))
    ((identity_smooth_backward d (f p)).mdifferentiableAt (by simp))
  change pullInner (E := E3) h f p = _ at h₂
  rw [hm p hp] at h₂
  exact congrArg (fun b : E3 →L[ℝ] E3 →L[ℝ] ℝ => b u v) h₂

-- @@ L542-542 verbatim
end ThreeManifold.Rechart


-- @@ L544-544 verbatim
namespace ThreeManifold.CylinderConstruction

-- @@ L545-545 verbatim
open MetricConstruction RiemannianCoordinates

-- @@ L546-546 verbatim
local instance : ChartedSpace E3 Cylinder := Rechart.charts coordinates

-- @@ L547-547 verbatim
local instance : IsManifold I3 ∞ Cylinder := Rechart.isManifold coordinates

-- @@ L548-550 verbatim
variable {r s c : ℝ → ℝ}
    (h1 : ContDiff ℝ ∞ r) (h2 : ContDiff ℝ ∞ s) (h3 : ContDiff ℝ ∞ c)
    (hr : ∀ t, r t ≠ 0) (hs : ∀ t, s t ≠ 0)

-- @@ L551-553 verbatim
def euclideanMetric : SmoothMetric E3 :=
  triangularMetric (h1.comp (contDiff_apply ℝ ℝ 0)) (h2.comp (contDiff_apply ℝ ℝ 0))
    (h3.comp (contDiff_apply ℝ ℝ 0)) (fun _ => hr _) (fun _ => hs _)

-- @@ L554-554 verbatim
def realMetric : SmoothMetric Cylinder := Rechart.realMetric coordinates (metric h1 h2 h3 hr hs)

-- @@ L555-555 verbatim
def euclideanProjection : E3 → Cylinder := projection ∘ coordinates.symm

-- @@ L556-558 verbatim
lemma euclideanProjection_smooth :
    ContMDiff I3 𝓘(ℝ,P) ∞ euclideanProjection := by
  exact projection_smooth.comp coordinates.symm.contDiff.contMDiff

-- @@ L559-572 verbatim
lemma euclideanProjection_metric (x : E3) :
    pullInner (E := E3) (metric h1 h2 h3 hr hs) euclideanProjection x =
      (euclideanMetric h1 h2 h3 hr hs).inner x := by
  rw [euclideanProjection,pull_composition _
    (((show ContMDiff I3 𝓘(ℝ,P) ∞ coordinates.symm from coordinates.symm.contDiff.contMDiff) x).mdifferentiableAt (by simp))
    ((projection_smooth _).mdifferentiableAt (by simp)),metric_projection]
  ext u v
  change (lifted h1 h2 h3 hr hs).inner (coordinates.symm x)
    (mfderiv I3 𝓘(ℝ,P) coordinates.symm x u)
    (mfderiv I3 𝓘(ℝ,P) coordinates.symm x v) = _
  rw [mfderiv_eq_fderiv,coordinates.symm.hasFDerivAt.fderiv,lifted_apply]
  exact (triangularMetric_apply (h1.comp (contDiff_apply ℝ ℝ 0))
    (h2.comp (contDiff_apply ℝ ℝ 0)) (h3.comp (contDiff_apply ℝ ℝ 0))
    (fun _ => hr _) (fun _ => hs _) x u v).symm


-- @@ L574-577 verbatim
def projectionIsometry : LocalMetricIsometry (euclideanMetric h1 h2 h3 hr hs)
    (realMetric h1 h2 h3 hr hs) euclideanProjection :=
  Rechart.realTargetIsometry coordinates _ _ _ univ isOpen_univ
    euclideanProjection_smooth.contMDiffOn (fun x _ => euclideanProjection_metric h1 h2 h3 hr hs x)

-- @@ L578-578 verbatim
end ThreeManifold.CylinderConstruction


-- @@ L580-580 verbatim
namespace ThreeManifold.RiemannianCoordinates

-- @@ L581-582 verbatim
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]

-- @@ L583-596 verbatim
lemma nonpositiveAt_of_chart (g : SmoothMetric M) {p : M}
    {d : OpenPartialHomeomorph M E3} (hd : d ∈ atlas E3 M) (hpd : p ∈ d.source)
    (hn : ∀ u v : E3, chartBilin g d (d p) (curvatureTerm g d (d p) u v v) u ≤ 0) :
    NonpositiveAt g p := by
  intro c hc hpc u v
  have hp : c.symm (c p) ∈ d.source := by rw [c.left_inv hpc]; exact hpd
  have he := chart_metric_transform g hc hd (c.map_source hpc) hp
    (curvatureTerm g c (c p) u v v) u
  have hR := curvature_change g hc hd (c.map_source hpc) hp u v v
  dsimp only at hR
  rw [← hR] at he
  simp only [Function.comp_apply,c.left_inv hpc] at he
  rw [he]
  exact hn _ _


-- @@ L598-614 verbatim
lemma LocalMetricIsometry.nonpositiveAt_image {g : SmoothMetric M} {h : SmoothMetric N}
    {f : M → N} (P : LocalMetricIsometry g h f) {p : M} (hp : p ∈ P.domain)
    (hn : NonpositiveAt g p) : NonpositiveAt h (f p) := by
  intro d hd hpd u v
  let c := chartAt E3 p
  have hc : c ∈ atlas E3 M := chart_mem_atlas E3 p
  have hpc : p ∈ c.source := mem_chart_source E3 p
  have hx := P.coordinateDomain_mem hp hpc hpd
  obtain ⟨a,ha⟩ := P.coordinate_surjective hc hd hx u
  obtain ⟨b,hb⟩ := P.coordinate_surjective hc hd hx v
  have he := P.coordinate_metric hc hd hx (curvatureTerm g c (c p) a b b) a
  have hR := (P.coordinates hc hd).curvature hc hd hx a b b
  dsimp only at hR
  rw [← hR] at he
  simp only [Function.comp_apply,c.left_inv hpc,ha,hb] at he
  rw [← he]
  exact hn c hc hpc a b

-- @@ L615-615 verbatim
end ThreeManifold.RiemannianCoordinates

-- @@ L616-616 verbatim
end


-- @@ L618-618 verbatim
section

-- @@ L619-619 verbatim
open Set Filter Topology Bundle Manifold IsManifold Matrix

-- @@ L620-620 verbatim
open scoped ContDiff Matrix.Norms.Elementwise

-- @@ L621-621 verbatim
namespace ThreeManifold.WarpedCurvature

-- @@ L622-622 verbatim
open MetricConstruction CylinderConstruction RiemannianCoordinates

-- @@ L623-623 verbatim
variable {r : ℝ → ℝ} (hs : ContDiff ℝ ∞ r) {b : ℝ} (hb : b ≠ 0) (hr : ∀ t, r t ≠ 0)

-- @@ L624-625 verbatim
def warpedModel : SmoothMetric E3 := euclideanMetric hs (contDiff_const (c := b))
  (contDiff_const (c := 0)) hr (fun _ => hb)

-- @@ L626-640 verbatim
lemma warpedModel_matrix (x : E3) :
    metricMatrix (warpedModel hs hb hr) (OpenPartialHomeomorph.refl E3) x =
      Neck.blockMatrix (Q r b (x 0)) := by
  ext i j
  change (warpedModel hs hb hr).inner x
    (mfderiv I3 I3 (id : E3 → E3) x (basisVector i))
    (mfderiv I3 I3 (id : E3 → E3) x (basisVector j)) = _
  rw [mfderiv_eq_fderiv,fderiv_id]
  have he := triangularMetric_apply (hs.comp (contDiff_apply ℝ ℝ 0))
    ((contDiff_const (c := b)).comp (contDiff_apply ℝ ℝ 0))
    ((contDiff_const (c := (0:ℝ))).comp (contDiff_apply ℝ ℝ 0))
    (fun x : E3 => hr (x 0)) (fun _ : E3 => hb) x (basisVector i) (basisVector j)
  change (warpedModel hs hb hr).inner x (basisVector i) (basisVector j) = _
  rw [show (warpedModel hs hb hr).inner x (basisVector i) (basisVector j) = _ from he]
  fin_cases i <;> fin_cases j <;> simp [Q,diag,Neck.blockMatrix,basisVector]

-- @@ L641-646 verbatim
lemma warpedModel_nonpositiveAt (x : E3) (hpos : 0 < r (x 0))
    (hc : 0 ≤ deriv (deriv r) (x 0)) : NonpositiveAt (warpedModel hs hb hr) x := by
  apply nonpositiveAt_of_chart _ (d := OpenPartialHomeomorph.refl E3) (by simp) (mem_univ x)
  intro u v
  rw [warped_curvature _ _ hs hr hb (Filter.Eventually.of_forall (warpedModel_matrix hs hb hr))]
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (mul_nonneg hpos.le hc)) (sq_nonneg _)

-- @@ L647-647 verbatim
end ThreeManifold.WarpedCurvature


-- @@ L649-649 verbatim
namespace ThreeManifold.CompactMetric

-- @@ L650-650 verbatim
open MetricConstruction CylinderConstruction RiemannianCoordinates WarpedCurvature

-- @@ L651-659 verbatim
lemma ell_convex_left {δ t : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (ht : t ≤ 0) :
    0 < deriv (deriv (Collar.ell δ)) t := by
  by_cases h : -1 ≤ t
  · exact Collar.ell_strictConvex_second hδ ⟨h,ht⟩
  · have he : Collar.k δ =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [Iio_mem_nhds (show t < -3/4 by linarith)] with s hs
      exact Collar.k_eq_one hs.le
    rw [Collar.ell_second ⟨hδ.1.le,hδ.2⟩,he.eq_of_nhds,he.deriv_eq,deriv_const]
    simpa using Collar.ell_pos δ t

-- @@ L660-664 verbatim
lemma radius₁_convex_left {δ B t : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B) (ht : t ≤ 0) :
    0 < deriv (deriv (radius₁ δ B)) t := by
  change 0 < deriv (deriv (fun s => (δ^2*B/6)*Collar.ell δ s)) t
  rw [deriv_const_mul_field',deriv_const_mul_field]
  exact mul_pos (div_pos (mul_pos (sq_pos_of_pos hδ.1) hB) (by norm_num)) (ell_convex_left hδ ht)


-- @@ L666-668 verbatim
def neckModel {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B) : SmoothMetric E3 :=
  euclideanMetric (radius₁_smooth ⟨hδ.1.le,hδ.2⟩ B) (radius₂_smooth ⟨hδ.1.le,hδ.2⟩ B)
    Cometric.χ_smooth (fun t => (radius₁_pos hδ.1 hB t).ne') (fun t => (radius₂_pos hB t).ne')

-- @@ L669-678 verbatim
lemma neckModel_apply {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B) (x u v : E3) :
    (neckModel hδ hB).inner x u v = u 0*v 0 + radius₁ δ B (x 0)^2*
      (u 1-Cometric.χ (x 0)*u 2)*(v 1-Cometric.χ (x 0)*v 2)+radius₂ δ B (x 0)^2*u 2*v 2 :=
  by
    exact triangularMetric_apply
      ((radius₁_smooth ⟨hδ.1.le,hδ.2⟩ B).comp (contDiff_apply ℝ ℝ 0))
      ((radius₂_smooth ⟨hδ.1.le,hδ.2⟩ B).comp (contDiff_apply ℝ ℝ 0))
      (Cometric.χ_smooth.comp (contDiff_apply ℝ ℝ 0))
      (fun y => (radius₁_pos hδ.1 hB (y 0)).ne')
      (fun y => (radius₂_pos hB (y 0)).ne') x u v

-- @@ L679-693 verbatim
lemma neckModel_matrix_left {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B)
    {x : E3} (hx : x 0 < 1/3) :
    metricMatrix (neckModel hδ hB) (OpenPartialHomeomorph.refl E3) x =
      Neck.blockMatrix (Q (radius₁ δ B) (B/6*Collar.ell δ 1) (x 0)) := by
  ext i j
  change (neckModel hδ hB).inner x
    (mfderiv I3 I3 (id : E3 → E3) x (basisVector i))
    (mfderiv I3 I3 (id : E3 → E3) x (basisVector j)) = _
  rw [mfderiv_eq_fderiv,fderiv_id]
  change (neckModel hδ hB).inner x (basisVector i) (basisVector j) = _
  rw [neckModel_apply,Cometric.χ_eq_zero (by linarith : x 0 ≤ 5/12)]
  have hr : radius₂ δ B (x 0) = B/6*Collar.ell δ 1 := by
    rw [radius₂,ell_plateau ⟨hδ.1.le,hδ.2⟩ (by linarith)]
  rw [hr]
  fin_cases i <;> fin_cases j <;> simp [Q,WarpedCurvature.diag,Neck.blockMatrix,basisVector]

-- @@ L694-705 verbatim
lemma neckModel_nonpositive_left {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B)
    {x : E3} (hx : x 0 ≤ 0) : NonpositiveAt (neckModel hδ hB) x := by
  have hb : B/6*Collar.ell δ 1 ≠ 0 := (mul_pos (div_pos hB (by norm_num)) (Collar.ell_pos _ _)).ne'
  have he : metricMatrix (neckModel hδ hB) (OpenPartialHomeomorph.refl E3) =ᶠ[𝓝 x]
      fun y => Neck.blockMatrix (Q (radius₁ δ B) (B/6*Collar.ell δ 1) (y 0)) := by
    filter_upwards [((continuous_apply 0).continuousAt.preimage_mem_nhds
      (Iio_mem_nhds (show x 0 < 1/3 by linarith)))] with y hy
    exact neckModel_matrix_left hδ hB hy
  apply nonpositiveAt_of_chart _ (d := OpenPartialHomeomorph.refl E3) (by simp) (mem_univ x)
  intro u v
  exact warped_nonpositive _ _ (radius₁_smooth ⟨hδ.1.le,hδ.2⟩ B)
    (radius₁_pos hδ.1 hB) hb he (radius₁_convex_left hδ hB hx).le u v


-- @@ L707-716 verbatim
lemma warpedModel_apply {r : ℝ → ℝ} (hs : ContDiff ℝ ∞ r) {b : ℝ} (hb : b ≠ 0)
    (hr : ∀ t, r t ≠ 0) (x u v : E3) :
    (warpedModel hs hb hr).inner x u v = u 0*v 0 + r (x 0)^2*u 1*v 1+b^2*u 2*v 2 := by
  have he : (warpedModel hs hb hr).inner x u v = u 0*v 0+
      r (x 0)^2*(u 1-0*u 2)*(v 1-0*v 2)+b^2*u 2*v 2 := by
    exact triangularMetric_apply (hs.comp (contDiff_apply ℝ ℝ 0))
      ((contDiff_const (c := b)).comp (contDiff_apply ℝ ℝ 0))
      ((contDiff_const (c := (0:ℝ))).comp (contDiff_apply ℝ ℝ 0))
      (fun y : E3 => hr (y 0)) (fun _ : E3 => hb) x u v
  simpa only [zero_mul,sub_zero] using he


-- @@ L718-718 verbatim
def rightRadius (δ B t : ℝ) := B/6*Collar.ell δ t

-- @@ L719-720 verbatim
lemma rightRadius_smooth {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (B : ℝ) : ContDiff ℝ ∞ (rightRadius δ B) :=
  contDiff_const.mul (Collar.ell_smooth ⟨hδ.1.le,hδ.2⟩)

-- @@ L721-722 verbatim
lemma rightRadius_pos (δ : ℝ) {B : ℝ} (hB : 0 < B) (t : ℝ) : 0 < rightRadius δ B t :=
  mul_pos (div_pos hB (by norm_num)) (Collar.ell_pos _ _)

-- @@ L723-727 verbatim
lemma rightRadius_convex_left {δ B t : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B) (ht : t ≤ 0) :
    0 < deriv (deriv (rightRadius δ B)) t := by
  change 0 < deriv (deriv (fun s => B/6*Collar.ell δ s)) t
  rw [deriv_const_mul_field',deriv_const_mul_field]
  exact mul_pos (div_pos hB (by norm_num)) (ell_convex_left hδ ht)

-- @@ L728-728 verbatim
def rightWidth (δ B : ℝ) := δ^2*B/6*Collar.ell δ 1

-- @@ L729-731 verbatim
lemma rightWidth_pos {δ B : ℝ} (hδ : 0 < δ) (hB : 0 < B) : 0 < rightWidth δ B := by
  unfold rightWidth
  exact mul_pos (div_pos (mul_pos (sq_pos_of_pos hδ) hB) (by norm_num)) (Collar.ell_pos _ _)


-- @@ L733-736 verbatim
def neckFlipLinear : E3 →L[ℝ] E3 :=
  ContinuousLinearMap.pi fun i : Fin 3 => if i = 0 then -(ContinuousLinearMap.proj 0 : E3 →L[ℝ] ℝ)
    else if i = 1 then (ContinuousLinearMap.proj 2 : E3 →L[ℝ] ℝ)
    else (ContinuousLinearMap.proj 1 : E3 →L[ℝ] ℝ) - ContinuousLinearMap.proj 2

-- @@ L737-738 verbatim
lemma neckFlipLinear_apply (u : E3) : neckFlipLinear u = ![-u 0,u 2,u 1-u 2] := by
  ext i; fin_cases i <;> simp [neckFlipLinear]

-- @@ L739-739 verbatim
def neckFlip (x : E3) : E3 := neckFlipLinear x + ![1,0,0]

-- @@ L740-742 verbatim
lemma neckFlip_apply (x : E3) : neckFlip x = ![1-x 0,x 2,x 1-x 2] := by
  rw [neckFlip,neckFlipLinear_apply]
  ext i; fin_cases i <;> simp; ring

-- @@ L743-743 verbatim
lemma neckFlip_smooth : ContDiff ℝ ∞ neckFlip := neckFlipLinear.contDiff.add contDiff_const

-- @@ L744-746 verbatim
lemma neckFlip_deriv (x : E3) : mfderiv I3 I3 neckFlip x = neckFlipLinear := by
  rw [mfderiv_eq_fderiv]
  exact (neckFlipLinear.hasFDerivAt.add_const _).fderiv


-- @@ L748-750 verbatim
def rightWarpedModel {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B) : SmoothMetric E3 :=
  warpedModel (rightRadius_smooth hδ B) (rightWidth_pos hδ.1 hB).ne'
    (fun t => (rightRadius_pos δ hB t).ne')

-- @@ L751-764 verbatim
lemma neckRight_tensor {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B)
    (x u v : E3) (hx : 2/3 < x 0) :
    (neckModel hδ hB).inner x u v =
      (rightWarpedModel hδ hB).inner (neckFlip x) (neckFlipLinear u) (neckFlipLinear v) := by
  rw [neckModel_apply]
  have hc : Cometric.χ (x 0) = 1 := Cometric.χ_eq_one (by linarith)
  have hr : radius₁ δ B (x 0) = rightWidth δ B := by
    rw [radius₁,ell_plateau ⟨hδ.1.le,hδ.2⟩ hx.le]
    rfl
  rw [hc,hr]
  unfold rightWarpedModel
  rw [warpedModel_apply,neckFlip_apply,neckFlipLinear_apply,neckFlipLinear_apply]
  simp [radius₂,rightRadius]
  ring


-- @@ L766-776 verbatim
def neckRightIsometry {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B) :
    LocalMetricIsometry (neckModel hδ hB) (rightWarpedModel hδ hB) neckFlip where
  domain := {x | 2/3 < x 0}
  isOpen_domain := isOpen_lt continuous_const (continuous_apply 0)
  smooth := neckFlip_smooth.contMDiff.contMDiffOn
  metric := by
    intro x hx u v
    have hu := congrArg (fun A : E3 →L[ℝ] E3 => A u) (neckFlip_deriv x)
    have hv := congrArg (fun A : E3 →L[ℝ] E3 => A v) (neckFlip_deriv x)
    exact (neckRight_tensor hδ hB x u v hx).trans (congrArg₂
      (fun a b : E3 => (rightWarpedModel hδ hB).inner (neckFlip x) a b) hu.symm hv.symm)

-- @@ L777-785 verbatim
lemma neckModel_nonpositive_right {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B)
    {x : E3} (hx : 1 ≤ x 0) : NonpositiveAt (neckModel hδ hB) x := by
  apply (neckRightIsometry hδ hB).nonpositiveAt x (by change 2/3 < x 0; linarith)
  apply warpedModel_nonpositiveAt
  · exact rightRadius_pos δ hB _
  · apply (rightRadius_convex_left hδ hB _).le
    rw [neckFlip_apply]
    change 1-x 0 ≤ 0
    linarith

-- @@ L786-786 verbatim
end ThreeManifold.CompactMetric

-- @@ L787-787 verbatim
end


-- @@ L789-789 verbatim
section

-- @@ L790-790 verbatim
open Set Filter Topology Bundle Manifold IsManifold

-- @@ L791-791 verbatim
open scoped ContDiff

-- @@ L792-792 verbatim
namespace ThreeManifold.Rechart

-- @@ L793-793 verbatim
open MetricConstruction RiemannianCoordinates

-- @@ L794-796 verbatim
variable {E M X : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ,E) ∞ M]
  [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]

-- @@ L797-818 verbatim
def realSourceIsometry (e : E ≃L[ℝ] E3)
    (g : Metric (E := E) M) (h : SmoothMetric X) (f : M → X)
    (U : Set M) (hU : IsOpen U)
    (hf : ContMDiffOn 𝓘(ℝ,E) I3 ∞ f U)
    (hm : ∀ p ∈ U, pullInner (E := E) h f p = g.inner p) :
    letI := charts (M := M) e
    letI := isManifold (M := M) e
    LocalMetricIsometry (realMetric e g) h f := by
  letI := charts (M := M) e
  letI := isManifold (M := M) e
  have hs (p : M) (hp : p ∈ U) := hf.contMDiffAt (hU.mem_nhds hp)
  refine ⟨U,hU,fun p hp => ((hs p hp).comp p
    (identity_smooth_backward e p)).contMDiffWithinAt,?_⟩
  intro p hp u v
  have h₁ := pull_composition h
    ((identity_smooth_backward e p).mdifferentiableAt (by simp))
    ((hs p hp).mdifferentiableAt (by simp))
  change pullInner (E := E3) h f p =
    pullBilin (E := E3) (F := E) (pullInner (E := E) h f p)
      (mfderiv I3 𝓘(ℝ,E) (id : M → M) p) at h₁
  rw [hm p hp] at h₁
  exact congrArg (fun b : E3 →L[ℝ] E3 →L[ℝ] ℝ => b u v) h₁.symm

-- @@ L819-819 verbatim
end ThreeManifold.Rechart

-- @@ L820-820 verbatim
end


-- @@ L822-822 verbatim
section

-- @@ L823-823 verbatim
open Set Filter Topology Bundle Manifold IsManifold Matrix

-- @@ L824-824 verbatim
open scoped ContDiff UpperHalfPlane RealInnerProductSpace

-- @@ L825-825 verbatim
namespace ThreeManifold.CompactMetric

-- @@ L826-826 verbatim
open MetricConstruction CylinderConstruction RiemannianCoordinates WarpedCurvature


-- @@ L828-829 verbatim
def universalMetric (c : ℝ) (hc : c ≠ 0) : Metric (E := EP) UniversalPiece :=
  product hyperbolic (scaleSq (euclidean (V := ℝ)) (fun _ => c) contMDiff_const (fun _ => hc))

-- @@ L830-839 verbatim
lemma universalMetric_apply (c : ℝ) (hc : c ≠ 0) (x : UniversalPiece) (u v : EP) :
    (universalMetric c hc).inner x u v = x.1.im⁻¹^2*inner ℝ u.1 v.1+c^2*u.2*v.2 := by
  apply (productInner_apply hyperbolic
    (scaleSq (euclidean (V := ℝ)) (fun _ => c) contMDiff_const (fun _ => hc)) x u v).trans
  change hyperbolic.inner x.1 u.1 v.1+c^2*inner ℝ u.2 v.2 = _
  have hh := hyperbolic_inner x.1 u.1 v.1
  rw [hh]
  have hi : inner ℝ u.2 v.2 = u.2*v.2 := by simp [mul_comm]
  rw [hi]
  ring


-- @@ L841-841 verbatim
def exponentialRadius (t : ℝ) := Real.exp (-t)

-- @@ L842-842 verbatim
lemma exponentialRadius_smooth : ContDiff ℝ ∞ exponentialRadius := contDiff_id.neg.exp

-- @@ L843-845 verbatim
lemma exponentialRadius_deriv : deriv exponentialRadius = fun t => -Real.exp (-t) := by
  funext t
  exact ((hasDerivAt_id t).neg.exp).deriv.trans (by simp)

-- @@ L846-848 verbatim
lemma exponentialRadius_second (t : ℝ) : deriv (deriv exponentialRadius) t = Real.exp (-t) := by
  rw [exponentialRadius_deriv]
  exact (((hasDerivAt_id t).neg.exp).neg).deriv.trans (by simp)


-- @@ L850-851 verbatim
def hyperbolicWarped (c : ℝ) (hc : c ≠ 0) : SmoothMetric E3 :=
  warpedModel exponentialRadius_smooth hc (fun t => (Real.exp_pos (-t)).ne')

-- @@ L852-857 verbatim
lemma hyperbolicWarped_nonpositive (c : ℝ) (hc : c ≠ 0) (x : E3) :
    NonpositiveAt (hyperbolicWarped c hc) x := by
  apply warpedModel_nonpositiveAt
  · exact Real.exp_pos _
  · rw [exponentialRadius_second]
    exact (Real.exp_pos _).le


-- @@ L859-859 verbatim
def universalLog : UniversalPiece → E3 := coordinates ∘ logarithmicLift

-- @@ L860-861 verbatim
lemma universalLog_smooth : ContMDiff 𝓘(ℝ,EP) I3 ∞ universalLog :=
  coordinates.contDiff.contMDiff.comp logarithmicLift_smooth

-- @@ L862-869 verbatim
lemma universalLog_deriv (x : UniversalPiece) :
    mfderiv 𝓘(ℝ,EP) I3 universalLog x = coordinates.toContinuousLinearMap.comp (logLinear x.1.im) := by
  have hs : ContMDiff 𝓘(ℝ,P) I3 ∞ coordinates := coordinates.contDiff.contMDiff
  rw [universalLog,mfderiv_comp x
    ((hs _).mdifferentiableAt (by simp))
    ((logarithmicLift_smooth x).mdifferentiableAt (by simp)),logarithmicLift_deriv,
    mfderiv_eq_fderiv,coordinates.hasFDerivAt.fderiv]
  rfl


-- @@ L871-884 verbatim
lemma universalLog_tensor (c : ℝ) (hc : c ≠ 0) (x : UniversalPiece) (u v : EP) :
    (hyperbolicWarped c hc).inner (universalLog x)
      (coordinates (logLinear x.1.im u)) (coordinates (logLinear x.1.im v)) =
    (universalMetric c hc).inner x u v := by
  have hw := warpedModel_apply exponentialRadius_smooth hc
    (fun t => (Real.exp_pos (-t)).ne') (universalLog x)
    (coordinates (logLinear x.1.im u)) (coordinates (logLinear x.1.im v))
  apply hw.trans
  rw [universalMetric_apply]
  change (x.1.im⁻¹*u.1.im)*(x.1.im⁻¹*v.1.im)+
    Real.exp (-Real.log x.1.im)^2*u.1.re*v.1.re+c^2*u.2*v.2 = _
  rw [Real.exp_neg,Real.exp_log x.1.im_pos,Complex.inner]
  simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im]
  ring


-- @@ L886-895 verbatim
lemma universalLog_metric (c : ℝ) (hc : c ≠ 0) (x : UniversalPiece) :
    pullInner (E := EP) (hyperbolicWarped c hc) universalLog x = (universalMetric c hc).inner x := by
  ext u v
  change (hyperbolicWarped c hc).inner (universalLog x)
    ((mfderiv 𝓘(ℝ,EP) I3 universalLog x : EP →L[ℝ] E3) u)
    ((mfderiv 𝓘(ℝ,EP) I3 universalLog x : EP →L[ℝ] E3) v) = _
  rw [universalLog_deriv]
  change (hyperbolicWarped c hc).inner (universalLog x)
    (coordinates (logLinear x.1.im u)) (coordinates (logLinear x.1.im v)) = _
  exact universalLog_tensor c hc x u v


-- @@ L897-897 verbatim
local instance : ChartedSpace E3 UniversalPiece := Rechart.charts Coordinates3.coordinates

-- @@ L898-898 verbatim
local instance : IsManifold I3 ∞ UniversalPiece := Rechart.isManifold Coordinates3.coordinates

-- @@ L899-899 verbatim
local instance : ChartedSpace E3 WholePiece := Rechart.charts Coordinates3.coordinates

-- @@ L900-900 verbatim
local instance : IsManifold I3 ∞ WholePiece := Rechart.isManifold Coordinates3.coordinates


-- @@ L902-903 verbatim
def realUniversalMetric (c : ℝ) (hc : c ≠ 0) : SmoothMetric UniversalPiece :=
  Rechart.realMetric Coordinates3.coordinates (universalMetric c hc)

-- @@ L904-905 verbatim
def realCoreMetric (c : ℝ) (hc : c ≠ 0) : SmoothMetric WholePiece :=
  Rechart.realMetric Coordinates3.coordinates (coreMetric c hc)

-- @@ L906-909 verbatim
def universalLogIsometry (c : ℝ) (hc : c ≠ 0) :
    LocalMetricIsometry (realUniversalMetric c hc) (hyperbolicWarped c hc) universalLog :=
  Rechart.realSourceIsometry Coordinates3.coordinates _ _ _ univ isOpen_univ
    universalLog_smooth.contMDiffOn (fun x _ => universalLog_metric c hc x)

-- @@ L910-912 verbatim
lemma realUniversalMetric_nonpositive (c : ℝ) (hc : c ≠ 0) (x : UniversalPiece) :
    NonpositiveAt (realUniversalMetric c hc) x :=
  (universalLogIsometry c hc).nonpositiveAt x (mem_univ x) (hyperbolicWarped_nonpositive c hc _)

-- @@ L913-919 verbatim
def coreProjectionIsometry (c : ℝ) (hc : c ≠ 0) :
    LocalMetricIsometry (realUniversalMetric c hc) (realCoreMetric c hc) sourceProjection :=
  Rechart.realIsometry Coordinates3.coordinates Coordinates3.coordinates _ _ _ univ isOpen_univ
    sourceProjection_smooth.contMDiffOn (by
      intro x _
      ext u v
      exact (coreMetric_projection c hc x u v).trans (universalMetric_apply c hc x u v).symm)

-- @@ L920-929 verbatim
lemma realCoreMetric_nonpositive (c : ℝ) (hc : c ≠ 0) (q : WholePiece) :
    NonpositiveAt (realCoreMetric c hc) q := by
  let x : UniversalPiece := (HyperbolicCore.sectionMap q.1,CircleConstruction.sectionMap 6 q.2)
  have he : sourceProjection x = q := by
    apply Prod.ext
    · exact HyperbolicCore.sectionMap_rightInverse q.1
    · exact CircleConstruction.section_spec 6 q.2
  rw [← he]
  exact (coreProjectionIsometry c hc).nonpositiveAt_image (mem_univ x)
    (realUniversalMetric_nonpositive c hc x)

-- @@ L930-930 verbatim
end ThreeManifold.CompactMetric

-- @@ L931-931 verbatim
end


-- @@ L933-933 verbatim
section

-- @@ L934-934 verbatim
open Set Filter Topology Bundle Manifold IsManifold

-- @@ L935-935 verbatim
open scoped ContDiff

-- @@ L936-936 verbatim
namespace ThreeManifold.RiemannianCoordinates

-- @@ L937-938 verbatim
variable {M N : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]

-- @@ L939-947 verbatim
lemma geodesic_congrOn (g : SmoothMetric M) {γ η : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (he : EqOn γ η U) (hγ : IsGeodesicOn g γ U) : IsGeodesicOn g η U := by
  refine ⟨hγ.1.congr he.symm,?_⟩
  intro c hc s hs hsc
  have hev : γ =ᶠ[nhds s] η := Filter.eventually_of_mem (hU.mem_nhds hs) (fun r hr => he hr)
  have hec : (c ∘ γ) =ᶠ[nhds s] (c ∘ η) := hev.fun_comp c
  have hcg := hγ.2 c hc s hs (by rwa [he hs])
  rw [along_congr g c hec.symm hec.deriv.symm]
  exact hcg

-- @@ L948-948 verbatim
namespace LocalMetricIsometry

-- @@ L949-950 verbatim
variable {g : SmoothMetric M} {h : SmoothMetric N} {f : M → N}
  (P : LocalMetricIsometry g h f)

-- @@ L951-959 verbatim
lemma deriv_injective {p : M} (hp : p ∈ P.domain) : Function.Injective (mfderiv I3 I3 f p) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  by_contra hn
  have he := P.metric p hp v v
  have hpos := g.pos p v hn
  rw [hv,map_zero] at he
  change g.inner p v v = 0 at he
  linarith

-- @@ L960-963 verbatim
lemma deriv_bijective {p : M} (hp : p ∈ P.domain) : Function.Bijective (mfderiv I3 I3 f p) := by
  change Function.Bijective (show E3 →L[ℝ] E3 from mfderiv I3 I3 f p)
  exact ⟨P.deriv_injective hp,(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (K := ℝ) rfl).mp
    (P.deriv_injective hp)⟩

-- @@ L964-975 verbatim
lemma geodesic_reflect {γ : ℝ → M} {U : Set ℝ} (hU : IsOpen U)
    (hγ : ContMDiffOn 𝓘(ℝ,ℝ) I3 ∞ γ U) (hγP : MapsTo γ U P.domain)
    (hg : IsGeodesicOn h (f ∘ γ) U) : IsGeodesicOn g γ U := by
  apply geodesic_of_acceleration_zero g hU hγ
  intro s hs
  apply P.deriv_injective (hγP hs)
  rw [map_zero]
  have he : velocity (f ∘ γ) =ᶠ[𝓝 s] P.mapField γ (velocity γ) := by
    filter_upwards [hU.mem_nhds hs] with r hr
    exact P.velocity_map (hγ.contMDiffAt (hU.mem_nhds hr)) (hγP hr)
  rw [← P.covariantDerivative_map hU hγ hγP (velocity_smooth hU hγ) hs,
    ← covariantDerivative_germ h he,geodesic_acceleration_zero h hU hg hs]

-- @@ L976-976 verbatim
end LocalMetricIsometry

-- @@ L977-977 verbatim
end ThreeManifold.RiemannianCoordinates

-- @@ L978-978 verbatim
end


-- @@ L980-980 verbatim
section

-- @@ L981-981 verbatim
open Set Filter Topology Bundle Manifold IsManifold Matrix

-- @@ L982-982 verbatim
open scoped ContDiff Matrix.Norms.Elementwise UpperHalfPlane

-- @@ L983-983 verbatim
namespace ThreeManifold.WarpedCurvature

-- @@ L984-984 verbatim
open RiemannianCoordinates Neck

-- @@ L985-1009 verbatim
lemma warped_fiber_geodesic {r : ℝ → ℝ} (hs : ContDiff ℝ ∞ r) {b : ℝ}
    (hb : b ≠ 0) (hr : ∀ t, r t ≠ 0) (a x k : ℝ) :
    IsGeodesicOn (warpedModel hs hb hr) (fun t => ![a,x,k*t]) univ := by
  have hsmooth : ContDiff ℝ ∞ (fun t : ℝ => (![a,x,k*t] : E3)) := by
    apply contDiff_pi.mpr; intro i; fin_cases i <;> simp <;> fun_prop
  refine ⟨hsmooth.contMDiff.contMDiffOn,?_⟩
  intro c hc t ht hct
  rw [chartedSpaceSelf_atlas] at hc
  subst c
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => (![a,x,k*t] : E3)) (![0,0,k] : E3) t := by
    apply hasDerivAt_pi.mpr; intro i; fin_cases i
    · exact hasDerivAt_const t a
    · exact hasDerivAt_const t x
    · simpa using (hasDerivAt_id t).const_mul k
  have hd' : deriv (fun t : ℝ => (![a,x,k*t] : E3)) = fun _ => (![0,0,k] : E3) :=
    funext (fun t => (hd t).deriv)
  change deriv (deriv (fun t : ℝ => (![a,x,k*t] : E3))) t +
    connectionTerm (warpedModel hs hb hr) (OpenPartialHomeomorph.refl E3)
      (![a,x,k*t] : E3) (deriv (fun t : ℝ => (![a,x,k*t] : E3)) t)
      (deriv (fun t : ℝ => (![a,x,k*t] : E3)) t) = 0
  rw [hd',deriv_const,zero_add,connectionTerm_product _ _
    (Filter.Eventually.of_forall (warpedModel_matrix hs hb hr))
    (Q_deriv hs b a) (QP r (hr a) hb) (diag_transpose _ _)]
  ext i; fin_cases i <;>
    simp [gamma,joinVector,splitVector,P,diag,pairing,dotProduct,Matrix.mulVec,Fin.sum_univ_two]

-- @@ L1010-1010 verbatim
end ThreeManifold.WarpedCurvature

-- @@ L1011-1011 verbatim
namespace ThreeManifold.CompactMetric

-- @@ L1012-1012 verbatim
open MetricConstruction CylinderConstruction RiemannianCoordinates

-- @@ L1013-1013 verbatim
local instance : ChartedSpace E3 UniversalPiece := Rechart.charts Coordinates3.coordinates

-- @@ L1014-1014 verbatim
local instance : IsManifold I3 ∞ UniversalPiece := Rechart.isManifold Coordinates3.coordinates

-- @@ L1015-1015 verbatim
local instance : ChartedSpace E3 WholePiece := Rechart.charts Coordinates3.coordinates

-- @@ L1016-1016 verbatim
local instance : IsManifold I3 ∞ WholePiece := Rechart.isManifold Coordinates3.coordinates

-- @@ L1017-1023 verbatim
lemma universal_fiber_smooth (z : ℍ) (k : ℝ) :
    ContMDiff 𝓘(ℝ,ℝ) I3 ∞ (fun t : ℝ => (z,k*t) : ℝ → UniversalPiece) := by
  have hf : ContMDiff 𝓘(ℝ,ℝ) 𝓘(ℝ,EP) ∞ (fun t : ℝ => (z,k*t) : ℝ → UniversalPiece) := by
    simpa only [EP,← modelWithCornersSelf_prod] using
      (contMDiff_const.prodMk (contMDiff_const.mul contMDiff_id) :
        ContMDiff 𝓘(ℝ,ℝ) (𝓘(ℝ,ℂ).prod 𝓘(ℝ,ℝ)) ∞ (fun t : ℝ => (z,k*t)))
  exact (Rechart.identity_smooth_forward Coordinates3.coordinates).comp hf

-- @@ L1024-1030 verbatim
lemma universal_fiber_geodesic (c : ℝ) (hc : c ≠ 0) (z : ℍ) (k : ℝ) :
    IsGeodesicOn (realUniversalMetric c hc) (fun t => (z,k*t)) univ := by
  apply (universalLogIsometry c hc).geodesic_reflect isOpen_univ
    (universal_fiber_smooth z k).contMDiffOn (fun _ _ => mem_univ _)
  change IsGeodesicOn (hyperbolicWarped c hc) (fun t => ![Real.log z.im,z.re,k*t]) univ
  exact WarpedCurvature.warped_fiber_geodesic exponentialRadius_smooth hc
    (fun t => (Real.exp_pos (-t)).ne') _ _ _

-- @@ L1031-1035 verbatim
lemma core_fiber_geodesic (c : ℝ) (hc : c ≠ 0) (z : ℍ) (k : ℝ) :
    IsGeodesicOn (realCoreMetric c hc)
      (fun t => (HyperbolicCore.projection z,((k*t : ℝ) : GluedConstruction.Circle))) univ := by
  exact (coreProjectionIsometry c hc).geodesic_map isOpen_univ
    (universal_fiber_geodesic c hc z k) (fun _ _ => mem_univ _)

-- @@ L1036-1036 verbatim
end ThreeManifold.CompactMetric

-- @@ L1037-1037 verbatim
end


-- @@ L1039-1039 verbatim
section

-- @@ L1040-1040 verbatim
open Set Filter Topology Bundle Manifold IsManifold

-- @@ L1041-1041 verbatim
open scoped ContDiff

-- @@ L1042-1042 verbatim
namespace ThreeManifold.CompactMetric

-- @@ L1043-1043 verbatim
open MetricConstruction CylinderConstruction GluedConstruction RiemannianCoordinates

-- @@ L1044-1044 verbatim
local instance : ChartedSpace E3 Piece := Rechart.charts Coordinates3.coordinates

-- @@ L1045-1045 verbatim
local instance : IsManifold I3 ∞ Piece := Rechart.isManifold Coordinates3.coordinates


-- @@ L1047-1048 verbatim
def realPieceMetric {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (i : Bool) : SmoothMetric Piece :=
  Rechart.realMetric Coordinates3.coordinates (pieceMetrics hδ i)


-- @@ L1050-1054 verbatim
def pieceInclusionIsometry {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (i : Bool) :
    LocalMetricIsometry (realPieceMetric hδ i) (realCompactMetric hδ) (inclusion i) :=
  Rechart.realIsometry Coordinates3.coordinates Coordinates3.coordinates
    (pieceMetrics hδ i) (compactMetric hδ) (inclusion i) univ isOpen_univ
    (inclusion_smooth i).contMDiffOn (fun x _ => compactMetric_local hδ i x)

-- @@ L1055-1055 verbatim
end ThreeManifold.CompactMetric


-- @@ L1057-1057 verbatim
namespace ThreeManifold.RiemannianCoordinates

-- @@ L1058-1060 verbatim
variable {M N X : Type} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold I3 ∞ M]
  [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
  [TopologicalSpace X] [ChartedSpace E3 X] [IsManifold I3 ∞ X]

-- @@ L1061-1061 verbatim
namespace LocalMetricIsometry

-- @@ L1062-1063 verbatim
variable {g : SmoothMetric M} {h : SmoothMetric N} {k : SmoothMetric X}
  {f : M → N} {w : N → X}

-- @@ L1064-1076 verbatim
def comp (Q : LocalMetricIsometry h k w) (P : LocalMetricIsometry g h f) :
    LocalMetricIsometry g k (w ∘ f) where
  domain := P.domain ∩ f ⁻¹' Q.domain
  isOpen_domain := P.smooth.continuousOn.isOpen_inter_preimage P.isOpen_domain Q.isOpen_domain
  smooth := fun p hp => ((Q.smoothAt hp.2).comp p (P.smoothAt hp.1)).contMDiffWithinAt
  metric := by
    intro p hp u v
    have hd := mfderiv_comp p ((Q.smoothAt hp.2).mdifferentiableAt (by simp))
      ((P.smoothAt hp.1).mdifferentiableAt (by simp))
    have he := (P.metric p hp.1 u v).trans (Q.metric (f p) hp.2 _ _)
    apply he.trans
    exact congrArg₂ (fun a b => k.inner (w (f p)) a b)
      (congrArg (fun D => D u) hd.symm) (congrArg (fun D => D v) hd.symm)


-- @@ L1078-1086 verbatim
def identity (g h : SmoothMetric M) (U : Set M) (hU : IsOpen U)
    (he : ∀ p ∈ U, g.inner p = h.inner p) : LocalMetricIsometry g h id where
  domain := U
  isOpen_domain := hU
  smooth := contMDiff_id.contMDiffOn
  metric := by
    intro p hp u v
    rw [mfderiv_id]
    exact congrArg (fun b => b u v) (he p hp)


-- @@ L1088-1095 verbatim
lemma nonpositiveAt_congr {g h : SmoothMetric M} {p : M}
    (he : ∀ᶠ q in 𝓝 p, g.inner q = h.inner q) : NonpositiveAt g p ↔ NonpositiveAt h p := by
  obtain ⟨U,hU,hUp,hEq⟩ := mem_nhds_iff.mp he
  constructor
  · intro hn
    exact (identity h g U hUp (fun q hq => (hU hq).symm)).nonpositiveAt p hEq hn
  · intro hn
    exact (identity g h U hUp (fun q hq => hU hq)).nonpositiveAt p hEq hn

-- @@ L1096-1096 verbatim
end LocalMetricIsometry

-- @@ L1097-1097 verbatim
end ThreeManifold.RiemannianCoordinates


-- @@ L1099-1099 verbatim
namespace ThreeManifold.CompactMetric


-- @@ L1101-1101 verbatim
section

-- @@ L1102-1102 verbatim
open MetricConstruction CylinderConstruction RiemannianCoordinates

-- @@ L1103-1103 verbatim
local instance : ChartedSpace E3 Cylinder := Rechart.charts coordinates

-- @@ L1104-1104 verbatim
local instance : IsManifold I3 ∞ Cylinder := Rechart.isManifold coordinates


-- @@ L1106-1107 verbatim
def realNeck {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B) : SmoothMetric Cylinder :=
  Rechart.realMetric coordinates (neck hδ hB)

-- @@ L1108-1111 verbatim
def neckProjectionIsometry {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B) :
    LocalMetricIsometry (neckModel hδ hB) (realNeck hδ hB) euclideanProjection :=
  projectionIsometry (radius₁_smooth ⟨hδ.1.le,hδ.2⟩ B) (radius₂_smooth ⟨hδ.1.le,hδ.2⟩ B)
    Cometric.χ_smooth (fun t => (radius₁_pos hδ.1 hB t).ne') (fun t => (radius₂_pos hB t).ne')

-- @@ L1112-1120 verbatim
lemma realNeck_nonpositive {δ B : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (hB : 0 < B)
    {q : Cylinder} (hq : q.1 ≤ 0 ∨ 1 ≤ q.1) : NonpositiveAt (realNeck hδ hB) q := by
  let x := coordinates (CylinderConstruction.sectionMap q)
  have he : euclideanProjection x = q := CylinderConstruction.section_spec q
  rw [← he]
  apply (neckProjectionIsometry hδ hB).nonpositiveAt_image (mem_univ x)
  rcases hq with hq|hq
  · exact neckModel_nonpositive_left hδ hB hq
  · exact neckModel_nonpositive_right hδ hB hq


-- @@ L1122-1126 verbatim
def radialIsometry (g : Metric (E := P) Cylinder) {L : ℝ} (hL : 4 ≤ L) :
    LocalMetricIsometry (Rechart.realMetric coordinates (radialPull g hL))
      (Rechart.realMetric coordinates g) (radial L) :=
  Rechart.realIsometry coordinates coordinates _ _ _ univ isOpen_univ
    (radial_smooth L).contMDiffOn (fun _ _ => rfl)

-- @@ L1127-1131 verbatim
def switchIsometry (g : Metric (E := P) Cylinder) :
    LocalMetricIsometry (Rechart.realMetric coordinates (switched g))
      (Rechart.realMetric coordinates g) switch :=
  Rechart.realIsometry coordinates coordinates _ _ _ univ isOpen_univ
    switch_smooth.contMDiffOn (fun _ _ => rfl)

-- @@ L1132-1137 verbatim
lemma radial_nonpos {L r : ℝ} (hL : 4 ≤ L) (hr : r ≤ Real.log 2) :
    RadialProfile.coordinate L r ≤ 0 := by
  have he : RadialProfile.coordinate L (Real.log 2) = 0 := by
    rw [RadialProfile.coordinate_right (RadialProfile.log_bounds.1.le),sub_self,zero_div]
  rw [← he]
  exact (RadialProfile.coordinate_strictMono hL).monotone hr

-- @@ L1138-1142 verbatim
lemma realLeftCylinder_nonpositive {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {q : Cylinder} (hq : q.1 ≤ Real.log 2) :
    NonpositiveAt (Rechart.realMetric coordinates (leftCylinder hδ)) q := by
  apply (radialIsometry (neck hδ (period_pos δ)) (leftLength_ge hδ)).nonpositiveAt q (mem_univ q)
  exact realNeck_nonpositive hδ (period_pos δ) (Or.inl (radial_nonpos (leftLength_ge hδ) hq))

-- @@ L1143-1151 verbatim
lemma realRightCylinder_nonpositive {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    {q : Cylinder} (hq : q.1 ≤ Real.log 2) :
    NonpositiveAt (Rechart.realMetric coordinates (rightCylinder hδ)) q := by
  apply (radialIsometry (switched (neck hδ (period_pos δ))) (L := 4) le_rfl).nonpositiveAt q (mem_univ q)
  apply (switchIsometry (neck hδ (period_pos δ))).nonpositiveAt _ (mem_univ _)
  apply realNeck_nonpositive hδ (period_pos δ)
  right
  change 1 ≤ 1-RadialProfile.coordinate 4 q.1
  linarith [radial_nonpos (L := 4) le_rfl hq]

-- @@ L1152-1152 verbatim
end


-- @@ L1154-1154 verbatim
open MetricConstruction CylinderConstruction RiemannianCoordinates


-- @@ L1156-1157 verbatim
def heightToLog (a : ℝ) (ha : 0 < a) : HeightCylinder a → Cylinder :=
  Subtype.val ∘ logCylinderHomeomorph a ha

-- @@ L1158-1160 verbatim
lemma heightToLog_smooth (a : ℝ) (ha : 0 < a) :
    ContMDiff 𝓘(ℝ,P) 𝓘(ℝ,P) ∞ (heightToLog a ha) :=
  (contMDiff_subtype_val (U := logDomain a)).comp (logCylinder_smooth a ha)

-- @@ L1161-1164 verbatim
lemma heightToLog_metric (g : Metric (E := P) Cylinder) (a : ℝ) (ha : 0 < a)
    (x : HeightCylinder a) : pullInner g (heightToLog a ha) x = (heightMetric g a ha).inner x := by
  exact pull_composition g (((logCylinder_smooth a ha) x).mdifferentiableAt (by simp))
    ((contMDiff_subtype_val (U := logDomain a) (n := ∞) _).mdifferentiableAt (by simp))


-- @@ L1166-1167 verbatim
def wholeCuspLog (a : ℝ) (ha : 1 < a) : WholePiece → Cylinder :=
  heightToLog a (by linarith) ∘ cuspChart a ha

-- @@ L1168-1170 verbatim
lemma cuspChart_source (a : ℝ) (ha : 1 < a) : (cuspChart a ha).source = wholeCusp a := by
  ext x
  simp [cuspChart]

-- @@ L1171-1176 verbatim
lemma wholeCuspLog_smooth {a : ℝ} (ha : 1 < a) {x : WholePiece} (hx : x ∈ wholeCusp a) :
    ContMDiffAt 𝓘(ℝ,EP) 𝓘(ℝ,P) ∞ (wholeCuspLog a ha) x := by
  apply ((heightToLog_smooth a (by linarith)) _).comp x
  apply (cuspChart_smooth a ha).contMDiffAt
  rw [cuspChart_source]
  exact (wholeCusp a).isOpen.mem_nhds hx

-- @@ L1177-1184 verbatim
lemma wholeCuspLog_metric (g : Metric (E := P) Cylinder) {a : ℝ} (ha : 1 < a)
    {x : WholePiece} (hx : x ∈ wholeCusp a) :
    pullInner g (wholeCuspLog a ha) x = (cuspMetric g a ha).inner x := by
  have hs := (cuspChart_smooth a ha).contMDiffAt (by
    rw [cuspChart_source]; exact (wholeCusp a).isOpen.mem_nhds hx)
  rw [wholeCuspLog,pull_composition _ (hs.mdifferentiableAt (by simp))
    (((heightToLog_smooth a (by linarith)) _).mdifferentiableAt (by simp)),heightToLog_metric]
  rfl

-- @@ L1185-1192 verbatim
lemma cuspChart_apply {a : ℝ} (ha : 1 < a) {x : WholePiece} (hx : x ∈ wholeCusp a) :
    cuspChart a ha x = wholeCoordinates a ha ⟨x,hx⟩ := by
  unfold cuspChart
  change wholeCoordinates a ha ((wholeCusp a).openPartialHomeomorphSubtypeCoe
    (wholeCusp_nonempty a ha) |>.symm x) = _
  congr 1
  apply Subtype.ext
  exact (wholeCusp a).openPartialHomeomorphSubtypeCoe (wholeCusp_nonempty a ha) |>.right_inv (by simpa using hx)

-- @@ L1193-1197 verbatim
lemma wholeCuspLog_height {a : ℝ} (ha : 1 < a) {x : WholePiece} (hx : x ∈ wholeCusp a) :
    (wholeCuspLog a ha x).1 = HyperbolicCore.height x.1 := by
  change Real.log ((cuspChart a ha x).1 : ℝ) = _
  rw [cuspChart_apply ha hx]
  exact (HyperbolicCore.height_cuspCoordinates a ha ⟨x.1,hx⟩).symm


-- @@ L1199-1199 verbatim
local instance : ChartedSpace E3 WholePiece := Rechart.charts Coordinates3.coordinates

-- @@ L1200-1200 verbatim
local instance : IsManifold I3 ∞ WholePiece := Rechart.isManifold Coordinates3.coordinates

-- @@ L1201-1201 verbatim
local instance : ChartedSpace E3 Cylinder := Rechart.charts coordinates

-- @@ L1202-1202 verbatim
local instance : IsManifold I3 ∞ Cylinder := Rechart.isManifold coordinates

-- @@ L1203-1206 verbatim
variable (g : Metric (E := P) Cylinder) (c : ℝ) (hc : c ≠ 0)
  (low : ∀ (x : P), x.1 < 1/4 → ∀ u v : P,
    pullInner (E := P) g projection x u v =
      u.1*v.1 + Real.exp (-x.1)^2*u.2.1*v.2.1 + c^2*u.2.2*v.2.2)

-- @@ L1207-1212 verbatim
def wholeCuspIsometry : LocalMetricIsometry
    (Rechart.realMetric Coordinates3.coordinates (wholeMetric g c hc low))
    (Rechart.realMetric coordinates g) (wholeCuspLog cuspLevel cuspLevel_gt) :=
  Rechart.realIsometry Coordinates3.coordinates coordinates _ _ _ (wholeCusp cuspLevel)
    (wholeCusp cuspLevel).isOpen (fun _ hx => (wholeCuspLog_smooth cuspLevel_gt hx).contMDiffWithinAt)
    (fun _ hx => (wholeCuspLog_metric g cuspLevel_gt hx).trans (wholeMetric_cusp g c hc low hx).symm)


-- @@ L1214-1224 verbatim
def wholeCoreIsometry : LocalMetricIsometry
    (Rechart.realMetric Coordinates3.coordinates (wholeMetric g c hc low))
    (realCoreMetric c hc) id :=
  Rechart.realIsometry Coordinates3.coordinates Coordinates3.coordinates _ _ _ coreRegion coreRegion.isOpen
    contMDiff_id.contMDiffOn (by
      intro x hx
      ext u v
      change (coreMetric c hc).inner x (mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,EP) id x u)
        (mfderiv 𝓘(ℝ,EP) 𝓘(ℝ,EP) id x v) = _
      rw [mfderiv_id]
      exact congrArg (fun b => b u v) (wholeMetric_core g c hc low hx).symm)

-- @@ L1225-1237 verbatim
lemma whole_nonpositive {x : WholePiece} (hx : HyperbolicCore.height x.1 ≤ Real.log 2)
    (hn : ∀ q : Cylinder, q.1 ≤ Real.log 2 → NonpositiveAt (Rechart.realMetric coordinates g) q) :
    NonpositiveAt (Rechart.realMetric Coordinates3.coordinates (wholeMetric g c hc low)) x := by
  by_cases hh : x ∈ coreRegion
  · exact (wholeCoreIsometry g c hc low).nonpositiveAt x hh (realCoreMetric_nonpositive c hc x)
  · have hh' : x ∈ wholeCusp cuspLevel := by
      apply (HyperbolicCore.mem_cusp_iff_height cuspLevel_gt x.1).mpr
      rw [log_cuspLevel]
      change ¬HyperbolicCore.height x.1 < 1/4 at hh
      linarith
    apply (wholeCuspIsometry g c hc low).nonpositiveAt x hh'
    apply hn
    rwa [wholeCuspLog_height cuspLevel_gt hh']

-- @@ L1238-1238 verbatim
end ThreeManifold.CompactMetric

-- @@ L1239-1239 verbatim
end


-- @@ L1241-1241 verbatim
open Set Filter Topology Bundle Manifold IsManifold

-- @@ L1242-1242 verbatim
open scoped ContDiff

-- @@ L1243-1243 verbatim
namespace ThreeManifold.CompactMetric

-- @@ L1244-1244 verbatim
open MetricConstruction CylinderConstruction RiemannianCoordinates GluedConstruction

-- @@ L1245-1245 verbatim
local instance : ChartedSpace E3 WholePiece := Rechart.charts Coordinates3.coordinates

-- @@ L1246-1246 verbatim
local instance : IsManifold I3 ∞ WholePiece := Rechart.isManifold Coordinates3.coordinates

-- @@ L1247-1247 verbatim
local instance : ChartedSpace E3 Piece := Rechart.charts Coordinates3.coordinates

-- @@ L1248-1248 verbatim
local instance : IsManifold I3 ∞ Piece := Rechart.isManifold Coordinates3.coordinates


-- @@ L1250-1254 verbatim
def pieceMapIsometry (g : Metric (E := EP) WholePiece) :
    LocalMetricIsometry (Rechart.realMetric Coordinates3.coordinates (pieceMetric g))
      (Rechart.realMetric Coordinates3.coordinates g) pieceMap :=
  Rechart.realIsometry Coordinates3.coordinates Coordinates3.coordinates _ _ _ univ isOpen_univ
    pieceMap_smooth.contMDiffOn (fun _ _ => rfl)

-- @@ L1255-1265 verbatim
lemma realPiece_nonpositive {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2)) (i : Bool)
    {x : Piece} (hx : x ∉ collar) : NonpositiveAt (realPieceMetric hδ i) x := by
  have hh : HyperbolicCore.height x.1.1 ≤ Real.log 2 := by
    apply le_of_not_gt
    intro h
    exact hx ((HyperbolicCore.mem_cusp_iff_height (by norm_num : (1:ℝ) < 2) x.1.1).mpr h)
  cases i
  · apply (pieceMapIsometry (leftWhole hδ)).nonpositiveAt x (mem_univ _)
    exact whole_nonpositive _ _ _ (leftCylinder_low hδ) hh (fun q hq => realLeftCylinder_nonpositive hδ hq)
  · apply (pieceMapIsometry (rightWhole hδ)).nonpositiveAt x (mem_univ _)
    exact whole_nonpositive _ _ _ (rightCylinder_low hδ) hh (fun q hq => realRightCylinder_nonpositive hδ hq)


-- @@ L1267-1267 verbatim
def openNeck : Set GluedConstruction.Manifold := inclusion false '' (collar : Set Piece)

-- @@ L1268-1269 verbatim
lemma openNeck_isOpen : IsOpen openNeck :=
  (TwoGluing.inclusion_openEmbedding collar gluingMap false).isOpenMap _ collar.isOpen

-- @@ L1270-1275 verbatim
lemma inclusion_collar_mem_openNeck (i : Bool) {x : Piece} (hx : x ∈ collar) :
    inclusion i x ∈ openNeck := by
  cases i
  · exact ⟨x,hx,rfl⟩
  · exact ⟨(gluingMap.symm ⟨x,hx⟩).1,(gluingMap.symm ⟨x,hx⟩).2,
      (TwoGluing.inclusion_symm_transition collar gluingMap ⟨x,hx⟩).symm⟩


-- @@ L1277-1283 verbatim
lemma realCompactMetric_nonpositive_off_neck {δ : ℝ} (hδ : δ ∈ Ioc 0 (1/2))
    (p : GluedConstruction.Manifold) (hp : p ∉ openNeck) :
    NonpositiveAt (realCompactMetric hδ) p := by
  obtain ⟨i,x,rfl⟩ := TwoGluing.inclusion_surjective collar gluingMap p
  apply (pieceInclusionIsometry hδ i).nonpositiveAt_image (mem_univ x)
  apply realPiece_nonpositive hδ i
  exact fun hx => hp (inclusion_collar_mem_openNeck i hx)

-- @@ L1284-1284 verbatim
end ThreeManifold.CompactMetric


-- @@ L1286-1286 verbatim
end


-- @@ L1288-1288 verbatim
end OAI
