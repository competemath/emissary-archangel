import OAI.Geometry.KahlerSplitting.Removable


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Manifold ContDiff

-- @@ L7-7 verbatim
open Set Topology Filter Metric

-- @@ L8-8 verbatim
open Set MeasureTheory Metric Filter Topology

-- @@ L9-9 verbatim
open scoped Interval

-- @@ L10-10 verbatim
open Set MeasureTheory

-- @@ L11-11 verbatim
open scoped ENNReal

-- @@ L12-12 verbatim
open Set Metric

-- @@ L13-13 verbatim
open scoped ENNReal NNReal

-- @@ L14-14 verbatim
open Set Metric Filter Topology

-- @@ L15-15 verbatim
open scoped Manifold ENNReal NNReal

-- @@ L16-16 verbatim
open Complex

-- @@ L17-17 verbatim
open Set Filter Topology

-- @@ L18-18 verbatim
open Set Metric Filter Topology Complex

-- @@ L19-19 verbatim
open Set Metric Filter Topology MeasureTheory Complex

-- @@ L20-20 verbatim
open Set Metric Filter Topology MeasureTheory

-- @@ L21-21 verbatim
open scoped Manifold ENNReal

-- @@ L22-22 verbatim
open Set

-- @@ L23-23 verbatim
open scoped Manifold


-- @@ L25-25 verbatim
namespace UniversalCoverSplitting

-- @@ L26-26 verbatim
variable {n r s : ℕ} {X : ComplexManifold n}


-- @@ L28-46 verbatim
theorem chart_mfderiv_inverses (c : X.Carrier) {z : Model n}
    (hz : z ∈ (extChartAt (model n) c).target) :
    (mfderiv (model n) (model n) (extChartAt (model n) c) ((extChartAt (model n) c).symm z)).comp
      (mfderiv (model n) (model n) (extChartAt (model n) c).symm z) =
      ContinuousLinearMap.id ℂ (Model n) ∧
    (mfderiv (model n) (model n) (extChartAt (model n) c).symm z).comp
      (mfderiv (model n) (model n) (extChartAt (model n) c) ((extChartAt (model n) c).symm z)) =
      ContinuousLinearMap.id ℂ (Model n) := by
  constructor
  · have h := mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm hz
    change (mfderiv (model n) (model n) (extChartAt (model n) c) ((extChartAt (model n) c).symm z)).comp
      (mfderivWithin (model n) (model n) (extChartAt (model n) c).symm (range (model n)) z) =
      ContinuousLinearMap.id ℂ (Model n) at h
    simpa only [ModelWithCorners.range_eq_univ,mfderivWithin_univ] using h
  · have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt hz
    change (mfderivWithin (model n) (model n) (extChartAt (model n) c).symm (range (model n)) z).comp
      (mfderiv (model n) (model n) (extChartAt (model n) c) ((extChartAt (model n) c).symm z)) =
      ContinuousLinearMap.id ℂ (Model n) at h
    simpa only [ModelWithCorners.range_eq_univ,mfderivWithin_univ] using h


-- @@ L48-63 verbatim
lemma projectionInChart_self (P : ProjectionField X) (c : X.Carrier) :
    projectionInChart P c (extChartAt (model n) c c) = P c := by
  let e := extChartAt (model n) c
  let A : X.Carrier → Model n →L[ℂ] Model n := fun x ↦ mfderiv (model n) (model n) e x
  let B : Model n → Model n →L[ℂ] Model n := fun z ↦ mfderiv (model n) (model n) e.symm z
  let T : X.Carrier → Model n →L[ℂ] Model n := fun x ↦ P x
  have hA : A c = ContinuousLinearMap.id ℂ (Model n) := mfderiv_extChartAt_self
  have hB : B (e c) = ContinuousLinearMap.id ℂ (Model n) := by
    have h := mfderivWithin_range_extChartAt_symm (I := model n) (x := c)
    change (mfderivWithin (model n) (model n) e.symm (range (model n)) (e c) :
      Model n →L[ℂ] Model n) = ContinuousLinearMap.id ℂ (Model n) at h
    simp only [ModelWithCorners.range_eq_univ,mfderivWithin_univ] at h
    exact h
  change (A (e.symm (e c))).comp ((T (e.symm (e c))).comp (B (e c))) = T c
  rw [e.left_inv (mem_extChartAt_source c),hA,hB]
  simp


-- @@ L65-77 verbatim
lemma projectionInChart_idempotent (S : HolomorphicSplitting X r s) (c : X.Carrier)
    {z : Model n} (hz : z ∈ (extChartAt (model n) c).target) (v : Model n) :
    projectionInChart S.projection c z (projectionInChart S.projection c z v) =
      projectionInChart S.projection c z v := by
  let e := extChartAt (model n) c
  let a : Model n →L[ℂ] Model n := mfderiv (model n) (model n) e (e.symm z)
  let b : Model n →L[ℂ] Model n := mfderiv (model n) (model n) e.symm z
  have hba : b.comp a = ContinuousLinearMap.id ℂ (Model n) := (chart_mfderiv_inverses c hz).2
  have hba' (u : Model n) : b (a u) = u := congrArg (fun L : Model n →L[ℂ] Model n ↦ L u) hba
  let T : Model n →L[ℂ] Model n := S.projection (e.symm z)
  have hT (u : Model n) : T (T u) = T u := S.idempotent (e.symm z) u
  change a (T (b (a (T (b v))))) = a (T (b v))
  rw [hba',hT]


-- @@ L79-92 verbatim
lemma projectionInChart_complement (P : ProjectionField X) (c : X.Carrier)
    {z : Model n} (hz : z ∈ (extChartAt (model n) c).target) :
    projectionInChart (fun x ↦ ContinuousLinearMap.id ℂ (Tangent X x)-P x) c z =
      ContinuousLinearMap.id ℂ (Model n)-projectionInChart P c z := by
  let e := extChartAt (model n) c
  let a : Model n →L[ℂ] Model n := mfderiv (model n) (model n) e (e.symm z)
  let b : Model n →L[ℂ] Model n := mfderiv (model n) (model n) e.symm z
  have hab : a.comp b = ContinuousLinearMap.id ℂ (Model n) := (chart_mfderiv_inverses c hz).1
  have hab' (u : Model n) : a (b u) = u := congrArg (fun L : Model n →L[ℂ] Model n ↦ L u) hab
  let T : Model n →L[ℂ] Model n := P (e.symm z)
  apply ContinuousLinearMap.ext
  intro v
  change a (b v-T (b v)) = v-a (T (b v))
  rw [map_sub,hab']


-- @@ L94-94 verbatim
end UniversalCoverSplitting


-- @@ L96-96 verbatim
open Set Metric Filter Topology Asymptotics


-- @@ L98-98 verbatim
namespace UniversalCoverSplitting

-- @@ L99-101 verbatim
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]


-- @@ L103-166 verbatim
theorem uniform_strict_derivative_on_compact {f : E → F} {D : E → E →L[𝕜] F}
    {K : Set E} (hK : IsCompact K)
    (hder : ∀ x ∈ K, HasStrictFDerivAt f (D x) x)
    (hD : ∀ x ∈ K, ContinuousAt D x) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ a ∈ K, ∀ x ∈ ball a δ, ∀ y ∈ ball a δ,
      ‖f x - f y - D a (x-y)‖ ≤ ε * ‖x-y‖ := by
  classical
  have hlocal (a : K) : ∃ d > 0,
      (∀ b ∈ ball a.val d, ‖D b-D a.val‖ ≤ ε/2) ∧
      ∀ x ∈ ball a.val (2*d), ∀ y ∈ ball a.val (2*d),
        ‖f x-f y-D a.val (x-y)‖ ≤ (ε/2)*‖x-y‖ := by
    have he := (hasStrictFDerivAt_iff_isLittleO.mp (hder a.val a.property)).bound (half_pos hε)
    obtain ⟨r,hr,hrb⟩ := Metric.eventually_nhds_iff_ball.mp he
    obtain ⟨s,hs,hsb⟩ := Metric.eventually_nhds_iff_ball.mp
      ((hD a.val a.property) (ball_mem_nhds (D a.val) (half_pos hε)))
    let d := min (r/3) s
    have hd : 0 < d := lt_min (by linarith) hs
    refine ⟨d,hd,?_,?_⟩
    · intro b hb
      have : b ∈ ball a.val s := ball_subset_ball (min_le_right _ _) hb
      exact le_of_lt (by simpa only [mem_ball,dist_eq_norm] using hsb b this)
    · intro x hx y hy
      apply hrb (x,y)
      rw [← ball_prod_same]
      have hcmp : 2*d ≤ r := by have := min_le_left (r/3) s; dsimp [d]; linarith
      exact ⟨ball_subset_ball hcmp hx,ball_subset_ball hcmp hy⟩
  choose d hd hDb hstrict using hlocal
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun a : K ↦ ball a.val (d a))
    (fun _ ↦ isOpen_ball) (fun a ha ↦ mem_iUnion.mpr ⟨⟨a,ha⟩,mem_ball_self (hd ⟨a,ha⟩)⟩)
  by_cases hsn : s.Nonempty
  · refine ⟨s.inf' hsn d, (Finset.lt_inf'_iff hsn).mpr (fun a _ ↦ hd a),?_⟩
    intro a ha x hx y hy
    obtain ⟨b,hb⟩ := mem_iUnion.mp (hs ha)
    obtain ⟨hbs,hab⟩ := mem_iUnion.mp hb
    have hdle : s.inf' hsn d ≤ d b := s.inf'_le d hbs
    have hxb : x ∈ ball b.val (2*d b) := by
      have : dist x b.val ≤ dist x a + dist a b.val := dist_triangle _ _ _
      change dist x a < _ at hx
      change dist a b.val < _ at hab
      change dist x b.val < _
      linarith
    have hyb : y ∈ ball b.val (2*d b) := by
      have : dist y b.val ≤ dist y a + dist a b.val := dist_triangle _ _ _
      change dist y a < _ at hy
      change dist a b.val < _ at hab
      change dist y b.val < _
      linarith
    have herr := hstrict b x hxb y hyb
    have hop : ‖D b.val-D a‖ ≤ ε/2 := by
      rw [norm_sub_rev]
      exact hDb b a hab
    calc
      ‖f x-f y-D a (x-y)‖ =
          ‖(f x-f y-D b.val (x-y)) + (D b.val-D a) (x-y)‖ := by
        congr 1; simp only [sub_apply]; abel
      _ ≤ ‖f x-f y-D b.val (x-y)‖ + ‖(D b.val-D a) (x-y)‖ := norm_add_le _ _
      _ ≤ (ε/2)*‖x-y‖ + (ε/2)*‖x-y‖ :=
        add_le_add herr (((D b.val-D a).le_opNorm _).trans (by gcongr))
      _ = ε*‖x-y‖ := by ring
  · refine ⟨1,zero_lt_one,?_⟩
    intro a ha
    have := hs ha
    simp only [Finset.not_nonempty_iff_eq_empty.mp hsn,Finset.notMem_empty, iUnion_of_empty,
      iUnion_empty,mem_empty_iff_false] at this


-- @@ L168-168 verbatim
end UniversalCoverSplitting

-- @@ L169-169 verbatim
open Set Metric Filter Topology Asymptotics


-- @@ L171-171 verbatim
namespace UniversalCoverSplitting

-- @@ L172-175 verbatim
variable {𝕜 E F T : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace T] [CompactSpace T]


-- @@ L177-188 verbatim
def pathLinearApply (A : C(T,E →L[𝕜] F)) : C(T,E) →L[𝕜] C(T,F) :=
  LinearMap.mkContinuous
    { toFun := fun η ↦ ⟨fun t ↦ A t (η t), by fun_prop⟩
      map_add' := by intros; ext; simp
      map_smul' := by intros; ext; simp }
    ‖A‖ (fun η ↦ by
      dsimp only [LinearMap.coe_mk, AddHom.coe_mk]
      apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg η))).mpr
      intro t
      exact ((A t).le_opNorm (η t)).trans
        (mul_le_mul (A.norm_coe_le_norm t) (η.norm_coe_le_norm t)
          (norm_nonneg _) (norm_nonneg _)))


-- @@ L190-191 verbatim
@[simp] theorem pathLinearApply_apply (A : C(T,E →L[𝕜] F)) (η : C(T,E)) (t : T) :
    pathLinearApply A η t = A t (η t) := rfl


-- @@ L193-196 verbatim
def pathDerivative (D : E → E →L[𝕜] F) (γ : C(T,E))
    (hD : ∀ t, ContinuousAt D (γ t)) : C(T,E →L[𝕜] F) :=
  ⟨fun t ↦ D (γ t), continuous_iff_continuousAt.mpr
    (fun t ↦ (hD t).comp γ.continuous.continuousAt)⟩


-- @@ L198-224 verbatim
theorem hasStrictFDerivAt_pathCompose (f : C(E,F)) (D : E → E →L[𝕜] F)
    (γ : C(T,E)) (hder : ∀ t, HasStrictFDerivAt f (D (γ t)) (γ t))
    (hD : ∀ t, ContinuousAt D (γ t)) :
    HasStrictFDerivAt (fun η : C(T,E) ↦ f.comp η)
      (pathLinearApply (pathDerivative D γ hD)) γ := by
  rw [hasStrictFDerivAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  obtain ⟨δ,hδ,hb⟩ := uniform_strict_derivative_on_compact
    (isCompact_range γ.continuous)
    (by rintro x ⟨t,rfl⟩; exact hder t)
    (by rintro x ⟨t,rfl⟩; exact hD t) hε
  apply Metric.eventually_nhds_iff_ball.mpr
  refine ⟨δ,hδ,?_⟩
  intro p hp
  rw [← ball_prod_same] at hp
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro t
  have hx : p.1 t ∈ ball (γ t) δ := by
    have ht := (p.1-γ).norm_coe_le_norm t
    rw [mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt ht (by simpa only [mem_ball,dist_eq_norm] using hp.1)
  have hy : p.2 t ∈ ball (γ t) δ := by
    have ht := (p.2-γ).norm_coe_le_norm t
    rw [mem_ball, dist_eq_norm]
    exact lt_of_le_of_lt ht (by simpa only [mem_ball,dist_eq_norm] using hp.2)
  exact (hb (γ t) (mem_range_self t) _ hx _ hy).trans
    (mul_le_mul_of_nonneg_left ((p.1-p.2).norm_coe_le_norm t) hε.le)


-- @@ L226-226 verbatim
end UniversalCoverSplitting

-- @@ L227-227 verbatim
open Set Metric Filter Topology


-- @@ L229-229 verbatim
namespace UniversalCoverSplitting

-- @@ L230-233 verbatim
variable {𝕜 E F T : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace T] [CompactSpace T]

 
-- @@ L235-243 verbatim
theorem pathLinearApply_norm_le (A : C(T,E →L[𝕜] F)) :
    ‖pathLinearApply A‖ ≤ ‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (pathLinearApply A) (norm_nonneg A)
  intro η
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg A) (norm_nonneg η))).mpr
  intro t
  exact ((A t).le_opNorm (η t)).trans
    (mul_le_mul (A.norm_coe_le_norm t) (η.norm_coe_le_norm t)
      (norm_nonneg _) (norm_nonneg _))


-- @@ L245-250 verbatim
def pathLinearApplyL : C(T,E →L[𝕜] F) →L[𝕜] C(T,E) →L[𝕜] C(T,F) :=
  LinearMap.mkContinuous
    { toFun := fun A : C(T,E →L[𝕜] F) ↦ pathLinearApply A
      map_add' := by intros; ext η t; simp
      map_smul' := by intros; ext η t; simp }
    1 (fun A ↦ by simpa using pathLinearApply_norm_le A)


-- @@ L252-253 verbatim
@[simp] theorem pathLinearApplyL_apply (A : C(T,E →L[𝕜] F)) :
    pathLinearApplyL A = pathLinearApply A := rfl


-- @@ L255-274 verbatim
theorem contDiffAt_pathCompose_one (f : C(E,F)) (D : C(E,E →L[𝕜] F))
    {U : Set E} (hU : IsOpen U)
    (hder : ∀ x ∈ U, HasFDerivAt f (D x) x)
    (γ : C(T,E)) (hγ : range γ ⊆ U) :
    ContDiffAt 𝕜 1 (fun η : C(T,E) ↦ f.comp η) γ := by
  let O : Set C(T,E) := {η | range η ⊆ U}
  have hO : IsOpen O := ContinuousMap.isOpen_setOfPred_range_subset hU
  have hcoef : Continuous (fun η : C(T,E) ↦ pathLinearApply (D.comp η)) :=
    pathLinearApplyL.continuous.comp D.continuous_postcomp
  apply contDiffAt_one_iff.mpr
  refine ⟨fun η ↦ pathLinearApply (D.comp η), O, hO.mem_nhds hγ,
    hcoef.continuousOn, ?_⟩
  intro η hη
  have hs (t : T) : HasStrictFDerivAt f (D (η t)) (η t) := by
    apply hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    · filter_upwards [hU.mem_nhds (hη (mem_range_self t))] with x hx
      exact hder x hx
    · exact D.continuous.continuousAt
  have hD (t : T) : ContinuousAt D (η t) := D.continuous.continuousAt
  convert! (hasStrictFDerivAt_pathCompose f D η hs hD).hasFDerivAt using 1


-- @@ L276-276 verbatim
end UniversalCoverSplitting


-- @@ L278-278 verbatim
end


-- @@ L280-280 verbatim
end OAI
