import OAI.Probability.GaussianPropeller.CapNumeric


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open MeasureTheory ProbabilityTheory

-- @@ L6-6 verbatim
open scoped ENNReal

-- @@ L7-7 verbatim
open scoped RealInnerProductSpace

-- @@ L8-8 verbatim
open scoped RealInnerProductSpace

-- @@ L9-9 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L10-10 verbatim
open scoped ENNReal RealInnerProductSpace

-- @@ L11-11 verbatim
open Filter

-- @@ L12-12 verbatim
open scoped Topology

-- @@ L13-13 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L14-14 verbatim
open scoped Topology

-- @@ L15-15 verbatim
open scoped RealInnerProductSpace

-- @@ L16-16 verbatim
open Set Filter

-- @@ L17-17 verbatim
open scoped Topology RealInnerProductSpace

-- @@ L18-18 verbatim
open scoped NNReal

-- @@ L19-19 verbatim
open Set Filter

-- @@ L20-20 verbatim
open scoped Topology RealInnerProductSpace NNReal

-- @@ L21-21 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L22-22 verbatim
open scoped Topology RealInnerProductSpace

-- @@ L23-23 verbatim
open MeasureTheory Set Filter

-- @@ L24-24 verbatim
open scoped Topology BigOperators

-- @@ L25-25 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L26-26 verbatim
open scoped RealInnerProductSpace Topology

-- @@ L27-27 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L28-28 verbatim
open scoped RealInnerProductSpace Topology ENNReal

-- @@ L29-29 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L30-30 verbatim
open scoped RealInnerProductSpace Topology ENNReal

-- @@ L31-31 verbatim
open Metric

-- @@ L32-32 verbatim
open MeasureTheory ProbabilityTheory Set

-- @@ L33-33 verbatim
open scoped RealInnerProductSpace ENNReal


-- @@ L35-35 verbatim
namespace GaussianPropeller.Reduction

-- @@ L36-36 verbatim
open Coords

-- @@ L37-37 verbatim
variable {d k n : ℕ} [NeZero k]


-- @@ L39-43 verbatim
omit [NeZero k] in
lemma closedCell_cone [NeZero k] (z : Fin k → Space d) (i : Fin k) (r:ℝ) (hr:0<r)
    (x:Space d) : r•x ∈ closedCell z i ↔ x∈closedCell z i := by
  simp only [closedCell, mem_ofPred_eq,inner_smul_right]
  exact forall_congr' (fun j => mul_le_mul_iff_right₀ hr)


-- @@ L45-59 verbatim
lemma coordinates_law {V : Submodule ℝ (Space d)}
    (b : OrthonormalBasis (Fin (n+1)) ℝ V) :
    (gaussian d).map (fun x => b.repr (V.orthogonalProjectionOnto x)) = gaussian (n+1) := by
  have ho : Orthonormal ℝ (fun j => (b j : Space d)) := by
    constructor
    · intro j; exact b.orthonormal.1 j
    · intro j l hjl; exact b.orthonormal.2 hjl
  have he : (fun x => b.repr (V.orthogonalProjectionOnto x)) =
      WithLp.toLp 2 ∘ (fun x => fun j => ⟪(b j:Space d),x⟫) := by
    funext x; ext j
    simp only [Function.comp_apply,WithLp.ofLp_toLp,OrthonormalBasis.repr_apply_apply,
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  unfold gaussian
  rw [he,← Measure.map_map (PiLp.continuous_toLp 2 _).measurable (by fun_prop),
    Analytic.map_orthonormal_stdGaussian _ ho,map_pi_eq_stdGaussian]


-- @@ L61-114 verbatim
lemma exists_span_cone {z : Fin k → Space d} (hsum : ∑ j,z j=0)
    (hneg : Pairwise (fun j l=>⟪z j,z l⟫<0)) (i:Fin k) (hzi:z i≠0)
    (hdim : k-1=n+1) (hcen : centroid (closedCell z i)=z i) :
    ∃ K : Set (Space (n+1)), MeasurableSet K ∧
      (∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K) ∧
      (gaussian (n+1)).real K=(gaussian d).real (closedCell z i) ∧
      (∫ x, K.indicator (fun x : Space (n+1)=> x 0) x ∂gaussian (n+1))=‖z i‖ := by
  let V := Submodule.span ℝ (range z)
  let zv : Fin k → V := fun j=>⟨z j,Submodule.subset_span (mem_range_self j)⟩
  have hnorm : 0<‖z i‖ := norm_pos_iff.mpr hzi
  let e : V := ‖z i‖⁻¹ • zv i
  have he : ‖e‖=1 := by simp [e,zv,norm_smul,hnorm.ne']
  obtain ⟨b,hb⟩ := exists_basis_zero
    (show Module.finrank ℝ V=n+1 by rw [Gram.finrank_span z hneg hsum i,Fintype.card_fin,hdim]) e he
  let T : Space d → Space (n+1) := fun x=> b.repr (V.orthogonalProjectionOnto x)
  let w : Fin k → Space (n+1) := fun j=>b.repr (zv j)
  let K := closedCell w i
  have hT : Continuous T := b.repr.continuous.comp V.orthogonalProjectionOnto.continuous
  have hm : (gaussian d).map T=gaussian (n+1) := coordinates_law b
  have hs : ∀ j x, ⟪w j,T x⟫=⟪z j,x⟫ := by
    intro j x
    dsimp [w,T]
    rw [b.repr.inner_map_map,Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left]
  have hp : T ⁻¹' K=closedCell z i := by
    ext x
    simp only [K,closedCell,mem_preimage,mem_ofPred_eq,hs]
  refine ⟨K,measurableSet_closedCell w i,closedCell_cone w i,?_,?_⟩
  · rw [← hm,measureReal_def,Measure.map_apply hT.measurable (measurableSet_closedCell w i),hp]
    rfl
  have ht0 : ∀ x, T x 0=‖z i‖⁻¹*⟪z i,x⟫ := by
    intro x
    dsimp [T]
    rw [b.repr_apply_apply,Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left,hb]
    simp only [e,Submodule.coe_smul,zv,real_inner_smul_left]
  have hi := integral_map (μ:=gaussian d) (φ:=T)
    (f:=K.indicator (fun x:Space (n+1)=>x 0)) hT.aemeasurable
    (((by fun_prop : Continuous (fun x:Space (n+1)=>x 0)).stronglyMeasurable.indicator
      (measurableSet_closedCell w i)).aestronglyMeasurable)
  rw [hm] at hi
  rw [hi]
  have heq : (fun x => K.indicator (fun x:Space (n+1)=>x 0) (T x)) =
      (closedCell z i).indicator (fun x=>‖z i‖⁻¹*⟪z i,x⟫) := by
    funext x
    have hh : T x∈K ↔ x∈closedCell z i := Set.ext_iff.mp hp x
    by_cases hx : x∈closedCell z i
    · simp only [indicator_of_mem hx,indicator_of_mem (hh.mpr hx),ht0]
    · simp only [indicator_of_notMem hx,indicator_of_notMem (mt hh.mp hx)]
  rw [heq,integral_indicator (measurableSet_closedCell z i),integral_const_mul]
  have hinner : (∫ x in closedCell z i, ⟪z i,x⟫ ∂gaussian d) =
      ⟪z i,centroid (closedCell z i)⟫ := Pair.integral_inner_eq_inner_integral _ _
  rw [hinner]
  change ‖z i‖⁻¹*⟪z i,centroid (closedCell z i)⟫=‖z i‖
  rw [hcen,real_inner_self_eq_norm_sq]
  field_simp


-- @@ L116-127 verbatim
lemma minimal_span_cone {A:Fin k→Set (Space d)} (hA:MinimalOptimal A)
    (hpos:0<value A) (hactive:∀ j,gaussian d (A j)≠0) (i:Fin k) (hdim:k-1=n+1) :
    ∃ K : Set (Space (n+1)), MeasurableSet K ∧
      (∀ r:ℝ, 0<r → ∀ x, r•x∈K ↔ x∈K) ∧
      (gaussian (n+1)).real K=(gaussian d).real (A i) ∧
      (∫ x, K.indicator (fun x : Space (n+1)=> x 0) x ∂gaussian (n+1))=‖centroid (A i)‖ := by
  obtain ⟨K,hK,hcone,hP,hM⟩ := exists_span_cone (sum_centroid_eq_zero hA.1.1)
    (fun j l hjl => negative_inner_of_minimal hA hjl (hactive j) (hactive l))
    i (active_centroid_ne_zero hA hpos (hactive i)) hdim
    (centroid_closedCell hA hpos (hactive i))
  refine ⟨K,hK,hcone,hP.trans ?_,hM⟩
  rw [measureReal_def,measureReal_def,measure_congr (active_eq_closedCell_ae hA hpos (hactive i))]


-- @@ L129-129 verbatim
end GaussianPropeller.Reduction


-- @@ L131-131 verbatim
end OAI
