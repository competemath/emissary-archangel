import OAI.Analysis.TracialSplitting.CoefficientBounds


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uE uF



-- @@ L8-8 verbatim
section


-- @@ L10-10 verbatim
noncomputable section


-- @@ L12-12 verbatim
noncomputable section


-- @@ L14-14 verbatim
open scoped ComplexOrder InnerProductSpace


-- @@ L16-16 verbatim
open UniformSpace.Completion


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
open scoped ComplexOrder InnerProductSpace


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
open scoped TensorProduct InnerProductSpace


-- @@ L30-30 verbatim
open UniformSpace.Completion


-- @@ L32-32 verbatim
noncomputable section


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-36 verbatim
noncomputable section


-- @@ L38-38 verbatim
noncomputable section


-- @@ L40-40 verbatim
noncomputable section


-- @@ L42-42 verbatim
noncomputable section


-- @@ L44-44 verbatim
noncomputable section


-- @@ L46-46 verbatim
noncomputable section


-- @@ L48-48 verbatim
noncomputable section


-- @@ L50-50 verbatim
noncomputable section


-- @@ L52-52 verbatim
noncomputable section


-- @@ L54-54 verbatim
open scoped ComplexOrder InnerProductSpace


-- @@ L56-56 verbatim
open UniformSpace.Completion


-- @@ L58-58 verbatim
noncomputable section


-- @@ L60-60 verbatim
open scoped ComplexOrder TensorProduct InnerProductSpace


-- @@ L62-62 verbatim
open UniformSpace.Completion UnitalTomsWinter


-- @@ L64-64 verbatim
noncomputable section


-- @@ L66-66 verbatim
open scoped ComplexOrder TensorProduct InnerProductSpace


-- @@ L68-68 verbatim
open Pureness UnitalTomsWinter


-- @@ L70-70 verbatim
noncomputable section


-- @@ L72-72 verbatim
open scoped Pointwise


-- @@ L74-74 verbatim
noncomputable section


-- @@ L76-76 verbatim
open scoped ComplexOrder


-- @@ L78-78 verbatim
noncomputable section


-- @@ L80-80 verbatim
open scoped ComplexOrder


-- @@ L82-82 verbatim
namespace NuclearTrace


-- @@ L84-84 verbatim
variable {A K I : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


-- @@ L86-86 verbatim
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]


-- @@ L88-88 verbatim
variable [Fintype I]


-- @@ L90-95 verbatim
def coefficientSelfAdjMap (α : A →⋆ₐ[ℂ] (K →L[ℂ] K))
    {n : ℕ} (k : Fin n → K) (a : Fin n → A) : selfAdjoint A →ₗ[ℝ] selfAdjoint A where
  toFun x := ⟨coefficientMap α k a x,coefficientMap_selfAdjoint α k a _ x.property⟩
  map_add' left right := Subtype.ext ((coefficientMap α k a).map_add left right)
  map_smul' scalar value :=
    Subtype.ext ((coefficientMap α k a).map_smul_of_tower scalar (value : A))


-- @@ L97-100 verbatim
def coefficientCone (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    ConvexCone ℝ (selfAdjoint A →ₗ[ℝ] selfAdjoint A) :=
  ConvexCone.hull ℝ {L | ∃ (n : ℕ) (k : Fin n → K) (a : Fin n → A),
    L = coefficientSelfAdjMap α k a}


-- @@ L102-108 verbatim
omit [PartialOrder A] [StarOrderedRing A] in
lemma coefficientCone_zero (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) :
    (0 : selfAdjoint A →ₗ[ℝ] selfAdjoint A) ∈ coefficientCone α := by
  apply ConvexCone.subset_hull
  refine ⟨0,Fin.elim0,Fin.elim0,?_⟩
  ext x
  simp [coefficientSelfAdjMap,coefficientMap]


-- @@ L110-114 verbatim
def evalTuple (x : I → selfAdjoint A) :
    (selfAdjoint A →ₗ[ℝ] selfAdjoint A) →ₗ[ℝ] (I → selfAdjoint A) where
  toFun L i := L (x i)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- @@ L116-118 verbatim
def tracialTupleSeminorm (τ : Pureness.TracialState A) :
    Seminorm ℝ (I → selfAdjoint A) :=
  ∑ i, (CurrentMain.tracialOneSeminorm τ).comp (LinearMap.proj i)


-- @@ L120-123 verbatim
@[simp] lemma tracialTupleSeminorm_apply (τ : Pureness.TracialState A)
    (x : I → selfAdjoint A) :
    tracialTupleSeminorm τ x = ∑ i, CurrentMain.traceOneNorm τ (x i) := by
  simp [tracialTupleSeminorm]


-- @@ L125-130 verbatim
lemma tracialTupleSeminorm_continuous (τ : Pureness.TracialState A) :
    Continuous (tracialTupleSeminorm (I := I) τ) := by
  simp only [funext (tracialTupleSeminorm_apply (I := I) τ)]
  apply continuous_finsetSum
  intro i _
  exact (CurrentMain.tracialOneSeminorm_continuous τ).comp (continuous_apply i)


-- @@ L132-135 verbatim
lemma tracialTupleSeminorm_single [DecidableEq I] (τ : Pureness.TracialState A)
    (i : I) (a : selfAdjoint A) :
    tracialTupleSeminorm τ (Pi.single i a) = CurrentMain.tracialOneSeminorm τ a := by
  simp [tracialTupleSeminorm_apply,Pi.single_apply,apply_ite,CurrentMain.traceOneNorm]


-- @@ L137-181 verbatim
theorem nuclear_tracial_coefficient_approximation (hA : Pureness.IsNuclear.{0,0} A)
    (α : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (hα : Function.Injective α)
    (τ : Pureness.TracialState A) (x : I → selfAdjoint A)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ L ∈ coefficientCone α,
      ∑ i, CurrentMain.traceOneNorm τ ((x i : A) - L (x i)) < ε := by
  classical
  let C := (coefficientCone α).map (evalTuple x)
  have h0 : (0 : I → selfAdjoint A) ∈ C := by
    exact ⟨0,coefficientCone_zero α,by ext i; rfl⟩
  have hs : ∀ t : ℝ, 0 ≤ t → ∀ s ∈ C, t • s ∈ C := by
    intro t ht s hs
    obtain rfl | ht := ht.eq_or_lt
    · simpa using h0
    · exact C.smul_mem ht hs
  have hdual (f : (I → selfAdjoint A) →L[ℝ] ℝ)
      (hf : ∃ c : ℝ, 0 ≤ c ∧ ∀ y, |f y| ≤ c * tracialTupleSeminorm τ y)
      (hfc : ∀ s ∈ C, f s ≤ 0) : f x ≤ 0 := by
    obtain ⟨c,hc,hf⟩ := hf
    let l (i : I) : selfAdjoint A →ₗ[ℝ] ℝ :=
      f.toLinearMap.comp (LinearMap.single ℝ (fun _ : I => selfAdjoint A) i)
    have hl (i : I) (a : selfAdjoint A) (ha : 0 ≤ (a : A)) :
        |l i a| ≤ c * (τ.functional a).re := by
      have hh := hf (Pi.single i a)
      rw [tracialTupleSeminorm_single,CurrentMain.tracialOneSeminorm_of_nonneg τ a ha] at hh
      exact hh
    have he (y : I → selfAdjoint A) : (∑ i, l i (y i)) = f y := by
      change (∑ i, f (Pi.single i (y i))) = f y
      rw [← map_sum]
      congr 1
      exact Finset.univ_sum_single y
    rw [← he x]
    apply nuclear_coefficient_dual_bound hA α hα τ.functional τ.normalized x l hc hl
    intro n k a
    rw [he]
    apply hfc
    refine ⟨coefficientSelfAdjMap α k a,?_,rfl⟩
    exact ConvexCone.subset_hull ⟨n,k,a,rfl⟩
  obtain ⟨s,hs,hclose⟩ := seminorm_cone_approximation_of_dual
    (tracialTupleSeminorm τ) (tracialTupleSeminorm_continuous τ)
    C C.convex h0 hs x hdual hε
  obtain ⟨L,hL,rfl⟩ := hs
  refine ⟨L,hL,?_⟩
  simpa only [tracialTupleSeminorm_apply,Pi.sub_apply,evalTuple,
    LinearMap.coe_mk,AddHom.coe_mk,(selfAdjoint A).coe_sub] using hclose


-- @@ L183-183 verbatim
end NuclearTrace


-- @@ L185-185 verbatim
noncomputable section


-- @@ L187-187 verbatim
namespace NuclearTrace


-- @@ L189-189 verbatim
open Set


-- @@ L191-191 verbatim
variable {E : Type uE} {F : Type uF}


-- @@ L193-193 verbatim
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]


-- @@ L195-195 verbatim
variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]


-- @@ L197-197 verbatim
variable [TopologicalSpace F] [AddCommGroup F] [Module ℝ F]


-- @@ L199-199 verbatim
variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]


-- @@ L201-231 verbatim
theorem compact_convex_uniform_cost {X : Set E} {Y : Set F}
    (hXne : X.Nonempty) (hX : IsCompact X) (hXconv : Convex ℝ X)
    (hYconv : Convex ℝ Y) (c : E → F → ℝ)
    (hcX : ∀ y ∈ Y, Continuous (fun x => c x y))
    (hcXconc : ∀ y ∈ Y, ConcaveOn ℝ X (fun x => c x y))
    (hcY : ∀ x ∈ X, ContinuousOn (c x) Y)
    (hcYconv : ∀ x ∈ X, ConvexOn ℝ Y (c x))
    {ε : ℝ} (hpoint : ∀ x ∈ X, ∃ y ∈ Y, c x y < ε) :
    ∃ y ∈ Y, ∀ x ∈ X, c x y < ε := by
  classical
  let U (y : Y) : Set E := {x | c x y < ε}
  have hUopen (y : Y) : IsOpen (U y) := (hcX y y.property).isOpen_preimage _ isOpen_Iio
  have hcover : X ⊆ ⋃ y : Y, U y := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := hpoint x hx
    exact mem_iUnion.mpr ⟨⟨y,hy⟩,hxy⟩
  obtain ⟨s,hs⟩ := hX.elim_finite_subcover U hUopen hcover
  have hfinitePoint : ∀ x ∈ X, ∃ y ∈ Subtype.val '' (s : Set Y), -ε < -c x y := by
    intro x hx
    obtain ⟨y,hy,hxy⟩ := mem_iUnion₂.mp (hs hx)
    exact ⟨y,⟨y,hy,rfl⟩,neg_lt_neg hxy⟩
  obtain ⟨y,hy,hyall⟩ := Sion.exists_lt_iInf_of_lt_iInf_of_finite
    (f := fun x y => -c x y) hXne hX
    (fun y hy => (hcX y hy).neg.continuousOn.lowerSemicontinuousOn)
    (fun y hy => (hcXconc y hy).neg.quasiconvexOn)
    hYconv
    (fun x hx => (hcY x hx).neg.upperSemicontinuousOn)
    (fun x hx => (hcYconv x hx).neg.quasiconcaveOn)
    hXconv (s.finite_toSet.image Subtype.val)
    (fun _ hy => by obtain ⟨y,_,rfl⟩ := hy; exact y.property) hfinitePoint
  exact ⟨y,hy,fun x hx => neg_lt_neg_iff.mp (hyall x hx)⟩


-- @@ L233-233 verbatim
end NuclearTrace


-- @@ L235-235 verbatim
end


-- @@ L237-237 verbatim
end


-- @@ L239-239 verbatim
end


-- @@ L241-241 verbatim
end


-- @@ L243-243 verbatim
end


-- @@ L245-245 verbatim
end


-- @@ L247-247 verbatim
end


-- @@ L249-249 verbatim
end


-- @@ L251-251 verbatim
end


-- @@ L253-253 verbatim
end


-- @@ L255-255 verbatim
end


-- @@ L257-257 verbatim
end


-- @@ L259-259 verbatim
end


-- @@ L261-261 verbatim
end


-- @@ L263-263 verbatim
end


-- @@ L265-265 verbatim
end


-- @@ L267-267 verbatim
end


-- @@ L269-269 verbatim
end


-- @@ L271-271 verbatim
end


-- @@ L273-273 verbatim
end


-- @@ L275-275 verbatim
end


-- @@ L277-277 verbatim
end


-- @@ L279-279 verbatim
end


-- @@ L281-281 verbatim
end


-- @@ L283-283 verbatim
end OAI
