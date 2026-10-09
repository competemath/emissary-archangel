import OAI.Analysis.CharacterCriterion.SquareZeroCone


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped TensorProduct

-- @@ L7-7 verbatim
open scoped InnerProductSpace

-- @@ L8-8 verbatim
open scoped BigOperators

-- @@ L9-9 verbatim
open Set Module

-- @@ L10-10 verbatim
open Topology

-- @@ L11-11 verbatim
open NormedSpace

-- @@ L12-12 verbatim
open scoped ComplexOrder

-- @@ L13-13 verbatim
open scoped ComplexOrder

-- @@ L14-14 verbatim
open scoped InnerProductSpace

-- @@ L15-15 verbatim
open scoped InnerProductSpace

-- @@ L16-16 verbatim
open NormedSpace

-- @@ L17-17 verbatim
open scoped TensorProduct InnerProductSpace

-- @@ L18-18 verbatim
open UniformSpace

-- @@ L19-19 verbatim
variable [instSize : KirchbergRordam.GenericRW.Size]

-- @@ L20-20 verbatim
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n



-- @@ L23-23 verbatim
namespace KirchbergRordam.GenericRW

-- @@ L24-24 verbatim
namespace ConeModel

-- @@ L25-25 verbatim
open scoped ContinuousMapZero BigOperators ComplexOrder

-- @@ L26-26 verbatim
abbrev M2 := CStarMatrix (Fin rankNum) (Fin rankNum) ℂ

-- @@ L27-27 verbatim
abbrev ConeMatrix := Matrix (Fin rankNum) (Fin rankNum) C(unitInterval, ℂ)₀


-- @@ L29-36 verbatim
def eval (t : unitInterval) : C(unitInterval, M2) →⋆ₐ[ℂ] M2 where
  toFun f := f t
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  commutes' _ := rfl
  map_star' _ := rfl



-- @@ L39-40 verbatim
def coneSubalgebra : StarSubalgebra ℂ C(unitInterval, M2) :=
  (⊥ : StarSubalgebra ℂ M2).comap (eval 0)


-- @@ L42-42 verbatim
abbrev Cone := coneSubalgebra


-- @@ L44-44 verbatim
def evaluate (t : unitInterval) : Cone →⋆ₐ[ℂ] M2 := (eval t).comp coneSubalgebra.subtype


-- @@ L46-48 verbatim
lemma evaluate_sum {ι : Type*} (s : Finset ι) (f : ι → Cone) (t : unitInterval) :
    ((∑ i ∈ s, f i : Cone): C(unitInterval,M2)) t = ∑ i ∈ s, (f i:C(unitInterval,M2)) t :=
  map_sum (evaluate t) f s


-- @@ L50-51 verbatim
lemma evaluate_add (f g : Cone) (t : unitInterval) :
    ((f+g:Cone):C(unitInterval,M2)) t = (f:C(unitInterval,M2)) t + (g:C(unitInterval,M2)) t := rfl


-- @@ L53-54 verbatim
lemma matrixSum_entry {ι : Type*} (s : Finset ι) (f : ι → M2) (i j : Fin rankNum) :
    (∑ k ∈ s, f k) i j = ∑ k ∈ s, f k i j := Matrix.sum_apply i j s f


-- @@ L56-57 verbatim
instance : FiniteDimensional ℂ M2 :=
  inferInstanceAs (FiniteDimensional ℂ (Matrix (Fin rankNum) (Fin rankNum) ℂ))


-- @@ L59-61 verbatim
instance coneClosed : IsClosed (coneSubalgebra : Set C(unitInterval, M2)) :=
  ((⊥ : StarSubalgebra ℂ M2).toSubalgebra.toSubmodule.closed_of_finiteDimensional).preimage
    (continuous_eval_const (0 : unitInterval))



-- @@ L64-75 verbatim
def coefficients : ConeMatrix →⋆ₙₐ[ℂ] C(unitInterval, M2) where
  toFun m := ⟨fun t => CStarMatrix.ofMatrix (fun i j => m i j t), by
    apply CStarMatrix.ofMatrixL.continuous.comp
    fun_prop⟩
  map_zero' := by ext t i j; rfl
  map_add' _ _ := by ext t i j; rfl
  map_smul' _ _ := by ext t i j; rfl
  map_mul' m n := by
    ext t i j
    change (∑ k, m i k * n k j) t = ∑ k, m i k t * n k j t
    simp
  map_star' _ := by ext t i j; rfl


-- @@ L77-78 verbatim
@[simp] lemma coefficients_apply (m : ConeMatrix) (t : unitInterval) (i j : Fin rankNum) :
    coefficients m t i j = m i j t := rfl


-- @@ L80-82 verbatim
lemma coefficients_zero (m : ConeMatrix) : coefficients m 0 = 0 := by
  ext i j
  exact map_zero (m i j)


-- @@ L84-85 verbatim
abbrev unitCoefficients : Unitization ℂ ConeMatrix →⋆ₐ[ℂ] C(unitInterval, M2) :=
  (Unitization.starLift (R := ℂ) (A := ConeMatrix) (C := C(unitInterval, M2))) coefficients


-- @@ L87-91 verbatim
lemma unitCoefficients_zero (m : Unitization ℂ ConeMatrix) :
    unitCoefficients m 0 = algebraMap ℂ M2 m.fst := by
  change (algebraMap ℂ C(unitInterval, M2) m.fst + coefficients m.snd) 0 = _
  rw [ContinuousMap.add_apply, coefficients_zero, add_zero]
  rfl


-- @@ L93-97 verbatim
def toCone : Unitization ℂ ConeMatrix →⋆ₐ[ℂ] Cone :=
  unitCoefficients.codRestrict coneSubalgebra fun m => by
    change unitCoefficients m 0 ∈ (⊥ : StarSubalgebra ℂ M2)
    rw [unitCoefficients_zero]
    exact StarSubalgebra.algebraMap_mem _ _


-- @@ L99-111 verbatim
lemma toCone_injective : Function.Injective toCone := by
  intro m n h
  have he := congrArg (fun f : Cone => (f : C(unitInterval, M2)) 0) h
  change unitCoefficients m 0 = unitCoefficients n 0 at he
  rw [unitCoefficients_zero, unitCoefficients_zero] at he
  have hf : m.fst = n.fst := (FaithfulSMul.algebraMap_injective ℂ M2) he
  apply Unitization.ext hf
  ext i j t
  have hh := congrArg (fun f : Cone => (f : C(unitInterval, M2)) t i j) h
  change (algebraMap ℂ M2 m.fst + coefficients m.snd t) i j =
    (algebraMap ℂ M2 n.fst + coefficients n.snd t) i j at hh
  rw [hf] at hh
  exact add_left_cancel hh


-- @@ L113-127 verbatim
lemma toCone_surjective : Function.Surjective toCone := by
  intro f
  obtain ⟨c, hc⟩ := f.property
  let m : ConeMatrix := fun i j =>
    ⟨⟨fun t => (f : C(unitInterval, M2)) t i j - (algebraMap ℂ M2 c) i j, by
      fun_prop⟩, by
      change (f : C(unitInterval, M2)) 0 i j - (algebraMap ℂ M2 c) i j = 0
      rw [show (f : C(unitInterval, M2)) 0 = algebraMap ℂ M2 c from hc.symm]
      exact sub_self _⟩
  refine ⟨⟨c, m⟩, ?_⟩
  apply Subtype.ext
  ext t i j
  change (algebraMap ℂ M2 c) i j + ((f : C(unitInterval, M2)) t i j -
    (algebraMap ℂ M2 c) i j) = (f : C(unitInterval, M2)) t i j
  ring



-- @@ L130-131 verbatim
def equiv : Unitization ℂ ConeMatrix ≃⋆ₐ[ℂ] Cone :=
  StarAlgEquiv.ofBijective toCone ⟨toCone_injective, toCone_surjective⟩


-- @@ L133-133 verbatim
end ConeModel


-- @@ L135-135 verbatim
open scoped ContinuousMapZero BigOperators ComplexOrder

-- @@ L136-136 verbatim
namespace ConeModel


-- @@ L138-139 verbatim
def corner (i j : Fin rankNum) : Cone :=
  toCone (Unitization.inr (Matrix.single i j (IntervalCalculus.coordMul 1)))


-- @@ L141-148 verbatim
lemma corner_apply (i j : Fin rankNum) (t : unitInterval) :
    (corner i j : C(unitInterval, M2)) t =
      (t : ℂ) • CStarMatrix.ofMatrix (Matrix.single i j 1) := by
  ext k l
  change ((algebraMap ℂ M2 0) + coefficients (Matrix.single i j (IntervalCalculus.coordMul 1)) t) k l = _
  simp only [map_zero, zero_add, coefficients_apply]
  by_cases hi : i = k <;> by_cases hj : j = l <;>
    simp [Matrix.single, hi, hj, IntervalCalculus.coordMul_apply]


-- @@ L150-150 verbatim
end ConeModel


-- @@ L152-152 verbatim
namespace SquareZeroCone.WeightedMatrix

-- @@ L153-153 verbatim
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]

-- @@ L154-154 verbatim
variable (W : WeightedMatrix A)


-- @@ L156-158 verbatim
def coneHom : ConeModel.Cone →⋆ₐ[ℂ] A :=
  ((Unitization.starLift (R := ℂ) (A := ConeMatrix) (C := A)) W.matrixHom).comp
    ConeModel.equiv.symm.toStarAlgHom


-- @@ L160-163 verbatim
lemma matrixHom_single (i j : Fin rankNum) (f : C(unitInterval, ℂ)₀) :
    W.matrixHom (Matrix.single i j f) = W.coeff i j f := by
  change (∑ k, ∑ l, W.coeff k l (Matrix.single i j f k l)) = _
  simp [Matrix.single, ite_and, apply_ite]


-- @@ L165-174 verbatim
lemma coneHom_corner (i j : Fin rankNum) : W.coneHom (ConeModel.corner i j) = W.x i j := by
  change (Unitization.starLift W.matrixHom)
    (ConeModel.equiv.symm (ConeModel.toCone
      (Unitization.inr (Matrix.single i j (IntervalCalculus.coordMul 1))))) = _
  rw [show ConeModel.toCone = ConeModel.equiv.toStarAlgHom from rfl]
  change (Unitization.starLift W.matrixHom) (ConeModel.equiv.symm
    (ConeModel.equiv (Unitization.inr (Matrix.single i j (IntervalCalculus.coordMul 1))))) = _
  rw [StarAlgEquiv.symm_apply_apply]
  change algebraMap ℂ A 0 + W.matrixHom (Matrix.single i j (IntervalCalculus.coordMul 1)) = W.x i j
  rw [map_zero, zero_add, W.matrixHom_single, W.coeff_coordMul, map_one, mul_one]

-- @@ L175-175 verbatim
end SquareZeroCone.WeightedMatrix

-- @@ L176-176 verbatim
end KirchbergRordam.GenericRW



-- @@ L179-179 verbatim
namespace KirchbergRordam.GenericRW

-- @@ L180-180 verbatim
namespace ClosedRightRange

-- @@ L181-181 verbatim
variable {A : Type*} [CStarAlgebra A]



-- @@ L184-185 verbatim
def space (a : A) : Submodule ℂ A :=
  (LinearMap.range (LinearMap.mulLeft ℂ a)).topologicalClosure


-- @@ L187-193 verbatim
omit instSize in
lemma mem_space.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    (a x : A) : a * x ∈ space a :=
  Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x)


-- @@ L195-201 verbatim
omit instSize in
lemma closed.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    (a : A) : IsClosed (space a : Set A) :=
  Submodule.isClosed_topologicalClosure _


-- @@ L203-204 verbatim
def embed (a : A) : A →ₗ[ℂ] space a :=
  (LinearMap.mulLeft ℂ a).codRestrict _ (mem_space a)


-- @@ L206-206 verbatim
@[simp] lemma embed_val (a x : A) : (embed a x : A) = a * x := rfl


-- @@ L208-223 verbatim
lemma dense (a : A) : DenseRange (embed a) := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro x
  rw [closure_subtype]
  change (x : A) ∈ closure (Subtype.val '' Set.range (embed a))
  have h : Subtype.val '' Set.range (embed a) = Set.range (fun z : A => a * z) := by
    ext y
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, rfl⟩
    · rintro ⟨z, rfl⟩
      exact ⟨embed a z, ⟨z, rfl⟩, rfl⟩
  rw [h]
  exact x.property


-- @@ L225-239 verbatim
omit instSize in
lemma norm_mul_eq.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {a b : A} (h : star a * a = star b * b) (x : A) :
    ‖a * x‖ = ‖b * x‖ := by
  have hh : ‖a * x‖ ^ 2 = ‖b * x‖ ^ 2 := by
    simp only [pow_two, ← CStarRing.norm_star_mul_self, star_mul]
    congr 1
    calc
      _ = star x * (star a * a) * x := by noncomm_ring
      _ = star x * (star b * b) * x := by rw [h]
      _ = _ := by noncomm_ring
  nlinarith [norm_nonneg (a*x), norm_nonneg (b*x)]



-- @@ L242-243 verbatim
def transport (a b : A) : space a →L[ℂ] A :=
  (LinearMap.mulLeft ℂ b).extendOfNorm (embed a)


-- @@ L245-248 verbatim
lemma transport_embed {a b : A} (h : star a * a = star b * b) (x : A) :
    transport a b (embed a x) = b * x := by
  exact LinearMap.extendOfNorm_eq (dense a)
    ⟨1, fun x => by change ‖b * x‖ ≤ 1 * ‖a * x‖; simpa only [one_mul] using (norm_mul_eq h x).ge⟩ x


-- @@ L250-261 verbatim
lemma transport_inner {a b : A} (h : star a * a = star b * b)
    (x y : space a) : star (transport a b x) * transport a b y = star (x : A) * y := by
  refine (dense a).induction_on₂ (p := fun x y =>
    star (transport a b x) * transport a b y = star (x : A) * y)
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_ x y
  intro x y
  rw [transport_embed h, transport_embed h]
  simp only [embed_val, star_mul]
  calc
    _ = star x * (star b * b) * y := by noncomm_ring
    _ = star x * (star a * a) * y := by rw [h]
    _ = _ := by noncomm_ring


-- @@ L263-268 verbatim
lemma transport_mem {a b : A} (h : star a * a = star b * b) (x : space a) :
    transport a b x ∈ space b := by
  refine (dense a).induction_on x ((closed b).preimage (by fun_prop)) ?_
  intro y
  rw [transport_embed h]
  exact mem_space b y


-- @@ L270-277 verbatim
lemma mul_right_mem {a z : A} (hz : z ∈ space a) (x : A) : z * x ∈ space a := by
  have hh (z : space a) : (z : A) * x ∈ space a := by
    refine (dense a).induction_on z ((closed a).preimage (by fun_prop)) ?_
    intro y
    change (a * y) * x ∈ space a
    rw [mul_assoc]
    exact mem_space a (y*x)
  exact hh ⟨z, hz⟩


-- @@ L279-282 verbatim
lemma space_le {a b : A} (ha : a ∈ space b) : space a ≤ space b := by
  apply Submodule.topologicalClosure_minimal _ ?_ (closed b)
  rintro z ⟨x, rfl⟩
  exact mul_right_mem ha x


-- @@ L284-284 verbatim
lemma space_mul_le (a b : A) : space (a*b) ≤ space a := space_le (mem_space a b)



-- @@ L287-287 verbatim
def hereditary (b : A) : Set A := closure (Set.range (fun x : A => b * x * b))


-- @@ L289-299 verbatim
lemma self_mul_star_mem_hereditary {b z : A} (hb : IsSelfAdjoint b) (hz : z ∈ space b) :
    z * star z ∈ hereditary b := by
  have hh (z : space b) : (z : A) * star (z : A) ∈ hereditary b := by
    refine (dense b).induction_on z (isClosed_closure.preimage (by fun_prop)) ?_
    intro x
    apply subset_closure
    refine ⟨x * star x, ?_⟩
    change b * (x * star x) * b = b * x * star (b*x)
    rw [star_mul, hb.star_eq]
    noncomm_ring
  exact hh ⟨z, hz⟩


-- @@ L301-301 verbatim
end ClosedRightRange

-- @@ L302-302 verbatim
end KirchbergRordam.GenericRW

-- @@ L303-303 verbatim
namespace KirchbergRordam.GenericRW.HereditaryTransport

-- @@ L304-304 verbatim
open ClosedRightRange

-- @@ L305-305 verbatim
variable {A : Type*} [CStarAlgebra A]



-- @@ L308-314 verbatim
def raw (a : A) (ha : IsSelfAdjoint a) : NonUnitalStarSubalgebra ℂ A where
  carrier := Set.range (fun x : A => a*x*a)
  zero_mem' := ⟨0,by simp⟩
  add_mem' := by rintro _ _ ⟨x,rfl⟩ ⟨y,rfl⟩; exact ⟨x+y,by noncomm_ring⟩
  mul_mem' := by rintro _ _ ⟨x,rfl⟩ ⟨y,rfl⟩; exact ⟨x*a*a*y,by noncomm_ring⟩
  smul_mem' := by rintro c _ ⟨x,rfl⟩; exact ⟨c • x,by simp only [mul_smul_comm,smul_mul_assoc]⟩
  star_mem' := by rintro _ ⟨x,rfl⟩; exact ⟨star x,by simp only [star_mul,ha.star_eq]; noncomm_ring⟩


-- @@ L316-316 verbatim
abbrev corner (a : A) (ha : IsSelfAdjoint a) := (raw a ha).topologicalClosure


-- @@ L318-318 verbatim
instance cornerClosed (a : A) (ha : IsSelfAdjoint a) : IsClosed (corner a ha : Set A) := isClosed_closure


-- @@ L320-320 verbatim
instance (a : A) (ha : IsSelfAdjoint a) : NonUnitalCStarAlgebra (corner a ha) := inferInstance


-- @@ L322-328 verbatim
omit instSize in
lemma mem_corner.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    (a : A) (ha : IsSelfAdjoint a) (x : A) : a*x*a ∈ corner a ha :=
  subset_closure ⟨x,rfl⟩


-- @@ L330-335 verbatim
omit instSize in
lemma corner_eq.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    (a : A) (ha : IsSelfAdjoint a) : (corner a ha : Set A)=hereditary a := rfl


-- @@ L337-342 verbatim
lemma in_space {a : A} {ha : IsSelfAdjoint a} {x : A} (hx : x ∈ corner a ha) : x ∈ space a := by
  apply closure_minimal (s := Set.range (fun y : A => a*y*a)) ?_ (closed a) hx
  rintro _ ⟨y,rfl⟩
  change a*y*a ∈ space a
  rw [mul_assoc]
  exact mem_space a (y*a)


-- @@ L344-344 verbatim
def embed (a : A) (ha : IsSelfAdjoint a) (x : A) : corner a ha := ⟨a*x*a,mem_corner a ha x⟩


-- @@ L346-359 verbatim
lemma dense (a : A) (ha : IsSelfAdjoint a) : DenseRange (embed a ha) := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro x
  rw [closure_subtype]
  change (x : A) ∈ closure (Subtype.val '' Set.range (embed a ha))
  have h : Subtype.val '' Set.range (embed a ha) = Set.range (fun z : A => a*z*a) := by
    ext y
    simp only [Set.mem_image,Set.mem_range]
    constructor
    · rintro ⟨_,⟨z,rfl⟩,rfl⟩; exact ⟨z,rfl⟩
    · rintro ⟨z,rfl⟩; exact ⟨embed a ha z,⟨z,rfl⟩,rfl⟩
  rw [h]
  exact x.property


-- @@ L361-361 verbatim
variable {a v : A} (ha : IsSelfAdjoint a) (hv : star a*a=star v*v)



-- @@ L364-364 verbatim
def left (x : corner a ha) : A := transport a v ⟨x,in_space x.property⟩


-- @@ L366-367 verbatim
lemma continuous_left : Continuous (left (v := v) ha) := by
  exact (transport a v).continuous.comp (continuous_subtype_val.subtype_mk _)


-- @@ L369-369 verbatim
include hv


-- @@ L371-375 verbatim
lemma left_embed (x : A) : left (v := v) ha (embed a ha x)=v*x*a := by
  unfold left
  have he : (⟨(embed a ha x : A),in_space (embed a ha x).property⟩ : space a) =
      ClosedRightRange.embed a (x*a) := Subtype.ext (mul_assoc a x a)
  rw [he,transport_embed hv,mul_assoc]


-- @@ L377-381 verbatim
lemma star_left_mem (x : corner a ha) : star (left (v := v) ha x) ∈ space a := by
  refine (dense a ha).induction_on x ((closed a).preimage (continuous_left ha).star) ?_
  intro y
  rw [left_embed ha hv,star_mul,ha.star_eq]
  exact mem_space a (star (v*y))



-- @@ L384-385 verbatim
def conjugate (x : corner a ha) : A :=
  star (transport a v ⟨star (left (v := v) ha x),star_left_mem ha hv x⟩)


-- @@ L387-389 verbatim
lemma continuous_conjugate : Continuous (conjugate ha hv) := by
  exact ((transport a v).continuous.comp
    ((continuous_left ha).star.subtype_mk _)).star


-- @@ L391-398 verbatim
lemma conjugate_embed (x : A) : conjugate ha hv (embed a ha x)=v*x*star v := by
  unfold conjugate
  have he : star (left (v := v) ha (embed a ha x))=a*(star x*star v) := by
    rw [left_embed ha hv,star_mul,star_mul,ha.star_eq]
  change star (transport a v ⟨_,_⟩)=_
  rw [show (⟨star (left (v := v) ha (embed a ha x)),_⟩ : space a)=
    ClosedRightRange.embed a (star x*star v) from Subtype.ext he]
  rw [transport_embed hv,star_mul,star_mul,star_star,star_star]


-- @@ L400-408 verbatim
lemma conjugate_add (x y : corner a ha) : conjugate ha hv (x+y)=conjugate ha hv x+conjugate ha hv y := by
  refine (dense a ha).induction_on₂
    (isClosed_eq ((continuous_conjugate ha hv).comp (continuous_fst.add continuous_snd))
      (((continuous_conjugate ha hv).comp continuous_fst).add
        ((continuous_conjugate ha hv).comp continuous_snd))) ?_ x y
  intro x y
  have he : embed a ha x+embed a ha y=embed a ha (x+y) := by ext; change a*x*a+a*y*a=a*(x+y)*a; noncomm_ring
  rw [he,conjugate_embed,conjugate_embed,conjugate_embed]
  noncomm_ring


-- @@ L410-412 verbatim
lemma conjugate_zero : conjugate ha hv 0=0 := by
  have hz : embed a ha (0 : A)=0 := by ext; simp [embed]
  rw [← hz,conjugate_embed]; simp


-- @@ L414-422 verbatim
lemma conjugate_smul (c : ℂ) (x : corner a ha) : conjugate ha hv (c • x)=c • conjugate ha hv x := by
  refine (dense a ha).induction_on x (isClosed_eq
    ((continuous_conjugate ha hv).comp (continuous_const_smul c))
    ((continuous_conjugate ha hv).const_smul c)) ?_
  intro x
  have he : c • embed a ha x=embed a ha (c • x) := by
    ext; change c • (a*x*a)=a*(c • x)*a; simp only [mul_smul_comm,smul_mul_assoc]
  rw [he,conjugate_embed,conjugate_embed]
  simp only [mul_smul_comm,smul_mul_assoc]


-- @@ L424-435 verbatim
lemma conjugate_mul (x y : corner a ha) : conjugate ha hv (x*y)=conjugate ha hv x*conjugate ha hv y := by
  refine (dense a ha).induction_on₂
    (isClosed_eq ((continuous_conjugate ha hv).comp (continuous_fst.mul continuous_snd))
      (((continuous_conjugate ha hv).comp continuous_fst).mul
        ((continuous_conjugate ha hv).comp continuous_snd))) ?_ x y
  intro x y
  have he : embed a ha x*embed a ha y=embed a ha (x*a*a*y) := by ext; change (a*x*a)*(a*y*a)=a*(x*a*a*y)*a; noncomm_ring
  rw [he,conjugate_embed,conjugate_embed,conjugate_embed]
  calc
    _=v*x*(star a*a)*y*star v := by rw [ha.star_eq]; noncomm_ring
    _=v*x*(star v*v)*y*star v := by rw [hv]
    _=_ := by noncomm_ring


-- @@ L437-444 verbatim
lemma conjugate_star (x : corner a ha) : conjugate ha hv (star x)=star (conjugate ha hv x) := by
  refine (dense a ha).induction_on x (isClosed_eq
    ((continuous_conjugate ha hv).comp continuous_star) (continuous_conjugate ha hv).star) ?_
  intro x
  have he : star (embed a ha x)=embed a ha (star x) := by
    ext; change star (a*x*a)=a*star x*a; rw [star_mul,star_mul,ha.star_eq]; noncomm_ring
  rw [he,conjugate_embed,conjugate_embed,star_mul,star_mul,star_star]
  noncomm_ring



-- @@ L447-453 verbatim
def hom : corner a ha →⋆ₙₐ[ℂ] A where
  toFun := conjugate ha hv
  map_zero' := conjugate_zero ha hv
  map_add' := conjugate_add ha hv
  map_mul' := conjugate_mul ha hv
  map_smul' := conjugate_smul ha hv
  map_star' := conjugate_star ha hv


-- @@ L455-456 verbatim
lemma left_inner (x y : corner a ha) : star (left (v := v) ha x)*left (v := v) ha y=star (x : A)*(y : A) :=
  transport_inner hv _ _


-- @@ L458-468 verbatim
lemma hom_inner (x y : corner a ha) : hom ha hv (x*star y)=left (v := v) ha x*star (left (v := v) ha y) := by
  refine (dense a ha).induction_on₂ (isClosed_eq
    ((continuous_conjugate ha hv).comp (continuous_fst.mul continuous_snd.star))
    (((continuous_left ha).comp continuous_fst).mul
      ((continuous_left ha).comp continuous_snd).star)) ?_ x y
  intro x y
  have he : embed a ha x*star (embed a ha y)=embed a ha (x*a*a*star y) := by
    ext; change (a*x*a)*star (a*y*a)=a*(x*a*a*star y)*a; rw [star_mul,star_mul,ha.star_eq]; noncomm_ring
  change conjugate ha hv _=_
  rw [he,conjugate_embed,left_embed ha hv,left_embed ha hv,star_mul,star_mul,ha.star_eq]
  noncomm_ring


-- @@ L470-470 verbatim
end KirchbergRordam.GenericRW.HereditaryTransport


-- @@ L472-472 verbatim
namespace KirchbergRordam.GenericRW

-- @@ L473-473 verbatim
namespace Vanish

-- @@ L474-474 verbatim
variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X]



-- @@ L477-483 verbatim
def algebra (S : Set X) : NonUnitalStarSubalgebra ℂ C(X,ℂ) where
  carrier := {f | ∀ t ∈ S, f t = 0}
  zero_mem' := by simp
  add_mem' := by intro f g hf hg t ht; simp [hf t ht,hg t ht]
  mul_mem' := by intro f g hf hg t ht; simp [hf t ht,hg t ht]
  smul_mem' := by intro z f hf t ht; simp [hf t ht]
  star_mem' := by intro f hf t ht; simp [hf t ht]


-- @@ L485-489 verbatim
instance closed (S : Set X) : IsClosed ((algebra S : NonUnitalStarSubalgebra ℂ C(X,ℂ)) : Set C(X,ℂ)) := by
  change IsClosed {f : C(X,ℂ) | ∀ t ∈ S, f t = 0}
  convert (isClosed_biInter fun (t : X) (_ : t ∈ S) =>
    isClosed_eq (continuous_eval_const t : Continuous (fun f : C(X,ℂ) => f t)) (continuous_const (y := (0:ℂ)))) using 1
  ext f; simp


-- @@ L491-491 verbatim
abbrev Functions (S : Set X) := algebra S


-- @@ L493-493 verbatim
instance (S : Set X) : NonUnitalCStarAlgebra (Functions S) := inferInstance



-- @@ L496-499 verbatim
def multiplier (p : C(X,ℂ)) : C(X,ℂ) →ₗ[ℂ] Functions {t | p t = 0} where
  toFun f := ⟨p*f, by intro t ht; simp [show p t=0 from ht]⟩
  map_add' f g := by ext t; simp [mul_add]
  map_smul' z f := by ext t; simp


-- @@ L501-507 verbatim
omit [CompactSpace X] [T2Space X] in
omit instSize in
@[simp] lemma multiplier_apply.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {X : Type contextLevel1}
    [TopologicalSpace X]
    (p f : C(X,ℂ)) (t : X) : (multiplier p f : C(X,ℂ)) t = p t*f t := rfl



-- @@ L510-543 verbatim
omit instSize in
lemma multiplier_dense.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    {X : Type contextLevel1}
    [TopologicalSpace X]
    [CompactSpace X]
    [T2Space X]
    (p : C(X,ℂ)) : DenseRange (multiplier p) := by
  let I : Ideal C(X,ℂ) := Ideal.span {p}
  have hs : ContinuousMap.setOfIdeal I = {t | p t = 0}ᶜ := by
    ext t
    rw [ContinuousMap.mem_setOfIdeal]
    constructor
    · rintro ⟨f,hf,hne⟩ ht
      obtain ⟨g,rfl⟩ := Ideal.mem_span_singleton'.mp hf
      apply hne
      simp [show p t=0 from ht]
    · intro ht
      exact ⟨p,Ideal.subset_span rfl,ht⟩
  have hi : (fun f : Functions {t | p t=0} => (f : C(X,ℂ))) '' Set.range (multiplier p) = I := by
    ext f
    constructor
    · rintro ⟨g,⟨v,rfl⟩,rfl⟩
      exact Ideal.mul_mem_right _ I (Ideal.subset_span rfl)
    · intro hf
      obtain ⟨g,hg⟩ := Ideal.mem_span_singleton'.mp hf
      refine ⟨multiplier p g,⟨g,rfl⟩,?_⟩
      change p*g=f
      rw [mul_comm,hg]
  apply (isUniformEmbedding_subtype_val.isEmbedding.isInducing.dense_iff).mpr
  intro f
  rw [hi,← Ideal.coe_closure,← ContinuousMap.idealOfSet_ofIdeal_eq_closure,hs]
  intro t ht
  exact f.property t (by simpa only [compl_compl] using ht)


-- @@ L545-545 verbatim
end Vanish

-- @@ L546-546 verbatim
end KirchbergRordam.GenericRW

-- @@ L547-547 verbatim
end


-- @@ L549-549 verbatim
end OAI
