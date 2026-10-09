import OAI.RingTheory.Tachikawa.CompleteTensor


-- @@ L3-3 verbatim
namespace OAI



-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
namespace Tachikawa.VectorSplit

-- @@ L8-8 verbatim
open CategoryTheory

-- @@ L9-9 verbatim
variable {k : Type*} [Field k] {I : Type*} {c : ComplexShape I}

-- @@ L10-10 verbatim
variable (K : HomologicalComplex (ModuleCat k) c)


-- @@ L12-12 verbatim
abbrev Z (i : I) := LinearMap.ker (K.d i (c.next i)).hom


-- @@ L14-14 verbatim
def inc (i : I) : Z K i →ₗ[k] K.X i := (Z K i).subtype


-- @@ L16-17 verbatim
def retract (i : I) : K.X i →ₗ[k] Z K i :=
  ((inc K i).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr Subtype.val_injective)).choose


-- @@ L19-20 verbatim
lemma retract_inc (i : I) : (retract K i).comp (inc K i) = LinearMap.id :=
  ((inc K i).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr Subtype.val_injective)).choose_spec


-- @@ L22-23 verbatim
@[simp] lemma retract_cycle (i : I) (z : Z K i) : retract K i z = z :=
  LinearMap.congr_fun (retract_inc K i) z


-- @@ L25-31 verbatim
lemma cycle_d (i j : I) (z : Z K i) : K.d i j z = 0 := by
  by_cases h : c.Rel i j
  · have hj : c.next i = j := c.next_eq' h
    subst j
    exact z.property
  · rw [K.shape i j h]
    rfl


-- @@ L33-37 verbatim
def boundary (i : I) : K.X (c.prev i) →ₗ[k] Z K i :=
  (K.d (c.prev i) i).hom.codRestrict _ (fun x => by
    change K.d i (c.next i) (K.d (c.prev i) i x) = 0
    exact congrArg (fun f : K.X (c.prev i) ⟶ K.X (c.next i) => f x)
      (K.d_comp_d (c.prev i) i (c.next i)))


-- @@ L39-41 verbatim
@[simp] lemma boundary_cycle (i : I) (z : Z K (c.prev i)) : boundary K i z = 0 := by
  apply Subtype.ext
  exact cycle_d K (c.prev i) i z


-- @@ L43-43 verbatim
abbrev H (i : I) := Z K i ⧸ LinearMap.range (boundary K i)


-- @@ L45-45 verbatim
def quotient (i : I) : Z K i →ₗ[k] H K i := (LinearMap.range (boundary K i)).mkQ


-- @@ L47-49 verbatim
def representatives (i : I) : H K i →ₗ[k] Z K i :=
  ((quotient K i).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _))).choose


-- @@ L51-54 verbatim
lemma quotient_representatives (i : I) :
    (quotient K i).comp (representatives K i) = LinearMap.id :=
  ((quotient K i).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _))).choose_spec


-- @@ L56-58 verbatim
@[simp] lemma quotient_representatives_apply (i : I) (x : H K i) :
    quotient K i (representatives K i x) = x :=
  LinearMap.congr_fun (quotient_representatives K i) x


-- @@ L60-62 verbatim
@[simp] lemma quotient_boundary (i : I) (x : K.X (c.prev i)) :
    quotient K i (boundary K i x) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).2 ⟨x,rfl⟩


-- @@ L64-68 verbatim
def boundaryPart (i : I) : Z K i →ₗ[k] LinearMap.range (boundary K i) :=
  (LinearMap.id - (representatives K i).comp (quotient K i)).codRestrict _ (fun z => by
    apply (Submodule.Quotient.mk_eq_zero _).1
    change quotient K i (z - representatives K i (quotient K i z)) = 0
    rw [map_sub, quotient_representatives_apply, sub_self])


-- @@ L70-72 verbatim
def rawLift (i : I) : LinearMap.range (boundary K i) →ₗ[k] K.X (c.prev i) :=
  ((boundary K i).rangeRestrict.exists_rightInverse_of_surjective
    (boundary K i).range_rangeRestrict).choose


-- @@ L74-79 verbatim
lemma boundary_rawLift (i : I) (z : LinearMap.range (boundary K i)) :
    boundary K i (rawLift K i z) = z := by
  have h := LinearMap.congr_fun
    (((boundary K i).rangeRestrict.exists_rightInverse_of_surjective
      (boundary K i).range_rangeRestrict).choose_spec) z
  exact congrArg Subtype.val h


-- @@ L81-82 verbatim
def lift (i : I) : LinearMap.range (boundary K i) →ₗ[k] K.X (c.prev i) :=
  (LinearMap.id - (inc K (c.prev i)).comp (retract K (c.prev i))).comp (rawLift K i)


-- @@ L84-88 verbatim
lemma boundary_lift (i : I) (z : LinearMap.range (boundary K i)) :
    boundary K i (lift K i z) = z := by
  change boundary K i (rawLift K i z - inc K (c.prev i) (retract K (c.prev i) (rawLift K i z))) = z
  change boundary K i (rawLift K i z - (retract K (c.prev i) (rawLift K i z) : K.X (c.prev i))) = z
  rw [map_sub, boundary_cycle, sub_zero, boundary_rawLift]


-- @@ L90-94 verbatim
lemma retract_lift (i : I) (z : LinearMap.range (boundary K i)) :
    retract K (c.prev i) (lift K i z) = 0 := by
  change retract K (c.prev i) (rawLift K i z - inc K (c.prev i) (retract K (c.prev i) (rawLift K i z))) = 0
  change retract K (c.prev i) (rawLift K i z - (retract K (c.prev i) (rawLift K i z) : K.X (c.prev i))) = 0
  rw [map_sub, retract_cycle, sub_self]


-- @@ L96-97 verbatim
def complement (i : I) : K.X i →ₗ[k] K.X i :=
  LinearMap.id - (inc K i).comp (retract K i)


-- @@ L99-102 verbatim
lemma complement_cycle (i : I) (z : Z K i) : complement K i z = 0 := by
  change (z : K.X i) - inc K i (retract K i z) = 0
  rw [retract_cycle]
  exact sub_self _


-- @@ L104-114 verbatim
lemma complement_eq_lift (i : I) (hi : c.Rel (c.prev i) i) (x : K.X (c.prev i)) :
    complement K (c.prev i) x = lift K i ((boundary K i).rangeRestrict x) := by
  have hz : x - rawLift K i ((boundary K i).rangeRestrict x) ∈ Z K (c.prev i) := by
    change K.d (c.prev i) (c.next (c.prev i)) (x - rawLift K i ((boundary K i).rangeRestrict x)) = 0
    rw [c.next_eq' hi, map_sub]
    have h := congrArg Subtype.val (boundary_rawLift K i ((boundary K i).rangeRestrict x))
    exact sub_eq_zero.mpr h.symm
  have h := complement_cycle K (c.prev i) ⟨_,hz⟩
  change complement K (c.prev i) (x - rawLift K i ((boundary K i).rangeRestrict x)) = 0 at h
  rw [map_sub, sub_eq_zero] at h
  exact h


-- @@ L116-117 verbatim
def homotopyComponent (i : I) : K.X i →ₗ[k] K.X (c.prev i) :=
  (lift K i).comp ((boundaryPart K i).comp (retract K i))


-- @@ L119-122 verbatim
lemma homotopy_d (i : I) (x : K.X i) :
    K.d (c.prev i) i (homotopyComponent K i x) =
      inc K i (retract K i x) - inc K i (representatives K i (quotient K i (retract K i x))) := by
  exact congrArg Subtype.val (boundary_lift K i (boundaryPart K i (retract K i x)))


-- @@ L124-134 verbatim
lemma homotopy_boundary (i : I) (hi : c.Rel (c.prev i) i) (x : K.X (c.prev i)) :
    homotopyComponent K i (K.d (c.prev i) i x) = complement K (c.prev i) x := by
  change lift K i (boundaryPart K i (retract K i (boundary K i x))) = _
  rw [retract_cycle]
  have h : boundaryPart K i (boundary K i x) = (boundary K i).rangeRestrict x := by
    apply Subtype.ext
    change boundary K i x - representatives K i (quotient K i (boundary K i x)) = _
    rw [quotient_boundary, map_zero, sub_zero]
    rfl
  rw [h]
  exact (complement_eq_lift K i hi x).symm


-- @@ L136-136 verbatim
end Tachikawa.VectorSplit




-- @@ L140-140 verbatim
namespace Tachikawa

-- @@ L141-141 verbatim
open CategoryTheory

-- @@ L142-142 verbatim
open scoped ModuleCat.Algebra

-- @@ L143-143 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R]

-- @@ L144-144 verbatim
variable (P : ChainComplex (ModuleCat R) ℤ) (N : ModuleCat R)


-- @@ L146-147 verbatim
def completeHom : CochainComplex (ModuleCat k) ℤ :=
  (((linearYoneda k (ModuleCat R)).obj N).mapHomologicalComplex (.up ℤ)).obj P.op


-- @@ L149-150 verbatim
@[simp] lemma completeHom_d (i j : ℤ) (f : P.X i ⟶ N) :
    (completeHom (k := k) P N).d i j f = P.d j i ≫ f := rfl


-- @@ L152-156 verbatim
lemma completeHom_memZ (j : ℤ) (f : P.X j ⟶ N) :
    f ∈ VectorSplit.Z (completeHom (k := k) P N) j ↔ P.d (j+1) j ≫ f = 0 := by
  change (completeHom (k := k) P N).d j ((ComplexShape.up ℤ).next j) f = 0 ↔ _
  rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel j (j+1) from rfl)]
  rfl


-- @@ L158-158 verbatim
namespace CompleteHom


-- @@ L160-178 verbatim
def cokerCycles (j : ℤ) : (CokerAt P j →ₗ[R] N) ≃ₗ[k]
    VectorSplit.Z (completeHom (k := k) P N) j where
  toFun f := ⟨ModuleCat.ofHom (f.comp (CokerAt.π P j)), by
    apply (completeHom_memZ P N j _).mpr
    apply ModuleCat.hom_ext
    change (f.comp (CokerAt.π P j)).comp (P.d (j+1) j).hom = 0
    rw [LinearMap.comp_assoc,CokerAt.π_d,LinearMap.comp_zero]⟩
  invFun z := CokerAt.descend P j z.val.hom (ModuleCat.hom_ext_iff.mp
    ((completeHom_memZ P N j z.val).mp z.property))
  left_inv f := by
    ext x
    obtain ⟨y,rfl⟩ := CokerAt.π_surjective P j x
    rfl
  right_inv z := by
    apply Subtype.ext
    apply ModuleCat.hom_ext
    rfl
  map_add' f g := rfl
  map_smul' r f := rfl


-- @@ L180-181 verbatim
variable (hP : TotallyAcyclic P) (fin : ∀ j, Module.Finite R (P.X j))
  (proj : ∀ j, Module.Projective R (P.X j))


-- @@ L183-201 verbatim
include hP fin proj in
lemma boundary_iff (j : ℤ) (z : VectorSplit.Z (completeHom (k := k) P N) j) :
    z ∈ LinearMap.range (VectorSplit.boundary (completeHom (k := k) P N) j) ↔
      (cokerCycles P N j).symm z ∈ projectiveFactors (k := k) := by
  change _ ↔ CokerAt.descend P j z.val.hom (ModuleCat.hom_ext_iff.mp
    ((completeHom_memZ P N j z.val).mp z.property)) ∈ projectiveFactors (k := k)
  refine Iff.trans ?_ (hP.factors_iff_boundary (k := k) fin proj j z.val.hom
    (ModuleCat.hom_ext_iff.mp ((completeHom_memZ P N j z.val).mp z.property))).symm
  change (∃ g : P.X ((ComplexShape.up ℤ).prev j) ⟶ N,
    VectorSplit.boundary (completeHom (k := k) P N) j g = z) ↔ _
  simp only [← Subtype.val_inj]
  change (∃ g : P.X ((ComplexShape.up ℤ).prev j) ⟶ N,
    P.d j ((ComplexShape.up ℤ).prev j) ≫ g = z.val) ↔ _
  rw [(ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (j-1) j by change (j-1)+1=j; omega)]
  constructor
  · rintro ⟨g,hg⟩
    exact ⟨g.hom,ModuleCat.hom_ext_iff.mp hg⟩
  · rintro ⟨g,hg⟩
    exact ⟨ModuleCat.ofHom g,ModuleCat.hom_ext hg⟩


-- @@ L203-213 verbatim
def equiv (j : ℤ) : VectorSplit.H (completeHom (k := k) P N) j ≃ₗ[k]
    StableHom (k := k) (R := R) (M := CokerAt P j) (N := N) := by
  apply Submodule.Quotient.equiv _ _ (cokerCycles P N j).symm
  ext f
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact (boundary_iff P N hP fin proj j z).mp hz
  · intro hf
    refine ⟨(cokerCycles P N j) f,?_,by simp⟩
    apply (boundary_iff P N hP fin proj j _).mpr
    simpa using hf


-- @@ L215-215 verbatim
end CompleteHom

-- @@ L216-216 verbatim
end Tachikawa




-- @@ L220-220 verbatim
namespace Tachikawa

-- @@ L221-225 verbatim
variable {k R M N P Q : Type} [Field k] [Ring R] [Algebra k R]
 [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
 [Module R M] [Module R N] [Module R P] [Module R Q]
 [Module k N] [Module k Q]
 [IsScalarTower k R N] [IsScalarTower k R Q]


-- @@ L227-235 verbatim
lemma linear_descent (ε : P →ₗ[R] M) (hε : Function.Surjective ε) (f : P →ₗ[R] Q)
    (h : LinearMap.ker ε ≤ LinearMap.ker f) : ∃ g : M →ₗ[R] Q, g.comp ε = f := by
  refine ⟨((LinearMap.ker ε).liftQ f h).comp (ε.quotKerEquivOfSurjective hε).symm.toLinearMap, ?_⟩
  apply LinearMap.ext
  intro x
  change (LinearMap.ker ε).liftQ f h ((ε.quotKerEquivOfSurjective hε).symm (ε x)) = f x
  have hx : ε x = (ε.quotKerEquivOfSurjective hε) ((LinearMap.ker ε).mkQ x) := rfl
  rw [hx,LinearEquiv.symm_apply_apply]
  rfl


-- @@ L237-237 verbatim
namespace StableShift

-- @@ L238-239 verbatim
variable (ε : P →ₗ[R] M) (δ : Q →ₗ[R] N) (hδ : Function.Surjective δ)
 [Module.Projective R P]


-- @@ L241-244 verbatim
include hδ in
lemma hom_lift_surjective : Function.Surjective (homPostcompose (k := k) (M := P) δ) := by
  intro f
  exact Module.projective_lifting_property δ f hδ


-- @@ L246-248 verbatim
def liftLinear : (M →ₗ[R] N) →ₗ[k] (P →ₗ[R] Q) :=
  (Classical.choose ((homPostcompose (k := k) (M := P) δ).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (hom_lift_surjective (k := k) δ hδ)))).comp (homPrecompose ε)


-- @@ L250-253 verbatim
lemma liftLinear_lifts (f : M →ₗ[R] N) : δ.comp (liftLinear (k := k) ε δ hδ f) = f.comp ε := by
  exact LinearMap.congr_fun (Classical.choose_spec
    ((homPostcompose (k := k) (M := P) δ).exists_rightInverse_of_surjective
      (LinearMap.range_eq_top.mpr (hom_lift_surjective (k := k) δ hδ)))) (f.comp ε)


-- @@ L255-272 verbatim
def kernelMap : (M →ₗ[R] N) →ₗ[k] (LinearMap.ker ε →ₗ[R] LinearMap.ker δ) where
  toFun f := LinearMap.codRestrict (LinearMap.ker δ) ((liftLinear (k := k) ε δ hδ f).domRestrict (LinearMap.ker ε)) (by
    intro x
    change δ (liftLinear (k := k) ε δ hδ f x) = 0
    have hh := LinearMap.congr_fun (liftLinear_lifts (k := k) ε δ hδ f) x
    change δ (liftLinear (k := k) ε δ hδ f x) = f (ε x) at hh
    rw [show ε x = 0 from x.property, map_zero] at hh
    exact hh)
  map_add' f g := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (map_add (liftLinear (k := k) ε δ hδ) f g) x
  map_smul' c f := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    exact LinearMap.congr_fun (map_smul (liftLinear (k := k) ε δ hδ) c f) x


-- @@ L274-274 verbatim
variable [Module.Finite R P]


-- @@ L276-297 verbatim
lemma kernelMap_class (f : M →ₗ[R] N) (g : LinearMap.ker ε →ₗ[R] LinearMap.ker δ)
    (h : P →ₗ[R] Q) (hh : δ.comp h = f.comp ε)
    (hg : h.comp (LinearMap.ker ε).subtype = (LinearMap.ker δ).subtype.comp g) :
    stableClass (k := k) (kernelMap (k := k) ε δ hδ f) = stableClass (k := k) g := by
  rw [← sub_eq_zero, ← map_sub, stableClass_eq_zero_iff]
  let t : P →ₗ[R] LinearMap.ker δ := LinearMap.codRestrict (LinearMap.ker δ)
    (liftLinear (k := k) ε δ hδ f - h) (by
      intro x
      change δ (liftLinear (k := k) ε δ hδ f x - h x) = 0
      rw [map_sub]
      have h₁ := LinearMap.congr_fun (liftLinear_lifts (k := k) ε δ hδ f) x
      have h₂ := LinearMap.congr_fun hh x
      dsimp only [LinearMap.comp_apply] at h₁ h₂
      rw [h₁,h₂,sub_self])
  refine ⟨ModuleCat.of R P, inferInstance, inferInstance, (LinearMap.ker ε).subtype, t, ?_⟩
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  have hx := LinearMap.congr_fun hg x
  change h x = (g x : Q) at hx
  change liftLinear (k := k) ε δ hδ f x - h x = liftLinear (k := k) ε δ hδ f x - (g x : Q)
  rw [hx]


-- @@ L299-299 verbatim
variable [Module.Finite R Q] [Module.Projective R Q]


-- @@ L301-311 verbatim
lemma kernelMap_factors (f : M →ₗ[R] N) (hf : f ∈ projectiveFactors (k := k)) :
    kernelMap (k := k) ε δ hδ f ∈ projectiveFactors (k := k) := by
  obtain ⟨s,hs⟩ := (factors_iff_lifts δ hδ f).mp hf
  have hc := kernelMap_class (k := k) ε δ hδ f 0 (s.comp ε)
    (by rw [← LinearMap.comp_assoc,hs]) (by
      apply LinearMap.ext
      intro x
      change s (ε x) = 0
      rw [x.property,map_zero])
  apply (stableClass_eq_zero_iff _).mp
  simpa only [map_zero] using hc


-- @@ L313-316 verbatim
def map : StableHom (k := k) (R := R) (M := M) (N := N) →ₗ[k]
    StableHom (k := k) (R := R) (M := LinearMap.ker ε) (N := LinearMap.ker δ) :=
  (projectiveFactors (k := k)).mapQ (projectiveFactors (k := k))
    (kernelMap (k := k) ε δ hδ) (kernelMap_factors (k := k) ε δ hδ)


-- @@ L318-320 verbatim
@[simp] lemma map_class (f : M →ₗ[R] N) :
    map (k := k) ε δ hδ (stableClass (k := k) f) =
      stableClass (k := k) (kernelMap (k := k) ε δ hδ f) := rfl


-- @@ L322-322 verbatim
variable [Module.Injective R R] (hε : Function.Surjective ε)


-- @@ L324-347 verbatim
include hε in
lemma kernelMap_reflects_factors (f : M →ₗ[R] N)
    (hf : kernelMap (k := k) ε δ hδ f ∈ projectiveFactors (k := k)) :
    f ∈ projectiveFactors (k := k) := by
  obtain ⟨v,hv⟩ := (factors_iff_extends (k := k) (LinearMap.ker ε).subtype Subtype.val_injective _).mp hf
  let d := liftLinear (k := k) ε δ hδ f - (LinearMap.ker δ).subtype.comp v
  have hd : LinearMap.ker ε ≤ LinearMap.ker d := by
    intro x hx
    have hh := congrArg Subtype.val (LinearMap.congr_fun hv ⟨x,hx⟩)
    change (v x : Q) = liftLinear (k := k) ε δ hδ f x at hh
    change liftLinear (k := k) ε δ hδ f x - (v x : Q) = 0
    rw [hh,sub_self]
  obtain ⟨s,hs⟩ := linear_descent ε hε d hd
  apply (factors_iff_lifts δ hδ f).mpr
  refine ⟨s, ?_⟩
  apply LinearMap.ext
  intro x
  obtain ⟨y,rfl⟩ := hε x
  have h₁ := LinearMap.congr_fun hs y
  have h₂ := LinearMap.congr_fun (liftLinear_lifts (k := k) ε δ hδ f) y
  change s (ε y) = liftLinear (k := k) ε δ hδ f y - (v y : Q) at h₁
  change δ (s (ε y)) = f (ε y)
  rw [h₁,map_sub,(v y).property,sub_zero]
  exact h₂


-- @@ L349-357 verbatim
include hε in
lemma map_injective : Function.Injective (map (k := k) ε δ hδ) := by
  apply (LinearMap.ker_eq_bot).mp
  apply eq_bot_iff.mpr
  intro x hx
  obtain ⟨f,rfl⟩ := stableClass_surjective x
  change stableClass (k := k) (kernelMap (k := k) ε δ hδ f) = 0 at hx
  exact (stableClass_eq_zero_iff _).mpr (kernelMap_reflects_factors (k := k) ε δ hδ hε f
    ((stableClass_eq_zero_iff _).mp hx))


-- @@ L359-375 verbatim
include hε in
lemma map_surjective : Function.Surjective (map (k := k) ε δ hδ) := by
  let : Module.Injective R Q := injective_of_finite_projective
  intro x
  obtain ⟨g,rfl⟩ := stableClass_surjective x
  obtain ⟨h,hh⟩ := Module.Injective.extension_property R Q (LinearMap.ker ε) P
    (LinearMap.ker ε).subtype Subtype.val_injective ((LinearMap.ker δ).subtype.comp g)
  have hd : LinearMap.ker ε ≤ LinearMap.ker (δ.comp h) := by
    intro x hx
    have h₁ := LinearMap.congr_fun hh ⟨x,hx⟩
    change h x = (g ⟨x,hx⟩ : Q) at h₁
    change δ (h x) = 0
    rw [h₁]
    exact (g ⟨x,hx⟩).property
  obtain ⟨f,hf⟩ := linear_descent ε hε (δ.comp h) hd
  refine ⟨stableClass (k := k) f, ?_⟩
  exact kernelMap_class (k := k) ε δ hδ f g h hf.symm hh


-- @@ L377-380 verbatim
def equiv : StableHom (k := k) (R := R) (M := M) (N := N) ≃ₗ[k]
    StableHom (k := k) (R := R) (M := LinearMap.ker ε) (N := LinearMap.ker δ) :=
  LinearEquiv.ofBijective (map (k := k) ε δ hδ)
    ⟨map_injective (k := k) ε δ hδ hε, map_surjective (k := k) ε δ hδ hε⟩


-- @@ L382-382 verbatim
end StableShift

-- @@ L383-383 verbatim
end Tachikawa




-- @@ L387-387 verbatim
namespace Tachikawa

-- @@ L388-388 verbatim
open CategoryTheory

-- @@ L389-389 verbatim
open scoped ModuleCat.Algebra

-- @@ L390-390 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R] [Module.Injective R R]

-- @@ L391-391 verbatim
variable {M N P Q M' N' : ModuleCat.{0} R}

-- @@ L392-393 verbatim
variable [Module.Finite R P] [Module.Projective R P]
  [Module.Finite R Q] [Module.Projective R Q]


-- @@ L395-454 verbatim
theorem exact_square_factors_iff
    (i : M →ₗ[R] P) (pi : P →ₗ[R] M') (hi : Function.Injective i)
    (hex : Function.Exact i pi) (hpi : Function.Surjective pi)
    (j : N →ₗ[R] Q) (delta : Q →ₗ[R] N') (hj : Function.Injective j)
    (hex' : Function.Exact j delta) (hdelta : Function.Surjective delta)
    (f : M →ₗ[R] N) (h : P →ₗ[R] Q) (g : M' →ₗ[R] N')
    (hu : h.comp i = j.comp f) (hl : delta.comp h = g.comp pi) :
    f ∈ projectiveFactors (k := k) ↔ g ∈ projectiveFactors (k := k) := by
  have hji : delta.comp j = 0 := by
    ext x
    exact (hex' (j x)).mpr ⟨x,rfl⟩
  have hpii : pi.comp i = 0 := by
    ext x
    exact (hex (i x)).mpr ⟨x,rfl⟩
  constructor
  · intro hf
    obtain ⟨d,hd⟩ := (factors_iff_extends (k := k) i hi f).mp hf
    have hz : LinearMap.ker pi ≤ LinearMap.ker (h - j.comp d) := by
      intro x hx
      obtain ⟨y,rfl⟩ := (hex x).mp hx
      change h (i y) - j (d (i y)) = 0
      have h1 := LinearMap.congr_fun hu y
      have h2 := LinearMap.congr_fun hd y
      change h (i y) = j (f y) at h1
      change d (i y) = f y at h2
      rw [h1,h2,sub_self]
    obtain ⟨s,hs⟩ := linear_descent pi hpi (h - j.comp d) hz
    apply (factors_iff_lifts (k := k) delta hdelta g).mpr
    refine ⟨s,?_⟩
    ext x
    obtain ⟨y,rfl⟩ := hpi x
    have h1 := LinearMap.congr_fun hs y
    have h2 := LinearMap.congr_fun hl y
    change s (pi y) = h y - j (d y) at h1
    change delta (h y) = g (pi y) at h2
    change delta (s (pi y)) = g (pi y)
    rw [h1,map_sub,show delta (j (d y)) = 0 from LinearMap.congr_fun hji (d y),sub_zero,h2]
  · intro hg
    obtain ⟨s,hs⟩ := (factors_iff_lifts (k := k) delta hdelta g).mp hg
    have hr (x : P) : (h - s.comp pi) x ∈ LinearMap.range j := by
      apply (hex' _).mp
      change delta (h x - s (pi x)) = 0
      rw [map_sub]
      have h1 := LinearMap.congr_fun hl x
      have h2 := LinearMap.congr_fun hs (pi x)
      change delta (h x) = g (pi x) at h1
      change delta (s (pi x)) = g (pi x) at h2
      rw [h1,h2,sub_self]
    let d := CokerAt.factorThrough j hj (h - s.comp pi) hr
    have hd := CokerAt.factorThrough_spec j hj (h - s.comp pi) hr
    apply (factors_iff_extends (k := k) i hi f).mpr
    refine ⟨d,?_⟩
    ext x
    apply hj
    have h1 := LinearMap.congr_fun hd (i x)
    have h2 := LinearMap.congr_fun hu x
    change j (d (i x)) = h (i x) - s (pi (i x)) at h1
    change h (i x) = j (f x) at h2
    change j (d (i x)) = j (f x)
    rw [h1,show pi (i x) = 0 from LinearMap.congr_fun hpii x,map_zero,sub_zero,h2]


-- @@ L456-476 verbatim
omit [Module.Finite R P] [Module.Projective R P] in

theorem exists_exact_square_down
    (i : M →ₗ[R] P) (pi : P →ₗ[R] M') (hi : Function.Injective i)
    (hex : Function.Exact i pi) (hpi : Function.Surjective pi)
    (j : N →ₗ[R] Q) (delta : Q →ₗ[R] N')
    (hex' : Function.Exact j delta) (f : M →ₗ[R] N) :
    ∃ (h : P →ₗ[R] Q) (g : M' →ₗ[R] N'),
      h.comp i = j.comp f ∧ delta.comp h = g.comp pi := by
  let : Module.Injective R Q := injective_of_finite_projective
  obtain ⟨h,hh⟩ := Module.Injective.extension_property R Q M P i hi (j.comp f)
  have hz : LinearMap.ker pi ≤ LinearMap.ker (delta.comp h) := by
    intro x hx
    obtain ⟨y,rfl⟩ := (hex x).mp hx
    have he := LinearMap.congr_fun hh y
    change h (i y) = j (f y) at he
    change delta (h (i y)) = 0
    rw [he]
    exact (hex' _).mpr ⟨f y,rfl⟩
  obtain ⟨g,hg⟩ := linear_descent pi hpi (delta.comp h) hz
  exact ⟨h,g,hh,hg.symm⟩

-- @@ L477-477 verbatim
end Tachikawa




-- @@ L481-481 verbatim
namespace Tachikawa.VectorSplit

-- @@ L482-482 verbatim
open CategoryTheory

-- @@ L483-484 verbatim
variable {k : Type*} [Field k] {I : Type*} {c : ComplexShape I}
  {K L M : HomologicalComplex (ModuleCat k) c}


-- @@ L486-492 verbatim
def cycleMap (f : K ⟶ L) (i : I) : Z K i →ₗ[k] Z L i :=
  ((f.f i).hom.comp (Z K i).subtype).codRestrict _ (fun x => by
    change L.d i (c.next i) (f.f i x) = 0
    have h := congrArg (fun z => z x) (f.comm i (c.next i))
    change L.d i (c.next i) (f.f i x) = f.f (c.next i) (K.d i (c.next i) x) at h
    rw [x.property,map_zero] at h
    exact h)


-- @@ L494-497 verbatim
lemma cycleMap_boundary (f : K ⟶ L) (i : I) (x : K.X (c.prev i)) :
    cycleMap f i (boundary K i x) = boundary L i (f.f (c.prev i) x) := by
  apply Subtype.ext
  exact (congrArg (fun z => z x) (f.comm (c.prev i) i)).symm


-- @@ L499-501 verbatim
def Hmap (f : K ⟶ L) (i : I) : H K i →ₗ[k] H L i :=
  (LinearMap.range (boundary K i)).mapQ (LinearMap.range (boundary L i)) (cycleMap f i)
    (by rintro _ ⟨x,rfl⟩; exact ⟨f.f (c.prev i) x,(cycleMap_boundary f i x).symm⟩)


-- @@ L503-504 verbatim
@[simp] lemma Hmap_quotient (f : K ⟶ L) (i : I) (z : Z K i) :
    Hmap f i (quotient K i z) = quotient L i (cycleMap f i z) := rfl


-- @@ L506-508 verbatim
lemma quotient_eq_zero_iff (i : I) (z : Z K i) :
    quotient K i z = 0 ↔ ∃ x, boundary K i x = z :=
  Submodule.Quotient.mk_eq_zero _


-- @@ L510-511 verbatim
lemma quotient_surjective (i : I) : Function.Surjective (quotient K i) :=
  Submodule.mkQ_surjective _


-- @@ L513-518 verbatim
@[simp] lemma Hmap_comp (f : K ⟶ L) (g : L ⟶ M) (i : I) :
    Hmap (f ≫ g) i = (Hmap g i).comp (Hmap f i) := by
  apply LinearMap.ext
  intro x
  obtain ⟨z,rfl⟩ := quotient_surjective i x
  rfl


-- @@ L520-524 verbatim
@[simp] lemma Hmap_id (i : I) : Hmap (𝟙 K) i = LinearMap.id := by
  apply LinearMap.ext
  intro x
  obtain ⟨z,rfl⟩ := quotient_surjective i x
  rfl


-- @@ L526-530 verbatim
@[simp] lemma Hmap_zero (i : I) : Hmap (0 : K ⟶ L) i = 0 := by
  apply LinearMap.ext
  intro x
  obtain ⟨z,rfl⟩ := quotient_surjective i x
  exact map_zero (quotient L i)


-- @@ L532-539 verbatim
@[simp] lemma Hmap_add (f g : K ⟶ L) (i : I) : Hmap (f+g) i = Hmap f i + Hmap g i := by
  apply LinearMap.ext
  intro x
  obtain ⟨z,rfl⟩ := quotient_surjective i x
  change quotient L i (cycleMap (f+g) i z) =
    quotient L i (cycleMap f i z) + quotient L i (cycleMap g i z)
  rw [← map_add]
  congr 1


-- @@ L541-547 verbatim
@[simp] lemma Hmap_smul (r : k) (f : K ⟶ L) (i : I) : Hmap (r • f) i = r • Hmap f i := by
  apply LinearMap.ext
  intro x
  obtain ⟨z,rfl⟩ := quotient_surjective i x
  change quotient L i (cycleMap (r • f) i z) = r • quotient L i (cycleMap f i z)
  rw [← map_smul]
  congr 1


-- @@ L549-549 verbatim
variable {K L M : CochainComplex (ModuleCat k) ℤ}


-- @@ L551-557 verbatim
lemma quotient_zero_iff_predecessor (i : ℤ) (z : Z K i) :
    quotient K i z = 0 ↔ ∃ x : K.X (i-1), K.d (i-1) i x = z.val := by
  rw [quotient_eq_zero_iff]
  simp only [← Subtype.val_inj]
  change (∃ x : K.X ((ComplexShape.up ℤ).prev i),
    K.d ((ComplexShape.up ℤ).prev i) i x = z.val) ↔ _
  rw [(ComplexShape.up ℤ).prev_eq' (show (ComplexShape.up ℤ).Rel (i-1) i by change (i-1)+1=i; omega)]


-- @@ L559-561 verbatim
lemma memZ_iff (i : ℤ) (x : K.X i) : x ∈ Z K i ↔ K.d i (i+1) x = 0 := by
  change K.d i ((ComplexShape.up ℤ).next i) x = 0 ↔ _
  rw [(ComplexShape.up ℤ).next_eq' (show (ComplexShape.up ℤ).Rel i (i+1) from rfl)]


-- @@ L563-563 verbatim
end Tachikawa.VectorSplit




-- @@ L567-567 verbatim
namespace Tachikawa.VectorSplit

-- @@ L568-568 verbatim
open CategoryTheory

-- @@ L569-573 verbatim
variable {k : Type*} [Field k] {K L M : CochainComplex (ModuleCat k) ℤ}
  (i : K ⟶ L) (p : L ⟶ M)
  (hi : ∀ a, Function.Injective (i.f a))
  (he : ∀ a, Function.Exact (i.f a) (p.f a))
  (hp : ∀ a, Function.Surjective (p.f a))


-- @@ L575-577 verbatim
lemma comm_apply {K L : CochainComplex (ModuleCat k) ℤ} (f : K ⟶ L)
    (a b : ℤ) (x : K.X a) : L.d a b (f.f a x) = f.f b (K.d a b x) :=
  congrArg (fun z => z x) (f.comm a b)


-- @@ L579-608 verbatim
include hi he hp in

lemma Hmap_surjective_of_right_zero (a : ℤ) (hM : Subsingleton (H M a)) :
    Function.Surjective (Hmap i a) := by
  intro x
  obtain ⟨z,rfl⟩ := quotient_surjective a x
  have hpz : quotient M a (cycleMap p a z) = 0 := hM.elim _ _
  obtain ⟨y,hy⟩ := (quotient_zero_iff_predecessor a _).mp hpz
  obtain ⟨v,hv⟩ := hp (a-1) y
  have hz' : p.f a (z.val - L.d (a-1) a v) = 0 := by
    rw [map_sub,← comm_apply p,hv,hy]
    exact sub_self _
  obtain ⟨u,hu⟩ := (he a _).mp hz'
  have huz : u ∈ Z K a := by
    rw [memZ_iff]
    apply hi (a+1)
    rw [map_zero,← comm_apply i,hu,map_sub]
    rw [(memZ_iff a z.val).mp z.property]
    have hd := congrArg (fun f => f v) (L.d_comp_d (a-1) a (a+1))
    change L.d a (a+1) (L.d (a-1) a v) = 0 at hd
    rw [hd,sub_self]
  refine ⟨quotient K a ⟨u,huz⟩,?_⟩
  rw [Hmap_quotient]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (quotient_zero_iff_predecessor a _).mpr
  use -v
  change L.d (a-1) a (-v) = i.f a u - z.val
  rw [map_neg,hu]
  abel


-- @@ L610-642 verbatim
include hi he hp in

lemma Hmap_injective_of_prev_surjective (a : ℤ)
    (hs : Function.Surjective (Hmap p (a-1))) : Function.Injective (Hmap i a) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  obtain ⟨z,rfl⟩ := quotient_surjective a x
  obtain ⟨v,hv⟩ := (quotient_zero_iff_predecessor a _).mp hx
  have hpv : p.f (a-1) v ∈ Z M (a-1) := by
    rw [memZ_iff,show a-1+1=a by omega,comm_apply p,hv]
    exact (he a _).mpr ⟨z.val,rfl⟩
  obtain ⟨c,hc⟩ := hs (quotient M (a-1) ⟨p.f (a-1) v,hpv⟩)
  obtain ⟨w,rfl⟩ := quotient_surjective (a-1) c
  have hw : quotient M (a-1) (⟨p.f (a-1) v,hpv⟩ - cycleMap p (a-1) w) = 0 := by
    rw [map_sub,← Hmap_quotient,hc,sub_self]
  obtain ⟨b,hb⟩ := (quotient_zero_iff_predecessor (a-1) _).mp hw
  obtain ⟨b',hb'⟩ := hp (a-1-1) b
  have hv' : p.f (a-1) (v-w.val-L.d (a-1-1) (a-1) b') = 0 := by
    rw [map_sub,map_sub,← comm_apply p,hb',hb]
    change p.f (a-1) v - p.f (a-1) w.val - (p.f (a-1) v-p.f (a-1) w.val) = 0
    exact sub_self _
  obtain ⟨u,hu⟩ := (he (a-1) _).mp hv'
  apply (quotient_zero_iff_predecessor a z).mpr
  refine ⟨u,?_⟩
  apply hi a
  rw [← comm_apply i,hu,map_sub,map_sub]
  have hwz := (memZ_iff (a-1) w.val).mp w.property
  rw [show a-1+1=a by omega] at hwz
  have hd := congrArg (fun f => f b') (L.d_comp_d (a-1-1) (a-1) a)
  change L.d (a-1) a (L.d (a-1-1) (a-1) b') = 0 at hd
  rw [hwz,hd,sub_zero,sub_zero]
  exact hv


-- @@ L644-649 verbatim
include hi he hp in
lemma Hmap_injective_of_prev_zero (a : ℤ) (hz : Subsingleton (H M (a-1))) :
    Function.Injective (Hmap i a) := by
  apply Hmap_injective_of_prev_surjective i p hi he hp a
  intro x
  exact ⟨0,by rw [map_zero]; exact hz.elim _ _⟩


-- @@ L651-655 verbatim
include hi he hp in
lemma Hmap_bijective_of_zeros (a : ℤ) (hprev : Subsingleton (H M (a-1)))
    (hnow : Subsingleton (H M a)) : Function.Bijective (Hmap i a) :=
  ⟨Hmap_injective_of_prev_zero i p hi he hp a hprev,
    Hmap_surjective_of_right_zero i p hi he hp a hnow⟩


-- @@ L657-657 verbatim
end Tachikawa.VectorSplit




-- @@ L661-661 verbatim
namespace Tachikawa

-- @@ L662-662 verbatim
open CategoryTheory

-- @@ L663-663 verbatim
open scoped ModuleCat.Algebra

-- @@ L664-665 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (P : ChainComplex (ModuleCat.{0} R) ℤ) {M N L : ModuleCat.{0} R}


-- @@ L667-676 verbatim
def completeHomMap (f : M ⟶ N) : completeHom (k := k) P M ⟶ completeHom (k := k) P N where
  f a := ModuleCat.ofHom (show (P.X a ⟶ M) →ₗ[k] (P.X a ⟶ N) from
    { toFun := fun g => g ≫ f
      map_add' := fun _ _ => by simp only [Preadditive.add_comp]
      map_smul' := fun r g => by simpa only [RingHom.id_apply] using (Linear.smul_comp (P.X a) M N r g f) })
  comm' _ _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    rfl


-- @@ L678-679 verbatim
@[simp] lemma completeHomMap_apply (f : M ⟶ N) (a : ℤ) (g : P.X a ⟶ M) :
    (completeHomMap (k := k) P f).f a g = g ≫ f := rfl


-- @@ L681-684 verbatim
@[simp] lemma completeHomMap_comp (f : M ⟶ N) (g : N ⟶ L) :
    completeHomMap (k := k) P (f ≫ g) = completeHomMap P f ≫ completeHomMap P g := by
  ext a x
  rfl


-- @@ L686-688 verbatim
@[simp] lemma completeHomMap_id : completeHomMap (k := k) P (𝟙 M) = 𝟙 _ := by
  ext a x
  rfl


-- @@ L690-692 verbatim
@[simp] lemma completeHomMap_zero : completeHomMap (k := k) P (0 : M ⟶ N) = 0 := by
  ext a x
  rfl


-- @@ L694-697 verbatim
@[simp] lemma completeHomMap_add (f g : M ⟶ N) :
    completeHomMap (k := k) P (f+g) = completeHomMap P f + completeHomMap P g := by
  ext a x
  rfl


-- @@ L699-704 verbatim
lemma completeHomMap_injective (i : M ⟶ N) (hi : Function.Injective i) (a : ℤ) :
    Function.Injective ((completeHomMap (k := k) P i).f a) := by
  change Function.Injective (fun f : P.X a ⟶ M => f ≫ i)
  intro f g h
  ext x
  exact hi (congrArg (fun z => z x) h)


-- @@ L706-719 verbatim
lemma completeHomMap_exact (i : M ⟶ N) (p : N ⟶ L)
    (hi : Function.Injective i) (he : Function.Exact i p) (a : ℤ) :
    Function.Exact ((completeHomMap (k := k) P i).f a) ((completeHomMap (k := k) P p).f a) := by
  change Function.Exact (fun f : P.X a ⟶ M => f ≫ i) (fun f : P.X a ⟶ N => f ≫ p)
  intro f
  constructor
  · intro hf
    have hr (x : P.X a) : f x ∈ LinearMap.range i.hom :=
      (he (f x)).mp (congrArg (fun z => z x) hf)
    refine ⟨ModuleCat.ofHom (CokerAt.factorThrough i.hom hi f.hom hr),?_⟩
    exact ModuleCat.hom_ext (CokerAt.factorThrough_spec i.hom hi f.hom hr)
  · rintro ⟨g,rfl⟩
    ext x
    exact (he _).mpr ⟨g x,rfl⟩


-- @@ L721-728 verbatim
lemma completeHomMap_surjective (p : N ⟶ L) (hp : Function.Surjective p)
    (proj : ∀ a, Module.Projective R (P.X a)) (a : ℤ) :
    Function.Surjective ((completeHomMap (k := k) P p).f a) := by
  let := proj a
  change Function.Surjective (fun f : P.X a ⟶ N => f ≫ p)
  intro f
  obtain ⟨g,hg⟩ := Module.projective_lifting_property p.hom f.hom hp
  exact ⟨ModuleCat.ofHom g,ModuleCat.hom_ext hg⟩


-- @@ L730-730 verbatim
end Tachikawa




-- @@ L734-734 verbatim
namespace Tachikawa

-- @@ L735-735 verbatim
open CategoryTheory

-- @@ L736-736 verbatim
open scoped ModuleCat.Algebra

-- @@ L737-738 verbatim
variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  (P : ChainComplex (ModuleCat.{0} R) ℤ)


-- @@ L740-749 verbatim
lemma completeHom_projective_zero (hP : TotallyAcyclic P) (N : ModuleCat.{0} R)
    [Module.Finite R N] [Module.Projective R N] (a : ℤ) :
    Subsingleton (VectorSplit.H (completeHom (k := k) P N) a) := by
  apply subsingleton_of_forall_eq 0
  intro x
  obtain ⟨z,rfl⟩ := VectorSplit.quotient_surjective a x
  obtain ⟨g,hg⟩ := hP.projective_boundaries a z.val.hom
    (ModuleCat.hom_ext_iff.mp ((completeHom_memZ P N a z.val).mp z.property))
  apply (VectorSplit.quotient_zero_iff_predecessor a z).mpr
  exact ⟨ModuleCat.ofHom g,ModuleCat.hom_ext hg⟩


-- @@ L751-752 verbatim
abbrev completeHmap {M N : ModuleCat.{0} R} (f : M ⟶ N) (a : ℤ) :=
  VectorSplit.Hmap (completeHomMap (k := k) P f) a


-- @@ L754-756 verbatim
@[simp] lemma completeHmap_comp {M N L : ModuleCat.{0} R} (f : M ⟶ N) (g : N ⟶ L) (a : ℤ) :
    completeHmap (k := k) P (f ≫ g) a = (completeHmap P g a).comp (completeHmap P f a) := by
  simp only [completeHmap,completeHomMap_comp,VectorSplit.Hmap_comp]

-- @@ L757-759 verbatim
@[simp] lemma completeHmap_id (M : ModuleCat.{0} R) (a : ℤ) :
    completeHmap (k := k) P (𝟙 M) a = LinearMap.id := by
  simp only [completeHmap,completeHomMap_id,VectorSplit.Hmap_id]

-- @@ L760-762 verbatim
@[simp] lemma completeHmap_add {M N : ModuleCat.{0} R} (f g : M ⟶ N) (a : ℤ) :
    completeHmap (k := k) P (f+g) a = completeHmap P f a + completeHmap P g a := by
  simp only [completeHmap,completeHomMap_add,VectorSplit.Hmap_add]

-- @@ L763-765 verbatim
@[simp] lemma completeHmap_zero {M N : ModuleCat.{0} R} (a : ℤ) :
    completeHmap (k := k) P (0 : M ⟶ N) a = 0 := by
  simp only [completeHmap,completeHomMap_zero,VectorSplit.Hmap_zero]


-- @@ L767-772 verbatim
def completeHomIso {M N : ModuleCat.{0} R} (e : M ≅ N) (a : ℤ) :
    VectorSplit.H (completeHom (k := k) P M) a ≃ₗ[k]
    VectorSplit.H (completeHom (k := k) P N) a :=
  LinearEquiv.ofLinearMap (completeHmap P e.hom a) (completeHmap P e.inv a)
    (by rw [← completeHmap_comp,e.inv_hom_id,completeHmap_id])
    (by rw [← completeHmap_comp,e.hom_inv_id,completeHmap_id])

-- @@ L773-773 verbatim
end Tachikawa




-- @@ L777-777 verbatim
namespace Tachikawa

-- @@ L778-778 verbatim
open CategoryTheory HomologicalComplex

-- @@ L779-779 verbatim
open scoped ModuleCat.Algebra

-- @@ L780-784 verbatim
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (F : ModuleCat.{0} R ⥤ ModuleCat.{0} S) [F.Additive] [F.Linear k]
  (P : ChainComplex (ModuleCat.{0} R) ℤ) (Q : ChainComplex (ModuleCat.{0} S) ℤ)
  (X : ModuleCat.{0} R)
  (l : Q ⟶ (F.mapHomologicalComplex (.down ℤ)).obj P)


-- @@ L786-796 verbatim
def completeFunctorHom : completeHom (k := k) P X ⟶ completeHom Q (F.obj X) where
  f a := ModuleCat.ofHom (show (P.X a ⟶ X) →ₗ[k] (Q.X a ⟶ F.obj X) from
    { toFun := fun g => l.f a ≫ F.map g
      map_add' := fun g h => by rw [F.map_add,Preadditive.comp_add]
      map_smul' := fun c g => by rw [F.map_smul,Linear.comp_smul]; rfl })
  comm' a b _ := by
    ext g
    change P.X a ⟶ X at g
    change Q.d b a ≫ l.f a ≫ F.map g = l.f b ≫ F.map (P.d b a ≫ g)
    rw [F.map_comp,← Category.assoc,← Category.assoc]
    exact congrArg (fun z => z ≫ F.map g) (l.comm b a).symm


-- @@ L798-824 verbatim
lemma completeFunctorHom_homotopic
    {l' : Q ⟶ (F.mapHomologicalComplex (.down ℤ)).obj P}
    (h : Homotopy l l') (a : ℤ) :
    VectorSplit.Hmap (completeFunctorHom (k := k) F P Q X l) a =
      VectorSplit.Hmap (completeFunctorHom (k := k) F P Q X l') a := by
  apply LinearMap.ext
  intro x
  obtain ⟨z,rfl⟩ := VectorSplit.quotient_surjective a x
  rw [VectorSplit.Hmap_quotient,VectorSplit.Hmap_quotient]
  apply sub_eq_zero.mp
  rw [← map_sub]
  apply (VectorSplit.quotient_zero_iff_predecessor a _).mpr
  refine ⟨h.hom (a-1) a ≫ F.map z.val,?_⟩
  change Q.d a (a-1) ≫ h.hom (a-1) a ≫ F.map z.val =
    l.f a ≫ F.map z.val - l'.f a ≫ F.map z.val
  have hc := h.comm a
  rw [dNext_eq _ (show (ComplexShape.down ℤ).Rel a (a-1) by change a-1+1=a; omega),
    prevD_eq _ (show (ComplexShape.down ℤ).Rel (a+1) a from rfl)] at hc
  have hz := (completeHom_memZ P X a z.val).mp z.property
  rw [hc,Preadditive.add_comp,Preadditive.add_comp,Category.assoc]
  let cycle : P.X a ⟶ X := z.val
  change P.d (a+1) a ≫ cycle = 0 at hz
  change Q.d a (a-1) ≫ h.hom (a-1) a ≫ F.map cycle =
    Q.d a (a-1) ≫ h.hom (a-1) a ≫ F.map cycle +
      (h.hom a (a+1) ≫ F.map (P.d (a+1) a) ≫ F.map cycle) +
      l'.f a ≫ F.map cycle - l'.f a ≫ F.map cycle
  rw [← F.map_comp,hz,F.map_zero,Limits.comp_zero,add_zero,add_sub_cancel_right]


-- @@ L826-826 verbatim
end Tachikawa




-- @@ L830-830 verbatim
namespace Tachikawa

-- @@ L831-831 verbatim
open CategoryTheory

-- @@ L832-832 verbatim
open scoped ModuleCat.Algebra

-- @@ L833-839 verbatim
variable {k R S : Type} [Field k] [Ring R] [Ring S] [Algebra k R] [Algebra k S]
  (F G : ModuleCat.{0} R ⥤ ModuleCat.{0} S) [F.Additive] [G.Additive]
  [F.Linear k] [G.Linear k]
  (P : ChainComplex (ModuleCat.{0} R) ℤ) (Q : ChainComplex (ModuleCat.{0} S) ℤ)
  (X : ModuleCat.{0} R)
  (l : Q ⟶ (F.mapHomologicalComplex (.down ℤ)).obj P)
  (α : F ⟶ G)


-- @@ L841-847 verbatim
lemma completeFunctorHom_natural :
    completeFunctorHom (k := k) F P Q X l ≫ completeHomMap Q (α.app X) =
      completeFunctorHom G P Q X (l ≫ (α.mapHomologicalComplex (.down ℤ)).app P) := by
  ext a g
  change P.X a ⟶ X at g
  change (l.f a ≫ F.map g) ≫ α.app X = (l.f a ≫ α.app (P.X a)) ≫ G.map g
  rw [Category.assoc,α.naturality,Category.assoc]


-- @@ L849-849 verbatim
end Tachikawa


-- @@ L851-851 verbatim
end


-- @@ L853-853 verbatim
end OAI
