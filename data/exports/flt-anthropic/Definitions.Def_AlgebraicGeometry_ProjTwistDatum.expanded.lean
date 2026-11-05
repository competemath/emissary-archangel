import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjSpaceCechGradedModule


-- @@ L5-5 verbatim
set_option autoImplicit false


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
universe u


-- @@ L11-11 verbatim
open CategoryTheory Opposite MvPolynomial HomogeneousLocalization


-- @@ L13-13 verbatim
namespace AlgebraicGeometry.ProjSpace


-- @@ L15-15 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L17-17 verbatim
variable (A : Type u) [CommRing A] (N : ℕ)


-- @@ L19-19 verbatim
local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A

-- @@ L20-20 verbatim
local notation "S" => MvPolynomial (Fin (N + 1)) A


-- @@ L22-34 verbatim
theorem val_awayMap_ratio (i i' k : Fin (N + 1)) {f g : S} (hg : g ∈ 𝒜 1) (hx : X i * X i' = f * g)
    (r : Away 𝒜 f) (a : S)
    (hr : r.val = Localization.mk a (⟨f ^ 1, ⟨1, rfl⟩⟩ : Submonoid.powers f)) :
    (awayMap 𝒜 hg hx r).val
      = Localization.mk (a * g) (⟨(X i * X i' : S) ^ 1, ⟨1, rfl⟩⟩ : Submonoid.powers (X i * X i' : S)) := by
  rw [val_awayMap, hr]
  have hv : algebraMap S (Localization.Away (X i * X i' : S)) f
      * Localization.mk g (⟨(X i * X i' : S) ^ 1, ⟨1, rfl⟩⟩ : Submonoid.powers (X i * X i' : S)) = 1 := by
    rw [← Localization.mk_one_eq_algebraMap, Localization.mk_mul, ← Localization.mk_one,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    exact ⟨1, by simp [hx]⟩
  rw [Localization.awayLift_mk (hv := hv), ← Localization.mk_one_eq_algebraMap, pow_one, Localization.mk_mul,
    one_mul]


-- @@ L36-48 verbatim
theorem awayMap_ratio_mul (i i' j : Fin (N + 1)) :
    awayMap 𝒜 (X_mem_one A N i') rfl (ratio A N i i')
        * awayMap 𝒜 (X_mem_one A N i) (mul_comm (X i) (X i') : (X i * X i' : S) = X i' * X i) (ratio A N i' j)
      = awayMap 𝒜 (X_mem_one A N i') rfl (ratio A N i j) := by
  apply HomogeneousLocalization.val_injective
  rw [val_mul,
    val_awayMap_ratio A N i i' i' (X_mem_one A N i') rfl _ (X i') (by rw [ratio, Away.val_mk]),
    val_awayMap_ratio A N i i' j (X_mem_one A N i) (mul_comm (X i) (X i')) _ (X j) (by rw [ratio, Away.val_mk]),
    val_awayMap_ratio A N i i' j (X_mem_one A N i') rfl _ (X j) (by rw [ratio, Away.val_mk]),
    Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩
  simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
  ring


-- @@ L50-54 verbatim
theorem awayMap_ratio_mul_swap (i i' : Fin (N + 1)) :
    awayMap 𝒜 (X_mem_one A N i') rfl (ratio A N i i')
        * awayMap 𝒜 (X_mem_one A N i) (mul_comm (X i) (X i') : (X i * X i' : S) = X i' * X i) (ratio A N i' i)
      = 1 := by
  rw [awayMap_ratio_mul, ratio_self, map_one]


-- @@ L56-56 verbatim
end AlgebraicGeometry.ProjSpace


-- @@ L58-58 verbatim
namespace AlgebraicGeometry


-- @@ L60-60 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L62-62 verbatim
namespace ProjSpace


-- @@ L64-65 verbatim
variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))


-- @@ L67-68 verbatim
def pullbackChart (i : Fin (N + 1)) : X.Opens :=
  φ ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X i)


-- @@ L70-71 verbatim
theorem pullbackChart_eq (i : Fin (N + 1)) :
    pullbackChart φ i = φ ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X i) := rfl


-- @@ L73-75 verbatim
def frameUnit (i j : Fin (N + 1)) : Γ(X, pullbackChart φ i) :=
  (φ.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X i))).hom
    ((Proj.awayToSection _ (MvPolynomial.X i)).hom (ProjSpace.ratio A N i j))


-- @@ L77-78 verbatim
abbrev restrictFun {U U' : X.Opens} (h : U ≤ U') : Γ(X, U') →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE h).op).hom


-- @@ L80-84 verbatim
def TwistCompat (m : ℕ) (U : X.Opens) (g : ∀ i : Fin (N + 1), Γ(X, U ⊓ pullbackChart φ i)) : Prop :=
  ∀ i j : Fin (N + 1),
    restrictFun (inf_le_left : (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ U ⊓ pullbackChart φ i) (g i)
      = restrictFun (le_trans inf_le_left inf_le_right : (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ pullbackChart φ i) (frameUnit φ i j) ^ m
        * restrictFun (le_inf (le_trans inf_le_left inf_le_left) inf_le_right : (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ U ⊓ pullbackChart φ j) (g j)


-- @@ L86-94 verbatim
def twistSections (m : ℕ) (U : X.Opens) : AddSubgroup (∀ i : Fin (N + 1), Γ(X, U ⊓ pullbackChart φ i)) where
  carrier := {g | TwistCompat φ m U g}
  zero_mem' := fun i j => by simp
  add_mem' := by
    intro g g' hg hg' i j
    simp only [Pi.add_apply, map_add, hg i j, hg' i j, mul_add]
  neg_mem' := by
    intro g hg i j
    simp only [Pi.neg_apply, map_neg, hg i j, mul_neg]


-- @@ L96-97 verbatim
theorem mem_twistSections {m : ℕ} {U : X.Opens} (g : ∀ i : Fin (N + 1), Γ(X, U ⊓ pullbackChart φ i)) :
    g ∈ twistSections φ m U ↔ TwistCompat φ m U g := Iff.rfl


-- @@ L99-111 verbatim
theorem smul_mem_twistSections {m : ℕ} {U : X.Opens} (a : Γ(X, U)) {g : ∀ i, Γ(X, U ⊓ pullbackChart φ i)}
    (hg : g ∈ twistSections φ m U) :
    (fun i => restrictFun (inf_le_left : U ⊓ pullbackChart φ i ≤ U) a * g i) ∈ twistSections φ m U := by
  intro i j
  simp only [map_mul, hg i j]
  have h1 : restrictFun (inf_le_left : (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ U ⊓ pullbackChart φ i) (restrictFun (inf_le_left : U ⊓ pullbackChart φ i ≤ U) a)
      = restrictFun (le_inf (le_trans inf_le_left inf_le_left) inf_le_right : (U ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ U ⊓ pullbackChart φ j)
          (restrictFun (inf_le_left : U ⊓ pullbackChart φ j ≤ U) a) := by
    show (X.presheaf.map _ ≫ X.presheaf.map _).hom a = (X.presheaf.map _ ≫ X.presheaf.map _).hom a
    rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
    rfl
  rw [h1]
  ring


-- @@ L113-128 verbatim
theorem res_mem_twistSections {m : ℕ} {U U' : X.Opens} (h : U ≤ U') {g : ∀ i, Γ(X, U' ⊓ pullbackChart φ i)}
    (hg : g ∈ twistSections φ m U') :
    (fun i => restrictFun (inf_le_inf_right (pullbackChart φ i) h) (g i)) ∈ twistSections φ m U := by
  intro i j
  have key := congrArg (restrictFun (inf_le_inf_right (pullbackChart φ j) (inf_le_inf_right (pullbackChart φ i) h))) (hg i j)
  simp only [map_mul, map_pow] at key

  have e1 : ∀ (W₁ W₂ W₃ : X.Opens) (h₁ : W₁ ≤ W₂) (h₂ : W₂ ≤ W₃) (x : Γ(X, W₃)),
      restrictFun h₁ (restrictFun h₂ x) = restrictFun (h₁.trans h₂) x := by
    intro W₁ W₂ W₃ h₁ h₂ x
    show (X.presheaf.map _ ≫ X.presheaf.map _).hom x = _
    rw [← X.presheaf.map_comp]
    rfl
  rw [e1, e1, e1] at key
  rw [e1, e1]
  convert key using 2


-- @@ L130-130 verbatim
end ProjSpace


-- @@ L132-132 verbatim
end AlgebraicGeometry


-- @@ L134-134 verbatim
namespace AlgebraicGeometry

-- @@ L135-135 verbatim
namespace ProjSpace


-- @@ L137-137 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L139-139 verbatim
variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}


-- @@ L141-145 verbatim
theorem restrictFun_restrictFun {W₁ W₂ W₃ : X.Opens} (h₁ : W₁ ≤ W₂) (h₂ : W₂ ≤ W₃) (x : Γ(X, W₃)) :
    restrictFun h₁ (restrictFun h₂ x) = restrictFun (h₁.trans h₂) x := by
  show (X.presheaf.map _ ≫ X.presheaf.map _).hom x = _
  rw [← X.presheaf.map_comp]
  rfl


-- @@ L147-147 verbatim
theorem restrictFun_irrel {W₁ W₂ : X.Opens} (h₁ h₂ : W₁ ≤ W₂) (x : Γ(X, W₂)) : restrictFun h₁ x = restrictFun h₂ x := rfl


-- @@ L149-152 verbatim
theorem restrictFun_refl {W : X.Opens} (x : Γ(X, W)) : restrictFun (le_refl W) x = x := by
  show (X.presheaf.map (homOfLE (le_refl W)).op).hom x = x
  rw [Subsingleton.elim (homOfLE (le_refl W)).op (𝟙 (op W)), X.presheaf.map_id]
  rfl


-- @@ L154-160 verbatim
theorem restrictFun_algebraMap (π : X ⟶ Spec (.of A)) {U U' : X.Opens} (h : U ≤ U') (r : A) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U'
    restrictFun h (algebraMap A (Γ(X, U') : Type u) r) = algebraMap A (Γ(X, U) : Type u) r := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π U'
  exact (Scheme.TwoAffineOpenCover.restrictAlgHom π h).commutes r


-- @@ L162-165 verbatim
theorem restrictFun_algebraMap' (π : X ⟶ Spec (.of A)) {U U' : X.Opens} (h : U ≤ U') (r : A) :
    restrictFun h ((Scheme.TwoAffineOpenCover.algebraOfHom π U').algebraMap r)
      = (Scheme.TwoAffineOpenCover.algebraOfHom π U).algebraMap r :=
  restrictFun_algebraMap π h r


-- @@ L167-171 verbatim
@[ext] structure twistObj (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ) (U : X.Opens) : Type u where

  val : ∀ i : Fin (N + 1), Γ(X, U ⊓ pullbackChart φ i)

  compat : TwistCompat φ m U val


-- @@ L173-178 verbatim
def twistObj.equivSections (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ) (U : X.Opens) :
    twistObj π φ m U ≃ twistSections φ m U where
  toFun g := ⟨g.val, g.compat⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl


-- @@ L180-181 verbatim
instance twistObj.addCommGroup (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ) (U : X.Opens) : AddCommGroup (twistObj π φ m U) :=
  (twistObj.equivSections π φ m U).addCommGroup


-- @@ L183-185 verbatim
theorem twistObj.val_injective {π : X ⟶ Spec (.of A)} {φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)} {m : ℕ} {U : X.Opens} :
    Function.Injective (twistObj.val (π := π) (φ := φ) (m := m) (U := U)) :=
  fun _ _ h => twistObj.ext h


-- @@ L187-212 verbatim
instance twistObj.moduleSections (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ) (U : X.Opens) : Module Γ(X, U) (twistObj π φ m U) where
  smul a g := ⟨fun i => restrictFun inf_le_left a * g.val i, smul_mem_twistSections φ a g.compat⟩
  one_smul g := by
    refine twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ 1 * g.val i = g.val i
    rw [map_one, one_mul]
  mul_smul a b g := by
    refine twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ (a * b) * g.val i = restrictFun _ a * (restrictFun _ b * g.val i)
    rw [map_mul, mul_assoc]
  smul_zero a := by
    refine twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ a * (0 : Γ(X, U ⊓ pullbackChart φ i)) = 0
    rw [mul_zero]
  smul_add a g g' := by
    refine twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ a * (g.val i + g'.val i) = restrictFun _ a * g.val i + restrictFun _ a * g'.val i
    rw [mul_add]
  add_smul a b g := by
    refine twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ (a + b) * g.val i = restrictFun _ a * g.val i + restrictFun _ b * g.val i
    rw [map_add, add_mul]
  zero_smul g := by
    refine twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ 0 * g.val i = 0
    rw [map_zero, zero_mul]


-- @@ L214-215 verbatim
@[simp] theorem twistObj.smul_val {π : X ⟶ Spec (.of A)} {φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)} {m : ℕ} {U : X.Opens} (a : Γ(X, U)) (g : twistObj π φ m U) (i : Fin (N + 1)) :
    (a • g).val i = restrictFun inf_le_left a * g.val i := rfl


-- @@ L217-219 verbatim
instance twistObj.module (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ) (U : X.Opens) : Module A (twistObj π φ m U) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
  Module.compHom (twistObj π φ m U) (algebraMap A (Γ(X, U) : Type u))


-- @@ L221-223 verbatim
theorem twistObj.algebraMap_smul {π : X ⟶ Spec (.of A)} {φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)} {m : ℕ} {U : X.Opens} (r : A) (g : twistObj π φ m U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    r • g = algebraMap A (Γ(X, U) : Type u) r • g := by rfl


-- @@ L225-238 verbatim
def twistRes (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ) {U U' : X.Opens} (h : U ≤ U') : twistObj π φ m U' →ₗ[A] twistObj π φ m U :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom π U'
  { toFun := fun g => ⟨fun i => restrictFun (inf_le_inf_right (pullbackChart φ i) h) (g.val i),
      res_mem_twistSections φ h g.compat⟩
    map_add' := fun g g' => by
      refine twistObj.ext (_root_.funext fun i => ?_)
      show restrictFun _ (g.val i + g'.val i) = restrictFun _ (g.val i) + restrictFun _ (g'.val i)
      rw [map_add]
    map_smul' := fun r g => by
      refine twistObj.ext (_root_.funext fun i => ?_)
      show restrictFun _ (restrictFun _ (algebraMap A (Γ(X, U') : Type u) r) * g.val i)
        = restrictFun _ (algebraMap A (Γ(X, U) : Type u) r) * restrictFun _ (g.val i)
      rw [map_mul, restrictFun_restrictFun, ← restrictFun_algebraMap π h r, restrictFun_restrictFun] }


-- @@ L240-241 verbatim
theorem twistRes_val (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ) {U U' : X.Opens} (h : U ≤ U') (g : twistObj π φ m U') (i : Fin (N + 1)) :
    (twistRes π φ m h g).val i = restrictFun (inf_le_inf_right (pullbackChart φ i) h) (g.val i) := rfl


-- @@ L243-266 verbatim
def twist (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ) : OModulePresheaf π where
  obj U := twistObj π φ m U
  addCommGroup _ := inferInstance
  module U := twistObj.module π φ m U
  moduleSections U := twistObj.moduleSections π φ m U
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    exact ⟨fun r a g => by
      show (r • a) • g = algebraMap A (Γ(X, U) : Type u) r • (a • g)
      rw [Algebra.smul_def, mul_smul]⟩
  res h := twistRes π φ m h
  res_smul h a g := by
    change twistRes π φ m h (a • g) = restrictFun h a • twistRes π φ m h g
    refine twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ (restrictFun _ a * g.val i) = restrictFun _ (restrictFun _ a) * restrictFun _ (g.val i)
    rw [map_mul, restrictFun_restrictFun, restrictFun_restrictFun]
  res_refl U := by
    refine LinearMap.ext fun g => twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ (g.val i) = g.val i
    exact restrictFun_refl _
  res_comp h h' := by
    refine LinearMap.ext fun g => twistObj.ext (_root_.funext fun i => ?_)
    show restrictFun _ (g.val i) = restrictFun _ (restrictFun _ (g.val i))
    rw [restrictFun_restrictFun]


-- @@ L268-268 verbatim
theorem twist_obj (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) (m : ℕ) (U : X.Opens) : (twist π φ m).obj U = twistObj π φ m U := rfl


-- @@ L270-270 verbatim
end ProjSpace

-- @@ L271-271 verbatim
end AlgebraicGeometry


-- @@ L273-273 verbatim
namespace AlgebraicGeometry.ProjSpace


-- @@ L275-275 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L277-278 verbatim
variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))


-- @@ L280-281 verbatim
def pullbackOverlap (i i' : Fin (N + 1)) : X.Opens :=
  φ ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (MvPolynomial.X i * MvPolynomial.X i')


-- @@ L283-284 verbatim
theorem pullbackOverlap_eq_inf (i i' : Fin (N + 1)) : pullbackOverlap φ i i' = pullbackChart φ i ⊓ pullbackChart φ i' := by
  rw [pullbackOverlap, Proj.basicOpen_mul, Scheme.Hom.preimage_inf]; rfl


-- @@ L286-287 verbatim
theorem pullbackOverlap_le_left (i i' : Fin (N + 1)) : pullbackOverlap φ i i' ≤ pullbackChart φ i := by
  rw [pullbackOverlap_eq_inf]; exact inf_le_left


-- @@ L289-290 verbatim
theorem pullbackOverlap_le_right (i i' : Fin (N + 1)) : pullbackOverlap φ i i' ≤ pullbackChart φ i' := by
  rw [pullbackOverlap_eq_inf]; exact inf_le_right


-- @@ L292-311 verbatim
theorem restrictFun_frameUnit_left (i i' k : Fin (N + 1)) :
    restrictFun (pullbackOverlap_le_left φ i i') (frameUnit φ i k)
      = (φ.app (Proj.basicOpen _ (MvPolynomial.X i * MvPolynomial.X i'))).hom
          ((Proj.awayToSection _ (MvPolynomial.X i * MvPolynomial.X i')).hom
            (awayMap _ (X_mem_one A N i') rfl (ratio A N i k))) := by

  have h1 := congrArg (fun (ψ : CommRingCat.of (Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)
      (MvPolynomial.X i)) ⟶ _) => ψ.hom (ratio A N i k))
    (Proj.awayMap_awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (X_mem_one A N i')
      (rfl : (MvPolynomial.X i * MvPolynomial.X i' : MvPolynomial (Fin (N + 1)) A) = MvPolynomial.X i * MvPolynomial.X i'))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
  rw [h1]

  have h2 := congrArg (fun ψ => ψ.hom ((Proj.awayToSection _ (MvPolynomial.X i)).hom (ratio A N i k)))
    (φ.naturality (homOfLE (show Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)
        (MvPolynomial.X i * MvPolynomial.X i') ≤ Proj.basicOpen _ (MvPolynomial.X i) from by
      rw [Proj.basicOpen_mul]; exact inf_le_left)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [h2]
  rfl


-- @@ L313-333 verbatim
theorem restrictFun_frameUnit_right (i i' k : Fin (N + 1)) :
    restrictFun (pullbackOverlap_le_right φ i i') (frameUnit φ i' k)
      = (φ.app (Proj.basicOpen _ (MvPolynomial.X i * MvPolynomial.X i'))).hom
          ((Proj.awayToSection _ (MvPolynomial.X i * MvPolynomial.X i')).hom
            (awayMap _ (X_mem_one A N i) (mul_comm (MvPolynomial.X i) (MvPolynomial.X i') :
              (MvPolynomial.X i * MvPolynomial.X i' : MvPolynomial (Fin (N + 1)) A) = MvPolynomial.X i' * MvPolynomial.X i)
              (ratio A N i' k))) := by
  have h1 := congrArg (fun (ψ : CommRingCat.of (Away (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)
      (MvPolynomial.X i')) ⟶ _) => ψ.hom (ratio A N i' k))
    (Proj.awayMap_awayToSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A) (X_mem_one A N i)
      (mul_comm (MvPolynomial.X i) (MvPolynomial.X i') :
        (MvPolynomial.X i * MvPolynomial.X i' : MvPolynomial (Fin (N + 1)) A) = MvPolynomial.X i' * MvPolynomial.X i))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1
  rw [h1]
  have h2 := congrArg (fun ψ => ψ.hom ((Proj.awayToSection _ (MvPolynomial.X i')).hom (ratio A N i' k)))
    (φ.naturality (homOfLE (show Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)
        (MvPolynomial.X i * MvPolynomial.X i') ≤ Proj.basicOpen _ (MvPolynomial.X i') from by
      rw [Proj.basicOpen_mul]; exact inf_le_right)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
  rw [h2]
  rfl


-- @@ L335-340 verbatim
theorem frameUnit_cocycle (i i' j : Fin (N + 1)) :
    restrictFun (pullbackOverlap_le_left φ i i') (frameUnit φ i i') * restrictFun (pullbackOverlap_le_right φ i i') (frameUnit φ i' j)
      = restrictFun (pullbackOverlap_le_left φ i i') (frameUnit φ i j) := by
  rw [restrictFun_frameUnit_left, restrictFun_frameUnit_right, restrictFun_frameUnit_left]
  exact (map_mul (((φ.app _).hom).comp (Proj.awayToSection _ _).hom) _ _).symm.trans
    (congrArg _ (awayMap_ratio_mul A N i i' j))


-- @@ L342-344 verbatim
theorem frameUnit_self (i : Fin (N + 1)) : frameUnit φ i i = 1 := by
  rw [frameUnit, ratio_self, map_one, map_one]
  rfl


-- @@ L346-348 verbatim
theorem frameUnit_mul_swap (i i' : Fin (N + 1)) :
    restrictFun (pullbackOverlap_le_left φ i i') (frameUnit φ i i') * restrictFun (pullbackOverlap_le_right φ i i') (frameUnit φ i' i) = 1 := by
  rw [frameUnit_cocycle, frameUnit_self, map_one]


-- @@ L350-350 verbatim
end AlgebraicGeometry.ProjSpace


-- @@ L352-352 verbatim
namespace AlgebraicGeometry.ProjSpace


-- @@ L354-354 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L356-356 verbatim
variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}


-- @@ L358-359 verbatim
@[simp] theorem twistObj.add_val {π : X ⟶ Spec (.of A)} {φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)} {m : ℕ} {U : X.Opens}
    (g g' : twistObj π φ m U) : (g + g').val = g.val + g'.val := rfl


-- @@ L361-362 verbatim
@[simp] theorem twistObj.zero_val {π : X ⟶ Spec (.of A)} {φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)} {m : ℕ} {U : X.Opens} :
    (0 : twistObj π φ m U).val = 0 := rfl


-- @@ L364-366 verbatim
@[simp] theorem twist_res_val {π : X ⟶ Spec (.of A)} {φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)} {m : ℕ}
    {U U' : X.Opens} (h : U ≤ U') (g : twistObj π φ m U') (i : Fin (N + 1)) :
    ((twist π φ m).res h g).val i = restrictFun (inf_le_inf_right (pullbackChart φ i) h) (g.val i) := rfl


-- @@ L368-370 verbatim
@[simp] theorem twist_smul_val {π : X ⟶ Spec (.of A)} {φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)} {m : ℕ}
    {U : X.Opens} (a : Γ(X, U)) (g : (twist π φ m).obj U) (i : Fin (N + 1)) :
    (a • g : twistObj π φ m U).val i = restrictFun inf_le_left a * (g : twistObj π φ m U).val i := rfl


-- @@ L372-376 verbatim
theorem twist_algebraMap_smul_val {π : X ⟶ Spec (.of A)} {φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)} {m : ℕ}
    {U : X.Opens} (r : A) (g : (twist π φ m).obj U) (i : Fin (N + 1)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    (r • g : twistObj π φ m U).val i = restrictFun inf_le_left (algebraMap A (Γ(X, U) : Type u) r) * (g : twistObj π φ m U).val i :=
  rfl


-- @@ L378-378 verbatim
end AlgebraicGeometry.ProjSpace


-- @@ L380-380 verbatim
namespace AlgebraicGeometry.ProjSpace


-- @@ L382-382 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L384-384 verbatim
variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}


-- @@ L386-386 verbatim
section GradedModuleOfTwist


-- @@ L388-388 verbatim
variable (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))


-- @@ L390-390 verbatim
def twistFam (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) : Type u := ℤ → ∀ i : Fin (N + 1), Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i)


-- @@ L392-392 verbatim
instance twistFam.addCommGroup (π : X ⟶ Spec (.of A)) : AddCommGroup (twistFam π φ) := inferInstanceAs (AddCommGroup (ℤ → ∀ i : Fin (N + 1), Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i)))


-- @@ L394-395 verbatim
@[reducible] def moduleOfHom (π : X ⟶ Spec (.of A)) (W : X.Opens) : Module A (Γ(X, W) : Type u) :=
  (Scheme.TwoAffineOpenCover.algebraOfHom π W).toModule


-- @@ L397-399 verbatim
instance twistFam.module (π : X ⟶ Spec (.of A)) : Module A (twistFam π φ) := by
  letI : ∀ i : Fin (N + 1), Module A (Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i) : Type u) := fun i => moduleOfHom π _
  exact inferInstanceAs (Module A (ℤ → ∀ i : Fin (N + 1), Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i)))


-- @@ L401-402 verbatim
theorem twistFam.smul_apply (π : X ⟶ Spec (.of A)) (r : A) (f : twistFam π φ) (d : ℤ) (i : Fin (N + 1)) :
    (r • f) d i = (Scheme.TwoAffineOpenCover.algebraOfHom π ((⊤ : X.Opens) ⊓ pullbackChart φ i)).algebraMap r * f d i := rfl


-- @@ L404-435 verbatim
def twistGrade (π : X ⟶ Spec (.of A)) (d : ℤ) : Submodule A (twistFam π φ) where
  carrier := {f | (∀ d', d' ≠ d → f d' = 0) ∧ (d < 0 → f d = 0) ∧ (0 ≤ d → TwistCompat φ d.toNat ⊤ (f d))}
  zero_mem' := ⟨fun _ _ => rfl, fun _ => rfl, fun _ => (twistSections φ d.toNat ⊤).zero_mem⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3⟩ ⟨hg1, hg2, hg3⟩
    refine ⟨fun d' hd' => ?_, fun hd => ?_, fun hd => (twistSections φ d.toNat ⊤).add_mem (hf3 hd) (hg3 hd)⟩
    · show f d' + g d' = 0
      rw [hf1 d' hd', hg1 d' hd', add_zero]
    · show f d + g d = 0
      rw [hf2 hd, hg2 hd, add_zero]
  smul_mem' := by
    rintro r f ⟨hf1, hf2, hf3⟩
    refine ⟨fun d' hd' => ?_, fun hd => ?_, fun hd => ?_⟩
    · funext i
      show _ * f d' i = 0
      rw [hf1 d' hd']
      exact mul_zero _
    · funext i
      show _ * f d i = 0
      rw [hf2 hd]
      exact mul_zero _
    · intro i j
      have hc := hf3 hd i j
      have hi := restrictFun_algebraMap' π
        (inf_le_left : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ (⊤ : X.Opens) ⊓ pullbackChart φ i) r
      have hj := restrictFun_algebraMap' π
        (le_inf (le_trans inf_le_left inf_le_left) inf_le_right :
          ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ j ≤ (⊤ : X.Opens) ⊓ pullbackChart φ j) r
      show restrictFun _ ((Scheme.TwoAffineOpenCover.algebraOfHom π _).algebraMap r * f d i)
        = _ * restrictFun _ ((Scheme.TwoAffineOpenCover.algebraOfHom π _).algebraMap r * f d j)
      rw [map_mul, map_mul, hc, hi, hj]
      ring


-- @@ L437-448 verbatim
def twistXMul (π : X ⟶ Spec (.of A)) (j : Fin (N + 1)) : twistFam π φ →ₗ[A] twistFam π φ where
  toFun f := fun d i => restrictFun inf_le_right (frameUnit φ i j) * f (d - 1) i
  map_add' f g := by
    funext d i
    show restrictFun _ (frameUnit φ i j) * (f (d - 1) i + g (d - 1) i) = _ * _ + _ * _
    rw [mul_add]
  map_smul' r f := by
    funext d i
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π ((⊤ : X.Opens) ⊓ pullbackChart φ i)
    show restrictFun _ (frameUnit φ i j) * (algebraMap A (Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i) : Type u) r * f (d - 1) i)
      = algebraMap A (Γ(X, (⊤ : X.Opens) ⊓ pullbackChart φ i) : Type u) r * (restrictFun _ (frameUnit φ i j) * f (d - 1) i)
    ring


-- @@ L450-451 verbatim
theorem twistXMul_apply (π : X ⟶ Spec (.of A)) (j : Fin (N + 1)) (f : twistFam π φ) (d : ℤ) (i : Fin (N + 1)) :
    twistXMul φ π j f d i = restrictFun inf_le_right (frameUnit φ i j) * f (d - 1) i := rfl


-- @@ L453-464 verbatim
theorem frameUnit_cocycle_top (i i' j : Fin (N + 1)) :
    restrictFun (inf_le_left : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i' ≤ (⊤ : X.Opens) ⊓ pullbackChart φ i)
        (restrictFun inf_le_right (frameUnit φ i j))
      = restrictFun (le_trans inf_le_left inf_le_right : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i' ≤ pullbackChart φ i) (frameUnit φ i i')
        * restrictFun (le_inf (le_trans inf_le_left inf_le_left) inf_le_right :
            ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i' ≤ (⊤ : X.Opens) ⊓ pullbackChart φ i')
          (restrictFun inf_le_right (frameUnit φ i' j)) := by
  have hW : ((⊤ : X.Opens) ⊓ pullbackChart φ i) ⊓ pullbackChart φ i' ≤ pullbackOverlap φ i i' := by
    rw [pullbackOverlap_eq_inf]; exact le_inf (le_trans inf_le_left inf_le_right) inf_le_right
  have key := congrArg (restrictFun hW) (frameUnit_cocycle φ i i' j)
  rw [map_mul, restrictFun_restrictFun, restrictFun_restrictFun, restrictFun_restrictFun] at key
  rw [restrictFun_restrictFun, restrictFun_restrictFun, ← key]


-- @@ L466-485 verbatim
theorem twistXMul_mem (π : X ⟶ Spec (.of A)) (j : Fin (N + 1)) (d : ℤ) (f : twistFam π φ) (hf : f ∈ twistGrade φ π d) :
    twistXMul φ π j f ∈ twistGrade φ π (d + 1) := by
  obtain ⟨hf1, hf2, hf3⟩ := hf
  refine ⟨fun d' hd' => ?_, fun hd => ?_, fun hd => ?_⟩
  · funext i; rw [twistXMul_apply, hf1 (d' - 1) (by omega)]; exact mul_zero _
  · funext i
    rw [twistXMul_apply, show d + 1 - 1 = d by ring, hf2 (by omega)]
    exact mul_zero _
  · rcases lt_or_ge d 0 with hlt | hge
    ·
      have h0 : f d = 0 := hf2 hlt
      intro i i'
      have h0i : ∀ k, f d k = 0 := fun k => by rw [h0]; rfl
      simp only [twistXMul_apply, show d + 1 - 1 = d by ring, h0i, mul_zero, map_zero]
    · have hc := hf3 hge
      have hnat : (d + 1).toNat = d.toNat + 1 := by omega
      intro i i'
      simp only [twistXMul_apply, show d + 1 - 1 = d by ring, map_mul, hnat, pow_succ]
      rw [hc i i', frameUnit_cocycle_top φ i i' j]
      ring


-- @@ L487-487 verbatim
end GradedModuleOfTwist


-- @@ L489-489 verbatim
end AlgebraicGeometry.ProjSpace


-- @@ L491-491 verbatim
namespace AlgebraicGeometry.ProjSpace


-- @@ L493-493 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L495-496 verbatim
variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))


-- @@ L498-503 verbatim
theorem twistXMul_comm (π : X ⟶ Spec (.of A)) (j k : Fin (N + 1)) : twistXMul φ π j ∘ₗ twistXMul φ π k = twistXMul φ π k ∘ₗ twistXMul φ π j := by
  refine LinearMap.ext fun f => ?_
  funext d i
  show restrictFun _ (frameUnit φ i j) * (restrictFun _ (frameUnit φ i k) * f (d - 1 - 1) i)
    = restrictFun _ (frameUnit φ i k) * (restrictFun _ (frameUnit φ i j) * f (d - 1 - 1) i)
  ring


-- @@ L505-510 verbatim
def twistGradedModule (π : X ⟶ Spec (.of A)) : ProjSpaceCech.GradedModule A N where
  M := twistFam π φ
  grade := twistGrade φ π
  xMul := twistXMul φ π
  xMul_mem_grade j d f hf := twistXMul_mem φ π j d f hf
  xMul_comm j k := twistXMul_comm φ π j k


-- @@ L512-512 verbatim
theorem twistGradedModule_M (π : X ⟶ Spec (.of A)) : (twistGradedModule φ π).M = twistFam π φ := rfl

-- @@ L513-513 verbatim
theorem twistGradedModule_grade (π : X ⟶ Spec (.of A)) (d : ℤ) : (twistGradedModule φ π).grade d = twistGrade φ π d := rfl

-- @@ L514-514 verbatim
theorem twistGradedModule_xMul (π : X ⟶ Spec (.of A)) (j : Fin (N + 1)) : (twistGradedModule φ π).xMul j = twistXMul φ π j := rfl


-- @@ L516-517 verbatim
def twistGradeToObj (π : X ⟶ Spec (.of A)) {d : ℤ} (hd : 0 ≤ d) (f : twistFam π φ) (hf : f ∈ twistGrade φ π d) : twistObj π φ d.toNat ⊤ :=
  ⟨f d, hf.2.2 hd⟩


-- @@ L519-520 verbatim
@[simp] theorem twistGradeToObj_val (π : X ⟶ Spec (.of A)) {d : ℤ} (hd : 0 ≤ d) (f : twistFam π φ) (hf : f ∈ twistGrade φ π d) :
    (twistGradeToObj φ π hd f hf).val = f d := rfl


-- @@ L522-522 verbatim
def objToTwistFam (π : X ⟶ Spec (.of A)) (m : ℕ) (g : twistObj π φ m ⊤) : twistFam π φ := fun d => if d = m then g.val else 0


-- @@ L524-527 verbatim
theorem objToTwistFam_mem (π : X ⟶ Spec (.of A)) (m : ℕ) (g : twistObj π φ m ⊤) : objToTwistFam φ π m g ∈ twistGrade φ π m := by
  refine ⟨fun d' hd' => ?_, fun hd => absurd hd (by omega), fun _ => ?_⟩
  · simp [objToTwistFam, hd']
  · simpa only [objToTwistFam, Int.toNat_natCast, if_true] using g.compat


-- @@ L529-529 verbatim
end AlgebraicGeometry.ProjSpace


-- @@ L531-531 verbatim
namespace AlgebraicGeometry.ProjSpace


-- @@ L533-533 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L535-536 verbatim
variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))


-- @@ L538-540 verbatim
theorem isUnit_restrictFun_frameUnit (i i' : Fin (N + 1)) :
    IsUnit (restrictFun (pullbackOverlap_le_left φ i i') (frameUnit φ i i')) :=
  ⟨⟨_, _, frameUnit_mul_swap φ i i', by rw [mul_comm]; exact frameUnit_mul_swap φ i i'⟩, rfl⟩


-- @@ L542-543 verbatim
theorem pullbackChart_eq_stdCoverPullback_U [IsAffineHom φ] (i : Fin (N + 1)) :
    pullbackChart φ i = (ProjSpace.stdCoverPullback φ).U ⟨i⟩ := rfl


-- @@ L545-546 verbatim
theorem isAffineOpen_pullbackChart [IsAffineHom φ] (i : Fin (N + 1)) : IsAffineOpen (pullbackChart φ i) :=
  ((ProjSpace.stdCover A N).isAffineOpen ⟨i⟩).preimage φ


-- @@ L548-549 verbatim
theorem isAffineOpen_pullbackOverlap [IsAffineHom φ] (i i' : Fin (N + 1)) : IsAffineOpen (pullbackOverlap φ i i') :=
  (Proj.isAffineOpen_basicOpen _ _ (SetLike.mul_mem_graded (X_mem_one A N i) (X_mem_one A N i')) (by norm_num)).preimage φ


-- @@ L551-551 verbatim
end AlgebraicGeometry.ProjSpace


-- @@ L553-553 verbatim
namespace AlgebraicGeometry.ProjSpace


-- @@ L555-555 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L557-558 verbatim
variable {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))


-- @@ L560-583 verbatim
def twistGradeEquiv (π : X ⟶ Spec (.of A)) {d : ℤ} (hd : 0 ≤ d) :
    twistGrade φ π d ≃ₗ[A] twistObj π φ d.toNat ⊤ where
  toFun f := twistGradeToObj φ π hd f.1 f.2
  invFun g := ⟨objToTwistFam φ π d.toNat g, by
    have h := objToTwistFam_mem φ π d.toNat g
    rwa [Int.toNat_of_nonneg hd] at h⟩
  map_add' f g := rfl
  map_smul' r f := by
    refine twistObj.ext (_root_.funext fun i => ?_)
    show (Scheme.TwoAffineOpenCover.algebraOfHom π ((⊤ : X.Opens) ⊓ pullbackChart φ i)).algebraMap r * f.1 d i
      = restrictFun inf_le_left ((Scheme.TwoAffineOpenCover.algebraOfHom π (⊤ : X.Opens)).algebraMap r) * f.1 d i
    rw [restrictFun_algebraMap' π]
  left_inv f := by
    apply Subtype.ext
    funext d'
    show (if d' = ((d.toNat : ℕ) : ℤ) then f.1 d else 0) = f.1 d'
    rw [Int.toNat_of_nonneg hd]
    split_ifs with h
    · rw [h]
    · exact (f.2.1 d' h).symm
  right_inv g := by
    refine twistObj.ext ?_
    show (if d = ((d.toNat : ℕ) : ℤ) then g.val else 0) = g.val
    rw [Int.toNat_of_nonneg hd, if_pos rfl]


-- @@ L585-586 verbatim
@[simp] theorem twistGradeEquiv_apply_val (π : X ⟶ Spec (.of A)) {d : ℤ} (hd : 0 ≤ d) (f : twistGrade φ π d) :
    (twistGradeEquiv φ π hd f).val = f.1 d := rfl


-- @@ L588-588 verbatim
end AlgebraicGeometry.ProjSpace


-- @@ L590-590 verbatim
end
