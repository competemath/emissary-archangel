import OAI.Analysis.CharacterCriterion.GeneralSystem


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
variable [KirchbergRordam.GenericRW.Size]

-- @@ L20-20 verbatim
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n

-- @@ L21-21 verbatim
variable [KirchbergRordam.GenericRW.PauliData]

-- @@ L22-22 verbatim
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]

-- @@ L23-23 verbatim
open Filter Topology BoundedContinuousFunction

-- @@ L24-24 verbatim
open Filter Topology

-- @@ L25-25 verbatim
open Topology

-- @@ L26-26 verbatim
open scoped TensorProduct CStarAlgebra

-- @@ L27-27 verbatim
open scoped CStarAlgebra ComplexOrder

-- @@ L28-28 verbatim
open NormedSpace

-- @@ L29-29 verbatim
open scoped ComplexOrder

-- @@ L30-30 verbatim
open scoped ComplexOrder

-- @@ L31-31 verbatim
open scoped InnerProductSpace

-- @@ L32-32 verbatim
open scoped CStarAlgebra ComplexOrder

-- @@ L33-33 verbatim
open scoped TensorProduct InnerProductSpace

-- @@ L34-34 verbatim
open UniformSpace


-- @@ L36-36 verbatim
namespace KirchbergRordam.Spatial

-- @@ L37-37 verbatim
open scoped TensorProduct

-- @@ L38-38 verbatim
open UniformSpace

-- @@ L39-40 verbatim
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

-- @@ L41-42 verbatim
def flipL : Hilbert H K →L[ℂ] Hilbert K H :=
  (TensorProduct.commIsometry ℂ H K).toContinuousLinearEquiv.toContinuousLinearMap.completion

-- @@ L43-45 verbatim
@[simp] lemma flipL_coe (x : H ⊗[ℂ] K) :
    flipL (x : Hilbert H K) = (TensorProduct.comm ℂ H K x : Hilbert K H) := by
  simp [flipL]

-- @@ L46-49 verbatim
lemma flipL_flipL (x : Hilbert H K) : flipL (flipL x) = x := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (flipL.continuous.comp flipL.continuous) continuous_id
  | ih x => simp

-- @@ L50-53 verbatim
lemma norm_flipL (x : Hilbert H K) : ‖flipL x‖ = ‖x‖ := by
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (continuous_norm.comp flipL.continuous) continuous_norm
  | ih x => simp [TensorProduct.norm_comm]

-- @@ L54-59 verbatim
def flip : Hilbert H K ≃ₗᵢ[ℂ] Hilbert K H where
  __ := flipL.toLinearMap
  invFun := flipL
  left_inv := flipL_flipL
  right_inv := flipL_flipL
  norm_map' := norm_flipL

-- @@ L60-61 verbatim
@[simp] lemma flip_coe (x : H ⊗[ℂ] K) :
    flip (x : Hilbert H K) = (TensorProduct.comm ℂ H K x : Hilbert K H) := flipL_coe x

-- @@ L62-62 verbatim
@[simp] lemma flip_symm : (flip (H:=H) (K:=K)).symm = flip := rfl

-- @@ L63-72 verbatim
lemma flip_map (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    flip.conjStarAlgEquiv (map T S) = map S T := by
  apply ext
  intro x
  simp only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply, flip_symm,
    flip_coe, map_coe]
  congr 1
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul k h => simp

-- @@ L73-77 verbatim
lemma norm_flip_conjugate (T : Hilbert H K →L[ℂ] Hilbert H K) :
    ‖(flip (H:=H) (K:=K)).conjStarAlgEquiv T‖=‖T‖ := by
  rw [LinearIsometryEquiv.conjStarAlgEquiv_apply]
  rw [ContinuousLinearMap.opNorm_linearIsometryEquiv_comp,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]


-- @@ L79-79 verbatim
end KirchbergRordam.Spatial

-- @@ L80-80 verbatim
namespace KirchbergRordam.MinTensor

-- @@ L81-81 verbatim
open scoped TensorProduct CStarAlgebra

-- @@ L82-82 verbatim
universe u

-- @@ L83-83 verbatim
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]

-- @@ L84-88 verbatim
def algebraicFlip : (A ⊗[ℂ] B) ≃⋆ₐ[ℂ] (B ⊗[ℂ] A) :=
  StarAlgEquiv.ofAlgEquiv (_root_.Algebra.TensorProduct.comm ℂ A B) fun x => by
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, star_add, hx, hy]
    | tmul a b => simp

-- @@ L89-89 verbatim
@[simp] lemma algebraicFlip_tmul (a : A) (b : B) : algebraicFlip (a ⊗ₜ[ℂ] b) = b ⊗ₜ[ℂ] a := rfl

-- @@ L90-91 verbatim
@[simp] lemma algebraicFlip_flip (x : A ⊗[ℂ] B) : algebraicFlip (algebraicFlip x) = x := by
  exact (_root_.Algebra.TensorProduct.comm ℂ A B).symm_apply_apply x


-- @@ L93-95 verbatim
def RepresentationPair.rawMap (ρ : RepresentationPair A B) :
    (A ⊗[ℂ] B) →⋆ₐ[ℂ] (Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K) :=
  MaxTensor.liftRaw (C := (Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K)) ρ.left ρ.right ρ.commute

-- @@ L96-97 verbatim
@[simp] lemma RepresentationPair.rawMap_tmul (ρ : RepresentationPair A B) (a : A) (b : B) :
    ρ.rawMap (a ⊗ₜ[ℂ] b) = ρ.left a * ρ.right b := rfl

-- @@ L98-108 verbatim
def RepresentationPair.swap (ρ : RepresentationPair A B) : RepresentationPair B A where
  H := ρ.K
  K := ρ.H
  normH := inferInstance
  innerH := inferInstance
  completeH := inferInstance
  normK := inferInstance
  innerK := inferInstance
  completeK := inferInstance
  leftRep := ρ.rightRep
  rightRep := ρ.leftRep

-- @@ L109-123 verbatim
lemma liftRaw_conjugate_swap {C E : Type*} [CStarAlgebra C] [CStarAlgebra E]
    (φ : A →⋆ₐ[ℂ] C) (ψ : B →⋆ₐ[ℂ] C) (h : ∀ a b, Commute (φ a) (ψ b))
    (φ' : B →⋆ₐ[ℂ] E) (ψ' : A →⋆ₐ[ℂ] E) (h' : ∀ b a, Commute (φ' b) (ψ' a))
    (e : C ≃⋆ₐ[ℂ] E) (he₁ : ∀ b, φ' b=e (ψ b)) (he₂ : ∀ a, ψ' a=e (φ a))
    (x : A ⊗[ℂ] B) :
    MaxTensor.liftRaw φ' ψ' h' (algebraicFlip x) = e (MaxTensor.liftRaw φ ψ h x) := by
  change MaxTensor.liftRaw φ' ψ' h' (MaxTensor.rawEquiv (algebraicFlip x)) =
    e (MaxTensor.liftRaw φ ψ h (MaxTensor.rawEquiv x))
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul a b =>
    change MaxTensor.liftRaw φ' ψ' h' (algebraicFlip (a ⊗ₜ[ℂ] b)) =
      e (MaxTensor.liftRaw φ ψ h (a ⊗ₜ[ℂ] b))
    simp only [algebraicFlip_tmul,MaxTensor.liftRaw_tmul,he₁,he₂,←map_mul]
    exact congrArg e (h a b).symm.eq

-- @@ L124-126 verbatim
lemma swap_left_flip (ρ : RepresentationPair A B) (b : B) :
    ρ.swap.left b=(Spatial.flip (H:=ρ.H) (K:=ρ.K)).conjStarAlgEquiv (ρ.right b) := by
  exact (Spatial.flip_map 1 (ρ.rightRep b)).symm

-- @@ L127-129 verbatim
lemma swap_right_flip (ρ : RepresentationPair A B) (a : A) :
    ρ.swap.right a=(Spatial.flip (H:=ρ.H) (K:=ρ.K)).conjStarAlgEquiv (ρ.left a) := by
  exact (Spatial.flip_map (ρ.leftRep a) 1).symm

-- @@ L130-146 verbatim
lemma liftRaw_swap (ρ : RepresentationPair A B) (x : A ⊗[ℂ] B) :
    ρ.swap.rawMap (algebraicFlip x) =
    (Spatial.flip (H:=ρ.H) (K:=ρ.K)).conjStarAlgEquiv (ρ.rawMap x) := by
  let e := (Spatial.flip (H:=ρ.H) (K:=ρ.K)).conjStarAlgEquiv
  have he0 : e 0=0 := map_zero (M:=Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K)
    (N:=Spatial.Hilbert ρ.K ρ.H →L[ℂ] Spatial.Hilbert ρ.K ρ.H) e
  have headd (s t : Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K) : e (s+t)=e s+e t :=
    e.toStarRingEquiv.toRingEquiv.map_add' s t
  have hemul (s t : Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K) : e (s*t)=e s*e t :=
    e.toStarRingEquiv.toRingEquiv.map_mul' s t
  change ρ.swap.rawMap (algebraicFlip x) = e (ρ.rawMap x)
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add,map_add,map_add,headd,hx,hy]; rfl
  | tmul a b =>
    simp only [algebraicFlip_tmul,RepresentationPair.rawMap_tmul,swap_left_flip,swap_right_flip]
    change e (ρ.right b)*e (ρ.left a)=e (ρ.left a*ρ.right b)
    rw [←hemul,(ρ.commute a b).symm.eq]


-- @@ L148-149 verbatim
lemma crossSeminorm_apply (ρ : RepresentationPair A B) (x : A ⊗[ℂ] B) :
    ρ.crossSeminorm.toSeminorm x = ‖ρ.rawMap x‖ := rfl

-- @@ L150-153 verbatim
lemma crossSeminorm_swap (ρ : RepresentationPair A B) (x : A ⊗[ℂ] B) :
    ρ.swap.crossSeminorm.toSeminorm (algebraicFlip x) = ρ.crossSeminorm.toSeminorm x := by
  rw [crossSeminorm_apply,crossSeminorm_apply,liftRaw_swap]
  exact Spatial.norm_flip_conjugate _


-- @@ L155-161 verbatim
lemma seminorm_algebraicFlip_le (x : A ⊗[ℂ] B) : seminorm (algebraicFlip x) ≤ seminorm x := by
  apply seminorm_le
  rintro (_|ρ)
  · exact apply_nonneg _ _
  · have h := crossSeminorm_swap ρ (algebraicFlip x)
    rw [algebraicFlip_flip] at h
    exact h.symm.le.trans (le_seminorm (some ρ.swap) x)

-- @@ L162-164 verbatim
lemma seminorm_algebraicFlip (x : A ⊗[ℂ] B) : seminorm (algebraicFlip x) = seminorm x :=
  le_antisymm (seminorm_algebraicFlip_le x)
    (by simpa only [algebraicFlip_flip] using seminorm_algebraicFlip_le (algebraicFlip x))

-- @@ L165-166 verbatim
def flipRaw : Raw A B →⋆ₐ[ℂ] Algebra B A :=
  of.comp ((rawEquiv.symm.trans (algebraicFlip.trans rawEquiv)).toStarAlgHom)

-- @@ L167-170 verbatim
lemma norm_flipRaw (x : Raw A B) : ‖flipRaw x‖ = ‖x‖ := by
  change ‖of (rawEquiv (algebraicFlip (rawEquiv.symm x)))‖=‖x‖
  rw [norm_of]
  exact seminorm_algebraicFlip x

-- @@ L171-175 verbatim
lemma continuous_flipRaw : Continuous (flipRaw (A:=A) (B:=B)) := by
  apply LipschitzWith.continuous (K:=1)
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub, norm_flipRaw, le_refl]

-- @@ L176-194 verbatim
def flipHom : Algebra A B →⋆ₐ[ℂ] Algebra B A where
  __ := UniformSpace.Completion.extensionHom (flipRaw (A:=A) (B:=B)).toRingHom continuous_flipRaw
  commutes' z := by
    change UniformSpace.Completion.extensionHom (flipRaw (A:=A) (B:=B)).toRingHom continuous_flipRaw
      ((algebraMap ℂ (Raw A B) z) : Algebra A B) = _
    rw [UniformSpace.Completion.extensionHom_coe]
    exact flipRaw.commutes z
  map_star' x := by
    induction x using UniformSpace.Completion.induction_on with
    | hp =>
      exact isClosed_eq
        (UniformSpace.Completion.continuous_extension.comp continuous_star)
        (continuous_star.comp UniformSpace.Completion.continuous_extension)
    | ih x =>
      change UniformSpace.Completion.extensionHom (flipRaw (A:=A) (B:=B)).toRingHom continuous_flipRaw
        (star (x : Algebra A B)) =
        star (UniformSpace.Completion.extensionHom (flipRaw (A:=A) (B:=B)).toRingHom continuous_flipRaw (x : Algebra A B))
      simp only [StarCompletion.star_coe, UniformSpace.Completion.extensionHom_coe]
      exact map_star flipRaw x

-- @@ L195-196 verbatim
@[simp] lemma flipHom_of (x : Raw A B) : flipHom (of x) = flipRaw x :=
  UniformSpace.Completion.extensionHom_coe _ continuous_flipRaw x

-- @@ L197-200 verbatim
@[simp] lemma flipHom_includeLeft (a : A) : flipHom (includeLeft (B:=B) a) = includeRight a := by
  change flipHom (of (rawEquiv (a ⊗ₜ[ℂ] (1 : B)))) = _
  rw [flipHom_of]
  rfl

-- @@ L201-204 verbatim
@[simp] lemma flipHom_includeRight (b : B) : flipHom (includeRight (A:=A) b) = includeLeft b := by
  change flipHom (of (rawEquiv ((1 : A) ⊗ₜ[ℂ] b))) = _
  rw [flipHom_of]
  rfl

-- @@ L205-214 verbatim
lemma flipHom_flipHom (x : Algebra A B) : flipHom (flipHom x) = x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq ((map_continuous flipHom).comp (map_continuous flipHom)) continuous_id
  | ih y =>
    change flipHom (flipHom (of y))=of y
    rw [flipHom_of]
    change flipHom (of (rawEquiv (algebraicFlip (rawEquiv.symm y)))) = of y
    rw [flipHom_of]
    change of (rawEquiv (algebraicFlip (algebraicFlip (rawEquiv.symm y))))=of y
    simp only [algebraicFlip_flip, StarAlgEquiv.apply_symm_apply]



-- @@ L217-219 verbatim
def flip : Algebra A B ≃⋆ₐ[ℂ] Algebra B A :=
  StarAlgEquiv.ofStarAlgHom flipHom flipHom
    (by ext x; exact flipHom_flipHom x) (by ext x; exact flipHom_flipHom x)

-- @@ L220-221 verbatim
@[simp] lemma flip_includeLeft (a : A) : flip (includeLeft (B:=B) a)=includeRight a :=
  flipHom_includeLeft a

-- @@ L222-223 verbatim
@[simp] lemma flip_includeRight (b : B) : flip (includeRight (A:=A) b)=includeLeft b :=
  flipHom_includeRight b

-- @@ L224-224 verbatim
end KirchbergRordam.MinTensor

-- @@ L225-225 verbatim
end


-- @@ L227-227 verbatim
end OAI
