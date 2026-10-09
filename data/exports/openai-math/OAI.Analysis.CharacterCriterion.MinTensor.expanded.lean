import OAI.Analysis.CharacterCriterion.Definitions
import OAI.Analysis.CharacterCriterion.Absorption


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped TensorProduct

-- @@ L8-8 verbatim
open scoped InnerProductSpace

-- @@ L9-9 verbatim
open scoped BigOperators

-- @@ L10-10 verbatim
open Set Module

-- @@ L11-11 verbatim
open Topology

-- @@ L12-12 verbatim
open NormedSpace

-- @@ L13-13 verbatim
open scoped ComplexOrder

-- @@ L14-14 verbatim
open scoped ComplexOrder

-- @@ L15-15 verbatim
open scoped InnerProductSpace

-- @@ L16-16 verbatim
open scoped InnerProductSpace

-- @@ L17-17 verbatim
open NormedSpace

-- @@ L18-18 verbatim
open scoped TensorProduct InnerProductSpace

-- @@ L19-19 verbatim
open UniformSpace

-- @@ L20-20 verbatim
variable [KirchbergRordam.GenericRW.Size]

-- @@ L21-21 verbatim
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n

-- @@ L22-22 verbatim
variable [KirchbergRordam.GenericRW.PauliData]

-- @@ L23-23 verbatim
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]

-- @@ L24-24 verbatim
open Filter Topology BoundedContinuousFunction

-- @@ L25-25 verbatim
open Filter Topology

-- @@ L26-26 verbatim
open Topology

-- @@ L27-27 verbatim
open scoped TensorProduct CStarAlgebra

-- @@ L28-28 verbatim
open scoped CStarAlgebra ComplexOrder

-- @@ L29-29 verbatim
open NormedSpace

-- @@ L30-30 verbatim
open scoped ComplexOrder

-- @@ L31-31 verbatim
open scoped ComplexOrder

-- @@ L32-32 verbatim
open scoped InnerProductSpace

-- @@ L33-33 verbatim
section

-- @@ L34-34 verbatim
open scoped CStarAlgebra ComplexOrder


-- @@ L36-36 verbatim
open scoped TensorProduct InnerProductSpace

-- @@ L37-37 verbatim
open UniformSpace

-- @@ L38-38 verbatim
namespace KirchbergRordam.Spatial

-- @@ L39-40 verbatim
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]



-- @@ L43-45 verbatim
@[simp] lemma map_coe (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x : H ⊗[ℂ] K) :
    map T S (x : Hilbert H K) = (TensorProduct.mapL T S x : H ⊗[ℂ] K) := by
  simp [map]


-- @@ L47-53 verbatim
@[ext] lemma ext {T S : Hilbert H K →L[ℂ] Hilbert H K}
    (h : ∀ x : H ⊗[ℂ] K, T x = S x) : T = S := by
  apply ContinuousLinearMap.ext
  intro x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq T.continuous S.continuous
  | ih x => exact h x


-- @@ L55-59 verbatim
lemma map_add_left (T U : H →L[ℂ] H) (S : K →L[ℂ] K) :
    map (T + U) S = map T S + map U S := by
  apply ext
  intro x
  simp [TensorProduct.mapL_add_left, ← Completion.coe_add]


-- @@ L61-65 verbatim
lemma map_add_right (T : H →L[ℂ] H) (S U : K →L[ℂ] K) :
    map T (S + U) = map T S + map T U := by
  apply ext
  intro x
  simp [TensorProduct.mapL_add_right, ← Completion.coe_add]


-- @@ L67-71 verbatim
lemma map_smul_left (z : ℂ) (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    map (z • T) S = z • map T S := by
  apply ext
  intro x
  simp [TensorProduct.mapL_smul_left, ← Completion.coe_smul]


-- @@ L73-77 verbatim
lemma map_smul_right (z : ℂ) (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    map T (z • S) = z • map T S := by
  apply ext
  intro x
  simp [TensorProduct.mapL_smul_right, ← Completion.coe_smul]


-- @@ L79-83 verbatim
lemma map_mul (T U : H →L[ℂ] H) (S V : K →L[ℂ] K) :
    map (T * U) (S * V) = map T S * map U V := by
  apply ext
  intro x
  simp only [mul_apply_eq_comp, map_coe, TensorProduct.mapL_mul]


-- @@ L85-89 verbatim
@[simp] lemma map_one : map (1 : H →L[ℂ] H) (1 : K →L[ℂ] K) = 1 := by
  apply ext
  intro x
  simp [show (1 : H →L[ℂ] H) = ContinuousLinearMap.id ℂ H from rfl,
    show (1 : K →L[ℂ] K) = ContinuousLinearMap.id ℂ K from rfl]


-- @@ L91-91 verbatim
variable [CompleteSpace H] [CompleteSpace K]


-- @@ L93-104 verbatim
lemma map_inner_algebraic (T : H →L[ℂ] H) (S : K →L[ℂ] K)
    (x y : H ⊗[ℂ] K) :
    ⟪TensorProduct.mapL (star T) (star S) x, y⟫_ℂ =
      ⟪x, TensorProduct.mapL T S y⟫_ℂ := by
  induction x using TensorProduct.inductionOn with
  | add x z hx hz => simp only [map_add, inner_add_left, hx, hz]
  | tmul a b =>
    induction y using TensorProduct.inductionOn with
    | add y z hy hz => simp only [map_add, inner_add_right, hy, hz]
    | tmul c d =>
      simp only [TensorProduct.mapL_tmul, TensorProduct.inner_tmul,
        ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]


-- @@ L106-110 verbatim
lemma map_inner (T : H →L[ℂ] H) (S : K →L[ℂ] K) (x y : Hilbert H K) :
    ⟪map (star T) (star S) x, y⟫_ℂ = ⟪x, map T S y⟫_ℂ := by
  induction x, y using Completion.induction_on₂ with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x y => simpa using map_inner_algebraic T S x y


-- @@ L112-119 verbatim
lemma map_star (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    map (star T) (star S) = star (map T S) := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [map_inner, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_left]



-- @@ L122-126 verbatim
lemma left_right_commute (T : H →L[ℂ] H) (S : K →L[ℂ] K) :
    Commute (left (K := K) T) (right (H := H) S) := by
  change map T 1 * map 1 S = map 1 S * map T 1
  rw [← map_mul, ← map_mul]
  simp


-- @@ L128-128 verbatim
end KirchbergRordam.Spatial


-- @@ L130-130 verbatim
end

-- @@ L131-131 verbatim
namespace KirchbergRordam.MinTensor

-- @@ L132-132 verbatim
open scoped TensorProduct

-- @@ L133-133 verbatim
universe u

-- @@ L134-134 verbatim
variable (A B : Type u) [CStarAlgebra A] [CStarAlgebra B]



-- @@ L137-139 verbatim
attribute [instance] RepresentationPair.normH RepresentationPair.innerH
  RepresentationPair.completeH RepresentationPair.normK RepresentationPair.innerK
  RepresentationPair.completeK

-- @@ L140-140 verbatim
variable {A B}

-- @@ L141-143 verbatim
lemma RepresentationPair.commute (ρ : RepresentationPair A B) (a : A) (b : B) :
    Commute (ρ.left a) (ρ.right b) :=
  Spatial.left_right_commute _ _



-- @@ L146-146 verbatim
end KirchbergRordam.MinTensor

-- @@ L147-147 verbatim
namespace KirchbergRordam.MinTensor

-- @@ L148-148 verbatim
open scoped TensorProduct

-- @@ L149-149 verbatim
universe u

-- @@ L150-150 verbatim
variable {A B : Type u} [CStarAlgebra A] [CStarAlgebra B]

-- @@ L151-152 verbatim
local instance : Ring (A ⊗[ℂ] B) :=
  _root_.Algebra.TensorProduct.instRing (R := ℂ) (A := A) (B := B)


-- @@ L154-159 verbatim
lemma bounded : BddAbove (Set.range (fun ρ : Option (RepresentationPair A B) =>
    (spatialIndex ρ).toSeminorm)) := by
  rw [Seminorm.bddAbove_range_iff]
  intro x
  obtain ⟨C,hC⟩ := MaxTensor.bounded_at x
  exact ⟨C,by rintro _ ⟨ρ,rfl⟩; exact hC _⟩

-- @@ L160-162 verbatim
lemma seminorm_apply (x : A ⊗[ℂ] B) :
    seminorm x=⨆ ρ : Option (RepresentationPair A B), (spatialIndex ρ).toSeminorm x :=
  Seminorm.iSup_apply bounded

-- @@ L163-168 verbatim
lemma le_seminorm (ρ : Option (RepresentationPair A B)) (x : A ⊗[ℂ] B) :
    (spatialIndex ρ).toSeminorm x ≤ seminorm x := by
  rw [seminorm_apply]
  apply le_ciSup _ ρ
  obtain ⟨C,hC⟩ := MaxTensor.bounded_at x
  exact ⟨C,by rintro _ ⟨ρ,rfl⟩; exact hC _⟩

-- @@ L169-173 verbatim
lemma seminorm_le {x : A ⊗[ℂ] B} {C : ℝ}
    (h : ∀ ρ : Option (RepresentationPair A B), (spatialIndex ρ).toSeminorm x ≤ C) :
    seminorm x ≤ C := by
  rw [seminorm_apply]
  exact ciSup_le h

-- @@ L174-182 verbatim
lemma seminorm_mul_le (x y : A ⊗[ℂ] B) :
    @LE.le ℝ Real.instLE
      (seminorm (@Mul.mul (A ⊗[ℂ] B)
        (_root_.Algebra.TensorProduct.instRing (R := ℂ) (A := A) (B := B)).toMul x y))
      (@Mul.mul ℝ Real.instMul (seminorm x) (seminorm y)) := by
  apply seminorm_le
  intro ρ
  exact ((spatialIndex ρ).mul_le x y).trans (mul_le_mul (le_seminorm ρ x)
    (le_seminorm ρ y) (apply_nonneg _ _) (apply_nonneg _ _))

-- @@ L183-187 verbatim
lemma seminorm_star (x : A ⊗[ℂ] B) : seminorm (star x)=seminorm x := by
  rw [seminorm_apply,seminorm_apply]
  congr 1
  funext ρ
  exact (spatialIndex ρ).star_eq x

-- @@ L188-200 verbatim
lemma seminorm_cstar (x : A ⊗[ℂ] B) :
    seminorm (star x*x)=seminorm x * seminorm x := by
  apply le_antisymm
  · calc
      seminorm (star x * x) ≤ seminorm (star x) * seminorm x := seminorm_mul_le (star x) x
      _ = seminorm x * seminorm x := by rw [seminorm_star]
  · have h : seminorm x ≤ Real.sqrt (seminorm (star x*x)) := by
      apply seminorm_le
      intro ρ
      apply (Real.le_sqrt (apply_nonneg _ _) (apply_nonneg _ _)).mpr
      simpa only [← (spatialIndex ρ).cstar_eq x,pow_two] using le_seminorm ρ (star x*x)
    have := mul_self_le_mul_self (apply_nonneg seminorm x) h
    rwa [Real.mul_self_sqrt (apply_nonneg seminorm _)] at this

-- @@ L201-202 verbatim
lemma seminorm_tmul_le (a : A) (b : B) : seminorm (a ⊗ₜ[ℂ] b) ≤ ‖a‖ * ‖b‖ :=
  seminorm_le fun ρ => (spatialIndex ρ).tmul_le a b

-- @@ L203-204 verbatim
lemma seminorm_le_maximal : (seminorm : Seminorm ℂ (A ⊗[ℂ] B)) ≤ MaxTensor.seminorm :=
  fun x => seminorm_le fun ρ => MaxTensor.le_seminorm (spatialIndex ρ) x



-- @@ L207-214 verbatim
theorem exists_spatial_crossSeminorm (A B : Type u) [CStarAlgebra A] [CStarAlgebra B] :
    ∃ p : MaxTensor.CrossSeminorm A B, p.toSeminorm=seminorm ∧
      p.toSeminorm ≤ MaxTensor.seminorm := by
  exact ⟨{toSeminorm := seminorm
          mul_le := seminorm_mul_le
          star_eq := seminorm_star
          cstar_eq := seminorm_cstar
          tmul_le := seminorm_tmul_le},rfl,seminorm_le_maximal⟩

-- @@ L215-215 verbatim
end KirchbergRordam.MinTensor


-- @@ L217-217 verbatim
namespace KirchbergRordam.MinTensor

-- @@ L218-218 verbatim
open scoped TensorProduct CStarAlgebra

-- @@ L219-219 verbatim
universe u

-- @@ L220-220 verbatim
variable (A B : Type u) [CStarAlgebra A] [CStarAlgebra B]


-- @@ L222-222 verbatim
variable {A B}

-- @@ L223-223 verbatim
instance : StarModule ℂ (Raw A B) := TensorProduct.instStarModule


-- @@ L225-226 verbatim
def rawEquiv : (A ⊗[ℂ] B) ≃⋆ₐ[ℂ] Raw A B :=
  StarAlgEquiv.refl ℂ (A ⊗[ℂ] B)



-- @@ L229-230 verbatim
instance : NormedAlgebra ℂ (Raw A B) where
  norm_smul_le z x := (map_smul_eq_mul seminorm z x).le

-- @@ L231-232 verbatim
instance : NormedStarGroup (Raw A B) where
  norm_star_le x := (seminorm_star x).le

-- @@ L233-233 verbatim
@[simp] lemma norm_raw (x : Raw A B) : ‖x‖ = seminorm x := rfl



-- @@ L236-243 verbatim
instance : CStarRing (Algebra A B) where
  norm_mul_self_le x := by
    induction x using UniformSpace.Completion.induction_on with
    | hp => exact isClosed_le (by fun_prop) (by fun_prop)
    | ih x =>
      simp only [StarCompletion.star_coe, ← UniformSpace.Completion.coe_mul,
        UniformSpace.Completion.norm_coe, norm_raw]
      exact (seminorm_cstar x).ge

-- @@ L244-244 verbatim
instance : CStarAlgebra (Algebra A B) where


-- @@ L246-249 verbatim
def of : Raw A B →⋆ₐ[ℂ] Algebra A B where
  __ := UniformSpace.Completion.coeRingHom
  commutes' _ := rfl
  map_star' x := (StarCompletion.star_coe _ x).symm

-- @@ L250-251 verbatim
@[simp] lemma norm_of (x : Raw A B) : ‖of x‖ = seminorm x :=
  UniformSpace.Completion.norm_coe x

-- @@ L252-253 verbatim
lemma denseRange_of : DenseRange (of (A := A) (B := B)) :=
  UniformSpace.Completion.denseRange_coe


-- @@ L255-257 verbatim
def includeLeft : A →⋆ₐ[ℂ] Algebra A B := of.comp (rawEquiv.toStarAlgHom.comp {
  toAlgHom := _root_.Algebra.TensorProduct.includeLeft
  map_star' a := by simp })


-- @@ L259-261 verbatim
def includeRight : B →⋆ₐ[ℂ] Algebra A B := of.comp (rawEquiv.toStarAlgHom.comp {
  toAlgHom := _root_.Algebra.TensorProduct.includeRight
  map_star' b := by simp })

-- @@ L262-268 verbatim
lemma legs_commute (a : A) (b : B) :
    Commute (includeLeft (B := B) a) (includeRight (A := A) b) := by
  change of (rawEquiv (a ⊗ₜ[ℂ] (1 : B))) * of (rawEquiv ((1 : A) ⊗ₜ[ℂ] b)) =
    of (rawEquiv ((1 : A) ⊗ₜ[ℂ] b)) * of (rawEquiv (a ⊗ₜ[ℂ] (1 : B)))
  rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
  congr 2
  simp only [_root_.Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]



-- @@ L271-275 verbatim
def spatialRaw (ρ : RepresentationPair A B) :
    Raw A B →⋆ₐ[ℂ] (Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K) :=
  (MaxTensor.liftRaw (A := A) (B := B)
    (C := (Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K))
    ρ.left ρ.right ρ.commute).comp rawEquiv.symm.toStarAlgHom

-- @@ L276-278 verbatim
lemma norm_spatialRaw_le (ρ : RepresentationPair A B) (x : Raw A B) :
    ‖spatialRaw ρ x‖ ≤ ‖x‖ :=
  le_seminorm (some ρ) x

-- @@ L279-283 verbatim
lemma lipschitz_spatialRaw (ρ : RepresentationPair A B) : LipschitzWith 1 (spatialRaw ρ) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one, one_mul, dist_eq_norm, ← map_sub]
  exact norm_spatialRaw_le ρ (x-y)

-- @@ L284-285 verbatim
lemma continuous_spatialRaw (ρ : RepresentationPair A B) : Continuous (spatialRaw ρ) :=
  (lipschitz_spatialRaw ρ).continuous

-- @@ L286-306 verbatim
private def extendHom {C : Type*} [NormedRing C] [NormedAlgebra ℂ C]
    [StarRing C] [NormedStarGroup C] [CompleteSpace C]
    (f : Raw A B →⋆ₐ[ℂ] C) (hf : Continuous f) : Algebra A B →⋆ₐ[ℂ] C where
  __ := UniformSpace.Completion.extensionHom f.toRingHom hf
  commutes' z := by
    change UniformSpace.Completion.extensionHom f.toRingHom hf
      (algebraMap ℂ (Raw A B) z) = _
    rw [UniformSpace.Completion.extensionHom_coe]
    exact f.commutes z
  map_star' x := by
    induction x using UniformSpace.Completion.induction_on with
    | hp =>
      exact isClosed_eq
        (UniformSpace.Completion.continuous_extension.comp continuous_star)
        (continuous_star.comp UniformSpace.Completion.continuous_extension)
    | ih x =>
      change UniformSpace.Completion.extensionHom f.toRingHom hf
        (star (x : Algebra A B)) =
        star (UniformSpace.Completion.extensionHom f.toRingHom hf (x : Algebra A B))
      simp only [StarCompletion.star_coe, UniformSpace.Completion.extensionHom_coe]
      exact map_star f x

-- @@ L307-311 verbatim
private lemma extendHom_of {C : Type*} [NormedRing C] [NormedAlgebra ℂ C]
    [StarRing C] [NormedStarGroup C] [CompleteSpace C]
    (f : Raw A B →⋆ₐ[ℂ] C) (hf : Continuous f) (x : Raw A B) :
    extendHom f hf (of x) = f x :=
  UniformSpace.Completion.extensionHom_coe _ hf x

-- @@ L312-316 verbatim
def spatialLift (ρ : RepresentationPair A B) :
    Algebra A B →⋆ₐ[ℂ] (Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K) :=
  extendHom (A := A) (B := B)
    (C := Spatial.Hilbert ρ.H ρ.K →L[ℂ] Spatial.Hilbert ρ.H ρ.K)
    (spatialRaw ρ) (continuous_spatialRaw ρ)



-- @@ L319-320 verbatim
def fromMaximal : MaxTensor.Algebra A B →⋆ₐ[ℂ] Algebra A B :=
  MaxTensor.lift includeLeft includeRight legs_commute

-- @@ L321-333 verbatim
@[simp] lemma fromMaximal_of (x : A ⊗[ℂ] B) :
    fromMaximal (MaxTensor.of (MaxTensor.rawEquiv x)) =
      of (rawEquiv (A := A) (B := B) x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul a b =>
    change MaxTensor.lift includeLeft includeRight legs_commute
      (MaxTensor.of (a ⊗ₜ[ℂ] b)) = _
    rw [MaxTensor.lift_of_tmul]
    change of (rawEquiv (a ⊗ₜ[ℂ] (1 : B))) * of (rawEquiv ((1 : A) ⊗ₜ[ℂ] b)) = of (rawEquiv (a ⊗ₜ[ℂ] b))
    rw [← map_mul, ← map_mul]
    congr 2
    simp only [_root_.Algebra.TensorProduct.tmul_mul_tmul,mul_one,one_mul]

-- @@ L334-337 verbatim
lemma fromMaximal_denseRange : DenseRange (fromMaximal (A := A) (B := B)) :=
  denseRange_of.mono (by
    rintro _ ⟨x, rfl⟩
    exact ⟨MaxTensor.of (MaxTensor.rawEquiv (rawEquiv.symm x)), by simp⟩)

-- @@ L338-338 verbatim
end KirchbergRordam.MinTensor

-- @@ L339-339 verbatim
namespace KirchbergRordam

-- @@ L340-340 verbatim
namespace Spatial

-- @@ L341-341 verbatim
open scoped TensorProduct

-- @@ L342-343 verbatim
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [Nontrivial H] [Nontrivial K]

-- @@ L344-345 verbatim
instance : Nontrivial (Hilbert H K) :=
  (UniformSpace.Completion.coe_injective (H ⊗[ℂ] K)).nontrivial

-- @@ L346-346 verbatim
end Spatial

-- @@ L347-347 verbatim
namespace MinTensor

-- @@ L348-348 verbatim
universe u

-- @@ L349-350 verbatim
variable (A B : Type u) [CStarAlgebra A] [CStarAlgebra B]
  [Nontrivial A] [Nontrivial B]



-- @@ L353-367 verbatim
instance : Nontrivial (Algebra A B) := by
  obtain ⟨π⟩ := exists_irreducible_representation A
  obtain ⟨σ⟩ := exists_irreducible_representation B
  let ρ : RepresentationPair A B := {
    H := π.space
    K := σ.space
    normH := inferInstance
    innerH := inferInstance
    completeH := inferInstance
    normK := inferInstance
    innerK := inferInstance
    completeK := inferInstance
    leftRep := π.representation
    rightRep := σ.representation }
  exact (spatialLift ρ).toRingHom.domain_nontrivial

-- @@ L368-368 verbatim
end MinTensor

-- @@ L369-369 verbatim
end KirchbergRordam

-- @@ L370-370 verbatim
namespace KirchbergRordam.States

-- @@ L371-371 verbatim
open scoped ComplexOrder



-- @@ L374-403 verbatim
theorem exists_norming_state (A : Type*) [CStarAlgebra A] [Nontrivial A]
    [PartialOrder A] [StarOrderedRing A] (a : A) :
    ∃ φ : A →ₚ[ℂ] ℂ, φ 1 = 1 ∧ ‖φ (star a * a)‖ = ‖a‖ ^ 2 := by
  let b := star a * a
  have hb : 0 ≤ b := star_mul_self_nonneg a
  let : IsStarNormal b := (IsSelfAdjoint.of_nonneg hb).isStarNormal
  let S := StarAlgebra.elemental ℂ b
  have hs : (‖b‖ : ℂ) ∈ spectrum ℂ b := by
    exact spectrum.algebraMap_mem ℂ (CStarAlgebra.norm_mem_spectrum_of_nonneg b hb)
  obtain ⟨χ,hχ⟩ := (StarAlgebra.elemental.bijective_characterSpaceToSpectrum b).surjective
    ⟨(‖b‖ : ℂ),hs⟩
  let g : S →ₐ[ℂ] ℂ := WeakDual.CharacterSpace.equivAlgHom χ
  let : StarHomClass (S →ₐ[ℂ] ℂ) S ℂ := AlgHomClass.instStarHomClass
  have hg : ‖g.toContinuousLinearMap‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simpa only [one_mul, AlgHom.coe_toContinuousLinearMap] using NonUnitalStarAlgHom.norm_apply_le g x
  obtain ⟨ψ,hψ,hψnorm⟩ := exists_extension_norm_eq S.toSubalgebra.toSubmodule
    g.toContinuousLinearMap
  have hψ1 : ψ 1 = 1 := by
    exact (hψ (1 : S)).trans (map_one g)
  have hψb : ψ b = (‖b‖ : ℂ) := by
    have hh := congrArg Subtype.val hχ
    exact (hψ ⟨b,StarAlgebra.elemental.self_mem ℂ b⟩).trans hh
  let φ : A →ₚ[ℂ] ℂ := PositiveLinearMap.mk₀ ψ.toLinearMap
    (eval_nonneg ψ (hψnorm.trans_le hg) hψ1)
  refine ⟨φ,hψ1,?_⟩
  change ‖ψ b‖ = ‖a‖ ^ 2
  rw [hψb,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg b)]
  simp only [b,CStarRing.norm_star_mul_self,pow_two]

-- @@ L404-404 verbatim
end KirchbergRordam.States

-- @@ L405-405 verbatim
end


-- @@ L407-407 verbatim
end OAI
