/-
Copyright (c) 2026 Kalle Kytölä. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kalle Kytölä
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import LeanPool.VirasoroProject.ToMathlib.Algebra.Lie.Basic


-- @@ L11-49 verbatim
/-!
# Lie algebra cohomology in degree two (for central extensions)

(*WARNING*: This file needs cleaning up. It was not the main goal and it was the first time I
tried to use multilinear maps in Lean.)

This file defines Lie algebra 2-cocycles and 2-coboundaries and constructs the Lie algebra
cohomology in degree two, with coefficients in a vector space (an Abelian Lie algebra).

## Main definitions

* `LieOneCochain`: The set C¹(𝓰,𝓪) of 1-cochains of a Lie algebra 𝓰 with coefficients in a
  vector space 𝓪.
* `LieTwoCocycle`: The set Z²(𝓰,𝓪) of 2-cocycles of a Lie algebra 𝓰 with coefficients in a
  vector space 𝓪.
* `LieTwoCoboundary`: The subspace B²(𝓰,𝓪) ⊆ Z²(𝓰,𝓪) of 2-coboundaries.
* `LieTwoCohomology`: The 2-cohomology H²(𝓰,𝓪) := Z²(𝓰,𝓪) ⧸ B²(𝓰,𝓪) of a Lie algebra 𝓰 with
  coefficients in a vector space 𝓪.

## Main statements

* `LieTwoCocycle.toLieTwoCohomologyEquiv`: If 𝓰 is abelian, then the canonical projection
  from 2-cocycles to 2-cohomologies is a linear isomorphism.

## Implementation notes

This file needs some clean-up! (But it works for the purposes of concrete calculations of
central extensions etc.)

A reasonable thing to do would be to define Lie algebra cohomology in general degrees. But for
concrete applications, the special case of degree two probably deserves its own API. Once a
general definition is made, the API for the degree 2 case (especially central extensions)
could be refactored.

## Tags

Lie algebra, cohomology

-/


-- @@ L51-51 verbatim
@[expose] public section


-- @@ L53-53 verbatim
namespace VirasoroProject


-- @@ L55-55 verbatim
universe u

-- @@ L56-56 verbatim
variable (𝕜 : Type*) [CommRing 𝕜]

-- @@ L57-57 verbatim
variable (𝓰 𝓪 : Type u) [LieRing 𝓰] [AddCommGroup 𝓪] [LieAlgebra 𝕜 𝓰] [Module 𝕜 𝓪]


-- @@ L59-59 verbatim
section LieOneCochain


-- @@ L61-61 verbatim
/-! ### Lie algebra 1-cochains -/


-- @@ L63-66 verbatim
/-- Lie algebra 1-cochains. -/
@[ext] structure LieOneCochain where
  /-- The underlying linear map of a Lie algebra 1-cochain. -/
  toLinearMap : 𝓰 →ₗ[𝕜] 𝓪


-- @@ L68-69 verbatim
instance : Zero (LieOneCochain 𝕜 𝓰 𝓪) where
  zero := { toLinearMap := 0 }


-- @@ L71-72 verbatim
instance : Add (LieOneCochain 𝕜 𝓰 𝓪) where
  add β β' := { toLinearMap := β.toLinearMap + β'.toLinearMap }


-- @@ L74-75 verbatim
instance : SMul 𝕜 (LieOneCochain 𝕜 𝓰 𝓪) where
  smul c β := { toLinearMap := c • β.toLinearMap }


-- @@ L77-77 verbatim
namespace LieOneCochain


-- @@ L79-80 verbatim
@[simp]
lemma toLinearMap_zero : (0 : LieOneCochain 𝕜 𝓰 𝓪).toLinearMap = 0 := rfl


-- @@ L82-84 verbatim
@[simp]
lemma toLinearMap_add (β β' : LieOneCochain 𝕜 𝓰 𝓪) :
    (β + β').toLinearMap = β.toLinearMap + β'.toLinearMap := rfl


-- @@ L86-88 verbatim
@[simp]
lemma toLinearMap_smul (c : 𝕜) (β : LieOneCochain 𝕜 𝓰 𝓪) :
    (c • β).toLinearMap = c • β.toLinearMap := rfl


-- @@ L90-105 verbatim
instance : AddCommMonoid (LieOneCochain 𝕜 𝓰 𝓪) where
  add_assoc β β' β'' := by ext1
                           simp [add_assoc]
  zero_add β := by ext1; simp
  add_zero β := by ext1; simp
  add_comm β β' := by ext1
                      simp [add_comm]
  nsmul n β := { toLinearMap := n • β.toLinearMap }
  nsmul_zero β := by
    ext1
    change (0 : ℕ) • β.toLinearMap = 0
    exact zero_nsmul β.toLinearMap
  nsmul_succ n β := by
    ext1
    change (n + 1) • β.toLinearMap = n • β.toLinearMap + β.toLinearMap
    exact succ_nsmul β.toLinearMap n


-- @@ L107-115 verbatim
instance : Module 𝕜 (LieOneCochain 𝕜 𝓰 𝓪) where
  one_smul β := by ext1; simp
  mul_smul c c' β := by ext1
                        simpa using mul_smul c c' β.toLinearMap
  smul_zero β := by ext1; simp
  smul_add c β β' := by ext1; simp
  add_smul c c' β := by ext1
                        simpa using add_smul c c' β.toLinearMap
  zero_smul β := by ext1; simp


-- @@ L117-118 verbatim
instance : AddCommGroup (LieOneCochain 𝕜 𝓰 𝓪) :=
  Module.addCommMonoidToAddCommGroup 𝕜


-- @@ L120-120 verbatim
variable {𝕜 𝓰 𝓪}


-- @@ L122-124 verbatim
instance : FunLike (LieOneCochain 𝕜 𝓰 𝓪) 𝓰 𝓪 where
  coe := fun β X ↦ β.toLinearMap X
  coe_injective := fun β β' h ↦ by ext1; exact LinearMap.ext_iff.mpr (congrFun h)


-- @@ L126-128 verbatim
instance : LinearMapClass (LieOneCochain 𝕜 𝓰 𝓪) 𝕜 𝓰 𝓪 where
  map_add β X Y := β.toLinearMap.map_add X Y
  map_smulₛₗ β c X := LinearMap.CompatibleSMul.map_smul β.toLinearMap c X


-- @@ L130-131 verbatim
@[simp]
lemma zero_apply (X : 𝓰) : (0 : LieOneCochain 𝕜 𝓰 𝓪) X = 0 := rfl


-- @@ L133-135 verbatim
@[simp]
lemma add_apply (β β' : LieOneCochain 𝕜 𝓰 𝓪) (X : 𝓰) :
    (β + β') X = β X + β' X := rfl


-- @@ L137-139 verbatim
@[simp]
lemma smul_apply (c : 𝕜) (β : LieOneCochain 𝕜 𝓰 𝓪) (X : 𝓰) :
    (c • β) X = c • β X := rfl


-- @@ L141-145 verbatim
@[simp]
lemma neg_apply (β : LieOneCochain 𝕜 𝓰 𝓪) (X : 𝓰) :
    (-β) X = -β X := by
  change (-1 : 𝕜) • β X = -β X
  simp


-- @@ L147-147 verbatim
end LieOneCochain -- namespace


-- @@ L149-149 verbatim
end LieOneCochain -- section


-- @@ L151-151 verbatim
section LieTwoCocycle


-- @@ L153-153 verbatim
/-! ### Lie algebra 2-cocycles -/


-- @@ L155-160 verbatim
/-- Lie algebra 2-cocycles. -/
@[ext] structure _root_.VirasoroProject.LieTwoCocycle where
  /-- The underlying bilinear map of a Lie algebra 2-cocycle. -/
  toBilin : 𝓰 →ₗ[𝕜] 𝓰 →ₗ[𝕜] 𝓪
  self' : ∀ X, toBilin X X = 0
  leibniz' : ∀ X Y Z, toBilin X ⁅Y, Z⁆ = toBilin ⁅X, Y⁆ Z + toBilin Y ⁅X, Z⁆


-- @@ L162-162 verbatim
namespace LieTwoCocycle


-- @@ L164-169 verbatim
instance : FunLike (LieTwoCocycle 𝕜 𝓰 𝓪) 𝓰 (𝓰 →ₗ[𝕜] 𝓪) where
  coe := fun γ X ↦ LieTwoCocycle.toBilin γ X
  coe_injective := by
    intro γ γ' h
    ext
    exact congrFun (congrArg DFunLike.coe (congrFun h _)) _


-- @@ L171-173 verbatim
instance : LinearMapClass (LieTwoCocycle 𝕜 𝓰 𝓪) 𝕜 𝓰 (𝓰 →ₗ[𝕜] 𝓪) where
  map_add γ X Y := (LieTwoCocycle.toBilin γ).map_add X Y
  map_smulₛₗ γ c X := (LieTwoCocycle.toBilin γ).map_smul c X


-- @@ L175-175 verbatim
variable {𝕜 𝓰 𝓪}

-- @@ L176-176 verbatim
variable (γ : LieTwoCocycle 𝕜 𝓰 𝓪)


-- @@ L178-179 verbatim
@[simp]
lemma _root_.VirasoroProject.LieTwoCocycle.self {X : 𝓰} : γ X X = 0 := γ.self' X


-- @@ L181-182 verbatim
lemma _root_.VirasoroProject.LieTwoCocycle.leibniz
    {X Y Z : 𝓰} : γ X ⁅Y, Z⁆ = γ ⁅X, Y⁆ Z + γ Y ⁅X, Z⁆ := γ.leibniz' X Y Z


-- @@ L184-185 verbatim
lemma _root_.VirasoroProject.LieTwoCocycle.apply_add
    (X₁ X₂ Y : 𝓰) : γ (X₁ + X₂) Y = γ X₁ Y + γ X₂ Y := by simp


-- @@ L187-188 verbatim
lemma _root_.VirasoroProject.LieTwoCocycle.apply_add₂
    (X Y₁ Y₂ : 𝓰) : γ X (Y₁ + Y₂) = γ X Y₁ + γ X Y₂ := by simp


-- @@ L190-191 verbatim
lemma _root_.VirasoroProject.LieTwoCocycle.apply_smul
    (c : 𝕜) (X Y : 𝓰) : γ (c • X) Y = c • γ X Y := by simp


-- @@ L193-194 verbatim
lemma _root_.VirasoroProject.LieTwoCocycle.apply_smul₂
    (c : 𝕜) (X Y : 𝓰) : γ X (c • Y) = c • γ X Y := by simp


-- @@ L196-199 verbatim
lemma _root_.VirasoroProject.LieTwoCocycle.skew (X Y : 𝓰) : -(γ Y X) = γ X Y := by
  have aux : γ (X + Y) X + γ (X + Y) Y = 0 := by
    simpa only [← LieTwoCocycle.apply_add₂] using  LieTwoCocycle.self γ
  simpa [neg_eq_iff_add_eq_zero] using aux


-- @@ L201-202 verbatim
instance : Zero (LieTwoCocycle 𝕜 𝓰 𝓪) where
  zero := { toBilin := 0 , self' := by simp , leibniz' := by simp }


-- @@ L204-210 verbatim
instance : Add (LieTwoCocycle 𝕜 𝓰 𝓪) where
  add γ γ' :=
    { toBilin := γ.toBilin + γ'.toBilin
      self' := fun X ↦ by simp [γ.self', γ'.self']
      leibniz' := fun X Y Z ↦ by
        simp only [LinearMap.add_apply, γ.leibniz' X Y Z, γ'.leibniz' X Y Z]
        ac_rfl }


-- @@ L212-216 verbatim
instance : SMul 𝕜 (LieTwoCocycle 𝕜 𝓰 𝓪) where
  smul c γ :=
    { toBilin := c • γ.toBilin
      self' := fun X ↦ by simp [γ.self']
      leibniz' := fun X Y Z ↦ by simp only [LinearMap.smul_apply, γ.leibniz' X Y Z, smul_add] }


-- @@ L218-220 verbatim
@[simp]
lemma _root_.VirasoroProject.LieTwoCocycle.toBilin_zero
    : (0 : LieTwoCocycle 𝕜 𝓰 𝓪).toBilin = 0 := rfl


-- @@ L222-224 verbatim
@[simp]
lemma _root_.VirasoroProject.LieTwoCocycle.toBilin_add (γ γ' : LieTwoCocycle 𝕜 𝓰 𝓪) :
    (γ + γ').toBilin = γ.toBilin + γ'.toBilin := rfl


-- @@ L226-228 verbatim
@[simp]
lemma _root_.VirasoroProject.LieTwoCocycle.toBilin_smul (c : 𝕜) (γ : LieTwoCocycle 𝕜 𝓰 𝓪) :
    (c • γ).toBilin = c • γ.toBilin := rfl


-- @@ L230-250 verbatim
instance : AddCommMonoid (LieTwoCocycle 𝕜 𝓰 𝓪) where
  add_assoc γ γ' γ'' := by ext1
                           simpa using add_assoc γ.toBilin γ'.toBilin γ''.toBilin
  zero_add γ := by ext1
                   simp [LieTwoCocycle.toBilin_add]
  add_zero γ := by ext1
                   simp [LieTwoCocycle.toBilin_add]
  add_comm γ γ' := by ext1
                      simpa using AddCommMagma.add_comm γ.toBilin γ'.toBilin
  nsmul n γ :=
    { toBilin := n • γ.toBilin
      self' := fun X ↦ by simp [γ.self']
      leibniz' := fun X Y Z ↦ by simp [γ.leibniz' X Y Z, smul_add] }
  nsmul_zero γ := by
    ext1
    change (0 : ℕ) • γ.toBilin = 0
    exact zero_nsmul γ.toBilin
  nsmul_succ n γ := by
    ext1
    change (n + 1) • γ.toBilin = n • γ.toBilin + γ.toBilin
    exact succ_nsmul γ.toBilin n


-- @@ L252-258 verbatim
instance : Module 𝕜 (LieTwoCocycle 𝕜 𝓰 𝓪) where
  one_smul γ := by ext1; simp
  mul_smul c c' γ := by ext1; simpa using mul_smul c c' γ.toBilin
  smul_zero γ := by ext1; simp
  smul_add c γ γ' := by ext1; simp
  add_smul c c' γ := by ext1; simpa using Module.add_smul c c' γ.toBilin
  zero_smul γ := by ext1; simp


-- @@ L260-261 verbatim
instance : AddCommGroup (LieTwoCocycle 𝕜 𝓰 𝓪) :=
  Module.addCommMonoidToAddCommGroup 𝕜


-- @@ L263-264 verbatim
lemma _root_.VirasoroProject.LieTwoCocycle.add_apply (γ₁ γ₂ : LieTwoCocycle 𝕜 𝓰 𝓪) (X Y : 𝓰) :
    (γ₁ + γ₂) X Y = γ₁ X Y + γ₂ X Y := rfl


-- @@ L266-267 verbatim
lemma _root_.VirasoroProject.LieTwoCocycle.smul_apply (c : 𝕜) (γ : LieTwoCocycle 𝕜 𝓰 𝓪) (X Y : 𝓰) :
    (c • γ) X Y = c • γ X Y := rfl


-- @@ L269-273 verbatim
lemma _root_.VirasoroProject.LieTwoCocycle.sub_apply (γ₁ γ₂ : LieTwoCocycle 𝕜 𝓰 𝓪) (X Y : 𝓰) :
    (γ₁ - γ₂) X Y = γ₁ X Y - γ₂ X Y := by
  simp only [sub_eq_add_neg, LieTwoCocycle.add_apply]
  rw [show -γ₂ = (-1 : 𝕜) • γ₂ from rfl, LieTwoCocycle.smul_apply]
  simp


-- @@ L275-276 verbatim
@[simp] lemma _root_.VirasoroProject.LieTwoCocycle.zero_apply
    (X Y : 𝓰) : (0 : LieTwoCocycle 𝕜 𝓰 𝓪) X Y = 0 := rfl


-- @@ L278-279 verbatim
@[simp] lemma _root_.VirasoroProject.LieTwoCocycle.zero_apply'
    (X : 𝓰) : (0 : LieTwoCocycle 𝕜 𝓰 𝓪) X = 0 := rfl


-- @@ L281-281 verbatim
end LieTwoCocycle -- namespace


-- @@ L283-283 verbatim
end LieTwoCocycle -- section


-- @@ L285-285 verbatim
section LieTwoCoboundary


-- @@ L287-287 verbatim
/-! ### Lie algebra 2-coboundaries -/


-- @@ L289-289 verbatim
variable {𝕜 𝓰 𝓪}


-- @@ L291-295 verbatim
/-- A Lie algebra 1-cochain determines a bilinear map via the differential. -/
def _root_.VirasoroProject.LieOneCochain.bdry' (β : LieOneCochain 𝕜 𝓰 𝓪) : 𝓰 →ₗ[𝕜] 𝓰 →ₗ[𝕜] 𝓪 where
  toFun := fun X ↦ β ∘ₗ LieAlgebra.bracketHom 𝕜 𝓰 X
  map_add' X₁ X₂ := by ext; simp
  map_smul' c X := by ext; simp


-- @@ L297-302 verbatim
/-- A Lie algebra 1-cochain linearly determines a bilinear map via the differential. -/
def _root_.VirasoroProject.LieOneCochain.bdryHom'
    : LieOneCochain 𝕜 𝓰 𝓪 →ₗ[𝕜] 𝓰 →ₗ[𝕜] 𝓰 →ₗ[𝕜] 𝓪 where
  toFun := fun β ↦ LieOneCochain.bdry' β
  map_add' β₁ β₂ := by ext X Y; rfl
  map_smul' c Z := by ext X Y; rfl


-- @@ L304-308 verbatim
/-- The `∂` of a Lie algebra 1-cochain as a Lie algebra 2-cocycle. -/
def _root_.VirasoroProject.LieOneCochain.bdry (β : LieOneCochain 𝕜 𝓰 𝓪) : LieTwoCocycle 𝕜 𝓰 𝓪 where
  toBilin := LieOneCochain.bdryHom' β
  self' X := by simp [LieOneCochain.bdryHom', LieOneCochain.bdry']
  leibniz' X Y Z := by simp [LieOneCochain.bdryHom', LieOneCochain.bdry']


-- @@ L310-310 verbatim
variable (𝕜 𝓰 𝓪)


-- @@ L312-317 verbatim
/-- The `∂` as a linear map from Lie algebra 1-cochains to Lie algebra 2-cocycles. -/
def _root_.VirasoroProject.LieOneCochainBdryHom
    : LieOneCochain 𝕜 𝓰 𝓪 →ₗ[𝕜] LieTwoCocycle 𝕜 𝓰 𝓪 where
  toFun β := β.bdry
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- @@ L319-322 verbatim
@[simp] lemma _root_.VirasoroProject.LieOneCochain.neg_bdry
    (β : LieOneCochain 𝕜 𝓰 𝓪) : (-β).bdry = -β.bdry := by
  change LieOneCochainBdryHom 𝕜 𝓰 𝓪 (-β) = -LieOneCochainBdryHom 𝕜 𝓰 𝓪 β
  simp


-- @@ L324-325 verbatim
lemma _root_.VirasoroProject.LieOneCochain.bdry_apply (β : LieOneCochain 𝕜 𝓰 𝓪) (X Y : 𝓰) :
    β.bdry X Y = β (⁅X, Y⁆) := rfl


-- @@ L327-328 verbatim
/-- Lie algebra 2-coboundaries as a vector space. -/
abbrev _root_.VirasoroProject.LieTwoCoboundary := LinearMap.range (LieOneCochainBdryHom 𝕜 𝓰 𝓪)


-- @@ L330-330 verbatim
end LieTwoCoboundary -- section


-- @@ L332-332 verbatim
section LieTwoCohomology


-- @@ L334-334 verbatim
/-! ### Lie algebra 2-cohomology -/


-- @@ L336-337 verbatim
/-- The 2-cohomology `H²(𝓰,𝓪)` of a Lie algebra `𝓰` with coefficients in `𝓪`. -/
def _root_.VirasoroProject.LieTwoCohomology := LieTwoCocycle 𝕜 𝓰 𝓪 ⧸ LieTwoCoboundary 𝕜 𝓰 𝓪


-- @@ L339-339 verbatim
namespace LieTwoCohomology


-- @@ L341-343 verbatim
/-- The 2-cohomology `H²(𝓰,𝓪)` is an additive commutative group. -/
instance : AddCommGroup (LieTwoCohomology 𝕜 𝓰 𝓪) :=
  Submodule.Quotient.addCommGroup (LieTwoCoboundary 𝕜 𝓰 𝓪)


-- @@ L345-347 verbatim
/-- The 2-cohomology `H²(𝓰,𝓪)` is a module over the scalar ring `𝕜`. -/
instance : Module 𝕜 (LieTwoCohomology 𝕜 𝓰 𝓪) :=
  Submodule.Quotient.module' _


-- @@ L349-349 verbatim
end LieTwoCohomology -- namespace


-- @@ L351-351 verbatim
namespace LieTwoCocycle


-- @@ L353-357 verbatim
/-- The linear map from 2-cocycles to 2-cohomologies of a Lie algebra `𝓰` with coefficients
in `𝓪`. -/
def _root_.VirasoroProject.LieTwoCocycle.toLieTwoCohomology
    : LieTwoCocycle 𝕜 𝓰 𝓪 →ₗ[𝕜] LieTwoCohomology 𝕜 𝓰 𝓪 :=
  (LieTwoCoboundary 𝕜 𝓰 𝓪).mkQ


-- @@ L359-361 verbatim
lemma _root_.VirasoroProject.LieTwoCocycle.range_toLieTwoCohomology_eq_top :
    LinearMap.range (toLieTwoCohomology 𝕜 𝓰 𝓪) = ⊤ :=
  Submodule.range_mkQ ..


-- @@ L363-363 verbatim
variable {𝕜 𝓰 𝓪}


-- @@ L365-369 verbatim
/-- The projection to 2-cohomologies from 2-cocycles of a Lie algebra `𝓰` with coefficients
in `𝓪`. (This definition is to enable dot notation, while the linear map version doesn't.) -/
def _root_.VirasoroProject.LieTwoCocycle.cohomologyClass
    (γ : LieTwoCocycle 𝕜 𝓰 𝓪) : LieTwoCohomology 𝕜 𝓰 𝓪 :=
  LieTwoCocycle.toLieTwoCohomology _ _ _ γ


-- @@ L371-376 verbatim
/-- Adding a coboundary does not change the cohomology class. -/
lemma _root_.VirasoroProject.LieTwoCocycle.cohomologyClass_add_bdry
    (γ : LieTwoCocycle 𝕜 𝓰 𝓪) (β : LieOneCochain 𝕜 𝓰 𝓪) :
    (γ + β.bdry).cohomologyClass = γ.cohomologyClass := by
  simp only [cohomologyClass, map_add, add_eq_left]
  exact (Submodule.Quotient.mk_eq_zero _).mpr <| LinearMap.mem_range.mpr ⟨β, rfl⟩


-- @@ L378-384 verbatim
/-- A cocycle representing a trivial cohomology class is a coboundary. -/
lemma _root_.VirasoroProject.LieTwoCocycle.exists_eq_bdry
    (γ : LieTwoCocycle 𝕜 𝓰 𝓪) (hγ : γ.cohomologyClass = 0) :
    ∃ β : LieOneCochain 𝕜 𝓰 𝓪, γ = β.bdry := by
  rw [LieTwoCocycle.cohomologyClass, LieTwoCocycle.toLieTwoCohomology] at hγ
  obtain ⟨β, hβ⟩ := LinearMap.mem_range.mp ((Submodule.Quotient.mk_eq_zero _).mp hγ)
  exact ⟨β, hβ.symm⟩


-- @@ L386-386 verbatim
end LieTwoCocycle -- namespace


-- @@ L388-388 verbatim
end LieTwoCohomology -- section


-- @@ L390-390 verbatim
section IsLieAbelian


-- @@ L392-392 verbatim
variable [IsLieAbelian 𝓰]


-- @@ L394-394 verbatim
variable {𝕜 𝓰 𝓪}


-- @@ L396-400 verbatim
/-- For abelian Lie algebras, a 2-coboundary is necessarily zero. -/
lemma _root_.VirasoroProject.LieOneCochain.bdry_apply_eq_zero_of_isLieAbelian
    (β : LieOneCochain 𝕜 𝓰 𝓪) (X Y : 𝓰) :
    β.bdry X Y = 0 := by
  simpa [LieOneCochain.bdry_apply] using congrArg β (trivial_lie_zero 𝓰 𝓰 X Y)


-- @@ L402-402 verbatim
variable (𝕜 𝓰 𝓪)


-- @@ L404-409 verbatim
/-- For abelian Lie algebras, the space of 2-coboundaries is the zero vector space. -/
lemma _root_.VirasoroProject.LieTwoCoboundary.eq_bot_of_isLieAbelian :
    LieTwoCoboundary 𝕜 𝓰 𝓪 = ⊥ := by
  refine LinearMap.range_eq_bot.mpr ?_
  ext β X Y
  exact β.bdry_apply_eq_zero_of_isLieAbelian X Y


-- @@ L411-417 verbatim
/-- For abelian Lie algebras, the map from 2-cocycles to their cohomology classes has
trivial kernel. -/
lemma _root_.VirasoroProject.LieTwoCocycle.ker_toLieTwoCohomology_eq_bot_of_isLieAbelian :
    LinearMap.ker (LieTwoCocycle.toLieTwoCohomology 𝕜 𝓰 𝓪) = ⊥ := by
  rw [LieTwoCocycle.toLieTwoCohomology]
  exact (LieTwoCoboundary 𝕜 𝓰 𝓪).ker_mkQ.trans
    (LieTwoCoboundary.eq_bot_of_isLieAbelian 𝕜 𝓰 𝓪)


-- @@ L419-425 verbatim
/-- For abelian Lie algebras, the map from 2-cocycles to their cohomology classes is a linear
equivalence. -/
noncomputable def _root_.VirasoroProject.LieTwoCocycle.toLieTwoCohomologyEquiv :
    LieTwoCocycle 𝕜 𝓰 𝓪 ≃ₗ[𝕜] LieTwoCohomology 𝕜 𝓰 𝓪 :=
  LinearEquiv.ofBijective (LieTwoCocycle.toLieTwoCohomology 𝕜 𝓰 𝓪)
    ⟨LinearMap.ker_eq_bot.mp <| LieTwoCocycle.ker_toLieTwoCohomology_eq_bot_of_isLieAbelian ..,
     LinearMap.range_eq_top.mp <| LieTwoCocycle.range_toLieTwoCohomology_eq_top ..⟩


-- @@ L427-429 verbatim
lemma _root_.VirasoroProject.LieTwoCocycle.toLieTwoCohomologyEquiv_toLinearMap :
    (LieTwoCocycle.toLieTwoCohomologyEquiv 𝕜 𝓰 𝓪).toLinearMap =
      LieTwoCocycle.toLieTwoCohomology 𝕜 𝓰 𝓪 := rfl


-- @@ L431-431 verbatim
end IsLieAbelian --section


-- @@ L433-433 verbatim
end VirasoroProject -- namespace
