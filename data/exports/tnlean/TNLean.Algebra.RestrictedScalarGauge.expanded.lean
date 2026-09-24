/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import TNLean.Algebra.LSymbol


-- @@ L8-25 verbatim
/-!
# Restricted scalar gauges

This file isolates the tensor-independent part of the standing gauge convention
in arXiv:2502.20257, lines 2050--2054. The fusion scalar `β` is one on both
identity axes and on every inverse pair `(g, g⁻¹)`, while the action scalar `γ`
is one at the identity. These conditions are closed under pointwise identity,
multiplication, and inversion.

No fusion tensor, action tensor, dagger gauge, or representation-level gauge is
constructed here.

## Main definitions

* `ScalarCocycle.IsInverseNormalized`: the restricted condition on `β`.
* `RestrictedFusionGauge`: an inverse-normalized fusion gauge.
* `RestrictedScalarGauge`: a bundled restricted choice `(β, γ)`.
-/


-- @@ L27-27 verbatim
namespace TNLean.Algebra


-- @@ L29-29 verbatim
variable {G X : Type*} [Group G] [MulAction G X]


-- @@ L31-31 verbatim
namespace ScalarCocycle


-- @@ L33-37 verbatim
/-- A fusion scalar `β` satisfies the restricted standing convention when it is
normalized and `β(g,g⁻¹) = 1` for every `g`. This is arXiv:2502.20257, lines
2050--2053. -/
def IsInverseNormalized (β : ScalarCocycle G) : Prop :=
  β.IsNormalized ∧ ∀ g, β g g⁻¹ = 1


-- @@ L39-42 verbatim
/-- The identity fusion scalar is inverse-normalized. -/
@[simp]
theorem isInverseNormalized_one : IsInverseNormalized (1 : ScalarCocycle G) := by
  exact ⟨⟨fun _ => rfl, fun _ => rfl⟩, fun _ => rfl⟩


-- @@ L44-50 verbatim
/-- Pointwise multiplication preserves the restricted fusion convention. -/
theorem IsInverseNormalized.mul {β₁ β₂ : ScalarCocycle G}
    (hβ₁ : β₁.IsInverseNormalized) (hβ₂ : β₂.IsInverseNormalized) :
    (β₁ * β₂).IsInverseNormalized := by
  refine ⟨⟨fun g => by simp [hβ₁.1.1 g, hβ₂.1.1 g],
    fun g => by simp [hβ₁.1.2 g, hβ₂.1.2 g]⟩, fun g => ?_⟩
  simp [hβ₁.2 g, hβ₂.2 g]


-- @@ L52-56 verbatim
/-- Pointwise inversion preserves the restricted fusion convention. -/
theorem IsInverseNormalized.inv {β : ScalarCocycle G}
    (hβ : β.IsInverseNormalized) : β⁻¹.IsInverseNormalized := by
  refine ⟨⟨fun g => by simp [hβ.1.1 g], fun g => by simp [hβ.1.2 g]⟩, fun g => ?_⟩
  simp [hβ.2 g]


-- @@ L58-58 verbatim
end ScalarCocycle


-- @@ L60-63 verbatim
/-- An inverse-normalized fusion scalar `β` satisfying the standing convention
of arXiv:2502.20257, lines 2050--2053. -/
@[ext]
structure RestrictedFusionGauge (G : Type*) [Group G] where
  
-- @@ L64-65 verbatim
/-- The scalar fusion gauge `β`. -/
  beta : ScalarCocycle G
  
-- @@ L66-67 verbatim
/-- Normalization on the identity axes and inverse pairs. -/
  isInverseNormalized : beta.IsInverseNormalized


-- @@ L69-69 verbatim
namespace RestrictedFusionGauge


-- @@ L71-74 verbatim
/-- The identity restricted fusion gauge. -/
def one : RestrictedFusionGauge G where
  beta := 1
  isInverseNormalized := ScalarCocycle.isInverseNormalized_one


-- @@ L76-79 verbatim
/-- Pointwise multiplication of restricted fusion gauges. -/
def mul (β₁ β₂ : RestrictedFusionGauge G) : RestrictedFusionGauge G where
  beta := β₁.beta * β₂.beta
  isInverseNormalized := β₁.isInverseNormalized.mul β₂.isInverseNormalized


-- @@ L81-84 verbatim
/-- Pointwise inversion of a restricted fusion gauge. -/
def inv (β : RestrictedFusionGauge G) : RestrictedFusionGauge G where
  beta := β.beta⁻¹
  isInverseNormalized := β.isInverseNormalized.inv


-- @@ L86-86 verbatim
instance : One (RestrictedFusionGauge G) := ⟨one⟩

-- @@ L87-87 verbatim
instance : Mul (RestrictedFusionGauge G) := ⟨mul⟩

-- @@ L88-88 verbatim
instance : Inv (RestrictedFusionGauge G) := ⟨inv⟩


-- @@ L90-106 verbatim
instance : Group (RestrictedFusionGauge G) where
  mul_assoc β₁ β₂ β₃ := by
    apply RestrictedFusionGauge.ext
    funext g h
    exact mul_assoc (β₁.beta g h) (β₂.beta g h) (β₃.beta g h)
  one_mul β := by
    apply RestrictedFusionGauge.ext
    funext g h
    exact one_mul (β.beta g h)
  mul_one β := by
    apply RestrictedFusionGauge.ext
    funext g h
    exact mul_one (β.beta g h)
  inv_mul_cancel β := by
    apply RestrictedFusionGauge.ext
    funext g h
    exact inv_mul_cancel (β.beta g h)


-- @@ L108-112 verbatim
/-- The identity restricted fusion gauge acts trivially on scalar 3-cochains. -/
@[simp]
theorem fusionGauge_one (ω : ScalarThreeCochain G) :
    ScalarThreeCochain.fusionGauge (1 : RestrictedFusionGauge G).beta ω = ω :=
  ScalarThreeCochain.fusionGauge_one ω


-- @@ L114-118 verbatim
/-- A restricted fusion gauge preserves normalization of scalar 3-cochains. -/
theorem isNormalized_fusionGauge (β : RestrictedFusionGauge G)
    {ω : ScalarThreeCochain G} (hω : ω.IsNormalized) :
    (ScalarThreeCochain.fusionGauge β.beta ω).IsNormalized :=
  hω.fusionGauge β.isInverseNormalized.1


-- @@ L120-124 verbatim
/-- A restricted fusion gauge preserves the scalar 3-cocycle equation. -/
theorem isCocycle_fusionGauge (β : RestrictedFusionGauge G)
    {ω : ScalarThreeCochain G} (hω : ω.IsCocycle) :
    (ScalarThreeCochain.fusionGauge β.beta ω).IsCocycle :=
  hω.fusionGauge β.beta


-- @@ L126-133 verbatim
/-- Successive restricted fusion gauges compose according to
`ScalarThreeCochain.fusionGauge_comp`. -/
theorem fusionGauge_mul (β₁ β₂ : RestrictedFusionGauge G)
    (ω : ScalarThreeCochain G) :
    ScalarThreeCochain.fusionGauge β₂.beta
        (ScalarThreeCochain.fusionGauge β₁.beta ω) =
      ScalarThreeCochain.fusionGauge (β₁ * β₂).beta ω :=
  ScalarThreeCochain.fusionGauge_comp β₁.beta β₂.beta ω


-- @@ L135-144 verbatim
/-- Applying a restricted fusion gauge and then its pointwise inverse is the
identity action. -/
@[simp]
theorem fusionGauge_inv (β : RestrictedFusionGauge G) (ω : ScalarThreeCochain G) :
    ScalarThreeCochain.fusionGauge (β⁻¹).beta
        (ScalarThreeCochain.fusionGauge β.beta ω) = ω := by
  rw [ScalarThreeCochain.fusionGauge_comp]
  change ScalarThreeCochain.fusionGauge (β.beta * β.beta⁻¹) ω = ω
  rw [mul_inv_cancel]
  exact ScalarThreeCochain.fusionGauge_one ω


-- @@ L146-146 verbatim
end RestrictedFusionGauge


-- @@ L148-148 verbatim
namespace ActionTensorGauge


-- @@ L150-154 verbatim
omit [MulAction G X] in
/-- The identity action scalar is normalized. -/
@[simp]
theorem isNormalized_one : IsNormalized (1 : ActionTensorGauge G X) :=
  fun _ => rfl


-- @@ L156-160 verbatim
omit [MulAction G X] in
/-- Pointwise multiplication preserves normalized action scalars. -/
theorem IsNormalized.mul {γ₁ γ₂ : ActionTensorGauge G X}
    (hγ₁ : γ₁.IsNormalized) (hγ₂ : γ₂.IsNormalized) : (γ₁ * γ₂).IsNormalized :=
  fun x => by simp [hγ₁ x, hγ₂ x]


-- @@ L162-166 verbatim
omit [MulAction G X] in
/-- Pointwise inversion preserves normalized action scalars. -/
theorem IsNormalized.inv {γ : ActionTensorGauge G X}
    (hγ : γ.IsNormalized) : γ⁻¹.IsNormalized :=
  fun x => by simp [hγ x]


-- @@ L168-168 verbatim
end ActionTensorGauge


-- @@ L170-173 verbatim
/-- A restricted scalar gauge bundles an inverse-normalized fusion scalar `β`
with a normalized action scalar `γ`, as in arXiv:2502.20257, lines 2050--2054. -/
@[ext]
structure RestrictedScalarGauge (G X : Type*) [Group G] where
  
-- @@ L174-175 verbatim
/-- The restricted fusion gauge. -/
  fusion : RestrictedFusionGauge G
  
-- @@ L176-177 verbatim
/-- The scalar action gauge `γ`. -/
  gamma : ActionTensorGauge G X
  
-- @@ L178-179 verbatim
/-- Normalization of `γ` at the identity. -/
  gamma_isNormalized : gamma.IsNormalized


-- @@ L181-181 verbatim
namespace RestrictedScalarGauge


-- @@ L183-187 verbatim
/-- The identity restricted scalar gauge. -/
def one : RestrictedScalarGauge G X where
  fusion := 1
  gamma := 1
  gamma_isNormalized := ActionTensorGauge.isNormalized_one


-- @@ L189-193 verbatim
/-- Pointwise multiplication of restricted scalar gauges. -/
def mul (κ₁ κ₂ : RestrictedScalarGauge G X) : RestrictedScalarGauge G X where
  fusion := κ₁.fusion * κ₂.fusion
  gamma := κ₁.gamma * κ₂.gamma
  gamma_isNormalized := κ₁.gamma_isNormalized.mul κ₂.gamma_isNormalized


-- @@ L195-199 verbatim
/-- Pointwise inversion of a restricted scalar gauge. -/
def inv (κ : RestrictedScalarGauge G X) : RestrictedScalarGauge G X where
  fusion := κ.fusion⁻¹
  gamma := κ.gamma⁻¹
  gamma_isNormalized := κ.gamma_isNormalized.inv


-- @@ L201-201 verbatim
instance : One (RestrictedScalarGauge G X) := ⟨one⟩

-- @@ L202-202 verbatim
instance : Mul (RestrictedScalarGauge G X) := ⟨mul⟩

-- @@ L203-203 verbatim
instance : Inv (RestrictedScalarGauge G X) := ⟨inv⟩


-- @@ L205-225 verbatim
instance : Group (RestrictedScalarGauge G X) where
  mul_assoc κ₁ κ₂ κ₃ := by
    apply RestrictedScalarGauge.ext
    · exact mul_assoc κ₁.fusion κ₂.fusion κ₃.fusion
    · funext g x
      exact mul_assoc (κ₁.gamma g x) (κ₂.gamma g x) (κ₃.gamma g x)
  one_mul κ := by
    apply RestrictedScalarGauge.ext
    · exact one_mul κ.fusion
    · funext g x
      exact one_mul (κ.gamma g x)
  mul_one κ := by
    apply RestrictedScalarGauge.ext
    · exact mul_one κ.fusion
    · funext g x
      exact mul_one (κ.gamma g x)
  inv_mul_cancel κ := by
    apply RestrictedScalarGauge.ext
    · exact inv_mul_cancel κ.fusion
    · funext g x
      exact inv_mul_cancel (κ.gamma g x)


-- @@ L227-232 verbatim
/-- The identity restricted scalar gauge acts trivially on L-symbols. -/
@[simp]
theorem gauge_one (L : LSymbol G X) :
    LSymbol.gauge (1 : RestrictedScalarGauge G X).fusion.beta
      (1 : RestrictedScalarGauge G X).gamma L = L :=
  LSymbol.gauge_one L


-- @@ L234-238 verbatim
/-- Restricted scalar gauges preserve normalized L-symbols. -/
theorem isNormalized_gauge (κ : RestrictedScalarGauge G X) {L : LSymbol G X}
    (hL : L.IsNormalized) :
    (LSymbol.gauge κ.fusion.beta κ.gamma L).IsNormalized :=
  hL.gauge κ.fusion.isInverseNormalized.1 κ.gamma_isNormalized


-- @@ L240-246 verbatim
/-- Restricted scalar gauges preserve compatibility while acting on the
corresponding scalar 3-cochain by the fusion gauge. -/
theorem isCompatible_gauge (κ : RestrictedScalarGauge G X) {L : LSymbol G X}
    {ω : ScalarThreeCochain G} (hL : L.IsCompatible ω) :
    (LSymbol.gauge κ.fusion.beta κ.gamma L).IsCompatible
      (ScalarThreeCochain.fusionGauge κ.fusion.beta ω) :=
  hL.gauge κ.fusion.beta κ.gamma


-- @@ L248-254 verbatim
/-- Successive restricted scalar gauges compose according to
`LSymbol.gauge_comp`. -/
theorem gauge_mul (κ₁ κ₂ : RestrictedScalarGauge G X) (L : LSymbol G X) :
    LSymbol.gauge κ₂.fusion.beta κ₂.gamma
        (LSymbol.gauge κ₁.fusion.beta κ₁.gamma L) =
      LSymbol.gauge (κ₁ * κ₂).fusion.beta (κ₁ * κ₂).gamma L :=
  LSymbol.gauge_comp κ₁.fusion.beta κ₂.fusion.beta κ₁.gamma κ₂.gamma L


-- @@ L256-266 verbatim
/-- Applying a restricted scalar gauge and then its pointwise inverse is the
identity action on L-symbols. -/
@[simp]
theorem gauge_inv (κ : RestrictedScalarGauge G X) (L : LSymbol G X) :
    LSymbol.gauge (κ⁻¹).fusion.beta (κ⁻¹).gamma
        (LSymbol.gauge κ.fusion.beta κ.gamma L) = L := by
  rw [LSymbol.gauge_comp]
  change LSymbol.gauge (κ.fusion.beta * κ.fusion.beta⁻¹)
    (κ.gamma * κ.gamma⁻¹) L = L
  rw [mul_inv_cancel, mul_inv_cancel]
  exact LSymbol.gauge_one L


-- @@ L268-268 verbatim
end RestrictedScalarGauge


-- @@ L270-270 verbatim
end TNLean.Algebra
