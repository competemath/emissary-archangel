import OAI.NumberTheory.DirichletL.Moments.FirstChildLower
import OAI.NumberTheory.DirichletL.Energy.AmplifiedRayDictionary


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission

-- @@ L10-10 verbatim
open HeckeFamily ConcretePrimeRowBridge CanonicalQuadraticSieve

-- @@ L11-11 verbatim
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile

-- @@ L12-12 verbatim
open CenteredMomentAmplificationChildInput CenteredMomentAmplificationChildSourceCaps

-- @@ L13-13 verbatim
open CenteredMomentEnergyAmplifiedRayDictionary CenteredMomentFirstAnnularInput

-- @@ L14-14 verbatim
open CenteredMomentFirstChildLower CenteredMomentFirstAmplificationChoice

-- @@ L15-15 verbatim
open CenteredMomentSectorLocalization

-- @@ L16-16 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L17-17 verbatim
variable {α:Type*}[Fintype α]

-- @@ L18-18 verbatim
local instance {ι:Type*}:DecidableEq ι:=Classical.decEq _


-- @@ L20-22 verbatim
def parentLower (s:Input α)(Z:ℝ):ℝ:=
  min (min (Real.logb Z s.X₁) (Real.logb Z s.X₂))
    (min (Real.logb Z s.Y₁) (Real.logb Z s.Y₂))


-- @@ L24-34 verbatim
theorem parent_lower_scales (s:Input α)(Z:ℝ)(hZ:1<Z):
    Z^(parentLower s Z)≤s.X₁ ∧ Z^(parentLower s Z)≤s.X₂ ∧
    Z^(parentLower s Z)≤s.Y₁ ∧ Z^(parentLower s Z)≤s.Y₂:=by
  have h (X:ℝ)(hX:0<X)(hx:parentLower s Z≤Real.logb Z X):Z^(parentLower s Z)≤X:=by
    calc
      _≤Z^(Real.logb Z X):=Real.rpow_le_rpow_of_exponent_le hZ.le hx
      _=X:=Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hX
  exact ⟨h _ s.X₁_pos ((min_le_left _ _).trans (min_le_left _ _)),
    h _ s.X₂_pos ((min_le_left _ _).trans (min_le_right _ _)),
    h _ s.Y₁_pos ((min_le_right _ _).trans (min_le_left _ _)),
    h _ s.Y₂_pos ((min_le_right _ _).trans (min_le_right _ _))⟩


-- @@ L36-42 verbatim
theorem main_minimum_lower (s:Input α)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t Z:ℝ)(hZ:1<Z):
    let d:=child s C R B τ t
    let r:=parentLower s Z-Real.logb Z (C.absNorm:ℝ)
    Z^r≤d.X₁ ∧ Z^r≤d.X₂ ∧ Z^r≤d.Y₁ ∧ Z^r≤d.Y₂:=by
  have h:=parent_lower_scales s Z hZ
  exact child_lower s C R hC B τ t Z (parentLower s Z) hZ h.1 h.2.1 h.2.2.1 h.2.2.2


-- @@ L44-60 verbatim
theorem active_error_lower (s:Input α)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)(p:O)(hp:p≠0)(k:ℕ)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools ((Ideal.span {p})^k))
    (υ:Character)(v Z r:ℝ)(hZ:1<Z)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    let d:=child (activeInput (child s C R B τ t)) ((Ideal.span {p})^k) (R*C) Bp υ v
    let r':=r-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k
    Z^r'≤d.X₁ ∧ Z^r'≤d.X₂ ∧ Z^r'≤d.Y₁ ∧ Z^r'≤d.Y₂:=by
  have hc:=child_lower s C R hC B τ t Z r hZ hX₁ hX₂ hY₁ hY₂
  have hpn:(Ideal.span {p}:Ideal O)≠0:=Ideal.span_singleton_eq_bot.not.mpr hp
  have hh:=child_lower (activeInput (child s C R B τ t)) ((Ideal.span {p})^k) (R*C)
    (pow_ne_zero k hpn) Bp υ v Z (r-Real.logb Z (C.absNorm:ℝ)) hZ
    hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
  have he:Real.logb Z (((Ideal.span {p}:Ideal O)^k).absNorm:ℝ)=errorRemoval p Z k:=by
    rw [map_pow,Nat.cast_pow,Real.logb_pow]
    rfl
  simpa only [he] using hh


-- @@ L62-70 verbatim
theorem restored_error_lower (s:Input α)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)(p:O)(hp:p≠0)(k:ℕ)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools ((Ideal.span {p})^k))
    (υ:Character)(v Z r:ℝ)(hZ:1<Z)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    let d:=restoredError s C R B τ t (Ideal.span {p}) k Bp υ v
    let r':=r-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k
    Z^r'≤d.X₁ ∧ Z^r'≤d.X₂ ∧ Z^r'≤d.Y₁ ∧ Z^r'≤d.Y₂:=by
  exact active_error_lower s C R hC B τ t p hp k Bp υ v Z r hZ hX₁ hX₂ hY₁ hY₂


-- @@ L72-81 verbatim
theorem error_minimum_lower (s:Input α)(C R:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(τ:Character)(t:ℝ)(p:O)(hp:p≠0)(k:ℕ)
    (Bp:actualAllocations (activeInput (child s C R B τ t)).pools ((Ideal.span {p})^k))
    (υ:Character)(v Z:ℝ)(hZ:1<Z):
    let d:=child (activeInput (child s C R B τ t)) ((Ideal.span {p})^k) (R*C) Bp υ v
    let r':=parentLower s Z-Real.logb Z (C.absNorm:ℝ)-errorRemoval p Z k
    Z^r'≤d.X₁ ∧ Z^r'≤d.X₂ ∧ Z^r'≤d.Y₁ ∧ Z^r'≤d.Y₂:=by
  have h:=parent_lower_scales s Z hZ
  exact active_error_lower s C R hC B τ t p hp k Bp υ v Z (parentLower s Z) hZ
    h.1 h.2.1 h.2.2.1 h.2.2.2


-- @@ L83-83 verbatim
end SevenEighths.CenteredMomentEnergyFirstRawScaleAdmission


-- @@ L85-85 verbatim
end


-- @@ L87-87 verbatim
end OAI
