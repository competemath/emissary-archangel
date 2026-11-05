import Mathlib
import Definitions.Def_ArtinL_EulerFactor
import Definitions.Def_Mathlib_RingTheory_Valuation_LowerRamificationGroup


-- @@ L5-5 verbatim
set_option autoImplicit false


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
open scoped MatrixGroups Pointwise


-- @@ L11-11 verbatim
namespace ArtinL


-- @@ L13-13 verbatim
variable {n : ℕ}


-- @@ L15-15 verbatim
local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

-- @@ L16-16 verbatim
local notation "ℚbar" => AlgebraicClosure ℚ


-- @@ L18-19 verbatim
def splittingField (ρ : Γℚ →* GL (Fin n) ℂ) : IntermediateField ℚ ℚbar :=
  IntermediateField.fixedField ρ.ker


-- @@ L21-30 verbatim
theorem apply_mem_splittingField (ρ : Γℚ →* GL (Fin n) ℂ) (σ : Γℚ) {x : ℚbar}
    (hx : x ∈ splittingField ρ) : σ x ∈ splittingField ρ := by
  rintro ⟨τ, hτ⟩
  change τ (σ x) = σ x
  have hmem : σ⁻¹ * τ * σ ∈ ρ.ker := by
    rw [MonoidHom.mem_ker] at hτ ⊢
    rw [map_mul, map_mul, hτ, mul_one, ← map_mul, inv_mul_cancel, map_one]
  have h := hx ⟨σ⁻¹ * τ * σ, hmem⟩
  change (σ⁻¹ * τ * σ) x = x at h
  simpa [AlgEquiv.mul_apply] using congrArg σ h


-- @@ L32-40 verbatim
instance mulSemiringActionSplittingField (ρ : Γℚ →* GL (Fin n) ℂ) :
    MulSemiringAction Γℚ (splittingField ρ) where
  smul σ x := ⟨σ (x : ℚbar), apply_mem_splittingField ρ σ x.2⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl
  smul_zero σ := Subtype.ext (map_zero σ)
  smul_add σ x y := Subtype.ext (map_add σ (x : ℚbar) (y : ℚbar))
  smul_one σ := Subtype.ext (map_one σ)
  smul_mul σ x y := Subtype.ext (map_mul σ (x : ℚbar) (y : ℚbar))


-- @@ L42-43 verbatim
@[simp] theorem coe_smul_splittingField (ρ : Γℚ →* GL (Fin n) ℂ) (σ : Γℚ)
    (x : splittingField ρ) : ((σ • x : splittingField ρ) : ℚbar) = σ (x : ℚbar) := rfl


-- @@ L45-47 verbatim
def placeUnder (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar) :
    ValuationSubring (splittingField ρ) :=
  A.comap (algebraMap (splittingField ρ) ℚbar)


-- @@ L49-50 verbatim
theorem mem_placeUnder_iff (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar)
    (x : splittingField ρ) : x ∈ placeUnder ρ A ↔ (x : ℚbar) ∈ A := Iff.rfl


-- @@ L52-59 verbatim
theorem smul_mem_placeUnder (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar)
    (σ : A.decompositionSubgroup ℚ) {x : splittingField ρ} (hx : x ∈ placeUnder ρ A) :
    (σ : Γℚ) • x ∈ placeUnder ρ A := by
  rw [mem_placeUnder_iff] at hx ⊢
  have h : (σ : Γℚ) • (x : ℚbar) ∈ (σ : Γℚ) • (A : ValuationSubring ℚbar) :=
    Set.smul_mem_smul_set hx
  rw [σ.2] at h
  exact h


-- @@ L61-70 verbatim
instance mulSemiringActionPlaceUnder (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar) :
    MulSemiringAction (A.decompositionSubgroup ℚ) (placeUnder ρ A) where
  smul σ x := ⟨(σ : Γℚ) • (x : splittingField ρ), smul_mem_placeUnder ρ A σ x.2⟩
  one_smul x := Subtype.ext (one_smul Γℚ (x : splittingField ρ))
  mul_smul σ τ x := Subtype.ext (mul_smul (σ : Γℚ) (τ : Γℚ) (x : splittingField ρ))
  smul_zero σ := Subtype.ext (smul_zero (σ : Γℚ))
  smul_add σ x y := Subtype.ext (smul_add (σ : Γℚ) (x : splittingField ρ) (y : splittingField ρ))
  smul_one σ := Subtype.ext (smul_one (σ : Γℚ))
  smul_mul σ x y :=
    Subtype.ext (MulSemiringAction.smul_mul (σ : Γℚ) (x : splittingField ρ) (y : splittingField ρ))


-- @@ L72-74 verbatim
@[simp] theorem coe_coe_smul_placeUnder (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar)
    (σ : A.decompositionSubgroup ℚ) (x : placeUnder ρ A) :
    (((σ • x : placeUnder ρ A) : splittingField ρ) : ℚbar) = (σ : Γℚ) ((x : splittingField ρ) : ℚbar) := rfl


-- @@ L76-80 verbatim
def ramificationGroup (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar) (i : ℕ) :
    Subgroup Γℚ :=
  A.inertiaSubgroupIn ℚ ⊓
    (IsLocalRing.lowerRamificationGroup (placeUnder ρ A) (A.decompositionSubgroup ℚ) i).map
      (A.decompositionSubgroup ℚ).subtype


-- @@ L82-83 verbatim
def codimInvariants (ρ : Γℚ →* GL (Fin n) ℂ) (H : Subgroup Γℚ) : ℕ :=
  n - Module.finrank ℂ (invariantsUnder ρ H)


-- @@ L85-89 verbatim
def swanConductor (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar) : ℚ :=
  ∑ᶠ i : ℕ,
    (Nat.card ((ramificationGroup ρ A (i + 1)).map ρ) : ℚ) /
        (Nat.card ((A.inertiaSubgroupIn ℚ).map ρ) : ℚ) *
      (codimInvariants ρ (ramificationGroup ρ A (i + 1)) : ℚ)


-- @@ L91-92 verbatim
def conductorExponentAt (ρ : Γℚ →* GL (Fin n) ℂ) (A : ValuationSubring ℚbar) : ℕ :=
  codimInvariants ρ (A.inertiaSubgroupIn ℚ) + ⌈swanConductor ρ A⌉₊


-- @@ L94-99 verbatim
open scoped Classical in

def conductorExponent (ρ : Γℚ →* GL (Fin n) ℂ) (p : ℕ) : ℕ :=
  if h : p.Prime ∧ ∃ A : ValuationSubring ℚbar, A.LiesOverPrime p then
    conductorExponentAt ρ h.2.choose
  else 0


-- @@ L101-102 verbatim
def conductor (ρ : Γℚ →* GL (Fin n) ℂ) : ℕ :=
  ∏ᶠ p : ℕ, p ^ conductorExponent ρ p


-- @@ L104-104 verbatim
end ArtinL


-- @@ L106-106 verbatim
end
