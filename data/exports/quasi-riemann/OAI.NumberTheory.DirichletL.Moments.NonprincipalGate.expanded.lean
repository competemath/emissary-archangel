import OAI.NumberTheory.DirichletL.Moments.SecondReducedPredicate


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentNonprincipalGate

-- @@ L9-9 verbatim
open HeckeFamily HeckeRowClosure CenteredExceptionalProfile CanonicalRowCompletion

-- @@ L10-10 verbatim
open ConcretePrimeRowBridge CenteredMomentRestrictedEnergy CenteredMomentChildRows RayFourExpansion

-- @@ L11-11 verbatim
local notation "O" => HeckeFamily.O


-- @@ L13-15 verbatim
def unitCharacter : Character := Character.ofResidue ⊤ top_ne_bot 1 (by
  intro u
  exact MulChar.one_apply (IsUnit.map (Ideal.Quotient.mk ⊤) u.isUnit))


-- @@ L17-20 verbatim
theorem unitCharacter_primitive : FiniteFourier.IsPrimitiveOnIdeals unitCharacter.residue := by
  change FiniteFourier.IsPrimitiveOnIdeals (1:MulChar (O⧸(⊤:Ideal O)) ℂ)
  intro I hI
  exact (hI (Subsingleton.elim _ _)).elim


-- @@ L22-26 verbatim
theorem unitCharacter_ideal (I:Ideal O) (hI:I≠0) : idealCoeff unitCharacter I=1 := by
  rw [←span_idealGenerator I,idealCoeff_span _ (idealGenerator_ne_zero I hI)]
  change (1:MulChar (O⧸(⊤:Ideal O)) ℂ) (Ideal.Quotient.mk _ (idealGenerator I))=1
  rw [show Ideal.Quotient.mk (⊤:Ideal O) (idealGenerator I)=1 from Subsingleton.elim _ _]
  exact map_one _


-- @@ L28-42 verbatim
theorem principal_inducedBy_unit (χ:Character) (hχ:χ.residue=1) : InducedBy χ unitCharacter := by
  intro I
  by_cases hI:I=0
  · subst I
    simp only [map_zero,ite_self]
  · have hn:=idealGenerator_ne_zero I hI
    rw [unitCharacter_ideal I hI]
    rw [←span_idealGenerator I,idealCoeff_span χ hn]
    change χ.residue (Ideal.Quotient.mk χ.modulus (idealGenerator I))=_
    rw [hχ]
    by_cases hc:IsCoprime (Ideal.span {idealGenerator I}) χ.modulus
    · rw [ite_eq_left hc]
      exact MulChar.one_apply ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hc)
    · rw [ite_eq_right hc]
      exact MulChar.map_nonunit _ (fun h=>hc ((IdealCharacter.isUnit_mk_iff_isCoprime _ _).mp h))


-- @@ L44-47 verbatim
theorem principal_row_fixed (η χ:Character) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hχ:χ.residue=1) : FixedInducingRow η Q m A z :=
  ⟨χ,unitCharacter,unitCharacter_primitive,principal_inducedBy_unit χ hχ,le_top,hrow⟩


-- @@ L49-52 verbatim
theorem actual_row_nonprincipal (η χ:Character) (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (hex:¬FixedInducingRow η Q m A z) : χ.residue≠1 :=
  fun h=>hex (principal_row_fixed η χ Q m A z hrow h)


-- @@ L54-58 verbatim
theorem nonexceptional_row_nonprincipal (η χ:Character) (ξ:RayCharacter)
    (Q:Ideal O) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=rowTwist (elementHom (childCharacter η ξ)) m 1 (A*z) n)
    (hex:nonexceptional η ξ Q m A z) : χ.residue≠1 :=
  actual_row_nonprincipal (childCharacter η ξ) χ Q m A z hrow hex.2


-- @@ L60-60 verbatim
end SevenEighths.CenteredMomentNonprincipalGate


-- @@ L62-62 verbatim
end


-- @@ L64-64 verbatim
end OAI
