import Mathlib
import Definitions.Def_LanglandsTunnell_OctahedralDatum
import Definitions.Def_LanglandsTunnell_IsGaloisAttachmentOf
import Definitions.Def_GaloisRep_ModThreeCyclotomic


-- @@ L6-6 verbatim
set_option autoImplicit false


-- @@ L8-8 verbatim
open AutomorphicForm WeierstrassCurve

-- @@ L9-9 verbatim
open FLT.TunnellOctahedralGlobalCarrier FLT.Qepw139bOctahedralDatumLinkedRecarve

-- @@ L10-10 verbatim
open scoped MatrixGroups


-- @@ L12-12 verbatim
noncomputable section


-- @@ L14-14 verbatim
namespace LanglandsTunnell


-- @@ L16-16 verbatim
local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)


-- @@ L18-24 verbatim
def TunnellExistsForAttachedOctahedralData (notionT : CuspidalityNotion (ℤ√(-2))) : Prop :=
  ∀ ρ : Γℚ →* GL (Fin 2) (ZMod 3), Continuous ρ → Function.Surjective ρ →
    (∀ σ : Γℚ, Matrix.GeneralLinearGroup.det (ρ σ) = modThreeCyclotomicChar σ) →
    ∀ (D : OctahedralGaloisDatumLinked ℚ (ℤ√(-2))) (S : Finset ℕ),
      IsGaloisAttachmentOf ρ D.toOctahedralGaloisDatum S →
      ∃ π : HeckeEigensystem ℚ (ℤ√(-2)),
        notionT.IsCusp ℚ π ∧ HeckeEigensystem.AgreesAwayFromFinite π D.attached


-- @@ L26-27 verbatim
def NotionInhabitedOverRat (notionD : CuspidalityNotion (ℤ√(-2))) : Prop :=
  ∃ π : HeckeEigensystem ℚ (ℤ√(-2)), notionD.IsCusp ℚ π


-- @@ L29-36 verbatim
def NotionCompatForAttachedOctahedralData (notionT notionD : CuspidalityNotion (ℤ√(-2))) : Prop :=
  ∀ ρ : Γℚ →* GL (Fin 2) (ZMod 3), Continuous ρ → Function.Surjective ρ →
    (∀ σ : Γℚ, Matrix.GeneralLinearGroup.det (ρ σ) = modThreeCyclotomicChar σ) →
    ∀ (D : OctahedralGaloisDatumLinked ℚ (ℤ√(-2))) (S : Finset ℕ),
      IsGaloisAttachmentOf ρ D.toOctahedralGaloisDatum S →
      ∀ π : HeckeEigensystem ℚ (ℤ√(-2)),
        notionT.IsCusp ℚ π → HeckeEigensystem.AgreesAwayFromFinite π D.attached →
        notionD.IsCusp ℚ π


-- @@ L38-38 verbatim
end LanglandsTunnell


-- @@ L40-40 verbatim
end
