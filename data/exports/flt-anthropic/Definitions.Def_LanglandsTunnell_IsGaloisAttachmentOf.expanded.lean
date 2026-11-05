import Mathlib
import Definitions.Def_LanglandsTunnell_OctahedralDatum
import Definitions.Def_LanglandsTunnell_ExplicitLift
import Definitions.Def_LanglandsTunnell_RealizationDictionary
import Definitions.Def_EllipticCurve_FrobeniusTrace


-- @@ L7-7 verbatim
set_option autoImplicit false


-- @@ L9-9 verbatim
open AutomorphicForm FLT.TunnellOctahedralGlobalCarrier FLT.ExplicitLift

-- @@ L10-10 verbatim
open scoped MatrixGroups


-- @@ L12-12 verbatim
namespace FLT.TunnellOctahedralGlobalCarrier


-- @@ L14-14 verbatim
local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)


-- @@ L16-22 verbatim
def IsGaloisAttachmentOf (ρ : Γℚ →* GL (Fin 2) (ZMod 3))
    (D : OctahedralGaloisDatum ℚ (ℤ√(-2))) (S : Finset ℕ) : Prop :=
  ∀ p : Nat.Primes, (p : ℕ) ∉ S →
    ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (p : ℕ) →
      ∀ σ : Γℚ, A.IsFrobeniusAt σ (p : ℕ) →
        red (D.attached.a (ratPrime p))
          = ((ρ σ : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).trace


-- @@ L24-24 verbatim
end FLT.TunnellOctahedralGlobalCarrier
