module

public import Foundation.FirstOrder.Incompleteness.StandardProvability


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-8 verbatim
/-!
# Löb's Theorem
-/


-- @@ L10-10 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L12-12 verbatim
open FFL.Entailment Bootstrapping ProvabilityAbstraction


-- @@ L14-14 expanded
variable {T : ArithmeticTheory} [T.Δ₁] [WeakerThan (ISigma 1) T] {σ : ArithmeticSentence}


-- @@ L16-17 expanded
theorem löb_theorem : Provable T binop% HArrow.hArrow (provabilityPred T σ) σ → Provable T σ :=
  ProvabilityAbstraction.löb_theorem (𝔅 := T.standardProvability)


-- @@ L19-20 expanded
theorem formalized_löb_theorem :
    Provable (ISigma 1)
      binop% HArrow.hArrow (provabilityPred T (binop% HArrow.hArrow (provabilityPred T σ) σ))
        (provabilityPred T σ) :=
  ProvabilityAbstraction.formalized_löb_theorem (𝔅 := T.standardProvability)


-- @@ L22-22 verbatim
end FFL.FirstOrder.Arithmetic
