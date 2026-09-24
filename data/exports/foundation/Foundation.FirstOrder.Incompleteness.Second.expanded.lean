module

public import Foundation.FirstOrder.Incompleteness.Consistency
public import Foundation.FirstOrder.Incompleteness.RosserProvability
public import Foundation.FirstOrder.Bootstrapping.Syntax.CraigTrick


-- @@ L7-7 verbatim
@[expose] public section

-- @@ L8-10 verbatim
/-!
# Gödel's second incompleteness theorem for arithmetic theories stronger than $\mathsf{I}\Sigma_1$
-/


-- @@ L12-12 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L14-14 verbatim
open FFL.Entailment ProvabilityAbstraction


-- @@ L16-16 verbatim
variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]


-- @@ L18-20 verbatim
/-- Gödel's second incompleteness theorem -/
theorem consistent_unprovable [Consistent T] : T ⊬ T.consistent.val :=
  ProvabilityAbstraction.con_unprovable (𝔅 := T.standardProvability)


-- @@ L22-25 verbatim
/-- Gödel's second incompleteness theorem for r.e. theories -/
theorem craig_consistent_unprovable_of_RE (T : ArithmeticTheory) [T.RE] [𝗜𝚺₁ ⪯ T]
    [Consistent T] : T ⊬ T.craig.consistent.val :=
  fun h ↦ consistent_unprovable T.craig (WeakerThan.pbl h)


-- @@ L27-28 verbatim
theorem inconsistent_unprovable [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : T ⊬ ∼T.consistent.val :=
  ProvabilityAbstraction.con_unrefutable (𝔅 := T.standardProvability)


-- @@ L30-32 verbatim
/-- The consistency statement is independent. -/
theorem inconsistent_independent [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : Independent T T.consistent.val :=
  ProvabilityAbstraction.con_independent (𝔅 := T.standardProvability)


-- @@ L34-37 verbatim
instance [Consistent T] : T ⪱ T ∪ T.Con :=
  StrictlyWeakerThan.of_unprovable_provable (φ := T.consistent)
    (consistent_unprovable T)
    (Entailment.by_axm (by simp))


-- @@ L39-42 verbatim
instance [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : T ⪱ T ∪ T.Incon :=
  StrictlyWeakerThan.of_unprovable_provable (φ := ∼T.consistent)
    (inconsistent_unprovable T)
    (Entailment.by_axm (by simp))


-- @@ L44-44 verbatim
end FFL.FirstOrder.Arithmetic
