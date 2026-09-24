module

public import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D1
public import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D2
public import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.D3
public import Foundation.FirstOrder.Incompleteness.ProvabilityAbstraction.Basic
public import Foundation.FirstOrder.Bootstrapping.FixedPoint


-- @@ L9-9 verbatim
@[expose] public section

-- @@ L10-12 verbatim
/-!
# Derivability conditions of standard provability predicate
-/


-- @@ L14-14 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L16-16 verbatim
open ISigma1 Bootstrapping ProvabilityAbstraction


-- @@ L18-20 expanded
noncomputable instance : Diagonalization (ISigma 1)
    where
  fixedpoint := fixedpoint
  diag θ := diagonal θ


-- @@ L22-22 verbatim
section


-- @@ L24-24 verbatim
variable {L : Language} [L.Encodable] [L.LORDefinable] {T : Theory L} [T.Δ₁]


-- @@ L26-26 verbatim
local prefix:90 "□" => provabilityPred T


-- @@ L28-30 expanded
/-- The derivability condition D1. -/
theorem provable_D1 {σ} : Provable T σ → Provable (ISigma 1) (Box.box σ) := fun h ↦
  complete (ISigma 1) _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using internalize_provability (V := V) h


-- @@ L32-34 expanded
/-- The derivability condition D2. -/
theorem provable_D2 {σ π} :
    Provable (ISigma 1)
      binop% HArrow.hArrow (Box.box (binop% HArrow.hArrow σ π))
        binop% HArrow.hArrow (Box.box σ) (Box.box π) :=
  complete (ISigma 1) _ fun (V : Type) _ _ ↦ by simpa [models_iff] using modus_ponens_sentence T


-- @@ L36-36 verbatim
variable (T)


-- @@ L38-40 expanded
noncomputable abbrev _root_.FFL.FirstOrder.Theory.standardProvability : Provability (ISigma 1) T
    where
  prov := provable T
  bew_def := provable_D1


-- @@ L42-42 verbatim
variable {T}


-- @@ L44-44 verbatim
instance : T.standardProvability.HBL2 := ⟨provable_D2⟩


-- @@ L46-46 verbatim
lemma standardProvability_def (σ : Sentence L) : T.standardProvability σ = provabilityPred T σ := rfl


-- @@ L48-49 verbatim
instance : T.standardProvability.SoundOn ℕ :=
  ⟨fun h ↦ by simpa [Arithmetic.standardProvability_def, models_iff] using h⟩


-- @@ L51-51 verbatim
end


-- @@ L53-53 verbatim
section arithmetic


-- @@ L55-55 verbatim
variable {T U : ArithmeticTheory} [T.Δ₁]


-- @@ L57-57 verbatim
local prefix:90 "□" => provabilityPred T


-- @@ L59-62 expanded
lemma provable_sigma_one_complete [WeakerThan PeanoMinus T] {σ : ArithmeticSentence}
    (hσ : Hierarchy SigmaSymbol.sigma 1 σ) :
    Provable (ISigma 1) binop% HArrow.hArrow σ (Box.box σ) :=
  complete (ISigma 1) _ fun (V : Type) _ _ ↦ by
    simpa [models_iff] using Bootstrapping.Arithmetic.sigma_one_complete (T := T) (V := V) hσ


-- @@ L64-66 expanded
/-- The derivability condition D3. -/
theorem provable_D3 [WeakerThan PeanoMinus T] {σ : ArithmeticSentence} :
    Provable (ISigma 1) binop% HArrow.hArrow (Box.box σ) (Box.box (Box.box σ)) :=
  provable_sigma_one_complete (by simp)


-- @@ L68-68 verbatim
open FFL.Entailment FFL.Entailment.FiniteContext


-- @@ L70-71 expanded
lemma provable_D2_context [WeakerThan (ISigma 1) U] {Γ σ π}
    (hσπ : Provable U Γ (Box.box (binop% HArrow.hArrow σ π))) (hσ : Provable U Γ (Box.box σ)) :
    Provable U Γ (Box.box π) :=
  mdp! (mdp! (FiniteContext.of' (weakening inferInstance provable_D2)) hσπ) hσ


-- @@ L73-74 expanded
lemma provable_D3_context [WeakerThan PeanoMinus T] [WeakerThan (ISigma 1) U] {Γ σ}
    (hσπ : Provable U Γ (Box.box σ)) : Provable U Γ (Box.box (Box.box σ)) :=
  mdp! (FiniteContext.of' (weakening inferInstance provable_D3)) hσπ


-- @@ L76-78 expanded
lemma provable_sound [U.SoundOnHierarchy SigmaSymbol.sigma 1] {σ} :
    Provable U (Box.box σ) → Provable T σ := fun h ↦
  by
  have : Models (Language.str ℕ oRing) (provabilityPred T σ) :=
    ArithmeticTheory.SoundOn.sound (F := Arithmetic.Hierarchy SigmaSymbol.sigma 1) h (by simp)
  simpa [models_iff] using this


-- @@ L80-81 expanded
lemma provable_complete [U.SoundOnHierarchy SigmaSymbol.sigma 1] [WeakerThan (ISigma 1) U] {σ} :
    Provable T σ ↔ Provable U (Box.box σ) :=
  ⟨fun h ↦ weakening inferInstance (provable_D1 h), provable_sound⟩


-- @@ L83-83 expanded
instance [WeakerThan PeanoMinus T] : T.standardProvability.HBL3 :=
  ⟨provable_D3⟩


-- @@ L85-85 expanded
instance [WeakerThan PeanoMinus T] : T.standardProvability.HBL where


-- @@ L87-87 expanded
instance [T.SoundOnHierarchy SigmaSymbol.sigma 1] : T.standardProvability.Kreisel :=
  ⟨fun h ↦ provable_sound h⟩


-- @@ L89-99 expanded
open FFL.Entailment in
/-- If `π` is equivalent to some 𝚺₁ sentence `σ`,
  then `π 🡒 □π` is provable in `T` (note: not `𝗜𝚺₁`, compare `provable_sigma_one_complete`)
-/
lemma provable_sigma_one_complete_of_E {σ π} [WeakerThan (ISigma 1) T]
    (hσ : Hierarchy SigmaSymbol.sigma 1 σ) (hσπ : Provable (ISigma 1) (LogicalConnective.iff σ π)) :
    Provable (ISigma 1) binop% HArrow.hArrow π (Box.box π) :=
  by
  apply C_replace ?_ ?_ $ provable_sigma_one_complete (T := T) $ hσ; · cl_prover[hσπ];
  · apply T.standardProvability.mono'; cl_prover[hσπ];


-- @@ L101-101 verbatim
end arithmetic


-- @@ L103-109 expanded
open FFL.Entailment in
lemma exists_true_but_unprovable_sentence_of_incomplete {T : ArithmeticTheory} (h : Incomplete T) :
    ∃ δ : ArithmeticSentence, Models (Language.str ℕ oRing) δ ∧ Unprovable T δ :=
  by
  obtain ⟨δ, hδ⟩ := incomplete_def.mp h; by_cases Models (Language.str ℕ oRing) δ
  · exact ⟨δ, by assumption, hδ.1⟩
  · exact ⟨unop% HTilde.hTilde δ, by simpa, hδ.2⟩


-- @@ L111-111 verbatim
end FFL.FirstOrder.Arithmetic
