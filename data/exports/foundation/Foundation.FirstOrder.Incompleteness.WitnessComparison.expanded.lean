module

public import Foundation.FirstOrder.Incompleteness.StandardProvability


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-8 verbatim
/-!
# Witness comparisons of provability
-/


-- @@ L10-10 verbatim
namespace FFL.FirstOrder.Arithmetic.Bootstrapping


-- @@ L12-12 verbatim
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


-- @@ L14-14 verbatim
section WitnessComparisons


-- @@ L16-16 verbatim
variable {L : Language} [L.Encodable] [L.LORDefinable]


-- @@ L18-18 verbatim
variable (T : Theory L) [T.Δ₁]


-- @@ L20-21 verbatim
def _root_.FFL.FirstOrder.Theory.ProvabilityComparisonLE (φ ψ : V) : Prop :=
  ∃ b, Proof T b φ ∧ ∀ b' < b, ¬Proof T b' ψ


-- @@ L23-24 verbatim
def _root_.FFL.FirstOrder.Theory.ProvabilityComparisonLT (φ ψ : V) : Prop :=
  ∃ b, Proof T b φ ∧ ∀ b' ≤ b, ¬Proof T b' ψ


-- @@ L26-26 verbatim
section


-- @@ L28-29 verbatim
noncomputable def _root_.FFL.FirstOrder.Theory.provabilityComparisonLE : 𝚺₁.Semisentence 2 := .mkSigma
  “φ ψ. ∃ b, !(proof T).sigma b φ ∧ ∀ b' < b, ¬!(proof T).pi b' ψ”


-- @@ L31-33 verbatim
instance _root_.FFL.FirstOrder.Theory.provability_comparison_le_defined :
    𝚺₁-Relation[V] T.ProvabilityComparisonLE via T.provabilityComparisonLE := .mk fun v ↦ by
  simp [Theory.provabilityComparisonLE, Theory.ProvabilityComparisonLE]


-- @@ L35-36 verbatim
instance _root_.FFL.FirstOrder.Theory.provability_comparison_le_definable : 𝚺₁-Relation[V] T.ProvabilityComparisonLE :=
  T.provability_comparison_le_defined.to_definable


-- @@ L38-40 verbatim
/-- instance for definability tactic -/
instance _root_.FFL.FirstOrder.Theory.provability_comparison_le_definable' :
    𝚺-[0 + 1]-Relation[V] T.ProvabilityComparisonLE := T.provability_comparison_le_definable



-- @@ L43-44 verbatim
noncomputable def _root_.FFL.FirstOrder.Theory.provabilityComparisonLT : 𝚺₁.Semisentence 2 := .mkSigma
  “φ ψ. ∃ b, !(proof T).sigma b φ ∧ ∀ b' <⁺ b, ¬!(proof T).pi b' ψ”


-- @@ L46-48 verbatim
instance _root_.FFL.FirstOrder.Theory.provability_comparison_lt_defined :
    𝚺₁-Relation[V] T.ProvabilityComparisonLT via T.provabilityComparisonLT := .mk fun v ↦ by
  simp [Theory.provabilityComparisonLT, Theory.ProvabilityComparisonLT]


-- @@ L50-51 verbatim
instance _root_.FFL.FirstOrder.Theory.provability_comparison_lt_definable : 𝚺₁-Relation[V] T.ProvabilityComparisonLT :=
  T.provability_comparison_lt_defined.to_definable


-- @@ L53-55 verbatim
/-- instance for definability tactic -/
instance _root_.FFL.FirstOrder.Theory.provability_comparison_lt_definable' :
    𝚺-[0 + 1]-Relation[V] T.ProvabilityComparisonLT := T.provability_comparison_lt_definable


-- @@ L57-57 verbatim
end


-- @@ L59-59 verbatim
variable {T : Theory L} [T.Δ₁]


-- @@ L61-61 verbatim
namespace ProvabilityComparison


-- @@ L63-63 verbatim
variable {φ ψ χ : V}


-- @@ L65-65 verbatim
local infixl:50 "≼" => T.ProvabilityComparisonLE

-- @@ L66-66 verbatim
local infixl:50 "≺" => T.ProvabilityComparisonLT

-- @@ L67-67 verbatim
local prefix:50 "□" => Provable T


-- @@ L69-70 verbatim
@[grind =>]
lemma le_of_lt : φ ≺ ψ → φ ≼ ψ := by rintro ⟨b, _⟩; exact ⟨b, by grind⟩


-- @@ L72-73 verbatim
@[grind =>]
lemma le_to_provable : φ ≼ ψ → □φ := by rintro ⟨b, hb, _⟩; exact ⟨b, by grind⟩


-- @@ L75-76 verbatim
@[grind =>]
lemma le_trans : φ ≼ ψ → ψ ≼ χ → φ ≼ χ := by rintro ⟨b, hb, h⟩ ⟨d, hd, H⟩; use b; grind;


-- @@ L78-98 verbatim
@[grind =>]
lemma le_antisymm : φ ≼ ψ → ψ ≼ φ → φ = ψ := by
  rintro ⟨b, hb, Hb⟩ ⟨d, hd, Hd⟩
  have : b = d := by
    by_contra ne
    wlog lt : b < d
    · grind;
    have : ¬Proof T b φ := Hd b lt
    contradiction
  have : ({φ} : V) = {ψ} := by simp [←hb.1, ←hd.1, this]
  simpa using this


lemma iff_le_refl_provable : φ ≼ φ ↔ □φ := by
  constructor
  · exact le_to_provable
  · rintro ⟨b, hb⟩
    have : ∃ b, Proof T b φ ∧ ∀ z < b, ¬Proof T z φ :=
      InductionOnHierarchy.least_number_sigma 𝚺 1 (P := (Proof T · φ)) (by definability) hb
    rcases this with ⟨b, bd, h⟩
    exact ⟨b, bd, h⟩


-- @@ L100-101 verbatim
@[grind .]
lemma lt_irrefl : ¬φ ≺ φ := by rintro ⟨b, hb, h⟩; have : ¬Proof T b φ := h b (by simp); contradiction


-- @@ L103-104 verbatim
@[grind =>]
lemma lt_trans : φ ≺ ψ → ψ ≺ χ → φ ≺ χ := by rintro ⟨b, hb, h⟩ ⟨d, hd, H⟩; use b; grind;



-- @@ L107-119 verbatim
@[grind =>]
lemma not_lt_of_le : φ ≼ ψ → ¬ψ ≺ φ := by grind;


lemma find_minimal_proof_fintype [Fintype ι] (φ : ι → V) (H : □(φ i)) :
    ∃ j, ∀ k, (φ j) ≼ (φ k) := by
  rcases show ∃ dᵢ, Proof T dᵢ (φ i)from H with ⟨dᵢ, Hdᵢ⟩
  have : ∃ z, (∃ j, Proof T z (φ j)) ∧ ∀ w < z, ∀ x, ¬Proof T w (φ x) := by
    simpa using
      InductionOnHierarchy.least_number_sigma 𝚺 1 (P := fun z ↦ ∃ j, Proof T z (φ j))
        (HierarchySymbol.Definable.fintype_exs fun j ↦ by definability) (x := dᵢ) ⟨i, Hdᵢ⟩
  rcases this with ⟨z, ⟨j, hj⟩, H⟩
  exact ⟨j, fun k ↦ ⟨z, hj, fun w hw ↦ H w hw k⟩⟩


-- @@ L121-121 verbatim
end ProvabilityComparison


-- @@ L123-123 verbatim
end WitnessComparisons


-- @@ L125-125 verbatim
end FFL.FirstOrder.Arithmetic.Bootstrapping
