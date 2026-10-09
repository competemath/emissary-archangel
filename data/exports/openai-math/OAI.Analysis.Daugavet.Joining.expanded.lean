import OAI.Analysis.Daugavet.ProductApproximation


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open MeasureTheory ProbabilityTheory Set Filter

-- @@ L7-7 verbatim
open scoped ENNReal NNReal Topology BigOperators


-- @@ L9-9 verbatim
universe uX uY uB uIota uKappa uBeta


-- @@ L11-11 verbatim
namespace ExactModuli.KW

-- @@ L12-12 verbatim
section CoordinateJoining

-- @@ L13-13 verbatim
variable {β : Type uBeta} {κ : Type uKappa} {ι : Type uIota} [Fintype β] [Fintype κ] [Fintype ι]


-- @@ L15-16 verbatim
def joinedCoordinates (d : β ⊕ (κ × ι) → ℕ) (ω : KWOmega) : cube β × (κ → cube ι) :=
  splitCoordinates (fun i => ω (d i))


-- @@ L18-20 verbatim
lemma joinedCoordinates_mp (d : β ⊕ (κ × ι) → ℕ) (hd : Function.Injective d) :
    MeasurePreserving (joinedCoordinates d) kwMeasure ((cubeMeasure β).prod (arrayMeasure κ ι)) :=
  splitCoordinates_mp.comp (finite_coordinates_mp d hd)


-- @@ L22-24 verbatim
def joinedL1 (d : β ⊕ (κ × ι) → ℕ) (hd : Function.Injective d) :
    Lp ℝ 1 ((cubeMeasure β).prod (arrayMeasure κ ι)) →ₗᵢ[ℝ] KWL1 :=
  Lp.compMeasurePreservingₗᵢ ℝ _ (joinedCoordinates_mp d hd)


-- @@ L26-30 verbatim
lemma joinedL1_range (d : β ⊕ (κ × ι) → ℕ) (hd : Function.Injective d) :
    (joinedL1 d hd).toLinearMap.range ≤ (coordinatesL1 d hd).toLinearMap.range := by
  rintro g ⟨f, rfl⟩
  refine ⟨Lp.compMeasurePreserving splitCoordinates splitCoordinates_mp f, ?_⟩
  exact (Lp.compMeasurePreserving_comp_apply f splitCoordinates_mp (finite_coordinates_mp d hd)).symm


-- @@ L32-43 verbatim
lemma joinedL1_old (c : β → ℕ) (hc : Function.Injective c)
    (d : β ⊕ (κ × ι) → ℕ) (hd : Function.Injective d) (hdc : ∀ b, d (Sum.inl b) = c b)
    (f : Lp ℝ 1 (cubeMeasure β)) :
    joinedL1 d hd (oldL1 f) = coordinatesL1 c hc f := by
  change (Lp.compMeasurePreserving (joinedCoordinates d) (joinedCoordinates_mp d hd))
      ((Lp.compMeasurePreserving Prod.fst measurePreserving_fst) f) = _
  rw [← Lp.compMeasurePreserving_comp_apply f measurePreserving_fst (joinedCoordinates_mp d hd)]
  have he : Prod.fst ∘ joinedCoordinates d = (fun ω : KWOmega => fun b => ω (c b)) := by
    funext ω b
    simp only [Function.comp_apply, joinedCoordinates, splitCoordinates, hdc]
  simp only [he]
  rfl


-- @@ L45-49 verbatim
lemma joinedL1_measureDistance (d : β ⊕ (κ × ι) → ℕ) (hd : Function.Injective d)
    (f g : Lp ℝ 1 ((cubeMeasure β).prod (arrayMeasure κ ι))) :
    measureDistance kwMeasure (joinedL1 d hd f) (joinedL1 d hd g) =
      measureDistance ((cubeMeasure β).prod (arrayMeasure κ ι)) f g :=
  measureDistance_pullback (joinedCoordinates_mp d hd) f g


-- @@ L51-51 verbatim
end CoordinateJoining


-- @@ L53-53 verbatim
section Model

-- @@ L54-55 verbatim
variable {X : Type uX} {Y : Type uY} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]


-- @@ L57-65 verbatim
lemma finiteDimensional_model (L : X →ₗᵢ[ℝ] Y) (G : Submodule ℝ Y) [FiniteDimensional ℝ G] :
    FiniteDimensional ℝ (G.comap L.toLinearMap) := by
  let T : G.comap L.toLinearMap →ₗ[ℝ] G :=
    (L.toLinearMap.domRestrict (G.comap L.toLinearMap)).codRestrict G (fun x => x.property)
  apply FiniteDimensional.of_injective T
  intro x y h
  apply Subtype.ext
  apply L.injective
  exact congrArg Subtype.val h


-- @@ L67-67 verbatim
end Model


-- @@ L69-69 verbatim
section ProductBasis

-- @@ L70-70 verbatim
variable {B : Type uB} [MeasurableSpace B] {μ : Measure B} [IsProbabilityMeasure μ]

-- @@ L71-71 verbatim
variable {κ : Type uKappa} {ι : Type uIota} [Fintype κ] [Fintype ι]


-- @@ L73-79 verbatim
omit [IsProbabilityMeasure μ] in
lemma productOperator_single [IsProbabilityMeasure μ] {p : ℝ} (hp : 1 < p)
    (u : κ → Lp ℝ 1 μ) (k : κ) (j : ι) :
    ∃ a : κ → ι → ℝ, productOperator hp u (0,a) = atomL1 hp (u k) k j := by
  classical
  refine ⟨fun k' j' => if k' = k then (if j' = j then 1 else 0) else 0, ?_⟩
  simp [productOperator, matrixCombination, ite_smul]


-- @@ L81-81 verbatim
end ProductBasis

-- @@ L82-82 verbatim
end ExactModuli.KW


-- @@ L84-84 verbatim
end


-- @@ L86-86 verbatim
end OAI
