/-
Copyright (c) 2026 mathlib-initiative. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: mathlib-initiative
-/

import RepresentationTheory.FiniteIntegerMatrixModels
import RepresentationTheory.AuxiliaryFiniteSetMembership
import RepresentationTheory.ThreeArrowQuiver.LinearRangeConfiguration
import RepresentationTheory.Quiver.DimensionVectorClassification
import RepresentationTheory.Alignment.Attribute


-- @@ L13-15 verbatim
/-!
# Four-vertex star representation classification
-/


-- @@ L17-17 verbatim
namespace RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations.FourVertexStarRepresentation


-- @@ L19-24 verbatim
/-- The vector space of a star-shaped representation at one of the four vertices. -/
abbrev vertexSpace {k : Type*} [Field k] (rho : RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations.FourVertexStarRepresentation k) : Fin 4 → Type _
  | 0 => rho.leafOne
  | 1 => rho.leafTwo
  | 2 => rho.leafThree
  | 3 => rho.center


-- @@ L26-30 verbatim
private theorem falseOfImpossibleArrow {a b : Fin 4}
    (e : @Quiver.Hom (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA a b)
    (h : RepresentationTheory.IntegerMatrices.integerMatrixA a b ≠ 1 ∨ ¬ a < b) : False := by
    rcases e with ⟨⟨hadj, hlt⟩⟩
    exact h.elim (fun hn => hn hadj) (fun hn => hn hlt)


-- @@ L32-62 verbatim
/-- Converts a star-shaped four-space representation into a representation of the fixed quiver. -/
noncomputable abbrev toQuiverRepresentation {k : Type*} [Field k] (rho : RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations.FourVertexStarRepresentation k) :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA :=
  @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.mk k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA (vertexSpace rho)
    (fun v => match v with
      | 0 => rho.leafOneAddCommGroup.toAddCommMonoid
      | 1 => rho.leafTwoAddCommGroup.toAddCommMonoid
      | 2 => rho.leafThreeAddCommGroup.toAddCommMonoid
      | 3 => rho.centerAddCommGroup.toAddCommMonoid)
    (fun v => match v with
      | 0 => rho.leafOneModule
      | 1 => rho.leafTwoModule
      | 2 => rho.leafThreeModule
      | 3 => rho.centerModule)
    (fun {a b} e => match a, b with
      | 0, 0 => False.elim (falseOfImpossibleArrow e (by decide))
      | 0, 1 => False.elim (falseOfImpossibleArrow e (by decide))
      | 0, 2 => False.elim (falseOfImpossibleArrow e (by decide))
      | 0, 3 => rho.leafOneToCenter
      | 1, 0 => False.elim (falseOfImpossibleArrow e (by decide))
      | 1, 1 => False.elim (falseOfImpossibleArrow e (by decide))
      | 1, 2 => False.elim (falseOfImpossibleArrow e (by decide))
      | 1, 3 => rho.leafTwoToCenter
      | 2, 0 => False.elim (falseOfImpossibleArrow e (by decide))
      | 2, 1 => False.elim (falseOfImpossibleArrow e (by decide))
      | 2, 2 => False.elim (falseOfImpossibleArrow e (by decide))
      | 2, 3 => rho.leafThreeToCenter
      | 3, 0 => False.elim (falseOfImpossibleArrow e (by decide))
      | 3, 1 => False.elim (falseOfImpossibleArrow e (by decide))
      | 3, 2 => False.elim (falseOfImpossibleArrow e (by decide))
      | 3, 3 => False.elim (falseOfImpossibleArrow e (by decide)))


-- @@ L64-70 verbatim
/-- The additive commutative monoid structure on a vertex space of the associated quiver representation. -/
noncomputable instance vertexAddCommMonoid {k : Type*} [Field k]
    (rho : RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations.FourVertexStarRepresentation k) (v : Fin 4) : AddCommMonoid
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
        rho.toQuiverRepresentation v) :=
  @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.addCommMonoid k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
    rho.toQuiverRepresentation v


-- @@ L72-78 verbatim
/-- The scalar module structure on a vertex space of the associated quiver representation. -/
noncomputable instance vertexModule {k : Type*} [Field k]
    (rho : RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations.FourVertexStarRepresentation k) (v : Fin 4) : Module k
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
        rho.toQuiverRepresentation v) :=
  @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.moduleInstance k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
    rho.toQuiverRepresentation v


-- @@ L80-85 verbatim
/-- Each vertex space of the associated quiver representation is a free module. -/
noncomputable instance vertexModuleFree {k : Type*} [Field k]
    (rho : RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations.FourVertexStarRepresentation k) (v : Fin 4) : Module.Free k
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
        rho.toQuiverRepresentation v) := by
  fin_cases v <;> infer_instance


-- @@ L87-92 verbatim
/-- Each vertex space of the associated quiver representation is a finite module. -/
noncomputable instance vertexModuleFinite {k : Type*} [Field k]
    (rho : RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations.FourVertexStarRepresentation k) (v : Fin 4) : Module.Finite k
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
        rho.toQuiverRepresentation v) := by
  fin_cases v <;> infer_instance


-- @@ L94-109 verbatim
/-- An equivalence between two four-space star-shaped representations. -/
structure Equiv {k : Type*} [Field k] (rho sigma : RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations.FourVertexStarRepresentation k) where
  /-- The linear equivalence on the center space of equivalent star-shaped representations. -/
  centerLinearEquiv : rho.center ≃ₗ[k] sigma.center
  /-- The linear equivalence on the first leaf space of equivalent star-shaped representations. -/
  leafOneLinearEquiv : rho.leafOne ≃ₗ[k] sigma.leafOne
  /-- The linear equivalence on the second leaf space of equivalent star-shaped representations. -/
  leafTwoLinearEquiv : rho.leafTwo ≃ₗ[k] sigma.leafTwo
  /-- The linear equivalence on the third leaf space of equivalent star-shaped representations. -/
  leafThreeLinearEquiv : rho.leafThree ≃ₗ[k] sigma.leafThree
  /-- The center and first-leaf equivalences intertwine the first leaf-to-center structure map. -/
  leafOne_comm_apply : ∀ x, centerLinearEquiv (rho.leafOneToCenter x) = sigma.leafOneToCenter (leafOneLinearEquiv x)
  /-- The center and second-leaf equivalences intertwine the second leaf-to-center structure map. -/
  leafTwo_comm_apply : ∀ x, centerLinearEquiv (rho.leafTwoToCenter x) = sigma.leafTwoToCenter (leafTwoLinearEquiv x)
  /-- The center and third-leaf equivalences intertwine the third leaf-to-center structure map. -/
  leafThree_comm_apply : ∀ x, centerLinearEquiv (rho.leafThreeToCenter x) = sigma.leafThreeToCenter (leafThreeLinearEquiv x)


-- @@ L111-124 verbatim
/-- An equivalence between the associated quiver representations induces an equivalence of the original star-shaped representations. -/
noncomputable def equivOfQuiverRepresentationEquiv {k : Type*} [Field k] {rho sigma : RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations.FourVertexStarRepresentation k}
    (f : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryData k _ (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
      rho.toQuiverRepresentation sigma.toQuiverRepresentation) : Equiv rho sigma where
  centerLinearEquiv := @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryData.linearEquivAt k _ (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA _ _ f 3
  leafOneLinearEquiv := @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryData.linearEquivAt k _ (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA _ _ f 0
  leafTwoLinearEquiv := @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryData.linearEquivAt k _ (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA _ _ f 1
  leafThreeLinearEquiv := @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryData.linearEquivAt k _ (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA _ _ f 2
  leafOne_comm_apply := fun x => @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryData.linearEquivAt_map k _ (Fin 4)
    RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA _ _ f 0 3 RepresentationTheory.ThreeArrowQuiver.LinearRangeConfiguration.zeroToSink x
  leafTwo_comm_apply := fun x => @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryData.linearEquivAt_map k _ (Fin 4)
    RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA _ _ f 1 3 RepresentationTheory.ThreeArrowQuiver.LinearRangeConfiguration.oneToSink x
  leafThree_comm_apply := fun x => @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryData.linearEquivAt_map k _ (Fin 4)
    RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA _ _ f 2 3 RepresentationTheory.ThreeArrowQuiver.LinearRangeConfiguration.twoToSink x


-- @@ L126-161 verbatim
/-- An indecomposable star-shaped representation yields an indecomposable associated quiver representation. -/
theorem toQuiverRepresentation_isIndecomposable {k : Type*} [Field k]
    {rho : RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations.FourVertexStarRepresentation k} (h : rho.IsIndecomposable) :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryCondition k _ (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
      rho.toQuiverRepresentation := by
  constructor
  · rcases h.1 with hV | h₁ | h₂ | h₃
    · exact ⟨3, Module.finrank_pos_iff.mp hV⟩
    · exact ⟨0, Module.finrank_pos_iff.mp h₁⟩
    · exact ⟨1, Module.finrank_pos_iff.mp h₂⟩
    · exact ⟨2, Module.finrank_pos_iff.mp h₃⟩
  · intro W₁ W₂ hW₁ hW₂ hcompl
    have hd := h.2 (W₁ 3) (W₂ 3) (W₁ 0) (W₂ 0)
      (W₁ 1) (W₂ 1) (W₁ 2) (W₂ 2)
      (hcompl 3) (hcompl 0) (hcompl 1) (hcompl 2)
      (fun x hx => hW₁ RepresentationTheory.ThreeArrowQuiver.LinearRangeConfiguration.zeroToSink x hx)
      (fun x hx => hW₂ RepresentationTheory.ThreeArrowQuiver.LinearRangeConfiguration.zeroToSink x hx)
      (fun x hx => hW₁ RepresentationTheory.ThreeArrowQuiver.LinearRangeConfiguration.oneToSink x hx)
      (fun x hx => hW₂ RepresentationTheory.ThreeArrowQuiver.LinearRangeConfiguration.oneToSink x hx)
      (fun x hx => hW₁ RepresentationTheory.ThreeArrowQuiver.LinearRangeConfiguration.twoToSink x hx)
      (fun x hx => hW₂ RepresentationTheory.ThreeArrowQuiver.LinearRangeConfiguration.twoToSink x hx)
    rcases hd with ⟨hV, h₁, h₂, h₃⟩ | ⟨hV, h₁, h₂, h₃⟩
    · left
      intro v
      fin_cases v
      · exact h₁
      · exact h₂
      · exact h₃
      · exact hV
    · right
      intro v
      fin_cases v
      · exact h₁
      · exact h₂
      · exact h₃
      · exact hV


-- @@ L163-226 verbatim
/-- Indecomposability of the associated quiver representation implies indecomposability of the original star-shaped representation. -/
theorem isIndecomposable_of_toQuiverRepresentation {k : Type*} [Field k]
    {rho : RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations.FourVertexStarRepresentation k}
    (h : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryCondition k _ (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
      rho.toQuiverRepresentation) : rho.IsIndecomposable := by
  constructor
  · obtain ⟨v, hv⟩ := h.1
    fin_cases v
    · exact Or.inr (Or.inl (Module.finrank_pos_iff.mpr hv))
    · exact Or.inr (Or.inr (Or.inl (Module.finrank_pos_iff.mpr hv)))
    · exact Or.inr (Or.inr (Or.inr (Module.finrank_pos_iff.mpr hv)))
    · exact Or.inl (Module.finrank_pos_iff.mpr hv)
  · intro p q p₁ q₁ p₂ q₂ p₃ q₃ hpq hpq₁ hpq₂ hpq₃
      hp₁ hq₁ hp₂ hq₂ hp₃ hq₃
    let W₁ : ∀ v, Submodule k
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
          rho.toQuiverRepresentation v) := fun v => match v with
      | 0 => p₁
      | 1 => p₂
      | 2 => p₃
      | 3 => p
    let W₂ : ∀ v, Submodule k
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
          rho.toQuiverRepresentation v) := fun v => match v with
      | 0 => q₁
      | 1 => q₂
      | 2 => q₃
      | 3 => q
    have hW₁ : ∀ {a b : Fin 4} (e : @Quiver.Hom (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA a b), ∀ x ∈ W₁ a,
        @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
          rho.toQuiverRepresentation a b e x ∈ W₁ b := by
      intro a b e x hx
      rcases RepresentationTheory.ThreeArrowQuiver.LinearRangeConfiguration.hom_eq_zeroToSink_or_oneToSink_or_twoToSink e with
        ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩
      · cases he
        exact hp₁ x hx
      · cases he
        exact hp₂ x hx
      · cases he
        exact hp₃ x hx
    have hW₂ : ∀ {a b : Fin 4} (e : @Quiver.Hom (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA a b), ∀ x ∈ W₂ a,
        @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.map k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
          rho.toQuiverRepresentation a b e x ∈ W₂ b := by
      intro a b e x hx
      rcases RepresentationTheory.ThreeArrowQuiver.LinearRangeConfiguration.hom_eq_zeroToSink_or_oneToSink_or_twoToSink e with
        ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩ | ⟨rfl, rfl, he⟩
      · cases he
        exact hq₁ x hx
      · cases he
        exact hq₂ x hx
      · cases he
        exact hq₃ x hx
    have hcompl : ∀ v, IsCompl (W₁ v) (W₂ v) := by
      intro v
      fin_cases v
      · exact hpq₁
      · exact hpq₂
      · exact hpq₃
      · exact hpq
    rcases h.2 W₁ W₂ hW₁ hW₂ hcompl with hbot | hbot
    · left
      exact ⟨hbot 3, hbot 0, hbot 1, hbot 2⟩
    · right
      exact ⟨hbot 3, hbot 0, hbot 1, hbot 2⟩


-- @@ L228-229 verbatim
/-- The type of admissible four-coordinate dimension data for the fixed representation shape. -/
abbrev AdmissibleDimension := {d // d ∈ RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations.fourVertexDimensionTuples}


-- @@ L231-236 verbatim
/-- Converts a four-component nested tuple of natural numbers into an integer-valued function on four vertices. -/
def tupleToDimensionVector (d : ℕ × ℕ × ℕ × ℕ) : Fin 4 → ℤ
  | 0 => d.2.1
  | 1 => d.2.2.1
  | 2 => d.2.2.2
  | 3 => d.1


-- @@ L238-252 verbatim
/-- The conversion from four-component tuples to integer-valued dimension vectors is injective. -/
theorem tupleToDimensionVector_injective : Function.Injective tupleToDimensionVector := by
  intro d e h
  rcases d with ⟨d, d₁, d₂, d₃⟩
  rcases e with ⟨e, e₁, e₂, e₃⟩
  have h₀ := congr_fun h 0
  have h₁ := congr_fun h 1
  have h₂ := congr_fun h 2
  have h₃ := congr_fun h 3
  simp only [tupleToDimensionVector, Int.ofNat_inj] at h₀ h₁ h₂ h₃
  subst e
  subst e₁
  subst e₂
  subst e₃
  rfl


-- @@ L254-260 verbatim
/-- The fixed four-by-four integer matrix satisfies the designated matrix condition. -/
theorem adjacencyMatrix_satisfies_condition : RepresentationTheory.AuxiliaryIntegerMatrixProperty.IsAuxiliaryMatrix 4 RepresentationTheory.IntegerMatrices.integerMatrixA := by
  let sigma : Fin 4 ≃ Fin 4 := Equiv.swap 1 3
  apply RepresentationTheory.FiniteIntegerMatrixModels.matrixCondition_of_relabeling sigma
    (adj := RepresentationTheory.FiniteIntegerMatrixModels.FiniteMatrixModel.matrix (.D 4 (by omega)))
  · decide
  · exact RepresentationTheory.FiniteIntegerMatrixModels.matrix_satisfies_condition (.D 4 (by omega))


-- @@ L262-264 verbatim
/-- The fixed four-vertex quiver and its integer matrix satisfy the designated compatibility condition. -/
theorem adjacencyMatrix_isCompatible : RepresentationTheory.Quiver.MatrixOrientation.IsMatrixOrientation RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA RepresentationTheory.IntegerMatrices.integerMatrixA :=
  RepresentationTheory.Quiver.MatrixOrientation.quiverOfAdjacencyMatrix_isMatrixOrientation RepresentationTheory.IntegerMatrices.integerMatrixA (by decide) (by decide)


-- @@ L266-269 verbatim
/-- Every arrow type between two vertices of the fixed four-vertex quiver is a subsingleton. -/
instance hom_subsingleton (a b : Fin 4) :
    Subsingleton (@Quiver.Hom (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA a b) :=
  inferInstance


-- @@ L271-287 verbatim
/-- Every admissible dimension satisfies the required integer matrix-vector condition. -/
theorem admissibleDimension_satisfies_condition (d : AdmissibleDimension) :
    RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition 4 RepresentationTheory.IntegerMatrices.integerMatrixA (tupleToDimensionVector d.1) := by
  rcases d with ⟨d, hd⟩
  change RepresentationTheory.IntegerMatrixVectorPredicates.integerMatrixVectorCondition 4 RepresentationTheory.IntegerMatrices.integerMatrixA (tupleToDimensionVector d)
  simp only [RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations.fourVertexDimensionTuples, Finset.mem_insert,
    Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    constructor
    · constructor
      · intro hzero
        have hsum := congr_arg (fun x : Fin 4 → ℤ => x 0 + x 1 + x 2 + x 3) hzero
        norm_num [tupleToDimensionVector] at hsum
      · decide
    · intro i
      fin_cases i <;> norm_num [tupleToDimensionVector]


-- @@ L289-289 verbatim
universe u


-- @@ L291-297 verbatim
/-- The predicate that a quiver representation satisfies the designated freeness condition at a vertex. -/
abbrev IsVertexFree {k : Type u} [Field k]
    (rho : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u, 0, u, 0} k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA)
    (v : Fin 4) : Prop :=
  @Module.Free k (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA rho v) _
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.addCommMonoid k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA rho v)
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.moduleInstance k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA rho v)


-- @@ L299-305 verbatim
/-- The predicate that a quiver representation satisfies the designated finiteness condition at a vertex. -/
abbrev IsVertexFinite {k : Type u} [Field k]
    (rho : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u, 0, u, 0} k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA)
    (v : Fin 4) : Prop :=
  @Module.Finite k (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA rho v) _
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.addCommMonoid k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA rho v)
    (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.moduleInstance k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA rho v)


-- @@ L307-321 verbatim
/-- Data realizing an admissible four-coordinate dimension by a representation over a field. -/
structure DimensionRealization (k : Type u) [Field k] (d : AdmissibleDimension) where
  /-- The four-vertex quiver representation determined by a dimension realization. -/
  toRepresentation : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u, 0, u, 0} k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
  /-- Every vertex of the representation associated with a dimension realization satisfies the free-vertex condition. -/
  [vertexFree : ∀ v, IsVertexFree toRepresentation v]
  /-- Every vertex of the representation associated with a dimension realization satisfies the finite-vertex condition. -/
  [vertexFinite : ∀ v, IsVertexFinite toRepresentation v]
  /-- The representation associated with a dimension realization is indecomposable. -/
  isIndecomposable : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryCondition k _ (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
    toRepresentation
  /-- The dimension of the realized representation at each vertex agrees with the corresponding coordinate of the prescribed dimension data. -/
  dimension_apply : ∀ v, tupleToDimensionVector d.1 v =
    (Module.finrank k
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA toRepresentation v) : ℤ)


-- @@ L323-323 verbatim
attribute [instance] DimensionRealization.vertexFree DimensionRealization.vertexFinite


-- @@ L325-337 verbatim
private theorem canonicalData_nonempty (k : Type u) [Field k] (d : AdmissibleDimension) :
    Nonempty (DimensionRealization k d) := by
  rcases (RepresentationTheory.Quiver.DimensionVectorClassification.Quiver.exists_finrankVector_and_related_of_vectorPredicate adjacencyMatrix_satisfies_condition k adjacencyMatrix_isCompatible
    (tupleToDimensionVector d.1) (admissibleDimension_satisfies_condition d)).1 with
    ⟨rho, hfree, hfinite, hind, hdim⟩
  exact ⟨{
    toRepresentation := rho
    vertexFree := hfree
    vertexFinite := hfinite
    isIndecomposable := hind
    dimension_apply := by
      intro v
      simpa using hdim v }⟩


-- @@ L339-342 verbatim
/-- The canonical realization of an admissible dimension over a field. -/
noncomputable def canonicalDimensionRealization (k : Type u) [Field k] (d : AdmissibleDimension) :
    DimensionRealization k d :=
  Classical.choice (canonicalData_nonempty k d)


-- @@ L344-348 verbatim
/-- The standard four-vertex quiver representation associated with an admissible dimension. -/
@[source_ref "Chapter6/Example6.3.1" (role := supporting)]
noncomputable abbrev standardRepresentation (k : Type u) [Field k] (d : AdmissibleDimension) :
    @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.{u, 0, u, 0} k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA :=
  (canonicalDimensionRealization k d).toRepresentation


-- @@ L350-353 verbatim
/-- The standard representation satisfies the free-vertex condition at every vertex. -/
noncomputable instance standardRepresentation_isVertexFree (k : Type u) [Field k]
    (d : AdmissibleDimension) (v : Fin 4) : IsVertexFree (standardRepresentation k d) v :=
  (canonicalDimensionRealization k d).vertexFree v


-- @@ L355-358 verbatim
/-- The standard representation satisfies the finite-vertex condition at every vertex. -/
noncomputable instance standardRepresentation_isVertexFinite (k : Type u) [Field k]
    (d : AdmissibleDimension) (v : Fin 4) : IsVertexFinite (standardRepresentation k d) v :=
  (canonicalDimensionRealization k d).vertexFinite v


-- @@ L360-365 verbatim
/-- Every standard representation indexed by an admissible dimension is indecomposable. -/
@[source_ref "Chapter6/Example6.3.1" (role := supporting)]
theorem standardRepresentation_isIndecomposable (k : Type u) [Field k]
    (d : AdmissibleDimension) : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryCondition k _ (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
      (standardRepresentation k d) :=
  (canonicalDimensionRealization k d).isIndecomposable


-- @@ L367-373 verbatim
/-- At each vertex, the standard representation has the coordinate prescribed by its admissible dimension. -/
theorem standardRepresentation_dimension_apply (k : Type u) [Field k]
    (d : AdmissibleDimension) (v : Fin 4) :
    tupleToDimensionVector d.1 v =
      (Module.finrank k
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA (standardRepresentation k d) v) : ℤ) :=
  (canonicalDimensionRealization k d).dimension_apply v


-- @@ L375-382 verbatim
/-- The converted dimension tuple of a representation agrees vertexwise with the dimension of its associated quiver representation. -/
theorem toQuiverRepresentation_dimension_apply {k : Type} [Field k]
    (rho : RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations.FourVertexStarRepresentation.{0, 0, 0, 0, 0} k) (v : Fin 4) :
    tupleToDimensionVector rho.dimension v =
      (Module.finrank k
        (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA rho.toQuiverRepresentation v) : ℤ) := by
  fin_cases v <;>
    simp [tupleToDimensionVector, RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations.FourVertexStarRepresentation.dimension, toQuiverRepresentation, vertexSpace]


-- @@ L384-387 verbatim
/-- The admissible dimension indexing an indecomposable star-shaped representation. -/
noncomputable def classificationIndex {k : Type} [Field k]
    (rho : RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations.FourVertexStarRepresentation.{0, 0, 0, 0, 0} k) (h : rho.IsIndecomposable) : AdmissibleDimension :=
  ⟨rho.dimension, RepresentationTheory.AuxiliaryFiniteSetMembership.auxiliary_value_mem_finset_of_property k rho h⟩


-- @@ L389-402 verbatim
/-- An indecomposable representation is equivalent to the standard representation indexed by its classification dimension. -/
theorem equiv_standardRepresentation_classificationIndex {k : Type} [Field k]
    (rho : RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations.FourVertexStarRepresentation.{0, 0, 0, 0, 0} k) (h : rho.IsIndecomposable) :
    Nonempty (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryData k _ (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
      rho.toQuiverRepresentation (standardRepresentation k (classificationIndex rho h))) := by
  let d := classificationIndex rho h
  apply (RepresentationTheory.Quiver.DimensionVectorClassification.Quiver.exists_finrankVector_and_related_of_vectorPredicate adjacencyMatrix_satisfies_condition k adjacencyMatrix_isCompatible
    (tupleToDimensionVector d.1) (admissibleDimension_satisfies_condition d)).2
  · exact toQuiverRepresentation_isIndecomposable h
  · exact standardRepresentation_isIndecomposable k d
  · intro v
    exact toQuiverRepresentation_dimension_apply rho v
  · intro v
    exact standardRepresentation_dimension_apply k d v


-- @@ L404-420 verbatim
private theorem canonical_index_eq_of_iso {k : Type} [Field k]
    {d e : AdmissibleDimension}
    (f : @RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryData k _ (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
      (standardRepresentation k d) (standardRepresentation k e)) : d = e := by
  apply Subtype.ext
  apply tupleToDimensionVector_injective
  funext v
  have hfin :
      Module.finrank k
          (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA (standardRepresentation k d) v) =
        Module.finrank k
          (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA (standardRepresentation k e) v) := by
    exact LinearEquiv.finrank_eq
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryData.linearEquivAt k _ (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA _ _ f v)
  exact (standardRepresentation_dimension_apply k d v).trans
    ((congr_arg (fun n : ℕ => (n : ℤ)) hfin).trans
      (standardRepresentation_dimension_apply k e v).symm)


-- @@ L422-429 verbatim
/-- Standard representations attached to distinct admissible dimensions are not equivalent. -/
@[source_ref "Chapter6/Example6.3.1" (role := supporting)]
theorem standardRepresentation_not_equiv_of_ne {k : Type} [Field k]
    {d e : AdmissibleDimension} (hde : d ≠ e) :
    ¬ Nonempty (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryData k _ (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
      (standardRepresentation k d) (standardRepresentation k e)) := by
  rintro ⟨f⟩
  exact hde (canonical_index_eq_of_iso f)


-- @@ L431-454 verbatim
/-- Every indecomposable representation is equivalent to a standard representation for a unique admissible dimension. -/
@[source_ref "Chapter6/Example6.3.1" (role := primary),
  source_ref "Chapter6/Discussion_after_Example6.3.1" (role := supporting)]
theorem existsUnique_equiv_standardRepresentation_of_isIndecomposable {k : Type} [Field k]
    (rho : RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations.FourVertexStarRepresentation.{0, 0, 0, 0, 0} k) (h : rho.IsIndecomposable) :
    ∃! d : AdmissibleDimension,
      Nonempty (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryData k _ (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA
        rho.toQuiverRepresentation (standardRepresentation k d)) := by
  refine ⟨classificationIndex rho h, equiv_standardRepresentation_classificationIndex rho h, ?_⟩
  intro e he
  obtain ⟨f⟩ := he
  apply Subtype.ext
  apply tupleToDimensionVector_injective
  funext v
  have hfin :
      Module.finrank k
          (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA rho.toQuiverRepresentation v) =
        Module.finrank k
          (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.obj k (Fin 4) _ RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA (standardRepresentation k e) v) := by
    exact LinearEquiv.finrank_eq
      (@RepresentationTheory.CategoryTheory.QuiverLinearDiagrams.AuxiliaryQuiverModuleData.AuxiliaryData.linearEquivAt k _ (Fin 4) RepresentationTheory.Quiver.FinFourLinearData.finFourQuiverA _ _ f v)
  exact (standardRepresentation_dimension_apply k e v).trans
    ((congr_arg (fun n : ℕ => (n : ℤ)) hfin).symm.trans
      (toQuiverRepresentation_dimension_apply rho v).symm)


-- @@ L456-460 verbatim
/-- There are exactly twelve admissible dimensions. -/
@[source_ref "Chapter6/Example6.3.1" (role := supporting)]
theorem card_admissibleDimension : Fintype.card AdmissibleDimension = 12 := by
  rw [Fintype.card_coe]
  exact RepresentationTheory.AuxiliaryFiniteSetMembership.auxiliary_finset_card_eq_twelve


-- @@ L462-462 verbatim
end RepresentationTheory.FiniteDimensionalFourVertexStarRepresentations.FourVertexStarRepresentation
