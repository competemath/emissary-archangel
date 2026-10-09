import OAI.Analysis.DiamondDistortion.PathModels


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u v


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators Classical Topology

-- @@ L9-9 verbatim
open Set


-- @@ L11-11 verbatim
namespace DiamondDistortion


-- @@ L13-13 verbatim
open scoped ENNReal


-- @@ L15-15 verbatim
namespace InfimalCost

-- @@ L16-17 verbatim
variable {E F G : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G]

-- @@ L18-25 verbatim
/-- A prescribed output of finite input coordinates, allowing all countable
    finite-cost representations rather than only finite ones. -/
structure Relation (E F G : Type*) [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup F] [Module ℝ F] [AddCommGroup G] [Module ℝ G] where
  output : E →ₗ[ℝ] G
  value : F →ₗ[ℝ] G
  sectionMap : F →ₗ[ℝ] E
  section_output : ∀ v,output (sectionMap v)=value v

-- @@ L26-26 verbatim
namespace Relation

-- @@ L27-27 verbatim
variable (A : Relation E F G)

-- @@ L28-29 verbatim
def seminorm : Seminorm ℝ F :=
  (normSeminorm ℝ (E ⧸ LinearMap.ker A.output)).comp ((LinearMap.ker A.output).mkQ.comp A.sectionMap)

-- @@ L30-35 verbatim
lemma representation_eq {d : E} {v : F} (hd : A.output d=A.value v) :
    (LinearMap.ker A.output).mkQ d=(LinearMap.ker A.output).mkQ (A.sectionMap v) := by
  change (Submodule.Quotient.mk d : E ⧸ LinearMap.ker A.output)=Submodule.Quotient.mk (A.sectionMap v)
  rw [Submodule.Quotient.eq]
  change A.output (d-A.sectionMap v)=0
  rw [map_sub,hd,A.section_output,sub_self]

-- @@ L36-39 verbatim
lemma le_representation {d : E} {v : F} (hd : A.output d=A.value v) : A.seminorm v ≤ ‖d‖ := by
  change ‖(LinearMap.ker A.output).mkQ (A.sectionMap v)‖ ≤ ‖d‖
  rw [← A.representation_eq hd]
  exact Submodule.Quotient.norm_mk_le _ d

-- @@ L40-48 verbatim
lemma near_representation (v : F) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : E,A.output d=A.value v ∧ ‖d‖ < A.seminorm v+ε := by
  obtain ⟨d,hd,hb⟩ := Submodule.Quotient.norm_mk_lt
    ((LinearMap.ker A.output).mkQ (A.sectionMap v)) hε
  refine ⟨d,?_,hb⟩
  have hh : d-A.sectionMap v ∈ LinearMap.ker A.output := (Submodule.Quotient.eq _).mp hd
  change A.output (d-A.sectionMap v)=0 at hh
  rw [map_sub,A.section_output,sub_eq_zero] at hh
  exact hh

-- @@ L49-58 verbatim
lemma eq_sInf (v : F) : A.seminorm v=sInf {r : ℝ | ∃ d : E,A.output d=A.value v ∧ ‖d‖=r} := by
  let costs := {r : ℝ | ∃ d : E,A.output d=A.value v ∧ ‖d‖=r}
  have hn : costs.Nonempty := ⟨‖A.sectionMap v‖,A.sectionMap v,A.section_output v,rfl⟩
  have hb : BddBelow costs := ⟨0,by rintro r ⟨d,hd,rfl⟩; exact norm_nonneg d⟩
  apply le_antisymm
  · exact le_csInf hn (by rintro r ⟨d,hd,rfl⟩; exact A.le_representation hd)
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨d,hd,hh⟩ := A.near_representation v hε
    exact (csInf_le hb ⟨d,hd,rfl⟩).trans hh.le

-- @@ L59-64 verbatim
lemma bound (v : F) {b : ℝ} (hb : ∀ d : E,A.output d=A.value v → b ≤ ‖d‖) :
    b ≤ A.seminorm v := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨d,hd,hh⟩ := A.near_representation v hε
  exact (hb d hd).trans hh.le

-- @@ L65-65 verbatim
end Relation

-- @@ L66-66 verbatim
end InfimalCost


-- @@ L68-68 verbatim
end DiamondDistortion


-- @@ L70-70 verbatim
end


-- @@ L72-72 verbatim
end OAI
