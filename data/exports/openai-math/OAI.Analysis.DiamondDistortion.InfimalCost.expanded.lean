import OAI.Analysis.DiamondDistortion.Vanishing


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
variable {E F : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [AddCommGroup F] [Module ℝ F]


-- @@ L19-25 verbatim
/-- Quotient construction of the exact infimum over all linear representations.
    No infimum or supremum is assumed to be attained. -/
structure Presentation (E F : Type*) [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [AddCommGroup F] [Module ℝ F] where
  output : E →ₗ[ℝ] F
  sectionMap : F →ₗ[ℝ] E
  right_inverse : ∀ v,output (sectionMap v)=v

-- @@ L26-26 verbatim
namespace Presentation

-- @@ L27-27 verbatim
variable (A : Presentation E F)

-- @@ L28-29 verbatim
def seminorm : Seminorm ℝ F :=
  (normSeminorm ℝ (E ⧸ LinearMap.ker A.output)).comp ((LinearMap.ker A.output).mkQ.comp A.sectionMap)

-- @@ L30-35 verbatim
lemma representation_eq {d : E} {v : F} (hd : A.output d=v) :
    (LinearMap.ker A.output).mkQ d=(LinearMap.ker A.output).mkQ (A.sectionMap v) := by
  change (Submodule.Quotient.mk d : E ⧸ LinearMap.ker A.output)=Submodule.Quotient.mk (A.sectionMap v)
  rw [Submodule.Quotient.eq]
  change A.output (d-A.sectionMap v)=0
  rw [map_sub,hd,A.right_inverse,sub_self]

-- @@ L36-39 verbatim
lemma le_representation {d : E} {v : F} (hd : A.output d=v) : A.seminorm v ≤ ‖d‖ := by
  change ‖(LinearMap.ker A.output).mkQ (A.sectionMap v)‖ ≤ ‖d‖
  rw [← A.representation_eq hd]
  exact Submodule.Quotient.norm_mk_le _ d

-- @@ L40-48 verbatim
lemma near_representation (v : F) {ε : ℝ} (hε : 0 < ε) :
    ∃ d : E,A.output d=v ∧ ‖d‖ < A.seminorm v+ε := by
  obtain ⟨d,hd,hb⟩ := Submodule.Quotient.norm_mk_lt
    ((LinearMap.ker A.output).mkQ (A.sectionMap v)) hε
  refine ⟨d,?_,hb⟩
  have hh : d-A.sectionMap v ∈ LinearMap.ker A.output := (Submodule.Quotient.eq _).mp hd
  change A.output (d-A.sectionMap v)=0 at hh
  rw [map_sub,A.right_inverse,sub_eq_zero] at hh
  exact hh

-- @@ L49-58 verbatim
lemma eq_sInf (v : F) : A.seminorm v=sInf {r : ℝ | ∃ d : E,A.output d=v ∧ ‖d‖=r} := by
  let costs := {r : ℝ | ∃ d : E,A.output d=v ∧ ‖d‖=r}
  have hn : costs.Nonempty := ⟨‖A.sectionMap v‖,A.sectionMap v,A.right_inverse v,rfl⟩
  have hb : BddBelow costs := ⟨0,by rintro r ⟨d,hd,rfl⟩; exact norm_nonneg d⟩
  apply le_antisymm
  · exact le_csInf hn (by rintro r ⟨d,hd,rfl⟩; exact A.le_representation hd)
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨d,hd,hh⟩ := A.near_representation v hε
    exact (csInf_le hb ⟨d,hd,rfl⟩).trans hh.le

-- @@ L59-70 verbatim
lemma bound (v : F) {C b : ℝ} (hC : 0 ≤ C) (hb : ∀ d : E,A.output d=v → b ≤ C*‖d‖) :
    b ≤ C*A.seminorm v := by
  by_cases hC0 : C=0
  · simpa only [hC0,zero_mul] using hb (A.sectionMap v) (A.right_inverse v)
  have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨d,hd,hh⟩ := A.near_representation v (div_pos hε hCpos)
  have he := (hb d hd).trans (mul_le_mul_of_nonneg_left hh.le hC)
  calc
    _ ≤ C*(A.seminorm v+ε/C) := he
    _ = C*A.seminorm v+ε := by field_simp

-- @@ L71-71 verbatim
end Presentation

-- @@ L72-72 verbatim
end InfimalCost


-- @@ L74-74 verbatim
end DiamondDistortion


-- @@ L76-76 verbatim
end


-- @@ L78-78 verbatim
end OAI
