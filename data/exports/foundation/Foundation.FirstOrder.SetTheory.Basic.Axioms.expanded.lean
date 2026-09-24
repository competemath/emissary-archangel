module

public import Foundation.FirstOrder.SetTheory.Basic.Misc


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-10 verbatim
/-!
# Basic axioms of set theory

reference: Ralf Schindler, "Set Theory, Exploring Independence and Truth" [Sch14]
-/


-- @@ L12-12 verbatim
namespace FFL.FirstOrder.SetTheory


-- @@ L14-14 verbatim
def isSubsetOf : SetTheorySemisentence 2 := “x y. ∀ z ∈ x, z ∈ y”


-- @@ L16-16 verbatim
syntax:45 first_order_term:45 " ⊆ " first_order_term:0 : first_order_formula


-- @@ L18-21 verbatim
open Lean Elab PrettyPrinter Delaborator SubExpr in
macro_rules
  | `(⤫formula($type)[ $binders* | $fbinders* | $t:first_order_term ⊆ $u:first_order_term ]) =>
    `(⤫formula($type)[ $binders* | $fbinders* | !isSubsetOf $t:first_order_term $u:first_order_term ])


-- @@ L23-23 verbatim
def isEmpty : SetTheorySemisentence 1 := “x. ∀ y, y ∉ x”


-- @@ L25-25 verbatim
def isNonempty : SetTheorySemisentence 1 := “x. ∃ y, y ∈ x”


-- @@ L27-27 verbatim
def isSucc : SetTheorySemisentence 2 := “y x. ∀ z, z ∈ y ↔ z = x ∨ z ∈ x”


-- @@ L29-29 verbatim
namespace Axiom


-- @@ L31-32 verbatim
/-- Axiom of empty set. -/
def empty : SetTheorySentence := “∃ e, ∀ y, y ∉ e”


-- @@ L34-35 verbatim
/-- Axiom of extentionality. -/
def extentionality : SetTheorySentence := “∀ x y, x = y ↔ ∀ z, z ∈ x ↔ z ∈ y”


-- @@ L37-38 verbatim
/-- Axiom of pairing. -/
def pairing : SetTheorySentence := “∀ x y, ∃ z, ∀ w, w ∈ z ↔ w = x ∨ w = y”


-- @@ L40-41 verbatim
/-- Axiom of union. -/
def union : SetTheorySentence := “∀ x, ∃ y, ∀ z, z ∈ y ↔ ∃ w ∈ x, z ∈ w”


-- @@ L43-44 verbatim
/-- Axiom of power set. -/
def power : SetTheorySentence := “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ⊆ x”


-- @@ L46-47 verbatim
/-- Axiom of infinity. -/
def infinity : SetTheorySentence := “∃ I, (∀ e, !isEmpty e → e ∈ I) ∧ (∀ x ∈ I, ∀ x', !isSucc x' x → x' ∈ I)”


-- @@ L49-50 verbatim
/-- Axiom of foundation. -/
def foundation : SetTheorySentence := “∀ x, !isNonempty x → ∃ y ∈ x, ∀ z ∈ x, z ∉ y”


-- @@ L52-54 verbatim
/-- Axiom schema of separation (Aussonderungsaxiom). -/
def separationSchema (φ : SetTheorySemiproposition 1) : SetTheorySentence :=
  .univCl “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ∈ x ∧ !φ z”


-- @@ L56-58 verbatim
/-- Axiom schema of replacement. -/
def replacementSchema (φ : SetTheorySemiproposition 2) : SetTheorySentence :=
  .univCl “(∀ x, ∃! y, !φ x y) → ∀ X, ∃ Y, ∀ y, y ∈ Y ↔ ∃ x ∈ X, !φ x y”


-- @@ L60-62 verbatim
/-- Axiom of choice. -/
def choice : SetTheorySentence :=
  “∀ 𝓧, (∀ X ∈ 𝓧, !isNonempty X) ∧ (∀ X ∈ 𝓧, ∀ Y ∈ 𝓧, (∃ z, z ∈ X ∧ z ∈ Y) → X = Y) → ∃ C, ∀ X ∈ 𝓧, ∃! x, x ∈ C ∧ x ∈ X”


-- @@ L64-64 verbatim
end Axiom


-- @@ L66-66 verbatim
/-! ### Zermelo set theory-/


-- @@ L68-71 verbatim
/-- Zermelo set theory. -/
inductive Zermelo : SetTheory
  /-- Axiom of equality. -/
  | axiom_of_equality : ∀ φ ∈ 𝗘𝗤 ℒₛₑₜ, Zermelo φ
  
-- @@ L72-73 verbatim
/-- Axiom of empty set. -/
  | axiom_of_empty_set : Zermelo Axiom.empty
  
-- @@ L74-75 verbatim
/-- Axiom of extentionality. -/
  | axiom_of_extentionality : Zermelo Axiom.extentionality
  
-- @@ L76-77 verbatim
/-- Axiom of pairing. -/
  | axiom_of_pairing : Zermelo Axiom.pairing
  
-- @@ L78-79 verbatim
/-- Axiom of empty union. -/
  | axiom_of_union : Zermelo Axiom.union
  
-- @@ L80-81 verbatim
/-- Axiom of power set. -/
  | axiom_of_power_set : Zermelo Axiom.power
  
-- @@ L82-83 verbatim
/-- Axiom of infinity. -/
  | axiom_of_infinity : Zermelo Axiom.infinity
  
-- @@ L84-85 verbatim
/-- Axiom of foundation. -/
  | axiom_of_foundation : Zermelo Axiom.foundation
  
-- @@ L86-87 verbatim
/-- Axiom schema of separation. -/
  | axiom_of_separation (φ : SetTheorySemiproposition 1) : Zermelo (Axiom.separationSchema φ)


-- @@ L89-89 verbatim
notation "𝗭" => Zermelo


-- @@ L91-91 verbatim
instance : 𝗘𝗤 _ ⪯ 𝗭 := Entailment.WeakerThan.ofSubset Zermelo.axiom_of_equality


-- @@ L93-93 verbatim
/-! ### Zermelo-Fraenkel set theory -/


-- @@ L95-98 verbatim
/-- Zermelo-Fraenkel set theory. -/
inductive ZermeloFraenkel : SetTheory
  /-- Axiom of equality. -/
  | axiom_of_equality : ∀ φ ∈ 𝗘𝗤 ℒₛₑₜ, ZermeloFraenkel φ
  
-- @@ L99-100 verbatim
/-- Axiom of empty set. -/
  | axiom_of_empty_set : ZermeloFraenkel Axiom.empty
  
-- @@ L101-102 verbatim
/-- Axiom of extentionality. -/
  | axiom_of_extentionality : ZermeloFraenkel Axiom.extentionality
  
-- @@ L103-104 verbatim
/-- Axiom of pairing. -/
  | axiom_of_pairing : ZermeloFraenkel Axiom.pairing
  
-- @@ L105-106 verbatim
/-- Axiom of union. -/
  | axiom_of_union : ZermeloFraenkel Axiom.union
  
-- @@ L107-108 verbatim
/-- Axiom of power set. -/
  | axiom_of_power_set : ZermeloFraenkel Axiom.power
  
-- @@ L109-110 verbatim
/-- Axiom of infinity. -/
  | axiom_of_infinity : ZermeloFraenkel Axiom.infinity
  
-- @@ L111-112 verbatim
/-- Axiom of foundation. -/
  | axiom_of_foundation : ZermeloFraenkel Axiom.foundation
  
-- @@ L113-114 verbatim
/-- Axiom schema of separation. -/
  | axiom_of_separation (φ : SetTheorySemiproposition 1) : ZermeloFraenkel (Axiom.separationSchema φ)
  
-- @@ L115-116 verbatim
/-- Axiom schema of replacement. -/
  | axiom_of_replacement (φ : SetTheorySemiproposition 2) : ZermeloFraenkel (Axiom.replacementSchema φ)


-- @@ L118-118 verbatim
notation "𝗭𝗙" => ZermeloFraenkel


-- @@ L120-132 verbatim
instance : 𝗘𝗤 _ ⪯ 𝗭𝗙 := Entailment.WeakerThan.ofSubset ZermeloFraenkel.axiom_of_equality

lemma z_subset_zf : 𝗭 ⊆ 𝗭𝗙 := by
  rintro φ ⟨h⟩
  · exact ZermeloFraenkel.axiom_of_equality φ (by assumption)
  · exact ZermeloFraenkel.axiom_of_empty_set
  · exact ZermeloFraenkel.axiom_of_extentionality
  · exact ZermeloFraenkel.axiom_of_pairing
  · exact ZermeloFraenkel.axiom_of_union
  · exact ZermeloFraenkel.axiom_of_power_set
  · exact ZermeloFraenkel.axiom_of_infinity
  · exact ZermeloFraenkel.axiom_of_foundation
  · exact ZermeloFraenkel.axiom_of_separation _


-- @@ L134-134 verbatim
instance : 𝗭 ⪯ 𝗭𝗙 := Entailment.WeakerThan.ofSubset z_subset_zf


-- @@ L136-136 verbatim
/-! ### Zermelo set theory with axiom of choice -/


-- @@ L138-139 verbatim
/-- AC: Axiom of choice. -/
def AxiomOfChoice : SetTheory := {Axiom.choice}


-- @@ L141-141 verbatim
notation "𝗔𝗖" => AxiomOfChoice


-- @@ L143-144 verbatim
/-- Zermelo set theory with axiom of choice. -/
abbrev ZermeloChoice : SetTheory := 𝗭 ∪ 𝗔𝗖


-- @@ L146-146 verbatim
notation "𝗭𝗖" => ZermeloChoice


-- @@ L148-148 verbatim
instance : 𝗭 ⪯ 𝗭𝗖 := inferInstance


-- @@ L150-152 verbatim
instance : 𝗘𝗤 _ ⪯ 𝗭𝗖 :=
  let : 𝗘𝗤 _ ⪯ 𝗭 := inferInstance
  Entailment.WeakerThan.trans this inferInstance


-- @@ L154-154 verbatim
/-! ### Zermelo-Fraenkel set theory with axiom of choice -/


-- @@ L156-157 verbatim
/-- Zermelo-Fraenkel set theory with axiom of choice. -/
abbrev ZermeloFraenkelChoice : SetTheory := 𝗭𝗙 ∪ 𝗔𝗖


-- @@ L159-159 verbatim
notation "𝗭𝗙𝗖" => ZermeloFraenkelChoice


-- @@ L161-161 verbatim
instance : 𝗭𝗙 ⪯ 𝗭𝗙𝗖 := inferInstance


-- @@ L163-167 verbatim
instance : 𝗘𝗤 _ ⪯ 𝗭𝗙𝗖 :=
  let : 𝗘𝗤 _ ⪯ 𝗭𝗙 := inferInstance
  Entailment.WeakerThan.trans this inferInstance

lemma zc_subset_zfc : 𝗭𝗖 ⊆ 𝗭𝗙𝗖 := Set.union_subset_union_left _ z_subset_zf


-- @@ L169-169 verbatim
instance : 𝗭𝗖 ⪯ 𝗭𝗙𝗖 := Entailment.WeakerThan.ofSubset zc_subset_zfc


-- @@ L171-171 verbatim
instance : 𝗭 ⪯ 𝗭𝗙𝗖 := Entailment.WeakerThan.trans (inferInstance : 𝗭 ⪯ 𝗭𝗙) inferInstance


-- @@ L173-173 verbatim
end FFL.FirstOrder.SetTheory
