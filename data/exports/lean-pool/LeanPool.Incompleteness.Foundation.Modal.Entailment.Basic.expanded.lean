/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Logic.Disjunctive
public import LeanPool.Incompleteness.Foundation.Modal.Axioms
public import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Context


-- @@ L12-12 verbatim
/-! # Basic -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
namespace LO

-- @@ L18-18 verbatim
namespace Entailment


-- @@ L20-20 verbatim
variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S]

-- @@ L21-21 verbatim
variable {𝓢 : S}



-- @@ L24-27 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class Necessitation (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  nec {φ : F} : Entailment.Prf 𝓢 φ → Entailment.Prf 𝓢 (Box.box φ)


-- @@ L29-29 verbatim
section «lp_section_1»


-- @@ L31-31 verbatim
variable [Necessitation 𝓢]

-- @@ L32-32 verbatim
alias nec := Necessitation.nec


-- @@ L34-34 expanded
lemma nec! : Provable 𝓢 φ → Provable 𝓢 (Box.box φ) := by rintro ⟨hp⟩; exact ⟨nec hp⟩


-- @@ L36-41 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def multinec : Entailment.Prf 𝓢 φ → Entailment.Prf 𝓢 (multibox n φ) := by intro h;
  induction n with
  | zero => simpa;
  | succ n ih => simpa using nec ih;


-- @@ L42-42 expanded
lemma multinec! : Provable 𝓢 φ → Provable 𝓢 (multibox n φ) := by rintro ⟨hp⟩; exact ⟨multinec hp⟩


-- @@ L44-44 verbatim
end «lp_section_1»



-- @@ L47-50 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class Unnecessitation (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  unnec {φ : F} : Entailment.Prf 𝓢 (Box.box φ) → Entailment.Prf 𝓢 φ


-- @@ L52-52 verbatim
section «lp_section_2»


-- @@ L54-54 verbatim
variable [Unnecessitation 𝓢]


-- @@ L56-56 verbatim
alias unnec := Unnecessitation.unnec

-- @@ L57-57 expanded
lemma unnec! : Provable 𝓢 (Box.box φ) → Provable 𝓢 φ := by rintro ⟨hp⟩; exact ⟨unnec hp⟩


-- @@ L59-64 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def multiunnec : Entailment.Prf 𝓢 (multibox n φ) → Entailment.Prf 𝓢 φ := by intro h;
  induction n generalizing φ with
  | zero => simpa;
  | succ n ih => exact unnec <| @ih (Box.box φ) h;


-- @@ L65-65 expanded
lemma multiunnec! : Provable 𝓢 (multibox n φ) → Provable 𝓢 φ := by rintro ⟨hp⟩;
  exact ⟨multiunnec hp⟩


-- @@ L67-67 verbatim
end «lp_section_2»



-- @@ L70-73 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class LoebRule [LogicalConnective F] (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  loeb {φ : F} : Entailment.Prf 𝓢 (Arrow.arrow (Box.box φ) φ) → Entailment.Prf 𝓢 φ


-- @@ L75-75 verbatim
section «lp_section_3»


-- @@ L77-77 verbatim
variable [LoebRule 𝓢]


-- @@ L79-79 verbatim
alias loeb := LoebRule.loeb

-- @@ L80-80 expanded
lemma loeb! : Provable 𝓢 (Arrow.arrow (Box.box φ) φ) → Provable 𝓢 φ := by rintro ⟨hp⟩;
  exact ⟨loeb hp⟩


-- @@ L82-82 verbatim
end «lp_section_3»



-- @@ L85-88 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HenkinRule [LogicalConnective F] (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  henkin {φ : F} : Entailment.Prf 𝓢 (LogicalConnective.iff (Box.box φ) φ) → Entailment.Prf 𝓢 φ


-- @@ L90-90 verbatim
section «lp_section_4»


-- @@ L92-92 verbatim
variable [HenkinRule 𝓢]


-- @@ L94-94 verbatim
alias henkin := HenkinRule.henkin

-- @@ L95-95 expanded
lemma henkin! : Provable 𝓢 (LogicalConnective.iff (Box.box φ) φ) → Provable 𝓢 φ := by rintro ⟨hp⟩;
  exact ⟨henkin hp⟩


-- @@ L97-97 verbatim
end «lp_section_4»




-- @@ L101-104 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasDiaDuality (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  diaDual (φ : F) : Entailment.Prf 𝓢 (Axioms.DiaDuality φ)


-- @@ L106-106 verbatim
section «lp_section_5»


-- @@ L108-108 verbatim
variable [HasDiaDuality 𝓢]


-- @@ L110-111 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def diaDuality :
    Entailment.Prf 𝓢 (LogicalConnective.iff (Dia.dia φ) (Tilde.tilde (Box.box (Tilde.tilde φ)))) :=
  HasDiaDuality.diaDual _


-- @@ L112-112 expanded
@[simp]
lemma dia_duality! :
    Provable 𝓢 (LogicalConnective.iff (Dia.dia φ) (Tilde.tilde (Box.box (Tilde.tilde φ)))) :=
  ⟨diaDuality⟩


-- @@ L114-114 verbatim
end «lp_section_5»




-- @@ L118-121 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomK [LogicalConnective F] [Box F] (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  K (φ ψ : F) : Entailment.Prf 𝓢 (Axioms.K φ ψ)


-- @@ L123-123 verbatim
section «lp_section_6»


-- @@ L125-125 verbatim
variable [HasAxiomK 𝓢]


-- @@ L127-128 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def axiomK :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box (Arrow.arrow φ ψ)) (Arrow.arrow (Box.box φ) (Box.box ψ))) :=
  HasAxiomK.K _ _


-- @@ L129-129 expanded
@[simp]
lemma axiomK! :
    Provable 𝓢 (Arrow.arrow (Box.box (Arrow.arrow φ ψ)) (Arrow.arrow (Box.box φ) (Box.box ψ))) :=
  ⟨axiomK⟩


-- @@ L131-131 verbatim
variable [Entailment.Minimal 𝓢]


-- @@ L133-133 verbatim
instance (Γ : FiniteContext F 𝓢) : HasAxiomK Γ := ⟨fun _ _ ↦ FiniteContext.of axiomK⟩

-- @@ L134-134 verbatim
instance (Γ : Context F 𝓢) : HasAxiomK Γ := ⟨fun _ _ ↦ Context.of axiomK⟩


-- @@ L136-137 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def axiomK' (h : Entailment.Prf 𝓢 (Box.box (Arrow.arrow φ ψ))) :
    Entailment.Prf 𝓢 (Arrow.arrow (Box.box φ) (Box.box ψ)) :=
  mdp axiomK h


-- @@ L138-138 expanded
@[simp 1100]
lemma axiomK'! (h : Provable 𝓢 (Box.box (Arrow.arrow φ ψ))) :
    Provable 𝓢 (Arrow.arrow (Box.box φ) (Box.box ψ)) :=
  ⟨axiomK' h.some⟩


-- @@ L140-141 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def axiomK'' (h₁ : Entailment.Prf 𝓢 (Box.box (Arrow.arrow φ ψ)))
    (h₂ : Entailment.Prf 𝓢 (Box.box φ)) : Entailment.Prf 𝓢 (Box.box ψ) :=
  mdp (axiomK' h₁) h₂


-- @@ L142-142 expanded
lemma axiomK''! (h₁ : Provable 𝓢 (Box.box (Arrow.arrow φ ψ))) (h₂ : Provable 𝓢 (Box.box φ)) :
    Provable 𝓢 (Box.box ψ) :=
  ⟨axiomK'' h₁.some h₂.some⟩


-- @@ L144-144 verbatim
end «lp_section_6»



-- @@ L147-150 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomT (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  T (φ : F) : Entailment.Prf 𝓢 (Axioms.T φ)


-- @@ L152-152 verbatim
section «lp_section_7»


-- @@ L154-154 verbatim
variable [HasAxiomT 𝓢]


-- @@ L156-157 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def axiomT : Entailment.Prf 𝓢 (Arrow.arrow (Box.box φ) φ) :=
  HasAxiomT.T _


-- @@ L158-158 expanded
@[simp]
lemma axiomT! : Provable 𝓢 (Arrow.arrow (Box.box φ) φ) :=
  ⟨axiomT⟩


-- @@ L160-160 verbatim
variable [Entailment.Minimal 𝓢]


-- @@ L162-162 verbatim
instance (Γ : FiniteContext F 𝓢) : HasAxiomT Γ := ⟨fun _ ↦ FiniteContext.of axiomT⟩

-- @@ L163-163 verbatim
instance (Γ : Context F 𝓢) : HasAxiomT Γ := ⟨fun _ ↦ Context.of axiomT⟩


-- @@ L165-166 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def axiomT' (h : Entailment.Prf 𝓢 (Box.box φ)) : Entailment.Prf 𝓢 φ :=
  mdp axiomT h


-- @@ L167-167 expanded
@[simp]
lemma axiomT'! (h : Provable 𝓢 (Box.box φ)) : Provable 𝓢 φ :=
  ⟨axiomT' h.some⟩


-- @@ L169-169 verbatim
end «lp_section_7»


-- @@ L171-174 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomDiaTc (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  diaTc (φ : F) : Entailment.Prf 𝓢 (Axioms.DiaTc φ)


-- @@ L176-176 verbatim
section «lp_section_8»


-- @@ L178-178 verbatim
variable [HasAxiomDiaTc 𝓢]


-- @@ L180-181 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def diaTc : Entailment.Prf 𝓢 (Arrow.arrow φ (Dia.dia φ)) :=
  HasAxiomDiaTc.diaTc _


-- @@ L182-182 expanded
@[simp]
lemma diaTc! : Provable 𝓢 (Arrow.arrow φ (Dia.dia φ)) :=
  ⟨diaTc⟩


-- @@ L184-184 verbatim
variable [Entailment.Minimal 𝓢]


-- @@ L186-186 verbatim
instance (Γ : FiniteContext F 𝓢) : HasAxiomDiaTc Γ := ⟨fun _ ↦ FiniteContext.of diaTc⟩

-- @@ L187-187 verbatim
instance (Γ : Context F 𝓢) : HasAxiomDiaTc Γ := ⟨fun _ ↦ Context.of diaTc⟩


-- @@ L189-190 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def diaTc' (h : Entailment.Prf 𝓢 φ) : Entailment.Prf 𝓢 (Dia.dia φ) :=
  mdp diaTc h


-- @@ L191-191 expanded
lemma diaTc'! (h : Provable 𝓢 φ) : Provable 𝓢 (Dia.dia φ) :=
  ⟨diaTc' h.some⟩


-- @@ L193-193 verbatim
end «lp_section_8»



-- @@ L196-199 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomD [Dia F] (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  D (φ : F) : Entailment.Prf 𝓢 (Axioms.D φ)


-- @@ L201-201 verbatim
section «lp_section_9»


-- @@ L203-203 verbatim
variable [HasAxiomD 𝓢]


-- @@ L205-206 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def axiomD : Entailment.Prf 𝓢 (Arrow.arrow (Box.box φ) (Dia.dia φ)) :=
  HasAxiomD.D _


-- @@ L207-207 expanded
@[simp]
lemma axiomD! : Provable 𝓢 (Arrow.arrow (Box.box φ) (Dia.dia φ)) :=
  ⟨axiomD⟩


-- @@ L210-210 verbatim
variable [Entailment.Minimal 𝓢]


-- @@ L212-212 verbatim
instance (Γ : FiniteContext F 𝓢) : HasAxiomD Γ := ⟨fun _ ↦ FiniteContext.of axiomD⟩

-- @@ L213-213 verbatim
instance (Γ : Context F 𝓢) : HasAxiomD Γ := ⟨fun _ ↦ Context.of axiomD⟩


-- @@ L215-216 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def axiomD' (h : Entailment.Prf 𝓢 (Box.box φ)) : Entailment.Prf 𝓢 (Dia.dia φ) :=
  mdp axiomD h


-- @@ L217-217 expanded
lemma axiomD'! (h : Provable 𝓢 (Box.box φ)) : Provable 𝓢 (Dia.dia φ) :=
  ⟨axiomD' h.some⟩


-- @@ L219-219 verbatim
end «lp_section_9»




-- @@ L223-226 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomP (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  P : Entailment.Prf 𝓢 Axioms.P


-- @@ L228-228 verbatim
section «lp_section_10»


-- @@ L230-230 verbatim
variable [HasAxiomP 𝓢]


-- @@ L232-233 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def axiomP : Entailment.Prf 𝓢 (Tilde.tilde (Box.box ⊥)) :=
  HasAxiomP.P


-- @@ L234-234 expanded
@[simp]
lemma axiomP! : Provable 𝓢 (Tilde.tilde (Box.box ⊥)) :=
  ⟨axiomP⟩


-- @@ L236-236 verbatim
variable [Entailment.Minimal 𝓢]


-- @@ L238-238 verbatim
instance (Γ : FiniteContext F 𝓢) : HasAxiomP Γ := ⟨FiniteContext.of axiomP⟩

-- @@ L239-239 verbatim
instance (Γ : Context F 𝓢) : HasAxiomP Γ := ⟨Context.of axiomP⟩


-- @@ L241-241 verbatim
end «lp_section_10»




-- @@ L245-248 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomB [Dia F] (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  B (φ : F) : Entailment.Prf 𝓢 (Axioms.B φ)


-- @@ L250-250 verbatim
section «lp_section_11»


-- @@ L252-252 verbatim
variable [HasAxiomB 𝓢]


-- @@ L254-255 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def axiomB : Entailment.Prf 𝓢 (Arrow.arrow φ (Box.box (Dia.dia φ))) :=
  HasAxiomB.B _


-- @@ L256-256 expanded
@[simp]
lemma axiomB! : Provable 𝓢 (Arrow.arrow φ (Box.box (Dia.dia φ))) :=
  ⟨axiomB⟩


-- @@ L258-258 verbatim
variable [Entailment.Minimal 𝓢]


-- @@ L260-260 verbatim
instance (Γ : FiniteContext F 𝓢) : HasAxiomB Γ := ⟨fun _ ↦ FiniteContext.of axiomB⟩

-- @@ L261-261 verbatim
instance (Γ : Context F 𝓢) : HasAxiomB Γ := ⟨fun _ ↦ Context.of axiomB⟩


-- @@ L263-264 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def axiomB' (h : Entailment.Prf 𝓢 φ) : Entailment.Prf 𝓢 (Box.box (Dia.dia φ)) :=
  mdp axiomB h


-- @@ L265-265 expanded
@[simp]
lemma axiomB'! (h : Provable 𝓢 φ) : Provable 𝓢 (Box.box (Dia.dia φ)) :=
  ⟨axiomB' h.some⟩


-- @@ L267-267 verbatim
end «lp_section_11»



-- @@ L270-273 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomFour (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Four (φ : F) : Entailment.Prf 𝓢 (Axioms.Four φ)


-- @@ L275-275 verbatim
section «lp_section_12»


-- @@ L277-277 verbatim
variable [HasAxiomFour 𝓢]


-- @@ L279-280 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def axiomFour : Entailment.Prf 𝓢 (Arrow.arrow (Box.box φ) (Box.box (Box.box φ))) :=
  HasAxiomFour.Four _


-- @@ L281-281 expanded
@[simp]
lemma axiomFour! : Provable 𝓢 (Arrow.arrow (Box.box φ) (Box.box (Box.box φ))) :=
  ⟨axiomFour⟩


-- @@ L283-283 verbatim
variable [Entailment.Minimal 𝓢]


-- @@ L285-285 verbatim
instance (Γ : FiniteContext F 𝓢) : HasAxiomFour Γ := ⟨fun _ ↦ FiniteContext.of axiomFour⟩

-- @@ L286-286 verbatim
instance (Γ : Context F 𝓢) : HasAxiomFour Γ := ⟨fun _ ↦ Context.of axiomFour⟩


-- @@ L288-289 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def axiomFour' (h : Entailment.Prf 𝓢 (Box.box φ)) : Entailment.Prf 𝓢 (Box.box (Box.box φ)) :=
  mdp axiomFour h


-- @@ L290-291 expanded
/-- Imported declaration from the Incompleteness formalization. -/
lemma axiomFour'! (h : Provable 𝓢 (Box.box φ)) : Provable 𝓢 (Box.box (Box.box φ)) :=
  ⟨axiomFour' h.some⟩


-- @@ L293-293 verbatim
end «lp_section_12»



-- @@ L296-299 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomFive [Dia F] (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Five (φ : F) : Entailment.Prf 𝓢 (Axioms.Five φ)


-- @@ L301-301 verbatim
section «lp_section_13»


-- @@ L303-303 verbatim
variable [HasAxiomFive 𝓢]


-- @@ L305-306 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def axiomFive : Entailment.Prf 𝓢 (Arrow.arrow (Dia.dia φ) (Box.box (Dia.dia φ))) :=
  HasAxiomFive.Five _


-- @@ L307-307 expanded
@[simp]
lemma axiomFive! : Provable 𝓢 (Arrow.arrow (Dia.dia φ) (Box.box (Dia.dia φ))) :=
  ⟨axiomFive⟩


-- @@ L309-309 verbatim
variable [Entailment.Minimal 𝓢]


-- @@ L311-311 verbatim
instance (Γ : FiniteContext F 𝓢) : HasAxiomFive Γ := ⟨fun _ ↦ FiniteContext.of axiomFive⟩

-- @@ L312-312 verbatim
instance (Γ : Context F 𝓢) : HasAxiomFive Γ := ⟨fun _ ↦ Context.of axiomFive⟩


-- @@ L314-314 verbatim
end «lp_section_13»




-- @@ L318-321 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomL (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  L (φ : F) : Entailment.Prf 𝓢 (Axioms.L φ)


-- @@ L323-323 verbatim
section «lp_section_14»


-- @@ L325-325 verbatim
variable [HasAxiomL 𝓢]


-- @@ L327-328 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def axiomL : Entailment.Prf 𝓢 (Arrow.arrow (Box.box (Arrow.arrow (Box.box φ) φ)) (Box.box φ)) :=
  HasAxiomL.L _


-- @@ L329-329 expanded
@[simp]
lemma axiomL! : Provable 𝓢 (Arrow.arrow (Box.box (Arrow.arrow (Box.box φ) φ)) (Box.box φ)) :=
  ⟨axiomL⟩


-- @@ L331-331 verbatim
variable [Entailment.Minimal 𝓢]


-- @@ L333-333 verbatim
instance (Γ : FiniteContext F 𝓢) : HasAxiomL Γ := ⟨fun _ ↦ FiniteContext.of axiomL⟩

-- @@ L334-334 verbatim
instance (Γ : Context F 𝓢) : HasAxiomL Γ := ⟨fun _ ↦ Context.of axiomL⟩


-- @@ L336-336 verbatim
end «lp_section_14»


-- @@ L338-341 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomDot2 [Dia F] (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Dot2 (φ : F) : Entailment.Prf 𝓢 (Axioms.Dot2 φ)


-- @@ L343-343 verbatim
section «lp_section_15»


-- @@ L345-345 verbatim
variable [HasAxiomDot2 𝓢]


-- @@ L347-348 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def axiomDot2 : Entailment.Prf 𝓢 (Arrow.arrow (Dia.dia (Box.box φ)) (Box.box (Dia.dia φ))) :=
  HasAxiomDot2.Dot2 _


-- @@ L349-349 expanded
@[simp]
lemma axiomDot2! : Provable 𝓢 (Arrow.arrow (Dia.dia (Box.box φ)) (Box.box (Dia.dia φ))) :=
  ⟨axiomDot2⟩


-- @@ L351-351 verbatim
variable [Entailment.Minimal 𝓢]


-- @@ L353-353 verbatim
instance (Γ : FiniteContext F 𝓢) : HasAxiomDot2 Γ := ⟨fun _ ↦ FiniteContext.of axiomDot2⟩

-- @@ L354-354 verbatim
instance (Γ : Context F 𝓢) : HasAxiomDot2 Γ := ⟨fun _ ↦ Context.of axiomDot2⟩


-- @@ L356-356 verbatim
end «lp_section_15»



-- @@ L359-362 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomDot3 (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Dot3 (φ ψ : F) : Entailment.Prf 𝓢 (Axioms.Dot3 φ ψ)


-- @@ L364-364 verbatim
section «lp_section_16»


-- @@ L366-366 verbatim
variable [HasAxiomDot3 𝓢]


-- @@ L368-369 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def axiomDot3 :
    Entailment.Prf 𝓢
      (Vee.vee (Box.box (Arrow.arrow (Box.box φ) ψ)) (Box.box (Arrow.arrow (Box.box ψ) φ))) :=
  HasAxiomDot3.Dot3 _ _


-- @@ L370-370 expanded
@[simp]
lemma axiomDot3! :
    Provable 𝓢
      (Vee.vee (Box.box (Arrow.arrow (Box.box φ) ψ)) (Box.box (Arrow.arrow (Box.box ψ) φ))) :=
  ⟨axiomDot3⟩


-- @@ L372-372 verbatim
variable [Entailment.Minimal 𝓢]


-- @@ L374-374 verbatim
instance (Γ : FiniteContext F 𝓢) : HasAxiomDot3 Γ := ⟨fun _ _ ↦ FiniteContext.of axiomDot3⟩

-- @@ L375-375 verbatim
instance (Γ : Context F 𝓢) : HasAxiomDot3 Γ := ⟨fun _ _ ↦ Context.of axiomDot3⟩


-- @@ L377-377 verbatim
end «lp_section_16»



-- @@ L380-383 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomGrz (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Grz (φ : F) : Entailment.Prf 𝓢 (Axioms.Grz φ)


-- @@ L385-385 verbatim
section «lp_section_17»


-- @@ L387-387 verbatim
variable [HasAxiomGrz 𝓢]


-- @@ L389-390 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def axiomGrz :
    Entailment.Prf 𝓢
      (Arrow.arrow (Box.box (Arrow.arrow (Box.box (Arrow.arrow φ (Box.box φ))) φ)) φ) :=
  HasAxiomGrz.Grz _


-- @@ L391-391 expanded
@[simp]
lemma axiomGrz! :
    Provable 𝓢 (Arrow.arrow (Box.box (Arrow.arrow (Box.box (Arrow.arrow φ (Box.box φ))) φ)) φ) :=
  ⟨axiomGrz⟩


-- @@ L393-393 verbatim
variable [Entailment.Minimal 𝓢]


-- @@ L395-395 verbatim
instance (Γ : FiniteContext F 𝓢) : HasAxiomGrz Γ := ⟨fun _ ↦ FiniteContext.of axiomGrz⟩

-- @@ L396-396 verbatim
instance (Γ : Context F 𝓢) : HasAxiomGrz Γ := ⟨fun _ ↦ Context.of axiomGrz⟩


-- @@ L398-398 verbatim
end «lp_section_17»



-- @@ L401-404 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomTc (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Tc (φ : F) : Entailment.Prf 𝓢 (Axioms.Tc φ)


-- @@ L406-406 verbatim
section «lp_section_18»


-- @@ L408-408 verbatim
variable [HasAxiomTc 𝓢]


-- @@ L410-411 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def axiomTc : Entailment.Prf 𝓢 (Arrow.arrow φ (Box.box φ)) :=
  HasAxiomTc.Tc _


-- @@ L412-412 expanded
@[simp]
lemma axiomTc! : Provable 𝓢 (Arrow.arrow φ (Box.box φ)) :=
  ⟨axiomTc⟩


-- @@ L414-414 verbatim
variable [Entailment.Minimal 𝓢]


-- @@ L416-416 verbatim
instance (Γ : FiniteContext F 𝓢) : HasAxiomTc Γ := ⟨fun _ ↦ FiniteContext.of axiomTc⟩

-- @@ L417-417 verbatim
instance (Γ : Context F 𝓢) : HasAxiomTc Γ := ⟨fun _ ↦ Context.of axiomTc⟩


-- @@ L419-419 verbatim
end «lp_section_18»



-- @@ L422-425 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomDiaT (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  diaT (φ : F) : Entailment.Prf 𝓢 (Axioms.DiaT φ)


-- @@ L427-427 verbatim
section «lp_section_19»


-- @@ L429-429 verbatim
variable [HasAxiomDiaT 𝓢]


-- @@ L431-432 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def diaT : Entailment.Prf 𝓢 (Arrow.arrow (Dia.dia φ) φ) :=
  HasAxiomDiaT.diaT _


-- @@ L433-433 expanded
@[simp]
lemma diaT! : Provable 𝓢 (Arrow.arrow (Dia.dia φ) φ) :=
  ⟨diaT⟩


-- @@ L435-435 verbatim
variable [Entailment.Minimal 𝓢]


-- @@ L437-437 verbatim
instance (Γ : FiniteContext F 𝓢) : HasAxiomDiaT Γ := ⟨fun _ ↦ FiniteContext.of diaT⟩

-- @@ L438-438 verbatim
instance (Γ : Context F 𝓢) : HasAxiomDiaT Γ := ⟨fun _ ↦ Context.of diaT⟩


-- @@ L440-441 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def diaT' (h : Entailment.Prf 𝓢 (Dia.dia φ)) : Entailment.Prf 𝓢 φ :=
  mdp diaT h


-- @@ L442-442 expanded
lemma diaT'! (h : Provable 𝓢 (Dia.dia φ)) : Provable 𝓢 φ :=
  ⟨diaT' h.some⟩


-- @@ L444-444 verbatim
end «lp_section_19»



-- @@ L447-450 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomVer (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  Ver (φ : F) : Entailment.Prf 𝓢 (Axioms.Ver φ)


-- @@ L452-452 verbatim
section «lp_section_20»


-- @@ L454-454 verbatim
variable [HasAxiomVer 𝓢]


-- @@ L456-457 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def axiomVer : Entailment.Prf 𝓢 (Box.box φ) :=
  HasAxiomVer.Ver _


-- @@ L458-458 expanded
@[simp]
lemma axiomVer! : Provable 𝓢 (Box.box φ) :=
  ⟨axiomVer⟩


-- @@ L460-460 verbatim
variable [Entailment.Minimal 𝓢]


-- @@ L462-462 verbatim
instance (Γ : FiniteContext F 𝓢) : HasAxiomVer Γ := ⟨fun _ ↦ FiniteContext.of axiomVer⟩

-- @@ L463-463 verbatim
instance (Γ : Context F 𝓢) : HasAxiomVer Γ := ⟨fun _ ↦ Context.of axiomVer⟩


-- @@ L465-465 verbatim
end «lp_section_20»




-- @@ L469-472 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class HasAxiomH (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  H (φ : F) : Entailment.Prf 𝓢 (Axioms.H φ)


-- @@ L474-474 verbatim
section «lp_section_21»


-- @@ L476-476 verbatim
variable [HasAxiomH 𝓢]


-- @@ L478-479 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def axiomH :
    Entailment.Prf 𝓢 (Arrow.arrow (Box.box (LogicalConnective.iff (Box.box φ) φ)) (Box.box φ)) :=
  HasAxiomH.H _


-- @@ L480-480 expanded
@[simp]
lemma axiomH! :
    Provable 𝓢 (Arrow.arrow (Box.box (LogicalConnective.iff (Box.box φ) φ)) (Box.box φ)) :=
  ⟨axiomH⟩


-- @@ L482-482 verbatim
variable [Entailment.Minimal 𝓢]


-- @@ L484-484 verbatim
instance (Γ : FiniteContext F 𝓢) : HasAxiomH Γ := ⟨fun _ ↦ FiniteContext.of axiomH⟩

-- @@ L485-485 verbatim
instance (Γ : Context F 𝓢) : HasAxiomH Γ := ⟨fun _ ↦ Context.of axiomH⟩


-- @@ L487-487 verbatim
end «lp_section_21»



-- @@ L490-490 verbatim
section «lp_section_22»


-- @@ L492-492 verbatim
variable [DecidableEq F]

-- @@ L493-493 verbatim
variable {φ ψ χ : F} {Γ Δ : List F}

-- @@ L494-494 verbatim
variable {𝓢 : S}


-- @@ L496-500 verbatim
instance [Entailment.Minimal 𝓢] [ModalDeMorgan F] : HasDiaDuality 𝓢 := ⟨by
  intro φ;
  simp only [Axioms.DiaDuality, ModalDeMorgan.box, DeMorgan.neg];
  apply iffId;
⟩


-- @@ L502-506 verbatim
instance [Entailment.Minimal 𝓢] [DiaAbbrev F] : HasDiaDuality 𝓢 := ⟨by
  intro φ;
  simp only [Axioms.DiaDuality, DiaAbbrev.dia_abbrev];
  apply iffId;
⟩


-- @@ L508-511 expanded
instance [ModusPonens 𝓢] [HasAxiomT 𝓢] : Unnecessitation 𝓢 :=
  ⟨by intro φ hp; exact mdp axiomT hp; ⟩


-- @@ L513-513 verbatim
end «lp_section_22»



-- @@ L516-516 verbatim
section «lp_section_23»


-- @@ L518-518 verbatim
variable (𝓢 : S)


-- @@ L520-521 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class K extends Entailment.Classical 𝓢, Necessitation 𝓢, HasAxiomK 𝓢, HasDiaDuality 𝓢


-- @@ L523-524 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class KD extends Entailment.K 𝓢, HasAxiomD 𝓢


-- @@ L526-527 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class KP extends Entailment.K 𝓢, HasAxiomP 𝓢


-- @@ L529-530 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class KB extends Entailment.K 𝓢, HasAxiomB 𝓢


-- @@ L532-533 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class KT extends Entailment.K 𝓢, HasAxiomT 𝓢

-- @@ L534-535 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class KT' extends Entailment.K 𝓢, HasAxiomDiaTc 𝓢


-- @@ L537-538 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class KTc extends Entailment.K 𝓢, HasAxiomTc 𝓢

-- @@ L539-540 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class KTc' extends Entailment.K 𝓢, HasAxiomDiaT 𝓢


-- @@ L542-543 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class KTB extends Entailment.K 𝓢, HasAxiomT 𝓢, HasAxiomB 𝓢


-- @@ L545-546 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class KD45 extends Entailment.K 𝓢, HasAxiomD 𝓢, HasAxiomFour 𝓢, HasAxiomFive 𝓢


-- @@ L548-549 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class KB4 extends Entailment.K 𝓢, HasAxiomB 𝓢, HasAxiomFour 𝓢


-- @@ L551-552 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class KB5 extends Entailment.K 𝓢, HasAxiomB 𝓢, HasAxiomFive 𝓢


-- @@ L554-555 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class KDB extends Entailment.K 𝓢, HasAxiomD 𝓢, HasAxiomB 𝓢


-- @@ L557-558 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class KD4 extends Entailment.K 𝓢, HasAxiomD 𝓢, HasAxiomFour 𝓢


-- @@ L560-561 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class KD5 extends Entailment.K 𝓢, HasAxiomD 𝓢, HasAxiomFive 𝓢


-- @@ L563-564 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class K45 extends Entailment.K 𝓢, HasAxiomFour 𝓢, HasAxiomFive 𝓢


-- @@ L566-567 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class Triv extends Entailment.K 𝓢, HasAxiomT 𝓢, HasAxiomTc 𝓢

-- @@ L568-568 verbatim
instance [Entailment.Triv 𝓢] : Entailment.KT 𝓢 where

-- @@ L569-569 verbatim
instance [Entailment.Triv 𝓢] : Entailment.KTc 𝓢 where


-- @@ L571-572 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class Ver extends Entailment.K 𝓢, HasAxiomVer 𝓢


-- @@ L574-575 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class K4 extends Entailment.K 𝓢, HasAxiomFour 𝓢


-- @@ L577-578 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class K5 extends Entailment.K 𝓢, HasAxiomFive 𝓢


-- @@ L580-581 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class S4 extends Entailment.K 𝓢, HasAxiomT 𝓢, HasAxiomFour 𝓢

-- @@ L582-582 verbatim
instance [Entailment.S4 𝓢] : Entailment.K4 𝓢 where

-- @@ L583-583 verbatim
instance [Entailment.S4 𝓢] : Entailment.KT 𝓢 where


-- @@ L585-586 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class S4Dot2 extends Entailment.S4 𝓢, HasAxiomDot2 𝓢


-- @@ L588-589 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class S4Dot3 extends Entailment.S4 𝓢, HasAxiomDot3 𝓢


-- @@ L591-592 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class S5 extends Entailment.K 𝓢, HasAxiomT 𝓢, HasAxiomFive 𝓢

-- @@ L593-593 verbatim
instance [Entailment.S5 𝓢] : Entailment.KT 𝓢 where

-- @@ L594-594 verbatim
instance [Entailment.S5 𝓢] : Entailment.K5 𝓢 where


-- @@ L596-597 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class GL extends Entailment.K 𝓢, HasAxiomL 𝓢


-- @@ L599-600 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected class Grz extends Entailment.K 𝓢, HasAxiomGrz 𝓢


-- @@ L602-602 verbatim
end «lp_section_23»



-- @@ L605-605 verbatim
section «lp_section_24»


-- @@ L607-609 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class ModalDisjunctive (𝓢 : S) : Prop where
  modal_disjunctive :
    ∀ {φ ψ : F}, Provable 𝓢 (Vee.vee (Box.box φ) (Box.box ψ)) → Provable 𝓢 φ ∨ Provable 𝓢 ψ


-- @@ L611-611 verbatim
alias modal_disjunctive := ModalDisjunctive.modal_disjunctive


-- @@ L613-613 verbatim
variable {𝓢 : S} [Entailment.Minimal 𝓢]


-- @@ L615-619 verbatim
instance [Disjunctive 𝓢] [Unnecessitation 𝓢] : ModalDisjunctive 𝓢 where
  modal_disjunctive h := by
    rcases disjunctive h with (h | h);
    · left; exact unnec! h;
    · right; exact unnec! h;


-- @@ L621-623 expanded
private lemma unnec_of_mdp_aux [ModalDisjunctive 𝓢] (h : Provable 𝓢 (Box.box φ)) : Provable 𝓢 φ :=
  by have : Provable 𝓢 (Vee.vee (Box.box φ) (Box.box φ)) := or₁'! h;
  rcases modal_disjunctive this with (h | h) <;> tauto;


-- @@ L625-627 verbatim
noncomputable instance unnecessitationOfModalDisjunctive [ModalDisjunctive 𝓢] :
    Unnecessitation 𝓢 where
  unnec h := (private_decl% (unnec_of_mdp_aux ⟨h⟩)).some


-- @@ L629-629 verbatim
end «lp_section_24»


-- @@ L631-631 verbatim
end Entailment

-- @@ L632-632 verbatim
end LO
