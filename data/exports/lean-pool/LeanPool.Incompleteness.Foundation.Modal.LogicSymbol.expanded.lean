/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Logic.LogicSymbol
public import Mathlib.Data.Finset.Preimage
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Bound.Init


-- @@ L13-13 verbatim
/-! # LogicSymbol -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
open Function


-- @@ L20-20 verbatim
namespace LO


-- @@ L22-27 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[notation_class]
class Box (F : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  box : F → F
  box_injective : Function.Injective box := by simp [Function.Injective];


-- @@ L29-30 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:76 "□" => Box.box


-- @@ L32-32 verbatim
namespace Box


-- @@ L34-34 verbatim
attribute [match_pattern] Box.box

-- @@ L35-35 verbatim
attribute [simp] Box.box_injective


-- @@ L37-37 verbatim
variable [Box F]


-- @@ L39-40 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[match_pattern]
abbrev boxdot [Wedge F] (φ : F) : F :=
  Wedge.wedge φ (Box.box φ)


-- @@ L41-42 verbatim
/-- Imported notation from the Incompleteness formalization. -/
prefix:76 "⊡" => boxdot


-- @@ L44-45 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev multibox (n : ℕ) : F → F :=
  (Box.box ·)^[n]


-- @@ L46-47 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:76 "□^[" n:90 "]" φ:80 => multibox n φ


-- @@ L49-51 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class Subclosed (C : F → Prop) where
  box_closed : C (Box.box φ) → C φ


-- @@ L53-53 verbatim
attribute [aesop safe 5 forward] Subclosed.box_closed



-- @@ L56-56 verbatim
variable {φ ψ : F} {n : ℕ}


-- @@ L58-59 expanded
@[simp]
lemma box_injective' : Box.box φ = Box.box ψ ↔ φ = ψ :=
  box_injective.eq_iff


-- @@ L61-61 expanded
@[simp]
lemma multibox_succ : multibox (n + 1) φ = Box.box (multibox n φ) := by apply iterate_succ_apply'


-- @@ L63-64 expanded
@[simp]
lemma multibox_injective : Function.Injective (multibox n · : F → F) := by
  apply Function.Injective.iterate (by simp);


-- @@ L66-67 expanded
@[simp]
lemma multimop_injective' : multibox n φ = multibox n ψ ↔ φ = ψ :=
  multibox_injective.eq_iff


-- @@ L69-69 verbatim
end Box



-- @@ L72-77 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[notation_class]
class Dia (F : Type*) where
  /-- Imported declaration from the Incompleteness formalization. -/
  dia : F → F
  dia_injective : Function.Injective dia := by simp [Function.Injective];


-- @@ L79-80 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:76 "◇" => Dia.dia


-- @@ L82-82 verbatim
namespace Dia


-- @@ L84-84 verbatim
attribute [match_pattern] Dia.dia

-- @@ L85-85 verbatim
attribute [simp] Dia.dia_injective


-- @@ L87-87 verbatim
variable [Dia F]


-- @@ L89-90 expanded
/-- Imported declaration from the Incompleteness formalization. -/
@[match_pattern]
abbrev diadot [Vee F] (φ : F) : F :=
  Vee.vee φ (Dia.dia φ)


-- @@ L91-92 verbatim
/-- Imported notation from the Incompleteness formalization. -/
prefix:76 "diaDot" => diadot


-- @@ L94-95 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev multidia (n : ℕ) : F → F :=
  (Dia.dia ·)^[n]


-- @@ L97-98 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:76 "◇^[" n:90 "]" φ:80 => multidia n φ


-- @@ L100-102 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class Subclosed [LogicalConnective F] (C : F → Prop) where
  dia_closed : C (Dia.dia φ) → C φ


-- @@ L104-104 verbatim
attribute [aesop safe 5 forward] Subclosed.dia_closed


-- @@ L106-106 verbatim
variable {φ ψ : F} {n : ℕ}


-- @@ L108-109 expanded
@[simp]
lemma dia_injective' : Dia.dia φ = Dia.dia ψ ↔ φ = ψ :=
  dia_injective.eq_iff


-- @@ L111-111 expanded
@[simp]
lemma multidia_succ : multidia (n + 1) φ = Dia.dia (multidia n φ) := by apply iterate_succ_apply'


-- @@ L113-114 expanded
@[simp]
lemma multidia_injective : Function.Injective (multidia n · : F → F) := by
  apply Function.Injective.iterate (by simp);


-- @@ L116-117 expanded
@[simp]
lemma multidia_injective' : multidia n φ = multidia n ψ ↔ φ = ψ :=
  multidia_injective.eq_iff


-- @@ L119-119 verbatim
end Dia


-- @@ L121-122 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class BasicModalLogicalConnective (F : Type*) extends LogicalConnective F, Box F, Dia F


-- @@ L124-129 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class _root_.LO.BasicModalLogicConnective.Subclosed [BasicModalLogicalConnective F] (C : F →
  Prop) extends
  toLogicalConnectiveSubclosed : LogicalConnective.Subclosed C,
  toBoxSubclosed : Box.Subclosed C,
  toDiaSubclosed : Dia.Subclosed C


-- @@ L131-133 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class DiaAbbrev (F : Type*) [Box F] [Dia F] [Tilde F] where
  dia_abbrev {φ : F} : Dia.dia φ = Tilde.tilde (Box.box (Tilde.tilde φ))


-- @@ L135-138 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class ModalDeMorgan (F : Type*) [LogicalConnective F] [Box F] [Dia F] extends DeMorgan F where
  dia (φ : F) : Tilde.tilde (Dia.dia φ) = Box.box (Tilde.tilde φ)
  box (φ : F) : Tilde.tilde (Box.box φ) = Dia.dia (Tilde.tilde φ)


-- @@ L140-140 verbatim
attribute [simp] ModalDeMorgan.dia ModalDeMorgan.box


-- @@ L142-142 verbatim
end LO



-- @@ L145-145 verbatim
section «lp_section_1»


-- @@ L147-147 verbatim
open LO (Box Dia)

-- @@ L148-148 verbatim
variable {F : Type*}


-- @@ L150-151 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Set.multibox [Box F] (n : ℕ) : Set F → Set F :=
  Set.image (Box.box ·)^[n]


-- @@ L152-153 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:80 "□''^[" n:90 "]" s:80 => Set.multibox n s


-- @@ L155-156 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Set.multidia [Dia F] (n : ℕ) : Set F → Set F :=
  Set.image (Dia.dia ·)^[n]


-- @@ L157-158 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:80 "◇''^[" n:90 "]" s:80 => Set.multidia n s


-- @@ L160-161 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Set.box [Box F] : Set F → Set F := Set.multibox (n := 1)

-- @@ L162-163 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "□''" => Set.box


-- @@ L165-166 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Set.dia [Dia F] : Set F → Set F := Set.multidia (n := 1)

-- @@ L167-168 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "◇''" => Set.dia



-- @@ L171-172 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Set.premultibox [Box F] (n : ℕ) : Set F → Set F :=
  Set.preimage (Box.box ·)^[n]


-- @@ L173-174 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:80 "□''⁻¹^[" n:90 "]" s:80 => Set.premultibox n s


-- @@ L176-177 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Set.premultidia [Dia F] (n : ℕ) : Set F → Set F :=
  Set.preimage (Dia.dia ·)^[n]


-- @@ L178-179 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:80 "◇''⁻¹^[" n:90 "]" s:80 => Set.premultidia n s


-- @@ L181-182 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Set.prebox [Box F] : Set F → Set F := Set.premultibox (n := 1)

-- @@ L183-184 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "□''⁻¹" => Set.prebox


-- @@ L186-187 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Set.predia [Dia F] : Set F → Set F := Set.premultidia (n := 1)

-- @@ L188-189 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "◇''⁻¹" => Set.predia



-- @@ L192-192 verbatim
namespace Set


-- @@ L194-194 verbatim
variable {s t : Set F}


-- @@ L196-196 verbatim
section «lp_section_2»


-- @@ L198-198 verbatim
variable [Box F]


-- @@ L200-200 expanded
@[simp]
lemma eq_box_multibox_one : Set.box s = Set.multibox 1 s := by rfl


-- @@ L202-202 expanded
@[simp 1100]
lemma eq_prebox_premultibox_one : Set.prebox s = Set.premultibox 1 s := by rfl


-- @@ L205-206 expanded
@[simp 1100]
lemma multibox_subset_mono (h : s ⊆ t) : Set.multibox n s ⊆ Set.multibox n t := by
  simp_all [Set.subset_def];


-- @@ L208-208 expanded
lemma box_subset_mono (h : s ⊆ t) : Set.box s ⊆ Set.box t := by
  simpa using multibox_subset_mono (n := 1) h;


-- @@ L211-212 expanded
@[simp 1100]
lemma premultibox_subset_mono (h : s ⊆ t) : Set.premultibox n s ⊆ Set.premultibox n t := by
  simp_all [Set.subset_def];


-- @@ L214-215 expanded
lemma prebox_subset_mono (h : s ⊆ t) : Set.prebox s ⊆ Set.prebox t := by
  simpa using premultibox_subset_mono (n := 1) h;


-- @@ L218-218 expanded
@[simp 1100]
lemma iff_mem_premultibox : φ ∈ Set.premultibox n s ↔ multibox n φ ∈ s := by simp;


-- @@ L220-220 expanded
@[simp 1100]
lemma iff_mem_multibox : multibox n φ ∈ Set.multibox n s ↔ φ ∈ s := by simp;


-- @@ L223-224 expanded
lemma subset_premulitibox_iff_multibox_subset (h : s ⊆ Set.premultibox n t) :
    Set.multibox n s ⊆ t := by simp_all


-- @@ L226-227 expanded
lemma subset_prebox_iff_box_subset (h : s ⊆ Set.prebox t) : Set.box s ⊆ t := by
  simpa using subset_premulitibox_iff_multibox_subset (n := 1) h


-- @@ L229-232 expanded
lemma subset_multibox_iff_premulitibox_subset (h : s ⊆ Set.multibox n t) :
    Set.premultibox n s ⊆ t := by intro φ hp; have := premultibox_subset_mono h hp; simp_all;


-- @@ L233-234 expanded
lemma subset_box_iff_prebox_subset (h : s ⊆ Set.box t) : Set.prebox s ⊆ t := by
  simpa using subset_multibox_iff_premulitibox_subset (n := 1) h


-- @@ L236-239 expanded
lemma forall_multibox_of_subset_multibox (h : s ⊆ Set.multibox n t) :
    ∀ φ ∈ s, ∃ ψ ∈ t, φ = multibox n ψ := by intro φ hp; obtain ⟨ψ, _, rfl⟩ := h hp; use ψ;


-- @@ L240-241 expanded
lemma forall_box_of_subset_box (h : s ⊆ Set.box t) : ∀ φ ∈ s, ∃ ψ ∈ t, φ = Box.box ψ := by
  simpa using forall_multibox_of_subset_multibox (n := 1) h


-- @@ L243-248 expanded
lemma eq_premultibox_multibox_of_subset_premultibox (h : s ⊆ Set.multibox n t) :
    Set.multibox n (Set.premultibox n s) = s :=
  by
  apply Set.eq_of_subset_of_subset; · simp_all
  · intro φ hp; obtain ⟨ψ, _, rfl⟩ := forall_multibox_of_subset_multibox h φ hp;
    simp_all [Set.premultibox];


-- @@ L249-250 expanded
lemma eq_prebox_box_of_subset_prebox (h : s ⊆ Set.box t) : Set.box (Set.prebox s) = s := by
  simpa using eq_premultibox_multibox_of_subset_premultibox (n := 1) h


-- @@ L252-252 verbatim
end «lp_section_2»



-- @@ L255-255 verbatim
section «lp_section_3»


-- @@ L257-257 verbatim
variable [Dia F]


-- @@ L259-259 expanded
@[simp]
lemma eq_dia_multidia_one : Set.dia s = Set.multidia 1 s := by rfl


-- @@ L261-261 expanded
@[simp 1100]
lemma eq_predia_premultidia_one : Set.predia s = Set.premultidia 1 s := by rfl


-- @@ L264-265 expanded
@[simp 1100]
lemma multidia_subset_mono (h : s ⊆ t) : Set.multidia n s ⊆ Set.multidia n t := by
  simp_all [Set.subset_def];


-- @@ L267-267 expanded
lemma dia_subset_mono (h : s ⊆ t) : Set.dia s ⊆ Set.dia t := by
  simpa using multidia_subset_mono (n := 1) h;


-- @@ L270-271 expanded
@[simp 1100]
lemma premultidia_subset_mono (h : s ⊆ t) : Set.premultidia n s ⊆ Set.premultidia n t := by
  simp_all [Set.subset_def];


-- @@ L273-274 expanded
lemma predia_subset_mono (h : s ⊆ t) : Set.predia s ⊆ Set.predia t := by
  simpa using premultidia_subset_mono (n := 1) h;


-- @@ L277-277 expanded
@[simp 1100]
lemma iff_mem_premultidia : φ ∈ Set.premultidia n s ↔ multidia n φ ∈ s := by simp;


-- @@ L279-279 expanded
@[simp 1100]
lemma iff_mem_multidia : multidia n φ ∈ Set.multidia n s ↔ φ ∈ s := by simp;


-- @@ L281-282 expanded
lemma subset_premultidia_iff_multidia_subset (h : s ⊆ Set.premultidia n t) : Set.multidia n s ⊆ t :=
  by simp_all


-- @@ L284-285 expanded
lemma subset_predia_iff_dia_subset (h : s ⊆ Set.predia t) : Set.dia s ⊆ t := by
  simpa using subset_premultidia_iff_multidia_subset (n := 1) h


-- @@ L287-290 expanded
lemma subset_multidia_iff_premultidia_subset (h : s ⊆ Set.multidia n t) : Set.premultidia n s ⊆ t :=
  by intro φ hp; have := premultidia_subset_mono h hp; simp_all;


-- @@ L292-293 expanded
lemma subset_dia_iff_predia_subset (h : s ⊆ Set.dia t) : Set.predia s ⊆ t := by
  simpa using subset_multidia_iff_premultidia_subset (n := 1) h


-- @@ L295-298 expanded
lemma forall_multidia_of_subset_multidia (h : s ⊆ Set.multidia n t) :
    ∀ φ ∈ s, ∃ ψ ∈ t, φ = multidia n ψ := by intro φ hp; obtain ⟨ψ, _, rfl⟩ := h hp; use ψ;


-- @@ L299-300 expanded
lemma forall_dia_of_subset_dia (h : s ⊆ Set.dia t) : ∀ φ ∈ s, ∃ ψ ∈ t, φ = Dia.dia ψ := by
  simpa using forall_multidia_of_subset_multidia (n := 1) h


-- @@ L302-307 expanded
lemma eq_premultidia_multidia_of_subset_premultidia (h : s ⊆ Set.multidia n t) :
    Set.multidia n (Set.premultidia n s) = s :=
  by
  apply Set.eq_of_subset_of_subset; · simp_all
  · intro φ hp; obtain ⟨ψ, _, rfl⟩ := forall_multidia_of_subset_multidia h φ hp;
    simp_all [Set.premultidia];


-- @@ L308-309 expanded
lemma eq_predia_dia_of_subset_predia (h : s ⊆ Set.dia t) : Set.dia (Set.predia s) = s := by
  simpa using eq_premultidia_multidia_of_subset_premultidia (n := 1) h


-- @@ L311-311 verbatim
end «lp_section_3»


-- @@ L313-313 verbatim
end Set



-- @@ L316-316 verbatim
section «lp_section_4»


-- @@ L318-318 verbatim
variable [DecidableEq F]


-- @@ L320-321 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Finset.multibox [Box F] (n : ℕ) : Finset F → Finset F :=
  Finset.image (Box.box ·)^[n]


-- @@ L323-324 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Finset.multidia [Dia F] (n : ℕ) : Finset F → Finset F :=
  Finset.image (Dia.dia ·)^[n]


-- @@ L326-327 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Finset.modalBox [Box F] : Finset F → Finset F := Finset.multibox (n := 1)


-- @@ L329-330 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Finset.dia [Dia F] : Finset F → Finset F := Finset.multidia (n := 1)



-- @@ L333-335 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev Finset.premultibox [Box F] (n : ℕ) : Finset F → Finset F := fun s =>
  Finset.preimage s (Box.box ·)^[n] (Box.box_injective.iterate n).injOn


-- @@ L337-339 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev Finset.premultidia [Dia F] (n : ℕ) : Finset F → Finset F := fun s =>
  Finset.preimage s (Dia.dia ·)^[n] (Dia.dia_injective.iterate n).injOn


-- @@ L341-343 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev Finset.prebox [Box F] : Finset F → Finset F :=
  Finset.premultibox (n := 1)


-- @@ L345-347 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev Finset.predia [Dia F] : Finset F → Finset F :=
  Finset.premultidia (n := 1)


-- @@ L349-349 verbatim
end «lp_section_4»


-- @@ L351-351 verbatim
namespace Finset


-- @@ L353-353 verbatim
variable {s t : Finset F} {n : ℕ}


-- @@ L355-355 verbatim
section «lp_section_5»


-- @@ L357-357 verbatim
variable [Box F]


-- @@ L359-359 verbatim
@[simp] lemma eq_box_multibox_one [DecidableEq F] : s.modalBox = s.multibox 1 := by rfl


-- @@ L361-361 verbatim
@[simp] lemma eq_prebox_premultibox_one : s.prebox = s.premultibox 1 := by rfl


-- @@ L363-363 expanded
lemma multibox_coe [DecidableEq F] : (s.multibox n) = Set.multibox n (s : Set F) := by simp_all


-- @@ L365-365 expanded
lemma box_coe [DecidableEq F] : s.modalBox = Set.box (s : Set F) := by
  simpa using multibox_coe (n := 1)


-- @@ L367-368 expanded
lemma multibox_mem_coe [DecidableEq F] : φ ∈ s.multibox n ↔ φ ∈ Set.multibox n (↑s : Set F) := by
  constructor <;> simp_all


-- @@ L370-370 expanded
lemma box_mem_coe [DecidableEq F] : φ ∈ s.modalBox ↔ φ ∈ Set.box (↑s : Set F) := by simp;


-- @@ L372-372 expanded
lemma premultibox_coe : (s.premultibox n) = Set.premultibox n (s : Set F) := by simp_all


-- @@ L374-374 expanded
lemma prebox_coe : s.prebox = Set.prebox (↑s : Set F) := by simpa using premultibox_coe (n := 1)


-- @@ L376-381 expanded
lemma premultibox_multibox_eq_of_subset_multibox [DecidableEq F] {s : Finset F} {t : Set F}
    (hs : ↑s ⊆ Set.multibox n t) : (s.premultibox n).multibox n = s := by
  have := Set.eq_premultibox_multibox_of_subset_premultibox hs;
  rw [← premultibox_coe, ← multibox_coe] at this; exact Finset.coe_inj.mp this;


-- @@ L383-385 expanded
lemma prebox_box_eq_of_subset_box [DecidableEq F] {s : Finset F} {t : Set F} (hs : ↑s ⊆ Set.box t) :
    s.prebox.modalBox = s := by simpa using premultibox_multibox_eq_of_subset_multibox (n := 1) hs


-- @@ L387-387 verbatim
end «lp_section_5»



-- @@ L390-390 verbatim
section «lp_section_6»


-- @@ L392-392 verbatim
variable [Dia F]


-- @@ L394-394 verbatim
@[simp] lemma eq_dia_multidia_one [DecidableEq F] : s.dia = s.multidia 1 := by rfl


-- @@ L396-396 verbatim
@[simp] lemma eq_predia_premultidia_one : s.predia = s.premultidia 1 := by rfl


-- @@ L398-398 expanded
lemma multidia_coe [DecidableEq F] : (s.multidia n) = Set.multidia n (s : Set F) := by simp_all


-- @@ L400-400 expanded
lemma dia_coe [DecidableEq F] : s.dia = Set.dia (s : Set F) := by simpa using multidia_coe (n := 1)


-- @@ L402-403 expanded
lemma multidia_mem_coe [DecidableEq F] : φ ∈ s.multidia n ↔ φ ∈ Set.multidia n (↑s : Set F) := by
  constructor <;> simp_all


-- @@ L405-405 expanded
lemma dia_mem_coe [DecidableEq F] : φ ∈ s.dia ↔ φ ∈ Set.dia (↑s : Set F) := by simp;


-- @@ L407-407 expanded
lemma premultidia_coe : (s.premultidia n) = Set.premultidia n (s : Set F) := by simp_all


-- @@ L409-409 expanded
lemma predia_coe : s.predia = Set.predia (↑s : Set F) := by simpa using premultidia_coe (n := 1)


-- @@ L411-416 expanded
lemma premultidia_multidia_eq_of_subset_multidia [DecidableEq F] {s : Finset F} {t : Set F}
    (hs : ↑s ⊆ Set.multidia n t) : (s.premultidia n).multidia n = s := by
  have := Set.eq_premultidia_multidia_of_subset_premultidia hs;
  rw [← premultidia_coe, ← multidia_coe] at this; exact Finset.coe_inj.mp this;


-- @@ L418-420 expanded
lemma predia_dia_eq_of_subset_dia [DecidableEq F] {s : Finset F} {t : Set F} (hs : ↑s ⊆ Set.dia t) :
    s.predia.dia = s := by simpa using premultidia_multidia_eq_of_subset_multidia (n := 1) hs


-- @@ L422-422 verbatim
end «lp_section_6»


-- @@ L424-424 verbatim
end Finset




-- @@ L428-428 verbatim
section «lp_section_7»


-- @@ L430-430 verbatim
variable [DecidableEq F]


-- @@ L432-434 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev List.multibox [Box F] (n : ℕ) : List F → List F :=
  fun l => Finset.multibox n l.toFinset |>.toList

-- @@ L435-436 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "□'^[" n:90 "]" l:80 => List.multibox n l


-- @@ L438-440 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev List.multidia [Dia F] (n : ℕ) : List F → List F :=
  fun l => Finset.multidia n l.toFinset |>.toList

-- @@ L441-442 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "◇'^[" n:90 "]" l:80 => List.multidia n l


-- @@ L444-445 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev List.box [Box F] : List F → List F := List.multibox (n := 1)

-- @@ L446-447 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "□'" => List.box


-- @@ L449-450 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev List.dia [Dia F] : List F → List F := List.multidia (n := 1)

-- @@ L451-452 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "◇'" => List.dia



-- @@ L455-457 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev List.premultibox [Box F] (n : ℕ) : List F → List F :=
  fun l => Finset.premultibox n l.toFinset |>.toList

-- @@ L458-459 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "□'⁻¹^[" n:90 "]" l:80 => List.premultibox n l


-- @@ L461-463 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev List.premultidia [Dia F] (n : ℕ) : List F → List F :=
  fun l => Finset.premultidia n l.toFinset |>.toList

-- @@ L464-465 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "◇'⁻¹^[" n:90 "]" l:80 => List.premultidia n l


-- @@ L467-468 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev List.prebox [Box F] : List F → List F := List.premultibox (n := 1)

-- @@ L469-470 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "□'⁻¹" => List.prebox


-- @@ L472-473 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected noncomputable abbrev List.predia [Dia F] : List F → List F := List.premultidia (n := 1)

-- @@ L474-475 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
prefix:80 "◇'⁻¹" => List.predia


-- @@ L477-477 verbatim
end «lp_section_7»


-- @@ L479-479 verbatim
namespace List


-- @@ L481-481 verbatim
variable {l : List F} {s : Set F} {φ : F}



-- @@ L484-488 expanded
lemma forall_multibox_of_subset_multibox [Box F] (h : ∀ φ ∈ l, φ ∈ Set.multibox n s) :
    ∀ φ ∈ l, ∃ ψ ∈ s, φ = multibox n ψ := by intro φ hp; obtain ⟨ψ, _, rfl⟩ := h φ hp; use ψ;


-- @@ L490-491 expanded
lemma forall_box_of_subset_box [Box F] (h : ∀ φ ∈ l, φ ∈ Set.box s) :
    ∀ φ ∈ l, ∃ ψ ∈ s, φ = Box.box ψ := by simpa using forall_multibox_of_subset_multibox (n := 1) h


-- @@ L494-498 expanded
lemma forall_multidia_of_subset_multidia [Dia F] (h : ∀ φ ∈ l, φ ∈ Set.multidia n s) :
    ∀ φ ∈ l, ∃ ψ ∈ s, φ = multidia n ψ := by intro φ hp; obtain ⟨ψ, _, rfl⟩ := h φ hp; use ψ;


-- @@ L500-501 expanded
lemma forall_dia_of_subset_dia [Dia F] (h : ∀ φ ∈ l, φ ∈ Set.dia s) :
    ∀ φ ∈ l, ∃ ψ ∈ s, φ = Dia.dia ψ := by simpa using forall_multidia_of_subset_multidia (n := 1) h


-- @@ L504-504 verbatim
variable [DecidableEq F]


-- @@ L506-506 verbatim
section «lp_section_8»


-- @@ L508-508 verbatim
variable [Box F]


-- @@ L510-510 expanded
@[simp]
lemma eq_box_multibox_one : List.box l = List.multibox 1 l := by rfl


-- @@ L512-512 expanded
@[simp]
lemma eq_prebox_premultibox_one : List.prebox l = List.premultibox 1 l := by rfl


-- @@ L515-515 expanded
@[simp 1100]
lemma multibox_nil : (List.multibox n ([] : List F)) = [] := by simp;


-- @@ L517-517 expanded
lemma box_nil : (List.box ([] : List F)) = [] := by simp;


-- @@ L520-520 expanded
@[simp 1100]
lemma premultibox_nil : (List.premultibox n ([] : List F)) = [] := by simp;


-- @@ L522-522 expanded
lemma prebox_nil : (List.prebox ([] : List F)) = [] := by simp;


-- @@ L525-525 expanded
@[simp 1100]
lemma multibox_single : (List.multibox n [φ]) = [multibox n φ] := by simp;


-- @@ L527-527 expanded
lemma box_single : (List.box [φ]) = [Box.box φ] := by simp;


-- @@ L530-533 expanded
lemma multibox_cons (hl : φ ∉ l) : List.multibox n (φ :: l) ~ multibox n φ :: List.multibox n l :=
  by simp only [List.multibox, Finset.multibox, List.toFinset_cons, Finset.image_insert];
  apply Finset.toList_insert; simp_all;


-- @@ L534-534 expanded
lemma box_cons (hl : φ ∉ l) : List.box (φ :: l) ~ Box.box φ :: List.box l :=
  multibox_cons hl


-- @@ L537-537 verbatim
end «lp_section_8»


-- @@ L539-539 verbatim
section «lp_section_9»


-- @@ L541-541 verbatim
variable [Dia F]


-- @@ L543-543 expanded
@[simp]
lemma eq_dia_multidia_one : List.dia l = List.multidia 1 l := by rfl


-- @@ L545-545 expanded
@[simp]
lemma eq_predia_premultidia_one : List.predia l = List.premultidia 1 l := by rfl


-- @@ L548-548 expanded
@[simp 1100]
lemma multidia_nil : (List.multidia n ([] : List F)) = [] := by simp;


-- @@ L550-550 expanded
lemma dia_nil : (List.dia ([] : List F)) = [] := by simp;


-- @@ L553-553 expanded
@[simp 1100]
lemma premultidia_nil : (List.premultidia n ([] : List F)) = [] := by simp;


-- @@ L555-555 expanded
lemma predia_nil : (List.predia ([] : List F)) = [] := by simp;


-- @@ L558-558 expanded
@[simp 1100]
lemma multidia_single : (List.multidia n [φ]) = [multidia n φ] := by simp;


-- @@ L560-560 expanded
lemma dia_single : (List.dia [φ]) = [Dia.dia φ] := by simp;


-- @@ L562-565 expanded
lemma multidia_cons (hl : φ ∉ l) : List.multidia n (φ :: l) ~ multidia n φ :: List.multidia n l :=
  by simp only [List.multidia, Finset.multidia, List.toFinset_cons, Finset.image_insert];
  apply Finset.toList_insert; simp_all;


-- @@ L567-567 expanded
lemma dia_cons (hl : φ ∉ l) : List.dia (φ :: l) ~ Dia.dia φ :: List.dia l :=
  multidia_cons hl


-- @@ L569-569 verbatim
end «lp_section_9»


-- @@ L571-571 verbatim
end List


-- @@ L573-573 verbatim
end «lp_section_1»
