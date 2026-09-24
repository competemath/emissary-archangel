module

public import Foundation.FirstOrder.SetTheory.Basic
public import Foundation.Vorspiel.ExistsUnique


-- @@ L6-10 verbatim
/-!
# Zermelo set theory

reference: Ralf Schindler, "Set Theory, Exploring Independence and Truth" [Sch14]
-/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
namespace FFL.FirstOrder.SetTheory


-- @@ L16-16 verbatim
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭]


-- @@ L18-24 verbatim
/-! ## Axiom of extentionality -/

lemma mem_ext_iff {x y : V} : x = y ↔ ∀ z, z ∈ x ↔ z ∈ y  := by
  have := by simpa [models_iff, Axiom.extentionality] using Theory.models V 𝗭 Zermelo.axiom_of_extentionality
  exact this x y

alias ⟨_, mem_ext⟩ := mem_ext_iff


-- @@ L26-26 verbatim
attribute [ext] mem_ext


-- @@ L28-31 verbatim
@[grind ->] lemma subset_antisymm {x y : V} (hxy : x ⊆ y) (hyx : y ⊆ x) : x = y := by
  ext z; constructor
  · exact hxy z
  · exact hyx z


-- @@ L33-33 verbatim
@[grind .] lemma subset_antisymm_iff {x y : V} : x ⊆ y ∧ y ⊆ x ↔ x = y := by aesop


-- @@ L35-53 verbatim
omit [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭] in
lemma subset_of_eq {x y : V} (h : x = y) : x ⊆ y := h ▸ subset_refl x

lemma SSubset.iff {x y : V} : x ⊊ y ↔ x ⊆ y ∧ ∃ z ∈ y, z ∉ x := by
  constructor
  · rintro ⟨ss, eq⟩
    refine ⟨ss, ?_⟩
    contrapose eq
    push Not at *
    apply subset_antisymm ss eq
  · rintro ⟨ss, ⟨z, hzy, hzx⟩⟩
    refine ⟨ss, ?_⟩
    rintro rfl
    contradiction

lemma SSubset.exists_not_mem {x y : V} (hxy : x ⊊ y) : ∃ z ∈ y, z ∉ x := (SSubset.iff.mp hxy).2

lemma SSubset.of_subset_of_not_mem_of_mem {x y z : V} (ss : x ⊆ y) (hzx : z ∉ x) (hzy : z ∈ y) : x ⊊ y :=
  SSubset.iff.mpr ⟨ss, z, hzy, hzx⟩


-- @@ L55-64 verbatim
/-! ## Axiom of empty set -/

lemma empty_exists : ∃ e : V, IsEmpty e := by simpa [models_iff] using! Theory.models V 𝗭 Zermelo.axiom_of_empty_set

lemma empty_existsUnique : ∃! e : V, IsEmpty e := by
  rcases empty_exists (V := V) with ⟨e, he⟩
  apply ExistsUnique.intro e he
  intro x hx
  ext y
  simp [hx.not_mem, he.not_mem]


-- @@ L66-66 verbatim
open Classical


-- @@ L68-68 verbatim
noncomputable scoped instance : EmptyCollection V := ⟨Classical.choose! empty_existsUnique⟩


-- @@ L70-70 verbatim
noncomputable instance : Inhabited V := Inhabited.mk ∅


-- @@ L72-72 verbatim
@[simp] lemma IsEmpty.empty : IsEmpty (∅ : V) := Classical.choose!_spec empty_existsUnique


-- @@ L74-74 verbatim
@[simp] lemma not_mem_empty {x} : x ∉ (∅ : V) := IsEmpty.empty.not_mem


-- @@ L76-77 verbatim
@[simp] lemma isEmpty_iff_eq_empty {x : V} :
    IsEmpty x ↔ x = ∅ := ⟨by intro h; ext; simp[h.not_mem], by rintro rfl; simp⟩


-- @@ L79-85 verbatim
@[simp] lemma ne_empty_iff_isNonempty {x : V} :
    x ≠ ∅ ↔ IsNonempty x := by simp [←isEmpty_iff_eq_empty]

lemma eq_empty_or_isNonempty (x : V) : x = ∅ ∨ IsNonempty x := by
  by_cases hx : x = ∅
  · simp_all
  · right; exact ne_empty_iff_isNonempty.mp hx


-- @@ L87-87 verbatim
@[simp] lemma empty_subset (x : V) : ∅ ⊆ x := by simp [subset_def]


-- @@ L89-89 verbatim
@[simp] lemma subset_empty_iff_eq_empty {x : V} : x ⊆ ∅ ↔ x = ∅ := by simp [mem_ext_iff, subset_def]


-- @@ L91-100 verbatim
/-! ## Axiom of pairing -/

lemma pairing_exists : ∀ x y : V, ∃ z : V, ∀ w, w ∈ z ↔ w = x ∨ w = y := by
  simpa [models_iff, Axiom.pairing] using Theory.models V 𝗭 Zermelo.axiom_of_pairing

lemma pairing_existsUnique (x y : V) : ∃! z : V, ∀ w, w ∈ z ↔ w = x ∨ w = y := by
  rcases pairing_exists x y with ⟨p, hp⟩
  apply ExistsUnique.intro p hp
  intro q hq
  ext z; simp_all


-- @@ L102-102 verbatim
noncomputable def doubleton (x y : V) : V := Classical.choose! (pairing_existsUnique x y)


-- @@ L104-104 verbatim
@[simp] lemma mem_doubleton_iff {x y z : V} : z ∈ doubleton x y ↔ z = x ∨ z = y := Classical.choose!_spec (pairing_existsUnique x y) z


-- @@ L106-106 verbatim
def doubleton.dfn : SetTheorySemisentence 3 := “p x y. ∀ z, z ∈ p ↔ z = x ∨ z = y”


-- @@ L108-109 verbatim
instance doubleton.defined : ℒₛₑₜ-function₂[V] doubleton via doubleton.dfn :=
  ⟨by intro v; simp [doubleton.dfn, doubleton]⟩


-- @@ L111-111 verbatim
instance doubleton.definable : ℒₛₑₜ-function₂[V] doubleton := doubleton.defined.to_definable


-- @@ L113-113 verbatim
@[simp] instance doubleton_isNonempty (x y : V) : IsNonempty (doubleton x y) := ⟨x, by simp⟩


-- @@ L115-115 verbatim
noncomputable def singleton (x : V) : V := doubleton x x


-- @@ L117-119 verbatim
noncomputable scoped instance : Singleton V V := ⟨singleton⟩

lemma singleton_def (x : V) : ({x} : V) = doubleton x x := rfl


-- @@ L121-121 verbatim
@[simp] lemma mem_singleton_iff {x z : V} : z ∈ ({x} : V) ↔ z = x := by simp [singleton_def]


-- @@ L123-123 verbatim
def singleton.dfn : SetTheorySemisentence 2 := “p x. !doubleton.dfn p x x”


-- @@ L125-126 verbatim
instance singleton.defined : ℒₛₑₜ-function₁[V] Singleton.singleton via singleton.dfn :=
  ⟨by intro v; simp [singleton.dfn]; rfl⟩


-- @@ L128-128 verbatim
instance singleton.definable : ℒₛₑₜ-function₁[V] Singleton.singleton := singleton.defined.to_definable


-- @@ L130-130 verbatim
@[simp] instance singleton_isNonempty (x : V) : IsNonempty ({x} : V) := ⟨x, by simp⟩


-- @@ L132-132 verbatim
@[simp] lemma singleton_subset_iff_mem {x y : V} : {x} ⊆ y ↔ x ∈ y := by simp [subset_def]


-- @@ L134-135 verbatim
@[simp] lemma singleton_ext_iff {x y : V} : ({x} : V) = {y} ↔ x = y := by
  simp [mem_ext_iff (x := {x})]


-- @@ L137-146 verbatim
/-! ## Axiom of union -/

lemma union_exists : ∀ x : V, ∃ y : V, ∀ z, z ∈ y ↔ ∃ w ∈ x, z ∈ w := by
  simpa [models_iff, Axiom.union] using Theory.models V 𝗭 Zermelo.axiom_of_union

lemma union_existsUnique (x : V) : ∃! y : V, ∀ z, z ∈ y ↔ ∃ w ∈ x, z ∈ w := by
  rcases union_exists x with ⟨u, hu⟩
  apply ExistsUnique.intro u hu
  intro v hv
  ext z; simp_all


-- @@ L148-148 verbatim
noncomputable def sUnion (x : V) : V := Classical.choose! (union_existsUnique x)


-- @@ L150-152 verbatim
prefix:110 "⋃ˢ " => sUnion

lemma mem_sUnion_iff {x z : V} : z ∈ ⋃ˢ x ↔ ∃ y ∈ x, z ∈ y := Classical.choose!_spec (union_existsUnique x) z


-- @@ L154-154 verbatim
def sUnion.dfn : SetTheorySemisentence 2 := “u x. ∀ z, z ∈ u ↔ ∃ w ∈ x, z ∈ w”


-- @@ L156-157 verbatim
instance sUnion.defined : ℒₛₑₜ-function₁[V] sUnion via sUnion.dfn :=
  ⟨by intro v; simp [sUnion.dfn, mem_sUnion_iff, mem_ext_iff]⟩


-- @@ L159-159 verbatim
instance sUnion.definable : ℒₛₑₜ-function₁[V] sUnion := sUnion.defined.to_definable


-- @@ L161-161 verbatim
@[simp] lemma sUnion_empty_eq_empty : ⋃ˢ (∅ : V) = ∅ := by ext; simp [mem_sUnion_iff]


-- @@ L163-163 verbatim
@[simp] lemma sUnion_singleton_eq (x : V) : ⋃ˢ ({x} : V) = x := by ext; simp [mem_sUnion_iff]


-- @@ L165-170 verbatim
@[simp] lemma IsNonempty_sUnion_iff {x : V} : IsNonempty (⋃ˢ x) ↔ ∃ y ∈ x, IsNonempty y := by
  simp only [isNonempty_def, mem_sUnion_iff]
  grind

lemma subset_sUnion_of_mem {x y : V} (h : x ∈ y) : x ⊆ ⋃ˢ y := fun z hz ↦ by
  simp only [mem_sUnion_iff]; grind


-- @@ L172-172 verbatim
/-! ### Union of two sets -/


-- @@ L174-174 verbatim
noncomputable def union (x y : V) : V := ⋃ˢ (doubleton x y)


-- @@ L176-178 verbatim
noncomputable scoped instance : Union V := ⟨union⟩

lemma union_def (x y : V) : x ∪ y = ⋃ˢ (doubleton x y) := rfl


-- @@ L180-180 verbatim
def union.dfn : SetTheorySemisentence 3 := “u x y. ∀ d, !doubleton.dfn d x y → !sUnion.dfn u d”


-- @@ L182-183 verbatim
instance union.defined : ℒₛₑₜ-function₂[V] Union.union via union.dfn :=
  ⟨by intro v; simp [union.dfn, union_def]⟩


-- @@ L185-185 verbatim
instance union.definable : ℒₛₑₜ-function₂[V] Union.union := union.defined.to_definable


-- @@ L187-187 verbatim
@[simp] lemma mem_union_iff {x y z : V} : z ∈ x ∪ y ↔ z ∈ x ∨ z ∈ y := by simp [union_def, mem_sUnion_iff]


-- @@ L189-193 verbatim
@[simp] lemma union_self_eq (x : V) : x ∪ x = x := by ext; simp

lemma union_comm (x y : V) : x ∪ y = y ∪ x := by ext; simp; tauto

lemma union_assoc (x y z : V) : (x ∪ y) ∪ z = x ∪ (y ∪ z) := by ext; simp; tauto


-- @@ L195-195 verbatim
@[simp] lemma union_empty (x : V) : x ∪ ∅ = x := by ext; simp


-- @@ L197-197 verbatim
@[simp] lemma empty_union (x : V) : ∅ ∪ x = x := by ext; simp


-- @@ L199-200 verbatim
@[simp] lemma IsNonempty_union_iff {x y : V} : IsNonempty (x ∪ y) ↔ IsNonempty x ∨ IsNonempty y := by
  simp only [isNonempty_def, mem_union_iff]; grind


-- @@ L202-202 verbatim
@[simp] lemma subset_union_left (x y : V) : x ⊆ x ∪ y := fun z hz ↦ by simp [hz]


-- @@ L204-204 verbatim
@[simp] lemma subset_union_right (x y : V) : y ⊆ x ∪ y := fun z hz ↦ by simp [hz]


-- @@ L206-206 verbatim
@[simp] lemma union_eq_iff_right {x y : V} : x ∪ y = x ↔ y ⊆ x := by simp [mem_ext_iff, subset_def]


-- @@ L208-208 verbatim
@[simp] lemma union_eq_iff_left {x y : V} : x ∪ y = y ↔ x ⊆ y := by simp [mem_ext_iff, subset_def]


-- @@ L210-210 verbatim
/-! ### Insert -/


-- @@ L212-212 verbatim
protected noncomputable def insert (x y : V) : V := {x} ∪ y


-- @@ L214-216 verbatim
noncomputable scoped instance : Insert V V := ⟨SetTheory.insert⟩

lemma insert_def (x y : V) : insert x y = {x} ∪ y := rfl


-- @@ L218-218 verbatim
def insert.dfn : SetTheorySemisentence 3 := “u x y. ∀ s, !singleton.dfn s x → !union.dfn u s y”


-- @@ L220-221 verbatim
instance insert.defined : ℒₛₑₜ-function₂[V] insert via insert.dfn :=
  ⟨by intro v; simp [insert.dfn, insert_def]⟩


-- @@ L223-223 verbatim
instance insert.definable : ℒₛₑₜ-function₂[V] insert := insert.defined.to_definable


-- @@ L225-225 verbatim
@[simp] lemma mem_insert {x y z : V} : z ∈ insert x y ↔ z = x ∨ z ∈ y := by simp [insert_def]


-- @@ L227-231 verbatim
@[simp] lemma insert_empty_eq (x : V) : (insert x ∅ : V) = {x} := by ext; simp

lemma union_insert (x y : V) : x ∪ insert y z = insert y (x ∪ z) := by ext; simp; tauto

lemma pair_eq_doubleton (x y : V) : {x, y} = doubleton x y := by ext; simp


-- @@ L233-233 verbatim
@[simp] lemma sUnion_insert (x y : V) : ⋃ˢ insert x y = x ∪ ⋃ˢ y := by ext; simp [mem_sUnion_iff]


-- @@ L235-235 verbatim
@[simp] lemma subset_insert (x y : V) : y ⊆ insert x y := by simp [insert_def]


-- @@ L237-237 verbatim
@[simp] instance insert_isNonempty (x y : V) : IsNonempty (insert x y) := ⟨x, by simp⟩


-- @@ L239-241 verbatim
@[simp] lemma intsert_union (x y z : V) :
    insert x y ∪ z = insert x (y ∪ z) := by
  ext; simp only [mem_union_iff, mem_insert]; grind


-- @@ L243-245 verbatim
@[simp] lemma singleton_inter (x y : V) :
    {x} ∪ y = insert x y := by
  ext; simp


-- @@ L247-248 verbatim
@[simp, grind =] lemma insert_eq_self_of_mem {x y : V} (hx : x ∈ y) : insert x y = y := by
  ext; simp only [mem_insert, or_iff_right_iff_imp]; grind


-- @@ L250-259 verbatim
/-! ## Axiom of power set -/

lemma power_exists : ∀ x : V, ∃ y : V, ∀ z, z ∈ y ↔ z ⊆ x := by
  simpa [models_iff, Axiom.power] using Theory.models V 𝗭 Zermelo.axiom_of_power_set

lemma power_existsUnique (x : V) : ∃! y : V, ∀ z, z ∈ y ↔ z ⊆ x := by
  rcases power_exists x with ⟨p, hp⟩
  apply ExistsUnique.intro p hp
  intro q hq
  ext; simp_all


-- @@ L261-261 verbatim
noncomputable def power (x : V) : V := Classical.choose! (power_existsUnique x)


-- @@ L263-263 verbatim
prefix:110 "℘ " => power


-- @@ L265-265 verbatim
@[simp] lemma mem_power_iff {x z : V} : z ∈ ℘ x ↔ z ⊆ x := Classical.choose!_spec (power_existsUnique x) z


-- @@ L267-267 verbatim
def power.dfn : SetTheorySemisentence 2 := “p x. ∀ z, z ∈ p ↔ z ⊆ x”


-- @@ L269-270 verbatim
instance power.defined : ℒₛₑₜ-function₁[V] power via power.dfn :=
  ⟨by intro v; simp [power.dfn, power]⟩


-- @@ L272-272 verbatim
instance power.definable : ℒₛₑₜ-function₁[V] power := power.defined.to_definable


-- @@ L274-274 verbatim
@[simp] lemma empty_mem_power (x : V) : ∅ ∈ ℘ x := by simp [mem_power_iff]


-- @@ L276-276 verbatim
@[simp] lemma self_mem_power (x : V) : x ∈ ℘ x := by simp [mem_power_iff]


-- @@ L278-278 verbatim
@[simp] lemma power_empty : ℘ (∅ : V) = {∅} := by ext; simp [mem_power_iff]


-- @@ L280-280 verbatim
@[simp] instance power_nonempty (x : V) : IsNonempty (℘ x) := ⟨x, by simp⟩


-- @@ L282-299 verbatim
/-! ## Aussonderungsaxiom -/

lemma separation_exists_eval (x : V) (φ : SetTheorySemiformula V 1) : ∃ y : V, ∀ z : V, z ∈ y ↔ z ∈ x ∧ φ.Eval ![z] id := by
  -- have : Inhabited V := inhabited_of_nonempty inferInstance
  let f := φ.enumerateFVar
  let ψ := (Rew.rewriteMap φ.idxOfFVar) ▹ φ
  have := by simpa [models_iff, Semiformula.eval_univCl, Axiom.separationSchema] using Theory.models V 𝗭 (Zermelo.axiom_of_separation ψ)
  simpa [ψ, f, Semiformula.eval_rewriteMap, Matrix.constant_eq_singleton] using this f x

lemma separation_exists (x : V) (P : V → Prop) (hP : ℒₛₑₜ-predicate P) : ∃ y : V, ∀ z : V, z ∈ y ↔ z ∈ x ∧ P z := by
  rcases hP with ⟨φ, hP⟩
  simpa [hP.iff] using separation_exists_eval x φ

lemma separation_existsUnique (x : V) (P : V → Prop) (hP : ℒₛₑₜ-predicate P) : ∃! y : V, ∀ z : V, z ∈ y ↔ z ∈ x ∧ P z := by
  rcases separation_exists x P hP with ⟨s, hs⟩
  apply ExistsUnique.intro s hs
  intro u hu
  ext; simp_all


-- @@ L301-301 verbatim
noncomputable def sep (x : V) (P : V → Prop) (hP : ℒₛₑₜ-predicate P := by definability) : V := Classical.choose! (separation_existsUnique x P hP)


-- @@ L303-304 verbatim
@[simp] lemma mem_sep_iff {P : V → Prop} {hP : ℒₛₑₜ-predicate P} {z x : V} :
    z ∈ sep x P (hP := hP) ↔ z ∈ x ∧ P z := Classical.choose!_spec (separation_existsUnique x P hP) z


-- @@ L306-307 verbatim
@[simp] lemma sep_empty_eq (P : V → Prop) {hP : ℒₛₑₜ-predicate P} :
    sep ∅ P (hP := hP) = ∅ := by ext; simp


-- @@ L309-310 verbatim
@[simp] lemma sep_subset {P : V → Prop} {hP : ℒₛₑₜ-predicate P} {x : V} :
    sep x P (hP := hP) ⊆ x := by intro z; simp; tauto


-- @@ L312-312 verbatim
section set_notation


-- @@ L314-314 verbatim
open Lean Elab Term Meta


-- @@ L316-319 verbatim
/--
Set-builder notation.
-/
syntax (name := internalSetBuilder) "{" binderIdent " ∈ " term " ; " term "}" : term


-- @@ L321-325 verbatim
@[term_elab internalSetBuilder]
meta def elabInternalSetBuilder : TermElab
  | `({ $x:ident ∈ $s ; $p }), expectedType? => do
    elabTerm (← `(sep $s (fun $x:ident ↦ $p))) expectedType?
  | _, _ => throwUnsupportedSyntax


-- @@ L327-333 verbatim
@[app_unexpander sep]
meta def sep.unexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $s $P $_) =>
    match P with
    | `(fun $x:ident ↦ $p) => `({ $x:ident ∈ $s ; $p })
    | _ => throw ()
  | _ => throw ()


-- @@ L335-335 verbatim
end set_notation


-- @@ L337-337 verbatim
/-! ### Intersection -/


-- @@ L339-339 verbatim
noncomputable def sInter (x : V) : V := {z ∈ ⋃ˢ x ; ∀ y ∈ x, z ∈ y}


-- @@ L341-345 verbatim
prefix:110 "⋂ˢ " => sInter

lemma mem_sInter_iff {x : V} : z ∈ ⋂ˢ x ↔ IsNonempty x ∧ ∀ y ∈ x, z ∈ y := by
  simp only [sInter, mem_sep_iff, mem_sUnion_iff, and_congr_left_iff, isNonempty_def]
  grind


-- @@ L347-347 verbatim
def sInter.dfn : SetTheorySemisentence 2 := “u x. ∀ z, z ∈ u ↔ !isNonempty x ∧ ∀ y ∈ x, z ∈ y”


-- @@ L349-350 verbatim
instance sInter.defined : ℒₛₑₜ-function₁[V] sInter via sInter.dfn :=
  ⟨by intro v; simp [sInter.dfn, mem_ext_iff, mem_sInter_iff]⟩


-- @@ L352-352 verbatim
instance sInter.definable : ℒₛₑₜ-function₁[V] sInter := sInter.defined.to_definable


-- @@ L354-356 verbatim
@[simp] lemma mem_sInter_iff_of_nonempty {x : V} [hx : IsNonempty x] :
    z ∈ ⋂ˢ x ↔ ∀ y ∈ x, z ∈ y := by
  simp [SetTheory.mem_sInter_iff, hx]


-- @@ L358-358 verbatim
@[simp] lemma sInter_empty_eq : ⋂ˢ (∅ : V) = ∅ := by ext; simp [mem_sInter_iff]


-- @@ L360-365 verbatim
@[simp] lemma sInter_singleton (x : V) : ⋂ˢ {x} = x := by ext; simp [mem_sInter_iff_of_nonempty]

lemma sInter_subset_of_mem_of_nonempty {x y : V} [IsNonempty y] (h : x ∈ y) : ⋂ˢ y ⊆ x := by
  intro z hz
  simp only [mem_sInter_iff_of_nonempty] at hz
  grind


-- @@ L367-374 verbatim
@[simp] lemma subset_sInter_iff_of_nonempty {x y : V} [IsNonempty y] : x ⊆ ⋂ˢ y ↔ ∀ z ∈ y, x ⊆ z := by
  constructor
  · intro h z hzy
    exact subset_trans h (sInter_subset_of_mem_of_nonempty hzy)
  · intro h z hz
    simp only [mem_sInter_iff_of_nonempty]
    intro v hvy
    exact h v hvy z hz


-- @@ L376-376 verbatim
/-! #### Intersection of two sets -/


-- @@ L378-378 verbatim
noncomputable def inter (x y : V) : V := ⋂ˢ {x, y}


-- @@ L380-382 verbatim
noncomputable instance : Inter V := ⟨inter⟩

lemma inter_def (x y : V) : x ∩ y = ⋂ˢ {x, y} := rfl


-- @@ L384-385 verbatim
@[simp] lemma mem_inter_iff {x y z : V} : z ∈ x ∩ y ↔ z ∈ x ∧ z ∈ y := by
  simp [inter_def, mem_sInter_iff_of_nonempty]


-- @@ L387-387 verbatim
def inter.dfn : SetTheorySemisentence 3 := “u x y. ∀ z, z ∈ u ↔ z ∈ x ∧ z ∈ y”


-- @@ L389-389 verbatim
instance inter.defined : ℒₛₑₜ-function₂[V] Inter.inter via inter.dfn := ⟨by intro v; simp [inter.dfn, mem_ext_iff]⟩


-- @@ L391-391 verbatim
instance inter.definable : ℒₛₑₜ-function₂[V] Inter.inter := inter.defined.to_definable


-- @@ L393-397 verbatim
@[simp] lemma inter_self (x : V) : x ∩ x = x := by ext; simp

lemma inter_comm (x y : V) : x ∩ y = y ∩ x := by ext; simp; tauto

lemma inter_assoc (x y z : V) : (x ∩ y) ∩ z = x ∩ (y ∩ z) := by ext; simp; tauto


-- @@ L399-399 verbatim
@[simp] lemma inter_empty (x : V) : x ∩ ∅ = ∅ := by ext; simp


-- @@ L401-401 verbatim
@[simp] lemma empty_inter (x : V) : ∅ ∩ x = ∅ := by ext; simp


-- @@ L403-403 verbatim
@[simp] lemma inter_eq_left_of_subset {x y : V} (h : x ⊆ y) : x ∩ y = x := by ext z; simpa using h z


-- @@ L405-405 verbatim
@[simp] lemma inter_eq_right_of_subset {x y : V} (h : y ⊆ x) : x ∩ y = y := by ext z; simpa using h z


-- @@ L407-408 verbatim
@[simp] lemma sInter_insert (x y : V) [hy : IsNonempty y] : ⋂ˢ insert x y = x ∩ ⋂ˢ y := by
  ext; simp [*, mem_sInter_iff_of_nonempty]


-- @@ L410-412 verbatim
@[simp, grind =] lemma intsert_inter_of_mem (x y z : V) (hx : x ∈ z) :
    insert x y ∩ z = insert x (y ∩ z) := by
  ext; simp only [inter_comm, mem_inter_iff, mem_insert]; grind


-- @@ L414-416 verbatim
@[simp, grind =] lemma intsert_inter_of_not_mem (x y z : V) (hx : x ∉ z) :
    insert x y ∩ z = y ∩ z := by
  ext; simp only [inter_comm, mem_inter_iff, mem_insert]; grind


-- @@ L418-422 verbatim
@[simp, grind =] lemma singleton_inter_of_mem {x y : V} (hx : x ∈ y) :
    {x} ∩ y = {x} := by
  ext
  simp only [inter_comm, mem_inter_iff, mem_singleton_iff,
    and_iff_right_iff_imp]; grind


-- @@ L424-427 verbatim
@[simp, grind =] lemma singleton_inter_of_not_mem {x y : V} (hx : x ∉ y) :
    {x} ∩ y = ∅ := by
  ext; simp only [inter_comm, mem_inter_iff, mem_singleton_iff, not_mem_empty, iff_false, not_and]
  grind


-- @@ L429-429 verbatim
/-! ### Set difference -/


-- @@ L431-431 verbatim
noncomputable def sdiff (x y : V) : V := {z ∈ x ; z ∉ y}


-- @@ L433-435 verbatim
noncomputable instance : SDiff V := ⟨sdiff⟩

lemma sdiff_def (x y : V) : x \ y = {z ∈ x ; z ∉ y} := rfl


-- @@ L437-437 verbatim
@[simp] lemma mem_sdiff_iff {x y z : V} : z ∈ x \ y ↔ z ∈ x ∧ z ∉ y := by simp [sdiff_def]


-- @@ L439-439 verbatim
def sdiff.dfn : SetTheorySemisentence 3 := “d x y. ∀ z, z ∈ d ↔ z ∈ x ∧ z ∉ y”


-- @@ L441-441 verbatim
instance sdiff.defined : ℒₛₑₜ-function₂[V] SDiff.sdiff via sdiff.dfn := ⟨by intro v; simp [sdiff.dfn, mem_ext_iff]⟩


-- @@ L443-443 verbatim
instance sdiff.definable : ℒₛₑₜ-function₂[V] SDiff.sdiff := sdiff.defined.to_definable


-- @@ L445-445 verbatim
@[simp] lemma sdiff_empty (x : V) : x \ ∅ = x := by ext; simp


-- @@ L447-447 verbatim
@[simp] lemma empty_sdiff (x : V) : ∅ \ x = ∅ := by ext; simp


-- @@ L449-453 verbatim
@[simp, grind =] lemma singleton_sdiff_of_mem {x z : V} (hx : x ∈ z) :
    {x} \ z = ∅ := by
  ext
  simp only [mem_sdiff_iff, mem_singleton_iff, not_mem_empty,
    iff_false, not_and, Decidable.not_not]; grind


-- @@ L455-457 verbatim
@[simp, grind =] lemma singleton_sdiff_of_not_mem {x z : V} (hx : x ∉ z) :
    {x} \ z = {x} := by
  ext; simp only [mem_sdiff_iff, mem_singleton_iff, and_iff_left_iff_imp]; grind


-- @@ L459-461 verbatim
@[simp, grind =] lemma insert_sdiff_of_mem {x y z : V} (hx : x ∈ z) :
    insert x y \ z = y \ z := by
  ext; simp only [mem_sdiff_iff, mem_insert, and_congr_left_iff, or_iff_right_iff_imp]; grind


-- @@ L463-470 verbatim
@[simp, grind =] lemma insert_sdiff_of_not_mem {x y z : V} (hx : x ∉ z) :
    insert x y \ z = insert x (y \ z) := by
  ext; simp only [mem_sdiff_iff, mem_insert]; grind

lemma isNonempty_sdiff_of_ssubset {x y : V} : x ⊊ y → IsNonempty (y \ x) := by
  intro h
  rcases h.exists_not_mem with ⟨z, hzy, hzx⟩
  exact ⟨z, by simp_all⟩


-- @@ L472-472 verbatim
/-! ### Kuratowski's ordered pair -/


-- @@ L474-474 verbatim
noncomputable def kpair (x y : V) : V := {{x}, {x, y}}


-- @@ L476-477 verbatim
/-- `⟨x, y, z, ...⟩ₖ` notation for `kpair` -/
syntax "⟨" term,* "⟩ₖ" : term


-- @@ L479-481 verbatim
macro_rules
  | `(⟨$term:term, $terms:term,*⟩ₖ) => `(kpair $term ⟨$terms,*⟩ₖ)
  | `(⟨$term:term⟩ₖ) => `($term)


-- @@ L483-486 verbatim
@[app_unexpander kpair]
meta def pairUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term $term2) => `(⟨$term, $term2⟩ₖ)
  | _ => throw ()



-- @@ L489-489 verbatim
noncomputable def kpair.π₁ (z : V) : V := ⋃ˢ ⋂ˢ z


-- @@ L491-491 verbatim
noncomputable def kpair.π₂ (z : V) : V := ⋃ˢ {x ∈ ⋃ˢ z; x ∈ ⋂ˢ z → ⋃ˢ z = ⋂ˢ z}


-- @@ L493-494 verbatim
def kpair.dfn : SetTheorySemisentence 3 :=
  “k x y. ∀ x', !singleton.dfn x' x → ∀ z, !doubleton.dfn z x y → !doubleton.dfn k x' z”


-- @@ L496-497 verbatim
instance kpair.defined : ℒₛₑₜ-function₂[V] kpair via kpair.dfn :=
  ⟨by intro v; simp [kpair.dfn, kpair, ←pair_eq_doubleton]⟩


-- @@ L499-499 verbatim
instance kpair.definable : ℒₛₑₜ-function₂[V] kpair := kpair.defined.to_definable


-- @@ L501-501 verbatim
def kpair.π₁.dfn : SetTheorySemisentence 2 := “p₁ x. ∀ i, !sInter.dfn i x → !sUnion.dfn p₁ i”


-- @@ L503-504 verbatim
instance kpair.π₁.defined : ℒₛₑₜ-function₁[V] kpair.π₁ via kpair.π₁.dfn :=
  ⟨by intro v; simp [kpair.π₁.dfn, π₁]⟩


-- @@ L506-506 verbatim
instance kpair.π₁.definable : ℒₛₑₜ-function₁[V] kpair.π₁ := kpair.π₁.defined.to_definable


-- @@ L508-509 verbatim
def kpair.π₂.dfn : SetTheorySemisentence 2 :=
  “p₂ x. ∀ u, !sUnion.dfn u x → ∀ i, !sInter.dfn i x → ∀ s, (∀ z, z ∈ s ↔ (z ∈ u ∧ (z ∈ i → u = i))) → !sUnion.dfn p₂ s”


-- @@ L511-523 verbatim
instance kpair.π₂.defined : ℒₛₑₜ-function₁[V] kpair.π₂ via kpair.π₂.dfn :=
  ⟨by intro v
      let u := ⋃ˢ v 1
      let i := ⋂ˢ v 1
      suffices (∀ s, (∀ z, z ∈ s ↔ z ∈ u ∧ (z ∈ i → u = i)) → v 0 = ⋃ˢ s) ↔ v 0 = ⋃ˢ {x ∈ u ; x ∈ i → u = i} by
        simpa [kpair.π₂.dfn, π₂] using this
      constructor
      · intro h
        apply h
        intro z; simp
      · intro e s hs; rw [e]
        congr; ext
        simp only [mem_sep_iff]; grind⟩


-- @@ L525-525 verbatim
instance kpair.π₂.definable : ℒₛₑₜ-function₁[V] kpair.π₂ := kpair.π₂.defined.to_definable


-- @@ L527-528 verbatim
@[grind =, simp] lemma kpair.π₁_kpair (x y : V) :
    π₁ ⟨x, y⟩ₖ = x := by simp [π₁, kpair]


-- @@ L530-548 verbatim
@[grind =, simp] lemma kpair.π₂_kpair (x y : V) :
    π₂ ⟨x, y⟩ₖ = y := calc
  π₂ ⟨x, y⟩ₖ = ⋃ˢ {z ∈ {x, y} ; z = x → ({x, y} : V) = {x}} := by simp [π₂, kpair]
  _              = ⋃ˢ {y} := by
    congr; ext z
    suffices (z = x ∨ z = y) ∧ (z = x → y = x) ↔ z = y by simpa [mem_ext_iff (x := {x, y})]
    grind
  _              = y := by simp

lemma kpair_inj {x₁ x₂ y₁ y₂ : V} :
    ⟨x₁, y₁⟩ₖ = ⟨x₂, y₂⟩ₖ → x₁ = x₂ ∧ y₁ = y₂ := by
  intro h
  constructor
  · calc x₁ = kpair.π₁ ⟨x₁, y₁⟩ₖ := by simp
    _       = kpair.π₁ ⟨x₂, y₂⟩ₖ := by rw [h]
    _       = x₂                 := by simp
  · calc y₁ = kpair.π₂ ⟨x₁, y₁⟩ₖ := by simp
    _       = kpair.π₂ ⟨x₂, y₂⟩ₖ := by rw [h]
    _       = y₂                 := by simp


-- @@ L550-552 verbatim
@[simp, grind =] lemma kpair_iff {x₁ x₂ y₁ y₂ : V} :
    ⟨x₁, y₁⟩ₖ = ⟨x₂, y₂⟩ₖ ↔ x₁ = x₂ ∧ y₁ = y₂ :=
  ⟨kpair_inj, by rintro ⟨rfl, rfl⟩; rfl⟩


-- @@ L554-554 verbatim
/-! ### Product -/


-- @@ L556-556 verbatim
noncomputable def prod (X Y : V) : V := {z ∈ ℘ ℘ (X ∪ Y) ; ∃ x ∈ X, ∃ y ∈ Y, z = ⟨x, y⟩ₖ}


-- @@ L558-563 verbatim
infix:60 " ×ˢ " => prod

lemma mem_prod_iff {X Y z : V} : z ∈ X ×ˢ Y ↔ ∃ x ∈ X, ∃ y ∈ Y, z = ⟨x, y⟩ₖ := by
  suffices ∀ x ∈ X, ∀ y ∈ Y, z = ⟨x, y⟩ₖ → z ∈ ℘ ℘ (X ∪ Y) by simpa [prod]
  rintro x hx y hy rfl
  simp_all [mem_power_iff, subset_def, kpair]


-- @@ L565-565 verbatim
def prod.dfn : SetTheorySemisentence 3 := “p X Y. ∀ z, z ∈ p ↔ ∃ x ∈ X, ∃ y ∈ Y, !kpair.dfn z x y”


-- @@ L567-568 verbatim
instance prod.defined : ℒₛₑₜ-function₂[V] prod via prod.dfn :=
  ⟨by intro v; simp [prod.dfn, mem_ext_iff, mem_prod_iff]⟩


-- @@ L570-570 verbatim
instance prod.definable : ℒₛₑₜ-function₂[V] prod := prod.defined.to_definable


-- @@ L572-572 verbatim
@[simp] lemma prod_empty (x : V) : x ×ˢ ∅ = ∅ := by ext; simp [mem_prod_iff]


-- @@ L574-574 verbatim
@[simp] lemma empty_prod (x : V) : ∅ ×ˢ x = ∅ := by ext; simp [mem_prod_iff]


-- @@ L576-586 verbatim
@[simp] lemma kpair_mem_iff {x y X Y : V} : ⟨x, y⟩ₖ ∈ X ×ˢ Y ↔ x ∈ X ∧ y ∈ Y := by
  simp [mem_prod_iff]

lemma prod_subset_prod_of_subset {X₁ X₂ Y₁ Y₂ : V} (hX : X₁ ⊆ X₂) (hY : Y₁ ⊆ Y₂) : X₁ ×ˢ Y₁ ⊆ X₂ ×ˢ Y₂ := by
  intro p hp
  have : ∃ x ∈ X₁, ∃ y ∈ Y₁, p = ⟨x, y⟩ₖ := by simpa [mem_prod_iff] using hp
  rcases this with ⟨x, hx, y, hy, rfl⟩
  simp [hX _ hx, hY _ hy]

lemma union_prod (x y z : V) : (x ∪ y) ×ˢ z = (x ×ˢ z) ∪ (y ×ˢ z) := by
  ext v; simp only [mem_prod_iff, mem_union_iff]; grind


-- @@ L588-597 verbatim
@[simp] lemma singleton_prod_singleton (x y : V) : ({x} ×ˢ {y} : V) = {⟨x, y⟩ₖ} := by
  ext z; simp [mem_prod_iff]

lemma insert_kpair_subset_insert_prod_insert_of_subset_prod {R X Y : V} (h : R ⊆ X ×ˢ Y) (x y : V) :
    insert ⟨x, y⟩ₖ R ⊆ insert x X ×ˢ insert y Y := by
  intro z hz
  rcases show z = ⟨x, y⟩ₖ ∨ z ∈ R by simpa using hz with (rfl | hz)
  · simp
  · exact prod_subset_prod_of_subset
      (show X ⊆ insert x X by simp) (show Y ⊆ insert y Y by simp) z (h z hz)


-- @@ L599-599 verbatim
/-! ## Axiom of infinity -/


-- @@ L601-603 verbatim
noncomputable def succ (x : V) : V := insert x x

lemma mem_succ_iff {x y : V} : y ∈ succ x ↔ y = x ∨ y ∈ x := by simp [succ]


-- @@ L605-605 verbatim
abbrev succ.dfn := isSucc


-- @@ L607-608 verbatim
instance succ.defined : ℒₛₑₜ-function₁[V] succ via succ.dfn :=
  ⟨fun v ↦ by simp [mem_succ_iff, succ.dfn, isSucc, mem_ext_iff (x := v 0)]⟩


-- @@ L610-610 verbatim
instance succ.definable : ℒₛₑₜ-function₁[V] succ := succ.defined.to_definable


-- @@ L612-612 verbatim
@[simp] lemma mem_succ_self (x : V) : x ∈ succ x := by simp [mem_succ_iff]


-- @@ L614-614 verbatim
@[simp] lemma mem_subset_refl (x : V) : x ⊆ succ x := by simp [succ]


-- @@ L616-616 verbatim
def IsInductive (x : V) : Prop := ∅ ∈ x ∧ ∀ y ∈ x, succ y ∈ x


-- @@ L618-619 verbatim
def IsInductive.dfn : SetTheorySemisentence 1 :=
  “x. (∀ e, !isEmpty e → e ∈ x) ∧ (∀ y ∈ x, ∀ y', !succ.dfn y' y → y' ∈ x)”


-- @@ L621-622 verbatim
instance IsInductive.defined : ℒₛₑₜ-predicate[V] IsInductive via IsInductive.dfn :=
  ⟨fun v ↦ by simp [IsInductive, IsInductive.dfn]⟩


-- @@ L624-645 verbatim
instance IsInductive.definable : ℒₛₑₜ-predicate[V] IsInductive := IsInductive.defined.to_definable

lemma IsInductive.zero {I : V} (hI : IsInductive I) : ∅ ∈ I := hI.1

lemma IsInductive.succ {I : V} (hI : IsInductive I) {x : V} (hx : x ∈ I) : succ x ∈ I := hI.2 x hx

lemma isInductive_exists : ∃ I : V, IsInductive I := by
  simpa [models_iff, Axiom.infinity] using! Theory.models V 𝗭 Zermelo.axiom_of_infinity

lemma omega_existsUnique : ∃! ω : V, ∀ x, x ∈ ω ↔ ∀ I : V, IsInductive I → x ∈ I := by
  rcases isInductive_exists (V := V) with ⟨I, hI⟩
  let ω : V := {x ∈ I ; ∀ J : V, IsInductive J → x ∈ J}
  have : ∀ x, x ∈ ω ↔ ∀ I : V, IsInductive I → x ∈ I := by
    intro x; constructor
    · intro hx J hJ
      have hx : x ∈ I ∧ ∀ J : V, IsInductive J → x ∈ J := by simpa [ω] using hx
      exact hx.2 J hJ
    · intro h
      suffices x ∈ I ∧ ∀ J : V, IsInductive J → x ∈ J by simpa [ω]
      exact ⟨h I hI, h⟩
  apply ExistsUnique.intro ω this
  intros; ext; simp_all


-- @@ L647-650 verbatim
noncomputable def ω : V := Classical.choose! (omega_existsUnique)

lemma mem_ω_iff_mem_all_inductive {x : V} :
  x ∈ (ω : V) ↔ ∀ I : V, IsInductive I → x ∈ I := Classical.choose!_spec (omega_existsUnique) x


-- @@ L652-652 verbatim
def isω : SetTheorySemisentence 1 := “ω. ∀ x, x ∈ ω ↔ ∀ I, !IsInductive.dfn I → x ∈ I”


-- @@ L654-654 verbatim
instance ω.defined : ℒₛₑₜ-function₀[V] ω via isω := ⟨fun v ↦ by simp [isω, ω]⟩


-- @@ L656-656 verbatim
@[simp] lemma empty_mem_ω : ∅ ∈ (ω : V) := mem_ω_iff_mem_all_inductive.mpr <| fun _ hI ↦ hI.zero


-- @@ L658-658 verbatim
@[simp] instance ω_nonempty : IsNonempty (ω : V) := ⟨⟨∅, by simp⟩⟩


-- @@ L660-664 verbatim
@[simp] lemma ω_succ_closed {x : V} : x ∈ (ω : V) → succ x ∈ (ω : V) := by
  intro hx
  apply mem_ω_iff_mem_all_inductive.mpr
  intro I hI
  exact hI.succ (mem_ω_iff_mem_all_inductive.mp hx I hI)


-- @@ L666-669 verbatim
@[simp] lemma ω_isInductive : IsInductive (ω : V) := ⟨empty_mem_ω, fun _ ↦ ω_succ_closed⟩

lemma IsInductive.ω_subset {I : V} (hI : IsInductive I) : (ω : V) ⊆ I :=
  fun _ hx ↦ mem_ω_iff_mem_all_inductive.mp hx I hI


-- @@ L671-673 verbatim
noncomputable def ofNat : ℕ → V
  |     0 => ∅
  | n + 1 => succ (ofNat n)


-- @@ L675-675 verbatim
noncomputable scoped instance (n) : OfNat V n := ⟨ofNat n⟩


-- @@ L677-681 verbatim
noncomputable scoped instance : NatCast V := ⟨ofNat⟩

lemma zero_def : (0 : V) = ∅ := rfl

lemma num_succ_def (n : ℕ) : ((n + 1 : ℕ) : V) = succ ↑n := rfl


-- @@ L683-683 verbatim
@[simp] lemma cast_zero_def : ((0 : ℕ) : V) = 0 := rfl


-- @@ L685-697 verbatim
@[simp] lemma cast_one_def : ((1 : ℕ) : V) = 1 := rfl

lemma one_def : (1 : V) = {0} := calc
  (1 : V) = succ ∅ := rfl
  _       = {∅} := by simp [succ]

lemma one_def' : (1 : V) = {∅} := one_def

lemma two_def : (2 : V) = {0, 1} := calc
  (2 : V) = succ 1     := rfl
  _       = insert 1 1 := by rfl
  _       = {1, 0}     := by rw [←one_def]
  _       = {0, 1}     := by ext; simp; tauto


-- @@ L699-703 verbatim
@[simp] lemma zero_ne_one : (0 : V) ≠ (1 : V) := by
  suffices ∅ ≠ {∅} by simpa [zero_def, one_def]
  intro e
  have := mem_ext_iff.mp e ∅
  simp at this


-- @@ L705-705 verbatim
@[simp] lemma one_ne_zero : (1 : V) ≠ (0 : V) := Ne.symm zero_ne_one


-- @@ L707-707 verbatim
@[simp] lemma mem_two_iff (x : V) : x ∈ (2 : V) ↔ x = 0 ∨ x = 1 := by simp [two_def]


-- @@ L709-709 verbatim
@[simp] lemma zero_mem_one : 0 ∈ (1 : V) := by simp [zero_def, one_def]


-- @@ L711-714 verbatim
@[simp] lemma ofNat_mem_ω (n : ℕ) : ↑n ∈ (ω : V) :=
  match n with
  |     0 => by simp [zero_def]
  | n + 1 => by simp [num_succ_def, ω_succ_closed (ofNat_mem_ω n)]


-- @@ L716-716 verbatim
@[simp] lemma zero_mem_ω : 0 ∈ (ω : V) := ofNat_mem_ω 0


-- @@ L718-718 verbatim
@[simp] lemma one_mem_ω : 1 ∈ (ω : V) := ofNat_mem_ω 1


-- @@ L720-720 verbatim
@[simp] lemma two_mem_ω : 2 ∈ (ω : V) := ofNat_mem_ω 2


-- @@ L722-736 verbatim
@[elab_as_elim]
lemma naturalNumber_induction (P : V → Prop) (hP : ℒₛₑₜ-predicate P)
    (zero : P 0) (succ : ∀ x ∈ (ω : V), P x → P (succ x)) : ∀ x ∈ (ω : V), P x := by
  let p : V := {x ∈ ω ; P x}
  have : IsInductive p := by
    constructor
    · simpa [p]
    · intro x hx
      have hx : x ∈ (ω : V) ∧ P x := by simpa [p] using hx
      suffices SetTheory.succ x ∈ ω ∧ P (SetTheory.succ x) by simpa [p]
      refine ⟨ω_succ_closed hx.1, succ x hx.1 hx.2⟩
  have : ω ⊆ p := this.ω_subset
  intro x hx
  have : x ∈ (ω : V) ∧ P x := by simpa [p] using this x hx
  exact this.2


-- @@ L738-745 verbatim
/-! ## Axiom of foundation -/

lemma foundation : ∀ x : V, [IsNonempty x] → ∃ y ∈ x, ∀ z ∈ x, z ∉ y := by
  simpa [models_iff, Axiom.foundation] using Theory.models V 𝗭 Zermelo.axiom_of_foundation

lemma foundation' (x : V) [IsNonempty x] : ∃ y ∈ x, x ∩ y = ∅ := by
  rcases foundation x with ⟨y, hyx, H⟩
  exact ⟨y, hyx, by ext z; simpa using H z⟩


-- @@ L747-761 verbatim
@[simp] lemma mem_irrefl (x : V) : x ∉ x := by
  simpa using foundation ({x} : V)

lemma ne_of_mem {x y : V} : x ∈ y → x ≠ y := by
  rintro h rfl; simp_all

lemma mem_asymm {x y : V} : x ∈ y → y ∉ x := by
  intro hxy hyx
  have : y ∉ x ∨ x ∉ y := by simpa using foundation ({x, y} : V)
  rcases this with (_ | _) <;> simp_all

lemma mem_asymm₃ {x y z : V} : x ∈ y → y ∈ z → z ∉ x := by
  intro hxy hyz
  have : y ∉ x ∧ z ∉ x := by simpa [hxy, hyz] using foundation ({x, y, z} : V)
  exact this.2


-- @@ L763-766 verbatim
@[simp] lemma ne_succ (x : V) : x ≠ succ x := by
  intro h
  have : x ∈ succ x := mem_succ_self x
  simp [←h] at this


-- @@ L768-768 verbatim
end FFL.FirstOrder.SetTheory
