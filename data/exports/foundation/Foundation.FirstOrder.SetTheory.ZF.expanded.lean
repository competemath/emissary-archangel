module

public import Foundation.FirstOrder.SetTheory.Z


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-7 verbatim
namespace FFL.FirstOrder.SetTheory


-- @@ L9-9 verbatim
variable {V : Type*} [SetStructure V] [Nonempty V] [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙]


-- @@ L11-11 verbatim
/-! ## Ersatzaxiom -/


-- @@ L13-29 verbatim
open Classical

lemma replacement_exists_eval (φ : SetTheorySemiformula V 2) (X : V) (h : (∀ x : V, ∃! y : V, φ.Eval ![x, y] id)) :
    ∃ Y : V, ∀ y : V, y ∈ Y ↔ ∃ x ∈ X, φ.Eval ![x, y] id := by
  /- `φ` can have finitely many free variables of type `V`, these are interpreted by `id : V → V` as finitely many parameters in `V`.
  `f` enumerates the parameters of `φ`. -/
  let f := φ.enumerateFVar
  /- While `φ` has free variables of type `V`, `ψ` has free variables of type `ℕ`.
  Since `f` enumerates the parameters, it is intended to be the valuation of the free variables of `ψ`. -/
  let ψ := (Rew.rewriteMap φ.idxOfFVar) ▹ φ

  have whole := by simpa [models_iff, Semiformula.eval_univCl, Axiom.replacementSchema] using Theory.models V 𝗭𝗙 (ZermeloFraenkel.axiom_of_replacement ψ)

  have cond : ∀ x, ∃! y : V, ψ.Eval ![x, y] f := by
    simpa [ψ, f, Semiformula.eval_rewriteMap]

  simpa [ψ, f, Semiformula.eval_rewriteMap, Matrix.constant_eq_singleton] using whole f cond X


-- @@ L31-40 verbatim
/--
Replacement exists (for a relation).
-/
lemma replacement_rel_exists (X : V) (R : V → V → Prop) (h : ∀ x, ∃! y, R x y) (hR : ℒₛₑₜ-relation R) :
    ∃ Y : V, ∀ y, y ∈ Y ↔ ∃ x ∈ X, R x y := by
  rcases hR with ⟨φ, hR⟩
  -- Put hR in a useful form
  have hR {x y : V} := by simpa using hR.iff ![x, y]
  have cond : ∀ x : V, ∃! y : V, φ.Eval ![x, y] id := by simpa [← hR] using h
  simpa [hR] using replacement_exists_eval φ X cond


-- @@ L42-50 verbatim
/--
Replacement exists uniquely (for a relation).
-/
lemma replacement_rel_existsUnique (X : V) (R : V → V → Prop) (h : ∀ x, ∃! y, R x y) (hR : ℒₛₑₜ-relation R) :
    ∃! Y : V, ∀ y : V, y ∈ Y ↔ ∃ x ∈ X, R x y := by
  rcases replacement_rel_exists X R h hR with ⟨s, hs⟩
  apply ExistsUnique.intro s hs
  intro u hu
  ext; simp_all


-- @@ L52-61 verbatim
/--
Replacement exists uniquely for a function.
-/
lemma replacement_existsUnique (X : V) (F : V → V) (hF : ℒₛₑₜ-function₁ F) :
    ∃! Y : V, ∀ y, y ∈ Y ↔ ∃ x ∈ X, y = F x := by
  let R (x y : V) : Prop := Function.Graph F y x
  have h : ∀ (x : V), ∃! y, R x y := by
    intro x
    simp only [Function.Graph, existsUnique_eq, R]
  exact replacement_rel_existsUnique X R h (by definability)


-- @@ L63-67 verbatim
/--
Replacement exists for a function.
-/
lemma replacement_exists (X : V) (F : V → V) (hF : ℒₛₑₜ-function₁ F) :
    ∃ Y : V, ∀ y, y ∈ Y ↔ ∃ x ∈ X, y = F x := (replacement_existsUnique X F hF).exists


-- @@ L69-72 verbatim
/--
The axiom of replacement for a relation.
-/
noncomputable def replRel (R : V → V → Prop) (h : ∀ x, ∃! y, R x y) (hR : ℒₛₑₜ-relation R := by definability) (X : V) : V := Classical.choose! (replacement_rel_existsUnique X R h hR)


-- @@ L74-77 verbatim
/--
The axiom of replacement.
-/
noncomputable def repl (F : V → V) (hF : ℒₛₑₜ-function₁ F := by definability) (X : V) : V := Classical.choose! (replacement_existsUnique X F hF)


-- @@ L79-79 verbatim
/-! ## Variants of replacement -/


-- @@ L81-98 verbatim
/--
A stronger variant of (unique existence of) replacement, which only requires uniqueness on `X`.
The statement of this lemma is thanks to tosiaki.
-/
lemma replacement_rel_existsUnique_of_mem_existsUnique (X : V) (R : V → V → Prop) (h : ∀ x ∈ X, ∃! y, R x y) (hR : ℒₛₑₜ-relation R) :
    ∃! Y : V, ∀ y, y ∈ Y ↔ ∃ x ∈ X, R x y := by
  /- Proof sketch: Define `R' x y` to hold iff `x ∈ X` and `R x y`, or `x ∉ X` and `y = ∅`.
  Show that `∀ x, ∃! y, R' x y` holds, by case subdivision on whether `x ∈ X` or not.
  Obtain `Y` from replacement.
  Then, for any `y`, we have that `y ∈ Y` iff `∃ x ∈ X, R x y`, iff `∃ x ∈ X, R' x y`.
  -/
  let R' (x y : V) : Prop := x ∈ X ∧ R x y ∨ x ∉ X ∧ y = ∅
  have cond : ∀ x, ∃! y, R' x y := by
    intro x
    refine Classical.byCases (p := x ∈ X) ?_ ?_ <;> (intro hx; simp_all [R'])
  obtain ⟨Y, hY⟩ := replacement_rel_exists X R' cond (by definability)
  use Y
  aesop


-- @@ L100-105 verbatim
/--
A stronger variant of replacement, which only requires uniqueness on `X`.
The statement of this lemma is thanks to tosiaki.
-/
lemma replacement_rel_exists_of_mem_existsUnique (X : V) (R : V → V → Prop) (h : ∀ x ∈ X, ∃! y, R x y) (hR : ℒₛₑₜ-relation R) :
    ∃ Y : V, ∀ y, y ∈ Y ↔ ∃ x ∈ X, R x y := (replacement_rel_existsUnique_of_mem_existsUnique X R h hR).exists


-- @@ L107-111 verbatim
/--
The axiom of replacement, only assuming uniqueness on `X`.
-/
noncomputable def replRelOverSet (X : V) (R : V → V → Prop) (h : ∀ x ∈ X, ∃! y, R x y) (hR : ℒₛₑₜ-relation R := by definability) : V :=
  Classical.choose! (replacement_rel_existsUnique_of_mem_existsUnique X R h hR)


-- @@ L113-113 verbatim
/-! ## Various lemmas -/


-- @@ L115-116 verbatim
@[simp] lemma replRel_spec {X y : V} {R : V → V → Prop} {h : ∀ x ∈ X, ∃! y, R x y} (hR : ℒₛₑₜ-relation R) :
    y ∈ replRelOverSet X R h hR ↔ ∃ x ∈ X, R x y := Classical.choose!_spec (replacement_rel_existsUnique_of_mem_existsUnique X R h hR) y


-- @@ L118-119 verbatim
@[simp] lemma repl_spec {X y : V} {F : V → V} (hF : ℒₛₑₜ-function₁ F) :
    y ∈ repl F hF X ↔ ∃ x ∈ X, y = F x := Classical.choose!_spec (replacement_existsUnique X F hF) y


-- @@ L121-122 verbatim
@[simp] lemma replRelOverSet_spec {X y : V} {R : V → V → Prop} {h : ∀ x ∈ X, ∃! y, R x y} (hR : ℒₛₑₜ-relation R) :
    y ∈ replRelOverSet X R h ↔ ∃ x ∈ X, R x y := Classical.choose!_spec (replacement_rel_existsUnique_of_mem_existsUnique X R h hR) y


-- @@ L124-127 verbatim
@[simp, definability] instance repl_definable {F : V → V} [hF : ℒₛₑₜ-function₁ F] : ℒₛₑₜ-function₁ (repl F hF) := by
  suffices ℒₛₑₜ-relation (fun y x ↦ y = repl F hF x) by exact this
  simp only [repl, choose!_eq_iff_right]
  definability


-- @@ L129-129 verbatim
/-! ### Definability Gadgets for Replacement -/


-- @@ L131-131 verbatim
namespace Repl


-- @@ L133-134 verbatim
structure Blueprint (arity : ℕ) where
  graph : SetTheorySemisentence (arity + 2)


-- @@ L136-137 verbatim
def Blueprint.resultDef (b : Blueprint arity) : SetTheorySemisentence (arity + 2) :=
  “Y X. ∀ y, y ∈ Y ↔ ∃ x ∈ X, !b.graph y x ⋯”


-- @@ L139-139 verbatim
variable (V)


-- @@ L141-143 verbatim
structure Construction {arity : ℕ} (b : Blueprint arity) where
  map : (Fin arity → V) → V → V
  map_defined : DefinedFunction (fun v ↦ map (v ·.succ) (v 0)) b.graph


-- @@ L145-145 verbatim
variable {V}


-- @@ L147-147 verbatim
namespace Construction


-- @@ L149-149 verbatim
variable {arity : ℕ} {b : Blueprint arity} (c : Construction V b)


-- @@ L151-152 verbatim
instance map_definable :
  (ℒₛₑₜ).DefinableFunction (fun v ↦ c.map (v ·.succ) (v 0)) := c.map_defined.to_definable


-- @@ L154-167 verbatim
noncomputable def result (v : Fin arity → V) : V → V := repl (c.map v) (by
  refine ⟨(Rew.embSubsts (#0 :> #1 :> fun i : Fin arity ↦ &(v i))) ▹ b.graph, ?_⟩
  intro x
  simpa [Semiformula.eval_embSubsts, Matrix.comp_vecCons', Function.comp_def]
    using c.map_defined.iff (x 0 :> x 1 :> v))

lemma result_defined : DefinedFunction (fun v ↦ c.result (v ·.succ) (v 0)) b.resultDef := .mk fun v ↦ by
  constructor
  · intro h
    simp [Blueprint.resultDef] at h
    ext y
    simpa [result, c.map_defined.iff] using h y
  · intro h
    simp [Blueprint.resultDef, result, c.map_defined.iff, h]


-- @@ L169-169 verbatim
@[simp] lemma eval_resultDef : b.resultDef.Evalb v ↔ v 0 = c.result (v ·.succ.succ) (v 1) := c.result_defined.iff v


-- @@ L171-172 verbatim
@[simp] lemma mem_result : y ∈ c.result v X ↔ ∃ x ∈ X, y = c.map v x := by
  simp [result, repl_spec]


-- @@ L174-174 verbatim
end Construction


-- @@ L176-176 verbatim
end Repl


-- @@ L178-178 verbatim
end FFL.FirstOrder.SetTheory
