module

public import Foundation.FirstOrder.Arithmetic.HFS.Fixpoint


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-10 verbatim
/-!

# Vec

-/


-- @@ L12-12 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L14-14 verbatim
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


-- @@ L16-16 verbatim
section adjoin


-- @@ L18-18 verbatim
noncomputable instance : Adjoin V V := ⟨(⟪·, ·⟫ + 1)⟩


-- @@ L20-20 verbatim
scoped infixr:67 " ∷ " => adjoin


-- @@ L22-22 verbatim
syntax "?[" term,* "]" : term


-- @@ L24-27 verbatim
macro_rules
  | `(?[$term:term, $terms:term,*]) => `(adjoin $term ?[$terms,*])
  | `(?[$term:term]) => `(adjoin $term 0)
  | `(?[]) => `(0)


-- @@ L29-35 verbatim
@[app_unexpander Adjoin.adjoin]
meta def adjoinUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term ?[$terms,*]) => `(?[$term, $terms,*])
  | `($_ $term 0) => `(?[$term])
  | _ => throw ()

lemma adjoin_def (x v : V) : x ∷ v = ⟪x, v⟫ + 1 := rfl


-- @@ L37-37 verbatim
@[simp] lemma fstIdx_adjoin (x v : V) : fstIdx (x ∷ v) = x := by simp [adjoin_def, fstIdx]


-- @@ L39-41 verbatim
@[simp] lemma sndIdx_adjoin (x v : V) : sndIdx (x ∷ v) = v := by simp [adjoin_def, sndIdx]

lemma succ_eq_adjoin (x : V) : x + 1 = π₁ x ∷ π₂ x := by simp [adjoin_def]


-- @@ L43-43 verbatim
@[simp] lemma lt_adjoin (x v : V) : x < x ∷ v := by simp [adjoin_def, lt_succ_iff_le]


-- @@ L45-45 verbatim
@[simp] lemma lt_adjoin' (x v : V) : v < x ∷ v := by simp [adjoin_def, lt_succ_iff_le]


-- @@ L47-47 verbatim
@[simp] lemma zero_lt_adjoin (x v : V) : 0 < x ∷ v := by simp [adjoin_def]


-- @@ L49-49 verbatim
@[simp] lemma adjoin_ne_zero (x v : V) : x ∷ v ≠ 0 := by simp [adjoin_def]


-- @@ L51-56 verbatim
@[simp] lemma zero_ne_adjoin (x v : V) : 0 ≠ x ∷ v := by symm; simp [adjoin_def]

lemma nil_or_adjoin (z : V) : z = 0 ∨ ∃ x v, z = x ∷ v := by
  rcases zero_or_succ z with (rfl | ⟨z, rfl⟩)
  · left; rfl
  · right; exact ⟨π₁ z, π₂ z, by simp [succ_eq_adjoin]⟩


-- @@ L58-62 verbatim
@[simp] lemma adjoin_inj (x₁ x₂ v₁ v₂ : V) :
    x₁ ∷ v₁ = x₂ ∷ v₂ ↔ x₁ = x₂ ∧ v₁ = v₂ := by simp [adjoin_def]

lemma adjoin_le_adjoin {x₁ x₂ v₁ v₂ : V} (hx : x₁ ≤ x₂) (hv : v₁ ≤ v₂) :
    x₁ ∷ v₁ ≤ x₂ ∷ v₂ := by simpa [adjoin_def] using pair_le_pair hx hv


-- @@ L64-64 verbatim
section


-- @@ L66-67 verbatim
def _root_.FFL.FirstOrder.Arithmetic.adjoinDef : 𝚺₀.Semisentence 3 :=
  .mkSigma “w x v. ∃ xv < w, !pairDef xv x v ∧ w = xv + 1”


-- @@ L69-69 verbatim
instance adjoin_defined : 𝚺₀-Function₂ (adjoin : V → V → V) via adjoinDef := .mk fun v ↦ by simp_all [adjoinDef, adjoin_def]


-- @@ L71-71 verbatim
instance adjoin_definable : 𝚺₀-Function₂ (adjoin : V → V → V) := adjoin_defined.to_definable


-- @@ L73-73 verbatim
instance adjoin_definable' (ℌ) : ℌ-Function₂ (adjoin : V → V → V) := adjoin_definable.of_zero


-- @@ L75-76 verbatim
def _root_.FFL.FirstOrder.Arithmetic.mkVec₁Def : 𝚺₀.Semisentence 2 := .mkSigma
  “s x. !adjoinDef s x 0”


-- @@ L78-78 verbatim
instance mkVec₁_defined : 𝚺₀-Function₁ (fun x : V ↦ ?[x]) via mkVec₁Def := .mk fun v ↦ by simp [mkVec₁Def]


-- @@ L80-80 verbatim
instance mkVec₁_definable : 𝚺₀-Function₁ (fun x : V ↦ ?[x]) := mkVec₁_defined.to_definable


-- @@ L82-82 verbatim
instance mkVec₁_definable' (ℌ) : ℌ-Function₁ (fun x : V ↦ ?[x]) := mkVec₁_definable.of_zero


-- @@ L84-85 verbatim
def _root_.FFL.FirstOrder.Arithmetic.mkVec₂Def : 𝚺₁.Semisentence 3 := .mkSigma
  “s x y. ∃ sy, !mkVec₁Def sy y ∧ !adjoinDef s x sy”


-- @@ L87-87 verbatim
instance mkVec₂_defined : 𝚺₁-Function₂ (fun x y : V ↦ ?[x, y]) via mkVec₂Def := .mk fun v ↦ by simp [mkVec₂Def]


-- @@ L89-89 verbatim
instance mkVec₂_definable : 𝚺₁-Function₂ (fun x y : V ↦ ?[x, y]) := mkVec₂_defined.to_definable


-- @@ L91-91 verbatim
instance mkVec₂_definable' (Γ m) : Γ-[m + 1]-Function₂ (fun x y : V ↦ ?[x, y]) := mkVec₂_definable.of_sigmaOne


-- @@ L93-93 verbatim
end


-- @@ L95-95 verbatim
end adjoin


-- @@ L97-101 verbatim
/-!

### N-th element of List

-/


-- @@ L103-103 verbatim
namespace Nth


-- @@ L105-106 verbatim
def Phi (C : Set V) (pr : V) : Prop :=
  (∃ v, pr = ⟪v, 0, fstIdx v⟫) ∨ (∃ v i x, pr = ⟪v, i + 1, x⟫ ∧ ⟪sndIdx v, i, x⟫ ∈ C)


-- @@ L108-120 verbatim
private lemma phi_iff (C pr : V) :
    Phi {x | x ∈ C} pr ↔
    (∃ v ≤ pr, ∃ fst ≤ v, fst = fstIdx v ∧ pr = ⟪v, 0, fst⟫) ∨
    (∃ v ≤ pr, ∃ i ≤ pr, ∃ x ≤ pr, pr = ⟪v, i + 1, x⟫ ∧ ∃ snd ≤ v, snd = sndIdx v ∧ ∃ six < C, six = ⟪snd, i, x⟫ ∧ six ∈ C) := by
  constructor
  · rintro (⟨v, rfl⟩ | ⟨v, i, x, rfl, hC⟩)
    · left; exact ⟨v, by simp, _, by simp, rfl, rfl⟩
    · right; exact ⟨v, by simp,
        i, le_trans (le_trans (by simp) (le_pair_left _ _)) (le_pair_right _ _),
        x, le_trans (by simp) (le_pair_right _ _), rfl, _, by simp, rfl, _, lt_of_mem hC, rfl, hC⟩
  · rintro (⟨v, _, _, _, rfl, rfl⟩ | ⟨v, _, i, _, x, _, rfl, _, _, rfl, _, _, rfl, hC⟩)
    · left; exact ⟨v, rfl⟩
    · right; exact ⟨v, i, x, rfl, hC⟩


-- @@ L122-129 verbatim
def blueprint : Fixpoint.Blueprint 0 where
  core := .ofZero
    (.mkSigma “pr C.
    (∃ v <⁺ pr, ∃ fst <⁺ v, !fstIdxDef fst v ∧ !pair₃Def pr v 0 fst) ∨
    (∃ v <⁺ pr, ∃ i <⁺ pr, ∃ x <⁺ pr, !pair₃Def pr v (i + 1) x ∧
      ∃ snd <⁺ v, !sndIdxDef snd v ∧ ∃ six < C, !pair₃Def six snd i x ∧ six ∈ C)”
    (by simp))
    _


-- @@ L131-137 verbatim
def adjointruction : Fixpoint.Construction V blueprint where
  Φ := fun _ ↦ Phi
  defined := .of_zero <| .mk fun v ↦ by simp [phi_iff]
  monotone := by
    rintro C C' hC _ x (h | ⟨v, i, x, rfl, h⟩)
    · left; exact h
    · right; exact ⟨v, i, x, rfl, hC h⟩


-- @@ L139-143 verbatim
instance : adjointruction.Finite V where
  finite := by
    rintro C v x (h | ⟨v, i, x, rfl, h⟩)
    · exact ⟨0, Or.inl h⟩
    · exact ⟨⟪sndIdx v, i, x⟫ + 1, Or.inr ⟨v, i, x, rfl, h, by simp⟩⟩


-- @@ L145-145 verbatim
def Graph : V → Prop := adjointruction.Fixpoint ![]


-- @@ L147-147 verbatim
section


-- @@ L149-149 verbatim
def graphDef : 𝚺₁.Semisentence 1 := blueprint.fixpointDef


-- @@ L151-151 verbatim
instance graph_defined : 𝚺₁-Predicate (Graph : V → Prop) via graphDef := adjointruction.fixpoint_defined


-- @@ L153-153 verbatim
instance graph_definable : 𝚺₁-Predicate (Graph : V → Prop) := graph_defined.to_definable


-- @@ L155-155 verbatim
instance graph_definable' : 𝚺-[0 + 1]-Predicate (Graph : V → Prop) := graph_definable


-- @@ L157-157 verbatim
end


-- @@ L159-210 verbatim
/-- TODO: move-/
@[simp] lemma zero_ne_add_one (x : V) : 0 ≠ x + 1 := ne_of_lt (by simp)

lemma graph_case {pr : V} :
    Graph pr ↔
    (∃ v, pr = ⟪v, 0, fstIdx v⟫) ∨ (∃ v i x, pr = ⟪v, i + 1, x⟫ ∧ Graph ⟪sndIdx v, i, x⟫) :=
  adjointruction.case

lemma graph_zero {v x : V} :
    Graph ⟪v, 0, x⟫ ↔ x = fstIdx v := by
  constructor
  · intro h
    rcases graph_case.mp h with (⟨w, h⟩ | ⟨w, i, x, h, _⟩)
    · rcases show v = w ∧ x = fstIdx w by simpa using h with ⟨rfl, rfl, rfl⟩; rfl
    · simp at h
  · rintro rfl; exact graph_case.mpr <| Or.inl ⟨v, rfl⟩

lemma graph_succ {v i x : V} :
    Graph ⟪v, i + 1, x⟫ ↔ Graph ⟪sndIdx v, i, x⟫ := by
  constructor
  · intro h
    rcases graph_case.mp h with (⟨w, h⟩ | ⟨w, j, y, h, hw⟩)
    · simp at h
    · rcases show v = w ∧ i = j ∧ x = y by simpa using h with ⟨rfl, rfl, rfl⟩; exact hw
  · intro h; exact graph_case.mpr <| Or.inr ⟨v, i, x, rfl, h⟩

lemma graph_exists (v i : V) : ∃ x, Graph ⟪v, i, x⟫ := by
  suffices ∀ i' ≤ i, ∀ v' ≤ v, ∃ x, Graph ⟪v', i', x⟫ from this i (by simp) v (by simp)
  intro i' hi'
  induction i' using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    intro v' _
    exact ⟨fstIdx v', graph_case.mpr <| Or.inl ⟨v', rfl⟩⟩
  case succ i' ih =>
    intro v' hv'
    rcases ih (le_trans le_self_add hi') (sndIdx v') (le_trans (by simp) hv') with ⟨x, hx⟩
    exact ⟨x, graph_case.mpr <| Or.inr ⟨v', i', x, rfl, hx⟩⟩

lemma graph_unique {v i x₁ x₂ : V} : Graph ⟪v, i, x₁⟫ → Graph ⟪v, i, x₂⟫ → x₁ = x₂ := by
  induction i using ISigma1.pi1_succ_induction generalizing v x₁ x₂
  · definability
  case zero =>
    simp only [graph_zero]
    rintro rfl rfl; rfl
  case succ i ih =>
    simp only [graph_succ]
    exact ih

lemma graph_existsUnique (v i : V) : ∃! x, Graph ⟪v, i, x⟫ := by
  rcases graph_exists v i with ⟨x, hx⟩
  exact ExistsUnique.intro x hx (fun y hy ↦ graph_unique hy hx)


-- @@ L212-212 verbatim
end Nth


-- @@ L214-214 verbatim
section nth


-- @@ L216-216 verbatim
open Nth


-- @@ L218-218 verbatim
noncomputable def nth (v i : V) : V := Classical.choose! (graph_existsUnique v i)


-- @@ L220-229 verbatim
scoped notation:max v:max ".[" i "]" => nth v i

lemma nth_graph (v i : V) : Graph ⟪v, i, v.[i]⟫ :=
  Classical.choose!_spec (graph_existsUnique v i)

lemma nth_eq_of_graph {v i x : V} (h : Graph ⟪v, i, x⟫) : nth v i = x := graph_unique (nth_graph v i) h

lemma nth_zero (v : V) : v.[0] = fstIdx v := nth_eq_of_graph (graph_zero.mpr rfl)

lemma nth_succ (v i : V) : v.[i + 1] = (sndIdx v).[i] := nth_eq_of_graph (graph_succ.mpr <| nth_graph _ _)


-- @@ L231-232 verbatim
@[simp] lemma nth_adjoin_zero (x v : V) : (x ∷ v).[0] = x := by
  simp [nth_zero]


-- @@ L234-235 verbatim
@[simp] lemma nth_adjoin_succ (x v i : V) : (x ∷ v).[i + 1] = v.[i] := by
  simp [nth_succ]


-- @@ L237-238 verbatim
@[simp] lemma nth_adjoin_one (x v : V) : (x ∷ v).[1] = v.[0] := by
  simpa using nth_adjoin_succ x v 0


-- @@ L240-254 verbatim
@[simp] lemma nth_adjoin_two (x v : V) : (x ∷ v).[2] = v.[1] := by
  simpa [-nth_adjoin_succ, one_add_one_eq_two] using nth_adjoin_succ x v 1

lemma adjoin_cases (x : V) : x = 0 ∨ ∃ y v, x = y ∷ v := by
  rcases zero_or_succ x with (rfl | ⟨z, rfl⟩)
  · simp
  · right; exact ⟨π₁ z, π₂ z, by simp [adjoin]⟩

lemma adjoin_induction (Γ) {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (nil : P 0) (adjoin : ∀ x v, P v → P (x ∷ v)) : ∀ v, P v :=
  ISigma1.order_induction Γ hP (by
    intro v ih
    rcases nil_or_adjoin v with (rfl | ⟨x, v, rfl⟩)
    · exact nil
    · exact adjoin _ _ (ih v (by simp)))


-- @@ L256-259 verbatim
@[elab_as_elim]
lemma adjoin_ISigma1.sigma1_succ_induction {P : V → Prop} (hP : 𝚺₁-Predicate P)
    (nil : P 0) (adjoin : ∀ x v, P v → P (x ∷ v)) : ∀ v, P v :=
  adjoin_induction 𝚺 hP nil adjoin


-- @@ L261-264 verbatim
@[elab_as_elim]
lemma adjoin_ISigma1.pi1_succ_induction {P : V → Prop} (hP : 𝚷₁-Predicate P)
    (nil : P 0) (adjoin : ∀ x v, P v → P (x ∷ v)) : ∀ v, P v :=
  adjoin_induction 𝚷 hP nil adjoin


-- @@ L266-266 verbatim
section


-- @@ L268-269 verbatim
def _root_.FFL.FirstOrder.Arithmetic.nthDef : 𝚺₁.Semisentence 3 :=
  .mkSigma “y v i. ∃ pr, !pair₃Def pr v i y ∧ !graphDef pr”


-- @@ L271-276 verbatim
set_option linter.flexible false in
instance nth_defined : 𝚺₁-Function₂ (nth : V → V → V) via nthDef := .mk fun v ↦ by
  simp [nthDef]
  constructor
  · intro h; simp [nth_eq_of_graph h]
  · intro h; rw [h]; exact nth_graph _ _


-- @@ L278-278 verbatim
instance nth_definable : 𝚺₁-Function₂ (nth : V → V → V) := nth_defined.to_definable


-- @@ L280-280 verbatim
instance nth_definable' (Γ m) : Γ-[m + 1]-Function₂ (nth : V → V → V) := nth_definable.of_sigmaOne


-- @@ L282-285 verbatim
end

lemma adjoin_absolute (a v : ℕ) : ((a ∷ v : ℕ) : V) = (a : V) ∷ (v : V) := by
  simpa using DefinedFunction.shigmaZero_absolute_func V adjoin_defined adjoin_defined ![a, v]


-- @@ L287-290 verbatim
/-- TODO: move-/
lemma pi₁_zero : π₁ (0 : V) = 0 := nonpos_iff_eq_zero.mp (pi₁_le_self 0)

lemma pi₂_zero : π₂ (0 : V) = 0 := nonpos_iff_eq_zero.mp (pi₂_le_self 0)


-- @@ L292-311 verbatim
@[simp] lemma nth_zero_idx (i : V) : (0).[i] = 0 := by
  induction i using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp [nth_zero, fstIdx, pi₁_zero]
  case succ i ih => simp [nth_succ, sndIdx, pi₂_zero, ih]

lemma nth_lt_of_pos {v} (hv : 0 < v) (i : V) : v.[i] < v := by
  induction i using ISigma1.pi1_succ_induction generalizing v
  · definability
  case zero =>
    rcases zero_or_succ v with (rfl | ⟨v, rfl⟩)
    · simp at hv
    · simp [succ_eq_adjoin]
  case succ i ih =>
    rcases zero_or_succ v with (rfl | ⟨v, rfl⟩)
    · simp at hv
    · simp only [succ_eq_adjoin v, nth_adjoin_succ]
      rcases eq_zero_or_pos (π₂ v) with (h | h)
      · simp [h]
      · exact lt_trans (ih h) (by simp)


-- @@ L313-316 verbatim
@[simp] lemma nth_le (v i : V) : v.[i] ≤ v := by
  rcases eq_zero_or_pos v with (h | h)
  · simp [h]
  · exact le_of_lt <| nth_lt_of_pos h i


-- @@ L318-318 verbatim
end nth



-- @@ L321-325 verbatim
/-!

### Inductivly Construction of Function on List

-/


-- @@ L327-327 verbatim
namespace VecRec


-- @@ L329-331 verbatim
structure Blueprint (arity : ℕ) where
  nil : 𝚺₁.Semisentence (arity + 1)
  adjoin : 𝚺₁.Semisentence (arity + 4)


-- @@ L333-333 verbatim
namespace Blueprint


-- @@ L335-335 verbatim
variable {arity : ℕ} (β : Blueprint arity)


-- @@ L337-352 verbatim
def blueprint : Fixpoint.Blueprint arity where
  core := .mkDelta
    (.mkSigma “pr C.
        (∃ nil, !β.nil nil ⋯ ∧ !pairDef pr 0 nil) ∨
        (∃ x < pr, ∃ xs < pr, ∃ ih < C,
          ∃ xxs, !adjoinDef xxs x xs ∧
          ∃ adjoin, !β.adjoin adjoin x xs ih ⋯ ∧
          !pairDef pr xxs adjoin ∧ :⟪xs, ih⟫:∈ C)”
      (by simp))
    (.mkPi “pr C.
        (∀ nil, !β.nil nil ⋯ → !pairDef pr 0 nil) ∨
        (∃ x < pr, ∃ xs < pr, ∃ ih < C,
          ∀ xxs, !adjoinDef xxs x xs →
          ∀ adjoin, !β.adjoin adjoin x xs ih ⋯ →
          !pairDef pr xxs adjoin ∧ :⟪xs, ih⟫:∈ C)”
      (by simp))


-- @@ L354-354 verbatim
def graphDef : 𝚺₁.Semisentence (arity + 1) := β.blueprint.fixpointDef


-- @@ L356-357 verbatim
def resultDef : 𝚺₁.Semisentence (arity + 2) :=
  .mkSigma “y xs. ∃ pr, !pairDef pr xs y ∧ !β.graphDef pr ⋯”


-- @@ L359-359 verbatim
end Blueprint


-- @@ L361-361 verbatim
variable (V)


-- @@ L363-367 verbatim
structure Construction {arity : ℕ} (β : Blueprint arity) where
  nil (param : Fin arity → V) : V
  adjoin (param : Fin arity → V) (x xs ih) : V
  nil_defined : 𝚺₁.DefinedFunction nil β.nil
  adjoin_defined : 𝚺₁.DefinedFunction (fun v ↦ adjoin (v ·.succ.succ.succ) (v 0) (v 1) (v 2)) β.adjoin


-- @@ L369-369 verbatim
variable {V}


-- @@ L371-371 verbatim
namespace Construction


-- @@ L373-373 verbatim
variable {arity : ℕ} {β : Blueprint arity} (c : Construction V β)


-- @@ L375-376 verbatim
def Phi (param : Fin arity → V) (C : Set V) (pr : V) : Prop :=
  pr = ⟪0, c.nil param⟫ ∨ (∃ x xs ih, pr = ⟪x ∷ xs, c.adjoin param x xs ih⟫ ∧ ⟪xs, ih⟫ ∈ C)


-- @@ L378-389 verbatim
private lemma phi_iff (param : Fin arity → V) (C pr : V) :
    c.Phi param {x | x ∈ C} pr ↔
    pr = ⟪0, c.nil param⟫ ∨ (∃ x < pr, ∃ xs < pr, ∃ ih < C, pr = ⟪x ∷ xs, c.adjoin param x xs ih⟫ ∧ ⟪xs, ih⟫ ∈ C) := by
  constructor
  · rintro (h | ⟨x, xs, ih, rfl, hC⟩)
    · left; exact h
    · right
      exact ⟨x, lt_of_lt_of_le (by simp) (le_pair_left _ _),
        xs, lt_of_lt_of_le (by simp) (le_pair_left _ _), ih, lt_of_mem_rng hC, rfl , hC⟩
  · rintro (h | ⟨x, _, xs, _, ih, _, rfl, hC⟩)
    · left; exact h
    · right; exact ⟨x, xs, ih, rfl, hC⟩


-- @@ L391-401 verbatim
def adjointruction : Fixpoint.Construction V β.blueprint where
  Φ := c.Phi
  defined := .mk ⟨by
    intro v; simp [Blueprint.blueprint, c.nil_defined.iff, c.adjoin_defined.iff], by
    intro v
    symm
    simpa [Blueprint.blueprint, c.nil_defined.iff, c.adjoin_defined.iff] using c.phi_iff _ _ _⟩
  monotone := by
    rintro C C' hC _ x (h | ⟨v, i, hv, rfl, h⟩)
    · left; exact h
    · right; exact ⟨v, i, hv, rfl, hC h⟩


-- @@ L403-407 verbatim
instance : c.adjointruction.Finite V where
  finite := by
    rintro C v x (h | ⟨x, xs, ih, rfl, h⟩)
    · exact ⟨0, Or.inl h⟩
    · exact ⟨⟪xs, ih⟫ + 1, Or.inr ⟨x, xs, ih, rfl, h, by simp⟩⟩


-- @@ L409-409 verbatim
variable (param : Fin arity → V)


-- @@ L411-411 verbatim
def Graph : V → Prop := c.adjointruction.Fixpoint param


-- @@ L413-416 verbatim
section

lemma graph_defined : 𝚺₁.Defined (fun v ↦ c.Graph (v ·.succ) (v 0)) β.graphDef :=
  c.adjointruction.fixpoint_defined


-- @@ L418-418 verbatim
instance graph_definable : 𝚺₁.Definable (fun v ↦ c.Graph (v ·.succ) (v 0)) := c.graph_defined.to_definable


-- @@ L420-421 verbatim
instance graph_definable' (param) : 𝚺₁-Predicate (c.Graph param) := by
  simpa using HierarchySymbol.Definable.retractiont (n := 1) c.graph_definable (#0 :> fun i ↦ &(param i))


-- @@ L423-423 verbatim
instance graph_definable'' (param) : 𝚺-[0 + 1]-Predicate (c.Graph param) := c.graph_definable' param


-- @@ L425-425 verbatim
end


-- @@ L427-450 verbatim
variable {param}

lemma graph_case {pr : V} :
    c.Graph param pr ↔ pr = ⟪0, c.nil param⟫ ∨ (∃ x xs ih, pr = ⟪x ∷ xs, c.adjoin param x xs ih⟫ ∧ c.Graph param ⟪xs, ih⟫) :=
  c.adjointruction.case

lemma graph_nil {l : V} :
    c.Graph param ⟪0, l⟫ ↔ l = c.nil param := by
  constructor
  · intro h
    rcases c.graph_case.mp h with (h | ⟨x, xs, ih, h, _⟩)
    · rcases show l = c.nil param by simpa using h with ⟨rfl, rfl⟩; rfl
    · simp at h
  · rintro rfl; exact c.graph_case.mpr <| Or.inl rfl

lemma graph_adjoin {x xs y : V} :
    c.Graph param ⟪x ∷ xs, y⟫ ↔ ∃ y', y = c.adjoin param x xs y' ∧ c.Graph param ⟪xs, y'⟫ := by
  constructor
  · intro h
    rcases c.graph_case.mp h with (h | ⟨z, zs, v, h, hg⟩)
    · simp at h
    · rcases show (x = z ∧ xs = zs) ∧ y = c.adjoin param z zs v by simpa using h with ⟨⟨rfl, rfl⟩, rfl⟩
      exact ⟨v, rfl, hg⟩
  · rintro ⟨y, rfl, h⟩; exact c.graph_case.mpr <| Or.inr ⟨x, xs, y, rfl, h⟩


-- @@ L452-461 verbatim
variable (param)

lemma graph_exists (xs : V) : ∃ y, c.Graph param ⟪xs, y⟫ := by
  induction xs using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil =>
    exact ⟨c.nil param, c.graph_nil.mpr rfl⟩
  case adjoin x xs ih =>
    · rcases ih with ⟨y, hy⟩
      exact ⟨c.adjoin param x xs y, c.graph_adjoin.mpr ⟨y, rfl, hy⟩⟩


-- @@ L463-473 verbatim
variable {param}

lemma graph_unique {xs y₁ y₂ : V} : c.Graph param ⟪xs, y₁⟫ → c.Graph param ⟪xs, y₂⟫ → y₁ = y₂ := by
  induction xs using adjoin_ISigma1.pi1_succ_induction generalizing y₁ y₂
  · definability
  case nil =>
    simp only [graph_nil]; rintro rfl rfl; rfl
  case adjoin x v ih =>
    simp only [graph_adjoin, forall_exists_index, and_imp]
    rintro l₁ rfl h₁ l₂ rfl h₂
    rcases ih h₁ h₂; rfl


-- @@ L475-479 verbatim
variable (param)

lemma graph_existsUnique (xs : V) : ∃! y, c.Graph param ⟪xs, y⟫ := by
  rcases c.graph_exists param xs with ⟨y, hy⟩
  exact ExistsUnique.intro y hy (fun y' hy' ↦ c.graph_unique hy' hy)


-- @@ L481-487 verbatim
noncomputable def result (xs : V) : V := Classical.choose! (c.graph_existsUnique param xs)

lemma result_graph (xs : V) : c.Graph param ⟪xs, c.result param xs⟫ :=
  Classical.choose!_spec (c.graph_existsUnique param xs)

lemma result_eq_of_graph {xs y : V} (h : c.Graph param ⟪xs, y⟫) : c.result param xs = y :=
  c.graph_unique (c.result_graph param xs) h


-- @@ L489-489 verbatim
@[simp] lemma result_nil : c.result param (0 : V) = c.nil param := c.result_eq_of_graph param (c.graph_nil.mpr rfl)


-- @@ L491-493 verbatim
@[simp] lemma result_adjoin (x xs : V) :
    c.result param (x ∷ xs) = c.adjoin param x xs (c.result param xs) :=
  c.result_eq_of_graph param (c.graph_adjoin.mpr ⟨_, rfl, c.result_graph param xs⟩)


-- @@ L495-495 verbatim
section


-- @@ L497-502 verbatim
set_option linter.flexible false in
lemma result_defined : 𝚺₁.DefinedFunction (fun v ↦ c.result (v ·.succ) (v 0)) β.resultDef := .mk fun v ↦ by
  simp [Blueprint.resultDef, c.graph_defined.iff]
  constructor
  · intro h; symm; simpa using c.result_eq_of_graph _ h
  · intro h; rw [h]; exact c.result_graph _ _


-- @@ L504-505 verbatim
@[simp] lemma eval_resultDef (v : Fin (arity + 2) → V) :
    β.resultDef.val.Evalb v ↔ v 0 = c.result (v ·.succ.succ) (v 1) := c.result_defined.iff


-- @@ L507-508 verbatim
instance result_definable : 𝚺₁.DefinableFunction (fun v ↦ c.result (v ·.succ) (v 0)) :=
  c.result_defined.to_definable


-- @@ L510-511 verbatim
instance result_definable' (Γ m) :
    Γ-[m + 1].DefinableFunction (fun v ↦ c.result (v ·.succ) (v 0)) := c.result_definable.of_sigmaOne


-- @@ L513-513 verbatim
end


-- @@ L515-515 verbatim
end Construction


-- @@ L517-517 verbatim
end VecRec


-- @@ L519-523 verbatim
/-!

### Length of List

-/


-- @@ L525-525 verbatim
namespace Len


-- @@ L527-529 verbatim
def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. y = 0”
  adjoin := .mkSigma “y x xs ih. y = ih + 1”


-- @@ L531-535 verbatim
def adjointruction : VecRec.Construction V blueprint where
  nil _ := 0
  adjoin _ _ _ ih := ih + 1
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]


-- @@ L537-537 verbatim
end Len


-- @@ L539-539 verbatim
section len


-- @@ L541-541 verbatim
open Len


-- @@ L543-543 verbatim
noncomputable def len (v : V) : V := adjointruction.result ![] v


-- @@ L545-545 verbatim
@[simp] lemma len_nil : len (0 : V) = 0 := by simp [len, adjointruction]


-- @@ L547-547 verbatim
@[simp] lemma len_adjoin (x v : V) : len (x ∷ v) = len v + 1 := by simp [len, adjointruction]


-- @@ L549-549 verbatim
section


-- @@ L551-551 verbatim
def _root_.FFL.FirstOrder.Arithmetic.lenDef : 𝚺₁.Semisentence 2 := blueprint.resultDef


-- @@ L553-553 verbatim
instance len_defined : 𝚺₁-Function₁ (len : V → V) via lenDef := adjointruction.result_defined


-- @@ L555-555 verbatim
instance len_definable : 𝚺₁-Function₁ (len : V → V) := len_defined.to_definable


-- @@ L557-557 verbatim
instance len_definable' (Γ m) : Γ-[m + 1]-Function₁ (len : V → V) := len_definable.of_sigmaOne


-- @@ L559-559 verbatim
end


-- @@ L561-571 verbatim
@[simp] lemma len_zero_iff_eq_nil {v : V} : len v = 0 ↔ v = 0 := by
  rcases nil_or_adjoin v with (rfl | ⟨x, v, rfl⟩) <;> simp

lemma nth_lt_len {v i : V} (hl : len v ≤ i) : v.[i] = 0 := by
  induction v using adjoin_ISigma1.pi1_succ_induction generalizing i
  · definability
  case nil => simp
  case adjoin x v ih =>
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp at hl
    simpa using ih (by simpa using hl)


-- @@ L573-580 verbatim
@[simp] lemma len_le (v : V) : len v ≤ v := by
  induction v using adjoin_ISigma1.pi1_succ_induction
  · definability
  case nil => simp
  case adjoin x v ih =>
    simp only [len_adjoin]
    simp only [adjoin, add_le_add_iff_right]
    exact le_trans ih (le_pair_right x v)


-- @@ L582-617 verbatim
end len

lemma nth_ext {v₁ v₂ : V} (hl : len v₁ = len v₂) (H : ∀ i < len v₁, v₁.[i] = v₂.[i]) : v₁ = v₂ := by
  induction v₁ using adjoin_ISigma1.pi1_succ_induction generalizing v₂
  · definability
  case nil =>
    exact Eq.symm <| len_zero_iff_eq_nil.mp (by simp [←hl])
  case adjoin x₁ v₁ ih =>
    rcases nil_or_adjoin v₂ with (rfl | ⟨x₂, v₂, rfl⟩)
    · simp at hl
    have hx : x₁ = x₂ := by simpa using H 0 (by simp)
    have hv : v₁ = v₂ := ih (by simpa using hl) (by intro i hi; simpa using H (i + 1) (by simpa using hi))
    simp [hx, hv]

lemma nth_ext' (l : V) {v₁ v₂ : V} (hl₁ : len v₁ = l) (hl₂ : len v₂ = l) (H : ∀ i < l, v₁.[i] = v₂.[i]) : v₁ = v₂ := by
  rcases hl₂; exact nth_ext hl₁ (by simpa [hl₁] using H)

lemma le_of_nth_le_nth {v₁ v₂ : V} (hl : len v₁ = len v₂) (H : ∀ i < len v₁, v₁.[i] ≤ v₂.[i]) : v₁ ≤ v₂ := by
  induction v₁ using adjoin_ISigma1.pi1_succ_induction generalizing v₂
  · definability
  case nil => simp
  case adjoin x₁ v₁ ih =>
    rcases nil_or_adjoin v₂ with (rfl | ⟨x₂, v₂, rfl⟩)
    · simp at hl
    have hx : x₁ ≤ x₂ := by simpa using H 0 (by simp)
    have hv : v₁ ≤ v₂ := ih (by simpa using hl) (by intro i hi; simpa using H (i + 1) (by simpa using hi))
    exact adjoin_le_adjoin hx hv

lemma nth_lt_self {v i : V} (hi : i < len v) : v.[i] < v := by
  induction v using adjoin_ISigma1.pi1_succ_induction generalizing i
  · definability
  case nil => simp at hi
  case adjoin x v ih =>
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · simpa using lt_trans (ih (by simpa using hi)) (by simp)


-- @@ L619-645 verbatim
theorem sigmaOne_skolem_vec {R : V → V → Prop} (hP : 𝚺₁-Relation R) {l}
    (H : ∀ x < l, ∃ y, R x y) : ∃ v, len v = l ∧ ∀ i < l, R i v.[i] := by
  have : ∀ k ≤ l, ∃ v, len v = k ∧ ∀ i < k, R (l - k + i) v.[i] := by
    intro k hk
    induction k using ISigma1.sigma1_succ_induction
    · definability
    case zero => exact ⟨0, by simp⟩
    case succ k ih =>
      rcases ih (le_trans (by simp) hk) with ⟨v, hvk, hv⟩
      have : ∃ y, R (l - (k + 1)) y := H (l - (k + 1)) (by simp [tsub_lt_iff_left hk])
      rcases this with ⟨y, hy⟩
      exact ⟨y ∷ v, by simp [hvk], fun i hi ↦ by
        rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
        · simpa using hy
        · simpa [sub_succ_add_succ (succ_le_iff_lt.mp hk) i] using hv i (by simpa using hi)⟩
  simpa using this l (by rfl)

lemma eq_singleton_iff_len_eq_one {v : V} : len v = 1 ↔ ∃ x, v = ?[x] := by
  constructor
  · intro h; exact ⟨v.[0], nth_ext (by simp [h]) (by simp [h])⟩
  · rintro ⟨x, rfl⟩; simp

lemma eq_doubleton_of_len_eq_two {v : V} : len v = 2 ↔ ∃ x y, v = ?[x, y] := by
  constructor
  · intro h; exact ⟨v.[0], v.[1],
      nth_ext (by simp [h, one_add_one_eq_two]) (by simp [lt_two_iff_le_one, le_one_iff_eq_zero_or_one, h])⟩
  · rintro ⟨x, y, rfl⟩; simp [one_add_one_eq_two]



-- @@ L648-652 verbatim
/-!

### Maximum of List

-/


-- @@ L654-654 verbatim
namespace ListMax


-- @@ L656-658 verbatim
def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. y = 0”
  adjoin := .mkSigma “y x xs ih. !max.dfn y x ih”


-- @@ L660-664 verbatim
noncomputable def adjointruction : VecRec.Construction V blueprint where
  nil _ := 0
  adjoin _ x _ ih := max x ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]


-- @@ L666-666 verbatim
end ListMax


-- @@ L668-668 verbatim
section listMax


-- @@ L670-670 verbatim
open ListMax


-- @@ L672-672 verbatim
noncomputable def listMax (v : V) : V := adjointruction.result ![] v


-- @@ L674-674 verbatim
@[simp] lemma listMax_nil : listMax (0 : V) = 0 := by simp [listMax, adjointruction]


-- @@ L676-676 verbatim
@[simp] lemma listMax_adjoin (x v : V) : listMax (x ∷ v) = max x (listMax v) := by simp [listMax, adjointruction]


-- @@ L678-678 verbatim
section


-- @@ L680-680 verbatim
def _root_.FFL.FirstOrder.Arithmetic.listMaxDef : 𝚺₁.Semisentence 2 := blueprint.resultDef


-- @@ L682-682 verbatim
instance listMax_defined : 𝚺₁-Function₁ (listMax : V → V) via listMaxDef := adjointruction.result_defined


-- @@ L684-684 verbatim
instance listMax_definable : 𝚺₁-Function₁ (listMax : V → V) := listMax_defined.to_definable


-- @@ L686-686 verbatim
instance listMax_definable' (Γ m) : Γ-[m + 1]-Function₁ (listMax : V → V) := listMax_definable.of_sigmaOne


-- @@ L688-721 verbatim
end

lemma nth_le_listMax {i v : V} (h : i < len v) : v.[i] ≤ listMax v := by
  induction v using adjoin_ISigma1.pi1_succ_induction generalizing i
  · definability
  case nil => simp
  case adjoin x v ih =>
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · simp [ih (by simpa using h)]

lemma listMaxss_le {v z : V} (h : ∀ i < len v, v.[i] ≤ z) : listMax v ≤ z := by
  induction v using adjoin_ISigma1.pi1_succ_induction
  · definability
  case nil => simp
  case adjoin x v ih =>
    simp only [listMax_adjoin, max_le_iff]
    constructor
    · simpa using h 0 (by simp)
    · exact ih (fun i hi ↦ by simpa using h (i + 1) (by simp [hi]))

lemma listMaxss_le_iff {v z : V} : listMax v ≤ z ↔ ∀ i < len v, v.[i] ≤ z := by
  constructor
  · intro h i hi; exact le_trans (nth_le_listMax hi) h
  · exact listMaxss_le

/-
lemma nth_le_listMaxs (v : V) (hv : v ≠ 0) : ∃ i < len v, v.[i] = listMax v := by
  induction v using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp at hv
  case adjoin x v ih =>
    simp
-/


-- @@ L723-723 verbatim
end listMax


-- @@ L725-729 verbatim
/-!

### Take Last k-Element

-/


-- @@ L731-731 verbatim
namespace TakeLast


-- @@ L733-737 verbatim
def blueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “y k. y = 0”
  adjoin := .mkSigma “y x xs ih k.
    ∃ l, !lenDef l xs ∧
    (l < k → !adjoinDef y x xs) ∧ (k ≤ l → y = ih)”


-- @@ L739-750 verbatim
noncomputable def adjointruction : VecRec.Construction V blueprint where
  nil _ := 0
  adjoin (param x xs ih) := if len xs < param 0 then x ∷ xs else ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by
    suffices
      (len (v 2) < v 4 → v 0 = v 1 ∷ v 2) ∧ (v 4 ≤ len (v 2) → v 0 = v 3) ↔
      (v 0 = if len (v 2) < v 4 then v 1 ∷ v 2 else v 3) by
      simpa [blueprint, Fin.isValue]
    rcases lt_or_ge (len (v 2)) (v 4) with (hv | hv)
    · simp [hv]
    · simp [hv, not_lt_of_ge hv]


-- @@ L752-752 verbatim
end TakeLast


-- @@ L754-754 verbatim
section takeLast


-- @@ L756-756 verbatim
open TakeLast


-- @@ L758-758 verbatim
noncomputable def takeLast (v k : V) : V := adjointruction.result ![k] v


-- @@ L760-763 verbatim
@[simp] lemma takeLast_nil : takeLast (0 : V) k = 0 := by simp [takeLast, adjointruction]

lemma takeLast_adjoin (x v : V) :
    takeLast (x ∷ v) k = if len v < k then x ∷ v else takeLast v k := by simp [takeLast, adjointruction]


-- @@ L765-765 verbatim
section


-- @@ L767-767 verbatim
def _root_.FFL.FirstOrder.Arithmetic.takeLastDef : 𝚺₁.Semisentence 3 := blueprint.resultDef


-- @@ L769-769 verbatim
instance takeLast_defined : 𝚺₁-Function₂ (takeLast : V → V → V) via takeLastDef := adjointruction.result_defined


-- @@ L771-771 verbatim
instance takeLast_definable : 𝚺₁-Function₂ (takeLast : V → V → V) := takeLast_defined.to_definable


-- @@ L773-773 verbatim
instance takeLast_definable' (Γ m) : Γ-[m + 1]-Function₂ (takeLast : V → V → V) := takeLast_definable.of_sigmaOne


-- @@ L775-788 verbatim
end

lemma len_takeLast {v k : V} (h : k ≤ len v) : len (takeLast v k) = k := by
  induction v using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp_all
  case adjoin x v ih =>
    have : k = len v + 1 ∨ k ≤ len v := by
      rcases eq_or_lt_of_le h with (h | h)
      · left; simpa using h
      · right; simpa [lt_succ_iff_le] using h
    rcases this with (rfl | hkv)
    · simp [takeLast_adjoin]
    · simp [takeLast_adjoin, not_lt_of_ge hkv, ih hkv]


-- @@ L790-791 verbatim
@[simp] lemma takeLast_len_self (v : V) : takeLast v (len v) = v := by
  rcases nil_or_adjoin v with (rfl | ⟨x, v, rfl⟩) <;> simp [takeLast_adjoin]


-- @@ L793-794 verbatim
/-- TODO: move -/
@[simp] lemma add_sub_add (a b c : V) : (a + c) - (b + c) = a - b := add_tsub_add_eq_tsub_right a c b


-- @@ L796-811 verbatim
@[simp] lemma takeLast_zero (v : V) : takeLast v 0 = 0 := by
  induction v using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin x v ih => simp [takeLast_adjoin, ih]

lemma takeLast_succ_of_lt {i v : V} (h : i < len v) : takeLast v (i + 1) = v.[len v - (i + 1)] ∷ takeLast v i := by
  induction v using adjoin_ISigma1.sigma1_succ_induction generalizing i
  · definability
  case nil => simp at h
  case adjoin x v ih =>
    rcases show i = len v ∨ i < len v from eq_or_lt_of_le (by simpa [lt_succ_iff_le] using h) with (rfl | hi)
    · simp [takeLast_adjoin]
    · have : len v - i = len v - (i + 1) + 1 := by
        rw [←Arithmetic.sub_sub, sub_add_self_of_le (pos_iff_one_le.mp (tsub_pos_of_lt hi))]
      simpa [takeLast_adjoin, lt_succ_iff_le, not_le_of_gt hi, this, not_lt_of_gt hi] using ih hi


-- @@ L813-813 verbatim
end takeLast


-- @@ L815-819 verbatim
/-!

### Concatation

-/


-- @@ L821-821 verbatim
namespace Concat


-- @@ L823-825 verbatim
def blueprint : VecRec.Blueprint 1 where
  nil := .mkSigma “y z. !adjoinDef y z 0”
  adjoin := .mkSigma “y x xs ih z. !adjoinDef y x ih”


-- @@ L827-831 verbatim
noncomputable def adjointruction : VecRec.Construction V blueprint where
  nil param := ?[param 0]
  adjoin (_ x _ ih) := x ∷ ih
  nil_defined := .mk fun v ↦ by simp [blueprint]
  adjoin_defined := .mk fun v ↦ by simp [blueprint, Fin.isValue]


-- @@ L833-833 verbatim
end Concat


-- @@ L835-835 verbatim
section concat


-- @@ L837-837 verbatim
open Concat


-- @@ L839-839 verbatim
noncomputable def concat (v z : V) : V := adjointruction.result ![z] v


-- @@ L841-841 verbatim
@[simp] lemma concat_nil (z : V) : concat 0 z = ?[z] := by simp [concat, adjointruction]


-- @@ L843-843 verbatim
@[simp] lemma concat_adjoin (x v z : V) : concat (x ∷ v) z = x ∷ concat v z := by simp [concat, adjointruction]


-- @@ L845-845 verbatim
section


-- @@ L847-847 verbatim
def _root_.FFL.FirstOrder.Arithmetic.concatDef : 𝚺₁.Semisentence 3 := blueprint.resultDef


-- @@ L849-849 verbatim
instance concat_defined : 𝚺₁-Function₂ (concat : V → V → V) via concatDef := adjointruction.result_defined


-- @@ L851-851 verbatim
instance concat_definable : 𝚺₁-Function₂ (concat : V → V → V) := concat_defined.to_definable


-- @@ L853-853 verbatim
instance concat_definable' (Γ m) : Γ-[m + 1]-Function₂ (concat : V → V → V) := concat_definable.of_sigmaOne


-- @@ L855-855 verbatim
end


-- @@ L857-870 verbatim
@[simp] lemma len_concat (v z : V) : len (concat v z) = len v + 1 := by
  induction v using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin x v ih => simp [ih]

lemma concat_nth_lt (v z : V) {i} (hi : i < len v) : (concat v z).[i] = v.[i] := by
  induction v using adjoin_ISigma1.sigma1_succ_induction generalizing i
  · definability
  case nil => simp at hi
  case adjoin x v ih =>
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · simp [ih (by simpa using hi)]


-- @@ L872-879 verbatim
@[simp] lemma concat_nth_len (v z : V) : (concat v z).[len v] = z := by
  induction v using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin x v ih => simp [ih]

lemma concat_nth_len' (v z : V) {i} (hi : len v = i) : (concat v z).[i] = z := by
  rcases hi; simp


-- @@ L881-881 verbatim
end concat


-- @@ L883-887 verbatim
/-!

### Membership

-/


-- @@ L889-889 verbatim
section vec_membership


-- @@ L891-891 verbatim
def MemVec (x v : V) : Prop := ∃ i < len v, x = v.[i]


-- @@ L893-893 verbatim
scoped infix:40 " ∈ᵥ " => MemVec


-- @@ L895-897 verbatim
@[simp] lemma not_memVec_empty (x : V) : ¬x ∈ᵥ 0 := by rintro ⟨i, h, _⟩; simp at h

lemma nth_mem_memVec {i v : V} (h : i < len v) : v.[i] ∈ᵥ v := ⟨i, by simp [h]⟩


-- @@ L899-899 verbatim
@[simp] lemma memVec_insert_fst {x v : V} : x ∈ᵥ x ∷ v := ⟨0, by simp⟩


-- @@ L901-913 verbatim
@[simp] lemma memVec_adjoin_iff {x y v : V} : x ∈ᵥ y ∷ v ↔ x = y ∨ x ∈ᵥ v := by
  constructor
  · rintro ⟨i, h, rfl⟩
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · right; simpa using nth_mem_memVec (by simpa using h)
  · rintro (rfl | hx)
    · simp
    · rcases hx with ⟨i, hi, rfl⟩
      exact ⟨i + 1, by simp [hi]⟩

lemma le_of_memVec {x v : V} (h : x ∈ᵥ v) : x ≤ v := by
  rcases h with ⟨i, _, rfl⟩; simp


-- @@ L915-915 verbatim
section


-- @@ L917-919 verbatim
def _root_.FFL.FirstOrder.Arithmetic.memVecDef : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “x v. ∃ l, !lenDef l v ∧ ∃ i < l, !nthDef x v i”)
  (.mkPi “x v. ∀ l, !lenDef l v → ∃ i < l, ∀ vi, !nthDef vi v i → x = vi”)


-- @@ L921-922 verbatim
instance memVec_defined : 𝚫₁-Relation (MemVec : V → V → Prop) via memVecDef :=
  ⟨by intro v; simp [memVecDef], by intro v; simp [memVecDef, MemVec]⟩


-- @@ L924-924 verbatim
instance memVec_definable : 𝚫₁-Relation (MemVec : V → V → Prop) := memVec_defined.to_definable


-- @@ L926-926 verbatim
instance memVec_definable' (Γ m) : Γ-[m + 1]-Relation (MemVec : V → V → Prop) := memVec_definable.of_deltaOne


-- @@ L928-928 verbatim
end


-- @@ L930-930 verbatim
end vec_membership


-- @@ L932-936 verbatim
/-!

### Subset

-/


-- @@ L938-938 verbatim
section vec_subset


-- @@ L940-940 verbatim
def SubsetVec (v w : V) : Prop := ∀ x, x ∈ᵥ v → x ∈ᵥ w


-- @@ L942-942 verbatim
scoped infix:30 " ⊆ᵥ " => SubsetVec


-- @@ L944-944 verbatim
@[simp, refl] lemma SubsetVec.refl (v : V) : v ⊆ᵥ v := fun _ hx ↦ hx


-- @@ L946-946 verbatim
@[simp] lemma subsetVec_insert_tail (x v : V) : v ⊆ᵥ x ∷ v := by intro y hy; simp [hy]


-- @@ L948-948 verbatim
section


-- @@ L950-952 verbatim
def _root_.FFL.FirstOrder.Arithmetic.subsetVecDef : 𝚫₁.Semisentence 2 := .mkDelta
  (.mkSigma “v w. ∀ x <⁺ v, !memVecDef.pi x v → !memVecDef.sigma x w”)
  (.mkPi “v w. ∀ x <⁺ v, !memVecDef.sigma x v → !memVecDef.pi x w”)


-- @@ L954-961 verbatim
set_option linter.flexible false in
instance subsetVec_defined : 𝚫₁-Relation (SubsetVec : V → V → Prop) via subsetVecDef :=
  ⟨by intro v; simp [subsetVecDef, HierarchySymbol.Semiformula.val_sigma, memVec_defined.proper.iff'],
   by intro v
      simp [subsetVecDef, HierarchySymbol.Semiformula.val_sigma, memVec_defined.proper.iff']
      constructor
      · intro h x hx; exact h x (le_of_memVec hx) hx
      · intro h x _; exact h x⟩


-- @@ L963-963 verbatim
instance subsetVec_definable : 𝚫₁-Relation (SubsetVec : V → V → Prop) := subsetVec_defined.to_definable


-- @@ L965-965 verbatim
instance subsetVec_definable' (Γ m) : Γ-[m + 1]-Relation (SubsetVec : V → V → Prop) := subsetVec_definable.of_deltaOne


-- @@ L967-967 verbatim
end


-- @@ L969-969 verbatim
end vec_subset


-- @@ L971-975 verbatim
/-!

### Repeat

-/


-- @@ L977-977 verbatim
section repaetVec


-- @@ L979-981 verbatim
def repeatVec.blueprint : PR.Blueprint 1 where
  zero := .mkSigma “y x. y = 0”
  succ := .mkSigma “y ih n x. !adjoinDef y x ih”


-- @@ L983-987 verbatim
noncomputable def repeatVec.adjointruction : PR.Construction V repeatVec.blueprint where
  zero := fun _ ↦ 0
  succ := fun x _ ih ↦ x 0 ∷ ih
  zero_defined := .mk fun v ↦ by simp [blueprint]
  succ_defined := .mk fun v ↦ by simp [blueprint]


-- @@ L989-990 verbatim
/-- `repeatVec x k = x ∷ x ∷ x ∷ ... k times ... ∷ 0`-/
noncomputable def repeatVec (x k : V) : V := repeatVec.adjointruction.result ![x] k


-- @@ L992-992 verbatim
@[simp] lemma repeatVec_zero (x : V) : repeatVec x 0 = 0 := by simp [repeatVec, repeatVec.adjointruction]


-- @@ L994-994 verbatim
@[simp] lemma repeatVec_succ (x k : V) : repeatVec x (k + 1) = x ∷ repeatVec x k := by simp [repeatVec, repeatVec.adjointruction]


-- @@ L996-996 verbatim
section


-- @@ L998-998 verbatim
def _root_.FFL.FirstOrder.Arithmetic.repeatVecDef : 𝚺₁.Semisentence 3 := repeatVec.blueprint.resultDef |>.rew (Rew.subst ![#0, #2, #1])


-- @@ L1000-1001 verbatim
instance repeatVec_defined : 𝚺₁-Function₂ (repeatVec : V → V → V) via repeatVecDef := .mk
  fun v ↦ by simp [repeatVec.adjointruction.result_defined_iff, repeatVecDef]; rfl


-- @@ L1003-1003 verbatim
instance repeatVec_definable : 𝚺₁-Function₂ (repeatVec : V → V → V) := repeatVec_defined.to_definable


-- @@ L1005-1005 verbatim
instance repeatVec_definable' (Γ) : Γ-[m + 1]-Function₂ (repeatVec : V → V → V) := repeatVec_definable.of_sigmaOne


-- @@ L1007-1007 verbatim
end


-- @@ L1009-1013 verbatim
@[simp] lemma len_repeatVec (x k : V) : len (repeatVec x k) = k := by
  induction k using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ k ih => simp [ih]


-- @@ L1015-1028 verbatim
@[simp] lemma le_repaetVec (x k : V) : k ≤ repeatVec x k := by
  simpa using len_le (repeatVec x k)

lemma nth_repeatVec (x k : V) {i} (h : i < k) : (repeatVec x k).[i] = x := by
  induction k using ISigma1.sigma1_succ_induction generalizing i
  · definability
  case zero => simp at h
  case succ k ih =>
    rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
    · simp
    · simpa using ih (by simpa using h)

lemma len_repeatVec_of_nth_le {v m : V} (H : ∀ i < len v, v.[i] ≤ m) : v ≤ repeatVec m (len v) :=
  le_of_nth_le_nth (by simp) (fun i hi ↦ by simp [nth_repeatVec m (len v) hi, H i hi])


-- @@ L1030-1030 verbatim
end repaetVec


-- @@ L1032-1036 verbatim
/-!

### Convert to Set

-/


-- @@ L1038-1038 verbatim
namespace VecToSet


-- @@ L1040-1042 verbatim
def blueprint : VecRec.Blueprint 0 where
  nil := .mkSigma “y. y = 0”
  adjoin := .mkSigma “y x xs ih. !insertDef y x ih”


-- @@ L1044-1048 verbatim
noncomputable def adjointruction : VecRec.Construction V blueprint where
  nil _ := ∅
  adjoin (_ x _ ih) := insert x ih
  nil_defined := .mk fun v ↦ by simp [blueprint, emptyset_def]
  adjoin_defined := .mk fun v ↦ by simp [blueprint]


-- @@ L1050-1050 verbatim
end VecToSet


-- @@ L1052-1052 verbatim
section vecToSet


-- @@ L1054-1054 verbatim
open VecToSet


-- @@ L1056-1056 verbatim
noncomputable def vecToSet (v : V) : V := adjointruction.result ![] v


-- @@ L1058-1058 verbatim
@[simp] lemma vecToSet_nil : vecToSet (0 : V) = ∅ := by simp [vecToSet, adjointruction]


-- @@ L1060-1061 verbatim
@[simp] lemma vecToSet_adjoin (x v : V) :
    vecToSet (x ∷ v) = insert x (vecToSet v) := by simp [vecToSet, adjointruction]


-- @@ L1063-1063 verbatim
section


-- @@ L1065-1065 verbatim
def _root_.FFL.FirstOrder.Arithmetic.vecToSetDef : 𝚺₁.Semisentence 2 := blueprint.resultDef


-- @@ L1067-1067 verbatim
instance vecToSet_defined : 𝚺₁-Function₁ (vecToSet : V → V) via vecToSetDef := adjointruction.result_defined


-- @@ L1069-1069 verbatim
instance vecToSet_definable : 𝚺₁-Function₁ (vecToSet : V → V) := vecToSet_defined.to_definable


-- @@ L1071-1071 verbatim
instance vecToSet_definable' (Γ) : Γ-[m + 1]-Function₁ (vecToSet : V → V) := vecToSet_definable.of_sigmaOne


-- @@ L1073-1088 verbatim
end

lemma mem_vecToSet_iff {v x : V} : x ∈ vecToSet v ↔ ∃ i < len v, x = v.[i] := by
  induction v using adjoin_ISigma1.sigma1_succ_induction
  · definability
  case nil => simp
  case adjoin y v ih =>
    simp only [vecToSet_adjoin, mem_bitInsert_iff, ih, len_adjoin]
    constructor
    · rintro (rfl | ⟨i, hi, rfl⟩)
      · exact ⟨0, by simp⟩
      · exact ⟨i + 1, by simp [hi]⟩
    · rintro ⟨i, hi, rfl⟩
      rcases zero_or_succ i with (rfl | ⟨i, rfl⟩)
      · simp
      · right; exact ⟨i, by simpa using hi, by simp⟩


-- @@ L1090-1091 verbatim
@[simp] lemma nth_mem_vecToSet {v i : V} (h : i < len v) : v.[i] ∈ vecToSet v :=
  mem_vecToSet_iff.mpr ⟨i, h, rfl⟩


-- @@ L1093-1093 verbatim
end vecToSet


-- @@ L1095-1095 verbatim
end FFL.FirstOrder.Arithmetic
