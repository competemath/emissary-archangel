/-
Copyright (c) 2026 Andrej Bauer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrej Bauer
-/
module

public import LeanPool.PartialCombinatoryAlgebras.PartialCombinatoryAlgebra
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.SetLike


-- @@ L13-18 verbatim
/-!
# Total combinatory algebras

A total combinatory structure on a type `A`, and the fact that any total
combinatory algebra induces a partial combinatory algebra on the same type.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace LeanPool.PartialCombinatoryAlgebras


-- @@ L24-33 expanded
/-- A (total) combinatory structure on a set `A`. -/
class CA (A : Type*) extends HasDot A where
  /-- The `K` combinator. -/
  K : A
  /-- The `S` combinator. -/
  S : A
  /-- The defining equation of `K`. -/
  eq_K : ∀ {a b : A}, HasDot.dot (HasDot.dot K a) b = a
  /-- The defining equation of `S`. -/
  eq_S :
    ∀ {a b c : A},
      HasDot.dot (HasDot.dot (HasDot.dot S a) b) c = HasDot.dot (HasDot.dot a c) (HasDot.dot b c)


-- @@ L35-35 verbatim
namespace Part


-- @@ L37-40 verbatim
/-- Missing from `Part`. -/
@[simps]
def map₂ {α β γ : Type*} (f : α → β → γ) (u : _root_.Part α) (v : _root_.Part β) : _root_.Part γ :=
  ⟨u.Dom ∧ v.Dom, fun p => f (u.get (And.left p)) (v.get (And.right p))⟩


-- @@ L42-46 verbatim
@[simp]
lemma eq_map₂_some {α β γ : Type*} (f : α → β → γ) (a : α) (b : β) :
    map₂ f (.some a) (.some b) = .some (f a b) := by
  rw [_root_.Part.eq_some_iff]
  exact ⟨⟨trivial, trivial⟩, rfl⟩


-- @@ L48-48 verbatim
end Part


-- @@ L50-50 verbatim
namespace CA


-- @@ L52-55 verbatim
/-- A total application induces a partial application -/
@[reducible]
instance partialApp {A : Type} [d : HasDot A] : PartialApplication A where
  app := Part.map₂ d.dot


-- @@ L57-61 expanded
lemma eq_app {A : Type} [HasDot A] {u v : Part A} (hu : Part.Dom u) (hv : Part.Dom v) :
    HasDot.dot u v = .some (HasDot.dot (u.get hu) (v.get hv)) :=
  by
  nth_rewrite 1 [← Part.some_get hu]
  nth_rewrite 1 [← Part.some_get hv]
  apply Part.eq_map₂_some


-- @@ L63-95 expanded
/-- A combinatory algebra is a PCA. -/
instance isPCA {A : Type} [CA A] : PCA A
    where
  K := .some K
  S := .some S
  df_K₀ := by trivial
  df_K₁ := by intros; trivial
  eq_K := by
    intro u v hu hv
    rw [CA.eq_app trivial hu, CA.eq_app trivial hv]
    change Part.some (HasDot.dot (HasDot.dot K (u.get hu)) (v.get hv)) = u
    rw [CA.eq_K]
    exact Part.some_get hu
  df_S₀ := by trivial
  df_S₁ := by intros; trivial
  df_S₂ := by intros; trivial
  eq_S := by
    intro u v w hu hv hw
    have huw : Part.Dom (HasDot.dot u w) := by rw [CA.eq_app hu hw]; trivial
    have hvw : Part.Dom (HasDot.dot v w) := by rw [CA.eq_app hv hw]; trivial
    have lhs :
      HasDot.dot (HasDot.dot (HasDot.dot (Part.some (S : A)) u) v) w =
        Part.some (HasDot.dot (HasDot.dot (HasDot.dot S (u.get hu)) (v.get hv)) (w.get hw)) :=
      by
      rw [CA.eq_app trivial hu, CA.eq_app trivial hv, CA.eq_app trivial hw]
      change
        Part.some (HasDot.dot (HasDot.dot (HasDot.dot S (u.get hu)) (v.get hv)) (w.get hw)) =
          Part.some (HasDot.dot (HasDot.dot (HasDot.dot S (u.get hu)) (v.get hv)) (w.get hw))
      rfl
    have heq1 : (HasDot.dot u w).get huw = HasDot.dot (u.get hu) (w.get hw) :=
      Part.get_eq_iff_eq_some.mpr (CA.eq_app hu hw)
    have heq2 : (HasDot.dot v w).get hvw = HasDot.dot (v.get hv) (w.get hw) :=
      Part.get_eq_iff_eq_some.mpr (CA.eq_app hv hw)
    have rhs :
      HasDot.dot (HasDot.dot u w) (HasDot.dot v w) =
        Part.some
          (HasDot.dot (HasDot.dot (u.get hu) (w.get hw)) (HasDot.dot (v.get hv) (w.get hw))) :=
      by rw [CA.eq_app huw hvw, heq1, heq2]
    rw [lhs, CA.eq_S, ← rhs]


-- @@ L97-97 verbatim
end CA


-- @@ L99-99 verbatim
end LeanPool.PartialCombinatoryAlgebras
