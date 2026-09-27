/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import LeanPool.QuasiBorelSpaces.MeasureTheory.Instances
import LeanPool.QuasiBorelSpaces.MeasureTheory.Cases



-- @@ L13-17 verbatim
/-!
# Quasi-Borel Spaces

This file defines the concept of a quasi-borel space, as given by [HeunenKSY17].
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open scoped MeasureTheory


-- @@ L23-49 verbatim
/--
A quasi‑borel space consists of a type `A` together with a set of "random
variables" in `ℝ → A` satisfying closure under constants, measurable
precomposition, and gluing along borel partitions.

See [HeunenKSY17], Definition 7.
-/
@[ext]
class QuasiBorelSpace (A : Type*) where
  /--
  `IsVar φ` denotes whether `φ` is a random variable. Variables can be
  approximately thought of as the measurable functions in `ℝ → A`.
  Avoid using this predicate directly. Prefer `IsHom` instead.
  -/
  IsVar : (ℝ → A) → Prop
  /-- Variables are closed under constant functions. -/
  isVar_const (x : A) : IsVar (fun _ : ℝ ↦ x)
  /-- Variables are closed under precomposition with measurable functions. -/
  isVar_comp {f : ℝ → ℝ} {φ : ℝ → A}
    : Measurable f
    → IsVar φ
    → IsVar (fun r ↦ φ (f r))
  /-- Variables are closed under gluing of countable families. -/
  isVar_cases' {ix : ℝ → ℕ} {φ : ℕ → ℝ → A}
    : Measurable ix
    → (∀n, IsVar (φ n))
    → IsVar (fun r ↦ φ (ix r) r)


-- @@ L51-51 verbatim
variable {A B : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B]


-- @@ L53-53 verbatim
namespace QuasiBorelSpace


-- @@ L55-55 verbatim
attribute [fun_prop] IsVar isVar_const isVar_comp


-- @@ L57-66 verbatim
/--
A function `f : A → B` between `QuasiBorelSpace`s is a _morphism_ if it
preserves variables under pre-composition.

See [HeunenKSY17], Definition 11.
-/
@[fun_prop]
inductive IsHom (f : A → B) : Prop where
  /-- Do not use this directly. -/
  | intro : (∀⦃φ⦄, IsVar φ → IsVar (fun x ↦ f (φ x))) → IsHom f


-- @@ L68-69 verbatim
@[inherit_doc IsHom]
scoped notation "IsHom[" inst₁ ", " inst₂ "]" => @IsHom _ _ inst₁ inst₂


-- @@ L71-76 verbatim
/-- Every `MeasurableSpace` induces a `QuasiBorelSpace`. -/
@[reducible] def ofMeasurableSpace [MeasurableSpace A] : QuasiBorelSpace A where
  IsVar φ := Measurable φ
  isVar_const x := measurable_const
  isVar_comp := by fun_prop
  isVar_cases' := by apply MeasureTheory.measurable_cases


-- @@ L78-78 verbatim
namespace Real

-- @@ L79-79 verbatim
instance : QuasiBorelSpace ℝ := ofMeasurableSpace

-- @@ L80-80 verbatim
end Real


-- @@ L82-82 verbatim
namespace ENNReal

-- @@ L83-83 verbatim
instance : QuasiBorelSpace ENNReal := ofMeasurableSpace

-- @@ L84-84 verbatim
end ENNReal


-- @@ L86-86 verbatim
namespace «Prop»

-- @@ L87-87 verbatim
instance : QuasiBorelSpace Prop := ofMeasurableSpace

-- @@ L88-88 verbatim
end «Prop»


-- @@ L90-90 verbatim
namespace Bool

-- @@ L91-91 verbatim
instance : QuasiBorelSpace Bool := ofMeasurableSpace

-- @@ L92-92 verbatim
end Bool


-- @@ L94-94 verbatim
namespace Empty

-- @@ L95-95 verbatim
instance : QuasiBorelSpace Empty := ofMeasurableSpace

-- @@ L96-96 verbatim
end Empty


-- @@ L98-98 verbatim
namespace PEmpty

-- @@ L99-99 verbatim
instance : QuasiBorelSpace PEmpty := ofMeasurableSpace

-- @@ L100-100 verbatim
end PEmpty


-- @@ L102-102 verbatim
namespace Unit

-- @@ L103-103 verbatim
instance : QuasiBorelSpace Unit := ofMeasurableSpace

-- @@ L104-104 verbatim
end Unit


-- @@ L106-106 verbatim
namespace PUnit

-- @@ L107-107 verbatim
instance : QuasiBorelSpace PUnit := ofMeasurableSpace

-- @@ L108-108 verbatim
end PUnit


-- @@ L110-110 verbatim
namespace Nat

-- @@ L111-111 verbatim
instance : QuasiBorelSpace Nat := ofMeasurableSpace

-- @@ L112-112 verbatim
end Nat


-- @@ L114-126 verbatim
/--
Every `QuasiBorelSpace` induces a `MeasurableSpace`.

See [HeunenKSY17], Proposition 14.
-/
@[reducible] def toMeasurableSpace : MeasurableSpace A where
  MeasurableSet' X := ∀{φ : ℝ → A}, IsHom φ → MeasurableSet (φ ⁻¹' X)
  measurableSet_empty hφ := by
    simp only [Set.preimage_empty, MeasurableSet.empty]
  measurableSet_compl X hX φ hφ := by
    simpa only [Set.preimage_compl, MeasurableSet.compl_iff] using hX hφ
  measurableSet_iUnion f hf φ hφ := by
    simpa only [Set.preimage_iUnion] using MeasurableSet.iUnion fun n ↦ hf n hφ


-- @@ L128-133 verbatim
/-- We can lift a `QuasiBorelSpace` from one type to another. -/
@[reducible] def lift (f : B → A) : QuasiBorelSpace B where
  IsVar φ := IsVar fun x ↦ f (φ x)
  isVar_const x := isVar_const (f x)
  isVar_comp := isVar_comp
  isVar_cases' := isVar_cases'


-- @@ L135-136 verbatim
instance : Inhabited (QuasiBorelSpace A) where
  default := @ofMeasurableSpace _ ⊤


-- @@ L138-138 verbatim
end QuasiBorelSpace


-- @@ L140-146 verbatim
/--
A _measurable quasi-borel space_ is the quasi-borel space where the notion of
variable aligns with measurable functions.
-/
class MeasurableQuasiBorelSpace (A : Type*) [QuasiBorelSpace A] [MeasurableSpace A] where
  /-- Variables are measurable functions. -/
  isHom_iff_measurable (φ : ℝ → A) : QuasiBorelSpace.IsHom φ ↔ Measurable φ


-- @@ L148-153 verbatim
/--
A _discrete quasi-borel space_ is the quasi-borel space analogue of the discrete
measurable space.
-/
class DiscreteQuasiBorelSpace (A : Type*) [QuasiBorelSpace A] [MeasurableSpace A] : Prop
  extends DiscreteMeasurableSpace A, MeasurableQuasiBorelSpace A


-- @@ L155-157 verbatim
instance {A : Type*} [QuasiBorelSpace A] [MeasurableSpace A]
    [DiscreteMeasurableSpace A] [MeasurableQuasiBorelSpace A]
    : DiscreteQuasiBorelSpace A := ⟨⟩
