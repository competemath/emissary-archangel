/-
Copyright (c) 2026 Juan Jose Fernandez Morales. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Jose Fernandez Morales
-/
module

public import PhyslibAlpha.ClassicalFieldTheory.Local.JetPoint

-- @@ L9-38 verbatim
/-!
# Fiber directions on jet points

## i. Overview

This module adds the affine fiber-direction structure on coordinate-level jet points.

At this stage, it introduces:

- fiber-coordinate data on jet points,
- affine translation and line maps in the jet fiber,
- and the jet-fiber direction determined by a field.

## ii. Key results

- `ClassicalFieldTheory.Local.JetFiberData`
- `ClassicalFieldTheory.Local.JetPoint.addFiber`
- `ClassicalFieldTheory.Local.JetPoint.lineMap`
- `ClassicalFieldTheory.Local.jetDirectionAt`

## iii. Table of contents

- A. Fiber-coordinate data
- B. Affine fiber structure on jet points
- C. Fiber directions determined by fields

## iv. References

* None.
-/


-- @@ L40-40 verbatim
@[expose] public section


-- @@ L42-42 verbatim
open Physlib

-- @@ L43-43 verbatim
open scoped ContDiff


-- @@ L45-45 verbatim
namespace ClassicalFieldTheory

-- @@ L46-46 verbatim
namespace Local


-- @@ L48-51 verbatim
/-!
## A. Fiber-coordinate data

-/


-- @@ L53-57 verbatim
/-- Fiber-coordinate data for jet points of order `k`. This records only the coordinates `u^a_I`,
not the base point in `Space d`. -/
structure JetFiberData (d m k : ℕ) where
  /-- The fiber coordinates indexed by all derivative indices of order at most `k`. -/
  coord : JetCoordinates d m k


-- @@ L59-59 verbatim
namespace JetFiberData


-- @@ L61-61 verbatim
variable {d m k : ℕ}


-- @@ L63-64 verbatim
instance : CoeFun (JetFiberData d m k) (fun _ => DerivativeIndex d k → Fin m → ℝ) where
  coe V := V.coord


-- @@ L66-77 verbatim
@[ext]
lemma ext (V W : JetFiberData d m k) (hcoord : ∀ I a, V.coord I a = W.coord I a) : V = W := by
  cases V with
  | mk coordV =>
  cases W with
  | mk coordW =>
  have h : coordV = coordW := by
    funext I
    funext a
    exact hcoord I a
  cases h
  rfl


-- @@ L79-81 verbatim
/-- The zero-th order component of a jet-fiber direction, corresponding to the field value. -/
def value (V : JetFiberData d m k) : EuclideanSpace ℝ (Fin m) :=
  WithLp.toLp 2 fun a => V.coord 0 a


-- @@ L83-86 verbatim
@[simp]
lemma value_apply (V : JetFiberData d m k) (a : Fin m) :
    V.value a = V.coord 0 a := by
  simp [value]


-- @@ L88-89 verbatim
instance : Zero (JetFiberData d m k) where
  zero := { coord := fun _ _ => 0 }


-- @@ L91-92 verbatim
instance : Add (JetFiberData d m k) where
  add V W := { coord := fun I a => V.coord I a + W.coord I a }


-- @@ L94-95 verbatim
instance : SMul ℝ (JetFiberData d m k) where
  smul c V := { coord := fun I a => c * V.coord I a }


-- @@ L97-99 verbatim
@[simp]
lemma zero_coord (I : DerivativeIndex d k) (a : Fin m) :
    (0 : JetFiberData d m k).coord I a = 0 := rfl


-- @@ L101-103 verbatim
@[simp]
lemma add_coord (V W : JetFiberData d m k) (I : DerivativeIndex d k) (a : Fin m) :
    (V + W).coord I a = V.coord I a + W.coord I a := rfl


-- @@ L105-107 verbatim
@[simp]
lemma smul_coord (c : ℝ) (V : JetFiberData d m k) (I : DerivativeIndex d k) (a : Fin m) :
    (c • V).coord I a = c * V.coord I a := rfl


-- @@ L109-109 verbatim
end JetFiberData


-- @@ L111-114 verbatim
/-!
## B. Affine fiber structure on jet points

-/


-- @@ L116-116 verbatim
namespace JetPoint


-- @@ L118-118 verbatim
variable {d m k : ℕ}


-- @@ L120-123 verbatim
/-- Translate a jet point by a fiber-direction increment. -/
def addFiber (J : JetPoint d m k) (V : JetFiberData d m k) : JetPoint d m k where
  base := J.base
  fiber := fun I a => J.fiber I a + V.coord I a


-- @@ L125-127 verbatim
/-- The affine line in jet space through `J` in the fiber direction `V`. -/
def lineMap (J : JetPoint d m k) (V : JetFiberData d m k) (s : ℝ) : JetPoint d m k :=
  J.addFiber (s • V)


-- @@ L129-131 verbatim
@[simp]
lemma addFiber_base (J : JetPoint d m k) (V : JetFiberData d m k) :
    (J.addFiber V).base = J.base := rfl


-- @@ L133-137 verbatim
@[simp]
lemma addFiber_value (J : JetPoint d m k) (V : JetFiberData d m k) :
    (J.addFiber V).value = J.value + V.value := by
  ext a
  rfl


-- @@ L139-142 verbatim
@[simp]
lemma addFiber_coord (J : JetPoint d m k) (V : JetFiberData d m k)
    (I : DerivativeIndex d k) (a : Fin m) :
    (J.addFiber V).coord I a = J.coord I a + V.coord I a := rfl


-- @@ L144-146 verbatim
@[simp]
lemma lineMap_base (J : JetPoint d m k) (V : JetFiberData d m k) (s : ℝ) :
    (J.lineMap V s).base = J.base := rfl


-- @@ L148-151 verbatim
@[simp]
lemma lineMap_coord (J : JetPoint d m k) (V : JetFiberData d m k) (s : ℝ)
    (I : DerivativeIndex d k) (a : Fin m) :
    (J.lineMap V s).coord I a = J.coord I a + s * V.coord I a := rfl


-- @@ L153-153 verbatim
end JetPoint


-- @@ L155-158 verbatim
/-!
## C. Fiber directions determined by fields

-/


-- @@ L160-164 verbatim
/-- The jet-fiber direction determined by a field `g` at a point `x`. -/
noncomputable def jetDirectionAt (k : ℕ) (g : Space d → EuclideanSpace ℝ (Fin m))
    (x : Space d) :
    JetFiberData d m k where
  coord := jetCoordinatesAt k g x


-- @@ L166-169 expanded
@[simp]
lemma jetDirectionAt_coord (k : ℕ) (g : Space d → EuclideanSpace ℝ (Fin m)) (x : Space d)
    (I : DerivativeIndex d k) (a : Fin m) :
    (jetDirectionAt k g x).coord I a = (iteratedDeriv I.1) (fun y => (g y) a) x :=
  rfl


-- @@ L171-174 verbatim
lemma jetDirectionAt_coord_zero (k : ℕ) (g : Space d → EuclideanSpace ℝ (Fin m))
    (x : Space d) (a : Fin m) :
    (jetDirectionAt k g x).coord 0 a = (g x) a := by
  simp [jetDirectionAt_coord]


-- @@ L176-203 expanded
lemma jetCoordinatesAt_add_smul (k : ℕ) (f g : Space d → EuclideanSpace ℝ (Fin m)) (x : Space d)
    (s : ℝ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    jetCoordinatesAt k (fun y => f y + s • g y) x =
      jetCoordinatesAt k f x + s • jetCoordinatesAt k g x :=
  by
  funext I
  funext a
  have hfa : ContDiff ℝ ∞ (fun y => (f y) a) := by
    exact
      (contDiff_piLp_apply (𝕜 := ℝ) (n := ∞) (p := 2) (E := fun _ : Fin m => ℝ) (i := a)).comp hf
  have hga : ContDiff ℝ ∞ (fun y => (g y) a) := by
    exact
      (contDiff_piLp_apply (𝕜 := ℝ) (n := ∞) (p := 2) (E := fun _ : Fin m => ℝ) (i := a)).comp hg
  have hadd : (fun y => (f y + s • g y) a) = (fun y => (f y) a) + s • fun y => (g y) a :=
    by
    funext y
    simp [smul_eq_mul]
  have hsg : ContDiff ℝ ∞ (s • fun y => (g y) a) := by exact hga.const_smul s
  simp [jetCoordinatesAt]
  have hsum := congrFun (Space.iteratedDeriv_add I.1 hfa hsg) x
  have hsmul := congrFun (Space.iteratedDeriv_const_smul I.1 s hga) x
  calc
    (iteratedDeriv I.1) ((fun y => (f y) a) + s • fun y => (g y) a) x =
        ((iteratedDeriv I.1) (fun y => (f y) a) + (iteratedDeriv I.1) (s • fun y => (g y) a)) x :=
      by simpa using hsum
    _ = (iteratedDeriv I.1) (fun y => (f y) a) x + s * (iteratedDeriv I.1) (fun y => (g y) a) x :=
      by simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsmul]


-- @@ L205-234 expanded
lemma jetAt_add_smul (k : ℕ) (f g : Space d → EuclideanSpace ℝ (Fin m)) (x : Space d) (s : ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    jetAt k (fun y => f y + s • g y) x = (jetAt k f x).lineMap (jetDirectionAt k g x) s :=
  by
  apply JetPoint.ext
  · simp [JetPoint.lineMap]
  · intro I a
    have hfa : ContDiff ℝ ∞ (fun y => (f y) a) := by
      exact
        (contDiff_piLp_apply (𝕜 := ℝ) (n := ∞) (p := 2) (E := fun _ : Fin m => ℝ) (i := a)).comp hf
    have hga : ContDiff ℝ ∞ (fun y => (g y) a) := by
      exact
        (contDiff_piLp_apply (𝕜 := ℝ) (n := ∞) (p := 2) (E := fun _ : Fin m => ℝ) (i := a)).comp hg
    have hadd : (fun y => (f y + s • g y) a) = (fun y => (f y) a) + s • fun y => (g y) a :=
      by
      funext y
      simp [smul_eq_mul]
    change
      (iteratedDeriv I.1) (fun y => (f y + s • g y) a) x =
        ((jetAt k f x).lineMap (jetDirectionAt k g x) s).coord I a
    rw [JetPoint.lineMap_coord, jetAt_coord, jetDirectionAt_coord]
    rw [hadd]
    have hsg : ContDiff ℝ ∞ (s • fun y => (g y) a) := by exact hga.const_smul s
    have hsum := congrFun (Space.iteratedDeriv_add I.1 hfa hsg) x
    have hsmul := congrFun (Space.iteratedDeriv_const_smul I.1 s hga) x
    calc
      (iteratedDeriv I.1) ((fun y => (f y) a) + s • fun y => (g y) a) x =
          ((iteratedDeriv I.1) (fun y => (f y) a) + (iteratedDeriv I.1) (s • fun y => (g y) a)) x :=
        hsum
      _ = (iteratedDeriv I.1) (fun y => (f y) a) x + s * (iteratedDeriv I.1) (fun y => (g y) a) x :=
        by simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsmul]


-- @@ L236-236 verbatim
end Local

-- @@ L237-237 verbatim
end ClassicalFieldTheory
