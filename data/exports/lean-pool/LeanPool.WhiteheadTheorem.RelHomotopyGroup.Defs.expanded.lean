/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/
module

public import LeanPool.WhiteheadTheorem.Shapes.Cube
public import LeanPool.WhiteheadTheorem.RelHomotopyGroup.Algebra   -- IsPointedMap
import Mathlib.Tactic.Measurability.Init


-- @@ L12-16 verbatim
/-!
# LeanPool.WhiteheadTheorem.RelHomotopyGroup.Defs

Imported Lean Pool material for `LeanPool.WhiteheadTheorem.RelHomotopyGroup.Defs`.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open scoped unitInterval Topology Topology.Homotopy



-- @@ L23-26 expanded
/-- relative generalized loops -/
def RelGenLoop (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) (a : A) : Set C(I^Fin n, X) :=
  {f | (∀ y ∈ Cube.boundary (Fin n), f y ∈ A) ∧ ∀ y ∈ Cube.boundaryJar n, f y = a}


-- @@ L29-29 verbatim
namespace RelGenLoop


-- @@ L31-31 verbatim
variable {n : ℕ} {X : Type*} [TopologicalSpace X] {A : Set X} {a : A}


-- @@ L33-35 verbatim
/-- The constant `RelGenLoop` at `a`. -/
def const : RelGenLoop n X A a :=
  ⟨ContinuousMap.const (I^ Fin n) a, ⟨by simp, by simp⟩⟩


-- @@ L37-38 verbatim
instance inhabited : Inhabited (RelGenLoop n X A a) :=
  ⟨const⟩


-- @@ L40-43 verbatim
/-- A homotopy between two relative generalized loops.
The intermediate maps of the homotopy always send `∂I^n` into `A ⊆ X` and `⊔I^n` to `a ∈ A`. -/
abbrev Homotopic (f g : RelGenLoop n X A a) : Prop :=
  ContinuousMap.HomotopicWith f g fun f ↦ f ∈ RelGenLoop n X A a


-- @@ L45-56 expanded
/-- For a continuous function `f` to be a `RelGenLoop`,
it suffices to show that `f` send the top face into `A ⊆ X` and `⊔I^n` to `a ∈ A`.
Note: this lemma does not work in dimension 0. -/
lemma mem_of_boundaryLid_and_boundaryJar (f : C(I^Fin n, X))
    (hlid : ∀ y ∈ Cube.boundaryLid n, f y ∈ A) (hjar : ∀ y ∈ Cube.boundaryJar n, f y = a) :
    f ∈ RelGenLoop n X A a := by
  constructor
  · intro y hy
    obtain hy | hy := Cube.mem_boundaryLid_or_mem_boundaryJar_of_mem_boundary y hy
    · exact hlid y hy
    · exact Set.mem_of_eq_of_mem (hjar y hy) (Subtype.coe_prop a)
  · intro y hy; exact hjar y hy


-- @@ L58-58 verbatim
namespace Homotopic


-- @@ L60-61 verbatim
lemma refl {f : RelGenLoop n X A a} : Homotopic f f :=
  ContinuousMap.HomotopicWith.refl f.val f.property


-- @@ L63-64 verbatim
lemma symm {f g : RelGenLoop n X A a} (H : Homotopic f g) : Homotopic g f :=
  ContinuousMap.HomotopicWith.symm H


-- @@ L66-68 verbatim
lemma trans {f g h : RelGenLoop n X A a}
    (H : Homotopic f g) (G : Homotopic g h) : Homotopic f h :=
  ContinuousMap.HomotopicWith.trans H G


-- @@ L70-72 verbatim
/-- `RelGenLoop.Homotopic` is an equivalence relationship. -/
theorem equiv : Equivalence (@Homotopic n X _ A a) :=
  ⟨@refl n X _ A a, @symm n X _ A a, @trans n X _ A a⟩


-- @@ L74-76 verbatim
instance setoid (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) (a : A) :
    Setoid (RelGenLoop n X A a) :=
  ⟨@Homotopic n X _ A a, @equiv n X _ A a⟩


-- @@ L78-78 verbatim
end Homotopic


-- @@ L80-88 expanded
/-- The 0-dimensional relative generalized loops based at `a` are in bijection with
the 0-dimensional generalized loops based at `a`. -/
def equivGenLoop (X : Type*) [TopologicalSpace X] (A : Set X) (a : A) :
    RelGenLoop 0 X A a ≃ Ω^ (Fin 0) X a
    where
  toFun f := ⟨f, fun y hy ↦ isEmptyElim (⟨y, hy⟩ : Cube.boundary (Fin 0))⟩
  invFun
    f :=
    ⟨f,
      ⟨fun y hy ↦ isEmptyElim (⟨y, hy⟩ : Cube.boundary (Fin 0)), fun y hy ↦
        isEmptyElim (⟨y, hy⟩ : Cube.boundaryJar 0)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl


-- @@ L90-90 verbatim
end RelGenLoop



-- @@ L93-98 verbatim
/-- We have defined relative homotopy "groups" as mere sets.
The group structure is not needed for the Whitehead theorem. -/
def RelHomotopyGroup (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) (a : A) :=
  Quotient (RelGenLoop.Homotopic.setoid n X A a)

-- scoped[Topology] notation "π_" => RelHomotopyGroup

-- @@ L99-100 verbatim
/-- `«termπ_rel»` -/
scoped[Topology] notation "π_rel" => RelHomotopyGroup   -- U+FE4D Dashed Low Line


-- @@ L102-104 verbatim
instance RelHomotopyGroup.inhabited {n : ℕ} {X : Type*} [TopologicalSpace X] {A : Set X} {a : A} :
    Inhabited (RelHomotopyGroup n X A a) :=
  inferInstanceAs <| Inhabited <| Quotient (RelGenLoop.Homotopic.setoid n X A a)



-- @@ L107-107 verbatim
namespace RelHomotopyGroup


-- @@ L109-109 verbatim
variable (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) (a : A)


-- @@ L111-121 expanded
/-- The 0-th relative homotopy "group" `π₀(X, A, a)` is in bijection with
the 0-th homotopy "group" `π₀(X, a)`. -/
def equivPi0 : RelHomotopyGroup 0 X A a ≃ π_ 0 X a :=
  Quotient.congr (RelGenLoop.equivGenLoop X A a) fun _ _ ↦
    ⟨fun H ↦
      Nonempty.intro
        { toHomotopy := H.some.toHomotopy
          prop' _ y hy := isEmptyElim (⟨y, hy⟩ : Cube.boundary (Fin 0)) },
      fun H ↦
      Nonempty.intro
        { toHomotopy := H.some.toHomotopy
          prop'
            _ :=
            ⟨fun y hy ↦ isEmptyElim (⟨y, hy⟩ : Cube.boundary (Fin 0)), fun y hy ↦
              isEmptyElim (⟨y, hy⟩ : Cube.boundaryJar 0)⟩ }⟩


-- @@ L123-126 verbatim
/-- `iStar'` -/
def iStar' (f : Ω^ (Fin n) A a) : π_ n X a :=
  Quotient.mk _ ⟨ ⟨Subtype.val ∘ f.val, f.val.continuous_toFun.subtype_val⟩,
    by intro y hy; simp only [ContinuousMap.coe_mk, Function.comp_apply, f.property y hy] ⟩


-- @@ L128-140 verbatim
/-- The inclusion map $i_*$ (of pointed sets) from πₙ(A, a) to πₙ(X, a) -/
def iStar : π_ n A a → π_ n X a :=
  Quotient.lift (iStar' n X A a) fun f g H ↦   -- if `f ≈ g` by `H`
    Quotient.sound <| Nonempty.intro   -- then `inc f ≈ inc g` by this homotopy:
      { toHomotopy := (ContinuousMap.Homotopy.refl
          ⟨Subtype.val, continuous_subtype_val⟩).comp H.some.toHomotopy
        prop' t y hy := by
          have := H.some.prop' t y hy
          simp only [GenLoop.coe_coe, ContinuousMap.toFun_eq_coe,
            ContinuousMap.Homotopy.coe_toContinuousMap,
            ContinuousMap.HomotopyWith.coe_toHomotopy, ContinuousMap.coe_mk] at this
          change ((Nonempty.some H) (t, y) : X) = _
          simp_all }


-- @@ L142-146 expanded
/-- `jStar'` -/
def jStar' (f : Ω^ (Fin n) X a) : RelHomotopyGroup n X A a :=
  Quotient.mk _
    ⟨f,
      ⟨fun y hy ↦ Set.mem_of_eq_of_mem (f.property y hy) (Subtype.coe_prop a), fun y hy ↦
        f.property y <| (Cube.boundaryJar_subset_boundary n) hy⟩⟩


-- @@ L148-168 expanded
/-- The inclusion map $j_*$ (of pointed sets) from πₙ(A, a) to πₙ(X, A, a) -/
def jStar : π_ n X a → RelHomotopyGroup n X A a :=
  Quotient.lift (jStar' n X A a) fun f g H ↦
    Quotient.sound <|
      Nonempty.intro
        { toHomotopy := H.some.toHomotopy
          prop'
            t :=
            ⟨fun y hy ↦ by
              have := H.some.prop' t y hy
              simp only [GenLoop.coe_coe, ContinuousMap.toFun_eq_coe,
                ContinuousMap.Homotopy.coe_toContinuousMap,
                ContinuousMap.HomotopyWith.coe_toHomotopy, ContinuousMap.coe_mk] at this ⊢
              rw [this]
              exact Set.mem_of_eq_of_mem (f.property y hy) (Subtype.coe_prop a), fun y hy ↦
              by
              have hy' := (Cube.boundaryJar_subset_boundary n) hy
              have := H.some.prop' t y hy'
              simp only [GenLoop.coe_coe, ContinuousMap.toFun_eq_coe,
                ContinuousMap.Homotopy.coe_toContinuousMap,
                ContinuousMap.HomotopyWith.coe_toHomotopy, ContinuousMap.coe_mk] at this ⊢
              rw [this]
              exact f.property y hy'⟩ }


-- @@ L170-183 verbatim
/-- Restrict `f : C(I^ Fin (n + 1), X)` to the top face
(where the last coordinate equals `1`). -/
def bd' (f : RelGenLoop (n + 1) X A a) : π_ n A a :=
  Quotient.mk _
    ⟨ { toFun y := ⟨ (f ∘ Cube.inclToTop) y,
          f.property.left _ ⟨Fin.last _, by right; simp [Cube.splitAtLast, Cube.inclToTop]⟩ ⟩
        continuous_toFun := by
          refine Continuous.subtype_mk ?_ _
          exact f.val.continuous_toFun.comp Cube.inclToTop.continuous },
      fun y hy ↦ by
        apply Subtype.ext
        apply f.property.right _
        simp only [Cube.inclToTop, ContinuousMap.coe_mk]
        exact Cube.inclToTop.mem_boundaryJar_of hy ⟩


-- @@ L185-204 expanded
/-- The boundary map $∂$ (of pointed sets) from πₙ₊₁(X, A, a) to πₙ(A, a) -/
def bd : RelHomotopyGroup (n + 1) X A a → π_ n A a :=
  Quotient.lift (bd' n X A a) fun f g H ↦
    Quotient.sound <|
      Nonempty.intro
        { toFun
            ty :=
            ⟨H.some.toHomotopy.comp (ContinuousMap.Homotopy.refl Cube.inclToTop) ty, by
              apply H.some.prop' ty.1 |>.left; exact Cube.inclToTop.mem_boundary _⟩
          continuous_toFun := by
            refine Continuous.subtype_mk ?_ _
            apply ContinuousMapClass.map_continuous
          map_zero_left := by
            simp only [ContinuousMap.Homotopy.apply_zero, ContinuousMap.comp_apply,
              Function.comp_apply, ContinuousMap.coe_mk, implies_true]
          map_one_left := by
            simp only [ContinuousMap.Homotopy.apply_one, ContinuousMap.comp_apply,
              Function.comp_apply, ContinuousMap.coe_mk, implies_true]
          prop' t y
            hy :=
            by
            simp only [ContinuousMap.Homotopy.comp_apply, ContinuousMap.Homotopy.refl_apply,
              ContinuousMap.HomotopyWith.coe_toHomotopy, ContinuousMap.coe_mk, Function.comp_apply,
              Subtype.mk.injEq]
            have hjar := H.some.prop' t |>.right _ (Cube.inclToTop.mem_boundaryJar_of hy)
            rw [f.property.right _ (Cube.inclToTop.mem_boundaryJar_of hy)]
            exact hjar }


-- @@ L207-210 verbatim
/-!
The induced maps `iStar`, `jStar`, and `bd` preserve the distinguished point,
i.e., they map (the homotopy class of) the constant loop to the constant loop.
-/


-- @@ L212-213 verbatim
private lemma iStar'_const : iStar' n X A a GenLoop.const = ⟦GenLoop.const⟧ :=
  Quotient.sound ⟨⟨ContinuousMap.Homotopy.refl _, fun _ _ _ ↦ rfl⟩⟩

-- @@ L214-216 verbatim
private lemma jStar'_const : jStar' n X A a GenLoop.const = ⟦RelGenLoop.const⟧ :=
  Quotient.sound ⟨⟨ContinuousMap.Homotopy.refl _, fun _ ↦
    ⟨fun _ _ ↦ Set.mem_of_eq_of_mem rfl (Subtype.coe_prop a), fun _ _ ↦ rfl ⟩ ⟩⟩

-- @@ L217-218 verbatim
private lemma bd'_const : bd' n X A a RelGenLoop.const = ⟦GenLoop.const⟧ :=
  Quotient.sound ⟨⟨ContinuousMap.Homotopy.refl _, fun _ _ _ ↦ rfl⟩⟩


-- @@ L220-220 verbatim
instance iStar_isPointedMap : IsPointedMap (iStar n X A a) := ⟨by apply iStar'_const⟩

-- @@ L221-221 verbatim
instance jStar_isPointedMap : IsPointedMap (jStar n X A a) := ⟨by apply jStar'_const⟩

-- @@ L222-222 verbatim
instance bd_isPointedMap : IsPointedMap (bd n X A a) := ⟨by apply bd'_const⟩



-- @@ L225-225 verbatim
end RelHomotopyGroup



-- @@ L228-228 verbatim
namespace RelGenLoop

-- @@ L229-231 verbatim
/-!
Some useful lemmas for the `compression_criterion`
-/


-- @@ L233-233 verbatim
variable {n : ℕ} {X : Type*} [TopologicalSpace X] {A : Set X} {a : A}


-- @@ L235-246 expanded
/-- Let `g` be a continuous function from `I^ Fin n` to `X`.
If `g` is homotopic rel `∂I^n` to some `f : RelGenLoop n X A a`,
then `g` itself can be regarded as a `RelGenLoop`. -/
def ofHomotopyRel {n : ℕ} {X : Type*} [TopologicalSpace X] {A : Set X} {a : A}
    (f : RelGenLoop n X A a) (g : C(I^Fin n, X))
    (H : ContinuousMap.HomotopyRel f g (Cube.boundary (Fin n))) : RelGenLoop n X A a :=
  let g_bd : ∀ y ∈ Cube.boundary (Fin n), g y = f.val y :=
    -- g maps `∂I^n` in the same way `f` does.
    fun y hy ↦ (H.map_one_left y).symm.trans (H.prop' 1 y hy)
  ⟨g,
    ⟨fun y hy ↦ by rw [g_bd y hy]; exact f.property.left y hy, fun y hy ↦
      by
      rw [g_bd y (Cube.boundaryJar_subset_boundary n hy)]
      exact f.property.right y hy⟩⟩


-- @@ L248-248 verbatim
namespace ofHomotopyRel


-- @@ L250-257 expanded
lemma eq (f : RelGenLoop n X A a) (g : C(I^Fin n, X))
    (H : ContinuousMap.HomotopyRel f g (Cube.boundary (Fin n))) :
    ⟦f⟧ = (⟦ofHomotopyRel f g H⟧ : RelHomotopyGroup n X A a) :=
  Quotient.eq.mpr <|
    Nonempty.intro
      { toHomotopy := H.toHomotopy
        prop'
          t :=
          ⟨fun y hy ↦ Set.mem_of_eq_of_mem (H.prop' t y hy) (f.property.left y hy), fun y hy ↦
            H.prop' t y (Cube.boundaryJar_subset_boundary n hy) |>.trans <| f.property.right y hy⟩ }


-- @@ L259-259 verbatim
end ofHomotopyRel


-- @@ L261-261 verbatim
end RelGenLoop
