/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
module

public import LeanPool.DirectedTopologyLean4.DirectedSpace


-- @@ L10-12 verbatim
/-!
# LeanPool.DirectedTopologyLean4.DirectedMap
-/


-- @@ L14-25 verbatim
@[expose] public section

/-
  # Definition of directed maps
  This file defines the directed map between two directed spaces `X` and `Y` :
  it is a continuous map from `X` to `Y` that is also `Directed`, i.e. it maps any dipath in `X` to
  a dipath in `Y`.
  We give the definitions of:
  * Constant maps
  * Identities
  * Composition of directed maps
-/


-- @@ L27-27 verbatim
namespace DirectedMap


-- @@ L29-31 verbatim
/-- A continuous map between two directed spaces is `Directed` if it maps dipaths to dipaths. -/
def Directed {α β : Type*} [DirectedSpace α] [DirectedSpace β] (f : C(α, β)) : Prop :=
  ∀ ⦃x y : α⦄ (γ : Path x y), IsDipath γ → IsDipath (γ.map f.continuous_toFun)


-- @@ L33-33 verbatim
end DirectedMap


-- @@ L35-38 verbatim
/-- Define the type of a directed map -/
structure DirectedMap (α β : Type*) [DirectedSpace α] [DirectedSpace β]
    extends ContinuousMap α β where
  protected directed_toFun : DirectedMap.Directed toContinuousMap


-- @@ L40-41 verbatim
/-- Notation `D(X,Y)` for directed maps from `X` to `Y` -/
notation "D("α","β")" => DirectedMap α β


-- @@ L43-43 verbatim
section


-- @@ L45-49 verbatim
/-- Type class for the bundled directed maps from `α` to `β`. -/
class DirectedMapClass (F : Type*) (α β : outParam <| Type*) [DirectedSpace α] [DirectedSpace β]
  [FunLike F α β] : Prop extends ContinuousMapClass F α β where
  /-- Each element of the class is directed when viewed as a continuous map. -/
  map_directed (f : F) : DirectedMap.Directed (f : C(α, β))


-- @@ L51-51 verbatim
end


-- @@ L53-53 verbatim
export DirectedMapClass (map_directed)


-- @@ L55-55 verbatim
section DirectedMapClass


-- @@ L57-58 verbatim
variable {F α β : Type*} [DirectedSpace α] [DirectedSpace β] [FunLike F α β]
    [hF : DirectedMapClass F α β]

-- @@ L59-60 expanded
/-- Coerce a member of a `DirectedMapClass` to the bundled directed map type `D(α, β)`. -/
@[coe]
def toDirectedMap (f : F) : DirectedMap α β :=
  ⟨f, map_directed f⟩


-- @@ L61-61 expanded
instance : CoeTC F (DirectedMap α β) :=
  ⟨toDirectedMap⟩


-- @@ L63-63 verbatim
end DirectedMapClass


-- @@ L65-65 verbatim
variable {α β γ δ : Type*} [DirectedSpace α] [DirectedSpace β] [DirectedSpace γ] [DirectedSpace δ]


-- @@ L67-67 verbatim
namespace DirectedMap


-- @@ L69-74 expanded
instance instFunLike : FunLike (DirectedMap α β) α β
    where
  coe := fun f => f.toFun
  coe_injective f g
    h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr


-- @@ L76-78 expanded
instance toDirectedMapClass : DirectedMapClass (DirectedMap α β) α β
    where
  map_continuous := fun f => f.continuous_toFun
  map_directed := fun f => f.directed_toFun


-- @@ L80-82 expanded
/-- Helper instance for when there's too many metavariables to apply `FunLike.hasCoeToFun` directly.
-/
instance : CoeFun (DirectedMap α β) fun _ => α → β :=
  DFunLike.toCoeFun


-- @@ L84-85 expanded
/-- A directed map can be coerced into a continuous map -/
instance : Coe (DirectedMap α β) C(α, β) :=
  ⟨fun f => f.toContinuousMap⟩


-- @@ L87-87 expanded
@[simp]
lemma toFun_eq_coe {f : DirectedMap α β} : f.toFun = (f : α → β) :=
  rfl


-- @@ L88-88 expanded
@[simp]
lemma coe_to_continuous_map (f : DirectedMap α β) : ⇑f.toContinuousMap = f :=
  rfl


-- @@ L89-90 expanded
@[simp]
protected lemma coe_coe {F : Type*} [FunLike F α β] [DirectedMapClass F α β] (f : F) :
    ⇑(f : DirectedMap α β) = f :=
  rfl


-- @@ L92-92 expanded
@[ext]
theorem ext {f g : DirectedMap α β} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h


-- @@ L94-94 verbatim
variable (α)


-- @@ L96-99 expanded
/-- The identity map is directed -/
protected def id : DirectedMap α α where
  toFun := id
  directed_toFun := fun x y γ γ_path => γ_path


-- @@ L101-101 verbatim
@[simp] lemma coe_id : ⇑(DirectedMap.id α) = id := rfl


-- @@ L103-106 expanded
/-- Constant maps are directed -/
def const (b : β) : DirectedMap α β
    where
  toFun := fun _ : α => b
  directed_toFun := fun x y γ _ => isDipath_constant b


-- @@ L108-108 verbatim
@[simp] lemma coe_const (b : β) : ⇑(const α b) = Function.const α b := rfl


-- @@ L110-110 verbatim
variable {α}


-- @@ L112-116 expanded
/-- The composition of directed maps is directed -/
def comp (f : DirectedMap β γ) (g : DirectedMap α β) : DirectedMap α γ
    where
  toFun := f ∘ g
  directed_toFun := fun x y p hp =>
    f.directed_toFun (p.map g.continuous_toFun) (g.directed_toFun p hp)


-- @@ L119-119 verbatim
@[simp] lemma id_apply (a : α) : DirectedMap.id α a = a := rfl

-- @@ L120-120 verbatim
@[simp] lemma const_apply (b : β) (a : α) : const α b a = b := rfl

-- @@ L121-121 expanded
@[simp]
lemma coe_comp (f : DirectedMap β γ) (g : DirectedMap α β) : ⇑(f.comp g) = f ∘ g :=
  rfl


-- @@ L122-122 expanded
@[simp]
lemma comp_apply (f : DirectedMap β γ) (g : DirectedMap α β) (a : α) : f.comp g a = f (g a) :=
  rfl


-- @@ L123-124 expanded
@[simp]
lemma comp_assoc (f : DirectedMap γ δ) (g : DirectedMap β γ) (h : DirectedMap α β) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl


-- @@ L125-125 expanded
@[simp]
lemma id_comp (f : DirectedMap α β) : (DirectedMap.id β).comp f = f :=
  ext fun _ => rfl


-- @@ L126-126 expanded
@[simp]
lemma comp_id (f : DirectedMap α β) : f.comp (DirectedMap.id α) = f :=
  ext fun _ => rfl


-- @@ L127-128 expanded
@[simp]
lemma const_comp (c : γ) (f : DirectedMap α β) : (const β c).comp f = const α c :=
  ext <| fun _ => rfl


-- @@ L129-130 expanded
@[simp]
lemma comp_const (f : DirectedMap β γ) (b : β) : f.comp (const α b) = const α (f b) :=
  ext <| fun _ => rfl


-- @@ L132-133 expanded
lemma coe_injective : @Function.Injective (DirectedMap α β) (α → β) (↑) := fun f g h => by cases f;
  cases g; congr; exact ContinuousMap.ext (congrFun h)


-- @@ L135-135 verbatim
end DirectedMap
