/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Control.Monad.Basic
public import Mathlib.CategoryTheory.Monad.Basic
public import Mathlib.CategoryTheory.Enriched.Basic


-- @@ L12-18 verbatim
/-!
# Relative monad

This file defines the `RelativeMonad` type class, both as a category-theoretic object and a
programming object.

-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
namespace CategoryTheory


-- @@ L24-24 verbatim
open Category


-- @@ L26-28 verbatim
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

-- morphism levels before object levels. See note [CategoryTheory universes].

-- @@ L29-29 verbatim
variable (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D]


-- @@ L31-53 verbatim
/-- The data of a **relative monad** over a functor `J : C ⟶ D` consists of:
- a map between objects `T : C → D`
- a natural transformation `η : ∀ {X}, J X ⟶ T X`
- a natural transformation `μ : ∀ {X Y}, (J X ⟶ T Y) ⟶ (T X ⟶ T Y)`
satisfying three equations:
- `μ_{X, X} ∘ η_X = 1_{T X}` (left unit)
- `∀ f, η_X ≫ μ_{X, Y} = f` (right unit)
- `∀ f g, μ_{X, Z} (f ≫ μ_{Y, Z} g) = μ_{X, Y} f ≫ μ_{Y, Z} g` (associativity)
-/
structure RelativeMonad (J : C ⥤ D) where
  /-- The monadic mapping on objects. -/
  T : C → D
  /-- The unit for the relative monad. -/
  η : ∀ {X}, J.obj X ⟶ T X
  /-- The multiplication for the monad. -/
  μ : ∀ {X Y}, ((J.obj X) ⟶ (T Y)) → ((T X) ⟶ (T Y))
  /-- `μ` applied to `η` is identity. -/
  left_unit : ∀ {X}, μ η = 𝟙 (T X) := by aesop_cat
  /-- `η` composed with `μ` is identity. -/
  right_unit : ∀ {X Y}, ∀ f : (J.obj X) ⟶ (T Y), η ≫ (μ f) = f := by aesop_cat
  /-- `μ` is associative. -/
  assoc : ∀ {X Y Z}, ∀ f : (J.obj X) ⟶ (T Y), ∀ g : (J.obj Y) ⟶ (T Z),
    μ (f ≫ μ g) = (μ f) ≫ (μ g) := by aesop_cat


-- @@ L55-55 verbatim
attribute [reassoc (attr := simp)] RelativeMonad.left_unit RelativeMonad.right_unit

-- @@ L56-56 verbatim
attribute [reassoc (attr := simp)] RelativeMonad.assoc


-- @@ L58-58 verbatim
namespace RelativeMonad


-- @@ L60-60 verbatim
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {J : C ⥤ D}


-- @@ L62-71 verbatim
/-- The functor induced by a relative monad.

**Note:** this is _not_ the same as the underlying functor of the relative monad. -/
@[simps]
def inducedFunctor (M : RelativeMonad C D J) : C ⥤ D where
  obj X := M.T X
  map f := M.μ (J.map f ≫ M.η)
  map_comp f g := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← assoc, Category.assoc, right_unit]


-- @@ L73-79 verbatim
/-- The natural transformation from the underlying functor of the relative monad, to the functor
induced by the relative monad. -/
def inducedNatTrans (M : RelativeMonad C D J) : NatTrans J M.inducedFunctor where
  app X := M.η
  naturality X Y f := by
    simp only [inducedFunctor_map]
    exact (M.right_unit (f := J.map f ≫ M.η)).symm


-- @@ L81-128 verbatim
/-- If a relative monad is over the identity functor, it is a monad. -/
def monadOfId (M : RelativeMonad C _ (𝟭 _)) : Monad C where
  toFunctor := M.inducedFunctor
  η :=
    { app := fun X => M.η
      naturality := fun X Y f => by
        simp only [Functor.id_map, inducedFunctor_map]
        exact (M.right_unit (f := f ≫ M.η)).symm }
  μ := NatTrans.mk (fun X => M.μ (𝟙 (M.T X)))
    (fun X Y f => by
      simp only [Functor.comp_map, inducedFunctor_map,
        Functor.id_obj, Functor.id_map]
      calc
        M.μ (M.μ (f ≫ M.η) ≫ M.η) ≫ M.μ (𝟙 (M.T Y))
            = M.μ ((M.μ (f ≫ M.η) ≫ M.η) ≫ M.μ (𝟙 (M.T Y))) := by
                symm
                exact M.assoc (f := M.μ (f ≫ M.η) ≫ M.η) (g := 𝟙 (M.T Y))
        _ = M.μ (M.μ (f ≫ M.η)) := by
              congr 1
              simp [Category.assoc]
        _ = M.μ (𝟙 (M.T X) ≫ M.μ (f ≫ M.η)) := by simp
        _ = M.μ (𝟙 (M.T X)) ≫ M.μ (f ≫ M.η) := by
              exact M.assoc (f := 𝟙 (M.T X)) (g := f ≫ M.η))
  left_unit X := by
    exact M.right_unit (f := 𝟙 (M.T X))
  right_unit X := by
    simp only [Functor.id_obj]
    calc
      M.μ (M.η ≫ M.η) ≫ M.μ (𝟙 (M.T X))
          = M.μ ((M.η ≫ M.η) ≫ M.μ (𝟙 (M.T X))) := by
              symm
              exact M.assoc (f := M.η ≫ M.η) (g := 𝟙 (M.T X))
      _ = M.μ M.η := by
            congr 1
            simp [Category.assoc]
      _ = 𝟙 (M.T X) := by simp
  assoc X := by
    calc
      M.μ (M.μ (𝟙 (M.T X)) ≫ M.η) ≫ M.μ (𝟙 (M.T X))
          = M.μ ((M.μ (𝟙 (M.T X)) ≫ M.η) ≫ M.μ (𝟙 (M.T X))) := by
              symm
              exact M.assoc (f := M.μ (𝟙 (M.T X)) ≫ M.η) (g := 𝟙 (M.T X))
      _ = M.μ (M.μ (𝟙 (M.T X))) := by
            congr 1
            simp [Category.assoc]
      _ = M.μ (𝟙 (M.T (M.T X)) ≫ M.μ (𝟙 (M.T X))) := by simp
      _ = M.μ (𝟙 (M.T (M.T X))) ≫ M.μ (𝟙 (M.T X)) := by
            exact M.assoc (f := 𝟙 (M.T (M.T X))) (g := 𝟙 (M.T X))


-- @@ L130-135 verbatim
/-- Transport a relative monad along a natural isomorphism of the underlying functor. -/
def ofNatIso {J₁ J₂ : C ⥤ D} (φ : J₁ ≅ J₂) (M : RelativeMonad C D J₁) : RelativeMonad C D J₂ where
  T := M.T
  η := φ.inv.app _ ≫ M.η
  μ := fun f => M.μ (φ.hom.app _ ≫ f)
  assoc f g := by rw [← assoc]; simp


-- @@ L137-147 verbatim
/-- Precompose a relative monad `M : RelativeMonad C D J` along a functor `J' : C' ⥤ C`. -/
def precompose {C' : Type u₃} [Category.{v₃} C'] (J' : C' ⥤ C) (M : RelativeMonad C D J) :
    RelativeMonad C' D (J' ⋙ J) where
  T := M.T ∘ J'.obj
  η := M.η
  μ := M.μ
  left_unit := M.left_unit
  right_unit f := M.right_unit f
  assoc f g := M.assoc f g

-- TODO: post-composition by a fully faithful functor


-- @@ L149-151 verbatim
variable {C₁ : Type u₁} [Category.{v₁} C₁] {D₁ : Type u₂} [Category.{v₂} D₁]
  {C₂ : Type u₃} [Category.{v₃} C₂] {D₂ : Type u₄} [Category.{v₄} D₂]
  {J₁ : C₁ ⥤ D₁} {J₂ : C₂ ⥤ D₂}


-- @@ L153-163 verbatim
/-- The product of two relative monads is a relative monad on the corresponding product
categories. -/
@[simps!]
def prod (M₁ : RelativeMonad C₁ D₁ J₁) (M₂ : RelativeMonad C₂ D₂ J₂) :
    RelativeMonad (C₁ × C₂) (D₁ × D₂) (Functor.prod J₁ J₂) where
  T := fun X => (M₁.T X.fst, M₂.T X.snd)
  η := ⟨M₁.η, M₂.η⟩
  μ := fun f => ⟨M₁.μ f.fst, M₂.μ f.snd⟩
  left_unit := Prod.ext M₁.left_unit M₂.left_unit
  right_unit f := Prod.ext (M₁.right_unit f.fst) (M₂.right_unit f.snd)
  assoc f g := Prod.ext (M₁.assoc f.fst g.fst) (M₂.assoc f.snd g.snd)


-- @@ L165-165 verbatim
end RelativeMonad


-- @@ L167-168 verbatim
variable {C : Type u₁} [Category.{v₁} C] {D₁ : Type u₂} [Category.{v₂} D₁]
  {D₂ : Type u₃} [Category.{v₃} D₂] {J₁ : C ⥤ D₁} {J₂ : C ⥤ D₂}


-- @@ L170-178 verbatim
/-- A morphism of relative monads, where the two ending categories may be different. We require
another functor & a natural isomorphism to correct for this discrepancy. -/
structure RelativeMonadHom (M₁ : RelativeMonad C D₁ J₁) (M₂ : RelativeMonad C D₂ J₂) where
  J₁₂ : D₁ ⥤ D₂
  φ : J₂ ≅ (J₁ ⋙ J₁₂)
  map : ∀ {X}, J₁₂.obj (M₁.T X) ⟶ M₂.T X
  map_η : ∀ {X}, J₁₂.map M₁.η ≫ map = φ.inv.app X ≫ M₂.η := by aesop_cat
  map_μ : ∀ {X Y}, ∀ f : (J₁.obj X) ⟶ M₁.T Y,
    J₁₂.map (M₁.μ f) ≫ map = map ≫ M₂.μ (φ.hom.app _ ≫ J₁₂.map f ≫ map) := by aesop_cat


-- @@ L180-180 verbatim
attribute [reassoc (attr := simp)] RelativeMonadHom.map_η RelativeMonadHom.map_μ


-- @@ L182-182 verbatim
end CategoryTheory


-- @@ L184-190 verbatim
/-! ## Old stuff below.

Turns out one cannot just work with `Type u → Type v`, since in the relational context, relative
relational specification monad actually has signature `Type u₁ × Type u₂ → Type v₁ × Type v₂`. This
means that we have to develop the general theory at the category-theoretic level.

-/


-- @@ L192-192 verbatim
universe u w v


-- @@ L194-197 verbatim
/-- Type class for the relative pure operation -/
class RelativePure (j : Type u → Type w) (f : Type u → Type v) where
  /-- The relative pure operation -/
  pureᵣ : {α : Type u} → j α → f α


-- @@ L199-199 verbatim
export RelativePure (pureᵣ)


-- @@ L201-204 verbatim
/-- Type class for the relative bind operation -/
class RelativeBind (j : Type u → Type w) (m : Type u → Type v) where
  /-- The relative bind operation -/
  bindᵣ : {α β : Type u} → m α → (j α → m β) → m β


-- @@ L206-206 verbatim
export RelativeBind (bindᵣ)


-- @@ L208-212 verbatim
/-- Type class for the relative map operation -/
class RelativeFunctor (j : Type u → Type w) (f : Type u → Type v) where
  /-- The relative map operation -/
  mapᵣ : {α β : Type u} → (j α → j β) → (f α → f β)
  mapConstᵣ : {α β : Type u} → j α → f β → f α := mapᵣ ∘ Function.const _


-- @@ L214-218 verbatim
export RelativeFunctor (mapᵣ mapConstᵣ)

/- The relative interface stops at `pure`, `bind`, and `map`: sequencing operations have no
relative counterpart here, since a relative applicative would need the sequencing structure on
the root functor as well. -/


-- @@ L220-220 verbatim
@[inherit_doc] infixl:55  " >>=ᵣ " => RelativeBind.bindᵣ

-- @@ L221-221 verbatim
@[inherit_doc] infixr:100 " <$>ᵣ " => RelativeFunctor.mapᵣ


-- @@ L223-226 verbatim
/-- Type class for the relative monad -/
class RelativeMonad (j : Type u → Type w) (m : Type u → Type v)
    extends RelativePure j m, RelativeBind j m, RelativeFunctor j m where
  mapᵣ f x := bindᵣ x (pureᵣ ∘ f)


-- @@ L228-231 verbatim
@[reducible] def instFunctorOfRelativeMonad {j : Type u → Type w} [Functor j]
    {m : Type u → Type v}
    [RelativeMonad j m] : Functor m where
  map f x := bindᵣ (j := j) x (pureᵣ ∘ (Functor.map f))


-- @@ L233-236 verbatim
@[reducible] def instSeqOfRelativeMonadOfSeq {j : Type u → Type w} [Seq j]
    {m : Type u → Type v}
    [RelativeMonad j m] : Seq m where
  seq f x := bindᵣ (j := j) (m := m) f (fun y => mapᵣ (y <*> ·) (x ()))


-- @@ L238-238 verbatim
variable {j : Type u → Type w} {m f : Type u → Type v}


-- @@ L240-241 verbatim
instance [RelativePure Id f] : Pure f where
  pure := @pureᵣ Id f _


-- @@ L243-244 verbatim
instance [RelativeBind Id m] : Bind m where
  bind := @bindᵣ Id m _


-- @@ L246-248 verbatim
instance [RelativeFunctor Id f] : Functor f where
  map := @mapᵣ Id f _
  mapConst := @mapConstᵣ Id f _


-- @@ L250-252 verbatim
instance [RelativeMonad Id m] : Monad m where
  pure := @pureᵣ Id m _
  bind := @bindᵣ Id m _


-- @@ L254-254 verbatim
section Lawful


-- @@ L256-264 expanded
class LawfulRelativeFunctor (j : Type u → Type w) (f : Type u → Type v) [RelativeFunctor j f] where
  map_constᵣ {α β : Type u} : (mapConstᵣ : j α → f β → _) = mapᵣ ∘ (Function.const _)
  id_mapᵣ {α : Type u} (x : f α) : RelativeFunctor.mapᵣ (id : j α → _) x = x
  comp_mapᵣ {α β γ : Type u} (g : j α → j β) (h : j β → j γ) (x : f α) :
    RelativeFunctor.mapᵣ (h ∘ g) x = RelativeFunctor.mapᵣ h (RelativeFunctor.mapᵣ g x)


-- @@ L266-266 verbatim
export LawfulRelativeFunctor (map_constᵣ id_mapᵣ comp_mapᵣ)


-- @@ L268-268 verbatim
attribute [simp] id_mapᵣ


-- @@ L270-270 verbatim
variable {α β γ : Type u}


-- @@ L272-274 expanded
@[simp]
theorem id_mapᵣ' [RelativeFunctor j f] [LawfulRelativeFunctor j f] (x : f α) :
    RelativeFunctor.mapᵣ (fun a : j α => a) x = x :=
  id_mapᵣ x


-- @@ L276-279 expanded
@[simp]
theorem RelativeFunctor.map_map [RelativeFunctor j f] [LawfulRelativeFunctor j f] (h : j α → j β)
    (g : j β → j γ) (x : f α) :
    RelativeFunctor.mapᵣ g (RelativeFunctor.mapᵣ h x) = RelativeFunctor.mapᵣ (fun a => g (h a)) x :=
  (comp_mapᵣ _ _ _).symm


-- @@ L281-295 expanded
class LawfulRelativeMonad (j : Type u → Type w) (m : Type u → Type v) [RelativeMonad j m] extends
    LawfulRelativeFunctor j m where
  pure_bindᵣ {α β : Type u} (x : j α) (f : j α → m β) : RelativeBind.bindᵣ (pureᵣ x) f = f x
  bind_pure_compᵣ {α β : Type u} (f : j α → j β) (x : m α) :
    RelativeBind.bindᵣ x (fun y => pureᵣ (f y)) = RelativeFunctor.mapᵣ f x
  bind_assocᵣ {α β γ : Type u} (x : m α) (f : j α → m β) (g : j β → m γ) :
    RelativeBind.bindᵣ (RelativeBind.bindᵣ x f) g =
      RelativeBind.bindᵣ x fun x ↦ RelativeBind.bindᵣ (f x) g


-- @@ L297-297 verbatim
export LawfulRelativeMonad (pure_bindᵣ bind_pure_compᵣ bind_assocᵣ)

-- @@ L298-298 verbatim
attribute [simp] pure_bindᵣ bind_pure_compᵣ bind_assocᵣ


-- @@ L300-303 expanded
@[simp]
theorem bind_pureᵣ [RelativeMonad j m] [LawfulRelativeMonad j m] (x : m α) :
    RelativeBind.bindᵣ x (pureᵣ (j := j)) = x :=
  by
  change RelativeBind.bindᵣ x (fun a => pureᵣ (id a)) = x
  rw [bind_pure_compᵣ, id_mapᵣ]


-- @@ L305-307 expanded
theorem map_eq_pure_bindᵣ [RelativeMonad j m] [LawfulRelativeMonad j m] (f : j α → j β) (x : m α) :
    RelativeFunctor.mapᵣ f x = RelativeBind.bindᵣ x fun a => pureᵣ (f a) := by
  rw [← bind_pure_compᵣ]


-- @@ L309-311 expanded
theorem bind_congrᵣ [RelativeBind j m] {x : m α} {f g : j α → m β} (h : ∀ a, f a = g a) :
    RelativeBind.bindᵣ x f = RelativeBind.bindᵣ x g := by simp [funext h]


-- @@ L313-315 expanded
theorem bind_pure_unitᵣ [RelativeMonad j m] [LawfulRelativeMonad j m] {x : m PUnit} :
    (RelativeBind.bindᵣ x fun y : j PUnit => pureᵣ y) = x := by rw [bind_pure_compᵣ];
  exact id_mapᵣ x


-- @@ L317-319 expanded
theorem map_congrᵣ [RelativeFunctor j m] {x : m α} {f g : j α → j β} (h : ∀ a, f a = g a) :
    (RelativeFunctor.mapᵣ f x : m β) = RelativeFunctor.mapᵣ g x := by simp [funext h]


-- @@ L321-325 expanded
@[simp]
theorem map_bindᵣ [RelativeMonad j m] [LawfulRelativeMonad j m] (f : j β → j γ) (x : m α)
    (g : j α → m β) :
    RelativeFunctor.mapᵣ f (RelativeBind.bindᵣ x g) =
      RelativeBind.bindᵣ x fun a : j α => RelativeFunctor.mapᵣ f (g a) :=
  by
  rw [← bind_pure_compᵣ, bind_assocᵣ]
  simp only [bind_pure_compᵣ]


-- @@ L327-331 expanded
@[simp]
theorem bind_map_leftᵣ [RelativeMonad j m] [LawfulRelativeMonad j m] (f : j α → j β) (x : m α)
    (g : j β → m γ) :
    (RelativeBind.bindᵣ (RelativeFunctor.mapᵣ f x) fun b => g b) =
      (RelativeBind.bindᵣ x fun a : j α => g (f a)) :=
  by
  rw [← bind_pure_compᵣ, bind_assocᵣ]
  simp only [pure_bindᵣ]


-- @@ L333-335 expanded
theorem RelativeFunctor.map_unitᵣ [RelativeMonad j m] [LawfulRelativeMonad j m] {a : m PUnit} :
    RelativeFunctor.mapᵣ (fun y : j PUnit => y) a = a := by simp


-- @@ L337-340 verbatim
instance [RelativeFunctor Id f] [LawfulRelativeFunctor Id f] : LawfulFunctor f where
  map_const := @map_constᵣ Id f _ _
  id_map := @id_mapᵣ Id f _ _
  comp_map := @comp_mapᵣ Id f _ _


-- @@ L342-342 verbatim
end Lawful


-- @@ L344-350 verbatim
class MonadIso (m : Type u → Type v) (n : Type u → Type w) where
  toLift : MonadLiftT m n
  invLift : MonadLiftT n m
  monadLift_left_inv {α : Type u} :
    Function.LeftInverse (toLift.monadLift (α := α)) (invLift.monadLift (α := α))
  monadLift_right_inv {α : Type u} :
    Function.RightInverse (toLift.monadLift (α := α)) (invLift.monadLift (α := α))


-- @@ L352-352 verbatim
universe u₁ u₂ v₁ v₂ w₁ w₂


-- @@ L354-365 expanded
class RelativeMonadMorphism (r₁ : Type u → Type v₁) (m₁ : Type u → Type v₁) (r₂ : Type u → Type v₂)
    (m₂ : Type u → Type v₂) [RelativeMonad r₁ m₁] [RelativeMonad r₂ m₂] where
  r₁₂ : Type v₁ → Type v₂
  [instFunctor : Functor r₁₂]
  φ : MonadIso r₂ (r₁₂ ∘ r₁)
  mmapᵣ {α : Type u} : r₁₂ (m₁ α) → m₂ α
  mmapᵣ_pureᵣ {α} :
    mmapᵣ ∘ (Functor.map (f := r₁₂) (@pureᵣ r₁ m₁ _ α)) = pureᵣ ∘ φ.invLift.monadLift
  mmapᵣ_bindᵣ {α β : Type u} (f : r₁ α → m₁ β) :
    mmapᵣ ∘ (Functor.map (f := r₁₂) (bindᵣ · f)) =
      (RelativeBind.bindᵣ · (mmapᵣ ∘ Functor.map (f := r₁₂) f ∘ φ.toLift.monadLift)) ∘ mmapᵣ

