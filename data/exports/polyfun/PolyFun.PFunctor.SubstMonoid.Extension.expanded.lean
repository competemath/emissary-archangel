/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.SubstMonoid
public import PolyFun.Control.Monad.Hom


-- @@ L11-19 verbatim
/-!
# Extensions of substitution monoids

A polynomial lens induces a natural map between polynomial extensions.  In
particular, the unit and multiplication of a substitution monoid equip the
extension of its carrier with a lawful monad.  This is the extension-level
bridge between monoid objects for polynomial substitution and ordinary
monads on types.
-/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
attribute [local implicit_reducible] PFunctor.Obj


-- @@ L25-25 verbatim
universe uA uB


-- @@ L27-27 verbatim
namespace PFunctor


-- @@ L29-29 verbatim
namespace SubstMonoid


-- @@ L31-36 verbatim
/-- The extension of the carrier polynomial of a substitution monoid.  It is
kept as a named type constructor so its monad instance determines the source
substitution monoid unambiguously. -/
@[reducible]
def Extension (M : SubstMonoid.{uA, uB}) (α : Type uB) : Type (max uA uB) :=
  M.carrier.Obj α


-- @@ L38-38 verbatim
namespace Extension


-- @@ L40-40 verbatim
variable (M : SubstMonoid.{uA, uB})


-- @@ L42-45 verbatim
/-- The extension-level unit induced by the polynomial unit lens. -/
def pure {α : Type uB} (x : α) : Extension M α :=
  Lens.mapObj M.unit
    (⟨PUnit.unit, fun _ => x⟩ : y.{max uA uB, uB}.Obj α)


-- @@ L47-52 verbatim
/-- The extension-level bind induced by polynomial substitution. -/
def bind {α β : Type uB} (x : Extension M α) (f : α → Extension M β) : Extension M β :=
  Lens.mapObj M.mult
    (⟨⟨x.1, fun d => (f (x.2 d)).1⟩,
      fun direction => (f (x.2 direction.1)).2 direction.2⟩ :
      (M.carrier ◃ M.carrier).Obj β)


-- @@ L54-56 verbatim
instance instMonad : Monad (Extension M) where
  pure := pure M
  bind := bind M


-- @@ L58-60 verbatim
@[simp]
theorem pure_def {α : Type uB} (x : α) : (Pure.pure x : Extension M α) = pure M x :=
  rfl


-- @@ L62-65 verbatim
@[simp]
theorem bind_def {α β : Type uB} (x : Extension M α) (f : α → Extension M β) :
    x >>= f = bind M x f :=
  rfl


-- @@ L67-69 verbatim
theorem pure_bind {α β : Type uB} (x : α) (f : α → Extension M β) :
    (Pure.pure x : Extension M α) >>= f = f x :=
  congrArg (fun lens => Lens.mapObj lens (f x)) M.unit_left


-- @@ L71-73 verbatim
theorem bind_pure {α : Type uB} (x : Extension M α) :
    x >>= (fun y => (Pure.pure y : Extension M α)) = x :=
  congrArg (fun lens => Lens.mapObj lens x) M.unit_right


-- @@ L75-82 verbatim
theorem bind_assoc {α β γ : Type uB} (x : Extension M α) (f : α → Extension M β)
    (g : β → Extension M γ) : (x >>= f) >>= g = x >>= fun y => f y >>= g :=
  let source : ((M.carrier ◃ M.carrier) ◃ M.carrier).Obj γ :=
    ⟨⟨⟨x.1, fun d => (f (x.2 d)).1⟩,
        fun direction => (g ((f (x.2 direction.1)).2 direction.2)).1⟩,
      fun direction =>
        (g ((f (x.2 direction.1.1)).2 direction.1.2)).2 direction.2⟩
  congrArg (fun lens => Lens.mapObj lens source) M.assoc


-- @@ L84-91 verbatim
instance instLawfulMonad : LawfulMonad (Extension M) := LawfulMonad.mk'
  (bind_pure_comp := by
    intro α β f x
    exact congrArg
      (fun lens => Lens.mapObj lens (⟨x.1, f ∘ x.2⟩ : M.carrier.Obj β)) M.unit_right)
  (id_map := fun _ => rfl)
  (pure_bind := pure_bind M)
  (bind_assoc := bind_assoc M)


-- @@ L93-93 verbatim
end Extension


-- @@ L95-95 verbatim
namespace Hom


-- @@ L97-97 verbatim
variable {M N : SubstMonoid.{uA, uB}}


-- @@ L99-110 verbatim
/-- A substitution-monoid homomorphism induces a monad homomorphism between
the extensions of its carrier polynomials. -/
def toMonadHom (f : SubstMonoid.Hom M N) : (Extension M) →ᵐ (Extension N) where
  toFun _ := Lens.mapObj f.toLens
  toFun_pure' x :=
    congrArg (fun lens => Lens.mapObj lens
      (⟨PUnit.unit, fun _ => x⟩ : y.{max uA uB, uB}.Obj _)) f.map_unit
  toFun_bind' x k :=
    let source : (M.carrier ◃ M.carrier).Obj _ :=
      ⟨⟨x.1, fun d => (k (x.2 d)).1⟩,
        fun direction => (k (x.2 direction.1)).2 direction.2⟩
    congrArg (fun lens => Lens.mapObj lens source) f.map_mult


-- @@ L112-115 verbatim
@[simp]
theorem toMonadHom_apply (f : SubstMonoid.Hom M N) {α : Type uB} (x : Extension M α) :
    f.toMonadHom x = Lens.mapObj f.toLens x :=
  rfl


-- @@ L117-117 verbatim
end Hom


-- @@ L119-119 verbatim
end SubstMonoid


-- @@ L121-121 verbatim
end PFunctor
