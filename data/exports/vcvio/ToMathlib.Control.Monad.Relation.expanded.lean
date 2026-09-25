/-
Copyright (c) 2025 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Batteries.Tactic.Alias


-- @@ L10-10 verbatim
/-! # Monad relations -/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
universe u v w v₁ w₁ v₂ w₂


-- @@ L16-17 verbatim
class MonadRelation (m : Type u → Type v) (n : Type u → Type w) where
  monadRel {α : Type u} : m α → n α → Prop


-- @@ L19-19 verbatim
export MonadRelation (monadRel)


-- @@ L21-21 verbatim
namespace MonadRelation


-- @@ L23-23 verbatim
scoped infix:50 " ∼ₘ " => monadRel


-- @@ L25-25 verbatim
end MonadRelation


-- @@ L27-31 verbatim
class LawfulMonadRelation (m : Type u → Type v) (n : Type u → Type w) [Monad m] [Monad n]
    [MonadRelation m n] where
  monadRel_pure {α : Type u} (a : α) : monadRel (pure a : m α) (pure a : n α)
  monadRel_bind {α β : Type u} {ma : m α} {mb : α → m β} {na : n α} {nb : α → n β}
    (ha : monadRel ma na) (hb : ∀ a, monadRel (mb a) (nb a)) : monadRel (ma >>= mb) (na >>= nb)


-- @@ L33-33 verbatim
export LawfulMonadRelation (monadRel_pure monadRel_bind)


-- @@ L35-37 verbatim
attribute [simp] monadRel_pure monadRel_bind

-- TODO: add examples & interactions with other monad classes


-- @@ L39-39 verbatim
namespace MonadRelation


-- @@ L41-43 verbatim
/-- A (transitive) monad lift defines a monad relation via its graph -/
instance instOfMonadLiftT {m n} [MonadLiftT m n] : MonadRelation m n where
  monadRel := fun ma na => liftM ma = na


-- @@ L45-49 verbatim
/-- A (transitive) lawful monad lift defines a lawful monad relation via its graph -/
instance instOfLawfulMonadLiftT {m n} [Monad m] [Monad n] [MonadLiftT m n] [LawfulMonadLiftT m n] :
    LawfulMonadRelation m n where
  monadRel_pure _ := by simp only [monadRel, liftM_pure]
  monadRel_bind _ _ := by simp_all only [monadRel, liftM_bind]


-- @@ L51-51 verbatim
end MonadRelation


-- @@ L53-56 verbatim
class MonadRelationHom (m₁ : Type u → Type v₁) (n₁ : Type u → Type w₁)
    (m₂ : Type u → Type v₂) (n₂ : Type u → Type w₂) where
  monadRelHomFst {α : Type u} : m₁ α → m₂ α
  monadRelHomSnd {α : Type u} : n₁ α → n₂ α


-- @@ L58-58 verbatim
export MonadRelationHom (monadRelHomFst monadRelHomSnd)


-- @@ L60-66 verbatim
open MonadRelation in
class LawfulMonadRelationHom (m₁ : Type u → Type v₁) (n₁ : Type u → Type w₁)
    (m₂ : Type u → Type v₂) (n₂ : Type u → Type w₂)
    [MonadRelation m₁ n₁] [MonadRelation m₂ n₂]
    [MonadRelationHom m₁ n₁ m₂ n₂] where
  monadRel_hom {α : Type u} {ma : m₁ α} {na : n₁ α} (h : ma ∼ₘ na) :
    (monadRelHomFst n₁ n₂ ma : m₂ α) ∼ₘ (monadRelHomSnd m₁ m₂ na : n₂ α)
