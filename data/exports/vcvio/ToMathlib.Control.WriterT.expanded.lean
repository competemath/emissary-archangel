/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
module

public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Control.Monad.Writer
public import Mathlib.Order.Basic
public import Batteries.Control.AlternativeMonad


-- @@ L13-23 verbatim
/-!
# Writer Monad Transformer Utilities

This file extends `WriterT` with helper lemmas and the additive wrapper `AddWriterT`.

The first half of the file collects basic `WriterT` run, bind, and lifting lemmas, together with
the `LawfulAppend` class used to build lawful `WriterT` instances over append-like logs.

The second half specializes `WriterT` to additive cost accumulation via `Multiplicative`, and
introduces predicates and notation for reasoning about outputs and accumulated costs.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
universe u v w


-- @@ L29-34 verbatim
/-- Typeclass for instances where `∅` is an identity for `++`. -/
class LawfulAppend (α : Type u)
    [EmptyCollection α] [Append α] where
  empty_append (x : α) : ∅ ++ x = x
  append_empty (x : α) : x ++ ∅ = x
  append_assoc (x y z : α) : x ++ (y ++ z) = x ++ y ++ z


-- @@ L36-36 verbatim
namespace LawfulAppend


-- @@ L38-38 verbatim
attribute [simp] LawfulAppend.empty_append LawfulAppend.append_empty


-- @@ L40-41 verbatim
attribute [grind =] LawfulAppend.empty_append
  LawfulAppend.append_empty LawfulAppend.append_assoc


-- @@ L43-49 verbatim
instance {M : Type u → Type v} {ω : Type u} [Monad M]
    [EmptyCollection ω] [Append ω] [LawfulAppend ω] [LawfulMonad M] :
    LawfulMonad (WriterT ω M) := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ => by ext; simp)
  (id_map := fun _ => by ext; simp)
  (pure_bind := fun _ _ => by ext; simp)
  (bind_assoc := fun _ _ _ => by ext; simp [LawfulAppend.append_assoc])


-- @@ L51-54 verbatim
instance (α : Type u) : LawfulAppend (List α) where
  empty_append := by simp
  append_empty := by simp
  append_assoc := by grind


-- @@ L56-56 verbatim
end LawfulAppend


-- @@ L58-58 verbatim
namespace WriterT


-- @@ L60-60 verbatim
section basic


-- @@ L62-62 verbatim
variable {m : Type u → Type v} [Monad m] {ω : Type u} {α β γ : Type u}


-- @@ L64-64 verbatim
section monoid


-- @@ L66-66 verbatim
variable [Monoid ω]


-- @@ L68-69 verbatim
@[simp]
lemma run_monadLift (x : m α) : (monadLift x : WriterT ω m α).run = (·, 1) <$> x := rfl


-- @@ L71-72 verbatim
lemma liftM_def (x : m α) :
    (liftM x : WriterT ω m α) = WriterT.mk ((·, 1) <$> x) := rfl


-- @@ L74-75 verbatim
lemma monadLift_def (x : m α) :
    (MonadLift.monadLift x : WriterT ω m α) = WriterT.mk ((·, 1) <$> x) := rfl


-- @@ L77-79 verbatim
lemma bind_def (x : WriterT ω m α) (f : α → WriterT ω m β) :
    x >>= f = WriterT.mk (x.run >>= fun (a, w₁) ↦
      (Prod.map id (w₁ * ·)) <$> (f a)) := rfl


-- @@ L81-84 verbatim
@[simp]
lemma run_seqLeft {m : Type u → Type v} [Monad m] {ω : Type u} [Monoid ω] {α β : Type u}
    (x : WriterT ω m α) (y : WriterT ω m β) :
    (x *> y).run = x.run >>= fun z => Prod.map id (z.2 * ·) <$> y.run := rfl


-- @@ L86-89 verbatim
/-- `Prod.fst <$> WriterT.run` preserves `pure` (Monoid flavour). -/
lemma fst_map_run_pure [LawfulMonad m] (x : α) :
    Prod.fst <$> ((pure x : WriterT ω m α).run) = pure x := by
  simp [WriterT.run_pure]


-- @@ L91-97 verbatim
/-- `Prod.fst <$> WriterT.run` preserves `bind` (Monoid flavour) — i.e. it is a
monad morphism `WriterT ω m → m`. -/
lemma fst_map_run_bind [LawfulMonad m] (b : WriterT ω m α) (f : α → WriterT ω m β) :
    Prod.fst <$> (b >>= f).run =
      (Prod.fst <$> b.run) >>= fun x => Prod.fst <$> (f x).run := by
  simp only [WriterT.run_bind, map_bind, Functor.map_map]
  exact (bind_map_left (m := m) Prod.fst b.run (fun x => Prod.fst <$> (f x).run)).symm


-- @@ L99-99 verbatim
end monoid


-- @@ L101-101 verbatim
section append


-- @@ L103-103 verbatim
variable [EmptyCollection ω]


-- @@ L105-106 verbatim
@[simp]
lemma run_monadLift' (x : m α) : (monadLift x : WriterT ω m α).run = (·, ∅) <$> x := rfl


-- @@ L108-109 verbatim
lemma liftM_def' (x : m α) :
    (liftM x : WriterT ω m α) = WriterT.mk ((·, ∅) <$> x) := rfl


-- @@ L111-112 verbatim
lemma monadLift_def' (x : m α) :
    (MonadLift.monadLift x : WriterT ω m α) = WriterT.mk ((·, ∅) <$> x) := rfl


-- @@ L114-114 verbatim
variable [Append ω]


-- @@ L116-118 verbatim
lemma bind_def' (x : WriterT ω m α) (f : α → WriterT ω m β) :
    x >>= f = WriterT.mk (x.run >>= fun (a, w₁) ↦
      (Prod.map id (w₁ ++ ·)) <$> (f a)) := rfl


-- @@ L120-122 verbatim
@[simp]
lemma run_pure' [LawfulMonad m] (x : α) :
    (pure x : WriterT ω m α).run = pure (x, ∅) := rfl


-- @@ L124-125 verbatim
lemma run_bind' [LawfulMonad m] (x : WriterT ω m α) (f : α → WriterT ω m β) :
    (x >>= f).run = x.run >>= fun (a, w₁) => Prod.map id (w₁ ++ ·) <$> (f a).run := rfl


-- @@ L127-127 verbatim
lemma run_map' (x : WriterT ω m α) (f : α → β) : (f <$> x).run = Prod.map f id <$> x.run := rfl


-- @@ L129-132 verbatim
/-- `Prod.fst <$> WriterT.run` preserves `pure` (Append flavour). -/
lemma fst_map_run_pure' [LawfulMonad m] (x : α) :
    Prod.fst <$> ((pure x : WriterT ω m α).run) = pure x := by
  simp


-- @@ L134-140 verbatim
/-- `Prod.fst <$> WriterT.run` preserves `bind` (Append flavour) — i.e. it is a
monad morphism `WriterT ω m → m`. -/
lemma fst_map_run_bind' [LawfulMonad m] (b : WriterT ω m α) (f : α → WriterT ω m β) :
    Prod.fst <$> (b >>= f).run =
      (Prod.fst <$> b.run) >>= fun x => Prod.fst <$> (f x).run := by
  simp only [WriterT.run_bind', map_bind, Functor.map_map]
  exact (bind_map_left (m := m) Prod.fst b.run (fun x => Prod.fst <$> (f x).run)).symm


-- @@ L142-142 verbatim
end append


-- @@ L144-157 verbatim
end basic

-- @[simp]
-- lemma run_fail [AlternativeMonad m] [LawfulAlternative m] :
--     (failure : WriterT ω m α).run = Failure.fail := by
--   simp [failureOfLift_eq_lift_fail, WriterT.liftM_def]

-- /-- The naturally induced `Failure` on `WriterT` is lawful. -/
-- instance [Monad m] [LawfulMonad m] [Failure m] [LawfulFailure m] :
--     LawfulFailure (WriterT ω m) where
--   fail_bind' {α β} f := by
--     show WriterT.mk _ = WriterT.mk _
--     simp [monadLift_def, map_eq_bind_pure_comp, WriterT.mk, bind_assoc,
--       failureOfLift_eq_lift_fail, liftM_def]


-- @@ L159-159 verbatim
section fail


-- @@ L161-161 verbatim
variable {m : Type u → Type v} [AlternativeMonad m] {ω : Type u} {α β γ : Type u}


-- @@ L163-166 verbatim
@[always_inline, inline]
protected def orElse {α : Type u} (x₁ : WriterT ω m α)
    (x₂ : Unit → WriterT ω m α) : WriterT ω m α :=
  WriterT.mk (x₁.run <|> (x₂ ()).run)


-- @@ L168-169 verbatim
@[always_inline, inline]
protected def failure {α : Type u} : WriterT ω m α := WriterT.mk failure


-- @@ L171-173 verbatim
instance [Monoid ω] : AlternativeMonad (WriterT ω m) where
  failure := WriterT.failure
  orElse  := WriterT.orElse


-- @@ L175-176 verbatim
@[simp]
lemma run_failure [Monoid ω] {α : Type u} : (failure : WriterT ω m α).run = failure := rfl


-- @@ L178-182 verbatim
instance [Monoid ω] [LawfulMonad m] : LawfulMonadLift m (WriterT ω m) where
  monadLift_pure x := map_pure (·, 1) x
  monadLift_bind {_ _} _ _ := by
    ext
    simp [MonadLift.monadLift]


-- @@ L184-184 verbatim
end fail


-- @@ L186-186 verbatim
end WriterT


-- @@ L188-188 verbatim
/-! ## AddWriterT: Additive Writer Monad Transformer -/


-- @@ L190-196 verbatim
/-- Writer monad transformer with additive cost accumulation.
Defined as `WriterT (Multiplicative ω) M`, which uses `Monoid (Multiplicative ω)`
(derived from `AddMonoid ω`) so that `tell` accumulates via `+` with identity `0`.

The types `Multiplicative ω` and `ω` are definitionally equal (`Multiplicative` is a plain
`def`, not a `structure`), so no runtime wrapping occurs. -/
abbrev AddWriterT (ω : Type u) (M : Type u → Type v) := WriterT (Multiplicative ω) M


-- @@ L198-198 verbatim
namespace AddWriterT


-- @@ L200-200 verbatim
variable {ω : Type u} {M : Type u → Type v} [Monad M] {α : Type u}


-- @@ L202-204 verbatim
/-- Forget the additive cost log and keep only the outputs of an `AddWriterT` computation. -/
def outputs (oa : AddWriterT ω M α) : M α :=
  Prod.fst <$> oa.run


-- @@ L206-208 verbatim
/-- Observe only the accumulated additive cost of an `AddWriterT` computation. -/
def costs (oa : AddWriterT ω M α) : M ω :=
  (fun z => Multiplicative.toAdd z.2) <$> oa.run


-- @@ L210-212 verbatim
/-- Record an additive cost `w` in the writer log. -/
def addTell [AddMonoid ω] (w : ω) : AddWriterT ω M PUnit :=
  tell (Multiplicative.ofAdd w)


-- @@ L214-216 verbatim
@[simp]
lemma outputs_def (oa : AddWriterT ω M α) :
    oa.outputs = Prod.fst <$> oa.run := rfl


-- @@ L218-220 verbatim
@[simp]
lemma costs_def (oa : AddWriterT ω M α) :
    oa.costs = (fun z => Multiplicative.toAdd z.2) <$> oa.run := rfl


-- @@ L222-224 verbatim
@[simp]
lemma run_addTell [AddMonoid ω] (w : ω) :
    (addTell (M := M) w).run = pure (⟨⟩, Multiplicative.ofAdd w) := rfl


-- @@ L226-228 verbatim
lemma outputs_addTell [AddMonoid ω] [LawfulMonad M] (w : ω) :
    (addTell (M := M) w).outputs = pure ⟨⟩ := by
  simp [outputs, addTell]


-- @@ L230-232 verbatim
lemma costs_addTell [AddMonoid ω] [LawfulMonad M] (w : ω) :
    (addTell (M := M) w).costs = pure w := by
  simp [costs, addTell]


-- @@ L234-234 verbatim
section costPredicates


-- @@ L236-243 verbatim
/-- `CostsAs oa f` means that the accumulated cost of `oa` is determined by its output via the
function `f`.

Concretely, whenever `oa` produces output `a`, the recorded cost is exactly `f a`. This is a
strong structural property: it can fail when the same output can be reached by different execution
paths carrying different costs. -/
def CostsAs (oa : AddWriterT ω M α) (f : α → ω) : Prop :=
  oa.costs = f <$> oa.outputs


-- @@ L245-247 verbatim
/-- `HasCost oa w` means that every execution path of `oa` incurs the constant cost `w`. -/
def HasCost (oa : AddWriterT ω M α) (w : ω) : Prop :=
  oa.CostsAs (fun _ ↦ w)


-- @@ L249-256 verbatim
/-- `OutputCostAtMost oa w` means that `oa` admits an output-indexed cost description bounded above
by the constant `w`.

Concretely, there is some function `f : α → ω` such that every execution producing output `a`
accumulates cost `f a`, and each such `f a` is at most `w`. This is stronger than a merely
pathwise upper bound when the same output can be reached with different costs. -/
def OutputCostAtMost [Preorder ω] (oa : AddWriterT ω M α) (w : ω) : Prop :=
  ∃ f : α → ω, oa.CostsAs f ∧ ∀ a, f a ≤ w


-- @@ L258-264 verbatim
/-- `OutputCostAtLeast oa w` means that `oa` admits an output-indexed cost description bounded
below by the constant `w`.

As with [`AddWriterT.OutputCostAtMost`], this packages a cost function determined by the final
output, not just an arbitrary pathwise lower bound. -/
def OutputCostAtLeast [Preorder ω] (oa : AddWriterT ω M α) (w : ω) : Prop :=
  ∃ f : α → ω, oa.CostsAs f ∧ ∀ a, w ≤ f a


-- @@ L266-272 verbatim
/-- `Cost[ oa ] = w` means that the `AddWriterT` computation `oa` incurs the same additive cost
`w` on every execution path.

This is notation for [`AddWriterT.HasCost`]. It is intended for theorem statements where the
constant-cost reading is more natural than the underlying output-indexed formulation
[`AddWriterT.CostsAs`]. -/
syntax:max "Cost[ " term " ]" " = " term:50 : term


-- @@ L274-275 expanded
macro_rules
  | `(AddWriterT.HasCost $oa $w) => `(AddWriterT.HasCost $oa $w)


-- @@ L277-281 verbatim
/-- `OutputCost[ oa ] ≤ w` means that `oa` admits an output-indexed additive-cost bound by `w`.

This is notation for [`AddWriterT.OutputCostAtMost`]. It is best used when cost is already known
to be determined by the final output, or when that stronger formulation is useful in a proof. -/
syntax:max "OutputCost[ " term " ]" " ≤ " term:50 : term


-- @@ L283-284 expanded
macro_rules
  | `(AddWriterT.OutputCostAtMost $oa $w) => `(AddWriterT.OutputCostAtMost $oa $w)


-- @@ L286-291 verbatim
/-- `OutputCost[ oa ] ≥ w` means that `oa` admits an output-indexed additive-cost lower bound by
`w`.

This is notation for [`AddWriterT.OutputCostAtLeast`]. As with [`OutputCost[ oa ] ≤ w`], it is
formulated in terms of an output-indexed cost witness rather than arbitrary execution paths. -/
syntax:max "OutputCost[ " term " ]" " ≥ " term:50 : term


-- @@ L293-294 expanded
macro_rules
  | `(AddWriterT.OutputCostAtLeast $oa $w) => `(AddWriterT.OutputCostAtLeast $oa $w)


-- @@ L296-299 verbatim
@[simp]
lemma costsAs_iff (oa : AddWriterT ω M α) (f : α → ω) :
    oa.CostsAs f ↔ oa.costs = f <$> oa.outputs :=
  Iff.rfl


-- @@ L301-304 expanded
@[simp]
lemma hasCost_iff (oa : AddWriterT ω M α) (w : ω) :
    (AddWriterT.HasCost oa w) ↔ oa.costs = (fun _ ↦ w) <$> oa.outputs :=
  Iff.rfl


-- @@ L306-309 expanded
@[simp]
lemma outputCostAtMost_iff [Preorder ω] (oa : AddWriterT ω M α) (w : ω) :
    (AddWriterT.OutputCostAtMost oa w) ↔ ∃ f : α → ω, oa.CostsAs f ∧ ∀ a, f a ≤ w :=
  Iff.rfl


-- @@ L311-314 expanded
@[simp]
lemma outputCostAtLeast_iff [Preorder ω] (oa : AddWriterT ω M α) (w : ω) :
    (AddWriterT.OutputCostAtLeast oa w) ↔ ∃ f : α → ω, oa.CostsAs f ∧ ∀ a, w ≤ f a :=
  Iff.rfl


-- @@ L316-319 expanded
lemma outputCostAtMost_of_hasCost [Preorder ω] {oa : AddWriterT ω M α} {w b : ω}
    (h : AddWriterT.HasCost oa w) (hwb : w ≤ b) : AddWriterT.OutputCostAtMost oa b :=
  by
  refine ⟨fun _ ↦ w, ?_, fun _ ↦ hwb⟩
  exact h


-- @@ L321-324 expanded
lemma outputCostAtLeast_of_hasCost [Preorder ω] {oa : AddWriterT ω M α} {w b : ω}
    (h : AddWriterT.HasCost oa w) (hbw : b ≤ w) : AddWriterT.OutputCostAtLeast oa b :=
  by
  refine ⟨fun _ ↦ w, ?_, fun _ ↦ hbw⟩
  exact h


-- @@ L326-326 verbatim
end costPredicates


-- @@ L328-328 verbatim
end AddWriterT
