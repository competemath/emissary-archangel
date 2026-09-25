/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import VCVio.OracleComp.HasQuery.Basic
public import PolyFun.PFunctor.Free.Basic


-- @@ L12-15 verbatim
/-!
# Computations with Oracle Access

-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
universe u v w


-- @@ L21-21 verbatim
open OracleSpec


-- @@ L23-29 verbatim
/-- `OracleComp spec α` represents computations with oracle access to oracles in `spec`,
where the final return value has type `α`, represented as a free monad over the `PFunctor`
corresponding to `spec.` -/
@[reducible]
def OracleComp {ι : Type u} (spec : OracleSpec.{u, v} ι) :
    Type w → Type (max u v w) :=
  PFunctor.FreeM spec.toPFunctor


-- @@ L31-31 verbatim
variable {α β γ : Type v} {ι} {spec : OracleSpec.{u, v} ι}


-- @@ L33-33 verbatim
namespace OracleComp


-- @@ L35-35 verbatim
open scoped OracleSpec.PrimitiveQuery


-- @@ L37-43 verbatim
/-- Interpret a raw polynomial free program as an oracle computation.

This is the explicit abstraction boundary for generic PolyFun constructions;
downstream semantics should use this function instead of unfolding
`OracleComp`. -/
@[reducible]
def ofFreeM {α : Type w} (oa : PFunctor.FreeM spec.toPFunctor α) : OracleComp spec α := oa


-- @@ L45-47 verbatim
/-- Expose the polynomial free program underlying an oracle computation. -/
@[reducible]
def toFreeM {α : Type w} (oa : OracleComp spec α) : PFunctor.FreeM spec.toPFunctor α := oa


-- @@ L49-50 verbatim
theorem ofFreeM_toFreeM {α : Type w} (oa : OracleComp spec α) :
    ofFreeM (toFreeM oa) = oa := rfl


-- @@ L52-53 verbatim
theorem toFreeM_ofFreeM {α : Type w} (oa : PFunctor.FreeM spec.toPFunctor α) :
    toFreeM (ofFreeM oa) = oa := rfl


-- @@ L55-63 verbatim
/-- Make one oracle query at input `t`, then continue with `k` on the response.

This is the `PFunctor.FreeM.liftBind` constructor specialized to `OracleComp`;
the `@[match_pattern]` attribute makes it usable both as a term and as a
`match` pattern. -/
@[match_pattern, reducible]
def queryBind {α} (t : spec.Domain) (k : spec.Range t → OracleComp spec α) :
    OracleComp spec α :=
  PFunctor.FreeM.liftBind t k


-- @@ L65-67 verbatim
theorem ofFreeM_pure {α : Type v} (x : α) :
    ofFreeM (PFunctor.FreeM.pure x : PFunctor.FreeM spec.toPFunctor α) =
      (pure x : OracleComp spec α) := rfl


-- @@ L69-73 verbatim
theorem ofFreeM_bind {α β : Type v}
    (oa : PFunctor.FreeM spec.toPFunctor α)
    (next : α → PFunctor.FreeM spec.toPFunctor β) :
    ofFreeM (PFunctor.FreeM.bind oa next) =
      (ofFreeM oa >>= fun x => ofFreeM (next x)) := rfl


-- @@ L75-77 verbatim
theorem ofFreeM_map {α β : Type v}
    (f : α → β) (oa : PFunctor.FreeM spec.toPFunctor α) :
    ofFreeM (PFunctor.FreeM.map f oa) = f <$> ofFreeM oa := rfl


-- @@ L79-82 verbatim
/-- Manually lift an `OracleQuery` to an `OracleComp`. -/
@[reducible]
protected def lift {ι} {spec : OracleSpec ι} {α} (q : OracleQuery spec α) :
    OracleComp spec α := liftM q


-- @@ L84-85 verbatim
protected lemma liftM_def (q : OracleQuery spec α) :
    liftM (n := OracleComp spec) q = PFunctor.FreeM.liftObj q := rfl


-- @@ L87-89 verbatim
@[simp, grind .]
lemma liftM_ne_pure (q : OracleQuery spec α) (x : α) :
    liftM (n := OracleComp spec) q ≠ pure x := PFunctor.FreeM.liftObj_ne_pure q x


-- @@ L91-93 verbatim
@[simp, grind .]
lemma pure_ne_liftM (x : α) (q : OracleQuery spec α) :
    pure x ≠ liftM (n := OracleComp spec) q := PFunctor.FreeM.pure_ne_liftObj q x


-- @@ L95-97 verbatim
@[grind =]
protected lemma liftM_map (q : OracleQuery spec α) (f : α → β) :
    liftM (n := OracleComp spec) (f <$> q) = f <$> liftM q := rfl


-- @@ L99-101 verbatim
/-- `coin` is the computation representing a coin flip, given a coin flipping oracle. -/
@[inline]
def coin : OracleComp coinSpec Bool := coinSpec.query ()


-- @@ L103-104 verbatim
@[grind =, aesop unsafe norm]
lemma coin_def : coin = coinSpec.query () := rfl


-- @@ L106-107 verbatim
protected lemma pure_def (x : α) :
    (pure x : OracleComp spec α) = PFunctor.FreeM.pure x := rfl


-- @@ L109-110 verbatim
protected lemma bind_def (oa : OracleComp spec α) (ob : α → OracleComp spec β) :
    oa >>= ob = PFunctor.FreeM.bind oa ob := rfl


-- @@ L112-126 verbatim
/-- Cases eliminator on `OracleComp` exposing the high-level `pure` /
`queryBind` alternatives. Registered as the default `cases` eliminator so that
`cases oa with | pure x => ... | queryBind t k => ...` works transparently on
top of the free-monad substrate. -/
@[elab_as_elim, cases_eliminator]
def casesOn {α} {motive : OracleComp spec α → Sort*}
    (oa : OracleComp spec α)
    (pure : (x : α) → motive (PFunctor.FreeM.pure x : OracleComp spec α))
    (queryBind : (t : spec.Domain) →
      (k : spec.Range t → OracleComp spec α) →
      motive (OracleComp.queryBind (spec := spec) t k)) :
    motive oa :=
  match oa with
  | .pure x => pure x
  | .queryBind t k => queryBind t k


-- @@ L128-145 verbatim
/-- Structural recursion eliminator on `OracleComp` exposing the high-level
`pure` / `queryBind` alternatives, with an induction hypothesis on every
continuation in the `queryBind` case. Registered as the default `induction`
eliminator so that
`induction oa with | pure x => ... | queryBind t k ih => ...`
works transparently on top of the free-monad substrate. -/
@[elab_as_elim, induction_eliminator]
def recOn {α} {motive : OracleComp spec α → Sort*}
    (oa : OracleComp spec α)
    (pure : (x : α) → motive (PFunctor.FreeM.pure x : OracleComp spec α))
    (queryBind : (t : spec.Domain) →
      (k : spec.Range t → OracleComp spec α) →
      ((u : spec.Range t) → motive (k u)) →
      motive (OracleComp.queryBind (spec := spec) t k)) :
    motive oa :=
  match oa with
  | .pure x => pure x
  | .queryBind t k => queryBind t k (fun u => recOn (k u) pure queryBind)


-- @@ L147-147 verbatim
protected lemma failure_def : (failure : OptionT (OracleComp spec) α) = OptionT.fail := rfl


-- @@ L149-152 verbatim
protected lemma orElse_def (oa oa' : OptionT (OracleComp spec) α) : (oa <|> oa') = OptionT.mk
    (do match ← OptionT.run oa with | some a => pure (some a) | _  => OptionT.run oa') := by
  simp only [HOrElse.hOrElse, OrElse.orElse, Alternative.orElse, OptionT.orElse]
  refine congr_arg OptionT.mk <| bind_congr fun x => by aesop


-- @@ L154-156 verbatim
@[aesop unsafe apply, grind =>]
protected lemma bind_congr' {oa oa' : OracleComp spec α} {ob ob' : α → OracleComp spec β}
    (h : oa = oa') (h' : ∀ x, ob x = ob' x) : oa >>= ob = oa' >>= ob' := h ▸ bind_congr h'


-- @@ L158-162 verbatim
@[simp] -- NOTE: debatable if this should be simp
lemma guard_eq {spec : OracleSpec ι} (p : Prop) [Decidable p] :
    (guard p : OptionT (OracleComp spec) Unit) = if p then pure () else failure := rfl

-- NOTE: This should maybe be a `@[simp]` lemma? `apply_ite` can't be a simp lemma in general.

-- @@ L163-165 verbatim
lemma ite_bind (p : Prop) [Decidable p] (oa oa' : OracleComp spec α)
    (ob : α → OracleComp spec β) : ite p oa oa' >>= ob = ite p (oa >>= ob) (oa' >>= ob) :=
  apply_ite (· >>= ob) p oa oa'


-- @@ L167-180 verbatim
/-- Nicer induction rule for `OracleComp` that uses monad notation.
Allows inductive definitions on computations by considering the two cases:
* `return x` / `pure x` for any `x`
* `do let u ← query i t; oa u` (with inductive results for `oa u`)
See `oracleComp_emptySpec_equiv` for an example of using this in a proof.
If the final result needs to be a `Type` and not a `Prop`, see `OracleComp.construct`. -/
@[elab_as_elim]
protected theorem inductionOn {α} {C : OracleComp spec α → Prop}
    (pure : (a : α) → C (pure a))
    (query_bind : (t : spec.Domain) →
      (oa : spec.Range t → OracleComp spec α) →
        (∀ u, C (oa u)) → C (query t >>= oa))
    (oa : OracleComp spec α) : C oa :=
  PFunctor.FreeM.induction pure query_bind oa


-- @@ L182-194 verbatim
/-- Version of `OracleComp.inductionOn` that includes an `OptionT` in the monad stack
and requires an explicit case to handle `failure`. -/
@[elab_as_elim]
protected theorem inductionOnOptional {α} {C : OptionT (OracleComp spec) α → Prop}
    (pure : (a : α) → C (pure a))
    (query_bind : (t : spec.Domain) →
      (oa : spec.Range t → OptionT (OracleComp spec) α) → (∀ u, C (oa u)) →
      C (query t >>= oa))
    (failure : C failure)
    (oa : OptionT (OracleComp spec) α) : C oa :=
  PFunctor.FreeM.induction
    (fun | some x => pure x | none => failure)
    (fun t => query_bind t) oa


-- @@ L196-202 verbatim
/-- Version of `OracleComp.inductionOn` with the computation at the start. -/
@[elab_as_elim]
protected theorem induction {α} {C : OracleComp spec α → Prop}
    (oa : OracleComp spec α) (pure : (a : α) → C (pure a))
    (query_bind : (t : spec.Domain) →
      (oa : spec.Range t → OracleComp spec α) → (∀ u, C (oa u)) → C (query t >>= oa)) : C oa :=
  PFunctor.FreeM.induction pure query_bind oa


-- @@ L204-214 verbatim
/-- Version of `OracleComp.inductionOnOptional` with the computation at the start. -/
@[elab_as_elim]
protected theorem inductionOptional {α} {C : OptionT (OracleComp spec) α → Prop}
    (oa : OptionT (OracleComp spec) α) (pure : (a : α) → C (pure a))
    (query_bind : (t : spec.Domain) →
      (oa : spec.Range t → OptionT (OracleComp spec) α) → (∀ u, C (oa u)) →
      C (query t >>= oa))
    (failure : C failure) : C oa :=
  PFunctor.FreeM.induction
    (fun | some x => pure x | none => failure)
    query_bind oa


-- @@ L216-216 verbatim
section construct


-- @@ L218-229 verbatim
/-- Version of `construct` with automatic induction on the `query` in when defining the
`query_bind` case. Can be useful with `spec.DecidableEq` and `spec.FiniteRange`.
`mapM`/`simulateQ` is usually preferable to this if the object being constructed is a monad. -/
@[elab_as_elim]
protected def construct {α}
    {C : OracleComp spec α → Type*}
    (pure : (a : α) → C (pure a))
    (query_bind : (t : spec.Domain) →
      (oa : spec.Range t → OracleComp spec α) →
      ((u : spec.Range t) → C (oa u)) → C (query t >>= oa))
    (oa : OracleComp spec α) : C oa :=
  OracleComp.recOn oa pure query_bind


-- @@ L231-236 verbatim
@[simp] lemma construct_pure {α} (x : α)
    {C : OracleComp spec α → Type*} (h_pure : (a : α) → C (pure a))
    (h_query_bind : (t : spec.Domain) →
        (oa : spec.Range t → OracleComp spec α) →
        ((u : spec.Range t) → C (oa u)) → C (query t >>= oa)) :
    OracleComp.construct h_pure h_query_bind (pure x) = h_pure x := rfl


-- @@ L238-245 verbatim
@[simp] lemma construct_query (t : spec.Domain)
    {C : OracleComp spec (spec.Range t) → Type*} (h_pure : (u : spec.Range t) → C (pure u))
    (h_query_bind : (t' : spec.Domain) →
      (oa : spec.Range t' → OracleComp spec (spec.Range t)) →
      ((u : spec.Range t') → C (oa u)) → C (query t' >>= oa)) :
    (OracleComp.construct h_pure h_query_bind
        (query t : OracleComp spec (spec.Range t)) : C (query t)) =
      h_query_bind t pure h_pure := rfl


-- @@ L247-253 verbatim
@[simp] lemma construct_query_bind {α} (t : spec.Domain) (mx : spec.Range t → OracleComp spec α)
    {C : OracleComp spec α → Type*} (h_pure : (a : α) → C (pure a))
    (h_query_bind : (t : spec.Domain) →
        (mx : spec.Range t → OracleComp spec α) →
        ((u : spec.Range t) → C (mx u)) → C (liftM (query t) >>= mx)) :
    OracleComp.construct h_pure h_query_bind (liftM (query t) >>= mx) =
      h_query_bind t mx fun u => OracleComp.construct h_pure h_query_bind (mx u) := rfl


-- @@ L255-255 verbatim
end construct


-- @@ L257-257 verbatim
section noConfusion


-- @@ L259-260 verbatim
variable (x : α) (y : β) (t : spec.Domain) (u : spec.Range t)
  (oa : β → OracleComp spec α) (ou : spec.Range t → OracleComp spec α)


-- @@ L262-265 verbatim
/-- Returns `true` for computations that don't query any oracles or fail, else `false`. -/
def isPure {α : Type _} : OracleComp spec α → Bool
  | .pure _ => true
  | .queryBind _ _ => false


-- @@ L267-267 verbatim
@[simp] lemma isPure_pure : isPure (pure x : OracleComp spec α) = true := rfl

-- @@ L268-268 verbatim
@[simp] lemma isPure_query : isPure (query t : OracleComp spec _) = false := rfl

-- @@ L269-269 verbatim
@[simp] lemma isPure_query_bind : isPure (liftM (OracleSpec.query t) >>= ou) = false := rfl


-- @@ L271-275 verbatim
lemma pure_ne_query :
    (pure u : OracleComp spec _) ≠ query t := by
  intro h
  have h' := congrArg (isPure (spec := spec)) h
  simp at h'

-- @@ L276-278 verbatim
lemma query_ne_pure :
    (query t : OracleComp spec _) ≠ pure u := by
  exact Ne.symm (pure_ne_query (spec := spec) t u)


-- @@ L280-280 verbatim
lemma pure_eq_query_iff_false : pure u = (query t : OracleComp spec _) ↔ False := by simp

-- @@ L281-281 verbatim
lemma query_eq_pure_iff_false : (query t : OracleComp spec _) = pure u ↔ False := by simp


-- @@ L283-283 verbatim
end noConfusion


-- @@ L285-288 verbatim
/-- Given a computation `oa : OracleComp spec α`, construct a value `x : α`,
by assuming each query returns the `default` value given by the `Inhabited` instance. -/
def defaultResult [spec.Inhabited] (oa : OracleComp spec α) : α :=
  PFunctor.FreeM.liftM (m := Id) (fun _ => default) oa


-- @@ L290-295 verbatim
/-- Total number of queries in a computation across all possible execution paths.
Can be a helpful alternative to `sizeOf` when proving recursive calls terminate. -/
def totalQueries [spec.Fintype] {α : Type v} (oa : OracleComp spec α) : ℕ := by
  induction oa using OracleComp.construct with
  | pure x => exact 0
  | query_bind t oa rec_n => exact 1 + ∑ x, rec_n x


-- @@ L297-297 verbatim
section inj


-- @@ L299-301 verbatim
/-- Two `pure` computations are equal iff they return the same value. -/
lemma pure_inj (x y : α) : pure (f := OracleComp spec) x = pure y ↔ x = y :=
  PFunctor.FreeM.pure_inj x y


-- @@ L303-307 verbatim
/-- Binding two computations gives a pure operation iff the first computation is pure
and the second computation does something pure with the result. -/
@[simp] lemma bind_eq_pure_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β) :
    oa >>= ob = pure y ↔ ∃ x : α, oa = pure x ∧ ob x = pure y :=
  PFunctor.FreeM.bind_eq_pure_iff oa ob y


-- @@ L309-313 verbatim
/-- Binding two computations gives a pure operation iff the first computation is pure
and the second computation does something pure with the result. -/
@[simp] lemma pure_eq_bind_iff (oa : OracleComp spec α) (ob : α → OracleComp spec β) (y : β) :
    pure y = oa >>= ob ↔ ∃ x : α, oa = pure x ∧ ob x = pure y :=
  eq_comm.trans (bind_eq_pure_iff oa ob y)


-- @@ L315-315 verbatim
alias ⟨_, bind_eq_pure⟩ := bind_eq_pure_iff

-- @@ L316-316 verbatim
alias ⟨_, pure_eq_bind⟩ := pure_eq_bind_iff


-- @@ L318-318 verbatim
end inj


-- @@ L320-320 verbatim
end OracleComp
