/-
Vendored from `google-deepmind/debate` (Apache-2.0) via the Lean v4.31.0 port
`LukaHobor/debate` @ `dafe25d`, and migrated in place to Lean v4.33.0. Changed at
the header only; ledger and rationale: `vendor/debate/PROVENANCE.md`.
-/

module

public import AISafetyAtlas.Upstream.Debate.Comp.Oracle
public import AISafetyAtlas.Upstream.Debate.Comp.Defs
public import AISafetyAtlas.Upstream.Debate.Prob.Arith
public import AISafetyAtlas.Upstream.Debate.Prob.Estimate
public import Mathlib.Data.Vector.Basic


-- @@ L15-18 verbatim
@[expose] public section

-- Linters off per `vendor/debate/PROVENANCE.md`; no correctness linter is
-- touched and incomplete proofs stay errors.

-- @@ L19-19 verbatim
set_option linter.unusedSimpArgs false

-- @@ L20-20 verbatim
set_option linter.unusedSectionVars false

-- @@ L21-21 verbatim
set_option linter.unusedVariables false

-- @@ L22-22 verbatim
set_option linter.deprecated false

-- @@ L23-23 verbatim
set_option linter.style.longLine false

-- @@ L24-24 verbatim
set_option linter.unnecessarySeqFocus false

-- @@ L25-25 verbatim
set_option linter.unusedTactic false


-- @@ L27-29 verbatim
/-!
## Basic properties of `Comp`
-/


-- @@ L31-31 verbatim
open Classical

-- @@ L32-32 verbatim
open Prob

-- @@ L33-33 verbatim
open Option (some none)

-- @@ L34-34 verbatim
open scoped Real

-- @@ L35-35 verbatim
noncomputable section


-- @@ L37-37 verbatim
variable {I : Type}

-- @@ L38-38 verbatim
variable {s t u : Set I}

-- @@ L39-39 verbatim
variable {α β γ : Type}


-- @@ L41-41 verbatim
namespace Comp


-- @@ L43-47 verbatim
lemma map_eq (f : α → β) (x : Comp s α) : f <$> x = x >>= (λ x ↦ pure (f x)) := rfl

-- PORT NOTE (v4.31): moved up from below. `simp` no longer unfolds `pure` through the
-- `Monad (Comp s)` instance, so `run`'s match equation never fires unless these fire first.
-- Statements unchanged; only their position in the file moved.

-- @@ L48-50 verbatim
@[simp] lemma run_pure' (x : α) (o : I → Oracle) :
    (Comp.pure' x : Comp s α).run o = pure (x, fun _ ↦ 0) := by
  simp only [Comp.run]


-- @@ L52-54 verbatim
@[simp] lemma run_pure (x : α) (o : I → Oracle) :
    (pure x : Comp s α).run o = pure (x, fun _ ↦ 0) := by
  simp only [pure, Comp.run]


-- @@ L56-72 verbatim
/-- `Comp` is a lawful monad -/
instance : LawfulMonad (Comp s) := LawfulMonad.mk'
  (id_map := by
    intro α f
    simp only [map_eq, id, bind, bind']
    induction' f with x β f g h o m n y f0 f1 h0 h1
    · rfl
    · simp only [bind', sample'.injEq, heq_eq_eq, true_and]; ext y; apply h
    · simp only [bind', h0, h1])
  (pure_bind := by intro α β x f; rfl)
  (bind_assoc := by
    intro α β β f g h
    simp only [bind]
    induction' f with x β f g h o m n y f0 f1 h0 h1
    · rfl
    · simp only [bind', sample'.injEq, heq_eq_eq, true_and, h]
    · simp only [bind', h0, h1])


-- @@ L74-78 verbatim
/-- Running a `pure'` is `pure` -/
@[simp] lemma prob_pure' (x : α) (o : I → Oracle) : (pure' x : Comp s α).prob o = pure x := by
  simp only [prob, run, map_pure]

-- The definition of `Comp.bind` as `simp` lemmas

-- @@ L79-79 verbatim
@[simp] lemma pure'_bind (x : α) (f : α → Comp s β) : (pure' x : Comp s α) >>= f = f x := rfl

-- @@ L80-81 verbatim
@[simp] lemma sample'_bind (f : Prob α) (g : α → Comp s β) (h : β → Comp s γ) :
    sample' f g >>= h = .sample' f fun x ↦ g x >>= h := rfl

-- @@ L82-83 verbatim
@[simp] lemma query'_bind (o : I) (m : o ∈ s) (n : ℕ) (y : List.Vector Bool n) (f0 f1 : Comp s α)
    (g : α → Comp s β) : query' o m n y f0 f1 >>= g = .query' o m n y (f0 >>= g) (f1 >>= g) := rfl


-- @@ L85-88 verbatim
/-- `sample'.prob` is easy -/
@[simp] lemma prob_sample' (f : Prob α) (g : α → Comp s β) (o : I → Oracle) :
    (Comp.sample' f g).prob o = f >>= fun x ↦ (g x).prob o  := by
  simp only [prob, run, map_bind, map_pure, bind_pure]


-- @@ L90-93 verbatim
/-- Coersion of `Prob` matches `run` -/
@[simp] lemma run_coe (f : Prob α) (o : I → Oracle) : (f : Comp s α).prob o = f := by
  have hp : ∀ a : α, (pure a : Comp s α).run o = pure (a, fun _ ↦ 0) := fun _ ↦ rfl
  simp only [prob, run, map_bind, hp, map_pure, bind_pure]


-- @@ L95-97 verbatim
/-- Cost is nonnegative -/
@[simp] lemma cost_nonneg {f : Comp s α} {o : I → Oracle} {i : I} : 0 ≤ f.cost o i := by
  apply exp_nonneg; simp only [ne_eq, Nat.cast_nonneg, implies_true, Prod.forall, forall_const]


-- @@ L99-101 verbatim
/-!
## `Comp.cost` commutes with various things
-/


-- @@ L103-106 verbatim
/-- `pure` is free -/
@[simp] lemma cost_pure (x : α) (o : I → Oracle) (i : I) : (pure x : Comp s α).cost o i = 0 := by
  show (Comp.pure' x : Comp s α).cost o i = 0
  simp only [cost, run, exp_pure, Nat.cast_zero]


-- @@ L108-111 verbatim
/-- `pure'` is free -/
@[simp] lemma cost_pure' (x : α) (o : I → Oracle) (i : I) :
    (Comp.pure' x : Comp s α).cost o i = 0 := by
  simp only [cost, run, exp_pure, Nat.cast_zero]


-- @@ L113-116 verbatim
/-- `sample'` cost's is the expected follow-on cost -/
@[simp] lemma cost_sample (f : Prob α) (g : α → Comp s β) (o : I → Oracle) (i : I) :
    (Comp.sample' f g).cost o i = f.exp (fun x ↦ (g x).cost o i) := by
  simp only [cost, run, exp_bind, Nat.cast_zero]


-- @@ L118-127 verbatim
/-- `query'` costs one query, plus the rest -/
@[simp] lemma cost_query' {i : I} (m : i ∈ s) {n : ℕ} (y : List.Vector Bool n) (f0 f1 : Comp s α)
    (o : I → Oracle) (j : I) :
    (Comp.query' i m n y f0 f1).cost o j =
      (if j = i then 1 else 0) +
      (o i _ y).exp (fun x ↦ if x then f0.cost o j else f1.cost o j) := by
  simp only [cost, run, exp_bind, Nat.cast_zero]
  rw [←exp_const_add]; apply exp_congr; intro x _; induction x;
  repeat simp only [Bool.false_eq_true, reduceIte, ite_false, ite_true, exp_bind, exp_pure, Pi.add_apply, Nat.cast_add,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, exp_add, exp_const, add_comm]


-- @@ L129-131 verbatim
/-- Non-oracle computations are free -/
@[simp] lemma cost_coe (f : Prob α) (o : I → Oracle) (i : I) : (f : Comp s α).cost o i = 0 := by
  simp only [cost_sample, cost_pure, exp_const]


-- @@ L133-141 verbatim
/-- Oracles we can't query don't get queried -/
lemma cost_of_not_mem (f : Comp s α) (o : I → Oracle) {i : I} (is : i ∉ s) : f.cost o i = 0 := by
  induction' f with x β f g h j js n y f0 f1 h0 h1
  · simp only [cost_pure']
  · simp only [cost_sample, h, exp_const]
  · simp only [cost_query', h0, h1, ite_self, exp_const, add_zero]
    by_cases ij : i = j
    · simp only [ij] at is; simp only [js, not_true_eq_false] at is
    · simp only [ij, if_false]


-- @@ L143-149 verbatim
/-- Expanding `query'.run` -/
lemma run_query {i : I} (m : i ∈ s) {n : ℕ} (y : List.Vector Bool n) (f0 f1 : Comp s α)
    (o : I → Oracle) : (Comp.query' i m n y f0 f1).run o = do
      let x ← (o i) n y
      let (z,c) ← if x then f0.run o else f1.run o
      return (z, c + fun j => if j = i then 1 else 0) := by
  rfl


-- @@ L151-167 verbatim
/-- The cost of `f >>= g` is roughly `f.cost + g.cost` -/
lemma cost_bind (f : Comp s α) (g : α → Comp s β) (o : I → Oracle) (i : I) :
    (f >>= g).cost o i = f.cost o i + (f.prob o).exp (fun x ↦ (g x).cost o i) := by
  induction' f with x β f g h j m n y f0 f1 h0 h1
  · simp only [cost_pure', zero_add, prob_pure, exp_pure, prob_pure', bind, bind']
  · simp only [bind, bind'] at h
    simp only [cost_sample, bind, bind', h, exp_add]
    apply congr_arg₂ _ rfl
    simp only [prob_sample', exp_bind]
  · simp only [bind, bind'] at h0 h1
    simp only [cost_query', bind, bind', prob, add_assoc, h0, h1]
    apply congr_arg₂ _ rfl
    simp only [run_query, map_bind, exp_bind, ←exp_add]
    apply exp_congr; intro x _; induction x; repeat {
      simp only [Bool.false_eq_true, reduceIte, ite_true, ite_false, add_right_inj, exp_map, Function.comp_def, exp_bind]
      apply exp_congr; intro _; simp only [ne_eq, exp_pure, implies_true]
    }


-- @@ L169-172 verbatim
/-- Map doesn't change `cost` -/
@[simp] lemma cost_map (f : α → β) (g : Comp s α) (o : I → Oracle) (i : I) :
    (f <$> g).cost o i = g.cost o i := by
  simp only [map_eq, cost_bind, cost_pure, exp_const, add_zero]


-- @@ L174-180 verbatim
/-- If an oracle isn't allowed, its cost is zero -/
lemma cost_eq_zero {f : Comp s α} {i : I} (m : i ∉ s) (o : I → Oracle) : f.cost o i = 0 := by
  induction' f with x β f g h j mj n y f0 f1 h0 h1
  · simp only [cost_pure']
  · simp only [cost_sample, h, exp_const]
  · simp only [cost_query', h0, h1, ite_self, exp_const, add_zero, ite_eq_right_iff, one_ne_zero]
    intro e; rw [e] at m; exact m mj


-- @@ L182-188 verbatim
/-- `count` multiplies cost by `n` -/
@[simp] lemma cost_count (f : Comp s Bool) (n : ℕ) (o : I → Oracle) (i : I) :
    (count f n).cost o i = n * (f.cost o i) := by
  induction' n with n h
  · simp only [Nat.zero_eq, count_zero, cost_pure, Nat.cast_zero, zero_mul]
  · simp only [count, add_comm, cost_bind, h, cost_pure, exp_const, add_zero, Nat.cast_succ,
      add_mul, one_mul]


-- @@ L190-193 verbatim
/-- `estimate` multiplies cost by `n` -/
@[simp] lemma cost_estimate (f : Comp s Bool) (n : ℕ) (o : I → Oracle) (i : I) :
    (estimate f n).cost o i = n * (f.cost o i) := by
  simp only [estimate, cost_map, cost_count]


-- @@ L195-198 verbatim
/-- `query` makes one query -/
@[simp] lemma cost_query (i : I) {n : ℕ} (y : List.Vector Bool n) (o : I → Oracle) :
    (query i y).cost o i = 1 := by
  simp only [Bool.false_eq_true, reduceIte, query, cost_query', ite_true, cost_pure, ite_self, exp_const, add_zero]


-- @@ L200-202 verbatim
/-!
## `Comp.run` commutes with various things
-/


-- @@ L204-217 verbatim
@[simp] lemma run_bind (f : Comp s α) (g : α → Comp s β) (o : I → Oracle) :
    (f >>= g).run o = f.run o >>= fun (x,c) ↦ (fun (y,c') ↦ (y, c + c')) <$> (g x).run o := by
  induction' f with x β f g' h j m n y f0 f1 h0 h1
  · simp only [pure'_bind, run_pure', Pi.add_def, pure_bind, zero_add, Prod.mk.eta, id_map']
  · have e : ∀ x, bind' (g' x) g = g' x >>= g := fun _ ↦ rfl
    have e2 : (sample' f g' : Comp s _) >>= g = sample' f (fun y ↦ g' y >>= g) := rfl
    simp only [e2, run, bind_assoc, e, h]
  · have e : ∀ h, bind' h g = h >>= g := fun _ ↦ rfl
    have e2 : (query' j m n y f0 f1 : Comp s _) >>= g = query' j m n y (f0 >>= g) (f1 >>= g) := rfl
    simp only [e2, run, e, h0, bind_assoc, h1, Prob.map_eq]
    refine congr_arg₂ _ rfl ?_
    funext b
    induction b
    repeat simp only [Bool.false_eq_true, reduceIte, ite_false, ite_true, bind_assoc, pure_bind, Pi.add_def, add_comm, add_assoc]


-- @@ L219-225 verbatim
@[simp] lemma run_allow (f : Comp s α) (st : s ⊆ t) (o : I → Oracle) :
    (f.allow st).run o = f.run o := by
  induction' f with x β f g h j _ n y f0 f1 h0 h1
  · simp only [allow, run_pure, run_pure']
  · have e : ((sample' f g).allow st : Comp t α) = sample' f (fun x ↦ (g x).allow st) := rfl
    simp only [e, run, h]
  · simp only [allow, run, h0, h1]


-- @@ L227-228 verbatim
@[simp] lemma run_allow_all (f : Comp s α) (o : I → Oracle) : f.allow_all.run o = f.run o := by
  apply run_allow

 
-- @@ L230-232 verbatim
/-!
## `Comp.prob` commutes with various things
-/


-- @@ L234-235 verbatim
@[simp] lemma prob_pure (x : α) (o : I → Oracle) : (pure x : Comp s α).prob o = pure x := by
  simp only [pure, prob_pure']


-- @@ L237-242 verbatim
@[simp] lemma prob_query' (i : I) (m : i ∈ s) (n : ℕ) (y : List.Vector Bool n) (f0 f1 : Comp s α)
    (o : I → Oracle) :
    (query' i m n y f0 f1).prob o = (do if ←o i n y then f0.prob o else f1.prob o) := by
  simp only [prob, Prob.map_eq, run, bind_assoc]
  apply congr_arg₂ _ rfl; funext y; induction y
  repeat simp only [Bool.false_eq_true, reduceIte, ite_false, ite_true, bind_assoc, pure_bind]


-- @@ L244-248 verbatim
@[simp] lemma prob_query (i : I) {n : ℕ} (y : List.Vector Bool n) (o : I → Oracle) :
    (query i y).prob o = o i n y := by
  have e : ∀ y : Bool, (if y = true then pure true else pure false) = (pure y : Prob Bool) := by
    intro y; induction y; simp only [Bool.false_eq_true, reduceIte, ite_false]; simp only [ite_true]
  simp only [query, prob_query', prob_pure, e, bind_pure]


-- @@ L250-257 verbatim
@[simp] lemma prob_bind (f : Comp s α) (g : α → Comp s β) (o : I → Oracle) :
    (f >>= g).prob o = f.prob o >>= fun x ↦ (g x).prob o := by
  induction' f with x β f g h j m n y f0 f1 h0 h1
  · simp only [pure'_bind, prob_pure', pure_bind]
  · simp only [sample'_bind, prob_sample', h, bind_assoc]
  · simp only [query'_bind, prob_query', h0, h1, bind_assoc]
    apply congr_arg₂ _ rfl; funext y; induction y
    repeat simp only [Bool.false_eq_true, reduceIte, ite_false, ite_true]


-- @@ L259-261 verbatim
@[simp] lemma prob_map (f : α → β) (g : Comp s α) (o : I → Oracle) :
    (f <$> g).prob o = f <$> g.prob o := by
  simp only [Comp.map_eq, prob_bind, prob_pure, Prob.map_eq]


-- @@ L263-267 verbatim
@[simp] lemma prob_count (f : Comp s Bool) (n : ℕ) (o : I → Oracle) :
    (count f n).prob o = count (f.prob o) n := by
  induction' n with n h
  · simp only [count, prob_pure]
  · simp only [count, prob_bind, h, prob_pure]


-- @@ L269-271 verbatim
@[simp] lemma prob_estimate (f : Comp s Bool) (n : ℕ) (o : I → Oracle) :
    (estimate f n).prob o = estimate (f.prob o) n := by
  simp only [estimate, prob_map, prob_count]


-- @@ L273-275 verbatim
/-!
## `allow` and `allow_all` don't change `.prob` or `.cost`
-/


-- @@ L277-282 verbatim
@[simp] lemma prob_allow (f : Comp s α) (st : s ⊆ t) (o : I → Oracle) :
    (f.allow st).prob o = f.prob o := by
  induction' f with x β f g h j m n y f0 f1 h0 h1
  · simp only [prob_pure', allow, prob_pure]
  · simp only [allow, sample'_bind, pure_bind, prob_sample', h]
  · simp only [allow, prob_query', h0, h1]


-- @@ L284-286 verbatim
@[simp] lemma prob_allow_all (f : Comp s α) (o : I → Oracle) :
    f.allow_all.prob o = f.prob o := by
  apply prob_allow


-- @@ L288-293 verbatim
@[simp] lemma cost_allow (f : Comp s α) (st : s ⊆ t) (o : I → Oracle) (i : I) :
    (f.allow st).cost o i = f.cost o i := by
  induction' f with x β f g h j m n y f0 f1 h0 h1
  · simp only [allow, cost_pure, cost_pure']
  · simp only [allow, sample'_bind, pure_bind, cost_sample, h]
  · simp only [allow, cost_query', h0, h1]


-- @@ L295-297 verbatim
@[simp] lemma cost_allow_all (f : Comp s α) (o : I → Oracle) (i : I) :
    f.allow_all.cost o i = f.cost o i := by
  apply cost_allow


-- @@ L299-300 verbatim
@[simp] lemma allow_pure (x : α) (st : s ⊆ t) : (pure x : Comp s α).allow st = pure x := by
  rfl


-- @@ L302-303 verbatim
@[simp] lemma allow_all_pure (x : α) : (pure x : Comp s α).allow_all = pure x := by
  simp only [allow_all, allow_pure]


-- @@ L305-311 verbatim
@[simp] lemma allow_bind (f : Comp s α) (g : α → Comp s β) (st : s ⊆ t) :
    (f >>= g).allow st = f.allow st >>= fun x ↦ (g x).allow st := by
  have e : ∀ v, bind' v g = v >>= g := fun _ ↦ rfl
  induction' f with x β u v h j m n y f0 f1 h0 h1
  · simp only [pure'_bind, allow, pure_bind]
  · simp only [allow, e, h, sample'_bind, pure_bind]
  · simp only [allow, e, h0, h1, query'_bind]


-- @@ L313-315 verbatim
@[simp] lemma allow_all_bind (f : Comp s α) (g : α → Comp s β) :
    (f >>= g).allow_all = f.allow_all >>= fun x ↦ (g x).allow_all :=
  allow_bind f g _


-- @@ L317-322 verbatim
@[simp] lemma allow_allow (f : Comp s α) (st : s ⊆ t) (tu : t ⊆ u) :
    (f.allow st).allow tu = f.allow (st.trans tu) := by
  induction' f with x β u v h j m n y f0 f1 h0 h1
  · rfl
  · simp only [allow, bind', h, sample'_bind, pure_bind]
  · simp only [allow, h0, h1]


-- @@ L324-326 verbatim
@[simp] lemma allow_all_allow (f : Comp s α) (st : s ⊆ t) :
    (f.allow st).allow_all = f.allow_all := by
  simp only [allow_all, allow_allow]


-- @@ L328-328 verbatim
end Comp


-- @@ L330-332 verbatim
/-!
### `Comp` tactics
-/


-- @@ L334-337 verbatim
/-- Show `i ∉ s` via `simp` -/
macro "not_mem" : tactic =>
  `(tactic| simp only [reduceCtorEq, Set.mem_singleton_iff, Set.mem_insert_iff, or_self,
    not_false_eq_true, not_false])


-- @@ L339-342 verbatim
/-- Show `s ⊆ t` via `simp` -/
macro "subset" : tactic =>
  `(tactic| simp only [reduceCtorEq, Set.mem_singleton_iff, Set.singleton_subset_iff,
    Set.mem_insert_iff, or_false, false_or, true_or, or_true])


-- @@ L344-350 expanded
/-- Show a cost is zero via `i : I` not being in `s` -/
macro "zero_cost" : tactic =>
  `(tactic|
    focus
      try simp only [Comp.cost_allow_all]
      rw [Comp.cost_eq_zero]
      simp only [reduceCtorEq, Set.mem_singleton_iff, Set.mem_insert_iff, or_self,
        not_false_eq_true, not_false])

