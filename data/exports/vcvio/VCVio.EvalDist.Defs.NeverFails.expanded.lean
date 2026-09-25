/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module

public import VCVio.EvalDist.Defs.AlternativeMonad
public import VCVio.EvalDist.Monad.Seq


-- @@ L12-29 verbatim
/-!
# Computations that Never Fail

This file defines a predicate-as-typeclass stating that a probabilistic computation never
produces failure mass, together with lemmas for how the property behaves under common
monadic combinators.

Given a `MonadLiftT m SPMF` instance and a computation `mx : m α` in that monad,
`NeverFail mx` means
that `Pr[⊥ | mx] = 0`, i.e. that the computation never fails.

Defined as a typeclass to allow it to be synthesized automatically in certain cases.
However we don't include any instances for `bind` as this blows up the search space.
Instances involving `bind` should be added manually as needed.

The existence of a `MonadLiftT m PMF` instance implies that `NeverFail mx` holds for any computation
in the monad, since the `PMF` doesn't allow any probability of failing.
-/


-- @@ L31-31 verbatim
@[expose] public section


-- @@ L33-33 verbatim
universe u v w


-- @@ L35-35 verbatim
variable {α β γ : Type u} {m : Type u → Type v} [Monad m]


-- @@ L37-51 expanded
/-- `NeverFail mx` states that the computation `mx : m α` has zero probability of failure,
equivalently the mass of `(evalSPMF mx)` at `none` is `0`.

Formally: `NeverFail mx` iff `Pr[⊥ | mx] = 0`.

Remarks:
- This class is a predicate (Prop-valued). It does not add data.
- Use the lemmas in this file (e.g. `bind_of_mem_support`) to transport the property through
  monadic structure. We intentionally avoid a `bind` instance, as the natural condition depends
  on the support of the left-hand side.
-/
class NeverFail {α : Type u} {m : Type u → Type v} [Monad m] [MonadLiftT m SPMF] (mx : m α) :
    Prop where mk ::
  probFailure_eq_zero : probFailure mx = 0


-- @@ L53-53 verbatim
export NeverFail (probFailure_eq_zero)


-- @@ L55-55 verbatim
attribute [simp] probFailure_eq_zero

-- @@ L56-56 verbatim
attribute [aesop safe apply] NeverFail.mk


-- @@ L58-61 expanded
/-- Version of `probFailure_eq_zero` that avoids typeclass search. -/
lemma probFailure_eq_zero' [MonadLiftT m SPMF] {mx : m α} (h : NeverFail mx) : probFailure mx = 0 :=
  NeverFail.probFailure_eq_zero


-- @@ L63-65 verbatim
/-- A computation in a monad with a total `PMF` lift can't fail. -/
instance [MonadLiftT m PMF] [LawfulMonadLiftT m PMF] (mx : m α) : NeverFail mx where
  probFailure_eq_zero := probFailure_of_liftM_PMF mx


-- @@ L67-67 verbatim
section neverFail_lemmas


-- @@ L69-69 verbatim
variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]


-- @@ L71-74 expanded
omit [LawfulMonadLiftT m SPMF] in
@[grind =]
lemma neverFail_iff (mx : m α) : NeverFail mx ↔ probFailure mx = 0 :=
  ⟨by aesop, NeverFail.mk⟩


-- @@ L76-80 verbatim
@[simp, grind =]
lemma neverFail_bind_iff [MonadLiftT m SetM] [EvalDistCompatible m]
    (mx : m α) (my : α → m β) :
    NeverFail (mx >>= my) ↔ NeverFail mx ∧ ∀ x ∈ support mx, NeverFail (my x) := by
  simp [neverFail_iff, probFailure_bind_eq_add_tsum_support, add_eq_zero]


-- @@ L82-85 verbatim
@[simp, grind =]
lemma neverFail_map_iff [LawfulMonad m] (mx : m α) (f : α → β) :
    NeverFail (f <$> mx) ↔ NeverFail mx := by
  grind [= map_eq_bind_pure_comp]


-- @@ L87-96 verbatim
@[simp]
lemma neverFail_seq_iff [LawfulMonad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    (mf : m (α → β)) (mx : m α) :
    NeverFail (mf <*> mx) ↔ NeverFail mf ∧ NeverFail mx := by
  simp only [seq_eq_bind_map, neverFail_bind_iff, neverFail_map_iff]
  refine ⟨fun ⟨hf, h⟩ => ⟨hf, ?_⟩, fun ⟨hf, hx⟩ => ⟨hf, fun _ _ => hx⟩⟩
  have hne : (support mf).Nonempty := by
    simp [Set.nonempty_iff_ne_empty, ← probFailure_eq_one_iff]
  exact h _ hne.choose_spec


-- @@ L98-103 verbatim
@[simp]
lemma not_neverFail_failure {m : Type u → Type v} [AlternativeMonad m]
    [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    [MonadLiftT m SetM] [EvalDistCompatible m] [HasEvalSet.LawfulFailure m] :
    ¬ NeverFail (failure : m α) := by
  simp [neverFail_iff]


-- @@ L105-105 verbatim
end neverFail_lemmas


-- @@ L107-107 verbatim
namespace NeverFail


-- @@ L109-109 verbatim
variable [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]


-- @@ L111-113 expanded
omit [LawfulMonadLiftT m SPMF] in
lemma of_probFailure_eq_zero (mx : m α) (h : probFailure mx = 0) : NeverFail mx :=
  { probFailure_eq_zero := h }


-- @@ L115-121 verbatim
/--
If `mx` is a pure return, it never fails.
This follows since `evalSPMF pure x` is the Dirac distribution on `some x`.
-/
@[simp, grind .]
instance instPure {x} : NeverFail (pure x : m α) where
  probFailure_eq_zero := by simp [probFailure_def]


-- @@ L123-139 verbatim
/--
Precise bind lemma: if `mx` never fails and for all `x` in the support of `mx` the continuation
`my x` never fails, then the whole bind never fails.

Sketch: using `evalSPMF_bind` and the identity

  `Pr[⊥ | mx >>= my] = Pr[⊥ | mx] + ∑ x, Pr[= x | mx] * Pr[⊥ | my x]`,

the first term vanishes by `NeverFail mx`, while for `x ∉ support mx` the coefficient
`Pr[= x | mx]` is `0`, and for `x ∈ support mx` the second factor vanishes by hypothesis.
Hence the sum is `0`.
-/
lemma bind_of_mem_support [MonadLiftT m SetM] [EvalDistCompatible m]
    {mx : m α} {my : α → m β}
    [hx : NeverFail mx] (hy : ∀ x ∈ support mx, NeverFail (my x)) :
    NeverFail (mx >>= my) where
  probFailure_eq_zero := ((neverFail_bind_iff mx my).mpr ⟨hx, hy⟩).probFailure_eq_zero


-- @@ L141-151 verbatim
/--
Weak bind lemma: if the right-hand side never fails for every possible input (`∀ x`),
then the bind never fails.

This is a convenience corollary of `bind_of_mem_support`; it is often easy to apply when
`my` is uniform in its input (e.g. ignores it) or is known to be never-failing globally.
-/
lemma bind_of_forall [MonadLiftT m SetM] [EvalDistCompatible m]
    {mx : m α} {my : α → m β}
    [hx : NeverFail mx] [hy : ∀ x, NeverFail (my x)] :
    NeverFail (mx >>= my) := bind_of_mem_support (hx := hx) (fun x _ => hy x)


-- @@ L153-160 verbatim
/--
Mapping a value through a total function preserves `NeverFail`.
-/
@[grind .]
instance instMap [LawfulMonad m] [MonadLiftT m SetM] [EvalDistCompatible m]
    {mx : m α} [h : NeverFail mx] (f : α → β) :
    NeverFail (f <$> mx) := by
  simp only [monad_norm, bind_of_forall, Function.comp_def]


-- @@ L162-168 verbatim
/-- If both the function computation and the argument computation never fail,
then their applicative sequencing also never fails. -/
@[simp, grind .]
instance instSeq [LawfulMonad m] [MonadLiftT m SetM] [EvalDistCompatible m]
    {mf : m (α → β)} {mx : m α}
    [hf : NeverFail mf] [hx : NeverFail mx] :
    NeverFail (mf <*> mx) := by aesop


-- @@ L170-175 verbatim
/-- If `mx` and `my` never fail, then `mx <* my` never fails. -/
@[simp, grind .]
instance instSeqLeft [LawfulMonad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    {mx : m α} {my : m β}
    [hx : NeverFail mx] [hy : NeverFail my] : NeverFail (mx <* my) := by aesop


-- @@ L177-182 verbatim
/-- If `mx` and `my` never fail, then `mx *> my` never fails. -/
@[simp, grind .]
instance instSeqRight [LawfulMonad m]
    [MonadLiftT m SetM] [LawfulMonadLiftT m SetM] [EvalDistCompatible m]
    {mx : m α} {my : m β}
    [hx : NeverFail mx] [hy : NeverFail my] : NeverFail (mx *> my) := by aesop


-- @@ L184-189 verbatim
example [LawfulMonad m] [MonadLiftT m SetM] [EvalDistCompatible m]
    (mx : m α) [h : NeverFail mx] : NeverFail (do
    let x ← mx
    let y ← mx
    return (x, y)) := by
  grind


-- @@ L191-191 verbatim
end NeverFail
