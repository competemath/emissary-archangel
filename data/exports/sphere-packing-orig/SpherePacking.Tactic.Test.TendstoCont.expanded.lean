/-
Copyright (c) 2025 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import SpherePacking.Tactic.TendstoCont
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Order.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic


-- @@ L16-22 verbatim
/-!
# Tests for the `tendsto_cont` tactic

The `#guard_msgs` tests in this file are sensitive to any other diagnostics emitted at the
guarded commands, so this file must keep a style-conformant header (otherwise
`linter.style.header` warnings can leak into the `#guard_msgs` output and fail CI).
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
open Filter Topology


-- @@ L28-30 verbatim
variable {f g k : ℝ → ℝ}

-- Constant function

-- @@ L31-33 verbatim
example : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (nhds 1) := by tendsto_cont

-- Single atom, identity

-- @@ L34-37 verbatim
example (h : Tendsto f atTop (nhds 3)) :
    Tendsto (fun z => f z) atTop (nhds 3) := by tendsto_cont

-- Single atom, scalar multiply

-- @@ L38-41 verbatim
example (h : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => 2 * f z) atTop (nhds 0) := by tendsto_cont

-- Two atoms, sum

-- @@ L42-45 verbatim
example (h₁ : Tendsto f atTop (nhds 1)) (h₂ : Tendsto g atTop (nhds 2)) :
    Tendsto (fun z => f z + g z) atTop (nhds 3) := by tendsto_cont

-- Two atoms, polynomial

-- @@ L46-49 verbatim
example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto g atTop (nhds 1)) :
    Tendsto (fun z => f z ^ 2 + f z * g z + g z ^ 2) atTop (nhds 1) := by tendsto_cont

-- Three atoms, subtraction

-- @@ L50-54 verbatim
example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto g atTop (nhds 1))
    (h₃ : Tendsto k atTop (nhds 1)) :
    Tendsto (fun z => f z + g z - k z) atTop (nhds 0) := by tendsto_cont

-- Unused hypotheses in context don't interfere

-- @@ L55-63 verbatim
example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto g atTop (nhds 1))
    (_h_unrelated : Tendsto f atBot (nhds 5)) :
    Tendsto (fun z => f z * g z) atTop (nhds 0) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Issue 1: Non-last-argument matching (isDefEq-based)
-- ══════════════════════════════════════════════════════════════

-- Atom where bound variable is not the last argument

-- @@ L64-71 verbatim
example (H : ℝ → ℝ → ℝ) (hH : Tendsto (fun z => H z 5) atTop (nhds 3)) :
    Tendsto (fun z => H z 5 + 1) atTop (nhds 4) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Issue 2: Symbolic target limits (ring fallback)
-- ══════════════════════════════════════════════════════════════

-- Commutativity: target says b + a, computed limit is a + b

-- @@ L72-75 verbatim
example (h₁ : Tendsto f atTop (nhds 1)) (h₂ : Tendsto g atTop (nhds 2)) :
    Tendsto (fun z => g z + f z) atTop (nhds 3) := by tendsto_cont

-- Symbolic commutativity: target limit (b + a) differs from computed (a + b)

-- @@ L76-79 verbatim
example {a b : ℝ} (h₁ : Tendsto f atTop (nhds a)) (h₂ : Tendsto g atTop (nhds b)) :
    Tendsto (fun z => f z + g z) atTop (nhds (b + a)) := by tendsto_cont

-- Symbolic associativity: target limit a + (b + c) vs computed order

-- @@ L80-88 verbatim
example {a b c : ℝ} (h₁ : Tendsto f atTop (nhds a)) (h₂ : Tendsto g atTop (nhds b))
    (h₃ : Tendsto k atTop (nhds c)) :
    Tendsto (fun z => f z + g z + k z) atTop (nhds (a + (b + c))) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Issue 3: Duplicate (same limit) hypotheses succeed
-- ══════════════════════════════════════════════════════════════

-- Two hypotheses for same atom with same limit should not error

-- @@ L89-94 verbatim
example (h₁ : Tendsto f atTop (nhds 0)) (_h₂ : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => f z + 1) atTop (nhds 1) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Issue 3: Ambiguity detection (different limits for same atom)
-- ══════════════════════════════════════════════════════════════


-- @@ L96-103 verbatim
/-- error: tendsto_cont: ambiguous limit for atom — found hypotheses with limits `0` and `1` for the same function -/
#guard_msgs(error, drop info) in
example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto f atTop (nhds 1)) :
    Tendsto (fun z => f z + 1) atTop (nhds 1) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Issue 4a: Zero atoms, no candidates for filter
-- ══════════════════════════════════════════════════════════════


-- @@ L105-111 verbatim
/-- error: tendsto_cont: no `Tendsto` hypotheses found for filter `atTop` -/
#guard_msgs(error, drop info) in
example : Tendsto (fun z : ℝ => z + 1) atTop (nhds 0) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Issue 4b: Zero atoms, candidates exist but none matched
-- ══════════════════════════════════════════════════════════════


-- @@ L113-123 verbatim
/-- error: tendsto_cont: body references the bound variable but no candidate matched.
Available candidates: [f] -/
#guard_msgs(error, drop info) in
example (h : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => g z + 1) atTop (nhds 0) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Non-polynomial continuous functions (sin, exp)
-- ══════════════════════════════════════════════════════════════

-- sin of a convergent function

-- @@ L124-127 verbatim
example (h : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => Real.sin (f z)) atTop (nhds 0) := by tendsto_cont

-- exp of a convergent function

-- @@ L128-131 verbatim
example (h : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => Real.exp (f z)) atTop (nhds 1) := by tendsto_cont

-- Mixed: polynomial + sin

-- @@ L132-135 verbatim
example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto g atTop (nhds 1)) :
    Tendsto (fun z => f z ^ 2 + Real.sin (g z)) atTop (nhds (Real.sin 1)) := by tendsto_cont

-- exp * sin composition

-- @@ L136-141 verbatim
example (h : Tendsto f atTop (nhds 0)) :
    Tendsto (fun z => Real.exp (f z) * Real.sin (f z)) atTop (nhds 0) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Complex numbers
-- ══════════════════════════════════════════════════════════════


-- @@ L143-143 verbatim
section Complex

-- @@ L144-144 verbatim
open Complex


-- @@ L146-148 verbatim
variable {fc gc : ℝ → ℂ}

-- Complex: sum

-- @@ L149-152 verbatim
example (h₁ : Tendsto fc atTop (nhds 1)) (h₂ : Tendsto gc atTop (nhds I)) :
    Tendsto (fun z => fc z + gc z) atTop (nhds (1 + I)) := by tendsto_cont

-- Complex: polynomial

-- @@ L153-156 verbatim
example (h₁ : Tendsto fc atTop (nhds 0)) (h₂ : Tendsto gc atTop (nhds 1)) :
    Tendsto (fun z => fc z ^ 2 + fc z * gc z + gc z ^ 2) atTop (nhds 1) := by tendsto_cont

-- Complex: exp

-- @@ L157-160 verbatim
example (h : Tendsto fc atTop (nhds 0)) :
    Tendsto (fun z => Complex.exp (fc z)) atTop (nhds 1) := by tendsto_cont

-- Complex.re composition (pattern from PR #307: continuous_re.tendsto.comp)

-- @@ L161-164 verbatim
example (h : Tendsto fc atTop (nhds 1)) :
    Tendsto (fun z => (fc z).re) atTop (nhds 1) := by tendsto_cont

-- Complex.im composition

-- @@ L165-166 verbatim
example (h : Tendsto fc atTop (nhds I)) :
    Tendsto (fun z => (fc z).im) atTop (nhds 1) := by tendsto_cont


-- @@ L168-175 verbatim
end Complex

-- ══════════════════════════════════════════════════════════════
-- Goal function behind a reducible definition (whnfR needed)
-- ══════════════════════════════════════════════════════════════

-- When the goal function is a reducible definition (abbrev), tendsto_cont
-- should reduce it via whnfR to find the lambda (no `change` or `show` needed).

-- @@ L176-176 verbatim
noncomputable abbrev myExpr (f g : ℝ → ℝ) : ℝ → ℝ := fun z => f z ^ 2 + g z


-- @@ L178-179 verbatim
example (hf : Tendsto f atTop (nhds 1)) (hg : Tendsto g atTop (nhds 2)) :
    Tendsto (myExpr f g) atTop (nhds 3) := by tendsto_cont


-- @@ L181-181 verbatim
noncomputable abbrev myExprMul (f g : ℝ → ℝ) : ℝ → ℝ := fun z => f z * g z


-- @@ L183-188 verbatim
example (hf : Tendsto f atTop (nhds 2)) (hg : Tendsto g atTop (nhds 3)) :
    Tendsto (myExprMul f g) atTop (nhds 6) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- General topological ring
-- ══════════════════════════════════════════════════════════════


-- @@ L190-192 verbatim
section GeneralRing

-- Sum over a general topological ring

-- @@ L193-199 verbatim
example {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
    {α : Type*} {l : Filter α}
    {f g : α → R} {a b : R}
    (h₁ : Tendsto f l (nhds a)) (h₂ : Tendsto g l (nhds b)) :
    Tendsto (fun z => f z + g z) l (nhds (a + b)) := by tendsto_cont

-- Product over a general topological ring

-- @@ L200-206 verbatim
example {R : Type*} [TopologicalSpace R] [Ring R] [IsTopologicalRing R]
    {α : Type*} {l : Filter α}
    {f g : α → R} {a b : R}
    (h₁ : Tendsto f l (nhds a)) (h₂ : Tendsto g l (nhds b)) :
    Tendsto (fun z => f z * g z) l (nhds (a * b)) := by tendsto_cont

-- Polynomial over a commutative topological ring (ring fallback)

-- @@ L207-211 verbatim
example {R : Type*} [TopologicalSpace R] [CommRing R] [IsTopologicalRing R]
    {α : Type*} {l : Filter α}
    {f g : α → R} {a b : R}
    (h₁ : Tendsto f l (nhds a)) (h₂ : Tendsto g l (nhds b)) :
    Tendsto (fun z => f z * g z + g z * f z) l (nhds (2 * a * b)) := by tendsto_cont


-- @@ L213-219 verbatim
end GeneralRing

-- ══════════════════════════════════════════════════════════════
-- Non-atTop filters (nhds 0, etc.)
-- ══════════════════════════════════════════════════════════════

-- Limit at nhds 0 (not atTop/atBot)

-- @@ L220-223 verbatim
example (h : Tendsto f (nhds 0) (nhds 1)) :
    Tendsto (fun x => 2 * f x) (nhds 0) (nhds 2) := by tendsto_cont

-- Two hypotheses with different filters: picks the right one

-- @@ L224-231 verbatim
example (_h₁ : Tendsto f (nhds 0) (nhds 1)) (h₂ : Tendsto f atTop (nhds 0)) :
    Tendsto (fun x => 2 * f x) atTop (nhds 0) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Composition: f(g(x)) as a single atom
-- ══════════════════════════════════════════════════════════════

-- Hypothesis about f(g(x)) treated as one atom

-- @@ L232-239 verbatim
example (h : Tendsto (fun x => f (g x)) (nhds 0) (nhds 1)) :
    Tendsto (fun x => 2 * f (g x)) (nhds 0) (nhds 2) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Composition via continuity: g(f(x)) where g is continuous
-- ══════════════════════════════════════════════════════════════

-- g continuous + f → 1 at 0 gives g(f(x)) → g(1) at 0

-- @@ L240-243 verbatim
example (hf : Tendsto f (nhds 0) (nhds 1)) (hg : Continuous g) :
    Tendsto (fun x => g (f x)) (nhds 0) (nhds (g 1)) := by tendsto_cont

-- Without continuity hypothesis, fun_prop can't prove ContinuousAt g

-- @@ L244-256 verbatim
/--
error: tendsto_cont: `fun_prop` failed:
`fun_prop` was unable to prove `ContinuousAt (fun p ↦ g p) 1`

Issues:
  No theorems found for `g` in order to prove `ContinuousAt (fun p ↦ g p) 1`
goal: ContinuousAt (fun p ↦ g p) 1
-/
#guard_msgs(error, drop info) in
example (hf : Tendsto f (nhds 0) (nhds 1)) :
    Tendsto (fun x => g (f x)) (nhds 0) (nhds (g 1)) := by tendsto_cont

-- But known continuous functions (Real.sin, etc.) work fine via fun_prop

-- @@ L257-262 verbatim
example (hf : Tendsto f (nhds 0) (nhds 1)) :
    Tendsto (fun x => Real.sin (f x)) (nhds 0) (nhds (Real.sin 1)) := by tendsto_cont

-- ══════════════════════════════════════════════════════════════
-- Inline argument syntax: tendsto_cont [h₁, h₂]
-- ══════════════════════════════════════════════════════════════


-- @@ L264-264 verbatim
section InlineArgs


-- @@ L266-266 verbatim
private def inlineFn : ℝ → ℝ := fun _ => 3


-- @@ L268-270 verbatim
private theorem inlineFn_tendsto : Tendsto inlineFn atTop (nhds 3) := by
  change Tendsto (fun _ : ℝ => (3 : ℝ)) atTop (nhds 3)
  exact tendsto_const_nhds


-- @@ L272-272 verbatim
private def inlineFn₂ : ℝ → ℝ := fun _ => 2


-- @@ L274-278 verbatim
private theorem inlineFn₂_tendsto : Tendsto inlineFn₂ atTop (nhds 2) := by
  change Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (nhds 2)
  exact tendsto_const_nhds

-- Without inline arg, no candidate exists

-- @@ L279-284 verbatim
/-- error: tendsto_cont: no `Tendsto` hypotheses found for filter `atTop` -/
#guard_msgs(error, drop info) in
example : Tendsto (fun z => inlineFn z + 1) atTop (nhds 4) := by
  tendsto_cont

-- Single inline argument makes it work

-- @@ L285-288 verbatim
example : Tendsto (fun z => inlineFn z + 1) atTop (nhds 4) := by
  tendsto_cont [inlineFn_tendsto]

-- Multiple inline arguments

-- @@ L289-292 verbatim
example : Tendsto (fun z => inlineFn z + inlineFn₂ z) atTop (nhds 5) := by
  tendsto_cont [inlineFn_tendsto, inlineFn₂_tendsto]

-- Redundant inline arg (already a local hypothesis) triggers warning

-- @@ L293-298 verbatim
/-- warning: tendsto_cont: inline argument `h` is redundant — it is already available as a local hypothesis -/
#guard_msgs(warning, drop info) in
example (h : Tendsto f atTop (nhds 3)) :
    Tendsto (fun z => f z + 1) atTop (nhds 4) := by tendsto_cont [h]

-- Inline arg shadows conflicting local hypothesis — no ambiguity error, no warning

-- @@ L299-303 verbatim
example (_h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto f atTop (nhds 1)) :
    Tendsto (fun z => f z + 1) atTop (nhds 2) := by tendsto_cont [h₂]

-- Inline FVar disambiguates against non-local inline arg — no redundancy warning
-- (removing h would change behavior: inlineFn_tendsto would be used instead)

-- @@ L304-308 verbatim
/-- error: tendsto_cont: ambiguous limit for atom — found hypotheses with limits `0` and `3` for the same function -/
#guard_msgs(error, drop info) in
example (h : Tendsto inlineFn atTop (nhds 0)) :
    Tendsto (fun z => inlineFn z + 1) atTop (nhds 4) := by
  tendsto_cont [h, inlineFn_tendsto]


-- @@ L310-314 verbatim
end InlineArgs

-- ══════════════════════════════════════════════════════════════
-- @[tendsto_cont] attribute
-- ══════════════════════════════════════════════════════════════


-- @@ L316-316 verbatim
section AttrRegistration


-- @@ L318-318 verbatim
private def attrFn : ℝ → ℝ := fun _ => 0


-- @@ L320-324 verbatim
private theorem attrFn_tendsto : Tendsto attrFn (nhds 0) (nhds 0) := by
  change Tendsto (fun _ : ℝ => (0 : ℝ)) (nhds 0) (nhds 0)
  exact tendsto_const_nhds

-- Before registration: fails

-- @@ L325-330 verbatim
/-- error: tendsto_cont: no `Tendsto` hypotheses found for filter `𝓝 0` -/
#guard_msgs(error, drop info) in
example : Tendsto (fun z => attrFn z + 1) (nhds 0) (nhds 1) := by
  tendsto_cont

-- Register via attribute

-- @@ L331-333 verbatim
attribute [tendsto_cont] attrFn_tendsto

-- After registration: works

-- @@ L334-335 verbatim
example : Tendsto (fun z => attrFn z + 1) (nhds 0) (nhds 1) := by
  tendsto_cont


-- @@ L337-340 verbatim
end AttrRegistration

-- Axiomatized function: fun_prop knows nothing about it,
-- so the attribute is the only source of the Tendsto fact.

-- @@ L341-341 verbatim
section AttrAxiom


-- @@ L343-343 verbatim
private axiom opaqueF : ℝ → ℝ

-- @@ L344-346 verbatim
private axiom opaqueF_tendsto : Tendsto opaqueF (nhds 1) (nhds 0)

-- Before registration: fails

-- @@ L347-350 verbatim
/-- error: tendsto_cont: no `Tendsto` hypotheses found for filter `𝓝 1` -/
#guard_msgs(error, drop info) in
example : Tendsto (fun z => opaqueF z + 1) (nhds 1) (nhds 1) := by
  tendsto_cont


-- @@ L352-354 verbatim
attribute [tendsto_cont] opaqueF_tendsto

-- After registration: works

-- @@ L355-356 verbatim
example : Tendsto (fun z => opaqueF z + 1) (nhds 1) (nhds 1) := by
  tendsto_cont


-- @@ L358-364 verbatim
end AttrAxiom

-- ══════════════════════════════════════════════════════════════
-- Negative tests: inline arguments
-- ══════════════════════════════════════════════════════════════

-- Wrong-filter inline arg is silently ignored → no candidates

-- @@ L365-370 verbatim
/-- error: tendsto_cont: no `Tendsto` hypotheses found for filter `atTop` -/
#guard_msgs(error, drop info) in
example (h : Tendsto f (nhds 0) (nhds 1)) :
    Tendsto (fun z => f z + 1) atTop (nhds 2) := by tendsto_cont [h]

-- Non-Tendsto inline arg is silently ignored → no candidates

-- @@ L371-376 verbatim
/-- error: tendsto_cont: no `Tendsto` hypotheses found for filter `atTop` -/
#guard_msgs(error, drop info) in
example (h : (1 : ℝ) + 1 = 2) :
    Tendsto (fun z : ℝ => z + 1) atTop (nhds 2) := by tendsto_cont [h]

-- Two inline args with same fn, different limits → ambiguity error

-- @@ L377-386 verbatim
/-- error: tendsto_cont: ambiguous limit for atom — found hypotheses with limits `0` and `1` for the same function -/
#guard_msgs(error, drop info) in
example (h₁ : Tendsto f atTop (nhds 0)) (h₂ : Tendsto f atTop (nhds 1)) :
    Tendsto (fun z => f z + 1) atTop (nhds 1) := by tendsto_cont [h₁, h₂]

-- ══════════════════════════════════════════════════════════════
-- Negative tests: attribute type validation
-- ══════════════════════════════════════════════════════════════

-- Non-Tendsto declaration rejected at registration time

-- @@ L387-392 verbatim
/-- error: `@[tendsto_cont]`: declaration type must be `Tendsto f l (nhds a)`, got head `True` -/
#guard_msgs(error, drop info) in
@[tendsto_cont]
theorem notATendstoTheorem : True := trivial

-- Parameterized declaration rejected (only closed lemmas allowed)

-- @@ L393-399 verbatim
/-- error: `@[tendsto_cont]`: declaration must be a closed `Tendsto` lemma with no parameters; got a declaration with binders -/
#guard_msgs(error, drop info) in
@[tendsto_cont]
theorem paramTendsto (_h : True) : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0) :=
  tendsto_const_nhds

-- Tendsto with wrong target filter rejected at registration time

-- @@ L400-407 verbatim
/-- error: `@[tendsto_cont]`: target filter must be `nhds _`, got `Filter.atTop` -/
#guard_msgs(error, drop info) in
@[tendsto_cont]
theorem wrongTargetFilter : Tendsto (fun z : ℝ => z) atTop atTop := tendsto_id

-- ══════════════════════════════════════════════════════════════
-- Negative tests: attribute scope rejection
-- ══════════════════════════════════════════════════════════════


-- @@ L409-410 verbatim
theorem testScopeRejection : Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (nhds 0) :=
  tendsto_const_nhds


-- @@ L412-414 verbatim
/-- error: `@[tendsto_cont]` only supports global scope (not `local` or `scoped`) -/
#guard_msgs(error, drop info) in
attribute [local tendsto_cont] testScopeRejection


-- @@ L416-416 verbatim
namespace TestScopeRejection

-- @@ L417-419 verbatim
/-- error: `@[tendsto_cont]` only supports global scope (not `local` or `scoped`) -/
#guard_msgs(error, drop info) in
attribute [scoped tendsto_cont] testScopeRejection

-- @@ L420-427 verbatim
end TestScopeRejection

-- ══════════════════════════════════════════════════════════════
-- Negative test: attribute-level ambiguity (same fn, different limits)
-- ══════════════════════════════════════════════════════════════

-- Use Bool with the indiscrete topology (⊤) so that nhds = ⊤ and
-- Tendsto holds trivially for any limit — no sorry needed.

-- @@ L428-428 verbatim
section AttrAmbiguity


-- @@ L430-430 verbatim
open Filter Topology


-- @@ L432-432 verbatim
local instance : TopologicalSpace Bool := ⊤


-- @@ L434-434 verbatim
private def bad : ℝ → Bool := fun _ => false


-- @@ L436-439 verbatim
@[tendsto_cont]
private theorem bad_tendsto_false : Tendsto bad atTop (nhds false) := by
  rw [nhds_top]
  exact tendsto_top


-- @@ L441-446 verbatim
@[tendsto_cont]
private theorem bad_tendsto_true : Tendsto bad atTop (nhds true) := by
  rw [nhds_top]
  exact tendsto_top

-- Same-bucket ambiguity: two attribute lemmas with same fn, different limits

-- @@ L447-450 verbatim
/-- error: tendsto_cont: ambiguous limit for atom — found hypotheses with limits `false` and `true` for the same function -/
#guard_msgs(error, drop info) in
example : Tendsto (fun z => bad z) atTop (nhds false) := by
  tendsto_cont


-- @@ L452-463 verbatim
end AttrAmbiguity

-- ══════════════════════════════════════════════════════════════
-- Cross-bucket shadowing: attribute vs local / attribute vs inline
-- ══════════════════════════════════════════════════════════════

-- Sierpinski-style topology on Bool via mkOfNhds:
-- nhds false = ⊤ (every set is a neighborhood of false)
-- nhds true = pure true (only sets containing true are neighborhoods)
-- These are genuinely distinguishable, so reconcileLimits cannot paper
-- over a wrong limit choice. Both Tendsto facts are provable because
-- good always returns true.

-- @@ L464-464 verbatim
section AttrShadowing


-- @@ L466-466 verbatim
open Filter Topology


-- @@ L468-469 verbatim
local instance : TopologicalSpace Bool :=
  TopologicalSpace.mkOfNhds (Function.update pure false ⊤)


-- @@ L471-474 verbatim
private lemma nhds_eq : ∀ b : Bool,
    @nhds Bool (TopologicalSpace.mkOfNhds (Function.update pure false ⊤)) b =
    Function.update pure false ⊤ b :=
  TopologicalSpace.nhds_mkOfNhds_single le_top


-- @@ L476-476 verbatim
private def good : ℝ → Bool := fun _ => true


-- @@ L478-480 verbatim
@[tendsto_cont]
private theorem good_attr_false : Tendsto good atTop (nhds false) := by
  rw [nhds_eq]; simp [Function.update_self]


-- @@ L482-487 verbatim
private theorem good_inline_true : Tendsto good atTop (nhds true) := by
  rw [nhds_eq]; simp [good]

-- Local context shadows attribute registry.
-- Load-bearing: if the attributed false limit were used instead,
-- nhds false = ⊤ ≠ pure true = nhds true, so reconcileLimits fails.

-- @@ L488-491 verbatim
example (h : Tendsto good atTop (nhds true)) :
    Tendsto (fun z => good z) atTop (nhds true) := by tendsto_cont

-- Inline arg shadows attribute registry.

-- @@ L492-493 verbatim
example : Tendsto (fun z => good z) atTop (nhds true) := by
  tendsto_cont [good_inline_true]


-- @@ L495-495 verbatim
end AttrShadowing
