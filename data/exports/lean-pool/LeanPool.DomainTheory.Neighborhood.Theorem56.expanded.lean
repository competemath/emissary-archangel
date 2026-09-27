/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import LeanPool.DomainTheory.Neighborhood.Example43
public import LeanPool.DomainTheory.Neighborhood.Exercise326
public import LeanPool.DomainTheory.Neighborhood.Theorem41
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow


-- @@ L18-68 verbatim
/-!
# Theorem 5.6 (Scott 1981, PRG-19, §5) — recursive functions are λ-definable

Scott's Theorem 5.6: every partial recursive `h : N → N` is denoted by a λ-term
whose only constants
are `cond`, `succ`, `pred`, `zero`, `0`. The proof is by the standard generation
of the partial
recursive functions: strict *starting* functions, closure under (multivariate)
*composition*,
*primitive recursion*, and the *μ-scheme* (least-number operator). We formalise
the constructive
heart of the proof — the actual combinators Scott writes down — over the
natural-number domain `N`
(Example 4.3) and the conditional `cond` (Exercise 3.26), proving the defining
equations of each
scheme. (We do not also wire these together against an external inductive
predicate of partial
recursive functions; that closure is a routine but lengthy induction over the
generation grammar,
built entirely from the pieces below.)

## What is proved

* **Strict starting functions** (Scott's "simple device" `λx. cond(zero(x), x,
x)`):
  - `strictId` with `strictId_natElem` (`= n̂`) and `strictId_bot` (`= ⊥`);
  - `strictProj₀ : N × N → N`, the strict first projection, with
  `strictProj₀_natElem`,
    `strictProj₀_bot_left`, `strictProj₀_bot_right` (strict in *both* arguments).

* **Primitive recursion** `primRec f g`, the least fixed point
  `!k λx,y. cond(zero(x), f(y), g(pred(x), y, k(pred(x), y)))`, with the scheme
  equations
  - `primRec_zero` : `hbar(0̂, m̂) = f(m̂)`,
  - `primRec_succ` : `hbar((n+1)^, m̂) = g(n̂, m̂, hbar(n̂, m̂))`,
  - `primRec_bot`  : `hbar(⊥, m̂) = ⊥`  (strict in the recursion argument).

* **The μ-scheme** `muRec f` / `muMap f`, the least fixed point
  `!g λx,y. cond(zero(f(x,y)), x, g(succ(x), y))` and `hbar = λy. gbar(0̂, y)`, with
  - `muRec_found` : `f(n̂, m̂) = 0̂  ⟹  gbar(n̂, m̂) = n̂`,
  - `muRec_step`  : `f(n̂, m̂) = (j+1)^  ⟹  gbar(n̂, m̂) = gbar((n+1)^, m̂)`,
  - `muRec_bot`   : `f(n̂, m̂) = ⊥  ⟹  gbar(n̂, m̂) = ⊥`,
  and the **capstone** `muMap_eq_least`: if `n₀` is the least zero of `f(·, m̂)`
  (all earlier values
  positive totals), then `μ(m̂) = n̂₀`.

All `cond`-based maps inherit `Classical.choice` structurally from the truth
domain `T`
(Example 1.2) exactly as `cond`/`zeroMap` already do; the fixed points come from
Theorem 4.1.
-/


-- @@ L70-70 verbatim
@[expose] public section


-- @@ L72-72 verbatim
namespace Domain.Neighborhood.Theorem56


-- @@ L74-74 verbatim
open Domain.Neighborhood NeighborhoodSystem ApproximableMap

-- @@ L75-77 verbatim
open Domain.Neighborhood.Example43 (N natElem zeroElt succMap predMap zeroMap
  succMap_natElem succMap_bot predMap_natElem_succ predMap_natElem_zero predMap_bot
  zeroMap_natElem_zero zeroMap_natElem_succ zeroMap_bot constLiftN constLiftN_natElem)

-- @@ L78-78 verbatim
open Domain.Neighborhood.Exercise326 (cond)


-- @@ L80-86 verbatim
/-- The truth-domain bottom of `T` agrees with `Example23.botElt` (both are the
least element).
Needed because `zeroMap_bot` lands in `T.bot` while `cond_bot` is phrased with
`Example23.botElt`,
and `bot` is not reducible. -/
theorem T_bot_eq : (Example43.T).bot = Example23.botElt :=
  le_antisymm ((Example43.T).bot_le _) (Example23.botElt_le _)


-- @@ L88-88 verbatim
/-! ### Strict starting functions (`λx. cond(zero x, x, x)`). -/


-- @@ L90-93 verbatim
/-- Scott's **strict identity** `λx. cond(zero(x), x, x)`: the identity on totals,
`⊥` on `⊥`. -/
def strictId : ApproximableMap N N :=
  (cond N).comp (paired zeroMap (paired (idMap N) (idMap N)))


-- @@ L95-100 verbatim
theorem strictId_natElem (n : ℕ) : strictId.toElementMap (natElem n) = natElem n := by
  rw [strictId, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_idMap]
  cases n with
  | zero => rw [zeroMap_natElem_zero, Exercise326.cond_true]
  | succ k => rw [zeroMap_natElem_succ, Exercise326.cond_false]


-- @@ L102-105 verbatim
theorem strictId_bot : strictId.toElementMap N.bot = N.bot := by
  rw [strictId, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_idMap]
  rw [zeroMap_bot, T_bot_eq, Exercise326.cond_bot]


-- @@ L107-112 verbatim
/-- Scott's **strict first projection** `λx₀, x₁. cond(zero(x₁), x₀, x₀)` on `N ×
N`. -/
def strictProj₀ : ApproximableMap (prod N N) N :=
  (cond N).comp
    (paired (zeroMap.comp (proj₁ N N))
      (paired (proj₀ N N) (proj₀ N N)))


-- @@ L114-119 verbatim
theorem strictProj₀_apply (x y : N.Element) :
    strictProj₀.toElementMap (pair x y) =
      (cond N).toElementMap (pair (zeroMap.toElementMap y) (pair x x)) := by
  rw [strictProj₀, toElementMap_comp]
  simp only [toElementMap_paired, toElementMap_comp, toElementMap_proj₀, toElementMap_proj₁,
    fst_pair, snd_pair]


-- @@ L121-127 verbatim
/-- `proj₀(n̂, m̂) = n̂`. -/
theorem strictProj₀_natElem (n m : ℕ) :
    strictProj₀.toElementMap (pair (natElem n) (natElem m)) = natElem n := by
  rw [strictProj₀_apply]
  cases m with
  | zero => rw [zeroMap_natElem_zero, Exercise326.cond_true]
  | succ k => rw [zeroMap_natElem_succ, Exercise326.cond_false]


-- @@ L129-132 verbatim
/-- Strict in the second argument: `proj₀(n̂, ⊥) = ⊥`. -/
theorem strictProj₀_bot_right (n : ℕ) :
    strictProj₀.toElementMap (pair (natElem n) N.bot) = N.bot := by
  rw [strictProj₀_apply, zeroMap_bot, T_bot_eq, Exercise326.cond_bot]


-- @@ L134-140 verbatim
/-- Strict in the first argument: `proj₀(⊥, m̂) = ⊥` (the output *is* `x₀ = ⊥`). -/
theorem strictProj₀_bot_left (m : ℕ) :
    strictProj₀.toElementMap (pair N.bot (natElem m)) = N.bot := by
  rw [strictProj₀_apply]
  cases m with
  | zero => rw [zeroMap_natElem_zero, Exercise326.cond_true]
  | succ k => rw [zeroMap_natElem_succ, Exercise326.cond_false]


-- @@ L142-148 verbatim
/-! ### Primitive recursion.

Given `f : N → N` and `g : N × N × N → N` (with `N³` modelled as `N × (N × N)`),
the primitive
recursion `hbar` with `hbar(0, m) = f(m)`, `hbar(n+1, m) = g(n, m, hbar(n, m))` is the
least fixed point of
`λk λx,y. cond(zero(x), f(y), g(pred(x), y, k(pred(x), y)))`. -/


-- @@ L150-155 verbatim
/-! ### Selector maps on `(N×N → N) × (N×N)`.

The recursion bodies live over `prod F Q` with `F = funSpace (N×N) N` (the
unknown) and `Q = N × N`
(the argument pair). We name the four selectors once to keep the body terms
readable. -/


-- @@ L157-159 verbatim
/-- The argument pair `⟨x, y⟩` (`= proj₁`). -/
def qSel : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) (prod N N) :=
  proj₁ (funSpace (prod N N) N) (prod N N)


-- @@ L161-163 verbatim
/-- The unknown function `k` (`= proj₀`). -/
def kSel : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) (funSpace (prod N N) N) :=
  proj₀ (funSpace (prod N N) N) (prod N N)


-- @@ L165-166 verbatim
/-- The first argument `x`. -/
def argX : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) N := (proj₀ N N).comp qSel


-- @@ L168-169 verbatim
/-- The second argument `y`. -/
def argY : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) N := (proj₁ N N).comp qSel


-- @@ L171-171 verbatim
section PrimRec


-- @@ L173-173 verbatim
variable (f : ApproximableMap N N) (g : ApproximableMap (prod N (prod N N)) N)


-- @@ L175-185 verbatim
/-- The two-argument body `M(k, ⟨x, y⟩) = cond(zero(x), f(y), g(pred x, y, k(pred
x, y)))`. -/
def primBody : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) N :=
  (cond N).comp
    (paired (zeroMap.comp argX)
      (paired (f.comp argY)
        (g.comp
          (paired (predMap.comp argX)
            (paired argY
              ((evalMap (prod N N) N).comp
                (paired kSel (paired (predMap.comp argX) argY))))))))


-- @@ L187-198 verbatim
theorem primBody_apply (k : (funSpace (prod N N) N).Element) (x y : N.Element) :
    (primBody f g).toElementMap (pair k (pair x y)) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap x)
          (pair (f.toElementMap y)
            (g.toElementMap
              (pair (predMap.toElementMap x)
                (pair y ((toApproxMap k).toElementMap
                  (pair (predMap.toElementMap x) y))))))) := by
  rw [primBody, toElementMap_comp]
  simp only [argX, argY, kSel, qSel, toElementMap_paired, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁, fst_pair, snd_pair, evalMap_apply]


-- @@ L200-204 verbatim
/-- The primitive-recursion operator `R(k) = λx,y. cond(zero x, f y, g(pred x, y,
k(pred x,
y)))`. -/
def primOp : ApproximableMap (funSpace (prod N N) N) (funSpace (prod N N) N) :=
  curry (primBody f g)


-- @@ L206-207 verbatim
/-- `primRec f g : N × N → N`, the least fixed point of `primOp`. -/
def primRec : ApproximableMap (prod N N) N := toApproxMap (primOp f g).fixElement


-- @@ L209-223 verbatim
/-- The defining recursion of `primRec`. -/
theorem primRec_rec (x y : N.Element) :
    (primRec f g).toElementMap (pair x y) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap x)
          (pair (f.toElementMap y)
            (g.toElementMap
              (pair (predMap.toElementMap x)
                (pair y ((primRec f g).toElementMap
                  (pair (predMap.toElementMap x) y))))))) := by
  have hfix : (primOp f g).toElementMap (primOp f g).fixElement = (primOp f g).fixElement :=
    toElementMap_fixElement (primOp f g)
  have hval := toElementMap_curry_apply (primBody f g) (primOp f g).fixElement (pair x y)
  rw [← primOp, hfix] at hval
  rw [primRec, hval, primBody_apply]


-- @@ L225-228 verbatim
/-- **Primitive recursion, base case.** `hbar(0̂, m̂) = f(m̂)`. -/
theorem primRec_zero (m : ℕ) :
    (primRec f g).toElementMap (pair (natElem 0) (natElem m)) = f.toElementMap (natElem m) := by
  rw [primRec_rec, zeroMap_natElem_zero, Exercise326.cond_true]


-- @@ L230-236 verbatim
/-- **Primitive recursion, step case.** `hbar((n+1)^, m̂) = g(n̂, m̂, hbar(n̂, m̂))`. -/
theorem primRec_succ (n m : ℕ) :
    (primRec f g).toElementMap (pair (natElem (n + 1)) (natElem m)) =
      g.toElementMap
        (pair (natElem n)
          (pair (natElem m) ((primRec f g).toElementMap (pair (natElem n) (natElem m))))) := by
  rw [primRec_rec, zeroMap_natElem_succ, Exercise326.cond_false, predMap_natElem_succ]


-- @@ L238-241 verbatim
/-- **Primitive recursion is strict in the recursion argument.** `hbar(⊥, m̂) = ⊥`. -/
theorem primRec_bot (m : ℕ) :
    (primRec f g).toElementMap (pair N.bot (natElem m)) = N.bot := by
  rw [primRec_rec, zeroMap_bot, T_bot_eq, Exercise326.cond_bot]


-- @@ L243-243 verbatim
end PrimRec


-- @@ L245-248 verbatim
/-! ### The μ-scheme (least-number operator).

Given `f : N × N → N`, the minimization `hbar(m) = μn. f(n, m) = 0` is obtained from
`gbar = !g λx,y. cond(zero(f(x,y)), x, g(succ(x), y))` by `hbar = λy. gbar(0̂, y)`. -/


-- @@ L250-250 verbatim
section Mu


-- @@ L252-252 verbatim
variable (f : ApproximableMap (prod N N) N)


-- @@ L254-260 verbatim
/-- The body `M(g, ⟨x, y⟩) = cond(zero(f(x, y)), x, g(succ x, y))`. -/
def muBody : ApproximableMap (prod (funSpace (prod N N) N) (prod N N)) N :=
  (cond N).comp
    (paired (zeroMap.comp (f.comp qSel))
      (paired argX
        ((evalMap (prod N N) N).comp
          (paired kSel (paired (succMap.comp argX) argY)))))


-- @@ L262-269 verbatim
theorem muBody_apply (k : (funSpace (prod N N) N).Element) (x y : N.Element) :
    (muBody f).toElementMap (pair k (pair x y)) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap (f.toElementMap (pair x y)))
          (pair x ((toApproxMap k).toElementMap (pair (succMap.toElementMap x) y)))) := by
  rw [muBody, toElementMap_comp]
  simp only [argX, argY, kSel, qSel, toElementMap_paired, toElementMap_comp, toElementMap_proj₀,
    toElementMap_proj₁, fst_pair, snd_pair, evalMap_apply]


-- @@ L271-273 verbatim
/-- The μ-operator `R(g) = λx,y. cond(zero(f(x, y)), x, g(succ x, y))`. -/
def muOp : ApproximableMap (funSpace (prod N N) N) (funSpace (prod N N) N) :=
  curry (muBody f)


-- @@ L275-276 verbatim
/-- `muRec f : N × N → N`, the binary search `gbar`, least fixed point of `muOp`. -/
def muRec : ApproximableMap (prod N N) N := toApproxMap (muOp f).fixElement


-- @@ L278-281 verbatim
/-- The minimization `μ : N → N`, `hbar(m) = gbar(0̂, m)` (the strict `0`-seeded
search). -/
def muMap : ApproximableMap N N := muRec f |>.comp (paired (constLiftN N (fun _ => zeroElt)) (
  idMap N))


-- @@ L283-293 verbatim
/-- The defining recursion of `muRec`. -/
theorem muRec_rec (x y : N.Element) :
    (muRec f).toElementMap (pair x y) =
      (cond N).toElementMap
        (pair (zeroMap.toElementMap (f.toElementMap (pair x y)))
          (pair x ((muRec f).toElementMap (pair (succMap.toElementMap x) y)))) := by
  have hfix : (muOp f).toElementMap (muOp f).fixElement = (muOp f).fixElement :=
    toElementMap_fixElement (muOp f)
  have hval := toElementMap_curry_apply (muBody f) (muOp f).fixElement (pair x y)
  rw [← muOp, hfix] at hval
  rw [muRec, hval, muBody_apply]


-- @@ L295-299 verbatim
/-- **μ, found.** If `f(n̂, m̂) = 0̂`, the search stops and returns `n̂`. -/
theorem muRec_found {n m : ℕ}
    (h : f.toElementMap (pair (natElem n) (natElem m)) = natElem 0) :
    (muRec f).toElementMap (pair (natElem n) (natElem m)) = natElem n := by
  rw [muRec_rec, h, zeroMap_natElem_zero, Exercise326.cond_true]


-- @@ L301-307 verbatim
/-- **μ, step.** If `f(n̂, m̂)` is a positive total `(j+1)^`, the search advances
to `n+1`. -/
theorem muRec_step {n m j : ℕ}
    (h : f.toElementMap (pair (natElem n) (natElem m)) = natElem (j + 1)) :
    (muRec f).toElementMap (pair (natElem n) (natElem m)) =
      (muRec f).toElementMap (pair (natElem (n + 1)) (natElem m)) := by
  rw [muRec_rec, h, zeroMap_natElem_succ, Exercise326.cond_false, succMap_natElem]


-- @@ L309-313 verbatim
/-- **μ is strict in the test.** If `f(n̂, m̂) = ⊥`, the search diverges. -/
theorem muRec_bot {n m : ℕ}
    (h : f.toElementMap (pair (natElem n) (natElem m)) = N.bot) :
    (muRec f).toElementMap (pair (natElem n) (natElem m)) = N.bot := by
  rw [muRec_rec, h, zeroMap_bot, T_bot_eq, Exercise326.cond_bot]


-- @@ L315-319 verbatim
/-- `μ(m̂) = gbar(0̂, m̂)`. -/
theorem muMap_natElem (m : ℕ) :
    (muMap f).toElementMap (natElem m) = (muRec f).toElementMap (pair zeroElt (natElem m)) := by
  rw [muMap, toElementMap_comp, toElementMap_paired, toElementMap_idMap,
    constLiftN_natElem]


-- @@ L321-339 verbatim
/-- The search advances over a run of positive totals: if `f((n+i)^, m̂)` is a
positive total for
all `i < k`, then `gbar(n̂, m̂) = gbar((n+k)^, m̂)`. -/
theorem muRec_climb (m : ℕ) :
    ∀ (k n : ℕ), (∀ i < k, ∃ j, f.toElementMap (pair (natElem (n +
      i)) (natElem m)) = natElem (j + 1)) →
      (muRec f).toElementMap (pair (natElem n) (natElem m)) =
        (muRec f).toElementMap (pair (natElem (n + k)) (natElem m)) := by
  intro k
  induction k with
  | zero => intro n _; rw [Nat.add_zero]
  | succ k ih =>
    intro n h
    obtain ⟨j, hj⟩ := h 0 (Nat.succ_pos k)
    rw [Nat.add_zero] at hj
    have key := ih (n + 1) (fun i hi => by
      obtain ⟨j', hj'⟩ := h (i + 1) (by omega)
      exact ⟨j', by rw [show n + 1 + i = n + (i + 1) by omega]; exact hj'⟩)
    rw [muRec_step f hj, key, show n + 1 + k = n + (k + 1) by omega]


-- @@ L341-352 verbatim
/-- **Capstone (μ-scheme correctness).** If `n₀` is the *least* zero of `f(·, m̂)`
— that is,
`f(n̂₀, m̂) = 0̂` and `f(î, m̂)` is a positive total for every `i < n₀` — then
`μ(m̂) = n̂₀`. -/
theorem muMap_eq_least {m n₀ : ℕ}
    (hzero : f.toElementMap (pair (natElem n₀) (natElem m)) = natElem 0)
    (hpos : ∀ i < n₀, ∃ j, f.toElementMap (pair (natElem i) (natElem m)) = natElem (j + 1)) :
    (muMap f).toElementMap (natElem m) = natElem n₀ := by
  rw [muMap_natElem]
  have hclimb := muRec_climb f m n₀ 0 (by simpa using hpos)
  rw [show (zeroElt : N.Element) = natElem 0 from rfl, hclimb, Nat.zero_add]
  exact muRec_found f hzero


-- @@ L354-354 verbatim
end Mu


-- @@ L356-356 verbatim
end Domain.Neighborhood.Theorem56
