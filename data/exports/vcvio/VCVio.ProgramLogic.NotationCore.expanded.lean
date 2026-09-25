/-
Copyright (c) 2026 Quang Dao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import VCVio.ProgramLogic.Unary.HoareTriple
public import VCVio.EvalDist.TVDist
public import VCVio.ProgramLogic.Relational.Basic
public import VCVio.ProgramLogic.Relational.QuantitativeDefs
public import ToMathlib.Control.Monad.RelWP


-- @@ L15-45 verbatim
/-!
# Ergonomic Notation and Convenience Layer for Program Logic

This file provides the lightweight user-facing notation and convenience predicates for
game-hopping proofs. It intentionally depends only on the core quantitative definitions,
not on the full eRHL theorem development.

The canonical proof mode lives in `VCVio/ProgramLogic/Tactics.lean`.

## Notation (activate with `open scoped OracleComp.ProgramLogic`)

### Prop indicator
- `𝟙⟦P⟧` — inject `Prop` into `ℝ≥0∞` (1 if true, 0 if false)

### Unary (Std.Do-inspired)
- `wp⟦c⟧` — quantitative WP (partial application, use as `wp⟦c⟧ post`)
- `⦃P⦄ c ⦃Q⦄` — quantitative Hoare triple (`P ≤ wp c Q`)

### Game-level
- `g₁ ≡ₚ g₂` — game equivalence (`evalSPMF g₁ = evalSPMF g₂`)

### Relational (EasyCrypt-inspired)
- `⟪c₁ ~ c₂ | R⟫` — pRHL coupling triple
- `⟪c₁ ≈[ε] c₂ | R⟫` — approximate coupling triple
- `⦃f⦄ c₁ ≈ₑ c₂ ⦃g⦄` — eRHL quantitative relational triple

## Convenience predicates

- `GameEquiv g₁ g₂` — two games have the same output distribution
- `AdvBound game ε` — advantage of a game is at most `ε`
-/


-- @@ L47-47 verbatim
@[expose] public section


-- @@ L49-49 verbatim
open ENNReal OracleSpec OracleComp


-- @@ L51-51 verbatim
universe u


-- @@ L53-53 verbatim
namespace OracleComp.ProgramLogic


-- @@ L55-55 verbatim
variable {ι₁ : Type u}

-- @@ L56-56 verbatim
variable {spec₁ : OracleSpec ι₁}

-- @@ L57-57 verbatim
variable [IsUniformSpec spec₁]

-- @@ L58-58 verbatim
variable {α β : Type}


-- @@ L60-60 verbatim
/-! ## Convenience predicates -/


-- @@ L62-64 expanded
/-- Two games have the same output distribution. -/
def GameEquiv (g₁ g₂ : OracleComp spec₁ α) : Prop :=
  evalSPMF g₁ = evalSPMF g₂


-- @@ L66-68 expanded
/-- Advantage of a Boolean game is at most `ε` (measured as deviation from 1/2). -/
def AdvBound (game : OracleComp spec₁ Bool) (ε : ℝ) : Prop :=
  |(probOutput game true).toReal - 1 / 2| ≤ ε


-- @@ L70-70 verbatim
@[refl] theorem GameEquiv.rfl {g : OracleComp spec₁ α} : GameEquiv g g := Eq.refl _


-- @@ L72-73 verbatim
@[symm] theorem GameEquiv.symm {g₁ g₂ : OracleComp spec₁ α}
    (h : GameEquiv g₁ g₂) : GameEquiv g₂ g₁ := Eq.symm h


-- @@ L75-77 verbatim
@[trans] theorem GameEquiv.trans {g₁ g₂ g₃ : OracleComp spec₁ α}
    (h₁ : GameEquiv g₁ g₂) (h₂ : GameEquiv g₂ g₃) : GameEquiv g₁ g₃ :=
  Eq.trans h₁ h₂


-- @@ L79-81 expanded
theorem GameEquiv.probOutput_eq {g₁ g₂ : OracleComp spec₁ α} (h : GameEquiv g₁ g₂) (x : α) :
    probOutput g₁ x = probOutput g₂ x :=
  probOutput_congr_evalSPMF h x


-- @@ L83-83 verbatim
/-! ## Prop-to-ℝ≥0∞ indicator -/


-- @@ L85-89 verbatim
open scoped Classical in
/-- Indicator embedding: lifts `P : Prop` into `ℝ≥0∞` as `1` (true) or `0` (false).
This is the quantitative analogue of Loom's pure proposition assertion, but
targets the expectation carrier rather than the current assertion lattice. -/
noncomputable def propInd (P : Prop) : ℝ≥0∞ := if P then 1 else 0


-- @@ L91-91 verbatim
@[simp] lemma propInd_true : propInd True = 1 := if_pos trivial

-- @@ L92-92 verbatim
@[simp] lemma propInd_false : propInd False = 0 := if_neg id


-- @@ L94-94 verbatim
lemma propInd_eq_ite {P : Prop} [Decidable P] : propInd P = if P then 1 else 0 := by simp [propInd]


-- @@ L96-98 verbatim
open scoped Classical in
@[simp] lemma propInd_and {P Q : Prop} : propInd (P ∧ Q) = propInd P * propInd Q := by
  unfold propInd; split_ifs <;> simp_all


-- @@ L100-102 verbatim
open scoped Classical in
lemma propInd_mono {P Q : Prop} (h : P → Q) : propInd P ≤ propInd Q := by
  unfold propInd; split_ifs <;> simp_all


-- @@ L104-105 verbatim
lemma propInd_le_one (P : Prop) : propInd P ≤ 1 := by
  unfold propInd; split_ifs <;> simp


-- @@ L107-108 verbatim
open scoped Classical in
lemma propInd_eq_one_iff {P : Prop} : propInd P = 1 ↔ P := by simp [propInd]


-- @@ L110-111 verbatim
open scoped Classical in
lemma propInd_eq_zero_iff {P : Prop} : propInd P = 0 ↔ ¬P := by simp [propInd]


-- @@ L113-115 verbatim
open scoped Classical in
lemma propInd_or_le {P Q : Prop} : propInd (P ∨ Q) ≤ propInd P + propInd Q := by
  unfold propInd; split_ifs <;> simp_all


-- @@ L117-119 verbatim
open scoped Classical in
lemma propInd_not {P : Prop} : propInd (¬P) = 1 - propInd P := by
  unfold propInd; split_ifs <;> simp_all


-- @@ L121-121 verbatim
/-! ## Notation -/


-- @@ L123-126 verbatim
/-- Numeric proposition indicator: `𝟙⟦P⟧ = 1` if `P` holds, `0` otherwise.
This is deliberately distinct from Loom's `⌜P⌝`, which embeds propositions as
top/bottom in the active assertion lattice. -/
scoped notation "𝟙⟦" P "⟧" => propInd P


-- @@ L128-132 verbatim
/-- Quantitative WP notation. `wp⟦c⟧ post` directly elaborates to
`wp c post`; `wp⟦c⟧` standalone elaborates to
the lambda `fun post => wp c post` for partial
application sites (e.g. `change wp⟦c⟧` or composition with `≤`). -/
scoped syntax:max (name := wpBracket) "wp⟦" term "⟧" : term

-- @@ L133-133 verbatim
scoped syntax:max (name := wpBracketApp) "wp⟦" term "⟧" term:max : term


-- @@ L135-137 verbatim
scoped macro_rules
  | `(wp⟦ $c ⟧ $post:term) => `(wp $c $post)
  | `(wp⟦ $c ⟧)            => `(fun post => wp $c post)


-- @@ L139-145 verbatim
/-- Raw relational WP notation.
`rwp⟦c₁ ~ c₂ | post; epost₁, epost₂⟧` elaborates to `Std.Do'.rwp`.
The normal assertion carrier and both exception-post carriers are inferred from
`post`, `epost₁`, and `epost₂`, so this notation also works for stateful and
exception-aware `RelWP` instances. -/
scoped syntax:max (name := relWpBracket)
  "rwp⟦" term:lead " ~ " term:lead " | " term ";" term ", " term "⟧" : term


-- @@ L147-149 verbatim
scoped macro_rules (kind := relWpBracket)
  | `(rwp⟦ $c₁ ~ $c₂ | $post; $epost₁, $epost₂ ⟧) =>
      `(Std.Do'.rwp $c₁ $c₂ $post $epost₁ $epost₂)


-- @@ L151-154 verbatim
/-- Game equivalence: `g₁ ≡ₚ g₂` means `evalSPMF g₁ = evalSPMF g₂`.
Uses `syntax` + `macro_rules` because `≡` conflicts with Mathlib's
modular equivalence notation (`a ≡ b [MOD n]`). -/
scoped syntax:50 term:50 " ≡ₚ " term:51 : term

-- @@ L155-155 expanded
macro_rules
  | `(GameEquiv $a $b) => `(GameEquiv $a $b)


-- @@ L157-158 verbatim
/-- pRHL coupling: `⟪c₁ ~ c₂ | R⟫` means `RelTriple c₁ c₂ R`. -/
scoped notation "⟪" c₁ " ~ " c₂ " | " R "⟫" => Relational.RelTriple c₁ c₂ R


-- @@ L160-162 verbatim
/-- Approximate coupling: `⟪c₁ ≈[ε] c₂ | R⟫` means `ApproxRelTriple ε c₁ c₂ R`. -/
scoped notation "⟪" c₁ " ≈[" ε "] " c₂ " | " R "⟫" =>
  Relational.ApproxRelTriple ε c₁ c₂ R


-- @@ L164-166 verbatim
/-- eRHL quantitative relational triple:
`⦃f⦄ c₁ ≈ₑ c₂ ⦃g⦄` means the quantitative `Std.Do'.RelTriple` form. -/
scoped syntax:lead "⦃" term "⦄ " term:lead " ≈ₑ " term:lead " ⦃" term "⦄" : term

-- @@ L167-169 expanded
macro_rules
  | `(Std.Do'.RelTriple $f $c₁ $c₂ $g Lean.Order.bot Lean.Order.bot) =>
    `(Std.Do'.RelTriple $f $c₁ $c₂ $g Lean.Order.bot Lean.Order.bot)


-- @@ L171-171 verbatim
/-! ## Bridge lemmas: numeric indicators and existing API -/


-- @@ L173-178 expanded
/-- `probEvent` equals WP of propInd postcondition. -/
lemma probEvent_eq_wp_propInd {ι : Type u} {spec : OracleSpec ι} [IsUniformSpec spec] {α : Type}
    (oa : OracleComp spec α) (p : α → Prop) : probEvent oa p = wp oa (fun x => 𝟙⟦p x⟧) := by
  classical simpa only [propInd_eq_ite] using probEvent_eq_wp_indicator oa p


-- @@ L180-183 verbatim
/-- `RelPost.indicator` is pointwise `𝟙⟦_⟧`. -/
lemma Relational.RelPost.indicator_eq_propInd {α β : Type}
    (R : Relational.RelPost α β) (a : α) (b : β) :
    Relational.RelPost.indicator R a b = 𝟙⟦R a b⟧ := rfl


-- @@ L185-193 expanded
/-- Almost-sure correctness: `Triple 𝟙⟦True⟧ c (fun x => 𝟙⟦p x⟧)` iff
`Pr[ p | c] = 1`. -/
lemma triple_propInd_iff_probEvent_eq_one {ι : Type u} {spec : OracleSpec ι} [IsUniformSpec spec]
    {α : Type} (oa : OracleComp spec α) (p : α → Prop) :
    Triple (𝟙⟦True⟧ : ℝ≥0∞) oa (fun x => 𝟙⟦p x⟧) ↔ probEvent oa p = 1 :=
  by
  rw [triple_iff_le_wp, propInd_true, ← probEvent_eq_wp_propInd]
  exact one_le_probEvent_iff


-- @@ L195-200 expanded
/-- Lower-bound event goals are exactly quantitative triples with indicator postconditions. -/
lemma triple_propInd_iff_le_probEvent {ι : Type u} {spec : OracleSpec ι} [IsUniformSpec spec]
    {α : Type} (oa : OracleComp spec α) (p : α → Prop) (r : ℝ≥0∞) :
    Triple r oa (fun x => 𝟙⟦p x⟧) ↔ r ≤ probEvent oa p := by
  rw [triple_iff_le_wp, ← probEvent_eq_wp_propInd]


-- @@ L202-202 verbatim
/-! ## Expectation-level bridge lemmas -/


-- @@ L204-211 verbatim
/-- WP of a disjunction indicator is bounded by the sum of individual WP indicators. -/
theorem wp_propInd_or_le {ι : Type u} {spec : OracleSpec ι} [IsUniformSpec spec] {α : Type}
    (oa : OracleComp spec α) (p q : α → Prop) :
    wp oa (fun x => 𝟙⟦p x ∨ q x⟧) ≤
        wp oa (fun x => 𝟙⟦p x⟧) +
          wp oa (fun x => 𝟙⟦q x⟧) := by
  rw [← probEvent_eq_wp_propInd, ← probEvent_eq_wp_propInd, ← probEvent_eq_wp_propInd]
  exact probEvent_or_le _ _ _


-- @@ L213-218 expanded
/-- Monotonicity for event probabilities, exposed through the program-logic namespace. -/
theorem probEvent_mono {ι : Type u} {spec : OracleSpec ι} [IsUniformSpec spec] {α : Type}
    (oa : OracleComp spec α) {p q : α → Prop} (h : ∀ x, p x → q x) :
    probEvent oa p ≤ probEvent oa q :=
  _root_.probEvent_mono (mx := oa) (fun x _ => h x)


-- @@ L220-230 expanded
/-- Markov inequality: if `a ≤ f x` whenever `p x`, then `a * Pr[ p | oa] ≤ E[f | oa]`. -/
theorem markov_bound {ι : Type u} {spec : OracleSpec ι} [IsUniformSpec spec] {α : Type}
    (oa : OracleComp spec α) (f : α → ℝ≥0∞) (a : ℝ≥0∞) (p : α → Prop) (hf : ∀ x, p x → a ≤ f x) :
    a * probEvent oa p ≤ wp oa f :=
  by
  rw [probEvent_eq_wp_propInd, ← wp_mul_const]
  refine wp_mono oa fun x => ?_
  unfold propInd
  split_ifs with hp
  · simpa using hf x hp
  · simp


-- @@ L232-238 verbatim
/-- `Triple` with precondition `1` and indicator postcondition when the event is almost sure. -/
theorem triple_propInd_of_support {ι : Type u} {spec : OracleSpec ι} [IsUniformSpec spec] {α : Type}
    (oa : OracleComp spec α) (p : α → Prop) (h : ∀ x ∈ support oa, p x) :
    Triple (1 : ℝ≥0∞) oa (fun x => 𝟙⟦p x⟧) := by
  rw [show (1 : ℝ≥0∞) = 𝟙⟦True⟧ from propInd_true.symm]
  exact (triple_propInd_iff_probEvent_eq_one oa p).mpr
    (probEvent_eq_one ⟨probFailure_of_liftM_PMF oa, h⟩)


-- @@ L240-240 verbatim
/-! ## Bridge lemmas: game equivalence and advantage -/


-- @@ L242-247 verbatim
/-- Game equivalence from basic pRHL equality coupling. -/
theorem GameEquiv.of_relTriple {g₁ g₂ : OracleComp spec₁ α}
    (h : Relational.RelTriple (spec₁ := spec₁) (spec₂ := spec₁) g₁ g₂
      (Relational.EqRel α)) :
    GameEquiv g₁ g₂ :=
  Relational.evalSPMF_eq_of_relTriple_eqRel h


-- @@ L249-257 expanded
/-- A bijection on a uniform sample is still uniform.
This is the key lemma behind OTP-style perfect secrecy proofs. -/
theorem GameEquiv.map_uniformSample_bij [SampleableType α] {f : α → α} (hf : Function.Bijective f) :
    GameEquiv (f <$> (uniformSample α : ProbComp α)) (uniformSample α : ProbComp α) :=
  by
  conv_rhs => rw [← id_map (uniformSample α : ProbComp α)]
  exact
    GameEquiv.of_relTriple
      (Relational.relTriple_map (Relational.relTriple_uniformSample_bij hf _ (fun _ => Eq.refl _)))


-- @@ L259-264 verbatim
/-- Game equivalence is a congruence for bind. -/
theorem GameEquiv.bind_congr {g₁ g₂ : OracleComp spec₁ α}
    {f₁ f₂ : α → OracleComp spec₁ β}
    (hg : GameEquiv g₁ g₂) (hf : ∀ a, GameEquiv (f₁ a) (f₂ a)) :
    GameEquiv (g₁ >>= f₁) (g₂ >>= f₂) := by
  rw [GameEquiv, evalSPMF_bind, evalSPMF_bind, hg, funext hf]


-- @@ L266-270 verbatim
/-- Game equivalence is a congruence for map. -/
theorem GameEquiv.map_congr {g₁ g₂ : OracleComp spec₁ α} (f : α → β)
    (hg : GameEquiv g₁ g₂) :
    GameEquiv (f <$> g₁) (f <$> g₂) := by
  rw [GameEquiv, evalSPMF_map, evalSPMF_map, hg]


-- @@ L272-279 verbatim
/-- Advantage bound via TV distance. -/
theorem AdvBound.of_tvDist {game₁ game₂ : OracleComp spec₁ Bool} {ε₁ ε₂ : ℝ}
    (hbound : AdvBound game₁ ε₁) (htv : tvDist game₁ game₂ ≤ ε₂) :
    AdvBound game₂ (ε₁ + ε₂) := by
  have hdiff := abs_probOutput_toReal_sub_le_tvDist game₁ game₂
  unfold AdvBound at *
  rw [abs_le] at *
  constructor <;> linarith [hdiff.1, hdiff.2]


-- @@ L281-286 verbatim
/-- Transfer advantage bounds across equivalent games. -/
theorem AdvBound.of_gameEquiv {g₁ g₂ : OracleComp spec₁ Bool} {ε : ℝ}
    (heq : GameEquiv g₁ g₂) (hbound : AdvBound g₁ ε) :
    AdvBound g₂ ε := by
  unfold AdvBound at *
  rwa [← heq.probOutput_eq]


-- @@ L288-288 verbatim
end OracleComp.ProgramLogic
