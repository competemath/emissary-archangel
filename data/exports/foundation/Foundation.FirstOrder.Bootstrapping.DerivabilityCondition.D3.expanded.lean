module

public import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition.PeanoMinus


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-8 verbatim
/-!
# Hilbert-Bernays-Löb derivability condition $\mathbf{D3}$ and formalized $\Sigma_1$-completeness
-/


-- @@ L10-16 verbatim
namespace FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic

-- `Arithmetic` is intentionally re-opened here even though the ambient namespace
-- already contains it; renaming would break the widely-used public API
-- (`Bootstrapping.Arithmetic.*`). Suppress the new dupNamespace linter for the
-- declarations in this namespace (the option is scoped by `namespace`/`end` and
-- reverts automatically at `end FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic`).

-- @@ L17-17 verbatim
set_option linter.dupNamespace false


-- @@ L19-19 verbatim
open Classical


-- @@ L21-21 verbatim
open FFL.Entailment FFL.Entailment.FiniteContext


-- @@ L23-23 expanded
variable {V : Type*} [ORingStructure V] [ModelsSet (Language.str V oRing) (ISigma 1)]


-- @@ L25-25 expanded
local prefix:max "#'" => Semiterm.bvar (V := V) (L := oRing)


-- @@ L27-27 expanded
local prefix:max "&'" => Semiterm.fvar (V := V) (L := oRing)


-- @@ L29-29 verbatim
local postfix:max "⇞" => Semiterm.shift


-- @@ L31-31 verbatim
local postfix:max "⤉" => Semiformula.shift


-- @@ L33-33 verbatim
local infix:40 " ⤕ " => Semiterm.subst


-- @@ L35-35 verbatim
local infix:40 " ⤔ " => Semiformula.subst


-- @@ L37-37 expanded
variable (T : ArithmeticTheory) [Theory.Δ₁ T] [WeakerThan PeanoMinus T]


-- @@ L39-39 verbatim
variable {T}


-- @@ L41-42 expanded
lemma eq_comm {t₁ t₂ : Term V oRing} :
    Provable (T.internalize V) (t₁ ≐ t₂) → Provable (T.internalize V) (t₂ ≐ t₁) := fun h ↦
  mdp! (eq_symm T _ _) h


-- @@ L44-44 expanded
noncomputable abbrev toNumVec (w : Fin n → V) : SemitermVec V oRing n k :=
  ((vecMap (𝕹·)) w)


-- @@ L46-46 verbatim
variable (T)


-- @@ L48-72 expanded
theorem term_complete {n : ℕ} (t : FirstOrder.ClosedSemiterm oRing n) (w : Fin n → V) :
    Provable (T.internalize V) ((toNumVec w ⤕ GödelQuote.quote t) ≐ 𝕹(t.valb w)) :=
  match t with
  | #z => by simp
  | &x => Empty.elim x
  | .func Language.Zero.zero v => by simp
  | .func Language.One.one v => by simp
  | .func Language.Add.add v =>
    by
    suffices
      Provable (T.internalize V)
        ((toNumVec w ⤕ GödelQuote.quote (v 0)) + (toNumVec w ⤕ GödelQuote.quote (v 1)) ≐
          𝕹((v 0).valb w + (v 1).valb w))
      by simpa [Rew.func, Semiterm.val_func]
    have ih :
      Provable (T.internalize V)
        ((toNumVec w ⤕ GödelQuote.quote (v 0)) + (toNumVec w ⤕ GödelQuote.quote (v 1)) ≐
          𝕹((v 0).valb w) + 𝕹((v 1).valb w)) :=
      mdp! (mdp! (subst_add_eq_add T _ _ _ _) (term_complete (v 0) w)) (term_complete (v 1) w)
    have :
      Provable (T.internalize V)
        (𝕹((v 0).valb w) + 𝕹((v 1).valb w) ≐ 𝕹((v 0).valb w + (v 1).valb w)) :=
      numeral_add T _ _
    exact eq_trans ih this
  | .func Language.Mul.mul v =>
    by
    suffices
      Provable (T.internalize V)
        ((toNumVec w ⤕ GödelQuote.quote (v 0)) * (toNumVec w ⤕ GödelQuote.quote (v 1)) ≐
          𝕹((v 0).valb w * (v 1).valb w))
      by simpa [Rew.func, Semiterm.val_func]
    have ih :
      Provable (T.internalize V)
        ((toNumVec w ⤕ GödelQuote.quote (v 0)) * (toNumVec w ⤕ GödelQuote.quote (v 1)) ≐
          𝕹((v 0).valb w) * 𝕹((v 1).valb w)) :=
      mdp! (mdp! (subst_mul_eq_mul T _ _ _ _) (term_complete (v 0) w)) (term_complete (v 1) w)
    have :
      Provable (T.internalize V)
        (𝕹((v 0).valb w) * 𝕹((v 1).valb w) ≐ 𝕹((v 0).valb w * (v 1).valb w)) :=
      numeral_mul T _ _
    exact eq_trans ih this


-- @@ L74-74 verbatim
open FirstOrder.Arithmetic


-- @@ L76-150 expanded
theorem bold_sigma_one_complete {n} {φ : ArithmeticSemisentence n}
    (hp : Hierarchy SigmaSymbol.sigma 1 φ) {w} :
    (@Evalb _ V _ _ w) φ → Provable (T.internalize V) (toNumVec w ⤔ GödelQuote.quote φ) :=
  by
  revert w
  apply sigma₁_induction' hp
  case hVerum => intro n; simp
  case hFalsum => intro n; simp
  case hEQ =>
    intro n t₁ t₂ w h
    suffices
      Provable (T.internalize V)
        ((toNumVec w ⤕ GödelQuote.quote t₁) ≐ (toNumVec w ⤕ GödelQuote.quote t₂))
      by simpa [Sentence.typed_quote_def]
    have : t₁.valb w = t₂.valb w := by simpa using h
    have h₀ : Provable (T.internalize V) (𝕹(t₁.valb w) ≐ 𝕹(t₂.valb w)) := by simp [this]
    have h₁ : Provable (T.internalize V) ((toNumVec w ⤕ GödelQuote.quote t₁) ≐ 𝕹(t₁.valb w)) :=
      term_complete T t₁ w
    have h₂ : Provable (T.internalize V) ((toNumVec w ⤕ GödelQuote.quote t₂) ≐ 𝕹(t₂.valb w)) :=
      term_complete T t₂ w
    exact eq_trans (eq_trans h₁ h₀) (eq_comm h₂)
  case hNEQ =>
    intro n t₁ t₂ w h
    suffices
      Provable (T.internalize V)
        ((toNumVec w ⤕ GödelQuote.quote t₁) ≉ (toNumVec w ⤕ GödelQuote.quote t₂))
      by simpa [Sentence.typed_quote_def]
    have : t₁.valb w ≠ t₂.valb w := by simpa using h
    have h₀ : Provable (T.internalize V) (𝕹(t₁.valb w) ≉ 𝕹(t₂.valb w)) := by
      simpa using numeral_ne T this
    have h₁ : Provable (T.internalize V) ((toNumVec w ⤕ GödelQuote.quote t₁) ≐ 𝕹(t₁.valb w)) :=
      term_complete T t₁ w
    have h₂ : Provable (T.internalize V) ((toNumVec w ⤕ GödelQuote.quote t₂) ≐ 𝕹(t₂.valb w)) :=
      term_complete T t₂ w
    exact mdp! (mdp! (mdp! (subst_ne T _ _ _ _) (eq_comm h₁)) (eq_comm h₂)) h₀
  case hLT =>
    intro n t₁ t₂ w h
    suffices
      Provable (T.internalize V)
        ((toNumVec w ⤕ GödelQuote.quote t₁) <' (toNumVec w ⤕ GödelQuote.quote t₂))
      by simpa [Sentence.typed_quote_def]
    have : t₁.valb w < t₂.valb w := by simpa using h
    have h₀ : Provable (T.internalize V) (𝕹(t₁.valb w) <' 𝕹(t₂.valb w)) := by
      simpa using numeral_lt T this
    have h₁ : Provable (T.internalize V) ((toNumVec w ⤕ GödelQuote.quote t₁) ≐ 𝕹(t₁.valb w)) :=
      term_complete T t₁ w
    have h₂ : Provable (T.internalize V) ((toNumVec w ⤕ GödelQuote.quote t₂) ≐ 𝕹(t₂.valb w)) :=
      term_complete T t₂ w
    exact mdp! (mdp! (mdp! (subst_lt T _ _ _ _) (eq_comm h₁)) (eq_comm h₂)) h₀
  case hNLT =>
    intro n t₁ t₂ w h
    suffices
      Provable (T.internalize V)
        ((toNumVec w ⤕ GödelQuote.quote t₁) ≮' (toNumVec w ⤕ GödelQuote.quote t₂))
      by simpa [Sentence.typed_quote_def]
    have : t₁.valb w ≥ t₂.valb w := by simpa using h
    have h₀ : Provable (T.internalize V) (𝕹(t₁.valb w) ≮' 𝕹(t₂.valb w)) := by
      simpa using numeral_nlt T this
    have h₁ : Provable (T.internalize V) ((toNumVec w ⤕ GödelQuote.quote t₁) ≐ 𝕹(t₁.valb w)) :=
      term_complete T t₁ w
    have h₂ : Provable (T.internalize V) ((toNumVec w ⤕ GödelQuote.quote t₂) ≐ 𝕹(t₂.valb w)) :=
      term_complete T t₂ w
    exact mdp! (mdp! (mdp! (subst_nlt T _ _ _ _) (eq_comm h₁)) (eq_comm h₂)) h₀
  case hAnd =>
    intro n φ ψ _ _ ihφ ihψ w h
    have H : (@Evalb _ V _ _ w) φ ∧ (@Evalb _ V _ _ w) ψ := by simpa using h
    simpa using K_intro (ihφ H.1) (ihψ H.2)
  case hOr =>
    intro n φ ψ _ _ ihφ ihψ w h
    suffices
      Provable (T.internalize V)
        binop% HVee.hVee (toNumVec w ⤔ GödelQuote.quote φ) (toNumVec w ⤔ GödelQuote.quote ψ)
      by simpa
    have : (@Evalb _ V _ _ w) φ ∨ (@Evalb _ V _ _ w) ψ := by simpa using h
    rcases this with (h | h)
    · apply A_intro_left (ihφ h)
    · apply A_intro_right (ihψ h)
  case hBall =>
    intro n t φ _ ih w h
    have h : ∀ i < t.valb w, (@Evalb _ V _ _ (vecCons i w)) φ := by simpa using h
    suffices
      Provable (T.internalize V)
        (((toNumVec w).q ⤔ GödelQuote.quote φ).ball (toNumVec w ⤕ GödelQuote.quote t))
      by
      simpa [Semiterm.empty_typed_quote_def, ← Rew.emb_bShift_term, Semiformula.ball, ball,
        Semiformula.imp_def]
    have : Provable (T.internalize V) (((toNumVec w).q ⤔ GödelQuote.quote φ).ball 𝕹(t.valb w)) :=
      by
      apply ball_intro
      intro i hi
      suffices Provable (T.internalize V) (toNumVec (vecCons i w) ⤔ GödelQuote.quote φ) by
        simpa [Semiformula.substs_substs, Matrix.vecMap_vecMap_comp']
      exact ih (h i hi)
    exact
      mdp!
        (mdp! (ball_replace T ((toNumVec w).q ⤔ GödelQuote.quote φ) _ _)
          (eq_comm <| term_complete T t w))
        this
  case hExs =>
    intro n φ hφ ih w hφ
    have : ∃ a, (@Evalb _ V _ _ (vecCons a w)) φ := by simpa using hφ
    rcases this with ⟨i, hφ⟩
    suffices Provable (T.internalize V) (ExsQuantifier.exs ((toNumVec w).q ⤔ GödelQuote.quote φ)) by
      simpa
    apply TProof.exs! (𝕹 i)
    suffices Provable (T.internalize V) (toNumVec (vecCons i w) ⤔ GödelQuote.quote φ) by
      simpa [Semiformula.substs_substs, Matrix.vecMap_vecMap_comp']
    exact ih hφ


-- @@ L152-157 expanded
theorem sigma_one_provable_of_models {σ : ArithmeticSentence}
    (hσ : Hierarchy SigmaSymbol.sigma 1 σ) :
    Models (Language.str V oRing) σ → Provable (T.internalize V) (GödelQuote.quote σ) :=
  by
  intro h
  have : Provable (T.internalize V) (toNumVec ![] ⤔ GödelQuote.quote σ) :=
    bold_sigma_one_complete T hσ (by simpa [models_iff] using h)
  simpa using this


-- @@ L159-163 expanded
/-- Hilbert–Bernays provability condition D3 -/
theorem sigma_one_complete {σ : ArithmeticSentence} (hσ : Hierarchy SigmaSymbol.sigma 1 σ) :
    Models (Language.str V oRing) σ → Provable T (GödelQuote.quote σ : V) := fun h ↦ by
  simpa [tprovable_iff_provable] using! Bootstrapping.Arithmetic.sigma_one_provable_of_models T hσ h


-- @@ L165-167 expanded
theorem provable_internalize {σ : ArithmeticSentence} :
    Provable T (GödelQuote.quote σ : V) → Provable T (GödelQuote.quote (provabilityPred T σ) : V) :=
  by
  simpa [models_iff] using sigma_one_complete (V := V) (T := T) (σ := provabilityPred T σ) (by simp)


-- @@ L169-169 verbatim
end FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
