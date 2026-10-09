import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators ComplexOrder


-- @@ L8-8 verbatim
namespace ThresholdParallelRepetition


-- @@ L10-14 verbatim
structure Game (x y a b : ℕ) where
  questionProb : Fin (x + 1) × Fin (y + 1) → ℝ
  questionProb_nonneg : ∀ z, 0 ≤ questionProb z
  questionProb_sum : ∑ z, questionProb z = 1
  accepts : Fin (x + 1) → Fin (y + 1) → Fin (a + 1) → Fin (b + 1) → Bool


-- @@ L16-26 verbatim
structure Strategy (X Y A B : Type) [Fintype A] [Fintype B] where
  dimA : ℕ
  dimB : ℕ
  state : Fin (dimA + 1) × Fin (dimB + 1) → ℂ
  state_unit : ∑ i, Complex.normSq (state i) = 1
  alice : X → A → Matrix (Fin (dimA + 1)) (Fin (dimA + 1)) ℂ
  bob : Y → B → Matrix (Fin (dimB + 1)) (Fin (dimB + 1)) ℂ
  alice_pos : ∀ x a, (alice x a).PosSemidef
  bob_pos : ∀ y b, (bob y b).PosSemidef
  alice_total : ∀ x, ∑ a, alice x a = 1
  bob_total : ∀ y, ∑ b, bob y b = 1


-- @@ L28-31 verbatim
def Strategy.born {X Y A B : Type} [Fintype A] [Fintype B]
    (S : Strategy X Y A B) (x : X) (y : Y) (a : A) (b : B) : ℝ :=
  ∑ i, ∑ j, (star (S.state i) *
    (S.alice x a i.1 j.1 * S.bob y b i.2 j.2) * S.state j).re


-- @@ L33-34 verbatim
abbrev SingleStrategy (x y a b : ℕ) :=
  Strategy (Fin (x + 1)) (Fin (y + 1)) (Fin (a + 1)) (Fin (b + 1))


-- @@ L36-39 verbatim
def successProbability {x y a b : ℕ} (G : Game x y a b) (S : SingleStrategy x y a b) : ℝ :=
  ∑ z : Fin (x + 1) × Fin (y + 1), G.questionProb z *
    ∑ w : Fin (a + 1) × Fin (b + 1),
      if G.accepts z.1 z.2 w.1 w.2 then S.born z.1 z.2 w.1 w.2 else 0


-- @@ L41-42 verbatim
def entangledValue {x y a b : ℕ} (G : Game x y a b) : ℝ :=
  sSup (Set.range (successProbability G))


-- @@ L44-46 verbatim
abbrev RepeatedStrategy (x y a b k : ℕ) :=
  Strategy (Fin k → Fin (x + 1)) (Fin k → Fin (y + 1))
    (Fin k → Fin (a + 1)) (Fin k → Fin (b + 1))


-- @@ L48-51 verbatim
def wins {x y a b k : ℕ} (G : Game x y a b)
    (xs : Fin k → Fin (x + 1)) (ys : Fin k → Fin (y + 1))
    (as : Fin k → Fin (a + 1)) (bs : Fin k → Fin (b + 1)) : ℕ :=
  ∑ i, if G.accepts (xs i) (ys i) (as i) (bs i) then 1 else 0


-- @@ L53-59 verbatim
def thresholdProbability {x y a b k : ℕ} (G : Game x y a b) (δ : ℝ)
    (S : RepeatedStrategy x y a b k) : ℝ :=
  ∑ xs : Fin k → Fin (x + 1), ∑ ys : Fin k → Fin (y + 1),
    (∏ i, G.questionProb (xs i, ys i)) *
      ∑ as : Fin k → Fin (a + 1), ∑ bs : Fin k → Fin (b + 1),
        if ⌈(entangledValue G + δ) * (k : ℝ)⌉₊ ≤ wins G xs ys as bs
        then S.born xs ys as bs else 0


-- @@ L61-62 verbatim
def thresholdValue {x y a b k : ℕ} (G : Game x y a b) (δ : ℝ) : ℝ :=
  sSup (Set.range (thresholdProbability (k := k) G δ))


-- @@ L64-64 verbatim
end ThresholdParallelRepetition


-- @@ L66-66 verbatim
end


-- @@ L68-68 verbatim
end OAI
