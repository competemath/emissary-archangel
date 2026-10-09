import OAI.Computability.FourierCircuit.Core


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
section

-- @@ L6-6 verbatim
namespace ExactFourier

-- @@ L7-10 verbatim
/-- A permutation matrix times an invertible diagonal matrix, literally P D. -/
def IsMonomial {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) : Prop :=
  ∃ (σ : Equiv.Perm (Fin q)) (d : Fin q → ℂ),
    (∀ j, d j ≠ 0) ∧ ∀ i j, A i j = if i = σ j then d j else 0


-- @@ L12-17 verbatim
/-- A call on an ordered tuple of distinct coordinates; all other values are fixed. -/
noncomputable def embeddedCall {q w : ℕ} (A : Matrix (Fin q) (Fin q) ℂ)
    (e : Fin q ↪ Fin w) : Matrix (Fin w) (Fin w) ℂ := by
  classical
  exact fun u v => (∑ i, ∑ j, if e i = u then (if e j = v then A i j else 0) else 0) +
    if u = v ∧ ¬ ∃ i, e i = u then 1 else 0


-- @@ L19-22 verbatim
/-- Only forward calls to the specified A are allowed. -/
inductive WordStep {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (w : ℕ) where
  | monomial (M : Matrix (Fin w) (Fin w) ℂ) (hM : IsMonomial M)
  | call (e : Fin q ↪ Fin w)


-- @@ L24-27 verbatim
noncomputable def WordStep.matrix {q w : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} :
    WordStep A w → Matrix (Fin w) (Fin w) ℂ
  | .monomial M _ => M
  | .call e => embeddedCall A e


-- @@ L29-31 verbatim
def WordStep.calls {q w : ℕ} {A : Matrix (Fin q) (Fin q) ℂ} : WordStep A w → ℕ
  | .monomial _ _ => 0
  | .call _ => 1


-- @@ L33-36 verbatim
/-- Stored chronologically, so a new step left-multiplies earlier steps. -/
noncomputable def wordMatrix {q w : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (W : List (WordStep A w)) : Matrix (Fin w) (Fin w) ℂ :=
  (W.map WordStep.matrix).reverse.prod


-- @@ L38-39 verbatim
def wordCalls {q w : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (W : List (WordStep A w)) : ℕ := (W.map WordStep.calls).sum


-- @@ L41-45 verbatim
/-- A fixed coordinate relabeling of the ordinary Kronecker tensor power. -/
noncomputable def tensorCoordinates (q b : ℕ) : Fin (q ^ b) ≃ (Fin b → Fin q) := by
  classical
  exact (Equiv.cast (by simp) : Fin (q ^ b) ≃ Fin (Fintype.card (Fin b → Fin q))) |>.trans
    (Fintype.equivFin (Fin b → Fin q)).symm


-- @@ L47-49 verbatim
noncomputable def tensorPower {q : ℕ} (A : Matrix (Fin q) (Fin q) ℂ) (b : ℕ) :
    Matrix (Fin (q ^ b)) (Fin (q ^ b)) ℂ :=
  fun i j => ∏ k : Fin b, A (tensorCoordinates q b i k) (tensorCoordinates q b j k)


-- @@ L51-54 verbatim
def FiniteWinStatement : Prop :=
  ∃ (q : ℕ) (A : Matrix (Fin q) (Fin q) ℂ), IsUnit A ∧ ¬ IsMonomial A ∧
    ∃ b : ℕ, 2 ≤ b ∧ ∃ W : List (WordStep A (q ^ b)),
      wordMatrix W = tensorPower A b ∧ wordCalls W < b * q ^ (b - 1)


-- @@ L56-56 verbatim
end ExactFourier


-- @@ L58-58 verbatim
end


-- @@ L60-60 verbatim
end OAI
