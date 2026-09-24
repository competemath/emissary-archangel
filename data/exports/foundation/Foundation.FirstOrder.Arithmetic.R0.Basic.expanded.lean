module

public import Foundation.FirstOrder.Arithmetic.Basic


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-9 verbatim
/-!
# Cobham's theory $\mathsf{R_0}$

-/


-- @@ L11-11 verbatim
noncomputable section


-- @@ L13-13 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L15-20 verbatim
inductive R0 : ArithmeticTheory
  | equal : ∀ φ ∈ 𝗘𝗤 ℒₒᵣ, R0 φ
  | Ω₁ (n m : ℕ) : R0 “↑n + ↑m = ↑(n + m)”
  | Ω₂ (n m : ℕ) : R0 “↑n * ↑m = ↑(n * m)”
  | Ω₃ (n m : ℕ) : n ≠ m → R0 “↑n ≠ ↑m”
  | Ω₄ (n : ℕ) : R0 “∀ x, x < ↑n ↔ ⋁ i < n, x = ↑i”


-- @@ L22-22 verbatim
notation "𝗥₀" => R0


-- @@ L24-24 verbatim
namespace R0


-- @@ L26-26 verbatim
instance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗥₀ := Entailment.WeakerThan.ofSubset <| fun φ hp ↦ R0.equal φ hp


-- @@ L28-35 verbatim
instance : ℕ↓[ℒₒᵣ] ⊧* 𝗥₀ := ⟨by
  intro σ h
  rcases h <;> try { simp [models_iff]; done }
  case equal h =>
    have : ℕ↓[ℒₒᵣ] ⊧* (𝗘𝗤 ℒₒᵣ : ArithmeticTheory) := inferInstance
    simpa [models_iff] using models_theory_iff.mp this _ h
  case Ω₃ h =>
    simpa [models_iff, ←le_iff_eq_or_lt] using h⟩


-- @@ L37-37 verbatim
end R0


-- @@ L39-39 verbatim
section model


-- @@ L41-41 verbatim
variable {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝗥₀]


-- @@ L43-61 verbatim
open Language ORingStructure

lemma numeral_add_numeral (n m : ℕ) : (numeral n : M) + numeral m = numeral (n + m) := by
  simpa [models_iff] using Theory.models M _ (R0.Ω₁ n m)

lemma numeral_mul_numeral (n m : ℕ) : (numeral n : M) * numeral m = numeral (n * m) := by
  simpa [models_iff] using Theory.models M _ (R0.Ω₂ n m)

lemma numeral_ne_numeral_of_ne {n m : ℕ} (h : n ≠ m) : (numeral n : M) ≠ numeral m := by
  simpa [models_iff] using Theory.models M _ (R0.Ω₃ n m h)

lemma lt_numeral_iff {x : M} {n : ℕ} : x < numeral n ↔ ∃ i : Fin n, x = numeral i := by
  have := by simpa [models_iff] using Theory.models M _ (R0.Ω₄ n)
  constructor
  · intro hx
    rcases (this x).mp hx with ⟨i, hi, rfl⟩
    exact ⟨⟨i, hi⟩, by simp⟩
  · rintro ⟨i, rfl⟩
    exact (this (numeral i)).mpr ⟨i, by simp, rfl⟩


-- @@ L63-64 verbatim
@[simp] lemma numeral_inj_iff {n m : ℕ} : (numeral n : M) = numeral m ↔ n = m :=
  ⟨by contrapose; exact numeral_ne_numeral_of_ne, by rintro rfl; rfl⟩


-- @@ L66-72 verbatim
@[simp] lemma numeral_lt_numeral_iff : (numeral n : M) < numeral m ↔ n < m :=
  ⟨by contrapose
      intro h H
      rcases lt_numeral_iff.mp H with ⟨i, hi⟩
      rcases numeral_inj_iff.mp hi
      exact (lt_self_iff_false m).mp (lt_of_le_of_lt (Nat.le_of_not_gt h) i.prop),
   fun h ↦ lt_numeral_iff.mpr ⟨⟨n, h⟩, by simp⟩⟩


-- @@ L74-116 verbatim
open Hierarchy

lemma val_numeral {n ξ} (bv : Fin n → ℕ) (fv : ξ → ℕ) (t : ArithmeticSemiterm ξ n) :
    t.val (M := M) (numeral ∘ bv) (numeral ∘ fv) = numeral (t.val bv fv) :=
  match t with
  |                         #_ => by simp
  |                         &_ => by simp
  | .func Language.Zero.zero _ => by simp [Matrix.empty_eq]
  |   .func Language.One.one _ => by simp [Matrix.empty_eq]
  |   .func Language.Add.add v => by simp [Semiterm.val_func, val_numeral _ _ (v 0), val_numeral _ _ (v 1), numeral_add_numeral]
  |   .func Language.Mul.mul v => by simp [Semiterm.val_func, val_numeral _ _ (v 0), val_numeral _ _ (v 1), numeral_mul_numeral]

lemma bold_sigma_one_completeness {n} {φ : ArithmeticSemiformula ξ n} (hp : Hierarchy 𝚺 1 φ) {bv : Fin n → ℕ} {fv : ξ → ℕ} :
    φ.Eval bv fv → φ.Eval (M := M) (numeral ∘ bv) (numeral ∘ fv) := by
  revert bv
  apply sigma₁_induction' hp
  case hVerum => simp
  case hFalsum => simp
  case hEQ => intro n t₁ t₂ e; simp [val_numeral]
  case hNEQ => intro n t₁ t₂ e; simp [val_numeral]
  case hLT => intro n t₁ t₂ e; simp [val_numeral]
  case hNLT => intro n t₁ t₂ e; simp [val_numeral]
  case hAnd => simp; grind
  case hOr => simp; grind
  case hBall =>
    intro n t φ _ ihp bv
    suffices
      (∀ x < t.val bv fv, (φ.Eval (x :> bv) fv)) →
       ∀ x < numeral (t.val bv fv), (φ.Eval (x :> numeral ∘ bv) (numeral ∘ fv)) by
      simpa [val_numeral]
    intro hp x hx
    rcases lt_numeral_iff.mp hx with ⟨x, rfl⟩
    simpa [Matrix.comp_vecCons''] using ihp (hp x (by simp))
  case hExs =>
    simp only [Semiformula.eval_ex, Nat.succ_eq_add_one, forall_exists_index]
    intro n φ _ ihp e x hp
    exact ⟨numeral x, by simpa [Matrix.comp_vecCons''] using ihp hp⟩

lemma R0.model_complete {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
    ℕ↓[ℒₒᵣ] ⊧ σ → M↓[ℒₒᵣ] ⊧ σ := by
  suffices σ.Evalb (M := ℕ) ![] → σ.Evalb (M := M) ![] by simpa [models_iff]
  intro h
  simpa [Matrix.empty_eq, Empty.eq_elim] using bold_sigma_one_completeness hσ h


-- @@ L118-127 verbatim
variable (M)

lemma nat_extention_sigmaOne {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
    ℕ↓[ℒₒᵣ] ⊧ σ → M↓[ℒₒᵣ] ⊧ σ := fun h ↦ by
  simpa [Matrix.empty_eq] using R0.model_complete (M := M) hσ h

lemma nat_extention_piOne {σ : ArithmeticSentence} (hσ : Hierarchy 𝚷 1 σ) :
    M↓[ℒₒᵣ] ⊧ σ → ℕ↓[ℒₒᵣ] ⊧ σ := by
  contrapose
  simpa using nat_extention_sigmaOne M (σ := ∼σ) (by simpa using hσ)


-- @@ L129-133 verbatim
variable {M}

lemma bold_sigma_one_completeness' {n} {σ : ArithmeticSemisentence n} (hσ : Hierarchy 𝚺 1 σ) {bv} :
    σ.Evalb (M := ℕ) bv → σ.Evalb (M := M) (numeral ∘ bv) := fun h ↦ by
  simpa [Empty.eq_elim] using bold_sigma_one_completeness (M := M) (φ := σ) hσ (fv := Empty.elim) (bv := bv) h


-- @@ L135-137 verbatim
instance consistent : Entailment.Consistent 𝗥₀ :=
  let : ℕ↓[ℒₒᵣ] ⊧* 𝗥₀ := inferInstance
  Sound.consistent_of_satisfiable ⟨_, this⟩


-- @@ L139-139 verbatim
end model


-- @@ L141-141 verbatim
variable {T : ArithmeticTheory} [𝗥₀ ⪯ T]


-- @@ L143-148 verbatim
theorem sigma_one_completeness {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
    ℕ↓[ℒₒᵣ] ⊧ σ → T ⊢ σ := fun H =>
  haveI : 𝗘𝗤 _ ⪯ T := Entailment.WeakerThan.trans (𝓣 := 𝗥₀) inferInstance inferInstance
  complete.{0} _ _ <| fun M _ _ ↦ by
    have : M↓[ℒₒᵣ] ⊧* 𝗥₀ := ModelsTheory.of_provably_subtheory M 𝗥₀ T inferInstance
    exact R0.model_complete hσ H


-- @@ L150-154 verbatim
open Classical in
theorem sigma_one_completeness_iff [T.SoundOnHierarchy 𝚺 1] {σ : ArithmeticSentence} (hσ : Hierarchy 𝚺 1 σ) :
    ℕ↓[ℒₒᵣ] ⊧ σ ↔ T ⊢ σ :=
  haveI : 𝗥₀ ⪯ T := Entailment.WeakerThan.trans (𝓣 := T) inferInstance inferInstance
  ⟨fun h ↦ sigma_one_completeness hσ h, fun h ↦ T.soundOnHierarchy 𝚺 1 h (by simp [hσ])⟩


-- @@ L156-160 verbatim
/-!
## Unprovable theorems of $\mathsf{R}_0$

$\omega + 1$ (the structure of order type $\omega + 1$) is a models of $\mathsf{R}_0$.
-/


-- @@ L162-162 verbatim
/-! ω + 1 models 𝗥₀ -/

-- @@ L163-163 verbatim
namespace R0.Countermodel


-- @@ L165-165 verbatim
def OmegaAddOne := Option ℕ


-- @@ L167-167 verbatim
namespace OmegaAddOne


-- @@ L169-169 verbatim
instance : NatCast OmegaAddOne := ⟨fun i ↦ .some i⟩


-- @@ L171-171 verbatim
instance (n : ℕ) : OfNat OmegaAddOne n := ⟨.some n⟩


-- @@ L173-173 verbatim
instance : Top OmegaAddOne := ⟨.none⟩


-- @@ L175-190 verbatim
instance : ORingStructure OmegaAddOne where
  add a b :=
    match a, b with
    | .some i, .some j => i + j
    |   .none,       _ => 0
    |       _,   .none => 0
  mul a b :=
    match a, b with
    | .some i, .some j => (i * j)
    |   .none,       _ => 0
    |       _,   .none => 0
  lt a b :=
    match a, b with
    | .some i, .some j => i < j
    |   .none,       _ => False
    | .some _,   .none => True


-- @@ L192-192 verbatim
@[simp] lemma coe_zero : (↑(0 : ℕ) : OmegaAddOne) = 0 := rfl


-- @@ L194-194 verbatim
@[simp] lemma coe_one : (↑(1 : ℕ) : OmegaAddOne) = 1 := rfl


-- @@ L196-196 verbatim
@[simp] lemma coe_add (a b : ℕ) : ↑(a + b) = ((↑a + ↑b) : OmegaAddOne) := rfl


-- @@ L198-198 verbatim
@[simp] lemma coe_mul (a b : ℕ) : ↑(a * b) = ((↑a * ↑b) : OmegaAddOne) := rfl


-- @@ L200-200 verbatim
@[simp] lemma lt_coe_iff (n m : ℕ) : (n : OmegaAddOne) < (m : OmegaAddOne) ↔ n < m := by rfl


-- @@ L202-202 verbatim
@[simp] lemma not_top_lt (n : ℕ) : ¬⊤ < (n : OmegaAddOne) := by rintro ⟨⟩


-- @@ L204-204 verbatim
@[simp] lemma lt_top (n : ℕ) : (n : OmegaAddOne) < ⊤ := by trivial


-- @@ L206-209 verbatim
@[simp] lemma top_add_zero : (⊤ : OmegaAddOne) + 0 = 0 := by rfl

lemma exists_add_zero_ne_self : ∃ x : OmegaAddOne, x + 0 ≠ x :=
  ⟨⊤, by simp⟩


-- @@ L211-215 verbatim
@[simp] lemma numeral_eq (n : ℕ) : (ORingStructure.numeral n : OmegaAddOne) = n :=
  match n with
  |     0 => rfl
  |     1 => rfl
  | n + 2 => by simp [ORingStructure.numeral, numeral_eq (n + 1)]; rfl


-- @@ L217-217 verbatim
@[simp] lemma coe_inj_iff (n m : ℕ) : (↑n : OmegaAddOne) = (↑m : OmegaAddOne) ↔ n = m := Option.some_inj


-- @@ L219-223 verbatim
def cases' {P : OmegaAddOne → Sort*}
    (nat : (n : ℕ) → P n)
    (top : P ⊤) : ∀ x : OmegaAddOne, P x
  | .some n => nat n
  |   .none => top


-- @@ L225-235 verbatim
set_option linter.flexible false in
instance : OmegaAddOne↓[ℒₒᵣ] ⊧* 𝗥₀ := ⟨by
  intro σ h
  rcases h <;> simp [models_iff]
  case equal h =>
    have : OmegaAddOne↓[ℒₒᵣ] ⊧* (𝗘𝗤 _ : ArithmeticTheory) := inferInstance
    exact models_theory_iff.mp this _ h
  case Ω₃ h => exact h
  case Ω₄ n =>
    intro x
    cases x using cases' <;> simp⟩


-- @@ L237-237 verbatim
end OmegaAddOne


-- @@ L239-243 verbatim
end Countermodel

lemma unprovable_addZero : 𝗥₀ ⊬ “∀ x, x + 0 = x” :=
  unprovable_of_countermodel _ (M := Countermodel.OmegaAddOne) <| by
    simpa [notModels_iff] using Countermodel.OmegaAddOne.exists_add_zero_ne_self


-- @@ L245-245 verbatim
end R0


-- @@ L247-247 verbatim
end FFL.FirstOrder.Arithmetic


-- @@ L249-249 verbatim
end
