module

public import Foundation.FirstOrder.Incompleteness.RosserProvability
public import Foundation.FirstOrder.Arithmetic.HFS.Superexp


-- @@ L6-6 verbatim
@[expose] public section

-- @@ L7-12 verbatim
/-!
# Provability with restricted proof size

Some results to consider provable predicate modified to state that "provable by proof whose Gödel number is less than `f e`" for a `𝚺₁`-definable bounding function `f` (where `e` is an arbitary meta natural number).
The results with `f = Superexp.superexp` recover "provable by proof whose Gödel number is less than the superexponential of `e`".
-/


-- @@ L14-14 verbatim
namespace FFL.FirstOrder


-- @@ L16-16 verbatim
open FirstOrder Arithmetic

-- @@ L17-17 verbatim
open PeanoMinus ISigma0 ISigma1 Bootstrapping Derivation


-- @@ L19-19 verbatim
namespace Theory


-- @@ L21-21 verbatim
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

-- @@ L22-22 verbatim
variable {L : Language} [L.Encodable] [L.LORDefinable]


-- @@ L24-24 verbatim
variable {T U : Theory L} [T.Δ₁] [U.Δ₁]


-- @@ L26-27 verbatim
/-- Provability with restriction of proof size -/
def RestrictedProvable (f : V → V) (e : ℕ) (T : Theory L) [T.Δ₁] (φ : V) := ∃ d < f (ORingStructure.numeral e), Arithmetic.Bootstrapping.Proof T d φ


-- @@ L29-29 verbatim
noncomputable def restrictedProvable (fDef : 𝚺₁.Semisentence 2) (e : ℕ) : 𝚷₁.Semisentence 1 := .mkPi “φ. ∀ E, !fDef E !e → ∃ d < E, !(proof T).pi d φ”


-- @@ L31-31 verbatim
noncomputable abbrev restrictedProvabilityPred (fDef : 𝚺₁.Semisentence 2) (e : ℕ) (σ : Sentence L) : ArithmeticSentence := (T.restrictedProvable fDef e).val/[⌜σ⌝]


-- @@ L33-35 verbatim
instance RestrictedProvable.defined {f : V → V} {fDef : 𝚺₁.Semisentence 2} [𝚺₁-Function₁[V] f via fDef] {e} :
    𝚷₁-Predicate[V] (T.RestrictedProvable f e) via (T.restrictedProvable fDef e) where
  defined {φ} := by simp [Theory.restrictedProvable, Theory.RestrictedProvable];


-- @@ L37-38 verbatim
/-- Gödel sentence by restricted provability -/
noncomputable abbrev restrictedGödel (fDef : 𝚺₁.Semisentence 2) (e : ℕ) (T : Theory L) [T.Δ₁] : ArithmeticSentence := fixedpoint (∼(T.restrictedProvable fDef e))


-- @@ L40-41 verbatim
private noncomputable abbrev restrictedGödel' (fDef : 𝚺₁.Semisentence 2) (e : ℕ) (T : Theory L) [T.Δ₁] : ArithmeticSentence :=
  ∼(T.restrictedProvable fDef e).val/[⌜restrictedGödel fDef e T⌝]


-- @@ L43-43 verbatim
private lemma restrictedGödel'_sigmaOne {fDef : 𝚺₁.Semisentence 2} {e : ℕ} : Hierarchy 𝚺 1 (T.restrictedGödel' fDef e) := by definability;


-- @@ L45-45 verbatim
end Theory



-- @@ L48-48 verbatim
namespace Arithmetic


-- @@ L50-50 verbatim
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

-- @@ L51-51 verbatim
variable {T U : ArithmeticTheory} [T.Δ₁]

-- @@ L52-54 verbatim
variable {fDef : 𝚺₁.Semisentence 2} {e : ℕ}

lemma def_restrictedGödel [𝗜𝚺₁ ⪯ U] : U ⊢ T.restrictedGödel fDef e 🡘 (∼(T.restrictedProvable fDef e).val)/[⌜T.restrictedGödel fDef e⌝] := diagonal _


-- @@ L56-56 verbatim
private lemma def_restrictedGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ T.restrictedGödel' fDef e 🡘 (∼(T.restrictedProvable fDef e).val)/[⌜T.restrictedGödel fDef e⌝] := by simp;


-- @@ L58-61 verbatim
private lemma provable_E_restrictedGödel_restrictedGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ T.restrictedGödel fDef e 🡘 T.restrictedGödel' fDef e := by
  apply Entailment.E_trans;
  . exact def_restrictedGödel;
  . exact Entailment.E_symm $ def_restrictedGödel';


-- @@ L63-64 verbatim
private lemma iff_provable_restrictedGödel_provable_restrictedGödel' [𝗜𝚺₁ ⪯ U] : U ⊢ (T.restrictedGödel fDef e) ↔ U ⊢ (T.restrictedGödel' fDef e) := by
  apply Entailment.iff_of_E provable_E_restrictedGödel_restrictedGödel';


-- @@ L66-74 verbatim
private lemma iff_true_restrictedGödel_true_restrictedGödel' : ℕ↓[ℒₒᵣ] ⊧ (T.restrictedGödel fDef e) ↔ ℕ↓[ℒₒᵣ] ⊧ (T.restrictedGödel' fDef e) := by
  apply Semantics.models_iff.mp;
  apply models_of_provable (T := 𝗜𝚺₁) inferInstance;
  apply provable_E_restrictedGödel_restrictedGödel';

lemma models_restrictedGödel (f : V → V) [𝚺₁-Function₁[V] f via fDef] :
    V↓[ℒₒᵣ] ⊧ T.restrictedGödel fDef e ↔ ∀ x : V, x < f (ORingStructure.numeral e) → ¬Arithmetic.Bootstrapping.Proof T x (⌜T.restrictedGödel fDef e⌝) := by
  apply Iff.trans $ Semantics.models_iff.mp $ models_of_provable (T := 𝗜𝚺₁) inferInstance $ def_restrictedGödel;
  simp [models_iff, Theory.RestrictedProvable]


-- @@ L76-78 verbatim
private lemma models_neg_restrictedGödel (f : V → V) [𝚺₁-Function₁[V] f via fDef] :
    ¬V↓[ℒₒᵣ] ⊧ T.restrictedGödel fDef e ↔ ∃ x : V, x < f (ORingStructure.numeral e) ∧ Arithmetic.Bootstrapping.Proof T x (⌜T.restrictedGödel fDef e⌝) := by
  simpa using (models_restrictedGödel f).not;


-- @@ L80-82 verbatim
variable [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]

/- Gödel sentence by restricted provability is true. -/

-- @@ L83-93 verbatim
theorem true_restrictedGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] : ℕ↓[ℒₒᵣ] ⊧ T.restrictedGödel fDef e := by
  by_contra hC;
  obtain ⟨e, _, he⟩ := models_neg_restrictedGödel f (e := e) |>.mp hC;
  apply hC;
  apply iff_true_restrictedGödel_true_restrictedGödel'.mpr;
  apply ArithmeticTheory.soundOnHierarchy T _ _ ?_ T.restrictedGödel'_sigmaOne;
  apply iff_provable_restrictedGödel_provable_restrictedGödel'.mp;
  apply Arithmetic.Bootstrapping.provable_of_standard_proof (T := T) (V := ℕ) (n := e);
  simpa using he;

/- Gödel sentence by restricted provability is provable. -/

-- @@ L94-97 verbatim
theorem provable_restrictedGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] : T ⊢ T.restrictedGödel fDef e := by
  apply iff_provable_restrictedGödel_provable_restrictedGödel'.mpr;
  apply Arithmetic.sigma_one_completeness_iff T.restrictedGödel'_sigmaOne |>.mp;
  apply iff_true_restrictedGödel_true_restrictedGödel'.mp $ true_restrictedGödel f;


-- @@ L99-105 verbatim
/-- Lower bound of a Gödel number of proof of restricted Gödel sentence is `f e`. -/
theorem lower_bound_gödelNumber_proof_restrictedGödel (f : ℕ → ℕ) [𝚺₁-Function₁ f via fDef] :
    ∀ b : T ⊢! T.restrictedGödel fDef e, f (ORingStructure.numeral e) ≤ ⌜b⌝ := by
  intro b;
  exact Nat.le_of_not_lt
    $ (imp_not_comm.mp $ (models_restrictedGödel f).mp (true_restrictedGödel f) ⌜b⌝)
    $ proof_of_quote_proof b;


-- @@ L107-107 verbatim
end Arithmetic


-- @@ L109-109 verbatim
namespace Arithmetic


-- @@ L111-112 verbatim
private lemma iterExp_le_succ (x y : ℕ) : iterExp x y ≤ iterExp x (y + 1) := by
  simp only [iterExp_succ]; exact (exponential_exp (iterExp x y)).lt.le


-- @@ L114-115 verbatim
private lemma iterExp_mono_right {x : ℕ} : Monotone (iterExp x) :=
  monotone_nat_of_le_succ (iterExp_le_succ x)


-- @@ L117-121 verbatim
theorem two_pow_le_superexp {e : ℕ} (he : 1 ≤ e) : 2 ^ e ≤ Superexp.superexp e := by
  have h1 : iterExp e 1 = 2 ^ e := (iterExp_succ e 0).trans (by rw [iterExp_zero]; exact exp_nat_eq_two_pow e)
  calc 2 ^ e = iterExp e 1 := h1.symm
    _ ≤ iterExp e e := iterExp_mono_right he
    _ = Superexp.superexp e := (superexp_eq e).symm


-- @@ L123-123 verbatim
variable {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [T.SoundOnHierarchy 𝚺 1]


-- @@ L125-126 verbatim
theorem provable_restrictedGödel_superexp {e : ℕ} : T ⊢ T.restrictedGödel superexpDef e :=
  provable_restrictedGödel Superexp.superexp


-- @@ L128-130 verbatim
theorem lower_bound_gödelNumber_proof_restrictedGödel_superexp {e : ℕ} :
    ∀ b : T ⊢! T.restrictedGödel superexpDef e, Superexp.superexp e ≤ ⌜b⌝ := by
  simpa [numeral_eq_natCast] using lower_bound_gödelNumber_proof_restrictedGödel Superexp.superexp (e := e)


-- @@ L132-140 verbatim
/--
  "This sentence cannot be proved by proof whose Gödel number is less than the superexponential of `10^9`" is provable and length of its proof is larger than the superexponential of `10^9`.
-/
example :
  letI e : ℕ := 10^9;
   T ⊢ T.restrictedGödel superexpDef e ∧ ∀ b : T ⊢! T.restrictedGödel superexpDef e, Superexp.superexp e ≤ ⌜b⌝  := by
  constructor;
  . apply provable_restrictedGödel_superexp;
  . apply lower_bound_gödelNumber_proof_restrictedGödel_superexp;


-- @@ L142-142 verbatim
end Arithmetic


-- @@ L144-144 verbatim
end FFL.FirstOrder
