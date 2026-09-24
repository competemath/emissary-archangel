module

public import Foundation.FirstOrder.Arithmetic.Schemata


-- @@ L5-11 verbatim
/-!
# Equivalence of the least number schemes `𝗟𝚺`, `𝗟𝚷` with `𝗜𝚺`

## References

- [HP98, Theorem I.2.4, Lemma I.2.8, Lemma I.2.12]
-/


-- @@ L13-13 verbatim
@[expose] public section


-- @@ L15-15 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L17-17 verbatim
open _root_.FFL.Entailment


-- @@ L19-19 verbatim
section models


-- @@ L21-21 verbatim
variable {V : Type*} [ORingStructure V]


-- @@ L23-23 verbatim
namespace LeastNumberScheme


-- @@ L25-25 expanded
variable {C : ArithmeticSemiformula ℕ 1 → Prop}
  [ModelsSet (Language.str V oRing) (LeastNumberScheme C)]


-- @@ L27-33 expanded
private lemma leastNumber_eval {φ : ArithmeticSemiformula ℕ 1} (hφ : C φ) (v : ℕ → V) :
    (∃ x, φ.Eval ![x] v) → ∃ z, φ.Eval ![z] v ∧ ∀ x < z, ¬φ.Eval ![x] v := by
  have : Models (Language.str V oRing) (.univCl (leastNumber φ)) :=
    Theory.models (T := LeastNumberScheme C) V (by simpa using mem_LeastNumberScheme_of_mem hφ);
  revert v;
  simpa [models_iff, Semiformula.eval_univCl, leastNumber, Semiformula.eval_substs,
    Matrix.constant_eq_singleton] using this;


-- @@ L35-39 verbatim
lemma least_number {P : V → Prop}
    (hP : ∃ e : ℕ → V, ∃ φ : ArithmeticSemiformula ℕ 1, C φ ∧ ∀ x, P x ↔ φ.Eval ![x] e)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z := by
  rcases hP with ⟨e, φ, Cφ, hφ⟩;
  simpa [← hφ] using leastNumber_eval (V := V) Cφ e ⟨x, (hφ x).mp h⟩;


-- @@ L41-41 verbatim
end LeastNumberScheme


-- @@ L43-43 verbatim
namespace LeastNumberOnHierarchy


-- @@ L45-45 expanded
variable (Γ : Polarity) (m : ℕ) [ModelsSet (Language.str V oRing) ((LeastNumberOnHierarchy Γ) m)]


-- @@ L47-47 expanded
instance : ModelsSet (Language.str V oRing) (LeastNumberScheme (Hierarchy Γ m)) :=
  models_of_subtheory ‹ModelsSet (Language.str V oRing) ((LeastNumberOnHierarchy Γ) m)›


-- @@ L49-60 expanded
lemma least_number {P : V → Prop} (hP : Γ-[m].DefinablePred P) {x} (h : P x) :
    ∃ y, P y ∧ ∀ z < y, ¬P z :=
  LeastNumberScheme.least_number (P := P) (C := Hierarchy Γ m)
    (by
      classical
      rcases hP with ⟨φ, hp⟩; have : Inhabited V := Classical.inhabited_of_nonempty';
      use φ.val.enumerateFVar, app (Rew.rewriteMap φ.val.idxOfFVar) φ.val; and_intros; · simp;
      · intro x; simp [Semiformula.eval_rewriteMap, hp.df.iff])
    h


-- @@ L62-81 expanded
lemma succ_induction {P : V → Prop} (hP : Γ.alt-[m].DefinablePred P) (zero : P 0)
    (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  by
  have : ModelsSet (Language.str V oRing) PeanoMinus :=
    models_of_subtheory ‹ModelsSet (Language.str V oRing) ((LeastNumberOnHierarchy Γ) m)›;
  have : ModelsSet (Language.str V oRing) RobinsonQ := models_of_subtheory this; by_contra! hcon;
  obtain ⟨a, ha⟩ := hcon;
  obtain ⟨y, hy, hmin⟩ :=
    least_number Γ m (P := fun x ↦ ¬P x)
      (by apply Arithmetic.HierarchySymbol.Definable.not; simpa [SigmaPiDelta.alt_coe]; ) ha;
  push Not at hmin;
  obtain ⟨z, rfl⟩ := Arithmetic.exists_succ_of_ne_zero $ show y ≠ 0 by rintro rfl; contradiction;
  apply hy; apply succ; apply hmin; apply lt_succ_iff_le.mpr; apply le_rfl;


-- @@ L83-95 expanded
lemma models_alt : ModelsSet (Language.str V oRing) ((InductionOnHierarchy Γ.alt) m) :=
  by
  have : ModelsSet (Language.str V oRing) PeanoMinus :=
    models_of_subtheory ‹ModelsSet (Language.str V oRing) ((LeastNumberOnHierarchy Γ) m)›;
  suffices ModelsSet (Language.str V oRing) (InductionScheme oRing (Hierarchy Γ.alt m)) by
    simpa [InductionOnHierarchy, Semantics.ModelsSet.union_iff] using ⟨‹_›, this⟩;
  simp only [InductionScheme]; apply Semantics.ModelsSet.setOf_iff.mpr; rintro _ ⟨φ, hφ, rfl⟩;
  suffices
    ∀ v : ℕ → V, φ.Eval ![0] v → (∀ x, φ.Eval ![x] v → φ.Eval ![x + 1] v) → ∀ x, φ.Eval ![x] v by
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this;
  intro v; exact succ_induction Γ m (definablePred_of_hierarchy hφ v);


-- @@ L97-97 verbatim
end LeastNumberOnHierarchy


-- @@ L99-99 verbatim
variable (n : ℕ)


-- @@ L101-113 expanded
lemma models_LeastNumberOnHierarchy_of_ISigma (Γ : Polarity) (n : ℕ)
    [ModelsSet (Language.str V oRing) (ISigma n)] :
    ModelsSet (Language.str V oRing) ((LeastNumberOnHierarchy Γ) n) :=
  by
  have : ModelsSet (Language.str V oRing) PeanoMinus :=
    models_of_subtheory ‹ModelsSet (Language.str V oRing) (ISigma n)›;
  suffices ModelsSet (Language.str V oRing) (LeastNumberScheme (Hierarchy Γ n)) by
    simpa [LeastNumberOnHierarchy, Semantics.ModelsSet.union_iff] using ⟨‹_›, this⟩;
  simp only [LeastNumberScheme]; apply Semantics.ModelsSet.setOf_iff.mpr; rintro _ ⟨φ, hφ, rfl⟩;
  suffices ∀ v : ℕ → V, (∃ x, φ.Eval ![x] v) → ∃ z, φ.Eval ![z] v ∧ ∀ x < z, ¬φ.Eval ![x] v by
    simpa [models_iff, Semiformula.eval_univCl, leastNumber, Semiformula.eval_substs,
      Matrix.constant_eq_singleton] using this;
  intro v ⟨x, hx⟩; exact InductionOnHierarchy.least_number Γ n (definablePred_of_hierarchy hφ v) hx;


-- @@ L115-116 expanded
instance models_LSigma_of_ISigma [ModelsSet (Language.str V oRing) (ISigma n)] :
    ModelsSet (Language.str V oRing) (LSigma n) :=
  models_LeastNumberOnHierarchy_of_ISigma SigmaSymbol.sigma n


-- @@ L118-119 expanded
instance models_LPi_of_ISigma [ModelsSet (Language.str V oRing) (ISigma n)] :
    ModelsSet (Language.str V oRing) (LPi n) :=
  models_LeastNumberOnHierarchy_of_ISigma PiSymbol.pi n


-- @@ L121-122 expanded
instance models_IPi_of_LSigma [ModelsSet (Language.str V oRing) (LSigma n)] :
    ModelsSet (Language.str V oRing) (IPi n) :=
  LeastNumberOnHierarchy.models_alt SigmaSymbol.sigma n


-- @@ L124-125 expanded
instance models_ISigma_of_LPi [ModelsSet (Language.str V oRing) (LPi n)] :
    ModelsSet (Language.str V oRing) (ISigma n) :=
  LeastNumberOnHierarchy.models_alt PiSymbol.pi n


-- @@ L127-127 verbatim
end models


-- @@ L129-129 verbatim
section theorems


-- @@ L131-132 expanded
theorem ISigma_equiv_IPi (n : ℕ) : Equiv (ISigma n) (IPi n) :=
  equiv_of_models.{0, 0} (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance)


-- @@ L134-135 expanded
theorem LSigma_equiv_ISigma (n : ℕ) : Equiv (LSigma n) (ISigma n) :=
  equiv_of_models.{0, 0} (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance)


-- @@ L137-138 expanded
theorem LPi_equiv_ISigma (n : ℕ) : Equiv (LPi n) (ISigma n) :=
  equiv_of_models.{0, 0} (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance)


-- @@ L140-140 verbatim
end theorems


-- @@ L142-142 verbatim
end FFL.FirstOrder.Arithmetic
