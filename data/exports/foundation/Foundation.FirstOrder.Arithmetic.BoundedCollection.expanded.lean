module

public import Foundation.FirstOrder.Arithmetic.Schemata


-- @@ L5-10 verbatim
/-!
# Σ_{s+1}-collection

Every `Σ_{s+1}` predicate bounded pointwise by a witness admits a single bound `w` that
witnesses all instances at once (`sigma_exists_bound_witness`).
-/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
open FFL

-- @@ L15-15 verbatim
open FFL.FirstOrder


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L21-21 verbatim
variable {V : Type*} {n s : ℕ} (e : Fin n → V)


-- @@ L23-24 verbatim
private def collectionCore (θ : ArithmeticSemisentence (n + 2)) : ArithmeticSemiformula V 4 :=
  Rew.embSubsts (#0 :> #1 :> fun i => (&(e i) : ArithmeticSemiterm V 4)) ▹ θ


-- @@ L26-31 verbatim
private def collectionMotive (θ : ArithmeticSemisentence (n + 2)) (a : V) :
    ArithmeticSemiformula V 1 :=
  let cond : ArithmeticSemiformula V 3 :=
    Semiformula.rel Language.LT.lt ![(#0 : ArithmeticSemiterm V 3), (&a : ArithmeticSemiterm V 3)]
  let inner : ArithmeticSemiformula V 3 := (collectionCore e θ).bexsLTSucc (#1 : ArithmeticSemiterm V 3)
  ∃¹ ((cond 🡒 inner).ballLT (#1 : ArithmeticSemiterm V 2))


-- @@ L33-33 verbatim
variable {θ : ArithmeticSemisentence (n + 2)}


-- @@ L35-37 verbatim
private lemma hierarchy_collectionCore (hθ : Hierarchy 𝚺 (s + 1) θ) :
    Hierarchy 𝚺 (s + 1) (collectionCore e θ) := by
  simp [collectionCore, hθ]


-- @@ L39-42 verbatim
private lemma hierarchy_collectionMotive (hθ : Hierarchy 𝚺 (s + 1) θ) (a : V) :
    Hierarchy 𝚺 (s + 1) (collectionMotive e θ a) := by
  have : Hierarchy 𝚺 (s + 1) (collectionCore e θ) := hierarchy_collectionCore e hθ
  simp [collectionMotive, this]


-- @@ L44-44 verbatim
variable [ORingStructure V]


-- @@ L46-50 verbatim
private lemma eval_collectionCore (u x w y : V) :
    (collectionCore e θ).Eval (u :> x :> w :> ![y]) id ↔ V ⊧/(u :> x :> e) θ := by
  simp only [collectionCore, Semiformula.eval_embSubsts, Function.comp_def]
  exact Iff.of_eq (congrArg (fun b => Semiformula.Evalb (M := V) b θ)
    (Fin.funext_two (by simp) (by simp) fun i => by simp))


-- @@ L52-57 verbatim
private lemma eval_collectionMotive [V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻] (a : V) (v : Fin 1 → V) :
    (collectionMotive e θ a).Eval v id ↔
      ∃ w, ∀ x < v 0, x < a → ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
  rw [Matrix.fun_eq_vec_one v]
  simp [collectionMotive, Semiformula.eval_ballLT, Semiformula.eval_bexsLTSucc,
    Arithmetic.lt_succ_iff_le, eval_collectionCore, Function.comp_def]


-- @@ L59-59 verbatim
variable [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 (s + 1)]


-- @@ L61-65 verbatim
private lemma collectionMotive_definable (hθ : Hierarchy 𝚺 (s + 1) θ) (a : V) :
    𝚺-[s + 1].DefinablePred (fun y => ∃ w, ∀ x < y, x < a → ∃ u ≤ w, V ⊧/(u :> x :> e) θ) := by
  have := mod_paMinus_of_ISigma (V := V) (n := s + 1)
  exact HierarchySymbol.Definable.mkPolarity (collectionMotive e θ a)
    (hierarchy_collectionMotive e hθ a) (fun v => (eval_collectionMotive e a v).symm)


-- @@ L67-92 verbatim
theorem sigma_exists_bound_witness {θ : ArithmeticSemisentence (n + 2)}
    (hθ : Hierarchy 𝚺 (s + 1) θ)
    (e : Fin n → V) (a : V) (h : ∀ x < a, ∃ u, V ⊧/(u :> x :> e) θ) :
    ∃ w, ∀ x < a, ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
  have := mod_paMinus_of_ISigma (V := V) (n := s + 1)
  have key : ∀ y : V, ∃ w, ∀ x < y, x < a → ∃ u ≤ w, V ⊧/(u :> x :> e) θ := by
    apply InductionOnHierarchy.succ_induction_sigma 𝚺 (s + 1)
      (P := fun y => ∃ w, ∀ x < y, x < a → ∃ u ≤ w, V ⊧/(u :> x :> e) θ)
      (hP := collectionMotive_definable e hθ a)
    . exact ⟨0, fun x hx _ => absurd hx (by simp)⟩
    . rintro y ⟨w, hw⟩
      rcases lt_or_ge y a with hya | hya
      . obtain ⟨u₀, hu₀⟩ := h y hya
        use max w u₀;
        intro x hx _
        rcases le_iff_lt_or_eq.mp (Arithmetic.lt_succ_iff_le.mp hx) with hx | rfl
        . obtain ⟨u, hu, hPu⟩ := hw x hx (lt_trans hx hya)
          exact ⟨u, le_trans hu (le_max_left w u₀), hPu⟩
        . exact ⟨u₀, le_max_right w u₀, hu₀⟩
      . use w;
        intro x hx hxa
        rcases le_iff_lt_or_eq.mp (Arithmetic.lt_succ_iff_le.mp hx) with hx | rfl
        . exact hw x hx hxa
        . exact absurd hxa (not_lt.mpr hya)
  obtain ⟨w, hw⟩ := key (a + 1)
  exact ⟨w, fun x hx => hw x (lt_trans hx (lt_add_one a)) hx⟩


-- @@ L94-94 verbatim
end FFL.FirstOrder.Arithmetic
