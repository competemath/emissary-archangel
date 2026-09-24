module

public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Functions
public import Foundation.FirstOrder.Arithmetic.TA.Basic


-- @@ L6-12 verbatim
/-!
# Induction and least number schemata of Arithmetic

## References

- [HP98, §I.2(a), I.2.3]
-/


-- @@ L14-14 verbatim
@[expose] public section


-- @@ L16-16 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L18-18 verbatim
section axioms


-- @@ L20-20 verbatim
variable {L : Language} [L.ORing] {ξ : Type*} [DecidableEq ξ]


-- @@ L22-22 verbatim
def succInd {ξ} (φ : Semiformula L ξ 1) : Formula L ξ := “!φ 0 → (∀ x, !φ x → !φ (x + 1)) → ∀ x, !φ x”


-- @@ L24-24 verbatim
def orderInd {ξ} (φ : Semiformula L ξ 1) : Formula L ξ := “(∀ x, (∀ y < x, !φ y) → !φ x) → ∀ x, !φ x”


-- @@ L26-27 verbatim
def leastNumber {ξ} (φ : Semiformula L ξ 1) : Formula L ξ :=
  “(∃ x, !φ x) → ∃ z, !φ z ∧ ∀ x < z, ¬!φ x”


-- @@ L29-29 verbatim
variable (L)


-- @@ L31-32 verbatim
def InductionScheme (Γ : Semiformula L ℕ 1 → Prop) : Theory L :=
  { ψ | ∃ φ : Semiformula L ℕ 1, Γ φ ∧ ψ = .univCl (succInd φ) }


-- @@ L34-34 verbatim
abbrev IOpen : ArithmeticTheory := 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ Semiformula.Open


-- @@ L36-36 verbatim
notation "𝗜𝗢𝗽𝗲𝗻" => IOpen


-- @@ L38-38 verbatim
abbrev InductionOnHierarchy (Γ : Polarity) (k : ℕ) : ArithmeticTheory := 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ (Arithmetic.Hierarchy Γ k)


-- @@ L40-40 verbatim
prefix:max "𝗜𝗡𝗗 " => InductionOnHierarchy


-- @@ L42-42 verbatim
abbrev ISigma (k : ℕ) : ArithmeticTheory := 𝗜𝗡𝗗 𝚺 k


-- @@ L44-44 verbatim
prefix:max "𝗜𝚺" => ISigma


-- @@ L46-46 verbatim
notation "𝗜𝚺₀" => ISigma 0


-- @@ L48-48 verbatim
abbrev IPi (k : ℕ) : ArithmeticTheory := 𝗜𝗡𝗗 𝚷 k


-- @@ L50-50 verbatim
prefix:max "𝗜𝚷" => IPi


-- @@ L52-52 verbatim
notation "𝗜𝚷₀" => IPi 0


-- @@ L54-54 verbatim
notation "𝗜𝚺₁" => ISigma 1


-- @@ L56-56 verbatim
notation "𝗜𝚷₁" => IPi 1


-- @@ L58-58 verbatim
abbrev Peano : ArithmeticTheory := 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ Set.univ


-- @@ L60-60 verbatim
notation "𝗣𝗔" => Peano


-- @@ L62-63 verbatim
def LeastNumberScheme (Γ : ArithmeticSemiformula ℕ 1 → Prop) : ArithmeticTheory :=
  { ψ | ∃ φ : ArithmeticSemiformula ℕ 1, Γ φ ∧ ψ = .univCl (leastNumber φ) }


-- @@ L65-66 verbatim
abbrev LeastNumberOnHierarchy (Γ : Polarity) (n : ℕ) : ArithmeticTheory :=
  𝗣𝗔⁻ ∪ LeastNumberScheme (Arithmetic.Hierarchy Γ n)


-- @@ L68-68 verbatim
prefix:max "𝗟 " => LeastNumberOnHierarchy


-- @@ L70-70 verbatim
abbrev LSigma (n : ℕ) : ArithmeticTheory := 𝗟 𝚺 n


-- @@ L72-72 verbatim
prefix:max "𝗟𝚺" => LSigma


-- @@ L74-74 verbatim
abbrev LPi (n : ℕ) : ArithmeticTheory := 𝗟 𝚷 n


-- @@ L76-76 verbatim
prefix:max "𝗟𝚷" => LPi


-- @@ L78-78 verbatim
variable {L}


-- @@ L80-93 verbatim
variable {C C' : ArithmeticSemiformula ℕ 1 → Prop}

lemma InductionScheme_subset (h : ∀ {φ : ArithmeticSemiformula ℕ 1},  C φ → C' φ) : InductionScheme ℒₒᵣ C ⊆ InductionScheme ℒₒᵣ C' := by
  intro _; simp only [InductionScheme, Set.mem_ofPred_eq, forall_exists_index, and_imp]; rintro φ hp rfl; exact ⟨φ, h hp, rfl⟩

lemma ISigma_subset_mono {s₁ s₂} (h : s₁ ≤ s₂) : 𝗜𝚺 s₁ ⊆ 𝗜𝚺 s₂ :=
  Set.union_subset_union_right _ (InductionScheme_subset (fun H ↦ H.mono h))

lemma ISigma_weakerThan_of_le {s₁ s₂} (h : s₁ ≤ s₂) : 𝗜𝚺 s₁ ⪯ 𝗜𝚺 s₂ :=
  Entailment.WeakerThan.ofSubset (ISigma_subset_mono h)

lemma ISigma_weakerThan_of_le_trans {T : ArithmeticTheory} {s₁ s₂} (h : s₁ ≤ s₂) (hT : 𝗜𝚺 s₂ ⪯ T) :
    𝗜𝚺 s₁ ⪯ T :=
  Entailment.WeakerThan.trans (ISigma_weakerThan_of_le h) hT


-- @@ L95-97 verbatim
instance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝗡𝗗 Γ n :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻ := inferInstance
  Entailment.WeakerThan.trans this inferInstance


-- @@ L99-101 verbatim
instance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝗢𝗽𝗲𝗻 :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻ := inferInstance
  Entailment.WeakerThan.trans this inferInstance


-- @@ L103-104 verbatim
instance : 𝗜𝗢𝗽𝗲𝗻 ⪯ 𝗜𝗡𝗗 Γ n :=
  Entailment.WeakerThan.ofSubset <| Set.union_subset_union_right _  <| InductionScheme_subset Arithmetic.Hierarchy.of_open


-- @@ L106-106 verbatim
instance : 𝗜𝚺₀ ⪯ 𝗜𝚺₁ := ISigma_weakerThan_of_le (by decide)


-- @@ L108-126 verbatim
instance : 𝗜𝚺i ⪯ 𝗣𝗔 :=
  Entailment.WeakerThan.ofSubset <| Set.union_subset_union_right _  <| InductionScheme_subset (by intros; trivial)

lemma mem_InductionScheme_of_mem {φ : ArithmeticSemiformula ℕ 1} (hp : C φ) :
    .univCl (succInd φ) ∈ InductionScheme ℒₒᵣ C := by
  simpa [InductionScheme] using ⟨φ, hp, rfl⟩

lemma LeastNumberScheme_subset (h : ∀ {φ : ArithmeticSemiformula ℕ 1}, C φ → C' φ) :
    LeastNumberScheme C ⊆ LeastNumberScheme C' := by
  rintro _ ⟨φ, hφ, rfl⟩; exact ⟨φ, h hφ, rfl⟩;

lemma mem_LeastNumberScheme_of_mem {φ : ArithmeticSemiformula ℕ 1} (hφ : C φ) :
    .univCl (leastNumber φ) ∈ LeastNumberScheme C := ⟨φ, hφ, rfl⟩

lemma LeastNumberOnHierarchy_subset_mono {n₁ n₂} (h : n₁ ≤ n₂) : 𝗟 Γ n₁ ⊆ 𝗟 Γ n₂ :=
  Set.union_subset_union_right _ (LeastNumberScheme_subset (fun H ↦ H.mono h))

lemma LeastNumberOnHierarchy_weakerThan_of_le {n₁ n₂} (h : n₁ ≤ n₂) : 𝗟 Γ n₁ ⪯ 𝗟 Γ n₂ :=
  Entailment.WeakerThan.ofSubset (LeastNumberOnHierarchy_subset_mono h)


-- @@ L128-129 verbatim
instance (Γ : Polarity) (n : ℕ) : 𝗣𝗔⁻ ⪯ 𝗟 Γ n :=
  Entailment.WeakerThan.ofSubset Set.subset_union_left


-- @@ L131-136 verbatim
instance (Γ : Polarity) (n : ℕ) : 𝗘𝗤 ℒₒᵣ ⪯ 𝗟 Γ n :=
  Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻) inferInstance

lemma mem_IOpen_of_qfree {φ : ArithmeticSemiformula ℕ 1} (hp : φ.Open) :
    .univCl (succInd φ) ∈ InductionScheme ℒₒᵣ Semiformula.Open := by
  exact ⟨φ, hp, rfl⟩


-- @@ L138-138 verbatim
instance : 𝗣𝗔⁻ ⪯ 𝗜𝗢𝗽𝗲𝗻 := inferInstance


-- @@ L140-140 verbatim
instance : 𝗜𝗢𝗽𝗲𝗻 ⪯ 𝗜𝚺₀ := inferInstance


-- @@ L142-142 verbatim
instance : 𝗜𝚺₁ ⪯ 𝗣𝗔 := inferInstance


-- @@ L144-151 verbatim
instance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔 :=
  have : 𝗘𝗤 ℒₒᵣ ⪯ 𝗣𝗔⁻ := inferInstance
  Entailment.WeakerThan.trans this inferInstance

-- This is stated as a `lemma`, not an `instance`, since `s` does not occur in the conclusion
-- `𝗘𝗤 ℒₒᵣ ⪯ T`, so instance search cannot infer it.
lemma eq_weakerThan_of_ISigma {T : ArithmeticTheory} {s : ℕ} [𝗜𝚺 s ⪯ T] : 𝗘𝗤 ℒₒᵣ ⪯ T :=
  Entailment.WeakerThan.trans (inferInstance : 𝗘𝗤 ℒₒᵣ ⪯ 𝗜𝚺₀) (ISigma_weakerThan_of_le_trans (by omega) ‹𝗜𝚺 s ⪯ T›)


-- @@ L153-153 verbatim
end axioms


-- @@ L155-155 verbatim
section models


-- @@ L157-157 verbatim
variable {V : Type*} [ORingStructure V]


-- @@ L159-159 verbatim
namespace InductionScheme


-- @@ L161-161 verbatim
variable {C : ArithmeticSemiformula ℕ 1 → Prop} [V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ C]


-- @@ L163-170 verbatim
private lemma induction_eval {φ : ArithmeticSemiformula ℕ 1} (hp : C φ) (v : ℕ → V) :
    φ.Eval ![0] v →
    (∀ x, φ.Eval ![x] v → φ.Eval ![x + 1] v) →
    ∀ x, φ.Eval ![x] v := by
  have : V↓[ℒₒᵣ] ⊧ .univCl (succInd φ) :=
    Theory.models (T := InductionScheme _ C) V (by simpa using mem_InductionScheme_of_mem hp)
  revert v
  simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_substs, Matrix.constant_eq_singleton] using this


-- @@ L172-176 verbatim
@[elab_as_elim]
lemma succ_induction {P : V → Prop}
    (hP : ∃ e : ℕ → V, ∃ φ : ArithmeticSemiformula ℕ 1, C φ ∧ ∀ x, P x ↔ φ.Eval ![x] e) :
    P 0 → (∀ x, P x → P (x + 1)) → ∀ x, P x := by
  rcases hP with ⟨e, φ, Cp, hp⟩; simpa [←hp] using induction_eval (V := V) Cp e


-- @@ L178-178 verbatim
end InductionScheme


-- @@ L180-180 verbatim
namespace InductionOnHierarchy


-- @@ L182-182 verbatim
section


-- @@ L184-184 verbatim
variable (Γ : Polarity) (m : ℕ) [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ m]


-- @@ L186-218 verbatim
instance : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (Hierarchy Γ m) :=
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ m := inferInstance
  models_of_subtheory this

lemma succ_induction {P : V → Prop} (hP : Γ-[m].DefinablePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ m := inferInstance
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory this
  InductionScheme.succ_induction (P := P) (C := Hierarchy Γ m) (by
    rcases hP with ⟨φ, hp⟩
    have : Inhabited V := Classical.inhabited_of_nonempty'
    exact ⟨φ.val.enumerateFVar, (Rew.rewriteMap φ.val.idxOfFVar) ▹ φ.val, by simp,
      by intro x; simp [Semiformula.eval_rewriteMap, hp.df.iff]⟩)
    zero succ

lemma order_induction {P : V → Prop} (hP : Γ-[m].DefinablePred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x := by
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ m := inferInstance
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory this
  suffices ∀ x, ∀ y < x, P y by
    intro x; exact this (x + 1) x (by simp only [lt_add_iff_pos_right, lt_one_iff_eq_zero])
  intro x; induction x using succ_induction
  · exact Γ
  · exact m
  · suffices Γ-[m].DefinablePred fun x ↦ ∀ y < x, P y by exact this
    exact HierarchySymbol.Definable.ball_blt (by simp) (hP.retraction ![0])
  case zero => simp
  case succ x IH =>
    intro y hxy
    rcases show y < x ∨ y = x from lt_or_eq_of_le (le_iff_lt_succ.mpr hxy) with (lt | rfl)
    · exact IH y lt
    · exact ind y IH
  case inst => infer_instance


-- @@ L220-246 verbatim
private lemma neg_succ_induction {P : V → Prop} (hP : Γ-[m].DefinablePred P)
    (nzero : ¬P 0) (nsucc : ∀ x, ¬P x → ¬P (x + 1)) : ∀ x, ¬P x := by
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ m := inferInstance
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory this
  by_contra A
  have : ∃ x, P x := by simpa using A
  rcases this with ⟨a, ha⟩
  have : ∀ x ≤ a, P (a - x) := by
    intro x; induction x using succ_induction
    · exact Γ
    · exact m
    · suffices Γ-[m].DefinablePred fun x ↦ x ≤ a → P (a - x) by exact this
      apply HierarchySymbol.Definable.imp
      · apply HierarchySymbol.Definable.bcomp₂ (by definability) (by definability)
      · apply HierarchySymbol.Definable.bcomp₁ (by definability)
    case zero =>
      intro _; simpa using ha
    case succ x IH =>
      intro hx
      have : P (a - x) := IH (le_of_add_le_left hx)
      exact (not_imp_not.mp <| nsucc (a - (x + 1))) (by
        rw [←Arithmetic.sub_sub, sub_add_self_of_le]
        · exact this
        · exact le_tsub_of_add_le_left hx)
    case inst => infer_instance
  have : P 0 := by simpa using this a (by rfl)
  contradiction


-- @@ L248-265 verbatim
instance models_InductionScheme_alt : V↓[ℒₒᵣ] ⊧* InductionScheme ℒₒᵣ (Arithmetic.Hierarchy Γ.alt m) := by
  suffices
      ∀ (φ : ArithmeticSemiformula ℕ 1), Hierarchy Γ.alt m φ →
      ∀ (f : ℕ → V),
        φ.Eval ![0] f →
        (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) →
        ∀ x, φ.Eval ![x] f by
    simp only [InductionScheme]
    refine Semantics.ModelsSet.setOf_iff.mpr ?_
    rintro _ ⟨φ, hφ, rfl⟩
    simpa [models_iff, Semiformula.eval_univCl, succInd, Semiformula.eval_rew_q,
        Semiformula.eval_substs, Function.comp, Matrix.constant_eq_singleton]
    using this φ hφ
  intro φ hp v
  simpa using
    neg_succ_induction Γ m (P := fun x ↦ ¬φ.Eval ![x] v)
      (.mkPolarity (∼(Rew.rewriteMap v ▹ φ)) (by simpa using hp)
      (by intro x; simp [←Matrix.fun_eq_vec_one, Semiformula.eval_rewriteMap]))


-- @@ L267-296 verbatim
instance models_alt : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ.alt m := by
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ m := inferInstance
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory this
  simp only [InductionOnHierarchy, Semantics.ModelsSet.union_iff]; constructor <;> infer_instance

lemma least_number {P : V → Prop} (hP : Γ-[m].DefinablePred P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z := by
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ m := inferInstance
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ := models_of_subtheory this
  by_contra A
  have A : ∀ z, P z → ∃ w < z, P w := by simpa using A
  have : ∀ z, ∀ w < z, ¬P w := by
    intro z
    induction z using succ_induction
    · exact Γ.alt
    · exact m
    · suffices Γ.alt-[m].DefinablePred fun z ↦ ∀ w < z, ¬P w by exact this
      apply HierarchySymbol.Definable.ball_blt (by definability)
      apply HierarchySymbol.Definable.not
      apply HierarchySymbol.Definable.bcomp₁ (hP := by simpa using hP) (by definability)
    case zero => simp
    case succ x IH =>
      intro w hx hw
      rcases le_iff_lt_or_eq.mp (lt_succ_iff_le.mp hx) with (hx | rfl)
      · exact IH w hx hw
      · have : ∃ v < w, P v := A w hw
        rcases this with ⟨v, hvw, hv⟩
        exact IH v hvw hv
    case inst => infer_instance
  exact this (x + 1) x (by simp) h


-- @@ L298-298 verbatim
end


-- @@ L300-300 verbatim
section


-- @@ L302-329 verbatim
variable (Γ : SigmaPiDelta) (m : ℕ) [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 𝚺 m]

lemma succ_induction_sigma {P : V → Prop} (hP : Γ-[m].DefinablePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  match Γ with
  | 𝚺 => succ_induction 𝚺 m hP zero succ
  | 𝚷 =>
    haveI : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 𝚷 m := models_alt 𝚺 m
    succ_induction 𝚷 m hP zero succ
  | 𝚫 => succ_induction 𝚺 m hP.of_delta zero succ

lemma order_induction_sigma {P : V → Prop} (hP : Γ-[m].DefinablePred P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  match Γ with
  | 𝚺 => order_induction 𝚺 m hP ind
  | 𝚷 =>
    haveI : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 𝚷 m := models_alt 𝚺 m
    order_induction 𝚷 m hP ind
  | 𝚫 => order_induction 𝚺 m hP.of_delta ind

lemma least_number_sigma {P : V → Prop} (hP : Γ-[m].DefinablePred P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z :=
  match Γ with
  | 𝚺 => least_number 𝚺 m hP h
  | 𝚷 =>
    haveI : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 𝚷 m := models_alt 𝚺 m
    least_number 𝚷 m hP h
  | 𝚫 => least_number 𝚺 m hP.of_delta h


-- @@ L331-331 verbatim
end


-- @@ L333-336 verbatim
instance [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 𝚺 m] : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ m := by
  rcases Γ
  · infer_instance
  · exact models_alt 𝚺 m


-- @@ L338-344 verbatim
instance [V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 𝚷 m] : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ m := by
  rcases Γ
  · exact models_alt 𝚷 m
  · infer_instance

lemma mod_ISigma_of_le {n₁ n₂} (h : n₁ ≤ n₂) [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n₂] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n₁ :=
  models_of_ss inferInstance (ISigma_subset_mono h)


-- @@ L346-346 verbatim
instance [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := mod_ISigma_of_le (show 0 ≤ 1 from by simp)


-- @@ L348-348 verbatim
instance [V↓[ℒₒᵣ] ⊧* 𝗜𝚺n] : V↓[ℒₒᵣ] ⊧* 𝗜𝚷n := inferInstance


-- @@ L350-353 verbatim
instance [V↓[ℒₒᵣ] ⊧* 𝗜𝚷n] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺n := inferInstance

lemma models_ISigma_iff_models_IPi {n} : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n ↔ V↓[ℒₒᵣ] ⊧* 𝗜𝚷 n :=
  ⟨fun _ ↦ inferInstance, fun _ ↦ inferInstance⟩


-- @@ L355-358 verbatim
instance [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n] : V↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ n :=
  match Γ with
  | 𝚺 => inferInstance
  | 𝚷 => inferInstance


-- @@ L360-360 verbatim
end InductionOnHierarchy


-- @@ L362-365 verbatim
@[elab_as_elim] lemma ISigma0.succ_induction [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    {P : V → Prop} (hP : 𝚺₀.DefinablePred P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  InductionOnHierarchy.succ_induction 𝚺 0 hP zero succ


-- @@ L367-370 verbatim
@[elab_as_elim] lemma ISigma1.sigma1_succ_induction [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {P : V → Prop} (hP : 𝚺₁-Predicate P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  InductionOnHierarchy.succ_induction 𝚺 1 hP zero succ


-- @@ L372-375 verbatim
@[elab_as_elim] lemma ISigma1.pi1_succ_induction [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {P : V → Prop} (hP : 𝚷₁-Predicate P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  InductionOnHierarchy.succ_induction 𝚷 1 hP zero succ


-- @@ L377-380 verbatim
@[elab_as_elim] lemma ISigma0.order_induction [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀]
    {P : V → Prop} (hP : 𝚺₀-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  InductionOnHierarchy.order_induction 𝚺 0 hP ind


-- @@ L382-385 verbatim
@[elab_as_elim] lemma ISigma1.sigma1_order_induction [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {P : V → Prop} (hP : 𝚺₁-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  InductionOnHierarchy.order_induction 𝚺 1 hP ind


-- @@ L387-394 verbatim
@[elab_as_elim] lemma ISigma1.pi1_order_induction [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
    {P : V → Prop} (hP : 𝚷₁-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  InductionOnHierarchy.order_induction 𝚷 1 hP ind

lemma ISigma0.least_number [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] {P : V → Prop} (hP : 𝚺₀-Predicate P)
    {x} (h : P x) : ∃ y, P y ∧ ∀ z < y, ¬P z :=
  InductionOnHierarchy.least_number 𝚺 0 hP h


-- @@ L396-399 verbatim
@[elab_as_elim] lemma ISigma1.succ_induction [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (Γ)
    {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (zero : P 0) (succ : ∀ x, P x → P (x + 1)) : ∀ x, P x :=
  InductionOnHierarchy.succ_induction_sigma Γ 1 hP zero succ


-- @@ L401-404 verbatim
@[elab_as_elim] lemma ISigma1.order_induction [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] (Γ)
    {P : V → Prop} (hP : Γ-[1]-Predicate P)
    (ind : ∀ x, (∀ y < x, P y) → P x) : ∀ x, P x :=
  InductionOnHierarchy.order_induction_sigma Γ 1 hP ind


-- @@ L406-408 verbatim
instance [V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻] : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := inferInstance
  models_of_subtheory this


-- @@ L410-412 verbatim
instance [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀] : V↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 :=
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := inferInstance
  models_of_subtheory this


-- @@ L414-414 verbatim
instance [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := inferInstance


-- @@ L416-423 verbatim
abbrev mod_ISigma_of_le {n₁ n₂} (h : n₁ ≤ n₂) [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n₂] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n₁ :=
  models_of_ss inferInstance (ISigma_subset_mono h)

-- This is stated as a `lemma`, not an `instance`, since `n` does not occur in the conclusion
-- `V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻`, so instance search cannot infer it.
lemma mod_paMinus_of_ISigma {n} [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n] : V↓[ℒₒᵣ] ⊧* 𝗣𝗔⁻ :=
  have : V↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := mod_ISigma_of_le (Nat.zero_le n)
  inferInstance


-- @@ L425-427 verbatim
instance [V↓[ℒₒᵣ] ⊧* 𝗣𝗔] : V↓[ℒₒᵣ] ⊧* 𝗜𝚺 n :=
  have : V↓[ℒₒᵣ] ⊧* 𝗣𝗔 := inferInstance
  models_of_subtheory this


-- @@ L429-438 verbatim
end models

lemma models_succInd (φ : ArithmeticSemiformula ℕ 1) : ℕ↓[ℒₒᵣ] ⊧ (succInd φ).univCl := by
  suffices
    ∀ f : ℕ → ℕ,
    φ.Eval ![0] f → (∀ x, φ.Eval ![x] f → φ.Eval ![x + 1] f) → ∀ x, φ.Eval ![x] f by
    simpa [Semiformula.eval_univCl, succInd, models_iff, Matrix.constant_eq_singleton, Semiformula.eval_substs]
  intro e hzero hsucc x; induction' x with x ih
  · exact hzero
  · exact hsucc x ih


-- @@ L440-444 verbatim
instance models_ISigma (Γ k) : ℕ↓[ℒₒᵣ] ⊧* 𝗜𝗡𝗗 Γ k := by
  have : ∀ φ, ℕ↓[ℒₒᵣ] ⊧ (succInd φ).univCl := models_succInd
  simp only [Semantics.ModelsSet.union_iff, PeanoMinus.instModelsSetStrucORingSentenceStrNat,
    true_and, InductionScheme]
  exact Semantics.ModelsSet.setOf_iff.mpr (fun ψ ⟨φ, _, hψ⟩ => hψ ▸ this φ)


-- @@ L446-446 verbatim
instance models_ISigmaZero : ℕ↓[ℒₒᵣ] ⊧* 𝗜𝚺₀ := inferInstance


-- @@ L448-448 verbatim
instance models_ISigmaOne : ℕ↓[ℒₒᵣ] ⊧* 𝗜𝚺₁ := inferInstance


-- @@ L450-454 verbatim
instance models_Peano : ℕ↓[ℒₒᵣ] ⊧* 𝗣𝗔 := by
  have : ∀ φ, ℕ↓[ℒₒᵣ] ⊧ (succInd φ).univCl := models_succInd
  simp only [Peano, Semantics.ModelsSet.union_iff, PeanoMinus.instModelsSetStrucORingSentenceStrNat,
    true_and, InductionScheme]
  exact Semantics.ModelsSet.setOf_iff.mpr (fun ψ ⟨φ, _, hψ⟩ => hψ ▸ this φ)


-- @@ L456-456 verbatim
instance sigmaOneSound_ISigmaOne : 𝗜𝚺₁.SoundOnHierarchy 𝚺 1 := inferInstance


-- @@ L458-458 verbatim
instance sigmaOneSound_Peano : 𝗣𝗔.SoundOnHierarchy 𝚺 1 := inferInstance


-- @@ L460-460 verbatim
instance : Entailment.Consistent (𝗜𝗡𝗗 Γ k) := (𝗜𝗡𝗗 Γ k).consistent_of_sound (Eq ⊥) rfl


-- @@ L462-462 verbatim
instance : Entailment.Consistent 𝗣𝗔 := 𝗣𝗔.consistent_of_sound (Eq ⊥) rfl


-- @@ L464-464 verbatim
instance : 𝗣𝗔 ⪯ 𝗧𝗔 := inferInstance


-- @@ L466-468 verbatim
instance (T : ArithmeticTheory) [𝗣𝗔⁻ ⪯ T] : 𝗥₀ ⪯ T :=
  have : 𝗥₀ ⪯ 𝗣𝗔⁻ := inferInstance
  Entailment.WeakerThan.trans this inferInstance


-- @@ L470-472 verbatim
instance (T : ArithmeticTheory) [𝗜𝚺₀ ⪯ T] : 𝗣𝗔⁻ ⪯ T :=
  have : 𝗣𝗔⁻ ⪯ 𝗜𝚺₀ := inferInstance
  Entailment.WeakerThan.trans this inferInstance


-- @@ L474-476 verbatim
instance (T : ArithmeticTheory) [𝗜𝚺₁ ⪯ T] : 𝗣𝗔⁻ ⪯ T :=
  have : 𝗣𝗔⁻ ⪯ 𝗜𝚺₁ := inferInstance
  Entailment.WeakerThan.trans this inferInstance


-- @@ L478-480 verbatim
instance (T : ArithmeticTheory) [𝗣𝗔 ⪯ T] : 𝗣𝗔⁻ ⪯ T :=
  have : 𝗣𝗔⁻ ⪯ 𝗣𝗔 := inferInstance
  Entailment.WeakerThan.trans this inferInstance


-- @@ L482-482 verbatim
end FFL.FirstOrder.Arithmetic
