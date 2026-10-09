import Mathlib
import OAI.Probability.ThorpCompatibility.LightRescaling


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
open scoped Classical

-- @@ L7-7 verbatim
namespace ThorpCompatibility

-- @@ L8-8 verbatim
namespace Law

-- @@ L9-9 verbatim
open Finset

-- @@ L10-10 verbatim
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]


-- @@ L12-24 verbatim
noncomputable def restrict (P : Law α) (S : α → Prop) : Law α :=
  if h : 0 < P.prob S then {
    mass := fun a => (if S a then P.mass a else 0) / P.prob S
    nonneg := fun a => div_nonneg (by split_ifs <;> simp_all [P.nonneg]) h.le
    total := by
      rw [← Finset.sum_div]
      have he : (∑ a, if S a then P.mass a else 0) = P.prob S := by
        unfold prob
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : S a <;> simp [h]
      rw [he, div_self h.ne']
  } else P


-- @@ L26-28 verbatim
lemma restrict_mass (P : Law α) (S : α → Prop) (h : 0 < P.prob S) (a : α) :
    (P.restrict S).mass a = (if S a then P.mass a else 0) / P.prob S := by
  simp [restrict, h]


-- @@ L30-31 verbatim
lemma prob_eq_map_mass (P : Law α) (Y : α → γ) (y : γ) :
    P.prob (fun a => Y a = y) = (P.map Y).mass y := by rfl


-- @@ L33-34 verbatim
noncomputable def predict (P : Law α) (X : α → β) (Y : α → γ) (y : γ) : Law β :=
  (P.restrict (fun a => Y a = y)).map X


-- @@ L36-45 verbatim
lemma predict_mass (P : Law α) (X : α → β) (Y : α → γ) (y : γ)
    (hy : 0 < (P.map Y).mass y) (x : β) :
    (P.predict X Y y).mass x =
      (P.map (fun a => (X a, Y a))).mass (x, y) / (P.map Y).mass y := by
  have hp : 0 < P.prob (fun a => Y a = y) := hy
  simp only [predict, map, P.restrict_mass _ hp, prob_eq_map_mass]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hx : X a = x <;> by_cases hy' : Y a = y <;> simp [hx, hy']


-- @@ L47-50 verbatim
lemma predict_mass_self (P : Law α) (X : α → β) (Y : α → γ)
    {a : α} (ha : 0 < P.mass a) :
    (P.predict X Y (Y a)).mass (X a) = P.condMass X Y a := by
  exact P.predict_mass X Y (Y a) (P.map_mass_pos Y ha) (X a)


-- @@ L52-55 verbatim
lemma predict_pos (P : Law α) (X : α → β) (Y : α → γ)
    {a : α} (ha : 0 < P.mass a) : 0 < (P.predict X Y (Y a)).mass (X a) := by
  rw [P.predict_mass_self X Y ha]
  exact P.condMass_pos X Y ha


-- @@ L57-66 verbatim
lemma predict_mass_zero (P : Law α) (X : α → β) (Y : α → γ) {y : γ} {x : β}
    (hy : 0 < (P.map Y).mass y)
    (h : ∀ a, 0 < P.mass a → Y a = y → X a ≠ x) :
    (P.predict X Y y).mass x = 0 := by
  rw [P.predict_mass X Y y hy x]
  suffices hz : (P.map (fun a => (X a, Y a))).mass (x, y) = 0 by simp [hz]
  by_contra hn
  obtain ⟨a, he, ha⟩ := (P.map_mass_pos_iff _ _).mp
    (lt_of_le_of_ne ((P.map _).nonneg _) (Ne.symm hn))
  exact h a ha (congrArg Prod.snd he) (congrArg Prod.fst he)


-- @@ L68-72 verbatim
lemma mean_predict_log (P : Law α) (X : α → β) (Y : α → γ) :
    P.mean (fun a => Real.log ((P.predict X Y (Y a)).mass (X a))) =
      -P.condEntropy X Y := by
  rw [P.condEntropy_eq_mean, neg_neg]
  exact P.mean_congr_support fun a ha => congrArg Real.log (P.predict_mass_self X Y ha)


-- @@ L74-106 verbatim
lemma mean_predict (P : Law α) (X : α → β) (Y : α → γ) (f : γ → β → ℝ) :
    P.mean (fun a => (P.predict X Y (Y a)).mean (f (Y a))) =
      P.mean (fun a => f (Y a) (X a)) := by
  have he : P.mean (fun a => (P.predict X Y (Y a)).mean (f (Y a))) =
      (P.map Y).mean (fun y => (P.predict X Y y).mean (f y)) := by
    rw [P.mean_map]
    rfl
  rw [he]
  have hsum : (P.map Y).mean (fun y => (P.predict X Y y).mean (f y)) =
      ∑ y, ∑ x, (P.map (fun a => (X a, Y a))).mass (x, y) * f y x := by
    unfold mean
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hy : (P.map Y).mass y = 0
    · have hz : (P.map (fun a => (X a, Y a))).mass (x, y) = 0 := by
        by_contra hn
        obtain ⟨a, he, ha⟩ := (P.map_mass_pos_iff _ _).mp
          (lt_of_le_of_ne ((P.map _).nonneg _) (Ne.symm hn))
        have hpos := P.map_mass_pos Y ha
        have hya : Y a = y := congrArg Prod.snd he
        rw [hya, hy] at hpos
        exact lt_irrefl _ hpos
      simp [hy, hz]
    · rw [P.predict_mass X Y y (lt_of_le_of_ne ((P.map Y).nonneg _) (Ne.symm hy)) x]
      field_simp
  rw [hsum, Finset.sum_comm]
  calc
    _ = (P.map (fun a => (X a, Y a))).mean (fun b => f b.2 b.1) := by
      rw [mean, Fintype.sum_prod_type]
    _ = _ := P.mean_map _ _


-- @@ L108-112 verbatim
lemma mean_predict_prob (P : Law α) (X : α → β) (Y : α → γ) (S : γ → β → Prop) :
    P.mean (fun a => (P.predict X Y (Y a)).prob (S (Y a))) =
      P.prob (fun a => S (Y a) (X a)) := by
  simp_rw [prob_eq_mean]
  exact P.mean_predict X Y (fun y x => if S y x then 1 else 0)


-- @@ L114-122 verbatim
lemma condEntropy_predict_comparison {δ : Type*} [Fintype δ]
    (P : Law α) (X : α → β) (Y : α → γ) (Z : α → δ)
    (g : δ → γ) (hg : ∀ a, g (Z a) = Y a) :
    P.condEntropy X Z ≤ P.condEntropy X Y := by
  have h := P.condEntropy_le_prediction X Z (fun z => P.predict X Y (g z))
    (by intro a ha; rw [hg]; exact P.predict_pos X Y ha)
  simp_rw [hg] at h
  rw [P.mean_predict_log, neg_neg] at h
  exact h


-- @@ L124-124 verbatim
end Law

-- @@ L125-125 verbatim
end ThorpCompatibility


-- @@ L127-127 verbatim
end OAI
