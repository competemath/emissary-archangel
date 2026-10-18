import OAI.Analysis.FourierLLogL.Finite.Comparison

-- @@ L2-2 verbatim
/-! # Entropy of mixtures -/

-- @@ L3-3 verbatim
open Function Set Filter

-- @@ L4-4 verbatim
open scoped BigOperators

-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace OAI


-- @@ L9-9 verbatim
namespace FourierLLogL.Law

-- @@ L10-10 verbatim
open Real

-- @@ L11-11 verbatim
universe u v w w'


-- @@ L13-14 verbatim
variable {α : Type u} {β : Type v} {γ : Type w} {η : Type w'}
  [Fintype α] [Fintype β] [Fintype γ] [Fintype η]


-- @@ L16-20 verbatim
lemma send_withNext (P : Law α) (Q : α → Law β) (X : α → β → γ) :
    (P.withNext Q).send (fun (z : α × β) => (z.1, X z.1 z.2)) =
      P.withNext (fun i => (Q i).send (X i)) := by
  apply ext_of_Ex; intro f
  simp_rw [Ex_withNext,Ex_send,Ex_withNext]


-- @@ L22-26 verbatim
lemma H_withNext (P : Law α) (Q : α → Law β) (X : α → β → γ) :
    (P.withNext Q).H (fun (z : α × β) => (z.1, X z.1 z.2)) =
      P.entropy + P.Ex (fun i => (Q i).H (X i)) := by
  unfold H
  rw [send_withNext, entropy_withNext]


-- @@ L28-40 verbatim
lemma Hcond_withNext (P : Law α) (Q : α → Law β) (X : α → β → γ) (W : α → β → η) :
    (P.withNext Q).Hcond (fun z => X z.1 z.2) (fun z => (z.1,W z.1 z.2)) =
      P.Ex fun i => (Q i).Hcond (X i) (W i) := by
  unfold Hcond
  let R := P.withNext Q
  have H : R.H (fun z => ((X z.1 z.2),z.1,W z.1 z.2)) =
      R.H (fun z => (z.1,X z.1 z.2,W z.1 z.2)) :=
    R.H_partition fun x y => by simp [and_left_comm]
  change R.H _ - R.H _ = _
  rw [H]
  unfold R
  rw [H_withNext P Q (fun i x => (X i x,W i x)), H_withNext P Q W,
    Ex_sub]; ring


-- @@ L42-47 verbatim
lemma Hcond_withNext' (P : Law α) (Q : α → Law β) (X : α → β → γ) :
    (P.withNext Q).Hcond (fun z => X z.1 z.2) Prod.fst =
      P.Ex fun i => (Q i).H (X i) := by
  have h := Hcond_withNext P Q X (fun _ _ => ())
  rw [Hcond_right_partition _ _ (Z:=Prod.fst) (by simp)] at h
  simpa only [Hcond_constant] using h


-- @@ L49-53 verbatim
lemma Hcond_through (P : Law α) (Q : α → Law β) (X : β → γ) (W : β → η) :
    P.Ex (fun a => (Q a).Hcond X W) ≤ (P.through Q).Hcond X W := by
  rw [← send_snd_withNext, Hcond_send,
    ← Hcond_withNext P Q (fun _ => X) (fun _ => W)]
  exact Hcond_refine _ _ Prod.fst _


-- @@ L55-59 verbatim
lemma H_through_ge (P : Law α) (Q : α → Law β) (X : β → γ) :
    P.Ex (fun a => (Q a).H X) ≤ (P.through Q).H X := by
  rw [← send_snd_withNext, H_send,
    ← Hcond_withNext' P Q (fun _ => X)]
  exact Hcond_le_H _ _ _


-- @@ L61-64 verbatim
lemma H_through_le (P : Law α) (Q : α → Law β) (X : β → γ) :
    (P.through Q).H X ≤ P.entropy + P.Ex (fun a => (Q a).H X) := by
  rw [← H_withNext P Q (fun _ => X), ← send_snd_withNext, H_send]
  exact H_le_of_determined _ (by simp)



-- @@ L67-68 verbatim
def coinP (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : Law Bool :=
  mixture (point true) (point false) t h0 h1


-- @@ L70-72 verbatim
lemma coinP_Ex (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (f : Bool → ℝ) :
    (coinP t h0 h1).Ex f = t*f true+(1-t)*f false := by
  rw [coinP, mixture_Ex, Ex_point, Ex_point]


-- @@ L74-75 verbatim
lemma coinP_entropy (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (coinP t h0 h1).entropy ≤ log 2 := by simpa using entropy_le_log_card (coinP t h0 h1)


-- @@ L77-81 verbatim
lemma mixture_eq_through (P Q : Law α) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    mixture P Q t h0 h1 = (coinP t h0 h1).through (fun b => if b then P else Q) := by
  apply ext_of_Ex; intro f
  rw [Ex_through,mixture_Ex,coinP_Ex]
  rfl


-- @@ L83-87 verbatim
lemma H_mixture_ge (P Q : Law α) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) (X : α → β) :
    t*(P.H X)+(1-t)*(Q.H X) ≤ (mixture P Q t h0 h1).H X := by
  rw [mixture_eq_through]
  have h := H_through_ge (coinP t h0 h1) (fun b => if b then P else Q) X
  rwa [coinP_Ex] at h


-- @@ L89-94 verbatim
lemma Hcond_mixture_ge (P Q : Law α) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (X : α → β) (W : α → γ) :
    t*(P.Hcond X W)+(1-t)*(Q.Hcond X W) ≤ (mixture P Q t h0 h1).Hcond X W := by
  rw [mixture_eq_through]
  have h := Hcond_through (coinP t h0 h1) (fun b => if b then P else Q) X W
  rwa [coinP_Ex] at h


-- @@ L96-105 verbatim
lemma entropy_mixture_le (P Q : Law α) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    (mixture P Q t h0 h1).entropy ≤ log 2 + (t*P.entropy+(1-t)*Q.entropy) := by
  rw [mixture_eq_through, ← H_self]
  let C := coinP t h0 h1
  let f (b : Bool) := if b then P else Q
  refine (H_through_le C f (fun x => x)).trans ?_
  dsimp only [C]
  rw [coinP_Ex]
  simp only [f, H_self]; norm_num
  exact coinP_entropy _ _ _


-- @@ L107-109 verbatim
lemma entropy_mixture_ge (P Q : Law α) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    t*P.entropy+(1-t)*Q.entropy ≤ (mixture P Q t h0 h1).entropy := by
  simpa only [H_self] using H_mixture_ge P Q t h0 h1 (fun x => x)


-- @@ L111-132 verbatim
/-- Support version of the entropy bound. -/
lemma entropy_le_log_size (P : Law α) (s : Finset α)
    (h : ∀ x, 0 < P x → x ∈ s) : P.entropy ≤ log (s.card : ℝ) := by
  classical
  let q (x : α) := if x ∈ s then (s.card:ℝ)⁻¹ else 0
  have hs : 0 < (s.card:ℝ) := by
    obtain ⟨x,hx⟩ := P.mem_nonempty
    exact_mod_cast (Finset.card_pos.mpr ⟨x,h x hx⟩)
  have H : P.entropy ≤ P.crossE q := by
    apply entropy_le_cross_aux
    · intro x; dsimp only [q]; split_ifs <;> positivity
    · rw [← Finset.sum_subset (Finset.subset_univ s) (by intros i _ hi; simp [q,hi])]
      rw [Finset.sum_congr rfl (fun x (hx : x ∈ s) => ite_eq_left hx : ∀ x ∈ s, q x = (s.card:ℝ)⁻¹)]
      simp [ne_of_gt hs]
    · intro x hx
      dsimp only [q]; rw [ite_eq_left (h x hx)]; positivity
  refine H.trans (le_of_eq ?_)
  unfold crossE
  calc
    _ = P.Ex (fun _ => log (s.card:ℝ)) := P.Ex_congr_mem fun x hx => by
      simp only [q, ite_eq_left (h x hx), log_inv, neg_neg]
    _ = _ := P.Ex_const _


-- @@ L134-184 verbatim
/-- Entropy modulus sufficient for the replacement by independent letters. -/
theorem entropy_le_of_tv (P Q : Law α) (s : Finset α)
    (h : ∀ x, 0 < P x → x ∈ s) :
    P.entropy ≤ Q.entropy + (log 2 + P.tv Q * log (s.card:ℝ)) := by
  let t := P.tv Q
  have h0 : 0 ≤ t := tv_nonneg _ _
  have h1 : t ≤ 1 := tv_le_one _ _
  let a (x : α) := min (P x) (Q x)
  have ht : ∑ x, a x = 1-t := P.tv_common Q
  have ha (x : α) : 0 ≤ a x := le_min (P.nonneg x) (Q.nonneg x)
  have hpl (x : α) : 0 ≤ P x - a x := sub_nonneg.mpr (min_le_left _ _)
  have hql (x : α) : 0 ≤ Q x - a x := sub_nonneg.mpr (min_le_right _ _)
  have hps : ∑ x, (P x - a x) = t := by rw [Finset.sum_sub_distrib, P.total, ht]; ring
  have hqs : ∑ x, (Q x - a x) = t := by rw [Finset.sum_sub_distrib, Q.total, ht]; ring
  have hg : 0 ≤ log (2:ℝ) := log_nonneg (by norm_num)
  change _ ≤ _+(log 2+t*_)
  obtain ht0|ht0 := eq_or_lt_of_le h0
  · have H : P = Q := by
      apply Law.ext; intro x
      have h1 := Finset.single_le_sum (f:=fun x => P x-a x) (fun y _ => hpl y) (Finset.mem_univ x)
      have h2 := Finset.single_le_sum (f:=fun x => Q x-a x) (fun y _ => hql y) (Finset.mem_univ x)
      linarith [hpl x,hql x]
    rw [← ht0, H,zero_mul]; linarith
  obtain ht1|ht1 := eq_or_lt_of_le h1
  · rw [ht1, one_mul]; linarith [entropy_le_log_size P s h, Q.entropy_nonneg]
  have hb := proportional_apply a ha (ht.symm ▸ sub_pos.mpr ht1)
  let R := proportional a ha (by linarith)
  let U := proportional _ hpl (by linarith)
  let V := proportional _ hql (by linarith)
  have hP : P = mixture U R t h0 h1 := by
    apply Law.ext; intro x
    rw [mixture_apply]
    dsimp only [R,U]; rw [proportional_apply, proportional_apply, ht,hps]
    field_simp
    ring

  have hQ : Q = mixture V R t h0 h1 := by
    apply Law.ext; intro x
    rw [mixture_apply]
    dsimp only [R,V]; rw [proportional_apply, proportional_apply, ht,hqs]
    field_simp
    ring
  have hU : U.entropy ≤ log (s.card:ℝ) := entropy_le_log_size U s fun x hx => by
    apply h
    rw [hP,mixture_apply]
    exact add_pos_of_pos_of_nonneg (mul_pos ht0 hx)
      (mul_nonneg (sub_nonneg.mpr h1) (R.nonneg x))
  have Hu := entropy_mixture_le U R t h0 h1
  have Hv := entropy_mixture_ge V R t h0 h1
  rw [hP, hQ]
  nlinarith [V.entropy_nonneg]


-- @@ L186-186 verbatim
end FourierLLogL.Law


-- @@ L188-188 verbatim
end OAI
