/-
Copyright (c) 2026 PFR contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PFR contributors
-/

module

public import LeanPool.PFR.MultiTauFunctional
import LeanPool.PFR.ForMathlib.Entropy.Group
import LeanPool.PFR.ForMathlib.FiniteRange.IdentDistrib
import LeanPool.PFR.Mathlib.Data.Fin.Basic
import LeanPool.PFR.Mathlib.MeasureTheory.Group.Arithmetic
import LeanPool.ZhangYeungInequality.PFR.Mathlib.Probability.Independence.Basic


-- @@ L16-18 verbatim
/-!
# Bounding the mutual information
-/


-- @@ L20-20 verbatim
open scoped ZhangYeungPFR



-- @@ L23-23 verbatim
universe u

-- @@ L24-24 verbatim
open MeasureTheory ProbabilityTheory


-- @@ L26-47 expanded
public lemma multiDist_of_cast {m m' : ℕ} (h : m' = m) {Ω : Fin m → Type*}
    (hΩ : ∀ i, MeasureSpace (Ω i)) (hΩfin : ∀ i, IsFiniteMeasure (hΩ i).volume) {G : Type*}
    [MeasurableFinGroup G] (X : ∀ i, Ω i → G) :
    (multiDist (fun i ↦ hΩ (i.cast h)) fun i ↦ X (i.cast h)) = multiDist hΩ X :=
  by
  unfold multiDist
  congr 1
  · apply IdentDistrib.entropy_congr
    refine
      { aemeasurable_fst := by fun_prop
        aemeasurable_snd := by fun_prop
        map_eq := ?_ }
    have :
      (fun (x : Fin m' → G) ↦ ∑ i, x i) =
        (fun (x : Fin m → G) ↦ ∑ i, x i) ∘ (fun (x : Fin m' → G) ↦ x ∘ (Fin.cast h.symm)) :=
      by ext x; dsimp; symm; apply Function.Bijective.sum_comp (Fin.cast_bijective h.symm)
    rw [this, ← Measure.map_map] <;> try fun_prop
    congr
    exact Measure.pi_map_piCongrLeft (finCongr h) (fun i ↦ Measure.map (X i) ℙ)
  congr 1
  · rw [h]
  convert Finset.sum_bijective _ (Fin.cast_bijective h) ?_ ?_ using 1 <;> simp


-- @@ L49-86 verbatim
/-- For Mathlib? -/
public
lemma ProbabilityTheory.iIndepFun.sum_elim {Ω I J G : Type*} [MeasurableSpace Ω] [MeasurableSpace G]
    (μ : Measure Ω) {f : I → Ω → G} {g : J → Ω → G} (hf_indep : iIndepFun f μ)
    (hg_indep : iIndepFun g μ) (hindep : IndepFun (fun ω x ↦ f x ω) (fun ω y ↦ g y ω) μ) :
    iIndepFun (Sum.elim f g) μ := by
  rw [iIndepFun_iff] at hf_indep hg_indep ⊢
  intro s E hE
  have : s.toLeft.disjSum s.toRight = s := Finset.toLeft_disjSum_toRight
  rw [←this, Finset.prod_disjSum,←hf_indep,←hg_indep]
  · simp_rw [MeasurableSpace.measurableSet_comap] at hE
    choose F hF using hE
    let S := ⋂ (i :s.toLeft), {x: I → G | x i ∈ F (Sum.inl i) (Finset.mem_toLeft.mp i.property)}
    let T := ⋂ (j:s.toRight), {y: J → G | y j ∈ F (Sum.inr j) (Finset.mem_toRight.mp j.property)}
    convert hindep.measure_inter_preimage_eq_mul S T _ _
    · ext ω
      simp only [Set.mem_iInter, Sum.forall, Finset.inl_mem_disjSum, Finset.mem_toLeft,
        Finset.inr_mem_disjSum, Finset.mem_toRight, Set.mem_inter_iff, Set.mem_preimage,
        Set.mem_ofPred_eq, Subtype.forall, S, T]
      congr! with i hi i hi <;> simp [← (hF _ hi).2]
    · ext ω
      simp only [Finset.mem_toLeft, Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq,
        Subtype.forall, S]
      congr! with i hi
      simp [← (hF _ hi).2]
    · ext ω
      simp only [Finset.mem_toRight, Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq,
        Subtype.forall, T]
      congr! with i hi
      simp [← (hF _ hi).2]
    all_goals {
      apply MeasurableSet.iInter; intro ⟨i, hi⟩
      simp only
      convert! measurableSet_preimage (measurable_pi_apply i) _
      apply (hF _ _).1
    }
  · intro i hi; apply hE; exact Finset.mem_toRight.mp hi
  intro j hj; apply hE; exact Finset.mem_toLeft.mp hj


-- @@ L88-95 expanded
public lemma condMultiDist_of_cast {m m' : ℕ} (h : m' = m) {Ω : Fin m → Type*}
    (hΩ : ∀ i, MeasureSpace (Ω i)) {G S : Type*} [MeasurableFinGroup G] [Fintype S]
    (X : ∀ i, Ω i → G) (Y : ∀ i, Ω i → S) :
    (condMultiDist (fun i ↦ hΩ (i.cast h)) (fun i ↦ X (i.cast h)) fun i ↦ Y (i.cast h)) =
      condMultiDist hΩ X Y :=
  by
  subst m'
  rfl


-- @@ L97-189 expanded
private lemma row_entropy_le {G Ωₒ : Type u} [MeasurableFinGroup G] [MeasureSpace Ωₒ]
    {p : multiRefPackage G Ωₒ} {Ω : Type u} [hΩ : MeasureSpace Ω] [IsProbabilityMeasure hΩ.volume]
    {X : Fin p.m → Ω → G} (hX : ∀ i, Measurable (X i)) (hIndependent : iIndepFun X) {Ω' : Type u}
    [hΩ' : MeasureSpace Ω'] [IsProbabilityMeasure hΩ'.volume] {X' : Fin p.m × Fin p.m → Ω' → G}
    (hX' : ∀ i j, Measurable (X' (i, j))) (hIndependent' : iIndepFun X')
    (hPermutation :
      ∀ j,
        ∃ e : Fin p.m ≃ Fin p.m,
          IdentDistrib (fun ω ↦ fun i ↦ X' (i, j) ω) (fun ω ↦ fun i ↦ X (e i) ω))
    (one : Fin p.m) (i : Fin p.m) :
    let V : Fin p.m → Ω' → G := fun i ω ↦ ∑ j, X' (i, j) ω
    entropy (V i) volume ≤
      entropy (∑ j, X j) volume + ∑ j, rdist (X' (i, j)) (X' (i, j)) volume volume :=
  by
  have hm := p.hm
  have _ : NeZero p.m := by rw [neZero_iff]; omega
  dsimp only
  obtain ⟨ν, XX, XX', hν, hXX, hXX', h_indep_XX_XX', hident_X, hident_X', hfin_XX, hfin_XX'⟩ :=
    independent_copies_finiteRange (X := fun ω i ↦ X i ω) (Y := fun ω q ↦ X' q ω) (by fun_prop)
      (by fun_prop) ℙ ℙ
  let Ω'' := (Fin p.m → G) × (Fin p.m × Fin p.m → G)
  let _ : MeasureSpace Ω'' := ⟨ν⟩
  let Z : Fin p.m → Ω'' → G := fun i ω ↦ XX ω i
  let Z' : Fin p.m × Fin p.m → Ω'' → G := fun i ω ↦ XX' ω i
  have hindep_Z : iIndepFun Z ℙ :=
    by
    rw [iIndepFun_iff_map_fun_eq_pi_map] at hIndependent ⊢ <;> try fun_prop
    convert hIndependent with i
    · exact IdentDistrib.map_eq hident_X
    apply IdentDistrib.map_eq
    exact hident_X.comp (u := fun x ↦ x i) (by fun_prop)
  have hindep_Z' : iIndepFun Z' ℙ :=
    by
    rw [iIndepFun_iff_map_fun_eq_pi_map] at hIndependent' ⊢ <;> try fun_prop
    convert hIndependent' with i
    · exact IdentDistrib.map_eq hident_X'
    apply IdentDistrib.map_eq
    exact hident_X'.comp (u := fun x ↦ x i) (by fun_prop)
  have hindep_all : iIndepFun (Sum.elim Z Z') ℙ := hindep_Z.sum_elim ℙ hindep_Z' h_indep_XX_XX'
  let s : Finset (Fin p.m ⊕ (Fin p.m × Fin p.m)) := Finset.image Sum.inl Finset.univ
  let t : Finset (Fin p.m ⊕ (Fin p.m × Fin p.m)) := Finset.image Sum.inr {q | q.1 = i}
  have hdisj : Disjoint s t := by rw [Finset.disjoint_left]; simp [s, t]
  have ht : t.Nonempty := by use Sum.inr (i, one); simp [t]
  choose e he using hPermutation
  let f : Fin p.m ⊕ (Fin p.m × Fin p.m) → Fin p.m ⊕ (Fin p.m × Fin p.m) := fun x ↦
    match x with
    | Sum.inl i => Sum.inl i
    | Sum.inr (i, j) => Sum.inl ((e j) i)
  convert ent_of_sum_le_ent_of_sum hdisj _ _ hindep_all f _
  · apply IdentDistrib.entropy_congr
    convert! hident_X'.symm.comp (u := fun x ↦ ∑ j : Fin p.m, x (i, j)) _ <;> try fun_prop
    ext ω
    simp only [Finset.sum_apply, Finset.coe_filter, Finset.mem_univ, true_and, Sum.inr.injEq,
      implies_true, Set.injOn_of_eq_iff_eq, Finset.sum_image, Sum.elim_inr, Function.comp_apply, t,
      Z, Z']
    apply Finset.sum_nbij' Prod.snd (fun j ↦ (i, j))
    on_goal 5 =>
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.forall]
      rintro a b rfl
      rfl
    all_goals simp
  · apply IdentDistrib.entropy_congr
    convert! hident_X.symm.comp (u := fun x ↦ ∑ j, x j) _ <;> try fun_prop
    all_goals ext ω; simp [Z, Z', s]
    simp [Finset.sum_image Sum.inl_injective.injOn]
  · let g : Fin p.m ⊕ (Fin p.m × Fin p.m) → Fin p.m := fun x ↦
      match x with
      | Sum.inl i => i
      | Sum.inr (_, j) => j
    apply
      Finset.sum_nbij' (fun j ↦ Sum.inr (i, j)) g (by simp [t]) (by simp [t, g]) (by simp [g])
        (by simp [t, g])
    simp only [Finset.mem_univ, Sum.elim_inr, Sum.elim_inl, forall_const, f]
    intro j
    have hident_1 : IdentDistrib (X' (i, j)) (Z' (i, j)) ℙ ℙ := by
      exact hident_X'.symm.comp (u := fun x ↦ x (i, j)) (by fun_prop)
    have hident_2 : IdentDistrib (Z' (i, j)) (Z ((e j) i)) ℙ ℙ :=
      by
      apply hident_1.symm.trans
      have h1 : IdentDistrib (X ((e j) i)) (Z ((e j) i)) ℙ ℙ := by
        exact hident_X.symm.comp (u := fun x ↦ x ((e j) i)) (by fun_prop)
      have h2 : IdentDistrib (X' (i, j)) (X ((e j) i)) ℙ ℙ := by
        exact (he j).comp (u := fun x ↦ x i) (by fun_prop)
      exact h2.trans h1
    calc
      _ = rdist (Z' (i, j)) (Z ((e j) i)) volume volume :=
        IdentDistrib.rdist_congr hident_1 (hident_1.trans hident_2)
      _ =
          entropy (Z' (i, j) - Z ((e j) i)) volume - entropy (Z' (i, j)) volume / 2 -
            entropy (Z ((e j) i)) volume / 2 :=
        by
        apply IndepFun.rdist_eq <;> try fun_prop
        symm
        apply h_indep_XX_XX'.comp (φ := fun x ↦ x (e j i)) (ψ := fun x ↦ x (i, j)) <;> fun_prop
      _ =
          entropy (Z' (i, j) - Z ((e j) i)) volume - entropy (Z ((e j) i)) volume / 2 -
            entropy (Z ((e j) i)) volume / 2 :=
        by rw [IdentDistrib.entropy_congr hident_2]
      _ = _ := by ring
  · fun_prop
  intro x
  simp [f, t, s]
  aesop


-- @@ L191-191 expanded
private def firstIndex {m : ℕ} (hm : m ≥ 2) : Fin m :=
  ⟨1, by omega⟩


-- @@ L193-193 expanded
private def finalIndex {m : ℕ} (hm : m ≥ 2) : Fin m :=
  ⟨m - 1, by omega⟩


-- @@ L195-197 verbatim
private abbrev rowTail {G Ω : Type*} [AddCommMonoid G] {m : ℕ}
    (X : Fin m × Fin m → Ω → G) (i j : Fin m) : Ω → G :=
  ∑ k ∈ Finset.Ici j, X (i, k)


-- @@ L199-244 expanded
private lemma conditional_self_rdist_le {G Ω : Type u} [MeasurableFinGroup G] [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {m : ℕ} (hm : m ≥ 2) {X : Fin m × Fin m → Ω → G}
    (hX : ∀ i j, Measurable (X (i, j))) (hIndependent : iIndepFun X) (i j : Fin m)
    (hj : j ∈ Finset.Iio (finalIndex hm)) :
    condRuzsaDist' (X (i, j)) (X (i, j)) (rowTail X i j) volume volume ≤
      rdist (X (i, j)) (X (i, j)) volume volume +
        (entropy (rowTail X i j) volume - entropy (rowTail X i (j + firstIndex hm)) volume) / 2 :=
  by
  calc
    _ ≤
        rdist (X (i, j)) (X (i, j)) volume volume +
          mutualInfo (X (i, j)) (rowTail X i j) volume / 2 :=
      by apply condRuzsaDist_le' <;> fun_prop
    _ =
        rdist (X (i, j)) (X (i, j)) volume volume +
          (entropy (rowTail X i j) volume -
              condEntropy (rowTail X i (j + firstIndex hm)) (X (i, j)) volume) /
            2 :=
      by
      congr
      rw [mutualInfo_comm]
      convert mutualInfo_eq_entropy_sub_condEntropy .. using 2 <;> try infer_instance
      all_goals try fun_prop
      rw [← condEntropy_add_left] <;> try fun_prop
      congr
      convert Finset.add_sum_erase (a := j) .. using 3
      · rfl
      · obtain ⟨j, hj'⟩ := j
        ext ⟨k, hk⟩
        simp [finalIndex, firstIndex] at hj ⊢
        have : (j + 1) % m = j + 1 := Nat.mod_eq_of_lt (by omega)
        simp [← Fin.val_fin_le, Fin.val_add, this]
      simp
    _ = _ := by
      congr
      apply ProbabilityTheory.IndepFun.condEntropy_eq_entropy <;> try fun_prop
      let T : Finset (Fin m × Fin m) := {q | q.2 > j}
      let T' : Finset (Fin m × Fin m) := {q | q.2 = j}
      let φ : (T → G) → G := fun f ↦
        ∑ k : Finset.Ici (j + firstIndex hm),
          f
            ⟨(i, k), by
              obtain ⟨⟨k, hk⟩, hk'⟩ := k
              obtain ⟨j, hj'⟩ := j
              simp [finalIndex] at hj ⊢
              have : (j + 1) % m = j + 1 := Nat.mod_eq_of_lt (by omega)
              simp [T, ← Fin.val_fin_le, Fin.val_add, this, firstIndex] at hj ⊢ hk'
              omega⟩
      let φ' : (T' → G) → G := fun f ↦ f ⟨(i, j), by simp [T']⟩
      convert
          iIndepFun.finsets_comp' _ hIndependent (by fun_prop) (φ := φ)
            (show Measurable φ by fun_prop) (show Measurable φ' by fun_prop) with
          ω ω <;>
        try simp [φ]
      · simp [← Finset.sum_attach (.Ici _)]
      rw [Finset.disjoint_left]
      rintro ⟨_, _⟩ h h'
      simp [T, T'] at h h'
      order


-- @@ L246-281 expanded
private lemma final_to_row_rdist_le {G Ω : Type u} [MeasurableFinGroup G] [MeasureSpace Ω]
    [IsProbabilityMeasure (ℙ : Measure Ω)] {m : ℕ} (hm : m ≥ 2) {X : Fin m × Fin m → Ω → G}
    (hX : ∀ i j, Measurable (X (i, j))) (hIndependent : iIndepFun X) (i : Fin m) :
    rdist (X (i, finalIndex hm)) (∑ j, X (i, j)) volume volume ≤
      rdist (X (i, finalIndex hm)) (X (i, finalIndex hm)) volume volume +
        (entropy (∑ j, X (i, j)) volume - entropy (X (i, finalIndex hm)) volume) / 2 :=
  by
  have hSum : ∑ j, X (i, j) = X (i, finalIndex hm) + ∑ j ∈ Finset.Iio (finalIndex hm), X (i, j) :=
    by
    symm
    ext ω
    simp only [Pi.add_apply, Finset.sum_apply]
    convert Finset.add_sum_erase (a := finalIndex hm) .. using 3
    · rfl
    · ext ⟨j, hj⟩
      simp [finalIndex]
      omega
    simp
  simp only [hSum, ← inv_mul_eq_div, ge_iff_le]
  apply kvm_ineq_III_aux' <;> try fun_prop
  let T : Finset (Fin m × Fin m) := {q | q.2 = finalIndex hm}
  let T' : Finset (Fin m × Fin m) := {q | q.2 < finalIndex hm}
  let φ : (T → G) → G := fun f ↦ f ⟨(i, finalIndex hm), by simp [T]⟩
  let φ' : (T' → G) → G := fun f ↦
    ∑ j : Finset.Iio (finalIndex hm),
      f
        ⟨(i, j), by
          obtain ⟨j, hj⟩ := j
          simpa [T'] using hj⟩
  convert
    iIndepFun.finsets_comp' _ hIndependent (by fun_prop) (φ := φ) (show Measurable φ by fun_prop)
      (show Measurable φ' by fun_prop) with
    ω ω
  · simp only [Finset.sum_apply, Finset.univ_eq_attach, φ']
    symm
    convert Finset.sum_attach _ _
    rfl
  rw [Finset.disjoint_left]
  rintro ⟨_, _⟩ h h'
  simp [T, T'] at h h'
  order


-- @@ L283-303 expanded
/-- The mutual-information chain rule with any index size at least two. -/
private lemma mutualInfo_le_multiDist_chain {G Ω : Type u} [MeasurableFinGroup G]
    [hΩ : MeasureSpace Ω] [IsProbabilityMeasure (ℙ : Measure Ω)] {m : ℕ} (hm : m ≥ 2)
    (X : Fin m × Fin m → Ω → G) (hX : ∀ i j, Measurable (X (i, j))) (hIndependent : iIndepFun X) :
    condMutualInfo (fun ω ↦ fun j ↦ ∑ i, X (i, j) ω) (fun ω ↦ fun i ↦ ∑ j, X (i, j) ω)
        (fun ω ↦ ∑ i, ∑ j, X (i, j) ω) volume ≤
      ∑ j ∈ Finset.Iio (finalIndex hm),
          ((multiDist (fun _ ↦ hΩ) fun i ↦ X (i, j)) -
            condMultiDist (fun _ ↦ hΩ) (fun i ↦ X (i, j)) fun i ↦ rowTail X i j) +
        ((multiDist (fun _ ↦ hΩ) fun i ↦ X (i, finalIndex hm)) -
          multiDist (fun _ ↦ hΩ) fun i ↦ ∑ j, X (i, j)) :=
  by
  cases m with
  | zero => omega
  | succ m =>
    have hlast : finalIndex hm = Fin.last m := rfl
    simpa only [hlast, rowTail, Fin.Iio_last_eq_map, Finset.sum_map, Fin.castSuccEmb_apply,
      Fintype.sum_prod_type, Finset.sum_fn, add_sub_assoc, Fin.top_eq_last] using
      cor_multiDist_chainRule hΩ X (fun i ↦ hX i.1 i.2) hIndependent


-- @@ L304-471 expanded
/-- Suppose that $X_{i, j}$, $1 \leq i, j \leq m$, are jointly independent $G$-valued random
variables, such that for each $j = 1,\dots,m$, the random variables $(X_{i, j})_{i = 1}^m$
coincide in distribution with some permutation of $X_{[m]}$.
  Write
$$ {\mathcal I} := \bbI[ \bigl(\sum_{i=1}^m X_{i, j}\bigr)_{j =1}^{m}
: \bigl(\sum_{j=1}^m X_{i, j}\bigr)_{i = 1}^m
\; \big| \; \sum_{i=1}^m \sum_{j = 1}^m X_{i, j} ].
 $$
 Then ${\mathcal I} \leq 4 m^2 \eta k.$
-/
public lemma mutual_information_le {G Ωₒ : Type u} [MeasurableFinGroup G] [MeasureSpace Ωₒ]
    {p : multiRefPackage G Ωₒ} {Ω : Type u} [hΩ : MeasureSpace Ω] [IsProbabilityMeasure hΩ.volume]
    {X : Fin p.m → Ω → G} (hX : ∀ i, Measurable (X i)) (h_indep : iIndepFun X)
    (h_min : multiTauMinimizes p (fun _ ↦ Ω) (fun _ ↦ hΩ) X) {Ω' : Type u} [hΩ' : MeasureSpace Ω']
    [IsProbabilityMeasure hΩ'.volume] {X' : Fin p.m × Fin p.m → Ω' → G}
    (hX' : ∀ i j, Measurable (X' (i, j))) (h_indep' : iIndepFun X')
    (hperm :
      ∀ j,
        ∃ e : Fin p.m ≃ Fin p.m,
          IdentDistrib (fun ω ↦ (fun i ↦ X' (i, j) ω)) (fun ω ↦ (fun i ↦ X (e i) ω))) :
    condMutualInfo (fun ω ↦ (fun j ↦ ∑ i, X' (i, j) ω)) (fun ω ↦ (fun i ↦ ∑ j, X' (i, j) ω))
        (fun ω ↦ ∑ i, ∑ j, X' (i, j) ω) volume ≤
      p.m * (4 * p.m + 1) * p.η * multiDist (fun _ ↦ hΩ) X :=
  by
  have hm := p.hm
  have _ : NeZero p.m := by rw [neZero_iff]; omega
  have hη := p.hη
  set I₀ :=
    condMutualInfo (fun ω ↦ (fun j ↦ ∑ i, X' (i, j) ω)) (fun ω ↦ (fun i ↦ ∑ j, X' (i, j) ω))
      (fun ω ↦ ∑ i, ∑ j, X' (i, j) ω) volume
  set k := multiDist (fun x ↦ hΩ) X
  set one : Fin p.m := ⟨1, by omega⟩
  set last : Fin p.m := ⟨p.m - 1, by omega⟩
  set column : Fin p.m → Fin p.m → Ω' → G := fun j i ω ↦ X' (i, j) ω
  set V : Fin p.m → Ω' → G := fun i ω ↦ ∑ j, X' (i, j) ω
  set S : Fin p.m → Fin p.m → Ω' → G := fun i j ↦ ∑ k ∈ .Ici j, X' (i, k)
  set A : Fin p.m → ℝ := fun j ↦
    multiDist (fun _ ↦ hΩ') (column j) - condMultiDist (fun _ ↦ hΩ') (column j) fun i ↦ S i j
  set B : ℝ :=
    multiDist (fun _ ↦ hΩ') (column last) - multiDist (fun _ ↦ hΩ') fun i ω ↦ ∑ j, X' (i, j) ω
  have h1 : I₀ ≤ ∑ j ∈ .Iio last, A j + B := by
    simpa only [I₀, A, B, column, S, last, finalIndex, rowTail, Finset.sum_fn] using
      mutualInfo_le_multiDist_chain p.hm X' hX' h_indep'
  have hD (j : Fin p.m) : multiDist (fun x ↦ hΩ') (column j) = k :=
    by
    obtain ⟨e, he⟩ := hperm j
    calc
      _ = multiDist (fun x ↦ hΩ) fun i ω ↦ X (e i) ω :=
        by
        apply multiDist_copy _ _ _ _ _
        intro i; exact IdentDistrib.comp (u := fun x ↦ x i) he (by fun_prop)
      _ = _ := by convert multiDist_of_perm (fun _ ↦ hΩ) _ _ e <;> try infer_instance
  have h2 {j : Fin p.m} (hj : j ∈ Finset.Iio last) :
    A j ≤ p.η * ∑ i, condRuzsaDist' (X' (i, j)) (X' (i, j)) (S i j) volume volume :=
    by
    obtain ⟨e, he⟩ := hperm j
    simp only [A, hD]
    convert
        sub_condMultiDistance_le' inferInstance hX h_min inferInstance (X' := fun i ↦ X' (i, j)) _ _
          e using
        3 with i _ <;>
      try infer_instance
    all_goals try fun_prop
    apply condRuzsaDist'_of_copy <;> try fun_prop
    · exact IdentDistrib.comp (u := fun x ↦ x i) he (by fun_prop)
    apply IdentDistrib.refl; fun_prop
  have h3 : B ≤ p.η * ∑ i, rdist (X' (i, last)) (V i) volume volume :=
    by
    obtain ⟨e, he⟩ := hperm last
    simp only [B, hD, V]
    convert
      sub_multiDistance_le' inferInstance hX h_min inferInstance (X' := fun i ↦ V i) (by fun_prop)
        e using
      3 with i _
    apply IdentDistrib.rdist_congr_left (by fun_prop);
    exact IdentDistrib.comp (u := fun x ↦ x i) he (by fun_prop)
  have h4 (i : Fin p.m) {j : Fin p.m} (hj : j ∈ Finset.Iio last) :
    condRuzsaDist' (X' (i, j)) (X' (i, j)) (S i j) volume volume ≤
      rdist (X' (i, j)) (X' (i, j)) volume volume +
        (entropy (S i j) volume - entropy (S i (j + one)) volume) / 2 :=
    by
    simpa [S, last, one, finalIndex, firstIndex] using
      conditional_self_rdist_le p.hm hX' h_indep' i j hj
  have h4a (i : Fin p.m) :
    ∑ j ∈ .Iio last, (entropy (S i j) volume - entropy (S i (j + one)) volume) =
      entropy (V i) volume - entropy (X' (i, last)) volume :=
    by
    convert
      Finset.sum_range_sub' (fun k ↦ entropy (∑ j ∈ {j | j.val ≥ k}, X' (i, j)) volume) (p.m - 1)
    · have (k : Fin p.m) : S i k = ∑ j ∈ {j | j.val ≥ k.val}, X' (i, j) :=
        by
        unfold S; congr
        ext ⟨j, hj⟩; obtain ⟨k, hk⟩ := k; simp
      simp_rw [this]
      convert Finset.sum_nbij (fun i ↦ i.val) (s := Finset.Iio last) ..
      · intro ⟨_, _⟩; simp [last]
      · intro ⟨_, _⟩ _ ⟨_, _⟩ _; simp
      · intro _ hi; simpa [last] using hi
      intro ⟨j, hj⟩ hj'
      simp only [Finset.mem_Iio, Fin.mk_lt_mk, ge_iff_le, Fin.val_fin_le, sub_right_inj, last,
        one] at hj' ⊢
      rcongr ⟨k, hk⟩
      have : (j + 1) % p.m = j + 1 := Nat.mod_eq_of_lt (by omega)
      simp [← Fin.val_fin_le, Fin.val_add, this]
    · ext ω; simp [V]
    ext ω
    simp only [ge_iff_le, tsub_le_iff_right, Finset.sum_apply]
    symm
    convert Finset.sum_singleton _ last
    ext ⟨j, hk⟩
    simp [last]
    omega
  have h5 (i : Fin p.m) :
    ∑ j ∈ .Iio last, condRuzsaDist' (X' (i, j)) (X' (i, j)) (S i j) volume volume ≤
      ∑ j ∈ .Iio last, rdist (X' (i, j)) (X' (i, j)) volume volume +
        (entropy (V i) volume - entropy (X' (i, last)) volume) / 2 :=
    calc
      _ ≤
          ∑ j ∈ .Iio last,
            (rdist (X' (i, j)) (X' (i, j)) volume volume +
              (entropy (S i j) volume - entropy (S i (j + one)) volume) / 2) :=
        by apply Finset.sum_le_sum; intro j hj; exact h4 i hj
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_div]; congr
        exact h4a i
  have h6 (i : Fin p.m) :
    rdist (X' (i, last)) (V i) volume volume ≤
      rdist (X' (i, last)) (X' (i, last)) volume volume +
        (entropy (V i) volume - entropy (X' (i, last)) volume) / 2 :=
    by
    have hV : V i = ∑ j, X' (i, j) := by
      ext ω
      simp [V]
    rw [hV]
    simpa [last, finalIndex] using final_to_row_rdist_le p.hm hX' h_indep' i
  have h7 :
    I₀ / p.η ≤
      p.m * ∑ i, rdist (X i) (X i) volume volume + ∑ i, entropy (V i) volume -
        ∑ i, entropy (X i) volume :=
    by
    rw [div_le_iff₀' hη]
    apply h1.trans
    calc
      _ ≤
          ∑ j ∈ .Iio last,
              (p.η * (∑ i, condRuzsaDist' (X' (i, j)) (X' (i, j)) (S i j) volume volume)) +
            p.η * ∑ i, rdist (X' (i, last)) (V i) volume volume :=
        by gcongr with j hj; exact h2 hj
      _ ≤
          p.η *
              (∑ i,
                (∑ j ∈ .Iio last, rdist (X' (i, j)) (X' (i, j)) volume volume +
                  (entropy (V i) volume - entropy (X' (i, last)) volume) / 2)) +
            p.η *
              ∑ i,
                (rdist (X' (i, last)) (X' (i, last)) volume volume +
                  (entropy (V i) volume - entropy (X' (i, last)) volume) / 2) :=
        by
        simp only [← Finset.mul_sum, Finset.sum_add_distrib]
        rw [Finset.sum_comm]
        gcongr
        · rw [← Finset.sum_add_distrib]; apply Finset.sum_le_sum; intro i _; exact h5 i
        rw [← Finset.sum_add_distrib]; apply Finset.sum_le_sum; intro i _; exact h6 i
      _ =
          p.η *
            (∑ i,
                  (∑ j ∈ .Iio last, rdist (X' (i, j)) (X' (i, j)) volume volume +
                    rdist (X' (i, last)) (X' (i, last)) volume volume) +
                ∑ i, entropy (V i) volume -
              ∑ i, entropy (X' (i, last)) volume) :=
        by simp_rw [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib]; ring
      _ =
          p.η *
            (∑ j, (∑ i, rdist (X' (i, j)) (X' (i, j)) volume volume) + ∑ i, entropy (V i) volume -
              ∑ i, entropy (X' (i, last)) volume) :=
        by
        rw [Finset.sum_comm]
        rcongr i
        convert Finset.sum_erase_add _ _ _ using 3
        · ext ⟨j, hj⟩; simp [last]; omega
        · infer_instance
        simp
      _ =
          p.η *
            ((∑ j : Fin p.m, (∑ i, rdist (X i) (X i) volume volume)) + ∑ i, entropy (V i) volume -
              ∑ i, entropy (X i) volume) :=
        by
        congr 2
        · congr; ext j; obtain ⟨e, he⟩ := hperm j
          convert Equiv.sum_comp e _ with i _
          apply IdentDistrib.rdist_congr <;> exact he.comp (u := fun x ↦ x i) (by fun_prop)
        obtain ⟨e, he⟩ := hperm last
        convert Equiv.sum_comp e _ with i _
        apply IdentDistrib.entropy_congr; exact he.comp (u := fun x ↦ x i) (by fun_prop)
      _ ≤ _ := by simp
  have h8 (i : Fin p.m) :
    entropy (V i) volume ≤
      entropy (∑ j, X j) volume + ∑ j, rdist (X' (i, j)) (X' (i, j)) volume volume :=
    by simpa [V] using row_entropy_le hX h_indep hX' h_indep' hperm one i
  have h9 :
    ∑ i, entropy (V i) volume ≤
      p.m * ∑ i, rdist (X i) (X i) volume volume + ∑ i, entropy (X i) volume + p.m * k :=
    calc
      _ ≤ ∑ i, (entropy (∑ j, X j) volume + ∑ j, rdist (X' (i, j)) (X' (i, j)) volume volume) := by
        apply Finset.sum_le_sum; intro i _; exact h8 i
      _ ≤ p.m * entropy (∑ j, X j) volume + ∑ j, ∑ i, rdist (X' (i, j)) (X' (i, j)) volume volume :=
        by rw [Finset.sum_add_distrib, Finset.sum_comm]; simp
      _ =
          (∑ i, entropy (X i) volume + p.m * k) +
            ∑ j : Fin p.m, ∑ i, rdist (X i) (X i) volume volume :=
        by
        congr
        · have : k = multiDist (fun _ ↦ hΩ) X := rfl
          rw [this, multiDist_indep _ _ h_indep]
          · field_simp; ring
          fun_prop
        ext j
        obtain ⟨e, he⟩ := hperm j
        convert Equiv.sum_comp e _ with i _
        apply IdentDistrib.rdist_congr <;> exact .comp (u := fun x ↦ x i) he (by fun_prop)
      _ = _ := by simp; abel
  have h10 : I₀ / p.η ≤ 2 * p.m * ∑ i, rdist (X i) (X i) volume volume + p.m * k := by linarith
  have h11 : ∑ i, rdist (X i) (X i) volume volume ≤ 2 * p.m * k := by
    convert multidist_ruzsa_II hm _ _ _ hX _ <;> try infer_instance
  calc
    _ ≤ p.η * (2 * p.m * ∑ i, rdist (X i) (X i) volume volume + p.m * k) := by
      rwa [← div_le_iff₀' (by positivity)]
    _ ≤ p.η * (2 * p.m * (2 * p.m * k) + p.m * k) := by gcongr
    _ = _ := by ring

