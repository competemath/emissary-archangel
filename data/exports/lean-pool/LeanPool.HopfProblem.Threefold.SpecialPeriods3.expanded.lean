/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Foundations.LocalOrbitQuotient
import all LeanPool.HopfProblem.Foundations.LocalOrbitQuotient


-- @@ L12-16 verbatim
/-!
# Hopf problem: threefold · special periods 3

Supporting definitions and proofs for this stage of the six-sphere construction.
-/



-- @@ L19-19 verbatim
open Set Function Filter Manifold Topology


-- @@ L21-24 verbatim
open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane


-- @@ L26-26 verbatim
universe u v


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
namespace Mathoverflow1973


-- @@ L32-32 verbatim
local infixr:80 " ≫ₚ " => Path.trans


-- @@ L34-34 verbatim
local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f


-- @@ L36-38 verbatim
private theorem SpecialPeriods.CoprodTorsion.word_prod_injective {ι : Type*} {M : ι → Type*}
    [∀ i, Monoid (M i)] : Function.Injective (Monoid.CoprodI.Word.prod (M := M)) := by
  classical exact (Monoid.CoprodI.Word.equiv (M := M)).symm.injective


-- @@ L40-48 verbatim
private theorem SpecialPeriods.CoprodTorsion.word_prod_eq_one_iff {ι : Type*} {M : ι → Type*}
    [∀ i, Monoid (M i)] (w : Monoid.CoprodI.Word M) :
    w.prod = 1 ↔ w = Monoid.CoprodI.Word.empty := by
  constructor
  · intro h
    apply word_prod_injective
    simpa only [Monoid.CoprodI.Word.prod_empty] using h
  · rintro rfl
    exact Monoid.CoprodI.Word.prod_empty


-- @@ L50-54 verbatim
private theorem SpecialPeriods.CoprodTorsion.neWord_prod_ne_one {ι : Type*} {M : ι → Type*}
    [∀ i, Monoid (M i)] {i j : ι} (w : Monoid.CoprodI.NeWord M i j) : w.prod ≠ 1 := by
  intro h
  have hw : w.toWord = Monoid.CoprodI.Word.empty := (word_prod_eq_one_iff w.toWord).mp h
  exact w.toList_ne_nil (congrArg Monoid.CoprodI.Word.toList hw)


-- @@ L56-60 verbatim
private def
    SpecialPeriods.CoprodTorsion.neWord_pow_succ {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]
    {i j : ι} (w : Monoid.CoprodI.NeWord M i j) (h : i ≠ j) : ℕ → Monoid.CoprodI.NeWord M i j
  | 0 => w
  | n + 1 => Monoid.CoprodI.NeWord.append (neWord_pow_succ w h n) h.symm w


-- @@ L62-67 verbatim
private theorem SpecialPeriods.CoprodTorsion.neWord_pow_succ_prod {ι : Type*} {M : ι → Type*}
    [∀ i, Monoid (M i)] {i j : ι} (w : Monoid.CoprodI.NeWord M i j) (h : i ≠ j) (n : ℕ) :
    (neWord_pow_succ w h n).prod = w.prod ^ (n + 1) := by
  induction n with
  | zero => simp [neWord_pow_succ]
  | succ n ih => simp only [neWord_pow_succ, Monoid.CoprodI.NeWord.append_prod, ih, pow_succ]


-- @@ L69-76 verbatim
private theorem SpecialPeriods.CoprodTorsion.neWord_pow_ne_one {ι : Type*} {M : ι → Type*}
    [∀ i, Monoid (M i)] {i j : ι} (w : Monoid.CoprodI.NeWord M i j) (h : i ≠ j) (n : ℕ)
    (hn : 0 < n) : w.prod ^ n ≠ 1 := by
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ n =>
    rw [← neWord_pow_succ_prod w h n]
    exact neWord_prod_ne_one _



-- @@ L79-91 verbatim
private theorem
    SpecialPeriods.CoprodTorsion.word_pow_ne_one_of_endpoints_ne {ι : Type*} {M : ι → Type*}
    [∀ i, Monoid (M i)] (w : Monoid.CoprodI.Word M)
    (h : w.toList.head?.map Sigma.fst ≠ w.toList.getLast?.map Sigma.fst) (n : ℕ) (hn : 0 < n) :
    w.prod ^ n ≠ 1 := by
  have hw : w ≠ Monoid.CoprodI.Word.empty := by
    rintro rfl
    exact h rfl
  obtain ⟨i, j, v, rfl⟩ := Monoid.CoprodI.NeWord.of_word w hw
  have hij : i ≠ j := by
    simpa only [Monoid.CoprodI.NeWord.toWord, Monoid.CoprodI.NeWord.toList_head?,
      Monoid.CoprodI.NeWord.toList_getLast?, Option.map_some, ne_eq, Option.some.injEq] using h
  exact neWord_pow_ne_one v hij n hn


-- @@ L93-99 verbatim
private theorem SpecialPeriods.CoprodTorsion.word_not_isOfFinOrder_of_endpoints_ne {ι : Type*}
    {M : ι → Type*} [∀ i, Monoid (M i)] (w : Monoid.CoprodI.Word M)
    (h : w.toList.head?.map Sigma.fst ≠ w.toList.getLast?.map Sigma.fst) : ¬IsOfFinOrder w.prod :=
  by
  rintro hf
  obtain ⟨n, hn, hpow⟩ := hf.exists_pow_eq_one
  exact word_pow_ne_one_of_endpoints_ne w h n hn hpow


-- @@ L101-106 verbatim
private theorem SpecialPeriods.CoprodTorsion.word_not_isOfFinOrder_of_head_getLast {ι : Type*}
    {M : ι → Type*} [∀ i, Monoid (M i)] (w : Monoid.CoprodI.Word M) (a b : Σ i, M i)
    (ha : w.toList.head? = Option.some a) (hb : w.toList.getLast? = Option.some b)
    (hab : a.1 ≠ b.1) : ¬IsOfFinOrder w.prod := by
  apply word_not_isOfFinOrder_of_endpoints_ne w
  simpa only [ha, hb, Option.map_some, ne_eq, Option.some.injEq] using hab


-- @@ L108-163 verbatim
private theorem SpecialPeriods.CoprodTorsion.exists_shorter_conjugate {ι : Type*} {G : ι → Type*}
    [∀ i, Group (G i)] (w : Monoid.CoprodI.Word G) (a b : Σ i, G i) (l : List (Σ i, G i))
    (hw : w.toList = a :: (l ++ [b])) (hab : a.1 = b.1) :
    ∃ v : Monoid.CoprodI.Word G, v.toList.length < w.toList.length ∧ IsConj v.prod w.prod := by
  classical
  rcases a with ⟨i, a⟩
  rcases b with ⟨j, b⟩
  dsimp only at hab
  subst j
  have hchain : (l ++ [Sigma.mk i b]).IsChain (fun x y : Σ i, G i => x.1 ≠ y.1) := by
    have hc := w.chain_ne
    rw [hw] at hc
    exact hc.tail
  have hletters : ∀ x ∈ l, Sigma.snd x ≠ 1 := by
    intro x hx
    apply w.ne_one x
    rw [hw]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ hx)
  let middle : Monoid.CoprodI.Word G := ⟨l, hletters, hchain.left_of_append⟩
  have hp : w.prod = Monoid.CoprodI.of a * (middle.prod * Monoid.CoprodI.of b) := by
    simp [Monoid.CoprodI.Word.prod, hw, middle]
  by_cases hba : b * a = 1
  · refine ⟨middle, ?_, ?_⟩
    · simp only [middle, hw, List.length_cons, List.length_append]
      omega
    · apply isConj_iff.mpr
      refine ⟨Monoid.CoprodI.of a, ?_⟩
      have hb : Monoid.CoprodI.of b = (Monoid.CoprodI.of a : Monoid.CoprodI G)⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        rw [← map_mul, hba, map_one]
      rw [hp, hb, mul_assoc]
  · let v : Monoid.CoprodI.Word G :=
      { toList := l ++ [⟨i, b * a⟩]
        ne_one := by
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hletters x hx
          · have hx' : x = ⟨i, b * a⟩ := List.mem_singleton.mp hx
            subst x
            exact hba
        chain_ne := by
          apply List.IsChain.append hchain.left_of_append (List.isChain_singleton _)
          intro x hx y hy
          have hy' : y = ⟨i, b * a⟩ := by simpa using hy.symm
          subst y
          exact (List.isChain_append.mp hchain).2.2 x hx ⟨i, b⟩ (by simp) }
    refine ⟨v, ?_, ?_⟩
    · simp only [v, hw, List.length_cons, List.length_append]
      omega
    · apply isConj_iff.mpr
      refine ⟨Monoid.CoprodI.of a, ?_⟩
      have hv : v.prod = middle.prod * Monoid.CoprodI.of (b * a) := by
        simp only [Monoid.CoprodI.Word.prod, v, middle, List.map_append, List.map_singleton,
          List.prod_append, List.prod_singleton]
      rw [hv, hp, map_mul]
      simp only [mul_assoc, mul_inv_cancel, mul_one]


-- @@ L165-170 verbatim
private theorem SpecialPeriods.CoprodTorsion.list_cases_endpoints_mo1973_16238 {α : Type*}
    (l : List α) : l = [] ∨ (∃ a, l = [a]) ∨ ∃ a m b, l = a :: (m ++ [b]) := by
  induction l using List.bidirectionalRec with
  | nil => exact Or.inl rfl
  | singleton a => exact Or.inr (Or.inl ⟨a, rfl⟩)
  | cons_append a l b _ => exact Or.inr (Or.inr ⟨a, l, b, rfl⟩)


-- @@ L172-203 verbatim
private theorem SpecialPeriods.CoprodTorsion.coprodI_isOfFinOrder_conjugate_factor {ι : Type*}
    {G : ι → Type*} [∀ i, Group (G i)] (x : Monoid.CoprodI G) (hx : IsOfFinOrder x) :
    x = 1 ∨ ∃ (i : ι) (a : G i), IsConj (Monoid.CoprodI.of a) x := by
  classical
  let P : ℕ → Prop := fun n => ∃ w : Monoid.CoprodI.Word G, w.toList.length = n ∧ IsConj w.prod x
  have hP : ∃ n, P n := by
    refine ⟨(Monoid.CoprodI.Word.equiv x).toList.length, Monoid.CoprodI.Word.equiv x, rfl, ?_⟩
    have hp : (Monoid.CoprodI.Word.equiv x).prod = x :=
      (Monoid.CoprodI.Word.equiv (M := G)).symm_apply_apply x
    rw [hp]
  obtain ⟨w, hwlen, hwconj⟩ := Nat.find_spec hP
  have hmin (v : Monoid.CoprodI.Word G) (hv : IsConj v.prod x) :
    w.toList.length ≤ v.toList.length := by
    rw [hwlen]
    exact Nat.find_min' hP ⟨v, rfl, hv⟩
  have hwfin : IsOfFinOrder w.prod := hwconj.symm.isOfFinOrder hx
  rcases list_cases_endpoints_mo1973_16238 w.toList with hnil | ⟨a, hsingle⟩ | ⟨a, l, b, hw⟩
  · left
    have hp : w.prod = 1 := by simp [Monoid.CoprodI.Word.prod, hnil]
    simpa only [hp, isConj_one_right] using hwconj
  · right
    refine ⟨a.1, a.2, ?_⟩
    have hp : w.prod = Monoid.CoprodI.of a.2 := by simp [Monoid.CoprodI.Word.prod, hsingle]
    simpa only [hp] using hwconj
  · by_cases hab : a.1 = b.1
    · obtain ⟨v, hvlen, hvconj⟩ := exists_shorter_conjugate w a b l hw hab
      exact (Nat.not_lt_of_ge (hmin v (hvconj.trans hwconj)) hvlen).elim
    · exfalso
      apply
        word_not_isOfFinOrder_of_head_getLast w a b (by simp [hw])
          (by rw [hw, ← List.cons_append, List.getLast?_append_of_ne_nil _ (by simp)]; rfl) hab
          hwfin


-- @@ L205-213 verbatim
private theorem
    SpecialPeriods.CoprodTorsion.coprodI_nontrivial_isOfFinOrder_conjugate_factor {ι : Type*}
    {G : ι → Type*} [∀ i, Group (G i)] (x : Monoid.CoprodI G) (hx : IsOfFinOrder x)
    (hne : x ≠ 1) : ∃ (i : ι) (a : G i), a ≠ 1 ∧ IsConj (Monoid.CoprodI.of a) x := by
  obtain hx | ⟨i, a, ha⟩ := coprodI_isOfFinOrder_conjugate_factor x hx
  · exact (hne hx).elim
  · refine ⟨i, a, ?_, ha⟩
    rintro rfl
    exact hne (by simpa using ha.symm)


-- @@ L215-248 verbatim
private theorem SpecialPeriods.CoprodTorsion.coprod_nontrivial_isOfFinOrder_conjugate_factor
    {A B : Type u} [Group A] [Group B] (x : Monoid.Coprod A B) (hx : IsOfFinOrder x)
    (hne : x ≠ 1) :
    (∃ a : A, a ≠ 1 ∧ IsConj (Monoid.Coprod.inl a) x) ∨
      ∃ b : B, b ≠ 1 ∧ IsConj (Monoid.Coprod.inr b) x := by
  let H : Bool → Type _ := fun b => cond b B A
  let : ∀ b, Group (H b) := Bool.rec (inferInstance : Group A) (inferInstance : Group B)
  let toI : Monoid.Coprod A B →* Monoid.CoprodI H :=
    Monoid.Coprod.lift (Monoid.CoprodI.of (M := H) (i := Bool.false))
      (Monoid.CoprodI.of (M := H) (i := Bool.true))
  let fromI : Monoid.CoprodI H →* Monoid.Coprod A B :=
    Monoid.CoprodI.lift fun b =>
      match b with
      | false => Monoid.Coprod.inl
      | true => Monoid.Coprod.inr
  have hleft : fromI.comp toI = MonoidHom.id (Monoid.Coprod A B) := by
    apply Monoid.Coprod.hom_ext
    · ext a
      simp [toI, fromI]
    · ext b
      simp [toI, fromI]
  have hleft_apply (y : Monoid.Coprod A B) : fromI (toI y) = y := DFunLike.congr_fun hleft y
  have hto_ne : toI x ≠ 1 := by
    intro he
    apply hne
    have hh := congrArg fromI he
    simpa only [hleft_apply, map_one] using hh
  obtain ⟨b, a, hane, ha⟩ :=
    coprodI_nontrivial_isOfFinOrder_conjugate_factor (toI x) (toI.isOfFinOrder hx) hto_ne
  have ha' := fromI.map_isConj ha
  rw [hleft_apply] at ha'
  cases b with
  | false => exact Or.inl ⟨a, hane, by simpa [fromI] using ha'⟩
  | true => exact Or.inr ⟨a, hane, by simpa [fromI] using ha'⟩


-- @@ L250-305 verbatim
private theorem SpecialPeriods.CoprodTorsion.coprodI_conjugate_factor {ι : Type*} {G : ι → Type*}
    [∀ i, Group (G i)] {i : ι} (a b : G i) (ha : a ≠ 1) (g : Monoid.CoprodI G)
    (h : g⁻¹ * Monoid.CoprodI.of a * g = Monoid.CoprodI.of b) :
    ∃ c : G i, g = Monoid.CoprodI.of c := by
  classical
  have hb : b ≠ 1 := by
    intro hb
    have he : (Monoid.CoprodI.of a : Monoid.CoprodI G) = 1 := by
      have hh := congrArg (fun x : Monoid.CoprodI G => g * x * g⁻¹) h
      simpa only [hb, map_one, mul_one, one_mul, mul_assoc, mul_inv_cancel, inv_mul_cancel,
        mul_inv_cancel_left] using hh
    apply ha
    apply Monoid.CoprodI.of_injective i
    simpa only [map_one] using he
  let p : Monoid.CoprodI.Word.Pair G i :=
    Monoid.CoprodI.Word.equivPair i (Monoid.CoprodI.Word.equiv g)
  have he : Monoid.CoprodI.Word.rcons p = Monoid.CoprodI.Word.equiv g :=
    (Monoid.CoprodI.Word.equivPair i).symm_apply_apply (Monoid.CoprodI.Word.equiv g)
  have hg : g = Monoid.CoprodI.of p.head * p.tail.prod := by
    calc
      g = (Monoid.CoprodI.Word.equiv g).prod :=
        ((Monoid.CoprodI.Word.equiv (M := G)).symm_apply_apply g).symm
      _ = (Monoid.CoprodI.Word.rcons p).prod := (congrArg Monoid.CoprodI.Word.prod he.symm)
      _ = Monoid.CoprodI.of p.head * p.tail.prod := Monoid.CoprodI.Word.prod_rcons p
  by_cases ht : p.tail = Monoid.CoprodI.Word.empty
  · exact ⟨p.head, by simpa only [ht, Monoid.CoprodI.Word.prod_empty, mul_one] using hg⟩
  · obtain ⟨j, k, w, hw⟩ := Monoid.CoprodI.NeWord.of_word p.tail ht
    have hji : j ≠ i := by
      have hh := p.fstIdx_ne
      rw [← hw] at hh
      simpa only [Monoid.CoprodI.Word.fstIdx, Monoid.CoprodI.NeWord.toWord,
        Monoid.CoprodI.NeWord.toList_head?, Option.map_some, ne_eq, Option.some.injEq] using hh
    let d : G i := p.head⁻¹ * a * p.head
    have hd : d ≠ 1 := by
      intro hd
      apply ha
      have hh := congrArg (fun x : G i => p.head * x * p.head⁻¹) hd
      simpa only [d, mul_assoc, mul_inv_cancel, inv_mul_cancel, mul_one, one_mul,
        mul_inv_cancel_left] using hh
    let v : Monoid.CoprodI.NeWord G k k :=
      Monoid.CoprodI.NeWord.append
        (Monoid.CoprodI.NeWord.append w.inv hji (Monoid.CoprodI.NeWord.singleton d hd)) hji.symm w
    have hgp : g = Monoid.CoprodI.of p.head * w.prod := by
      simpa only [Monoid.CoprodI.NeWord.prod, hw] using hg
    have hv : v.prod = Monoid.CoprodI.of b := by
      rw [hgp] at h
      simpa only [v, Monoid.CoprodI.NeWord.append_prod, Monoid.CoprodI.NeWord.inv_prod,
        Monoid.CoprodI.NeWord.prod_singleton, d, map_mul, map_inv, mul_inv_rev, mul_assoc] using h
    have hvw : v.toWord = (Monoid.CoprodI.NeWord.singleton b hb).toWord := by
      apply word_prod_injective
      exact hv.trans (Monoid.CoprodI.NeWord.prod_singleton b hb).symm
    have hlen := congrArg (fun t : Monoid.CoprodI.Word G => t.toList.length) hvw
    simp only [v, Monoid.CoprodI.NeWord.toWord, Monoid.CoprodI.NeWord.toList, List.length_append,
      List.length_singleton] at hlen
    have hpos : 0 < w.toList.length := List.length_pos_iff.mpr w.toList_ne_nil
    omega


-- @@ L307-312 verbatim
private theorem SpecialPeriods.CoprodTorsion.coprodI_commute_of {ι : Type*} {G : ι → Type*}
    [∀ i, Group (G i)] {i : ι} (a : G i) (ha : a ≠ 1) (g : Monoid.CoprodI G)
    (h : Commute (Monoid.CoprodI.of a) g) : ∃ b : G i, g = Monoid.CoprodI.of b := by
  apply coprodI_conjugate_factor a a ha g
  have hh := congrArg (fun x : Monoid.CoprodI G => g⁻¹ * x) h.eq
  simpa only [mul_assoc, inv_mul_cancel_left] using hh


-- @@ L314-341 verbatim
private theorem
    SpecialPeriods.CoprodTorsion.coprod_commute_inl {A B : Type u} [Group A] [Group B] (a : A)
    (ha : a ≠ 1) (g : Monoid.Coprod A B) (h : Commute (Monoid.Coprod.inl a) g) :
    ∃ b : A, g = Monoid.Coprod.inl b := by
  let H : Bool → Type u := fun b => cond b B A
  let : ∀ b, Group (H b) := Bool.rec (inferInstance : Group A) (inferInstance : Group B)
  let toI : Monoid.Coprod A B →* Monoid.CoprodI H :=
    Monoid.Coprod.lift (Monoid.CoprodI.of (M := H) (i := Bool.false))
      (Monoid.CoprodI.of (M := H) (i := Bool.true))
  let fromI : Monoid.CoprodI H →* Monoid.Coprod A B :=
    Monoid.CoprodI.lift fun b =>
      match b with
      | false => Monoid.Coprod.inl
      | true => Monoid.Coprod.inr
  have hleft : fromI.comp toI = MonoidHom.id (Monoid.Coprod A B) := by
    apply Monoid.Coprod.hom_ext
    · ext b
      simp [toI, fromI]
    · ext b
      simp [toI, fromI]
  have hleft_apply (x : Monoid.Coprod A B) : fromI (toI x) = x := DFunLike.congr_fun hleft x
  have hc : Commute (Monoid.CoprodI.of (i := Bool.false) a) (toI g) := by
    have hh := congrArg toI h.eq
    simpa only [commute_iff_eq, map_mul, toI, Monoid.Coprod.lift_apply_inl] using hh
  obtain ⟨b, hb⟩ := coprodI_commute_of (G := H) (i := Bool.false) a ha (toI g) hc
  refine ⟨b, ?_⟩
  have hh := congrArg fromI hb
  simpa only [hleft_apply, fromI, Monoid.CoprodI.lift_of] using hh


-- @@ L343-353 verbatim
public
theorem SpecialPeriods.CoprodTorsion.coprod_commute_inr {A B : Type u} [Group A] [Group B] (a : B)
    (ha : a ≠ 1) (g : Monoid.Coprod A B) (h : Commute (Monoid.Coprod.inr a) g) :
    ∃ b : B, g = Monoid.Coprod.inr b := by
  have hc : Commute (Monoid.Coprod.inl a) (Monoid.Coprod.swap A B g) := by
    have hh := congrArg (Monoid.Coprod.swap A B) h.eq
    simpa only [commute_iff_eq, map_mul, Monoid.Coprod.swap_inr] using hh
  obtain ⟨b, hb⟩ := coprod_commute_inl a ha (Monoid.Coprod.swap A B g) hc
  refine ⟨b, ?_⟩
  have hh := congrArg (Monoid.Coprod.swap B A) hb
  simpa only [Monoid.Coprod.swap_swap, Monoid.Coprod.swap_inl] using hh


-- @@ L355-355 verbatim
end Mathoverflow1973


-- @@ L357-357 verbatim
end
