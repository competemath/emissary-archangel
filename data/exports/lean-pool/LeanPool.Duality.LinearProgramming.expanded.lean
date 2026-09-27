/-
Copyright (c) 2026 Martin Dvorak. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Dvorak
-/
module

public import LeanPool.Duality.FarkasSpecial
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Sum
import Mathlib.Data.Rat.Cast.Order
import Mathlib.LinearAlgebra.Matrix.RowCol
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific


-- @@ L19-21 verbatim
/-!
# LeanPool.Duality.LinearProgramming
-/


-- @@ L23-23 verbatim
@[expose] public section


-- @@ L25-36 expanded
/-- Linear program over `F∞` in the standard form (i.e.,
    a system of linear inequalities with nonnegative variables).
    Variables are of type `J`. Conditions are indexed by type `I`.
    The objective function is intended to be minimized. -/
@[ext]
structure ExtendedLP (I J F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F] where
  /-- The left-hand-side matrix. -/
  A : Matrix I J (Extend F)
  /-- The right-hand-side vector. -/
  b : I → Extend F
  /-- The objective function coefficients. -/
  c : J → Extend F


-- @@ L38-52 verbatim
/-- Extended linear program with properties that are needed for duality theorems. -/
structure ValidELP (I J F : Type*) [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    extends ExtendedLP I J F where
  /-- No `⊥` and `⊤` in the same row. -/
  hAi : ¬∃ i : I, (∃ j : J, A i j = ⊥) ∧ (∃ j : J, A i j = ⊤)
  /-- No `⊥` and `⊤` in the same column. -/
  hAj : ¬∃ j : J, (∃ i : I, A i j = ⊥) ∧ (∃ i : I, A i j = ⊤)
  /-- No `⊥` in the row where the right-hand-side vector has `⊥`. -/
  hbA : ¬∃ i : I, (∃ j : J, A i j = ⊥) ∧ b i = ⊥
  /-- No `⊤` in the column where the objective function has `⊥`. -/
  hcA : ¬∃ j : J, (∃ i : I, A i j = ⊤) ∧ c j = ⊥
  /-- No `⊤` in the row where the right-hand-side vector has `⊤`. -/
  hAb : ¬∃ i : I, (∃ j : J, A i j = ⊤) ∧ b i = ⊤
  /-- No `⊥` in the column where the objective function has `⊤`. -/
  hAc : ¬∃ j : J, (∃ i : I, A i j = ⊥) ∧ c j = ⊤


-- @@ L54-54 verbatim
open scoped Matrix


-- @@ L56-56 verbatim
variable {I J F : Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]


-- @@ L58-58 verbatim
section extended_LP_definitions


-- @@ L60-64 expanded
/-- A nonnegative vector `x` is a solution to a linear program `P` iff
    its multiplication by matrix `A` from the left yields a vector whose
    all entries are less or equal to corresponding entries of the vector `b`. -/
def ExtendedLP.IsSolution [Fintype J] (P : ExtendedLP I J F) (x : J → NNeg F) : Prop :=
  Matrix.mulWeig P.A x ≤ P.b


-- @@ L66-70 expanded
/-- Linear program `P` reaches objective value `r` iff there is a solution `x` such that,
    when its entries are elementwise multiplied by the the coefficients `c` and summed up,
    the result is the value `r`. -/
def ExtendedLP.Reaches [Fintype J] (P : ExtendedLP I J F) (r : Extend F) : Prop :=
  ∃ x : J → NNeg F, P.IsSolution x ∧ dotWeig P.c x = r


-- @@ L72-74 expanded
/-- Linear program `P` is feasible iff `P` reaches a value that is not `⊤`. -/
def ExtendedLP.IsFeasible [Fintype J] (P : ExtendedLP I J F) : Prop :=
  ∃ p : Extend F, P.Reaches p ∧ p ≠ ⊤


-- @@ L76-79 expanded
/-- Linear program `P` is bounded by `r` iff every value reached by `P` is
    greater or equal to `r` (i.e., `P` is bounded by `r` from below). -/
def ExtendedLP.IsBoundedBy [Fintype J] (P : ExtendedLP I J F) (r : F) : Prop :=
  ∀ p : Extend F, P.Reaches p → r ≤ p


-- @@ L81-83 verbatim
/-- Linear program `P` is unbounded iff values reached by `P` have no finite lower bound. -/
def ExtendedLP.IsUnbounded [Fintype J] (P : ExtendedLP I J F) : Prop :=
  ¬∃ r : F, P.IsBoundedBy r


-- @@ L85-97 expanded
open scoped Classical in
/-- Extended notion of "optimum" of "minimization LP" (the less the better). -/
noncomputable def ExtendedLP.optimum [Fintype J] (P : ExtendedLP I J F) : Option (Extend F) :=
  if ¬P.IsFeasible then
    some
      ⊤ -- infeasible means that the minimum is `⊤`
        
  else
    if P.IsUnbounded then
      some
        ⊥ -- unbounded means that the minimum is `⊥`
          
    else
      if hr : ∃ r : F, P.Reaches (toE r) ∧ P.IsBoundedBy r then
        some
          (toE hr.choose) -- the minimum is finite
            
      else none


-- @@ L99-102 expanded
/-- `OppositesOpt p q` essentially says `none ≠ p = -q`. -/
def OppositesOpt : Option (Extend F) → Option (Extend F) → Prop
  | (p : Extend F), (q : Extend F) => p = -q
  | _, _ => False


-- @@ L104-110 verbatim
/-- Dualize an extended linear program in the standard form.
    The matrix gets transposed and its values flip signs.
    The original objective function becomes the new right-hand-side vector.
    The original right-hand-side vector becomes the new objective function.
    Both linear programs are intended to be minimized. -/
abbrev ExtendedLP.dualize (P : ExtendedLP I J F) : ExtendedLP J I F :=
  ⟨-P.Aᵀ, P.c, P.b⟩


-- @@ L112-120 expanded
/-- Dualize a valid extended linear program. -/
def ValidELP.dualize (P : ValidELP I J F) : ValidELP J I F
    where
  toExtendedLP := P.toExtendedLP.dualize
  hAi := by intro <;> apply P.hAj <;> aesop
  hAj := by intro <;> apply P.hAi <;> aesop
  hbA := by intro <;> apply P.hcA <;> aesop
  hcA := by intro <;> apply P.hbA <;> aesop
  hAb := by intro <;> apply P.hAc <;> aesop
  hAc := by intro <;> apply P.hAb <;> aesop


-- @@ L122-122 verbatim
end extended_LP_definitions



-- @@ L125-125 verbatim
section weak_duality


-- @@ L127-134 expanded
lemma EF.one_smul (r : Extend F) : (1 : NNeg F) • r = r := by
  match r with
  | ⊥ => rfl
  | ⊤ =>
    change EF.smulNN 1 ⊤ = ⊤
    change (if (1 : NNeg F) = 0 then (0 : Extend F) else ⊤) = ⊤
    exact ite_eq_right (by norm_num)
  | (q : F) => exact congr_arg toE (one_mul q)


-- @@ L136-146 expanded
lemma EF.sub_nonpos_iff (r s : Extend F) : r + (-s) ≤ 0 ↔ r ≤ s := by
  match r with
  | ⊥ => convert_to True ↔ True <;> simp
  | ⊤ =>
    match s with
    | ⊥ => convert_to False ↔ False <;> simp
    | ⊤ => convert_to True ↔ True <;> simp
    | (_ : F) => convert_to False ↔ False <;> simp [← EF.coe_neg]
  | (_ : F) =>
    match s with
    | ⊥ => convert_to False ↔ False <;> simp
    | ⊤ => convert_to True ↔ True <;> simp
    | (_ : F) => simp [← EF.coe_neg, ← EF.coe_add]


-- @@ L148-149 expanded
lemma EF.vec_sub_nonpos_iff (u v : I → Extend F) : u + (-v) ≤ 0 ↔ u ≤ v := by
  constructor <;> intro huv i <;> simpa [EF.sub_nonpos_iff] using huv i


-- @@ L151-155 expanded
omit [IsStrictOrderedRing F] in
lemma sumElim_dotWeig_sumElim [Fintype I] [Fintype J] (u : I → Extend F) (v : J → Extend F)
    (x : I → NNeg F) (y : J → NNeg F) :
    dotWeig (Sum.elim u v) (Sum.elim x y) = dotWeig u x + dotWeig v y := by simp [dotWeig]


-- @@ L157-161 expanded
omit [IsStrictOrderedRing F] in
lemma Matrix.fromRows_mulWeig [Fintype J] {I₁ I₂ : Type*} (M₁ : Matrix I₁ J (Extend F))
    (M₂ : Matrix I₂ J (Extend F)) (w : J → NNeg F) :
    Matrix.mulWeig (Matrix.fromRows M₁ M₂) w =
      Sum.elim (Matrix.mulWeig M₁ w) (Matrix.mulWeig M₂ w) :=
  by ext (_ | _) <;> rfl


-- @@ L163-168 expanded
omit [IsStrictOrderedRing F] in
lemma Matrix.fromCols_mulWeig_sumElim {J₁ J₂ : Type*} [Fintype J₁] [Fintype J₂]
    (M₁ : Matrix I J₁ (Extend F)) (M₂ : Matrix I J₂ (Extend F)) (w₁ : J₁ → NNeg F)
    (w₂ : J₂ → NNeg F) :
    Matrix.mulWeig (Matrix.fromCols M₁ M₂) (Sum.elim w₁ w₂) =
      Matrix.mulWeig M₁ w₁ + Matrix.mulWeig M₂ w₂ :=
  by
  ext
  simp [Matrix.fromCols, Matrix.mulWeig, dotWeig]


-- @@ L170-177 expanded
lemma dotWeig_eq_bot [Fintype J] {v : J → Extend F} {w : J → NNeg F} :
    (∃ j : J, v j = ⊥) ↔ dotWeig v w = ⊥ := by
  constructor
  · intro ⟨j, hvj⟩
    apply has_bot_dotWeig_nneg hvj
  · intro hvw
    by_contra! contr
    exact no_bot_dotWeig_nneg contr w hvw


-- @@ L179-254 expanded
lemma ValidELP.weakDuality_of_no_bot [Fintype I] [Fintype J] (P : ValidELP I J F)
    (hb : ¬∃ i : I, P.b i = ⊥) (hc : ¬∃ j : J, P.c j = ⊥) {p : Extend F} (hP : P.Reaches p)
    {q : Extend F} (hQ : P.dualize.Reaches q) : 0 ≤ p + q := by
  classical
  obtain ⟨x, hx, rfl⟩ := hP
  obtain ⟨y, hy, rfl⟩ := hQ
  by_contra contr
  apply
    not_and_of_neq
      (extendedFarkas (Matrix.fromRows P.A (Matrix.replicateRow Unit P.c))
        (Sum.elim P.b (fun _ => (dotWeig P.c x)))
        (by
          intro ⟨i, ⟨s, his⟩, ⟨t, hit⟩⟩
          cases i with
          | inl i' => exact P.hAi ⟨i', ⟨s, his⟩, ⟨t, hit⟩⟩
          | inr => exact hc ⟨s, his⟩)
        (by
          intro ⟨j, ⟨s, hjs⟩, ⟨t, hjt⟩⟩
          cases s with
          | inl iₛ =>
            cases t with
            | inl iₜ => exact P.hAj ⟨j, ⟨iₛ, hjs⟩, ⟨iₜ, hjt⟩⟩
            | inr => exact P.hAc ⟨j, ⟨iₛ, hjs⟩, hjt⟩
          | inr => simp_all)
        (by
          intro ⟨i, ⟨j, hij⟩, hi⟩
          cases i with
          | inl i' => exact P.hAb ⟨i', ⟨j, hij⟩, hi⟩
          | inr =>
            rw [Sum.elim_inr] at hi
            push Not at contr
            rw [hi] at contr
            match hby : dotWeig P.b y with
            | ⊥ =>
              change dotWeig P.b y = ⊥ at hby
              rw [← dotWeig_eq_bot] at hby
              exact hb hby
            | ⊤ =>
              dsimp only [ValidELP.dualize] at contr
              rw [hby] at contr
              change ⊤ + ⊤ < 0 at contr
              simp at contr
            | (q : F) =>
              dsimp only [ValidELP.dualize] at contr
              rw [hby] at contr
              change ⊤ + toE q < 0 at contr
              simp at contr)
        (by simp_all))
  constructor
  · use x
    rw [Matrix.fromRows_mulWeig, Sum.elim_le_elim_iff]
    exact ⟨hx, by rfl⟩
  · use Sum.elim y 1
    constructor
    · rw [Matrix.transpose_fromRows, Matrix.fromCols_neg, Matrix.fromCols_mulWeig_sumElim]
      have hle0 : Matrix.mulWeig (-P.Aᵀ) y + (-P.c) ≤ 0 := by rwa [EF.vec_sub_nonpos_iff]
      convert hle0
      ext
      simp [Matrix.mulWeig, dotWeig, EF.one_smul]
    · have hlt0 : dotWeig P.b y + dotWeig P.c x < 0 :=
        by
        push Not at contr
        rwa [add_comm]
      rw [sumElim_dotWeig_sumElim]
      have h1 :
        dotWeig ((fun _ => (dotWeig P.c x)) : Unit → Extend F) (1 : Unit → NNeg F) =
          dotWeig P.c x :=
        by simp only [dotWeig, Fintype.sum_unique, EF.one_smul, Pi.one_apply]
      rwa [h1]


-- @@ L256-262 expanded
lemma ValidELP.no_bot_of_reaches [Fintype J] (P : ValidELP I J F) {p : Extend F} (hP : P.Reaches p)
    (i : I) : P.b i ≠ ⊥ := by
  intro contr
  obtain ⟨x, hx, -⟩ := hP
  have impos : dotWeig (P.A i) x ≤ ⊥ := contr ▸ hx i
  rw [le_bot_iff, ← dotWeig_eq_bot] at impos
  exact P.hbA ⟨i, impos, contr⟩


-- @@ L264-276 expanded
theorem ValidELP.weakDuality [Fintype I] [Fintype J] (P : ValidELP I J F) {p : Extend F}
    (hP : P.Reaches p) {q : Extend F} (hQ : P.dualize.Reaches q) : 0 ≤ p + q :=
  by
  by_cases hb : ∃ i : I, P.b i = ⊥
  · exfalso
    obtain ⟨i, hi⟩ := hb
    exact P.no_bot_of_reaches hP i hi
  by_cases hc : ∃ j : J, P.c j = ⊥
  · exfalso
    obtain ⟨j, hj⟩ := hc
    exact P.dualize.no_bot_of_reaches hQ j hj
  exact P.weakDuality_of_no_bot hb hc hP hQ


-- @@ L278-278 verbatim
end weak_duality



-- @@ L281-281 verbatim
section strong_duality


-- @@ L283-283 verbatim
section nneg_vs_zero


-- @@ L285-288 expanded
omit [IsStrictOrderedRing F] in
lemma eq_zero_of_zero_eq_val {k : NNeg F} (hk : 0 = k.val) : k = 0 :=
  Subtype.ext hk.symm


-- @@ L290-294 expanded
omit [IsStrictOrderedRing F] in
lemma pos_of_NN_not_zero {k : NNeg F} (hk : ¬(k = 0)) : 0 < k :=
  by
  apply lt_of_le_of_ne k.property
  exact hk ∘ eq_zero_of_zero_eq_val


-- @@ L296-296 verbatim
end nneg_vs_zero


-- @@ L298-298 verbatim
section misc_EF_properties


-- @@ L300-308 expanded
lemma EF.smul_nonpos {r : Extend F} (hr : r ≤ 0) (k : NNeg F) : k • r ≤ 0 := by
  match r with
  | ⊥ => apply bot_le
  | ⊤ => exact absurd hr (not_le.mpr EF.zero_lt_top)
  | (f : F) =>
    change (toE (k.val * f) : Extend F) ≤ (0 : Extend F)
    exact
      (Iff.mpr (EF.coe_le_coe_iff (x := k.val * f) (y := 0)))
        (mul_nonpos_of_nonneg_of_nonpos k.property ((Iff.mp EF.coe_nonpos) hr))


-- @@ L310-354 expanded
lemma EF.smul_lt_smul_left {k : NNeg F} (hk : 0 < k) (r s : Extend F) : k • r < k • s ↔ r < s := by
  match s with
  | ⊥ =>
    convert_to False ↔ False
    · rw [iff_false]
      apply not_lt_bot
    · simp
    rfl
  | ⊤ =>
    match r with
    | ⊥ =>
      convert_to True ↔ True
      · rw [EF.pos_smul_top hk, iff_true]
        apply bot_lt_top
      · simp
      rfl
    | ⊤ => simp_all
    | (_ : F) =>
      convert_to True ↔ True
      · rw [EF.pos_smul_top hk, iff_true]
        apply EF.coe_lt_top
      · simp
      rfl
  | (q : F) =>
    match r with
    | ⊥ =>
      convert_to True ↔ True
      · rw [iff_true]
        apply EF.bot_lt_coe
      · simp
      rfl
    | ⊤ =>
      convert_to False ↔ False
      · rw [EF.pos_smul_top hk, iff_false]
        apply not_top_lt
      · simp
      rfl
    | (p : F) =>
      rw [EF.coe_lt_coe_iff]
      change (toE (k.val * p) < toE (k.val * q) : Prop) ↔ p < q
      rw [EF.coe_lt_coe_iff]
      have hk' : (0 : F) < k.val := hk
      exact mul_lt_mul_iff_right₀ hk'


-- @@ L356-358 expanded
lemma EF.smul_le_smul_left {k : NNeg F} (hk : 0 < k) (r s : Extend F) : k • r ≤ k • s ↔ r ≤ s := by
  convert neg_iff_neg (EF.smul_lt_smul_left hk s r) <;> exact Iff.symm not_lt


-- @@ L360-380 expanded
lemma EF.smul_neg {k : NNeg F} {r : Extend F} (hkr : k = 0 → r ≠ ⊥ ∧ r ≠ ⊤) : k • (-r) = -(k • r) :=
  by
  match r with
  | ⊥ =>
    rw [EF.neg_bot]
    if hk : 0 < k then 
      rewrite [EF.pos_smul_top hk]
      rfl
    else simp_all
  | ⊤ =>
    rw [EF.neg_top]
    if hk : 0 < k then 
      rewrite [EF.pos_smul_top hk, EF.neg_top]
      rfl
    else simp_all
  | (f : F) =>
    rw [← EF.coe_neg]
    change toE (k * (-f)) = toE (-(k * f))
    rw [mul_neg]


-- @@ L382-386 expanded
lemma EF.pos_smul_neg {k : NNeg F} (hk : 0 < k) (r : Extend F) : k • (-r) = -(k • r) :=
  by
  apply EF.smul_neg
  intro h0
  simp_all


-- @@ L388-402 expanded
lemma EF.smul_smul {k : NNeg F} (hk : 0 < k) (l : NNeg F) (r : Extend F) :
    l • (k • r) = k • (l • r) := by
  match r with
  | ⊥ => rw [EF.smul_bot, EF.smul_bot, EF.smul_bot]
  | ⊤ =>
    rw [EF.pos_smul_top hk]
    if hl : 0 < l then rw [EF.pos_smul_top hl, EF.pos_smul_top hk]
    else if hl0 : l = 0 then rw [hl0, EF.zero_smul_nonbot top_ne_bot, smul_zero] else simp_all
  | (f : F) => exact (Iff.mpr EF.coe_eq_coe_iff) (mul_left_comm l.val k.val f)


-- @@ L404-424 expanded
lemma EF.add_smul (k l : NNeg F) (r : Extend F) : (k + l) • r = k • r + l • r := by
  match r with
  | ⊥ =>
    rewrite [EF.smul_bot, EF.smul_bot, EF.smul_bot]
    rfl
  | ⊤ =>
    if k_eq_0 : k = 0 then rw [k_eq_0, EF.zero_smul_nonbot top_ne_bot, zero_add, zero_add]
    else
      have k_pos : 0 < k := pos_of_NN_not_zero k_eq_0
      rw [EF.pos_smul_top (add_pos_of_pos_of_nonneg k_pos l.property)]
      rw [EF.pos_smul_top k_pos]
      if l_eq_0 : l = 0 then rw [l_eq_0, EF.zero_smul_nonbot top_ne_bot, add_zero]
      else
        rw [EF.pos_smul_top (pos_of_NN_not_zero l_eq_0)]
        rfl
  | (f : F) =>
    change toE ((k.val + l.val) * f) = toE (k.val * f) + toE (l.val * f)
    rw [← EF.coe_add, add_mul]


-- @@ L426-447 expanded
omit [IsStrictOrderedRing F] in
lemma EF.smul_add {k : NNeg F} (hk : 0 < k) (r s : Extend F) : k • (r + s) = k • r + k • s := by
  match r, s with
  | ⊥, _ => rw [EF.bot_add, EF.smul_bot, EF.bot_add]
  | _, ⊥ => rw [EF.add_bot, EF.smul_bot, EF.add_bot]
  | (p : F), (q : F) =>
    change toE (k * (p + q)) = toE (k * p) + toE (k * q)
    rewrite [mul_add]
    rfl
  | (p : F), ⊤ =>
    rw [EF.coe_add_top, EF.pos_smul_top hk]
    change ⊤ = toE (k * p) + ⊤
    rw [EF.coe_add_top]
  | ⊤, (q : F) =>
    rw [EF.top_add_coe, EF.pos_smul_top hk]
    change ⊤ = ⊤ + toE (k * q)
    rw [EF.top_add_coe]
  | ⊤, ⊤ => rw [EF.top_add_top, EF.pos_smul_top hk, EF.top_add_top]


-- @@ L449-470 expanded
lemma EF.mul_smul (k l : NNeg F) (r : Extend F) : (k * l) • r = k • (l • r) := by
  match r with
  | ⊥ => iterate 3 rw [EF.smul_bot]
  | ⊤ =>
    if l_eq_0 : l = 0 then
      rw [l_eq_0, EF.zero_smul_nonbot top_ne_bot, mul_zero, EF.zero_smul_nonbot top_ne_bot,
        smul_zero]
    else
      have l_pos : 0 < l := by
        apply lt_of_le_of_ne l.property
        exact l_eq_0 ∘ eq_zero_of_zero_eq_val
      rw [EF.pos_smul_top l_pos]
      if k_eq_0 : k = 0 then
        rw [k_eq_0, EF.zero_smul_nonbot top_ne_bot, zero_mul, EF.zero_smul_nonbot top_ne_bot]
      else
        have c_pos : 0 < k := pos_of_NN_not_zero k_eq_0
        rw [EF.pos_smul_top c_pos, EF.pos_smul_top (mul_pos c_pos l_pos)]
  | (f : F) =>
    change toE ((k * l) * f) = toE (k * (l * f))
    rw [mul_assoc]


-- @@ L472-475 expanded
lemma EF.one_smul_vec (v : J → Extend F) : (1 : NNeg F) • v = v :=
  by
  ext
  apply EF.one_smul


-- @@ L477-481 expanded
omit [IsStrictOrderedRing F] in
lemma EF.smul_add_vec {k : NNeg F} (hk : 0 < k) (v w : J → Extend F) :
    k • (v + w) = k • v + k • w := by
  ext
  apply EF.smul_add hk


-- @@ L483-486 expanded
lemma EF.mul_smul_vec (k l : NNeg F) (v : J → Extend F) : (k * l) • v = k • (l • v) :=
  by
  ext
  apply EF.mul_smul


-- @@ L488-490 expanded
lemma EF.vec_smul_le_smul_left {k : NNeg F} (hk : 0 < k) (u v : I → Extend F) :
    k • u ≤ k • v ↔ u ≤ v := by simp [Pi.le_def, EF.smul_le_smul_left, hk]


-- @@ L492-504 expanded
lemma Multiset.sum_neq_EF_top {s : Multiset (Extend F)} (hs : ⊤ ∉ s) : s.sum ≠ ⊤ := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a m ih =>
    rw [Multiset.sum_cons]
    match a with
    | ⊥ => simp
    | ⊤ => simp at hs
    | (_ : F) =>
      match hm : m.sum with
      | ⊥ => simp
      | ⊤ => exact (ih (by simpa using hs) hm).elim
      | (_ : F) => simp [← EF.coe_add]


-- @@ L506-511 expanded
omit [IsStrictOrderedRing F] in
lemma Multiset.smul_EF_sum {k : NNeg F} (hk : 0 < k) (s : Multiset (Extend F)) :
    (s.map (k • ·)).sum = k • s.sum := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a m ih => simp [EF.smul_add hk, ← ih]


-- @@ L513-518 expanded
omit [IsStrictOrderedRing F] in
lemma Finset.smul_EF_sum [Fintype J] {k : NNeg F} (hk : 0 < k) (v : J → Extend F) :
    ∑ j : J, k • v j = k • ∑ j : J, v j :=
  by
  convert Multiset.smul_EF_sum hk (Finset.univ.val.map v) using 2
  · simp
  · rfl


-- @@ L520-520 verbatim
end misc_EF_properties


-- @@ L522-522 verbatim
section dotWeig_EF_properties


-- @@ L524-527 expanded
omit [IsStrictOrderedRing F] in
lemma zero_dotWeig [Fintype J] (w : J → NNeg F) : dotWeig (0 : J → Extend F) w = 0 :=
  by
  apply Finset.sum_eq_zero
  simp_all


-- @@ L529-531 expanded
lemma dotWeig_add [Fintype J] (x : J → Extend F) (v w : J → NNeg F) :
    dotWeig x (v + w) = dotWeig x v + dotWeig x w := by
  simp [dotWeig, EF.add_smul, Finset.sum_add_distrib]


-- @@ L533-539 expanded
lemma dotWeig_smul [Fintype J] {k : NNeg F} (hk : 0 < k) (x : J → Extend F) (v : J → NNeg F) :
    dotWeig x (k • v) = k • (dotWeig x v) :=
  by
  change ∑ j : J, (k * v j) • x j = k • ∑ j : J, v j • x j
  rw [← Finset.smul_EF_sum hk]
  apply congr_arg
  ext
  apply EF.mul_smul


-- @@ L541-549 expanded
lemma no_top_dotWeig_nneg [Fintype J] {v : J → Extend F} (hv : ∀ j, v j ≠ ⊤) (w : J → NNeg F) :
    dotWeig v w ≠ (⊤ : Extend F) :=
  by
  apply Multiset.sum_neq_EF_top
  rw [Multiset.mem_map]
  intro ⟨i, _, hi⟩
  match hvi : v i with
  | ⊥ => exact bot_ne_top (hvi ▸ hi)
  | ⊤ => exact false_of_ne (hvi ▸ hv i)
  | (_ : F) => exact EF.coe_neq_top _ (hvi ▸ hi)


-- @@ L551-551 verbatim
end dotWeig_EF_properties


-- @@ L553-553 verbatim
section matrix_EF_properties


-- @@ L555-558 expanded
omit [IsStrictOrderedRing F] in
lemma Matrix.EF_neg_zero : -(0 : Matrix I J (Extend F)) = 0 :=
  by
  ext
  apply neg_zero


-- @@ L560-562 expanded
omit [IsStrictOrderedRing F] in
lemma Matrix.EF_neg_neg (M : Matrix I J (Extend F)) : -(-M) = M := by simp_all


-- @@ L564-567 expanded
omit [IsStrictOrderedRing F] in
lemma Matrix.zero_mulWeig [Fintype J] (v : J → NNeg F) :
    Matrix.mulWeig (0 : Matrix I J (Extend F)) v = 0 :=
  by
  ext
  simp [Matrix.mulWeig, dotWeig]


-- @@ L569-572 expanded
lemma Matrix.mulWeig_add [Fintype J] (M : Matrix I J (Extend F)) (v w : J → NNeg F) :
    Matrix.mulWeig M (v + w) = Matrix.mulWeig M v + Matrix.mulWeig M w :=
  by
  ext
  apply dotWeig_add


-- @@ L574-577 expanded
lemma Matrix.mulWeig_smul [Fintype J] {k : NNeg F} (hk : 0 < k) (M : Matrix I J (Extend F))
    (v : J → NNeg F) : Matrix.mulWeig M (k • v) = k • (Matrix.mulWeig M v) :=
  by
  ext
  apply dotWeig_smul hk


-- @@ L579-579 verbatim
end matrix_EF_properties


-- @@ L581-581 verbatim
section extended_LP_properties


-- @@ L583-585 verbatim
lemma ValidELP.dualize_dualize (P : ValidELP I J F) : P = P.dualize.dualize := by
  obtain ⟨⟨_, _, _⟩⟩ := P
  simp [ValidELP.dualize]


-- @@ L587-589 verbatim
lemma ValidELP.no_bot_of_feasible [Fintype J] (P : ValidELP I J F) (hP : P.IsFeasible) (i : I) :
    P.b i ≠ ⊥ :=
  P.no_bot_of_reaches hP.choose_spec.left i


-- @@ L591-591 verbatim
variable [Fintype J]


-- @@ L593-595 expanded
lemma ValidELP.isUnbounded_iff (P : ValidELP I J F) :
    P.IsUnbounded ↔ ∀ r : F, ∃ p : Extend F, P.Reaches p ∧ p < r := by
  simp [ExtendedLP.IsUnbounded, ExtendedLP.IsBoundedBy]


-- @@ L597-603 expanded
lemma ValidELP.unbounded_of_reaches_le (P : ValidELP I J F)
    (hP : ∀ r : F, ∃ p : Extend F, P.Reaches p ∧ p ≤ r) : P.IsUnbounded :=
  by
  rw [ValidELP.isUnbounded_iff]
  intro r
  obtain ⟨p, hPp, hpr⟩ := hP (r - 1)
  exact ⟨p, hPp, hpr.trans_lt ((Iff.mpr EF.coe_lt_coe_iff) (sub_one_lt r))⟩


-- @@ L605-668 expanded
lemma ValidELP.unbounded_of_feasible_of_neg (P : ValidELP I J F) (hP : P.IsFeasible)
    {x₀ : J → NNeg F} (hx₀ : dotWeig P.c x₀ < 0)
    (hAx₀ : Matrix.mulWeig P.A x₀ + (0 : NNeg F) • (-P.b) ≤ 0) : P.IsUnbounded :=
  by
  have nobot := P.no_bot_of_feasible hP
  obtain ⟨e, ⟨xₚ, hxₚ, hce⟩, he⟩ := hP
  apply P.unbounded_of_reaches_le
  intro s
  if hs : e ≤ s then 
    refine ⟨e, ⟨xₚ, hxₚ, hce⟩, ?_⟩
    simpa using hs
  else
    push Not at hs
    match e with
    | ⊥ => simp at hs
    | ⊤ => simp at he
    | (e : F) =>
      clear he
      match hcx₀ : dotWeig P.c x₀ with
      | ⊥ =>
        refine ⟨⊥, ⟨xₚ, hxₚ, ?_⟩, bot_le⟩
        change dotWeig P.c x₀ = ⊥ at hcx₀
        rwa [← dotWeig_eq_bot] at hcx₀ ⊢
      | ⊤ =>
        exfalso
        rw [hcx₀] at hx₀
        exact (hx₀.trans_le le_top).false
      | (d : F) =>
        rw [hcx₀] at hx₀
        have coef_pos : 0 < (s - e) / d :=
          by
          apply div_pos_of_neg_of_neg
          · rwa [sub_neg, ← EF.coe_lt_coe_iff]
          · rwa [← EF.coe_neg']
        let k : NNeg F := ⟨((s - e) / d), coef_pos.le⟩
        let k_pos : 0 < k := coef_pos
        refine ⟨s, ⟨xₚ + k • x₀, ?_, ?_⟩, by rfl⟩
        · intro i
          match hi : P.b i with
          | ⊥ =>
            exfalso
            exact nobot i hi
          | ⊤ => apply le_top
          | (bᵢ : F) =>
            specialize hAx₀ i
            rw [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, hi] at hAx₀
            have zeros : (Matrix.mulWeig P.A x₀) i + (0 : Extend F) ≤ 0 :=
              by
              convert hAx₀
              · change 0 = 0 • -(toE bᵢ)
                rw [← EF.coe_neg, EF.zero_smul_coe]
            rw [add_zero] at zeros
            rw [Matrix.mulWeig_add, Matrix.mulWeig_smul k_pos, Pi.add_apply]
            apply add_le_of_le_of_nonpos
            · convert_to (Matrix.mulWeig P.A xₚ) i ≤ P.b i
              · exact hi.symm
              exact hxₚ i
            · exact EF.smul_nonpos zeros k
        · rw [dotWeig_add, hce, dotWeig_smul k_pos, hcx₀]
          change toE (e + ((s - e) / d) * d) = toE s
          rw [EF.coe_eq_coe_iff, div_mul_cancel_of_imp]
          · exact add_sub_cancel e s
          · intro d_eq_0
            exfalso
            rw [d_eq_0] at hx₀
            exact hx₀.false


-- @@ L670-670 verbatim
variable [Fintype I]


-- @@ L672-741 expanded
lemma ValidELP.unbounded_of_feasible_of_infeasible (P : ValidELP I J F) (hP : P.IsFeasible)
    (hQ : ¬P.dualize.IsFeasible) : P.IsUnbounded :=
  by
  let I' : Type _ := { i : I // P.b i ≠ ⊤ }
  let A' : Matrix I' J (Extend F) := Matrix.of (fun i' : I' => P.A i'.val)
  let b' : I' → Extend F := (fun i' : I' => P.b i'.val)
  cases
    or_of_neq
      (extendedFarkas (-A'ᵀ) P.c (by intro <;> apply P.hAj <;> aesop)
        (by intro <;> apply P.hAi <;> aesop) (by intro <;> apply P.hAc <;> aesop)
        (by intro <;> apply P.hcA <;> aesop)) with
  | inl caseI =>
    exfalso
    obtain ⟨y, hy⟩ := caseI
    match hby : dotWeig b' y with
    | ⊥ => exact no_bot_dotWeig_nneg (P.no_bot_of_feasible hP ·.val ·) y hby
    | ⊤ => exact no_top_dotWeig_nneg (·.property) y hby
    | (q : F) =>
      apply hQ
      refine ⟨toE q, ⟨fun i : I => if hi : (P.b i ≠ ⊤) then y ⟨i, hi⟩ else 0, ?_⟩, EF.coe_neq_top q⟩
      constructor
      · unfold ValidELP.dualize ExtendedLP.IsSolution Matrix.mulWeig
        convert hy
        simp only [Matrix.mulWeig, dotWeig, dite_not, dite_smul]
        rw [Finset.sum_dite]
        convert zero_add _ using 1
        apply congr_arg₂
        · apply Finset.sum_eq_zero
          intro i _
          apply EF.zero_smul_nonbot
          intro contr
          exact P.hAb ⟨i.val, by aesop, by aesop⟩
        · erw [← Finset.sum_coe_sort_eq_attach]
          apply Finset.subtype_univ_sum_eq_subtype_univ_sum
          · ext
            simp
          · intros
            rfl
      · simp only [dotWeig, dite_not, dite_smul]
        rw [Finset.sum_dite]
        convert zero_add _
        · apply Finset.sum_eq_zero
          intro i _
          apply EF.zero_smul_nonbot
          exact P.no_bot_of_feasible hP i.val
        · change dotWeig b' y = toE q at hby
          erw [← Finset.sum_coe_sort_eq_attach]
          rw [← hby]
          apply Finset.subtype_univ_sum_eq_subtype_univ_sum
          · ext
            simp
          · intros
            rfl
  | inr caseJ =>
    obtain ⟨x, hAx, hcx⟩ := caseJ
    apply P.unbounded_of_feasible_of_neg hP hcx
    rw [Matrix.transpose_neg, Matrix.transpose_transpose, Matrix.EF_neg_neg] at hAx
    intro i
    match hbi : P.b i with
    | ⊥ =>
      exfalso
      exact P.no_bot_of_feasible hP i hbi
    | ⊤ =>
      change P.b i = ⊤ at hbi
      rw [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, hbi, EF.neg_top, EF.smul_bot, EF.add_bot]
      apply bot_le
    | (f : F) =>
      change P.b i = toE f at hbi
      have hf : -(toE f) ≠ (⊥ : Extend F) := by simp_all
      rw [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, hbi, EF.zero_smul_nonbot hf, add_zero]
      exact hAx ⟨i, hbi ▸ EF.coe_neq_top f⟩


-- @@ L743-762 verbatim
lemma ValidELP.infeasible_of_unbounded (P : ValidELP I J F) (hP : P.IsUnbounded) :
    ¬P.dualize.IsFeasible := by
  intro ⟨q, hPq, hq⟩
  rw [ValidELP.isUnbounded_iff] at hP
  match q with
  | ⊥ =>
    obtain ⟨p, hp, -⟩ := hP 0
    simpa using P.weakDuality hp hPq
  | ⊤ =>
    exact hq rfl
  | (f : F) =>
    obtain ⟨p, hp, hpq⟩ := hP (-f)
    have wd := P.weakDuality hp hPq
    match p with
    | ⊥ => simp at wd
    | ⊤ => simp at hpq
    | (_ : F) =>
      rw [←EF.coe_add, ←EF.coe_zero, EF.coe_le_coe_iff] at wd
      rw [EF.coe_lt_coe_iff] at hpq
      linarith


-- @@ L764-766 verbatim
/-! The strong duality auxiliary proof is split because the original single proof exceeded the
LeanPool 200-line cap. We dispatch on the two cases coming from `extendedFarkas` and finish
each in its own helper. -/


-- @@ L768-819 expanded
private lemma ValidELP.strongDuality_aux_caseX (P : ValidELP I J F) (hP : P.IsFeasible)
    (hQ : P.dualize.IsFeasible) {X : J ⊕ I → NNeg F}
    (hX :
      Matrix.mulWeig
          (Matrix.fromRows (Matrix.fromBlocks P.A 0 0 (-P.Aᵀ))
            (Matrix.replicateRow Unit (Sum.elim P.c P.b)))
          X ≤
        Sum.elim (Sum.elim P.b P.c) 0) :
    ∃ p q : F, P.Reaches p ∧ P.dualize.Reaches q ∧ p + q ≤ 0 :=
  by
  rw [Matrix.fromRows_mulWeig, Sum.elim_le_elim_iff, ← Matrix.fromRows_fromCols_eq_fromBlocks,
    Matrix.fromRows_mulWeig, Sum.elim_le_elim_iff, ← Sum.elim_comp_inl_inr X,
    Matrix.fromCols_mulWeig_sumElim, Matrix.fromCols_mulWeig_sumElim, Matrix.zero_mulWeig, add_zero,
    Matrix.zero_mulWeig, zero_add] at hX
  set x := X ∘ Sum.inl
  set y := X ∘ Sum.inr
  obtain ⟨⟨hx, hy⟩, hxy⟩ := hX
  specialize hxy 0
  change dotWeig (Sum.elim P.c P.b) (Sum.elim x y) ≤ 0 at hxy
  rw [sumElim_dotWeig_sumElim] at hxy
  match hcx : dotWeig P.c x with
  | ⊥ =>
    exfalso
    obtain ⟨j, hj⟩ := (Iff.mpr dotWeig_eq_bot) hcx
    exact P.dualize.no_bot_of_feasible hQ j hj
  | ⊤ =>
    exfalso
    match hby : dotWeig P.b y with
    | ⊥ =>
      obtain ⟨i, hi⟩ := (Iff.mpr dotWeig_eq_bot) hby
      exact P.no_bot_of_feasible hP i hi
    | ⊤ =>
      rw [hcx, hby] at hxy
      exact (hxy.trans_lt EF.zero_lt_top).false
    | (_ : F) =>
      rw [hcx, hby] at hxy
      exact (hxy.trans_lt EF.zero_lt_top).false
  | (p : F) =>
    match hby : dotWeig P.b y with
    | ⊥ =>
      exfalso
      obtain ⟨i, hi⟩ := (Iff.mpr dotWeig_eq_bot) hby
      exact P.no_bot_of_feasible hP i hi
    | ⊤ =>
      exfalso
      rw [hcx, hby] at hxy
      exact (hxy.trans_lt EF.zero_lt_top).false
    | (q : F) =>
      refine ⟨p, q, ⟨x, hx, hcx⟩, ⟨y, hy, hby⟩, ?_⟩
      rw [← EF.coe_le_coe_iff]
      rwa [hcx, hby] at hxy


-- @@ L821-921 expanded
private lemma ValidELP.strongDuality_aux_caseY (P : ValidELP I J F) (hP : P.IsFeasible)
    (hQ : P.dualize.IsFeasible) {Y : (I ⊕ J) ⊕ Unit → NNeg F}
    (hAY :
      Matrix.mulWeig
          (-(Matrix.fromRows (Matrix.fromBlocks P.A 0 0 (-P.Aᵀ))
                (Matrix.replicateRow Unit (Sum.elim P.c P.b)))ᵀ)
          Y ≤
        0)
    (hbc : dotWeig (Sum.elim (Sum.elim P.b P.c) 0) Y < 0) :
    ∃ p q : F, P.Reaches p ∧ P.dualize.Reaches q ∧ p + q ≤ 0 :=
  by
  rw [Matrix.transpose_fromRows, Matrix.fromBlocks_transpose, Matrix.transpose_zero,
    Matrix.transpose_zero, Matrix.transpose_neg, Matrix.transpose_transpose,
    Matrix.transpose_replicateRow, Matrix.fromCols_neg, ← Sum.elim_comp_inl_inr Y,
    Matrix.fromCols_mulWeig_sumElim, Matrix.fromBlocks_neg, Matrix.EF_neg_neg, Matrix.EF_neg_zero,
    Matrix.EF_neg_zero, ← Matrix.fromRows_fromCols_eq_fromBlocks, Matrix.fromRows_mulWeig, ←
    Sum.elim_comp_inl_inr (Y ∘ Sum.inl), Matrix.fromCols_mulWeig_sumElim,
    Matrix.fromCols_mulWeig_sumElim, Matrix.zero_mulWeig, add_zero, Matrix.zero_mulWeig, zero_add,
    ] at hAY
  rw [← Sum.elim_comp_inl_inr Y, ← Sum.elim_comp_inl_inr (Y ∘ Sum.inl)] at hbc
  set x := (Y ∘ Sum.inl) ∘ Sum.inr
  set y := (Y ∘ Sum.inl) ∘ Sum.inl
  set z := (Y ∘ Sum.inr) 0
  have hAyx :
    Sum.elim (Matrix.mulWeig (-P.Aᵀ) y) (Matrix.mulWeig P.A x) + z • (-Sum.elim P.c P.b) ≤ 0 :=
    by
    convert hAY
    ext
    simp [Matrix.replicateCol, Matrix.mulWeig, dotWeig, z]
  have hAyx' :
    Sum.elim (Matrix.mulWeig (-P.Aᵀ) y) (Matrix.mulWeig P.A x) +
        Sum.elim (z • (-P.c)) (z • (-P.b)) ≤
      0 :=
    by
    convert hAyx
    aesop
  clear hAY hAyx
  rw [← Sum.elim_add_add, Sum.elim_nonpos_iff] at hAyx'
  obtain ⟨hy, hx⟩ := hAyx'
  rw [sumElim_dotWeig_sumElim, zero_dotWeig, add_zero, sumElim_dotWeig_sumElim] at hbc
  have z_pos : 0 < z := by
    by_contra contr
    have z_eq_0 : z = 0 := by simp_all
    rw [z_eq_0] at hx hy
    clear contr z_eq_0 z
    if hxc : dotWeig P.c x < 0 then
      exact P.infeasible_of_unbounded (P.unbounded_of_feasible_of_neg hP hxc hx) hQ
    else
      have hyb : dotWeig P.b y < 0 := by
        push Not at hxc
        by_contra! contr
        exact (hbc.trans_le (add_nonneg contr hxc)).false
      exact
        P.dualize.infeasible_of_unbounded (P.dualize.unbounded_of_feasible_of_neg hQ hyb hy)
          (P.dualize_dualize ▸ hP)
  match hcx : dotWeig P.c x with
  | ⊥ =>
    exfalso
    obtain ⟨j, hj⟩ := (Iff.mpr dotWeig_eq_bot) hcx
    exact P.dualize.no_bot_of_feasible hQ j hj
  | ⊤ =>
    exfalso
    match hby : dotWeig P.b y with
    | ⊥ =>
      obtain ⟨i, hi⟩ := (Iff.mpr dotWeig_eq_bot) hby
      exact P.no_bot_of_feasible hP i hi
    | ⊤ =>
      rw [hcx, hby] at hbc
      exact (hbc.trans EF.zero_lt_top).false
    | (_ : F) =>
      rw [hcx, hby] at hbc
      exact (hbc.trans EF.zero_lt_top).false
  | (p : F) =>
    match hby : dotWeig P.b y with
    | ⊥ =>
      exfalso
      obtain ⟨i, hi⟩ := (Iff.mpr dotWeig_eq_bot) hby
      exact P.no_bot_of_feasible hP i hi
    | ⊤ =>
      exfalso
      rw [hcx, hby] at hbc
      exact (hbc.trans EF.zero_lt_top).false
    | (q : F) =>
      have z_inv_pos : 0 < z⁻¹ := inv_pos_of_pos z_pos
      refine ⟨z⁻¹ * p, z⁻¹ * q, ⟨z⁻¹ • x, ?_, ?_⟩, ⟨z⁻¹ • y, ?_, ?_⟩, ?_⟩
      ·
        rwa [← EF.vec_smul_le_smul_left z_inv_pos, smul_zero, EF.smul_add_vec z_inv_pos, ←
          Matrix.mulWeig_smul z_inv_pos, ← EF.mul_smul_vec, inv_mul_cancel₀ (ne_of_lt z_pos).symm,
          EF.one_smul_vec, EF.vec_sub_nonpos_iff] at hx
      · rewrite [dotWeig_smul z_inv_pos, hcx]
        rfl
      ·
        rwa [← EF.vec_smul_le_smul_left z_inv_pos, smul_zero, EF.smul_add_vec z_inv_pos, ←
          Matrix.mulWeig_smul z_inv_pos, ← EF.mul_smul_vec, inv_mul_cancel₀ (ne_of_lt z_pos).symm,
          EF.one_smul_vec, EF.vec_sub_nonpos_iff] at hy
      · dsimp only [ValidELP.dualize]
        rewrite [dotWeig_smul z_inv_pos, hby]
        rfl
      rw [hcx, hby] at hbc
      rw [← mul_add]
      have hpq : p + q < 0 := by rwa [← EF.coe_lt_coe_iff, add_comm]
      exact mul_nonpos_of_nonneg_of_nonpos z_inv_pos.le hpq.le


-- @@ L923-1029 verbatim
lemma ValidELP.strongDuality_aux (P : ValidELP I J F)
    (hP : P.IsFeasible) (hQ : P.dualize.IsFeasible) :
    ∃ p q : F, P.Reaches p ∧ P.dualize.Reaches q ∧ p + q ≤ 0 := by
  cases
    or_of_neq
      (extendedFarkas
        (Matrix.fromRows
          (Matrix.fromBlocks P.A 0 0 (-P.Aᵀ))
          (Matrix.replicateRow Unit (Sum.elim P.c P.b)))
        (Sum.elim (Sum.elim P.b P.c) 0)
        (by
          intro ⟨k, ⟨s, hks⟩, ⟨t, hkt⟩⟩
          cases k with
          | inl k' =>
            cases k' with
            | inl i =>
              cases s with
              | inl jₛ =>
                cases t with
                | inl jₜ =>
                  exact P.hAi
                    ⟨i, ⟨⟨jₛ, by simpa using hks⟩, ⟨jₜ, by simpa using hkt⟩⟩⟩
                | inr iₜ => simp at hkt
              | inr iₛ => simp at hks
            | inr j =>
              cases t with
              | inl jₜ => simp at hkt
              | inr iₜ =>
                cases s with
                | inl jₛ => simp at hks
                | inr iₛ =>
                  exact P.hAj
                    ⟨j, ⟨iₜ, by simpa using hkt⟩, ⟨iₛ, by simpa using hks⟩⟩
          | inr =>
            cases s with
            | inl jₛ => exact P.dualize.no_bot_of_feasible hQ jₛ hks
            | inr iₛ => exact P.no_bot_of_feasible hP iₛ hks
        )
        (by
          intro ⟨k, ⟨s, hks⟩, ⟨t, hkt⟩⟩
          cases k with
          | inl j =>
            cases s with
            | inl s' =>
              cases s' with
              | inl iₛ =>
                cases t with
                | inl t' =>
                  cases t' with
                  | inl iₜ => exact P.hAj ⟨j, ⟨⟨iₛ, hks⟩, ⟨iₜ, hkt⟩⟩⟩
                  | inr jₜ => simp at hkt
                | inr => exact P.hAc ⟨j, ⟨iₛ, hks⟩, hkt⟩
              | inr jₛ => simp at hks
            | inr => exact P.dualize.no_bot_of_feasible hQ j hks
          | inr i =>
            cases s with
            | inl s' =>
              cases s' with
              | inl iₛ => simp at hks
              | inr jₛ =>
                cases t with
                | inl t' =>
                  cases t' with
                  | inl iₜ => simp at hkt
                  | inr jₜ =>
                    exact P.hAi
                      ⟨i, ⟨jₜ, by simpa using hkt⟩, ⟨jₛ, by simpa using hks⟩⟩
                | inr => exact P.hAb ⟨i, ⟨jₛ, by simpa using hks⟩, hkt⟩
            | inr => exact P.no_bot_of_feasible hP i hks
        )
        (by
          intro ⟨k, ⟨t, hkt⟩, hk⟩
          cases k with
          | inl k' =>
            cases k' with
            | inl i =>
              cases t with
              | inl jₜ => exact P.hAb ⟨i, ⟨jₜ, hkt⟩, hk⟩
              | inr iₜ => simp at hkt
            | inr j =>
              cases t with
              | inl jₜ => simp at hkt
              | inr iₜ => exact P.hAc ⟨j, ⟨iₜ, by simpa using hkt⟩, hk⟩
          | inr => simp at hk
        )
        (by
          intro ⟨k, ⟨s, hks⟩, hk⟩
          cases k with
          | inl k' =>
            cases k' with
            | inl i =>
              cases s with
              | inl jₛ => exact P.no_bot_of_feasible hP i hk
              | inr iₛ => simp at hks
            | inr j =>
              cases s with
              | inl jₛ => simp at hks
              | inr iₛ => exact P.dualize.no_bot_of_feasible hQ j hk
          | inr => simp at hk
        )
      ) with
  | inl case_X =>
    obtain ⟨X, hX⟩ := case_X
    exact P.strongDuality_aux_caseX hP hQ hX
  | inr case_Y =>
    obtain ⟨Y, hAY, hbc⟩ := case_Y
    exact P.strongDuality_aux_caseY hP hQ hAY hbc


-- @@ L1031-1041 verbatim
lemma ValidELP.strongDuality_of_both_feasible (P : ValidELP I J F)
    (hP : P.IsFeasible) (hQ : P.dualize.IsFeasible) :
    ∃ r : F, P.Reaches (toE (-r)) ∧ P.dualize.Reaches (toE r) := by
  obtain ⟨p, q, hp, hq, hpq⟩ := P.strongDuality_aux hP hQ
  have h0pq : 0 ≤ p + q := by
    rw [←EF.coe_le_coe_iff, EF.coe_add, EF.coe_zero]
    exact P.weakDuality hp hq
  have hqp : -q = p := by
    rw [neg_eq_iff_add_eq_zero, add_comm]
    exact le_antisymm hpq h0pq
  exact ⟨q, hqp ▸ hp, hq⟩


-- @@ L1043-1043 verbatim
end extended_LP_properties


-- @@ L1045-1045 verbatim
section extended_LP_optima


-- @@ L1047-1055 verbatim
lemma ExtendedLP.optimum_unique [Fintype J] {P : ExtendedLP I J F} {r s : F}
    (hPr : P.Reaches (toE r) ∧ P.IsBoundedBy r) (hPs : P.Reaches (toE s) ∧ P.IsBoundedBy s) :
    r = s := by
  rw [←EF.coe_eq_coe_iff]
  apply le_antisymm
  · apply hPr.right
    exact hPs.left
  · apply hPs.right
    exact hPr.left


-- @@ L1057-1070 verbatim
lemma ExtendedLP.optimum_eq_of_reaches_bounded [Fintype J] {P : ExtendedLP I J F} {r : F}
    (reaches : P.Reaches (toE r)) (bounded : P.IsBoundedBy r) :
    P.optimum = some r := by
  have hP : P.IsFeasible := by
    obtain ⟨x, hx⟩ := reaches
    exact ⟨toE r, ⟨x, hx⟩, EF.coe_neq_top r⟩
  have hPP : ∃ r : F, P.Reaches (toE r) ∧ P.IsBoundedBy r := by
    use r
  have hPb : ¬P.IsUnbounded := (· ⟨r, bounded⟩)
  have hopt : P.optimum = some (toE hPP.choose) := by
    unfold ExtendedLP.optimum
    rw [ite_eq_right (not_not.mpr hP), ite_eq_right hPb, dite_eq_left hPP]
  rw [hopt]
  exact congr_arg (some <| toE ·) (ExtendedLP.optimum_unique hPP.choose_spec ⟨reaches, bounded⟩)


-- @@ L1072-1093 expanded
omit [IsStrictOrderedRing F] in
lemma oppositesOpt_comm (p q : Option (Extend F)) : OppositesOpt p q ↔ OppositesOpt q p := by
  cases p with
  | none =>
    convert_to False ↔ False
    · simp [OppositesOpt]
    · simp [OppositesOpt]
    rfl
  | some r =>
    cases q with
    | none => trivial
    | some s =>
      if hrs : r = -s then 
        convert_to True ↔ True
        · simpa [OppositesOpt]
        · simpa [OppositesOpt, neg_eq_iff_eq_neg] using hrs.symm
        rfl
      else
        convert_to False ↔ False
        · simpa [OppositesOpt]
        · simpa [OppositesOpt, neg_eq_iff_eq_neg] using Ne.symm hrs
        rfl


-- @@ L1095-1095 verbatim
variable [Fintype I] [Fintype J]


-- @@ L1097-1133 verbatim
lemma ValidELP.strongDuality_of_prim_feasible (P : ValidELP I J F) (hP : P.IsFeasible) :
    OppositesOpt P.optimum P.dualize.optimum := by
  if hQ : P.dualize.IsFeasible then
    obtain ⟨r, hPr, hQr⟩ := P.strongDuality_of_both_feasible hP hQ
    have hPopt : P.optimum = some (toE (-r)) := by
      apply ExtendedLP.optimum_eq_of_reaches_bounded hPr
      intro p hPp
      have Pwd := P.weakDuality hPp hQr
      match p with
      | ⊥ => simp at Pwd
      | ⊤ => apply le_top
      | (_ : F) =>
        rw [←EF.coe_add, ←EF.coe_zero] at Pwd
        rw [EF.coe_le_coe_iff] at Pwd ⊢
        rwa [neg_le_iff_add_nonneg]
    have hQopt : P.dualize.optimum = some (toE r) := by
      apply ExtendedLP.optimum_eq_of_reaches_bounded hQr
      intro q hQq
      have Qwd := P.weakDuality hPr hQq
      match q with
      | ⊥ => simp at Qwd
      | ⊤ => apply le_top
      | (_ : F) =>
        rw [←EF.coe_add, ←EF.coe_zero, add_comm] at Qwd
        rw [EF.coe_le_coe_iff] at Qwd ⊢
        rwa [le_add_neg_iff_le] at Qwd
    rewrite [hPopt, hQopt]
    rfl
  else
    have hPopt : P.optimum = some ⊥ := by
      simp only [ExtendedLP.optimum, hP, P.unbounded_of_feasible_of_infeasible hP hQ]
      rfl
    have hQopt : P.dualize.optimum = some ⊤ := by
      simp only [ExtendedLP.optimum, hQ]
      rfl
    rw [hPopt, hQopt]
    exact EF.neg_top


-- @@ L1135-1142 verbatim
omit [Fintype I] in
theorem ValidELP.optimum_neq_none [Finite I] (P : ValidELP I J F) : P.optimum ≠ none := by
  let : Fintype I := Fintype.ofFinite I
  if hP : P.IsFeasible then
    intro contr
    simpa [contr, OppositesOpt] using P.strongDuality_of_prim_feasible hP
  else
    simp [ExtendedLP.optimum, hP]


-- @@ L1144-1148 verbatim
lemma ValidELP.strongDuality_of_dual_feasible (P : ValidELP I J F) (hP : P.dualize.IsFeasible) :
    OppositesOpt P.optimum P.dualize.optimum := by
  rw [oppositesOpt_comm]
  nth_rw 2 [P.dualize_dualize]
  exact P.dualize.strongDuality_of_prim_feasible hP


-- @@ L1150-1154 verbatim
theorem ValidELP.strongDuality (P : ValidELP I J F) (hP : P.IsFeasible ∨ P.dualize.IsFeasible) :
    OppositesOpt P.optimum P.dualize.optimum :=
  hP.casesOn
    (P.strongDuality_of_prim_feasible ·)
    (P.strongDuality_of_dual_feasible ·)


-- @@ L1156-1156 verbatim
end extended_LP_optima


-- @@ L1158-1158 verbatim
end strong_duality
