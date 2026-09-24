module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Typed
public import Mathlib.Combinatorics.Colex


-- @@ L6-6 verbatim
@[expose] public section

-- @@ L7-7 verbatim
open Encodable FFL FirstOrder Arithmetic PeanoMinus Bootstrapping


-- @@ L9-9 verbatim
namespace FFL.FirstOrder.Semiterm


-- @@ L11-11 expanded
variable {V : Type*} [ORingStructure V] [ModelsSet (Language.str V oRing) (ISigma 1)]


-- @@ L13-13 verbatim
variable {L : Language} [L.Encodable] [L.LORDefinable]


-- @@ L15-15 verbatim
variable (V) {n : ℕ}


-- @@ L17-20 expanded
noncomputable def typedQuote : SyntacticSemiterm L n → Bootstrapping.Semiterm V L n
  | Semiterm.bvar x => Bootstrapping.Semiterm.bvar x
  | Semiterm.fvar x => Bootstrapping.Semiterm.fvar x
  | func f v => Bootstrapping.Semiterm.func f fun i ↦ (v i).typedQuote


-- @@ L22-23 verbatim
noncomputable instance : GödelQuote (SyntacticSemiterm L n) (Bootstrapping.Semiterm V L n) where
  quote := typedQuote V


-- @@ L25-25 verbatim
variable {V}


-- @@ L27-28 expanded
@[simp]
lemma typed_quote_bvar (x : Fin n) :
    (GödelQuote.quote (Semiterm.bvar x : SyntacticSemiterm L n) : Bootstrapping.Semiterm V L n) =
      Bootstrapping.Semiterm.bvar x :=
  rfl


-- @@ L30-31 expanded
@[simp]
lemma typed_quote_fvar (x : ℕ) :
    (GödelQuote.quote (Semiterm.fvar x : SyntacticSemiterm L n) : Bootstrapping.Semiterm V L n) =
      Bootstrapping.Semiterm.fvar ↑x :=
  rfl


-- @@ L33-34 expanded
@[simp]
lemma typed_quote_func (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    (GödelQuote.quote (func f v) : Bootstrapping.Semiterm V L n) =
      Bootstrapping.Semiterm.func f fun i ↦ GödelQuote.quote (v i) :=
  rfl


-- @@ L36-38 expanded
@[simp]
lemma typed_quote_shift (t : SyntacticSemiterm L n) :
    (GödelQuote.quote (Rew.shift t) : Bootstrapping.Semiterm V L n) =
      Bootstrapping.Semiterm.shift (GödelQuote.quote t : Bootstrapping.Semiterm V L n) :=
  by induction t <;> simp [Rew.func, *]; rfl


-- @@ L40-42 expanded
@[simp]
lemma typed_quote_bShift (t : SyntacticSemiterm L n) :
    (GödelQuote.quote (Rew.bShift t) : Bootstrapping.Semiterm V L (n + 1)) =
      Bootstrapping.Semiterm.bShift (GödelQuote.quote t : Bootstrapping.Semiterm V L n) :=
  by induction t <;> simp [Rew.func, *]; rfl


-- @@ L44-46 expanded
@[simp]
lemma typed_quote_substs {n m} (t : SyntacticSemiterm L n) (w : Fin n → SyntacticSemiterm L m) :
    (GödelQuote.quote (Rew.subst w t) : Bootstrapping.Semiterm V L m) =
      Bootstrapping.Semiterm.subst (fun i ↦ GödelQuote.quote (w i)) (GödelQuote.quote t) :=
  by induction t <;> simp [Rew.func, *]; rfl


-- @@ L48-48 verbatim
open Bootstrapping.Arithmetic


-- @@ L50-51 expanded
@[simp]
lemma typed_quote_add (t u : SyntacticSemiterm oRing n) :
    (GödelQuote.quote (Semiterm.Operator.Add.add.operator ![t, u] : SyntacticSemiterm oRing n) :
        Bootstrapping.Semiterm V oRing n) =
      GödelQuote.quote t + GödelQuote.quote u :=
  rfl


-- @@ L53-54 expanded
@[simp]
lemma typed_quote_mul (t u : SyntacticSemiterm oRing n) :
    (GödelQuote.quote (Semiterm.Operator.Mul.mul.operator ![t, u] : SyntacticSemiterm oRing n) :
        Bootstrapping.Semiterm V oRing n) =
      GödelQuote.quote t * GödelQuote.quote u :=
  rfl


-- @@ L56-60 expanded
lemma typed_quote_numeral_eq_numeral_one :
    (GödelQuote.quote ((1 : ℕ) : SyntacticSemiterm oRing n) : Bootstrapping.Semiterm V oRing n) =
      typedNumeral 1 :=
  by
  simp [Bootstrapping.Arithmetic.typedNumeral, Bootstrapping.Arithmetic.one,
    Bootstrapping.Arithmetic.qqFunc_absolute, qqFuncN_eq_qqFunc]
  rfl


-- @@ L62-74 expanded
@[simp]
lemma typed_quote_numeral_eq_numeral (k : ℕ) :
    (GödelQuote.quote (↑k : SyntacticSemiterm oRing n) : Bootstrapping.Semiterm V oRing n) =
      typedNumeral ↑k :=
  by
  match k with
  |
  0 =>
    simp [Bootstrapping.Arithmetic.typedNumeral, Bootstrapping.Arithmetic.zero,
      Bootstrapping.Arithmetic.qqFunc_absolute, qqFuncN_eq_qqFunc]
    rfl
  | 1 => simp [typed_quote_numeral_eq_numeral_one]
  | k + 1 + 1 =>
    calc
      (GödelQuote.quote (↑(k + 1 + 1) : SyntacticSemiterm oRing n) :
          Bootstrapping.Semiterm V oRing n)
      _ =
          GödelQuote.quote (↑(k + 1) : SyntacticSemiterm oRing n) +
            GödelQuote.quote ((1 : ℕ) : SyntacticSemiterm oRing n) :=
        rfl
      _ = typedNumeral ↑(k + 1) + typedNumeral 1 := by
        simp [typed_quote_numeral_eq_numeral (k + 1), typed_quote_numeral_eq_numeral_one]
      _ = typedNumeral (↑k + 1 + 1) := by simp


-- @@ L76-96 expanded
lemma typed_quote_inj {t u : SyntacticSemiterm L n} :
    (GödelQuote.quote t : Bootstrapping.Semiterm V L n) = GödelQuote.quote u → t = u :=
  match t, u with
  | Semiterm.bvar x, Semiterm.bvar y => by simp
  | Semiterm.fvar x, Semiterm.fvar y => by simp
  | func f₁ v₁, func f₂ v₂ =>
    by
    simp only [typed_quote_func, Bootstrapping.Semiterm.func, Semiterm.mk.injEq, qqFunc_inj,
      Nat.cast_inj, func.injEq, and_imp]
    rintro rfl
    simp only [quote_func_inj, heq_eq_eq, true_and]
    rintro rfl
    suffices ((fun i ↦ GödelQuote.quote (v₁ i)) = fun i ↦ GödelQuote.quote (v₂ i)) → v₁ = v₂ by
      simpa [← SemitermVec.val_inj]
    intro h
    ext i
    exact typed_quote_inj (congr_fun h i)
  | Semiterm.bvar _, Semiterm.fvar _ | Semiterm.bvar _, func _ _ | Semiterm.fvar _,
    Semiterm.bvar _ | Semiterm.fvar _, func _ _ | func _ _, Semiterm.bvar _ | func _ _,
    Semiterm.fvar _ => by
    simp [Bootstrapping.Semiterm.bvar, Bootstrapping.Semiterm.fvar, Bootstrapping.Semiterm.func,
      qqBvar, qqFvar, qqFunc]


-- @@ L98-99 expanded
@[simp]
lemma typed_quote_inj_iff {t u : SyntacticSemiterm L n} :
    (GödelQuote.quote t : Bootstrapping.Semiterm V L n) = GödelQuote.quote u ↔ t = u :=
  ⟨typed_quote_inj, by rintro rfl; rfl⟩


-- @@ L101-102 expanded
noncomputable instance : GödelQuote (SyntacticSemiterm L n) V where
  quote t := (GödelQuote.quote t : Bootstrapping.Semiterm V L n).val


-- @@ L104-104 expanded
theorem quote_def (t : SyntacticSemiterm L n) :
    (GödelQuote.quote t : V) = (GödelQuote.quote t : Bootstrapping.Semiterm V L n).val :=
  rfl


-- @@ L106-118 expanded
private lemma quote_eq_encode'_aux (v : Fin k → Semiterm L ℕ n)
    (H : ∀ i, (GödelQuote.quote (v i) : Bootstrapping.Semiterm V L n).val = encode ↑(v i)) :
    (SemitermVec.val fun i ↦ (GödelQuote.quote (v i) : Bootstrapping.Semiterm V L n)) =
      ↑(Matrix.vecToNat fun i ↦ encode (v i)) :=
  by
  induction k
  case zero => simp
  case succ k
    ih =>
    suffices
      (GödelQuote.quote (v 0) : Bootstrapping.Semiterm V L n).val = encode ↑(v 0) ∧
        SemitermVec.val (fun i ↦ GödelQuote.quote (v i.succ)) =
          ↑(Matrix.vecToNat fun i ↦ encode (v i.succ) : V)
      by
      simpa [Matrix.vecToNat, coe_pair_eq_pair_coe, adjoin_def, Matrix.vecHead, Matrix.vecTail,
        Function.comp_def]
    constructor
    · exact H 0
    · exact ih (fun i ↦ v i.succ) (fun i ↦ by simpa using H i.succ)


-- @@ L120-129 expanded
lemma quote_eq_encode (t : SyntacticSemiterm L n) : (GödelQuote.quote t : V) = ↑(encode t) := by
  match t with
  | Semiterm.bvar x => simp [quote_def, encode_eq_toNat, toNat, qqBvar, coe_pair_eq_pair_coe]
  | Semiterm.fvar x => simp [quote_def, encode_eq_toNat, toNat, qqFvar, coe_pair_eq_pair_coe]
  |
  func f
      v =>
    suffices
      (GödelQuote.quote f : V) = ↑(encode f) ∧
        (SemitermVec.val (V := V) fun i ↦ GödelQuote.quote (v i)) =
          ↑(Matrix.vecToNat fun i ↦ encode (v i))
      by
      simpa [quote_def, encode_eq_toNat, toNat, Bootstrapping.Semiterm.func, qqFunc,
        coe_pair_eq_pair_coe]
    constructor
    · rfl
    · exact quote_eq_encode'_aux _ fun i ↦ quote_eq_encode (v i)


-- @@ L131-133 expanded
lemma quote_eq_encode' (v : Fin k → Semiterm L ℕ n) :
    (SemitermVec.val fun i ↦ (GödelQuote.quote (v i) : Bootstrapping.Semiterm V L n)) =
      ↑(Matrix.vecToNat fun i ↦ encode (v i)) :=
  quote_eq_encode'_aux _ fun i ↦ quote_eq_encode (v i)


-- @@ L135-135 expanded
lemma quote_eq_encode_standard (t : SyntacticSemiterm L n) : (GödelQuote.quote t : ℕ) = encode t :=
  by simp [quote_eq_encode]


-- @@ L137-138 expanded
lemma coe_quote_eq_quote (t : SyntacticSemiterm L n) :
    (↑(GödelQuote.quote t : ℕ) : V) = GödelQuote.quote t := by simp [quote_eq_encode]


-- @@ L140-142 expanded
lemma coe_quote_eq_quote' (t : SyntacticSemiterm L n) :
    (↑(GödelQuote.quote t : Bootstrapping.Semiterm ℕ L n).val : V) =
      (GödelQuote.quote t : Bootstrapping.Semiterm V L n).val :=
  coe_quote_eq_quote t


-- @@ L144-144 expanded
@[simp]
lemma quote_bvar (x : Fin n) :
    (GödelQuote.quote (Semiterm.bvar x : SyntacticSemiterm L n) : V) = qqBvar ↑x :=
  rfl


-- @@ L146-146 expanded
@[simp]
lemma quote_fvar (x : ℕ) :
    (GödelQuote.quote (Semiterm.fvar x : SyntacticSemiterm L n) : V) = qqFvar ↑x :=
  rfl


-- @@ L148-149 expanded
@[simp]
lemma quote_func (f : L.Func k) (v : Fin k → SyntacticSemiterm L n) :
    (GödelQuote.quote (func f v) : V) =
      (qqFunc ↑k) (GödelQuote.quote f)
        (SemitermVec.val fun i ↦ (GödelQuote.quote (v i) : Bootstrapping.Semiterm V L n)) :=
  rfl


-- @@ L151-151 verbatim
variable (V)


-- @@ L153-154 expanded
noncomputable instance : GödelQuote (ClosedSemiterm L n) (Bootstrapping.Semiterm V L n) where
  quote t := GödelQuote.quote (Rew.emb t : SyntacticSemiterm L n)


-- @@ L156-156 verbatim
variable {V}


-- @@ L158-159 expanded
theorem empty_typed_quote_def (t : ClosedSemiterm L n) :
    (GödelQuote.quote t : Bootstrapping.Semiterm V L n) =
      GödelQuote.quote (Rew.emb t : SyntacticSemiterm L n) :=
  rfl


-- @@ L161-162 expanded
@[simp]
lemma empty_typed_quote_bvar (x : Fin n) :
    (GödelQuote.quote (Semiterm.bvar x : ClosedSemiterm L n) : Bootstrapping.Semiterm V L n) =
      Bootstrapping.Semiterm.bvar x :=
  rfl


-- @@ L164-165 expanded
@[simp]
lemma empty_typed_quote_func (f : L.Func k) (v : Fin k → ClosedSemiterm L n) :
    (GödelQuote.quote (func f v) : Bootstrapping.Semiterm V L n) =
      Bootstrapping.Semiterm.func f fun i ↦ GödelQuote.quote (v i) :=
  rfl


-- @@ L167-168 expanded
@[simp]
lemma empty_typed_quote_add (t u : ClosedSemiterm oRing n) :
    (GödelQuote.quote (Semiterm.Operator.Add.add.operator ![t, u] : ClosedSemiterm oRing n) :
        Bootstrapping.Semiterm V oRing n) =
      GödelQuote.quote t + GödelQuote.quote u :=
  rfl


-- @@ L170-171 expanded
@[simp]
lemma empty_typed_quote_mul (t u : ClosedSemiterm oRing n) :
    (GödelQuote.quote (Semiterm.Operator.Mul.mul.operator ![t, u] : ClosedSemiterm oRing n) :
        Bootstrapping.Semiterm V oRing n) =
      GödelQuote.quote t * GödelQuote.quote u :=
  rfl


-- @@ L173-175 expanded
@[simp]
lemma empty_typed_quote_numeral_eq_numeral (k : ℕ) :
    (GödelQuote.quote (↑k : ClosedSemiterm oRing n) : Bootstrapping.Semiterm V oRing n) =
      typedNumeral ↑k :=
  by simp [empty_typed_quote_def]


-- @@ L177-178 expanded
noncomputable instance : GödelQuote (ClosedSemiterm L n) V where
  quote t := GödelQuote.quote (Rew.emb t : SyntacticSemiterm L n)


-- @@ L180-180 expanded
lemma empty_quote_def (t : ClosedSemiterm L n) :
    (GödelQuote.quote t : V) = GödelQuote.quote (Rew.emb t : SyntacticSemiterm L n) :=
  rfl


-- @@ L182-182 expanded
theorem empty_quote_eq (t : ClosedSemiterm L n) :
    (GödelQuote.quote t : V) = (GödelQuote.quote t : Bootstrapping.Semiterm V L n).val :=
  rfl


-- @@ L184-184 expanded
lemma empty_quote_eq_encode (t : ClosedSemiterm L n) : (GödelQuote.quote t : V) = ↑(encode t) := by
  simp [empty_quote_def, quote_eq_encode]


-- @@ L186-187 expanded
@[simp]
lemma coe_quote {ξ n} (t : SyntacticSemiterm L n) :
    ↑(GödelQuote.quote t : ℕ) = (GödelQuote.quote t : ArithmeticSemiterm ξ m) := by
  simp [gödelNumber'_def, quote_eq_encode]


-- @@ L189-190 expanded
@[simp]
lemma coe_empty_quote {ξ n} (t : ClosedSemiterm L n) :
    ↑(GödelQuote.quote t : ℕ) = (GödelQuote.quote t : ArithmeticSemiterm ξ m) := by
  simp [gödelNumber'_def, empty_quote_eq_encode]


-- @@ L192-192 verbatim
end FFL.FirstOrder.Semiterm


-- @@ L194-194 verbatim
namespace FFL.FirstOrder.Arithmetic.Bootstrapping


-- @@ L196-196 verbatim
open Encodable FirstOrder


-- @@ L198-205 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma mem_iff_mem_bitIndices {x s : ℕ} : x ∈ s ↔ x ∈ s.bitIndices := by
  induction s using Nat.binaryRec generalizing x
  case zero => simp
  case bit b s ih =>
    cases b <;> simp
    · cases' x with x <;> simp [ih]
    · cases' x with x <;> simp [ih]


-- @@ L207-208 verbatim
lemma nat_mem_iff {x s : ℕ} : x ∈ s ↔ s / 2 ^ x % 2 = 1 := by
  simp [mem_iff_mem_bitIndices, Nat.testBit_eq_decide_div_mod_eq]


-- @@ L210-212 verbatim
lemma nat_insert_eq (x s : ℕ) :
    (insert x s : ℕ) = if s / 2 ^ x % 2 = 1 then s else s + 2 ^ x := by
  simp [insert_eq, bitInsert, exp_nat_eq_two_pow, nat_mem_iff]


-- @@ L214-214 verbatim
variable {L : Language} [L.Encodable] [L.LORDefinable]


-- @@ L216-236 expanded
lemma IsSemiterm.sound {n t : ℕ} (ht : IsSemiterm L n t) :
    ∃ T : FirstOrder.SyntacticSemiterm L n, GödelQuote.quote T = t :=
  by
  induction t using Nat.strongRec
  case ind t
    ih =>
    rcases ht.case with (⟨z, hz, rfl⟩ | ⟨x, rfl⟩ | ⟨k, f, v, hf, hv, rfl⟩)
    · exact ⟨Semiterm.bvar ⟨z, hz⟩, by simp⟩
    · exact ⟨Semiterm.fvar x, by simp [Semiterm.quote_fvar]⟩
    · have : ∀ i : Fin k, ∃ t : FirstOrder.SyntacticSemiterm L n, GödelQuote.quote t = nth v i :=
        fun i ↦ ih (nth v i) (nth_lt_qqFunc_of_lt (by simp [hv.lh])) (hv.nth i.prop)
      choose v' hv' using this
      have : ∃ F, encode F = f :=
        isFunc_quote_quote (V := ℕ) (L := L) (x := f) (k := k) |>.mp (by simp [hf])
      rcases this with ⟨f, rfl⟩
      refine ⟨FirstOrder.Semiterm.func f v', ?_⟩
      suffices SemitermVec.val (fun i ↦ GödelQuote.quote (v' i)) = v by
        simpa [Semiterm.quote_func, quote_func_def]
      apply nth_ext' k (by simp) (by simp [hv.lh])
      intro i hik
      let j : Fin k := ⟨i, hik⟩
      calc
        nth (SemitermVec.val fun i ↦ GödelQuote.quote (v' i)) i =
            nth (SemitermVec.val fun i ↦ GödelQuote.quote (v' i)) ↑j :=
          rfl
        _ = GödelQuote.quote (v' j) := by
          simpa [Semiterm.quote_def] using
            SemitermVec.val_nth_eq
              (fun i ↦ (GödelQuote.quote (v' i) : Bootstrapping.Semiterm ℕ L n)) j
        _ = nth v i := hv' j


-- @@ L238-238 verbatim
end FFL.FirstOrder.Arithmetic.Bootstrapping
