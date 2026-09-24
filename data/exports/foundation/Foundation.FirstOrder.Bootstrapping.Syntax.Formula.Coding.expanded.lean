module

public import Foundation.FirstOrder.Basic.PrimrecCoding
public import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Typed
public import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Coding


-- @@ L7-7 verbatim
@[expose] public section

-- @@ L8-8 verbatim
open Encodable FFL FirstOrder Arithmetic Bootstrapping


-- @@ L10-10 verbatim
namespace FFL


-- @@ L12-21 verbatim
class LCWQIsoGödelQuote (α β : ℕ → Type*) [LCWQ α] [LCWQ β] where
  gq : ∀ n, GödelQuote (α n) (β n)
  top : ⌜(⊤ : α n)⌝ = (⊤ : β n)
  bot : ⌜(⊥ : α n)⌝ = (⊥ : β n)
  and (φ ψ : α n) : (⌜φ ⋏ ψ⌝ : β n) = ⌜φ⌝ ⋏ ⌜ψ⌝
  or (φ ψ : α n) : (⌜φ ⋎ ψ⌝ : β n) = ⌜φ⌝ ⋎ ⌜ψ⌝
  imply (φ ψ : α n) : (⌜φ 🡒 ψ⌝ : β n) = ⌜φ⌝ 🡒 ⌜ψ⌝
  neg (φ : α n) : (⌜∼φ⌝ : β n) = ∼⌜φ⌝
  all (φ : α (n + 1)) : (⌜∀¹ φ⌝ : β n) = ∀¹ ⌜φ⌝
  exs (φ : α (n + 1)) : (⌜∃¹ φ⌝ : β n) = ∃¹ ⌜φ⌝


-- @@ L23-23 verbatim
namespace LCWQIsoGödelQuote


-- @@ L25-25 verbatim
attribute [simp] top bot and or imply neg all exs


-- @@ L27-27 verbatim
variable {α β : ℕ → Type*} [LCWQ α] [LCWQ β] [LCWQIsoGödelQuote α β]


-- @@ L29-29 verbatim
instance (n : ℕ) : GödelQuote (α n) (β n) := gq n


-- @@ L31-31 verbatim
@[simp] lemma iff (φ ψ : α n) : (⌜φ 🡘 ψ⌝ : β n) = ⌜φ⌝ 🡘 ⌜ψ⌝ := by simp [LogicalConnective.iff]


-- @@ L33-34 verbatim
@[simp] lemma ball (φ : α (n + 1)) (ψ : α (n + 1)) :
    (⌜∀¹[φ] ψ⌝ : β n)  = ∀¹[⌜φ⌝] ⌜ψ⌝ := by simp [FFL.FirstOrder.ball]


-- @@ L36-37 verbatim
@[simp] lemma bexs (φ : α (n + 1)) (ψ : α (n + 1)) :
    (⌜∃¹[φ] ψ⌝ : β n)  = ∃¹[⌜φ⌝] ⌜ψ⌝ := by simp [FFL.FirstOrder.bexs]


-- @@ L39-39 verbatim
end LCWQIsoGödelQuote


-- @@ L41-41 verbatim
end FFL


-- @@ L43-43 verbatim
namespace FFL


-- @@ L45-45 verbatim
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


-- @@ L47-47 verbatim
variable {L : Language} [L.Encodable] [L.LORDefinable]


-- @@ L49-49 verbatim
namespace FirstOrder.Semiformula


-- @@ L51-51 verbatim
variable (V) {n : ℕ}


-- @@ L53-61 verbatim
noncomputable def typedQuote {n} : Semiproposition L n → Bootstrapping.Semiformula V L n
  |  rel R v => Bootstrapping.Semiformula.rel R fun i ↦ ⌜v i⌝
  | nrel R v => Bootstrapping.Semiformula.nrel R fun i ↦ ⌜v i⌝
  |        ⊤ => ⊤
  |        ⊥ => ⊥
  |    φ ⋏ ψ => φ.typedQuote ⋏ ψ.typedQuote
  |    φ ⋎ ψ => φ.typedQuote ⋎ ψ.typedQuote
  |     ∀¹ φ => ∀¹ φ.typedQuote
  |     ∃¹ φ => ∃¹ φ.typedQuote


-- @@ L63-74 verbatim
variable {V}

lemma typedQuote_neg {n} (φ : Semiproposition L n) : (∼φ).typedQuote V = ∼(φ.typedQuote V) := by
  match φ with
  |  rel R v => simp [typedQuote]
  | nrel R v => simp [typedQuote]
  |        ⊤ => simp [typedQuote]
  |        ⊥ => simp [typedQuote]
  |    φ ⋏ ψ => simp [typedQuote, typedQuote_neg φ, typedQuote_neg ψ]
  |    φ ⋎ ψ => simp [typedQuote, typedQuote_neg φ, typedQuote_neg ψ]
  |     ∀¹ φ => simp [typedQuote, typedQuote_neg φ]
  |     ∃¹ φ => simp [typedQuote, typedQuote_neg φ]


-- @@ L76-85 verbatim
noncomputable instance : LCWQIsoGödelQuote (Semiproposition L) (Bootstrapping.Semiformula V L) where
  gq _ := ⟨typedQuote V⟩
  top := rfl
  bot := rfl
  and _ _ := rfl
  or _ _ := rfl
  neg _ := by simpa [typedQuote] using! typedQuote_neg _
  imply _ _ := by simpa [Bootstrapping.Semiformula.imp_def, imp_eq, typedQuote] using! typedQuote_neg _
  all _ := rfl
  exs _ := rfl


-- @@ L87-88 verbatim
@[simp] lemma typed_quote_rel (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜rel R v⌝ : Bootstrapping.Semiformula V L n) = Bootstrapping.Semiformula.rel R fun i ↦ ⌜v i⌝ := rfl


-- @@ L90-91 verbatim
@[simp] lemma typed_quote_nrel (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜nrel R v⌝ : Bootstrapping.Semiformula V L n) = Bootstrapping.Semiformula.nrel R fun i ↦ ⌜v i⌝ := rfl


-- @@ L93-103 verbatim
@[simp] lemma typed_quote_shift (φ : Semiproposition L n) :
    (⌜Rewriting.shift φ⌝ : Bootstrapping.Semiformula V L n) = Bootstrapping.Semiformula.shift ⌜φ⌝ := by
  induction φ using Semiformula.rec'
  case hrel => simp [*]; rfl
  case hnrel => simp [*]; rfl
  case hverum => simp
  case hfalsum => simp
  case hand => simp [*]
  case hor => simp [*]
  case hall φ ih => simp [*]
  case hexs φ ih => simp [*]


-- @@ L105-117 verbatim
@[simp] lemma typed_quote_substs {n m} (w : Fin n → SyntacticSemiterm L m) (φ : Semiproposition L n) :
    (⌜φ ⇜ w⌝ : Bootstrapping.Semiformula V L m) = Bootstrapping.Semiformula.subst (fun i ↦ ⌜w i⌝) ⌜φ⌝ := by
  induction φ using Semiformula.rec' generalizing m
  case hrel => simp [*]; rfl
  case hnrel => simp [*]; rfl
  case hverum => simp
  case hfalsum => simp
  case hand => simp [*]
  case hor => simp [*]
  case hall φ ih =>
    simp [*, Rew.q_subst, Matrix.comp_vecCons']; rfl
  case hexs φ ih =>
    simp [*, Rew.q_subst, Matrix.comp_vecCons']; rfl


-- @@ L119-122 verbatim
@[simp] lemma free_quote (φ : Semiproposition L 1) :
    (⌜Rewriting.free φ⌝ : Bootstrapping.Formula V L) = Bootstrapping.Semiformula.free ⌜φ⌝ := by
  rw [← LawfulSyntacticRewriting.app_subst_fbar_zero_comp_shift_eq_free, typed_quote_substs, typed_quote_shift]
  simp [Bootstrapping.Semiformula.free, Matrix.constant_eq_singleton]


-- @@ L124-124 verbatim
open Bootstrapping.Arithmetic


-- @@ L126-127 verbatim
@[simp] lemma typed_quote_eq (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜(“!!t = !!u” : ArithmeticSemiproposition n)⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) = (⌜t⌝ ≐ ⌜u⌝) := rfl


-- @@ L129-130 verbatim
@[simp] lemma typed_quote_ne (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜(“!!t ≠ !!u” : ArithmeticSemiproposition n)⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) = (⌜t⌝ ≉ ⌜u⌝) := rfl


-- @@ L132-133 verbatim
@[simp] lemma typed_quote_lt (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜(“!!t < !!u” : ArithmeticSemiproposition n)⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) = (⌜t⌝ <' ⌜u⌝) := rfl


-- @@ L135-188 verbatim
@[simp] lemma typed_quote_nlt (t u : SyntacticSemiterm ℒₒᵣ n) :
    (⌜(“!!t ≮ !!u” : ArithmeticSemiproposition n)⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) = (⌜t⌝ ≮' ⌜u⌝) := rfl

lemma ne_iff_val_ne (φ ψ : Bootstrapping.Semiformula V L n) : φ ≠ ψ ↔ φ.val ≠ ψ.val := Iff.ne Semiformula.ext_iff

lemma typed_quote_inj {n} {φ₁ φ₂ : Semiproposition L n} : (⌜φ₁⌝ : Bootstrapping.Semiformula V L n) = ⌜φ₂⌝ → φ₁ = φ₂ :=
  match φ₁, φ₂ with
  | rel R₁ v₁, rel R₂ v₂ => by
    simp only [typed_quote_rel, Bootstrapping.Semiformula.rel, Semiformula.mk.injEq, qqRel_inj,
      Nat.cast_inj, rel.injEq, and_imp]
    rintro rfl
    simp only [quote_rel_inj, heq_eq_eq, true_and]
    rintro rfl
    suffices ((fun i ↦ ⌜v₁ i⌝) = fun i ↦ ⌜v₂ i⌝) → v₁ = v₂ by
      simpa [←SemitermVec.val_inj]
    intro h
    ext i
    exact Semiterm.typed_quote_inj (congr_fun h i)
  | nrel R₁ v₁, nrel R₂ v₂ => by
    simp only [typed_quote_nrel, Bootstrapping.Semiformula.nrel, Semiformula.mk.injEq, qqNRel_inj,
      Nat.cast_inj, nrel.injEq, and_imp]
    rintro rfl
    simp only [quote_rel_inj, heq_eq_eq, true_and]
    rintro rfl
    suffices ((fun i ↦ ⌜v₁ i⌝) = fun i ↦ ⌜v₂ i⌝) → v₁ = v₂ by
      simpa [←SemitermVec.val_inj]
    intro h
    ext i
    exact Semiterm.typed_quote_inj (congr_fun h i)
  |         ⊤,         ⊤ => by simp
  |         ⊥,         ⊥ => by simp
  |   φ₁ ⋏ ψ₁,   φ₂ ⋏ ψ₂ => by
    simp only [LCWQIsoGödelQuote.and, Bootstrapping.Semiformula.and_inj, and_inj, and_imp]
    intro hφ hψ
    refine ⟨typed_quote_inj hφ, typed_quote_inj hψ⟩
  |   φ₁ ⋎ ψ₁,   φ₂ ⋎ ψ₂ => by
    simp only [LCWQIsoGödelQuote.or, Bootstrapping.Semiformula.or_inj, or_inj, and_imp]
    intro hφ hψ
    refine ⟨typed_quote_inj hφ, typed_quote_inj hψ⟩
  |     ∀¹ φ₁,     ∀¹ φ₂ => by
    simp only [LCWQIsoGödelQuote.all, Bootstrapping.Semiformula.all_inj, all_inj]
    exact typed_quote_inj
  |     ∃¹ φ₁,     ∃¹ φ₂ => by
    simp only [LCWQIsoGödelQuote.exs, Bootstrapping.Semiformula.exs_inj, exs_inj]
    exact typed_quote_inj
  | rel _ _, nrel _ _ | rel _ _, ⊤ | rel _ _, ⊥ | rel _ _, _ ⋏ _ | rel _ _, _ ⋎ _ | rel _ _, ∀¹ _ | rel _ _, ∃¹ _
  | nrel _ _, rel _ _ | nrel _ _, ⊤ | nrel _ _, ⊥ | nrel _ _, _ ⋏ _ | nrel _ _, _ ⋎ _ | nrel _ _, ∀¹ _ | nrel _ _, ∃¹ _
  | ⊤, rel _ _ | ⊤, nrel _ _ | ⊤, ⊥ | ⊤, _ ⋏ _ | ⊤, _ ⋎ _ | ⊤, ∀¹ _ | ⊤, ∃¹ _
  | ⊥, rel _ _ | ⊥, nrel _ _ | ⊥, ⊤ | ⊥, _ ⋏ _ | ⊥, _ ⋎ _ | ⊥, ∀¹ _ | ⊥, ∃¹ _
  | _ ⋏ _, rel _ _ | _ ⋏ _, nrel _ _ | _ ⋏ _, ⊤ | _ ⋏ _, ⊥ | _ ⋏ _, _ ⋎ _ | _ ⋏ _, ∀¹ _ | _ ⋏ _, ∃¹ _
  | _ ⋎ _, rel _ _ | _ ⋎ _, nrel _ _ | _ ⋎ _, ⊤ | _ ⋎ _, ⊥ | _ ⋎ _, _ ⋏ _ | _ ⋎ _, ∀¹ _ | _ ⋎ _, ∃¹ _
  | ∀¹ _, rel _ _ | ∀¹ _, nrel _ _ | ∀¹ _, ⊤ | ∀¹ _, ⊥ | ∀¹ _, _ ⋏ _ | ∀¹ _, _ ⋎ _ | ∀¹ _, ∃¹ _
  | ∃¹ _, rel _ _ | ∃¹ _, nrel _ _ | ∃¹ _, ⊤ | ∃¹ _, ⊥ | ∃¹ _, _ ⋏ _ | ∃¹ _, _ ⋎ _ | ∃¹ _, ∀¹ _ => by
    simp [ne_iff_val_ne, qqRel, qqNRel, qqVerum, qqFalsum, qqAnd, qqOr, qqAll, qqExs]


-- @@ L190-191 verbatim
@[simp] lemma typed_quote_inj_iff {φ₁ φ₂ : Semiproposition L n} :
    (⌜φ₁⌝ : Bootstrapping.Semiformula V L n) = ⌜φ₂⌝ ↔ φ₁ = φ₂ := ⟨typed_quote_inj, by rintro rfl; rfl⟩


-- @@ L193-196 verbatim
noncomputable instance : GödelQuote (Semiproposition L n) V where
  quote φ := (⌜φ⌝ : Bootstrapping.Semiformula V L n).val

lemma quote_def (φ : Semiproposition L n) : (⌜φ⌝ : V) = (⌜φ⌝ : Bootstrapping.Semiformula V L n).val := rfl


-- @@ L198-198 verbatim
@[simp] lemma quote_isSemiformula (φ : Semiproposition L n) : IsSemiformula L ↑n (⌜φ⌝ : V) := by simp [quote_def]


-- @@ L200-200 verbatim
@[simp] lemma quote_isSemiformula₀ (φ : Proposition L) : IsSemiformula L 0 (⌜φ⌝ : V) := by simp [quote_def]


-- @@ L202-202 verbatim
@[simp] lemma quote_isSemiformul₁ (φ : Semiproposition L 1) : IsSemiformula L 1 (⌜φ⌝ : V) := by simp [quote_def]


-- @@ L204-205 verbatim
@[simp] lemma quote_rel (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜rel R v⌝ : V) = ^rel ↑k ⌜R⌝ (SemitermVec.val fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm V L n)) := rfl


-- @@ L207-208 verbatim
@[simp] lemma quote_nrel (R : L.Rel k) (v : Fin k → SyntacticSemiterm L n) :
    (⌜nrel R v⌝ : V) = ^nrel ↑k ⌜R⌝ (SemitermVec.val fun i ↦ (⌜v i⌝ : Bootstrapping.Semiterm V L n)) := rfl


-- @@ L210-210 verbatim
@[simp] lemma quote_verum : (⌜(⊤ : Semiproposition L n)⌝ : V) = ^⊤ := rfl


-- @@ L212-212 verbatim
@[simp] lemma quote_falsum : (⌜(⊥ : Semiproposition L n)⌝ : V) = ^⊥ := rfl


-- @@ L214-214 verbatim
@[simp] lemma quote_and (φ ψ : Semiproposition L n) : (⌜φ ⋏ ψ⌝ : V) = ⌜φ⌝ ^⋏ ⌜ψ⌝ := rfl


-- @@ L216-216 verbatim
@[simp] lemma quote_or (φ ψ : Semiproposition L n) : (⌜φ ⋎ ψ⌝ : V) = ⌜φ⌝ ^⋎ ⌜ψ⌝ := rfl


-- @@ L218-218 verbatim
@[simp] lemma quote_all (φ : Semiproposition L (n + 1)) : (⌜∀¹ φ⌝ : V) = ^∀ ⌜φ⌝ := rfl


-- @@ L220-247 verbatim
@[simp] lemma quote_ex (φ : Semiproposition L (n + 1)) : (⌜∃¹ φ⌝ : V) = ^∃ ⌜φ⌝ := rfl

lemma quote_shift (φ : Semiproposition L n) :
    (⌜Rewriting.shift φ⌝ : V) = Bootstrapping.shift L ⌜φ⌝ := by simp [quote_def]

lemma quote_eq_encode (φ : Semiproposition L n) : (⌜φ⌝ : V) = ↑(encode φ) := by
  suffices (⌜φ⌝ : Bootstrapping.Semiformula V L n).val = ↑(encode φ) from this
  induction φ using rec'
  case hrel => simp [encode_rel, qqRel, coe_pair_eq_pair_coe, Semiterm.quote_eq_encode']; rfl
  case hnrel => simp [encode_nrel, qqNRel, coe_pair_eq_pair_coe, Semiterm.quote_eq_encode']; rfl
  case hverum => simp [encode_verum, qqVerum, coe_pair_eq_pair_coe]
  case hfalsum => simp [encode_falsum, qqFalsum, coe_pair_eq_pair_coe]
  case hand => simp [encode_and, qqAnd, coe_pair_eq_pair_coe,  *]; simp [encode_eq_toNat]
  case hor => simp [encode_or, qqOr, coe_pair_eq_pair_coe,  *]; simp [encode_eq_toNat]
  case hall => simp [encode_all, qqAll, coe_pair_eq_pair_coe, *]; simp [encode_eq_toNat]
  case hexs => simp [encode_ex, qqExs, coe_pair_eq_pair_coe, *]; simp [encode_eq_toNat]

lemma coe_quote_eq_quote (φ : Semiproposition L n) : (↑(⌜φ⌝ : ℕ) : V) = ⌜φ⌝ := by
  simp [quote_eq_encode]

lemma coe_quote_eq_quote' (φ : Semiproposition L n) :
    (↑(⌜φ⌝ : Bootstrapping.Semiformula ℕ L n).val : V) = (⌜φ⌝ : Bootstrapping.Semiformula V L n).val :=
  coe_quote_eq_quote φ

lemma quote_eq_encode_nat (φ : Semiproposition L n) : (⌜φ⌝ : ℕ) = encode φ := by simpa using quote_eq_encode (V := ℕ) φ

lemma primrec_quote_natCast [L.Primcodable] : Primrec λ φ : Semiproposition L n ↦ (⌜φ⌝ : ℕ) :=
  Primrec.encode.of_eq λ φ ↦ (quote_eq_encode_nat φ).symm


-- @@ L249-250 verbatim
@[simp] lemma quote_inj_iff {φ₁ φ₂ : Semiproposition L n} :
    (⌜φ₁⌝ : V) = ⌜φ₂⌝ ↔ φ₁ = φ₂ := by simp [quote_eq_encode]


-- @@ L252-261 verbatim
noncomputable instance : LCWQIsoGödelQuote (Semisentence L) (Bootstrapping.Semiformula V L) where
  gq n := ⟨fun σ ↦ (⌜(Rewriting.emb σ : Semiproposition L n)⌝)⟩
  top := by simp
  bot := by simp
  and _ _ := by simp
  or _ _ := by simp
  neg _ := by simp
  imply _ _ := by simp
  all _ := by simp
  exs _ := by simp


-- @@ L263-264 verbatim
@[simp] lemma coe_quote {ξ n} (φ : Semiproposition L n) : ↑(⌜φ⌝ : ℕ) = (⌜φ⌝ : ArithmeticSemiterm ξ m) := by
  simp [gödelNumber'_def, Semiformula.quote_eq_encode]


-- @@ L266-268 verbatim
@[simp] lemma quote_quote_eq_numeral (φ : Semiproposition L n) :
    (⌜(⌜φ⌝ : ArithmeticSemiterm ℕ m)⌝ : Bootstrapping.Semiterm V ℒₒᵣ m) = Bootstrapping.Arithmetic.typedNumeral ⌜φ⌝ := by
  simp [←coe_quote, coe_quote_eq_quote]


-- @@ L270-270 verbatim
end Semiformula


-- @@ L272-272 verbatim
namespace Sentence


-- @@ L274-275 verbatim
theorem typed_quote_def (σ : Semisentence L n) :
    (⌜σ⌝ : Bootstrapping.Semiformula V L n) = ⌜(Rewriting.emb σ : Semiproposition L n)⌝ := rfl


-- @@ L277-278 verbatim
@[simp] lemma typed_quote_eq (t u : ClosedSemiterm ℒₒᵣ n) :
    (⌜(“!!t = !!u” : ArithmeticSemisentence n)⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) = (⌜t⌝ ≐ ⌜u⌝) := rfl


-- @@ L280-281 verbatim
@[simp] lemma typed_quote_ne (t u : ClosedSemiterm ℒₒᵣ n) :
    (⌜(“!!t ≠ !!u” : ArithmeticSemisentence n)⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) = (⌜t⌝ ≉ ⌜u⌝) := rfl


-- @@ L283-284 verbatim
@[simp] lemma typed_quote_lt (t u : ClosedSemiterm ℒₒᵣ n) :
    (⌜(“!!t < !!u” : ArithmeticSemisentence n)⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) = (⌜t⌝ <' ⌜u⌝) := rfl


-- @@ L286-287 verbatim
@[simp] lemma typed_quote_nlt (t u : ClosedSemiterm ℒₒᵣ n) :
    (⌜(“!!t ≮ !!u” : ArithmeticSemisentence n)⌝ : Bootstrapping.Semiformula V ℒₒᵣ n) = (⌜t⌝ ≮' ⌜u⌝) := rfl


-- @@ L289-292 verbatim
noncomputable instance : GödelQuote (Semisentence L n) V where
  quote σ := ⌜(Rewriting.emb σ : Semiproposition L n)⌝

lemma quote_def (σ : Semisentence L n) : (⌜σ⌝ : V) = ⌜(Rewriting.emb σ : Semiproposition L n)⌝ := rfl


-- @@ L294-294 verbatim
theorem quote_eq (σ : Semisentence L n) : (⌜σ⌝ : V) = (⌜σ⌝ : Bootstrapping.Semiformula V L n).val := rfl


-- @@ L296-296 verbatim
@[simp] lemma quote_isSemiformula (φ : Semisentence L n) : IsSemiformula L ↑n (⌜φ⌝ : V) := by simp [quote_def]


-- @@ L298-298 verbatim
@[simp] lemma quote_isSemiformula₀ (φ : Sentence L) : IsSemiformula L 0 (⌜φ⌝ : V) := by simp [quote_def]


-- @@ L300-310 verbatim
@[simp] lemma quote_isSemiformul₁ (φ : Semisentence L 1) : IsSemiformula L 1 (⌜φ⌝ : V) := by simp [quote_def]

lemma quote_eq_encode (σ : Semisentence L n) : (⌜σ⌝ : V) = ↑(encode σ) := by simp [quote_def, Semiformula.quote_eq_encode]

lemma coe_quote_eq_quote (σ : Semisentence L n) : (↑(⌜σ⌝ : ℕ) : V) = ⌜σ⌝ := by
  simp [quote_eq_encode]

lemma quote_eq_encode_nat (σ : Semisentence L n) : (⌜σ⌝ : ℕ) = encode σ := by simpa using quote_eq_encode (V := ℕ) σ

lemma primrec_quote_natCast [L.Primcodable] : Primrec λ σ : Semisentence L n ↦ (⌜σ⌝ : ℕ) :=
  Primrec.encode.of_eq λ σ ↦ (quote_eq_encode_nat σ).symm


-- @@ L312-314 verbatim
@[simp] lemma val_quote {bv : Fin m → V} {fv : ξ → V} (σ : Semisentence L n) :
    (⌜σ⌝ : ArithmeticSemiterm ξ m).val bv fv = ⌜σ⌝ := by
  simp [gödelNumber'_def, quote_eq_encode, numeral_eq_natCast]


-- @@ L316-317 verbatim
@[simp] lemma coe_quote {ξ n} (σ : Semisentence L n) : ↑(⌜σ⌝ : ℕ) = (⌜σ⌝ : ArithmeticSemiterm ξ m) := by
  simp [gödelNumber'_def, quote_eq_encode]


-- @@ L319-321 verbatim
@[simp] lemma quote_quote_eq_numeral (σ : Semisentence L n) :
    (⌜(⌜σ⌝ : ArithmeticSemiterm ℕ m)⌝ : Bootstrapping.Semiterm V ℒₒᵣ m) = Bootstrapping.Arithmetic.typedNumeral ⌜σ⌝ := by
  simp [←coe_quote, coe_quote_eq_quote]


-- @@ L323-324 verbatim
@[simp] lemma quote_inj_iff {σ₁ σ₂ : Semisentence L n} :
    (⌜σ₁⌝ : V) = ⌜σ₂⌝ ↔ σ₁ = σ₂ := by simp [quote_eq_encode]


-- @@ L326-326 verbatim
end Sentence


-- @@ L328-328 verbatim
end FirstOrder


-- @@ L330-330 verbatim
namespace FirstOrder.Arithmetic.Bootstrapping


-- @@ L332-379 verbatim
open Encodable FirstOrder

lemma IsSemiformula.sound {n φ : ℕ} (h : IsSemiformula L n φ) : ∃ F : FirstOrder.Semiproposition L n, ⌜F⌝ = φ := by
  induction φ using Nat.strongRec generalizing n
  case ind φ ih =>
    rcases IsSemiformula.case_iff.mp h with
      (⟨k, r, v, hr, hv, rfl⟩ | ⟨k, r, v, hr, hv, rfl⟩ | rfl | rfl |
       ⟨φ, ψ, hp, hq, rfl⟩ | ⟨φ, ψ, hp, hq, rfl⟩ | ⟨φ, hp, rfl⟩ | ⟨φ, hp, rfl⟩)
    · have : ∀ i : Fin k, ∃ t : FirstOrder.SyntacticSemiterm L n, ⌜t⌝ = v.[i] := fun i ↦ (hv.nth i.prop).sound
      choose v' hv' using this
      have : ∃ R, encode R = r := isRel_quote_quote (V := ℕ) (L := L) (x := r) (k := k) |>.mp (by simp [hr])
      rcases this with ⟨R, rfl⟩
      refine ⟨FirstOrder.Semiformula.rel R v', ?_⟩
      suffices SemitermVec.val (fun i ↦ ⌜v' i⌝) = v by simpa [Semiformula.quote_rel, quote_rel_def]
      apply nth_ext' k (by simp) (by simp [hv.lh])
      intro i hik
      let j : Fin k := ⟨i, hik⟩
      calc
        (SemitermVec.val fun i ↦ ⌜v' i⌝).[i] = (SemitermVec.val fun i ↦ ⌜v' i⌝).[↑j] := rfl
        _                                    = ⌜v' j⌝ := by
          simpa [Semiterm.quote_def] using SemitermVec.val_nth_eq (fun i ↦ (⌜v' i⌝ : Bootstrapping.Semiterm ℕ L n)) j
        _                                    = v.[i] := hv' j
    · have : ∀ i : Fin k, ∃ t : FirstOrder.SyntacticSemiterm L n, ⌜t⌝ = v.[i] := fun i ↦ (hv.nth i.prop).sound
      choose v' hv' using this
      have : ∃ R, encode R = r := isRel_quote_quote (V := ℕ) (L := L) (x := r) (k := k) |>.mp (by simp [hr])
      rcases this with ⟨R, rfl⟩
      refine ⟨FirstOrder.Semiformula.nrel R v', ?_⟩
      suffices SemitermVec.val (fun i ↦ ⌜v' i⌝) = v by simpa [Semiformula.quote_nrel, quote_rel_def]
      apply nth_ext' k (by simp) (by simp [hv.lh])
      intro i hik
      let j : Fin k := ⟨i, hik⟩
      calc
        (SemitermVec.val fun i ↦ ⌜v' i⌝).[i] = (SemitermVec.val fun i ↦ ⌜v' i⌝).[↑j] := rfl
        _                                    = ⌜v' j⌝ := by
          simpa [Semiterm.quote_def] using SemitermVec.val_nth_eq (fun i ↦ (⌜v' i⌝ : Bootstrapping.Semiterm ℕ L n)) j
        _                                    = v.[i] := hv' j
    · exact ⟨⊤, by simp⟩
    · exact ⟨⊥, by simp⟩
    · rcases ih φ (by simp) hp with ⟨φ, rfl⟩
      rcases ih ψ (by simp) hq with ⟨ψ, rfl⟩
      exact ⟨φ ⋏ ψ, by simp⟩
    · rcases ih φ (by simp) hp with ⟨φ, rfl⟩
      rcases ih ψ (by simp) hq with ⟨ψ, rfl⟩
      exact ⟨φ ⋎ ψ, by simp⟩
    · rcases ih φ (by simp) hp with ⟨φ, rfl⟩
      exact ⟨∀¹ φ, by simp⟩
    · rcases ih φ (by simp) hp with ⟨φ, rfl⟩
      exact ⟨∃¹ φ, by simp⟩


-- @@ L381-381 verbatim
end FirstOrder.Arithmetic.Bootstrapping


-- @@ L383-383 verbatim
end FFL
