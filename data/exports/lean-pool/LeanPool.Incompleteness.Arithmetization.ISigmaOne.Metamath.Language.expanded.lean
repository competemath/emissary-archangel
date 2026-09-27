/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Arithmetization.Basic.Ind
import LeanPool.Incompleteness.Arithmetization.Definability.Absoluteness
import LeanPool.Incompleteness.Arithmetization.Definability.BoundedBoldface
import LeanPool.Incompleteness.Arithmetization.Definability.Init


-- @@ L13-13 verbatim
/-! # Language -/


-- @@ L15-15 verbatim
@[expose] public section



-- @@ L18-18 verbatim
noncomputable section «lp_nc_section_1»


-- @@ L20-20 verbatim
namespace LO

-- @@ L21-21 verbatim
namespace Arith


-- @@ L23-23 verbatim
open FirstOrder FirstOrder.Arith


-- @@ L25-25 verbatim
section «lp_section_1»


-- @@ L27-27 verbatim
variable {V : Type*} [ORingStruc V]


-- @@ L29-29 verbatim
variable (V)


-- @@ L31-36 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure _root_.LO.FirstOrder.Arith.LDef where
  /-- Imported declaration from the Incompleteness formalization. -/
  func : Sg0.Semisentence 2
  /-- Imported declaration from the Incompleteness formalization. -/
  rel : Sg0.Semisentence 2


-- @@ L38-43 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
protected structure Language where
  /-- Imported declaration from the Incompleteness formalization. -/
  Func (arity : V) : V → Prop
  /-- Imported declaration from the Incompleteness formalization. -/
  Rel (arity : V) : V → Prop


-- @@ L45-45 verbatim
variable {V}


-- @@ L47-47 verbatim
namespace Language


-- @@ L49-52 expanded
/-- Imported declaration from the Incompleteness formalization. -/
protected class Defined (L : Arith.Language V) (pL : outParam LDef) where
  func : DefinedRel Sg0 L.Func pL.func
  rel : DefinedRel Sg0 L.Rel pL.rel


-- @@ L54-54 verbatim
variable {L : Arith.Language V} {pL : LDef} [L.Defined pL]


-- @@ L56-57 verbatim
lemma _root_.LO.Arith.Language.Defined.eval_func (v) :
    Semiformula.Evalbm V v pL.func.val ↔ L.Func (v 0) (v 1) := Defined.func.df.iff v


-- @@ L59-60 verbatim
lemma _root_.LO.Arith.Language.Defined.eval_rel_iff (v) :
    Semiformula.Evalbm V v pL.rel.val ↔ L.Rel (v 0) (v 1) := Defined.rel.df.iff v


-- @@ L62-63 expanded
instance _root_.LO.Arith.Language.Defined.func_definable : BoldfaceRel Sg0 L.Func :=
  Defined.func.to_definable


-- @@ L65-66 expanded
instance _root_.LO.Arith.Language.Defined.rel_definable : BoldfaceRel Sg0 L.Rel :=
  Defined.rel.to_definable


-- @@ L68-70 expanded
@[simp, aesop 10 (rule_sets := [Definability]) safe]
instance _root_.LO.Arith.Language.Defined.func_definable' (ℌ) : BoldfaceRel ℌ L.Func :=
  HierarchySymbol.Boldface.of_zero Defined.func_definable


-- @@ L72-74 expanded
@[simp, aesop 10 (rule_sets := [Definability]) safe]
instance _root_.LO.Arith.Language.Defined.rel_definable' (ℌ) : BoldfaceRel ℌ L.Rel :=
  HierarchySymbol.Boldface.of_zero Defined.rel_definable


-- @@ L76-76 verbatim
end Language


-- @@ L78-78 verbatim
end «lp_section_1»


-- @@ L80-80 verbatim
section «lp_section_2»


-- @@ L82-82 verbatim
variable {L₀ : Language} [L₀.ORing]


-- @@ L84-84 verbatim
variable {L : Language} [(k : ℕ) → Encodable (L.Func k)] [(k : ℕ) → Encodable (L.Rel k)]


-- @@ L86-87 verbatim
instance (k) : Semiterm.Operator.GoedelNumber L₀ (L.Func k) :=
  ⟨fun f ↦ Semiterm.Operator.numeral L₀ (Encodable.encode f)⟩


-- @@ L89-90 verbatim
instance (k) : Semiterm.Operator.GoedelNumber L₀ (L.Rel k) :=
  ⟨fun r ↦ Semiterm.Operator.numeral L₀ (Encodable.encode r)⟩


-- @@ L92-92 verbatim
variable (L)


-- @@ L94-99 expanded
/-- Imported declaration from the Incompleteness formalization. -/
class DefinableLanguage extends Arith.LDef where
  func_iff {k c : ℕ} : c ∈ Set.range (Encodable.encode : L.Func k → ℕ) ↔ (Evalbm ℕ ![k, c]) func.val
  rel_iff {k c : ℕ} : c ∈ Set.range (Encodable.encode : L.Rel k → ℕ) ↔ (Evalbm ℕ ![k, c]) rel.val


-- @@ L101-102 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Language.lDef [d : DefinableLanguage L] : LDef := d.toLDef


-- @@ L104-104 verbatim
variable {L}


-- @@ L106-106 verbatim
variable [DefinableLanguage L]


-- @@ L108-108 verbatim
variable {V : Type*} [ORingStruc V]


-- @@ L110-110 verbatim
variable (L V)


-- @@ L112-115 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Language.codeIn : Arith.Language V
    where
  Func := fun x y ↦ (Evalbm V ![x, y]) L.lDef.func.val
  Rel := fun x y ↦ (Evalbm V ![x, y]) L.lDef.rel.val


-- @@ L117-119 expanded
lemma _root_.LO.FirstOrder.Language.codeIn_func_def :
    (L.codeIn V).Func = fun x y ↦ (Evalbm V ![x, y]) L.lDef.func.val :=
  rfl


-- @@ L121-121 verbatim
variable {L V}


-- @@ L123-123 expanded
variable [ModelsTheory V PeanoMinus]


-- @@ L125-127 verbatim
instance : (L.codeIn V).Defined L.lDef where
  func := by intro v; simp [Language.codeIn, ←Matrix.fun_eq_vec₂]
  rel := by intro v; simp [Language.codeIn, ←Matrix.fun_eq_vec₂]


-- @@ L129-129 verbatim
instance : GoedelQuote (L.Func k) V := ⟨fun f ↦ ↑(Encodable.encode f)⟩


-- @@ L131-131 verbatim
instance : GoedelQuote (L.Rel k) V := ⟨fun R ↦ ↑(Encodable.encode R)⟩


-- @@ L133-134 expanded
omit [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L] in
lemma quote_func_def (f : L.Func k) : (GoedelQuote.quote f : V) = ↑(Encodable.encode f) :=
  rfl


-- @@ L136-137 expanded
omit [(k : ℕ) → Encodable (L.Func k)] [DefinableLanguage L] in
lemma quote_rel_def (R : L.Rel k) : (GoedelQuote.quote R : V) = ↑(Encodable.encode R) :=
  rfl


-- @@ L139-144 expanded
lemma codeIn_func_quote_iff {k x : ℕ} :
    (L.codeIn V).Func k x ↔ ∃ f : L.Func k, Encodable.encode f = x :=
  have : (Evalbm V ![k, x]) L.lDef.func.val ↔ (Evalbm ℕ ![k, x]) L.lDef.func.val := by
    simpa [Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
      models_iff_of_Sigma0 (V := V) (σ := L.lDef.func.val) (by simp) (e := ![k, x])
  Iff.trans this <| Iff.trans (DefinableLanguage.func_iff.symm) <| (by simp)


-- @@ L146-151 expanded
lemma codeIn_rel_quote_iff {k x : ℕ} :
    (L.codeIn V).Rel k x ↔ ∃ R : L.Rel k, Encodable.encode R = x :=
  have : (Evalbm V ![k, x]) L.lDef.rel.val ↔ (Evalbm ℕ ![k, x]) L.lDef.rel.val := by
    simpa [Matrix.comp_vecCons', Matrix.constant_eq_singleton] using
      models_iff_of_Sigma0 (V := V) (σ := L.lDef.rel.val) (by simp) (e := ![k, x])
  Iff.trans this <| Iff.trans (DefinableLanguage.rel_iff.symm) <| (by simp [])


-- @@ L153-154 expanded
@[simp]
lemma codeIn_func_quote {k : ℕ} (f : L.Func k) : (L.codeIn V).Func k (GoedelQuote.quote f) :=
  (codeIn_func_quote_iff (V := V)).mpr ⟨f, rfl⟩


-- @@ L156-157 expanded
@[simp]
lemma codeIn_rel_quote {k : ℕ} (r : L.Rel k) : (L.codeIn V).Rel k (GoedelQuote.quote r) :=
  (codeIn_rel_quote_iff (V := V)).mpr ⟨r, rfl⟩


-- @@ L159-161 expanded
omit [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L] in
@[simp]
lemma quote_func_inj (f₁ f₂ : L.Func k) :
    (GoedelQuote.quote f₁ : V) = (GoedelQuote.quote f₂ : V) ↔ f₁ = f₂ := by simp [quote_func_def]


-- @@ L163-165 expanded
omit [(k : ℕ) → Encodable (L.Func k)] [DefinableLanguage L] in
@[simp]
lemma quote_rel_inj (R₁ R₂ : L.Rel k) :
    (GoedelQuote.quote R₁ : V) = (GoedelQuote.quote R₂ : V) ↔ R₁ = R₂ := by simp [quote_rel_def]


-- @@ L167-169 expanded
omit [(k : ℕ) → Encodable (L.Rel k)] [DefinableLanguage L] in
@[simp]
lemma coe_quote_func_nat (f : L.Func k) :
    ((GoedelQuote.quote f : ℕ) : V) = (GoedelQuote.quote f : V) := by simp [quote_func_def]


-- @@ L171-173 expanded
omit [(k : ℕ) → Encodable (L.Func k)] [DefinableLanguage L] in
@[simp]
lemma coe_quote_rel_nat (R : L.Rel k) :
    ((GoedelQuote.quote R : ℕ) : V) = (GoedelQuote.quote R : V) := by simp [quote_rel_def]


-- @@ L175-175 verbatim
end «lp_section_2»


-- @@ L177-192 expanded
/-- TODO: move to Basic/Syntax/Language.lean -/
lemma _root_.LO.FirstOrder.Language.ORing.of_mem_range_encode_func {k f : ℕ} :
    f ∈ Set.range (Encodable.encode : FirstOrder.Language.Func oRing k → ℕ) ↔
      (k = 0 ∧ f = 0) ∨ (k = 0 ∧ f = 1) ∨ (k = 2 ∧ f = 0) ∨ (k = 2 ∧ f = 1) :=
  by
  constructor
  · rintro ⟨f, rfl⟩
    match k, f with
    | 0, Language.ORing.Func.zero => simp; rfl
    | 0, Language.ORing.Func.one => simp; rfl
    | 2, Language.ORing.Func.add => simp; rfl
    | 2, Language.ORing.Func.mul => simp; rfl
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Language.ORing.Func.zero, rfl⟩
    · exact ⟨Language.ORing.Func.one, rfl⟩
    · exact ⟨Language.ORing.Func.add, rfl⟩
    · exact ⟨Language.ORing.Func.mul, rfl⟩


-- @@ L194-205 expanded
/-- TODO: move to Basic/Syntax/Language.lean -/
lemma _root_.LO.FirstOrder.Language.ORing.of_mem_range_encode_rel {k r : ℕ} :
    r ∈ Set.range (Encodable.encode : FirstOrder.Language.Rel oRing k → ℕ) ↔
      (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1) :=
  by
  constructor
  · rintro ⟨r, rfl⟩
    match k, r with
    | 2, Language.ORing.Rel.eq => simp; rfl
    | 2, Language.ORing.Rel.lt => simp; rfl
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Language.ORing.Rel.eq, rfl⟩
    · exact ⟨Language.ORing.Rel.lt, rfl⟩


-- @@ L207-212 expanded
instance : DefinableLanguage oRing
    where
  func :=
    .mkSigma
      (Vee.vee
        (Wedge.wedge (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 0])
          (Semiformula.Operator.operator Operator.Eq.eq ![#1, Semiterm.numeral 0]))
        (Vee.vee
          (Wedge.wedge (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 0])
            (Semiformula.Operator.operator Operator.Eq.eq ![#1, Semiterm.numeral 1]))
          (Vee.vee
            (Wedge.wedge (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 2])
              (Semiformula.Operator.operator Operator.Eq.eq ![#1, Semiterm.numeral 0]))
            (Wedge.wedge (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 2])
              (Semiformula.Operator.operator Operator.Eq.eq ![#1, Semiterm.numeral 1])))))
      (by simp)
  rel :=
    .mkSigma
      (Vee.vee
        (Wedge.wedge (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 2])
          (Semiformula.Operator.operator Operator.Eq.eq ![#1, Semiterm.numeral 0]))
        (Wedge.wedge (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 2])
          (Semiformula.Operator.operator Operator.Eq.eq ![#1, Semiterm.numeral 1])))
      (by simp)
  func_iff {k c} := by exact Language.ORing.of_mem_range_encode_func
  rel_iff {k c} := by exact Language.ORing.of_mem_range_encode_rel


-- @@ L214-214 verbatim
namespace Formalized


-- @@ L216-216 expanded
variable {V : Type*} [ORingStruc V] [ModelsTheory V (iSigma 1)]


-- @@ L218-219 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev LOR : Arith.Language V :=
  Language.codeIn oRing V


-- @@ L221-222 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Arith.Formalized.LOR.code : LDef :=
  Language.lDef oRing


-- @@ L224-225 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "⌜ℒₒᵣ⌝" => LOR


-- @@ L227-228 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "⌜ℒₒᵣ⌝[" V "]" => LOR (V := V)


-- @@ L230-231 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation "p⌜ℒₒᵣ⌝" => LOR.code


-- @@ L233-233 verbatim
variable (V)


-- @@ L235-237 expanded
instance _root_.LO.Arith.Formalized.LOR.defined :
    (LOR : Arith.Language V).Defined (Language.lDef oRing) :=
  inferInstance


-- @@ L239-239 verbatim
variable {V}


-- @@ L241-242 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def zeroIndex : ℕ :=
  Encodable.encode (Language.Zero.zero : (oRing : FirstOrder.Language).Func 0)


-- @@ L244-245 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def oneIndex : ℕ :=
  Encodable.encode (Language.One.one : (oRing : FirstOrder.Language).Func 0)


-- @@ L247-248 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def addIndex : ℕ :=
  Encodable.encode (Language.Add.add : (oRing : FirstOrder.Language).Func 2)


-- @@ L250-251 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def mulIndex : ℕ :=
  Encodable.encode (Language.Mul.mul : (oRing : FirstOrder.Language).Func 2)


-- @@ L253-254 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def eqIndex : ℕ :=
  Encodable.encode (Language.Eq.eq : (oRing : FirstOrder.Language).Rel 2)


-- @@ L256-257 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ltIndex : ℕ :=
  Encodable.encode (Language.LT.lt : (oRing : FirstOrder.Language).Rel 2)


-- @@ L259-260 expanded
@[simp]
lemma LOR_func_zeroIndex : LOR.Func 0 (zeroIndex : V) :=
  codeIn_func_quote (V := V) (L := oRing) Language.Zero.zero


-- @@ L261-262 expanded
@[simp]
lemma LOR_func_oneIndex : LOR.Func 0 (oneIndex : V) :=
  codeIn_func_quote (V := V) (L := oRing) Language.One.one


-- @@ L263-264 expanded
@[simp]
lemma LOR_func_addIndex : LOR.Func 2 (addIndex : V) :=
  codeIn_func_quote (V := V) (L := oRing) Language.Add.add


-- @@ L265-266 expanded
@[simp]
lemma LOR_func_mulIndex : LOR.Func 2 (mulIndex : V) :=
  codeIn_func_quote (V := V) (L := oRing) Language.Mul.mul


-- @@ L267-268 expanded
@[simp]
lemma LOR_rel_eqIndex : LOR.Rel 2 (eqIndex : V) :=
  codeIn_rel_quote (V := V) (L := oRing) Language.Eq.eq


-- @@ L269-270 expanded
@[simp]
lemma LOR_rel_ltIndex : LOR.Rel 2 (ltIndex : V) :=
  codeIn_rel_quote (V := V) (L := oRing) Language.LT.lt


-- @@ L272-275 expanded
lemma _root_.LO.Arith.Formalized.lDef.func_def :
    (oRing).lDef.func =
      .mkSigma
        (Vee.vee
          (Wedge.wedge (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 0])
            (Semiformula.Operator.operator Operator.Eq.eq ![#1, Semiterm.numeral 0]))
          (Vee.vee
            (Wedge.wedge (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 0])
              (Semiformula.Operator.operator Operator.Eq.eq ![#1, Semiterm.numeral 1]))
            (Vee.vee
              (Wedge.wedge (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 2])
                (Semiformula.Operator.operator Operator.Eq.eq ![#1, Semiterm.numeral 0]))
              (Wedge.wedge (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 2])
                (Semiformula.Operator.operator Operator.Eq.eq ![#1, Semiterm.numeral 1])))))
        (by simp) :=
  rfl


-- @@ L277-277 verbatim
lemma coe_zeroIndex_eq : (zeroIndex : V) = 0 := rfl


-- @@ L279-279 verbatim
lemma coe_oneIndex_eq : (oneIndex : V) = 1 := by simp [oneIndex]; rfl


-- @@ L281-281 verbatim
lemma coe_addIndex_eq : (addIndex : V) = 0 := rfl


-- @@ L283-283 verbatim
lemma coe_mulIndex_eq : (mulIndex : V) = 1 := by simp [mulIndex]; rfl


-- @@ L285-289 expanded
lemma func_iff {k f : V} :
    LOR.Func k f ↔
      (k = 0 ∧ f = zeroIndex) ∨
        (k = 0 ∧ f = oneIndex) ∨ (k = 2 ∧ f = addIndex) ∨ (k = 2 ∧ f = mulIndex) :=
  by
  simp [FirstOrder.Language.codeIn_func_def, lDef.func_def, coe_zeroIndex_eq, coe_oneIndex_eq,
    coe_addIndex_eq, coe_mulIndex_eq]


-- @@ L291-291 verbatim
end Formalized


-- @@ L293-293 verbatim
end Arith

-- @@ L294-294 verbatim
end LO


-- @@ L296-296 verbatim
end «lp_nc_section_1»
