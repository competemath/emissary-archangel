module

public import Foundation.Logic.LogicSymbol
public import Mathlib.Logic.Encodable.Basic


-- @@ L6-7 verbatim
@[expose]
public section


-- @@ L9-9 verbatim
namespace FFL.Propositional


-- @@ L11-11 verbatim
variable {α : Type*}


-- @@ L13-19 verbatim
inductive Formula (α : Type u) : Type u
  | atom   : α → Formula α
  | falsum : Formula α
  | and    : Formula α → Formula α → Formula α
  | or     : Formula α → Formula α → Formula α
  | imp    : Formula α → Formula α → Formula α
  deriving DecidableEq


-- @@ L21-21 verbatim
abbrev FormulaSet (α) := Set (Formula α)


-- @@ L23-23 verbatim
abbrev FormulaFinset (α) := Finset (Formula α)


-- @@ L25-25 verbatim
variable {φ ψ φ₁ ψ₁ φ₂ ψ₂ : Formula α}



-- @@ L28-28 verbatim
namespace Formula


-- @@ L30-30 verbatim
prefix:max "#" => Formula.atom


-- @@ L32-32 verbatim
abbrev neg (φ : Formula α) : Formula α := imp φ falsum


-- @@ L34-34 verbatim
abbrev verum : Formula α := imp falsum falsum


-- @@ L36-40 verbatim
instance : LogicalConnective (Formula α) where
  arrow := imp
  wedge := and
  vee := or
  tilde := neg


-- @@ L42-44 verbatim
instance : LogicalNeutral (Formula α) where
  top := verum
  bot := falsum


-- @@ L46-46 verbatim
instance : FFL.NegAbbrev (Formula α) := by tauto;


-- @@ L48-48 verbatim
section ToString


-- @@ L50-50 verbatim
variable [ToString α]


-- @@ L52-59 verbatim
def toStr : Formula α → String
  | ⊤       => "\\top"
  | ⊥       => "\\bot"
  | atom a  => "{" ++ toString a ++ "}"
  | ∼φ      => "\\lnot " ++ toStr φ
  | φ ⋏ ψ   => "\\left(" ++ toStr φ ++ " \\land " ++ toStr ψ ++ "\\right)"
  | φ ⋎ ψ   => "\\left(" ++ toStr φ ++ " \\lor "  ++ toStr ψ ++ "\\right)"
  | φ 🡒 ψ   => "\\left(" ++ toStr φ ++ " \\rightarrow " ++ toStr ψ ++ "\\right)"


-- @@ L61-61 verbatim
instance : Repr (Formula α) := ⟨fun t _ => toStr t⟩

-- @@ L62-62 verbatim
instance : ToString (Formula α) := ⟨toStr⟩


-- @@ L64-73 verbatim
end ToString

lemma and_inj : φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := Iff.of_eq <| and.injEq _ _ _ _
lemma or_inj : φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := Iff.of_eq <| or.injEq _ _ _ _
lemma imp_inj : φ₁ 🡒 φ₂ = ψ₁ 🡒 ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := Iff.of_eq <| imp.injEq _ _ _ _
lemma neg_inj : ∼φ = ∼ψ ↔ φ = ψ := by simp [NegAbbrev.neg, imp_inj]

lemma neg_def : ∼φ = φ 🡒 ⊥ := rfl
lemma top_def : (⊤ : Formula α) = ⊥ 🡒 ⊥ := rfl
lemma iff_def (φ ψ : Formula α) : φ 🡘 ψ = (φ 🡒 ψ) ⋏ (ψ 🡒 φ) := by rfl



-- @@ L76-82 verbatim
@[grind]
def complexity : Formula α → ℕ
| atom _  => 0
| ⊥       => 0
| φ 🡒 ψ  => max φ.complexity ψ.complexity + 1
| φ ⋏ ψ   => max φ.complexity ψ.complexity + 1
| φ ⋎ ψ   => max φ.complexity ψ.complexity + 1


-- @@ L84-84 verbatim
@[simp, grind =] lemma complexity_bot : (⊥ : Formula α).complexity = 0 := rfl

-- @@ L85-85 verbatim
@[simp, grind =] lemma complexity_atom : (atom a).complexity = 0 := rfl

-- @@ L86-86 verbatim
@[simp, grind =] lemma complexity_imp : complexity (φ 🡒 ψ) = max φ.complexity ψ.complexity + 1 := rfl

-- @@ L87-87 verbatim
@[simp, grind =] lemma complexity_and : complexity (φ ⋏ ψ) = max φ.complexity ψ.complexity + 1 := rfl

-- @@ L88-88 verbatim
@[simp, grind =] lemma complexity_or : complexity (φ ⋎ ψ) = max φ.complexity ψ.complexity + 1 := rfl



-- @@ L91-103 verbatim
@[elab_as_elim]
def cases' {C : Formula α → Sort w}
    (hfalsum : C ⊥)
    (hatom   : ∀ a : α, C (atom a))
    (himp    : ∀ (φ ψ : Formula α), C (φ 🡒 ψ))
    (hand    : ∀ (φ ψ : Formula α), C (φ ⋏ ψ))
    (hor     : ∀ (φ ψ : Formula α), C (φ ⋎ ψ))
    : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | φ 🡒 ψ   => himp φ ψ
  | φ ⋏ ψ   => hand φ ψ
  | φ ⋎ ψ   => hor φ ψ


-- @@ L105-117 verbatim
@[induction_eliminator]
def rec' {C : Formula α → Sort w}
  (hfalsum : C ⊥)
  (hatom   : ∀ a : α, C (atom a))
  (himp    : ∀ (φ ψ : Formula α), C φ → C ψ → C (φ 🡒 ψ))
  (hand    : ∀ (φ ψ : Formula α), C φ → C ψ → C (φ ⋏ ψ))
  (hor     : ∀ (φ ψ : Formula α), C φ → C ψ → C (φ ⋎ ψ))
  : (φ : Formula α) → C φ
  | ⊥       => hfalsum
  | atom a  => hatom a
  | φ 🡒 ψ  => himp φ ψ (rec' hfalsum hatom himp hand hor φ) (rec' hfalsum hatom himp hand hor ψ)
  | φ ⋏ ψ   => hand φ ψ (rec' hfalsum hatom himp hand hor φ) (rec' hfalsum hatom himp hand hor ψ)
  | φ ⋎ ψ   => hor φ ψ (rec' hfalsum hatom himp hand hor φ) (rec' hfalsum hatom himp hand hor ψ)


-- @@ L119-119 verbatim
section Decidable


-- @@ L121-121 verbatim
variable [DecidableEq α]


-- @@ L123-156 verbatim
def hasDecEq : (φ ψ : Formula α) → Decidable (φ = ψ)
  | ⊥, ψ => by
    cases ψ using cases' <;>
    { simp only [reduceCtorEq]; try { exact isFalse not_false }; try { exact isTrue trivial } }
  | atom a, ψ => by
    cases ψ using cases' <;> try { simp only [reduceCtorEq]; exact isFalse not_false }
    simp only [atom.injEq]; exact decEq _ _
  | φ 🡒 ψ, χ => by
    cases χ using cases' <;> try { simp only [reduceCtorEq]; exact isFalse not_false }
    case himp φ' ψ' =>
      exact match hasDecEq φ φ' with
      | isTrue hp =>
        match hasDecEq ψ ψ' with
        | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
        | isFalse hq => isFalse (by simp [hp, hq, imp_inj])
      | isFalse hp => isFalse (by simp [hp, imp_inj])
  | φ ⋏ ψ, χ => by
    cases χ using cases' <;> try { simp only [reduceCtorEq]; exact isFalse not_false }
    case hand φ' ψ' =>
      exact match hasDecEq φ φ' with
      | isTrue hp =>
        match hasDecEq ψ ψ' with
        | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
        | isFalse hq => isFalse (by simp [hp, hq, and_inj])
      | isFalse hp => isFalse (by simp [hp, and_inj])
  | φ ⋎ ψ, χ => by
    cases χ using cases' <;> try { simp only [reduceCtorEq]; exact isFalse not_false }
    case hor φ' ψ' =>
      exact match hasDecEq φ φ' with
      | isTrue hp =>
        match hasDecEq ψ ψ' with
        | isTrue hq  => isTrue (hp ▸ hq ▸ rfl)
        | isFalse hq => isFalse (by simp [hp, hq, or_inj])
      | isFalse hp => isFalse (by simp [hp, or_inj])


-- @@ L158-158 verbatim
instance : DecidableEq (Formula α) := hasDecEq


-- @@ L160-160 verbatim
end Decidable


-- @@ L162-162 verbatim
section Encodable


-- @@ L164-164 verbatim
variable [Encodable α]

-- @@ L165-165 verbatim
open Encodable


-- @@ L167-172 verbatim
def toNat : Formula α → ℕ
  | ⊥       => (Nat.pair 0 0) + 1
  | atom a  => (Nat.pair 1 <| encode a) + 1
  | φ 🡒 ψ   => (Nat.pair 2 <| φ.toNat.pair ψ.toNat) + 1
  | φ ⋏ ψ   => (Nat.pair 3 <| φ.toNat.pair ψ.toNat) + 1
  | φ ⋎ ψ   => (Nat.pair 4 <| φ.toNat.pair ψ.toNat) + 1


-- @@ L174-210 verbatim
def ofNat : ℕ → Option (Formula α)
  | 0 => none
  | e + 1 =>
    let idx := e.unpair.1
    let c := e.unpair.2
    match idx with
    | 0 => some ⊥
    | 1 => (decode c).map Formula.atom
    | 2 =>
      have : c.unpair.1 < e + 1 := Nat.lt_succ_iff.mpr $ le_trans (Nat.unpair_left_le _) $ Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 := Nat.lt_succ_iff.mpr $ le_trans (Nat.unpair_right_le _) $ Nat.unpair_right_le _
      do
        let φ <- ofNat c.unpair.1
        let ψ <- ofNat c.unpair.2
        return φ 🡒 ψ
    | 3 =>
      have : c.unpair.1 < e + 1 := Nat.lt_succ_iff.mpr $ le_trans (Nat.unpair_left_le _) $ Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 := Nat.lt_succ_iff.mpr $ le_trans (Nat.unpair_right_le _) $ Nat.unpair_right_le _
      do
        let φ <- ofNat c.unpair.1
        let ψ <- ofNat c.unpair.2
        return φ ⋏ ψ
    | 4 =>
      have : c.unpair.1 < e + 1 := Nat.lt_succ_iff.mpr $ le_trans (Nat.unpair_left_le _) $ Nat.unpair_right_le _
      have : c.unpair.2 < e + 1 := Nat.lt_succ_iff.mpr $ le_trans (Nat.unpair_right_le _) $ Nat.unpair_right_le _
      do
        let φ <- ofNat c.unpair.1
        let ψ <- ofNat c.unpair.2
        return φ ⋎ ψ
    | _ => none

lemma ofNat_toNat : ∀ (φ : Formula α), ofNat (toNat φ) = some φ
  | atom a  => by simp [toNat, ofNat, Nat.unpair_pair, encodek];
  | ⊥       => by simp [toNat, ofNat]
  | φ 🡒 ψ   => by simp [toNat, ofNat, ofNat_toNat φ, ofNat_toNat ψ]
  | φ ⋏ ψ   => by simp [toNat, ofNat, ofNat_toNat φ, ofNat_toNat ψ]
  | φ ⋎ ψ   => by simp [toNat, ofNat, ofNat_toNat φ, ofNat_toNat ψ]


-- @@ L212-215 verbatim
instance : Encodable (Formula α) where
  encode := toNat
  decode := ofNat
  encodek := ofNat_toNat


-- @@ L217-217 verbatim
end Encodable



-- @@ L220-220 verbatim
section Letterless


-- @@ L222-228 verbatim
@[grind]
def Letterless : Formula α → Prop
  | .atom _ => False
  | ⊥ => True
  | φ 🡒 ψ => (φ.Letterless) ∧ (ψ.Letterless)
  | φ ⋏ ψ => (φ.Letterless) ∧ (ψ.Letterless)
  | φ ⋎ ψ => (φ.Letterless) ∧ (ψ.Letterless)


-- @@ L230-230 verbatim
attribute [grind =] NegAbbrev.neg


-- @@ L232-232 verbatim
@[grind .] lemma not_letterless_atom {a : α} : ¬(Formula.Letterless (.atom a)) := by grind;

-- @@ L233-233 verbatim
@[grind .] lemma letterless_falsum : (⊥ : Formula α).Letterless := by simp [Letterless];

-- @@ L234-234 verbatim
@[grind .] lemma letterless_verum : (⊤ : Formula α).Letterless := by simp [Letterless];

-- @@ L235-235 verbatim
@[grind =] lemma letterless_imp {φ ψ : Formula α} : (φ 🡒 ψ).Letterless ↔ φ.Letterless ∧ ψ.Letterless := by simp [Letterless];

-- @@ L236-236 verbatim
@[grind =] lemma letterless_and : (φ ⋏ ψ).Letterless ↔ φ.Letterless ∧ ψ.Letterless := by simp [Letterless];

-- @@ L237-237 verbatim
@[grind =] lemma letterless_or : (φ ⋎ ψ).Letterless ↔ φ.Letterless ∧ ψ.Letterless := by simp [Letterless];

-- @@ L238-238 verbatim
@[grind =] lemma letterless_neg : (∼φ).Letterless ↔ φ.Letterless ∧ (⊥ : Formula α).Letterless := by grind;


-- @@ L240-240 verbatim
end Letterless


-- @@ L242-242 verbatim
end Formula



-- @@ L245-245 verbatim
section Subformula


-- @@ L247-247 verbatim
variable [DecidableEq α]


-- @@ L249-255 verbatim
@[grind]
def Formula.subformulas : Formula α → Finset (Formula α)
  | ⊥      => {⊥}
  | atom a => {atom a}
  | φ 🡒 ψ  => insert (φ 🡒 ψ) (φ.subformulas ∪ ψ.subformulas)
  | φ ⋏ ψ  => insert (φ ⋏ ψ) (φ.subformulas ∪ ψ.subformulas)
  | φ ⋎ ψ  => insert (φ ⋎ ψ) (φ.subformulas ∪ ψ.subformulas)


-- @@ L257-257 verbatim
namespace Formula.subformulas


-- @@ L259-259 verbatim
variable {φ ψ χ : Formula α}


-- @@ L261-261 verbatim
@[simp, grind .] lemma mem_self : φ ∈ φ.subformulas := by induction φ <;> simp [subformulas];


-- @@ L263-263 verbatim
@[grind ⇒]

-- @@ L264-271 verbatim
protected lemma mem_imp (h : (ψ 🡒 χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∧ χ ∈ φ.subformulas := by
  induction φ with
  | himp =>
    simp_all only [subformulas, Finset.mem_insert, imp_inj, Finset.mem_union];
    rcases h with ⟨_⟩ | ⟨⟨_⟩ | ⟨_⟩⟩ <;> simp_all;
  | hor => simp_all only [subformulas, Finset.mem_insert, Finset.mem_union]; tauto;
  | hand => simp_all only [subformulas, Finset.mem_insert, Finset.mem_union]; tauto;
  | _ => simp_all [subformulas];


-- @@ L273-273 verbatim
@[grind! =>]

-- @@ L274-281 verbatim
protected lemma mem_and (h : (ψ ⋏ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∧ χ ∈ φ.subformulas := by
  induction φ with
  | himp => simp_all only [subformulas, Finset.mem_insert, Finset.mem_union]; tauto;
  | hor => simp_all only [subformulas, Finset.mem_insert, Finset.mem_union]; tauto;
  | hand =>
    simp_all only [subformulas, Finset.mem_insert, Finset.mem_union, and_inj];
    rcases h with ⟨_⟩ | ⟨⟨_⟩ | ⟨_⟩⟩ <;> simp_all;
  | _ => simp_all [subformulas];


-- @@ L283-283 verbatim
@[grind! =>]

-- @@ L284-291 verbatim
protected lemma mem_or (h : (ψ ⋎ χ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∧ χ ∈ φ.subformulas := by
  induction φ with
  | himp => simp_all only [subformulas, Finset.mem_insert, Finset.mem_union]; tauto;
  | hor =>
    simp_all only [subformulas, Finset.mem_insert, Finset.mem_union, or_inj];
    rcases h with ⟨_⟩ | ⟨⟨_⟩ | ⟨_⟩⟩ <;> simp_all;
  | hand => simp_all only [subformulas, Finset.mem_insert, Finset.mem_union]; tauto;
  | _ => simp_all [subformulas];


-- @@ L293-293 verbatim
@[grind! =>]

-- @@ L294-296 verbatim
protected lemma mem_neg (h : (∼ψ) ∈ φ.subformulas) : ψ ∈ φ.subformulas ∧ ⊥ ∈ φ.subformulas := by
  rw [neg_def] at h;
  grind;


-- @@ L298-298 verbatim
example {_ : φ ∈ φ.subformulas} : φ ∈ φ.subformulas := by grind;

-- @@ L299-299 verbatim
example {_ : ψ 🡒 χ ∈ φ.subformulas} : ψ ∈ φ.subformulas := by grind

-- @@ L300-300 verbatim
example {_ : ψ 🡒 χ ∈ φ.subformulas} : χ ∈ φ.subformulas := by grind

-- @@ L301-301 verbatim
example {_ : ∼ψ ∈ φ.subformulas} : ψ ∈ φ.subformulas := by grind;

-- @@ L302-302 verbatim
example {_ : ∼ψ ∈ φ.subformulas} : ⊥ ∈ φ.subformulas := by grind;

-- @@ L303-303 verbatim
example {_ : ψ ⋏ χ ∈ φ.subformulas} : ψ ∈ φ.subformulas := by grind

-- @@ L304-304 verbatim
example {_ : ψ ⋎ χ ∈ φ.subformulas} : ψ ∈ φ.subformulas := by grind

-- @@ L305-305 verbatim
example {_ : ψ 🡒 χ ∈ φ.subformulas} : χ ∈ φ.subformulas := by grind

-- @@ L306-306 verbatim
example {_ : ψ ⋏ (ψ ⋎ (χ 🡒 ξ)) ∈ φ.subformulas} : χ ∈ φ.subformulas := by grind;


-- @@ L308-308 verbatim
end Formula.subformulas



-- @@ L311-312 verbatim
class FormulaFinset.SubformulaClosed (Γ : FormulaFinset α) where
  closed : ∀ φ ∈ Γ, φ.subformulas ⊆ Γ


-- @@ L314-314 verbatim
namespace FormulaFinset.SubformulaClosed


-- @@ L316-316 verbatim
variable {φ ψ χ : Formula α} {Γ : FormulaFinset α} [Γ.SubformulaClosed]


-- @@ L318-318 verbatim
@[grind ⇒] lemma mem_and₁ (h : φ ⋏ ψ ∈ Γ) : φ ∈ Γ := by apply SubformulaClosed.closed _ h; simp [Formula.subformulas];

-- @@ L319-319 verbatim
@[grind ⇒] lemma mem_and₂ (h : φ ⋏ ψ ∈ Γ) : ψ ∈ Γ := by apply SubformulaClosed.closed _ h; simp [Formula.subformulas];

-- @@ L320-320 verbatim
@[grind ⇒] lemma mem_or₁ (h : φ ⋎ ψ ∈ Γ) : φ ∈ Γ := by apply SubformulaClosed.closed _ h; simp [Formula.subformulas];

-- @@ L321-321 verbatim
@[grind ⇒] lemma mem_or₂ (h : φ ⋎ ψ ∈ Γ) : ψ ∈ Γ := by apply SubformulaClosed.closed _ h; simp [Formula.subformulas];

-- @@ L322-322 verbatim
@[grind ⇒] lemma mem_imp₁ (h : φ 🡒 ψ ∈ Γ) : φ ∈ Γ := by apply SubformulaClosed.closed _ h; simp [Formula.subformulas];

-- @@ L323-323 verbatim
@[grind ⇒] lemma mem_imp₂ (h : φ 🡒 ψ ∈ Γ) : ψ ∈ Γ := by apply SubformulaClosed.closed _ h; simp [Formula.subformulas];


-- @@ L325-359 verbatim
instance subformulaClosed_subformulas {φ : Formula α} : SubformulaClosed (φ.subformulas) := ⟨by
  induction φ with
  | hatom => simp [Formula.subformulas];
  | hfalsum => simp [Formula.subformulas];
  | himp φ ψ ihφ ihψ =>
    rintro ξ hξ;
    rcases (by simpa [Formula.subformulas] using hξ) with (rfl | hξ | hξ);
    . tauto;
    . trans φ.subformulas;
      . exact ihφ _ hξ;
      . intro; simp_all [Formula.subformulas];
    . trans ψ.subformulas;
      . exact ihψ _ hξ;
      . intro; simp_all [Formula.subformulas];
  | hand φ ψ ihφ ihψ =>
    rintro ξ hξ;
    rcases (by simpa [Formula.subformulas] using hξ) with (rfl | hξ | hξ);
    . tauto;
    . trans φ.subformulas;
      . exact ihφ _ hξ;
      . intro; simp_all [Formula.subformulas];
    . trans ψ.subformulas;
      . exact ihψ _ hξ;
      . intro; simp_all [Formula.subformulas];
  | hor φ ψ ihφ ihψ =>
    rintro ξ hξ;
    rcases (by simpa [Formula.subformulas] using hξ) with (rfl | hξ | hξ);
    . tauto;
    . trans φ.subformulas;
      . exact ihφ _ hξ;
      . intro; simp_all [Formula.subformulas];
    . trans ψ.subformulas;
      . exact ihψ _ hξ;
      . intro; simp_all [Formula.subformulas];
⟩


-- @@ L361-361 verbatim
end FormulaFinset.SubformulaClosed



-- @@ L364-365 verbatim
class FormulaSet.SubformulaClosed (T : FormulaSet α) where
  closed : ∀ φ ∈ T, ↑φ.subformulas ⊆ T



-- @@ L368-368 verbatim
namespace FormulaSet.SubformulaClosed


-- @@ L370-370 verbatim
variable {φ ψ χ : Formula α} {T : FormulaSet α} [T.SubformulaClosed]


-- @@ L372-372 verbatim
@[grind ⇒] 
-- @@ L372-372 verbatim
protected lemma mem_and₁ (h : φ ⋏ ψ ∈ T) : φ ∈ T := by apply closed _ h; simp [Formula.subformulas];

-- @@ L373-373 verbatim
@[grind ⇒] 
-- @@ L373-373 verbatim
protected lemma mem_and₂ (h : φ ⋏ ψ ∈ T) : ψ ∈ T := by apply closed _ h; simp [Formula.subformulas];

-- @@ L374-374 verbatim
@[grind ⇒] 
-- @@ L374-374 verbatim
protected lemma mem_or₁ (h : φ ⋎ ψ ∈ T) : φ ∈ T := by apply closed _ h; simp [Formula.subformulas];

-- @@ L375-375 verbatim
@[grind ⇒] 
-- @@ L375-375 verbatim
protected lemma mem_or₂ (h : φ ⋎ ψ ∈ T) : ψ ∈ T := by apply closed _ h; simp [Formula.subformulas];

-- @@ L376-376 verbatim
@[grind ⇒] 
-- @@ L376-376 verbatim
protected lemma mem_imp₁ (h : φ 🡒 ψ ∈ T) : φ ∈ T := by apply closed _ h; simp [Formula.subformulas];

-- @@ L377-377 verbatim
@[grind ⇒] 
-- @@ L377-377 verbatim
protected lemma mem_imp₂ (h : φ 🡒 ψ ∈ T) : ψ ∈ T := by apply closed _ h; simp [Formula.subformulas];


-- @@ L379-381 verbatim
instance {φ : Formula α} : SubformulaClosed φ.subformulas.toSet := ⟨by
  simpa using FormulaFinset.SubformulaClosed.subformulaClosed_subformulas (φ := φ) |>.closed;
⟩


-- @@ L383-383 verbatim
example {_ : φ ⋏ ψ ∈ T} : φ ∈ T := by grind

-- @@ L384-384 verbatim
example {_ : φ ⋏ ψ ∈ T} : ψ ∈ T := by grind

-- @@ L385-385 verbatim
example {_ : φ ⋎ ψ ∈ T} : φ ∈ T := by grind

-- @@ L386-386 verbatim
example {_ : φ ⋎ ψ ∈ T} : ψ ∈ T := by grind

-- @@ L387-387 verbatim
example {_ : φ 🡒 ψ ∈ T} : φ ∈ T := by grind

-- @@ L388-388 verbatim
example {_ : φ 🡒 ψ ∈ T} : ψ ∈ T := by grind


-- @@ L390-390 verbatim
end FormulaSet.SubformulaClosed


-- @@ L392-392 verbatim
end Subformula



-- @@ L395-395 verbatim
section Substitution


-- @@ L397-397 verbatim
abbrev Substitution (α) := α → (Formula α)


-- @@ L399-399 verbatim
abbrev Substitution.id {α} : Substitution α := λ a => .atom a


-- @@ L401-401 verbatim
namespace Formula


-- @@ L403-403 verbatim
variable {φ ψ : Formula α} {s : Substitution α}


-- @@ L405-410 verbatim
def subst (s : Substitution α) : Formula α → Formula α
  | atom a  => (s a)
  | ⊥       => ⊥
  | φ ⋏ ψ   => φ.subst s ⋏ ψ.subst s
  | φ ⋎ ψ   => φ.subst s ⋎ ψ.subst s
  | φ 🡒 ψ   => φ.subst s 🡒 ψ.subst s


-- @@ L412-421 verbatim
notation:80 φ "⟦" s "⟧" => Formula.subst s φ

lemma subst_atom {a} : (#a)⟦s⟧ = s a := rfl
lemma subst_bot : ⊥⟦s⟧ = ⊥ := rfl
lemma subst_top : ⊤⟦s⟧ = ⊤ := rfl
lemma subst_imp : (φ 🡒 ψ)⟦s⟧ = φ⟦s⟧ 🡒 ψ⟦s⟧ := rfl
lemma subst_neg : (∼φ)⟦s⟧ = ∼(φ⟦s⟧) := rfl
lemma subst_and : (φ ⋏ ψ)⟦s⟧ = φ⟦s⟧ ⋏ ψ⟦s⟧ := rfl
lemma subst_or : (φ ⋎ ψ)⟦s⟧ = φ⟦s⟧ ⋎ ψ⟦s⟧ := rfl
lemma subst_iff : (φ 🡘 ψ)⟦s⟧ = (φ⟦s⟧ 🡘 ψ⟦s⟧) := rfl


-- @@ L423-431 verbatim
attribute [simp, grind =>]
  subst_atom
  subst_bot
  subst_top
  subst_imp
  subst_neg
  subst_and
  subst_or
  subst_iff


-- @@ L433-434 verbatim
@[simp, grind =]
lemma subst_id {φ : Formula α} : φ⟦.id⟧ = φ := by induction φ <;> grind;


-- @@ L436-436 verbatim
end Formula



-- @@ L439-440 verbatim
@[grind]
def Substitution.comp (s₁ s₂ : Substitution α) : Substitution α := λ a => (s₁ a)⟦s₂⟧

-- @@ L441-441 verbatim
infixr:80 " ∘ " => Substitution.comp


-- @@ L443-445 verbatim
@[simp, grind =]
lemma Formula.subst_comp {s₁ s₂ : Substitution α} {φ : Formula α} : φ⟦s₁ ∘ s₂⟧ = φ⟦s₁⟧⟦s₂⟧ := by
  induction φ <;> grind;



-- @@ L448-448 verbatim
def ZeroSubstitution (α) := { s : Substitution α // ∀ {a : α}, (#a⟦s⟧).Letterless }

-- @@ L449-449 verbatim
instance : Coe (ZeroSubstitution α) (Substitution α) := ⟨Subtype.val⟩


-- @@ L451-455 verbatim
@[grind .]
lemma Formula.letterless_zeroSubst {s : ZeroSubstitution α} : (φ⟦s⟧).Letterless := by
  induction φ;
  case hatom => exact s.2;
  all_goals. simp_all [Formula.Letterless];


-- @@ L457-458 verbatim
class SubstitutionClosed (S : Set (Formula α)) where
  closed : ∀ φ ∈ S, (∀ s : Substitution α, φ⟦s⟧ ∈ S)


-- @@ L460-460 verbatim
end Substitution


-- @@ L462-462 verbatim
end FFL.Propositional


-- @@ L464-464 verbatim
end
