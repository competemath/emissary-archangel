module

public import Foundation.Propositional.Entailment.Cl
public import Foundation.Propositional.Logic.Basic
public import Foundation.Propositional.Formula.Basic


-- @@ L7-7 verbatim
@[expose] public section


-- @@ L9-9 verbatim
namespace FFL.Propositional


-- @@ L11-11 verbatim
variable {α : Type*}


-- @@ L13-15 verbatim
structure Hilbert (α) where
  schema : Set (Formula α)
  schema_closed : ∀ φ ∈ schema, ∀ s, φ⟦s⟧ ∈ schema


-- @@ L17-17 verbatim
namespace Hilbert


-- @@ L19-21 verbatim
instance : SetLike (Hilbert α) (Formula α) where
  coe := Hilbert.schema
  coe_injective := by intro ⟨A, hA⟩ ⟨B, hB⟩ h; simpa;


-- @@ L23-23 verbatim
protected def Min : Hilbert α := ⟨∅, by tauto⟩

-- @@ L24-24 verbatim
protected def Int : Hilbert α := ⟨{ Axioms.EFQ φ | φ }, by grind⟩

-- @@ L25-28 verbatim
protected def Cl : Hilbert α := ⟨
  { Axioms.EFQ φ | φ } ∪ { Axioms.LEM φ | φ },
  by rintro φ (_ | _) <;> grind;
⟩


-- @@ L30-30 verbatim
@[simp, grind .] lemma Int_le_Cl : (Hilbert.Int : Hilbert α).schema ⊆ Hilbert.Cl.schema := by tauto;


-- @@ L32-32 verbatim
end Hilbert



-- @@ L35-46 verbatim
inductive HilbertProof (Λ : Hilbert α) : Formula α → Type _
| axm {φ}        : φ ∈ Λ → HilbertProof Λ φ
| mdp {φ ψ}      : HilbertProof Λ (φ 🡒 ψ) → HilbertProof Λ φ → HilbertProof Λ ψ
| verum          : HilbertProof Λ $ Axioms.Verum
| implyS {φ ψ χ} : HilbertProof Λ $ Axioms.ImplyS φ ψ χ
| implyK {φ ψ}   : HilbertProof Λ $ Axioms.ImplyK φ ψ
| andElimL {φ ψ} : HilbertProof Λ $ Axioms.AndElim₁ φ ψ
| andElimR {φ ψ} : HilbertProof Λ $ Axioms.AndElim₂ φ ψ
| andIntro {φ ψ} : HilbertProof Λ $ Axioms.AndInst φ ψ
| orIntroL {φ ψ} : HilbertProof Λ $ Axioms.OrInst₁ φ ψ
| orIntroR {φ ψ} : HilbertProof Λ $ Axioms.OrInst₂ φ ψ
| orElim {φ ψ χ} : HilbertProof Λ $ Axioms.OrElim φ ψ χ


-- @@ L48-48 verbatim
instance : Entailment (Hilbert α) (Formula α) := ⟨HilbertProof⟩


-- @@ L50-50 verbatim
namespace Hilbert


-- @@ L52-52 verbatim
open HilbertProof


-- @@ L54-54 verbatim
variable (H : Hilbert α)


-- @@ L56-56 verbatim
instance : Entailment.ModusPonens H := ⟨mdp⟩

-- @@ L57-57 verbatim
instance : Entailment.HasAxiomImplyK H := ⟨implyK⟩

-- @@ L58-58 verbatim
instance : Entailment.HasAxiomImplyS H := ⟨implyS⟩

-- @@ L59-59 verbatim
instance : Entailment.HasAxiomAndInst H := ⟨andIntro⟩

-- @@ L60-66 verbatim
instance : Entailment.Minimal H where
  verum! := verum
  and₁! := andElimL
  and₂! := andElimR
  or₁! := orIntroL
  or₂! := orIntroR
  or₃! := orElim


-- @@ L68-70 verbatim
variable {H} {H₁ H₂ : Hilbert α}

alias ofSchema := HilbertProof.axm

-- @@ L71-71 verbatim
@[grind <=] lemma of_schema (h : φ ∈ H) : H ⊢ φ := ⟨ofSchema h⟩


-- @@ L73-86 verbatim
def ofLE (h : H₁.schema ⊆ H₂.schema) : H₁ ⊢! φ → H₂ ⊢! φ
  | axm h₁ => axm $ h h₁
  | mdp h₁ h₂ => mdp (ofLE h h₁) (ofLE h h₂)
  | verum => verum
  | implyS => implyS
  | implyK => implyK
  | andElimL => andElimL
  | andElimR => andElimR
  | andIntro => andIntro
  | orIntroL => orIntroL
  | orIntroR => orIntroR
  | orElim => orElim

lemma of_le (h : H₁.schema ⊆ H₂.schema) : H₁ ⊢ φ → H₂ ⊢ φ := λ ⟨hφ⟩ => ⟨ofLE h hφ⟩


-- @@ L88-89 verbatim
@[grind <=]
lemma weakerThan_of_le (h : H₁.schema ⊆ H₂.schema) : H₁ ⪯ H₂ := Entailment.weakerThan_iff.mpr $ of_le h


-- @@ L91-104 verbatim
def Subst {H : Hilbert α} (s) : H ⊢! φ → H ⊢! φ⟦s⟧
  | axm h₁ => axm $ H.schema_closed φ h₁ s
  | mdp h₁ h₂ => mdp (Subst s h₁) (Subst s h₂)
  | verum => verum
  | implyS => implyS
  | implyK => implyK
  | andElimL => andElimL
  | andElimR => andElimR
  | andIntro => andIntro
  | orIntroL => orIntroL
  | orIntroR => orIntroR
  | orElim => orElim

lemma subst {H : Hilbert α} (s) : H ⊢ φ → H ⊢ φ⟦s⟧ := λ ⟨hφ⟩ => ⟨Subst s hφ⟩


-- @@ L106-121 verbatim
def ofProofSchema (h : H₂ ⊢!* H₁.schema) : H₁ ⊢! φ → H₂ ⊢! φ
  | axm h₁ => h h₁
  | mdp h₁ h₂ => mdp (ofProofSchema h h₁) (ofProofSchema h h₂)
  | verum => verum
  | implyS => implyS
  | implyK => implyK
  | andElimL => andElimL
  | andElimR => andElimR
  | andIntro => andIntro
  | orIntroL => orIntroL
  | orIntroR => orIntroR
  | orElim => orElim

lemma of_proof_schema (h : H₂ ⊢* H₁.schema) : H₁ ⊢ φ → H₂ ⊢ φ := λ ⟨hφ⟩ => ⟨ofProofSchema (fun _ hφ ↦ (h hφ).get) hφ⟩

lemma weakerThan_of_provable_schema (h : H₂ ⊢* H₁.schema) : H₁ ⪯ H₂ := Entailment.weakerThan_iff.mpr $ of_proof_schema h


-- @@ L123-123 verbatim
section


-- @@ L125-126 verbatim
instance : Entailment.Int (Hilbert.Int : Hilbert α) where
  efq! := axm $ by tauto


-- @@ L128-128 verbatim
instance : Entailment.HasAxiomEFQ (Hilbert.Cl : Hilbert α) := ⟨axm $ by tauto⟩

-- @@ L129-129 verbatim
instance : Entailment.HasAxiomLEM (Hilbert.Cl : Hilbert α) := ⟨axm $ by tauto⟩

-- @@ L130-130 verbatim
instance : Entailment.Int (Hilbert.Cl : Hilbert α) where

-- @@ L131-131 verbatim
instance [DecidableEq α] : Entailment.Cl (Hilbert.Cl : Hilbert α) where


-- @@ L133-133 verbatim
end


-- @@ L135-135 verbatim
end Hilbert



-- @@ L138-138 verbatim
namespace Hilbert


-- @@ L140-143 verbatim
abbrev logic (H : Hilbert α) : Logic α where
  logic := Entailment.theory H
  subst s {_} := Hilbert.subst s
  mdp := Entailment.mdp;


-- @@ L145-150 verbatim
variable {H : Hilbert α}

lemma mem_logic_of_proof (h : H ⊢! φ) : φ ∈ H.logic := ⟨h⟩

lemma mem_logic_of_provable (h : H ⊢ φ) : φ ∈ H.logic := mem_logic_of_proof h.get
lemma provable_of_mem_logic (h : φ ∈ H.logic) : H ⊢ φ := h


-- @@ L152-153 verbatim
@[grind =]
lemma iff_mem_logic_provable : H ⊢ φ ↔ φ ∈ H.logic := ⟨mem_logic_of_provable, provable_of_mem_logic⟩


-- @@ L155-155 verbatim
end Hilbert



-- @@ L158-158 verbatim
protected abbrev Int : Logic α := Hilbert.Int.logic

-- @@ L159-159 verbatim
protected abbrev Cl  : Logic α := Hilbert.Cl.logic


-- @@ L161-161 verbatim
end FFL.Propositional


-- @@ L163-163 verbatim
end
