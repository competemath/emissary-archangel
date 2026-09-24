module
public import Foundation.Propositional.Entailment.Int


-- @@ L4-4 verbatim
@[expose] public section


-- @@ L6-6 verbatim
namespace FFL.Axioms


-- @@ L8-8 verbatim
variable {F : Type*} [LogicalConnective F]

-- @@ L9-9 verbatim
variable (φ ψ χ : F)


-- @@ L11-11 verbatim
protected abbrev DNE := ∼∼φ 🡒 φ


-- @@ L13-13 verbatim
protected abbrev LEM := φ ⋎ ∼φ


-- @@ L15-15 verbatim
protected abbrev Peirce := ((φ 🡒 ψ) 🡒 φ) 🡒 φ


-- @@ L17-17 verbatim
protected abbrev ElimContra := (∼ψ 🡒 ∼φ) 🡒 (φ 🡒 ψ)


-- @@ L19-19 verbatim
end FFL.Axioms



-- @@ L22-22 verbatim
namespace FFL.Entailment


-- @@ L24-24 verbatim
variable {S F : Type*} [LogicalConnective F] [Entailment S F]

-- @@ L25-25 verbatim
variable {𝓢 : S} {φ ψ χ : F}


-- @@ L27-28 verbatim
class HasAxiomDNE (𝓢 : S)  where
  dne! {φ : F} : 𝓢 ⊢! Axioms.DNE φ

-- @@ L29-29 verbatim
export HasAxiomDNE (dne!)


-- @@ L31-31 verbatim
@[simp] lemma dne [HasAxiomDNE 𝓢] : 𝓢 ⊢ ∼∼φ 🡒 φ  := ⟨dne!⟩


-- @@ L33-33 verbatim
def of_NN! [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (b : 𝓢 ⊢! ∼∼φ) : 𝓢 ⊢! φ := dne! ⨀ b

-- @@ L34-34 verbatim
@[grind ⇒] lemma of_NN [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (h : 𝓢 ⊢ ∼∼φ) : 𝓢 ⊢ φ := ⟨of_NN! h.some⟩


-- @@ L36-36 verbatim
section


-- @@ L38-38 verbatim
variable [LogicalNeutral F] [Entailment.Minimal 𝓢]


-- @@ L40-40 verbatim
namespace FiniteContext


-- @@ L42-42 verbatim
instance [Entailment.HasAxiomDNE 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomDNE Γ := ⟨of! dne!⟩


-- @@ L44-44 verbatim
end FiniteContext



-- @@ L47-47 verbatim
namespace Context


-- @@ L49-49 verbatim
instance [Entailment.HasAxiomDNE 𝓢] (Γ : Context F 𝓢) : HasAxiomDNE Γ := ⟨of! dne!⟩


-- @@ L51-51 verbatim
end Context


-- @@ L53-53 verbatim
end



-- @@ L56-57 verbatim
class HasAxiomLEM (𝓢 : S)  where
  lem! {φ : F} : 𝓢 ⊢! Axioms.LEM φ

-- @@ L58-58 verbatim
export HasAxiomLEM (lem!)


-- @@ L60-60 verbatim
@[simp] lemma lem [HasAxiomLEM 𝓢] : 𝓢 ⊢ φ ⋎ ∼φ := ⟨lem!⟩



-- @@ L63-63 verbatim
section


-- @@ L65-65 verbatim
variable [LogicalNeutral F] [Entailment.Minimal 𝓢]


-- @@ L67-67 verbatim
namespace FiniteContext


-- @@ L69-69 verbatim
instance [Entailment.HasAxiomLEM 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomLEM Γ := ⟨of! lem!⟩


-- @@ L71-71 verbatim
end FiniteContext



-- @@ L74-74 verbatim
namespace Context


-- @@ L76-76 verbatim
instance [Entailment.HasAxiomLEM 𝓢] (Γ : Context F 𝓢) : HasAxiomLEM Γ := ⟨of! lem!⟩


-- @@ L78-78 verbatim
end Context


-- @@ L80-80 verbatim
end



-- @@ L83-84 verbatim
class HasAxiomPeirce (𝓢 : S)  where
  peirce! {φ ψ : F} : 𝓢 ⊢! Axioms.Peirce φ ψ

-- @@ L85-85 verbatim
export HasAxiomPeirce (peirce!)


-- @@ L87-87 verbatim
@[simp] lemma peirce [LogicalNeutral F] [HasAxiomPeirce 𝓢] : 𝓢 ⊢ ((φ 🡒 ψ) 🡒 φ) 🡒 φ := ⟨peirce!⟩



-- @@ L90-90 verbatim
section


-- @@ L92-92 verbatim
variable [LogicalNeutral F] [Entailment.Minimal 𝓢]


-- @@ L94-94 verbatim
namespace FiniteContext


-- @@ L96-96 verbatim
instance [Entailment.HasAxiomPeirce 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomPeirce Γ := ⟨of! peirce!⟩


-- @@ L98-98 verbatim
end FiniteContext



-- @@ L101-101 verbatim
namespace Context


-- @@ L103-103 verbatim
instance [Entailment.HasAxiomPeirce 𝓢] (Γ : Context F 𝓢) : HasAxiomPeirce Γ := ⟨of! peirce!⟩


-- @@ L105-105 verbatim
end Context


-- @@ L107-107 verbatim
end



-- @@ L110-111 verbatim
class HasAxiomElimContra (𝓢 : S)  where
  elimContra! {φ ψ : F} : 𝓢 ⊢! Axioms.ElimContra φ ψ

-- @@ L112-112 verbatim
export HasAxiomElimContra (elimContra!)


-- @@ L114-114 verbatim
@[simp] lemma elim_contra [HasAxiomElimContra 𝓢] : 𝓢 ⊢ (∼ψ 🡒 ∼φ) 🡒 (φ 🡒 ψ)  := ⟨elimContra!⟩



-- @@ L117-121 verbatim
variable {F : Type*} [LogicalConnective F] [LogicalNeutral F] [DecidableEq F]
         {S : Type*} [Entailment S F]
         {𝓢 : S}
         {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ ξ : F}
         {Γ Δ : List F}


-- @@ L123-123 verbatim
protected class Cl (𝓢 : S) extends Entailment.Minimal 𝓢, Entailment.HasAxiomDNE 𝓢


-- @@ L125-125 verbatim
variable [Entailment.Cl 𝓢]


-- @@ L127-127 verbatim
namespace FiniteContext

-- @@ L128-128 verbatim
instance (Γ : FiniteContext F 𝓢) : Entailment.Cl Γ where

-- @@ L129-129 verbatim
end FiniteContext


-- @@ L131-131 verbatim
namespace Context

-- @@ L132-132 verbatim
instance (Γ : Context F 𝓢) : Entailment.Cl Γ where

-- @@ L133-133 verbatim
end Context



-- @@ L136-136 verbatim
open NegationEquiv

-- @@ L137-137 verbatim
open FiniteContext

-- @@ L138-138 verbatim
open List


-- @@ L140-140 verbatim
def dn! : 𝓢 ⊢! φ 🡘 ∼∼φ := E!_intro dni! dne!

-- @@ L141-141 verbatim
@[simp] lemma dn : 𝓢 ⊢ φ 🡘 ∼∼φ := ⟨dn!⟩


-- @@ L143-143 verbatim
def A!_of_ANNNN! (d : 𝓢 ⊢! ∼∼φ ⋎ ∼∼ψ) : 𝓢 ⊢! φ ⋎ ψ := of_C!_of_C!_of_A! (C!_trans dne! or₁!) (C!_trans dne! or₂!) d

-- @@ L144-144 verbatim
omit [DecidableEq F] in lemma A_of_ANNNN (d : 𝓢 ⊢ ∼∼φ ⋎ ∼∼ψ) : 𝓢 ⊢ φ ⋎ ψ := ⟨A!_of_ANNNN! d.some⟩


-- @@ L146-147 verbatim
def CN!_of_CN!_left (b : 𝓢 ⊢! ∼φ 🡒 ψ) : 𝓢 ⊢! ∼ψ 🡒 φ := C!_trans (contra! b) dne!
lemma CN_of_CN_left (b : 𝓢 ⊢ ∼φ 🡒 ψ) : 𝓢 ⊢ ∼ψ 🡒 φ := ⟨CN!_of_CN!_left b.some⟩


-- @@ L149-149 verbatim
def CCNCN'! : 𝓢 ⊢! (∼φ 🡒 ψ) 🡒 (∼ψ 🡒 φ) := deduct'! $ CN!_of_CN!_left FiniteContext.id!

-- @@ L150-150 verbatim
@[simp] lemma CCNCN' : 𝓢 ⊢ (∼φ 🡒 ψ) 🡒 (∼ψ 🡒 φ) := ⟨CCNCN'!⟩



-- @@ L153-154 verbatim
def C!_of_CNN! (b : 𝓢 ⊢! ∼φ 🡒 ∼ψ) : 𝓢 ⊢! ψ 🡒 φ := C!_trans dni! (CN!_of_CN!_left b)
lemma C_of_CNN (b : 𝓢 ⊢ ∼φ 🡒 ∼ψ) : 𝓢 ⊢ ψ 🡒 φ := ⟨C!_of_CNN! b.some⟩



-- @@ L157-157 verbatim
def CCNNC! : 𝓢 ⊢! (∼φ 🡒 ∼ψ) 🡒 (ψ 🡒 φ) :=  deduct'! $ C!_of_CNN! FiniteContext.id!

-- @@ L158-158 verbatim
@[simp] lemma CCNNC : 𝓢 ⊢ (∼φ 🡒 ∼ψ) 🡒 (ψ 🡒 φ) := ⟨CCNNC!⟩


-- @@ L160-164 verbatim
def EN!_of_EN!_right (h : 𝓢 ⊢! φ 🡘 ∼ψ) : 𝓢 ⊢! ∼φ 🡘 ψ := by
  apply E!_intro;
  . apply CN!_of_CN!_left $  K!_right h;
  . apply CN!_of_CN!_right $  K!_left h;
lemma EN_of_EN_right (h : 𝓢 ⊢ φ 🡘 ∼ψ) : 𝓢 ⊢ ∼φ 🡘 ψ := ⟨EN!_of_EN!_right h.some⟩


-- @@ L166-167 verbatim
def EN!_of_EN!_left (h : 𝓢 ⊢! ∼φ 🡘 ψ) : 𝓢 ⊢! φ 🡘 ∼ψ := E!_symm $ EN!_of_EN!_right $ E!_symm h
lemma EN_of_EN_left (h : 𝓢 ⊢ ∼φ 🡘 ψ) : 𝓢 ⊢ φ 🡘 ∼ψ := ⟨EN!_of_EN!_left h.some⟩


-- @@ L169-170 verbatim
def ECCOO! : 𝓢 ⊢! φ 🡘 ((φ 🡒 ⊥) 🡒 ⊥) := E!_trans dn! ENNCCOO!
lemma ECCOO : 𝓢 ⊢ φ 🡘 ((φ 🡒 ⊥) 🡒 ⊥) := ⟨ECCOO!⟩



-- @@ L173-176 verbatim
def CNKANN! : 𝓢 ⊢! ∼(φ ⋏ ψ) 🡒 (∼φ ⋎ ∼ψ) := by
  apply CN!_of_CN!_left;
  apply deduct'!;
  exact K!_replace (KNN!_of_NA! $ FiniteContext.id!) dne! dne!;

-- @@ L177-177 verbatim
@[simp] lemma CNKANN : 𝓢 ⊢ ∼(φ ⋏ ψ) 🡒 (∼φ ⋎ ∼ψ) := ⟨CNKANN!⟩


-- @@ L179-180 verbatim
def ANN!_of_NK! (b : 𝓢 ⊢! ∼(φ ⋏ ψ)) : 𝓢 ⊢! ∼φ ⋎ ∼ψ := CNKANN! ⨀ b
lemma ANN_of_NK (b : 𝓢 ⊢ ∼(φ ⋏ ψ)) : 𝓢 ⊢ ∼φ ⋎ ∼ψ := ⟨ANN!_of_NK! b.some⟩


-- @@ L182-190 verbatim
def AN!_of_C! (d : 𝓢 ⊢! φ 🡒 ψ) : 𝓢 ⊢! ∼φ ⋎ ψ := by
  apply of_NN!;
  apply N!_of_CO!;
  apply deduct'!;
  have d₁ : [∼(∼φ ⋎ ψ)] ⊢[𝓢]! ∼∼φ ⋏ ∼ψ := KNN!_of_NA! $ FiniteContext.id!;
  have d₂ : [∼(∼φ ⋎ ψ)] ⊢[𝓢]! ∼φ 🡒 ⊥ := CO!_of_N! $ K!_left d₁;
  have d₃ : [∼(∼φ ⋎ ψ)] ⊢[𝓢]! ∼φ := (of! (Γ := [∼(∼φ ⋎ ψ)]) $ contra! d) ⨀ (K!_right d₁);
  exact d₂ ⨀ d₃;
lemma AN_of_C (d : 𝓢 ⊢ φ 🡒 ψ) : 𝓢 ⊢ ∼φ ⋎ ψ := ⟨AN!_of_C! d.some⟩


-- @@ L192-196 verbatim
def CCAN! : 𝓢 ⊢! (φ 🡒 ψ) 🡒 (∼φ ⋎ ψ) := by
  apply deduct'!;
  apply AN!_of_C!;
  exact FiniteContext.byAxm!;
lemma CCAN : 𝓢 ⊢ (φ 🡒 ψ) 🡒 ∼φ ⋎ ψ := ⟨CCAN!⟩



-- @@ L199-202 verbatim
instance : HasAxiomEFQ 𝓢 where
  efq! {φ} := by
    apply C!_of_CNN!;
    exact C!_trans (K!_left negEquiv!) $ C!_trans (C!_swap implyK!) (K!_right negEquiv!);


-- @@ L204-204 verbatim
instance : Entailment.Int 𝓢 where



-- @@ L207-211 verbatim
instance : HasAxiomElimContra 𝓢 where
  elimContra! {φ ψ} := by
    apply deduct'!;
    have : [∼ψ 🡒 ∼φ] ⊢[𝓢]! ∼ψ 🡒 ∼φ := FiniteContext.byAxm!;
    exact C!_of_CNN! this;


-- @@ L213-218 verbatim
instance : HasAxiomLEM 𝓢 := ⟨A!_of_ANNNN! $ AN!_of_C! dni!⟩


lemma CNC_of_C_of_CN (hpq : 𝓢 ⊢ φ 🡒 ψ) (hpnr : 𝓢 ⊢ φ 🡒 ∼ξ) : 𝓢 ⊢ φ 🡒 ∼(ψ 🡒 ξ) :=
  deduct' $ (contra $ CCAN) ⨀
    (NA_of_KNN $ K_intro (dni' $ of' hpq ⨀ FiniteContext.by_axm) (of' hpnr ⨀ FiniteContext.by_axm))


-- @@ L220-220 verbatim
def of_A!_of_N! (b : 𝓢 ⊢! φ ⋎ ψ) (d : 𝓢 ⊢! ∼φ) : 𝓢 ⊢! ψ := A!_cases (C!_of_CNN! (dhyp! d)) (C!_id) b


-- @@ L222-222 verbatim
theorem of_A_of_N (b : 𝓢 ⊢ φ ⋎ ψ) (d : 𝓢 ⊢ ∼φ) : 𝓢 ⊢ ψ := ⟨of_A!_of_N! b.get d.get⟩


-- @@ L224-224 verbatim
def ECAN! : 𝓢 ⊢! (φ 🡒 ψ) 🡘 (∼φ ⋎ ψ) := E!_intro CCAN! (deduct'! (A!_cases CNC! implyK! byAxm₀!))

-- @@ L225-225 verbatim
theorem ECAN : 𝓢 ⊢ (φ 🡒 ψ) 🡘 (∼φ ⋎ ψ) := ⟨ECAN!⟩




-- @@ L229-229 verbatim
section


-- @@ L231-255 verbatim
@[simp]
lemma CNDisj₂NConj₂ {Γ : List F} : 𝓢 ⊢ ∼⋁(Γ.map (∼·)) 🡒 ⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ hΓ ih =>
    simp_all only [ne_eq, not_false_eq_true, List.disj₂_cons_nonempty, List.map_cons, List.map_eq_nil_iff, List.conj₂_cons_nonempty];
    suffices 𝓢 ⊢ ∼(∼φ ⋎ ∼∼⋁List.map (fun x ↦ ∼x) Γ) 🡒 φ ⋏ ⋀Γ by
      apply C_trans ?_ this;
      apply contra;
      apply CAA_of_C_right;
      exact dne;
    apply C_trans CNAKNN ?_;
    apply CKK_of_C_of_C;
    . exact dne;
    . exact C_trans dne ih;

lemma CNFdisj₂NFconj₂ {Γ : Finset F} : 𝓢 ⊢ ∼(Γ.image (∼·)).disj 🡒 Γ.conj := by
  apply C_replace ?_ ?_ $ CNDisj₂NConj₂ (Γ := Γ.toList);
  . apply contra;
    apply left_Disj₂_intro;
    intro ψ hψ;
    apply right_Fdisj_intro;
    simpa using hψ;
  . simp;


-- @@ L257-257 verbatim
end



-- @@ L260-260 verbatim
section consistency


-- @@ L262-262 verbatim
omit [Entailment.Cl 𝓢]


-- @@ L264-279 verbatim
variable [AdjunctiveSet F S] [Axiomatized S] [Deduction S] [∀ 𝓢 : S, Entailment.Cl 𝓢]

lemma provable_iff_inconsistent_adjoin {φ : F} :
    𝓢 ⊢ φ ↔ Inconsistent (adjoin (∼φ) 𝓢) := by
  constructor
  · intro h
    apply inconsistent_of_provable_of_unprovable (φ := φ)
    · exact Axiomatized.to_adjoin h
    · exact Axiomatized.adjoin! _ _
  · intro h
    have : 𝓢 ⊢ ∼φ 🡒 ⊥ := Deduction.of_insert! (h _)
    refine of_NN <| N_iff_CO.mpr this

lemma unprovable_iff_consistent_adjoin {φ : F} :
    𝓢 ⊬ φ ↔ Consistent (adjoin (∼φ) 𝓢) := by
  simpa using provable_iff_inconsistent_adjoin.not


-- @@ L281-281 verbatim
instance deductiveExplosion : Entailment.DeductiveExplosion S := inferInstance


-- @@ L283-283 verbatim
end consistency



-- @@ L286-286 verbatim
section


-- @@ L288-297 verbatim
instance : HasAxiomPeirce 𝓢 where
  peirce! {φ ψ} := by
    apply of_C!_of_C!_of_A! implyK! ?_ lem!;
    apply deduct'!;
    apply deduct!;
    refine (FiniteContext.byAxm! (φ := (φ 🡒 ψ) 🡒 φ)) ⨀ ?_;
    apply deduct!;
    apply efq_of_mem_either! (φ := φ);
    . simp;
    . simp;


-- @@ L299-299 verbatim
instance : HasAxiomEFQ 𝓢 := inferInstance


-- @@ L301-301 verbatim
instance : Entailment.Int 𝓢 where


-- @@ L303-303 verbatim
end


-- @@ L305-305 verbatim
section


-- @@ L307-307 verbatim
variable {G T : Type*} [Entailment T G] [LogicalConnective G] [LogicalNeutral G] {𝓣 : T}


-- @@ L309-323 verbatim
abbrev Cl.ofEquiv (𝓢 : S) [Entailment.Cl 𝓢] (𝓣 : T) (f : G →ˡᶜ F) (e : (φ : G) → 𝓢 ⊢! f φ ≃ 𝓣 ⊢! φ) : Entailment.Cl 𝓣 where
  mdp! {φ ψ dpq dp} := (e ψ) (
    let d : 𝓢 ⊢! f φ 🡒 f ψ := by simpa using (e (φ 🡒 ψ)).symm dpq
    d ⨀ ((e φ).symm dp))
  negEquiv! := e _ (by simpa using negEquiv!)
  verum! := e _ (by simpa using verum!)
  implyK! := e _ (by simpa using implyK!)
  implyS! := e _ (by simpa using implyS!)
  and₁! := e _ (by simpa using and₁!)
  and₂! := e _ (by simpa using and₂!)
  and₃! := e _ (by simpa using and₃!)
  or₁! := e _ (by simpa using or₁!)
  or₂! := e _ (by simpa using or₂!)
  or₃! := e _ (by simpa using or₃!)
  dne! := e _ (by simpa using dne!)


-- @@ L325-325 verbatim
end



-- @@ L328-328 verbatim
section


-- @@ L330-331 verbatim
variable {S F : Type*} [LogicalConnective F] [LogicalNeutral F] [DecidableEq F] [Entailment S F]
         {𝓢 : S} [Entailment.Int 𝓢]


-- @@ L333-333 verbatim
open FiniteContext


-- @@ L335-343 verbatim
instance [HasAxiomLEM 𝓢] : HasAxiomDNE 𝓢 where
  dne! {φ} := by
    apply deduct'!;
    exact of_C!_of_C!_of_A! C!_id (by
      apply deduct!;
      have nnp : [∼φ, ∼∼φ] ⊢[𝓢]! ∼φ 🡒 ⊥ := CO!_of_N! $ FiniteContext.byAxm!;
      have np : [∼φ, ∼∼φ] ⊢[𝓢]! ∼φ := FiniteContext.byAxm!;
      exact of_O! $ nnp ⨀ np;
    ) $ of! lem!;


-- @@ L345-345 verbatim
instance [HasAxiomLEM 𝓢] : Entailment.Cl 𝓢 where


-- @@ L347-347 verbatim
end


-- @@ L349-349 verbatim
end FFL.Entailment


-- @@ L351-351 verbatim
end
