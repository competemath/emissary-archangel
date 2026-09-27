/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Logic.HilbertStyle.Basic


-- @@ L10-10 verbatim
/-! # Context -/


-- @@ L12-12 verbatim
@[expose] public section



-- @@ L15-15 verbatim
namespace LO


-- @@ L17-17 verbatim
namespace Entailment


-- @@ L19-19 verbatim
variable (F : Type*) {S : Type*}


-- @@ L21-24 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure FiniteContext (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  ctx : List F


-- @@ L26-26 verbatim
variable {F}


-- @@ L28-28 verbatim
namespace FiniteContext


-- @@ L30-30 verbatim
variable {𝓢 : S}


-- @@ L32-32 verbatim
instance : Coe (List F) (FiniteContext F 𝓢) := ⟨mk⟩


-- @@ L34-35 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev conj [LogicalConnective F] (Γ : FiniteContext F 𝓢) : F :=
  List.conj₂ Γ.ctx


-- @@ L37-38 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev disj [LogicalConnective F] (Γ : FiniteContext F 𝓢) : F :=
  disj₂ Γ.ctx


-- @@ L40-40 verbatim
instance : EmptyCollection (FiniteContext F 𝓢) := ⟨⟨[]⟩⟩


-- @@ L42-42 verbatim
instance : Membership F (FiniteContext F 𝓢) := ⟨fun Γ x => (x ∈ Γ.ctx)⟩


-- @@ L44-44 verbatim
instance : HasSubset (FiniteContext F 𝓢) := ⟨(·.ctx ⊆ ·.ctx)⟩


-- @@ L46-46 verbatim
instance : Cons F (FiniteContext F 𝓢) := ⟨(· :: ·.ctx)⟩


-- @@ L48-48 verbatim
lemma mem_def {φ : F} {Γ : FiniteContext F 𝓢} : φ ∈ Γ ↔ φ ∈ Γ.ctx := iff_of_eq rfl


-- @@ L50-51 verbatim
@[simp 1100] lemma coe_subset_coe_iff {Γ Δ : List F} : (Γ : FiniteContext F 𝓢) ⊆ Δ ↔ Γ ⊆ Δ :=
  iff_of_eq rfl


-- @@ L53-54 verbatim
@[simp] lemma mem_coe_iff {φ : F} {Γ : List F} : φ ∈ (Γ : FiniteContext F 𝓢) ↔ φ ∈ Γ :=
  iff_of_eq rfl


-- @@ L56-58 verbatim
@[simp 1100] lemma not_mem_empty (φ : F) : ¬φ ∈ (∅ :
    FiniteContext F 𝓢) := by
  simp [EmptyCollection.emptyCollection]


-- @@ L60-63 verbatim
instance : Collection F (FiniteContext F 𝓢) where
  subset_iff := List.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Cons.cons, mem_def]


-- @@ L65-65 verbatim
variable [Entailment F S] [LogicalConnective F]


-- @@ L67-67 expanded
instance (𝓢 : S) : Entailment F (FiniteContext F 𝓢) :=
  ⟨(Entailment.Prf 𝓢 (Arrow.arrow ·.conj ·))⟩


-- @@ L69-70 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Prf (𝓢 : S) (Γ : List F) (φ : F) : Type _ :=
  Entailment.Prf (Γ : FiniteContext F 𝓢) φ


-- @@ L72-73 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Provable (𝓢 : S) (Γ : List F) (φ : F) : Prop :=
  Provable (Γ : FiniteContext F 𝓢) φ


-- @@ L75-76 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Unprovable (𝓢 : S) (Γ : List F) (φ : F) : Prop :=
  Unprovable (Γ : FiniteContext F 𝓢) φ


-- @@ L78-79 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev PrfSet (𝓢 : S) (Γ : List F) (s : Set F) : Type _ :=
  PrfSet (Γ : FiniteContext F 𝓢) s


-- @@ L81-82 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev ProvableSet (𝓢 : S) (Γ : List F) (s : Set F) : Prop :=
  ProvableSet (Γ : FiniteContext F 𝓢) s


-- @@ L84-85 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ:45 " ⊢[" 𝓢 "] " φ:46 => Prf 𝓢 Γ φ


-- @@ L87-88 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ:45 " ⊢[" 𝓢 "]! " φ:46 => Provable 𝓢 Γ φ


-- @@ L90-91 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ:45 " ⊬[" 𝓢 "] " φ:46 => Unprovable 𝓢 Γ φ


-- @@ L93-94 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ:45 " ⊢[" 𝓢 "]* " s:46 => PrfSet 𝓢 Γ s


-- @@ L96-97 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ:45 " ⊢[" 𝓢 "]*! " s:46 => ProvableSet 𝓢 Γ s


-- @@ L99-99 expanded
lemma entailment_def (Γ : FiniteContext F 𝓢) (φ : F) :
    (Entailment.Prf Γ φ) = (Entailment.Prf 𝓢 (Arrow.arrow Γ.conj φ)) :=
  rfl


-- @@ L101-102 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ofDef {Γ : List F} {φ : F} (b : Entailment.Prf 𝓢 (Arrow.arrow (List.conj₂ Γ) φ)) : Prf 𝓢 Γ φ :=
  b


-- @@ L104-105 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def toDef {Γ : List F} {φ : F} (b : Prf 𝓢 Γ φ) : Entailment.Prf 𝓢 (Arrow.arrow (List.conj₂ Γ) φ) :=
  b


-- @@ L107-107 expanded
lemma toₛ! (b : Provable 𝓢 Γ φ) : Provable 𝓢 (Arrow.arrow (List.conj₂ Γ) φ) :=
  b


-- @@ L109-109 expanded
lemma provable_iff {φ : F} : Provable 𝓢 Γ φ ↔ Provable 𝓢 (Arrow.arrow (List.conj₂ Γ) φ) :=
  iff_of_eq rfl


-- @@ L111-112 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def cast {Γ φ} (d : Prf 𝓢 Γ φ) (eΓ : Γ = Γ') (eφ : φ = φ') : Prf 𝓢 Γ' φ' :=
  eΓ ▸ eφ ▸ d


-- @@ L114-114 verbatim
section «lp_section_1»


-- @@ L116-116 verbatim
variable {Γ Δ E : List F}

-- @@ L117-117 verbatim
variable [Entailment.Minimal 𝓢]


-- @@ L119-121 verbatim
instance [DecidableEq F] : Axiomatized (FiniteContext F 𝓢) where
  prfAxm := fun hp ↦ generalConj' hp
  weakening := fun H b ↦ impTrans'' (conjImplyConj' H) b


-- @@ L123-127 verbatim
instance : Compact (FiniteContext F 𝓢) where
  φ := fun {Γ} _ _ ↦ Γ
  φPrf := id
  φ_subset := by simp
  φ_finite := by rintro ⟨Γ⟩; simp [Collection.Finite, Collection.set]


-- @@ L129-130 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def nthAxm {Γ} (n : ℕ) (h : n < Γ.length := by simp) : Prf 𝓢 Γ Γ[n] :=
  conj₂Nth Γ n h


-- @@ L131-131 expanded
lemma nth_axm! {Γ} (n : ℕ) (h : n < Γ.length := by simp) : Provable 𝓢 Γ Γ[n] :=
  ⟨nthAxm n h⟩


-- @@ L133-134 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def byAxm [DecidableEq F] {φ} (h : φ ∈ Γ := by simp) : Prf 𝓢 Γ φ :=
  Axiomatized.prfAxm (by simpa)


-- @@ L136-139 expanded
lemma by_axm! {φ} (h : φ ∈ Γ := by simp) : Provable 𝓢 Γ φ := by
  classical exact Axiomatized.provable_axm _ (by simpa)


-- @@ L141-143 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def weakening [DecidableEq F] (h : Γ ⊆ Δ) {φ} : Prf 𝓢 Γ φ → Prf 𝓢 Δ φ :=
  Axiomatized.weakening (by simpa)


-- @@ L145-147 expanded
lemma weakening! (h : Γ ⊆ Δ) {φ} : Provable 𝓢 Γ φ → Provable 𝓢 Δ φ := by
  classical exact fun h ↦ (Axiomatized.le_of_subset (by simpa)).subset h


-- @@ L149-150 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def of {φ : F} (b : Entailment.Prf 𝓢 φ) : Prf 𝓢 Γ φ :=
  imply₁' (ψ := List.conj₂ Γ) b


-- @@ L152-153 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def emptyPrf {φ : F} : Prf 𝓢 [] φ → Entailment.Prf 𝓢 φ := fun b ↦ mdp b verum


-- @@ L155-157 expanded
/-- Imported declaration from the Incompleteness formalization. -/
lemma provable_iff_provable {φ : F} : Provable 𝓢 φ ↔ Provable 𝓢 [] φ :=
  ⟨fun b ↦ ⟨of b.some⟩, fun b ↦ ⟨emptyPrf b.some⟩⟩


-- @@ L159-160 expanded
lemma of'! (h : Provable 𝓢 φ) : Provable 𝓢 Γ φ :=
  weakening! (by simp) <| provable_iff_provable.mp h


-- @@ L162-163 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def id : Prf 𝓢 [φ] φ :=
  nthAxm 0


-- @@ L164-164 expanded
@[simp]
lemma id! : Provable 𝓢 [φ] φ :=
  nth_axm! 0


-- @@ L166-167 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def byAxm₀ : Prf 𝓢 (φ :: Γ) φ :=
  nthAxm 0


-- @@ L168-168 expanded
lemma by_axm₀! : Provable 𝓢 (φ :: Γ) φ :=
  nth_axm! 0


-- @@ L170-171 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def byAxm₁ : Prf 𝓢 (φ :: ψ :: Γ) ψ :=
  nthAxm 1


-- @@ L172-172 expanded
lemma by_axm₁! : Provable 𝓢 (φ :: ψ :: Γ) ψ :=
  nth_axm! 1


-- @@ L174-175 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def byAxm₂ : Prf 𝓢 (φ :: ψ :: χ :: Γ) χ :=
  nthAxm 2


-- @@ L176-176 expanded
lemma by_axm₂! : Provable 𝓢 (φ :: ψ :: χ :: Γ) χ :=
  nth_axm! 2


-- @@ L178-178 verbatim
instance (Γ : FiniteContext F 𝓢) : Entailment.ModusPonens Γ := ⟨mdp₁⟩


-- @@ L180-180 verbatim
instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomVerum Γ := ⟨of verum⟩


-- @@ L182-182 verbatim
instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomImply₁ Γ := ⟨fun _ _ ↦ of imply₁⟩


-- @@ L184-184 verbatim
instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomImply₂ Γ := ⟨fun _ _ _ ↦ of imply₂⟩


-- @@ L186-187 verbatim
instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomAndElim Γ :=
  ⟨fun _ _ ↦ of and₁, fun _ _ ↦ of and₂⟩


-- @@ L189-189 verbatim
instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomAndInst Γ := ⟨fun _ _ ↦ of and₃⟩


-- @@ L191-192 verbatim
instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomOrInst Γ :=
  ⟨fun _ _ ↦ of or₁, fun _ _ ↦ of or₂⟩


-- @@ L194-194 verbatim
instance (Γ : FiniteContext F 𝓢) : Entailment.HasAxiomOrElim Γ := ⟨fun _ _ _ ↦ of or₃⟩


-- @@ L196-196 verbatim
instance (Γ : FiniteContext F 𝓢) : Entailment.NegationEquiv Γ := ⟨fun _ ↦ of negEquiv⟩


-- @@ L198-198 verbatim
instance (Γ : FiniteContext F 𝓢) : Entailment.Minimal Γ where



-- @@ L201-203 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def mdp' [DecidableEq F] (bΓ : Prf 𝓢 Γ (Arrow.arrow φ ψ)) (bΔ : Prf 𝓢 Δ φ) : Prf 𝓢 (Γ ++ Δ) ψ :=
  mdp (wk (by simp) bΓ) (wk (by simp) bΔ)


-- @@ L205-208 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def deduct {φ ψ : F} : {Γ : List F} → Prf 𝓢 (φ :: Γ) ψ → Prf 𝓢 Γ (Arrow.arrow φ ψ)
  | .nil => fun b ↦ ofDef <| imply₁' (toDef b)
  | .cons _ _ => fun b ↦ ofDef <| andImplyIffImplyImply'.mp (impTrans'' (andComm _ _) (toDef b))


-- @@ L210-210 expanded
lemma deduct! (h : Provable 𝓢 (φ :: Γ) ψ) : Provable 𝓢 Γ (Arrow.arrow φ ψ) :=
  ⟨FiniteContext.deduct h.some⟩


-- @@ L212-215 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def deductInv {φ ψ : F} : {Γ : List F} → Prf 𝓢 Γ (Arrow.arrow φ ψ) → Prf 𝓢 (φ :: Γ) ψ
  | .nil => fun b => ofDef <| mdp (toDef b) verum
  | .cons _ _ => fun b => ofDef <| (impTrans'' (andComm _ _) (andImplyIffImplyImply'.mpr (toDef b)))


-- @@ L217-217 expanded
lemma deductInv! (h : Provable 𝓢 Γ (Arrow.arrow φ ψ)) : Provable 𝓢 (φ :: Γ) ψ :=
  ⟨FiniteContext.deductInv h.some⟩


-- @@ L219-220 expanded
lemma deduct_iff {φ ψ : F} {Γ : List F} : Provable 𝓢 Γ (Arrow.arrow φ ψ) ↔ Provable 𝓢 (φ :: Γ) ψ :=
  ⟨fun h ↦ ⟨deductInv h.some⟩, fun h ↦ ⟨deduct h.some⟩⟩


-- @@ L222-223 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def deduct' : Prf 𝓢 [φ] ψ → Entailment.Prf 𝓢 (Arrow.arrow φ ψ) := fun b ↦ emptyPrf <| deduct b


-- @@ L225-225 expanded
lemma deduct'! (h : Provable 𝓢 [φ] ψ) : Provable 𝓢 (Arrow.arrow φ ψ) :=
  ⟨FiniteContext.deduct' h.some⟩


-- @@ L228-229 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def deductInv' : Entailment.Prf 𝓢 (Arrow.arrow φ ψ) → Prf 𝓢 [φ] ψ := fun b ↦ deductInv <| of b


-- @@ L231-231 expanded
lemma deductInv'! (h : Provable 𝓢 (Arrow.arrow φ ψ)) : Provable 𝓢 [φ] ψ :=
  ⟨FiniteContext.deductInv' h.some⟩


-- @@ L234-236 verbatim
instance deduction : Deduction (FiniteContext F 𝓢) where
  ofInsert := deduct
  inv := deductInv


-- @@ L238-241 expanded
instance : StrongCut (FiniteContext F 𝓢) (FiniteContext F 𝓢) :=
  ⟨fun {Γ Δ _} bΓ bΔ ↦
    have : Entailment.Prf Γ Δ.conj := conjIntro' _ (fun _ hp ↦ bΓ hp)
    ofDef <| impTrans'' (toDef this) (toDef bΔ)⟩


-- @@ L243-243 verbatim
instance [HasAxiomEFQ 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomEFQ Γ := ⟨fun _ ↦ of efq⟩


-- @@ L245-245 verbatim
instance [HasAxiomEFQ 𝓢] : DeductiveExplosion (FiniteContext F 𝓢) := inferInstance


-- @@ L247-247 verbatim
instance [HasAxiomDNE 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomDNE Γ := ⟨fun φ ↦ of (HasAxiomDNE.dne φ)⟩


-- @@ L249-249 verbatim
end «lp_section_1»


-- @@ L251-251 verbatim
instance [Entailment.Intuitionistic 𝓢] (Γ : FiniteContext F 𝓢) : Entailment.Intuitionistic Γ where


-- @@ L253-253 verbatim
instance [Entailment.Classical 𝓢] (Γ : FiniteContext F 𝓢) : Entailment.Classical Γ where


-- @@ L255-255 verbatim
end FiniteContext



-- @@ L258-258 verbatim
variable (F)


-- @@ L260-263 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure Context (𝓢 : S) where
  /-- Imported declaration from the Incompleteness formalization. -/
  ctx : Set F


-- @@ L265-265 verbatim
variable {F}



-- @@ L268-268 verbatim
namespace Context


-- @@ L270-270 verbatim
variable {𝓢 : S}


-- @@ L272-272 verbatim
instance : Coe (Set F) (Context F 𝓢) := ⟨mk⟩


-- @@ L274-274 verbatim
instance : EmptyCollection (Context F 𝓢) := ⟨⟨∅⟩⟩


-- @@ L276-276 verbatim
instance : Membership F (Context F 𝓢) := ⟨fun Γ x => (x ∈ Γ.ctx)⟩


-- @@ L278-278 verbatim
instance : HasSubset (Context F 𝓢) := ⟨(·.ctx ⊆ ·.ctx)⟩


-- @@ L280-280 verbatim
instance : Cons F (Context F 𝓢) := ⟨(⟨insert · ·.ctx⟩)⟩


-- @@ L282-282 verbatim
lemma mem_def {φ : F} {Γ : Context F 𝓢} : φ ∈ Γ ↔ φ ∈ Γ.ctx := iff_of_eq rfl


-- @@ L284-284 verbatim
@[simp 1100] lemma coe_subset_coe_iff {Γ Δ : Set F} : (Γ : Context F 𝓢) ⊆ Δ ↔ Γ ⊆ Δ := iff_of_eq rfl


-- @@ L286-286 verbatim
@[simp] lemma mem_coe_iff {φ : F} {Γ : Set F} : φ ∈ (Γ : Context F 𝓢) ↔ φ ∈ Γ := iff_of_eq rfl


-- @@ L288-288 verbatim
@[simp 1100] lemma not_mem_empty (φ : F) : ¬φ ∈ (∅ : Context F 𝓢) := fun h ↦ h


-- @@ L290-293 verbatim
instance : Collection F (Context F 𝓢) where
  subset_iff := by rintro ⟨s⟩ ⟨u⟩; simp [Set.subset_def]
  not_mem_empty := by simp
  mem_cons_iff := by simp [Cons.cons, mem_def]


-- @@ L295-295 verbatim
variable [LogicalConnective F] [Entailment F S]


-- @@ L297-303 expanded
/-- Imported declaration from the Incompleteness formalization. -/
structure Proof (Γ : Context F 𝓢) (φ : F) where
  /-- Imported declaration from the Incompleteness formalization. -/
  ctx : List F
  subset : ∀ ψ ∈ ctx, ψ ∈ Γ
  /-- Imported declaration from the Incompleteness formalization. -/
  prf : Prf 𝓢 ctx φ


-- @@ L305-305 verbatim
instance (𝓢 : S) : Entailment F (Context F 𝓢) := ⟨Proof⟩


-- @@ L307-307 verbatim
variable (𝓢)


-- @@ L309-310 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Prf (Γ : Set F) (φ : F) : Type _ :=
  Entailment.Prf (Γ : Context F 𝓢) φ


-- @@ L312-313 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Provable (Γ : Set F) (φ : F) : Prop :=
  Provable (Γ : Context F 𝓢) φ


-- @@ L315-316 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev Unprovable (Γ : Set F) (φ : F) : Prop :=
  Unprovable (Γ : Context F 𝓢) φ


-- @@ L318-319 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev PrfSet (Γ : Set F) (s : Set F) : Type _ :=
  PrfSet (Γ : Context F 𝓢) s


-- @@ L321-322 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev ProvableSet (Γ : Set F) (s : Set F) : Prop :=
  ProvableSet (Γ : Context F 𝓢) s


-- @@ L324-325 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ:45 " *⊢[" 𝓢 "] " φ:46 => Prf 𝓢 Γ φ


-- @@ L327-328 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ:45 " *⊢[" 𝓢 "]! " φ:46 => Provable 𝓢 Γ φ


-- @@ L330-331 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ:45 " *⊬[" 𝓢 "] " φ:46 => Unprovable 𝓢 Γ φ


-- @@ L333-334 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ:45 " *⊢[" 𝓢 "]* " s:46 => PrfSet 𝓢 Γ s


-- @@ L336-337 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation Γ:45 " *⊢[" 𝓢 "]*! " s:46 => ProvableSet 𝓢 Γ s


-- @@ L339-339 verbatim
section «lp_section_2»


-- @@ L341-341 verbatim
variable {𝓢}


-- @@ L343-344 expanded
lemma provable_iff {φ : F} : Provable 𝓢 Γ φ ↔ ∃ Δ : List F, (∀ ψ ∈ Δ, ψ ∈ Γ) ∧ Provable 𝓢 Δ φ :=
  ⟨by rintro ⟨⟨Δ, h, b⟩⟩; exact ⟨Δ, h, ⟨b⟩⟩, by rintro ⟨Δ, h, ⟨d⟩⟩; exact ⟨⟨Δ, h, d⟩⟩⟩


-- @@ L346-346 verbatim
section «lp_section_3»


-- @@ L348-348 verbatim
variable [Entailment.Minimal 𝓢]


-- @@ L350-352 verbatim
instance [DecidableEq F] : Axiomatized (Context F 𝓢) where
  prfAxm := fun {Γ φ} hp ↦ ⟨[φ], by simpa using hp, byAxm (by simp [Collection.set])⟩
  weakening := fun h b ↦ ⟨b.ctx, fun φ hp ↦ Collection.subset_iff.mp h φ (b.subset φ hp), b.prf⟩


-- @@ L354-358 verbatim
instance : Compact (Context F 𝓢) where
  φ := fun b ↦ Collection.set b.ctx
  φPrf := fun b ↦ ⟨b.ctx, by simp [Collection.set], b.prf⟩
  φ_subset := by rintro ⟨Γ⟩ φ b; exact b.subset
  φ_finite := by rintro ⟨Γ⟩; simp [Collection.Finite, Collection.set]


-- @@ L360-375 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def deduct [DecidableEq F] {φ ψ : F} {Γ : Set F} : Prf 𝓢 (insert φ Γ) ψ → Prf 𝓢 Γ (Arrow.arrow φ ψ)
  | ⟨Δ, h, b⟩ =>
    have h : ∀ ψ ∈ Δ, ψ = φ ∨ ψ ∈ Γ := by simpa using h
    let b' : Prf 𝓢 (φ :: Δ.filter (· ≠ φ)) ψ :=
      FiniteContext.weakening (by simp only [ne_eq, decide_not]; rintro χ hr; simp [hr]; tauto) b
    ⟨Δ.filter (· ≠ φ), by
      intro ψ;
      simp only [ne_eq, decide_not, List.mem_filter, Bool.not_eq_eq_eq_not, Bool.not_true,
        decide_eq_false_iff_not, mem_coe_iff, and_imp]
      intro hq ne
      rcases h ψ hq
      · contradiction
      · assumption, FiniteContext.deduct b'⟩


-- @@ L377-380 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def deductInv {φ ψ : F} {Γ : Set F} : Prf 𝓢 Γ (Arrow.arrow φ ψ) → Prf 𝓢 (insert φ Γ) ψ
  | ⟨Δ, h, b⟩ => ⟨φ :: Δ, by simp_all, FiniteContext.deductInv b⟩


-- @@ L382-384 verbatim
instance deduction [DecidableEq F] : Deduction (Context F 𝓢) where
  ofInsert := deduct
  inv := deductInv


-- @@ L386-387 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def of {φ : F} (b : Entailment.Prf 𝓢 φ) : Prf 𝓢 Γ φ :=
  ⟨[], by simp, FiniteContext.of b⟩


-- @@ L389-389 expanded
lemma of! (b : Provable 𝓢 φ) : Provable 𝓢 Γ φ :=
  ⟨Context.of b.some⟩


-- @@ L391-397 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def mdp [DecidableEq F] {Γ : Set F} (bpq : Prf 𝓢 Γ (Arrow.arrow φ ψ)) (bp : Prf 𝓢 Γ φ) :
    Prf 𝓢 Γ ψ :=
  ⟨bpq.ctx ++ bp.ctx, by
    simp only [List.mem_append, mem_coe_iff]; rintro χ (hr | hr)
    · exact bpq.subset χ hr
    · exact bp.subset χ hr, FiniteContext.mdp' bpq.prf bp.prf⟩


-- @@ L399-401 expanded
lemma by_axm! (h : φ ∈ Γ) : Provable 𝓢 Γ φ := by classical exact Entailment.by_axm _ (by simpa)


-- @@ L403-408 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def emptyPrf {φ : F} : Prf 𝓢 ∅ φ → Entailment.Prf 𝓢 φ :=
  by
  rintro ⟨Γ, hΓ, h⟩
  have := List.eq_nil_iff_forall_not_mem.mpr hΓ
  subst this
  exact FiniteContext.emptyPrf h


-- @@ L410-410 expanded
lemma emptyPrf! {φ : F} : Provable 𝓢 ∅ φ → Provable 𝓢 φ := fun h ↦ ⟨emptyPrf h.some⟩


-- @@ L412-412 expanded
lemma provable_iff_provable {φ : F} : Provable 𝓢 φ ↔ Provable 𝓢 ∅ φ :=
  ⟨of!, emptyPrf!⟩


-- @@ L414-425 verbatim
instance minimal [DecidableEq F] (Γ : Context F 𝓢) : Entailment.Minimal Γ where
  mdp := mdp
  verum := of verum
  imply₁ := fun _ _ ↦ of imply₁
  imply₂ := fun _ _ _ ↦ of imply₂
  and₁ := fun _ _ ↦ of and₁
  and₂ := fun _ _ ↦ of and₂
  and₃ := fun _ _ ↦ of and₃
  or₁ := fun _ _ ↦ of or₁
  or₂ := fun _ _ ↦ of or₂
  or₃ := fun _ _ _ ↦ of or₃
  negEquiv := fun _ ↦ of negEquiv


-- @@ L427-427 verbatim
instance [HasAxiomEFQ 𝓢] (Γ : Context F 𝓢) : HasAxiomEFQ Γ := ⟨fun _ ↦ of efq⟩


-- @@ L429-429 verbatim
instance [HasAxiomDNE 𝓢] (Γ : Context F 𝓢) : HasAxiomDNE Γ := ⟨fun φ ↦ of (HasAxiomDNE.dne φ)⟩


-- @@ L431-431 verbatim
instance [HasAxiomEFQ 𝓢] : DeductiveExplosion (FiniteContext F 𝓢) := inferInstance


-- @@ L433-433 verbatim
end «lp_section_3»


-- @@ L435-436 verbatim
instance [DecidableEq F] [Entailment.Intuitionistic 𝓢] (Γ : Context F 𝓢) :
    Entailment.Intuitionistic Γ where


-- @@ L438-438 verbatim
instance [DecidableEq F] [Entailment.Classical 𝓢] (Γ : Context F 𝓢) : Entailment.Classical Γ where


-- @@ L440-440 verbatim
end «lp_section_2»


-- @@ L442-442 verbatim
end Context


-- @@ L444-444 verbatim
end Entailment


-- @@ L446-446 verbatim
end LO
