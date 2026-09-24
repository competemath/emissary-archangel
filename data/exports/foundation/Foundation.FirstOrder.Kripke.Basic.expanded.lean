module

public import Foundation.FirstOrder.Basic
public import Foundation.Syntax.Predicate.Relational
public import Foundation.Logic.ForcingRelation
public import Foundation.Vorspiel.Order.Dense


-- @@ L8-8 verbatim
@[expose] public section

-- @@ L9-9 verbatim
namespace FFL.FirstOrder


-- @@ L11-20 verbatim
/-- Kripke model for relational first-order language -/
class KripkeModel
    (L : outParam Language) [L.Relational]
    (World : Type*) [Preorder World]
    (Carrier : outParam Type*) where
  Domain : World → Set Carrier
  domain_nonempty : ∀ w, ∃ x, x ∈ Domain w
  domain_antimonotone : w ≥ v → Domain w ⊆ Domain v
  Rel (w : World) {k : ℕ} (R : L.Rel k) : (Fin k → Carrier) → Prop
  rel_monotone : Rel w R t → ∀ v ≤ w, Rel v R t


-- @@ L22-26 verbatim
class KripkeModel.ConstantDomain
    {L : Language} [L.Relational]
    (World : Type*) [Preorder World]
    {Carrier : Type*} [KripkeModel L World Carrier] where
  const_domain : ∀ w : World, Domain w = Set.univ


-- @@ L28-28 verbatim
attribute [simp] KripkeModel.ConstantDomain.const_domain


-- @@ L30-30 verbatim
variable (L : Language) [L.Relational] (W : Type*) [Preorder W] (C : outParam Type*) [KripkeModel L W C]


-- @@ L32-32 verbatim
instance : CoeSort W (Type _) := ⟨fun w ↦ KripkeModel.Domain w⟩


-- @@ L34-34 verbatim
instance : ForcingExists W C := ⟨fun p x ↦ x ∈ KripkeModel.Domain p⟩


-- @@ L36-36 verbatim
variable {L W C}


-- @@ L38-40 verbatim
namespace KripkeModel

lemma domain_nonempty' (p : W) : ∃ x, p ⊩↓ x := domain_nonempty p


-- @@ L42-47 verbatim
instance (p : W) : Nonempty p := by
  rcases domain_nonempty p with ⟨x, _⟩
  exact ⟨x, by assumption⟩

lemma domain_monotone {p : W} : p ⊩↓ x → ∀ q ≤ p, q ⊩↓ x := fun hx _ h ↦
  domain_antimonotone h hx


-- @@ L49-49 verbatim
@[simp] lemma domain_forcesExists {p : W} (x : p) : p ⊩↓ x.val := x.prop


-- @@ L51-52 verbatim
@[simp] lemma forcingExists_of_constantDomain [ConstantDomain W] (w : W) (x : C) : w ⊩↓ x := by
  suffices x ∈ Domain w from this; simp



-- @@ L55-55 verbatim
section filter


-- @@ L57-57 verbatim
variable (W)


-- @@ L59-59 verbatim
abbrev Filter : Type _ := Order.PFilter W


-- @@ L61-61 verbatim
variable {W}


-- @@ L63-63 verbatim
namespace Filter


-- @@ L65-68 verbatim
/-- A domain of filter `F` -/
@[ext] structure Model (F : Filter W) where
  val : C
  mem_filter : ∃ p ∈ F, p ⊩↓ val


-- @@ L70-70 verbatim
attribute [coe] Model.val


-- @@ L72-72 verbatim
variable (F : Filter W)


-- @@ L74-85 verbatim
instance : CoeOut F.Model C := ⟨fun x ↦ x.val⟩

lemma finite_colimit [Fintype ι] (p : ι → W) (hp : ∀ i, p i ∈ F) : ∃ q ∈ F, ∀ i, q ≤ p i :=
  DirectedOn.fintype_colimit isTrans_ge (Order.PFilter.nonempty F) F.directed p hp

lemma finite_colimit_domain [Fintype ι] (v : ι → F.Model) :
    ∃ q ∈ F, ∀ i, q ⊩↓ ↑(v i) := by
  have : ∀ i, ∃ p ∈ F, p ⊩↓ ↑(v i) := fun i ↦ (v i).mem_filter
  choose p hp using this
  have : ∃ q ∈ F, ∀ i, q ≤ p i := F.finite_colimit p fun i ↦ (hp i).1
  rcases this with ⟨q, hq, hqp⟩
  refine ⟨q, hq, fun i ↦ domain_antimonotone (hqp i) (hp i).2⟩


-- @@ L87-89 verbatim
instance Str : Structure L F.Model where
  func _ f _ := IsEmpty.elim' inferInstance f
  rel _ R v := ∀ p ∈ F, (∀ i, p ⊩↓ ↑(v i)) → Rel p R fun i ↦ (v i).val


-- @@ L91-92 verbatim
@[simp] lemma Str.rel_iff {k : ℕ} (R : L.Rel k) (v : Fin k → F.Model) :
    F.Str.rel R v ↔ ∀ p ∈ F, (∀ i, p ⊩↓ ↑(v i)) → Rel p R fun i ↦ (v i).val := by rfl


-- @@ L94-94 verbatim
end Filter


-- @@ L96-96 verbatim
end filter


-- @@ L98-98 verbatim
variable (W)




-- @@ L102-102 verbatim
end KripkeModel


-- @@ L104-104 verbatim
end FFL.FirstOrder
