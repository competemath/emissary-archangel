module

public import Foundation.FirstOrder.SetTheory.Basic.Axioms


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-6 verbatim
/-! # Basic properties of model of set theory-/


-- @@ L8-8 verbatim
namespace FFL.FirstOrder.SetTheory


-- @@ L10-10 verbatim
variable {V : Type*} [SetStructure V]


-- @@ L12-14 verbatim
scoped instance : HasSubset V := ⟨fun x y ↦ ∀ z ∈ x, z ∈ y⟩

lemma subset_def {a b : V} : a ⊆ b ↔ ∀ x ∈ a, x ∈ b := by rfl


-- @@ L16-17 verbatim
instance Subset.defined_isSubsetOf : ℒₛₑₜ-relation[V] Subset via isSubsetOf :=
  ⟨fun v ↦ by simp [isSubsetOf, subset_def]⟩


-- @@ L19-19 verbatim
instance Subset.definable : ℒₛₑₜ-relation[V] Subset := defined_isSubsetOf.to_definable


-- @@ L21-21 verbatim
@[simp, refl] lemma subset_refl (x : V) : x ⊆ x := by simp [subset_def]


-- @@ L23-23 verbatim
@[simp, trans] lemma subset_trans {x y z : V} : x ⊆ y → y ⊆ z → x ⊆ z := fun hxy hyz v hv ↦ hyz v (hxy v hv)


-- @@ L25-25 verbatim
instance : Std.Refl (α := V) Subset := ⟨subset_refl⟩


-- @@ L27-27 verbatim
instance : IsTrans V Subset := ⟨fun _ _ _ ↦ subset_trans⟩


-- @@ L29-31 verbatim
def IsEmpty (a : V) : Prop := ∀ x, x ∉ a

lemma IsEmpty.not_mem {a x : V} (h : IsEmpty a) : x ∉ a := h x


-- @@ L33-34 verbatim
instance IsEmpty.defined : ℒₛₑₜ-predicate[V] IsEmpty via isEmpty :=
  ⟨fun v ↦ by simp [isEmpty, IsEmpty]⟩


-- @@ L36-36 verbatim
instance IsEmpty.definable : ℒₛₑₜ-predicate[V] IsEmpty := defined.to_definable


-- @@ L38-41 verbatim
class IsNonempty (a : V) : Prop where
  nonempty : ∃ x, x ∈ a

lemma isNonempty_def {x : V} : IsNonempty x ↔ ∃ y, y ∈ x := ⟨fun h ↦ h.nonempty, fun h ↦ ⟨h⟩⟩


-- @@ L43-44 verbatim
instance IsNonempty.defined_isNonempty : ℒₛₑₜ-predicate[V] IsNonempty via isNonempty :=
  ⟨fun v ↦ by simp [isNonempty, isNonempty_def]⟩


-- @@ L46-46 verbatim
instance IsNonempty.definable : ℒₛₑₜ-predicate[V] IsNonempty := defined_isNonempty.to_definable


-- @@ L48-49 verbatim
@[simp] lemma not_isEmpty_iff_isNonempty {x : V} :
    ¬IsEmpty x ↔ IsNonempty x := by simp [IsEmpty, isNonempty_def]


-- @@ L51-52 verbatim
@[simp] lemma not_isNonempty_iff_isEmpty {x : V} :
    ¬IsNonempty x ↔ IsEmpty x := by simp [IsEmpty, isNonempty_def]


-- @@ L54-54 verbatim
scoped instance : CoeSort V (Type _) := ⟨fun x ↦ {z : V // z ∈ x}⟩


-- @@ L56-56 verbatim
def SSubset (x y : V) : Prop := x ⊆ y ∧ x ≠ y


-- @@ L58-60 verbatim
infix:50 " ⊊ " => SSubset

lemma ssubset_def {x y : V} : x ⊊ y ↔ x ⊆ y ∧ x ≠ y := by rfl


-- @@ L62-62 verbatim
def SSubset.dfn : SetTheorySemisentence 2 := “x y. x ⊆ y ∧ x ≠ y”


-- @@ L64-64 verbatim
instance SSubset.defined : ℒₛₑₜ-relation[V] SSubset via SSubset.dfn := ⟨fun v ↦ by simp [ssubset_def, SSubset.dfn]⟩


-- @@ L66-66 verbatim
instance SSubset.definable : ℒₛₑₜ-relation[V] SSubset := SSubset.defined.to_definable


-- @@ L68-74 verbatim
@[simp] lemma SSubset.irrefl (x : V) : ¬x ⊊ x := by simp [ssubset_def]

lemma SSubset.subset {x y : V} : x ⊊ y → x ⊆ y := fun h ↦ h.1

lemma val_isSucc_iff {v : Fin 2 → V} :
    V ⊧/v isSucc ↔ ∀ z, z ∈ v 0 ↔ z = v 1 ∨ z ∈ v 1 := by
  simp [isSucc]


-- @@ L76-76 verbatim
section


-- @@ L78-78 verbatim
variable [Nonempty V]


-- @@ L80-80 verbatim
instance [V↓[ℒₛₑₜ] ⊧* 𝗭] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] : V↓[ℒₛₑₜ] ⊧* 𝗭𝗖 := inferInstance


-- @@ L82-82 verbatim
instance [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] [V↓[ℒₛₑₜ] ⊧* 𝗔𝗖] : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖 := inferInstance


-- @@ L84-84 verbatim
instance [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙] : V↓[ℒₛₑₜ] ⊧* 𝗭 := models_of_subtheory (inferInstance : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙)


-- @@ L86-86 verbatim
instance [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖] : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙 := models_of_subtheory (inferInstance : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖)


-- @@ L88-88 verbatim
instance [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖] : V↓[ℒₛₑₜ] ⊧* 𝗭 := models_of_subtheory (inferInstance : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖)


-- @@ L90-90 verbatim
instance [V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖] : V↓[ℒₛₑₜ] ⊧* 𝗔𝗖 := models_of_subtheory (inferInstance : V↓[ℒₛₑₜ] ⊧* 𝗭𝗙𝗖)


-- @@ L92-92 verbatim
instance : V↓[ℒₛₑₜ] ⊧* (𝗘𝗤 _ : SetTheory) := Structure.Eq.models_eqAxiom' ℒₛₑₜ V


-- @@ L94-94 verbatim
end


-- @@ L96-96 verbatim
section


-- @@ L98-98 verbatim
variable {U : Set V}


-- @@ L100-103 verbatim
instance submodel (U : Set V) : SetStructure U := ⟨fun y x ↦ x.val ∈ y.val⟩

lemma submodel_mem_iff {x y : U} :
    x ∈ y ↔ x.val ∈ y.val := by rfl


-- @@ L105-106 verbatim
@[simp] lemma mk_mem_mk_iff_mem {x y : V} {hx hy} :
    (⟨x, hx⟩ : U) ∈ (⟨y, hy⟩ : U) ↔ x ∈ y := by rfl


-- @@ L108-108 verbatim
end


-- @@ L110-110 verbatim
end FFL.FirstOrder.SetTheory
