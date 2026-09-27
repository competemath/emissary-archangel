/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.FirstOrder.Basic.Semantics.Semantics
import Mathlib.Tactic.Bound.Init


-- @@ L11-11 verbatim
/-! # Elementary -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
namespace LO


-- @@ L18-18 verbatim
namespace FirstOrder


-- @@ L20-20 verbatim
section «lp_section_1»


-- @@ L22-22 verbatim
variable {L : Language}

-- @@ L23-23 verbatim
variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

-- @@ L24-25 verbatim
variable [Nonempty M] [Nonempty M₁] [Nonempty M₂] [Nonempty M₃]
  [s : Structure L M] [s₁ : Structure L M₁] [s₂ : Structure L M₂] [s₃ : Structure L M₃]


-- @@ L27-27 verbatim
namespace Structure


-- @@ L29-29 verbatim
variable (L M M₁ M₂ M₃)


-- @@ L31-36 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
structure Hom where
  /-- Imported declaration from the Incompleteness formalization. -/
  toFun : M₁ → M₂
  func' : ∀ {k} (f : L.Func k) (v : Fin k → M₁), toFun (s₁.func f v) = s₂.func f (toFun ∘ v)
  rel' : ∀ {k} (r : L.Rel k) (v : Fin k → M₁), s₁.rel r v → s₂.rel r (toFun ∘ v)


-- @@ L38-39 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:25 M " →ₛ[" L "] " M' => Hom L M M'


-- @@ L41-44 expanded
/-- Imported declaration from the Incompleteness formalization. -/
structure Embedding extends Hom L M₁ M₂ where
  toFun_inj : Function.Injective toFun
  rel_inv' {k} (r : L.Rel k) (v : Fin k → M₁) : s₂.rel r (toFun ∘ v) → s₁.rel r v


-- @@ L46-47 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:25 M " ↪ₛ[" L "] " M' => Embedding L M M'


-- @@ L49-51 expanded
/-- Imported declaration from the Incompleteness formalization. -/
structure Iso extends Embedding L M₁ M₂ where
  toFun_bij : Function.Bijective toFun


-- @@ L53-54 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:25 M " ≃ₛ[" L "] " M' => Iso L M M'


-- @@ L56-61 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[ext] structure ClosedSubset where
  /-- Imported declaration from the Incompleteness formalization. -/
  domain : Set M
  /-- Imported declaration from the Incompleteness formalization. -/
  domain_closed : ∀ {k} (f : L.Func k) {v : Fin k → M}, (∀ i, v i ∈ domain) → s.func f v ∈ domain


-- @@ L63-68 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class HomClass (F : Type*) (L : outParam (Language.{u}))
    (M₁ : outParam (Type*)) (M₂ : outParam (Type*)) [s₁ : Structure L M₁] [s₂ : Structure L M₂]
      [FunLike F M₁ M₂] where
  map_func : ∀ (h : F) {k} (f : L.Func k) (v : Fin k → M₁), h (func f v) = func f (h ∘ v)
  map_rel : ∀ (h : F) {k} (r : L.Rel k) (v : Fin k → M₁), s₁.rel r v → s₂.rel r (h ∘ v)


-- @@ L70-76 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class EmbeddingClass (F : Type*) (L : outParam (Language.{u}))
    (M₁ : outParam (Type*)) (M₂ : outParam (Type*)) [s₁ : Structure L M₁] [s₂ : Structure L M₂]
      [FunLike F M₁ M₂]
    extends HomClass F L M₁ M₂ where
  map_inj (f : F) : Function.Injective f
  map_rel_inv (f : F) {k} (r : L.Rel k) (v : Fin k → M₁) : s₂.rel r (f ∘ v) → s₁.rel r v


-- @@ L78-83 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
class IsoClass (F : Type*) (L : outParam (Language.{u}))
    (M₁ : outParam (Type*)) (M₂ : outParam (Type*)) [s₁ : Structure L M₁] [s₂ : Structure L M₂]
      [FunLike F M₁ M₂]
    extends EmbeddingClass F L M₁ M₂ where
  map_bij (f : F) : Function.Bijective f


-- @@ L85-85 verbatim
variable {L M M₁ M₂ M₃}


-- @@ L87-91 expanded
instance : FunLike (Hom L M₁ M₂) M₁ M₂
    where
  coe := fun φ => φ.toFun
  coe_injective := fun φ ψ h => by
    rcases φ
    simp_all


-- @@ L93-95 expanded
instance : HomClass (Hom L M₁ M₂) L M₁ M₂
    where
  map_func := Hom.func'
  map_rel := Hom.rel'


-- @@ L97-97 verbatim
omit [Nonempty M₁] [Nonempty M₂]

-- @@ L98-99 expanded
@[ext]
lemma _root_.LO.FirstOrder.Structure.Hom.ext (φ ψ : Hom L M₁ M₂) (h : ∀ x, φ x = ψ x) : φ = ψ :=
  DFunLike.ext φ ψ h


-- @@ L101-101 verbatim
namespace HomClass


-- @@ L103-103 verbatim
variable {F : Type*} [FunLike F M₁ M₂] [HomClass F L M₁ M₂] (φ : F)


-- @@ L105-105 verbatim
@[ext] lemma ext (φ ψ : F) (h : ∀ x, φ x = ψ x) : φ = ψ := DFunLike.ext φ ψ h


-- @@ L107-108 verbatim
protected lemma func {k} (f : L.Func k) (v : Fin k → M₁) :
    φ (s₁.func f v) = s₂.func f (φ ∘ v) := map_func φ f v


-- @@ L110-111 verbatim
protected lemma rel {k} (r : L.Rel k) (v : Fin k → M₁) :
    s₁.rel r v → s₂.rel r (φ ∘ v) := map_rel φ r v


-- @@ L113-115 verbatim
lemma val_term (e : Fin n → M₁) (ε : ξ → M₁) (t : Semiterm L ξ n) :
    φ (t.val s₁ e ε) = t.val s₂ (φ ∘ e) (φ ∘ ε) := by
  induction t <;> simp [*, Semiterm.val_func, HomClass.func, Function.comp_def]


-- @@ L117-117 verbatim
end HomClass


-- @@ L119-126 expanded
instance : FunLike (Embedding L M₁ M₂) M₁ M₂
    where
  coe := fun φ => φ.toFun
  coe_injective := fun φ ψ h => by
    rcases φ
    rcases ψ
    simp only [Embedding.mk.injEq] at h ⊢
    ext
    exact congr_fun h _


-- @@ L128-132 expanded
instance : EmbeddingClass (Embedding L M₁ M₂) L M₁ M₂
    where
  map_func := fun φ => φ.func'
  map_rel := fun φ => φ.rel'
  map_inj := Embedding.toFun_inj
  map_rel_inv := fun φ => φ.rel_inv'


-- @@ L134-135 expanded
@[ext]
lemma _root_.LO.FirstOrder.Structure.Embedding.ext (φ ψ : Embedding L M₁ M₂) (h : ∀ x, φ x = ψ x) :
    φ = ψ :=
  DFunLike.ext φ ψ h


-- @@ L137-137 verbatim
namespace EmbeddingClass

-- @@ L138-138 verbatim
open HomClass

-- @@ L139-139 verbatim
variable {F : Type*} [FunLike F M₁ M₂] [EmbeddingClass F L M₁ M₂] (φ : F)


-- @@ L141-144 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def toEmbedding : M₁ ↪ M₂ where
  toFun := φ
  inj'  := map_inj φ


-- @@ L146-147 verbatim
protected lemma func {k} (f : L.Func k) (v : Fin k → M₁) :
    φ (s₁.func f v) = s₂.func f (φ ∘ v) := map_func φ f v


-- @@ L149-150 verbatim
protected lemma rel {k} (r : L.Rel k) (v : Fin k → M₁) :
    s₂.rel r (φ ∘ v) ↔ s₁.rel r v := ⟨map_rel_inv φ r v, HomClass.rel φ r v⟩


-- @@ L152-152 verbatim
end EmbeddingClass


-- @@ L154-161 expanded
instance : FunLike (Iso L M₁ M₂) M₁ M₂
    where
  coe := fun φ => φ.toFun
  coe_injective := fun φ ψ h => by
    rcases φ
    rcases ψ
    simp only [Iso.mk.injEq] at h ⊢
    ext
    exact congr_fun h _


-- @@ L163-168 expanded
instance : IsoClass (Iso L M₁ M₂) L M₁ M₂
    where
  map_func := fun φ => φ.func'
  map_rel := fun φ => φ.rel'
  map_inj := fun φ => φ.toFun_inj
  map_rel_inv := fun φ => φ.rel_inv'
  map_bij := fun φ => φ.toFun_bij


-- @@ L170-171 expanded
@[ext]
lemma _root_.LO.FirstOrder.Structure.Iso.ext (φ ψ : Iso L M₁ M₂) (h : ∀ x, φ x = ψ x) : φ = ψ :=
  DFunLike.ext φ ψ h


-- @@ L173-173 verbatim
namespace IsoClass


-- @@ L175-175 verbatim
end IsoClass


-- @@ L177-177 verbatim
namespace ClosedSubset


-- @@ L179-179 verbatim
variable (u : ClosedSubset L M)


-- @@ L181-182 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
instance : SetLike (ClosedSubset L M) M := ⟨ClosedSubset.domain, fun _ _ ↦ ClosedSubset.ext⟩


-- @@ L184-184 verbatim
omit [Nonempty M]

-- @@ L185-186 verbatim
lemma closed {k} (f : L.Func k) {v : Fin k → M} (hv : ∀ i, v i ∈ u) :
    s.func f v ∈ u := u.domain_closed f hv


-- @@ L188-190 verbatim
instance toStructure (u : ClosedSubset L M) : Structure L u where
  func := fun k f v => ⟨s.func f (fun i ↦ ↑(v i)), u.closed f (by simp)⟩
  rel := fun k r v => s.rel r (fun i ↦ v i)


-- @@ L192-193 verbatim
protected lemma func {k} (f : L.Func k) (v : Fin k → u) :
    u.toStructure.func f v = s.func f (fun i ↦ v i) := rfl


-- @@ L195-196 verbatim
protected lemma rel {k} (r : L.Rel k) (v : Fin k → u) :
    u.toStructure.rel r v ↔ s.rel r (fun i ↦ v i) := of_eq rfl


-- @@ L198-204 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def inclusion : Embedding L u M where
  toFun := Subtype.val
  func' := by simp [ClosedSubset.func, Function.comp_def]
  rel' := by simp [ClosedSubset.rel, Function.comp_def]
  rel_inv' := by simp [ClosedSubset.rel, Function.comp_def]
  toFun_inj := Subtype.val_injective


-- @@ L206-206 verbatim
end ClosedSubset


-- @@ L208-208 verbatim
end Structure


-- @@ L210-210 verbatim
namespace Semiformula

-- @@ L211-211 verbatim
open Structure


-- @@ L213-213 verbatim
variable {F : Type*} [FunLike F M₁ M₂] [EmbeddingClass F L M₁ M₂] (Θ : F)

-- @@ L214-214 verbatim
variable {e₁ : Fin n → M₁} {ε₁ : ξ → M₁}


-- @@ L216-216 verbatim
omit [Nonempty M₁] [Nonempty M₂]

-- @@ L217-224 expanded
lemma eval_hom_iff_of_open {n} {e₁ : Fin n → M₁} {ε₁ : ξ → M₁} :
    {φ : Semiformula L ξ n} → φ.Open → (Eval s₁ e₁ ε₁ φ ↔ Eval s₂ (Θ ∘ e₁) (Θ ∘ ε₁) φ)
  | ⊤, _ => by simp
  | ⊥, _ => by simp
  | rel r v, _ => by simp [Function.comp_def, eval_rel, ← EmbeddingClass.rel Θ, HomClass.val_term]
  | nrel r v, _ => by simp [Function.comp_def, eval_nrel, ← EmbeddingClass.rel Θ, HomClass.val_term]
  | Wedge.wedge φ ψ, h => by simp at h ⊢; simp [eval_hom_iff_of_open h.1, eval_hom_iff_of_open h.2]
  | Vee.vee φ ψ, h => by simp at h ⊢; simp [eval_hom_iff_of_open h.1, eval_hom_iff_of_open h.2]


-- @@ L226-230 expanded
lemma eval_hom_univClosure {n} {ε₁ : ξ → M₁} {φ : Semiformula L ξ n} (hp : φ.Open) :
    Evalf s₂ (Θ ∘ ε₁) (univClosure φ) → Evalf s₁ ε₁ (univClosure φ) :=
  by
  simp only [eval_univClosure]
  intro h e₁
  exact (eval_hom_iff_of_open Θ hp).mpr (h (Θ ∘ e₁))


-- @@ L232-232 verbatim
end Semiformula


-- @@ L234-234 verbatim
end «lp_section_1»


-- @@ L236-236 verbatim
section «lp_section_2»


-- @@ L238-238 verbatim
variable {L : Language} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

-- @@ L239-240 verbatim
variable [Nonempty M] [Nonempty M₁] [Nonempty M₂] [Nonempty M₃]
  [s : Structure L M] [s₁ : Structure L M₁] [s₂ : Structure L M₂] [s₃ : Structure L M₃]


-- @@ L242-242 verbatim
namespace Structure


-- @@ L244-244 verbatim
variable (L M₁ M₂)


-- @@ L246-247 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def ElementaryEquiv : Prop :=
  ∀ φ : SyntacticFormula L, Models M₁ φ ↔ Models M₂ φ


-- @@ L249-250 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
notation:50 M₁ " ≡ₑ[" L "] " M₂ => ElementaryEquiv L M₁ M₂


-- @@ L252-252 verbatim
variable {L M₁ M₂}


-- @@ L254-254 verbatim
namespace ElementaryEquiv


-- @@ L256-257 expanded
@[refl]
lemma refl (M) [Nonempty M] [Structure L M] : ElementaryEquiv L M M := fun σ => by rfl


-- @@ L259-260 expanded
@[symm]
lemma symm : (ElementaryEquiv L M₁ M₂) → (ElementaryEquiv L M₂ M₁) := fun h σ => (h σ).symm


-- @@ L262-264 expanded
@[trans]
lemma trans : (ElementaryEquiv L M₁ M₂) → (ElementaryEquiv L M₂ M₃) → (ElementaryEquiv L M₁ M₃) :=
  fun h₁ h₂ σ => Iff.trans (h₁ σ) (h₂ σ)


-- @@ L266-267 expanded
lemma models (h : ElementaryEquiv L M₁ M₂) :
    ∀ {φ : SyntacticFormula L}, Models M₁ φ ↔ Models M₂ φ :=
  @h


-- @@ L269-270 expanded
lemma modelsTheory (h : ElementaryEquiv L M₁ M₂) {T : Theory L} :
    ModelsTheory M₁ T ↔ ModelsTheory M₂ T := by simp [modelsTheory_iff, h.models]


-- @@ L272-282 expanded
lemma ofEquiv [Nonempty N] (Θ : M ≃ N) :
    letI : Structure L N := Structure.ofEquiv Θ
    ElementaryEquiv L M N :=
  fun φ => by
  let : Structure L N := Structure.ofEquiv Θ
  rw [models_iff, models_iff]
  constructor
  · intro h f
    exact (Structure.evalf_ofEquiv_iff (Θ := Θ)).mpr (h _)
  · intro h f
    have := (Structure.evalf_ofEquiv_iff (Θ := Θ) (ε := Θ ∘ f)).mp (h (Θ ∘ f))
    simpa [← Function.comp_assoc] using this


-- @@ L284-284 verbatim
end ElementaryEquiv


-- @@ L286-286 verbatim
end Structure


-- @@ L288-288 verbatim
end «lp_section_2»


-- @@ L290-290 verbatim
end FirstOrder


-- @@ L292-292 verbatim
end LO
