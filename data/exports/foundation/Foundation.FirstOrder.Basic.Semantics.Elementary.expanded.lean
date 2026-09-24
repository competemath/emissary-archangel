module

public import Foundation.FirstOrder.Basic.Semantics.Semantics


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-7 verbatim
namespace FFL.FirstOrder


-- @@ L9-9 verbatim
section


-- @@ L11-11 verbatim
variable {L : Language}

-- @@ L12-12 verbatim
variable {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

-- @@ L13-14 verbatim
variable [Nonempty M] [Nonempty M₁] [Nonempty M₂] [Nonempty M₃]
  [s : Structure L M] [s₁ : Structure L M₁] [s₂ : Structure L M₂] [s₃ : Structure L M₃]


-- @@ L16-16 verbatim
namespace Structure


-- @@ L18-18 verbatim
variable (L M M₁ M₂ M₃)


-- @@ L20-23 verbatim
structure Hom where
  toFun : M₁ → M₂
  func' : ∀ {k} (f : L.Func k) (v : Fin k → M₁), toFun (s₁.func f v) = s₂.func f (toFun ∘ v)
  rel' : ∀ {k} (r : L.Rel k) (v : Fin k → M₁), s₁.rel r v → s₂.rel r (toFun ∘ v)


-- @@ L25-25 verbatim
notation:25 M " →ₛ[" L "] " M' => Hom L M M'


-- @@ L27-29 verbatim
structure Embedding extends M₁ →ₛ[L] M₂ where
  toFun_inj : Function.Injective toFun
  rel_inv' {k} (r : L.Rel k) (v : Fin k → M₁) : s₂.rel r (toFun ∘ v) → s₁.rel r v


-- @@ L31-31 verbatim
notation:25 M " ↪ₛ[" L "] " M' => Embedding L M M'


-- @@ L33-34 verbatim
structure Iso extends M₁ ↪ₛ[L] M₂ where
  toFun_bij : Function.Bijective toFun


-- @@ L36-36 verbatim
notation:25 M " ≃ₛ[" L "] " M' => Iso L M M'


-- @@ L38-40 verbatim
@[ext] structure ClosedSubset where
  domain : Set M
  domain_closed : ∀ {k} (f : L.Func k) {v : Fin k → M}, (∀ i, v i ∈ domain) → s.func f v ∈ domain


-- @@ L42-45 verbatim
class HomClass (F : Type*) (L : outParam (Language.{u}))
    (M₁ : outParam (Type*)) (M₂ : outParam (Type*)) [s₁ : Structure L M₁] [s₂ : Structure L M₂] [FunLike F M₁ M₂] where
  map_func : ∀ (h : F) {k} (f : L.Func k) (v : Fin k → M₁), h (func f v) = func f (h ∘ v)
  map_rel : ∀ (h : F) {k} (r : L.Rel k) (v : Fin k → M₁), s₁.rel r v → s₂.rel r (h ∘ v)


-- @@ L47-51 verbatim
class EmbeddingClass (F : Type*) (L : outParam (Language.{u}))
    (M₁ : outParam (Type*)) (M₂ : outParam (Type*)) [s₁ : Structure L M₁] [s₂ : Structure L M₂] [FunLike F M₁ M₂]
    extends HomClass F L M₁ M₂ where
  map_inj (f : F) : Function.Injective f
  map_rel_inv (f : F) {k} (r : L.Rel k) (v : Fin k → M₁) : s₂.rel r (f ∘ v) → s₁.rel r v


-- @@ L53-56 verbatim
class IsoClass (F : Type*) (L : outParam (Language.{u}))
    (M₁ : outParam (Type*)) (M₂ : outParam (Type*)) [s₁ : Structure L M₁] [s₂ : Structure L M₂] [FunLike F M₁ M₂]
    extends EmbeddingClass F L M₁ M₂ where
  map_bij (f : F) : Function.Bijective f


-- @@ L58-58 verbatim
variable {L M M₁ M₂ M₃}


-- @@ L60-65 verbatim
instance : FunLike (M₁ →ₛ[L] M₂) M₁ M₂ where
  coe := fun φ => φ.toFun
  coe_injective := fun φ ψ h => by
    rcases φ; rcases ψ
    simp only [Hom.mk.injEq] at h ⊢
    ext; exact congr_fun h _


-- @@ L67-69 verbatim
instance : HomClass (M₁ →ₛ[L] M₂) L M₁ M₂ where
  map_func := Hom.func'
  map_rel := Hom.rel'


-- @@ L71-71 verbatim
omit [Nonempty M₁] [Nonempty M₂]

-- @@ L72-72 verbatim
@[ext] lemma Hom.ext (φ ψ : M₁ →ₛ[L] M₂) (h : ∀ x, φ x = ψ x) : φ = ψ := DFunLike.ext φ ψ h


-- @@ L74-74 verbatim
namespace HomClass


-- @@ L76-76 verbatim
variable {F : Type*} [FunLike F M₁ M₂] [HomClass F L M₁ M₂] (φ : F)


-- @@ L78-78 verbatim
@[ext] lemma ext (φ ψ : F) (h : ∀ x, φ x = ψ x) : φ = ψ := DFunLike.ext φ ψ h


-- @@ L80-81 verbatim
protected lemma func {k} (f : L.Func k) (v : Fin k → M₁) :
    φ (s₁.func f v) = s₂.func f (φ ∘ v) := map_func φ f v


-- @@ L83-88 verbatim
protected lemma rel {k} (r : L.Rel k) (v : Fin k → M₁) :
    s₁.rel r v → s₂.rel r (φ ∘ v) := map_rel φ r v

lemma val_term (e : Fin n → M₁) (ε : ξ → M₁) (t : Semiterm L ξ n) :
    φ (t.val e ε) = t.val (φ ∘ e) (φ ∘ ε) := by
  induction t <;> simp [*, HomClass.func, Function.comp_def]


-- @@ L90-90 verbatim
end HomClass


-- @@ L92-95 verbatim
instance : FunLike (M₁ ↪ₛ[L] M₂) M₁ M₂ where
  coe := fun φ => φ.toFun
  coe_injective := fun φ ψ h => by
    rcases φ; rcases ψ; simp only [Embedding.mk.injEq] at h ⊢; ext; exact congr_fun h _


-- @@ L97-101 verbatim
instance : EmbeddingClass (M₁ ↪ₛ[L] M₂) L M₁ M₂ where
  map_func := fun φ => φ.func'
  map_rel := fun φ => φ.rel'
  map_inj := Embedding.toFun_inj
  map_rel_inv := fun φ => φ.rel_inv'


-- @@ L103-103 verbatim
@[ext] lemma Embedding.ext (φ ψ : M₁ ↪ₛ[L] M₂) (h : ∀ x, φ x = ψ x) : φ = ψ := DFunLike.ext φ ψ h


-- @@ L105-105 verbatim
namespace EmbeddingClass

-- @@ L106-106 verbatim
open HomClass

-- @@ L107-107 verbatim
variable {F : Type*} [FunLike F M₁ M₂] [EmbeddingClass F L M₁ M₂] (φ : F)


-- @@ L109-111 verbatim
def toEmbedding : M₁ ↪ M₂ where
  toFun := φ
  inj'  := map_inj φ


-- @@ L113-114 verbatim
protected lemma func {k} (f : L.Func k) (v : Fin k → M₁) :
    φ (s₁.func f v) = s₂.func f (φ ∘ v) := map_func φ f v


-- @@ L116-117 verbatim
protected lemma rel {k} (r : L.Rel k) (v : Fin k → M₁) :
    s₂.rel r (φ ∘ v) ↔ s₁.rel r v := ⟨map_rel_inv φ r v, HomClass.rel φ r v⟩


-- @@ L119-119 verbatim
end EmbeddingClass


-- @@ L121-124 verbatim
instance : FunLike (M₁ ≃ₛ[L] M₂) M₁ M₂ where
  coe := fun φ => φ.toFun
  coe_injective := fun φ ψ h => by
    rcases φ; rcases ψ; simp only [Iso.mk.injEq] at h ⊢; ext; exact congr_fun h _


-- @@ L126-131 verbatim
instance : IsoClass (M₁ ≃ₛ[L] M₂) L M₁ M₂ where
  map_func := fun φ => φ.func'
  map_rel := fun φ => φ.rel'
  map_inj := fun φ => φ.toFun_inj
  map_rel_inv := fun φ => φ.rel_inv'
  map_bij := fun φ => φ.toFun_bij


-- @@ L133-133 verbatim
@[ext] lemma Iso.ext (φ ψ : M₁ ≃ₛ[L] M₂) (h : ∀ x, φ x = ψ x) : φ = ψ := DFunLike.ext φ ψ h


-- @@ L135-135 verbatim
namespace IsoClass


-- @@ L137-137 verbatim
end IsoClass


-- @@ L139-139 verbatim
namespace ClosedSubset


-- @@ L141-141 verbatim
variable (u : ClosedSubset L M)


-- @@ L143-143 verbatim
instance : SetLike (ClosedSubset L M) M := ⟨ClosedSubset.domain, fun _ _ ↦ ClosedSubset.ext⟩


-- @@ L145-146 verbatim
omit [Nonempty M]
lemma closed {k} (f : L.Func k) {v : Fin k → M} (hv : ∀ i, v i ∈ u) : s.func f v ∈ u := u.domain_closed f hv


-- @@ L148-150 verbatim
instance toStructure (u : ClosedSubset L M) : Structure L u where
  func := fun k f v => ⟨s.func f (fun i ↦ ↑(v i)), u.closed f (by simp)⟩
  rel := fun k r v => s.rel r (fun i ↦ v i)


-- @@ L152-152 verbatim
protected lemma func {k} (f : L.Func k) (v : Fin k → u) : u.toStructure.func f v = s.func f (fun i ↦ v i) := rfl


-- @@ L154-154 verbatim
protected lemma rel {k} (r : L.Rel k) (v : Fin k → u) : u.toStructure.rel r v ↔ s.rel r (fun i ↦ v i) := of_eq rfl


-- @@ L156-161 verbatim
def inclusion : u ↪ₛ[L] M where
  toFun := Subtype.val
  func' := by simp [ClosedSubset.func, Function.comp_def]
  rel' := by simp [ClosedSubset.rel, Function.comp_def]
  rel_inv' := by simp [ClosedSubset.rel, Function.comp_def]
  toFun_inj := Subtype.val_injective


-- @@ L163-163 verbatim
end ClosedSubset


-- @@ L165-165 verbatim
end Structure


-- @@ L167-167 verbatim
namespace Semiformula

-- @@ L168-168 verbatim
open Structure


-- @@ L170-170 verbatim
variable {F : Type*} [FunLike F M₁ M₂] [EmbeddingClass F L M₁ M₂] (Θ : F)

-- @@ L171-171 verbatim
variable {e₁ : Fin n → M₁} {ε₁ : ξ → M₁}



-- @@ L174-185 verbatim
omit [Nonempty M₁] [Nonempty M₂]
lemma eval_hom_iff_of_open {n} {e₁ : Fin n → M₁} {ε₁ : ξ → M₁} {φ : Semiformula L ξ n} (h : φ.Open) :
    φ.Eval e₁ ε₁ ↔ φ.Eval (Θ ∘ e₁) (Θ ∘ ε₁) :=
  match φ with
  | rel r v | nrel r v => by simp [Function.comp_def, ←EmbeddingClass.rel Θ, HomClass.val_term]
  | ⊤ | ⊥ => by simp
  | φ ⋏ ψ | φ ⋎ ψ => by simp at h ⊢; simp [eval_hom_iff_of_open h.1, eval_hom_iff_of_open h.2]

lemma eval_hom_allClosure {n} {ε₁ : ξ → M₁} {φ : Semiformula L ξ n} (hp : φ.Open) :
    (∀¹* φ).Evalf (Θ ∘ ε₁) → (∀¹* φ).Evalf ε₁ := by
  simp only [eval_allClosure]
  intro h e₁; exact (eval_hom_iff_of_open Θ hp).mpr (h (Θ ∘ e₁))


-- @@ L187-187 verbatim
end Semiformula


-- @@ L189-189 verbatim
end


-- @@ L191-191 verbatim
section


-- @@ L193-193 verbatim
variable {L : Language} {M : Type*} {M₁ : Type*} {M₂ : Type*} {M₃ : Type*}

-- @@ L194-195 verbatim
variable [Nonempty M] [Nonempty M₁] [Nonempty M₂] [Nonempty M₃]
  [s : Structure L M] [s₁ : Structure L M₁] [s₂ : Structure L M₂] [s₃ : Structure L M₃]


-- @@ L197-197 verbatim
namespace Structure


-- @@ L199-199 verbatim
variable (L M₁ M₂)


-- @@ L201-202 verbatim
class ElementaryEquiv : Prop where
  models {φ : Sentence L} : M₁↓[L] ⊧ φ ↔ M₂↓[L] ⊧ φ


-- @@ L204-204 verbatim
notation:50 M₁ " ≡ₑ[" L "] " M₂ => ElementaryEquiv L M₁ M₂


-- @@ L206-206 verbatim
variable {L M₁ M₂}


-- @@ L208-208 verbatim
namespace ElementaryEquiv


-- @@ L210-210 verbatim
@[refl] instance refl (M) [Nonempty M] [Structure L M] : M ≡ₑ[L] M := ⟨by rfl⟩


-- @@ L212-212 verbatim
@[symm] lemma symm : (M₁ ≡ₑ[L] M₂) → (M₂ ≡ₑ[L] M₁) := fun h ↦ ⟨h.models.symm⟩


-- @@ L214-218 verbatim
@[trans] lemma trans : (M₁ ≡ₑ[L] M₂) → (M₂ ≡ₑ[L] M₃) → (M₁ ≡ₑ[L] M₃) :=
  fun h₁ h₂ ↦ ⟨Iff.trans h₁.models h₂.models⟩

lemma modelsTheory [h : M₁ ≡ₑ[L] M₂] {T : Theory L} :
    M₁↓[L] ⊧* T ↔ M₂↓[L] ⊧* T := by simp [models_theory_iff, h.models]


-- @@ L220-223 verbatim
variable (M₁ M₂)

lemma modelsTheory' [M₁ ≡ₑ[L] M₂] (T : Theory L) [h : M₂↓[L] ⊧* T] :
    M₁↓[L] ⊧* T := modelsTheory.mpr h


-- @@ L225-231 verbatim
variable {M₁ M₂}

lemma ofEquiv [Nonempty N] (Θ : M ≃ N) :
    letI : Structure L N := Structure.ofEquiv Θ
    M ≡ₑ[L] N :=
  letI : Structure L N := Structure.ofEquiv Θ
  ⟨by simp [models_iff, Empty.eq_elim, Structure.evalf_ofEquiv_iff (Θ := Θ)]⟩


-- @@ L233-246 verbatim
omit [Nonempty M₁] [Nonempty M₂] in
lemma val_eq_of_equiv {f₁ f₂ b₁ b₂}
    (I : M₁ ≃ M₂)
    (hf : ∀ x, I (f₁ x) = f₂ x) (hb : ∀ x, I (b₁ x) = b₂ x)
    (hfunc : ∀ {k} (f : L.Func k) {v₁ : Fin k → M₁} {v₂ : Fin k → M₂}, (∀ i, I (v₁ i) = v₂ i) → I (s₁.func f v₁) = s₂.func f v₂)
    (t : Semiterm L ξ n) :
    I (t.val b₁ f₁) = t.val b₂ f₂ :=
  match t with
  | #x => by simp [hb]
  | &x => by simp [hf]
  | .func f v => by
    have ih : ∀ i, I ((v i).val b₁ f₁) = (v i).val b₂ f₂ := fun i ↦
      val_eq_of_equiv I hf hb hfunc (v i)
    simp [hfunc, ih, Function.comp_def]


-- @@ L248-306 verbatim
omit [Nonempty M₁] [Nonempty M₂] in
lemma eval_iff_of_equiv {f₁ f₂ b₁ b₂}
    (I : M₁ ≃ M₂)
    (hf : ∀ x, I (f₁ x) = f₂ x) (hb : ∀ x, I (b₁ x) = b₂ x)
    (hrel : ∀ {k} (R : L.Rel k) {v₁ : Fin k → M₁} {v₂ : Fin k → M₂}, (∀ i, I (v₁ i) = v₂ i) → (s₁.rel R v₁ ↔ s₂.rel R v₂))
    (hfunc : ∀ {k} (f : L.Func k) {v₁ : Fin k → M₁} {v₂ : Fin k → M₂}, (∀ i, I (v₁ i) = v₂ i) → I (s₁.func f v₁) = s₂.func f v₂)
    (φ : Semiformula L ξ n) :
    φ.Eval b₁ f₁ ↔ φ.Eval b₂ f₂ :=
  match φ with
  | .rel R v => by
    simpa [Function.comp_def] using hrel R fun i ↦ val_eq_of_equiv I hf hb hfunc (v i)
  | .nrel R v => by
    simpa [Function.comp_def] using not_congr <| hrel R fun i ↦ val_eq_of_equiv I hf hb hfunc (v i)
  | ⊤ => by simp
  | ⊥ => by simp
  | φ ⋏ ψ => by
    simp [eval_iff_of_equiv I hf hb hrel hfunc φ, eval_iff_of_equiv I hf hb hrel hfunc ψ]
  | φ ⋎ ψ => by
    simp [eval_iff_of_equiv I hf hb hrel hfunc φ, eval_iff_of_equiv I hf hb hrel hfunc ψ]
  | ∀¹ φ => by
    suffices
      (∀ x₁ : M₁, φ.Eval (x₁ :> b₁) f₁) ↔ (∀ x₂ : M₂, φ.Eval (x₂ :> b₂) f₂) by simpa
    constructor
    · intro h x₂
      have : φ.Eval (I.symm x₂ :> b₁) f₁ ↔ φ.Eval (x₂ :> b₂) f₂ :=
        eval_iff_of_equiv I (b₁ := I.symm x₂ :> b₁) (b₂ := x₂ :> b₂) hf
          (by intro i; cases i using Fin.cases <;> simp [hb])
          hrel hfunc φ
      exact this.mp (h (I.symm x₂))
    · intro h x₁
      have : φ.Eval (x₁ :> b₁) f₁ ↔ φ.Eval (I x₁ :> b₂) f₂ :=
        eval_iff_of_equiv I (b₁ := x₁ :> b₁) (b₂ := I x₁ :> b₂) hf
          (by intro i; cases i using Fin.cases <;> simp [hb])
          hrel hfunc φ
      exact this.mpr (h _)
  | ∃¹ φ => by
    suffices
      (∃ x₁, φ.Eval (x₁ :> b₁) f₁) ↔ (∃ x₂, φ.Eval (x₂ :> b₂) f₂) by simpa
    constructor
    · rintro ⟨x₁, h⟩
      have : φ.Eval (x₁ :> b₁) f₁ ↔ φ.Eval (I x₁ :> b₂) f₂ :=
        eval_iff_of_equiv I (b₁ := x₁ :> b₁) (b₂ := I x₁ :> b₂) hf
          (by intro i; cases i using Fin.cases <;> simp [hb])
          hrel hfunc φ
      exact ⟨I x₁, this.mp h⟩
    · rintro ⟨x₂, h⟩
      have : φ.Eval (I.symm x₂ :> b₁) f₁ ↔ φ.Eval (x₂ :> b₂) f₂ :=
        eval_iff_of_equiv I (b₁ := I.symm x₂ :> b₁) (b₂ := x₂ :> b₂) hf
          (by intro i; cases i using Fin.cases <;> simp [hb])
          hrel hfunc φ
      exact ⟨I.symm x₂, this.mpr h⟩

lemma of_equiv
    (I : M₁ ≃ M₂)
    (hrel : ∀ {k} (R : L.Rel k) {v₁ : Fin k → M₁} {v₂ : Fin k → M₂}, (∀ i, I (v₁ i) = v₂ i) → (s₁.rel R v₁ ↔ s₂.rel R v₂))
    (hfunc : ∀ {k} (f : L.Func k) {v₁ : Fin k → M₁} {v₂ : Fin k → M₂}, (∀ i, I (v₁ i) = v₂ i) → I (s₁.func f v₁) = s₂.func f v₂) :
    M₁ ≡ₑ[L] M₂ := ⟨fun {φ} ↦
  eval_iff_of_equiv
    (b₁ := ![]) (b₂ := ![]) (f₁ := Empty.elim) (f₂ := Empty.elim) I (by simp) (by simp) hrel hfunc φ⟩


-- @@ L308-308 verbatim
end ElementaryEquiv


-- @@ L310-310 verbatim
end Structure


-- @@ L312-312 verbatim
end


-- @@ L314-314 verbatim
end  FFL.FirstOrder

-- @@ L315-315 verbatim
end
