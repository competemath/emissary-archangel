module
public import Foundation.FirstOrder.Basic.Operator
public import Foundation.FirstOrder.Basic.Semantics.Elementary

-- @@ L4-4 verbatim
@[expose] public section


-- @@ L6-6 verbatim
namespace FFL


-- @@ L8-8 verbatim
namespace FirstOrder


-- @@ L10-10 verbatim
namespace Structure


-- @@ L12-13 verbatim
structure Model (L : Language) (M : Type*) where
  intro : M


-- @@ L15-15 verbatim
namespace Model


-- @@ L17-17 verbatim
variable [Structure L M]


-- @@ L19-23 verbatim
def equiv (L : Language) (M : Type*) : M ≃ Model L M where
  toFun := fun x => ⟨x⟩
  invFun := Model.intro
  left_inv := by intro x; simp
  right_inv := by rintro ⟨x⟩; simp


-- @@ L25-25 verbatim
instance : Structure L (Model L M) := Structure.ofEquiv (equiv L M)


-- @@ L27-28 verbatim
instance [h : Nonempty M] : Nonempty (Model L M) := by
  rcases h with ⟨x⟩; exact ⟨equiv L M x⟩


-- @@ L30-31 verbatim
instance elementaryEquiv (L : Language) (M : Type*) [Nonempty M] [Structure L M] : M ≡ₑ[L] Model L M :=
  ElementaryEquiv.ofEquiv _


-- @@ L33-33 verbatim
section


-- @@ L35-35 verbatim
open Semiterm Semiformula


-- @@ L37-37 verbatim
instance [Operator.Zero L] : Zero (Model L M) := ⟨(@Operator.Zero.zero L _).val ![]⟩


-- @@ L39-39 verbatim
instance [Operator.Zero L] : Structure.Zero L (Model L M) := ⟨rfl⟩


-- @@ L41-41 verbatim
instance [Operator.One L] : One (Model L M) := ⟨(@Operator.One.one L _).val ![]⟩


-- @@ L43-43 verbatim
instance [Operator.One L] : Structure.One L (Model L M) := ⟨rfl⟩


-- @@ L45-46 verbatim
instance [Operator.Add L] : Add (Model L M) :=
  ⟨fun x y => (@Operator.Add.add L _).val ![x, y]⟩


-- @@ L48-48 verbatim
instance [Operator.Add L] : Structure.Add L (Model L M) := ⟨fun _ _ => rfl⟩


-- @@ L50-51 verbatim
instance [Operator.Mul L] : Mul (Model L M) :=
  ⟨fun x y => (@Operator.Mul.mul L _).val ![x, y]⟩


-- @@ L53-53 verbatim
instance [Operator.Mul L] : Structure.Mul L (Model L M) := ⟨fun _ _ => rfl⟩


-- @@ L55-56 verbatim
instance [Operator.Exp L] : Exp (Model L M) :=
  ⟨fun x => (@Operator.Exp.exp L _).val ![x]⟩


-- @@ L58-58 verbatim
instance [Operator.Exp L] : Structure.Exp L (Model L M) := ⟨fun _ => rfl⟩


-- @@ L60-61 verbatim
instance [Operator.Eq L] [Structure.Eq L M] : Structure.Eq L (Model L M) :=
  ⟨fun x y => by simp [operator_val_ofEquiv_iff]⟩


-- @@ L63-64 verbatim
instance [Operator.LT L] : LT (Model L M) :=
  ⟨fun x y => (@Operator.LT.lt L _).val ![x, y]⟩


-- @@ L66-66 verbatim
instance [Operator.LT L] : Structure.LT L (Model L M) := ⟨fun _ _ => iff_of_eq rfl⟩


-- @@ L68-69 verbatim
instance [Operator.Mem L] : Membership (Model L M) (Model L M) :=
  ⟨fun x y => (@Operator.Mem.mem L _).val ![y, x]⟩


-- @@ L71-71 verbatim
instance [Operator.Mem L] : Structure.Mem L (Model L M) := ⟨fun _ _ => iff_of_eq rfl⟩


-- @@ L73-73 verbatim
end


-- @@ L75-75 verbatim
end Model


-- @@ L77-77 verbatim
section ofFunc


-- @@ L79-79 verbatim
variable (F : ℕ → Type*) {M : Type*} (fF : {k : ℕ} → (f : F k) → (Fin k → M) → M)


-- @@ L81-85 verbatim
abbrev ofFunc : Structure (Language.ofFunc F) M where
  func := fun _ f v => fF f v
  rel  := fun _ r _ => r.elim

lemma func_ofFunc {k} (f : F k) (v : Fin k → M) : (ofFunc F fF).func f v = fF f v := rfl


-- @@ L87-87 verbatim
end ofFunc


-- @@ L89-89 verbatim
section add


-- @@ L91-91 verbatim
variable (L₁ : Language.{u₁}) (L₂ : Language.{u₂}) (M : Type*) [str₁ : Structure L₁ M] [str₂ : Structure L₂ M]


-- @@ L93-101 verbatim
instance add : Structure (L₁.add L₂) M where
  func := fun _ f v =>
    match f with
    | Sum.inl f => func f v
    | Sum.inr f => func f v
  rel := fun _ r v =>
    match r with
    | Sum.inl r => rel r v
    | Sum.inr r => rel r v


-- @@ L103-103 verbatim
variable {L₁ L₂ M}


-- @@ L105-106 verbatim
@[simp] lemma func_sigma_inl {k} (f : L₁.Func k) (v : Fin k → M) :
    (add L₁ L₂ M).func (Sum.inl f) v = func f v := rfl


-- @@ L108-109 verbatim
@[simp] lemma func_sigma_inr {k} (f : L₂.Func k) (v : Fin k → M) :
    (add L₁ L₂ M).func (Sum.inr f) v = func f v := rfl


-- @@ L111-112 verbatim
@[simp] lemma rel_sigma_inl {k} (r : L₁.Rel k) (v : Fin k → M) :
    (add L₁ L₂ M).rel (Sum.inl r) v ↔ rel r v := iff_of_eq rfl


-- @@ L114-119 verbatim
@[simp] lemma rel_sigma_inr {k} (r : L₂.Rel k) (v : Fin k → M) :
    (add L₁ L₂ M).rel (Sum.inr r) v ↔ rel r v := iff_of_eq rfl

lemma lMap_add₁ : (add L₁ L₂ M).lMap (Language.Hom.add₁ L₁ L₂) = str₁ := rfl

lemma lMap_add₂ : (add L₁ L₂ M).lMap (Language.Hom.add₂ L₁ L₂) = str₂ := rfl


-- @@ L121-123 verbatim
@[simp] lemma val_lMap_add₁ {n} (t : Semiterm L₁ μ n) (e : Fin n → M) (f : μ → M) :
    Semiterm.val (s := add L₁ L₂ M) e f (t.lMap (Language.Hom.add₁ L₁ L₂)) = t.val (s := str₁) e f := by
  rw [Semiterm.val_lMap, lMap_add₁]


-- @@ L125-127 verbatim
@[simp] lemma val_lMap_add₂ {n} (t : Semiterm L₂ μ n) (e : Fin n → M) (f : μ → M) :
    Semiterm.val (s := add L₁ L₂ M) e f (t.lMap (Language.Hom.add₂ L₁ L₂)) = t.val (s := str₂) e f := by
  rw [Semiterm.val_lMap, lMap_add₂]


-- @@ L129-132 verbatim
@[simp] lemma eval_lMap_add₁ {n} (φ : Semiformula L₁ μ n) (e : Fin n → M) (f : μ → M) :
    (Semiformula.lMap (Language.Hom.add₁ L₁ L₂) φ).Eval (s := add L₁ L₂ M) e f
    ↔ φ.Eval (s := str₁) e f := by
  rw [Semiformula.eval_lMap, lMap_add₁]


-- @@ L134-137 verbatim
@[simp] lemma eval_lMap_add₂ {n} (φ : Semiformula L₂ μ n) (e : Fin n → M) (f : μ → M) :
    (Semiformula.lMap (Language.Hom.add₂ L₁ L₂) φ).Eval (s := add L₁ L₂ M) e f
    ↔ φ.Eval (s := str₂) e f := by
  rw [Semiformula.eval_lMap, lMap_add₂]


-- @@ L139-139 verbatim
end add


-- @@ L141-141 verbatim
section sigma


-- @@ L143-143 verbatim
variable (L : ι → Language) (M : Type*) [str : (i : ι) → Structure (L i) M]


-- @@ L145-147 verbatim
instance sigma : Structure (Language.sigma L) M where
  func := fun _ ⟨_, f⟩ v ↦ func f v
  rel  := fun _ ⟨_, r⟩ v ↦ rel r v


-- @@ L149-149 verbatim
@[simp] lemma func_sigma {k} (f : (L i).Func k) (v : Fin k → M) : (sigma L M).func ⟨i, f⟩ v = func f v := rfl


-- @@ L151-153 verbatim
@[simp] lemma rel_sigma {k} (r : (L i).Rel k) (v : Fin k → M) : (sigma L M).rel ⟨i, r⟩ v ↔ rel r v := iff_of_eq rfl

lemma lMap_sigma : (sigma L M).lMap (Language.Hom.sigma L i) = str i := rfl


-- @@ L155-157 verbatim
@[simp] lemma val_lMap_sigma {n} (t : Semiterm (L i) μ n) (e : Fin n → M) (f : μ → M) :
    Semiterm.val (s := sigma L M) e f (t.lMap (Language.Hom.sigma L i)) = t.val (s := str i) e f := by
  rw [Semiterm.val_lMap, lMap_sigma]


-- @@ L159-162 verbatim
@[simp] lemma eval_lMap_sigma {n} (φ : Semiformula (L i) μ n) (e : Fin n → M) (f : μ → M) :
    (Semiformula.lMap (Language.Hom.sigma L i) φ).Eval (s := sigma L M) e f
    ↔ φ.Eval (s := str i) e f := by
  rw [Semiformula.eval_lMap, lMap_sigma]


-- @@ L164-164 verbatim
end sigma


-- @@ L166-166 verbatim
end Structure


-- @@ L168-168 verbatim
section ULift


-- @@ L170-170 verbatim
variable {L : Language.{u}} {M : Type v} [Structure L M]


-- @@ L172-174 verbatim
instance : Structure L (ULift.{v'} M) where
  func _ f v := ⟨Structure.func f (ULift.down ∘ v)⟩
  rel _ r v := Structure.rel r (ULift.down ∘ v)


-- @@ L176-177 verbatim
@[simp] lemma Structure.func_uLift {k} (f : L.Func k) (v : Fin k → ULift.{v'} M) :
    Structure.func f v = ⟨Structure.func f (ULift.down ∘ v)⟩ := rfl


-- @@ L179-189 verbatim
@[simp] lemma Structure.rel_uLift {k} (r : L.Rel k) (v : Fin k → ULift.{v'} M) :
    Structure.rel r v = Structure.rel r (ULift.down ∘ v) := rfl

lemma Semiterm.val_uLift {e : Fin n → ULift.{v'} M} {f : ξ → ULift.{v'} M} {t : Semiterm L ξ n} :
    Semiterm.val e f t = ⟨Semiterm.val (ULift.down ∘ e) (ULift.down ∘ f) t⟩ := by
  induction t <;> simp [*, Function.comp_def]

lemma Semiformula.eval_uLift {e : Fin n → ULift.{v'} M} {f : ξ → ULift.{v'} M} {φ : Semiformula L ξ n} :
    φ.Eval e f ↔ φ.Eval (ULift.down ∘ e) (ULift.down ∘ f) := by
  induction φ using Semiformula.rec' <;>
    simp [*, Semiterm.val_uLift, Matrix.comp_vecCons', Function.comp_def]


-- @@ L191-194 verbatim
variable (L M)

lemma uLift_elementaryEquiv [Nonempty M] : ULift.{v'} M ≡ₑ[L] M := ⟨by
  intro σ; simp [models_iff, Semiformula.eval_uLift, Matrix.empty_eq, Empty.eq_elim]⟩


-- @@ L196-196 verbatim
end ULift


-- @@ L198-198 verbatim
end FirstOrder


-- @@ L200-200 verbatim
end FFL


-- @@ L202-202 verbatim
end
