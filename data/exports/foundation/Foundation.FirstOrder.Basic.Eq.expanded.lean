module
public import Foundation.FirstOrder.Basic.BinderNotation
public import Foundation.FirstOrder.Basic.Semantics.Elementary
public import Foundation.FirstOrder.Basic.Soundness
public import Foundation.Vorspiel.Quotient
public import Foundation.Vorspiel.Finset.Card


-- @@ L8-8 verbatim
@[expose] public section


-- @@ L10-10 verbatim
namespace Matrix


-- @@ L12-12 verbatim
variable {α : Type*}


-- @@ L14-14 verbatim
def iget [Inhabited α] (v : Fin k → α) (x : ℕ) : α := if h : x < k then v ⟨x, h⟩ else default


-- @@ L16-16 verbatim
end Matrix


-- @@ L18-18 verbatim
namespace FFL


-- @@ L20-20 verbatim
namespace FirstOrder


-- @@ L22-22 verbatim
variable {L : Language} {ξ : Type*} [Semiformula.Operator.Eq L]


-- @@ L24-24 verbatim
namespace Theory


-- @@ L26-26 verbatim
section Eq


-- @@ L28-28 verbatim
variable (L)


-- @@ L30-30 verbatim
abbrev Eq.refl : Sentence L := “∀ x, x = x”


-- @@ L32-32 verbatim
abbrev Eq.symm : Sentence L := “∀ x y, x = y → y = x”


-- @@ L34-34 verbatim
abbrev Eq.trans : Sentence L := “∀ x y z, x = y → y = z → x = z”


-- @@ L36-36 verbatim
variable {L}


-- @@ L38-42 verbatim
abbrev Eq.funcExt {k} (f : L.Func k) : Sentence L :=
  let σ : Semisentence L (k + k) :=
    (Matrix.conj fun i : Fin k ↦ “#(i.addCast k) = #(i.addNat k)”) 🡒
      op(=).operator ![Semiterm.func f (fun i ↦ #(i.addCast k)), Semiterm.func f (fun i ↦ #(i.addNat k))]
  ∀¹* σ


-- @@ L44-48 verbatim
abbrev Eq.relExt {k} (r : L.Rel k) : Sentence L :=
  let σ : Semisentence L (k + k) :=
    (Matrix.conj fun i : Fin k ↦ “#(i.addCast k) = #(i.addNat k)”) 🡒
      Semiformula.rel r (fun i ↦ #(i.addCast k)) 🡒 Semiformula.rel r (fun i ↦ #(i.addNat k))
  ∀¹* σ


-- @@ L50-50 verbatim
variable (L)


-- @@ L52-57 verbatim
inductive eqAxiom : Theory L
  | refl : eqAxiom (Eq.refl L)
  | symm : eqAxiom (Eq.symm L)
  | trans : eqAxiom (Eq.trans L)
  | funcExt {k} (f : L.Func k) : eqAxiom (Eq.funcExt f)
  | relExt {k} (r : L.Rel k) : eqAxiom (Eq.relExt r)


-- @@ L59-59 verbatim
notation "𝗘𝗤" => eqAxiom


-- @@ L61-81 verbatim
variable {L}

lemma Eq.defeq :
    𝗘𝗤 L = {Eq.refl L, Eq.symm L, Eq.trans L}
      ∪ Set.range (fun f : (k : ℕ) × L.Func k ↦ Eq.funcExt f.2)
      ∪ Set.range (fun f : (k : ℕ) × L.Rel k ↦ Eq.relExt f.2) := by
  ext φ; constructor
  · rintro ⟨⟩
    case refl => simp
    case symm => simp
    case trans => simp
    case funcExt k f =>
      left; right; exact ⟨⟨k, f⟩, rfl⟩
    case relExt k r =>
      right; exact ⟨⟨k, r⟩, rfl⟩
  · rintro (((rfl | rfl | rfl) | ⟨f, rfl⟩) | ⟨r, rfl⟩)
    · exact eqAxiom.refl
    · exact eqAxiom.symm
    · exact eqAxiom.trans
    · exact eqAxiom.funcExt _
    · exact eqAxiom.relExt _


-- @@ L83-87 verbatim
@[simp] lemma EqAxiom.finite [L.Finite] : Set.Finite (𝗘𝗤 L) := by
  have : Fintype ((k : ℕ) × L.Func k) := Language.Finite.func
  have : Fintype ((k : ℕ) × L.Rel k) := Language.Finite.rel
  rw [Eq.defeq]
  simp [Set.finite_range]


-- @@ L89-89 verbatim
end Eq


-- @@ L91-91 verbatim
end Theory


-- @@ L93-93 verbatim
namespace Structure


-- @@ L95-95 verbatim
namespace Eq


-- @@ L97-97 verbatim
variable (L) (M : Type*) [Nonempty M] [Structure L M]


-- @@ L99-104 verbatim
@[simp] instance models_eq [Structure.Eq L M] :
    M↓[L] ⊧* 𝗘𝗤 L := ⟨by
  intro φ h
  rcases h with (_ | _ | _ | _ | _) <;> simp [models_iff, Theory.Eq.funcExt, Theory.Eq.relExt]
  · simp [Function.comp_def]; grind
  · simp [Function.comp_def]; grind⟩


-- @@ L106-106 verbatim
instance models_eqAxiom' [Structure.Eq L M] : M↓[L] ⊧* 𝗘𝗤 L := models_eq _ _


-- @@ L108-108 verbatim
variable {M}


-- @@ L110-110 verbatim
def eqv (a b : M) : Prop := (@Semiformula.Operator.Eq.eq L _).val ![a, b]


-- @@ L112-112 verbatim
variable {L}


-- @@ L114-114 verbatim
variable [H : M↓[L] ⊧* 𝗘𝗤 L]


-- @@ L116-164 verbatim
open Semiterm Theory Semiformula

lemma eqv_refl (a : M) : eqv L a a := by
  have : M↓[L] ⊧ “∀ x, x = x” := H.models _ (Theory.eqAxiom.refl (L := L))
  have : ∀ x : M, op(=)[L].val ![x, x] := by simpa [models_iff] using this
  exact this a

lemma eqv_symm {a b : M} : eqv L a b → eqv L b a := by
  have : M↓[L] ⊧ “∀ x y, x = y → y = x” := H.models _ (Theory.eqAxiom.symm (L := L))
  have : ∀ x y : M, op(=)[L].val ![x, y] → op(=)[L].val ![y, x] := by simpa [models_iff] using this
  exact this a b

lemma eqv_trans {a b c : M} : eqv L a b → eqv L b c → eqv L a c := by
  have : M↓[L] ⊧ “∀ x y z, x = y → y = z → x = z” := H.models _ (Theory.eqAxiom.trans (L := L))
  have : ∀ x y z : M, op(=)[L].val ![x, y] → op(=)[L].val ![y, z] → op(=)[L].val ![x, z] := by simpa [models_iff] using this
  exact this a b c

lemma eqv_funcExt {k} (f : L.Func k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    eqv L (func f v) (func f w) := by
  have : M↓[L] ⊧ Eq.funcExt f := H.models _ (eqAxiom.funcExt f)
  have :
      ∀ m : Fin (k + k) → M,
      (∀ (i : Fin k), op(=)[L].val ![m (Fin.addCast k i), m (i.addNat k)]) →
        op(=)[L].val ![func f fun i ↦ m (Fin.addCast k i), func f fun i ↦ m (i.addNat k)] := by
    simpa [models_iff, Semiterm.val_func] using! this
  have := this (Matrix.vecAppend rfl v w) (fun i ↦ by simpa [Matrix.vecAppend_eq_ite, eqv] using h i)
  simpa [Semiterm.val_func, Matrix.vecAppend_eq_ite, eqv] using this

lemma eqv_relExt_aux {k} (r : L.Rel k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    rel r v → rel r w := by
  have : M↓[L] ⊧ Eq.relExt r := H.models _ (eqAxiom.relExt r)
  have :
      ∀ m : Fin (k + k) → M,
      (∀ (i : Fin k), op(=)[L].val ![m (Fin.addCast k i), m (i.addNat k)]) →
        (rel r fun i ↦ m (Fin.addCast k i)) → rel r fun i ↦ m (i.addNat k) := by
    simpa [models_iff, Semiterm.val_func, eval_rel] using! this
  have := this (Matrix.vecAppend rfl v w) (fun i ↦ by simpa [Matrix.vecAppend_eq_ite, eqv] using h i)
  simpa [Semiterm.val_func, Matrix.vecAppend_eq_ite, eqv] using this

lemma eqv_relExt {k} (r : L.Rel k) {v w : Fin k → M} (h : ∀ i, eqv L (v i) (w i)) :
    rel r v ↔ rel r w := by
  constructor
  · exact eqv_relExt_aux r h
  · exact eqv_relExt_aux r (fun i => eqv_symm (h i))

lemma eqv_equivalence : Equivalence (eqv L (M := M)) where
  refl := eqv_refl
  symm := eqv_symm
  trans := eqv_trans


-- @@ L166-166 verbatim
variable (L M)


-- @@ L168-168 verbatim
def eqvSetoid : Setoid M := Setoid.mk (eqv L) eqv_equivalence


-- @@ L170-170 verbatim
def QuotEq := Quotient (eqvSetoid L M)


-- @@ L172-172 verbatim
variable {L M}


-- @@ L174-176 verbatim
instance QuotEq.inhabited : Nonempty (QuotEq L M) := Nonempty.map (⟦·⟧) inferInstance

lemma of_eq_of {a b : M} : (⟦a⟧ : QuotEq L M) = ⟦b⟧ ↔ eqv L a b := Quotient.eq (r := eqvSetoid L M)


-- @@ L178-178 verbatim
namespace QuotEq


-- @@ L180-181 verbatim
def func ⦃k⦄ (f : L.Func k) (v : Fin k → QuotEq L M) : QuotEq L M :=
  Quotient.liftVec (s := eqvSetoid L M) (⟦Structure.func f ·⟧) (fun _ _ hvw ↦ of_eq_of.mpr (eqv_funcExt f hvw)) v


-- @@ L183-184 verbatim
def Rel ⦃k⦄ (r : L.Rel k) (v : Fin k → QuotEq L M) : Prop :=
  Quotient.liftVec (s := eqvSetoid L M) (Structure.rel r) (fun _ _ hvw ↦ eq_iff_iff.mpr <| eqv_relExt r hvw) v


-- @@ L186-241 verbatim
instance struc : Structure L (QuotEq L M) where
  func := QuotEq.func
  rel := QuotEq.Rel

lemma funk_mk {k} (f : L.Func k) (v : Fin k → M) : Structure.func (M := QuotEq L M) f (⟦v ·⟧) = ⟦Structure.func f v⟧ :=
  Quotient.liftVec_mk (s := eqvSetoid L M) _ _ _

lemma rel_mk {k} (r : L.Rel k) (v : Fin k → M) : Structure.rel (M := QuotEq L M) r (⟦v ·⟧) ↔ Structure.rel r v :=
  of_eq <| Quotient.liftVec_mk (s := eqvSetoid L M) _ _ _

lemma funk_mk_of_eq {k} (f : L.Func k) {w : Fin k → QuotEq L M} {v : Fin k → M}
    (h : ∀ i, w i = ⟦v i⟧) : Structure.func (M := QuotEq L M) f w = ⟦Structure.func f v⟧ :=
  funext h ▸ funk_mk f v

lemma rel_mk_of_eq {k} (r : L.Rel k) {w : Fin k → QuotEq L M} {v : Fin k → M}
    (h : ∀ i, w i = ⟦v i⟧) : Structure.rel (M := QuotEq L M) r w ↔ Structure.rel r v :=
  funext h ▸ rel_mk r v

lemma val_mk {bv fv} (t : Semiterm L ξ n) :
    t.val (M := QuotEq L M) (⟦bv ·⟧) (⟦fv ·⟧) = ⟦t.val bv fv⟧ := by
  induction t with
  | bvar x => rfl
  | fvar x => rfl
  | func f v ih => exact funk_mk_of_eq f ih

lemma eval_mk {bv fv} {φ : Semiformula L ξ n} :
    φ.Eval (M := QuotEq L M) (⟦bv ·⟧) (⟦fv ·⟧) ↔ φ.Eval bv fv := by
  induction φ using Semiformula.rec'
  case hall n φ ih =>
    constructor
    · intro h a; exact (ih (bv := a :> bv)).mp (by simp only [Matrix.comp_vecCons]; exact h ⟦a⟧)
    · intro h a;
      induction' a using Quotient.ind with a
      have h2 := ih.mpr (h a); simp only [Matrix.comp_vecCons] at h2; exact h2
  case hexs n φ ih =>
    constructor
    · intro ⟨a, h⟩
      induction' a using Quotient.ind with a
      exact ⟨a, (ih (bv := a :> bv)).mp (by simp only [Matrix.comp_vecCons]; exact h)⟩
    · intro ⟨a, h⟩; refine ⟨⟦a⟧, ?_⟩
      have h2 := ih.mpr h; simp only [Matrix.comp_vecCons] at h2; exact h2
  case _ => simp [*]
  case _ => simp [*]
  case hrel r v => exact rel_mk_of_eq r fun i ↦ val_mk (v i)
  case hnrel r v => exact not_congr (rel_mk_of_eq r fun i ↦ val_mk (v i))
  case _ => simp [*]
  case _ => simp [*]

lemma evalf_mk {fv} {φ : Formula L ξ} :
    φ.Evalf (M := QuotEq L M) (⟦fv ·⟧) ↔ φ.Evalf fv := by
  have h := eval_mk (bv := ![]) (fv := fv) (φ := φ)
  simp only [Matrix.empty_eq] at h; exact h

lemma models_iff {σ : Sentence L} : (QuotEq L M)↓[L] ⊧ σ ↔ M↓[L] ⊧ σ := by
  have h := eval_mk (M := M) (ξ := Empty) (φ := σ) (bv := ![]) (fv := Empty.elim)
  simp only [Empty.eq_elim, Matrix.empty_eq] at h; exact h


-- @@ L243-245 verbatim
variable (L M)

lemma elementaryEquiv : QuotEq L M ≡ₑ[L] M := ⟨models_iff⟩


-- @@ L247-247 verbatim
variable {L M}


-- @@ L249-255 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma rel_eq (a b : QuotEq L M) : op(=)[L].val (M := QuotEq L M) ![a, b] ↔ a = b := by
  induction' a using Quotient.ind with a
  induction' b using Quotient.ind with b
  rw [of_eq_of]; simp [eqv, Semiformula.Operator.val];
  simpa [Matrix.fun_eq_vec_two, Empty.eq_elim] using
    eval_mk (H := H) (bv := ![a, b]) (fv := Empty.elim) (φ := Semiformula.Operator.Eq.eq.sentence)


-- @@ L257-257 verbatim
instance structureEq : Structure.Eq L (QuotEq L M) := ⟨rel_eq⟩


-- @@ L259-259 verbatim
end QuotEq


-- @@ L261-261 verbatim
end Eq


-- @@ L263-289 verbatim
end Structure

lemma consequence_iff_eq {T : Theory L} [𝗘𝗤 L ⪯ T] {σ : Sentence L} :
    T ⊨[Struc.{v, u} L] σ ↔ (∀ (M : Type v) [Nonempty M] [Structure L M] [Structure.Eq L M], M↓[L] ⊧* T → M↓[L] ⊧ σ) := by
  simp only [consequence_iff, Nonempty.forall]
  constructor
  · intro h M x s _ hM; exact h M x hM
  · intro h M x s hM
    have : Nonempty M := ⟨x⟩
    have H : M↓[L] ⊧* 𝗘𝗤 L := models_of_subtheory hM
    have e : Structure.Eq.QuotEq L M ≡ₑ[L] M := Structure.Eq.QuotEq.elementaryEquiv L M
    exact e.models.mp $ h (Structure.Eq.QuotEq L M) ⟦x⟧ (e.modelsTheory.mpr hM)

lemma consequence_iff_eq' {T : Theory L} [𝗘𝗤 L ⪯ T] {σ : Sentence L} :
    T ⊨[Struc.{v, u} L] σ ↔ (∀ (M : Type v) [Nonempty M] [Structure L M] [Structure.Eq L M] [M↓[L] ⊧* T], M↓[L] ⊧ σ) := by
  rw [consequence_iff_eq]

lemma satisfiable_iff_eq {T : Theory L} [𝗘𝗤 L ⪯ T] :
    Semantics.Satisfiable (Struc.{v, u} L) T ↔ (∃ (M : Type v) (_ : Nonempty M) (_ : Structure L M) (_ : Structure.Eq L M), M↓[L] ⊧* T) := by
  simp only [satisfiable_iff, Nonempty.exists, exists_prop]
  constructor
  · intro ⟨M, x, s, hM⟩;
    have : Nonempty M := ⟨x⟩
    have H : M↓[L] ⊧* 𝗘𝗤 L := models_of_subtheory hM
    have e : Structure.Eq.QuotEq L M ≡ₑ[L] M := Structure.Eq.QuotEq.elementaryEquiv L M
    exact ⟨Structure.Eq.QuotEq L M, ⟦x⟧, inferInstance, inferInstance, e.modelsTheory.mpr hM⟩
  · intro ⟨M, i, s, _, hM⟩; exact ⟨M, i, s, hM⟩


-- @@ L291-292 verbatim
instance {T : Theory L} [𝗘𝗤 L ⪯ T] (sat : Semantics.Satisfiable (Struc.{v, u} L) T) :
    (ModelOfSat sat)↓[L] ⊧* 𝗘𝗤 L := models_of_subtheory (ModelOfSat.models sat)


-- @@ L294-295 verbatim
def ModelOfSatEq {T : Theory L} [𝗘𝗤 L ⪯ T] (sat : Semantics.Satisfiable (Struc.{v, u} L) T) : Type _ :=
  Structure.Eq.QuotEq L (ModelOfSat sat)


-- @@ L297-297 verbatim
namespace ModelOfSatEq


-- @@ L299-299 verbatim
variable {T : Theory L} [𝗘𝗤 L ⪯ T] (sat : Semantics.Satisfiable (Struc.{v, u} L) T)


-- @@ L301-301 verbatim
noncomputable instance : Nonempty (ModelOfSatEq sat) := Structure.Eq.QuotEq.inhabited


-- @@ L303-303 verbatim
noncomputable instance struc : Structure L (ModelOfSatEq sat) := Structure.Eq.QuotEq.struc


-- @@ L305-309 verbatim
noncomputable instance : Structure.Eq L (ModelOfSatEq sat) := Structure.Eq.QuotEq.structureEq

lemma models : (ModelOfSatEq sat)↓[L] ⊧* T :=
  have e : ModelOfSatEq sat ≡ₑ[L] ModelOfSat sat := Structure.Eq.QuotEq.elementaryEquiv L (ModelOfSat sat)
  e.modelsTheory.mpr (ModelOfSat.models _)


-- @@ L311-311 verbatim
instance mod : (ModelOfSatEq sat)↓[L] ⊧* T := models sat


-- @@ L313-313 verbatim
open Semiterm Semiformula


-- @@ L315-315 verbatim
noncomputable instance [Operator.Zero L] : Zero (ModelOfSatEq sat) := ⟨(@Operator.Zero.zero L _).val ![]⟩


-- @@ L317-317 verbatim
instance strucZero [Operator.Zero L] : Structure.Zero L (ModelOfSatEq sat) := ⟨rfl⟩


-- @@ L319-319 verbatim
noncomputable instance [Operator.One L] : One (ModelOfSatEq sat) := ⟨(@Operator.One.one L _).val ![]⟩


-- @@ L321-321 verbatim
instance [Operator.One L] : Structure.One L (ModelOfSatEq sat) := ⟨rfl⟩


-- @@ L323-324 verbatim
noncomputable instance [Operator.Add L] : Add (ModelOfSatEq sat) :=
  ⟨fun x y ↦ (@Operator.Add.add L _).val ![x, y]⟩


-- @@ L326-326 verbatim
instance [Operator.Add L] : Structure.Add L (ModelOfSatEq sat) := ⟨fun _ _ ↦ rfl⟩


-- @@ L328-329 verbatim
noncomputable instance [Operator.Mul L] : Mul (ModelOfSatEq sat) :=
  ⟨fun x y ↦ (@Operator.Mul.mul L _).val ![x, y]⟩


-- @@ L331-331 verbatim
instance [Operator.Mul L] : Structure.Mul L (ModelOfSatEq sat) := ⟨fun _ _ ↦ rfl⟩


-- @@ L333-334 verbatim
instance [Operator.LT L] : LT (ModelOfSatEq sat) :=
  ⟨fun x y ↦ (@Operator.LT.lt L _).val ![x, y]⟩


-- @@ L336-336 verbatim
instance [Operator.LT L] : Structure.LT L (ModelOfSatEq sat) := ⟨fun _ _ ↦ iff_of_eq rfl⟩


-- @@ L338-339 verbatim
instance [Operator.Mem L] : Membership (ModelOfSatEq sat) (ModelOfSatEq sat) :=
  ⟨fun x y ↦ (@Operator.Mem.mem L _).val ![y, x]⟩


-- @@ L341-341 verbatim
instance [Operator.Mem L] : Structure.Mem L (ModelOfSatEq sat) := ⟨fun _ _ ↦ iff_of_eq rfl⟩


-- @@ L343-343 verbatim
end ModelOfSatEq


-- @@ L345-345 verbatim
namespace Semiformula


-- @@ L347-348 verbatim
def existsUnique {ξ} (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  “∃ y, !φ y ⋯ ∧ ∀ z, !φ z ⋯ → z = y”


-- @@ L350-350 verbatim
prefix:64 "∃¹! " => existsUnique


-- @@ L352-352 verbatim
variable {M : Type*} [s : Structure L M] [Structure.Eq L M]


-- @@ L354-357 verbatim
@[simp] lemma eval_existsUnique {e ε} {φ : Semiformula L ξ (n + 1)} :
    Eval (M := M) e ε (∃¹! φ) ↔ ∃! x, Eval (M := M) (x :> e) ε φ := by
  simp [existsUnique, Semiformula.eval_substs, Matrix.comp_vecCons'', ExistsUnique]
  simp [Function.comp_def]


-- @@ L359-359 verbatim
end Semiformula


-- @@ L361-361 verbatim
namespace BinderNotation


-- @@ L363-363 verbatim
open Lean PrettyPrinter Delaborator SubExpr


-- @@ L365-365 verbatim
syntax:max "∃! " first_order_formula:0 : first_order_formula

-- @@ L366-366 verbatim
syntax:max "∃! " ident ", " first_order_formula:0 : first_order_formula


-- @@ L368-376 verbatim
macro_rules
  | `(⤫formula($type)[ $binders* | $fbinders* | ∃! $φ:first_order_formula ]) => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∃¹! ⤫formula($type)[ $binders'* | $fbinders* | $φ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ∃! $x, $φ ])                 => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    let binders' := binders.insertIdx 0 x
    `(∃¹! ⤫formula($type)[ $binders'* | $fbinders* | $φ ])


-- @@ L378-378 verbatim
end BinderNotation


-- @@ L380-380 verbatim
end FirstOrder


-- @@ L382-382 verbatim
end FFL


-- @@ L384-384 verbatim
end
