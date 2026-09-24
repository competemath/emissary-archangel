module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Typed
public import Foundation.FirstOrder.Bootstrapping.Syntax.Formula.Iteration


-- @@ L6-6 verbatim
@[expose] public section

-- @@ L7-9 verbatim
/-!
# Typed Formalized Semiformula/Formula
-/


-- @@ L11-11 verbatim
namespace FFL.FirstOrder.Arithmetic.Bootstrapping


-- @@ L13-13 verbatim
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


-- @@ L15-25 verbatim
variable {L : Language} [L.Encodable] [L.LORDefinable]

lemma sub_succ_lt_self {a b : V} (h : b < a) : a - (b + 1) < a := by
  simp [tsub_lt_iff_left (succ_le_iff_lt.mpr h)]

lemma sub_succ_lt_selfs {a b : V} (h : b < a) : a - (a - (b + 1) + 1) = b := by
  rw [←Arithmetic.sub_sub]
  apply sub_remove_left
  apply sub_remove_left
  rw [←add_sub_of_le (succ_le_iff_lt.mpr h)]
  simp


-- @@ L27-27 verbatim
section typed_formula


-- @@ L29-29 verbatim
variable (V L)


-- @@ L31-33 verbatim
structure Semiformula (n : ℕ) where
  val : V
  isSemiformula : IsSemiformula L ↑n val


-- @@ L35-35 verbatim
attribute [simp] Semiformula.isSemiformula


-- @@ L37-37 verbatim
abbrev Formula := Semiformula (V := V) L 0


-- @@ L39-39 verbatim
variable {L V}


-- @@ L41-41 verbatim
variable {k n m : ℕ}


-- @@ L43-44 verbatim
@[simp] lemma Semiformula.isSemiformula_zero (φ : Formula V L) :
    IsSemiformula L 0 φ.val := by simpa using φ.isSemiformula


-- @@ L46-47 verbatim
@[simp] lemma Semiformula.isSemiformula_one (φ : Semiformula V L 1) :
    IsSemiformula L 1 φ.val := by simpa using φ.isSemiformula


-- @@ L49-50 verbatim
@[simp] lemma Semiformula.isSemiformula_succ (φ : Semiformula V L (n + 1)) :
    IsSemiformula L (↑n + 1 : V) φ.val := by simpa using φ.isSemiformula


-- @@ L52-52 verbatim
@[simp] lemma Semiformula.isUFormula (φ : Semiformula V L n) : IsUFormula L φ.val := φ.isSemiformula.isUFormula


-- @@ L54-54 verbatim
noncomputable def Semiformula.rel (R : L.Rel k) (v : SemitermVec V L k n) : Semiformula V L n := ⟨^rel ↑k ⌜R⌝ v.val, by simp⟩


-- @@ L56-56 verbatim
noncomputable def Semiformula.nrel (R : L.Rel k) (v : SemitermVec V L k n) : Semiformula V L n := ⟨^nrel ↑k ⌜R⌝ v.val, by simp⟩


-- @@ L58-59 verbatim
@[simp] lemma Semiformula.rel_val (R : L.Rel k) (v : SemitermVec V L k n) :
    (Semiformula.rel R v).val = ^rel ↑k ⌜R⌝ v.val := rfl


-- @@ L61-62 verbatim
@[simp] lemma Semiformula.nrel_val (R : L.Rel k) (v : SemitermVec V L k n) :
    (Semiformula.nrel R v).val = ^nrel ↑k ⌜R⌝ v.val := rfl


-- @@ L64-68 verbatim
noncomputable scoped instance : LogicalConnective (Semiformula V L n) where
  wedge (φ ψ) := ⟨φ.val ^⋏ ψ.val, by simp⟩
  vee (φ ψ) := ⟨φ.val ^⋎ ψ.val, by simp⟩
  arrow (φ ψ) := ⟨imp L φ.val ψ.val, by simp⟩
  tilde (φ) := ⟨neg L φ.val, by simp⟩


-- @@ L70-72 verbatim
noncomputable scoped instance : LogicalNeutral (Semiformula V L n) where
  top := ⟨^⊤, by simp⟩
  bot := ⟨^⊥, by simp⟩


-- @@ L74-78 verbatim
noncomputable instance : LCWQ (Semiformula V L) where
  connectives := inferInstance
  neutrals := inferInstance
  all φ := ⟨^∀ φ.val, by simp⟩
  exs φ := ⟨^∃ φ.val, by simp⟩


-- @@ L80-80 verbatim
noncomputable def verums (k : V) : Semiformula V L n := ⟨qqVerums k, by simp⟩


-- @@ L82-82 verbatim
namespace Semiformula


-- @@ L84-84 verbatim
@[simp] lemma val_verum : (⊤ : Semiformula V L n).val = ^⊤ := rfl


-- @@ L86-86 verbatim
@[simp] lemma val_falsum : (⊥ : Semiformula V L n).val = ^⊥ := rfl


-- @@ L88-89 verbatim
@[simp] lemma val_and (φ ψ : Semiformula V L n) :
    (φ ⋏ ψ).val = φ.val ^⋏ ψ.val := rfl


-- @@ L91-92 verbatim
@[simp] lemma val_or (φ ψ : Semiformula V L n) :
    (φ ⋎ ψ).val = φ.val ^⋎ ψ.val := rfl


-- @@ L94-95 verbatim
@[simp] lemma val_neg (φ : Semiformula V L n) :
    (∼φ).val = neg L φ.val := rfl


-- @@ L97-98 verbatim
@[simp] lemma val_imp (φ ψ : Semiformula V L n) :
    (φ 🡒 ψ).val = imp L φ.val ψ.val := rfl


-- @@ L100-101 verbatim
@[simp] lemma val_all (φ : Semiformula V L (n + 1)) :
    (∀¹ φ).val = ^∀ φ.val := rfl


-- @@ L103-104 verbatim
@[simp] lemma val_exs (φ : Semiformula V L (n + 1)) :
    (∃¹ φ).val = ^∃ φ.val := rfl


-- @@ L106-110 verbatim
@[simp] lemma val_iff (φ ψ : Semiformula V L n) :
    (φ 🡘 ψ).val = iff L φ.val ψ.val := rfl

lemma val_inj {φ ψ : Semiformula V L n} :
    φ.val = ψ.val ↔ φ = ψ := by rcases φ; rcases ψ; simp


-- @@ L112-112 verbatim
@[ext] lemma ext {φ ψ : Semiformula V L n} (h : φ.val = ψ.val) : φ = ψ := val_inj.mp h


-- @@ L114-115 verbatim
@[simp] lemma and_inj {φ₁ φ₂ ψ₁ ψ₂ : Semiformula V L n} :
    φ₁ ⋏ φ₂ = ψ₁ ⋏ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Semiformula.ext_iff]


-- @@ L117-118 verbatim
@[simp] lemma or_inj {φ₁ φ₂ ψ₁ ψ₂ : Semiformula V L n} :
    φ₁ ⋎ φ₂ = ψ₁ ⋎ ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [Semiformula.ext_iff]


-- @@ L120-121 verbatim
@[simp] lemma all_inj {φ ψ : Semiformula V L (n + 1)} :
    ∀¹ φ = ∀¹ ψ ↔ φ = ψ := by simp [Semiformula.ext_iff]


-- @@ L123-124 verbatim
@[simp] lemma exs_inj {φ ψ : Semiformula V L (n + 1)} :
    ∃¹ φ = ∃¹ ψ ↔ φ = ψ := by simp [Semiformula.ext_iff]


-- @@ L126-126 verbatim
@[simp] lemma val_verums (k : V) : (verums k : Semiformula V L n).val = qqVerums k := rfl


-- @@ L128-128 verbatim
@[simp] lemma verums_zero : (verums 0 : Semiformula V L n) = ⊤ := by ext; simp


-- @@ L130-130 verbatim
@[simp] lemma verums_succ (k : V) : (verums (k + 1) : Semiformula V L n) = ⊤ ⋏ verums k := by ext; simp


-- @@ L132-133 verbatim
instance : TildeInvolutive (Semiformula V L n) where
  tilde_involutive _ := by ext; simp


-- @@ L135-138 verbatim
instance : LogicalConnective.DeMorgan (Semiformula V L n) where
  and _ _ := by ext; simp
  or _ _ := by ext; simp
  imply _ _ := by ext; simp; rfl


-- @@ L140-142 verbatim
instance : LogicalNeutral.DeMorgan (Semiformula V L n) where
  verum := by ext; simp
  falsum := by ext; simp


-- @@ L144-144 verbatim
@[simp] lemma neg_all (φ : Semiformula V L (n + 1)) : ∼(∀¹ φ) = ∃¹ (∼φ) := by ext; simp

-- @@ L145-145 verbatim
@[simp] lemma neg_ex (φ : Semiformula V L (n + 1)) : ∼(∃¹ φ) = ∀¹ (∼φ) := by ext; simp


-- @@ L147-148 verbatim
@[simp] lemma neg_rel (R : L.Rel k) (v : SemitermVec V L k n) :
    ∼Semiformula.rel R v = Semiformula.nrel R v := by ext; simp

-- @@ L149-152 verbatim
@[simp] lemma neg_nrel (R : L.Rel k) (v : SemitermVec V L k n) :
    ∼Semiformula.nrel R v = Semiformula.rel R v := by ext; simp

lemma imp_def (φ ψ : Semiformula V L n) : φ 🡒 ψ = ∼φ ⋎ ψ := by ext; simp [imp]


-- @@ L154-154 verbatim
noncomputable def shift (φ : Semiformula V L n) : Semiformula V L n := ⟨Bootstrapping.shift L φ.val, φ.isSemiformula.shift⟩


-- @@ L156-157 verbatim
noncomputable def subst (w : SemitermVec V L n m) (φ : Semiformula V L n) : Semiformula V L m :=
  ⟨Bootstrapping.subst L w.val φ.val, φ.isSemiformula.subst w.isSemitermVec⟩


-- @@ L159-159 verbatim
@[simp] lemma val_shift (φ : Semiformula V L n) : φ.shift.val = Bootstrapping.shift L φ.val := rfl

-- @@ L160-160 verbatim
@[simp] lemma val_substs (φ : Semiformula V L n) (w : SemitermVec V L n m) : (φ.subst w).val = Bootstrapping.subst L w.val φ.val := rfl


-- @@ L162-162 verbatim
@[simp] lemma shift_verum : (⊤ : Semiformula V L n).shift = ⊤ := by ext; simp [shift]

-- @@ L163-163 verbatim
@[simp] lemma shift_falsum : (⊥ : Semiformula V L n).shift = ⊥ := by ext; simp [shift]

-- @@ L164-164 verbatim
@[simp] lemma shift_and (φ ψ : Semiformula V L n) : (φ ⋏ ψ).shift = φ.shift ⋏ ψ.shift := by ext; simp [shift]

-- @@ L165-165 verbatim
@[simp] lemma shift_or (φ ψ : Semiformula V L n) : (φ ⋎ ψ).shift = φ.shift ⋎ ψ.shift := by ext; simp [shift]

-- @@ L166-166 verbatim
@[simp] lemma shift_all (φ : Semiformula V L (n + 1)) : (∀¹ φ).shift = ∀¹ φ.shift := by ext; simp [shift]

-- @@ L167-167 verbatim
@[simp] lemma shift_exs (φ : Semiformula V L (n + 1)) : (∃¹ φ).shift = ∃¹ φ.shift := by ext; simp [shift]

-- @@ L168-168 verbatim
@[simp] lemma shift_rel (R : L.Rel k) (v : SemitermVec V L k n) : (rel R v).shift = rel R (Semiterm.shift⨟ v) := by ext; simp

-- @@ L169-169 verbatim
@[simp] lemma shift_nrel (R : L.Rel k) (v : SemitermVec V L k n) : (nrel R v).shift = nrel R (Semiterm.shift⨟ v) := by ext; simp


-- @@ L171-173 verbatim
@[simp] lemma neg_inj {φ ψ : Semiformula V L n} :
    ∼φ = ∼ψ ↔ φ = ψ :=
  ⟨by intro h; simpa using congr_arg (∼·) h, by rintro rfl; rfl⟩


-- @@ L175-176 verbatim
@[simp] lemma imp_inj {φ₁ φ₂ ψ₁ ψ₂ : Semiformula V L n} :
    φ₁ 🡒 φ₂ = ψ₁ 🡒 ψ₂ ↔ φ₁ = ψ₁ ∧ φ₂ = ψ₂ := by simp [imp_def]


-- @@ L178-179 verbatim
@[simp] lemma shift_neg (φ : Semiformula V L n) : (∼φ).shift = ∼(φ.shift) := by
  ext; simp [shift, val_neg]; simp [Bootstrapping.shift_neg φ.isSemiformula]


-- @@ L181-182 verbatim
@[simp] lemma shift_imp (φ ψ : Semiformula V L n) : (φ 🡒 ψ).shift = φ.shift 🡒 ψ.shift := by
  simp [imp_def]

-- @@ L183-184 verbatim
@[simp] lemma shift_iff (φ ψ : Semiformula V L n) : (φ 🡘 ψ).shift = φ.shift 🡘 ψ.shift := by
  simp [LogicalConnective.iff]


-- @@ L186-186 verbatim
@[simp] lemma substs_verum (w : SemitermVec V L n m) : (⊤ : Semiformula V L n).subst w = ⊤ := by ext; simp [subst]

-- @@ L187-187 verbatim
@[simp] lemma substs_falsum (w : SemitermVec V L n m) : (⊥ : Semiformula V L n).subst w = ⊥ := by ext; simp [subst]

-- @@ L188-189 verbatim
@[simp] lemma substs_and (w : SemitermVec V L n m) (φ ψ : Semiformula V L n) :
    (φ ⋏ ψ).subst w = φ.subst w ⋏ ψ.subst w := by ext; simp [subst]

-- @@ L190-191 verbatim
@[simp] lemma substs_or (w : SemitermVec V L n m) (φ ψ : Semiformula V L n) :
    (φ ⋎ ψ).subst w = φ.subst w ⋎ ψ.subst w := by ext; simp [subst]

-- @@ L192-194 verbatim
@[simp] lemma substs_all (w : SemitermVec V L n m) (φ : Semiformula V L (n + 1)) :
    (∀¹ φ).subst w = ∀¹ (φ.subst w.q) := by
  ext; simp [subst, Semiterm.bvar, qVec, SemitermVec.q, w.isSemitermVec.lh]

-- @@ L195-197 verbatim
@[simp] lemma substs_ex (w : SemitermVec V L n m) (φ : Semiformula V L (n + 1)) :
    (∃¹ φ).subst w = ∃¹ (φ.subst w.q) := by
  ext; simp [subst, Semiterm.bvar, qVec, SemitermVec.q, w.isSemitermVec.lh]

-- @@ L198-199 verbatim
@[simp] lemma substs_rel (w : SemitermVec V L n m) (R : L.Rel k) (v : SemitermVec V L k n) :
    (rel R v).subst w = rel R ((Semiterm.subst w)⨟ v) := by ext; simp

-- @@ L200-201 verbatim
@[simp] lemma substs_nrel (w : SemitermVec V L n m) (R : L.Rel k) (v : SemitermVec V L k n) :
    (nrel R v).subst w = nrel R ((Semiterm.subst w)⨟ v) := by ext; simp


-- @@ L203-204 verbatim
@[simp] lemma substs_neg (w : SemitermVec V L n m) (φ : Semiformula V L n) : (∼φ).subst w = ∼(φ.subst w) := by
  ext; simp [subst, val_neg, Bootstrapping.substs_neg φ.isSemiformula w.isSemitermVec]

-- @@ L205-206 verbatim
@[simp] lemma substs_imp (w : SemitermVec V L n m) (φ ψ : Semiformula V L n) : (φ 🡒 ψ).subst w = φ.subst w 🡒 ψ.subst w := by
  simp [imp_def]

-- @@ L207-208 verbatim
@[simp] lemma substs_imply (w : SemitermVec V L n m) (φ ψ : Semiformula V L n) : (φ 🡘 ψ).subst w = φ.subst w 🡘 ψ.subst w := by
  simp [LogicalConnective.iff]


-- @@ L210-212 verbatim
@[simp] lemma substs_ball (t) (w : SemitermVec V L n m) (φ : Semiformula V L (n + 1)) :
    (∀¹[t] φ).subst w = ∀¹[t.subst w.q] (φ.subst w.q) := by
  simp [ball]

-- @@ L213-223 verbatim
@[simp] lemma substs_bexs (t) (w : SemitermVec V L n m) (φ : Semiformula V L (n + 1)) :
    (∃¹[t] φ).subst w = ∃¹[t.subst w.q] (φ.subst w.q) := by
  simp [bexs]

lemma subst_eq_self {n : ℕ} (w : SemitermVec V L n n) (φ : Semiformula V L n) (H : ∀ i, w i = Semiterm.bvar i) :
    φ.subst w = φ := by
  suffices ∀ i < ↑n, w.val.[i] = ^#i by
    ext; simp only [Semiformula.val_substs]; rw [Bootstrapping.subst_eq_self φ.isSemiformula w.isSemitermVec]; simpa
  intro i hi
  rcases eq_fin_of_lt_nat hi with ⟨i, rfl⟩
  simpa using congr_arg Semiterm.val <| H i


-- @@ L225-228 verbatim
@[simp] lemma subst_eq_self₁ (φ : Semiformula V L 1) :
    φ.subst ![Semiterm.bvar 0] = φ := by
  apply subst_eq_self
  simp


-- @@ L230-238 verbatim
@[simp] lemma subst_nil_eq_self (w : SemitermVec V L 0 0) (φ : Semiformula V L 0) :
    φ.subst w = φ := subst_eq_self _ _ (by simp)

lemma shift_substs (w : SemitermVec V L n m) (φ : Semiformula V L n) :
    (φ.subst w).shift = φ.shift.subst (Semiterm.shift⨟ w) := by ext; simp [Bootstrapping.shift_substs φ.isSemiformula w.isSemitermVec]

lemma substs_substs {n m l : ℕ} (v : SemitermVec V L m l) (w : SemitermVec V L n m) (φ : Semiformula V L n) :
    (φ.subst w).subst v = φ.subst ((Semiterm.subst v)⨟ w) := by
  ext; simp [Bootstrapping.substs_substs φ.isSemiformula v.isSemitermVec w.isSemitermVec]


-- @@ L240-240 verbatim
noncomputable def free (φ : Semiformula V L 1) : Formula V L := φ.shift.subst ![Semiterm.fvar 0]


-- @@ L242-243 verbatim
@[simp] lemma free_val (φ : Semiformula V L 1) : φ.free.val = Bootstrapping.free L φ.val := by
  simp [free]; rfl


-- @@ L245-245 verbatim
noncomputable def free1 (φ : Semiformula V L 2) : Semiformula V L 1 := φ.shift.subst ![Semiterm.fvar 0, Semiterm.bvar 0]


-- @@ L247-248 verbatim
@[simp] lemma free1_val (φ : Semiformula V L 2) : φ.free1.val = Bootstrapping.free1 L φ.val := by
  simp [free1]; rfl


-- @@ L250-250 verbatim
open Bootstrapping.Arithmetic


-- @@ L252-255 verbatim
noncomputable def substItrConj (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) : Semiformula V ℒₒᵣ n :=
  ⟨^⋀ Bootstrapping.Arithmetic.substItr w.val φ.val z, by
    have : IsSemiformula ℒₒᵣ (↑m + 1 : V) φ.val := by simp
    exact this.substItrConj w.isSemitermVec z⟩


-- @@ L257-260 verbatim
noncomputable def substItrDisj (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) : Semiformula V ℒₒᵣ n :=
  ⟨^⋁ Bootstrapping.Arithmetic.substItr w.val φ.val z, by
    have : IsSemiformula ℒₒᵣ (↑m + 1 : V) φ.val := by simp
    exact this.substItrDisj w.isSemitermVec z⟩


-- @@ L262-263 verbatim
@[simp] lemma substItrConj_val (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    (φ.substItrConj w z).val = ^⋀ Bootstrapping.Arithmetic.substItr w.val φ.val z := rfl


-- @@ L265-266 verbatim
@[simp] lemma substItrDisj_val (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    (φ.substItrDisj w z).val = ^⋁ Bootstrapping.Arithmetic.substItr w.val φ.val z := rfl


-- @@ L268-269 verbatim
@[simp] lemma substItrConj_zero (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) :
    φ.substItrConj w 0 = ⊤ := by ext; simp


-- @@ L271-272 verbatim
@[simp] lemma substItrConj_succ (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    φ.substItrConj w (z + 1) = φ.subst (typedNumeral z :> w) ⋏ φ.substItrConj w z := by ext; simp


-- @@ L274-276 verbatim
@[simp] lemma substItrConj_one (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) :
    φ.substItrConj w 1 = φ.subst (typedNumeral 0 :> w) ⋏ ⊤ := by
  simpa using substItrConj_succ w φ 0


-- @@ L278-279 verbatim
@[simp] lemma substItrDisj_zero (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) :
    φ.substItrDisj w 0 = ⊥ := by ext; simp


-- @@ L281-282 verbatim
@[simp] lemma substItrDisj_succ (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    φ.substItrDisj w (z + 1) = φ.subst (typedNumeral z :> w) ⋎ φ.substItrDisj w z := by ext; simp


-- @@ L284-286 verbatim
@[simp] lemma substItrDisj_one (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) :
    φ.substItrDisj w 1 = φ.subst (typedNumeral 0 :> w) ⋎ ⊥ := by
  simpa using substItrDisj_succ w φ 0


-- @@ L288-290 verbatim
@[simp] lemma substItrConj_neg (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    ∼(φ.substItrConj w z) = (∼φ).substItrDisj w z := by
  ext; simp [substItrConj, substItrDisj, neg_conj_substItr φ.isSemiformula w.isSemitermVec]


-- @@ L292-294 verbatim
@[simp] lemma substItrDisj_neg (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    ∼(φ.substItrDisj w z) = (∼φ).substItrConj w z := by
  ext; simp [substItrConj, substItrDisj, neg_disj_substItr φ.isSemiformula w.isSemitermVec]


-- @@ L296-299 verbatim
@[simp] lemma substItrConj_substs (v : SemitermVec V ℒₒᵣ n k) (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    (φ.substItrConj w z).subst v = φ.substItrConj ((Semiterm.subst v)⨟ w) z := by
  ext; simp only [substItrConj, val_substs, SemitermVec.val_substs]
  rw [substs_conj_substItr φ.isSemiformula w.isSemitermVec v.isSemitermVec]; rfl


-- @@ L301-304 verbatim
@[simp] lemma substItrDisj_substs (v : SemitermVec V ℒₒᵣ n k) (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    (φ.substItrDisj w z).subst v = φ.substItrDisj ((Semiterm.subst v)⨟ w) z := by
  ext; simp only [substItrDisj, val_substs, SemitermVec.val_substs]
  rw [substs_disj_substItr φ.isSemiformula w.isSemitermVec v.isSemitermVec]; rfl


-- @@ L306-309 verbatim
@[simp] lemma substItrConj_shift (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    (φ.substItrConj w z).shift = φ.shift.substItrConj (Semiterm.shift⨟ w) z := by
  ext; simp only [substItrConj, val_shift, SemitermVec.val_shift]
  rw [shift_conj_substItr φ.isSemiformula w.isSemitermVec]; rfl


-- @@ L311-314 verbatim
@[simp] lemma substItrDisj_shift (w : SemitermVec V ℒₒᵣ m n) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    (φ.substItrDisj w z).shift = φ.shift.substItrDisj (Semiterm.shift⨟ w) z := by
  ext; simp only [substItrDisj, val_shift, SemitermVec.val_shift]
  rw [shift_disj_substItr φ.isSemiformula w.isSemitermVec]; rfl


-- @@ L316-318 verbatim
@[simp] lemma substItrConj_free (w : SemitermVec V ℒₒᵣ m 1) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    (φ.substItrConj w z).free = φ.shift.substItrConj (Semiterm.free⨟ w) z := by
  unfold free; simp [Matrix.vecMap_vecMap_comp']; rfl


-- @@ L320-322 verbatim
@[simp] lemma substItrDisj_free (w : SemitermVec V ℒₒᵣ m 1) (φ : Semiformula V ℒₒᵣ (m + 1)) (z : V) :
    (φ.substItrDisj w z).free = φ.shift.substItrDisj (Semiterm.free⨟ w) z := by
  unfold free; simp [Matrix.vecMap_vecMap_comp']; rfl


-- @@ L324-324 verbatim
end Semiformula


-- @@ L326-364 verbatim
end typed_formula

/-
section typed_isfvfree

namespace Semiformula

def FVFree (φ : Semiformula V L n) : Prop := L.IsFVFree n φ.val

lemma FVFree.iff {φ : Semiformula V L n} : φ.FVFree ↔ φ.shift = φ := by
  simp [FVFree, Language.IsFVFree, ext_iff]

@[simp] lemma Fvfree.verum : (⊤ : Semiformula V L n).FVFree := by simp [FVFree]

@[simp] lemma Fvfree.falsum : (⊥ : Semiformula V L n).FVFree := by simp [FVFree]

@[simp] lemma Fvfree.and {φ ψ : Semiformula V L n} :
    (φ ⋏ ψ).FVFree ↔ φ.FVFree ∧ ψ.FVFree := by
  simp [FVFree.iff, FVFree.iff]

@[simp] lemma Fvfree.or {φ ψ : Semiformula V L n} : (φ ⋎ ψ).FVFree ↔ φ.FVFree ∧ ψ.FVFree := by
  simp [FVFree.iff]

@[simp] lemma Fvfree.neg {φ : Semiformula V L n} : (∼φ).FVFree ↔ φ.FVFree := by
  simp [FVFree.iff]

@[simp] lemma Fvfree.all {φ : Semiformula V L (n + 1)} : ∀¹ φ.FVFree ↔ φ.FVFree := by
  simp [FVFree.iff]

@[simp] lemma Fvfree.exs {φ : Semiformula V L (n + 1)} : ∃¹ φ.FVFree ↔ φ.FVFree := by
  simp [FVFree.iff]

@[simp] lemma Fvfree.imp {φ ψ : Semiformula V L n} : (φ 🡒 ψ).FVFree ↔ φ.FVFree ∧ ψ.FVFree := by
  simp [FVFree.iff]

end Semiformula

end typed_isfvfree
-/


-- @@ L366-366 verbatim
open Bootstrapping.Arithmetic


-- @@ L368-368 verbatim
variable {k n m : ℕ}


-- @@ L370-370 verbatim
noncomputable def Semiterm.equals (t u : Semiterm V ℒₒᵣ n) : Semiformula V ℒₒᵣ n := ⟨t.val ^= u.val, by simp [qqEQ]⟩


-- @@ L372-372 verbatim
noncomputable def Semiterm.notEquals (t u : Semiterm V ℒₒᵣ n) : Semiformula V ℒₒᵣ n := ⟨t.val ^≠ u.val, by simp [qqNEQ]⟩


-- @@ L374-374 verbatim
noncomputable def Semiterm.lessThan (t u : Semiterm V ℒₒᵣ n) : Semiformula V ℒₒᵣ n := ⟨t.val ^< u.val, by simp [qqLT]⟩


-- @@ L376-376 verbatim
noncomputable def Semiterm.notLessThan (t u : Semiterm V ℒₒᵣ n) : Semiformula V ℒₒᵣ n := ⟨t.val ^≮ u.val, by simp [qqNLT]⟩


-- @@ L378-378 verbatim
scoped infix:46 " ≐ " => Semiterm.equals


-- @@ L380-380 verbatim
scoped infix:46 " ≉ " => Semiterm.notEquals


-- @@ L382-382 verbatim
scoped infix:46 " <' " => Semiterm.lessThan


-- @@ L384-384 verbatim
scoped infix:46 " ≮' " => Semiterm.notLessThan


-- @@ L386-387 verbatim
noncomputable def Semiformula.ball (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) : Semiformula V ℒₒᵣ n :=
  ∀¹ ((Semiterm.bvar 0 ≮' t.bShift) ⋎ φ)


-- @@ L389-390 verbatim
noncomputable def Semiformula.bexs (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) : Semiformula V ℒₒᵣ n :=
  ∃¹ ((Semiterm.bvar 0 <' t.bShift) ⋏ φ)


-- @@ L392-398 verbatim
namespace Arithmetic

-- `Arithmetic` is intentionally re-opened here even though the ambient namespace
-- already contains it; renaming would break the widely-used public API
-- (`Bootstrapping.Arithmetic.*`). Suppress the new dupNamespace linter for the
-- declarations in this namespace (the option is scoped by `namespace`/`end` and
-- reverts automatically at `end Arithmetic`).

-- @@ L399-399 verbatim
set_option linter.dupNamespace false


-- @@ L401-401 verbatim
variable {n m : ℕ}


-- @@ L403-405 verbatim
@[simp] lemma rel_eq_eq (v : Fin 2 → Semiterm V ℒₒᵣ n) :
    Semiformula.rel (Language.Eq.eq : (ℒₒᵣ).Rel 2) v = (v 0 ≐ v 1) := by
  ext; rfl


-- @@ L407-409 verbatim
@[simp] lemma nrel_eq_eq (v : Fin 2 → Semiterm V ℒₒᵣ n) :
    Semiformula.nrel (Language.Eq.eq : (ℒₒᵣ).Rel 2) v = (v 0 ≉ v 1) := by
  ext; rfl


-- @@ L411-413 verbatim
@[simp] lemma rel_lt_eq (v : Fin 2 → Semiterm V ℒₒᵣ n) :
    Semiformula.rel (Language.LT.lt : (ℒₒᵣ).Rel 2) v = (v 0 <' v 1) := by
  ext; rfl


-- @@ L415-417 verbatim
@[simp] lemma nrel_lt_eq (v : Fin 2 → Semiterm V ℒₒᵣ n) :
    Semiformula.nrel (Language.LT.lt : (ℒₒᵣ).Rel 2) v = (v 0 ≮' v 1) := by
  ext; rfl


-- @@ L419-419 verbatim
@[simp] lemma val_equals (t u : Semiterm V ℒₒᵣ n) : (t ≐ u).val = t.val ^= u.val := rfl

-- @@ L420-420 verbatim
@[simp] lemma val_notEquals (t u : Semiterm V ℒₒᵣ n) : (t ≉ u).val = t.val ^≠ u.val := rfl

-- @@ L421-421 verbatim
@[simp] lemma val_lessThan (t u : Semiterm V ℒₒᵣ n) : (t <' u).val = t.val ^< u.val := rfl

-- @@ L422-422 verbatim
@[simp] lemma val_notLessThan (t u : Semiterm V ℒₒᵣ n) : (t ≮' u).val = t.val ^≮ u.val := rfl


-- @@ L424-426 verbatim
@[simp] lemma equals_iff {t₁ t₂ u₁ u₂ : Semiterm V ℒₒᵣ n} :
    (t₁ ≐ u₁) = (t₂ ≐ u₂) ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [Semiformula.ext_iff, Semiterm.ext_iff, qqEQ]


-- @@ L428-430 verbatim
@[simp] lemma notequals_iff {t₁ t₂ u₁ u₂ : Semiterm V ℒₒᵣ n} :
    (t₁ ≉ u₁) = (t₂ ≉ u₂) ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [Semiformula.ext_iff, Semiterm.ext_iff, qqNEQ]


-- @@ L432-434 verbatim
@[simp] lemma lessThan_iff {t₁ t₂ u₁ u₂ : Semiterm V ℒₒᵣ n} :
    (t₁ <' u₁) = (t₂ <' u₂) ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [Semiformula.ext_iff, Semiterm.ext_iff, qqLT]


-- @@ L436-438 verbatim
@[simp] lemma notLessThan_iff {t₁ t₂ u₁ u₂ : Semiterm V ℒₒᵣ n} :
    (t₁ ≮' u₁) = (t₂ ≮' u₂) ↔ t₁ = t₂ ∧ u₁ = u₂ := by
  simp [Semiformula.ext_iff, Semiterm.ext_iff, qqNLT]


-- @@ L440-442 verbatim
@[simp] lemma neg_equals (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    ∼(t₁ ≐ t₂) = (t₁ ≉ t₂) := by
  ext; simp [Semiterm.equals, Semiterm.notEquals, qqEQ, qqNEQ]


-- @@ L444-446 verbatim
@[simp] lemma neg_notEquals (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    ∼(t₁ ≉ t₂) = (t₁ ≐ t₂) := by
  ext; simp [Semiterm.equals, Semiterm.notEquals, qqEQ, qqNEQ]


-- @@ L448-450 verbatim
@[simp] lemma neg_lessThan (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    ∼(t₁ <' t₂) = (t₁ ≮' t₂) := by
  ext; simp [Semiterm.lessThan, Semiterm.notLessThan, qqLT, qqNLT]


-- @@ L452-454 verbatim
@[simp] lemma neg_notLessThan (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    ∼(t₁ ≮' t₂) = (t₁ <' t₂) := by
  ext; simp [Semiterm.lessThan, Semiterm.notLessThan, qqLT, qqNLT]


-- @@ L456-458 verbatim
@[simp] lemma shift_equals (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ ≐ t₂).shift = (t₁.shift ≐ t₂.shift) := by
  ext; simp [Semiterm.equals, Semiterm.shift, Semiformula.shift, qqEQ]


-- @@ L460-462 verbatim
@[simp] lemma shift_notEquals (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ ≉ t₂).shift = (t₁.shift ≉ t₂.shift) := by
  ext; simp [Semiterm.notEquals, Semiterm.shift, Semiformula.shift, qqNEQ]


-- @@ L464-466 verbatim
@[simp] lemma shift_lessThan (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ <' t₂).shift = (t₁.shift <' t₂.shift) := by
  ext; simp [Semiterm.lessThan, Semiterm.shift, Semiformula.shift, qqLT]


-- @@ L468-470 verbatim
@[simp] lemma shift_notLessThan (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ ≮' t₂).shift = (t₁.shift ≮' t₂.shift) := by
  ext; simp [Semiterm.notLessThan, Semiterm.shift, Semiformula.shift, qqNLT]


-- @@ L472-474 verbatim
@[simp] lemma substs_equals (w : SemitermVec V ℒₒᵣ n m) (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ ≐ t₂).subst w = (t₁.subst w ≐ t₂.subst w) := by
  ext; simp [Semiterm.equals, Semiterm.subst, Semiformula.subst, qqEQ]


-- @@ L476-478 verbatim
@[simp] lemma substs_notEquals (w : SemitermVec V ℒₒᵣ n m) (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ ≉ t₂).subst w = (t₁.subst w ≉ t₂.subst w) := by
  ext; simp [Semiterm.notEquals, Semiterm.subst, Semiformula.subst, qqNEQ]


-- @@ L480-482 verbatim
@[simp] lemma substs_lessThan (w : SemitermVec V ℒₒᵣ n m) (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ <' t₂).subst w = (t₁.subst w <' t₂.subst w) := by
  ext; simp [Semiterm.lessThan, Semiterm.subst, Semiformula.subst, qqLT]


-- @@ L484-486 verbatim
@[simp] lemma substs_notLessThan (w : SemitermVec V ℒₒᵣ n m) (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ ≮' t₂).subst w = (t₁.subst w ≮' t₂.subst w) := by
  ext; simp [Semiterm.notLessThan, Semiterm.subst, Semiformula.subst, qqNLT]


-- @@ L488-490 verbatim
@[simp] lemma val_ball (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) :
    (φ.ball t).val = ^∀ (^#0 ^≮ termBShift ℒₒᵣ t.val) ^⋎ φ.val := by
  simp [Semiformula.ball]


-- @@ L492-502 verbatim
@[simp] lemma val_bexs (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) :
    (φ.bexs t).val = ^∃ (^#0 ^< termBShift ℒₒᵣ t.val) ^⋏ φ.val := by
  simp [Semiformula.bexs]

lemma neg_ball (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) :
    ∼(φ.ball t) = (∼φ).bexs t := by
  ext; simp [neg_all, neg_or, qqNLT, qqLT, t.isSemiterm.termBShift.isUTerm]

lemma neg_bexs (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) :
    ∼(φ.bexs t) = (∼φ).ball t := by
  ext; simp [neg_ex, neg_and, qqNLT, qqLT, t.isSemiterm.termBShift.isUTerm]


-- @@ L504-506 verbatim
@[simp] lemma shifts_ball (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) :
    (φ.ball t).shift = φ.shift.ball t.shift := by
  simp [Semiformula.ball, Semiterm.bShift_shift_comm]


-- @@ L508-510 verbatim
@[simp] lemma shifts_bexs (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) :
    (φ.bexs t).shift = φ.shift.bexs t.shift := by
  simp [Semiformula.bexs, Semiterm.bShift_shift_comm]


-- @@ L512-514 verbatim
@[simp] lemma substs_ball (w : SemitermVec V ℒₒᵣ n m) (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) :
    (φ.ball t).subst w = (φ.subst w.q).ball (t.subst w) := by
  simp [Semiformula.ball]


-- @@ L516-518 verbatim
@[simp] lemma substs_bexs (w : SemitermVec V ℒₒᵣ n m) (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) :
    (φ.bexs t).subst w = (φ.subst w.q).bexs (t.subst w) := by
  simp [Semiformula.bexs]


-- @@ L520-523 verbatim
end Arithmetic

lemma Semiformula.ball_eqss_imp (t : Semiterm V ℒₒᵣ n) (φ : Semiformula V ℒₒᵣ (n + 1)) :
    φ.ball t = ∀¹ ((Semiterm.bvar 0 <' t.bShift) 🡒 φ) := by simp [Semiformula.ball, imp_def]


-- @@ L525-525 verbatim
end FFL.FirstOrder.Arithmetic.Bootstrapping
