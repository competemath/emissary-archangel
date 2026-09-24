module

public import Foundation.FirstOrder.Bootstrapping.Syntax.Term.Functions


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-10 verbatim
/-!

# Typed Formalized IsSemiterm/Term

-/


-- @@ L12-12 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L14-14 verbatim
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


-- @@ L16-16 verbatim
noncomputable def matrixToVec (v : Fin k → V) : V := Matrix.foldr (fun t w ↦ t ∷ w) 0 v


-- @@ L18-18 verbatim
@[simp] lemma matrixToVec_nil (v : Fin 0 → V) : matrixToVec v = 0 := rfl


-- @@ L20-20 verbatim
@[simp] lemma matrixToVec_succ (v : Fin (k + 1) → V) : matrixToVec v = Matrix.vecHead v ∷ matrixToVec (Matrix.vecTail v) := rfl


-- @@ L22-23 verbatim
@[simp] lemma matrixToVec_len (v : Fin k → V) : len (matrixToVec v) = k := by
  induction k <;> simp [*]


-- @@ L25-30 verbatim
@[simp] lemma matrixToVec_nth (v : Fin k → V) (i : Fin k) : (matrixToVec v).[↑i] = v i := by
  induction k
  · exact i.elim0
  · cases i using Fin.cases
    · simp; rfl
    · simp [*]; rfl


-- @@ L32-32 verbatim
namespace Bootstrapping


-- @@ L34-34 verbatim
variable {L : Language} [L.Encodable] [L.LORDefinable]


-- @@ L36-36 verbatim
section typed_term


-- @@ L38-38 verbatim
variable (V L)


-- @@ L40-42 verbatim
structure Semiterm (n : ℕ) where
  val : V
  isSemiterm : IsSemiterm (V := V) L n val


-- @@ L44-44 verbatim
abbrev SemitermVec (m n : ℕ) := Fin m → Semiterm V L (n : ℕ)


-- @@ L46-46 verbatim
attribute [simp] Semiterm.isSemiterm


-- @@ L48-48 verbatim
abbrev Term := Semiterm (V := V) L 0


-- @@ L50-50 verbatim
abbrev TermVec (m : ℕ) := SemitermVec (V := V) L m 0


-- @@ L52-52 verbatim
variable {V L} {k n m : ℕ}


-- @@ L54-56 verbatim
@[ext]
lemma Semiterm.ext (t u : Semiterm V L n)
    (h : t.val = u.val) : t = u := by rcases t; rcases u; simpa using h


-- @@ L58-59 verbatim
@[simp] lemma Semiterm.isSemiterm_zero (t : Term V L) :
   IsSemiterm L 0 t.val := by simpa using t.isSemiterm


-- @@ L61-62 verbatim
@[simp] lemma Semiterm.isSemiterm_one (t : Semiterm V L 1) :
   IsSemiterm L 1 t.val := by simpa using t.isSemiterm


-- @@ L64-65 verbatim
@[simp] lemma Semiterm.isSemiterm_succ (t : Semiterm V L (n + 1)) :
    IsSemiterm L (↑n + 1 : V) t.val := by simpa using t.isSemiterm


-- @@ L67-67 verbatim
@[simp] lemma Semiterm.isUTerm (t : Semiterm V L n) : IsUTerm L t.val := t.isSemiterm.isUTerm


-- @@ L69-69 verbatim
noncomputable def SemitermVec.val (v : SemitermVec V L k n) : V := matrixToVec ((fun t ↦ t.val)⨟ v)


-- @@ L71-71 verbatim
@[simp] lemma SemitermVec.val_nil (v : SemitermVec V L 0 n) : v.val = 0 := rfl


-- @@ L73-74 verbatim
@[simp] lemma SemitermVec.val_cons (t : Semiterm V L n) (v : SemitermVec V L k n) :
    SemitermVec.val (t :> v : SemitermVec V L (k + 1) n) = t.val ∷ v.val := by rfl


-- @@ L76-83 verbatim
@[simp] lemma SemitermVec.val_succ (v : SemitermVec V L (k + 1) n) :
    SemitermVec.val (v : SemitermVec V L (k + 1) n) = (Matrix.vecHead v).val ∷ SemitermVec.val (Matrix.vecTail v) := by rfl

lemma SemitermVec.val_inj (v₁ v₂ : SemitermVec V L k n) : v₁ = v₂ ↔ v₁.val = v₂.val := by
    induction k
    · simp [Matrix.empty_eq]
    case succ k ih =>
      simp [← Semiterm.ext_iff, ←ih, Matrix.eq_iff_eq_vecHead_of_eq_vecTail]


-- @@ L85-86 verbatim
@[simp] lemma SemitermVec.isSemitermVec {k} (v : SemitermVec V L k n) : IsSemitermVec (V := V) L k n v.val := by
  induction k <;> simp [*]


-- @@ L88-89 verbatim
@[simp] lemma SemitermVec.isUTermVec {k} (v : SemitermVec V L k n) : IsUTermVec (V := V) L k v.val := by
  induction k <;> simp [*]


-- @@ L91-92 verbatim
@[simp] lemma SemitermVec.len_eq (v : SemitermVec V L k n) : len v.val = ↑k := by
  induction k <;> simp [*]


-- @@ L94-100 verbatim
@[simp] lemma SemitermVec.val_nth_eq (v : SemitermVec V L k n) (i : Fin k) :
    v.val.[(i : V)] = (v i).val := by
  induction k
  · apply finZeroElim i
  · cases i using Fin.cases
    · simp; rfl
    · simp [*]; rfl


-- @@ L102-102 verbatim
noncomputable def Semiterm.bvar (z : Fin n) : Semiterm V L n := ⟨^#z, by simp⟩


-- @@ L104-104 verbatim
noncomputable def Semiterm.fvar (x : V) : Semiterm V L n := ⟨^&x, by simp⟩


-- @@ L106-107 verbatim
noncomputable def Semiterm.func (f : L.Func k) (v : SemitermVec V L k n) :
    Semiterm V L n := ⟨^func ↑k ⌜f⌝ v.val , by simp⟩

-- @@ L108-108 verbatim
noncomputable abbrev Semiterm.bv (x : Fin n) : Semiterm V L n := Semiterm.bvar x

-- @@ L109-109 verbatim
noncomputable abbrev Semiterm.fv (x : V) : Semiterm V L n := Semiterm.fvar x


-- @@ L111-111 verbatim
@[simp] lemma Semiterm.bvar_val (z : Fin n) : (Semiterm.bvar z : Semiterm V L n).val = ^#(z : V) := rfl

-- @@ L112-112 verbatim
@[simp] lemma Semiterm.fvar_val (x : V) : (Semiterm.fvar x : Semiterm V L n).val = ^&x := rfl

-- @@ L113-114 verbatim
@[simp] lemma Semiterm.func_val (f : L.Func k) (v : SemitermVec V L k n) :
    (Semiterm.func f v).val = ^func ↑k ⌜f⌝ v.val := rfl



-- @@ L117-117 verbatim
namespace Semiterm


-- @@ L119-120 verbatim
@[simp] lemma bvar_inj_iff (z x : Fin n) :
    (bvar z : Semiterm V L n) = bvar x ↔ z = x := ⟨by simpa [bvar] using Fin.eq_of_val_eq, by rintro rfl; rfl⟩


-- @@ L122-122 verbatim
@[simp] lemma fvar_inj_iff (z x : V) : (fvar z : Semiterm V L n) = fvar x ↔ z = x := by simp [fvar]


-- @@ L124-127 verbatim
@[simp] lemma func_inj_iff (f₁ f₂ : L.Func k) (v₁ v₂ : SemitermVec V L k n) : func f₁ v₁ = func f₂ v₂ ↔ f₁ = f₂ ∧ v₁ = v₂ := by
  simp only [func, Semiterm.ext_iff, qqFunc_inj, quote_func_inj, true_and, and_congr_right_iff]
  rintro rfl
  symm; exact SemitermVec.val_inj v₁ v₂


-- @@ L129-130 verbatim
noncomputable def shift (t : Semiterm V L n) : Semiterm V L n :=
  ⟨termShift L t.val, IsSemiterm.termShift t.isSemiterm⟩


-- @@ L132-133 verbatim
noncomputable def bShift (t : Semiterm V L n) : Semiterm V L (n + 1) :=
  ⟨termBShift L t.val, IsSemiterm.termBShift t.isSemiterm⟩


-- @@ L135-136 verbatim
noncomputable def subst (w : SemitermVec V L n m) (t : Semiterm V L n) : Semiterm V L m :=
  ⟨termSubst L w.val t.val, w.isSemitermVec.termSubst t.isSemiterm⟩


-- @@ L138-139 verbatim
noncomputable def free (t : Semiterm V L 1) : Semiterm V L 0 :=
  t.shift.subst ![fvar 0]


-- @@ L141-141 verbatim
@[simp] lemma val_shift (t : Semiterm V L n) : t.shift.val = termShift L t.val := rfl

-- @@ L142-142 verbatim
@[simp] lemma val_bShift (t : Semiterm V L n) : t.bShift.val = termBShift L t.val := rfl

-- @@ L143-143 verbatim
@[simp] lemma val_substs (w : SemitermVec V L n m) (t : Semiterm V L n) : (t.subst w).val = termSubst L w.val t.val := rfl


-- @@ L145-145 verbatim
end Semiterm


-- @@ L147-147 verbatim
namespace SemitermVec


-- @@ L149-150 verbatim
@[simp] lemma val_shift (v : SemitermVec V L k n) : val (Semiterm.shift⨟ v) = termShiftVec L ↑k v.val := by
  induction k <;> simp [termShiftVec_cons, *]


-- @@ L152-153 verbatim
@[simp] lemma val_bShift (v : SemitermVec V L k n) : val (Semiterm.bShift⨟ v) = termBShiftVec L ↑k v.val := by
  induction k <;> simp [termBShiftVec_cons, *]


-- @@ L155-157 verbatim
@[simp] lemma val_substs (v : SemitermVec V L k n) (w : SemitermVec V L n m) :
    val ((Semiterm.subst w)⨟ v) = termSubstVec L ↑k w.val v.val := by
  induction k <;> simp [termSubstVec_cons, *]


-- @@ L159-159 verbatim
noncomputable def q (w : SemitermVec V L k n) : SemitermVec V L (k + 1) (n + 1) := Semiterm.bvar 0 :> Semiterm.bShift⨟ w


-- @@ L161-161 verbatim
@[simp] lemma q_zero (w : SemitermVec V L k n) : w.q 0 = Semiterm.bvar 0 := rfl


-- @@ L163-163 verbatim
@[simp] lemma q_succ (w : SemitermVec V L k n) (i : Fin k) : w.q i.succ = Semiterm.bShift (w i) := rfl


-- @@ L165-165 verbatim
@[simp] lemma q_val_eq_qVec (w : SemitermVec V L k n) : w.q.val = qVec L w.val := by simp [q, qVec]


-- @@ L167-167 verbatim
@[simp] lemma q_vecHead (w : SemitermVec V L k n) : Matrix.vecHead w.q = Semiterm.bvar 0 := rfl


-- @@ L169-169 verbatim
@[simp] lemma q_vecTail (w : SemitermVec V L k n) : Matrix.vecTail w.q = Semiterm.bShift⨟ w := rfl


-- @@ L171-171 verbatim
end SemitermVec


-- @@ L173-173 verbatim
namespace Semiterm


-- @@ L175-176 verbatim
@[simp] lemma shift_bvar (z : Fin n) :
    shift (Semiterm.bvar z : Semiterm V L n) = Semiterm.bvar z := by ext; simp [Semiterm.bvar, shift]


-- @@ L178-179 verbatim
@[simp] lemma shift_fvar (x : V) :
    shift (Semiterm.fvar x : Semiterm V L n) = Semiterm.fvar (x + 1) := by ext; simp [Semiterm.fvar, shift]


-- @@ L181-182 verbatim
@[simp] lemma shift_func (f : L.Func k) (v : SemitermVec V L k n) :
    shift (func f v) = func f (shift⨟ v) := by ext; simp [Semiterm.func, shift]


-- @@ L184-185 verbatim
@[simp] lemma bShift_bvar (z : Fin n) :
    bShift (Semiterm.bvar z : Semiterm V L n) = Semiterm.bvar z.succ := by ext; simp [Semiterm.bvar, bShift]


-- @@ L187-188 verbatim
@[simp] lemma bShift_fvar (x : V) :
    bShift (Semiterm.fvar x : Semiterm V L n) = Semiterm.fvar x := by ext; simp [Semiterm.fvar, bShift]


-- @@ L190-191 verbatim
@[simp] lemma bShift_func (f : L.Func k) (v : SemitermVec V L k n) :
    bShift (func f v) = func f (bShift⨟ v) := by ext; simp [Semiterm.func, bShift]


-- @@ L193-194 verbatim
@[simp] lemma substs_bvar (z : Fin n) (w : SemitermVec V L n m) :
    (Semiterm.bvar z).subst w = w z := by ext; simp [subst]


-- @@ L196-197 verbatim
@[simp] lemma substs_fvar (w : SemitermVec V L n m) (x : V) :
    (Semiterm.fvar x : Semiterm V L n).subst w = Semiterm.fvar x := by ext; simp [Semiterm.fvar, subst]


-- @@ L199-200 verbatim
@[simp] lemma substs_func (f : L.Func k) (w : SemitermVec V L n m) (v : SemitermVec V L k n) :
    (func f v).subst w = func f ((subst w)⨟ v) := by ext; simp [Semiterm.func, subst]


-- @@ L202-202 verbatim
@[simp] lemma free_bvar (z : Fin 1) : free (bvar z : Semiterm V L 1) = fvar 0 := by simp [free]


-- @@ L204-204 verbatim
@[simp] lemma free_fvar (x : V) : free (Semiterm.fvar x : Semiterm V L 1) = fvar (x + 1) := by simp [free]


-- @@ L206-208 verbatim
@[simp] lemma bShift_substs_q (t : Semiterm V L n) (w : SemitermVec V L n m) :
    t.bShift.subst w.q = (t.subst w).bShift := by
  ext; simp only [subst, SemitermVec.q_val_eq_qVec, bShift, substs_qVec_bShift t.isSemiterm w.isSemitermVec]


-- @@ L210-216 verbatim
@[simp] lemma bShift_substs_sing (t u : Term V L) :
    t.bShift.subst ![u] = t := by
  ext; simp [subst, bShift, substs_cons_bShift t.isSemiterm, substs_nil t.isSemiterm]

lemma bShift_substs_succ (w : SemitermVec V L (n + 1) m) (t : Semiterm V L n) :
    t.bShift.subst w = t.subst (Matrix.vecTail w) := by
  ext; simp [subst, bShift, substs_cons_bShift t.isSemiterm]


-- @@ L218-231 verbatim
@[simp] lemma bShift_substs_zero (t : Term V L) :
    t.subst ![] = t := by
  ext; simp [subst]

lemma bShift_shift_comm (t : Semiterm V L n) :
    t.shift.bShift = t.bShift.shift := by
  ext; simp [termBShift_termShift t.isSemiterm]

lemma shift_substs (w : SemitermVec V L n m) (t : Semiterm V L n) :
    (t.subst w).shift = t.shift.subst (Semiterm.shift⨟ w) := by ext; simp [Bootstrapping.termShift_termSubsts t.isSemiterm w.isSemitermVec]

lemma substs_substs {n m l : ℕ} (v : SemitermVec V L m l) (w : SemitermVec V L n m) (t : Semiterm V L n) :
    (t.subst w).subst v = t.subst ((Semiterm.subst v)⨟ w) := by
  ext;simp [Bootstrapping.termSubst_termSubst w.isSemitermVec t.isSemiterm]


-- @@ L233-233 verbatim
end Semiterm


-- @@ L235-235 verbatim
end typed_term


-- @@ L237-237 verbatim
section typed_isfvfree


-- @@ L239-239 verbatim
variable {k n m : ℕ}


-- @@ L241-241 verbatim
namespace Semiterm


-- @@ L243-246 verbatim
def FVFree (t : Semiterm V L n) : Prop := IsTermFVFree L ↑n t.val

lemma FVFree.iff {t : Semiterm V L n} : t.FVFree ↔ t.shift = t := by
  simp [FVFree, IsTermFVFree, Semiterm.ext_iff]


-- @@ L248-248 verbatim
@[simp] lemma FVFree.bvar (i : Fin n) : (Semiterm.bvar i : Semiterm V L n).FVFree := by simp [FVFree]


-- @@ L250-251 verbatim
@[simp] lemma FVFree.bShift (t : Semiterm V L n) (ht : t.FVFree) :
    t.bShift.FVFree := by simp [FVFree.iff, ←bShift_shift_comm, FVFree.iff.mp ht]


-- @@ L253-253 verbatim
end Semiterm


-- @@ L255-255 verbatim
end typed_isfvfree


-- @@ L257-263 verbatim
namespace Arithmetic

-- `Arithmetic` is intentionally re-opened here even though the ambient namespace
-- already contains it; renaming would break the widely-used public API
-- (`Bootstrapping.Arithmetic.*`). Suppress the new dupNamespace linter for the
-- declarations in this namespace (the option is scoped by `namespace`/`end` and
-- reverts automatically at `end FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic`).

-- @@ L264-264 verbatim
set_option linter.dupNamespace false


-- @@ L266-266 verbatim
variable {k n m : ℕ}


-- @@ L268-268 verbatim
noncomputable def typedNumeral (m : V) : Semiterm V ℒₒᵣ n := ⟨numeral m, by simp⟩


-- @@ L270-270 verbatim
scoped prefix:max "𝕹" => typedNumeral


-- @@ L272-272 verbatim
noncomputable def add (t u : Semiterm V ℒₒᵣ n) : Semiterm V ℒₒᵣ n := ⟨t.val ^+ u.val, by simp [qqAdd]⟩


-- @@ L274-274 verbatim
noncomputable def mul (t u : Semiterm V ℒₒᵣ n) : Semiterm V ℒₒᵣ n := ⟨t.val ^* u.val, by simp [qqMul]⟩


-- @@ L276-276 verbatim
noncomputable instance (n : ℕ) : Add (Semiterm V ℒₒᵣ n) := ⟨add⟩


-- @@ L278-278 verbatim
noncomputable instance (n : ℕ) : Mul (Semiterm V ℒₒᵣ n) := ⟨mul⟩


-- @@ L280-280 verbatim
@[simp] lemma val_numeral (x : V) : (𝕹 x : Semiterm V ℒₒᵣ n).val = numeral x := rfl


-- @@ L282-282 verbatim
@[simp] lemma val_add (t₁ t₂ : Semiterm V ℒₒᵣ n) : (t₁ + t₂).val = t₁.val ^+ t₂.val := rfl


-- @@ L284-284 verbatim
@[simp] lemma val_mul (t₁ t₂ : Semiterm V ℒₒᵣ n) : (t₁ * t₂).val = t₁.val ^* t₂.val := rfl


-- @@ L286-288 verbatim
@[simp] lemma zero_eq (v) :
    Semiterm.func (V := V) (n := n) (Language.Zero.zero : (ℒₒᵣ).Func 0) v = typedNumeral 0 := by
  ext; simp [coe_zero_eq]


-- @@ L290-292 verbatim
@[simp] lemma one_eq (v) :
    Semiterm.func (V := V) (n := n) (Language.One.one : (ℒₒᵣ).Func 0) v = typedNumeral 1 := by
  ext; simp [coe_one_eq]


-- @@ L294-296 verbatim
@[simp] lemma add_eq (v : Fin 2 → Semiterm V ℒₒᵣ n) :
    Semiterm.func (Language.Add.add : (ℒₒᵣ).Func 2) v = v 0 + v 1 := by
  ext; rfl


-- @@ L298-300 verbatim
@[simp] lemma mul_eq (v : Fin 2 → Semiterm V ℒₒᵣ n) :
    Semiterm.func (Language.Mul.mul : (ℒₒᵣ).Func 2) v = v 0 * v 1 := by
  ext; rfl


-- @@ L302-304 verbatim
@[simp] lemma add_inj_iff {t₁ t₂ u₁ u₂ : Semiterm V ℒₒᵣ n} :
    t₁ + t₂ = u₁ + u₂ ↔ t₁ = u₁ ∧ t₂ = u₂ := by
  simp [Semiterm.ext_iff, qqAdd]


-- @@ L306-308 verbatim
@[simp] lemma mul_inj_iff {t₁ t₂ u₁ u₂ : Semiterm V ℒₒᵣ n} :
    t₁ * t₂ = u₁ * u₂ ↔ t₁ = u₁ ∧ t₂ = u₂ := by
  simp [Semiterm.ext_iff, qqMul]


-- @@ L310-316 verbatim
@[simp] lemma numeral_add_two' (x : V) :
    (typedNumeral (x + 1 + 1) : Semiterm V ℒₒᵣ n) = typedNumeral (x + 1) + typedNumeral 1 := by
  ext; simp [numeral]

lemma numeral_succ_pos' {x : V} (pos : 0 < x) :
    (typedNumeral (x + 1) : Semiterm V ℒₒᵣ n) = typedNumeral x + typedNumeral 1 := by
  ext; simp [numeral_succ_pos pos]


-- @@ L318-320 verbatim
@[simp] lemma subst_numeral (w : SemitermVec V ℒₒᵣ n m) (x : V) :
    (𝕹 x : Semiterm V ℒₒᵣ n).subst w = 𝕹 x := by
  ext; simp [Semiterm.subst, numeral_substs w.isSemitermVec]


-- @@ L322-324 verbatim
@[simp] lemma subst_add (w : SemitermVec V ℒₒᵣ n m) (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ + t₂).subst w = t₁.subst w + t₂.subst w := by
  ext; simp [qqAdd, Semiterm.subst]


-- @@ L326-328 verbatim
@[simp] lemma subst_mul (w : SemitermVec V ℒₒᵣ n m) (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ * t₂).subst w = t₁.subst w * t₂.subst w := by
  ext; simp [qqMul, Semiterm.subst]


-- @@ L330-331 verbatim
@[simp] lemma shift_numeral (x : V) : (𝕹 x : Semiterm V ℒₒᵣ n).shift = 𝕹 x := by
  ext; simp [Semiterm.shift]


-- @@ L333-334 verbatim
@[simp] lemma shift_add (t₁ t₂ : Semiterm V ℒₒᵣ n) : (t₁ + t₂).shift = t₁.shift + t₂.shift := by
  ext; simp [qqAdd, Semiterm.shift]


-- @@ L336-337 verbatim
@[simp] lemma shift_mul (t₁ t₂ : Semiterm V ℒₒᵣ n) : (t₁ * t₂).shift = t₁.shift * t₂.shift := by
  ext; simp [qqMul, Semiterm.shift]


-- @@ L339-340 verbatim
@[simp] lemma bShift_numeral (x : V) : (𝕹 x : Semiterm V ℒₒᵣ n).bShift = 𝕹 x := by
  ext; simp [Semiterm.bShift]


-- @@ L342-343 verbatim
@[simp] lemma bShift_add (t₁ t₂ : Semiterm V ℒₒᵣ n) : (t₁ + t₂).bShift = t₁.bShift + t₂.bShift := by
  ext; simp [qqAdd, Semiterm.bShift]


-- @@ L345-346 verbatim
@[simp] lemma bShift_mul (t₁ t₂ : Semiterm V ℒₒᵣ n) : (t₁ * t₂).bShift = t₁.bShift * t₂.bShift := by
  ext; simp [qqMul, Semiterm.bShift]


-- @@ L348-348 verbatim
@[simp] lemma fvFree_numeral (x : V) : (𝕹 x : Semiterm V ℒₒᵣ n).FVFree := by simp [Semiterm.FVFree.iff]


-- @@ L350-351 verbatim
@[simp] lemma fvFree_add (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ + t₂).FVFree ↔ t₁.FVFree ∧ t₂.FVFree := by simp [Semiterm.FVFree.iff]


-- @@ L353-354 verbatim
@[simp] lemma fvFree_mul (t₁ t₂ : Semiterm V ℒₒᵣ n) :
    (t₁ * t₂).FVFree ↔ t₁.FVFree ∧ t₂.FVFree := by simp [Semiterm.FVFree.iff]


-- @@ L356-357 verbatim
@[simp] lemma free_add (t₁ t₂ : Semiterm V ℒₒᵣ 1) : (t₁ + t₂).free = t₁.free + t₂.free := by
  simp [Semiterm.free]


-- @@ L359-360 verbatim
@[simp] lemma free_mul (t₁ t₂ : Semiterm V ℒₒᵣ 1) : (t₁ * t₂).free = t₁.free * t₂.free := by
  simp [Semiterm.free]


-- @@ L362-396 verbatim
@[simp] lemma free_numeral (x : V) : (𝕹 x : Semiterm V ℒₒᵣ 1).free = 𝕹 x := by simp [Semiterm.free]

/-
lemma replace {P : α → isSemiterm} {x y} (hx : P x) (h : x = y) : P y := h ▸ hx

lemma semiterm_induction (Γ) {n : V} {P : Semiterm V ℒₒᵣ n → isSemiterm}
    (hP : Γ-[1]-Predicate (fun x ↦ (h : IsSemiterm ℒₒᵣ n x) → P ⟨x, h⟩))
    (hBvar : ∀ (z : V) (h : z < n), P (bvar ℒₒᵣ z h))
    (hFvar : ∀ x, P (⌜ℒₒᵣ⌝.fvar x))
    (hZero : P ((0 : V) : Semiterm V ℒₒᵣ n))
    (hOne : P ((1 : V) : Semiterm V ℒₒᵣ n))
    (hAdd : ∀ t₁ t₂, P t₁ → P t₂ → P (t₁ + t₂))
    (hMul : ∀ t₁ t₂, P t₁ → P t₂ → P (t₁ * t₂)) :
    ∀ (t : ⌜ℒₒᵣ⌝[V].Semiterm n), P t := by
  let Q := fun x ↦ (h : IsSemiterm ℒₒᵣ n x) → P ⟨x, h⟩
  suffices ∀ t, IsSemiterm ℒₒᵣ n t → Q t by intro t; exact this t.val t.isSemiterm t.isSemiterm
  apply IsSemiterm.induction Γ hP
  case hbvar => intro z hz _; exact hBvar z hz
  case hfvar => intro x _; exact hFvar x
  case hfunc =>
    intro k f v hf hv ih _
    rcases (by simpa [func_iff] using hf) with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rcases (by simpa using hv)
      exact replace hZero (by ext; simp [Formalized.zero, qqFunc_absolute])
    · rcases (by simpa using hv)
      exact replace hOne (by ext; simp [Formalized.one, qqFunc_absolute])
    · rcases IsSemitermVec.two_iff.mp hv with ⟨t₁, t₂, ht₁, ht₂, rfl⟩
      exact hAdd ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
        (by simpa using ih 0 (by simp) (by simp [ht₁]))
        (by simpa using ih 1 (by simp) (by simp [ht₂]))
    · rcases IsSemitermVec.two_iff.mp hv with ⟨t₁, t₂, ht₁, ht₂, rfl⟩
      exact hMul ⟨t₁, ht₁⟩ ⟨t₂, ht₂⟩
        (by simpa using ih 0 (by simp) (by simp [ht₁]))
        (by simpa using ih 1 (by simp) (by simp [ht₂]))
-/


-- @@ L398-398 verbatim
end FFL.FirstOrder.Arithmetic.Bootstrapping.Arithmetic
