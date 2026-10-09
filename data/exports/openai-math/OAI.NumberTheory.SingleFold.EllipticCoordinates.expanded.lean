import OAI.NumberTheory.SingleFold.RationalCodes


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SingleFold.PointCompiler


-- @@ L7-7 verbatim
section

-- @@ L8-8 verbatim
open Compiler RationalCompiler

-- @@ L9-9 verbatim
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point


-- @@ L11-11 verbatim
def E : WeierstrassCurve.Affine ℚ := ⟨0,0,0,-25,0⟩

-- @@ L12-14 verbatim
instance : E.IsElliptic := by
  constructor
  norm_num [E,WeierstrassCurve.Δ,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]

-- @@ L15-17 verbatim
lemma equation_iff (x y : ℚ) : E.Nonsingular x y ↔ y^2=x^3-25*x := by
  rw [←E.equation_iff_nonsingular]
  simp [WeierstrassCurve.Affine.equation_iff,E,sub_eq_add_neg]


-- @@ L19-22 verbatim
structure Code where
  flag : ℕ
  x : RationalCode
  y : RationalCode


-- @@ L24-26 verbatim
def Code.Valid (c : Code) : Prop := c.x.Valid ∧ c.y.Valid ∧
  ((c.flag=1 ∧ c.x.value=0 ∧ c.y.value=0) ∨
   (c.flag=0 ∧ c.y.value^2=c.x.value^3-25*c.x.value))

-- @@ L27-28 verbatim
noncomputable def Code.toPoint (c : Code) (hc : c.Valid) : E.Point :=
  if h : c.flag=1 then 0 else some c.x.value c.y.value ((equation_iff _ _).mpr (hc.2.2.resolve_left (by tauto)).2)

-- @@ L29-31 verbatim
noncomputable def encode : E.Point → Code
  | .zero => ⟨1,RationalCode.encode 0,RationalCode.encode 0⟩
  | .some x y _ => ⟨0,RationalCode.encode x,RationalCode.encode y⟩

-- @@ L32-37 verbatim
lemma encode_valid (P : E.Point) : (encode P).Valid := by
  cases P with
  | zero => exact ⟨RationalCode.encode_valid _,RationalCode.encode_valid _,Or.inl ⟨rfl,RationalCode.encode_value _,RationalCode.encode_value _⟩⟩
  | some x y hp =>
    refine ⟨RationalCode.encode_valid _,RationalCode.encode_valid _,Or.inr ⟨rfl,?_⟩⟩
    simpa [encode,RationalCode.encode_value] using (equation_iff _ _).mp hp

-- @@ L38-47 verbatim
lemma Code.encode_toPoint (c : Code) (hc : c.Valid) : encode (c.toPoint hc)=c := by
  by_cases hf : c.flag=1
  · have hxy := (hc.2.2.resolve_right (by rintro ⟨h,_⟩; omega)).2
    have hx : RationalCode.encode 0=c.x := RationalCode.unique (RationalCode.encode_valid _) hc.1 ((RationalCode.encode_value _).trans hxy.1.symm)
    have hy : RationalCode.encode 0=c.y := RationalCode.unique (RationalCode.encode_valid _) hc.2.1 ((RationalCode.encode_value _).trans hxy.2.symm)
    simp only [Code.toPoint,dite_eq_left hf,encode,hx]
    cases c; simp_all
  · have hf0 := (hc.2.2.resolve_left (by tauto)).1
    simp only [Code.toPoint,dite_eq_right hf,encode,←RationalCode.eq_encode hc.1,←RationalCode.eq_encode hc.2.1]
    cases c; simp_all

-- @@ L48-51 verbatim
lemma encode_toPoint (P : E.Point) : (encode P).toPoint (encode_valid P)=P := by
  cases P with
  | zero => simp [Code.toPoint,encode,←zero_def]
  | some x y h => simp [Code.toPoint,encode,RationalCode.encode_value]

-- @@ L52-53 verbatim
lemma Code.unique {c d : Code} (hc : c.Valid) (hd : d.Valid) (he : c.toPoint hc=d.toPoint hd) : c=d := by
  rw [←c.encode_toPoint hc,←d.encode_toPoint hd,he]


-- @@ L55-55 verbatim
abbrev Var := Unit ⊕ (Fin 2 × Fin 6)

-- @@ L56-57 verbatim
def fromTuple (z : Var → ℕ) : Code :=
  ⟨z (.inl ()),code (fun j => z (.inr (0,j))),code (fun j => z (.inr (1,j)))⟩

-- @@ L58-58 verbatim
def tuple (c : Code) : Var → ℕ := Sum.elim (fun _ => c.flag) (fun ij => if ij.1=0 then RationalCompiler.tuple c.x ij.2 else RationalCompiler.tuple c.y ij.2)

-- @@ L59-62 verbatim
lemma from_tuple (c : Code) : fromTuple (tuple c)=c := by
  simp only [fromTuple,tuple,Sum.elim_inl,Sum.elim_inr,ite_true,show (1:Fin 2)≠0 by decide,ite_false]
  change Code.mk c.flag (code (RationalCompiler.tuple c.x)) (code (RationalCompiler.tuple c.y))=c
  rw [code_tuple,code_tuple]

-- @@ L63-67 verbatim
lemma tuple_from (z : Var → ℕ) : tuple (fromTuple z)=z := by
  funext i
  rcases i with i|⟨i,j⟩
  · rfl
  · fin_cases i <;> fin_cases j <;> rfl


-- @@ L69-94 verbatim
lemma code_valid_semi : Semi (fun z => (fromTuple z).Valid) := by
  let f : Fin 2 × Fin 6 → Var := Sum.inr
  let G : (Var → ℕ) → Prop := fun z => Valid (z ∘ f)
  have hg : Semi G := valid_semi.reindex f
  have eqc (p q : Expr (Fin 2)) := Expr.eq_under hg f (fun _ h => h) p q
  let x : Expr (Fin 2) := .var 0
  let y : Expr (Fin 2) := .var 1
  have ho := (Semi.eq (Poly.proj (.inl () : Var)) 1).and ((eqc x 0).and (eqc y 0))
  have ha := (Semi.eq (Poly.proj (.inl () : Var)) 0).and (eqc (y^2) (x^3-25*x))
  refine (ho.or ha).congr ?_
  intro z
  have hG : G z ↔ (fromTuple z).x.Valid ∧ (fromTuple z).y.Valid := by
    change (∀ i : Fin 2, (code (fun j => z (Sum.inr (i,j)))).Valid) ↔ _
    constructor
    · intro h; exact ⟨h 0,h 1⟩
    · intro h i; fin_cases i; exact h.1; exact h.2
  simp only [Expr.eval_pow,Expr.eval_sub,Expr.eval_mul,Expr.eval_zero,
    Expr.eval_var,Poly.proj_apply,Poly.one_apply,Poly.zero_apply,x,y] at *
  change (((z (.inl ()):ℤ)=1 ∧ (G z ∧ (fromTuple z).x.value=0) ∧ G z ∧ (fromTuple z).y.value=0) ∨
    (z (.inl ()):ℤ)=0 ∧ G z ∧ (fromTuple z).y.value^2=(fromTuple z).x.value^3-25*(fromTuple z).x.value) ↔ _
  rw [hG]
  have h1 : (z (.inl ()):ℤ)=1 ↔ z (.inl ())=1 := by omega
  have h0 : (z (.inl ()):ℤ)=0 ↔ z (.inl ())=0 := by omega
  rw [h1,h0]
  dsimp only [Code.Valid,fromTuple]
  tauto


-- @@ L96-97 verbatim
def Line (d n x₁ x₂ y₁ x₃ y₃ : ℚ) : Prop :=
  d^2*(x₃+x₁+x₂)=n^2 ∧ d*(y₃+y₁)=n*(x₁-x₃)

-- @@ L98-111 verbatim
lemma line_iff {d n x₁ x₂ y₁ x₃ y₃ : ℚ} (hd : d≠0) :
    Line d n x₁ x₂ y₁ x₃ y₃ ↔
      x₃=(n/d)^2-x₁-x₂ ∧ y₃=n/d*(x₁-x₃)-y₁ := by
  unfold Line
  constructor
  · rintro ⟨hx,hy⟩
    constructor
    · field_simp
      nlinarith only [hx]
    · field_simp
      nlinarith only [hy]
  · rintro ⟨hx,hy⟩
    field_simp at hx hy
    constructor <;> nlinarith only [hx,hy]


-- @@ L113-113 verbatim
@[simp] lemma E_addX (x₁ x₂ l : ℚ) : E.addX x₁ x₂ l=l^2-x₁-x₂ := by simp [E]

-- @@ L114-114 verbatim
@[simp] lemma E_addY (x₁ x₂ y₁ l : ℚ) : E.addY x₁ x₂ y₁ l=l*(x₁-(l^2-x₁-x₂))-y₁ := by simp [WeierstrassCurve.Affine.addY,WeierstrassCurve.Affine.negAddY,WeierstrassCurve.Affine.negY,E]; ring

-- @@ L115-115 verbatim
@[simp] lemma E_negY (x y : ℚ) : E.negY x y= -y := by simp [E]


-- @@ L117-124 verbatim
lemma line_chord {x₁ x₂ y₁ y₂ x₃ y₃ : ℚ}
    (h₁ : E.Nonsingular x₁ y₁) (h₂ : E.Nonsingular x₂ y₂) (h₃ : E.Nonsingular x₃ y₃)
    (hx : x₁≠x₂) :
    Line (x₁-x₂) (y₁-y₂) x₁ x₂ y₁ x₃ y₃ ↔ some x₁ y₁ h₁+some x₂ y₂ h₂=some x₃ y₃ h₃ := by
  rw [line_iff (sub_ne_zero.mpr hx),add_of_X_ne hx,some.injEq,slope_of_X_ne hx,E_addX,E_addY]
  constructor
  · rintro ⟨hx,hy⟩; exact ⟨hx.symm,by rw [←hx]; exact hy.symm⟩
  · rintro ⟨hx,hy⟩; exact ⟨hx.symm,by rw [hx] at hy; exact hy.symm⟩

-- @@ L125-136 verbatim
lemma line_tangent {x y x₃ y₃ : ℚ}
    (h : E.Nonsingular x y) (h₃ : E.Nonsingular x₃ y₃) (hy : y≠0) :
    Line (2*y) (3*x^2-25) x x y x₃ y₃ ↔ some x y h+some x y h=some x₃ y₃ h₃ := by
  have hyn : y≠E.negY x y := by rw [E_negY]; intro he; apply hy; linarith
  have hs : E.slope x x y y=(3*x^2-25)/(2*y) := by
    rw [slope_of_Y_ne rfl hyn,E_negY]
    simp only [E]
    congr 1 <;> ring
  rw [line_iff (mul_ne_zero (by norm_num) hy),add_self_of_Y_ne hyn,some.injEq,hs,E_addX,E_addY]
  constructor
  · rintro ⟨hx,hy⟩; exact ⟨hx.symm,by rw [←hx]; exact hy.symm⟩
  · rintro ⟨hx,hy⟩; exact ⟨hx.symm,by rw [hx] at hy; exact hy.symm⟩


-- @@ L138-145 verbatim
def AddEq (a b c : Code) : Prop :=
  (a.flag=1 ∧ c=b) ∨
  (a.flag=0 ∧ b.flag=1 ∧ c=a) ∨
  (a.flag=0 ∧ b.flag=0 ∧ a.x.value=b.x.value ∧ a.y.value+b.y.value=0 ∧ c.flag=1) ∨
  (a.flag=0 ∧ b.flag=0 ∧ a.x.value≠b.x.value ∧ c.flag=0 ∧
    Line (a.x.value-b.x.value) (a.y.value-b.y.value) a.x.value b.x.value a.y.value c.x.value c.y.value) ∨
  (a.flag=0 ∧ b.flag=0 ∧ a.x.value=b.x.value ∧ a.y.value+b.y.value≠0 ∧ c.flag=0 ∧
    Line (2*a.y.value) (3*a.x.value^2-25) a.x.value a.x.value a.y.value c.x.value c.y.value)


-- @@ L147-151 verbatim
lemma encode_injective : Function.Injective encode := by
  intro p q he
  have he' : (⟨encode p,encode_valid p⟩ : {c : Code // c.Valid})=⟨encode q,encode_valid q⟩ := Subtype.ext he
  have hh := congrArg (fun c : {c : Code // c.Valid} => c.1.toPoint c.2) he'
  simpa only [encode_toPoint] using hh


-- @@ L153-192 verbatim
lemma addEq_encode (P Q R : E.Point) : AddEq (encode P) (encode Q) (encode R) ↔ P+Q=R := by
  cases P with
  | zero =>
    simp only [AddEq,encode,one_ne_zero,false_and,true_and,or_false]
    change (encode R=encode Q) ↔ (0:E.Point)+Q=R
    simp only [zero_add,encode_injective.eq_iff,eq_comm]
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero =>
      simp only [AddEq,encode,zero_ne_one,false_and,true_and,false_or,one_ne_zero]
      change (encode R=encode (some x₁ y₁ h₁)) ∨ False ↔ some x₁ y₁ h₁+(0:E.Point)=R
      simp only [or_false,add_zero,encode_injective.eq_iff,eq_comm]
    | some x₂ y₂ h₂ =>
      have hv := (equation_iff _ _).mp h₁
      have hw := (equation_iff _ _).mp h₂
      by_cases hx : x₁=x₂
      · subst x₂
        by_cases hy : y₁+y₂=0
        · have he : y₁=E.negY x₁ y₂ := by rw [E_negY]; linarith
          rw [add_of_Y_eq rfl he]
          cases R <;> simp [AddEq,encode,RationalCode.encode_value,hy,←zero_def]
        · have hy' : y₁=y₂ := by
            rcases (sq_eq_sq_iff_eq_or_eq_neg).mp (hv.trans hw.symm) with hh|hh
            · exact hh
            · exact False.elim (hy (by linarith))
          subst y₂
          have hyn : y₁≠0 := by intro he; simp [he] at hy
          cases R with
          | zero =>
            have hn : y₁≠E.negY x₁ y₁ := by rw [E_negY]; intro he; apply hyn; linarith
            rw [add_self_of_Y_ne hn]
            simp [AddEq,encode,RationalCode.encode_value,hy,←zero_def]
          | some x₃ y₃ h₃ =>
            simpa [AddEq,encode,RationalCode.encode_value,hy] using line_tangent h₁ h₃ hyn
      · cases R with
        | zero =>
          rw [add_of_X_ne hx]
          simp [AddEq,encode,RationalCode.encode_value,hx,←zero_def]
        | some x₃ y₃ h₃ =>
          simpa [AddEq,encode,RationalCode.encode_value,hx] using line_chord h₁ h₂ h₃ hx


-- @@ L194-196 verbatim
lemma addEq_spec (a b c : Code) (ha : a.Valid) (hb : b.Valid) (hc : c.Valid) :
    AddEq a b c ↔ a.toPoint ha+b.toPoint hb=c.toPoint hc := by
  simpa only [Code.encode_toPoint] using addEq_encode (a.toPoint ha) (b.toPoint hb) (c.toPoint hc)

-- @@ L197-206 verbatim
lemma addition_existsUnique (a b : Code) (ha : a.Valid) (hb : b.Valid) :
    ∃! c : Code, c.Valid ∧ AddEq a b c := by
  let P := a.toPoint ha+b.toPoint hb
  have hc := encode_valid P
  have hh : AddEq a b (encode P) := (addEq_spec _ _ _ ha hb hc).mpr (encode_toPoint P).symm
  refine ⟨encode P,⟨hc,hh⟩,?_⟩
  rintro c ⟨hv,he⟩
  apply Code.unique hv hc
  rw [encode_toPoint P]
  exact ((addEq_spec _ _ _ ha hb hv).mp he).symm


-- @@ L208-208 verbatim
variable {ι : Type} [Finite ι]

-- @@ L209-209 verbatim
def At (z : ι×Var → ℕ) (i : ι) : Code := fromTuple (fun k => z (i,k))

-- @@ L210-210 verbatim
def AllValid (z : ι×Var → ℕ) : Prop := ∀ i, (At z i).Valid

-- @@ L211-212 verbatim
lemma allValid_semi : Semi (@AllValid ι) :=
  Semi.all (fun i => code_valid_semi.reindex (fun k => (i,k)))

-- @@ L213-215 verbatim
omit [Finite ι] in
lemma flag_semi (i : ι) (n : ℕ) : Semi (fun z => (At z i).flag=n) :=
  (Semi.eq (Poly.proj (i,Sum.inl ())) (Poly.const n)).congr (by intro z; change (z (i,Sum.inl ()):ℤ)=(n:ℤ) ↔ _; exact_mod_cast Iff.rfl)

-- @@ L216-227 verbatim
omit [Finite ι] in
lemma codeEq_semi (i j : ι) : Semi (fun z => At z i=At z j) := by
  have h : Semi (fun z : ι×Var → ℕ => ∀ k, z (i,k)=z (j,k)) :=
    Semi.all (fun k => (Semi.eq (Poly.proj (i,k)) (Poly.proj (j,k))).congr (by intro z; change (z (i,k):ℤ)=(z (j,k):ℤ) ↔ _; exact_mod_cast Iff.rfl))
  refine h.congr ?_
  intro z
  constructor
  · intro he; exact congrArg fromTuple (funext he)
  · intro he k
    have hh := congrArg tuple he
    simp only [At,tuple_from] at hh
    exact congrFun hh k


-- @@ L229-229 verbatim
def ratMap : (ι×Fin 2)×Fin 6 → ι×Var := fun v => (v.1.1,Sum.inr (v.1.2,v.2))

-- @@ L230-230 verbatim
def values (z : ι×Var → ℕ) : ι×Fin 2 → ℚ := value (z ∘ ratMap)

-- @@ L231-231 verbatim
def xe (i : ι) : Expr (ι×Fin 2) := .var (i,0)

-- @@ L232-232 verbatim
def ye (i : ι) : Expr (ι×Fin 2) := .var (i,1)

-- @@ L233-238 verbatim
omit [Finite ι] in
lemma allValid_rational (z) (hz : AllValid z) : Valid (z ∘ @ratMap ι) := by
  intro ⟨i,v⟩
  fin_cases v
  · exact (hz i).1
  · exact (hz i).2.1

-- @@ L239-240 verbatim
lemma exprEq_semi (p q : Expr (ι×Fin 2)) : Semi (fun z => AllValid z ∧ p.eval (values z)=q.eval (values z)) :=
  Expr.eq_under allValid_semi ratMap allValid_rational p q

-- @@ L241-242 verbatim
lemma exprNe_semi (p q : Expr (ι×Fin 2)) : Semi (fun z => AllValid z ∧ p.eval (values z)≠q.eval (values z)) :=
  (allValid_semi.and (exprEq_semi p q).not).congr (by intro z; tauto)

-- @@ L243-249 verbatim
lemma line_semi (d n x₁ x₂ y₁ x₃ y₃ : Expr (ι×Fin 2)) :
    Semi (fun z => AllValid z ∧ Line (d.eval (values z)) (n.eval (values z))
      (x₁.eval (values z)) (x₂.eval (values z)) (y₁.eval (values z)) (x₃.eval (values z)) (y₃.eval (values z))) := by
  refine ((exprEq_semi (d^2*(x₃+x₁+x₂)) (n^2)).and (exprEq_semi (d*(y₃+y₁)) (n*(x₁-x₃)))).congr ?_
  intro z
  simp only [Expr.eval_pow,Expr.eval_mul,Expr.eval_add,Expr.eval_sub,Line]
  tauto


-- @@ L251-257 verbatim
lemma chord_semi (i j k : ι) : Semi (fun z => AllValid z ∧
    Line ((At z i).x.value-(At z j).x.value) ((At z i).y.value-(At z j).y.value)
      (At z i).x.value (At z j).x.value (At z i).y.value (At z k).x.value (At z k).y.value) := by
  refine (line_semi (xe i-xe j) (ye i-ye j) (xe i) (xe j) (ye i) (xe k) (ye k)).congr ?_
  intro z
  simp only [Expr.eval_sub,xe,ye,Expr.eval_var]
  rfl

-- @@ L258-264 verbatim
lemma tangent_semi (i k : ι) : Semi (fun z => AllValid z ∧
    Line (2*(At z i).y.value) (3*(At z i).x.value^2-25)
      (At z i).x.value (At z i).x.value (At z i).y.value (At z k).x.value (At z k).y.value) := by
  refine (line_semi (2*ye i) (3*(xe i)^2-25) (xe i) (xe i) (ye i) (xe k) (ye k)).congr ?_
  intro z
  simp only [Expr.eval_pow,Expr.eval_sub,Expr.eval_mul,xe,ye,Expr.eval_var]
  rfl

-- @@ L265-265 verbatim
lemma xeq_semi (i j : ι) : Semi (fun z => AllValid z ∧ (At z i).x.value=(At z j).x.value) := exprEq_semi (xe i) (xe j)

-- @@ L266-266 verbatim
lemma xne_semi (i j : ι) : Semi (fun z => AllValid z ∧ (At z i).x.value≠(At z j).x.value) := exprNe_semi (xe i) (xe j)

-- @@ L267-267 verbatim
lemma yneg_semi (i j : ι) : Semi (fun z => AllValid z ∧ (At z i).y.value+(At z j).y.value=0) := exprEq_semi (ye i+ye j) 0

-- @@ L268-268 verbatim
lemma ynneg_semi (i j : ι) : Semi (fun z => AllValid z ∧ (At z i).y.value+(At z j).y.value≠0) := exprNe_semi (ye i+ye j) 0


-- @@ L270-272 verbatim
omit [Finite ι] in
lemma add1_semi (i j k : ι) : Semi (fun z => (At z i).flag=1 ∧ At z k=At z j) :=
  (flag_semi i 1).and (codeEq_semi k j)

-- @@ L273-275 verbatim
omit [Finite ι] in
lemma add2_semi (i j k : ι) : Semi (fun z => (At z i).flag=0 ∧ (At z j).flag=1 ∧ At z k=At z i) :=
  (flag_semi i 0).and ((flag_semi j 1).and (codeEq_semi k i))

-- @@ L276-279 verbatim
lemma add3_semi (i j k : ι) : Semi (fun z => AllValid z ∧ (At z i).flag=0 ∧ (At z j).flag=0 ∧
    (At z i).x.value=(At z j).x.value ∧ (At z i).y.value+(At z j).y.value=0 ∧ (At z k).flag=1) := by
  refine ((flag_semi i 0).and ((flag_semi j 0).and ((xeq_semi i j).and ((yneg_semi i j).and (flag_semi k 1))))).congr ?_
  intro z; tauto

-- @@ L280-285 verbatim
lemma add4_semi (i j k : ι) : Semi (fun z => AllValid z ∧ (At z i).flag=0 ∧ (At z j).flag=0 ∧
    (At z i).x.value≠(At z j).x.value ∧ (At z k).flag=0 ∧
    Line ((At z i).x.value-(At z j).x.value) ((At z i).y.value-(At z j).y.value)
      (At z i).x.value (At z j).x.value (At z i).y.value (At z k).x.value (At z k).y.value) := by
  refine ((flag_semi i 0).and ((flag_semi j 0).and ((xne_semi i j).and ((flag_semi k 0).and (chord_semi i j k))))).congr ?_
  intro z; tauto

-- @@ L286-291 verbatim
lemma add5_semi (i j k : ι) : Semi (fun z => AllValid z ∧ (At z i).flag=0 ∧ (At z j).flag=0 ∧
    (At z i).x.value=(At z j).x.value ∧ (At z i).y.value+(At z j).y.value≠0 ∧ (At z k).flag=0 ∧
    Line (2*(At z i).y.value) (3*(At z i).x.value^2-25)
      (At z i).x.value (At z i).x.value (At z i).y.value (At z k).x.value (At z k).y.value) := by
  refine ((flag_semi i 0).and ((flag_semi j 0).and ((xeq_semi i j).and ((ynneg_semi i j).and ((flag_semi k 0).and (tangent_semi i k)))))).congr ?_
  intro z; tauto

-- @@ L292-296 verbatim
lemma addEq_semi (i j k : ι) : Semi (fun z => AllValid z ∧ AddEq (At z i) (At z j) (At z k)) := by
  refine (allValid_semi.and ((add1_semi i j k).or ((add2_semi i j k).or ((add3_semi i j k).or ((add4_semi i j k).or (add5_semi i j k)))))).congr ?_
  intro z
  unfold AddEq
  tauto

-- @@ L297-297 verbatim
end


-- @@ L299-299 verbatim
open Compiler RationalCompiler

-- @@ L300-300 verbatim
open WeierstrassCurve.Affine.Point


-- @@ L302-305 verbatim
lemma fromTuple_injective : Function.Injective fromTuple := by
  intro x y h
  have hh := congrArg tuple h
  simpa only [tuple_from] using hh


-- @@ L307-307 verbatim
def MulRel (n : ℕ) (a b : Code) : Prop := ∃ P : E.Point, a=encode P ∧ b=encode (n • P)

-- @@ L308-310 verbatim
lemma mulRel_valid {n a b} (h : MulRel n a b) : a.Valid ∧ b.Valid := by
  obtain ⟨P,rfl,rfl⟩ := h
  exact ⟨encode_valid _,encode_valid _⟩

-- @@ L311-314 verbatim
lemma mulRel_unique {n a b c} (hb : MulRel n a b) (hc : MulRel n a c) : b=c := by
  obtain ⟨P,rfl,rfl⟩ := hb
  obtain ⟨Q,hq,rfl⟩ := hc
  exact congrArg (fun P => encode (n • P)) (encode_injective hq)

-- @@ L315-318 verbatim
lemma mulRel_exists (n : ℕ) (a : Code) (ha : a.Valid) : ∃! b, MulRel n a b := by
  refine ⟨encode (n • a.toPoint ha),⟨a.toPoint ha,(a.encode_toPoint ha).symm,rfl⟩,?_⟩
  intro b hb
  exact mulRel_unique hb ⟨a.toPoint ha,(a.encode_toPoint ha).symm,rfl⟩

-- @@ L319-322 verbatim
lemma mulRel_zero (a b : Code) : MulRel 0 a b ↔ a.Valid ∧ b=encode 0 := by
  constructor
  · rintro ⟨P,rfl,hb⟩; exact ⟨encode_valid _,by simpa using hb⟩
  · rintro ⟨ha,rfl⟩; exact ⟨a.toPoint ha,(a.encode_toPoint ha).symm,by simp⟩

-- @@ L323-335 verbatim
lemma mulRel_succ (n : ℕ) (a b : Code) : MulRel (n+1) a b ↔
    ∃ c, MulRel n a c ∧ c.Valid ∧ a.Valid ∧ b.Valid ∧ AddEq c a b := by
  constructor
  · rintro ⟨P,rfl,rfl⟩
    refine ⟨encode (n • P),⟨P,rfl,rfl⟩,encode_valid _,encode_valid _,encode_valid _,?_⟩
    apply (addEq_encode _ _ _).mpr
    exact (add_nsmul P n 1).symm.trans (by simp)
  · rintro ⟨c,⟨P,rfl,rfl⟩,_,_,hb,he⟩
    refine ⟨P,rfl,?_⟩
    have hh := (addEq_spec _ _ _ (encode_valid _) (encode_valid _) hb).mp he
    rw [encode_toPoint,encode_toPoint] at hh
    have hh' : b.toPoint hb=(n+1) • P := by rw [←hh,add_nsmul,one_nsmul]
    exact (b.encode_toPoint hb).symm.trans (congrArg encode hh')


-- @@ L337-337 verbatim
variable {α : Type}

-- @@ L338-338 verbatim
lemma valid_sf (f : Var → α) : SF (fun z => (fromTuple (z ∘ f)).Valid) := code_valid_semi.1.reindex f

-- @@ L339-346 verbatim
lemma const_sf (f : Var → α) (c : Code) : SF (fun z => fromTuple (z ∘ f)=c) := by
  have h : SF (fun z : α → ℕ => ∀ v, z (f v)=tuple c v) :=
    SF.all (fun v => (SF.eq (Poly.proj (f v)) (Poly.const (tuple c v))).congr (by intro z; change (z (f v):ℤ)=(tuple c v:ℤ) ↔ _; exact_mod_cast Iff.rfl))
  refine h.congr ?_
  intro z
  constructor
  · intro hh; have he : z ∘ f=tuple c := funext hh; rw [he,from_tuple]
  · intro hh v; simpa only [tuple_from,Function.comp_apply] using congrFun (congrArg tuple hh) v


-- @@ L348-348 verbatim
def tripleMap (f g h : Var → α) (v : Fin 3×Var) : α := ![f v.2,g v.2,h v.2] v.1

-- @@ L349-365 verbatim
lemma add_general_sf (f g h : Var → α) : SF (fun z =>
    (fromTuple (z ∘ f)).Valid ∧ (fromTuple (z ∘ g)).Valid ∧ (fromTuple (z ∘ h)).Valid ∧
    AddEq (fromTuple (z ∘ f)) (fromTuple (z ∘ g)) (fromTuple (z ∘ h))) := by
  refine ((addEq_semi (ι:=Fin 3) 0 1 2).1.reindex (tripleMap f g h)).congr ?_
  intro z
  have hh : AllValid (z ∘ tripleMap f g h) ↔
      (fromTuple (z ∘ f)).Valid ∧ (fromTuple (z ∘ g)).Valid ∧ (fromTuple (z ∘ h)).Valid := by
    constructor
    · intro hh; exact ⟨hh 0,hh 1,hh 2⟩
    · rintro ⟨h₀,h₁,h₂⟩ i
      fin_cases i
      exact h₀
      exact h₁
      exact h₂
  change (AllValid (z ∘ tripleMap f g h) ∧ _) ↔ _
  rw [hh]
  tauto


-- @@ L367-397 verbatim
lemma mulRel_sf (n : ℕ) : ∀ {α : Type} (f g : Var → α),
    SF (fun z => MulRel n (fromTuple (z ∘ f)) (fromTuple (z ∘ g))) := by
  induction n with
  | zero =>
    intro α f g
    exact ((valid_sf f).and (const_sf g (encode 0))).congr (fun _ => (mulRel_zero _ _).symm)
  | succ n ih =>
    intro α f g
    let f' : Var → α⊕Var := Sum.inl ∘ f
    let g' : Var → α⊕Var := Sum.inl ∘ g
    have h := (ih f' Sum.inr).and (add_general_sf Sum.inr f' g')
    have hu : ∀ x y y',
        (MulRel n (fromTuple (Sum.elim x y ∘ f')) (fromTuple (Sum.elim x y ∘ Sum.inr)) ∧
          (fromTuple (Sum.elim x y ∘ Sum.inr)).Valid ∧ (fromTuple (Sum.elim x y ∘ f')).Valid ∧
          (fromTuple (Sum.elim x y ∘ g')).Valid ∧ AddEq (fromTuple (Sum.elim x y ∘ Sum.inr))
            (fromTuple (Sum.elim x y ∘ f')) (fromTuple (Sum.elim x y ∘ g'))) →
        (MulRel n (fromTuple (Sum.elim x y' ∘ f')) (fromTuple (Sum.elim x y' ∘ Sum.inr)) ∧
          (fromTuple (Sum.elim x y' ∘ Sum.inr)).Valid ∧ (fromTuple (Sum.elim x y' ∘ f')).Valid ∧
          (fromTuple (Sum.elim x y' ∘ g')).Valid ∧ AddEq (fromTuple (Sum.elim x y' ∘ Sum.inr))
            (fromTuple (Sum.elim x y' ∘ f')) (fromTuple (Sum.elim x y' ∘ g'))) → y=y' := by
      intro x y y' hy hy'
      exact fromTuple_injective (mulRel_unique hy.1 hy'.1)
    refine (h.ex hu).congr ?_
    intro z
    change (∃ y : Var → ℕ, MulRel n (fromTuple (z ∘ f)) (fromTuple y) ∧
      (fromTuple y).Valid ∧ (fromTuple (z ∘ f)).Valid ∧ (fromTuple (z ∘ g)).Valid ∧
      AddEq (fromTuple y) (fromTuple (z ∘ f)) (fromTuple (z ∘ g))) ↔ _
    rw [mulRel_succ]
    constructor
    · rintro ⟨y,hy⟩; exact ⟨fromTuple y,hy⟩
    · rintro ⟨c,hc⟩; exact ⟨tuple c,by simpa only [from_tuple] using hc⟩

-- @@ L398-398 verbatim
end SingleFold.PointCompiler


-- @@ L400-400 verbatim
namespace SingleFold.Compiler.Semi

-- @@ L401-401 verbatim
variable {α : Type}

-- @@ L402-408 verbatim
theorem max_eq (p q r : Poly α) : Semi (fun z => max (p z) (q z)=r z) := by
  refine (((Semi.le p q).and (Semi.eq q r)).or ((Semi.lt q p).and (Semi.eq p r))).congr ?_
  intro z
  by_cases h : p z≤q z
  · simp only [h,max_eq_right h,true_and,not_lt_of_ge h,false_and,or_false]
  · have h' := lt_of_not_ge h
    simp only [h,max_eq_left h'.le,false_and,h',true_and,false_or]

-- @@ L409-409 verbatim
end SingleFold.Compiler.Semi


-- @@ L411-411 verbatim
namespace SingleFold.PointCompiler

-- @@ L412-412 verbatim
open Compiler RationalCompiler

-- @@ L413-413 verbatim
open WeierstrassCurve.Affine.Point


-- @@ L415-415 verbatim
def Code.height (a : Code) : ℕ := max (a.x.p+a.x.n) a.x.d

-- @@ L416-417 verbatim
lemma height_pos {a : Code} (ha : a.Valid) : 0<a.height :=
  lt_of_lt_of_le (RationalCode.den_pos ha.1) (le_max_right _ _)

-- @@ L418-426 verbatim
lemma height_semi {α : Type} (f : Var → α) (v : α) :
    Semi (fun z => (fromTuple (z ∘ f)).height=z v) := by
  let p : Poly α := Poly.proj (f (.inr (0,0)))+Poly.proj (f (.inr (0,1)))
  let q : Poly α := Poly.proj (f (.inr (0,2)))
  refine (Semi.max_eq p q (Poly.proj v)).congr ?_
  intro z
  change max ((z (f (.inr (0,0))):ℤ)+z (f (.inr (0,1)))) (z (f (.inr (0,2))):ℤ)=(z v:ℤ) ↔ _
  dsimp only [Code.height,fromTuple,RationalCompiler.code,Function.comp_apply]
  exact_mod_cast Iff.rfl


-- @@ L428-428 verbatim
def WRel (m : ℕ) (a : Code) (v : ℕ) : Prop := ∃ b, MulRel m a b ∧ b.height=v

-- @@ L429-433 verbatim
lemma wRel_semantics (m : ℕ) (a : Code) (v : ℕ) :
    WRel m a v ↔ ∃ P, a=encode P ∧ (encode (m • P)).height=v := by
  constructor
  · rintro ⟨b,⟨P,ha,rfl⟩,hv⟩; exact ⟨P,ha,hv⟩
  · rintro ⟨P,rfl,hv⟩; exact ⟨encode (m • P),⟨P,rfl,rfl⟩,hv⟩

-- @@ L434-437 verbatim
lemma wRel_unique {m a v w} (hv : WRel m a v) (hw : WRel m a w) : v=w := by
  obtain ⟨b,hb,rfl⟩ := hv
  obtain ⟨c,hc,rfl⟩ := hw
  rw [mulRel_unique hb hc]

-- @@ L438-440 verbatim
lemma wRel_exists (m : ℕ) (a : Code) (ha : a.Valid) : ∃! v, WRel m a v := by
  obtain ⟨b,hb,_⟩ := mulRel_exists m a ha
  exact ⟨b.height,⟨b,hb,rfl⟩,fun w hw => wRel_unique hw ⟨b,hb,rfl⟩⟩

-- @@ L441-450 verbatim
lemma wRel_sf {α : Type} (m : ℕ) (f : Var → α) (v : α) :
    SF (fun z => WRel m (fromTuple (z ∘ f)) (z v)) := by
  let f' : Var → α⊕Var := Sum.inl ∘ f
  have h := (mulRel_sf m f' Sum.inr).and (height_semi Sum.inr (Sum.inl v)).1
  refine (h.ex (fun z x y hx hy => fromTuple_injective (mulRel_unique hx.1 hy.1))).congr ?_
  intro z
  change (∃ b : Var → ℕ, MulRel m (fromTuple (z ∘ f)) (fromTuple b) ∧ (fromTuple b).height=z v) ↔ _
  constructor
  · rintro ⟨b,hb⟩; exact ⟨fromTuple b,hb⟩
  · rintro ⟨b,hb⟩; exact ⟨tuple b,by simpa only [from_tuple] using hb⟩


-- @@ L452-460 verbatim
lemma rational_height (r : ℚ) :
    max ((RationalCode.encode r).p+(RationalCode.encode r).n) (RationalCode.encode r).d=
      max r.num.natAbs r.den := by
  have hv := RationalCode.encode_valid r
  have hc := RationalCode.canonical hv
  have hp := RationalCode.positive_num hv
  have hn := RationalCode.negative_num hv
  rw [RationalCode.encode_value] at hc hp hn
  rw [←hp,←hn,hc.2,Int.toNat_add_toNat_neg_eq_natAbs]

-- @@ L461-461 verbatim
end SingleFold.PointCompiler


-- @@ L463-463 verbatim
end OAI
