import OAI.Computability.RationalHitting.LiftComputation


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace RationalHitting.StackLanguage

-- @@ L6-6 verbatim
open Function

-- @@ L7-7 verbatim
variable {A : Type} [Coding A]

 
-- @@ L9-10 verbatim
def flattenStep (a : List (List A)×List A) : List (List A)×List A :=
  (a.1.tail,a.2++a.1.headD [])

 
-- @@ L12-23 verbatim
lemma flattenStep_code_le (a : List (List A)×List A) :
    (code (flattenStep a)).length≤(code a).length := by
  rcases a with ⟨l,r⟩
  cases l with
  | nil => simp [flattenStep]
  | cons x l =>
    simp only [flattenStep,List.tail_cons,List.headD_cons,prod_code_length]
    change 2*(listCode code l).length+1+(listCode code (r++x)).length≤
      2*(listCode code (x::l)).length+1+(listCode code r).length
    simp only [listCode_cons,listCode_append,List.length_append,codeWord_length]
    change _≤2*(2*(listCode code x).length+1+(listCode code l).length)+1+(listCode code r).length
    omega

 
-- @@ L25-29 verbatim
lemma flattenStep_iterate_code (a : List (List A)×List A) (k : ℕ) :
    (code (flattenStep^[k] a)).length≤(code a).length := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply'];exact (flattenStep_code_le _).trans ih

 
-- @@ L31-37 verbatim
lemma flattenStep_iterate {A : Type} [Coding A] (l : List (List A)) (r : List A) :
    flattenStep^[l.length] (l,r)=([],r++l.flatten) := by
  induction l generalizing r with
  | nil => simp
  | cons x l ih =>
    rw [List.length_cons,iterate_succ_apply]
    simp [flattenStep,ih,List.append_assoc]


-- @@ L39-39 verbatim
namespace Poly

-- @@ L40-51 verbatim
@[fun_prop] theorem listFlatten : Poly (List.flatten : List (List A) → List A) := by
  have hs : Poly (flattenStep (A:=A)) := by
    unfold flattenStep
    fun_prop
  have ht := hs.iterate TimeBound.variable (by
    intro n a i hi
    have hh := flattenStep_iterate_code a i
    simp only [TimeBound.eval_variable,pairCode_length,unaryCode_length]
    omega)
  have ho := (show Poly (Prod.snd : List (List A)×List A → List A) from snd).comp
    (ht.comp (show Poly (fun a : List (List A) => (Unary.mk a.length,(a,([] : List A)))) by fun_prop))
  exact ho.of_eq (by intro a;simp [flattenStep_iterate])


-- @@ L53-56 verbatim
theorem listFlatMap {B C : Type} [Coding B] [Coding C] [Inhabited B]
    {f : C×B → List A} (hf : Poly f) :
    Poly (fun a : C×List B => a.2.flatMap (fun b => f (a.1,b))) := by
  exact (listFlatten.comp hf.listMap).of_eq (by intro a;rw [List.flatMap_def])

-- @@ L57-57 verbatim
end Poly

-- @@ L58-58 verbatim
end RationalHitting.StackLanguage



-- @@ L61-61 verbatim
namespace RationalHitting.StackLanguage

-- @@ L62-62 verbatim
open Function


-- @@ L64-64 verbatim
instance : Inhabited BitWord := ⟨⟨[]⟩⟩


-- @@ L66-67 verbatim
def concatStep (a : List BitWord×BitWord) : List BitWord×BitWord :=
  (a.1.tail,⟨a.2.val++(a.1.headD ⟨[]⟩).val⟩)


-- @@ L69-80 verbatim
lemma concatStep_code_le (a : List BitWord×BitWord) :
    (code (concatStep a)).length≤(code a).length := by
  rcases a with ⟨l,⟨r⟩⟩
  cases l with
  | nil => simp [concatStep]
  | cons x l =>
    simp only [concatStep,List.tail_cons,List.headD_cons,prod_code_length]
    change 2*(listCode code l).length+1+(r++x.val).length≤
      2*(listCode code (x::l)).length+1+r.length
    simp only [listCode_cons,List.length_append,codeWord_length]
    change _≤2*(2*x.val.length+1+(listCode code l).length)+1+r.length
    omega


-- @@ L82-86 verbatim
lemma concatStep_iterate_code (a : List BitWord×BitWord) (k : ℕ) :
    (code (concatStep^[k] a)).length≤(code a).length := by
  induction k with
  | zero => rfl
  | succ k ih => rw [iterate_succ_apply'];exact (concatStep_code_le _).trans ih


-- @@ L88-94 verbatim
lemma concatStep_iterate (l : List BitWord) (r : List Bool) :
    concatStep^[l.length] (l,⟨r⟩)=([],⟨r++l.flatMap BitWord.val⟩) := by
  induction l generalizing r with
  | nil => simp
  | cons x l ih =>
    rw [List.length_cons,iterate_succ_apply]
    simp [concatStep,ih,List.append_assoc]


-- @@ L96-96 verbatim
namespace Procedure


-- @@ L98-115 verbatim
def encodeWord : Procedure _root_.id _root_.id StackLanguage.encodedWord where
  Registers := Fin 4
  finite := inferInstance
  decEq := inferInstance
  input := 0
  output := 1
  program := StackLanguage.encodeWord
  bound := 15*TimeBound.variable
  correct a := by
    refine ⟨11*a.length+7,by simp;omega,?_⟩
    have hh := eval_encodeWord (single (0:Fin 4) a) (by simp [single]) (by simp [single])
    have hout : update (update (single (0:Fin 4) a) 0 []) 1
        (encodedWord ((single (0:Fin 4) a) 0)++(single (0:Fin 4) a) 1)=
        single 1 (encodedWord a) := by
      funext j;fin_cases j <;> simp [single]
    rw [hout] at hh
    simpa [single] using hh
  size a := by simp [encodedWord];omega

-- @@ L116-116 verbatim
end Procedure


-- @@ L118-118 verbatim
namespace Poly

-- @@ L119-130 verbatim
@[fun_prop] theorem wordConcat : Poly (fun l : List BitWord => BitWord.mk (l.flatMap BitWord.val)) := by
  have hs : Poly concatStep := by
    have hh : Poly (fun a : List BitWord×BitWord => (a.2,a.1.headD ⟨[]⟩)) := by fun_prop
    exact (listTail.comp fst).pair (wordAppend.comp hh)
  have ht := hs.iterate TimeBound.variable (by
    intro n a i hi
    have hh := concatStep_iterate_code a i
    simp only [TimeBound.eval_variable,pairCode_length,unaryCode_length]
    omega)
  have ho := (show Poly (Prod.snd : List BitWord×BitWord → BitWord) from snd).comp
    (ht.comp (show Poly (fun a : List BitWord => (Unary.mk a.length,(a,(⟨[]⟩ : BitWord)))) by fun_prop))
  exact ho.of_eq (by intro a;simp [concatStep_iterate])


-- @@ L132-134 verbatim
@[fun_prop] theorem encodeNat : Poly (fun a : ℕ => BitWord.mk (RationalHitting.encodeNat a)) := by
  exact (show Feasible _root_.id _root_.id StackLanguage.encodedWord from ⟨Procedure.encodeWord⟩).recode
    _ _ _ Nat.bits (by intro a;rfl) (by intro a;exact encodedWord_bits a)


-- @@ L136-137 verbatim
@[fun_prop] theorem encodeUnary : Poly (fun a : Unary => BitWord.mk (RationalHitting.encodeNat a.val)) :=
  encodeNat.comp unaryToNat

-- @@ L138-138 verbatim
end Poly

-- @@ L139-139 verbatim
end RationalHitting.StackLanguage



-- @@ L142-142 verbatim
namespace RationalHitting.StackLanguage

-- @@ L143-143 verbatim
namespace Runtime


-- @@ L145-145 verbatim
abbrev GridPoint := Unary×Unary×Unary


-- @@ L147-147 verbatim
def gridFn (x : GridPoint) : Fin 3 → ℕ := ![x.1.val,x.2.1.val,x.2.2.val]


-- @@ L149-150 verbatim
def matrix (p : Params) (x : GridPoint) (a : Unary) : DenseSquare :=
  ⟨p.m*p.q,fun i j => entry p.m p.N p.q a.val x.1.val x.2.1.val x.2.2.val i.val j.val⟩


-- @@ L152-157 verbatim
@[fun_prop] theorem matrix_poly : Poly (fun a : Params×GridPoint×Unary => matrix a.1 a.2.1 a.2.2) := by
  have hn : Poly (fun a : Params×GridPoint×Unary => a.1.2.2.1*a.1.2.2.2.1) := by fun_prop
  have he : Poly (fun a : (Params×GridPoint×Unary)×(Unary×Unary) =>
      ((a.1.1.2.2.1,a.1.1.2.1,a.1.1.2.2.2.1),
      (a.1.2.2.toInt,a.1.2.1.1.toInt,a.1.2.1.2.1.toInt,a.1.2.1.2.2.toInt),a.2)) := by fun_prop
  exact Poly.denseBuild hn (entry_poly.comp he)


-- @@ L159-164 verbatim
lemma matrix_eq (n s : ℕ) (x : GridPoint) (a : Fin (n+1)) :
    matrix (Params.of n s) x ⟨a.val⟩ = DenseSquare.of
      (Generator.U n (Parameters.N n s) (Parameters.exponent n s) (gridFn x) a) := by
  apply congrArg (fun A => (⟨Generator.D (Parameters.exponent n s),A⟩ : DenseSquare))
  funext i j
  exact entry_eq n _ _ (gridFn x) a i j


-- @@ L166-167 verbatim
def cramer (A B : DenseSquare) (i j : ℕ) : DenseSquare :=
  ⟨A.dim,fun r c => if c.val=i then B.get r.val j else A.val r c⟩


-- @@ L169-185 verbatim
@[fun_prop] theorem cramer_poly : Poly (fun a : (DenseSquare×DenseSquare)×(Unary×Unary) =>
    cramer a.1.1 a.1.2 a.2.1.val a.2.2.val) := by
  have hn : Poly (fun a : (DenseSquare×DenseSquare)×(Unary×Unary) => Unary.mk a.1.1.dim) :=
    Poly.denseDim.comp (by fun_prop)
  have hc : Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×(Unary×Unary) =>
    Unary.eqb a.2.2 a.1.2.1) := by fun_prop
  have hv : Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×(Unary×Unary) =>
    a.1.1.2.get a.2.1.val a.1.2.2.val) := Poly.denseGet.comp (show Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×(Unary×Unary) =>
      (a.1.1.2,(a.2.1,a.1.2.2))) by fun_prop)
  have hw : Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×(Unary×Unary) =>
    a.1.1.1.get a.2.1.val a.2.2.val) := Poly.denseGet.comp (show Poly (fun a : ((DenseSquare×DenseSquare)×(Unary×Unary))×(Unary×Unary) =>
      (a.1.1.1,(a.2.1,a.2.2))) by fun_prop)
  exact (Poly.denseBuild hn (hc.cond hv hw)).of_eq (by
    intro a
    apply congrArg (fun A => (⟨a.1.1.dim,A⟩ : DenseSquare))
    funext i j
    simp [Unary.eqb])


-- @@ L187-193 verbatim
lemma cramer_of {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) (i j : Fin d) :
    cramer (DenseSquare.of A) (DenseSquare.of B) i.val j.val=
      DenseSquare.of (A.updateCol i (fun r => B r j)) := by
  unfold cramer DenseSquare.of
  congr 1
  funext r c
  simp [DenseSquare.get,Matrix.updateCol_apply,Fin.ext_iff]


-- @@ L195-195 verbatim
end Runtime

-- @@ L196-196 verbatim
end RationalHitting.StackLanguage



-- @@ L199-199 verbatim
namespace RationalHitting.StackLanguage.Runtime


-- @@ L201-207 verbatim
lemma cramer_det_of {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) (i j : Fin d) :
    (cramer (DenseSquare.of A) (DenseSquare.of B) i.val j.val).val.det=
      (A.updateCol i (fun r => B r j)).det := by
  unfold cramer DenseSquare.of
  apply congrArg Matrix.det
  funext r c
  simp [DenseSquare.get,Matrix.updateCol_apply,Fin.ext_iff]


-- @@ L209-212 verbatim
lemma cramer_encode_of {d : ℕ} (A B : Matrix (Fin d) (Fin d) ℤ) (den : ℤ) (i j : Fin d) :
    encodeRat (Rat.divInt (cramer (DenseSquare.of A) (DenseSquare.of B) i.val j.val).val.det den)=
      encodeRat (Rat.divInt (A.updateCol i (fun r => B r j)).det den) :=
  congrArg (fun z => encodeRat (Rat.divInt z den)) (cramer_det_of A B i j)


-- @@ L214-214 verbatim
end RationalHitting.StackLanguage.Runtime


-- @@ L216-216 verbatim
end OAI
