/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.Epr.Expansion
import DescriptiveComplexity.PSpaceHierarchy
import DescriptiveComplexity.Exponential.Classes


-- @@ L11-34 verbatim
/-!
# EPR is in NEXPTIME

The membership half. Read over the expansion whose points are the *relations*
on the instance (`DescriptiveComplexity.Epr.eprExp`), the whole of EPR is one
`Σ₁` sentence:

> guess a relation `I` between the symbols and the assignments; check that it is
> local, that the instance is well-formed, and that some assignment of the
> existential variables makes every clause true at *every* assignment of the
> universal variables.

Both quantifiers over assignments are first-order there, an assignment being a
point, so the sentence has one second-order block and NEXPTIME is `NP.exp`.

## The two layers

The kernel is written once as formulas over an arbitrary index of free
variables, and read back in two steps: a *semantic* reading at arbitrary points
(`DescriptiveComplexity.Epr.MemPt` and its siblings), and then a computation of
those predicates at the three kinds of point, which is where
`DescriptiveComplexity.Epr.realize_memP` and the rest of the expansion's API is
used. Splitting the two keeps the formula layer free of case analysis.
-/


-- @@ L36-36 verbatim
namespace DescriptiveComplexity


-- @@ L38-38 verbatim
open FirstOrder


-- @@ L40-40 verbatim
open Language Structure


-- @@ L42-42 verbatim
namespace Epr


-- @@ L44-44 verbatim
/-! ### The guess and its vocabulary -/


-- @@ L46-46 verbatim
section Vocabulary


-- @@ L48-53 verbatim
/-- **The block the `Σ₁` definition guesses**: one binary relation variable,
read as “the symbol `s` holds of the assignment `w`”. -/
@[reducible]
def ivBlock : SOBlock where
  ι := Unit
  arity := fun _ => 2


-- @@ L55-56 verbatim
/-- The vocabulary of the kernel: the points, together with the guess. -/
abbrev eprSOLang : Language := Language.eprPt.sum ivBlock.lang


-- @@ L58-59 verbatim
/-- A unary symbol of the points, in the kernel's vocabulary. -/
abbrev ptS₁ (r : Language.eprPt.Relations 1) : eprSOLang.Relations 1 := Sum.inl r


-- @@ L61-62 verbatim
/-- A binary symbol of the points, in the kernel's vocabulary. -/
abbrev ptS₂ (r : Language.eprPt.Relations 2) : eprSOLang.Relations 2 := Sum.inl r


-- @@ L64-65 verbatim
/-- The guessed symbol. -/
abbrev ivS : eprSOLang.Relations 2 := Sum.inr ⟨(), rfl⟩


-- @@ L67-67 verbatim
end Vocabulary


-- @@ L69-69 verbatim
/-! ### The atoms -/


-- @@ L71-71 verbatim
section Atoms


-- @@ L73-73 verbatim
variable {γ : Type}


-- @@ L75-77 expanded
/-- A unary symbol of the points, as a formula. -/
noncomputable def ptF₁ (r : Language.eprPt.Relations 1) (x : γ) : eprSOLang.Formula γ :=
  FirstOrder.Language.Relations.formula₁ (ptS₁ r) (FirstOrder.Language.Term.var x)


-- @@ L79-81 expanded
/-- A binary symbol of the points, as a formula. -/
noncomputable def ptF₂ (r : Language.eprPt.Relations 2) (x y : γ) : eprSOLang.Formula γ :=
  FirstOrder.Language.Relations.formula₂ (ptS₂ r) (FirstOrder.Language.Term.var x)
    (FirstOrder.Language.Term.var y)


-- @@ L83-84 expanded
/-- The guessed symbol, as a formula. -/
noncomputable def ivF (s w : γ) : eprSOLang.Formula γ :=
  FirstOrder.Language.Relations.formula₂ ivS (FirstOrder.Language.Term.var s)
    (FirstOrder.Language.Term.var w)


-- @@ L86-87 expanded
/-- Equality of two points. -/
noncomputable def ptEqF (x y : γ) : eprSOLang.Formula γ :=
  FirstOrder.Language.Term.equal (FirstOrder.Language.Term.var x) (FirstOrder.Language.Term.var y)


-- @@ L89-89 verbatim
variable {A : Type} [Language.epr.Structure A] [LinearOrder A]


-- @@ L91-95 verbatim
/-- The structure the kernel is read in: the points, with the guess. -/
@[instance_reducible]
noncomputable def eprSOStructure (ρ : ivBlock.Assignment (eprExp.Map A)) :
    eprSOLang.Structure (eprExp.Map A) :=
  @sumStructure _ _ _ (eprPtStructure A) (ivBlock.structure ρ)


-- @@ L97-97 verbatim
variable (ρ : ivBlock.Assignment (eprExp.Map A)) {v : γ → eprExp.Map A}


-- @@ L99-109 verbatim
@[simp]
theorem realize_ptF₁ (r : Language.eprPt.Relations 1) (x : γ) :
    (@Formula.Realize eprSOLang (eprExp.Map A)
        (eprSOStructure ρ) _ (ptF₁ r x) v ↔
      letI := eprPtStructure A
      RelMap r ![v x]) := by
  let := eprPtStructure A
  let := ivBlock.structure ρ
  let := eprSOStructure ρ
  rw [ptF₁, Formula.realize_rel₁, Language.relMap_sumInl]
  simp only [Term.realize_var]


-- @@ L111-121 verbatim
@[simp]
theorem realize_ptF₂ (r : Language.eprPt.Relations 2) (x y : γ) :
    (@Formula.Realize eprSOLang (eprExp.Map A)
        (eprSOStructure ρ) _ (ptF₂ r x y) v ↔
      letI := eprPtStructure A
      RelMap r ![v x, v y]) := by
  let := eprPtStructure A
  let := ivBlock.structure ρ
  let := eprSOStructure ρ
  rw [ptF₂, Formula.realize_rel₂, Language.relMap_sumInl]
  simp only [Term.realize_var]


-- @@ L123-133 verbatim
@[simp]
theorem realize_ivF (s w : γ) :
    (@Formula.Realize eprSOLang (eprExp.Map A)
        (eprSOStructure ρ) _ (ivF s w) v ↔
      ρ () ![v s, v w]) := by
  let := eprPtStructure A
  let := ivBlock.structure ρ
  let := eprSOStructure ρ
  rw [ivF, Formula.realize_rel₂]
  simp only [Term.realize_var]
  rfl


-- @@ L135-143 verbatim
@[simp]
theorem realize_ptEqF (x y : γ) :
    (@Formula.Realize eprSOLang (eprExp.Map A)
        (eprSOStructure ρ) _ (ptEqF x y) v ↔
      v x = v y) := by
  let := eprPtStructure A
  let := ivBlock.structure ρ
  let := eprSOStructure ρ
  rw [ptEqF, Formula.realize_equal, Term.realize_var, Term.realize_var]


-- @@ L145-145 verbatim
end Atoms


-- @@ L147-147 verbatim
/-! ### The semantic reading, at arbitrary points -/


-- @@ L149-149 verbatim
section Semantic


-- @@ L151-151 verbatim
variable {A : Type} [Language.epr.Structure A] [LinearOrder A]


-- @@ L153-156 verbatim
/-- The point is an element of the instance. -/
def IsEltPt (p : eprExp.Map A) : Prop :=
  letI := eprPtStructure A
  RelMap Language.peIsEltSym ![p]


-- @@ L158-161 verbatim
/-- The point is an ordered pair. -/
def IsPairPt (p : eprExp.Map A) : Prop :=
  letI := eprPtStructure A
  RelMap Language.peIsPairSym ![p]


-- @@ L163-166 verbatim
/-- The point is an assignment. -/
def IsAsgPt (p : eprExp.Map A) : Prop :=
  letI := eprPtStructure A
  RelMap Language.peIsAsgSym ![p]


-- @@ L168-171 verbatim
/-- The point `q` is the pair of `x` and `y`. -/
def PairOfPt (q x y : eprExp.Map A) : Prop :=
  letI := eprPtStructure A
  IsPairPt q ∧ RelMap Language.peFstSym ![q, x] ∧ RelMap Language.peSndSym ![q, y]


-- @@ L173-176 verbatim
/-- The assignment `w` sends `x` to `y`. -/
def MemPt (w x y : eprExp.Map A) : Prop :=
  letI := eprPtStructure A
  ∃ q, PairOfPt q x y ∧ RelMap Language.peMemSym ![w, q]


-- @@ L178-181 verbatim
/-- The literal `l` names the variable `x` at the position `p`. -/
def ArgPt (l p x : eprExp.Map A) : Prop :=
  letI := eprPtStructure A
  ∃ q, PairOfPt q l p ∧ RelMap Language.peArgSym ![q, x]


-- @@ L183-186 verbatim
/-- The element is an existential variable. -/
def EVarPt (x : eprExp.Map A) : Prop :=
  letI := eprPtStructure A
  RelMap Language.peEVarSym ![x]


-- @@ L188-191 verbatim
/-- The element is a clause. -/
def ClPt (c : eprExp.Map A) : Prop :=
  letI := eprPtStructure A
  RelMap Language.peClSym ![c]


-- @@ L193-196 verbatim
/-- The literal occurs in the clause. -/
def InClPt (c l : eprExp.Map A) : Prop :=
  letI := eprPtStructure A
  RelMap Language.peInClSym ![c, l]


-- @@ L198-201 verbatim
/-- The literal is the positive atom of the symbol. -/
def PosPt (l s : eprExp.Map A) : Prop :=
  letI := eprPtStructure A
  RelMap Language.pePosSym ![l, s]


-- @@ L203-206 verbatim
/-- The literal is the negated atom of the symbol. -/
def NegPt (l s : eprExp.Map A) : Prop :=
  letI := eprPtStructure A
  RelMap Language.peNegSym ![l, s]


-- @@ L208-211 verbatim
/-- The symbol has the argument position. -/
def SigPt (s p : eprExp.Map A) : Prop :=
  letI := eprPtStructure A
  RelMap Language.peSigSym ![s, p]


-- @@ L213-216 verbatim
/-- The assignment `w` of the argument positions matches the environment on the
arguments the literal declares. -/
def MatchPt (l vv w : eprExp.Map A) : Prop :=
  ∀ p x y, IsEltPt p → IsEltPt x → IsEltPt y → ArgPt l p x → MemPt vv x y → MemPt w p y


-- @@ L218-221 verbatim
/-- The environment `w` is the one two assignments make. -/
def CombPt (e u w : eprExp.Map A) : Prop :=
  ∀ x y, IsEltPt x → IsEltPt y →
    (MemPt w x y ↔ ((EVarPt x ∧ MemPt e x y) ∨ (¬EVarPt x ∧ MemPt u x y)))


-- @@ L223-224 verbatim
/-- Every element is sent somewhere by the assignment. -/
def TotalPt (w : eprExp.Map A) : Prop := ∀ x, IsEltPt x → ∃ y, IsEltPt y ∧ MemPt w x y


-- @@ L226-228 verbatim
/-- And to one place only. -/
def FuncPt (w : eprExp.Map A) : Prop :=
  ∀ x y z, IsEltPt x → IsEltPt y → IsEltPt z → MemPt w x y → MemPt w x z → y = z


-- @@ L230-233 verbatim
/-- The literal `l` is true at the environment `vv`, under the guess `ρ`. -/
def LitTruePt (ρ : ivBlock.Assignment (eprExp.Map A)) (l vv : eprExp.Map A) : Prop :=
  ∃ s w, (IsEltPt s ∧ IsAsgPt w ∧ TotalPt w ∧ FuncPt w ∧ MatchPt l vv w) ∧
    ((PosPt l s ∧ ρ () ![s, w]) ∨ (NegPt l s ∧ ¬ρ () ![s, w]))


-- @@ L235-240 verbatim
/-- The guess is local: the value of a symbol is decided by the arguments its
signature declares. -/
def LocalPt (ρ : ivBlock.Assignment (eprExp.Map A)) : Prop :=
  ∀ s w w', IsEltPt s → IsAsgPt w → IsAsgPt w' →
    (∀ p y, IsEltPt p → IsEltPt y → SigPt s p → (MemPt w p y ↔ MemPt w' p y)) →
    (ρ () ![s, w] ↔ ρ () ![s, w'])


-- @@ L242-247 verbatim
/-- The instance is well-formed, read at the points. -/
def WFPt (A : Type) [Language.epr.Structure A] [LinearOrder A] : Prop :=
  (∀ l p x y : eprExp.Map A, IsEltPt l → IsEltPt p → IsEltPt x → IsEltPt y →
      ArgPt l p x → ArgPt l p y → x = y) ∧
    ∀ l s p : eprExp.Map A, IsEltPt l → IsEltPt s → IsEltPt p →
      (PosPt l s ∨ NegPt l s) → SigPt s p → ∃ x, IsEltPt x ∧ ArgPt l p x


-- @@ L249-253 verbatim
theorem exists_eltPt {p : eprExp.Map A} (h : IsEltPt p) : ∃ x, p = eltPt x := by
  rcases cases_point p with ⟨x, rfl⟩ | ⟨x, y, rfl⟩ | ⟨R, rfl⟩
  · exact ⟨x, rfl⟩
  · exact absurd ((realize_isElt _).mp h) (by simp)
  · exact absurd ((realize_isElt _).mp h) (by simp)


-- @@ L255-259 verbatim
theorem exists_pairPt {p : eprExp.Map A} (h : IsPairPt p) : ∃ x y, p = pairPt x y := by
  rcases cases_point p with ⟨x, rfl⟩ | ⟨x, y, rfl⟩ | ⟨R, rfl⟩
  · exact absurd ((realize_isPair _).mp h) (by simp)
  · exact ⟨x, y, rfl⟩
  · exact absurd ((realize_isPair _).mp h) (by simp)


-- @@ L261-265 verbatim
theorem exists_asgPt {p : eprExp.Map A} (h : IsAsgPt p) : ∃ R, p = asgPt R := by
  rcases cases_point p with ⟨x, rfl⟩ | ⟨x, y, rfl⟩ | ⟨R, rfl⟩
  · exact absurd ((realize_isAsg _).mp h) (by simp)
  · exact absurd ((realize_isAsg _).mp h) (by simp)
  · exact ⟨R, rfl⟩


-- @@ L267-268 verbatim
@[simp]
theorem isEltPt_eltPt (x : A) : IsEltPt (eltPt x) := (realize_isElt _).mpr rfl


-- @@ L270-271 verbatim
@[simp]
theorem isPairPt_pairPt (x y : A) : IsPairPt (pairPt x y) := (realize_isPair _).mpr rfl


-- @@ L273-274 verbatim
@[simp]
theorem isAsgPt_asgPt (R : A → A → Prop) : IsAsgPt (asgPt R) := (realize_isAsg _).mpr rfl


-- @@ L276-281 verbatim
@[simp]
theorem pairOfPt_iff (x y a b : A) :
    PairOfPt (pairPt x y) (eltPt a) (eltPt b) ↔ (a = x ∧ b = y) := by
  refine ⟨fun h => ⟨(realize_fstP x y a).mp h.2.1, (realize_sndP x y b).mp h.2.2⟩,
    fun ⟨ha, hb⟩ => ⟨isPairPt_pairPt x y, (realize_fstP x y a).mpr ha,
      (realize_sndP x y b).mpr hb⟩⟩


-- @@ L283-292 verbatim
@[simp]
theorem memPt_iff (R : A → A → Prop) (x y : A) :
    MemPt (asgPt R) (eltPt x) (eltPt y) ↔ R x y := by
  constructor
  · rintro ⟨q, hq, hm⟩
    obtain ⟨a, b, rfl⟩ := exists_pairPt hq.1
    obtain ⟨rfl, rfl⟩ := (pairOfPt_iff a b x y).mp hq
    exact (realize_memP R _ _).mp hm
  · intro h
    exact ⟨pairPt x y, (pairOfPt_iff x y x y).mpr ⟨rfl, rfl⟩, (realize_memP R x y).mpr h⟩


-- @@ L294-295 verbatim
@[simp]
theorem eVarPt_iff (x : A) : EVarPt (eltPt x) ↔ EVarG x := realize_evarE x


-- @@ L297-298 verbatim
@[simp]
theorem clPt_iff (c : A) : ClPt (eltPt c) ↔ ClauseG c := realize_clE c


-- @@ L300-301 verbatim
@[simp]
theorem inClPt_iff (c l : A) : InClPt (eltPt c) (eltPt l) ↔ InClG c l := realize_inClE c l


-- @@ L303-304 verbatim
@[simp]
theorem posPt_iff (l s : A) : PosPt (eltPt l) (eltPt s) ↔ PosG l s := realize_posLE l s


-- @@ L306-307 verbatim
@[simp]
theorem negPt_iff (l s : A) : NegPt (eltPt l) (eltPt s) ↔ NegG l s := realize_negLE l s


-- @@ L309-310 verbatim
@[simp]
theorem sigPt_iff (s p : A) : SigPt (eltPt s) (eltPt p) ↔ SigG s p := realize_sigE s p


-- @@ L312-321 verbatim
@[simp]
theorem argPt_iff (l p x : A) :
    ArgPt (eltPt l) (eltPt p) (eltPt x) ↔ ArgG l p x := by
  constructor
  · rintro ⟨q, hq, ha⟩
    obtain ⟨a, b, rfl⟩ := exists_pairPt hq.1
    obtain ⟨rfl, rfl⟩ := (pairOfPt_iff a b l p).mp hq
    exact (realize_argP _ _ x).mp ha
  · intro h
    exact ⟨pairPt l p, (pairOfPt_iff l p l p).mpr ⟨rfl, rfl⟩, (realize_argP l p x).mpr h⟩


-- @@ L323-323 verbatim
end Semantic


-- @@ L325-325 verbatim
/-! ### The formulas of the kernel -/


-- @@ L327-327 verbatim
section Formulas


-- @@ L329-329 verbatim
variable {γ : Type}


-- @@ L331-334 expanded
/-- `q` is the pair of `x` and `y`. -/
noncomputable def pairOfF (q x y : γ) : eprSOLang.Formula γ :=
  (ptF₁ Language.peIsPairSym) q ⊓ ((ptF₂ Language.peFstSym) q x ⊓ (ptF₂ Language.peSndSym) q y)


-- @@ L336-338 expanded
/-- The assignment `w` sends `x` to `y`. -/
noncomputable def memF (w x y : γ) : eprSOLang.Formula γ :=
  FirstOrder.Language.Formula.iExs (Fin 1)
    (pairOfF (Sum.inr 0) (Sum.inl x) (Sum.inl y) ⊓ (ptF₂ Language.peMemSym) (Sum.inl w) (Sum.inr 0))


-- @@ L340-342 expanded
/-- The literal `l` names the variable `x` at the position `p`. -/
noncomputable def argF (l p x : γ) : eprSOLang.Formula γ :=
  FirstOrder.Language.Formula.iExs (Fin 1)
    (pairOfF (Sum.inr 0) (Sum.inl l) (Sum.inl p) ⊓ (ptF₂ Language.peArgSym) (Sum.inr 0) (Sum.inl x))


-- @@ L344-347 expanded
/-- Every element is sent somewhere by `w`. -/
noncomputable def totalF (w : γ) : eprSOLang.Formula γ :=
  FirstOrder.Language.Formula.iAlls (Fin 1)
    (((ptF₁ Language.peIsEltSym) (Sum.inr 0)).imp
      (FirstOrder.Language.Formula.iExs (Fin 1)
        ((ptF₁ Language.peIsEltSym) (Sum.inr 0) ⊓
          memF (Sum.inl (Sum.inl w)) (Sum.inl (Sum.inr 0)) (Sum.inr 0))))


-- @@ L349-354 expanded
/-- And to one place only. -/
noncomputable def funcF (w : γ) : eprSOLang.Formula γ :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
    (((ptF₁ Language.peIsEltSym) (Sum.inr 0) ⊓
            ((ptF₁ Language.peIsEltSym) (Sum.inr 1) ⊓ (ptF₁ Language.peIsEltSym) (Sum.inr 2)) ⊓
          (memF (Sum.inl w) (Sum.inr 0) (Sum.inr 1) ⊓ memF (Sum.inl w) (Sum.inr 0) (Sum.inr 2))).imp
      (ptEqF (Sum.inr 1) (Sum.inr 2)))


-- @@ L356-356 verbatim
variable {A : Type} [Language.epr.Structure A] [LinearOrder A]

-- @@ L357-357 verbatim
variable (ρ : ivBlock.Assignment (eprExp.Map A)) {v : γ → eprExp.Map A}


-- @@ L359-363 verbatim
@[simp]
theorem realize_pairOfF (q x y : γ) :
    (@Formula.Realize eprSOLang (eprExp.Map A) (eprSOStructure ρ) _ (pairOfF q x y) v ↔
      PairOfPt (v q) (v x) (v y)) := by
  simp only [pairOfF, PairOfPt, IsPairPt, Formula.realize_inf, realize_ptF₁, realize_ptF₂]


-- @@ L365-371 verbatim
@[simp]
theorem realize_memF (w x y : γ) :
    (@Formula.Realize eprSOLang (eprExp.Map A) (eprSOStructure ρ) _ (memF w x y) v ↔
      MemPt (v w) (v x) (v y)) := by
  simp only [memF, MemPt, Formula.realize_iExs, Formula.realize_inf, realize_pairOfF,
    realize_ptF₂, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨u, hu⟩ => ⟨u 0, hu⟩, fun ⟨q, hq⟩ => ⟨fun _ => q, hq⟩⟩


-- @@ L373-379 verbatim
@[simp]
theorem realize_argF (l p x : γ) :
    (@Formula.Realize eprSOLang (eprExp.Map A) (eprSOStructure ρ) _ (argF l p x) v ↔
      ArgPt (v l) (v p) (v x)) := by
  simp only [argF, ArgPt, Formula.realize_iExs, Formula.realize_inf, realize_pairOfF,
    realize_ptF₂, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨u, hu⟩ => ⟨u 0, hu⟩, fun ⟨q, hq⟩ => ⟨fun _ => q, hq⟩⟩


-- @@ L381-392 verbatim
@[simp]
theorem realize_totalF (w : γ) :
    (@Formula.Realize eprSOLang (eprExp.Map A) (eprSOStructure ρ) _ (totalF w) v ↔
      TotalPt (v w)) := by
  simp only [totalF, TotalPt, IsEltPt, Formula.realize_iAlls, Formula.realize_iExs,
    Formula.realize_imp, Formula.realize_inf, realize_ptF₁, realize_memF,
    Sum.elim_inl, Sum.elim_inr]
  refine ⟨fun h x hx => ?_, fun h u hu => ?_⟩
  · obtain ⟨u, hu⟩ := h (fun _ => x) hx
    exact ⟨u 0, hu⟩
  · obtain ⟨y, hy⟩ := h (u 0) hu
    exact ⟨fun _ => y, hy⟩


-- @@ L394-402 verbatim
@[simp]
theorem realize_funcF (w : γ) :
    (@Formula.Realize eprSOLang (eprExp.Map A) (eprSOStructure ρ) _ (funcF w) v ↔
      FuncPt (v w)) := by
  simp only [funcF, FuncPt, IsEltPt, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_ptF₁, realize_memF, realize_ptEqF,
    Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h x y z hx hy hz h1 h2 => h ![x, y, z] ⟨⟨hx, hy, hz⟩, h1, h2⟩,
    fun h u hu => h (u 0) (u 1) (u 2) hu.1.1 hu.1.2.1 hu.1.2.2 hu.2.1 hu.2.2⟩


-- @@ L404-404 verbatim
end Formulas


-- @@ L406-406 verbatim
/-! ### The clauses of the kernel -/


-- @@ L408-408 verbatim
section Clauses


-- @@ L410-410 verbatim
variable {γ : Type}


-- @@ L412-418 expanded
/-- The environment `w` is the one the two assignments make: the witness at an
existential variable, the assignment being tested elsewhere. -/
noncomputable def combF (e u w : γ) : eprSOLang.Formula γ :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
    (((ptF₁ Language.peIsEltSym) (Sum.inr 0) ⊓ (ptF₁ Language.peIsEltSym) (Sum.inr 1)).imp
      ((memF (Sum.inl w) (Sum.inr 0) (Sum.inr 1)).iff
        ((ptF₁ Language.peEVarSym) (Sum.inr 0) ⊓ memF (Sum.inl e) (Sum.inr 0) (Sum.inr 1) ⊔
          FirstOrder.Language.BoundedFormula.not ((ptF₁ Language.peEVarSym) (Sum.inr 0)) ⊓
            memF (Sum.inl u) (Sum.inr 0) (Sum.inr 1))))


-- @@ L420-426 expanded
/-- The assignment `w` of the argument positions matches the environment `v` on
the arguments the literal `l` declares. -/
noncomputable def matchF (l v w : γ) : eprSOLang.Formula γ :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
    (((ptF₁ Language.peIsEltSym) (Sum.inr 0) ⊓
            ((ptF₁ Language.peIsEltSym) (Sum.inr 1) ⊓ (ptF₁ Language.peIsEltSym) (Sum.inr 2)) ⊓
          (argF (Sum.inl l) (Sum.inr 0) (Sum.inr 1) ⊓ memF (Sum.inl v) (Sum.inr 1) (Sum.inr 2))).imp
      (memF (Sum.inl w) (Sum.inr 0) (Sum.inr 2)))


-- @@ L428-434 expanded
/-- The literal `l` is true at the environment `v`. -/
noncomputable def litTrueF (l v : γ) : eprSOLang.Formula γ :=
  FirstOrder.Language.Formula.iExs (Fin 2)
    ((ptF₁ Language.peIsEltSym) (Sum.inr 0) ⊓
        ((ptF₁ Language.peIsAsgSym) (Sum.inr 1) ⊓
          (totalF (Sum.inr 1) ⊓ (funcF (Sum.inr 1) ⊓ matchF (Sum.inl l) (Sum.inl v) (Sum.inr 1)))) ⊓
      ((ptF₂ Language.pePosSym) (Sum.inl l) (Sum.inr 0) ⊓ ivF (Sum.inr 0) (Sum.inr 1) ⊔
        (ptF₂ Language.peNegSym) (Sum.inl l) (Sum.inr 0) ⊓
          FirstOrder.Language.BoundedFormula.not (ivF (Sum.inr 0) (Sum.inr 1))))


-- @@ L436-443 expanded
/-- Every clause is true at every assignment of the universal variables. -/
noncomputable def matrixF (e : γ) : eprSOLang.Formula γ :=
  FirstOrder.Language.Formula.iAlls (Fin 2)
    (((ptF₁ Language.peIsAsgSym) (Sum.inr 0) ⊓
          (totalF (Sum.inr 0) ⊓
            (funcF (Sum.inr 0) ⊓
              ((ptF₁ Language.peIsAsgSym) (Sum.inr 1) ⊓
                combF (Sum.inl e) (Sum.inr 0) (Sum.inr 1))))).imp
      (FirstOrder.Language.Formula.iAlls (Fin 1)
        (((ptF₁ Language.peIsEltSym) (Sum.inr 0) ⊓ (ptF₁ Language.peClSym) (Sum.inr 0)).imp
          (FirstOrder.Language.Formula.iExs (Fin 1)
            ((ptF₁ Language.peIsEltSym) (Sum.inr 0) ⊓
              ((ptF₂ Language.peInClSym) (Sum.inl (Sum.inr 0)) (Sum.inr 0) ⊓
                litTrueF (Sum.inr 0) (Sum.inl (Sum.inl (Sum.inr 1)))))))))


-- @@ L445-445 verbatim
variable {A : Type} [Language.epr.Structure A] [LinearOrder A]

-- @@ L446-446 verbatim
variable (ρ : ivBlock.Assignment (eprExp.Map A)) {v : γ → eprExp.Map A}


-- @@ L448-455 verbatim
@[simp]
theorem realize_combF (e u w : γ) :
    (@Formula.Realize eprSOLang (eprExp.Map A) (eprSOStructure ρ) _ (combF e u w) v ↔
      CombPt (v e) (v u) (v w)) := by
  simp only [combF, CombPt, IsEltPt, EVarPt, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, Formula.realize_iff, Formula.realize_sup, Formula.realize_not,
    realize_ptF₁, realize_memF, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h x y hx hy => h ![x, y] ⟨hx, hy⟩, fun h u hu => h (u 0) (u 1) hu.1 hu.2⟩


-- @@ L457-465 verbatim
@[simp]
theorem realize_matchF (l vv w : γ) :
    (@Formula.Realize eprSOLang (eprExp.Map A) (eprSOStructure ρ) _ (matchF l vv w) v ↔
      MatchPt (v l) (v vv) (v w)) := by
  simp only [matchF, MatchPt, IsEltPt, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_inf, realize_ptF₁, realize_argF, realize_memF,
    Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun h p x y hp hx hy ha hm => h ![p, x, y] ⟨⟨hp, hx, hy⟩, ha, hm⟩,
    fun h u hu => h (u 0) (u 1) (u 2) hu.1.1 hu.1.2.1 hu.1.2.2 hu.2.1 hu.2.2⟩


-- @@ L467-475 verbatim
@[simp]
theorem realize_litTrueF (l vv : γ) :
    (@Formula.Realize eprSOLang (eprExp.Map A) (eprSOStructure ρ) _ (litTrueF l vv) v ↔
      LitTruePt ρ (v l) (v vv)) := by
  simp only [litTrueF, LitTruePt, MatchPt, IsEltPt, IsAsgPt, PosPt, NegPt,
    Formula.realize_iExs, Formula.realize_inf, Formula.realize_sup, Formula.realize_not,
    realize_ptF₁, realize_ptF₂, realize_totalF, realize_funcF, realize_matchF, realize_ivF,
    Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨u, hu⟩ => ⟨u 0, u 1, hu⟩, fun ⟨s, w, hs⟩ => ⟨![s, w], hs⟩⟩


-- @@ L477-493 verbatim
@[simp]
theorem realize_matrixF (e : γ) :
    (@Formula.Realize eprSOLang (eprExp.Map A) (eprSOStructure ρ) _ (matrixF e) v ↔
      ∀ u w, IsAsgPt u → TotalPt u → FuncPt u → IsAsgPt w → CombPt (v e) u w →
        ∀ c, IsEltPt c → ClPt c → ∃ l, IsEltPt l ∧ InClPt c l ∧ LitTruePt ρ l w) := by
  simp only [matrixF, CombPt, IsAsgPt, IsEltPt, ClPt, InClPt, Formula.realize_iAlls,
    Formula.realize_iExs, Formula.realize_imp, Formula.realize_inf, realize_ptF₁,
    realize_ptF₂, realize_totalF, realize_funcF, realize_combF, realize_litTrueF,
    Sum.elim_inl, Sum.elim_inr]
  constructor
  · intro h u w hu htot hfun hw hcomb c hc hcl
    obtain ⟨l, hl⟩ := h ![u, w] ⟨hu, htot, hfun, hw, hcomb⟩ ![c] ⟨hc, hcl⟩
    exact ⟨l 0, hl⟩
  · intro h uu hu cc hc
    obtain ⟨l, hl⟩ := h (uu 0) (uu 1) hu.1 hu.2.1 hu.2.2.1 hu.2.2.2.1 hu.2.2.2.2 (cc 0)
      hc.1 hc.2
    exact ⟨fun _ => l, hl⟩


-- @@ L495-495 verbatim
end Clauses


-- @@ L497-497 verbatim
/-! ### The kernel -/


-- @@ L499-499 verbatim
section Kernel


-- @@ L501-510 expanded
/-- The guess is local. -/
noncomputable def localF : eprSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 3)
    (((ptF₁ Language.peIsEltSym) (Sum.inr 0) ⊓
            ((ptF₁ Language.peIsAsgSym) (Sum.inr 1) ⊓ (ptF₁ Language.peIsAsgSym) (Sum.inr 2)) ⊓
          FirstOrder.Language.Formula.iAlls (Fin 2)
            (((ptF₁ Language.peIsEltSym) (Sum.inr 0) ⊓
                  ((ptF₁ Language.peIsEltSym) (Sum.inr 1) ⊓
                    (ptF₂ Language.peSigSym) (Sum.inl (Sum.inr 0)) (Sum.inr 0))).imp
              ((memF (Sum.inl (Sum.inr 1)) (Sum.inr 0) (Sum.inr 1)).iff
                (memF (Sum.inl (Sum.inr 2)) (Sum.inr 0) (Sum.inr 1))))).imp
      ((ivF (Sum.inr 0) (Sum.inr 1)).iff (ivF (Sum.inr 0) (Sum.inr 2))))


-- @@ L512-524 expanded
/-- The instance is well-formed: an atom names one variable at each position of
its symbol's signature, and names one at each. -/
noncomputable def wfF : eprSOLang.Sentence :=
  FirstOrder.Language.Formula.iAlls (Fin 4)
      (((ptF₁ Language.peIsEltSym) (Sum.inr 0) ⊓
              ((ptF₁ Language.peIsEltSym) (Sum.inr 1) ⊓
                ((ptF₁ Language.peIsEltSym) (Sum.inr 2) ⊓ (ptF₁ Language.peIsEltSym) (Sum.inr 3))) ⊓
            (argF (Sum.inr 0) (Sum.inr 1) (Sum.inr 2) ⊓
              argF (Sum.inr 0) (Sum.inr 1) (Sum.inr 3))).imp
        (ptEqF (Sum.inr 2) (Sum.inr 3))) ⊓
    FirstOrder.Language.Formula.iAlls (Fin 3)
      (((ptF₁ Language.peIsEltSym) (Sum.inr 0) ⊓
              ((ptF₁ Language.peIsEltSym) (Sum.inr 1) ⊓ (ptF₁ Language.peIsEltSym) (Sum.inr 2)) ⊓
            (((ptF₂ Language.pePosSym) (Sum.inr 0) (Sum.inr 1) ⊔
                (ptF₂ Language.peNegSym) (Sum.inr 0) (Sum.inr 1)) ⊓
              (ptF₂ Language.peSigSym) (Sum.inr 1) (Sum.inr 2))).imp
        (FirstOrder.Language.Formula.iExs (Fin 1)
          ((ptF₁ Language.peIsEltSym) (Sum.inr 0) ⊓
            argF (Sum.inl (Sum.inr 0)) (Sum.inl (Sum.inr 2)) (Sum.inr 0))))


-- @@ L526-531 expanded
/-- **The kernel of the `Σ₁` definition**: the instance is well-formed, the
guess is local, and some assignment of the existential variables satisfies every
clause at every assignment of the universal ones. -/
noncomputable def eprKernel : eprSOLang.Sentence :=
  wfF ⊓
    (localF ⊓
      FirstOrder.Language.Formula.iExs (Fin 1)
        ((ptF₁ Language.peIsAsgSym) (Sum.inr 0) ⊓ (totalF (Sum.inr 0) ⊓ funcF (Sum.inr 0)) ⊓
          matrixF (Sum.inr 0)))


-- @@ L533-533 verbatim
variable {A : Type} [Language.epr.Structure A] [LinearOrder A]

-- @@ L534-534 verbatim
variable (ρ : ivBlock.Assignment (eprExp.Map A))


-- @@ L536-543 verbatim
/-- Splitting a conjunction of sentences, kept at the level of `Sentence.Realize`
so that the clause lemmas still apply to the parts. -/
theorem realizeS_inf (φ ψ : eprSOLang.Sentence) :
    (@Sentence.Realize eprSOLang (eprExp.Map A) (eprSOStructure ρ) (φ ⊓ ψ) ↔
      ((@Sentence.Realize eprSOLang (eprExp.Map A) (eprSOStructure ρ) φ) ∧
        @Sentence.Realize eprSOLang (eprExp.Map A) (eprSOStructure ρ) ψ)) :=
  letI := eprSOStructure ρ
  Formula.realize_inf


-- @@ L545-554 verbatim
@[simp]
theorem realize_localF :
    (@Sentence.Realize eprSOLang (eprExp.Map A) (eprSOStructure ρ) localF ↔ LocalPt ρ) := by
  simp only [localF, LocalPt, IsEltPt, IsAsgPt, SigPt, Sentence.Realize,
    Formula.realize_iAlls, Formula.realize_imp, Formula.realize_inf, Formula.realize_iff,
    realize_ptF₁, realize_ptF₂, realize_memF, realize_ivF, Sum.elim_inl, Sum.elim_inr]
  refine ⟨fun h s w w' hs hw hw' hag => h ![s, w, w'] ⟨⟨hs, hw, hw'⟩, fun u hu => ?_⟩,
    fun h u hu => h (u 0) (u 1) (u 2) hu.1.1 hu.1.2.1 hu.1.2.2 fun p y hp hy hsig => ?_⟩
  · exact hag (u 0) (u 1) hu.1 hu.2.1 hu.2.2
  · exact hu.2 ![p, y] ⟨hp, hy, hsig⟩


-- @@ L556-572 verbatim
@[simp]
theorem realize_wfF :
    (@Sentence.Realize eprSOLang (eprExp.Map A) (eprSOStructure ρ) wfF ↔ WFPt A) := by
  simp only [wfF, WFPt, IsEltPt, PosPt, NegPt, SigPt, Sentence.Realize, Formula.realize_inf,
    Formula.realize_iAlls, Formula.realize_iExs, Formula.realize_imp, Formula.realize_sup,
    realize_ptF₁, realize_ptF₂, realize_argF, realize_ptEqF, Sum.elim_inl, Sum.elim_inr]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun l p x y hl hp hx hy ha hb => h1 ![l, p, x, y] ⟨⟨hl, hp, hx, hy⟩, ha, hb⟩, ?_⟩
    intro l s p hl hs hp hpn hsig
    obtain ⟨u, hu⟩ := h2 ![l, s, p] ⟨⟨hl, hs, hp⟩, hpn, hsig⟩
    exact ⟨u 0, hu⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun u hu => h1 (u 0) (u 1) (u 2) (u 3) hu.1.1 hu.1.2.1 hu.1.2.2.1 hu.1.2.2.2
      hu.2.1 hu.2.2, fun u hu => ?_⟩
    obtain ⟨x, hx⟩ := h2 (u 0) (u 1) (u 2) hu.1.1 hu.1.2.1 hu.1.2.2 hu.2.1 hu.2.2
    exact ⟨fun _ => x, hx⟩


-- @@ L574-584 verbatim
@[simp]
theorem realize_eprKernel :
    (@Sentence.Realize eprSOLang (eprExp.Map A) (eprSOStructure ρ) eprKernel ↔
      (WFPt A ∧ LocalPt ρ ∧ ∃ e, (IsAsgPt e ∧ TotalPt e ∧ FuncPt e) ∧
        ∀ u w, IsAsgPt u → TotalPt u → FuncPt u → IsAsgPt w → CombPt e u w →
          ∀ c, IsEltPt c → ClPt c → ∃ l, IsEltPt l ∧ InClPt c l ∧ LitTruePt ρ l w)) := by
  rw [eprKernel, realizeS_inf, realizeS_inf, realize_wfF, realize_localF]
  refine and_congr Iff.rfl (and_congr Iff.rfl ?_)
  simp only [Sentence.Realize, Formula.realize_iExs, Formula.realize_inf, realize_ptF₁,
    realize_totalF, realize_funcF, realize_matrixF, IsAsgPt, Sum.elim_inr]
  exact ⟨fun ⟨u, hu⟩ => ⟨u 0, hu⟩, fun ⟨e, he⟩ => ⟨fun _ => e, he⟩⟩


-- @@ L586-586 verbatim
end Kernel


-- @@ L588-588 verbatim
/-! ### The points a model is made of -/


-- @@ L590-590 verbatim
section Bridge


-- @@ L592-592 verbatim
variable {A : Type} [Language.epr.Structure A] [LinearOrder A]


-- @@ L594-595 verbatim
/-- **The point a function is**: its graph. -/
noncomputable def funPt (f : A → A) : eprExp.Map A := asgPt (fun a b => f a = b)


-- @@ L597-598 verbatim
@[simp]
theorem isAsgPt_funPt (f : A → A) : IsAsgPt (funPt f) := isAsgPt_asgPt _


-- @@ L600-602 verbatim
@[simp]
theorem memPt_funPt (f : A → A) (x y : A) : MemPt (funPt f) (eltPt x) (eltPt y) ↔ f x = y :=
  memPt_iff _ x y


-- @@ L604-607 verbatim
theorem totalPt_funPt (f : A → A) : TotalPt (funPt f) := by
  intro x hx
  obtain ⟨a, rfl⟩ := exists_eltPt hx
  exact ⟨eltPt (f a), isEltPt_eltPt _, (memPt_funPt f a (f a)).mpr rfl⟩


-- @@ L609-614 verbatim
theorem funcPt_funPt (f : A → A) : FuncPt (funPt f) := by
  intro x y z hx hy hz h1 h2
  obtain ⟨a, rfl⟩ := exists_eltPt hx
  obtain ⟨b, rfl⟩ := exists_eltPt hy
  obtain ⟨c, rfl⟩ := exists_eltPt hz
  rw [← (memPt_funPt f a b).mp h1, ← (memPt_funPt f a c).mp h2]


-- @@ L616-635 verbatim
open Classical in
/-- **A total functional assignment is the graph of a function.** -/
theorem exists_funPt {w : eprExp.Map A} (hw : IsAsgPt w) (ht : TotalPt w) (hf : FuncPt w) :
    ∃ f : A → A, w = funPt f := by
  classical
  obtain ⟨R, rfl⟩ := exists_asgPt hw
  have hex : ∀ x : A, ∃ y : A, R x y := by
    intro x
    obtain ⟨y, hy, hmem⟩ := ht (eltPt x) (isEltPt_eltPt x)
    obtain ⟨b, rfl⟩ := exists_eltPt hy
    exact ⟨b, (memPt_iff R x b).mp hmem⟩
  refine ⟨fun x => (hex x).choose, ?_⟩
  refine congrArg asgPt (funext fun x => funext fun y => propext ⟨fun h => ?_, fun h => ?_⟩)
  · have h1 : MemPt (asgPt R) (eltPt x) (eltPt y) := (memPt_iff R x y).mpr h
    have h2 : MemPt (asgPt R) (eltPt x) (eltPt (hex x).choose) :=
      (memPt_iff R x _).mpr (hex x).choose_spec
    exact (eltPt_injective (hf _ _ _ (isEltPt_eltPt x) (isEltPt_eltPt y)
      (isEltPt_eltPt _) h1 h2)).symm
  · rw [← h]
    exact (hex x).choose_spec


-- @@ L637-637 verbatim
end Bridge


-- @@ L639-639 verbatim
/-! ### The agreement -/


-- @@ L641-641 verbatim
section Agreement


-- @@ L643-643 verbatim
variable {A : Type} [Language.epr.Structure A] [LinearOrder A]


-- @@ L645-670 verbatim
/-- **Well-formedness read at the points is well-formedness.** -/
theorem wfPt_iff : WFPt A ↔ IsWF A := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun l p x y hx hy => eltPt_injective (h1 (eltPt l) (eltPt p) (eltPt x) (eltPt y)
      (isEltPt_eltPt l) (isEltPt_eltPt p) (isEltPt_eltPt x) (isEltPt_eltPt y)
      ((argPt_iff l p x).mpr hx) ((argPt_iff l p y).mpr hy)), fun l s p hls hsp => ?_⟩
    obtain ⟨q, hq, ha⟩ := h2 (eltPt l) (eltPt s) (eltPt p) (isEltPt_eltPt l)
      (isEltPt_eltPt s) (isEltPt_eltPt p)
      (hls.imp (posPt_iff l s).mpr (negPt_iff l s).mpr) ((sigPt_iff s p).mpr hsp)
    obtain ⟨x, rfl⟩ := exists_eltPt hq
    exact ⟨x, (argPt_iff l p x).mp ha⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun l p x y hl hp hx hy ha hb => ?_, fun l s p hl hs hp hpn hsig => ?_⟩
    · obtain ⟨l', rfl⟩ := exists_eltPt hl
      obtain ⟨p', rfl⟩ := exists_eltPt hp
      obtain ⟨x', rfl⟩ := exists_eltPt hx
      obtain ⟨y', rfl⟩ := exists_eltPt hy
      exact congrArg eltPt (h1 l' p' x' y' ((argPt_iff l' p' x').mp ha)
        ((argPt_iff l' p' y').mp hb))
    · obtain ⟨l', rfl⟩ := exists_eltPt hl
      obtain ⟨s', rfl⟩ := exists_eltPt hs
      obtain ⟨p', rfl⟩ := exists_eltPt hp
      obtain ⟨x, hx⟩ := h2 l' s' p' (hpn.imp (posPt_iff l' s').mp (negPt_iff l' s').mp)
        ((sigPt_iff s' p').mp hsig)
      exact ⟨eltPt x, isEltPt_eltPt x, (argPt_iff l' p' x).mpr hx⟩


-- @@ L672-678 verbatim
/-- **The guess a model is**: a symbol holds of an assignment when the
interpretation holds of a function the assignment agrees with on the signature
positions. -/
noncomputable def modelGuess (I : A → (A → A) → Prop) :
    ivBlock.Assignment (eprExp.Map A) :=
  fun _ v => ∃ (x : A) (f : A → A), v 0 = eltPt x ∧
    (∀ p y : A, SigG x p → (MemPt (v 1) (eltPt p) (eltPt y) ↔ f p = y)) ∧ I x f


-- @@ L680-690 verbatim
theorem modelGuess_funPt {I : A → (A → A) → Prop} (hlocal : Local I) (x : A) (f : A → A) :
    modelGuess I () ![eltPt x, funPt f] ↔ I x f := by
  constructor
  · rintro ⟨x', f', hx, hag, hI⟩
    have hxx : x = x' := eltPt_injective hx
    subst hxx
    refine (hlocal x f f' fun p hp => ?_).mpr hI
    exact ((hag p (f p) hp).mp ((memPt_funPt f p (f p)).mpr rfl)).symm
  · intro hI
    refine ⟨x, f, rfl, fun p y _ => ?_, hI⟩
    exact memPt_funPt f p y


-- @@ L692-704 verbatim
/-- **The environment two assignments make, as a point.** -/
theorem combPt_funPt (e g : A → A) :
    CombPt (funPt e) (funPt g) (funPt (eprVal e g)) := by
  classical
  intro x y hx hy
  obtain ⟨a, rfl⟩ := exists_eltPt hx
  obtain ⟨b, rfl⟩ := exists_eltPt hy
  rw [memPt_funPt, memPt_funPt, memPt_funPt, eVarPt_iff, eprVal]
  by_cases ha : EVarG a
  · rw [ite_eq_left ha]
    exact ⟨fun h => Or.inl ⟨ha, h⟩, fun h => h.elim (fun h => h.2) (fun h => absurd ha h.1)⟩
  · rw [ite_eq_right ha]
    exact ⟨fun h => Or.inr ⟨ha, h⟩, fun h => h.elim (fun h => absurd h.1 ha) (fun h => h.2)⟩


-- @@ L706-800 verbatim
/-- **A model on the instance is a guess the kernel accepts, and back.** -/
theorem selfModel_iff_kernel :
    (SelfModel A ↔ ∃ ρ : ivBlock.Assignment (eprExp.Map A),
      LocalPt ρ ∧ ∃ e, (IsAsgPt e ∧ TotalPt e ∧ FuncPt e) ∧
        ∀ u w, IsAsgPt u → TotalPt u → FuncPt u → IsAsgPt w → CombPt e u w →
          ∀ c, IsEltPt c → ClPt c → ∃ l, IsEltPt l ∧ InClPt c l ∧ LitTruePt ρ l w) := by
  classical
  constructor
  · rintro ⟨I, ε, hlocal, hsat⟩
    refine ⟨modelGuess I, ?_, funPt ε,
      ⟨isAsgPt_funPt ε, totalPt_funPt ε, funcPt_funPt ε⟩, ?_⟩
    · -- locality: the guess reads the assignment only at the signature positions
      intro s w w' hs hw hw' hag
      obtain ⟨x, rfl⟩ := exists_eltPt hs
      constructor
      · rintro ⟨x', f, hx, hf, hI⟩
        have hxx : x = x' := eltPt_injective hx
        subst hxx
        refine ⟨x, f, hx, fun p y hp => ?_, hI⟩
        exact (hag (eltPt p) (eltPt y) (isEltPt_eltPt p) (isEltPt_eltPt y)
          ((sigPt_iff x p).mpr hp)).symm.trans (hf p y hp)
      · rintro ⟨x', f, hx, hf, hI⟩
        have hxx : x = x' := eltPt_injective hx
        subst hxx
        refine ⟨x, f, hx, fun p y hp => ?_, hI⟩
        exact (hag (eltPt p) (eltPt y) (isEltPt_eltPt p) (isEltPt_eltPt y)
          ((sigPt_iff x p).mpr hp)).trans (hf p y hp)
    · -- the matrix, at every assignment of the universal variables
      intro u w hu htot hfun hw hcomb c hc hcl
      obtain ⟨g, rfl⟩ := exists_funPt hu htot hfun
      obtain ⟨c', rfl⟩ := exists_eltPt hc
      obtain ⟨Rw, rfl⟩ := exists_asgPt hw
      have hwv : Rw = fun a b => eprVal ε g a = b := by
        funext a b
        refine propext ?_
        have h := hcomb (eltPt a) (eltPt b) (isEltPt_eltPt a) (isEltPt_eltPt b)
        rw [memPt_iff, memPt_funPt, memPt_funPt, eVarPt_iff] at h
        rw [h, eprVal]
        by_cases ha : EVarG a
        · rw [ite_eq_left ha]
          exact ⟨fun hc => hc.elim (fun h => h.2) (fun h => absurd ha h.1),
            fun hc => Or.inl ⟨ha, hc⟩⟩
        · rw [ite_eq_right ha]
          exact ⟨fun hc => hc.elim (fun h => absurd h.1 ha) (fun h => h.2),
            fun hc => Or.inr ⟨ha, hc⟩⟩
      subst hwv
      obtain ⟨l, hl, htrue⟩ := hsat g c' ((clPt_iff c').mp hcl)
      refine ⟨eltPt l, isEltPt_eltPt l, (inClPt_iff c' l).mpr hl, ?_⟩
      have hmatch : ∀ (f : A → A), (∀ p x, ArgG l p x → f p = eprVal ε g x) →
          MatchPt (eltPt l) (asgPt fun a b => eprVal ε g a = b) (funPt f) := by
        intro f hf p x y hp hx hy harg hmem
        obtain ⟨p', rfl⟩ := exists_eltPt hp
        obtain ⟨x', rfl⟩ := exists_eltPt hx
        obtain ⟨y', rfl⟩ := exists_eltPt hy
        rw [memPt_funPt]
        rw [memPt_iff] at hmem
        rw [← hmem]
        exact hf p' x' ((argPt_iff l p' x').mp harg)
      rcases htrue with ⟨s, hs, f, hf, hI⟩ | ⟨s, hs, f, hf, hI⟩
      · exact ⟨eltPt s, funPt f, ⟨isEltPt_eltPt s, isAsgPt_funPt f, totalPt_funPt f,
          funcPt_funPt f, hmatch f hf⟩,
          Or.inl ⟨(posPt_iff l s).mpr hs, (modelGuess_funPt hlocal s f).mpr hI⟩⟩
      · exact ⟨eltPt s, funPt f, ⟨isEltPt_eltPt s, isAsgPt_funPt f, totalPt_funPt f,
          funcPt_funPt f, hmatch f hf⟩,
          Or.inr ⟨(negPt_iff l s).mpr hs,
            fun hc => hI ((modelGuess_funPt hlocal s f).mp hc)⟩⟩
  · rintro ⟨ρ, hlocal, e, ⟨he, hte, hfe⟩, hmat⟩
    obtain ⟨ε, rfl⟩ := exists_funPt he hte hfe
    refine ⟨fun x f => ρ () ![eltPt x, funPt f], ε, ?_, ?_⟩
    · -- locality of the interpretation the guess is
      intro s w w' hag
      refine hlocal (eltPt s) (funPt w) (funPt w') (isEltPt_eltPt s) (isAsgPt_funPt w)
        (isAsgPt_funPt w') fun p y hp hy hsig => ?_
      obtain ⟨p', rfl⟩ := exists_eltPt hp
      obtain ⟨y', rfl⟩ := exists_eltPt hy
      rw [memPt_funPt, memPt_funPt, hag p' ((sigPt_iff s p').mp hsig)]
    · -- and the matrix it satisfies
      intro g c hcl
      obtain ⟨l, hl, hin, htrue⟩ := hmat (funPt g) (funPt (eprVal ε g)) (isAsgPt_funPt g)
        (totalPt_funPt g) (funcPt_funPt g) (isAsgPt_funPt _) (combPt_funPt ε g)
        (eltPt c) (isEltPt_eltPt c) ((clPt_iff c).mpr hcl)
      obtain ⟨l', rfl⟩ := exists_eltPt hl
      refine ⟨l', (inClPt_iff c l').mp hin, ?_⟩
      obtain ⟨s, w, ⟨hs, hw, htot, hfun, hmatch⟩, hpn⟩ := htrue
      obtain ⟨s', rfl⟩ := exists_eltPt hs
      obtain ⟨f, rfl⟩ := exists_funPt hw htot hfun
      have hf : ∀ p x, ArgG l' p x → f p = eprVal ε g x := by
        intro p x harg
        have := hmatch (eltPt p) (eltPt x) (eltPt (eprVal ε g x)) (isEltPt_eltPt p)
          (isEltPt_eltPt x) (isEltPt_eltPt _) ((argPt_iff l' p x).mpr harg)
          ((memPt_funPt (eprVal ε g) x _).mpr rfl)
        exact (memPt_funPt f p _).mp this
      rcases hpn with ⟨hp, hiv⟩ | ⟨hp, hiv⟩
      · exact Or.inl ⟨s', (posPt_iff l' s').mp hp, f, hf, hiv⟩
      · exact Or.inr ⟨s', (negPt_iff l' s').mp hp, f, hf, hiv⟩


-- @@ L802-802 verbatim
end Agreement


-- @@ L804-804 verbatim
/-! ### The membership -/


-- @@ L806-806 verbatim
section Membership


-- @@ L808-822 verbatim
/-- **The kernel says what the problem does.** -/
theorem epr_iff_kernel (A : Type) [Language.epr.Structure A] [LinearOrder A]
    [Finite A] [Nonempty A] :
    (EPR A ↔ ∃ ρ : ivBlock.Assignment (eprExp.Map A),
      @Sentence.Realize eprSOLang (eprExp.Map A) (eprSOStructure ρ) eprKernel) := by
  constructor
  · rintro ⟨hwf, hsat⟩
    obtain ⟨ρ, hlocal, e, he, hmat⟩ :=
      selfModel_iff_kernel.mp ((eprSatOn_iff_selfModel hwf).mp hsat)
    exact ⟨ρ, (realize_eprKernel ρ).mpr ⟨wfPt_iff.mpr hwf, hlocal, e, he, hmat⟩⟩
  · rintro ⟨ρ, hρ⟩
    obtain ⟨hwf, hlocal, e, he, hmat⟩ := (realize_eprKernel ρ).mp hρ
    have hwf' : IsWF A := wfPt_iff.mp hwf
    exact ⟨hwf', (eprSatOn_iff_selfModel hwf').mpr
      (selfModel_iff_kernel.mpr ⟨ρ, hlocal, e, he, hmat⟩)⟩


-- @@ L824-835 verbatim
/-- **EPR is in NEXPTIME.** The expansion's points are the relations on the
instance, so an assignment of the universal variables is one of them and the
`∀` that makes the problem exponential is first-order there; what is guessed is
one relation between the symbols and the assignments, which is one `Σ₁`
block. -/
theorem epr_mem_NEXPTIME : EPR ∈ NEXPTIME := by
  let hinst : ∀ (A : Type) [Language.epr.Structure A] [LinearOrder A],
      Language.eprPt.Structure (eprExp.Map A) := fun A => eprPtStructure A
  refine ⟨eprExp, soProblem Language.eprPt [ivBlock] eprKernel true,
    ⟨[ivBlock], rfl, eprKernel, fun A _ _ _ => Iff.rfl⟩, ?_⟩
  intro A _ _ _ _
  exact epr_iff_kernel A


-- @@ L837-837 verbatim
end Membership


-- @@ L839-839 verbatim
end Epr


-- @@ L841-841 verbatim
end DescriptiveComplexity
