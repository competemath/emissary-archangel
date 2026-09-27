/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/
module


public import LeanPool.FormalizationOfBoundedArithmetic.Order
import LeanPool.FormalizationOfBoundedArithmetic.Register


-- @@ L12-14 verbatim
/-!
# LeanPool.FormalizationOfBoundedArithmetic.Complexity
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
open FirstOrder Language


-- @@ L20-20 verbatim
universe u

-- @@ L21-21 verbatim
variable {L : Language} {α β : Type u} {n : Nat}


-- @@ L23-23 verbatim
namespace FirstOrder.Language


-- @@ L25-25 verbatim
attribute [local implicit_reducible] zambella


-- @@ L27-27 verbatim
namespace BoundedFormula.IsAtomic

-- @@ L28-28 verbatim
variable {φ : L.BoundedFormula α n}


-- @@ L30-30 verbatim
namespace relabelEquiv


-- @@ L32-35 verbatim
theorem mpr {f : α ≃ β} (h : φ.IsAtomic)
  : (φ.relabelEquiv f).IsAtomic
:=
  IsAtomic.recOn h (fun _ _ => IsAtomic.equal _ _) fun _ _ => IsAtomic.rel _ _


-- @@ L37-40 verbatim
theorem mp {f : α ≃ β} (h : (φ.relabelEquiv f).IsAtomic)
  : φ.IsAtomic :=
by
  cases φ <;> (try cases h) <;> constructor


-- @@ L42-42 verbatim
end relabelEquiv


-- @@ L44-47 verbatim
@[delta0_simps]
theorem relabelEquiv {f : α ≃ β} :
  (φ.relabelEquiv f).IsAtomic <-> φ.IsAtomic :=
  ⟨relabelEquiv.mp, relabelEquiv.mpr⟩

-- @@ L48-48 verbatim
end BoundedFormula.IsAtomic


-- @@ L50-50 verbatim
namespace Formula.IsAtomic

-- @@ L51-51 verbatim
open BoundedFormula


-- @@ L53-58 verbatim
@[delta0_simps]
theorem display1 {n1} {phi : L.Formula (Vars1 n1)} :
  phi.display1.IsAtomic <-> phi.IsAtomic :=
by
  unfold Formula.display1
  rw [IsAtomic.relabelEquiv]


-- @@ L60-65 verbatim
@[delta0_simps]
theorem display2 {n1 n2} {phi : L.Formula (Vars2 n1 n2)} :
  phi.display2.IsAtomic <-> phi.IsAtomic :=
by
  unfold Formula.display2
  rw [IsAtomic.relabelEquiv]


-- @@ L67-72 verbatim
@[delta0_simps]
theorem display3 {n1 n2 n3} {phi : L.Formula (Vars3 n1 n2 n3)} :
  phi.display3.IsAtomic <-> phi.IsAtomic :=
by
  unfold Formula.display3
  rw [IsAtomic.relabelEquiv]


-- @@ L74-74 verbatim
end Formula.IsAtomic


-- @@ L76-76 verbatim
namespace BoundedFormula.IsQF


-- @@ L78-78 verbatim
namespace imp


-- @@ L80-94 verbatim
@[delta0_simps]
theorem mpr {L : Language} {α} {m} {φ ψ : L.BoundedFormula α m} :
  (φ.imp ψ).IsQF <-> (φ.IsQF ∧ ψ.IsQF) :=
by
  constructor
  · intro h
    constructor
    · cases h with
      | of_isAtomic h' => cases h'
      | imp pre post => exact pre
    · cases h with
      | of_isAtomic h' => cases h'
      | imp pre post => exact post
  · intro h
    apply IsQF.imp h.left h.right


-- @@ L96-96 verbatim
end imp


-- @@ L98-98 verbatim
namespace relabelEquiv


-- @@ L100-127 verbatim
@[delta0_simps]
theorem mp {L : Language} {α β} {m : ℕ} {φ : L.BoundedFormula α m}
  (f : α ≃ β)
  (h : φ.IsQF)
  : (φ.relabelEquiv f).IsQF :=
by
  induction φ with
  | falsum =>
    constructor
  | equal lhs rhs =>
    simp only [relabelEquiv, mapTermRelEquiv, Equiv.coe_refl, Equiv.refl_symm, Equiv.coe_fn_mk,
      mapTermRel, Term.relabelEquiv_apply]
    constructor; constructor
  | rel R ts =>
    simp only [relabelEquiv, mapTermRelEquiv, Equiv.coe_refl, Equiv.refl_symm, Equiv.coe_fn_mk,
      mapTermRel, Term.relabelEquiv_apply]
    constructor; constructor
  | imp pre post hind_pre hind_post =>
    cases h with
    | of_isAtomic hh => cases hh
    | imp hpre hpost =>
      rw [relabelEquiv.imp]
      apply IsQF.imp
      · exact hind_pre hpre
      · exact hind_post hpost
  | all f f_ih =>
    cases h with
    | of_isAtomic h' => cases h'


-- @@ L129-137 verbatim
@[delta0_simps]
theorem mpr {L : Language} {α β} {m : ℕ} {φ : L.BoundedFormula α m} (f : α ≃ β)
  (h : (φ.relabelEquiv f).IsQF)
  : φ.IsQF :=
by
  have h' : relabelEquiv f.symm ((relabelEquiv f) φ) = φ := relabelEquiv.comp_inv f
  rw [<- h']
  apply relabelEquiv.mp
  exact h


-- @@ L139-139 verbatim
end relabelEquiv


-- @@ L141-143 verbatim
@[delta0_simps]
theorem relabelEquiv {L : Language} {α β} {m : ℕ} {φ : L.BoundedFormula α m} (f : α ≃ β) :
  (φ.relabelEquiv f).IsQF <-> φ.IsQF := ⟨IsQF.relabelEquiv.mpr f, IsQF.relabelEquiv.mp f⟩



-- @@ L146-151 verbatim
end BoundedFormula.IsQF




-- Definition 3.7, page 36 of draft (47 of pdf)

-- @@ L152-152 verbatim
namespace BoundedFormula


-- @@ L154-156 verbatim
/-- Open formulas are quantifier-free bounded formulas. -/
abbrev IsOpen (formula : L.BoundedFormula α n)
  := IsQF formula

-- @@ L157-157 verbatim
namespace IsOpen

-- @@ L158-158 verbatim
variable {phi : L.BoundedFormula α n}


-- @@ L160-165 verbatim
@[delta0_simps]
theorem equal (t1 t2 : L.Term (α ⊕ Fin n))
  : (t1.bdEqual t2).IsOpen :=
by
  constructor
  apply IsAtomic.equal


-- @@ L167-167 verbatim
namespace imp

-- @@ L168-168 verbatim
namespace mpr


-- @@ L170-179 verbatim
@[delta0_simps]
theorem left {psi : _}
  : (phi.imp psi).IsOpen -> phi.IsOpen :=
by
  intro h
  -- TODO: order of constructors in IsQF should be reversed,
  -- so that `constructor` here works!
  cases h with
  | of_isAtomic h => cases h
  | imp p q => exact p


-- @@ L181-188 verbatim
@[delta0_simps]
theorem right {psi : _}
  : (phi.imp psi).IsOpen -> psi.IsOpen :=
by
  intro h
  cases h with
  | of_isAtomic h => cases h
  | imp p q => exact q


-- @@ L190-190 verbatim
end mpr

-- @@ L191-191 verbatim
end imp


-- @@ L193-201 verbatim
@[delta0_simps]
theorem not
  : phi.not.IsOpen <-> phi.IsOpen :=
by
  constructor <;> (unfold BoundedFormula.not; intro h)
  · exact imp.mpr.left h
  · apply IsQF.imp
    · assumption
    · exact isQF_bot


-- @@ L203-207 verbatim
@[delta0_simps]
theorem relabelEquiv {f : α ≃ β}
  : (phi.relabelEquiv f).IsOpen <-> phi.IsOpen :=
by
  apply IsQF.relabelEquiv


-- @@ L209-209 verbatim
end IsOpen

-- @@ L210-210 verbatim
end BoundedFormula


-- @@ L212-212 verbatim
namespace Formula.IsOpen

-- @@ L213-213 verbatim
open BoundedFormula.IsOpen


-- @@ L215-219 verbatim
@[delta0_simps]
theorem display1 {n1} {phi : L.Formula (Vars1 n1)} :
    phi.display1.IsOpen <-> phi.IsOpen := by
  unfold Formula.display1
  rw [relabelEquiv]


-- @@ L221-225 verbatim
@[delta0_simps]
theorem display2 {n1 n2} {phi : L.Formula (Vars2 n1 n2)} :
    phi.display2.IsOpen <-> phi.IsOpen := by
  unfold Formula.display2
  rw [relabelEquiv]


-- @@ L227-231 verbatim
@[delta0_simps]
theorem display3 {n1 n2 n3} {phi : L.Formula (Vars3 n1 n2 n3)} :
    phi.display3.IsOpen <-> phi.IsOpen := by
  unfold Formula.display3
  rw [relabelEquiv]


-- @@ L233-233 verbatim
end Formula.IsOpen




-- @@ L237-237 verbatim
variable {L : Language} [IsOrdered L] {a : Type u}

-- @@ L238-242 verbatim
open BoundedFormula Formula

-- Definition 3.7, page 36 of draft (47 of pdf)
-- + Definition 3.6, page 35 of draft (46 of pdf)
-- fix level of `a` to 0, because level of `Vars` was fixed to 0!

-- @@ L243-243 verbatim
namespace BoundedFormula


-- @@ L245-259 verbatim
/-- Delta-zero formulas, built from quantifier-free formulas and bounded number quantifiers. -/
inductive IsDelta0 :
    ∀ {a : Type} {n : Nat}, L.BoundedFormula a n -> Prop
| bdEx {a : Type} {n : FvName}
  {phi : L.Formula (a ⊕ (Vars1 n))}
  (t : L.Term (a ⊕ Fin 0))
  : IsDelta0 phi -> (IsDelta0 <| iBdEx' t phi)
| bdAll {a : Type} {n : FvName}
  {phi : L.Formula (a ⊕ (Vars1 n))}
  (t : L.Term (a ⊕ Fin 0))
  : IsDelta0 phi -> (IsDelta0 <| iBdAll' t phi)
| imp {a : Type} {n : Nat} {phi1 phi2 : L.BoundedFormula a n}
  : IsDelta0 phi1 -> IsDelta0 phi2 -> IsDelta0 (phi1.imp phi2)
| of_isQF {a : Type} {n : Nat} {phi : L.BoundedFormula a n}
  : BoundedFormula.IsQF phi -> IsDelta0 phi


-- @@ L261-261 verbatim
end BoundedFormula


-- @@ L263-263 verbatim
namespace IsDelta0


-- @@ L265-268 verbatim
@[delta0_simps]
theorem bot {a n} : (⊥ : L.BoundedFormula a n).IsDelta0  := by
  constructor
  exact isQF_bot


-- @@ L270-276 verbatim
@[delta0_simps]
theorem equal {a n} (t1 t2 : L.Term (a ⊕ Fin n))
  : (t1.bdEqual t2).IsDelta0 :=
by
  constructor
  constructor
  apply IsAtomic.equal


-- @@ L278-278 verbatim
namespace of_open


-- @@ L280-299 verbatim
theorem imp {a n} {phi psi : L.BoundedFormula a n} (h : phi.IsOpen)
  : (phi.imp psi).IsDelta0 <-> (phi.IsDelta0 ∧ psi.IsDelta0) :=
by
  constructor
  · intro h
    cases h with
    | imp p q =>
      exact ⟨p, q⟩
    | of_isQF q =>
      rw [IsQF.imp.mpr] at q
      constructor <;>
        apply IsDelta0.of_isQF
      · exact q.left
      · exact q.right
    | bdEx phi t =>
      cases h with
      | of_isAtomic h' =>
        cases h' with
  · intro h
    exact IsDelta0.imp h.left h.right


-- @@ L301-301 verbatim
end of_open


-- @@ L303-303 verbatim
namespace of_notfalsum


-- @@ L305-322 verbatim
theorem imp {a n} {phi psi : L.BoundedFormula a n} (h : psi ≠ falsum)
  : (phi.imp psi).IsDelta0 <-> (phi.IsDelta0 ∧ psi.IsDelta0) :=
by
  constructor
  · intro h'
    cases h' with
    | imp p q =>
      exact ⟨p, q⟩
    | of_isQF q =>
      rw [IsQF.imp.mpr] at q
      constructor <;>
        apply IsDelta0.of_isQF
      · exact q.left
      · exact q.right
    | bdEx phi t =>
      simp only [Bot.bot, ne_eq, not_true_eq_false] at h
  · intro h
    exact IsDelta0.imp h.left h.right


-- @@ L324-324 verbatim
end of_notfalsum



-- @@ L327-333 expanded
@[delta0_simps]
theorem neq {a n} (t1 t2 : L.Term (a ⊕ Fin n)) : (Term.neq t1 t2).IsDelta0 :=
  by
  constructor
  · apply equal
  · apply bot


-- @@ L335-335 verbatim
namespace of_open


-- @@ L337-342 verbatim
theorem not {a n} {phi : L.BoundedFormula a n} (h : phi.IsOpen)
  : phi.not.IsDelta0 <-> phi.IsDelta0 :=
by
  unfold BoundedFormula.not
  rw [of_open.imp h]
  exact ⟨fun h => h.left, fun h => ⟨h, IsDelta0.bot⟩⟩


-- @@ L344-344 verbatim
end of_open


-- @@ L346-346 verbatim
namespace relabelEquiv


-- @@ L348-368 verbatim
theorem mpAux {a b n} {phi : peano.BoundedFormula a n}
  (g : a ≃ b)
  (h : phi.IsDelta0)
  : (phi.relabelEquiv g).IsDelta0 :=
by
  induction h generalizing b with
  | bdEx t hphi ih =>
    rw [iBdEx'.relabelEquiv]
    constructor
    exact ih (g.sumCongr (_root_.Equiv.refl _))
  | bdAll t hphi ih =>
    rw [iBdAll'.relabelEquiv]
    constructor
    exact ih (g.sumCongr (_root_.Equiv.refl _))
  | imp pre post ihpre ihpost =>
    rw [relabelEquiv.imp]
    constructor
    · exact ihpre g
    · exact ihpost g
  | of_isQF f =>
    exact IsDelta0.of_isQF (BoundedFormula.IsQF.relabelEquiv.mp g f)


-- @@ L370-376 verbatim
theorem gSumCongr
  {a b c}
  {phi : peano.Formula (a ⊕ c)}
  (g : a ≃ b)
  (h : phi.IsDelta0)
  : ((relabelEquiv (g.sumCongr (_root_.Equiv.refl c))) phi).IsDelta0 :=
  relabelEquiv.mpAux (g.sumCongr (_root_.Equiv.refl c)) h



-- @@ L379-384 verbatim
@[delta0_simps]
theorem mp {a b} {phi : peano.Formula a}
  (g : a ≃ b)
  (h : phi.IsDelta0)
  : (phi.relabelEquiv g).IsDelta0 :=
  relabelEquiv.mpAux g h



-- @@ L387-395 verbatim
@[delta0_simps]
theorem mpr {α β} {φ : peano.Formula α} (f : α ≃ β)
  (h : (φ.relabelEquiv f).IsDelta0)
  : φ.IsDelta0 :=
by
  have h' : relabelEquiv f.symm ((relabelEquiv f) φ) = φ := relabelEquiv.comp_inv f
  rw [<- h']
  apply relabelEquiv.mp
  exact h


-- @@ L397-397 verbatim
end relabelEquiv


-- @@ L399-402 verbatim
@[delta0_simps]
theorem relabelEquiv {α β} (φ : peano.Formula α) {f : α ≃ β} :
  (φ.relabelEquiv f).IsDelta0 <-> φ.IsDelta0 :=
  ⟨IsDelta0.relabelEquiv.mpr f, IsDelta0.relabelEquiv.mp f⟩



-- @@ L405-408 verbatim
@[delta0_simps]
theorem display1 {n} (phi : peano.Formula (Vars1 n)) :
  phi.display1.IsDelta0 <-> phi.IsDelta0 :=
  IsDelta0.relabelEquiv phi


-- @@ L410-413 verbatim
@[delta0_simps]
theorem display2 {n1 n2} (phi : peano.Formula (Vars2 n1 n2)) :
  phi.display2.IsDelta0 <-> phi.IsDelta0 :=
  IsDelta0.relabelEquiv phi


-- @@ L415-418 verbatim
@[delta0_simps]
theorem display3 {n1 n2 n3} (phi : peano.Formula (Vars3 n1 n2 n3)) :
  phi.display3.IsDelta0 <-> phi.IsDelta0 :=
  IsDelta0.relabelEquiv phi


-- @@ L420-423 verbatim
@[delta0_simps]
theorem flip {a b} (phi : peano.Formula (a ⊕ b)) :
  phi.flip.IsDelta0 <-> phi.IsDelta0 :=
  IsDelta0.relabelEquiv phi


-- @@ L425-431 verbatim
end IsDelta0




-- only bounded number quantifiers allowed. and free string vars.
-- p. 82 of pdf of Logical Foundatoin release

-- @@ L432-432 verbatim
namespace BoundedFormula


-- @@ L434-457 verbatim
/-- Sigma-zero-B formulas in the two-sorted Zambella language. -/
inductive IsSigma0B {a : Type} :
    {n : Nat} -> zambella.BoundedFormula a n -> Prop
| imp {phi1 phi2} (h1 : IsSigma0B phi1) (h2 : IsSigma0B phi2)
  : IsSigma0B (phi1.imp phi2)
| bdEx
  {n : FvName}
  (phi : zambella.Formula (a ⊕ (Vars1 n)))
  (t : zambella.Term (a ⊕ Fin 0))
  : IsSigma0B <| iBdEx' t
      ((rel ZambellaRel.isnum ![var <| Sum.inl <| Sum.inr <| .fv1]) ⊓ phi)
-- TODO: WHICH ONE IS REDUNDANT?
| bdAll
  {n : FvName}
  (phi : zambella.Formula (a ⊕ (Vars1 n)))
  (t : zambella.Term (a ⊕ Fin 0))
  : IsSigma0B <| iBdAllNum' t phi
| bdAllLt
  {n : FvName}
  (phi : zambella.Formula (a ⊕ (Vars1 n)))
  (t : zambella.Term (a ⊕ Fin 0))
  : IsSigma0B <| iBdAllLt' t
      ((rel ZambellaRel.isnum ![var <| Sum.inl <| Sum.inr <| .fv1]) ⊓ phi)
| of_isQF {phi} (h : IsQF phi) : IsSigma0B phi


-- @@ L459-459 verbatim
end BoundedFormula


-- @@ L461-461 verbatim
namespace Sigma0B


-- @@ L463-463 verbatim
namespace relabelEquiv


-- @@ L465-510 verbatim
theorem mpAux {a b n} {phi : zambella.BoundedFormula a n}
  (g : a ≃ b)
  (h : phi.IsSigma0B)
  : (phi.relabelEquiv g).IsSigma0B :=
by
  induction h generalizing b with
  | imp h1 h2 ih1 ih2 =>
    rw [relabelEquiv.imp]
    exact BoundedFormula.IsSigma0B.imp (ih1 g) (ih2 g)
  | bdEx phi t =>
    rw [iBdEx'.relabelEquiv]
    convert BoundedFormula.IsSigma0B.bdEx
      (phi.relabelEquiv (g.sumCongr (_root_.Equiv.refl _)))
      (Term.relabelEquiv (g.sumCongr (_root_.Equiv.refl _)) t) using 1
    simp only [Term.relabelEquiv_apply, relabelEquiv.nf, relabelEquiv.rel,
      Matrix.cons_val_fin_one, Term.relabel.eq_1, Sum.map_inl, Equiv.sumCongr_apply,
      Equiv.coe_refl, Sum.map_inr, id_eq]
    congr
    funext i
    simp_all
  | bdAll phi t =>
    unfold iBdAllNum'
    rw [iBdAll'.relabelEquiv]
    convert BoundedFormula.IsSigma0B.bdAll
      (phi.relabelEquiv (g.sumCongr (_root_.Equiv.refl _)))
      (Term.relabelEquiv (g.sumCongr (_root_.Equiv.refl _)) t) using 1
    unfold Term.IsNum Relations.boundedFormula₁ Relations.boundedFormula
    rw [relabelEquiv.imp]
    congr
    rw [relabelEquiv.rel]
    congr
    funext i
    simp_all
  | bdAllLt phi t =>
    rw [iBdAllLt'.relabelEquiv]
    convert BoundedFormula.IsSigma0B.bdAllLt
      (phi.relabelEquiv (g.sumCongr (_root_.Equiv.refl _)))
      (Term.relabelEquiv (g.sumCongr (_root_.Equiv.refl _)) t) using 1
    simp only [Term.relabelEquiv_apply, relabelEquiv.nf, relabelEquiv.rel,
      Matrix.cons_val_fin_one, Term.relabel.eq_1, Sum.map_inl, Equiv.sumCongr_apply,
      Equiv.coe_refl, Sum.map_inr, id_eq]
    congr
    funext i
    simp_all
  | of_isQF h =>
    exact BoundedFormula.IsSigma0B.of_isQF (BoundedFormula.IsQF.relabelEquiv.mp g h)


-- @@ L512-519 verbatim
theorem mprAux {a b n} {phi : zambella.BoundedFormula a n}
  (g : a ≃ b)
  (h : (phi.relabelEquiv g).IsSigma0B)
  : phi.IsSigma0B :=
by
  have h' : relabelEquiv g.symm ((relabelEquiv g) phi) = phi := relabelEquiv.comp_inv g
  rw [<- h']
  exact relabelEquiv.mpAux g.symm h


-- @@ L521-521 verbatim
end relabelEquiv


-- @@ L523-526 verbatim
@[delta0_simps]
theorem relabelEquiv {a b} {g : a ≃ b} (phi : zambella.Formula a) :
  (phi.relabelEquiv g).IsSigma0B <-> phi.IsSigma0B :=
  ⟨relabelEquiv.mprAux g, relabelEquiv.mpAux g⟩


-- @@ L528-530 verbatim
/-- Discharge a `Sigma0B` closure lemma for a `Formula.*` reshaping. -/
macro "sigma0bViaRelabel " target:ident : tactic =>
  `(tactic| (unfold $target; apply relabelEquiv))


-- @@ L532-538 expanded
@[delta0_simps]
nonrec theorem display1 {n1 : FvName} (phi : zambella.Formula (Vars1 n1)) :
    phi.display1.IsSigma0B <-> phi.IsSigma0B := by (unfold display1; apply relabelEquiv)


-- @@ L540-546 expanded
@[delta0_simps]
nonrec theorem display2 {n1 n2 : FvName} (phi : zambella.Formula (Vars2 n1 n2)) :
    phi.display2.IsSigma0B <-> phi.IsSigma0B := by (unfold display2; apply relabelEquiv)


-- @@ L548-554 expanded
@[delta0_simps]
nonrec theorem display3 {n1 n2 n3 : FvName} (phi : zambella.Formula (Vars3 n1 n2 n3)) :
    phi.display3.IsSigma0B <-> phi.IsSigma0B := by (unfold display3; apply relabelEquiv)


-- @@ L556-562 expanded
@[delta0_simps]
nonrec theorem display4 {n1 n2 n3 n4 : FvName} (phi : zambella.Formula (Vars4 n1 n2 n3 n4)) :
    phi.display4.IsSigma0B <-> phi.IsSigma0B := by (unfold display4; apply relabelEquiv)


-- @@ L564-570 expanded
@[delta0_simps]
nonrec theorem displaySwapleft {n1 n2 n3 : FvName}
    (phi : zambella.Formula (Vars1 n1 ⊕ Vars2 n2 n3)) :
    phi.displaySwapleft.IsSigma0B <-> phi.IsSigma0B := by
  (unfold displaySwapleft; apply relabelEquiv)


-- @@ L572-578 expanded
@[delta0_simps]
nonrec theorem displaySwapleft' {n1 n2 n3 : FvName}
    (phi : zambella.Formula (Vars1 n1 ⊕ Vars2 n2 n3)) :
    phi.displaySwapleft'.IsSigma0B <-> phi.IsSigma0B := by
  (unfold displaySwapleft'; apply relabelEquiv)


-- @@ L580-586 expanded
@[delta0_simps]
nonrec theorem rotate21 {n1 n2 : FvName} (phi : zambella.Formula (Vars2 n1 n2)) :
    phi.rotate21.IsSigma0B <-> phi.IsSigma0B := by (unfold rotate21; apply relabelEquiv)


-- @@ L588-594 expanded
@[delta0_simps]
nonrec theorem rotate213 {n1 n2 n3 : FvName} (phi : zambella.Formula (Vars3 n1 n2 n3)) :
    phi.rotate213.IsSigma0B <-> phi.IsSigma0B := by (unfold rotate213; apply relabelEquiv)


-- @@ L596-602 expanded
@[delta0_simps]
nonrec theorem rotate231 {n1 n2 n3 : FvName} (phi : zambella.Formula (Vars3 n1 n2 n3)) :
    phi.rotate231.IsSigma0B <-> phi.IsSigma0B := by (unfold rotate231; apply relabelEquiv)


-- @@ L604-610 expanded
@[delta0_simps]
nonrec theorem flip {a b} (phi : zambella.Formula (a ⊕ b)) : phi.flip.IsSigma0B <-> phi.IsSigma0B :=
  by (unfold Formula.flip; apply relabelEquiv)


-- @@ L612-612 verbatim
end Sigma0B


-- @@ L614-615 verbatim
/-- Simplify complexity side conditions in a hypothesis. -/
syntax (name := simpComplexity) "simpComplexity" " at " (ppSpace ident)? : tactic


-- @@ L617-626 verbatim
macro_rules
| `(tactic| simpComplexity at $h:ident) =>
  `(tactic|
  conv at $h =>
    conv =>
      lhs
      simp only [delta0_simps]
    -- this has to work! the `IsOpen` goal has to reduce to `True`.
    rw [forall_const]
  )



-- @@ L629-629 verbatim
end FirstOrder.Language
