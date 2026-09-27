/-
Copyright (c) 2026 ruplet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ruplet
-/
module


public import LeanPool.FormalizationOfBoundedArithmetic.Syntax
public import LeanPool.FormalizationOfBoundedArithmetic.LanguageZambella
import Mathlib.Tactic.FinCases


-- @@ L13-15 verbatim
/-!
# LeanPool.FormalizationOfBoundedArithmetic.Order
-/


-- @@ L17-17 verbatim
@[expose] public section


-- @@ L19-19 verbatim
namespace FirstOrder.Language.Formula


-- @@ L21-21 verbatim
open Language BoundedFormula


-- @@ L23-23 verbatim
section IsOrdered

-- @@ L24-24 verbatim
universe u

-- @@ L25-25 verbatim
variable {L : Language} [IsOrdered L] {α : Type u}


-- @@ L27-27 verbatim
variable {n r} (a b : L.BoundedFormula n r)



-- @@ L30-34 verbatim
/-- Existential quantification bounded by a term. -/
def iBdEx' {α n} (bdTerm : L.Term (α ⊕ Fin 0))
    (φ : L.Formula (α ⊕ (Vars1 n))) : L.Formula α :=
  let bd := (var (.inl (Sum.inr (.fv1)))).le <| bdTerm.relabel (Sum.map .inl id)
  iExs' <| bd ⊓ φ


-- @@ L36-43 verbatim
/-- Universal quantification bounded by a term. -/
def iBdAll' {α n} (bdTerm : L.Term (α ⊕ Fin 0))
    (φ : L.Formula (α ⊕ (Vars1 n))) : L.Formula α :=
  let bd := (var (.inl (Sum.inr (.fv1)))).le <| bdTerm.relabel (Sum.map .inl id)
  iAlls' <| bd ⟹ φ

-- TODO: there should only be Lt constructors in Complexity
-- and iBd should be an alias to iBdLt with term + 1

-- @@ L44-48 verbatim
/-- Universal quantification bounded strictly by a term. -/
def iBdAllLt' {α n} (bdTerm : L.Term (α ⊕ Fin 0))
    (φ : L.Formula (α ⊕ (Vars1 n))) : L.Formula α :=
  let bd := (var (.inl (Sum.inr (.fv1)))).lt <| bdTerm.relabel (Sum.map .inl id)
  iAlls' <| bd ⟹ φ


-- @@ L50-56 verbatim
/-- Existential quantification bounded by a term and guarded as numeric. -/
def iBdExNum'
  {α n}
  (bdTerm : zambella.Term (α ⊕ Fin 0))
  (φ : zambella.Formula (α ⊕ (Vars1 n)))
  : zambella.Formula α :=
  iBdEx' bdTerm <| (var <| Sum.inl <| Sum.inr <| .fv1).IsNum ⊓ φ


-- @@ L58-64 verbatim
/-- Existential quantification bounded by a term and guarded as a string. -/
def iBdExStr'
  {α n}
  (bdTerm : zambella.Term (α ⊕ Fin 0))
  (φ : zambella.Formula (α ⊕ (Vars1 n)))
  : zambella.Formula α :=
  iBdEx' bdTerm <| (var <| Sum.inl <| Sum.inr <| .fv1).IsStr ⊓ φ


-- @@ L66-72 verbatim
/-- Universal quantification bounded by a term and guarded as numeric. -/
def iBdAllNum'
  {α n}
  (bdTerm : zambella.Term (α ⊕ Fin 0))
  (φ : zambella.Formula (α ⊕ (Vars1 n)))
  : zambella.Formula α :=
  iBdAll' bdTerm <| (var <| Sum.inl <| Sum.inr <| .fv1).IsNum ⟹ φ


-- @@ L74-80 verbatim
/-- Universal quantification strictly bounded by a term and guarded as numeric. -/
def iBdAllNumLt'
  {α n}
  (bdTerm : zambella.Term (α ⊕ Fin 0))
  (φ : zambella.Formula (α ⊕ (Vars1 n)))
  : zambella.Formula α :=
  iBdAllLt' bdTerm <| (var <| Sum.inl <| Sum.inr <| .fv1).IsNum ⟹ φ




-- @@ L84-84 verbatim
open Lean Elab Tactic


-- @@ L86-100 verbatim
/-- Discharge the `Term.le` bound-comparison subgoal shared by the
`iBdEx'`/`iBdAll'` `relabelEquiv` congruence proofs. -/
macro "relabelTermLeCongr" : tactic =>
  `(tactic| (
    unfold Term.le Relations.boundedFormula₂ Relations.boundedFormula
    rw [relabelEquiv.rel]
    congr
    funext x
    simp only [Term.relabelEquiv_apply, Term.relabel_relabel]
    fin_cases x
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Term.relabel.eq_1, Sum.map_inl,
        Equiv.sumCongr_apply, Equiv.coe_refl, Sum.map_inr, id_eq]
    · simp [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Term.relabel_relabel, Sum.map_comp_map, Function.comp_id, Equiv.sumCongr]
      congr 1))


-- @@ L102-102 verbatim
namespace iBdEx'


-- @@ L104-117 expanded
theorem relabelEquiv {α β n} (bdTerm : L.Term (α ⊕ Fin 0)) (φ : L.Formula (α ⊕ (Vars1 n)))
    (f : α ≃ β) :
    relabelEquiv f (iBdEx' bdTerm φ) =
      iBdEx' (Term.relabelEquiv (f.sumCongr (_root_.Equiv.refl (Fin 0))) bdTerm)
        (relabelEquiv (f.sumCongr (_root_.Equiv.refl (Vars1 n))) φ) :=
  by
  unfold iBdEx'
  rw [relabelEquiv.iExs']
  congr
  rw [relabelEquiv.inf]
  congr
  · ( unfold Term.le Relations.boundedFormula₂ Relations.boundedFormula
      rw [relabelEquiv.rel]
      congr
      funext x
      simp only [Term.relabelEquiv_apply, Term.relabel_relabel]
      fin_cases x
      ·
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Term.relabel.eq_1, Sum.map_inl,
          Equiv.sumCongr_apply, Equiv.coe_refl, Sum.map_inr, id_eq]
      · simp [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Term.relabel_relabel,
          Sum.map_comp_map, Function.comp_id, Equiv.sumCongr]
        congr 1)


-- @@ L119-119 verbatim
end iBdEx'


-- @@ L121-121 verbatim
namespace iBdAll'


-- @@ L123-136 expanded
theorem relabelEquiv {α β n} (bdTerm : L.Term (α ⊕ Fin 0)) (φ : L.Formula (α ⊕ (Vars1 n)))
    (f : α ≃ β) :
    relabelEquiv f (iBdAll' bdTerm φ) =
      iBdAll' (Term.relabelEquiv (f.sumCongr (_root_.Equiv.refl (Fin 0))) bdTerm)
        (relabelEquiv (f.sumCongr (_root_.Equiv.refl (Vars1 n))) φ) :=
  by
  unfold iBdAll'
  rw [relabelEquiv.iAlls']
  congr
  rw [relabelEquiv.imp]
  congr
  · ( unfold Term.le Relations.boundedFormula₂ Relations.boundedFormula
      rw [relabelEquiv.rel]
      congr
      funext x
      simp only [Term.relabelEquiv_apply, Term.relabel_relabel]
      fin_cases x
      ·
        simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Term.relabel.eq_1, Sum.map_inl,
          Equiv.sumCongr_apply, Equiv.coe_refl, Sum.map_inr, id_eq]
      · simp [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one, Term.relabel_relabel,
          Sum.map_comp_map, Function.comp_id, Equiv.sumCongr]
        congr 1)


-- @@ L138-138 verbatim
end iBdAll'


-- @@ L140-140 verbatim
namespace iBdAllLt'


-- @@ L142-177 verbatim
theorem relabelEquiv
  {α β n} (bdTerm : L.Term (α ⊕ Fin 0)) (φ : L.Formula (α ⊕ (Vars1 n)))
  (f : α ≃ β)
  : relabelEquiv f (iBdAllLt' bdTerm φ)
    = iBdAllLt'
        (Term.relabelEquiv (f.sumCongr (_root_.Equiv.refl (Fin 0))) bdTerm)
        (relabelEquiv (f.sumCongr (_root_.Equiv.refl (Vars1 n))) φ) :=
by
  unfold iBdAllLt'
  rw [relabelEquiv.iAlls']
  congr
  rw [relabelEquiv.imp]
  congr
  · unfold Term.lt
    rw [BoundedFormula.relabelEquiv.inf]
    congr
    · unfold Term.le Relations.boundedFormula₂ Relations.boundedFormula
      rw [BoundedFormula.relabelEquiv.rel]
      congr
      funext x
      simp only [Term.relabelEquiv_apply, Term.relabel_relabel]
      fin_cases x <;> simp [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.cons_val_zero, Term.relabel_relabel, Sum.map_comp_map,
        Function.comp_id, Equiv.sumCongr]
      congr 1
    · rw [BoundedFormula.relabelEquiv.not]
      congr
      unfold Term.le Relations.boundedFormula₂ Relations.boundedFormula
      rw [BoundedFormula.relabelEquiv.rel]
      congr
      funext x
      simp only [Term.relabelEquiv_apply, Term.relabel_relabel]
      fin_cases x <;> simp [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one,
        Matrix.cons_val_zero, Term.relabel_relabel, Sum.map_comp_map,
        Function.comp_id, Equiv.sumCongr]
      congr 1


-- @@ L179-179 verbatim
end iBdAllLt'


-- @@ L181-181 verbatim
end IsOrdered


-- @@ L183-183 verbatim
end FirstOrder.Language.Formula
