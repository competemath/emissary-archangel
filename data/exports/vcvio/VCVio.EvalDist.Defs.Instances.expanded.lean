/-
Copyright (c) 2025 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module
public import VCVio.EvalDist.Monad.Basic


-- @@ L10-14 verbatim
/-!
# Monad Evaluation Semantics Instances

This file defines various instances of evaluation semantics for different monads
-/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
universe u v w


-- @@ L20-20 verbatim
variable {α β γ : Type u}


-- @@ L22-22 verbatim
namespace SetM


-- @@ L24-25 verbatim
@[simp, grind =]
lemma support_eq_run (s : SetM α) : support s = s.run := rfl


-- @@ L27-27 verbatim
end SetM


-- @@ L29-29 verbatim
namespace SPMF


-- @@ L31-32 verbatim
@[simp, grind =]
protected lemma evalSPMF_def (p : SPMF α) : evalSPMF p = p := rfl


-- @@ L34-35 verbatim
@[grind =]
protected lemma support_eq_support (p : SPMF α) : support p = SPMF.support p := rfl


-- @@ L37-39 expanded
@[grind =]
lemma probOutput_eq_apply (p : SPMF α) (x : α) : probOutput p x = p x :=
  probOutput_def p x


-- @@ L41-43 expanded
lemma evalSPMF_eq_iff {m} [Monad m] [MonadLiftT m SPMF] (mx : m α) (p : SPMF α) :
    evalSPMF mx = p ↔ ∀ x, probOutput mx x = p x := by simp only [probOutput_def, DFunLike.ext_iff]


-- @@ L45-45 verbatim
end SPMF


-- @@ L47-47 verbatim
namespace PMF


-- @@ L49-49 verbatim
@[simp] lemma evalSPMF_eq (p : PMF α) : evalSPMF p = liftM p := rfl


-- @@ L51-52 expanded
@[simp]
lemma probOutput_eq_apply (p : PMF α) (x : α) : probOutput p x = p x := by simp [probOutput_def]


-- @@ L54-54 verbatim
end PMF


-- @@ L56-57 expanded
@[simp]
lemma SPMF.evalSPMF_liftM (p : PMF α) : evalSPMF (m := SPMF) (liftM p) = evalSPMF p :=
  rfl


-- @@ L59-60 expanded
@[simp]
lemma SPMF.probOutput_liftM (p : PMF α) (x : α) :
    probOutput (liftM p : SPMF α) x = probOutput p x :=
  rfl


-- @@ L62-63 expanded
@[simp]
lemma SPMF.probEvent_liftM (p : PMF α) (e : α → Prop) :
    probEvent (liftM p : SPMF α) e = probEvent p e :=
  rfl


-- @@ L65-66 expanded
@[simp]
lemma SPMF.probFailure_liftM (p : PMF α) : probFailure (liftM p : SPMF α) = probFailure p :=
  rfl


-- @@ L68-68 verbatim
namespace Id


-- @@ L70-72 verbatim
/-- Lift `Id` into `PMF` (a `pure` of the result), giving `Id` the canonical total denotation. -/
noncomputable instance : MonadLift Id PMF where
  monadLift x := pure x.run


-- @@ L74-78 verbatim
noncomputable instance : LawfulMonadLift Id PMF where
  monadLift_pure _ := rfl
  monadLift_bind _ _ := by
    change (PMF.pure _ : PMF _) = (pure _ : PMF _).bind fun x => pure _
    simp


-- @@ L80-86 verbatim
instance : HasEvalFinset Id where
  finSupport x := {x}
  coe_finSupport x := by
    ext y
    change y ∈ (↑({x.run} : Finset _) : Set _) ↔ y ∈ SetM.run (pure x.run : SetM _)
    rw [Finset.coe_singleton]
    rfl


-- @@ L88-89 verbatim
@[simp, grind =]
lemma support_eq_singleton (x : Id α) : support x = {x.run} := rfl


-- @@ L91-92 verbatim
@[simp, grind =]
lemma finSupport_eq_singleton [DecidableEq α] (x : Id α) : finSupport x = {x.run} := rfl


-- @@ L94-98 expanded
@[simp, grind =]
lemma probOutput_eq_ite [DecidableEq α] (x : Id α) (y : α) :
    probOutput x y = if y = x.run then 1 else 0 :=
  by
  rw [← Id.pure_run x, probOutput_pure]
  rfl


-- @@ L100-104 expanded
@[simp, grind =]
lemma probEvent_eq_ite (x : Id α) (p : α → Prop) [DecidablePred p] :
    probEvent x p = if p x.run then 1 else 0 :=
  by
  rw [← Id.pure_run x, probEvent_pure]
  rfl


-- @@ L106-106 expanded
lemma probFailure_eq_zero (x : Id α) : probFailure x = 0 :=
  probFailure_pure _


-- @@ L108-108 verbatim
end Id
