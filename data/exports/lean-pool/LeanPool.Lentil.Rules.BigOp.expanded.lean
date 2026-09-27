/-
Copyright (c) 2026 Qiyuan Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qiyuan Zhao
-/
module

public import LeanPool.Lentil.Tactics.Basic
import Aesop.Frontend.Tactic
import Aesop.Main
import LeanPool.Lentil.Rules.Basic
import LeanPool.Lentil.Util
import LeanPool.Lentil.Utils.MiscLemmas
import Std.Tactic.BVDecide.Normalize.Prop


-- @@ L16-16 verbatim
/-! Theorems about big operators (e.g., `⋀`, `⋁`). -/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
open Classical LentilLib


-- @@ L22-22 verbatim
namespace TLA


-- @@ L24-24 verbatim
section bigop


-- @@ L26-31 verbatim
variable {α : Type u} {β : Type v} (f g : β → pred α) (l : List β)

-- FIXME: currently we only have the definition of `fold`, but we do not specify
-- its result, so for each `Foldable` instance, we need to repeat the following proofs!
-- maybe we should revise the definitions of `bigwedge` and `bigvee` (see `Lentil/Basic.lean`)
-- also, can we get rid of the repetition?


-- @@ L33-33 verbatim
section bigwedge


-- @@ L35-36 expanded
@[tlasimp]
theorem bigwedge_list_nil : TLA.tlaBigwedge (fun x => (f x)) [] = TLA.tlaTrue :=
  rfl


-- @@ L38-39 expanded
@[tlasimp]
theorem bigwedge_list_cons (b : β) :
    TLA.tlaBigwedge (fun x => (f x)) (b :: l) =
      TLA.tlaAnd (f b) (TLA.tlaBigwedge (fun x => (f x)) l) :=
  rfl


-- @@ L41-50 expanded
@[tlasimp]
theorem bigwedge_list_append (l1 l2 : List β) :
    TLA.tlaBigwedge (fun x => (f x)) (l1 ++ l2) =
      TLA.tlaAnd (TLA.tlaBigwedge (fun x => (f x)) l1) (TLA.tlaBigwedge (fun x => (f x)) l2) :=
  by
  simp only [tlaBigwedge, Foldable.fold, List.foldr_append]
  simp only [← List.foldr_map]
  generalize (l1.map f) = l1'; clear l1
  generalize (List.foldr tlaAnd TLA.tlaTrue (List.map f l2)) = p; clear l2
  induction l1' with
  | nil => simp [true_and]
  | cons b l1' ih => simp [and_assoc, ih]


-- @@ L52-57 expanded
theorem bigwedge_forall_list :
    TLA.tlaBigwedge (fun x => (f x)) l =
      TLA.tlaForall fun x => TLA.tlaImplies (TLA.purePred (x ∈ l)) (f x) :=
  by
  induction l with
  | nil => funext e; (simp [tlasimp_def] at *)
  | cons b l ih =>
    simp [tlasimp, ih]
    funext e; (simp [tlasimp_def] at *)


-- @@ L59-61 expanded
theorem bigwedge_forall_fintype_list :
    TLA.tlaBigwedge (fun x => (f x)) l = TLA.tlaForall fun x : Fin l.length => (f l[x]) :=
  by
  rw [bigwedge_forall_list]
  funext e; (simp [tlasimp_def] at *); apply List.mem_forall_iff_fin_index


-- @@ L63-65 expanded
omit f in
theorem bigwedge_forall_swap {γ : Type w} (f : β → γ → pred α) :
    (TLA.tlaForall fun c : γ => TLA.tlaBigwedge (fun x => (f x c)) l) =
      TLA.tlaBigwedge (fun x => TLA.tlaForall fun c : γ => (f x c)) l :=
  by simp only [bigwedge_forall_fintype_list]; apply TLA.forall_comm


-- @@ L67-68 expanded
theorem bigwedge_inner_and_split :
    TLA.tlaBigwedge (fun x => TLA.tlaAnd (f x) (g x)) l =
      TLA.tlaAnd (TLA.tlaBigwedge (fun x => (f x)) l) (TLA.tlaBigwedge (fun x => (g x)) l) :=
  by (repeat rw [bigwedge_forall_list]); funext e; (simp [tlasimp_def] at *); aesop


-- @@ L70-71 expanded
theorem always_bigwedge :
    TLA.always (TLA.tlaBigwedge (fun x => (f x)) l) =
      TLA.tlaBigwedge (fun x => TLA.always (f x)) l :=
  by (repeat rw [bigwedge_forall_list]); funext e; (simp [tlasimp_def] at *); aesop


-- @@ L73-76 expanded
theorem eventually_always_bigwedge_distrib :
    TLA.eventually (TLA.always (TLA.tlaBigwedge (fun x => (f x)) l)) =
      TLA.tlaBigwedge (fun x => TLA.eventually (TLA.always (f x))) l :=
  by
  induction l with
  | nil => funext e; (simp [tlasimp_def] at *)
  | cons x l ih => simp [tlasimp, eventually_always_and_distrib, ih]


-- @@ L78-78 verbatim
end bigwedge


-- @@ L80-80 verbatim
section bigvee


-- @@ L82-83 expanded
@[tlasimp]
theorem bigvee_list_nil : TLA.tlaBigvee (fun x => (f x)) [] = TLA.tlaFalse :=
  rfl


-- @@ L85-86 expanded
@[tlasimp]
theorem bigvee_list_cons (b : β) :
    TLA.tlaBigvee (fun x => (f x)) (b :: l) = TLA.tlaOr (f b) (TLA.tlaBigvee (fun x => (f x)) l) :=
  rfl


-- @@ L88-93 expanded
theorem bigvee_exists_list :
    TLA.tlaBigvee (fun x => (f x)) l =
      TLA.tlaExists fun x => TLA.tlaAnd (TLA.purePred (x ∈ l)) (f x) :=
  by
  induction l with
  | nil => funext e; (simp [tlasimp_def] at *)
  | cons b l ih =>
    simp [tlasimp, ih]
    funext e; (simp [tlasimp_def] at *)


-- @@ L95-97 expanded
theorem bigvee_exists_fintype_list :
    TLA.tlaBigvee (fun x => (f x)) l = TLA.tlaExists fun x : Fin l.length => (f l[x]) :=
  by
  rw [bigvee_exists_list]
  funext e; (simp [tlasimp_def] at *); apply List.mem_exists_iff_fin_index


-- @@ L99-101 expanded
theorem bigvee_and_distrib (p : pred α) :
    TLA.tlaAnd p (TLA.tlaBigvee (fun x => (f x)) l) =
      TLA.tlaBigvee (fun x => TLA.tlaAnd p (f x)) l :=
  by
  repeat rw [bigvee_exists_list]
  funext e; (simp [tlasimp_def] at *); aesop


-- @@ L103-103 verbatim
end bigvee


-- @@ L105-106 expanded
theorem bigwedge_bigvee_match :
    TLA.predImplies
      (TLA.tlaAnd (TLA.tlaBigwedge (fun x => (f x)) l) (TLA.tlaBigvee (fun x => (g x)) l))
      (TLA.tlaBigvee (fun x => TLA.tlaAnd (f x) (g x)) l) :=
  by rw [bigwedge_forall_list, bigvee_exists_list, bigvee_exists_list]; (simp [tlasimp_def] at *);
  aesop


-- @@ L108-108 verbatim
end bigop


-- @@ L110-110 verbatim
end TLA
