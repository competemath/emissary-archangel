/-
Copyright (c) 2026 Alfie Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies
-/
module

public import LeanPool.MisereGames.Form.Short
public import Mathlib.Order.Closure


-- @@ L11-13 verbatim
/-!
Misere combinatorial games.
-/


-- @@ L15-15 verbatim
namespace MisereGames


-- @@ L17-17 verbatim
universe u


-- @@ L19-19 verbatim
variable {G : Type (u + 1)} [Form G]


-- @@ L21-21 verbatim
open Form


-- @@ L23-23 verbatim
public section


-- @@ L25-29 expanded
/-- Closure under nonempty dicotic set construction inside an ambient predicate. -/
class ClosedUnderDicotic (IsAmbient : G → Prop) (A : G → Prop) where
  closed_dicotic (B C : Set G) [Small B] [Small C] (hB : ∀ b ∈ B, A b) (hC : ∀ c ∈ C, A c) :
    B.Nonempty →
      C.Nonempty →
        IsAmbient
            (OfSets.ofSets (Player.cases B C)
                (by
                  first
                  | done
                  | trivial
                  | assumption
                  | aesop
                  |
                    fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                      where `h` is a proof that sets are valid") :
              G) →
          A
            (OfSets.ofSets (Player.cases B C)
                (by
                  first
                  | done
                  | trivial
                  | assumption
                  | aesop
                  |
                    fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                      where `h` is a proof that sets are valid") :
              G)


-- @@ L31-33 verbatim
/-- Closure under nonempty dicotic construction in the long ambient space. -/
abbrev ClosedUnderLongDicotic (A : G → Prop) :=
  ClosedUnderDicotic IsLong A


-- @@ L35-37 verbatim
/-- Closure under nonempty dicotic construction in the short ambient space. -/
abbrev ClosedUnderShortDicotic (A : G → Prop) :=
  ClosedUnderDicotic IsShort A


-- @@ L39-40 verbatim
instance : ClosedUnderAdd (IsShort (G := G)) where
  has_add _ _ := Short.add


-- @@ L42-43 verbatim
instance : Hereditary (IsShort (G := G)) where
  has_option := Short.isOption


-- @@ L45-46 verbatim
instance : ClosedUnderDicotic (IsShort (G := G)) (IsShort (G := G)) where
  closed_dicotic _ _ _ _ _ _ _ _ hShort := hShort


-- @@ L48-48 verbatim
namespace Form.ClosedUnderAdd


-- @@ L50-56 verbatim
theorem sInf_closed {S : Set (G → Prop)}
    (hS : ∀ A ∈ S, ClosedUnderAdd A) : ClosedUnderAdd (sInf S) where
  has_add g h hg hh := by
    simp only [sInf_apply, iInf_Prop_eq] at hg hh ⊢
    intro P
    have : ClosedUnderAdd (fun x => P.1 x) := hS P P.2
    exact ClosedUnderAdd.has_add g h (hg P) (hh P)


-- @@ L58-64 verbatim
/--
The closure operator for finding the smallest additively closed set containing
the given set.
-/
noncomputable abbrev closureOperator : ClosureOperator (G → Prop) :=
  ClosureOperator.ofCompletePred (fun A : G → Prop => ClosedUnderAdd A) fun _ hS =>
    sInf_closed hS


-- @@ L66-70 verbatim
/--
The additive closure of a given set.
-/
noncomputable abbrev closure (A : G → Prop) : G → Prop :=
  closureOperator A


-- @@ L72-73 verbatim
theorem subset_closure (A : G → Prop) : A ≤ closure A :=
  closureOperator.le_closure A


-- @@ L75-76 verbatim
theorem mem_closure_of_mem {A : G → Prop} {g : G} (hg : A g) : closure A g :=
  subset_closure A g hg


-- @@ L78-80 verbatim
instance closure_closed (A : G → Prop) : ClosedUnderAdd (closure A) := by
  simpa only [ClosureOperator.ofCompletePred_isClosed] using
    (closureOperator (G := G)).isClosed_closure A


-- @@ L82-84 verbatim
theorem add_mem_closure {A : G → Prop} {g h : G}
    (hg : closure A g) (hh : closure A h) : closure A (g + h) :=
  ClosedUnderAdd.has_add g h hg hh


-- @@ L86-89 verbatim
theorem closure_min {A B : G → Prop} (hAB : A ≤ B) [ClosedUnderAdd B] :
    closure A ≤ B :=
  ClosureOperator.closure_min (c := closureOperator) hAB (by
    simp_all)


-- @@ L91-92 verbatim
theorem closure_le {A B : G → Prop} [ClosedUnderAdd B] : closure A ≤ B ↔ A ≤ B :=
  ⟨(subset_closure A).trans, fun h => closure_min h⟩


-- @@ L94-95 verbatim
theorem closure_mono {A B : G → Prop} (hAB : A ≤ B) : closure A ≤ closure B :=
  closure_min (hAB.trans (subset_closure B))


-- @@ L97-97 verbatim
end Form.ClosedUnderAdd


-- @@ L99-99 verbatim
namespace Form


-- @@ L101-101 verbatim
namespace Hereditary


-- @@ L103-109 verbatim
theorem sInf_closed {S : Set (G → Prop)}
    (hS : ∀ A ∈ S, Hereditary A) : Hereditary (sInf S) where
  has_option hg h := by
    simp only [sInf_apply, iInf_Prop_eq] at hg ⊢
    intro P
    have : Hereditary (fun x => P.1 x) := hS P P.2
    exact Hereditary.has_option (hg P) h


-- @@ L111-117 verbatim
/--
The closure operator for finding the smallest hereditary set containing the
given set.
-/
noncomputable abbrev closureOperator : ClosureOperator (G → Prop) :=
  ClosureOperator.ofCompletePred (fun A : G → Prop => Hereditary A) fun _ hS =>
    sInf_closed hS


-- @@ L119-123 verbatim
/--
The hereditary closure of a given set.
-/
noncomputable abbrev closure (A : G → Prop) : G → Prop :=
  closureOperator A


-- @@ L125-126 verbatim
theorem subset_closure (A : G → Prop) : A ≤ closure A :=
  closureOperator.le_closure A


-- @@ L128-129 verbatim
theorem mem_closure_of_mem {A : G → Prop} {g : G} (hg : A g) : closure A g :=
  subset_closure A g hg


-- @@ L131-133 verbatim
instance closure_closed (A : G → Prop) : Hereditary (closure A) := by
  simpa only [ClosureOperator.ofCompletePred_isClosed] using
    (closureOperator (G := G)).isClosed_closure A


-- @@ L135-137 verbatim
theorem has_option_mem_closure {A : G → Prop} {g g' : G}
    (hg : closure A g) (h : Moves.IsOption g' g) : closure A g' :=
  Hereditary.has_option hg h


-- @@ L139-142 verbatim
theorem closure_min {A B : G → Prop} (hAB : A ≤ B) [Hereditary B] :
    closure A ≤ B :=
  ClosureOperator.closure_min (c := closureOperator) hAB (by
    simp_all)


-- @@ L144-145 verbatim
theorem closure_le {A B : G → Prop} [Hereditary B] : closure A ≤ B ↔ A ≤ B :=
  ⟨(subset_closure A).trans, fun h => closure_min h⟩


-- @@ L147-148 verbatim
theorem closure_mono {A B : G → Prop} (hAB : A ≤ B) : closure A ≤ closure B :=
  closure_min (hAB.trans (subset_closure B))


-- @@ L150-150 verbatim
end Hereditary


-- @@ L152-152 verbatim
namespace ClosedUnderNeg


-- @@ L154-160 verbatim
theorem sInf_closed {S : Set (G → Prop)}
    (hS : ∀ A ∈ S, ClosedUnderNeg A) : ClosedUnderNeg (sInf S) where
  neg_of hg := by
    simp only [sInf_apply, iInf_Prop_eq] at hg ⊢
    intro P
    have : ClosedUnderNeg (fun x => P.1 x) := hS P P.2
    exact ClosedUnderNeg.neg_of (hg P)


-- @@ L162-168 verbatim
/--
The closure operator for finding the smallest conjugate closed set containing
the given set.
-/
noncomputable abbrev closureOperator : ClosureOperator (G → Prop) :=
  ClosureOperator.ofCompletePred (fun A : G → Prop => ClosedUnderNeg A) fun _ hS =>
    sInf_closed hS


-- @@ L170-174 verbatim
/--
The conjugate closure of a given set.
-/
noncomputable abbrev closure (A : G → Prop) : G → Prop :=
  closureOperator A


-- @@ L176-177 verbatim
theorem subset_closure (A : G → Prop) : A ≤ closure A :=
  closureOperator.le_closure A


-- @@ L179-180 verbatim
theorem mem_closure_of_mem {A : G → Prop} {g : G} (hg : A g) : closure A g :=
  subset_closure A g hg


-- @@ L182-184 verbatim
instance closure_closed (A : G → Prop) : ClosedUnderNeg (closure A) := by
  simpa only [ClosureOperator.ofCompletePred_isClosed] using
    (closureOperator (G := G)).isClosed_closure A


-- @@ L186-187 verbatim
theorem neg_mem_closure {A : G → Prop} {g : G} (hg : closure A g) : closure A (-g) :=
  ClosedUnderNeg.neg_of hg


-- @@ L189-192 verbatim
theorem closure_min {A B : G → Prop} (hAB : A ≤ B) [ClosedUnderNeg B] :
    closure A ≤ B :=
  ClosureOperator.closure_min (c := closureOperator) hAB (by
    simp_all)


-- @@ L194-195 verbatim
theorem closure_le {A B : G → Prop} [ClosedUnderNeg B] : closure A ≤ B ↔ A ≤ B :=
  ⟨(subset_closure A).trans, fun h => closure_min h⟩


-- @@ L197-198 verbatim
theorem closure_mono {A B : G → Prop} (hAB : A ≤ B) : closure A ≤ closure B :=
  closure_min (hAB.trans (subset_closure B))


-- @@ L200-200 verbatim
end ClosedUnderNeg


-- @@ L202-202 verbatim
end Form


-- @@ L204-204 verbatim
namespace ClosedUnderDicotic


-- @@ L206-214 verbatim
theorem sInf_closed (IsAmbient : G → Prop) {S : Set (G → Prop)}
    (hS : ∀ A ∈ S, ClosedUnderDicotic IsAmbient A) :
    ClosedUnderDicotic IsAmbient (sInf S) where
  closed_dicotic B C _ _ hB hC hBne hCne hAmbient := by
    simp only [sInf_apply, iInf_Prop_eq] at hB hC ⊢
    intro P
    have : ClosedUnderDicotic IsAmbient (fun x => P.1 x) := hS P P.2
    exact ClosedUnderDicotic.closed_dicotic B C
      (fun b hb => hB b hb P) (fun c hc => hC c hc P) hBne hCne hAmbient


-- @@ L216-223 verbatim
/--
The closure operator for finding the smallest dicotically closed set (given the
ambient context) containing the given set.
-/
noncomputable abbrev closureOperator (IsAmbient : G → Prop) : ClosureOperator (G → Prop) :=
  ClosureOperator.ofCompletePred
    (fun A : G → Prop => ClosedUnderDicotic IsAmbient A) fun _ hS =>
      sInf_closed IsAmbient hS


-- @@ L225-229 verbatim
/--
The dicotic closure (within the ambient context) of a given set.
-/
noncomputable abbrev closure (IsAmbient : G → Prop) (A : G → Prop) : G → Prop :=
  closureOperator IsAmbient A


-- @@ L231-233 verbatim
theorem subset_closure (IsAmbient : G → Prop) (A : G → Prop) :
    A ≤ closure IsAmbient A :=
  (closureOperator IsAmbient).le_closure A


-- @@ L235-237 verbatim
theorem mem_closure_of_mem {IsAmbient A : G → Prop} {g : G} (hg : A g) :
    closure IsAmbient A g :=
  subset_closure IsAmbient A g hg


-- @@ L239-242 verbatim
instance closure_closed (IsAmbient : G → Prop) (A : G → Prop) :
    ClosedUnderDicotic IsAmbient (closure IsAmbient A) := by
  simpa only [ClosureOperator.ofCompletePred_isClosed] using
    (closureOperator IsAmbient).isClosed_closure A


-- @@ L244-248 expanded
theorem dicotic_mem_closure {IsAmbient A : G → Prop} (B C : Set G) [Small B] [Small C]
    (hB : ∀ b ∈ B, closure IsAmbient A b) (hC : ∀ c ∈ C, closure IsAmbient A c) (hBne : B.Nonempty)
    (hCne : C.Nonempty)
    (hAmbient :
      IsAmbient
        (OfSets.ofSets (Player.cases B C)
            (by
              first
              | done
              | trivial
              | assumption
              | aesop
              |
                fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                  where `h` is a proof that sets are valid") :
          G)) :
    closure IsAmbient A
      (OfSets.ofSets (Player.cases B C)
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid") :
        G) :=
  ClosedUnderDicotic.closed_dicotic B C hB hC hBne hCne hAmbient


-- @@ L250-253 verbatim
theorem closure_min {IsAmbient A B : G → Prop} (hAB : A ≤ B)
    [ClosedUnderDicotic IsAmbient B] : closure IsAmbient A ≤ B :=
  ClosureOperator.closure_min (c := closureOperator IsAmbient) hAB (by
    simp_all)


-- @@ L255-257 verbatim
theorem closure_le {IsAmbient A B : G → Prop} [ClosedUnderDicotic IsAmbient B] :
    closure IsAmbient A ≤ B ↔ A ≤ B :=
  ⟨(subset_closure IsAmbient A).trans, fun h => closure_min h⟩


-- @@ L259-261 verbatim
theorem closure_mono {IsAmbient A B : G → Prop} (hAB : A ≤ B) :
    closure IsAmbient A ≤ closure IsAmbient B :=
  closure_min (hAB.trans (subset_closure IsAmbient B))


-- @@ L263-263 verbatim
end ClosedUnderDicotic


-- @@ L265-265 verbatim
end


-- @@ L267-267 verbatim
end MisereGames
