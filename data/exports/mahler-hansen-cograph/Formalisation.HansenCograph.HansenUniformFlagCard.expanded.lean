/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Formalisation.HansenCograph.HansenPortalFlagIntervals
import Formalisation.HansenCograph.HansenJoinPortalIntervals
import Formalisation.HansenCograph.HansenJoinPortalUpperIntervals
import Formalisation.HansenCograph.HansenFullFlagSingleton
import Formalisation.HansenCograph.UniformFlagCard


-- @@ L12-19 verbatim
/-!
# Uniform length of Hansen full flags

The portal recurrence needs the upper shuffle length to be determined by the
lower one.  This file proves the required purity statement directly at the
level of maximal-chain cardinalities, avoiding a separate global grading of
the intrinsic face lattice.
-/


-- @@ L21-21 verbatim
open Set SimpleGraph


-- @@ L23-23 verbatim
namespace HansenCograph


-- @@ L25-25 verbatim
universe u v


-- @@ L27-27 verbatim
namespace Flag


-- @@ L29-36 verbatim
/-- The set-based flag corresponding to a finite flag has the cardinality
of its carrier finset. -/
theorem card_finsetFlagEquiv
    {P : Type u} [PartialOrder P] [Fintype P] [DecidableEq P]
    (s : FinsetFlag P) :
    Nat.card (finsetFlagEquiv P s) = s.1.card := by
  change Nat.card {x // x ∈ (s.1 : Set P)} = s.1.card
  rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]


-- @@ L38-38 verbatim
end Flag


-- @@ L40-40 verbatim
namespace SingletonFace


-- @@ L42-46 verbatim
set_option maxRecDepth 100000 in
/-- Every maximal chain in the certified four-element singleton Hansen
face lattice has four elements. -/
theorem fullFlag_card_four :
    ∀ s : FullFlag, s.1.card = 4 := by decide


-- @@ L48-48 verbatim
end SingletonFace


-- @@ L50-50 verbatim
namespace UniformFlagCard


-- @@ L52-69 verbatim
/-- The one-vertex Hansen polygon has four faces in every full flag. -/
theorem hansenSingleton :
    UniformFlagCard
      (HansenCombinatorialFace (⊥ : SimpleGraph PUnit)) 4 := by
  intro t
  let mapped := Flag.map HansenCombinatorialFace.singletonFaceOrderIso t
  let finite : SingletonFace.FullFlag :=
    (finsetFlagEquiv (OrderDual SingletonFace.Closed)).symm mapped
  have hrecover :
      finsetFlagEquiv (OrderDual SingletonFace.Closed) finite = mapped :=
    (finsetFlagEquiv (OrderDual SingletonFace.Closed)).apply_symm_apply mapped
  calc
    Nat.card t = Nat.card mapped :=
      (Flag.card_map HansenCombinatorialFace.singletonFaceOrderIso t).symm
    _ = finite.1.card := by
      rw [← hrecover]
      exact Flag.card_finsetFlagEquiv finite
    _ = 4 := SingletonFace.fullFlag_card_four finite


-- @@ L71-80 verbatim
/-- Relabelling a graph preserves the common length of its Hansen full
flags. -/
theorem hansenIso
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) {r : ℕ}
    (hG : UniformFlagCard (HansenCombinatorialFace G) r) :
    UniformFlagCard (HansenCombinatorialFace H) r :=
  UniformFlagCard.orderIso (hansenFaceOrderIso e) hG


-- @@ L82-89 verbatim
/-- Hansen polarity preserves the common length of full flags. -/
theorem hansenCompl
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {r : ℕ}
    (hG : UniformFlagCard (HansenCombinatorialFace G) r) :
    UniformFlagCard (HansenCombinatorialFace Gᶜ) r :=
  UniformFlagCard.orderIso (hansenFaceComplOrderIso G)
    (UniformFlagCard.orderDual hG)


-- @@ L91-91 verbatim
end UniformFlagCard


-- @@ L93-93 verbatim
namespace HansenCombinatorialFace


-- @@ L95-118 verbatim
/-- For a fixed positive portal, a lower interval flag and a rooted upper
interval flag account for all but the common top of a Hansen full flag. -/
theorem portalIntervalFlag_card_add_one
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {r : ℕ}
    (hG : UniformFlagCard (HansenCombinatorialFace G) r)
    (p : HansenPortal G)
    (lo : Flag (Set.Iic p.1.1.1))
    (up : Flag (Set.Ici p.1.2)) :
    Nat.card lo + Nat.card up + 1 = r := by
  let hi : Flag (Set.Ici p.1.2.1) :=
    Flag.map (rootedUpperWithTopOrderIso G p.1.2)
      (Flag.addWithTop up)
  let full : Flag (HansenCombinatorialFace G) :=
    (Flag.throughCoverEquiv p.2 (lo, hi)).1
  have hfull : Nat.card full = r := hG full
  have hsplit : Nat.card full = Nat.card lo + Nat.card hi :=
    Flag.card_throughCoverEquiv p.2 (lo, hi)
  have hhi : Nat.card hi = Nat.card up + 1 := by
    calc
      Nat.card hi = Nat.card (Flag.addWithTop up) :=
        Flag.card_map (rootedUpperWithTopOrderIso G p.1.2) _
      _ = Nat.card up + 1 := Flag.card_addWithTop up
  omega


-- @@ L120-140 verbatim
/-- The join upper-interval equivalence removes precisely the single common
top face. -/
theorem card_joinRootedUpperIntervalFlagEquiv_add_one
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (A : SimpleGraph V) (B : SimpleGraph W)
    (F : RootedPos A) (K : RootedPos B)
    (s : Flag (Set.Ici (joinRootedPos A B F K))) :
    Nat.card (joinRootedUpperIntervalFlagEquiv A B F K s) + 1 =
      Nat.card s := by
  change Nat.card
      (Flag.withTopEquiv
        (Flag.map (joinRootedUpperIntervalOrderIso A B F K) s)) + 1 =
    Nat.card s
  calc
    Nat.card
          (Flag.withTopEquiv
            (Flag.map (joinRootedUpperIntervalOrderIso A B F K) s)) + 1 =
        Nat.card (Flag.map (joinRootedUpperIntervalOrderIso A B F K) s) :=
      Flag.card_withTopEquiv_add_one _
    _ = Nat.card s := Flag.card_map _ _


-- @@ L142-211 expanded
/-- A full flag through a specified pair of factor portals has the expected
join cardinality. -/
theorem card_of_mem_joinPortal {V : Type u} {W : Type v} [Fintype V] [DecidableEq V] [Fintype W]
    [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W) {r s : ℕ}
    (hA : UniformFlagCard (HansenCombinatorialFace A) r)
    (hB : UniformFlagCard (HansenCombinatorialFace B) s) (p : HansenPortal A) (q : HansenPortal B)
    (c : Flag (HansenCombinatorialFace (graphJoin A B))) (hlo : joinNeutral A B p.1.1 q.1.1 ∈ c)
    (hhi : joinRootedPos A B p.1.2 q.1.2 ∈ c) : Nat.card c = r + s - 3 := by
  classical
  have hcover : joinNeutral A B p.1.1 q.1.1 ⋖ joinRootedPos A B p.1.2 q.1.2 :=
    joinPortal_covBy_of_factors A B p.1.1 q.1.1 p.1.2 q.1.2 p.2 q.2
  let marked :
    { t : Flag (HansenCombinatorialFace (graphJoin A B)) //
      joinNeutral A B p.1.1 q.1.1 ∈ t ∧ joinRootedPos A B p.1.2 q.1.2 ∈ t } :=
    ⟨c, hlo, hhi⟩
  let split := (Flag.throughCoverEquiv hcover).symm marked
  let loProd := (joinNeutralLowerIntervalFlagEquiv A B p.1.1 q.1.1).symm split.1
  let upProd := joinRootedUpperIntervalFlagEquiv A B p.1.2 q.1.2 split.2
  let loA := Flag.fstProjection loProd
  let loB := Flag.sndProjection loProd
  let upA := Flag.fstProjection upProd
  let upB := Flag.sndProjection upProd
  let _ : Nonempty loA := (loA.maxChain.nonempty_iff.mp inferInstance).to_subtype
  let _ : Nonempty loB := (loB.maxChain.nonempty_iff.mp inferInstance).to_subtype
  let _ : Nonempty upA := (upA.maxChain.nonempty_iff.mp inferInstance).to_subtype
  let _ : Nonempty upB := (upB.maxChain.nonempty_iff.mp inferInstance).to_subtype
  have hc : Nat.card c = Nat.card split.1 + Nat.card split.2 :=
    Flag.card_eq_add_card_throughCoverEquiv_symm hcover marked
  have hloMap : Nat.card split.1 = Nat.card loProd :=
    by
    rw [←
      show joinNeutralLowerIntervalFlagEquiv A B p.1.1 q.1.1 loProd = split.1 from
        (joinNeutralLowerIntervalFlagEquiv A B p.1.1 q.1.1).apply_symm_apply split.1]
    simpa [joinNeutralLowerIntervalFlagEquiv] using
      Flag.card_map (joinNeutralLowerIntervalOrderIso A B p.1.1 q.1.1) loProd
  have hloProd : Nat.card loProd = Nat.card loA + Nat.card loB - 1 :=
    Flag.card_eq_projection_cards loProd
  have hupProd : Nat.card upProd = Nat.card upA + Nat.card upB - 1 :=
    Flag.card_eq_projection_cards upProd
  have hupMap : Nat.card upProd + 1 = Nat.card split.2 :=
    card_joinRootedUpperIntervalFlagEquiv_add_one A B p.1.2 q.1.2 split.2
  have hfactorA : Nat.card loA + Nat.card upA + 1 = r :=
    portalIntervalFlag_card_add_one hA p loA upA
  have hfactorB : Nat.card loB + Nat.card upB + 1 = s :=
    portalIntervalFlag_card_add_one hB q loB upB
  have hloApos : 0 < Nat.card loA := Nat.card_pos
  have hloBpos : 0 < Nat.card loB := Nat.card_pos
  have hupApos : 0 < Nat.card upA := Nat.card_pos
  have hupBpos : 0 < Nat.card upB := Nat.card_pos
  omega


-- @@ L213-237 expanded
/-- Every positive-portal-marked flag of a join has the expected
cardinality. -/
theorem positivePortalFlag_card_join {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W] (A : SimpleGraph V) (B : SimpleGraph W) {r s : ℕ}
    (hA : UniformFlagCard (HansenCombinatorialFace A) r)
    (hB : UniformFlagCard (HansenCombinatorialFace B) s)
    (marked : HansenPortalFlag (graphJoin A B)) : Nat.card marked.1.2 = r + s - 3 :=
  by
  let pq := (joinPortalEquiv A B).symm marked.1.1
  rcases hpq : pq with ⟨p, q⟩
  have hportal : joinPortalEquiv A B (p, q) = marked.1.1 :=
    by
    rw [← hpq]
    exact (joinPortalEquiv A B).apply_symm_apply marked.1.1
  have hlo : joinNeutral A B p.1.1 q.1.1 ∈ marked.1.2 :=
    by
    change (joinPortalEquiv A B (p, q)).1.1.1 ∈ marked.1.2
    rw [hportal]
    exact marked.2.1
  have hhi : joinRootedPos A B p.1.2 q.1.2 ∈ marked.1.2 :=
    by
    change (joinPortalEquiv A B (p, q)).1.2.1 ∈ marked.1.2
    rw [hportal]
    exact marked.2.2
  exact card_of_mem_joinPortal A B hA hB p q marked.1.2 hlo hhi


-- @@ L239-246 verbatim
/-- Central symmetry preserves the number of elements in a portal-marked
flag. -/
theorem card_hansenCentralPortalFlagEquiv
    {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (marked : HansenPortalFlag G) :
    Nat.card (hansenCentralPortalFlagEquiv G marked).1.2 =
      Nat.card marked.1.2 := by
  exact Flag.card_map (hansenCentralFaceOrderIso G) marked.1.2


-- @@ L248-248 verbatim
end HansenCombinatorialFace


-- @@ L250-250 verbatim
namespace UniformFlagCard


-- @@ L252-290 expanded
/-- Hansen join sends factor full-flag lengths `r,s` to `r+s-3`. -/
theorem hansenJoin {V : Type u} {W : Type v} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (A : SimpleGraph V) (B : SimpleGraph W) {r s : ℕ}
    (hA : UniformFlagCard (HansenCombinatorialFace A) r)
    (hB : UniformFlagCard (HansenCombinatorialFace B) s) :
    UniformFlagCard (HansenCombinatorialFace (graphJoin A B)) (r + s - 3) :=
  by
  intro c
  let code := (HansenCombinatorialFace.signedPortalFlagEquiv (graphJoin A B)).symm c
  have hcode : HansenCombinatorialFace.signedPortalFlagEquiv (graphJoin A B) code = c :=
    (HansenCombinatorialFace.signedPortalFlagEquiv (graphJoin A B)).apply_symm_apply c
  rcases code with marked | marked
  · have hflag : marked.1.2 = c := hcode
    rw [← hflag]
    exact HansenCombinatorialFace.positivePortalFlag_card_join A B hA hB marked
  · let positive :=
      (HansenCombinatorialFace.hansenCentralPortalFlagEquiv (graphJoin A B)).symm marked
    have hcentral :
      HansenCombinatorialFace.hansenCentralPortalFlagEquiv (graphJoin A B) positive = marked :=
      (HansenCombinatorialFace.hansenCentralPortalFlagEquiv (graphJoin A B)).apply_symm_apply marked
    have hnegativeFlag : marked.1.2 = c := hcode
    calc
      Nat.card c = Nat.card marked.1.2 := by rw [hnegativeFlag]
      _ =
          Nat.card
            (HansenCombinatorialFace.hansenCentralPortalFlagEquiv (graphJoin A B) positive).1.2 :=
        by rw [hcentral]
      _ = Nat.card positive.1.2 :=
        (HansenCombinatorialFace.card_hansenCentralPortalFlagEquiv (graphJoin A B) positive)
      _ = r + s - 3 := HansenCombinatorialFace.positivePortalFlag_card_join A B hA hB positive


-- @@ L292-292 verbatim
end UniformFlagCard


-- @@ L294-294 verbatim
namespace Cotree


-- @@ L296-326 verbatim
/-- Every full flag of a Hansen polytope arising from a cotree of syntactic
order `n` has `n+3` faces, including the empty face and the whole polytope. -/
theorem uniformFlagCard_eval_order (T : Cotree) :
    UniformFlagCard (HansenCombinatorialFace T.eval) (T.order + 3) := by
  induction T with
  | leaf =>
      rw [Cotree.eval_leaf, Cotree.order]
      exact UniformFlagCard.hansenSingleton
  | compl A ih =>
      rw [Cotree.eval_compl, Cotree.order]
      exact UniformFlagCard.hansenCompl A.eval ih
  | sum A B ihA ihB =>
      have hAc := UniformFlagCard.hansenCompl A.eval ihA
      have hBc := UniformFlagCard.hansenCompl B.eval ihB
      have hjoin := UniformFlagCard.hansenJoin A.evalᶜ B.evalᶜ hAc hBc
      have hlen :
          (A.order + 3) + (B.order + 3) - 3 =
            A.order + B.order + 3 := by
        omega
      rw [hlen] at hjoin
      rw [← compl_sum_eq_join] at hjoin
      have hsumCompl :
          UniformFlagCard
            (HansenCombinatorialFace (A.eval ⊕g B.eval)ᶜ)
            (A.order + B.order + 3) := by
        exact hjoin
      have hsum :=
        UniformFlagCard.hansenCompl (A.eval ⊕g B.eval)ᶜ hsumCompl
      rw [compl_compl] at hsum
      rw [Cotree.eval_sum, Cotree.order]
      exact hsum


-- @@ L328-333 verbatim
/-- Cardinal form of `uniformFlagCard_eval_order`. -/
theorem uniformFlagCard_eval (T : Cotree) :
    UniformFlagCard (HansenCombinatorialFace T.eval)
      (Fintype.card T.Vert + 3) := by
  rw [card_vert_eq_order]
  exact uniformFlagCard_eval_order T


-- @@ L335-335 verbatim
end Cotree


-- @@ L337-337 verbatim
end HansenCograph
