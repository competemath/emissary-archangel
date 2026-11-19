/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Formalisation.HansenCograph.HansenPortalFlags
import Formalisation.HansenCograph.FlagCoverDecomposition


-- @@ L9-14 verbatim
/-!
# Interval decomposition of Hansen portal flags

This specializes maximal-chain decomposition across a cover to positive
Hansen portals.
-/


-- @@ L16-16 verbatim
open Set SimpleGraph


-- @@ L18-18 verbatim
namespace HansenCograph

-- @@ L19-19 verbatim
namespace HansenCombinatorialFace


-- @@ L21-21 verbatim
universe u v


-- @@ L23-24 verbatim
variable {V : Type u} {W : Type v} [Fintype V] [DecidableEq V]
  [Fintype W] [DecidableEq W]


-- @@ L26-30 verbatim
/-- A positive portal together with independently chosen maximal chains in
the intervals below and above its endpoints. -/
abbrev HansenPortalIntervalFlags (G : SimpleGraph V) :=
  Σ p : HansenPortal G,
    Flag (Set.Iic p.1.1.1) × Flag (Set.Ici p.1.2.1)


-- @@ L32-53 verbatim
/-- Splitting a portal-marked full flag at its marked cover gives exactly
the two interval flags on either side. -/
noncomputable def hansenPortalFlagIntervalEquiv (G : SimpleGraph V) :
    HansenPortalFlag G ≃ HansenPortalIntervalFlags G where
  toFun marked :=
    ⟨marked.1.1,
      (HansenCograph.Flag.throughCoverEquiv marked.1.1.2).symm
        ⟨marked.1.2, marked.2⟩⟩
  invFun code := by
    let marked := HansenCograph.Flag.throughCoverEquiv code.1.2 code.2
    exact ⟨(code.1, marked.1), marked.2⟩
  left_inv marked := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · exact congrArg Subtype.val
        ((HansenCograph.Flag.throughCoverEquiv marked.1.1.2).apply_symm_apply
          ⟨marked.1.2, marked.2⟩)
  right_inv code := by
    rcases code with ⟨p, pair⟩
    exact congrArg (Sigma.mk p)
      ((HansenCograph.Flag.throughCoverEquiv p.2).symm_apply_apply pair)


-- @@ L55-56 verbatim
noncomputable instance instFintypeHansenPortalIntervalIndex
    (G : SimpleGraph V) : Fintype (HansenPortal G) := Fintype.ofFinite _


-- @@ L58-84 verbatim
/-- The positive portal count is the sum, over positive portals, of the
product of the lower- and upper-interval full-flag counts. -/
theorem hansenPositivePortalFlagCount_eq_sum_intervalFlags
    (G : SimpleGraph V) :
    hansenPositivePortalFlagCount G =
      ∑ p : HansenPortal G,
        Nat.card (Flag (Set.Iic p.1.1.1)) *
          Nat.card (Flag (Set.Ici p.1.2.1)) := by
  classical
  calc
    hansenPositivePortalFlagCount G = Nat.card (HansenPortalFlag G) := by
      exact Nat.card_eq_fintype_card.symm
    _ = Nat.card (HansenPortalIntervalFlags G) :=
      Nat.card_congr (hansenPortalFlagIntervalEquiv G)
    _ = ∑ p : HansenPortal G,
        Nat.card (Flag (Set.Iic p.1.1.1) ×
          Flag (Set.Ici p.1.2.1)) := Nat.card_sigma
    _ = ∑ p : HansenPortal G,
        Nat.card (Flag (Set.Iic p.1.1.1)) *
          Nat.card (Flag (Set.Ici p.1.2.1)) := by
      apply Finset.sum_congr rfl
      intro p hp
      exact Nat.card_prod _ _

/- Reindex the exact portal-interval sum for a join by the bijection of
factor portals.  The summand is intentionally left as an interval flag
count: the shuffle multiplicities belong to those product-poset counts. -/

-- @@ L85-95 expanded
theorem hansenPositivePortalFlagCount_join_eq_sum_factorPortals (A : SimpleGraph V)
    (B : SimpleGraph W) :
    hansenPositivePortalFlagCount (graphJoin A B) =
      ∑ p : HansenPortal A × HansenPortal B,
        Nat.card (Flag (Set.Iic (joinNeutral A B p.1.1.1 p.2.1.1))) *
          Nat.card (Flag (Set.Ici (joinRootedPos A B p.1.1.2 p.2.1.2))) :=
  by
  rw [hansenPositivePortalFlagCount_eq_sum_intervalFlags]
  symm
  refine Fintype.sum_equiv (joinPortalEquiv A B) _ _ ?_
  intro p
  rfl


-- @@ L97-97 verbatim
end HansenCombinatorialFace

-- @@ L98-98 verbatim
end HansenCograph
