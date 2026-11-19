/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Formalisation.HansenCograph.HansenPortalVector
import Formalisation.HansenCograph.FixedProductFlagShuffle
import Formalisation.HansenCograph.CographPortalRestrictedProduct


-- @@ L10-23 verbatim
/-!
# Exact portal layers at a Hansen graph join

At a join portal, both the lower interval and the rooted upper interval are
products.  This file records the resulting exact (not merely injective)
classification.  A code consists of the two factor portals, a product-shuffle
code below the portal, and a product-shuffle code above it.  Restricting the
lower code to a fixed total number of steps gives the parent portal layer.

Under uniform factor flag lengths `n+3` and `m+3`, the projections of the
lower code are elements of factor portal layers `k,l`, while the two shuffle
paths have sizes `choose (k+l) k` and
`choose ((n-k)+(m-l)) (n-k)` respectively.
-/


-- @@ L25-25 verbatim
open Set SimpleGraph


-- @@ L27-27 verbatim
namespace HansenCograph

-- @@ L28-28 verbatim
namespace HansenCombinatorialFace


-- @@ L30-30 verbatim
universe u v


-- @@ L32-32 verbatim
variable {V : Type u} {W : Type v}

-- @@ L33-33 verbatim
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


-- @@ L35-42 verbatim
/-- The exact data of a rooted positive portal code at a graph join: factor
portals and independent lower and upper product-chain shuffle codes. -/
abbrev HansenJoinPortalShuffleCode (A : SimpleGraph V) (B : SimpleGraph W) :=
  Σ pq : HansenPortal A × HansenPortal B,
    Flag.ProductShuffleCode
        (Set.Iic pq.1.1.1.1) (Set.Iic pq.2.1.1.1) ×
      Flag.ProductShuffleCode
        (Set.Ici pq.1.1.2) (Set.Ici pq.2.1.2)


-- @@ L44-52 verbatim
/-- Decode the lower product shuffle at a pair of factor portals. -/
noncomputable def joinLowerShuffleEquiv
    (A : SimpleGraph V) (B : SimpleGraph W)
    (p : HansenPortal A) (q : HansenPortal B) :
    Flag.ProductShuffleCode
        (Set.Iic p.1.1.1) (Set.Iic q.1.1.1) ≃
      Flag (Set.Iic (joinNeutral A B p.1.1 q.1.1)) :=
  Flag.productShuffleEquiv.trans
    (joinNeutralLowerIntervalFlagEquiv A B p.1.1 q.1.1)


-- @@ L54-65 expanded
/-- Decode the upper product shuffle, then restore the common global top and
finally remove it again in the rooted join stratum. -/
noncomputable def joinRootedUpperShuffleEquiv (A : SimpleGraph V) (B : SimpleGraph W)
    (p : HansenPortal A) (q : HansenPortal B) :
    Flag.ProductShuffleCode (Set.Ici p.1.2) (Set.Ici q.1.2) ≃
      Flag (Set.Ici (joinRootedPosMap A B (p.1.2, q.1.2))) :=
  Flag.productShuffleEquiv.trans
    ((joinRootedUpperIntervalFlagEquiv A B p.1.2 q.1.2).symm.trans
      (rootedUpperIntervalFlagEquiv (graphJoin A B) (joinRootedPosMap A B (p.1.2, q.1.2))))


-- @@ L67-75 expanded
/-- Exact classification of rooted positive portal codes of a Hansen join by
the two factor portals and the independent lower and upper shuffle data. -/
noncomputable def hansenJoinPortalShuffleEquiv (A : SimpleGraph V) (B : SimpleGraph W) :
    HansenJoinPortalShuffleCode A B ≃ HansenPortalCode (graphJoin A B) :=
  Equiv.sigmaCongr (joinPortalEquiv A B) fun pq =>
    Equiv.prodCongr (joinLowerShuffleEquiv A B pq.1 pq.2)
      (joinRootedUpperShuffleEquiv A B pq.1 pq.2)


-- @@ L77-82 verbatim
/-- Join shuffle codes whose lower step counts add to the parent layer
index. -/
abbrev HansenJoinPortalShuffleLayerCode
    (A : SimpleGraph V) (B : SimpleGraph W) (t : ℕ) :=
  {c : HansenJoinPortalShuffleCode A B //
    c.2.1.n + c.2.1.m = t}


-- @@ L84-100 expanded
/-- The exact fixed-layer classification at a Hansen join. -/
noncomputable def hansenJoinPortalLayerEquiv (A : SimpleGraph V) (B : SimpleGraph W) (t : ℕ) :
    HansenJoinPortalShuffleLayerCode A B t ≃ HansenPortalLayer (graphJoin A B) t :=
  (hansenJoinPortalShuffleEquiv A B).subtypeEquiv fun c =>
    by
    change c.2.1.n + c.2.1.m = t ↔ Nat.card ((hansenJoinPortalShuffleEquiv A B c).2.1) - 1 = t
    have hmap : Nat.card ((hansenJoinPortalShuffleEquiv A B c).2.1) = Nat.card c.2.1.decode := by
      exact Flag.card_map (joinNeutralLowerIntervalOrderIso A B c.1.1.1.1 c.1.2.1.1) c.2.1.decode
    rw [hmap, Flag.ProductShuffleCode.decode_card]
    omega


-- @@ L102-107 verbatim
/-- The factor portal code read from the left projections of a join shuffle
code. -/
def HansenJoinPortalShuffleCode.leftFactorCode
    {A : SimpleGraph V} {B : SimpleGraph W}
    (c : HansenJoinPortalShuffleCode A B) : HansenPortalCode A :=
  ⟨c.1.1, c.2.1.leftFlag, c.2.2.leftFlag⟩


-- @@ L109-114 verbatim
/-- The factor portal code read from the right projections of a join shuffle
code. -/
def HansenJoinPortalShuffleCode.rightFactorCode
    {A : SimpleGraph V} {B : SimpleGraph W}
    (c : HansenJoinPortalShuffleCode A B) : HansenPortalCode B :=
  ⟨c.1.2, c.2.1.rightFlag, c.2.2.rightFlag⟩


-- @@ L116-128 verbatim
/-- The left lower projection lies in the layer indexed by the left step
count of the lower shuffle code. -/
def HansenJoinPortalShuffleCode.leftFactorLayer
    {A : SimpleGraph V} {B : SimpleGraph W}
    (c : HansenJoinPortalShuffleCode A B) :
    HansenPortalLayer A c.2.1.n :=
  ⟨c.leftFactorCode, by
    have hpos : 0 < Nat.card c.2.1.leftFlag := by
      rw [c.2.1.left_card]
      omega
    change Nat.card c.2.1.leftFlag - 1 = c.2.1.n
    rw [c.2.1.left_card]
    omega⟩


-- @@ L130-142 verbatim
/-- The right lower projection lies in the layer indexed by the right step
count of the lower shuffle code. -/
def HansenJoinPortalShuffleCode.rightFactorLayer
    {A : SimpleGraph V} {B : SimpleGraph W}
    (c : HansenJoinPortalShuffleCode A B) :
    HansenPortalLayer B c.2.1.m :=
  ⟨c.rightFactorCode, by
    have hpos : 0 < Nat.card c.2.1.rightFlag := by
      rw [c.2.1.right_card]
      omega
    change Nat.card c.2.1.rightFlag - 1 = c.2.1.m
    rw [c.2.1.right_card]
    omega⟩


-- @@ L144-155 verbatim
/-- Uniform length in the left factor determines the number of upper
shuffle steps from the lower layer index. -/
theorem HansenJoinPortalShuffleCode.upper_left_steps
    {A : SimpleGraph V} {B : SimpleGraph W} {n : ℕ}
    (hA : UniformFlagCard (HansenCombinatorialFace A) (n + 3))
    (c : HansenJoinPortalShuffleCode A B) :
    c.2.2.n = n - c.2.1.n := by
  have htotal := portalCode_card hA c.leftFactorCode
  change Nat.card c.2.1.leftFlag + Nat.card c.2.2.leftFlag + 1 =
    n + 3 at htotal
  rw [c.2.1.left_card, c.2.2.left_card] at htotal
  omega


-- @@ L157-168 verbatim
/-- Uniform length in the right factor determines the number of upper
shuffle steps from the lower layer index. -/
theorem HansenJoinPortalShuffleCode.upper_right_steps
    {A : SimpleGraph V} {B : SimpleGraph W} {m : ℕ}
    (hB : UniformFlagCard (HansenCombinatorialFace B) (m + 3))
    (c : HansenJoinPortalShuffleCode A B) :
    c.2.2.m = m - c.2.1.m := by
  have htotal := portalCode_card hB c.rightFactorCode
  change Nat.card c.2.1.rightFlag + Nat.card c.2.2.rightFlag + 1 =
    m + 3 at htotal
  rw [c.2.1.right_card, c.2.2.right_card] at htotal
  omega


-- @@ L170-186 verbatim
/-- The two path fibres over a join shuffle code have exactly the two
binomial multiplicities appearing in the portal convolution kernel. -/
theorem HansenJoinPortalShuffleCode.card_path_fibre
    {A : SimpleGraph V} {B : SimpleGraph W} {n m : ℕ}
    (hA : UniformFlagCard (HansenCombinatorialFace A) (n + 3))
    (hB : UniformFlagCard (HansenCombinatorialFace B) (m + 3))
    (c : HansenJoinPortalShuffleCode A B) :
    Nat.card
        (ShufflePath c.2.1.n c.2.1.m ×
          ShufflePath c.2.2.n c.2.2.m) =
      Nat.choose (c.2.1.n + c.2.1.m) c.2.1.n *
        Nat.choose
          ((n - c.2.1.n) + (m - c.2.1.m))
          (n - c.2.1.n) := by
  rw [Nat.card_prod, Interleaving.card_shufflePath_eq_choose,
    Interleaving.card_shufflePath_eq_choose,
    c.upper_left_steps hA, c.upper_right_steps hB]


-- @@ L188-196 verbatim
/-- A factor portal layer determines the cardinality of its lower flag. -/
theorem portalLayer_lower_card
    {G : SimpleGraph V} {k : ℕ} (c : HansenPortalLayer G k) :
    Nat.card c.1.2.1 = k + 1 := by
  have hpos : 0 < Nat.card c.1.2.1 := by
    let _ : Nonempty c.1.2.1 :=
      (c.1.2.1.maxChain.nonempty_iff.mp inferInstance).to_subtype
    exact Nat.card_pos
  omega


-- @@ L198-208 verbatim
/-- With full-flag length `n+3`, the rooted upper flag in factor layer `k`
has `n-k` steps. -/
theorem portalLayer_upper_card
    {G : SimpleGraph V} {n k : ℕ}
    (hG : UniformFlagCard (HansenCombinatorialFace G) (n + 3))
    (c : HansenPortalLayer G k) :
    Nat.card c.1.2.2 = (n - k) + 1 := by
  have htotal := portalCode_card hG c.1
  have hlo := portalLayer_lower_card c
  have hk := portalLayer_index_lt hG c
  omega


-- @@ L210-221 verbatim
/-- The convolution-shaped factor data for the `t`th portal layer of a
join.  The compatibility proof makes the displayed sum of factor layers
literal, not an implicit side condition. -/
abbrev HansenJoinFactorLayerCode
    (A : SimpleGraph V) (B : SimpleGraph W)
    (n m t : ℕ) :=
  Σ k : Fin (n + 1), Σ l : Fin (m + 1),
    {_z :
        (HansenPortalLayer A k.1 × HansenPortalLayer B l.1) ×
          (ShufflePath k.1 l.1 ×
            ShufflePath (n - k.1) (m - l.1)) //
      k.1 + l.1 = t}


-- @@ L223-243 verbatim
/-- Read the factor-layer form of an exact join shuffle code. -/
noncomputable def joinShuffleLayerToFactorLayerCode
    (A : SimpleGraph V) (B : SimpleGraph W)
    {n m t : ℕ}
    (hA : UniformFlagCard (HansenCombinatorialFace A) (n + 3))
    (hB : UniformFlagCard (HansenCombinatorialFace B) (m + 3)) :
    HansenJoinPortalShuffleLayerCode A B t →
      HansenJoinFactorLayerCode A B n m t := fun c => by
  let k : Fin (n + 1) :=
    ⟨c.1.2.1.n, portalLayer_index_lt hA c.1.leftFactorLayer⟩
  let l : Fin (m + 1) :=
    ⟨c.1.2.1.m, portalLayer_index_lt hB c.1.rightFactorLayer⟩
  let upperPath : ShufflePath (n - k.1) (m - l.1) :=
    cast
      (congrArg₂ ShufflePath
        (c.1.upper_left_steps hA)
        (c.1.upper_right_steps hB))
      c.1.2.2.path
  exact ⟨k, l,
    ⟨((c.1.leftFactorLayer, c.1.rightFactorLayer),
      (c.1.2.1.path, upperPath)), c.2⟩⟩


-- @@ L245-279 verbatim
set_option maxHeartbeats 800000 in
-- The dependent sigma reassembly requires substantially more elaboration than
-- the surrounding nondependent equivalences.
/-- Reassemble lower and upper product-shuffle codes from factor layers and
their two paths. -/
noncomputable def factorLayerCodeToJoinShuffleLayer
    (A : SimpleGraph V) (B : SimpleGraph W)
    {n m t : ℕ}
    (hA : UniformFlagCard (HansenCombinatorialFace A) (n + 3))
    (hB : UniformFlagCard (HansenCombinatorialFace B) (m + 3)) :
    HansenJoinFactorLayerCode A B n m t →
      HansenJoinPortalShuffleLayerCode A B t := by
  rintro ⟨k, l, ⟨⟨⟨left, right⟩, ⟨lowerPath, upperPath⟩⟩, hkl⟩⟩
  let lower : Flag.ProductShuffleCode
      (Set.Iic left.1.1.1.1.1) (Set.Iic right.1.1.1.1.1) :=
    { n := k.1
      m := l.1
      leftFlag := left.1.2.1
      rightFlag := right.1.2.1
      left_card := portalLayer_lower_card left
      right_card := portalLayer_lower_card right
      path := lowerPath }
  let upper : Flag.ProductShuffleCode
      (Set.Ici left.1.1.1.2) (Set.Ici right.1.1.1.2) :=
    { n := n - k.1
      m := m - l.1
      leftFlag := left.1.2.2
      rightFlag := right.1.2.2
      left_card := portalLayer_upper_card hA left
      right_card := portalLayer_upper_card hB right
      path := upperPath }
  exact ⟨⟨(left.1.1, right.1.1), lower, upper⟩, hkl⟩

/- Reindexing both dimensions of a product-shuffle code and transporting its
path does not change the decoded product flag. -/

-- @@ L280-299 verbatim
theorem Flag.ProductShuffleCode.decode_reindex
    {P : Type*} {Q : Type*}
    [PartialOrder P] [Finite P] [Nonempty P]
    [PartialOrder Q] [Finite Q] [Nonempty Q]
    (c : Flag.ProductShuffleCode P Q) {n' m' : ℕ}
    (hn : c.n = n') (hm : c.m = m')
    (hl : Nat.card c.leftFlag = n' + 1)
    (hr : Nat.card c.rightFlag = m' + 1) :
    Flag.ProductShuffleCode.decode
        { n := n'
          m := m'
          leftFlag := c.leftFlag
          rightFlag := c.rightFlag
          left_card := hl
          right_card := hr
          path := cast (congrArg₂ ShufflePath hn hm) c.path } =
      c.decode := by
  subst n'
  subst m'
  rfl


-- @@ L301-361 verbatim
set_option maxHeartbeats 1200000 in
-- Checking both dependent inverse laws unfolds two nested sigma transports.
/-- Regrouping the two product shuffle codes is bijective: it gives exactly
two factor portal-layer elements and the lower and upper paths. -/
noncomputable def hansenJoinFactorLayerEquiv
    (A : SimpleGraph V) (B : SimpleGraph W)
    {n m : ℕ}
    (hA : UniformFlagCard (HansenCombinatorialFace A) (n + 3))
    (hB : UniformFlagCard (HansenCombinatorialFace B) (m + 3))
    (t : ℕ) :
    HansenJoinPortalShuffleLayerCode A B t ≃
      HansenJoinFactorLayerCode A B n m t := by
  let f := joinShuffleLayerToFactorLayerCode A B (t := t) hA hB
  let g := factorLayerCodeToJoinShuffleLayer A B (t := t) hA hB
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · exact Function.LeftInverse.injective (g := g) (by
      intro c
      apply Subtype.ext
      apply Sigma.ext
      · rfl
      · apply heq_of_eq
        apply Prod.ext
        · apply Flag.ProductShuffleCode.decode_injective
          unfold Flag.ProductShuffleCode.decode
          simp only [f, g, joinShuffleLayerToFactorLayerCode,
            factorLayerCodeToJoinShuffleLayer,
            HansenJoinPortalShuffleCode.leftFactorLayer,
            HansenJoinPortalShuffleCode.rightFactorLayer,
            HansenJoinPortalShuffleCode.leftFactorCode,
            HansenJoinPortalShuffleCode.rightFactorCode]
          congr
        · apply Flag.ProductShuffleCode.decode_injective
          simp only [f, g, joinShuffleLayerToFactorLayerCode,
            factorLayerCodeToJoinShuffleLayer,
            HansenJoinPortalShuffleCode.leftFactorLayer,
            HansenJoinPortalShuffleCode.rightFactorLayer,
            HansenJoinPortalShuffleCode.leftFactorCode,
            HansenJoinPortalShuffleCode.rightFactorCode]
          exact Flag.ProductShuffleCode.decode_reindex c.1.2.2
            (c.1.upper_left_steps hA) (c.1.upper_right_steps hB)
            (portalLayer_upper_card hA c.1.leftFactorLayer)
            (portalLayer_upper_card hB c.1.rightFactorLayer))
  · intro z
    refine ⟨g z, ?_⟩
    rcases z with ⟨k, l,
      ⟨⟨⟨left, right⟩, ⟨lowerPath, upperPath⟩⟩, hkl⟩⟩
    apply Sigma.ext
    · apply Fin.ext
      rfl
    · apply heq_of_eq
      apply Sigma.ext
      · apply Fin.ext
        rfl
      · apply heq_of_eq
        apply Subtype.ext
        apply Prod.ext
        · apply Prod.ext <;> apply Subtype.ext <;> rfl
        · apply Prod.ext
          · rfl
          · simp [f, g, joinShuffleLayerToFactorLayerCode,
              factorLayerCodeToJoinShuffleLayer]


-- @@ L363-417 verbatim
/-- Cardinality of one fixed `(k,l)` fibre in the factor-layer model. -/
theorem card_hansenJoinFactorLayer_fibre
    (A : SimpleGraph V) (B : SimpleGraph W)
    (n m t : ℕ) (k : Fin (n + 1)) (l : Fin (m + 1)) :
    Nat.card
        {_z :
            (HansenPortalLayer A k.1 × HansenPortalLayer B l.1) ×
              (ShufflePath k.1 l.1 ×
                ShufflePath (n - k.1) (m - l.1)) //
          k.1 + l.1 = t} =
      if PortalRankCompatible t k.1 l.1 then
        Fintype.card
          (RestrictedProductPortalChain n m t k.1 l.1
            (hansenPortalVector A k.1) (hansenPortalVector B l.1))
      else 0 := by
  by_cases h : k.1 + l.1 = t
  · have hp : PortalRankCompatible t k.1 l.1 := h
    rw [ite_eq_left hp]
    let e :
        {z :
            (HansenPortalLayer A k.1 × HansenPortalLayer B l.1) ×
              (ShufflePath k.1 l.1 ×
                ShufflePath (n - k.1) (m - l.1)) //
          k.1 + l.1 = t} ≃
        (HansenPortalLayer A k.1 × HansenPortalLayer B l.1) ×
          (ShufflePath k.1 l.1 ×
            ShufflePath (n - k.1) (m - l.1)) :=
      { toFun := fun z => z.1
        invFun := fun z => ⟨z, h⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.card_prod,
      Interleaving.card_shufflePath_eq_choose,
      Interleaving.card_shufflePath_eq_choose,
      card_restrictedProductPortalChain]
    simp only [hansenPortalVector, Nat.card_eq_fintype_card]
    have hk : k.1 ≤ n := Nat.lt_succ_iff.mp k.2
    have hl : l.1 ≤ m := Nat.lt_succ_iff.mp l.2
    have hu := restrictedProduct_upper_rank_sum hk hl hp
    rw [hu]
    ac_rfl
  · have hp : ¬ PortalRankCompatible t k.1 l.1 := h
    rw [ite_eq_right hp]
    let e :
          {z :
              (HansenPortalLayer A k.1 × HansenPortalLayer B l.1) ×
                (ShufflePath k.1 l.1 ×
                  ShufflePath (n - k.1) (m - l.1)) //
            k.1 + l.1 = t} ≃ Empty :=
      { toFun := fun z => False.elim (h z.2)
        invFun := fun z => nomatch z
        left_inv := fun z => False.elim (h z.2)
        right_inv := fun z => nomatch z }
    rw [Nat.card_congr e]
    simp


-- @@ L419-445 verbatim
/-- The explicit factor-layer model has exactly the natural-valued
restricted-product portal count. -/
theorem card_hansenJoinFactorLayerCode_eq_restrictedProductPortalCount
    (A : SimpleGraph V) (B : SimpleGraph W)
    (n m t : ℕ) :
    Nat.card (HansenJoinFactorLayerCode A B n m t) =
      restrictedProductPortalCount n m t
        (hansenPortalVector A) (hansenPortalVector B) := by
  unfold restrictedProductPortalCount
  let F : ℕ → ℕ → ℕ := fun k l =>
    Nat.card
      {z :
          (HansenPortalLayer A k × HansenPortalLayer B l) ×
            (ShufflePath k l × ShufflePath (n - k) (m - l)) //
        k + l = t}
  rw [Nat.card_sigma]
  simp_rw [Nat.card_sigma]
  change (∑ k : Fin (n + 1), ∑ l : Fin (m + 1), F k.1 l.1) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => ∑ l : Fin (m + 1), F k l.1)]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Fin.sum_univ_eq_sum_range (fun l : ℕ => F k l)]
  apply Finset.sum_congr rfl
  intro l hl
  exact card_hansenJoinFactorLayer_fibre A B n m t
    ⟨k, Finset.mem_range.mp hk⟩ ⟨l, Finset.mem_range.mp hl⟩


-- @@ L447-469 expanded
/-- Exact portal-vector convolution law for a Hansen graph join. -/
theorem hansenPortalVector_join_eq_restrictedProductPortalCount (A : SimpleGraph V)
    (B : SimpleGraph W) {n m : ℕ} (hA : UniformFlagCard (HansenCombinatorialFace A) (n + 3))
    (hB : UniformFlagCard (HansenCombinatorialFace B) (m + 3)) (t : ℕ) :
    hansenPortalVector (graphJoin A B) t =
      restrictedProductPortalCount n m t (hansenPortalVector A) (hansenPortalVector B) :=
  by
  calc
    hansenPortalVector (graphJoin A B) t = Nat.card (HansenJoinPortalShuffleLayerCode A B t) :=
      (by
        change Fintype.card (HansenPortalLayer (graphJoin A B) t) = _
        rw [← Nat.card_eq_fintype_card]
        exact (Nat.card_congr (hansenJoinPortalLayerEquiv A B t)).symm)
    _ = Nat.card (HansenJoinFactorLayerCode A B n m t) :=
      (Nat.card_congr (hansenJoinFactorLayerEquiv A B hA hB t))
    _ = restrictedProductPortalCount n m t (hansenPortalVector A) (hansenPortalVector B) :=
      card_hansenJoinFactorLayerCode_eq_restrictedProductPortalCount A B n m t


-- @@ L471-484 expanded
/-- Real-valued form of the exact portal-vector convolution law. -/
theorem hansenPortalVector_join_cast_eq_portalShuffleConvolution (A : SimpleGraph V)
    (B : SimpleGraph W) {n m : ℕ} (hA : UniformFlagCard (HansenCombinatorialFace A) (n + 3))
    (hB : UniformFlagCard (HansenCombinatorialFace B) (m + 3)) (t : ℕ) :
    (hansenPortalVector (graphJoin A B) t : ℝ) =
      portalShuffleConvolution n m (fun k => (hansenPortalVector A k : ℝ))
        (fun l => (hansenPortalVector B l : ℝ)) t :=
  by
  rw [hansenPortalVector_join_eq_restrictedProductPortalCount A B hA hB t]
  exact
    restrictedProductPortalCount_cast_eq_portalShuffleConvolution n m t (hansenPortalVector A)
      (hansenPortalVector B)


-- @@ L486-494 expanded
/-- Exact cardinality of a parent portal layer as the cardinality of its
factor-portal/product-shuffle model. -/
theorem hansenPortalVector_join_eq_card_shuffleLayer (A : SimpleGraph V) (B : SimpleGraph W)
    (t : ℕ) :
    hansenPortalVector (graphJoin A B) t = Nat.card (HansenJoinPortalShuffleLayerCode A B t) :=
  by
  change Fintype.card (HansenPortalLayer (graphJoin A B) t) = _
  rw [← Nat.card_eq_fintype_card]
  exact (Nat.card_congr (hansenJoinPortalLayerEquiv A B t)).symm


-- @@ L496-496 verbatim
end HansenCombinatorialFace

-- @@ L497-497 verbatim
end HansenCograph
