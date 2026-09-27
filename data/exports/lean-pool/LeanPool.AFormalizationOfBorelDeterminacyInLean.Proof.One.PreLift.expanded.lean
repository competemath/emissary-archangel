/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
module

public import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.CoveringClosedGame
public import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.WinAsap
public import LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.BuildLevelwise
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Set.Subset
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.ApplyFun
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific


-- @@ L21-25 verbatim
/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.One.PreLift

Auxiliary declarations for the Borel determinacy formalization.
-/


-- @@ L27-27 verbatim
@[expose] public section



-- @@ L30-30 verbatim
namespace GaleStewartGame.BorelDet.One

-- @@ L31-31 verbatim
open Stream'.Discrete Descriptive Tree Game PreStrategy

-- @@ L32-32 verbatim
open CategoryTheory


-- @@ L34-34 verbatim
variable {A : Type*} {G : Game A} {k m n : ℕ} {hyp : Hyp G k}


-- @@ L36-36 verbatim
noncomputable section «Section1»


-- @@ L38-45 verbatim
variable (hyp) in
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[ext] structure PreLift where
  /-- Auxiliary declaration for the Borel determinacy formalization. -/
  x : G.tree
  hlvl : 2 * k < x.val.length (α := no_index _)
  /-- Auxiliary declaration for the Borel determinacy formalization. -/
  R : ResStrategy (gameAsTrees hyp) Player.one (2 * k + 1)

-- @@ L46-46 verbatim
namespace PreLift

-- @@ L47-47 verbatim
variable (H : PreLift hyp)

-- @@ L48-48 verbatim
attribute [simp] hlvl

-- @@ L49-49 verbatim
lemma hlvl_le : 2 * k + 1 ≤ H.x.val.length (α := no_index _) := by simp

-- @@ L50-50 verbatim
@[simp] lemma hlvl' : 2 * k ≤ H.x.val.length (α := no_index _) := by linarith [H.hlvl]

-- @@ L51-57 verbatim
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
lemma pInv_take_length :
    (pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val.length (α := no_index _) = 2 * k := by
  rw [pInv_treeHom_val]
  · change (pInvTreeHomMap hyp (List.take (2 * k) H.x.val)).length = 2 * k
    simp_all
  · simp

-- @@ L58-69 verbatim
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
lemma gameTree_eq :
    subAt (getTree' hyp (pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val)
      [H.x.val[2 * k]'H.hlvl] =
  subAt G.tree (H.x.val.take (2 * k + 1)) := by
  rw [pInv_treeHom_val]
  · rw [getTree_pInvTreeHomMap, Game.residual_tree, subAt_append]
    congr 1
    change List.take (2 * k) H.x.val ++ [H.x.val[2 * k]] =
      List.take (2 * k + 1) H.x.val
    exact H.x.val.take_concat_get' (2 * k) H.hlvl
  · simp


-- @@ L71-75 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def take (n : ℕ) (h : 2 * k < n) : PreLift hyp where
  x := Tree.take n H.x
  hlvl := by simp [h]
  R := H.R

-- @@ L76-76 verbatim
attribute [simp_lengths] take_x

-- @@ L77-78 verbatim
lemma take_of_length_le {h} (h' : H.x.val.length ≤ n) : H.take n h = H := by
  ext1 <;> [ext1; skip] <;> simp [h']

-- @@ L79-80 verbatim
@[simp] lemma take_rfl : H.take (H.x.val.length (α := no_index _)) H.hlvl = H :=
  H.take_of_length_le le_rfl

-- @@ L81-83 verbatim
@[simp] lemma take_trans hm hn : (H.take m hm).take n hn
  = H.take (min m n) (by as_aux_lemma => omega) := by
  ext1 <;> simp [min_comm]


-- @@ L85-86 verbatim
@[simps] instance : LE (PreLift hyp) where
  le p q := q.take p.x.val.length p.hlvl = p

-- @@ L87-89 verbatim
lemma length_mono {p q : PreLift hyp} (h : p ≤ q) : p.x.val.length ≤ q.x.val.length := by
  -- This is not registered as a `gcongr` lemma because of the dependent projections.
  rw [← h]; simp

-- @@ L90-96 verbatim
instance : PartialOrder (PreLift hyp) where
  le_refl := by simp
  le_trans _ _ _ pq qr := by have := length_mono pq; rw [← qr] at pq; simpa [this] using pq
  le_antisymm _ _ pq qp := by
    ext1 <;> [ext1; skip] <;> rw [← pq]
    · simpa using length_mono qp
    · simp

-- @@ L97-101 verbatim
lemma take_le {h} : H.take n h ≤ H := by
  dsimp [LE.le]
  ext1
  · simp_all
  · rfl

-- @@ L102-103 verbatim
lemma take_le_take hm hn : H.take m hm ≤ H.take n hn ↔ m ≤ n ∨ H.x.val.length ≤ n := by
  (conv => lhs; dsimp [LE.le]); simp [PreLift.ext_iff]

-- @@ L104-104 verbatim
end PreLift


-- @@ L106-112 verbatim
variable (hyp) in
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[ext (flat := false)] structure Lift extends PreLift hyp where
  /-- Auxiliary declaration for the Borel determinacy formalization. -/
  liftTree : tree A
  htree : ∃ S : QuasiStrategy (subAt G.tree (x.val.take (2 * k + 1))) Player.one,
    liftTree = S.1.subtree

-- @@ L113-116 verbatim
@[simps] instance : Preorder (Lift hyp) where
  le p q := p.toPreLift ≤ q.toPreLift
  le_refl _ := le_rfl (α := PreLift hyp)
  le_trans _ _ _ := le_trans (α := PreLift hyp)

-- @@ L117-117 verbatim
namespace Lift

-- @@ L118-118 verbatim
variable (H : Lift hyp)

-- @@ L119-141 verbatim
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def liftVeryShort : gameTree hyp where
  val := (pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val ++
    [⟨H.x.val[2 * k]'H.hlvl, H.liftTree⟩]
  property := by
    apply (gameTree_concat (hyp := hyp)
      (x := (pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val)
      (a := ⟨H.x.val[2 * k]'H.hlvl, H.liftTree⟩)).mpr
    constructor
    · exact (pInv (treeHom hyp) (Tree.take (2 * k) H.x)).prop
    · have hlen : (pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val.length = 2 * k :=
        H.toPreLift.pInv_take_length
      rw [validExt_zero hlen]
      constructor
      · rw [pInv_treeHom_val]
        · rw [getTree_pInvTreeHomMap]
          change List.take (2 * k) H.x.val ++ [H.x.val[2 * k]] ∈ G.tree
          rw [H.x.val.take_concat_get' (2 * k) H.hlvl]
          exact Tree.take_mem H.x
        · simp
      · rw [H.gameTree_eq]
        exact H.htree

-- @@ L142-149 verbatim
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
@[simp, simp_lengths] lemma liftVeryShort_length :
  H.liftVeryShort.val.length (α := no_index _) = 2 * k + 1 := by
  simp only [liftVeryShort]
  change List.length ((pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val ++
    [⟨H.x.val[2 * k]'H.hlvl, H.liftTree⟩]) = 2 * k + 1
  rw [List.length_append, H.toPreLift.pInv_take_length]
  rfl

-- @@ L150-165 verbatim
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
@[simp] lemma liftVeryShort_val_map :
  H.liftVeryShort.val.map (α := no_index _) Prod.fst = H.x.val.take (2 * k + 1) := by
  calc
    H.liftVeryShort.val.map Prod.fst =
        (pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val.map Prod.fst ++
          [H.x.val[2 * k]] :=
      List.map_append ..
    _ = H.x.val.take (2 * k) ++ [H.x.val[2 * k]] := by
      congr 1
      change (treeHom hyp (pInv (treeHom hyp) (Tree.take (2 * k) H.x))).val =
        H.x.val.take (2 * k)
      rw [cancel_pInv_right]
      rfl
    _ = H.x.val.take (2 * k + 1) := by
      simp_all

-- @@ L166-173 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def liftShort : gameTree hyp := (H.R H.liftVeryShort
  (by
    change H.liftVeryShort.val.length % 2 = Player.one.toNat
    simp_all)
  (by
    change H.liftVeryShort.val.length ≤ 2 * k + 1
    rw [H.liftVeryShort_length])).valT'

-- @@ L174-190 verbatim
@[simp, simp_lengths] lemma liftShort_length :
  H.liftShort.val.length (α := no_index _) = 2 * k + 2 := by
  have hlen := ExtensionsAt.val'_length
    (H.R H.liftVeryShort (by
      change H.liftVeryShort.val.length % 2 = Player.one.toNat
      simp_all) (by
      change H.liftVeryShort.val.length ≤ 2 * k + 1
      rw [H.liftVeryShort_length]))
  change
    (H.R H.liftVeryShort (by
      change H.liftVeryShort.val.length % 2 = Player.one.toNat
      simp_all) (by
      change H.liftVeryShort.val.length ≤ 2 * k + 1
      rw [H.liftVeryShort_length])).val'.length = 2 * k + 2
  rw [hlen]
  change H.liftVeryShort.val.length + 1 = 2 * k + 2
  rw [H.liftVeryShort_length]

-- @@ L191-193 verbatim
@[simp] lemma liftShort_val_take :
  H.liftShort.val.take (α := no_index _) (2 * k + 1) = H.liftVeryShort :=
  ExtensionsAt.val'_take_of_eq _ H.liftVeryShort_length.symm

-- @@ L194-198 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def liftVal := if H.x.val.length = 2 * k + 1 then H.liftVeryShort.val
  else H.liftShort.val ++
  (H.x.val.drop (2 * k + 2)).zipInitsMap
    (fun a y ↦ ⟨a, subAt (getTree' hyp H.liftShort.val) y⟩)

-- @@ L199-200 verbatim
lemma liftVal_very_short (h : H.x.val.length = 2 * k + 1) : H.liftVal = H.liftVeryShort.val := by
  unfold liftVal; split_ifs; rfl

-- @@ L201-204 expanded
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
@[simp, simp_lengths]
lemma liftVal_length : H.liftVal.length (α := no_index _) = H.x.val.length := by have := H.hlvl;
  simp_rw [liftVal];
  split_ifs <;>
    first
    | done
    |
      (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
            simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
              simp_lengths] <;>
          omega)


-- @@ L205-209 verbatim
@[simp] lemma liftVal_take_short (h : 2 * k + 2 ≤ H.x.val.length) :
  H.liftVal.take (α := no_index _) (2 * k + 2) = H.liftShort.val := by
  unfold liftVal; split_ifs
  · omega
  · simp

-- @@ L210-218 verbatim
@[simp] lemma liftVal_take_veryShort :
  H.liftVal.take (α := no_index _) (2 * k + 1) = H.liftVeryShort.val := by
  conv => simp [liftVal, liftShort]
  split_ifs
  · simp
  · rw [List.take_append_of_le_length (by
      change 2 * k + 1 ≤ H.liftShort.val.length
      simp_all)]
    exact H.liftShort_val_take

-- @@ L219-242 verbatim
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
@[simp] lemma liftVal_take_init (h : n ≤ 2 * k) :
  H.liftVal.take (α := no_index _) n = pInvTreeHomMap hyp (H.x.val.take n) := by
  have hmin : n = min n (2 * k + 1) := by omega
  rw [hmin, ← List.take_take, liftVal_take_veryShort]
  simp only [liftVeryShort]
  have hpInvLen :
      n ≤ (pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val.length := by
    rw [H.toPreLift.pInv_take_length]
    exact h
  change List.take n ((pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val ++
      [⟨H.x.val[2 * k]'H.hlvl, H.liftTree⟩]) =
    pInvTreeHomMap hyp (H.x.val.take (min n (2 * k + 1)))
  rw [List.take_append_of_le_length (by
    exact hpInvLen)]
  rw [pInv_treeHom_val]
  · change List.take n (pInvTreeHomMap hyp (List.take (2 * k) H.x.val)) =
      pInvTreeHomMap hyp (H.x.val.take (min n (2 * k + 1)))
    rw [pInvTreeHomMap, List.zipInitsMap_take]
    congr 1
    rw [List.take_take]
    rw [min_eq_left h, min_eq_left (by omega : n ≤ 2 * k + 1)]
  · simp
-- for u drop (2 * k + 1)

-- @@ L243-247 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def PreWonPos (u : List A) := LosingCondition H.liftShort.val (by simp) ∧
  (∃ (h : u ≠ []), u[0]'(by simpa [List.length_pos_iff]) = H.liftShort.val[2 * k + 1].1) ∧
  getTree' hyp H.liftShort.val =
    pullSub (subAt G.tree (H.x.val.take (2 * k + 1) ++ u)) u.tail


-- @@ L249-255 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps toPreLift liftTree] def take (n : ℕ) (h : 2 * k + 1 ≤ n) : Lift hyp where
  toPreLift := H.toPreLift.take n (by omega)
  liftTree := H.liftTree
  htree := by
    obtain ⟨S, hS⟩ := H.htree; use cast (by simp [List.take_take, h]) S
    rw [hS]; symm; apply cast_subtree (by simp [List.take_take, h]) rfl

-- @@ L256-256 verbatim
attribute [simp_lengths] take_toPreLift

-- @@ L257-258 verbatim
lemma take_of_length_le {h} (h' : H.x.val.length ≤ n) : H.take n h = H := by
  ext1; apply PreLift.take_of_length_le <;> omega; rfl

-- @@ L259-260 verbatim
@[simp] lemma take_rfl : H.take (H.x.val.length (α := no_index _)) H.hlvl = H :=
  H.take_of_length_le le_rfl

-- @@ L261-264 verbatim
@[simp] lemma take_trans hm hn : (H.take m hm).take n hn = H.take (min m n) (by simp [*]) := by
  ext1
  · simp
  · rfl

-- @@ L265-277 verbatim
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
@[simp] lemma liftVeryShort_take h : (H.take n h).liftVeryShort = H.liftVeryShort := by
  ext1
  simp only [liftVeryShort, take_toPreLift, take_liftTree, PreLift.take_x, take_coe]
  congr 1
  · rw [pInv_treeHom_val]
    · rw [pInv_treeHom_val]
      · change pInvTreeHomMap hyp (List.take (2 * k) (List.take n H.x.val)) =
          pInvTreeHomMap hyp (List.take (2 * k) H.x.val)
        rw [List.take_take, min_eq_left (by omega : 2 * k ≤ n)]
      · simp_all
    · simp_all
  · simp

-- @@ L278-283 verbatim
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
@[simp] lemma liftShort_take h : (H.take n h).liftShort = H.liftShort := by
  apply tree_ext
  simpa [liftShort] using congrArg Subtype.val
    (ResStrategy.eval_valT'_congr' H.R H.R rfl
      (H.take n h).liftVeryShort H.liftVeryShort (H.liftVeryShort_take h) _ _)

-- @@ L284-293 expanded
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
@[simp]
lemma liftVal_take n h : (H.take n h).liftVal = H.liftVal.take n :=
  by
  unfold Lift.liftVal; split_ifs
  · simpa
  · have : n = 2 * k + 1 := by
      first
      | done
      |
        (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
              simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
                simp_lengths] <;>
            omega)
    rw [List.take_append_of_le_length (by simp [this])]; simp [this]
  ·
    first
    | done
    |
      (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
            simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
              simp_lengths] <;>
          omega)
  · conv => simp [List.take_append, List.drop_take, List.zipInitsMap_take]
    have := H.hlvl;
    first
    | done
    |
      (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
            simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
              simp_lengths] <;>
          omega)


-- @@ L294-295 verbatim
@[simp] lemma preWonPos_take h u :
  (H.take n h).PreWonPos u ↔ H.PreWonPos u := by simp [PreWonPos, List.take_take, h]

-- @@ L296-296 verbatim
lemma take_le {h} : H.take n h ≤ H := H.toPreLift.take_le (h := h)

-- @@ L297-298 verbatim
lemma take_le_take hm hn : H.take m hm ≤ H.take n hn ↔ m ≤ n ∨ H.x.val.length ≤ n :=
  H.toPreLift.take_le_take hm hn

-- @@ L299-303 verbatim
lemma eq_take {H H' : Lift hyp} (h : H ≤ H') (ht : H.liftTree = H'.liftTree) :
  H = H'.take H.x.val.length (by simp) := by
  ext1
  · exact h.symm
  · exact ht

-- @@ L304-305 verbatim
lemma liftVal_mono {H H' : Lift hyp} (h : H ≤ H') (ht : H.liftTree = H'.liftTree) :
  H.liftVal <+: H'.liftVal := by rw [eq_take h ht]; simpa using List.take_prefix _ _


-- @@ L307-309 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def Con := H.x.val.drop (2 * k + 1) ∈
  pullSub (getTree' hyp H.liftShort.val) [H.liftShort.val[2 * k + 1].1]

-- @@ L310-311 verbatim
lemma Con.take h (h' : H.Con) : (H.take n h).Con := by
  simpa [Lift.Con, List.drop_take] using take_mem ⟨_, h'⟩

-- @@ L312-313 verbatim
lemma con_of_short (h : H.x.val.length = 2 * k + 1) : H.Con := by
  simpa [Con, ← h] using (getTree_ne_and_pruned _).1

-- @@ L314-317 verbatim
lemma con_short_long (h : 2 * k + 2 ≤ H.x.val.length) : H.Con ↔
  H.liftShort.val[2 * k + 1].1 = H.x.val[2 * k + 1] ∧
  H.x.val.drop (2 * k + 2) ∈ getTree' hyp H.liftShort.val := by
  simp [Con, pullSub, List.take_one_drop_eq_of_lt_length h, eq_comm]

-- @@ L318-318 verbatim
end Lift


-- @@ L320-323 verbatim
variable (hyp) in
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[ext (flat := false)] structure Lift' extends Lift hyp where
  con : toLift.Con

-- @@ L324-327 verbatim
instance : Preorder (Lift' hyp) where
  le p q := p.toLift ≤ q.toLift
  le_refl _ := le_rfl (α := Lift hyp)
  le_trans _ _ _ := le_trans (α := Lift hyp)

-- @@ L328-328 verbatim
namespace Lift'

-- @@ L329-329 verbatim
variable (H : Lift' hyp)

-- @@ L330-332 verbatim
lemma conShort (h : 2 * k + 2 ≤ H.x.val.length) :
  H.liftShort.val[2 * k + 1].1 = H.x.val[2 * k + 1] :=
  ((H.con_short_long h).mp H.con).1

-- @@ L333-334 verbatim
lemma conLong : H.x.val.drop (2 * k + 2) ∈ getTree' hyp H.liftShort.val := by
  simpa [add_comm, ← add_assoc] using H.con.2

-- @@ L335-350 verbatim
@[simp] lemma liftShort_val_map (h : 2 * k + 2 ≤ H.x.val.length) :
  H.liftShort.val.map (α := no_index _) Prod.fst = H.x.val.take (2 * k + 2) := by
  rw [H.liftShort.val.eq_take_concat (2 * k + 1) (by simp)]
  calc
    List.map Prod.fst (List.take (2 * k + 1) H.liftShort.val ++
        [H.liftShort.val[2 * k + 1]]) =
        List.map Prod.fst (List.take (2 * k + 1) H.liftShort.val) ++
          [H.liftShort.val[2 * k + 1].1] :=
      List.map_append ..
    _ = H.x.val.take (2 * k + 1) ++ [H.x.val[2 * k + 1]] := by
      congr 1
      · exact congrArg (List.map Prod.fst) H.liftShort_val_take |>.trans
          H.liftVeryShort_val_map
      · exact congrArg List.singleton (H.conShort h)
    _ = H.x.val.take (2 * k + 2) :=
      H.x.val.take_concat_get' (2 * k + 1) (by omega)

-- @@ L351-375 verbatim
@[simp] lemma liftVal_lift : H.liftVal.map (α := no_index _) Prod.fst = H.x.val := by
  unfold Lift.liftVal
  split_ifs with hshort
  · simp_all
  · have hlong : 2 * k + 2 ≤ H.x.val.length := by
      have := H.hlvl
      omega
    let tail : List (upA hyp) :=
      (H.x.val.drop (2 * k + 2)).zipInitsMap
        (fun a y ↦ ⟨a, subAt (getTree' hyp H.liftShort.val) y⟩)
    change List.map Prod.fst (H.liftShort.val ++ tail) = H.x.val
    calc
      List.map Prod.fst (H.liftShort.val ++ tail) =
          H.liftShort.val.map Prod.fst ++ tail.map Prod.fst :=
        List.map_append ..
      _ = H.liftShort.val.map Prod.fst ++ H.x.val.drop (2 * k + 2) := by
        congr 1
        change List.map Prod.fst
            ((H.x.val.drop (2 * k + 2)).zipInitsMap fun a y ↦
              (a, subAt (getTree' hyp H.liftShort.val) y)) =
          H.x.val.drop (2 * k + 2)
        rw [← List.zipInitsMap_map]
        simp
      _ = H.x.val := by
        simp_all

-- @@ L376-386 verbatim
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
@[simp] lemma liftVal_lift_get (h : n < H.x.val.length) :
  (H.liftVal[n]'(by simp [h])).1 = H.x.val[n]'(by simpa) := by
  have hlift : n < H.liftVal.length := by simpa [H.liftVal_length] using h
  have hget := congrArg (fun xs ↦ xs[n]?) H.liftVal_lift
  change (H.liftVal.map Prod.fst)[n]? = H.x.val[n]? at hget
  rw [List.getElem?_eq_getElem (by simpa [List.length_map] using hlift)] at hget
  rw [List.getElem?_eq_getElem h] at hget
  have hget' := Option.some.inj hget
  rw [List.getElem_map] at hget'
  exact hget'


-- @@ L388-391 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps toLift] def take (n : ℕ) (h : 2 * k + 1 ≤ n) : Lift' hyp where
  toLift := H.toLift.take n (by omega)
  con := H.con.take _ _

-- @@ L392-392 verbatim
attribute [simp_lengths] take_toLift

-- @@ L393-394 verbatim
lemma take_of_length_le {h} (h' : H.x.val.length ≤ n) : H.take n h = H := by
  ext1; apply Lift.take_of_length_le <;> omega

-- @@ L395-396 verbatim
@[simp] lemma take_rfl : H.take (H.x.val.length (α := no_index _)) H.hlvl = H :=
  H.take_of_length_le le_rfl

-- @@ L397-398 verbatim
@[simp] lemma take_trans hm hn : (H.take m hm).take n hn = H.take (min m n) (by simp [*]) := by
  ext1; simp


-- @@ L400-446 expanded
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps]
def lift : gameTree hyp where
  val := H.liftVal
  property := by
    let ⟨n, hn⟩ := le_iff_exists_add.mp (Nat.add_one_le_iff.mpr H.hlvl)
    induction n generalizing H with
    | zero => simp [Lift.liftVal, hn]
    | succ n ih =>
      specialize ih (H.take (2 * k + 1 + n) (by omega)); conv at ih => simp [hn]
      rcases n with _ | n
      · simp at hn; simp [Lift.liftVal, ← hn]; simp [hn]
      · rw [H.liftVal.eq_take_concat (2 * k + 1 + (n + 1))
            (by
              first
              | done
              |
                (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
                      simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
                        simp_lengths] <;>
                    omega))]
        have hnat : 2 * k + 1 + (n + 1) = (2 * k + 2) + n := by omega
        conv => simp [-List.take_append_getElem]
        use ih; constructor
        · conv => simp [getTree_eq' _ ih, hn]
          simp_rw [hnat]
          rw [List.drop_take]
          convert take_mem (n := n + 1) ⟨_, H.conLong⟩ using 1
          · rw [List.take_take]
            rw [show min (2 * k + 2) (2 * k + 2 + n) = 2 * k + 2 by omega]
            exact congrArg (getTree' hyp) (H.liftVal_take_short (by omega))
          · have hdrop : n < (List.drop (2 * k + 2) H.x.val).length :=
              by
              simp [hn]
              omega
            rw [show H.x.val[2 * k + 2 + n] = (H.x.val.drop (2 * k + 2))[n]'hdrop by
                rw [List.getElem_drop']]
            rw [← List.take_concat_get' (List.drop (2 * k + 2) H.x.val) n hdrop]
            congr 1
            rw [show 2 * k + 2 + n - (2 * k + 2) = n by omega]
        · split_ifs
          ·
            first
            | done
            |
              (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
                    simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
                      simp_lengths] <;>
                  omega)
          ·
            first
            | done
            |
              (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
                    simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
                      simp_lengths] <;>
                  omega)
          · conv => lhs; unfold Lift.liftVal
            conv => simp [hn]
            rw [List.getElem_append_right
                (by
                  first
                  | done
                  |
                    (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
                          simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
                            simp_lengths] <;>
                        omega)),
              getTree_eq' _ ih]
            conv => simp (disch := omega) [List.take_take, hnat]
            congr 2
            rw [List.drop_take]
            rw [show 2 * k + 2 + n - (2 * k + 2) = n by omega]
            have hdrop : n < (List.drop (2 * k + 2) H.x.val).length :=
              by
              simp [hn]
              omega
            rw [← List.take_concat_get' (List.drop (2 * k + 2) H.x.val) n hdrop]
            congr 1
            rw [List.getElem_drop']


-- @@ L447-447 verbatim
lemma lift_lift : treeHom hyp H.lift = H.x := tree_ext H.liftVal_lift

-- @@ L448-448 verbatim
attribute [simp_lengths] lift_coe

-- @@ L449-449 verbatim
end Lift'


-- @@ L451-451 verbatim
namespace PreLift

-- @@ L452-452 verbatim
variable (H : PreLift hyp)

-- @@ L453-458 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps toPreLift liftTree] def extend --weird simps! error message
  (S : QuasiStrategy (subAt G.tree (H.x.val.take (2 * k + 1))) Player.one) : Lift hyp where
  toPreLift := H
  liftTree := S.1.subtree
  htree := ⟨S, rfl⟩

-- @@ L459-459 verbatim
attribute [simp_lengths] extend_toPreLift

-- @@ L460-461 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def WonPos := {u | ∃ S, (H.extend S).PreWonPos u}

-- @@ L462-465 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps -isSimp] def game : Game A where
  tree := subAt G.tree (H.x.val.take (2 * k + 1))
  payoff := Subtype.val ⁻¹' ⋃ u ∈ H.WonPos, principalOpen u

-- @@ L466-467 verbatim
lemma game_open : IsOpen H.game.payoff := IsOpen.preimage
  continuous_subtype_val (isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ principalOpen_isOpen _)

-- @@ L468-474 verbatim
lemma extend_take h S : (H.take n h).extend S =
  (H.extend (cast (by simp [List.take_take, h]) S)).take n h := by
  ext1
  · rfl
  · simp only [extend_liftTree, Lift.take_liftTree]
    symm
    apply cast_subtree (by simp [List.take_take, h]) rfl

-- @@ L475-477 verbatim
@[simp] lemma wonPos_take h : (H.take n h).WonPos = H.WonPos := by
  ext; conv => simp [WonPos, extend_take]
  generalize_proofs pf; rw [(cast_bijective pf).surjective.exists]

-- @@ L478-479 verbatim
@[simp] lemma game_take h : (H.take n h).game = H.game := by
  ext1 <;> simp [game, List.take_take, h]

-- @@ L480-481 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def Won := ∃ u ∈ H.WonPos, u <+: H.x.val.drop (2 * k + 1)

-- @@ L482-483 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def Winnable := WinningPrefix H.game Player.zero (H.x.val.drop (2 * k + 1))

-- @@ L484-485 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def Losable' := ¬ WinningPrefix H.game Player.zero (H.x.val.drop (2 * k + 1))

-- @@ L486-486 verbatim
end PreLift


-- @@ L488-488 verbatim
end «Section1»

-- @@ L489-489 verbatim
end GaleStewartGame.BorelDet.One
