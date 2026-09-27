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
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific


-- @@ L19-23 verbatim
/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.Zero.PreLift

Auxiliary declarations for the Borel determinacy formalization.
-/


-- @@ L25-25 verbatim
@[expose] public section



-- @@ L28-28 verbatim
namespace GaleStewartGame.BorelDet.Zero

-- @@ L29-29 verbatim
open Stream'.Discrete Descriptive Tree Game PreStrategy

-- @@ L30-30 verbatim
open CategoryTheory


-- @@ L32-32 verbatim
variable {A : Type*} {G : Game A} {k : ℕ} {hyp : Hyp G k} {m n : ℕ}


-- @@ L34-34 verbatim
noncomputable section «Section1»


-- @@ L36-43 verbatim
variable (hyp) in
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[ext] structure PreLift where
  /-- Auxiliary declaration for the Borel determinacy formalization. -/
  x : G.tree
  hlvl : 2 * k < x.val.length (α := no_index _)
  /-- Auxiliary declaration for the Borel determinacy formalization. -/
  R : ResStrategy (gameAsTrees hyp) Player.zero (2 * k)

-- @@ L44-44 verbatim
variable (H : PreLift hyp)

-- @@ L45-45 verbatim
namespace PreLift

-- @@ L46-46 verbatim
attribute [simp] hlvl

-- @@ L47-48 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
lemma hlvl_le : 2 * k + 1 ≤ H.x.val.length (α := no_index _) := by simp

-- @@ L49-49 verbatim
@[simp] lemma hlvl' : 2 * k ≤ H.x.val.length (α := no_index _) := by linarith [H.hlvl]

-- @@ L50-56 verbatim
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
lemma pInv_take_length :
    (pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val.length (α := no_index _) = 2 * k := by
  rw [pInv_treeHom_val]
  · change (pInvTreeHomMap hyp (List.take (2 * k) H.x.val)).length = 2 * k
    simp_all
  · simp

-- @@ L57-64 verbatim
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
lemma pInv_take_position :
    IsPosition (pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val Player.zero := by
  rw [pInv_treeHom_val]
  · change (pInvTreeHomMap hyp (List.take (2 * k) H.x.val)).length % 2 =
      Player.zero.toNat
    simp_all
  · simp

-- @@ L65-68 verbatim
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
lemma pInv_take_length_le :
    (pInv (treeHom hyp) (Tree.take (2 * k) H.x)).val.length (α := no_index _) ≤ 2 * k := by
  rw [H.pInv_take_length]

-- @@ L69-72 verbatim
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def liftShort : gameTree hyp := (H.R (pInv (treeHom hyp) (Tree.take (2 * k) H.x))
  H.pInv_take_position H.pInv_take_length_le).valT'

-- @@ L73-82 verbatim
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
@[simp, simp_lengths] lemma liftShort_length :
  H.liftShort.val.length (α := no_index _) = 2 * k + 1 := by
  have hlen := ExtensionsAt.val'_length
    (H.R (pInv (treeHom hyp) (Tree.take (2 * k) H.x))
      H.pInv_take_position H.pInv_take_length_le)
  change
    (H.R (pInv (treeHom hyp) (Tree.take (2 * k) H.x))
      H.pInv_take_position H.pInv_take_length_le).val'.length = 2 * k + 1
  rw [hlen, H.pInv_take_length]

-- @@ L83-87 verbatim
lemma getTree_fair {y} {a} (hy : y ∈ getTree' hyp H.liftShort.val)
  (hp : IsPosition y Player.zero) (ha : H.liftShort.val.map Prod.fst ++ (y ++ [a]) ∈ G.tree) :
  y ++ [a] ∈ getTree' hyp H.liftShort.val := by
  obtain ⟨S, hS⟩ := T'_snd_medium' H.liftShort H.liftShort_length
  simp_rw [hS] at hy ⊢; rwa [S.1.subtree_fair ⟨y, hy⟩ hp]


-- @@ L89-92 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps -isSimp] def game : Game A where
  tree := getTree' hyp H.liftShort.val
  payoff := Subtype.val ⁻¹' (Subtype.val '' (G.residual (H.x.val.take (2 * k + 1))).payoffᶜ)

-- @@ L93-94 verbatim
lemma game_tree_sub : H.game.tree ≤ subAt G.tree (H.liftShort.val.map Prod.fst) :=
  getTree_sub H.liftShort

-- @@ L95-95 verbatim
lemma game_pruned : IsPruned H.game.tree := (getTree_ne_and_pruned _).2

-- @@ L96-103 expanded
lemma game_closed : IsClosed H.game.payoff :=
  by
  apply IsClosed.preimage continuous_subtype_val
  apply
    (Topology.IsClosedEmbedding.subtypeVal
        (body_isClosed (G.residual (H.x.val.take (2 * k + 1))).tree)).isClosed_iff_image_isClosed.mp
  rw [G.residual_payoff_odd _
      (by have := H.hlvl;
        first
        | done
        |
          (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
                simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
                  simp_lengths] <;>
              omega))]
  change IsClosed ((body.append (H.x.val.take (2 * k + 1)) ⁻¹' G.payoff)ᶜᶜ)
  convert hyp.closed.preimage (body.append_con (H.x.val.take (2 * k + 1))) using 1
  simp_all


-- @@ L105-109 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def take (n : ℕ) (h : 2 * k < n) : PreLift hyp where
  x := Tree.take n H.x
  hlvl := by simp [h]
  R := H.R

-- @@ L110-111 verbatim
lemma take_of_length_le {h} (h' : H.x.val.length ≤ n) : H.take n h = H := by
  ext1 <;> [ext1; skip] <;> simp [h']

-- @@ L112-113 verbatim
@[simp] lemma take_rfl : H.take (H.x.val.length (α := no_index _)) H.hlvl = H :=
  H.take_of_length_le le_rfl

-- @@ L114-116 verbatim
@[simp] lemma take_trans hm hn : (H.take m hm).take n hn
  = H.take (min m n) (by as_aux_lemma => omega) := by
  ext1 <;> simp [min_comm]

-- @@ L117-134 verbatim
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
@[simp] lemma liftShort_take h : (H.take n h).liftShort = H.liftShort := by
  have harg : pInv (treeHom hyp) (Tree.take (2 * k) (H.take n h).x) =
      pInv (treeHom hyp) (Tree.take (2 * k) H.x) := by
    ext1
    rw [pInv_treeHom_val]
    · rw [pInv_treeHom_val]
      · change pInvTreeHomMap hyp (List.take (2 * k) (List.take n H.x.val)) =
          pInvTreeHomMap hyp (List.take (2 * k) H.x.val)
        rw [List.take_take]
        rw [min_eq_left (by omega : 2 * k ≤ n)]
      · simp
    · simp
  apply tree_ext
  exact congrArg Subtype.val
    (ResStrategy.eval_valT'_congr' H.R H.R rfl
      (pInv (treeHom hyp) (Tree.take (2 * k) (H.take n h).x))
      (pInv (treeHom hyp) (Tree.take (2 * k) H.x)) harg _ _)

-- @@ L135-150 verbatim
@[simp] lemma game_take h : (H.take n h).game = H.game := by
  have hprefixTake : (H.take n h).x.val.take (2 * k + 1) = H.x.val.take (2 * k + 1) := by
    change List.take (2 * k + 1) (List.take n H.x.val) = H.x.val.take (2 * k + 1)
    rw [List.take_take, min_eq_left (by omega : 2 * k + 1 ≤ n)]
  have htree : (H.take n h).game.tree = H.game.tree := by
    rw [game_tree, game_tree, H.liftShort_take h]
  apply Game.ext'
  · exact htree
  · rw [game_payoff, game_payoff, hprefixTake]
    ext x
    constructor <;> rintro ⟨y, hy, rfl⟩
    · refine ⟨⟨y.val, ?_⟩, hy, rfl⟩
      rw [← htree]
      exact y.prop
    · refine ⟨⟨y.val, ?_⟩, hy, rfl⟩
      simp_all


-- @@ L152-153 verbatim
@[simps] instance : LE (PreLift hyp) where
  le p q := q.take p.x.val.length p.hlvl = p

-- @@ L154-156 verbatim
lemma length_mono {p q : PreLift hyp} (h : p ≤ q) : p.x.val.length ≤ q.x.val.length := by
  -- This is not registered as a `gcongr` lemma because of the dependent projections.
  rw [← h]; simp

-- @@ L157-163 verbatim
instance : PartialOrder (PreLift hyp) where
  le_refl := by simp
  le_trans _ _ _ pq qr := by have := length_mono pq; rw [← qr] at pq; simpa [this] using pq
  le_antisymm _ _ pq qp := by
    ext1 <;> [ext1; skip] <;> rw [← pq]
    · simpa using length_mono qp
    · simp

-- @@ L164-168 verbatim
lemma take_le {h} : H.take n h ≤ H := by
  dsimp [LE.le]
  ext1
  · simp_all
  · rfl

-- @@ L169-170 verbatim
lemma take_le_take hm hn : H.take m hm ≤ H.take n hn ↔ m ≤ n ∨ H.x.val.length ≤ n := by
  (conv => lhs; dsimp [LE.le]); simp [PreLift.ext_iff]


-- @@ L172-173 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def ConShort := H.x.val[2 * k]'H.hlvl = H.liftShort.val[2 * k].1

-- @@ L174-175 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simp] lemma conShort_iff_take h : (H.take n h).ConShort ↔ H.ConShort := by simp [ConShort]

-- @@ L176-177 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def ConLong := H.x.val.drop (2 * k + 1) ∈ H.game.tree

-- @@ L178-179 verbatim
lemma conLong_take {h} (h' : H.ConLong) : (H.take n h).ConLong := by
  simpa [PreLift.ConLong, List.drop_take] using take_mem ⟨_, h'⟩

-- @@ L180-180 verbatim
end PreLift

-- @@ L181-185 verbatim
variable (hyp) in
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[ext (flat := false)] structure Lift extends PreLift hyp where
  h'lvl : 2 * k + 1 < toPreLift.x.val.length (α := no_index _)
  conShort : toPreLift.ConShort

-- @@ L186-190 verbatim
instance : PartialOrder (Lift hyp) where
  le p q := p.toPreLift ≤ q.toPreLift
  le_refl _ := le_rfl (α := PreLift hyp)
  le_trans _ _ _ := le_trans (α := PreLift hyp)
  le_antisymm _ _ pq qp := Lift.ext (le_antisymm pq qp)

-- @@ L191-191 verbatim
namespace Lift

-- @@ L192-192 verbatim
variable (H : Lift hyp)

-- @@ L193-194 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def Lost' := G.WonPosition H.x.val (Player.one.residual H.x.val)

-- @@ L195-196 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def Losable := H.ConLong ∧ WinningPrefix H.game Player.one (H.x.val.drop (2 * k + 1))

-- @@ L197-198 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def Winnable := ¬ WinningPrefix H.game Player.one (H.x.val.drop (2 * k + 1))

-- @@ L199-200 verbatim
lemma Winnable.conLong (h : H.Winnable) : H.ConLong := Classical.byContradiction fun h' ↦
  h (winningPrefix_of_notMem H.game Player.one h')


-- @@ L202-202 verbatim
attribute [simp] h'lvl

-- @@ L203-203 verbatim
@[simp] lemma h'lvl_le : 2 * k + 2 ≤ H.x.val.length (α := no_index _) := by have := H.h'lvl; omega

-- @@ L204-218 verbatim
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
@[simp] lemma liftShort_val_map :
  H.liftShort.val.map (α := no_index _) Prod.fst = H.x.val.take (2 * k + 1) := by
  rw [H.liftShort.val.eq_take_concat (2 * k) (by simp)]
  conv => rhs; rw [(H.x.val.take (2 * k + 1)).eq_take_concat (2 * k) (by simp),
    List.getElem_take, H.conShort]
  rw [List.map_append, List.map_singleton]
  congr 1
  unfold PreLift.liftShort
  simp only [ExtensionsAt.valT'_coe]
  erw [ExtensionsAt.val'_take_of_eq _ H.toPreLift.pInv_take_length.symm]
  change (treeHom hyp (pInv (treeHom hyp) (Tree.take (2 * k) H.x))).val =
    List.take (2 * k) (List.take (2 * k + 1) H.x.val)
  rw [cancel_pInv_right]
  simp [List.take_take]

-- @@ L219-220 verbatim
lemma liftShort_lift : treeHom hyp H.liftShort = Tree.take (2 * k + 1) H.x :=
  tree_ext H.liftShort_val_map

-- @@ L221-222 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def liftNode : A := H.x.val[2 * k + 1]


-- @@ L224-228 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps toPreLift] def take (n : ℕ) (h : 2 * k + 2 ≤ n) : Lift hyp where
  toPreLift := H.toPreLift.take n (by omega)
  h'lvl := by simpa
  conShort := by simpa using H.conShort

-- @@ L229-230 verbatim
lemma take_of_length_le {h} (h' : H.x.val.length ≤ n) : H.take n h = H := by
  ext1; apply PreLift.take_of_length_le <;> omega

-- @@ L231-232 verbatim
@[simp] lemma take_rfl : H.take (H.x.val.length (α := no_index _)) H.h'lvl = H :=
  H.take_of_length_le le_rfl

-- @@ L233-234 verbatim
@[simp] lemma take_trans hm hn : (H.take m hm).take n hn = H.take (min m n) (by simp [*]) := by
  ext1; simp

-- @@ L235-235 verbatim
@[simp] lemma liftNode_take h : (H.take n h).liftNode = H.liftNode := by simp [liftNode]

-- @@ L236-237 verbatim
lemma eq_take_of_le {p q : Lift hyp} (h : p ≤ q) :
  q.take p.x.val.length (by simp) = p := Lift.ext h

-- @@ L238-238 verbatim
lemma take_le {h} : H.take n h ≤ H := H.toPreLift.take_le (h := by omega)

-- @@ L239-240 verbatim
lemma take_le_take hm hn : H.take m hm ≤ H.take n hn ↔ m ≤ n ∨ H.x.val.length ≤ n :=
  H.toPreLift.take_le_take (by omega) (by omega)

-- @@ L241-241 verbatim
end Lift


-- @@ L243-247 verbatim
variable (hyp) in
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[ext (flat := false)] structure WLLift extends Lift hyp where
  /-- Auxiliary declaration for the Borel determinacy formalization. -/
  liftTree : tree A

-- @@ L248-251 verbatim
instance : Preorder (WLLift hyp) where
  le p q := p.toLift ≤ q.toLift
  le_refl _ := le_rfl (α := Lift hyp)
  le_trans _ _ _ := le_trans (α := Lift hyp)

-- @@ L252-252 verbatim
namespace WLLift


-- @@ L254-254 verbatim
variable (H : WLLift hyp)

-- @@ L255-256 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def liftMediumVal : List (upA hyp) := H.liftShort.val ++ [⟨H.liftNode, H.liftTree⟩]

-- @@ L257-259 verbatim
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
@[simp, simp_lengths] lemma liftMediumVal_length :
  H.liftMediumVal.length (α := no_index _) = 2 * k + 2 := by simp [liftMediumVal]

-- @@ L260-262 verbatim
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
@[simp] lemma getTree_liftMediumVal : getTree' hyp H.liftMediumVal = H.liftTree := by
  simp [liftMediumVal]

-- @@ L263-272 verbatim
@[simp] lemma liftMediumVal_map : H.liftMediumVal.map Prod.fst = H.x.val.take (2 * k + 2) := by
  calc
    H.liftMediumVal.map Prod.fst = H.liftShort.val.map Prod.fst ++ [H.liftNode] := by
      rw [liftMediumVal]
      exact List.map_append ..
    _ = H.x.val.take (2 * k + 1) ++ [H.x.val[2 * k + 1]] := by
      rw [H.liftShort_val_map]
      rfl
    _ = H.x.val.take (2 * k + 2) := by
      simp_all


-- @@ L274-276 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def liftVal := H.liftMediumVal ++
  (H.x.val.drop (2 * k + 2)).zipInitsMap (fun a y ↦ ⟨a, subAt H.liftTree y⟩)

-- @@ L277-278 verbatim
@[simp] lemma liftVal_take_medium : H.liftVal.take (2 * k + 2) = H.liftMediumVal := by
  simp [liftVal]

-- @@ L279-280 verbatim
@[simp] lemma liftVal_take_short : H.liftVal.take (2 * k + 1) = H.liftShort.val := by
  simp [liftVal, liftMediumVal]

-- @@ L281-297 verbatim
@[simp] lemma liftVal_lift : H.liftVal.map Prod.fst = H.x.val := by
  let tail : List (upA hyp) :=
    (H.x.val.drop (2 * k + 2)).zipInitsMap (fun a y ↦ ⟨a, subAt H.liftTree y⟩)
  change List.map Prod.fst (H.liftMediumVal ++ tail) = H.x.val
  calc
    List.map Prod.fst (H.liftMediumVal ++ tail) =
        H.liftMediumVal.map Prod.fst ++ tail.map Prod.fst :=
      List.map_append ..
    _ = H.liftMediumVal.map Prod.fst ++ H.x.val.drop (2 * k + 2) := by
      congr 1
      change List.map Prod.fst
          ((H.x.val.drop (2 * k + 2)).zipInitsMap fun a y ↦ (a, subAt H.liftTree y)) =
        H.x.val.drop (2 * k + 2)
      rw [← List.zipInitsMap_map]
      simp
    _ = H.x.val := by
      simp_all

-- @@ L298-301 verbatim
@[simp, simp_lengths] lemma liftVal_length : H.liftVal.length (α := no_index _)
  = H.x.val.length := by
  rw [← H.liftVal_lift]
  exact (List.length_map (f := Prod.fst) (as := H.liftVal)).symm

-- @@ L302-312 verbatim
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
@[simp] lemma liftVal_lift_get (h : n < H.liftVal.length) :
  H.liftVal[n].1 = H.x.val[n]'(by simpa using h) := by
  have hget := congrArg (fun xs => xs[n]?) H.liftVal_lift
  change (H.liftVal.map Prod.fst)[n]? = H.x.val[n]? at hget
  have hx : n < H.x.val.length := by simpa [H.liftVal_length] using h
  rw [List.getElem?_eq_getElem (by simpa [List.length_map] using h)] at hget
  rw [List.getElem?_eq_getElem hx] at hget
  have hget' := Option.some.inj hget
  rw [List.getElem_map] at hget'
  exact hget'

-- @@ L313-320 verbatim
attribute [local implicit_reducible] upA oldAsTrees gameAsTrees in
lemma liftVal_take_eq_of_tree {H H' : WLLift hyp} (h : H ≤ H') (ht : H.liftTree = H'.liftTree) :
  H.liftVal = H'.liftVal.take H.x.val.length := by
  simp_rw [WLLift.liftVal]
  obtain ⟨n, hn⟩ := le_iff_exists_add.mp (by simp : H'.liftMediumVal.length ≤ H.x.val.length)
  rw [hn, List.take_append]; congr 1
  · simp_rw [liftMediumVal, ht]; rw [← Lift.eq_take_of_le h]; simp
  · rw [List.zipInitsMap_take, List.take_drop, ht, ← Lift.eq_take_of_le h]; simp [hn]

-- @@ L321-321 verbatim
end WLLift


-- @@ L323-326 verbatim
variable (hyp) in
/-- Auxiliary declaration for the Borel determinacy formalization. -/
structure WLLift' extends WLLift hyp where
  hlift : toWLLift.liftVal ∈ gameTree hyp

-- @@ L327-327 verbatim
namespace WLLift'

-- @@ L328-328 verbatim
variable (H : WLLift' hyp)

-- @@ L329-330 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps coe] def lift : gameTree hyp := ⟨H.liftVal, H.hlift⟩

-- @@ L331-331 verbatim
attribute [simp_lengths] lift_coe

-- @@ L332-332 verbatim
lemma lift_lift : treeHom hyp H.lift = H.x := tree_ext H.liftVal_lift


-- @@ L334-334 verbatim
section «Section2»

-- @@ L335-343 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def extension (hp : IsPosition H.x.val Player.zero)
    (R : ResStrategy (gameAsTrees hyp) Player.zero H.x.val.length) :=
  R H.lift (by
    change H.liftVal.length % 2 = Player.zero.toNat
    rw [H.liftVal_length]
    exact hp) (by
    change H.liftVal.length ≤ H.x.val.length
    rw [H.liftVal_length])

-- @@ L344-347 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def extensionMap (hp : IsPosition H.x.val Player.zero)
    (R : ResStrategy (gameAsTrees hyp) Player.zero H.x.val.length) :=
  ExtensionsAt.map (treeHom hyp) H.lift_lift (H.extension hp R)

-- @@ L348-349 verbatim
variable (hp : IsPosition H.x.val Player.zero)
  (R : ResStrategy (gameAsTrees hyp) Player.zero H.x.val.length)

-- @@ L350-353 verbatim
@[simp] lemma extension_take :
  (H.extension hp R).val' (A := no_index _).take (α := no_index _)
    (H.x.val.length (α := no_index _))
  = H.liftVal := ExtensionsAt.val'_take_of_eq _ H.liftVal_length.symm

-- @@ L354-356 verbatim
@[simp] lemma extensionMap_take (h : n ≤ H.x.val.length) :
  (H.extensionMap hp R).val' (A := no_index _).take (α := no_index _) n
  = H.x.val.take n := ExtensionsAt.val'_take_of_le _ h

-- @@ L357-362 verbatim
@[simp] lemma extension_take_medium :
  (H.extension hp R).val'.take (α := no_index _) (2 * k + 2) = H.liftMediumVal := by
  have htake := congrArg (List.take (2 * k + 2)) (H.extension_take hp R)
  rw [List.take_take, min_eq_left H.h'lvl_le] at htake
  rw [← H.liftVal_take_medium]
  simpa [gameAsTrees] using htake

-- @@ L363-371 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def extensionPreLift : PreLift hyp where
  x := (H.extensionMap hp R).valT'
  R := H.R
  hlvl := by
    have hlen := ExtensionsAt.val'_length (H.extensionMap hp R)
    change 2 * k < (H.extensionMap hp R).val'.length
    rw [hlen]
    exact Nat.lt_of_lt_of_le (Nat.lt_trans (Nat.lt_succ_self _) H.h'lvl) (Nat.le_succ _)

-- @@ L372-372 verbatim
attribute [simp_lengths] extensionPreLift_x

-- @@ L373-378 expanded
@[simp]
lemma extensionPreLift_take :
    (H.extensionPreLift hp R).take (H.x.val.length (α := no_index _))
        (by have := H.hlvl;
          first
          | done
          |
            (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
                  simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
                    simp_lengths] <;>
                omega)) =
      H.toPreLift :=
  by
  ext1
  · exact ExtensionsAt.valT'_take _
  · rfl


-- @@ L379-380 verbatim
@[simp] lemma extensionPreLift_liftShort : (H.extensionPreLift hp R).liftShort = H.liftShort := by
  rw [← extensionPreLift_take, PreLift.liftShort_take]

-- @@ L381-383 expanded
@[simp]
lemma extensionPreLift_game : (H.extensionPreLift hp R).game = H.game :=
  by
  rw [←
    (H.extensionPreLift hp R).game_take (h := by have := H.hlvl;
      first
      | done
      |
        (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
              simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
                simp_lengths] <;>
            omega))]
  rw [extensionPreLift_take]


-- @@ L384-395 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps! toPreLift] def extensionLift : Lift hyp where
  toPreLift := H.extensionPreLift hp R
  h'lvl := by
    have hlen := ExtensionsAt.val'_length (H.extensionMap hp R)
    change 2 * k + 1 < (H.extensionMap hp R).val'.length
    rw [hlen]
    exact Nat.lt_of_lt_of_le H.h'lvl (Nat.le_succ _)
  conShort := by
    rw [← PreLift.conShort_iff_take, extensionPreLift_take]
    · exact H.conShort
    · exact H.hlvl

-- @@ L396-398 verbatim
@[simp] lemma extensionLift_take :
  (H.extensionLift hp R).take (H.x.val.length (α := no_index _)) (by simp) = H.toLift := by
  ext1; apply extensionPreLift_take

-- @@ L399-399 verbatim
end «Section2»

-- @@ L400-400 verbatim
end WLLift'

-- @@ L401-401 verbatim
end «Section1»

-- @@ L402-402 verbatim
end GaleStewartGame.BorelDet.Zero
