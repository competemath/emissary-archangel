/-
Copyright (c) 2026 Sven Manthe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sven Manthe
-/
module

public import LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.TreeExtensions
public import LeanPool.AFormalizationOfBorelDeterminacyInLean.Tree.BodyFunctor
public import LeanPool.AFormalizationOfBorelDeterminacyInLean.Game.Strategies
import LeanPool.AFormalizationOfBorelDeterminacyInLean.Basic.Meta
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Order.Lattice.Nat
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow


-- @@ L20-24 verbatim
/-!
# LeanPool.AFormalizationOfBorelDeterminacyInLean.Proof.BuildLevelwise

Auxiliary declarations for the Borel determinacy formalization.
-/


-- @@ L26-26 verbatim
@[expose] public section



-- @@ L29-29 verbatim
namespace GaleStewartGame

-- @@ L30-30 verbatim
open CategoryTheory Descriptive Tree

-- @@ L31-31 verbatim
open Stream'.Discrete


-- @@ L33-33 verbatim
noncomputable section «Section1»

-- @@ L34-34 verbatim
variable {k m n : ℕ} {S T : Trees} {p : Player}

-- @@ L35-39 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[ext] structure BodySystemObj (T : Trees) where
  /-- Auxiliary declaration for the Borel determinacy formalization. -/
  res : ∀ k, (resEq k).obj T
  con : ∀ k, (res k).val <+: (res (k + 1)).val

-- @@ L40-50 verbatim
@[simp] lemma bodySystem_con' (x : BodySystemObj T) :
  (x.res k).val <+: (x.res m).val ↔ k ≤ m := by
  constructor <;> intro h
  · simpa using h.length_le
  · obtain ⟨n, rfl⟩ := le_iff_exists_add.mp h
    induction n with
    | zero => rfl
    | succ n ih =>
      trans
      · apply ih; omega
      · apply x.con

-- @@ L51-54 verbatim
@[simp] lemma bodySystem_take_val (x : BodySystemObj T) :
  (x.res k).val.take m = (x.res (k ⊓ m)).val := by
  rw [List.prefix_iff_eq_take.mp ((bodySystem_con' x).mpr (by simp : k ⊓ m ≤ k))]
  simp only [resEq_len, List.take_eq_take_iff, inf_le_left, min_eq_left, inf_comm]

-- @@ L55-57 verbatim
@[simp] lemma bodySystem_take (x : BodySystemObj T) :
  Tree.take m (resEq.val' (x.res k)) = resEq.val' (x.res (k ⊓ m)) := by
  ext; simp_rw [take_coe, resEq.val'_coe, bodySystem_take_val]

-- @@ L58-61 verbatim
lemma bodySystem_take' (x : BodySystemObj T) (h : m ≤ k) :
  (x.res k).val.take m = (x.res m).val := by
  rw [bodySystem_take_val]
  exact congrArg (fun j ↦ (x.res j).val) (inf_of_le_right h)

-- @@ L62-70 verbatim
/-- an isomorph of `bodyFunctor` that is more convenient to build levelwise -/
@[simps obj] def bodySystem : Trees ⥤ Type* where
  obj T := BodySystemObj T
  map {S T} f := TypeCat.ofHom fun x : BodySystemObj S ↦ ({
    res := fun k ↦ (resEq k).map f (x.res k)
    con := by intro _; simp_rw [resEq_map]; apply f.monotone; apply x.con
  } : BodySystemObj T)
  map_id _ := rfl
  map_comp _ _ := rfl

-- @@ L71-71 verbatim
namespace BodySystemObj

-- @@ L72-74 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev toObj (x : BodySystemObj T) : bodySystem.obj T :=
  cast (by dsimp [bodySystem] : BodySystemObj T = bodySystem.obj T) x

-- @@ L75-77 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev ofObj (x : bodySystem.obj T) : BodySystemObj T :=
  cast (by dsimp [bodySystem] : bodySystem.obj T = BodySystemObj T) x

-- @@ L78-80 verbatim
@[ext] lemma obj_ext {x y : bodySystem.obj T}
  (h : BodySystemObj.ofObj x = BodySystemObj.ofObj y) : x = y :=
  (Equiv.cast (by dsimp [bodySystem] : bodySystem.obj T = BodySystemObj T)).injective h

-- @@ L81-81 verbatim
end BodySystemObj

-- @@ L82-103 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def bodyEquivSystemApp (T : Trees) : body T.2 ≃ BodySystemObj T where
  toFun x := {
    res := fun k ↦ ⟨x.val.take k, by simp⟩
    con := by simp
  }
  invFun x := ⟨fun n ↦ (x.res (n + 1)).val.get ⟨n, by simp⟩, by
    intro y h; suffices y = (x.res y.length).val by simp only [this, resEq_mem]
    apply List.ext_getElem (by simp); intro n hn
    replace h := (principalOpen_index _ _).mp h
    conv => simp [hn]; rw [← h _ hn]
    apply List.IsPrefix.getElem; rw [bodySystem_con']; omega⟩
  left_inv x := by ext n; simp [Stream'.get]
  right_inv x := by
    ext1; ext1 n; ext1
    apply List.ext_getElem (by rw [Stream'.length_take, resEq_len])
    intro m hm h₂
    have hmn : m < n := by rwa [resEq_len] at h₂
    refine Eq.trans (Stream'.take_get m n _ ?_) ?_
    · rw [Stream'.length_take]; exact hmn
    · exact List.IsPrefix.getElem (xs := (x.res (m + 1)).val) (ys := (x.res n).val)
        ((bodySystem_con' x).mpr (by omega)) (by rw [resEq_len]; omega)

-- @@ L104-116 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps! -isSimp] def bodyEquivSystem : bodyFunctor ≅ bodySystem := NatIso.ofComponents
  (fun T ↦ eqToIso (by rfl : bodyFunctor.obj T = body T.2) ≪≫
    (bodyEquivSystemApp T).toIso ≪≫
    eqToIso (by dsimp [bodySystem] : BodySystemObj T = bodySystem.obj T)) (by
    intro S T f
    apply ConcreteCategory.hom_ext
    intro x
    apply BodySystemObj.obj_ext
    apply BodySystemObj.ext
    funext n
    apply resEq_ext
    convert bodyMap_restrict f x n using 1 <;> rfl)

-- @@ L117-118 verbatim
lemma bodyEquivSystem_hom_app_res_coe (x : bodyFunctor.obj T) :
  ((BodySystemObj.ofObj (bodyEquivSystem.hom.app T x)).res k).val = x.val.take k := rfl


-- @@ L120-120 verbatim
namespace BodySystemObj

-- @@ L121-123 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev contains (x : BodySystemObj T) (y : List T.1) :=
  y = (x.res y.length).val

-- @@ L124-126 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
abbrev containsTree (x : BodySystemObj T) (y : T) :=
  y = resEq.val' (x.res y.val.length)

-- @@ L127-131 verbatim
lemma bodySystem_contains_iff (x : BodySystemObj T) y :
  x.contains y.val ↔ x.containsTree y := by
  constructor
  · intro h; ext1; exact h
  · apply congr_arg

-- @@ L132-133 verbatim
lemma bodySystem_contains_iff' (x : BodySystemObj T) {z} (y : ExtensionsAt z) :
  x.contains y.val' ↔ x.containsTree y.valT' := bodySystem_contains_iff x y.valT'


-- @@ L135-139 verbatim
@[congr] --simp needs this
lemma res_val_congr (x y : BodySystemObj T) (h : x = y)
  (h' : m = n) : (x.res m).val = (y.res n).val := by
  subst h h'
  rfl

-- @@ L140-144 verbatim
@[congr] --how can this help if it is proven with congr?
lemma res_val'_congr (x y : BodySystemObj T) (h : x = y)
  (h' : m = n) : resEq.val' (x.res m) = resEq.val' (y.res n) := by
  subst h h'
  rfl

-- @@ L145-151 verbatim
lemma containsTree.map {x : BodySystemObj S} {y}
  (h : x.containsTree y) (f : S ⟶ T) :
  (BodySystemObj.ofObj (bodySystem.map f x.toObj)).containsTree (f y) := by
  rw [h]
  unfold BodySystemObj.containsTree BodySystemObj.ofObj BodySystemObj.toObj bodySystem
  simp [LenHom.h_length_simp]
  rfl

-- @@ L152-152 verbatim
end BodySystemObj


-- @@ L154-156 expanded
@[simp]
lemma IsPosition.iff_lenHom (p : Player) {S T : Trees} (f : S ⟶ T) x :
    IsPosition (A := no_index _) (f x).val p ↔ IsPosition x.val p := by
  first
  | done
  |
    (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
          simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
            simp_lengths] <;>
        omega)


-- @@ L157-159 expanded
@[simp]
lemma iff_pInv_lenHom (p : Player) {S T : Trees} (f : S ⟶ T) x (h : Fixing x.val.length f) :
    IsPosition (A := no_index _) (Tree.pInv f x h).val p ↔ IsPosition x.val p := by
  first
  | done
  |
    (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
          simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
            simp_lengths] <;>
        omega)


-- @@ L161-163 verbatim
/-- a strategy defined only on positions up to length k -/
def ResStrategy (T : Trees) (p : Player) (k : ℕ) :=
  ∀ x : T, IsPosition x.val p → x.val.length ≤ k → ExtensionsAt x

-- @@ L164-164 verbatim
namespace ResStrategy

-- @@ L165-166 verbatim
@[ext] lemma ext {S S' : ResStrategy T p k} (h : ∀ x hp hl, S x hp hl = S' x hp hl) : S = S' :=
  funext (fun x ↦ funext (fun hp ↦ funext (h x hp)))

-- @@ L167-171 verbatim
@[congr] --simp needs this
lemma eval_val'_congr' (S S' : ResStrategy T p k) (h : S = S')
  (x x' : T) (h' : x = x') hp hl :
  (S x hp hl).val' = (S' x' (by subst h'; exact hp) (by subst h'; exact hl)).val' := by
  congr!

-- @@ L172-176 verbatim
@[congr]
lemma eval_valT'_congr' (S S' : ResStrategy T p k) (h : S = S')
  (x x' : T) (h' : x = x') hp hl :
  (S x hp hl).valT' = (S' x' (by subst h'; exact hp) (by subst h'; exact hl)).valT' := by
  congr!

-- @@ L177-182 verbatim
@[congr]
lemma eval_val_congr' (S S' : ResStrategy T p k) (h : S = S')
  (x x' : T) (h' : x = x') hp hl :
  (S x hp hl).val = (S' x' (by subst h'; exact hp) (by subst h'; exact hl)).val := by
  subst h h'
  rfl

-- @@ L183-185 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def res (h : m ≤ k) (S : ResStrategy T p k) : ResStrategy T p m :=
  fun x hp hl ↦ S x hp (by omega)

-- @@ L186-186 verbatim
@[simp] lemma res_refl (S : ResStrategy T p k) : S.res le_rfl = S := rfl

-- @@ L187-188 verbatim
@[simp] lemma res_trans (m n k) (S : ResStrategy T p k) (mn : m ≤ n) (nk : n ≤ k) :
  (S.res nk).res mn = S.res (mn.trans nk) := rfl


-- @@ L190-194 expanded
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def fromMap (f : S ⟶ T)
    (h : Tree.Fixing k f := by
      as_aux_lemma =>
        first
        | done
        |
          simp (config := { failIfUnchanged := false }) only [simp_fixing, simp_lengths] at * <;>
              (try exact fixing_iso) <;>
            (apply Fixing.mon inferInstance;
              simp (config := { failIfUnchanged := false }) only [simp_fixing, simp_lengths] <;>
                omega))
    (S' : ResStrategy S p k) : ResStrategy T p k := fun x hx hl ↦
  ExtensionsAt.map f (x := pInv f x) (y := x) (by simp_rw [cancel_pInv_right])
    (S' _ (by simpa only [iff_pInv_lenHom]) (by simpa only [h_length_pInv]))


-- @@ L195-200 verbatim
@[congr] --simp needs this
lemma fromMap_congr {f g : S ⟶ T}
  (heq : f = g) (hh : Tree.Fixing k f) :
  ResStrategy.fromMap f hh =
    ResStrategy.fromMap (p := p) (f := g) (h := by subst heq; exact hh) := by
  congr! --could be generated automatically, propositional extensionality

-- @@ L201-205 expanded
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def fromMapInv (f : S ⟶ T)
    (h : Tree.Fixing (k + 1) f := by
      as_aux_lemma =>
        first
        | done
        |
          simp (config := { failIfUnchanged := false }) only [simp_fixing, simp_lengths] at * <;>
              (try exact fixing_iso) <;>
            (apply Fixing.mon inferInstance;
              simp (config := { failIfUnchanged := false }) only [simp_fixing, simp_lengths] <;>
                omega))
    (S' : ResStrategy T p k) : ResStrategy S p k := fun y hy hl ↦
  (@Tree.extensionsEquiv _ _ f y (h.mon (by simpa))).symm
    (S' _
      (by
        first
        | done
        |
          (focus repeat all_goals casesPlayer <;> (try apply_fun List.length at *) <;>
                simpAtStar (config := { failIfUnchanged := false }) only [simp_isPosition,
                  simp_lengths] <;>
              omega))
      (by simpa only [LenHom.h_length_simp]))


-- @@ L206-218 expanded
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def fromMapEquiv p k (f : S ⟶ T)
    (h : Tree.Fixing (k + 1) f := by
      as_aux_lemma =>
        first
        | done
        |
          simp (config := { failIfUnchanged := false }) only [simp_fixing, simp_lengths] at * <;>
              (try exact fixing_iso) <;>
            (apply Fixing.mon inferInstance;
              simp (config := { failIfUnchanged := false }) only [simp_fixing, simp_lengths] <;>
                omega)) :
    ResStrategy S p k ≃ ResStrategy T p k
    where
  toFun := fromMap f
  invFun := fromMapInv f
  left_inv
    S' := by
    ext1 x _ hl; apply ExtensionsAt.ext_valT'
    simp_rw [fromMapInv, fromMap, extensionsEquiv_symm_val', ExtensionsAt.map_valT',
      cancel_pInv_left]
  right_inv
    S' := by
    ext1; apply ExtensionsAt.ext_valT'
    simp_rw [fromMap, fromMapInv, ExtensionsAt.map_valT', extensionsEquiv_symm_val',
      cancel_pInv_right]


-- @@ L219-221 verbatim
@[simp] lemma res_fromMap {k m} (h : m ≤ k) (f : S ⟶ T) (hf : Fixing k f)
  (S' : ResStrategy S p k) : (fromMap f hf S').res h = (fromMap f) (S'.res h) := by
  ext1; apply ExtensionsAt.ext_valT'; simp [fromMap, res]

-- @@ L222-224 verbatim
@[simp] lemma fromMap_id k (S' : ResStrategy T p k) :
  (fromMap (𝟙 T)) S' = S' := by
  ext1; apply ExtensionsAt.ext_valT'; simp [fromMap]


-- @@ L226-232 expanded
@[simp]
lemma fromMap_comp k {S T U : Trees} (f : S ⟶ T) (g : T ⟶ U)
    (hf : Tree.Fixing k f := by
      as_aux_lemma =>
        first
        | done
        |
          simp (config := { failIfUnchanged := false }) only [simp_fixing, simp_lengths] at * <;>
              (try exact fixing_iso) <;>
            (apply Fixing.mon inferInstance;
              simp (config := { failIfUnchanged := false }) only [simp_fixing, simp_lengths] <;>
                omega))
    (hg : Tree.Fixing k g := by
      as_aux_lemma =>
        first
        | done
        |
          simp (config := { failIfUnchanged := false }) only [simp_fixing, simp_lengths] at * <;>
              (try exact fixing_iso) <;>
            (apply Fixing.mon inferInstance;
              simp (config := { failIfUnchanged := false }) only [simp_fixing, simp_lengths] <;>
                omega))
    (S' : ResStrategy S p k) : (fromMap (f ≫ g)) S' = (fromMap g hg) ((fromMap f hf) S') :=
  by
  ext1 x _ hl; apply ExtensionsAt.ext_valT'
  simp_rw [fromMap, ExtensionsAt.map_valT', CategoryTheory.comp_apply, ← pInv_comp']


-- @@ L233-235 verbatim
lemma fromMap_comp' k {S T U : Trees} (f : S ⟶ T) (g : T ⟶ U) --regression need
  (hf : Tree.Fixing k f) (hg : Tree.Fixing k g) (S' : ResStrategy S p k) :
  (fromMap (f ≫ g)) S' = (fromMap g hg) ((fromMap f hf) S') := fromMap_comp k f g hf hg S'

-- @@ L236-239 verbatim
@[simp] lemma fromMap_valT' {S T : Trees}
  (f : S ⟶ T) (hf : Tree.Fixing k f) (S' : ResStrategy S p k) x hx hl :
  (fromMap f hf S' (f x) (by simp [hx]) (by simp [hl])).valT' = f (S' x hx hl).valT' := by
  ext; simp_rw [fromMap, ExtensionsAt.map_valT', cancel_pInv_left]

-- @@ L240-240 verbatim
end ResStrategy


-- @@ L242-246 verbatim
/-- a strategy as an inverse limit of a sequence of `ResStrategy` -/
@[ext] structure StrategySystem (T : Trees) (p : Player) where
  /-- Auxiliary declaration for the Borel determinacy formalization. -/
  str : ∀ k, ResStrategy T p k
  con : ∀ k, (str (k + 1)).res (Nat.le_succ k) = str k

-- @@ L247-254 verbatim
@[simp] lemma StrategySystem.con' (S : StrategySystem T p) (h : k ≤ m) :
  (S.str m).res h = S.str k := by
  obtain ⟨n, rfl⟩ := le_iff_exists_add.mp h
  induction n with
  | zero => rfl
  | succ n ih =>
    simp_rw [← ih (by simp), Nat.add_succ, ← (S.str (k + n + 1)).res_trans k
      (k + n) (k + n + 1) (by omega) (by omega), S.con]

-- @@ L255-264 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
@[simps] def strategyEquivSystem : Strategy T.2 p ≃ StrategySystem T p where
  toFun S := {
    str := fun _ x h _ ↦ S x h
    con := fun _ ↦ rfl
  }
  invFun S x hp := S.str x.val.length x hp (by omega)
  left_inv _ := rfl
  right_inv S := by
    ext1; ext1; ext1 _ _ hl; simp_rw [← S.con' hl]; rfl


-- @@ L266-266 verbatim
section «Section2»

-- @@ L267-267 verbatim
variable {A : Type*} {T : tree A} {y : Stream' A}

-- @@ L268-279 verbatim
lemma preStrategy_body (f : PreStrategy T p) : y ∈ body f.subtree
  ↔ ∃ (hy : y ∈ body T), ∀ (x : T), (hp : IsPosition x.val p) → (hb : y ∈ principalOpen x.val) →
    ⟨y.get x.val.length, by apply hy; simp [principalOpen_concat, hb]⟩ ∈ f x hp := by
  constructor <;> intro h
  · use body_mono f.subtree_sub h
    intro x _ hy; specialize h (x ++ [y.get x.val.length]) (by simp [principalOpen_concat, hy])
    apply h.2 List.prefix_rfl
  · intro x hx; have hxT := h.1 _ hx
    use hxT; intro z a hpr hpo
    replace h := h.2 ⟨_, mem_of_append (mem_of_prefix hpr hxT)⟩ hpo
    replace hx := principalOpen_mono hpr hx; rw [principalOpen_concat] at hx
    obtain ⟨hx, rfl⟩ := hx; exact h hx

-- @@ L280-288 verbatim
lemma strategy_body (f : Strategy T p) : y ∈ body f.pre.subtree ↔ y ∈ body T ∧
  ∀ (x : T), (hp : IsPosition x.val p) → y ∈ principalOpen x.val →
  y.get x.val.length = (f x hp).val := by
  rw [preStrategy_body]
  constructor
  · rintro ⟨hy, h⟩
    exact ⟨hy, fun x hp hx ↦ congrArg Subtype.val (h x hp hx)⟩
  · rintro ⟨hy, h⟩
    exact ⟨hy, fun x hp hx ↦ ExtensionsAt.ext (h x hp hx)⟩

-- @@ L289-289 verbatim
end «Section2»

-- @@ L290-293 verbatim
/-- Auxiliary declaration for the Borel determinacy formalization. -/
def consistent (x : bodySystem.obj T) (S : StrategySystem T p) :=
  ∀ (y : T), (hp : IsPosition y.val p) → (BodySystemObj.ofObj x).contains y.val
  → (BodySystemObj.ofObj x).contains (S.str y.val.length y hp le_rfl).val'

-- @@ L294-300 verbatim
lemma mem_principalOpen_iff_bodySystem_contains {T : Trees} (x : List T.1) (y : body T.2) :
  y.val ∈ principalOpen x ↔
    (BodySystemObj.ofObj (bodyEquivSystem.hom.app _ y)).contains x := by
  constructor <;> intro h
  · apply List.ext_getElem?; intro n; rw [principalOpen_iff_restrict] at h
    exact congrArg (fun l ↦ l[n]?) h
  · rw [h]; exact extend_sub _ _

-- @@ L301-314 verbatim
lemma bodyEquivSystem_strat {x} (S : StrategySystem T p) :
  x.val ∈ body (strategyEquivSystem.symm S).pre.subtree
  ↔ consistent (bodyEquivSystem.hom.app _ x) S := by
  simp only [strategy_body, consistent]
  rw [and_iff_right x.prop]
  -- `congr!` needs the quantified form exposed here.
  change (∀ x : T, _) ↔ _
  congr! with y hp
  rw [mem_principalOpen_iff_bodySystem_contains y.val x]
  congr! with hc
  rw [← mem_principalOpen_iff_bodySystem_contains (S.str y.val.length y hp le_rfl).val' x,
    ExtensionsAt.val', principalOpen_concat,
    and_iff_right ((mem_principalOpen_iff_bodySystem_contains y.val x).mpr hc)]
  rfl

-- @@ L315-319 verbatim
lemma bodyEquivSystem_strat' {x} (S : StrategySystem T p) :
  (bodyEquivSystem.inv.app _ x).val ∈ body (strategyEquivSystem.symm S).pre.subtree
  ↔ consistent x S := by
  rw [bodyEquivSystem_strat]
  simp_all

-- @@ L320-323 verbatim
lemma bodyEquivSystem_strat'' {x} (S : Strategy T.2 p) :
  x.val ∈ body S.pre.subtree
  ↔ consistent (bodyEquivSystem.hom.app T x) (strategyEquivSystem S) :=
  bodyEquivSystem_strat (x := x) (strategyEquivSystem S)

-- @@ L324-324 verbatim
end «Section1»

-- @@ L325-325 verbatim
end GaleStewartGame
