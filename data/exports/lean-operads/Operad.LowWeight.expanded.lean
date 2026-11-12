/-
# The convolution algebra of a binary operad in low weight

The deformation complexes of binary quadratic operads that one computes by hand live in weights
one to three: cochains on the corollas, on the two-vertex trees and on the three-vertex trees.
This file gives those trees names and computes the signed convolution product and the bracket
on them, for cochains with values in any non-symmetric operad `Q`:

* the corolla `cor e`, the two combs `lc e e'` (child in the first slot) and `rc e e'` (child in
  the second slot), and the five three-vertex trees `ll`, `lr`, `bl`, `rl`, `rr`; every tree of
  arity two, three and four is one of these (`OfArity.eq_cor`, `eq_lc_or_rc`, `cases_four`);
* `compFin` of two cochains at a factored tree (`compFin_apply_graft`) and away from any
  factorization (`compFin_apply_eq_zero`);
* the values of `f ⋆ₛ g` (weights one and one), `f ⋆ₛ θ` and `θ ⋆ₛ f` (weights one and two), and of
  the brackets `⁅f, g⁆ₛ = f ⋆ₛ g + g ⋆ₛ f` and `⁅f, θ⁆ₛ = f ⋆ₛ θ - θ ⋆ₛ f`, tree by tree.

These are the formulas for the Maurer–Cartan equation and the twisted differentials `d¹`, `d²`.
-/
import Operad.KoszulDual
import Operad.DG


-- @@ L22-22 verbatim
universe u v w


-- @@ L24-24 verbatim
namespace Operad


-- @@ L26-26 verbatim
open NSOperad BTree


-- @@ L28-28 verbatim
namespace BTree.OfArity


-- @@ L30-30 verbatim
variable {E : Type v}


-- @@ L32-33 verbatim
/-- The corolla of a generator. -/
abbrev cor (e : E) : OfArity E 2 := corolla e


-- @@ L35-36 verbatim
/-- The left comb: `e` with `e'` in its first slot. -/
def lc (e e' : E) : OfArity E 3 := ⟨node e (node e' leaf leaf) leaf, rfl⟩


-- @@ L38-39 verbatim
/-- The right comb: `e` with `e'` in its second slot. -/
def rc (e e' : E) : OfArity E 3 := ⟨node e leaf (node e' leaf leaf), rfl⟩


-- @@ L41-42 verbatim
/-- `((· ·) ·) ·` -/
def ll (e₁ e₂ e₃ : E) : OfArity E 4 := ⟨node e₁ (node e₂ (node e₃ leaf leaf) leaf) leaf, rfl⟩

-- @@ L43-44 verbatim
/-- `(· (· ·)) ·` -/
def lr (e₁ e₂ e₃ : E) : OfArity E 4 := ⟨node e₁ (node e₂ leaf (node e₃ leaf leaf)) leaf, rfl⟩

-- @@ L45-47 verbatim
/-- `(· ·) (· ·)`, with `e₂` on the left and `e₃` on the right. -/
def bl (e₁ e₂ e₃ : E) : OfArity E 4 :=
  ⟨node e₁ (node e₂ leaf leaf) (node e₃ leaf leaf), rfl⟩

-- @@ L48-49 verbatim
/-- `· ((· ·) ·)` -/
def rl (e₁ e₂ e₃ : E) : OfArity E 4 := ⟨node e₁ leaf (node e₂ (node e₃ leaf leaf) leaf), rfl⟩

-- @@ L50-51 verbatim
/-- `· (· (· ·))` -/
def rr (e₁ e₂ e₃ : E) : OfArity E 4 := ⟨node e₁ leaf (node e₂ leaf (node e₃ leaf leaf)), rfl⟩


-- @@ L53-54 verbatim
private lemma arity_eq_one_iff {t : BTree E} : t.arity = 1 ↔ t = leaf :=
  ⟨eq_leaf_of_arity_eq_one, fun h => h ▸ rfl⟩


-- @@ L56-67 verbatim
/-- Every tree of arity two is a corolla. -/
lemma eq_cor (t : OfArity E 2) : ∃ e, t = cor e := by
  obtain ⟨t, ht⟩ := t
  cases t with
  | leaf => simp [arity] at ht
  | node e l r =>
    simp only [arity_node] at ht
    have hl := arity_pos l
    have hr := arity_pos r
    obtain rfl := eq_leaf_of_arity_eq_one (show l.arity = 1 by omega)
    obtain rfl := eq_leaf_of_arity_eq_one (show r.arity = 1 by omega)
    exact ⟨e, rfl⟩


-- @@ L69-88 verbatim
/-- Every tree of arity three is a comb. -/
lemma eq_lc_or_rc (t : OfArity E 3) : (∃ e e', t = lc e e') ∨ ∃ e e', t = rc e e' := by
  obtain ⟨t, ht⟩ := t
  cases t with
  | leaf => simp [arity] at ht
  | node e l r =>
    simp only [arity_node] at ht
    have hl := arity_pos l
    have hr := arity_pos r
    by_cases h : l.arity = 1
    · obtain rfl := eq_leaf_of_arity_eq_one h
      obtain ⟨e', he'⟩ := eq_cor (⟨r, by simp at ht; omega⟩ : OfArity E 2)
      have : r = node e' leaf leaf := congrArg Subtype.val he'
      subst this
      exact Or.inr ⟨e, e', rfl⟩
    · obtain rfl := eq_leaf_of_arity_eq_one (show r.arity = 1 by omega)
      obtain ⟨e', he'⟩ := eq_cor (⟨l, by omega⟩ : OfArity E 2)
      have : l = node e' leaf leaf := congrArg Subtype.val he'
      subst this
      exact Or.inl ⟨e, e', rfl⟩


-- @@ L90-125 verbatim
/-- Every tree of arity four is one of the five shapes. -/
lemma cases_four (t : OfArity E 4) :
    (∃ e₁ e₂ e₃, t = ll e₁ e₂ e₃) ∨ (∃ e₁ e₂ e₃, t = lr e₁ e₂ e₃) ∨
    (∃ e₁ e₂ e₃, t = bl e₁ e₂ e₃) ∨ (∃ e₁ e₂ e₃, t = rl e₁ e₂ e₃) ∨
    (∃ e₁ e₂ e₃, t = rr e₁ e₂ e₃) := by
  obtain ⟨t, ht⟩ := t
  cases t with
  | leaf => simp [arity] at ht
  | node e₁ l r =>
    simp only [arity_node] at ht
    have hl := arity_pos l
    have hr := arity_pos r
    by_cases h1 : l.arity = 1
    · obtain rfl := eq_leaf_of_arity_eq_one h1
      rcases eq_lc_or_rc (⟨r, by simp at ht; omega⟩ : OfArity E 3) with ⟨e₂, e₃, h⟩ | ⟨e₂, e₃, h⟩
      · have : r = (lc e₂ e₃).1 := congrArg Subtype.val h
        subst this
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨e₁, e₂, e₃, rfl⟩)))
      · have : r = (rc e₂ e₃).1 := congrArg Subtype.val h
        subst this
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨e₁, e₂, e₃, rfl⟩)))
    · by_cases h2 : l.arity = 2
      · obtain ⟨e₂, he₂⟩ := eq_cor (⟨l, h2⟩ : OfArity E 2)
        obtain ⟨e₃, he₃⟩ := eq_cor (⟨r, by omega⟩ : OfArity E 2)
        have hl' : l = node e₂ leaf leaf := congrArg Subtype.val he₂
        have hr' : r = node e₃ leaf leaf := congrArg Subtype.val he₃
        subst hl' hr'
        exact Or.inr (Or.inr (Or.inl ⟨e₁, e₂, e₃, rfl⟩))
      · obtain rfl := eq_leaf_of_arity_eq_one (show r.arity = 1 by omega)
        rcases eq_lc_or_rc (⟨l, by omega⟩ : OfArity E 3) with ⟨e₂, e₃, h⟩ | ⟨e₂, e₃, h⟩
        · have : l = (lc e₂ e₃).1 := congrArg Subtype.val h
          subst this
          exact Or.inl ⟨e₁, e₂, e₃, rfl⟩
        · have : l = (rc e₂ e₃).1 := congrArg Subtype.val h
          subst this
          exact Or.inr (Or.inl ⟨e₁, e₂, e₃, rfl⟩)


-- @@ L127-127 verbatim
/-! ### Telling the named trees apart -/


-- @@ L129-129 verbatim
section Distinct


-- @@ L131-131 verbatim
variable {a b c a' b' c' : E}


-- @@ L133-134 verbatim
@[simp] lemma lc_inj : lc a b = lc a' b' ↔ a = a' ∧ b = b' :=
  ⟨fun h => by simpa [lc] using congrArg Subtype.val h, fun ⟨h, h'⟩ => h ▸ h' ▸ rfl⟩


-- @@ L136-137 verbatim
@[simp] lemma rc_inj : rc a b = rc a' b' ↔ a = a' ∧ b = b' :=
  ⟨fun h => by simpa [rc] using congrArg Subtype.val h, fun ⟨h, h'⟩ => h ▸ h' ▸ rfl⟩


-- @@ L139-140 verbatim
@[simp] lemma lc_ne_rc : lc a b ≠ rc a' b' := fun h => by
  simpa [lc, rc] using congrArg Subtype.val h


-- @@ L142-143 verbatim
@[simp] lemma rc_ne_lc : rc a b ≠ lc a' b' := fun h => by
  simpa [lc, rc] using congrArg Subtype.val h


-- @@ L145-146 verbatim
@[simp] lemma ll_inj : ll a b c = ll a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' :=
  ⟨fun h => by simpa [ll] using congrArg Subtype.val h, fun ⟨h, h', h''⟩ => h ▸ h' ▸ h'' ▸ rfl⟩


-- @@ L148-149 verbatim
@[simp] lemma lr_inj : lr a b c = lr a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' :=
  ⟨fun h => by simpa [lr] using congrArg Subtype.val h, fun ⟨h, h', h''⟩ => h ▸ h' ▸ h'' ▸ rfl⟩


-- @@ L151-152 verbatim
@[simp] lemma bl_inj : bl a b c = bl a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' :=
  ⟨fun h => by simpa [bl] using congrArg Subtype.val h, fun ⟨h, h', h''⟩ => h ▸ h' ▸ h'' ▸ rfl⟩


-- @@ L154-155 verbatim
@[simp] lemma rl_inj : rl a b c = rl a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' :=
  ⟨fun h => by simpa [rl] using congrArg Subtype.val h, fun ⟨h, h', h''⟩ => h ▸ h' ▸ h'' ▸ rfl⟩


-- @@ L157-158 verbatim
@[simp] lemma rr_inj : rr a b c = rr a' b' c' ↔ a = a' ∧ b = b' ∧ c = c' :=
  ⟨fun h => by simpa [rr] using congrArg Subtype.val h, fun ⟨h, h', h''⟩ => h ▸ h' ▸ h'' ▸ rfl⟩


-- @@ L160-161 verbatim
@[simp] lemma ll_ne_lr : ll a b c ≠ lr a' b' c' := fun h => by
  simpa [ll, lr] using congrArg Subtype.val h

-- @@ L162-163 verbatim
@[simp] lemma ll_ne_bl : ll a b c ≠ bl a' b' c' := fun h => by
  simpa [ll, bl] using congrArg Subtype.val h

-- @@ L164-165 verbatim
@[simp] lemma ll_ne_rl : ll a b c ≠ rl a' b' c' := fun h => by
  simpa [ll, rl] using congrArg Subtype.val h

-- @@ L166-167 verbatim
@[simp] lemma ll_ne_rr : ll a b c ≠ rr a' b' c' := fun h => by
  simpa [ll, rr] using congrArg Subtype.val h

-- @@ L168-169 verbatim
@[simp] lemma lr_ne_ll : lr a b c ≠ ll a' b' c' := fun h => by
  simpa [ll, lr] using congrArg Subtype.val h

-- @@ L170-171 verbatim
@[simp] lemma lr_ne_bl : lr a b c ≠ bl a' b' c' := fun h => by
  simpa [lr, bl] using congrArg Subtype.val h

-- @@ L172-173 verbatim
@[simp] lemma lr_ne_rl : lr a b c ≠ rl a' b' c' := fun h => by
  simpa [lr, rl] using congrArg Subtype.val h

-- @@ L174-175 verbatim
@[simp] lemma lr_ne_rr : lr a b c ≠ rr a' b' c' := fun h => by
  simpa [lr, rr] using congrArg Subtype.val h

-- @@ L176-177 verbatim
@[simp] lemma bl_ne_ll : bl a b c ≠ ll a' b' c' := fun h => by
  simpa [bl, ll] using congrArg Subtype.val h

-- @@ L178-179 verbatim
@[simp] lemma bl_ne_lr : bl a b c ≠ lr a' b' c' := fun h => by
  simpa [bl, lr] using congrArg Subtype.val h

-- @@ L180-181 verbatim
@[simp] lemma bl_ne_rl : bl a b c ≠ rl a' b' c' := fun h => by
  simpa [bl, rl] using congrArg Subtype.val h

-- @@ L182-183 verbatim
@[simp] lemma bl_ne_rr : bl a b c ≠ rr a' b' c' := fun h => by
  simpa [bl, rr] using congrArg Subtype.val h

-- @@ L184-185 verbatim
@[simp] lemma rl_ne_ll : rl a b c ≠ ll a' b' c' := fun h => by
  simpa [rl, ll] using congrArg Subtype.val h

-- @@ L186-187 verbatim
@[simp] lemma rl_ne_lr : rl a b c ≠ lr a' b' c' := fun h => by
  simpa [rl, lr] using congrArg Subtype.val h

-- @@ L188-189 verbatim
@[simp] lemma rl_ne_bl : rl a b c ≠ bl a' b' c' := fun h => by
  simpa [rl, bl] using congrArg Subtype.val h

-- @@ L190-191 verbatim
@[simp] lemma rl_ne_rr : rl a b c ≠ rr a' b' c' := fun h => by
  simpa [rl, rr] using congrArg Subtype.val h

-- @@ L192-193 verbatim
@[simp] lemma rr_ne_ll : rr a b c ≠ ll a' b' c' := fun h => by
  simpa [rr, ll] using congrArg Subtype.val h

-- @@ L194-195 verbatim
@[simp] lemma rr_ne_lr : rr a b c ≠ lr a' b' c' := fun h => by
  simpa [rr, lr] using congrArg Subtype.val h

-- @@ L196-197 verbatim
@[simp] lemma rr_ne_bl : rr a b c ≠ bl a' b' c' := fun h => by
  simpa [rr, bl] using congrArg Subtype.val h

-- @@ L198-199 verbatim
@[simp] lemma rr_ne_rl : rr a b c ≠ rl a' b' c' := fun h => by
  simpa [rr, rl] using congrArg Subtype.val h


-- @@ L201-201 verbatim
end Distinct


-- @@ L203-203 verbatim
end BTree.OfArity


-- @@ L205-205 verbatim
namespace TConv


-- @@ L207-207 verbatim
open BTree.OfArity


-- @@ L209-210 verbatim
variable {R : Type u} [CommRing R] {E : Type v}
  {Q : ℕ → Type w} [∀ n, AddCommGroup (Q n)] [∀ n, Module R (Q n)] [NSOperad R Q]


-- @@ L212-222 verbatim
/-- **`compFin` of two cochains at a factored tree.** -/
lemma compFin_apply_graft {m n : ℕ} (i : Fin m) (f : TConv R E Q m) (g : TConv R E Q n)
    (t₁ : OfArity E m) (t₂ : OfArity E n) (t : OfArity E (m - 1 + n))
    (h : t₁.1.graft i t₂.1 = t.1) :
    compFin (R := R) i f g t = compFin (R := R) (P := Q) i (f t₁) (g t₂) := by
  have hi := i.isLt
  unfold compFin
  rw [reindex_apply, comp_apply]
  rw [compFun_eq (i : ℕ) (m - i - 1) _ g (OfArity.cast (by omega) t₁) t₂
    (by rw [OfArity.cast_val, OfArity.cast_val]; exact h), reindex_apply]
  simp only [OfArity.cast_cast, OfArity.cast_self]


-- @@ L224-233 verbatim
/-- **`compFin` of two cochains vanishes away from any factorization.** -/
lemma compFin_apply_eq_zero {m n : ℕ} (i : Fin m) (f : TConv R E Q m) (g : TConv R E Q n)
    (t : OfArity E (m - 1 + n))
    (h : ∀ (t₁ : OfArity E m) (t₂ : OfArity E n), t₁.1.graft i t₂.1 ≠ t.1) :
    compFin (R := R) i f g t = 0 := by
  have hi := i.isLt
  unfold compFin
  rw [reindex_apply, comp_apply]
  rw [compFun_eq_zero (i : ℕ) (m - i - 1) _ g (fun t₁ t₂ h' =>
    h (OfArity.cast (by omega) t₁) t₂ (by simpa using h')), map_zero]


-- @@ L235-240 verbatim
lemma sstar_apply {j k : ℕ} (f : TConv R E Q (j + 1)) (g : TConv R E Q (k + 1))
    (t : OfArity E (j + k + 1)) :
    sstar (R := R) f g t
      = ∑ a : Fin (j + 1), ((-1 : R) ^ ((a : ℕ) * k)) • compFin (R := R) a f g t := by
  rw [sstar_def, Finset.sum_apply]
  rfl


-- @@ L242-242 verbatim
/-! ## Evaluating composites along slices -/


-- @@ L244-244 verbatim
section Slices


-- @@ L246-246 verbatim
variable [Fintype E] [DecidableEq E]


-- @@ L248-254 verbatim
/-- The inner slice of a chain at a `Fin` slot of an outer tree. -/
def sliceIn {m n : ℕ} (i : Fin m) (t₁ : OfArity E m) (x : Chain R E (m - 1 + n)) : Chain R E n :=
  fun t₂ => x ⟨t₁.1.graft i t₂.1, by
    have h := arity_graft t₁.1 i t₂.1 (by rw [t₁.2]; exact i.isLt)
    rw [t₁.2, t₂.2] at h
    have := i.isLt
    omega⟩


-- @@ L256-262 verbatim
/-- The outer slice of a chain at an inner tree, for a `Fin` slot. -/
def sliceOut {m n : ℕ} (i : Fin m) (t₂ : OfArity E n) (x : Chain R E (m - 1 + n)) : Chain R E m :=
  fun t₁ => x ⟨t₁.1.graft i t₂.1, by
    have h := arity_graft t₁.1 i t₂.1 (by rw [t₁.2]; exact i.isLt)
    rw [t₁.2, t₂.2] at h
    have := i.isLt
    omega⟩


-- @@ L264-269 verbatim
lemma compFin_sum_left {m n : ℕ} (i : Fin m) {ι : Type*} (s : Finset ι) (F : ι → Q m) (y : Q n) :
    compFin (R := R) i (∑ k ∈ s, F k) y = ∑ k ∈ s, compFin (R := R) i (F k) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, compFin_add_left, ih]


-- @@ L271-276 verbatim
lemma compFin_sum_right {m n : ℕ} (i : Fin m) (x : Q m) {ι : Type*} (s : Finset ι) (F : ι → Q n) :
    compFin (R := R) i x (∑ k ∈ s, F k) = ∑ k ∈ s, compFin (R := R) i x (F k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, compFin_add_right, ih]


-- @@ L278-284 verbatim
/-- Grafting a pair of trees at a `Fin` slot. -/
def graftPair {m n : ℕ} (i : Fin m) (p : OfArity E m × OfArity E n) : OfArity E (m - 1 + n) :=
  ⟨p.1.1.graft i p.2.1, by
    have h := arity_graft p.1.1 i p.2.1 (by rw [p.1.2]; exact i.isLt)
    rw [p.1.2, p.2.2] at h
    have := i.isLt
    omega⟩


-- @@ L286-292 verbatim
omit [Fintype E] [DecidableEq E] in
lemma graftPair_injective {m n : ℕ} (i : Fin m) :
    Function.Injective (graftPair (E := E) (n := n) i) :=
  fun p q h => by
    have h' := BTree.graft_inj p.1.1 q.1.1 i p.2.1 q.2.1 (by rw [p.1.2]; exact i.isLt)
      (by rw [q.1.2]; exact i.isLt) (by rw [p.2.2, q.2.2]) (congrArg Subtype.val h)
    exact Prod.ext (Subtype.ext h'.1) (Subtype.ext h'.2)


-- @@ L294-304 verbatim
/-- A `compFin` of cochains, evaluated on a chain, as a sum over the factorizations. -/
lemma eval_compFin_pairs {m n : ℕ} (i : Fin m) (f : TConv R E Q m) (g : TConv R E Q n)
    (x : Chain R E (m - 1 + n)) :
    eval (compFin (R := R) i f g) x = ∑ p : OfArity E m × OfArity E n,
      sliceOut i p.2 x p.1 • compFin (R := R) (P := Q) i (f p.1) (g p.2) := by
  rw [eval_apply]
  refine (Fintype.sum_of_injective (graftPair i) (graftPair_injective i) _ _ (fun t ht => ?_)
    (fun p => ?_)).symm
  · rw [compFin_apply_eq_zero i f g t (fun t₁ t₂ h => ht ⟨(t₁, t₂), Subtype.ext h⟩), smul_zero]
  · rw [compFin_apply_graft i f g p.1 p.2 _ rfl]
    rfl


-- @@ L306-316 verbatim
/-- **Evaluating a `compFin` of cochains along inner slices.** -/
theorem eval_compFin_in {m n : ℕ} (i : Fin m) (f : TConv R E Q m) (g : TConv R E Q n)
    (x : Chain R E (m - 1 + n)) :
    eval (compFin (R := R) i f g) x
      = ∑ t₁, compFin (R := R) (P := Q) i (f t₁) (eval g (sliceIn i t₁ x)) := by
  rw [eval_compFin_pairs, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun t₁ _ => ?_
  rw [eval_apply, compFin_sum_right]
  refine Finset.sum_congr rfl fun t₂ _ => ?_
  rw [compFin_smul_right]
  rfl


-- @@ L318-327 verbatim
/-- **Evaluating a `compFin` of cochains along outer slices.** -/
theorem eval_compFin_out {m n : ℕ} (i : Fin m) (f : TConv R E Q m) (g : TConv R E Q n)
    (x : Chain R E (m - 1 + n)) :
    eval (compFin (R := R) i f g) x
      = ∑ t₂, compFin (R := R) (P := Q) i (eval f (sliceOut i t₂ x)) (g t₂) := by
  rw [eval_compFin_pairs, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun t₂ _ => ?_
  rw [eval_apply, compFin_sum_left]
  refine Finset.sum_congr rfl fun t₁ _ => ?_
  rw [compFin_smul_left]


-- @@ L329-335 verbatim
omit [NSOperad R Q] in
lemma eval_sum {n : ℕ} {ι : Type*} (s : Finset ι) (F : ι → TConv R E Q n) (x : Chain R E n) :
    eval (∑ k ∈ s, F k) x = ∑ k ∈ s, eval (F k) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, eval_add, ih]


-- @@ L337-346 verbatim
/-- **Evaluating the signed product**: the signed sum of its `compFin` terms. -/
theorem eval_sstar {j k : ℕ} (f : TConv R E Q (j + 1)) (g : TConv R E Q (k + 1))
    (x : Chain R E (j + k + 1)) :
    eval (sstar (R := R) f g) x
      = ∑ a : Fin (j + 1), ((-1 : R) ^ ((a : ℕ) * k)) • eval (compFin (R := R) a f g) x := by
  rw [sstar_def]
  show eval (∑ a : Fin (j + 1), ((-1 : R) ^ ((a : ℕ) * k)) •
    (compFin (R := R) a f g : TConv R E Q (j + k + 1))) x = _
  rw [eval_sum]
  exact Finset.sum_congr rfl fun a _ => eval_smul _ _ _


-- @@ L348-355 verbatim
/-- Summing over the trees of arity two is summing over the generators. -/
lemma sum_ofArity_two {M : Type*} [AddCommMonoid M] (F : OfArity E 2 → M) :
    ∑ t, F t = ∑ e, F (cor e) := by
  refine (Fintype.sum_bijective cor ⟨fun a b h => ?_, fun t => ?_⟩ _ _ fun _ => rfl).symm
  · have := congrArg Subtype.val h
    simpa [cor, corolla] using this
  · obtain ⟨e, rfl⟩ := eq_cor t
    exact ⟨e, rfl⟩


-- @@ L357-357 verbatim
/-! The slices of an arity-four chain at a corolla, on the named trees. -/


-- @@ L359-361 verbatim
section Named

-- The instances are needed by `sliceIn` and `sliceOut` in the statements, not by the proofs.

-- @@ L362-362 verbatim
set_option linter.unusedSectionVars false


-- @@ L364-364 verbatim
variable (x : Chain R E 4) (e p q : E)


-- @@ L366-367 verbatim
@[simp] lemma sliceOut_zero_lc : sliceOut (m := 3) (0 : Fin 3) (cor e) x (lc p q) = x (ll p q e) :=
  rfl

-- @@ L368-369 verbatim
@[simp] lemma sliceOut_one_lc : sliceOut (m := 3) (1 : Fin 3) (cor e) x (lc p q) = x (lr p q e) :=
  rfl

-- @@ L370-371 verbatim
@[simp] lemma sliceOut_two_lc : sliceOut (m := 3) (2 : Fin 3) (cor e) x (lc p q) = x (bl p q e) :=
  rfl

-- @@ L372-373 verbatim
@[simp] lemma sliceOut_zero_rc : sliceOut (m := 3) (0 : Fin 3) (cor e) x (rc p q) = x (bl p e q) :=
  rfl

-- @@ L374-375 verbatim
@[simp] lemma sliceOut_one_rc : sliceOut (m := 3) (1 : Fin 3) (cor e) x (rc p q) = x (rl p q e) :=
  rfl

-- @@ L376-377 verbatim
@[simp] lemma sliceOut_two_rc : sliceOut (m := 3) (2 : Fin 3) (cor e) x (rc p q) = x (rr p q e) :=
  rfl

-- @@ L378-379 verbatim
@[simp] lemma sliceIn_zero_lc : sliceIn (n := 3) (0 : Fin 2) (cor e) x (lc p q) = x (ll e p q) :=
  rfl

-- @@ L380-381 verbatim
@[simp] lemma sliceIn_zero_rc : sliceIn (n := 3) (0 : Fin 2) (cor e) x (rc p q) = x (lr e p q) :=
  rfl

-- @@ L382-383 verbatim
@[simp] lemma sliceIn_one_lc : sliceIn (n := 3) (1 : Fin 2) (cor e) x (lc p q) = x (rl e p q) :=
  rfl

-- @@ L384-385 verbatim
@[simp] lemma sliceIn_one_rc : sliceIn (n := 3) (1 : Fin 2) (cor e) x (rc p q) = x (rr e p q) :=
  rfl


-- @@ L387-387 verbatim
end Named


-- @@ L389-389 verbatim
end Slices


-- @@ L391-391 verbatim
/-! ## Weight one against weight one -/


-- @@ L393-393 verbatim
section Two


-- @@ L395-395 verbatim
variable (f g : TConv R E Q 2) (e e' : E)


-- @@ L397-404 verbatim
lemma sstar_apply_lc :
    sstar (R := R) (j := 1) (k := 1) f g (lc e e')
      = compFin (R := R) (P := Q) (0 : Fin 2) (f (cor e)) (g (cor e')) := by
  rw [sstar_apply, Fin.sum_univ_two, compFin_apply_graft 0 f g (cor e) (cor e') _ rfl,
    compFin_apply_eq_zero 1 f g _ (fun t₁ t₂ h => ?_)]
  · simp
  · obtain ⟨x, rfl⟩ := eq_cor t₁
    simp [lc, cor, corolla, graft_node] at h


-- @@ L406-417 verbatim
lemma sstar_apply_rc :
    sstar (R := R) (j := 1) (k := 1) f g (rc e e')
      = -compFin (R := R) (P := Q) (1 : Fin 2) (f (cor e)) (g (cor e')) := by
  rw [sstar_apply, Fin.sum_univ_two, compFin_apply_graft 1 f g (cor e) (cor e') _ rfl,
    compFin_apply_eq_zero 0 f g _ (fun t₁ t₂ h => ?_)]
  · simp
  · obtain ⟨x, rfl⟩ := eq_cor t₁
    obtain ⟨t₂, ht₂⟩ := t₂
    simp only [cor, corolla, Fin.val_zero, graft_node, arity_leaf, Nat.lt_one_iff, if_true,
      graft_leaf, rc, node.injEq] at h
    obtain ⟨_, rfl, _⟩ := h
    simp at ht₂


-- @@ L419-419 verbatim
end Two


-- @@ L421-421 verbatim
/-! ## Weight one against weight two -/


-- @@ L423-426 verbatim
section Three

-- The same shape comparison closes every non-factorization branch; the tree names it needs vary
-- from branch to branch, so the list is kept uniform.

-- @@ L427-427 verbatim
set_option linter.unusedSimpArgs false


-- @@ L429-429 verbatim
variable (f : TConv R E Q 2) (θ : TConv R E Q 3) (e₁ e₂ e₃ : E)


-- @@ L431-433 verbatim
private lemma graft_cor_zero (x : E) (s : BTree E) :
    (cor x).1.graft 0 s = node x s leaf := by
  simp [cor, corolla, graft_node]


-- @@ L435-437 verbatim
private lemma graft_cor_one (x : E) (s : BTree E) :
    (cor x).1.graft 1 s = node x leaf s := by
  simp [cor, corolla, graft_node]


-- @@ L439-447 verbatim
lemma sstar12_apply_ll :
    sstar (R := R) (j := 1) (k := 2) f θ (ll e₁ e₂ e₃)
      = compFin (R := R) (P := Q) (0 : Fin 2) (f (cor e₁)) (θ (lc e₂ e₃)) := by
  rw [sstar_apply, Fin.sum_univ_two, compFin_apply_graft 0 f θ (cor e₁) (lc e₂ e₃) _ rfl,
    compFin_apply_eq_zero 1 f θ _ (fun t₁ t₂ h => ?_)]
  · simp
  · obtain ⟨x, rfl⟩ := eq_cor t₁
    rw [Fin.val_one, graft_cor_one] at h
    simp [ll] at h


-- @@ L449-457 verbatim
lemma sstar12_apply_lr :
    sstar (R := R) (j := 1) (k := 2) f θ (lr e₁ e₂ e₃)
      = compFin (R := R) (P := Q) (0 : Fin 2) (f (cor e₁)) (θ (rc e₂ e₃)) := by
  rw [sstar_apply, Fin.sum_univ_two, compFin_apply_graft 0 f θ (cor e₁) (rc e₂ e₃) _ rfl,
    compFin_apply_eq_zero 1 f θ _ (fun t₁ t₂ h => ?_)]
  · simp
  · obtain ⟨x, rfl⟩ := eq_cor t₁
    rw [Fin.val_one, graft_cor_one] at h
    simp [lr] at h


-- @@ L459-466 verbatim
lemma sstar12_apply_bl : sstar (R := R) (j := 1) (k := 2) f θ (bl e₁ e₂ e₃) = 0 := by
  rw [sstar_apply, Fin.sum_univ_two, compFin_apply_eq_zero 0 f θ _ (fun t₁ t₂ h => ?_),
    compFin_apply_eq_zero 1 f θ _ (fun t₁ t₂ h => ?_)]
  · simp
  all_goals
    obtain ⟨x, rfl⟩ := eq_cor t₁
    simp only [Fin.val_zero, Fin.val_one, graft_cor_zero, graft_cor_one] at h
    simp [bl] at h


-- @@ L468-476 verbatim
lemma sstar12_apply_rl :
    sstar (R := R) (j := 1) (k := 2) f θ (rl e₁ e₂ e₃)
      = compFin (R := R) (P := Q) (1 : Fin 2) (f (cor e₁)) (θ (lc e₂ e₃)) := by
  rw [sstar_apply, Fin.sum_univ_two, compFin_apply_graft 1 f θ (cor e₁) (lc e₂ e₃) _ rfl,
    compFin_apply_eq_zero 0 f θ _ (fun t₁ t₂ h => ?_)]
  · simp
  · obtain ⟨x, rfl⟩ := eq_cor t₁
    rw [Fin.val_zero, graft_cor_zero] at h
    simp [rl] at h


-- @@ L478-486 verbatim
lemma sstar12_apply_rr :
    sstar (R := R) (j := 1) (k := 2) f θ (rr e₁ e₂ e₃)
      = compFin (R := R) (P := Q) (1 : Fin 2) (f (cor e₁)) (θ (rc e₂ e₃)) := by
  rw [sstar_apply, Fin.sum_univ_two, compFin_apply_graft 1 f θ (cor e₁) (rc e₂ e₃) _ rfl,
    compFin_apply_eq_zero 0 f θ _ (fun t₁ t₂ h => ?_)]
  · simp
  · obtain ⟨x, rfl⟩ := eq_cor t₁
    rw [Fin.val_zero, graft_cor_zero] at h
    simp [rr] at h


-- @@ L488-491 verbatim
private lemma graft_lc (x y e : E) (i : ℕ) :
    (lc x y).1.graft i (cor e).1 = if i = 0 then (ll x y e).1 else if i = 1 then (lr x y e).1
      else (bl x y e).1 := by
  rcases i with _ | _ | i <;> simp [lc, cor, corolla, graft_node, ll, lr, bl]


-- @@ L493-496 verbatim
private lemma graft_rc (x y e : E) (i : ℕ) :
    (rc x y).1.graft i (cor e).1 = if i = 0 then (bl x e y).1 else if i = 1 then (rl x y e).1
      else (rr x y e).1 := by
  rcases i with _ | _ | i <;> simp [rc, cor, corolla, graft_node, bl, rl, rr]


-- @@ L498-506 verbatim
/-- The factorizations of a three-vertex tree at a cherry. -/
private lemma factor_cherry (i : ℕ) (t₁ : OfArity E 3) (e : E) :
    (∃ x y, t₁ = lc x y ∧ t₁.1.graft i (cor e).1 = if i = 0 then (ll x y e).1
      else if i = 1 then (lr x y e).1 else (bl x y e).1) ∨
    (∃ x y, t₁ = rc x y ∧ t₁.1.graft i (cor e).1 = if i = 0 then (bl x e y).1
      else if i = 1 then (rl x y e).1 else (rr x y e).1) := by
  rcases eq_lc_or_rc t₁ with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩
  · exact Or.inl ⟨x, y, rfl, graft_lc x y e i⟩
  · exact Or.inr ⟨x, y, rfl, graft_rc x y e i⟩


-- @@ L508-518 verbatim
lemma sstar21_apply_ll :
    sstar (R := R) (j := 2) (k := 1) θ f (ll e₁ e₂ e₃)
      = compFin (R := R) (P := Q) (0 : Fin 3) (θ (lc e₁ e₂)) (f (cor e₃)) := by
  rw [sstar_apply, Fin.sum_univ_three, compFin_apply_graft 0 θ f (lc e₁ e₂) (cor e₃) _ rfl]
  rw [compFin_apply_eq_zero 1 θ f _ (fun t₁ t₂ h => ?_),
    compFin_apply_eq_zero 2 θ f _ (fun t₁ t₂ h => ?_)]
  · simp
  all_goals
    obtain ⟨e, rfl⟩ := eq_cor t₂
    rcases factor_cherry _ t₁ e with ⟨x, y, rfl, hg⟩ | ⟨x, y, rfl, hg⟩ <;>
      rw [hg] at h <;> simp [ll, lr, bl, rl, rr] at h


-- @@ L520-530 verbatim
lemma sstar21_apply_lr :
    sstar (R := R) (j := 2) (k := 1) θ f (lr e₁ e₂ e₃)
      = -compFin (R := R) (P := Q) (1 : Fin 3) (θ (lc e₁ e₂)) (f (cor e₃)) := by
  rw [sstar_apply, Fin.sum_univ_three, compFin_apply_graft 1 θ f (lc e₁ e₂) (cor e₃) _ rfl]
  rw [compFin_apply_eq_zero 0 θ f _ (fun t₁ t₂ h => ?_),
    compFin_apply_eq_zero 2 θ f _ (fun t₁ t₂ h => ?_)]
  · simp
  all_goals
    obtain ⟨e, rfl⟩ := eq_cor t₂
    rcases factor_cherry _ t₁ e with ⟨x, y, rfl, hg⟩ | ⟨x, y, rfl, hg⟩ <;>
      rw [hg] at h <;> simp [ll, lr, bl, rl, rr] at h


-- @@ L532-542 verbatim
lemma sstar21_apply_bl :
    sstar (R := R) (j := 2) (k := 1) θ f (bl e₁ e₂ e₃)
      = compFin (R := R) (P := Q) (0 : Fin 3) (θ (rc e₁ e₃)) (f (cor e₂))
        + compFin (R := R) (P := Q) (2 : Fin 3) (θ (lc e₁ e₂)) (f (cor e₃)) := by
  rw [sstar_apply, Fin.sum_univ_three, compFin_apply_graft 0 θ f (rc e₁ e₃) (cor e₂) _ rfl,
    compFin_apply_graft 2 θ f (lc e₁ e₂) (cor e₃) _ rfl]
  rw [compFin_apply_eq_zero 1 θ f _ (fun t₁ t₂ h => ?_)]
  · simp
  · obtain ⟨e, rfl⟩ := eq_cor t₂
    rcases factor_cherry _ t₁ e with ⟨x, y, rfl, hg⟩ | ⟨x, y, rfl, hg⟩ <;>
      rw [hg] at h <;> simp [ll, lr, bl, rl, rr] at h


-- @@ L544-554 verbatim
lemma sstar21_apply_rl :
    sstar (R := R) (j := 2) (k := 1) θ f (rl e₁ e₂ e₃)
      = -compFin (R := R) (P := Q) (1 : Fin 3) (θ (rc e₁ e₂)) (f (cor e₃)) := by
  rw [sstar_apply, Fin.sum_univ_three, compFin_apply_graft 1 θ f (rc e₁ e₂) (cor e₃) _ rfl]
  rw [compFin_apply_eq_zero 0 θ f _ (fun t₁ t₂ h => ?_),
    compFin_apply_eq_zero 2 θ f _ (fun t₁ t₂ h => ?_)]
  · simp
  all_goals
    obtain ⟨e, rfl⟩ := eq_cor t₂
    rcases factor_cherry _ t₁ e with ⟨x, y, rfl, hg⟩ | ⟨x, y, rfl, hg⟩ <;>
      rw [hg] at h <;> simp [ll, lr, bl, rl, rr] at h


-- @@ L556-566 verbatim
lemma sstar21_apply_rr :
    sstar (R := R) (j := 2) (k := 1) θ f (rr e₁ e₂ e₃)
      = compFin (R := R) (P := Q) (2 : Fin 3) (θ (rc e₁ e₂)) (f (cor e₃)) := by
  rw [sstar_apply, Fin.sum_univ_three, compFin_apply_graft 2 θ f (rc e₁ e₂) (cor e₃) _ rfl]
  rw [compFin_apply_eq_zero 0 θ f _ (fun t₁ t₂ h => ?_),
    compFin_apply_eq_zero 1 θ f _ (fun t₁ t₂ h => ?_)]
  · simp
  all_goals
    obtain ⟨e, rfl⟩ := eq_cor t₂
    rcases factor_cherry _ t₁ e with ⟨x, y, rfl, hg⟩ | ⟨x, y, rfl, hg⟩ <;>
      rw [hg] at h <;> simp [ll, lr, bl, rl, rr] at h


-- @@ L568-568 verbatim
end Three


-- @@ L570-570 verbatim
/-! ## The brackets -/


-- @@ L572-577 verbatim
/-- **The bracket of two weight-one cochains**: `⁅f, g⁆ₛ = f ⋆ₛ g + g ⋆ₛ f`. -/
lemma gbracket11_apply (f g : TConv R E Q 2) (t : OfArity E 3) :
    gbracket (R := R) (j := 1) (k := 1) f g t
      = sstar (R := R) (j := 1) (k := 1) f g t + sstar (R := R) (j := 1) (k := 1) g f t := by
  rw [gbracket, Pi.sub_apply, Pi.smul_apply, reindex_apply, reindex_self, OfArity.cast_self]
  norm_num


-- @@ L579-584 verbatim
/-- **The bracket of a weight-one and a weight-two cochain**: `⁅f, θ⁆ₛ = f ⋆ₛ θ - θ ⋆ₛ f`. -/
lemma gbracket12_apply (f : TConv R E Q 2) (θ : TConv R E Q 3) (t : OfArity E 4) :
    gbracket (R := R) (j := 1) (k := 2) f θ t
      = sstar (R := R) (j := 1) (k := 2) f θ t - sstar (R := R) (j := 2) (k := 1) θ f t := by
  rw [gbracket, Pi.sub_apply, Pi.smul_apply, reindex_apply, reindex_self]
  norm_num


-- @@ L586-586 verbatim
section EvalBracket


-- @@ L588-588 verbatim
variable [Fintype E] [DecidableEq E]


-- @@ L590-645 verbatim
omit [Fintype E] [DecidableEq E] in
/-- **Membership in the Koszul dual in arity four**, slice by slice: a chain on the three-vertex
trees lies in the Koszul dual exactly when its three outer slices and its two inner slices at
every corolla lie in the relation space. -/
theorem mem_koszulDual_four_iff (Rel : Submodule R (Chain R E 3)) (x : Chain R E 4) :
    x ∈ koszulDual Rel 4 ↔
      (∀ (a : Fin 3) (e : E), sliceOut (n := 2) a (cor e) x ∈ Rel) ∧
        (∀ (a : Fin 2) (e : E), sliceIn (n := 3) a (cor e) x ∈ Rel) := by
  have K3 := koszulDual_three Rel
  refine (mem_koszulDual_add_four Rel 0 x).trans ⟨fun h => ⟨fun a e => ?_, fun a e => ?_⟩,
    fun ⟨ho, hi⟩ a b k hk h2 hab => ?_⟩
  · rw [← K3]
    fin_cases a
    · have h1 := (h 0 2 2 rfl le_rfl (by norm_num)).1 (cor e)
      change sliceOut (n := 2) (0 : Fin 3) (cor e) x ∈ koszulDual Rel 3 at h1
      exact h1
    · have h1 := (h 1 1 2 rfl le_rfl (by norm_num)).1 (cor e)
      change sliceOut (n := 2) (1 : Fin 3) (cor e) x ∈ koszulDual Rel 3 at h1
      exact h1
    · have h1 := (h 2 0 2 rfl le_rfl (by norm_num)).1 (cor e)
      change sliceOut (n := 2) (2 : Fin 3) (cor e) x ∈ koszulDual Rel 3 at h1
      exact h1
  · rw [← K3]
    fin_cases a
    · have h1 := (h 0 1 3 rfl (by norm_num) (by norm_num)).2 (cor e)
      change sliceIn (n := 3) (0 : Fin 2) (cor e) x ∈ koszulDual Rel 3 at h1
      exact h1
    · have h1 := (h 1 0 3 rfl (by norm_num) (by norm_num)).2 (cor e)
      change sliceIn (n := 3) (1 : Fin 2) (cor e) x ∈ koszulDual Rel 3 at h1
      exact h1
  · have hk' : k = 2 ∨ k = 3 := by omega
    rcases hk' with rfl | rfl
    · have hab' : (a = 0 ∧ b = 2) ∨ (a = 1 ∧ b = 1) ∨ (a = 2 ∧ b = 0) := by omega
      refine ⟨fun t₂ => ?_, fun t₁ => mem_koszulDual_of_le_two Rel le_rfl _⟩
      obtain ⟨e, rfl⟩ := eq_cor t₂
      rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have h1 := ho 0 e
        rw [← K3] at h1
        exact h1
      · have h1 := ho 1 e
        rw [← K3] at h1
        exact h1
      · have h1 := ho 2 e
        rw [← K3] at h1
        exact h1
    · have hab' : (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by omega
      refine ⟨fun t₂ => mem_koszulDual_of_le_two Rel (by omega) _, fun t₁ => ?_⟩
      rcases hab' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · obtain ⟨e, rfl⟩ := eq_cor t₁
        have h1 := hi 0 e
        rw [← K3] at h1
        exact h1
      · obtain ⟨e, rfl⟩ := eq_cor t₁
        have h1 := hi 1 e
        rw [← K3] at h1
        exact h1


-- @@ L647-671 verbatim
/-- **The bracket of a weight-one and a weight-two cochain, evaluated along slices**: on an
arity-four chain, `⁅f, θ⁆ₛ` is `f` composed with `θ` evaluated on the two inner slices of each
corolla, minus `θ` evaluated on the three outer slices composed with `f`, with the sign of the
middle slot reversed. -/
theorem eval_gbracket12 (f : TConv R E Q 2) (θ : TConv R E Q 3) (x : Chain R E 4) :
    eval (gbracket (R := R) (j := 1) (k := 2) f θ) x
      = ∑ e, (compFin (R := R) (P := Q) (0 : Fin 2) (f (cor e))
            (eval θ (sliceIn (n := 3) (0 : Fin 2) (cor e) x))
          + compFin (R := R) (P := Q) (1 : Fin 2) (f (cor e))
            (eval θ (sliceIn (n := 3) (1 : Fin 2) (cor e) x)))
        - ∑ e, (compFin (R := R) (P := Q) (0 : Fin 3)
            (eval θ (sliceOut (n := 2) (0 : Fin 3) (cor e) x)) (f (cor e))
          - compFin (R := R) (P := Q) (1 : Fin 3)
            (eval θ (sliceOut (n := 2) (1 : Fin 3) (cor e) x)) (f (cor e))
          + compFin (R := R) (P := Q) (2 : Fin 3)
            (eval θ (sliceOut (n := 2) (2 : Fin 3) (cor e) x)) (f (cor e))) := by
  have hb : gbracket (R := R) (j := 1) (k := 2) f θ
      = sstar (R := R) (j := 1) (k := 2) f θ - sstar (R := R) (j := 2) (k := 1) θ f :=
    funext fun t => gbracket12_apply f θ t
  rw [hb, eval_sub, eval_sstar, eval_sstar, Fin.sum_univ_two, Fin.sum_univ_three,
    eval_compFin_in, eval_compFin_in, eval_compFin_out, eval_compFin_out, eval_compFin_out,
    sum_ofArity_two, sum_ofArity_two, sum_ofArity_two, sum_ofArity_two, sum_ofArity_two]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, zero_mul, one_mul, mul_one, pow_zero,
    pow_one, neg_one_sq, one_smul, neg_one_smul, sub_eq_add_neg]


-- @@ L673-673 verbatim
end EvalBracket


-- @@ L675-675 verbatim
end TConv


-- @@ L677-677 verbatim
end Operad
