import OAI.Combinatorics.Automata.Rank


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace OneWayLiveness


-- @@ L7-7 verbatim
namespace FiniteWiring

-- @@ L8-8 verbatim
variable {V C : Type*} (G : SimpleGraph V)


-- @@ L10-19 verbatim
/-- Only edge constraints in the starting component are needed. -/
lemma color_eq_of_reachable_from (color : V → C) (s : V)
    (hc : ∀ x y, G.Reachable s x → G.Adj x y → color x = color y)
    {y : V} (h : G.Reachable s y) : color s = color y := by
  obtain ⟨p⟩ := h
  have aux {x y : V} (p : G.Walk x y) (hx : G.Reachable s x) : color x = color y := by
    induction p with
    | nil => rfl
    | @cons x y z h p ih => exact (hc x y hx h).trans (ih (hx.trans h.reachable))
  exact aux p (.refl s)

-- @@ L20-20 verbatim
end FiniteWiring


-- @@ L22-22 verbatim
namespace Pairing

-- @@ L23-23 verbatim
open scoped Classical

-- @@ L24-24 verbatim
variable {A B : Type*} [Fintype A] [Fintype B]


-- @@ L26-30 verbatim
/-- Index the outer identity paths touched by a specified set of interface
edges. The definition is made once, independently of a replacement diagram. -/
noncomputable def marked (v : Pairing (A ⊕ B)) (u : Pairing (B ⊕ A)) (J : Finset B) : Finset A :=
  Finset.univ.filter fun x => ∃ i ∈ J,
    (glueGraph v u).Reachable (outer (.inl x)) (.inl (.inr i))


-- @@ L32-34 verbatim
@[simp] lemma mem_marked (v : Pairing (A ⊕ B)) (u : Pairing (B ⊕ A)) (J : Finset B) (x : A) :
    x ∈ marked v u J ↔ ∃ i ∈ J,
      (glueGraph v u).Reachable (outer (.inl x)) (.inl (.inr i)) := by simp [marked]


-- @@ L36-43 verbatim
lemma left_reachable_eq (v : Pairing (A ⊕ B)) (u : Pairing (B ⊕ A))
    (huv : compose v u = identity A) {x y : A}
    (h : (glueGraph v u).Reachable (outer (.inl x)) (outer (.inl y))) : x = y := by
  by_contra hne
  have hl : (compose v u).link (.inl x) (.inl y) :=
    ⟨fun he => hne (Sum.inl.inj he), h⟩
  rw [huv, identity_link] at hl
  cases hl


-- @@ L45-60 verbatim
lemma marked_card_le (v : Pairing (A ⊕ B)) (u : Pairing (B ⊕ A))
    (huv : compose v u = identity A) (J : Finset B) : (marked v u J).card ≤ J.card := by
  let f : {x // x ∈ marked v u J} → {i // i ∈ J} := fun x =>
    ⟨((mem_marked v u J x).mp x.property).choose,
     ((mem_marked v u J x).mp x.property).choose_spec.1⟩
  have hf (x : {x // x ∈ marked v u J}) :
      (glueGraph v u).Reachable (outer (.inl x.val)) (.inl (.inr (f x).val)) :=
    ((mem_marked v u J x).mp x.property).choose_spec.2
  have hinj : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply left_reachable_eq v u huv
    have hx := hf x
    rw [hxy] at hx
    exact hx.trans (hf y).symm
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj


-- @@ L62-116 verbatim
/-- Unmarked original identity paths retain their equality constraints
through every supported perturbation of the middle diagram. -/
lemma support_sandwich_subset_marked (v : Pairing (A ⊕ B)) (u : Pairing (B ⊕ A))
    (huv : compose v u = identity A) (J : Finset B) (a : Pairing (B ⊕ B))
    (ha : support a ⊆ J) : support (compose (compose v a) u) ⊆ marked v u J := by
  intro x hx
  by_contra hxm
  have hfix : (compose (compose v a) u).link (.inl x) (.inr x) := by
    apply link_of_color_eq _ Sum.inl_ne_inr
    intro c hc
    let f : A → Bool := fun y => c (.inl y)
    let g : A → Bool := fun y => c (.inr y)
    have hc' : (compose (compose v a) u).Compatible (Sum.elim f g) := by
      have he : Sum.elim f g = c := by funext y; cases y <;> rfl
      simpa only [he] using hc
    obtain ⟨β, hva, hu⟩ := (compose_compatible (compose v a) u f g).mp hc'
    obtain ⟨α, hv, hab⟩ := (compose_compatible v a f β).mp hva
    let col : ((A ⊕ B) ⊕ (B ⊕ A)) → Bool := Sum.elim (Sum.elim f α) (Sum.elim β g)
    have hab_eq (i : B) (hi : i ∉ J) : α i = β i := by
      have hs : i ∉ support a := fun his => hi (ha his)
      have hl : a.link (.inl i) (.inr i) := by simpa only [mem_support, not_not] using hs
      exact hab _ _ hl
    have hedge : ∀ y z, (glueGraph v u).Reachable (outer (.inl x)) y →
        (glueGraph v u).Adj y z → col y = col z := by
      intro y z hy hyz
      rcases y with (i | i) | (i | i) <;>
        rcases z with (j | j) | (j | j)
      · exact hv _ _ hyz
      · exact hv _ _ hyz
      · exact hyz.elim
      · exact hyz.elim
      · exact hv _ _ hyz
      · exact hv _ _ hyz
      · change i = j at hyz
        subst j
        exact hab_eq i (fun hi => hxm ((mem_marked v u J x).mpr ⟨i, hi, hy⟩))
      · exact hyz.elim
      · exact hyz.elim
      · change j = i at hyz
        subst j
        have hreach : (glueGraph v u).Reachable (outer (.inl x)) (.inl (.inr i)) :=
          hy.trans (show (glueGraph v u).Adj (.inr (.inl i)) (.inl (.inr i)) from rfl).reachable
        exact (hab_eq i (fun hi => hxm ((mem_marked v u J x).mpr ⟨i, hi, hreach⟩))).symm
      · exact hu _ _ hyz
      · exact hu _ _ hyz
      · exact hyz.elim
      · exact hyz.elim
      · exact hu _ _ hyz
      · exact hu _ _ hyz
    have hpath : (glueGraph v u).Reachable (outer (.inl x)) (outer (.inr x)) := by
      have hi : (compose v u).link (.inl x) (.inr x) := by
        rw [huv, identity_link]; rfl
      exact hi.2
    exact FiniteWiring.color_eq_of_reachable_from _ col _ hedge hpath
  exact (mem_support _ _).mp hx hfix


-- @@ L118-124 verbatim
/-- The simultaneous support estimate: a single small set works for every
middle diagram supported in the original set, including products and powers. -/
lemma common_support (v : Pairing (A ⊕ B)) (u : Pairing (B ⊕ A))
    (huv : compose v u = identity A) (J : Finset B) :
    ∃ K : Finset A, K.card ≤ J.card ∧ ∀ a : Pairing (B ⊕ B), support a ⊆ J →
      support (compose (compose v a) u) ⊆ K :=
  ⟨marked v u J, marked_card_le v u huv J, support_sandwich_subset_marked v u huv J⟩


-- @@ L126-126 verbatim
end Pairing


-- @@ L128-128 verbatim
namespace Pairing

-- @@ L129-129 verbatim
open scoped Classical

-- @@ L130-130 verbatim
variable {A : Type*} [Fintype A]

-- @@ L131-136 verbatim
noncomputable instance : Monoid (Pairing (A ⊕ A)) where
  mul := compose
  one := identity A
  mul_assoc := compose_assoc
  one_mul := identity_compose
  mul_one := compose_identity


-- @@ L138-138 verbatim
@[simp] lemma mul_eq_compose (a b : Pairing (A ⊕ A)) : a * b = compose a b := rfl

-- @@ L139-139 verbatim
@[simp] lemma one_eq_identity : (1 : Pairing (A ⊕ A)) = identity A := rfl


-- @@ L141-147 verbatim
lemma rank_one : rank (1 : Pairing (A ⊕ A)) = Fintype.card A := by
  unfold rank
  have hl : lefts (identity A) = Finset.univ := by
    ext i
    simp only [Finset.mem_univ, iff_true, mem_lefts]
    exact ⟨i, by simp [identity_link]⟩
  rw [one_eq_identity, hl, Finset.card_univ]


-- @@ L149-151 verbatim
lemma support_one : support (1 : Pairing (A ⊕ A)) = ∅ := by
  ext i
  simp [mem_support, identity_link]


-- @@ L153-154 verbatim
lemma rank_mul_le_left (a b : Pairing (A ⊕ A)) : rank (a * b) ≤ rank a :=
  rank_compose_le_left a b

-- @@ L155-156 verbatim
lemma rank_mul_le_right (a b : Pairing (A ⊕ A)) : rank (a * b) ≤ rank b :=
  rank_compose_le_right a b


-- @@ L158-170 verbatim
lemma full_rank_isUnit (a : Pairing (A ⊕ A)) (h : rank a = Fintype.card A) : IsUnit a := by
  have hl : lefts a = Finset.univ := Finset.eq_univ_of_card _ h
  have hr : lefts (flip a) = Finset.univ := by
    apply Finset.eq_univ_of_card
    have hs : lefts (flip a) = rights a := by
      ext i
      simp only [mem_lefts, mem_rights, flip_link, Sum.swap_inl, Sum.swap_inr]
      exact ⟨fun ⟨j, hj⟩ => ⟨j, a.symm hj⟩, fun ⟨j, hj⟩ => ⟨j, a.symm hj⟩⟩
    rw [hs, ← rank_eq_rights, h]
  refine ⟨⟨a, flip a, ?_, ?_⟩, rfl⟩
  · exact compose_flip_eq_identity a (by simp [hl])
  · change compose (flip a) a = identity A
    simpa only [flip_flip] using compose_flip_eq_identity (flip a) (by simp [hr])


-- @@ L172-177 verbatim
lemma rank_eq_card_of_isUnit (a : Pairing (A ⊕ A)) (h : IsUnit a) :
    rank a = Fintype.card A := by
  obtain ⟨u, rfl⟩ := h
  apply le_antisymm (rank_le_card _)
  have hr := rank_mul_le_left (u : Pairing (A ⊕ A)) (↑u⁻¹)
  simpa only [Units.val_inv_eq_inv_val, Units.mul_inv, rank_one] using hr


-- @@ L179-183 verbatim
lemma rank_mul_unit (a : Pairing (A ⊕ A)) (u : (Pairing (A ⊕ A))ˣ) :
    rank (a * (u : Pairing (A ⊕ A))) = rank a := by
  apply le_antisymm (rank_mul_le_left _ _)
  have hr := rank_mul_le_left (a * (u : Pairing (A ⊕ A))) (↑u⁻¹)
  simpa only [mul_assoc, Units.mul_inv, mul_one] using hr

-- @@ L184-188 verbatim
lemma rank_unit_mul (u : (Pairing (A ⊕ A))ˣ) (a : Pairing (A ⊕ A)) :
    rank ((u : Pairing (A ⊕ A)) * a) = rank a := by
  apply le_antisymm (rank_mul_le_right _ _)
  have hr := rank_mul_le_right (↑u⁻¹) ((u : Pairing (A ⊕ A)) * a)
  simpa only [← mul_assoc, Units.inv_mul, one_mul] using hr


-- @@ L190-191 verbatim
lemma support_mul_subset (a b : Pairing (A ⊕ A)) :
    support (a * b) ⊆ support a ∪ support b := support_compose_subset a b


-- @@ L193-198 verbatim
lemma support_pow_subset (a : Pairing (A ⊕ A)) (n : ℕ) : support (a ^ n) ⊆ support a := by
  induction n with
  | zero => simp only [pow_zero, support_one, Finset.empty_subset]
  | succ n ih =>
    rw [pow_succ]
    exact (support_mul_subset _ _).trans (Finset.union_subset ih (Finset.Subset.refl _))


-- @@ L200-204 verbatim
/-- Delete the prescribed caps of an idempotent.  Its retained left endpoints
are used as the smaller index set, avoiding an arbitrary numbering. -/
noncomputable def reduce (e z : Pairing (A ⊕ A)) :
    Pairing ({i // i ∈ lefts e} ⊕ {i // i ∈ lefts e}) :=
  compose (compose (splitRight e) z) (splitLeft e)


-- @@ L206-208 verbatim
noncomputable def expand (e : Pairing (A ⊕ A))
    (z : Pairing ({i // i ∈ lefts e} ⊕ {i // i ∈ lefts e})) : Pairing (A ⊕ A) :=
  compose (compose (splitLeft e) z) (splitRight e)


-- @@ L210-211 verbatim
lemma expand_reduce (e z : Pairing (A ⊕ A)) : expand e (reduce e z) = e * z * e := by
  simp only [expand, reduce, mul_eq_compose, compose_assoc, ← splitLeft_splitRight e]


-- @@ L213-218 verbatim
lemma reduce_expand (e : Pairing (A ⊕ A)) (he : e * e = e)
    (z : Pairing ({i // i ∈ lefts e} ⊕ {i // i ∈ lefts e})) :
    reduce e (expand e z) = z := by
  simp only [reduce, expand, compose_assoc]
  rw [← compose_assoc (splitRight e) (splitLeft e), splitRight_splitLeft e he,
    identity_compose, compose_identity]


-- @@ L220-225 verbatim
lemma splitRight_absorb (e : Pairing (A ⊕ A)) (he : e * e = e) :
    compose (splitRight e) e = splitRight e := by
  calc
    _ = compose (splitRight e) (compose (splitLeft e) (splitRight e)) :=
      congrArg (compose (splitRight e)) (splitLeft_splitRight e).symm
    _ = _ := by rw [← compose_assoc, splitRight_splitLeft e he, identity_compose]


-- @@ L227-232 verbatim
lemma splitLeft_absorb (e : Pairing (A ⊕ A)) (he : e * e = e) :
    compose e (splitLeft e) = splitLeft e := by
  calc
    _ = compose (compose (splitLeft e) (splitRight e)) (splitLeft e) :=
      congrArg (fun t => compose t (splitLeft e)) (splitLeft_splitRight e).symm
    _ = _ := by rw [compose_assoc, splitRight_splitLeft e he, compose_identity]


-- @@ L234-237 verbatim
lemma reduce_self (e : Pairing (A ⊕ A)) (he : e * e = e) : reduce e e = 1 := by
  unfold reduce
  rw [splitRight_absorb e he, splitRight_splitLeft e he]
  rfl


-- @@ L239-243 verbatim
lemma reduce_mul (e x y : Pairing (A ⊕ A)) (hxe : x * e = x) :
    reduce e (x * y) = reduce e x * reduce e y := by
  simp only [reduce, mul_eq_compose, compose_assoc]
  rw [← compose_assoc (splitLeft e), splitLeft_splitRight e,
    ← compose_assoc x e, ← mul_eq_compose x e, hxe]


-- @@ L245-250 verbatim
lemma reduce_sandwich (e a : Pairing (A ⊕ A)) (he : e * e = e) :
    reduce e (e * a * e) = reduce e a := by
  unfold reduce
  simp only [mul_eq_compose, compose_assoc]
  rw [← compose_assoc (splitRight e) e]
  rw [splitRight_absorb e he, splitLeft_absorb e he]


-- @@ L252-260 verbatim
lemma rank_reduce (e z : Pairing (A ⊕ A)) (hzl : e * z = z) (hzr : z * e = z) :
    rank (reduce e z) = rank z := by
  apply le_antisymm
  · exact (rank_compose_le_left _ _).trans (rank_compose_le_right _ _)
  · have heq : expand e (reduce e z) = z := by rw [expand_reduce, hzl, hzr]
    calc
      rank z = rank (expand e (reduce e z)) := congrArg rank heq.symm
      _ ≤ rank (compose (splitLeft e) (reduce e z)) := rank_compose_le_left _ _
      _ ≤ rank (reduce e z) := rank_compose_le_right _ _


-- @@ L262-266 verbatim
lemma reduce_injective (e : Pairing (A ⊕ A)) {x y : Pairing (A ⊕ A)}
    (hxl : e * x = x) (hxr : x * e = x) (hyl : e * y = y) (hyr : y * e = y)
    (h : reduce e x = reduce e y) : x = y := by
  have hh := congrArg (expand e) h
  simpa only [expand_reduce, hxl, hxr, hyl, hyr] using hh


-- @@ L268-275 verbatim
lemma reduce_common_support (e : Pairing (A ⊕ A)) (he : e * e = e) (J : Finset A) :
    ∃ K : Finset {i // i ∈ lefts e}, K.card ≤ J.card ∧
      ∀ a : Pairing (A ⊕ A), support a ⊆ J → support (reduce e (e * a * e)) ⊆ K := by
  obtain ⟨K, hK, hall⟩ := common_support (splitRight e) (splitLeft e)
    (splitRight_splitLeft e he) J
  refine ⟨K, hK, fun a ha => ?_⟩
  rw [reduce_sandwich e a he]
  exact hall a ha


-- @@ L277-278 verbatim
lemma card_reduced (e : Pairing (A ⊕ A)) : Fintype.card {i // i ∈ lefts e} = rank e :=
  Fintype.card_coe _

-- @@ L279-279 verbatim
end Pairing


-- @@ L281-281 verbatim
end OneWayLiveness


-- @@ L283-283 verbatim
end OAI
