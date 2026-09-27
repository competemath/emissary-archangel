/-
Copyright (c) 2026 Vincent Trélat. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Trélat
-/
module

public import Mathlib.Data.NNRat.Defs

public import LeanPool.ZFLean.Functions
import LeanPool.ZFLean.Tactics
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow


-- @@ L16-20 verbatim
/-!
# LeanPool.ZFLean.Sum

Imported Lean Pool material for `LeanPool.ZFLean.Sum`.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
universe u v


-- @@ L26-26 verbatim
namespace ZFSet


-- @@ L28-30 verbatim
/-- Imported ZFLean declaration. -/
def Sum (A B : ZFSet) :=
  {x // x ∈ (ZFSet.prod { ZFBool.false.val } A) ∪ (ZFSet.prod { ZFBool.true.val } B)}

-- @@ L31-32 verbatim
/-- Imported ZFLean declaration. -/
infixr:50 " ⊎ " => Sum


-- @@ L34-34 verbatim
namespace Sum

-- @@ L35-38 verbatim
/-- Imported ZFLean declaration. -/
def inl {A B : ZFSet} (a : {x // x ∈ A}) : Sum A B :=
  ⟨ZFSet.pair ZFBool.false a,
    mem_union.mpr (Or.inl <| pair_mem_prod.mpr ⟨mem_singleton.mpr rfl, a.prop⟩)⟩

-- @@ L39-42 verbatim
/-- Imported ZFLean declaration. -/
def inr {A B : ZFSet} (b : {x // x ∈ B}) : Sum A B :=
  ⟨ZFSet.pair ZFBool.true b,
    mem_union.mpr (Or.inr <| pair_mem_prod.mpr ⟨mem_singleton.mpr rfl, b.prop⟩)⟩


-- @@ L44-50 expanded
theorem _root_.ZFSet.Sum.inl.injEq {A B : ZFSet} {x y : { x // x ∈ A }} :
    (inl x : Sum A B) = inl y ↔ x = y := by
  constructor
  · intro heq
    injection heq with heq
    simp_all
  · simp_all


-- @@ L52-58 expanded
theorem _root_.ZFSet.Sum.inr.injEq {A B : ZFSet} {x y : { x // x ∈ B }} :
    (inr x : Sum A B) = inr y ↔ x = y := by
  constructor
  · intro heq
    injection heq with heq
    simp_all
  · simp_all


-- @@ L60-67 expanded
theorem cases {A B : ZFSet} (x : Sum A B) : x.val.π₂ ∈ A ∨ x.val.π₂ ∈ B :=
  by
  let ⟨x, hx⟩ := x
  rw [mem_union, mem_prod] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ | hx := hx
  · simp_all
  · rw [mem_prod] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    simp_all


-- @@ L68-117 expanded
/-- Imported ZFLean declaration. -/
@[cases_eliminator]
noncomputable def casesOn {A B : ZFSet.{u}} {motive : Sum A B → Sort v} (x : Sum A B)
    (inl : (val : { x // x ∈ A }) → motive (inl val))
    (inr : (val : { x // x ∈ B }) → motive (inr val)) : motive x :=
  by
  by_cases h : x.val.π₁ = ZFBool.false.val
  · have : x.val.π₂ ∈ A := by
      obtain ⟨x, hx⟩ := x
      rw [mem_union, mem_prod] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ | hx := hx
      · rwa [π₂_pair]
      · dsimp at h
        rw [pair_eta hx, pair_mem_prod, mem_singleton, h] at hx
        nomatch zftrue_ne_zffalse hx.1.symm
    have : x = Sum.inl ⟨x.val.π₂, this⟩ :=
      by
      obtain ⟨x, hx⟩ := x
      rw [mem_union, mem_prod] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ | hx := hx
      · rw [π₁_pair] at h
        subst a
        congr 2
        simp_all
      · rw [pair_eta hx, pair_mem_prod, mem_singleton, h] at hx
        nomatch zftrue_ne_zffalse hx.1.symm
    rw [this]
    apply inl
  · have x₁_eq_true : x.val.π₁ = ZFBool.true :=
      by
      have := Subtype.property x
      rw [mem_union, mem_prod] at this
      obtain ⟨a, ha, b, hb, eq⟩ | hx := this
      · simp_all
      · rw [pair_eta hx, pair_mem_prod, mem_singleton] at hx
        exact hx.1
    have : x.val.π₂ ∈ B := by
      obtain ⟨x, hx⟩ := x
      rw [mem_union, mem_prod] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ | hx := hx
      · simp_all
      · rw [pair_eta hx, pair_mem_prod, mem_singleton] at hx
        exact hx.2
    have : x = Sum.inr ⟨x.val.π₂, this⟩ :=
      by
      obtain ⟨x, hx⟩ := x
      rw [mem_union, mem_prod] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ | hx := hx
      · simp_all
      · congr
        conv_lhs => rw [pair_eta hx]
        simp_all
    rw [this]
    apply inr


-- @@ L119-129 expanded
@[simp]
theorem casesOn_of_inl {A B : ZFSet} {motive : Sum A B → Sort*} (a : { x // x ∈ A })
    (inl_case : (val : { x // x ∈ A }) → motive (inl val))
    (inr_case : (val : { x // x ∈ B }) → motive (inr val)) :
    casesOn (inl a) inl_case inr_case = inl_case a :=
  by
  rw [casesOn, dite_eq_left_of_eq_true (eq_true (by rw [inl, π₁_pair]))]
  dsimp
  rw [cast_eq_iff_heq]
  congr
  unfold inl
  rw [π₂_pair]


-- @@ L131-143 expanded
@[simp]
theorem casesOn_of_inr {A B : ZFSet} {motive : Sum A B → Sort*} (a : { x // x ∈ B })
    (inl_case : (val : { x // x ∈ A }) → motive (inl val))
    (inr_case : (val : { x // x ∈ B }) → motive (inr val)) :
    casesOn (inr a) inl_case inr_case = inr_case a :=
  by
  rw [casesOn, dite_eq_right_of_eq_false (eq_false ?_)]
  · dsimp
    rw [cast_eq_iff_heq]
    congr
    unfold inr
    rw [π₂_pair]
  · rw [inr, π₁_pair]
    exact zftrue_ne_zffalse


-- @@ L145-168 expanded
/-- The equivalence between the ZF disjoint sum and Lean's subtype sum. -/
noncomputable def instEquivSumSubtypeMem {A B : ZFSet} : Sum A B ≃ ({ x // x ∈ A } ⊕ { x // x ∈ B })
    where
  toFun
    x := by
    cases x with
    | inl a => exact _root_.Sum.inl a
    | inr b => exact _root_.Sum.inr b
  invFun
    x := by
    cases x with
    | inl a => exact inl a
    | inr b => exact inr b
  left_inv := by
    intro x
    cases x with
    | inl a =>
      beta_reduce
      conv_lhs => rw [casesOn_of_inl]
    | inr b =>
      beta_reduce
      conv_lhs => rw [casesOn_of_inr]
  right_inv := by
    intro x
    cases x with
    | inl a => simp only [casesOn_of_inl]
    | inr b => simp only [casesOn_of_inr]


-- @@ L170-170 verbatim
end Sum

-- @@ L171-172 expanded
/-- Imported ZFLean declaration. -/
def Option (S : ZFSet) :=
  Sum {∅} S


-- @@ L174-174 verbatim
instance {T : ZFSet} : Nonempty (Option T) := ⟨Sum.inl ⟨∅, mem_singleton.mpr rfl⟩⟩


-- @@ L176-176 verbatim
namespace Option

-- @@ L177-178 verbatim
/-- Imported ZFLean declaration. -/
abbrev none {S : ZFSet} : Option S := Sum.inl ⟨∅, mem_singleton.mpr rfl⟩

-- @@ L179-180 verbatim
/-- Imported ZFLean declaration. -/
abbrev some {S : ZFSet} (x : {x // x ∈ S}) : Option S := Sum.inr x


-- @@ L182-190 verbatim
theorem some_ne_none {S : ZFSet} (x : {x // x ∈ S}) : some x ≠ none := by
  unfold some Sum.inr none Sum.inl
  intro h
  injection h with h
  rw [ZFSet.pair_inj] at h
  unfold ZFBool.false ZFBool.true zftrue zffalse at h
  obtain ⟨contr, _⟩ := h
  simp_rw [ZFSet.ext_iff, notMem_empty, iff_false, mem_singleton] at contr
  nomatch contr ∅


-- @@ L192-217 verbatim
theorem casesOn {S : ZFSet} (x : Option S) : x = none ∨ (∃ y, x = some y) := by
  obtain ⟨x, hx⟩ := x
  rw [mem_union] at hx
  rcases hx with hx | hx <;> (
    rw [mem_prod] at hx
    obtain ⟨opt, hopt, val, hval, rfl⟩ := hx
    rw [mem_singleton] at hopt
    subst hopt
    rw [mem_union, pair_mem_prod] at hx)
  · left
    unfold none Sum.inl
    rw [mem_singleton] at hval
    subst val
    apply Subtype.ext
    rfl
  · right
    rcases hx with hx | hx
    · rw [mem_singleton] at hx
      absurd hx.left
      unfold ZFBool.false ZFBool.true zftrue zffalse
      intro contr
      simp_rw [ZFSet.ext_iff, notMem_empty, iff_false, mem_singleton] at contr
      nomatch contr ∅
    · rw [pair_mem_prod] at hx
      unfold some Sum.inr
      exists ⟨val, hx.right⟩


-- @@ L219-224 expanded
open Classical in
/-- Imported ZFLean declaration. -/
noncomputable abbrev the {S : ZFSet} (S_nemp : S ≠ ∅) (x : Option S) : { x // x ∈ S } :=
  if isNone : x = none then
    ⟨(Classical.epsilon fun z ↦ z ∈ ·) S, epsilon_spec (nonempty_exists_iff.mp S_nemp)⟩
  else choose (Or.resolve_left (casesOn x) isNone)


-- @@ L228-231 verbatim
open Classical in
/-- Convert a set-theoretic option to a Lean option of members of the underlying set. -/
noncomputable def into {T : ZFSet} : Option T → _root_.Option {x // x ∈ T} := fun x ↦
  if hx : x = none then .none else .some <| Classical.choose <| Or.resolve_left (casesOn x) hx


-- @@ L233-239 verbatim
theorem _root_.ZFSet.Option.some.injEq
    {T : ZFSet} {x y : {x // x ∈ T}} : some x = some y ↔ x = y := by
  constructor
  · intro heq
    injection heq with heq
    simp_all
  · simp_all


-- @@ L241-246 verbatim
theorem some_val_injEq {T : ZFSet} {x y : {x // x ∈ T}} :
    (some x).val = (some y).val ↔ x = y := by
  constructor
  · intro heq
    exact some.injEq.mp (Subtype.ext heq)
  · simp_all


-- @@ L248-252 verbatim
theorem ne_none_is_some {T : ZFSet} (x : Option T) : x ≠ none → ∃ y, x = some y := by
  intro h
  obtain ⟨y, hy⟩ := casesOn x
  · contradiction
  · assumption


-- @@ L254-265 verbatim
theorem _root_.ZFSet.Option.into.inj {T : ZFSet} :
    Function.Injective (into : Option T → _root_.Option {x // x ∈ T}) := by
  intro x y heq
  unfold into at heq
  split_ifs at heq with hx hy hy
  · rw [hx, hy]
  · injection heq with heq
    obtain ⟨x, rfl⟩ := ne_none_is_some x hx
    obtain ⟨y, rfl⟩ := ne_none_is_some y hy
    generalize_proofs px py at heq
    rw [Classical.choose_spec px, Classical.choose_spec py]
    congr


-- @@ L267-279 verbatim
theorem _root_.ZFSet.Option.into.surj {T : ZFSet} :
    Function.Surjective (into : Option T → _root_.Option {x // x ∈ T}) := by
  intro y
  unfold into
  cases y with
  | none =>
    simp_all
  | some v =>
    exists (some v)
    split_ifs with h
    · nomatch some_ne_none v h
    · generalize_proofs pv
      rw [← some.injEq.mp <| Classical.choose_spec pv]


-- @@ L281-282 verbatim
theorem _root_.ZFSet.Option.into.bij {T : ZFSet} :
  Function.Bijective (into : Option T → _root_.Option {x // x ∈ T}) := ⟨into.inj, into.surj⟩

-- @@ L283-286 verbatim
/-- Imported ZFLean declaration. -/
noncomputable def EmbeddingZFOptionOption {T : ZFSet} : Option T ↪ _root_.Option {x // x ∈ T} where
  toFun := into
  inj' := into.inj


-- @@ L288-294 verbatim
/-- The equivalence between ZF options and Lean options over a subtype. -/
noncomputable def instEquivZFOptionOption {T : ZFSet} :
    Option T ≃ _root_.Option {x // x ∈ T} where
  toFun := into
  invFun := Function.invFun into
  left_inv := Function.leftInverse_invFun into.inj
  right_inv := Function.rightInverse_invFun into.surj




-- @@ L298-301 verbatim
/-- Convert a Lean option of set members to the set-theoretic option encoding. -/
def outof {T : ZFSet} : _root_.Option {x // x ∈ T} → Option T
  | .some ⟨x, hx⟩ => some ⟨x, hx⟩
  | .none => none


-- @@ L303-327 verbatim
theorem _root_.ZFSet.Option.outof.inj {T : ZFSet} :
    Function.Injective (outof : _root_.Option {x // x ∈ T} → Option T) := by
  intro x y heq
  cases x <;> cases y <;> unfold outof at heq
  · rfl
  · injection heq with heq
    rw [pair_inj] at heq
    absurd heq.1
    unfold ZFBool.false ZFBool.true zftrue zffalse
    intro contr
    rw [Subtype.val_inj] at contr
    injection contr with contr
    rw [ZFSet.ext_iff] at contr
    exact (notMem_empty ∅) <| (mem_singleton.eq ▸ contr ∅).mpr rfl
  · injection heq with heq
    rw [pair_inj] at heq
    absurd heq.1
    unfold ZFBool.false ZFBool.true zftrue zffalse
    intro contr
    rw [Subtype.val_inj] at contr
    injection contr with contr
    rw [ZFSet.ext_iff] at contr
    exact (notMem_empty ∅) <| (mem_singleton.eq ▸ contr ∅).mp rfl
  · injection heq with heq
    simp_all


-- @@ L329-335 verbatim
theorem _root_.ZFSet.Option.outof.surj {T : ZFSet} :
    Function.Surjective (outof : _root_.Option {x // x ∈ T} → Option T) := by
  intro y
  unfold outof
  rcases y.casesOn with rfl | ⟨x, rfl⟩
  · exists .none
  · exists .some x


-- @@ L337-338 verbatim
theorem _root_.ZFSet.Option.outof.bij {T : ZFSet} :
  Function.Bijective (outof : _root_.Option {x // x ∈ T} → Option T) := ⟨outof.inj, outof.surj⟩

-- @@ L339-342 verbatim
/-- Imported ZFLean declaration. -/
def EmbeddingOptionZFOption {T : ZFSet} : _root_.Option {x // x ∈ T} ↪ Option T where
  toFun := outof
  inj' := outof.inj


-- @@ L344-350 verbatim
/-- The equivalence between Lean options over a subtype and ZF options. -/
noncomputable def instEquivOptionZFOption {T : ZFSet} :
    _root_.Option {x // x ∈ T} ≃ Option T where
  toFun := outof
  invFun := Function.invFun outof
  left_inv := Function.leftInverse_invFun outof.inj
  right_inv := Function.rightInverse_invFun outof.surj

-- @@ L351-353 verbatim
/-- Imported ZFLean declaration. -/
abbrev toZFSet (T : ZFSet) :
  ZFSet := (ZFSet.prod { ZFBool.false.val } {∅}) ∪ (ZFSet.prod { ZFBool.true.val } T)


-- @@ L355-373 expanded
open Classical in
/-- Imported ZFLean declaration. -/
noncomputable def flift {A B : ZFSet} (f : ZFSet)
    (hf : IsFunc A B f := by solve_by_elim using zfun) :
    { f' : ZFSet // IsFunc (Option.toZFSet A) (Option.toZFSet B) f' } :=
  let f' : ZFSet :=
    ZFSet.lambda (Option.toZFSet A) (Option.toZFSet B) fun x ↦
      if hx : x ∈ Option.toZFSet A then
        if isSome : ∃ y, ⟨x, hx⟩ = some y then
          let ⟨y, hy⟩ := Classical.choose isSome
          some (S := B) ((fapply f) ⟨y, by rwa [ZFSet.is_func_dom_eq]⟩) |>.val
        else none (S := B).val
      else ∅
  have hf' : IsFunc (Option.toZFSet A) (Option.toZFSet B) f' :=
    by
    apply ZFSet.lambda_isFunc
    intro x hx
    rw [dite_eq_left_of_eq_true (eq_true hx)]
    split_ifs with isSome <;> apply SetLike.coe_mem
  ⟨f', hf'⟩


-- @@ L375-516 verbatim
theorem flift_bijective {f A B : ZFSet} (hf : IsFunc A B f) :
    (ZFSet.Option.flift f).val.IsBijective (Subtype.property _) ↔ f.IsBijective hf where
  mp := by
    rintro ⟨hinj, hsurj⟩
    and_intros
    · intro x y z hx hy hz xz yz
      specialize hinj (Option.some ⟨x, hx⟩).val (Option.some ⟨y, hy⟩).val (Option.some ⟨z, hz⟩).val
        (SetLike.coe_mem _) (SetLike.coe_mem _) (SetLike.coe_mem _) ?_ ?_
      · rw [flift, lambda_spec]
        have hsome_x_mem :
            (Option.some ⟨x, hx⟩).val ∈ Option.toZFSet A := SetLike.coe_mem _
        have hsome_z_mem :
            (Option.some ⟨z, hz⟩).val ∈ Option.toZFSet B := SetLike.coe_mem _
        refine ⟨hsome_x_mem, hsome_z_mem, ?_⟩
        rw [dite_eq_left_of_eq_true (eq_true hsome_x_mem)]
        split_ifs with isSome
        · have chosen_eq : Classical.choose isSome = ⟨x, hx⟩ :=
            (some_val_injEq.mp
              (congrArg Subtype.val (Classical.choose_spec isSome))).symm
          rw [chosen_eq]
          apply congrArg Subtype.val
          apply ZFSet.Option.some.injEq.mpr
          symm
          exact fapply.of_pair _ xz
        · exfalso
          apply isSome
          exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
      · rw [flift, lambda_spec]
        have hsome_y_mem :
            (Option.some ⟨y, hy⟩).val ∈ Option.toZFSet A := SetLike.coe_mem _
        have hsome_z_mem :
            (Option.some ⟨z, hz⟩).val ∈ Option.toZFSet B := SetLike.coe_mem _
        refine ⟨hsome_y_mem, hsome_z_mem, ?_⟩
        rw [dite_eq_left_of_eq_true (eq_true hsome_y_mem)]
        split_ifs with isSome
        · have chosen_eq : Classical.choose isSome = ⟨y, hy⟩ :=
            (some_val_injEq.mp
              (congrArg Subtype.val (Classical.choose_spec isSome))).symm
          rw [chosen_eq]
          apply congrArg Subtype.val
          apply ZFSet.Option.some.injEq.mpr
          symm
          exact fapply.of_pair _ yz
        · exfalso
          apply isSome
          exact ⟨⟨y, hy⟩, Subtype.ext rfl⟩
      · have hxy : (⟨x, hx⟩ : {x // x ∈ A}) = ⟨y, hy⟩ := some_val_injEq.mp hinj
        exact Subtype.ext_iff.mp hxy
    · intro y hy
      have : (Option.some ⟨y, hy⟩).val ∈ Option.toZFSet B :=
        SetLike.coe_mem _
      obtain ⟨x, hx, xy⟩ := hsurj _ this
      rw [flift, lambda_spec, dite_eq_left_of_eq_true (eq_true hx)] at xy
      obtain ⟨-, -, eq⟩ := xy
      split_ifs at eq with issome
      · have eq_val := congrArg Subtype.val (some_val_injEq.mp eq)
        dsimp at eq_val
        obtain rfl := eq_val
        use (Classical.choose issome).val
        and_intros
        · apply SetLike.coe_mem
        · apply fapply.def
      · exact False.elim (ZFSet.Option.some_ne_none _ (Subtype.ext eq))
  mpr := by
    intro hbij
    rw [bijective_exists1_iff] at hbij ⊢
    intro y hy
    obtain eq | ⟨⟨y, hy⟩, eq⟩ := Option.casesOn ⟨y, hy⟩
    · have eq_val := congrArg Subtype.val eq
      dsimp [none, Sum.inl] at eq_val
      obtain rfl := eq_val
      use (@none A).val
      have hnone_mem : (@none A).val ∈ Option.toZFSet A := SetLike.coe_mem _
      and_intros
      · apply SetLike.coe_mem
      · rw [flift, lambda_spec, dite_eq_left_of_eq_true (eq_true hnone_mem)]
        and_intros
        · apply SetLike.coe_mem
        · exact hy
        · split_ifs with isnone
          · obtain ⟨_, contr⟩ := isnone
            change none = some _ at contr
            nomatch ZFSet.Option.some_ne_none _ contr.symm
          · rfl
      · rintro y ⟨hy, pair⟩
        rw [flift, lambda_spec] at pair
        obtain ⟨-, -, eq⟩ := pair
        rw [dite_eq_left_of_eq_true (eq_true hy)] at eq
        split_ifs at eq with issome
        · exact False.elim (ZFSet.Option.some_ne_none _ (Subtype.ext eq.symm))
        · have this : (⟨y, hy⟩ : Option A) = none := by
            by_contra hnone
            exact issome (ZFSet.Option.ne_none_is_some _ hnone)
          exact congrArg Subtype.val this
    · have eq_val := congrArg Subtype.val eq
      dsimp [some, Sum.inr] at eq_val
      obtain rfl := eq_val
      obtain ⟨x, ⟨hx, fxy⟩, x_unq⟩ := hbij y ‹_›
      use (Option.some ⟨x, hx⟩).val
      have hsome_mem : (Option.some ⟨x, hx⟩).val ∈ Option.toZFSet A :=
        SetLike.coe_mem _
      and_intros
      · apply SetLike.coe_mem
      · rw [flift, lambda_spec, dite_eq_left_of_eq_true (eq_true hsome_mem)]
        and_intros
        · apply SetLike.coe_mem
        · exact hy
        · split_ifs with isnone
          · have := Classical.choose_spec isnone
            change some _ = some _ at this
            rw [ZFSet.Option.some.injEq, Subtype.ext_iff] at this
            dsimp at this
            rw [this] at fxy
            have fxy_apply := fapply.of_pair (is_func_is_pfunc hf) fxy
            dsimp [ZFSet.Option.some, Sum.inr]
            rw [pair_inj]
            exact ⟨rfl, (congrArg Subtype.val fxy_apply).symm⟩
          · exact False.elim (isnone ⟨⟨x, hx⟩, Subtype.ext rfl⟩)
      · rintro z ⟨hz, fzy⟩
        rw [flift, lambda_spec] at fzy
        obtain ⟨-, -, eq⟩ := fzy
        rw [dite_eq_left_of_eq_true (eq_true hz)] at eq
        split_ifs at eq with issome
        · have z_eq_some := congrArg Subtype.val (Classical.choose_spec issome)
          have chosen_pair : (Classical.choose issome).val.pair y ∈ f := by
            have hdom : (Classical.choose issome).val ∈ f.Dom := by
              rw [is_func_dom_eq hf]
              exact (Classical.choose issome).property
            have hpair := fapply.def (is_func_is_pfunc hf) hdom
            dsimp [ZFSet.Option.some, Sum.inr] at eq
            rw [pair_inj] at eq
            rwa [eq.2]
          have chosen_eq : (Classical.choose issome).val = x :=
            x_unq _ ⟨(Classical.choose issome).property, chosen_pair⟩
          trans (ZFSet.Option.some (Classical.choose issome)).val
          · exact z_eq_some
          · dsimp [ZFSet.Option.some, Sum.inr]
            rw [pair_inj]
            exact ⟨rfl, chosen_eq⟩
        · dsimp [ZFSet.Option.none, Sum.inl] at eq
          rw [pair_inj] at eq
          exact False.elim (zftrue_ne_zffalse eq.1)


-- @@ L518-518 verbatim
end Option


-- @@ L520-520 verbatim
end ZFSet
