import Mathlib.Tactic
import Analysis.Section_3_1
import Analysis.Tools.ExistsUnique


-- @@ L5-5 verbatim
set_option doc.verso.suggestions false


-- @@ L7-40 verbatim
/-!
# Analysis I, Section 3.3: Functions

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter. In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- A notion of function `Function X Y` between two sets `X`, `Y` in the set theory of Section 3.1
- Various relations with the Mathlib notion of a function `X → Y` between two types `X`, `Y`.
  (Note from Section 3.1 that every `Set` `X` can also be viewed as a subtype
  `{x : Object // x ∈ X }` of `Object`.)
- Basic function properties and operations, such as composition, one-to-one and onto functions,
  and inverses.

In the rest of the book we will deprecate the Chapter 3 version of a function, and work with the
Mathlib notion of a function instead.  Even within this section, we will switch to the Mathlib
formalism for some of the examples involving number systems such as {lean}`ℤ` or {lean}`ℝ` that have not been
implemented in the Chapter 3 framework.

We will work here with the version {name}`Nat` of the natural numbers internal to the Chapter 3 set
theory, though usually we will use coercions to then immediately translate to the Mathlib
natural numbers {lean}`ℕ`.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their tips for future users in this section as PRs.

- (Add tip here)

-/



-- @@ L43-43 verbatim
namespace Chapter3


-- @@ L45-45 verbatim
export SetTheory (Set Object)


-- @@ L47-47 verbatim
variable [SetTheory]


-- @@ L49-56 verbatim
/--
  Definition 3.3.1. {lean}`Function X Y` is the structure of functions from {lean}`X` to {lean}`Y`.
  Analogous to the Mathlib type {lean}`X → Y`.
-/
@[ext]
structure Function (X Y: Set) where
  P : X → Y → Prop
  unique : ∀ x: X, ∃! y: Y, P x y


-- @@ L58-58 verbatim
#check Function.mk


-- @@ L60-66 verbatim
/--
  Converting a Chapter 3 function {lean}`f: Function X Y` to a Mathlib function {lean}`f: X → Y`.
  The Chapter 3 definition of a function was nonconstructive, so we have to use the
  axiom of choice here.
-/
noncomputable def Function.to_fn {X Y: Set} (f: Function X Y) : X → Y :=
  fun x ↦ (f.unique x).choose


-- @@ L68-69 verbatim
noncomputable instance Function.inst_coefn (X Y: Set) : CoeFun (Function X Y) (fun _ ↦ X → Y) where
  coe := Function.to_fn


-- @@ L71-71 verbatim
theorem Function.to_fn_eval {X Y: Set} (f: Function X Y) (x:X) : f.to_fn x = f x := rfl


-- @@ L73-75 verbatim
/-- Converting a Mathlib function to a Chapter 3 {name}`Function` -/
abbrev Function.mk_fn {X Y: Set} (f: X → Y) : Function X Y :=
  Function.mk (fun x y ↦ y = f x) (by simp)


-- @@ L77-79 verbatim
/-- Definition 3.3.1 -/
theorem Function.eval {X Y: Set} (f: Function X Y) (x: X) (y: Y) : y = f x ↔ f.P x y := by
  convert ((f.unique x).choose_iff y).symm


-- @@ L81-83 verbatim
@[simp]
theorem Function.eval_of {X Y: Set} (f: X → Y) (x:X) : (Function.mk_fn f) x = f x := by
  symm; rw [eval]



-- @@ L86-87 verbatim
/-- Example 3.3.3.   -/
abbrev P_3_3_3a : Nat → Nat → Prop := fun x y ↦ (y:ℕ) = (x:ℕ)+1


-- @@ L89-93 verbatim
theorem SetTheory.Set.P_3_3_3a_existsUnique (x: Nat) : ∃! y: Nat, P_3_3_3a x y := by
  apply ExistsUnique.intro ((x+1:ℕ):Nat)
  . simp [P_3_3_3a]
  intro y h
  simpa [P_3_3_3a, Equiv.symm_apply_eq] using h


-- @@ L95-95 verbatim
abbrev SetTheory.Set.f_3_3_3a : Function Nat Nat := Function.mk P_3_3_3a P_3_3_3a_existsUnique


-- @@ L97-98 verbatim
theorem SetTheory.Set.f_3_3_3a_eval (x y: Nat) : y = f_3_3_3a x ↔ (y:ℕ) = (x+1:ℕ) :=
  Function.eval _ _ _



-- @@ L101-103 verbatim
theorem SetTheory.Set.f_3_3_3a_eval' (n: ℕ) : f_3_3_3a (n:Nat) = (n+1:ℕ) := by
  symm
  simp only [f_3_3_3a_eval, nat_equiv_coe_of_coe]


-- @@ L105-105 verbatim
theorem SetTheory.Set.f_3_3_3a_eval'' : f_3_3_3a 4 = 5 :=  f_3_3_3a_eval' 4


-- @@ L107-108 verbatim
theorem SetTheory.Set.f_3_3_3a_eval''' (n:ℕ) : f_3_3_3a (2*n+3: ℕ) = (2*n+4:ℕ) := by
  convert f_3_3_3a_eval' _


-- @@ L110-110 verbatim
abbrev SetTheory.Set.P_3_3_3b : Nat → Nat → Prop := fun x y ↦ (y+1:ℕ) = (x:ℕ)


-- @@ L112-116 verbatim
theorem SetTheory.Set.not_P_3_3_3b_existsUnique : ¬ ∀ x, ∃! y: Nat, P_3_3_3b x y := by
  by_contra h
  choose n hn _ using h (0:Nat)
  have : ((0:Nat):ℕ) = 0 := by simp [OfNat.ofNat]
  simp [P_3_3_3b, this] at hn


-- @@ L118-119 verbatim
abbrev SetTheory.Set.P_3_3_3c : (Nat \ {(0:Object)}: Set) → Nat → Prop :=
  fun x y ↦ ((y+1:ℕ):Object) = x


-- @@ L121-132 verbatim
theorem SetTheory.Set.P_3_3_3c_existsUnique (x: (Nat \ {(0:Object)}: Set)) :
    ∃! y: Nat, P_3_3_3c x y := by
  -- Some technical unpacking here due to the subtle distinctions between the `Object` type,
  -- sets converted to subtypes of `Object`, and subsets of those sets.
  obtain ⟨ x, hx ⟩ := x; simp at hx; obtain ⟨ hx1, hx2 ⟩ := hx
  set n := ((⟨ x, hx1 ⟩:Nat):ℕ)
  have : x = (n:Nat) := by simp [n]
  simp [P_3_3_3c, this, Object.ofnat_eq'] at hx2 ⊢
  replace hx2 : n = (n-1) + 1 := by omega
  apply ExistsUnique.intro ((n-1:ℕ):Nat)
  . simp [←hx2]
  intro y hy; simp [←hy]


-- @@ L134-135 verbatim
abbrev SetTheory.Set.f_3_3_3c : Function (Nat \ {(0:Object)}: Set) Nat :=
  Function.mk P_3_3_3c P_3_3_3c_existsUnique


-- @@ L137-138 verbatim
theorem SetTheory.Set.f_3_3_3c_eval (x: (Nat \ {(0:Object)}: Set)) (y: Nat) :
    y = f_3_3_3c x ↔ ((y+1:ℕ):Object) = x := Function.eval _ _ _


-- @@ L140-146 verbatim
/-- Create a version of a non-zero {lean}`n` inside {lean}`Nat \ {0}` for any natural number n. -/
abbrev SetTheory.Set.coe_nonzero (n:ℕ) (h: n ≠ 0): (Nat \ {(0:Object)}: Set) :=
  ⟨((n:ℕ):Object), by
    simp [Object.ofnat_eq',h]
    rw [←Object.ofnat_eq]
    exact Subtype.property _
  ⟩


-- @@ L148-149 verbatim
theorem SetTheory.Set.f_3_3_3c_eval' (n: ℕ) : f_3_3_3c (coe_nonzero (n+1) (by positivity)) = n := by
  symm; simp [f_3_3_3c_eval]


-- @@ L151-152 verbatim
theorem SetTheory.Set.f_3_3_3c_eval'' : f_3_3_3c (coe_nonzero 4 (by positivity)) = 3 := by
  convert f_3_3_3c_eval' 3


-- @@ L154-155 verbatim
theorem SetTheory.Set.f_3_3_3c_eval''' (n:ℕ) :
    f_3_3_3c (coe_nonzero (2*n+3) (by positivity)) = (2*n+2:ℕ) := by convert f_3_3_3c_eval' (2*n+2)


-- @@ L157-167 verbatim
/--
  Example 3.3.4 is a little tricky to replicate with the current formalism as the real numbers
  have not been constructed yet.  Instead, I offer some Mathlib counterparts, using the
  Mathlib API for {name}`NNReal` and {lean}`ℝ`.
-/
example : ¬ ∃ f: ℝ → ℝ, ∀ x y, y = f x ↔ y^2 = x := by
  by_contra h
  obtain ⟨f, hf⟩ := h; set y := f (-1)
  have h1 := (hf _ y).mp (by rfl)
  have h2 := sq_nonneg y
  linarith


-- @@ L169-175 verbatim
example : ¬ ∃ f: NNReal → ℝ, ∀ x y, y = f x ↔ y^2 = x := by
  by_contra h
  obtain ⟨f, hf⟩ := h; specialize hf 4; set y := f 4
  have hy := (hf y).mp (by rfl)
  have h1 : 2 = y := (hf 2).mpr (by norm_num)
  have h2 : -2 = y := (hf (-2)).mpr (by norm_num)
  linarith


-- @@ L177-181 verbatim
example : ∃ f: NNReal → NNReal, ∀ x y, y = f x ↔ y^2 = x := by
  use NNReal.sqrt; intro x y
  constructor <;> intro h
  · rw [h, NNReal.sq_sqrt]
  · rw [←h, NNReal.sqrt_sq]


-- @@ L183-184 verbatim
/-- Example 3.3.5. The unused variable {lit}`_x` is underscored to avoid triggering a linter. -/
abbrev SetTheory.Set.P_3_3_5 : Nat → Nat → Prop := fun _x y ↦ y = 7


-- @@ L186-187 verbatim
theorem SetTheory.Set.P_3_3_5_existsUnique (x: Nat) : ∃! y: Nat, P_3_3_5 x y := by
  apply ExistsUnique.intro 7 <;> simp [P_3_3_5]


-- @@ L189-189 verbatim
abbrev SetTheory.Set.f_3_3_5 : Function Nat Nat := Function.mk P_3_3_5 P_3_3_5_existsUnique


-- @@ L191-192 verbatim
theorem SetTheory.Set.f_3_3_5_eval (x: Nat) : f_3_3_5 x = 7 := by
  symm; rw [Function.eval]


-- @@ L194-200 verbatim
/-- Definition 3.3.8 (Equality of functions) -/
theorem Function.eq_iff {X Y: Set} (f g: Function X Y) : f = g ↔ ∀ x: X, f x = g x := by
  constructor <;> intro h
  . simp [h]
  ext x y; constructor <;> intros
  . rwa [←Function.eval, ←h x, Function.eval]
  rwa [←Function.eval, h x, Function.eval]


-- @@ L202-206 verbatim
/--
  Example 3.3.10 (simplified).  The second part of the example is tricky to replicate in this
  formalism, so a Mathlib substitute is offered instead.
-/
abbrev SetTheory.Set.f_3_3_10a : Function Nat Nat := Function.mk_fn (fun x ↦ (x^2 + 2*x + 1:ℕ))


-- @@ L208-208 verbatim
abbrev SetTheory.Set.f_3_3_10b : Function Nat Nat := Function.mk_fn (fun x ↦ ((x+1)^2:ℕ))


-- @@ L210-212 verbatim
theorem SetTheory.Set.f_3_3_10_eq : f_3_3_10a = f_3_3_10b := by
  simp_rw [Function.eq_iff, Function.eval_of]
  intros; simp; ring


-- @@ L214-215 verbatim
example : (fun x:NNReal ↦ (x:ℝ)) = (fun x:NNReal ↦ |(x:ℝ)|) := by
  simp_rw [NNReal.abs_eq]


-- @@ L217-222 verbatim
example : (fun x:ℝ ↦ (x:ℝ)) ≠ (fun x:ℝ ↦ |(x:ℝ)|) := by
  intro h
  let a := (fun (x:ℝ) ↦ x) (-1)
  let b := (fun x:ℝ ↦ |(x:ℝ)|) (-1)
  have hab : a = b := by unfold a; rw [h]
  norm_num [a, b] at hab


-- @@ L224-226 verbatim
/-- Example 3.3.11 -/
abbrev SetTheory.Set.f_3_3_11 (X:Set) : Function (∅:Set) X :=
  Function.mk (fun _ _ ↦ True) (by intro ⟨ x, hx ⟩; simp at hx)


-- @@ L228-228 verbatim
theorem SetTheory.Set.empty_function_unique {X: Set} (f g: Function (∅:Set) X) : f = g := by sorry


-- @@ L230-236 verbatim
/-- Definition 3.3.13 (Composition) -/
noncomputable abbrev Function.comp {X Y Z: Set} (g: Function Y Z) (f: Function X Y) :
    Function X Z :=
  Function.mk_fn (fun x ↦ g (f x))

-- `∘` is already taken in Mathlib for the composition of Mathlib functions,
-- so we use `○` here instead to avoid ambiguity.

-- @@ L237-237 verbatim
infix:90 "○" => Function.comp


-- @@ L239-240 expanded
theorem Function.comp_eval {X Y Z : Set} (g : Function Y Z) (f : Function X Y) (x : X) :
    (Function.comp g f) x = g (f x) :=
  Function.eval_of _ _


-- @@ L242-247 expanded
/-- Compatibility with Mathlib's composition operation.
-/
theorem Function.comp_eq_comp {X Y Z : Set} (g : Function Y Z) (f : Function X Y) :
    (Function.comp g f).to_fn = g.to_fn ∘ f.to_fn := by ext;
  simp only [Function.comp_eval, Function.comp_apply]


-- @@ L249-250 verbatim
/-- Example 3.3.14 -/
abbrev SetTheory.Set.f_3_3_14 : Function Nat Nat := Function.mk_fn (fun x ↦ (2*x:ℕ))


-- @@ L252-252 verbatim
abbrev SetTheory.Set.g_3_3_14 : Function Nat Nat := Function.mk_fn (fun x ↦ (x+3:ℕ))


-- @@ L254-256 expanded
theorem SetTheory.Set.g_circ_f_3_3_14 :
    Function.comp g_3_3_14 f_3_3_14 = Function.mk_fn (fun x ↦ ((2 * (x : ℕ) + 3 : ℕ) : Nat)) := by
  simp [Function.eq_iff, Function.eval_of]


-- @@ L258-261 expanded
theorem SetTheory.Set.f_circ_g_3_3_14 :
    Function.comp f_3_3_14 g_3_3_14 = Function.mk_fn (fun x ↦ ((2 * (x : ℕ) + 6 : ℕ) : Nat)) :=
  by
  simp [Function.eq_iff, Function.eval_of]
  intros; ring


-- @@ L263-267 expanded
/-- Lemma 3.3.15 (Composition is associative) -/
theorem SetTheory.Set.comp_assoc {W X Y Z : Set} (h : Function Y Z) (g : Function X Y)
    (f : Function W X) :
    Function.comp h (Function.comp g f) = Function.comp (Function.comp h g) f := by
  simp [Function.eq_iff]


-- @@ L269-269 verbatim
abbrev Function.one_to_one {X Y: Set} (f: Function X Y) : Prop := ∀ x x': X, x ≠ x' → f x ≠ f x'


-- @@ L271-273 verbatim
theorem Function.one_to_one_iff {X Y: Set} (f: Function X Y) :
    f.one_to_one ↔ ∀ x x': X, f x = f x' → x = x' := by
  peel with x hx; tauto


-- @@ L275-281 verbatim
/--
  Compatibility with Mathlib's {name}`Function.Injective`.  You may wish to use the {tactic}`unfold` tactic to
  understand Mathlib concepts such as {name}`Function.Injective`.
-/
theorem Function.one_to_one_iff' {X Y: Set} (f: Function X Y) :
    f.one_to_one ↔ Function.Injective f.to_fn := by
  rw [one_to_one_iff, Function.Injective]


-- @@ L283-291 verbatim
/--
  Example 3.3.18.  One half of the example requires the integers, and so is expressed using
  Mathlib functions instead of Chapter 3 functions.
-/
theorem SetTheory.Set.f_3_3_18_one_to_one :
    (Function.mk_fn (fun (n:Nat) ↦ ((n^2:ℕ):Nat))).one_to_one := by
  rw [Function.one_to_one_iff]
  intro _ _ h
  simpa [Function.eval, Function.eval_of] using h


-- @@ L293-299 verbatim
example : ¬ Function.Injective (fun (n:ℤ) ↦ n^2) := by
  intro h
  have h1 : (fun n ↦ n ^ 2) 1 = (1:ℤ) := by norm_num
  have h2 : (fun n ↦ n ^ 2) (-1) = (1:ℤ) := by norm_num
  nth_rewrite 2 [←h1] at h2
  specialize h h2
  contradiction


-- @@ L301-302 verbatim
example : Function.Injective (fun (n:ℕ) ↦ n^2) := by
  intro _ _ _; rwa [← pow_left_inj₀ (by norm_num) (by norm_num) (show 2 ≠ 0 by norm_num)]


-- @@ L304-307 verbatim
/-- Remark 3.3.19 -/
theorem SetTheory.Set.two_to_one {X Y: Set} {f: Function X Y} (h: ¬ f.one_to_one) :
    ∃ x x': X, x ≠ x' ∧ f x = f x' := by
  rw [Function.one_to_one] at h; aesop


-- @@ L309-310 verbatim
/-- Definition 3.3.20 (Onto functions) -/
abbrev Function.onto {X Y: Set} (f: Function X Y) : Prop := ∀ y: Y, ∃ x: X, f x = y


-- @@ L312-313 verbatim
/-- Compatibility with Mathlib's {name}`Function.Surjective` -/
theorem Function.onto_iff {X Y: Set} (f: Function X Y) : f.onto ↔ Function.Surjective f.to_fn := by rfl


-- @@ L315-319 verbatim
/-- Example 3.3.21 (using Mathlib) -/
example : ¬ Function.Surjective (fun (n:ℤ) ↦ n^2) := by
  unfold Function.Surjective; push_neg
  use (-1); intro a
  linarith [sq_nonneg a]


-- @@ L321-321 verbatim
abbrev A_3_3_21 := { m:ℤ // ∃ n:ℤ, m = n^2 }


-- @@ L323-325 verbatim
example : Function.Surjective (fun (n:ℤ) ↦ ⟨ n^2, by use n ⟩ : ℤ → A_3_3_21) := by
  rintro ⟨b, ⟨a, ha⟩⟩; use a
  simp only [ha]


-- @@ L327-328 verbatim
/-- Definition 3.3.23 (Bijective functions) -/
abbrev Function.bijective {X Y: Set} (f: Function X Y) : Prop := f.one_to_one ∧ f.onto


-- @@ L330-333 verbatim
/-- Compatibility with Mathlib's {name}`Function.Bijective` -/
theorem Function.bijective_iff {X Y: Set} (f: Function X Y) :
    f.bijective ↔ Function.Bijective f.to_fn := by
  rw [Function.bijective, Function.Bijective, one_to_one_iff', onto_iff]


-- @@ L335-339 verbatim
/-- Example 3.3.24 (using Mathlib) -/
abbrev f_3_3_24 : Fin 3 → ({3,4}:_root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨ 3, by norm_num ⟩
| 1 => ⟨ 3, by norm_num ⟩
| 2 => ⟨ 4, by norm_num ⟩


-- @@ L341-341 verbatim
example : ¬ Function.Injective f_3_3_24 := by decide

-- @@ L342-342 verbatim
example : ¬ Function.Bijective f_3_3_24 := by decide


-- @@ L344-346 verbatim
abbrev g_3_3_24 : Fin 2 → ({2,3,4}:_root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨ 2, by norm_num ⟩
| 1 => ⟨ 3, by norm_num ⟩


-- @@ L348-348 verbatim
example : ¬ Function.Surjective g_3_3_24 := by decide

-- @@ L349-349 verbatim
example : ¬ Function.Bijective g_3_3_24 := by decide


-- @@ L351-354 verbatim
abbrev h_3_3_24 : Fin 3 → ({3,4,5}:_root_.Set ℕ) := fun x ↦ match x with
| 0 => ⟨ 3, by norm_num ⟩
| 1 => ⟨ 4, by norm_num ⟩
| 2 => ⟨ 5, by norm_num ⟩


-- @@ L356-356 verbatim
example : Function.Bijective h_3_3_24 := by decide


-- @@ L358-367 verbatim
/--
  Example 3.3.25 is formulated using Mathlib rather than the set theory framework here to avoid
  some tedious technical issues (cf. Exercise 3.3.2)
-/
example : Function.Bijective (fun n ↦ ⟨ n+1, by omega⟩ : ℕ → { n:ℕ // n ≠ 0 }) := by
  constructor
  · intro _ _
    simp only [Subtype.mk.injEq]; omega
  intro ⟨x, hx⟩; use x-1
  simp only [Subtype.mk.injEq]; omega


-- @@ L369-373 verbatim
example : ¬ Function.Bijective (fun n ↦ n+1) := by
  suffices h : ¬ Function.Surjective (fun n ↦ n+1) by unfold Function.Bijective; tauto
  unfold Function.Surjective; push_neg
  use 0; intros
  symm; apply Nat.zero_ne_add_one


-- @@ L375-388 verbatim
/-- Remark 3.3.27 -/
theorem Function.bijective_incorrect_def :
    ∃ X Y: Set, ∃ f: Function X Y, (∀ x: X, ∃! y: Y, y = f x) ∧ ¬ f.bijective := by
  use Nat, Nat
  set f := mk_fn fun x ↦ (0: Nat); use f
  constructor
  · intros
    apply existsUnique_of_exists_of_unique
    · use 0; rw [Function.eval]
    intros; rw [Function.eval] at *; aesop
  rw [Function.bijective]
  suffices h : ¬ f.one_to_one by tauto
  rw [Function.one_to_one_iff]
  push_neg; use 0, 1; simp [f]


-- @@ L390-405 verbatim
/--
  We cannot use the notation {syntax term}`f⁻¹` for the inverse because in Mathlib's {name}`Inv` class, the inverse
  of {name}`f` must be exactly of the same type of {name}`f`, and {lean}`Function Y X` is a different type from
  {lean}`Function X Y`.
-/
abbrev Function.inverse {X Y: Set} (f: Function X Y) (h: f.bijective) :
    Function Y X :=
  Function.mk (fun y x ↦ f x = y) (by
    intros
    apply existsUnique_of_exists_of_unique
    . aesop
    intro _ _ hx hx'; simp at hx hx'
    rw [←hx'] at hx
    apply f.one_to_one_iff.mp h.1
    simp [hx]
  )


-- @@ L407-408 verbatim
theorem Function.inverse_eval {X Y: Set} {f: Function X Y} (h: f.bijective) (y: Y) (x: X) :
    x = (f.inverse h) y ↔ f x = y := Function.eval _ _ _


-- @@ L410-415 verbatim
/-- Compatibility with Mathlib's notion of inverse -/
theorem Function.inverse_eq {X Y: Set} [Nonempty X] {f: Function X Y} (h: f.bijective) :
    (f.inverse h).to_fn = Function.invFun f.to_fn := by
  ext y; congr; symm
  rw [inverse_eval]
  apply Function.rightInverse_invFun (f.bijective_iff.mp h).2


-- @@ L417-421 verbatim
/--
  Exercise 3.3.1.  Although a proof operating directly on functions would be shorter,
  the spirit of the exercise is to show these using the {name}`Function.eq_iff` definition.
-/
theorem Function.refl {X Y:Set} (f: Function X Y) : f = f := by sorry


-- @@ L423-423 verbatim
theorem Function.symm {X Y:Set} (f g: Function X Y) : f = g ↔ g = f := by sorry


-- @@ L425-425 verbatim
theorem Function.trans {X Y:Set} {f g h: Function X Y} (hfg: f = g) (hgh: g = h) : f = h := by sorry


-- @@ L427-428 expanded
theorem Function.comp_congr {X Y Z : Set} {f f' : Function X Y} (hff' : f = f')
    {g g' : Function Y Z} (hgg' : g = g') : Function.comp g f = Function.comp g' f' := by sorry


-- @@ L430-432 expanded
/-- Exercise 3.3.2 -/
theorem Function.comp_of_inj {X Y Z : Set} {f : Function X Y} {g : Function Y Z} (hf : f.one_to_one)
    (hg : g.one_to_one) : (Function.comp g f).one_to_one := by sorry


-- @@ L434-435 expanded
theorem Function.comp_of_surj {X Y Z : Set} {f : Function X Y} {g : Function Y Z} (hf : f.onto)
    (hg : g.onto) : (Function.comp g f).onto := by sorry


-- @@ L437-440 verbatim
/--
  Exercise 3.3.3 - fill in the sorrys in the statements in a reasonable fashion.
-/
theorem empty_function_one_to_one_iff (X: Set) (f: Function ∅ X) : f.one_to_one ↔ sorry := by sorry


-- @@ L442-442 verbatim
theorem empty_function_onto_iff (X: Set) (f: Function ∅ X) : f.onto ↔ sorry := by sorry


-- @@ L444-444 verbatim
theorem empty_function_bijective_iff (X: Set) (f: Function ∅ X) : f.bijective ↔ sorry:= by sorry


-- @@ L446-450 expanded
/-- Exercise 3.3.4.
-/
theorem Function.comp_cancel_left {X Y Z : Set} {f f' : Function X Y} {g : Function Y Z}
    (heq : Function.comp g f = Function.comp g f') (hg : g.one_to_one) : f = f' := by sorry


-- @@ L452-453 expanded
theorem Function.comp_cancel_right {X Y Z : Set} {f : Function X Y} {g g' : Function Y Z}
    (heq : Function.comp g f = Function.comp g' f) (hf : f.onto) : g = g' := by sorry


-- @@ L455-457 expanded
def Function.comp_cancel_left_without_hg :
    Decidable
      (∀ (X Y Z : Set) (f f' : Function X Y) (g : Function Y Z)
        (heq : Function.comp g f = Function.comp g f'), f = f') :=
  by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry


-- @@ L459-461 expanded
def Function.comp_cancel_right_without_hg :
    Decidable
      (∀ (X Y Z : Set) (f : Function X Y) (g g' : Function Y Z)
        (heq : Function.comp g f = Function.comp g' f), g = g') :=
  by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry


-- @@ L463-467 expanded
/-- Exercise 3.3.5.
-/
theorem Function.comp_injective {X Y Z : Set} {f : Function X Y} {g : Function Y Z}
    (hinj : (Function.comp g f).one_to_one) : f.one_to_one := by sorry


-- @@ L469-470 expanded
theorem Function.comp_surjective {X Y Z : Set} {f : Function X Y} {g : Function Y Z}
    (hsurj : (Function.comp g f).onto) : g.onto := by sorry


-- @@ L472-475 expanded
def Function.comp_injective' :
    Decidable
      (∀ (X Y Z : Set) (f : Function X Y) (g : Function Y Z)
        (hinj : (Function.comp g f).one_to_one), g.one_to_one) :=
  by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry


-- @@ L477-480 expanded
def Function.comp_surjective' :
    Decidable
      (∀ (X Y Z : Set) (f : Function X Y) (g : Function Y Z) (hsurj : (Function.comp g f).onto),
        f.onto) :=
  by
  -- the first line of this construction should be either `apply isTrue` or `apply isFalse`.
  sorry


-- @@ L482-484 verbatim
/-- Exercise 3.3.6 -/
theorem Function.inverse_comp_self {X Y: Set} {f: Function X Y} (h: f.bijective) (x: X) :
    (f.inverse h) (f x) = x := by sorry


-- @@ L486-487 verbatim
theorem Function.self_comp_inverse {X Y: Set} {f: Function X Y} (h: f.bijective) (y: Y) :
    f ((f.inverse h) y) = y := by sorry


-- @@ L489-490 verbatim
theorem Function.inverse_bijective {X Y: Set} {f: Function X Y} (h: f.bijective) :
    (f.inverse h).bijective := by sorry


-- @@ L492-493 verbatim
theorem Function.inverse_inverse {X Y: Set} {f: Function X Y} (h: f.bijective) :
    (f.inverse h).inverse (f.inverse_bijective h) = f := by sorry


-- @@ L495-497 expanded
/-- Exercise 3.3.7 -/
theorem Function.comp_bijective {X Y Z : Set} {f : Function X Y} {g : Function Y Z}
    (hf : f.bijective) (hg : g.bijective) : (Function.comp g f).bijective := by sorry


-- @@ L499-501 expanded
theorem Function.inv_of_comp {X Y Z : Set} {f : Function X Y} {g : Function Y Z} (hf : f.bijective)
    (hg : g.bijective) :
    (Function.comp g f).inverse (Function.comp_bijective hf hg) =
      Function.comp (f.inverse hf) (g.inverse hg) :=
  by sorry


-- @@ L503-505 verbatim
/-- Exercise 3.3.8 -/
abbrev Function.inclusion {X Y:Set} (h: X ⊆ Y) :
    Function X Y := Function.mk_fn (fun x ↦ ⟨ x.val, h x.val x.property ⟩ )


-- @@ L507-507 verbatim
abbrev Function.id (X:Set) : Function X X := Function.mk_fn (fun x ↦ x)


-- @@ L509-510 verbatim
theorem Function.inclusion_id (X:Set) :
    Function.inclusion (SetTheory.Set.subset_self X) = Function.id X := by sorry


-- @@ L512-513 expanded
theorem Function.inclusion_comp (X Y Z : Set) (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) :
    Function.comp (Function.inclusion hYZ) (Function.inclusion hXY) =
      Function.inclusion (SetTheory.Set.subset_trans hXY hYZ) :=
  by sorry


-- @@ L515-515 expanded
theorem Function.comp_id {A B : Set} (f : Function A B) : Function.comp f (Function.id A) = f := by
  sorry


-- @@ L517-517 expanded
theorem Function.id_comp {A B : Set} (f : Function A B) : Function.comp (Function.id B) f = f := by
  sorry


-- @@ L519-520 expanded
theorem Function.comp_inv {A B : Set} (f : Function A B) (hf : f.bijective) :
    Function.comp f (f.inverse hf) = Function.id B := by sorry


-- @@ L522-523 expanded
theorem Function.inv_comp {A B : Set} (f : Function A B) (hf : f.bijective) :
    Function.comp (f.inverse hf) f = Function.id A := by sorry


-- @@ L525-528 expanded
open Classical in
theorem Function.glue {X Y Z : Set} (hXY : Disjoint X Y) (f : Function X Z) (g : Function Y Z) :
    ∃! h : Function (X ∪ Y) Z,
      (Function.comp h (Function.inclusion (SetTheory.Set.subset_union_left X Y)) = f) ∧
        (Function.comp h (Function.inclusion (SetTheory.Set.subset_union_right X Y)) = g) :=
  by sorry


-- @@ L530-534 expanded
open Classical in
theorem Function.glue' {X Y Z : Set} (f : Function X Z) (g : Function Y Z)
    (hfg : ∀ x : ((X ∩ Y) : Set), f ⟨x.val, by aesop⟩ = g ⟨x.val, by aesop⟩) :
    ∃! h : Function (X ∪ Y) Z,
      (Function.comp h (Function.inclusion (SetTheory.Set.subset_union_left X Y)) = f) ∧
        (Function.comp h (Function.inclusion (SetTheory.Set.subset_union_right X Y)) = g) :=
  by sorry


-- @@ L536-536 verbatim
end Chapter3
