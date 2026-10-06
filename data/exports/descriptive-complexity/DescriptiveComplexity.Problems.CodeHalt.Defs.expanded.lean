/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import Mathlib.Computability.PartrecCode
import DescriptiveComplexity.Interpretation


-- @@ L9-43 verbatim
/-!
# CODEHALT: does the partial recursive code drawn in the instance halt?

The instance is a **syntax tree**, drawn with one element per node: a node
carries one of the eight constructor marks of `Nat.Partrec.Code`, and its
children are named by two binary symbols. The yes-instances are those whose
root draws a code that halts on input `0`.

This is the catalog problem the *undecidability* of the whole development goes
through. Its point is that the passage from Mathlib's halting problem to an
instance is a plain tree encoding – `DescriptiveComplexity.codeStruct`, in
`DescriptiveComplexity.Computability.CodeHalt` – rather than the simulation of
a machine: the code *is* the instance, and only the computation has to be
guessed. That is what makes the map `c ↦ instance` primitive recursive, which
the machine route could not deliver: Mathlib's universal machine is not
finite-state, so a machine instance cannot carry the program it runs.

## The semantics

`DescriptiveComplexity.DecodesTo` relates a node of the instance to a
`Nat.Partrec.Code`, by recursion on the code: a node decodes to `zero` when it
carries the `zero` mark, to `pair cf cg` when it carries the `pair` mark and
its two children decode to `cf` and `cg`, and so on. A yes-instance is one
whose root decodes to a code halting on `0`.

Reading the semantics off an *existential* over codes, rather than as a fixed
point computed inside the instance, is what keeps this file small: the
encoding direction is then immediate, and the converse needs only that
decoding is unique (`DescriptiveComplexity.decodesTo_unique`), which holds as
soon as the marks are exclusive and the child relations are functional
(`DescriptiveComplexity.CodeWF`).
-/

/- The language of code instances lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.graph` and `Language.order`. -/

-- @@ L44-44 verbatim
namespace FirstOrder


-- @@ L46-46 verbatim
namespace Language


-- @@ L48-72 verbatim
/-- Relation symbols of code instances. -/
inductive codeRel : ℕ → Type
  /-- `croot n`: `n` is the root of the syntax tree. -/
  | croot : codeRel 1
  /-- `czero n`: `n` draws the constructor `zero`. -/
  | czero : codeRel 1
  /-- `csucc n`: `n` draws the constructor `succ`. -/
  | csucc : codeRel 1
  /-- `cleft n`: `n` draws the constructor `left`. -/
  | cleft : codeRel 1
  /-- `cright n`: `n` draws the constructor `right`. -/
  | cright : codeRel 1
  /-- `cpair n`: `n` draws the constructor `pair`. -/
  | cpair : codeRel 1
  /-- `ccomp n`: `n` draws the constructor `comp`. -/
  | ccomp : codeRel 1
  /-- `cprec n`: `n` draws the constructor `prec`. -/
  | cprec : codeRel 1
  /-- `crfind n`: `n` draws the constructor `rfind'`. -/
  | crfind : codeRel 1
  /-- `carg1 n m`: `m` is the first child of `n`. -/
  | carg1 : codeRel 2
  /-- `carg2 n m`: `m` is the second child of `n`. -/
  | carg2 : codeRel 2
  deriving DecidableEq


-- @@ L74-78 verbatim
/-- The relational language of code instances: the eight constructor marks,
the mark of the root, and the two child relations. -/
protected def code : Language :=
  ⟨fun _ => Empty, codeRel⟩
  deriving IsRelational


-- @@ L80-81 verbatim
/-- The root symbol. -/
abbrev cRoot : Language.code.Relations 1 := .croot


-- @@ L83-84 verbatim
/-- The `zero` symbol. -/
abbrev cZero : Language.code.Relations 1 := .czero


-- @@ L86-87 verbatim
/-- The `succ` symbol. -/
abbrev cSucc : Language.code.Relations 1 := .csucc


-- @@ L89-90 verbatim
/-- The `left` symbol. -/
abbrev cLeft : Language.code.Relations 1 := .cleft


-- @@ L92-93 verbatim
/-- The `right` symbol. -/
abbrev cRight : Language.code.Relations 1 := .cright


-- @@ L95-96 verbatim
/-- The `pair` symbol. -/
abbrev cPair : Language.code.Relations 1 := .cpair


-- @@ L98-99 verbatim
/-- The `comp` symbol. -/
abbrev cComp : Language.code.Relations 1 := .ccomp


-- @@ L101-102 verbatim
/-- The `prec` symbol. -/
abbrev cPrec : Language.code.Relations 1 := .cprec


-- @@ L104-105 verbatim
/-- The `rfind'` symbol. -/
abbrev cRfind : Language.code.Relations 1 := .crfind


-- @@ L107-108 verbatim
/-- The first-child symbol. -/
abbrev cArg1 : Language.code.Relations 2 := .carg1


-- @@ L110-111 verbatim
/-- The second-child symbol. -/
abbrev cArg2 : Language.code.Relations 2 := .carg2


-- @@ L113-113 verbatim
end Language


-- @@ L115-115 verbatim
end FirstOrder


-- @@ L117-117 verbatim
namespace DescriptiveComplexity


-- @@ L119-119 verbatim
open FirstOrder


-- @@ L121-121 verbatim
open Language Structure


-- @@ L123-123 verbatim
/-! ### The shorthands of the vocabulary -/


-- @@ L125-125 verbatim
section Shorthands


-- @@ L127-127 verbatim
variable {A : Type} [Language.code.Structure A]


-- @@ L129-130 verbatim
/-- Being the root. -/
def CRoot (a : A) : Prop := RelMap cRoot ![a]


-- @@ L132-133 verbatim
/-- Drawing the constructor `zero`. -/
def CZero (a : A) : Prop := RelMap cZero ![a]


-- @@ L135-136 verbatim
/-- Drawing the constructor `succ`. -/
def CSucc (a : A) : Prop := RelMap cSucc ![a]


-- @@ L138-139 verbatim
/-- Drawing the constructor `left`. -/
def CLeft (a : A) : Prop := RelMap cLeft ![a]


-- @@ L141-142 verbatim
/-- Drawing the constructor `right`. -/
def CRight (a : A) : Prop := RelMap cRight ![a]


-- @@ L144-145 verbatim
/-- Drawing the constructor `pair`. -/
def CPair (a : A) : Prop := RelMap cPair ![a]


-- @@ L147-148 verbatim
/-- Drawing the constructor `comp`. -/
def CComp (a : A) : Prop := RelMap cComp ![a]


-- @@ L150-151 verbatim
/-- Drawing the constructor `prec`. -/
def CPrec (a : A) : Prop := RelMap cPrec ![a]


-- @@ L153-154 verbatim
/-- Drawing the constructor `rfind'`. -/
def CRfind (a : A) : Prop := RelMap cRfind ![a]


-- @@ L156-157 verbatim
/-- Being the first child. -/
def CArg1 (a b : A) : Prop := RelMap cArg1 ![a, b]


-- @@ L159-160 verbatim
/-- Being the second child. -/
def CArg2 (a b : A) : Prop := RelMap cArg2 ![a, b]


-- @@ L162-162 verbatim
end Shorthands


-- @@ L164-164 verbatim
/-! ### Decoding a node into a code -/


-- @@ L166-166 verbatim
section Decode


-- @@ L168-168 verbatim
variable {A : Type} [Language.code.Structure A]


-- @@ L170-190 verbatim
/-- The eight constructors of `Nat.Partrec.Code`, as a tag. Naming them makes
the exclusivity of the marks one statement instead of twenty-eight, and the
uniqueness of decoding a uniform argument instead of sixty-four cases. -/
inductive CodeTag
  /-- The tag of `zero`. -/
  | zero
  /-- The tag of `succ`. -/
  | succ
  /-- The tag of `left`. -/
  | left
  /-- The tag of `right`. -/
  | right
  /-- The tag of `pair`. -/
  | pair
  /-- The tag of `comp`. -/
  | comp
  /-- The tag of `prec`. -/
  | prec
  /-- The tag of `rfind'`. -/
  | rfind
  deriving DecidableEq


-- @@ L192-201 verbatim
/-- The mark a tag stands for. -/
def Mark : CodeTag → A → Prop
  | .zero => CZero
  | .succ => CSucc
  | .left => CLeft
  | .right => CRight
  | .pair => CPair
  | .comp => CComp
  | .prec => CPrec
  | .rfind => CRfind


-- @@ L203-212 verbatim
/-- The tag of a code. -/
def tagOf : Nat.Partrec.Code → CodeTag
  | .zero => .zero
  | .succ => .succ
  | .left => .left
  | .right => .right
  | .pair _ _ => .pair
  | .comp _ _ => .comp
  | .prec _ _ => .prec
  | .rfind' _ => .rfind


-- @@ L214-228 verbatim
/-- **The node `n` draws the code `c`.** A recursion on the code: the mark of
the node must be the constructor's, and its children must draw the
constructor's arguments. -/
def DecodesTo (n : A) : Nat.Partrec.Code → Prop
  | .zero => CZero n
  | .succ => CSucc n
  | .left => CLeft n
  | .right => CRight n
  | .pair cf cg =>
      CPair n ∧ ∃ a b, CArg1 n a ∧ CArg2 n b ∧ DecodesTo a cf ∧ DecodesTo b cg
  | .comp cf cg =>
      CComp n ∧ ∃ a b, CArg1 n a ∧ CArg2 n b ∧ DecodesTo a cf ∧ DecodesTo b cg
  | .prec cf cg =>
      CPrec n ∧ ∃ a b, CArg1 n a ∧ CArg2 n b ∧ DecodesTo a cf ∧ DecodesTo b cg
  | .rfind' cf => CRfind n ∧ ∃ a, CArg1 n a ∧ DecodesTo a cf


-- @@ L230-238 verbatim
theorem decodesTo_mark : ∀ (c : Nat.Partrec.Code) (n : A), DecodesTo n c → Mark (tagOf c) n
  | .zero, _, h => h
  | .succ, _, h => h
  | .left, _, h => h
  | .right, _, h => h
  | .pair _ _, _, h => h.1
  | .comp _ _, _, h => h.1
  | .prec _ _, _, h => h.1
  | .rfind' _, _, h => h.1


-- @@ L240-250 verbatim
/-- **Well-formedness of a code instance**: at most one constructor mark per
node, and functional child relations. This is what makes decoding unique; it
is *not* folded into the yes-instances, because the problem is stated by an
existential over codes and a junk instance simply decodes to nothing. -/
structure CodeWF (A : Type) [Language.code.Structure A] : Prop where
  /-- At most one constructor mark per node. -/
  exclusive : ∀ (a : A) (t t' : CodeTag), Mark t a → Mark t' a → t = t'
  /-- The first child is unique. -/
  arg1_fun : ∀ a b b' : A, CArg1 a b → CArg1 a b' → b = b'
  /-- The second child is unique. -/
  arg2_fun : ∀ a b b' : A, CArg2 a b → CArg2 a b' → b = b'


-- @@ L252-254 verbatim
theorem tag_eq_of_decodesTo (h : CodeWF A) {c c' : Nat.Partrec.Code} {n : A}
    (h1 : DecodesTo n c) (h2 : DecodesTo n c') : tagOf c = tagOf c' :=
  h.exclusive n _ _ (decodesTo_mark c n h1) (decodesTo_mark c' n h2)


-- @@ L256-327 verbatim
/-- **Decoding is unique** on a well-formed instance. -/
theorem decodesTo_unique (h : CodeWF A) :
    ∀ (c c' : Nat.Partrec.Code) (n : A), DecodesTo n c → DecodesTo n c' → c = c' := by
  intro c
  induction c with
  | zero =>
    intro c' n h1 h2
    have ht := tag_eq_of_decodesTo h h1 h2
    cases c'
    case zero => rfl
    all_goals exact absurd ht (by simp [tagOf])
  | succ =>
    intro c' n h1 h2
    have ht := tag_eq_of_decodesTo h h1 h2
    cases c'
    case succ => rfl
    all_goals exact absurd ht (by simp [tagOf])
  | left =>
    intro c' n h1 h2
    have ht := tag_eq_of_decodesTo h h1 h2
    cases c'
    case left => rfl
    all_goals exact absurd ht (by simp [tagOf])
  | right =>
    intro c' n h1 h2
    have ht := tag_eq_of_decodesTo h h1 h2
    cases c'
    case right => rfl
    all_goals exact absurd ht (by simp [tagOf])
  | pair cf cg ihf ihg =>
    intro c' n h1 h2
    have ht := tag_eq_of_decodesTo h h1 h2
    cases c'
    case pair cf' cg' =>
      obtain ⟨-, a, b, ha, hb, hf, hg⟩ := h1
      obtain ⟨-, a', b', ha', hb', hf', hg'⟩ := h2
      rw [h.arg1_fun n a' a ha' ha] at hf'
      rw [h.arg2_fun n b' b hb' hb] at hg'
      rw [ihf cf' a hf hf', ihg cg' b hg hg']
    all_goals exact absurd ht (by simp [tagOf])
  | comp cf cg ihf ihg =>
    intro c' n h1 h2
    have ht := tag_eq_of_decodesTo h h1 h2
    cases c'
    case comp cf' cg' =>
      obtain ⟨-, a, b, ha, hb, hf, hg⟩ := h1
      obtain ⟨-, a', b', ha', hb', hf', hg'⟩ := h2
      rw [h.arg1_fun n a' a ha' ha] at hf'
      rw [h.arg2_fun n b' b hb' hb] at hg'
      rw [ihf cf' a hf hf', ihg cg' b hg hg']
    all_goals exact absurd ht (by simp [tagOf])
  | prec cf cg ihf ihg =>
    intro c' n h1 h2
    have ht := tag_eq_of_decodesTo h h1 h2
    cases c'
    case prec cf' cg' =>
      obtain ⟨-, a, b, ha, hb, hf, hg⟩ := h1
      obtain ⟨-, a', b', ha', hb', hf', hg'⟩ := h2
      rw [h.arg1_fun n a' a ha' ha] at hf'
      rw [h.arg2_fun n b' b hb' hb] at hg'
      rw [ihf cf' a hf hf', ihg cg' b hg hg']
    all_goals exact absurd ht (by simp [tagOf])
  | rfind' cf ihf =>
    intro c' n h1 h2
    have ht := tag_eq_of_decodesTo h h1 h2
    cases c'
    case rfind' cf' =>
      obtain ⟨-, a, ha, hf⟩ := h1
      obtain ⟨-, a', ha', hf'⟩ := h2
      rw [h.arg1_fun n a' a ha' ha] at hf'
      rw [ihf cf' a hf hf']
    all_goals exact absurd ht (by simp [tagOf])


-- @@ L329-329 verbatim
end Decode


-- @@ L331-331 verbatim
/-! ### Isomorphism-invariance -/


-- @@ L333-333 verbatim
section Iso


-- @@ L335-335 verbatim
variable {A B : Type} [Language.code.Structure A] [Language.code.Structure B]


-- @@ L337-338 verbatim
private theorem mark_equiv (e : A ≃[Language.code] B) (r : Language.code.Relations 1) (n : A) :
    (RelMap r ![n] : Prop) ↔ RelMap r ![(e n : B)] := relMap_equiv₁ e r n


-- @@ L340-343 verbatim
private theorem arg_equiv_symm (e : A ≃[Language.code] B) (r : Language.code.Relations 2)
    (n : A) (b : B) : (RelMap r ![n, e.symm b] : Prop) ↔ RelMap r ![(e n : B), b] := by
  have h := relMap_equiv₂ e r n (e.symm b)
  rwa [show (e (e.symm b) : B) = b from e.toEquiv.apply_symm_apply b] at h


-- @@ L345-401 verbatim
/-- **Decoding transports along an isomorphism**: what a node draws is a
first-order property of the instance. -/
theorem decodesTo_equiv (e : A ≃[Language.code] B) :
    ∀ (c : Nat.Partrec.Code) (n : A), DecodesTo n c ↔ DecodesTo (e n) c := by
  intro c
  induction c with
  | zero => intro n; exact mark_equiv e cZero n
  | succ => intro n; exact mark_equiv e cSucc n
  | left => intro n; exact mark_equiv e cLeft n
  | right => intro n; exact mark_equiv e cRight n
  | pair cf cg ihf ihg =>
    intro n
    refine and_congr (mark_equiv e cPair n) ⟨?_, ?_⟩
    · rintro ⟨a, b, ha, hb, hf, hg⟩
      exact ⟨e a, e b, (relMap_equiv₂ e cArg1 n a).mp ha, (relMap_equiv₂ e cArg2 n b).mp hb,
        (ihf a).mp hf, (ihg b).mp hg⟩
    · rintro ⟨a, b, ha, hb, hf, hg⟩
      refine ⟨e.symm a, e.symm b, (arg_equiv_symm e cArg1 n a).mpr ha,
        (arg_equiv_symm e cArg2 n b).mpr hb, ?_, ?_⟩
      · refine (ihf (e.symm a)).mpr ?_
        rwa [show (e (e.symm a) : B) = a from e.toEquiv.apply_symm_apply a]
      · refine (ihg (e.symm b)).mpr ?_
        rwa [show (e (e.symm b) : B) = b from e.toEquiv.apply_symm_apply b]
  | comp cf cg ihf ihg =>
    intro n
    refine and_congr (mark_equiv e cComp n) ⟨?_, ?_⟩
    · rintro ⟨a, b, ha, hb, hf, hg⟩
      exact ⟨e a, e b, (relMap_equiv₂ e cArg1 n a).mp ha, (relMap_equiv₂ e cArg2 n b).mp hb,
        (ihf a).mp hf, (ihg b).mp hg⟩
    · rintro ⟨a, b, ha, hb, hf, hg⟩
      refine ⟨e.symm a, e.symm b, (arg_equiv_symm e cArg1 n a).mpr ha,
        (arg_equiv_symm e cArg2 n b).mpr hb, ?_, ?_⟩
      · refine (ihf (e.symm a)).mpr ?_
        rwa [show (e (e.symm a) : B) = a from e.toEquiv.apply_symm_apply a]
      · refine (ihg (e.symm b)).mpr ?_
        rwa [show (e (e.symm b) : B) = b from e.toEquiv.apply_symm_apply b]
  | prec cf cg ihf ihg =>
    intro n
    refine and_congr (mark_equiv e cPrec n) ⟨?_, ?_⟩
    · rintro ⟨a, b, ha, hb, hf, hg⟩
      exact ⟨e a, e b, (relMap_equiv₂ e cArg1 n a).mp ha, (relMap_equiv₂ e cArg2 n b).mp hb,
        (ihf a).mp hf, (ihg b).mp hg⟩
    · rintro ⟨a, b, ha, hb, hf, hg⟩
      refine ⟨e.symm a, e.symm b, (arg_equiv_symm e cArg1 n a).mpr ha,
        (arg_equiv_symm e cArg2 n b).mpr hb, ?_, ?_⟩
      · refine (ihf (e.symm a)).mpr ?_
        rwa [show (e (e.symm a) : B) = a from e.toEquiv.apply_symm_apply a]
      · refine (ihg (e.symm b)).mpr ?_
        rwa [show (e (e.symm b) : B) = b from e.toEquiv.apply_symm_apply b]
  | rfind' cf ihf =>
    intro n
    refine and_congr (mark_equiv e cRfind n) ⟨?_, ?_⟩
    · rintro ⟨a, ha, hf⟩
      exact ⟨e a, (relMap_equiv₂ e cArg1 n a).mp ha, (ihf a).mp hf⟩
    · rintro ⟨a, ha, hf⟩
      refine ⟨e.symm a, (arg_equiv_symm e cArg1 n a).mpr ha, (ihf (e.symm a)).mpr ?_⟩
      rwa [show (e (e.symm a) : B) = a from e.toEquiv.apply_symm_apply a]


-- @@ L403-403 verbatim
end Iso


-- @@ L405-405 verbatim
/-! ### The problem -/


-- @@ L407-427 verbatim
/-- **CODEHALT**: does the partial recursive code drawn by the root of the
instance halt on input `0`?

The yes-instances are stated by an existential over `Nat.Partrec.Code`: some
node is the root, it draws some code, and that code halts on `0`. Nothing is
promised of the instance, so a junk one simply draws nothing and is a
no-instance. -/
def CODEHALT : DecisionProblem Language.code where
  Holds A _ := ∃ (n : A) (c : Nat.Partrec.Code),
    CRoot n ∧ DecodesTo n c ∧ (Nat.Partrec.Code.eval c 0).Dom
  iso_invariant := fun {A B} _ _ e => by
    constructor
    · rintro ⟨n, c, hr, hd, hh⟩
      exact ⟨e n, c, (mark_equiv e cRoot n).mp hr, (decodesTo_equiv e c n).mp hd, hh⟩
    · rintro ⟨m, c, hr, hd, hh⟩
      refine ⟨e.symm m, c, ?_, ?_, hh⟩
      · have hm := mark_equiv e cRoot (e.symm m)
        rw [show (e (e.symm m) : B) = m from e.toEquiv.apply_symm_apply m] at hm
        exact hm.mpr hr
      · refine (decodesTo_equiv e c (e.symm m)).mpr ?_
        rwa [show (e (e.symm m) : B) = m from e.toEquiv.apply_symm_apply m]


-- @@ L429-433 verbatim
@[simp]
theorem codehalt_holds_iff (A : Type) [Language.code.Structure A] :
    CODEHALT A ↔ ∃ (n : A) (c : Nat.Partrec.Code),
      CRoot n ∧ DecodesTo n c ∧ (Nat.Partrec.Code.eval c 0).Dom :=
  Iff.rfl


-- @@ L435-435 verbatim
end DescriptiveComplexity
