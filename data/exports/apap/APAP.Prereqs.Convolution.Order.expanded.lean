module

public import APAP.Prereqs.Convolution.Discrete.Defs

import APAP.Prereqs.DummyPositivity
import Mathlib.Algebra.Order.Star.Conjneg
import Mathlib.Analysis.Complex.Order


-- @@ L9-9 verbatim
@[expose] public section


-- @@ L11-11 verbatim
open Finset Function Real

-- @@ L12-12 verbatim
open scoped ComplexConjugate NNReal Pointwise


-- @@ L14-14 verbatim
variable {G R : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]


-- @@ L16-16 verbatim
section OrderedCommSemiring

-- @@ L17-17 verbatim
variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g : G → R}


-- @@ L19-20 expanded
lemma ddconv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ ddconv f g := fun _a ↦
  sum_nonneg fun _x _ ↦ mul_nonneg (hf _) (hg _)


-- @@ L22-23 expanded
lemma ddconv_apply_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) (a : G) : 0 ≤ (ddconv f g) a :=
  ddconv_nonneg hf hg _


-- @@ L25-25 verbatim
variable [StarRing R] [StarOrderedRing R]


-- @@ L27-28 expanded
lemma dddconv_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ dddconv f g := fun _a ↦
  sum_nonneg fun _x _ ↦ mul_nonneg (hf _) <| star_nonneg_iff.2 <| hg _


-- @@ L30-31 expanded
lemma dddconv_apply_nonneg (hf : 0 ≤ f) (hg : 0 ≤ g) (a : G) : 0 ≤ (dddconv f g) a :=
  dddconv_nonneg hf hg _


-- @@ L33-33 verbatim
end OrderedCommSemiring


-- @@ L35-35 verbatim
section StrictOrderedCommSemiring

-- @@ L36-38 verbatim
variable [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] {f g : G → R}

--TODO: Those can probably be generalised to `OrderedCommSemiring` but we don't really care

-- @@ L39-45 expanded
@[simp]
lemma support_ddconv (hf : 0 ≤ f) (hg : 0 ≤ g) : support (ddconv f g) = support f + support g :=
  by
  refine (support_ddconv_subset _ _).antisymm ?_
  rintro _ ⟨a, ha, b, hb, rfl⟩
  rw [mem_support, ddconv_apply_add]
  exact
    ne_of_gt <|
      sum_pos' (fun c _ ↦ mul_nonneg (hf _) <| hg _)
        ⟨0, mem_univ _,
          mul_pos ((hf _).lt_of_ne' <| by simpa using ha) <| (hg _).lt_of_ne' <| by simpa using hb⟩


-- @@ L47-53 expanded
lemma ddconv_pos (hf : 0 < f) (hg : 0 < g) : 0 < ddconv f g :=
  by
  rw [Pi.lt_def] at hf hg ⊢
  obtain ⟨hf, a, ha⟩ := hf
  obtain ⟨hg, b, hb⟩ := hg
  refine ⟨ddconv_nonneg hf hg, a + b, ?_⟩
  rw [ddconv_apply_add]
  exact sum_pos' (fun c _ ↦ mul_nonneg (hf _) <| hg _) ⟨0, by simpa using mul_pos ha hb⟩


-- @@ L55-55 verbatim
variable [StarRing R] [StarOrderedRing R]


-- @@ L57-59 expanded
@[simp]
lemma support_dddconv (hf : 0 ≤ f) (hg : 0 ≤ g) : support (dddconv f g) = support f - support g :=
  by simpa [sub_eq_add_neg] using support_ddconv hf (conjneg_nonneg.2 hg)


-- @@ L61-62 expanded
lemma dddconv_pos (hf : 0 < f) (hg : 0 < g) : 0 < dddconv f g := by rw [← ddconv_conjneg];
  exact ddconv_pos hf (conjneg_pos.2 hg)


-- @@ L64-64 verbatim
end StrictOrderedCommSemiring


-- @@ L66-66 verbatim
section OrderedCommSemiring

-- @@ L67-67 verbatim
variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g : G → R} {n : ℕ}


-- @@ L69-71 expanded
@[simp]
lemma iterConv_nonneg (hf : 0 ≤ f) : ∀ {n}, 0 ≤ iterConv f n
  | 0 => fun _ ↦ by dsimp; split_ifs <;> norm_num
  | n + 1 => ddconv_nonneg (iterConv_nonneg hf) hf


-- @@ L73-73 verbatim
end OrderedCommSemiring


-- @@ L75-75 verbatim
section StrictOrderedCommSemiring

-- @@ L76-77 verbatim
variable [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] [StarRing R] [StarOrderedRing R]
  {f g : G → R} {n : ℕ}


-- @@ L79-81 expanded
@[simp]
lemma iterConv_pos (hf : 0 < f) : ∀ {n}, 0 < iterConv f n
  | 0 => Pi.lt_def.2 ⟨iterConv_nonneg hf.le, 0, by simp⟩
  | n + 1 => ddconv_pos (iterConv_pos hf) hf


-- @@ L83-83 verbatim
end StrictOrderedCommSemiring


-- @@ L85-85 verbatim
namespace Mathlib.Meta.Positivity

-- @@ L86-86 verbatim
open Lean Meta Qq Function


-- @@ L88-88 verbatim
section

-- @@ L89-89 verbatim
variable [CommSemiring R] [PartialOrder R] [IsOrderedRing R] {f g : G → R}


-- @@ L91-92 expanded
private lemma ddconv_nonneg_of_pos_of_nonneg (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ ddconv f g :=
  ddconv_nonneg hf.le hg


-- @@ L94-95 expanded
private lemma ddconv_nonneg_of_nonneg_of_pos (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ ddconv f g :=
  ddconv_nonneg hf hg.le


-- @@ L97-97 verbatim
variable [StarRing R] [StarOrderedRing R]


-- @@ L99-100 expanded
private lemma dddconv_nonneg_of_pos_of_nonneg (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ dddconv f g :=
  dddconv_nonneg hf.le hg


-- @@ L102-103 expanded
private lemma dddconv_nonneg_of_nonneg_of_pos (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ dddconv f g :=
  dddconv_nonneg hf hg.le


-- @@ L105-107 verbatim
end

-- TODO: Make it sound again :(

-- @@ L108-129 unexpanded
set_option linter.unusedVariables false in
/-- The `positivity` extension which identifies expressions of the form `f ∗ᵈ g`,
such that `positivity` successfully recognises both `f` and `g`. -/
@[positivity _ ∗ᵈ _] meta def evalConv : PositivityExt where eval {u G} zG pG e := do
  let .app (.app (_f : Q($G → $G → $G)) (a : Q($G))) (b : Q($G)) ← withReducible (whnf e)
    | throwError "not ∗"
  id <| match pG with
  | none => pure .none
  | some pα => do
    let ra ← core zG (some pα) a
    let rb ← core zG (some pα) b
    match ra, rb with
    | .positive pa, .positive pb => return .positive q(dummy_pos_of_pos_pos $pa $pb)
    | .positive pa, .nonnegative pb => return .nonnegative q(dummy_nng_of_pos_nng $pa $pb)
    | .nonnegative pa, .positive pb => return .nonnegative q(dummy_nng_of_nng_pos $pa $pb)
    | .nonnegative pa, .nonnegative pb => return .nonnegative q(dummy_nng_of_nng_nng $pa $pb)
    | .positive pa, .nonzero pb => return .nonzero q(dummy_nzr_of_pos_nzr $pa $pb)
    | .nonzero pa, .positive pb => return .nonzero q(dummy_nzr_of_nzr_pos $pa $pb)
    | .nonzero pa, .nonzero pb => return .nonzero q(dummy_nzr_of_nzr_nzr $pa $pb)
    | _, _ => pure .none

-- TODO: Make it sound again :(

-- @@ L130-151 unexpanded
set_option linter.unusedVariables false in
/-- The `positivity` extension which identifies expressions of the form `f ○ᵈ g`,
such that `positivity` successfully recognises both `f` and `g`. -/
@[positivity _ ○ᵈ _] meta def evalDConv : PositivityExt where eval {u G} zG pG e := do
  let .app (.app (_f : Q($G → $G → $G)) (a : Q($G))) (b : Q($G)) ← withReducible (whnf e)
    | throwError "not ∗"
  id <| match pG with
  | none => pure .none
  | some pα => do
    let ra ← core zG (some pα) a
    let rb ← core zG (some pα) b
    match ra, rb with
    | .positive pa, .positive pb => return .positive q(dummy_pos_of_pos_pos $pa $pb)
    | .positive pa, .nonnegative pb => return .nonnegative q(dummy_nng_of_pos_nng $pa $pb)
    | .nonnegative pa, .positive pb => return .nonnegative q(dummy_nng_of_nng_pos $pa $pb)
    | .nonnegative pa, .nonnegative pb => return .nonnegative q(dummy_nng_of_nng_nng $pa $pb)
    | .positive pa, .nonzero pb => return .nonzero q(dummy_nzr_of_pos_nzr $pa $pb)
    | .nonzero pa, .positive pb => return .nonzero q(dummy_nzr_of_nzr_pos $pa $pb)
    | .nonzero pa, .nonzero pb => return .nonzero q(dummy_nzr_of_nzr_nzr $pa $pb)
    | _, _ => pure .none

-- TODO: Make it sound again :(

-- @@ L152-166 unexpanded
set_option linter.unusedVariables false in
/-- The `positivity` extension which identifies expressions of the form `f ○ᵈ g`,
such that `positivity` successfully recognises both `f` and `g`. -/
@[positivity _ ∗ᵈ^ _] meta def evalIterConv : PositivityExt where eval {u G} zG pG e := do
  let .app (.app (_f : Q($G → $G → $G)) (a : Q($G))) (b : Q($G)) ← withReducible (whnf e)
    | throwError "not ∗"
  id <| match pG with
  | none => pure .none
  | some pα => do
    let ra ← core zG (some pα) a
    match ra with
    | .positive pa => return .positive q(dummy_pos_of_pos $pa)
    | .nonnegative pa => return .nonnegative q(dummy_nng_of_nng $pa)
    | .nonzero pa => return .nonzero q(dummy_nzr_of_nzr $pa)
    | _ => return .none


-- @@ L168-169 verbatim
variable [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R] [StarRing R] [StarOrderedRing R]
  {f g : G → R}


-- @@ L171-171 expanded
example (hf : 0 < f) (hg : 0 < g) : 0 < ddconv f g := by positivity


-- @@ L172-172 expanded
example (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ ddconv f g := by positivity


-- @@ L173-173 expanded
example (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ ddconv f g := by positivity


-- @@ L174-174 expanded
example (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ ddconv f g := by positivity


-- @@ L175-175 expanded
example (hf : 0 < f) (hg : 0 < g) : 0 < dddconv f g := by positivity


-- @@ L176-176 expanded
example (hf : 0 < f) (hg : 0 ≤ g) : 0 ≤ dddconv f g := by positivity


-- @@ L177-177 expanded
example (hf : 0 ≤ f) (hg : 0 < g) : 0 ≤ dddconv f g := by positivity


-- @@ L178-178 expanded
example (hf : 0 ≤ f) (hg : 0 ≤ g) : 0 ≤ dddconv f g := by positivity


-- @@ L179-179 expanded
example (hf : 0 < f) (n : ℕ) : 0 < iterConv f n := by positivity


-- @@ L180-180 expanded
example (hf : 0 ≤ f) (n : ℕ) : 0 ≤ iterConv f n := by positivity


-- @@ L182-182 verbatim
end Mathlib.Meta.Positivity
