/-
Copyright (c) 2026 Andrej Bauer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrej Bauer
-/
module

public import LeanPool.PartialCombinatoryAlgebras.PartialCombinatoryAlgebra
import Mathlib.Data.Finset.Attr
import Mathlib.Tactic.NthRewrite
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Widget.Calc


-- @@ L14-34 verbatim
/-! ## Programming with PCAs

  A (non-trivial) PCA is Turing-complete in the sense that it implements
  every partial computable function. We develop here basic programming
  constructs that witness this fact:

  * the identity combinator `I`
  * ordered pairs `pair` with projections `fst` and `snd`
  * booleans `tru`, `fal` and the conditional statement `ite`
  * fixed-point combinators `Z` and `Y`
  * Curry numerals `numeral n` with successor `succ`, predecessor `pred`
    and primitive recursion `primrec`

  For each combinator `C` we prove a definedness lemma `df_C` characterizing
  totality of expressions involving `C`. Characteristic equations for the
  simpler combinators (`I`, `K'`, `pair`, `fst`, `snd`, the booleans, `X`, `W`,
  and the fixed-point combinators) are also proved here; equations for the
  more complex Curry-numeral predecessor and primitive-recursion combinators
  are omitted in this v4.30 port — they remain expressible in terms of the
  combinators themselves.
-/


-- @@ L36-36 verbatim
@[expose] public section


-- @@ L38-38 verbatim
namespace LeanPool.PartialCombinatoryAlgebras


-- @@ L40-40 verbatim
namespace PCA


-- @@ L42-42 verbatim
universe u

-- @@ L43-43 verbatim
variable {A : Type u} [PCA A]


-- @@ L45-46 expanded
/-- The identity combinator -/
def I : Part A :=
  HasDot.dot (HasDot.dot S K) K


-- @@ L48-48 verbatim
namespace Expr


-- @@ L50-51 expanded
/-- The expression denoting the identity combinator -/
def I {Γ} : Expr Γ A :=
  HasDot.dot (HasDot.dot .S .K) .K


-- @@ L53-53 verbatim
end Expr


-- @@ L55-56 expanded
@[simp]
theorem df_I : Part.Dom (I : Part A) :=
  df_S₂ df_K₀ df_K₀


-- @@ L58-61 expanded
@[simp]
theorem eq_I {u : Part A} (hu : Part.Dom u) : HasDot.dot I u = u :=
  by
  change HasDot.dot (HasDot.dot (HasDot.dot S K) K) u = u
  rw [eq_S _ _ _ df_K₀ df_K₀ hu, eq_K _ _ hu (df_K₁ hu)]


-- @@ L63-64 expanded
/-- The `K I` combinator: `K' u v = v`. -/
def K' : Part A :=
  HasDot.dot K I


-- @@ L66-66 verbatim
namespace Expr


-- @@ L68-69 expanded
/-- Formal expression denoting `K'`. -/
def K' {Γ} : Expr Γ A :=
  HasDot.dot .K .I


-- @@ L71-71 verbatim
end Expr


-- @@ L73-74 expanded
@[simp]
theorem df_K' : Part.Dom (K' : Part A) :=
  df_K₁ df_I


-- @@ L76-79 expanded
@[simp]
theorem eq_K' (u v : Part A) (hu : Part.Dom u) (hv : Part.Dom v) :
    HasDot.dot (HasDot.dot K' u) v = v :=
  by
  change HasDot.dot (HasDot.dot (HasDot.dot K I) u) v = v
  rw [eq_K _ _ df_I hu, eq_I hv]


-- @@ L81-81 verbatim
/-! ### Pairing -/


-- @@ L83-84 expanded
/-- The pairing combinator. -/
def pair : Part A :=
  LeanPool.PartialCombinatoryAlgebras.PCA.compile (Γ := Lean.Name)
    (LeanPool.PartialCombinatoryAlgebras.PCA.abstr `x
      (LeanPool.PartialCombinatoryAlgebras.PCA.abstr `y
        (LeanPool.PartialCombinatoryAlgebras.PCA.abstr `z
          (HasDot.dot (HasDot.dot (.var `z) (.var `x)) (.var `y)))))


-- @@ L86-87 expanded
@[simp]
theorem df_pair : Part.Dom (pair : Part A) :=
  df_abstr _ _ _


-- @@ L89-94 expanded
@[simp]
theorem df_pair_app (u : Part A) (hu : Part.Dom u) : Part.Dom (HasDot.dot pair u) :=
  by
  unfold pair
  simp only [compile]
  rw [eval_abstr_app _ _ _ _ hu]
  exact df_abstr _ _ _


-- @@ L96-101 expanded
@[simp]
theorem df_pair_app_app (u v : Part A) (hu : Part.Dom u) (hv : Part.Dom v) :
    Part.Dom (HasDot.dot (HasDot.dot pair u) v) :=
  by
  unfold pair
  simp only [compile]
  rw [eval_abstr_app _ _ _ _ hu, eval_abstr_app _ _ _ _ hv]
  exact df_abstr _ _ _


-- @@ L103-109 expanded
@[simp]
theorem eq_pair (u v w : Part A) (hu : Part.Dom u) (hv : Part.Dom v) (hw : Part.Dom w) :
    HasDot.dot (HasDot.dot (HasDot.dot pair u) v) w = HasDot.dot (HasDot.dot w u) v :=
  by
  unfold pair
  simp only [compile]
  rw [eval_abstr_app _ _ _ _ hu, eval_abstr_app _ _ _ _ hv, eval_abstr_app _ _ _ _ hw]
  simp [HasDot.dot, eval, subst]


-- @@ L111-112 expanded
/-- The first projection. -/
def fst : Part A :=
  LeanPool.PartialCombinatoryAlgebras.PCA.compile (Γ := Lean.Name)
    (LeanPool.PartialCombinatoryAlgebras.PCA.abstr `x (HasDot.dot (.var `x) .K))


-- @@ L114-114 verbatim
namespace fst


-- @@ L116-117 verbatim
/-- The first projection as a formal expression. -/
def elm {Γ} : Expr Γ A := .elm (fst.get (df_abstr _ _ _))


-- @@ L119-119 verbatim
end fst


-- @@ L121-126 expanded
@[simp]
theorem eq_fst (u : Part A) (hu : Part.Dom u) : HasDot.dot fst u = HasDot.dot u PCA.K :=
  by
  unfold fst
  simp only [compile]
  rw [eval_abstr_app _ _ _ _ hu]
  simp [HasDot.dot, eval, subst]


-- @@ L128-129 expanded
/-- The second projection. -/
def snd : Part A :=
  LeanPool.PartialCombinatoryAlgebras.PCA.compile (Γ := Lean.Name)
    (LeanPool.PartialCombinatoryAlgebras.PCA.abstr `x (HasDot.dot (.var `x) .K'))


-- @@ L131-131 verbatim
namespace snd


-- @@ L133-134 verbatim
/-- The second projection as a formal expression. -/
def elm {Γ} : Expr Γ A := .elm (snd.get (df_abstr _ _ _))


-- @@ L136-136 verbatim
end snd


-- @@ L138-143 expanded
@[simp]
theorem eq_snd (u : Part A) (hu : Part.Dom u) : HasDot.dot snd u = HasDot.dot u K' :=
  by
  unfold snd
  simp only [compile]
  rw [eval_abstr_app _ _ _ _ hu]
  simp [HasDot.dot, eval, subst, Expr.K', Expr.I, K', I]


-- @@ L145-149 expanded
theorem eq_fst_pair (u v : Part A) (hu : Part.Dom u) (hv : Part.Dom v) :
    HasDot.dot fst (HasDot.dot (HasDot.dot pair u) v) = u := by
  calc
    _ = HasDot.dot (HasDot.dot (HasDot.dot pair u) v) K := eq_fst _ (df_pair_app_app u v hu hv)
    _ = HasDot.dot (HasDot.dot K u) v := (eq_pair u v K hu hv df_K₀)
    _ = u := eq_K _ _ hu hv


-- @@ L151-152 expanded
theorem eq_snd_pair (u v : Part A) (hu : Part.Dom u) (hv : Part.Dom v) :
    HasDot.dot snd (HasDot.dot (HasDot.dot pair u) v) = v := by simp_all


-- @@ L154-155 verbatim
/-- Conditional statements -/
def ite : Part A := I


-- @@ L157-158 verbatim
/-- The boolean false -/
def fal : Part A := K'


-- @@ L160-160 expanded
@[simp]
theorem df_fal : Part.Dom (fal : Part A) :=
  df_K'


-- @@ L162-163 expanded
@[simp]
theorem eq_fal (u v : Part A) (hu : Part.Dom u) (hv : Part.Dom v) :
    HasDot.dot (HasDot.dot fal u) v = v :=
  eq_K' u v hu hv


-- @@ L165-166 verbatim
/-- The boolean true -/
def tru : Part A := K


-- @@ L168-168 expanded
@[simp]
theorem df_tru : Part.Dom (tru : Part A) :=
  df_K₀


-- @@ L170-174 expanded
@[simp]
theorem eq_ite_fal (u v : Part A) (hu : Part.Dom u) (hv : Part.Dom v) :
    HasDot.dot (HasDot.dot (HasDot.dot ite fal) u) v = v :=
  by
  change HasDot.dot (HasDot.dot (HasDot.dot I fal) u) v = v
  rw [eq_I df_fal, eq_fal u v hu hv]


-- @@ L176-180 expanded
@[simp]
theorem eq_ite_tru (u v : Part A) (hu : Part.Dom u) (hv : Part.Dom v) :
    HasDot.dot (HasDot.dot (HasDot.dot ite tru) u) v = u :=
  by
  change HasDot.dot (HasDot.dot (HasDot.dot I K) u) v = u
  rw [eq_I df_K₀, eq_K u v hu hv]


-- @@ L182-182 verbatim
/-! ### The fixed point combinator -/


-- @@ L184-185 expanded
/-- Auxiliary combinator used to define the fixed point combinator `Z`. -/
def X : Part A :=
  LeanPool.PartialCombinatoryAlgebras.PCA.compile (Γ := Lean.Name)
    (LeanPool.PartialCombinatoryAlgebras.PCA.abstr `x
      (LeanPool.PartialCombinatoryAlgebras.PCA.abstr `y
        (LeanPool.PartialCombinatoryAlgebras.PCA.abstr `z
          (HasDot.dot (HasDot.dot (.var `y) (HasDot.dot (HasDot.dot (.var `x) (.var `x)) (.var `y)))
            (.var `z)))))


-- @@ L187-188 expanded
@[simp]
theorem df_X : Part.Dom (X : Part A) :=
  df_abstr _ _ _


-- @@ L190-195 expanded
@[simp]
theorem df_X_app (u : Part A) (hu : Part.Dom u) : Part.Dom (HasDot.dot X u) :=
  by
  unfold X
  simp only [compile]
  rw [eval_abstr_app _ _ _ _ hu]
  exact df_abstr _ _ _


-- @@ L197-202 expanded
@[simp]
theorem df_X_app_app (u v : Part A) (hu : Part.Dom u) (hv : Part.Dom v) :
    Part.Dom (HasDot.dot (HasDot.dot X u) v) :=
  by
  unfold X
  simp only [compile]
  rw [eval_abstr_app _ _ _ _ hu, eval_abstr_app _ _ _ _ hv]
  exact df_abstr _ _ _


-- @@ L204-209 expanded
theorem eq_X (u v w : Part A) (hu : Part.Dom u) (hv : Part.Dom v) (hw : Part.Dom w) :
    HasDot.dot (HasDot.dot (HasDot.dot X u) v) w =
      HasDot.dot (HasDot.dot v (HasDot.dot (HasDot.dot u u) v)) w :=
  by
  unfold X
  simp only [compile]
  rw [eval_abstr_app _ _ _ _ hu, eval_abstr_app _ _ _ _ hv, eval_abstr_app _ _ _ _ hw]
  simp [HasDot.dot, eval, subst]


-- @@ L211-212 expanded
/-- The call-by-name fixed-point combinator. -/
def Z : Part A :=
  HasDot.dot X X


-- @@ L214-215 expanded
@[simp]
theorem df_Z : Part.Dom (Z : Part A) :=
  df_X_app X df_X


-- @@ L217-217 verbatim
namespace Z


-- @@ L219-221 verbatim
/-- The fixed-point combinator `Z` as a formal expression. -/
@[reducible]
def elm {Γ} : Expr Γ A := .elm (Z.get df_Z)


-- @@ L223-223 verbatim
end Z


-- @@ L225-227 expanded
@[simp]
theorem df_Z_app (u : Part A) (hu : Part.Dom u) : Part.Dom (HasDot.dot Z u) :=
  df_X_app_app X u df_X hu


-- @@ L229-231 expanded
theorem eq_Z (u v : Part A) (hu : Part.Dom u) (hv : Part.Dom v) :
    HasDot.dot (HasDot.dot Z u) v = HasDot.dot (HasDot.dot u (HasDot.dot Z u)) v :=
  by
  change
    HasDot.dot (HasDot.dot (HasDot.dot X X) u) v =
      HasDot.dot (HasDot.dot u (HasDot.dot (HasDot.dot X X) u)) v
  rw [eq_X X u v df_X hu hv]


-- @@ L233-234 expanded
/-- Auxiliary combinator used to define the call-by-value fixed point combinator `Y`. -/
def W : Part A :=
  LeanPool.PartialCombinatoryAlgebras.PCA.compile (Γ := Lean.Name)
    (LeanPool.PartialCombinatoryAlgebras.PCA.abstr `x
      (LeanPool.PartialCombinatoryAlgebras.PCA.abstr `y
        (HasDot.dot (.var `y) (HasDot.dot (HasDot.dot (.var `x) (.var `x)) (.var `y)))))


-- @@ L236-237 expanded
@[simp]
theorem df_W : Part.Dom (W : Part A) :=
  df_abstr _ _ _


-- @@ L239-244 expanded
@[simp]
theorem df_W_app (u : Part A) (hu : Part.Dom u) : Part.Dom (HasDot.dot W u) :=
  by
  unfold W
  simp only [compile]
  rw [eval_abstr_app _ _ _ _ hu]
  exact df_abstr _ _ _


-- @@ L246-251 expanded
theorem eq_W (u v : Part A) (hu : Part.Dom u) (hv : Part.Dom v) :
    HasDot.dot (HasDot.dot W u) v = HasDot.dot v (HasDot.dot (HasDot.dot u u) v) :=
  by
  unfold W
  simp only [compile]
  rw [eval_abstr_app _ _ _ _ hu, eval_abstr_app _ _ _ _ hv]
  simp [HasDot.dot, eval, subst]


-- @@ L253-254 expanded
/-- The call-by-value fixed-point combinator. -/
def Y : Part A :=
  HasDot.dot W W


-- @@ L256-257 expanded
@[simp]
theorem df_Y : Part.Dom (Y : Part A) :=
  df_W_app W df_W


-- @@ L259-261 expanded
theorem eq_Y (u : Part A) (hu : Part.Dom u) : HasDot.dot Y u = HasDot.dot u (HasDot.dot Y u) :=
  by
  change HasDot.dot (HasDot.dot W W) u = HasDot.dot u (HasDot.dot (HasDot.dot W W) u)
  nth_rw 1 [eq_W W u df_W hu]


-- @@ L263-263 verbatim
/-! ### Curry numerals -/


-- @@ L265-268 expanded
/-- Curry numeral -/
def numeral : Nat → Part A
  | 0 => I
  | .succ n => HasDot.dot (HasDot.dot pair fal) (numeral n)


-- @@ L270-274 expanded
@[simp]
theorem df_numeral (n : Nat) : Part.Dom (numeral n : Part A) := by
  induction n with
  | zero => exact df_I
  | succ n ih => exact df_pair_app_app fal _ df_fal ih


-- @@ L276-277 expanded
/-- The successor of a Curry numeral -/
def succ : Part A :=
  HasDot.dot pair fal


-- @@ L279-280 expanded
@[simp]
theorem df_succ : Part.Dom (succ : Part A) :=
  df_pair_app fal df_fal


-- @@ L282-284 expanded
@[simp]
theorem df_succ_app (u : Part A) (hu : Part.Dom u) : Part.Dom (HasDot.dot succ u) :=
  df_pair_app_app fal u df_fal hu


-- @@ L286-287 verbatim
/-- Is a numeral equal to zero? -/
def iszero : Part A := fst


-- @@ L289-294 expanded
@[simp]
theorem eq_iszero_0 : HasDot.dot iszero (numeral 0) = (tru : Part A) :=
  by
  change HasDot.dot fst I = tru
  rw [eq_fst I df_I]
  change HasDot.dot I K = K
  exact eq_I df_K₀


-- @@ L296-299 expanded
@[simp]
theorem eq_iszero_succ (n : Nat) : HasDot.dot iszero (numeral n.succ) = (fal : Part A) :=
  by
  change HasDot.dot fst (HasDot.dot (HasDot.dot pair fal) (numeral n)) = fal
  rw [eq_fst_pair fal _ df_fal (df_numeral n)]


-- @@ L301-302 expanded
/-- Predecessor of a Curry numeral -/
def pred : Part A :=
  LeanPool.PartialCombinatoryAlgebras.PCA.compile (Γ := Lean.Name)
    (LeanPool.PartialCombinatoryAlgebras.PCA.abstr `x
      (HasDot.dot (HasDot.dot (HasDot.dot fst.elm (.var `x)) .I) (HasDot.dot snd.elm (.var `x))))


-- @@ L304-305 expanded
@[simp]
theorem df_pred : Part.Dom (pred : Part A) :=
  df_abstr _ _ _


-- @@ L307-307 verbatim
namespace pred


-- @@ L309-311 verbatim
/-- The predecessor combinator as a formal expression. -/
@[reducible]
def elm {Γ} : Expr Γ A := .elm (pred.get df_pred)


-- @@ L313-313 verbatim
end pred


-- @@ L315-315 verbatim
namespace primrec


-- @@ L317-323 expanded
/-- Auxiliary combinator used in the definition of primitive recursion. -/
def R : Part A :=
  LeanPool.PartialCombinatoryAlgebras.PCA.compile (Γ := Lean.Name)
    (LeanPool.PartialCombinatoryAlgebras.PCA.abstr `r
      (LeanPool.PartialCombinatoryAlgebras.PCA.abstr `x
        (LeanPool.PartialCombinatoryAlgebras.PCA.abstr `f
          (LeanPool.PartialCombinatoryAlgebras.PCA.abstr `m
            (HasDot.dot (HasDot.dot (HasDot.dot fst.elm (.var `m)) (HasDot.dot .K (.var `x)))
              (LeanPool.PartialCombinatoryAlgebras.PCA.abstr `y
                (HasDot.dot (HasDot.dot (.var `f) (HasDot.dot pred.elm (.var `m)))
                  (HasDot.dot
                    (HasDot.dot (HasDot.dot (HasDot.dot (.var `r) (.var `x)) (.var `f))
                      (HasDot.dot pred.elm (.var `m)))
                    .I))))))))


-- @@ L325-326 expanded
@[simp]
theorem df_R : Part.Dom (R : Part A) :=
  df_abstr _ _ _


-- @@ L328-328 verbatim
namespace R


-- @@ L330-331 verbatim
/-- The auxiliary combinator `primrec.R` as a formal expression. -/
def elm {Γ} : Expr Γ A := .elm (primrec.R.get primrec.df_R)


-- @@ L333-333 verbatim
end R


-- @@ L335-335 verbatim
end primrec


-- @@ L337-339 expanded
/-- Primitive recursion -/
def primrec : Part A :=
  LeanPool.PartialCombinatoryAlgebras.PCA.compile (Γ := Lean.Name)
    (LeanPool.PartialCombinatoryAlgebras.PCA.abstr `x
      (LeanPool.PartialCombinatoryAlgebras.PCA.abstr `f
        (LeanPool.PartialCombinatoryAlgebras.PCA.abstr `m
          (HasDot.dot
            (HasDot.dot
              (HasDot.dot (HasDot.dot (HasDot.dot Z.elm primrec.R.elm) (.var `x)) (.var `f))
              (.var `m))
            .I))))


-- @@ L341-341 verbatim
end PCA


-- @@ L343-343 verbatim
end LeanPool.PartialCombinatoryAlgebras
