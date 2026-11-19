/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Formalisation.HansenCograph.Invariant
import Formalisation.Mathlib.Analysis.Convex.BrunnMinkowski


-- @@ L9-9 verbatim
set_option linter.unusedSectionVars false

-- @@ L10-10 verbatim
set_option linter.unusedFintypeInType false

-- @@ L11-11 verbatim
set_option linter.unusedDecidableInType false


-- @@ L13-13 verbatim
open scoped BigOperators Pointwise

-- @@ L14-14 verbatim
open Set

-- @@ L15-15 verbatim
open MeasureTheory

-- @@ L16-16 verbatim
open SimpleGraph


-- @@ L18-18 verbatim
universe u v w


-- @@ L20-20 verbatim
namespace HansenCograph


-- @@ L22-24 verbatim
/-!
## Graph-side normalized Mahler ratio
-/


-- @@ L26-26 verbatim
section GraphRho


-- @@ L28-28 verbatim
variable {V : Type u} [Fintype V] [DecidableEq V]


-- @@ L30-39 verbatim
/--
Graph-side formula for the normalized Hansen Mahler ratio:

    graphRho(G)
      = N(G) N(Gᶜ) / (2^(m+2) (m+1)!).
-/
noncomputable def graphRho (G : SimpleGraph V) : ℝ :=
  N G * N Gᶜ /
    ((2 : ℝ) ^ (Fintype.card V + 2) *
      ((Fintype.card V + 1).factorial : ℝ))


-- @@ L41-46 verbatim
theorem graphRho_nonneg (G : SimpleGraph V) :
    0 ≤ graphRho G := by
  unfold graphRho
  exact div_nonneg
    (mul_nonneg (N_nonneg G) (N_nonneg Gᶜ))
    (by positivity)


-- @@ L48-53 verbatim
theorem graphRho_pos (G : SimpleGraph V) :
    0 < graphRho G := by
  unfold graphRho
  exact div_pos
    (mul_pos (N_pos G) (N_pos Gᶜ))
    (by positivity)


-- @@ L55-60 verbatim
@[simp]
theorem graphRho_compl (G : SimpleGraph V) :
    graphRho Gᶜ = graphRho G := by
  unfold graphRho
  simp only [compl_compl]
  ring


-- @@ L62-62 verbatim
end GraphRho


-- @@ L64-72 verbatim
/-!
## Exact correlation identity

For `G = A ⊕g B`:

  rho(G)
    = rho(A) rho(B)
      * (∫q_A q_B) / ((∫q_A)(∫q_B)).
-/


-- @@ L74-74 verbatim
section CorrelationIdentity


-- @@ L76-76 verbatim
variable {V : Type u} [Fintype V] [DecidableEq V]

-- @@ L77-77 verbatim
variable {W : Type v} [Fintype W] [DecidableEq W]


-- @@ L79-110 expanded
theorem graphRho_sum_eq (A : SimpleGraph V) (B : SimpleGraph W) :
    graphRho (A ⊕g B) =
      graphRho A * graphRho B *
        ((∫ x in (0 : ℝ)..1, q A x * q B x) /
          ((∫ x in (0 : ℝ)..1, q A x) * (∫ x in (0 : ℝ)..1, q B x))) :=
  by
  have hcompl : (A ⊕g B)ᶜ = graphJoin Aᶜ Bᶜ :=
    by
    unfold graphJoin
    rw [compl_compl, compl_compl]
  have hNsum :
    N (A ⊕g B) =
      2 * ((Fintype.card V + Fintype.card W + 1).factorial : ℝ) *
        (∫ x in (0 : ℝ)..1, q A x * q B x) :=
    by
    rw [N_eq_two_factorial_mul_integral_q, Fintype.card_sum]
    congr 1
    apply intervalIntegral.integral_congr
    intro x hx
    exact q_sum A B x
  have hNcompl : N (A ⊕g B)ᶜ = N Aᶜ * N Bᶜ / 2 := by rw [hcompl, N_join]
  have hNA := N_eq_two_factorial_mul_integral_q A
  have hNB := N_eq_two_factorial_mul_integral_q B
  have hIA : (∫ x in (0 : ℝ)..1, q A x) ≠ 0 := ne_of_gt (integral_q_pos A)
  have hIB : (∫ x in (0 : ℝ)..1, q B x) ≠ 0 := ne_of_gt (integral_q_pos B)
  unfold graphRho
  rw [hNsum, hNcompl, hNA, hNB, Fintype.card_sum]
  field_simp [hIA, hIB, pow_add]
  ring


-- @@ L112-112 verbatim
end CorrelationIdentity


-- @@ L114-126 verbatim
/-!
## Generic integral Chebyshev / positive covariance

Rather than approximating by sums, prove the continuous integral inequality
from the double-integral covariance identity

  1/2 ∫∫ (f(x)-f(y))(g(x)-g(y))
    = ∫fg - (∫f)(∫g)

on the probability interval [0,1].

This is a reusable Mathlib-quality lemma.
-/


-- @@ L128-128 verbatim
section IntegralChebyshev


-- @@ L130-138 verbatim
/--
Two functions are "monovary" on `[0,1]` if their pairwise differences always
have the same sign.
-/
def MonovaryOnUnit (f g : ℝ → ℝ) : Prop :=
  ∀ ⦃x y : ℝ⦄,
    x ∈ Set.Icc (0 : ℝ) 1 →
    y ∈ Set.Icc (0 : ℝ) 1 →
    0 ≤ (f x - f y) * (g x - g y)


-- @@ L140-222 verbatim
/--
Continuous Chebyshev integral inequality on [0,1].
-/
theorem integral_mul_ge_mul_integral_of_monovary
    {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1))
    (hmono : MonovaryOnUnit f g) :
    (∫ x in (0 : ℝ)..1, f x) *
        (∫ x in (0 : ℝ)..1, g x)
      ≤
    ∫ x in (0 : ℝ)..1, f x * g x := by
  let D : ℝ → ℝ → ℝ := fun x y =>
    (f x - f y) * (g x - g y)
  have hfi : IntervalIntegrable f volume 0 1 :=
    hf.intervalIntegrable_of_Icc (by norm_num)
  have hgi : IntervalIntegrable g volume 0 1 :=
    hg.intervalIntegrable_of_Icc (by norm_num)
  have hfgi : IntervalIntegrable (fun x => f x * g x) volume 0 1 :=
    (hf.mul hg).intervalIntegrable_of_Icc (by norm_num)
  have hnonneg :
      0 ≤ ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, D x y := by
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro x hx
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro y hy
    exact hmono hx hy
  have hinner (x : ℝ) :
      (∫ y in (0 : ℝ)..1, D x y) =
        (f x * g x -
          f x * (∫ y in (0 : ℝ)..1, g y) -
          (∫ y in (0 : ℝ)..1, f y) * g x) +
          (∫ y in (0 : ℝ)..1, f y * g y) := by
    have hconst : IntervalIntegrable
        (fun _ : ℝ => f x * g x) volume 0 1 :=
      continuousOn_const.intervalIntegrable_of_Icc (by norm_num)
    have hfxg : IntervalIntegrable
        (fun y : ℝ => f x * g y) volume 0 1 :=
      (continuousOn_const.mul hg).intervalIntegrable_of_Icc (by norm_num)
    have hfygx : IntervalIntegrable
        (fun y : ℝ => f y * g x) volume 0 1 :=
      (hf.mul continuousOn_const).intervalIntegrable_of_Icc (by norm_num)
    have hD : (fun y => D x y) =
        (fun y => ((f x * g x - f x * g y) - f y * g x) +
          f y * g y) := by
      funext y
      dsimp [D]
      ring
    rw [hD]
    rw [intervalIntegral.integral_add
      ((hconst.sub hfxg).sub hfygx) hfgi]
    rw [intervalIntegral.integral_sub (hconst.sub hfxg) hfygx]
    rw [intervalIntegral.integral_sub hconst hfxg]
    rw [intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const]
    norm_num
  have hdouble :
      (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, D x y) =
        2 * ((∫ x in (0 : ℝ)..1, f x * g x) -
          (∫ x in (0 : ℝ)..1, f x) *
            (∫ x in (0 : ℝ)..1, g x)) := by
    rw [intervalIntegral.integral_congr (fun x hx => hinner x)]
    have hfg_sub : IntervalIntegrable
        (fun x => f x * g x -
          f x * (∫ y in (0 : ℝ)..1, g y)) volume 0 1 :=
      hfgi.sub (hfi.mul_const _)
    have hthree : IntervalIntegrable
        (fun x => f x * g x -
          f x * (∫ y in (0 : ℝ)..1, g y) -
          (∫ y in (0 : ℝ)..1, f y) * g x) volume 0 1 :=
      hfg_sub.sub (hgi.const_mul _)
    rw [intervalIntegral.integral_add hthree
      (continuousOn_const.intervalIntegrable_of_Icc (by norm_num))]
    rw [intervalIntegral.integral_sub hfg_sub (hgi.const_mul _)]
    rw [intervalIntegral.integral_sub hfgi (hfi.mul_const _)]
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    norm_num
    ring
  rw [hdouble] at hnonneg
  nlinarith


-- @@ L224-337 verbatim
/--
Strict version: if the difference product is positive at one pair of points,
continuity makes it positive on a rectangle of positive measure.
-/
theorem integral_mul_gt_mul_integral_of_strict_monovary
    {f g : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) 1))
    (hg : ContinuousOn g (Set.Icc (0 : ℝ) 1))
    (hmono : MonovaryOnUnit f g)
    (hstrict :
      ∃ x y : ℝ,
        x ∈ Set.Icc (0 : ℝ) 1 ∧
        y ∈ Set.Icc (0 : ℝ) 1 ∧
        0 < (f x - f y) * (g x - g y)) :
    (∫ x in (0 : ℝ)..1, f x) *
        (∫ x in (0 : ℝ)..1, g x)
      <
    ∫ x in (0 : ℝ)..1, f x * g x := by
  rcases hstrict with ⟨x₀, y₀, hx₀, hy₀, hDxy⟩
  let D : ℝ → ℝ → ℝ := fun x y =>
    (f x - f y) * (g x - g y)
  let I : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..1, D x y
  have hfi : IntervalIntegrable f volume 0 1 :=
    hf.intervalIntegrable_of_Icc (by norm_num)
  have hgi : IntervalIntegrable g volume 0 1 :=
    hg.intervalIntegrable_of_Icc (by norm_num)
  have hfgi : IntervalIntegrable (fun x => f x * g x) volume 0 1 :=
    (hf.mul hg).intervalIntegrable_of_Icc (by norm_num)
  have hDcont (x : ℝ) : ContinuousOn (D x) (Set.Icc (0 : ℝ) 1) := by
    dsimp [D]
    exact (continuousOn_const.sub hf).mul (continuousOn_const.sub hg)
  have hInonneg : ∀ x ∈ Set.Ioc (0 : ℝ) 1, 0 ≤ I x := by
    intro x hx
    dsimp [I]
    apply intervalIntegral.integral_nonneg (by norm_num)
    intro y hy
    exact hmono ⟨hx.1.le, hx.2⟩ hy
  have hIx₀ : 0 < I x₀ := by
    dsimp [I]
    apply intervalIntegral.integral_pos (by norm_num) (hDcont x₀)
    · intro y hy
      exact hmono hx₀ ⟨hy.1.le, hy.2⟩
    · exact ⟨y₀, hy₀, hDxy⟩
  have hinner (x : ℝ) :
      I x =
        (f x * g x -
          f x * (∫ y in (0 : ℝ)..1, g y) -
          (∫ y in (0 : ℝ)..1, f y) * g x) +
          (∫ y in (0 : ℝ)..1, f y * g y) := by
    have hconst : IntervalIntegrable
        (fun _ : ℝ => f x * g x) volume 0 1 :=
      continuousOn_const.intervalIntegrable_of_Icc (by norm_num)
    have hfxg : IntervalIntegrable
        (fun y : ℝ => f x * g y) volume 0 1 :=
      (continuousOn_const.mul hg).intervalIntegrable_of_Icc (by norm_num)
    have hfygx : IntervalIntegrable
        (fun y : ℝ => f y * g x) volume 0 1 :=
      (hf.mul continuousOn_const).intervalIntegrable_of_Icc (by norm_num)
    have hD : (fun y => D x y) =
        (fun y => ((f x * g x - f x * g y) - f y * g x) +
          f y * g y) := by
      funext y
      dsimp [D]
      ring
    dsimp [I]
    rw [hD]
    rw [intervalIntegral.integral_add
      ((hconst.sub hfxg).sub hfygx) hfgi]
    rw [intervalIntegral.integral_sub (hconst.sub hfxg) hfygx]
    rw [intervalIntegral.integral_sub hconst hfxg]
    rw [intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_mul_const]
    norm_num
  have hIcont : ContinuousOn I (Set.Icc (0 : ℝ) 1) := by
    have hIeq : I = fun x =>
        (f x * g x -
          f x * (∫ y in (0 : ℝ)..1, g y) -
          (∫ y in (0 : ℝ)..1, f y) * g x) +
          (∫ y in (0 : ℝ)..1, f y * g y) := by
      funext x
      exact hinner x
    rw [hIeq]
    exact (((hf.mul hg).sub (hf.mul continuousOn_const)).sub
      (continuousOn_const.mul hg)).add continuousOn_const
  have hdoublepos : 0 < ∫ x in (0 : ℝ)..1, I x := by
    apply intervalIntegral.integral_pos (by norm_num) hIcont hInonneg
    exact ⟨x₀, hx₀, hIx₀⟩
  have hfg_sub : IntervalIntegrable
      (fun x => f x * g x -
        f x * (∫ y in (0 : ℝ)..1, g y)) volume 0 1 :=
    hfgi.sub (hfi.mul_const _)
  have hthree : IntervalIntegrable
      (fun x => f x * g x -
        f x * (∫ y in (0 : ℝ)..1, g y) -
        (∫ y in (0 : ℝ)..1, f y) * g x) volume 0 1 :=
    hfg_sub.sub (hgi.const_mul _)
  have hdouble :
      (∫ x in (0 : ℝ)..1, I x) =
        2 * ((∫ x in (0 : ℝ)..1, f x * g x) -
          (∫ x in (0 : ℝ)..1, f x) *
            (∫ x in (0 : ℝ)..1, g x)) := by
    rw [intervalIntegral.integral_congr (fun x hx => hinner x)]
    rw [intervalIntegral.integral_add hthree
      (continuousOn_const.intervalIntegrable_of_Icc (by norm_num))]
    rw [intervalIntegral.integral_sub hfg_sub (hgi.const_mul _)]
    rw [intervalIntegral.integral_sub hfgi (hfi.mul_const _)]
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const]
    norm_num
    ring
  rw [hdouble] at hdoublepos
  nlinarith


-- @@ L339-339 verbatim
end IntegralChebyshev


-- @@ L341-348 verbatim
/-!
## Symmetry + Brunn--Minkowski => q is monotone toward the centre

Brunn--Minkowski implies `q_G^(1/m)` is concave.
Together with `q_G(x)=q_G(1-x)`, this makes `q_G` nondecreasing on [0,1/2].

Only this order-theoretic consequence is needed by the cograph proof.
-/


-- @@ L350-350 verbatim
section BrunnMinkowskiInterface


-- @@ L352-352 verbatim
variable {V : Type u} [Fintype V] [DecidableEq V]


-- @@ L354-358 verbatim
private theorem stableIndicators_finite (G : SimpleGraph V) :
    (stableIndicators G).Finite := by
  refine Set.Finite.subset (Set.finite_range (indicator : Finset V → V → ℝ)) ?_
  rintro x ⟨s, hs, rfl⟩
  exact Set.mem_range_self s


-- @@ L360-362 verbatim
private theorem isCompact_stab (G : SimpleGraph V) :
    IsCompact (stab G) := by
  exact (stableIndicators_finite G).isCompact_convexHull ℝ


-- @@ L364-368 verbatim
private theorem isCompact_sectionSet (G : SimpleGraph V) (x : ℝ) :
    IsCompact (sectionSet G x) := by
  unfold sectionSet
  exact ((isCompact_stab G).smul x).add
    ((isCompact_stab G).smul (-(1 - x)))


-- @@ L370-374 verbatim
private theorem convex_sectionSet (G : SimpleGraph V) (x : ℝ) :
    Convex ℝ (sectionSet G x) := by
  unfold sectionSet
  exact ((convex_stab G).smul x).add
    ((convex_stab G).smul (-(1 - x)))


-- @@ L376-382 verbatim
private theorem zero_mem_sectionSet (G : SimpleGraph V) (x : ℝ) :
    (0 : V → ℝ) ∈ sectionSet G x := by
  unfold sectionSet
  rw [Set.mem_add]
  refine ⟨0, ?_, 0, ?_, by simp⟩
  · exact Set.mem_smul_set.mpr ⟨0, zero_mem_stab G, by simp⟩
  · exact Set.mem_smul_set.mpr ⟨0, zero_mem_stab G, by simp⟩


-- @@ L384-406 verbatim
private theorem exists_weighted_stab
    (G : SimpleGraph V) {r s : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s)
    {p q : V → ℝ} (hp : p ∈ stab G) (hq : q ∈ stab G) :
    ∃ w ∈ stab G, r • p + s • q = (r + s) • w := by
  by_cases hrs : r + s = 0
  · have hr0 : r = 0 := by linarith
    have hs0 : s = 0 := by linarith
    subst r
    subst s
    exact ⟨0, zero_mem_stab G, by simp⟩
  · have hrspos : 0 < r + s := lt_of_le_of_ne (add_nonneg hr hs) (Ne.symm hrs)
    let a := r / (r + s)
    let b := s / (r + s)
    have ha : 0 ≤ a := div_nonneg hr hrspos.le
    have hb : 0 ≤ b := div_nonneg hs hrspos.le
    have hab : a + b = 1 := by
      dsimp [a, b]
      field_simp
    refine ⟨a • p + b • q, (convex_stab G) hp hq ha hb hab, ?_⟩
    dsimp [a, b]
    ext v
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    field_simp


-- @@ L408-458 verbatim
private theorem sectionSet_combo_subset
    (G : SimpleGraph V)
    {x y a b : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) (hy : y ∈ Set.Icc (0 : ℝ) 1)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a • sectionSet G x + b • sectionSet G y ⊆
      sectionSet G (a * x + b * y) := by
  rintro z ⟨zx, hzx, zy, hzy, rfl⟩
  rcases Set.mem_smul_set.mp hzx with ⟨sx, hsx, rfl⟩
  rcases Set.mem_smul_set.mp hzy with ⟨sy, hsy, rfl⟩
  rcases Set.mem_add.mp hsx with ⟨xp, hxp, xn, hxn, hsx'⟩
  rcases Set.mem_add.mp hsy with ⟨yp, hyp, yn, hyn, hsy'⟩
  rcases Set.mem_smul_set.mp hxp with ⟨p, hp, hxp'⟩
  rcases Set.mem_smul_set.mp hxn with ⟨q, hq, hxn'⟩
  rcases Set.mem_smul_set.mp hyp with ⟨p', hp', hyp'⟩
  rcases Set.mem_smul_set.mp hyn with ⟨q', hq', hyn'⟩
  have hax : 0 ≤ a * x := mul_nonneg ha hx.1
  have hby : 0 ≤ b * y := mul_nonneg hb hy.1
  obtain ⟨p'', hp'', hpcomb⟩ :=
    exists_weighted_stab G hax hby hp hp'
  have hanx : 0 ≤ a * (1 - x) :=
    mul_nonneg ha (sub_nonneg.mpr hx.2)
  have hbny : 0 ≤ b * (1 - y) :=
    mul_nonneg hb (sub_nonneg.mpr hy.2)
  obtain ⟨q'', hq'', hqcomb⟩ :=
    exists_weighted_stab G hanx hbny hq hq'
  have hqneg :
      (-(1 - (a * x + b * y))) • q'' =
        a • (-(1 - x) • q) + b • (-(1 - y) • q') := by
    ext v
    have hqv := congrFun hqcomb v
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hqv ⊢
    have hcoeff :
        1 - (a * x + b * y) = a * (1 - x) + b * (1 - y) := by
      nlinarith
    rw [hcoeff]
    linear_combination hqv
  unfold sectionSet
  apply Set.mem_add.mpr
  refine ⟨(a * x + b * y) • p'',
    Set.smul_mem_smul_set hp'',
    (-(1 - (a * x + b * y))) • q'',
    Set.smul_mem_smul_set hq'', ?_⟩
  subst sx
  subst sy
  subst xp
  subst xn
  subst yp
  subst yn
  rw [← hpcomb, hqneg]
  module


-- @@ L460-465 verbatim
private theorem volume_smul_toReal
    {S : Set (V → ℝ)} {r : ℝ} (hr : 0 ≤ r) :
    (volume (r • S)).toReal =
      r ^ Fintype.card V * (volume S).toReal := by
  rw [Measure.addHaar_smul]
  simp [abs_of_nonneg hr, abs_pow, pow_nonneg hr]


-- @@ L467-472 verbatim
private theorem rpow_nat_pow_inv
    {r : ℝ} (hr : 0 ≤ r) (hcard : Fintype.card V ≠ 0) :
    Real.rpow (r ^ Fintype.card V) ((Fintype.card V : ℝ)⁻¹) = r := by
  rw [Real.rpow_eq_pow, ← Real.rpow_natCast, ← Real.rpow_mul hr]
  have hcast : (Fintype.card V : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcard
  rw [mul_inv_cancel₀ hcast, Real.rpow_one]


-- @@ L474-485 verbatim
private theorem sectionSet_smul_root
    (G : SimpleGraph V) {x r : ℝ} (hr : 0 ≤ r)
    (hcard : Fintype.card V ≠ 0) :
    Real.rpow (volume (r • sectionSet G x)).toReal
        ((Fintype.card V : ℝ)⁻¹) =
      r * Real.rpow (volume (sectionSet G x)).toReal
        ((Fintype.card V : ℝ)⁻¹) := by
  rw [volume_smul_toReal hr]
  simp only [Real.rpow_eq_pow]
  rw [Real.mul_rpow (pow_nonneg hr _)
    ENNReal.toReal_nonneg]
  rw [← Real.rpow_eq_pow, rpow_nat_pow_inv hr hcard]


-- @@ L487-547 verbatim
/--
Brunn--Minkowski/Brunn concavity interface.

For nonzero dimension, `q_G^(1/m)` is concave on [0,1].
Dimension zero is handled separately.
-/
theorem section_root_concave (G : SimpleGraph V) :
    Fintype.card V = 0 ∨
      ConcaveOn ℝ (Set.Icc (0 : ℝ) 1)
        (fun x => Real.rpow (q G x) ((Fintype.card V : ℝ)⁻¹)) := by
  by_cases hzero : Fintype.card V = 0
  · exact Or.inl hzero
  right
  let _ : Nonempty V := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hzero)
  refine ⟨convex_Icc (0 : ℝ) 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hcombo : a * x + b * y ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact add_nonneg (mul_nonneg ha hx.1) (mul_nonneg hb hy.1)
    · calc
        a * x + b * y ≤ a * 1 + b * 1 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left hx.2 ha)
            (mul_le_mul_of_nonneg_left hy.2 hb)
        _ = 1 := by linarith
  let A : Set (V → ℝ) := a • sectionSet G x
  let B : Set (V → ℝ) := b • sectionSet G y
  have hAcompact : IsCompact A := (isCompact_sectionSet G x).smul a
  have hBcompact : IsCompact B := (isCompact_sectionSet G y).smul b
  have hABcompact : IsCompact (A + B) := hAcompact.add hBcompact
  have hAne : A.Nonempty := by
    exact ⟨a • (0 : V → ℝ), Set.smul_mem_smul_set (zero_mem_sectionSet G x)⟩
  have hBne : B.Nonempty := by
    exact ⟨b • (0 : V → ℝ), Set.smul_mem_smul_set (zero_mem_sectionSet G y)⟩
  have hbm := brunn_minkowski_fintype_toReal
    hAne hAcompact.measurableSet hBne hBcompact.measurableSet
    hABcompact.measurableSet hAcompact.measure_lt_top.ne
    hBcompact.measure_lt_top.ne hABcompact.measure_lt_top.ne
  have hsubset : A + B ⊆ sectionSet G (a * x + b * y) := by
    exact sectionSet_combo_subset G hx hy ha hb hab
  have hvol : (volume (A + B)).toReal ≤
      (volume (sectionSet G (a * x + b * y))).toReal := by
    exact ENNReal.toReal_mono
      (isCompact_sectionSet G (a * x + b * y)).measure_lt_top.ne
      (measure_mono hsubset)
  have hrootmono :
      Real.rpow (volume (A + B)).toReal ((Fintype.card V : ℝ)⁻¹) ≤
        Real.rpow (volume (sectionSet G (a * x + b * y))).toReal
          ((Fintype.card V : ℝ)⁻¹) :=
    Real.rpow_le_rpow ENNReal.toReal_nonneg hvol (by positivity)
  dsimp [A, B] at hbm
  simp only [← Real.rpow_eq_pow] at hbm
  rw [sectionSet_smul_root G ha hzero,
    sectionSet_smul_root G hb hzero] at hbm
  change a * Real.rpow (q G x) ((Fintype.card V : ℝ)⁻¹) +
      b * Real.rpow (q G y) ((Fintype.card V : ℝ)⁻¹) ≤
    Real.rpow (q G (a * x + b * y)) ((Fintype.card V : ℝ)⁻¹)
  rw [q_eq_section_volume G hx.1 hx.2,
    q_eq_section_volume G hy.1 hy.2,
    q_eq_section_volume G hcombo.1 hcombo.2]
  exact hbm.trans hrootmono


-- @@ L549-592 verbatim
/--
The exact downstream consequence needed from Brunn--Minkowski.
-/
theorem q_monotoneOn_half (G : SimpleGraph V) :
    MonotoneOn (q G) (Set.Icc (0 : ℝ) (1 / 2 : ℝ)) := by
  intro x hx y hy hxy
  by_cases hzero : Fintype.card V = 0
  · have : IsEmpty V := Fintype.card_eq_zero_iff.mp hzero
    have hG : G = ⊥ := by
      ext u v
      exact isEmptyElim u
    subst G
    have huniv : (Finset.univ : Finset V) = ∅ :=
      Finset.card_eq_zero.mp (by simp)
    unfold q
    rw [huniv]
    simp [qCoeff, nuInduced, inducedFinset, nu_bot]
  · have hconc := (section_root_concave G).resolve_left hzero
    have hcardpos : 0 < Fintype.card V := Nat.pos_of_ne_zero hzero
    have hexp : 0 < ((Fintype.card V : ℝ)⁻¹) := by
      exact inv_pos.mpr (Nat.cast_pos.mpr hcardpos)
    have hxfull : x ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact hx.1
      · linarith [hx.2]
    have hxmirror : 1 - x ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith [hx.1, hx.2]
    have hseg : y ∈ segment ℝ x (1 - x) := by
      rw [segment_eq_Icc (by linarith [hx.2])]
      constructor
      · exact hxy
      · linarith [hy.2]
    have hroot := hconc.ge_on_segment hxfull hxmirror hseg
    have hsymroot :
        Real.rpow (q G (1 - x)) ((Fintype.card V : ℝ)⁻¹) =
          Real.rpow (q G x) ((Fintype.card V : ℝ)⁻¹) := by
      rw [q_one_sub]
    rw [hsymroot, min_self] at hroot
    by_contra hnot
    have hlt : q G y < q G x := lt_of_not_ge hnot
    have hry : 0 ≤ q G y :=
      q_nonneg_on_unit G hy.1 (by linarith [hy.2])
    have hrootlt := Real.rpow_lt_rpow hry hlt hexp
    exact (not_lt_of_ge hroot) hrootlt


-- @@ L594-599 verbatim
/--
Convenient bundled property.
-/
def SymmCenterIncreasing (f : ℝ → ℝ) : Prop :=
  (∀ x : ℝ, f (1 - x) = f x) ∧
  MonotoneOn f (Set.Icc (0 : ℝ) (1 / 2 : ℝ))


-- @@ L601-605 verbatim
theorem q_symmCenterIncreasing (G : SimpleGraph V) :
    SymmCenterIncreasing (q G) := by
  constructor
  · exact q_one_sub G
  · exact q_monotoneOn_half G


-- @@ L607-607 verbatim
end BrunnMinkowskiInterface


-- @@ L609-611 verbatim
/-!
## Symmetric centre-increasing functions are similarly ordered
-/


-- @@ L613-613 verbatim
section SymmetricOrder


-- @@ L615-667 verbatim
/--
If f and g are symmetric about 1/2 and increase toward 1/2, then their
differences have the same sign on [0,1].

Proof idea:
  each function is a monotone function of `min x (1-x)`, equivalently a
  monotone function of distance to the centre with reversed orientation.
-/
theorem monovary_of_symmCenterIncreasing
    {f g : ℝ → ℝ}
    (hf : SymmCenterIncreasing f)
    (hg : SymmCenterIncreasing g) :
    MonovaryOnUnit f g := by
  intro x y hx hy
  rcases hf with ⟨hsf, hmf⟩
  rcases hg with ⟨hsg, hmg⟩
  let fold : ℝ → ℝ := fun z => min z (1 - z)
  have fold_mem (z : ℝ) (hz : z ∈ Set.Icc (0 : ℝ) 1) :
      fold z ∈ Set.Icc (0 : ℝ) (1 / 2 : ℝ) := by
    constructor
    · exact le_min hz.1 (sub_nonneg.mpr hz.2)
    · by_cases h : z ≤ (1 / 2 : ℝ)
      · exact (min_le_left z (1 - z)).trans h
      · have hz' : 1 - z ≤ (1 / 2 : ℝ) := by linarith
        exact (min_le_right z (1 - z)).trans hz'
  have f_fold (z : ℝ) : f (fold z) = f z := by
    dsimp [fold]
    by_cases h : z ≤ 1 - z
    · rw [min_eq_left h]
    · rw [min_eq_right (le_of_not_ge h)]
      exact hsf z
  have g_fold (z : ℝ) : g (fold z) = g z := by
    dsimp [fold]
    by_cases h : z ≤ 1 - z
    · rw [min_eq_left h]
    · rw [min_eq_right (le_of_not_ge h)]
      exact hsg z
  rcases le_total (fold x) (fold y) with hxy | hyx
  · have hfx : f (fold x) ≤ f (fold y) :=
      hmf (fold_mem x hx) (fold_mem y hy) hxy
    have hgx : g (fold x) ≤ g (fold y) :=
      hmg (fold_mem x hx) (fold_mem y hy) hxy
    rw [f_fold x, f_fold y] at hfx
    rw [g_fold x, g_fold y] at hgx
    exact mul_nonneg_of_nonpos_of_nonpos
      (sub_nonpos.mpr hfx) (sub_nonpos.mpr hgx)
  · have hfy : f (fold y) ≤ f (fold x) :=
      hmf (fold_mem y hy) (fold_mem x hx) hyx
    have hgy : g (fold y) ≤ g (fold x) :=
      hmg (fold_mem y hy) (fold_mem x hx) hyx
    rw [f_fold y, f_fold x] at hfy
    rw [g_fold y, g_fold x] at hgy
    exact mul_nonneg (sub_nonneg.mpr hfy) (sub_nonneg.mpr hgy)


-- @@ L669-669 verbatim
end SymmetricOrder


-- @@ L671-673 verbatim
/-!
## Positive correlation of Hansen section profiles
-/


-- @@ L675-675 verbatim
section QCorrelation


-- @@ L677-677 verbatim
variable {V : Type u} [Fintype V] [DecidableEq V]

-- @@ L678-678 verbatim
variable {W : Type v} [Fintype W] [DecidableEq W]


-- @@ L680-691 verbatim
theorem q_positive_correlation
    (A : SimpleGraph V) (B : SimpleGraph W) :
    (∫ x in (0 : ℝ)..1, q A x) *
        (∫ x in (0 : ℝ)..1, q B x)
      ≤
    ∫ x in (0 : ℝ)..1, q A x * q B x := by
  apply integral_mul_ge_mul_integral_of_monovary
  · exact (continuous_q A).continuousOn
  · exact (continuous_q B).continuousOn
  · exact monovary_of_symmCenterIncreasing
      (q_symmCenterIncreasing A)
      (q_symmCenterIncreasing B)


-- @@ L693-714 verbatim
/--
The main multiplicativity inequality under disjoint union.
-/
theorem graphRho_mul_le_sum
    (A : SimpleGraph V) (B : SimpleGraph W) :
    graphRho A * graphRho B ≤ graphRho (A ⊕g B) := by
  rw [graphRho_sum_eq A B]
  have hcorr := q_positive_correlation A B
  have hIA : 0 < ∫ x in (0 : ℝ)..1, q A x :=
    integral_q_pos A
  have hIB : 0 < ∫ x in (0 : ℝ)..1, q B x :=
    integral_q_pos B
  have hquot :
      1 ≤
        (∫ x in (0 : ℝ)..1, q A x * q B x) /
          ((∫ x in (0 : ℝ)..1, q A x) *
           (∫ x in (0 : ℝ)..1, q B x)) := by
    apply (le_div_iff₀ (mul_pos hIA hIB)).2
    simpa using hcorr
  have hρ : 0 ≤ graphRho A * graphRho B :=
    mul_nonneg (graphRho_nonneg A) (graphRho_nonneg B)
  nlinarith


-- @@ L716-716 verbatim
end QCorrelation


-- @@ L718-731 verbatim
/-!
## Equality: q constant iff G is edgeless

Mathematical route:

  q constant
  => q(1/2)=q(0)
  => every projection coefficient has its minimum value
  => an edge would make its singleton projection coefficient strictly larger
  => G has no edge
  => STAB(G) is the cube, hence centrally symmetric.

Conversely, if G is edgeless, STAB(G) is the cube and q ≡ 1.
-/


-- @@ L733-733 verbatim
section QConstancy


-- @@ L735-735 verbatim
variable {V : Type u} [Fintype V] [DecidableEq V]


-- @@ L737-739 verbatim
/-- A function takes the same value at every pair of arguments. -/
def IsConstantFunction {α β : Sort*} (f : α → β) : Prop :=
  ∀ x y, f x = f y


-- @@ L741-744 verbatim
private noncomputable def projectionBox (G : SimpleGraph V) (s : Finset V) :
    Set (V → ℝ) :=
  (splitEquiv s) ⁻¹'
    (stab (inducedFinset G s) ×ˢ stab (inducedFinset G sᶜ))


-- @@ L746-755 verbatim
private theorem mem_projectionBox_iff
    (G : SimpleGraph V) (s : Finset V) (x : V → ℝ) :
    x ∈ projectionBox G s ↔
      restrictTo s x ∈ stab (inducedFinset G s) ∧
      restrictTo sᶜ x ∈ stab (inducedFinset G sᶜ) := by
  unfold projectionBox
  change splitEquiv s x ∈
      (stab (inducedFinset G s) ×ˢ stab (inducedFinset G sᶜ)) ↔ _
  rw [splitEquiv_apply]
  rfl


-- @@ L757-761 verbatim
private theorem stab_subset_projectionBox (G : SimpleGraph V) (s : Finset V) :
    stab G ⊆ projectionBox G s := by
  intro x hx
  rw [mem_projectionBox_iff]
  exact ⟨restrictTo_mem_stab G s hx, restrictTo_mem_stab G sᶜ hx⟩


-- @@ L763-778 verbatim
private theorem convex_projectionBox (G : SimpleGraph V) (s : Finset V) :
    Convex ℝ (projectionBox G s) := by
  intro x hx y hy a b ha hb hab
  rw [mem_projectionBox_iff] at hx hy ⊢
  have hs : restrictTo s (a • x + b • y) =
      a • restrictTo s x + b • restrictTo s y := by
    ext v
    rfl
  have hsc : restrictTo sᶜ (a • x + b • y) =
      a • restrictTo sᶜ x + b • restrictTo sᶜ y := by
    ext v
    rfl
  rw [hs, hsc]
  constructor
  · exact (convex_stab (inducedFinset G s)) hx.1 hy.1 ha hb hab
  · exact (convex_stab (inducedFinset G sᶜ)) hx.2 hy.2 ha hb hab


-- @@ L780-784 verbatim
private theorem interior_projectionBox_nonempty
    (G : SimpleGraph V) (s : Finset V) :
    (interior (projectionBox G s)).Nonempty := by
  obtain ⟨x, hx⟩ := interior_stab_nonempty G
  exact ⟨x, interior_mono (stab_subset_projectionBox G s) hx⟩


-- @@ L786-793 verbatim
private theorem projectionBox_volume_toReal
    (G : SimpleGraph V) (s : Finset V) :
    (volume (projectionBox G s)).toReal =
      (volume (stab (inducedFinset G s))).toReal *
        (volume (stab (inducedFinset G sᶜ))).toReal := by
  unfold projectionBox
  rw [(splitEquiv_measurePreserving (V := V) s).measure_preimage_equiv]
  rw [Measure.volume_eq_prod, Measure.prod_prod, ENNReal.toReal_mul]


-- @@ L795-803 verbatim
private theorem projectionBox_volume_ne_top
    (G : SimpleGraph V) (s : Finset V) :
    volume (projectionBox G s) ≠ ⊤ := by
  unfold projectionBox
  rw [(splitEquiv_measurePreserving (V := V) s).measure_preimage_equiv]
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_ne_top
    (volume_stab_ne_top (inducedFinset G s))
    (volume_stab_ne_top (inducedFinset G sᶜ))


-- @@ L805-818 verbatim
private theorem qCoeff_eq_projectionBox_volume
    (G : SimpleGraph V) (s : Finset V) :
    qCoeff G s = (volume (projectionBox G s)).toReal := by
  rw [projectionBox_volume_toReal]
  unfold qCoeff nuInduced nu
  have hs : Fintype.card ↥(↑s : Set V) = s.card := by simp
  have hsc : Fintype.card ↥(↑sᶜ : Set V) = Fintype.card V - s.card := by
    rw [← Finset.card_compl s]
    unfold Fintype.card
    simp
  rw [hs, hsc]
  have hsf : (s.card.factorial : ℝ) ≠ 0 := by positivity
  have hscf : ((Fintype.card V - s.card).factorial : ℝ) ≠ 0 := by positivity
  field_simp


-- @@ L820-831 verbatim
private theorem projectionBox_empty (G : SimpleGraph V) :
    projectionBox G ∅ = stab G := by
  ext x
  rw [mem_projectionBox_iff]
  constructor
  · rintro ⟨hempty, hfull⟩
    have hext := extendZero_mem_stab G (∅ : Finset V)ᶜ hfull
    convert hext using 1
    ext v
    simp [extendZero, restrictTo]
  · intro hx
    exact (stab_subset_projectionBox G ∅) hx


-- @@ L833-835 verbatim
private theorem qCoeff_empty_eq_volume_stab (G : SimpleGraph V) :
    qCoeff G ∅ = (volume (stab G)).toReal := by
  rw [qCoeff_eq_projectionBox_volume, projectionBox_empty]


-- @@ L837-842 verbatim
private theorem qCoeff_empty_le (G : SimpleGraph V) (s : Finset V) :
    qCoeff G ∅ ≤ qCoeff G s := by
  rw [qCoeff_empty_eq_volume_stab, qCoeff_eq_projectionBox_volume]
  exact ENNReal.toReal_mono
    (projectionBox_volume_ne_top G s)
    (measure_mono (stab_subset_projectionBox G s))


-- @@ L844-872 verbatim
private theorem convex_eq_of_subset_of_volume_eq
    {K L : Set (V → ℝ)}
    (hKcompact : IsCompact K) (hLconvex : Convex ℝ L)
    (hLint : (interior L).Nonempty) (hKL : K ⊆ L)
    (hvol : volume K = volume L) : K = L := by
  apply Set.Subset.antisymm hKL
  have hinterior : interior L ⊆ K := by
    intro x hx
    by_contra hxK
    let U := interior L \ K
    have hUopen : IsOpen U :=
      isOpen_interior.sdiff hKcompact.isClosed
    have hUne : U.Nonempty := ⟨x, hx, hxK⟩
    have hUpos : 0 < volume U := hUopen.measure_pos volume hUne
    have hUsub : U ⊆ L \ K := by
      exact Set.sdiff_subset_sdiff interior_subset (Set.Subset.rfl)
    have hdiff : volume (L \ K) = 0 := by
      rw [MeasureTheory.measure_sdiff hKL hKcompact.measurableSet.nullMeasurableSet
        hKcompact.measure_lt_top.ne, ← hvol, tsub_self]
    have hmono : (volume : Measure (V → ℝ)) U ≤ volume (L \ K) :=
      measure_mono hUsub
    rw [hdiff] at hmono
    exact (not_lt_of_ge hmono) hUpos
  have hclosure : closure (interior L) ⊆ K :=
    closure_minimal hinterior hKcompact.isClosed
  intro x hx
  apply hclosure
  rw [hLconvex.closure_interior_eq_closure_of_nonempty_interior hLint]
  exact subset_closure hx


-- @@ L874-932 verbatim
private theorem qCoeff_singleton_lt_of_adj
    (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    qCoeff G ∅ < qCoeff G {u} := by
  have hle := qCoeff_empty_le G {u}
  rcases hle.lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    have hreal :
        (volume (stab G)).toReal =
          (volume (projectionBox G {u})).toReal := by
      rw [← qCoeff_empty_eq_volume_stab G,
        ← qCoeff_eq_projectionBox_volume G {u}]
      exact heq
    have hvol : volume (stab G) = volume (projectionBox G {u}) := by
      apply le_antisymm
      · exact (ENNReal.toReal_le_toReal
          (volume_stab_ne_top G)
          (projectionBox_volume_ne_top G {u})).mp hreal.le
      · exact (ENNReal.toReal_le_toReal
          (projectionBox_volume_ne_top G {u})
          (volume_stab_ne_top G)).mp hreal.ge
    have hsets : stab G = projectionBox G {u} :=
      convex_eq_of_subset_of_volume_eq
        (isCompact_stab G) (convex_projectionBox G {u})
        (interior_projectionBox_nonempty G {u})
        (stab_subset_projectionBox G {u}) hvol
    have hzbox : indicator ({u, v} : Finset V) ∈ projectionBox G {u} := by
      rw [mem_projectionBox_iff]
      constructor
      · rw [restrictTo_indicator]
        apply indicator_mem_stab
        intro a ha b hb hab
        exfalso
        apply hab
        apply Subtype.ext
        have ha' : (a : V) = u := by simpa using a.property
        have hb' : (b : V) = u := by simpa using b.property
        exact ha'.trans hb'.symm
      · rw [restrictTo_indicator]
        apply indicator_mem_stab
        intro a ha b hb hab
        exfalso
        apply hab
        apply Subtype.ext
        have ha' : (a : V) = u ∨ (a : V) = v := by
          simpa [restrictFinset] using ha
        have hb' : (b : V) = u ∨ (b : V) = v := by
          simpa [restrictFinset] using hb
        have hau : (a : V) ≠ u := by simpa using a.property
        have hbu : (b : V) ≠ u := by simpa using b.property
        exact (ha'.resolve_left hau).trans (hb'.resolve_left hbu).symm
    have hz : indicator ({u, v} : Finset V) ∈ stab G := by
      rw [hsets]
      exact hzbox
    have hedge := stab_edge_ineq G hz huv
    have hu_mem : u ∈ ({u, v} : Finset V) := by simp
    have hv_mem : v ∈ ({u, v} : Finset V) := by simp
    rw [indicator_apply_mem hu_mem, indicator_apply_mem hv_mem] at hedge
    norm_num at hedge


-- @@ L934-943 verbatim
private theorem q_zero_eq_qCoeff_empty (G : SimpleGraph V) :
    q G 0 = qCoeff G ∅ := by
  classical
  unfold q
  rw [Finset.sum_eq_single ∅]
  · simp
  · intro s hs hne
    have hcard : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
    simp [zero_pow hcard.ne']
  · simp


-- @@ L945-964 verbatim
private theorem q_mid_eq_scaled_coeff_sum (G : SimpleGraph V) :
    q G (1 / 2 : ℝ) =
      (1 / 2 : ℝ) ^ Fintype.card V *
        ∑ s ∈ (Finset.univ : Finset V).powerset, qCoeff G s := by
  classical
  unfold q
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  have hcard : s.card + (Fintype.card V - s.card) = Fintype.card V :=
    Nat.add_sub_of_le (Finset.card_le_univ s)
  norm_num
  calc
    qCoeff G s * (1 / 2 : ℝ) ^ s.card *
          (1 / 2 : ℝ) ^ (Fintype.card V - s.card) =
        qCoeff G s * ((1 / 2 : ℝ) ^ s.card *
          (1 / 2 : ℝ) ^ (Fintype.card V - s.card)) := by ring
    _ = qCoeff G s * (1 / 2 : ℝ) ^ Fintype.card V := by
      rw [← pow_add, hcard]
    _ = (1 / 2 : ℝ) ^ Fintype.card V * qCoeff G s := by ring


-- @@ L966-987 verbatim
private theorem q_mid_gt_endpoint_of_adj
    (G : SimpleGraph V) {u v : V} (huv : G.Adj u v) :
    q G 0 < q G (1 / 2 : ℝ) := by
  classical
  let a := qCoeff G ∅
  let P := (Finset.univ : Finset V).powerset
  have hsum :
      (∑ _s ∈ P, a) < ∑ s ∈ P, qCoeff G s := by
    apply Finset.sum_lt_sum
    · intro s hs
      exact qCoeff_empty_le G s
    · refine ⟨{u}, ?_, ?_⟩
      · simp [P]
      · exact qCoeff_singleton_lt_of_adj G huv
  have hscale : 0 < (1 / 2 : ℝ) ^ Fintype.card V := by positivity
  have hscaled := mul_lt_mul_of_pos_left hsum hscale
  rw [q_zero_eq_qCoeff_empty, q_mid_eq_scaled_coeff_sum]
  change a < (1 / 2 : ℝ) ^ Fintype.card V * ∑ s ∈ P, qCoeff G s
  calc
    a = (1 / 2 : ℝ) ^ Fintype.card V * ∑ _s ∈ P, a := by
      simp [P]
    _ < _ := hscaled


-- @@ L989-1011 verbatim
/-- Equality in the section inequality makes `STAB(G)` centrally symmetric. -/
theorem centrallySymmetric_stab_of_q_mid_eq_endpoint
    (G : SimpleGraph V)
    (h : q G (1 / 2 : ℝ) = q G 0) :
    ∃ c : V → ℝ,
      ∀ x : V → ℝ,
        x ∈ stab G ↔ (2 • c - x) ∈ stab G := by
  have hG : G = ⊥ := by
    apply le_antisymm
    · intro u v huv
      have hstrict := q_mid_gt_endpoint_of_adj G huv
      linarith
    · exact bot_le
  refine ⟨fun _ => (1 / 2 : ℝ), ?_⟩
  rw [hG, stab_bot]
  intro x
  simp only [Set.mem_Icc, Pi.le_def, Pi.zero_apply, Pi.one_apply,
    Pi.sub_apply, Pi.smul_apply]
  constructor <;> rintro ⟨hlower, hupper⟩ <;> constructor <;> intro v
  all_goals specialize hlower v
  all_goals specialize hupper v
  all_goals norm_num at *
  all_goals linarith


-- @@ L1013-1039 verbatim
/--
The only possible centre of symmetry of a stable-set polytope is
(1/2,...,1/2), because every coordinate ranges exactly from 0 to 1.
-/
theorem stab_symmetry_center_eq_half
    (G : SimpleGraph V)
    {c : V → ℝ}
    (hc :
      ∀ x : V → ℝ,
        x ∈ stab G ↔ (2 • c - x) ∈ stab G) :
    c = fun _ => (1 / 2 : ℝ) := by
  funext v
  have hzero : (0 : V → ℝ) ∈ stab G := zero_mem_stab G
  have hreflectZero : (2 • c - (0 : V → ℝ)) ∈ stab G :=
    (hc (0 : V → ℝ)).mp hzero
  have hupper := stab_coordinate_le_one G hreflectZero v
  have hsingleton : indicator ({v} : Finset V) ∈ stab G := by
    apply indicator_mem_stab
    simp
  have hreflectSingleton :
      (2 • c - indicator ({v} : Finset V)) ∈ stab G :=
    (hc (indicator ({v} : Finset V))).mp hsingleton
  have hlower := stab_coordinate_nonneg G hreflectSingleton v
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply,
    indicator_apply_mem (Finset.mem_singleton_self v)] at hupper hlower
  norm_num at hupper hlower ⊢
  linarith


-- @@ L1041-1057 verbatim
theorem allOnes_mem_stab_of_centrallySymmetric
    (G : SimpleGraph V)
    (hsym :
      ∃ c : V → ℝ,
        ∀ x : V → ℝ,
          x ∈ stab G ↔ (2 • c - x) ∈ stab G) :
    (fun _ : V => (1 : ℝ)) ∈ stab G := by
  obtain ⟨c, hc⟩ := hsym
  have hc' : c = fun _ : V => (1 / 2 : ℝ) :=
    stab_symmetry_center_eq_half G hc
  subst c
  have h0 : (0 : V → ℝ) ∈ stab G :=
    zero_mem_stab G
  have hreflect := (hc (0 : V → ℝ)).mp h0
  convert hreflect using 1
  ext v
  norm_num [Pi.smul_apply]


-- @@ L1059-1067 verbatim
theorem eq_bot_of_allOnes_mem_stab
    (G : SimpleGraph V)
    (h1 : (fun _ : V => (1 : ℝ)) ∈ stab G) :
    G = ⊥ := by
  apply le_antisymm
  · intro u v huv
    have hineq := stab_edge_ineq G h1 huv
    norm_num at hineq
  · exact bot_le


-- @@ L1069-1090 verbatim
@[simp]
theorem q_bot_eq_one (x : ℝ) :
    q (⊥ : SimpleGraph V) x = 1 := by
  classical
  have hcoeff (s : Finset V) :
      qCoeff (⊥ : SimpleGraph V) s = 1 := by
    unfold qCoeff nuInduced inducedFinset
    change nu (⊥ : SimpleGraph ↥(↑s : Set V)) *
        nu (⊥ : SimpleGraph ↥(↑sᶜ : Set V)) /
          ((s.card.factorial : ℝ) *
            ((Fintype.card V - s.card).factorial : ℝ)) = 1
    simp only [nu_bot, Set.fintypeCard_eq_ncard,
      Set.ncard_coe_finset, Finset.card_compl]
    field_simp
  unfold q
  simp_rw [hcoeff, one_mul]
  rw [show (∑ s ∈ Finset.univ.powerset,
      x ^ s.card * (1 - x) ^ (Fintype.card V - s.card)) =
      (x + (1 - x)) ^ Fintype.card V by
        simpa using Finset.sum_pow_mul_eq_add_pow
          x (1 - x) (Finset.univ : Finset V)]
  simp


-- @@ L1092-1098 verbatim
/--
For an edgeless graph, the section profile is constant.
-/
theorem q_bot_constant :
    IsConstantFunction (q (⊥ : SimpleGraph V)) := by
  intro x y
  rw [q_bot_eq_one, q_bot_eq_one]


-- @@ L1100-1112 verbatim
theorem q_constant_iff_edgeless (G : SimpleGraph V) :
    IsConstantFunction (q G) ↔ G = ⊥ := by
  constructor
  · intro hq
    have hmid : q G (1 / 2 : ℝ) = q G 0 :=
      hq _ _
    have hsym :=
      centrallySymmetric_stab_of_q_mid_eq_endpoint G hmid
    exact eq_bot_of_allOnes_mem_stab G
      (allOnes_mem_stab_of_centrallySymmetric G hsym)
  · intro hG
    subst G
    exact q_bot_constant


-- @@ L1114-1133 verbatim
/--
Nonconstant q has strict centre rise.
-/
theorem q_mid_gt_endpoint_of_nonconstant
    (G : SimpleGraph V)
    (h : ¬ IsConstantFunction (q G)) :
    q G 0 < q G (1 / 2 : ℝ) := by
  have hle : q G 0 ≤ q G (1 / 2 : ℝ) := by
    apply q_monotoneOn_half G
    · norm_num
    · norm_num
    · norm_num
  apply lt_of_le_of_ne hle
  intro heq
  have hmid : q G (1 / 2 : ℝ) = q G 0 := heq.symm
  have hsym := centrallySymmetric_stab_of_q_mid_eq_endpoint G hmid
  have hG : G = ⊥ :=
    eq_bot_of_allOnes_mem_stab G
      (allOnes_mem_stab_of_centrallySymmetric G hsym)
  exact h ((q_constant_iff_edgeless G).mpr hG)


-- @@ L1135-1135 verbatim
end QConstancy


-- @@ L1137-1139 verbatim
/-!
## Strict correlation and sharp union equality
-/


-- @@ L1141-1141 verbatim
section StrictCorrelation


-- @@ L1143-1143 verbatim
variable {V : Type u} [Fintype V] [DecidableEq V]

-- @@ L1144-1144 verbatim
variable {W : Type v} [Fintype W] [DecidableEq W]


-- @@ L1146-1165 verbatim
theorem q_strict_positive_correlation
    (A : SimpleGraph V) (B : SimpleGraph W)
    (hA : ¬ IsConstantFunction (q A))
    (hB : ¬ IsConstantFunction (q B)) :
    (∫ x in (0 : ℝ)..1, q A x) *
        (∫ x in (0 : ℝ)..1, q B x)
      <
    ∫ x in (0 : ℝ)..1, q A x * q B x := by
  apply integral_mul_gt_mul_integral_of_strict_monovary
  · exact (continuous_q A).continuousOn
  · exact (continuous_q B).continuousOn
  · exact monovary_of_symmCenterIncreasing
      (q_symmCenterIncreasing A)
      (q_symmCenterIncreasing B)
  · refine ⟨(1 / 2 : ℝ), 0, ?_, ?_, ?_⟩
    · norm_num
    · norm_num
    · have hA' := q_mid_gt_endpoint_of_nonconstant A hA
      have hB' := q_mid_gt_endpoint_of_nonconstant B hB
      nlinarith [mul_pos (sub_pos.mpr hA') (sub_pos.mpr hB')]


-- @@ L1167-1234 verbatim
/--
Sharp equality for the disjoint-union correlation factor.

Equality holds exactly when at least one child is edgeless.
-/
theorem graphRho_sum_eq_mul_iff
    (A : SimpleGraph V) (B : SimpleGraph W) :
    graphRho (A ⊕g B) = graphRho A * graphRho B
      ↔ A = ⊥ ∨ B = ⊥ := by
  constructor
  · intro hEq
    by_contra h
    push Not at h
    obtain ⟨hAne, hBne⟩ := h
    have hqA : ¬ IsConstantFunction (q A) := by
      intro hconst
      exact hAne ((q_constant_iff_edgeless A).mp hconst)
    have hqB : ¬ IsConstantFunction (q B) := by
      intro hconst
      exact hBne ((q_constant_iff_edgeless B).mp hconst)
    have hstrict :=
      q_strict_positive_correlation A B hqA hqB
    have hIA : 0 < ∫ x in (0 : ℝ)..1, q A x :=
      integral_q_pos A
    have hIB : 0 < ∫ x in (0 : ℝ)..1, q B x :=
      integral_q_pos B
    have hfactor :
        1 <
          (∫ x in (0 : ℝ)..1, q A x * q B x) /
            ((∫ x in (0 : ℝ)..1, q A x) *
             (∫ x in (0 : ℝ)..1, q B x)) := by
      apply (lt_div_iff₀ (mul_pos hIA hIB)).2
      simpa using hstrict
    rw [graphRho_sum_eq A B] at hEq
    have hρ : 0 < graphRho A * graphRho B := by
      exact mul_pos (graphRho_pos A) (graphRho_pos B)
    nlinarith
  · rintro (hA | hB)
    · subst A
      have hfun : q (⊥ : SimpleGraph V) =
          fun _ => q (⊥ : SimpleGraph V) 0 := by
        funext x
        exact q_bot_constant x 0
      have hcov :
          (∫ x in (0 : ℝ)..1,
              q (⊥ : SimpleGraph V) x * q B x) =
            (∫ x in (0 : ℝ)..1, q (⊥ : SimpleGraph V) x) *
              (∫ x in (0 : ℝ)..1, q B x) := by
        rw [hfun]
        simp
      rw [graphRho_sum_eq, hcov,
        div_self (mul_ne_zero (ne_of_gt (integral_q_pos _))
          (ne_of_gt (integral_q_pos B))), mul_one]
    · subst B
      have hfun : q (⊥ : SimpleGraph W) =
          fun _ => q (⊥ : SimpleGraph W) 0 := by
        funext x
        exact q_bot_constant x 0
      have hcov :
          (∫ x in (0 : ℝ)..1,
              q A x * q (⊥ : SimpleGraph W) x) =
            (∫ x in (0 : ℝ)..1, q A x) *
              (∫ x in (0 : ℝ)..1, q (⊥ : SimpleGraph W) x) := by
        rw [hfun]
        simp
      rw [graphRho_sum_eq, hcov,
        div_self (mul_ne_zero (ne_of_gt (integral_q_pos A))
          (ne_of_gt (integral_q_pos _))), mul_one]


-- @@ L1236-1236 verbatim
end StrictCorrelation


-- @@ L1238-1238 verbatim
end HansenCograph
