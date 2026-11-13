import Mathlib
import Submission.CompactHopfPairFiber
import Submission.StandardSaddleCobordism


-- @@ L5-21 verbatim
/-!
# A compact Hopf pair-of-pants model

In the first four spatial coordinates write `z = x₀ + i x₁` and
`u = x₂ + i x₃`.  The moving core equations are

`|x|² = 1`, `(z + a(t)) * conj(u) = ε(t)`.

At the incoming end `a = ε = 0`, so the fiber is the two coordinate
circles of `CompactHopfPairConfiguration`.  At the outgoing end `a = 2` and
`ε = 0`; since `|z| ≤ 1`, the coefficient `z + 2` cannot vanish and the
fiber is the single circle `u = 0`.

The spatial compactification uses the same positive radial background as the
compact Hopf pair.  Its radial row alone rules out every transition-annulus
zero, uniformly in `a` and `ε`.
-/


-- @@ L23-23 verbatim
set_option autoImplicit false


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
namespace Submission

-- @@ L28-28 verbatim
namespace CompactHopfPairPants


-- @@ L30-30 verbatim
open Set Function Metric InnerProductSpace

-- @@ L31-31 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L33-33 verbatim
variable (m : ℕ) (hm : 0 < m)

-- @@ L34-34 verbatim
include hm


-- @@ L36-36 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (m + 3))

-- @@ L37-37 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m + 2))


-- @@ L39-39 verbatim
/-! ## The moving polynomial core -/


-- @@ L41-43 verbatim
/-- Real part of `(z + a) * conj(u) - ε`. -/
def pairRe (a ε : ℝ) (x : E) : ℝ :=
  CompactHopfPairConfiguration.hopfRe m hm x + a * x 2 - ε


-- @@ L45-47 verbatim
/-- Imaginary part of `(z + a) * conj(u) - ε`. -/
def pairIm (a : ℝ) (x : E) : ℝ :=
  CompactHopfPairConfiguration.hopfIm m hm x - a * x 3


-- @@ L49-55 verbatim
lemma pair_normSq (a : ℝ) (x : E) :
    (CompactHopfPairConfiguration.hopfRe m hm x + a * x 2) ^ 2 +
        (CompactHopfPairConfiguration.hopfIm m hm x - a * x 3) ^ 2 =
      ((x 0 + a) ^ 2 + x 1 ^ 2) * (x 2 ^ 2 + x 3 ^ 2) := by
  simp only [CompactHopfPairConfiguration.hopfRe,
    CompactHopfPairConfiguration.hopfIm]
  ring


-- @@ L57-60 verbatim
lemma contDiff_pairRe (a ε : ℝ) : ContDiff ℝ ∞ (pairRe m hm a ε) := by
  exact ((CompactHopfPairConfiguration.contDiff_hopfRe m hm).add
    (contDiff_const.mul
      (EuclideanSpace.proj 2 : E →L[ℝ] ℝ).contDiff)).sub contDiff_const


-- @@ L62-65 verbatim
lemma contDiff_pairIm (a : ℝ) : ContDiff ℝ ∞ (pairIm m hm a) := by
  exact (CompactHopfPairConfiguration.contDiff_hopfIm m hm).sub
    (contDiff_const.mul
      (EuclideanSpace.proj 3 : E →L[ℝ] ℝ).contDiff)


-- @@ L67-73 verbatim
/-- The uncompactified spatial equation at parameters `(a,ε)`. -/
def coreMap (a ε : ℝ) (x : E) : F :=
  WithLp.toLp 2 fun i =>
    if i = 0 then (CompactBirth.normSq x - 1) / 2
    else if i = 1 then pairRe m hm a ε x
    else if i = 2 then pairIm m hm a x
    else x i.succ


-- @@ L75-77 verbatim
@[simp] lemma coreMap_apply_zero (a ε : ℝ) (x : E) :
    coreMap m hm a ε x 0 = (CompactBirth.normSq x - 1) / 2 := by
  simp [coreMap]


-- @@ L79-81 verbatim
@[simp] lemma coreMap_apply_one (a ε : ℝ) (x : E) :
    coreMap m hm a ε x 1 = pairRe m hm a ε x := by
  simp [coreMap]


-- @@ L83-94 verbatim
@[simp] lemma coreMap_apply_two (a ε : ℝ) (x : E) :
    coreMap m hm a ε x 2 = pairIm m hm a x := by
  have hm2 : 2 < m + 2 := by omega
  have h20 : (2 : Fin (m + 2)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt hm2] at hv
  have h21 : (2 : Fin (m + 2)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt hm2] at hv
  simp [coreMap, h20, h21]


-- @@ L96-99 verbatim
lemma coreMap_apply_tail (a ε : ℝ) (x : E) {i : Fin (m + 2)}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
    coreMap m hm a ε x i = x i.succ := by
  simp [coreMap, hi0, hi1, hi2]


-- @@ L101-115 verbatim
lemma contDiff_coreMap (a ε : ℝ) : ContDiff ℝ ∞ (coreMap m hm a ε) := by
  rw [contDiff_piLp]
  intro i
  by_cases hi0 : i = 0
  · subst i
    simpa only [coreMap_apply_zero] using
      (CompactBirth.contDiff_normSq.sub contDiff_const).div_const 2
  · by_cases hi1 : i = 1
    · subst i
      simpa only [coreMap_apply_one] using contDiff_pairRe m hm a ε
    · by_cases hi2 : i = 2
      · subst i
        simpa only [coreMap_apply_two] using contDiff_pairIm m hm a
      · simp only [coreMap_apply_tail m hm a ε _ hi0 hi1 hi2]
        exact (EuclideanSpace.proj i.succ : E →L[ℝ] ℝ).contDiff


-- @@ L117-117 verbatim
/-! ## Compactification -/


-- @@ L119-122 verbatim
/-- Compact spatial presentation with a common positive radial background. -/
def levelMap (a ε : ℝ) (x : E) : F :=
  (1 - CompactBirth.cutoff x) • coreMap m hm a ε x +
    CompactBirth.cutoff x • CompactHopfPairConfiguration.background m hm


-- @@ L124-127 verbatim
lemma contDiff_levelMap (a ε : ℝ) : ContDiff ℝ ∞ (levelMap m hm a ε) := by
  exact ((contDiff_const.sub CompactBirth.contDiff_cutoff).smul
    (contDiff_coreMap m hm a ε)).add
    (CompactBirth.contDiff_cutoff.smul contDiff_const)


-- @@ L129-134 verbatim
@[simp] lemma levelMap_apply_zero (a ε : ℝ) (x : E) :
    levelMap m hm a ε x 0 =
      (1 - CompactBirth.cutoff x) *
          ((CompactBirth.normSq x - 1) / 2) +
        CompactBirth.cutoff x := by
  simp [levelMap]


-- @@ L136-141 verbatim
lemma cutoff_ne_one_of_levelMap_eq_zero {a ε : ℝ} {x : E}
    (hx : levelMap m hm a ε x = 0) : CompactBirth.cutoff x ≠ 1 := by
  intro hc
  have h0 := congrArg (fun q : F => q 0) hx
  rw [levelMap_apply_zero, hc] at h0
  norm_num at h0


-- @@ L143-146 verbatim
lemma cutoff_lt_one_of_levelMap_eq_zero {a ε : ℝ} {x : E}
    (hx : levelMap m hm a ε x = 0) : CompactBirth.cutoff x < 1 :=
  lt_of_le_of_ne (CompactBirth.cutoff_le_one x)
    (cutoff_ne_one_of_levelMap_eq_zero m hm hx)


-- @@ L148-163 verbatim
/-- Uniformly in the moving parameters, a zero cannot enter the cutoff
annulus. -/
lemma normSq_lt_two_of_levelMap_eq_zero {a ε : ℝ} {x : E}
    (hx : levelMap m hm a ε x = 0) : CompactBirth.normSq x < 2 := by
  have hc_lt := cutoff_lt_one_of_levelMap_eq_zero m hm hx
  have hc0 := CompactBirth.cutoff_nonneg x
  have h0 := congrArg (fun q : F => q 0) hx
  rw [levelMap_apply_zero] at h0
  simp only [PiLp.zero_apply] at h0
  by_contra hnot
  have hn : 2 ≤ CompactBirth.normSq x := not_lt.mp hnot
  have hfac : 0 < 1 - CompactBirth.cutoff x := sub_pos.mpr hc_lt
  have hrad : 0 < (CompactBirth.normSq x - 1) / 2 := by linarith
  have hprod : 0 < (1 - CompactBirth.cutoff x) *
      ((CompactBirth.normSq x - 1) / 2) := mul_pos hfac hrad
  linarith


-- @@ L165-168 verbatim
lemma cutoff_eq_zero_of_levelMap_eq_zero {a ε : ℝ} {x : E}
    (hx : levelMap m hm a ε x = 0) : CompactBirth.cutoff x = 0 :=
  CompactBirth.cutoff_eq_zero
    (normSq_lt_two_of_levelMap_eq_zero m hm hx).le


-- @@ L170-184 verbatim
/-- The compact blend has exactly the polynomial zero set. -/
theorem levelMap_eq_zero_iff_coreMap_eq_zero (a ε : ℝ) (x : E) :
    levelMap m hm a ε x = 0 ↔ coreMap m hm a ε x = 0 := by
  constructor
  · intro hx
    have hc := cutoff_eq_zero_of_levelMap_eq_zero m hm hx
    simpa [levelMap, hc] using hx
  · intro hx
    have h0 := congrArg (fun q : F => q 0) hx
    rw [coreMap_apply_zero] at h0
    simp only [PiLp.zero_apply] at h0
    have hn : CompactBirth.normSq x = 1 := by linarith
    have hc : CompactBirth.cutoff x = 0 :=
      CompactBirth.cutoff_eq_zero (by rw [hn]; norm_num)
    simp [levelMap, hc, hx]


-- @@ L186-194 verbatim
/-- Literal common-background behavior outside the radius-two ball. -/
theorem levelMap_flatOutside (a ε : ℝ) {x : E} (hx : 2 ≤ ‖x‖) :
    levelMap m hm a ε x =
      CompactHopfPairConfiguration.background m hm := by
  have hs : 4 ≤ CompactBirth.normSq x := by
    rw [CompactBirth.normSq_eq_norm_sq]
    nlinarith [norm_nonneg x]
  have hc := CompactBirth.cutoff_eq_one hs
  simp [levelMap, hc]


-- @@ L196-196 verbatim
/-! ## Exact incoming and outgoing fibers -/


-- @@ L198-203 verbatim
lemma coreMap_zero_zero_eq_source :
    coreMap m hm 0 0 = CompactHopfPairConfiguration.coreMap m hm := by
  funext x
  apply PiLp.ext
  intro i
  simp [coreMap, pairRe, pairIm, CompactHopfPairConfiguration.coreMap]


-- @@ L205-209 verbatim
lemma levelMap_zero_zero_eq_source :
    levelMap m hm 0 0 = CompactHopfPairConfiguration.levelMap m hm := by
  funext x
  rw [levelMap, CompactHopfPairConfiguration.levelMap,
    coreMap_zero_zero_eq_source]


-- @@ L211-216 verbatim
lemma normSq_eq_one_of_coreMap_eq_zero {a ε : ℝ} {x : E}
    (hx : coreMap m hm a ε x = 0) : CompactBirth.normSq x = 1 := by
  have h0 := congrArg (fun q : F => q 0) hx
  rw [coreMap_apply_zero] at h0
  simp only [PiLp.zero_apply] at h0
  linarith


-- @@ L218-221 verbatim
lemma pairRe_eq_zero_of_coreMap_eq_zero {a ε : ℝ} {x : E}
    (hx : coreMap m hm a ε x = 0) : pairRe m hm a ε x = 0 := by
  have h := congrArg (fun q : F => q 1) hx
  simpa using h


-- @@ L223-226 verbatim
lemma pairIm_eq_zero_of_coreMap_eq_zero {a ε : ℝ} {x : E}
    (hx : coreMap m hm a ε x = 0) : pairIm m hm a x = 0 := by
  have h := congrArg (fun q : F => q 2) hx
  simpa using h


-- @@ L228-247 verbatim
lemma target_u_eq_zero_of_coreMap_eq_zero {x : E}
    (hx : coreMap m hm 2 0 x = 0) : x 2 = 0 ∧ x 3 = 0 := by
  have hre := pairRe_eq_zero_of_coreMap_eq_zero m hm hx
  have him := pairIm_eq_zero_of_coreMap_eq_zero m hm hx
  have hprod : ((x 0 + 2) ^ 2 + x 1 ^ 2) * (x 2 ^ 2 + x 3 ^ 2) = 0 := by
    rw [← pair_normSq m hm 2 x]
    simp [pairRe, pairIm] at hre him
    rw [hre, him]
    norm_num
  rcases mul_eq_zero.mp hprod with hcoef | hu
  · have hn := normSq_eq_one_of_coreMap_eq_zero m hm hx
    have hnormsq : ‖x‖ ^ 2 = 1 := by
      simpa [CompactBirth.normSq_eq_norm_sq] using hn
    have hnorm : ‖x‖ = 1 := by nlinarith [norm_nonneg x]
    have hx0 : x 0 = -2 := by
      nlinarith [sq_nonneg (x 0 + 2), sq_nonneg (x 1)]
    have hcoord := abs_coordinate_le_norm x (0 : Fin (m + 3))
    rw [hx0, hnorm] at hcoord
    norm_num at hcoord
  · constructor <;> nlinarith [sq_nonneg (x 2), sq_nonneg (x 3)]


-- @@ L249-269 verbatim
lemma target_coreMap_eq_source_of_eq_zero {x : E}
    (hx : coreMap m hm 2 0 x = 0) :
    CompactHopfPairConfiguration.coreMap m hm x = 0 := by
  have hu := target_u_eq_zero_of_coreMap_eq_zero m hm hx
  rw [← coreMap_zero_zero_eq_source]
  apply PiLp.ext
  intro i
  by_cases hi0 : i = 0
  · subst i
    simpa using congrArg (fun q : F => q 0) hx
  · by_cases hi1 : i = 1
    · subst i
      simp [coreMap_apply_one, pairRe,
        CompactHopfPairConfiguration.hopfRe, hu.1, hu.2]
    · by_cases hi2 : i = 2
      · subst i
        simp [coreMap_apply_two, pairIm,
          CompactHopfPairConfiguration.hopfIm, hu.1, hu.2]
      · rw [coreMap_apply_tail m hm 0 0 _ hi0 hi1 hi2]
        simpa [coreMap_apply_tail m hm 2 0 _ hi0 hi1 hi2] using
          congrArg (fun q : F => q i) hx


-- @@ L271-335 verbatim
theorem target_coreMap_eq_zero_iff_standardCircle (x : E) :
    coreMap m hm 2 0 x = 0 ↔ x ∈ standardCircle := by
  constructor
  · intro hx
    have hsource := target_coreMap_eq_source_of_eq_zero m hm hx
    have hu := target_u_eq_zero_of_coreMap_eq_zero m hm hx
    rcases (CompactHopfPairConfiguration.coreMap_eq_zero_iff_two_circles
      m hm x).mp hsource with hfirst | hsecond
    · exact hfirst
    · rcases hsecond with ⟨theta, htheta⟩
      have h2 := congrArg (fun q : E => q 2) htheta.symm
      have h3 := congrArg (fun q : E => q 3) htheta.symm
      rw [CompactHopfPairConfiguration.secondCircleAt_apply_two] at h2
      rw [CompactHopfPairConfiguration.secondCircleAt_apply_three] at h3
      rw [hu.1] at h2
      rw [hu.2] at h3
      exfalso
      nlinarith [Real.cos_sq_add_sin_sq theta]
  · rintro ⟨theta, rfl⟩
    have h20 : (2 : Fin (m + 3)) ≠ 0 := by
      intro h
      have hv := congrArg Fin.val h
      simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3)] at hv
    have h21 : (2 : Fin (m + 3)) ≠ 1 := by
      intro h
      have hv := congrArg Fin.val h
      simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3)] at hv
    have h30 : (3 : Fin (m + 3)) ≠ 0 := by
      intro h
      have hv := congrArg Fin.val h
      simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at hv
    have h31 : (3 : Fin (m + 3)) ≠ 1 := by
      intro h
      have hv := congrArg Fin.val h
      simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at hv
    have hc2 : circleAt (m := m) theta 2 = 0 :=
      circleAt_apply_other theta h20 h21
    have hc3 : circleAt (m := m) theta 3 = 0 :=
      circleAt_apply_other theta h30 h31
    apply PiLp.ext
    intro i
    by_cases hi0 : i = 0
    · subst i
      rw [coreMap_apply_zero, CompactBirth.normSq_eq_norm_sq,
        norm_circleAt, one_pow]
      norm_num
    · by_cases hi1 : i = 1
      · subst i
        rw [coreMap_apply_one, pairRe,
          CompactHopfPairConfiguration.hopfRe, hc2, hc3]
        ring_nf
        simp
      · by_cases hi2 : i = 2
        · subst i
          rw [coreMap_apply_two, pairIm,
            CompactHopfPairConfiguration.hopfIm, hc2, hc3]
          ring_nf
          simp
        · rw [coreMap_apply_tail m hm 2 0 _ hi0 hi1 hi2]
          apply circleAt_apply_other theta
          · exact Fin.succ_ne_zero i
          · intro h
            apply hi0
            apply Fin.succ_injective
            simpa using h


-- @@ L337-343 verbatim
theorem source_levelMap_eq_zero_iff_two_circles (x : E) :
    levelMap m hm 0 0 x = 0 ↔
      x ∈ standardCircle ∨
        x ∈ CompactHopfPairConfiguration.secondCircle m hm := by
  rw [levelMap_zero_zero_eq_source,
    CompactHopfPairConfiguration.levelMap_eq_zero_iff_coreMap_eq_zero,
    CompactHopfPairConfiguration.coreMap_eq_zero_iff_two_circles]


-- @@ L345-348 verbatim
theorem target_levelMap_eq_zero_iff_standardCircle (x : E) :
    levelMap m hm 2 0 x = 0 ↔ x ∈ standardCircle := by
  rw [levelMap_eq_zero_iff_coreMap_eq_zero,
    target_coreMap_eq_zero_iff_standardCircle]


-- @@ L350-350 verbatim
/-! ## Regularity of the outgoing slice -/


-- @@ L352-364 verbatim
omit hm in
private lemma fderiv_coord_apply
    (G : E → F) (hG : ContDiff ℝ ∞ G)
    (i : Fin (m + 2)) (x h : E) :
    fderiv ℝ (fun q => G q i) x h = fderiv ℝ G x h i := by
  let outProj : F →L[ℝ] ℝ := EuclideanSpace.proj i
  have hG' : HasFDerivAt G (fderiv ℝ G x) x :=
    (hG.differentiable infty_ne_zero x).hasFDerivAt
  have hcomp : HasFDerivAt (fun q => G q i)
      (outProj.comp (fderiv ℝ G x)) x := by
    exact (PiLp.hasFDerivAt_apply 2 (G x) i).comp x hG'
  have happ := congrArg (fun L : E →L[ℝ] ℝ => L h) hcomp.fderiv
  simpa [outProj] using happ


-- @@ L366-377 verbatim
lemma fderiv_target_coreMap_apply_zero (x h : E) :
    fderiv ℝ (coreMap m hm 2 0) x h 0 = ⟪x, h⟫_ℝ := by
  rw [← fderiv_coord_apply m (coreMap m hm 2 0)
    (contDiff_coreMap m hm 2 0) 0 x h]
  have hfun : (fun q : E => coreMap m hm 2 0 q 0) =
      fun q => CompactHopfPairConfiguration.coreMap m hm q 0 := by
    funext q
    simp
  rw [hfun, fderiv_coord_apply m
    (CompactHopfPairConfiguration.coreMap m hm)
    (CompactHopfPairConfiguration.contDiff_coreMap m hm) 0 x h]
  exact CompactHopfPairConfiguration.fderiv_coreMap_apply_zero m hm x h


-- @@ L379-406 verbatim
lemma fderiv_target_coreMap_apply_one (x h : E) :
    fderiv ℝ (coreMap m hm 2 0) x h 1 =
      h 0 * x 2 + (x 0 + 2) * h 2 + h 1 * x 3 + x 1 * h 3 := by
  rw [← fderiv_coord_apply m (coreMap m hm 2 0)
    (contDiff_coreMap m hm 2 0) 1 x h]
  have hfun : (fun q : E => coreMap m hm 2 0 q 1) =
      fun q => q 0 * q 2 + q 1 * q 3 + 2 * q 2 := by
    funext q
    simp [pairRe, CompactHopfPairConfiguration.hopfRe]
  rw [hfun]
  let p0 : E →L[ℝ] ℝ := EuclideanSpace.proj 0
  let p1 : E →L[ℝ] ℝ := EuclideanSpace.proj 1
  let p2 : E →L[ℝ] ℝ := EuclideanSpace.proj 2
  let p3 : E →L[ℝ] ℝ := EuclideanSpace.proj 3
  have h0 : HasFDerivAt (fun q : E => q 0) p0 x := p0.hasFDerivAt
  have h1 : HasFDerivAt (fun q : E => q 1) p1 x := p1.hasFDerivAt
  have h2 : HasFDerivAt (fun q : E => q 2) p2 x := p2.hasFDerivAt
  have h3 : HasFDerivAt (fun q : E => q 3) p3 x := p3.hasFDerivAt
  have hd := ((h0.mul h2).add (h1.mul h3)).add (h2.const_mul 2)
  have happ := congrArg (fun L : E →L[ℝ] ℝ => L h) hd.fderiv
  change fderiv ℝ (((fun q : E => q 0) * fun q => q 2) +
      ((fun q : E => q 1) * fun q => q 3) +
      fun q : E => 2 * q 2) x h = _
  calc
    _ = x 0 * h 2 + x 2 * h 0 +
        (x 1 * h 3 + x 3 * h 1) + 2 * h 2 := by
      simpa [p0, p1, p2, p3] using happ
    _ = _ := by ring


-- @@ L408-435 verbatim
lemma fderiv_target_coreMap_apply_two (x h : E) :
    fderiv ℝ (coreMap m hm 2 0) x h 2 =
      h 1 * x 2 + x 1 * h 2 - h 0 * x 3 - (x 0 + 2) * h 3 := by
  rw [← fderiv_coord_apply m (coreMap m hm 2 0)
    (contDiff_coreMap m hm 2 0) 2 x h]
  have hfun : (fun q : E => coreMap m hm 2 0 q 2) =
      fun q => q 1 * q 2 - q 0 * q 3 - 2 * q 3 := by
    funext q
    simp [pairIm, CompactHopfPairConfiguration.hopfIm]
  rw [hfun]
  let p0 : E →L[ℝ] ℝ := EuclideanSpace.proj 0
  let p1 : E →L[ℝ] ℝ := EuclideanSpace.proj 1
  let p2 : E →L[ℝ] ℝ := EuclideanSpace.proj 2
  let p3 : E →L[ℝ] ℝ := EuclideanSpace.proj 3
  have h0 : HasFDerivAt (fun q : E => q 0) p0 x := p0.hasFDerivAt
  have h1 : HasFDerivAt (fun q : E => q 1) p1 x := p1.hasFDerivAt
  have h2 : HasFDerivAt (fun q : E => q 2) p2 x := p2.hasFDerivAt
  have h3 : HasFDerivAt (fun q : E => q 3) p3 x := p3.hasFDerivAt
  have hd := ((h1.mul h2).sub (h0.mul h3)).sub (h3.const_mul 2)
  have happ := congrArg (fun L : E →L[ℝ] ℝ => L h) hd.fderiv
  change fderiv ℝ (((fun q : E => q 1) * fun q => q 2) -
      ((fun q : E => q 0) * fun q => q 3) -
      fun q : E => 2 * q 3) x h = _
  calc
    _ = x 1 * h 2 + x 2 * h 1 -
        (x 0 * h 3 + x 3 * h 0) - 2 * h 3 := by
      simpa [p0, p1, p2, p3] using happ
    _ = _ := by ring


-- @@ L437-447 verbatim
lemma fderiv_target_coreMap_apply_tail (x h : E) {i : Fin (m + 2)}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
    fderiv ℝ (coreMap m hm 2 0) x h i = h i.succ := by
  rw [← fderiv_coord_apply m (coreMap m hm 2 0)
    (contDiff_coreMap m hm 2 0) i x h]
  have hfun : (fun q : E => coreMap m hm 2 0 q i) = fun q => q i.succ := by
    funext q
    exact coreMap_apply_tail m hm 2 0 q hi0 hi1 hi2
  rw [hfun]
  exact congrArg (fun L : E →L[ℝ] ℝ => L h)
    (EuclideanSpace.proj i.succ : E →L[ℝ] ℝ).hasFDerivAt.fderiv


-- @@ L449-456 verbatim
/-- Explicit right inverse for the outgoing core differential. -/
def targetPreimage (_hm : 0 < m) (x : E) (y : F) : E :=
  let S := (x 0 + 2) ^ 2 + x 1 ^ 2
  WithLp.toLp 2 <| Fin.cases (x 0 * y 0) fun i =>
    if i = 0 then x 1 * y 0
    else if i = 1 then ((x 0 + 2) * y 1 + x 1 * y 2) / S
    else if i = 2 then (x 1 * y 1 - (x 0 + 2) * y 2) / S
    else y i


-- @@ L458-460 verbatim
@[simp] lemma targetPreimage_apply_zero (x : E) (y : F) :
    targetPreimage m hm x y 0 = x 0 * y 0 := by
  simp [targetPreimage]


-- @@ L462-472 verbatim
@[simp] lemma targetPreimage_apply_succ (x : E) (y : F) (i : Fin (m + 2)) :
    targetPreimage m hm x y i.succ =
      if i = 0 then x 1 * y 0
      else if i = 1 then
        ((x 0 + 2) * y 1 + x 1 * y 2) /
          ((x 0 + 2) ^ 2 + x 1 ^ 2)
      else if i = 2 then
        (x 1 * y 1 - (x 0 + 2) * y 2) /
          ((x 0 + 2) ^ 2 + x 1 ^ 2)
      else y i := by
  simp [targetPreimage]


-- @@ L474-484 verbatim
@[simp] lemma targetPreimage_apply_one (x : E) (y : F) :
    targetPreimage m hm x y 1 = x 1 * y 0 := by
  have h1 : (1 : Fin (m + 3)) = (0 : Fin (m + 2)).succ := by
    apply Fin.ext
    simp
  calc
    targetPreimage m hm x y 1 =
        targetPreimage m hm x y (0 : Fin (m + 2)).succ :=
      congrArg (fun j => targetPreimage m hm x y j) h1
    _ = _ := by
      simpa using targetPreimage_apply_succ m hm x y (0 : Fin (m + 2))


-- @@ L486-504 verbatim
@[simp] lemma targetPreimage_apply_two (x : E) (y : F) :
    targetPreimage m hm x y 2 =
      ((x 0 + 2) * y 1 + x 1 * y 2) /
        ((x 0 + 2) ^ 2 + x 1 ^ 2) := by
  have h2 : (2 : Fin (m + 3)) = (1 : Fin (m + 2)).succ := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 1 < m + 2),
      Nat.mod_eq_of_lt (by omega : 2 < m + 3)]
  have h10 : (1 : Fin (m + 2)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 1 < m + 2)] at hv
  calc
    targetPreimage m hm x y 2 =
        targetPreimage m hm x y (1 : Fin (m + 2)).succ :=
      congrArg (fun j => targetPreimage m hm x y j) h2
    _ = _ := by
      simpa [h10] using
        targetPreimage_apply_succ m hm x y (1 : Fin (m + 2))


-- @@ L506-528 verbatim
@[simp] lemma targetPreimage_apply_three (x : E) (y : F) :
    targetPreimage m hm x y 3 =
      (x 1 * y 1 - (x 0 + 2) * y 2) /
        ((x 0 + 2) ^ 2 + x 1 ^ 2) := by
  have h3 : (3 : Fin (m + 3)) = (2 : Fin (m + 2)).succ := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2),
      Nat.mod_eq_of_lt (by omega : 3 < m + 3)]
  have h20 : (2 : Fin (m + 2)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2)] at hv
  have h21 : (2 : Fin (m + 2)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2)] at hv
  calc
    targetPreimage m hm x y 3 =
        targetPreimage m hm x y (2 : Fin (m + 2)).succ :=
      congrArg (fun j => targetPreimage m hm x y j) h3
    _ = _ := by
      simpa [h20, h21] using
        targetPreimage_apply_succ m hm x y (2 : Fin (m + 2))


-- @@ L530-533 verbatim
lemma targetPreimage_apply_tail (x : E) (y : F) {i : Fin (m + 2)}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
    targetPreimage m hm x y i.succ = y i := by
  simp [targetPreimage, hi0, hi1, hi2]


-- @@ L535-540 verbatim
omit hm in
private lemma inner_eq_sum_local (x h : E) :
    ⟪x, h⟫_ℝ = ∑ j, x j * h j := by
  rw [PiLp.inner_apply]
  exact Finset.sum_congr rfl fun j _ => by
    simp [RCLike.inner_apply, mul_comm]


-- @@ L542-568 verbatim
lemma inner_targetPreimage {x : E}
    (hx : coreMap m hm 2 0 x = 0) (y : F) :
    ⟪x, targetPreimage m hm x y⟫_ℝ = y 0 := by
  have hu := target_u_eq_zero_of_coreMap_eq_zero m hm hx
  have hsource := target_coreMap_eq_source_of_eq_zero m hm hx
  rw [inner_eq_sum_local]
  have hpoint : ∀ j : Fin (m + 3),
      x j * targetPreimage m hm x y j = x j ^ 2 * y 0 := by
    intro j
    by_cases hj0 : j = 0
    · subst j
      simp [pow_two, mul_assoc]
    · by_cases hj1 : j = 1
      · subst j
        simp [pow_two, mul_assoc]
      · by_cases hj2 : j = 2
        · subst j
          simp [hu.1]
        · by_cases hj3 : j = 3
          · subst j
            simp [hu.2]
          · rw [CompactHopfPairConfiguration.coordinate_eq_zero_of_coreMap_eq_zero
              m hm hsource hj0 hj1 hj2 hj3]
            simp
  rw [Finset.sum_congr rfl fun j _ => hpoint j, ← Finset.sum_mul]
  change CompactBirth.normSq x * y 0 = y 0
  rw [normSq_eq_one_of_coreMap_eq_zero m hm hx, one_mul]


-- @@ L570-575 verbatim
lemma target_denominator_pos {x : E} (hx : coreMap m hm 2 0 x = 0) :
    0 < (x 0 + 2) ^ 2 + x 1 ^ 2 := by
  have hu := target_u_eq_zero_of_coreMap_eq_zero m hm hx
  have hsource := target_coreMap_eq_source_of_eq_zero m hm hx
  have hn := CompactHopfPairConfiguration.first_branch_normSq m hm hsource hu
  nlinarith [sq_nonneg (x 0 + 1)]


-- @@ L577-604 verbatim
lemma fderiv_target_coreMap_targetPreimage {x : E}
    (hx : coreMap m hm 2 0 x = 0) (y : F) :
    fderiv ℝ (coreMap m hm 2 0) x (targetPreimage m hm x y) = y := by
  have hu := target_u_eq_zero_of_coreMap_eq_zero m hm hx
  have hden := target_denominator_pos m hm hx
  apply PiLp.ext
  intro i
  by_cases hi0 : i = 0
  · subst i
    rw [fderiv_target_coreMap_apply_zero, inner_targetPreimage m hm hx y]
  · by_cases hi1 : i = 1
    · subst i
      rw [fderiv_target_coreMap_apply_one]
      simp only [targetPreimage_apply_zero, targetPreimage_apply_one,
        targetPreimage_apply_two, targetPreimage_apply_three, hu.1, hu.2,
        mul_zero, zero_mul, zero_add]
      field_simp
      ring
    · by_cases hi2 : i = 2
      · subst i
        rw [fderiv_target_coreMap_apply_two]
        simp only [targetPreimage_apply_zero, targetPreimage_apply_one,
          targetPreimage_apply_two, targetPreimage_apply_three, hu.1, hu.2,
          mul_zero, zero_mul, zero_add, sub_zero]
        field_simp
        ring
      · rw [fderiv_target_coreMap_apply_tail m hm x _ hi0 hi1 hi2,
          targetPreimage_apply_tail m hm x y hi0 hi1 hi2]


-- @@ L606-611 verbatim
theorem surjective_fderiv_target_coreMap_of_eq_zero {x : E}
    (hx : coreMap m hm 2 0 x = 0) :
    Function.Surjective (fderiv ℝ (coreMap m hm 2 0) x) := by
  intro y
  exact ⟨targetPreimage m hm x y,
    fderiv_target_coreMap_targetPreimage m hm hx y⟩


-- @@ L613-620 verbatim
lemma levelMap_eventuallyEq_coreMap (a ε : ℝ) {x : E}
    (hx : CompactBirth.normSq x < 2) :
    levelMap m hm a ε =ᶠ[nhds x] coreMap m hm a ε := by
  have hopen : IsOpen {z : E | CompactBirth.normSq z < 2} :=
    isOpen_lt CompactBirth.contDiff_normSq.continuous continuous_const
  exact Filter.eventuallyEq_of_mem (hopen.mem_nhds hx) fun z hz => by
    rw [levelMap, CompactBirth.cutoff_eq_zero hz.le]
    simp


-- @@ L622-629 verbatim
theorem surjective_fderiv_target_levelMap_of_eq_zero {x : E}
    (hx : levelMap m hm 2 0 x = 0) :
    Function.Surjective (fderiv ℝ (levelMap m hm 2 0) x) := by
  have hxcore := (levelMap_eq_zero_iff_coreMap_eq_zero m hm 2 0 x).mp hx
  have hn := normSq_eq_one_of_coreMap_eq_zero m hm hxcore
  have hlt : CompactBirth.normSq x < 2 := by rw [hn]; norm_num
  rw [(levelMap_eventuallyEq_coreMap m hm 2 0 hlt).fderiv_eq]
  exact surjective_fderiv_target_coreMap_of_eq_zero m hm hxcore


-- @@ L631-645 verbatim
/-- The outgoing compact circle, packaged as a framed level set. -/
def targetFLS : FramedLevelSet (m + 2) where
  g := levelMap m hm 2 0
  smooth := contDiff_levelMap m hm 2 0
  fiber_bounded := by
    apply (Metric.isBounded_closedBall (x := (0 : E)) (r := 1)).subset
    intro x hx
    rw [mem_closedBall, dist_zero_right]
    have hxcore := (levelMap_eq_zero_iff_coreMap_eq_zero m hm 2 0 x).mp hx
    have hn := normSq_eq_one_of_coreMap_eq_zero m hm hxcore
    rw [CompactBirth.normSq_eq_norm_sq] at hn
    nlinarith [norm_nonneg x]
  regular := by
    intro x hx
    exact surjective_fderiv_target_levelMap_of_eq_zero m hm hx


-- @@ L647-647 verbatim
/-! ## Collar-flat time parameters -/


-- @@ L649-651 verbatim
/-- The coefficient moves from `0` to `2` and is literally `t + 1/2` on the
central time interval. -/
def shift (t : ℝ) : ℝ := StandardSaddle.height t + 1


-- @@ L653-656 verbatim
/-- A very small positive displacement during the middle of the event. -/
def epsilon (t : ℝ) : ℝ :=
  (1 / 1000 : ℝ) * StandardSaddle.leftCutoff t *
    (1 - StandardSaddle.rightCutoff t)


-- @@ L658-660 verbatim
omit hm in
lemma contDiff_shift : ContDiff ℝ ∞ shift :=
  StandardSaddle.contDiff_height.add contDiff_const


-- @@ L662-665 verbatim
omit hm in
lemma contDiff_epsilon : ContDiff ℝ ∞ epsilon := by
  exact (contDiff_const.mul StandardSaddle.contDiff_leftCutoff).mul
    (contDiff_const.sub StandardSaddle.contDiff_rightCutoff)


-- @@ L667-670 verbatim
omit hm in
lemma shift_of_le_quarter {t : ℝ} (ht : t ≤ 1 / 4) : shift t = 0 := by
  rw [shift, StandardSaddle.height_of_le_quarter ht]
  ring


-- @@ L672-675 verbatim
omit hm in
lemma shift_of_threeQuarter_le {t : ℝ} (ht : 3 / 4 ≤ t) : shift t = 2 := by
  rw [shift, StandardSaddle.height_of_threeQuarter_le ht]
  ring


-- @@ L677-683 verbatim
omit hm in
lemma epsilon_of_le_quarter {t : ℝ} (ht : t ≤ 1 / 4) : epsilon t = 0 := by
  have hleft : StandardSaddle.leftCutoff t = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    change 8 * (t - 1 / 4) ≤ 0
    linarith
  simp [epsilon, hleft]


-- @@ L685-691 verbatim
omit hm in
lemma epsilon_of_threeQuarter_le {t : ℝ} (ht : 3 / 4 ≤ t) : epsilon t = 0 := by
  have hright : StandardSaddle.rightCutoff t = 1 := by
    apply Real.smoothTransition.one_of_one_le
    change 1 ≤ 8 * (t - 5 / 8)
    linarith
  simp [epsilon, hright]


-- @@ L693-695 verbatim
omit hm in
@[simp] lemma shift_zero : shift 0 = 0 :=
  shift_of_le_quarter (by norm_num)


-- @@ L697-699 verbatim
omit hm in
@[simp] lemma shift_one : shift 1 = 2 :=
  shift_of_threeQuarter_le (by norm_num)


-- @@ L701-703 verbatim
omit hm in
@[simp] lemma epsilon_zero : epsilon 0 = 0 :=
  epsilon_of_le_quarter (by norm_num)


-- @@ L705-707 verbatim
omit hm in
@[simp] lemma epsilon_one : epsilon 1 = 0 :=
  epsilon_of_threeQuarter_le (by norm_num)


-- @@ L709-710 verbatim
/-- The compact spatial slice of the event. -/
def sliceMap (t : ℝ) : E → F := levelMap m hm (shift t) (epsilon t)


-- @@ L712-714 verbatim
lemma sliceMap_zero_eq_source :
    sliceMap m hm 0 = CompactHopfPairConfiguration.levelMap m hm := by
  simp [sliceMap, levelMap_zero_zero_eq_source]


-- @@ L716-720 verbatim
theorem sliceMap_zero_fiber (x : E) :
    sliceMap m hm 0 x = 0 ↔
      x ∈ standardCircle ∨
        x ∈ CompactHopfPairConfiguration.secondCircle m hm := by
  simpa [sliceMap] using source_levelMap_eq_zero_iff_two_circles m hm x


-- @@ L722-724 verbatim
theorem sliceMap_one_fiber (x : E) :
    sliceMap m hm 1 x = 0 ↔ x ∈ standardCircle := by
  simpa [sliceMap] using target_levelMap_eq_zero_iff_standardCircle m hm x


-- @@ L726-728 verbatim
theorem sliceMap_flatOutside (t : ℝ) {x : E} (hx : 2 ≤ ‖x‖) :
    sliceMap m hm t x = CompactHopfPairConfiguration.background m hm :=
  levelMap_flatOutside m hm (shift t) (epsilon t) hx


-- @@ L730-730 verbatim
/-! ## The compact space-time event -/


-- @@ L732-732 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (m + 4))


-- @@ L734-737 verbatim
/-- The compact pair-of-pants equation on space-time. -/
def eventMap (v : E') : F :=
  levelMap m hm (shift (vertC v)) (epsilon (vertC v))
    (initCLM (m + 3) v)


-- @@ L739-742 verbatim
/-- The polynomial space-time equation before spatial compactification. -/
def eventCoreMap (v : E') : F :=
  coreMap m hm (shift (vertC v)) (epsilon (vertC v))
    (initCLM (m + 3) v)


-- @@ L744-746 verbatim
lemma eventMap_spaceTime (x : E) (t : ℝ) :
    eventMap m hm (spaceTime x t) = sliceMap m hm t x := by
  simp [eventMap, sliceMap, initCLM_spaceTime, vertC_spaceTime]


-- @@ L748-785 verbatim
lemma contDiff_eventMap : ContDiff ℝ ∞ (eventMap m hm) := by
  let p : E' →L[ℝ] E := initCLM (m + 3)
  have hp : ContDiff ℝ ∞ p := p.contDiff
  have ht : ContDiff ℝ ∞ (fun v : E' => shift (vertC v)) :=
    contDiff_shift.comp contDiff_vertC
  have he : ContDiff ℝ ∞ (fun v : E' => epsilon (vertC v)) :=
    contDiff_epsilon.comp contDiff_vertC
  have hcore : ContDiff ℝ ∞ (fun v : E' =>
      coreMap m hm (shift (vertC v)) (epsilon (vertC v)) (p v)) := by
    rw [contDiff_piLp]
    intro i
    by_cases hi0 : i = 0
    · subst i
      simpa [coreMap_apply_zero, Function.comp_apply] using
        ((CompactBirth.contDiff_normSq.comp hp).sub contDiff_const).div_const 2
    · by_cases hi1 : i = 1
      · subst i
        have hhopf :=
          (CompactHopfPairConfiguration.contDiff_hopfRe m hm).comp hp
        have hcoord :=
          (EuclideanSpace.proj 2 : E →L[ℝ] ℝ).contDiff.comp hp
        simpa [coreMap_apply_one, pairRe, Function.comp_apply] using
          (hhopf.add (ht.mul hcoord)).sub he
      · by_cases hi2 : i = 2
        · subst i
          have hhopf :=
            (CompactHopfPairConfiguration.contDiff_hopfIm m hm).comp hp
          have hcoord :=
            (EuclideanSpace.proj 3 : E →L[ℝ] ℝ).contDiff.comp hp
          simpa [coreMap_apply_two, pairIm, Function.comp_apply] using
            hhopf.sub (ht.mul hcoord)
        · simp only [coreMap_apply_tail m hm _ _ _ hi0 hi1 hi2]
          exact (EuclideanSpace.proj i.succ : E →L[ℝ] ℝ).contDiff.comp hp
  have hcut : ContDiff ℝ ∞ (fun v : E' => CompactBirth.cutoff (p v)) :=
    CompactBirth.contDiff_cutoff.comp hp
  unfold eventMap levelMap
  exact ((contDiff_const.sub hcut).smul hcore).add
    (hcut.smul contDiff_const)


-- @@ L787-818 verbatim
lemma contDiff_eventCoreMap : ContDiff ℝ ∞ (eventCoreMap m hm) := by
  let p : E' →L[ℝ] E := initCLM (m + 3)
  have hp : ContDiff ℝ ∞ p := p.contDiff
  have ht : ContDiff ℝ ∞ (fun v : E' => shift (vertC v)) :=
    contDiff_shift.comp contDiff_vertC
  have he : ContDiff ℝ ∞ (fun v : E' => epsilon (vertC v)) :=
    contDiff_epsilon.comp contDiff_vertC
  unfold eventCoreMap
  rw [contDiff_piLp]
  intro i
  by_cases hi0 : i = 0
  · subst i
    simpa [coreMap_apply_zero, Function.comp_apply] using
      ((CompactBirth.contDiff_normSq.comp hp).sub contDiff_const).div_const 2
  · by_cases hi1 : i = 1
    · subst i
      have hhopf :=
        (CompactHopfPairConfiguration.contDiff_hopfRe m hm).comp hp
      have hcoord :=
        (EuclideanSpace.proj 2 : E →L[ℝ] ℝ).contDiff.comp hp
      simpa [coreMap_apply_one, pairRe, Function.comp_apply, p, initCLM_apply] using
        (hhopf.add (ht.mul hcoord)).sub he
    · by_cases hi2 : i = 2
      · subst i
        have hhopf :=
          (CompactHopfPairConfiguration.contDiff_hopfIm m hm).comp hp
        have hcoord :=
          (EuclideanSpace.proj 3 : E →L[ℝ] ℝ).contDiff.comp hp
        simpa [coreMap_apply_two, pairIm, Function.comp_apply, p, initCLM_apply] using
          hhopf.sub (ht.mul hcoord)
      · simp only [coreMap_apply_tail m hm _ _ _ hi0 hi1 hi2]
        exact (EuclideanSpace.proj i.succ : E →L[ℝ] ℝ).contDiff.comp hp


-- @@ L820-832 verbatim
omit hm in
private lemma fderiv_event_coord_apply
    (G : E' → F) (hG : ContDiff ℝ ∞ G)
    (i : Fin (m + 2)) (v h : E') :
    fderiv ℝ (fun q => G q i) v h = fderiv ℝ G v h i := by
  let outProj : F →L[ℝ] ℝ := EuclideanSpace.proj i
  have hG' : HasFDerivAt G (fderiv ℝ G v) v :=
    (hG.differentiable infty_ne_zero v).hasFDerivAt
  have hcomp : HasFDerivAt (fun q => G q i)
      (outProj.comp (fderiv ℝ G v)) v := by
    exact (PiLp.hasFDerivAt_apply 2 (G v) i).comp v hG'
  have happ := congrArg (fun L : E' →L[ℝ] ℝ => L h) hcomp.fderiv
  simpa [outProj] using happ


-- @@ L834-859 verbatim
lemma fderiv_eventCoreMap_apply_zero (v h : E') :
    fderiv ℝ (eventCoreMap m hm) v h 0 =
      ⟪initCLM (m + 3) v, initCLM (m + 3) h⟫_ℝ := by
  rw [← fderiv_event_coord_apply m (eventCoreMap m hm)
    (contDiff_eventCoreMap m hm) 0 v h]
  let p : E' →L[ℝ] E := initCLM (m + 3)
  have hfun : (fun q : E' => eventCoreMap m hm q 0) =
      fun q => CompactHopfPairConfiguration.coreMap m hm (p q) 0 := by
    funext q
    simp [eventCoreMap, p]
  rw [hfun]
  have hs : HasFDerivAt (CompactHopfPairConfiguration.coreMap m hm)
      (fderiv ℝ (CompactHopfPairConfiguration.coreMap m hm) (p v)) (p v) :=
    ((CompactHopfPairConfiguration.contDiff_coreMap m hm).differentiable
      infty_ne_zero (p v)).hasFDerivAt
  have hc := (PiLp.hasFDerivAt_apply 2
    (CompactHopfPairConfiguration.coreMap m hm (p v)) (0 : Fin (m + 2))).comp
      (p v) hs
  have hcomp := hc.comp v p.hasFDerivAt
  change (fderiv ℝ (((fun f : F => f 0) ∘
    CompactHopfPairConfiguration.coreMap m hm) ∘ p) v) h = _
  rw [hcomp.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  change fderiv ℝ (CompactHopfPairConfiguration.coreMap m hm)
    (p v) (p h) 0 = _
  rw [CompactHopfPairConfiguration.fderiv_coreMap_apply_zero]


-- @@ L861-901 verbatim
lemma fderiv_eventCoreMap_apply_one (v h : E') :
    fderiv ℝ (eventCoreMap m hm) v h 1 =
      h 0 * v 2 + (v 0 + shift (vertC v)) * h 2 +
        h 1 * v 3 + v 1 * h 3 +
        (deriv shift (vertC v) * v 2 - deriv epsilon (vertC v)) * vertC h := by
  rw [← fderiv_event_coord_apply m (eventCoreMap m hm)
    (contDiff_eventCoreMap m hm) 1 v h]
  let p0 : E' →L[ℝ] ℝ := EuclideanSpace.proj 0
  let p1 : E' →L[ℝ] ℝ := EuclideanSpace.proj 1
  let p2 : E' →L[ℝ] ℝ := EuclideanSpace.proj 2
  let p3 : E' →L[ℝ] ℝ := EuclideanSpace.proj 3
  let pT : E' →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last (m + 3))
  have h0 : HasFDerivAt (fun q : E' => q 0) p0 v := p0.hasFDerivAt
  have h1 : HasFDerivAt (fun q : E' => q 1) p1 v := p1.hasFDerivAt
  have h2 : HasFDerivAt (fun q : E' => q 2) p2 v := p2.hasFDerivAt
  have h3 : HasFDerivAt (fun q : E' => q 3) p3 v := p3.hasFDerivAt
  have ha0 : HasDerivAt shift (deriv shift (vertC v)) (vertC v) :=
    (contDiff_shift.differentiable infty_ne_zero (vertC v)).hasDerivAt
  have he0 : HasDerivAt epsilon (deriv epsilon (vertC v)) (vertC v) :=
    (contDiff_epsilon.differentiable infty_ne_zero (vertC v)).hasDerivAt
  have ha := ha0.hasFDerivAt.comp v pT.hasFDerivAt
  have he := he0.hasFDerivAt.comp v pT.hasFDerivAt
  have hd := (((h0.mul h2).add (h1.mul h3)).add (ha.mul h2)).sub he
  have h2cast : ((2 : Fin (m + 3)).castSucc : Fin (m + 4)) = 2 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3),
      Nat.mod_eq_of_lt (by omega : 2 < m + 4)]
  have h3cast : ((3 : Fin (m + 3)).castSucc : Fin (m + 4)) = 3 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3),
      Nat.mod_eq_of_lt (by omega : 3 < m + 4)]
  have hfun : (fun q : E' => eventCoreMap m hm q 1) = fun q =>
      q 0 * q 2 + q 1 * q 3 + shift (vertC q) * q 2 - epsilon (vertC q) := by
    funext q
    simp [eventCoreMap, pairRe, CompactHopfPairConfiguration.hopfRe,
      initCLM_apply, h2cast, h3cast]
  have hdEvent := hd.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun q => congrFun hfun q)
  rw [hdEvent.fderiv]
  simp [p0, p1, p2, p3, pT, Function.comp_apply, vertC]
  ring


-- @@ L903-940 verbatim
lemma fderiv_eventCoreMap_apply_two (v h : E') :
    fderiv ℝ (eventCoreMap m hm) v h 2 =
      h 1 * v 2 + v 1 * h 2 - h 0 * v 3 -
        (v 0 + shift (vertC v)) * h 3 -
        deriv shift (vertC v) * v 3 * vertC h := by
  rw [← fderiv_event_coord_apply m (eventCoreMap m hm)
    (contDiff_eventCoreMap m hm) 2 v h]
  let p0 : E' →L[ℝ] ℝ := EuclideanSpace.proj 0
  let p1 : E' →L[ℝ] ℝ := EuclideanSpace.proj 1
  let p2 : E' →L[ℝ] ℝ := EuclideanSpace.proj 2
  let p3 : E' →L[ℝ] ℝ := EuclideanSpace.proj 3
  let pT : E' →L[ℝ] ℝ := EuclideanSpace.proj (Fin.last (m + 3))
  have h0 : HasFDerivAt (fun q : E' => q 0) p0 v := p0.hasFDerivAt
  have h1 : HasFDerivAt (fun q : E' => q 1) p1 v := p1.hasFDerivAt
  have h2 : HasFDerivAt (fun q : E' => q 2) p2 v := p2.hasFDerivAt
  have h3 : HasFDerivAt (fun q : E' => q 3) p3 v := p3.hasFDerivAt
  have ha0 : HasDerivAt shift (deriv shift (vertC v)) (vertC v) :=
    (contDiff_shift.differentiable infty_ne_zero (vertC v)).hasDerivAt
  have ha := ha0.hasFDerivAt.comp v pT.hasFDerivAt
  have hd := ((h1.mul h2).sub (h0.mul h3)).sub (ha.mul h3)
  have h2cast : ((2 : Fin (m + 3)).castSucc : Fin (m + 4)) = 2 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3),
      Nat.mod_eq_of_lt (by omega : 2 < m + 4)]
  have h3cast : ((3 : Fin (m + 3)).castSucc : Fin (m + 4)) = 3 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3),
      Nat.mod_eq_of_lt (by omega : 3 < m + 4)]
  have hfun : (fun q : E' => eventCoreMap m hm q 2) = fun q =>
      q 1 * q 2 - q 0 * q 3 - shift (vertC q) * q 3 := by
    funext q
    simp [eventCoreMap, pairIm, CompactHopfPairConfiguration.hopfIm,
      initCLM_apply, h2cast, h3cast]
  have hdEvent := hd.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun q => congrFun hfun q)
  rw [hdEvent.fderiv]
  simp [p0, p1, p2, p3, pT, Function.comp_apply, vertC]
  ring


-- @@ L942-954 verbatim
lemma fderiv_eventCoreMap_apply_tail (v h : E') {i : Fin (m + 2)}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
    fderiv ℝ (eventCoreMap m hm) v h i = h i.succ.castSucc := by
  rw [← fderiv_event_coord_apply m (eventCoreMap m hm)
    (contDiff_eventCoreMap m hm) i v h]
  have hfun : (fun q : E' => eventCoreMap m hm q i) =
      fun q => q i.succ.castSucc := by
    funext q
    simp [eventCoreMap, coreMap_apply_tail m hm _ _ _ hi0 hi1 hi2,
      initCLM_apply]
  rw [hfun]
  exact congrArg (fun L : E' →L[ℝ] ℝ => L h)
    (EuclideanSpace.proj i.succ.castSucc : E' →L[ℝ] ℝ).hasFDerivAt.fderiv


-- @@ L956-956 verbatim
/-! ## Algebra controlling the unique spatially critical zone -/


-- @@ L958-961 verbatim
omit hm in
lemma shift_nonneg (t : ℝ) : 0 ≤ shift t := by
  unfold shift
  linarith [StandardSaddle.neg_one_le_height t]


-- @@ L963-966 verbatim
omit hm in
lemma shift_le_two (t : ℝ) : shift t ≤ 2 := by
  unfold shift
  linarith [StandardSaddle.height_le_one t]


-- @@ L968-974 verbatim
omit hm in
lemma epsilon_nonneg (t : ℝ) : 0 ≤ epsilon t := by
  have hL := Real.smoothTransition.nonneg (8 * (t - 1 / 4))
  have hR := Real.smoothTransition.le_one (8 * (t - 5 / 8))
  change 0 ≤ (1 / 1000 : ℝ) * StandardSaddle.leftCutoff t *
    (1 - StandardSaddle.rightCutoff t)
  positivity


-- @@ L976-995 verbatim
omit hm in
lemma epsilon_le_small (t : ℝ) : epsilon t ≤ 1 / 1000 := by
  have hL0 := Real.smoothTransition.nonneg (8 * (t - 1 / 4))
  have hL1 := Real.smoothTransition.le_one (8 * (t - 1 / 4))
  have hR0 := Real.smoothTransition.nonneg (8 * (t - 5 / 8))
  have hR1 := Real.smoothTransition.le_one (8 * (t - 5 / 8))
  change 0 ≤ StandardSaddle.leftCutoff t at hL0
  change StandardSaddle.leftCutoff t ≤ 1 at hL1
  change 0 ≤ StandardSaddle.rightCutoff t at hR0
  change StandardSaddle.rightCutoff t ≤ 1 at hR1
  change (1 / 1000 : ℝ) * StandardSaddle.leftCutoff t *
    (1 - StandardSaddle.rightCutoff t) ≤ 1 / 1000
  have hp : StandardSaddle.leftCutoff t *
      (1 - StandardSaddle.rightCutoff t) ≤ 1 := by
    have hB0 : 0 ≤ 1 - StandardSaddle.rightCutoff t := by linarith
    have hB1 : 1 - StandardSaddle.rightCutoff t ≤ 1 := by linarith
    calc
      _ ≤ 1 * 1 := mul_le_mul hL1 hB1 hB0 (by norm_num)
      _ = 1 := by norm_num
  nlinarith


-- @@ L997-1014 verbatim
omit hm in
lemma epsilon_eq_zero_time_dichotomy {t : ℝ} (he : epsilon t = 0) :
    t ≤ 1 / 4 ∨ 3 / 4 ≤ t := by
  have hprod : StandardSaddle.leftCutoff t *
      (1 - StandardSaddle.rightCutoff t) = 0 := by
    unfold epsilon at he
    norm_num at he ⊢
    exact he
  rcases mul_eq_zero.mp hprod with hL | hR
  · left
    have harg : 8 * (t - 1 / 4) ≤ 0 :=
      Real.smoothTransition.zero_iff_nonpos.mp hL
    linarith
  · right
    have hReq : StandardSaddle.rightCutoff t = 1 := by linarith
    have harg : 1 ≤ 8 * (t - 5 / 8) :=
      Real.smoothTransition.eq_one_iff_one_le.mp hReq
    linarith


-- @@ L1016-1037 verbatim
omit hm in
lemma shift_le_seven_eighth {t : ℝ} (ht : t ≤ 3 / 8) :
    shift t ≤ 7 / 8 := by
  by_cases hq : t ≤ 1 / 4
  · rw [shift_of_le_quarter hq]
    norm_num
  · have hh : t < 1 / 2 := by linarith
    rw [shift, StandardSaddle.height, if_pos hh, StandardSaddle.heightLeft]
    have hc0 := Real.smoothTransition.nonneg (8 * (t - 1 / 4))
    have hc1 := Real.smoothTransition.le_one (8 * (t - 1 / 4))
    change (1 - StandardSaddle.leftCutoff t) * (-1) +
        StandardSaddle.leftCutoff t * (t - 1 / 2) + 1 ≤ 7 / 8
    change 0 ≤ StandardSaddle.leftCutoff t at hc0
    change StandardSaddle.leftCutoff t ≤ 1 at hc1
    have hb0 : 0 ≤ t + 1 / 2 := by linarith
    have hb1 : t + 1 / 2 ≤ 7 / 8 := by linarith
    have hp : StandardSaddle.leftCutoff t * (t + 1 / 2) ≤ 7 / 8 := by
      calc
        _ ≤ 1 * (t + 1 / 2) :=
          mul_le_mul_of_nonneg_right hc1 hb0
        _ ≤ 7 / 8 := by linarith
    linarith


-- @@ L1039-1061 verbatim
omit hm in
lemma nine_eighth_le_shift {t : ℝ} (ht : 5 / 8 ≤ t) :
    9 / 8 ≤ shift t := by
  by_cases hq : 3 / 4 ≤ t
  · rw [shift_of_threeQuarter_le hq]
    norm_num
  · have hh : ¬ t < 1 / 2 := by linarith
    rw [shift, StandardSaddle.height, if_neg hh, StandardSaddle.heightRight]
    have hc0 := Real.smoothTransition.nonneg (8 * (t - 5 / 8))
    have hc1 := Real.smoothTransition.le_one (8 * (t - 5 / 8))
    change 0 ≤ StandardSaddle.rightCutoff t at hc0
    change StandardSaddle.rightCutoff t ≤ 1 at hc1
    change 9 / 8 ≤ (1 - StandardSaddle.rightCutoff t) *
        (t - 1 / 2) + StandardSaddle.rightCutoff t + 1
    have hb0 : 0 ≤ 3 / 2 - t := by linarith
    have hb1 : 3 / 2 - t ≤ 7 / 8 := by linarith
    have hp : (1 - StandardSaddle.rightCutoff t) * (3 / 2 - t) ≤ 7 / 8 := by
      have hc : 0 ≤ 1 - StandardSaddle.rightCutoff t := by linarith
      calc
        _ ≤ 1 * (3 / 2 - t) :=
          mul_le_mul_of_nonneg_right (by linarith) hb0
        _ ≤ 7 / 8 := by linarith
    nlinarith


-- @@ L1063-1069 verbatim
omit hm in
lemma epsilon_eq_small_of_middle {t : ℝ}
    (ht0 : 3 / 8 ≤ t) (ht1 : t ≤ 5 / 8) :
    epsilon t = 1 / 1000 := by
  rw [epsilon, StandardSaddle.leftCutoff_eq_one ht0,
    StandardSaddle.rightCutoff_eq_zero ht1]
  ring


-- @@ L1071-1080 verbatim
omit hm in
lemma hasDerivAt_shift_of_middle {t : ℝ}
    (ht0 : 3 / 8 < t) (ht1 : t < 5 / 8) : HasDerivAt shift 1 t := by
  have hlinear : shift =ᶠ[nhds t] fun s : ℝ => s + 1 / 2 :=
    Filter.eventuallyEq_of_mem
      (isOpen_Ioo.mem_nhds (show t ∈ Ioo (3 / 8 : ℝ) (5 / 8) from ⟨ht0, ht1⟩))
      fun s hs => by
        rw [shift, StandardSaddle.height_eq_linear hs.1.le hs.2.le]
        ring
  exact ((hasDerivAt_id t).add_const (1 / 2)).congr_of_eventuallyEq hlinear


-- @@ L1082-1088 verbatim
omit hm in
lemma hasDerivAt_epsilon_of_middle {t : ℝ}
    (ht0 : 3 / 8 < t) (ht1 : t < 5 / 8) : HasDerivAt epsilon 0 t := by
  apply (hasDerivAt_const t (1 / 1000 : ℝ)).congr_of_eventuallyEq
  exact Filter.eventuallyEq_of_mem
    (isOpen_Ioo.mem_nhds (show t ∈ Ioo (3 / 8 : ℝ) (5 / 8) from ⟨ht0, ht1⟩))
    fun s hs => epsilon_eq_small_of_middle hs.1.le hs.2.le


-- @@ L1090-1262 verbatim
set_option maxHeartbeats 800000 in
/-- Pure real-algebra checkpoint: for a small positive displacement, a
spatial critical point can only occur while the shift lies in `(7/8,9/8)`. -/
private lemma critical_shift_mem_middle
    {x y p q a e : ℝ}
    (ha0 : 0 ≤ a) (ha2 : a ≤ 2)
    (he0 : 0 < e) (he1 : e ≤ 1 / 1000)
    (hsphere : x ^ 2 + y ^ 2 + p ^ 2 + q ^ 2 = 1)
    (hre : (x + a) * p + y * q = e)
    (him : y * p - (x + a) * q = 0)
    (hrx : x * ((x + a) ^ 2 + y ^ 2) -
      (x + a) * (p ^ 2 + q ^ 2) = 0)
    (hry : y * (((x + a) ^ 2 + y ^ 2) - (p ^ 2 + q ^ 2)) = 0) :
    7 / 8 < a ∧ a < 9 / 8 := by
  let X : ℝ := x + a
  let W : ℝ := X ^ 2 + y ^ 2
  let U : ℝ := p ^ 2 + q ^ 2
  have hprod : W * U = e ^ 2 := by
    dsimp [W, U, X]
    nlinarith [sq_nonneg ((x + a) * p + y * q),
      sq_nonneg (y * p - (x + a) * q)]
  have hW0 : 0 ≤ W := by dsimp [W]; positivity
  have hU0 : 0 ≤ U := by dsimp [U]; positivity
  have hW : 0 < W := by
    by_contra hn
    have : W = 0 := le_antisymm (not_lt.mp hn) hW0
    rw [this, zero_mul] at hprod
    nlinarith
  have hU : 0 < U := by
    by_contra hn
    have : U = 0 := le_antisymm (not_lt.mp hn) hU0
    rw [this, mul_zero] at hprod
    nlinarith
  have hcriticalX : x * W - X * U = 0 := by simpa [W, U, X] using hrx
  have hcriticalY : y * (W - U) = 0 := by simpa [W, U, X] using hry
  have hWU : W ≠ U := by
    intro hEq
    have haW : a * W = 0 := by
      rw [hEq] at hcriticalX
      dsimp [X] at hcriticalX
      nlinarith
    have ha : a = 0 := (mul_eq_zero.mp haW).resolve_right hW.ne'
    have hEq0 : x ^ 2 + y ^ 2 = p ^ 2 + q ^ 2 := by
      simpa [W, U, X, ha] using hEq
    have hhalfW : W = 1 / 2 := by
      dsimp [W, X]
      rw [ha]
      nlinarith
    have hhalfU : U = 1 / 2 := by
      rw [← hEq]
      exact hhalfW
    have hehalf : e = 1 / 2 := by
      rw [hhalfW, hhalfU] at hprod
      nlinarith
    linarith
  have hy : y = 0 := (mul_eq_zero.mp hcriticalY).resolve_right (sub_ne_zero.mpr hWU)
  have hX : X ≠ 0 := by
    intro hX0
    dsimp [W] at hW
    rw [hX0, hy] at hW
    norm_num at hW
  have hq : q = 0 := by
    have hX' : x + a ≠ 0 := by simpa [X] using hX
    rw [hy] at him
    exact (mul_eq_zero.mp (by linarith : (x + a) * q = 0)).resolve_left hX'
  have hp2 : p ^ 2 = x * X := by
    have hfactor : X * (x * X - p ^ 2) = 0 := by
      dsimp [W, U] at hcriticalX
      rw [hy, hq] at hcriticalX
      linear_combination hcriticalX
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_left hX)).symm
  have hs : x ^ 2 + p ^ 2 = 1 := by rw [hy, hq] at hsphere; nlinarith
  have hpne : p ≠ 0 := by
    intro hp
    rw [hy, hq, hp] at hre
    norm_num at hre
    linarith
  have hxp : 0 < x * X := by rw [← hp2]; exact sq_pos_of_ne_zero hpne
  have hxne : x ≠ 0 := by
    intro hx
    rw [hx, zero_mul] at hxp
    exact lt_irrefl 0 hxp
  have hXsign : (0 < x ∧ 0 < X) ∨ (x < 0 ∧ X < 0) :=
    (mul_pos_iff.mp hxp)
  have heSq : e ^ 2 = X ^ 2 * p ^ 2 := by
    have hreX : X * p = e := by simpa [X, hy, hq] using hre
    nlinarith [sq_nonneg (X * p)]
  constructor
  · by_contra hnot
    have ha : a ≤ 7 / 8 := not_lt.mp hnot
    rcases hXsign with hpos | hneg
    · have hxX : x ≤ X := by dsimp [X]; linarith
      have hxx : x ^ 2 ≤ x * X := by
        simpa [pow_two] using mul_le_mul_of_nonneg_left hxX hpos.1.le
      have hhalf1 : 1 / 2 ≤ x * X := by nlinarith
      have hhalf2 : 1 / 2 ≤ X ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right hxX hpos.2.le
        exact hhalf1.trans (by simpa [pow_two] using hmul)
      have hquarter : 1 / 4 ≤ e ^ 2 := by
        rw [heSq, hp2]
        calc
          (1 / 4 : ℝ) = (1 / 2 : ℝ) * (1 / 2 : ℝ) := by norm_num
          _ ≤ X ^ 2 * (x * X) :=
            mul_le_mul hhalf2 hhalf1 (by norm_num) (sq_nonneg X)
      have hesmall : e ^ 2 ≤ (1 / 1000 : ℝ) ^ 2 :=
        by simpa [pow_two] using mul_self_le_mul_self he0.le he1
      norm_num at hquarter hesmall
      linarith
    · let r : ℝ := -X
      have hr : 0 < r := by dsimp [r]; linarith
      have hxform : -x = r + a := by dsimp [r, X]; ring
      have hpform : p ^ 2 = (r + a) * r := by
        rw [hp2]
        dsimp [r]
        nlinarith
      have hsform : (r + a) * (2 * r + a) = 1 := by
        rw [hpform] at hs
        nlinarith [sq_nonneg (r + a)]
      have hr16 : 1 / 16 < r := by
        by_contra hnr
        have hrle : r ≤ 1 / 16 := not_lt.mp hnr
        have h1 : r + a ≤ 15 / 16 := by linarith
        have h2 : 2 * r + a ≤ 1 := by linarith
        have hnon1 : 0 ≤ r + a := by linarith
        have hnon2 : 0 ≤ 2 * r + a := by linarith
        have hpbound : (r + a) * (2 * r + a) ≤ (15 / 16 : ℝ) * 1 :=
          mul_le_mul h1 h2 hnon2 (by norm_num)
        linarith
      have hpge : r ^ 2 ≤ p ^ 2 := by
        rw [hpform]
        nlinarith [mul_nonneg ha0 hr.le]
      have heform : e ^ 2 = r ^ 2 * p ^ 2 := by
        rw [heSq]
        dsimp [r]
        ring
      have hr2 : (1 / 16 : ℝ) ^ 2 < r ^ 2 := by nlinarith
      have heLower : (1 / 16 : ℝ) ^ 4 < e ^ 2 := by
        calc
          (1 / 16 : ℝ) ^ 4 =
              (1 / 16 : ℝ) ^ 2 * (1 / 16 : ℝ) ^ 2 := by ring
          _ < r ^ 2 * r ^ 2 :=
            mul_self_lt_mul_self (by norm_num) hr2
          _ ≤ r ^ 2 * p ^ 2 :=
            mul_le_mul_of_nonneg_left hpge (sq_nonneg r)
          _ = e ^ 2 := heform.symm
      have heUpper : e ^ 2 ≤ (1 / 1000 : ℝ) ^ 2 :=
        by simpa [pow_two] using mul_self_le_mul_self he0.le he1
      norm_num at heLower heUpper
      linarith
  · by_contra hnot
    have ha : 9 / 8 ≤ a := not_lt.mp hnot
    rcases hXsign with hpos | hneg
    · have hxX : x ≤ X := by dsimp [X]; linarith
      have hxx : x ^ 2 ≤ x * X := by
        simpa [pow_two] using mul_le_mul_of_nonneg_left hxX hpos.1.le
      have hhalf1 : 1 / 2 ≤ x * X := by nlinarith
      have hhalf2 : 1 / 2 ≤ X ^ 2 := by
        have hmul := mul_le_mul_of_nonneg_right hxX hpos.2.le
        exact hhalf1.trans (by simpa [pow_two] using hmul)
      have hquarter : 1 / 4 ≤ e ^ 2 := by
        rw [heSq, hp2]
        calc
          (1 / 4 : ℝ) = (1 / 2 : ℝ) * (1 / 2 : ℝ) := by norm_num
          _ ≤ X ^ 2 * (x * X) :=
            mul_le_mul hhalf2 hhalf1 (by norm_num) (sq_nonneg X)
      have hesmall : e ^ 2 ≤ (1 / 1000 : ℝ) ^ 2 :=
        by simpa [pow_two] using mul_self_le_mul_self he0.le he1
      norm_num at hquarter hesmall
      linarith
    · have hxlt : x < -1 := by
        dsimp [X] at hneg
        linarith
      nlinarith [sq_nonneg (x + 1)]


-- @@ L1264-1264 verbatim
/-! ## Explicit event right inverses -/


-- @@ L1266-1292 verbatim
lemma coordinate_eq_zero_of_coreMap_eq_zero {a e : ℝ} {x : E}
    (hx : coreMap m hm a e x = 0) {j : Fin (m + 3)}
    (hj0 : j ≠ 0) (hj1 : j ≠ 1) (hj2 : j ≠ 2) (hj3 : j ≠ 3) :
    x j = 0 := by
  let i : Fin (m + 2) := j.pred hj0
  have hji : i.succ = j := Fin.succ_pred j hj0
  have hi0 : i ≠ 0 := by
    intro hi
    apply hj1
    rw [← hji, hi]
    rfl
  have hi1 : i ≠ 1 := by
    intro hi
    apply hj2
    rw [← hji, hi]
    rfl
  have hi2 : i ≠ 2 := by
    intro hi
    apply hj3
    rw [← hji, hi]
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2),
      Nat.mod_eq_of_lt (by omega : 3 < m + 3)]
  have hout := congrArg (fun q : F => q i) hx
  rw [coreMap_apply_tail m hm a e x hi0 hi1 hi2] at hout
  simp only [PiLp.zero_apply] at hout
  rwa [hji] at hout


-- @@ L1294-1302 verbatim
/-- Assemble four distinguished spatial coordinates and lift all output tail
coordinates literally. -/
def eventSpatialLift (_hm : 0 < m)
    (c0 c1 c2 c3 : ℝ) (y : F) : E :=
  WithLp.toLp 2 <| Fin.cases c0 fun i =>
    if i = 0 then c1
    else if i = 1 then c2
    else if i = 2 then c3
    else y i


-- @@ L1304-1307 verbatim
@[simp] lemma eventSpatialLift_apply_zero
    (c0 c1 c2 c3 : ℝ) (y : F) :
    eventSpatialLift m hm c0 c1 c2 c3 y 0 = c0 := by
  simp [eventSpatialLift]


-- @@ L1309-1316 verbatim
@[simp] lemma eventSpatialLift_apply_succ
    (c0 c1 c2 c3 : ℝ) (y : F) (i : Fin (m + 2)) :
    eventSpatialLift m hm c0 c1 c2 c3 y i.succ =
      if i = 0 then c1
      else if i = 1 then c2
      else if i = 2 then c3
      else y i := by
  simp [eventSpatialLift]


-- @@ L1318-1329 verbatim
@[simp] lemma eventSpatialLift_apply_one
    (c0 c1 c2 c3 : ℝ) (y : F) :
    eventSpatialLift m hm c0 c1 c2 c3 y 1 = c1 := by
  have h1 : (1 : Fin (m + 3)) = (0 : Fin (m + 2)).succ := by
    apply Fin.ext
    simp
  calc
    _ = eventSpatialLift m hm c0 c1 c2 c3 y (0 : Fin (m + 2)).succ :=
      congrArg (fun j => eventSpatialLift m hm c0 c1 c2 c3 y j) h1
    _ = _ := by
      simpa using eventSpatialLift_apply_succ m hm c0 c1 c2 c3 y
        (0 : Fin (m + 2))


-- @@ L1331-1346 verbatim
@[simp] lemma eventSpatialLift_apply_two
    (c0 c1 c2 c3 : ℝ) (y : F) :
    eventSpatialLift m hm c0 c1 c2 c3 y 2 = c2 := by
  have h2 : (2 : Fin (m + 3)) = (1 : Fin (m + 2)).succ := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3)]
  have h10 : (1 : Fin (m + 2)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 1 < m + 2)] at hv
  calc
    _ = eventSpatialLift m hm c0 c1 c2 c3 y (1 : Fin (m + 2)).succ :=
      congrArg (fun j => eventSpatialLift m hm c0 c1 c2 c3 y j) h2
    _ = _ := by
      simpa [h10] using eventSpatialLift_apply_succ m hm c0 c1 c2 c3 y
        (1 : Fin (m + 2))


-- @@ L1348-1366 verbatim
@[simp] lemma eventSpatialLift_apply_three
    (c0 c1 c2 c3 : ℝ) (y : F) :
    eventSpatialLift m hm c0 c1 c2 c3 y 3 = c3 := by
  have h3 : (3 : Fin (m + 3)) = (2 : Fin (m + 2)).succ := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2),
      Nat.mod_eq_of_lt (by omega : 3 < m + 3)]
  have h20 : (2 : Fin (m + 2)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2)] at hv
  have h21 : (2 : Fin (m + 2)) ≠ 1 := by
    intro h
    have hv := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2)] at hv
  calc
    _ = eventSpatialLift m hm c0 c1 c2 c3 y (2 : Fin (m + 2)).succ :=
      congrArg (fun j => eventSpatialLift m hm c0 c1 c2 c3 y j) h3
    _ = _ := by simp [h20, h21]


-- @@ L1368-1372 verbatim
lemma eventSpatialLift_apply_tail
    (c0 c1 c2 c3 : ℝ) (y : F) {i : Fin (m + 2)}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
    eventSpatialLift m hm c0 c1 c2 c3 y i.succ = y i := by
  simp [eventSpatialLift, hi0, hi1, hi2]


-- @@ L1374-1429 verbatim
lemma inner_eventSpatialLift_of_coreMap_eq_zero
    {a e : ℝ} {x : E} (hx : coreMap m hm a e x = 0)
    (c0 c1 c2 c3 : ℝ) (y : F) :
    ⟪x, eventSpatialLift m hm c0 c1 c2 c3 y⟫_ℝ =
      x 0 * c0 + x 1 * c1 + x 2 * c2 + x 3 * c3 := by
  rw [inner_eq_sum_local]
  have hpoint : ∀ j : Fin (m + 3),
      x j * eventSpatialLift m hm c0 c1 c2 c3 y j =
        (if j = 0 then x 0 * c0 else 0) +
        (if j = 1 then x 1 * c1 else 0) +
        (if j = 2 then x 2 * c2 else 0) +
        (if j = 3 then x 3 * c3 else 0) := by
    intro j
    by_cases hj0 : j = 0
    · subst j
      have h02 : (0 : Fin (m + 3)) ≠ 2 := by
        intro h
        have hv := congrArg Fin.val h
        simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3)] at hv
      have h03 : (0 : Fin (m + 3)) ≠ 3 := by
        intro h
        have hv := congrArg Fin.val h
        simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at hv
      simp [h02, h03]
    · by_cases hj1 : j = 1
      · subst j
        have h12 : (1 : Fin (m + 3)) ≠ 2 := by
          intro h
          have hv := congrArg Fin.val h
          simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3)] at hv
        have h13 : (1 : Fin (m + 3)) ≠ 3 := by
          intro h
          have hv := congrArg Fin.val h
          simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at hv
        simp [hj0, h12, h13]
      · by_cases hj2 : j = 2
        · subst j
          have h23 : (2 : Fin (m + 3)) ≠ 3 := by
            intro h
            have hv := congrArg Fin.val h
            simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3),
              Nat.mod_eq_of_lt (by omega : 3 < m + 3)] at hv
          simp [hj0, hj1, h23]
        · by_cases hj3 : j = 3
          · subst j
            simp [hj0, hj1, hj2]
          · rw [coordinate_eq_zero_of_coreMap_eq_zero m hm hx
              hj0 hj1 hj2 hj3]
            simp [hj0, hj1, hj2, hj3]
  rw [Finset.sum_congr rfl fun j _ => hpoint j]
  simp only [Finset.sum_add_distrib,
    Finset.sum_ite_eq' _ (0 : Fin (m + 3)) (fun _ => x 0 * c0),
    Finset.sum_ite_eq' _ (1 : Fin (m + 3)) (fun _ => x 1 * c1),
    Finset.sum_ite_eq' _ (2 : Fin (m + 3)) (fun _ => x 2 * c2),
    Finset.sum_ite_eq' _ (3 : Fin (m + 3)) (fun _ => x 3 * c3),
    if_pos (Finset.mem_univ _)]


-- @@ L1431-1441 verbatim
lemma eventSpatialLift_spaceTime_apply_tail
    (c0 c1 c2 c3 s : ℝ) (y : F) {i : Fin (m + 2)}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
    spaceTime (eventSpatialLift m hm c0 c1 c2 c3 y) s
        i.succ.castSucc = y i := by
  calc
    _ = eventSpatialLift m hm c0 c1 c2 c3 y i.succ := by
      have h := congrArg (fun z : E => z i.succ)
        (initCLM_spaceTime (eventSpatialLift m hm c0 c1 c2 c3 y) s)
      simpa [initCLM_apply] using h
    _ = y i := eventSpatialLift_apply_tail m hm c0 c1 c2 c3 y hi0 hi1 hi2


-- @@ L1443-1448 verbatim
lemma spaceTime_eventSpatialLift_apply_zero
    (c0 c1 c2 c3 s : ℝ) (y : F) :
    spaceTime (eventSpatialLift m hm c0 c1 c2 c3 y) s 0 = c0 := by
  have h := congrArg (fun z : E => z 0)
    (initCLM_spaceTime (eventSpatialLift m hm c0 c1 c2 c3 y) s)
  simpa [initCLM_apply] using h


-- @@ L1450-1454 verbatim
omit hm in
lemma spaceTime_apply_spatial_zero (x : E) (s : ℝ) :
    spaceTime x s 0 = x 0 := by
  have h := congrArg (fun z : E => z 0) (initCLM_spaceTime x s)
  simpa [initCLM_apply] using h


-- @@ L1456-1460 verbatim
omit hm in
lemma spaceTime_apply_spatial_one (x : E) (s : ℝ) :
    spaceTime x s 1 = x 1 := by
  have h := congrArg (fun z : E => z 1) (initCLM_spaceTime x s)
  simpa [initCLM_apply] using h


-- @@ L1462-1470 verbatim
omit hm in
lemma spaceTime_apply_spatial_two (x : E) (s : ℝ) :
    spaceTime x s 2 = x 2 := by
  have h2cast : ((2 : Fin (m + 3)).castSucc : Fin (m + 4)) = 2 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3),
      Nat.mod_eq_of_lt (by omega : 2 < m + 4)]
  have h := congrArg (fun z : E => z 2) (initCLM_spaceTime x s)
  simpa [initCLM_apply, h2cast] using h


-- @@ L1472-1479 verbatim
lemma spaceTime_apply_spatial_three (x : E) (s : ℝ) :
    spaceTime x s 3 = x 3 := by
  have h3cast : ((3 : Fin (m + 3)).castSucc : Fin (m + 4)) = 3 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3),
      Nat.mod_eq_of_lt (by omega : 3 < m + 4)]
  have h := congrArg (fun z : E => z 3) (initCLM_spaceTime x s)
  simpa [initCLM_apply, h3cast] using h


-- @@ L1481-1486 verbatim
lemma spaceTime_eventSpatialLift_apply_one
    (c0 c1 c2 c3 s : ℝ) (y : F) :
    spaceTime (eventSpatialLift m hm c0 c1 c2 c3 y) s 1 = c1 := by
  have h := congrArg (fun z : E => z 1)
    (initCLM_spaceTime (eventSpatialLift m hm c0 c1 c2 c3 y) s)
  simpa [initCLM_apply] using h


-- @@ L1488-1497 verbatim
lemma spaceTime_eventSpatialLift_apply_two
    (c0 c1 c2 c3 s : ℝ) (y : F) :
    spaceTime (eventSpatialLift m hm c0 c1 c2 c3 y) s 2 = c2 := by
  have h2cast : ((2 : Fin (m + 3)).castSucc : Fin (m + 4)) = 2 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3),
      Nat.mod_eq_of_lt (by omega : 2 < m + 4)]
  have h := congrArg (fun z : E => z 2)
    (initCLM_spaceTime (eventSpatialLift m hm c0 c1 c2 c3 y) s)
  simpa [initCLM_apply, h2cast] using h


-- @@ L1499-1508 verbatim
lemma spaceTime_eventSpatialLift_apply_three
    (c0 c1 c2 c3 s : ℝ) (y : F) :
    spaceTime (eventSpatialLift m hm c0 c1 c2 c3 y) s 3 = c3 := by
  have h3cast : ((3 : Fin (m + 3)).castSucc : Fin (m + 4)) = 3 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3),
      Nat.mod_eq_of_lt (by omega : 3 < m + 4)]
  have h := congrArg (fun z : E => z 3)
    (initCLM_spaceTime (eventSpatialLift m hm c0 c1 c2 c3 y) s)
  simpa [initCLM_apply, h3cast] using h


-- @@ L1510-1562 verbatim
lemma first_four_sq_eq_one_of_coreMap_eq_zero
    {a e : ℝ} {x : E} (hx : coreMap m hm a e x = 0) :
    x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 = 1 := by
  let z : F := 0
  let w : E := eventSpatialLift m hm (x 0) (x 1) (x 2) (x 3) z
  have hw : w = x := by
    apply PiLp.ext
    intro j
    by_cases hj0 : j = 0
    · subst j
      simp [w]
    · by_cases hj1 : j = 1
      · subst j
        simp [w]
      · by_cases hj2 : j = 2
        · subst j
          simp [w]
        · by_cases hj3 : j = 3
          · subst j
            simp [w]
          · let i : Fin (m + 2) := j.pred hj0
            have hji : i.succ = j := Fin.succ_pred j hj0
            have hi0 : i ≠ 0 := by
              intro hi
              apply hj1
              rw [← hji, hi]
              rfl
            have hi1 : i ≠ 1 := by
              intro hi
              apply hj2
              rw [← hji, hi]
              rfl
            have hi2 : i ≠ 2 := by
              intro hi
              apply hj3
              rw [← hji, hi]
              apply Fin.ext
              simp [Nat.mod_eq_of_lt (by omega : 2 < m + 2),
                Nat.mod_eq_of_lt (by omega : 3 < m + 3)]
            have hxi : x i.succ = 0 := by
              rw [hji]
              exact coordinate_eq_zero_of_coreMap_eq_zero m hm hx
                hj0 hj1 hj2 hj3
            rw [← hji, eventSpatialLift_apply_tail m hm _ _ _ _ z hi0 hi1 hi2]
            simp [z, hxi]
  have hinner := inner_eventSpatialLift_of_coreMap_eq_zero m hm hx
    (x 0) (x 1) (x 2) (x 3) z
  change ⟪x, w⟫_ℝ =
    x 0 * x 0 + x 1 * x 1 + x 2 * x 2 + x 3 * x 3 at hinner
  rw [hw, real_inner_self_eq_norm_sq,
    ← CompactBirth.normSq_eq_norm_sq,
    normSq_eq_one_of_coreMap_eq_zero m hm hx] at hinner
  nlinarith


-- @@ L1564-1579 verbatim
lemma eventCoreMap_zero_sphere {v : E'}
    (hv : eventCoreMap m hm v = 0) :
    v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + v 3 ^ 2 = 1 := by
  have h2cast : ((2 : Fin (m + 3)).castSucc : Fin (m + 4)) = 2 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3),
      Nat.mod_eq_of_lt (by omega : 2 < m + 4)]
  have h3cast : ((3 : Fin (m + 3)).castSucc : Fin (m + 4)) = 3 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3),
      Nat.mod_eq_of_lt (by omega : 3 < m + 4)]
  have hcore : coreMap m hm (shift (vertC v)) (epsilon (vertC v))
      (initCLM (m + 3) v) = 0 := by
    simpa [eventCoreMap] using hv
  have hfour := first_four_sq_eq_one_of_coreMap_eq_zero m hm hcore
  simpa [initCLM_apply, h2cast, h3cast] using hfour


-- @@ L1581-1597 verbatim
lemma eventCoreMap_zero_pairRe {v : E'}
    (hv : eventCoreMap m hm v = 0) :
    (v 0 + shift (vertC v)) * v 2 + v 1 * v 3 =
      epsilon (vertC v) := by
  have h := congrArg (fun q : F => q 1) hv
  simp only [eventCoreMap, coreMap_apply_one, pairRe,
    CompactHopfPairConfiguration.hopfRe, PiLp.zero_apply] at h
  have h2cast : ((2 : Fin (m + 3)).castSucc : Fin (m + 4)) = 2 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3),
      Nat.mod_eq_of_lt (by omega : 2 < m + 4)]
  have h3cast : ((3 : Fin (m + 3)).castSucc : Fin (m + 4)) = 3 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3),
      Nat.mod_eq_of_lt (by omega : 3 < m + 4)]
  simp [initCLM_apply, h2cast, h3cast] at h
  nlinarith


-- @@ L1599-1614 verbatim
lemma eventCoreMap_zero_pairIm {v : E'}
    (hv : eventCoreMap m hm v = 0) :
    v 1 * v 2 - (v 0 + shift (vertC v)) * v 3 = 0 := by
  have h := congrArg (fun q : F => q 2) hv
  simp only [eventCoreMap, coreMap_apply_two, pairIm,
    CompactHopfPairConfiguration.hopfIm, PiLp.zero_apply] at h
  have h2cast : ((2 : Fin (m + 3)).castSucc : Fin (m + 4)) = 2 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3),
      Nat.mod_eq_of_lt (by omega : 2 < m + 4)]
  have h3cast : ((3 : Fin (m + 3)).castSucc : Fin (m + 4)) = 3 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3),
      Nat.mod_eq_of_lt (by omega : 3 < m + 4)]
  simp [initCLM_apply, h2cast, h3cast] at h
  nlinarith


-- @@ L1616-1635 verbatim
lemma fderiv_eventCoreMap_eventSpatialLift_apply_zero
    {v : E'} (hv : eventCoreMap m hm v = 0)
    (c0 c1 c2 c3 s : ℝ) (y : F) :
    fderiv ℝ (eventCoreMap m hm) v
        (spaceTime (eventSpatialLift m hm c0 c1 c2 c3 y) s) 0 =
      v 0 * c0 + v 1 * c1 + v 2 * c2 + v 3 * c3 := by
  have h2cast : ((2 : Fin (m + 3)).castSucc : Fin (m + 4)) = 2 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3),
      Nat.mod_eq_of_lt (by omega : 2 < m + 4)]
  have h3cast : ((3 : Fin (m + 3)).castSucc : Fin (m + 4)) = 3 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3),
      Nat.mod_eq_of_lt (by omega : 3 < m + 4)]
  have hcore : coreMap m hm (shift (vertC v)) (epsilon (vertC v))
      (initCLM (m + 3) v) = 0 := by
    simpa [eventCoreMap] using hv
  rw [fderiv_eventCoreMap_apply_zero, initCLM_spaceTime,
    inner_eventSpatialLift_of_coreMap_eq_zero m hm hcore]
  simp [initCLM_apply, h2cast, h3cast]


-- @@ L1637-1649 verbatim
lemma fderiv_eventCoreMap_eventSpatialLift_apply_one
    {v : E'} (c0 c1 c2 c3 s : ℝ) (y : F) :
    fderiv ℝ (eventCoreMap m hm) v
        (spaceTime (eventSpatialLift m hm c0 c1 c2 c3 y) s) 1 =
      c0 * v 2 + (v 0 + shift (vertC v)) * c2 +
        c1 * v 3 + v 1 * c3 +
        (deriv shift (vertC v) * v 2 - deriv epsilon (vertC v)) * s := by
  rw [fderiv_eventCoreMap_apply_one,
    spaceTime_eventSpatialLift_apply_zero,
    spaceTime_eventSpatialLift_apply_one,
    spaceTime_eventSpatialLift_apply_two,
    spaceTime_eventSpatialLift_apply_three,
    vertC_spaceTime]


-- @@ L1651-1663 verbatim
lemma fderiv_eventCoreMap_eventSpatialLift_apply_two
    {v : E'} (c0 c1 c2 c3 s : ℝ) (y : F) :
    fderiv ℝ (eventCoreMap m hm) v
        (spaceTime (eventSpatialLift m hm c0 c1 c2 c3 y) s) 2 =
      c1 * v 2 + v 1 * c2 - c0 * v 3 -
        (v 0 + shift (vertC v)) * c3 -
        deriv shift (vertC v) * v 3 * s := by
  rw [fderiv_eventCoreMap_apply_two,
    spaceTime_eventSpatialLift_apply_zero,
    spaceTime_eventSpatialLift_apply_one,
    spaceTime_eventSpatialLift_apply_two,
    spaceTime_eventSpatialLift_apply_three,
    vertC_spaceTime]


-- @@ L1665-1671 verbatim
lemma fderiv_eventCoreMap_eventSpatialLift_apply_tail
    {v : E'} (c0 c1 c2 c3 s : ℝ) (y : F) {i : Fin (m + 2)}
    (hi0 : i ≠ 0) (hi1 : i ≠ 1) (hi2 : i ≠ 2) :
    fderiv ℝ (eventCoreMap m hm) v
        (spaceTime (eventSpatialLift m hm c0 c1 c2 c3 y) s) i = y i := by
  rw [fderiv_eventCoreMap_apply_tail m hm v _ hi0 hi1 hi2,
    eventSpatialLift_spaceTime_apply_tail m hm c0 c1 c2 c3 s y hi0 hi1 hi2]


-- @@ L1673-1713 verbatim
lemma fderiv_eventCoreMap_spaceTime_zero_eq_source
    (v : E') (h : E) (ha : shift (vertC v) = 0) :
    fderiv ℝ (eventCoreMap m hm) v (spaceTime h 0) =
      fderiv ℝ (CompactHopfPairConfiguration.coreMap m hm)
        (initCLM (m + 3) v) h := by
  have h2cast : ((2 : Fin (m + 3)).castSucc : Fin (m + 4)) = 2 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3),
      Nat.mod_eq_of_lt (by omega : 2 < m + 4)]
  have h3cast : ((3 : Fin (m + 3)).castSucc : Fin (m + 4)) = 3 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3),
      Nat.mod_eq_of_lt (by omega : 3 < m + 4)]
  apply PiLp.ext
  intro i
  by_cases hi0 : i = 0
  · subst i
    rw [fderiv_eventCoreMap_apply_zero,
      CompactHopfPairConfiguration.fderiv_coreMap_apply_zero,
      initCLM_spaceTime]
  · by_cases hi1 : i = 1
    · subst i
      rw [fderiv_eventCoreMap_apply_one,
        CompactHopfPairConfiguration.fderiv_coreMap_apply_one,
        spaceTime_apply_spatial_zero, spaceTime_apply_spatial_one,
        spaceTime_apply_spatial_two, spaceTime_apply_spatial_three m hm,
        vertC_spaceTime, ha]
      simp [initCLM_apply, h2cast, h3cast]
    · by_cases hi2 : i = 2
      · subst i
        rw [fderiv_eventCoreMap_apply_two,
          CompactHopfPairConfiguration.fderiv_coreMap_apply_two,
          spaceTime_apply_spatial_zero, spaceTime_apply_spatial_one,
          spaceTime_apply_spatial_two, spaceTime_apply_spatial_three m hm,
          vertC_spaceTime, ha]
        simp [initCLM_apply, h2cast, h3cast]
      · rw [fderiv_eventCoreMap_apply_tail m hm v _ hi0 hi1 hi2,
          CompactHopfPairConfiguration.fderiv_coreMap_apply_tail
            m hm (initCLM (m + 3) v) h hi0 hi1 hi2]
        have hcoord := congrArg (fun z : E => z i.succ) (initCLM_spaceTime h 0)
        simpa [initCLM_apply] using hcoord


-- @@ L1715-1753 verbatim
lemma fderiv_eventCoreMap_spaceTime_zero_eq_target
    (v : E') (h : E) (ha : shift (vertC v) = 2) :
    fderiv ℝ (eventCoreMap m hm) v (spaceTime h 0) =
      fderiv ℝ (coreMap m hm 2 0) (initCLM (m + 3) v) h := by
  have h2cast : ((2 : Fin (m + 3)).castSucc : Fin (m + 4)) = 2 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 2 < m + 3),
      Nat.mod_eq_of_lt (by omega : 2 < m + 4)]
  have h3cast : ((3 : Fin (m + 3)).castSucc : Fin (m + 4)) = 3 := by
    apply Fin.ext
    simp [Nat.mod_eq_of_lt (by omega : 3 < m + 3),
      Nat.mod_eq_of_lt (by omega : 3 < m + 4)]
  apply PiLp.ext
  intro i
  by_cases hi0 : i = 0
  · subst i
    rw [fderiv_eventCoreMap_apply_zero,
      fderiv_target_coreMap_apply_zero, initCLM_spaceTime]
  · by_cases hi1 : i = 1
    · subst i
      rw [fderiv_eventCoreMap_apply_one,
        fderiv_target_coreMap_apply_one,
        spaceTime_apply_spatial_zero, spaceTime_apply_spatial_one,
        spaceTime_apply_spatial_two, spaceTime_apply_spatial_three m hm,
        vertC_spaceTime, ha]
      simp [initCLM_apply, h2cast, h3cast]
    · by_cases hi2 : i = 2
      · subst i
        rw [fderiv_eventCoreMap_apply_two,
          fderiv_target_coreMap_apply_two,
          spaceTime_apply_spatial_zero, spaceTime_apply_spatial_one,
          spaceTime_apply_spatial_two, spaceTime_apply_spatial_three m hm,
          vertC_spaceTime, ha]
        simp [initCLM_apply, h2cast, h3cast]
      · rw [fderiv_eventCoreMap_apply_tail m hm v _ hi0 hi1 hi2,
          fderiv_target_coreMap_apply_tail m hm (initCLM (m + 3) v) h
            hi0 hi1 hi2]
        have hcoord := congrArg (fun z : E => z i.succ) (initCLM_spaceTime h 0)
        simpa [initCLM_apply] using hcoord


-- @@ L1755-1783 verbatim
lemma surjective_fderiv_eventCoreMap_of_epsilon_eq_zero
    {v : E'} (hv : eventCoreMap m hm v = 0)
    (he : epsilon (vertC v) = 0) :
    Function.Surjective (fderiv ℝ (eventCoreMap m hm) v) := by
  have hcore : coreMap m hm (shift (vertC v)) (epsilon (vertC v))
      (initCLM (m + 3) v) = 0 := by
    simpa [eventCoreMap] using hv
  rcases epsilon_eq_zero_time_dichotomy he with ht | ht
  · have ha : shift (vertC v) = 0 := shift_of_le_quarter ht
    have hsource : CompactHopfPairConfiguration.coreMap m hm
        (initCLM (m + 3) v) = 0 := by
      rw [← coreMap_zero_zero_eq_source m hm]
      simpa [ha, he] using hcore
    intro y
    obtain ⟨h, hh⟩ :=
      CompactHopfPairConfiguration.surjective_fderiv_coreMap_of_eq_zero
        m hm hsource y
    refine ⟨spaceTime h 0, ?_⟩
    rw [fderiv_eventCoreMap_spaceTime_zero_eq_source m hm v h ha]
    exact hh
  · have ha : shift (vertC v) = 2 := shift_of_threeQuarter_le ht
    have htarget : coreMap m hm 2 0 (initCLM (m + 3) v) = 0 := by
      simpa [ha, he] using hcore
    intro y
    obtain ⟨h, hh⟩ :=
      surjective_fderiv_target_coreMap_of_eq_zero m hm htarget y
    refine ⟨spaceTime h 0, ?_⟩
    rw [fderiv_eventCoreMap_spaceTime_zero_eq_target m hm v h ha]
    exact hh


-- @@ L1785-2070 verbatim
set_option maxHeartbeats 800000 in
lemma surjective_fderiv_eventCoreMap_of_epsilon_pos
    {v : E'} (hv : eventCoreMap m hm v = 0)
    (he : 0 < epsilon (vertC v)) :
    Function.Surjective (fderiv ℝ (eventCoreMap m hm) v) := by
  let X : ℝ := v 0 + shift (vertC v)
  let W : ℝ := X ^ 2 + v 1 ^ 2
  let U : ℝ := v 2 ^ 2 + v 3 ^ 2
  let S : ℝ := W + U
  let RX : ℝ := v 0 * W - X * U
  let RY : ℝ := v 1 * (W - U)
  have hsphere := eventCoreMap_zero_sphere m hm hv
  have hre := eventCoreMap_zero_pairRe m hm hv
  have him := eventCoreMap_zero_pairIm m hm hv
  have hSnonneg : 0 ≤ S := by
    dsimp [S, W, U]
    positivity
  have hS : S ≠ 0 := by
    intro hS0
    have hXsq : X ^ 2 = 0 := by
      dsimp [S, W, U] at hS0
      nlinarith [sq_nonneg X, sq_nonneg (v 1),
        sq_nonneg (v 2), sq_nonneg (v 3)]
    have hysq : v 1 ^ 2 = 0 := by
      dsimp [S, W, U] at hS0
      nlinarith [sq_nonneg X, sq_nonneg (v 1),
        sq_nonneg (v 2), sq_nonneg (v 3)]
    have hX0 : X = 0 := sq_eq_zero_iff.mp hXsq
    have hy0 : v 1 = 0 := sq_eq_zero_iff.mp hysq
    change X * v 2 + v 1 * v 3 = epsilon (vertC v) at hre
    rw [hX0, hy0] at hre
    norm_num at hre
    linarith
  have hSpos : 0 < S := lt_of_le_of_ne hSnonneg (Ne.symm hS)
  intro y
  let A : ℝ := y 1 / S
  let B : ℝ := y 2 / S
  let b0 : ℝ := A * v 2 - B * v 3
  let b1 : ℝ := A * v 3 + B * v 2
  let b2 : ℝ := A * X + B * v 1
  let b3 : ℝ := A * v 1 - B * X
  let rbase : ℝ := v 0 * b0 + v 1 * b1 + v 2 * b2 + v 3 * b3
  have hAS : A * S = y 1 := by
    dsimp [A]
    field_simp [hS]
  have hBS : B * S = y 2 := by
    dsimp [B]
    field_simp [hS]
  have hbase1 :
      b0 * v 2 + X * b2 + b1 * v 3 + v 1 * b3 = y 1 := by
    calc
      _ = A * S := by
        dsimp [b0, b1, b2, b3, S, W, U]
        ring
      _ = y 1 := hAS
  have hbase2 :
      b1 * v 2 + v 1 * b2 - b0 * v 3 - X * b3 = y 2 := by
    calc
      _ = B * S := by
        dsimp [b0, b1, b2, b3, S, W, U]
        ring
      _ = y 2 := hBS
  by_cases hRX : RX ≠ 0
  · let c : ℝ := (y 0 - rbase) / RX
    let k2 : ℝ := -X * v 2 + v 1 * v 3
    let k3 : ℝ := -v 1 * v 2 - X * v 3
    have hk0 : v 0 * W + v 2 * k2 + v 3 * k3 = RX := by
      dsimp [k2, k3, RX, W, U, X]
      ring
    have hk1 : W * v 2 + X * k2 + v 1 * k3 = 0 := by
      dsimp [k2, k3, W]
      ring
    have hk2 : v 1 * k2 - W * v 3 - X * k3 = 0 := by
      dsimp [k2, k3, W]
      ring
    refine ⟨spaceTime
      (eventSpatialLift m hm (b0 + c * W) b1
        (b2 + c * k2) (b3 + c * k3) y) 0, ?_⟩
    apply PiLp.ext
    intro i
    by_cases hi0 : i = 0
    · subst i
      rw [fderiv_eventCoreMap_eventSpatialLift_apply_zero m hm hv]
      calc
        _ = rbase + c * RX := by
          rw [← hk0]
          dsimp [rbase]
          ring
        _ = y 0 := by
          dsimp [c]
          field_simp [hRX]
          ring
    · by_cases hi1 : i = 1
      · subst i
        rw [fderiv_eventCoreMap_eventSpatialLift_apply_one]
        simp only [mul_zero, add_zero]
        calc
          _ = (b0 * v 2 + X * b2 + b1 * v 3 + v 1 * b3) +
              c * (W * v 2 + X * k2 + v 1 * k3) := by
            ring
          _ = y 1 := by rw [hbase1, hk1]; ring
      · by_cases hi2 : i = 2
        · subst i
          rw [fderiv_eventCoreMap_eventSpatialLift_apply_two]
          simp only [mul_zero, sub_zero]
          calc
            _ = (b1 * v 2 + v 1 * b2 - b0 * v 3 - X * b3) +
                c * (v 1 * k2 - W * v 3 - X * k3) := by
              ring
            _ = y 2 := by rw [hbase2, hk2]; ring
        · rw [fderiv_eventCoreMap_eventSpatialLift_apply_tail
            m hm _ _ _ _ _ y hi0 hi1 hi2]
  · have hRX0 : RX = 0 := not_ne_iff.mp hRX
    by_cases hRY : RY ≠ 0
    · let c : ℝ := (y 0 - rbase) / RY
      let k2 : ℝ := -X * v 3 - v 1 * v 2
      let k3 : ℝ := -v 1 * v 3 + X * v 2
      have hk0 : v 1 * W + v 2 * k2 + v 3 * k3 = RY := by
        dsimp [k2, k3, RY, W, U]
        ring
      have hk1 : X * k2 + W * v 3 + v 1 * k3 = 0 := by
        dsimp [k2, k3, W]
        ring
      have hk2 : W * v 2 + v 1 * k2 - X * k3 = 0 := by
        dsimp [k2, k3, W]
        ring
      refine ⟨spaceTime
        (eventSpatialLift m hm b0 (b1 + c * W)
          (b2 + c * k2) (b3 + c * k3) y) 0, ?_⟩
      apply PiLp.ext
      intro i
      by_cases hi0 : i = 0
      · subst i
        rw [fderiv_eventCoreMap_eventSpatialLift_apply_zero m hm hv]
        calc
          _ = rbase + c * RY := by
            rw [← hk0]
            dsimp [rbase]
            ring
          _ = y 0 := by
            dsimp [c]
            field_simp [hRY]
            ring
      · by_cases hi1 : i = 1
        · subst i
          rw [fderiv_eventCoreMap_eventSpatialLift_apply_one]
          simp only [mul_zero, add_zero]
          calc
            _ = (b0 * v 2 + X * b2 + b1 * v 3 + v 1 * b3) +
                c * (X * k2 + W * v 3 + v 1 * k3) := by
              ring
            _ = y 1 := by rw [hbase1, hk1]; ring
        · by_cases hi2 : i = 2
          · subst i
            rw [fderiv_eventCoreMap_eventSpatialLift_apply_two]
            simp only [mul_zero, sub_zero]
            calc
              _ = (b1 * v 2 + v 1 * b2 - b0 * v 3 - X * b3) +
                  c * (W * v 2 + v 1 * k2 - X * k3) := by
                ring
              _ = y 2 := by rw [hbase2, hk2]; ring
          · rw [fderiv_eventCoreMap_eventSpatialLift_apply_tail
              m hm _ _ _ _ _ y hi0 hi1 hi2]
    · have hRY0 : RY = 0 := not_ne_iff.mp hRY
      have hcrit := critical_shift_mem_middle (m := m) (hm := hm)
        (x := v 0) (y := v 1) (p := v 2) (q := v 3)
        (a := shift (vertC v)) (e := epsilon (vertC v))
        (shift_nonneg (vertC v)) (shift_le_two (vertC v)) he
        (epsilon_le_small (vertC v)) hsphere hre him
        (by simpa [RX, W, U, X] using hRX0)
        (by simpa [RY, W, U, X] using hRY0)
      have ht0 : 3 / 8 < vertC v := by
        by_contra hnot
        have hle : vertC v ≤ 3 / 8 := not_lt.mp hnot
        linarith [shift_le_seven_eighth hle]
      have ht1 : vertC v < 5 / 8 := by
        by_contra hnot
        have hle : 5 / 8 ≤ vertC v := not_lt.mp hnot
        linarith [nine_eighth_le_shift hle]
      have hda : deriv shift (vertC v) = 1 :=
        (hasDerivAt_shift_of_middle ht0 ht1).deriv
      have hde : deriv epsilon (vertC v) = 0 :=
        (hasDerivAt_epsilon_of_middle ht0 ht1).deriv
      have hWnonneg : 0 ≤ W := by
        dsimp [W]
        positivity
      have hWpos : 0 < W := by
        by_contra hnot
        have hW0 : W = 0 := le_antisymm (not_lt.mp hnot) hWnonneg
        have hXsq : X ^ 2 = 0 := by
          dsimp [W] at hW0
          nlinarith [sq_nonneg X, sq_nonneg (v 1)]
        have hysq : v 1 ^ 2 = 0 := by
          dsimp [W] at hW0
          nlinarith [sq_nonneg X, sq_nonneg (v 1)]
        have hX0 : X = 0 := sq_eq_zero_iff.mp hXsq
        have hy0 : v 1 = 0 := sq_eq_zero_iff.mp hysq
        change X * v 2 + v 1 * v 3 = epsilon (vertC v) at hre
        rw [hX0, hy0] at hre
        norm_num at hre
        linarith
      have hWU : W ≠ U := by
        intro hEq
        have hRX' := hRX0
        dsimp [RX, X] at hRX'
        rw [← hEq] at hRX'
        have haW : shift (vertC v) * W = 0 := by nlinarith
        exact (mul_ne_zero (by linarith [hcrit.1]) hWpos.ne') haW
      have hy0 : v 1 = 0 := by
        have hRY' := hRY0
        dsimp [RY] at hRY'
        exact (mul_eq_zero.mp hRY').resolve_right (sub_ne_zero.mpr hWU)
      have hX : X ≠ 0 := by
        intro hX0
        have hW' := hWpos
        dsimp [W] at hW'
        rw [hX0, hy0] at hW'
        norm_num at hW'
      have hq0 : v 3 = 0 := by
        have him' := him
        change v 1 * v 2 - X * v 3 = 0 at him'
        rw [hy0] at him'
        have hXq : X * v 3 = 0 := by nlinarith
        exact (mul_eq_zero.mp hXq).resolve_left hX
      have hXp : X * v 2 = epsilon (vertC v) := by
        have hre' := hre
        change X * v 2 + v 1 * v 3 = epsilon (vertC v) at hre'
        simpa [hy0, hq0] using hre'
      have hp : v 2 ≠ 0 := by
        intro hp0
        rw [hp0, mul_zero] at hXp
        linarith
      let k2 : ℝ := -X * v 2 + v 1 * v 3
      let k3 : ℝ := -v 1 * v 2 - X * v 3
      let RT : ℝ := v 2 * k2 + v 3 * k3
      have hRTform : RT = -epsilon (vertC v) * v 2 := by
        dsimp [RT, k2, k3]
        rw [hy0, hq0]
        rw [← hXp]
        ring
      have hRT : RT ≠ 0 := by
        rw [hRTform]
        exact mul_ne_zero (neg_ne_zero.mpr he.ne') hp
      have hk1 : X * k2 + v 1 * k3 = -W * v 2 := by
        dsimp [k2, k3, W]
        ring
      have hk2 : v 1 * k2 - X * k3 = W * v 3 := by
        dsimp [k2, k3, W]
        ring
      let c : ℝ := (y 0 - rbase) / RT
      refine ⟨spaceTime
        (eventSpatialLift m hm b0 b1
          (b2 + c * k2) (b3 + c * k3) y) (c * W), ?_⟩
      apply PiLp.ext
      intro i
      by_cases hi0 : i = 0
      · subst i
        rw [fderiv_eventCoreMap_eventSpatialLift_apply_zero m hm hv]
        calc
          _ = rbase + c * RT := by
            dsimp [rbase, RT]
            ring
          _ = y 0 := by
            dsimp [c]
            field_simp [hRT]
            ring
      · by_cases hi1 : i = 1
        · subst i
          rw [fderiv_eventCoreMap_eventSpatialLift_apply_one]
          rw [hda, hde]
          calc
            _ = (b0 * v 2 + X * b2 + b1 * v 3 + v 1 * b3) +
                c * (X * k2 + v 1 * k3 + W * v 2) := by
              ring
            _ = y 1 := by rw [hbase1, hk1]; ring
        · by_cases hi2 : i = 2
          · subst i
            rw [fderiv_eventCoreMap_eventSpatialLift_apply_two]
            rw [hda]
            calc
              _ = (b1 * v 2 + v 1 * b2 - b0 * v 3 - X * b3) +
                  c * (v 1 * k2 - X * k3 - W * v 3) := by
                ring
              _ = y 2 := by rw [hbase2, hk2]; ring
          · rw [fderiv_eventCoreMap_eventSpatialLift_apply_tail
              m hm _ _ _ _ _ y hi0 hi1 hi2]


-- @@ L2072-2078 verbatim
theorem surjective_fderiv_eventCoreMap_of_eq_zero
    {v : E'} (hv : eventCoreMap m hm v = 0) :
    Function.Surjective (fderiv ℝ (eventCoreMap m hm) v) := by
  by_cases he : epsilon (vertC v) = 0
  · exact surjective_fderiv_eventCoreMap_of_epsilon_eq_zero m hm hv he
  · apply surjective_fderiv_eventCoreMap_of_epsilon_pos m hm hv
    exact lt_of_le_of_ne (epsilon_nonneg (vertC v)) (Ne.symm he)


-- @@ L2080-2103 verbatim
lemma eventMap_eventuallyEq_eventCoreMap {v : E'}
    (hv : eventMap m hm v = 0) :
    eventMap m hm =ᶠ[nhds v] eventCoreMap m hm := by
  have hvlevel : levelMap m hm (shift (vertC v)) (epsilon (vertC v))
      (initCLM (m + 3) v) = 0 := by
    simpa [eventMap] using hv
  have hcore :=
    (levelMap_eq_zero_iff_coreMap_eq_zero m hm _ _ _).mp hvlevel
  have hn := normSq_eq_one_of_coreMap_eq_zero m hm hcore
  have hcont : Continuous (fun q : E' =>
      CompactBirth.normSq (initCLM (m + 3) q)) :=
    CompactBirth.contDiff_normSq.continuous.comp
      (initCLM (m + 3)).continuous
  have hopen : IsOpen {q : E' |
      CompactBirth.normSq (initCLM (m + 3) q) < 2} :=
    isOpen_lt hcont continuous_const
  have hvopen : v ∈ {q : E' |
      CompactBirth.normSq (initCLM (m + 3) q) < 2} := by
    change CompactBirth.normSq (initCLM (m + 3) v) < 2
    rw [hn]
    norm_num
  exact Filter.eventuallyEq_of_mem (hopen.mem_nhds hvopen) fun q hq => by
    simp [eventMap, eventCoreMap, levelMap,
      CompactBirth.cutoff_eq_zero hq.le]


-- @@ L2105-2115 verbatim
theorem surjective_fderiv_eventMap_of_eq_zero
    {v : E'} (hv : eventMap m hm v = 0) :
    Function.Surjective (fderiv ℝ (eventMap m hm) v) := by
  have hvlevel : levelMap m hm (shift (vertC v)) (epsilon (vertC v))
      (initCLM (m + 3) v) = 0 := by
    simpa [eventMap] using hv
  have hcore : eventCoreMap m hm v = 0 := by
    simpa [eventCoreMap] using
      (levelMap_eq_zero_iff_coreMap_eq_zero m hm _ _ _).mp hvlevel
  rw [(eventMap_eventuallyEq_eventCoreMap m hm hv).fderiv_eq]
  exact surjective_fderiv_eventCoreMap_of_eq_zero m hm hcore


-- @@ L2117-2121 verbatim
lemma eventMap_collar_zero (x : E) {t : ℝ} (ht : t ≤ 1 / 4) :
    eventMap m hm (spaceTime x t) = sliceMap m hm 0 x := by
  rw [eventMap_spaceTime]
  simp only [sliceMap, shift_of_le_quarter ht, epsilon_of_le_quarter ht,
    shift_zero, epsilon_zero]


-- @@ L2123-2127 verbatim
lemma eventMap_collar_one (x : E) {t : ℝ} (ht : 3 / 4 ≤ t) :
    eventMap m hm (spaceTime x t) = sliceMap m hm 1 x := by
  rw [eventMap_spaceTime]
  simp only [sliceMap, shift_of_threeQuarter_le ht,
    epsilon_of_threeQuarter_le ht, shift_one, epsilon_one]


-- @@ L2129-2133 verbatim
theorem eventMap_eq_zero_iff_coreMap_eq_zero (v : E') :
    eventMap m hm v = 0 ↔
      coreMap m hm (shift (vertC v)) (epsilon (vertC v))
        (initCLM (m + 3) v) = 0 := by
  exact levelMap_eq_zero_iff_coreMap_eq_zero m hm _ _ _


-- @@ L2135-2139 verbatim
lemma eventMap_spatial_normSq_eq_one {v : E'}
    (hv : eventMap m hm v = 0) :
    CompactBirth.normSq (initCLM (m + 3) v) = 1 := by
  exact normSq_eq_one_of_coreMap_eq_zero m hm
    ((eventMap_eq_zero_iff_coreMap_eq_zero m hm v).mp hv)


-- @@ L2141-2148 verbatim
/-- The event zero surface is contained in the unit spatial sphere. -/
lemma eventMap_spatial_bounded :
    ∃ R : ℝ, ∀ v, eventMap m hm v = 0 → ‖initCLM (m + 3) v‖ ≤ R := by
  refine ⟨1, ?_⟩
  intro v hv
  have hn := eventMap_spatial_normSq_eq_one m hm hv
  rw [CompactBirth.normSq_eq_norm_sq] at hn
  nlinarith [norm_nonneg (initCLM (m + 3) v)]


-- @@ L2150-2154 verbatim
/-- The whole event has the same literal spatial background, uniformly in
time. -/
theorem eventMap_flatOutside {v : E'} (hv : 2 ≤ ‖initCLM (m + 3) v‖) :
    eventMap m hm v = CompactHopfPairConfiguration.background m hm := by
  exact levelMap_flatOutside m hm _ _ hv


-- @@ L2156-2156 verbatim
/-! ## Packaged compact pair-of-pants cobordism -/


-- @@ L2158-2161 verbatim
/-- The incoming framed level set, definitionally the existing compact Hopf
pair presentation. -/
def sourceFLS : FramedLevelSet (m + 2) :=
  CompactHopfPairConfiguration.X m hm


-- @@ L2163-2181 verbatim
/-- The compact pair-of-pants as a literal framed level cobordism. -/
def cobordism : FramedLevelCobordism (m + 2) where
  X₀ := sourceFLS m hm
  X₁ := targetFLS m hm
  G := eventMap m hm
  smooth := contDiff_eventMap m hm
  spatial_bounded := eventMap_spatial_bounded m hm
  regular := by
    intro v hv
    exact surjective_fderiv_eventMap_of_eq_zero m hm hv
  collar_zero := by
    intro x t ht
    rw [eventMap_collar_zero m hm x ht]
    simp [sourceFLS, sliceMap, levelMap_zero_zero_eq_source,
      CompactHopfPairConfiguration.X]
  collar_one := by
    intro x t ht
    rw [eventMap_collar_one m hm x ht]
    simp [targetFLS, sliceMap]


-- @@ L2183-2187 verbatim
/-- Constant positive sign on both incoming circles. -/
def sourceSign : FiberSign (sourceFLS m hm) where
  toFun := fun _ => 1
  continuous := continuous_const
  nonzero := by simp


-- @@ L2189-2193 verbatim
/-- Constant positive sign on the outgoing circle. -/
def targetSign : FiberSign (targetFLS m hm) where
  toFun := fun _ => 1
  continuous := continuous_const
  nonzero := by simp


-- @@ L2195-2205 verbatim
/-- The signed compact pair-of-pants, with its constant positive label. -/
def signedCobordism :
    SignedFramedLevelCobordism (sourceSign m hm) (targetSign m hm) where
  cobordism := cobordism m hm
  source_eq := rfl
  target_eq := rfl
  toFun := fun _ => 1
  continuous := continuous_const
  nonzero := by simp
  collar_zero := by simp [sourceSign]
  collar_one := by simp [targetSign]


-- @@ L2207-2210 verbatim
theorem nonempty_signedCobordism :
    Nonempty (SignedFramedLevelCobordism
      (sourceSign m hm) (targetSign m hm)) :=
  ⟨signedCobordism m hm⟩


-- @@ L2212-2212 verbatim
end CompactHopfPairPants

-- @@ L2213-2213 verbatim
end Submission
