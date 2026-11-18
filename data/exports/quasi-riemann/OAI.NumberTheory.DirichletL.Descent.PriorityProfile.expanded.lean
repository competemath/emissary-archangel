import OAI.NumberTheory.DirichletL.Descent.SecondBlockEnergy
import OAI.NumberTheory.DirichletL.Descent.WholePriorityPhysical


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff


-- @@ L9-9 verbatim
namespace SevenEighths.InverseMoment

-- @@ L10-10 verbatim
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic

-- @@ L11-11 verbatim
open InverseSecondPrincipalCaller InverseSecondProfileUniform

-- @@ L12-12 verbatim
open FourierBridge CompletedHeight SecondPassIntegration

-- @@ L13-13 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L15-18 verbatim
def priorityLogWindow (om:𝓢(ℝ,ℂ)) (a b:ℝ) (ha:0<a)
    (hs:Function.support om⊆Set.Icc a b) (negative:Bool):𝓢(ℝ,ℂ) :=
  if negative then conjugateProfile (CubicReflectionKernel.logSchwartz om a b ha hs (om.smooth ⊤))
  else CubicReflectionKernel.logSchwartz om a b ha hs (om.smooth ⊤)


-- @@ L20-20 verbatim
def priorityHeight (negative:Bool) (t:ℝ):ℝ := if negative then -t else t


-- @@ L22-36 verbatim
theorem priorityLogWindow_support (om:𝓢(ℝ,ℂ)) (a b:ℝ) (ha:0<a)
    (hs:Function.support om⊆Set.Icc a b) (negative:Bool) :
    Function.support (priorityLogWindow om a b ha hs negative)⊆
      Set.Icc (-(|Real.log a|+|Real.log b|)) (|Real.log a|+|Real.log b|) := by
  intro y hy
  have hn:om (Real.exp y)≠0:=by
    cases negative <;> simpa only [priorityLogWindow,Bool.false_eq_true,ite_true,ite_false,
      conjugateProfile_apply,CubicReflectionKernel.logSchwartz_apply,Function.mem_support,star_ne_zero] using hy
  have hh:=hs hn
  have hlo:=Real.log_le_log ha hh.1
  have hhi:=Real.log_le_log (Real.exp_pos y) hh.2
  rw [Real.log_exp] at hlo hhi
  constructor
  · linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)]
  · linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]


-- @@ L38-45 verbatim
theorem principalWindow_positiveSource (om:𝓢(ℝ,ℂ)) (a b:ℝ) (ha:0<a)
    (hs:Function.support om⊆Set.Icc a b) (negative:Bool) (t x:ℝ) (hx:0<x) :
    principalWindow om a b ha hs negative t x =
      positiveSource (priorityLogWindow om a b ha hs negative) 1 (priorityHeight negative t) x := by
  rw [principalWindow_apply]
  cases negative <;> simp only [priorityLogWindow,priorityHeight,Bool.false_eq_true,ite_true,ite_false,
    positiveSource,Real.log_one,add_zero,conjugateProfile_apply,CubicReflectionKernel.logSchwartz_apply,
    Real.exp_log hx,normTwistedSource]


-- @@ L47-50 verbatim
theorem positiveSource_conjugate_one (g:𝓢(ℝ,ℂ)) (t x:ℝ) :
    star (positiveSource (conjugateProfile g) 1 (-t) x)=positiveSource g 1 t x := by
  simp only [positiveSource,Real.log_one,add_zero,conjugateProfile_apply,star_mul,star_star,
    logPhase_conjugate,neg_neg,mul_comm]


-- @@ L52-78 verbatim
theorem actualSecondProfileRow_congr_positive {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι) (x:SecondProfileData ι) (slots₁ slots₂:Finset σ)
    (lists₁ lists₂:σ→Finset ι) (a₁ a₂:σ→ι→ℂ)
    (W₁ W₂ V₁ V₂:ℝ→ℂ) (Φ:𝓢(ℝ,ℂ)) (Y X:ℝ) (hX:0<X)
    (h₁:∀t,0<t→W₁ t=V₁ t) (h₂:∀t,0<t→W₂ t=V₂ t) :
    actualSecondProfileRow p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X =
      actualSecondProfileRow p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂ V₁ V₂ Φ Y X := by
  simp only [actualSecondProfileRow_eq_whole p hp hcop hg]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  congr 1
  unfold secondNormProfile
  have h0 : secondActualNorms p x N M 0 = primeProductNorm p x.common := rfl
  have h2 : secondActualNorms p x N M 2 = primeProductNorm p x.overlap := rfl
  have h4 : secondActualNorms p x N M 4 = primeProductNorm p N := rfl
  have h5 : secondActualNorms p x N M 5 = primeProductNorm p M := rfl
  rw [h0,h2,h4,h5]
  dsimp only
  rw [h₁ _ (div_pos (mul_pos (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))
      (primeProductNorm_pos p hp _)) hX),
    h₂ _ (div_pos (mul_pos (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))
      (primeProductNorm_pos p hp _)) hX)]


-- @@ L80-101 verbatim
theorem actual_priority_profile_common {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι) (x:SecondProfileData ι) (slots₁ slots₂:Finset σ)
    (lists₁ lists₂:σ→Finset ι) (a₁ a₂:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (negative:Bool) (t:ℝ) (Φ:𝓢(ℝ,ℂ)) (Y X:ℝ) (hX:0<X) :
    let g:=priorityLogWindow om lo hi hlo hs negative
    let θ:=priorityHeight negative t
    actualSecondProfileRow p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
      (principalWindow om lo hi hlo hs negative t) (principalWindow om lo hi hlo hs negative t) Φ Y X =
      actualSecondProfileRow p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
        (fun y=>star (positiveSource (conjugateProfile g) 1 (-θ) y)) (positiveSource g 1 θ) Φ Y X := by
  intro g θ
  apply actualSecondProfileRow_congr_positive p hp hcop hg pool x slots₁ slots₂ lists₁ lists₂ a₁ a₂
    _ _ _ _ Φ Y X hX
  · intro y hy
    rw [positiveSource_conjugate_one]
    exact principalWindow_positiveSource om lo hi hlo hs negative t y hy
  · intro y hy
    exact principalWindow_positiveSource om lo hi hlo hs negative t y hy


-- @@ L103-103 verbatim
end SevenEighths.InverseMoment


-- @@ L105-105 verbatim
end


-- @@ L107-107 verbatim
end OAI
