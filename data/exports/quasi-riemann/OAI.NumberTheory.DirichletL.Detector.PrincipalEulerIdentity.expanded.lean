import OAI.NumberTheory.DirichletL.Detector.LocalSummation
import OAI.NumberTheory.DirichletL.Detector.EulerCoordinates


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
namespace SevenEighths.ProbeEuler

-- @@ L9-9 verbatim
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L12-25 verbatim
lemma evenRatio_eq_coordR (Q : ℝ) (hQ : 0<Q) (a x z : ℂ) :
    evenRatio Q a ((Q:ℂ)^(-x)) (coordV Q z) = coordR Q (a^2) x z := by
  have hn : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  unfold evenRatio coordR coordV
  calc
    _ = a^2 * ((Q:ℂ)^4 * ((Q:ℂ)^(-x))^6 * (Q:ℂ)^(-6*z)) := by ring
    _ = a^2 * ((Q:ℂ)^(4:ℂ) * (Q:ℂ)^((6:ℂ)*(-x)) * (Q:ℂ)^(-6*z)) := by
      rw [Complex.cpow_ofNat]
      have h6 : (Q:ℂ)^((6:ℂ)*(-x)) = ((Q:ℂ)^(-x))^6 := by
        simpa using Complex.cpow_nat_mul (Q:ℂ) 6 (-x)
      rw [h6]
    _ = a^2 * (Q:ℂ)^((4:ℂ)+6*(-x)+(-6*z)) := by
      rw [← Complex.cpow_add _ _ hn, ← Complex.cpow_add _ _ hn]
    _ = _ := by congr 2; ring


-- @@ L27-32 verbatim
lemma coordK_eq_geometric (Q : ℝ) (hQ : 0<Q) (eta x w : ℂ) :
    coordK Q eta x w = eta*((Q:ℂ)-1)*((Q:ℂ)^(-x))*((Q:ℂ)^(-w)) := by
  have hn : (Q:ℂ) ≠ 0 := by exact_mod_cast hQ.ne'
  unfold coordK
  rw [show -x-w = -x+(-w) by ring, Complex.cpow_add _ _ hn]
  ring


-- @@ L34-38 verbatim
lemma one_sub_ne_zero_of_norm_lt_one (a : ℂ) (ha : ‖a‖<1) : 1-a ≠ 0 := by
  intro h
  have he : a=1 := by linear_combination -h
  rw [he, norm_one] at ha
  exact lt_irrefl _ ha


-- @@ L40-41 verbatim
variable (p : O) (hp : Prime p) [(Ideal.span {p} : Ideal O).IsMaximal]
  (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)


-- @@ L43-44 verbatim
def principalFullSeries (eta a X W V : ℂ) : ℂ :=
  1/(1-V)+W/(1-W)+principalMarkedSeries p hp hg eta a X W V


-- @@ L46-46 verbatim
include hc


-- @@ L48-79 verbatim
theorem principalFullSeries_euler_identity (eta a x w z : ℂ)
    (hV : ‖coordV (Ideal.absNorm (Ideal.span {p})) z‖<1)
    (hR : ‖coordR (Ideal.absNorm (Ideal.span {p})) (a^2) x z‖<1)
    (hW : ‖coordW (Ideal.absNorm (Ideal.span {p})) 1 w‖<1)
    (hD : 1-coordD (Ideal.absNorm (Ideal.span {p})) eta 1 x ≠ 0) :
    let Q : ℝ := Ideal.absNorm (Ideal.span {p})
    principalFullSeries p hp hg eta a ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w)) (coordV Q z) =
      (1-coordD Q eta 1 x) / ((1-coordV Q z)*(1-coordW Q 1 w)) *
        unramifiedClosed Q (a^2) eta 1 x w z := by
  dsimp only
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  simp only [Complex.ofReal_natCast]
  have hratio := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ a x z
  simp only [Complex.ofReal_natCast] at hratio
  have hr : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) a
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
      (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    rw [hratio]
    exact hR
  rw [principalFullSeries, principalMarkedSeries_eq p hp hg hc _ _ _ _ _ hV hr,
    hratio]
  unfold unramifiedClosed
  dsimp only
  rw [coordK_eq_geometric _ hQ]
  have hv := one_sub_ne_zero_of_norm_lt_one _ hV
  have hw := one_sub_ne_zero_of_norm_lt_one _ hW
  simp only [coordW, coordD, star_one, mul_one, one_mul, Complex.ofReal_natCast] at hD hw ⊢
  unfold ProbeLocal.continuedCorrection
  field_simp [hD, hv, hw]
  ring


-- @@ L81-81 verbatim
omit hc


-- @@ L83-84 verbatim
def actualACube (eta : HeckeFamily.Character) (p : O) : ℂ :=
  star (FiniteGaussPhase.angularFactor p)^3 * HeckeFamily.elementCoeff eta p^3


-- @@ L86-89 verbatim
lemma actualACube_sq (eta : HeckeFamily.Character) (p : O) :
    actualACube eta p ^ 2 = actualAPhase eta p := by
  unfold actualACube actualAPhase
  ring


-- @@ L91-91 verbatim
end SevenEighths.ProbeEuler

-- @@ L92-92 verbatim
end


-- @@ L94-94 verbatim
end OAI
