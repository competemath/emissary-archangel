/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderSlowCurlTime
public import LeanPool.NavierStokesAndEuler.Euler.ContinuousTimeWeight
import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialWeight
import LeanPool.NavierStokesAndEuler.Euler.CylinderSlowCurlBounds
public import LeanPool.NavierStokesAndEuler.Euler.CylinderPotentialTime


-- @@ L15-15 verbatim
/-! Related estimates used together by the same construction modules. -/


-- @@ L17-17 verbatim
section


-- @@ L19-19 verbatim
/-! Exact time-profile normalization of the actual slow curl and its time derivative. -/


-- @@ L21-21 verbatim
@[expose] public section


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace EulerCylinderSlowCurl


-- @@ L27-30 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerCylinderSobolev EulerLpCylinderTranslation
  EulerLpCylinderRectangular EulerMeanCoefficients EulerPacketPiola
  EulerParameterWordGevrey EulerGevrey EulerContinuousTimeWeight EulerCylinderPotential

-- @@ L31-31 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L33-33 verbatim
section General


-- @@ L35-36 verbatim
variable (P : ℝ) [Fact (0 < P)]
  {K : Type*} [TopologicalSpace K] [CompactSpace K]


-- @@ L38-39 verbatim
/-- Cache the standard `NormedAddCommGroup (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderSlowCurlWeight1 : NormedAddCommGroup (LiftL2 P) := inferInstance

-- @@ L40-41 verbatim
/-- Cache the standard `NormedSpace ℝ (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderSlowCurlWeight2 : NormedSpace ℝ (LiftL2 P) := inferInstance

-- @@ L42-44 verbatim
/-- Cache the standard `NormedAddCommGroup C(K,LiftL2 P)` instance to shorten typeclass
synthesis. -/
local instance instCylinderSlowCurlWeight3 : NormedAddCommGroup C(K,LiftL2 P) := inferInstance

-- @@ L45-46 verbatim
/-- Cache the standard `NormedSpace ℝ C(K,LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderSlowCurlWeight4 : NormedSpace ℝ C(K,LiftL2 P) := inferInstance


-- @@ L48-49 verbatim
variable (g : C(K, ℝ)) (G : C(K, Space →ᵇ Space →L[ℝ] Space))
  (p : C(K, LiftL2 P)) (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))


-- @@ L51-54 verbatim
include hp in
theorem term_weight (i : Fin 3) : term P G (weight g p) i = weight g (term P G p i) := by
  unfold term
  rw [derivativePath_weight P g p hp i.succ, fullMultiplier_weight]


-- @@ L56-60 verbatim
include hp in
theorem path_weight : path P G (weight g p) = weight g (path P G p) := by
  unfold path
  simp_rw [term_weight P g G p hp]
  exact (map_sum (weight g) _ _).symm


-- @@ L62-65 verbatim
include hp in
theorem path_normalize (hg : ∀ t, 0 < g t) :
    path P G (normalize g hg p) = normalize g hg (path P G p) :=
  path_weight P (reciprocal g hg) G p hp


-- @@ L67-82 verbatim
include hp in
/-- The literal normalized curl has the same radius, with one spatial derivative. -/
theorem normalized_path_block_bound (hg : ∀ t, 0 < g t)
    (hG : ContDiff ℝ ∞ (translateCoefficientPath G))
    (q : ℕ) (Rc C R D : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR : sobolevCoefficientRadius (Fin 4) Rc ≤ R)
    (hbG : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath G) a‖ ≤ C * majorant Rc 0 n)
    (d : ℕ) (hbp : ∀ n, block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg p)) n 0 ≤ D*majorant R d n)
    (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (path P G p))) n 0 ≤
      (9*sobolevCoefficientAmplitude (Fin 4) q Rc C*D)*majorant R (d+1) n := by
  rw [← path_normalize P g G p hp hg]
  exact path_block_bound P G hG (normalize g hg p)
    (weighted_orbit P (reciprocal g hg) p hp) q Rc C R D hRc hC hD hR hbG d hbp n


-- @@ L84-84 verbatim
end General


-- @@ L86-86 verbatim
section Time


-- @@ L88-93 verbatim
variable (P : ℝ) [Fact (0 < P)] (T : ℝ)
  (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
  (G G₁ : C(Icc (0 : ℝ) T, Space →ᵇ Space →L[ℝ] Space))
  (p f : C(Icc (0 : ℝ) T, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a f))


-- @@ L95-102 verbatim
include hp hf in
/-- This is C_t/g, so no derivative or extremum of the profile is needed. -/
theorem derivative_normalize :
    normalize g hg (derivative P T G G₁ p f) =
      derivative P T G G₁ (normalize g hg p) (normalize g hg f) := by
  unfold derivative EulerContinuousTimeWeight.normalize
  rw [map_add, path_weight P (reciprocal g hg) G₁ p hp,
    path_weight P (reciprocal g hg) G f hf]


-- @@ L104-124 verbatim
include hp hf in
theorem normalized_derivative_block_bound
    (hG : ContDiff ℝ ∞ (translateCoefficientPath G))
    (hG₁ : ContDiff ℝ ∞ (translateCoefficientPath G₁))
    (q : ℕ) (Rc C R D : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR : sobolevCoefficientRadius (Fin 4) Rc ≤ R)
    (hbG : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath G) a‖ ≤ C * majorant Rc 0 n)
    (hbG₁ : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath G₁) a‖ ≤ C * majorant Rc 0 n)
    (d : ℕ)
    (hbp : ∀ n, block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg p)) n 0 ≤ D*majorant R d n)
    (hbf : ∀ n, block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg f)) n 0 ≤ D*majorant R d n)
    (n : ℕ) :
    block standardDirection q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg (derivative P T G G₁ p f))) n 0 ≤
      (18*sobolevCoefficientAmplitude (Fin 4) q Rc C*D)*majorant R (d+1) n := by
  rw [derivative_normalize P T g hg G G₁ p f hp hf]
  exact derivative_block_bound P T G G₁ hG hG₁ (normalize g hg p) (normalize g hg f)
    (weighted_orbit P (reciprocal g hg) p hp) (weighted_orbit P (reciprocal g hg) f hf)
    q Rc C R D hRc hC hD hR hbG hbG₁ d hbp hbf n


-- @@ L126-126 verbatim
end Time


-- @@ L128-128 verbatim
end EulerCylinderSlowCurl


-- @@ L130-130 verbatim
end

-- @@ L131-131 verbatim
end


-- @@ L133-133 verbatim
end


-- @@ L135-135 verbatim
section


-- @@ L137-138 verbatim
/-! Same-radius bounds and literal profile normalization for the constructed potential time
derivative. -/


-- @@ L140-140 verbatim
@[expose] public section


-- @@ L142-142 verbatim
noncomputable section


-- @@ L144-144 verbatim
namespace EulerCylinderPotential


-- @@ L146-148 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerCylinderSmoothOrbit EulerLpCylinderTranslation EulerMeanCoefficients
  EulerParameterWordGevrey EulerGevrey EulerContinuousTimeWeight

-- @@ L149-149 verbatim
open scoped ContDiff BoundedContinuousFunction


-- @@ L151-157 verbatim
variable (P : ℝ) [Fact (0 < P)] (T : ℝ)
  (B B₁ : C(Icc (0 : ℝ) T, Space →ᵇ Space →L[ℝ] Space))
  (hB : ContDiff ℝ ∞ (translateCoefficientPath B))
  (hB₁ : ContDiff ℝ ∞ (translateCoefficientPath B₁))
  (p f : C(Icc (0 : ℝ) T, LiftL2 P))
  (hp : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a p))
  (hf : ContDiff ℝ ∞ (fun a : LiftTangent => pathTranslate P a f))


-- @@ L159-160 verbatim
/-- Cache the standard `NormedAddCommGroup (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderPotentialTimeWeight1 : NormedAddCommGroup (LiftL2 P) := inferInstance

-- @@ L161-162 verbatim
/-- Cache the standard `NormedSpace ℝ (LiftL2 P)` instance to shorten typeclass synthesis. -/
local instance instCylinderPotentialTimeWeight2 : NormedSpace ℝ (LiftL2 P) := inferInstance

-- @@ L163-166 verbatim
/-- Cache the standard `NormedAddCommGroup C(Icc (0 : ℝ) T,LiftL2 P)` instance to shorten
typeclass synthesis. -/
local instance instCylinderPotentialTimeWeight3 : NormedAddCommGroup C(Icc (0 : ℝ) T,LiftL2 P) :=
    inferInstance

-- @@ L167-170 verbatim
/-- Cache the standard `NormedSpace ℝ C(Icc (0 : ℝ) T,LiftL2 P)` instance to shorten typeclass
synthesis. -/
local instance instCylinderPotentialTimeWeight4 : NormedSpace ℝ C(Icc (0 : ℝ) T,LiftL2 P) :=
    inferInstance


-- @@ L172-200 verbatim
include hB hB₁ hp hf in
theorem potentialDerivative_block_bound {ι : Type*} [Fintype ι]
    (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (Rc C R D : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR : sobolevCoefficientRadius ι Rc ≤ R)
    (hbB : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath B) a‖ ≤ C * majorant Rc 0 n)
    (hbB₁ : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath B₁) a‖ ≤ C * majorant Rc 0 n)
    (d : ℕ)
    (hbp : ∀ n, block directions q (fun a : LiftTangent => pathTranslate P a p) n 0 ≤ D*majorant R
        d n)
    (hbf : ∀ n, block directions q (fun a : LiftTangent => pathTranslate P a f) n 0 ≤ D*majorant R
        d n)
    (n : ℕ) :
    block directions q (fun a : LiftTangent =>
      pathTranslate P a (potentialDerivative P T B B₁ p f)) n 0 ≤
      (6*sobolevCoefficientAmplitude ι q Rc C*(P*D))*majorant R d n := by
  have he : (fun a : LiftTangent => pathTranslate P a (potentialDerivative P T B B₁ p f)) =
      (fun a : LiftTangent => pathTranslate P a (potentialPath P B₁ p)) +
        (fun a : LiftTangent => pathTranslate P a (potentialPath P B f)) := by
    funext a
    exact map_add (pathTranslate P a) _ _
  rw [he]
  have hs := block_add_le directions q _ _
    (potentialPath_orbit P B₁ hB₁ p hp) (potentialPath_orbit P B hB f hf) n (0 : LiftTangent)
  have h₁ := potentialPath_block_bound P B₁ hB₁ p hp directions hd q
    Rc C R D hRc hC hD hR hbB₁ d hbp n
  have h₂ := potentialPath_block_bound P B hB f hf directions hd q
    Rc C R D hRc hC hD hR hbB d hbf n
  exact (hs.trans (add_le_add h₁ h₂)).trans_eq (by ring)


-- @@ L202-207 verbatim
theorem potentialDerivative_normalize (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t) :
    normalize g hg (potentialDerivative P T B B₁ p f) =
      potentialDerivative P T B B₁ (normalize g hg p) (normalize g hg f) := by
  unfold potentialDerivative EulerContinuousTimeWeight.normalize
  rw [map_add, potentialPath_weight P (reciprocal g hg) p B₁,
    potentialPath_weight P (reciprocal g hg) f B]


-- @@ L209-231 verbatim
include hB hB₁ hp hf in
/-- Estimate Q_t/g from A/g and A_t/g, without differentiating the profile g. -/
theorem normalized_potentialDerivative_block_bound
    (g : C(Icc (0 : ℝ) T, ℝ)) (hg : ∀ t, 0 < g t)
    {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (hd : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
    (Rc C R D : ℝ) (hRc : 0 ≤ Rc) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hR : sobolevCoefficientRadius ι Rc ≤ R)
    (hbB : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath B) a‖ ≤ C * majorant Rc 0 n)
    (hbB₁ : ∀ n a, ‖iteratedFDeriv ℝ n (translateCoefficientPath B₁) a‖ ≤ C * majorant Rc 0 n)
    (d : ℕ)
    (hbp : ∀ n, block directions q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg p)) n 0 ≤ D*majorant R d n)
    (hbf : ∀ n, block directions q
      (fun a : LiftTangent => pathTranslate P a (normalize g hg f)) n 0 ≤ D*majorant R d n)
    (n : ℕ) :
    block directions q (fun a : LiftTangent =>
      pathTranslate P a (normalize g hg (potentialDerivative P T B B₁ p f))) n 0 ≤
      (6*sobolevCoefficientAmplitude ι q Rc C*(P*D))*majorant R d n := by
  rw [potentialDerivative_normalize]
  exact potentialDerivative_block_bound P T B B₁ hB hB₁
    (normalize g hg p) (normalize g hg f)
    (weighted_orbit P (reciprocal g hg) p hp) (weighted_orbit P (reciprocal g hg) f hf)
    directions hd q Rc C R D hRc hC hD hR hbB hbB₁ d hbp hbf n


-- @@ L233-233 verbatim
end EulerCylinderPotential


-- @@ L235-235 verbatim
end

-- @@ L236-236 verbatim
end


-- @@ L238-238 verbatim
end
