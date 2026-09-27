/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldWeight
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldUnique
import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderWeightedLinear
import LeanPool.NavierStokesAndEuler.Euler.PacketGradeAbsorption


-- @@ L14-14 verbatim
/-! Comparison of the actual time profiles and absorption of a finite family at a fixed radius. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace EulerPacketCylinderField


-- @@ L23-24 verbatim
open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace
  EulerPacketProfileRecursion EulerContinuousTimeWeight EulerGevrey

-- @@ L25-25 verbatim
open scoped ContDiff


-- @@ L27-31 verbatim
/-- Profile ratio, given by `⟨fun t => g t/b t,g.continuous.div b.continuous (fun t => (hb
t).ne')⟩`. -/
def profileRatio {K : Type*} [TopologicalSpace K]
    (g b : C(K, ℝ)) (hb : ∀ t, 0 < b t) : C(K,ℝ) :=
  ⟨fun t => g t/b t,g.continuous.div b.continuous (fun t => (hb t).ne')⟩


-- @@ L33-34 verbatim
@[simp] theorem profileRatio_apply {K : Type*} [TopologicalSpace K]
    (g b : C(K, ℝ)) (hb : ∀ t, 0 < b t) (t : K) : profileRatio g b hb t = g t/b t := rfl


-- @@ L36-40 verbatim
theorem profileRatio_abs_le {K : Type*} [TopologicalSpace K]
    (g b : C(K, ℝ)) (hg : ∀ t, 0 ≤ g t) (hb : ∀ t, 0 < b t)
    (C : ℝ) (hC : ∀ t, g t ≤ C * b t) (t : K) : |profileRatio g b hb t| ≤ C := by
  rw [profileRatio_apply,abs_of_nonneg (div_nonneg (hg t) (hb t).le)]
  exact (div_le_iff₀ (hb t)).mpr (hC t)


-- @@ L42-42 verbatim
namespace Field


-- @@ L44-46 verbatim
variable {P T : ℝ} [Fact (0 < P)] {raw : VectorField} (G : Field P T raw)
  (hT : 0 ≤ T) (g b : C(Icc (0 : ℝ) T, ℝ))
  (hg : ∀ t, 0 < g t) (hb : ∀ t, 0 < b t)


-- @@ L48-58 verbatim
theorem normalized_changeProfile_path : (G.normalized hT b hb).path =
    ((G.normalized hT g hg).weighted hT (profileRatio g b hb)).path := by
  apply path_eq_of_raw_eq
  intro t x θ
  change profileRatio g b hb (projIcc 0 T hT t) •
      ((g (projIcc 0 T hT t))⁻¹ • raw (t,(x,θ))) =
        (b (projIcc 0 T hT t))⁻¹ • raw (t,(x,θ))
  rw [projIcc_of_mem hT t.property]
  simp only [profileRatio_apply,smul_smul]
  congr 1
  field_simp [(hg t).ne',(hb t).ne']


-- @@ L60-60 verbatim
variable {G g hg}


-- @@ L62-68 verbatim
theorem WordBound.changeProfile {q d : ℕ} {R A : ℝ}
    (hG : (G.normalized hT g hg).WordBound q R A d)
    (C : ℝ) (hC : 0 ≤ C) (hgb : ∀ t, g t ≤ C * b t) :
    (G.normalized hT b hb).WordBound q R (C*A) d := by
  have hw := hG.weighted hT (profileRatio g b hb) C hC
    (profileRatio_abs_le g b (fun t => (hg t).le) hb C hgb)
  exact hw.of_path_eq _ (G.normalized_changeProfile_path hT g b hg hb)


-- @@ L70-74 verbatim
theorem WordBound.enlargeProfile {q d : ℕ} {R A : ℝ}
    (hG : (G.normalized hT g hg).WordBound q R A d) (hgb : ∀ t, g t ≤ b t) :
    (G.normalized hT b hb).WordBound q R A d := by
  have hh := hG.changeProfile hT b hb 1 zero_le_one (by simpa only [one_mul] using hgb)
  simpa only [one_mul] using hh


-- @@ L76-85 verbatim
theorem wordBound_normalized_finset_absorb {ι : Type*} (s : Finset ι)
    (f : ι → VectorField) (W : ∀ i, Field P T (f i))
    (q : ℕ) (R C : ℝ) (d : ℕ) (shift : ι → ℕ)
    (hR : 1 ≤ R) (hC : 0 ≤ C) (hCR : C ≤ R) (hd : 0 < d)
    (hcount : s.card ≤ d ^ 2) (hshift : ∀ i ∈ s, shift i < d)
    (hW : ∀ i ∈ s, ((W i).normalized hT b hb).WordBound q R C (shift i)) :
    ((Field.finsetSum s f W).normalized hT b hb).WordBound q R 1 d := by
  have hh := wordBound_finset_absorb s _ (fun i => (W i).normalized hT b hb)
    q R C d shift hR hC hCR hd hcount hshift hW
  exact hh.of_path_eq _ (normalized_finsetSum_path hT b hb s f W)


-- @@ L87-87 verbatim
end Field

-- @@ L88-88 verbatim
end EulerPacketCylinderField
