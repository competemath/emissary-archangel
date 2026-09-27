/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketForcing
public import LeanPool.NavierStokesAndEuler.Euler.LpSmoothFieldAlgebra


-- @@ L12-18 verbatim
/-!
# Genuine algebraic closure of admissible mean forcing

Admissibility is preserved by finite sums, bounded linear maps, and actual
spatial directional derivatives. Every witness consists of literal smooth
fields and their continuous L² jets; no inverse or equation is assumed.
-/


-- @@ L20-20 verbatim
@[expose] public section



-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace EulerMeanPacketProvider


-- @@ L27-29 verbatim
open Set MeasureTheory ContinuousLinearMap EulerSmoothLimit EulerMeanSolenoidal
  EulerLpTranslation EulerLpTranslation.SmoothL2Field EulerPacketPointJets
  EulerPacketProfileRecursion

-- @@ L30-30 verbatim
open scoped ContDiff


-- @@ L32-32 verbatim
namespace Forcing


-- @@ L34-34 verbatim
variable {D : Data} {raw raw' : VectorField}


-- @@ L36-44 verbatim
/-- The time path is constructed from the actual zeroth L² jet. -/
def ofSlices (A : ℝ → SmoothL2Field Space)
    (hA : ∀ n, Continuous (fun t : Icc (0 : ℝ) D.T => (A t).jetLp n))
    (heq : ∀ (t : Icc (0 : ℝ) D.T) x θ, raw (t,(x,θ)) = (A t).field x) : Forcing D raw where
  slices := A
  jets_continuous := hA
  path := ⟨fun t => (A t).toLp, continuous_toLp (fun t : Icc (0 : ℝ) D.T => A t) (hA 0)⟩
  path_eq _ := rfl
  raw_eq := heq


-- @@ L46-49 verbatim
/-- Zero, given by `ofSlices (fun _ => zeroField) (fun _ => continuous_const) (fun _ _ _ =>
rfl)`. -/
def zero (D : Data) : Forcing D (0 : VectorField) :=
  ofSlices (fun _ => zeroField) (fun _ => continuous_const) (fun _ _ _ => rfl)


-- @@ L51-56 verbatim
/-- Add, constructed using `ofSlices`. -/
def add (G : Forcing D raw) (H : Forcing D raw') : Forcing D (raw+raw') :=
  ofSlices (fun t => addField (G.slices t) (H.slices t))
    (continuous_jetLp_addField (fun t : Icc (0 : ℝ) D.T => G.slices t)
      (fun t : Icc (0 : ℝ) D.T => H.slices t) G.jets_continuous H.jets_continuous)
    (fun t x θ => by simp only [Pi.add_apply, G.raw_eq t x θ, H.raw_eq t x θ, addField_field])


-- @@ L58-62 verbatim
/-- Applying a genuine bounded linear map preserves every actual L² jet. -/
def map (G : Forcing D raw) (L : Space →L[ℝ] Space) : Forcing D (fun z => L (raw z)) :=
  ofSlices (fun t => mapField L (G.slices t))
    (continuous_jetLp_mapField L (fun t : Icc (0 : ℝ) D.T => G.slices t) G.jets_continuous)
    (fun t x θ => by simp only [G.raw_eq t x θ, mapField_field])


-- @@ L64-66 verbatim
/-- Smul, given by `G.map (c • ContinuousLinearMap.id ℝ Space)`. -/
def smul (G : Forcing D raw) (c : ℝ) : Forcing D (c • raw) :=
  G.map (c • ContinuousLinearMap.id ℝ Space)


-- @@ L68-69 verbatim
/-- Neg, given by `G.map (-ContinuousLinearMap.id ℝ Space)`. -/
def neg (G : Forcing D raw) : Forcing D (-raw) := G.map (-ContinuousLinearMap.id ℝ Space)


-- @@ L71-81 verbatim
/-- The derivative is the ordinary derivative of the prescribed raw field at fixed time and angle.
-/
def spatialDerivative (G : Forcing D raw) (v : Space) :
    Forcing D (fun z => fderiv ℝ (fun x => raw (z.1,(x,z.2.2))) z.2.1 v) :=
  ofSlices (fun t => directionalField (G.slices t) v)
    (continuous_jetLp_directionalField (fun t : Icc (0 : ℝ) D.T => G.slices t) G.jets_continuous v)
    (fun t x θ => by
      have he : (fun y => raw (t,(y,θ))) = (G.slices t).field :=
        funext (fun y => G.raw_eq t y θ)
      rw [he]
      rfl)


-- @@ L83-83 verbatim
end Forcing


-- @@ L85-97 verbatim
/-- Every actual finite sum of admissible forcing fields is admissible. -/
theorem admissible_finset_sum {ι : Type*} (D : Data) (s : Finset ι) (raw : ι → VectorField)
    (h : ∀ i ∈ s, Nonempty (Forcing D (raw i))) : Nonempty (Forcing D (∑ i ∈ s, raw i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (show Nonempty (Forcing D 0) from ⟨Forcing.zero D⟩)
  | @insert i s his ih =>
    have hi : Nonempty (Forcing D (raw i)) := h i (Finset.mem_insert_self i s)
    have hs : Nonempty (Forcing D (∑ j ∈ s, raw j)) := ih (fun j hj => h j
        (Finset.mem_insert_of_mem hj))
    simpa only [Finset.sum_insert his] using
      (show Nonempty (Forcing D (raw i+∑ j ∈ s, raw j)) from ⟨(Classical.choice hi).add
          (Classical.choice hs)⟩)


-- @@ L99-99 verbatim
end EulerMeanPacketProvider
