/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import LeanPool.JacobianDiffgeo.Forms.Analyticity
import LeanPool.JacobianDiffgeo.Surface.Bridges
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul


-- @@ L13-26 verbatim
/-!
# The differential of a holomorphic function (CC1, design §2.4)

Unit: holomorphic-forms (`docs/design/holomorphic-forms.md`). `RS.mdifferential f hf` is the
holomorphic 1-form `df` of a holomorphic function `f : X → ℂ`; in every maximal-atlas chart its
coefficient is the planar derivative of the chart composite
(`RS.coeffIn_mdifferential : coeffIn e (df) = deriv (f ∘ e.symm)` on `e.target`).

Also provides `RS.Form1.smulFun` (multiplication of a form by a holomorphic function, used by
canonical-forms) with its coefficient formula.

Holomorphic 1-forms only — no meromorphic machinery here (meromorphic 1-forms are later
`f • η` pairs in canonical-forms/meromorphic-trace).
-/


-- @@ L28-28 verbatim
@[expose] public section


-- @@ L30-30 verbatim
open scoped ContDiff Manifold Bundle

-- @@ L31-31 verbatim
open Set IsManifold


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-35 verbatim
namespace RS


-- @@ L37-37 verbatim
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]


-- @@ L39-43 verbatim
/-- The underlying covector section of the differential: `x ↦ d f_x`, crossing the
`TangentSpace ↦ Bundle.Trivial` defeq in the codomain. -/
def mdifferentialSection (f : X → ℂ) (x : X) :
    TangentSpace 𝓘(ℂ) x →L[ℂ] Bundle.Trivial X ℂ x :=
  (mfderiv 𝓘(ℂ) 𝓘(ℂ) f x : TangentSpace 𝓘(ℂ) x →L[ℂ] TangentSpace 𝓘(ℂ) (f x))


-- @@ L45-57 verbatim
omit [IsManifold 𝓘(ℂ, ℂ) ω X] in
/-- The raw chart coefficient of the differential section is the derivative of the chart
composite. -/
theorem coeffInFun_mdifferentialSection {f : X → ℂ} {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) {z : ℂ} (hz : z ∈ e.target)
    (hf : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) f (e.symm z)) :
    coeffInFun e (mdifferentialSection f) z = deriv (f ∘ ⇑e.symm) z := by
  have hesymm : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (⇑e.symm) z :=
    (contMDiffAt_symm_of_mem_maximalAtlas he hz).mdifferentiableAt (by simp)
  calc coeffInFun e (mdifferentialSection f) z
      = tangentCoord (mfderiv 𝓘(ℂ) 𝓘(ℂ) f (e.symm z)
          (mfderiv 𝓘(ℂ) 𝓘(ℂ) (⇑e.symm) z (1 : ℂ))) := rfl
    _ = deriv (f ∘ ⇑e.symm) z := tangentCoord_mfderiv_comp hf hesymm


-- @@ L59-69 verbatim
/-- The differential of a holomorphic function, as a holomorphic 1-form. -/
def mdifferential (f : X → ℂ) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) : Form1 X :=
  Form1.ofSectionAnalytic (mdifferentialSection f) (fun x => by
    have hb : AnalyticAt ℂ (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
      contMDiffAt_iff_analyticAt_comp_chartAt.mp (hf x)
    have heq : coeffInFun (chartAt ℂ x) (mdifferentialSection f) =ᶠ[nhds (chartAt ℂ x x)]
        deriv (f ∘ ⇑(chartAt ℂ x).symm) := by
      filter_upwards [(chartAt ℂ x).open_target.mem_nhds (mem_chart_target ℂ x)] with z hz
      exact coeffInFun_mdifferentialSection (chart_mem_maximalAtlas x) hz
        ((hf _).mdifferentiableAt (by simp))
    exact hb.deriv.congr heq.symm)


-- @@ L71-76 verbatim
/-- Chart-coefficient formula for the differential: `coeffIn e (df) = deriv (f ∘ e.symm)` on
`e.target` (CC1's `d`-rule). -/
theorem coeffIn_mdifferential {e : OpenPartialHomeomorph X ℂ}
    (he : e ∈ maximalAtlas 𝓘(ℂ) ω X) {f : X → ℂ} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) :
    Set.EqOn (coeffIn e (mdifferential f hf)) (deriv (f ∘ ⇑e.symm)) e.target :=
  fun _z hz => coeffInFun_mdifferentialSection he hz ((hf _).mdifferentiableAt (by simp))


-- @@ L78-81 verbatim
/-- Preferred-chart coefficient of the differential. -/
theorem coeffAt_mdifferential (f : X → ℂ) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (x : X) :
    coeffAt x (mdifferential f hf) = deriv (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
  coeffIn_mdifferential (chart_mem_maximalAtlas x) hf (mem_chart_target ℂ x)


-- @@ L83-86 verbatim
/-! ### `ℂ`-linearity of the differential

The smoothness proofs of the combined functions are taken as hypotheses (no smooth-algebra
instances needed; the value of `mdifferential` does not depend on the proof argument). -/


-- @@ L88-100 verbatim
@[simp]
theorem mdifferential_add {f g : X → ℂ} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) (hfg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (f + g)) :
    mdifferential (f + g) hfg = mdifferential f hf + mdifferential g hg := by
  refine Form1.ext_coeffAt fun x => ?_
  have hdf : DifferentiableAt ℂ (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
    (contMDiffAt_iff_analyticAt_comp_chartAt.mp (hf x)).differentiableAt
  have hdg : DifferentiableAt ℂ (g ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
    (contMDiffAt_iff_analyticAt_comp_chartAt.mp (hg x)).differentiableAt
  have hcomp : (f + g) ∘ ⇑(chartAt ℂ x).symm =
      (f ∘ ⇑(chartAt ℂ x).symm) + (g ∘ ⇑(chartAt ℂ x).symm) := rfl
  rw [coeffAt_add, coeffAt_mdifferential, coeffAt_mdifferential, coeffAt_mdifferential,
    hcomp, deriv_add hdf hdg]


-- @@ L102-111 verbatim
@[simp]
theorem mdifferential_smul (c : ℂ) {f : X → ℂ} (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (hcf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω (c • f)) :
    mdifferential (c • f) hcf = c • mdifferential f hf := by
  refine Form1.ext_coeffAt fun x => ?_
  have hdf : DifferentiableAt ℂ (f ∘ ⇑(chartAt ℂ x).symm) (chartAt ℂ x x) :=
    (contMDiffAt_iff_analyticAt_comp_chartAt.mp (hf x)).differentiableAt
  have hcomp : (c • f) ∘ ⇑(chartAt ℂ x).symm = c • (f ∘ ⇑(chartAt ℂ x).symm) := rfl
  rw [coeffAt_smul, coeffAt_mdifferential, coeffAt_mdifferential, hcomp,
    deriv_const_smul c hdf, smul_eq_mul]


-- @@ L113-119 verbatim
@[simp]
theorem mdifferential_const (c : ℂ) :
    mdifferential (fun _ : X => c) contMDiff_const = 0 := by
  refine Form1.ext_coeffAt fun x => ?_
  rw [coeffAt_mdifferential, coeffAt_zero]
  have hcomp : (fun _ : X => c) ∘ ⇑(chartAt ℂ x).symm = fun _ => c := rfl
  rw [hcomp, deriv_const]


-- @@ L121-121 verbatim
/-! ### Multiplication of a form by a holomorphic function -/


-- @@ L123-126 verbatim
/-- Multiply a holomorphic 1-form by a holomorphic function (used by canonical-forms to build
`h • η`). -/
def Form1.smulFun (f : X → ℂ) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (η : Form1 X) : Form1 X :=
  ⟨f • ⇑η, hf.smul_section η.contMDiff⟩


-- @@ L128-131 verbatim
@[simp]
theorem coeffIn_smulFun (e : OpenPartialHomeomorph X ℂ) (f : X → ℂ)
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (η : Form1 X) (z : ℂ) :
    coeffIn e (Form1.smulFun f hf η) z = f (e.symm z) * coeffIn e η z := rfl


-- @@ L133-138 verbatim
@[simp]
theorem coeffAt_smulFun (x : X) (f : X → ℂ) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (η : Form1 X) :
    coeffAt x (Form1.smulFun f hf η) = f x * coeffAt x η := by
  have h : coeffAt x (Form1.smulFun f hf η) =
      f ((chartAt ℂ x).symm (chartAt ℂ x x)) * coeffAt x η := rfl
  rw [h, (chartAt ℂ x).left_inv (mem_chart_source ℂ x)]


-- @@ L140-140 verbatim
end RS


-- @@ L142-142 verbatim
end
