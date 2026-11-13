import Mathlib
import Submission.SORotation
import Submission.FrameGaugeNormalization


-- @@ L5-16 verbatim
/-!
# General special-orthogonal frame gauges

A smooth field of special-orthogonal matrices acts on the codomain of a framed
defining map by invertible continuous linear maps.  This file packages that
action and feeds a smooth `SO(n)`-valued homotopy directly into
`DefiningMapHomotopy.ofGauge`.

Thus the analytic conversion from a smooth frame homotopy to an actual
common-fiber defining-map homotopy is completely general; only the geometric
extension of loop data to such a smooth spatial field remains separate.
-/


-- @@ L18-18 verbatim
set_option autoImplicit false


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
open Set Function

-- @@ L23-23 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L25-25 verbatim
namespace Submission

-- @@ L26-26 verbatim
namespace SOFrameGauge


-- @@ L28-28 verbatim
variable {n : ℕ}


-- @@ L30-30 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)

-- @@ L31-31 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L32-32 verbatim
local notation "M" => Matrix (Fin n) (Fin n) ℝ


-- @@ L34-36 verbatim
/-- The Euclidean continuous-linear action of a special-orthogonal matrix. -/
def toCLM (A : SOGroup n) : F →L[ℝ] F :=
  (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) (A : M)


-- @@ L38-41 verbatim
@[simp] theorem toCLM_apply (A : SOGroup n) (x : F) :
    toCLM A x =
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) (A : M) x :=
  rfl


-- @@ L43-47 verbatim
@[simp] theorem toCLM_apply_coord (A : SOGroup n) (x : F) (i : Fin n) :
    toCLM A x i = ∑ j : Fin n, (A : M) i j * x j := by
  change (Matrix.toLpLin 2 2 (A : M) x) i = _
  rw [Matrix.toLpLin_apply]
  rfl


-- @@ L49-54 verbatim
@[simp] theorem toCLM_one :
    toCLM (1 : SOGroup n) = ContinuousLinearMap.id ℝ F := by
  apply ContinuousLinearMap.ext
  intro x
  change (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) (1 : M) x = x
  simp


-- @@ L56-67 verbatim
theorem toCLM_inv_apply (A : SOGroup n) (x : F) :
    toCLM A⁻¹ (toCLM A x) = x := by
  change (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) ((↑A⁻¹ : M))
    ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) (A : M) x) = x
  change
    (((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) ((↑A⁻¹ : M))) *
      ((Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)) (A : M))) x = x
  rw [← map_mul]
  change (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ))
    ((↑(A⁻¹ * A) : M)) x = x
  rw [inv_mul_cancel A]
  simp


-- @@ L69-71 verbatim
theorem toCLM_apply_inv (A : SOGroup n) (x : F) :
    toCLM A (toCLM A⁻¹ x) = x := by
  simpa using toCLM_inv_apply A⁻¹ x


-- @@ L73-79 verbatim
theorem toCLM_bijective (A : SOGroup n) : Bijective (toCLM A) := by
  constructor
  · intro x y hxy
    have h := congrArg (toCLM A⁻¹) hxy
    simpa only [toCLM_inv_apply] using h
  · intro y
    exact ⟨toCLM A⁻¹ y, toCLM_apply_inv A y⟩


-- @@ L81-94 verbatim
/-- Coordinatewise smoothness of an `SO(n)` field implies smoothness of its
continuous-linear action.  Matrix space itself carries only the product
topology here, so the coordinatewise statement is the robust formulation. -/
theorem contDiff_toCLM {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {R : P → SOGroup n}
    (hR : ∀ i j, ContDiff ℝ ∞ (fun p => ((R p : SOGroup n) : M) i j)) :
    ContDiff ℝ ∞ (fun p => toCLM (R p)) := by
  rw [contDiff_clm_apply_iff]
  intro x
  rw [contDiff_euclidean]
  intro i
  simp_rw [toCLM_apply_coord]
  exact ContDiff.sum (s := Finset.univ)
    (fun j _ => (hR i j).mul contDiff_const)


-- @@ L96-111 verbatim
/-- A smooth `SO(n)`-valued family starting at the identity gives an actual
defining-map homotopy, with no separate invertibility assumption. -/
def homotopy (X : FramedLevelSet n)
    (R : ℝ → E → SOGroup n)
    (hR : ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × E => ((R p.1 p.2 : SOGroup n) : M) i j))
    (hRzero : ∀ x, R 0 x = 1) :
    DefiningMapHomotopy X
      (X.gaugeTransform (fun x => toCLM (R 1 x))
        (contDiff_toCLM (fun i j =>
          (hR i j).comp (contDiff_const.prodMk contDiff_id)))
        (fun x => toCLM_bijective (R 1 x))) :=
  DefiningMapHomotopy.ofGauge X (fun s x => toCLM (R s x))
    (contDiff_toCLM hR)
    (fun x => by rw [hRzero x, toCLM_one])
    (fun s _ x => toCLM_bijective (R s x))


-- @@ L113-119 verbatim
@[simp] theorem homotopy_H (X : FramedLevelSet n)
    (R : ℝ → E → SOGroup n)
    (hR : ∀ i j, ContDiff ℝ ∞
      (fun p : ℝ × E => ((R p.1 p.2 : SOGroup n) : M) i j))
    (hRzero : ∀ x, R 0 x = 1) (s : ℝ) (x : E) :
    (homotopy X R hR hRzero).H s x = toCLM (R s x) (X.g x) :=
  rfl


-- @@ L121-121 verbatim
end SOFrameGauge

-- @@ L122-122 verbatim
end Submission
