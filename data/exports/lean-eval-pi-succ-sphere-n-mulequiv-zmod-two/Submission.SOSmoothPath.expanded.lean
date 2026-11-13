import Mathlib
import Submission.NormalizeMoves
import Submission.SOPositiveDetApproximation
import Submission.SOStable
import Submission.SOFrameGauge


-- @@ L7-17 verbatim
/-!
# Smooth paths from the identity in the special orthogonal group

`SO(n)` is path connected, but the path supplied by the topological instance
is only continuous.  Frame gauges require a jointly smooth time parameter.
This file flattens an arbitrary continuous path near its endpoints with
`normRamp`, then applies the existing relative smoothing theorem inside
`SO(n)`.  The result is an everywhere smooth real-parameter family which is
exactly the identity at time zero and exactly the prescribed matrix at time
one.
-/


-- @@ L19-19 verbatim
set_option autoImplicit false


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
open Set Function

-- @@ L24-24 verbatim
open scoped Topology ContDiff unitInterval RealInnerProductSpace


-- @@ L26-26 verbatim
namespace Submission


-- @@ L28-35 verbatim
/-- A coordinatewise smooth real-parameter path in `SO(n)` from the identity
to a prescribed endpoint. -/
structure SmoothSOPath {n : ℕ} (A : SOGroup n) where
  Q : ℝ → SOGroup n
  smooth : ∀ i j, ContDiff ℝ ∞ fun s =>
    ((Q s : SOGroup n) : Matrix (Fin n) (Fin n) ℝ) i j
  zero : Q 0 = 1
  one : Q 1 = A


-- @@ L37-37 verbatim
namespace SmoothSOPath


-- @@ L39-39 verbatim
variable {n : ℕ}


-- @@ L41-112 verbatim
/-- Every special-orthogonal matrix in positive dimension admits a smooth
path from the identity.  Endpoint equality is preserved exactly by relative
smoothing. -/
theorem nonempty (hn : 0 < n) (A : SOGroup n) :
    Nonempty (SmoothSOPath A) := by
  let p : Path (1 : SOGroup n) A := PathConnectedSpace.somePath 1 A
  let r : ℝ → I := fun s =>
    ⟨normRamp s, normRamp_nonneg s, normRamp_le_one s⟩
  have hr : Continuous r :=
    Continuous.subtype_mk contDiff_normRamp.continuous _
  let R : ℝ → SOGroup n := fun s => p (r s)
  have hR : Continuous R := p.continuous.comp hr
  have hRzero : R 0 = 1 := by
    change p (r 0) = 1
    have h0 : normRamp 0 = 0 := normRamp_of_le_quarter (by norm_num)
    have hr0 : r 0 = 0 := Subtype.ext h0
    rw [hr0]
    exact p.source
  have hRone : R 1 = A := by
    change p (r 1) = A
    have h1 : normRamp 1 = 1 :=
      normRamp_of_three_quarter_le (by norm_num)
    have hr1 : r 1 = 1 := Subtype.ext h1
    rw [hr1]
    exact p.target
  let S : Set ℝ := {0, 1}
  let U : Set ℝ := Iio (1 / 4) ∪ Ioi (3 / 4)
  have hS : IsClosed S := by
    exact isClosed_singleton.union isClosed_singleton
  have hUopen : IsOpen U := isOpen_Iio.union isOpen_Ioi
  have hSU : S ⊆ U := by
    intro s hs
    rcases hs with (rfl | hs)
    · exact Or.inl (by norm_num)
    · have hs1 : s = 1 := by simpa using hs
      subst s
      exact Or.inr (by norm_num)
  have hU : U ∈ nhdsSet S := hUopen.mem_nhdsSet.mpr hSU
  let f : ℝ → EuclideanSpace ℝ (Fin n × Fin n) := fun s =>
    matrixToEuclidean
      ((R s : SOGroup n) : Matrix (Fin n) (Fin n) ℝ)
  have hfleft : ContDiffOn ℝ ∞ f (Iio (1 / 4)) := by
    let c : EuclideanSpace ℝ (Fin n × Fin n) :=
      matrixToEuclidean ((1 : SOGroup n) : Matrix (Fin n) (Fin n) ℝ)
    apply (contDiff_const (c := c)).contDiffOn.congr
    intro s hs
    have hramps : normRamp s = 0 :=
      normRamp_of_le_quarter hs.le
    have hrs : r s = 0 := Subtype.ext hramps
    change f s = c
    simp only [f, R]
    rw [hrs, p.source]
  have hfright : ContDiffOn ℝ ∞ f (Ioi (3 / 4)) := by
    let c : EuclideanSpace ℝ (Fin n × Fin n) :=
      matrixToEuclidean ((A : SOGroup n) : Matrix (Fin n) (Fin n) ℝ)
    apply (contDiff_const (c := c)).contDiffOn.congr
    intro s hs
    have hramps : normRamp s = 1 :=
      normRamp_of_three_quarter_le hs.le
    have hrs : r s = 1 := Subtype.ext hramps
    change f s = c
    simp only [f, R]
    rw [hrs, p.target]
  have hfU : ContDiffOn ℝ ∞ f U :=
    hfleft.union_of_isOpen hfright isOpen_Iio isOpen_Ioi
  obtain ⟨Q, hQ, hQS⟩ :=
    exists_contDiff_SO_approx_and_eqOn hn hR hS hU hfU
  have hQzero : Q 0 = 1 := by
    rw [hQS (by simp [S]), hRzero]
  have hQone : Q 1 = A := by
    rw [hQS (by simp [S]), hRone]
  exact ⟨⟨Q, hQ, hQzero, hQone⟩⟩


-- @@ L114-114 verbatim
/-! ## Constant spatial gauges -/


-- @@ L116-116 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L118-121 verbatim
/-- Regard a smooth path in `SO(n)` as a spatially constant gauge. -/
def spatialGauge {A : SOGroup n} (D : SmoothSOPath A)
    (s : ℝ) (_x : E) : SOGroup n :=
  D.Q s


-- @@ L123-128 verbatim
theorem spatialGauge_smooth {A : SOGroup n} (D : SmoothSOPath A) :
    ∀ i j, ContDiff ℝ ∞ fun p : ℝ × E =>
      ((D.spatialGauge p.1 p.2 : SOGroup n) :
        Matrix (Fin n) (Fin n) ℝ) i j := by
  intro i j
  exact (D.smooth i j).comp contDiff_fst


-- @@ L130-133 verbatim
@[simp] theorem spatialGauge_zero {A : SOGroup n}
    (D : SmoothSOPath A) (x : E) :
    D.spatialGauge 0 x = 1 :=
  D.zero


-- @@ L135-138 verbatim
@[simp] theorem spatialGauge_one {A : SOGroup n}
    (D : SmoothSOPath A) (x : E) :
    D.spatialGauge 1 x = A :=
  D.one


-- @@ L140-153 verbatim
/-- The common-fiber defining-map homotopy induced by a constant smooth
special-orthogonal gauge. -/
def definingMapHomotopy {A : SOGroup n} (D : SmoothSOPath A)
    (X : FramedLevelSet n) :
    DefiningMapHomotopy X
      (X.gaugeTransform
        (fun x => SOFrameGauge.toCLM (D.spatialGauge 1 x))
        (SOFrameGauge.contDiff_toCLM
          (fun i j => (D.spatialGauge_smooth i j).comp
            (contDiff_const.prodMk contDiff_id)))
        (fun x => SOFrameGauge.toCLM_bijective
          (D.spatialGauge 1 x))) :=
  SOFrameGauge.homotopy X D.spatialGauge D.spatialGauge_smooth
    D.spatialGauge_zero


-- @@ L155-161 verbatim
/-- A smooth `SO(n)` path gives an actual signed framed cobordism; no
topological path witness remains in the result. -/
def signedCobordism {A : SOGroup n} (D : SmoothSOPath A)
    {X : FramedLevelSet n} (S : FiberSign X) :
    SignedFramedLevelCobordism S
      (S.restrict (D.definingMapHomotopy X).fiber_subset) :=
  (D.definingMapHomotopy X).signedCobordism S


-- @@ L163-163 verbatim
end SmoothSOPath

-- @@ L164-164 verbatim
end Submission
