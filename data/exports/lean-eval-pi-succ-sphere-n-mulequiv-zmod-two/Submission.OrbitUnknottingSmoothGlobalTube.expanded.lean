import Mathlib
import Submission.OrbitUnknottingSmoothTubeInverse


-- @@ L4-16 verbatim
/-!
# A globally injective smooth tube inverse

The derivative of the lifted orbit tube is invertible on its zero section.
Invertibility is open, the derivative varies continuously, and the phase is
period one.  Compactness of one phase interval therefore gives a single
positive normal radius on which every derivative is invertible.

After intersecting this radius with the globally injective quotient-tube
radius, we construct one inverse on the entire tube image.  Since `AddCircle`
is used here only as a topological quotient, smoothness of that inverse is
recorded by compatible smooth real-phase lifts around every tube point.
-/


-- @@ L18-18 verbatim
set_option autoImplicit false

-- @@ L19-19 verbatim
set_option maxHeartbeats 800000


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
open Set Function

-- @@ L24-24 verbatim
open scoped Topology ContDiff


-- @@ L26-26 verbatim
namespace Submission

-- @@ L27-27 verbatim
namespace TamedField


-- @@ L29-29 verbatim
variable {n : ℕ} {X : FramedLevelSet n} (V : TamedField X)


-- @@ L31-31 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L32-32 verbatim
local notation "N" => EuclideanSpace ℝ (Fin n)

-- @@ L33-33 verbatim
local notation "C" => AddCircle (1 : ℝ)


-- @@ L35-52 verbatim
/-- The derivative of the lifted tube is itself period one in the phase
coordinate. -/
theorem periodic_fderiv_orbitTubeLift (O : V.OrbitIndex) :
    Function.Periodic
      (fun q : ℝ × N => fderiv ℝ (V.orbitTubeLift O) q)
      ((1 : ℝ), (0 : N)) := by
  have hfun :
      (fun q : ℝ × N =>
        V.orbitTubeLift O (q + ((1 : ℝ), (0 : N)))) =
      V.orbitTubeLift O := by
    funext q
    rcases q with ⟨u, z⟩
    simpa only [Prod.mk_add_mk, add_zero] using
      V.periodic_orbitTubeLift O z u
  intro q
  have h := congrArg
    (fun f : (ℝ × N) → E => fderiv ℝ f q) hfun
  simpa only [fderiv_comp_add_right] using h


-- @@ L54-62 verbatim
/-- The set of lifted tube points with invertible derivative is open. -/
theorem isOpen_orbitTubeLift_regularSet (O : V.OrbitIndex) :
    IsOpen
      ((fderiv ℝ (V.orbitTubeLift O)) ⁻¹'
        Set.range
          ((↑) : ((ℝ × N) ≃L[ℝ] E) →
            ((ℝ × N) →L[ℝ] E))) := by
  exact ContinuousLinearEquiv.isOpen.preimage
    ((V.contDiff_orbitTubeLift O).continuous_fderiv (by simp))


-- @@ L64-73 verbatim
/-- Every point of the zero section has invertible derivative. -/
theorem orbitTubeLift_zero_mem_regularSet (O : V.OrbitIndex) (u : ℝ) :
    (u, (0 : N)) ∈
      (fderiv ℝ (V.orbitTubeLift O)) ⁻¹'
        Set.range
          ((↑) : ((ℝ × N) ≃L[ℝ] E) →
            ((ℝ × N) →L[ℝ] E)) := by
  refine ⟨V.orbitTubeDerivEquiv O u, ?_⟩
  rw [V.orbitTubeDerivEquiv_coe O u]
  exact (V.hasFDerivAt_orbitTubeLift_zero O u).fderiv.symm


-- @@ L75-131 verbatim
/-- Periodic compactness upgrades zero-section invertibility to one uniform
positive normal radius. -/
theorem exists_orbitTubeLift_uniform_deriv_equiv (O : V.OrbitIndex) :
    ∃ r > 0, ∀ (u : ℝ) (z : N), z ∈ Metric.ball (0 : N) r →
      ∃ e : (ℝ × N) ≃L[ℝ] E,
        (e : (ℝ × N) →L[ℝ] E) =
          fderiv ℝ (V.orbitTubeLift O) (u, z) := by
  let A := Set.Icc (0 : ℝ) 1
  let R : Set (ℝ × N) :=
    (fderiv ℝ (V.orbitTubeLift O)) ⁻¹'
      Set.range
        ((↑) : ((ℝ × N) ≃L[ℝ] E) →
          ((ℝ × N) →L[ℝ] E))
  let j : A × N → ℝ × N := fun q => (q.1.1, q.2)
  let T : Set (A × N) := j ⁻¹' R
  have hAcompact : IsCompact A := isCompact_Icc
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hAcompact
  have hj : Continuous j :=
    continuous_subtype_val.comp continuous_fst |>.prodMk continuous_snd
  have hTopen : IsOpen T := by
    exact (V.isOpen_orbitTubeLift_regularSet O).preimage hj
  have hzero :
      (Set.univ : Set A) ×ˢ ({0} : Set N) ⊆ T := by
    rintro ⟨a, z⟩ ⟨-, hz⟩
    rw [Set.mem_singleton_iff] at hz
    change z = 0 at hz
    subst z
    exact V.orbitTubeLift_zero_mem_regularSet O a.1
  obtain ⟨U, W, hUopen, hWopen, hAU, hzeroW, hUWT⟩ :=
    generalized_tube_lemma (X := A) (Y := N)
      isCompact_univ isCompact_singleton hTopen hzero
  have hzero_mem_W : (0 : N) ∈ W := hzeroW (Set.mem_singleton 0)
  rcases (Metric.isOpen_iff.mp hWopen) 0 hzero_mem_W with
    ⟨r, hr, hrW⟩
  refine ⟨r, hr, ?_⟩
  intro u z hz
  let a : A := ⟨Int.fract u,
    Int.fract_nonneg u, (Int.fract_lt_one u).le⟩
  have hregFract : (Int.fract u, z) ∈ R := by
    have ht : (a, z) ∈ T :=
      hUWT ⟨hAU (Set.mem_univ a), hrW hz⟩
    exact ht
  have hperiod := (V.periodic_fderiv_orbitTubeLift O).zsmul ⌊u⌋
  have heq :
      fderiv ℝ (V.orbitTubeLift O) (u, z) =
        fderiv ℝ (V.orbitTubeLift O) (Int.fract u, z) := by
    have h := hperiod (Int.fract u, z)
    have hpoint :
        (Int.fract u, z) + ⌊u⌋ • ((1 : ℝ), (0 : N)) =
          (u, z) := by
      ext
      · simpa [add_comm] using Int.fract_add_floor u
      · simp
    rw [hpoint] at h
    exact h
  rw [heq]
  exact hregFract


-- @@ L133-161 verbatim
/-- A single inverse on a full quotient tube, together with smooth real-phase
local lifts at every point.  The last field says that the globally defined
quotient inverse is locally represented, along the tube image, by an honest
smooth map into `ℝ × ℝⁿ`. -/
structure OrbitTubeGlobalSmoothInverse (O : V.OrbitIndex) where
  radius : ℝ
  radius_pos : 0 < radius
  inverse : E → C × N
  injOn : Set.InjOn (V.orbitTube O)
    ((Set.univ : Set C) ×ˢ Metric.ball (0 : N) radius)
  embedding : Topology.IsEmbedding
    (fun q : ↥((Set.univ : Set C) ×ˢ Metric.ball (0 : N) radius) =>
      V.orbitTube O q.1)
  inverse_left : ∀ q ∈
      ((Set.univ : Set C) ×ˢ Metric.ball (0 : N) radius),
    inverse (V.orbitTube O q) = q
  local_smooth_lift : ∀ (u : ℝ) (z : N),
      z ∈ Metric.ball (0 : N) radius →
    ∃ e : (ℝ × N) ≃L[ℝ] E, ∃ g : E → ℝ × N,
      HasFDerivAt (V.orbitTubeLift O)
          (e : (ℝ × N) →L[ℝ] E) (u, z) ∧
      ContDiffAt ℝ ∞ g (V.orbitTubeLift O (u, z)) ∧
      HasFDerivAt g (e.symm : E →L[ℝ] (ℝ × N))
          (V.orbitTubeLift O (u, z)) ∧
      g (V.orbitTubeLift O (u, z)) = (u, z) ∧
      ∀ᶠ p in 𝓝 (u, z),
        inverse (V.orbitTubeLift O p) =
          (((g (V.orbitTubeLift O p)).1 : C),
            (g (V.orbitTubeLift O p)).2)


-- @@ L163-267 verbatim
/-- The uniform derivative radius and the global topological embedding radius
can be chosen simultaneously, producing a globally injective tube whose
inverse has smooth local lifts everywhere. -/
theorem nonempty_orbitTubeGlobalSmoothInverse (O : V.OrbitIndex) :
    Nonempty (V.OrbitTubeGlobalSmoothInverse O) := by
  obtain ⟨R, hR, hRinj, hRemb⟩ := V.exists_orbitTube_global_embedding O
  obtain ⟨S, hS, hSderiv⟩ :=
    V.exists_orbitTubeLift_uniform_deriv_equiv O
  let r : ℝ := min R S
  have hr : 0 < r := lt_min hR hS
  have hrR : r ≤ R := min_le_left R S
  have hrS : r ≤ S := min_le_right R S
  let D : Set (C × N) :=
    (Set.univ : Set C) ×ˢ Metric.ball (0 : N) r
  let DR : Set (C × N) :=
    (Set.univ : Set C) ×ˢ Metric.ball (0 : N) R
  have hDR : D ⊆ DR := by
    exact prod_mono Subset.rfl (Metric.ball_subset_ball hrR)
  have hinj : Set.InjOn (V.orbitTube O) D :=
    hRinj.mono hDR
  have hemb : Topology.IsEmbedding
      (fun q : D => V.orbitTube O q.1) := by
    simpa [Function.comp_def, Set.inclusion, D, DR] using
      hRemb.comp (Topology.IsEmbedding.inclusion hDR)
  have hzeroD : ((0 : C), (0 : N)) ∈ D := by
    exact ⟨Set.mem_univ _, Metric.mem_ball_self hr⟩
  let qzero : D := ⟨((0 : C), (0 : N)), hzeroD⟩
  letI : Nonempty D := ⟨qzero⟩
  let tube : D → E := fun q => V.orbitTube O q.1
  have htube_inj : Function.Injective tube := by
    intro p q hpq
    apply Subtype.ext
    exact hinj p.property q.property hpq
  let invTube : E → D := Function.invFun tube
  let inverse : E → C × N := fun y => (invTube y).1
  have hinverse_left : ∀ q ∈ D,
      inverse (V.orbitTube O q) = q := by
    intro q hq
    let qs : D := ⟨q, hq⟩
    have hi : invTube (tube qs) = qs := by
      exact Function.leftInverse_invFun htube_inj qs
    exact congrArg Subtype.val hi
  refine ⟨{
    radius := r
    radius_pos := hr
    inverse := inverse
    injOn := hinj
    embedding := hemb
    inverse_left := hinverse_left
    local_smooth_lift := ?_
  }⟩
  intro u z hz
  have hzS : z ∈ Metric.ball (0 : N) S :=
    Metric.ball_subset_ball hrS hz
  obtain ⟨e, he⟩ := hSderiv u z hzS
  have hf : HasFDerivAt (V.orbitTubeLift O)
      (e : (ℝ × N) →L[ℝ] E) (u, z) := by
    have hf' := (V.contDiff_orbitTubeLift O).differentiable
      (by simp) (u, z) |>.hasFDerivAt
    rw [he]
    exact hf'
  let chart : OpenPartialHomeomorph (ℝ × N) E :=
    (V.contDiff_orbitTubeLift O).contDiffAt.toOpenPartialHomeomorph
      (V.orbitTubeLift O) hf (by simp)
  let g : E → ℝ × N := chart.symm
  have hsource : (u, z) ∈ chart.source := by
    exact (V.contDiff_orbitTubeLift O).contDiffAt
      |>.mem_toOpenPartialHomeomorph_source hf (by simp)
  have htarget : V.orbitTubeLift O (u, z) ∈ chart.target :=
    chart.map_source hsource
  have hgcenter : g (V.orbitTubeLift O (u, z)) = (u, z) := by
    change chart.symm (V.orbitTubeLift O (u, z)) = (u, z)
    rw [← show (chart : (ℝ × N) → E) = V.orbitTubeLift O by rfl]
    exact chart.left_inv hsource
  have hforwardDeriv : HasFDerivAt chart
      (e : (ℝ × N) →L[ℝ] E)
      (chart.symm (V.orbitTubeLift O (u, z))) := by
    rw [show chart.symm (V.orbitTubeLift O (u, z)) = (u, z) by
      exact hgcenter]
    exact hf
  have hforwardSmooth : ContDiffAt ℝ ∞ chart
      (chart.symm (V.orbitTubeLift O (u, z))) := by
    rw [show chart.symm (V.orbitTubeLift O (u, z)) = (u, z) by
      exact hgcenter]
    exact (V.contDiff_orbitTubeLift O).contDiffAt
  have hgsmooth : ContDiffAt ℝ ∞ g
      (V.orbitTubeLift O (u, z)) := by
    exact chart.contDiffAt_symm htarget hforwardDeriv hforwardSmooth
  have hgderiv : HasFDerivAt g
      (e.symm : E →L[ℝ] (ℝ × N))
      (V.orbitTubeLift O (u, z)) := by
    exact chart.hasFDerivAt_symm htarget hforwardDeriv
  have hlocal : ∀ᶠ p in 𝓝 (u, z),
      g (V.orbitTubeLift O p) = p := by
    exact chart.eventually_left_inverse hsource
  have hball : ∀ᶠ p in 𝓝 (u, z),
      p.2 ∈ Metric.ball (0 : N) r := by
    exact continuous_snd.continuousAt.preimage_mem_nhds
      (Metric.isOpen_ball.mem_nhds hz)
  refine ⟨e, g, hf, hgsmooth, hgderiv, hgcenter, ?_⟩
  filter_upwards [hlocal, hball] with p hp hpr
  have hglobal := hinverse_left (((p.1 : ℝ) : C), p.2)
    ⟨Set.mem_univ _, hpr⟩
  rw [V.orbitTube_coe O p.1 p.2] at hglobal
  simpa [hp] using hglobal


-- @@ L269-273 verbatim
/-- A fixed globally smooth tube inverse, chosen once for downstream
tube-coordinate constructions. -/
def globalSmoothOrbitTube (O : V.OrbitIndex) :
    V.OrbitTubeGlobalSmoothInverse O :=
  Classical.choice (V.nonempty_orbitTubeGlobalSmoothInverse O)


-- @@ L275-282 verbatim
/-- The chosen global inverse really is a left inverse on its whole tube
domain. -/
@[simp] theorem globalSmoothOrbitTube_inverse_apply
    (O : V.OrbitIndex) (q : C × N)
    (hq : q ∈ (Set.univ : Set C) ×ˢ
      Metric.ball (0 : N) (V.globalSmoothOrbitTube O).radius) :
    (V.globalSmoothOrbitTube O).inverse (V.orbitTube O q) = q :=
  (V.globalSmoothOrbitTube O).inverse_left q hq


-- @@ L284-284 verbatim
end TamedField

-- @@ L285-285 verbatim
end Submission
