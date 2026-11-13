import Mathlib
import Submission.SignedPTEndpoint


-- @@ L4-16 verbatim
/-!
# Endpoint PT cutoffs for arbitrary signed framed level sets

The signed Pontryagin--Thom endpoint construction in `SignedPTEndpoint` starts
from a compactly supported smooth cutoff which is one on the positive part of
the zero fiber and zero on its negative part.  A cutoff induced from an already
given signed cobordism was available, but normalization must start with an
arbitrary signed framed level set.  This file supplies that missing entry point.

The zero fiber is compact.  On it, the weakly positive and weakly negative
pieces are disjoint closed sets because the sign label never vanishes.  Smooth
Urysohn separation therefore produces the required endpoint cutoff.
-/


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
namespace Submission


-- @@ L22-22 verbatim
open Set Function Metric

-- @@ L23-23 verbatim
open scoped Topology RealInnerProductSpace ContDiff


-- @@ L25-25 verbatim
variable {n : ℕ}


-- @@ L27-27 verbatim
namespace FiberSign


-- @@ L29-29 verbatim
variable {X : FramedLevelSet n} (S : FiberSign X)


-- @@ L31-31 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L33-37 verbatim
/-- The closed weakly positive piece of the compact zero fiber.  Weak and
strict positivity agree on the fiber, but the weak form is topologically
closed and is therefore convenient for smooth separation. -/
def nonnegativeFiber : Set E :=
  {x | x ∈ X.fiber ∧ 0 ≤ S x}


-- @@ L39-41 verbatim
/-- The closed weakly negative piece of the compact zero fiber. -/
def nonpositiveFiber : Set E :=
  {x | x ∈ X.fiber ∧ S x ≤ 0}


-- @@ L43-45 verbatim
lemma isClosed_nonnegativeFiber : IsClosed S.nonnegativeFiber := by
  rw [nonnegativeFiber]
  exact X.isClosed_fiber.inter (isClosed_Ici.preimage S.continuous)


-- @@ L47-49 verbatim
lemma isClosed_nonpositiveFiber : IsClosed S.nonpositiveFiber := by
  rw [nonpositiveFiber]
  exact X.isClosed_fiber.inter (isClosed_Iic.preimage S.continuous)


-- @@ L51-53 verbatim
lemma isCompact_nonnegativeFiber : IsCompact S.nonnegativeFiber :=
  X.isCompact_fiber.of_isClosed_subset S.isClosed_nonnegativeFiber
    (fun _ hx => hx.1)


-- @@ L55-57 verbatim
lemma isCompact_nonpositiveFiber : IsCompact S.nonpositiveFiber :=
  X.isCompact_fiber.of_isClosed_subset S.isClosed_nonpositiveFiber
    (fun _ hx => hx.1)


-- @@ L59-63 verbatim
lemma disjoint_nonnegativeFiber_nonpositiveFiber :
    Disjoint S.nonnegativeFiber S.nonpositiveFiber := by
  rw [Set.disjoint_left]
  rintro x ⟨hxfib, hpos⟩ ⟨-, hneg⟩
  exact S.nonzero x hxfib (le_antisymm hneg hpos)


-- @@ L65-65 verbatim
namespace PTCutoff


-- @@ L67-113 verbatim
/-- Every signed framed level set admits a compactly supported smooth endpoint
PT selector.  This is the starting datum for applying the signed PT collapse
to an arbitrary endpoint, independently of any pre-existing cobordism. -/
theorem nonempty : Nonempty (PTCutoff S) := by
  have hopen : IsOpen S.nonpositiveFiberᶜ :=
    S.isClosed_nonpositiveFiber.isOpen_compl
  have hsub : S.nonnegativeFiber ⊆ S.nonpositiveFiberᶜ := by
    intro x hp hn
    exact Set.disjoint_left.mp S.disjoint_nonnegativeFiber_nonpositiveFiber hp hn
  obtain ⟨δ, hδpos, hδsub⟩ :=
    S.isCompact_nonnegativeFiber.exists_cthickening_subset_open hopen hsub
  let U : Set E := Metric.thickening δ S.nonnegativeFiber
  have hKU : S.nonnegativeFiber ⊆ U :=
    Metric.self_subset_thickening hδpos _
  have hUc : IsCompact (closure U) := by
    apply IsCompact.of_isClosed_subset S.isCompact_nonnegativeFiber.cthickening
      isClosed_closure
    exact closure_minimal
      (Metric.thickening_subset_cthickening _ _) Metric.isClosed_cthickening
  have hs : IsClosed Uᶜ := Metric.isOpen_thickening.isClosed_compl
  have hd : Disjoint Uᶜ S.nonnegativeFiber := by
    rw [Set.disjoint_left]
    intro x hxU hxK
    exact hxU (hKU hxK)
  obtain ⟨χ, hχ0, hχ1, hχ01⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed
      (modelWithCornersSelf ℝ E) (n := (⊤ : ℕ∞)) hs
      S.isClosed_nonnegativeFiber hd
  have hχsmooth : ContDiff ℝ ∞ (⇑χ) := by
    rw [← contMDiff_iff_contDiff]
    exact χ.contMDiff
  have hχsupport : HasCompactSupport (⇑χ) := by
    have hsupport : support (⇑χ) ⊆ U := by
      intro x hx
      by_contra hxU
      exact hx (hχ0 hxU)
    have htsupport : tsupport (⇑χ) ⊆ closure U :=
      closure_minimal (hsupport.trans subset_closure) isClosed_closure
    exact IsCompact.of_isClosed_subset hUc isClosed_closure htsupport
  refine ⟨⟨⇑χ, hχsmooth, hχ01, ?_, ?_, hχsupport⟩⟩
  · rintro x ⟨hxfib, hxpos⟩
    exact hχ1 ⟨hxfib, hxpos.le⟩
  · rintro x ⟨hxfib, hxneg⟩
    apply hχ0
    intro hxU
    exact hδsub (Metric.thickening_subset_cthickening _ _ hxU)
      ⟨hxfib, hxneg.le⟩


-- @@ L115-151 verbatim
/-- The north-pole fiber of an arbitrary endpoint PT collapse is exactly the
positively labelled part of the original zero fiber.  Thus the cutoff supplied
by `nonempty` loses no positive component and introduces no spurious one. -/
theorem sphereMap_eq_signedPTNorthPole_iff (κ : PTCutoff S) (x : E) :
    sphereMap S κ x =
        SignedFramedLevelCobordism.SignedSlabCutoff.signedPTNorthPole ↔
      x ∈ S.positivePart := by
  constructor
  · intro hmap
    have hnorm : 0 < ‖raw S κ x‖ :=
      norm_pos_iff.mpr (raw_ne_zero S κ x)
    have hcoe : ‖raw S κ x‖⁻¹ • raw S κ x = eLast n := by
      have := congrArg Subtype.val hmap
      simpa [sphereMap_coe,
        SignedFramedLevelCobordism.SignedSlabCutoff.signedPTNorthPole] using this
    have hraw : raw S κ x = ‖raw S κ x‖ • eLast n := by
      calc
        raw S κ x = ‖raw S κ x‖ •
            (‖raw S κ x‖⁻¹ • raw S κ x) := by
              rw [smul_smul, mul_inv_cancel₀ hnorm.ne', one_smul]
        _ = ‖raw S κ x‖ • eLast n := by rw [hcoe]
    have hlast := congrArg (fun z : E => z (Fin.last n)) hraw
    rw [raw_last] at hlast
    have hlast' : 2 * κ x - 1 = ‖raw S κ x‖ := by
      simpa [PiLp.smul_apply, eLast] using hlast
    have hκpos : 0 < κ x := by linarith
    have hinit := congrArg (initCLM n) hraw
    rw [initCLM_raw, map_smul, initCLM_eLast, smul_zero] at hinit
    have hg : X.g x = 0 :=
      (smul_eq_zero.mp hinit).resolve_left hκpos.ne'
    refine ⟨hg, ?_⟩
    by_contra hSpos
    have hSneg : S x < 0 :=
      lt_of_le_of_ne (le_of_not_gt hSpos) (S.nonzero x hg)
    have hκzero := κ.negative_zero x ⟨hg, hSneg⟩
    linarith
  · exact sphereMap_of_positivePart S κ


-- @@ L153-153 verbatim
/-! ## Exact endpoint framing at the north-pole fiber -/


-- @@ L155-158 verbatim
/-- Horizontal north-pole coordinates of the normalized endpoint collapse. -/
def normalizedHorizontalRaw (κ : PTCutoff S) (x : E) :
    EuclideanSpace ℝ (Fin n) :=
  initCLM n (‖raw S κ x‖⁻¹ • raw S κ x)


-- @@ L160-163 verbatim
lemma normalizedHorizontalRaw_eq (κ : PTCutoff S) (x : E) :
    normalizedHorizontalRaw S κ x =
      (‖raw S κ x‖⁻¹ * κ x) • X.g x := by
  rw [normalizedHorizontalRaw, map_smul, initCLM_raw, smul_smul]


-- @@ L165-189 verbatim
/-- In the north-pole chart, the endpoint PT collapse carries exactly the
original defining-map framing along every positive component. -/
theorem fderiv_normalizedHorizontalRaw_of_positivePart
    (κ : PTCutoff S) {x : E} (hx : x ∈ S.positivePart) :
    fderiv ℝ (normalizedHorizontalRaw S κ) x = fderiv ℝ X.g x := by
  have hfun : normalizedHorizontalRaw S κ = fun q =>
      (‖raw S κ q‖⁻¹ * κ q) • X.g q := by
    funext q
    exact normalizedHorizontalRaw_eq S κ q
  rw [hfun]
  have hraw0 : raw S κ x ≠ 0 := by
    rw [raw_of_positivePart S κ hx]
    exact (norm_ne_zero_iff.mp (by rw [norm_eLast]; norm_num))
  have hrnorm : DifferentiableAt ℝ (fun q => ‖raw S κ q‖) x :=
    (contDiff_raw S κ).differentiable infty_ne_zero |>.differentiableAt |>.norm
      ℝ hraw0
  have hscalar : DifferentiableAt ℝ
      (fun q => ‖raw S κ q‖⁻¹ * κ q) x :=
    (hrnorm.inv (norm_ne_zero_iff.mpr hraw0)).mul
      (κ.smooth.differentiable infty_ne_zero |>.differentiableAt)
  have hGd : DifferentiableAt ℝ X.g x :=
    X.smooth.differentiable infty_ne_zero |>.differentiableAt
  rw [fderiv_fun_smul hscalar hGd, hx.1, raw_of_positivePart S κ hx,
    norm_eLast, κ.positive_one x hx]
  simp


-- @@ L191-195 verbatim
theorem surjective_fderiv_normalizedHorizontalRaw_of_positivePart
    (κ : PTCutoff S) {x : E} (hx : x ∈ S.positivePart) :
    Function.Surjective (fderiv ℝ (normalizedHorizontalRaw S κ) x) := by
  rw [fderiv_normalizedHorizontalRaw_of_positivePart S κ hx]
  exact X.regular x hx.1


-- @@ L197-197 verbatim
end PTCutoff


-- @@ L199-199 verbatim
end FiberSign


-- @@ L201-201 verbatim
end Submission
