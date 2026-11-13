import Mathlib
import Submission.AmbientNormalizationPrimitive


-- @@ L4-19 verbatim
/-!
# Conjugating an ambient isotopy by an accumulated endpoint

Componentwise normalization starts with local moves written in the original
coordinates.  After some components have already been moved, the next local
move must be transported by the endpoint diffeomorphism accumulated so far.
This file supplies that transport for `SmoothAmbientIsotopy`.

If `A` is the accumulated isotopy and `B` is the next move, then

`B.conjugateByEndpoint A = A₁ ∘ Bₛ ∘ A₁⁻¹`.

Consequently a set fixed by `B` is transported to its current image under
`A₁`, and composing `A` with the conjugate applies the original endpoint moves
in their intended order.
-/


-- @@ L21-21 verbatim
set_option autoImplicit false


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open Set Function

-- @@ L26-26 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L28-28 verbatim
namespace Submission

-- @@ L29-29 verbatim
namespace SmoothAmbientIsotopy


-- @@ L31-31 verbatim
variable {n : ℕ}


-- @@ L33-33 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L35-38 verbatim
/-- Forward family `A₁ ∘ Bₛ ∘ A₁⁻¹`. -/
def endpointConjugateForward (B A : SmoothAmbientIsotopy n)
    (s : ℝ) (x : E) : E :=
  A.forward 1 (B.forward s (A.inverse 1 x))


-- @@ L40-43 verbatim
/-- Inverse family `A₁ ∘ Bₛ⁻¹ ∘ A₁⁻¹`. -/
def endpointConjugateInverse (B A : SmoothAmbientIsotopy n)
    (s : ℝ) (x : E) : E :=
  A.forward 1 (B.inverse s (A.inverse 1 x))


-- @@ L45-53 verbatim
theorem contDiff_endpointConjugateForward (B A : SmoothAmbientIsotopy n) :
    ContDiff ℝ ∞ (fun p : ℝ × E =>
      endpointConjugateForward B A p.1 p.2) := by
  have hAinv : ContDiff ℝ ∞ (fun p : ℝ × E => A.inverse 1 p.2) :=
    (A.contDiff_inverse_slice 1).comp contDiff_snd
  have hB : ContDiff ℝ ∞
      (fun p : ℝ × E => B.forward p.1 (A.inverse 1 p.2)) :=
    B.forward_smooth.comp (contDiff_fst.prodMk hAinv)
  exact (A.contDiff_forward_slice 1).comp hB


-- @@ L55-63 verbatim
theorem contDiff_endpointConjugateInverse (B A : SmoothAmbientIsotopy n) :
    ContDiff ℝ ∞ (fun p : ℝ × E =>
      endpointConjugateInverse B A p.1 p.2) := by
  have hAinv : ContDiff ℝ ∞ (fun p : ℝ × E => A.inverse 1 p.2) :=
    (A.contDiff_inverse_slice 1).comp contDiff_snd
  have hB : ContDiff ℝ ∞
      (fun p : ℝ × E => B.inverse p.1 (A.inverse 1 p.2)) :=
    B.inverse_smooth.comp (contDiff_fst.prodMk hAinv)
  exact (A.contDiff_forward_slice 1).comp hB


-- @@ L65-72 verbatim
theorem endpointConjugate_leftInverse (B A : SmoothAmbientIsotopy n)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    LeftInverse (endpointConjugateInverse B A s)
      (endpointConjugateForward B A s) := by
  intro x
  simp only [endpointConjugateInverse, endpointConjugateForward]
  rw [A.left_inv 1 ⟨zero_le_one, le_rfl⟩,
    B.left_inv s hs, A.right_inv 1 ⟨zero_le_one, le_rfl⟩]


-- @@ L74-81 verbatim
theorem endpointConjugate_rightInverse (B A : SmoothAmbientIsotopy n)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    RightInverse (endpointConjugateInverse B A s)
      (endpointConjugateForward B A s) := by
  intro x
  simp only [endpointConjugateInverse, endpointConjugateForward]
  rw [A.left_inv 1 ⟨zero_le_one, le_rfl⟩,
    B.right_inv s hs, A.right_inv 1 ⟨zero_le_one, le_rfl⟩]


-- @@ L83-126 verbatim
/-- Transport a local move by the endpoint diffeomorphism of an accumulated
ambient isotopy. -/
def conjugateByEndpoint (B A : SmoothAmbientIsotopy n) :
    SmoothAmbientIsotopy n where
  forward := endpointConjugateForward B A
  inverse := endpointConjugateInverse B A
  forward_smooth := contDiff_endpointConjugateForward B A
  inverse_smooth := contDiff_endpointConjugateInverse B A
  forward_zero := by
    funext x
    simp only [endpointConjugateForward, B.forward_zero, id_eq]
    exact A.right_inv 1 ⟨zero_le_one, le_rfl⟩ x
  left_inv := endpointConjugate_leftInverse B A
  right_inv := endpointConjugate_rightInverse B A
  inverse_fderiv_surjective := by
    intro s hs x
    let f : E → E := endpointConjugateForward B A s
    let g : E → E := endpointConjugateInverse B A s
    have hf : ContDiff ℝ ∞ f :=
      (contDiff_endpointConjugateForward B A).comp
        (contDiff_const.prodMk contDiff_id)
    have hg : ContDiff ℝ ∞ g :=
      (contDiff_endpointConjugateInverse B A).comp
        (contDiff_const.prodMk contDiff_id)
    let y : E := g x
    have hfy : f y = x := endpointConjugate_rightInverse B A s hs x
    have hgf : (fun z => g (f z)) = id := by
      funext z
      exact endpointConjugate_leftInverse B A s hs z
    have hcomp : HasFDerivAt (fun z => g (f z))
        ((fderiv ℝ g (f y)).comp (fderiv ℝ f y)) y :=
      ((hg.differentiable (by simp) (f y)).hasFDerivAt.comp y
        (hf.differentiable (by simp) y).hasFDerivAt)
    rw [hgf] at hcomp
    have hderiv0 : (fderiv ℝ g (f y)).comp (fderiv ℝ f y) =
        ContinuousLinearMap.id ℝ E :=
      hcomp.fderiv.symm.trans (hasFDerivAt_id y).fderiv
    have hderiv : (fderiv ℝ g x).comp (fderiv ℝ f y) =
        ContinuousLinearMap.id ℝ E := by
      rwa [hfy] at hderiv0
    intro z
    refine ⟨fderiv ℝ f y z, ?_⟩
    have hz := congrArg (fun M : E →L[ℝ] E => M z) hderiv
    simpa [ContinuousLinearMap.comp_apply] using hz


-- @@ L128-132 verbatim
@[simp] theorem conjugateByEndpoint_forward (B A : SmoothAmbientIsotopy n)
    (s : ℝ) (x : E) :
    (B.conjugateByEndpoint A).forward s x =
      A.forward 1 (B.forward s (A.inverse 1 x)) :=
  rfl


-- @@ L134-138 verbatim
@[simp] theorem conjugateByEndpoint_inverse (B A : SmoothAmbientIsotopy n)
    (s : ℝ) (x : E) :
    (B.conjugateByEndpoint A).inverse s x =
      A.forward 1 (B.inverse s (A.inverse 1 x)) :=
  rfl


-- @@ L140-147 verbatim
/-- On the current image of an original point, endpoint conjugation is the
literal transported original move. -/
theorem conjugateByEndpoint_forward_endpoint_image
    (B A : SmoothAmbientIsotopy n) (s : ℝ) (x : E) :
    (B.conjugateByEndpoint A).forward s (A.forward 1 x) =
      A.forward 1 (B.forward s x) := by
  rw [conjugateByEndpoint_forward,
    A.left_inv 1 ⟨zero_le_one, le_rfl⟩]


-- @@ L149-155 verbatim
/-- A relative fixed set is transported to its current endpoint image. -/
theorem FixedOn.conjugateByEndpoint {B A : SmoothAmbientIsotopy n}
    {K : Set E} (hB : B.FixedOn K) :
    (B.conjugateByEndpoint A).FixedOn (A.forward 1 '' K) := by
  intro s hs x hx
  obtain ⟨y, hyK, rfl⟩ := hx
  rw [conjugateByEndpoint_forward_endpoint_image, hB s hs y hyK]


-- @@ L157-170 verbatim
/-- Endpoint conjugation transports the image of every set by the accumulated
endpoint map. -/
theorem conjugateByEndpoint_forward_image (B A : SmoothAmbientIsotopy n)
    (s : ℝ) (K : Set E) :
    (B.conjugateByEndpoint A).forward s '' (A.forward 1 '' K) =
      A.forward 1 '' (B.forward s '' K) := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hyK, rfl⟩, rfl⟩
    exact ⟨B.forward s y, ⟨y, hyK, rfl⟩,
      (conjugateByEndpoint_forward_endpoint_image B A s y).symm⟩
  · rintro ⟨_, ⟨y, hyK, rfl⟩, rfl⟩
    exact ⟨A.forward 1 y, ⟨y, hyK, rfl⟩,
      conjugateByEndpoint_forward_endpoint_image B A s y⟩


-- @@ L172-179 verbatim
/-- Composing the accumulated move with the transported next move applies the
two original endpoint maps in order. -/
theorem followedBy_conjugateByEndpoint_forward_one
    (A B : SmoothAmbientIsotopy n) (x : E) :
    (A.followedBy (B.conjugateByEndpoint A)).forward 1 x =
      A.forward 1 (B.forward 1 x) := by
  rw [followedBy_forward,
    conjugateByEndpoint_forward_endpoint_image]


-- @@ L181-181 verbatim
end SmoothAmbientIsotopy

-- @@ L182-182 verbatim
end Submission
