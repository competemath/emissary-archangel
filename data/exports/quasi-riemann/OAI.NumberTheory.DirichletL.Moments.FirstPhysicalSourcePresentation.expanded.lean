import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindowEnergy


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentFirstPhysicalSource

-- @@ L9-9 verbatim
open ActualEisensteinCubic ConcreteTraceCRT HeckeFamily CanonicalQuadraticSieve

-- @@ L10-10 verbatim
open CenteredMomentSecondHeightFamily CenteredMomentCanonicalFirst

-- @@ L11-11 verbatim
open CenteredMomentFirstCanonicalFamily

-- @@ L12-12 verbatim
local notation "O"=>ActualEisensteinCubic.O


-- @@ L14-15 verbatim
def fixedPresentationCost : ℝ:=
  (Ideal.absNorm (Ideal.span {fixedBadMask}):ℝ)*Ideal.absNorm (Ideal.span {(72:O)})


-- @@ L17-22 verbatim
theorem fixedPresentationCost_pos : 0<fixedPresentationCost:=by
  apply mul_pos
  · exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (by simpa only [Ideal.span_singleton_eq_bot] using fixedBadMask_ne_zero))
  · exact_mod_cast Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (by simp))


-- @@ L24-32 verbatim
theorem fixed_presentation_norm (η τ:Character)(C D:Ideal O)(E:Finset (CommonIndex C D))
    (hM:τ.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    (τ.modulus.absNorm:ℝ)=fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2:=by
  rw [hM,←Ideal.span_singleton_mul_span_singleton]
  simp only [map_mul,Nat.cast_mul,eisEmbedding_norm_sq_eq_absNorm_span,fixedPresentationCost]
  ring


-- @@ L34-46 verbatim
theorem fixed_pair_presentation_caps (η τ₁ τ₂:Character)(C D:Ideal O)
    (E:Finset (CommonIndex C D))
    (hM₁:τ₁.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D})
    (hM₂:τ₂.modulus=η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E*activeConductor C D}):
    (τ₁.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2 ∧
    (τ₂.modulus.absNorm:ℝ)≤fixedPresentationCost*(η.modulus.absNorm:ℝ)*
      ‖eisEmbedding (primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E)‖^2*
      ‖eisEmbedding (activeConductor C D)‖^2:=
  ⟨(fixed_presentation_norm η τ₁ C D E hM₁).le,(fixed_presentation_norm η τ₂ C D E hM₂).le⟩


-- @@ L48-48 verbatim
end SevenEighths.CenteredMomentFirstPhysicalSource


-- @@ L50-50 verbatim
end


-- @@ L52-52 verbatim
end OAI
