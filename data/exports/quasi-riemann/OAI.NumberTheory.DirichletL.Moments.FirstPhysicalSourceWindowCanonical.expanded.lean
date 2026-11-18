import OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceWindowColumns


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators ContDiff

-- @@ L7-7 verbatim
open MeasureTheory


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentFirstPhysicalSource

-- @@ L10-10 verbatim
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve

-- @@ L11-11 verbatim
open CenteredMomentSourceRow CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors

-- @@ L12-12 verbatim
open CenteredMomentGaussEnergy CenteredMomentSmooth CenteredMomentHeckeColumnWindow

-- @@ L13-13 verbatim
open CenteredMomentSecondSectorColumns CenteredMomentConjugateWindow

-- @@ L14-14 verbatim
open CenteredMomentSecondHeightFamily CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum

-- @@ L15-15 verbatim
open CenteredMomentFirstColumns CenteredMomentChildAssembly CenteredMomentCanonicalFirst

-- @@ L16-16 verbatim
open CenteredMomentFirstCanonicalFamily CenteredMomentCommonSupport RayFourExpansion IdealMobiusDivisorSum

-- @@ L17-17 verbatim
open FourierBridge

-- @@ L18-18 verbatim
local notation "O"=>ActualEisensteinCubic.O

-- @@ L19-19 verbatim
variable {ι:Type*}[Fintype ι]

-- @@ L20-20 verbatim
local instance firstWindowCanonicalDecidableEq : DecidableEq (ι⊕Fin 2):=Classical.decEq _


-- @@ L22-31 verbatim
def leftWindowChild (s:OriginalData ι)(η:Character)(m:O)(t:ℝ)
    (C D:Ideal O)(hC:Supported C)(E:Finset (CommonIndex C D))
    (χ:RayCharacter)(L:Ideal O)(θ X:ℝ)(V:ℝ→ℂ)(z:O):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let r:=activeConductor C D
  let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
  gaussPolynomial Finset.univ (element C C hC.1 s.columns) (element_supported C C hC.1 s.columns)
    (fun I=>divisorCoefficient L (element C C hC.1 s.columns)
      (fun a=>coefficient η m 1 t s.beta C a*leftCoefficient e r ρ (element C C hC.1 s.columns a)) χ I*
      columnPhase V (Real.log (‖eisEmbedding (element C C hC.1 s.columns I)‖^2/X)) θ) z


-- @@ L33-42 verbatim
def rightWindowChild (s:OriginalData ι)(η:Character)(m:O)(t:ℝ)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(E:Finset (CommonIndex C D))
    (χ:RayCharacter)(L:Ideal O)(θ X:ℝ)(V:ℝ→ℂ)(z:O):ℂ:=
  let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E
  let r:=activeConductor C D
  let ρ:=finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
  gaussPolynomial Finset.univ (element C D hD.1 s.columns) (element_supported C D hD.1 s.columns)
    (fun I=>divisorCoefficient L (element C D hD.1 s.columns)
      (fun a=>coefficient η m 1 t s.beta D a*rightCoefficient e r ρ (element C D hD.1 s.columns a)) χ I*
      star (columnPhase V (Real.log (‖eisEmbedding (element C D hD.1 s.columns I)‖^2/X)) θ)) z


-- @@ L44-70 verbatim
theorem actual_canonical_window_integrals (η:Character)(m:O)(hm:m≠0)
    (hmLam:goodLambda∣m)(hm2:(2:O)∣m)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)(hCD:primeSupport C=primeSupport D)
    (E:Finset (CommonIndex C D))(ξ₁ ξ₂:RayCharacter):
    let e:=primeSubsetGenerator (fun P:CommonIndex C D=>P.val) E;
    let M:=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*Ideal.span {e*activeConductor C D};
    ∃τ₁ τ₂:Character,τ₁.modulus=M ∧ τ₂.modulus=M ∧
      ∀s:OriginalData ι,(∀i,∀I∈s.S i,I≠0)→(∀i,∀I∈s.S (Sum.inl i),Prime I)→
      s.s∣C→s.s∣D→∀t T θ X Y:ℝ,0<X→0<Y→
      ∀V₁:ℝ→ℂ,∀hV₁c:HasCompactSupport V₁,∀hV₁s:ContDiff ℝ ∞ V₁,
      ∀V₂:ℝ→ℂ,∀hV₂c:HasCompactSupport V₂,∀hV₂s:ContDiff ℝ ∞ V₂,
      ∀L:Ideal O,∀z:O,
        (Real.sqrt T:ℂ)⁻¹*leftWindowChild s η m t C D hC E ξ₁ L θ X V₁ z=
          (∫w:ℝ,columnDensity V₁ hV₁c hV₁s w*logPhase (θ-w) (Real.log X)*
            allocatedPolynomial s C L τ₁ (t+2*Real.pi*(w-θ)) T z) ∧
        (Real.sqrt T:ℂ)⁻¹*rightWindowChild s η m t C D hC hD E ξ₂ L θ Y V₂ (-z)=
          (∫w:ℝ,columnDensity (fun x=>star (V₂ x)) (conjugate_compact V₂ hV₂c)
            (conjugate_smooth V₂ hV₂s) w*logPhase (-θ-w) (Real.log Y)*
            allocatedPolynomial s D L τ₂ (t+2*Real.pi*(w-(-θ))) T (-z)):=by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩:=actual_child_family η m hm hmLam hm2 C D hC hD E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,?_⟩
  intro s hS hp hsC hsD t T θ X Y hX hY V₁ hV₁c hV₁s V₂ hV₂c hV₂s L z
  constructor
  · exact column_window_original_integral s hS hp C C hC.1 hC rfl hsC τ₁ t T θ X hX
      V₁ hV₁c hV₁s L _ (h₁ s.columns s.beta t L) z
  · exact column_star_window_original_integral s hS hp C D hC.1 hD hCD hsD τ₂ t T θ Y hY
      V₂ hV₂c hV₂s L _ (h₂ s.columns s.beta t L) z


-- @@ L72-72 verbatim
end SevenEighths.CenteredMomentFirstPhysicalSource


-- @@ L74-74 verbatim
end


-- @@ L76-76 verbatim
end OAI
