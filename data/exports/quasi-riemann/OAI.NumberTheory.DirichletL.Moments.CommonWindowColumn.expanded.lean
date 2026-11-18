import OAI.NumberTheory.DirichletL.Moments.ExceptionalWholeWindow
import OAI.NumberTheory.DirichletL.Moments.CommonPairedSource
import OAI.NumberTheory.DirichletL.Moments.CommonHeightEnvelope


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped Classical BigOperators SchwartzMap ContDiff

-- @@ L9-9 verbatim
open MeasureTheory


-- @@ L11-11 verbatim
namespace SevenEighths.CenteredMomentCommonWindowColumn

-- @@ L12-12 verbatim
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData

-- @@ L13-13 verbatim
open CenteredMomentCommonHeightEnvelope CenteredMomentCommonPairedSource

-- @@ L14-14 verbatim
open CenteredMomentCommonLinearSource CenteredMomentExceptionalAmplitudePair

-- @@ L15-15 verbatim
open CenteredMomentSourceRow CenteredMomentSourceMass CenteredMomentSourceProfileMass

-- @@ L16-16 verbatim
open CenteredMomentFirstSectors CenteredMomentRowNorm CenteredMomentHeckeColumnWindow

-- @@ L17-17 verbatim
open CenteredMomentExceptionalWholeWindow CenteredMomentSmooth

-- @@ L18-18 verbatim
local notation "O" => HeckeFamily.O

-- @@ L19-19 verbatim
local instance {ι:Type*} : DecidableEq (ι⊕Fin 2) := Classical.decEq _

-- @@ L20-20 verbatim
variable {ι:Type*}[Fintype ι][DecidableEq ι]


-- @@ L22-23 verbatim
def columns (s:Input ι)(C:Ideal O)(hC:Supported C):Finset (Ideal O):=
  residualPool C hC.1 (finiteColumns (Fintype.piFinset s.pools))


-- @@ L25-30 verbatim
def coefficient (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (I:supportedColumns (columns s C hC)):ℂ:=
  (Real.sqrt (volume s.toData):ℂ)⁻¹*
    (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then
      finiteColumnCoefficient (Fintype.piFinset s.pools)
        (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 seed) (C*I) else 0)


-- @@ L32-36 verbatim
def windowColumn (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (η:Character)(t θ X:ℝ)(V:ℝ→ℂ)(z:O):ℂ:=
  rowPolynomial Finset.univ (sourceGenerator (columns s C hC))
    (fun I=>coefficient s C hC R seed L I*heightCoeff η t I*
      columnPhase V (Real.log ((Ideal.absNorm (I:Ideal O):ℝ)/X)) θ) z


-- @@ L38-47 verbatim
omit [DecidableEq ι] in
theorem coefficient_polynomial (s:Input ι)(C:Ideal O)(hC:Supported C)(R seed L:Ideal O)
    (η:Character)(t:ℝ)(z:O):
    rowPolynomial Finset.univ (sourceGenerator (columns s C hC))
      (fun I=>coefficient s C hC R seed L I*heightCoeff η t I) z=
      normalizedColumn (withHeight s η t) C hC R seed L z:=by
  unfold normalizedColumn sourceColumn
  dsimp only [withHeight,Input.pools,columns]
  simp only [coefficient,mul_assoc,rowPolynomial_factor,Input.pools,columns]
  rfl


-- @@ L49-51 verbatim
theorem sourceGenerator_span (S:Finset (Ideal O))(I:supportedColumns S):
    Ideal.span {sourceGenerator S I}=(I:Ideal O):=
  primary_span_supported I (Finset.mem_filter.mp I.property).2


-- @@ L53-75 verbatim
omit [DecidableEq ι] in
theorem whole_window_pair (s v:Input ι)(C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (R seed:Ideal O)(Ds:Finset (Ideal O))(μ:Ideal O→ℂ)(rows:Finset O)
    (η τ:Character)(t₁ t₂ θ₁ θ₂ X Y:ℝ)(hX:0<X)(hY:0<Y)
    (V₁ V₂:ℝ→ℂ)(hc₁:HasCompactSupport V₁)(hc₂:HasCompactSupport V₂)
    (hs₁:ContDiff ℝ ∞ V₁)(hs₂:ContDiff ℝ ∞ V₂)(J₁ J₂:ℕ)(E:ℝ)(hE:0≤E)
    (hpair:∀u w:ℝ,(∑L∈Ds,‖μ L‖*∑z∈rows,
      ‖normalizedColumn (withHeight s η (t₁+2*Real.pi*(u-θ₁))) C hC R seed L z‖*
      ‖normalizedColumn (withHeight v τ (t₂+2*Real.pi*(w-θ₂))) D hD R seed L z‖)≤
        E*(1+‖u‖)^J₁*(1+‖w‖)^J₂):
    (∑L∈Ds,‖μ L‖*∑z∈rows,
      ‖windowColumn s C hC R seed L η t₁ θ₁ X V₁ z‖*
      ‖windowColumn v D hD R seed L τ t₂ θ₂ Y V₂ z‖)≤
      E*(∫u:ℝ,(1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)*
        (∫w:ℝ,(1+‖w‖)^J₂*‖columnDensity V₂ hc₂ hs₂ w‖):=by
  have hh:=whole_plain_window_pair Ds μ rows Finset.univ Finset.univ
    (sourceGenerator (columns s C hC)) (sourceGenerator (columns v D hD))
    (sourceGenerator_supported _) (sourceGenerator_supported _)
    (coefficient s C hC R seed) (coefficient v D hD R seed) η τ t₁ t₂ θ₁ θ₂ X Y hX hY
    V₁ V₂ hc₁ hc₂ hs₁ hs₂ J₁ J₂ E hE ?_
  · simpa only [sourceGenerator_span,windowColumn] using hh
  · intro u w
    simpa only [sourceGenerator_span,coefficient_polynomial] using hpair u w


-- @@ L77-77 verbatim
end SevenEighths.CenteredMomentCommonWindowColumn


-- @@ L79-79 verbatim
end


-- @@ L81-81 verbatim
end OAI
