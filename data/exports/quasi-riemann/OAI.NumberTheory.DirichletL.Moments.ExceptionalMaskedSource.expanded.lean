import OAI.NumberTheory.DirichletL.Moments.ExceptionalWholeSource
import OAI.NumberTheory.DirichletL.Moments.SourceRectangleEnergy


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
open Filter


-- @@ L10-10 verbatim
namespace SevenEighths.CenteredMomentExceptionalMaskedSource

-- @@ L11-11 verbatim
open HeckeFamily UniqueFactorizationMonoid CenteredMomentEligibleEnergy

-- @@ L12-12 verbatim
open CenteredMomentDivisorRowEnergy CenteredMomentActiveAllocation

-- @@ L13-13 verbatim
open CenteredMomentAllocatedDetectorAmplitude CenteredMomentExceptionalAmplitudePair

-- @@ L14-14 verbatim
open CenteredMomentExceptionalSourceShell CenteredMomentExceptionalWholeSource

-- @@ L15-15 verbatim
open CenteredMomentSourceRectangle CenteredMomentSourceRectangleEnergy

-- @@ L16-16 verbatim
open CenteredMomentSourceMass CenteredMomentSourceProfileMass

-- @@ L17-17 verbatim
open CenteredMomentHeckeExpansion CenteredMomentSecondHeightFamily CenteredMomentHeckeColumnWindow

-- @@ L18-18 verbatim
open CanonicalQuadraticSieve ConcretePrimeRowBridge CenteredMomentSourceRow CenteredMomentRowNorm

-- @@ L19-19 verbatim
local notation "O" => HeckeFamily.O

-- @@ L20-20 verbatim
universe u

-- @@ L21-21 verbatim
variable {ι κ:Type u} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]


-- @@ L23-25 verbatim
def maskedAmplitude (s:Data ι)(D:Ideal O)(z:O):ℂ:=
  (Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
    maskedRectangle s.η s.m s.A z s.t s.slots s.coefficient D s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂


-- @@ L27-33 verbatim
theorem maskedAmplitude_eq (s:Data ι)(D:Ideal O)(hD:Squarefree D)(z:O):
    maskedAmplitude s D z=∑a∈s.toSource.active D,amplitude s D a z:=by
  unfold maskedAmplitude
  rw [masked_eq_active_allocations s.η s.m s.A z s.t s.slots s.coefficient D hD
    s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ s.support₁ s.support₂
    s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos,Finset.mul_sum]
  rfl


-- @@ L35-52 verbatim
theorem source_polynomial_eq (s:Data ι)(S₁ S₂:Finset (Ideal O))(R D B₁ B₂:Ideal O)
    (X₁ X₂ Y₁ Y₂:ℝ)
    (hm:s.m=fixedBadMask*idealGenerator R)(hA:s.A=1)
    (hX₁:s.X₁=X₁/Ideal.absNorm B₁)(hX₂:s.X₂=X₂/Ideal.absNorm B₂)
    (hY₁:s.Y₁=Y₁/Ideal.absNorm B₁)(hY₂:s.Y₂=Y₂/Ideal.absNorm B₂)
    (hc₁:PlainCoverage S₁ s.W₁ B₁ X₁ Y₁)(hc₂:PlainCoverage S₂ s.W₂ B₂ X₂ Y₂)(z:O):
    (Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
      rowPolynomial Finset.univ (sourceGenerator (finiteColumns (tuplePool s.slots S₁ S₂)))
        (fun I: supportedColumns (finiteColumns (tuplePool s.slots S₁ S₂))=>
          finiteColumnCoefficient (tuplePool s.slots S₁ S₂)
            (profileCoefficient R s.ν s.W s.P s.W₁ s.W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ D) I*
              heightCoeff s.η s.t I) z=maskedAmplitude s D z:=by
  rw [height_source_row]
  rw [CenteredMomentSourceRectangleMask.source_polynomial_eq_maskedRectangle
    s.η fixedBadMask 1 z s.t (dvd_mul_right _ _) (dvd_mul_left _ _)
    s.slots S₁ S₂ R D s.ν s.W s.P s.W₁ s.W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ hc₁ hc₂]
  simp only [maskedAmplitude,hm,hA,hX₁,hX₂,hY₁,hY₂]
  rfl


-- @@ L54-70 verbatim
theorem paired_masked_le (s:Data ι)(v:Data κ)(D:Ideal O)(hD:Squarefree D)(rows:Finset O):
    (∑z∈rows,‖maskedAmplitude s D z‖*‖maskedAmplitude v D z‖)≤
      ∑a∈s.toSource.active D,∑b∈v.toSource.active D,
        ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖:=by
  calc
    _≤∑z∈rows,(∑a∈s.toSource.active D,‖amplitude s D a z‖)*
        (∑b∈v.toSource.active D,‖amplitude v D b z‖):=by
      apply Finset.sum_le_sum
      intro z hz
      rw [maskedAmplitude_eq s D hD,maskedAmplitude_eq v D hD]
      exact mul_le_mul (norm_sum_le _ _) (norm_sum_le _ _) (norm_nonneg _)
        (Finset.sum_nonneg (fun a _=>norm_nonneg _))
    _=_:=by
      simp only [Finset.sum_mul,Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_comm (s:=rows) (t:=s.toSource.active D)]
      exact Finset.sum_comm


-- @@ L72-82 verbatim
theorem whole_masked_le (s:Data ι)(v:Data κ)(Ds:Finset (Ideal O))(rows:Finset O):
    (∑D∈Ds,‖(moebius D:ℂ)‖*∑z∈rows,‖maskedAmplitude s D z‖*‖maskedAmplitude v D z‖)≤
      ∑D∈Ds,‖(moebius D:ℂ)‖*∑a∈s.toSource.active D,∑b∈v.toSource.active D,
        ∑z∈rows,‖amplitude s D a z‖*‖amplitude v D b z‖:=by
  apply Finset.sum_le_sum
  intro D hD
  by_cases hμ:(moebius D:ℂ)=0
  · simp [hμ]
  · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply paired_masked_le s v D
    exact CenteredMomentWholeDivisorShell.squarefree_of_moebius_ne_zero D hμ


-- @@ L84-103 verbatim
theorem actual_masked_whole_source (lo hi:ι→ℝ)(ε δ B Lbound:ℝ)
    (hε:0<ε)(hδ:0<δ)(hB:0≤B)(hL:0≤Lbound):
    ∃J:ℕ,∀Q:Ideal O,Q≠0 → ∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(I L:Finset ι)(s:Data I)(v:Data L)(p q:Tests),
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀r:ℝ,∀rows:Finset O,(∀z∈rows,Admissible s p Q Z B r z) →
      (∀z∈rows,Admissible v q Q Z B r z) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,(moebius D:ℂ)≠0 → (D.absNorm:ℝ)≤Z^Lbound) →
      (∑D∈Ds,‖(moebius D:ℂ)‖*∑z∈rows,
        ‖maskedAmplitude s D z‖*‖maskedAmplitude v D z‖)≤
        C*(rows.card:ℝ)*Z^(2*ε+δ-r)*profileMass s v p q J:=by
  obtain ⟨J,hJ⟩:=actual_whole_source lo hi ε δ B Lbound hε hδ hB hL
  refine ⟨J,?_⟩
  intro Q hQ
  obtain ⟨C,hC,hCZ⟩:=hJ Q hQ
  refine ⟨C,hC,?_⟩
  filter_upwards [hCZ] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro I L s v p q hlo hhi r rows hs hv Ds hDs
  exact (whole_masked_le s v Ds rows).trans (hZ.2 I L s v p q hlo hhi r rows hs hv Ds hDs)


-- @@ L105-105 verbatim
end SevenEighths.CenteredMomentExceptionalMaskedSource


-- @@ L107-107 verbatim
end


-- @@ L109-109 verbatim
end OAI
