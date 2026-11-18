import OAI.NumberTheory.DirichletL.Energy.ReferenceHomogeneousError


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentEnergyZeroReferenceError

-- @@ L9-9 verbatim
open HeckeFamily ConcreteTraceCRT HeckeDyadic QuadraticInitialBound

-- @@ L10-10 verbatim
open CenteredMomentCommonMaskEnergy CenteredMomentOriginalRadialComparison

-- @@ L11-11 verbatim
open CenteredMomentEnergyReferenceHomogeneousError

-- @@ L12-12 verbatim
local notation "O"=>HeckeFamily.O


-- @@ L14-26 verbatim
theorem short_energy_bound (b:ℝ):
    ∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),Function.support (W:ℝ→ℂ)⊆Set.Iic b →
      ∀(χ:O→Character)(t X K:ℝ)(Φ:𝓢(ℝ,ℂ))(keep:O→Prop),0<X →0<K →
      (∀z:O,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      radialEnergy (fun z=>polynomial (χ z) false W X 0 t) keep Φ K≤
        C*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*diagonalControl Φ*max 1 K*X:=by
  obtain ⟨C,hC,h⟩:=natural_reference_error_homogeneous (∅:Finset (Fin 0)) b
    (fun _=>0) (fun _=>0) (by simp)
  refine ⟨C,hC,?_⟩
  intro W hs χ t X K Φ keep hX hK hΦ
  have hh:=h ∅ (Finset.Subset.refl _) W hs χ (fun _=>∅) (fun _ _=>0)
    (fun _=>1) t X K Φ keep hX hK (by simp) (by simp) (by simp) (by simp) hΦ
  simpa only [Finset.prod_empty,mul_one] using hh


-- @@ L28-28 verbatim
end SevenEighths.CenteredMomentEnergyZeroReferenceError


-- @@ L30-30 verbatim
end


-- @@ L32-32 verbatim
end OAI
