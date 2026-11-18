import OAI.NumberTheory.DirichletL.Moments.SourceInputFirstSectorTailUniform


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators SchwartzMap ContDiff

-- @@ L7-7 verbatim
open Filter


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentSourceInputFirstSectorTail

-- @@ L10-10 verbatim
open HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData

-- @@ L11-11 verbatim
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass CenteredMomentSourceRow

-- @@ L12-12 verbatim
open CenteredMomentSourceZeroEnergy CenteredMomentSourceLiveColumn CenteredMomentSupportedZeroEnergy

-- @@ L13-13 verbatim
open CenteredMomentSourceProfileMassUniform CenteredMomentSourceProfileMass

-- @@ L14-14 verbatim
open CenteredMomentSupportedTailAggregate CenteredMomentSectorLocalization

-- @@ L15-15 verbatim
open CenteredMomentExceptionalAmplitudePair CenteredMomentNaturalRadialCutoff

-- @@ L16-16 verbatim
open CenteredMomentSourceInputTailUniform CenteredMomentFirstTailAggregate

-- @@ L17-17 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L18-18 verbatim
variable {ι:Type*}[Fintype ι][DecidableEq ι]

-- @@ L19-19 verbatim
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _


-- @@ L21-50 verbatim
omit [DecidableEq ι] in
theorem local_input_tail (hi:ι→ℝ)(wlo whi B ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(hwlo:0<wlo)(hwhi:0≤whi)(hB:0≤B)(hξ:0<ξ):
    ∃SΦ:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),s.W₁=W₁→s.W₂=W₂→
      Function.support (W₁:ℝ→ℂ)⊆Set.Icc wlo whi→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc wlo whi→
      (∀i,s.hi i≤hi i)→∀(m A:O)(R seed:Ideal O)(Φ:𝓢(ℝ,ℂ))(K:ℝ),
      0<K→volume s.toData≤Z^B→K⁻¹≤Z^B→
      ‖CenteredMomentFirstSectorLocalization.discardedEnergy s.η m A s.t (finiteColumns (Fintype.piFinset s.pools))
        (coefficient s R seed) Φ K (volume s.toData) Z ξ‖/volume s.toData≤
      C*(plainControl s W₁ W₂)^2*SΦ.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*K*Z^(-saving) := by
  obtain ⟨S,C,hC,htail⟩ := local_input_tail_arbitrary_saving hi wlo whi (3*B) ξ saving
    hhi hwlo hwhi (by positivity) hξ
  refine ⟨S,C,hC,?_⟩
  filter_upwards [htail] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K hK hV hKi
  have hz : 0<Z := zero_lt_one.trans hZ.1
  have hV0 : 0<volume s.toData := volume_pos s
  have hVcap : volume s.toData≤Z^(3*B) := hV.trans
    (Real.rpow_le_rpow_of_exponent_le hZ.1.le (by linarith))
  have hTcap : (volume s.toData)^2/K≤Z^(3*B) := by
    rw [div_eq_mul_inv]
    apply (mul_le_mul (pow_le_pow_left₀ hV0.le hV 2) hKi (inv_nonneg.mpr hK.le) (by positivity)).trans_eq
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_add hz]
    congr 1
    norm_num
    ring
  exact hZ.2 s W₁ W₂ he₁ he₂ hs₁ hs₂ hshi m A R seed Φ K _ hK hVcap hTcap le_rfl


-- @@ L52-52 verbatim
end SevenEighths.CenteredMomentSourceInputFirstSectorTail


-- @@ L54-54 verbatim
end


-- @@ L56-56 verbatim
end OAI
