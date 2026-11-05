import Mathlib
import Definitions.Def_Deformations_ProartinianCat


-- @@ L4-4 verbatim
set_option autoImplicit false


-- @@ L6-6 verbatim
universe u


-- @@ L8-8 verbatim
namespace Deformation


-- @@ L10-10 verbatim
open CategoryTheory IsLocalRing MvPowerSeries


-- @@ L12-12 verbatim
local notation3:max "𝓴" 𝓞:max => (IsLocalRing.ResidueField 𝓞)


-- @@ L14-14 verbatim
namespace ProartinianCat


-- @@ L16-16 verbatim
section Nilpotence


-- @@ L18-18 verbatim
variable {R : Type u} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

-- @@ L19-19 verbatim
variable [IsLocalRing R] [IsProartinian R]


-- @@ L21-28 verbatim
lemma isTopologicallyNilpotent_of_mem_maximalIdeal {x : R} (hx : x ∈ maximalIdeal R) :
    IsTopologicallyNilpotent x := by
  rw [IsTopologicallyNilpotent,
    (IsLinearTopology.hasBasis_open_ideal (R := R)).tendsto_right_iff]
  intro I hI
  obtain ⟨N, hN⟩ := exists_maximalIdeal_pow_le_of_isProartinian I hI
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  exact hN (Ideal.pow_le_pow_right hn (Ideal.pow_mem_pow hx n))


-- @@ L30-35 verbatim
lemma hasEval_of_forall_mem_maximalIdeal {σ : Type*} [Finite σ] {x : σ → R}
    (hx : ∀ j, x j ∈ maximalIdeal R) : MvPowerSeries.HasEval x where
  hpow j := isTopologicallyNilpotent_of_mem_maximalIdeal (hx j)
  tendsto_zero := by
    rw [Filter.cofinite_eq_bot]
    exact Filter.tendsto_bot


-- @@ L37-37 verbatim
end Nilpotence


-- @@ L39-39 verbatim
section Object


-- @@ L41-41 verbatim
open MvPowerSeries.WithPiTopology


-- @@ L43-43 verbatim
variable (𝓞 : Type u) [CommRing 𝓞] (σ : Type)


-- @@ L45-49 verbatim
omit [CommRing 𝓞] in

lemma compactSpace_mvPowerSeries [TopologicalSpace 𝓞] [CompactSpace 𝓞] :
    CompactSpace (MvPowerSeries σ 𝓞) :=
  inferInstanceAs (CompactSpace ((σ →₀ ℕ) → 𝓞))


-- @@ L51-55 verbatim
lemma X_mem_maximalIdeal [IsLocalRing 𝓞] (j : σ) :
    MvPowerSeries.X j ∈ maximalIdeal (MvPowerSeries σ 𝓞) := by
  rw [mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff,
    MvPowerSeries.constantCoeff_X]
  exact fun h => h.ne_zero rfl


-- @@ L57-64 verbatim
lemma isProartinian_mvPowerSeries [IsLocalRing 𝓞] [IsNoetherianRing 𝓞] [TopologicalSpace 𝓞]
    [IsTopologicalRing 𝓞] [IsAdicTopology 𝓞] [CompactSpace 𝓞] :
    IsProartinian (MvPowerSeries σ 𝓞) := by
  haveI : CompactSpace (MvPowerSeries σ 𝓞) := compactSpace_mvPowerSeries 𝓞 σ
  exact
    { isArtinianRing_quotient := fun I hI => by
        have : Finite (MvPowerSeries σ 𝓞 ⧸ I) := AddSubgroup.quotient_finite_of_isOpen _ hI
        exact isArtinian_of_finite }


-- @@ L66-72 verbatim
lemma isLocalHom_algebraMap_mvPowerSeries [IsLocalRing 𝓞] :
    IsLocalHom (algebraMap 𝓞 (MvPowerSeries σ 𝓞)) := by
  constructor
  intro a ha
  rw [← MvPowerSeries.c_eq_algebraMap, MvPowerSeries.isUnit_iff_constantCoeff,
    MvPowerSeries.constantCoeff_C] at ha
  exact ha


-- @@ L74-83 verbatim
lemma isResidueAlgebra_mvPowerSeries [IsLocalRing 𝓞] :
    IsResidueAlgebra 𝓞 (MvPowerSeries σ 𝓞) := by
  constructor
  intro y
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨MvPowerSeries.constantCoeff f, ?_⟩
  show residue _ _ = residue _ _
  rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, mem_maximalIdeal, mem_nonunits_iff,
    MvPowerSeries.isUnit_iff_constantCoeff]
  simp [← MvPowerSeries.c_eq_algebraMap]


-- @@ L85-92 verbatim
lemma isLocalProartinianAlgebra_mvPowerSeries [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]
    [TopologicalSpace 𝓞] [IsTopologicalRing 𝓞] [IsAdicTopology 𝓞] [CompactSpace 𝓞] :
    IsLocalProartinianAlgebra 𝓞 (MvPowerSeries σ 𝓞) := by
  haveI : IsProartinian (MvPowerSeries σ 𝓞) := isProartinian_mvPowerSeries 𝓞 σ
  haveI : IsLocalHom (algebraMap 𝓞 (MvPowerSeries σ 𝓞)) :=
    isLocalHom_algebraMap_mvPowerSeries 𝓞 σ
  haveI : IsResidueAlgebra 𝓞 (MvPowerSeries σ 𝓞) := isResidueAlgebra_mvPowerSeries 𝓞 σ
  exact ⟨⟩


-- @@ L94-94 verbatim
end Object


-- @@ L96-96 verbatim
section Category


-- @@ L98-98 verbatim
variable (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞] [IsNoetherianRing 𝓞]

-- @@ L99-99 verbatim
variable [Finite (ResidueField 𝓞)] [IsAdicComplete (maximalIdeal 𝓞) 𝓞]


-- @@ L101-111 verbatim
noncomputable def mvPowerSeriesObj (n : ℕ) : ProartinianCat 𝓞 where
  carrier := MvPowerSeries (Fin n) 𝓞
  topologicalSpace :=
    letI := (maximalIdeal 𝓞).adicTopology
    WithPiTopology.instTopologicalSpace 𝓞
  isLocalProartinianAlgebra :=
    letI := (maximalIdeal 𝓞).adicTopology
    letI : IsTopologicalRing 𝓞 := (RingSubgroupsBasis.toRingFilterBasis _).isTopologicalRing
    letI : IsAdicTopology 𝓞 := ⟨rfl⟩
    letI : CompactSpace 𝓞 := compactSpace_of_finite_residueField
    isLocalProartinianAlgebra_mvPowerSeries 𝓞 (Fin n)


-- @@ L113-113 verbatim
variable {𝓞}


-- @@ L115-116 verbatim
noncomputable def mvPowerSeriesObjX {n : ℕ} (j : Fin n) : (mvPowerSeriesObj 𝓞 n).carrier :=
  MvPowerSeries.X j


-- @@ L118-120 verbatim
lemma mvPowerSeriesObjX_mem_maximalIdeal {n : ℕ} (j : Fin n) :
    mvPowerSeriesObjX (𝓞 := 𝓞) j ∈ maximalIdeal (mvPowerSeriesObj 𝓞 n).carrier :=
  X_mem_maximalIdeal 𝓞 (Fin n) j


-- @@ L122-122 verbatim
end Category


-- @@ L124-124 verbatim
end ProartinianCat


-- @@ L126-126 verbatim
end Deformation
