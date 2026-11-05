import Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicLevel
import Definitions.Def_IsDedekindDomain_FiniteUnitIdeles


-- @@ L6-6 verbatim
set_option autoImplicit false


-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
open NumberField MeasureTheory LanglandsTunnell.CubicInduction


-- @@ L12-12 verbatim
namespace LanglandsTunnell.CubicInduction.AdelicEpstein


-- @@ L14-14 verbatim
local notation "𝔸" => AdeleRing (𝓞 ℚ) ℚ

-- @@ L15-15 verbatim
local notation "Ẑˣ" => IsDedekindDomain.FiniteAdeleRing.unitIdeles (𝓞 ℚ) ℚ


-- @@ L17-18 verbatim
def ofReal (t : ℝ) : Rat.infinitePlace.Completion :=
  (InfinitePlace.Completion.ringEquivRealOfIsReal Rat.isReal_infinitePlace).symm t


-- @@ L20-22 verbatim
def archIdele (t : ℝ) : 𝔸ˣ :=
  if h : t = 0 then 1 else
    TateGlobal.archUnitHom Rat.infinitePlace (Units.mk0 (ofReal t) (by unfold ofReal; exact (map_ne_zero _).mpr h))


-- @@ L24-25 verbatim
def finUnitIdele (u : Ẑˣ) : 𝔸ˣ :=
  Units.map (AdelicLevel.finIncl (𝓞 ℚ) ℚ) (u : (IsDedekindDomain.FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ)


-- @@ L27-27 verbatim
def adelicDiag (ξ : Fin 3 → ℚ) : Fin 3 → 𝔸 := fun i => algebraMap ℚ 𝔸 (ξ i)


-- @@ L29-30 verbatim
def point (t : ℝ) (u : Ẑˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) (ξ : Fin 3 → ℚ) : Fin 3 → 𝔸 :=
  fun i => ((archIdele t * finUnitIdele u : 𝔸ˣ) : 𝔸) * (Matrix.vecMul (adelicDiag ξ) (g : Matrix (Fin 3) (Fin 3) 𝔸)) i


-- @@ L32-33 verbatim
def scaleMeasure : Measure ℝ :=
  (volume.restrict (Set.Ioi (0 : ℝ))).withDensity fun t => ENNReal.ofReal t⁻¹


-- @@ L35-36 verbatim
def latticeSum (Φ : (Fin 3 → 𝔸) → ℂ) (t : ℝ) (u : Ẑˣ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℂ :=
  ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, Φ (point t u g ξ)


-- @@ L38-40 verbatim
def epstein [MeasurableSpace Ẑˣ] (du : Measure Ẑˣ) (Φ : (Fin 3 → 𝔸) → ℂ) (σ : ℝ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) : ℂ :=
  ((TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ : ℝ) : ℂ) *
    ∫ t, ((t ^ (3 * σ) : ℝ) : ℂ) * ∫ u, latticeSum Φ t u g ∂du ∂scaleMeasure


-- @@ L42-46 verbatim
def epsteinPlus [MeasurableSpace Ẑˣ] (du : Measure Ẑˣ) (Φ : (Fin 3 → 𝔸) → ℂ) (σ : ℝ) (g : AdelicGL 3 (𝓞 ℚ) ℚ) :
    ENNReal :=
  ENNReal.ofReal (TateGlobal.ideleNorm ℚ (Matrix.GeneralLinearGroup.det g) ^ σ) *
    ∫⁻ t, ENNReal.ofReal (t ^ (3 * σ)) *
      ∫⁻ u, ∑' ξ : {ξ : Fin 3 → ℚ // ξ ≠ 0}, (‖Φ (point t u g ξ)‖₊ : ENNReal) ∂du ∂scaleMeasure


-- @@ L48-49 verbatim
@[reducible] def unitIdeleMeasurableSpace : MeasurableSpace Ẑˣ :=
  MeasurableSpace.comap (fun u : Ẑˣ => ((finUnitIdele u : 𝔸ˣ) : 𝔸)) (NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ)


-- @@ L51-54 verbatim
theorem measurable_finUnitIdele :
    @Measurable Ẑˣ 𝔸 unitIdeleMeasurableSpace (NumberField.AdelicHaar.adeleBorel (𝓞 ℚ) ℚ)
      (fun u : Ẑˣ => ((finUnitIdele u : 𝔸ˣ) : 𝔸)) :=
  comap_measurable _


-- @@ L56-56 verbatim
end LanglandsTunnell.CubicInduction.AdelicEpstein


-- @@ L58-58 verbatim
end
