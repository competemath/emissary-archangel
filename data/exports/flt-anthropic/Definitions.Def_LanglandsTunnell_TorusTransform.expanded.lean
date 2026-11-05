import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_AutomorphicForm_CarrierPins
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_NumberField_NormPowChar
import Definitions.Def_LocalLanglands_HeckeCosetLocal
import Definitions.Def_M4aHerbrand_IdeleClassVocab
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Probability.ConditionalProbability
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_AutomorphicForm_ArchType
import Definitions.Def_AutomorphicForm_ArchWeightChar
import Definitions.Def_AutomorphicForm_ViaCompactCuspNotion
import Definitions.Def_LanglandsTunnell_JLSynthesis


-- @@ L19-19 verbatim
set_option autoImplicit false


-- @@ L21-21 verbatim
open IsDedekindDomain NumberField AutomorphicForm

-- @@ L22-22 verbatim
open NumberField.AdelicLevel NumberField.AdelicBox NumberField.TateGlobal

-- @@ L23-23 verbatim
open AutomorphicForm.WindowedSiegel

-- @@ L24-24 verbatim
open LanglandsTunnell.Converse


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
section

-- @@ L29-29 verbatim
open scoped WithZero

-- @@ L30-30 verbatim
noncomputable section

-- @@ L31-31 verbatim
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel

-- @@ L32-32 verbatim
open NumberField.AdelicVolume NumberField.TateGlobal

-- @@ L33-33 verbatim
open Filter Topology

-- @@ L34-34 verbatim
namespace LanglandsTunnell.Converse.Ideles

-- @@ L35-35 verbatim
variable {K : Type} [Field K] [NumberField K]

-- @@ L36-36 verbatim
local notation "𝔸" => AdeleRing (𝓞 K) K

-- @@ L37-39 verbatim
theorem val_mul_inv_snd_apply (z : 𝔸ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    (z : 𝔸).2 v * ((z⁻¹ : 𝔸ˣ) : 𝔸).2 v = 1 :=
  congrArg (fun x : 𝔸 => x.2 v) z.mul_inv

-- @@ L40-40 verbatim
end LanglandsTunnell.Converse.Ideles

-- @@ L41-41 verbatim
end

-- @@ L42-42 verbatim
end


-- @@ L44-44 verbatim
section

-- @@ L45-45 verbatim
open scoped WithZero

-- @@ L46-46 verbatim
noncomputable section

-- @@ L47-47 verbatim
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel

-- @@ L48-48 verbatim
open NumberField.AdelicVolume NumberField.TateGlobal

-- @@ L49-49 verbatim
open Filter Topology

-- @@ L50-50 verbatim
namespace LanglandsTunnell.Converse.Ideles

-- @@ L51-51 verbatim
variable {K : Type} [Field K] [NumberField K]

-- @@ L52-52 verbatim
local notation "𝔸" => AdeleRing (𝓞 K) K

-- @@ L53-55 verbatim
theorem val_inv_mul_snd_apply (z : 𝔸ˣ) (v : HeightOneSpectrum (𝓞 K)) :
    ((z⁻¹ : 𝔸ˣ) : 𝔸).2 v * (z : 𝔸).2 v = 1 :=
  congrArg (fun x : 𝔸 => x.2 v) z.inv_mul

-- @@ L56-56 verbatim
end LanglandsTunnell.Converse.Ideles

-- @@ L57-57 verbatim
end

-- @@ L58-58 verbatim
end


-- @@ L60-60 verbatim
section

-- @@ L61-61 verbatim
open scoped WithZero

-- @@ L62-62 verbatim
noncomputable section

-- @@ L63-63 verbatim
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel

-- @@ L64-64 verbatim
open NumberField.AdelicVolume NumberField.TateGlobal

-- @@ L65-65 verbatim
open Filter Topology

-- @@ L66-66 verbatim
namespace LanglandsTunnell.Converse.Ideles

-- @@ L67-67 verbatim
variable {K : Type} [Field K] [NumberField K]

-- @@ L68-68 verbatim
local notation "𝔸" => AdeleRing (𝓞 K) K


-- @@ L70-71 verbatim
def archProd (a : ∀ w : InfinitePlace K, (w.Completion)ˣ) (T : Finset (InfinitePlace K)) : 𝔸ˣ :=
  ∏ w ∈ T, archUnitHom w (a w)

-- @@ L72-72 verbatim
end LanglandsTunnell.Converse.Ideles

-- @@ L73-73 verbatim
end

-- @@ L74-74 verbatim
end


-- @@ L76-76 verbatim
section

-- @@ L77-77 verbatim
open scoped WithZero

-- @@ L78-78 verbatim
noncomputable section

-- @@ L79-79 verbatim
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel

-- @@ L80-80 verbatim
open NumberField.AdelicVolume NumberField.TateGlobal

-- @@ L81-81 verbatim
open Filter Topology

-- @@ L82-82 verbatim
namespace LanglandsTunnell.Converse.Ideles

-- @@ L83-83 verbatim
variable {K : Type} [Field K] [NumberField K]

-- @@ L84-84 verbatim
local notation "𝔸" => AdeleRing (𝓞 K) K


-- @@ L86-90 verbatim
def unitAt (v : HeightOneSpectrum (𝓞 K)) (z : 𝔸ˣ) : (v.adicCompletion K)ˣ where
  val := (z : 𝔸).2 v
  inv := ((z⁻¹ : 𝔸ˣ) : 𝔸).2 v
  val_inv := val_mul_inv_snd_apply z v
  inv_val := val_inv_mul_snd_apply z v

-- @@ L91-91 verbatim
end LanglandsTunnell.Converse.Ideles

-- @@ L92-92 verbatim
end

-- @@ L93-93 verbatim
end


-- @@ L95-95 verbatim
section

-- @@ L96-96 verbatim
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm

-- @@ L97-97 verbatim
open LanglandsTunnell.Converse LanglandsTunnell.Converse.Ideles NumberField.AdelicVolume NumberField.TateGlobal

-- @@ L98-98 verbatim
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

-- @@ L99-99 verbatim
open scoped Classical

-- @@ L100-100 verbatim
namespace LanglandsTunnell.Converse.Ideles

-- @@ L101-101 verbatim
section ScalingLine

-- @@ L102-102 verbatim
variable {K : Type} [Field K]


-- @@ L104-106 verbatim
noncomputable def expAt (w : InfinitePlace K) (s : ℝ) : w.Completion :=
  if hw : w.IsReal then (ringEquivRealOfIsReal hw).symm (Real.exp s)
  else (ringEquivComplexOfIsComplex (not_isReal_iff_isComplex.mp hw)).symm (Complex.exp s)

-- @@ L107-107 verbatim
end ScalingLine

-- @@ L108-108 verbatim
end LanglandsTunnell.Converse.Ideles

-- @@ L109-109 verbatim
end


-- @@ L111-111 verbatim
section

-- @@ L112-112 verbatim
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm

-- @@ L113-113 verbatim
open LanglandsTunnell.Converse LanglandsTunnell.Converse.Ideles NumberField.AdelicVolume NumberField.TateGlobal

-- @@ L114-114 verbatim
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

-- @@ L115-115 verbatim
open scoped Classical

-- @@ L116-116 verbatim
namespace LanglandsTunnell.Converse.Ideles

-- @@ L117-117 verbatim
section ScalingLine

-- @@ L118-118 verbatim
variable {K : Type} [Field K]

-- @@ L119-132 verbatim
theorem norm_expAt (w : InfinitePlace K) (s : ℝ) : ‖expAt w s‖ = Real.exp s := by
  unfold expAt
  split_ifs with hw
  · have h := (isometry_extensionEmbeddingOfIsReal hw).norm_map_of_map_zero (map_zero _)
      ((ringEquivRealOfIsReal hw).symm (Real.exp s))
    rw [← h]
    change ‖ringEquivRealOfIsReal hw ((ringEquivRealOfIsReal hw).symm (Real.exp s))‖ = _
    rw [RingEquiv.apply_symm_apply, Real.norm_eq_abs, abs_of_pos (Real.exp_pos s)]
  · set hc := not_isReal_iff_isComplex.mp hw
    have h := (isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _)
      ((ringEquivComplexOfIsComplex hc).symm (Complex.exp s))
    rw [← h]
    change ‖ringEquivComplexOfIsComplex hc ((ringEquivComplexOfIsComplex hc).symm (Complex.exp s))‖ = _
    rw [RingEquiv.apply_symm_apply, Complex.norm_exp_ofReal]

-- @@ L133-133 verbatim
end ScalingLine

-- @@ L134-134 verbatim
end LanglandsTunnell.Converse.Ideles

-- @@ L135-135 verbatim
end


-- @@ L137-137 verbatim
section

-- @@ L138-138 verbatim
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm

-- @@ L139-139 verbatim
open LanglandsTunnell.Converse LanglandsTunnell.Converse.Ideles NumberField.AdelicVolume NumberField.TateGlobal

-- @@ L140-140 verbatim
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

-- @@ L141-141 verbatim
open scoped Classical

-- @@ L142-142 verbatim
namespace LanglandsTunnell.Converse.Ideles

-- @@ L143-143 verbatim
section ScalingLine

-- @@ L144-144 verbatim
variable {K : Type} [Field K]

-- @@ L145-149 verbatim
theorem expAt_ne_zero (w : InfinitePlace K) (s : ℝ) : expAt w s ≠ 0 := by
  intro h
  have := norm_expAt w s
  rw [h, norm_zero] at this
  exact (Real.exp_pos s).ne this

-- @@ L150-150 verbatim
end ScalingLine

-- @@ L151-151 verbatim
end LanglandsTunnell.Converse.Ideles

-- @@ L152-152 verbatim
end


-- @@ L154-154 verbatim
section

-- @@ L155-155 verbatim
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm

-- @@ L156-156 verbatim
open LanglandsTunnell.Converse LanglandsTunnell.Converse.Ideles NumberField.AdelicVolume NumberField.TateGlobal

-- @@ L157-157 verbatim
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

-- @@ L158-158 verbatim
open scoped Classical

-- @@ L159-159 verbatim
namespace LanglandsTunnell.Converse.Ideles

-- @@ L160-160 verbatim
section ScalingLine

-- @@ L161-161 verbatim
variable {K : Type} [Field K]


-- @@ L163-163 verbatim
noncomputable def expUnitAt (w : InfinitePlace K) (s : ℝ) : (w.Completion)ˣ := Units.mk0 _ (expAt_ne_zero w s)

-- @@ L164-164 verbatim
end ScalingLine

-- @@ L165-165 verbatim
end LanglandsTunnell.Converse.Ideles

-- @@ L166-166 verbatim
end


-- @@ L168-168 verbatim
section

-- @@ L169-169 verbatim
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.AdelicLevel AutomorphicForm

-- @@ L170-170 verbatim
open LanglandsTunnell.Converse LanglandsTunnell.Converse.Ideles NumberField.AdelicVolume NumberField.TateGlobal

-- @@ L171-171 verbatim
open NumberField.InfinitePlace NumberField.InfinitePlace.Completion

-- @@ L172-172 verbatim
open scoped Classical

-- @@ L173-173 verbatim
namespace LanglandsTunnell.Converse.Ideles

-- @@ L174-174 verbatim
section ScalingLine

-- @@ L175-175 verbatim
variable {K : Type} [Field K]

-- @@ L176-176 verbatim
variable [NumberField K]

-- @@ L177-180 verbatim
variable (K) in

noncomputable def archScale (t : ℝ) : (AdeleRing (𝓞 K) K)ˣ :=
  archProd (fun w => expUnitAt w (t / Module.finrank ℚ K)) Finset.univ

-- @@ L181-181 verbatim
end ScalingLine

-- @@ L182-182 verbatim
end LanglandsTunnell.Converse.Ideles

-- @@ L183-183 verbatim
end


-- @@ L185-185 verbatim
namespace LanglandsTunnell.Converse.CuspSynthesis

-- @@ L186-186 verbatim
open AutomorphicForm.SmoothCusp

-- @@ L187-187 verbatim
variable {K : Type} [Field K] [NumberField K]

-- @@ L188-188 verbatim
section

-- @@ L189-189 verbatim
section TorusModel

-- @@ L190-190 verbatim
open LanglandsTunnell.Converse.Ideles

-- @@ L191-192 verbatim
theorem unitAt_mul (v : HeightOneSpectrum (𝓞 K)) (a b : (AdeleRing (𝓞 K) K)ˣ) :
    unitAt v (a * b) = unitAt v a * unitAt v b := Units.ext rfl

-- @@ L193-193 verbatim
end TorusModel

-- @@ L194-194 verbatim
end

-- @@ L195-195 verbatim
end LanglandsTunnell.Converse.CuspSynthesis


-- @@ L197-197 verbatim
namespace LanglandsTunnell.Converse.CuspSynthesis

-- @@ L198-198 verbatim
open AutomorphicForm.SmoothCusp

-- @@ L199-199 verbatim
variable {K : Type} [Field K] [NumberField K]

-- @@ L200-200 verbatim
section

-- @@ L201-201 verbatim
section TorusModel

-- @@ L202-202 verbatim
open LanglandsTunnell.Converse.Ideles

-- @@ L203-203 verbatim
theorem unitAt_one (v : HeightOneSpectrum (𝓞 K)) : unitAt v (1 : (AdeleRing (𝓞 K) K)ˣ) = 1 := Units.ext rfl

-- @@ L204-204 verbatim
end TorusModel

-- @@ L205-205 verbatim
end

-- @@ L206-206 verbatim
end LanglandsTunnell.Converse.CuspSynthesis


-- @@ L208-208 verbatim
namespace LanglandsTunnell.Converse.CuspSynthesis

-- @@ L209-209 verbatim
open AutomorphicForm.SmoothCusp

-- @@ L210-210 verbatim
variable {K : Type} [Field K] [NumberField K]

-- @@ L211-211 verbatim
section

-- @@ L212-212 verbatim
section TorusModel

-- @@ L213-213 verbatim
open LanglandsTunnell.Converse.Ideles

-- @@ L214-215 verbatim
theorem unitAt_inv (v : HeightOneSpectrum (𝓞 K)) (a : (AdeleRing (𝓞 K) K)ˣ) : unitAt v a⁻¹ = (unitAt v a)⁻¹ :=
  Units.ext rfl

-- @@ L216-216 verbatim
end TorusModel

-- @@ L217-217 verbatim
end

-- @@ L218-218 verbatim
end LanglandsTunnell.Converse.CuspSynthesis


-- @@ L220-220 verbatim
namespace LanglandsTunnell.Converse.CuspSynthesis

-- @@ L221-221 verbatim
open AutomorphicForm.SmoothCusp

-- @@ L222-222 verbatim
variable {K : Type} [Field K] [NumberField K]

-- @@ L223-223 verbatim
section

-- @@ L224-224 verbatim
section TorusModel

-- @@ L225-225 verbatim
open LanglandsTunnell.Converse.Ideles


-- @@ L227-237 verbatim
def unitIdelesAt (S : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup (AdeleRing (𝓞 K) K)ˣ where
  carrier := {a | ∀ v : ↥S, Valued.v (unitAt v.1 a : v.1.adicCompletion K) = 1}
  mul_mem' {a b} ha hb v := by
    show Valued.v (unitAt v.1 (a * b) : v.1.adicCompletion K) = 1
    rw [unitAt_mul, Units.val_mul, map_mul, ha v, hb v, one_mul]
  one_mem' v := by
    show Valued.v (unitAt v.1 1 : v.1.adicCompletion K) = 1
    rw [unitAt_one, Units.val_one, map_one]
  inv_mem' {a} ha v := by
    show Valued.v (unitAt v.1 a⁻¹ : v.1.adicCompletion K) = 1
    rw [unitAt_inv, Units.val_inv_eq_inv_val, map_inv₀, ha v, inv_one]

-- @@ L238-238 verbatim
end TorusModel

-- @@ L239-239 verbatim
end

-- @@ L240-240 verbatim
end LanglandsTunnell.Converse.CuspSynthesis


-- @@ L242-242 verbatim
namespace LanglandsTunnell.Converse.CuspSynthesis

-- @@ L243-243 verbatim
open AutomorphicForm.SmoothCusp

-- @@ L244-244 verbatim
variable {K : Type} [Field K] [NumberField K]

-- @@ L245-245 verbatim
section

-- @@ L246-246 verbatim
section TorusModel

-- @@ L247-247 verbatim
open LanglandsTunnell.Converse.Ideles

-- @@ L248-251 verbatim
variable (K) in

abbrev NormOneQuot : Type :=
  ↥(normOneIdeles K) ⧸ (M4aHerbrand.principalIdeles (𝓞 K) K).subgroupOf (normOneIdeles K)

-- @@ L252-252 verbatim
end TorusModel

-- @@ L253-253 verbatim
end

-- @@ L254-254 verbatim
end LanglandsTunnell.Converse.CuspSynthesis


-- @@ L256-256 verbatim
namespace LanglandsTunnell.Converse.CuspSynthesis

-- @@ L257-257 verbatim
open AutomorphicForm.SmoothCusp

-- @@ L258-258 verbatim
variable {K : Type} [Field K] [NumberField K]

-- @@ L259-259 verbatim
section

-- @@ L260-260 verbatim
section TorusClass

-- @@ L261-261 verbatim
open LanglandsTunnell.Converse.Ideles NumberField.TateGlobal


-- @@ L263-264 verbatim
noncomputable def torusClass (S : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup (NormOneQuot K) :=
  ((unitIdelesAt S).subgroupOf (normOneIdeles K)).map (QuotientGroup.mk' _)

-- @@ L265-265 verbatim
end TorusClass

-- @@ L266-266 verbatim
end

-- @@ L267-267 verbatim
end LanglandsTunnell.Converse.CuspSynthesis


-- @@ L269-269 verbatim
namespace LanglandsTunnell.Converse.CuspSynthesis

-- @@ L270-270 verbatim
open AutomorphicForm.SmoothCusp

-- @@ L271-271 verbatim
variable {K : Type} [Field K] [NumberField K]

-- @@ L272-272 verbatim
section

-- @@ L273-273 verbatim
section TorusClass

-- @@ L274-274 verbatim
open LanglandsTunnell.Converse.Ideles NumberField.TateGlobal

-- @@ L275-278 verbatim
theorem mem_torusClass_iff {S : Finset (HeightOneSpectrum (𝓞 K))} {q : NormOneQuot K} :
    q ∈ torusClass S ↔
      ∃ x : ↥(normOneIdeles K), (x : (AdeleRing (𝓞 K) K)ˣ) ∈ unitIdelesAt S ∧ QuotientGroup.mk x = q := by
  simp only [torusClass, Subgroup.mem_map, Subgroup.mem_subgroupOf, QuotientGroup.mk'_apply]

-- @@ L279-279 verbatim
end TorusClass

-- @@ L280-280 verbatim
end

-- @@ L281-281 verbatim
end LanglandsTunnell.Converse.CuspSynthesis


-- @@ L283-283 verbatim
namespace LanglandsTunnell.Converse.CuspSynthesis

-- @@ L284-284 verbatim
open AutomorphicForm.SmoothCusp

-- @@ L285-285 verbatim
variable {K : Type} [Field K] [NumberField K]

-- @@ L286-286 verbatim
section

-- @@ L287-287 verbatim
section TorusClass

-- @@ L288-288 verbatim
open LanglandsTunnell.Converse.Ideles NumberField.TateGlobal


-- @@ L290-292 verbatim
noncomputable def torusLift {S : Finset (HeightOneSpectrum (𝓞 K))} (q : ↥(torusClass (K := K) S)) :
    ↥(normOneIdeles K) :=
  Classical.choose (mem_torusClass_iff.1 q.2)

-- @@ L293-293 verbatim
end TorusClass

-- @@ L294-294 verbatim
end

-- @@ L295-295 verbatim
end LanglandsTunnell.Converse.CuspSynthesis


-- @@ L297-297 verbatim
noncomputable section

-- @@ L298-298 verbatim
namespace LanglandsTunnell.Converse.CuspSynthesis

-- @@ L299-299 verbatim
open MeasureTheory Topology

-- @@ L300-300 verbatim
section TorusMeasure

-- @@ L301-301 verbatim
variable {K : Type} [Field K] [NumberField K]


-- @@ L303-305 verbatim
@[reducible] def torusBorel (S : Finset (HeightOneSpectrum (𝓞 K))) :
    MeasurableSpace ↥(torusClass (K := K) S) :=
  borel _

-- @@ L306-306 verbatim
end TorusMeasure

-- @@ L307-307 verbatim
end LanglandsTunnell.Converse.CuspSynthesis

-- @@ L308-308 verbatim
end


-- @@ L310-310 verbatim
noncomputable section

-- @@ L311-311 verbatim
namespace LanglandsTunnell.Converse.CuspSynthesis

-- @@ L312-312 verbatim
open MeasureTheory Topology

-- @@ L313-313 verbatim
section TorusMeasure

-- @@ L314-314 verbatim
variable {K : Type} [Field K] [NumberField K]

-- @@ L315-317 verbatim
theorem borelSpace_torusBorel (S : Finset (HeightOneSpectrum (𝓞 K))) :
    @BorelSpace ↥(torusClass (K := K) S) _ (torusBorel S) :=
  @BorelSpace.mk _ _ (torusBorel S) rfl

-- @@ L318-318 verbatim
end TorusMeasure

-- @@ L319-319 verbatim
end LanglandsTunnell.Converse.CuspSynthesis

-- @@ L320-320 verbatim
end


-- @@ L322-322 verbatim
noncomputable section

-- @@ L323-323 verbatim
namespace LanglandsTunnell.Converse.CuspSynthesis

-- @@ L324-324 verbatim
open MeasureTheory Topology

-- @@ L325-325 verbatim
section TorusMeasure

-- @@ L326-326 verbatim
variable {K : Type} [Field K] [NumberField K]


-- @@ L328-330 verbatim
def torusPoint {S : Finset (HeightOneSpectrum (𝓞 K))} (g : AdelicGL2 (𝓞 K) K)
    (p : ↥(torusClass (K := K) S) × ℝ) : AdelicGL2 (𝓞 K) K :=
  diagOne (((torusLift p.1 : ↥(normOneIdeles K)) : (AdeleRing (𝓞 K) K)ˣ) * Ideles.archScale K p.2) * g

-- @@ L331-331 verbatim
end TorusMeasure

-- @@ L332-332 verbatim
end LanglandsTunnell.Converse.CuspSynthesis

-- @@ L333-333 verbatim
end


-- @@ L335-335 verbatim
namespace LanglandsTunnell.Converse.CuspSynthesis


-- @@ L337-337 verbatim
noncomputable section


-- @@ L339-339 verbatim
section DualSeries


-- @@ L341-341 verbatim
variable {K : Type} [Field K] [NumberField K]

-- @@ L342-342 verbatim
variable {S : Finset (HeightOneSpectrum (𝓞 K))} {Pi : HeckeEigensystem K ℂ}

-- @@ L343-343 verbatim
variable {epsS : ∀ v : HeightOneSpectrum (𝓞 K), (v.adicCompletion K)ˣ →* ℂˣ} {ω : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ}


-- @@ L345-345 verbatim
open scoped Classical

-- @@ L346-346 verbatim
open scoped WithZero

-- @@ L347-347 verbatim
open LanglandsTunnell.TateLocal NumberField.StandardAddChar NumberField.InfinitePlace UnramifiedWhittaker


-- @@ L349-359 verbatim
variable (K) in

def weylGL2 : GL (Fin 2) K where
  val := !![0, 1; -1, 0]
  inv := !![0, -1; 1, 0]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]


-- @@ L361-362 verbatim
omit [NumberField K] in
theorem weylGL2_coe : ((weylGL2 K : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := rfl


-- @@ L364-364 verbatim
def weylA (d : JLData K S epsS ω) : GL (Fin 2) K := weylGL2 K * diagOne (-d.A)


-- @@ L366-370 verbatim
theorem weylA_coe (d : JLData K S epsS ω) :
    ((weylA d : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; (d.A : K), 0] := by
  refine Matrix.ext fun i j => ?_
  simp only [weylA, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two, diagOne_coe_apply, weylGL2_coe]
  fin_cases i <;> fin_cases j <;> simp


-- @@ L372-379 verbatim
def dualSeriesTerm (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) (g : AdelicGL2 (𝓞 K) K) (α : Kˣ) : ℂ :=
  d.ad α * d.epsChar g * archW' archR archC dR dC (globalPoints (𝓞 K) K (diagOne α * weylA d) * g)
    * dF.Wf (globalPoints (𝓞 K) K (diagOne α * weylA d) * g)


-- @@ L381-387 verbatim
def dualSeries' (d : JLData K S epsS ω)
    (archR : ∀ w : InfinitePlace K, w.IsReal → RealArchParam)
    (archC : ∀ w : InfinitePlace K, w.IsComplex → ComplexArchParam)
    (dR : ∀ (w : InfinitePlace K) (hw : w.IsReal), ArchDatumR (archR w hw))
    (dC : ∀ (w : InfinitePlace K) (hw : w.IsComplex), ArchDatumC (archC w hw))
    (dF : FinWhittakerDatum K S Pi) (g : AdelicGL2 (𝓞 K) K) : ℂ :=
  ∑' α : Kˣ, dualSeriesTerm d archR archC dR dC dF g α


-- @@ L389-389 verbatim
end DualSeries


-- @@ L391-391 verbatim
end


-- @@ L393-393 verbatim
end LanglandsTunnell.Converse.CuspSynthesis
