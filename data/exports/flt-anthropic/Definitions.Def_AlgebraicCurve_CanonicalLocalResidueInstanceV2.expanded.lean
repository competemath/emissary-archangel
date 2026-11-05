import Mathlib
import Definitions.Def_AlgebraicCurve_LocalResidue
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_DivisorPushPull
import Definitions.Def_AlgebraicCurve_PlaceCompletion
import Definitions.Def_AlgebraicCurve_WeilOfKaehler


-- @@ L8-8 verbatim
set_option autoImplicit false

-- @@ L9-9 verbatim
set_option maxHeartbeats 1600000


-- @@ L11-11 verbatim
set_option autoImplicit false


-- @@ L13-13 verbatim
noncomputable section


-- @@ L15-15 verbatim
namespace AlgebraicCurve


-- @@ L17-17 verbatim
variable {K F : Type*} [Field K] [Field F] [Algebra K F]


-- @@ L19-23 verbatim
instance HasSeparableResidue.of_perfectField [PerfectField K]
    [∀ v : Place K F, v.FiniteResidue] : HasSeparableResidue K F where
  trace_ne_zero v :=
    haveI : Module.Finite K v.ResidueField := Place.FiniteResidue.finite
    Algebra.trace_ne_zero K v.ResidueField


-- @@ L25-27 verbatim
instance HasSeparableResidue.of_perfectField_of_isCurveOver [PerfectField K]
    [IsCurveOver K F] : HasSeparableResidue K F :=
  HasSeparableResidue.of_perfectField


-- @@ L29-29 verbatim
section PerfectDischarge


-- @@ L31-32 verbatim
variable [HasCanonicalLocalResidueKStar K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates] [Nontrivial Ω[F⁄K]]


-- @@ L34-34 verbatim
end PerfectDischarge


-- @@ L36-36 verbatim
end AlgebraicCurve


-- @@ L38-38 verbatim
end


-- @@ L40-40 verbatim
set_option autoImplicit false

-- @@ L41-41 verbatim
set_option linter.unusedSectionVars false

-- @@ L42-42 verbatim
set_option maxHeartbeats 400000

-- @@ L43-43 verbatim
set_option synthInstance.maxHeartbeats 400000

-- @@ L44-44 verbatim
set_option maxRecDepth 4000


-- @@ L46-46 verbatim
noncomputable section


-- @@ L48-48 verbatim
open Polynomial IntermediateField


-- @@ L50-50 verbatim
namespace ModularCurve.Ldgr37Ch


-- @@ L52-52 verbatim
universe u v


-- @@ L54-54 verbatim
section HenselEngine


-- @@ L56-56 verbatim
variable {R : Type u} [CommRing R] [HenselianLocalRing R]

-- @@ L57-57 verbatim
variable {F : Type v} [Field F] [Algebra F (IsLocalRing.ResidueField R)]

-- @@ L58-58 verbatim
variable (i : F →+* R)

-- @@ L59-60 verbatim
variable (hi : (IsLocalRing.residue R).comp i
  = algebraMap F (IsLocalRing.ResidueField R))

-- @@ L61-61 verbatim
variable (abar : IsLocalRing.ResidueField R)


-- @@ L63-63 verbatim
include hi


-- @@ L65-65 verbatim
end HenselEngine


-- @@ L67-67 verbatim
section CoefficientEmbedding


-- @@ L69-69 verbatim
variable {R : Type u} [CommRing R] [HenselianLocalRing R]

-- @@ L70-70 verbatim
variable {F : Type v} [Field F] [Algebra F (IsLocalRing.ResidueField R)]

-- @@ L71-71 verbatim
variable (i : F →+* R)

-- @@ L72-73 verbatim
variable (hi : (IsLocalRing.residue R).comp i
  = algebraMap F (IsLocalRing.ResidueField R))

-- @@ L74-74 verbatim
variable (abar : IsLocalRing.ResidueField R)


-- @@ L76-76 verbatim
include hi


-- @@ L78-78 verbatim
end CoefficientEmbedding


-- @@ L80-80 verbatim
section SectionIdentity


-- @@ L82-82 verbatim
variable {R : Type u} [CommRing R] [HenselianLocalRing R]

-- @@ L83-83 verbatim
variable {F : Type v} [Field F] [Algebra F (IsLocalRing.ResidueField R)]

-- @@ L84-84 verbatim
variable (i : F →+* R)

-- @@ L85-86 verbatim
variable (hi : (IsLocalRing.residue R).comp i
  = algebraMap F (IsLocalRing.ResidueField R))

-- @@ L87-87 verbatim
variable (abar : IsLocalRing.ResidueField R)


-- @@ L89-89 verbatim
include hi


-- @@ L91-91 verbatim
end SectionIdentity


-- @@ L93-93 verbatim
end ModularCurve.Ldgr37Ch


-- @@ L95-95 verbatim
end


-- @@ L97-97 verbatim
set_option autoImplicit false


-- @@ L99-99 verbatim
noncomputable section


-- @@ L101-101 verbatim
open IsDedekindDomain WithZero IsLocalRing

-- @@ L102-102 verbatim
open scoped Polynomial


-- @@ L104-104 verbatim
namespace AlgebraicCurve


-- @@ L106-106 verbatim
namespace Place


-- @@ L108-108 verbatim
section DegPos


-- @@ L110-110 verbatim
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)


-- @@ L112-113 verbatim
theorem finiteResidue_of_deg_pos (h : 0 < v.deg) : v.FiniteResidue :=
  ⟨Module.finite_of_finrank_pos h⟩


-- @@ L115-115 verbatim
end DegPos


-- @@ L117-117 verbatim
end Place


-- @@ L119-119 verbatim
namespace Place


-- @@ L121-121 verbatim
section Restrict


-- @@ L123-125 verbatim
variable {K F F' : Type*} [Field K] [Field F] [Field F']
  [Algebra K F'] [Algebra F F'] [Algebra K F] [IsScalarTower K F F']
  [Algebra.IsIntegral F F'] (w : Place K F')


-- @@ L127-131 verbatim
def restrictSubringHom : (w.restrict F).toValuationSubring →+* w.toValuationSubring :=
  RingHom.codRestrict
    ((algebraMap F F').comp (w.restrict F).toValuationSubring.subtype)
    w.toValuationSubring.toSubring
    fun x => x.2


-- @@ L133-153 verbatim
instance instIsLocalHom_restrictSubringHom : IsLocalHom (w.restrictSubringHom (F := F)) := by
  constructor
  intro a ha

  obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.mp ha
  have hb' : algebraMap F F' (a : F) * (b : F') = 1 := by
    exact congrArg Subtype.val hb
  have ha0 : (a : F) ≠ 0 := by
    rintro h0
    rw [h0, map_zero, zero_mul] at hb'
    exact zero_ne_one hb'

  have hbeq : (b : F') = algebraMap F F' (a : F)⁻¹ := by
    rw [map_inv₀]
    exact eq_inv_of_mul_eq_one_right (by linear_combination hb')

  have hmem : (a : F)⁻¹ ∈ (w.restrict F).toValuationSubring := by
    show algebraMap F F' (a : F)⁻¹ ∈ w.toValuationSubring
    exact hbeq ▸ b.2
  exact isUnit_iff_exists_inv.mpr
    ⟨⟨(a : F)⁻¹, hmem⟩, Subtype.ext (mul_inv_cancel₀ ha0)⟩


-- @@ L155-156 verbatim
def residueFieldMapRestrict : (w.restrict F).ResidueField →+* w.ResidueField :=
  IsLocalRing.ResidueField.map (w.restrictSubringHom (F := F))


-- @@ L158-159 verbatim
instance instAlgebra_restrictResidueField : Algebra (w.restrict F).ResidueField w.ResidueField :=
  (w.residueFieldMapRestrict (F := F)).toAlgebra


-- @@ L161-165 verbatim
theorem algebraMap_residueField_residue (x : (w.restrict F).toValuationSubring) :
    algebraMap (w.restrict F).ResidueField w.ResidueField
        (IsLocalRing.residue _ x)
      = IsLocalRing.residue _ (w.restrictSubringHom x) :=
  IsLocalRing.ResidueField.map_residue _ _


-- @@ L167-176 verbatim
instance instIsScalarTower_restrictResidueField : IsScalarTower K (w.restrict F).ResidueField w.ResidueField := by
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  show IsLocalRing.residue _ (algebraMap K w.toValuationSubring a)
      = algebraMap (w.restrict F).ResidueField w.ResidueField
          (IsLocalRing.residue _ (algebraMap K (w.restrict F).toValuationSubring a))
  rw [algebraMap_residueField_residue]
  congr 1
  ext
  show algebraMap K F' a = algebraMap F F' (algebraMap K F a)
  rw [IsScalarTower.algebraMap_apply K F F']


-- @@ L178-178 verbatim
end Restrict


-- @@ L180-180 verbatim
end Place

-- @@ L181-181 verbatim
end AlgebraicCurve


-- @@ L183-183 verbatim
end


-- @@ L185-185 verbatim
set_option autoImplicit false


-- @@ L187-187 verbatim
noncomputable section


-- @@ L189-189 verbatim
open IsDedekindDomain WithZero Module IsLocalRing


-- @@ L191-191 verbatim
namespace AlgebraicCurve


-- @@ L193-193 verbatim
variable {K F : Type*} [Field K] [Field F] [Algebra K F]


-- @@ L195-195 verbatim
namespace Place


-- @@ L197-197 verbatim
variable (v : Place K F)


-- @@ L199-200 verbatim
def uniformizerSubring : v.toValuationSubring :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose


-- @@ L202-203 verbatim
@[simp]
theorem coe_uniformizerSubring : (v.uniformizerSubring : F) = v.uniformizer := rfl


-- @@ L205-206 verbatim
theorem irreducible_uniformizerSubring : Irreducible v.uniformizerSubring :=
  (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec


-- @@ L208-221 verbatim
private theorem ord_nonneg_of_mem {f : F} (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg (Subtype.val) hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n


-- @@ L223-229 verbatim
private theorem mem_of_ord_nonneg {f : F} (hf : f ≠ 0) (h : 0 ≤ v.ord f) :
    f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)


-- @@ L231-233 verbatim
private theorem mem_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f :=
  ⟨v.ord_nonneg_of_mem, v.mem_of_ord_nonneg hf⟩


-- @@ L235-237 verbatim
theorem uniformizerSubring_mem_maximalIdeal :
    v.uniformizerSubring ∈ IsLocalRing.maximalIdeal v.toValuationSubring :=
  (IsLocalRing.mem_maximalIdeal _).mpr v.irreducible_uniformizerSubring.not_isUnit


-- @@ L239-240 verbatim
theorem uniformizer_mem : v.uniformizer ∈ v.toValuationSubring :=
  v.uniformizerSubring.2


-- @@ L242-250 verbatim
def simplePoleSubmodule : Submodule K F where
  carrier := {f | v.uniformizer * f ∈ v.toValuationSubring}
  add_mem' {f g} hf hg := by
    simpa only [Set.mem_setOf_eq, mul_add] using add_mem hf hg
  zero_mem' := by simpa only [Set.mem_setOf_eq, mul_zero] using zero_mem _
  smul_mem' c f hf := by
    show v.uniformizer * (c • f) ∈ v.toValuationSubring
    rw [Algebra.smul_def, mul_left_comm]
    exact mul_mem (v.algebraMap_mem' c) hf


-- @@ L252-254 verbatim
@[simp]
theorem mem_simplePoleSubmodule {f : F} :
    f ∈ v.simplePoleSubmodule ↔ v.uniformizer * f ∈ v.toValuationSubring := Iff.rfl


-- @@ L256-258 verbatim
theorem mem_simplePoleSubmodule_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    f ∈ v.simplePoleSubmodule :=
  mul_mem v.uniformizer_mem hf


-- @@ L260-267 verbatim
def simplePoleMulUniformizer : v.simplePoleSubmodule →ₗ[K] v.toValuationSubring where
  toFun f := ⟨v.uniformizer * f.1, f.2⟩
  map_add' f g := Subtype.ext (mul_add _ _ _)
  map_smul' c f := Subtype.ext <| by
    show v.uniformizer * ((c • f : v.simplePoleSubmodule) : F)
        = ((c • ⟨v.uniformizer * f.1, f.2⟩ : v.toValuationSubring) : F)
    simp only [Algebra.smul_def, MulMemClass.coe_mul, v.coe_algebraMap, Submodule.coe_smul,
      mul_left_comm]


-- @@ L269-271 verbatim
def simplePoleResidueAux : v.simplePoleSubmodule →ₗ[K] v.ResidueField :=
  (Ideal.Quotient.mkₐ K (IsLocalRing.maximalIdeal v.toValuationSubring)).toLinearMap
    ∘ₗ v.simplePoleMulUniformizer


-- @@ L273-274 verbatim
theorem simplePoleResidueAux_apply (f : v.simplePoleSubmodule) :
    v.simplePoleResidueAux f = IsLocalRing.residue _ ⟨v.uniformizer * f.1, f.2⟩ := rfl


-- @@ L276-283 verbatim
theorem simplePoleResidueAux_eq_zero_of_mem {f : F} (hf : f ∈ v.toValuationSubring) :
    v.simplePoleResidueAux ⟨f, v.mem_simplePoleSubmodule_of_mem hf⟩ = 0 := by
  rw [simplePoleResidueAux_apply, IsLocalRing.residue_eq_zero_iff]

  have hmul : (⟨v.uniformizer * f, mul_mem v.uniformizer_mem hf⟩ : v.toValuationSubring)
      = v.uniformizerSubring * ⟨f, hf⟩ := Subtype.ext rfl
  rw [hmul]
  exact Ideal.mul_mem_right _ _ v.uniformizerSubring_mem_maximalIdeal


-- @@ L285-286 verbatim
def localResidueExtend : F →ₗ[K] v.ResidueField :=
  v.simplePoleResidueAux.exists_extend.choose


-- @@ L288-291 verbatim
theorem localResidueExtend_apply_of_mem {f : F} (hf : f ∈ v.simplePoleSubmodule) :
    v.localResidueExtend f = v.simplePoleResidueAux ⟨f, hf⟩ :=
  congrArg (fun φ => φ (⟨f, hf⟩ : v.simplePoleSubmodule))
    v.simplePoleResidueAux.exists_extend.choose_spec


-- @@ L293-299 verbatim
def localResidueDataOfExtend : v.LocalResidueData where
  res := v.localResidueExtend
  res_of_mem f hf := by
    rw [v.localResidueExtend_apply_of_mem (v.mem_simplePoleSubmodule_of_mem hf),
      v.simplePoleResidueAux_eq_zero_of_mem hf]
  res_simplePole f hf := by
    rw [v.localResidueExtend_apply_of_mem hf, simplePoleResidueAux_apply]


-- @@ L301-301 verbatim
end Place


-- @@ L303-304 verbatim
instance instHasLocalResidue : HasLocalResidue K F where
  exists_data v := ⟨v.localResidueDataOfExtend⟩


-- @@ L306-306 verbatim
variable [HasCanonicalLocalResidueKStar K F]


-- @@ L308-310 verbatim
theorem gate_hasLocalResidue_uniformizer_inv (v : Place K F) :
    v.localResidue v.uniformizer⁻¹ = 1 :=
  v.gate_localResidue_uniformizer_inv


-- @@ L312-320 verbatim
theorem gate_uniformizer_inv_mem_simplePoleSubmodule (v : Place K F) :
    v.uniformizer⁻¹ ∈ v.simplePoleSubmodule ∧ v.uniformizer⁻¹ ∉ v.toValuationSubring := by
  refine ⟨?_, ?_⟩
  · rw [Place.mem_simplePoleSubmodule, mul_inv_cancel₀ v.uniformizer_ne_zero]
    exact one_mem _
  · intro hmem
    have h0 := v.ord_nonneg_of_mem hmem
    rw [v.ord_inv, v.ord_uniformizer] at h0
    omega


-- @@ L322-322 verbatim
end AlgebraicCurve


-- @@ L324-324 verbatim
end


-- @@ L326-326 verbatim
set_option autoImplicit false


-- @@ L328-328 verbatim
noncomputable section


-- @@ L330-330 verbatim
open IsDedekindDomain WithZero Module IsLocalRing


-- @@ L332-332 verbatim
namespace AlgebraicCurve


-- @@ L334-334 verbatim
variable {K F : Type*} [Field K] [Field F] [Algebra K F]


-- @@ L336-336 verbatim
namespace Place


-- @@ L338-338 verbatim
variable (v : Place K F)


-- @@ L340-348 verbatim
def poleSubmodule (n : ℕ) : Submodule K F where
  carrier := {f | v.uniformizer ^ n * f ∈ v.toValuationSubring}
  add_mem' {f g} hf hg := by
    simpa only [Set.mem_setOf_eq, mul_add] using add_mem hf hg
  zero_mem' := by simpa only [Set.mem_setOf_eq, mul_zero] using zero_mem _
  smul_mem' c f hf := by
    show v.uniformizer ^ n * (c • f) ∈ v.toValuationSubring
    rw [Algebra.smul_def, mul_left_comm]
    exact mul_mem (v.algebraMap_mem' c) hf


-- @@ L350-352 verbatim
@[simp]
theorem mem_poleSubmodule {n : ℕ} {f : F} :
    f ∈ v.poleSubmodule n ↔ v.uniformizer ^ n * f ∈ v.toValuationSubring := Iff.rfl


-- @@ L354-355 verbatim
theorem uniformizer_pow_ne_zero (n : ℕ) : (v.uniformizer ^ n : F) ≠ 0 :=
  pow_ne_zero n v.uniformizer_ne_zero


-- @@ L357-359 verbatim
theorem ord_uniformizer_pow (n : ℕ) : v.ord (v.uniformizer ^ n) = (n : ℤ) := by
  rw [show (v.uniformizer ^ n : F) = v.uniformizer ^ (n : ℤ) from (zpow_natCast _ n).symm,
    v.ord_zpow, v.ord_uniformizer, mul_one]


-- @@ L361-363 verbatim
theorem coe_poleSubmodule_zero :
    (v.poleSubmodule 0 : Set F) = (v.toValuationSubring : Set F) := by
  ext f; simp [mem_poleSubmodule]


-- @@ L365-367 verbatim
@[simp]
theorem poleSubmodule_one : v.poleSubmodule 1 = v.simplePoleSubmodule := by
  ext f; simp [mem_poleSubmodule, mem_simplePoleSubmodule]


-- @@ L369-373 verbatim
theorem mem_poleSubmodule_iff_ord {n : ℕ} {f : F} (hf : f ≠ 0) :
    f ∈ v.poleSubmodule n ↔ -(n : ℤ) ≤ v.ord f := by
  rw [mem_poleSubmodule, v.mem_iff_ord_nonneg (mul_ne_zero (v.uniformizer_pow_ne_zero n) hf),
    v.ord_mul (v.uniformizer_pow_ne_zero n) hf, v.ord_uniformizer_pow]
  omega


-- @@ L375-381 verbatim
theorem poleSubmodule_mono : Monotone v.poleSubmodule := by
  intro m n hmn f hf
  rcases eq_or_ne f 0 with rfl | hf0
  · exact zero_mem _
  · rw [v.mem_poleSubmodule_iff_ord hf0] at hf ⊢
    have : -(n : ℤ) ≤ -(m : ℤ) := by exact_mod_cast neg_le_neg (Nat.cast_le.mpr hmn)
    omega


-- @@ L383-391 verbatim
theorem iSup_poleSubmodule_eq_top : ⨆ n, v.poleSubmodule n = ⊤ := by
  rw [eq_top_iff]
  intro f _
  rcases eq_or_ne f 0 with rfl | hf0
  · exact Submodule.mem_iSup_of_mem 0 (zero_mem _)
  · refine Submodule.mem_iSup_of_mem (-v.ord f).toNat ?_
    rw [v.mem_poleSubmodule_iff_ord hf0]
    have h := Int.self_le_toNat (-v.ord f)
    omega


-- @@ L393-400 verbatim
def poleMulUniformizerPow (n : ℕ) : v.poleSubmodule n →ₗ[K] v.toValuationSubring where
  toFun f := ⟨v.uniformizer ^ n * f.1, f.2⟩
  map_add' f g := Subtype.ext (mul_add _ _ _)
  map_smul' c f := Subtype.ext <| by
    show v.uniformizer ^ n * ((c • f : v.poleSubmodule n) : F)
        = ((c • ⟨v.uniformizer ^ n * f.1, f.2⟩ : v.toValuationSubring) : F)
    simp only [Algebra.smul_def, MulMemClass.coe_mul, v.coe_algebraMap, Submodule.coe_smul,
      mul_left_comm]


-- @@ L402-404 verbatim
def laurentTailCoeff (n : ℕ) : v.poleSubmodule n →ₗ[K] v.ResidueField :=
  (Ideal.Quotient.mkₐ K (IsLocalRing.maximalIdeal v.toValuationSubring)).toLinearMap
    ∘ₗ v.poleMulUniformizerPow n


-- @@ L406-407 verbatim
theorem laurentTailCoeff_apply {n : ℕ} (f : v.poleSubmodule n) :
    v.laurentTailCoeff n f = IsLocalRing.residue _ ⟨v.uniformizer ^ n * f.1, f.2⟩ := rfl


-- @@ L409-412 verbatim
theorem coe_mul_uniformizer_pow_inv_mem_poleSubmodule {n : ℕ} (c : v.toValuationSubring) :
    (c : F) * (v.uniformizer ^ n)⁻¹ ∈ v.poleSubmodule n := by
  rw [mem_poleSubmodule, mul_left_comm, mul_inv_cancel₀ (v.uniformizer_pow_ne_zero n), mul_one]
  exact c.2


-- @@ L414-439 verbatim
theorem laurentTail_remainder_mem_poleSubmodule {n : ℕ} {f : F}
    (hf : f ∈ v.poleSubmodule (n + 1)) {c : v.toValuationSubring}
    (hc : IsLocalRing.residue _ c = v.laurentTailCoeff (n + 1) ⟨f, hf⟩) :
    f - (c : F) * (v.uniformizer ^ (n + 1))⁻¹ ∈ v.poleSubmodule n := by

  set a : v.toValuationSubring := ⟨v.uniformizer ^ (n + 1) * f, hf⟩ with ha_def
  have hmem : a - c ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, hc, laurentTailCoeff_apply, sub_self]
  rw [v.irreducible_uniformizerSubring.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
  obtain ⟨d, hd⟩ := hmem

  rw [mem_poleSubmodule]
  have hcoe : v.uniformizer ^ (n + 1) * f - (c : F) = v.uniformizer * (d : F) := by
    have h := congrArg (Subtype.val) hd
    push_cast [coe_uniformizerSubring] at h
    exact h
  have hkey : v.uniformizer ^ n * (f - (c : F) * (v.uniformizer ^ (n + 1))⁻¹) = (d : F) := by
    refine mul_left_cancel₀ v.uniformizer_ne_zero ?_
    calc v.uniformizer * (v.uniformizer ^ n * (f - (c : F) * (v.uniformizer ^ (n + 1))⁻¹))
        = v.uniformizer ^ (n + 1) * f
            - (c : F) * (v.uniformizer ^ (n + 1) * (v.uniformizer ^ (n + 1))⁻¹) := by ring
      _ = v.uniformizer ^ (n + 1) * f - (c : F) := by
          rw [mul_inv_cancel₀ (v.uniformizer_pow_ne_zero (n + 1)), mul_one]
      _ = v.uniformizer * (d : F) := hcoe
  rw [hkey]
  exact d.2


-- @@ L441-443 verbatim
theorem localResidueData_agree_on_simplePole (R₁ R₂ : v.LocalResidueData) {f : F}
    (hf : f ∈ v.simplePoleSubmodule) : R₁.res f = R₂.res f := by
  rw [R₁.res_simplePole f hf, R₂.res_simplePole f hf]


-- @@ L445-447 verbatim
theorem localResidueData_res_eq_simplePoleResidueAux (R : v.LocalResidueData) {f : F}
    (hf : f ∈ v.simplePoleSubmodule) : R.res f = v.simplePoleResidueAux ⟨f, hf⟩ := by
  rw [R.res_simplePole f hf, simplePoleResidueAux_apply]


-- @@ L449-449 verbatim
end Place


-- @@ L451-459 verbatim
theorem gate_poleSubmodule_strictMono (v : Place K F) (n : ℕ) :
    (v.uniformizer ^ (n + 1))⁻¹ ∈ v.poleSubmodule (n + 1) ∧
      (v.uniformizer ^ (n + 1))⁻¹ ∉ v.poleSubmodule n := by
  refine ⟨?_, ?_⟩
  · rw [Place.mem_poleSubmodule, mul_inv_cancel₀ (v.uniformizer_pow_ne_zero (n + 1))]
    exact one_mem _
  · rw [v.mem_poleSubmodule_iff_ord (inv_ne_zero (v.uniformizer_pow_ne_zero (n + 1))),
      v.ord_inv, v.ord_uniformizer_pow]
    omega

-- @@ L460-460 verbatim
end AlgebraicCurve


-- @@ L462-462 verbatim
end


-- @@ L464-464 verbatim
set_option autoImplicit false


-- @@ L466-466 verbatim
noncomputable section


-- @@ L468-468 verbatim
open IsDedekindDomain WithZero Module IsLocalRing


-- @@ L470-470 verbatim
namespace AlgebraicCurve


-- @@ L472-472 verbatim
variable {K F : Type*} [Field K] [Field F] [Algebra K F]


-- @@ L474-474 verbatim
namespace Place


-- @@ L476-476 verbatim
variable (v : Place K F)


-- @@ L478-484 verbatim
theorem exists_mem_poleSubmodule (f : F) : ∃ n, f ∈ v.poleSubmodule n := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, zero_mem _⟩
  · refine ⟨(-v.ord f).toNat, ?_⟩
    rw [v.mem_poleSubmodule_iff_ord hf0]
    have h := Int.self_le_toNat (-v.ord f)
    omega


-- @@ L486-495 verbatim
theorem laurentTailCoeff_coe_mul_uniformizer_pow_inv {n : ℕ} (c : v.toValuationSubring) :
    v.laurentTailCoeff (n + 1)
        ⟨(c : F) * (v.uniformizer ^ (n + 1))⁻¹,
          v.coe_mul_uniformizer_pow_inv_mem_poleSubmodule c⟩
      = IsLocalRing.residue _ c := by
  rw [laurentTailCoeff_apply]
  congr 1
  exact Subtype.ext <| by
    show v.uniformizer ^ (n + 1) * ((c : F) * (v.uniformizer ^ (n + 1))⁻¹) = (c : F)
    rw [mul_left_comm, mul_inv_cancel₀ (v.uniformizer_pow_ne_zero (n + 1)), mul_one]


-- @@ L497-497 verbatim
end Place


-- @@ L499-499 verbatim
namespace Place


-- @@ L501-501 verbatim
variable (v : Place K F)


-- @@ L503-503 verbatim
end Place


-- @@ L505-505 verbatim
end AlgebraicCurve


-- @@ L507-507 verbatim
end


-- @@ L509-509 verbatim
set_option autoImplicit false


-- @@ L511-511 verbatim
noncomputable section


-- @@ L513-513 verbatim
open IsDedekindDomain WithZero Module IsLocalRing


-- @@ L515-515 verbatim
namespace AlgebraicCurve


-- @@ L517-517 verbatim
variable {K F : Type*} [Field K] [Field F] [Algebra K F]


-- @@ L519-519 verbatim
namespace Place


-- @@ L521-521 verbatim
variable (v : Place K F)


-- @@ L523-525 verbatim
theorem uniformizer_mul_uniformizer_sq_inv :
    (v.uniformizer : F) * (v.uniformizer ^ 2)⁻¹ = v.uniformizer⁻¹ := by
  rw [sq, mul_inv, ← mul_assoc, mul_inv_cancel₀ v.uniformizer_ne_zero, one_mul]


-- @@ L527-527 verbatim
end Place


-- @@ L529-529 verbatim
namespace Place


-- @@ L531-531 verbatim
variable (v : Place K F)


-- @@ L533-538 verbatim
theorem CanonicalLocalResidueDataK.res_algebraMap_mul_uniformizer_pow_inv
    (R : v.CanonicalLocalResidueDataK) {n : ℕ} (hn : 1 ≤ n) (c : K) :
    R.res ((algebraMap K F c) * (v.uniformizer ^ (n + 1))⁻¹) = 0 := by
  have h : (algebraMap K F c) * (v.uniformizer ^ (n + 1))⁻¹
      = c • (v.uniformizer ^ (n + 1))⁻¹ := (Algebra.smul_def c _).symm
  rw [h, map_smul, R.res_higherPoleMonomial n hn, smul_zero]


-- @@ L540-543 verbatim
theorem CanonicalLocalResidueDataK.res_laurentRecK (R : v.CanonicalLocalResidueDataK)
    {n : ℕ} (hn : 1 ≤ n) (f : F) (c : K) :
    R.res (f - (algebraMap K F c) * (v.uniformizer ^ (n + 1))⁻¹) = R.res f := by
  rw [map_sub, R.res_algebraMap_mul_uniformizer_pow_inv v hn c, sub_zero]


-- @@ L545-545 verbatim
end Place


-- @@ L547-547 verbatim
end AlgebraicCurve


-- @@ L549-549 verbatim
end


-- @@ L551-551 verbatim
set_option autoImplicit false


-- @@ L553-553 verbatim
noncomputable section


-- @@ L555-555 verbatim
open IsDedekindDomain WithZero Module IsLocalRing


-- @@ L557-557 verbatim
namespace AlgebraicCurve


-- @@ L559-559 verbatim
variable {K F : Type*} [Field K] [Field F] [Algebra K F]


-- @@ L561-561 verbatim
namespace Place


-- @@ L563-563 verbatim
variable (v : Place K F)


-- @@ L565-567 verbatim
theorem uniformizer_pow_inv_mem_poleSubmodule_self (m : ℕ) :
    (v.uniformizer ^ (m + 2))⁻¹ ∈ v.poleSubmodule (m + 2) :=
  (gate_poleSubmodule_strictMono v (m + 1)).1


-- @@ L569-575 verbatim
theorem higherPoleMonomial_sum_mem_poleSubmodule {s : Finset ℕ} {N : ℕ}
    (hs : ∀ m ∈ s, m < N) (c : ℕ → K) :
    ∑ m ∈ s, c m • (v.uniformizer ^ (m + 2))⁻¹ ∈ v.poleSubmodule (N + 1) :=
  Submodule.sum_mem _ fun m hm =>
    Submodule.smul_mem _ _ <|
      v.poleSubmodule_mono (by have := hs m hm; omega)
        (v.uniformizer_pow_inv_mem_poleSubmodule_self m)


-- @@ L577-605 verbatim
theorem higherPoleMonomial_coeff_eq_zero_of_mem (s : Finset ℕ) (c : ℕ → K)
    (hmem : ∑ m ∈ s, c m • (v.uniformizer ^ (m + 2))⁻¹ ∈ v.poleSubmodule 1) :
    ∀ m ∈ s, c m = 0 := by
  induction s using Finset.induction_on_max with
  | empty => intro m hm; exact absurd hm (Finset.notMem_empty m)
  | insert N s hN ih =>
    have hNs : N ∉ s := fun h => absurd (hN N h) (lt_irrefl N)
    rw [Finset.sum_insert hNs] at hmem

    have hrest : ∑ m ∈ s, c m • (v.uniformizer ^ (m + 2))⁻¹ ∈ v.poleSubmodule (N + 1) :=
      v.higherPoleMonomial_sum_mem_poleSubmodule hN c

    have hwhole := v.poleSubmodule_mono (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero N)) hmem

    have htop : c N • (v.uniformizer ^ (N + 2))⁻¹ ∈ v.poleSubmodule (N + 1) := by
      have hsub := (v.poleSubmodule (N + 1)).sub_mem hwhole hrest
      rwa [add_sub_cancel_right] at hsub

    have hcN : c N = 0 := by
      by_contra hcN
      exact (gate_poleSubmodule_strictMono v (N + 1)).2 <|
        (inv_smul_smul₀ hcN ((v.uniformizer ^ (N + 2))⁻¹)) ▸
          (v.poleSubmodule (N + 1)).smul_mem (c N)⁻¹ htop

    intro m hm
    rcases Finset.mem_insert.mp hm with rfl | hm'
    · exact hcN
    · refine ih ?_ m hm'
      rwa [hcN, zero_smul, zero_add] at hmem


-- @@ L607-615 verbatim
theorem linearIndependent_higherPoleMonomial_mkQ :
    LinearIndependent K
      (fun m : ℕ => (v.poleSubmodule 1).mkQ ((v.uniformizer ^ (m + 2))⁻¹)) := by
  rw [linearIndependent_iff']
  intro s c hsum m hm
  refine v.higherPoleMonomial_coeff_eq_zero_of_mem s c ?_ m hm
  have h := hsum
  simp only [← map_smul, ← map_sum] at h
  rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h


-- @@ L617-622 verbatim
def higherPoleCorrectionAux :
    Submodule.span K
        (Set.range fun m : ℕ => (v.poleSubmodule 1).mkQ ((v.uniformizer ^ (m + 2))⁻¹))
      →ₗ[K] v.ResidueField :=
  (Basis.span v.linearIndependent_higherPoleMonomial_mkQ).constr K
    (fun m => v.localResidueExtend ((v.uniformizer ^ (m + 2))⁻¹))


-- @@ L624-625 verbatim
def higherPoleCorrection : F →ₗ[K] v.ResidueField :=
  v.higherPoleCorrectionAux.exists_extend.choose ∘ₗ (v.poleSubmodule 1).mkQ


-- @@ L627-631 verbatim
theorem higherPoleCorrection_apply_of_mem {f : F} (hf : f ∈ v.poleSubmodule 1) :
    v.higherPoleCorrection f = 0 := by
  unfold higherPoleCorrection
  rw [LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).mpr hf,
    map_zero]


-- @@ L633-649 verbatim
theorem higherPoleCorrection_uniformizer_pow_inv (m : ℕ) :
    v.higherPoleCorrection ((v.uniformizer ^ (m + 2))⁻¹)
      = v.localResidueExtend ((v.uniformizer ^ (m + 2))⁻¹) := by

  have hmem : (v.poleSubmodule 1).mkQ ((v.uniformizer ^ (m + 2))⁻¹)
      ∈ Submodule.span K
          (Set.range fun m : ℕ => (v.poleSubmodule 1).mkQ ((v.uniformizer ^ (m + 2))⁻¹)) :=
    Submodule.subset_span ⟨m, rfl⟩
  have hext := DFunLike.congr_fun v.higherPoleCorrectionAux.exists_extend.choose_spec
    ⟨(v.poleSubmodule 1).mkQ ((v.uniformizer ^ (m + 2))⁻¹), hmem⟩

  refine hext.trans ?_

  unfold higherPoleCorrectionAux
  have hb := (Basis.span v.linearIndependent_higherPoleMonomial_mkQ).constr_basis K
    (fun m => v.localResidueExtend ((v.uniformizer ^ (m + 2))⁻¹)) m
  rwa [Basis.span_apply] at hb


-- @@ L651-666 verbatim
def canonicalLocalResidueDataKOfExtend : v.CanonicalLocalResidueDataK where
  res := v.localResidueExtend - v.higherPoleCorrection
  res_of_mem f hf := by
    have h1 : f ∈ v.poleSubmodule 1 :=
      v.poleSubmodule_one ▸ v.mem_simplePoleSubmodule_of_mem hf
    rw [LinearMap.sub_apply, v.higherPoleCorrection_apply_of_mem h1, sub_zero,
      v.localResidueExtend_apply_of_mem (v.mem_simplePoleSubmodule_of_mem hf),
      v.simplePoleResidueAux_eq_zero_of_mem hf]
  res_simplePole f hf := by
    have h1 : f ∈ v.poleSubmodule 1 := v.poleSubmodule_one ▸ hf
    rw [LinearMap.sub_apply, v.higherPoleCorrection_apply_of_mem h1, sub_zero,
      v.localResidueExtend_apply_of_mem hf, simplePoleResidueAux_apply]
  res_higherPoleMonomial n hn := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [show 1 + m + 1 = m + 2 from by omega, LinearMap.sub_apply,
      v.higherPoleCorrection_uniformizer_pow_inv m, sub_self]


-- @@ L668-668 verbatim
end Place


-- @@ L670-671 verbatim
instance instHasCanonicalLocalResidueK : HasCanonicalLocalResidueK K F where
  exists_data v := ⟨v.canonicalLocalResidueDataKOfExtend⟩


-- @@ L673-673 verbatim
namespace Place


-- @@ L675-675 verbatim
variable (v : Place K F)


-- @@ L677-702 verbatim
theorem canonicalLocalResidueDataK_agree_on_poleSubmodule_of_surj
    (hsurj : Function.Surjective (algebraMap K v.ResidueField))
    (R₁ R₂ : v.CanonicalLocalResidueDataK) (n : ℕ) {f : F} (hf : f ∈ v.poleSubmodule n) :
    R₁.res f = R₂.res f := by
  induction n generalizing f with
  | zero =>
    have hf' : f ∈ v.toValuationSubring := by
      rwa [show f ∈ v.toValuationSubring ↔ (f ∈ (v.poleSubmodule 0 : Set F))
        from (v.coe_poleSubmodule_zero ▸ Iff.rfl)]
    rw [R₁.res_of_mem f hf', R₂.res_of_mem f hf']
  | succ n ih =>
    rcases Nat.lt_or_ge n 1 with hn | hn
    ·
      interval_cases n
      exact v.localResidueData_agree_on_simplePole R₁.toLocalResidueData R₂.toLocalResidueData
        (v.poleSubmodule_one ▸ hf)
    ·
      obtain ⟨c, hc⟩ := hsurj (v.laurentTailCoeff (n + 1) ⟨f, hf⟩)
      have hclift : IsLocalRing.residue _ (algebraMap K v.toValuationSubring c)
          = v.laurentTailCoeff (n + 1) ⟨f, hf⟩ := by
        rw [← hc, IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
          IsLocalRing.ResidueField.algebraMap_eq]
      have hrem : f - (algebraMap K F c) * (v.uniformizer ^ (n + 1))⁻¹ ∈ v.poleSubmodule n := by
        have := v.laurentTail_remainder_mem_poleSubmodule hf hclift
        rwa [v.coe_algebraMap] at this
      rw [← R₁.res_laurentRecK v hn f c, ← R₂.res_laurentRecK v hn f c, ih hrem]


-- @@ L704-704 verbatim
end Place


-- @@ L706-706 verbatim
end AlgebraicCurve


-- @@ L708-708 verbatim
end


-- @@ L710-710 verbatim
set_option autoImplicit false


-- @@ L712-712 verbatim
noncomputable section


-- @@ L714-714 verbatim
open IsDedekindDomain WithZero Module IsLocalRing


-- @@ L716-716 verbatim
namespace AlgebraicCurve


-- @@ L718-718 verbatim
variable {K F : Type*} [Field K] [Field F] [Algebra K F]


-- @@ L720-720 verbatim
namespace Place


-- @@ L722-722 verbatim
variable (v : Place K F)


-- @@ L724-728 verbatim
structure CoefficientFieldSection where

  lift : v.ResidueField →ₐ[K] v.toValuationSubring

  residue_lift : ∀ a, IsLocalRing.residue _ (lift a) = a


-- @@ L730-734 verbatim
structure CanonicalLocalResidueDataS (σ : v.CoefficientFieldSection)
    extends v.LocalResidueData where

  res_higherPoleSectionMonomial : ∀ (n : ℕ), 1 ≤ n → ∀ a : v.ResidueField,
    res ((σ.lift a : F) * (v.uniformizer ^ (n + 1))⁻¹) = 0


-- @@ L736-736 verbatim
namespace CanonicalLocalResidueDataS


-- @@ L738-738 verbatim
variable {v} {σ : v.CoefficientFieldSection} (R : v.CanonicalLocalResidueDataS σ)


-- @@ L740-742 verbatim
theorem res_laurentRecS {n : ℕ} (hn : 1 ≤ n) (f : F) (a : v.ResidueField) :
    R.res (f - (σ.lift a : F) * (v.uniformizer ^ (n + 1))⁻¹) = R.res f := by
  rw [map_sub, R.res_higherPoleSectionMonomial n hn a, sub_zero]


-- @@ L744-744 verbatim
end CanonicalLocalResidueDataS


-- @@ L746-767 verbatim
theorem canonicalLocalResidueDataS_agree_on_poleSubmodule (σ : v.CoefficientFieldSection)
    (R₁ R₂ : v.CanonicalLocalResidueDataS σ) (n : ℕ) {f : F} (hf : f ∈ v.poleSubmodule n) :
    R₁.res f = R₂.res f := by
  induction n generalizing f with
  | zero =>
    have hf' : f ∈ v.toValuationSubring := by
      rwa [show f ∈ v.toValuationSubring ↔ (f ∈ (v.poleSubmodule 0 : Set F))
        from (v.coe_poleSubmodule_zero ▸ Iff.rfl)]
    rw [R₁.res_of_mem f hf', R₂.res_of_mem f hf']
  | succ n ih =>
    rcases Nat.lt_or_ge n 1 with hn | hn
    ·
      interval_cases n
      exact v.localResidueData_agree_on_simplePole R₁.toLocalResidueData R₂.toLocalResidueData
        (v.poleSubmodule_one ▸ hf)
    ·
      set a : v.ResidueField := v.laurentTailCoeff (n + 1) ⟨f, hf⟩ with ha_def
      have hclift : IsLocalRing.residue _ (σ.lift a)
          = v.laurentTailCoeff (n + 1) ⟨f, hf⟩ := σ.residue_lift a
      have hrem : f - (σ.lift a : F) * (v.uniformizer ^ (n + 1))⁻¹ ∈ v.poleSubmodule n :=
        v.laurentTail_remainder_mem_poleSubmodule hf hclift
      rw [← R₁.res_laurentRecS hn f a, ← R₂.res_laurentRecS hn f a, ih hrem]


-- @@ L769-783 verbatim
def coefficientFieldSectionOfBijective
    (hbij : Function.Bijective (algebraMap K v.ResidueField)) :
    v.CoefficientFieldSection where
  lift := (Algebra.ofId K v.toValuationSubring).comp
    (AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hbij).symm.toAlgHom
  residue_lift a := by
    simp only [AlgHom.coe_comp, Function.comp_apply]
    set c : K := (AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hbij).symm a with hc_def
    show IsLocalRing.residue _ (algebraMap K v.toValuationSubring c) = a

    rw [show IsLocalRing.residue _ (algebraMap K v.toValuationSubring c)
          = algebraMap K v.ResidueField c from by
        rw [IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
          IsLocalRing.ResidueField.algebraMap_eq]]
    exact (AlgEquiv.ofBijective (Algebra.ofId K v.ResidueField) hbij).apply_symm_apply a


-- @@ L785-785 verbatim
end Place


-- @@ L787-787 verbatim
end AlgebraicCurve


-- @@ L789-789 verbatim
end


-- @@ L791-791 verbatim
set_option autoImplicit false

-- @@ L792-792 verbatim
set_option linter.unusedSectionVars false

-- @@ L793-793 verbatim
set_option maxHeartbeats 800000

-- @@ L794-794 verbatim
set_option synthInstance.maxHeartbeats 400000

-- @@ L795-795 verbatim
set_option maxRecDepth 8000


-- @@ L797-797 verbatim
noncomputable section


-- @@ L799-799 verbatim
open IsDedekindDomain WithZero IsLocalRing Polynomial


-- @@ L801-801 verbatim
namespace ModularCurve.Ldgr35Cl


-- @@ L803-803 verbatim
open AlgebraicCurve


-- @@ L805-805 verbatim
end ModularCurve.Ldgr35Cl


-- @@ L807-807 verbatim
end


-- @@ L809-809 verbatim
set_option autoImplicit false

-- @@ L810-810 verbatim
set_option linter.unusedSectionVars false

-- @@ L811-811 verbatim
set_option maxHeartbeats 400000

-- @@ L812-812 verbatim
set_option maxRecDepth 8000


-- @@ L814-814 verbatim
noncomputable section


-- @@ L816-816 verbatim
open IsDedekindDomain WithZero Module IsLocalRing


-- @@ L818-818 verbatim
namespace ModularCurve.Ldgr35Cs


-- @@ L820-820 verbatim
open AlgebraicCurve


-- @@ L822-822 verbatim
end ModularCurve.Ldgr35Cs


-- @@ L824-824 verbatim
end


-- @@ L826-826 verbatim
set_option autoImplicit false


-- @@ L828-828 verbatim
noncomputable section


-- @@ L830-830 verbatim
open IsDedekindDomain WithZero Module IsLocalRing Polynomial

-- @@ L831-831 verbatim
open AlgebraicCurve

-- @@ L832-832 verbatim
open scoped Polynomial


-- @@ L834-834 verbatim
end


-- @@ L836-836 verbatim
set_option autoImplicit false

-- @@ L837-837 verbatim
set_option linter.unusedSectionVars false

-- @@ L838-838 verbatim
set_option maxHeartbeats 800000

-- @@ L839-839 verbatim
set_option synthInstance.maxHeartbeats 400000

-- @@ L840-840 verbatim
set_option maxRecDepth 8000


-- @@ L842-842 verbatim
noncomputable section


-- @@ L844-844 verbatim
open IsDedekindDomain WithZero IsLocalRing Polynomial


-- @@ L846-846 verbatim
namespace ModularCurve.Ldgr36Si


-- @@ L848-848 verbatim
open AlgebraicCurve


-- @@ L850-850 verbatim
section Generic


-- @@ L852-853 verbatim
variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']


-- @@ L855-855 verbatim
end Generic


-- @@ L857-857 verbatim
end ModularCurve.Ldgr36Si


-- @@ L859-859 verbatim
end


-- @@ L861-861 verbatim
set_option autoImplicit false

-- @@ L862-862 verbatim
set_option linter.unusedSectionVars false

-- @@ L863-863 verbatim
set_option maxHeartbeats 400000

-- @@ L864-864 verbatim
set_option maxRecDepth 8000


-- @@ L866-866 verbatim
noncomputable section


-- @@ L868-868 verbatim
open IsDedekindDomain WithZero Module IsLocalRing


-- @@ L870-870 verbatim
namespace ModularCurve.Ldgr36Rc


-- @@ L872-872 verbatim
open AlgebraicCurve

-- @@ L873-873 verbatim
open ModularCurve.Ldgr35Cs

-- @@ L874-874 verbatim
open ModularCurve.Ldgr35Cl


-- @@ L876-876 verbatim
section Restriction


-- @@ L878-879 verbatim
variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']


-- @@ L881-881 verbatim
end Restriction


-- @@ L883-883 verbatim
section ReCarve


-- @@ L885-886 verbatim
variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']


-- @@ L888-888 verbatim
end ReCarve


-- @@ L890-890 verbatim
section NoForkTies


-- @@ L892-893 verbatim
variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']


-- @@ L895-895 verbatim
end NoForkTies


-- @@ L897-897 verbatim
section PaymentRewire


-- @@ L899-901 verbatim
variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']
  [HasCanonicalLocalResidueKStar K F']


-- @@ L903-903 verbatim
end PaymentRewire


-- @@ L905-905 verbatim
section Supply


-- @@ L907-908 verbatim
variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']


-- @@ L910-910 verbatim
end Supply


-- @@ L912-912 verbatim
end ModularCurve.Ldgr36Rc


-- @@ L914-914 verbatim
end


-- @@ L916-916 verbatim
set_option autoImplicit false


-- @@ L918-918 verbatim
noncomputable section


-- @@ L920-920 verbatim
open IsDedekindDomain WithZero Module IsLocalRing Polynomial


-- @@ L922-922 verbatim
end


-- @@ L924-924 verbatim
set_option autoImplicit false

-- @@ L925-925 verbatim
set_option linter.unusedSectionVars false

-- @@ L926-926 verbatim
set_option maxHeartbeats 400000

-- @@ L927-927 verbatim
set_option maxRecDepth 8000


-- @@ L929-929 verbatim
noncomputable section


-- @@ L931-931 verbatim
open IsDedekindDomain WithZero Module IsLocalRing


-- @@ L933-933 verbatim
namespace ModularCurve.Lg37


-- @@ L935-935 verbatim
open AlgebraicCurve

-- @@ L936-936 verbatim
open ModularCurve.Ldgr36Si

-- @@ L937-937 verbatim
open ModularCurve.Ldgr36Rc

-- @@ L938-938 verbatim
open ModularCurve.Ldgr35Cs


-- @@ L940-940 verbatim
section CompletionCarrier


-- @@ L942-942 verbatim
variable {K F : Type*} [Field K] [Field F] [Algebra K F]


-- @@ L944-945 verbatim
abbrev lg37_completion (v : Place K F) : Type _ :=
  AdicCompletion (IsLocalRing.maximalIdeal v.toValuationSubring) v.toValuationSubring


-- @@ L947-949 verbatim
def lg37_residueHat (v : Place K F) :
    lg37_completion v →+* v.ResidueField :=
  (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal v.toValuationSubring)).toRingHom


-- @@ L951-954 verbatim
theorem lg37_residueHat_algebraMap (v : Place K F) (x : v.toValuationSubring) :
    lg37_residueHat v
        (algebraMap v.toValuationSubring (lg37_completion v) x)
      = IsLocalRing.residue v.toValuationSubring x := rfl


-- @@ L956-960 verbatim
structure Lg37CompletionSection (v : Place K F) where

  lift : v.ResidueField →ₐ[K] lg37_completion v

  residueHat_lift : ∀ a, lg37_residueHat v (lift a) = a


-- @@ L962-962 verbatim
end CompletionCarrier


-- @@ L964-964 verbatim
section MovedCarrier


-- @@ L966-967 verbatim
variable {K K' F' : Type*} [Field K] [Field K'] [Field F']
  [Algebra K K'] [Algebra K' F'] [Algebra K F'] [IsScalarTower K K' F']

-- @@ L968-968 verbatim
variable [HasCanonicalLocalResidueKStar K F']


-- @@ L970-970 verbatim
end MovedCarrier


-- @@ L972-972 verbatim
end ModularCurve.Lg37


-- @@ L974-974 verbatim
end


-- @@ L976-976 verbatim
set_option autoImplicit false

-- @@ L977-977 verbatim
set_option linter.unusedSectionVars false

-- @@ L978-978 verbatim
set_option maxHeartbeats 400000

-- @@ L979-979 verbatim
set_option synthInstance.maxHeartbeats 400000


-- @@ L981-981 verbatim
noncomputable section


-- @@ L983-983 verbatim
open IsDedekindDomain WithZero Module IsLocalRing Polynomial


-- @@ L985-985 verbatim
namespace Mp72a102T1


-- @@ L987-987 verbatim
open AlgebraicCurve

-- @@ L988-988 verbatim
open ModularCurve.Lg37 ModularCurve.Ldgr37Ch


-- @@ L990-990 verbatim
open scoped Polynomial


-- @@ L992-992 verbatim
attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial


-- @@ L994-994 verbatim
section Engine


-- @@ L996-996 verbatim
variable {K F : Type*} [Field K] [Field F] [Algebra K F]


-- @@ L998-1001 verbatim
noncomputable abbrev mp72a102_t1_maximalIdealHat (v : Place K F) :
    Ideal (lg37_completion v) :=
  (IsLocalRing.maximalIdeal v.toValuationSubring).map
    (algebraMap v.toValuationSubring (lg37_completion v))


-- @@ L1003-1005 verbatim
theorem mp72a102_t1_isScalarTower (v : Place K F) :
    IsScalarTower K v.toValuationSubring (lg37_completion v) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl


-- @@ L1007-1013 verbatim
theorem mp72a102_t1_isAdicComplete_maximalIdealHat (v : Place K F) :
    IsAdicComplete (mp72a102_t1_maximalIdealHat v) (lg37_completion v) :=
  (IsAdicComplete.map_algebraMap_iff (IsLocalRing.maximalIdeal v.toValuationSubring)
      (lg37_completion v)).mpr
    (AdicCompletion.isAdicComplete
      (IsPrincipalIdealRing.principal
        (IsLocalRing.maximalIdeal v.toValuationSubring)).fg)


-- @@ L1015-1018 verbatim
theorem mp72a102_t1_henselianRing_completion (v : Place K F) :
    HenselianRing (lg37_completion v) (mp72a102_t1_maximalIdealHat v) :=
  letI := mp72a102_t1_isAdicComplete_maximalIdealHat v
  IsAdicComplete.henselianRing (lg37_completion v) (mp72a102_t1_maximalIdealHat v)


-- @@ L1020-1024 verbatim
theorem mp72a102_t1_maximalIdealHat_le_ker_residueHat (v : Place K F) :
    mp72a102_t1_maximalIdealHat v ≤ RingHom.ker (lg37_residueHat v) :=
  Ideal.map_le_iff_le_comap.mpr fun s hs => by
    rw [Ideal.mem_comap, RingHom.mem_ker, lg37_residueHat_algebraMap]
    exact (IsLocalRing.residue_eq_zero_iff s).mpr hs


-- @@ L1026-1094 verbatim
theorem mp72a102_t1_exists_completion_root_of_residue_root
    (v : Place K F) {p : K[X]} (hpmon : p.Monic) (hpsep : p.Separable)
    {rbar : v.ResidueField} (hrbar : Polynomial.aeval rbar p = 0) :
    ∃ α : lg37_completion v,
      Polynomial.aeval α p = 0 ∧ lg37_residueHat v α = rbar := by
  classical
  haveI _htower : IsScalarTower K v.toValuationSubring (lg37_completion v) :=
    mp72a102_t1_isScalarTower v

  obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective (R := v.toValuationSubring) rbar

  have hapI : Polynomial.aeval a p ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    have h1 : IsLocalRing.residue v.toValuationSubring (Polynomial.aeval a p)
        = Polynomial.aeval rbar p := by
      rw [← ha, ← IsLocalRing.ResidueField.algebraMap_eq,
        Polynomial.aeval_algebraMap_apply]
    rw [h1, hrbar]

  have hapIhat : Polynomial.aeval
      (algebraMap v.toValuationSubring (lg37_completion v) a) p
        ∈ mp72a102_t1_maximalIdealHat v := by
    rw [Polynomial.aeval_algebraMap_apply]
    exact Ideal.mem_map_of_mem _ hapI

  have hfeval : ∀ x : lg37_completion v,
      (p.map (algebraMap K (lg37_completion v))).eval x = Polynomial.aeval x p :=
    fun x => by rw [Polynomial.eval_map, ← Polynomial.aeval_def]
  have hfderiv :
      (p.map (algebraMap K (lg37_completion v))).derivative.eval
          (algebraMap v.toValuationSubring (lg37_completion v) a)
        = Polynomial.aeval
            (algebraMap v.toValuationSubring (lg37_completion v) a)
            (Polynomial.derivative p) := by
    rw [Polynomial.derivative_map, Polynomial.eval_map, ← Polynomial.aeval_def]

  obtain ⟨u, w, huw⟩ := hpsep
  have hunit : IsUnit (Ideal.Quotient.mk (mp72a102_t1_maximalIdealHat v)
      ((p.map (algebraMap K (lg37_completion v))).derivative.eval
        (algebraMap v.toValuationSubring (lg37_completion v) a))) := by
    rw [hfderiv]
    set a₀ := algebraMap v.toValuationSubring (lg37_completion v) a
    have h1 : Polynomial.aeval a₀ u * Polynomial.aeval a₀ p
        + Polynomial.aeval a₀ w * Polynomial.aeval a₀ (Polynomial.derivative p)
        = 1 := by
      have h0 := congrArg (Polynomial.aeval (R := K) a₀) huw
      simpa only [map_add, map_mul, map_one] using h0
    have h2 := congrArg (Ideal.Quotient.mk (mp72a102_t1_maximalIdealHat v)) h1
    rw [map_add, map_mul, map_mul, map_one,
      Ideal.Quotient.eq_zero_iff_mem.mpr hapIhat, mul_zero, zero_add] at h2
    exact IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans h2)

  obtain ⟨α, hαroot, hαnear⟩ :=
    (mp72a102_t1_henselianRing_completion v).is_henselian
      (p.map (algebraMap K (lg37_completion v))) (hpmon.map _)
      (algebraMap v.toValuationSubring (lg37_completion v) a)
      (by rw [hfeval]; exact hapIhat) hunit
  refine ⟨α, ?_, ?_⟩
  · rw [← hfeval]
    exact hαroot
  ·
    have h0 : lg37_residueHat v
        (α - algebraMap v.toValuationSubring (lg37_completion v) a) = 0 :=
      RingHom.mem_ker.mp (mp72a102_t1_maximalIdealHat_le_ker_residueHat v hαnear)
    have heq : lg37_residueHat v α
        = lg37_residueHat v
            (algebraMap v.toValuationSubring (lg37_completion v) a) := by
      rwa [map_sub, sub_eq_zero] at h0
    rw [heq, lg37_residueHat_algebraMap, ha]


-- @@ L1096-1096 verbatim
end Engine


-- @@ L1098-1098 verbatim
end Mp72a102T1


-- @@ L1100-1100 verbatim
end


-- @@ L1102-1102 verbatim
set_option autoImplicit false

-- @@ L1103-1103 verbatim
set_option linter.unusedSectionVars false

-- @@ L1104-1104 verbatim
set_option maxHeartbeats 400000

-- @@ L1105-1105 verbatim
set_option maxRecDepth 8000


-- @@ L1107-1107 verbatim
noncomputable section


-- @@ L1109-1109 verbatim
open IsLocalRing Polynomial


-- @@ L1111-1111 verbatim
open scoped Polynomial


-- @@ L1113-1113 verbatim
namespace ModularCurve.Mp72a102T3


-- @@ L1115-1115 verbatim
open AlgebraicCurve ModularCurve.Lg37


-- @@ L1117-1117 verbatim
section General


-- @@ L1119-1119 verbatim
variable {R : Type*} [CommRing R] (I : Ideal R)


-- @@ L1121-1125 verbatim
theorem mp72a102_t3_evalₐ_zero_depth (z : AdicCompletion I R) :
    AdicCompletion.evalₐ I 0 z = 0 := by
  haveI : Subsingleton (R ⧸ (I ^ 0)) :=
    Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
  exact Subsingleton.elim _ _


-- @@ L1127-1131 verbatim
theorem mp72a102_t3_evalₐ_algebraMap (n : ℕ) (r : R) :
    AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) r)
      = Ideal.Quotient.mk (I ^ n) r := by
  rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    AdicCompletion.evalₐ_of]


-- @@ L1133-1138 verbatim
theorem mp72a102_t3_evalₐ_factor {m n : ℕ} (hmn : m ≤ n) (z : AdicCompletion I R) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right hmn) (AdicCompletion.evalₐ I n z)
      = AdicCompletion.evalₐ I m z := by
  obtain ⟨c, rfl⟩ := AdicCompletion.mk_surjective I R z
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk, Ideal.Quotient.factor_mk]
  exact AdicCompletion.Ideal.mk_eq_mk I hmn c


-- @@ L1140-1147 verbatim
theorem mp72a102_t3_exists_rep_of_evalₐ_eq_zero {n : ℕ} {z : AdicCompletion I R}
    (h : AdicCompletion.evalₐ I n z = 0) :
    ∃ w ∈ I ^ n, AdicCompletion.evalₐ I (n + 1) z = Ideal.Quotient.mk (I ^ (n + 1)) w := by
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I (n + 1) z)
  refine ⟨w, ?_, hw.symm⟩
  have hfac := mp72a102_t3_evalₐ_factor I (Nat.le_succ n) z
  rw [← hw, Ideal.Quotient.factor_mk, h] at hfac
  exact Ideal.Quotient.eq_zero_iff_mem.mp hfac


-- @@ L1149-1155 verbatim
theorem mp72a102_t3_evalₐ_succ_mul_eq_zero {n : ℕ} {r : R} (hr : r ∈ I)
    {z : AdicCompletion I R} (h : AdicCompletion.evalₐ I n z = 0) :
    AdicCompletion.evalₐ I (n + 1) (algebraMap R (AdicCompletion I R) r * z) = 0 := by
  obtain ⟨w, hw, hwz⟩ := mp72a102_t3_exists_rep_of_evalₐ_eq_zero I h
  rw [map_mul, mp72a102_t3_evalₐ_algebraMap, hwz, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem, pow_succ']
  exact Ideal.mul_mem_mul hr hw


-- @@ L1157-1163 verbatim
theorem mp72a102_t3_evalₐ_one_eq_zero_of_evalOneₐ {z : AdicCompletion I R}
    (h : AdicCompletion.evalOneₐ I z = 0) : AdicCompletion.evalₐ I 1 z = 0 := by
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I 1 z)
  have hfac := AdicCompletion.factorₐ_evalₐ_one I z
  rw [← hw, Ideal.Quotient.factor_mk, h] at hfac
  rw [← hw, Ideal.Quotient.eq_zero_iff_mem, pow_one]
  exact Ideal.Quotient.eq_zero_iff_mem.mp hfac


-- @@ L1165-1165 verbatim
end General


-- @@ L1167-1167 verbatim
section Carrier


-- @@ L1169-1169 verbatim
variable {K F : Type*} [Field K] [Field F] [Algebra K F]


-- @@ L1171-1176 verbatim
theorem mp72a102_t3_evalDepth_add (v : Place K F) (n : ℕ)
    (x y : lg37_completion v) :
    AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n (x + y)
      = AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n x
        + AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n y :=
  map_add _ x y


-- @@ L1178-1183 verbatim
theorem mp72a102_t3_evalDepth_mul (v : Place K F) (n : ℕ)
    (x y : lg37_completion v) :
    AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n (x * y)
      = AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n x
        * AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n y :=
  map_mul _ x y


-- @@ L1185-1192 verbatim
theorem mp72a102_t3_residueHat_congr_of_depth_one (v : Place K F)
    {x y : lg37_completion v}
    (h : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) 1 x
        = AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) 1 y) :
    lg37_residueHat v x = lg37_residueHat v y := by
  show AdicCompletion.evalOneₐ (maximalIdeal v.toValuationSubring) x
      = AdicCompletion.evalOneₐ (maximalIdeal v.toValuationSubring) y
  rw [← AdicCompletion.factorₐ_evalₐ_one, ← AdicCompletion.factorₐ_evalₐ_one, h]


-- @@ L1194-1197 verbatim
theorem mp72a102_t3_evalDepth_one_eq_zero_of_residueHat (v : Place K F)
    {x : lg37_completion v} (hx : lg37_residueHat v x = 0) :
    AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) 1 x = 0 :=
  mp72a102_t3_evalₐ_one_eq_zero_of_evalOneₐ _ hx


-- @@ L1199-1203 verbatim
theorem mp72a102_t3_eq_uniformizer_mul_of_mem_maximalIdeal (v : Place K F)
    {w : v.toValuationSubring} (hw : w ∈ maximalIdeal v.toValuationSubring) :
    ∃ u : v.toValuationSubring, w = v.uniformizerSubring * u := by
  rw [v.irreducible_uniformizerSubring.maximalIdeal_eq, Ideal.mem_span_singleton] at hw
  exact hw


-- @@ L1205-1226 verbatim
theorem mp72a102_t3_exists_uniformizer_factor (v : Place K F)
    {x : lg37_completion v} (hx : lg37_residueHat v x = 0) (n : ℕ) :
    ∃ u : v.toValuationSubring,
      AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n
        (x - algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
          * algebraMap v.toValuationSubring (lg37_completion v) u) = 0 := by
  rcases n with _ | n
  · exact ⟨0, mp72a102_t3_evalₐ_zero_depth _ _⟩
  · obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective
      (AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 1) x)
    have h1 : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) 1 x = 0 :=
      mp72a102_t3_evalDepth_one_eq_zero_of_residueHat v hx
    have hfac := mp72a102_t3_evalₐ_factor (maximalIdeal v.toValuationSubring)
      (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero n)) x
    rw [← hw, Ideal.Quotient.factor_mk, h1] at hfac
    have hwm : w ∈ maximalIdeal v.toValuationSubring := by
      have hmem := Ideal.Quotient.eq_zero_iff_mem.mp hfac
      rwa [pow_one] at hmem
    obtain ⟨u, hu⟩ := mp72a102_t3_eq_uniformizer_mul_of_mem_maximalIdeal v hwm
    refine ⟨u, ?_⟩
    rw [map_sub, map_mul, mp72a102_t3_evalₐ_algebraMap, mp72a102_t3_evalₐ_algebraMap,
      ← map_mul, ← hu, ← hw, sub_self]


-- @@ L1228-1280 verbatim
theorem mp72a102_t3_sigma_taylor_expansion (v : Place K F)
    (S : Lg37CompletionSection v) (n : ℕ) (x : lg37_completion v) :
    ∃ a : ℕ → v.ResidueField,
      AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n
        (x - ∑ i ∈ Finset.range n, S.lift (a i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i) = 0 := by
  induction n generalizing x with
  | zero => exact ⟨fun _ => 0, mp72a102_t3_evalₐ_zero_depth _ _⟩
  | succ n ih =>
    have hres : lg37_residueHat v (x - S.lift (lg37_residueHat v x)) = 0 := by
      rw [map_sub, S.residueHat_lift, sub_self]
    obtain ⟨u, hu⟩ := mp72a102_t3_exists_uniformizer_factor v hres (n + 1)
    obtain ⟨a, ha⟩ := ih (algebraMap v.toValuationSubring (lg37_completion v) u)
    have hshift := mp72a102_t3_evalₐ_succ_mul_eq_zero
      (maximalIdeal v.toValuationSubring) v.uniformizerSubring_mem_maximalIdeal ha
    refine ⟨fun i => Nat.rec (motive := fun _ => v.ResidueField)
      (lg37_residueHat v x) (fun j _ => a j) i, ?_⟩
    rw [Finset.sum_range_succ']
    show AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 1)
        (x - ((∑ i ∈ Finset.range n, S.lift (a i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ (i + 1))
          + S.lift (lg37_residueHat v x)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ 0)) = 0
    have hsum : ∑ i ∈ Finset.range n, S.lift (a i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ (i + 1)
        = algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
          * ∑ i ∈ Finset.range n, S.lift (a i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum, pow_zero, mul_one]
    have hdecomp : x - (algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring
          * ∑ i ∈ Finset.range n, S.lift (a i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i
          + S.lift (lg37_residueHat v x))
        = (x - S.lift (lg37_residueHat v x)
            - algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring
              * algebraMap v.toValuationSubring (lg37_completion v) u)
          + algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
            * (algebraMap v.toValuationSubring (lg37_completion v) u
              - ∑ i ∈ Finset.range n, S.lift (a i)
                * algebraMap v.toValuationSubring (lg37_completion v)
                    v.uniformizerSubring ^ i) := by
      ring
    rw [hdecomp, map_add, hu, hshift, add_zero]


-- @@ L1282-1282 verbatim
end Carrier


-- @@ L1284-1284 verbatim
section RatProduction


-- @@ L1286-1286 verbatim
attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial


-- @@ L1288-1288 verbatim
variable [HasCanonicalLocalResidueKStar ℚ (RatFunc ℚ)]

-- @@ L1289-1289 verbatim
variable [HasCanonicalLocalResidueKStar (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ))]


-- @@ L1291-1291 verbatim
end RatProduction


-- @@ L1293-1293 verbatim
end ModularCurve.Mp72a102T3


-- @@ L1295-1295 verbatim
end


-- @@ L1297-1297 verbatim
set_option autoImplicit false

-- @@ L1298-1298 verbatim
set_option linter.unusedSectionVars false

-- @@ L1299-1299 verbatim
set_option maxHeartbeats 400000

-- @@ L1300-1300 verbatim
set_option maxRecDepth 8000


-- @@ L1302-1302 verbatim
noncomputable section


-- @@ L1304-1304 verbatim
open IsDedekindDomain WithZero Module IsLocalRing Polynomial


-- @@ L1306-1306 verbatim
namespace Mp72a102T2


-- @@ L1308-1308 verbatim
open AlgebraicCurve

-- @@ L1309-1309 verbatim
open ModularCurve.Lg37 ModularCurve.Ldgr35Cs


-- @@ L1311-1311 verbatim
open scoped Polynomial


-- @@ L1313-1313 verbatim
section ResidueCalculus


-- @@ L1315-1315 verbatim
variable {K F : Type*} [Field K] [Field F] [Algebra K F]


-- @@ L1317-1324 verbatim
theorem mp72a102_t2_residueHat_algebraMap_base (v : Place K F) (c : K) :
    lg37_residueHat v (algebraMap K (lg37_completion v) c)
      = algebraMap K v.ResidueField c := by
  have h : algebraMap K (lg37_completion v) c
      = algebraMap v.toValuationSubring (lg37_completion v)
          (algebraMap K v.toValuationSubring c) := rfl
  rw [h, lg37_residueHat_algebraMap v]
  rfl


-- @@ L1326-1329 verbatim
def mp72a102_t2_residueHatAlgHom (v : Place K F) :
    lg37_completion v →ₐ[K] v.ResidueField where
  toRingHom := lg37_residueHat v
  commutes' := mp72a102_t2_residueHat_algebraMap_base v


-- @@ L1331-1331 verbatim
end ResidueCalculus


-- @@ L1333-1333 verbatim
section RatProduction


-- @@ L1335-1335 verbatim
attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial


-- @@ L1337-1337 verbatim
end RatProduction


-- @@ L1339-1339 verbatim
end Mp72a102T2


-- @@ L1341-1341 verbatim
end


-- @@ L1343-1343 verbatim
set_option autoImplicit false

-- @@ L1344-1344 verbatim
set_option maxHeartbeats 800000


-- @@ L1346-1346 verbatim
open AlgebraicCurve ModularCurve.Lg37 Polynomial IntermediateField Mp72a102T1 Mp72a102T2


-- @@ L1348-1348 verbatim
namespace ModularCurve.KwNo6Section


-- @@ L1350-1350 verbatim
section GenericIso


-- @@ L1352-1352 verbatim
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)


-- @@ L1354-1358 verbatim
noncomputable def residueFieldAdjoinRootEquiv {ᾱ : v.ResidueField} (hint : IsIntegral K ᾱ)
    (htop : K⟮ᾱ⟯ = ⊤) :
    AdjoinRoot (minpoly K ᾱ) ≃ₐ[K] v.ResidueField :=
  (adjoinRootEquivAdjoin K hint).trans
    ((IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv)


-- @@ L1360-1367 verbatim
theorem residueFieldAdjoinRootEquiv_root {ᾱ : v.ResidueField} (hint : IsIntegral K ᾱ)
    (htop : K⟮ᾱ⟯ = ⊤) :
    residueFieldAdjoinRootEquiv v hint htop (AdjoinRoot.root (minpoly K ᾱ)) = ᾱ := by
  have hgen := adjoinRootEquivAdjoin_apply_root K hint

  simp only [residueFieldAdjoinRootEquiv, AlgEquiv.trans_apply, hgen,
    IntermediateField.topEquiv_apply]
  exact AdjoinSimple.coe_gen K ᾱ


-- @@ L1369-1369 verbatim
end GenericIso


-- @@ L1371-1371 verbatim
section GenericSection


-- @@ L1373-1373 verbatim
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)


-- @@ L1375-1401 verbatim
noncomputable def sectionOfPrimitiveRoot {ᾱ : v.ResidueField} (hint : IsIntegral K ᾱ)
    (htop : K⟮ᾱ⟯ = ⊤) (αhat : lg37_completion v)
    (hroot : (aeval αhat) (minpoly K ᾱ) = 0)
    (hres : lg37_residueHat v αhat = ᾱ) :
    Lg37CompletionSection v where
  lift :=
    (AdjoinRoot.liftAlgHom (minpoly K ᾱ) (Algebra.ofId K (lg37_completion v)) αhat
      (by rw [aeval_def] at hroot; exact hroot)).comp
      (residueFieldAdjoinRootEquiv v hint htop).symm.toAlgHom
  residueHat_lift a := by

    have hres' : lg37_residueHat v αhat
        = residueFieldAdjoinRootEquiv v hint htop (AdjoinRoot.root (minpoly K ᾱ)) :=
      hres.trans (residueFieldAdjoinRootEquiv_root v hint htop).symm
    have hkey : (mp72a102_t2_residueHatAlgHom v).comp
          (AdjoinRoot.liftAlgHom (minpoly K ᾱ) (Algebra.ofId K (lg37_completion v)) αhat
            (by rw [aeval_def] at hroot; exact hroot))
        = (residueFieldAdjoinRootEquiv v hint htop).toAlgHom := by
      refine AdjoinRoot.algHom_ext ?_
      rw [AlgHom.comp_apply, AdjoinRoot.liftAlgHom_root]
      exact hres'
    have h1 := DFunLike.congr_fun hkey ((residueFieldAdjoinRootEquiv v hint htop).symm a)
    rw [AlgHom.comp_apply] at h1
    have h2 : (residueFieldAdjoinRootEquiv v hint htop).toAlgHom
        ((residueFieldAdjoinRootEquiv v hint htop).symm a) = a :=
      (residueFieldAdjoinRootEquiv v hint htop).apply_symm_apply a
    exact h1.trans h2


-- @@ L1403-1403 verbatim
end GenericSection


-- @@ L1405-1405 verbatim
end ModularCurve.KwNo6Section


-- @@ L1407-1407 verbatim
set_option autoImplicit false

-- @@ L1408-1408 verbatim
set_option linter.unusedSectionVars false

-- @@ L1409-1409 verbatim
set_option maxHeartbeats 400000

-- @@ L1410-1410 verbatim
set_option maxRecDepth 8000


-- @@ L1412-1412 verbatim
noncomputable section


-- @@ L1414-1414 verbatim
open IsDedekindDomain IsLocalRing Polynomial


-- @@ L1416-1416 verbatim
open scoped Polynomial


-- @@ L1418-1418 verbatim
namespace Mp72a103T2


-- @@ L1420-1420 verbatim
open AlgebraicCurve

-- @@ L1421-1421 verbatim
open ModularCurve.Lg37 ModularCurve.Mp72a102T3

-- @@ L1422-1422 verbatim
open Mp72a102T2


-- @@ L1424-1424 verbatim
section Calculus


-- @@ L1426-1426 verbatim
variable {K F : Type*} [Field K] [Field F] [Algebra K F]


-- @@ L1428-1451 verbatim
theorem mp72a103_t2_evalDepth_of_uniformizer_mul (v : Place K F) {n : ℕ}
    {z : lg37_completion v}
    (h : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 1)
        (algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring * z) = 0) :
    AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n z = 0 := by
  obtain ⟨w, hw⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 1) z)
  rw [map_mul, mp72a102_t3_evalₐ_algebraMap, ← hw, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem, v.irreducible_uniformizerSubring.maximalIdeal_eq,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  obtain ⟨u, hu⟩ := h
  have hw' : v.uniformizerSubring * w
      = v.uniformizerSubring * (v.uniformizerSubring ^ n * u) := by
    rw [hu, pow_succ', mul_assoc]
  have hcancel : w = v.uniformizerSubring ^ n * u :=
    mul_left_cancel₀ v.irreducible_uniformizerSubring.ne_zero hw'
  have hfac := mp72a102_t3_evalₐ_factor (maximalIdeal v.toValuationSubring)
    (Nat.le_succ n) z
  rw [← hw, Ideal.Quotient.factor_mk] at hfac
  rw [← hfac, Ideal.Quotient.eq_zero_iff_mem, hcancel,
    v.irreducible_uniformizerSubring.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton]
  exact ⟨u, rfl⟩


-- @@ L1453-1459 verbatim
theorem mp72a103_t2_lift_eq_zero_of_depth_one (v : Place K F)
    (S : Lg37CompletionSection v) {c : v.ResidueField}
    (h : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) 1 (S.lift c) = 0) :
    c = 0 := by
  have hres : lg37_residueHat v (S.lift c) = lg37_residueHat v 0 :=
    mp72a102_t3_residueHat_congr_of_depth_one v (by rw [h, map_zero])
  rwa [S.residueHat_lift, map_zero] at hres


-- @@ L1461-1517 verbatim
theorem mp72a103_t2_taylor_coeff_eq_zero_of_depth (v : Place K F)
    (S : Lg37CompletionSection v) :
    ∀ (n : ℕ) (a : ℕ → v.ResidueField),
      AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n
        (∑ i ∈ Finset.range n, S.lift (a i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i) = 0 →
      ∀ i < n, a i = 0 := by
  intro n
  induction n with
  | zero => intro a _ i hi; exact absurd hi (Nat.not_lt_zero i)
  | succ n ih =>
    intro a h
    have hsplit : (∑ i ∈ Finset.range (n + 1), S.lift (a i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
            * (∑ i ∈ Finset.range n, S.lift (a (i + 1))
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i)
          + S.lift (a 0) := by
      rw [Finset.sum_range_succ', pow_zero, mul_one, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    have hfac1 := mp72a102_t3_evalₐ_factor (maximalIdeal v.toValuationSubring)
      (show 1 ≤ n + 1 by omega)
      (∑ i ∈ Finset.range (n + 1), S.lift (a i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i)
    rw [h, map_zero] at hfac1
    have hT1 : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) 1
        (algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
          * (∑ i ∈ Finset.range n, S.lift (a (i + 1))
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i)) = 0 :=
      mp72a102_t3_evalₐ_succ_mul_eq_zero (maximalIdeal v.toValuationSubring)
        v.uniformizerSubring_mem_maximalIdeal
        (mp72a102_t3_evalₐ_zero_depth (maximalIdeal v.toValuationSubring) _)
    have h1 : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) 1
        (S.lift (a 0)) = 0 := by
      have h1' := hfac1.symm
      rw [hsplit, map_add, hT1, zero_add] at h1'
      exact h1'
    have ha0 : a 0 = 0 := mp72a103_t2_lift_eq_zero_of_depth_one v S h1
    have hT : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) n
        (∑ i ∈ Finset.range n, S.lift (a (i + 1))
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i) = 0 := by
      apply mp72a103_t2_evalDepth_of_uniformizer_mul v
      have h' := h
      rw [hsplit, ha0, map_zero, add_zero] at h'
      exact h'
    have hrec := ih (fun j => a (j + 1)) hT
    intro i hi
    cases i with
    | zero => exact ha0
    | succ j => exact hrec j (Nat.lt_of_succ_lt_succ hi)


-- @@ L1519-1519 verbatim
end Calculus


-- @@ L1521-1521 verbatim
section RatProduction


-- @@ L1523-1523 verbatim
attribute [local instance 2000] RatFunc.instAlgebraOfPolynomial


-- @@ L1525-1525 verbatim
variable [HasCanonicalLocalResidueKStar ℚ (RatFunc ℚ)]

-- @@ L1526-1526 verbatim
variable [HasCanonicalLocalResidueKStar (AlgebraicClosure ℚ) (RatFunc (AlgebraicClosure ℚ))]


-- @@ L1528-1528 verbatim
end RatProduction


-- @@ L1530-1530 verbatim
end Mp72a103T2


-- @@ L1532-1532 verbatim
end


-- @@ L1534-1534 verbatim
set_option autoImplicit false

-- @@ L1535-1535 verbatim
set_option maxHeartbeats 1600000


-- @@ L1537-1537 verbatim
open Polynomial IsLocalRing AlgebraicCurve

-- @@ L1538-1538 verbatim
open ModularCurve.Lg37 ModularCurve.Mp72a102T3 Mp72a103T2 Mp72a102T1

-- @@ L1539-1539 verbatim
open ModularCurve.KwNo6Section


-- @@ L1541-1541 verbatim
namespace ModularCurve.KwNo6Pin


-- @@ L1543-1543 verbatim
variable {K F : Type*} [Field K] [Field F] [Algebra K F]


-- @@ L1545-1547 verbatim
theorem maximalIdeal_fg (v : Place K F) :
    (maximalIdeal v.toValuationSubring).FG :=
  IsNoetherian.noetherian _


-- @@ L1549-1554 verbatim
theorem isAdicComplete_map (v : Place K F) :
    IsAdicComplete
        ((maximalIdeal v.toValuationSubring).map
          (algebraMap v.toValuationSubring (lg37_completion v)))
        (lg37_completion v) :=
  mp72a102_t1_isAdicComplete_maximalIdealHat v


-- @@ L1556-1560 verbatim
theorem residueHat_surjective (v : Place K F) :
    Function.Surjective (lg37_residueHat v) := fun y => by
  obtain ⟨x, hx⟩ := IsLocalRing.residue_surjective (R := v.toValuationSubring) y
  exact ⟨algebraMap v.toValuationSubring (lg37_completion v) x,
    (lg37_residueHat_algebraMap v x).trans hx⟩


-- @@ L1562-1600 verbatim
theorem ker_residueHat (v : Place K F) :
    RingHom.ker (lg37_residueHat v)
      = (maximalIdeal v.toValuationSubring).map
          (algebraMap v.toValuationSubring (lg37_completion v)) := by
  apply le_antisymm
  · intro x hx
    have hx0 : lg37_residueHat v x = 0 := RingHom.mem_ker.mp hx
    have htop : ((maximalIdeal v.toValuationSubring) ^ 1 • ⊤ :
        Ideal v.toValuationSubring) = (maximalIdeal v.toValuationSubring) ^ 1 := by
      ext a; simp
    have h2 : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) 1 x = 0 := by
      have hfac : Ideal.Quotient.factor
          (show (maximalIdeal v.toValuationSubring) ^ 1
              ≤ maximalIdeal v.toValuationSubring by simp)
          (AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) 1 x) = 0 :=
        (AdicCompletion.factorₐ_evalₐ_one
          (I := maximalIdeal v.toValuationSubring) x).trans hx0
      obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective
        (AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) 1 x)
      rw [← hy, Ideal.Quotient.factor_mk] at hfac
      rw [← hy, Ideal.Quotient.eq_zero_iff_mem, pow_one]
      exact Ideal.Quotient.eq_zero_iff_mem.mp hfac
    have h4 : Ideal.quotientEquivAlgOfEq v.toValuationSubring htop
        (AdicCompletion.eval (maximalIdeal v.toValuationSubring)
          v.toValuationSubring 1 x) = 0 := h2
    have h3 : AdicCompletion.eval (maximalIdeal v.toValuationSubring)
        v.toValuationSubring 1 x = 0 :=
      (Ideal.quotientEquivAlgOfEq v.toValuationSubring htop).injective
        (h4.trans (map_zero _).symm)
    have h6 : x ∈ ((maximalIdeal v.toValuationSubring) ^ 1 • ⊤ :
        Submodule v.toValuationSubring (lg37_completion v)) := by
      rw [AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal_fg v)]
      exact LinearMap.mem_ker.mpr h3
    rw [pow_one, Ideal.smul_top_eq_map] at h6
    simpa using h6
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker, lg37_residueHat_algebraMap]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr ha


-- @@ L1602-1606 verbatim
theorem map_isMaximal (v : Place K F) :
    ((maximalIdeal v.toValuationSubring).map
        (algebraMap v.toValuationSubring (lg37_completion v))).IsMaximal := by
  rw [← ker_residueHat v]
  exact RingHom.ker_isMaximal_of_surjective _ (residueHat_surjective v)


-- @@ L1608-1614 verbatim
instance isLocalRing_completion (v : Place K F) :
    IsLocalRing (lg37_completion v) := by
  haveI := map_isMaximal v
  haveI := isAdicComplete_map v
  exact isLocalRing_of_isAdicComplete_maximal
    ((maximalIdeal v.toValuationSubring).map
      (algebraMap v.toValuationSubring (lg37_completion v)))


-- @@ L1616-1620 verbatim
theorem ker_residueHat_eq_maximalIdeal (v : Place K F) :
    RingHom.ker (lg37_residueHat v)
      = maximalIdeal (lg37_completion v) := by
  rw [ker_residueHat v]
  exact (IsLocalRing.eq_maximalIdeal (map_isMaximal v))


-- @@ L1622-1655 verbatim
theorem hensel_unique (v : Place K F) {p : K[X]} (hsep : p.Separable)
    {α β : lg37_completion v}
    (hα : aeval α p = 0) (hβ : aeval β p = 0)
    (hres : lg37_residueHat v α = lg37_residueHat v β) : α = β := by
  haveI := isLocalRing_completion v
  set f := p.map (algebraMap K (lg37_completion v)) with hf
  have hevalα : f.eval α = 0 := by rw [hf, eval_map, ← aeval_def]; exact hα
  have hevalβ : f.eval β = 0 := by rw [hf, eval_map, ← aeval_def]; exact hβ

  set φ := (AdicCompletion.evalOneₐ (maximalIdeal v.toValuationSubring)).restrictScalars K
    with hφ
  have hφeq : ∀ z, φ z = lg37_residueHat v z := fun z => rfl

  have hsub0 : lg37_residueHat v (α - β) = 0 := by rw [map_sub, hres, sub_self]
  have hmem : (α - β) ∈ maximalIdeal (lg37_completion v) := by
    rw [← ker_residueHat_eq_maximalIdeal v]; exact RingHom.mem_ker.mpr hsub0
  have hnu : ¬ IsUnit (α - β) := fun hu => notMem_maximalIdeal.mpr hu hmem

  have hfderiv : f.derivative.eval α = aeval α (derivative p) := by
    rw [hf, derivative_map, eval_map, ← aeval_def]
  have hαroot : aeval (lg37_residueHat v α) p = 0 := by
    have h := Polynomial.aeval_algHom_apply φ α p
    rw [hφeq, hφeq, hα, map_zero] at h
    exact h
  have hderivbar : aeval (lg37_residueHat v α) (derivative p) ≠ 0 :=
    hsep.aeval_derivative_ne_zero hαroot
  have hunit : IsUnit (f.derivative.eval α) := by
    rw [← notMem_maximalIdeal, ← ker_residueHat_eq_maximalIdeal v, RingHom.mem_ker, hfderiv]
    intro hk
    apply hderivbar
    have h := Polynomial.aeval_algHom_apply φ α (derivative p)
    rw [hφeq, hφeq] at h
    exact h.trans hk
  exact eq_of_eval_eq_zero_of_not_isUnit_sub hevalα hevalβ hnu hunit


-- @@ L1657-1681 verbatim
theorem section_unique (v : Place K F)
    [FiniteDimensional K v.ResidueField] [Algebra.IsSeparable K v.ResidueField]
    (S S' : Lg37CompletionSection v) : S.lift = S'.lift := by
  obtain ⟨θ, htop⟩ := Field.exists_primitive_element K v.ResidueField
  have hint : IsIntegral K θ := Algebra.IsIntegral.isIntegral θ
  have hsep : (minpoly K θ).Separable := Algebra.IsSeparable.isSeparable K θ
  have hroot : ∀ (T : Lg37CompletionSection v),
      aeval (T.lift θ) (minpoly K θ) = 0 := by
    intro T
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hθ : S.lift θ = S'.lift θ :=
    hensel_unique v hsep (hroot S) (hroot S')
      ((S.residueHat_lift θ).trans (S'.residueHat_lift θ).symm)

  have hcomp : S.lift.comp (residueFieldAdjoinRootEquiv v hint htop).toAlgHom
      = S'.lift.comp (residueFieldAdjoinRootEquiv v hint htop).toAlgHom := by
    refine AdjoinRoot.algHom_ext ?_
    have hr : (residueFieldAdjoinRootEquiv v hint htop).toAlgHom
        (AdjoinRoot.root (minpoly K θ)) = θ := residueFieldAdjoinRootEquiv_root v hint htop
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hr]
    exact hθ
  refine AlgHom.ext (fun a => ?_)
  obtain ⟨b, rfl⟩ := (residueFieldAdjoinRootEquiv v hint htop).surjective a
  have hb := DFunLike.congr_fun hcomp b
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_algHom] using hb


-- @@ L1683-1685 verbatim
noncomputable def aCoeff (v : Place K F) (S : Lg37CompletionSection v)
    (n : ℕ) (x : lg37_completion v) : v.ResidueField :=
  (Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (n + 1) x)) n


-- @@ L1687-1724 verbatim
theorem aCoeff_section_indep (v : Place K F)
    [FiniteDimensional K v.ResidueField] [Algebra.IsSeparable K v.ResidueField]
    (S S' : Lg37CompletionSection v) (n : ℕ) (x : lg37_completion v) :
    aCoeff v S n x = aCoeff v S' n x := by
  have hlift : S.lift = S'.lift := section_unique v S S'
  have ha := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (n + 1) x)
  have ha' := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S' (n + 1) x)
  set a := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (n + 1) x) with ha_def
  set a' := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S' (n + 1) x) with ha'_def

  have ha'' : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 1)
      (x - ∑ i ∈ Finset.range (n + 1), S.lift (a' i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    simpa only [← hlift] using ha'

  have key : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 1)
      (∑ i ∈ Finset.range (n + 1), S.lift ((fun i => a' i - a i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e1 : (∑ i ∈ Finset.range (n + 1), S.lift (a' i - a i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = (x - ∑ i ∈ Finset.range (n + 1), S.lift (a i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i)
          - (x - ∑ i ∈ Finset.range (n + 1), S.lift (a' i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl
        (fun i _ => by rw [map_sub, sub_mul]), Finset.sum_sub_distrib]
      ring
    rw [e1, map_sub, ha, ha'', sub_zero]
  have hzero := mp72a103_t2_taylor_coeff_eq_zero_of_depth v S (n + 1)
    (fun i => a' i - a i) key n (Nat.lt_succ_self n)
  have han : a n = a' n := (sub_eq_zero.mp hzero).symm
  simp only [aCoeff, ← ha_def, ← ha'_def]
  exact han


-- @@ L1726-1726 verbatim
end ModularCurve.KwNo6Pin


-- @@ L1728-1728 verbatim
set_option autoImplicit false

-- @@ L1729-1729 verbatim
set_option maxHeartbeats 1600000


-- @@ L1731-1731 verbatim
open Polynomial IsLocalRing AlgebraicCurve

-- @@ L1732-1732 verbatim
open ModularCurve.Lg37 ModularCurve.Mp72a102T3 Mp72a103T2 Mp72a102T1

-- @@ L1733-1733 verbatim
open ModularCurve.KwNo6Section


-- @@ L1735-1735 verbatim
namespace ModularCurve.KwNo6Pin


-- @@ L1737-1737 verbatim
variable {K F : Type*} [Field K] [Field F] [Algebra K F]


-- @@ L1739-1749 verbatim
theorem aCoeff_zero (v : Place K F) (S : Lg37CompletionSection v)
    (x : lg37_completion v) :
    aCoeff v S 0 x = lg37_residueHat v x := by
  have ha := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S 1 x)
  set a := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S 1 x) with ha_def
  rw [Finset.sum_range_one, pow_zero, mul_one] at ha
  have hres : lg37_residueHat v (x - S.lift (a 0)) = lg37_residueHat v 0 :=
    mp72a102_t3_residueHat_congr_of_depth_one v (by rw [ha, map_zero])
  rw [map_sub, S.residueHat_lift, map_zero, sub_eq_zero] at hres
  simp only [aCoeff, ← ha_def]
  exact hres.symm


-- @@ L1751-1799 verbatim
theorem aCoeff_add (v : Place K F) (S : Lg37CompletionSection v) (m : ℕ)
    (x y : lg37_completion v) :
    aCoeff v S m (x + y) = aCoeff v S m x + aCoeff v S m y := by
  have hx := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1) x)
  have hy := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1) y)
  have hxy := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1) (x + y))
  set ax := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1) x) with hax_def
  set ay := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1) y) with hay_def
  set axy := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1) (x + y))
    with haxy_def
  have hsum : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (m + 1)
      ((x + y) - ∑ i ∈ Finset.range (m + 1), S.lift ((fun i => ax i + ay i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e : (x + y) - ∑ i ∈ Finset.range (m + 1), S.lift (ax i + ay i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i
        = (x - ∑ i ∈ Finset.range (m + 1), S.lift (ax i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i)
          + (y - ∑ i ∈ Finset.range (m + 1), S.lift (ay i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_add, add_mul]),
        Finset.sum_add_distrib]
      ring
    rw [e, mp72a102_t3_evalDepth_add, hx, hy, add_zero]
  have key : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (m + 1)
      (∑ i ∈ Finset.range (m + 1), S.lift ((fun i => (ax i + ay i) - axy i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e1 : (∑ i ∈ Finset.range (m + 1), S.lift ((ax i + ay i) - axy i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = ((x + y) - ∑ i ∈ Finset.range (m + 1), S.lift (axy i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i)
          - ((x + y) - ∑ i ∈ Finset.range (m + 1), S.lift (ax i + ay i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_sub, sub_mul]),
        Finset.sum_sub_distrib]
      ring
    rw [e1, map_sub, hxy, hsum, sub_zero]
  have hzero := mp72a103_t2_taylor_coeff_eq_zero_of_depth v S (m + 1)
    (fun i => (ax i + ay i) - axy i) key m (Nat.lt_succ_self m)
  have han : axy m = ax m + ay m := (sub_eq_zero.mp hzero).symm
  simp only [aCoeff, ← hax_def, ← hay_def, ← haxy_def]
  exact han


-- @@ L1801-1858 verbatim
theorem aCoeff_smul (v : Place K F) (S : Lg37CompletionSection v) (m : ℕ) (c : K)
    (x : lg37_completion v) :
    aCoeff v S m (algebraMap K (lg37_completion v) c * x)
      = algebraMap K v.ResidueField c * aCoeff v S m x := by
  have hx := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1) x)
  have hcx := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (m + 1)
    (algebraMap K (lg37_completion v) c * x))
  set ax := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1) x) with hax_def
  set acx := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (m + 1)
    (algebraMap K (lg37_completion v) c * x)) with hacx_def
  have hsmul : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (m + 1)
      ((algebraMap K (lg37_completion v) c * x)
        - ∑ i ∈ Finset.range (m + 1),
            S.lift ((fun i => algebraMap K v.ResidueField c * ax i) i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i) = 0 := by
    have e : (algebraMap K (lg37_completion v) c * x)
          - ∑ i ∈ Finset.range (m + 1), S.lift (algebraMap K v.ResidueField c * ax i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i
        = algebraMap K (lg37_completion v) c
          * (x - ∑ i ∈ Finset.range (m + 1), S.lift (ax i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i) := by
      rw [mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      have hlift : S.lift (algebraMap K v.ResidueField c * ax i)
          = algebraMap K (lg37_completion v) c * S.lift (ax i) := by
        rw [← Algebra.smul_def c (ax i), map_smul, Algebra.smul_def]
      rw [hlift, mul_assoc]
    rw [e, mp72a102_t3_evalDepth_mul, hx, mul_zero]
  have key : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (m + 1)
      (∑ i ∈ Finset.range (m + 1),
          S.lift ((fun i => algebraMap K v.ResidueField c * ax i - acx i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e1 : (∑ i ∈ Finset.range (m + 1),
            S.lift (algebraMap K v.ResidueField c * ax i - acx i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = ((algebraMap K (lg37_completion v) c * x)
            - ∑ i ∈ Finset.range (m + 1), S.lift (acx i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i)
          - ((algebraMap K (lg37_completion v) c * x)
            - ∑ i ∈ Finset.range (m + 1), S.lift (algebraMap K v.ResidueField c * ax i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_sub, sub_mul]),
        Finset.sum_sub_distrib]
      ring
    rw [e1, map_sub, hcx, hsmul, sub_zero]
  have hzero := mp72a103_t2_taylor_coeff_eq_zero_of_depth v S (m + 1)
    (fun i => algebraMap K v.ResidueField c * ax i - acx i) key m (Nat.lt_succ_self m)
  have han : acx m = algebraMap K v.ResidueField c * ax m := (sub_eq_zero.mp hzero).symm
  simp only [aCoeff, ← hax_def, ← hacx_def]
  exact han


-- @@ L1860-1928 verbatim
theorem aCoeff_shift (v : Place K F) (S : Lg37CompletionSection v) (n : ℕ)
    (x : lg37_completion v) :
    aCoeff v S (n + 1)
        (algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x)
      = aCoeff v S n x := by
  have ha := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (n + 1) x)
  have hpx := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (n + 2)
    (algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x))
  set a := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (n + 1) x) with ha_def
  set b := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (n + 2)
    (algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x))
    with hb_def

  set c : ℕ → v.ResidueField :=
    fun i => Nat.rec (motive := fun _ => v.ResidueField) 0 (fun j _ => a j) i with hc_def

  have hshift : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 2)
      ((algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x)
        - ∑ i ∈ Finset.range (n + 2), S.lift (c i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i) = 0 := by
    have hmul := mp72a102_t3_evalₐ_succ_mul_eq_zero (maximalIdeal v.toValuationSubring)
      v.uniformizerSubring_mem_maximalIdeal ha
    have e : (algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x)
          - ∑ i ∈ Finset.range (n + 2), S.lift (c i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i
        = algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
          * (x - ∑ i ∈ Finset.range (n + 1), S.lift (a i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i) := by
      have hc0 : c 0 = 0 := rfl
      have hcs : ∀ i, c (i + 1) = a i := fun _ => rfl
      rw [Finset.sum_range_succ', hc0, map_zero, zero_mul, add_zero, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [hcs i, pow_succ]
      ring
    rw [e]
    exact hmul

  have key : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 2)
      (∑ i ∈ Finset.range (n + 2), S.lift ((fun i => c i - b i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e1 : (∑ i ∈ Finset.range (n + 2), S.lift (c i - b i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = ((algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x)
            - ∑ i ∈ Finset.range (n + 2), S.lift (b i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i)
          - ((algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * x)
            - ∑ i ∈ Finset.range (n + 2), S.lift (c i)
              * algebraMap v.toValuationSubring (lg37_completion v)
                  v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_sub, sub_mul]),
        Finset.sum_sub_distrib]
      ring
    rw [e1, map_sub, hpx, hshift, sub_zero]
  have hzero := mp72a103_t2_taylor_coeff_eq_zero_of_depth v S (n + 2)
    (fun i => c i - b i) key (n + 1) (Nat.lt_succ_self (n + 1))
  have hcn : c (n + 1) = a n := rfl
  have hbn : b (n + 1) = a n := by
    have := sub_eq_zero.mp hzero
    rw [hcn] at this
    exact this.symm
  simp only [aCoeff, ← ha_def, ← hb_def]
  exact hbn


-- @@ L1930-1945 verbatim
theorem aCoeff_shift_pow (v : Place K F) (S : Lg37CompletionSection v) (n k : ℕ)
    (x : lg37_completion v) :
    aCoeff v S (n + k)
        ((algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring) ^ k
          * x)
      = aCoeff v S n x := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep : (algebraMap v.toValuationSubring (lg37_completion v)
          v.uniformizerSubring) ^ (k + 1) * x
        = algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
          * ((algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring) ^ k * x) := by
      rw [pow_succ]; ring
    rw [show n + (k + 1) = (n + k) + 1 from by omega, hstep, aCoeff_shift, ih]


-- @@ L1947-1988 verbatim
theorem aCoeff_one_eq_zero (v : Place K F) (S : Lg37CompletionSection v)
    {n : ℕ} (hn : 1 ≤ n) : aCoeff v S n 1 = 0 := by
  have hc := Classical.choose_spec (mp72a102_t3_sigma_taylor_expansion v S (n + 1) 1)
  set cc := Classical.choose (mp72a102_t3_sigma_taylor_expansion v S (n + 1) 1) with hcc_def

  set e : ℕ → v.ResidueField := fun i => if i = 0 then 1 else 0 with he_def
  have hesum : (∑ i ∈ Finset.range (n + 1), S.lift (e i)
      * algebraMap v.toValuationSubring (lg37_completion v)
          v.uniformizerSubring ^ i) = 1 := by
    rw [Finset.sum_eq_single 0]
    · simp [he_def]
    · intro i _ hi; simp [he_def, hi]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hevalid : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 1)
      ((1 : lg37_completion v) - ∑ i ∈ Finset.range (n + 1), S.lift (e i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    rw [hesum, sub_self, map_zero]
  have key : AdicCompletion.evalₐ (maximalIdeal v.toValuationSubring) (n + 1)
      (∑ i ∈ Finset.range (n + 1), S.lift ((fun i => e i - cc i) i)
        * algebraMap v.toValuationSubring (lg37_completion v)
            v.uniformizerSubring ^ i) = 0 := by
    have e1 : (∑ i ∈ Finset.range (n + 1), S.lift (e i - cc i)
          * algebraMap v.toValuationSubring (lg37_completion v)
              v.uniformizerSubring ^ i)
        = ((1 : lg37_completion v) - ∑ i ∈ Finset.range (n + 1), S.lift (cc i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i)
          - ((1 : lg37_completion v) - ∑ i ∈ Finset.range (n + 1), S.lift (e i)
            * algebraMap v.toValuationSubring (lg37_completion v)
                v.uniformizerSubring ^ i) := by
      rw [Finset.sum_congr rfl (fun i _ => by rw [map_sub, sub_mul]),
        Finset.sum_sub_distrib]
      ring
    rw [e1, map_sub, hc, hevalid, sub_zero]
  have hzero := mp72a103_t2_taylor_coeff_eq_zero_of_depth v S (n + 1)
    (fun i => e i - cc i) key n (Nat.lt_succ_self n)
  have hen : e n = 0 := by simp [he_def, Nat.one_le_iff_ne_zero.mp hn]
  have : e n - cc n = 0 := hzero
  rw [hen, zero_sub, neg_eq_zero] at this
  simp only [aCoeff, ← hcc_def]
  exact this


-- @@ L1990-1998 verbatim
theorem clearPow_mem (v : Place K F) (f : F) {N : ℕ} (hN : (-v.ord f).toNat ≤ N) :
    v.uniformizer ^ (N + 1) * f ∈ v.toValuationSubring := by
  rcases eq_or_ne f 0 with rfl | hf0
  · rw [mul_zero]; exact zero_mem _
  · refine (v.mem_iff_ord_nonneg (mul_ne_zero (v.uniformizer_pow_ne_zero _) hf0)).mpr ?_
    rw [v.ord_mul (v.uniformizer_pow_ne_zero _) hf0, v.ord_uniformizer_pow]
    have h := Int.self_le_toNat (-v.ord f)
    have hNc : ((-v.ord f).toNat : ℤ) ≤ (N : ℤ) := by exact_mod_cast hN
    omega


-- @@ L2000-2003 verbatim
noncomputable def clearedHat (v : Place K F) (f : F) {N : ℕ} (hN : (-v.ord f).toNat ≤ N) :
    lg37_completion v :=
  algebraMap v.toValuationSubring (lg37_completion v)
    ⟨v.uniformizer ^ (N + 1) * f, clearPow_mem v f hN⟩


-- @@ L2005-2007 verbatim
noncomputable def resStar (v : Place K F) (S : Lg37CompletionSection v) (f : F) :
    v.ResidueField :=
  aCoeff v S ((-v.ord f).toNat) (clearedHat v f (le_refl _))


-- @@ L2009-2022 verbatim
theorem aCoeff_clearedHat_of_le (v : Place K F) (S : Lg37CompletionSection v) (f : F)
    {N : ℕ} (hN : (-v.ord f).toNat ≤ N) :
    aCoeff v S N (clearedHat v f hN) = resStar v S f := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hN
  unfold clearedHat resStar
  have hfac : (⟨v.uniformizer ^ (((-v.ord f).toNat + k) + 1) * f,
        clearPow_mem v f hN⟩ : v.toValuationSubring)
      = v.uniformizerSubring ^ k
        * ⟨v.uniformizer ^ ((-v.ord f).toNat + 1) * f, clearPow_mem v f (le_refl _)⟩ := by
    apply Subtype.ext
    push_cast [v.coe_uniformizerSubring]
    ring
  rw [hfac, map_mul, map_pow]
  exact aCoeff_shift_pow v S ((-v.ord f).toNat) k _


-- @@ L2024-2038 verbatim
theorem resStar_add (v : Place K F) (S : Lg37CompletionSection v) (f g : F) :
    resStar v S (f + g) = resStar v S f + resStar v S g := by
  set N := (-v.ord f).toNat ⊔ (-v.ord g).toNat ⊔ (-v.ord (f + g)).toNat with hN
  have hf : (-v.ord f).toNat ≤ N := le_trans le_sup_left le_sup_left
  have hg : (-v.ord g).toNat ≤ N := le_trans le_sup_right le_sup_left
  have hfg : (-v.ord (f + g)).toNat ≤ N := le_sup_right
  rw [← aCoeff_clearedHat_of_le v S f hf, ← aCoeff_clearedHat_of_le v S g hg,
    ← aCoeff_clearedHat_of_le v S (f + g) hfg, ← aCoeff_add]
  congr 1
  unfold clearedHat
  rw [← map_add]
  congr 1
  apply Subtype.ext
  push_cast
  ring


-- @@ L2040-2053 verbatim
theorem resStar_smul (v : Place K F) (S : Lg37CompletionSection v) (c : K) (f : F) :
    resStar v S (c • f) = c • resStar v S f := by
  set N := (-v.ord (c • f)).toNat ⊔ (-v.ord f).toNat with hN
  have hcf : (-v.ord (c • f)).toNat ≤ N := le_sup_left
  have hf : (-v.ord f).toNat ≤ N := le_sup_right
  rw [← aCoeff_clearedHat_of_le v S (c • f) hcf, ← aCoeff_clearedHat_of_le v S f hf,
    Algebra.smul_def c (aCoeff v S N (clearedHat v f hf)), ← aCoeff_smul]
  congr 1
  unfold clearedHat
  rw [IsScalarTower.algebraMap_apply K v.toValuationSubring (lg37_completion v) c, ← map_mul]
  congr 1
  apply Subtype.ext
  push_cast [v.coe_algebraMap, Algebra.smul_def]
  ring


-- @@ L2055-2059 verbatim
noncomputable def resStarₗ (v : Place K F) (S : Lg37CompletionSection v) :
    F →ₗ[K] v.ResidueField where
  toFun := resStar v S
  map_add' := resStar_add v S
  map_smul' c f := by rw [RingHom.id_apply]; exact resStar_smul v S c f


-- @@ L2061-2079 verbatim
theorem resStar_simplePole (v : Place K F) (S : Lg37CompletionSection v) (f : F)
    (hf : v.uniformizer * f ∈ v.toValuationSubring) :
    resStar v S f = IsLocalRing.residue _ ⟨v.uniformizer * f, hf⟩ := by
  have hM : (-v.ord f).toNat ≤ 1 := by
    rcases eq_or_ne f 0 with rfl | hf0
    · rw [v.ord_zero]; simp
    · have hge : (0 : ℤ) ≤ v.ord (v.uniformizer * f) :=
        (v.mem_iff_ord_nonneg (mul_ne_zero v.uniformizer_ne_zero hf0)).mp hf
      rw [v.ord_mul v.uniformizer_ne_zero hf0, v.ord_uniformizer] at hge
      have := Int.self_le_toNat (-v.ord f)
      omega
  rw [← aCoeff_clearedHat_of_le v S f hM]
  unfold clearedHat
  have hfac : (⟨v.uniformizer ^ (1 + 1) * f, clearPow_mem v f hM⟩ : v.toValuationSubring)
      = v.uniformizerSubring * ⟨v.uniformizer * f, hf⟩ := by
    apply Subtype.ext
    push_cast [v.coe_uniformizerSubring]
    ring
  rw [hfac, map_mul, aCoeff_shift, aCoeff_zero, lg37_residueHat_algebraMap]


-- @@ L2081-2087 verbatim
theorem resStar_of_mem (v : Place K F) (S : Lg37CompletionSection v) {f : F}
    (hf : f ∈ v.toValuationSubring) : resStar v S f = 0 := by
  rw [resStar_simplePole v S f (mul_mem v.uniformizer_mem hf), IsLocalRing.residue_eq_zero_iff]
  have : (⟨v.uniformizer * f, mul_mem v.uniformizer_mem hf⟩ : v.toValuationSubring)
      = v.uniformizerSubring * ⟨f, hf⟩ := Subtype.ext rfl
  rw [this]
  exact Ideal.mul_mem_right _ _ v.uniformizerSubring_mem_maximalIdeal


-- @@ L2089-2108 verbatim
theorem resStar_higherPoleMonomial (v : Place K F) (S : Lg37CompletionSection v)
    {n : ℕ} (hn : 1 ≤ n) : resStar v S (v.uniformizer ^ (n + 1))⁻¹ = 0 := by
  have hord : v.ord (v.uniformizer ^ (n + 1))⁻¹ = -((n : ℤ) + 1) := by
    rw [v.ord_inv, v.ord_uniformizer_pow]; push_cast; ring
  have hM : (-v.ord (v.uniformizer ^ (n + 1))⁻¹).toNat = n + 1 := by
    rw [hord]; simp
  have hle : (-v.ord (v.uniformizer ^ (n + 1))⁻¹).toNat ≤ n + 1 := le_of_eq hM
  rw [← aCoeff_clearedHat_of_le v S (v.uniformizer ^ (n + 1))⁻¹ hle]
  unfold clearedHat
  have hfac : (⟨v.uniformizer ^ ((n + 1) + 1) * (v.uniformizer ^ (n + 1))⁻¹,
        clearPow_mem v (v.uniformizer ^ (n + 1))⁻¹ hle⟩ : v.toValuationSubring)
      = v.uniformizerSubring := by
    apply Subtype.ext
    push_cast [v.coe_uniformizerSubring]
    rw [pow_succ, mul_right_comm, mul_inv_cancel₀ (v.uniformizer_pow_ne_zero (n + 1)), one_mul]
  rw [hfac]
  have : algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring
      = algebraMap v.toValuationSubring (lg37_completion v) v.uniformizerSubring * 1 := by
    rw [mul_one]
  rw [this, aCoeff_shift, aCoeff_one_eq_zero v S hn]


-- @@ L2110-2115 verbatim
noncomputable def canonicalLocalResidueDataKStar (v : Place K F)
    (S : Lg37CompletionSection v) : v.CanonicalLocalResidueDataK where
  res := resStarₗ v S
  res_of_mem _f hf := resStar_of_mem v S hf
  res_simplePole f hf := resStar_simplePole v S f hf
  res_higherPoleMonomial _n hn := resStar_higherPoleMonomial v S hn


-- @@ L2117-2117 verbatim
section WitnessW

-- @@ L2118-2119 verbatim
variable {v : Place K F} {ℓ : v.toValuationSubring}
  (hℓ : IsLocalRing.residue v.toValuationSubring ℓ ∉ Set.range (algebraMap K v.ResidueField))

-- @@ L2120-2120 verbatim
include hℓ


-- @@ L2122-2122 verbatim
end WitnessW


-- @@ L2124-2124 verbatim
end ModularCurve.KwNo6Pin


-- @@ L2126-2126 verbatim
set_option autoImplicit false

-- @@ L2127-2127 verbatim
set_option maxHeartbeats 1600000


-- @@ L2129-2129 verbatim
open Polynomial IsLocalRing AlgebraicCurve

-- @@ L2130-2130 verbatim
open ModularCurve.Lg37 ModularCurve.KwNo6Section ModularCurve.KwNo6Pin

-- @@ L2131-2131 verbatim
open Mp72a102T1


-- @@ L2133-2133 verbatim
namespace AlgebraicCurve


-- @@ L2135-2135 verbatim
variable {K F : Type*} [Field K] [Field F] [Algebra K F]


-- @@ L2137-2147 verbatim
theorem completionSection_nonempty_generic (v : Place K F)
    [FiniteDimensional K v.ResidueField] [Algebra.IsSeparable K v.ResidueField] :
    Nonempty (Lg37CompletionSection v) := by
  obtain ⟨ᾱ, htop⟩ := Field.exists_primitive_element K v.ResidueField
  have hint : IsIntegral K ᾱ := Algebra.IsIntegral.isIntegral ᾱ
  have hmon : (minpoly K ᾱ).Monic := minpoly.monic hint
  have hsep : (minpoly K ᾱ).Separable := Algebra.IsSeparable.isSeparable K ᾱ
  have haevalbar : (aeval ᾱ) (minpoly K ᾱ) = 0 := minpoly.aeval K ᾱ
  obtain ⟨αhat, hαroot, hαres⟩ :=
    mp72a102_t1_exists_completion_root_of_residue_root v hmon hsep haevalbar
  exact ⟨sectionOfPrimitiveRoot v hint htop αhat hαroot hαres⟩


-- @@ L2149-2156 verbatim
noncomputable instance instHasCanonicalLocalResidueKStar [IsCurveOver K F] [PerfectField K] :
    HasCanonicalLocalResidueKStar K F where
  dataKStar v :=
    haveI : FiniteDimensional K v.ResidueField := Place.FiniteResidue.finite
    haveI : Algebra.IsSeparable K v.ResidueField :=
      Algebra.IsAlgebraic.isSeparable_of_perfectField
    canonicalLocalResidueDataKStar v
      (Classical.choice (completionSection_nonempty_generic v))


-- @@ L2158-2166 verbatim
theorem localResidue_eq_resStar [IsCurveOver K F] [PerfectField K] (v : Place K F)
    (S : Lg37CompletionSection v) (f : F) :
    v.localResidue f = resStar v S f := by
  haveI : FiniteDimensional K v.ResidueField := Place.FiniteResidue.finite
  haveI : Algebra.IsSeparable K v.ResidueField :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  show resStar v (Classical.choice (completionSection_nonempty_generic v)) f = resStar v S f
  unfold resStar
  exact aCoeff_section_indep v _ S _ _


-- @@ L2168-2171 verbatim
theorem localResidue_eq_resStarₗ [IsCurveOver K F] [PerfectField K] (v : Place K F)
    (S : Lg37CompletionSection v) :
    v.localResidue = resStarₗ v S :=
  LinearMap.ext (localResidue_eq_resStar v S)


-- @@ L2173-2173 verbatim
end AlgebraicCurve
