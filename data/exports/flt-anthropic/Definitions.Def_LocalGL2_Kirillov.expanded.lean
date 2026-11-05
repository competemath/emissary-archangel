import Mathlib
import Definitions.Def_AutomorphicForm_ConstantTerm
import Definitions.Def_NumberField_Completion_Finite


-- @@ L5-5 verbatim
set_option autoImplicit false

-- @@ L6-6 verbatim
set_option linter.unusedVariables false

-- @@ L7-7 verbatim
set_option linter.unusedSectionVars false

-- @@ L8-8 verbatim
set_option linter.style.longLine false


-- @@ L10-10 verbatim
open scoped Classical


-- @@ L12-12 verbatim
noncomputable section


-- @@ L14-14 verbatim
namespace LocalGL2.Kirillov


-- @@ L16-16 verbatim
open AutomorphicForm IsDedekindDomain NumberField


-- @@ L18-18 verbatim
variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))


-- @@ L20-20 verbatim
local notation "F" => HeightOneSpectrum.adicCompletion K v

-- @@ L21-21 verbatim
local notation "G" => GL (Fin 2) (HeightOneSpectrum.adicCompletion K v)

-- @@ L22-22 verbatim
local notation "Fx" => (HeightOneSpectrum.adicCompletion K v)ˣ

-- @@ L23-23 verbatim
local notation "Γ" => (WithZero (Multiplicative ℤ))ˣ


-- @@ L25-26 verbatim
def defectSet (ψ : AddChar F ℂ) (S : Submodule ℂ (G → ℂ)) : Set (G → ℂ) :=
  {V | ∃ U ∈ S, ∃ x : F, V = (fun g => U (g * unipotentGL2 x)) - ψ x • U}


-- @@ L28-29 verbatim
abbrev defectSpan (ψ : AddChar F ℂ) (S : Submodule ℂ (G → ℂ)) : Submodule ℂ (G → ℂ) :=
  Submodule.span ℂ (defectSet v ψ S)


-- @@ L31-34 verbatim
def rT (k : G) : (G → ℂ) →ₗ[ℂ] (G → ℂ) where
  toFun V := fun g => V (g * k)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- @@ L36-36 verbatim
@[simp] theorem rT_apply (k : G) (V : G → ℂ) (g : G) : rT v k V g = V (g * k) := rfl


-- @@ L38-39 verbatim
theorem rT_rT (k₁ k₂ : G) (V : G → ℂ) : rT v k₁ (rT v k₂ V) = rT v (k₁ * k₂) V := by
  funext g; simp [mul_assoc]


-- @@ L41-41 verbatim
@[simp] theorem rT_one (V : G → ℂ) : rT v 1 V = V := by funext g; simp


-- @@ L43-44 verbatim
abbrev coinv (ψ : AddChar F ℂ) (S : Submodule ℂ (G → ℂ)) : Submodule ℂ ((G → ℂ) ⧸ defectSpan v ψ S) :=
  S.map (defectSpan v ψ S).mkQ


-- @@ L46-50 verbatim
def dg (a : Fx) : G where
  val := !![(a : F), 0; 0, 1]
  inv := !![((a⁻¹ : Fx) : F), 0; 0, 1]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]


-- @@ L52-52 verbatim
@[simp] theorem dg_coe (a : Fx) : (dg v a : Matrix (Fin 2) (Fin 2) F) = !![(a : F), 0; 0, 1] := rfl


-- @@ L54-58 verbatim
theorem dg_mul (a b : Fx) : dg v (a * b) = dg v a * dg v b := by
  apply Units.ext
  simp only [Units.val_mul, dg_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]


-- @@ L60-64 verbatim
theorem dg_one : dg v 1 = 1 := by
  apply Units.ext
  simp only [dg_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp


-- @@ L66-71 verbatim
theorem dg_mul_unipotent (a : Fx) (x : F) :
    dg v a * unipotentGL2 x = unipotentGL2 ((a : F) * x) * dg v a := by
  apply Units.ext
  simp only [Units.val_mul, dg_coe, unipotentGL2_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]


-- @@ L73-77 verbatim
def wG : G where
  val := !![0, 1; 1, 0]
  inv := !![0, 1; 1, 0]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]


-- @@ L79-79 verbatim
@[simp] theorem wG_coe : (wG v : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := rfl


-- @@ L81-85 verbatim
theorem wG_mul_wG : wG v * wG v = 1 := by
  apply Units.ext
  simp only [Units.val_mul, wG_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]


-- @@ L87-91 verbatim
def zG (c : Fx) : G where
  val := !![(c : F), 0; 0, (c : F)]
  inv := !![((c⁻¹ : Fx) : F), 0; 0, ((c⁻¹ : Fx) : F)]
  val_inv := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  inv_val := by ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]


-- @@ L93-94 verbatim
@[simp] theorem zG_coe (c : Fx) :
    (zG v c : Matrix (Fin 2) (Fin 2) F) = !![(c : F), 0; 0, (c : F)] := rfl


-- @@ L96-100 verbatim
theorem zG_mul_comm (c : Fx) (k : G) : zG v c * k = k * zG v c := by
  apply Units.ext
  simp only [Units.val_mul, zG_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, mul_comm]


-- @@ L102-106 verbatim
theorem dg_mul_wG (a : Fx) : dg v a * wG v = wG v * zG v a * dg v a⁻¹ := by
  apply Units.ext
  simp only [Units.val_mul, dg_coe, wG_coe, zG_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]


-- @@ L108-112 verbatim
theorem zG_mul (c d : Fx) : zG v (c * d) = zG v c * zG v d := by
  apply Units.ext
  simp only [Units.val_mul, zG_coe]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]


-- @@ L114-118 verbatim
theorem zG_one : zG v 1 = 1 := by
  apply Units.ext
  simp only [zG_coe, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp


-- @@ L120-128 verbatim
theorem exists_unit_gt (y : F) : ∃ β₀ : Γ, Valued.v y < (β₀ : WithZero (Multiplicative ℤ)) := by
  rcases eq_or_ne y 0 with rfl | hy
  · exact ⟨1, by simp⟩
  · have hv : Valued.v y ≠ (0 : WithZero (Multiplicative ℤ)) := (Valuation.ne_zero_iff _).mpr hy
    obtain ⟨m, hm⟩ := WithZero.ne_zero_iff_exists.mp hv
    refine ⟨Units.mk0 ((m * Multiplicative.ofAdd (1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      WithZero.coe_ne_zero, ?_⟩
    rw [← hm, Units.val_mk0, WithZero.coe_lt_coe, ← Multiplicative.toAdd_lt, toAdd_mul, toAdd_ofAdd]
    exact lt_add_one _


-- @@ L130-140 verbatim
theorem exists_ball_subset_of_mem_nhds {s : Set F} (hs : s ∈ nhds (0 : F)) :
    ∃ δ : Γ, ∀ y : F, Valued.v y < (δ : WithZero (Multiplicative ℤ)) → y ∈ s := by
  obtain ⟨γ, hγ⟩ := (Valued.is_topological_valuation _).mp hs
  have hb : MonoidWithZeroHom.ValueGroup₀.embedding γ.val ≠ (0 : WithZero (Multiplicative ℤ)) := by
    intro h
    exact γ.ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective (h.trans (map_zero _).symm))
  refine ⟨Units.mk0 _ hb, fun y hy => ?_⟩
  apply hγ
  show Valued.v.restrict y < γ.val
  rw [Valuation.restrict_lt_iff_lt_embedding]
  simpa using hy


-- @@ L142-148 verbatim
theorem continuous_unipotentGL2 : Continuous (fun x : F => (unipotentGL2 x : G)) := by
  rw [Units.continuous_iff]
  constructor
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2_coe] <;> fun_prop
  · refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp [unipotentGL2] <;> fun_prop


-- @@ L150-157 verbatim
theorem exists_unipotent_mem_of_isOpen (K₀ : Subgroup G) (hK : IsOpen (K₀ : Set G)) :
    ∃ δ : Γ, ∀ z : F, Valued.v z < (δ : WithZero (Multiplicative ℤ)) → unipotentGL2 z ∈ K₀ := by
  have hU : ((fun z : F => (unipotentGL2 z : G)) ⁻¹' (K₀ : Set G)) ∈ nhds (0 : F) := by
    apply (hK.preimage (continuous_unipotentGL2 v)).mem_nhds
    show unipotentGL2 (0 : F) ∈ K₀
    rw [unipotentGL2_zero]
    exact K₀.one_mem
  exact exists_ball_subset_of_mem_nhds v hU


-- @@ L159-173 verbatim
theorem exists_forall_mem_of_continuous (K₀ : Subgroup G) (hK : IsOpen (K₀ : Set G)) (f : Fx → G)
    (hf : Continuous f) (hf1 : f 1 ∈ K₀) :
    ∃ δ : Γ, ∀ u : Fx, Valued.v ((u : F) - 1) < (δ : WithZero (Multiplicative ℤ)) → f u ∈ K₀ := by
  have h1 : (f ⁻¹' (K₀ : Set G)) ∈ nhds (1 : Fx) := (hK.preimage hf).mem_nhds hf1
  rw [Units.isEmbedding_val₀.toIsInducing.nhds_eq_comap] at h1
  obtain ⟨T, hT, hTsub⟩ := Filter.mem_comap.mp h1
  have hT' : T ∈ nhds (1 : F) := hT
  have hc : ContinuousAt (fun y : F => 1 + y) 0 := (continuous_const.add continuous_id).continuousAt
  have h0 : (fun y : F => 1 + y) ⁻¹' T ∈ nhds (0 : F) := hc.preimage_mem_nhds (by simpa using hT')
  obtain ⟨δ, hδ⟩ := exists_ball_subset_of_mem_nhds v h0
  refine ⟨δ, fun u hu => ?_⟩
  have hmem : (u : F) ∈ T := by
    have h := hδ _ hu
    simpa using h
  exact hTsub hmem


-- @@ L175-180 verbatim
theorem continuous_dg : Continuous (fun u : Fx => (dg v u : G)) := by
  have hφ : Continuous (fun a : F => !![a, 0; 0, (1 : F)]) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  rw [Units.continuous_iff]
  exact ⟨hφ.comp Units.continuous_val, hφ.comp Units.continuous_coe_inv⟩


-- @@ L182-187 verbatim
theorem continuous_zG : Continuous (fun c : Fx => (zG v c : G)) := by
  have hφ : Continuous (fun a : F => !![a, 0; 0, a]) := by
    refine continuous_pi fun i => continuous_pi fun j => ?_
    fin_cases i <;> fin_cases j <;> simp <;> fun_prop
  rw [Units.continuous_iff]
  exact ⟨hφ.comp Units.continuous_val, hφ.comp Units.continuous_coe_inv⟩


-- @@ L189-191 verbatim
theorem exists_dg_mem_of_isOpen (K₀ : Subgroup G) (hK : IsOpen (K₀ : Set G)) :
    ∃ δ : Γ, ∀ u : Fx, Valued.v ((u : F) - 1) < (δ : WithZero (Multiplicative ℤ)) → dg v u ∈ K₀ :=
  exists_forall_mem_of_continuous v K₀ hK _ (continuous_dg v) (by rw [dg_one]; exact K₀.one_mem)


-- @@ L193-195 verbatim
theorem exists_zG_mem_of_isOpen (K₀ : Subgroup G) (hK : IsOpen (K₀ : Set G)) :
    ∃ δ : Γ, ∀ c : Fx, Valued.v ((c : F) - 1) < (δ : WithZero (Multiplicative ℤ)) → zG v c ∈ K₀ :=
  exists_forall_mem_of_continuous v K₀ hK _ (continuous_zG v) (by rw [zG_one]; exact K₀.one_mem)


-- @@ L197-200 verbatim
theorem isCompact_integers : IsCompact {x : F | Valued.v x ≤ 1} := by
  have h := NumberField.isCompactAdicCompletionIntegers K v
  convert h using 1
  all_goals try rfl


-- @@ L202-206 verbatim
theorem isOpen_unit_ball : IsOpen {x : F | Valued.v x < (1 : WithZero (Multiplicative ℤ))} := by
  have h := Valued.isOpen_ball (R := F) 1
  convert h using 1
  ext x
  simp [Valuation.restrict_lt_iff_lt_embedding]


-- @@ L208-216 verbatim
theorem isCompact_valuation_eq_one : IsCompact {x : F | Valued.v x = 1} := by
  have hclosed : IsClosed {x : F | Valued.v x = 1} := by
    have h1 : IsClosed {x : F | Valued.v x ≤ 1} := (isCompact_integers v).isClosed
    have h2 : IsClosed {x : F | Valued.v x < (1 : WithZero (Multiplicative ℤ))}ᶜ := (isOpen_unit_ball v).isClosed_compl
    convert h1.inter h2 using 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_compl_iff, not_lt]
    exact ⟨fun h => ⟨h.le, h.ge⟩, fun h => le_antisymm h.1 h.2⟩
  exact (isCompact_integers v).of_isClosed_subset hclosed (fun x hx => le_of_eq hx)


-- @@ L218-225 verbatim
theorem exists_valuation_eq (r : Γ) : ∃ c : F, Valued.v c = (r : WithZero (Multiplicative ℤ)) := by
  obtain ⟨π, hπ⟩ := v.valuation_exists_uniformizer K
  have hπ' : Valued.v ((π : K) : F) = WithZero.exp (-1 : ℤ) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact hπ
  refine ⟨((π : K) : F) ^ (-WithZero.log (r : WithZero (Multiplicative ℤ))), ?_⟩
  rw [map_zpow₀, hπ', ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, neg_neg,
    WithZero.exp_log r.ne_zero]


-- @@ L227-243 verbatim
theorem isOpen_radiusBall (r : Γ) : IsOpen {x : F | Valued.v x < (r : WithZero (Multiplicative ℤ))} := by
  obtain ⟨c, hc⟩ := exists_valuation_eq v r
  have hset : {x : F | Valued.v x < (r : WithZero (Multiplicative ℤ))}
      = (fun x : F => c⁻¹ * x) ⁻¹' {y : F | Valued.v y < (1 : WithZero (Multiplicative ℤ))} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, map_mul, map_inv₀, hc]
    constructor
    · intro hx
      calc ((r : WithZero (Multiplicative ℤ)))⁻¹ * Valued.v x
          < ((r : WithZero (Multiplicative ℤ)))⁻¹ * (r : WithZero (Multiplicative ℤ)) :=
            mul_lt_mul_of_pos_left hx (zero_lt_iff.mpr (inv_ne_zero r.ne_zero))
        _ = 1 := inv_mul_cancel₀ r.ne_zero
    · intro hx
      have h := mul_lt_mul_of_pos_left hx (zero_lt_iff.mpr r.ne_zero)
      rwa [← mul_assoc, mul_inv_cancel₀ r.ne_zero, one_mul, mul_one] at h
  rw [hset]
  exact (isOpen_unit_ball v).preimage (continuous_const.mul continuous_id)


-- @@ L245-249 verbatim
theorem radiusBall_mem_nhds (y : F) (r : Γ) :
    {x : F | Valued.v (x - y) < (r : WithZero (Multiplicative ℤ))} ∈ nhds y := by
  have hopen : IsOpen {x : F | Valued.v (x - y) < (r : WithZero (Multiplicative ℤ))} :=
    (isOpen_radiusBall v r).preimage (continuous_id.sub continuous_const)
  exact hopen.mem_nhds (by simp)


-- @@ L251-261 verbatim
def UF : Subgroup Fx where
  carrier := {u | Valued.v (u : F) = 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Units.val_mul, map_mul] at ha hb ⊢
    rw [ha, hb, mul_one]
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Units.val_inv_eq_inv_val, map_inv₀] at ha ⊢
    rw [ha, inv_one]


-- @@ L263-263 verbatim
theorem v_coe_UF (u : UF v) : Valued.v ((u : Fx) : F) = 1 := u.2


-- @@ L265-286 verbatim
def Um (δ : Γ) : Subgroup (UF v) where
  carrier := {u | Valued.v (((u : Fx) : F) - 1) < (δ : WithZero (Multiplicative ℤ))}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    have e : (((a * b : UF v) : Fx) : F) - 1 = ((a : Fx) : F) * (((b : Fx) : F) - 1) + (((a : Fx) : F) - 1) := by
      simp only [Subgroup.coe_mul, Units.val_mul]
      ring
    rw [e]
    refine (Valuation.map_add _ _ _).trans_lt (max_lt ?_ ha)
    rw [map_mul, v_coe_UF, one_mul]
    exact hb
  one_mem' := by simp
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have e : (((a⁻¹ : UF v) : Fx) : F) - 1 = (((a⁻¹ : UF v) : Fx) : F) * (1 - ((a : Fx) : F)) := by
      have h : (((a⁻¹ : UF v) : Fx) : F) * ((a : Fx) : F) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
      rw [mul_sub, mul_one, h]
    rw [e, map_mul, v_coe_UF, one_mul, Valuation.map_sub_swap]
    exact ha


-- @@ L288-289 verbatim
theorem mem_Um_iff (δ : Γ) (u : UF v) :
    u ∈ Um v δ ↔ Valued.v (((u : Fx) : F) - 1) < (δ : WithZero (Multiplicative ℤ)) := Iff.rfl


-- @@ L291-291 verbatim
abbrev Qm (δ : Γ) : Type := UF v ⧸ Um v δ


-- @@ L293-302 verbatim
theorem mk_eq_mk_of_close (δ : Γ) (u x : UF v)
    (h : Valued.v (((x : Fx) : F) - ((u : Fx) : F)) < (δ : WithZero (Multiplicative ℤ))) :
    ((x : Qm v δ) = (u : Qm v δ)) := by
  rw [QuotientGroup.eq, mem_Um_iff]
  have e : (((x⁻¹ * u : UF v) : Fx) : F) - 1 = (((x⁻¹ : UF v) : Fx) : F) * (((u : Fx) : F) - ((x : Fx) : F)) := by
    have h1 : (((x⁻¹ : UF v) : Fx) : F) * ((x : Fx) : F) = 1 := by
      rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel, Subgroup.coe_one, Units.val_one]
    rw [mul_sub, h1, Subgroup.coe_mul, Units.val_mul]
  rw [e, map_mul, v_coe_UF, one_mul, Valuation.map_sub_swap]
  exact h


-- @@ L304-332 verbatim
instance finite_Qm (δ : Γ) : Finite (Qm v δ) := by
  obtain ⟨T, hT, hcover⟩ := (isCompact_valuation_eq_one v).elim_nhds_subcover
    (fun y => {x : F | Valued.v (x - y) < (δ : WithZero (Multiplicative ℤ))}) (fun y _ => radiusBall_mem_nhds v y δ)

  have hsurj : ∀ q : Qm v δ, ∃ t ∈ T, ∃ u : UF v, ((u : Fx) : F) = t ∧ (u : Qm v δ) = q := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : ((x : Fx) : F) ∈ {x : F | Valued.v x = 1} := v_coe_UF v x
    have hxU := hcover hx
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop] at hxU
    obtain ⟨t, htT, hxt⟩ := hxU
    have ht1 : Valued.v t = 1 := hT t htT
    have ht0 : t ≠ 0 := by
      rintro rfl
      simp at ht1
    refine ⟨t, htT, ⟨Units.mk0 t ht0, ?_⟩, rfl, ?_⟩
    · show Valued.v ((Units.mk0 t ht0 : Fx) : F) = 1
      simpa using ht1
    · exact (mk_eq_mk_of_close v δ _ _ (by simpa using hxt)).symm
  choose ft hftT fu hfu hfq using hsurj

  have hinj : Function.Injective (fun q : Qm v δ => (⟨ft q, hftT q⟩ : T)) := by
    intro q₁ q₂ h
    have h' : ft q₁ = ft q₂ := congrArg Subtype.val h
    rw [← hfq q₁, ← hfq q₂]
    have hu : ((fu q₁ : Fx) : F) = ((fu q₂ : Fx) : F) := by rw [hfu, hfu, h']
    have hu' : fu q₁ = fu q₂ := Subtype.ext (Units.ext hu)
    rw [hu']
  exact Finite.of_injective _ hinj


-- @@ L334-334 verbatim
instance fintype_Qm (δ : Γ) : Fintype (Qm v δ) := Fintype.ofFinite _


-- @@ L336-336 verbatim
def rep (δ : Γ) (q : Qm v δ) : UF v := q.out


-- @@ L338-338 verbatim
theorem mk_rep (δ : Γ) (q : Qm v δ) : ((rep v δ q : UF v) : Qm v δ) = q := QuotientGroup.out_eq' q


-- @@ L340-340 verbatim
section charGeneric


-- @@ L342-342 verbatim
variable {A : Type*} [AddCommGroup A]


-- @@ L344-344 verbatim
abbrev charAddCommGroup : AddCommGroup (AddChar A ℂ) := inferInstance


-- @@ L346-346 verbatim
abbrev charFintype [Finite A] : Fintype (AddChar A ℂ) := inferInstance


-- @@ L348-348 verbatim
theorem char_map_add (ψ : AddChar A ℂ) (a b : A) : ψ (a + b) = ψ a * ψ b := AddChar.map_add_eq_mul ψ a b


-- @@ L350-350 verbatim
theorem char_map_zero (ψ : AddChar A ℂ) : ψ 0 = 1 := AddChar.map_zero_eq_one ψ


-- @@ L352-352 verbatim
theorem char_map_neg (ψ : AddChar A ℂ) (a : A) : ψ (-a) = (ψ a)⁻¹ := AddChar.map_neg_eq_inv ψ a


-- @@ L354-354 verbatim
theorem char_add_apply (ψ φ : AddChar A ℂ) (a : A) : (ψ + φ) a = ψ a * φ a := AddChar.add_apply ψ φ a


-- @@ L356-356 verbatim
theorem char_neg_apply (ψ : AddChar A ℂ) (a : A) : (-ψ) a = (ψ a)⁻¹ := AddChar.neg_apply' ψ a


-- @@ L358-358 verbatim
theorem char_zero_apply (a : A) : (0 : AddChar A ℂ) a = 1 := AddChar.zero_apply a


-- @@ L360-360 verbatim
theorem char_ext {ψ φ : AddChar A ℂ} (h : ∀ a : A, ψ a = φ a) : ψ = φ := AddChar.ext ψ φ h


-- @@ L362-365 verbatim
theorem char_sum_apply_of_eq_zero [Fintype A] {a : A} (ha : a = 0) :
    ∑ ψ : AddChar A ℂ, ψ a = (Fintype.card A : ℂ) := by
  classical
  rw [AddChar.sum_apply_eq_ite, if_pos ha]


-- @@ L367-369 verbatim
theorem char_sum_apply_of_ne_zero [Fintype A] {a : A} (ha : a ≠ 0) : ∑ ψ : AddChar A ℂ, ψ a = 0 := by
  classical
  rw [AddChar.sum_apply_eq_ite, if_neg ha]


-- @@ L371-373 verbatim
theorem char_sum_of_eq_zero [Fintype A] {ψ : AddChar A ℂ} (hψ : ψ = 0) : ∑ a, ψ a = (Fintype.card A : ℂ) := by
  classical
  rw [AddChar.sum_eq_ite, if_pos hψ]


-- @@ L375-377 verbatim
theorem char_sum_of_ne_zero [Fintype A] {ψ : AddChar A ℂ} (hψ : ψ ≠ 0) : ∑ a, ψ a = 0 := by
  classical
  rw [AddChar.sum_eq_ite, if_neg hψ]


-- @@ L379-379 verbatim
end charGeneric


-- @@ L381-382 verbatim
instance addCommGroup_additive_Qm (δ : Γ) : AddCommGroup (Additive (Qm v δ)) :=
  @Additive.addCommGroup _ (QuotientGroup.Quotient.commGroup _)


-- @@ L384-384 verbatim
instance finite_additive_Qm (δ : Γ) : Finite (Additive (Qm v δ)) := Finite.of_equiv _ Additive.ofMul


-- @@ L386-386 verbatim
def Ch (δ : Γ) : Type := AddChar (Additive (Qm v δ)) ℂ


-- @@ L388-388 verbatim
instance addCommGroup_Ch (δ : Γ) : AddCommGroup (Ch v δ) := charAddCommGroup (A := Additive (Qm v δ))


-- @@ L390-390 verbatim
instance fintype_Ch (δ : Γ) : Fintype (Ch v δ) := charFintype (A := Additive (Qm v δ))


-- @@ L392-392 verbatim
instance decidableEq_Ch (δ : Γ) : DecidableEq (Ch v δ) := Classical.decEq _


-- @@ L394-396 verbatim
variable {v} in

def Ch.toChar {δ : Γ} (χ : Ch v δ) : AddChar (Additive (Qm v δ)) ℂ := χ


-- @@ L398-400 verbatim
variable {v} in

def chv {δ : Γ} (χ : Ch v δ) (u : UF v) : ℂ := Ch.toChar χ (Additive.ofMul (u : Qm v δ))


-- @@ L402-406 verbatim
variable {v} in
theorem chv_mul {δ : Γ} (χ : Ch v δ) (u w : UF v) : chv χ (u * w) = chv χ u * chv χ w := by
  unfold chv
  rw [QuotientGroup.mk_mul, ofMul_mul]
  exact char_map_add (Ch.toChar χ) _ _


-- @@ L408-412 verbatim
variable {v} in
theorem chv_one {δ : Γ} (χ : Ch v δ) : chv χ (1 : UF v) = 1 := by
  unfold chv
  rw [QuotientGroup.mk_one, ofMul_one]
  exact char_map_zero (Ch.toChar χ)


-- @@ L414-418 verbatim
variable {v} in
theorem chv_inv {δ : Γ} (χ : Ch v δ) (u : UF v) : chv χ u⁻¹ = (chv χ u)⁻¹ := by
  unfold chv
  rw [QuotientGroup.mk_inv, ofMul_inv]
  exact char_map_neg (Ch.toChar χ) _


-- @@ L420-425 verbatim
variable {v} in
theorem chv_ne_zero {δ : Γ} (χ : Ch v δ) (u : UF v) : chv χ u ≠ 0 := by
  intro h
  have h1 := chv_mul χ u u⁻¹
  rw [mul_inv_cancel, chv_one, h, zero_mul] at h1
  exact one_ne_zero h1


-- @@ L427-432 verbatim
variable {v} in

theorem chv_of_mem {δ : Γ} (χ : Ch v δ) {m : UF v} (hm : m ∈ Um v δ) : chv χ m = 1 := by
  unfold chv
  rw [(QuotientGroup.eq_one_iff m).mpr hm, ofMul_one]
  exact char_map_zero (Ch.toChar χ)


-- @@ L434-436 verbatim
variable {v} in
theorem chv_add {δ : Γ} (χ ρ : Ch v δ) (u : UF v) : chv (χ + ρ) u = chv χ u * chv ρ u :=
  char_add_apply (A := Additive (Qm v δ)) χ ρ _


-- @@ L438-440 verbatim
variable {v} in
theorem chv_neg {δ : Γ} (χ : Ch v δ) (u : UF v) : chv (-χ) u = (chv χ u)⁻¹ :=
  char_neg_apply (A := Additive (Qm v δ)) χ _


-- @@ L442-444 verbatim
variable {v} in
theorem chv_zero {δ : Γ} (u : UF v) : chv (0 : Ch v δ) u = 1 :=
  char_zero_apply (A := Additive (Qm v δ)) _


-- @@ L446-455 verbatim
variable {v} in

theorem ext_chv {δ : Γ} {χ ρ : Ch v δ} (h : ∀ u : UF v, chv χ u = chv ρ u) : χ = ρ := by
  apply char_ext (A := Additive (Qm v δ))
  intro a
  obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (Additive.toMul a)
  have h1 := h u
  unfold chv Ch.toChar at h1
  rw [hu, ofMul_toMul] at h1
  exact h1


-- @@ L457-465 verbatim
variable {v} in

theorem sum_chv_eq {δ : Γ} (u : UF v) :
    ∑ χ : Ch v δ, chv χ u = if (u : Qm v δ) = 1 then (Fintype.card (Qm v δ) : ℂ) else 0 := by
  unfold chv
  rw [Fintype.card_congr (Additive.ofMul : Qm v δ ≃ Additive (Qm v δ))]
  split_ifs with h
  · exact char_sum_apply_of_eq_zero (A := Additive (Qm v δ)) (ofMul_eq_zero.mpr h)
  · exact char_sum_apply_of_ne_zero (A := Additive (Qm v δ)) (fun h' => h (ofMul_eq_zero.mp h'))


-- @@ L467-474 verbatim
variable {v} in

theorem sum_toChar_eq {δ : Γ} (χ : Ch v δ) :
    ∑ a : Additive (Qm v δ), Ch.toChar χ a = if χ = 0 then (Fintype.card (Qm v δ) : ℂ) else 0 := by
  rw [Fintype.card_congr (Additive.ofMul : Qm v δ ≃ Additive (Qm v δ))]
  split_ifs with h
  · exact char_sum_of_eq_zero (A := Additive (Qm v δ)) (by rw [h]; rfl)
  · exact char_sum_of_ne_zero (A := Additive (Qm v δ)) h


-- @@ L476-476 verbatim
section fourier


-- @@ L478-478 verbatim
variable {X : Type*} [AddCommGroup X] [Module ℂ X]


-- @@ L480-480 verbatim
def IsLvl (δ : Γ) (f : UF v → X) : Prop := ∀ u : UF v, ∀ m ∈ Um v δ, f (u * m) = f u


-- @@ L482-483 verbatim
def comp (δ : Γ) (f : UF v → X) (χ : Ch v δ) : X :=
  (Fintype.card (Qm v δ) : ℂ)⁻¹ • ∑ q : Qm v δ, chv χ (rep v δ q) • f (rep v δ q)


-- @@ L485-486 verbatim
theorem size_Qm_ne_zero (δ : Γ) : (Fintype.card (Qm v δ) : ℂ) ≠ 0 := by
  exact_mod_cast (Fintype.card_ne_zero : Fintype.card (Qm v δ) ≠ 0)


-- @@ L488-494 verbatim
omit [AddCommGroup X] [Module ℂ X] in
theorem apply_rep_mk_of_isLvl {δ : Γ} {f : UF v → X} (hf : IsLvl v δ f) (u : UF v) :
    f (rep v δ (u : Qm v δ)) = f u := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (Um v δ) u
  show f ((u : Qm v δ).out) = f u
  rw [hm]
  exact hf u m m.2


-- @@ L496-498 verbatim
theorem mk_mul_inv_eq_one_iff (δ : Γ) (q : Qm v δ) (u : UF v) :
    ((rep v δ q * u⁻¹ : UF v) : Qm v δ) = 1 ↔ q = (u : Qm v δ) := by
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mk_rep, mul_inv_eq_one]


-- @@ L500-506 verbatim
theorem chv_rep_mk {δ δ₁ : Γ} (hδ : δ ≤ δ₁) (χ : Ch v δ₁) (u : UF v) :
    chv χ (rep v δ (u : Qm v δ)) = chv χ u := by
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (Um v δ) u
  have hm₁ : (m : UF v) ∈ Um v δ₁ :=
    (mem_Um_iff v δ₁ m).mpr (((mem_Um_iff v δ m).mp m.2).trans_le (Units.val_le_val.mpr hδ))
  show chv χ ((u : Qm v δ).out) = chv χ u
  rw [hm, chv_mul, chv_of_mem χ hm₁, mul_one]


-- @@ L508-525 verbatim
def chOfFun (δ : Γ) (f : UF v → ℂ) (hmul : ∀ u w : UF v, f (u * w) = f u * f w)
    (htriv : ∀ m ∈ Um v δ, f m = 1) : Ch v δ where
  toFun a := f (rep v δ (Additive.toMul a))
  map_zero_eq_one' := by
    show f (rep v δ (1 : Qm v δ)) = 1
    apply htriv
    rw [← QuotientGroup.eq_one_iff, mk_rep]
  map_add_eq_mul' a b := by
    show f (rep v δ (Additive.toMul a * Additive.toMul b)) =
      f (rep v δ (Additive.toMul a)) * f (rep v δ (Additive.toMul b))
    rw [← hmul]
    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (Um v δ)
      (rep v δ (Additive.toMul a) * rep v δ (Additive.toMul b))
    have hclass : rep v δ (Additive.toMul a * Additive.toMul b) =
        ((rep v δ (Additive.toMul a) * rep v δ (Additive.toMul b) : UF v) : Qm v δ).out := by
      unfold rep
      rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq']
    rw [hclass, hm, hmul, htriv m m.2, mul_one]


-- @@ L527-533 verbatim
theorem chv_chOfFun (δ : Γ) (f : UF v → ℂ) (hmul : ∀ u w : UF v, f (u * w) = f u * f w)
    (htriv : ∀ m ∈ Um v δ, f m = 1) (u : UF v) : chv (chOfFun v δ f hmul htriv) u = f u := by
  show f (rep v δ (Additive.toMul (Additive.ofMul (u : Qm v δ)))) = f u
  rw [toMul_ofMul]
  obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (Um v δ) u
  show f ((u : Qm v δ).out) = f u
  rw [hm, hmul, htriv m m.2, mul_one]


-- @@ L535-536 verbatim
theorem Um_mono {δ δ₁ : Γ} (h : δ ≤ δ₁) : Um v δ ≤ Um v δ₁ := fun m hm =>
  ((mem_Um_iff v δ m).mp hm).trans_le (Units.val_le_val.mpr h)


-- @@ L538-539 verbatim
def refineCh {δ δ₁ : Γ} (h : δ ≤ δ₁) (τ : Ch v δ₁) : Ch v δ :=
  chOfFun v δ (chv τ) (chv_mul τ) fun _ hm => chv_of_mem τ (Um_mono v h hm)


-- @@ L541-542 verbatim
theorem chv_refineCh {δ δ₁ : Γ} (h : δ ≤ δ₁) (τ : Ch v δ₁) (u : UF v) : chv (refineCh v h τ) u = chv τ u :=
  chv_chOfFun v δ _ _ _ u


-- @@ L544-545 verbatim
theorem refineCh_zero {δ δ₁ : Γ} (h : δ ≤ δ₁) : refineCh v h (0 : Ch v δ₁) = 0 :=
  ext_chv fun u => by rw [chv_refineCh, chv_zero, chv_zero]


-- @@ L547-552 verbatim
theorem refineCh_ne_zero {δ δ₁ : Γ} (h : δ ≤ δ₁) {γ : Ch v δ₁} (hγ : γ ≠ 0) : refineCh v h γ ≠ 0 := by
  intro h0
  apply hγ
  apply ext_chv
  intro u
  rw [← chv_refineCh v h γ u, h0, chv_zero, chv_zero]


-- @@ L554-584 verbatim
theorem sum_inv_chv_smul_comp {δ : Γ} {f : UF v → X} (hf : IsLvl v δ f) (u : UF v) :
    ∑ χ : Ch v δ, (chv χ u)⁻¹ • comp v δ f χ = f u := by
  have h1 : ∀ χ : Ch v δ, (chv χ u)⁻¹ • comp v δ f χ =
      (Fintype.card (Qm v δ) : ℂ)⁻¹ • ∑ q : Qm v δ, chv χ (rep v δ q * u⁻¹) • f (rep v δ q) := by
    intro χ
    unfold comp
    rw [smul_comm]
    congr 1
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [smul_smul, chv_mul, chv_inv, mul_comm]
  have h2 : ∀ q : Qm v δ, (∑ χ : Ch v δ, chv χ (rep v δ q * u⁻¹)) • f (rep v δ q) =
      if q = (u : Qm v δ) then (Fintype.card (Qm v δ) : ℂ) • f (rep v δ q) else 0 := by
    intro q
    rw [sum_chv_eq, ite_smul, zero_smul]
    exact if_congr (mk_mul_inv_eq_one_iff v δ q u) rfl rfl
  calc ∑ χ : Ch v δ, (chv χ u)⁻¹ • comp v δ f χ
      = (Fintype.card (Qm v δ) : ℂ)⁻¹ •
          ∑ χ : Ch v δ, ∑ q : Qm v δ, chv χ (rep v δ q * u⁻¹) • f (rep v δ q) := by
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun χ _ => h1 χ
    _ = (Fintype.card (Qm v δ) : ℂ)⁻¹ •
          ∑ q : Qm v δ, (∑ χ : Ch v δ, chv χ (rep v δ q * u⁻¹)) • f (rep v δ q) := by
        rw [Finset.sum_comm]
        congr 1
        exact Finset.sum_congr rfl fun q _ => (Finset.sum_smul).symm
    _ = (Fintype.card (Qm v δ) : ℂ)⁻¹ • ((Fintype.card (Qm v δ) : ℂ) • f (rep v δ (u : Qm v δ))) := by
        congr 1
        simp only [h2, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    _ = f u := by
        rw [smul_smul, inv_mul_cancel₀ (size_Qm_ne_zero v δ), one_smul, apply_rep_mk_of_isLvl v hf]


-- @@ L586-589 verbatim
theorem eq_zero_of_forall_comp_eq_zero {δ : Γ} {f : UF v → X} (hf : IsLvl v δ f)
    (h : ∀ χ : Ch v δ, comp v δ f χ = 0) (u : UF v) : f u = 0 := by
  rw [← sum_inv_chv_smul_comp v hf u]
  simp [h]


-- @@ L591-596 verbatim
theorem comp_add (δ : Γ) (f g : UF v → X) (χ : Ch v δ) :
    comp v δ (fun w => f w + g w) χ = comp v δ f χ + comp v δ g χ := by
  unfold comp
  rw [← smul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun q _ => smul_add _ _ _


-- @@ L598-603 verbatim
theorem comp_sub (δ : Γ) (f g : UF v → X) (χ : Ch v δ) :
    comp v δ (fun w => f w - g w) χ = comp v δ f χ - comp v δ g χ := by
  unfold comp
  rw [← smul_sub, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun q _ => smul_sub _ _ _


-- @@ L605-611 verbatim
theorem comp_const_smul (δ : Γ) (c : ℂ) (f : UF v → X) (χ : Ch v δ) :
    comp v δ (fun w => c • f w) χ = c • comp v δ f χ := by
  unfold comp
  rw [smul_comm]
  congr 1
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun q _ => smul_comm (chv χ (rep v δ q)) c (f (rep v δ q))


-- @@ L613-615 verbatim
theorem comp_const_mul (δ : Γ) (c : ℂ) (g : UF v → ℂ) (γ : Ch v δ) :
    comp v δ (fun u => c * g u) γ = c * comp v δ g γ :=
  comp_const_smul v δ c g γ


-- @@ L617-622 verbatim
theorem comp_smul_const (δ : Γ) (g : UF v → ℂ) (ξ : X) (χ : Ch v δ) :
    comp v δ (fun w => g w • ξ) χ = comp v δ g χ • ξ := by
  unfold comp
  rw [smul_assoc, Finset.sum_smul]
  congr 1
  exact Finset.sum_congr rfl fun q _ => (smul_assoc _ _ _).symm


-- @@ L624-629 verbatim
theorem comp_chv_smul (δ : Γ) (ρ : Ch v δ) (f : UF v → X) (χ : Ch v δ) :
    comp v δ (fun w => chv ρ w • f w) χ = comp v δ f (χ + ρ) := by
  unfold comp
  congr 1
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [smul_smul, chv_add]


-- @@ L631-645 verbatim
theorem comp_chv (δ : Γ) (ρ χ : Ch v δ) :
    comp v δ (fun w => chv ρ w) χ = if χ + ρ = 0 then 1 else 0 := by
  unfold comp
  have h : ∀ q : Qm v δ, chv χ (rep v δ q) • chv ρ (rep v δ q) = chv (χ + ρ) (rep v δ q) := by
    intro q
    rw [smul_eq_mul, chv_add]
  simp only [h]
  have h2 : ∑ q : Qm v δ, chv (χ + ρ) (rep v δ q) = ∑ a : Additive (Qm v δ), Ch.toChar (χ + ρ) a := by
    unfold chv
    simp only [mk_rep]
    exact Fintype.sum_equiv Additive.ofMul _ _ (fun _ => rfl)
  rw [h2, sum_toChar_eq]
  split_ifs
  · rw [smul_eq_mul, inv_mul_cancel₀ (size_Qm_ne_zero v δ)]
  · simp


-- @@ L647-653 verbatim
theorem comp_sum {ι : Type*} (δ : Γ) (s : Finset ι) (f : ι → UF v → X) (χ : Ch v δ) :
    comp v δ (fun w => ∑ i ∈ s, f i w) χ = ∑ i ∈ s, comp v δ (f i) χ := by
  unfold comp
  rw [← Finset.smul_sum]
  congr 1
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.smul_sum


-- @@ L655-657 verbatim
theorem comp_zero (δ : Γ) (χ : Ch v δ) : comp v δ (fun _ : UF v => (0 : X)) χ = 0 := by
  unfold comp
  simp


-- @@ L659-665 verbatim
theorem comp_const (δ : Γ) (ξ : X) (γ : Ch v δ) :
    comp v δ (fun _ : UF v => ξ) γ = if γ = 0 then ξ else 0 := by
  have h : (fun _ : UF v => ξ) = fun u => chv (0 : Ch v δ) u • ξ := by
    funext u
    rw [chv_zero, one_smul]
  rw [h, comp_smul_const, comp_chv, add_zero]
  split_ifs <;> simp


-- @@ L667-672 verbatim
theorem comp_mul_chv_smul (δ : Γ) (c : ℂ) (χ : Ch v δ) (ξ : X)
    (γ : Ch v δ) : comp v δ (fun u => (c * chv χ u) • ξ) γ = if γ + χ = 0 then c • ξ else 0 := by
  have h : (fun u => (c * chv χ u) • ξ) = fun u => chv χ u • (c • ξ) := by
    funext u
    rw [smul_smul, mul_comm]
  rw [h, comp_chv_smul, comp_const]


-- @@ L674-680 verbatim
omit [AddCommGroup X] [Module ℂ X] in

theorem apply_eq_of_mk_eq_of_isLvl {δ : Γ} {f : UF v → X} (hf : IsLvl v δ f) {u w : UF v}
    (h : (u : Qm v δ) = (w : Qm v δ)) : f u = f w := by
  rw [QuotientGroup.eq] at h
  have hw : w = u * (u⁻¹ * w) := (mul_inv_cancel_left u w).symm
  rw [hw, hf u _ h]


-- @@ L682-686 verbatim
theorem chv_eq_of_mk_eq {δ δ₁ : Γ} (hδ : δ ≤ δ₁) (τ : Ch v δ₁) {u w : UF v}
    (h : (u : Qm v δ) = (w : Qm v δ)) : chv τ u = chv τ w := by
  rw [QuotientGroup.eq] at h
  have hw : w = u * (u⁻¹ * w) := (mul_inv_cancel_left u w).symm
  rw [hw, chv_mul, chv_of_mem τ (Um_mono v hδ h), mul_one]


-- @@ L688-690 verbatim
omit [AddCommGroup X] [Module ℂ X] in
theorem isLvl_mono {δ δ₁ : Γ} (h : δ ≤ δ₁) {f : UF v → X}
    (hf : IsLvl v δ₁ f) : IsLvl v δ f := fun u m hm => hf u m (Um_mono v h hm)


-- @@ L692-693 verbatim
theorem isLvl_chv {δ : Γ} (τ : Ch v δ) : IsLvl v δ (chv τ) := fun u m hm => by
  rw [chv_mul, chv_of_mem τ hm, mul_one]


-- @@ L695-696 verbatim
def qmap {δ' δ : Γ} (h : δ' ≤ δ) : Qm v δ' →* Qm v δ :=
  QuotientGroup.map (Um v δ') (Um v δ) (MonoidHom.id (UF v)) fun _ hm => Um_mono v h hm


-- @@ L698-698 verbatim
theorem qmap_mk {δ' δ : Γ} (h : δ' ≤ δ) (u : UF v) : qmap v h (u : Qm v δ') = (u : Qm v δ) := rfl


-- @@ L700-703 verbatim
theorem qmap_surjective {δ' δ : Γ} (h : δ' ≤ δ) : Function.Surjective (qmap v h) := by
  intro q
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨(u : Qm v δ'), rfl⟩


-- @@ L705-737 verbatim
theorem comp_refineCh {δ' δ : Γ} (h : δ' ≤ δ) {f : UF v → X} (hf : IsLvl v δ f) (σ : Ch v δ) :
    comp v δ' f (refineCh v h σ) = comp v δ f σ := by
  classical
  unfold comp
  have hterm : ∀ q' : Qm v δ', chv (refineCh v h σ) (rep v δ' q') • f (rep v δ' q') =
      chv σ (rep v δ (qmap v h q')) • f (rep v δ (qmap v h q')) := by
    intro q'
    have hcl : ((rep v δ' q' : UF v) : Qm v δ) = ((rep v δ (qmap v h q') : UF v) : Qm v δ) := by
      rw [mk_rep, ← qmap_mk v h, mk_rep]
    rw [chv_refineCh, chv_eq_of_mk_eq v le_rfl σ hcl, apply_eq_of_mk_eq_of_isLvl v hf hcl]
  simp_rw [hterm]
  set nF : ℕ := (Finset.univ.filter fun q' : Qm v δ' => qmap v h q' = 1).card with hF
  have hfib : ∀ q : Qm v δ, (Finset.univ.filter fun q' : Qm v δ' => qmap v h q' = q).card = nF := by
    intro q
    exact MonoidHom.card_fiber_eq_of_mem_range (qmap v h) (qmap_surjective v h q) (qmap_surjective v h 1)
  have hsum : ∀ g : Qm v δ → X, ∑ q' : Qm v δ', g (qmap v h q') = ∑ q : Qm v δ, (nF : ℂ) • g q := by
    intro g
    rw [← Finset.sum_fiberwise' Finset.univ (qmap v h) g]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_const, hfib q, Nat.cast_smul_eq_nsmul]
  have hcard : (Fintype.card (Qm v δ') : ℂ) = (Fintype.card (Qm v δ) : ℂ) * nF := by
    have h1 : Fintype.card (Qm v δ') = Fintype.card (Qm v δ) * nF := by
      rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise fun q' _ => Finset.mem_univ (qmap v h q')]
      simp only [hfib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [h1, Nat.cast_mul]
  have hF0 : (nF : ℂ) ≠ 0 := by
    have : 0 < nF := by
      rw [hF, Finset.card_pos]
      obtain ⟨q₁, hq₁⟩ := qmap_surjective v h 1
      exact ⟨q₁, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq₁⟩⟩
    exact_mod_cast this.ne'
  rw [hsum fun q => chv σ (rep v δ q) • f (rep v δ q), ← Finset.smul_sum, smul_smul, hcard, mul_inv,
    mul_assoc, inv_mul_cancel₀ hF0, mul_one]


-- @@ L739-748 verbatim
theorem comp_honest_eq {δ δ' δ'' : Γ} (h' : δ' ≤ δ) (h'' : δ'' ≤ δ)
    {f : UF v → X} (hf' : IsLvl v δ' f) (hf'' : IsLvl v δ'' f) (γ : Ch v δ) :
    comp v δ' f (refineCh v h' γ) = comp v δ'' f (refineCh v h'' γ) := by
  have e1 := comp_refineCh v (min_le_left δ' δ'') hf' (refineCh v h' γ)
  have e2 := comp_refineCh v (min_le_right δ' δ'') hf'' (refineCh v h'' γ)
  rw [← e1, ← e2]
  congr 1
  apply ext_chv
  intro u
  rw [chv_refineCh, chv_refineCh, chv_refineCh, chv_refineCh]


-- @@ L750-762 verbatim
theorem comp_translate {δ : Γ} {f : UF v → X} (hf : IsLvl v δ f)
    (ν : UF v) (γ : Ch v δ) : comp v δ (fun u => f (u * ν)) γ = (chv γ ν)⁻¹ • comp v δ f γ := by
  unfold comp
  rw [smul_comm]
  congr 1
  rw [Finset.smul_sum, ← Equiv.sum_comp (Equiv.mulRight ((ν : Qm v δ)⁻¹))]
  refine Finset.sum_congr rfl fun q _ => ?_
  simp only [Equiv.coe_mulRight]
  have h1 : ((rep v δ (q * (ν : Qm v δ)⁻¹) * ν : UF v) : Qm v δ) = ((rep v δ q : UF v) : Qm v δ) := by
    rw [QuotientGroup.mk_mul, mk_rep, mk_rep, inv_mul_cancel_right]
  have h2 : ((rep v δ (q * (ν : Qm v δ)⁻¹) : UF v) : Qm v δ) = ((rep v δ q * ν⁻¹ : UF v) : Qm v δ) := by
    rw [mk_rep, QuotientGroup.mk_mul, QuotientGroup.mk_inv, mk_rep]
  rw [apply_eq_of_mk_eq_of_isLvl v hf h1, chv_eq_of_mk_eq v le_rfl γ h2, chv_mul, chv_inv, smul_smul, mul_comm]


-- @@ L764-764 verbatim
end fourier


-- @@ L766-766 verbatim
section kirillovFunction


-- @@ L768-769 verbatim
variable (ψ : AddChar (HeightOneSpectrum.adicCompletion K v) ℂ)
  (S : Submodule ℂ (GL (Fin 2) (HeightOneSpectrum.adicCompletion K v) → ℂ))


-- @@ L771-772 verbatim
def kirillov (V : G → ℂ) (a : Fx) : (G → ℂ) ⧸ defectSpan v ψ S :=
  (defectSpan v ψ S).mkQ (rT v (dg v a) V)


-- @@ L774-775 verbatim
def theta (V : G → ℂ) : (G → ℂ) ⧸ defectSpan v ψ S :=
  (defectSpan v ψ S).mkQ (rT v (wG v) V)


-- @@ L777-779 verbatim
theorem kirillov_one (V : G → ℂ) : kirillov v ψ S V 1 = (defectSpan v ψ S).mkQ V := by
  unfold kirillov
  rw [dg_one, rT_one]


-- @@ L781-784 verbatim
theorem kirillov_rT_dg (V : G → ℂ) (b a : Fx) :
    kirillov v ψ S (rT v (dg v b) V) a = kirillov v ψ S V (a * b) := by
  unfold kirillov
  rw [rT_rT, dg_mul]


-- @@ L786-789 verbatim
theorem kirillov_add (V W : G → ℂ) (a : Fx) :
    kirillov v ψ S (V + W) a = kirillov v ψ S V a + kirillov v ψ S W a := by
  unfold kirillov
  rw [map_add, map_add]


-- @@ L791-794 verbatim
theorem kirillov_sub (V W : G → ℂ) (a : Fx) :
    kirillov v ψ S (V - W) a = kirillov v ψ S V a - kirillov v ψ S W a := by
  unfold kirillov
  rw [map_sub, map_sub]


-- @@ L796-798 verbatim
theorem kirillov_smul (c : ℂ) (V : G → ℂ) (a : Fx) : kirillov v ψ S (c • V) a = c • kirillov v ψ S V a := by
  unfold kirillov
  rw [map_smul, map_smul]


-- @@ L800-802 verbatim
theorem kirillov_zero (a : Fx) : kirillov v ψ S (0 : G → ℂ) a = 0 := by
  unfold kirillov
  rw [map_zero, map_zero]


-- @@ L804-808 verbatim
theorem kirillov_sum {ι : Type*} (s : Finset ι) (f : ι → G → ℂ) (a : Fx) :
    kirillov v ψ S (∑ i ∈ s, f i) a = ∑ i ∈ s, kirillov v ψ S (f i) a := by
  have h : kirillov v ψ S (∑ i ∈ s, f i) a = ((defectSpan v ψ S).mkQ.comp (rT v (dg v a))) (∑ i ∈ s, f i) := rfl
  rw [h, map_sum]
  rfl


-- @@ L810-810 verbatim
variable (ϖ : (HeightOneSpectrum.adicCompletion K v)ˣ)


-- @@ L812-813 verbatim
def shell (V : G → ℂ) (n : ℤ) (u : UF v) : (G → ℂ) ⧸ defectSpan v ψ S :=
  kirillov v ψ S V (ϖ ^ n * (u : Fx))


-- @@ L815-816 verbatim
def mel (δ : Γ) (V : G → ℂ) (n : ℤ) (χ : Ch v δ) : (G → ℂ) ⧸ defectSpan v ψ S :=
  comp v δ (shell v ψ S ϖ V n) χ


-- @@ L818-819 verbatim
theorem shell_add (V W : G → ℂ) (n : ℤ) (u : UF v) :
    shell v ψ S ϖ (V + W) n u = shell v ψ S ϖ V n u + shell v ψ S ϖ W n u := kirillov_add v ψ S V W _


-- @@ L821-822 verbatim
theorem shell_sub (V W : G → ℂ) (n : ℤ) (u : UF v) :
    shell v ψ S ϖ (V - W) n u = shell v ψ S ϖ V n u - shell v ψ S ϖ W n u := kirillov_sub v ψ S V W _


-- @@ L824-825 verbatim
theorem shell_smul (c : ℂ) (V : G → ℂ) (n : ℤ) (u : UF v) :
    shell v ψ S ϖ (c • V) n u = c • shell v ψ S ϖ V n u := kirillov_smul v ψ S c V _


-- @@ L827-827 verbatim
theorem shell_zero (n : ℤ) (u : UF v) : shell v ψ S ϖ (0 : G → ℂ) n u = 0 := kirillov_zero v ψ S _


-- @@ L829-830 verbatim
theorem shell_sum {ι : Type*} (s : Finset ι) (f : ι → G → ℂ) (n : ℤ) (u : UF v) :
    shell v ψ S ϖ (∑ i ∈ s, f i) n u = ∑ i ∈ s, shell v ψ S ϖ (f i) n u := kirillov_sum v ψ S s f _


-- @@ L832-834 verbatim
theorem shell_zero_one (V : G → ℂ) : shell v ψ S ϖ V 0 (1 : UF v) = (defectSpan v ψ S).mkQ V := by
  unfold shell
  rw [zpow_zero, OneMemClass.coe_one, mul_one, kirillov_one]


-- @@ L836-839 verbatim
theorem shell_rT_dg_unit (V : G → ℂ) (ν : UF v) (k : ℤ) (u : UF v) :
    shell v ψ S ϖ (rT v (dg v (ν : Fx)) V) k u = shell v ψ S ϖ V k (u * ν) := by
  unfold shell
  rw [kirillov_rT_dg, mul_assoc, Subgroup.coe_mul]


-- @@ L841-842 verbatim
def IsBump {δ : Γ} (n : ℤ) (τ : Ch v δ) (ξ : (G → ℂ) ⧸ defectSpan v ψ S) (E : G → ℂ) : Prop :=
  ∀ (k : ℤ) (u : UF v), shell v ψ S ϖ E k u = if k = n then chv τ u • ξ else 0


-- @@ L844-844 verbatim
end kirillovFunction


-- @@ L846-846 verbatim
section uniformiser


-- @@ L848-849 verbatim
variable (ϖ : (HeightOneSpectrum.adicCompletion K v)ˣ)
  (hϖ : Valued.v (ϖ : HeightOneSpectrum.adicCompletion K v) = WithZero.exp (-1 : ℤ))


-- @@ L851-853 verbatim
include hϖ in
theorem v_pi_zpow (n : ℤ) : Valued.v (((ϖ ^ n : Fx) : F)) = WithZero.exp (-n) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hϖ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one]


-- @@ L855-858 verbatim
include hϖ in
theorem v_pi_zpow_ne (n : ℤ) : Valued.v (((ϖ ^ n : Fx) : F)) ≠ 0 := by
  rw [v_pi_zpow v ϖ hϖ]
  exact WithZero.exp_ne_zero


-- @@ L860-869 verbatim
include hϖ in

theorem exists_shell_decomp (a : Fx) : ∃ (k : ℤ) (u : UF v), a = ϖ ^ k * (u : Fx) := by
  have hva : Valued.v (a : F) ≠ 0 := (Valuation.ne_zero_iff _).mpr a.ne_zero
  set k : ℤ := -WithZero.log (Valued.v (a : F)) with hk
  have hvk : Valued.v (((ϖ ^ k : Fx) : F)) = Valued.v (a : F) := by
    rw [v_pi_zpow v ϖ hϖ, hk, neg_neg, WithZero.exp_log hva]
  have hu : Valued.v ((((ϖ ^ k)⁻¹ * a : Fx) : F)) = 1 := by
    rw [Units.val_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hvk, inv_mul_cancel₀ hva]
  exact ⟨k, ⟨(ϖ ^ k)⁻¹ * a, hu⟩, (mul_inv_cancel_left (ϖ ^ k) a).symm⟩


-- @@ L871-893 verbatim
include hϖ in

theorem eq_of_v_sub_lt {k n : ℤ} (u r : UF v) {δ : Γ} (hδ : δ ≤ 1)
    (h : Valued.v (((ϖ ^ k * (u : Fx) : Fx) : F) - ((ϖ ^ n * (r : Fx) : Fx) : F)) <
      (δ : WithZero (Multiplicative ℤ)) * Valued.v (((ϖ ^ n : Fx) : F))) : k = n := by
  have hδ' : (δ : WithZero (Multiplicative ℤ)) ≤ 1 := Units.val_le_val.mpr hδ
  have hvn : Valued.v (((ϖ ^ n * (r : Fx) : Fx) : F)) = Valued.v (((ϖ ^ n : Fx) : F)) := by
    rw [Units.val_mul, map_mul, v_coe_UF, mul_one]
  have hvk : Valued.v (((ϖ ^ k * (u : Fx) : Fx) : F)) = Valued.v (((ϖ ^ k : Fx) : F)) := by
    rw [Units.val_mul, map_mul, v_coe_UF, mul_one]
  have hlt : Valued.v (((ϖ ^ k * (u : Fx) : Fx) : F) - ((ϖ ^ n * (r : Fx) : Fx) : F)) <
      Valued.v (((ϖ ^ n * (r : Fx) : Fx) : F)) := by
    rw [hvn]
    refine h.trans_le ?_
    calc (δ : WithZero (Multiplicative ℤ)) * Valued.v (((ϖ ^ n : Fx) : F))
        ≤ 1 * Valued.v (((ϖ ^ n : Fx) : F)) := mul_le_mul_left hδ' _
      _ = _ := one_mul _
  have heq : Valued.v (((ϖ ^ k * (u : Fx) : Fx) : F)) = Valued.v (((ϖ ^ n * (r : Fx) : Fx) : F)) := by
    have e : ((ϖ ^ k * (u : Fx) : Fx) : F) =
        (((ϖ ^ k * (u : Fx) : Fx) : F) - ((ϖ ^ n * (r : Fx) : Fx) : F)) + ((ϖ ^ n * (r : Fx) : Fx) : F) := by ring
    rw [e, Valuation.map_add_eq_of_lt_right _ hlt]
  rw [hvk, hvn, v_pi_zpow v ϖ hϖ, v_pi_zpow v ϖ hϖ] at heq
  exact neg_injective (WithZero.exp_injective heq)


-- @@ L895-907 verbatim
theorem v_sub_lt_iff_mk_eq (δ : Γ) (u r : UF v) :
    Valued.v (((u : Fx) : F) - ((r : Fx) : F)) < (δ : WithZero (Multiplicative ℤ)) ↔ (u : Qm v δ) = (r : Qm v δ) := by
  constructor
  · intro h
    exact mk_eq_mk_of_close v δ r u h
  · intro h
    rw [eq_comm, QuotientGroup.eq, mem_Um_iff] at h
    have e : ((u : Fx) : F) - ((r : Fx) : F) = ((r : Fx) : F) * ((((r⁻¹ * u : UF v) : Fx) : F) - 1) := by
      have h1 : ((r : Fx) : F) * (((r⁻¹ : UF v) : Fx) : F) = 1 := by
        rw [← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel, Subgroup.coe_one, Units.val_one]
      rw [Subgroup.coe_mul, Units.val_mul, mul_sub, mul_one, ← mul_assoc, h1, one_mul]
    rw [e, map_mul, v_coe_UF, one_mul]
    exact h


-- @@ L909-909 verbatim
def lvl (K₀ : ℤ) : Γ := Units.mk0 (WithZero.exp K₀) WithZero.exp_ne_zero


-- @@ L911-911 verbatim
theorem lvl_val (K₀ : ℤ) : ((lvl K₀ : Γ) : WithZero (Multiplicative ℤ)) = WithZero.exp K₀ := rfl


-- @@ L913-915 verbatim
def negUF : UF v := ⟨-1, by
  show Valued.v (((-1 : Fx) : F)) = 1
  rw [Units.val_neg, Units.val_one, Valuation.map_neg, Valuation.map_one]⟩


-- @@ L917-919 verbatim
theorem coe_negUF : (((negUF v : UF v) : Fx) : F) = -1 := by
  show (((-1 : Fx)) : F) = -1
  rw [Units.val_neg, Units.val_one]


-- @@ L921-928 verbatim
theorem wG_identity :
    wG v * (unipotentGL2 (1 : F) * wG v) =
      unipotentGL2 (1 : F) * (dg v ((negUF v : UF v) : Fx) * (wG v * unipotentGL2 (1 : F))) := by
  apply Units.ext
  simp only [Units.val_mul, wG_coe, dg_coe, unipotentGL2_coe]
  rw [coe_negUF]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]


-- @@ L930-930 verbatim
end uniformiser


-- @@ L932-932 verbatim
end LocalGL2.Kirillov


-- @@ L934-934 verbatim
end
