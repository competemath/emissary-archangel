import Mathlib.RingTheory.LaurentSeries
import Mathlib.RingTheory.PowerSeries.PiTopology
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Squarefree


-- @@ L9-9 verbatim
set_option autoImplicit false


-- @@ L11-11 verbatim
noncomputable section


-- @@ L13-13 verbatim
open scoped PowerSeries.WithPiTopology


-- @@ L15-15 verbatim
open PowerSeries HahnSeries IntermediateField


-- @@ L17-17 verbatim
namespace ModularCurve


-- @@ L19-19 verbatim
section QExpand


-- @@ L21-21 verbatim
variable {R : Type*} [CommRing R]


-- @@ L23-29 verbatim
variable (R) in

def qExpand (N : ℕ) [NeZero N] : LaurentSeries R →+* LaurentSeries R :=
  HahnSeries.embDomainRingHom (AddMonoidHom.mulLeft (N : ℤ))
    (mul_right_injective₀ (by exact_mod_cast NeZero.ne N))
    (fun g g' => mul_le_mul_iff_of_pos_left
      (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)))


-- @@ L31-31 verbatim
variable (N : ℕ) [NeZero N]


-- @@ L33-36 verbatim
@[simp]
theorem qExpand_coeff_mul (f : LaurentSeries R) (k : ℤ) :
    (qExpand R N f).coeff ((N : ℤ) * k) = f.coeff k :=
  HahnSeries.embDomain_coeff


-- @@ L38-42 verbatim
theorem qExpand_coeff_of_not_dvd (f : LaurentSeries R) {k : ℤ} (hk : ¬ (N : ℤ) ∣ k) :
    (qExpand R N f).coeff k = 0 := by
  refine HahnSeries.embDomain_notin_range ?_
  rintro ⟨m, rfl⟩
  exact hk ⟨m, rfl⟩


-- @@ L44-47 verbatim
@[simp]
theorem qExpand_single (k : ℤ) (r : R) :
    qExpand R N (HahnSeries.single k r) = HahnSeries.single ((N : ℤ) * k) r :=
  HahnSeries.embDomain_single


-- @@ L49-51 verbatim
@[simp]
theorem qExpand_C (r : R) : qExpand R N (HahnSeries.C r) = HahnSeries.C r :=
  HahnSeries.embDomainRingHom_C


-- @@ L53-54 verbatim
theorem qExpand_injective : Function.Injective (qExpand R N) :=
  HahnSeries.embDomain_injective


-- @@ L56-60 verbatim
theorem qExpand_one_apply (f : LaurentSeries R) : qExpand R 1 f = f := by
  ext k
  have h : ((1 : ℕ) : ℤ) * k = k := by simp
  conv_lhs => rw [← h]
  rw [qExpand_coeff_mul]


-- @@ L62-64 verbatim
theorem qExpand_congr {M K : ℕ} [NeZero M] [NeZero K] (h : M = K) (f : LaurentSeries R) :
    qExpand R M f = qExpand R K f := by
  subst h; rfl


-- @@ L66-83 verbatim
theorem qExpand_qExpand (M : ℕ) [NeZero M] (f : LaurentSeries R) :
    qExpand R M (qExpand R N f) = qExpand R (M * N) f := by
  ext k
  by_cases hk : ((M : ℤ) * N) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    trans f.coeff m
    · rw [show (M : ℤ) * N * m = (M : ℤ) * ((N : ℤ) * m) by ring, qExpand_coeff_mul,
        qExpand_coeff_mul]
    · rw [show (M : ℤ) * N * m = (((M * N : ℕ) : ℤ)) * m by push_cast; ring,
        qExpand_coeff_mul]
  · rw [qExpand_coeff_of_not_dvd (M * N) f (by push_cast; exact hk)]
    by_cases hkM : (M : ℤ) ∣ k
    · obtain ⟨m, rfl⟩ := hkM
      rw [qExpand_coeff_mul M _ m]
      refine qExpand_coeff_of_not_dvd N _ ?_
      rintro ⟨c, hc⟩
      exact hk ⟨c, by rw [hc]; ring⟩
    · exact qExpand_coeff_of_not_dvd M _ hkM


-- @@ L85-85 verbatim
end QExpand


-- @@ L87-87 verbatim
section RatAlgebra


-- @@ L89-89 verbatim
variable (N : ℕ) [NeZero N]


-- @@ L91-96 verbatim
theorem algebraMap_apply_eq_single (c : ℚ) :
    algebraMap ℚ (LaurentSeries ℚ) c = HahnSeries.single 0 c := by
  have h1 : algebraMap ℚ (PowerSeries ℚ) c = PowerSeries.C c := by
    simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl


-- @@ L98-102 verbatim
def qExpandₐ : LaurentSeries ℚ →ₐ[ℚ] LaurentSeries ℚ where
  __ := qExpand ℚ N
  commutes' r := by
    show qExpand ℚ N (algebraMap ℚ (LaurentSeries ℚ) r) = algebraMap ℚ (LaurentSeries ℚ) r
    rw [algebraMap_apply_eq_single, qExpand_single, mul_zero]


-- @@ L104-105 verbatim
@[simp]
theorem qExpandₐ_apply (f : LaurentSeries ℚ) : qExpandₐ N f = qExpand ℚ N f := rfl


-- @@ L107-107 verbatim
end RatAlgebra


-- @@ L109-109 verbatim
section JFunction


-- @@ L111-112 verbatim
def eisenstein4 : PowerSeries ℤ :=
  PowerSeries.mk fun n => if n = 0 then 1 else 240 * ∑ d ∈ n.divisors, (d : ℤ) ^ 3


-- @@ L114-117 verbatim
@[simp]
theorem constantCoeff_eisenstein4 : PowerSeries.constantCoeff eisenstein4 = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [eisenstein4]


-- @@ L119-120 verbatim
def etaProd : PowerSeries ℤ :=
  ∏' n : ℕ, (1 - PowerSeries.X ^ (n + 1))


-- @@ L122-125 verbatim
theorem constantCoeff_etaProd : PowerSeries.constantCoeff etaProd = 1 := by
  rw [etaProd]
  simp [(PowerSeries.WithPiTopology.multipliable_one_sub_X_pow ℤ).map_tprod _
    (PowerSeries.WithPiTopology.continuous_constantCoeff ℤ)]


-- @@ L127-127 verbatim
def dedekindEtaUnit : PowerSeries ℤ := etaProd ^ 24


-- @@ L129-130 verbatim
theorem constantCoeff_dedekindEtaUnit : PowerSeries.constantCoeff dedekindEtaUnit = 1 := by
  rw [dedekindEtaUnit, map_pow, constantCoeff_etaProd, one_pow]


-- @@ L132-132 verbatim
def dedekindEtaUnitInv : PowerSeries ℤ := dedekindEtaUnit.invOfUnit 1


-- @@ L134-135 verbatim
theorem dedekindEtaUnit_mul_inv : dedekindEtaUnit * dedekindEtaUnitInv = 1 :=
  PowerSeries.mul_invOfUnit _ _ (by rw [constantCoeff_dedekindEtaUnit]; rfl)


-- @@ L137-140 verbatim
theorem constantCoeff_dedekindEtaUnitInv :
    PowerSeries.constantCoeff dedekindEtaUnitInv = 1 := by
  have h := congrArg (PowerSeries.constantCoeff (R := ℤ)) dedekindEtaUnit_mul_inv
  rwa [map_mul, constantCoeff_dedekindEtaUnit, one_mul, map_one] at h


-- @@ L142-142 verbatim
def jNum : PowerSeries ℤ := eisenstein4 ^ 3 * dedekindEtaUnitInv


-- @@ L144-147 verbatim
@[simp]
theorem constantCoeff_jNum : PowerSeries.constantCoeff jNum = 1 := by
  rw [jNum, map_mul, map_pow, constantCoeff_eisenstein4, constantCoeff_dedekindEtaUnitInv,
    one_pow, one_mul]


-- @@ L149-149 verbatim
def jNumQ : PowerSeries ℚ := jNum.map (Int.castRingHom ℚ)


-- @@ L151-155 verbatim
@[simp]
theorem constantCoeff_jNumQ : PowerSeries.constantCoeff jNumQ = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, jNumQ, PowerSeries.coeff_map,
    PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_jNum]
  simp


-- @@ L157-158 verbatim
def jq : LaurentSeries ℚ :=
  HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℚ jNumQ


-- @@ L160-165 verbatim
theorem ofPowerSeries_coeff_of_neg {R : Type*} [Semiring R] (f : PowerSeries R) {k : ℤ}
    (hk : k < 0) : (HahnSeries.ofPowerSeries ℤ R f).coeff k = 0 := by
  rw [HahnSeries.ofPowerSeries_apply]
  refine HahnSeries.embDomain_notin_range ?_
  rintro ⟨m, rfl⟩
  exact absurd hk (not_lt.mpr (Int.natCast_nonneg m))


-- @@ L167-170 verbatim
theorem jq_pow (n : ℕ) :
    jq ^ n = HahnSeries.single (-(n : ℤ)) 1 * HahnSeries.ofPowerSeries ℤ ℚ (jNumQ ^ n) := by
  have h : n • (-1 : ℤ) = -(n : ℤ) := by simp
  rw [jq, mul_pow, HahnSeries.single_pow, one_pow, h, ← map_pow]


-- @@ L172-175 verbatim
theorem coeff_jq_pow_self (n : ℕ) : (jq ^ n).coeff (-(n : ℤ)) = 1 := by
  rw [jq_pow, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constantCoeff_jNumQ, one_pow]


-- @@ L177-179 verbatim
theorem coeff_jq_pow_of_lt {n : ℕ} {m : ℤ} (hm : m < -(n : ℤ)) : (jq ^ n).coeff m = 0 := by
  rw [jq_pow, HahnSeries.coeff_single_mul, one_mul]
  exact ofPowerSeries_coeff_of_neg _ (by omega)


-- @@ L181-184 verbatim
@[simp]
theorem coeff_jq_neg_one : jq.coeff (-1 : ℤ) = 1 := by
  have h := coeff_jq_pow_self 1
  simpa using h


-- @@ L186-188 verbatim
theorem coeff_jq_of_lt {k : ℤ} (hk : k < -1) : jq.coeff k = 0 := by
  have h := coeff_jq_pow_of_lt (n := 1) (m := k) (by simpa using hk)
  simpa using h


-- @@ L190-190 verbatim
theorem jq_ne_zero : jq ≠ 0 := fun h => by simpa [h] using coeff_jq_neg_one


-- @@ L192-192 verbatim
end JFunction


-- @@ L194-194 verbatim
def jqN (N : ℕ) [NeZero N] : LaurentSeries ℚ := qExpand ℚ N jq


-- @@ L196-197 verbatim
@[simp]
theorem jqN_one : jqN 1 = jq := qExpand_one_apply jq


-- @@ L199-199 verbatim
section NamedInputs


-- @@ L201-201 verbatim
def dedekindPsi (N : ℕ) : ℕ := ∑ d ∈ N.divisors with Squarefree d, N / d


-- @@ L203-206 verbatim
@[simp]
theorem dedekindPsi_one : dedekindPsi 1 = 1 := by
  rw [dedekindPsi, Nat.divisors_one, Finset.filter_singleton, if_pos squarefree_one]
  simp


-- @@ L208-209 verbatim
def evalAtJ : Polynomial ℤ →+* LaurentSeries ℚ :=
  (Polynomial.aeval (R := ℤ) jq).toRingHom


-- @@ L211-213 verbatim
@[simp]
theorem evalAtJ_X : evalAtJ Polynomial.X = jq := by
  simp [evalAtJ]


-- @@ L215-223 verbatim
structure ModularPolynomialData (N : ℕ) [NeZero N] : Type where

  Φ : Polynomial (Polynomial ℤ)

  monic : Φ.Monic

  natDegree_eq : Φ.natDegree = dedekindPsi N

  eval_eq_zero : Φ.eval₂ evalAtJ (jqN N) = 0


-- @@ L225-231 verbatim
def modularPolynomialDataOne : ModularPolynomialData 1 where
  Φ := Polynomial.X - Polynomial.C Polynomial.X
  monic := Polynomial.monic_X_sub_C _
  natDegree_eq := by simp
  eval_eq_zero := by
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C, jqN_one,
      evalAtJ_X, sub_self]


-- @@ L233-235 verbatim
def FunctionFieldGeneration (M : ℕ) [NeZero M] : Prop :=
  ∀ d : ℕ, d ∣ M → ∀ (_ : NeZero d), qExpand ℚ d jq ∈
    IntermediateField.adjoin ℚ {jq, qExpand ℚ M jq}


-- @@ L237-242 verbatim
theorem functionFieldGeneration_one : FunctionFieldGeneration 1 := by
  intro d hd hne
  haveI := hne
  rw [Nat.dvd_one] at hd
  subst hd
  exact subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)


-- @@ L244-244 verbatim
end NamedInputs


-- @@ L246-246 verbatim
section FunctionField


-- @@ L248-248 verbatim
variable (N : ℕ) [NeZero N]


-- @@ L250-251 verbatim
def modularFunctionField : IntermediateField ℚ (LaurentSeries ℚ) :=
  IntermediateField.adjoin ℚ {jq, qExpand ℚ N jq}


-- @@ L253-254 verbatim
theorem jq_mem : jq ∈ modularFunctionField N :=
  IntermediateField.subset_adjoin ℚ _ (Set.mem_insert _ _)


-- @@ L256-257 verbatim
theorem jqN_mem : qExpand ℚ N jq ∈ modularFunctionField N :=
  IntermediateField.subset_adjoin ℚ _ (Set.mem_insert_of_mem _ rfl)


-- @@ L259-260 verbatim
theorem modularFunctionField_one : modularFunctionField 1 = ℚ⟮jq⟯ := by
  rw [modularFunctionField, qExpand_one_apply, Set.pair_eq_singleton]


-- @@ L262-264 verbatim
theorem adjoin_jq_le : ℚ⟮jq⟯ ≤ modularFunctionField N := by
  rw [IntermediateField.adjoin_le_iff]
  exact Set.singleton_subset_iff.mpr (jq_mem N)


-- @@ L266-266 verbatim
end FunctionField


-- @@ L268-268 verbatim
def jGen : ℚ⟮jq⟯ := ⟨jq, IntermediateField.mem_adjoin_simple_self ℚ jq⟩


-- @@ L270-271 verbatim
def evalAtJGen : Polynomial ℤ →+* ℚ⟮jq⟯ :=
  Polynomial.eval₂RingHom (Int.castRingHom ℚ⟮jq⟯) jGen


-- @@ L273-281 verbatim
theorem algebraMap_comp_evalAtJGen :
    (algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)).comp evalAtJGen = evalAtJ := by
  refine Polynomial.ringHom_ext' (Subsingleton.elim _ _) ?_
  show algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ) (evalAtJGen Polynomial.X) = evalAtJ Polynomial.X
  rw [evalAtJ_X]
  show algebraMap ℚ⟮jq⟯ (LaurentSeries ℚ)
    (Polynomial.eval₂ (Int.castRingHom ℚ⟮jq⟯) jGen Polynomial.X) = jq
  rw [Polynomial.eval₂_X]
  rfl


-- @@ L283-283 verbatim
namespace ModularPolynomialData


-- @@ L285-285 verbatim
variable {N : ℕ} [NeZero N] (data : ModularPolynomialData N)


-- @@ L287-287 verbatim
def toAdjoin : Polynomial ℚ⟮jq⟯ := data.Φ.map evalAtJGen


-- @@ L289-289 verbatim
theorem toAdjoin_monic : data.toAdjoin.Monic := data.monic.map _


-- @@ L291-291 verbatim
end ModularPolynomialData


-- @@ L293-293 verbatim
section AllDivisors


-- @@ L295-295 verbatim
variable (N : ℕ) [NeZero N]


-- @@ L297-298 verbatim
def divisorExpansions : Set (LaurentSeries ℚ) :=
  {x | ∃ (d : ℕ) (_ : NeZero d), d ∣ N ∧ x = qExpand ℚ d jq}


-- @@ L300-303 verbatim
omit [NeZero N] in
theorem mem_divisorExpansions {d : ℕ} [NeZero d] (hd : d ∣ N) :
    qExpand ℚ d jq ∈ divisorExpansions N :=
  ⟨d, ‹_›, hd, rfl⟩


-- @@ L305-306 verbatim
def modularFunctionFieldFull : IntermediateField ℚ (LaurentSeries ℚ) :=
  IntermediateField.adjoin ℚ (divisorExpansions N)


-- @@ L308-311 verbatim
omit [NeZero N] in
theorem jqd_mem_full {d : ℕ} [NeZero d] (hd : d ∣ N) :
    qExpand ℚ d jq ∈ modularFunctionFieldFull N :=
  subset_adjoin ℚ _ (mem_divisorExpansions N hd)


-- @@ L313-319 verbatim
theorem modularFunctionField_le_full :
    modularFunctionField N ≤ modularFunctionFieldFull N := by
  rw [modularFunctionField, adjoin_le_iff]
  rintro x (rfl | rfl)
  · have h := jqd_mem_full N (one_dvd N)
    rwa [qExpand_one_apply] at h
  · exact jqd_mem_full N dvd_rfl


-- @@ L321-326 verbatim
theorem full_degeneracy_le {N M : ℕ} [NeZero N] [NeZero M] (h : N ∣ M) :
    modularFunctionFieldFull N ≤ modularFunctionFieldFull M := by
  rw [modularFunctionFieldFull, adjoin_le_iff]
  rintro x ⟨d, hne, hdvd, rfl⟩
  haveI := hne
  exact jqd_mem_full M (hdvd.trans h)


-- @@ L328-338 verbatim
omit [NeZero N] in

theorem full_degeneracy_map_le (ℓ : ℕ) [NeZero ℓ] :
    (modularFunctionFieldFull N).map (qExpandₐ ℓ) ≤ modularFunctionFieldFull (N * ℓ) := by
  rw [modularFunctionFieldFull, adjoin_map, adjoin_le_iff]
  rintro x ⟨y, ⟨d, hne, hdvd, rfl⟩, rfl⟩
  haveI := hne
  haveI : NeZero (ℓ * d) := ⟨Nat.mul_ne_zero (NeZero.ne ℓ) (NeZero.ne d)⟩
  show qExpandₐ ℓ (qExpand ℚ d jq) ∈ _
  rw [qExpandₐ_apply, qExpand_qExpand]
  exact jqd_mem_full (N * ℓ) ((mul_dvd_mul_left ℓ hdvd).trans (dvd_of_eq (mul_comm ℓ N)))


-- @@ L340-344 verbatim
theorem qExpandₐ_comp (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] :
    (qExpandₐ ℓ).comp (qExpandₐ ℓ') = qExpandₐ (ℓ * ℓ') := by
  refine AlgHom.ext fun f => ?_
  simp only [AlgHom.comp_apply, qExpandₐ_apply]
  exact qExpand_qExpand ℓ' ℓ f


-- @@ L346-346 verbatim
end AllDivisors


-- @@ L348-348 verbatim
end ModularCurve
