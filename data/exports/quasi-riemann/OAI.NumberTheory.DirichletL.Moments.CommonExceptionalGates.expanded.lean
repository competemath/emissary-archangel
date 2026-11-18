import OAI.NumberTheory.DirichletL.Moments.CommonLinearSource
import OAI.NumberTheory.DirichletL.Moments.FixedRowMask


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentCommonExceptionalGates

-- @@ L10-10 verbatim
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge

-- @@ L11-11 verbatim
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentSourceMass

-- @@ L12-12 verbatim
open CenteredMomentAddedZeroUniform CenteredMomentExceptionalAmplitudePair

-- @@ L13-13 verbatim
open CenteredMomentFixedRowMask CenteredExceptionalProfile CenteredMomentSecondHeightFamily

-- @@ L14-14 verbatim
local notation "O" => HeckeFamily.O

-- @@ L15-15 verbatim
variable {ι:Type*} [Fintype ι] [DecidableEq ι]


-- @@ L17-21 verbatim
omit [DecidableEq ι] in
theorem coordinate_dvd (s:Input ι)(C:Ideal O)(B:actualAllocations s.pools C)(j:ι⊕Fin 2):
    B.val j∣C:=by
  exact (Finset.dvd_prod_of_mem B.val (Finset.mem_univ j)).trans
    (dvd_of_eq (Finset.mem_filter.mp B.property).2)


-- @@ L23-28 verbatim
omit [DecidableEq ι] in
theorem coordinate_norm_le (s:Input ι)(C:Ideal O)(hC:C≠0)
    (B:actualAllocations s.pools C)(j:ι⊕Fin 2):
    (Ideal.absNorm (B.val j):ℝ)≤Ideal.absNorm C:=by
  exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC))
    (map_dvd Ideal.absNorm (coordinate_dvd s C B j))


-- @@ L30-39 verbatim
omit [DecidableEq ι] in
theorem extracted_lower (s:Input ι)(C:Ideal O)(hC:C≠0)(B:actualAllocations s.pools C)
    (j:ι⊕Fin 2)(Z r X:ℝ)(hZ:1<Z)(hX:Z^r≤X):
    Z^(r-Real.logb Z (Ideal.absNorm C:ℝ))≤X/Ideal.absNorm (B.val j):=by
  have hz:=zero_lt_one.trans hZ
  have hN:(0:ℝ)<Ideal.absNorm C:=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hC)
  rw [Real.rpow_sub hz,Real.rpow_logb hz hZ.ne' hN]
  exact div_le_div₀ ((Real.rpow_nonneg hz.le r).trans hX) hX (alloc_norm_pos s C B j)
    (coordinate_norm_le s C hC B j)


-- @@ L41-48 verbatim
omit [DecidableEq ι] in
theorem common_mask_inducing (s:Input ι)(C R Q:Ideal O)(hC:C≠0)(hR:R≠0)
    (B:actualAllocations s.pools C)(z:O)(hz:z≠0):
    FixedInducingRow (commonData s C R B).η Q (commonData s C R B).m
      (commonData s C R B).A z ↔ FixedInducingRow s.η Q fixedBadMask 1 z:=by
  exact fixedInducingRow_mul_mask_iff s.η Q fixedBadMask (idealGenerator (R*C)) 1 z
    fixedBadMask_ne_zero (idealGenerator_ne_zero _ (mul_ne_zero hR hC)) one_ne_zero hz
    (dvd_mul_right _ _) (dvd_mul_left _ _)


-- @@ L50-58 verbatim
omit [DecidableEq ι] in
theorem common_conductor (s:Input ι)(C R:Ideal O)(B:actualAllocations s.pools C)(z:O):
    HeckeRowClosure.rowConductorBound (commonData s C R B).η (commonData s C R B).m 1
      ((commonData s C R B).A*z)=
      s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
        (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:=by
  simp only [commonData,HeckeRowClosure.rowConductorBound,one_mul,
    ←Ideal.span_singleton_mul_span_singleton,span_idealGenerator,map_mul,Ideal.span_singleton_one,Ideal.absNorm_top,one_pow]
  ring


-- @@ L60-80 verbatim
omit [DecidableEq ι] in
theorem common_admissible (s:Input ι)(p:Tests)(C R Q:Ideal O)(hC:C≠0)(hR:R≠0)
    (B:actualAllocations s.pools C)(Z width r:ℝ)(hZ:1<Z)(z:O)(hz:z≠0)
    (hP:∀i,1≤s.P i)(hex:FixedInducingRow s.η Q fixedBadMask 1 z)
    (hcond:(s.η.modulus.absNorm*(Ideal.span {(fixedBadMask:O)}).absNorm*
      (Ideal.span {(72:O)}).absNorm*(R.absNorm*C.absNorm)*(Ideal.span {z}).absNorm:ℝ)≤Z^width)
    (hW₁:s.W₁=p.profile 0)(hW₂:s.W₂=p.profile 1)
    (hX₁:Z^r≤s.X₁)(hX₂:Z^r≤s.X₂)(hY₁:Z^r≤s.Y₁)(hY₂:Z^r≤s.Y₂):
    Admissible (commonData s C R B) p Q Z width
      (r-Real.logb Z (Ideal.absNorm C:ℝ)) z:=by
  refine ⟨fun i=>hP i.val,?_,one_ne_zero,hz,?_,?_,?_,?_,hW₁,hW₂,?_,?_,?_,?_⟩
  · exact mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ (mul_ne_zero hR hC))
  · exact (dvd_mul_right _ _).trans (dvd_mul_right _ _)
  · exact (dvd_mul_left _ _).trans (dvd_mul_right _ _)
  · rw [common_conductor]
    simpa only [Nat.cast_mul] using hcond
  · exact (common_mask_inducing s C R Q hC hR B z hz).mpr hex
  · exact extracted_lower s C hC B (Sum.inr 0) Z r s.X₁ hZ hX₁
  · exact extracted_lower s C hC B (Sum.inr 1) Z r s.X₂ hZ hX₂
  · exact extracted_lower s C hC B (Sum.inr 0) Z r s.Y₁ hZ hY₁
  · exact extracted_lower s C hC B (Sum.inr 1) Z r s.Y₂ hZ hY₂


-- @@ L82-82 verbatim
end SevenEighths.CenteredMomentCommonExceptionalGates


-- @@ L84-84 verbatim
end


-- @@ L86-86 verbatim
end OAI
