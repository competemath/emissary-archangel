/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Pi1.MappingTorusHomology
import all LeanPool.HopfProblem.HomologyTheory.SingularMayerVietoris
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology1
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology3
import all LeanPool.HopfProblem.Foundations.Core2
import all LeanPool.HopfProblem.PeriodFamily.PeriodPoint
import all LeanPool.HopfProblem.Elliptic.Core1
import all LeanPool.HopfProblem.Pi1.MappingTorus
import all LeanPool.HopfProblem.Elliptic.Core2
import all LeanPool.HopfProblem.TorusHomology.PeriodTorusHigherHomology6
import all LeanPool.HopfProblem.Pi1.FundamentalGroupVanKampen2
import all LeanPool.HopfProblem.Elliptic.Core5
import all LeanPool.HopfProblem.Pi1.MappingTorusHomology


-- @@ L24-28 verbatim
/-!
# Hopf problem: elliptic · core 7

Supporting definitions and proofs for this stage of the six-sphere construction.
-/



-- @@ L31-31 verbatim
open Set Function Filter Manifold Topology


-- @@ L33-36 verbatim
open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane


-- @@ L38-38 verbatim
universe u v


-- @@ L40-40 verbatim
noncomputable section


-- @@ L42-42 verbatim
namespace Mathoverflow1973


-- @@ L44-44 verbatim
local infixr:80 " ≫ₚ " => Path.trans


-- @@ L46-46 verbatim
local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f


-- @@ L48-50 verbatim
private def Elliptic.HigherHomology.CoverAlgebra.secondMap {M : Type*} [AddCommGroup M] [Module ℤ M]
    (L : M →ₗ[ℤ] (Fin 2 → ℤ)) : M →ₗ[ℤ] ℤ :=
  (LinearMap.proj 1).comp L


-- @@ L52-58 verbatim
private def Elliptic.HigherHomology.fibreIntoPeriodTorus (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) : C(PeriodTorusHigherHomology.ProductTorus 3, p.val.Torus)
    where
  toFun x := (splitPeriodTorusHomeomorph j p.val).symm (0, x)
  continuous_toFun :=
    (splitPeriodTorusHomeomorph j p.val).symm.continuous.comp
      (continuous_const.prodMk continuous_id)


-- @@ L60-64 verbatim
private def
    Elliptic.HigherHomology.fibreIntoSurface (j : Elliptic.Kind) (p : Elliptic.FixedPeriod j) :
    C(PeriodTorusHigherHomology.ProductTorus 3,
      Elliptic.Surface j p j.twist (Elliptic.mainTwist_admissible j)) :=
  (periodCover j p j.twist (Elliptic.mainTwist_admissible j)).comp (fibreIntoPeriodTorus j p)


-- @@ L66-80 verbatim
private theorem Elliptic.HigherHomology.surfaceMappingTorusHomeomorph_comp_fibreIntoSurface
    (j : Elliptic.Kind) (p : Elliptic.FixedPeriod j) :
    (surfaceMappingTorusHomeomorph j p :
            C(Elliptic.Surface j p j.twist (Elliptic.mainTwist_admissible j),
              mappingTorusModel j)).comp
        (fibreIntoSurface j p) =
      MappingTorus.HomologyCover.fibreInclusion (fibreTorusHomeomorph j).symm := by
  ext x
  change
    surfaceMappingTorusHomeomorph j p
        (Elliptic.surfaceProjection j p j.twist (Elliptic.mainTwist_admissible j)
          ((splitPeriodTorusHomeomorph j p.val).symm (0, x))) =
      MappingTorus.mk (fibreTorusHomeomorph j).symm (0, x)
  simpa only [AddCircle.coe_zero, MulZeroClass.zero_mul] using
    surfaceMappingTorusHomeomorph_splitPeriodTorus j p (0 : ℝ) x


-- @@ L82-90 verbatim
private theorem Elliptic.HigherHomology.surfaceMappingTorusHomology_fibre_map (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ) :
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p)
            n).toLinearMap.comp
        (SingularMayerVietoris.singularHomologyMap (fibreIntoSurface j p) n) =
      MappingTorusHomology.fibreHomologyMap (fibreTorusHomeomorph j).symm n := by
  rw [PeriodTorusHigherHomology.homeomorphHomologyEquiv_toLinearMap, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp,
    surfaceMappingTorusHomeomorph_comp_fibreIntoSurface]


-- @@ L92-98 verbatim
private theorem Elliptic.HigherHomology.surfaceMappingTorusHomology_fibre (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) n) :
    PeriodTorusHigherHomology.homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p) n
        (SingularMayerVietoris.singularHomologyMap (fibreIntoSurface j p) n a) =
      MappingTorusHomology.fibreHomologyMap (fibreTorusHomeomorph j).symm n a :=
  DFunLike.congr_fun (surfaceMappingTorusHomology_fibre_map j p n) a


-- @@ L100-108 verbatim
private def Elliptic.HigherHomology.mappingTorusProductCover (j : Elliptic.Kind) :
    C(MappingTorus.Circle × PeriodTorusHigherHomology.ProductTorus 3, mappingTorusModel j) :=
  (MappingTorusQuotient.mappingTorusHomeomorph j.order (fibreTorusHomeomorph j)
          (fibreTorusHomeomorph_pow_order j) :
        C(surfaceProductQuotient j, mappingTorusModel j)).comp
    ⟨MappingTorusQuotient.project j.order (fibreTorusHomeomorph j)
        (fibreTorusHomeomorph_pow_order j),
      MappingTorusQuotient.project_continuous j.order (fibreTorusHomeomorph j)
        (fibreTorusHomeomorph_pow_order j)⟩


-- @@ L110-120 verbatim
private theorem
    Elliptic.HigherHomology.surfaceMappingTorusHomeomorph_comp_periodCover (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    (surfaceMappingTorusHomeomorph j p :
            C(Elliptic.Surface j p j.twist (Elliptic.mainTwist_admissible j),
              mappingTorusModel j)).comp
        (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) =
      (mappingTorusProductCover j).comp
        (splitPeriodTorusHomeomorph j p.val :
          C(p.val.Torus, MappingTorus.Circle × PeriodTorusHigherHomology.ProductTorus 3)) :=
  rfl


-- @@ L122-136 verbatim
private theorem
    Elliptic.HigherHomology.surfaceMappingTorusHomology_periodCover_map (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ) :
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p)
            n).toLinearMap.comp
        (SingularMayerVietoris.singularHomologyMap
          (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) n) =
      (SingularMayerVietoris.singularHomologyMap (mappingTorusProductCover j) n).comp
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val)
            n).toLinearMap := by
  rw [PeriodTorusHigherHomology.homeomorphHomologyEquiv_toLinearMap, ←
    PeriodTorusHigherHomology.singularHomologyMap_comp,
    surfaceMappingTorusHomeomorph_comp_periodCover,
    PeriodTorusHigherHomology.singularHomologyMap_comp,
    PeriodTorusHigherHomology.homeomorphHomologyEquiv_toLinearMap]


-- @@ L138-147 verbatim
private theorem Elliptic.HigherHomology.surfaceMappingTorusHomology_periodCover (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology p.val.Torus n) :
    PeriodTorusHigherHomology.homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p) n
        (SingularMayerVietoris.singularHomologyMap
          (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) n a) =
      SingularMayerVietoris.singularHomologyMap (mappingTorusProductCover j) n
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val) n
          a) :=
  DFunLike.congr_fun (surfaceMappingTorusHomology_periodCover_map j p n) a


-- @@ L149-159 verbatim
private theorem Elliptic.HigherHomology.surfaceH2Equiv_fibre (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2) :
    surfaceH2Equiv j p (SingularMayerVietoris.singularHomologyMap (fibreIntoSurface j p) 2 a) =
      ![torusH2Coordinates a 0, 0] := by
  change
    mappingTorusH2Equiv j
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p) 2
          (SingularMayerVietoris.singularHomologyMap (fibreIntoSurface j p) 2 a)) =
      _
  rw [surfaceMappingTorusHomology_fibre, mappingTorusH2Equiv_fibre]


-- @@ L161-171 verbatim
private theorem Elliptic.HigherHomology.surfaceH3Equiv_fibre (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    surfaceH3Equiv j p (SingularMayerVietoris.singularHomologyMap (fibreIntoSurface j p) 3 a) =
      ![torusH3Coordinates a, 0] := by
  change
    mappingTorusH3Equiv j
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p) 3
          (SingularMayerVietoris.singularHomologyMap (fibreIntoSurface j p) 3 a)) =
      _
  rw [surfaceMappingTorusHomology_fibre, mappingTorusH3Equiv_fibre]


-- @@ L173-189 verbatim
private theorem Elliptic.HigherHomology.surfaceH2Equiv_periodCover_fibre (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2) :
    surfaceH2Equiv j p
        (SingularMayerVietoris.singularHomologyMap
          (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 2
          (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) 2 a)) =
      ![torusH2Coordinates a 0, 0] := by
  change
    surfaceH2Equiv j p
        (((SingularMayerVietoris.singularHomologyMap
                (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 2).comp
            (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) 2))
          a) =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact surfaceH2Equiv_fibre j p a


-- @@ L191-207 verbatim
private theorem Elliptic.HigherHomology.surfaceH3Equiv_periodCover_fibre (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    surfaceH3Equiv j p
        (SingularMayerVietoris.singularHomologyMap
          (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 3
          (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) 3 a)) =
      ![torusH3Coordinates a, 0] := by
  change
    surfaceH3Equiv j p
        (((SingularMayerVietoris.singularHomologyMap
                (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 3).comp
            (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) 3))
          a) =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact surfaceH3Equiv_fibre j p a


-- @@ L209-214 verbatim
private def Elliptic.HigherHomology.surfacePeriodCoverH2Coordinates (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    SingularMayerVietoris.SingularHomology p.val.Torus 2 →ₗ[ℤ] (Fin 2 → ℤ) :=
  (surfaceH2Equiv j p).toLinearMap.comp
    (SingularMayerVietoris.singularHomologyMap
      (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 2)


-- @@ L216-221 verbatim
private def Elliptic.HigherHomology.surfacePeriodCoverH3Coordinates (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    SingularMayerVietoris.SingularHomology p.val.Torus 3 →ₗ[ℤ] (Fin 2 → ℤ) :=
  (surfaceH3Equiv j p).toLinearMap.comp
    (SingularMayerVietoris.singularHomologyMap
      (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 3)


-- @@ L223-227 verbatim
private def Elliptic.HigherHomology.surfacePeriodCoverH4Coordinates (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) : SingularMayerVietoris.SingularHomology p.val.Torus 4 →ₗ[ℤ] ℤ :=
  (surfaceH4Equiv j p).toLinearMap.comp
    (SingularMayerVietoris.singularHomologyMap
      (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 4)


-- @@ L229-233 verbatim
/-- The index contributed by the norm map for each elliptic fibre type. -/
public
def Elliptic.HigherHomology.fibreNormIndex : Elliptic.Kind → ℕ
  | .three => 1
  | .four => 2


-- @@ L235-237 verbatim
@[simp]
private theorem Elliptic.HigherHomology.fibreNormIndex_three : fibreNormIndex .three = 1 :=
  rfl


-- @@ L239-241 verbatim
@[simp]
private theorem Elliptic.HigherHomology.fibreNormIndex_four : fibreNormIndex .four = 2 :=
  rfl


-- @@ L243-245 verbatim
private theorem
    Elliptic.HigherHomology.fibreNormIndex_pos (j : Elliptic.Kind) : 0 < fibreNormIndex j := by
  cases j <;> decide


-- @@ L247-249 verbatim
public
theorem Elliptic.HigherHomology.fibreNormIndex_int_ne_zero (j : Elliptic.Kind) :
    (fibreNormIndex j : ℤ) ≠ 0 := by exact_mod_cast (fibreNormIndex_pos j).ne'


-- @@ L251-252 verbatim
private def Elliptic.HigherHomology.fibreNormMatrix (j : Elliptic.Kind) : FibreMatrix :=
  ∑ k ∈ Finset.range j.order, (fibreMatrix j) ^ k


-- @@ L254-255 verbatim
private def Elliptic.HigherHomology.fibreSquareNormMatrix (j : Elliptic.Kind) : FibreMatrix :=
  ∑ k ∈ Finset.range j.order, (fibreSquareMatrix j) ^ k


-- @@ L257-259 verbatim
@[simp]
private theorem Elliptic.HigherHomology.fibreNormMatrix_three :
    fibreNormMatrix .three = !![0, 0, 0; 0, 0, 0; 2, 1, 3] := by decide


-- @@ L261-263 verbatim
@[simp]
private theorem Elliptic.HigherHomology.fibreNormMatrix_four :
    fibreNormMatrix .four = !![0, 0, 0; 0, 0, 0; 2, 2, 4] := by decide


-- @@ L265-267 verbatim
@[simp]
private theorem Elliptic.HigherHomology.fibreSquareNormMatrix_three :
    fibreSquareNormMatrix .three = !![3, 0, 0; -1, 0, 0; 2, 0, 0] := by decide


-- @@ L269-271 verbatim
@[simp]
private theorem Elliptic.HigherHomology.fibreSquareNormMatrix_four :
    fibreSquareNormMatrix .four = !![4, 0, 0; -2, 0, 0; 2, 0, 0] := by decide


-- @@ L273-275 verbatim
private def
    Elliptic.HigherHomology.fibreNorm (j : Elliptic.Kind) : FibreLattice →ₗ[ℤ] FibreLattice :=
  (fibreNormMatrix j).mulVecLin


-- @@ L277-282 verbatim
private theorem Elliptic.HigherHomology.fibreNorm_apply (j : Elliptic.Kind) (v : FibreLattice) :
    fibreNorm j v =
      ((fibreNormIndex j : ℤ) * fibreCoinvariantCoordinate j v) • fibreKernelVector := by
  cases j <;> ext i <;> fin_cases i <;>
    simp [fibreCoinvariantCoordinate, fibreNorm, fibreKernelVector, dotProduct, Fin.sum_univ_succ]
  all_goals ring


-- @@ L284-288 verbatim
@[simp]
private theorem Elliptic.HigherHomology.fibreNorm_apply_two (j : Elliptic.Kind) (v : FibreLattice) :
    fibreNorm j v 2 = (fibreNormIndex j : ℤ) * fibreCoinvariantCoordinate j v := by
  rw [fibreNorm_apply]
  simp [fibreKernelVector]


-- @@ L290-292 verbatim
private def Elliptic.HigherHomology.fibreSquareNorm (j : Elliptic.Kind) :
    FibreLattice →ₗ[ℤ] FibreLattice :=
  (fibreSquareNormMatrix j).mulVecLin


-- @@ L294-300 verbatim
@[simp]
private theorem
    Elliptic.HigherHomology.fibreSquareNorm_apply (j : Elliptic.Kind) (v : FibreLattice) :
    fibreSquareNorm j v = ((fibreNormIndex j : ℤ) * v 0) • fibreSquareKernelVector j := by
  cases j <;> ext i <;> fin_cases i <;>
    simp [fibreSquareKernelVector, fibreSquareNorm, dotProduct, Fin.sum_univ_succ]
  all_goals ring


-- @@ L302-306 verbatim
private theorem
    Elliptic.HigherHomology.fibreSquareNorm_mem_ker (j : Elliptic.Kind) (v : FibreLattice) :
    fibreSquareNorm j v ∈ LinearMap.ker (fibreSquareDifference j) := by
  rw [LinearMap.mem_ker, fibreSquareNorm_apply, map_smul, fibreSquareDifference_kernelVector,
    smul_zero]


-- @@ L308-310 verbatim
private def Elliptic.HigherHomology.fibreSquareNormToKernel (j : Elliptic.Kind) :
    FibreLattice →ₗ[ℤ] LinearMap.ker (fibreSquareDifference j) :=
  (fibreSquareNorm j).codRestrict _ (fibreSquareNorm_mem_ker j)


-- @@ L312-314 verbatim
private def Elliptic.HigherHomology.fibreSquareNormCoordinate (j : Elliptic.Kind) :
    FibreLattice →ₗ[ℤ] ℤ :=
  (fibreSquareKernelEquivInt j).toLinearMap.comp (fibreSquareNormToKernel j)


-- @@ L316-318 verbatim
private theorem Elliptic.HigherHomology.fibreSquareNormCoordinate_eq_neg_second (j : Elliptic.Kind)
    (v : FibreLattice) : fibreSquareNormCoordinate j v = -(fibreSquareNorm j v) 1 :=
  rfl


-- @@ L320-324 verbatim
@[simp]
private theorem Elliptic.HigherHomology.fibreSquareNormCoordinate_apply (j : Elliptic.Kind)
    (v : FibreLattice) : fibreSquareNormCoordinate j v = (fibreNormIndex j : ℤ) * v 0 := by
  rw [fibreSquareNormCoordinate_eq_neg_second, fibreSquareNorm_apply]
  simp


-- @@ L326-331 verbatim
private theorem Elliptic.HigherHomology.markedLinearPower {M : Type*} [AddCommGroup M] [Module ℤ M]
    (e : M ≃ₗ[ℤ] FibreLattice) (f : M →ₗ[ℤ] M) (A : FibreMatrix) (h : ∀ a, e (f a) = A *ᵥ e a)
    (k : ℕ) (a : M) : e ((f ^ k) a) = A ^ k *ᵥ e a := by
  induction k generalizing a with
  | zero => simp only [pow_zero, Module.End.one_apply, Matrix.one_mulVec]
  | succ k ih => rw [pow_succ, Module.End.mul_apply, ih, h, pow_succ, Matrix.mulVec_mulVec]


-- @@ L333-337 verbatim
private def Elliptic.HigherHomology.fibreHomologyNorm (j : Elliptic.Kind) (n : ℕ) :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) n →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) n :=
  ∑ k ∈ Finset.range j.order,
    (MappingTorusHomology.monodromyHomologyMap (fibreTorusHomeomorph j) n) ^ k


-- @@ L339-343 verbatim
private theorem Elliptic.HigherHomology.fibreHomologyMonodromy_one (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1) :
    torusH1Equiv (MappingTorusHomology.monodromyHomologyMap (fibreTorusHomeomorph j) 1 a) =
      fibreMatrix j *ᵥ torusH1Equiv a :=
  torusH1Equiv_matrix_natural (fibreMatrix j) a


-- @@ L345-349 verbatim
private theorem Elliptic.HigherHomology.fibreHomologyMonodromy_two (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2) :
    torusH2Coordinates (MappingTorusHomology.monodromyHomologyMap (fibreTorusHomeomorph j) 2 a) =
      fibreSquareMatrix j *ᵥ torusH2Coordinates a :=
  torusH2Coordinates_fibreMatrix j a


-- @@ L351-355 verbatim
private theorem Elliptic.HigherHomology.fibreHomologyMonodromy_three (j : Elliptic.Kind) :
    MappingTorusHomology.monodromyHomologyMap (fibreTorusHomeomorph j) 3 = 1 := by
  ext a
  apply torusH3Coordinates.injective
  exact torusH3Coordinates_fibreMatrix j a


-- @@ L357-364 verbatim
private theorem Elliptic.HigherHomology.fibreHomologyNorm_one (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1) :
    torusH1Equiv (fibreHomologyNorm j 1 a) = fibreNorm j (torusH1Equiv a) := by
  simp only [fibreHomologyNorm, LinearMap.sum_apply, map_sum, fibreNorm, Matrix.mulVecLin_apply,
    fibreNormMatrix]
  apply Finset.sum_congr rfl
  intro k hk
  exact markedLinearPower torusH1Equiv _ _ (fibreHomologyMonodromy_one j) k a


-- @@ L366-373 verbatim
private theorem Elliptic.HigherHomology.fibreHomologyNorm_two (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2) :
    torusH2Coordinates (fibreHomologyNorm j 2 a) = fibreSquareNorm j (torusH2Coordinates a) := by
  simp only [fibreHomologyNorm, LinearMap.sum_apply, map_sum, fibreSquareNorm,
    Matrix.mulVecLin_apply, fibreSquareNormMatrix]
  apply Finset.sum_congr rfl
  intro k hk
  exact markedLinearPower torusH2Coordinates _ _ (fibreHomologyMonodromy_two j) k a


-- @@ L375-378 verbatim
private theorem Elliptic.HigherHomology.fibreHomologyNorm_three (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    torusH3Coordinates (fibreHomologyNorm j 3 a) = (j.order : ℤ) * torusH3Coordinates a := by
  simp [fibreHomologyNorm, fibreHomologyMonodromy_three]


-- @@ L380-382 verbatim
private def Elliptic.HigherHomology.fibreHomologyNormOneCoordinate (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1 →ₗ[ℤ] ℤ :=
  (LinearMap.proj (2 : Fin 3)).comp (torusH1Equiv.toLinearMap.comp (fibreHomologyNorm j 1))


-- @@ L384-389 verbatim
private theorem Elliptic.HigherHomology.fibreHomologyNormOneCoordinate_apply (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1) :
    fibreHomologyNormOneCoordinate j a =
      (fibreNormIndex j : ℤ) * fibreCoinvariantCoordinate j (torusH1Equiv a) := by
  change torusH1Equiv (fibreHomologyNorm j 1 a) 2 = _
  rw [fibreHomologyNorm_one, fibreNorm_apply_two]


-- @@ L391-393 verbatim
private def Elliptic.HigherHomology.fibreHomologyNormTwoCoordinate (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2 →ₗ[ℤ] ℤ :=
  (-LinearMap.proj (1 : Fin 3)).comp (torusH2Coordinates.toLinearMap.comp (fibreHomologyNorm j 2))


-- @@ L395-400 verbatim
private theorem Elliptic.HigherHomology.fibreHomologyNormTwoCoordinate_apply (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 2) :
    fibreHomologyNormTwoCoordinate j a = (fibreNormIndex j : ℤ) * torusH2Coordinates a 0 := by
  change -(torusH2Coordinates (fibreHomologyNorm j 2 a) 1) = _
  rw [fibreHomologyNorm_two]
  exact fibreSquareNormCoordinate_apply j (torusH2Coordinates a)


-- @@ L402-404 verbatim
private def Elliptic.HigherHomology.fibreHomologyNormThreeCoordinate (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3 →ₗ[ℤ] ℤ :=
  torusH3Coordinates.toLinearMap.comp (fibreHomologyNorm j 3)


-- @@ L406-409 verbatim
private theorem Elliptic.HigherHomology.fibreHomologyNormThreeCoordinate_apply (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 3) :
    fibreHomologyNormThreeCoordinate j a = (j.order : ℤ) * torusH3Coordinates a :=
  fibreHomologyNorm_three j a


-- @@ L411-417 verbatim
@[simp]
private theorem
    Elliptic.HigherHomology.mappingTorusProductCover_eq_productCover (j : Elliptic.Kind) :
    mappingTorusProductCover j =
      MappingTorusHomology.Covering.productCover j.order (fibreTorusHomeomorph j)
        (fibreTorusHomeomorph_pow_order j) :=
  rfl


-- @@ L419-424 verbatim
private theorem
    Elliptic.HigherHomology.fibreHomologyNorm_eq_homologyNorm (j : Elliptic.Kind) (n : ℕ) :
    fibreHomologyNorm j n =
      MappingTorusHomology.Covering.homologyNorm j.order (fibreTorusHomeomorph j) n :=
  (MappingTorusHomology.Covering.homologyNorm_eq_sum_powers j.order (fibreTorusHomeomorph j)
      n).symm


-- @@ L426-432 verbatim
private def Elliptic.HigherHomology.surfacePeriodCoverCircleBoundary (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ) :
    SingularMayerVietoris.SingularHomology p.val.Torus (n + 1) →ₗ[ℤ]
      SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) n :=
  (PeriodTorusHigherHomology.circleBoundary (PeriodTorusHigherHomology.ProductTorus 3) n).comp
    (PeriodTorusHigherHomology.homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val)
        (n + 1)).toLinearMap


-- @@ L434-442 verbatim
@[simp]
private theorem Elliptic.HigherHomology.surfacePeriodCoverCircleBoundary_apply (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology p.val.Torus (n + 1)) :
    surfacePeriodCoverCircleBoundary j p n a =
      PeriodTorusHigherHomology.circleBoundary (PeriodTorusHigherHomology.ProductTorus 3) n
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val)
          (n + 1) a) :=
  rfl


-- @@ L444-469 verbatim
private theorem Elliptic.HigherHomology.surfacePeriodCover_wangBoundary (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (n : ℕ)
    (a : SingularMayerVietoris.SingularHomology p.val.Torus (n + 1)) :
    MappingTorusHomology.wangBoundary (fibreTorusHomeomorph j).symm n
        (surfaceMappingTorusHomologyEquiv j p (n + 1)
          (SingularMayerVietoris.singularHomologyMap
            (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) (n + 1) a)) =
      fibreHomologyNorm j n (surfacePeriodCoverCircleBoundary j p n a) := by
  change
    MappingTorusHomology.wangBoundary (fibreTorusHomeomorph j).symm n
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p)
          (n + 1)
          (SingularMayerVietoris.singularHomologyMap
            (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) (n + 1) a)) =
      _
  rw [surfaceMappingTorusHomology_periodCover, mappingTorusProductCover_eq_productCover]
  change
    MappingTorusHomology.wangBoundary (fibreTorusHomeomorph j).symm n
        (MappingTorusHomology.Covering.productCoverHomology j.order (fibreTorusHomeomorph j)
          (fibreTorusHomeomorph_pow_order j) (n + 1)
          (PeriodTorusHigherHomology.homeomorphHomologyEquiv (splitPeriodTorusHomeomorph j p.val)
            (n + 1) a)) =
      _
  rw [MappingTorusHomology.Covering.wangBoundary_productCover_apply, ←
    fibreHomologyNorm_eq_homologyNorm]
  rfl


-- @@ L471-485 verbatim
private theorem
    Elliptic.HigherHomology.surfacePeriodCoverH2Coordinates_secondMap (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    CoverAlgebra.secondMap (surfacePeriodCoverH2Coordinates j p) =
      (fibreHomologyNormOneCoordinate j).comp (surfacePeriodCoverCircleBoundary j p 1) := by
  ext a
  change
    mappingTorusH2Equiv j
        (surfaceMappingTorusHomologyEquiv j p 2
          (SingularMayerVietoris.singularHomologyMap
            (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 2 a))
        1 =
      _
  rw [mappingTorusH2Equiv_boundary, surfacePeriodCover_wangBoundary]
  rfl


-- @@ L487-501 verbatim
private theorem
    Elliptic.HigherHomology.surfacePeriodCoverH3Coordinates_secondMap (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    CoverAlgebra.secondMap (surfacePeriodCoverH3Coordinates j p) =
      (fibreHomologyNormTwoCoordinate j).comp (surfacePeriodCoverCircleBoundary j p 2) := by
  ext a
  change
    mappingTorusH3Equiv j
        (surfaceMappingTorusHomologyEquiv j p 3
          (SingularMayerVietoris.singularHomologyMap
            (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 3 a))
        1 =
      _
  rw [mappingTorusH3Equiv_boundary, surfacePeriodCover_wangBoundary]
  rfl


-- @@ L503-514 verbatim
private theorem Elliptic.HigherHomology.surfacePeriodCoverH4Coordinates_eq_norm (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    surfacePeriodCoverH4Coordinates j p =
      (fibreHomologyNormThreeCoordinate j).comp (surfacePeriodCoverCircleBoundary j p 3) := by
  ext a
  change
    mappingTorusH4Equiv j
        (surfaceMappingTorusHomologyEquiv j p 4
          (SingularMayerVietoris.singularHomologyMap
            (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 4 a)) =
      torusH3Coordinates (fibreHomologyNorm j 3 (surfacePeriodCoverCircleBoundary j p 3 a))
  rw [mappingTorusH4Equiv_boundary, surfacePeriodCover_wangBoundary]


-- @@ L516-521 verbatim
private theorem Elliptic.HigherHomology.surfacePeriodCoverH4Coordinates_apply (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) (a : SingularMayerVietoris.SingularHomology p.val.Torus 4) :
    surfacePeriodCoverH4Coordinates j p a =
      (j.order : ℤ) * torusH3Coordinates (surfacePeriodCoverCircleBoundary j p 3 a) := by
  rw [surfacePeriodCoverH4Coordinates_eq_norm, LinearMap.comp_apply,
    fibreHomologyNormThreeCoordinate_apply]



-- @@ L524-529 verbatim
private def
    Elliptic.HigherHomology.surfaceH1Equiv (j : Elliptic.Kind) (p : Elliptic.FixedPeriod j) :
    SingularMayerVietoris.SingularHomology
        (Elliptic.Surface j p j.twist (Elliptic.mainTwist_admissible j)) 1 ≃ₗ[ℤ]
      (Fin 2 → ℤ) :=
  (surfaceMappingTorusHomologyEquiv j p 1).trans (mappingTorusH1Equiv j)


-- @@ L531-541 verbatim
private theorem Elliptic.HigherHomology.surfaceH1Equiv_fibre (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1) :
    surfaceH1Equiv j p (SingularMayerVietoris.singularHomologyMap (fibreIntoSurface j p) 1 a) =
      ![fibreCoinvariantCoordinate j (torusH1Equiv a), 0] := by
  change
    mappingTorusH1Equiv j
        (PeriodTorusHigherHomology.homeomorphHomologyEquiv (surfaceMappingTorusHomeomorph j p) 1
          (SingularMayerVietoris.singularHomologyMap (fibreIntoSurface j p) 1 a)) =
      _
  rw [surfaceMappingTorusHomology_fibre, mappingTorusH1Equiv_fibre]


-- @@ L543-559 verbatim
private theorem Elliptic.HigherHomology.surfaceH1Equiv_periodCover_fibre (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 1) :
    surfaceH1Equiv j p
        (SingularMayerVietoris.singularHomologyMap
          (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 1
          (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) 1 a)) =
      ![fibreCoinvariantCoordinate j (torusH1Equiv a), 0] := by
  change
    surfaceH1Equiv j p
        (((SingularMayerVietoris.singularHomologyMap
                (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 1).comp
            (SingularMayerVietoris.singularHomologyMap (fibreIntoPeriodTorus j p) 1))
          a) =
      _
  rw [← PeriodTorusHigherHomology.singularHomologyMap_comp]
  exact surfaceH1Equiv_fibre j p a


-- @@ L561-569 verbatim
private theorem Elliptic.HigherHomology.fibreHomologyMonodromy_zero (j : Elliptic.Kind) :
    MappingTorusHomology.monodromyHomologyMap (fibreTorusHomeomorph j) 0 = 1 := by
  ext a
  apply torusH0Coordinates.injective
  exact
    PeriodTorusHigherHomology.connectedHomologyZeroEquiv_natural
      (fibreTorusHomeomorph j :
        C(PeriodTorusHigherHomology.ProductTorus 3, PeriodTorusHigherHomology.ProductTorus 3))
      a


-- @@ L571-574 verbatim
private theorem Elliptic.HigherHomology.fibreHomologyNorm_zero (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 0) :
    torusH0Coordinates (fibreHomologyNorm j 0 a) = (j.order : ℤ) * torusH0Coordinates a := by
  simp [fibreHomologyNorm, fibreHomologyMonodromy_zero]


-- @@ L576-578 verbatim
private def Elliptic.HigherHomology.fibreHomologyNormZeroCoordinate (j : Elliptic.Kind) :
    SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 0 →ₗ[ℤ] ℤ :=
  torusH0Coordinates.toLinearMap.comp (fibreHomologyNorm j 0)


-- @@ L580-583 verbatim
private theorem Elliptic.HigherHomology.fibreHomologyNormZeroCoordinate_apply (j : Elliptic.Kind)
    (a : SingularMayerVietoris.SingularHomology (PeriodTorusHigherHomology.ProductTorus 3) 0) :
    fibreHomologyNormZeroCoordinate j a = (j.order : ℤ) * torusH0Coordinates a :=
  fibreHomologyNorm_zero j a


-- @@ L585-590 verbatim
private def Elliptic.HigherHomology.surfacePeriodCoverH1Coordinates (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    SingularMayerVietoris.SingularHomology p.val.Torus 1 →ₗ[ℤ] (Fin 2 → ℤ) :=
  (surfaceH1Equiv j p).toLinearMap.comp
    (SingularMayerVietoris.singularHomologyMap
      (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 1)


-- @@ L592-606 verbatim
private theorem
    Elliptic.HigherHomology.surfacePeriodCoverH1Coordinates_secondMap (j : Elliptic.Kind)
    (p : Elliptic.FixedPeriod j) :
    CoverAlgebra.secondMap (surfacePeriodCoverH1Coordinates j p) =
      (fibreHomologyNormZeroCoordinate j).comp (surfacePeriodCoverCircleBoundary j p 0) := by
  ext a
  change
    mappingTorusH1Equiv j
        (surfaceMappingTorusHomologyEquiv j p 1
          (SingularMayerVietoris.singularHomologyMap
            (periodCover j p j.twist (Elliptic.mainTwist_admissible j)) 1 a))
        1 =
      _
  rw [mappingTorusH1Equiv_boundary, surfacePeriodCover_wangBoundary]
  rfl


-- @@ L608-608 verbatim
end Mathoverflow1973


-- @@ L610-610 verbatim
end
