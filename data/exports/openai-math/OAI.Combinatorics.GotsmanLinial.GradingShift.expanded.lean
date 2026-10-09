import OAI.Combinatorics.GotsmanLinial.WeightedGrading
import OAI.Combinatorics.GotsmanLinial.ProjectionBlocks
import OAI.Combinatorics.GotsmanLinial.CoordinateDegree


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-12 verbatim
/-!
# A degree shift is tridiagonal in the associated orthogonal grading

These lemmas retain the degree-shift premise explicitly. The cube application
discharges it using coordinate multiplication and the weighted Fourier flag.
-/


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
namespace LeanBlast.GotsmanLinial


-- @@ L18-18 verbatim
section FiniteFlag


-- @@ L20-21 verbatim
variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
  [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]


-- @@ L23-23 verbatim
local instance : CompleteSpace E := FiniteDimensional.complete 𝕜 E


-- @@ L25-36 verbatim
/-- An operator that raises the flag index by at most one has no blocks
strictly above the first off-diagonal. -/
theorem flagProjection_mul_shift_eq_zero
    (K : ℕ → Submodule 𝕜 E) (hK : Monotone K) (Z : E →L[𝕜] E)
    (hshift : ∀ k x, x ∈ K k → Z x ∈ K (k + 1))
    {r s : ℕ} (hrs : r + 1 < s) :
    flagProjection K s * Z * flagProjection K r = 0 := by
  ext x
  change flagProjection K s (Z (flagProjection K r x)) = 0
  apply flagProjection_apply_eq_zero_of_mem_prev
  exact hK (by omega : r + 1 + 1 ≤ s)
    (hshift (r + 1) (flagProjection K r x) (flagProjection_apply_mem_next K r x))


-- @@ L38-49 verbatim
/-- Self-adjointness gives the other half of the band by taking adjoints. -/
theorem flagProjection_tridiagonal
    (K : ℕ → Submodule 𝕜 E) (hK : Monotone K) (Z : E →L[𝕜] E)
    (hZ : IsSelfAdjoint Z)
    (hshift : ∀ k x, x ∈ K k → Z x ∈ K (k + 1))
    {r s : ℕ} (hrs : r + 1 < s ∨ s + 1 < r) :
    flagProjection K s * Z * flagProjection K r = 0 := by
  rcases hrs with hrs | hsr
  · exact flagProjection_mul_shift_eq_zero K hK Z hshift hrs
  · have h := congrArg star (flagProjection_mul_shift_eq_zero K hK Z hshift hsr)
    simpa only [star_mul, star_zero, (flagProjection_isSelfAdjoint K r).star_eq,
      (flagProjection_isSelfAdjoint K s).star_eq, hZ.star_eq, mul_assoc] using h


-- @@ L51-60 verbatim
/-- The band property is preserved by taking matrices or any other ring
representation of the operator algebra. -/
theorem map_flagProjection_tridiagonal
    {A : Type*} [Ring A] (F : (E →L[𝕜] E) →+* A)
    (K : ℕ → Submodule 𝕜 E) (hK : Monotone K) (Z : E →L[𝕜] E)
    (hZ : IsSelfAdjoint Z)
    (hshift : ∀ k x, x ∈ K k → Z x ∈ K (k + 1))
    {r s : ℕ} (hrs : r + 1 < s ∨ s + 1 < r) :
    F (flagProjection K s) * F Z * F (flagProjection K r) = 0 := by
  rw [← map_mul, ← map_mul, flagProjection_tridiagonal K hK Z hZ hshift hrs, map_zero]


-- @@ L62-71 verbatim
omit [FiniteDimensional 𝕜 E] in
/-- Commutation transports a degree-shift statement through a weight map. -/
theorem shift_mem_map_of_commute
    (V : ℕ → Submodule 𝕜 E) (D Z : E →ₗ[𝕜] E)
    (hcommute : ∀ x, Z (D x) = D (Z x))
    (hshift : ∀ k x, x ∈ V k → Z x ∈ V (k + 1))
    (k : ℕ) {x : E} (hx : x ∈ (V k).map D) :
    Z x ∈ (V (k + 1)).map D := by
  rcases hx with ⟨y, hy, rfl⟩
  exact ⟨Z y, hshift k y hy, (hcommute y).symm⟩


-- @@ L73-73 verbatim
end FiniteFlag


-- @@ L75-75 verbatim
section MatrixFlag


-- @@ L77-78 verbatim
variable {E ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [Fintype ι] [DecidableEq ι]


-- @@ L80-80 verbatim
local instance : CompleteSpace E := FiniteDimensional.complete ℂ E


-- @@ L82-93 verbatim
/-- The concrete matrix form consumed by the commutator estimate. -/
theorem operatorMatrix_flagProjection_tridiagonal
    (b : OrthonormalBasis ι ℂ E)
    (K : ℕ → Submodule ℂ E) (hK : Monotone K) (Z : E →L[ℂ] E)
    (hZ : IsSelfAdjoint Z)
    (hshift : ∀ k x, x ∈ K k → Z x ∈ K (k + 1))
    (n : ℕ) (r s : Fin (n + 1))
    (hrs : r.val + 1 < s.val ∨ s.val + 1 < r.val) :
    operatorMatrix b (flagProjection K s.val) * operatorMatrix b Z *
      operatorMatrix b (flagProjection K r.val) = 0 := by
  exact map_flagProjection_tridiagonal (operatorMatrixEquiv b).toRingHom
    K hK Z hZ hshift hrs


-- @@ L95-95 verbatim
end MatrixFlag


-- @@ L97-97 verbatim
section WeightedCube


-- @@ L99-99 verbatim
variable {n : ℕ}


-- @@ L101-109 verbatim
/-- Coordinate signs commute with the actual positive square-root weight. -/
theorem coordinateMultiplier_sqrtWeight_commute
    (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) (i : Fin n)
    (a : EuclideanSpace ℂ (Cube n)) :
    coordinateMultiplier i (sqrtWeightEquiv w hw a) =
      sqrtWeightEquiv w hw (coordinateMultiplier i a) := by
  ext x
  simp only [coordinateMultiplier_apply, sqrtWeightEquiv_apply]
  exact mul_left_comm _ _ _


-- @@ L111-122 verbatim
/-- The actual weighted Fourier flag retains the one-step coordinate shift. -/
theorem coordinateMultiplier_weightedFlag_shift
    (w : Cube n → ℝ) (hw : ∀ x, 0 < w x) (i : Fin n) :
    ∀ k (a : EuclideanSpace ℂ (Cube n)),
      a ∈ transportFlag (sqrtWeightEquiv w hw) (fourierFlag n) k →
      coordinateMultiplier i a ∈
        transportFlag (sqrtWeightEquiv w hw) (fourierFlag n) (k + 1) := by
  intro k a ha
  exact shift_mem_map_of_commute (fourierFlag n) (sqrtWeightEquiv w hw).toLinearMap
    (coordinateMultiplier i).toLinearMap
    (coordinateMultiplier_sqrtWeight_commute w hw i)
    (coordinateMultiplier_fourierFlag_shift i) k ha


-- @@ L124-138 verbatim
/-- Tridiagonality for the actually constructed weighted Fourier projections,
expressed in an arbitrary orthonormal coordinate system. -/
theorem weightedFlag_operatorMatrix_tridiagonal
    (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (b : OrthonormalBasis (Cube n) ℂ (EuclideanSpace ℂ (Cube n)))
    (i : Fin n) (r s : Fin (n + 1))
    (hrs : r.val + 1 < s.val ∨ s.val + 1 < r.val) :
    flagProjectionMatrix b (transportFlag (sqrtWeightEquiv w hw) (fourierFlag n)) s.val *
      operatorMatrix b (coordinateMultiplier i) *
      flagProjectionMatrix b (transportFlag (sqrtWeightEquiv w hw) (fourierFlag n)) r.val = 0 := by
  exact operatorMatrix_flagProjection_tridiagonal b
    (transportFlag (sqrtWeightEquiv w hw) (fourierFlag n))
    (transportFlag_monotone _ _ (fourierFlag_mono n))
    (coordinateMultiplier i) (coordinateMultiplier_isSelfAdjoint i)
    (coordinateMultiplier_weightedFlag_shift w hw i) n r s hrs


-- @@ L140-151 verbatim
/-- The raw coordinate-sign matrices are tridiagonal for the actual weighted
Fourier projection family. There is no remaining degree-shift hypothesis. -/
theorem weightedProjectionMatrix_tridiagonal
    (w : Cube n → ℝ) (hw : ∀ x, 0 < w x)
    (i : Fin n) (r s : Fin (n + 1))
    (hrs : r.val + 1 < s.val ∨ s.val + 1 < r.val) :
    weightedProjectionMatrix w hw s * coordinateSignMatrix i *
      weightedProjectionMatrix w hw r = 0 := by
  simpa only [weightedProjectionMatrix, weightedFourierFlag, coordinateMultiplier,
    signMultiplier, operatorMatrix_toEuclideanCLM, coordinateSignMatrix] using
    weightedFlag_operatorMatrix_tridiagonal w hw
      (EuclideanSpace.basisFun (Cube n) ℂ) i r s hrs


-- @@ L153-153 verbatim
end WeightedCube


-- @@ L155-155 verbatim
end LeanBlast.GotsmanLinial


-- @@ L157-157 verbatim
end


-- @@ L159-159 verbatim
end OAI
