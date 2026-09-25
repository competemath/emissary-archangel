/-
Copyright (c) 2026 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kei Tsukamoto, Kento Mori, Hayata Yamasaki
-/
module

public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.LownerHeinzTheorem
public import QuantumInfo.ForMathlib.HayataGroup.TraceInequality.GeneralizedPerspectiveFunction

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Topology.Algebra.Module.FiniteDimension


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace HilbertSchmidtOperatorSpace


-- @@ L22-22 verbatim
open LownerHeinzTheorem


-- @@ L24-24 verbatim
universe u


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
variable {ℋ : Type u}

-- @@ L29-29 verbatim
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]

-- @@ L30-30 verbatim
variable [FiniteDimensional ℂ ℋ]


-- @@ L32-35 verbatim
/-- The canonical finite index used for Hilbert-Schmidt coordinates. -/
abbrev HSIndex (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [FiniteDimensional ℂ ℋ] :=
  Fin (Module.finrank ℂ ℋ)


-- @@ L37-40 verbatim
/-- The standard orthonormal basis on a finite-dimensional Hilbert space. -/
noncomputable abbrev hsOrthonormalBasis :
    OrthonormalBasis (HSIndex ℋ) ℂ ℋ :=
  stdOrthonormalBasis ℂ ℋ


-- @@ L42-45 verbatim
/-- Coordinate space for Hilbert-Schmidt operators. -/
abbrev HSCoords (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [FiniteDimensional ℂ ℋ] :=
  EuclideanSpace ℂ (HSIndex ℋ × HSIndex ℋ)


-- @@ L47-50 verbatim
/-- The underlying coordinate function space for Hilbert-Schmidt operators. -/
abbrev HSCoordFun (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [FiniteDimensional ℂ ℋ] :=
  HSIndex ℋ × HSIndex ℋ → ℂ


-- @@ L52-54 verbatim
/-- The operator space `L ℋ`, viewed later with the Hilbert-Schmidt structure. -/
def HSOp (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] : Type u :=
  L ℋ


-- @@ L56-58 verbatim
instance : AddCommGroup (HSOp ℋ) := by
  delta HSOp
  infer_instance


-- @@ L60-63 verbatim
set_option synthInstance.maxHeartbeats 200000 in
instance : Module ℂ (HSOp ℋ) := by
  show Module ℂ (ℋ →L[ℂ] ℋ)
  infer_instance


-- @@ L65-67 verbatim
instance : Star (HSOp ℋ) := by
  delta HSOp
  infer_instance


-- @@ L69-71 verbatim
instance : Mul (HSOp ℋ) := by
  delta HSOp
  infer_instance


-- @@ L73-75 verbatim
instance : One (HSOp ℋ) := by
  delta HSOp
  infer_instance


-- @@ L77-79 verbatim
instance : Inhabited (HSOp ℋ) := by
  delta HSOp
  infer_instance


-- @@ L81-83 verbatim
instance : Zero (HSOp ℋ) := by
  delta HSOp
  infer_instance


-- @@ L85-88 verbatim
set_option synthInstance.maxHeartbeats 200000 in
instance : FiniteDimensional ℂ (HSOp ℋ) := by
  show FiniteDimensional ℂ (ℋ →L[ℂ] ℋ)
  infer_instance


-- @@ L90-93 verbatim
noncomputable def hsCoordsLinearEquiv :
    HSCoords ℋ ≃ₗ[ℂ] (HSCoordFun ℋ) := by
  simpa [HSCoords, HSCoordFun] using
    (WithLp.linearEquiv (2 : ENNReal) ℂ (HSCoordFun ℋ))


-- @@ L95-110 verbatim
def matrixToFun :
    Matrix (HSIndex ℋ) (HSIndex ℋ) ℂ ≃ₗ[ℂ] HSCoordFun ℋ where
  toFun M p := M p.1 p.2
  invFun f i j := f (i, j)
  map_add' M N := by
    ext ⟨i, j⟩
    rfl
  map_smul' c M := by
    ext ⟨i, j⟩
    rfl
  left_inv M := by
    ext i j
    rfl
  right_inv f := by
    ext ⟨i, j⟩
    rfl


-- @@ L112-114 verbatim
noncomputable def matrixToCoords :
    Matrix (HSIndex ℋ) (HSIndex ℋ) ℂ ≃ₗ[ℂ] HSCoords ℋ :=
  (matrixToFun (ℋ := ℋ)).trans hsCoordsLinearEquiv.symm


-- @@ L116-119 verbatim
/-- Forget continuity and identify continuous linear operators with linear endomorphisms. -/
noncomputable def hsLinearMapEquiv :
    HSOp ℋ ≃ₗ[ℂ] (ℋ →ₗ[ℂ] ℋ) :=
  LinearMap.toContinuousLinearMap.symm


-- @@ L121-127 verbatim
/-- Hilbert-Schmidt coordinates on `L ℋ`. -/
noncomputable def toHSCoordsLinearEquiv :
    HSOp ℋ ≃ₗ[ℂ] HSCoords ℋ :=
  (hsLinearMapEquiv (ℋ := ℋ)).trans <|
    (LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
      (hsOrthonormalBasis (ℋ := ℋ)).toBasis).trans <|
      matrixToCoords (ℋ := ℋ)


-- @@ L129-148 verbatim
omit [CompleteSpace ℋ] in
@[simp] lemma toHSCoordsLinearEquiv_apply_apply
    (T : HSOp ℋ) (i j : HSIndex ℋ) :
    toHSCoordsLinearEquiv (ℋ := ℋ) T (i, j) =
      LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
        (hsOrthonormalBasis (ℋ := ℋ)).toBasis
        ((hsLinearMapEquiv (ℋ := ℋ)) T) i j := by
  change hsCoordsLinearEquiv (toHSCoordsLinearEquiv (ℋ := ℋ) T) (i, j) =
    LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
      (hsOrthonormalBasis (ℋ := ℋ)).toBasis
      ((hsLinearMapEquiv (ℋ := ℋ)) T) i j
  let f : HSCoordFun ℋ := fun p =>
    LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
      (hsOrthonormalBasis (ℋ := ℋ)).toBasis
      ((hsLinearMapEquiv (ℋ := ℋ)) T) p.1 p.2
  have h : hsCoordsLinearEquiv (toHSCoordsLinearEquiv (ℋ := ℋ) T) = f := by
    simp [toHSCoordsLinearEquiv, matrixToCoords, matrixToFun, f]
    rfl
  have hEval := congrArg (fun g : HSCoordFun ℋ => g (i, j)) h
  simpa [f] using hEval


-- @@ L150-152 verbatim
instance : NormedAddCommGroup (HSOp ℋ) :=
  NormedAddCommGroup.induced (HSOp ℋ) (HSCoords ℋ)
    (toHSCoordsLinearEquiv (ℋ := ℋ)) (toHSCoordsLinearEquiv (ℋ := ℋ)).injective


-- @@ L154-155 verbatim
instance : NormedSpace ℂ (HSOp ℋ) :=
  NormedSpace.induced ℂ (HSOp ℋ) (HSCoords ℋ) (toHSCoordsLinearEquiv (ℋ := ℋ))


-- @@ L157-158 verbatim
instance : Inner ℂ (HSOp ℋ) where
  inner T S := inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) T) (toHSCoordsLinearEquiv (ℋ := ℋ) S)


-- @@ L160-186 verbatim
instance : InnerProductSpace ℂ (HSOp ℋ) where
  norm_sq_eq_re_inner T := by
    change ‖toHSCoordsLinearEquiv (ℋ := ℋ) T‖ ^ 2 =
      Complex.re (inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) T)
        (toHSCoordsLinearEquiv (ℋ := ℋ) T))
    simpa using
      (inner_self_eq_norm_sq (𝕜 := ℂ) (toHSCoordsLinearEquiv (ℋ := ℋ) T)).symm
  conj_inner_symm T S := by
    change star (inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) S)
      (toHSCoordsLinearEquiv (ℋ := ℋ) T)) =
      inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) T) (toHSCoordsLinearEquiv (ℋ := ℋ) S)
    simp [inner_conj_symm (toHSCoordsLinearEquiv (ℋ := ℋ) T)
      (toHSCoordsLinearEquiv (ℋ := ℋ) S)]
  add_left T S R := by
    change inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) (T + S))
      (toHSCoordsLinearEquiv (ℋ := ℋ) R) =
      inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) T)
        (toHSCoordsLinearEquiv (ℋ := ℋ) R) +
      inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) S)
        (toHSCoordsLinearEquiv (ℋ := ℋ) R)
    simp [inner_add_left, map_add]
  smul_left T S z := by
    change inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) (z • T))
      (toHSCoordsLinearEquiv (ℋ := ℋ) S) =
      star z * inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) T)
        (toHSCoordsLinearEquiv (ℋ := ℋ) S)
    simp [inner_smul_left, map_smul]


-- @@ L188-196 verbatim
/-- Hilbert-Schmidt coordinates as a linear isometry. -/
noncomputable def toHSCoordsLinearIsometryEquiv :
    HSOp ℋ ≃ₗᵢ[ℂ] HSCoords ℋ :=
  LinearEquiv.isometryOfInner (toHSCoordsLinearEquiv (ℋ := ℋ)) <| by
    intro T S
    change inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) T)
      (toHSCoordsLinearEquiv (ℋ := ℋ) S) =
      inner ℂ T S
    rfl


-- @@ L198-204 verbatim
instance : CompleteSpace (HSOp ℋ) :=
  let e : HSOp ℋ ≃ HSCoords ℋ :=
    (toHSCoordsLinearIsometryEquiv.toContinuousLinearEquiv.toLinearEquiv.toEquiv)
  (completeSpace_congr (e := e) <| by
    exact
      (toHSCoordsLinearIsometryEquiv.toContinuousLinearEquiv.isUniformEmbedding)).2
    inferInstance


-- @@ L206-208 verbatim
instance : ContinuousSMul ℂ (HSOp ℋ) :=
  (toHSCoordsLinearIsometryEquiv (ℋ := ℋ)).isometry.isUniformInducing.isInducing.continuousSMul
    continuous_id fun {c x} => map_smul (toHSCoordsLinearEquiv (ℋ := ℋ)) c x


-- @@ L210-211 verbatim
/-- Reinterpret an operator as an element of the Hilbert-Schmidt operator space. -/
abbrev ofOp (T : L ℋ) : HSOp ℋ := T


-- @@ L213-214 verbatim
/-- Forget the Hilbert-Schmidt structure and recover the underlying operator. -/
abbrev toOp (T : HSOp ℋ) : L ℋ := T


-- @@ L216-221 verbatim
/-- Left multiplication on the Hilbert-Schmidt operator space. -/
noncomputable def leftMulHS (A : L ℋ) : HSOp ℋ →L[ℂ] HSOp ℋ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => ofOp (A * toOp T)
      map_add' := fun T S => mul_add A (toOp T) (toOp S)
      map_smul' := fun z T => mul_smul_comm z A (toOp T) }


-- @@ L223-228 verbatim
/-- Right multiplication on the Hilbert-Schmidt operator space. -/
noncomputable def rightMulHS (B : L ℋ) : HSOp ℋ →L[ℂ] HSOp ℋ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun T => ofOp (toOp T * B)
      map_add' := fun T S => add_mul (toOp T) (toOp S) B
      map_smul' := fun z T => smul_mul_assoc z (toOp T) B }


-- @@ L230-232 verbatim
omit [CompleteSpace ℋ] in
@[simp] lemma leftMulHS_apply (A : L ℋ) (T : HSOp ℋ) :
    toOp (leftMulHS (ℋ := ℋ) A T) = A * toOp T := rfl


-- @@ L234-236 verbatim
omit [CompleteSpace ℋ] in
@[simp] lemma rightMulHS_apply (B : L ℋ) (T : HSOp ℋ) :
    toOp (rightMulHS (ℋ := ℋ) B T) = toOp T * B := rfl


-- @@ L238-243 verbatim
set_option backward.isDefEq.respectTransparency false in
omit [CompleteSpace ℋ] in
@[simp] lemma leftMulHS_mul (A B : L ℋ) :
    leftMulHS (ℋ := ℋ) (A * B) = leftMulHS (ℋ := ℋ) A * leftMulHS (ℋ := ℋ) B := by
  ext T
  simp [mul_assoc]


-- @@ L245-250 verbatim
set_option backward.isDefEq.respectTransparency false in
omit [CompleteSpace ℋ] in
@[simp] lemma rightMulHS_mul (A B : L ℋ) :
    rightMulHS (ℋ := ℋ) (A * B) = rightMulHS (ℋ := ℋ) B * rightMulHS (ℋ := ℋ) A := by
  ext T
  simp [mul_assoc]


-- @@ L252-256 verbatim
omit [CompleteSpace ℋ] in
@[simp] lemma leftMulHS_one :
    leftMulHS (ℋ := ℋ) (1 : L ℋ) = (1 : L (HSOp ℋ)) := by
  ext T
  simp


-- @@ L258-262 verbatim
omit [CompleteSpace ℋ] in
@[simp] lemma rightMulHS_one :
    rightMulHS (ℋ := ℋ) (1 : L ℋ) = (1 : L (HSOp ℋ)) := by
  ext T
  simp


-- @@ L264-269 verbatim
set_option backward.isDefEq.respectTransparency false in
omit [CompleteSpace ℋ] in
lemma leftMulHS_rightMulHS_commute (A B : L ℋ) :
    Commute (leftMulHS (ℋ := ℋ) A) (rightMulHS (ℋ := ℋ) B) := by
  ext T
  simp [mul_assoc]


-- @@ L271-301 verbatim
omit [CompleteSpace ℋ] in
private lemma hsInner_eq_pairSum (X Y : L ℋ) :
    inner ℂ (ofOp X) (ofOp Y) =
      ∑ p : HSIndex ℋ × HSIndex ℋ,
        LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
          (hsOrthonormalBasis (ℋ := ℋ)).toBasis Y.toLinearMap p.1 p.2 *
        star
          (LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
            (hsOrthonormalBasis (ℋ := ℋ)).toBasis X.toLinearMap p.1 p.2) := by
  have hXfun :
      ((toHSCoordsLinearEquiv (ℋ := ℋ) (ofOp X) : HSCoords ℋ).ofLp : HSCoordFun ℋ) =
        fun p =>
          LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
            (hsOrthonormalBasis (ℋ := ℋ)).toBasis X.toLinearMap p.1 p.2 := by
    funext p
    change (toHSCoordsLinearEquiv (ℋ := ℋ) (ofOp X) :
      EuclideanSpace ℂ (HSIndex ℋ × HSIndex ℋ)) p = _
    exact toHSCoordsLinearEquiv_apply_apply (ℋ := ℋ) (T := ofOp X) p.1 p.2
  have hYfun :
      ((toHSCoordsLinearEquiv (ℋ := ℋ) (ofOp Y) : HSCoords ℋ).ofLp : HSCoordFun ℋ) =
        fun p =>
          LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
            (hsOrthonormalBasis (ℋ := ℋ)).toBasis Y.toLinearMap p.1 p.2 := by
    funext p
    change (toHSCoordsLinearEquiv (ℋ := ℋ) (ofOp Y) :
      EuclideanSpace ℂ (HSIndex ℋ × HSIndex ℋ)) p = _
    exact toHSCoordsLinearEquiv_apply_apply (ℋ := ℋ) (T := ofOp Y) p.1 p.2
  change inner ℂ (toHSCoordsLinearEquiv (ℋ := ℋ) (ofOp X))
      (toHSCoordsLinearEquiv (ℋ := ℋ) (ofOp Y)) = _
  rw [EuclideanSpace.inner_eq_star_dotProduct, hXfun, hYfun]
  simp [dotProduct]


-- @@ L303-343 verbatim
private lemma trace_star_mul_eq_pairSum (X Y : L ℋ) :
    LinearMap.trace ℂ ℋ ((star X * Y).toLinearMap) =
      ∑ p : HSIndex ℋ × HSIndex ℋ,
        LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
          (hsOrthonormalBasis (ℋ := ℋ)).toBasis Y.toLinearMap p.1 p.2 *
        star
          (LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
            (hsOrthonormalBasis (ℋ := ℋ)).toBasis X.toLinearMap p.1 p.2) := by
  let b := hsOrthonormalBasis (ℋ := ℋ)
  calc
    LinearMap.trace ℂ ℋ ((star X * Y).toLinearMap)
        = ∑ i : HSIndex ℋ, ∑ j : HSIndex ℋ,
            LinearMap.toMatrix b.toBasis b.toBasis Y.toLinearMap j i *
              star (LinearMap.toMatrix b.toBasis b.toBasis X.toLinearMap j i) := by
            rw [LinearMap.trace_eq_sum_inner ((star X * Y).toLinearMap) b]
            apply Finset.sum_congr rfl
            intro i hi
            calc
              inner ℂ (b i) (((star X * Y).toLinearMap) (b i)) = inner ℂ (X (b i)) (Y (b i)) := by
                simpa [ContinuousLinearMap.star_eq_adjoint] using
                  (ContinuousLinearMap.adjoint_inner_right (A := X) (x := b i) (y := Y (b i)))
              _ = ∑ j : HSIndex ℋ, inner ℂ (X (b i)) (b j) * inner ℂ (b j) (Y (b i)) := by
                symm
                exact OrthonormalBasis.sum_inner_mul_inner b (X (b i)) (Y (b i))
              _ = ∑ j : HSIndex ℋ,
                    LinearMap.toMatrix b.toBasis b.toBasis Y.toLinearMap j i *
                      star (LinearMap.toMatrix b.toBasis b.toBasis X.toLinearMap j i) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  simp [LinearMap.toMatrix_apply, OrthonormalBasis.repr_apply_apply, mul_comm]
    _ = ∑ p : HSIndex ℋ × HSIndex ℋ,
          LinearMap.toMatrix b.toBasis b.toBasis Y.toLinearMap p.1 p.2 *
            star (LinearMap.toMatrix b.toBasis b.toBasis X.toLinearMap p.1 p.2) := by
          rw [Finset.sum_comm]
          symm
          simpa [Finset.univ_product_univ] using
            (Finset.sum_product' (s := (Finset.univ : Finset (HSIndex ℋ)))
              (t := (Finset.univ : Finset (HSIndex ℋ)))
              (f := fun j i =>
                LinearMap.toMatrix b.toBasis b.toBasis Y.toLinearMap j i *
                  star (LinearMap.toMatrix b.toBasis b.toBasis X.toLinearMap j i)))


-- @@ L345-358 verbatim
lemma hsInner_eq_trace (X Y : L ℋ) :
    inner ℂ (ofOp X) (ofOp Y) = LinearMap.trace ℂ ℋ ((star X * Y).toLinearMap) := by
  calc
    inner ℂ (ofOp X) (ofOp Y)
        = ∑ p : HSIndex ℋ × HSIndex ℋ,
            LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
              (hsOrthonormalBasis (ℋ := ℋ)).toBasis Y.toLinearMap p.1 p.2 *
            star
              (LinearMap.toMatrix (hsOrthonormalBasis (ℋ := ℋ)).toBasis
                (hsOrthonormalBasis (ℋ := ℋ)).toBasis X.toLinearMap p.1 p.2) :=
          hsInner_eq_pairSum (X := X) (Y := Y)
    _ = LinearMap.trace ℂ ℋ ((star X * Y).toLinearMap) := by
          symm
          exact trace_star_mul_eq_pairSum (X := X) (Y := Y)


-- @@ L360-363 verbatim
lemma re_hsInner_eq_traceRe (X Y : L ℋ) :
    Complex.re (inner ℂ (ofOp X) (ofOp Y)) =
      Complex.re (LinearMap.trace ℂ ℋ ((star X * Y).toLinearMap)) := by
  simpa using congrArg Complex.re (hsInner_eq_trace (X := X) (Y := Y))


-- @@ L365-375 verbatim
@[simp] lemma leftMulHS_star (A : L ℋ) :
    star (leftMulHS (ℋ := ℋ) A) = leftMulHS (ℋ := ℋ) (star A) := by
  rw [eq_comm, ContinuousLinearMap.star_eq_adjoint]
  refine (ContinuousLinearMap.eq_adjoint_iff
    (A := leftMulHS (ℋ := ℋ) (star A)) (B := leftMulHS (ℋ := ℋ) A)).2 ?_
  intro X Y
  change inner ℂ (ofOp ((star A) * toOp X)) (ofOp (toOp Y)) =
    inner ℂ (ofOp (toOp X)) (ofOp (A * toOp Y))
  rw [hsInner_eq_trace]
  rw [hsInner_eq_trace]
  simp [mul_assoc]


-- @@ L377-382 verbatim
omit [CompleteSpace ℋ] in
@[simp] lemma leftMulHS_real_smul_one (r : ℝ) :
    leftMulHS (ℋ := ℋ) (r • (1 : L ℋ)) = r • (1 : L (HSOp ℋ)) := by
  ext T
  change ofOp ((r • (1 : L ℋ)) * toOp T) = ofOp (r • toOp T)
  simp [Algebra.smul_def]


-- @@ L384-389 verbatim
omit [CompleteSpace ℋ] in
@[simp] lemma rightMulHS_real_smul_one (r : ℝ) :
    rightMulHS (ℋ := ℋ) (r • (1 : L ℋ)) = r • (1 : L (HSOp ℋ)) := by
  ext T
  change ofOp (toOp T * (r • (1 : L ℋ))) = ofOp (r • toOp T)
  simp [Algebra.smul_def, Algebra.commutes (R := ℝ) (A := L ℋ) r (toOp T)]


-- @@ L391-434 verbatim
lemma leftMulHS_nonneg {A : L ℋ} (hA0 : 0 ≤ A) :
    0 ≤ leftMulHS (ℋ := ℋ) A := by
  have hApos : A.IsPositive := (ContinuousLinearMap.nonneg_iff_isPositive A).1 hA0
  have hA_sa : IsSelfAdjoint A := hApos.isSelfAdjoint
  have hleft_sa : IsSelfAdjoint (leftMulHS (ℋ := ℋ) A) := by
    change star (leftMulHS (ℋ := ℋ) A) = leftMulHS (ℋ := ℋ) A
    simp [hA_sa.star_eq, leftMulHS_star (ℋ := ℋ) A]
  refine (ContinuousLinearMap.nonneg_iff_isPositive _).2 ?_
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro X
  constructor
  · have hsymm :
        ((leftMulHS (ℋ := ℋ) A : HSOp ℋ →L[ℂ] HSOp ℋ) : HSOp ℋ →ₗ[ℂ] HSOp ℋ).IsSymmetric :=
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric).mp hleft_sa
    simpa using LinearMap.IsSymmetric.coe_re_inner_apply_self hsymm X
  · let b := hsOrthonormalBasis (ℋ := ℋ)
    have htrace :
        Complex.re (inner ℂ (leftMulHS (ℋ := ℋ) A X) X) =
          ∑ i : HSIndex ℋ, Complex.re (inner ℂ (A (toOp X (b i))) (toOp X (b i))) := by
      calc
        Complex.re (inner ℂ (leftMulHS (ℋ := ℋ) A X) X)
            = Complex.re (LinearMap.trace ℂ ℋ
                ((star (A * toOp X) * toOp X).toLinearMap)) := by
                  simpa [leftMulHS_apply] using
                    re_hsInner_eq_traceRe (ℋ := ℋ) (X := A * toOp X) (Y := toOp X)
        _ = ∑ i : HSIndex ℋ,
              Complex.re (inner ℂ (b i)
                (((star (A * toOp X) * toOp X).toLinearMap) (b i))) := by
              rw [LinearMap.trace_eq_sum_inner ((star (A * toOp X) * toOp X).toLinearMap) b]
              simp
        _ = ∑ i : HSIndex ℋ,
              Complex.re (inner ℂ (A (toOp X (b i))) (toOp X (b i))) := by
              apply Finset.sum_congr rfl
              intro i hi
              exact congrArg Complex.re <| by
                simpa [ContinuousLinearMap.star_eq_adjoint, mul_assoc] using
                  (ContinuousLinearMap.adjoint_inner_right
                  (A := A * toOp X) (x := b i) (y := toOp X (b i)))
    have htrace' :
        RCLike.re (inner ℂ (leftMulHS (ℋ := ℋ) A X) X) =
          ∑ i : HSIndex ℋ, Complex.re (inner ℂ (A (toOp X (b i))) (toOp X (b i))) := by
      simpa using htrace
    rw [htrace']
    exact Finset.sum_nonneg fun i _ => hApos.re_inner_nonneg_left (toOp X (b i))


-- @@ L436-444 verbatim
lemma leftMulHS_le_leftMulHS {A B : L ℋ} (hAB : A ≤ B) :
    leftMulHS (ℋ := ℋ) A ≤ leftMulHS (ℋ := ℋ) B := by
  have hnonneg : 0 ≤ leftMulHS (ℋ := ℋ) (B - A) :=
    leftMulHS_nonneg (ℋ := ℋ) (sub_nonneg.mpr hAB)
  have hsub :
      leftMulHS (ℋ := ℋ) B - leftMulHS (ℋ := ℋ) A =
        leftMulHS (ℋ := ℋ) (B - A) := by
    ext T; exact congrArg ofOp (sub_mul B A (toOp T)).symm
  exact sub_nonneg.mp (by simpa [hsub] using hnonneg)


-- @@ L446-465 verbatim
lemma leftMulHS_pdSet [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]
    {A : L ℋ} (hA : A ∈ GeneralizedPerspectiveFunction.pdSet (ℋ := ℋ)) :
    leftMulHS (ℋ := ℋ) A ∈ GeneralizedPerspectiveFunction.pdSet (ℋ := HSOp ℋ) := by
  rcases hA with ⟨hA_sa, hA_spec⟩
  have hleft_sa : IsSelfAdjoint (leftMulHS (ℋ := ℋ) A) := by
    change star (leftMulHS (ℋ := ℋ) A) = leftMulHS (ℋ := ℋ) A
    simp [hA_sa.star_eq, leftMulHS_star (ℋ := ℋ) A]
  let : Nontrivial (HSOp ℋ) := by
    delta HSOp
    infer_instance
  let : Nontrivial (L (HSOp ℋ)) := inferInstance
  refine ⟨?_, ?_⟩
  · exact hleft_sa
  · rcases (CFC.exists_pos_algebraMap_le_iff (A := L ℋ) (a := A) (ha := hA_sa)).2 hA_spec
      with ⟨r, hr, hrA⟩
    refine (CFC.exists_pos_algebraMap_le_iff
      (A := L (HSOp ℋ)) (a := leftMulHS (ℋ := ℋ) A) (ha := hleft_sa)).1 ?_
    refine ⟨r, hr, ?_⟩
    simpa [Algebra.algebraMap_eq_smul_one, leftMulHS_real_smul_one (r := r)] using
      leftMulHS_le_leftMulHS (ℋ := ℋ) hrA


-- @@ L467-481 verbatim
@[simp] lemma rightMulHS_star (A : L ℋ) :
    star (rightMulHS (ℋ := ℋ) A) = rightMulHS (ℋ := ℋ) (star A) := by
  rw [eq_comm, ContinuousLinearMap.star_eq_adjoint]
  refine (ContinuousLinearMap.eq_adjoint_iff
    (A := rightMulHS (ℋ := ℋ) (star A)) (B := rightMulHS (ℋ := ℋ) A)).2 ?_
  intro X Y
  change inner ℂ (ofOp (toOp X * star A)) (ofOp (toOp Y)) =
    inner ℂ (ofOp (toOp X)) (ofOp (toOp Y * A))
  rw [hsInner_eq_trace]
  rw [hsInner_eq_trace]
  rw [star_mul, star_star, mul_assoc]
  symm
  simpa [mul_assoc] using
    (LinearMap.trace_mul_cycle (R := ℂ) (M := ℋ)
      (f := (star (toOp X)).toLinearMap) (g := (toOp Y).toLinearMap) (h := A.toLinearMap))


-- @@ L483-496 verbatim
/-- Left multiplication as a real `⋆`-algebra homomorphism on the Hilbert-Schmidt operator space. -/
noncomputable def leftMulHSStarAlgHom : L ℋ →⋆ₐ[ℝ] L (HSOp ℋ) where
  toFun := leftMulHS (ℋ := ℋ)
  map_one' := leftMulHS_one (ℋ := ℋ)
  map_mul' := leftMulHS_mul (ℋ := ℋ)
  map_zero' := by ext T; exact congrArg ofOp (zero_mul (toOp T))
  map_add' := fun A B => by ext T; exact congrArg ofOp (add_mul A B (toOp T))
  commutes' := by
    intro r
    simp only [Algebra.algebraMap_eq_smul_one]
    exact leftMulHS_real_smul_one (ℋ := ℋ) r
  map_star' := by
    intro A
    simp [leftMulHS_star (ℋ := ℋ) A]


-- @@ L498-519 verbatim
/-- Right multiplication as a real `⋆`-algebra homomorphism out of the opposite algebra. -/
noncomputable def rightMulHSStarAlgHom : (L ℋ)ᵐᵒᵖ →⋆ₐ[ℝ] L (HSOp ℋ) where
  toFun := fun A => rightMulHS (ℋ := ℋ) (MulOpposite.unop A)
  map_one' := by simp [rightMulHS_one (ℋ := ℋ)]
  map_mul' := by intro A B; ext T; simp [rightMulHS_apply]
  map_zero' := by
    ext T
    change ofOp (toOp T * MulOpposite.unop (0 : (L ℋ)ᵐᵒᵖ)) = ofOp (0 : L ℋ)
    congr 1; simp
  map_add' := fun A B => by
    ext T
    change ofOp (toOp T * MulOpposite.unop (A + B)) =
      ofOp (toOp T * MulOpposite.unop A + toOp T * MulOpposite.unop B)
    congr 1; simp [MulOpposite.unop_add, mul_add]
  commutes' := by
    intro r
    show rightMulHS (ℋ := ℋ) (MulOpposite.unop (MulOpposite.op (r • (1 : L ℋ)))) =
      r • (1 : L (HSOp ℋ))
    simp [rightMulHS_real_smul_one (ℋ := ℋ) r]
  map_star' := by
    intro A
    simp [rightMulHS_star (ℋ := ℋ) (MulOpposite.unop A)]


-- @@ L521-523 verbatim
@[simp] theorem rightMulHSStarAlgHom_apply (A : (L ℋ)ᵐᵒᵖ) :
    rightMulHSStarAlgHom (ℋ := ℋ) A = rightMulHS (ℋ := ℋ) (MulOpposite.unop A) :=
  rfl


-- @@ L525-542 verbatim
/-- The `⋆`-algebra hom sending `A` to `op (star A)`. On selfadjoint operators this is just `op`. -/
noncomputable def opStarHSStarAlgHom : L ℋ →⋆ₐ[ℝ] (L ℋ)ᵐᵒᵖ where
  toFun := fun A => MulOpposite.op (star A)
  map_one' := by simp
  map_mul' := by
    intro A B
    simp [star_mul]
  map_zero' := by simp
  map_add' := by
    intro A B
    simp
  commutes' := by
    intro r
    apply congrArg MulOpposite.op
    simp [Algebra.algebraMap_eq_smul_one]
  map_star' := by
    intro A
    simp


-- @@ L544-553 verbatim
private noncomputable def opStarHSAlgEquiv : L ℋ ≃ₐ[ℝ] (L ℋ)ᵐᵒᵖ where
  toFun A := MulOpposite.op (star A)
  invFun A := star (MulOpposite.unop A)
  left_inv A := by simp
  right_inv A := by simp
  map_mul' A B := by simp [star_mul]
  map_add' A B := by simp
  commutes' r := by
    apply congrArg MulOpposite.op
    simp [Algebra.algebraMap_eq_smul_one]


-- @@ L555-558 verbatim
omit [FiniteDimensional ℂ ℋ] in
lemma op_isSelfAdjoint (A : L ℋ) (hA : IsSelfAdjoint A) :
    IsSelfAdjoint (MulOpposite.op A : (L ℋ)ᵐᵒᵖ) := by
  exact congrArg MulOpposite.op hA.star_eq


-- @@ L560-572 verbatim
private noncomputable def opStarHSLinearMap : L ℋ →ₗ[ℝ] (L ℋ)ᵐᵒᵖ where
  toFun := fun A => MulOpposite.op (star A)
  map_add' A B := by simp
  map_smul' r A := by
    apply MulOpposite.unop_injective
    rw [MulOpposite.unop_op, MulOpposite.unop_smul, MulOpposite.unop_op]
    rw [Algebra.smul_def, star_mul]
    show star A * star ((algebraMap ℝ (L ℋ)) r) = (algebraMap ℝ (L ℋ)) r * star A
    have hstar : star ((algebraMap ℝ (L ℋ)) r) = (algebraMap ℝ (L ℋ)) r := by
      rw [Algebra.algebraMap_eq_smul_one, star_smul, star_one]
      simp
    rw [hstar]
    simpa using (Algebra.commutes (R := ℝ) (A := L ℋ) r (star A)).symm


-- @@ L574-580 verbatim
private noncomputable def leftMulHSLinearMap : L ℋ →ₗ[ℝ] L (HSOp ℋ) where
  toFun := leftMulHS (ℋ := ℋ)
  map_add' A B := by ext T; exact congrArg ofOp (add_mul A B (toOp T))
  map_smul' r A := by
    ext T
    show ((r • A) * toOp T : L ℋ) = r • (A * toOp T)
    rw [smul_mul_assoc]


-- @@ L582-594 verbatim
private noncomputable def rightMulHSLinearMap : (L ℋ)ᵐᵒᵖ →ₗ[ℝ] L (HSOp ℋ) where
  toFun := fun A => rightMulHS (ℋ := ℋ) (MulOpposite.unop A)
  map_add' A B := by
    ext T
    change ofOp (toOp T * MulOpposite.unop (A + B)) =
      ofOp (toOp T * MulOpposite.unop A + toOp T * MulOpposite.unop B)
    congr 1; simp [MulOpposite.unop_add, mul_add]
  map_smul' r A := by
    ext T
    change ofOp (toOp T * MulOpposite.unop (r • A)) =
      ofOp (r • (toOp T * MulOpposite.unop A))
    congr 1
    rw [MulOpposite.unop_smul, mul_smul_comm]


-- @@ L596-602 verbatim
omit [FiniteDimensional ℂ ℋ] in
lemma spectrum_op_eq [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]
    (A : L ℋ) (hA : IsSelfAdjoint A) :
    spectrum ℝ (MulOpposite.op A : (L ℋ)ᵐᵒᵖ) = spectrum ℝ A := by
  have hopA : IsSelfAdjoint (MulOpposite.op A : (L ℋ)ᵐᵒᵖ) := op_isSelfAdjoint (A := A) hA
  simpa [opStarHSAlgEquiv, hA.star_eq, hopA.star_eq] using
    (AlgEquiv.spectrum_eq (opStarHSAlgEquiv (ℋ := ℋ)) A)


-- @@ L604-626 verbatim
lemma cfc_op_eq_op_cfc [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
    [ContinuousFunctionalCalculus ℝ ((L ℋ)ᵐᵒᵖ) IsSelfAdjoint] [Nontrivial (L ℋ)]
    (f : ℝ → ℝ) (A : L ℋ) (hA : IsSelfAdjoint A)
    (hf : ContinuousOn f (spectrum ℝ A)) :
    cfc (R := ℝ) (A := (L ℋ)ᵐᵒᵖ) (p := IsSelfAdjoint) f (MulOpposite.op A) =
      MulOpposite.op (cfcR f A) := by
  let φ : L ℋ →⋆ₐ[ℝ] (L ℋ)ᵐᵒᵖ := opStarHSStarAlgHom (ℋ := ℋ)
  have hφ : Continuous φ := by
    exact
      (LinearMap.continuous_of_finiteDimensional (opStarHSLinearMap (ℋ := ℋ)))
  have hopA : IsSelfAdjoint (MulOpposite.op A : (L ℋ)ᵐᵒᵖ) := op_isSelfAdjoint (A := A) hA
  have hφA : IsSelfAdjoint (φ A) := hA.map φ
  have hcfcA :
      IsSelfAdjoint (cfc (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint) f A) := by
    simp [IsSelfAdjoint.cfc (f := f) (a := A)]
  have hopcfcA :
      IsSelfAdjoint
        (MulOpposite.op (cfc (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint) f A) : (L ℋ)ᵐᵒᵖ) :=
    op_isSelfAdjoint (A := cfc (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint) f A) hcfcA
  have hmap := StarAlgHom.map_cfc (φ := φ) (f := f) (a := A)
    (hf := hf) (hφ := hφ) (ha := hA) (hφa := hφA)
  simpa [φ, opStarHSStarAlgHom, cfcR, hA.star_eq, hopA.star_eq, hcfcA.star_eq,
    hopcfcA.star_eq] using hmap.symm


-- @@ L628-640 verbatim
lemma leftMulHS_cfcR [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint] [Nontrivial (L ℋ)]
    (f : ℝ → ℝ) (A : L ℋ) (hA : IsSelfAdjoint A)
    (hf : ContinuousOn f (spectrum ℝ A)) :
    leftMulHS (ℋ := ℋ) (cfcR f A) =
      cfcR (ℋ := HSOp ℋ) f (leftMulHS (ℋ := ℋ) A) := by
  let φ : L ℋ →⋆ₐ[ℝ] L (HSOp ℋ) := leftMulHSStarAlgHom (ℋ := ℋ)
  have hφ : Continuous φ := by
    exact
      (LinearMap.continuous_of_finiteDimensional (leftMulHSLinearMap (ℋ := ℋ)))
  have hφA : IsSelfAdjoint (φ A) := hA.map φ
  have hmap := StarAlgHom.map_cfc (φ := φ) (f := f) (a := A)
    (hf := hf) (hφ := hφ) (ha := hA) (hφa := hφA)
  exact hmap


-- @@ L642-661 verbatim
lemma rightMulHS_cfcR [ContinuousFunctionalCalculus ℝ (L ℋ) IsSelfAdjoint]
    [ContinuousFunctionalCalculus ℝ ((L ℋ)ᵐᵒᵖ) IsSelfAdjoint] [Nontrivial (L ℋ)]
    (f : ℝ → ℝ) (A : L ℋ) (hA : IsSelfAdjoint A)
    (hf : ContinuousOn f (spectrum ℝ A)) :
    rightMulHS (ℋ := ℋ) (cfcR f A) =
      cfcR (ℋ := HSOp ℋ) f (rightMulHS (ℋ := ℋ) A) := by
  let φ : (L ℋ)ᵐᵒᵖ →⋆ₐ[ℝ] L (HSOp ℋ) := rightMulHSStarAlgHom (ℋ := ℋ)
  have hφ : Continuous φ := by
    exact
      (LinearMap.continuous_of_finiteDimensional (rightMulHSLinearMap (ℋ := ℋ)))
  have hopA : IsSelfAdjoint (MulOpposite.op A : (L ℋ)ᵐᵒᵖ) := op_isSelfAdjoint (A := A) hA
  have hφA : IsSelfAdjoint (φ (MulOpposite.op A)) := hopA.map φ
  have hmap := StarAlgHom.map_cfc (φ := φ) (f := f) (a := MulOpposite.op A)
    (hf := by simpa [spectrum_op_eq (A := A) hA] using hf)
    (hφ := hφ) (ha := hopA) (hφa := hφA)
  have hopcfc :
      cfc (R := ℝ) (A := (L ℋ)ᵐᵒᵖ) (p := IsSelfAdjoint) f (MulOpposite.op A) =
        MulOpposite.op (cfcR f A) :=
    cfc_op_eq_op_cfc (ℋ := ℋ) f A hA hf
  simpa [φ, cfcR, rightMulHSStarAlgHom, hopcfc] using hmap


-- @@ L663-663 verbatim
end


-- @@ L665-665 verbatim
end HilbertSchmidtOperatorSpace
