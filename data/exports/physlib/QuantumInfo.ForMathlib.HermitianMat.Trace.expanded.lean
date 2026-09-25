/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.ForMathlib.HermitianMat.Reindex


-- @@ L10-23 verbatim
/-! # Trace of Hermitian Matrices

While the trace of a Hermitian matrix is, in informal math, typically just "the same as" a trace of
a matrix that happens to be Hermitian - it is a real number, not a complex number. Or more generally,
it is a self-adjoint element of the base `StarAddMonoid`.

Working directly with `Matrix.trace` then means that there would be constant casts between rings,
chasing imaginary parts and inequalities and so on. By defining `HermitianMat.trace` as its own
operation, we encapsulate the mess and give a clean interface.

The `IsMaximalSelfAdjoint` class is used so that (for example) for matrices over ℤ or ℝ,
`HermitianMat.trace` works as well and is in fact defeq to `Matrix.trace`. For ℂ or `RCLike`,
it uses the real part.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
namespace HermitianMat


-- @@ L29-29 verbatim
variable {R n m α : Type*} [Star R] [TrivialStar R] [Fintype n] [Fintype m]


-- @@ L31-31 verbatim
section star

-- @@ L32-32 verbatim
variable [AddGroup α] [StarAddMonoid α] [CommSemiring R] [Semiring α] [Algebra R α] [IsMaximalSelfAdjoint R α]


-- @@ L34-40 verbatim
set_option linter.overlappingInstances false in
/-- The trace of the matrix. This requires a `IsMaximalSelfAdjoint R α` instance, and then maps from
  `HermitianMat n α` to `R`. This means that the trace of (say) a `HermitianMat n ℤ` gives values in ℤ,
  but that the trace of a `HermitianMat n ℂ` gives values in ℝ. The fact that traces are "automatically"
  real reduces coercions down the line. -/
def trace (A : HermitianMat n α) : R :=
  IsMaximalSelfAdjoint.selfadjMap (A.mat.trace)


-- @@ L42-47 verbatim
set_option linter.overlappingInstances false in
/-- `HermitianMat.trace` reduces to `Matrix.trace` in the algebra.-/
theorem trace_eq_trace (A : HermitianMat n α) : algebraMap R α A.trace = Matrix.trace A.mat := by
  rw [trace, Matrix.trace, map_sum, map_sum]
  congr! 1
  exact IsMaximalSelfAdjoint.selfadj_algebra (Matrix.IsHermitian.apply A.H _ _)


-- @@ L49-53 verbatim
set_option linter.overlappingInstances false in
variable [StarModule R α] in
@[simp]
theorem trace_smul (A : HermitianMat n α) (r : R) : (r • A).trace = r * A.trace := by
  simp [trace, IsMaximalSelfAdjoint.selfadj_smul]


-- @@ L55-55 verbatim
end star

-- @@ L56-56 verbatim
section semiring

-- @@ L57-57 verbatim
variable [CommSemiring R] [Ring α] [StarAddMonoid α] [Algebra R α] [IsMaximalSelfAdjoint R α]


-- @@ L59-61 verbatim
@[simp]
theorem trace_zero : (0 : HermitianMat n α).trace = 0 := by
  simp [trace]


-- @@ L63-65 verbatim
@[simp]
theorem trace_add (A B : HermitianMat n α) : (A + B).trace = A.trace + B.trace := by
  simp [trace]


-- @@ L67-67 verbatim
end semiring

-- @@ L68-68 verbatim
section ring


-- @@ L70-70 verbatim
variable [CommRing R] [Ring α] [StarAddMonoid α] [Algebra R α] [IsMaximalSelfAdjoint R α]

-- @@ L71-73 verbatim
@[simp]
theorem trace_neg (A : HermitianMat n α) : (-A).trace = -A.trace := by
  simp [trace]


-- @@ L75-77 verbatim
@[simp]
theorem trace_sub (A B : HermitianMat n α) : (A - B).trace = A.trace - B.trace := by
  simp [trace]


-- @@ L79-79 verbatim
end ring

-- @@ L80-80 verbatim
section starring


-- @@ L82-84 verbatim
variable [CommRing R] [CommRing α] [StarRing α] [Algebra R α] [IsMaximalSelfAdjoint R α]

--Move somewhere else? Needs to import `IsMaximalSelfAdjoint`, so maybe just here.

-- @@ L85-87 verbatim
theorem _root_.Matrix.IsHermitian.isSelfAdjoint_trace {A : Matrix n n α} (hA : A.IsHermitian) :
    IsSelfAdjoint A.trace := by
  simp [Matrix.trace, IsSelfAdjoint, ← Matrix.star_apply, show star A = A from hA]


-- @@ L89-89 verbatim
variable (A : HermitianMat m α) (B : HermitianMat n α)


-- @@ L91-100 expanded
@[simp]
theorem trace_kronecker [FaithfulSMul R α] :
    (HermitianMat.kronecker A B).trace = A.trace * B.trace :=
  by
  apply FaithfulSMul.algebraMap_injective R α
  simp only [trace, kronecker_mat]
  rw [Matrix.trace_kronecker A.mat B.mat]
  simp only [map_mul]
  have hA := A.H.isSelfAdjoint_trace
  have hB := B.H.isSelfAdjoint_trace
  open IsMaximalSelfAdjoint in
    rw [selfadj_algebra hA, selfadj_algebra hB, selfadj_algebra (hA.mul hB)]


-- @@ L102-102 verbatim
end starring


-- @@ L104-104 verbatim
section trivialstar


-- @@ L106-106 verbatim
variable [Star α] [TrivialStar α] [CommSemiring α]


-- @@ L108-112 verbatim
/-- `HermitianMat.trace` reduces to `Matrix.trace` when the elements are a `TrivialStar`. -/
@[simp]
theorem trace_eq_trace_trivial (A : HermitianMat n ℝ) : A.trace = A.mat.trace := by
  rw [← trace_eq_trace]
  rfl


-- @@ L114-114 verbatim
end trivialstar


-- @@ L116-116 verbatim
section RCLike


-- @@ L118-118 verbatim
variable {n m 𝕜 : Type*} [Fintype n] [Fintype m] [RCLike 𝕜]


-- @@ L120-121 verbatim
theorem trace_eq_re_trace (A : HermitianMat n 𝕜) : A.trace = RCLike.re A.mat.trace := by
  rfl


-- @@ L123-125 verbatim
@[simp]
theorem trace_one [DecidableEq n] : (1 : HermitianMat n 𝕜).trace = Fintype.card n := by
  simp [trace_eq_re_trace]


-- @@ L127-132 verbatim
/-- `HermitianMat.trace` reduces to `Matrix.trace` when the elements are `RCLike`. -/
@[simp]
theorem trace_eq_trace_rc (A : HermitianMat n 𝕜) : A.trace = A.mat.trace := by
  rw [trace, Matrix.trace, map_sum, RCLike.ofReal_sum]
  congr 1
  exact Matrix.IsHermitian.coe_re_diag A.H


-- @@ L134-137 verbatim
theorem trace_diagonal {T : Type*} [Fintype T] [DecidableEq T] (f : T → ℝ) :
    (diagonal 𝕜 f).trace = ∑ i, f i := by
  rw [trace_eq_re_trace]
  simp [HermitianMat.diagonal, Matrix.trace]


-- @@ L139-145 verbatim
theorem sum_eigenvalues_eq_trace [DecidableEq n] (A : HermitianMat n 𝕜) :
    ∑ i, A.H.eigenvalues i = A.trace := by
  convert! congrArg RCLike.re A.H.sum_eigenvalues_eq_trace
  rw [RCLike.ofReal_re]

--Proving that traces are 0 or 1 is common enough that we have a convenience lemma here for turning
--statements about HermitianMat traces into Matrix traces.

-- @@ L146-148 verbatim
theorem trace_eq_zero_iff (A : HermitianMat n 𝕜) : A.trace = 0 ↔ A.mat.trace = 0 := by
  rw [← trace_eq_trace_rc]
  exact ⟨mod_cast id, mod_cast id⟩


-- @@ L150-152 verbatim
theorem trace_eq_one_iff (A : HermitianMat n 𝕜) : A.trace = 1 ↔ A.mat.trace = 1 := by
  rw [← trace_eq_trace_rc]
  exact ⟨mod_cast id, mod_cast id⟩


-- @@ L154-158 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp]
theorem trace_reindex (A : HermitianMat n ℂ) (e : n ≃ m) :
    (A.reindex e).trace = A.trace := by
  simp [reindex, trace_eq_re_trace]


-- @@ L160-160 verbatim
end RCLike

-- @@ L161-161 verbatim
section partialTrace

-- @@ L162-162 verbatim
section addCommGroup


-- @@ L164-164 verbatim
variable [AddCommGroup α] [StarAddMonoid α]

-- @@ L165-165 verbatim
omit [Fintype n]


-- @@ L167-168 verbatim
def traceLeft (A : HermitianMat (m × n) α) : HermitianMat n α :=
  ⟨A.mat.traceLeft, A.H.traceLeft⟩


-- @@ L170-171 verbatim
def traceRight (A : HermitianMat (m × n) α) : HermitianMat m α :=
  ⟨A.mat.traceRight, A.H.traceRight⟩


-- @@ L173-173 verbatim
variable (A B : HermitianMat (m × n) α)


-- @@ L175-177 verbatim
@[simp]
theorem traceLeft_mat : A.traceLeft.mat = A.mat.traceLeft := by
  rfl


-- @@ L179-181 verbatim
@[simp]
theorem traceLeft_add : (A + B).traceLeft = A.traceLeft + B.traceLeft := by
  ext1; simp


-- @@ L183-185 verbatim
@[simp]
theorem traceLeft_neg : (-A).traceLeft = -A.traceLeft := by
  ext1; simp


-- @@ L187-189 verbatim
@[simp]
theorem traceLeft_sub : (A - B).traceLeft = A.traceLeft - B.traceLeft := by
  ext1; simp


-- @@ L191-191 verbatim
variable (A B : HermitianMat (n × m) α)


-- @@ L193-196 verbatim
@[simp]
theorem traceRight_mat :
    (traceRight A).mat = A.mat.traceRight := by
  rfl


-- @@ L198-200 verbatim
@[simp]
theorem traceRight_add : (A + B).traceRight = A.traceRight + B.traceRight := by
  ext1; simp


-- @@ L202-204 verbatim
@[simp]
theorem traceRight_neg : (-A).traceRight = -A.traceRight := by
  ext1; simp


-- @@ L206-208 verbatim
@[simp]
theorem traceRight_sub : (A - B).traceRight = A.traceRight - B.traceRight := by
  ext1; simp


-- @@ L210-210 verbatim
end addCommGroup

-- @@ L211-211 verbatim
section rcLike


-- @@ L213-213 verbatim
variable {𝕜} [RCLike 𝕜]

-- @@ L214-214 verbatim
variable (A : HermitianMat (m × n) 𝕜)


-- @@ L216-219 verbatim
omit [Fintype n] in
@[simp]
theorem traceLeft_smul (r : ℝ) : (r • A).traceLeft = r • A.traceLeft := by
  ext1; simp


-- @@ L221-224 verbatim
omit [Fintype m] in
@[simp]
theorem traceRight_smul (r : ℝ) : (r • A).traceRight = r • A.traceRight := by
  ext1; simp


-- @@ L226-228 verbatim
@[simp]
theorem traceLeft_trace : A.traceLeft.trace = A.trace := by
  simp [trace_eq_re_trace]


-- @@ L230-232 verbatim
@[simp]
theorem traceRight_trace : A.traceRight.trace = A.trace := by
  simp [trace_eq_re_trace]


-- @@ L234-234 verbatim
end rcLike

-- @@ L235-235 verbatim
section kron


-- @@ L237-237 verbatim
variable {m n 𝕜 : Type*} [RCLike 𝕜]

-- @@ L238-238 verbatim
variable (A : HermitianMat m 𝕜) (B : HermitianMat n 𝕜)


-- @@ L240-244 expanded
@[simp]
theorem traceLeft_kron [Fintype m] : (HermitianMat.kronecker A B).traceLeft = A.trace • B :=
  by
  ext : 2
  simp only [HermitianMat.traceLeft, Matrix.traceLeft, kronecker_mat, mat_mk]
  simp [Matrix.trace, RCLike.real_smul_eq_coe_mul, ← Finset.sum_mul]


-- @@ L246-250 expanded
@[simp]
theorem traceRight_kron [Fintype n] : (HermitianMat.kronecker A B).traceRight = B.trace • A :=
  by
  ext : 2
  simp only [HermitianMat.traceRight, Matrix.traceRight, kronecker_mat, mat_mk]
  simp [Matrix.trace, RCLike.real_smul_eq_coe_mul, ← Finset.mul_sum, mul_comm]


-- @@ L252-252 verbatim
end kron

-- @@ L253-253 verbatim
end partialTrace
