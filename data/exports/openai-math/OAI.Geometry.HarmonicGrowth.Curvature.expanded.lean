import OAI.Geometry.HarmonicGrowth.Berger


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open Filter MeasureTheory

-- @@ L7-7 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L8-8 verbatim
open Matrix

-- @@ L9-9 verbatim
open scoped BigOperators

-- @@ L10-10 verbatim
open Matrix

-- @@ L11-11 verbatim
open scoped BigOperators

-- @@ L12-12 verbatim
open Filter Matrix

-- @@ L13-13 verbatim
open scoped BigOperators Topology ContDiff


-- @@ L15-15 verbatim
namespace HarmonicCounterexample.Berger

-- @@ L16-16 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


-- @@ L18-20 verbatim
lemma ComplexStructure.square_mulVec (J : ComplexStructure ι) (u : ι → ℝ) :
    J.matrix *ᵥ (J.matrix *ᵥ u) = -u := by
  rw [Matrix.mulVec_mulVec, J.square, Matrix.neg_mulVec, Matrix.one_mulVec]


-- @@ L22-25 verbatim
lemma ComplexStructure.trace_zero (J : ComplexStructure ι) : J.matrix.trace = 0 := by
  have h := congrArg Matrix.trace J.skew
  rw [Matrix.trace_transpose, Matrix.trace_neg] at h
  linarith


-- @@ L27-32 verbatim
lemma ComplexStructure.dot_skew (J : ComplexStructure ι) (u v : ι → ℝ) :
    (J.matrix *ᵥ u) ⬝ᵥ v = -(u ⬝ᵥ (J.matrix *ᵥ v)) := by
  calc
    _ = (J.matrixᵀ *ᵥ v) ⬝ᵥ u := by
      rw [dotProduct_comm, dotProduct_mulVec, Matrix.mulVec_transpose]
    _ = _ := by rw [J.skew, Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm]


-- @@ L34-38 verbatim
omit [DecidableEq ι] in
lemma trace_rank_mul (u v : ι → ℝ) (A : Matrix ι ι ℝ) :
    (Matrix.vecMulVec u v * A).trace = v ⬝ᵥ (A *ᵥ u) := by
  rw [Matrix.trace_mul_comm, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec,
    dotProduct_comm]


-- @@ L40-43 verbatim
omit [DecidableEq ι] in
lemma trace_mul_rank (A : Matrix ι ι ℝ) (u v : ι → ℝ) :
    (A * Matrix.vecMulVec u v).trace = v ⬝ᵥ (A *ᵥ u) := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]


-- @@ L45-50 verbatim
omit [DecidableEq ι] in
lemma trace_rank_rank (u v w z : ι → ℝ) :
    (Matrix.vecMulVec u v * Matrix.vecMulVec w z).trace =
      (v ⬝ᵥ w) * (z ⬝ᵥ u) := by
  rw [trace_rank_mul, Matrix.vecMulVec_mulVec, dotProduct_smul]
  simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]



-- @@ L53-63 verbatim
/-- The endomorphism v ↦ Γ(u,v), after raising the first-kind connection.
This nine-low-rank decomposition permits exact finite-dimensional traces. -/
def connectionMatrix (J : ComplexStructure ι) (x : ι → ℝ)
    (a b c d e f : ℝ) (u : ι → ℝ) : Matrix ι ι ℝ :=
  (a*(x ⬝ᵥ u)) • 1 + a • Matrix.vecMulVec u x + b • Matrix.vecMulVec x u +
  (c*(x ⬝ᵥ u)) • Matrix.vecMulVec x x +
  (d*(x ⬝ᵥ u)) • Matrix.vecMulVec (J.matrix *ᵥ x) (J.matrix *ᵥ x) +
  (d*((J.matrix *ᵥ x) ⬝ᵥ u)) • Matrix.vecMulVec (J.matrix *ᵥ x) x +
  (e*((J.matrix *ᵥ x) ⬝ᵥ u)) • Matrix.vecMulVec x (J.matrix *ᵥ x) +
  f • Matrix.vecMulVec (J.matrix *ᵥ u) (J.matrix *ᵥ x) +
  (f*((J.matrix *ᵥ x) ⬝ᵥ u)) • J.matrix


-- @@ L65-73 verbatim
lemma connectionMatrix_trace (J : ComplexStructure ι) (x u : ι → ℝ)
    (a b c d e f : ℝ) :
    (connectionMatrix J x a b c d e f u).trace =
      (a*((Fintype.card ι:ℝ)+1)+b+(c+d)*(x ⬝ᵥ x)+f)*(x ⬝ᵥ u) := by
  simp only [connectionMatrix, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_one,
    Matrix.trace_vecMulVec, J.trace_zero, J.preserves_dot, J.orthogonal_radial,
    smul_eq_mul, dotProduct_comm (J.matrix *ᵥ x) x, mul_zero, add_zero,
    dotProduct_comm u x]
  ring


-- @@ L75-100 verbatim
/-- Exact quadratic connection trace, the difficult algebraic part of Ricci.
No dimension-specific computation or assumed Gauss/Codazzi formula is used. -/
lemma connectionMatrix_trace_product (J : ComplexStructure ι) (x u v : ι → ℝ)
    (a b c d e f : ℝ) :
    (connectionMatrix J x a b c d e f u *
      connectionMatrix J x a b c d e f v).trace =
    2*a*b*(x ⬝ᵥ x)*(u ⬝ᵥ v) +
    ((2*a+b+c*(x ⬝ᵥ x))^2 + (a+d*(x ⬝ᵥ x)+f)^2 +
      ((Fintype.card ι:ℝ)-2)*a^2-2*a*b)*(x ⬝ᵥ u)*(x ⬝ᵥ v) +
    (2*(a+d*(x ⬝ᵥ x)+f)*(b+e*(x ⬝ᵥ x)-2*f) -
      ((Fintype.card ι:ℝ)-2)*f^2-2*a*b)*
        ((J.matrix *ᵥ x) ⬝ᵥ u)*((J.matrix *ᵥ x) ⬝ᵥ v) := by
  simp only [connectionMatrix, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul,
    one_mul, mul_one, Matrix.trace_one, Matrix.trace_vecMulVec, J.trace_zero,
    trace_mul_rank, trace_rank_mul, Matrix.vecMulVec_mulVec, dotProduct_smul,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, J.square,
    Matrix.trace_neg, J.square_mulVec, J.preserves_dot,
    J.orthogonal_radial, dotProduct_neg, mul_zero, zero_mul, add_zero,
    zero_add, dotProduct_comm (J.matrix *ᵥ x) x, dotProduct_comm u x,
    dotProduct_comm v x, dotProduct_comm u v,
    dotProduct_comm u (J.matrix *ᵥ x), dotProduct_comm v (J.matrix *ᵥ x)]
  have hux := J.dot_skew x u
  have hvx := J.dot_skew x v
  simp only [hux, hvx]
  ring


-- @@ L102-102 verbatim
end HarmonicCounterexample.Berger


-- @@ L104-104 verbatim
end


-- @@ L106-106 verbatim
noncomputable section

-- @@ L107-107 verbatim
open Filter MeasureTheory

-- @@ L108-108 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L109-109 verbatim
open Matrix

-- @@ L110-110 verbatim
open scoped BigOperators

-- @@ L111-111 verbatim
open Matrix

-- @@ L112-112 verbatim
open scoped BigOperators

-- @@ L113-113 verbatim
open Filter Matrix

-- @@ L114-114 verbatim
open scoped BigOperators Topology ContDiff


-- @@ L116-116 verbatim
namespace HarmonicCounterexample.Berger

-- @@ L117-117 verbatim
open Matrix

-- @@ L118-118 verbatim
variable {n : ℕ}


-- @@ L120-124 verbatim
lemma ComplexStructure.diagonal_zero (J : ComplexStructure (Fin n)) (i : Fin n) :
    J.matrix i i = 0 := by
  have h := congrFun (congrFun J.skew i) i
  change J.matrix i i = -J.matrix i i at h
  linarith


-- @@ L126-127 verbatim
lemma ComplexStructure.entry_skew (J : ComplexStructure (Fin n)) (i j : Fin n) :
    J.matrix j i = -J.matrix i j := congrFun (congrFun J.skew i) j


-- @@ L129-132 verbatim
lemma ComplexStructure.sum_x_entry (J : ComplexStructure (Fin n)) (x : Space n) (i : Fin n) :
    (∑ k, x k * J.matrix k i) = -(J.matrix *ᵥ x) i := by
  simp only [J.entry_skew i, mul_neg]
  simp [Matrix.mulVec, dotProduct, mul_comm]


-- @@ L134-137 verbatim
lemma ComplexStructure.sum_w_entry (J : ComplexStructure (Fin n)) (x : Space n) (i : Fin n) :
    (∑ k, (J.matrix *ᵥ x) k * J.matrix k i) = x i := by
  rw [J.sum_x_entry]
  simp [J.square_mulVec]


-- @@ L139-141 verbatim
lemma ComplexStructure.sum_entries (J : ComplexStructure (Fin n)) (i j : Fin n) :
    (∑ k, J.matrix k i * J.matrix k j) = (1 : Mat n) i j := by
  exact congrFun (congrFun J.orthogonal i) j


-- @@ L143-150 verbatim
/-- Cartesian Christoffel coefficients written in their invariant six-term form. -/
def connectionCoeff (J : ComplexStructure (Fin n)) (x : Space n)
    (a b c d e f : ℝ) (k i j : Fin n) : ℝ :=
  a*(x i*(1:Mat n) k j+x j*(1:Mat n) k i)+b*x k*(1:Mat n) i j+
  c*x k*x i*x j+
  d*(J.matrix *ᵥ x) k*(x i*(J.matrix *ᵥ x) j+x j*(J.matrix *ᵥ x) i)+
  e*x k*(J.matrix *ᵥ x) i*(J.matrix *ᵥ x) j+
  f*((J.matrix *ᵥ x) j*J.matrix k i+(J.matrix *ᵥ x) i*J.matrix k j)


-- @@ L152-164 verbatim
lemma connectionCoeff_eq_matrix (J : ComplexStructure (Fin n)) (x : Space n)
    (a b c d e f : ℝ) (k i j : Fin n) :
    connectionCoeff J x a b c d e f k i j =
      connectionMatrix J x a b c d e f (Pi.single i 1) k j := by
  simp only [connectionMatrix, connectionCoeff, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul, Matrix.vecMulVec_apply, dotProduct_single_one, Matrix.mulVec_single,
    Matrix.one_apply, Pi.single_apply]
  have hji : (if i = j then (1:ℝ) else 0) = (if j = i then (1:ℝ) else 0) := by
    simp only [eq_comm]
  simp only [hji, Pi.smul_apply, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, mul_one]
  change _ = _ + f * (J.matrix k i * (J.matrix *ᵥ x) j) + _
  ring


-- @@ L166-172 verbatim
lemma connectionCoeff_symmetric (J : ComplexStructure (Fin n)) (x : Space n)
    (a b c d e f : ℝ) (k i j : Fin n) :
    connectionCoeff J x a b c d e f k i j =
      connectionCoeff J x a b c d e f k j i := by
  have h : (1 : Mat n) i j = (1 : Mat n) j i := by simp [Matrix.one_apply, eq_comm]
  simp only [connectionCoeff, h]
  ring


-- @@ L174-181 verbatim
lemma connectionCoeff_trace (J : ComplexStructure (Fin n)) (x : Space n)
    (a b c d e f : ℝ) (i : Fin n) :
    (∑ k, connectionCoeff J x a b c d e f k i k) =
      (a*((n:ℝ)+1)+b+(c+d)*(x ⬝ᵥ x)+f)*x i := by
  simp only [connectionCoeff_eq_matrix]
  change (connectionMatrix J x a b c d e f (Pi.single i 1)).trace = _
  rw [connectionMatrix_trace]
  simp


-- @@ L183-197 verbatim
lemma connectionCoeff_inner_trace (J : ComplexStructure (Fin n)) (x : Space n)
    (a b c d e f : ℝ) (i j : Fin n) :
    (∑ k, ∑ l, connectionCoeff J x a b c d e f l i k *
      connectionCoeff J x a b c d e f k j l) =
    2*a*b*(x ⬝ᵥ x)*(1:Mat n) i j+
    ((2*a+b+c*(x ⬝ᵥ x))^2+(a+d*(x ⬝ᵥ x)+f)^2+
      ((n:ℝ)-2)*a^2-2*a*b)*x i*x j+
    (2*(a+d*(x ⬝ᵥ x)+f)*(b+e*(x ⬝ᵥ x)-2*f)-
      ((n:ℝ)-2)*f^2-2*a*b)*(J.matrix *ᵥ x) i*(J.matrix *ᵥ x) j := by
  simp only [connectionCoeff_eq_matrix]
  rw [Finset.sum_comm]
  change (connectionMatrix J x a b c d e f (Pi.single i 1) *
    connectionMatrix J x a b c d e f (Pi.single j 1)).trace = _
  rw [connectionMatrix_trace_product]
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]


-- @@ L199-208 verbatim
lemma coordDeriv_radialSquare (x : Space n) (i : Fin n) :
    coordDeriv i (fun y : Space n => y ⬝ᵥ y) x = 2*x i := by
  change coordDeriv i (fun y : Space n => ∑ k, y k * y k) x = _
  rw [coordDeriv_sum Finset.univ (f := fun k y => y k * y k)
    (fun k _ => (hasFDerivAt_apply k x).differentiableAt.mul
      (hasFDerivAt_apply k x).differentiableAt)]
  simp [coordDeriv_mul (hasFDerivAt_apply _ _).differentiableAt
    (hasFDerivAt_apply _ _).differentiableAt, coordDeriv_coordinate, Matrix.one_apply,
    Finset.sum_add_distrib]
  ring


-- @@ L210-213 verbatim
lemma differentiableAt_linear_entry (M : Mat n) (x : Space n) (i : Fin n) :
    DifferentiableAt ℝ (fun y => (M *ᵥ y) i) x := by
  change DifferentiableAt ℝ (fun y => ∑ j, M i j * y j) x
  fun_prop


-- @@ L215-215 verbatim
end HarmonicCounterexample.Berger


-- @@ L217-217 verbatim
end


-- @@ L219-219 verbatim
noncomputable section

-- @@ L220-220 verbatim
open Filter MeasureTheory

-- @@ L221-221 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L222-222 verbatim
open Matrix

-- @@ L223-223 verbatim
open scoped BigOperators

-- @@ L224-224 verbatim
open Matrix

-- @@ L225-225 verbatim
open scoped BigOperators

-- @@ L226-226 verbatim
open Filter Matrix

-- @@ L227-227 verbatim
open scoped BigOperators Topology ContDiff


-- @@ L229-229 verbatim
namespace HarmonicCounterexample.Berger

-- @@ L230-230 verbatim
open Matrix

-- @@ L231-231 verbatim
variable {n : ℕ}


-- @@ L233-242 verbatim
lemma divergence_delta_radial {p : Space n → ℝ} {x : Space n} {pd : ℝ}
    (hp : DifferentiableAt ℝ p x) (hpd : ∀ i, coordDeriv i p x = pd*x i)
    (i j : Fin n) :
    (∑ k, coordDeriv k (fun y => p y * (y i*(1:Mat n) k j+y j*(1:Mat n) k i)) x) =
      2*p x*(1:Mat n) i j+2*pd*x i*x j := by
  simp (disch := fun_prop) only [coordDeriv_mul, coordDeriv_add,
    coordDeriv_const, coordDeriv_coordinate, hpd, mul_zero]
  simp only [Matrix.one_apply]
  simp [Finset.sum_add_distrib, mul_add, add_mul, eq_comm]
  split_ifs <;> ring


-- @@ L244-260 verbatim
lemma divergence_radial_delta {p : Space n → ℝ} {x : Space n} {pd : ℝ}
    (hp : DifferentiableAt ℝ p x) (hpd : ∀ i, coordDeriv i p x = pd*x i)
    (i j : Fin n) :
    (∑ k, coordDeriv k (fun y => p y * y k * (1:Mat n) i j) x) =
      ((n:ℝ)*p x+pd*(x ⬝ᵥ x))*(1:Mat n) i j := by
  simp (disch := fun_prop) only [coordDeriv_mul, coordDeriv_const,
    coordDeriv_coordinate, hpd, mul_zero, zero_add, Matrix.one_apply_eq, mul_one]
  calc
    _ = ∑ k, ((1:Mat n) i j*p x + pd*(1:Mat n) i j*(x k*x k)) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
      change _ + pd*(1:Mat n) i j*(x ⬝ᵥ x) = _
      ring


-- @@ L262-281 verbatim
lemma divergence_radial_cubic {p : Space n → ℝ} {x : Space n} {pd : ℝ}
    (hp : DifferentiableAt ℝ p x) (hpd : ∀ i, coordDeriv i p x = pd*x i)
    (i j : Fin n) :
    (∑ k, coordDeriv k (fun y => p y * y k * y i * y j) x) =
      (pd*(x ⬝ᵥ x)+((n:ℝ)+2)*p x)*x i*x j := by
  simp (disch := fun_prop) only [coordDeriv_mul, coordDeriv_coordinate,
    hpd, Matrix.one_apply_eq, mul_one]
  calc
    _ = ∑ k, (p x*x i*x j + (pd*x i*x j)*(x k*x k) +
        (p x*x j)*((1:Mat n) i k*x k) + (p x*x i)*((1:Mat n) j k*x k)) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
      simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq]
      change _ + pd*x i*x j*(x ⬝ᵥ x) + _ + _ = _
      simp only [Finset.mem_univ, ite_true]
      ring


-- @@ L283-311 verbatim
lemma divergence_hopf_mixed (J : ComplexStructure (Fin n))
    {p : Space n → ℝ} {x : Space n} {pd : ℝ}
    (hp : DifferentiableAt ℝ p x) (hpd : ∀ i, coordDeriv i p x = pd*x i)
    (i j : Fin n) :
    (∑ k, coordDeriv k (fun y => p y * (J.matrix *ᵥ y) k *
      (y i*(J.matrix *ᵥ y) j+y j*(J.matrix *ᵥ y) i)) x) =
      2*p x*(J.matrix *ᵥ x) i*(J.matrix *ᵥ x) j-2*p x*x i*x j := by
  have hJ (k : Fin n) := differentiableAt_linear_entry J.matrix x k
  simp (disch := fun_prop) only [coordDeriv_mul, coordDeriv_add,
    coordDeriv_coordinate, coordDeriv_linear, hpd, J.diagonal_zero, mul_zero, zero_add]
  calc
    _ = ∑ k, ((pd*(x i*(J.matrix *ᵥ x) j+x j*(J.matrix *ᵥ x) i))*
        (x k*(J.matrix *ᵥ x) k) +
      (p x*(J.matrix *ᵥ x) j)*((1:Mat n) i k*(J.matrix *ᵥ x) k) +
      (p x*(J.matrix *ᵥ x) i)*((1:Mat n) j k*(J.matrix *ᵥ x) k) +
      (p x*x i)*(J.matrix j k*(J.matrix *ᵥ x) k) +
      (p x*x j)*(J.matrix i k*(J.matrix *ᵥ x) k)) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      change pd*_*(x ⬝ᵥ (J.matrix *ᵥ x)) + _ + _ +
        (p x*x i)*(J.matrix *ᵥ (J.matrix *ᵥ x)) j +
        (p x*x j)*(J.matrix *ᵥ (J.matrix *ᵥ x)) i = _
      rw [J.orthogonal_radial, J.square_mulVec]
      simp only [mul_zero, zero_add, Pi.neg_apply, Matrix.one_apply, ite_mul,
        one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
      ring


-- @@ L313-335 verbatim
lemma divergence_hopf_cubic (J : ComplexStructure (Fin n))
    {p : Space n → ℝ} {x : Space n} {pd : ℝ}
    (hp : DifferentiableAt ℝ p x) (hpd : ∀ i, coordDeriv i p x = pd*x i)
    (i j : Fin n) :
    (∑ k, coordDeriv k (fun y => p y * y k *
      (J.matrix *ᵥ y) i*(J.matrix *ᵥ y) j) x) =
      (pd*(x ⬝ᵥ x)+((n:ℝ)+2)*p x)*(J.matrix *ᵥ x) i*(J.matrix *ᵥ x) j := by
  have hJ (k : Fin n) := differentiableAt_linear_entry J.matrix x k
  simp (disch := fun_prop) only [coordDeriv_mul, coordDeriv_coordinate,
    coordDeriv_linear, hpd, Matrix.one_apply_eq, mul_one]
  calc
    _ = ∑ k, (p x*(J.matrix *ᵥ x) i*(J.matrix *ᵥ x) j +
      (pd*(J.matrix *ᵥ x) i*(J.matrix *ᵥ x) j)*(x k*x k) +
      (p x*(J.matrix *ᵥ x) j)*(J.matrix i k*x k) +
      (p x*(J.matrix *ᵥ x) i)*(J.matrix j k*x k)) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
      change _ + _*(x ⬝ᵥ x) + _*(J.matrix *ᵥ x) i + _*(J.matrix *ᵥ x) j = _
      ring


-- @@ L337-359 verbatim
lemma divergence_hopf_linear (J : ComplexStructure (Fin n))
    {p : Space n → ℝ} {x : Space n} {pd : ℝ}
    (hp : DifferentiableAt ℝ p x) (hpd : ∀ i, coordDeriv i p x = pd*x i)
    (i j : Fin n) :
    (∑ k, coordDeriv k (fun y => p y *
      ((J.matrix *ᵥ y) j*J.matrix k i+(J.matrix *ᵥ y) i*J.matrix k j)) x) =
      -2*p x*(1:Mat n) i j-2*pd*(J.matrix *ᵥ x) i*(J.matrix *ᵥ x) j := by
  have hJ (k : Fin n) := differentiableAt_linear_entry J.matrix x k
  simp (disch := fun_prop) only [coordDeriv_mul, coordDeriv_add, coordDeriv_const,
    coordDeriv_linear, hpd, mul_zero, zero_add]
  calc
    _ = ∑ k, ((pd*(J.matrix *ᵥ x) j)*(x k*J.matrix k i) +
      (pd*(J.matrix *ᵥ x) i)*(x k*J.matrix k j) -
      p x*(J.matrix k i*J.matrix k j)-p x*(J.matrix k i*J.matrix k j)) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [J.entry_skew k j, J.entry_skew k i]
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      simp only [← Finset.mul_sum]
      rw [J.sum_entries, J.sum_x_entry, J.sum_x_entry]
      ring


-- @@ L361-361 verbatim
end HarmonicCounterexample.Berger


-- @@ L363-363 verbatim
end


-- @@ L365-365 verbatim
noncomputable section

-- @@ L366-366 verbatim
open Filter MeasureTheory

-- @@ L367-367 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L368-368 verbatim
open Matrix

-- @@ L369-369 verbatim
open scoped BigOperators

-- @@ L370-370 verbatim
open Matrix

-- @@ L371-371 verbatim
open scoped BigOperators

-- @@ L372-372 verbatim
open Filter Matrix

-- @@ L373-373 verbatim
open scoped BigOperators Topology ContDiff


-- @@ L375-375 verbatim
namespace HarmonicCounterexample.Berger

-- @@ L376-376 verbatim
open Matrix

-- @@ L377-377 verbatim
variable {n : ℕ}


-- @@ L379-401 verbatim
lemma connectionCoeff_radial_contraction (J : ComplexStructure (Fin n)) (x : Space n)
    (a b c d e f : ℝ) (i j : Fin n) :
    (∑ k, connectionCoeff J x a b c d e f k i j * x k) =
      b*(x ⬝ᵥ x)*(1:Mat n) i j+(2*a+c*(x ⬝ᵥ x))*x i*x j+
        (e*(x ⬝ᵥ x)-2*f)*(J.matrix *ᵥ x) i*(J.matrix *ᵥ x) j := by
  calc
    _ = ∑ k, ((a*x i)*((1:Mat n) k j*x k)+(a*x j)*((1:Mat n) k i*x k)+
        (b*(1:Mat n) i j+c*x i*x j+e*(J.matrix *ᵥ x) i*(J.matrix *ᵥ x) j)*(x k*x k)+
        (d*(x i*(J.matrix *ᵥ x) j+x j*(J.matrix *ᵥ x) i))*(x k*(J.matrix *ᵥ x) k)+
        (f*(J.matrix *ᵥ x) j)*(x k*J.matrix k i)+
        (f*(J.matrix *ᵥ x) i)*(x k*J.matrix k j)) := by
      apply Finset.sum_congr rfl
      intro k _
      simp only [connectionCoeff]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [J.sum_x_entry, J.sum_x_entry]
      change _ + _ + _*(x ⬝ᵥ x) + _*(x ⬝ᵥ (J.matrix *ᵥ x)) + _ + _ = _
      rw [J.orthogonal_radial]
      simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, mul_zero, add_zero]
      ring


-- @@ L403-419 verbatim
lemma connectionCoeff_outer_trace (J : ComplexStructure (Fin n)) (x : Space n)
    (a b c d e f : ℝ) (i j : Fin n) :
    (∑ k, ∑ l, connectionCoeff J x a b c d e f k i j *
      connectionCoeff J x a b c d e f l k l) =
    (a*((n:ℝ)+1)+b+(c+d)*(x ⬝ᵥ x)+f)*
      (b*(x ⬝ᵥ x)*(1:Mat n) i j+(2*a+c*(x ⬝ᵥ x))*x i*x j+
        (e*(x ⬝ᵥ x)-2*f)*(J.matrix *ᵥ x) i*(J.matrix *ᵥ x) j) := by
  simp only [← Finset.mul_sum, connectionCoeff_trace]
  rw [show (∑ k, connectionCoeff J x a b c d e f k i j *
      ((a*((n:ℝ)+1)+b+(c+d)*(x ⬝ᵥ x)+f)*x k)) =
    (a*((n:ℝ)+1)+b+(c+d)*(x ⬝ᵥ x)+f)*
      ∑ k, connectionCoeff J x a b c d e f k i j*x k by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring]
  rw [connectionCoeff_radial_contraction]


-- @@ L421-430 verbatim
lemma connectionCoeff_differentiableAt (J : ComplexStructure (Fin n))
    {a b c d e f : Space n → ℝ} {x : Space n}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hc : DifferentiableAt ℝ c x) (hd : DifferentiableAt ℝ d x)
    (he : DifferentiableAt ℝ e x) (hf : DifferentiableAt ℝ f x)
    (k i j : Fin n) :
    DifferentiableAt ℝ (fun y => connectionCoeff J y (a y) (b y) (c y) (d y) (e y) (f y) k i j) x := by
  have hJ (l : Fin n) := differentiableAt_linear_entry J.matrix x l
  unfold connectionCoeff
  fun_prop


-- @@ L432-451 verbatim
lemma connectionCoeff_divergence (J : ComplexStructure (Fin n))
    {a b c d e f : Space n → ℝ} {x : Space n} {ad bd cd dd ed fd : ℝ}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hc : DifferentiableAt ℝ c x) (hd : DifferentiableAt ℝ d x)
    (he : DifferentiableAt ℝ e x) (hf : DifferentiableAt ℝ f x)
    (had : ∀ i, coordDeriv i a x = ad*x i) (hbd : ∀ i, coordDeriv i b x = bd*x i)
    (hcd : ∀ i, coordDeriv i c x = cd*x i) (hdd : ∀ i, coordDeriv i d x = dd*x i)
    (hed : ∀ i, coordDeriv i e x = ed*x i) (hfd : ∀ i, coordDeriv i f x = fd*x i)
    (i j : Fin n) :
    (∑ k, coordDeriv k (fun y => connectionCoeff J y (a y) (b y) (c y) (d y) (e y) (f y) k i j) x) =
      (2*a x+(n:ℝ)*b x+bd*(x ⬝ᵥ x)-2*f x)*(1:Mat n) i j+
      (2*ad+cd*(x ⬝ᵥ x)+((n:ℝ)+2)*c x-2*d x)*x i*x j+
      (2*d x+ed*(x ⬝ᵥ x)+((n:ℝ)+2)*e x-2*fd)*(J.matrix *ᵥ x) i*(J.matrix *ᵥ x) j := by
  have hJ (l : Fin n) := differentiableAt_linear_entry J.matrix x l
  simp only [connectionCoeff]
  simp (disch := fun_prop) only [coordDeriv_add, Finset.sum_add_distrib]
  rw [divergence_delta_radial ha had, divergence_radial_delta hb hbd,
    divergence_radial_cubic hc hcd, divergence_hopf_mixed J hd hdd,
    divergence_hopf_cubic J he hed, divergence_hopf_linear J hf hfd]
  ring


-- @@ L453-477 verbatim
lemma connectionCoeff_trace_derivative (J : ComplexStructure (Fin n))
    {a b c d e f : Space n → ℝ} {x : Space n} {ad bd cd dd fd : ℝ}
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hc : DifferentiableAt ℝ c x) (hd : DifferentiableAt ℝ d x)
    (he : DifferentiableAt ℝ e x) (hf : DifferentiableAt ℝ f x)
    (had : ∀ i, coordDeriv i a x = ad*x i) (hbd : ∀ i, coordDeriv i b x = bd*x i)
    (hcd : ∀ i, coordDeriv i c x = cd*x i) (hdd : ∀ i, coordDeriv i d x = dd*x i)
    (hfd : ∀ i, coordDeriv i f x = fd*x i)
    (i j : Fin n) :
    (∑ k, coordDeriv j (fun y => connectionCoeff J y (a y) (b y) (c y) (d y) (e y) (f y) k i k) x) =
      (a x*((n:ℝ)+1)+b x+(c x+d x)*(x ⬝ᵥ x)+f x)*(1:Mat n) i j+
      (ad*((n:ℝ)+1)+bd+(cd+dd)*(x ⬝ᵥ x)+2*(c x+d x)+fd)*x i*x j := by
  rw [← coordDeriv_sum Finset.univ (fun k _ => connectionCoeff_differentiableAt J ha hb hc hd he hf k i k)]
  have hsum : (fun y => ∑ k, connectionCoeff J y (a y) (b y) (c y) (d y) (e y) (f y) k i k) =
      (fun y => (a y*((n:ℝ)+1)+b y+(c y+d y)*(y ⬝ᵥ y)+f y)*y i) := by
    funext y
    exact connectionCoeff_trace J y _ _ _ _ _ _ i
  rw [hsum]
  have hs : DifferentiableAt ℝ (fun y : Space n => y ⬝ᵥ y) x := by
    unfold dotProduct
    fun_prop
  simp (disch := fun_prop) only [coordDeriv_mul, coordDeriv_add, coordDeriv_const,
    coordDeriv_radialSquare, coordDeriv_coordinate, had, hbd, hcd, hdd, hfd, mul_zero,
    zero_add]
  ring


-- @@ L479-511 verbatim
/-- Ricci computed from the exact Christoffel ansatz on a neighbourhood.
This theorem uses the frozen coordinate definition of `ricci` verbatim. -/
theorem ricci_of_connectionCoeff (g : SmoothMetric n) (J : ComplexStructure (Fin n))
    {a b c d e f : Space n → ℝ} {x : Space n} {ad bd cd dd ed fd : ℝ}
    (hΓ : ∀ᶠ y in 𝓝 x, ∀ k i j, christoffel g y k i j =
      connectionCoeff J y (a y) (b y) (c y) (d y) (e y) (f y) k i j)
    (ha : DifferentiableAt ℝ a x) (hb : DifferentiableAt ℝ b x)
    (hc : DifferentiableAt ℝ c x) (hd : DifferentiableAt ℝ d x)
    (he : DifferentiableAt ℝ e x) (hf : DifferentiableAt ℝ f x)
    (had : ∀ i, coordDeriv i a x = ad*x i) (hbd : ∀ i, coordDeriv i b x = bd*x i)
    (hcd : ∀ i, coordDeriv i c x = cd*x i) (hdd : ∀ i, coordDeriv i d x = dd*x i)
    (hed : ∀ i, coordDeriv i e x = ed*x i) (hfd : ∀ i, coordDeriv i f x = fd*x i)
    (i j : Fin n) :
    let S := x ⬝ᵥ x
    let T := a x*((n:ℝ)+1)+b x+(c x+d x)*S+f x
    let Td := ad*((n:ℝ)+1)+bd+(cd+dd)*S+2*(c x+d x)+fd
    ricci g x i j =
      (2*a x+(n:ℝ)*b x+bd*S-2*f x-T+T*b x*S-2*a x*b x*S)*(1:Mat n) i j+
      (2*ad+cd*S+((n:ℝ)+2)*c x-2*d x-Td+T*(2*a x+c x*S)-
        ((2*a x+b x+c x*S)^2+(a x+d x*S+f x)^2+((n:ℝ)-2)*(a x)^2-2*a x*b x))*x i*x j+
      (2*d x+ed*S+((n:ℝ)+2)*e x-2*fd+T*(e x*S-2*f x)-
        (2*(a x+d x*S+f x)*(b x+e x*S-2*f x)-((n:ℝ)-2)*(f x)^2-2*a x*b x))*
          (J.matrix *ᵥ x) i*(J.matrix *ᵥ x) j := by
  dsimp only
  have hval := hΓ.self_of_nhds
  have hdiff (l k i j : Fin n) : coordDeriv l (fun y => christoffel g y k i j) x =
      coordDeriv l (fun y => connectionCoeff J y (a y) (b y) (c y) (d y) (e y) (f y) k i j) x :=
    coordDeriv_congr (hΓ.mono fun y hy => hy k i j) l
  simp only [ricci, hval, hdiff, Finset.sum_sub_distrib]
  rw [connectionCoeff_divergence J ha hb hc hd he hf had hbd hcd hdd hed hfd,
    connectionCoeff_trace_derivative J ha hb hc hd he hf had hbd hcd hdd hfd,
    connectionCoeff_outer_trace, connectionCoeff_inner_trace]
  ring


-- @@ L513-513 verbatim
end HarmonicCounterexample.Berger


-- @@ L515-515 verbatim
end


-- @@ L517-517 verbatim
noncomputable section

-- @@ L518-518 verbatim
open Filter MeasureTheory

-- @@ L519-519 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L520-520 verbatim
open Matrix

-- @@ L521-521 verbatim
open scoped BigOperators

-- @@ L522-522 verbatim
open Matrix

-- @@ L523-523 verbatim
open scoped BigOperators

-- @@ L524-524 verbatim
open Filter Matrix

-- @@ L525-525 verbatim
open scoped BigOperators Topology ContDiff


-- @@ L527-527 verbatim
namespace HarmonicCounterexample.Berger

-- @@ L528-528 verbatim
open Matrix

-- @@ L529-529 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


-- @@ L531-535 verbatim
/-- Polar tensor in unnormalized Cartesian coordinates. Its radial/Hopf/
horizontal eigenvalues are respectively 1,D,A. -/
def polarTensor (J : ComplexStructure ι) (x : ι → ℝ) (A D : ℝ) : Matrix ι ι ℝ :=
  A • 1+((1-A)/(x ⬝ᵥ x)) • vecMulVec x x+
    ((D-A)/(x ⬝ᵥ x)) • vecMulVec (J.matrix *ᵥ x) (J.matrix *ᵥ x)


-- @@ L537-551 verbatim
lemma polarTensor_inverse (J : ComplexStructure ι) {x : ι → ℝ}
    (hx : x ⬝ᵥ x ≠ 0) {A D : ℝ} (hA : A ≠ 0) (hD : D ≠ 0) :
    (polarTensor J x A D)⁻¹ = polarTensor J x A⁻¹ D⁻¹ := by
  apply Matrix.inv_eq_right_inv
  have hwx : (J.matrix *ᵥ x) ⬝ᵥ x = 0 := by
    rw [dotProduct_comm, J.orthogonal_radial]
  simp only [polarTensor, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul,
    Matrix.mul_smul, one_mul, mul_one, Matrix.vecMulVec_mul_vecMulVec,
    J.orthogonal_radial, hwx, J.preserves_dot, zero_smul, Matrix.vecMulVec_zero,
    smul_zero, add_zero]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Pi.smul_apply, smul_eq_mul]
  field_simp
  ring


-- @@ L553-562 verbatim
lemma polarTensor_mulVec (J : ComplexStructure ι) (x v : ι → ℝ) (A D : ℝ) :
    polarTensor J x A D *ᵥ v =
      A • v+(((1-A)/(x ⬝ᵥ x))*(x ⬝ᵥ v)) • x+
        (((D-A)/(x ⬝ᵥ x))*((J.matrix *ᵥ x) ⬝ᵥ v)) • (J.matrix *ᵥ x) := by
  simp only [polarTensor, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    Matrix.vecMulVec_mulVec]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, smul_eq_mul]
  ring


-- @@ L564-564 verbatim
end HarmonicCounterexample.Berger


-- @@ L566-566 verbatim
end


-- @@ L568-568 verbatim
noncomputable section

-- @@ L569-569 verbatim
open Filter MeasureTheory

-- @@ L570-570 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L571-571 verbatim
open Matrix

-- @@ L572-572 verbatim
open scoped BigOperators

-- @@ L573-573 verbatim
open Matrix

-- @@ L574-574 verbatim
open scoped BigOperators

-- @@ L575-575 verbatim
open Filter Matrix

-- @@ L576-576 verbatim
open scoped BigOperators Topology ContDiff


-- @@ L578-578 verbatim
namespace HarmonicCounterexample.Berger

-- @@ L579-579 verbatim
open Matrix

-- @@ L580-580 verbatim
variable {n : ℕ}


-- @@ L582-584 verbatim
def rawPolarEntry (J : ComplexStructure (Fin n)) (A B C : Space n → ℝ)
    (x : Space n) (i j : Fin n) : ℝ :=
  A x*(1:Mat n) i j+B x*x i*x j+C x*(J.matrix *ᵥ x) i*(J.matrix *ᵥ x) j


-- @@ L586-592 verbatim
def lowerConnectionCoeff (J : ComplexStructure (Fin n)) (x : Space n)
    (B C Ad Bd Cd : ℝ) (l i j : Fin n) : ℝ :=
  (Ad/2)*(x i*(1:Mat n) j l+x j*(1:Mat n) i l-x l*(1:Mat n) i j)+
  (Bd/2)*x i*x j*x l+B*(1:Mat n) i j*x l+
  (Cd/2)*(x i*(J.matrix *ᵥ x) j*(J.matrix *ᵥ x) l+
    x j*(J.matrix *ᵥ x) i*(J.matrix *ᵥ x) l-x l*(J.matrix *ᵥ x) i*(J.matrix *ᵥ x) j)+
  C*((J.matrix *ᵥ x) j*J.matrix l i+(J.matrix *ᵥ x) i*J.matrix l j)


-- @@ L594-620 verbatim
/-- First-kind Levi-Civita calculation, directly from coordinate derivatives. -/
lemma firstKind_rawPolar (J : ComplexStructure (Fin n))
    {A B C : Space n → ℝ} {x : Space n} {Ad Bd Cd : ℝ}
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x)
    (hC : DifferentiableAt ℝ C x)
    (hAd : ∀ i, coordDeriv i A x = Ad*x i)
    (hBd : ∀ i, coordDeriv i B x = Bd*x i)
    (hCd : ∀ i, coordDeriv i C x = Cd*x i)
    (l i j : Fin n) :
    (1/2:ℝ)*(coordDeriv i (fun y => rawPolarEntry J A B C y j l) x+
      coordDeriv j (fun y => rawPolarEntry J A B C y i l) x-
      coordDeriv l (fun y => rawPolarEntry J A B C y i j) x) =
      lowerConnectionCoeff J x (B x) (C x) Ad Bd Cd l i j := by
  have hJ (k : Fin n) := differentiableAt_linear_entry J.matrix x k
  simp only [rawPolarEntry]
  simp (disch := fun_prop) only [coordDeriv_add, coordDeriv_mul, coordDeriv_const,
    coordDeriv_coordinate, coordDeriv_linear, hAd, hBd, hCd, mul_zero, zero_add]
  simp only [lowerConnectionCoeff, J.entry_skew i j, J.entry_skew l i,
    J.entry_skew l j, Matrix.one_apply]
  have hji : (if j=i then (1:ℝ) else 0) = (if i=j then (1:ℝ) else 0) := by
    simp only [eq_comm]
  have hli : (if l=i then (1:ℝ) else 0) = (if i=l then (1:ℝ) else 0) := by
    simp only [eq_comm]
  have hlj : (if l=j then (1:ℝ) else 0) = (if j=l then (1:ℝ) else 0) := by
    simp only [eq_comm]
  simp only [hji, hli, hlj]
  ring


-- @@ L622-622 verbatim
end HarmonicCounterexample.Berger


-- @@ L624-624 verbatim
end


-- @@ L626-626 verbatim
noncomputable section

-- @@ L627-627 verbatim
open Filter MeasureTheory

-- @@ L628-628 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L629-629 verbatim
open Matrix

-- @@ L630-630 verbatim
open scoped BigOperators

-- @@ L631-631 verbatim
open Matrix

-- @@ L632-632 verbatim
open scoped BigOperators

-- @@ L633-633 verbatim
open Filter Matrix

-- @@ L634-634 verbatim
open scoped BigOperators Topology ContDiff


-- @@ L636-636 verbatim
namespace HarmonicCounterexample.Berger

-- @@ L637-637 verbatim
open Matrix

-- @@ L638-638 verbatim
variable {n : ℕ}


-- @@ L640-663 verbatim
lemma lowerConnection_radial (J : ComplexStructure (Fin n)) (x : Space n)
    (B C Ad Bd Cd : ℝ) (i j : Fin n) :
    x ⬝ᵥ (fun l => lowerConnectionCoeff J x B C Ad Bd Cd l i j) =
      (Ad+Bd*(x ⬝ᵥ x)/2)*x i*x j+(B-Ad/2)*(x ⬝ᵥ x)*(1:Mat n) i j-
        (Cd*(x ⬝ᵥ x)/2+2*C)*(J.matrix *ᵥ x) i*(J.matrix *ᵥ x) j := by
  change (∑ l, x l*lowerConnectionCoeff J x B C Ad Bd Cd l i j) = _
  calc
    _ = ∑ l, ((Ad*x i/2)*((1:Mat n) j l*x l)+(Ad*x j/2)*((1:Mat n) i l*x l)+
      ((B-Ad/2)*(1:Mat n) i j+Bd*x i*x j/2-Cd*(J.matrix *ᵥ x) i*(J.matrix *ᵥ x) j/2)*(x l*x l)+
      (Cd/2*(x i*(J.matrix *ᵥ x) j+x j*(J.matrix *ᵥ x) i))*(x l*(J.matrix *ᵥ x) l)+
      (C*(J.matrix *ᵥ x) j)*(x l*J.matrix l i)+
      (C*(J.matrix *ᵥ x) i)*(x l*J.matrix l j)) := by
      apply Finset.sum_congr rfl
      intro l _
      simp only [lowerConnectionCoeff]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [J.sum_x_entry, J.sum_x_entry]
      change _ + _ + _*(x ⬝ᵥ x) + _*(x ⬝ᵥ (J.matrix *ᵥ x)) + _ + _ = _
      rw [J.orthogonal_radial]
      simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true, mul_zero, add_zero]
      ring


-- @@ L665-691 verbatim
lemma lowerConnection_hopf (J : ComplexStructure (Fin n)) (x : Space n)
    (B C Ad Bd Cd : ℝ) (i j : Fin n) :
    (J.matrix *ᵥ x) ⬝ᵥ (fun l => lowerConnectionCoeff J x B C Ad Bd Cd l i j) =
      (Ad/2+Cd*(x ⬝ᵥ x)/2+C)*(x i*(J.matrix *ᵥ x) j+x j*(J.matrix *ᵥ x) i) := by
  change (∑ l, (J.matrix *ᵥ x) l*lowerConnectionCoeff J x B C Ad Bd Cd l i j) = _
  calc
    _ = ∑ l, ((Ad*x i/2)*((1:Mat n) j l*(J.matrix *ᵥ x) l)+
      (Ad*x j/2)*((1:Mat n) i l*(J.matrix *ᵥ x) l)+
      ((B-Ad/2)*(1:Mat n) i j+Bd*x i*x j/2-Cd*(J.matrix *ᵥ x) i*(J.matrix *ᵥ x) j/2)*
        (x l*(J.matrix *ᵥ x) l)+
      (Cd/2*(x i*(J.matrix *ᵥ x) j+x j*(J.matrix *ᵥ x) i))*
        ((J.matrix *ᵥ x) l*(J.matrix *ᵥ x) l)+
      (C*(J.matrix *ᵥ x) j)*((J.matrix *ᵥ x) l*J.matrix l i)+
      (C*(J.matrix *ᵥ x) i)*((J.matrix *ᵥ x) l*J.matrix l j)) := by
      apply Finset.sum_congr rfl
      intro l _
      simp only [lowerConnectionCoeff]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [J.sum_w_entry, J.sum_w_entry]
      change _ + _ + _*(x ⬝ᵥ (J.matrix *ᵥ x)) +
        _*((J.matrix *ᵥ x) ⬝ᵥ (J.matrix *ᵥ x)) + _ + _ = _
      rw [J.orthogonal_radial, J.preserves_dot]
      simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_univ, ite_true, mul_zero, add_zero]
      ring


-- @@ L693-713 verbatim
/-- Raising the first-kind expression gives exactly the six invariant scalar
coefficients; this is an algebra theorem, not a curvature assumption. -/
lemma raise_lowerConnection (J : ComplexStructure (Fin n)) (x : Space n)
    (hx : x ⬝ᵥ x ≠ 0) (A D B C Ad Bd Cd : ℝ) (k i j : Fin n) :
    (∑ l, polarTensor J x A⁻¹ D⁻¹ k l*lowerConnectionCoeff J x B C Ad Bd Cd l i j) =
    connectionCoeff J x (Ad/(2*A)) (B-Ad/2)
      (Ad*(1-A⁻¹)/(x ⬝ᵥ x)+Bd/2)
      (Ad*(D⁻¹-A⁻¹)/(2*(x ⬝ᵥ x))+Cd/(2*D)+C*(D⁻¹-A⁻¹)/(x ⬝ᵥ x))
      (-Cd/2-2*C*(1-A⁻¹)/(x ⬝ᵥ x)) (C/A) k i j := by
  change (polarTensor J x A⁻¹ D⁻¹ *ᵥ
    (fun l => lowerConnectionCoeff J x B C Ad Bd Cd l i j)) k = _
  rw [polarTensor_mulVec, lowerConnection_radial, lowerConnection_hopf]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, lowerConnectionCoeff,
    connectionCoeff, div_eq_mul_inv, _root_.mul_inv_rev]
  have h₁ : (1:Mat n) j k = (1:Mat n) k j := by simp [Matrix.one_apply, eq_comm]
  have h₂ : (1:Mat n) i k = (1:Mat n) k i := by simp [Matrix.one_apply, eq_comm]
  rw [h₁, h₂]
  generalize A⁻¹ = Ai
  generalize D⁻¹ = Di
  field_simp [hx]
  ring


-- @@ L715-715 verbatim
end HarmonicCounterexample.Berger


-- @@ L717-717 verbatim
end


-- @@ L719-719 verbatim
noncomputable section

-- @@ L720-720 verbatim
open Filter MeasureTheory

-- @@ L721-721 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L722-722 verbatim
open Matrix

-- @@ L723-723 verbatim
open scoped BigOperators

-- @@ L724-724 verbatim
open Matrix

-- @@ L725-725 verbatim
open scoped BigOperators

-- @@ L726-726 verbatim
open Filter Matrix

-- @@ L727-727 verbatim
open scoped BigOperators Topology ContDiff


-- @@ L729-729 verbatim
namespace HarmonicCounterexample.Berger

-- @@ L730-730 verbatim
open Matrix

-- @@ L731-731 verbatim
variable {n : ℕ}


-- @@ L733-777 verbatim
/-- The actual Levi-Civita connection is computed from locally given Cartesian
metric entries. The only assumptions are differentiability and the polar tensor
identities, not any curvature or connection formula. -/
theorem christoffel_of_rawPolar (g : SmoothMetric n) (J : ComplexStructure (Fin n))
    {A B C : Space n → ℝ} {x : Space n} {D Ad Bd Cd : ℝ}
    (hcoeff : ∀ᶠ y in 𝓝 x, ∀ i j, g.coeff y i j = rawPolarEntry J A B C y i j)
    (hx : x ⬝ᵥ x ≠ 0) (hA0 : A x ≠ 0) (hD0 : D ≠ 0)
    (hBval : B x = (1-A x)/(x ⬝ᵥ x)) (hCval : C x = (D-A x)/(x ⬝ᵥ x))
    (hA : DifferentiableAt ℝ A x) (hB : DifferentiableAt ℝ B x)
    (hC : DifferentiableAt ℝ C x)
    (hAd : ∀ i, coordDeriv i A x = Ad*x i)
    (hBd : ∀ i, coordDeriv i B x = Bd*x i)
    (hCd : ∀ i, coordDeriv i C x = Cd*x i)
    (k i j : Fin n) :
    christoffel g x k i j =
    connectionCoeff J x (Ad/(2*A x)) (B x-Ad/2)
      (Ad*(1-(A x)⁻¹)/(x ⬝ᵥ x)+Bd/2)
      (Ad*(D⁻¹-(A x)⁻¹)/(2*(x ⬝ᵥ x))+Cd/(2*D)+C x*(D⁻¹-(A x)⁻¹)/(x ⬝ᵥ x))
      (-Cd/2-2*C x*(1-(A x)⁻¹)/(x ⬝ᵥ x)) (C x/A x) k i j := by
  have hval := hcoeff.self_of_nhds
  have hgx : g.coeff x = polarTensor J x (A x) D := by
    ext l v
    rw [hval, rawPolarEntry, hBval, hCval]
    simp only [polarTensor, Matrix.add_apply, Matrix.smul_apply,
      Matrix.vecMulVec_apply, smul_eq_mul]
    ring
  have hdiff (l i j : Fin n) :
      coordDeriv l (fun y => g.coeff y i j) x =
      coordDeriv l (fun y => rawPolarEntry J A B C y i j) x :=
    coordDeriv_congr (hcoeff.mono fun y hy => hy i j) l
  unfold christoffel
  rw [hgx, polarTensor_inverse J hx hA0 hD0]
  simp only [hdiff]
  calc
    _ = ∑ l, polarTensor J x (A x)⁻¹ D⁻¹ k l *
        ((1/2:ℝ)*(coordDeriv i (fun y => rawPolarEntry J A B C y j l) x+
          coordDeriv j (fun y => rawPolarEntry J A B C y i l) x-
          coordDeriv l (fun y => rawPolarEntry J A B C y i j) x)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by
      simp only [firstKind_rawPolar J hA hB hC hAd hBd hCd]
      exact raise_lowerConnection J x hx _ _ _ _ _ _ _ k i j


-- @@ L779-779 verbatim
end HarmonicCounterexample.Berger


-- @@ L781-781 verbatim
end


-- @@ L783-783 verbatim
noncomputable section

-- @@ L784-784 verbatim
open Filter MeasureTheory

-- @@ L785-785 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L786-786 verbatim
open Matrix

-- @@ L787-787 verbatim
open scoped BigOperators

-- @@ L788-788 verbatim
open Matrix

-- @@ L789-789 verbatim
open scoped BigOperators

-- @@ L790-790 verbatim
open Filter Matrix

-- @@ L791-791 verbatim
open scoped BigOperators Topology ContDiff


-- @@ L793-793 verbatim
namespace HarmonicCounterexample.Berger

-- @@ L794-794 verbatim
open Matrix

-- @@ L795-795 verbatim
variable {n : ℕ}


-- @@ L797-797 verbatim
def normalAlpha (S h : ℝ) : ℝ := h/S

-- @@ L798-798 verbatim
def normalBeta (S A h : ℝ) : ℝ := (1-A*(1+h))/S

-- @@ L799-799 verbatim
def normalGamma (S A h : ℝ) : ℝ := (A*(1+h)-1-2*h)/S^2

-- @@ L800-800 verbatim
def normalDelta (S q p : ℝ) : ℝ := (1-q+p)/S^2

-- @@ L801-801 verbatim
def normalEpsilon (S A q h p : ℝ) : ℝ := (A*(1+h)-A*q*(1+h+p)+2*(q-1))/S^2

-- @@ L802-802 verbatim
def normalZeta (S q : ℝ) : ℝ := (q-1)/S


-- @@ L804-808 verbatim
def normalizedConnectionCoeff (J : ComplexStructure (Fin n)) (x : Space n)
    (A q h p : ℝ) (k i j : Fin n) : ℝ :=
  connectionCoeff J x (normalAlpha (x ⬝ᵥ x) h) (normalBeta (x ⬝ᵥ x) A h)
    (normalGamma (x ⬝ᵥ x) A h) (normalDelta (x ⬝ᵥ x) q p)
    (normalEpsilon (x ⬝ᵥ x) A q h p) (normalZeta (x ⬝ᵥ x) q) k i j


-- @@ L810-823 verbatim
lemma normalize_connection (J : ComplexStructure (Fin n)) {x : Space n}
    (hS : x ⬝ᵥ x ≠ 0) {A q : ℝ} (hA : A ≠ 0) (hq : q ≠ 0)
    (h p : ℝ) (k i j : Fin n) :
    connectionCoeff J x ((2*A*h/(x ⬝ᵥ x))/(2*A))
      ((1-A)/(x ⬝ᵥ x)-(2*A*h/(x ⬝ᵥ x))/2)
      ((2*A*h/(x ⬝ᵥ x))*(1-A⁻¹)/(x ⬝ᵥ x)+(-2*A*h-2+2*A)/(x ⬝ᵥ x)^2/2)
      ((2*A*h/(x ⬝ᵥ x))*((A*q)⁻¹-A⁻¹)/(2*(x ⬝ᵥ x))+
        (2*A*(q*(h+p)-h-q+1)/(x ⬝ᵥ x)^2)/(2*(A*q))+
        (A*(q-1)/(x ⬝ᵥ x))*((A*q)⁻¹-A⁻¹)/(x ⬝ᵥ x))
      (-(2*A*(q*(h+p)-h-q+1)/(x ⬝ᵥ x)^2)/2-
        2*(A*(q-1)/(x ⬝ᵥ x))*(1-A⁻¹)/(x ⬝ᵥ x))
      ((A*(q-1)/(x ⬝ᵥ x))/A) k i j = normalizedConnectionCoeff J x A q h p k i j := by
  unfold normalizedConnectionCoeff normalAlpha normalBeta normalGamma normalDelta normalEpsilon normalZeta
  congr 1 <;> field_simp <;> ring


-- @@ L825-828 verbatim
lemma differentiableAt_radialSquare (x : Space n) :
    DifferentiableAt ℝ (fun y : Space n => y ⬝ᵥ y) x := by
  unfold dotProduct
  fun_prop


-- @@ L830-863 verbatim
/-- Actual normalized Christoffel producer from first derivatives of the metric
profiles. Here h=(log A)'/2 and p=(log q)'/2 in logarithmic radius. -/
theorem christoffel_normalized (g : SmoothMetric n) (J : ComplexStructure (Fin n))
    {A q : Space n → ℝ} {x : Space n} {h p : ℝ}
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ i j, g.coeff y i j =
      rawPolarEntry J A (fun z => (1-A z)/(z ⬝ᵥ z))
        (fun z => A z*(q z-1)/(z ⬝ᵥ z)) y i j)
    (hS : x ⬝ᵥ x ≠ 0) (hA0 : A x ≠ 0) (hq0 : q x ≠ 0)
    (hA : DifferentiableAt ℝ A x) (hq : DifferentiableAt ℝ q x)
    (hAd : ∀ i, coordDeriv i A x = (2*A x*h/(x ⬝ᵥ x))*x i)
    (hqd : ∀ i, coordDeriv i q x = (2*q x*p/(x ⬝ᵥ x))*x i)
    (k i j : Fin n) :
    christoffel g x k i j = normalizedConnectionCoeff J x (A x) (q x) h p k i j := by
  have hs := differentiableAt_radialSquare x
  have hB : DifferentiableAt ℝ (fun y => (1-A y)/(y ⬝ᵥ y)) x :=
    by fun_prop (disch := assumption)
  have hC : DifferentiableAt ℝ (fun y => A y*(q y-1)/(y ⬝ᵥ y)) x :=
    by fun_prop (disch := assumption)
  have hBd (l : Fin n) : coordDeriv l (fun y => (1-A y)/(y ⬝ᵥ y)) x =
      ((-2*A x*h-2+2*A x)/(x ⬝ᵥ x)^2)*x l := by
    simp (disch := first | assumption | fun_prop) only [coordDeriv_div,
      coordDeriv_sub, coordDeriv_const, coordDeriv_radialSquare, hAd]
    field_simp
    ring
  have hCd (l : Fin n) : coordDeriv l (fun y => A y*(q y-1)/(y ⬝ᵥ y)) x =
      (2*A x*(q x*(h+p)-h-q x+1)/(x ⬝ᵥ x)^2)*x l := by
    simp (disch := first | assumption | fun_prop) only [coordDeriv_div,
      coordDeriv_mul, coordDeriv_sub, coordDeriv_const, coordDeriv_radialSquare, hAd, hqd]
    field_simp
    ring
  have hcval : A x*(q x-1)/(x ⬝ᵥ x) = (A x*q x-A x)/(x ⬝ᵥ x) := by ring
  rw [christoffel_of_rawPolar g J hmetric hS hA0 (mul_ne_zero hA0 hq0) rfl hcval
    hA hB hC hAd hBd hCd]
  exact normalize_connection J hS hA0 hq0 h p k i j


-- @@ L865-865 verbatim
end HarmonicCounterexample.Berger


-- @@ L867-867 verbatim
end


-- @@ L869-869 verbatim
noncomputable section

-- @@ L870-870 verbatim
open Filter MeasureTheory

-- @@ L871-871 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L872-872 verbatim
open Matrix

-- @@ L873-873 verbatim
open scoped BigOperators

-- @@ L874-874 verbatim
open Matrix

-- @@ L875-875 verbatim
open scoped BigOperators

-- @@ L876-876 verbatim
open Filter Matrix

-- @@ L877-877 verbatim
open scoped BigOperators Topology ContDiff


-- @@ L879-879 verbatim
namespace HarmonicCounterexample.Berger

-- @@ L880-880 verbatim
open Matrix

-- @@ L881-881 verbatim
variable {n : ℕ}


-- @@ L883-883 verbatim
def normalAlphaD (S u ud : ℝ) : ℝ := (ud-2*u)/S^2

-- @@ L884-884 verbatim
def normalBetaD (S A u ud : ℝ) : ℝ := (-2*A*u*(1+u)-A*ud-2*(1-A*(1+u)))/S^2

-- @@ L885-885 verbatim
def normalGammaD (S A u ud : ℝ) : ℝ := (2*A*u*(1+u)+A*ud-2*ud-4*(A*(1+u)-1-2*u))/S^3

-- @@ L886-886 verbatim
def normalDeltaD (S q v vd : ℝ) : ℝ := (-2*q*v+vd-4*(1-q+v))/S^3

-- @@ L887-887 verbatim
def normalEpsilonD (S A q u v ud vd : ℝ) : ℝ := (2*A*u*(1+u)+A*ud-2*A*q*(u+v)*(1+u+v)-A*q*(ud+vd)+4*q*v-4*(A*(1+u)-A*q*(1+u+v)+2*(q-1)))/S^3

-- @@ L888-888 verbatim
def normalZetaD (S q v : ℝ) : ℝ := (2*q*v-2*(q-1))/S^2


-- @@ L890-901 verbatim
lemma gradient_normalAlpha {u : Space n → ℝ} {x : Space n} {ud : ℝ}
    (hS : x ⬝ᵥ x ≠ 0)
    (hu : DifferentiableAt ℝ u x)
    (hdu : ∀ i, coordDeriv i u x = (ud)/(x ⬝ᵥ x)*x i)
    (i : Fin n) :
    coordDeriv i (fun y => normalAlpha (y ⬝ᵥ y) (u y)) x =
      normalAlphaD (x ⬝ᵥ x) (u x) ud*x i := by
  have hs := differentiableAt_radialSquare x
  simp only [normalAlpha, normalAlphaD]
  simp (disch := first | assumption | exact pow_ne_zero _ hS | fun_prop) only
    [coordDeriv_div, coordDeriv_radialSquare, hdu]
  field_simp


-- @@ L903-917 verbatim
lemma gradient_normalBeta {A u : Space n → ℝ} {x : Space n} {ud : ℝ}
    (hS : x ⬝ᵥ x ≠ 0)
    (hA : DifferentiableAt ℝ A x)
    (hu : DifferentiableAt ℝ u x)
    (hdA : ∀ i, coordDeriv i A x = (2*A x*u x)/(x ⬝ᵥ x)*x i)
    (hdu : ∀ i, coordDeriv i u x = (ud)/(x ⬝ᵥ x)*x i)
    (i : Fin n) :
    coordDeriv i (fun y => normalBeta (y ⬝ᵥ y) (A y) (u y)) x =
      normalBetaD (x ⬝ᵥ x) (A x) (u x) ud*x i := by
  have hs := differentiableAt_radialSquare x
  simp only [normalBeta, normalBetaD]
  simp (disch := first | assumption | exact pow_ne_zero _ hS | fun_prop) only
    [coordDeriv_div, coordDeriv_add, coordDeriv_sub, coordDeriv_mul, coordDeriv_const, coordDeriv_radialSquare, hdA, hdu]
  field_simp
  ring


-- @@ L919-933 verbatim
lemma gradient_normalGamma {A u : Space n → ℝ} {x : Space n} {ud : ℝ}
    (hS : x ⬝ᵥ x ≠ 0)
    (hA : DifferentiableAt ℝ A x)
    (hu : DifferentiableAt ℝ u x)
    (hdA : ∀ i, coordDeriv i A x = (2*A x*u x)/(x ⬝ᵥ x)*x i)
    (hdu : ∀ i, coordDeriv i u x = (ud)/(x ⬝ᵥ x)*x i)
    (i : Fin n) :
    coordDeriv i (fun y => normalGamma (y ⬝ᵥ y) (A y) (u y)) x =
      normalGammaD (x ⬝ᵥ x) (A x) (u x) ud*x i := by
  have hs := differentiableAt_radialSquare x
  simp only [normalGamma, normalGammaD]
  simp (disch := first | assumption | exact pow_ne_zero _ hS | fun_prop) only
    [coordDeriv_div, coordDeriv_pow, coordDeriv_add, coordDeriv_sub, coordDeriv_mul, coordDeriv_const, coordDeriv_radialSquare, hdA, hdu]
  field_simp
  ring


-- @@ L935-949 verbatim
lemma gradient_normalDelta {q v : Space n → ℝ} {x : Space n} {vd : ℝ}
    (hS : x ⬝ᵥ x ≠ 0)
    (hq : DifferentiableAt ℝ q x)
    (hv : DifferentiableAt ℝ v x)
    (hdq : ∀ i, coordDeriv i q x = (2*q x*v x)/(x ⬝ᵥ x)*x i)
    (hdv : ∀ i, coordDeriv i v x = (vd)/(x ⬝ᵥ x)*x i)
    (i : Fin n) :
    coordDeriv i (fun y => normalDelta (y ⬝ᵥ y) (q y) (v y)) x =
      normalDeltaD (x ⬝ᵥ x) (q x) (v x) vd*x i := by
  have hs := differentiableAt_radialSquare x
  simp only [normalDelta, normalDeltaD]
  simp (disch := first | assumption | exact pow_ne_zero _ hS | fun_prop) only
    [coordDeriv_div, coordDeriv_pow, coordDeriv_add, coordDeriv_sub, coordDeriv_const, coordDeriv_radialSquare, hdq, hdv]
  field_simp
  ring


-- @@ L951-969 verbatim
lemma gradient_normalEpsilon {A q u v : Space n → ℝ} {x : Space n} {ud vd : ℝ}
    (hS : x ⬝ᵥ x ≠ 0)
    (hA : DifferentiableAt ℝ A x)
    (hq : DifferentiableAt ℝ q x)
    (hu : DifferentiableAt ℝ u x)
    (hv : DifferentiableAt ℝ v x)
    (hdA : ∀ i, coordDeriv i A x = (2*A x*u x)/(x ⬝ᵥ x)*x i)
    (hdq : ∀ i, coordDeriv i q x = (2*q x*v x)/(x ⬝ᵥ x)*x i)
    (hdu : ∀ i, coordDeriv i u x = (ud)/(x ⬝ᵥ x)*x i)
    (hdv : ∀ i, coordDeriv i v x = (vd)/(x ⬝ᵥ x)*x i)
    (i : Fin n) :
    coordDeriv i (fun y => normalEpsilon (y ⬝ᵥ y) (A y) (q y) (u y) (v y)) x =
      normalEpsilonD (x ⬝ᵥ x) (A x) (q x) (u x) (v x) ud vd*x i := by
  have hs := differentiableAt_radialSquare x
  simp only [normalEpsilon, normalEpsilonD]
  simp (disch := first | assumption | exact pow_ne_zero _ hS | fun_prop) only
    [coordDeriv_div, coordDeriv_pow, coordDeriv_add, coordDeriv_sub, coordDeriv_mul, coordDeriv_const, coordDeriv_radialSquare, hdA, hdq, hdu, hdv]
  field_simp
  ring


-- @@ L971-983 verbatim
lemma gradient_normalZeta {q v : Space n → ℝ} {x : Space n}
    (hS : x ⬝ᵥ x ≠ 0)
    (hq : DifferentiableAt ℝ q x)
    (hdq : ∀ i, coordDeriv i q x = (2*q x*v x)/(x ⬝ᵥ x)*x i)
    (i : Fin n) :
    coordDeriv i (fun y => normalZeta (y ⬝ᵥ y) (q y)) x =
      normalZetaD (x ⬝ᵥ x) (q x) (v x)*x i := by
  have hs := differentiableAt_radialSquare x
  simp only [normalZeta, normalZetaD]
  simp (disch := first | assumption | exact pow_ne_zero _ hS | fun_prop) only
    [coordDeriv_div, coordDeriv_sub, coordDeriv_const, coordDeriv_radialSquare, hdq]
  field_simp
  ring


-- @@ L985-985 verbatim
end HarmonicCounterexample.Berger


-- @@ L987-987 verbatim
end


-- @@ L989-989 verbatim
noncomputable section

-- @@ L990-990 verbatim
open Filter MeasureTheory

-- @@ L991-991 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L992-992 verbatim
open Matrix

-- @@ L993-993 verbatim
open scoped BigOperators

-- @@ L994-994 verbatim
open Matrix

-- @@ L995-995 verbatim
open scoped BigOperators

-- @@ L996-996 verbatim
open Filter Matrix

-- @@ L997-997 verbatim
open scoped BigOperators Topology ContDiff


-- @@ L999-999 verbatim
namespace HarmonicCounterexample.Berger


-- @@ L1001-1001 verbatim
def normalTrace (N S u v : ℝ) : ℝ := ((N-1)*u+v)/S

-- @@ L1002-1002 verbatim
def normalTraceD (N S u v ud vd : ℝ) : ℝ := ((N-1)*ud+vd-2*((N-1)*u+v))/S^2


-- @@ L1004-1005 verbatim
def horizontalRicciNumerator (N A q u v ud : ℝ) : ℝ :=
  N-2*q-A*(ud+(N-2+(N-1)*u+v)*(1+u))

-- @@ L1006-1007 verbatim
def verticalRicciNumerator (N A q u v ud vd : ℝ) : ℝ :=
  (N-2)*q^2-A*q*(ud+vd+(N-2+(N-1)*u+v)*(1+u+v))

-- @@ L1008-1009 verbatim
def radialRicciNumerator (N u v ud vd : ℝ) : ℝ :=
  -((N-1)*(u+ud+u^2)+v+vd+2*u*v+v^2)


-- @@ L1011-1017 verbatim
lemma normalTrace_identity (N S A q u v : ℝ) (hS : S ≠ 0) :
    normalAlpha S u*(N+1)+normalBeta S A u+
      (normalGamma S A u+normalDelta S q v)*S+normalZeta S q =
      normalTrace N S u v := by
  unfold normalAlpha normalBeta normalGamma normalDelta normalZeta normalTrace
  field_simp
  ring


-- @@ L1019-1027 verbatim
lemma normalTraceD_identity (N S A q u v ud vd : ℝ) (hS : S ≠ 0) :
    normalAlphaD S u ud*(N+1)+normalBetaD S A u ud+
      (normalGammaD S A u ud+normalDeltaD S q v vd)*S+
      2*(normalGamma S A u+normalDelta S q v)+normalZetaD S q v =
      normalTraceD N S u v ud vd := by
  unfold normalAlphaD normalBetaD normalGammaD normalDeltaD normalZetaD
    normalGamma normalDelta normalTraceD
  field_simp
  ring


-- @@ L1029-1040 verbatim
lemma normalized_ricci_zero (N S A q u v ud : ℝ) (hS : S ≠ 0) :
    let a := normalAlpha S u
    let b := normalBeta S A u
    let f := normalZeta S q
    let bd := normalBetaD S A u ud
    let T := normalTrace N S u v
    2*a+N*b+bd*S-2*f-T+T*b*S-2*a*b*S =
      horizontalRicciNumerator N A q u v ud/S := by
  dsimp only
  unfold normalAlpha normalBeta normalZeta normalBetaD normalTrace horizontalRicciNumerator
  field_simp
  ring


-- @@ L1042-1059 verbatim
lemma normalized_ricci_one (N S A q u v ud vd : ℝ) (hS : S ≠ 0) :
    let a := normalAlpha S u
    let b := normalBeta S A u
    let c := normalGamma S A u
    let d := normalDelta S q v
    let f := normalZeta S q
    let ad := normalAlphaD S u ud
    let cd := normalGammaD S A u ud
    let T := normalTrace N S u v
    let Td := normalTraceD N S u v ud vd
    2*ad+cd*S+(N+2)*c-2*d-Td+T*(2*a+c*S)-
      ((2*a+b+c*S)^2+(a+d*S+f)^2+(N-2)*a^2-2*a*b) =
      (radialRicciNumerator N u v ud vd-horizontalRicciNumerator N A q u v ud)/S^2 := by
  dsimp only
  unfold normalAlpha normalBeta normalGamma normalDelta normalZeta normalAlphaD normalGammaD
    normalTrace normalTraceD radialRicciNumerator horizontalRicciNumerator
  field_simp
  ring


-- @@ L1061-1077 verbatim
lemma normalized_ricci_two (N S A q u v ud vd : ℝ) (hS : S ≠ 0) :
    let a := normalAlpha S u
    let b := normalBeta S A u
    let d := normalDelta S q v
    let e := normalEpsilon S A q u v
    let f := normalZeta S q
    let ed := normalEpsilonD S A q u v ud vd
    let fd := normalZetaD S q v
    let T := normalTrace N S u v
    2*d+ed*S+(N+2)*e-2*fd+T*(e*S-2*f)-
      (2*(a+d*S+f)*(b+e*S-2*f)-(N-2)*f^2-2*a*b) =
      (verticalRicciNumerator N A q u v ud vd-horizontalRicciNumerator N A q u v ud)/S^2 := by
  dsimp only
  unfold normalAlpha normalBeta normalDelta normalEpsilon normalZeta normalEpsilonD normalZetaD
    normalTrace verticalRicciNumerator horizontalRicciNumerator
  field_simp
  ring


-- @@ L1079-1079 verbatim
end HarmonicCounterexample.Berger


-- @@ L1081-1081 verbatim
end


-- @@ L1083-1083 verbatim
noncomputable section

-- @@ L1084-1084 verbatim
open Filter MeasureTheory

-- @@ L1085-1085 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L1086-1086 verbatim
open Matrix

-- @@ L1087-1087 verbatim
open scoped BigOperators

-- @@ L1088-1088 verbatim
open Matrix

-- @@ L1089-1089 verbatim
open scoped BigOperators

-- @@ L1090-1090 verbatim
open Filter Matrix

-- @@ L1091-1091 verbatim
open scoped BigOperators Topology ContDiff


-- @@ L1093-1093 verbatim
namespace HarmonicCounterexample.Berger

-- @@ L1094-1094 verbatim
open Matrix

-- @@ L1095-1095 verbatim
variable {n : ℕ}


-- @@ L1097-1147 verbatim
/-- Exact Cartesian Ricci coefficients for the Berger metric, in logarithmic
radial variables. All curvature operations use the frozen coordinate formula. -/
theorem ricci_normalized (g : SmoothMetric n) (J : ComplexStructure (Fin n))
    {A q u v : Space n → ℝ} {x : Space n} {ud vd : ℝ}
    (hΓ : ∀ᶠ y in 𝓝 x, ∀ k i j, christoffel g y k i j =
      normalizedConnectionCoeff J y (A y) (q y) (u y) (v y) k i j)
    (hS : x ⬝ᵥ x ≠ 0)
    (hA : DifferentiableAt ℝ A x) (hq : DifferentiableAt ℝ q x)
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (hdA : ∀ i, coordDeriv i A x = (2*A x*u x)/(x ⬝ᵥ x)*x i)
    (hdq : ∀ i, coordDeriv i q x = (2*q x*v x)/(x ⬝ᵥ x)*x i)
    (hdu : ∀ i, coordDeriv i u x = ud/(x ⬝ᵥ x)*x i)
    (hdv : ∀ i, coordDeriv i v x = vd/(x ⬝ᵥ x)*x i)
    (i j : Fin n) :
    ricci g x i j =
      horizontalRicciNumerator n (A x) (q x) (u x) (v x) ud/(x ⬝ᵥ x)*(1:Mat n) i j+
      (radialRicciNumerator n (u x) (v x) ud vd-
        horizontalRicciNumerator n (A x) (q x) (u x) (v x) ud)/(x ⬝ᵥ x)^2*x i*x j+
      (verticalRicciNumerator n (A x) (q x) (u x) (v x) ud vd-
        horizontalRicciNumerator n (A x) (q x) (u x) (v x) ud)/(x ⬝ᵥ x)^2*
          (J.matrix *ᵥ x) i*(J.matrix *ᵥ x) j := by
  have hs := differentiableAt_radialSquare x
  have ha : DifferentiableAt ℝ (fun y => normalAlpha (y ⬝ᵥ y) (u y)) x := by
    unfold normalAlpha
    fun_prop (disch := assumption)
  have hb : DifferentiableAt ℝ (fun y => normalBeta (y ⬝ᵥ y) (A y) (u y)) x := by
    unfold normalBeta
    fun_prop (disch := assumption)
  have hc : DifferentiableAt ℝ (fun y => normalGamma (y ⬝ᵥ y) (A y) (u y)) x := by
    unfold normalGamma
    fun_prop (disch := exact pow_ne_zero _ hS)
  have hd : DifferentiableAt ℝ (fun y => normalDelta (y ⬝ᵥ y) (q y) (v y)) x := by
    unfold normalDelta
    fun_prop (disch := exact pow_ne_zero _ hS)
  have he : DifferentiableAt ℝ (fun y => normalEpsilon (y ⬝ᵥ y) (A y) (q y) (u y) (v y)) x := by
    unfold normalEpsilon
    fun_prop (disch := exact pow_ne_zero _ hS)
  have hf : DifferentiableAt ℝ (fun y => normalZeta (y ⬝ᵥ y) (q y)) x := by
    unfold normalZeta
    fun_prop (disch := assumption)
  have h := ricci_of_connectionCoeff g J hΓ ha hb hc hd he hf
    (gradient_normalAlpha hS hu hdu) (gradient_normalBeta hS hA hu hdA hdu)
    (gradient_normalGamma hS hA hu hdA hdu) (gradient_normalDelta hS hq hv hdq hdv)
    (gradient_normalEpsilon hS hA hq hu hv hdA hdq hdu hdv)
    (gradient_normalZeta hS hq hdq) i j
  dsimp only at h
  rw [normalTrace_identity _ _ _ _ _ _ hS, normalTraceD_identity _ _ _ _ _ _ _ _ hS,
    normalized_ricci_zero _ _ _ _ _ _ _ hS,
    normalized_ricci_one _ _ _ _ _ _ _ _ hS,
    normalized_ricci_two _ _ _ _ _ _ _ _ hS] at h
  exact h


-- @@ L1149-1149 verbatim
end HarmonicCounterexample.Berger


-- @@ L1151-1151 verbatim
end


-- @@ L1153-1153 verbatim
noncomputable section

-- @@ L1154-1154 verbatim
open Filter MeasureTheory

-- @@ L1155-1155 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L1156-1156 verbatim
open Matrix

-- @@ L1157-1157 verbatim
open scoped BigOperators

-- @@ L1158-1158 verbatim
open Matrix

-- @@ L1159-1159 verbatim
open scoped BigOperators

-- @@ L1160-1160 verbatim
open Filter Matrix

-- @@ L1161-1161 verbatim
open scoped BigOperators Topology ContDiff


-- @@ L1163-1163 verbatim
namespace HarmonicCounterexample.Cartesian

-- @@ L1164-1164 verbatim
open Matrix Berger

-- @@ L1165-1165 verbatim
variable {n : ℕ}


-- @@ L1167-1175 verbatim
lemma coordDeriv_logRadius {x : Space n} (hx : x ≠ 0) (i : Fin n) :
    coordDeriv i logRadius x = x i/(x ⬝ᵥ x) := by
  have hS : x ⬝ᵥ x ≠ 0 := (squareRadius_pos hx).ne'
  unfold logRadius squareRadius
  rw [coordDeriv_mul (differentiableAt_const _)
    ((differentiableAt_radialSquare x).log hS), coordDeriv_const,
    coordDeriv_chain (differentiableAt_radialSquare x) (Real.hasDerivAt_log hS),
    coordDeriv_radialSquare]
  ring


-- @@ L1177-1182 verbatim
lemma coordDeriv_logProfile {f : ℝ → ℝ} {d : ℝ} {x : Space n}
    (hx : x ≠ 0) (hf : HasDerivAt f d (logRadius x)) (i : Fin n) :
    coordDeriv i (fun y => f (logRadius y)) x = d/(x ⬝ᵥ x)*x i := by
  rw [coordDeriv_chain ((logRadius_smoothAt hx).differentiableAt (by simp)) hf,
    coordDeriv_logRadius hx]
  ring


-- @@ L1184-1193 verbatim
lemma tensor_eq_rawPolar (J : ComplexStructure (Fin n)) {x : Space n}
    (hx : x ≠ 0) (A q : Space n → ℝ) (i j : Fin n) :
    tensor (radialUnit x) (hopfUnit J x) (A x) (q x) i j =
      rawPolarEntry J A (fun y => (1-A y)/(y ⬝ᵥ y))
        (fun y => A y*(q y-1)/(y ⬝ᵥ y)) x i j := by
  have hr := (radius_pos hx).ne'
  have hs : x ⬝ᵥ x = radius x^2 := (radius_sq x).symm
  simp only [tensor, radialUnit, hopfUnit, Matrix.add_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul, rawPolarEntry, hs]
  field_simp


-- @@ L1195-1220 verbatim
/-- Produces the actual Levi-Civita connection for logarithmic profiles, locally
in a fixed complex label (round gaps can use any label). -/
theorem christoffel_logProfiles (g : SmoothMetric n) (J : ComplexStructure (Fin n))
    {A q u v : ℝ → ℝ} {x : Space n} (hx : x ≠ 0)
    (hg : ∀ᶠ y in 𝓝 x, g.coeff y =
      tensor (radialUnit y) (hopfUnit J y) (A (logRadius y)) (q (logRadius y)))
    (hA : HasDerivAt A (2*A (logRadius x)*u (logRadius x)) (logRadius x))
    (hq : HasDerivAt q (2*q (logRadius x)*v (logRadius x)) (logRadius x))
    (hA0 : A (logRadius x) ≠ 0) (hq0 : q (logRadius x) ≠ 0)
    (k i j : Fin n) :
    christoffel g x k i j = normalizedConnectionCoeff J x
      (A (logRadius x)) (q (logRadius x)) (u (logRadius x)) (v (logRadius x)) k i j := by
  have hlog := (logRadius_smoothAt hx).differentiableAt (by simp)
  apply christoffel_normalized g J (A := fun y => A (logRadius y))
    (q := fun y => q (logRadius y))
  · filter_upwards [hg, isOpen_ne.mem_nhds hx] with y hy hy0
    intro i j
    rw [hy]
    exact tensor_eq_rawPolar J hy0 (fun z => A (logRadius z)) (fun z => q (logRadius z)) i j
  · exact (squareRadius_pos hx).ne'
  · exact hA0
  · exact hq0
  · exact hA.differentiableAt.comp x hlog
  · exact hq.differentiableAt.comp x hlog
  · exact coordDeriv_logProfile hx hA
  · exact coordDeriv_logProfile hx hq


-- @@ L1222-1257 verbatim
/-- Full Ricci formula from the Cartesian definition for a locally fixed Berger
label. It includes radial, Hopf and horizontal curvature with mixed terms zero. -/
theorem ricci_logProfiles (g : SmoothMetric n) (J : ComplexStructure (Fin n))
    {A q u v : ℝ → ℝ} {x : Space n} {ud vd : ℝ} (hx : x ≠ 0)
    (hg : ∀ᶠ y in 𝓝 x, g.coeff y =
      tensor (radialUnit y) (hopfUnit J y) (A (logRadius y)) (q (logRadius y)))
    (hA : ∀ t, HasDerivAt A (2*A t*u t) t)
    (hq : ∀ t, HasDerivAt q (2*q t*v t) t)
    (hA0 : ∀ t, A t ≠ 0) (hq0 : ∀ t, q t ≠ 0)
    (hu : HasDerivAt u ud (logRadius x)) (hv : HasDerivAt v vd (logRadius x))
    (i j : Fin n) :
    let t := logRadius x
    let S := x ⬝ᵥ x
    ricci g x i j =
      horizontalRicciNumerator n (A t) (q t) (u t) (v t) ud/S*(1:Mat n) i j+
      (radialRicciNumerator n (u t) (v t) ud vd-
        horizontalRicciNumerator n (A t) (q t) (u t) (v t) ud)/S^2*x i*x j+
      (verticalRicciNumerator n (A t) (q t) (u t) (v t) ud vd-
        horizontalRicciNumerator n (A t) (q t) (u t) (v t) ud)/S^2*
          (J.matrix *ᵥ x) i*(J.matrix *ᵥ x) j := by
  have hlog := (logRadius_smoothAt hx).differentiableAt (by simp)
  apply ricci_normalized g J (A := fun y => A (logRadius y))
    (q := fun y => q (logRadius y)) (u := fun y => u (logRadius y))
    (v := fun y => v (logRadius y))
  · filter_upwards [hg.eventually_nhds, isOpen_ne.mem_nhds hx] with y hy hy0
    intro k i j
    exact christoffel_logProfiles g J hy0 hy (hA _) (hq _) (hA0 _) (hq0 _) k i j
  · exact (squareRadius_pos hx).ne'
  · exact (hA _).differentiableAt.comp x hlog
  · exact (hq _).differentiableAt.comp x hlog
  · exact hu.differentiableAt.comp x hlog
  · exact hv.differentiableAt.comp x hlog
  · exact coordDeriv_logProfile hx (hA _)
  · exact coordDeriv_logProfile hx (hq _)
  · exact coordDeriv_logProfile hx hu
  · exact coordDeriv_logProfile hx hv


-- @@ L1259-1259 verbatim
end HarmonicCounterexample.Cartesian


-- @@ L1261-1261 verbatim
end


-- @@ L1263-1263 verbatim
noncomputable section

-- @@ L1264-1264 verbatim
open Filter MeasureTheory

-- @@ L1265-1265 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L1266-1266 verbatim
open Matrix

-- @@ L1267-1267 verbatim
open scoped BigOperators

-- @@ L1268-1268 verbatim
open Matrix

-- @@ L1269-1269 verbatim
open scoped BigOperators

-- @@ L1270-1270 verbatim
open Filter Matrix

-- @@ L1271-1271 verbatim
open scoped BigOperators Topology ContDiff


-- @@ L1273-1273 verbatim
namespace HarmonicCounterexample.Berger

-- @@ L1274-1274 verbatim
open Matrix

-- @@ L1275-1275 verbatim
variable {n : ℕ}


-- @@ L1277-1294 verbatim
lemma polar_quadratic (x z w : Space n) (a b c : ℝ) :
    (∑ i, ∑ j, (a*(1:Mat n) i j+b*x i*x j+c*z i*z j)*w i*w j) =
      a*(w ⬝ᵥ w)+b*(x ⬝ᵥ w)^2+c*(z ⬝ᵥ w)^2 := by
  calc
    _ = w ⬝ᵥ ((a • (1:Mat n)+b • vecMulVec x x+c • vecMulVec z z) *ᵥ w) := by
      simp only [dotProduct, mulVec, Matrix.add_apply, Matrix.smul_apply,
        Matrix.vecMulVec_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        Matrix.vecMulVec_mulVec, dotProduct_add, dotProduct_smul,
        MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, smul_eq_mul]
      rw [dotProduct_comm w x, dotProduct_comm w z]
      ring


-- @@ L1296-1301 verbatim
lemma radialRicci_shape (m b bd p pd : ℝ) (hm : m ≠ 0) :
    radialRicciNumerator (m+1) (b-p/m) p (bd-pd/m) pd =
      -m*(b+bd+b^2)-(m-1)/m*p^2 := by
  unfold radialRicciNumerator
  field_simp
  ring


-- @@ L1303-1307 verbatim
lemma horizontalRicci_round (m A b bd : ℝ) :
    horizontalRicciNumerator (m+1) A 1 b 0 bd =
      (m-1)*(1-A*(1+b)^2)-A*(b+bd+b^2) := by
  unfold horizontalRicciNumerator
  ring


-- @@ L1309-1313 verbatim
lemma verticalRicci_round (m A b bd : ℝ) :
    verticalRicciNumerator (m+1) A 1 b 0 bd 0 =
      horizontalRicciNumerator (m+1) A 1 b 0 bd := by
  unfold verticalRicciNumerator horizontalRicciNumerator
  ring


-- @@ L1315-1331 verbatim
lemma roundRicci_nonnegative {m A b bd : ℝ}
    (hm : 1 ≤ m) (hA : 0 ≤ A) (hA1 : A ≤ 1)
    (hb : -1 ≤ b) (hb0 : b ≤ 0) (hbd : b+bd+b^2 ≤ 0) :
    0 ≤ radialRicciNumerator (m+1) b 0 bd 0 ∧
    0 ≤ horizontalRicciNumerator (m+1) A 1 b 0 bd ∧
    0 ≤ verticalRicciNumerator (m+1) A 1 b 0 bd 0 := by
  have hg : (1+b)^2 ≤ 1 := by nlinarith
  have hAg : A*(1+b)^2 ≤ 1 :=
    (mul_le_mul_of_nonneg_left hg hA).trans (by simpa using hA1)
  have hpos : 0 ≤ (m-1)*(1-A*(1+b)^2)-A*(b+bd+b^2) := by
    exact sub_nonneg.2 (le_trans (mul_nonpos_of_nonneg_of_nonpos hA hbd)
      (mul_nonneg (by linarith) (by linarith)))
  refine ⟨?_, ?_, ?_⟩
  · unfold radialRicciNumerator
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (show 0 ≤ m by linarith) hbd]
  · rwa [horizontalRicci_round]
  · rwa [verticalRicci_round, horizontalRicci_round]


-- @@ L1333-1333 verbatim
end HarmonicCounterexample.Berger


-- @@ L1335-1335 verbatim
end


-- @@ L1337-1337 verbatim
noncomputable section

-- @@ L1338-1338 verbatim
open Filter MeasureTheory

-- @@ L1339-1339 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L1340-1340 verbatim
open Matrix

-- @@ L1341-1341 verbatim
open scoped BigOperators

-- @@ L1342-1342 verbatim
open Matrix

-- @@ L1343-1343 verbatim
open scoped BigOperators

-- @@ L1344-1344 verbatim
open Filter Matrix

-- @@ L1345-1345 verbatim
open scoped BigOperators Topology ContDiff


-- @@ L1347-1347 verbatim
namespace HarmonicCounterexample.Cartesian

-- @@ L1348-1348 verbatim
open Matrix Berger

-- @@ L1349-1349 verbatim
variable {n : ℕ}


-- @@ L1351-1375 verbatim
/-- Eigenvalue positivity implies nonnegative Ricci as the frozen bilinear form,
including all directions, not only radial or eigenvector test directions. -/
lemma polarCoefficients_nonnegative (J : ComplexStructure (Fin n))
    {x : Space n} (hx : x ≠ 0) {H R V : ℝ}
    (hH : 0 ≤ H) (hR : 0 ≤ R) (hV : 0 ≤ V) (w : Space n) :
    0 ≤ ∑ i, ∑ j, (H/(x ⬝ᵥ x)*(1:Mat n) i j+
      (R-H)/(x ⬝ᵥ x)^2*x i*x j+
      (V-H)/(x ⬝ᵥ x)^2*(J.matrix *ᵥ x) i*(J.matrix *ᵥ x) j)*w i*w j := by
  rw [polar_quadratic]
  have hb := two_vector_bessel (radialUnit_unit hx) (hopfUnit_unit J hx)
    (radial_hopf_orthogonal J x) w
  have hr := (radius_pos hx).ne'
  have hS : 0 < x ⬝ᵥ x := squareRadius_pos hx
  have hs : x ⬝ᵥ x = radius x^2 := (radius_sq x).symm
  have heq : H/(x ⬝ᵥ x)*(w ⬝ᵥ w)+(R-H)/(x ⬝ᵥ x)^2*(x ⬝ᵥ w)^2+
      (V-H)/(x ⬝ᵥ x)^2*((J.matrix *ᵥ x) ⬝ᵥ w)^2 =
      (H*((w ⬝ᵥ w)-(radialUnit x ⬝ᵥ w)^2-(hopfUnit J x ⬝ᵥ w)^2)+
        R*(radialUnit x ⬝ᵥ w)^2+V*(hopfUnit J x ⬝ᵥ w)^2)/(x ⬝ᵥ x) := by
    simp only [radialUnit, hopfUnit, smul_dotProduct, smul_eq_mul, hs]
    field_simp
    ring
  rw [heq]
  apply div_nonneg _ hS.le
  exact add_nonneg (add_nonneg (mul_nonneg hH (by linarith))
    (mul_nonneg hR (sq_nonneg _))) (mul_nonneg hV (sq_nonneg _))


-- @@ L1377-1377 verbatim
end HarmonicCounterexample.Cartesian


-- @@ L1379-1379 verbatim
end


-- @@ L1381-1381 verbatim
noncomputable section

-- @@ L1382-1382 verbatim
open Filter MeasureTheory

-- @@ L1383-1383 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L1384-1384 verbatim
open Matrix

-- @@ L1385-1385 verbatim
open scoped BigOperators

-- @@ L1386-1386 verbatim
open Matrix

-- @@ L1387-1387 verbatim
open scoped BigOperators

-- @@ L1388-1388 verbatim
open Filter Matrix

-- @@ L1389-1389 verbatim
open scoped BigOperators Topology ContDiff


-- @@ L1391-1391 verbatim
namespace HarmonicCounterexample.Berger


-- @@ L1393-1413 verbatim
lemma radial_scalar_budget {m μ x C b bd p pd : ℝ}
    (hm : 1 ≤ m) (hx : 0 < x)
    (hc : 64*C^2 ≤ m*μ*x^2)
    (hb : b+bd+b^2 ≤ -μ/(64*x^10)) (hp : |p| ≤ C/x^6) :
    0 ≤ radialRicciNumerator (m+1) (b-p/m) p (bd-pd/m) pd := by
  have hm0 : 0 < m := by linarith
  rw [radialRicci_shape _ _ _ _ _ hm0.ne']
  have hp2 : p^2 ≤ C^2/x^12 := by
    have hh := (sq_le_sq₀ (abs_nonneg p) ((abs_nonneg _).trans hp)).2 hp
    simpa only [sq_abs, div_pow, ← pow_mul] using hh
  have hb2 : C^2/x^12 ≤ m*μ/(64*x^10) := by
    apply (div_le_div_iff₀ (pow_pos hx _) (by positivity : 0 < 64*x^10)).2
    have hh := mul_le_mul_of_nonneg_right hc (pow_nonneg hx.le 10)
    nlinarith only [hh]
  have hf : (m-1)/m ≤ 1 := (div_le_one hm0).2 (by linarith)
  have hf0 : 0 ≤ (m-1)/m := div_nonneg (by linarith) hm0.le
  have hh := mul_le_mul_of_nonneg_right hf (sq_nonneg p)
  have hr := mul_le_mul_of_nonneg_left hb hm0.le
  have he : m*(-μ/(64*x^10)) = -(m*μ/(64*x^10)) := by ring
  rw [he] at hr
  nlinarith


-- @@ L1415-1415 verbatim
end HarmonicCounterexample.Berger


-- @@ L1417-1417 verbatim
end


-- @@ L1419-1419 verbatim
end OAI
