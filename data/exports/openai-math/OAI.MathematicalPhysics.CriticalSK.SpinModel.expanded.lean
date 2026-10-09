import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators Topology NNReal ENNReal


-- @@ L9-9 verbatim
open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

-- @@ L10-10 verbatim
open Set Metric MeasureTheory MeasureTheory.Measure

-- @@ L11-11 verbatim
open MeasureTheory ProbabilityTheory

-- @@ L12-12 verbatim
open scoped ENNReal NNReal

-- @@ L13-13 verbatim
open scoped BigOperators InnerProductSpace

-- @@ L14-14 verbatim
open Module

-- @@ L15-15 verbatim
open scoped BigOperators ENNReal NNReal Real Topology

-- @@ L16-16 verbatim
open MeasureTheory ProbabilityTheory Filter

-- @@ L17-17 verbatim
open scoped BigOperators NNReal

-- @@ L18-18 verbatim
open scoped BigOperators

-- @@ L19-19 verbatim
open Matrix Polynomial

-- @@ L20-20 verbatim
open scoped BigOperators Topology

-- @@ L21-21 verbatim
open Filter

-- @@ L22-22 verbatim
namespace CriticalSK


-- @@ L24-24 verbatim
section


-- @@ L26-26 verbatim
abbrev Spin (n : ℕ) := Fin n → Bool


-- @@ L28-28 verbatim
abbrev Edge (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}


-- @@ L30-30 verbatim
abbrev Disorder (n : ℕ) := Edge n → ℝ


-- @@ L32-32 verbatim
def spinValue (b : Bool) : ℝ := if b then 1 else -1


-- @@ L34-35 verbatim
def hamiltonian {n : ℕ} (W : Disorder n) (x : Spin n) : ℝ :=
  ∑ e : Edge n, W e * spinValue (x e.val.1) * spinValue (x e.val.2)


-- @@ L37-38 verbatim
def partition {n : ℕ} (W : Disorder n) : ℝ :=
  ∑ x : Spin n, Real.exp (hamiltonian W x)


-- @@ L40-41 verbatim
def gibbs {n : ℕ} (W : Disorder n) (x : Spin n) : ℝ :=
  Real.exp (hamiltonian W x) / partition W


-- @@ L43-44 verbatim
def disorderLaw (n : ℕ) : Measure (Disorder n) :=
  Measure.pi fun _ : Edge n => gaussianReal 0 (n : ℝ≥0)⁻¹


-- @@ L46-47 verbatim
def sameExcept {n : ℕ} (i : Fin n) (x y : Spin n) : Prop :=
  ∀ j, j ≠ i → y j = x j


-- @@ L49-50 verbatim
instance {n : ℕ} (i : Fin n) (x y : Spin n) : Decidable (sameExcept i x y) :=
  Classical.propDecidable _


-- @@ L52-55 verbatim
def siteKernel {n : ℕ} (W : Disorder n) (i : Fin n) : Matrix (Spin n) (Spin n) ℝ :=
  fun x y => if sameExcept i x y then
    gibbs W y / (∑ z : Spin n, if sameExcept i x z then gibbs W z else 0)
  else 0


-- @@ L57-58 verbatim
def discreteKernel {n : ℕ} (W : Disorder n) : Matrix (Spin n) (Spin n) ℝ :=
  (n : ℝ)⁻¹ • ∑ i : Fin n, siteKernel W i


-- @@ L60-61 verbatim
def generator {n : ℕ} (W : Disorder n) : Matrix (Spin n) (Spin n) ℝ :=
  ∑ i : Fin n, (siteKernel W i - 1)


-- @@ L63-65 verbatim
def continuousKernel {n : ℕ} (W : Disorder n) (t : ℝ) :
    Matrix (Spin n) (Spin n) ℝ :=
  NormedSpace.exp (t • generator W)


-- @@ L67-68 verbatim
def totalVariation {n : ℕ} (W : Disorder n) (p : Spin n → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ y : Spin n, |p y - gibbs W y|


-- @@ L70-71 verbatim
def continuousDistance {n : ℕ} (W : Disorder n) (t : ℝ) (x : Spin n) : ℝ :=
  totalVariation W (continuousKernel W t x)


-- @@ L73-74 verbatim
def discreteDistance {n : ℕ} (W : Disorder n) (k : ℕ) (x : Spin n) : ℝ :=
  totalVariation W ((discreteKernel W ^ k) x)


-- @@ L76-77 verbatim
def continuousMixingTime {n : ℕ} (W : Disorder n) : ℝ :=
  sInf {t : ℝ | 0 ≤ t ∧ ∀ x, continuousDistance W t x ≤ 1 / 4}


-- @@ L79-80 verbatim
def discreteMixingTime {n : ℕ} (W : Disorder n) : ℕ :=
  sInf {k : ℕ | ∀ x, discreteDistance W k x ≤ 1 / 4}


-- @@ L82-83 verbatim
def mean {n : ℕ} (W : Disorder n) (f : Spin n → ℝ) : ℝ :=
  ∑ x : Spin n, gibbs W x * f x


-- @@ L85-86 verbatim
def variance {n : ℕ} (W : Disorder n) (f : Spin n → ℝ) : ℝ :=
  mean W (fun x => (f x - mean W f) ^ 2)


-- @@ L88-89 verbatim
def dirichlet {n : ℕ} (W : Disorder n) (f : Spin n → ℝ) : ℝ :=
  ∑ i : Fin n, mean W (fun x => (f x - ∑ y : Spin n, siteKernel W i x y * f y) ^ 2)


-- @@ L91-92 verbatim
def linearObservable {n : ℕ} (a : Fin n → ℝ) (x : Spin n) : ℝ :=
  ∑ i : Fin n, a i * spinValue (x i)


-- @@ L94-97 verbatim
def covariance {n : ℕ} (W : Disorder n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => mean W (fun x =>
    (spinValue (x i) - mean W (fun y => spinValue (y i))) *
    (spinValue (x j) - mean W (fun y => spinValue (y j))))


-- @@ L99-100 verbatim
def covarianceNorm {n : ℕ} (W : Disorder n) : ℝ :=
  ‖(covariance W).toEuclideanLin.toContinuousLinearMap‖


-- @@ L102-104 verbatim
def linearRayleigh {n : ℕ} (W : Disorder n) : ℝ :=
  sSup {r : ℝ | ∃ a : Fin n → ℝ, a ≠ 0 ∧
    r = variance W (linearObservable a) / dirichlet W (linearObservable a)}


-- @@ L106-107 verbatim
def continuousGoodMass {n : ℕ} (W : Disorder n) (t : ℝ) : ℝ :=
  ∑ x : Spin n, if 1 / 4 < continuousDistance W t x then gibbs W x else 0


-- @@ L109-110 verbatim
def discreteGoodMass {n : ℕ} (W : Disorder n) (k : ℕ) : ℝ :=
  ∑ x : Spin n, if 1 / 4 < discreteDistance W k x then gibbs W x else 0


-- @@ L112-112 verbatim
variable {n : ℕ} (W : Disorder n)


-- @@ L114-115 verbatim
@[simp] lemma spinValue_sq (b : Bool) : spinValue b ^ 2 = 1 := by
  cases b <;> norm_num [spinValue]


-- @@ L117-117 verbatim
end


-- @@ L119-119 verbatim
section


-- @@ L121-122 verbatim
def cubeVector {n : ℕ} (x : Spin n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => spinValue (x i))


-- @@ L124-124 verbatim
def cubeOverlap {n : ℕ} (x y : Spin n) : ℝ := inner ℝ (cubeVector x) (cubeVector y) / n


-- @@ L126-127 verbatim
instance {n : ℕ} (i : Fin n) (x y : Spin n) : Decidable (sameExcept i x y) :=
  Classical.propDecidable _


-- @@ L129-130 verbatim
instance {n : ℕ} (i : Fin n) (x y : Spin n) : Decidable (sameExcept i x y) :=
  Classical.propDecidable _


-- @@ L132-132 verbatim
open Set MeasureTheory


-- @@ L134-135 verbatim
def gibbsOverlap {n : ℕ} (W : Disorder n) : ℝ :=
  ∑ x : Spin n, ∑ y : Spin n, gibbs W x*gibbs W y*(cubeOverlap x y)^2


-- @@ L137-137 verbatim
end


-- @@ L139-140 verbatim
instance {n : ℕ} (i : Fin n) (x y : Spin n) : Decidable (sameExcept i x y) :=
  Classical.propDecidable _


-- @@ L142-142 verbatim
end CriticalSK


-- @@ L144-144 verbatim
end


-- @@ L146-146 verbatim
end OAI
