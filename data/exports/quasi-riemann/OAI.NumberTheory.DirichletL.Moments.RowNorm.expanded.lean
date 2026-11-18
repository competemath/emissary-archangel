import OAI.NumberTheory.DirichletL.Moments.Initial
import OAI.NumberTheory.DirichletL.Moments.Cauchy


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentRowNorm

-- @@ L9-9 verbatim
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson

-- @@ L10-10 verbatim
open CanonicalRowCompletion CanonicalQuadraticSieve

-- @@ L11-11 verbatim
open CenteredMomentCorrelation CenteredMomentFourier CenteredMomentSupportedCorrelation

-- @@ L12-12 verbatim
open CenteredMomentCommonSupport

-- @@ L13-13 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L15-19 verbatim
def pairResidue (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (x : Residue (a * b)) : ℂ :=
  supportedModulusCharacter a ha (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
    star (supportedModulusCharacter b hb
      (frequencyReduction b (a * b) (dvd_mul_left b a) x))


-- @@ L21-25 verbatim
@[simp] theorem pairResidue_mk (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (z : O) :
    pairResidue a b ha hb (Ideal.Quotient.mk _ z) =
      idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b})) := by
  simp only [pairResidue, frequencyReduction_mk, supportedModulusCharacter_mk]


-- @@ L27-31 verbatim
def pairFourier (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (h : O) : ℂ :=
  ∑' x : Residue (a * b), pairResidue a b ha hb x *
    quotientTrace (a * b) (mul_ne_zero (supported_element_ne_zero a ha)
      (supported_element_ne_zero b hb)) (Ideal.Quotient.mk _ h * x)


-- @@ L33-43 verbatim
theorem row_pair_summable (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O =>
      (idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b}))) *
        W (‖eisEmbedding z‖ ^ 2 / K)) := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  have h := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
    (Ideal.Quotient.mk (Ideal.span {a * b})) (pairResidue a b ha hb)
  simpa only [pairResidue_mk, scaledRadialTest_apply] using h


-- @@ L45-59 verbatim
theorem row_pair_poisson (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O,
      (idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b}))) *
        W (‖eisEmbedding z‖ ^ 2 / K)) =
    ((K / ‖eisEmbedding (a * b)‖ ^ 2 : ℝ) : ℂ) *
      ∑' h : O, pairFourier a b ha hb h *
        paperRadialFourier W (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (a * b)‖ ^ 2) := by
  let := finite_quotient_span (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  have h := actual_radial_paper_poisson_trace W K hK (a * b)
    (mul_ne_zero (supported_element_ne_zero a ha) (supported_element_ne_zero b hb))
    (pairResidue a b ha hb)
  simpa only [pairResidue_mk, pairFourier, quotientTrace, tsum_fintype, Complex.real_smul] using h


-- @@ L61-62 verbatim
def rowPolynomial {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ) (z : O) : ℂ :=
  ∑ i ∈ S, c i * idealRowHom z (Ideal.span {a i})


-- @@ L64-67 verbatim
def rowEnergy {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) : ℂ :=
  ∑' z : O, ((‖rowPolynomial S a c z‖ ^ 2 : ℝ) : ℂ) *
    W (‖eisEmbedding z‖ ^ 2 / K)


-- @@ L69-82 verbatim
theorem rowPolynomial_norm_sq {α : Type*} (S : Finset α) (a : α → O)
    (c : α → ℂ) (z : O) :
    ((‖rowPolynomial S a c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (idealRowHom z (Ideal.span {a i}) * star (idealRowHom z (Ideal.span {a j}))) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [rowPolynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring


-- @@ L84-99 verbatim
theorem rowEnergy_expand {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    rowEnergy S a c W K =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        ∑' z : O, (idealRowHom z (Ideal.span {a i}) *
          star (idealRowHom z (Ideal.span {a j}))) * W (‖eisEmbedding z‖ ^ 2 / K) := by
  have hs (i j : α) := (row_pair_summable (a i) (a j) (ha i) (ha j) W K hK).mul_left
    (c i * star (c j))
  simp only [mul_assoc] at hs
  simp only [rowEnergy, rowPolynomial_norm_sq, Finset.sum_mul, mul_assoc]
  rw [Summable.tsum_finsetSum (fun i _ => (hasSum_sum (fun j _ => (hs i j).hasSum)).summable)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Summable.tsum_finsetSum (fun j _ => hs i j)]
  simp only [tsum_mul_left]


-- @@ L101-115 verbatim
theorem rowEnergy_poisson {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    rowEnergy S a c W K =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (((K / ‖eisEmbedding (a i * a j)‖ ^ 2 : ℝ) : ℂ) *
          ∑' h : O, pairFourier (a i) (a j) (ha i) (ha j) h *
            paperRadialFourier W
              (K * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding (a i * a j)‖ ^ 2)) := by
  rw [rowEnergy_expand S a c ha W K hK]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [row_pair_poisson (a i) (a j) (ha i) (ha j) W K hK]


-- @@ L117-117 verbatim
end SevenEighths.CenteredMomentRowNorm


-- @@ L119-119 verbatim
end


-- @@ L121-121 verbatim
end OAI
