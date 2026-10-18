import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.RingTheory.Localization.FractionRing


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-15 verbatim
/-!
# Constants in polynomial charts

Section 5 identifies two localizations of the determinant ring with polynomial
rings over principal localizations of `k[a,d,u]`.  The needed intersection with
`k(a,d,u)` is not a set-theoretic assertion: a polynomial over the chart's
coefficient ring which becomes constant over the fraction field has that
constant in its coefficient ring.  The lemmas here prove that exact algebraic
interface without assuming the manuscript's chart identifications.
-/


-- @@ L17-17 verbatim
namespace StableCoordinate.PolynomialChartIntersection


-- @@ L19-19 verbatim
open Polynomial


-- @@ L21-21 verbatim
section RingHom


-- @@ L23-23 verbatim
variable {R S : Type*} [Semiring R] [Semiring S]


-- @@ L25-34 verbatim
/-- Taking the constant coefficient recovers a constant in the range of an
actual polynomial coefficient map.  No injectivity assumption is needed. -/
theorem constant_mem_range_map_iff (f : R →+* S) (s : S) :
    C s ∈ Set.range (Polynomial.map f) ↔ s ∈ Set.range f := by
  constructor
  · rintro ⟨p, hp⟩
    refine ⟨p.coeff 0, ?_⟩
    simpa only [coeff_map, coeff_C_zero] using congrArg (fun q : S[X] ↦ q.coeff 0) hp
  · rintro ⟨r, rfl⟩
    exact ⟨C r, map_C f⟩


-- @@ L36-50 verbatim
/-- A mapped polynomial that becomes constant was itself constant when the
coefficient map is injective. -/
theorem map_eq_C_iff (f : R →+* S) (hf : Function.Injective f)
    (p : R[X]) (s : S) :
    Polynomial.map f p = C s ↔ ∃ r : R, p = C r ∧ f r = s := by
  constructor
  · intro h
    have hr : f (p.coeff 0) = s := by
      simpa only [coeff_map, coeff_C_zero] using congrArg (fun q : S[X] ↦ q.coeff 0) h
    use p.coeff 0
    refine ⟨?_, hr⟩
    apply Polynomial.map_injective f hf
    rw [h, map_C, hr]
  · rintro ⟨r, rfl, rfl⟩
    exact map_C f


-- @@ L52-63 verbatim
/-- The intersection of coefficientwise images with the constant polynomials
is exactly the image of the original coefficient ring. -/
theorem polynomial_range_inf_constants (f : R →+* S) :
    (Polynomial.mapRingHom f).rangeS ⊓ (C : S →+* S[X]).rangeS =
      ((C : S →+* S[X]).comp f).rangeS := by
  ext p
  constructor
  · rintro ⟨⟨r, hr⟩, ⟨s, rfl⟩⟩
    obtain ⟨a, ha⟩ := (constant_mem_range_map_iff f s).mp ⟨r, hr⟩
    exact ⟨a, by simp only [RingHom.comp_apply, ha]⟩
  · rintro ⟨r, rfl⟩
    exact ⟨⟨C r, map_C f⟩, ⟨f r, rfl⟩⟩


-- @@ L65-65 verbatim
end RingHom


-- @@ L67-67 verbatim
end StableCoordinate.PolynomialChartIntersection


-- @@ L69-69 verbatim
namespace StableCoordinate.PolynomialChartIntersection


-- @@ L71-71 verbatim
open Polynomial


-- @@ L73-73 verbatim
section CompatibleCharts


-- @@ L75-75 verbatim
variable {A C K Ω : Type*} [Semiring A] [Semiring C] [Semiring K] [Semiring Ω]


-- @@ L77-97 verbatim
/-- If a polynomial chart and a coefficient-field embedding agree in a common
ambient ring, injectivity of the polynomial chart forces the putative constant
to belong to the chart coefficient ring.  All maps and commuting-square
conditions are explicit; no identification of abstractly isomorphic rings is
silently used. -/
theorem mem_coefficient_range_of_compatible_chart
    (f : A →+* K) (chart : C →+* A[X])
    (inclusion : C →+* Ω) (coefficients : K →+* Ω)
    (polynomialEmbedding : K[X] →+* Ω)
    (hinj : Function.Injective polynomialEmbedding)
    (hchart : (polynomialEmbedding.comp (Polynomial.mapRingHom f)).comp chart = inclusion)
    (hcoeff : polynomialEmbedding.comp (Polynomial.C : K →+* K[X]) = coefficients)
    {c : C} {q : K} (h : inclusion c = coefficients q) :
    q ∈ Set.range f := by
  apply (constant_mem_range_map_iff f q).mp
  refine ⟨chart c, hinj ?_⟩
  calc
    polynomialEmbedding (Polynomial.map f (chart c)) = inclusion c :=
      RingHom.congr_fun hchart c
    _ = coefficients q := h
    _ = polynomialEmbedding (Polynomial.C q) := (RingHom.congr_fun hcoeff q).symm


-- @@ L99-116 verbatim
/-- The previous lemma also records the stronger conclusion that the chart
polynomial itself is constant whenever its coefficient map is injective. -/
theorem chart_eq_constant_of_compatible_chart
    (f : A →+* K) (hf : Function.Injective f) (chart : C →+* A[X])
    (inclusion : C →+* Ω) (coefficients : K →+* Ω)
    (polynomialEmbedding : K[X] →+* Ω)
    (hinj : Function.Injective polynomialEmbedding)
    (hchart : (polynomialEmbedding.comp (Polynomial.mapRingHom f)).comp chart = inclusion)
    (hcoeff : polynomialEmbedding.comp (Polynomial.C : K →+* K[X]) = coefficients)
    {c : C} {q : K} (h : inclusion c = coefficients q) :
    ∃ a : A, chart c = Polynomial.C a ∧ f a = q := by
  apply (map_eq_C_iff f hf _ _).mp
  apply hinj
  calc
    polynomialEmbedding (Polynomial.map f (chart c)) = inclusion c :=
      RingHom.congr_fun hchart c
    _ = coefficients q := h
    _ = polynomialEmbedding (Polynomial.C q) := (RingHom.congr_fun hcoeff q).symm


-- @@ L118-118 verbatim
end CompatibleCharts


-- @@ L120-120 verbatim
section AlgebraHom


-- @@ L122-123 verbatim
variable {k R S : Type*} [CommSemiring k] [Semiring R] [Semiring S]
  [Algebra k R] [Algebra k S]


-- @@ L125-136 verbatim
/-- The constants-in-chart statement in the form of an equality of
`k`-subalgebras, for direct use with affine coordinate rings. -/
theorem polynomial_algRange_inf_constants (f : R →ₐ[k] S) :
    (Polynomial.mapAlgHom f).range ⊓ (Polynomial.CAlgHom : S →ₐ[k] S[X]).range =
      ((Polynomial.CAlgHom : S →ₐ[k] S[X]).comp f).range := by
  ext p
  constructor
  · rintro ⟨⟨r, hr⟩, ⟨s, rfl⟩⟩
    obtain ⟨a, ha⟩ := (constant_mem_range_map_iff f.toRingHom s).mp ⟨r, hr⟩
    exact ⟨a, congrArg (Polynomial.C : S → S[X]) ha⟩
  · rintro ⟨r, rfl⟩
    exact ⟨⟨C r, map_C f.toRingHom⟩, ⟨f r, rfl⟩⟩


-- @@ L138-138 verbatim
end AlgebraHom


-- @@ L140-140 verbatim
end StableCoordinate.PolynomialChartIntersection


-- @@ L142-142 verbatim
end OAI
