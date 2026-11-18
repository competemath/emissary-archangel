import OAI.NumberTheory.DirichletL.Reflection.Shape
import OAI.NumberTheory.DirichletL.CubicSieve.Ideal


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L12-13 verbatim
@[simp] lemma shapeArgument_one : shapeArgument (1:Eis)=1 := by
  simp [shapeArgument,Ideal.span_singleton_one]


-- @@ L15-18 verbatim
lemma stratumShapeFactor_mul_one {H : Matrix.SpecialLinearGroup (Fin 2) Eis}
    (s : FixedCuspShape H) (c r : Eis) :
    s.stratumShapeFactor (c*r)=s.stratumShapeFactor c*shapeArgument r := by
  simpa only [mul_one,shapeArgument_one] using stratumShapeFactor_mul s c r 1


-- @@ L20-23 verbatim
lemma primeFamily_primary_product_ne_zero {φ : Type*} [Fintype φ] (F : PrimeFamily φ) :
    primaryGenerator (∏ i,F.ideal i)≠0 := by
  rw [←F.generator_product]
  exact Finset.prod_ne_zero_iff.mpr (fun i _ => F.generator_ne_zero i)


-- @@ L25-28 verbatim
lemma stratumShapeFactor_frozen_norm {φ : Type*} [Fintype φ]
    {H : Matrix.SpecialLinearGroup (Fin 2) Eis} (s : FixedCuspShape H) (c : Eis) (F : PrimeFamily φ) :
    ‖s.stratumShapeFactor (c*primaryGenerator (∏ i,F.ideal i))‖=‖s.stratumShapeFactor c‖ := by
  rw [stratumShapeFactor_mul_one,norm_mul,shapeArgument_norm _ (primeFamily_primary_product_ne_zero F),mul_one]


-- @@ L30-33 verbatim
lemma row_shape_weight_norm (r : Ideal Eis→ℂ) (K : Ideal Eis) (hK : Admissible K) :
    ‖r K*shapeArgument (primaryGenerator K)‖=‖r K‖ := by
  have hk := PrimaryIdealUnitReindex.primaryGenerator_ne_zero_of_good_factors K hK.1 (fun P hP => (hK.2.2 P hP).1)
  rw [norm_mul,shapeArgument_norm _ hk,mul_one]


-- @@ L35-37 verbatim
lemma slot_shape_weight_norm (aw : Ideal Eis→ℂ) (P : Ideal Eis) (hP : CubicSieve.Admissible P) :
    ‖aw P*shapeArgument (primaryGenerator P)‖=‖aw P‖ := by
  rw [norm_mul,shapeArgument_norm _ hP.2,mul_one]

-- @@ L38-38 verbatim
end

-- @@ L39-39 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L41-41 verbatim
end OAI
