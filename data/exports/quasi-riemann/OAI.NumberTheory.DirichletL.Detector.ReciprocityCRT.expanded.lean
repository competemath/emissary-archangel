import OAI.NumberTheory.DirichletL.Detector.PhysicalCRT
import OAI.NumberTheory.DirichletL.Detector.PhasePowers


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L8-8 verbatim
open ActualEisensteinCubic CanonicalRowCompletion CanonicalQuadraticSieve

-- @@ L9-9 verbatim
open ConcretePrimeRowBridge CubicEisenstein ProbePhase

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L12-13 verbatim
def reciprocityCoefficient (A s : O) (hA : A≠0) (H : O) : ℂ :=
  reciprocitySign A s * bareCongruenceCoefficient A s hA H


-- @@ L15-59 verbatim
theorem reciprocityCoefficient_product (A B s r : O)
    (hA : Supported (Ideal.span {A})) (hB : Supported (Ideal.span {B}))
    (hs : Supported (Ideal.span {s})) (hr : Supported (Ideal.span {r}))
    (hpA : goodLambda^2∣A-1) (hpB : goodLambda^2∣B-1)
    (hps : goodLambda^2∣s-1) (hpr : goodLambda^2∣r-1)
    (hcop : IsCoprime (A*s) (B*r)) (H : O) :
    reciprocityCoefficient (A*B) (s*r)
      (mul_ne_zero (supportedElement_ne_zero A hA) (supportedElement_ne_zero B hB)) H =
      (idealRowHom B (Ideal.span {A}) * idealRowHom A (Ideal.span {B})) *
        reciprocityCoefficient A s (supportedElement_ne_zero A hA) H *
        reciprocityCoefficient B r (supportedElement_ne_zero B hB) H := by
  have hsB := idealRowHom_ne_zero_of_coprime s B hs hcop.of_mul_left_right.of_mul_right_left
  have hrA := idealRowHom_ne_zero_of_coprime r A hr hcop.of_mul_left_left.of_mul_right_right.symm
  have hAr : idealRowHom r (Ideal.span {A}) = reciprocitySign A r * idealRowHom A (Ideal.span {r}) :=
    idealRowHom_primary_reciprocity A r hpA hpr hA hr
  have hBs : idealRowHom s (Ideal.span {B}) = reciprocitySign B s * idealRowHom B (Ideal.span {s}) :=
    idealRowHom_primary_reciprocity B s hpB hps hB hs
  have hratio :
      (idealRowHom B (Ideal.span {A}) * idealRowHom r (Ideal.span {A}) *
       idealRowHom A (Ideal.span {B}) * idealRowHom s (Ideal.span {B})) /
      (idealRowHom B (Ideal.span {s}) * idealRowHom A (Ideal.span {r})) =
      (idealRowHom B (Ideal.span {A}) * idealRowHom A (Ideal.span {B})) *
        reciprocitySign A r * reciprocitySign B s := by
    rw [hAr, hBs]
    field_simp
  have hsign : reciprocitySign (A*B) (s*r) * reciprocitySign A r * reciprocitySign B s =
      reciprocitySign A s * reciprocitySign B r := by
    calc
      _ = reciprocitySign A s * reciprocitySign B r *
          reciprocitySign A r ^ 2 * reciprocitySign B s ^ 2 := by
        simp only [reciprocitySign_mul_left, reciprocitySign_mul_right]
        ring
      _ = _ := by
        rw [reciprocitySign_sq A r (supported_residue_odd A hA) (supported_residue_odd r hr),
          reciprocitySign_sq B s (supported_residue_odd B hB) (supported_residue_odd s hs),
          mul_one, mul_one]
  unfold reciprocityCoefficient
  rw [bareCongruenceCoefficient_product_reduced A B s r (supportedElement_ne_zero A hA)
    (supportedElement_ne_zero B hB) hs hr hcop H, hratio]
  calc
    _ = (reciprocitySign (A*B) (s*r) * reciprocitySign A r * reciprocitySign B s) *
        (idealRowHom B (Ideal.span {A}) * idealRowHom A (Ideal.span {B})) *
        bareCongruenceCoefficient A s (supportedElement_ne_zero A hA) H *
        bareCongruenceCoefficient B r (supportedElement_ne_zero B hB) H := by ring
    _ = _ := by rw [hsign]; ring


-- @@ L61-61 verbatim
end SevenEighths.ProbePhysical

-- @@ L62-62 verbatim
end


-- @@ L64-64 verbatim
end OAI
