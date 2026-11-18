import OAI.NumberTheory.DirichletL.Detector.TupleRows


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical

-- @@ L7-7 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L8-8 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L9-9 verbatim
local notation "Id" => Ideal O


-- @@ L11-14 verbatim
def tuplePhysicalScalar {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (J : Finset (Fin K)) : ℂ :=
  (-1:ℂ)^J.card*((elementNorm (∏i∈J,p i)^(-(3/2:ℝ)):ℝ):ℂ)*
    star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))


-- @@ L16-31 verbatim
lemma tuple_scaled_coefficient {K : ℕ} (η : HeckeFamily.Character) (p : Fin K→O)
    (hp : ∀i,p i≠0) (J : Finset (Fin K)) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (x w z : ℂ) :
    tuplePhysicalScalar η p J*
      sourceMellinWeight W0 W1 (X/elementNorm (∏i∈J,p i)) (Y/elementNorm (∏i∈J,p i))
        (Z*elementNorm (∏i∈Finset.univ\J,p i)) x w z=
    sourceMellinWeight W0 W1 X Y Z x w z*(∏i,(elementNorm (p i):ℂ)^(z-1))*
      tupleIndexedCoefficient η p J x w := by
  have ha := sourceMellinWeight_subset W0 W1 X Y Z (elementNorm (∏i∈J,p i))
    (elementNorm (∏i∈Finset.univ\J,p i)) hX hY hZ (tuple_norm_pos p hp J)
    (tuple_norm_pos p hp (Finset.univ\J))
    (star (HeckeFamily.elementCoeff η (∏i∈Finset.univ\J,p i))) x w z
  have hb := tuple_source_scalar η p hp J x w z
  unfold tuplePhysicalScalar tupleIndexedCoefficient
  linear_combination (-1:ℂ)^J.card*ha +
    (-1:ℂ)^J.card*sourceMellinWeight W0 W1 X Y Z x w z*hb


-- @@ L33-47 verbatim
lemma compensatedRow_kernel_subsets {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (p : Fin K→O) (hp : ∀i,p i≠0) (u : O) (a : ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (x w z : ℂ) :
    sourceMellinWeight W0 W1 X Y Z x w z*(∏i,(elementNorm (p i):ℂ)^(z-1))*
      (a*indexedCompensatedHigh η S p u x w z)=
    ∑J∈(Finset.univ:Finset (Fin K)).powerset,tuplePhysicalScalar η p J*
      ((a*markedIdealHighSeries S (Ideal.span {∏i∈Finset.univ\J,p i}) η u x w z)*
        sourceMellinWeight W0 W1 (X/elementNorm (∏i∈J,p i)) (Y/elementNorm (∏i∈J,p i))
          (Z*elementNorm (∏i∈Finset.univ\J,p i)) x w z) := by
  unfold indexedCompensatedHigh
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  have he := tuple_scaled_coefficient η p hp J W0 W1 X Y Z hX hY hZ x w z
  linear_combination -a*markedIdealHighSeries S (Ideal.span {∏i∈Finset.univ\J,p i}) η u x w z*he


-- @@ L49-49 verbatim
end SevenEighths.ProbePhysical

-- @@ L50-50 verbatim
end


-- @@ L52-52 verbatim
end OAI
