import OAI.NumberTheory.DirichletL.Detector.GaussianPhysicalTuple
import OAI.NumberTheory.DirichletL.Detector.PhysicalNorms


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical SchwartzMap

-- @@ L8-8 verbatim
open MeasureTheory FourierBridge CompletedGauss

-- @@ L9-9 verbatim
namespace SevenEighths.ProbePhysical

-- @@ L10-10 verbatim
open ProbeCompleted ProbeRow

-- @@ L11-11 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L12-12 verbatim
local notation "Id" => Ideal O


-- @@ L14-17 verbatim
lemma physicalElementNorm_pos (a : O) (ha : a≠0) : 0<elementNorm a := by
  unfold elementNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr ha))


-- @@ L19-23 verbatim
lemma elementNorm_slotProduct {K : ℕ} (p : Fin K→O) (J : Finset (Fin K)) :
    elementNorm (slotProduct p J)=∏i∈J,elementNorm (p i) := by
  induction J using Finset.induction_on with
  | empty => simp [slotProduct,elementNorm_one]
  | @insert i J hi ih => simpa only [slotProduct,Finset.prod_insert hi,elementNorm_mul] using congrArg (fun x=>elementNorm (p i)*x) ih


-- @@ L25-26 verbatim
lemma slotProduct_nonzero {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    slotProduct p J≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)


-- @@ L28-29 verbatim
lemma slotProduct_norm_pos {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    0<elementNorm (slotProduct p J) := physicalElementNorm_pos _ (slotProduct_nonzero p hp J)


-- @@ L31-34 verbatim
def compensationSubsetCoefficient {K : ℕ} (η : HeckeFamily.Character)
    (p : Fin K→O) (J : Finset (Fin K)) : ℂ :=
  (-1:ℂ)^J.card*((elementNorm (slotProduct p J)^(-(3/2:ℝ)):ℝ):ℂ)*
    star (HeckeFamily.elementCoeff η (slotProduct p (Finset.univ\J)))


-- @@ L36-41 verbatim
def compensationSubsetProbe {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (p : Fin K→O) (J : Finset (Fin K)) (X Y Z : ℝ) : ℂ :=
  compensationSubsetCoefficient η p J*
    markedPhysicalProbe η C (Ideal.span {slotProduct p (Finset.univ\J)}) W0 W1
      (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))
      (Z*elementNorm (slotProduct p (Finset.univ\J)))


-- @@ L43-46 verbatim
lemma compensatedTuple_eq_subsets {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (p : Fin K→O) (X Y Z : ℝ) :
    compensatedTuple η C W0 W1 p X Y Z=
      ∑J∈(Finset.univ : Finset (Fin K)).powerset,compensationSubsetProbe η C W0 W1 p J X Y Z := rfl


-- @@ L48-58 verbatim
lemma compensatedPhysicalProbe_eq_subsets {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slotPrimes : Fin K→Finset O)
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (X Y Z : ℝ) :
    compensatedPhysicalProbe η C W0 W1 slotPrimes W P X Y Z=
      ∑J∈(Finset.univ : Finset (Fin K)).powerset,
        ∑p : ((i : Fin K)→{a : O // a∈slotPrimes i}),
          (∏i,W i (elementNorm (p i).val/P i))*
            compensationSubsetProbe η C W0 W1 (fun i=>(p i).val) J X Y Z := by
  unfold compensatedPhysicalProbe
  simp_rw [compensatedTuple_eq_subsets,Finset.mul_sum]
  exact Finset.sum_comm


-- @@ L60-74 verbatim
theorem compensationSubsetProbe_eq_gaussian_rows {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K))
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensationSubsetProbe η C W0 W1 p J X Y Z=
      compensationSubsetCoefficient η p J*
        ∑'r : PhysicalRowIndex,
          physicalRowWeight C W0 W1 (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J)) r*
            correctedCompletedT C.excluded (Ideal.span {slotProduct p (Finset.univ\J)})
              (physicalRowMonoid η C r) gaussianCompletedProfile
                (Z*elementNorm (slotProduct p (Finset.univ\J))) := by
  unfold compensationSubsetProbe
  rw [markedPhysicalProbe_eq_gaussian_rows η C _ W0 W1 hW0 hW1 _ _ _
    (div_pos hX (slotProduct_norm_pos p hp J)) (div_pos hY (slotProduct_norm_pos p hp J))
    (mul_pos hZ (slotProduct_norm_pos p hp _))]


-- @@ L76-76 verbatim
end SevenEighths.ProbePhysical

-- @@ L77-77 verbatim
end


-- @@ L79-79 verbatim
end OAI
