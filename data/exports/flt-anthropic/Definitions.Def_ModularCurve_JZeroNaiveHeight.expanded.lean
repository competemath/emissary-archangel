import Definitions.Def_ModularCurve_AtkinLehner
import Mathlib.Algebra.Ring.Action.Submonoid
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.NumberTheory.Height.NumberField
import Definitions.Def_Compat_Mathlib430


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
open AlgebraicCurve Polynomial


-- @@ L11-11 verbatim
namespace ModularCurve


-- @@ L13-13 verbatim
variable (N : ℕ) [NeZero N]


-- @@ L15-19 verbatim
def jCoord (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : AlgebraicClosure ℚ :=
  Classical.epsilon fun c : AlgebraicClosure ℚ =>
    0 < v.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) c)


-- @@ L21-25 verbatim
def jFactor (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Polynomial (AlgebraicClosure ℚ) :=
  if 0 ≤ v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N)
  then X - C (jCoord N v) else 1


-- @@ L27-29 verbatim
def symPoly (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Polynomial (AlgebraicClosure ℚ) :=
  D.prod fun v n => jFactor N v ^ n.toNat


-- @@ L31-33 verbatim
def symVec (g' : ℕ) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    Fin (g' + 1) → AlgebraicClosure ℚ :=
  fun k => (symPoly N D).coeff (g' - k)


-- @@ L35-37 verbatim
instance numberField_of_finiteDimensional (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] : NumberField K :=
  NumberField.mk


-- @@ L39-39 verbatim
variable (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]


-- @@ L41-44 verbatim
open scoped Classical in

def divNaiveHeight (g' : ℕ) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : ℝ :=
  if h : ∀ k, symVec N g' D k ∈ K then Height.logHeight fun k => (⟨symVec N g' D k, h k⟩ : K) else 0


-- @@ L46-55 expanded
def JZero.repHeights (g' : ℕ) (c : ↥(FixedPoints.addSubgroup (↥K.fixingSubgroup) (JZero N))) :
    Set ℝ :=
  {r |
    ∃ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (E :
      Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))),
      (∀ v, 0 ≤ D v) ∧
        (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) +
              (g' : ℤ) • Finsupp.single (cuspInftyBar N) 1 =
            D ∧
          (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
              σ ∈ K.fixingSubgroup → arithmeticGalois (modularFunctionFieldFull N) σ • D = D) ∧
            Pic0.mk E = (c : JZero N) ∧ r = divNaiveHeight N K g' D}


-- @@ L57-58 expanded
def JZero.naiveHeight (g' : ℕ) (c : ↥(FixedPoints.addSubgroup (↥K.fixingSubgroup) (JZero N))) : ℝ :=
  sInf (JZero.repHeights N K g' c)


-- @@ L60-60 verbatim
variable {N K}


-- @@ L62-66 verbatim
theorem jFactor_of_nonneg {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hv : 0 ≤ v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N)) :
    jFactor N v = X - C (jCoord N v) :=
  if_pos hv


-- @@ L68-72 verbatim
theorem jFactor_of_neg {v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (hv : v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ : modularFunctionFieldBar N) < 0) :
    jFactor N v = 1 :=
  if_neg (not_le.mpr hv)


-- @@ L74-76 verbatim
@[simp]
theorem symPoly_zero : symPoly N 0 = 1 :=
  Finsupp.prod_zero_index


-- @@ L78-80 verbatim
theorem symPoly_single (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (n : ℤ) :
    symPoly N (Finsupp.single v n) = jFactor N v ^ n.toNat :=
  Finsupp.prod_single_index (by simp)


-- @@ L82-87 verbatim
theorem divNaiveHeight_nonneg (g' : ℕ) (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    0 ≤ divNaiveHeight N K g' D := by
  unfold divNaiveHeight
  split_ifs with h
  · exact Height.logHeight_nonneg _
  · exact le_rfl


-- @@ L89-92 expanded
theorem JZero.repHeights_nonneg {g' : ℕ}
    {c : ↥(FixedPoints.addSubgroup (↥K.fixingSubgroup) (JZero N))} {r : ℝ}
    (hr : r ∈ JZero.repHeights N K g' c) : 0 ≤ r :=
  by
  obtain ⟨D, E, -, -, -, -, rfl⟩ := hr
  exact divNaiveHeight_nonneg g' D


-- @@ L94-96 expanded
theorem JZero.naiveHeight_nonneg (g' : ℕ)
    (c : ↥(FixedPoints.addSubgroup (↥K.fixingSubgroup) (JZero N))) :
    0 ≤ JZero.naiveHeight N K g' c :=
  Real.sInf_nonneg fun _ hr => JZero.repHeights_nonneg hr


-- @@ L98-108 expanded
theorem JZero.naiveHeight_le (g' : ℕ) (c : ↥(FixedPoints.addSubgroup (↥K.fixingSubgroup) (JZero N)))
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (E : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N)))
    (hD : ∀ v, 0 ≤ D v)
    (hE :
      (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) +
          (g' : ℤ) • Finsupp.single (cuspInftyBar N) 1 =
        D)
    (hK :
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        σ ∈ K.fixingSubgroup → arithmeticGalois (modularFunctionFieldFull N) σ • D = D)
    (hc : Pic0.mk E = (c : JZero N)) : JZero.naiveHeight N K g' c ≤ divNaiveHeight N K g' D :=
  csInf_le ⟨0, fun _ hr => JZero.repHeights_nonneg hr⟩ ⟨D, E, hD, hE, hK, hc, rfl⟩


-- @@ L110-112 expanded
theorem JZero.naiveHeight_eq_zero (g' : ℕ)
    (c : ↥(FixedPoints.addSubgroup (↥K.fixingSubgroup) (JZero N)))
    (h : JZero.repHeights N K g' c = ∅) : JZero.naiveHeight N K g' c = 0 := by
  rw [JZero.naiveHeight, h, Real.sInf_empty]


-- @@ L114-114 verbatim
end ModularCurve


-- @@ L116-116 verbatim
end
