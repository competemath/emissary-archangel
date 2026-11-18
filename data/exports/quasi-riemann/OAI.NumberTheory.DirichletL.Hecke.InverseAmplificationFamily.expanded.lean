import OAI.NumberTheory.DirichletL.Hecke.InverseAmplificationEnergy


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical ContDiff

-- @@ L7-7 verbatim
namespace SevenEighths.HeckeInverseAmplification

-- @@ L8-8 verbatim
open HeckeFamily HeckeDyadic HeckeRowClosure

-- @@ L9-9 verbatim
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

-- @@ L10-10 verbatim
abbrev NonzeroElement := UnrestrictedIdealReindex.NonzeroElement


-- @@ L12-19 verbatim
structure RowData where
  η : Character
  m : O
  f : O
  m_ne_zero : m≠0
  f_ne_zero : f≠0
  lambda_dvd : λ₀∣m
  two_dvd : (2 : O)∣m


-- @@ L21-23 verbatim
def RowData.character (data : RowData) (u : NonzeroElement) : Character :=
  Classical.choose (exists_row_character data.η data.m data.f u.val
    data.m_ne_zero data.f_ne_zero u.property data.lambda_dvd data.two_dvd)


-- @@ L25-29 verbatim
theorem RowData.character_spec (data : RowData) (u : NonzeroElement) (n : O) :
    elementCoeff (data.character u) n=
      CanonicalRowCompletion.rowTwist (elementHom data.η) data.m data.f u.val n :=
  Classical.choose_spec (exists_row_character data.η data.m data.f u.val
    data.m_ne_zero data.f_ne_zero u.property data.lambda_dvd data.two_dvd) n


-- @@ L31-33 verbatim
def amplifiedElement (u : NonzeroElement) (A : NonzeroIdeal) : NonzeroElement :=
  ⟨u.val*(ConcretePrimeRowBridge.idealGenerator A.val)^6,
    mul_ne_zero u.property (pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero A.val A.property))⟩


-- @@ L35-44 verbatim
theorem RowData.amplified_prime_mask (data : RowData) (u : NonzeroElement)
    (P : SmoothMobiusCorrection.PrimeIdeal) :
    idealCoeff (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩))=
      IdealEuler.deletePrimes {P} (idealCoeff (data.character u)) := by
  exact amplified_row_prime_mask data.η (data.character u)
    (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) data.m data.f u.val
    (ConcretePrimeRowBridge.idealGenerator P.val) P
    (ConcretePrimeRowBridge.span_idealGenerator P.val)
    (data.character_spec u) (data.character_spec (amplifiedElement u ⟨P.val,P.property.ne_zero⟩))
    data.lambda_dvd data.two_dvd


-- @@ L46-55 verbatim
theorem RowData.prime_column (data : RowData) (u : NonzeroElement)
    (P : SmoothMobiusCorrection.PrimeIdeal) (W : ℝ→ℂ) (a b : ℝ)
    (ha : 0<a) (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0<D) :
    polynomial (data.character u) true W D σ freq=
      polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W D σ freq-
      idealCoeff (data.character u) P.val*(P.val.absNorm : ℂ)^(-(1/2 : ℂ))*
        polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W
          (D/(P.val.absNorm : ℝ)) σ freq :=
  prime_column_identity _ _ P (data.amplified_prime_mask u P) W a b ha hWs hW D σ freq hD


-- @@ L57-65 verbatim
theorem RowData.prime_energy (data : RowData) (u : NonzeroElement)
    (P : SmoothMobiusCorrection.PrimeIdeal) (W : ℝ→ℂ) (a b : ℝ)
    (ha : 0<a) (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (D σ freq : ℝ) (hD : 0<D) :
    ‖polynomial (data.character u) true W D σ freq‖^2≤
      2*(‖polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W D σ freq‖^2+
        ‖polynomial (data.character (amplifiedElement u ⟨P.val,P.property.ne_zero⟩)) true W
          (D/(P.val.absNorm : ℝ)) σ freq‖^2) :=
  prime_column_energy _ _ P (data.amplified_prime_mask u P) W a b ha hWs hW D σ freq hD


-- @@ L67-67 verbatim
end SevenEighths.HeckeInverseAmplification


-- @@ L69-69 verbatim
end


-- @@ L71-71 verbatim
end OAI
