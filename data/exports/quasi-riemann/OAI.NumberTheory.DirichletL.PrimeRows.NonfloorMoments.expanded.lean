import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDictionary
import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorSourceCount


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
namespace SevenEighths.ProbeHighRowFamily

-- @@ L9-9 verbatim
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch HeckeDetectorRawFiber

-- @@ L10-10 verbatim
local notation "O" => HeckeFamily.O

-- @@ L11-11 verbatim
variable (M : Ideal O) [NeZero M]

-- @@ L12-12 verbatim
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L13-13 verbatim
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)


-- @@ L15-27 verbatim
def SourceMomentsAt {N : ℕ} (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (rows : Finset FreeRow) (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d a ε τ dmax b slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ)
    (Δ c κ C height εm : ℝ) : Prop :=
  ∀q : ℝ,∀B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
      (Z^d) a ε (HeckeDetectorAdaptiveCutoff.cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
    B.rows⊆rows → B.data=sourceMomentData M H hH S hS η →
    B.reverse=sourceMomentReverse M H → B.slots=Finset.univ →
    B.widths=(fun j=>ell j/d) → B.profile=W → B.upper=(fun _=>b) → B.external=(fun _=>z) →
    B.mesh=slotMesh → B.binWidth=binWidth →
    (∀u∈B.rows,∀j,B.family u j=sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j) →
    ∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
      Moments (B.fiber bin j J K hne) Δ c κ C height εm


-- @@ L29-29 verbatim
end SevenEighths.ProbeHighRowFamily


-- @@ L31-31 verbatim
end


-- @@ L33-33 verbatim
end OAI
