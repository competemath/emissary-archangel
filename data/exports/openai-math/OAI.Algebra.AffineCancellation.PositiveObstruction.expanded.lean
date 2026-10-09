import OAI.Algebra.AffineCancellation.Bundle
import OAI.Algebra.AffineCancellation.HomogeneousExtraction


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
namespace ComplexCancellation.Determinant

-- @@ L9-12 verbatim
lemma Euler_v : Euler v=2*v := by
  simp only [v,map_sub,Derivation.leibniz,Derivation.leibniz_pow,
    Euler_a,Euler_b,Euler_d,Euler_u,smul_eq_mul]
  ring

-- @@ L13-13 verbatim
end ComplexCancellation.Determinant

-- @@ L14-14 verbatim
namespace ComplexCancellation.Bundle

-- @@ L15-15 verbatim
open Determinant

-- @@ L16-17 verbatim
abbrev valuationPieces (e : ℤ) : Submodule ℂ B :=
  (AffineModification.pieces T v e).restrictScalars ℂ

-- @@ L18-19 verbatim
instance valuationGrading : GradedAlgebra valuationPieces :=
  { (AffineModification.grading T v) with }

-- @@ L20-20 verbatim
def fiberEuler : Derivation ℂ B B := AffineModification.euler v Euler Euler_v

-- @@ L21-35 verbatim
/-- The positive-invariant obstruction on the pullback ring. -/
theorem no_positive_invariant
    (D : Derivation ℂ B B) (hD : LND.LocallyNilpotent D) (hDn : D ≠ 0)
    (j : ℤ) (hshift : ∀ e r, r ∈ valuationPieces e → D r ∈ valuationPieces (e+j))
    (hcomm : ∀ z, fiberEuler (D z)=D (fiberEuler z))
    (w : B) (hw : w ≠ 0) (e : ℤ) (he : 0 < e)
    (hwg : w ∈ valuationPieces e) (hDw : D w=0) : False := by
  have hV := AffineModification.fixed_V_of_positive_invariant v v_ne_zero D hD w hw e he hwg hDw
  obtain ⟨E,n,hEn,hEl,hshiftE,hEv⟩ :=
    AffineModification.extract v v_ne_zero Euler Euler_v D hD hDn j hshift hcomm hV
  apply hEn
  apply rigidity E hEl (-(n : ℤ)) (by omega) _ hEv
  intro r
  rw [hshiftE]
  simp only [Int.cast_neg,Int.cast_natCast,neg_smul,Nat.cast_smul_eq_nsmul]

-- @@ L36-36 verbatim
end ComplexCancellation.Bundle


-- @@ L38-38 verbatim
end


-- @@ L40-40 verbatim
end OAI
