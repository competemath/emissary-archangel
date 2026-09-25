module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechMembershipDefs
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechConstructionA
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.Shell4.LeechConstructionAMain



-- @@ L7-12 verbatim
/-!
# Shell4 Isometry Leech Membership Type II

Leech lattice membership (BS81 Lemma 21), Pattern II: `((±2)^8, 0^16)`.

-/


-- @@ L14-14 verbatim
namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
open scoped RealInnerProductSpace BigOperators


-- @@ L20-20 verbatim
open Uniqueness.BS81

-- @@ L21-21 verbatim
open Uniqueness.BS81.CodingTheory

-- @@ L22-22 verbatim
open Uniqueness.BS81.Thm15.Lemma21


-- @@ L24-24 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L26-26 verbatim
namespace Shell4IsometryLeechMembership


-- @@ L28-28 verbatim
open Set


-- @@ L30-31 verbatim
lemma pattern1_even (z : Fin 24 → ℤ) (hz : isPattern1 z) : ∀ k, Even (z k) :=
  fun k => even_of_isPattern1 hz k


-- @@ L33-49 verbatim
/--
Leech lattice membership for Pattern II: an integer vector `z` with pattern `((±2)^8, 0^16)`
whose residue word lies in `leechParityCode` and whose coordinate sum is divisible by `8`
defines a Leech lattice vector `vecOfScaledStd z`.
-/
public theorem mem_leechLattice_of_typeII
    (z : Fin 24 → ℤ)
    (hz : isPattern1 z)
    (hw :
      Shell4IsometryLeechConstructionA.halfWord z ∈ Shell4IsometryLeechParityCode.leechParityCode)
    (hsum : (8 : ℤ) ∣ ∑ k : Fin 24, z k) :
  vecOfScaledStd z ∈ (LeechLattice : Set ℝ²⁴) := by
  have hzEven : ∀ k, Even (z k) := pattern1_even z hz
  simpa [vecOfScaledStd_eq_leechD24_vecOfScaledStd,
    Shell4IsometryLeechConstructionA.vecOfScaledStd] using
    (Shell4IsometryLeechConstructionA.mem_LeechLattice_vecOfScaledStd_of_even_of_halfWord_mem
      (z := z) hzEven hw hsum)


-- @@ L51-51 verbatim
end Shell4IsometryLeechMembership


-- @@ L53-53 verbatim
end


-- @@ L55-55 verbatim
end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
