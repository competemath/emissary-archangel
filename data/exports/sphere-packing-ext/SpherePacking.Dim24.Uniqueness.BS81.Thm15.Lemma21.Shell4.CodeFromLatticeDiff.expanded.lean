module
public import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.CodeFromLattice
import SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.ScaledCoord



-- @@ L6-16 verbatim
/-!
# Even differences lie in `codeFromLattice`

If `x,y ∈ latticeL C` have integer scaled coordinates `zx, zy`, then the mod-`2` word obtained from
the even coordinate difference `zx - zy` lies in `codeFromLattice`. This is a basic helper used in
the Type III bound in BS81 Lemma 21.

## Main statement
* `Shell4IsometryCodeFromLatticeDiff.halfWord_sub_mem_codeFromLattice`

-/



-- @@ L19-19 verbatim
namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
open Uniqueness.BS81

-- @@ L24-24 verbatim
open Uniqueness.BS81.Thm15.Lemma21


-- @@ L26-26 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L28-28 verbatim
namespace Shell4IsometryCodeFromLatticeDiff


-- @@ L30-30 verbatim
local notation "code" => CodeFromLattice.codeFromLattice


-- @@ L32-51 verbatim
/-- If `zx-zy` is coordinatewise even, then `halfWord (zx-zy)` lies in the extracted code. -/
public theorem halfWord_sub_mem_codeFromLattice
    (C : Set ℝ²⁴)
    (hDn : Uniqueness.BS81.Thm15.Lemma20.ContainsDn C 24)
    {x y : ℝ²⁴}
    (hx : x ∈ (latticeL C : Set ℝ²⁴))
    (hy : y ∈ (latticeL C : Set ℝ²⁴))
    (zx zy : Fin 24 → ℤ)
    (hzx : ∀ i : Fin 24, scaledCoord hDn.e i x = (zx i : ℝ))
    (hzy : ∀ i : Fin 24, scaledCoord hDn.e i y = (zy i : ℝ))
    (hEven : ∀ i : Fin 24, Even (zx i - zy i)) :
    (fun i : Fin 24 => (((zx i - zy i) / 2 : ℤ) : ZMod 2)) ∈ code (C := C) hDn := by
  refine ⟨x - y, (latticeL C).sub_mem hx hy, zx - zy, ?_, hEven, fun _ => rfl⟩
  · intro i
    calc
      scaledCoord hDn.e i (x - y) =
          scaledCoord hDn.e i x - scaledCoord hDn.e i y :=
            scaledCoord_sub (e := hDn.e) i x y
      _ = (zx i : ℝ) - (zy i : ℝ) := by simp [hzx i, hzy i]
      _ = ((zx i - zy i : ℤ) : ℝ) := by norm_cast


-- @@ L53-53 verbatim
end Shell4IsometryCodeFromLatticeDiff


-- @@ L55-55 verbatim
end


-- @@ L57-57 verbatim
end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma21.IsometrySteps
