/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/

import LieLean.Algebra.QuantumGroup.RestrictedBraidIsometry.Isometry
import LieLean.Algebra.QuantumGroup.LusztigF.BraidIntersection


-- @@ L10-17 verbatim
/-!
# Adapted PBW pairing and norm recursion

The actual inverse braid preserves adapted-tail pairings on integral PBW preimages.
This gives a one-step pairing and norm recursion for arbitrary reduced words,
without an additional tail-kernel premise. No full product norm or lattice result
is asserted here.
-/


-- @@ L19-19 verbatim
noncomputable section

-- @@ L20-20 verbatim
open LieLean LieLean.QuantumGroup LusztigF

-- @@ L21-21 verbatim
open RestrictedBraidIsometry

-- @@ L22-22 verbatim
namespace RestrictedBraidConsumer

-- @@ L23-23 verbatim
local notation "𝕂" => RatFunc ℚ

-- @@ L24-24 verbatim
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)

-- @@ L25-25 verbatim
attribute [local instance] neZero_ratFunc_X

-- @@ L26-27 verbatim
variable {I Y : Type*} [Finite I] [DecidableEq I] [AddCommGroup Y]
  {D : LusztigCartanDatum I} (R : D.RootDatum Y)


-- @@ L29-35 verbatim
/-- Importing consumer on arbitrary actual left-kernel elements and actual braid images. -/
theorem actual_maps (i : I) {x z y w : Quotient D 𝕧}
    (hx : quotientLDeriv D i x = 0) (hz : quotientLDeriv D i z = 0)
    (hxy : braidEquivOfNotRoot R ratFunc_X_not_root i (quotientPlus R x) = quotientPlus R y)
    (hzw : braidEquivOfNotRoot R ratFunc_X_not_root i (quotientPlus R z) = quotientPlus R w) :
    quotientForm D y w = quotientForm D x z :=
  restricted_braid_isometry R i hx hz hxy hzw


-- @@ L37-37 verbatim
open Modified

-- @@ L38-38 verbatim
attribute [local instance] laurentAlgebraK laurentAlgebraU laurentTowerU

-- @@ L39-40 verbatim
variable {W : Type*} [Group W] {cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W}
  {i : I} {w : List I}


-- @@ L42-50 verbatim
/-- The actual inverse-braid adapted tail, with no assumed tail-kernel or isometry premise. -/
theorem adapted_tail_pairing (hw : cs.IsReduced (i :: w)) (c d : Fin w.length → ℕ) :
    quotientForm D (integralPBWPreimage R hw (Fin.cons 0 c))
      (integralPBWPreimage R hw (Fin.cons 0 d)) =
    quotientForm D (integralPBWPreimage R (w := w) (by simpa using hw.drop 1) c)
      (integralPBWPreimage R (w := w) (by simpa using hw.drop 1) d) := by
  exact restricted_inverse_braid_isometry R i
    (quotientPlus_integralPBWPreimage_cons_zero R hw c).symm
    (quotientPlus_integralPBWPreimage_cons_zero R hw d).symm


-- @@ L52-67 verbatim
/-- One genuine PBW norm/orthogonality recursion step on the original preimages. -/
theorem adapted_pbw_pairing_recursion (hw : cs.IsReduced (i :: w))
    (c d : Fin (i :: w).length → ℕ) :
    quotientForm D (integralPBWPreimage R hw c) (integralPBWPreimage R hw d) =
      if c 0 = d 0 then GrandLoop.coefU D 𝕧 i (c 0) *
        quotientForm D
          (integralPBWPreimage R (w := w) (by simpa using hw.drop 1) (fun n ↦ c n.succ))
          (integralPBWPreimage R (w := w) (by simpa using hw.drop 1) (fun n ↦ d n.succ))
      else 0 := by
  rw [integralPBWPreimage_cons R hw c, integralPBWPreimage_cons R hw d,
    quotientForm_divided_mul_of_mem_skewGenerators D i (c 0) (d 0)
      ((mem_quotientSkewGenerators_iff D i _).mpr
        (quotientLDeriv_integralPBWPreimage_cons_zero R hw (fun n ↦ c n.succ)))
      ((mem_quotientSkewGenerators_iff D i _).mpr
        (quotientLDeriv_integralPBWPreimage_cons_zero R hw (fun n ↦ d n.succ))),
    adapted_tail_pairing R hw]


-- @@ L69-77 verbatim
/-- Actual PBW adapted-tail norm recursion, not a norm assumption. -/
theorem adapted_pbw_norm_recursion (hw : cs.IsReduced (i :: w))
    (c : Fin (i :: w).length → ℕ) :
    quotientForm D (integralPBWPreimage R hw c) (integralPBWPreimage R hw c) =
      GrandLoop.coefU D 𝕧 i (c 0) *
        quotientForm D
          (integralPBWPreimage R (w := w) (by simpa using hw.drop 1) (fun n ↦ c n.succ))
          (integralPBWPreimage R (w := w) (by simpa using hw.drop 1) (fun n ↦ c n.succ)) := by
  simpa only [ite_true] using adapted_pbw_pairing_recursion R hw c c


-- @@ L79-79 verbatim
end RestrictedBraidConsumer
