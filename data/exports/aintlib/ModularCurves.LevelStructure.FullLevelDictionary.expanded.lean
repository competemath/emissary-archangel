/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.LevelStructure.FullLevelBridge


-- @@ L8-17 verbatim
/-!
# The T-D8 dictionary, axiom-clean form

`isFullLevel_iff_naive'` — the Drinfeld/naive full-level dictionary (KM 3.7 / 1.4.4 for
Γ(N), `N` invertible), proven from the COMPLETE T-D8 bridge
`fullLevel_divisor_iff_naive_gen'` (`FullLevelBridge.lean`, both halves axiom-clean,
v10.304-KM) instead of the `Basic.lean:115` register-box shell (which stays sorried only
for import-order reasons). Consumers of `isFullLevel_iff_naive` repoint here; the
statement is identical.
-/


-- @@ L19-19 verbatim
universe u


-- @@ L21-21 verbatim
namespace ModularCurves


-- @@ L23-23 verbatim
namespace EllipticCurve


-- @@ L25-25 verbatim
open AlgebraicGeometry


-- @@ L27-27 verbatim
variable {S : AlgebraicGeometry.Scheme.{u}} (E : EllipticCurve S)


-- @@ L29-42 verbatim
/-- **(T-D8 = KM 3.7 / KM 1.4.4 upgraded to Γ(N), AXIOM-CLEAN)** For `N` invertible on
`S`, Drinfeld full-level structures and naive full-level structures coincide. Statement
identical to `isFullLevel_iff_naive` (`LevelStructure/Basic.lean`); proven from the
complete bridge `fullLevel_divisor_iff_naive_gen'` — no register box. -/
theorem isFullLevel_iff_naive' (N : ℕ) [NeZero N] (hN : NIsInvertible S N)
    (P Q : E.Section) :
    E.IsFullLevel N P Q ↔ E.IsNaiveFullLevel N P Q := by
  constructor
  · rintro ⟨⟨hP, hQ⟩, hdiv⟩
    exact ⟨⟨hP, hQ⟩,
      (fullLevel_divisor_iff_naive_gen' E N hN P Q hP hQ).mp hdiv⟩
  · rintro ⟨⟨hP, hQ⟩, hgen⟩
    exact ⟨⟨hP, hQ⟩,
      (fullLevel_divisor_iff_naive_gen' E N hN P Q hP hQ).mpr hgen⟩


-- @@ L44-44 verbatim
end EllipticCurve


-- @@ L46-46 verbatim
end ModularCurves
