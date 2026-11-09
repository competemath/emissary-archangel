/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import ModularCurves.LevelStructure.Incidence
import ModularCurves.GroupScheme.CyclicSubgroup


-- @@ L9-26 verbatim
/-!
# Level spaces over the Weierstrass atlas (T-W8)

The level spaces `U_{Γ₁(N)}`, `U_{Γ(N)}` (and `U_{Γ₀(N)}`) as closed subschemes cut out of the
`N`-torsion (resp. its self-product) by the D-stream Cartier incidence loci. Parametric over an
arbitrary `E : EllipticCurve S`; the universal instantiation over `weierstrassAtlas` follows once
the universal `EllipticCurve` is available. The classifying/universal properties (`_spec`) are the
representability presentations `T-E7` and the H-stream consume.

Per v10.24(b) each level-space definition ships its opaque interface — the closed immersion and
the universal-property `_spec` — in this same file; downstream consumers use `_spec`, never the
raw `Classical.choose`.

## Main definitions

* `levelSpaceΓ₁ E N` : `U_{Γ₁(N)}`, closed in `E[N]`, cut by the exact-order locus.
* `levelSpaceΓ E N`   : `U_{Γ(N)}`, closed in `E[N] ×_S E[N]`, cut by the full-level locus.
-/


-- @@ L28-28 verbatim
open AlgebraicGeometry CategoryTheory Limits


-- @@ L30-30 verbatim
universe u


-- @@ L32-32 verbatim
namespace ModularCurves


-- @@ L34-34 verbatim
variable {S : Scheme.{u}} (E : EllipticCurve S) (N : ℕ) [NeZero N]


-- @@ L36-36 verbatim
/-! ### `U_{Γ₁(N)}` — exact-order-`N` level structures -/


-- @@ L38-41 verbatim
/-- **(T-W8, `U_{Γ₁(N)}`)** The `Γ₁(N)` level space: the closed subscheme of `E[N]` where the
tautological torsion point has exact order `N`, cut out by `exists_exactOrderLocus`. -/
noncomputable def levelSpaceΓ₁ : Scheme.{u} :=
  (exists_exactOrderLocus E N).choose.subscheme


-- @@ L43-45 verbatim
/-- The closed immersion `U_{Γ₁(N)} ↪ E[N]`. -/
noncomputable def levelSpaceΓ₁ι : levelSpaceΓ₁ E N ⟶ E.torsion N :=
  (exists_exactOrderLocus E N).choose.subschemeι


-- @@ L47-56 verbatim
/-- **Opaque interface (v10.24(b))** — the universal property of `U_{Γ₁(N)}`: a point of `E`
killed by `N` over `t` factors (via its classifying map to `E[N]`) through `U_{Γ₁(N)}` iff it has
exact order `N` on the base-changed curve. -/
theorem levelSpaceΓ₁_spec :
    ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S) (P : E.Point t)
      (hP : P.1 ≫ E.mulByHom N = t ≫ E.zero),
      (∃ h : T ⟶ levelSpaceΓ₁ E N, h ≫ levelSpaceΓ₁ι E N = E.pointToTorsion P hP) ↔
        EllipticCurve.Section.HasExactOrder (E.baseChange t)
          (EllipticCurve.Point.asSection E t P) N :=
  (exists_exactOrderLocus E N).choose_spec


-- @@ L58-58 verbatim
/-! ### `U_{Γ(N)}` — Drinfeld full level-`N` structures -/


-- @@ L60-63 verbatim
/-- **(T-W8, `U_{Γ(N)}`)** The `Γ(N)` level space: the closed subscheme of `E[N] ×_S E[N]` where
the tautological pair is a Drinfeld full level-`N` structure, cut out by `exists_fullLevelLocus`. -/
noncomputable def levelSpaceΓ : Scheme.{u} :=
  (exists_fullLevelLocus E N).choose.subscheme


-- @@ L65-68 verbatim
/-- The closed immersion `U_{Γ(N)} ↪ E[N] ×_S E[N]`. -/
noncomputable def levelSpaceΓι :
    levelSpaceΓ E N ⟶ pullback (E.torsionπ N) (E.torsionπ N) :=
  (exists_fullLevelLocus E N).choose.subschemeι


-- @@ L70-81 verbatim
/-- **Opaque interface (v10.24(b))** — the universal property of `U_{Γ(N)}`: a pair of points of
`E` killed by `N` over `t` factors (via its classifying map to `E[N] ×_S E[N]`) through
`U_{Γ(N)}` iff it is a Drinfeld full level-`N` structure. -/
theorem levelSpaceΓ_spec :
    ∀ ⦃T : Scheme.{u}⦄ (t : T ⟶ S) (P Q : E.Point t)
      (hP : P.1 ≫ E.mulByHom N = t ≫ E.zero)
      (hQ : Q.1 ≫ E.mulByHom N = t ≫ E.zero),
      (∃ h : T ⟶ levelSpaceΓ E N, h ≫ levelSpaceΓι E N =
          pullback.lift (E.pointToTorsion P hP) (E.pointToTorsion Q hQ) (by simp)) ↔
        (E.baseChange t).IsFullLevel N (EllipticCurve.Point.asSection E t P)
          (EllipticCurve.Point.asSection E t Q) :=
  (exists_fullLevelLocus E N).choose_spec


-- @@ L83-91 verbatim
/-! ### `U_{Γ₀(N)}` — cyclic rank-`N` subgroup structures

Unlike `Γ₁(N)`/`Γ(N)`, the `Γ₀(N)` level datum is **structure, not predicate**: it is a *choice*
of a cyclic finite locally free rank-`N` subgroup scheme, not a condition cutting a locus inside a
fixed torsion scheme. So there is no `levelSpaceΓ₀` closed subscheme of the Γ₁/Γ shape — the
`Γ₀(N)` "level space" is the moduli of such subgroup schemes, whose representability is the
separate Γ₀ GATE (SG3 closedness of cyclicity). The def-of-record `GammaZeroStructure`
(`GroupScheme/CyclicSubgroup.lean`, T-SG2) is that datum; the T-W8 name below is a thin alias so
the three level types share a uniform entry point. -/


-- @@ L93-97 verbatim
/-- **(T-W8, `U_{Γ₀(N)}` — as far as T-SG2 reaches)** The `Γ₀(N)` level datum over `S`: a cyclic
finite locally free rank-`N` subgroup scheme of `E` (`GammaZeroStructure`, T-SG2's def-of-record).
It is a *structure* on `E/S`, not a torsion-point locus, so it has no closed-subscheme
presentation of the `Γ₁`/`Γ` shape; its representability is the separate SG3 GATE. -/
abbrev levelStructureΓ₀ := EllipticCurve.GammaZeroStructure E N


-- @@ L99-99 verbatim
end ModularCurves
