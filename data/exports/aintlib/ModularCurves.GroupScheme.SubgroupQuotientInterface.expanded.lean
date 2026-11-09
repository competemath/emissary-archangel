import ModularCurves.GroupScheme.Subgroup


-- @@ L3-13 verbatim
/-!
# The `G`-invariance interface for the quotient `E/G`

**Low interface layer (T-G3d-infra).** The descent condition
`FiniteLocallyFreeSubgroup.IsInvariant` on a morphism out of `E`, extracted here — *below*
`TranslationAction` — so that the quotient construction (which imports `TranslationAction`) can in
turn be imported by `SubgroupQuotient.lean` when discharging the six pins, with no import cycle.
Only `IsInvariant` (+ `IsInvariant.comp`) lives here; the pins
(`quotient` / `quotientS` / `quotientπ` / …) stay in `SubgroupQuotient.lean`, where they are
discharged against the glue construction.
-/


-- @@ L15-15 verbatim
open AlgebraicGeometry CategoryTheory Limits


-- @@ L17-17 verbatim
universe u


-- @@ L19-19 verbatim
namespace ModularCurves


-- @@ L21-21 verbatim
namespace EllipticCurve


-- @@ L23-23 verbatim
variable {S : Scheme.{u}} {E : EllipticCurve S}


-- @@ L25-33 verbatim
/-- A morphism `f : E ⟶ Y` is **invariant** under the translation action of the finite locally free
subgroup scheme `G ⊆ E` when `f(x + t) = f(x)` for every point `x : E.Point g` and every `G`-point
`t` (`t ∈ G.pointSubgroup g`). This is the functor-of-points form of the coequalizer condition cut
out by the two maps `G ×_S E ⇉ E` (translate `(t, x) ↦ x + t`, project `(t, x) ↦ x`); it is the
universal condition for a morphism to factor through `E/G`. -/
def FiniteLocallyFreeSubgroup.IsInvariant (G : FiniteLocallyFreeSubgroup E) {Y : Scheme.{u}}
    (f : E.E ⟶ Y) : Prop :=
  ∀ ⦃T : Scheme.{u}⦄ (g : T ⟶ S) (x t : E.Point g), t ∈ G.pointSubgroup g →
    (x + t).1 ≫ f = x.1 ≫ f


-- @@ L35-35 verbatim
namespace FiniteLocallyFreeSubgroup


-- @@ L37-40 verbatim
/-- Invariance is preserved by post-composition: if `f` collapses `G`-translates, so does `f ≫ h`. -/
theorem IsInvariant.comp {G : FiniteLocallyFreeSubgroup E} {Y Z : Scheme.{u}} {f : E.E ⟶ Y}
    (hf : G.IsInvariant f) (h : Y ⟶ Z) : G.IsInvariant (f ≫ h) := fun _ g x t ht => by
  rw [← Category.assoc, hf g x t ht, Category.assoc]


-- @@ L42-48 verbatim
/-- **The killing-integer hypothesis** of the quotient construction: `G` is annihilated by
multiplication by some positive integer `N` (`ι ≫ [N] = 0` as maps `G ⟶ E`). Every torsion
subgroup `E[N]` satisfies it by definition of the kernel (the pullback condition), and every
constant-rank subgroup satisfies it with `N = rank` (Deligne–Oort–Tate, KM 1.4.2). The option-γ
glue construction of `E/G` consumes exactly this datum. -/
class HasKillingInt (G : FiniteLocallyFreeSubgroup E) : Prop where
  exists_kill : ∃ N : ℕ, N ≠ 0 ∧ G.ι ≫ E.mulByHom N = G.π ≫ E.zero


-- @@ L50-50 verbatim
variable (G : FiniteLocallyFreeSubgroup E) [G.HasKillingInt]


-- @@ L52-54 verbatim
/-- A chosen killing integer for `G` (positive: `NeZero G.killN`; kills: `killN_spec`). -/
noncomputable def killN : ℕ :=
  (HasKillingInt.exists_kill (G := G)).choose


-- @@ L56-57 verbatim
instance : NeZero G.killN :=
  ⟨(HasKillingInt.exists_kill (G := G)).choose_spec.1⟩


-- @@ L59-61 verbatim
/-- The chosen killing integer kills `G`. -/
theorem killN_spec : G.ι ≫ E.mulByHom G.killN = G.π ≫ E.zero :=
  (HasKillingInt.exists_kill (G := G)).choose_spec.2


-- @@ L63-63 verbatim
end FiniteLocallyFreeSubgroup


-- @@ L65-65 verbatim
end EllipticCurve


-- @@ L67-67 verbatim
end ModularCurves
