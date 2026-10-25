import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField


-- @@ L5-21 verbatim
/-! # An ample line bundle on a proper scheme gives a closed immersion into projective space

Stacks 0B5T(1)–(2), in the form needed for Serre vanishing: if `X` is proper over a
field `k` and `L` is an ample line bundle on `X`, then there are `d > 0`, `N` and a **closed immersion**
`i : X ⟶ P^N_k` over `k` with `i^* O(1) ≅ L^{⊗d}`.

Proof. `X` is quasi-compact (part of `IsAmple`) and of finite type over `k` (proper), so Stacks 01VU/01VR
(`IsAmple.exists_projectivizationMorphism_isImmersion`)
give `d > 0` and finitely many sections `P_ℓ ∈ Γ(X, L^{⊗d})` without common zero such that the induced
`i := projectivizationMorphism (L^{⊗d}) P : X ⟶ P^N_k` is an immersion; it is a `k`-morphism
(`projectivizationMorphism_comp_over`) and `i^* O(1) ≅ L^{⊗d}` (`projectivizationMorphism_pullback_twist`).
Since `X → Spec k` is proper and `P^N_k → Spec k` is separated, `i` is proper (`IsProper.of_comp`), and a
proper monomorphism (immersions are monomorphisms) is a closed immersion (Mathlib
`IsClosedImmersion.iff_isProper_and_mono`, Stacks 04XV).

Source: Stacks 0B5T (proof of (1)), 01VU, 01VR.
-/


-- @@ L23-23 verbatim
set_option autoImplicit false

-- @@ L24-24 verbatim
set_option maxHeartbeats 400000


-- @@ L26-26 verbatim
universe u


-- @@ L28-28 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L29-29 verbatim
open scoped AlgebraicGeometry


-- @@ L31-31 verbatim
noncomputable section


-- @@ L33-59 verbatim
theorem AlgebraicGeometry.exists_closedImmersion_projectiveSpace_pullback_twist_iso {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hX : IsProperOver k X) (L : X.Modules) [L.IsLineBundle] (hL : AlgebraicGeometry.IsAmple L) :
    ∃ (d N : ℕ) (_ : 0 < d) (i : X ⟶ ProjectiveSpace N k) (_ : AlgebraicGeometry.IsClosedImmersion i),
      i.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) ∧
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback i).obj (projectiveSpaceTwist k N 1) ≅
        AlgebraicGeometry.Scheme.Modules.tensorPow L d) := by
  letI : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hX
  haveI : CompactSpace X := hL.1
  obtain ⟨d, N, hd, P, hP, hi⟩ :=
    AlgebraicGeometry.IsAmple.exists_projectivizationMorphism_isImmersion k X L hL
  let i : X ⟶ ProjectiveSpace N k :=
    projectivizationMorphism (k := k) (AlgebraicGeometry.Scheme.Modules.tensorPow L d) P hP
  have hover : i.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨projectivizationMorphism_comp_over (k := k) _ P hP⟩
  haveI : AlgebraicGeometry.IsImmersion i := hi
  haveI : AlgebraicGeometry.IsProper
      (i ≫ ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    rw [hover.1]
    infer_instance
  haveI : AlgebraicGeometry.IsProper i :=
    AlgebraicGeometry.IsProper.of_comp i (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have hci : AlgebraicGeometry.IsClosedImmersion i :=
    (AlgebraicGeometry.IsClosedImmersion.iff_isProper_and_mono i).2 ⟨inferInstance, inferInstance⟩
  obtain ⟨θ, -⟩ := projectivizationMorphism_pullback_twist (k := k)
    (AlgebraicGeometry.Scheme.Modules.tensorPow L d) P hP
  exact ⟨d, N, hd, i, hci, hover, ⟨θ⟩⟩


-- @@ L61-61 verbatim
end
