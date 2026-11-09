/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import HasseWeil.HasseBound.WeilPairing.FrobeniusFunctionFieldEquiv
import HasseWeil.HasseBound.WeilPairing.FrobeniusGenericCovariance


-- @@ L9-47 verbatim
/-!
# The translation conjugation for the arithmetic Frobenius `σ` (Silverman III.8.1d)

This file proves the **conjugation / translation-covariance** of the concrete arithmetic
Frobenius `σ = frobeniusFunctionFieldEquiv W` of `K̄(E)`:

  `σ (τ_S g) = τ_{π̄ S} (σ g)`   for every `g : K̄(E)`,

where `τ_S = translateAlgEquivOfPoint (W.baseChange K̄) S` and
`π̄ S = frobeniusHomBaseChange S = geomFrobeniusPoint S = (S_x^q, S_y^q)`.

The main theorem is `frobeniusFunctionFieldEquiv_conj`.

## Route (point-level via the generic point, then ring-hom ext)

The proof first establishes the conjugation at the generic point, then reads off the generator
coordinates and upgrades them to a ring-hom equality by `ringHom_ext_base_x_y_gen`.

* `σ` **fixes** the generators (`frobeniusFunctionFieldEquiv_x_gen/_y_gen`: it `q`-powers the
  `K̄`-coefficients and fixes the `𝔽_q`-rational `x_gen, y_gen`), so `Point.map σ_K` *fixes the
  generic point* `P_gen = (x_gen, y_gen)`;
* `Point.map σ_K` sends the lift of a `K̄`-point `S` to the lift of its geometric Frobenius
  `π̄ S = (S_x^q, S_y^q)` (`sigmaConjugation_lift_twist`), mirroring
  `frobeniusGenericCovariance_lift_twist`;
* therefore both `Point.map σ_K (Point.map τ_S P_gen)` and
  `Point.map τ_{π̄ S} (Point.map σ_K P_gen)` equal `P_gen + lift (π̄ S)`;
  see `sigmaConjugation_point`.

Reading off coordinates (`Point.map_map`) gives the two generator equalities, and the ring-hom ext
upgrades them to the pointwise conjugation `frobeniusFunctionFieldEquiv_conj`.

`σ_K` is `σ` viewed as a `K`-algebra hom `K̄(E) →ₐ[K] K̄(E)`
(`frobeniusFunctionFieldEquivK`).  Typing the `Point.map` over the base curve `W` sidesteps the
`K̄`-linearity diamond, exactly as in `FrobeniusGenericCovariance.lean`.

## References

* Silverman, *The Arithmetic of Elliptic Curves*, III.8.1 (Galois equivariance of the Weil pairing).
-/


-- @@ L49-49 verbatim
open WeierstrassCurve HasseWeil.Curves Polynomial


-- @@ L51-51 verbatim
namespace HasseWeil.WeilPairing


-- @@ L53-53 verbatim
open HasseWeil


-- @@ L55-55 verbatim
section RingHomExt


-- @@ L57-57 verbatim
variable {F : Type*} [Field F] [DecidableEq F]

-- @@ L58-58 verbatim
variable (W : WeierstrassCurve F) [W.toAffine.IsElliptic]


-- @@ L60-60 verbatim
local notation "KE" => W.toAffine.FunctionField


-- @@ L62-96 verbatim
omit [DecidableEq F] [W.toAffine.IsElliptic] in
/-- Ring-hom extensionality from agreement on the base, `x_gen`, and `y_gen`. -/
theorem ringHom_ext_base_x_y_gen (ψ₁ ψ₂ : KE →+* KE)
    (hbase : ∀ a : F, ψ₁ (algebraMap F KE a) = ψ₂ (algebraMap F KE a))
    (hx : ψ₁ (x_gen W) = ψ₂ (x_gen W)) (hy : ψ₁ (y_gen W) = ψ₂ (y_gen W)) :
    ψ₁ = ψ₂ := by
  apply IsFractionRing.ringHom_ext (A := W.toAffine.CoordinateRing)
  suffices h : (ψ₁.comp (algebraMap W.toAffine.CoordinateRing KE)) =
      (ψ₂.comp (algebraMap W.toAffine.CoordinateRing KE)) by
    intro r
    exact RingHom.congr_fun h r
  apply AdjoinRoot.ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro a
      change ψ₁ (algebraMap W.toAffine.CoordinateRing KE
          ((AdjoinRoot.of W.toAffine.polynomial) (C a))) =
        ψ₂ (algebraMap W.toAffine.CoordinateRing KE
          ((AdjoinRoot.of W.toAffine.polynomial) (C a)))
      have hca : (algebraMap W.toAffine.CoordinateRing KE)
          ((AdjoinRoot.of W.toAffine.polynomial) (C a)) = algebraMap F KE a := by
        rw [show (AdjoinRoot.of W.toAffine.polynomial) (C a) =
            algebraMap F W.toAffine.CoordinateRing a from rfl,
          ← IsScalarTower.algebraMap_apply]
      rw [hca]
      exact hbase a
    · change ψ₁ (algebraMap W.toAffine.CoordinateRing KE
          ((AdjoinRoot.of W.toAffine.polynomial) X)) =
        ψ₂ (algebraMap W.toAffine.CoordinateRing KE
          ((AdjoinRoot.of W.toAffine.polynomial) X))
      exact hx
  · change ψ₁ (algebraMap W.toAffine.CoordinateRing KE
        (AdjoinRoot.root W.toAffine.polynomial)) =
      ψ₂ (algebraMap W.toAffine.CoordinateRing KE
        (AdjoinRoot.root W.toAffine.polynomial))
    exact hy


-- @@ L98-98 verbatim
end RingHomExt


-- @@ L100-119 verbatim
/-- `CoordinateRing.map f` fixes the `X`-generator. -/
theorem coordRingMap_X {R S : Type*} [CommRing R] [CommRing S]
    (W' : WeierstrassCurve.Affine R) (f : R →+* S) :
    WeierstrassCurve.Affine.CoordinateRing.map W' f
        (algebraMap (Polynomial R) W'.CoordinateRing Polynomial.X) =
      algebraMap (Polynomial S) (W'.map f).toAffine.CoordinateRing Polynomial.X := by
  have h1 : (algebraMap (Polynomial R) W'.CoordinateRing Polynomial.X) =
      WeierstrassCurve.Affine.CoordinateRing.mk W' (Polynomial.C Polynomial.X) := by
    change (AdjoinRoot.of W'.polynomial) Polynomial.X = _
    rw [AdjoinRoot.of]
    rfl
  rw [h1, WeierstrassCurve.Affine.CoordinateRing.map_mk]
  have h2 : ((Polynomial.C Polynomial.X).map (Polynomial.mapRingHom f)) =
      Polynomial.C Polynomial.X := by
    simp
  rw [h2]
  change (AdjoinRoot.mk (W'.map f).toAffine.polynomial) (Polynomial.C Polynomial.X) = _
  rw [show (algebraMap (Polynomial S) (W'.map f).toAffine.CoordinateRing Polynomial.X) =
      (AdjoinRoot.of (W'.map f).toAffine.polynomial) Polynomial.X from rfl, AdjoinRoot.of]
  rfl


-- @@ L121-127 verbatim
/-- `CoordinateRing.map f` sends the root to the root of the mapped polynomial. -/
theorem coordRingMap_root {R S : Type*} [CommRing R] [CommRing S]
    (W' : WeierstrassCurve.Affine R) (f : R →+* S) :
    WeierstrassCurve.Affine.CoordinateRing.map W' f (AdjoinRoot.root W'.polynomial) =
      AdjoinRoot.root (W'.map f).toAffine.polynomial := by
  rw [WeierstrassCurve.Affine.CoordinateRing.map]
  exact AdjoinRoot.lift_root _


-- @@ L129-129 verbatim
section BaseChange


-- @@ L131-131 verbatim
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

-- @@ L132-132 verbatim
variable (W : WeierstrassCurve K) [W.toAffine.IsElliptic]


-- @@ L134-134 verbatim
noncomputable local instance instDecEqACFC : DecidableEq (AlgebraicClosure K) := Classical.decEq _


-- @@ L136-136 verbatim
variable [(W.baseChange (AlgebraicClosure K)).toAffine.IsElliptic]


-- @@ L138-161 verbatim
/-- The arithmetic Frobenius `σ = frobeniusFunctionFieldEquiv W` fixes `x_gen`. -/
theorem frobeniusFunctionFieldEquiv_x_gen :
    frobeniusFunctionFieldEquiv W (x_gen (W.baseChange (AlgebraicClosure K))) =
      x_gen (W.baseChange (AlgebraicClosure K)) := by
  rw [frobeniusFunctionFieldEquiv, RingEquiv.trans_apply]
  rw [show x_gen (W.baseChange (AlgebraicClosure K)) =
      algebraMap (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
        (algebraMap (Polynomial (AlgebraicClosure K))
          (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing Polynomial.X) from rfl]
  rw [ffFrobEquivRaw, IsFractionRing.ringEquivOfRingEquiv_algebraMap, crFrobEquiv_apply,
    coordRingMap_X]
  rw [ffFrobCast]
  have key : ∀ (V : WeierstrassCurve (AlgebraicClosure K))
      (h : V = W.baseChange (AlgebraicClosure K)),
      (RingEquiv.cast
          (R := fun (U : WeierstrassCurve (AlgebraicClosure K)) ↦ U.toAffine.FunctionField) h)
        (algebraMap V.toAffine.CoordinateRing V.toAffine.FunctionField
          (algebraMap (Polynomial (AlgebraicClosure K)) V.toAffine.CoordinateRing Polynomial.X)) =
      x_gen (W.baseChange (AlgebraicClosure K)) := by
    intro V h
    subst h
    rfl
  exact key _ (map_coeffFrobEquiv_eq W)


-- @@ L163-185 verbatim
/-- The arithmetic Frobenius `σ = frobeniusFunctionFieldEquiv W` fixes `y_gen`. -/
theorem frobeniusFunctionFieldEquiv_y_gen :
    frobeniusFunctionFieldEquiv W (y_gen (W.baseChange (AlgebraicClosure K))) =
      y_gen (W.baseChange (AlgebraicClosure K)) := by
  rw [frobeniusFunctionFieldEquiv, RingEquiv.trans_apply]
  rw [show y_gen (W.baseChange (AlgebraicClosure K)) =
      algebraMap (W.baseChange (AlgebraicClosure K)).toAffine.CoordinateRing
          (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField
        (AdjoinRoot.root (W.baseChange (AlgebraicClosure K)).toAffine.polynomial) from rfl]
  rw [ffFrobEquivRaw, IsFractionRing.ringEquivOfRingEquiv_algebraMap, crFrobEquiv_apply,
    coordRingMap_root]
  rw [ffFrobCast]
  have key : ∀ (V : WeierstrassCurve (AlgebraicClosure K))
      (h : V = W.baseChange (AlgebraicClosure K)),
      (RingEquiv.cast
          (R := fun (U : WeierstrassCurve (AlgebraicClosure K)) ↦ U.toAffine.FunctionField) h)
        (algebraMap V.toAffine.CoordinateRing V.toAffine.FunctionField
          (AdjoinRoot.root V.toAffine.polynomial)) =
      y_gen (W.baseChange (AlgebraicClosure K)) := by
    intro V h
    subst h
    rfl
  exact key _ (map_coeffFrobEquiv_eq W)


-- @@ L187-196 verbatim
/-- The arithmetic Frobenius `σ = frobeniusFunctionFieldEquiv W` fixes the base field. -/
theorem frobeniusFunctionFieldEquiv_baseField (a : K) :
    frobeniusFunctionFieldEquiv W
        (algebraMap K (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a) =
      algebraMap K (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField a := by
  rw [IsScalarTower.algebraMap_apply K (AlgebraicClosure K)
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField,
    frobeniusFunctionFieldEquiv_algebraMap]
  congr 1
  rw [← map_pow, FiniteField.pow_card]


-- @@ L198-203 verbatim
/-- The arithmetic Frobenius `σ` as a `K`-algebra hom. -/
noncomputable def frobeniusFunctionFieldEquivK :
    (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[K]
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField where
  __ := (frobeniusFunctionFieldEquiv W).toRingHom
  commutes' a := frobeniusFunctionFieldEquiv_baseField W a


-- @@ L205-207 verbatim
@[simp] theorem frobeniusFunctionFieldEquivK_apply
    (z : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    frobeniusFunctionFieldEquivK W z = frobeniusFunctionFieldEquiv W z := rfl


-- @@ L209-220 verbatim
omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] in
/-- The image of the generic point under a `K`-algebra hom, in coordinates. -/
theorem map_genericPoint_some
    (h : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField →ₐ[K]
      (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    ∃ hns, WeierstrassCurve.Affine.Point.map (W' := W) h
        (HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K))) =
      Affine.Point.some (h (x_gen (W.baseChange (AlgebraicClosure K))))
        (h (y_gen (W.baseChange (AlgebraicClosure K)))) hns := by
  rw [HasseWeil.genericPoint_xOf_some]
  exact ⟨_, WeierstrassCurve.Affine.Point.map_some (W' := W) (f := h)
    (generic_nonsingular (W.baseChange (AlgebraicClosure K)))⟩


-- @@ L222-226 verbatim
/-- The point-level action induced by the arithmetic Frobenius on function-field points. -/
noncomputable def sigmaFunctionFieldPointKbar :
    (W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point →+
      (W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point :=
  WeierstrassCurve.Affine.Point.map (W' := W) (frobeniusFunctionFieldEquivK W)


-- @@ L228-231 verbatim
theorem sigmaFunctionFieldPointKbar_apply
    (P : (W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point) :
    sigmaFunctionFieldPointKbar W P =
      WeierstrassCurve.Affine.Point.map (W' := W) (frobeniusFunctionFieldEquivK W) P := rfl


-- @@ L233-243 verbatim
omit [Fintype K] [DecidableEq K] [W.toAffine.IsElliptic] in
/-- The `K̄`-linear translation and its `K`-restriction induce the same point map. -/
theorem sigmaConjugation_tau_mapW (S : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (P : (W_KE (W.baseChange (AlgebraicClosure K))).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (W' := W.baseChange (AlgebraicClosure K))
        (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S).toAlgHom P =
      WeierstrassCurve.Affine.Point.map (W' := W)
          ((HasseWeil.translateAlgEquivOfPoint
              (W.baseChange (AlgebraicClosure K)) S).toAlgHom.restrictScalars K)
        P := by
  cases P <;> rfl


-- @@ L245-262 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The action induced by `σ` sends the lift of a point to the lift of its Frobenius image. -/
theorem sigmaConjugation_lift_twist (S : (W.baseChange (AlgebraicClosure K)).toAffine.Point) :
    sigmaFunctionFieldPointKbar W (HasseWeil.liftPointToKE (W.baseChange (AlgebraicClosure K)) S) =
      HasseWeil.liftPointToKE (W.baseChange (AlgebraicClosure K)) (geomFrobeniusPointFun W S) := by
  rcases S with _ | ⟨sx, sy, hns⟩
  · change sigmaFunctionFieldPointKbar W
        (HasseWeil.liftPointToKE (W.baseChange (AlgebraicClosure K)) 0) =
        HasseWeil.liftPointToKE (W.baseChange (AlgebraicClosure K)) (geomFrobeniusPointFun W 0)
    rw [geomFrobeniusPointFun_zero, map_zero, map_zero]
  · rw [geomFrobeniusPointFun_some, HasseWeil.liftPointToKE_some, HasseWeil.liftPointToKE_some,
      HasseWeil.liftSomePoint, HasseWeil.liftSomePoint]
    change WeierstrassCurve.Affine.Point.map (W' := W) (frobeniusFunctionFieldEquivK W)
        (Affine.Point.some _ _ _) = Affine.Point.some _ _ _
    rw [WeierstrassCurve.Affine.Point.map_some (W' := W) (f := frobeniusFunctionFieldEquivK W)]
    refine (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr ⟨?_, ?_⟩ <;>
      · simp only [frobeniusFunctionFieldEquivK_apply, FiniteField.coe_frobeniusAlgHom]
        rw [frobeniusFunctionFieldEquiv_algebraMap]


-- @@ L264-274 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The point map induced by `σ` fixes the generic point. -/
theorem sigmaConjugation_fix_genericPoint :
    sigmaFunctionFieldPointKbar W (HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K))) =
      HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K)) := by
  rw [HasseWeil.genericPoint_xOf_some]
  change WeierstrassCurve.Affine.Point.map (W' := W) (frobeniusFunctionFieldEquivK W)
      (Affine.Point.some _ _ _) = _
  rw [WeierstrassCurve.Affine.Point.map_some (W' := W) (f := frobeniusFunctionFieldEquivK W)]
  exact (WeierstrassCurve.Affine.Point.some.injEq _ _ _ _ _ _).mpr
    ⟨frobeniusFunctionFieldEquiv_x_gen W, frobeniusFunctionFieldEquiv_y_gen W⟩


-- @@ L276-296 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The arithmetic Frobenius conjugation identity at the generic point. -/
theorem sigmaConjugation_point (S : (W.baseChange (AlgebraicClosure K)).toAffine.Point) :
    WeierstrassCurve.Affine.Point.map (W' := W) (frobeniusFunctionFieldEquivK W)
        (WeierstrassCurve.Affine.Point.map (W' := W)
          ((HasseWeil.translateAlgEquivOfPoint
              (W.baseChange (AlgebraicClosure K)) S).toAlgHom.restrictScalars K)
          (HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K)))) =
      WeierstrassCurve.Affine.Point.map (W' := W)
        ((HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
            (geomFrobeniusPointFun W S)).toAlgHom.restrictScalars K)
        (WeierstrassCurve.Affine.Point.map (W' := W) (frobeniusFunctionFieldEquivK W)
          (HasseWeil.genericPoint (W.baseChange (AlgebraicClosure K)))) := by
  rw [← sigmaFunctionFieldPointKbar_apply, ← sigmaFunctionFieldPointKbar_apply]
  rw [sigmaConjugation_fix_genericPoint W,
    ← sigmaConjugation_tau_mapW W (geomFrobeniusPointFun W S),
    HasseWeil.translateAlgEquivOfPoint_map_genericPoint (W.baseChange (AlgebraicClosure K))
      (geomFrobeniusPointFun W S)]
  rw [← sigmaConjugation_tau_mapW W S,
    HasseWeil.translateAlgEquivOfPoint_map_genericPoint (W.baseChange (AlgebraicClosure K)) S,
    map_add, sigmaConjugation_fix_genericPoint W, sigmaConjugation_lift_twist W]


-- @@ L298-326 verbatim
/-- The translation conjugation for `σ` on `x_gen` and `y_gen`. -/
theorem sigmaConjugation_x_y_gen (S : (W.baseChange (AlgebraicClosure K)).toAffine.Point) :
    frobeniusFunctionFieldEquiv W
        (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S
          (x_gen (W.baseChange (AlgebraicClosure K)))) =
      HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
        (geomFrobeniusPointFun W S)
        (frobeniusFunctionFieldEquiv W (x_gen (W.baseChange (AlgebraicClosure K)))) ∧
    frobeniusFunctionFieldEquiv W
        (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S
          (y_gen (W.baseChange (AlgebraicClosure K)))) =
      HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
        (geomFrobeniusPointFun W S)
        (frobeniusFunctionFieldEquiv W (y_gen (W.baseChange (AlgebraicClosure K)))) := by
  have hpt := sigmaConjugation_point W S
  obtain ⟨_, e1⟩ := map_genericPoint_some W
    ((HasseWeil.translateAlgEquivOfPoint
        (W.baseChange (AlgebraicClosure K)) S).toAlgHom.restrictScalars K)
  obtain ⟨_, e2⟩ := map_genericPoint_some W (frobeniusFunctionFieldEquivK W)
  rw [e1, e2] at hpt
  rw [WeierstrassCurve.Affine.Point.map_some (W' := W) (f := frobeniusFunctionFieldEquivK W),
    WeierstrassCurve.Affine.Point.map_some (W' := W)
      (f := (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
        (geomFrobeniusPointFun W S)).toAlgHom.restrictScalars K),
    WeierstrassCurve.Affine.Point.some.injEq] at hpt
  obtain ⟨hx, hy⟩ := hpt
  simp only [AlgHom.coe_restrictScalars',
    frobeniusFunctionFieldEquivK_apply] at hx hy
  exact ⟨hx, hy⟩


-- @@ L328-337 verbatim
/-- The application form of `(σ.toRingHom.comp τ_S.toRingHom) g`. -/
theorem frob_comp_tau_apply (S : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (g : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    ((frobeniusFunctionFieldEquiv W).toRingHom.comp
        (HasseWeil.translateAlgEquivOfPoint
          (W.baseChange (AlgebraicClosure K)) S).toRingEquiv.toRingHom)
        g =
      frobeniusFunctionFieldEquiv W
        (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S g) :=
  RingHom.comp_apply _ _ g


-- @@ L339-348 verbatim
/-- The application form of `(τ_{π̄ S}.toRingHom.comp σ.toRingHom) g`. -/
theorem tau_comp_frob_apply (S : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (g : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    ((HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
          (geomFrobeniusPointFun W S)).toRingEquiv.toRingHom.comp
        (frobeniusFunctionFieldEquiv W).toRingHom)
        g =
      HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
        (geomFrobeniusPointFun W S) (frobeniusFunctionFieldEquiv W g) :=
  RingHom.comp_apply _ _ g


-- @@ L350-368 verbatim
/-- The translation conjugation for `σ`, as a ring-hom composition equality. -/
theorem frobeniusFunctionFieldEquiv_comp_translate_eq
    (S : (W.baseChange (AlgebraicClosure K)).toAffine.Point) :
    (frobeniusFunctionFieldEquiv W).toRingHom.comp
        (HasseWeil.translateAlgEquivOfPoint
          (W.baseChange (AlgebraicClosure K)) S).toRingEquiv.toRingHom
      = (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
          (geomFrobeniusPointFun W S)).toRingEquiv.toRingHom.comp
        (frobeniusFunctionFieldEquiv W).toRingHom := by
  obtain ⟨hx, hy⟩ := sigmaConjugation_x_y_gen W S
  refine ringHom_ext_base_x_y_gen (W.baseChange (AlgebraicClosure K)) _ _ (fun a ↦ ?_)
    (by
      rw [frob_comp_tau_apply, tau_comp_frob_apply]
      exact hx)
    (by
      rw [frob_comp_tau_apply, tau_comp_frob_apply]
      exact hy)
  rw [frob_comp_tau_apply, tau_comp_frob_apply]
  simp only [AlgEquiv.commutes, frobeniusFunctionFieldEquiv_algebraMap]


-- @@ L370-378 verbatim
/-- The translation conjugation for the arithmetic Frobenius `σ`, pointwise. -/
theorem frobeniusFunctionFieldEquiv_conj (S : (W.baseChange (AlgebraicClosure K)).toAffine.Point)
    (g : (W.baseChange (AlgebraicClosure K)).toAffine.FunctionField) :
    frobeniusFunctionFieldEquiv W
        (HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K)) S g) =
      HasseWeil.translateAlgEquivOfPoint (W.baseChange (AlgebraicClosure K))
        (geomFrobeniusPointFun W S) (frobeniusFunctionFieldEquiv W g) := by
  rw [← frob_comp_tau_apply, ← tau_comp_frob_apply]
  exact RingHom.congr_fun (frobeniusFunctionFieldEquiv_comp_translate_eq W S) g


-- @@ L380-380 verbatim
end BaseChange


-- @@ L382-382 verbatim
end HasseWeil.WeilPairing
