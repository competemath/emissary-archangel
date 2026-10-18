/-
Copyright (c) 2026 The tempered-fundamental-groups contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib


-- @@ L8-33 verbatim
/-!
# The generic point of an elliptic curve and its affine automorphisms

Let `W` be an elliptic curve over a field `k` with function field `F = k(W)`. This file
constructs the generic point `genericPoint W ∈ W(F)` (with coordinates the classes of `X` and
`Y`) and the group `AffAut W` of affine automorphisms `P ↦ ε • P + m` (`ε = ±1`, `m ∈ W(k)`) of
`W`, acting on `F` by pullback of functions.

For `g : AffAut W` the `k`-algebra endomorphism `pullback W g : F →ₐ[k] F` ("`f ↦ f ∘ g`") is
the unique one sending the generic point to `g(genericPoint W)`; it exists because the
`x`-coordinate of `g(genericPoint W)` is transcendental over `k`. We have
`pullback W (g * h) = (pullback W h).comp (pullback W g)`, so that `g • f := pullback W g⁻¹ f`
is a left action by `k`-algebra automorphisms.

## Main definitions

* `xOf`, `yOf`: the coordinates of a point (`0` for the point at infinity).
* `bc W L`: the base change `W(k) →+ W(L)`.
* `genericPoint W`: the generic point of `W` in `W(k(W))`.
* `liftFF`: the `k`-algebra map `k(W) → L` sending the generic point to an `L`-point with
  transcendental `x`-coordinate.
* `AffAut W`: the group of affine automorphisms `P ↦ ε • P + m`, acting on points over any
  extension by `AffAut.act`.
* `pullback W g`: the pullback of functions along `g`; the instance
  `MulSemiringAction (AffAut W) (funField W)`.
-/


-- @@ L35-35 verbatim
universe u


-- @@ L37-37 verbatim
open Polynomial WeierstrassCurve WeierstrassCurve.Affine

-- @@ L38-38 verbatim
open scoped Polynomial.Bivariate


-- @@ L40-40 verbatim
namespace TemperedFundamentalGroups.Orbicurve


-- @@ L42-42 verbatim
noncomputable section


-- @@ L44-44 verbatim
variable {k : Type u} [Field k] (W : WeierstrassCurve k)


-- @@ L46-46 verbatim
/-! ### Coordinates of points -/


-- @@ L48-48 verbatim
section Coordinates


-- @@ L50-50 verbatim
variable {L : Type*} [Field L] {V : Affine L}


-- @@ L52-55 verbatim
/-- The `x`-coordinate of a point (`0` for the point at infinity). -/
def xOf : V.Point → L
  | .zero => 0
  | .some x _ _ => x


-- @@ L57-60 verbatim
/-- The `y`-coordinate of a point (`0` for the point at infinity). -/
def yOf : V.Point → L
  | .zero => 0
  | .some _ y _ => y


-- @@ L62-62 verbatim
@[simp] lemma xOf_some {x y : L} (h : V.Nonsingular x y) : xOf (.some x y h) = x := rfl


-- @@ L64-64 verbatim
@[simp] lemma yOf_some {x y : L} (h : V.Nonsingular x y) : yOf (.some x y h) = y := rfl


-- @@ L66-69 verbatim
lemma nonsingular_xOf_yOf {P : V.Point} (hP : P ≠ 0) : V.Nonsingular (xOf P) (yOf P) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact h


-- @@ L71-72 verbatim
lemma equation_xOf_yOf {P : V.Point} (hP : P ≠ 0) : V.Equation (xOf P) (yOf P) :=
  (nonsingular_xOf_yOf hP).1


-- @@ L74-77 verbatim
lemma eq_some_xOf_yOf {P : V.Point} (hP : P ≠ 0) : P = .some _ _ (nonsingular_xOf_yOf hP) := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => rfl


-- @@ L79-82 verbatim
lemma Point.ext_xOf_yOf {P Q : V.Point} (hP : P ≠ 0) (hQ : Q ≠ 0) (hx : xOf P = xOf Q)
    (hy : yOf P = yOf Q) : P = Q := by
  rw [eq_some_xOf_yOf hP, eq_some_xOf_yOf hQ]
  simp [hx, hy]


-- @@ L84-86 verbatim
variable {K : Type*} [Field K] [DecidableEq L] [DecidableEq K] [Algebra k L] [Algebra k K]
  (φ : L →ₐ[k] K)
  {V : WeierstrassCurve k}


-- @@ L88-91 verbatim
lemma xOf_map (P : (V.toAffine⁄L).Point) : xOf (Point.map φ P) = φ (xOf P) := by
  cases P with
  | zero => exact (map_zero φ).symm
  | some x y h => rfl


-- @@ L93-96 verbatim
lemma yOf_map (P : (V.toAffine⁄L).Point) : yOf (Point.map φ P) = φ (yOf P) := by
  cases P with
  | zero => exact (map_zero φ).symm
  | some x y h => rfl


-- @@ L98-100 verbatim
lemma map_eq_zero_iff {P : (V.toAffine⁄L).Point} : Point.map φ P = 0 ↔ P = 0 := by
  rw [← (Point.map φ).map_zero]
  exact (Point.map_injective φ).eq_iff


-- @@ L102-102 verbatim
end Coordinates


-- @@ L104-104 verbatim
/-! ### Base change of rational points -/


-- @@ L106-106 verbatim
section BaseChange


-- @@ L108-108 verbatim
variable [DecidableEq k] (L : Type*) [Field L] [DecidableEq L] [Algebra k L]


-- @@ L110-112 verbatim
/-- The base change `W(k) →+ W(L)` of rational points. -/
def bc : W.toAffine.Point →+ (W.toAffine⁄L).Point :=
  Point.map (W' := W.toAffine) (Algebra.ofId k L)


-- @@ L114-114 verbatim
variable {W L}


-- @@ L116-117 verbatim
@[simp] lemma xOf_bc (P : W.toAffine.Point) : xOf (bc W L P) = algebraMap k L (xOf P) :=
  xOf_map (V := W) (Algebra.ofId k L) P


-- @@ L119-120 verbatim
@[simp] lemma yOf_bc (P : W.toAffine.Point) : yOf (bc W L P) = algebraMap k L (yOf P) :=
  yOf_map (V := W) (Algebra.ofId k L) P


-- @@ L122-123 verbatim
@[simp] lemma bc_eq_zero_iff {P : W.toAffine.Point} : bc W L P = 0 ↔ P = 0 :=
  map_eq_zero_iff (V := W) (Algebra.ofId k L)


-- @@ L125-130 verbatim
lemma map_bc {K : Type*} [Field K] [DecidableEq K] [Algebra k K] (φ : L →ₐ[k] K)
    (P : W.toAffine.Point) :
    Point.map φ (bc W L P) = bc W K P := by
  have := Point.map_map (W' := W.toAffine) (Algebra.ofId k L) φ P
  rw [Subsingleton.elim (φ.comp (Algebra.ofId k L)) (Algebra.ofId k K)] at this
  exact this


-- @@ L132-135 verbatim
omit [DecidableEq k] in
lemma map_units_smul {K : Type*} [Field K] [DecidableEq K] [Algebra k K] (φ : L →ₐ[k] K) (ε : ℤˣ)
    (P : (W.toAffine⁄L).Point) : Point.map φ (ε • P) = ε • Point.map φ P := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]


-- @@ L137-138 verbatim
lemma bc_units_smul (ε : ℤˣ) (P : W.toAffine.Point) : bc W L (ε • P) = ε • bc W L P := by
  rw [Units.smul_def, Units.smul_def, map_zsmul]


-- @@ L140-140 verbatim
end BaseChange


-- @@ L142-142 verbatim
/-! ### The generic point -/


-- @@ L144-145 verbatim
/-- The function field `k(W)` of `W`. -/
abbrev funField : Type u := W.toAffine.FunctionField


-- @@ L147-149 verbatim
/-- The `x`-coordinate of the generic point: the class of `X` in `k(W)`. -/
def xGen : funField W :=
  algebraMap W.toAffine.CoordinateRing _ (AdjoinRoot.mk W.toAffine.polynomial (C X))


-- @@ L151-153 verbatim
/-- The `y`-coordinate of the generic point: the class of `Y` in `k(W)`. -/
def yGen : funField W :=
  algebraMap W.toAffine.CoordinateRing _ (AdjoinRoot.mk W.toAffine.polynomial X)


-- @@ L155-158 verbatim
lemma algebraMap_funField (a : k) : algebraMap k (funField W) a =
    algebraMap W.toAffine.CoordinateRing _ (AdjoinRoot.mk W.toAffine.polynomial (C (C a))) := by
  rw [IsScalarTower.algebraMap_apply k W.toAffine.CoordinateRing]
  rfl


-- @@ L160-169 verbatim
lemma equation_gen : (W.toAffine⁄(funField W)).Equation (xGen W) (yGen W) := by
  have h0 : AdjoinRoot.mk W.toAffine.polynomial (Y ^ 2 + C (C W.a₁ * X + C W.a₃) * Y -
      C (X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆)) = 0 := AdjoinRoot.mk_self
  have h := congrArg (algebraMap W.toAffine.CoordinateRing (funField W)) h0
  rw [equation_iff]
  simp only [map_add, map_sub, map_mul, map_pow, map_zero] at h
  simp only [xGen, yGen, WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄,
    WeierstrassCurve.map_a₆, algebraMap_funField]
  linear_combination h


-- @@ L171-175 verbatim
variable {W} in
lemma nonsingular_of_equation [W.IsElliptic] {L : Type*} [Field L] [Algebra k L] {x y : L}
    (h : (W.toAffine⁄L).Equation x y) : (W.toAffine⁄L).Nonsingular x y := by
  haveI : (W.toAffine⁄L).IsElliptic := inferInstanceAs (W.map (algebraMap k L)).IsElliptic
  exact equation_iff_nonsingular.mp h


-- @@ L177-179 verbatim
/-- The generic point of `W`, a point of `W` over its function field. -/
def genericPoint [W.IsElliptic] : (W.toAffine⁄(funField W)).Point :=
  .some (xGen W) (yGen W) (nonsingular_of_equation (equation_gen W))


-- @@ L181-182 verbatim
@[simp] lemma genericPoint_ne_zero [W.IsElliptic] : genericPoint W ≠ 0 :=
  Point.some_ne_zero _


-- @@ L184-184 verbatim
@[simp] lemma xOf_genericPoint [W.IsElliptic] : xOf (genericPoint W) = xGen W := rfl


-- @@ L186-186 verbatim
@[simp] lemma yOf_genericPoint [W.IsElliptic] : yOf (genericPoint W) = yGen W := rfl


-- @@ L188-194 verbatim
lemma aeval_xGen (p : k[X]) : aeval (xGen W) p =
    algebraMap W.toAffine.CoordinateRing (funField W)
      (AdjoinRoot.mk W.toAffine.polynomial (C p)) := by
  rw [xGen, ← IsScalarTower.coe_toAlgHom' k, Polynomial.aeval_algHom_apply]
  congr 1
  rw [AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq, aeval_algebraMap_apply, aeval_X_left_apply,
    AdjoinRoot.algebraMap_eq, AdjoinRoot.mk_C]


-- @@ L196-203 verbatim
lemma transcendental_xGen : Transcendental k (xGen W) := by
  rw [transcendental_iff_injective]
  intro p q h
  simp only [aeval_xGen] at h
  have := IsFractionRing.injective W.toAffine.CoordinateRing (funField W) h
  rw [AdjoinRoot.mk_C, AdjoinRoot.mk_C] at this
  exact AdjoinRoot.of.injective_of_degree_ne_zero
    (by rw [W.toAffine.degree_polynomial]; decide) this


-- @@ L205-205 verbatim
/-! ### Maps out of the function field -/


-- @@ L207-207 verbatim
section Eval


-- @@ L209-209 verbatim
variable {L : Type*} [CommRing L] [Algebra k L]


-- @@ L211-219 verbatim
/-- The evaluation `k[W] →ₐ[k] L` at a solution `(x, y)` of the Weierstrass equation. -/
def evalHom (x y : L) (h : (W.toAffine⁄L).Equation x y) :
    W.toAffine.CoordinateRing →ₐ[k] L :=
  AdjoinRoot.liftAlgHom _ (Polynomial.aeval x) y (by
    rw [equation_iff] at h
    simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
      WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at h
    simp [WeierstrassCurve.Affine.polynomial, eval₂_add, eval₂_pow]
    linear_combination h)


-- @@ L221-221 verbatim
variable {W}


-- @@ L223-225 verbatim
lemma evalHom_of (x y : L) (h : (W.toAffine⁄L).Equation x y) (p : k[X]) :
    evalHom W x y h (AdjoinRoot.of _ p) = aeval x p := by
  simp [evalHom]


-- @@ L227-229 verbatim
lemma evalHom_x (x y : L) (h : (W.toAffine⁄L).Equation x y) :
    evalHom W x y h (AdjoinRoot.mk W.toAffine.polynomial (C X)) = x := by
  rw [AdjoinRoot.mk_C, evalHom_of, aeval_X]


-- @@ L231-233 verbatim
lemma evalHom_y (x y : L) (h : (W.toAffine⁄L).Equation x y) :
    evalHom W x y h (AdjoinRoot.mk W.toAffine.polynomial X) = y := by
  simp [evalHom]


-- @@ L235-235 verbatim
end Eval


-- @@ L237-237 verbatim
section Lift


-- @@ L239-239 verbatim
variable {L : Type*} [Field L] [Algebra k L] {W}


-- @@ L241-242 verbatim
instance : Module.Finite k[X] W.toAffine.CoordinateRing :=
  Module.Finite.of_basis (CoordinateRing.basis W.toAffine)


-- @@ L244-252 verbatim
lemma injective_evalHom (x y : L) (h : (W.toAffine⁄L).Equation x y) (hx : Transcendental k x) :
    Function.Injective (evalHom W x y h) := by
  have hker : RingHom.ker (evalHom W x y h) = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := k[X])
    refine eq_bot_iff.mpr fun p hp => ?_
    rw [Ideal.mem_comap, RingHom.mem_ker, AdjoinRoot.algebraMap_eq, evalHom_of] at hp
    by_contra hp0
    exact hx ⟨p, hp0, hp⟩
  exact (RingHom.injective_iff_ker_eq_bot _).mpr hker


-- @@ L254-258 verbatim
/-- The `k`-algebra map `k(W) → L` sending the generic point to the `L`-point `(x, y)`, for `x`
transcendental over `k`. -/
def liftFF (x y : L) (h : (W.toAffine⁄L).Equation x y) (hx : Transcendental k x) :
    funField W →ₐ[k] L :=
  IsFractionRing.liftAlgHom (injective_evalHom x y h hx)


-- @@ L260-263 verbatim
@[simp] lemma liftFF_xGen (x y : L) (h : (W.toAffine⁄L).Equation x y) (hx : Transcendental k x) :
    liftFF x y h hx (xGen W) = x := by
  rw [liftFF, IsFractionRing.liftAlgHom_apply, xGen, IsFractionRing.lift_algebraMap]
  exact evalHom_x x y h


-- @@ L265-268 verbatim
@[simp] lemma liftFF_yGen (x y : L) (h : (W.toAffine⁄L).Equation x y) (hx : Transcendental k x) :
    liftFF x y h hx (yGen W) = y := by
  rw [liftFF, IsFractionRing.liftAlgHom_apply, yGen, IsFractionRing.lift_algebraMap]
  exact evalHom_y x y h


-- @@ L270-284 verbatim
/-- A `k`-algebra map out of `k(W)` is determined by the images of the coordinates of the generic
point. -/
lemma algHom_ext_funField {φ ψ : funField W →ₐ[k] L} (hx : φ (xGen W) = ψ (xGen W))
    (hy : φ (yGen W) = ψ (yGen W)) : φ = ψ := by
  have hc : φ.comp (IsScalarTower.toAlgHom k W.toAffine.CoordinateRing (funField W)) =
      ψ.comp (IsScalarTower.toAlgHom k W.toAffine.CoordinateRing (funField W)) := by
    apply AdjoinRoot.algHom_ext'
    · apply Polynomial.algHom_ext
      change φ (algebraMap _ _ (AdjoinRoot.of _ X)) = ψ (algebraMap _ _ (AdjoinRoot.of _ X))
      rw [← AdjoinRoot.mk_C]
      exact hx
    · exact hy
  apply AlgHom.coe_ringHom_injective
  exact IsFractionRing.ringHom_ext (A := W.toAffine.CoordinateRing)
    fun c => DFunLike.congr_fun hc c


-- @@ L286-286 verbatim
variable [DecidableEq L] [W.IsElliptic]


-- @@ L288-289 verbatim
lemma xOf_map_genericPoint (φ : funField W →ₐ[k] L) :
    xOf (Point.map φ (genericPoint W)) = φ (xGen W) := xOf_map φ _


-- @@ L291-292 verbatim
lemma yOf_map_genericPoint (φ : funField W →ₐ[k] L) :
    yOf (Point.map φ (genericPoint W)) = φ (yGen W) := yOf_map φ _


-- @@ L294-299 verbatim
/-- A `k`-algebra map out of `k(W)` is determined by the image of the generic point. -/
lemma algHom_ext_of_map_genericPoint {φ ψ : funField W →ₐ[k] L}
    (h : Point.map φ (genericPoint W) = Point.map ψ (genericPoint W)) : φ = ψ := by
  apply algHom_ext_funField
  · rw [← xOf_map_genericPoint, h, xOf_map_genericPoint]
  · rw [← yOf_map_genericPoint, h, yOf_map_genericPoint]


-- @@ L301-307 verbatim
lemma map_liftFF_genericPoint {P : (W.toAffine⁄L).Point} (hP : P ≠ 0)
    (hx : Transcendental k (xOf P)) :
    Point.map (liftFF (xOf P) (yOf P) (equation_xOf_yOf hP) hx) (genericPoint W) = P := by
  refine Point.ext_xOf_yOf ?_ hP ?_ ?_
  · exact fun h => genericPoint_ne_zero W ((map_eq_zero_iff _).mp h)
  · rw [xOf_map_genericPoint, liftFF_xGen]
  · rw [yOf_map_genericPoint, liftFF_yGen]


-- @@ L309-309 verbatim
end Lift


-- @@ L311-311 verbatim
/-! ### Affine automorphisms -/


-- @@ L313-313 verbatim
variable [DecidableEq k]


-- @@ L315-321 verbatim
/-- The affine automorphism `P ↦ ε • P + m` of `W`, for `ε = ±1` and `m ∈ W(k)`. -/
@[ext]
structure AffAut : Type u where
  /-- The linear part `ε = ±1`. -/
  ε : ℤˣ
  /-- The translation part `m ∈ W(k)`. -/
  m : W.toAffine.Point


-- @@ L323-323 verbatim
namespace AffAut


-- @@ L325-325 verbatim
variable {W}


-- @@ L327-346 verbatim
instance : Group (AffAut W) where
  mul g h := ⟨g.ε * h.ε, g.ε • h.m + g.m⟩
  one := ⟨1, 0⟩
  inv g := ⟨g.ε⁻¹, -(g.ε⁻¹ • g.m)⟩
  mul_assoc g h l := by
    refine AffAut.ext (mul_assoc g.ε h.ε l.ε) ?_
    change (g.ε * h.ε) • l.m + (g.ε • h.m + g.m) = g.ε • (h.ε • l.m + h.m) + g.m
    rw [smul_add, mul_smul, add_assoc]
  one_mul g := by
    refine AffAut.ext (one_mul g.ε) ?_
    change (1 : ℤˣ) • g.m + 0 = g.m
    rw [one_smul, add_zero]
  mul_one g := by
    refine AffAut.ext (mul_one g.ε) ?_
    change g.ε • (0 : W.toAffine.Point) + g.m = g.m
    rw [smul_zero, zero_add]
  inv_mul_cancel g := by
    refine AffAut.ext (inv_mul_cancel g.ε) ?_
    change g.ε⁻¹ • g.m + -(g.ε⁻¹ • g.m) = 0
    rw [add_neg_cancel]


-- @@ L348-348 verbatim
@[simp] lemma mul_ε (g h : AffAut W) : (g * h).ε = g.ε * h.ε := rfl

-- @@ L349-349 verbatim
@[simp] lemma mul_m (g h : AffAut W) : (g * h).m = g.ε • h.m + g.m := rfl

-- @@ L350-350 verbatim
@[simp] lemma one_ε : (1 : AffAut W).ε = 1 := rfl

-- @@ L351-351 verbatim
@[simp] lemma one_m : (1 : AffAut W).m = 0 := rfl

-- @@ L352-352 verbatim
@[simp] lemma inv_ε (g : AffAut W) : g⁻¹.ε = g.ε⁻¹ := rfl

-- @@ L353-353 verbatim
@[simp] lemma inv_m (g : AffAut W) : g⁻¹.m = -(g.ε⁻¹ • g.m) := rfl


-- @@ L355-359 verbatim
/-- The action of an affine automorphism on the `L`-points: `P ↦ ε • P + m`. -/
def act (L : Type*) [Field L] [DecidableEq L] [Algebra k L] (g : AffAut W)
    (P : (W.toAffine⁄L).Point) :
    (W.toAffine⁄L).Point :=
  g.ε • P + bc W L g.m


-- @@ L361-361 verbatim
variable (L : Type*) [Field L] [DecidableEq L] [Algebra k L]


-- @@ L363-364 verbatim
lemma act_def (g : AffAut W) (P : (W.toAffine⁄L).Point) : g.act L P = g.ε • P + bc W L g.m :=
  rfl


-- @@ L366-368 verbatim
lemma act_mul (g h : AffAut W) (P : (W.toAffine⁄L).Point) :
    (g * h).act L P = g.act L (h.act L P) := by
  simp only [act_def, mul_ε, mul_m, map_add, bc_units_smul, smul_add, mul_smul, add_assoc]


-- @@ L370-371 verbatim
lemma act_one (P : (W.toAffine⁄L).Point) : (1 : AffAut W).act L P = P := by
  simp [act_def]


-- @@ L373-374 verbatim
lemma act_inv_act (g : AffAut W) (P : (W.toAffine⁄L).Point) : g⁻¹.act L (g.act L P) = P := by
  rw [← act_mul, inv_mul_cancel, act_one]


-- @@ L376-379 verbatim
variable {L} in
lemma map_act {K : Type*} [Field K] [DecidableEq K] [Algebra k K] (φ : L →ₐ[k] K) (g : AffAut W)
    (P : (W.toAffine⁄L).Point) : Point.map φ (g.act L P) = g.act K (Point.map φ P) := by
  rw [act_def, act_def, map_add, map_units_smul, map_bc]


-- @@ L381-389 verbatim
/-- The action of affine automorphisms on the rational points. -/
instance : MulAction (AffAut W) W.toAffine.Point where
  smul g P := g.ε • P + g.m
  one_smul P := by
    change (1 : ℤˣ) • P + 0 = P
    rw [one_smul, add_zero]
  mul_smul g h P := by
    change (g.ε * h.ε) • P + (g.ε • h.m + g.m) = g.ε • (h.ε • P + h.m) + g.m
    rw [smul_add, mul_smul, add_assoc]


-- @@ L391-391 verbatim
lemma smul_def (g : AffAut W) (P : W.toAffine.Point) : g • P = g.ε • P + g.m := rfl


-- @@ L393-394 verbatim
lemma bc_smul (g : AffAut W) (P : W.toAffine.Point) : bc W L (g • P) = g.act L (bc W L P) := by
  rw [smul_def, act_def, map_add, bc_units_smul]


-- @@ L396-396 verbatim
end AffAut


-- @@ L398-398 verbatim
/-! ### Pullback of functions -/


-- @@ L400-400 verbatim
section Pullback


-- @@ L402-402 verbatim
variable [W.IsElliptic]


-- @@ L404-405 verbatim
/-- The algebraic closure of `k` in `k(W)`. -/
local notation "K₀" => algebraicClosure k (funField W)


-- @@ L407-434 verbatim
omit [DecidableEq k] [W.IsElliptic] in
lemma mem_range_of_isAlgebraic {Q : (W.toAffine⁄(funField W)).Point}
    (hQ : Q ≠ 0 → IsAlgebraic k (xOf Q)) : Q ∈ Set.range (Point.map (K₀).val) := by
  by_cases hQ0 : Q = 0
  · exact ⟨0, by rw [hQ0, map_zero]⟩
  have hx : xOf Q ∈ K₀ := mem_algebraicClosure_iff.mpr (hQ hQ0)
  set x : K₀ := ⟨xOf Q, hx⟩
  have hns := nonsingular_xOf_yOf hQ0
  have hy : IsAlgebraic k (yOf Q) := by
    obtain ⟨b, hb⟩ : ∃ b : K₀, b = algebraMap k K₀ W.a₁ * x + algebraMap k K₀ W.a₃ := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : K₀, c = x ^ 3 + algebraMap k K₀ W.a₂ * x ^ 2 +
      algebraMap k K₀ W.a₄ * x + algebraMap k K₀ W.a₆ := ⟨_, rfl⟩
    let p : (K₀)[X] := X ^ 2 + C b * X - C c
    have hp : p ≠ 0 := fun h => by simpa [p] using congrArg (coeff · 2) h
    have hpy : aeval (yOf Q) p = 0 := by
      have := (equation_iff _ _).mp hns.1
      simp only [WeierstrassCurve.baseChange, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
        WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆] at this
      simp only [p, hb, hc, map_sub, map_add, map_mul, map_pow, aeval_X, aeval_C,
        IntermediateField.algebraMap_apply, IntermediateField.coe_algebraMap_apply, x]
      linear_combination this
    exact IsAlgebraic.restrictScalars k ⟨p, hp, hpy⟩
  set y : K₀ := ⟨yOf Q, mem_algebraicClosure_iff.mpr hy⟩
  have hns' : (W.toAffine⁄K₀).Nonsingular x y :=
    (W.toAffine.baseChange_nonsingular (f := (K₀).val) Subtype.val_injective x y).mp hns
  refine ⟨.some x y hns', Point.ext_xOf_yOf ?_ hQ0 rfl rfl⟩
  rw [Ne, map_eq_zero_iff]
  exact Point.some_ne_zero _


-- @@ L436-444 verbatim
omit [DecidableEq k] in
lemma genericPoint_notMem_range : genericPoint W ∉ Set.range (Point.map (K₀).val) := by
  rintro ⟨Q, hQ⟩
  have hx : xGen W = (K₀).val (xOf Q) := by
    rw [← xOf_genericPoint, ← hQ]
    exact xOf_map _ Q
  apply transcendental_xGen W
  rw [hx]
  exact mem_algebraicClosure_iff.mp (xOf Q).2


-- @@ L446-455 verbatim
lemma act_genericPoint_ne_zero_and (g : AffAut W) :
    g.act _ (genericPoint W) ≠ 0 ∧ Transcendental k (xOf (g.act _ (genericPoint W))) := by
  by_contra h
  rw [not_and_or, not_not, Transcendental, not_not] at h
  have hmem := mem_range_of_isAlgebraic W (Q := g.act _ (genericPoint W))
    fun h0 => h.resolve_left h0
  obtain ⟨Q, hQ⟩ := hmem
  apply genericPoint_notMem_range W
  refine ⟨g⁻¹.act _ Q, ?_⟩
  rw [AffAut.map_act, hQ, AffAut.act_inv_act]


-- @@ L457-458 verbatim
lemma act_genericPoint_ne_zero (g : AffAut W) : g.act _ (genericPoint W) ≠ 0 :=
  (act_genericPoint_ne_zero_and W g).1


-- @@ L460-462 verbatim
lemma transcendental_xOf_act (g : AffAut W) :
    Transcendental k (xOf (g.act _ (genericPoint W))) :=
  (act_genericPoint_ne_zero_and W g).2


-- @@ L464-467 verbatim
/-- The pullback of functions along an affine automorphism `g`: the `k`-algebra endomorphism
`f ↦ f ∘ g` of `k(W)`, characterized by sending the generic point to `g(genericPoint W)`. -/
def pullback (g : AffAut W) : funField W →ₐ[k] funField W :=
  liftFF _ _ (equation_xOf_yOf (act_genericPoint_ne_zero W g)) (transcendental_xOf_act W g)


-- @@ L469-471 verbatim
lemma map_pullback_genericPoint (g : AffAut W) :
    Point.map (pullback W g) (genericPoint W) = g.act _ (genericPoint W) :=
  map_liftFF_genericPoint (act_genericPoint_ne_zero W g) _


-- @@ L473-474 verbatim
lemma pullback_xGen (g : AffAut W) : pullback W g (xGen W) = xOf (g.act _ (genericPoint W)) :=
  liftFF_xGen _ _ _ _


-- @@ L476-477 verbatim
lemma pullback_yGen (g : AffAut W) : pullback W g (yGen W) = yOf (g.act _ (genericPoint W)) :=
  liftFF_yGen _ _ _ _


-- @@ L479-481 verbatim
lemma eq_pullback_of (g : AffAut W) {φ : funField W →ₐ[k] funField W}
    (h : Point.map φ (genericPoint W) = g.act _ (genericPoint W)) : φ = pullback W g :=
  algHom_ext_of_map_genericPoint (by rw [h, map_pullback_genericPoint])


-- @@ L483-488 verbatim
lemma pullback_mul (g h : AffAut W) :
    pullback W (g * h) = (pullback W h).comp (pullback W g) := by
  symm
  apply eq_pullback_of
  rw [← Point.map_map, map_pullback_genericPoint, AffAut.map_act, map_pullback_genericPoint,
    AffAut.act_mul]


-- @@ L490-494 verbatim
lemma pullback_one : pullback W 1 = AlgHom.id k (funField W) := by
  symm
  apply eq_pullback_of
  rw [AffAut.act_one]
  rfl


-- @@ L496-500 verbatim
/-- The pullback along `g` as a `k`-algebra automorphism of `k(W)`. -/
def pullbackEquiv (g : AffAut W) : funField W ≃ₐ[k] funField W :=
  AlgEquiv.ofAlgHom (pullback W g) (pullback W g⁻¹)
    (by rw [← pullback_mul, inv_mul_cancel, pullback_one])
    (by rw [← pullback_mul, mul_inv_cancel, pullback_one])


-- @@ L502-503 verbatim
@[simp] lemma pullbackEquiv_apply (g : AffAut W) (f : funField W) :
    pullbackEquiv W g f = pullback W g f := rfl


-- @@ L505-519 verbatim
/-- The left action of affine automorphisms on the function field: `g • f = f ∘ g⁻¹`. -/
instance : MulSemiringAction (AffAut W) (funField W) where
  smul g f := pullback W g⁻¹ f
  one_smul f := by
    change pullback W 1⁻¹ f = f
    rw [inv_one, pullback_one]
    rfl
  mul_smul g h f := by
    change pullback W (g * h)⁻¹ f = pullback W g⁻¹ (pullback W h⁻¹ f)
    rw [mul_inv_rev, pullback_mul]
    rfl
  smul_zero g := map_zero (pullback W g⁻¹)
  smul_add g := map_add (pullback W g⁻¹)
  smul_one g := map_one (pullback W g⁻¹)
  smul_mul g := map_mul (pullback W g⁻¹)


-- @@ L521-521 verbatim
lemma smul_funField_def (g : AffAut W) (f : funField W) : g • f = pullback W g⁻¹ f := rfl


-- @@ L523-524 verbatim
instance : SMulCommClass (AffAut W) k (funField W) :=
  ⟨fun g c f => by simp only [smul_funField_def, map_smul]⟩


-- @@ L526-526 verbatim
end Pullback


-- @@ L528-528 verbatim
end


-- @@ L530-530 verbatim
end TemperedFundamentalGroups.Orbicurve
