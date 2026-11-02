import HodgePilot.ProjectiveLine


-- @@ L3-76 verbatim
/-! # The projective line: chart units and the nonvanishing of the
# point-divisor class

Golden-path wave 2.  This module proves, for the projective line
`p1 = Proj ℂ[X₀, X₁]` of `HodgePilot.ProjectiveLine`:

**Part 1 — the chart isomorphism (G1e).**  The chart ring of the standard
chart is a polynomial ring: `Away 𝒜 X₀ ≃ₐ[ℂ] ℂ[t]`
(`awayXZeroPolyEquiv`, from the generic `chartPolyEquiv` at either
chart), as an isomorphism of `ℂ`-algebras.  The `ℂ`-algebra structures
involved are all induced by the single grade-zero constants map
`ℂ → 𝒜 0 → Away 𝒜 f` (`instAlgebraAwayC`, with the scalar-tower receipt
`instIsScalarTowerAwayC`), so that there is exactly ONE `ℂ`-structure in
play at every constants comparison below; the two charts' constants are
proved to agree in the function field (`germK_awaySection_algebraMap`),
through the overlap chart, rather than assumed.

**Part 2 — the nonvanishing theorem (G2d).**  `dinfClass_ne_zero`:
the class `dinfClass` of the point-divisor datum `dinf` is
**a nonzero class in `H^1(X, O^*)` in the sense of Mathlib's `Sheaf.H`**.
The route is valuation-free: by the shipped exactness
`CartierClass.cdivClass_eq_zero_iff`, nonvanishing reduces to
non-principality; a hypothesized `divOf f = dinf` is restricted to the
two charts, where the pin's section-level left-exactness
(`TopCat.Sheaf.sections_exact_of_left_exact`) extracts unit factors;
units of the chart rings are constants (Part 1 +
`MvPolynomial.isUnit_iff_eq_C_of_isReduced`); comparing the two chart
factorizations in the function field forces the coordinate function to
be a constant, which is refuted through an injective ring map from the
polynomial ring (`totalDegree`).  No cohomology group is computed
anywhere.

**Part 3 — the falsifier suite.**  Shipped alongside the theorem so that
a wrong proof would be caught: the negative control
`cdivClass_divOf_zElt` (the SAME coordinate function's divisor class IS
zero — a proof scheme that secretly proved "everything is nonzero" would
collide with it); the corollaries `dinf_ne_divOf`,
`dinf_notMem_range_divOf`, `dinfClass_notMem_zero`; the `rfl`-receipts
`dinf_receipt`/`dinfClass_receipt` pinning the theorem's subject to the
literal Mayer–Vietoris glue datum of wave 1 (guarding statement drift);
and the kernel audit.

**Part 4 — the affine-site transport.**  Along the shipped
`CycCarrier.unitsHSiteEquiv`/`cdivClass_siteMove`, the nonvanishing
moves to the small affine Zariski site (the home of the first Chern
class map): `dinfClassAffine_ne_zero`, `cdivClassAffine_dinfAffine_ne_zero`.

## Claim discipline

The nonvanishing proved here is exactly: **a nonzero class in
`H^1(X, O^*)` in the sense of Mathlib's `Sheaf.H`**, for `X = p1`.
`H^1(X, O^*)` is *classically* the Picard group; **no Picard group is
constructed and no such identification is claimed**.  No degree
homomorphism is constructed, no comparison with any other cohomology
theory (or any other presentation of `H^1`) is stated, implied, or
approached, and no Weil divisor, order of vanishing, or valuation
appears anywhere.  The chart isomorphism is an exhibited isomorphism of
`ℂ`-algebras onto `MvPolynomial (Fin 1) ℂ`; no smoothness statement of
any kind is made in this module.  Nothing here makes the Hodge
conjecture statable.

## Credits

`Proj`, its chart API (`awayToSection`, `basicOpenIsoAway`, `awayMap`
naturality) are Andrew Yang's Mathlib infrastructure; homogeneous
localizations and their grade-zero algebra structure are Jujian Zhang's
and Eric Wieser's, with the `Away` generation theorem
(`adjoin_mk_prod_pow_eq_top`) from the 2025 Proj cluster; section-level
left-exactness of sheaf short exact sequences is Brian Nugent's
Mathlib file; `Sheaf.H` and its `Ext` infrastructure are Joël Riou's.
The Cartier machinery consumed here is `HodgePilot.CartierClass` and
`HodgePilot.CycCarrier`; the object and its divisor datum are
`HodgePilot.ProjectiveLine` (wave 1).
-/


-- @@ L78-78 verbatim
set_option maxHeartbeats 1000000

-- @@ L79-79 verbatim
set_option synthInstance.maxHeartbeats 1000000


-- @@ L81-81 verbatim
noncomputable section


-- @@ L83-83 verbatim
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

-- @@ L84-84 verbatim
open AlgebraicGeometry HomogeneousLocalization


-- @@ L86-86 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L88-88 verbatim
namespace HodgePilot


-- @@ L90-90 verbatim
namespace ProjectiveLineUnits


-- @@ L92-92 verbatim
open HodgePilot.DLog HodgePilot.CartierClass HodgePilot.CycCarrier

-- @@ L93-93 verbatim
open HodgePilot.ProjectiveLine


-- @@ L95-96 verbatim
/-- The standard grading of `ℂ[X₀, X₁]` by total degree. -/
local notation "𝒜₂" => MvPolynomial.homogeneousSubmodule (Fin 2) ℂ


-- @@ L98-98 verbatim
/-! ## Part 1(a). The single `ℂ`-structure on the chart rings -/


-- @@ L100-103 verbatim
/-- The variables are homogeneous of degree 1. -/
theorem X_mem_grade_one (i : Fin 2) :
    (MvPolynomial.X i : MvPolynomial (Fin 2) ℂ) ∈ 𝒜₂ 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X ℂ i)


-- @@ L105-128 verbatim
/-- **The single `ℂ`-algebra structure on the chart rings**: every chart
ring `(ℂ[X₀,X₁]_f)₀` is a `ℂ`-algebra through the one grade-zero
constants map `ℂ → 𝒜 0 → Away 𝒜 f` (single-`ℂ`-structure discipline:
all constants comparisons below happen at this one structure).  The
`smul` field is the already-registered `HomogeneousLocalization` scalar
action, so no second `SMul ℂ` instance is created. -/
instance instAlgebraAwayC (f : MvPolynomial (Fin 2) ℂ) :
    Algebra ℂ (Away 𝒜₂ f) where
  toSMul := inferInstance
  algebraMap := (fromZeroRingHom 𝒜₂ (Submonoid.powers f)).comp (algebraMap ℂ (𝒜₂ 0))
  commutes' _ _ := mul_comm _ _
  smul_def' c x := by
    apply HomogeneousLocalization.val_injective
    obtain ⟨y, rfl⟩ := HomogeneousLocalization.mk_surjective x
    rw [HomogeneousLocalization.val_smul, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_mk]
    show c • Localization.mk _ _ =
      (HomogeneousLocalization.mk ⟨0, algebraMap ℂ (𝒜₂ 0) c, 1, one_mem _⟩).val * _
    rw [HomogeneousLocalization.val_mk, Localization.smul_mk, Localization.mk_mul,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    use 1
    simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul,
      SetLike.GradeZero.coe_one, SetLike.GradeZero.coe_algebraMap,
      MvPolynomial.algebraMap_eq, MvPolynomial.smul_eq_C_mul]


-- @@ L130-153 verbatim
/-- Single-`ℂ`-structure receipt: the `ℂ`-structure of `instAlgebraAwayC`
is the restriction of the grade-zero structure (a scalar tower at the
ambient actions). -/
instance instIsScalarTowerAwayC (f : MvPolynomial (Fin 2) ℂ) :
    IsScalarTower ℂ (𝒜₂ 0) (Away 𝒜₂ f) where
  smul_assoc c r x := by
    apply HomogeneousLocalization.val_injective
    obtain ⟨y, rfl⟩ := HomogeneousLocalization.mk_surjective x
    show ((fromZeroRingHom 𝒜₂ (Submonoid.powers f) (c • r)) *
        HomogeneousLocalization.mk y).val =
      (c • (fromZeroRingHom 𝒜₂ (Submonoid.powers f) r *
        HomogeneousLocalization.mk y)).val
    rw [HomogeneousLocalization.val_smul, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_mul, HomogeneousLocalization.val_mk]
    show (HomogeneousLocalization.mk ⟨0, c • r, 1, one_mem _⟩).val * _ =
      c • ((HomogeneousLocalization.mk ⟨0, r, 1, one_mem _⟩).val * _)
    rw [HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk,
      Localization.mk_mul, Localization.mk_mul, Localization.smul_mk,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    use 1
    simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul,
      SetLike.GradeZero.coe_one, Submodule.coe_smul,
      MvPolynomial.smul_eq_C_mul]
    ring


-- @@ L155-159 verbatim
/-- Receipt: the constants map of `instAlgebraAwayC`, explicitly. -/
theorem algebraMap_away_apply (f : MvPolynomial (Fin 2) ℂ) (c : ℂ) :
    algebraMap ℂ (Away 𝒜₂ f) c =
      fromZeroRingHom 𝒜₂ (Submonoid.powers f) (algebraMap ℂ (𝒜₂ 0) c) :=
  rfl


-- @@ L161-161 verbatim
/-! ## Part 1(b). The coordinate fraction and the evaluation maps -/


-- @@ L163-166 verbatim
/-- The coordinate fraction `Xⱼ/Xᵢ` on the chart `D₊(Xᵢ)`. -/
def coordFrac (i j : Fin 2) : Away 𝒜₂ (MvPolynomial.X i) :=
  HomogeneousLocalization.Away.mk 𝒜₂ (X_mem_grade_one i) 1 (MvPolynomial.X j)
    ((one_smul ℕ 1).symm ▸ X_mem_grade_one j)


-- @@ L168-173 verbatim
theorem coordFrac_val (i j : Fin 2) :
    (coordFrac i j).val =
      Localization.mk (MvPolynomial.X j)
        (⟨MvPolynomial.X i ^ 1, 1, rfl⟩ :
          Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 2) ℂ)) :=
  HomogeneousLocalization.Away.val_mk _ _ _ _ _


-- @@ L175-179 verbatim
/-- The `ℂ`-algebra map `ℂ[t] → (ℂ[X₀,X₁]_{Xᵢ})₀` sending the variable to
the coordinate fraction `Xⱼ/Xᵢ`. -/
def chartPolyHom (i j : Fin 2) :
    MvPolynomial (Fin 1) ℂ →ₐ[ℂ] Away 𝒜₂ (MvPolynomial.X i) :=
  MvPolynomial.aeval (fun _ => coordFrac i j)


-- @@ L181-183 verbatim
theorem chartPolyHom_X (i j : Fin 2) (k : Fin 1) :
    chartPolyHom i j (MvPolynomial.X k) = coordFrac i j :=
  MvPolynomial.aeval_X _ k


-- @@ L185-188 verbatim
theorem chartPolyHom_C (i j : Fin 2) (c : ℂ) :
    chartPolyHom i j (MvPolynomial.C c) =
      algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X i)) c :=
  MvPolynomial.aeval_C _ c


-- @@ L190-193 verbatim
/-- The evaluation point of the chart `D₊(Xᵢ)` with coordinate value
`lam`: `Xᵢ ↦ 1`, the other variable `↦ lam`. -/
def chartEvalPt (i : Fin 2) (lam : ℂ) : Fin 2 → ℂ :=
  fun k => if k = i then 1 else lam


-- @@ L195-196 verbatim
theorem chartEvalPt_self (i : Fin 2) (lam : ℂ) : chartEvalPt i lam i = 1 :=
  if_pos rfl


-- @@ L198-200 verbatim
theorem chartEvalPt_other {i j : Fin 2} (hij : j ≠ i) (lam : ℂ) :
    chartEvalPt i lam j = lam :=
  if_neg hij


-- @@ L202-205 verbatim
theorem chartEvalPt_isUnit (i : Fin 2) (lam : ℂ) :
    IsUnit (MvPolynomial.eval (chartEvalPt i lam) (MvPolynomial.X i)) := by
  rw [MvPolynomial.eval_X, chartEvalPt_self]
  exact isUnit_one


-- @@ L207-213 verbatim
/-- Evaluation of the chart ring at the point of the chart with
coordinate `lam` (through the underlying localization). -/
def chartEval (i : Fin 2) (lam : ℂ) : Away 𝒜₂ (MvPolynomial.X i) →+* ℂ :=
  (Localization.awayLift (MvPolynomial.eval (chartEvalPt i lam)) (MvPolynomial.X i)
    (chartEvalPt_isUnit i lam)).comp
    (algebraMap (Away 𝒜₂ (MvPolynomial.X i))
      (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin 2) ℂ)))


-- @@ L215-226 verbatim
theorem chartEval_algebraMap (i : Fin 2) (lam c : ℂ) :
    chartEval i lam (algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X i)) c) = c := by
  have hval : (algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X i)) c).val =
      algebraMap (MvPolynomial (Fin 2) ℂ)
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin 2) ℂ))
        (MvPolynomial.C c) := by
    rw [algebraMap_away_apply]
    show Localization.mk _ 1 = _
    rw [Localization.mk_one_eq_algebraMap, SetLike.GradeZero.coe_algebraMap,
      MvPolynomial.algebraMap_eq]
  rw [chartEval, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, hval,
    IsLocalization.Away.lift_eq, MvPolynomial.eval_C]


-- @@ L228-233 verbatim
theorem chartEval_coordFrac {i j : Fin 2} (hij : j ≠ i) (lam : ℂ) :
    chartEval i lam (coordFrac i j) = lam := by
  rw [chartEval, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    coordFrac_val,
    Localization.awayLift_mk (hv := by rw [MvPolynomial.eval_X, chartEvalPt_self, one_mul]),
    MvPolynomial.eval_X, chartEvalPt_other hij, one_pow, mul_one]


-- @@ L235-235 verbatim
/-! ## Part 1(c). Injectivity (by evaluation at the `ℂ`-points of the chart) -/


-- @@ L237-264 verbatim
theorem chartPolyHom_injective {i j : Fin 2} (hij : j ≠ i) :
    Function.Injective (chartPolyHom i j) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have key : ∀ lam : ℂ, MvPolynomial.eval (fun _ => lam) p = 0 := by
    intro lam
    have hcomp : (chartEval i lam).comp (chartPolyHom i j).toRingHom =
        MvPolynomial.eval (fun _ : Fin 1 => lam) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        rw [RingHom.comp_apply]
        show chartEval i lam (chartPolyHom i j (MvPolynomial.C c)) = _
        rw [chartPolyHom_C, chartEval_algebraMap, MvPolynomial.eval_C]
      · intro k
        rw [RingHom.comp_apply]
        show chartEval i lam (chartPolyHom i j (MvPolynomial.X k)) = _
        rw [chartPolyHom_X, chartEval_coordFrac hij, MvPolynomial.eval_X]
    have := DFunLike.congr_fun hcomp p
    rw [RingHom.comp_apply] at this
    show MvPolynomial.eval (fun _ : Fin 1 => lam) p = 0
    rw [← this]
    show chartEval i lam (chartPolyHom i j p) = 0
    rw [hp, map_zero]
  apply MvPolynomial.funext (R := ℂ)
  intro x
  have hx : x = fun _ => x 0 := funext fun k => by rw [Subsingleton.elim k 0]
  rw [map_zero, hx]
  exact key (x 0)


-- @@ L266-266 verbatim
/-! ## Part 1(d). Surjectivity (the `Away` generation theorem of the pin) -/


-- @@ L268-282 verbatim
/-- `ℂ[X₀, X₁]` is generated over its degree-zero part by the variables. -/
theorem adjoin_range_X_eq_top :
    Algebra.adjoin (𝒜₂ 0)
      (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℂ)) = ⊤ := by
  rw [eq_top_iff]
  intro a _
  have ha : a ∈ Algebra.adjoin ℂ
      (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℂ)) := by
    rw [MvPolynomial.adjoin_range_X]; trivial
  have hle : Algebra.adjoin ℂ
      (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℂ)) ≤
      Subalgebra.restrictScalars ℂ (Algebra.adjoin (𝒜₂ 0)
        (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℂ))) :=
    Algebra.adjoin_le fun s hs => Algebra.subset_adjoin hs
  exact (Subalgebra.mem_restrictScalars ℂ).mp (hle ha)


-- @@ L284-324 verbatim
theorem chartPolyHom_surjective {i j : Fin 2} (hij : i ≠ j) :
    Function.Surjective (chartPolyHom i j) := by
  have huniv : ({i, j} : Finset (Fin 2)) = Finset.univ :=
    Finset.eq_univ_of_card _
      ((Finset.card_pair_eq_two_iff.mpr hij).trans (Fintype.card_fin 2).symm)
  intro x
  have htop := HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
    (𝒜 := 𝒜₂) (X_mem_grade_one i) (Fin 2) MvPolynomial.X adjoin_range_X_eq_top
    (fun _ => 1) (fun k => X_mem_grade_one k)
  have hx := htop.ge (Algebra.mem_top (x := x))
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨a, ai, hai, -, rfl⟩ := hy
    have hsum : ai i + ai j = a := by
      have h3 : (∑ k, ai k) = a := by simpa using hai
      rw [← h3, ← huniv, Finset.sum_pair hij]
    subst hsum
    refine ⟨MvPolynomial.X 0 ^ ai j, ?_⟩
    apply HomogeneousLocalization.val_injective
    rw [map_pow, chartPolyHom_X, HomogeneousLocalization.val_pow, coordFrac_val,
      Localization.mk_pow, HomogeneousLocalization.Away.val_mk,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    use 1
    have hprod : (∏ k, MvPolynomial.X k ^ ai k : MvPolynomial (Fin 2) ℂ) =
        MvPolynomial.X i ^ ai i * MvPolynomial.X j ^ ai j := by
      rw [← huniv, Finset.prod_pair hij]
    simp only [OneMemClass.coe_one, one_mul, SubmonoidClass.coe_pow, hprod]
    ring
  | algebraMap r =>
    obtain ⟨c, rfl⟩ := gradeZero_algebraMap_bijective.2 r
    exact ⟨MvPolynomial.C c,
      (chartPolyHom_C i j c).trans
        (IsScalarTower.algebraMap_apply ℂ (𝒜₂ 0) (Away 𝒜₂ (MvPolynomial.X i)) c)⟩
  | add y z _ _ hy hz =>
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨q, rfl⟩ := hz
    exact ⟨p + q, map_add _ _ _⟩
  | mul y z _ _ hy hz =>
    obtain ⟨p, rfl⟩ := hy
    obtain ⟨q, rfl⟩ := hz
    exact ⟨p * q, map_mul _ _ _⟩


-- @@ L326-326 verbatim
/-! ## Part 1(e). The chart isomorphism (G1e, the headline of Part 1) -/


-- @@ L328-332 verbatim
/-- The polynomial ring maps isomorphically onto the chart ring. -/
def polyChartEquiv (i j : Fin 2) (hij : i ≠ j) :
    MvPolynomial (Fin 1) ℂ ≃ₐ[ℂ] Away 𝒜₂ (MvPolynomial.X i) :=
  AlgEquiv.ofBijective (chartPolyHom i j)
    ⟨chartPolyHom_injective hij.symm, chartPolyHom_surjective hij⟩


-- @@ L334-336 verbatim
theorem polyChartEquiv_apply (i j : Fin 2) (hij : i ≠ j) (p : MvPolynomial (Fin 1) ℂ) :
    polyChartEquiv i j hij p = chartPolyHom i j p :=
  rfl


-- @@ L338-345 verbatim
/-- **The chart isomorphism**: the chart ring `(ℂ[X₀,X₁]_{Xᵢ})₀` of the
chart `D₊(Xᵢ)` is a polynomial ring in one variable over `ℂ`, as an
isomorphism of `ℂ`-algebras at the single `ℂ`-structure of
`instAlgebraAwayC` (the variable corresponds to the coordinate fraction
`Xⱼ/Xᵢ`, an exhibited choice — no canonicity is claimed for it). -/
def chartPolyEquiv (i j : Fin 2) (hij : i ≠ j) :
    Away 𝒜₂ (MvPolynomial.X i) ≃ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  (polyChartEquiv i j hij).symm


-- @@ L347-352 verbatim
/-- **G1e headline**: `Away 𝒜 X₀ ≃ₐ[ℂ] ℂ[t]` — the chart ring of the
standard chart `D₊(X₀)` of the projective line is `ℂ`-algebra
isomorphic to the polynomial ring in one variable over `ℂ`. -/
def awayXZeroPolyEquiv :
    Away 𝒜₂ (MvPolynomial.X 0) ≃ₐ[ℂ] MvPolynomial (Fin 1) ℂ :=
  chartPolyEquiv 0 1 (by decide)


-- @@ L354-354 verbatim
/-! ## Part 1(f). Units of the chart rings are constants -/


-- @@ L356-376 verbatim
/-- Units of a chart ring are (unit) constants: the transported
`MvPolynomial.isUnit_iff_eq_C_of_isReduced` along the chart
isomorphism. -/
theorem away_unit_eq_algebraMap {i j : Fin 2} (hij : i ≠ j)
    (u : (Away 𝒜₂ (MvPolynomial.X i))ˣ) :
    ∃ c : ℂˣ, (u : Away 𝒜₂ (MvPolynomial.X i)) =
      algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X i)) c := by
  obtain ⟨c, hc, hCc⟩ :=
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced
      (P := chartPolyEquiv i j hij (u : Away 𝒜₂ (MvPolynomial.X i)))).mp
      (u.isUnit.map (chartPolyEquiv i j hij))
  have h2 : (u : Away 𝒜₂ (MvPolynomial.X i)) =
      (chartPolyEquiv i j hij).symm (MvPolynomial.C c) := by
    rw [← hCc, AlgEquiv.symm_apply_apply]
  have h3 : (chartPolyEquiv i j hij).symm (MvPolynomial.C c) =
      algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X i)) c := by
    rw [← MvPolynomial.algebraMap_eq]
    exact AlgEquiv.commutes _ c
  refine ⟨hc.unit, ?_⟩
  rw [IsUnit.unit_spec]
  exact h2.trans h3


-- @@ L378-378 verbatim
/-! ## Part 2. Chart sections, germs, and constants in the function field -/


-- @@ L380-382 verbatim
theorem genericPoint_mem_basicX (i : Fin 2) :
    genericPoint p1 ∈ Proj.basicOpen 𝒜₂ (MvPolynomial.X i) :=
  genericPoint_mem ⟨botPt, botPt_mem_basicOpen (MvPolynomial.X_ne_zero i)⟩


-- @@ L384-387 verbatim
theorem genericPoint_mem_basicX01 :
    genericPoint p1 ∈ Proj.basicOpen 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) :=
  genericPoint_mem ⟨botPt, botPt_mem_basicOpen
    (mul_ne_zero (MvPolynomial.X_ne_zero 0) (MvPolynomial.X_ne_zero 1))⟩


-- @@ L389-392 verbatim
/-- The generic point lies in the second chart (wave 1 provided the first
chart and the overlap). -/
theorem genericPoint_mem_U1 : genericPoint p1 ∈ U1 :=
  genericPoint_mem_basicX 1


-- @@ L394-398 verbatim
/-- The germ-at-the-generic-point map into the function field, as a ring
homomorphism. -/
def germK {W : p1.Opens} (h : genericPoint p1 ∈ W) :
    Γ(p1, W) →+* p1.functionField :=
  (p1.presheaf.germ W (genericPoint p1) h).hom


-- @@ L400-402 verbatim
theorem germK_apply {W : p1.Opens} (h : genericPoint p1 ∈ W) (s : Γ(p1, W)) :
    germK h s = p1.presheaf.germ W (genericPoint p1) h s :=
  rfl


-- @@ L404-408 verbatim
/-- Germs at the generic point are injective on every open
(`germ_injective_of_isIntegral`; the projective line is integral). -/
theorem germK_injective {W : p1.Opens} (h : genericPoint p1 ∈ W) :
    Function.Injective (germK h) :=
  germ_injective_of_isIntegral p1 (genericPoint p1) h


-- @@ L410-413 verbatim
/-- The chart-ring-to-sections map of the pin, as a ring homomorphism. -/
def awaySection (f : MvPolynomial (Fin 2) ℂ) :
    Away 𝒜₂ f →+* Γ(p1, Proj.basicOpen 𝒜₂ f) :=
  (Proj.awayToSection 𝒜₂ f).hom


-- @@ L415-421 verbatim
/-- `awayToSection` is an isomorphism at positive-degree homogeneous
elements (the pin's `basicOpenIsoAway`). -/
theorem isIso_awayToSection {f : MvPolynomial (Fin 2) ℂ} {m : ℕ}
    (hf : f ∈ 𝒜₂ m) (hm : 0 < m) :
    IsIso (Proj.awayToSection 𝒜₂ f) := by
  rw [← Proj.basicOpenIsoAway_hom 𝒜₂ f hf hm]
  infer_instance


-- @@ L423-427 verbatim
theorem awaySection_injective {f : MvPolynomial (Fin 2) ℂ} {m : ℕ}
    (hf : f ∈ 𝒜₂ m) (hm : 0 < m) :
    Function.Injective (awaySection f) := by
  haveI := isIso_awayToSection hf hm
  exact (ConcreteCategory.bijective_of_isIso (Proj.awayToSection 𝒜₂ f)).injective


-- @@ L429-437 verbatim
/-- **The fixed constants map** `ℂ → κ(p1)`: the constants of the
overlap chart ring, pushed to sections over `D₊(X₀X₁)` and then to the
germ at the generic point.  The ONE constants map against which both
charts' constants are compared (an exhibited choice; no canonicity is
claimed for it). -/
def constK : ℂ →+* p1.functionField :=
  ((germK genericPoint_mem_basicX01).comp
    (awaySection (MvPolynomial.X 0 * MvPolynomial.X 1))).comp
    (algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)))


-- @@ L439-476 verbatim
/-- **Both charts' constants agree in the function field**: the germ of a
constant of either chart ring is `constK` of it (through the pin's
`awayMap`/`awayToSection` naturality and `awayMap_fromZeroRingHom`).
This is the single-`ℂ`-structure discipline made into a theorem rather
than an assumption. -/
theorem germK_awaySection_algebraMap (i j : Fin 2)
    (hx : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) =
      MvPolynomial.X i * MvPolynomial.X j)
    (c : ℂ) :
    germK (genericPoint_mem_basicX i)
      (awaySection (MvPolynomial.X i)
        (algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X i)) c)) = constK c := by
  have hres := Proj.awayMap_awayToSection (𝒜 := 𝒜₂) (X_mem_grade_one j) hx
  have hpt := congrArg
    (fun t : CommRingCat.of (Away 𝒜₂ (MvPolynomial.X i)) ⟶
        Γ(p1, Proj.basicOpen 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)) =>
      t (algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X i)) c)) hres
  simp only [CategoryTheory.comp_apply] at hpt
  -- hpt : awayToSection (X0X1) (awayMap … (algebraMap c))
  --     = presheaf.map (homOfLE …).op (awayToSection (X i) (algebraMap c))
  have hmap : awayMap 𝒜₂ (X_mem_grade_one j) hx
      (algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X i)) c) =
      algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)) c := by
    rw [algebraMap_away_apply, awayMap_fromZeroRingHom]
    rfl
  rw [germK_apply,
    ← TopCat.Presheaf.germ_res_apply p1.presheaf
      (homOfLE (Proj.basicOpen_mono _ _ _ ⟨_, hx⟩)) (genericPoint p1)
      genericPoint_mem_basicX01]
  show p1.presheaf.germ _ (genericPoint p1) genericPoint_mem_basicX01
      ((p1.presheaf.map (homOfLE (Proj.basicOpen_mono _ _ _ ⟨_, hx⟩)).op)
        (Proj.awayToSection 𝒜₂ (MvPolynomial.X i)
          (algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X i)) c))) = constK c
  rw [← hpt]
  exact congrArg (fun z : Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) =>
    p1.presheaf.germ (Proj.basicOpen 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1))
      (genericPoint p1) genericPoint_mem_basicX01
      (Proj.awayToSection 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) z)) hmap


-- @@ L478-478 verbatim
/-! ## Part 3. The coordinate germ: the polynomial ring in the function field -/


-- @@ L480-480 verbatim
theorem zero_ne_one_fin : (0 : Fin 2) ≠ 1 := by decide


-- @@ L482-487 verbatim
/-- The injective ring map `ℂ[t] → κ(p1)`: through the chart
isomorphism, the chart sections, and the germ at the generic point. -/
def polyToK : MvPolynomial (Fin 1) ℂ →+* p1.functionField :=
  (((germK (genericPoint_mem_basicX 0)).comp
    (awaySection (MvPolynomial.X 0))).comp
    (polyChartEquiv 0 1 zero_ne_one_fin).toAlgHom.toRingHom)


-- @@ L489-492 verbatim
theorem polyToK_injective : Function.Injective polyToK :=
  ((germK_injective _).comp
    (awaySection_injective (X_mem_grade_one 0) one_pos)).comp
    (polyChartEquiv 0 1 zero_ne_one_fin).injective


-- @@ L494-503 verbatim
/-- The constants of the polynomial ring land on `constK`. -/
theorem polyToK_C (c : ℂ) : polyToK (MvPolynomial.C c) = constK c := by
  have h1 : (polyChartEquiv 0 1 zero_ne_one_fin) (MvPolynomial.C c) =
      algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X 0)) c :=
    chartPolyHom_C 0 1 c
  show germK (genericPoint_mem_basicX 0)
      (awaySection (MvPolynomial.X 0)
        ((polyChartEquiv 0 1 zero_ne_one_fin) (MvPolynomial.C c))) = constK c
  rw [h1]
  exact germK_awaySection_algebraMap 0 1 rfl c


-- @@ L505-531 verbatim
/-- The `awayMap` to the overlap chart carries the coordinate fraction to
the wave-1 overlap unit numerator `awayNum`. -/
theorem awayMap_coordFrac :
    awayMap 𝒜₂ (X_mem_grade_one 1)
      (rfl : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) =
        MvPolynomial.X 0 * MvPolynomial.X 1) (coordFrac 0 1) = awayNum := by
  apply HomogeneousLocalization.val_injective
  have h1 : (awayMap 𝒜₂ (X_mem_grade_one 1)
      (rfl : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) =
        MvPolynomial.X 0 * MvPolynomial.X 1) (coordFrac 0 1)).val =
      Localization.mk (MvPolynomial.X 1 * MvPolynomial.X 1 ^ 1)
        (⟨(MvPolynomial.X 0 * MvPolynomial.X 1) ^ 1, 1, rfl⟩ :
          Submonoid.powers
            (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ)) := by
    rw [show coordFrac 0 1 = HomogeneousLocalization.Away.mk 𝒜₂ (X_mem_grade_one 0) 1
        (MvPolynomial.X 1) ((one_smul ℕ 1).symm ▸ X_mem_grade_one 1) from rfl,
      awayMap_mk]
    exact HomogeneousLocalization.Away.val_mk _ _ _ _ _
  have h2 : (awayNum).val =
      Localization.mk (MvPolynomial.X 1 * MvPolynomial.X 1)
        (⟨(MvPolynomial.X 0 * MvPolynomial.X 1) ^ 1, 1, rfl⟩ :
          Submonoid.powers
            (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ)) :=
    HomogeneousLocalization.Away.val_mk _ _ _ _ _
  rw [h1, h2, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  ring


-- @@ L533-565 verbatim
/-- The coordinate of the polynomial ring lands on the germ of the
overlap unit numerator. -/
theorem polyToK_X :
    polyToK (MvPolynomial.X 0) =
      germK genericPoint_mem_basicX01
        (awaySection (MvPolynomial.X 0 * MvPolynomial.X 1) awayNum) := by
  have h1 : (polyChartEquiv 0 1 zero_ne_one_fin) (MvPolynomial.X 0) =
      coordFrac 0 1 :=
    chartPolyHom_X 0 1 0
  show germK (genericPoint_mem_basicX 0)
      (awaySection (MvPolynomial.X 0)
        ((polyChartEquiv 0 1 zero_ne_one_fin) (MvPolynomial.X 0))) = _
  rw [h1]
  have hres := Proj.awayMap_awayToSection (𝒜 := 𝒜₂) (X_mem_grade_one 1)
    (rfl : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) =
      MvPolynomial.X 0 * MvPolynomial.X 1)
  have hpt := congrArg
    (fun t : CommRingCat.of (Away 𝒜₂ (MvPolynomial.X 0)) ⟶
        Γ(p1, Proj.basicOpen 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)) =>
      t (coordFrac 0 1)) hres
  simp only [CategoryTheory.comp_apply] at hpt
  rw [germK_apply,
    ← TopCat.Presheaf.germ_res_apply p1.presheaf
      (homOfLE (Proj.basicOpen_mono _ _ _ ⟨_, rfl⟩)) (genericPoint p1)
      genericPoint_mem_basicX01]
  show p1.presheaf.germ _ (genericPoint p1) genericPoint_mem_basicX01
      ((p1.presheaf.map (homOfLE (Proj.basicOpen_mono _ _ _ ⟨_, rfl⟩)).op)
        (Proj.awayToSection 𝒜₂ (MvPolynomial.X 0) (coordFrac 0 1))) = _
  rw [← hpt]
  exact congrArg (fun z : Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) =>
    p1.presheaf.germ (Proj.basicOpen 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1))
      (genericPoint p1) genericPoint_mem_basicX01
      (Proj.awayToSection 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) z)) awayMap_coordFrac


-- @@ L567-576 verbatim
/-- **The coordinate is not a constant** (in the function field, through
the injective `polyToK` — the `totalDegree` separation). -/
theorem polyToK_X_ne_C (c : ℂ) :
    polyToK (MvPolynomial.X 0) ≠ polyToK (MvPolynomial.C c) := by
  intro h
  have hXC := polyToK_injective h
  have h1 : (MvPolynomial.X (R := ℂ) (0 : Fin 1)).totalDegree = 1 :=
    MvPolynomial.totalDegree_X 0
  rw [hXC, MvPolynomial.totalDegree_C] at h1
  exact zero_ne_one h1


-- @@ L578-578 verbatim
/-! ## Part 4. Section-level extraction (the pin's left-exactness) -/


-- @@ L580-580 verbatim
section Extraction


-- @@ L582-582 verbatim
variable (X : Scheme.{0}) [IsIntegral X]


-- @@ L584-595 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Section-level extraction from the Cartier sequence: the pin's
`TopCat.Sheaf.sections_exact_of_left_exact` applied to the shipped
`cartierSC X`, crossed to the `TopCat.Sheaf` spelling.  Section-level;
no stalks and no valuations anywhere. -/
theorem cartier_sections_extraction (U : X.Opens)
    (s : (KUnitsAb X).obj.obj (op U))
    (h : (divisorsπ X).hom.app (op U) s = 0) :
    ∃ t : (unitsAb X).obj.obj (op U), (unitsToK X).hom.app (op U) t = s :=
  TopCat.Sheaf.sections_exact_of_left_exact
    (S := (cartierSC X : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} (X : TopCat))))
    (cartierSC_shortExact X).exact (cartierSC_shortExact X).mono_f s h


-- @@ L597-611 verbatim
/-- `divOf` at the concrete `Γ(⊤)`-sections level (the pin's
`Sheaf.H.equiv₀_naturality`). -/
theorem cdivSectionsEquiv_divOf (f : Additive (X.functionField)ˣ) :
    cdivSectionsEquiv X (divOf X f) =
      (divisorsπ X).hom.app (op (⊤ : X.Opens)) ((kSectionsTopEquiv X).symm f) :=
  calc cdivSectionsEquiv X (divOf X f)
      = Sheaf.H.equiv₀ (divisorsAb X) (opensTopIsTerminal X)
          (Sheaf.H.map (divisorsπ X) 0 ((kUnitsH0Equiv X).symm f)) := rfl
    _ = (divisorsπ X).hom.app (op (⊤ : X.Opens))
          (Sheaf.H.equiv₀ (KUnitsAb X) (opensTopIsTerminal X)
            ((kUnitsH0Equiv X).symm f)) :=
        (Sheaf.H.equiv₀_naturality (opensTopIsTerminal X) (divisorsπ X) _).symm
    _ = (divisorsπ X).hom.app (op (⊤ : X.Opens)) ((kSectionsTopEquiv X).symm f) :=
        congrArg _ ((Sheaf.H.equiv₀ (KUnitsAb X)
          (opensTopIsTerminal X)).apply_symm_apply _)


-- @@ L613-613 verbatim
end Extraction


-- @@ L615-615 verbatim
/-! ## Part 5. Restricting a hypothesized principality to the charts -/


-- @@ L617-619 verbatim
/-- Wave 1's rational function `zElt`, retyped once at
`Additive κ(p1)ˣ` (statement-hygiene wrapper; definitionally `zElt`). -/
def zeltK : Additive (p1.functionField)ˣ := zElt


-- @@ L621-622 verbatim
/-- Receipt: `zeltK` is wave 1's `zElt`, definitionally. -/
theorem zeltK_eq : zeltK = zElt := rfl


-- @@ L624-629 verbatim
/-- The section of `K^*` over `W` given by a rational function (the
skyscraper sections identification; wave 1's `zSectionK` at an arbitrary
rational function). -/
def kSec (f : Additive (p1.functionField)ˣ) {W : p1.Opens}
    (h : genericPoint p1 ∈ W) : ((KUnitsAb p1).obj.obj (op W)) :=
  eqToHom (KUnitsAb_obj_of_mem p1 h).symm f


-- @@ L631-634 verbatim
/-- Receipt: at `zeltK`, `kSec` is wave 1's `zSectionK`. -/
theorem kSec_zElt {W : p1.Opens} (h : genericPoint p1 ∈ W) :
    kSec zeltK h = zSectionK h :=
  rfl


-- @@ L636-638 verbatim
theorem kSectionsTopEquiv_symm_eq (f : Additive (p1.functionField)ˣ) :
    (kSectionsTopEquiv p1).symm f = kSec f (Opens.mem_top (genericPoint p1)) :=
  rfl


-- @@ L640-647 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem kSec_restrict (f : Additive (p1.functionField)ˣ) {W W' : p1.Opens}
    (i : W' ⟶ W) (h : genericPoint p1 ∈ W) (h' : genericPoint p1 ∈ W') :
    (KUnitsAb p1).obj.map i.op (kSec f h) = kSec f h' := by
  rw [KUnitsAb_map_of_mem p1 i.op h']
  show (eqToHom (KUnitsAb_obj_of_mem p1 h).symm ≫ eqToHom _) f = _
  rw [eqToHom_trans]
  rfl


-- @@ L649-656 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem divisorsπ_app_restrict {W W' : p1.Opens} (i : W' ⟶ W)
    (s : (KUnitsAb p1).obj.obj (op W)) :
    (divisorsAb p1).obj.map i.op ((divisorsπ p1).hom.app (op W) s) =
      (divisorsπ p1).hom.app (op W') ((KUnitsAb p1).obj.map i.op s) := by
  show ((divisorsπ p1).hom.app (op W) ≫ (divisorsAb p1).obj.map i.op) s = _
  rw [← (divisorsπ p1).hom.naturality]
  rfl


-- @@ L658-673 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The wave-1 top section restricts to the left gluing datum on the
first chart. -/
theorem dinfTopSection_restrict_U0 :
    (divisorsAb p1).obj.map (homOfLE (le_top : U0 ≤ ⊤)).op dinfTopSection =
      dinfLeft := by
  show (divisorsAb p1).obj.map (homOfLE le_top).op
      ((divisorsAb p1).obj.map (homOfLE U0_sup_U1.ge).op
        (dinfGlued : (divisorsAb p1).obj.obj (op (U0 ⊔ U1)))) = dinfLeft
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  have harr : (homOfLE U0_sup_U1.ge).op ≫ (homOfLE (le_top : U0 ≤ ⊤)).op =
      ((Opens.mayerVietorisSquare U0 U1).f₂₄).op := by
    rw [← op_comp]
    exact congrArg Quiver.Hom.op (Subsingleton.elim _ _)
  rw [harr]
  exact dinfGlued_restrict_left


-- @@ L675-690 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The wave-1 top section restricts to zero on the second chart. -/
theorem dinfTopSection_restrict_U1 :
    (divisorsAb p1).obj.map (homOfLE (le_top : U1 ≤ ⊤)).op dinfTopSection =
      0 := by
  show (divisorsAb p1).obj.map (homOfLE le_top).op
      ((divisorsAb p1).obj.map (homOfLE U0_sup_U1.ge).op
        (dinfGlued : (divisorsAb p1).obj.obj (op (U0 ⊔ U1)))) =
    (0 : (divisorsAb p1).obj.obj (op U1))
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp]
  have harr : (homOfLE U0_sup_U1.ge).op ≫ (homOfLE (le_top : U1 ≤ ⊤)).op =
      ((Opens.mayerVietorisSquare U0 U1).f₃₄).op := by
    rw [← op_comp]
    exact congrArg Quiver.Hom.op (Subsingleton.elim _ _)
  rw [harr]
  exact dinfGlued_restrict_right


-- @@ L692-730 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **The chart factorization over `U0`**: if `divOf f = dinf`, then over
the first chart `f` differs from `zElt` by (the germ of) a unit of the
structure sheaf.  Section-level extraction; no valuation. -/
theorem exists_unit_factor_U0 (f : Additive (p1.functionField)ˣ)
    (hf : divOf p1 f = dinf) :
    ∃ t : (unitsAb p1).obj.obj (op U0),
      germUnitsHom p1 genericPoint_mem_U0 t = f - zeltK := by
  have hTop : (divisorsπ p1).hom.app (op (⊤ : p1.Opens))
      ((kSectionsTopEquiv p1).symm f) = dinfTopSection := by
    have h1 := cdivSectionsEquiv_divOf p1 f
    rw [hf] at h1
    rw [← h1]
    exact (cdivSectionsEquiv p1).apply_symm_apply dinfTopSection
  have hres0 : (divisorsπ p1).hom.app (op U0) (kSec f genericPoint_mem_U0) =
      (divisorsπ p1).hom.app (op U0) (zSectionK genericPoint_mem_U0) := by
    have h2 := congrArg
      ((divisorsAb p1).obj.map (homOfLE (le_top : U0 ≤ ⊤)).op) hTop
    rw [divisorsπ_app_restrict, dinfTopSection_restrict_U0,
      kSectionsTopEquiv_symm_eq,
      kSec_restrict f (homOfLE le_top) (Opens.mem_top (genericPoint p1))
        genericPoint_mem_U0] at h2
    rw [h2]
    rfl
  have hzero : (divisorsπ p1).hom.app (op U0)
      (kSec f genericPoint_mem_U0 - zSectionK genericPoint_mem_U0) = 0 := by
    rw [map_sub, hres0, sub_self]
  obtain ⟨t, ht⟩ := cartier_sections_extraction p1 U0 _ hzero
  refine ⟨t, ?_⟩
  rw [unitsToK_app_of_mem p1 (U := op U0) genericPoint_mem_U0] at ht
  have hsub : kSec f genericPoint_mem_U0 - zSectionK genericPoint_mem_U0 =
      eqToHom (KUnitsAb_obj_of_mem p1 genericPoint_mem_U0).symm (f - zeltK) := by
    rw [map_sub]
    rfl
  rw [hsub, CategoryTheory.comp_apply] at ht
  have hinj : Function.Injective
      (eqToHom (KUnitsAb_obj_of_mem p1 genericPoint_mem_U0).symm) :=
    (ConcreteCategory.bijective_of_isIso _).injective
  exact hinj ht


-- @@ L732-761 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **The chart factorization over `U1`**: if `divOf f = dinf`, then over
the second chart `f` is (the germ of) a unit of the structure sheaf. -/
theorem exists_unit_factor_U1 (f : Additive (p1.functionField)ˣ)
    (hf : divOf p1 f = dinf) :
    ∃ t : (unitsAb p1).obj.obj (op U1),
      germUnitsHom p1 genericPoint_mem_U1 t = f := by
  have hTop : (divisorsπ p1).hom.app (op (⊤ : p1.Opens))
      ((kSectionsTopEquiv p1).symm f) = dinfTopSection := by
    have h1 := cdivSectionsEquiv_divOf p1 f
    rw [hf] at h1
    rw [← h1]
    exact (cdivSectionsEquiv p1).apply_symm_apply dinfTopSection
  have hzero : (divisorsπ p1).hom.app (op U1)
      (kSec f genericPoint_mem_U1) = 0 := by
    have h2 := congrArg
      ((divisorsAb p1).obj.map (homOfLE (le_top : U1 ≤ ⊤)).op) hTop
    rw [divisorsπ_app_restrict, dinfTopSection_restrict_U1,
      kSectionsTopEquiv_symm_eq,
      kSec_restrict f (homOfLE le_top) (Opens.mem_top (genericPoint p1))
        genericPoint_mem_U1] at h2
    exact h2
  obtain ⟨t, ht⟩ := cartier_sections_extraction p1 U1 _ hzero
  refine ⟨t, ?_⟩
  rw [unitsToK_app_of_mem p1 (U := op U1) genericPoint_mem_U1,
    CategoryTheory.comp_apply] at ht
  have hinj : Function.Injective
      (eqToHom (KUnitsAb_obj_of_mem p1 genericPoint_mem_U1).symm) :=
    (ConcreteCategory.bijective_of_isIso _).injective
  exact hinj ht


-- @@ L763-763 verbatim
/-! ## Part 6. The endgame in the function field -/


-- @@ L765-767 verbatim
/-- The units-level constants map `ℂˣ → κ(p1)ˣ`. -/
def embUnits : ℂˣ →* (p1.functionField)ˣ :=
  Units.map (constK : ℂ →+* p1.functionField).toMonoidHom


-- @@ L769-774 verbatim
theorem toMul_germUnitsHom {W : p1.Opens} (h : genericPoint p1 ∈ W)
    (t : (unitsAb p1).obj.obj (op W)) :
    (Additive.toMul (germUnitsHom p1 h t) : (p1.functionField)ˣ) =
      Units.map ((p1.presheaf.germ W (genericPoint p1) h).hom :
        Γ(p1, W) →* p1.functionField) (Additive.toMul t) :=
  rfl


-- @@ L776-800 verbatim
/-- Units of the chart sections have constant germs: the chart
isomorphism (Part 1) transported through `awayToSection`. -/
theorem section_unit_germ_eq_const {i j : Fin 2} (hij : i ≠ j)
    (hx : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) =
      MvPolynomial.X i * MvPolynomial.X j)
    (u : (Γ(p1, Proj.basicOpen 𝒜₂ (MvPolynomial.X i)))ˣ) :
    ∃ c : ℂˣ, germK (genericPoint_mem_basicX i)
      (u : Γ(p1, Proj.basicOpen 𝒜₂ (MvPolynomial.X i))) = constK c := by
  haveI := isIso_awayToSection (X_mem_grade_one i) one_pos
  let e := (asIso (Proj.awayToSection 𝒜₂
    (MvPolynomial.X i))).commRingCatIsoToRingEquiv
  obtain ⟨c, hc⟩ := away_unit_eq_algebraMap hij (Units.map e.symm.toMonoidHom u)
  refine ⟨c, ?_⟩
  have h1 : (u : Γ(p1, Proj.basicOpen 𝒜₂ (MvPolynomial.X i))) =
      awaySection (MvPolynomial.X i)
        (algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X i)) c) := by
    have h0 : (u : Γ(p1, Proj.basicOpen 𝒜₂ (MvPolynomial.X i))) =
        e (e.symm (u : Γ(p1, Proj.basicOpen 𝒜₂ (MvPolynomial.X i)))) :=
      (e.apply_symm_apply _).symm
    rw [h0,
      show e.symm (u : Γ(p1, Proj.basicOpen 𝒜₂ (MvPolynomial.X i))) =
        algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X i)) c from hc]
    rfl
  rw [h1]
  exact germK_awaySection_algebraMap i j hx c


-- @@ L802-819 verbatim
/-- The germ of a chart-sections unit is an embedded constant unit. -/
theorem germUnits_factor_embUnits (i j : Fin 2) (hij : i ≠ j)
    (hx : (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) =
      MvPolynomial.X i * MvPolynomial.X j)
    (h : genericPoint p1 ∈ Proj.basicOpen 𝒜₂ (MvPolynomial.X i))
    (t : (unitsAb p1).obj.obj (op (Proj.basicOpen 𝒜₂ (MvPolynomial.X i)))) :
    ∃ c : ℂˣ, (Additive.toMul (germUnitsHom p1 h t) : (p1.functionField)ˣ) =
      embUnits c := by
  obtain ⟨c, hc⟩ := section_unit_germ_eq_const hij hx
    (Additive.toMul t : (Γ(p1, Proj.basicOpen 𝒜₂ (MvPolynomial.X i)))ˣ)
  refine ⟨c, ?_⟩
  apply Units.ext
  rw [toMul_germUnitsHom]
  show germK h ((Additive.toMul t :
      (Γ(p1, Proj.basicOpen 𝒜₂ (MvPolynomial.X i)))ˣ) :
    Γ(p1, Proj.basicOpen 𝒜₂ (MvPolynomial.X i))) = _
  rw [show germK h = germK (genericPoint_mem_basicX i) from rfl, hc]
  rfl


-- @@ L821-836 verbatim
/-- The germ of `zElt` in the function field is the image of the chart
coordinate under `polyToK` (both are the germ of the overlap unit
numerator over `D₊(X₀X₁)`). -/
theorem zElt_toMul_val :
    ((Additive.toMul zeltK : (p1.functionField)ˣ) : p1.functionField) =
      polyToK (MvPolynomial.X 0) := by
  rw [polyToK_X]
  show germK genericPoint_mem_U01 (overlapRingHom awayNum) =
    germK genericPoint_mem_basicX01
      (awaySection (MvPolynomial.X 0 * MvPolynomial.X 1) awayNum)
  rw [germK_apply, germK_apply]
  show p1.presheaf.germ (U0 ⊓ U1) (genericPoint p1) genericPoint_mem_U01
      ((p1.presheaf.map (homOfLE (le_of_eq U0_inf_U1)).op)
        (Proj.awayToSection 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) awayNum)) = _
  rw [TopCat.Presheaf.germ_res_apply]
  rfl


-- @@ L838-838 verbatim
/-! ## Part 7. THE NONVANISHING THEOREM and its falsifier suite -/


-- @@ L840-872 verbatim
/-- **Non-principality of the point-divisor datum**: no rational function
on the projective line has divisor datum `dinf`.  (The two chart
factorizations force the coordinate `zElt` to be an embedded constant,
refuted by the `totalDegree` separation through the injective
`polyToK`.) -/
theorem divOf_ne_dinf (f : Additive (p1.functionField)ˣ) :
    divOf p1 f ≠ dinf := by
  intro hf
  obtain ⟨t0, ht0⟩ := exists_unit_factor_U0 f hf
  obtain ⟨t1, ht1⟩ := exists_unit_factor_U1 f hf
  obtain ⟨c0, hc0⟩ := germUnits_factor_embUnits 0 1 zero_ne_one_fin rfl
    genericPoint_mem_U0 t0
  obtain ⟨c1, hc1⟩ := germUnits_factor_embUnits 1 0 zero_ne_one_fin.symm
    (mul_comm _ _) genericPoint_mem_U1 t1
  have h0 : (Additive.toMul (f : Additive (p1.functionField)ˣ) :
      (p1.functionField)ˣ) / Additive.toMul zeltK = embUnits c0 :=
    (toMul_sub f zeltK).symm.trans
      ((congrArg Additive.toMul ht0).symm.trans hc0)
  have h1 : (Additive.toMul (f : Additive (p1.functionField)ˣ) :
      (p1.functionField)ˣ) = embUnits c1 :=
    (congrArg Additive.toMul ht1).symm.trans hc1
  have hZc : (Additive.toMul zeltK : (p1.functionField)ˣ) =
      embUnits (c0⁻¹ * c1) := by
    have hZ : (Additive.toMul zeltK : (p1.functionField)ˣ) =
        (embUnits c0)⁻¹ * Additive.toMul (f : Additive (p1.functionField)ˣ) :=
      eq_inv_mul_iff_mul_eq.mpr (div_eq_iff_eq_mul.mp h0).symm
    rw [hZ, h1, map_mul, map_inv]
  have hval := congrArg Units.val hZc
  rw [zElt_toMul_val] at hval
  have hval2 : polyToK (MvPolynomial.X 0) =
      constK ((c0⁻¹ * c1 : ℂˣ) : ℂ) := hval
  rw [← polyToK_C] at hval2
  exact polyToK_X_ne_C _ hval2


-- @@ L874-886 verbatim
/-- **THE NONVANISHING THEOREM (G2d)**: the class of the point-divisor
datum `dinf` is **a nonzero class in `H^1(X, O^*)` in the sense of
Mathlib's `Sheaf.H`**, for `X` the projective line.

By the shipped exactness `cdivClass_eq_zero_iff`, this is exactly the
non-principality `divOf_ne_dinf`; no cohomology group is computed.
`H^1(X, O^*)` is *classically* the Picard group; no Picard group is
constructed, no degree homomorphism is constructed, and no comparison
with any other cohomology theory (or other presentation of `H^1`) is
claimed.  Nothing here makes the Hodge conjecture statable. -/
theorem dinfClass_ne_zero : dinfClass ≠ 0 :=
  (not_congr (cdivClass_eq_zero_iff p1 dinf)).mpr
    (fun h => h.elim (fun f hf => divOf_ne_dinf f hf))


-- @@ L888-890 verbatim
/-! ### The falsifier suite

Shipped alongside the theorem so that a wrong proof would be caught. -/


-- @@ L892-896 verbatim
/-- **Negative control**: the divisor class of the SAME coordinate
function `zElt` (as a principal divisor) IS zero — a proof scheme that
secretly proved "every class is nonzero" would contradict this. -/
theorem cdivClass_divOf_zElt : cdivClass p1 (divOf p1 zeltK) = 0 :=
  cdivClass_divOf p1 zeltK


-- @@ L898-900 verbatim
/-- Corollary (restatement): `dinf` is not in the range of `divOf`. -/
theorem dinf_notMem_range_divOf : dinf ∉ Set.range (divOf p1) :=
  fun h => h.elim (fun f hf => divOf_ne_dinf f hf)


-- @@ L902-904 verbatim
/-- Corollary (restatement): `dinfClass` is not in `{0}`. -/
theorem dinfClass_notMem_zero : dinfClass ∉ ({0} : Set (unitsH1 p1)) :=
  fun h => dinfClass_ne_zero h


-- @@ L906-913 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **Statement-drift guard**: the theorem's `dinf` is wave 1's literal
Mayer–Vietoris glue datum, definitionally. -/
theorem dinf_receipt :
    dinf = (cdivSectionsEquiv p1).symm
      ((divisorsAb p1).obj.map (homOfLE U0_sup_U1.ge).op
        (dinfGlued : (divisorsAb p1).obj.obj (op (U0 ⊔ U1)))) :=
  rfl


-- @@ L915-918 verbatim
/-- **Statement-drift guard**: the theorem's subject is wave 1's literal
divisor class, definitionally. -/
theorem dinfClass_receipt : dinfClass = cdivClass p1 dinf :=
  rfl


-- @@ L920-924 verbatim
/-- `H^1(X, O^*)` of the projective line, in the sense of Mathlib's
`Sheaf.H`, is a nontrivial group.  (No Picard group is constructed and
no such identification is claimed.) -/
theorem nontrivial_unitsH1 : Nontrivial (unitsH1 p1) :=
  ⟨⟨dinfClass, 0, dinfClass_ne_zero⟩⟩


-- @@ L926-926 verbatim
/-! ## Part 8. Transport to the small affine Zariski site -/


-- @@ L928-934 verbatim
/-- The nonvanishing at `chernOneF`'s affine-site home: the transported
class is nonzero (one application of the shipped equivalence
`CycCarrier.unitsHSiteEquiv`). -/
theorem dinfClassAffine_ne_zero : unitsHSiteEquiv p1 1 dinfClass ≠ 0 := by
  intro h
  exact dinfClass_ne_zero
    ((unitsHSiteEquiv p1 1).injective (h.trans (map_zero _).symm))


-- @@ L936-944 verbatim
/-- The affine-site divisor class of the moved datum `dinfAffine` is
nonzero (via the shipped `cdivClass_siteMove`). -/
theorem cdivClassAffine_dinfAffine_ne_zero :
    cdivClassAffine p1 dinfAffine ≠ 0 := by
  intro h
  apply dinfClassAffine_ne_zero
  show unitsHSiteEquiv p1 1 (cdivClass p1 dinf) = 0
  rw [← cdivClass_siteMove p1 dinf]
  exact h


-- @@ L946-946 verbatim
end ProjectiveLineUnits


-- @@ L948-948 verbatim
end HodgePilot


-- @@ L950-950 verbatim
end
