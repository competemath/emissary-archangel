import HodgePilot.ProjectivePlane
import HodgePilot.PlaneCarrierProbe
import HodgePilot.CalibrationDegreeFour


-- @@ L5-34 verbatim
/-! # Projective-plane chart algebra (`HodgePilot.ProjectivePlaneChart`)

The two-variable chart isomorphism of the standard charts of
`ℙ² = Proj ℂ[X₀,X₁,X₂]`:

    Away 𝒜₃ Xᵢ ≃ₐ[ℂ] ℂ[s,t]          (`chartPolyEquiv`, `awayXZeroPolyEquiv`)

together with the constants receipt of the plane chart rings against the
structure `ℂ`-algebra (`constants_receipt`), the units-are-constants analysis
(`away_unit_eq_algebraMap`), and the two-generated chart seed: the chart de Rham
terms die in degrees `≥ 3` (`subsingleton_DR_chart`).

This is the `Fin 2 → Fin 3`, `𝒜₂ → 𝒜₃`, single-generator → **pair-generator**
re-key of `HodgePilot.ProjectiveLineUnits` Part 1 and
`HodgePilot.CalibrationDegreeFour` §2–3; the two-generator de Rham collapse is
`HodgePilot.PlaneCarrierProbe.subsingleton_DR_of_adjoin_pair` (shipped).

## Claim discipline

Pure carrier bookkeeping on constructed objects.  Standard-chart coordinate
rings are *presented* so the generic de Rham machinery applies; **no
nonvanishing of any cohomology is produced or approached, no comparison map, no
canonicity, and nothing here is claimed to make the Hodge conjecture statable**.
The carriers are constructed; no Picard group and no linear-equivalence
statement is made anywhere; the filtration everywhere is the naive
(brutal-truncation) one.  The FULL-carrier `F²H⁴` statement stays OUT of scope
(parked on upstream affine vanishing).  Nothing here is a novelty claim beyond
what `NOVELTIES.md` logs (the P1 `chartPolyEquiv` is already logged; its P2
sibling inherits the same constructed-carrier ceilings).
-/


-- @@ L36-36 verbatim
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

-- @@ L37-37 verbatim
open AlgebraicGeometry HomogeneousLocalization


-- @@ L39-39 verbatim
set_option maxHeartbeats 1000000

-- @@ L40-40 verbatim
set_option synthInstance.maxHeartbeats 1000000


-- @@ L42-42 verbatim
noncomputable section


-- @@ L44-44 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L46-46 verbatim
namespace HodgePilot

-- @@ L47-47 verbatim
namespace ProjectivePlaneChart


-- @@ L49-49 verbatim
open HodgePilot.DeRham HodgePilot.DeRhamPresheaf HodgePilot.DeRhamSheaf

-- @@ L50-50 verbatim
open HodgePilot.ProjectivePlane


-- @@ L52-52 verbatim
local notation "𝒜₃" => MvPolynomial.homogeneousSubmodule (Fin 3) ℂ


-- @@ L54-54 verbatim
/-! ## Part 1(a). The single `ℂ`-structure on the chart rings -/


-- @@ L56-58 verbatim
theorem X_mem_grade_one (i : Fin 3) :
    (MvPolynomial.X i : MvPolynomial (Fin 3) ℂ) ∈ 𝒜₃ 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X ℂ i)


-- @@ L60-79 verbatim
/-- The single `ℂ`-algebra structure on the plane chart rings (re-key of
`ProjectiveLineUnits.instAlgebraAwayC`). -/
instance instAlgebraAwayC (f : MvPolynomial (Fin 3) ℂ) :
    Algebra ℂ (Away 𝒜₃ f) where
  toSMul := inferInstance
  algebraMap := (fromZeroRingHom 𝒜₃ (Submonoid.powers f)).comp (algebraMap ℂ (𝒜₃ 0))
  commutes' _ _ := mul_comm _ _
  smul_def' c x := by
    apply HomogeneousLocalization.val_injective
    obtain ⟨y, rfl⟩ := HomogeneousLocalization.mk_surjective x
    rw [HomogeneousLocalization.val_smul, HomogeneousLocalization.val_mul,
      HomogeneousLocalization.val_mk]
    show c • Localization.mk _ _ =
      (HomogeneousLocalization.mk ⟨0, algebraMap ℂ (𝒜₃ 0) c, 1, one_mem _⟩).val * _
    rw [HomogeneousLocalization.val_mk, Localization.smul_mk, Localization.mk_mul,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    use 1
    simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul,
      SetLike.GradeZero.coe_one, SetLike.GradeZero.coe_algebraMap,
      MvPolynomial.algebraMap_eq, MvPolynomial.smul_eq_C_mul]


-- @@ L81-101 verbatim
instance instIsScalarTowerAwayC (f : MvPolynomial (Fin 3) ℂ) :
    IsScalarTower ℂ (𝒜₃ 0) (Away 𝒜₃ f) where
  smul_assoc c r x := by
    apply HomogeneousLocalization.val_injective
    obtain ⟨y, rfl⟩ := HomogeneousLocalization.mk_surjective x
    show ((fromZeroRingHom 𝒜₃ (Submonoid.powers f) (c • r)) *
        HomogeneousLocalization.mk y).val =
      (c • (fromZeroRingHom 𝒜₃ (Submonoid.powers f) r *
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


-- @@ L103-106 verbatim
theorem algebraMap_away_apply (f : MvPolynomial (Fin 3) ℂ) (c : ℂ) :
    algebraMap ℂ (Away 𝒜₃ f) c =
      fromZeroRingHom 𝒜₃ (Submonoid.powers f) (algebraMap ℂ (𝒜₃ 0) c) :=
  rfl


-- @@ L108-108 verbatim
/-! ## Part 1(b). Coordinate fractions and the PAIR chart-poly hom (B1.1–B1.3) -/


-- @@ L110-113 verbatim
/-- B1.2: the coordinate fraction `Xⱼ/Xᵢ` on `D₊(Xᵢ)`. -/
def coordFrac (i j : Fin 3) : Away 𝒜₃ (MvPolynomial.X i) :=
  HomogeneousLocalization.Away.mk 𝒜₃ (X_mem_grade_one i) 1 (MvPolynomial.X j)
    ((one_smul ℕ 1).symm ▸ X_mem_grade_one j)


-- @@ L115-120 verbatim
theorem coordFrac_val (i j : Fin 3) :
    (coordFrac i j).val =
      Localization.mk (MvPolynomial.X j)
        (⟨MvPolynomial.X i ^ 1, 1, rfl⟩ :
          Submonoid.powers (MvPolynomial.X i : MvPolynomial (Fin 3) ℂ)) :=
  HomogeneousLocalization.Away.val_mk _ _ _ _ _


-- @@ L122-125 verbatim
/-- B1.1: the PAIR chart-poly hom `ℂ[s,t] → Away 𝒜₃ Xᵢ`, `s↦Xⱼ/Xᵢ`, `t↦Xₖ/Xᵢ`. -/
def chartPolyHom (i j k : Fin 3) :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ] Away 𝒜₃ (MvPolynomial.X i) :=
  MvPolynomial.aeval (![coordFrac i j, coordFrac i k])


-- @@ L127-129 verbatim
theorem chartPolyHom_X0 (i j k : Fin 3) :
    chartPolyHom i j k (MvPolynomial.X 0) = coordFrac i j := by
  rw [chartPolyHom, MvPolynomial.aeval_X]; rfl


-- @@ L131-133 verbatim
theorem chartPolyHom_X1 (i j k : Fin 3) :
    chartPolyHom i j k (MvPolynomial.X 1) = coordFrac i k := by
  rw [chartPolyHom, MvPolynomial.aeval_X]; rfl


-- @@ L135-138 verbatim
theorem chartPolyHom_C (i j k : Fin 3) (c : ℂ) :
    chartPolyHom i j k (MvPolynomial.C c) =
      algebraMap ℂ (Away 𝒜₃ (MvPolynomial.X i)) c :=
  MvPolynomial.aeval_C _ c


-- @@ L140-140 verbatim
/-! ## Part 1(c). Evaluation at ℂ-points (B1.3) -/


-- @@ L142-143 verbatim
def chartEvalPt (i j _k : Fin 3) (lam0 lam1 : ℂ) : Fin 3 → ℂ :=
  fun m => if m = i then 1 else if m = j then lam0 else lam1


-- @@ L145-146 verbatim
theorem chartEvalPt_i (i j k : Fin 3) (l0 l1 : ℂ) : chartEvalPt i j k l0 l1 i = 1 :=
  if_pos rfl


-- @@ L148-149 verbatim
theorem chartEvalPt_j {i j k : Fin 3} (hji : j ≠ i) (l0 l1 : ℂ) :
    chartEvalPt i j k l0 l1 j = l0 := by rw [chartEvalPt, if_neg hji, if_pos rfl]


-- @@ L151-152 verbatim
theorem chartEvalPt_k {i j k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) (l0 l1 : ℂ) :
    chartEvalPt i j k l0 l1 k = l1 := by rw [chartEvalPt, if_neg hki, if_neg hkj]


-- @@ L154-156 verbatim
theorem chartEvalPt_isUnit (i j k : Fin 3) (l0 l1 : ℂ) :
    IsUnit (MvPolynomial.eval (chartEvalPt i j k l0 l1) (MvPolynomial.X i)) := by
  rw [MvPolynomial.eval_X, chartEvalPt_i]; exact isUnit_one


-- @@ L158-162 verbatim
def chartEval (i j k : Fin 3) (l0 l1 : ℂ) : Away 𝒜₃ (MvPolynomial.X i) →+* ℂ :=
  (Localization.awayLift (MvPolynomial.eval (chartEvalPt i j k l0 l1)) (MvPolynomial.X i)
    (chartEvalPt_isUnit i j k l0 l1)).comp
    (algebraMap (Away 𝒜₃ (MvPolynomial.X i))
      (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin 3) ℂ)))


-- @@ L164-175 verbatim
theorem chartEval_algebraMap (i j k : Fin 3) (l0 l1 c : ℂ) :
    chartEval i j k l0 l1 (algebraMap ℂ (Away 𝒜₃ (MvPolynomial.X i)) c) = c := by
  have hval : (algebraMap ℂ (Away 𝒜₃ (MvPolynomial.X i)) c).val =
      algebraMap (MvPolynomial (Fin 3) ℂ)
        (Localization.Away (MvPolynomial.X i : MvPolynomial (Fin 3) ℂ))
        (MvPolynomial.C c) := by
    rw [algebraMap_away_apply]
    show Localization.mk _ 1 = _
    rw [Localization.mk_one_eq_algebraMap, SetLike.GradeZero.coe_algebraMap,
      MvPolynomial.algebraMap_eq]
  rw [chartEval, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, hval,
    IsLocalization.Away.lift_eq, MvPolynomial.eval_C]


-- @@ L177-182 verbatim
theorem chartEval_coordFrac_j {i j k : Fin 3} (hji : j ≠ i) (l0 l1 : ℂ) :
    chartEval i j k l0 l1 (coordFrac i j) = l0 := by
  rw [chartEval, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    coordFrac_val,
    Localization.awayLift_mk (hv := by rw [MvPolynomial.eval_X, chartEvalPt_i, one_mul]),
    MvPolynomial.eval_X, chartEvalPt_j hji, one_pow, mul_one]


-- @@ L184-189 verbatim
theorem chartEval_coordFrac_k {i j k : Fin 3} (hki : k ≠ i) (hkj : k ≠ j) (l0 l1 : ℂ) :
    chartEval i j k l0 l1 (coordFrac i k) = l1 := by
  rw [chartEval, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    coordFrac_val,
    Localization.awayLift_mk (hv := by rw [MvPolynomial.eval_X, chartEvalPt_i, one_mul]),
    MvPolynomial.eval_X, chartEvalPt_k hki hkj, one_pow, mul_one]


-- @@ L191-191 verbatim
/-! ## Part 1(d). Injectivity — genuine two-variable funext (B1.4) -/


-- @@ L193-223 verbatim
theorem chartPolyHom_injective {i j k : Fin 3} (hji : j ≠ i) (hki : k ≠ i)
    (hkj : k ≠ j) : Function.Injective (chartPolyHom i j k) := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  have key : ∀ l0 l1 : ℂ, MvPolynomial.eval (![l0, l1]) p = 0 := by
    intro l0 l1
    have hcomp : (chartEval i j k l0 l1).comp (chartPolyHom i j k).toRingHom =
        MvPolynomial.eval (![l0, l1]) := by
      apply MvPolynomial.ringHom_ext
      · intro c
        rw [RingHom.comp_apply]
        show chartEval i j k l0 l1 (chartPolyHom i j k (MvPolynomial.C c)) = _
        rw [chartPolyHom_C, chartEval_algebraMap, MvPolynomial.eval_C]
      · intro v
        rw [RingHom.comp_apply]
        fin_cases v
        · show chartEval i j k l0 l1 (chartPolyHom i j k (MvPolynomial.X 0)) = _
          rw [chartPolyHom_X0, chartEval_coordFrac_j hji, MvPolynomial.eval_X]; rfl
        · show chartEval i j k l0 l1 (chartPolyHom i j k (MvPolynomial.X 1)) = _
          rw [chartPolyHom_X1, chartEval_coordFrac_k hki hkj, MvPolynomial.eval_X]; rfl
    have := DFunLike.congr_fun hcomp p
    rw [RingHom.comp_apply] at this
    show MvPolynomial.eval (![l0, l1]) p = 0
    rw [← this]
    show chartEval i j k l0 l1 (chartPolyHom i j k p) = 0
    rw [hp, map_zero]
  apply MvPolynomial.funext (R := ℂ)
  intro x
  rw [map_zero]
  have hx : x = ![x 0, x 1] := by funext v; fin_cases v <;> rfl
  rw [hx]; exact key (x 0) (x 1)


-- @@ L225-225 verbatim
/-! ## Part 1(e). Three-index surjectivity (B1.5, B1.6) -/


-- @@ L227-240 verbatim
theorem adjoin_range_X_eq_top :
    Algebra.adjoin (𝒜₃ 0)
      (Set.range (MvPolynomial.X : Fin 3 → MvPolynomial (Fin 3) ℂ)) = ⊤ := by
  rw [eq_top_iff]
  intro a _
  have ha : a ∈ Algebra.adjoin ℂ
      (Set.range (MvPolynomial.X : Fin 3 → MvPolynomial (Fin 3) ℂ)) := by
    rw [MvPolynomial.adjoin_range_X]; trivial
  have hle : Algebra.adjoin ℂ
      (Set.range (MvPolynomial.X : Fin 3 → MvPolynomial (Fin 3) ℂ)) ≤
      Subalgebra.restrictScalars ℂ (Algebra.adjoin (𝒜₃ 0)
        (Set.range (MvPolynomial.X : Fin 3 → MvPolynomial (Fin 3) ℂ))) :=
    Algebra.adjoin_le fun s hs => Algebra.subset_adjoin hs
  exact (Subalgebra.mem_restrictScalars ℂ).mp (hle ha)


-- @@ L242-247 verbatim
/-- The three distinct indices exhaust `Fin 3`. -/
theorem triple_univ {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ({i, j, k} : Finset (Fin 3)) = Finset.univ := by
  apply Finset.eq_univ_of_card
  rw [Fintype.card_fin, Finset.card_insert_of_notMem (by simp [hij, hik]),
    Finset.card_insert_of_notMem (by simp [hjk]), Finset.card_singleton]


-- @@ L249-254 verbatim
/-- Triple-sum decomposition over the exhausting index set. -/
theorem sum_triple {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (g : Fin 3 → ℕ) : (∑ m, g m) = g i + g j + g k := by
  rw [← triple_univ hij hik hjk,
    Finset.sum_insert (by simp [hij, hik]), Finset.sum_insert (by simp [hjk]),
    Finset.sum_singleton, add_assoc]


-- @@ L256-261 verbatim
/-- Triple-product decomposition over the exhausting index set. -/
theorem prod_triple {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (g : Fin 3 → MvPolynomial (Fin 3) ℂ) : (∏ m, g m) = g i * g j * g k := by
  rw [← triple_univ hij hik hjk,
    Finset.prod_insert (by simp [hij, hik]), Finset.prod_insert (by simp [hjk]),
    Finset.prod_singleton, mul_assoc]


-- @@ L263-302 verbatim
theorem chartPolyHom_surjective {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) : Function.Surjective (chartPolyHom i j k) := by
  intro x
  have htop := HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
    (𝒜 := 𝒜₃) (X_mem_grade_one i) (Fin 3) MvPolynomial.X adjoin_range_X_eq_top
    (fun _ => 1) (fun m => X_mem_grade_one m)
  have hx := htop.ge (Algebra.mem_top (x := x))
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨a, ai, hai, -, rfl⟩ := hy
    have hsum : ai i + ai j + ai k = a := by
      have h3 : (∑ m, ai m) = a := by simpa using hai
      rw [← h3, sum_triple hij hik hjk]
    subst hsum
    refine ⟨MvPolynomial.X 0 ^ ai j * MvPolynomial.X 1 ^ ai k, ?_⟩
    apply HomogeneousLocalization.val_injective
    rw [map_mul, map_pow, map_pow, chartPolyHom_X0, chartPolyHom_X1,
      HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
      HomogeneousLocalization.val_pow, coordFrac_val, coordFrac_val,
      Localization.mk_pow, Localization.mk_pow, Localization.mk_mul,
      HomogeneousLocalization.Away.val_mk,
      Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    use 1
    have hprod : (∏ m, MvPolynomial.X m ^ ai m : MvPolynomial (Fin 3) ℂ) =
        MvPolynomial.X i ^ ai i * MvPolynomial.X j ^ ai j * MvPolynomial.X k ^ ai k :=
      prod_triple hij hik hjk (fun m => MvPolynomial.X m ^ ai m)
    simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul, SubmonoidClass.coe_pow,
      hprod]
    ring
  | algebraMap r =>
    obtain ⟨c, rfl⟩ := gradeZero_algebraMap_bijective.2 r
    exact ⟨MvPolynomial.C c,
      (chartPolyHom_C i j k c).trans
        (IsScalarTower.algebraMap_apply ℂ (𝒜₃ 0) (Away 𝒜₃ (MvPolynomial.X i)) c)⟩
  | add y z _ _ hy hz =>
    obtain ⟨p, rfl⟩ := hy; obtain ⟨q, rfl⟩ := hz
    exact ⟨p + q, map_add _ _ _⟩
  | mul y z _ _ hy hz =>
    obtain ⟨p, rfl⟩ := hy; obtain ⟨q, rfl⟩ := hz
    exact ⟨p * q, map_mul _ _ _⟩


-- @@ L304-304 verbatim
/-! ## Part 1(f). The chart isomorphism (B1.7 — the B1 headline) -/


-- @@ L306-309 verbatim
def polyChartEquiv (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    MvPolynomial (Fin 2) ℂ ≃ₐ[ℂ] Away 𝒜₃ (MvPolynomial.X i) :=
  AlgEquiv.ofBijective (chartPolyHom i j k)
    ⟨chartPolyHom_injective hij.symm hik.symm hjk.symm, chartPolyHom_surjective hij hik hjk⟩


-- @@ L311-313 verbatim
theorem polyChartEquiv_apply (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (p : MvPolynomial (Fin 2) ℂ) : polyChartEquiv i j k hij hik hjk p = chartPolyHom i j k p :=
  rfl


-- @@ L315-318 verbatim
/-- **B1.7 (generic chart)**: `Away 𝒜₃ Xᵢ ≃ₐ[ℂ] ℂ[s,t]`. -/
def chartPolyEquiv (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Away 𝒜₃ (MvPolynomial.X i) ≃ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  (polyChartEquiv i j k hij hik hjk).symm


-- @@ L320-324 verbatim
/-- **B1.7 headline**: `Away 𝒜₃ X₀ ≃ₐ[ℂ] ℂ[s,t]` — EXACTLY the spelling that
`PlaneLineHomology`'s `LineDataDistinct` was parked on (plh_design §5). -/
def awayXZeroPolyEquiv :
    Away 𝒜₃ (MvPolynomial.X 0) ≃ₐ[ℂ] MvPolynomial (Fin 2) ℂ :=
  chartPolyEquiv 0 1 2 (by decide) (by decide) (by decide)


-- @@ L326-331 verbatim
/-- Distinctness-discharge receipt: the chart iso lands at the exact type the
parked `LineDataDistinct` input requires (`Away 𝒜₃ X₀ ≅ ℂ[s,t]`). -/
theorem awayXZeroPolyEquiv_spelling :
    (awayXZeroPolyEquiv :
      Away 𝒜₃ (MvPolynomial.X 0) ≃ₐ[ℂ] MvPolynomial (Fin 2) ℂ) = awayXZeroPolyEquiv :=
  rfl


-- @@ L333-333 verbatim
/-! ## Part 1(g). Units of the chart rings are constants (distinctness bridge) -/


-- @@ L335-353 verbatim
/-- **The distinctness-discharge tool** (`ProjectiveLineUnits.away_unit_eq_algebraMap`
one variable up): every unit of a plane chart ring is a constant.  This is the
exact chart-ring unit analysis `plh_design §5` said was blocked on the chart
iso; it is the last shipped-machinery step before `divOf p2 lineRatio ≠ 0`. -/
theorem away_unit_eq_algebraMap {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k)
    (hjk : j ≠ k) (u : (Away 𝒜₃ (MvPolynomial.X i))ˣ) :
    ∃ c : ℂˣ, (u : Away 𝒜₃ (MvPolynomial.X i)) =
      algebraMap ℂ (Away 𝒜₃ (MvPolynomial.X i)) c := by
  obtain ⟨c, hc, hCc⟩ :=
    (MvPolynomial.isUnit_iff_eq_C_of_isReduced
      (P := chartPolyEquiv i j k hij hik hjk (u : Away 𝒜₃ (MvPolynomial.X i)))).mp
      (u.isUnit.map (chartPolyEquiv i j k hij hik hjk))
  have h2 : (u : Away 𝒜₃ (MvPolynomial.X i)) =
      (chartPolyEquiv i j k hij hik hjk).symm (MvPolynomial.C c) := by
    rw [← hCc, AlgEquiv.symm_apply_apply]
  have h3 : (chartPolyEquiv i j k hij hik hjk).symm (MvPolynomial.C c) =
      algebraMap ℂ (Away 𝒜₃ (MvPolynomial.X i)) c := by
    rw [← MvPolynomial.algebraMap_eq]; exact AlgEquiv.commutes _ c
  exact ⟨hc.unit, by rw [IsUnit.unit_spec]; exact h2.trans h3⟩


-- @@ L355-355 verbatim
/-! ## Part 2. Chart sections and the constants receipt (B1.8–B1.9) -/


-- @@ L357-359 verbatim
/-- The chart `D₊(Xᵢ)` of `ℙ²` (definitionally `ProjectivePlane.chart i`;
inlined as `Proj.basicOpen` to match the `CalibrationDegreeFour` spelling). -/
abbrev chartOpen (i : Fin 3) : p2.Opens := Proj.basicOpen 𝒜₃ (MvPolynomial.X i)


-- @@ L361-364 verbatim
/-- B1.8: the chart-ring-to-sections map (`Proj.awayToSection`). -/
def awaySection (f : MvPolynomial (Fin 3) ℂ) :
    Away 𝒜₃ f →+* Γ(p2, Proj.basicOpen 𝒜₃ f) :=
  (Proj.awayToSection 𝒜₃ f).hom


-- @@ L366-368 verbatim
theorem isIso_awayToSection {f : MvPolynomial (Fin 3) ℂ} {m : ℕ}
    (hf : f ∈ 𝒜₃ m) (hm : 0 < m) : IsIso (Proj.awayToSection 𝒜₃ f) := by
  rw [← Proj.basicOpenIsoAway_hom 𝒜₃ f hf hm]; infer_instance


-- @@ L370-373 verbatim
theorem awaySection_injective {f : MvPolynomial (Fin 3) ℂ} {m : ℕ}
    (hf : f ∈ 𝒜₃ m) (hm : 0 < m) : Function.Injective (awaySection f) := by
  haveI := isIso_awayToSection hf hm
  exact (ConcreteCategory.bijective_of_isIso (Proj.awayToSection 𝒜₃ f)).injective


-- @@ L375-381 verbatim
/-- B1.9(a). -/
theorem gradeZero_fromZero_eq_algebraMap (i : Fin 3) :
    gradeZeroEquiv.toCommRingCatIso.hom ≫
      CommRingCat.ofHom
        (fromZeroRingHom 𝒜₃ (Submonoid.powers (MvPolynomial.X i))) =
    CommRingCat.ofHom (algebraMap ℂ (Away 𝒜₃ (MvPolynomial.X i))) := by
  ext c; rfl


-- @@ L383-395 verbatim
/-- B1.9(b): the ΓSpecIso-naturality chase (probe-verified). -/
theorem constants_awayι (i : Fin 3) :
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ structMor.appTop) ≫
      (Proj.awayι 𝒜₃ (MvPolynomial.X i) (X_mem_grade_one i) one_pos).appTop =
    CommRingCat.ofHom (algebraMap ℂ (Away 𝒜₃ (MvPolynomial.X i))) ≫
      (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜₃ (MvPolynomial.X i)))).inv := by
  have hs : structMor =
      Proj.toSpecZero 𝒜₃ ≫ Spec.map (gradeZeroEquiv.toCommRingCatIso.hom) := rfl
  rw [hs, Scheme.Hom.comp_appTop, Category.assoc, Category.assoc,
    ← Scheme.Hom.comp_appTop, Proj.awayι_toSpecZero, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, ← Category.assoc,
    gradeZero_fromZero_eq_algebraMap]


-- @@ L397-402 verbatim
theorem chart_ι_appTop_topIso (i : Fin 3) :
    (chartOpen i).ι.appTop ≫ (chartOpen i).topIso.hom =
      p2.presheaf.map (homOfLE (le_top : chartOpen i ≤ ⊤)).op := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  exact (p2.presheaf.map_comp _ _).symm.trans
    (congrArg p2.presheaf.map (Subsingleton.elim _ _))


-- @@ L404-409 verbatim
theorem awayι_appTop (i : Fin 3) :
    (Proj.awayι 𝒜₃ (MvPolynomial.X i) (X_mem_grade_one i) one_pos).appTop =
      (chartOpen i).ι.appTop ≫
        (Proj.basicOpenIsoSpec 𝒜₃ (MvPolynomial.X i)
          (X_mem_grade_one i) one_pos).inv.appTop := by
  rw [← Scheme.Hom.comp_appTop]; rfl


-- @@ L411-418 verbatim
theorem basicOpenIsoSpec_hom_appTop (i : Fin 3) :
    (Proj.basicOpenIsoSpec 𝒜₃ (MvPolynomial.X i)
        (X_mem_grade_one i) one_pos).hom.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜₃ (MvPolynomial.X i)))).hom ≫
        Proj.awayToSection 𝒜₃ (MvPolynomial.X i) ≫
        (chartOpen i).topIso.inv := by
  rw [Proj.basicOpenIsoSpec_hom]
  exact Proj.basicOpenToSpec_app_top 𝒜₃ (MvPolynomial.X i)


-- @@ L420-435 verbatim
theorem constants_section_hom (i : Fin 3) :
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ structMor.appTop) ≫
      p2.presheaf.map (homOfLE (le_top : chartOpen i ≤ ⊤)).op =
    CommRingCat.ofHom (algebraMap ℂ (Away 𝒜₃ (MvPolynomial.X i))) ≫
      Proj.awayToSection 𝒜₃ (MvPolynomial.X i) := by
  have hι : (chartOpen i).ι.appTop =
      (Proj.awayι 𝒜₃ (MvPolynomial.X i) (X_mem_grade_one i) one_pos).appTop ≫
        (Proj.basicOpenIsoSpec 𝒜₃ (MvPolynomial.X i)
          (X_mem_grade_one i) one_pos).hom.appTop := by
    rw [awayι_appTop, Category.assoc, ← Scheme.Hom.comp_appTop,
      Iso.hom_inv_id, Scheme.Hom.id_appTop, Category.comp_id]
  rw [← chart_ι_appTop_topIso, hι, basicOpenIsoSpec_hom_appTop]
  simp only [← Category.assoc]
  rw [constants_awayι]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]


-- @@ L437-448 verbatim
/-- **B1.9 (constants receipt, elementwise)**: the `Sec`-algebra constants of
`cRingHom structMor` restrict on each chart to the `instAlgebraAwayC` constants
along `awaySection`. -/
theorem constants_receipt (i : Fin 3) (c : ℂ) :
    res (cRingHom structMor) (le_top : chartOpen i ≤ ⊤) (cRingHom structMor c) =
      awaySection (MvPolynomial.X i)
        (algebraMap ℂ (Away 𝒜₃ (MvPolynomial.X i)) c) := by
  have h1 : res (cRingHom structMor) (le_top : chartOpen i ≤ ⊤)
      (cRingHom structMor c) =
      (((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ structMor.appTop) ≫
        p2.presheaf.map (homOfLE (le_top : chartOpen i ≤ ⊤)).op).hom c := rfl
  rw [h1, constants_section_hom]; rfl


-- @@ L450-451 verbatim
/-! ## Part 3. The chart seed (B1.10–B1.12): two-generated `ℂ`-algebras,
de Rham terms dead in degrees ≥3 -/


-- @@ L453-457 verbatim
/-- B1.10. -/
def awaySectionAlgHom (i : Fin 3) :
    Away 𝒜₃ (MvPolynomial.X i) →ₐ[ℂ] Sec (cRingHom structMor) (chartOpen i) where
  toRingHom := awaySection (MvPolynomial.X i)
  commutes' c := (constants_receipt i c).symm


-- @@ L459-463 verbatim
theorem awaySectionAlgHom_surjective (i : Fin 3) :
    Function.Surjective (awaySectionAlgHom i) := by
  haveI := isIso_awayToSection (X_mem_grade_one i) one_pos
  exact (ConcreteCategory.bijective_of_isIso
    (Proj.awayToSection 𝒜₃ (MvPolynomial.X i))).surjective


-- @@ L465-468 verbatim
/-- B1.10: the chart section ring presented as `ℂ[s,t]` image (PAIR generators). -/
def chartPoly (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    MvPolynomial (Fin 2) ℂ →ₐ[ℂ] Sec (cRingHom structMor) (chartOpen i) :=
  (awaySectionAlgHom i).comp (chartPolyEquiv i j k hij hik hjk).symm.toAlgHom


-- @@ L470-472 verbatim
theorem chartPoly_surjective (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Function.Surjective (chartPoly i j k hij hik hjk) :=
  (awaySectionAlgHom_surjective i).comp (chartPolyEquiv i j k hij hik hjk).symm.surjective


-- @@ L474-502 verbatim
/-- **B1.11**: the chart section rings are TWO-generated `ℂ`-algebras (by the
images of the two coordinate variables). -/
theorem adjoin_chartGen (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Algebra.adjoin ℂ
      ({chartPoly i j k hij hik hjk (MvPolynomial.X 0),
        chartPoly i j k hij hik hjk (MvPolynomial.X 1)} :
        Set (Sec (cRingHom structMor) (chartOpen i))) = ⊤ := by
  have himg : (chartPoly i j k hij hik hjk '' Set.range (MvPolynomial.X : Fin 2 → _)) =
      ({chartPoly i j k hij hik hjk (MvPolynomial.X 0),
        chartPoly i j k hij hik hjk (MvPolynomial.X 1)} :
        Set (Sec (cRingHom structMor) (chartOpen i))) := by
    rw [← Set.range_comp]
    ext y
    simp only [Set.mem_range, Function.comp, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨v, rfl⟩; fin_cases v
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  have h3 : Subalgebra.map (chartPoly i j k hij hik hjk)
      (Algebra.adjoin ℂ (Set.range (MvPolynomial.X : Fin 2 → _))) =
      Algebra.adjoin ℂ
        (chartPoly i j k hij hik hjk '' Set.range (MvPolynomial.X : Fin 2 → _)) :=
    AlgHom.map_adjoin _ _
  rw [MvPolynomial.adjoin_range_X, Algebra.map_top,
    (AlgHom.range_eq_top _).mpr (chartPoly_surjective i j k hij hik hjk), himg] at h3
  exact h3.symm


-- @@ L504-510 verbatim
/-- **B1.12 (the seed the bridge consumes)**: the chart de Rham terms vanish in
degrees `≥ 3` — the PAIR-collapse (`PlaneCarrierProbe.subsingleton_DR_of_adjoin_pair`)
applied to the two-generated chart section ring. -/
theorem subsingleton_DR_chart (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {p : ℕ} (hp : 3 ≤ p) :
    Subsingleton (DeRham.DR ℂ (Sec (cRingHom structMor) (chartOpen i)) p) :=
  PlaneCarrierProbe.subsingleton_DR_of_adjoin_pair (adjoin_chartGen i j k hij hik hjk) hp


-- @@ L512-512 verbatim
end ProjectivePlaneChart

-- @@ L513-513 verbatim
end HodgePilot

-- @@ L514-514 verbatim
end
