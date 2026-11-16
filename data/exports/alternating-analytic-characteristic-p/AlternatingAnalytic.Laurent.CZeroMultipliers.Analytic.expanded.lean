import AlternatingAnalytic.Laurent.CZeroMultipliers.NoLift


-- @@ L3-11 verbatim
/-!
# Nowhere analyticity of precomposition with multipliers on a `c₀` base

The second and third assertions of Proposition C.6. If `x ↦ w ∘ (u₀ + D x, …, u₀ + D x)` has a
power series at some point, then along every line its value is a polynomial whose top coefficient
is `w ∘ (D h, …, D h)`, so the degree-`n` term of the series is a bounded `n`-linear lift of
`h ↦ w ∘ (D h, …, D h)`. For the Laurent pair and coordinatewise multipliers on `c₀(ℕ, K₁)` no
such lift exists, so `a ↦ A(u₀ + D_a)(W_B)` and `a ↦ A(u₀ + D_a)` are analytic nowhere.
-/


-- @@ L13-13 verbatim
noncomputable section

-- @@ L14-14 verbatim
set_option backward.isDefEq.respectTransparency false

-- @@ L15-15 verbatim
open Filter Topology Module

-- @@ L16-16 verbatim
open scoped NNReal BoundedContinuousFunction ZeroAtInfty


-- @@ L18-18 verbatim
namespace AlternatingAnalytic


-- @@ L20-20 verbatim
section General


-- @@ L22-26 verbatim
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {X : Type*} [NormedAddCommGroup X] [NormedSpace 𝕜 X]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {ι : Type*} [Fintype ι]


-- @@ L28-61 verbatim
/-- The `n`-th term of a power series of `x ↦ w ∘ (u₀ + D x, …)` is a lift of
`h ↦ w ∘ (D h, …, D h)`, where `n` is the degree of `w`. -/
theorem precompAffine_coeff_eq_of_hasFPowerSeriesAt (n : ℕ) (hn : Fintype.card ι = n)
    (D : X →ₗ[𝕜] (E →L[𝕜] E)) (u₀ : E →L[𝕜] E) (w : E [⋀^ι]→L[𝕜] F)
    {p : FormalMultilinearSeries 𝕜 X (E [⋀^ι]→L[𝕜] F)} {x₀ : X}
    (hp : HasFPowerSeriesAt (fun x => w.compContinuousLinearMap (u₀ + D x)) p x₀) (h : X) :
    p n (fun _ => h) = w.compContinuousLinearMap (D h) := by
  classical
  subst hn
  let Amb : ContinuousMultilinearMap 𝕜 (fun _ : ι => E →L[𝕜] E)
      (ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F) :=
    (ContinuousLinearMap.apply 𝕜 _ w.toContinuousMultilinearMap).compContinuousMultilinearMap
      (ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear 𝕜
        (fun _ : ι => E) (fun _ : ι => E) F)
  have hAmb : ∀ f : E →L[𝕜] E, Amb (fun _ => f) =
      (w.compContinuousLinearMap f).toContinuousMultilinearMap := fun f => by
    ext x
    rfl
  let j : (E [⋀^ι]→L[𝕜] F) →L[𝕜] ContinuousMultilinearMap 𝕜 (fun _ : ι => E) F :=
    ContinuousAlternatingMap.toContinuousMultilinearMapCLM 𝕜
  have hj : Function.Injective j := ContinuousAlternatingMap.toContinuousMultilinearMap_injective
  refine LiftCriterion.coeff_eq_of_ambient (𝕜 := 𝕜)
    (fun x => w.compContinuousLinearMap (u₀ + D x)) x₀ (Fintype.card ι)
    (fun r x => LiftCriterion.lineCoeff Amb (u₀ + D x₀) r (D x)) j hj
    (fun x => w.compContinuousLinearMap (D x)) ?_ ?_ p hp h
  · intro t x
    have hline : u₀ + D (x₀ + t • x) = (u₀ + D x₀) + t • D x := by
      rw [map_add, map_smul, add_assoc]
    change (w.compContinuousLinearMap (u₀ + D (x₀ + t • x))).toContinuousMultilinearMap = _
    rw [hline, ← hAmb]
    exact LiftCriterion.map_diag_add_smul Amb (u₀ + D x₀) (D x) t
  · intro x
    rw [LiftCriterion.lineCoeff_card, hAmb]
    rfl


-- @@ L63-69 verbatim
/-- Evaluating an analytic family of operators on forms at a fixed form is analytic. -/
theorem analyticAt_apply_of_analyticAt {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
    (w : E' [⋀^ι]→L[𝕜] F) {f : X → (E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)} {x₀ : X}
    (hf : AnalyticAt 𝕜 f x₀) : AnalyticAt 𝕜 (fun x => f x w) x₀ := by
  let ev : ((E' [⋀^ι]→L[𝕜] F) →L[𝕜] (E [⋀^ι]→L[𝕜] F)) →L[𝕜] (E [⋀^ι]→L[𝕜] F) :=
    ContinuousLinearMap.apply 𝕜 _ w
  exact (ev.analyticAt _).comp hf


-- @@ L71-71 verbatim
end General


-- @@ L73-73 verbatim
variable (κ : Type*) [Field κ] (r : ℝ≥0) [Fact (0 < r)] [Fact (r < 1)] (k : ℕ)


-- @@ L75-75 verbatim
local notation "K" => LaurentField κ r

-- @@ L76-76 verbatim
local notation "E" => (ℕ →ᵇ LaurentField κ r)


-- @@ L78-86 verbatim
/-- Coordinatewise multiplication by a null sequence, as a linear map into operators. -/
def czeroMultiplier : C₀(ℕ, LaurentField κ r) →ₗ[K] (E →L[K] E) where
  toFun a := ContinuousLinearMap.mul K E a.toBCF
  map_add' a b := by
    rw [← map_add]
    rfl
  map_smul' c a := by
    rw [← map_smul]
    rfl


-- @@ L88-99 verbatim
/-- For every `u₀`, `a ↦ A(u₀ + D_a)(W_B)` is analytic at no point of `c₀(ℕ, K₁)`
(Proposition C.6). -/
theorem czero_not_analyticAt_precomp_wedge [Finite κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (hpk : p ≤ k) (u₀ : E →L[K] E) (a₀ : C₀(ℕ, LaurentField κ r)) :
    ¬ AnalyticAt K
      (fun a : C₀(ℕ, LaurentField κ r) =>
        ContinuousAlternatingMap.compContinuousLinearMapCLM
          (u₀ + ContinuousLinearMap.mul K E a.toBCF) (completedExteriorWedge K ℕ k)) a₀ := by
  rintro ⟨q, hq⟩
  exact czero_not_exists_multiplierLift κ r k p hpk
    ⟨q k, precompAffine_coeff_eq_of_hasFPowerSeriesAt k (Fintype.card_fin k)
      (czeroMultiplier κ r) u₀ (completedExteriorWedge K ℕ k) hq⟩


-- @@ L101-112 verbatim
/-- For every `u₀`, `a ↦ A(u₀ + D_a)` is analytic at no point of `c₀(ℕ, K₁)` (Proposition C.6). -/
theorem czero_not_analyticAt_precomp [Finite κ] (p : ℕ) [Fact p.Prime] [CharP κ p]
    (hpk : p ≤ k) (u₀ : E →L[K] E) (a₀ : C₀(ℕ, LaurentField κ r)) :
    ¬ AnalyticAt K
      (fun a : C₀(ℕ, LaurentField κ r) =>
        (ContinuousAlternatingMap.compContinuousLinearMapCLM
          (u₀ + ContinuousLinearMap.mul K E a.toBCF) :
          (E [⋀^Fin k]→L[K] ProjectiveExteriorCompletion K ℕ k) →L[K]
            (E [⋀^Fin k]→L[K] ProjectiveExteriorCompletion K ℕ k))) a₀ := by
  intro h
  exact czero_not_analyticAt_precomp_wedge κ r k p hpk u₀ a₀
    (analyticAt_apply_of_analyticAt (completedExteriorWedge K ℕ k) h)


-- @@ L114-114 verbatim
end AlternatingAnalytic
