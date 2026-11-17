import Mathlib

-- Lean 4.33 makes several bundled additive and tangent-space instances non-reducible.  The
-- compatibility mode keeps the pre-4.33 definitional equalities used throughout this development.

-- @@ L5-5 verbatim
set_option backward.isDefEq.respectTransparency false

-- @@ L6-6 verbatim
set_option backward.isDefEq.respectTransparency.types false


-- @@ L8-11 verbatim
/-!
# Proofs of the smooth Loewner and Carathéodory counterexamples

-/


-- @@ L13-13 verbatim
scoped[EuclideanGeometry] notation "ℝ³" => EuclideanSpace ℝ (Fin 3)


-- @@ L15-15 verbatim
open scoped EuclideanGeometry

-- @@ L16-16 verbatim
open Matrix


-- @@ L18-19 expanded
noncomputable instance Module.orientedEuclideanSpaceFinThree :
    Module.Oriented ℝ (EuclideanSpace ℝ (Fin 3)) (Fin 3) :=
  ⟨Basis.orientation <| PiLp.basisFun ..⟩


-- @@ L21-21 verbatim
namespace EuclideanHypersurface


-- @@ L23-27 expanded
noncomputable def euclideanCross :
    EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  let e := WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)
  let f := ((crossProduct.comp e.toLinearMap).compl₂ e.toLinearMap).compr₂ e.symm.toLinearMap
  LinearMap.toContinuousLinearMap (LinearMap.toContinuousLinearMap.toLinearMap.comp f)


-- @@ L29-29 verbatim
open Set Metric

-- @@ L30-30 verbatim
open scoped ContDiff EuclideanSpace Manifold RealInnerProductSpace


-- @@ L32-33 verbatim
variable {V E : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]


-- @@ L35-36 verbatim
noncomputable def firstFundamentalFormAt (dF : V →L[ℝ] E) : LinearMap.BilinForm ℝ V :=
  LinearMap.BilinForm.comp (innerₗ E) dF.toLinearMap dF.toLinearMap


-- @@ L38-40 verbatim
noncomputable def secondFundamentalFormAt (dn dF : V →L[ℝ] E) :
    LinearMap.BilinForm ℝ V :=
  -(LinearMap.BilinForm.comp (innerₗ E) dn.toLinearMap dF.toLinearMap)


-- @@ L42-44 verbatim
def IsUmbilic (V E : Type*) [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (dF dn : V →L[ℝ] E) : Prop :=
  ∃ κ : ℝ, secondFundamentalFormAt dn dF = κ • firstFundamentalFormAt dF


-- @@ L46-49 expanded
noncomputable def sphereTangentBasis (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Module.Basis (Fin 2) ℝ (TangentSpace (𝓡 2) p) :=
  (trivializationAt (EuclideanSpace ℝ (Fin 2)) (TangentSpace (𝓡 2)) p).basisAt
    (PiLp.basisFun 2 ℝ (Fin 2)) (FiberBundle.mem_baseSet_trivializationAt' p)


-- @@ L51-58 expanded
noncomputable def sphereNormalRaw
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3) :=
  let b := sphereTangentBasis p
  let dι : TangentSpace (𝓡 2) p →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mvfderiv (𝓡 2)
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
  let dF : TangentSpace (𝓡 2) p →L[ℝ] EuclideanSpace ℝ (Fin 3) := mvfderiv (𝓡 2) F p
  inner ℝ (euclideanCross (dι (b 0)) (dι (b 1))) (p : EuclideanSpace ℝ (Fin 3)) •
    euclideanCross (dF (b 0)) (dF (b 1))


-- @@ L60-62 expanded
noncomputable def sphereNormal
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : EuclideanSpace ℝ (Fin 3) :=
  NormedSpace.normalize (sphereNormalRaw F p)


-- @@ L64-64 verbatim
end EuclideanHypersurface


-- @@ L66-66 verbatim
open Set Metric

-- @@ L67-67 verbatim
open scoped ContDiff EuclideanSpace Manifold RealInnerProductSpace


-- @@ L69-69 verbatim
namespace LoewnerConjecture


-- @@ L71-75 verbatim
/-- The trace-free Hessian of `f : ℂ → ℝ`, encoded so its argument is twice the principal-line
angle. Its zeros are exactly the points where the Hessian has a repeated eigenvalue. -/
noncomputable def traceFreeHessian (f : ℂ → ℝ) (z : ℂ) : ℂ :=
  let H := iteratedFDeriv ℝ 2 f z
  H ![1, 1] - H ![Complex.I, Complex.I] + 2 * H ![1, Complex.I] * Complex.I


-- @@ L77-89 verbatim
/-- A complex-valued function `q` has an isolated zero at `z` with winding number `m`.

Continuity on the witness ball makes the winding number independent of the sufficiently small
circle; `θ` is an argument lift on one such circle. For a trace-free Hessian, the principal-line
index is `m / 2`. -/
def HasIsolatedZeroIndex (q : ℂ → ℂ) (z : ℂ) (m : ℤ) : Prop :=
  ∃ ε > 0,
    ContinuousOn q (ball z ε) ∧ q z = 0 ∧
      (∀ w, w ≠ z → dist w z < ε → q w ≠ 0) ∧
      ∃ r, 0 < r ∧ r < ε ∧ ∃ θ : ℝ → ℝ, Continuous θ ∧
        (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
          NormedSpace.normalize (q (z + r * Complex.exp ((t : ℂ) * Complex.I)))) ∧
        θ (2 * Real.pi) - θ 0 = 2 * Real.pi * m


-- @@ L91-95 verbatim
/-- Loewner's conjecture for functions of class `C^k` near an isolated umbilic. The integer `m`
is twice the principal-line index, so the bound `m ≤ 2` says that this index is at most one. -/
def LoewnerConjectureOfClass (k : WithTop ℕ∞) : Prop :=
  ∀ (f : ℂ → ℝ) (z : ℂ) (m : ℤ), ContDiffAt ℝ k f z →
    HasIsolatedZeroIndex (traceFreeHessian f) z m → m ≤ 2


-- @@ L97-97 verbatim
end LoewnerConjecture


-- @@ L99-99 verbatim
namespace CaratheodoryConjecture


-- @@ L101-106 expanded
def IsConvexSphereOfClass (k : WithTop ℕ∞)
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3)) : Prop :=
  ContMDiff (𝓡 2) (𝓡 3) (k + 1) F ∧
    Topology.IsEmbedding F ∧
      (∀ p, Function.Injective (mvfderiv (𝓡 2) F p)) ∧
        ∃ K : ConvexBody (EuclideanSpace ℝ (Fin 3)),
          (interior (K : Set (EuclideanSpace ℝ (Fin 3)))).Nonempty ∧
            range F = frontier (K : Set (EuclideanSpace ℝ (Fin 3)))


-- @@ L108-116 expanded
def CaratheodoryConjectureOfClass (k : WithTop ℕ∞) : Prop :=
  ∀ F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3),
    IsConvexSphereOfClass k F →
      ∃ p₁ p₂,
        p₁ ≠ p₂ ∧
          EuclideanHypersurface.IsUmbilic (TangentSpace (𝓡 2) p₁) (EuclideanSpace ℝ (Fin 3))
              (mvfderiv (𝓡 2) F p₁) (mvfderiv (𝓡 2) (EuclideanHypersurface.sphereNormal F) p₁) ∧
            EuclideanHypersurface.IsUmbilic (TangentSpace (𝓡 2) p₂) (EuclideanSpace ℝ (Fin 3))
              (mvfderiv (𝓡 2) F p₂) (mvfderiv (𝓡 2) (EuclideanHypersurface.sphereNormal F) p₂)


-- @@ L118-118 verbatim
end CaratheodoryConjecture


-- @@ L120-120 verbatim
/-! ## Flattened from `FormalConjecturesForMathlib/Analysis/SpecialFunctions/FlatRpowExp.lean` -/


-- @@ L122-122 verbatim
section FlatRpowExpSection


-- @@ L124-124 verbatim
noncomputable section


-- @@ L126-126 verbatim
open Filter Function Topology


-- @@ L128-128 verbatim
namespace ContDiff


-- @@ L130-132 verbatim
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]


-- @@ L134-190 verbatim
/-- A smooth function on the punctured space whose every iterated derivative is little-oh of the
distance to the origin extends smoothly across the origin, with zero Taylor series there. -/
theorem at_zero_of_iteratedFDeriv_isLittleO {f : E → F}
    (hf : ∀ x ≠ 0, ContDiffAt 𝕜 ∞ f x) (hzero : f 0 = 0)
    (hflat : ∀ m : ℕ, (iteratedFDeriv 𝕜 m f) =o[𝓝[≠] 0] (id : E → E)) :
    ContDiffAt 𝕜 ∞ f 0 := by
  classical
  let p : E → FormalMultilinearSeries 𝕜 E F := fun x m ↦
    if x = 0 then 0 else iteratedFDeriv 𝕜 m f x
  have hp_flat (m : ℕ) : (fun x ↦ p x m) =o[𝓝 0] (id : E → E) := by
    have heq : iteratedFDeriv 𝕜 m f =ᶠ[𝓝[≠] 0] fun x ↦ p x m := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
      simp [p, hx]
    rw [← nhdsNE_sup_pure (0 : E)]
    refine ((hflat m).congr' heq EventuallyEq.rfl).sup <|
      Asymptotics.isLittleO_iff.2 fun c hc ↦ ?_
    rw [eventually_pure]
    simp [p]
  have hp_deriv (m : ℕ) (x : E) :
      HasFDerivAt (p · m) (p x m.succ).curryLeft x := by
    by_cases hx : x = 0
    · subst x
      rw [hasFDerivAt_iff_isLittleO_nhds_zero]
      have hfun : (fun h : E ↦ p h m - p 0 m - (p 0 m.succ).curryLeft h) =
          fun h ↦ p h m := by
        funext h
        have hp0 (i : ℕ) : p 0 i = 0 := by simp [p]
        rw [hp0 m, hp0 m.succ]
        have hz : (0 : ContinuousMultilinearMap 𝕜 (fun _ : Fin (m + 1) ↦ E) F).curryLeft h =
            0 := by
          ext v
          rfl
        rw [hz, sub_zero, sub_zero]
      simp only [zero_add]
      rw [hfun]
      exact hp_flat m
    · have heq (i : ℕ) : (fun y ↦ p y i) =ᶠ[𝓝 x] iteratedFDeriv 𝕜 i f := by
        filter_upwards [eventually_ne_nhds hx] with y hy
        simp [p, hy]
      have hd := ((hf x hx).differentiableAt_iteratedFDeriv (m := m)
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl m)).hasFDerivAt
      rw [fderiv_iteratedFDeriv, Function.comp_apply] at hd
      refine (hd.congr_of_eventuallyEq (heq m)).congr_fderiv ?_
      simp only [p, hx, if_false, Nat.succ_eq_add_one]
      rfl
  have hp : HasFTaylorSeriesUpToOn ∞ f p Set.univ := by
    rw [hasFTaylorSeriesUpToOn_top_iff' le_rfl]
    constructor
    · intro x _
      by_cases hx : x = 0
      · subst x
        simp [p, hzero]
      · simp [p, hx]
    · intro m x _
      simpa only [hasFDerivWithinAt_univ] using hp_deriv m x
  exact hp.contDiffOn.contDiffAt univ_mem


-- @@ L192-218 verbatim
/-- A smooth function with zero Taylor series at the origin is little-oh of every power of the
distance to the origin. -/
theorem isLittleO_norm_pow_of_iteratedFDeriv_zero [NormedSpace ℝ E] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ ∞ f)
    (hzero : ∀ m : ℕ, iteratedFDeriv ℝ m f 0 = 0) (m n : ℕ) :
    iteratedFDeriv ℝ m f =o[𝓝 0] fun x ↦ ‖x‖ ^ n := by
  induction n generalizing m with
  | zero =>
      rw [show (fun x : E ↦ ‖x‖ ^ 0) = fun _ ↦ (1 : ℝ) by simp]
      rw [Asymptotics.isLittleO_one_iff]
      rw [← hzero m]
      exact hf.continuous_iteratedFDeriv (m := m)
        (ENat.natCast_le_of_coe_top_le_withTop le_rfl m) |>.continuousAt
  | succ n ih =>
      have hdiff : Differentiable ℝ (iteratedFDeriv ℝ m f) :=
        hf.differentiable_iteratedFDeriv
          (ENat.natCast_lt_of_coe_top_le_withTop le_rfl m)
      have hderiv : fderiv ℝ (iteratedFDeriv ℝ m f) =o[𝓝 0] fun x ↦ ‖x‖ ^ n := by
        rw [Asymptotics.isLittleO_iff] at ⊢
        intro c hc
        filter_upwards [(ih (m + 1)).bound hc] with x hx
        rw [norm_fderiv_iteratedFDeriv]
        exact hx
      have h := (convex_univ : Convex ℝ (Set.univ : Set E)).isLittleO_pow_succ
        (Set.mem_univ 0) (fun x _ ↦ hdiff.differentiableAt.hasFDerivAt.hasFDerivWithinAt)
        (by simpa using hderiv)
      simpa [hzero m] using h


-- @@ L220-249 verbatim
/-- Composing on the right preserves a zero Taylor series at the origin, provided the inner
function fixes the origin. -/
theorem iteratedFDeriv_comp_zero_of_outer [NormedSpace ℝ E] [NormedSpace ℝ F]
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {g : F → G} {f : E → F}
    (hg : ContDiff ℝ ∞ g) (hf : ContDiff ℝ ∞ f) (hf0 : f 0 = 0)
    (hzero : ∀ m : ℕ, iteratedFDeriv ℝ m g 0 = 0) (n : ℕ) :
    iteratedFDeriv ℝ n (g ∘ f) 0 = 0 := by
  let D := 1 + ∑ i ∈ Finset.range (n + 1), ‖iteratedFDeriv ℝ i f 0‖
  rw [← norm_eq_zero]
  apply le_antisymm
  · refine (norm_iteratedFDeriv_comp_le hg hf (mod_cast le_top) 0
      (C := 0) (D := D) ?_ ?_).trans ?_
    · intro i hi
      rw [hf0, hzero i]
      simp only [norm_zero]
      exact le_rfl
    · intro i hi hin
      have hD_one : 1 ≤ D := by
        simp only [D, le_add_iff_nonneg_right]
        exact Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
      calc
        ‖iteratedFDeriv ℝ i f 0‖ ≤ D := by
          simp only [D]
          exact le_add_of_nonneg_of_le zero_le_one <|
            Finset.single_le_sum (f := fun j ↦ ‖iteratedFDeriv ℝ j f 0‖)
              (fun j _ ↦ norm_nonneg _)
              (Finset.mem_range.mpr (Nat.lt_succ_of_le hin))
        _ ≤ D ^ i := le_self_pow₀ hD_one (Nat.ne_of_gt hi)
    · simp
  · exact norm_nonneg _


-- @@ L251-265 verbatim
/-- Multiplying a smooth scalar-valued function with zero Taylor series by another smooth
function preserves its zero Taylor series. -/
theorem iteratedFDeriv_mul_zero_of_left [NormedSpace ℝ E] {f g : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hzero : ∀ m : ℕ, iteratedFDeriv ℝ m f 0 = 0) (n : ℕ) :
    iteratedFDeriv ℝ n (fun x ↦ f x * g x) 0 = 0 := by
  rw [← norm_eq_zero]
  apply le_antisymm
  · refine (norm_iteratedFDeriv_mul_le hf hg 0 (mod_cast le_top) (n := n)).trans ?_
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro i hi
    rw [hzero i]
    simp
  · exact norm_nonneg _


-- @@ L267-267 verbatim
end ContDiff


-- @@ L269-269 verbatim
namespace Real


-- @@ L271-273 verbatim
/-- The extension by zero of `x ↦ exp (-c * x ^ (-a))` from the positive half-line. -/
def flatRpowExp (a c x : ℝ) : ℝ :=
  if x ≤ 0 then 0 else exp (-c * x ^ (-a))


-- @@ L275-275 verbatim
namespace flatRpowExp


-- @@ L277-278 verbatim
theorem zero_of_nonpos (a c : ℝ) {x : ℝ} (hx : x ≤ 0) : flatRpowExp a c x = 0 := by
  simp [flatRpowExp, hx]


-- @@ L280-281 verbatim
@[simp]
theorem zero (a c : ℝ) : flatRpowExp a c 0 = 0 := zero_of_nonpos a c le_rfl


-- @@ L283-285 verbatim
theorem of_pos (a c : ℝ) {x : ℝ} (hx : 0 < x) :
    flatRpowExp a c x = exp (-c * x ^ (-a)) := by
  simp [flatRpowExp, hx.not_ge]


-- @@ L287-298 verbatim
/-- Exponential decay at zero dominates every real power. -/
theorem tendsto_rpow_mul_zero {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (s : ℝ) :
    Tendsto (fun x : ℝ ↦ x ^ s * flatRpowExp a c x) (𝓝[>] 0) (𝓝 0) := by
  have ht : Tendsto (fun x : ℝ ↦ x ^ (-a)) (𝓝[>] 0) atTop :=
    tendsto_rpow_neg_nhdsGT_zero (neg_neg_of_pos ha)
  refine ((tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (-s / a) c hc).comp ht).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  change (x ^ (-a)) ^ (-s / a) * exp (-c * x ^ (-a)) =
    x ^ s * flatRpowExp a c x
  rw [of_pos a c hx, ← Real.rpow_mul hx.le]
  congr 2
  field_simp [ha.ne']


-- @@ L300-301 verbatim
/-- A single generalized Laurent monomial times `flatRpowExp`. -/
private def term (a c ν d x : ℝ) : ℝ := d * x ^ ν * flatRpowExp a c x


-- @@ L303-315 verbatim
private theorem term_tendsto_zero {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (ν d : ℝ) :
    Tendsto (term a c ν d) (𝓝 0) (𝓝 0) := by
  have hinner : Tendsto (fun x : ℝ ↦ x ^ ν * flatRpowExp a c x) (𝓝 0) (𝓝 0) := by
    simp only [flatRpowExp, mul_ite, mul_zero]
    refine tendsto_const_nhds.if ?_
    simp only [not_le]
    refine (tendsto_rpow_mul_zero ha hc ν).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [of_pos a c hx]
  change Tendsto (fun x : ℝ ↦ d * x ^ ν * flatRpowExp a c x) (𝓝 0) (𝓝 0)
  simpa only [mul_assoc, mul_zero] using
    (tendsto_const_nhds.mul hinner :
      Tendsto (fun x : ℝ ↦ d * (x ^ ν * flatRpowExp a c x)) (𝓝 0) (𝓝 (d * 0)))


-- @@ L317-366 verbatim
private theorem term_hasDerivAt {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (ν d x : ℝ) :
    HasDerivAt (term a c ν d)
      (term a c (ν - 1) (d * ν) x + term a c (ν - a - 1) (d * c * a) x) x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have heq : term a c ν d =ᶠ[𝓝 x] fun _ ↦ 0 := by
      filter_upwards [gt_mem_nhds hx] with y hy
      simp [term, zero_of_nonpos a c hy.le]
    simpa [term, zero_of_nonpos a c hx.le] using
      (hasDerivAt_const x 0).congr_of_eventuallyEq heq
  · simp only [term, zero a c, mul_zero, add_zero]
    rw [hasDerivAt_iff_tendsto_slope]
    refine ((term_tendsto_zero ha hc (ν - 1) d).mono_left inf_le_left).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy
    by_cases hypos : 0 < y
    · simp [slope_def_field, term, zero a c, of_pos a c hypos, div_eq_mul_inv]
      rw [Real.rpow_sub_one hypos.ne']
      ring
    · have hynonpos : y ≤ 0 := le_of_not_gt hypos
      simp [slope_def_field, term, zero a c, zero_of_nonpos a c hynonpos]
  · have hpow : HasDerivAt (fun y : ℝ ↦ y ^ ν) (ν * x ^ (ν - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl hx.ne')
    have hpow' : HasDerivAt (fun y : ℝ ↦ y ^ (-a))
        ((-a) * x ^ (-a - 1)) x := Real.hasDerivAt_rpow_const (Or.inl hx.ne')
    have hinner : HasDerivAt (fun y : ℝ ↦ -c * y ^ (-a))
        (c * a * x ^ (-a - 1)) x := by
      have h := hpow'.const_mul (-c)
      have hcoef : (-c) * ((-a) * x ^ (-a - 1)) = c * a * x ^ (-a - 1) := by ring
      rw [hcoef] at h
      exact h
    have hexp : HasDerivAt (fun y : ℝ ↦ exp (-c * y ^ (-a)))
        (exp (-c * x ^ (-a)) * (c * a * x ^ (-a - 1))) x := hinner.exp
    have heq : term a c ν d =ᶠ[𝓝 x]
        fun y ↦ (d * y ^ ν) * exp (-c * y ^ (-a)) := by
      filter_upwards [lt_mem_nhds hx] with y hy
      simp [term, of_pos a c hy]
    have hderiv := ((hpow.const_mul d).mul hexp).congr_of_eventuallyEq heq
    have hrpow : x ^ (ν - a - 1) = x ^ ν * x ^ (-a - 1) := by
      rw [← Real.rpow_add hx]
      congr 1
      ring
    have hcoef :
        term a c (ν - 1) (d * ν) x + term a c (ν - a - 1) (d * c * a) x =
          d * (ν * x ^ (ν - 1)) * exp (-c * x ^ (-a)) +
            d * x ^ ν * (exp (-c * x ^ (-a)) * (c * a * x ^ (-a - 1))) := by
      simp only [term, of_pos a c hx]
      rw [hrpow]
      ring
    rw [hcoef]
    exact hderiv


-- @@ L368-370 verbatim
/-- A finite sum of generalized Laurent monomials times `flatRpowExp`. -/
private def sum (a c : ℝ) (p : Multiset (ℝ × ℝ)) (x : ℝ) : ℝ :=
  (p.map fun q ↦ term a c q.1 q.2 x).sum


-- @@ L372-388 verbatim
private theorem sum_hasDerivAt {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (p : Multiset (ℝ × ℝ)) : ∃ q : Multiset (ℝ × ℝ),
      ∀ x, HasDerivAt (sum a c p) (sum a c q x) x := by
  induction p using Multiset.induction_on with
  | empty =>
      refine ⟨0, fun x ↦ ?_⟩
      change HasDerivAt (fun _ : ℝ ↦ 0) 0 x
      exact hasDerivAt_const x 0
  | @cons head tail ih =>
      rcases ih with ⟨q, hq⟩
      refine ⟨(head.1 - 1, head.2 * head.1) ::ₘ
        (head.1 - a - 1, head.2 * c * a) ::ₘ q, fun x ↦ ?_⟩
      have h := (term_hasDerivAt ha hc head.1 head.2 x).add (hq x)
      rw [show sum a c (head ::ₘ tail) = term a c head.1 head.2 + sum a c tail by
        funext y
        simp [sum]]
      simpa [sum, add_assoc] using h


-- @@ L390-403 verbatim
private theorem sum_contDiff {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (p : Multiset (ℝ × ℝ)) {n : ℕ∞} : ContDiff ℝ n (sum a c p) := by
  apply contDiff_all_iff_nat.2 (fun m ↦ ?_) n
  induction m generalizing p with
  | zero =>
      exact contDiff_zero.2 <| continuous_iff_continuousAt.2 fun x ↦
        ((sum_hasDerivAt ha hc p).choose_spec x).continuousAt
  | succ m ih =>
      obtain ⟨q, hq⟩ := sum_hasDerivAt ha hc p
      rw [show ((m + 1 : ℕ) : WithTop ℕ∞) = m + 1 from rfl]
      refine contDiff_succ_iff_deriv.2 ⟨fun x ↦ (hq x).differentiableAt, by simp, ?_⟩
      have hderiv : deriv (sum a c p) = sum a c q := funext fun x ↦ (hq x).deriv
      rw [hderiv]
      exact ih q


-- @@ L405-414 verbatim
private theorem sum_iteratedDeriv_zero {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    (p : Multiset (ℝ × ℝ)) (n : ℕ) : iteratedDeriv n (sum a c p) 0 = 0 := by
  induction n generalizing p with
  | zero => simp [sum, term]
  | succ n ih =>
      obtain ⟨q, hq⟩ := sum_hasDerivAt ha hc p
      rw [iteratedDeriv_succ']
      have hderiv : deriv (sum a c p) = sum a c q := funext fun x ↦ (hq x).deriv
      rw [hderiv]
      exact ih q


-- @@ L416-422 verbatim
/-- Multiplying `flatRpowExp a c` by an arbitrary real power preserves smoothness. -/
@[fun_prop]
theorem rpow_mul_contDiff {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (s : ℝ) {n : ℕ∞} :
    ContDiff ℝ n (fun x ↦ x ^ s * flatRpowExp a c x) := by
  convert sum_contDiff (n := n) ha hc ({(s, 1)} : Multiset (ℝ × ℝ)) using 1
  funext x
  simp [sum, term]


-- @@ L424-433 verbatim
/-- Every iterated derivative of `x ^ s * flatRpowExp a c x` vanishes at the origin. -/
theorem rpow_mul_iteratedFDeriv_zero {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (s : ℝ)
    (n : ℕ) : iteratedFDeriv ℝ n (fun x ↦ x ^ s * flatRpowExp a c x) 0 = 0 := by
  have hfun : (fun x ↦ x ^ s * flatRpowExp a c x) =
      sum a c ({(s, 1)} : Multiset (ℝ × ℝ)) := by
    funext x
    simp [sum, term]
  rw [hfun, ← norm_eq_zero, norm_iteratedFDeriv_eq_norm_iteratedDeriv,
    sum_iteratedDeriv_zero ha hc]
  simp


-- @@ L435-438 verbatim
/-- Every iterated derivative of `flatRpowExp a c` vanishes at the origin. -/
theorem iteratedFDeriv_zero {a c : ℝ} (ha : 0 < a) (hc : 0 < c) (n : ℕ) :
    iteratedFDeriv ℝ n (flatRpowExp a c) 0 = 0 := by
  simpa using rpow_mul_iteratedFDeriv_zero ha hc 0 n


-- @@ L440-446 verbatim
/-- `flatRpowExp a c` is smooth when both parameters are positive. -/
@[fun_prop]
theorem contDiff {a c : ℝ} (ha : 0 < a) (hc : 0 < c) {n : ℕ∞} :
    ContDiff ℝ n (flatRpowExp a c) := by
  convert sum_contDiff (n := n) ha hc ({(0, 1)} : Multiset (ℝ × ℝ)) using 1
  funext x
  simp [sum, term]


-- @@ L448-448 verbatim
end flatRpowExp


-- @@ L450-450 verbatim
end Real


-- @@ L452-452 verbatim
end


-- @@ L454-454 verbatim
end FlatRpowExpSection


-- @@ L456-456 verbatim
/-! ## Flattened from `FormalConjecturesForMathlib/Geometry/3d.lean` -/


-- @@ L458-458 verbatim
section GeometryThreeSection


-- @@ L460-464 verbatim
/-!
# Three-dimensional Euclidean geometry

This file defines the preferred orientation and bundled continuous cross product on `ℝ³`.
-/



-- @@ L467-467 verbatim
open scoped EuclideanGeometry

-- @@ L468-468 verbatim
open Matrix


-- @@ L470-470 verbatim
namespace EuclideanHypersurface


-- @@ L472-476 expanded
/-- The bundled Euclidean cross product agrees with the coordinate cross product. -/
theorem euclideanCross_apply (a b : EuclideanSpace ℝ (Fin 3)) :
    euclideanCross a b = WithLp.toLp 2 (crossProduct (WithLp.ofLp a) (WithLp.ofLp b)) :=
  rfl


-- @@ L478-484 expanded
/-- Swapping the arguments of the cross product negates it. -/
@[simp]
theorem euclideanCross_anticomm (a b : EuclideanSpace ℝ (Fin 3)) :
    -euclideanCross a b = euclideanCross b a :=
  by
  rw [euclideanCross_apply, euclideanCross_apply]
  change WithLp.toLp 2 (-crossProduct (WithLp.ofLp a) (WithLp.ofLp b)) = _
  exact congrArg (WithLp.toLp 2) (cross_anticomm (WithLp.ofLp a) (WithLp.ofLp b))


-- @@ L486-489 expanded
/-- A vector has zero cross product with itself. -/
@[simp]
theorem euclideanCross_self (a : EuclideanSpace ℝ (Fin 3)) : euclideanCross a a = 0 := by
  simp [euclideanCross_apply]


-- @@ L491-495 expanded
/-- The cross product is orthogonal to its left input. -/
@[simp]
theorem euclideanCross_inner_left (a b : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (euclideanCross a b) a = 0 := by
  simp [euclideanCross_apply, EuclideanSpace.inner_eq_star_dotProduct, dot_self_cross]


-- @@ L497-501 expanded
/-- The cross product is orthogonal to its right input. -/
@[simp]
theorem euclideanCross_inner_right (a b : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (euclideanCross a b) b = 0 := by
  simp [euclideanCross_apply, EuclideanSpace.inner_eq_star_dotProduct, dot_cross_self]


-- @@ L503-509 expanded
/-- The inner product of two cross products is the corresponding Gram-determinant expression. -/
theorem inner_euclideanCross_euclideanCross (a b c d : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ (euclideanCross a b) (euclideanCross c d) =
      inner ℝ a c * inner ℝ b d - inner ℝ a d * inner ℝ b c :=
  by
  simp only [euclideanCross_apply, EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
    cross_dot_cross]
  rw [mul_comm (WithLp.ofLp c ⬝ᵥ WithLp.ofLp b)]


-- @@ L511-521 expanded
/-- The right-nested vector triple-product identity. -/
theorem euclideanCross_cross (u v w : EuclideanSpace ℝ (Fin 3)) :
    euclideanCross u (euclideanCross v w) = inner ℝ u w • v - inner ℝ u v • w :=
  by
  change
    WithLp.toLp 2 (crossProduct (WithLp.ofLp u) (crossProduct (WithLp.ofLp v) (WithLp.ofLp w))) = _
  rw [cross_cross_eq_smul_sub_smul']
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  rw [dotProduct_comm (WithLp.ofLp w) (WithLp.ofLp u),
    dotProduct_comm (WithLp.ofLp v) (WithLp.ofLp u)]
  rfl


-- @@ L523-534 expanded
/-- A cross product is nonzero exactly when its two inputs are linearly independent. -/
theorem euclideanCross_ne_zero_iff_linearIndependent (a b : EuclideanSpace ℝ (Fin 3)) :
    euclideanCross a b ≠ 0 ↔ LinearIndependent ℝ ![a, b] :=
  by
  let e := WithLp.linearEquiv 2 ℝ (Fin 3 → ℝ)
  have hne : euclideanCross a b ≠ 0 ↔ crossProduct (e a) (e b) ≠ 0 :=
    by
    rw [euclideanCross]
    exact e.symm.injective.ne_iff
  rw [hne, crossProduct_ne_zero_iff_linearIndependent]
  have hf : e.toLinearMap ∘ ![a, b] = ![e a, e b] :=
    by
    funext i
    fin_cases i <;> simp
  exact hf ▸ e.toLinearMap.linearIndependent_iff_of_injOn e.injective.injOn


-- @@ L536-546 expanded
/-- The cross product of two vectors orthogonal to a unit vector is parallel to that vector. -/
theorem euclideanCross_eq_inner_smul_of_orthogonal (p x y : EuclideanSpace ℝ (Fin 3)) (hp : ‖p‖ = 1)
    (hx : inner ℝ p x = 0) (hy : inner ℝ p y = 0) :
    euclideanCross x y = inner ℝ (euclideanCross x y) p • p :=
  by
  let c := euclideanCross x y
  have hpc : euclideanCross p c = 0 := by
    dsimp only [c]
    simp [euclideanCross_cross, hy, hx]
  have hsecond := euclideanCross_cross p p c
  rw [hpc, map_zero, show inner ℝ p p = 1 by simp [hp], one_smul] at hsecond
  simpa [c, real_inner_comm] using (sub_eq_zero.mp hsecond.symm).symm


-- @@ L548-548 verbatim
end EuclideanHypersurface


-- @@ L550-550 verbatim
end GeometryThreeSection


-- @@ L552-552 verbatim
/-! ## Flattened from `FormalConjecturesForMathlib/Geometry/EuclideanHypersurface.lean` -/


-- @@ L554-554 verbatim
section EuclideanHypersurfaceSection


-- @@ L556-561 verbatim
/-!
# Extrinsic fundamental forms in Euclidean space

The second fundamental form uses `II(v, w) = -⟪dn(v), dF(w)⟫`, so `dn = c • dF` corresponds
to `II = (-c) • I`.
-/



-- @@ L564-564 verbatim
open scoped RealInnerProductSpace


-- @@ L566-566 verbatim
namespace EuclideanHypersurface


-- @@ L568-569 verbatim
variable {V E : Type*} [TopologicalSpace V] [AddCommGroup V] [Module ℝ V]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]


-- @@ L571-574 verbatim
@[simp]
theorem firstFundamentalFormAt_apply (dF : V →L[ℝ] E) (v w : V) :
    firstFundamentalFormAt dF v w = inner ℝ (dF v) (dF w) :=
  rfl


-- @@ L576-579 verbatim
@[simp]
theorem secondFundamentalFormAt_apply (dn dF : V →L[ℝ] E) (v w : V) :
    secondFundamentalFormAt dn dF v w = -inner ℝ (dn v) (dF w) :=
  rfl


-- @@ L581-588 verbatim
/-- If `dn = c • dF`, the point is umbilic with scalar `-c` under our sign convention. -/
theorem isUmbilic_of_normal_deriv_eq_smul
    (dF dn : V →L[ℝ] E) (c : ℝ) (h : dn = c • dF) :
    IsUmbilic V E dF dn := by
  refine ⟨-c, ?_⟩
  ext v w
  change -inner ℝ (dn v) (dF w) = -c * inner ℝ (dF v) (dF w)
  rw [h, ContinuousLinearMap.smul_apply, real_inner_smul_left, neg_mul]


-- @@ L590-611 verbatim
/-- If `dn` is tangent to the immersion, umbilicity is equivalent to `dn` being a scalar multiple
of `dF`. -/
theorem isUmbilic_iff_normal_deriv_eq_smul
    (dF dn : V →L[ℝ] E) (htangent : dn.range ≤ dF.range) :
    IsUmbilic V E dF dn ↔ ∃ c : ℝ, dn = c • dF := by
  constructor
  · rintro ⟨κ, hκ⟩
    refine ⟨-κ, ?_⟩
    ext v
    obtain ⟨u, hu⟩ := htangent ⟨v, rfl⟩
    have horth (w : V) : inner ℝ (dn v + κ • dF v) (dF w) = 0 := by
      have h := congrArg (fun B : LinearMap.BilinForm ℝ V ↦ B v w) hκ
      change -inner ℝ (dn v) (dF w) = κ * inner ℝ (dF v) (dF w) at h
      rw [inner_add_left, real_inner_smul_left, ← h, add_neg_cancel]
    have hrange : dn v + κ • dF v = dF (u + κ • v) := by
      change dF u = dn v at hu
      rw [map_add, map_smul, ← hu]
    have hzero := horth (u + κ • v)
    rw [← hrange, real_inner_self_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero] at hzero
    simpa [ContinuousLinearMap.smul_apply] using
      eq_neg_of_add_eq_zero_left hzero
  · exact fun ⟨c, hc⟩ ↦ isUmbilic_of_normal_deriv_eq_smul dF dn c hc


-- @@ L613-613 verbatim
end EuclideanHypersurface


-- @@ L615-615 verbatim
end EuclideanHypersurfaceSection


-- @@ L617-617 verbatim
/-! ## Flattened from `FormalConjecturesForMathlib/Geometry/SphereImmersion.lean` -/


-- @@ L619-619 verbatim
section SphereImmersionSection


-- @@ L621-627 verbatim
/-!
# A canonical normal for immersed two-spheres in three-space

Mathlib models each sphere tangent space on a fixed copy of `ℝ²`. We orient the cross product
using the standard sphere inclusion; changing the model frame then contributes a squared
determinant, which disappears after normalization.
-/



-- @@ L630-630 verbatim
open Metric

-- @@ L631-631 verbatim
open scoped EuclideanGeometry EuclideanSpace Manifold RealInnerProductSpace


-- @@ L633-633 verbatim
namespace EuclideanHypersurface


-- @@ L635-646 expanded
/-- The basis induced by the tangent-bundle trivialization at its base point agrees with the
standard model basis. -/
theorem sphereTangentBasis_apply (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (i : Fin 2) :
    sphereTangentBasis p i = PiLp.basisFun 2 ℝ (Fin 2) i :=
  by
  simp only [sphereTangentBasis, Bundle.Trivialization.basisAt, Module.Basis.map_apply,
    Bundle.Trivialization.linearEquivAt_symm_apply]
  rw [←
    Bundle.Trivialization.symmL_apply (R := ℝ)
      (trivializationAt (EuclideanSpace ℝ (Fin 2)) (TangentSpace (𝓡 2)) p)
      (FiberBundle.mem_baseSet_trivializationAt' p)]
  rw [TangentBundle.symmL_trivializationAt_eq_core (mem_chart_source _ p)]
  simpa using!
    (tangentBundleCore (𝓡 2) _).coordChange_self (achart _ p) p (mem_chart_source _ p)
      (PiLp.basisFun 2 ℝ (Fin 2) i)


-- @@ L648-678 expanded
private theorem mfderiv_inclusion_sphereTangentBasis_apply
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (i : Fin 2) :
    (mvfderiv (𝓡 2)
            (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p :
          TangentSpace (𝓡 2) p →L[ℝ] EuclideanSpace ℝ (Fin 3))
        (sphereTangentBasis p i) =
      let U :=
        (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2
            (ne_zero_of_mem_unit_sphere (-p))).repr
      ((U.symm (PiLp.basisFun 2 ℝ (Fin 2) i) : (ℝ ∙ (↑(-p) : EuclideanSpace ℝ (Fin 3)))ᗮ) :
        EuclideanSpace ℝ (Fin 3)) :=
  by
  rw [((contMDiff_coe_sphere p).mdifferentiableAt one_ne_zero).mvfderiv]
  simp only [chartAt, fderivWithin_univ, mfld_simps]
  rw [sphereTangentBasis_apply]
  let U :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2 (ne_zero_of_mem_unit_sphere (-p))).repr
  change
    (fderiv ℝ
          ((stereoInvFunAux (-p : EuclideanSpace ℝ (Fin 3)) ∘
              (Subtype.val :
                (ℝ ∙ (↑(-p) : EuclideanSpace ℝ (Fin 3)))ᗮ → EuclideanSpace ℝ (Fin 3))) ∘
            U.symm)
          (stereographic' 2 (-p) p))
        (PiLp.basisFun 2 ℝ (Fin 2) i) =
      ((U.symm (PiLp.basisFun 2 ℝ (Fin 2) i) : (ℝ ∙ (↑(-p) : EuclideanSpace ℝ (Fin 3)))ᗮ) :
        EuclideanSpace ℝ (Fin 3))
  have hp0 : stereographic' 2 (-p) p = 0 :=
    by
    change U (stereographic (norm_eq_of_mem_sphere (-p)) p) = 0
    rw [stereographic_neg_apply, map_zero]
  rw [hp0]
  have h :
    HasFDerivAt
      (stereoInvFunAux (-p : EuclideanSpace ℝ (Fin 3)) ∘
        (Subtype.val : (ℝ ∙ (↑(-p) : EuclideanSpace ℝ (Fin 3)))ᗮ → EuclideanSpace ℝ (Fin 3)))
      (ℝ ∙ (↑(-p) : EuclideanSpace ℝ (Fin 3)))ᗮ.subtypeL (U.symm 0) :=
    by
    convert! hasFDerivAt_stereoInvFunAux_comp_coe (-p : EuclideanSpace ℝ (Fin 3))
    simp
  rw [(h.comp 0 U.symm.toContinuousLinearEquiv.hasFDerivAt).fderiv]
  rfl


-- @@ L680-701 expanded
/-- The standard model basis maps to an orthonormal frame under the derivative of the sphere
inclusion. -/
@[simp]
theorem inner_mfderiv_inclusion_sphereTangentBasis (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (i j : Fin 2) :
    inner ℝ
        (show EuclideanSpace ℝ (Fin 3) from
          mvfderiv (𝓡 2)
            (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
            (sphereTangentBasis p i))
        (show EuclideanSpace ℝ (Fin 3) from
          mvfderiv (𝓡 2)
            (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
            (sphereTangentBasis p j)) =
      if i = j then 1 else 0 :=
  by
  rw [mfderiv_inclusion_sphereTangentBasis_apply p i,
    mfderiv_inclusion_sphereTangentBasis_apply p j]
  let U :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) 2 (ne_zero_of_mem_unit_sphere (-p))).repr
  change
    inner ℝ
        ((ℝ ∙
                ((-p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
                  EuclideanSpace ℝ (Fin 3)))ᗮ.subtypeₗᵢ
          (U.symm (PiLp.basisFun 2 ℝ (Fin 2) i)))
        ((ℝ ∙
                ((-p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
                  EuclideanSpace ℝ (Fin 3)))ᗮ.subtypeₗᵢ
          (U.symm (PiLp.basisFun 2 ℝ (Fin 2) j))) =
      _
  rw [LinearIsometry.inner_map_map, U.symm.inner_map_map]
  exact orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin 2) ℝ).orthonormal i j


-- @@ L703-709 expanded
/-- The derivative of the sphere inclusion maps the standard model basis to an orthonormal
family. -/
theorem orthonormal_mfderiv_inclusion_sphereTangentBasis
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Orthonormal ℝ fun i : Fin 2 ↦
      (show EuclideanSpace ℝ (Fin 3) from
        mvfderiv (𝓡 2)
          (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
          (sphereTangentBasis p i)) :=
  orthonormal_iff_ite.mpr (inner_mfderiv_inclusion_sphereTangentBasis p)


-- @@ L711-723 expanded
private theorem sphere_inclusion_cross_eq_smul (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    let b := sphereTangentBasis p
    let dι : TangentSpace (𝓡 2) p →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
      mvfderiv (𝓡 2)
        (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
    euclideanCross (dι (b 0)) (dι (b 1)) =
      inner ℝ (euclideanCross (dι (b 0)) (dι (b 1))) (p : EuclideanSpace ℝ (Fin 3)) •
        (p : EuclideanSpace ℝ (Fin 3)) :=
  by
  dsimp only
  refine euclideanCross_eq_inner_smul_of_orthogonal _ _ _ (norm_eq_of_mem_sphere p) ?_ ?_
  ·
    exact
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp <|
        range_mvfderiv_subtypeVal (n := 2) p ▸ ⟨sphereTangentBasis p 0, rfl⟩
  ·
    exact
      Submodule.mem_orthogonal_singleton_iff_inner_right.mp <|
        range_mvfderiv_subtypeVal (n := 2) p ▸ ⟨sphereTangentBasis p 1, rfl⟩


-- @@ L725-746 expanded
private theorem sphere_inclusion_orientation_factor_sq
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    let b := sphereTangentBasis p
    let dι : TangentSpace (𝓡 2) p →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
      mvfderiv (𝓡 2)
        (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
    inner ℝ (euclideanCross (dι (b 0)) (dι (b 1))) (p : EuclideanSpace ℝ (Fin 3)) ^ 2 = 1 :=
  by
  dsimp only
  let b := sphereTangentBasis p
  let dι : TangentSpace (𝓡 2) p →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mvfderiv (𝓡 2)
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
  have hON : Orthonormal ℝ fun i : Fin 2 ↦ dι (b i) :=
    orthonormal_mfderiv_inclusion_sphereTangentBasis p
  let c := euclideanCross (dι (b 0)) (dι (b 1))
  let s := inner ℝ c (p : EuclideanSpace ℝ (Fin 3))
  change s ^ 2 = 1
  calc
    s ^ 2 = inner ℝ c c := by
      simp [show c = s • (p : EuclideanSpace ℝ (Fin 3)) from sphere_inclusion_cross_eq_smul p,
        norm_smul, norm_eq_of_mem_sphere p, pow_two]
    _ = 1 := by
      dsimp only [c]
      rw [inner_euclideanCross_euclideanCross]
      simp [hON.norm_eq_one, hON.inner_eq_zero]


-- @@ L748-760 expanded
/-- The raw canonical normal of the standard sphere inclusion is the radial vector. -/
@[simp]
theorem sphereNormalRaw_inclusion (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    sphereNormalRaw
        (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p =
      (p : EuclideanSpace ℝ (Fin 3)) :=
  by
  let b := sphereTangentBasis p
  let dι : TangentSpace (𝓡 2) p →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mvfderiv (𝓡 2)
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
  let c := euclideanCross (dι (b 0)) (dι (b 1))
  let s := inner ℝ c (p : EuclideanSpace ℝ (Fin 3))
  change s • c = (p : EuclideanSpace ℝ (Fin 3))
  rw [show c = s • (p : EuclideanSpace ℝ (Fin 3)) from sphere_inclusion_cross_eq_smul p, smul_smul,
    ← pow_two, show s ^ 2 = 1 from sphere_inclusion_orientation_factor_sq p, one_smul]


-- @@ L762-777 expanded
/-- The raw canonical normal is orthogonal to every image tangent vector. -/
@[simp]
theorem inner_sphereNormalRaw_mfderiv
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (v : TangentSpace (𝓡 2) p) :
    inner ℝ (sphereNormalRaw F p) (show EuclideanSpace ℝ (Fin 3) from mvfderiv (𝓡 2) F p v) = 0 :=
  by
  let b := sphereTangentBasis p
  let dι : TangentSpace (𝓡 2) p →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mvfderiv (𝓡 2)
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
  let dF : TangentSpace (𝓡 2) p →L[ℝ] EuclideanSpace ℝ (Fin 3) := mvfderiv (𝓡 2) F p
  change
    inner ℝ
        (inner ℝ (euclideanCross (dι (b 0)) (dι (b 1))) (p : EuclideanSpace ℝ (Fin 3)) •
          euclideanCross (dF (b 0)) (dF (b 1)))
        (dF v) =
      0
  rw [real_inner_smul_left, ← b.sum_repr v, map_sum]
  simp [Fin.sum_univ_two, map_smul, inner_add_right, real_inner_smul_right]


-- @@ L779-787 expanded
/-- The canonical normal is orthogonal to every image tangent vector, even at a non-immersion. -/
@[simp]
theorem inner_sphereNormal_mfderiv
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (v : TangentSpace (𝓡 2) p) :
    inner ℝ (sphereNormal F p) (show EuclideanSpace ℝ (Fin 3) from mvfderiv (𝓡 2) F p v) = 0 := by
  rw [sphereNormal, NormedSpace.normalize, real_inner_smul_left, inner_sphereNormalRaw_mfderiv,
    mul_zero]


-- @@ L789-807 expanded
private theorem sphereNormalRaw_ne_zero_iff
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    sphereNormalRaw F p ≠ 0 ↔ Function.Injective (mvfderiv (𝓡 2) F p) :=
  by
  let b := sphereTangentBasis p
  let dι : TangentSpace (𝓡 2) p →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mvfderiv (𝓡 2)
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
  let dF : TangentSpace (𝓡 2) p →L[ℝ] EuclideanSpace ℝ (Fin 3) := mvfderiv (𝓡 2) F p
  have hfactor :
    inner ℝ (euclideanCross (dι (b 0)) (dι (b 1))) (p : EuclideanSpace ℝ (Fin 3)) ≠ 0 :=
    by
    intro h
    simpa [b, dι, h] using sphere_inclusion_orientation_factor_sq p
  rw [sphereNormalRaw, smul_ne_zero_iff, and_iff_right hfactor,
    euclideanCross_ne_zero_iff_linearIndependent]
  have hfamily : dF.toLinearMap ∘ b = ![dF (b 0), dF (b 1)] :=
    by
    funext i
    fin_cases i <;> rfl
  constructor
  · exact fun hLI ↦ LinearMap.injective_of_linearIndependent b.span_eq (hfamily.symm ▸ hLI)
  ·
    exact fun hF ↦
      hfamily ▸ b.linearIndependent.map' dF.toLinearMap (LinearMap.ker_eq_bot_of_injective hF)


-- @@ L809-815 expanded
/-- The canonical normal is nonzero exactly at the points where the manifold derivative is
injective. -/
theorem sphereNormal_ne_zero_iff
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    sphereNormal F p ≠ 0 ↔ Function.Injective (mvfderiv (𝓡 2) F p) := by
  simpa [sphereNormal, NormedSpace.normalize_eq_zero_iff] using sphereNormalRaw_ne_zero_iff F p


-- @@ L817-823 expanded
/-- At an immersion point, the canonical normal has unit length. -/
theorem norm_sphereNormal_of_injective
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (hF : Function.Injective (mvfderiv (𝓡 2) F p)) :
    ‖sphereNormal F p‖ = 1 := by
  simpa [sphereNormal] using NormedSpace.norm_normalize ((sphereNormalRaw_ne_zero_iff F p).mpr hF)


-- @@ L825-831 expanded
/-- Normalizing a positive multiple of the radial vector recovers the radial vector. -/
theorem sphereNormal_eq_of_raw_eq_pos_smul
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (c : ℝ) (hc : 0 < c)
    (hraw : sphereNormalRaw F p = c • (p : EuclideanSpace ℝ (Fin 3))) :
    sphereNormal F p = (p : EuclideanSpace ℝ (Fin 3)) := by
  rw [sphereNormal, hraw, NormedSpace.normalize_smul_of_pos hc,
    NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere p)]


-- @@ L833-895 expanded
/-- A radially tangent map whose derivative is positively coercive relative to the standard
sphere inclusion has the outward radial canonical normal. -/
theorem sphereNormal_eq_radial_of_coercive
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (c : ℝ) (hc : 0 < c)
    (hnormal :
      ∀ v,
        inner ℝ (p : EuclideanSpace ℝ (Fin 3))
            (show EuclideanSpace ℝ (Fin 3) from mvfderiv (𝓡 2) F p v) =
          0)
    (hcoercive :
      ∀ v,
        c *
            ‖(show EuclideanSpace ℝ (Fin 3) from
                  mvfderiv (𝓡 2)
                    (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦
                      (q : EuclideanSpace ℝ (Fin 3)))
                    p v)‖ ^
              2 ≤
          inner ℝ (show EuclideanSpace ℝ (Fin 3) from mvfderiv (𝓡 2) F p v)
            (show EuclideanSpace ℝ (Fin 3) from
              mvfderiv (𝓡 2)
                (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
                v)) :
    sphereNormal F p = (p : EuclideanSpace ℝ (Fin 3)) :=
  by
  let b := sphereTangentBasis p
  let dι : TangentSpace (𝓡 2) p →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mvfderiv (𝓡 2)
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
  let dF : TangentSpace (𝓡 2) p →L[ℝ] EuclideanSpace ℝ (Fin 3) := mvfderiv (𝓡 2) F p
  let u := dι (b 0)
  let v := dι (b 1)
  let x := dF (b 0)
  let y := dF (b 1)
  let A := inner ℝ x u
  let D := inner ℝ y v
  let P := inner ℝ x v
  let Q := inner ℝ y u
  have hON : Orthonormal ℝ fun i : Fin 2 ↦ dι (b i) :=
    orthonormal_mfderiv_inclusion_sphereTangentBasis p
  have hcoercive0 : c * ‖dι (b 0)‖ ^ 2 ≤ inner ℝ (dF (b 0)) (dι (b 0)) := hcoercive (b 0)
  rw [hON.norm_eq_one 0, one_pow, mul_one] at hcoercive0
  have hApos : 0 < A := hc.trans_le <| by simpa [A, x, u] using hcoercive0
  let s := P + Q
  let t := s • b 0 - (2 * A) • b 1
  have ht : t ≠ 0 := by
    intro ht
    have htCoord := congrArg (fun z ↦ b.repr z 1) ht
    simp [t] at htCoord
    linarith
  have hdιt : dι t ≠ 0 := (map_ne_zero_iff dι (injective_mvfderiv_subtypeVal_sphere p)).mpr ht
  have hquadpos : 0 < inner ℝ (dF t) (dι t) :=
    (mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hdιt))).trans_le (hcoercive t)
  simp only [t, map_sub, map_smul] at hquadpos
  change 0 < inner ℝ (s • x - (2 * A) • y) (s • u - (2 * A) • v) at hquadpos
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, s, A, P,
    Q] at hquadpos
  have hdetAux : 0 < 4 * A * D - (P + Q) ^ 2 := by nlinarith
  have hdet : 0 < A * D - P * Q := by nlinarith [sq_nonneg (P - Q)]
  have hcrossPos : 0 < inner ℝ (euclideanCross u v) (euclideanCross x y) :=
    by
    rw [inner_euclideanCross_euclideanCross, ← real_inner_comm u x, ← real_inner_comm v y, ←
      real_inner_comm u y, ← real_inner_comm v x]
    change 0 < A * D - Q * P
    simpa [mul_comm Q P] using hdet
  apply
    sphereNormal_eq_of_raw_eq_pos_smul F p (inner ℝ (euclideanCross u v) (euclideanCross x y))
      hcrossPos
  change
    inner ℝ (euclideanCross u v) (p : EuclideanSpace ℝ (Fin 3)) • euclideanCross x y =
      inner ℝ (euclideanCross u v) (euclideanCross x y) • (p : EuclideanSpace ℝ (Fin 3))
  rw [euclideanCross_eq_inner_smul_of_orthogonal (p : EuclideanSpace ℝ (Fin 3)) x y
      (norm_eq_of_mem_sphere p) (hnormal (b 0)) (hnormal (b 1)),
    real_inner_smul_right, smul_smul, mul_comm]


-- @@ L897-902 expanded
/-- The canonical normal of the standard sphere inclusion points radially outward. -/
@[simp]
theorem sphereNormal_inclusion (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    sphereNormal (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3)))
        p =
      (p : EuclideanSpace ℝ (Fin 3)) :=
  by
  rw [sphereNormal, sphereNormalRaw_inclusion,
    NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere p)]


-- @@ L904-904 verbatim
end EuclideanHypersurface


-- @@ L906-906 verbatim
end SphereImmersionSection


-- @@ L908-908 verbatim
/-! ## Flattened from `FormalConjecturesForMathlib/Geometry/SphereImmersionRegularity.lean` -/


-- @@ L910-910 verbatim
section SphereImmersionRegularitySection


-- @@ L912-918 verbatim
/-!
# Regularity of the canonical normal of a sphere immersion

Although the sphere charts do not give a continuous global tangent frame, `sphereNormal` is
regular. In local tangent coordinates, a frame change scales its raw normal by a positive square,
which normalization removes. Thus a `C^(m + 1)` immersion has a `C^m` canonical normal.
-/



-- @@ L921-921 verbatim
open Metric

-- @@ L922-922 verbatim
open scoped EuclideanGeometry EuclideanSpace Manifold RealInnerProductSpace


-- @@ L924-924 verbatim
namespace EuclideanHypersurface


-- @@ L926-937 expanded
private theorem euclideanCross_comp_basis {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (b : Module.Basis (Fin 2) ℝ V) (L : V →L[ℝ] EuclideanSpace ℝ (Fin 3)) (A : V →L[ℝ] V) :
    euclideanCross (L (A (b 0))) (L (A (b 1))) =
      LinearMap.det A.toLinearMap • euclideanCross (L (b 0)) (L (b 1)) :=
  by
  rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two, ← b.sum_repr (A (b 0)), ←
    b.sum_repr (A (b 1))]
  simp only [Fin.sum_univ_two, map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, euclideanCross_self, smul_zero, add_zero,
    LinearMap.toMatrix_apply]
  rw [← euclideanCross_anticomm (L (b 0)) (L (b 1))]
  module


-- @@ L939-944 expanded
private theorem contMDiffAt_normalize {m : WithTop ℕ∞}
    {f : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3)}
    {p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1} (hf : ContMDiffAt (𝓡 2) (𝓡 3) m f p)
    (h0 : f p ≠ 0) : ContMDiffAt (𝓡 2) (𝓡 3) m (fun q ↦ NormedSpace.normalize (f q)) p :=
  by
  change ContMDiffAt (𝓡 2) (𝓡 3) m (fun q ↦ ‖f q‖⁻¹ • f q) p
  exact (((contDiffAt_norm ℝ h0).inv (norm_ne_zero_iff.mpr h0)).comp_contMDiffAt hf).smul hf


-- @@ L946-956 expanded
private theorem inTangentCoordinates_sphere_eq_comp
    (G : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (p q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (hq : q ∈ (extChartAt (𝓡 2) p).source) :
    inTangentCoordinates (𝓡 2) (𝓡 3) id G (mfderiv (𝓡 2) (𝓡 3) G) p q =
      mfderiv (𝓡 2) (𝓡 3) G q ∘L
        (tangentCoordChange (𝓡 2) p q q :
          EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :=
  by
  rw [inTangentCoordinates_eq _ _ _ (by simpa [extChartAt_source] using hq) (by simp),
    tangentBundleCore_coordChange_model_space, ContinuousLinearMap.id_comp]
  rfl


-- @@ L958-968 expanded
private theorem tangentCoordChange_injective (p q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hq : q ∈ (extChartAt (𝓡 2) p).source) :
    Function.Injective
      (tangentCoordChange (𝓡 2) p q q : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :=
  by
  intro u v huv
  have hmem :
    q ∈ (extChartAt (𝓡 2) p).source ∩ (extChartAt (𝓡 2) q).source ∩ (extChartAt (𝓡 2) p).source :=
    ⟨⟨hq, mem_extChartAt_source q⟩, hq⟩
  simpa only [tangentCoordChange_comp hmem, tangentCoordChange_self hq] using
    congrArg
      (tangentCoordChange (𝓡 2) q p q : EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) huv


-- @@ L970-982 expanded
private noncomputable def sphereNormalRawInCoordinates
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3) :=
  let b := PiLp.basisFun 2 ℝ (Fin 2)
  let e0 := b 0
  let e1 := b 1
  let dι :=
    inTangentCoordinates (𝓡 2) (𝓡 3) id
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3)))
      (mfderiv (𝓡 2) (𝓡 3)
        (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))))
      p
  let dF := inTangentCoordinates (𝓡 2) (𝓡 3) id F (mfderiv (𝓡 2) (𝓡 3) F) p
  fun q ↦
  inner ℝ (euclideanCross (dι q e0) (dι q e1)) (q : EuclideanSpace ℝ (Fin 3)) •
    euclideanCross (dF q e0) (dF q e1)


-- @@ L984-1011 expanded
private theorem contMDiffAt_sphereNormalRawInCoordinates {m n : WithTop ℕ∞}
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (hF : ContMDiffAt (𝓡 2) (𝓡 3) n F p)
    (hmn : m + 1 ≤ n) : ContMDiffAt (𝓡 2) (𝓡 3) m (sphereNormalRawInCoordinates F p) p :=
  by
  let b := PiLp.basisFun 2 ℝ (Fin 2)
  let e0 := b 0
  let e1 := b 1
  let dι :=
    inTangentCoordinates (𝓡 2) (𝓡 3) id
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3)))
      (mfderiv (𝓡 2) (𝓡 3)
        (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))))
      p
  let dF := inTangentCoordinates (𝓡 2) (𝓡 3) id F (mfderiv (𝓡 2) (𝓡 3) F) p
  have hdι :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)) m dι p :=
    (contMDiff_coe_sphere (n := 2) (m := ⊤) p).mfderiv_const le_top
  have hdF :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 3)) m dF p :=
    hF.mfderiv_const hmn
  have hdι0 := hdι.clm_apply (contMDiffAt_const (c := e0))
  have hdι1 := hdι.clm_apply (contMDiffAt_const (c := e1))
  have hdF0 := hdF.clm_apply (contMDiffAt_const (c := e0))
  have hdF1 := hdF.clm_apply (contMDiffAt_const (c := e1))
  have hcι := (euclideanCross.contMDiffAt.comp p hdι0).clm_apply hdι1
  have hcF := (euclideanCross.contMDiffAt.comp p hdF0).clm_apply hdF1
  have hinner :
    ContDiff ℝ m (fun x : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) ↦ inner ℝ x.1 x.2) :=
    contDiff_inner
  have hraw := (hinner.comp_contMDiffAt (hcι.prodMk_space (contMDiff_coe_sphere p))).smul hcF
  apply hraw.congr_of_eventuallyEq
  filter_upwards with q
  simp [sphereNormalRawInCoordinates, b, e0, e1, dι, dF, Function.comp_def]


-- @@ L1013-1049 expanded
private theorem sphereNormalRawInCoordinates_eq_smul
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (p q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (hq : q ∈ (extChartAt (𝓡 2) p).source) :
    sphereNormalRawInCoordinates F p q =
      LinearMap.det
            (tangentCoordChange (𝓡 2) p q q :
                EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)).toLinearMap ^
          2 •
        sphereNormalRaw F q :=
  by
  let b := PiLp.basisFun 2 ℝ (Fin 2)
  let A := tangentCoordChange (𝓡 2) p q q
  let dι : TangentSpace (𝓡 2) q →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mvfderiv (𝓡 2)
      (fun r : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (r : EuclideanSpace ℝ (Fin 3))) q
  let dF : TangentSpace (𝓡 2) q →L[ℝ] EuclideanSpace ℝ (Fin 3) := mvfderiv (𝓡 2) F q
  let dιc :=
    inTangentCoordinates (𝓡 2) (𝓡 3) id
      (fun r : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (r : EuclideanSpace ℝ (Fin 3)))
      (mfderiv (𝓡 2) (𝓡 3)
        (fun r : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (r : EuclideanSpace ℝ (Fin 3))))
      p q
  let dFc := inTangentCoordinates (𝓡 2) (𝓡 3) id F (mfderiv (𝓡 2) (𝓡 3) F) p q
  rw [sphereNormalRaw]
  rw [sphereTangentBasis_apply q 0, sphereTangentBasis_apply q 1]
  change
    inner ℝ (euclideanCross (dιc (b 0)) (dιc (b 1))) (q : EuclideanSpace ℝ (Fin 3)) •
        euclideanCross (dFc (b 0)) (dFc (b 1)) =
      LinearMap.det A.toLinearMap ^ 2 •
        (inner ℝ (euclideanCross (dι (b 0)) (dι (b 1))) (q : EuclideanSpace ℝ (Fin 3)) •
          euclideanCross (dF (b 0)) (dF (b 1)))
  rw [show dιc = dι.comp A from
      inTangentCoordinates_sphere_eq_comp
        (fun r : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (r : EuclideanSpace ℝ (Fin 3))) p q hq,
    show dFc = dF.comp A from inTangentCoordinates_sphere_eq_comp F p q hq]
  calc
    _ =
        inner ℝ (LinearMap.det A.toLinearMap • euclideanCross (dι (b 0)) (dι (b 1)))
            (q : EuclideanSpace ℝ (Fin 3)) •
          (LinearMap.det A.toLinearMap • euclideanCross (dF (b 0)) (dF (b 1))) :=
      congrArg₂ (fun (s : ℝ) (x : EuclideanSpace ℝ (Fin 3)) ↦ s • x)
        (congrArg (fun x ↦ inner ℝ x (q : EuclideanSpace ℝ (Fin 3)))
          (euclideanCross_comp_basis b dι A))
        (euclideanCross_comp_basis b dF A)
    _ = _ := by
      rw [real_inner_smul_left]
      module


-- @@ L1051-1056 expanded
private theorem det_tangentCoordChange_ne_zero (p q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
    (hq : q ∈ (extChartAt (𝓡 2) p).source) :
    LinearMap.det
        (tangentCoordChange (𝓡 2) p q q :
            EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)).toLinearMap ≠
      0 :=
  by
  simpa [LinearMap.det_eq_zero_iff_ker_ne_bot] using
    LinearMap.ker_eq_bot_of_injective (tangentCoordChange_injective p q hq)


-- @@ L1058-1076 expanded
/-- At an immersion point, a locally `C^n` map has a locally `C^m` canonical unit normal when
`m + 1 ≤ n`. -/
theorem contMDiffAt_sphereNormal_of_le {m n : WithTop ℕ∞}
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (hF : ContMDiffAt (𝓡 2) (𝓡 3) n F p)
    (hmn : m + 1 ≤ n) (himm : Function.Injective (mvfderiv (𝓡 2) F p)) :
    ContMDiffAt (𝓡 2) (𝓡 3) m (sphereNormal F) p :=
  by
  have hp : p ∈ (extChartAt (𝓡 2) p).source := mem_extChartAt_source p
  have hlocal : sphereNormalRawInCoordinates F p p ≠ 0 :=
    by
    rw [sphereNormalRawInCoordinates_eq_smul F p p hp]
    refine smul_ne_zero (pow_ne_zero 2 (det_tangentCoordChange_ne_zero p p hp)) ?_
    simpa [sphereNormal, NormedSpace.normalize_eq_zero_iff] using
      (sphereNormal_ne_zero_iff F p).2 himm
  apply
    (contMDiffAt_normalize (contMDiffAt_sphereNormalRawInCoordinates F p hF hmn)
        hlocal).congr_of_eventuallyEq
  filter_upwards [extChartAt_source_mem_nhds (I := 𝓡 2) p] with q hq
  rw [sphereNormal, sphereNormalRawInCoordinates_eq_smul F p q hq,
    NormedSpace.normalize_smul_of_pos (sq_pos_of_ne_zero (det_tangentCoordChange_ne_zero p q hq))]


-- @@ L1078-1084 expanded
/-- At an immersion point, a locally `C^(m + 1)` map has a locally `C^m` canonical unit normal. -/
theorem contMDiffAt_sphereNormal {m : WithTop ℕ∞}
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (hF : ContMDiffAt (𝓡 2) (𝓡 3) (m + 1) F p)
    (himm : Function.Injective (mvfderiv (𝓡 2) F p)) :
    ContMDiffAt (𝓡 2) (𝓡 3) m (sphereNormal F) p :=
  contMDiffAt_sphereNormal_of_le F p hF le_rfl himm


-- @@ L1086-1093 expanded
/-- A `C^n` immersion of the unit two-sphere has a `C^m` canonical unit normal when
`m + 1 ≤ n`. -/
theorem contMDiff_sphereNormal_of_le {m n : WithTop ℕ∞}
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (hF : ContMDiff (𝓡 2) (𝓡 3) n F) (hmn : m + 1 ≤ n)
    (himm : ∀ p, Function.Injective (mvfderiv (𝓡 2) F p)) :
    ContMDiff (𝓡 2) (𝓡 3) m (sphereNormal F) := fun p ↦
  contMDiffAt_sphereNormal_of_le F p (hF p) hmn (himm p)


-- @@ L1095-1101 expanded
/-- A `C^(m + 1)` immersion of the unit two-sphere has a `C^m` canonical unit normal. -/
theorem contMDiff_sphereNormal {m : WithTop ℕ∞}
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (hF : ContMDiff (𝓡 2) (𝓡 3) (m + 1) F) (himm : ∀ p, Function.Injective (mvfderiv (𝓡 2) F p)) :
    ContMDiff (𝓡 2) (𝓡 3) m (sphereNormal F) :=
  contMDiff_sphereNormal_of_le F hF le_rfl himm


-- @@ L1103-1103 verbatim
end EuclideanHypersurface



-- @@ L1106-1106 verbatim
namespace CaratheodoryConjecture


-- @@ L1108-1108 verbatim
end CaratheodoryConjecture


-- @@ L1110-1110 verbatim
end SphereImmersionRegularitySection


-- @@ L1112-1112 verbatim
/-! ## Flattened from `FormalConjecturesForMathlib/Geometry/SupportFunctionSphere.lean` -/


-- @@ L1114-1114 verbatim
section SupportFunctionSphereSection


-- @@ L1116-1116 verbatim
open Metric Set

-- @@ L1117-1117 verbatim
open scoped Gradient Topology


-- @@ L1119-1119 verbatim
namespace SphereSupport


-- @@ L1121-1121 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]


-- @@ L1123-1127 verbatim
open scoped Classical in
/-- The degree-one radial extension of a function on the unit sphere. -/
noncomputable def radialExtension (h : sphere (0 : E) 1 → ℝ) (x : E) : ℝ :=
  if hx : x = 0 then 0
  else ‖x‖ * h ⟨‖x‖⁻¹ • x, by simp [norm_smul, hx]⟩


-- @@ L1129-1133 verbatim
/-- The radial extension restricts to the original function on the unit sphere. -/
@[simp]
theorem radialExtension_coe (h : sphere (0 : E) 1 → ℝ) (p : sphere (0 : E) 1) :
    radialExtension h (p : E) = h p := by
  simp [radialExtension, ne_zero_of_mem_unit_sphere p, norm_eq_of_mem_sphere p]


-- @@ L1135-1159 verbatim
/-- The radial extension is positively homogeneous of degree one. -/
theorem radialExtension_smul_of_pos (h : sphere (0 : E) 1 → ℝ) (x : E) {t : ℝ}
    (ht : 0 < t) : radialExtension h (t • x) = t * radialExtension h x := by
  by_cases hx : x = 0
  · simp [hx, radialExtension]
  have htx : t • x ≠ 0 := smul_ne_zero ht.ne' hx
  have hnorm : ‖t • x‖ = t * ‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  have hunit (z : E) (hz : z ≠ 0) : ‖‖z‖⁻¹ • z‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg z))]
    exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)
  have hnormalized :
      (⟨‖t • x‖⁻¹ • (t • x), by
        rw [mem_sphere, dist_zero_right]
        exact hunit (t • x) htx⟩ : sphere (0 : E) 1) =
        ⟨‖x‖⁻¹ • x, by
          rw [mem_sphere, dist_zero_right]
          exact hunit x hx⟩ := by
    apply Subtype.ext
    simp only [hnorm, smul_smul]
    congr 1
    field_simp [ht.ne']
  simp only [radialExtension, dif_neg htx, dif_neg hx]
  rw [hnormalized, hnorm]
  ring


-- @@ L1161-1165 verbatim
/-- The contact map associated to a differentiable positively homogeneous function on the
ambient vector space. -/
noncomputable def homogeneousGradient [CompleteSpace E]
    (H : E → ℝ) (p : sphere (0 : E) 1) : E :=
  ∇ H (p : E)


-- @@ L1167-1192 verbatim
/-- Euler's identity for a differentiable function that is positively homogeneous of degree
one. This is the contact identity underlying the support-gradient construction. -/
theorem inner_homogeneousGradient [CompleteSpace E] (H : E → ℝ) (p : sphere (0 : E) 1)
    (hH : DifferentiableAt ℝ H (p : E))
    (hhom : ∀ (t : ℝ), 0 < t → H (t • (p : E)) = t * H p) :
    inner ℝ (homogeneousGradient H p) (p : E) = H p := by
  rw [homogeneousGradient, inner_gradient_left]
  have hline : HasDerivAt (fun t : ℝ ↦ H ((p : E) + t • (p : E)))
      (fderiv ℝ H (p : E) (p : E)) 0 := by
    have harg : HasDerivAt (fun t : ℝ ↦ (p : E) + t • (p : E)) (p : E) 0 :=
      by
        simpa only [id_eq, zero_add, one_smul] using
          ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const (p : E)).const_add (p : E)
    simpa [Function.comp_def] using
      hH.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) harg (by simp)
  have heq : (fun t : ℝ ↦ H ((p : E) + t • (p : E))) =ᶠ[𝓝 0]
      fun t : ℝ ↦ (1 + t) * H p := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with t ht
    rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
    calc
      H ((p : E) + t • (p : E)) = H ((1 + t) • (p : E)) := by rw [add_smul, one_smul]
      _ = (1 + t) * H p := hhom (1 + t) (by linarith [(abs_lt.mp ht).1])
  have hright : HasDerivAt (fun t : ℝ ↦ (1 + t) * H p) (H p) 0 := by
    simpa only [id_eq, one_mul] using
      ((hasDerivAt_id (𝕜 := ℝ) 0).const_add 1).mul_const (H p)
  exact (hline.congr_of_eventuallyEq heq.symm).unique hright


-- @@ L1194-1219 verbatim
/-- A differentiable positively homogeneous majorant has a unique contact point: its gradient.
This is the ambient form of the first-variation argument for support functions. -/
theorem eq_homogeneousGradient_of_global_support [CompleteSpace E] (H : E → ℝ)
    (p : sphere (0 : E) 1) (x : E) (hH : DifferentiableAt ℝ H (p : E))
    (hmajor : ∀ y : E, inner ℝ x y ≤ H y) (hcontact : inner ℝ x (p : E) = H p) :
    x = homogeneousGradient H p := by
  let G : E → ℝ := fun y ↦ H y - inner ℝ x y
  have hmin : IsMinOn G univ (p : E) := by
    intro y _
    dsimp [G]
    rw [hcontact]
    linarith [hmajor y]
  have hlinear : DifferentiableAt ℝ (fun y : E ↦ inner ℝ x y) (p : E) :=
    (innerSL ℝ x).differentiableAt
  have hderiv : fderiv ℝ H (p : E) = innerSL ℝ x := by
    have hzero := (hmin.isLocalMin Filter.univ_mem).fderiv_eq_zero
    have hinner_deriv :
        fderiv ℝ (fun y : E ↦ inner ℝ x y) (p : E) = innerSL ℝ x := by
      rw [show (fun y : E ↦ inner ℝ x y) = (innerSL ℝ x : E → ℝ) by funext y; rfl]
      exact (innerSL ℝ x).hasFDerivAt.fderiv
    rw [show G = fun y : E ↦ H y - inner ℝ x y by rfl,
      fderiv_fun_sub hH hlinear, hinner_deriv] at hzero
    exact sub_eq_zero.mp hzero
  apply ext_inner_right ℝ
  intro y
  rw [homogeneousGradient, inner_gradient_left, hderiv, innerSL_apply_apply]


-- @@ L1221-1247 verbatim
/-- The gradient of a differentiable convex function that is positively homogeneous of degree
one lies below that function in every direction. -/
theorem inner_homogeneousGradient_le [CompleteSpace E] (H : E → ℝ)
    (p : sphere (0 : E) 1) (y : E)
    (hconvex : ConvexOn ℝ univ H) (hH : DifferentiableAt ℝ H (p : E))
    (hhom : ∀ (t : ℝ), 0 < t → H (t • (p : E)) = t * H p) :
    inner ℝ (homogeneousGradient H p) y ≤ H y := by
  let e : ℝ →ᵃ[ℝ] E := AffineMap.lineMap (p : E) y
  have hline_convex : ConvexOn ℝ univ (H ∘ e) := by
    simpa [e] using hconvex.comp_affineMap e
  have he0 : e 0 = (p : E) := by simp [e]
  have he1 : e 1 = y := by simp [e]
  have he_deriv : HasDerivAt e (y - (p : E)) (0 : ℝ) := by
    simpa [e] using (AffineMap.hasDerivAt_lineMap (𝕜 := ℝ) (E := E)
      (a := (p : E)) (b := y) (x := (0 : ℝ)))
  have hline_deriv : HasDerivAt (H ∘ e) (fderiv ℝ H (p : E) (y - (p : E))) 0 := by
    exact hH.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) he_deriv he0.symm
  have hslope := hline_convex.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1)
    zero_lt_one hline_deriv
  have heuler : fderiv ℝ H (p : E) (p : E) = H p := by
    rw [← inner_homogeneousGradient H p hH hhom, homogeneousGradient,
      inner_gradient_left]
  have hslope' : fderiv ℝ H (p : E) (y - (p : E)) ≤ H y - H p := by
    simpa [slope, Function.comp_apply, he0, he1] using hslope
  rw [map_sub, heuler] at hslope'
  rw [homogeneousGradient, inner_gradient_left]
  linarith


-- @@ L1249-1280 verbatim
/-- Stereographic charts based at antipodal unit vectors are related by radial inversion. -/
theorem stereoToFun_stereoInvFunAux_neg {v w : E} (hv : ‖v‖ = 1)
    (hw : w ∈ (ℝ ∙ v)ᗮ) (hw0 : w ≠ 0) :
    stereoToFun v (stereoInvFunAux (-v) w) =
      (4 / ‖w‖ ^ 2) • (⟨w, hw⟩ : (ℝ ∙ v)ᗮ) := by
  rw [stereoToFun_apply, stereoInvFunAux_apply]
  have hprojw : (ℝ ∙ v)ᗮ.orthogonalProjection w = ⟨w, hw⟩ := by
    simpa using (ℝ ∙ v)ᗮ.orthogonalProjection_mem_subspace_eq_self
      (⟨w, hw⟩ : (ℝ ∙ v)ᗮ)
  have hprojneg : (ℝ ∙ v)ᗮ.orthogonalProjection (-v) = 0 := by
    rw [map_neg, Submodule.orthogonalProjection_orthogonalComplement_singleton_eq_zero]
    exact neg_zero
  have hinnerw : inner ℝ v w = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp hw
  have hinnerv : inner ℝ v v = 1 := by
    rw [real_inner_self_eq_norm_sq, hv]
    norm_num
  simp only [map_smul, map_add, hprojw, hprojneg, smul_zero, add_zero, innerSL_apply_apply,
    hinnerw, hinnerv, inner_neg_right, smul_smul]
  have hwsub : (⟨w, hw⟩ : (ℝ ∙ v)ᗮ) ≠ 0 := by
    intro h
    exact hw0 (congr_arg Subtype.val h)
  rw [smul_left_inj hwsub]
  simp only [smul_eq_mul]
  have hdenom :
      1 - (‖w‖ ^ 2 + 4)⁻¹ * ((‖w‖ ^ 2 - 4) * -1) =
        2 * ‖w‖ ^ 2 / (‖w‖ ^ 2 + 4) := by
    field_simp
    ring
  simp only [zero_add]
  rw [hdenom]
  field_simp [norm_ne_zero_iff.mpr hw0]


-- @@ L1282-1284 verbatim
/-- The closed convex set cut out by the supporting half-spaces prescribed by `h`. -/
def body (h : sphere (0 : E) 1 → ℝ) : Set E :=
  {x | ∀ p : sphere (0 : E) 1, inner ℝ (p : E) x ≤ h p}


-- @@ L1286-1290 verbatim
/-- A support-function body is convex. -/
theorem body_convex (h : sphere (0 : E) 1 → ℝ) : Convex ℝ (body h) := by
  rw [body, setOf_forall]
  exact convex_iInter fun p ↦
    convex_halfSpace_le (innerSL ℝ (p : E)).toLinearMap.isLinear (h p)


-- @@ L1292-1295 verbatim
/-- A support-function body is closed. -/
theorem body_isClosed (h : sphere (0 : E) 1 → ℝ) : IsClosed (body h) := by
  rw [body, setOf_forall]
  exact isClosed_iInter fun p ↦ isClosed_Iic.preimage (innerSL ℝ (p : E)).continuous


-- @@ L1297-1309 verbatim
/-- If `h` is bounded below by a positive constant, its support-function body has nonempty
interior. -/
theorem body_interior_nonempty (h : sphere (0 : E) 1 → ℝ) {r : ℝ} (hr : 0 < r)
    (hlower : ∀ p, r ≤ h p) : (interior (body h)).Nonempty := by
  have hball : ball (0 : E) r ⊆ body h := by
    intro x hx p
    calc
      inner ℝ (p : E) x ≤ ‖(p : E)‖ * ‖x‖ := real_inner_le_norm _ _
      _ = ‖x‖ := by rw [norm_eq_of_mem_sphere p, one_mul]
      _ ≤ r := (by simpa [mem_ball, dist_zero_right] using hx : ‖x‖ < r).le
      _ ≤ h p := hlower p
  refine ⟨0, mem_interior_iff_mem_nhds.mpr ?_⟩
  exact Filter.mem_of_superset (ball_mem_nhds 0 hr) hball


-- @@ L1311-1331 verbatim
/-- A uniform upper bound on `h` bounds its support-function body. -/
theorem body_isBounded (h : sphere (0 : E) 1 → ℝ) {R : ℝ} (hupper : ∀ p, h p ≤ R) :
    Bornology.IsBounded (body h) := by
  rw [Metric.isBounded_iff_subset_closedBall (0 : E)]
  refine ⟨max R 0, ?_⟩
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  by_cases hx0 : x = 0
  · simp [hx0]
  · have hxnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx0
    let p : sphere (0 : E) 1 := ⟨‖x‖⁻¹ • x, by
      simp [norm_smul, hxnorm]⟩
    have hp : inner ℝ (p : E) x ≤ h p := hx p
    have hinner : inner ℝ (p : E) x = ‖x‖ := by
      change inner ℝ (‖x‖⁻¹ • x) x = ‖x‖
      rw [real_inner_smul_left, real_inner_self_eq_norm_mul_norm]
      calc
        ‖x‖⁻¹ * (‖x‖ * ‖x‖) = (‖x‖⁻¹ * ‖x‖) * ‖x‖ := by ring
        _ = ‖x‖ := by rw [inv_mul_cancel₀ hxnorm, one_mul]
    rw [hinner] at hp
    exact (hp.trans (hupper p)).trans (le_max_left _ _)


-- @@ L1333-1337 verbatim
/-- In a proper real inner-product space, a uniformly upper-bounded support function cuts out a
compact body. -/
theorem body_isCompact [ProperSpace E] (h : sphere (0 : E) 1 → ℝ) {R : ℝ}
    (hupper : ∀ p, h p ≤ R) : IsCompact (body h) :=
  Metric.isCompact_iff_isClosed_bounded.mpr ⟨body_isClosed h, body_isBounded h hupper⟩


-- @@ L1339-1343 verbatim
/-- A continuous function on the unit sphere cuts out a compact support-function body. -/
theorem body_isCompact_of_continuous [ProperSpace E] (h : sphere (0 : E) 1 → ℝ)
    (hh : Continuous h) : IsCompact (body h) := by
  obtain ⟨R, hR⟩ := (isCompact_range hh).bddAbove
  exact body_isCompact h fun p ↦ hR ⟨p, rfl⟩


-- @@ L1345-1375 verbatim
/-- Every boundary point of a closed convex body with nonempty interior admits an outward unit
supporting normal. -/
theorem exists_unit_supporting_normal {K : Set E} (hconvex : Convex ℝ K)
    [CompleteSpace E] (hclosed : IsClosed K) (hinterior : (interior K).Nonempty) {x : E}
    (hx : x ∈ frontier K) :
    ∃ p : sphere (0 : E) 1, ∀ y ∈ K, inner ℝ (p : E) y ≤ inner ℝ (p : E) x := by
  have hx_not_interior : x ∉ interior K := by
    rw [frontier] at hx
    exact hx.2
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hconvex.interior isOpen_interior
    hx_not_interior
  have hf0 : f ≠ 0 := by
    intro hzero
    obtain ⟨y, hy⟩ := hinterior
    simpa [hzero] using hf y hy
  let v : E := (InnerProductSpace.toDual ℝ E).symm f
  have hv0 : v ≠ 0 := (InnerProductSpace.toDual ℝ E).symm.map_ne_zero_iff.mpr hf0
  let p : sphere (0 : E) 1 := ⟨‖v‖⁻¹ • v, by
    simp [norm_smul, hv0]⟩
  refine ⟨p, fun y hy ↦ ?_⟩
  have hhalf_closed : IsClosed {z : E | f z ≤ f x} :=
    isClosed_Iic.preimage f.continuous
  have hhalf : closure (interior K) ⊆ {z : E | f z ≤ f x} :=
    closure_minimal (fun z hz ↦ (hf z hz).le) hhalf_closed
  have hclosure : closure (interior K) = K := by
    rw [hconvex.closure_interior_eq_closure_of_nonempty_interior hinterior,
      hclosed.closure_eq]
  have hfy : f y ≤ f x := hhalf (hclosure.symm ▸ hy)
  change inner ℝ (‖v‖⁻¹ • v) y ≤ inner ℝ (‖v‖⁻¹ • v) x
  simpa only [real_inner_smul_left, v, InnerProductSpace.toDual_symm_apply] using
    mul_le_mul_of_nonneg_left hfy (inv_nonneg.mpr (norm_nonneg v))


-- @@ L1377-1387 verbatim
/-- Pointwise contact and cross-support inequalities place every parametrized point in the
support-function body and make it attain the corresponding supporting hyperplane. -/
theorem contact_mem_body (h : sphere (0 : E) 1 → ℝ) (F : sphere (0 : E) 1 → E)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    (hcross : ∀ (p q : sphere (0 : E) 1), inner ℝ (F p) (q : E) ≤ h q) :
    ∀ p, F p ∈ body h ∧ inner ℝ (F p) (p : E) = h p ∧
      ∀ x ∈ body h, inner ℝ x (p : E) ≤ h p := by
  intro p
  refine ⟨fun q ↦ ?_, hcontact p, fun x hx ↦ ?_⟩
  · simpa [real_inner_comm] using hcross p q
  · simpa [real_inner_comm] using hx p


-- @@ L1389-1418 verbatim
/-- A parametrized contact point lies on the frontier of the support-function body. -/
theorem contact_mem_frontier (h : sphere (0 : E) 1 → ℝ) (F : sphere (0 : E) 1 → E)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    (hcross : ∀ (p q : sphere (0 : E) 1), inner ℝ (F p) (q : E) ≤ h q) :
    ∀ p, F p ∈ frontier (body h) := by
  intro p
  rw [frontier, (body_isClosed h).closure_eq]
  refine ⟨(contact_mem_body h F hcontact hcross p).1, ?_⟩
  intro hpinterior
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hpinterior) with
    ⟨ε, hε, hball⟩
  let y := F p + (ε / 2) • (p : E)
  have hyball : y ∈ ball (F p) ε := by
    rw [mem_ball, dist_eq_norm]
    simp [y, norm_smul, norm_eq_of_mem_sphere p]
    rw [abs_of_pos hε]
    linarith
  have hybody : y ∈ body h := hball hyball
  have hy_support := hybody p
  have hpp : inner ℝ (p : E) (p : E) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p]
    norm_num
  have hcontact' : inner ℝ (p : E) (F p) = h p := by
    rw [real_inner_comm]
    exact hcontact p
  have hy_inner : inner ℝ (p : E) y = h p + ε / 2 := by
    rw [show y = F p + (ε / 2) • (p : E) by rfl, inner_add_right,
      hcontact', real_inner_smul_right, hpp, mul_one]
  rw [hy_inner] at hy_support
  linarith


-- @@ L1420-1445 verbatim
/-- If every exposed contact face is the prescribed singleton, the contact parametrization covers
the whole frontier of its support-function body. -/
theorem range_eq_frontier_of_unique_contact [CompleteSpace E]
    (h : sphere (0 : E) 1 → ℝ) (F : sphere (0 : E) 1 → E)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    (hcross : ∀ (p q : sphere (0 : E) 1), inner ℝ (F p) (q : E) ≤ h q)
    (hinterior : (interior (body h)).Nonempty)
    (hunique : ∀ (p : sphere (0 : E) 1) (x : E), x ∈ body h →
      inner ℝ (p : E) x = h p → x = F p) :
    range F = frontier (body h) := by
  apply Subset.antisymm
  · rintro _ ⟨p, rfl⟩
    exact contact_mem_frontier h F hcontact hcross p
  · intro x hx
    obtain ⟨p, hp⟩ := exists_unit_supporting_normal (body_convex h) (body_isClosed h)
      hinterior hx
    have hxbody : x ∈ body h := by
      rw [frontier, (body_isClosed h).closure_eq] at hx
      exact hx.1
    have hFpbody := (contact_mem_body h F hcontact hcross p).1
    have hle : h p ≤ inner ℝ (p : E) x := by
      rw [← hcontact p, real_inner_comm]
      exact hp (F p) hFpbody
    have hxeq : inner ℝ (p : E) x = h p :=
      le_antisymm (hxbody p) hle
    exact ⟨p, (hunique p x hxbody hxeq).symm⟩


-- @@ L1447-1463 verbatim
/-- A contact point is uniquely determined once its displacement from the prescribed point is
orthogonal to every tangent vector. This is the linear-algebra step in the first-variation
argument for support parametrizations. -/
theorem eq_contact_of_tangent_orthogonal (h : sphere (0 : E) 1 → ℝ)
    (F : sphere (0 : E) 1 → E)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    {p : sphere (0 : E) 1} {x : E} (hxeq : inner ℝ (p : E) x = h p)
    (htangent : ∀ v : E, v ∈ (ℝ ∙ (p : E))ᗮ → inner ℝ (x - F p) v = 0) :
    x = F p := by
  have hdisplacement : x - F p ∈ (ℝ ∙ (p : E))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, hxeq]
    have hpcontact : inner ℝ (p : E) (F p) = h p := by
      rw [real_inner_comm]
      exact hcontact p
    rw [hpcontact, sub_self]
  exact sub_eq_zero.mp (inner_self_eq_zero.mp
    (htangent (x - F p) hdisplacement))


-- @@ L1465-1477 verbatim
/-- First variation at every exposed contact point, together with contact and cross-support,
forces a parametrization to cover the whole frontier. -/
theorem range_eq_frontier_of_first_variation [CompleteSpace E]
    (h : sphere (0 : E) 1 → ℝ) (F : sphere (0 : E) 1 → E)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    (hcross : ∀ (p q : sphere (0 : E) 1), inner ℝ (F p) (q : E) ≤ h q)
    (hinterior : (interior (body h)).Nonempty)
    (hstationary : ∀ (p : sphere (0 : E) 1) (x : E), x ∈ body h →
      inner ℝ (p : E) x = h p → ∀ v : E, v ∈ (ℝ ∙ (p : E))ᗮ →
        inner ℝ (x - F p) v = 0) :
    range F = frontier (body h) :=
  range_eq_frontier_of_unique_contact h F hcontact hcross hinterior fun p x hx hxeq ↦
    eq_contact_of_tangent_orthogonal h F hcontact hxeq (hstationary p x hx hxeq)


-- @@ L1479-1496 verbatim
/-- Contact, cross-support, and first variation produce the compact convex body represented by a
support function. This packages the set-theoretic part of the support-gradient construction. -/
theorem exists_compact_body_of_first_variation [ProperSpace E] [CompleteSpace E]
    (h : sphere (0 : E) 1 → ℝ) (F : sphere (0 : E) 1 → E)
    (hh : Continuous h) {r : ℝ} (hr : 0 < r) (hlower : ∀ p, r ≤ h p)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    (hcross : ∀ (p q : sphere (0 : E) 1), inner ℝ (F p) (q : E) ≤ h q)
    (hstationary : ∀ (p : sphere (0 : E) 1) (x : E), x ∈ body h →
      inner ℝ (p : E) x = h p → ∀ v : E, v ∈ (ℝ ∙ (p : E))ᗮ →
        inner ℝ (x - F p) v = 0) :
    ∃ K : Set E, Convex ℝ K ∧ IsCompact K ∧ (interior K).Nonempty ∧
      range F = frontier K ∧ ∀ p, F p ∈ K ∧ inner ℝ (F p) (p : E) = h p ∧
        ∀ x ∈ K, inner ℝ x (p : E) ≤ h p := by
  refine ⟨body h, body_convex h, body_isCompact_of_continuous h hh,
    body_interior_nonempty h hr hlower,
    range_eq_frontier_of_first_variation h F hcontact hcross
      (body_interior_nonempty h hr hlower) hstationary, ?_⟩
  exact contact_mem_body h F hcontact hcross


-- @@ L1498-1508 verbatim
/-- Strict cross-support separates the parametrizing normals, so the contact map is injective. -/
theorem injective_of_strictCross (h : sphere (0 : E) 1 → ℝ)
    (F : sphere (0 : E) 1 → E)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    (hstrict : ∀ (p q : sphere (0 : E) 1), p ≠ q → inner ℝ (F p) (q : E) < h q) :
    Function.Injective F := by
  intro p q hpq
  by_contra hpne
  have hpq_strict := hstrict p q hpne
  rw [hpq, hcontact q] at hpq_strict
  exact (lt_irrefl _ hpq_strict)


-- @@ L1510-1516 verbatim
/-- A continuous strict contact parametrization of the unit sphere is a topological embedding. -/
theorem isEmbedding_of_strictCross [ProperSpace E] (h : sphere (0 : E) 1 → ℝ)
    (F : sphere (0 : E) 1 → E) (hF : Continuous F)
    (hcontact : ∀ p, inner ℝ (F p) (p : E) = h p)
    (hstrict : ∀ (p q : sphere (0 : E) 1), p ≠ q → inner ℝ (F p) (q : E) < h q) :
    Topology.IsEmbedding F :=
  (hF.isClosedEmbedding (injective_of_strictCross h F hcontact hstrict)).isEmbedding


-- @@ L1518-1518 verbatim
end SphereSupport


-- @@ L1520-1520 verbatim
end SupportFunctionSphereSection


-- @@ L1522-1522 verbatim
/-! ## Flattened from `FormalConjectures/Other/CaratheodoryLoewnerCounterexample/Defs.lean` -/


-- @@ L1524-1524 verbatim
section CounterexampleDefsSection


-- @@ L1526-1534 verbatim
/-!
# Definitions for the announced smooth Carathéodory–Loewner counterexamples

This file records the explicit planar family, its stereographic chart, and the support-function
predicate used in the counterexample announced by Levent Alpöge on 19 August 2026.

*Reference:*
- [L. Alpöge, X post 2089971359921156203](https://x.com/__alpoge__/status/2089971359921156203)
-/


-- @@ L1536-1536 verbatim
open scoped ContDiff EuclideanGeometry Manifold

-- @@ L1537-1537 verbatim
open Set Metric


-- @@ L1539-1539 verbatim
namespace CaratheodoryLoewnerCounterexample


-- @@ L1541-1541 verbatim
open CaratheodoryConjecture LoewnerConjecture


-- @@ L1543-1546 verbatim
/-- The periodic real-valued function used in the announced counterexample. -/
noncomputable def counterexampleSeed (z : ℂ) : ℝ :=
  -Real.cos (2 * z.re) / 4 + 3 * Real.cos (2 * z.im) / 10 -
    Real.cos (4 * z.im) / 32 + Real.sin z.re * Real.sin z.im


-- @@ L1548-1550 verbatim
/-- The seed is invariant under the sign ambiguity of a square root. -/
theorem counterexampleSeed_neg (z : ℂ) : counterexampleSeed (-z) = counterexampleSeed z := by
  simp [counterexampleSeed]


-- @@ L1552-1560 verbatim
/-- The announced family `g_k` of smooth functions on the complex plane.

The use of the principal complex power chooses a square-root branch when `k` is odd. The seed is
even, so the resulting real-valued expression is independent of the sign of that square root. -/
noncomputable def counterexample (k : ℕ) (z : ℂ) : ℝ :=
  let r := ‖z‖
  let w := Complex.cpow (100 / star z) ((k : ℂ) / 2)
  r ^ 2 * Real.exp (-Real.rpow r (-(1 : ℝ) / 4) * Real.exp (-(r ^ 2))) *
      counterexampleSeed w / (1 + r ^ 2) + 10 ^ 10


-- @@ L1562-1564 verbatim
/-- Every member of the family takes the constant support value at the origin. -/
theorem counterexample_zero (k : ℕ) : counterexample k 0 = 10 ^ 10 := by
  simp [counterexample]


-- @@ L1566-1570 expanded
/-- The north pole used to fix the stereographic chart for the global counterexample. -/
noncomputable def counterexampleNorthPole : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  ⟨EuclideanSpace.single (2 : Fin 3) 1,
    by
    rw [mem_sphere, dist_zero_right]
    simp⟩


-- @@ L1572-1580 expanded
/-- The inverse stereographic chart in which the formula `counterexample 2` is written.

Mathlib's stereographic coordinate has a conventional factor of two. Scaling its target
coordinate by two makes the pullback of the round metric equal to
`4 / (1 + ‖z‖ ^ 2) ^ 2` times the Euclidean metric. -/
noncomputable def counterexampleSphereChart (z : ℂ) : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨finrank_euclideanSpace_fin⟩
  (stereographic' 2 counterexampleNorthPole).symm (2 • Complex.orthonormalBasisOneI.repr z)


-- @@ L1582-1587 verbatim
/-- The origin of the planar chart represents the south pole. This test fixes the scale and sign
convention in `counterexampleSphereChart`. -/
theorem counterexampleSphereChart_zero :
    counterexampleSphereChart 0 = -counterexampleNorthPole := by
  apply Subtype.ext
  simp [counterexampleSphereChart, stereographic'_symm_apply]


-- @@ L1589-1598 expanded
/-- `F` parametrizes the supporting point of `K` with outer unit normal `p`, and `h p` is
the corresponding support value.

The final inequality says that the hyperplane through `F p` perpendicular to `p` supports
the whole body. Requiring `F p ∈ K` makes the supremum attained and avoids conventions for
`sSup ∅`. -/
def IsSupportParametrization (h : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ)
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (K : Set (EuclideanSpace ℝ (Fin 3))) : Prop :=
  ∀ p,
    F p ∈ K ∧
      inner ℝ (F p) (p : EuclideanSpace ℝ (Fin 3)) = h p ∧
        ∀ x ∈ K, inner ℝ x (p : EuclideanSpace ℝ (Fin 3)) ≤ h p


-- @@ L1600-1600 verbatim
end CaratheodoryLoewnerCounterexample


-- @@ L1602-1602 verbatim
end CounterexampleDefsSection


-- @@ L1604-1604 verbatim
/-! ## Flattened from `FormalConjectures/Other/CaratheodoryLoewnerCounterexample/Smooth.lean` -/


-- @@ L1606-1606 verbatim
section CounterexampleSmoothSection


-- @@ L1608-1616 verbatim
/-!
# Smoothness of the announced Carathéodory–Loewner counterexamples

The proof is split between the punctured plane, where branch independence is the main issue, and
the origin, where the flat exponential dominates every derivative.

*Reference:*
- [L. Alpöge, X post 2089971359921156203](https://x.com/__alpoge__/status/2089971359921156203)
-/


-- @@ L1618-1618 verbatim
open Filter Topology

-- @@ L1619-1619 verbatim
open scoped ContDiff


-- @@ L1621-1621 verbatim
namespace CaratheodoryLoewnerCounterexample


-- @@ L1623-1623 verbatim
noncomputable section


-- @@ L1625-1634 verbatim
/-- The trigonometric seed is smooth as a real-valued function of the complex variable. -/
theorem counterexampleSeed_contDiff : ContDiff ℝ ∞ counterexampleSeed := by
  unfold counterexampleSeed
  have hre : ContDiff ℝ ∞ (fun z : ℂ ↦ z.re) := by
    rw [show (fun z : ℂ ↦ z.re) = (Complex.reCLM : ℂ → ℝ) by funext z; rfl]
    exact Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ (fun z : ℂ ↦ z.im) := by
    rw [show (fun z : ℂ ↦ z.im) = (Complex.imCLM : ℂ → ℝ) by funext z; rfl]
    exact Complex.imCLM.contDiff
  fun_prop


-- @@ L1636-1640 verbatim
@[fun_prop]
private theorem sin_hasTemperateGrowth : Function.HasTemperateGrowth Real.sin := by
  refine ⟨Real.contDiff_sin, fun n ↦ ⟨0, 1, fun x ↦ ?_⟩⟩
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, pow_zero, mul_one]
    using Real.abs_iteratedDeriv_sin_le_one n x


-- @@ L1642-1646 verbatim
@[fun_prop]
private theorem cos_hasTemperateGrowth : Function.HasTemperateGrowth Real.cos := by
  refine ⟨Real.contDiff_cos, fun n ↦ ⟨0, 1, fun x ↦ ?_⟩⟩
  simpa only [norm_iteratedFDeriv_eq_norm_iteratedDeriv, Real.norm_eq_abs, pow_zero, mul_one]
    using Real.abs_iteratedDeriv_cos_le_one n x


-- @@ L1648-1658 verbatim
private theorem counterexampleSeed_hasTemperateGrowth :
    Function.HasTemperateGrowth counterexampleSeed := by
  unfold counterexampleSeed
  have hre : Function.HasTemperateGrowth (fun z : ℂ ↦ z.re) := by
    rw [show (fun z : ℂ ↦ z.re) = (Complex.reCLM : ℂ → ℝ) by funext z; rfl]
    exact Complex.reCLM.hasTemperateGrowth
  have him : Function.HasTemperateGrowth (fun z : ℂ ↦ z.im) := by
    rw [show (fun z : ℂ ↦ z.im) = (Complex.imCLM : ℂ → ℝ) by funext z; rfl]
    exact Complex.imCLM.hasTemperateGrowth
  simp only [div_eq_mul_inv]
  fun_prop


-- @@ L1660-1662 verbatim
private def cpowFalling : ℂ → ℕ → ℂ
  | _, 0 => 1
  | c, n + 1 => c * cpowFalling (c - 1) n


-- @@ L1664-1683 verbatim
private theorem iteratedDeriv_cpow_const (c : ℂ) (n : ℕ) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) :
    iteratedDeriv n (fun w : ℂ ↦ w ^ c) z = cpowFalling c n * z ^ (c - n) := by
  induction n generalizing c with
  | zero => simp [cpowFalling]
  | succ n ih =>
      rw [iteratedDeriv_succ']
      have hderiv : deriv (fun w : ℂ ↦ w ^ c) =ᶠ[𝓝 z] fun w ↦ c * w ^ (c - 1) := by
        filter_upwards [Complex.isOpen_slitPlane.mem_nhds hz] with w hw
        simpa using ((hasDerivAt_id w).cpow_const hw).deriv
      rw [hderiv.iteratedDeriv_eq n]
      have hsmooth : ContDiffAt ℂ n (fun w : ℂ ↦ w ^ (c - 1)) z :=
        (analyticAt_id.cpow analyticAt_const hz).contDiffAt.of_le (mod_cast le_top)
      rw [iteratedDeriv_const_mul c hsmooth, ih (c - 1)]
      have hexp : c - 1 - (n : ℂ) = c - ((n + 1 : ℕ) : ℂ) := by
        norm_num [Nat.cast_add]
        ring
      change c * (cpowFalling (c - 1) n * z ^ (c - 1 - (n : ℂ))) =
        (c * cpowFalling (c - 1) n) * z ^ (c - ((n + 1 : ℕ) : ℂ))
      rw [mul_assoc, hexp]


-- @@ L1685-1698 verbatim
private theorem norm_iteratedFDeriv_cpow_const (c : ℝ) (n : ℕ) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) :
    ‖iteratedFDeriv ℝ n (fun w : ℂ ↦ w ^ (c : ℂ)) z‖ =
      ‖cpowFalling (c : ℂ) n‖ * ‖z‖ ^ (c - n) := by
  have hsmooth : ContDiffAt ℂ n (fun w : ℂ ↦ w ^ (c : ℂ)) z :=
    (analyticAt_id.cpow analyticAt_const hz).contDiffAt.of_le (mod_cast le_top)
  rw [← hsmooth.restrictScalars_iteratedFDeriv (𝕜 := ℝ), Function.comp_apply,
    ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_cpow_const (c : ℂ) n hz,
    norm_mul]
  congr 1
  convert Complex.norm_cpow_real z (c - n) using 1
  push_cast
  ring


-- @@ L1700-1705 verbatim
private theorem cpow_pos_mul (r : ℝ) (hr : 0 < r) {z c : ℂ} (hz : z ≠ 0) :
    ((r : ℂ) * z) ^ c = (r : ℂ) ^ c * z ^ c := by
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hz),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne'),
    Complex.cpow_def_of_ne_zero hz, Complex.log_ofReal_mul hr hz, add_mul, Complex.exp_add,
    Complex.ofReal_log hr.le]


-- @@ L1707-1716 verbatim
private theorem div_cpow_eq (k : ℕ) {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    (100 / z) ^ ((k : ℂ) / 2) =
      (100 : ℂ) ^ ((k : ℂ) / 2) * z ^ (-((k : ℂ) / 2)) := by
  rw [div_eq_mul_inv]
  change (((100 : ℝ) : ℂ) * z⁻¹) ^ ((k : ℂ) / 2) =
    ((100 : ℂ) ^ ((k : ℂ) / 2)) * z ^ (-((k : ℂ) / 2))
  rw [cpow_pos_mul 100 (by norm_num)
      (inv_ne_zero (Complex.slitPlane_ne_zero hz)),
    Complex.inv_cpow z _ (Complex.slitPlane_arg_ne_pi hz), Complex.cpow_neg]
  norm_num


-- @@ L1718-1719 verbatim
private def negConjLIE : ℂ ≃ₗᵢ[ℝ] ℂ :=
  Complex.conjLIE.trans (LinearIsometryEquiv.neg ℝ)


-- @@ L1721-1723 verbatim
@[simp]
private theorem negConjLIE_apply (z : ℂ) : negConjLIE z = -star z := by
  rfl


-- @@ L1725-1726 verbatim
private def branchPhase (k : ℕ) (a : ℂ) (z : ℂ) : ℂ :=
  a * (100 : ℂ) ^ ((k : ℂ) / 2) * z ^ (-((k : ℂ) / 2))


-- @@ L1728-1745 verbatim
private theorem norm_iteratedFDeriv_branchPhase (k n : ℕ) (a : ℂ) {z : ℂ}
    (hz : z ∈ Complex.slitPlane) :
    ‖iteratedFDeriv ℝ n (branchPhase k a) z‖ =
      ‖a * (100 : ℂ) ^ ((k : ℂ) / 2)‖ *
        ‖cpowFalling (-((k : ℂ) / 2)) n‖ * ‖z‖ ^ (-(k : ℝ) / 2 - n) := by
  have hsmooth : ContDiffAt ℝ n (fun w : ℂ ↦ w ^ (-((k : ℂ) / 2))) z :=
    ((analyticAt_id.cpow analyticAt_const hz).restrictScalars.contDiffAt).of_le
      (mod_cast le_top)
  have hc : -((k : ℂ) / 2) = ((-(k : ℝ) / 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [show branchPhase k a = fun w ↦
      (a * (100 : ℂ) ^ ((k : ℂ) / 2)) • w ^ (-((k : ℂ) / 2)) by
        funext w; simp [branchPhase],
    iteratedFDeriv_const_smul_apply' hsmooth, norm_smul, hc,
    norm_iteratedFDeriv_cpow_const (-(k : ℝ) / 2) n hz]
  push_cast
  ring


-- @@ L1747-1751 verbatim
private theorem norm_iteratedFDeriv_branchPhase_comp_conj (k n : ℕ) (a : ℂ) (z : ℂ) :
    ‖iteratedFDeriv ℝ n (branchPhase k a ∘ Complex.conjLIE) z‖ =
      ‖iteratedFDeriv ℝ n (branchPhase k a) (star z)‖ := by
  simpa [Complex.conjLIE_apply] using
    Complex.conjLIE.norm_iteratedFDeriv_comp_right (branchPhase k a) z n


-- @@ L1753-1756 verbatim
private theorem norm_iteratedFDeriv_branchPhase_comp_negConj (k n : ℕ) (a : ℂ) (z : ℂ) :
    ‖iteratedFDeriv ℝ n (branchPhase k a ∘ negConjLIE) z‖ =
      ‖iteratedFDeriv ℝ n (branchPhase k a) (-star z)‖ := by
  simpa using negConjLIE.norm_iteratedFDeriv_comp_right (branchPhase k a) z n


-- @@ L1758-1851 verbatim
private theorem branchOscillatory_iteratedFDeriv_polynomial_bound (k n : ℕ) (a : ℂ)
    (ha : ‖a‖ = 1) (e : ℂ ≃ₗᵢ[ℝ] ℂ) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ z : ℂ, e z ∈ Complex.slitPlane → ‖z‖ ≤ 1 →
      ‖iteratedFDeriv ℝ n (counterexampleSeed ∘ branchPhase k a ∘ e) z‖ ≤
        C * ‖z‖ ^ (-(N : ℝ)) := by
  obtain ⟨d, C, hC, hseed⟩ :=
    counterexampleSeed_hasTemperateGrowth.norm_iteratedFDeriv_le_uniform n
  let P := k + n
  let B := 1 + ‖(100 : ℂ) ^ ((k : ℂ) / 2)‖ *
    ∑ i ∈ Finset.range (n + 1), ‖cpowFalling (-((k : ℂ) / 2)) i‖
  refine ⟨P * (d + n), Nat.factorial n * C * (1 + B) ^ d * B ^ n,
    by positivity, ?_⟩
  intro z hz hz_one
  have hz0 : z ≠ 0 := fun h ↦ Complex.slitPlane_ne_zero hz (by simp [h])
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hB : 1 ≤ B := by
    simp only [B, le_add_iff_nonneg_right]
    positivity
  let R : ℝ := ‖z‖ ^ (-(P : ℝ))
  have hR : 1 ≤ R := by
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hz_one
      (neg_nonpos.mpr (Nat.cast_nonneg P))
  let Q := B * R
  have hQ : 1 ≤ Q := one_le_mul_of_one_le_of_one_le hB hR
  have hphase (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i (branchPhase k a ∘ e) z‖ ≤ Q := by
    rw [e.norm_iteratedFDeriv_comp_right]
    rw [norm_iteratedFDeriv_branchPhase k i a hz]
    rw [LinearIsometryEquiv.norm_map]
    have hcoeff : ‖a * (100 : ℂ) ^ ((k : ℂ) / 2)‖ *
        ‖cpowFalling (-((k : ℂ) / 2)) i‖ ≤ B := by
      rw [norm_mul, ha, one_mul]
      have hi_mem : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hi)
      have hsum : ‖cpowFalling (-((k : ℂ) / 2)) i‖ ≤
          ∑ j ∈ Finset.range (n + 1), ‖cpowFalling (-((k : ℂ) / 2)) j‖ :=
        Finset.single_le_sum (f := fun j ↦ ‖cpowFalling (-((k : ℂ) / 2)) j‖)
          (fun _ _ ↦ norm_nonneg _) hi_mem
      dsimp only [B]
      nlinarith [mul_le_mul_of_nonneg_left hsum (norm_nonneg ((100 : ℂ) ^ ((k : ℂ) / 2)))]
    have hexp : ‖z‖ ^ (-(k : ℝ) / 2 - i) ≤ R := by
      apply Real.rpow_le_rpow_of_exponent_ge hr hz_one
      dsimp only [R, P]
      have hiR : (i : ℝ) ≤ n := by exact_mod_cast hi
      have hkR : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
      push_cast
      linarith
    dsimp only [Q]
    exact mul_le_mul hcoeff hexp (Real.rpow_nonneg (norm_nonneg z) _) (by positivity)
  let s := e ⁻¹' Complex.slitPlane
  have hs : IsOpen s := Complex.isOpen_slitPlane.preimage e.continuous
  have hzs : z ∈ s := hz
  have hinner : ContDiffOn ℝ ∞ (branchPhase k a ∘ e) s := by
    intro x hx
    apply ContDiffAt.contDiffWithinAt
    apply ContDiffAt.comp x ?_ e.contDiff.contDiffAt
    unfold branchPhase
    exact (contDiffAt_const.mul
      ((analyticAt_id.cpow analyticAt_const hx).restrictScalars.contDiffAt))
  have houter (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i counterexampleSeed Set.univ
          ((branchPhase k a ∘ e) z)‖ ≤ C * (1 + Q) ^ d := by
    rw [iteratedFDerivWithin_univ]
    refine (hseed i hi _).trans ?_
    gcongr
    simpa only [norm_iteratedFDeriv_zero] using hphase 0 (Nat.zero_le n)
  have hinner_bound (i : ℕ) (hi : 1 ≤ i) (hin : i ≤ n) :
      ‖iteratedFDerivWithin ℝ i (branchPhase k a ∘ e) s z‖ ≤ Q ^ i := by
    rw [iteratedFDerivWithin_of_isOpen i hs hzs]
    exact (hphase i hin).trans (le_self_pow₀ hQ (Nat.ne_of_gt hi))
  have hcomp := norm_iteratedFDerivWithin_comp_le
    counterexampleSeed_contDiff.contDiffOn hinner (mod_cast le_top)
    uniqueDiffOn_univ hs.uniqueDiffOn (fun _ _ ↦ Set.mem_univ _) hzs houter hinner_bound
  rw [iteratedFDerivWithin_of_isOpen n hs hzs] at hcomp
  have h_one_add : 1 + Q ≤ (1 + B) * R := by
    dsimp only [Q]
    nlinarith [mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr hR)]
  have hRpow : R ^ (d + n) = ‖z‖ ^ (-((P * (d + n) : ℕ) : ℝ)) := by
    dsimp only [R]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z)]
    congr 1
    push_cast
    ring
  calc
    ‖iteratedFDeriv ℝ n (counterexampleSeed ∘ branchPhase k a ∘ e) z‖
        ≤ Nat.factorial n * (C * (1 + Q) ^ d) * Q ^ n := hcomp
    _ ≤ Nat.factorial n * (C * ((1 + B) * R) ^ d) * (B * R) ^ n := by
      gcongr
    _ = (Nat.factorial n * C * (1 + B) ^ d * B ^ n) * (R ^ d * R ^ n) := by
      rw [mul_pow, mul_pow]
      ring
    _ = (Nat.factorial n * C * (1 + B) ^ d * B ^ n) * R ^ (d + n) := by
      rw [pow_add]
    _ = (Nat.factorial n * C * (1 + B) ^ d * B ^ n) *
        ‖z‖ ^ (-((P * (d + n) : ℕ) : ℝ)) := by rw [hRpow]


-- @@ L1853-1854 verbatim
private def oscillatoryFactor (k : ℕ) (z : ℂ) : ℝ :=
  counterexampleSeed (Complex.cpow (100 / star z) ((k : ℂ) / 2))


-- @@ L1856-1860 verbatim
private theorem oscillatoryFactor_eq_plus (k : ℕ) {z : ℂ}
    (hz : star z ∈ Complex.slitPlane) :
    oscillatoryFactor k z = counterexampleSeed ((branchPhase k 1 ∘ Complex.conjLIE) z) := by
  simpa [oscillatoryFactor, Function.comp_apply, Complex.conjLIE_apply, branchPhase] using
    congrArg counterexampleSeed (div_cpow_eq k hz)


-- @@ L1862-1863 verbatim
private def radialArgument (z : ℂ) : ℝ :=
  Complex.normSq z * Real.exp (8 * Complex.normSq z)


-- @@ L1865-1866 verbatim
private def radialFlat (z : ℂ) : ℝ :=
  Real.flatRpowExp (1 / 8 : ℝ) 1 (radialArgument z)


-- @@ L1868-1877 verbatim
private theorem normSq_contDiff : ContDiff ℝ ∞ Complex.normSq := by
  have hre : ContDiff ℝ ∞ (fun z : ℂ ↦ z.re) := by
    rw [show (fun z : ℂ ↦ z.re) = (Complex.reCLM : ℂ → ℝ) by funext z; rfl]
    exact Complex.reCLM.contDiff
  have him : ContDiff ℝ ∞ (fun z : ℂ ↦ z.im) := by
    rw [show (fun z : ℂ ↦ z.im) = (Complex.imCLM : ℂ → ℝ) by funext z; rfl]
    exact Complex.imCLM.contDiff
  rw [show Complex.normSq = fun z : ℂ ↦ z.re * z.re + z.im * z.im by
    funext z; exact Complex.normSq_apply z]
  convert! hre.mul hre |>.add (him.mul him) using 1


-- @@ L1879-1881 verbatim
private theorem radialArgument_contDiff : ContDiff ℝ ∞ radialArgument := by
  unfold radialArgument
  exact normSq_contDiff.mul <| Real.contDiff_exp.comp <| contDiff_const.mul normSq_contDiff


-- @@ L1883-1884 verbatim
private theorem radialArgument_zero : radialArgument 0 = 0 := by
  simp [radialArgument]


-- @@ L1886-1888 verbatim
private theorem radialFlat_contDiff : ContDiff ℝ ∞ radialFlat := by
  unfold radialFlat
  exact (Real.flatRpowExp.contDiff (by norm_num) (by norm_num)).comp radialArgument_contDiff


-- @@ L1890-1895 verbatim
private theorem radialFlat_iteratedFDeriv_zero (n : ℕ) :
    iteratedFDeriv ℝ n radialFlat 0 = 0 := by
  unfold radialFlat
  exact ContDiff.iteratedFDeriv_comp_zero_of_outer
    (Real.flatRpowExp.contDiff (by norm_num) (by norm_num)) radialArgument_contDiff
    radialArgument_zero (Real.flatRpowExp.iteratedFDeriv_zero (by norm_num) (by norm_num)) n


-- @@ L1897-1898 verbatim
private def radialAmplitude (z : ℂ) : ℝ :=
  radialFlat z * (Complex.normSq z / (1 + Complex.normSq z))


-- @@ L1900-1904 verbatim
private theorem radialAmplitude_contDiff : ContDiff ℝ ∞ radialAmplitude := by
  unfold radialAmplitude
  apply radialFlat_contDiff.mul
  exact normSq_contDiff.div (contDiff_const.add normSq_contDiff) fun z ↦
    ne_of_gt (by have := Complex.normSq_nonneg z; linarith)


-- @@ L1906-1912 verbatim
private theorem radialAmplitude_iteratedFDeriv_zero (n : ℕ) :
    iteratedFDeriv ℝ n radialAmplitude 0 = 0 := by
  unfold radialAmplitude
  apply ContDiff.iteratedFDeriv_mul_zero_of_left radialFlat_contDiff
  · exact normSq_contDiff.div (contDiff_const.add normSq_contDiff) fun z ↦
      ne_of_gt (by have := Complex.normSq_nonneg z; linarith)
  · exact radialFlat_iteratedFDeriv_zero


-- @@ L1914-1917 verbatim
private theorem radialAmplitude_isLittleO_norm_pow (m n : ℕ) :
    iteratedFDeriv ℝ m radialAmplitude =o[𝓝 0] fun z : ℂ ↦ ‖z‖ ^ n :=
  ContDiff.isLittleO_norm_pow_of_iteratedFDeriv_zero radialAmplitude_contDiff
    radialAmplitude_iteratedFDeriv_zero m n


-- @@ L1919-1938 verbatim
private theorem radialFlat_eq (z : ℂ) (hz : z ≠ 0) :
    radialFlat z =
      Real.exp (-‖z‖ ^ (-(1 : ℝ) / 4) * Real.exp (-‖z‖ ^ 2)) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hx : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  rw [radialFlat, radialArgument,
    Real.flatRpowExp.of_pos _ _ (mul_pos hx (Real.exp_pos _))]
  have hpow : Complex.normSq z ^ (-(1 / 8 : ℝ)) = ‖z‖ ^ (-(1 : ℝ) / 4) := by
    rw [Complex.normSq_eq_norm_sq, ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg z)]
    congr 1
    ring
  have hexp : Real.exp (8 * Complex.normSq z) ^ (-(1 / 8 : ℝ)) =
      Real.exp (-‖z‖ ^ 2) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp,
      Complex.normSq_eq_norm_sq]
    congr 1
    ring
  rw [Real.mul_rpow hx.le (Real.exp_pos _).le, hpow, hexp]
  congr 1
  ring


-- @@ L1940-1953 verbatim
private theorem counterexample_eq_radialAmplitude (k : ℕ) (z : ℂ) (hz : z ≠ 0) :
    counterexample k z = radialAmplitude z * oscillatoryFactor k z + 10 ^ 10 := by
  have hexp :
      Real.exp (-(Real.rpow ‖z‖ (-(1 : ℝ) / 4) * Real.exp (-‖z‖ ^ 2))) =
        Real.exp (-(Real.exp (-‖z‖ ^ 2) * ‖z‖ ^ (-(1 : ℝ) / 4))) := by
    congr 1
    change -(‖z‖ ^ (-(1 : ℝ) / 4) * Real.exp (-‖z‖ ^ 2)) =
      -(Real.exp (-‖z‖ ^ 2) * ‖z‖ ^ (-(1 : ℝ) / 4))
    ring
  rw [counterexample, radialAmplitude, oscillatoryFactor, radialFlat_eq z hz,
    Complex.normSq_eq_norm_sq]
  ring_nf
  all_goals rw [hexp]
  all_goals ring


-- @@ L1955-1960 verbatim
private lemma cpow_half_nat_sq (z : ℂ) (k : ℕ) :
    (z ^ ((k : ℂ) / 2)) ^ 2 = z ^ k := by
  rw [← Complex.cpow_mul_nat, ← Complex.cpow_natCast]
  congr 1
  push_cast
  ring


-- @@ L1962-1971 verbatim
private lemma alt_cpow_half_nat_sq (z : ℂ) (k : ℕ) :
    ((Complex.I ^ k) * ((-z) ^ ((k : ℂ) / 2))) ^ 2 = z ^ k := by
  rw [mul_pow, cpow_half_nat_sq, ← pow_mul]
  conv_lhs => lhs; rw [show k * 2 = 2 * k by omega]
  rw [pow_mul, Complex.I_sq]
  rw [neg_pow z k]
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]
    simp
  rw [← mul_assoc, hsign, one_mul]


-- @@ L1973-1977 verbatim
private lemma counterexampleSeed_eq_of_sq_eq_sq {z w : ℂ} (h : z ^ 2 = w ^ 2) :
    counterexampleSeed z = counterexampleSeed w := by
  rcases eq_or_eq_neg_of_sq_eq_sq z w h with h | h
  · rw [h]
  · rw [h, counterexampleSeed_neg]


-- @@ L1979-1985 verbatim
/-- The seed identifies the principal half-integral power with the smooth alternate branch based
at `-z`. This pointwise identity is useful for differentiating at points on the branch cut. -/
theorem counterexampleSeed_cpow_eq_alt (k : ℕ) (z : ℂ) :
    counterexampleSeed (z ^ ((k : ℂ) / 2)) =
      counterexampleSeed ((Complex.I ^ k) * ((-z) ^ ((k : ℂ) / 2))) :=
  counterexampleSeed_eq_of_sq_eq_sq <|
    (cpow_half_nat_sq z k).trans (alt_cpow_half_nat_sq z k).symm


-- @@ L1987-2000 verbatim
private theorem oscillatoryFactor_eq_minus (k : ℕ) {z : ℂ}
    (hz : -star z ∈ Complex.slitPlane) :
    oscillatoryFactor k z = counterexampleSeed ((branchPhase k (Complex.I ^ k) ∘ negConjLIE) z) := by
  have hneg : -(100 / star z) = 100 / (-star z) := by ring
  calc
    oscillatoryFactor k z =
        counterexampleSeed ((Complex.I ^ k) * ((-(100 / star z)) ^ ((k : ℂ) / 2))) := by
      simpa [oscillatoryFactor] using counterexampleSeed_cpow_eq_alt k (100 / star z)
    _ = counterexampleSeed
        ((Complex.I ^ k) * ((100 / (-star z)) ^ ((k : ℂ) / 2))) := by rw [hneg]
    _ = counterexampleSeed ((branchPhase k (Complex.I ^ k) ∘ negConjLIE) z) := by
      rw [div_cpow_eq k hz]
      simp only [Function.comp_apply, negConjLIE_apply, branchPhase]
      ring_nf


-- @@ L2002-2045 verbatim
private theorem oscillatoryFactor_iteratedFDeriv_polynomial_bound (k n : ℕ) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧ ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ 1 →
      ‖iteratedFDeriv ℝ n (oscillatoryFactor k) z‖ ≤ C * ‖z‖ ^ (-(N : ℝ)) := by
  obtain ⟨Np, Cp, hCp, hp⟩ :=
    branchOscillatory_iteratedFDeriv_polynomial_bound k n 1 (by simp) Complex.conjLIE
  obtain ⟨Nm, Cm, hCm, hm⟩ :=
    branchOscillatory_iteratedFDeriv_polynomial_bound k n (Complex.I ^ k)
      (by simp) negConjLIE
  refine ⟨Np + Nm, Cp + Cm, add_nonneg hCp hCm, ?_⟩
  intro z hz hz_one
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hpowp : ‖z‖ ^ (-(Np : ℝ)) ≤ ‖z‖ ^ (-((Np + Nm : ℕ) : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_ge hr hz_one
    push_cast
    linarith
  have hpowm : ‖z‖ ^ (-(Nm : ℝ)) ≤ ‖z‖ ^ (-((Np + Nm : ℕ) : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_ge hr hz_one
    push_cast
    linarith
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane (star_ne_zero.mpr hz) with hslit | hslit
  · have heq : oscillatoryFactor k =ᶠ[𝓝 z]
        counterexampleSeed ∘ branchPhase k 1 ∘ Complex.conjLIE := by
      filter_upwards [Complex.isOpen_slitPlane.preimage Complex.continuous_conj |>.mem_nhds hslit]
        with w hw
      exact oscillatoryFactor_eq_plus k hw
    rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds]
    calc
      _ ≤ Cp * ‖z‖ ^ (-(Np : ℝ)) := hp z hslit hz_one
      _ ≤ (Cp + Cm) * ‖z‖ ^ (-((Np + Nm : ℕ) : ℝ)) := by
        exact (mul_le_mul_of_nonneg_left hpowp hCp).trans <|
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCm)
            (Real.rpow_nonneg (norm_nonneg z) _)
  · have heq : oscillatoryFactor k =ᶠ[𝓝 z]
        counterexampleSeed ∘ branchPhase k (Complex.I ^ k) ∘ negConjLIE := by
      filter_upwards [Complex.isOpen_slitPlane.preimage negConjLIE.continuous |>.mem_nhds hslit]
        with w hw
      exact oscillatoryFactor_eq_minus k hw
    rw [(heq.iteratedFDeriv ℝ n).eq_of_nhds]
    calc
      _ ≤ Cm * ‖z‖ ^ (-(Nm : ℝ)) := hm z hslit hz_one
      _ ≤ (Cp + Cm) * ‖z‖ ^ (-((Np + Nm : ℕ) : ℝ)) := by
        exact (mul_le_mul_of_nonneg_left hpowm hCm).trans <|
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCp)
            (Real.rpow_nonneg (norm_nonneg z) _)


-- @@ L2047-2059 verbatim
private theorem counterexampleSeed_cpow_contDiffAt (k : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (fun w : ℂ ↦ counterexampleSeed (w ^ ((k : ℂ) / 2))) z := by
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hz with hz | hz
  · exact counterexampleSeed_contDiff.contDiffAt.comp z
      ((analyticAt_id.cpow analyticAt_const hz).restrictScalars.contDiffAt)
  · have hq : ContDiffAt ℝ ∞
        (fun w : ℂ ↦ (Complex.I ^ k) * ((-w) ^ ((k : ℂ) / 2))) z :=
      ((analyticAt_const.mul
        (analyticAt_id.neg.cpow analyticAt_const hz)).restrictScalars.contDiffAt)
    apply (counterexampleSeed_contDiff.contDiffAt.comp z hq).congr_of_eventuallyEq
    filter_upwards
    intro w
    exact counterexampleSeed_cpow_eq_alt k w


-- @@ L2061-2071 verbatim
private theorem oscillatoryFactor_contDiffAt (k : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (oscillatoryFactor k) z := by
  have hstar : ContDiffAt ℝ ∞ (fun w : ℂ ↦ star w) z := by
    rw [show (fun w : ℂ ↦ star w) = (Complex.conjLIE : ℂ → ℂ) by funext w; rfl]
    exact Complex.conjLIE.contDiff.contDiffAt
  have hstar_ne : star z ≠ 0 := star_ne_zero.mpr hz
  have hinv : ContDiffAt ℝ ∞ (fun w : ℂ ↦ 100 / star w) z := by
    simpa [div_eq_mul_inv] using contDiffAt_const.mul (hstar.inv hstar_ne)
  unfold oscillatoryFactor
  exact (counterexampleSeed_cpow_contDiffAt k
    (div_ne_zero (by norm_num) hstar_ne)).comp z hinv


-- @@ L2073-2166 verbatim
private theorem radialAmplitude_mul_oscillatory_flatness (k : ℕ) :
    ContDiffAt ℝ ∞ (fun z ↦ radialAmplitude z * oscillatoryFactor k z) 0 ∧
      ∀ m, iteratedFDeriv ℝ m (fun z ↦ radialAmplitude z * oscillatoryFactor k z) =o[𝓝[≠] 0]
        (id : ℂ → ℂ) := by
  let s : Set ℂ := {0}ᶜ
  have hs : IsOpen s := isClosed_singleton.isOpen_compl
  have hosc : ContDiffOn ℝ ∞ (oscillatoryFactor k) s := by
    intro z hz
    exact (oscillatoryFactor_contDiffAt k (by simpa [s] using hz)).contDiffWithinAt
  have hflat : ∀ m, iteratedFDeriv ℝ m
      (fun z ↦ radialAmplitude z * oscillatoryFactor k z) =o[𝓝[≠] 0]
        (id : ℂ → ℂ) := by
    intro m
    have hsum' : (∑ i ∈ Finset.range (m + 1), fun z : ℂ ↦
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i radialAmplitude z‖ *
          ‖iteratedFDeriv ℝ (m - i) (oscillatoryFactor k) z‖) =o[𝓝[≠] 0]
        fun z ↦ ‖z‖ := by
      apply Asymptotics.IsLittleO.sum
      intro i hi
      obtain ⟨N, C, hC, hpoly⟩ :=
        oscillatoryFactor_iteratedFDeriv_polynomial_bound k (m - i)
      have hoscO : (iteratedFDeriv ℝ (m - i) (oscillatoryFactor k)) =O[𝓝[≠] 0]
          fun z : ℂ ↦ ‖z‖ ^ (-(N : ℝ)) := by
        rw [Asymptotics.isBigO_iff]
        refine ⟨C, ?_⟩
        have hball : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∈ Metric.ball 0 1 :=
          Filter.Eventually.filter_mono inf_le_left (Metric.ball_mem_nhds 0 one_pos)
        filter_upwards [self_mem_nhdsWithin, hball] with z hz hball
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
        have hz_one : ‖z‖ ≤ 1 := by
          rw [Metric.mem_ball, dist_zero_right] at hball
          exact hball.le
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
        exact hpoly z hz hz_one
      have hamp := (radialAmplitude_isLittleO_norm_pow i (N + 1)).mono
        (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 from inf_le_left)
      have hprod : (fun z : ℂ ↦
          ‖iteratedFDeriv ℝ i radialAmplitude z‖ *
            ‖iteratedFDeriv ℝ (m - i) (oscillatoryFactor k) z‖) =o[𝓝[≠] 0]
          fun z ↦ ‖z‖ ^ (N + 1) * ‖z‖ ^ (-(N : ℝ)) :=
        hamp.norm_left.mul_isBigO hoscO.norm_left
      have htarget : (fun z : ℂ ↦ ‖z‖ ^ (N + 1) * ‖z‖ ^ (-(N : ℝ))) =ᶠ[𝓝[≠] 0]
          fun z ↦ ‖z‖ := by
        filter_upwards [self_mem_nhdsWithin] with z hz
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
        have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
        rw [← Real.rpow_natCast, ← Real.rpow_add hr]
        have hN : ((N + 1 : ℕ) : ℝ) + -(N : ℝ) = 1 := by
          push_cast
          ring
        rw [hN, Real.rpow_one]
      simpa only [mul_assoc] using
        (hprod.congr' EventuallyEq.rfl htarget).const_mul_left (m.choose i : ℝ)
    have hsum : (fun z : ℂ ↦ ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i radialAmplitude z‖ *
          ‖iteratedFDeriv ℝ (m - i) (oscillatoryFactor k) z‖) =o[𝓝[≠] 0]
        fun z ↦ ‖z‖ := by
      have heq : (∑ i ∈ Finset.range (m + 1), fun z : ℂ ↦
          (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i radialAmplitude z‖ *
            ‖iteratedFDeriv ℝ (m - i) (oscillatoryFactor k) z‖) =
          fun z ↦ ∑ i ∈ Finset.range (m + 1),
            (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i radialAmplitude z‖ *
              ‖iteratedFDeriv ℝ (m - i) (oscillatoryFactor k) z‖ := by
        funext z
        classical
        induction Finset.range (m + 1) using Finset.induction_on with
        | empty => simp
        | @insert a s ha ih => simp [ha, ih]
      rw [← heq]
      exact hsum'
    rw [Asymptotics.isLittleO_iff] at hsum ⊢
    intro c hc
    filter_upwards [hsum hc, self_mem_nhdsWithin] with z hbound hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz
    have hmul := norm_iteratedFDerivWithin_mul_le
      radialAmplitude_contDiff.contDiffOn hosc hs.uniqueDiffOn (show z ∈ s by simpa [s] using hz)
      (mod_cast le_top : m ≤ (∞ : WithTop ℕ∞))
    rw [iteratedFDerivWithin_of_isOpen m hs (show z ∈ s by simpa [s] using hz)] at hmul
    simp_rw [iteratedFDerivWithin_of_isOpen _ hs (show z ∈ s by simpa [s] using hz)] at hmul
    have hsum_nonneg : 0 ≤ ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i radialAmplitude z‖ *
          ‖iteratedFDeriv ℝ (m - i) (oscillatoryFactor k) z‖ := by
      apply Finset.sum_nonneg
      intro i hi
      exact mul_nonneg
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)) (norm_nonneg _)
    rw [Real.norm_of_nonneg hsum_nonneg] at hbound
    exact hmul.trans (by simpa using hbound)
  refine ⟨?_, hflat⟩
  apply ContDiff.at_zero_of_iteratedFDeriv_isLittleO
  · intro z hz
    exact radialAmplitude_contDiff.contDiffAt.mul (oscillatoryFactor_contDiffAt k hz)
  · simp [radialAmplitude, radialFlat, radialArgument]
  · exact hflat


-- @@ L2168-2171 verbatim
private theorem radialAmplitude_mul_oscillatory_iteratedFDeriv_isLittleO (k m : ℕ) :
    iteratedFDeriv ℝ m (fun z ↦ radialAmplitude z * oscillatoryFactor k z) =o[𝓝[≠] 0]
      (id : ℂ → ℂ) :=
  (radialAmplitude_mul_oscillatory_flatness k).2 m


-- @@ L2173-2175 verbatim
private theorem radialAmplitude_mul_oscillatory_contDiffAt_zero (k : ℕ) :
    ContDiffAt ℝ ∞ (fun z ↦ radialAmplitude z * oscillatoryFactor k z) 0 :=
  (radialAmplitude_mul_oscillatory_flatness k).1


-- @@ L2177-2188 verbatim
private theorem radialAmplitude_mul_oscillatory_iteratedFDeriv_zero (k m : ℕ) :
    iteratedFDeriv ℝ m (fun z ↦ radialAmplitude z * oscillatoryFactor k z) 0 = 0 := by
  have hcontinuous := (radialAmplitude_mul_oscillatory_contDiffAt_zero k)
    |>.continuousAt_iteratedFDeriv (mod_cast le_top : m ≤ (∞ : WithTop ℕ∞))
  have hcontinuous' : Tendsto
      (iteratedFDeriv ℝ m (fun z ↦ radialAmplitude z * oscillatoryFactor k z))
      (𝓝[≠] 0) (𝓝 (iteratedFDeriv ℝ m
        (fun z ↦ radialAmplitude z * oscillatoryFactor k z) 0)) :=
    hcontinuous.mono_left (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 from inf_le_left)
  have hzero := (radialAmplitude_mul_oscillatory_iteratedFDeriv_isLittleO k m).trans_tendsto
    (tendsto_id.mono_left inf_le_left)
  exact tendsto_nhds_unique' (NormedField.nhdsNE_neBot (0 : ℂ)) hcontinuous' hzero


-- @@ L2190-2208 verbatim
/-- Away from the origin the principal-power formula is smooth. For odd `k`, evenness of the seed
removes the sign jump of the chosen square-root branch. -/
theorem counterexample_contDiffAt_of_ne_zero (k : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (counterexample k) z := by
  have hstar : ContDiffAt ℝ ∞ (fun w : ℂ ↦ star w) z := by
    rw [show (fun w : ℂ ↦ star w) = (Complex.conjLIE : ℂ → ℂ) by funext w; rfl]
    exact Complex.conjLIE.contDiff.contDiffAt
  have hstar_ne : star z ≠ 0 := star_ne_zero.mpr hz
  have hinv : ContDiffAt ℝ ∞ (fun w : ℂ ↦ 100 / star w) z := by
    simpa [div_eq_mul_inv] using contDiffAt_const.mul (hstar.inv hstar_ne)
  have hseed : ContDiffAt ℝ ∞
      (fun w : ℂ ↦ counterexampleSeed ((100 / star w) ^ ((k : ℂ) / 2))) z :=
    by
      simpa [Function.comp_def] using
        (counterexampleSeed_cpow_contDiffAt k (div_ne_zero (by norm_num) hstar_ne)).comp z hinv
  apply (radialAmplitude_contDiff.contDiffAt.mul hseed).add contDiffAt_const
    |>.congr_of_eventuallyEq
  filter_upwards [eventually_ne_nhds hz] with w hw
  exact counterexample_eq_radialAmplitude k w hw


-- @@ L2210-2220 verbatim
private theorem counterexample_contDiffAt_zero_all (k : ℕ) :
    ContDiffAt ℝ ∞ (counterexample k) 0 := by
  have hconstant : ContDiffAt ℝ ∞ (fun _ : ℂ ↦ (10 : ℝ) ^ 10) 0 := contDiffAt_const
  apply (radialAmplitude_mul_oscillatory_contDiffAt_zero k).add hconstant
    |>.congr_of_eventuallyEq
  filter_upwards
  intro z
  by_cases hz : z = 0
  · subst z
    simp [counterexample_zero, radialAmplitude, radialFlat, radialArgument]
  · exact counterexample_eq_radialAmplitude k z hz


-- @@ L2222-2228 verbatim
/-- At the origin the nonconstant part of `counterexample k` is flat: exponential decay dominates
the algebraic growth of every derivative of the oscillatory factor. -/
theorem counterexample_contDiffAt_zero (k : ℕ) (hk : 0 < k) :
    ContDiffAt ℝ ∞ (counterexample k) 0 := by
  cases k with
  | zero => omega
  | succ k => exact counterexample_contDiffAt_zero_all (k + 1)


-- @@ L2230-2249 verbatim
/-- The first Fréchet derivative of the counterexample vanishes at the origin. -/
theorem counterexample_fderiv_zero (k : ℕ) (hk : 0 < k) :
    fderiv ℝ (counterexample k) 0 = 0 := by
  cases k with
  | zero => omega
  | succ k =>
    have hfun : counterexample (Nat.succ k) = fun z ↦
        radialAmplitude z * oscillatoryFactor (Nat.succ k) z + (10 : ℝ) ^ 10 := by
      funext z
      by_cases hz : z = 0
      · subst z
        simp [counterexample_zero, radialAmplitude, radialFlat, radialArgument]
      · exact counterexample_eq_radialAmplitude (Nat.succ k) z hz
    rw [hfun]
    simp only [fderiv_add_const]
    ext v
    have hzero := radialAmplitude_mul_oscillatory_iteratedFDeriv_zero (Nat.succ k) 1
    have happ := congrArg (fun L : ℂ [×1]→L[ℝ] ℝ ↦ L ![v]) hzero
    simpa only [iteratedFDeriv_one_apply, ContinuousMultilinearMap.zero_apply,
      Matrix.cons_val_zero] using happ


-- @@ L2251-2266 verbatim
private theorem counterexample_fderiv_fderiv_zero_all (k : ℕ) :
    fderiv ℝ (fun w ↦ fderiv ℝ (counterexample k) w) 0 = 0 := by
  have hfun : counterexample k = fun z ↦
      radialAmplitude z * oscillatoryFactor k z + (10 : ℝ) ^ 10 := by
    funext z
    by_cases hz : z = 0
    · subst z
      simp [counterexample_zero, radialAmplitude, radialFlat, radialArgument]
    · exact counterexample_eq_radialAmplitude k z hz
  rw [hfun]
  simp only [fderiv_add_const]
  ext v w
  have hzero := radialAmplitude_mul_oscillatory_iteratedFDeriv_zero k 2
  have happ := congrArg (fun L : ℂ [×2]→L[ℝ] ℝ ↦ L ![v, w]) hzero
  simpa only [iteratedFDeriv_two_apply, ContinuousMultilinearMap.zero_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] using happ


-- @@ L2268-2274 verbatim
/-- The second Fréchet derivative of the counterexample vanishes at the origin. This is the
flatness consequence used in the index computation. -/
theorem counterexample_fderiv_fderiv_zero (k : ℕ) (hk : 0 < k) :
    fderiv ℝ (fun w ↦ fderiv ℝ (counterexample k) w) 0 = 0 := by
  cases k with
  | zero => omega
  | succ k => exact counterexample_fderiv_fderiv_zero_all (k + 1)


-- @@ L2276-2283 verbatim
/-- Each positive member of the announced family is smooth on the whole complex plane, including
at the origin. The flat exponential factor is essential at the origin. -/
theorem counterexample_contDiff (k : ℕ) (hk : 0 < k) : ContDiff ℝ ∞ (counterexample k) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z = 0
  · simpa [hz] using counterexample_contDiffAt_zero k hk
  · exact counterexample_contDiffAt_of_ne_zero k hz


-- @@ L2285-2285 verbatim
end


-- @@ L2287-2287 verbatim
end CaratheodoryLoewnerCounterexample


-- @@ L2289-2289 verbatim
end CounterexampleSmoothSection


-- @@ L2291-2291 verbatim
/-! ## Flattened from `FormalConjectures/Other/CaratheodoryLoewnerCounterexample/Index.lean` -/


-- @@ L2293-2293 verbatim
section CounterexampleIndexSection


-- @@ L2295-2302 verbatim
/-!
# Index of the announced Carathéodory–Loewner counterexamples

This file computes the winding number of the trace-free Hessian near the origin.

*Reference:*
- [L. Alpöge, X post 2089971359921156203](https://x.com/__alpoge__/status/2089971359921156203)
-/


-- @@ L2304-2304 verbatim
open Metric

-- @@ L2305-2305 verbatim
open Filter

-- @@ L2306-2306 verbatim
open scoped ContDiff Topology unitInterval


-- @@ L2308-2308 verbatim
namespace CaratheodoryLoewnerCounterexample


-- @@ L2310-2310 verbatim
open LoewnerConjecture


-- @@ L2312-2317 verbatim
private theorem traceFreeHessian_eq_second_fderiv (f : ℂ → ℝ) (z : ℂ) :
    traceFreeHessian f z =
      let H := fderiv ℝ (fun w ↦ fderiv ℝ f w) z
      (H 1 1 - H Complex.I Complex.I : ℝ) +
        (2 * H 1 Complex.I : ℝ) * Complex.I := by
  simp [traceFreeHessian, iteratedFDeriv_two_apply]


-- @@ L2319-2323 verbatim
private theorem traceFreeHessian_eq_zero_of_second_fderiv_eq_zero (f : ℂ → ℝ) (z : ℂ)
    (h : fderiv ℝ (fun w ↦ fderiv ℝ f w) z = 0) :
    traceFreeHessian f z = 0 := by
  rw [traceFreeHessian_eq_second_fderiv, h]
  simp


-- @@ L2325-2330 verbatim
/-- The explicit trace-free Hessian of the seed. Keeping this local avoids adding another
public synonym for a one-line expression. -/
private noncomputable def seedTraceFreeHessianModel (z : ℂ) : ℂ :=
  ((Real.cos (2 * z.re) + 6 / 5 * Real.cos (2 * z.im) -
      1 / 2 * Real.cos (4 * z.im) : ℝ) : ℂ) +
    ((2 * Real.cos z.re * Real.cos z.im : ℝ) : ℂ) * Complex.I


-- @@ L2332-2335 verbatim
private noncomputable def seedGradient (z : ℂ) : ℂ →L[ℝ] ℝ :=
  (Real.sin (2 * z.re) / 2 + Real.cos z.re * Real.sin z.im) • Complex.reCLM +
    (-3 * Real.sin (2 * z.im) / 5 + Real.sin (4 * z.im) / 8 +
      Real.sin z.re * Real.cos z.im) • Complex.imCLM


-- @@ L2337-2342 verbatim
private noncomputable def seedHessian (z : ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  ((Real.cos (2 * z.re) - Real.sin z.re * Real.sin z.im) • Complex.reCLM +
      (Real.cos z.re * Real.cos z.im) • Complex.imCLM).smulRight Complex.reCLM +
    ((Real.cos z.re * Real.cos z.im) • Complex.reCLM +
      (-6 / 5 * Real.cos (2 * z.im) + 1 / 2 * Real.cos (4 * z.im) -
        Real.sin z.re * Real.sin z.im) • Complex.imCLM).smulRight Complex.imCLM


-- @@ L2344-2347 verbatim
private noncomputable def seedWirtingerModel (z : ℂ) : ℂ :=
  (((Real.sin (2 * z.re) / 2 + Real.cos z.re * Real.sin z.im : ℝ) : ℂ) -
    ((-3 * Real.sin (2 * z.im) / 5 + Real.sin (4 * z.im) / 8 +
      Real.sin z.re * Real.cos z.im : ℝ) : ℂ) * Complex.I) / 2


-- @@ L2349-2351 verbatim
private theorem seedTraceFreeHessianModel_neg (z : ℂ) :
    seedTraceFreeHessianModel (-z) = seedTraceFreeHessianModel z := by
  simp [seedTraceFreeHessianModel]


-- @@ L2353-2356 verbatim
private theorem seedWirtingerModel_neg (z : ℂ) :
    seedWirtingerModel (-z) = -seedWirtingerModel z := by
  simp [seedWirtingerModel]
  ring


-- @@ L2358-2361 verbatim
private theorem seedWirtingerModel_eq_gradient (z : ℂ) :
    seedWirtingerModel z =
      ((seedGradient z 1 : ℂ) - (seedGradient z Complex.I : ℂ) * Complex.I) / 2 := by
  simp [seedWirtingerModel, seedGradient]


-- @@ L2363-2419 verbatim
private theorem norm_seedWirtingerModel_le (z : ℂ) : ‖seedWirtingerModel z‖ ≤ 129 / 80 := by
  have hfx : |Real.sin (2 * z.re) / 2 + Real.cos z.re * Real.sin z.im| ≤ 3 / 2 := by
    calc
      _ ≤ |Real.sin (2 * z.re) / 2| + |Real.cos z.re * Real.sin z.im| := abs_add_le ..
      _ = |Real.sin (2 * z.re)| / 2 + |Real.cos z.re| * |Real.sin z.im| := by
        rw [abs_div, abs_mul]
        norm_num
      _ ≤ 1 / 2 + 1 := by
        exact add_le_add
          (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by norm_num))
          (mul_le_one₀ (Real.abs_cos_le_one _) (abs_nonneg _) (Real.abs_sin_le_one _))
      _ = 3 / 2 := by norm_num
  have hfy : |-3 * Real.sin (2 * z.im) / 5 + Real.sin (4 * z.im) / 8 +
      Real.sin z.re * Real.cos z.im| ≤ 69 / 40 := by
    calc
      _ ≤ |-3 * Real.sin (2 * z.im) / 5 + Real.sin (4 * z.im) / 8| +
          |Real.sin z.re * Real.cos z.im| := abs_add_le ..
      _ ≤ |-3 * Real.sin (2 * z.im) / 5| + |Real.sin (4 * z.im) / 8| +
          |Real.sin z.re * Real.cos z.im| := by gcongr; exact abs_add_le ..
      _ = 3 / 5 * |Real.sin (2 * z.im)| + |Real.sin (4 * z.im)| / 8 +
          |Real.sin z.re| * |Real.cos z.im| := by
        rw [abs_div, abs_mul, abs_div, abs_mul]
        norm_num
        ring
      _ ≤ 3 / 5 + 1 / 8 + 1 := by
        exact add_le_add
          (add_le_add
            (by simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one (2 * z.im))
                (by norm_num : (0 : ℝ) ≤ 3 / 5)))
            (div_le_div_of_nonneg_right (Real.abs_sin_le_one _) (by norm_num)))
          (mul_le_one₀ (Real.abs_sin_le_one _) (abs_nonneg (Real.cos z.im))
            (Real.abs_cos_le_one _))
      _ = 69 / 40 := by norm_num
  calc
    ‖seedWirtingerModel z‖ ≤
        (|Real.sin (2 * z.re) / 2 + Real.cos z.re * Real.sin z.im| +
          |-3 * Real.sin (2 * z.im) / 5 + Real.sin (4 * z.im) / 8 +
            Real.sin z.re * Real.cos z.im|) / 2 := by
      have hmodel : seedWirtingerModel z =
          (((Real.sin (2 * z.re) / 2 + Real.cos z.re * Real.sin z.im : ℝ) : ℂ) -
            (((-3 * Real.sin (2 * z.im) / 5 + Real.sin (4 * z.im) / 8 +
              Real.sin z.re * Real.cos z.im : ℝ) : ℂ) * Complex.I)) / 2 := rfl
      have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
      rw [hmodel, norm_div, htwo]
      apply div_le_div_of_nonneg_right _ (by norm_num)
      calc
        _ ≤ ‖((Real.sin (2 * z.re) / 2 + Real.cos z.re * Real.sin z.im : ℝ) : ℂ)‖ +
            ‖(((-3 * Real.sin (2 * z.im) / 5 + Real.sin (4 * z.im) / 8 +
              Real.sin z.re * Real.cos z.im : ℝ) : ℂ) * Complex.I)‖ := norm_sub_le _ _
        _ = |Real.sin (2 * z.re) / 2 + Real.cos z.re * Real.sin z.im| +
            |-3 * Real.sin (2 * z.im) / 5 + Real.sin (4 * z.im) / 8 +
              Real.sin z.re * Real.cos z.im| := by
          rw [Complex.norm_real, norm_mul, Complex.norm_real]
          simp only [Complex.norm_I, mul_one, Real.norm_eq_abs]
    _ ≤ (3 / 2 + 69 / 40) / 2 := div_le_div_of_nonneg_right (add_le_add hfx hfy) (by norm_num)
    _ = 129 / 80 := by norm_num


-- @@ L2421-2452 verbatim
/-- The seed has the uniform absolute-value bound used in the global Hessian estimates. -/
theorem counterexampleSeed_abs_le (z : ℂ) : |counterexampleSeed z| ≤ 253 / 160 := by
  calc
    _ ≤ |-Real.cos (2 * z.re) / 4 + 3 * Real.cos (2 * z.im) / 10 -
          Real.cos (4 * z.im) / 32| + |Real.sin z.re * Real.sin z.im| := by
      simpa [counterexampleSeed] using abs_add_le
        (-Real.cos (2 * z.re) / 4 + 3 * Real.cos (2 * z.im) / 10 -
          Real.cos (4 * z.im) / 32) (Real.sin z.re * Real.sin z.im)
    _ ≤ |-Real.cos (2 * z.re) / 4 + 3 * Real.cos (2 * z.im) / 10| +
          |Real.cos (4 * z.im) / 32| + |Real.sin z.re * Real.sin z.im| := by
      exact add_le_add (abs_sub (-Real.cos (2 * z.re) / 4 +
        3 * Real.cos (2 * z.im) / 10) (Real.cos (4 * z.im) / 32)) le_rfl
    _ ≤ |-Real.cos (2 * z.re) / 4| + |3 * Real.cos (2 * z.im) / 10| +
          |Real.cos (4 * z.im) / 32| + |Real.sin z.re * Real.sin z.im| := by
      exact add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
    _ = |Real.cos (2 * z.re)| / 4 + 3 / 10 * |Real.cos (2 * z.im)| +
          |Real.cos (4 * z.im)| / 32 + |Real.sin z.re| * |Real.sin z.im| := by
      rw [abs_div, abs_neg, abs_div, abs_mul, abs_div, abs_mul]
      norm_num
      ring
    _ ≤ 1 / 4 + 3 / 10 + 1 / 32 + 1 := by
      exact add_le_add
        (add_le_add
          (add_le_add
            (div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by norm_num))
            (by simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (2 * z.im))
                (by norm_num : (0 : ℝ) ≤ 3 / 10))))
          (div_le_div_of_nonneg_right (Real.abs_cos_le_one _) (by norm_num)))
        (mul_le_one₀ (Real.abs_sin_le_one _) (abs_nonneg (Real.sin z.im))
          (Real.abs_sin_le_one _))
    _ = 253 / 160 := by norm_num


-- @@ L2454-2466 verbatim
private theorem hasFDerivAt_counterexampleSeed (z : ℂ) :
    HasFDerivAt counterexampleSeed (seedGradient z) z := by
  let hx : HasFDerivAt (fun u : ℂ ↦ u.re) Complex.reCLM z := Complex.reCLM.hasFDerivAt
  let hy : HasFDerivAt (fun u : ℂ ↦ u.im) Complex.imCLM z := Complex.imCLM.hasFDerivAt
  have hraw := (((hx.const_mul 2).cos.neg.mul_const (4 : ℝ)⁻¹).add
    (((hy.const_mul 2).cos.const_mul 3).mul_const (10 : ℝ)⁻¹)).add
    (((hy.const_mul 4).cos.neg).mul_const (32 : ℝ)⁻¹) |>.add (hx.sin.mul hy.sin)
  convert! hraw using 1
  · funext u
    simp [counterexampleSeed, sub_eq_add_neg, div_eq_mul_inv]
  · ext v
    simp [seedGradient]
    ring


-- @@ L2468-2499 verbatim
private theorem hasFDerivAt_seedGradient (z : ℂ) :
    HasFDerivAt seedGradient (seedHessian z) z := by
  let hx : HasFDerivAt (fun u : ℂ ↦ u.re) Complex.reCLM z := Complex.reCLM.hasFDerivAt
  let hy : HasFDerivAt (fun u : ℂ ↦ u.im) Complex.imCLM z := Complex.imCLM.hasFDerivAt
  have hfx := ((hx.const_mul 2).sin.mul_const (2 : ℝ)⁻¹).add (hx.cos.mul hy.sin)
  have hfy := (((hy.const_mul 2).sin.const_mul (-3)).mul_const (5 : ℝ)⁻¹).add
    ((hy.const_mul 4).sin.mul_const (8 : ℝ)⁻¹) |>.add (hx.sin.mul hy.cos)
  have hraw := (hfx.smul_const Complex.reCLM).add (hfy.smul_const Complex.imCLM)
  let G : ℂ → (ℂ →L[ℝ] ℝ) :=
    (fun y ↦ (((fun y : ℂ ↦ Real.sin (2 * y.re) * (2 : ℝ)⁻¹) +
      (fun x : ℂ ↦ Real.cos x.re) * fun x : ℂ ↦ Real.sin x.im) y) • Complex.reCLM) +
    fun y ↦ ((((fun y : ℂ ↦ -3 * Real.sin (2 * y.im) * (5 : ℝ)⁻¹) +
      fun y : ℂ ↦ Real.sin (4 * y.im) * (8 : ℝ)⁻¹) +
      (fun x : ℂ ↦ Real.sin x.re) * fun x : ℂ ↦ Real.cos x.im) y) • Complex.imCLM
  have hfun : G = seedGradient := by
    funext u
    simp [G, seedGradient, div_eq_mul_inv]
  have hdiff : DifferentiableAt ℝ seedGradient z := by
    rw [← hfun]
    dsimp only [G]
    exact hraw.differentiableAt
  have hD : fderiv ℝ seedGradient z = seedHessian z := by
    rw [← hfun]
    dsimp only [G]
    rw [hraw.fderiv]
    apply DFunLike.coe_injective
    funext v
    apply DFunLike.coe_injective
    funext w
    simp [seedHessian]
    ring
  exact hdiff.hasFDerivAt.congr_fderiv hD


-- @@ L2501-2511 verbatim
/-- Direct differentiation identifies the finite trigonometric Hessian model with the
repository's Fréchet-derivative encoding. -/
private theorem traceFreeHessian_counterexampleSeed (z : ℂ) :
    traceFreeHessian counterexampleSeed z = seedTraceFreeHessianModel z := by
  rw [traceFreeHessian_eq_second_fderiv]
  rw [show (fun w ↦ fderiv ℝ counterexampleSeed w) = seedGradient by
    funext w
    exact (hasFDerivAt_counterexampleSeed w).fderiv]
  rw [(hasFDerivAt_seedGradient z).fderiv]
  simp [seedHessian, seedTraceFreeHessianModel]
  ring


-- @@ L2513-2558 verbatim
/-- The only part of the derivative of the seed's first Wirtinger derivative needed by the
anti-holomorphic chain rule. -/
private theorem exists_seedWirtingerModel_fderiv (z : ℂ) :
    ∃ Q : ℂ →L[ℝ] ℂ, HasFDerivAt seedWirtingerModel Q z ∧ ∀ b : ℂ,
      Q b + Complex.I * Q (-Complex.I * b) =
        b * star (seedTraceFreeHessianModel z) / 2 := by
  have hx := (hasFDerivAt_seedGradient z).clm_apply (hasFDerivAt_const (1 : ℂ) z)
  have hy := (hasFDerivAt_seedGradient z).clm_apply
    (hasFDerivAt_const Complex.I z)
  have hx' := Complex.ofRealCLM.hasFDerivAt.comp z hx
  have hy' := Complex.ofRealCLM.hasFDerivAt.comp z hy
  have hraw := (hx'.sub (hy'.mul_const Complex.I)).mul_const ((2 : ℂ)⁻¹)
  have heq : seedWirtingerModel = fun w ↦
      (((seedGradient w 1 : ℂ) - (seedGradient w Complex.I : ℂ) * Complex.I) / 2) := by
    funext w
    exact seedWirtingerModel_eq_gradient w
  let Q : ℂ →L[ℝ] ℂ := (2 : ℂ)⁻¹ •
    (Complex.ofRealCLM.comp ((seedHessian z).flip 1) -
      Complex.I • Complex.ofRealCLM.comp ((seedHessian z).flip Complex.I))
  have hqRaw : HasFDerivAt (fun w ↦
      (((seedGradient w 1 : ℂ) - (seedGradient w Complex.I : ℂ) * Complex.I) / 2)) Q z := by
    apply hraw.congr_fderiv
    ext b
    simp [Q]
  have hq : HasFDerivAt seedWirtingerModel Q z := by
    rw [heq]
    exact hqRaw
  refine ⟨Q, hq, fun b ↦ ?_⟩
  have hx2 : (2 : ℂ) * (z.re : ℂ) = ((2 * z.re : ℝ) : ℂ) := by
    push_cast
    ring
  have hy2 : (2 : ℂ) * (z.im : ℂ) = ((2 * z.im : ℝ) : ℂ) := by
    push_cast
    ring
  have hy4 : (4 : ℂ) * (z.im : ℂ) = ((4 * z.im : ℝ) : ℂ) := by
    push_cast
    ring
  apply Complex.ext
  · simp [Q, seedHessian, seedTraceFreeHessianModel, Complex.mul_re, Complex.mul_im]
    rw [hx2, hy2, hy4]
    simp only [Complex.cos_ofReal_re, Complex.cos_ofReal_im]
    ring
  · simp [Q, seedHessian, seedTraceFreeHessianModel, Complex.mul_re, Complex.mul_im]
    rw [hx2, hy2, hy4]
    simp only [Complex.cos_ofReal_re, Complex.cos_ofReal_im]
    ring


-- @@ L2560-2658 verbatim
/-- The exact uniform nonvanishing certificate behind the index computation. -/
private theorem seven_div_fifty_le_norm_seedTraceFreeHessianModel (z : ℂ) :
    7 / 50 ≤ ‖seedTraceFreeHessianModel z‖ := by
  let s := Real.cos z.re ^ 2
  let t := Real.cos z.im ^ 2
  let a := -4 * t ^ 2 + 32 / 5 * t - 27 / 10
  let sstar := (4 * t ^ 2 - 37 / 5 * t + 27 / 10) / 2
  have hs0 : 0 ≤ s := by positivity
  have ht0 : 0 ≤ t := by positivity
  have hs1 : s ≤ 1 := by
    have hplus : 0 ≤ 1 + Real.cos z.re := by linarith [Real.neg_one_le_cos z.re]
    have h := mul_nonneg (sub_nonneg.mpr (Real.cos_le_one z.re))
      hplus
    dsimp [s]
    nlinarith only [h]
  have ht1 : t ≤ 1 := by
    have hplus : 0 ≤ 1 + Real.cos z.im := by linarith [Real.neg_one_le_cos z.im]
    have h := mul_nonneg (sub_nonneg.mpr (Real.cos_le_one z.im))
      hplus
    dsimp [t]
    nlinarith only [h]
  have hcos4y : Real.cos (4 * z.im) =
      8 * Real.cos z.im ^ 4 - 8 * Real.cos z.im ^ 2 + 1 := by
    rw [show 4 * z.im = 2 * (2 * z.im) by ring, Real.cos_two_mul, Real.cos_two_mul]
    ring
  have hnorm : ‖seedTraceFreeHessianModel z‖ ^ 2 = (2 * s + a) ^ 2 + 4 * s * t := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    rw [seedTraceFreeHessianModel]
    simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
      sub_zero, add_zero, mul_one]
    have hreSq (x : ℝ) : x * x = x ^ 2 := by ring
    rw [hreSq, show (0 + 2 * Real.cos z.re * Real.cos z.im) *
        (0 + 2 * Real.cos z.re * Real.cos z.im) =
          (2 * Real.cos z.re * Real.cos z.im) ^ 2 by ring]
    rw [Real.cos_two_mul, Real.cos_two_mul, hcos4y]
    dsimp [s, t, a]
    ring
  have hcomplete : (2 * s + a) ^ 2 + 4 * s * t =
      4 * (s - sstar) ^ 2 + t * (8 * t ^ 2 - 69 / 5 * t + 27 / 5) := by
    dsimp [a, sstar]
    ring
  rw [← sq_le_sq₀ (by positivity) (norm_nonneg _), hnorm]
  by_cases htlow : t ≤ 1 / 10
  · have hfactor : 0 ≤ (t - 1 / 10) * (4 * t - 7) :=
      mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    have hstar : 1 ≤ sstar := by
      dsimp [sstar]
      nlinarith only [ht0, htlow, sq_nonneg t]
    have hdist : (1 - sstar) ^ 2 ≤ (s - sstar) ^ 2 := by
      have hprod : 0 ≤ (s - 1) * (s + 1 - 2 * sstar) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
      nlinarith only [hprod]
    have hP1 : (2 + a) ^ 2 + 4 * t ≤ (2 * s + a) ^ 2 + 4 * s * t := by
      dsimp [a, sstar] at hdist ⊢
      nlinarith only [hdist]
    by_cases ht64 : 1 / 64 ≤ t
    · nlinarith only [hP1, ht64, sq_nonneg (2 + a)]
    · have hA : 2 + a ≤ -3 / 5 := by
        dsimp [a]
        nlinarith only [ht0, ht64, sq_nonneg t]
      have hneg : 0 ≤ -(2 + a) := by linarith only [hA]
      have hsq : (7 / 50) ^ 2 ≤ (2 + a) ^ 2 := by
        rw [show (2 + a) ^ 2 = (-(2 + a)) ^ 2 by ring]
        exact (sq_le_sq₀ (by norm_num) hneg).2 (by linarith only [hA])
      nlinarith only [hP1, hsq, ht0]
  · have htlo : 1 / 10 ≤ t := by linarith only [htlow]
    by_cases htmid : t ≤ 1 / 2
    · have hquad : 8 * t ^ 2 - 49 / 5 * t + 1 / 2 ≤ 0 := by
        have hfactor : (t - 1 / 10) * (8 * (t + 1 / 10) - 49 / 5) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
        nlinarith only [hfactor]
      have hfactor : 0 ≤
          (t - 1 / 2) * (8 * t ^ 2 - 49 / 5 * t + 1 / 2) :=
        mul_nonneg_of_nonpos_of_nonpos (by linarith) hquad
      have hminimum : 1 / 4 ≤ t * (8 * t ^ 2 - 69 / 5 * t + 27 / 5) := by
        nlinarith only [hfactor]
      rw [hcomplete]
      nlinarith only [hminimum, sq_nonneg (s - sstar)]
    · have hthi : 1 / 2 ≤ t := by linarith only [htmid]
      have hfactor : (t - 1 / 2) * (4 * (t + 1 / 2) - 37 / 5) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      have hstar : sstar ≤ 0 := by
        dsimp [sstar]
        nlinarith only [hfactor]
      have hdist : (-sstar) ^ 2 ≤ (s - sstar) ^ 2 := by
        have hprod : 0 ≤ s * (s - 2 * sstar) := mul_nonneg hs0 (by linarith)
        nlinarith only [hprod]
      have hP0 : a ^ 2 ≤ (2 * s + a) ^ 2 + 4 * s * t := by
        dsimp [a, sstar] at hdist ⊢
        nlinarith only [hdist]
      have hA : a ≤ -7 / 50 := by
        dsimp [a]
        nlinarith only [hthi, ht1, sq_nonneg (t - 4 / 5)]
      have hneg : 0 ≤ -a := by linarith only [hA]
      have hsq : (7 / 50) ^ 2 ≤ a ^ 2 := by
        rw [show a ^ 2 = (-a) ^ 2 by ring]
        exact (sq_le_sq₀ (by norm_num) hneg).2 (by linarith only [hA])
      nlinarith only [hP0, hsq]


-- @@ L2660-2664 verbatim
/-- The trace-free Hessian of the seed is uniformly separated from zero. -/
theorem counterexampleSeed_traceFreeHessian_norm_lower (z : ℂ) :
    7 / 50 ≤ ‖traceFreeHessian counterexampleSeed z‖ := by
  rw [traceFreeHessian_counterexampleSeed]
  exact seven_div_fifty_le_norm_seedTraceFreeHessianModel z


-- @@ L2666-2714 verbatim
/-- A deliberately crude uniform upper bound for the seed's trace-free Hessian. -/
theorem counterexampleSeed_traceFreeHessian_norm_upper (z : ℂ) :
    ‖traceFreeHessian counterexampleSeed z‖ ≤ 47 / 10 := by
  rw [traceFreeHessian_counterexampleSeed]
  have hre : |Real.cos (2 * z.re) + 6 / 5 * Real.cos (2 * z.im) -
      1 / 2 * Real.cos (4 * z.im)| ≤ 1 + 6 / 5 + 1 / 2 := by
    calc
      _ ≤ |Real.cos (2 * z.re)| + |6 / 5 * Real.cos (2 * z.im)| +
          |1 / 2 * Real.cos (4 * z.im)| := by
        exact (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ = |Real.cos (2 * z.re)| + 6 / 5 * |Real.cos (2 * z.im)| +
          1 / 2 * |Real.cos (4 * z.im)| := by
        rw [abs_mul, abs_mul]
        norm_num
      _ ≤ 1 + 6 / 5 + 1 / 2 := by
        exact add_le_add
          (add_le_add (Real.abs_cos_le_one _)
            (by simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (2 * z.im))
                (by norm_num : (0 : ℝ) ≤ 6 / 5))))
          (by simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one (4 * z.im))
              (by norm_num : (0 : ℝ) ≤ 1 / 2)))
  have him : |2 * Real.cos z.re * Real.cos z.im| ≤ 2 := by
    rw [abs_mul, abs_mul]
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      2 * |Real.cos z.re| * |Real.cos z.im| ≤ 2 * 1 * 1 := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _)
            (by norm_num : (0 : ℝ) ≤ 2))
          (Real.abs_cos_le_one _) (abs_nonneg (Real.cos z.im))
          (by norm_num)
      _ = 2 := by norm_num
  calc
    ‖seedTraceFreeHessianModel z‖ ≤
        |Real.cos (2 * z.re) + 6 / 5 * Real.cos (2 * z.im) -
          1 / 2 * Real.cos (4 * z.im)| +
        |2 * Real.cos z.re * Real.cos z.im| := by
      rw [seedTraceFreeHessianModel]
      calc
        _ ≤ ‖((Real.cos (2 * z.re) + 6 / 5 * Real.cos (2 * z.im) -
              1 / 2 * Real.cos (4 * z.im) : ℝ) : ℂ)‖ +
            ‖((2 * Real.cos z.re * Real.cos z.im : ℝ) : ℂ) * Complex.I‖ :=
          norm_add_le _ _
        _ = _ := by rw [Complex.norm_real, norm_mul, Complex.norm_real, Complex.norm_I,
          mul_one, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (1 + 6 / 5 + 1 / 2) + 2 := add_le_add hre him
    _ = 47 / 10 := by norm_num


-- @@ L2716-2769 verbatim
/-- The scalar trace of the seed Hessian has a uniform absolute-value bound. -/
theorem counterexampleSeed_chartLaplacian_abs_le (z : ℂ) :
    |let H := fderiv ℝ (fun w ↦ fderiv ℝ counterexampleSeed w) z;
      H 1 1 + H Complex.I Complex.I| ≤ 47 / 10 := by
  rw [show (fun w ↦ fderiv ℝ counterexampleSeed w) = seedGradient by
    funext w
    exact (hasFDerivAt_counterexampleSeed w).fderiv]
  rw [(hasFDerivAt_seedGradient z).fderiv]
  have hformula : seedHessian z 1 1 + seedHessian z Complex.I Complex.I =
      Real.cos (2 * z.re) - 6 / 5 * Real.cos (2 * z.im) +
        1 / 2 * Real.cos (4 * z.im) - 2 * Real.sin z.re * Real.sin z.im := by
    simp [seedHessian]
    ring
  rw [hformula]
  have htriangle :
      |Real.cos (2 * z.re) - 6 / 5 * Real.cos (2 * z.im) +
          1 / 2 * Real.cos (4 * z.im) - 2 * Real.sin z.re * Real.sin z.im| ≤
        |Real.cos (2 * z.re)| + |-6 / 5 * Real.cos (2 * z.im)| +
          |1 / 2 * Real.cos (4 * z.im)| + |-2 * Real.sin z.re * Real.sin z.im| := by
    rw [sub_eq_add_neg, sub_eq_add_neg]
    rw [show -(6 / 5 * Real.cos (2 * z.im)) =
        -6 / 5 * Real.cos (2 * z.im) by ring,
      show -(2 * Real.sin z.re * Real.sin z.im) =
        -2 * Real.sin z.re * Real.sin z.im by ring]
    calc
      _ ≤ |Real.cos (2 * z.re) + -6 / 5 * Real.cos (2 * z.im) +
            1 / 2 * Real.cos (4 * z.im)| +
          |-2 * Real.sin z.re * Real.sin z.im| := abs_add_le ..
      _ ≤ (|Real.cos (2 * z.re) + -6 / 5 * Real.cos (2 * z.im)| +
            |1 / 2 * Real.cos (4 * z.im)|) +
          |-2 * Real.sin z.re * Real.sin z.im| := by
        simpa [add_assoc, add_comm, add_left_comm] using
          add_le_add_right
            (abs_add_le
              (Real.cos (2 * z.re) + -6 / 5 * Real.cos (2 * z.im))
              (1 / 2 * Real.cos (4 * z.im)))
            |-2 * Real.sin z.re * Real.sin z.im|
      _ ≤ ((|Real.cos (2 * z.re)| + |-6 / 5 * Real.cos (2 * z.im)|) +
            |1 / 2 * Real.cos (4 * z.im)|) +
          |-2 * Real.sin z.re * Real.sin z.im| := by
        simpa [add_assoc, add_comm, add_left_comm] using
          add_le_add_right
            (add_le_add_right
              (abs_add_le (Real.cos (2 * z.re))
                (-6 / 5 * Real.cos (2 * z.im)))
              |1 / 2 * Real.cos (4 * z.im)|)
            |-2 * Real.sin z.re * Real.sin z.im|
  refine htriangle.trans ?_
  simp only [abs_mul]
  norm_num
  have hsin : |Real.sin z.re| * |Real.sin z.im| ≤ 1 :=
    mul_le_one₀ (Real.abs_sin_le_one _) (abs_nonneg _) (Real.abs_sin_le_one _)
  nlinarith only [Real.abs_cos_le_one (2 * z.re),
    Real.abs_cos_le_one (2 * z.im), Real.abs_cos_le_one (4 * z.im), hsin]


-- @@ L2771-2777 verbatim
/-- The first Wirtinger derivative of the seed has a uniform norm bound. -/
theorem counterexampleSeed_wirtinger_norm_upper (z : ℂ) :
    ‖((fderiv ℝ counterexampleSeed z 1 : ℂ) -
        (fderiv ℝ counterexampleSeed z Complex.I : ℂ) * Complex.I) / 2‖ ≤ 129 / 80 := by
  rw [(hasFDerivAt_counterexampleSeed z).fderiv]
  rw [← seedWirtingerModel_eq_gradient]
  exact norm_seedWirtingerModel_le z


-- @@ L2779-2821 verbatim
/-- The normalized seed Hessian has a global continuous argument, chosen evenly under
`z ↦ -z`. This is what makes the half-integral powers for odd `k` contribute no extra winding. -/
private theorem exists_even_continuous_seed_argument :
    ∃ θ : ℂ → ℝ, Continuous θ ∧
      (∀ z, Complex.exp ((θ z : ℂ) * Complex.I) =
        seedTraceFreeHessianModel z / ‖seedTraceFreeHessianModel z‖) ∧
      ∀ z, θ (-z) = θ z := by
  have hmodel0 (z : ℂ) : seedTraceFreeHessianModel z ≠ 0 := by
    rw [← norm_pos_iff]
    exact (by norm_num : (0 : ℝ) < 7 / 50).trans_le
      (seven_div_fifty_le_norm_seedTraceFreeHessianModel z)
  have hmodel_cont : Continuous seedTraceFreeHessianModel := by
    unfold seedTraceFreeHessianModel
    fun_prop
  have hmodel_even := seedTraceFreeHessianModel_neg
  let qCircle : C(ℂ, Circle) :=
    ⟨fun z ↦ ⟨seedTraceFreeHessianModel z / ‖seedTraceFreeHessianModel z‖,
      mem_sphere_zero_iff_norm.2 <| by
        rw [norm_div]
        simp [hmodel0 z]⟩,
      (hmodel_cont.div (Complex.continuous_ofReal.comp hmodel_cont.norm)
        (fun z ↦ Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hmodel0 z)))).subtype_mk _⟩
  let θ0 := Complex.arg (qCircle 0 : ℂ)
  rcases Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts qCircle 0 θ0
      (Circle.exp_arg (qCircle 0)) with ⟨θ, ⟨-, hθ⟩, -⟩
  have hθ' (z : ℂ) : Circle.exp (θ z) = qCircle z := congrFun hθ z
  have hθeven : (fun z : ℂ ↦ θ (-z)) = θ := by
    refine Circle.isCoveringMap_exp.eq_of_comp_eq
      (θ.continuous.comp continuous_neg) θ.continuous ?_ (0 : ℂ) ?_
    · funext z
      simp only [Function.comp_apply]
      rw [hθ', hθ']
      apply Subtype.ext
      change seedTraceFreeHessianModel (-z) / ‖seedTraceFreeHessianModel (-z)‖ =
        seedTraceFreeHessianModel z / ‖seedTraceFreeHessianModel z‖
      rw [hmodel_even]
    · simp
  refine ⟨θ, θ.continuous, ?_, fun z ↦ congrFun hθeven z⟩
  intro z
  have hz := congrArg (fun w : Circle ↦ (w : ℂ)) (hθ' z)
  change Complex.exp ((θ z : ℂ) * Complex.I) =
    seedTraceFreeHessianModel z / ‖seedTraceFreeHessianModel z‖ at hz
  exact hz


-- @@ L2823-2885 verbatim
/-- The lifted leading Hessian model on a circle has argument change `2π(2+k)`. The path in
the seed variable is chosen continuously, rather than by the discontinuous principal branch. -/
private theorem exists_seed_leading_argument (k : ℕ) (a c : ℝ) :
    ∃ θ : ℝ → ℝ, Continuous θ ∧
      (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
        Complex.exp (((c + (2 + k : ℕ) * t : ℝ) : ℂ) * Complex.I) *
          star (seedTraceFreeHessianModel
            ((a : ℂ) * Complex.exp (((k / 2 * t : ℝ) : ℂ) * Complex.I))) /
          ‖seedTraceFreeHessianModel
            ((a : ℂ) * Complex.exp (((k / 2 * t : ℝ) : ℂ) * Complex.I))‖) ∧
      θ (2 * Real.pi) - θ 0 = 2 * Real.pi * ((2 + k : ℕ) : ℤ) := by
  rcases exists_even_continuous_seed_argument with ⟨φ, hφcont, hφ, hφeven⟩
  let w : ℝ → ℂ := fun t ↦
    (a : ℂ) * Complex.exp (((k / 2 * t : ℝ) : ℂ) * Complex.I)
  let θ : ℝ → ℝ := fun t ↦ c + (2 + k : ℕ) * t - φ (w t)
  have hwcont : Continuous w := by
    fun_prop
  have hθcont : Continuous θ := by
    fun_prop
  have hphase (t : ℝ) : Complex.exp ((θ t : ℂ) * Complex.I) =
      Complex.exp (((c + (2 + k : ℕ) * t : ℝ) : ℂ) * Complex.I) *
        star (seedTraceFreeHessianModel (w t)) / ‖seedTraceFreeHessianModel (w t)‖ := by
    have hs := congrArg star (hφ (w t))
    rw [show ((θ t : ℂ) * Complex.I) =
      (((c + (2 + k : ℕ) * t : ℝ) : ℂ) * Complex.I) +
        -((φ (w t) : ℂ) * Complex.I) by simp [θ]; ring, Complex.exp_add]
    have hs' : Complex.exp (-((φ (w t) : ℂ) * Complex.I)) =
        star (seedTraceFreeHessianModel (w t)) /
          ‖seedTraceFreeHessianModel (w t)‖ := by
      calc
        _ = star (Complex.exp ((φ (w t) : ℂ) * Complex.I)) := by
          change Complex.exp (-((φ (w t) : ℂ) * Complex.I)) =
            (starRingEnd ℂ) (Complex.exp ((φ (w t) : ℂ) * Complex.I))
          rw [← Complex.exp_conj]
          congr 1
          simp
        _ = star (seedTraceFreeHessianModel (w t) /
            ‖seedTraceFreeHessianModel (w t)‖) := hs
        _ = _ := by simp
    rw [hs']
    ring
  have hexp : Complex.exp ((((k : ℝ) * Real.pi : ℂ) * Complex.I)) = (-1 : ℂ) ^ k := by
    rw [show (((k : ℝ) * Real.pi : ℂ) * Complex.I) =
      (k : ℂ) * ((Real.pi : ℂ) * Complex.I) by push_cast; ring,
      Complex.exp_nat_mul, Complex.exp_pi_mul_I]
  have hwendpoint : φ (w (2 * Real.pi)) = φ (w 0) := by
    have hwvalue : w (2 * Real.pi) = (a : ℂ) * (-1 : ℂ) ^ k := by
      simp only [w]
      rw [show k / 2 * (2 * Real.pi) = (k : ℝ) * Real.pi by ring]
      congr 1
      simpa only [Complex.ofReal_mul] using hexp
    rcases neg_one_pow_eq_or ℂ k with hk | hk
    · rw [hwvalue, hk]
      simp [w]
    · rw [hwvalue, hk]
      simpa [w] using hφeven (a : ℂ)
  refine ⟨θ, hθcont, fun t ↦ by simpa [w] using hphase t, ?_⟩
  dsimp [θ]
  rw [hwendpoint]
  have hcast : ((2 + k : ℕ) : ℝ) = ((2 + (k : ℤ) : ℤ) : ℝ) := by
    norm_num
  rw [hcast]
  ring


-- @@ L2887-2914 verbatim
/-- Lifting a homotopy through the exponential covering preserves the total argument change
when every stage has matching endpoints. -/
private theorem homotopy_preserves_argument_change (H : C(I × ℝ, Circle))
    (θ0 : C(ℝ, ℝ)) (T C : ℝ) (hH0 : ∀ t, H (0, t) = Circle.exp (θ0 t))
    (hperiodic : ∀ s, H (s, T) = H (s, 0)) (hchange : θ0 T - θ0 0 = C)
    (hC : Circle.exp C = 1) :
    ∃ θ : ℝ → ℝ, Continuous θ ∧ (∀ t, Circle.exp (θ t) = H (1, t)) ∧
      θ T - θ 0 = C := by
  let Θ := Circle.isCoveringMap_exp.liftHomotopy H θ0 hH0
  have hΘ (s : I) (t : ℝ) : Circle.exp (Θ (s, t)) = H (s, t) := by
    exact congrFun (Circle.isCoveringMap_exp.liftHomotopy_lifts H θ0 hH0) (s, t)
  have hendpoint : (fun s : I ↦ Θ (s, T)) = fun s ↦ Θ (s, 0) + C := by
    refine Circle.isCoveringMap_exp.eq_of_comp_eq
      (Θ.continuous.comp (continuous_id.prodMk continuous_const))
      ((Θ.continuous.comp (continuous_id.prodMk continuous_const)).add continuous_const)
      ?_ (0 : I) ?_
    · funext s
      simp only [Function.comp_apply]
      rw [Circle.exp_add, hC, mul_one, hΘ, hΘ, hperiodic]
    · change Θ (0, T) = Θ (0, 0) + C
      rw [Circle.isCoveringMap_exp.liftHomotopy_zero,
        Circle.isCoveringMap_exp.liftHomotopy_zero]
      linarith
  refine ⟨fun t ↦ Θ (1, t),
    Θ.continuous.comp (continuous_const.prodMk continuous_id), fun t ↦ hΘ 1 t, ?_⟩
  have := congrFun hendpoint 1
  change Θ (1, T) = Θ (1, 0) + C at this
  linarith


-- @@ L2916-2924 verbatim
/-- A positive real power of the radius tends to zero on the punctured complex plane. -/
private theorem tendsto_norm_rpow_nhdsWithin_zero {p : ℝ} (hp : 0 < p) :
    Tendsto (fun z : ℂ ↦ ‖z‖ ^ p) (𝓝[≠] 0) (𝓝 0) := by
  have hrpow := (Real.continuousAt_rpow_const 0 p (.inr hp.le)).tendsto
  have hnormAt : ContinuousAt (fun z : ℂ ↦ ‖z‖) 0 := continuous_norm.continuousAt
  have hnorm : Tendsto (fun z : ℂ ↦ ‖z‖) (𝓝[≠] 0) (𝓝 0) := by
    simpa using hnormAt.tendsto.mono_left
      (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 from inf_le_left)
  simpa only [Function.comp_def, Real.zero_rpow hp.ne'] using hrpow.comp hnorm


-- @@ L2926-2935 verbatim
/-- The three powers occurring in the Hessian error-to-leading ratios all tend to zero for
positive `k`. -/
private theorem counterexample_error_powers_tendsto_zero (k : ℕ) (hk : 0 < k) :
    Tendsto (fun z : ℂ ↦ ‖z‖ ^ ((k : ℝ) / 2)) (𝓝[≠] 0) (𝓝 0) ∧
    Tendsto (fun z : ℂ ↦ ‖z‖ ^ ((k : ℝ) / 2 - 1 / 4)) (𝓝[≠] 0) (𝓝 0) ∧
    Tendsto (fun z : ℂ ↦ ‖z‖ ^ ((k : ℝ) - 1 / 2)) (𝓝[≠] 0) (𝓝 0) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  refine ⟨tendsto_norm_rpow_nhdsWithin_zero (by positivity),
    tendsto_norm_rpow_nhdsWithin_zero (by linarith),
    tendsto_norm_rpow_nhdsWithin_zero (by linarith)⟩


-- @@ L2937-2988 verbatim
/-- A perturbation smaller in norm than a nonvanishing leading term has the same argument
change. The proof uses the normalized straight-line homotopy. -/
private theorem exists_argument_of_norm_error_lt (leading error : ℝ → ℂ) (T C : ℝ)
    (hleading : Continuous leading) (herror : Continuous error)
    (hsmall : ∀ t, ‖error t‖ < ‖leading t‖)
    (hperiodicLeading : leading T = leading 0) (hperiodicError : error T = error 0)
    (θ0 : ℝ → ℝ) (hθ0 : Continuous θ0)
    (hphase0 : ∀ t, Complex.exp ((θ0 t : ℂ) * Complex.I) = leading t / ‖leading t‖)
    (hchange : θ0 T - θ0 0 = C) (hC : Circle.exp C = 1) :
    ∃ θ : ℝ → ℝ, Continuous θ ∧
      (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
        (leading t + error t) / ‖leading t + error t‖) ∧
      θ T - θ 0 = C := by
  have hne (s : I) (t : ℝ) : leading t + (s : ℝ) • error t ≠ 0 := by
    intro hzero
    have heq : leading t = -((s : ℝ) • error t) := eq_neg_of_add_eq_zero_left hzero
    have hle : ‖leading t‖ ≤ ‖error t‖ := by
      rw [heq, norm_neg, norm_smul, Real.norm_of_nonneg s.2.1]
      exact mul_le_of_le_one_left (norm_nonneg _) s.2.2
    exact (not_lt_of_ge hle) (hsmall t)
  have hscalar : Continuous (fun st : I × ℝ ↦ (st.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have herror' : Continuous (fun st : I × ℝ ↦ error st.2) :=
    herror.comp continuous_snd
  have htotal : Continuous (fun st : I × ℝ ↦
      leading st.2 + (st.1 : ℝ) • error st.2) :=
    (hleading.comp continuous_snd).add (hscalar.smul herror')
  let H : C(I × ℝ, Circle) :=
    ⟨fun st ↦ ⟨(leading st.2 + (st.1 : ℝ) • error st.2) /
          ‖leading st.2 + (st.1 : ℝ) • error st.2‖, mem_sphere_zero_iff_norm.2 <| by
        rw [norm_div]
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_norm]
        exact div_self (norm_ne_zero_iff.mpr (hne st.1 st.2))⟩,
      (htotal.div
          (Complex.continuous_ofReal.comp htotal.norm)
          (fun st ↦ Complex.ofReal_ne_zero.mpr
            (norm_ne_zero_iff.mpr (hne st.1 st.2)))).subtype_mk _⟩
  let θ0Map : C(ℝ, ℝ) := ⟨θ0, hθ0⟩
  have hH0 (t : ℝ) : H (0, t) = Circle.exp (θ0Map t) := by
    apply Subtype.ext
    simpa [H, θ0Map, smul_eq_mul] using (hphase0 t).symm
  have hHperiodic (s : I) : H (s, T) = H (s, 0) := by
    apply Subtype.ext
    change (leading T + (s : ℝ) • error T) / ‖leading T + (s : ℝ) • error T‖ =
      (leading 0 + (s : ℝ) • error 0) / ‖leading 0 + (s : ℝ) • error 0‖
    rw [hperiodicLeading, hperiodicError]
  rcases homotopy_preserves_argument_change H θ0Map T C hH0 hHperiodic hchange hC with
    ⟨θ, hθ, hphase, hθchange⟩
  refine ⟨θ, hθ, ?_, hθchange⟩
  intro t
  have ht := congrArg (fun w : Circle ↦ (w : ℂ)) (hphase t)
  simpa [H] using ht


-- @@ L2990-2993 verbatim
/-- The radial amplitude in the counterexample, separated from the oscillatory seed. -/
private noncomputable def counterexampleRadialAmplitude (r : ℝ) : ℝ :=
  r ^ 2 * Real.exp (-Real.rpow r (-(1 : ℝ) / 4) * Real.exp (-(r ^ 2))) /
    (1 + r ^ 2)


-- @@ L2995-2998 verbatim
/-- The logarithmic derivative of the radial amplitude on the positive real axis. -/
private noncomputable def counterexampleRadialLogDerivOne (r : ℝ) : ℝ :=
  2 / r - 2 * r / (1 + r ^ 2) + Real.exp (-(r ^ 2)) *
    (1 / 4 * Real.rpow r (-(5 : ℝ) / 4) + 2 * Real.rpow r (3 / 4))


-- @@ L3000-3004 verbatim
/-- The derivative of `counterexampleRadialLogDerivOne` on the positive real axis. -/
private noncomputable def counterexampleRadialLogDerivTwo (r : ℝ) : ℝ :=
  -2 / r ^ 2 + 2 * (r ^ 2 - 1) / (1 + r ^ 2) ^ 2 + Real.exp (-(r ^ 2)) *
    (Real.rpow r (-(1 : ℝ) / 4) - 5 / 16 * Real.rpow r (-(9 : ℝ) / 4) -
      4 * Real.rpow r (7 / 4))


-- @@ L3006-3125 verbatim
/-- Crude radial logarithmic-derivative bounds, sufficient for the Hessian error estimate. -/
private theorem counterexampleRadialLogDeriv_bounds {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    |counterexampleRadialLogDerivOne r| ≤ 7 * r ^ (-(5 : ℝ) / 4) ∧
      |counterexampleRadialLogDerivTwo r| ≤ 10 * r ^ (-(9 : ℝ) / 4) := by
  have hexp0 : 0 ≤ Real.exp (-(r ^ 2)) := (Real.exp_pos _).le
  have hexp1 : Real.exp (-(r ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg r))
  have hpFive : 0 < r ^ (-(5 : ℝ) / 4) := Real.rpow_pos_of_pos hr _
  have hpNine : 0 < r ^ (-(9 : ℝ) / 4) := Real.rpow_pos_of_pos hr _
  have hFiveOne : 1 ≤ r ^ (-(5 : ℝ) / 4) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by norm_num)
  have hNineOne : 1 ≤ r ^ (-(9 : ℝ) / 4) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr hr1 (by norm_num)
  have hNegOneFive : r ^ (-(1 : ℝ)) ≤ r ^ (-(5 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by norm_num)
  have hNegTwoNine : r ^ (-(2 : ℝ)) ≤ r ^ (-(9 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by norm_num)
  have hThreeFive : r ^ ((3 : ℝ) / 4) ≤ r ^ (-(5 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by norm_num)
  have hOneNine : r ^ (-(1 : ℝ) / 4) ≤ r ^ (-(9 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by norm_num)
  have hSevenNine : r ^ ((7 : ℝ) / 4) ≤ r ^ (-(9 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_ge hr hr1 (by norm_num)
  have hfirst : |2 / r| ≤ 2 * r ^ (-(5 : ℝ) / 4) := by
    rw [abs_div, abs_of_nonneg (by norm_num), abs_of_pos hr]
    rw [div_eq_mul_inv, ← Real.rpow_neg_one]
    gcongr
  have hsecond : |2 * r / (1 + r ^ 2)| ≤ 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num), abs_of_pos hr,
      abs_of_pos (by positivity : 0 < 1 + r ^ 2)]
    apply (div_le_iff₀ (by positivity : 0 < 1 + r ^ 2)).2
    nlinarith
  have hexpTerm : Real.exp (-(r ^ 2)) *
      (1 / 4 * r ^ (-(5 : ℝ) / 4) + 2 * r ^ ((3 : ℝ) / 4)) ≤
      9 / 4 * r ^ (-(5 : ℝ) / 4) := by
    calc
      _ ≤ 1 * (1 / 4 * r ^ (-(5 : ℝ) / 4) +
          2 * r ^ ((3 : ℝ) / 4)) := by gcongr
      _ ≤ _ := by nlinarith only [hThreeFive, hpFive]
  constructor
  · rw [counterexampleRadialLogDerivOne]
    calc
      |2 / r - 2 * r / (1 + r ^ 2) + Real.exp (-(r ^ 2)) *
          (1 / 4 * r ^ (-(5 : ℝ) / 4) + 2 * r ^ ((3 : ℝ) / 4))| ≤
          |2 / r| + |2 * r / (1 + r ^ 2)| +
            |Real.exp (-(r ^ 2)) *
              (1 / 4 * r ^ (-(5 : ℝ) / 4) + 2 * r ^ ((3 : ℝ) / 4))| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
      _ ≤ 2 * r ^ (-(5 : ℝ) / 4) + 2 +
          9 / 4 * r ^ (-(5 : ℝ) / 4) := by
        gcongr
        rw [abs_of_nonneg (mul_nonneg hexp0 (by positivity))]
        exact hexpTerm
      _ ≤ 7 * r ^ (-(5 : ℝ) / 4) := by nlinarith only [hFiveOne]
  · have hmiddle : |2 * (r ^ 2 - 1) / (1 + r ^ 2) ^ 2| ≤ 2 := by
      rw [abs_div, abs_mul, abs_of_nonneg (by norm_num),
        abs_of_pos (by positivity : 0 < (1 + r ^ 2) ^ 2)]
      have hrsq : r ^ 2 ≤ 1 := by nlinarith
      have habs : |r ^ 2 - 1| ≤ 1 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
      apply (div_le_iff₀ (by positivity : 0 < (1 + r ^ 2) ^ 2)).2
      nlinarith [sq_nonneg (r ^ 2)]
    have hexpTermTwo : |Real.exp (-(r ^ 2)) *
        (r ^ (-(1 : ℝ) / 4) - 5 / 16 * r ^ (-(9 : ℝ) / 4) -
          4 * r ^ ((7 : ℝ) / 4))| ≤ 85 / 16 * r ^ (-(9 : ℝ) / 4) := by
      rw [abs_mul, abs_of_nonneg hexp0]
      have hinside :
          |r ^ (-(1 : ℝ) / 4) - 5 / 16 * r ^ (-(9 : ℝ) / 4) -
              4 * r ^ ((7 : ℝ) / 4)| ≤
            r ^ (-(1 : ℝ) / 4) + 5 / 16 * r ^ (-(9 : ℝ) / 4) +
              4 * r ^ ((7 : ℝ) / 4) := by
        calc
          _ ≤ |r ^ (-(1 : ℝ) / 4) - 5 / 16 * r ^ (-(9 : ℝ) / 4)| +
              |4 * r ^ ((7 : ℝ) / 4)| := abs_sub ..
          _ ≤ |r ^ (-(1 : ℝ) / 4)| + |5 / 16 * r ^ (-(9 : ℝ) / 4)| +
              |4 * r ^ ((7 : ℝ) / 4)| := add_le_add (abs_sub _ _) le_rfl
          _ = _ := by
            rw [abs_mul, abs_mul, abs_of_nonneg, abs_of_nonneg, abs_of_nonneg,
              abs_of_nonneg, abs_of_nonneg]
            all_goals positivity
      calc
        Real.exp (-(r ^ 2)) *
            |r ^ (-(1 : ℝ) / 4) - 5 / 16 * r ^ (-(9 : ℝ) / 4) -
              4 * r ^ ((7 : ℝ) / 4)| ≤
            1 * (r ^ (-(1 : ℝ) / 4) + 5 / 16 * r ^ (-(9 : ℝ) / 4) +
              4 * r ^ ((7 : ℝ) / 4)) := by gcongr
        _ ≤ _ := by nlinarith only [hOneNine, hSevenNine, hpNine]
    rw [counterexampleRadialLogDerivTwo]
    calc
      |-2 / r ^ 2 + 2 * (r ^ 2 - 1) / (1 + r ^ 2) ^ 2 +
          Real.exp (-(r ^ 2)) *
            (r ^ (-(1 : ℝ) / 4) - 5 / 16 * r ^ (-(9 : ℝ) / 4) -
              4 * r ^ ((7 : ℝ) / 4))| ≤
          |2 / r ^ 2| + |2 * (r ^ 2 - 1) / (1 + r ^ 2) ^ 2| +
            |Real.exp (-(r ^ 2)) *
              (r ^ (-(1 : ℝ) / 4) - 5 / 16 * r ^ (-(9 : ℝ) / 4) -
                4 * r ^ ((7 : ℝ) / 4))| := by
        calc
          _ ≤ |-2 / r ^ 2 + 2 * (r ^ 2 - 1) / (1 + r ^ 2) ^ 2| +
              |Real.exp (-(r ^ 2)) *
                (r ^ (-(1 : ℝ) / 4) - 5 / 16 * r ^ (-(9 : ℝ) / 4) -
                  4 * r ^ ((7 : ℝ) / 4))| := abs_add_le ..
          _ ≤ (|-2 / r ^ 2| + |2 * (r ^ 2 - 1) / (1 + r ^ 2) ^ 2|) +
              |Real.exp (-(r ^ 2)) *
                (r ^ (-(1 : ℝ) / 4) - 5 / 16 * r ^ (-(9 : ℝ) / 4) -
                  4 * r ^ ((7 : ℝ) / 4))| :=
            add_le_add (abs_add_le _ _) le_rfl
          _ = _ := by
            rw [show -2 / r ^ 2 = -(2 / r ^ 2) by ring, abs_neg]
      _ ≤ 2 * r ^ (-(9 : ℝ) / 4) + 2 +
          85 / 16 * r ^ (-(9 : ℝ) / 4) := by
        gcongr
        have hinv : (r ^ 2)⁻¹ = r ^ (-(2 : ℝ)) := by
          calc
            (r ^ 2)⁻¹ = (r ^ (2 : ℝ))⁻¹ :=
              congrArg Inv.inv (Real.rpow_natCast r 2).symm
            _ = r ^ (-(2 : ℝ)) := (Real.rpow_neg hr.le (2 : ℝ)).symm
        rw [abs_div, abs_of_nonneg (by norm_num), abs_of_pos (sq_pos_of_pos hr),
          div_eq_mul_inv, hinv]
        exact mul_le_mul_of_nonneg_left hNegTwoNine (by norm_num)
      _ ≤ 10 * r ^ (-(9 : ℝ) / 4) := by nlinarith only [hNineOne]


-- @@ L3127-3172 verbatim
private theorem hasDerivAt_counterexampleRadialExponent {r : ℝ} (hr : 0 < r) :
    HasDerivAt
      (fun x : ℝ ↦ -Real.rpow x (-(1 : ℝ) / 4) * Real.exp (-(x ^ 2)))
      (Real.exp (-(r ^ 2)) *
        (1 / 4 * Real.rpow r (-(5 : ℝ) / 4) + 2 * Real.rpow r (3 / 4))) r := by
  have hpow :=
    (Real.hasDerivAt_rpow_const (x := r) (p := -(1 : ℝ) / 4) (Or.inl hr.ne')).neg
  have hexp := ((hasDerivAt_id r).pow 2).neg.exp
  have hpow' : HasDerivAt (fun x : ℝ ↦ -Real.rpow x (-(1 : ℝ) / 4))
      (1 / 4 * Real.rpow r (-(5 : ℝ) / 4)) r := by
    convert hpow using 1
    all_goals first
      | with_reducible_and_instances rfl
      | simp only [Real.rpow_eq_pow]
        rw [show -(1 : ℝ) / 4 - 1 = -5 / 4 by ring]
        ring
  have hexp' : HasDerivAt (fun x : ℝ ↦ Real.exp (-(x ^ 2)))
      (-2 * r * Real.exp (-(r ^ 2))) r := by
    convert hexp using 1 <;>
      simp [Function.comp_def, Pi.neg_apply, Pi.pow_apply, id_eq] <;> ring
  have hrpow : r * Real.rpow r (-(1 : ℝ) / 4) = Real.rpow r (3 / 4) := by
    calc
      r * Real.rpow r (-(1 : ℝ) / 4) =
          Real.rpow r 1 * Real.rpow r (-(1 : ℝ) / 4) :=
        congrArg (fun x ↦ x * Real.rpow r (-(1 : ℝ) / 4)) (Real.rpow_one r).symm
      _ = Real.rpow r (1 + (-(1 : ℝ) / 4)) := (Real.rpow_add hr _ _).symm
      _ = Real.rpow r (3 / 4) := by
        congr 1
        ring
  have hcoef : Real.exp (-(r ^ 2)) *
        (1 / 4 * Real.rpow r (-(5 : ℝ) / 4) + 2 * Real.rpow r (3 / 4)) =
      1 / 4 * Real.rpow r (-(5 : ℝ) / 4) * Real.exp (-(r ^ 2)) +
        -Real.rpow r (-(1 : ℝ) / 4) * (-2 * r * Real.exp (-(r ^ 2))) := by
    calc
    Real.exp (-(r ^ 2)) *
          (1 / 4 * Real.rpow r (-(5 : ℝ) / 4) + 2 * Real.rpow r (3 / 4)) =
        1 / 4 * Real.rpow r (-(5 : ℝ) / 4) * Real.exp (-(r ^ 2)) +
          2 * Real.rpow r (3 / 4) * Real.exp (-(r ^ 2)) := by ring
    _ = 1 / 4 * Real.rpow r (-(5 : ℝ) / 4) * Real.exp (-(r ^ 2)) +
          2 * (r * Real.rpow r (-(1 : ℝ) / 4)) * Real.exp (-(r ^ 2)) := by rw [hrpow]
    _ = 1 / 4 * Real.rpow r (-(5 : ℝ) / 4) * Real.exp (-(r ^ 2)) +
          -Real.rpow r (-(1 : ℝ) / 4) * (-2 * r * Real.exp (-(r ^ 2))) := by ring
  have hmul := hpow'.mul hexp'
  rw [← hcoef] at hmul
  convert hmul using 1
  all_goals first | with_reducible_and_instances rfl | simp only [Pi.mul_apply]


-- @@ L3174-3213 verbatim
private theorem hasDerivAt_counterexampleRadialAmplitude {r : ℝ} (hr : 0 < r) :
    HasDerivAt counterexampleRadialAmplitude
      (counterexampleRadialAmplitude r * counterexampleRadialLogDerivOne r) r := by
  have hE := (hasDerivAt_counterexampleRadialExponent hr).exp
  have hnum := ((hasDerivAt_id r).pow 2).mul hE
  have hden := (hasDerivAt_const r 1).add ((hasDerivAt_id r).pow 2)
  have hnum' : HasDerivAt (fun x : ℝ ↦ x ^ 2 *
      Real.exp (-Real.rpow x (-(1 : ℝ) / 4) * Real.exp (-(x ^ 2))))
      (2 * r * Real.exp (-Real.rpow r (-(1 : ℝ) / 4) * Real.exp (-(r ^ 2))) +
        r ^ 2 * (Real.exp (-Real.rpow r (-(1 : ℝ) / 4) * Real.exp (-(r ^ 2))) *
          (Real.exp (-(r ^ 2)) *
            (1 / 4 * Real.rpow r (-(5 : ℝ) / 4) + 2 * Real.rpow r (3 / 4))))) r := by
    have heq : (fun x : ℝ ↦ x ^ 2 *
        Real.exp (-Real.rpow x (-(1 : ℝ) / 4) * Real.exp (-(x ^ 2)))) =ᶠ[nhds r]
        (id ^ 2 * fun x : ℝ ↦
          Real.exp (-Real.rpow x (-(1 : ℝ) / 4) * Real.exp (-(x ^ 2)))) := by
      filter_upwards with x
      simp only [Pi.mul_apply, Pi.pow_apply, id_eq]
    with_reducible_and_instances
      convert hnum.congr_of_eventuallyEq heq using 1
    all_goals first
      | with_reducible_and_instances rfl
      | simp only [Pi.mul_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat]
        ring
  have hden' : HasDerivAt (fun x : ℝ ↦ 1 + x ^ 2) (2 * r) r := by
    have heq : (fun x : ℝ ↦ 1 + x ^ 2) =ᶠ[nhds r] ((fun _ : ℝ ↦ 1) + id ^ 2) := by
      filter_upwards with x
      simp only [Pi.add_apply, Pi.pow_apply, id_eq]
    with_reducible_and_instances
      convert hden.congr_of_eventuallyEq heq using 1
    all_goals first
      | with_reducible_and_instances rfl
      | simp only [Pi.add_apply, Pi.pow_apply, id_eq, Nat.cast_ofNat]
        ring
  unfold counterexampleRadialAmplitude counterexampleRadialLogDerivOne
  convert hnum'.div hden' (by positivity) using 1
  all_goals first
    | with_reducible_and_instances rfl
    | field_simp [hr.ne']
      ring


-- @@ L3215-3292 verbatim
private theorem hasDerivAt_counterexampleRadialLogDerivOne {r : ℝ} (hr : 0 < r) :
    HasDerivAt counterexampleRadialLogDerivOne (counterexampleRadialLogDerivTwo r) r := by
  have hr0 : r ≠ 0 := hr.ne'
  have hfirst := (hasDerivAt_const r 2).div (hasDerivAt_id r) hr0
  have hmiddle := ((hasDerivAt_const r 2).mul (hasDerivAt_id r)).div
    ((hasDerivAt_const r 1).add ((hasDerivAt_id r).pow 2)) (by dsimp; positivity)
  have hexp := ((hasDerivAt_id r).pow 2).neg.exp
  have hpFive := Real.hasDerivAt_rpow_const (x := r) (p := -(5 : ℝ) / 4) (Or.inl hr0)
  have hpThree := Real.hasDerivAt_rpow_const (x := r) (p := (3 : ℝ) / 4) (Or.inl hr0)
  have hlast := hexp.mul
    ((hasDerivAt_const r (1 / 4)).mul hpFive |>.add
      ((hasDerivAt_const r 2).mul hpThree))
  have hseven : r * Real.rpow r (3 / 4) = Real.rpow r (7 / 4) := by
    calc
      r * Real.rpow r (3 / 4) = Real.rpow r 1 * Real.rpow r (3 / 4) :=
        congrArg (fun x ↦ x * Real.rpow r (3 / 4)) (Real.rpow_one r).symm
      _ = Real.rpow r (1 + 3 / 4) := (Real.rpow_add hr _ _).symm
      _ = Real.rpow r (7 / 4) := by
        congr 1
        ring
  have hminus : r * Real.rpow r (-(5 : ℝ) / 4) = Real.rpow r (-(1 : ℝ) / 4) := by
    calc
      r * Real.rpow r (-(5 : ℝ) / 4) =
          Real.rpow r 1 * Real.rpow r (-(5 : ℝ) / 4) :=
        congrArg (fun x ↦ x * Real.rpow r (-(5 : ℝ) / 4)) (Real.rpow_one r).symm
      _ = Real.rpow r (1 + (-(5 : ℝ) / 4)) := (Real.rpow_add hr _ _).symm
      _ = Real.rpow r (-(1 : ℝ) / 4) := by
        congr 1
        ring
  have hfirst' : HasDerivAt (fun x : ℝ ↦ 2 / x) (-2 / r ^ 2) r := by
    convert hfirst using 1
    all_goals first
      | with_reducible_and_instances rfl
      | funext x
        rfl
      | simp only [Pi.div_apply, id_eq, zero_mul]
        field_simp [hr0]
        ring
  have hmiddle' : HasDerivAt (fun x : ℝ ↦ 2 * x / (1 + x ^ 2))
      (2 * (1 - r ^ 2) / (1 + r ^ 2) ^ 2) r := by
    convert hmiddle using 1
    all_goals first
      | with_reducible_and_instances rfl
      | funext x
        rfl
      | simp only [Pi.div_apply, Pi.mul_apply, Pi.add_apply, Pi.pow_apply, id_eq,
          Nat.cast_ofNat, zero_mul, zero_add]
        field_simp
        ring
  have hlast' : HasDerivAt (fun x : ℝ ↦ Real.exp (-(x ^ 2)) *
      (1 / 4 * Real.rpow x (-(5 : ℝ) / 4) + 2 * Real.rpow x (3 / 4)))
      (Real.exp (-(r ^ 2)) *
        (Real.rpow r (-(1 : ℝ) / 4) - 5 / 16 * Real.rpow r (-(9 : ℝ) / 4) -
          4 * Real.rpow r (7 / 4))) r := by
    convert hlast using 1
    all_goals first
      | with_reducible_and_instances rfl
      | funext x
        simp only [Pi.mul_apply, Pi.add_apply, Pi.neg_apply, Pi.pow_apply, id_eq,
          Real.rpow_eq_pow]
      | simp only [Pi.mul_apply, Pi.add_apply, Pi.neg_apply, Pi.pow_apply, id_eq,
          Nat.cast_ofNat, zero_mul, zero_add, Real.rpow_eq_pow]
        norm_num only [Nat.reduceSub, pow_one, mul_one, one_mul]
        have hseven' : r * r ^ ((3 : ℝ) / 4) = r ^ ((7 : ℝ) / 4) := by
          simpa only [← Real.rpow_eq_pow] using hseven
        have hminus' : r * r ^ (-(5 : ℝ) / 4) = r ^ (-(1 : ℝ) / 4) := by
          simpa only [← Real.rpow_eq_pow] using hminus
        have hminus'' : r * r ^ (-(5 / 4 : ℝ)) = r ^ (-(1 / 4 : ℝ)) := by
          convert hminus' using 1 <;> ring_nf
        rw [← hseven', ← hminus'']
        ring
  unfold counterexampleRadialLogDerivOne counterexampleRadialLogDerivTwo
  convert hfirst'.sub hmiddle' |>.add hlast' using 1
  all_goals first
    | with_reducible_and_instances rfl
    | funext x
      rfl
    | ring_nf


-- @@ L3294-3305 verbatim
private theorem hasDerivAt_counterexampleRadialAmplitude_deriv {r : ℝ} (hr : 0 < r) :
    HasDerivAt (fun x ↦ counterexampleRadialAmplitude x *
      counterexampleRadialLogDerivOne x)
      (counterexampleRadialAmplitude r *
        (counterexampleRadialLogDerivOne r ^ 2 + counterexampleRadialLogDerivTwo r)) r := by
  convert (hasDerivAt_counterexampleRadialAmplitude hr).mul
    (hasDerivAt_counterexampleRadialLogDerivOne hr) using 1
  all_goals first
    | with_reducible_and_instances rfl
    | funext x
      rfl
    | ring


-- @@ L3307-3325 verbatim
private theorem hasFDerivAt_norm_complex {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun w : ℂ ↦ ‖w‖)
      ((z.re / ‖z‖) • Complex.reCLM + (z.im / ‖z‖) • Complex.imCLM) z := by
  have hsquare := ((Complex.reCLM.hasFDerivAt (x := z)).pow 2).add
    ((Complex.imCLM.hasFDerivAt (x := z)).pow 2)
  have hsquare_ne : z.re ^ 2 + z.im ^ 2 ≠ 0 := by
    rw [show z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring]
    positivity
  have hsqrt := (Real.hasDerivAt_sqrt hsquare_ne).comp_hasFDerivAt z hsquare
  convert hsqrt using 1 <;> try with_reducible_and_instances rfl
  · ext w
    simp only [Function.comp_apply, Pi.add_apply, Complex.reCLM_apply, Complex.imCLM_apply]
    rw [Complex.norm_def, Complex.normSq_apply]
    ring
  · ext v
    simp [Complex.norm_def, Complex.normSq_apply]
    field_simp [norm_ne_zero_iff.mpr hz]


-- @@ L3327-3339 verbatim
private theorem hasFDerivAt_counterexampleRadialAmplitude_norm {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt (fun w : ℂ ↦ counterexampleRadialAmplitude ‖w‖)
      (((counterexampleRadialAmplitude ‖z‖ * counterexampleRadialLogDerivOne ‖z‖) *
          z.re / ‖z‖) • Complex.reCLM +
        ((counterexampleRadialAmplitude ‖z‖ * counterexampleRadialLogDerivOne ‖z‖) *
          z.im / ‖z‖) • Complex.imCLM) z := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have h := (hasDerivAt_counterexampleRadialAmplitude hr).comp_hasFDerivAt z
    (hasFDerivAt_norm_complex hz)
  apply h.congr_fderiv
  ext v
  simp
  ring


-- @@ L3341-3391 verbatim
private theorem exists_counterexampleRadialGradient_fderiv {z : ℂ} (hz : z ≠ 0) :
    ∃ R : ℂ →L[ℝ] ℂ,
      HasFDerivAt (fun w : ℂ ↦
        (counterexampleRadialAmplitude ‖w‖ * counterexampleRadialLogDerivOne ‖w‖ : ℂ) *
          w / ‖w‖) R z ∧
      R 1 + Complex.I * R Complex.I =
        (counterexampleRadialAmplitude ‖z‖ *
          (counterexampleRadialLogDerivOne ‖z‖ ^ 2 +
            counterexampleRadialLogDerivTwo ‖z‖) : ℂ) * z ^ 2 / ‖z‖ ^ 2 -
          (counterexampleRadialAmplitude ‖z‖ *
            counterexampleRadialLogDerivOne ‖z‖ : ℂ) * z ^ 2 / ‖z‖ ^ 3 := by
  have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hnorm := hasFDerivAt_norm_complex hz
  have hnorm' := Complex.ofRealCLM.hasFDerivAt.comp z hnorm
  have hAprime := (hasDerivAt_counterexampleRadialAmplitude_deriv hr).comp_hasFDerivAt z hnorm
  have hAprime' := Complex.ofRealCLM.hasFDerivAt.comp z hAprime
  have hnormInv := (hasFDerivAt_inv' (𝕜 := ℝ)
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))).comp z hnorm'
  have hquotient := (hasFDerivAt_id z).mul hnormInv
  have hgradient := hAprime'.mul hquotient
  let Fraw : ℂ → ℂ :=
    (⇑Complex.ofRealCLM ∘
      (fun x ↦ counterexampleRadialAmplitude x * counterexampleRadialLogDerivOne x) ∘ norm) *
      (id * Inv.inv ∘ ⇑Complex.ofRealCLM ∘ fun w : ℂ ↦ ‖w‖)
  let F : ℂ → ℂ := fun w ↦
      (counterexampleRadialAmplitude ‖w‖ * counterexampleRadialLogDerivOne ‖w‖ : ℂ) *
        w / ‖w‖
  have hF : Fraw = F := by
    funext w
    simp [Fraw, F, div_eq_mul_inv]
    ring
  have hgradient' : HasFDerivAt Fraw
      (fderiv ℝ Fraw z) z := by
    have hdiffRaw : DifferentiableAt ℝ Fraw z := by
      simpa only [Fraw] using hgradient.differentiableAt
    exact hdiffRaw.hasFDerivAt
  have hdiff : DifferentiableAt ℝ F z := by
    rw [← hF]
    exact hgradient'.differentiableAt
  let R : ℂ →L[ℝ] ℂ := fderiv ℝ F z
  have hR : HasFDerivAt F R z := hdiff.hasFDerivAt
  refine ⟨R, hR, ?_⟩
  dsimp only [R]
  rw [← hF]
  dsimp only [Fraw]
  rw [hgradient.fderiv]
  simp [div_eq_mul_inv]
  field_simp [norm_ne_zero_iff.mpr hz]
  apply Complex.ext <;>
    simp [pow_two, Complex.mul_re, Complex.mul_im] <;>
    ring


-- @@ L3393-3399 verbatim
private theorem counterexamplePrincipalBranch_sq (k : ℕ) (u : ℂ) :
    (Complex.cpow u ((k : ℂ) / 2)) ^ 2 = u ^ k := by
  change (u ^ ((k : ℂ) / 2)) ^ (2 : ℕ) = u ^ k
  rw [← Complex.cpow_mul_nat, ← Complex.cpow_natCast]
  congr 1
  push_cast
  ring


-- @@ L3401-3409 verbatim
private theorem counterexampleAlternateBranch_sq (k : ℕ) (u : ℂ) :
    ((Complex.I ^ k) * Complex.cpow (-u) ((k : ℂ) / 2)) ^ 2 = u ^ k := by
  rw [mul_pow, counterexamplePrincipalBranch_sq, ← pow_mul]
  conv_lhs => lhs; rw [show k * 2 = 2 * k by omega]
  rw [pow_mul, Complex.I_sq, neg_pow u k]
  have hsign : (-1 : ℂ) ^ k * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]
    simp
  rw [← mul_assoc, hsign, one_mul]


-- @@ L3411-3418 verbatim
private theorem cpow_half_nat_eq_or_eq_neg_alt (k : ℕ) (u : ℂ) :
    Complex.cpow u ((k : ℂ) / 2) =
        (Complex.I ^ k) * Complex.cpow (-u) ((k : ℂ) / 2) ∨
      Complex.cpow u ((k : ℂ) / 2) =
        -((Complex.I ^ k) * Complex.cpow (-u) ((k : ℂ) / 2)) := by
  apply eq_or_eq_neg_of_sq_eq_sq
  exact (counterexamplePrincipalBranch_sq k u).trans
    (counterexampleAlternateBranch_sq k u).symm


-- @@ L3420-3469 verbatim
private theorem hasFDerivAt_counterexamplePrincipalBranch (k : ℕ) {z : ℂ} (hz : z ≠ 0)
    (hslit : 100 / star z ∈ Complex.slitPlane) :
    HasFDerivAt (fun y : ℂ ↦ Complex.cpow (100 / star y) ((k : ℂ) / 2))
      ((-((k : ℂ) / 2) * Complex.cpow (100 / star z) ((k : ℂ) / 2) / star z) •
        (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z := by
  have hstar : HasFDerivAt (fun y : ℂ ↦ star y)
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) z := by
    rw [show (fun y : ℂ ↦ star y) = (Complex.conjCLE : ℂ → ℂ) by funext y; rfl]
    exact Complex.conjCLE.hasFDerivAt
  have hstar0 : star z ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hz
  have hinvComplex : HasDerivAt (fun u : ℂ ↦ 100 / u) (-100 / (star z) ^ 2) (star z) := by
    convert (hasDerivAt_const (star z) 100).div (hasDerivAt_id (star z)) hstar0 using 1
    all_goals first
      | with_reducible_and_instances rfl
      | funext u
        rfl
      | simp only [Pi.div_apply, id_eq, zero_mul]
        field_simp
        ring
  have hinv : HasFDerivAt (fun y : ℂ ↦ 100 / star y)
      ((-100 / (star z) ^ 2) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z := by
    convert hinvComplex.comp_hasFDerivAt z hstar using 1
    all_goals first | with_reducible_and_instances rfl | simp [Function.comp_def]
  have hpowerComplex :=
    (hasDerivAt_id (100 / star z)).cpow_const (c := (k : ℂ) / 2) hslit
  let D : ℂ →L[ℝ] ℂ :=
    ((((k : ℂ) / 2) * (100 / star z) ^ ((k : ℂ) / 2 - 1)) *
      (-100 / (star z) ^ 2)) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)
  have hpower : HasFDerivAt
      (fun y : ℂ ↦ Complex.cpow (100 / star y) ((k : ℂ) / 2)) D z := by
    convert hpowerComplex.comp_hasFDerivAt z hinv using 1
    all_goals first
      | with_reducible_and_instances rfl
      | funext y
        rfl
      | simp only [D, Function.comp_apply, id_eq, mul_one, smul_smul]
  apply hpower.congr_fderiv
  ext v
  have hu0 : 100 / star z ≠ 0 := div_ne_zero (by norm_num) hstar0
  dsimp only [D]
  have hcpow : Complex.cpow (100 / star z) ((k : ℂ) / 2 - 1) =
      Complex.cpow (100 / star z) ((k : ℂ) / 2) /
        Complex.cpow (100 / star z) 1 := Complex.cpow_sub _ _ hu0
  change (((((k : ℂ) / 2) * Complex.cpow (100 / star z) ((k : ℂ) / 2 - 1)) *
      (-100 / (star z) ^ 2)) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) v = _
  rw [hcpow]
  simp [Complex.conjCLE_apply]
  field_simp
  ring
  exact Or.inl trivial


-- @@ L3471-3490 verbatim
private theorem hasFDerivAt_counterexamplePrincipalBranch_barDeriv (k : ℕ) {z : ℂ}
    (hz : z ≠ 0) (hslit : 100 / star z ∈ Complex.slitPlane) :
    HasFDerivAt (fun y : ℂ ↦
      -((k : ℂ) / 2) * Complex.cpow (100 / star y) ((k : ℂ) / 2) / star y)
      ((((k : ℂ) / 2) * ((k : ℂ) / 2 + 1) *
        Complex.cpow (100 / star z) ((k : ℂ) / 2) / (star z) ^ 2) •
          (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z := by
  have hstar : HasFDerivAt (fun y : ℂ ↦ star y)
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) z := by
    rw [show (fun y : ℂ ↦ star y) = (Complex.conjCLE : ℂ → ℂ) by funext y; rfl]
    exact Complex.conjCLE.hasFDerivAt
  have hstar0 : star z ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hz
  have hbranch := hasFDerivAt_counterexamplePrincipalBranch k hz hslit
  have hstarInv := (hasFDerivAt_inv' (𝕜 := ℝ) hstar0).comp z hstar
  have h := ((hasFDerivAt_const (-((k : ℂ) / 2)) z).mul hbranch).mul hstarInv
  apply h.congr_fderiv
  ext v
  simp [Complex.conjCLE_apply, div_eq_mul_inv]
  field_simp
  ring


-- @@ L3492-3525 verbatim
private theorem hasFDerivAt_counterexampleAlternateBranch (k : ℕ) {z : ℂ} (hz : z ≠ 0)
    (hslit : -(100 / star z) ∈ Complex.slitPlane) :
    HasFDerivAt (fun y : ℂ ↦
      (Complex.I ^ k) * Complex.cpow (-(100 / star y)) ((k : ℂ) / 2))
      ((-((k : ℂ) / 2) *
        ((Complex.I ^ k) * Complex.cpow (-(100 / star z)) ((k : ℂ) / 2)) / star z) •
          (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z := by
  have hslit' : 100 / star (-z) ∈ Complex.slitPlane := by
    rw [show 100 / star (-z) = -(100 / star z) by simp; ring]
    exact hslit
  have hbase := hasFDerivAt_counterexamplePrincipalBranch k (neg_ne_zero.mpr hz) hslit'
  have hneg := hbase.comp z (hasFDerivAt_id z).neg
  have hbase_eq (y : ℂ) : 100 / star (-y) = -(100 / star y) := by
    simp
    ring
  have hfun : ((fun y : ℂ ↦ Complex.cpow (100 / star y) ((k : ℂ) / 2)) ∘ Neg.neg) =
      fun y : ℂ ↦ Complex.cpow (-(100 / star y)) ((k : ℂ) / 2) := by
    funext y
    exact congrArg (fun u : ℂ ↦ Complex.cpow u ((k : ℂ) / 2)) (hbase_eq y)
  have hneg' := hneg.congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun y ↦ (congrFun hfun y).symm)
  have hraw := (hasFDerivAt_const (Complex.I ^ k) z).mul hneg'
  have hmulfun :
      ((fun _ : ℂ ↦ Complex.I ^ k) *
        fun y : ℂ ↦ Complex.cpow (-(100 / star y)) ((k : ℂ) / 2)) =
      fun y : ℂ ↦ (Complex.I ^ k) *
        Complex.cpow (-(100 / star y)) ((k : ℂ) / 2) := by
    funext y
    rfl
  rw [hmulfun] at hraw
  apply hraw.congr_fderiv
  ext v
  simp [Complex.conjCLE_apply]
  ring


-- @@ L3527-3546 verbatim
private theorem hasFDerivAt_counterexampleAlternateBranch_barDeriv (k : ℕ) {z : ℂ}
    (hz : z ≠ 0) (hslit : -(100 / star z) ∈ Complex.slitPlane) :
    HasFDerivAt (fun y : ℂ ↦ -((k : ℂ) / 2) *
      ((Complex.I ^ k) * Complex.cpow (-(100 / star y)) ((k : ℂ) / 2)) / star y)
      ((((k : ℂ) / 2) * ((k : ℂ) / 2 + 1) *
        ((Complex.I ^ k) * Complex.cpow (-(100 / star z)) ((k : ℂ) / 2)) /
          (star z) ^ 2) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z := by
  have hstar : HasFDerivAt (fun y : ℂ ↦ star y)
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) z := by
    rw [show (fun y : ℂ ↦ star y) = (Complex.conjCLE : ℂ → ℂ) by funext y; rfl]
    exact Complex.conjCLE.hasFDerivAt
  have hstar0 : star z ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hz
  have hbranch := hasFDerivAt_counterexampleAlternateBranch k hz hslit
  have hstarInv := (hasFDerivAt_inv' (𝕜 := ℝ) hstar0).comp z hstar
  have h := ((hasFDerivAt_const (-((k : ℂ) / 2)) z).mul hbranch).mul hstarInv
  apply h.congr_fderiv
  ext v
  simp [Complex.conjCLE_apply, div_eq_mul_inv]
  field_simp
  ring


-- @@ L3548-3572 verbatim
private theorem hasFDerivAt_radial_mul_seed_branch (W B : ℂ → ℂ) {z : ℂ} (hz : z ≠ 0)
    (hW : HasFDerivAt W ((B z) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z) :
    let G :=
      (counterexampleRadialAmplitude ‖z‖ * counterexampleRadialLogDerivOne ‖z‖ : ℂ) *
          z / ‖z‖ * counterexampleSeed (W z) +
        2 * counterexampleRadialAmplitude ‖z‖ * seedWirtingerModel (W z) * B z
    HasFDerivAt (fun y : ℂ ↦ counterexampleRadialAmplitude ‖y‖ * counterexampleSeed (W y))
      (G.re • Complex.reCLM + G.im • Complex.imCLM) z := by
  dsimp only
  have hA := hasFDerivAt_counterexampleRadialAmplitude_norm hz
  have hseed := (hasFDerivAt_counterexampleSeed (W z)).comp z hW
  have hWre2 : (2 : ℂ) * ((W z).re : ℂ) = ((2 * (W z).re : ℝ) : ℂ) := by
    norm_cast
  have hWim2 : (2 : ℂ) * ((W z).im : ℂ) = ((2 * (W z).im : ℝ) : ℂ) := by
    norm_cast
  have hWim4 : (4 : ℂ) * ((W z).im : ℂ) = ((4 * (W z).im : ℝ) : ℂ) := by
    norm_cast
  apply (hA.mul hseed).congr_fderiv
  ext v
  rw [seedWirtingerModel_eq_gradient]
  simp [seedGradient, Complex.conjCLE_apply, Complex.mul_re, Complex.mul_im]
  rw [hWre2, hWim2, hWim4]
  simp only [Complex.sin_ofReal_re, Complex.sin_ofReal_im,
    Complex.cos_ofReal_re]
  ring


-- @@ L3574-3876 verbatim
private theorem exists_radial_seed_gradient_fderiv (W B : ℂ → ℂ) (C : ℂ) {z : ℂ}
    (hz : z ≠ 0)
    (hW : HasFDerivAt W ((B z) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z)
    (hB : HasFDerivAt B (C • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z) :
    let G := fun y : ℂ ↦
      (counterexampleRadialAmplitude ‖y‖ * counterexampleRadialLogDerivOne ‖y‖ : ℂ) *
          y / ‖y‖ * counterexampleSeed (W y) +
        2 * counterexampleRadialAmplitude ‖y‖ * seedWirtingerModel (W y) * B y
    ∃ G' : ℂ →L[ℝ] ℂ, HasFDerivAt G G' z ∧
      G' 1 + Complex.I * G' Complex.I =
        (counterexampleRadialAmplitude ‖z‖ : ℂ) *
            star (seedTraceFreeHessianModel (W z)) * B z ^ 2 +
          4 * counterexampleRadialAmplitude ‖z‖ * seedWirtingerModel (W z) * C +
          4 * ((counterexampleRadialAmplitude ‖z‖ *
              counterexampleRadialLogDerivOne ‖z‖ : ℝ) * z / ‖z‖) *
            seedWirtingerModel (W z) * B z +
          ((counterexampleRadialAmplitude ‖z‖ *
                (counterexampleRadialLogDerivOne ‖z‖ ^ 2 +
                  counterexampleRadialLogDerivTwo ‖z‖) : ℝ) * z ^ 2 / ‖z‖ ^ 2 -
              (counterexampleRadialAmplitude ‖z‖ *
                counterexampleRadialLogDerivOne ‖z‖ : ℝ) * z ^ 2 / ‖z‖ ^ 3) *
            counterexampleSeed (W z) := by
  dsimp only
  rcases exists_counterexampleRadialGradient_fderiv hz with ⟨R, hR, hRbar⟩
  rcases exists_seedWirtingerModel_fderiv (W z) with ⟨Q, hQ, hQbar⟩
  have hAreal := hasFDerivAt_counterexampleRadialAmplitude_norm hz
  have hA0 := Complex.ofRealCLM.hasFDerivAt.comp z hAreal
  have hseedReal := (hasFDerivAt_counterexampleSeed (W z)).comp z hW
  have hseed0 := Complex.ofRealCLM.hasFDerivAt.comp z hseedReal
  have hq0 := hQ.comp z hW
  let DA : ℂ →L[ℝ] ℂ :=
    fderiv ℝ (fun y : ℂ ↦ (counterexampleRadialAmplitude ‖y‖ : ℂ)) z
  have hA : HasFDerivAt
      (fun y : ℂ ↦ (counterexampleRadialAmplitude ‖y‖ : ℂ)) DA z := by
    apply DifferentiableAt.hasFDerivAt
    convert hA0.differentiableAt using 1
    all_goals first
      | with_reducible_and_instances rfl
      | funext y
        rfl
      | simp [Function.comp_def]
  let Dseed : ℂ →L[ℝ] ℂ :=
    fderiv ℝ (fun y : ℂ ↦ (counterexampleSeed (W y) : ℂ)) z
  have hseed : HasFDerivAt
      (fun y : ℂ ↦ (counterexampleSeed (W y) : ℂ)) Dseed z := by
    apply DifferentiableAt.hasFDerivAt
    convert hseed0.differentiableAt using 1
    all_goals first
      | with_reducible_and_instances rfl
      | funext y
        rfl
      | simp [Function.comp_def]
  let Dq : ℂ →L[ℝ] ℂ := fderiv ℝ (fun y : ℂ ↦ seedWirtingerModel (W y)) z
  have hq : HasFDerivAt (fun y : ℂ ↦ seedWirtingerModel (W y)) Dq z := by
    apply DifferentiableAt.hasFDerivAt
    convert hq0.differentiableAt using 1
    all_goals first
      | with_reducible_and_instances rfl
      | funext y
        rfl
      | simp [Function.comp_def]
  have hone0 := hR.mul hseed
  have htwo0 := (hasFDerivAt_const (2 : ℂ) z).mul ((hA.mul hq).mul hB)
  let Done : ℂ →L[ℝ] ℂ := fderiv ℝ (fun y : ℂ ↦
    ((counterexampleRadialAmplitude ‖y‖ * counterexampleRadialLogDerivOne ‖y‖ : ℂ) *
      y / ‖y‖) * counterexampleSeed (W y)) z
  have hone : HasFDerivAt (fun y : ℂ ↦
      ((counterexampleRadialAmplitude ‖y‖ * counterexampleRadialLogDerivOne ‖y‖ : ℂ) *
        y / ‖y‖) * counterexampleSeed (W y)) Done z := by
    apply DifferentiableAt.hasFDerivAt
    convert hone0.differentiableAt using 1
    all_goals first
      | with_reducible_and_instances rfl
      | funext y
        rfl
      | simp [Pi.mul_apply]
  let Dtwo : ℂ →L[ℝ] ℂ := fderiv ℝ (fun y : ℂ ↦
    2 * counterexampleRadialAmplitude ‖y‖ * seedWirtingerModel (W y) * B y) z
  have htwo : HasFDerivAt (fun y : ℂ ↦
      2 * counterexampleRadialAmplitude ‖y‖ * seedWirtingerModel (W y) * B y)
      Dtwo z := by
    apply DifferentiableAt.hasFDerivAt
    convert htwo0.differentiableAt using 1
    all_goals first
      | with_reducible_and_instances rfl
      | funext y
        simp [Pi.mul_apply, mul_assoc]
      | simp [Pi.mul_apply, mul_assoc]
  have hG0 := hone.add htwo
  let DG : ℂ →L[ℝ] ℂ := Done + Dtwo
  have hG : HasFDerivAt (fun y : ℂ ↦
      (counterexampleRadialAmplitude ‖y‖ * counterexampleRadialLogDerivOne ‖y‖ : ℂ) *
          y / ‖y‖ * counterexampleSeed (W y) +
        2 * counterexampleRadialAmplitude ‖y‖ * seedWirtingerModel (W y) * B y)
      DG z := by
    convert hG0 using 1
    all_goals first
      | with_reducible_and_instances rfl
      | funext y
        rfl
      | simp only [DG, Pi.add_apply, mul_assoc]
  have hAbar : DA 1 + Complex.I * DA Complex.I =
      (counterexampleRadialAmplitude ‖z‖ *
        counterexampleRadialLogDerivOne ‖z‖ : ℂ) * z / ‖z‖ := by
    let DA0 : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp
      ((((counterexampleRadialAmplitude ‖z‖ * counterexampleRadialLogDerivOne ‖z‖) *
            z.re / ‖z‖) • Complex.reCLM) +
        (((counterexampleRadialAmplitude ‖z‖ * counterexampleRadialLogDerivOne ‖z‖) *
            z.im / ‖z‖) • Complex.imCLM))
    have hA0' : HasFDerivAt
        (fun y : ℂ ↦ (counterexampleRadialAmplitude ‖y‖ : ℂ)) DA0 z := by
      convert hA0 using 1
      all_goals first
        | with_reducible_and_instances rfl
        | funext y
          rfl
        | simp only [DA0, Function.comp_apply]
    have hDA : DA = DA0 := hA.unique hA0'
    rw [hDA]
    simp [DA0, Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.imCLM_apply]
    calc
      _ = (counterexampleRadialAmplitude ‖z‖ *
            counterexampleRadialLogDerivOne ‖z‖ : ℂ) *
          ((z.re : ℂ) + (z.im : ℂ) * Complex.I) / ‖z‖ := by ring
      _ = _ := by rw [Complex.re_add_im]
  have hseedbar : Dseed 1 + Complex.I * Dseed Complex.I =
      2 * seedWirtingerModel (W z) * B z := by
    have hcombine (a b x : ℂ) :
        a * (x.re : ℂ) + b * (x.im : ℂ) +
            Complex.I * (a * (x.im : ℂ) + -(b * (x.re : ℂ))) =
          2 * ((a - b * Complex.I) / 2) * x := by
      apply Complex.ext <;>
        simp [Complex.mul_re, Complex.mul_im] <;>
        ring
    let Dseed0 : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp
      ((seedGradient (W z)).comp
        ((B z) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)))
    have hseed0' : HasFDerivAt
        (fun y : ℂ ↦ (counterexampleSeed (W y) : ℂ)) Dseed0 z := by
      convert hseed0 using 1
      all_goals first
        | with_reducible_and_instances rfl
        | funext y
          rfl
        | simp only [Dseed0, Function.comp_apply]
    have hDseed : Dseed = Dseed0 := hseed.unique hseed0'
    rw [hDseed, seedWirtingerModel_eq_gradient]
    simp [Dseed0, seedGradient, Complex.ofRealCLM_apply, Complex.conjCLE_apply,
      Complex.mul_re, Complex.mul_im]
    exact hcombine _ _ _
  have hqbar : Dq 1 + Complex.I * Dq Complex.I =
      B z * star (seedTraceFreeHessianModel (W z)) / 2 := by
    let Dq0 : ℂ →L[ℝ] ℂ := Q.comp
      ((B z) • (Complex.conjCLE : ℂ →L[ℝ] ℂ))
    have hq0' : HasFDerivAt (fun y : ℂ ↦ seedWirtingerModel (W y)) Dq0 z := by
      convert hq0 using 1
      all_goals first
        | with_reducible_and_instances rfl
        | funext y
          rfl
        | simp only [Dq0, Function.comp_apply]
    have hDqone : Dq0 1 = Q (B z) := by
      simp [Dq0, Complex.conjCLE_apply]
    have hDqI : Dq0 Complex.I = Q (-Complex.I * B z) := by
      dsimp only [Dq0]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [show (Complex.conjCLE : ℂ →L[ℝ] ℂ) Complex.I = -Complex.I by
        simp [Complex.conjCLE_apply]]
      congr 1
      ring
    have hDq : Dq = Dq0 := hq.unique hq0'
    rw [hDq]
    rw [hDqone, hDqI]
    exact hQbar (B z)
  have hBbar : (C • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) 1 +
      Complex.I * (C • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) Complex.I = 2 * C := by
    simp [Complex.conjCLE_apply]
    rw [show Complex.I * (C * Complex.I) = -C by
      rw [show Complex.I * (C * Complex.I) = C * Complex.I ^ 2 by ring,
        Complex.I_sq]
      ring]
    ring
  have honebar : Done 1 + Complex.I * Done Complex.I =
      ((counterexampleRadialAmplitude ‖z‖ *
            (counterexampleRadialLogDerivOne ‖z‖ ^ 2 +
              counterexampleRadialLogDerivTwo ‖z‖) : ℝ) * z ^ 2 / ‖z‖ ^ 2 -
          (counterexampleRadialAmplitude ‖z‖ *
            counterexampleRadialLogDerivOne ‖z‖ : ℝ) * z ^ 2 / ‖z‖ ^ 3) *
        counterexampleSeed (W z) +
      2 * ((counterexampleRadialAmplitude ‖z‖ *
          counterexampleRadialLogDerivOne ‖z‖ : ℝ) * z / ‖z‖) *
        seedWirtingerModel (W z) * B z := by
    let Done0 : ℂ →L[ℝ] ℂ := fderiv ℝ
      ((fun y : ℂ ↦
        (counterexampleRadialAmplitude ‖y‖ * counterexampleRadialLogDerivOne ‖y‖ : ℂ) *
          y / ‖y‖) * fun y : ℂ ↦ (counterexampleSeed (W y) : ℂ)) z
    have hone0Raw : HasFDerivAt
        ((fun y : ℂ ↦
          (counterexampleRadialAmplitude ‖y‖ * counterexampleRadialLogDerivOne ‖y‖ : ℂ) *
            y / ‖y‖) * fun y : ℂ ↦ (counterexampleSeed (W y) : ℂ)) Done0 z := by
      exact hone0.differentiableAt.hasFDerivAt
    have honeFun :
        ((fun y : ℂ ↦
          (counterexampleRadialAmplitude ‖y‖ * counterexampleRadialLogDerivOne ‖y‖ : ℂ) *
            y / ‖y‖) * fun y : ℂ ↦ (counterexampleSeed (W y) : ℂ)) =
        fun y : ℂ ↦
          ((counterexampleRadialAmplitude ‖y‖ * counterexampleRadialLogDerivOne ‖y‖ : ℂ) *
            y / ‖y‖) * counterexampleSeed (W y) := by
      rfl
    have hone0' : HasFDerivAt (fun y : ℂ ↦
        ((counterexampleRadialAmplitude ‖y‖ * counterexampleRadialLogDerivOne ‖y‖ : ℂ) *
          y / ‖y‖) * counterexampleSeed (W y)) Done0 z := by
      rw [← honeFun]
      exact hone0Raw
    have hDone : Done = Done0 := hone.unique hone0'
    rw [hDone]
    dsimp only [Done0]
    rw [hone0.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    rw [show
      ((counterexampleRadialAmplitude ‖z‖ * counterexampleRadialLogDerivOne ‖z‖ : ℂ) *
          z / ‖z‖) * Dseed 1 + (counterexampleSeed (W z) : ℂ) * R 1 +
          Complex.I *
            (((counterexampleRadialAmplitude ‖z‖ *
                counterexampleRadialLogDerivOne ‖z‖ : ℂ) * z / ‖z‖) *
                Dseed Complex.I + (counterexampleSeed (W z) : ℂ) * R Complex.I) =
        ((counterexampleRadialAmplitude ‖z‖ *
            counterexampleRadialLogDerivOne ‖z‖ : ℂ) * z / ‖z‖) *
            (Dseed 1 + Complex.I * Dseed Complex.I) +
          (counterexampleSeed (W z) : ℂ) *
            (R 1 + Complex.I * R Complex.I) by ring]
    rw [hRbar, hseedbar]
    simp only [Complex.ofReal_mul, Complex.ofReal_add, Complex.ofReal_pow]
    ring
  have htwobar : Dtwo 1 + Complex.I * Dtwo Complex.I =
      (counterexampleRadialAmplitude ‖z‖ : ℂ) *
          star (seedTraceFreeHessianModel (W z)) * B z ^ 2 +
        4 * counterexampleRadialAmplitude ‖z‖ * seedWirtingerModel (W z) * C +
        2 * ((counterexampleRadialAmplitude ‖z‖ *
            counterexampleRadialLogDerivOne ‖z‖ : ℝ) * z / ‖z‖) *
          seedWirtingerModel (W z) * B z := by
    let Dtwo0 : ℂ →L[ℝ] ℂ := fderiv ℝ
      ((fun _ : ℂ ↦ (2 : ℂ)) *
        (((fun y : ℂ ↦ (counterexampleRadialAmplitude ‖y‖ : ℂ)) *
          fun y : ℂ ↦ seedWirtingerModel (W y)) * B)) z
    have htwo0Raw : HasFDerivAt
        ((fun _ : ℂ ↦ (2 : ℂ)) *
          (((fun y : ℂ ↦ (counterexampleRadialAmplitude ‖y‖ : ℂ)) *
            fun y : ℂ ↦ seedWirtingerModel (W y)) * B)) Dtwo0 z := by
      exact htwo0.differentiableAt.hasFDerivAt
    have htwoFun :
        ((fun _ : ℂ ↦ (2 : ℂ)) *
          (((fun y : ℂ ↦ (counterexampleRadialAmplitude ‖y‖ : ℂ)) *
            fun y : ℂ ↦ seedWirtingerModel (W y)) * B)) =
        fun y : ℂ ↦
          2 * counterexampleRadialAmplitude ‖y‖ * seedWirtingerModel (W y) * B y := by
      funext y
      simp only [Pi.mul_apply]
      ring
    have htwo0' : HasFDerivAt (fun y : ℂ ↦
        2 * counterexampleRadialAmplitude ‖y‖ * seedWirtingerModel (W y) * B y) Dtwo0 z := by
      rw [← htwoFun]
      exact htwo0Raw
    have hDtwo : Dtwo = Dtwo0 := htwo.unique htwo0'
    rw [hDtwo]
    dsimp only [Dtwo0]
    rw [htwo0.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, Pi.mul_apply, ContinuousLinearMap.zero_apply, mul_zero, add_zero]
    have hBbar' : C * (Complex.conjCLE : ℂ →L[ℝ] ℂ) 1 +
        Complex.I * (C * (Complex.conjCLE : ℂ →L[ℝ] ℂ) Complex.I) = 2 * C := by
      simpa only [ContinuousLinearMap.smul_apply, smul_eq_mul] using hBbar
    rw [show
      2 * ((counterexampleRadialAmplitude ‖z‖ : ℂ) * seedWirtingerModel (W z) *
            (C * (Complex.conjCLE : ℂ →L[ℝ] ℂ) 1) +
          B z * ((counterexampleRadialAmplitude ‖z‖ : ℂ) * Dq 1 +
            seedWirtingerModel (W z) * DA 1)) +
        Complex.I *
          (2 * ((counterexampleRadialAmplitude ‖z‖ : ℂ) * seedWirtingerModel (W z) *
              (C * (Complex.conjCLE : ℂ →L[ℝ] ℂ) Complex.I) +
            B z * ((counterexampleRadialAmplitude ‖z‖ : ℂ) * Dq Complex.I +
              seedWirtingerModel (W z) * DA Complex.I))) =
        2 * ((counterexampleRadialAmplitude ‖z‖ : ℂ) * seedWirtingerModel (W z)) *
            (C * (Complex.conjCLE : ℂ →L[ℝ] ℂ) 1 +
              Complex.I * (C * (Complex.conjCLE : ℂ →L[ℝ] ℂ) Complex.I)) +
          2 * B z *
            ((counterexampleRadialAmplitude ‖z‖ : ℂ) *
                (Dq 1 + Complex.I * Dq Complex.I) +
              seedWirtingerModel (W z) * (DA 1 + Complex.I * DA Complex.I)) by ring,
      hBbar', hqbar, hAbar]
    simp only [Complex.ofReal_mul]
    ring
  have hDG : DG = Done + Dtwo := by
    rfl
  refine ⟨DG, hG, ?_⟩
  rw [hDG]
  simp only [ContinuousLinearMap.add_apply]
  rw [show Done 1 + Dtwo 1 + Complex.I * (Done Complex.I + Dtwo Complex.I) =
    (Done 1 + Complex.I * Done Complex.I) +
      (Dtwo 1 + Complex.I * Dtwo Complex.I) by ring,
    honebar, htwobar]
  ring


-- @@ L3878-3928 verbatim
private theorem traceFreeHessian_radial_mul_seed_branch (W B : ℂ → ℂ) (C : ℂ) (D : ℝ)
    {z : ℂ} (hz : z ≠ 0)
    (hW : ∀ᶠ y in 𝓝 z,
      HasFDerivAt W ((B y) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) y)
    (hB : HasFDerivAt B (C • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z) :
    traceFreeHessian
      (fun y : ℂ ↦ counterexampleRadialAmplitude ‖y‖ * counterexampleSeed (W y) + D) z =
        (counterexampleRadialAmplitude ‖z‖ : ℂ) *
            star (seedTraceFreeHessianModel (W z)) * B z ^ 2 +
          4 * counterexampleRadialAmplitude ‖z‖ * seedWirtingerModel (W z) * C +
          4 * ((counterexampleRadialAmplitude ‖z‖ *
              counterexampleRadialLogDerivOne ‖z‖ : ℝ) * z / ‖z‖) *
            seedWirtingerModel (W z) * B z +
          ((counterexampleRadialAmplitude ‖z‖ *
                (counterexampleRadialLogDerivOne ‖z‖ ^ 2 +
                  counterexampleRadialLogDerivTwo ‖z‖) : ℝ) * z ^ 2 / ‖z‖ ^ 2 -
              (counterexampleRadialAmplitude ‖z‖ *
                counterexampleRadialLogDerivOne ‖z‖ : ℝ) * z ^ 2 / ‖z‖ ^ 3) *
            counterexampleSeed (W z) := by
  let G := fun y : ℂ ↦
    (counterexampleRadialAmplitude ‖y‖ * counterexampleRadialLogDerivOne ‖y‖ : ℂ) *
        y / ‖y‖ * counterexampleSeed (W y) +
      2 * counterexampleRadialAmplitude ‖y‖ * seedWirtingerModel (W y) * B y
  have hWz := hW.self_of_nhds
  rcases exists_radial_seed_gradient_fderiv W B C hz hWz hB with ⟨G', hG, hGbar⟩
  have hfirst : ∀ᶠ y in 𝓝 z, HasFDerivAt
      (fun y : ℂ ↦ counterexampleRadialAmplitude ‖y‖ * counterexampleSeed (W y) + D)
      ((G y).re • Complex.reCLM + (G y).im • Complex.imCLM) y := by
    filter_upwards [hW, eventually_ne_nhds hz] with y hWy hy
    simpa [G] using (hasFDerivAt_radial_mul_seed_branch W B hy hWy).add_const D
  have hre := Complex.reCLM.hasFDerivAt.comp z hG
  have him := Complex.imCLM.hasFDerivAt.comp z hG
  have hgradient := (hre.smul_const Complex.reCLM).add (him.smul_const Complex.imCLM)
  have hfirst' : fderiv ℝ
      (fun y : ℂ ↦ counterexampleRadialAmplitude ‖y‖ * counterexampleSeed (W y) + D) =ᶠ[𝓝 z]
      (fun y ↦ (G y).re • Complex.reCLM + (G y).im • Complex.imCLM) :=
    hfirst.mono fun _ hy ↦ hy.fderiv
  have hsymm : (G' Complex.I).re = (G' 1).im := by
    have h := second_derivative_symmetric_of_eventually_of_real hfirst hgradient
      (1 : ℂ) Complex.I
    simpa using h.symm
  rw [traceFreeHessian_eq_second_fderiv,
    (hgradient.congr_of_eventuallyEq hfirst').fderiv]
  simp
  have hcontract :
      ((G' 1).re : ℂ) - ((G' Complex.I).im : ℂ) +
          2 * ((G' 1).im : ℂ) * Complex.I = G' 1 + Complex.I * G' Complex.I := by
    apply Complex.ext <;> simp [hsymm] <;> ring
  rw [hcontract, hGbar]
  push_cast
  simp only [starRingEnd_apply]


-- @@ L3930-3935 verbatim
/-- The dominant part of the trace-free Hessian on the punctured plane. -/
private noncomputable def counterexampleHessianLeading (k : ℕ) (z : ℂ) : ℂ :=
  let r := ‖z‖
  let w := Complex.cpow (100 / star z) ((k : ℂ) / 2)
  (counterexampleRadialAmplitude r : ℂ) * star (seedTraceFreeHessianModel w) *
    (-((k : ℂ) / 2) * w / star z) ^ 2


-- @@ L3937-3952 verbatim
/-- The lower-order part of the trace-free Hessian on a local analytic branch. -/
private noncomputable def counterexampleHessianError (k : ℕ) (z : ℂ) : ℂ :=
  let r := ‖z‖
  let w := Complex.cpow (100 / star z) ((k : ℂ) / 2)
  let wbar := -((k : ℂ) / 2) * w / star z
  let wbarbar := ((k : ℂ) / 2) * ((k : ℂ) / 2 + 1) * w / (star z) ^ 2
  let A := counterexampleRadialAmplitude r
  let L₁ := counterexampleRadialLogDerivOne r
  let L₂ := counterexampleRadialLogDerivTwo r
  let Abar : ℂ := (A * L₁ : ℝ) * z / (2 * r)
  let Abarbar : ℂ :=
    (A * (L₁ ^ 2 + L₂) : ℝ) * z ^ 2 / (4 * r ^ 2) -
      (A * L₁ : ℝ) * z ^ 2 / (4 * r ^ 3)
  4 * A * seedWirtingerModel w * wbarbar +
    8 * Abar * seedWirtingerModel w * wbar +
    4 * Abarbar * counterexampleSeed w


-- @@ L3954-3957 verbatim
private theorem counterexampleRadialAmplitude_pos {r : ℝ} (hr : 0 < r) :
    0 < counterexampleRadialAmplitude r := by
  simp only [counterexampleRadialAmplitude]
  positivity


-- @@ L3959-4144 verbatim
/-- A radial upper bound for the three lower-order Hessian terms. -/
private theorem counterexampleHessianError_raw_bound (k : ℕ) (hk : 0 < k) {z : ℂ}
    (hz : z ≠ 0) (hz1 : ‖z‖ ≤ 1) :
    ‖counterexampleHessianError k z‖ ≤
      counterexampleRadialAmplitude ‖z‖ * (129 / 20) * ((k : ℝ) / 2) *
          (((k : ℝ) / 2) + 1) *
          ‖Complex.cpow (100 / star z) ((k : ℂ) / 2)‖ / ‖z‖ ^ 2 +
        counterexampleRadialAmplitude ‖z‖ * (903 / 20) * ((k : ℝ) / 2) *
          ‖Complex.cpow (100 / star z) ((k : ℂ) / 2)‖ *
          ‖z‖ ^ (-(9 : ℝ) / 4) +
        counterexampleRadialAmplitude ‖z‖ * (8349 / 80) *
          ‖z‖ ^ (-(5 : ℝ) / 2) := by
  let r := ‖z‖
  let p := (k : ℝ) / 2
  let w := Complex.cpow (100 / star z) ((k : ℂ) / 2)
  let A := counterexampleRadialAmplitude r
  let L₁ := counterexampleRadialLogDerivOne r
  let L₂ := counterexampleRadialLogDerivTwo r
  have hr : 0 < r := by simpa only [r] using norm_pos_iff.mpr hz
  have hp : 0 < p := by
    dsimp only [p]
    positivity
  have hA : 0 < A := by exact counterexampleRadialAmplitude_pos hr
  have hL := counterexampleRadialLogDeriv_bounds hr (by simpa only [r] using hz1)
  have hwbar : ‖-((k : ℂ) / 2) * w / star z‖ = p * ‖w‖ / r := by
    have hpCast : ((k : ℂ) / 2) = ((p : ℝ) : ℂ) := by
      dsimp only [p]
      push_cast
      ring
    rw [hpCast]
    simp only [norm_div, norm_mul, norm_neg, norm_star, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hp, show ‖z‖ = r by rfl]
  have hwbarbar :
      ‖((k : ℂ) / 2) * ((k : ℂ) / 2 + 1) * w / (star z) ^ 2‖ =
        p * (p + 1) * ‖w‖ / r ^ 2 := by
    have hpCast : ((k : ℂ) / 2) = ((p : ℝ) : ℂ) := by
      dsimp only [p]
      push_cast
      ring
    rw [hpCast, show ((p : ℂ) + 1) = (((p + 1 : ℝ) : ℂ)) by push_cast; ring]
    simp only [norm_div, norm_mul, norm_pow, norm_star, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hp, abs_of_pos (by positivity : 0 < p + 1),
      show ‖z‖ = r by rfl]
  let Abar : ℂ := (A * L₁ : ℝ) * z / (2 * r)
  let Abarbar : ℂ :=
    (A * (L₁ ^ 2 + L₂) : ℝ) * z ^ 2 / (4 * r ^ 2) -
      (A * L₁ : ℝ) * z ^ 2 / (4 * r ^ 3)
  have hAbar : ‖Abar‖ ≤ A * (7 / 2) * r ^ (-(5 : ℝ) / 4) := by
    have hAbarNorm : ‖Abar‖ = A * |L₁| / 2 := by
      dsimp only [Abar]
      rw [norm_div, norm_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, abs_mul, abs_of_pos hA,
        show ‖z‖ = r by rfl]
      simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      norm_num
      field_simp [hr.ne']
    rw [hAbarNorm]
    calc
      A * |L₁| / 2 ≤ A * (7 * r ^ (-(5 : ℝ) / 4)) / 2 := by
        exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hL.1 hA.le) (by norm_num)
      _ = A * (7 / 2) * r ^ (-(5 : ℝ) / 4) := by ring
  have hpowNineFive : r ^ (-(9 : ℝ) / 4) ≤ r ^ (-(5 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_ge hr (by simpa only [r] using hz1) (by norm_num)
  have hpowSquare : (r ^ (-(5 : ℝ) / 4)) ^ 2 = r ^ (-(5 : ℝ) / 2) := by
    rw [← Real.rpow_mul_natCast hr.le]
    congr 1
    ring
  have hAbarbar : ‖Abarbar‖ ≤ A * (66 / 4) * r ^ (-(5 : ℝ) / 2) := by
    calc
      ‖Abarbar‖ ≤
          ‖(A * (L₁ ^ 2 + L₂) : ℝ) * z ^ 2 / (4 * r ^ 2)‖ +
            ‖(A * L₁ : ℝ) * z ^ 2 / (4 * r ^ 3)‖ := by
        exact norm_sub_le _ _
      _ = A / 4 * (|L₁ ^ 2 + L₂| + |L₁| / r) := by
        rw [norm_div, norm_div, norm_mul, norm_mul, norm_mul, norm_mul,
          Complex.norm_real, Complex.norm_real, norm_pow, norm_pow,
          Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_pos hA, show ‖z‖ = r by rfl]
        simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
        norm_num
        field_simp [hr.ne']
        rw [abs_of_pos hr]
        ring
      _ ≤ A / 4 *
          ((7 * r ^ (-(5 : ℝ) / 4)) ^ 2 +
            10 * r ^ (-(9 : ℝ) / 4) +
            7 * r ^ (-(5 : ℝ) / 4) / r) := by
        gcongr
        · exact (abs_add_le _ _).trans <| add_le_add
            (by simpa only [abs_pow] using pow_le_pow_left₀ (abs_nonneg L₁) hL.1 2)
            hL.2
        · exact hL.1
      _ ≤ A * (66 / 4) * r ^ (-(5 : ℝ) / 2) := by
        have hdiv : r ^ (-(5 : ℝ) / 4) / r = r ^ (-(9 : ℝ) / 4) := by
          have h := Real.rpow_sub hr (-(5 : ℝ) / 4) 1
          rw [Real.rpow_one] at h
          rw [← h]
          congr 1
          ring
        rw [mul_pow, hpowSquare]
        have hsum : 7 ^ 2 * r ^ (-(5 : ℝ) / 2) +
            10 * r ^ (-(9 : ℝ) / 4) + 7 * r ^ (-(9 : ℝ) / 4) ≤
            66 * r ^ (-(5 : ℝ) / 2) := by
          nlinarith only [hpowNineFive]
        calc
          A / 4 * (7 ^ 2 * r ^ (-(5 : ℝ) / 2) +
              10 * r ^ (-(9 : ℝ) / 4) + 7 * r ^ (-(5 : ℝ) / 4) / r) =
              A / 4 * (7 ^ 2 * r ^ (-(5 : ℝ) / 2) +
                10 * r ^ (-(9 : ℝ) / 4) + 7 * (r ^ (-(5 : ℝ) / 4) / r)) := by
            ring
          _ = A / 4 * (7 ^ 2 * r ^ (-(5 : ℝ) / 2) +
              10 * r ^ (-(9 : ℝ) / 4) + 7 * r ^ (-(9 : ℝ) / 4)) := by rw [hdiv]
          _ ≤ A / 4 * (66 * r ^ (-(5 : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hsum (by positivity)
          _ = _ := by ring
  have htermOne :
      ‖4 * A * seedWirtingerModel w *
          (((k : ℂ) / 2) * ((k : ℂ) / 2 + 1) * w / (star z) ^ 2)‖ ≤
        A * (129 / 20) * p * (p + 1) * ‖w‖ / r ^ 2 := by
    rw [norm_mul, norm_mul, norm_mul, hwbarbar]
    norm_num [abs_of_pos hA]
    calc
      4 * A * ‖seedWirtingerModel w‖ * (p * (p + 1) * ‖w‖ / r ^ 2) ≤
          4 * A * (129 / 80) * (p * (p + 1) * ‖w‖ / r ^ 2) := by
        gcongr
        exact norm_seedWirtingerModel_le w
      _ = _ := by ring
  have htermTwo :
      ‖8 * Abar * seedWirtingerModel w * (-((k : ℂ) / 2) * w / star z)‖ ≤
        A * (903 / 20) * p * ‖w‖ * r ^ (-(9 : ℝ) / 4) := by
    rw [norm_mul, norm_mul, norm_mul, hwbar]
    norm_num
    calc
      8 * ‖Abar‖ * ‖seedWirtingerModel w‖ * (p * ‖w‖ / r) ≤
          8 * (A * (7 / 2) * r ^ (-(5 : ℝ) / 4)) * (129 / 80) *
            (p * ‖w‖ / r) := by gcongr; exact norm_seedWirtingerModel_le w
      _ = A * (903 / 20) * p * ‖w‖ * r ^ (-(9 / 4 : ℝ)) := by
        have hdiv : r ^ (-(5 : ℝ) / 4) / r = r ^ (-(9 : ℝ) / 4) := by
          have h := Real.rpow_sub hr (-(5 : ℝ) / 4) 1
          rw [Real.rpow_one] at h
          rw [← h]
          congr 1
          ring
        have hExp : r ^ (-(9 : ℝ) / 4) = r ^ (-(9 / 4 : ℝ)) := by
          congr 1
          ring
        have hdiv' : r ^ (-(5 : ℝ) / 4) / r = r ^ (-(9 / 4 : ℝ)) :=
          hdiv.trans hExp
        calc
          8 * (A * (7 / 2) * r ^ (-(5 : ℝ) / 4)) * (129 / 80) *
              (p * ‖w‖ / r) =
              A * (903 / 20) * p * ‖w‖ *
                (r ^ (-(5 : ℝ) / 4) / r) := by ring
          _ = A * (903 / 20) * p * ‖w‖ * r ^ (-(9 / 4 : ℝ)) :=
            congrArg (fun x : ℝ ↦ A * (903 / 20) * p * ‖w‖ * x) hdiv'
  have htermThree : ‖4 * Abarbar * counterexampleSeed w‖ ≤
      A * (8349 / 80) * r ^ (-(5 : ℝ) / 2) := by
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    norm_num
    calc
      4 * ‖Abarbar‖ * |counterexampleSeed w| ≤
          4 * (A * (66 / 4) * r ^ (-(5 : ℝ) / 2)) * (253 / 160) := by
        gcongr
        exact counterexampleSeed_abs_le w
      _ = _ := by ring
  simp only [counterexampleHessianError]
  dsimp only [r, p, w, A, L₁, L₂, Abar, Abarbar] at *
  calc
    ‖4 * counterexampleRadialAmplitude ‖z‖ *
          seedWirtingerModel (Complex.cpow (100 / star z) ((k : ℂ) / 2)) *
          (((k : ℂ) / 2) * ((k : ℂ) / 2 + 1) *
            Complex.cpow (100 / star z) ((k : ℂ) / 2) / (star z) ^ 2) +
        8 * ((counterexampleRadialAmplitude ‖z‖ *
              counterexampleRadialLogDerivOne ‖z‖ : ℝ) * z / (2 * ‖z‖)) *
          seedWirtingerModel (Complex.cpow (100 / star z) ((k : ℂ) / 2)) *
          (-((k : ℂ) / 2) * Complex.cpow (100 / star z) ((k : ℂ) / 2) / star z) +
        4 * ((counterexampleRadialAmplitude ‖z‖ *
              (counterexampleRadialLogDerivOne ‖z‖ ^ 2 +
                counterexampleRadialLogDerivTwo ‖z‖) : ℝ) * z ^ 2 /
              (4 * ‖z‖ ^ 2) -
            (counterexampleRadialAmplitude ‖z‖ *
              counterexampleRadialLogDerivOne ‖z‖ : ℝ) * z ^ 2 /
              (4 * ‖z‖ ^ 3)) *
          counterexampleSeed (Complex.cpow (100 / star z) ((k : ℂ) / 2))‖ ≤
        _ := (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add htermOne htermTwo) htermThree


-- @@ L4146-4152 verbatim
private theorem counterexampleBranch_norm (k : ℕ) (z : ℂ) :
    ‖Complex.cpow (100 / star z) ((k : ℂ) / 2)‖ =
      (100 / ‖z‖) ^ ((k : ℝ) / 2) := by
  rw [Complex.cpow_eq_pow,
    show ((k : ℂ) / 2) = (((k : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_real, norm_div, norm_star]
  norm_num


-- @@ L4154-4174 verbatim
private theorem counterexampleHessianLeading_lower_bound (k : ℕ) (hk : 0 < k) {z : ℂ}
    (hz : z ≠ 0) :
    counterexampleRadialAmplitude ‖z‖ * (7 / 50) *
        (((k : ℝ) / 2) ^ 2 *
          ‖Complex.cpow (100 / star z) ((k : ℂ) / 2)‖ ^ 2 / ‖z‖ ^ 2) ≤
      ‖counterexampleHessianLeading k z‖ := by
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hA := counterexampleRadialAmplitude_pos (norm_pos_iff.mpr hz)
  have hsquare :
      ((k : ℝ) / 2) ^ 2 *
          ‖Complex.cpow (100 / star z) ((k : ℂ) / 2)‖ ^ 2 / ‖z‖ ^ 2 =
        (((k : ℝ) / 2) *
          ‖Complex.cpow (100 / star z) ((k : ℂ) / 2)‖ / ‖z‖) ^ 2 := by
    ring
  rw [hsquare]
  simp only [counterexampleHessianLeading, norm_mul, norm_star, norm_pow, norm_neg,
    norm_div, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs]
  norm_num [abs_of_nonneg hk0]
  rw [abs_of_pos hA]
  gcongr
  exact seven_div_fifty_le_norm_seedTraceFreeHessianModel _


-- @@ L4176-4186 verbatim
private theorem counterexampleHessianLeading_ne_zero (k : ℕ) (hk : 0 < k) {z : ℂ}
    (hz : z ≠ 0) : counterexampleHessianLeading k z ≠ 0 := by
  rw [← norm_pos_iff]
  have hW : Complex.cpow (100 / star z) ((k : ℂ) / 2) ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr <| Or.inl <|
      div_ne_zero (by norm_num) ((map_ne_zero (starRingEnd ℂ)).mpr hz)
  have hlower := counterexampleHessianLeading_lower_bound k hk hz
  refine lt_of_lt_of_le ?_ hlower
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hA := counterexampleRadialAmplitude_pos (norm_pos_iff.mpr hz)
  positivity


-- @@ L4188-4343 verbatim
/-- The three error terms are bounded by the leading term times a sum of positive powers of
the radius. -/
private theorem counterexampleHessianError_le_leading_mul_ratio (k : ℕ) (hk : 0 < k)
    {z : ℂ} (hz : z ≠ 0) (hz_one : ‖z‖ ≤ 1) :
    ‖counterexampleHessianError k z‖ ≤ ‖counterexampleHessianLeading k z‖ *
      (140 * ‖z‖ ^ ((k : ℝ) / 2) +
        645 * ‖z‖ ^ ((k : ℝ) / 2 - 1 / 4) +
        3000 * ‖z‖ ^ ((k : ℝ) - 1 / 2)) := by
  let r := ‖z‖
  let p := (k : ℝ) / 2
  let W := ‖Complex.cpow (100 / star z) ((k : ℂ) / 2)‖
  let A := counterexampleRadialAmplitude r
  let D := A * (7 / 50) * (p ^ 2 * W ^ 2 / r ^ 2)
  have hr : 0 < r := by simpa only [r] using norm_pos_iff.mpr hz
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : (1 : ℝ) / 2 ≤ p := by
    dsimp only [p]
    linarith
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hA : 0 < A := counterexampleRadialAmplitude_pos hr
  have hW : 0 < W := by
    dsimp only [W]
    rw [norm_pos_iff]
    exact Complex.cpow_ne_zero_iff.mpr <| Or.inl <|
      div_ne_zero (by norm_num) ((map_ne_zero (starRingEnd ℂ)).mpr hz)
  have hscale : 1 ≤ r ^ p * W := by
    calc
      1 ≤ (100 : ℝ) ^ p := Real.one_le_rpow (by norm_num) hp0.le
      _ = r ^ p * (100 / r) ^ p := by
        rw [Real.div_rpow (by norm_num) hr.le]
        field_simp [(Real.rpow_pos_of_pos hr p).ne']
      _ = r ^ p * W := by
        dsimp only [W, r, p]
        rw [counterexampleBranch_norm]
  have hraw : ‖counterexampleHessianError k z‖ ≤
      A * (129 / 20) * p * (p + 1) * W / r ^ 2 +
        A * (903 / 20) * p * W * r ^ (-(9 : ℝ) / 4) +
        A * (8349 / 80) * r ^ (-(5 : ℝ) / 2) := by
    simpa only [A, W, p, r] using counterexampleHessianError_raw_bound k hk hz hz_one
  have hcoeffOne : (129 / 20) * p * (p + 1) ≤ (98 / 5) * p ^ 2 := by
    nlinarith only [hp]
  have hcoeffTwo : (903 / 20) * p ≤ (903 / 10) * p ^ 2 := by
    nlinarith only [hp]
  have hcoeffThree : (8349 / 80) ≤ 420 * p ^ 2 := by
    nlinarith only [hp, sq_nonneg (p - 1 / 2)]
  have hpowTwo : r ^ (p - 1 / 4) / r ^ 2 =
      r ^ p * r ^ (-(9 : ℝ) / 4) := by
    calc
      r ^ (p - 1 / 4) / r ^ 2 = r ^ (p - 1 / 4) / r ^ (2 : ℝ) :=
        congrArg (fun x : ℝ ↦ r ^ (p - 1 / 4) / x) (Real.rpow_natCast r 2).symm
      _ = r ^ ((p - 1 / 4) - 2) :=
        (Real.rpow_sub hr _ _).symm
      _ = r ^ (p + (-(9 : ℝ) / 4)) := by congr 1; ring
      _ = r ^ p * r ^ (-(9 : ℝ) / 4) := Real.rpow_add hr _ _
  have hpowThree : r ^ ((k : ℝ) - 1 / 2) / r ^ 2 =
      (r ^ p) ^ 2 * r ^ (-(5 : ℝ) / 2) := by
    calc
      r ^ ((k : ℝ) - 1 / 2) / r ^ 2 =
          r ^ ((k : ℝ) - 1 / 2) / r ^ (2 : ℝ) :=
        congrArg (fun x : ℝ ↦ r ^ ((k : ℝ) - 1 / 2) / x)
          (Real.rpow_natCast r 2).symm
      _ = r ^ (((k : ℝ) - 1 / 2) - 2) := (Real.rpow_sub hr _ _).symm
      _ = r ^ (p + p + (-(5 : ℝ) / 2)) := by
        congr 1
        dsimp only [p]
        ring
      _ = (r ^ p) ^ 2 * r ^ (-(5 : ℝ) / 2) := by
        rw [Real.rpow_add hr, Real.rpow_add hr]
        ring
  have htermOne : A * (129 / 20) * p * (p + 1) * W / r ^ 2 ≤
      D * (140 * r ^ p) := by
    have hbase : 0 ≤ A * (98 / 5) * p ^ 2 * W / r ^ 2 := by positivity
    calc
      A * (129 / 20) * p * (p + 1) * W / r ^ 2 ≤
          A * (98 / 5) * p ^ 2 * W / r ^ 2 := by
        calc
          _ = (A * W / r ^ 2) * ((129 / 20) * p * (p + 1)) := by ring
          _ ≤ (A * W / r ^ 2) * ((98 / 5) * p ^ 2) :=
            mul_le_mul_of_nonneg_left hcoeffOne (by positivity)
          _ = _ := by ring
      _ ≤ (A * (98 / 5) * p ^ 2 * W / r ^ 2) * (r ^ p * W) :=
        le_mul_of_one_le_right hbase hscale
      _ = D * (140 * r ^ p) := by
        dsimp only [D]
        ring
  have htargetTwo : D * (645 * r ^ (p - 1 / 4)) =
      (A * (903 / 10) * p ^ 2 * W * r ^ (-(9 : ℝ) / 4)) * (r ^ p * W) := by
    dsimp only [D]
    calc
      (A * (7 / 50) * (p ^ 2 * W ^ 2 / r ^ 2)) *
            (645 * r ^ (p - 1 / 4)) =
          A * (903 / 10) * p ^ 2 * W ^ 2 *
            (r ^ (p - 1 / 4) / r ^ 2) := by ring
      _ = _ := by rw [hpowTwo]; ring
  have htermTwo : A * (903 / 20) * p * W * r ^ (-(9 : ℝ) / 4) ≤
      D * (645 * r ^ (p - 1 / 4)) := by
    have hbase : 0 ≤ A * (903 / 10) * p ^ 2 * W * r ^ (-(9 : ℝ) / 4) := by
      positivity
    calc
      A * (903 / 20) * p * W * r ^ (-(9 : ℝ) / 4) ≤
          A * (903 / 10) * p ^ 2 * W * r ^ (-(9 : ℝ) / 4) := by
        calc
          _ = (A * W * r ^ (-(9 : ℝ) / 4)) * ((903 / 20) * p) := by ring
          _ ≤ (A * W * r ^ (-(9 : ℝ) / 4)) * ((903 / 10) * p ^ 2) :=
            mul_le_mul_of_nonneg_left hcoeffTwo (by positivity)
          _ = _ := by ring
      _ ≤ (A * (903 / 10) * p ^ 2 * W * r ^ (-(9 : ℝ) / 4)) *
          (r ^ p * W) := le_mul_of_one_le_right hbase hscale
      _ = D * (645 * r ^ (p - 1 / 4)) := htargetTwo.symm
  have hscaleSquare : 1 ≤ (r ^ p * W) ^ 2 := by nlinarith only [hscale]
  have htargetThree : D * (3000 * r ^ ((k : ℝ) - 1 / 2)) =
      (A * 420 * p ^ 2 * r ^ (-(5 : ℝ) / 2)) * (r ^ p * W) ^ 2 := by
    dsimp only [D]
    calc
      (A * (7 / 50) * (p ^ 2 * W ^ 2 / r ^ 2)) *
            (3000 * r ^ ((k : ℝ) - 1 / 2)) =
          A * 420 * p ^ 2 * W ^ 2 *
            (r ^ ((k : ℝ) - 1 / 2) / r ^ 2) := by ring
      _ = _ := by rw [hpowThree]; ring
  have htermThree : A * (8349 / 80) * r ^ (-(5 : ℝ) / 2) ≤
      D * (3000 * r ^ ((k : ℝ) - 1 / 2)) := by
    have hbase : 0 ≤ A * 420 * p ^ 2 * r ^ (-(5 : ℝ) / 2) := by positivity
    calc
      A * (8349 / 80) * r ^ (-(5 : ℝ) / 2) ≤
          A * 420 * p ^ 2 * r ^ (-(5 : ℝ) / 2) := by
        calc
          _ = (A * r ^ (-(5 : ℝ) / 2)) * (8349 / 80) := by ring
          _ ≤ (A * r ^ (-(5 : ℝ) / 2)) * (420 * p ^ 2) :=
            mul_le_mul_of_nonneg_left hcoeffThree (by positivity)
          _ = _ := by ring
      _ ≤ (A * 420 * p ^ 2 * r ^ (-(5 : ℝ) / 2)) * (r ^ p * W) ^ 2 :=
        le_mul_of_one_le_right hbase hscaleSquare
      _ = D * (3000 * r ^ ((k : ℝ) - 1 / 2)) := htargetThree.symm
  have hratioNonneg : 0 ≤
      140 * r ^ p + 645 * r ^ (p - 1 / 4) +
        3000 * r ^ ((k : ℝ) - 1 / 2) := by positivity
  have hlower : D ≤ ‖counterexampleHessianLeading k z‖ := by
    simpa only [D, A, W, p, r] using counterexampleHessianLeading_lower_bound k hk hz
  calc
    ‖counterexampleHessianError k z‖ ≤
        A * (129 / 20) * p * (p + 1) * W / r ^ 2 +
          A * (903 / 20) * p * W * r ^ (-(9 : ℝ) / 4) +
          A * (8349 / 80) * r ^ (-(5 : ℝ) / 2) := hraw
    _ ≤ D * (140 * r ^ p) + D * (645 * r ^ (p - 1 / 4)) +
        D * (3000 * r ^ ((k : ℝ) - 1 / 2)) :=
      add_le_add (add_le_add htermOne htermTwo) htermThree
    _ = D * (140 * r ^ p + 645 * r ^ (p - 1 / 4) +
        3000 * r ^ ((k : ℝ) - 1 / 2)) := by ring
    _ ≤ ‖counterexampleHessianLeading k z‖ *
        (140 * r ^ p + 645 * r ^ (p - 1 / 4) +
          3000 * r ^ ((k : ℝ) - 1 / 2)) :=
      mul_le_mul_of_nonneg_right hlower hratioNonneg
    _ = ‖counterexampleHessianLeading k z‖ *
        (140 * ‖z‖ ^ ((k : ℝ) / 2) +
          645 * ‖z‖ ^ ((k : ℝ) / 2 - 1 / 4) +
          3000 * ‖z‖ ^ ((k : ℝ) - 1 / 2)) := by rfl


-- @@ L4345-4376 verbatim
/-- The Hessian error is eventually strictly smaller than the leading term. -/
private theorem counterexampleHessianError_lt_leading_eventually (k : ℕ) (hk : 0 < k) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      ‖counterexampleHessianError k z‖ < ‖counterexampleHessianLeading k z‖ := by
  rcases counterexample_error_powers_tendsto_zero k hk with
    ⟨hhalf, hquarter, hminus⟩
  have hratio : Tendsto
      (fun z : ℂ ↦ 140 * ‖z‖ ^ ((k : ℝ) / 2) +
        645 * ‖z‖ ^ ((k : ℝ) / 2 - 1 / 4) +
        3000 * ‖z‖ ^ ((k : ℝ) - 1 / 2))
      (𝓝[≠] 0) (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (((hhalf.const_mul (140 : ℝ)).add (hquarter.const_mul (645 : ℝ))).add
        (hminus.const_mul (3000 : ℝ)))
  have hnormAt : ContinuousAt (fun z : ℂ ↦ ‖z‖) 0 := continuous_norm.continuousAt
  have hnorm : Tendsto (fun z : ℂ ↦ ‖z‖) (𝓝[≠] 0) (𝓝 0) := by
    simpa using hnormAt.tendsto.mono_left
      (show 𝓝[≠] (0 : ℂ) ≤ 𝓝 0 from inf_le_left)
  filter_upwards [hratio.eventually_lt_const zero_lt_one,
    hnorm.eventually_lt_const zero_lt_one, self_mem_nhdsWithin] with z hR hz_one hz
  have hz' : z ≠ 0 := by simpa using hz
  have hlead : 0 < ‖counterexampleHessianLeading k z‖ :=
    norm_pos_iff.mpr (counterexampleHessianLeading_ne_zero k hk hz')
  calc
    ‖counterexampleHessianError k z‖ ≤
        ‖counterexampleHessianLeading k z‖ *
          (140 * ‖z‖ ^ ((k : ℝ) / 2) +
            645 * ‖z‖ ^ ((k : ℝ) / 2 - 1 / 4) +
            3000 * ‖z‖ ^ ((k : ℝ) - 1 / 2)) :=
      counterexampleHessianError_le_leading_mul_ratio k hk hz' hz_one.le
    _ < ‖counterexampleHessianLeading k z‖ * 1 := mul_lt_mul_of_pos_left hR hlead
    _ = ‖counterexampleHessianLeading k z‖ := mul_one _


-- @@ L4378-4461 verbatim
/-- On either analytic square-root branch, the trace-free Hessian is the displayed dominant
term plus the three lower-order product-and-chain-rule terms. -/
private theorem counterexample_traceFreeHessian_decomposition (k : ℕ) {z : ℂ} (hz : z ≠ 0) :
    traceFreeHessian (counterexample k) z =
      counterexampleHessianLeading k z + counterexampleHessianError k z := by
  let U : ℂ → ℂ := fun y ↦ 100 / star y
  let W : ℂ → ℂ := fun y ↦ Complex.cpow (U y) ((k : ℂ) / 2)
  let B : ℂ → ℂ := fun y ↦ -((k : ℂ) / 2) * W y / star y
  let C : ℂ := ((k : ℂ) / 2) * ((k : ℂ) / 2 + 1) * W z / (star z) ^ 2
  have hU0 : U z ≠ 0 :=
    div_ne_zero (by norm_num) ((map_ne_zero (starRingEnd ℂ)).mpr hz)
  rcases Complex.mem_slitPlane_or_neg_mem_slitPlane hU0 with hslit | hslit
  · have hUcont : ContinuousAt U z := by
      dsimp [U]
      fun_prop (disch := aesop)
    have hW : ∀ᶠ y in 𝓝 z,
        HasFDerivAt W ((B y) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) y := by
      filter_upwards [hUcont (Complex.isOpen_slitPlane.mem_nhds hslit),
        eventually_ne_nhds hz] with y hyU hy
      simpa [U, W, B] using hasFDerivAt_counterexamplePrincipalBranch k hy hyU
    have hB : HasFDerivAt B (C • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z := by
      simpa [U, W, B, C] using
        hasFDerivAt_counterexamplePrincipalBranch_barDeriv k hz hslit
    have htrace := traceFreeHessian_radial_mul_seed_branch W B C (10 ^ 10) hz hW hB
    have hcounterexample : counterexample k = fun y : ℂ ↦
        counterexampleRadialAmplitude ‖y‖ * counterexampleSeed (W y) + 10 ^ 10 := by
      funext y
      simp [counterexample, counterexampleRadialAmplitude, U, W]
      ring
    rw [hcounterexample, htrace]
    simp only [counterexampleHessianLeading, counterexampleHessianError]
    dsimp only [U, W, B, C]
    field_simp [norm_ne_zero_iff.mpr hz]
    ring
  · let W' : ℂ → ℂ := fun y ↦
      (Complex.I ^ k) * Complex.cpow (-U y) ((k : ℂ) / 2)
    let B' : ℂ → ℂ := fun y ↦ -((k : ℂ) / 2) * W' y / star y
    let C' : ℂ := ((k : ℂ) / 2) * ((k : ℂ) / 2 + 1) * W' z / (star z) ^ 2
    have hUcont : ContinuousAt (fun y ↦ -U y) z := by
      dsimp [U]
      fun_prop (disch := aesop)
    have hW' : ∀ᶠ y in 𝓝 z,
        HasFDerivAt W' ((B' y) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) y := by
      filter_upwards [hUcont (Complex.isOpen_slitPlane.mem_nhds hslit),
        eventually_ne_nhds hz] with y hyU hy
      simpa [U, W', B'] using hasFDerivAt_counterexampleAlternateBranch k hy hyU
    have hB' : HasFDerivAt B' (C' • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z := by
      simpa [U, W', B', C'] using
        hasFDerivAt_counterexampleAlternateBranch_barDeriv k hz hslit
    have htrace := traceFreeHessian_radial_mul_seed_branch W' B' C' (10 ^ 10) hz hW' hB'
    have hcounterexample : counterexample k = fun y : ℂ ↦
        counterexampleRadialAmplitude ‖y‖ * counterexampleSeed (W' y) + 10 ^ 10 := by
      funext y
      simp only [counterexample]
      have hseed : counterexampleSeed (Complex.cpow (U y) ((k : ℂ) / 2)) =
          counterexampleSeed
            ((Complex.I ^ k) * Complex.cpow (-U y) ((k : ℂ) / 2)) := by
        simpa only [← Complex.cpow_eq_pow] using counterexampleSeed_cpow_eq_alt k (U y)
      rw [hseed]
      simp [counterexampleRadialAmplitude, U, W']
      ring
    rw [hcounterexample]
    have hrelation := cpow_half_nat_eq_or_eq_neg_alt k (U z)
    rcases hrelation with hrelation | hrelation
    · have hWvalue : W z = W' z := by simpa [W, W', U] using hrelation
      rw [htrace]
      dsimp only [B', C']
      rw [← hWvalue]
      simp only [counterexampleHessianLeading, counterexampleHessianError]
      dsimp only [U, W, B, C]
      field_simp [norm_ne_zero_iff.mpr hz]
      ring
    · have hWvalue : W' z = -W z := by
        have hneg := congrArg Neg.neg hrelation
        simpa [W, W', U] using hneg.symm
      rw [htrace]
      dsimp only [B', C']
      rw [hWvalue]
      simp only [seedTraceFreeHessianModel_neg, seedWirtingerModel_neg,
        counterexampleSeed_neg]
      simp only [counterexampleHessianLeading, counterexampleHessianError]
      dsimp only [U, W, B, C]
      field_simp [norm_ne_zero_iff.mpr hz]
      ring


-- @@ L4463-4471 verbatim
/-- The trace-free Hessian of a smooth member of the family is continuous. -/
private theorem continuous_traceFreeHessian_counterexample (k : ℕ) (hk : 0 < k) :
    Continuous (traceFreeHessian (counterexample k)) := by
  have hsecond : Continuous
      (iteratedFDeriv ℝ 2 (counterexample k)) :=
    ContDiff.continuous_iteratedFDeriv (n := (⊤ : ℕ∞))
      (WithTop.coe_le_coe.2 le_top) (counterexample_contDiff k hk)
  unfold traceFreeHessian
  fun_prop


-- @@ L4473-4634 verbatim
/-- The principal-branch leading term on a circle admits a continuous representative and an
argument lift. The representative uses the continuous half-power branch
`(100/r)^(k/2) exp(i(k/2)t)`, including when `k` is odd. -/
private theorem exists_continuous_counterexampleHessianLeading_circle
    (k : ℕ) (hk : 0 < k) {r : ℝ} (hr : 0 < r) :
    ∃ L : ℝ → ℂ, Continuous L ∧
      (∀ t, L t = counterexampleHessianLeading k
        ((r : ℂ) * Complex.exp ((t : ℂ) * Complex.I))) ∧
      L (2 * Real.pi) = L 0 ∧
      ∃ θ : ℝ → ℝ, Continuous θ ∧
        (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) = L t / ‖L t‖) ∧
        θ (2 * Real.pi) - θ 0 = 2 * Real.pi * ((2 + k : ℕ) : ℤ) := by
  let p : ℝ := (k : ℝ) / 2
  let a : ℝ := (100 / r) ^ p
  let zcircle : ℝ → ℂ := fun t ↦
    (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)
  let w : ℝ → ℂ := fun t ↦
    (a : ℂ) * Complex.exp (((p * t : ℝ) : ℂ) * Complex.I)
  let S : ℝ := counterexampleRadialAmplitude r * p ^ 2 * a ^ 2 / r ^ 2
  let L : ℝ → ℂ := fun t ↦
    (S : ℂ) *
      Complex.exp (((((2 + k : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) *
      star (seedTraceFreeHessianModel (w t))
  have hp : 0 < p := by
    dsimp only [p]
    positivity
  have ha : 0 < a := by
    dsimp only [a]
    exact Real.rpow_pos_of_pos (by positivity) _
  have hS : 0 < S := by
    dsimp only [S]
    have hA := counterexampleRadialAmplitude_pos hr
    positivity
  have hzNorm (t : ℝ) : ‖zcircle t‖ = r := by
    dsimp only [zcircle]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Complex.norm_exp]
    simp [Complex.mul_re]
  have hzNe (t : ℝ) : zcircle t ≠ 0 := by
    rw [← norm_pos_iff, hzNorm]
    exact hr
  have hstar (t : ℝ) : star (zcircle t) =
      (r : ℂ) * Complex.exp (-((t : ℂ) * Complex.I)) := by
    change (starRingEnd ℂ) ((r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)) = _
    rw [map_mul, ← Complex.exp_conj]
    simp
  have hU (t : ℝ) : 100 / star (zcircle t) =
      ((100 / r : ℝ) : ℂ) * Complex.exp ((t : ℂ) * Complex.I) := by
    rw [hstar, div_eq_mul_inv, mul_inv, Complex.exp_neg, inv_inv]
    push_cast
    field_simp [hr.ne']
  have haSq : a ^ 2 = (100 / r) ^ k := by
    dsimp only [a]
    rw [← Real.rpow_mul_natCast (by positivity : 0 ≤ 100 / r)]
    have hpTwo : p * (2 : ℕ) = (k : ℝ) := by
      dsimp only [p]
      push_cast
      ring
    rw [hpTwo, Real.rpow_natCast]
  have hpCast : ((k : ℂ) / 2) = ((p : ℝ) : ℂ) := by
    dsimp only [p]
    push_cast
    ring
  have hwsq (t : ℝ) : w t ^ 2 =
      Complex.cpow (100 / star (zcircle t)) ((k : ℂ) / 2) ^ 2 := by
    rw [counterexamplePrincipalBranch_sq, hU, mul_pow]
    rw [mul_pow]
    have haSqC : (a : ℂ) ^ 2 = (((100 / r) ^ k : ℝ) : ℂ) := by
      exact_mod_cast haSq
    have hbasePowC : ((100 / r : ℝ) : ℂ) ^ k =
        (((100 / r) ^ k : ℝ) : ℂ) := by norm_cast
    rw [haSqC, hbasePowC, ← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1
    dsimp only [p]
    push_cast
    ring
  have hmodel (t : ℝ) : seedTraceFreeHessianModel (w t) =
      seedTraceFreeHessianModel
        (Complex.cpow (100 / star (zcircle t)) ((k : ℂ) / 2)) := by
    have hbranches : w t = Complex.cpow (100 / star (zcircle t)) ((k : ℂ) / 2) ∨
        w t = -Complex.cpow (100 / star (zcircle t)) ((k : ℂ) / 2) := by
      apply eq_or_eq_neg_of_sq_eq_sq
      exact hwsq t
    rcases hbranches with hbranch | hbranch
    · rw [hbranch]
    · rw [hbranch, seedTraceFreeHessianModel_neg]
  have hphaseFactor (t : ℝ) :
      Complex.exp (((p * t : ℝ) : ℂ) * Complex.I) ^ 2 /
          Complex.exp (-((t : ℂ) * Complex.I)) ^ 2 =
        Complex.exp (((((2 + k : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, div_eq_mul_inv,
      ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    dsimp only [p]
    push_cast
    ring
  have hfactor (t : ℝ) :
      (-((k : ℂ) / 2) *
          Complex.cpow (100 / star (zcircle t)) ((k : ℂ) / 2) /
          star (zcircle t)) ^ 2 =
        ((p ^ 2 * a ^ 2 / r ^ 2 : ℝ) : ℂ) *
          Complex.exp (((((2 + k : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
    calc
      _ = (((k : ℂ) / 2) ^ 2 *
            Complex.cpow (100 / star (zcircle t)) ((k : ℂ) / 2) ^ 2) /
          star (zcircle t) ^ 2 := by ring
      _ = ((p : ℂ) ^ 2 *
            Complex.cpow (100 / star (zcircle t)) ((k : ℂ) / 2) ^ 2) /
          star (zcircle t) ^ 2 := by rw [hpCast]
      _ = ((p : ℂ) ^ 2 * w t ^ 2) / star (zcircle t) ^ 2 := by rw [hwsq]
      _ = ((p ^ 2 * a ^ 2 / r ^ 2 : ℝ) : ℂ) *
          (Complex.exp (((p * t : ℝ) : ℂ) * Complex.I) ^ 2 /
            Complex.exp (-((t : ℂ) * Complex.I)) ^ 2) := by
        dsimp only [w]
        rw [hstar, mul_pow, mul_pow]
        push_cast
        field_simp [hr.ne']
      _ = _ := by rw [hphaseFactor]
  have hLeq (t : ℝ) : L t = counterexampleHessianLeading k (zcircle t) := by
    simp only [counterexampleHessianLeading]
    rw [hzNorm, ← hmodel, hfactor]
    dsimp only [L, S]
    push_cast
    ring
  have hLcont : Continuous L := by
    have hmodelCont : Continuous seedTraceFreeHessianModel := by
      unfold seedTraceFreeHessianModel
      fun_prop
    have hwcont : Continuous w := by
      dsimp only [w]
      fun_prop
    have hphaseCont : Continuous (fun t : ℝ ↦
        Complex.exp (((((2 + k : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I)) := by
      fun_prop
    exact (continuous_const.mul hphaseCont).mul
      (continuous_star.comp (hmodelCont.comp hwcont))
  have hLnorm (t : ℝ) : ‖L t‖ = S * ‖seedTraceFreeHessianModel (w t)‖ := by
    dsimp only [L]
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS,
      Complex.norm_exp, norm_star]
    simp [Complex.mul_re]
  have hzperiod : zcircle (2 * Real.pi) = zcircle 0 := by
    dsimp only [zcircle]
    rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I =
      2 * (Real.pi : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_two_pi_mul_I]
    simp
  have hLperiod : L (2 * Real.pi) = L 0 := by
    rw [hLeq, hLeq, hzperiod]
  rcases exists_seed_leading_argument k a 0 with ⟨θ, hθcont, hθphase, hθchange⟩
  refine ⟨L, hLcont, fun t ↦ by simpa only [zcircle] using hLeq t,
    hLperiod, θ, hθcont, ?_, hθchange⟩
  intro t
  have hphase : Complex.exp ((θ t : ℂ) * Complex.I) =
      Complex.exp (((((2 + k : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) *
        star (seedTraceFreeHessianModel (w t)) /
          ‖seedTraceFreeHessianModel (w t)‖ := by
    simpa [w, p] using hθphase t
  rw [hphase, hLnorm]
  dsimp only [L]
  push_cast
  field_simp [hS.ne']


-- @@ L4636-4640 verbatim
/-- Flatness at the origin makes the trace-free Hessian vanish there. -/
theorem counterexample_traceFreeHessian_zero (k : ℕ) (hk : 0 < k) :
    traceFreeHessian (counterexample k) 0 = 0 := by
  exact traceFreeHessian_eq_zero_of_second_fderiv_eq_zero _ _
    (counterexample_fderiv_fderiv_zero k hk)


-- @@ L4642-4661 verbatim
/-- The leading oscillatory Hessian term dominates on a punctured neighbourhood of the origin. -/
theorem counterexample_traceFreeHessian_isolated (k : ℕ) (hk : 0 < k) :
    ∃ ε > 0, ∀ w, w ≠ 0 → dist w 0 < ε →
      traceFreeHessian (counterexample k) w ≠ 0 := by
  have hdom := counterexampleHessianError_lt_leading_eventually k hk
  have hnonzero : ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      traceFreeHessian (counterexample k) z ≠ 0 := by
    filter_upwards [hdom, self_mem_nhdsWithin] with z hsmall hz
    have hz' : z ≠ 0 := by simpa using hz
    rw [counterexample_traceFreeHessian_decomposition k hz']
    intro hzero
    have heq : counterexampleHessianLeading k z = -counterexampleHessianError k z :=
      eq_neg_of_add_eq_zero_left hzero
    have hnormeq : ‖counterexampleHessianLeading k z‖ =
        ‖counterexampleHessianError k z‖ := by rw [heq, norm_neg]
    exact (ne_of_gt hsmall) hnormeq
  rw [eventually_nhdsWithin_iff] at hnonzero
  rcases Metric.eventually_nhds_iff.mp hnonzero with ⟨ε, hε, hεprop⟩
  refine ⟨ε, hε, fun w hw hdist ↦ ?_⟩
  exact hεprop hdist (by simpa using hw)


-- @@ L4663-4736 verbatim
/-- On an arbitrarily small positively oriented circle, the trace-free Hessian has an argument
lift whose total change is `2π(2+k)`. -/
theorem counterexample_traceFreeHessian_argument (k : ℕ) (hk : 0 < k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ r, 0 < r ∧ r < ε ∧ ∃ θ : ℝ → ℝ, Continuous θ ∧
      (∀ t, Complex.exp ((θ t : ℂ) * Complex.I) =
        traceFreeHessian (counterexample k) (r * Complex.exp ((t : ℂ) * Complex.I)) /
          ‖traceFreeHessian (counterexample k)
            (r * Complex.exp ((t : ℂ) * Complex.I))‖) ∧
      θ (2 * Real.pi) - θ 0 = 2 * Real.pi * ((2 + k : ℕ) : ℤ) := by
  have hdom := counterexampleHessianError_lt_leading_eventually k hk
  rw [eventually_nhdsWithin_iff] at hdom
  rcases Metric.eventually_nhds_iff.mp hdom with ⟨δ, hδ, hδprop⟩
  let r := min (ε / 2) (δ / 2)
  have hr : 0 < r := by
    dsimp only [r]
    exact lt_min (half_pos hε) (half_pos hδ)
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hε)
  have hrδ : r < δ := lt_of_le_of_lt (min_le_right _ _) (half_lt_self hδ)
  let circle : ℝ → ℂ := fun t ↦
    (r : ℂ) * Complex.exp ((t : ℂ) * Complex.I)
  have hcircleNorm (t : ℝ) : ‖circle t‖ = r := by
    dsimp only [circle]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      Complex.norm_exp]
    simp [Complex.mul_re]
  have hcircleNe (t : ℝ) : circle t ≠ 0 := by
    rw [← norm_pos_iff, hcircleNorm]
    exact hr
  have hcircleDist (t : ℝ) : dist (circle t) 0 = r := by
    rw [dist_zero_right, hcircleNorm]
  have hcirclePeriod : circle (2 * Real.pi) = circle 0 := by
    dsimp only [circle]
    rw [show ((2 * Real.pi : ℝ) : ℂ) * Complex.I =
      2 * (Real.pi : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_two_pi_mul_I]
    simp
  rcases exists_continuous_counterexampleHessianLeading_circle k hk hr with
    ⟨L, hLcont, hLeq, hLperiod, θ0, hθ0cont, hθ0phase, hθ0change⟩
  let q : ℝ → ℂ := fun t ↦ traceFreeHessian (counterexample k) (circle t)
  let error : ℝ → ℂ := fun t ↦ q t - L t
  have hcircleCont : Continuous circle := by
    dsimp only [circle]
    fun_prop
  have hqcont : Continuous q :=
    (continuous_traceFreeHessian_counterexample k hk).comp hcircleCont
  have herrorcont : Continuous error := hqcont.sub hLcont
  have herrorEq (t : ℝ) : error t = counterexampleHessianError k (circle t) := by
    dsimp only [error, q]
    rw [counterexample_traceFreeHessian_decomposition k (hcircleNe t), ← hLeq]
    ring
  have hsmall (t : ℝ) : ‖error t‖ < ‖L t‖ := by
    rw [herrorEq, hLeq]
    exact hδprop (by simpa only [hcircleDist] using hrδ) (by simpa using hcircleNe t)
  have hqperiod : q (2 * Real.pi) = q 0 := by
    dsimp only [q]
    rw [hcirclePeriod]
  have herrorperiod : error (2 * Real.pi) = error 0 := by
    dsimp only [error]
    rw [hqperiod, hLperiod]
  have hC : Circle.exp (2 * Real.pi * ((2 + k : ℕ) : ℤ)) = 1 :=
    Circle.exp_two_pi_mul_int ((2 + k : ℕ) : ℤ)
  rcases exists_argument_of_norm_error_lt L error (2 * Real.pi)
      (2 * Real.pi * ((2 + k : ℕ) : ℤ)) hLcont herrorcont hsmall hLperiod
      herrorperiod θ0 hθ0cont hθ0phase hθ0change hC with
    ⟨θ, hθcont, hθphase, hθchange⟩
  refine ⟨r, hr, hrε, θ, hθcont, ?_, hθchange⟩
  intro t
  have hsum : L t + error t = q t := by
    dsimp only [error]
    ring
  have hphase := hθphase t
  rw [hsum] at hphase
  simpa only [q, circle] using hphase


-- @@ L4738-4747 verbatim
/-- For positive `k`, the origin is an isolated umbilic of principal-line index `1 + k / 2`.

`HasIsolatedZeroIndex` stores twice the principal-line index, hence the integer `2 + k` here. -/
theorem counterexample_hasIsolatedZeroIndex (k : ℕ) (hk : 0 < k) :
    HasIsolatedZeroIndex (traceFreeHessian (counterexample k)) 0 (2 + k) := by
  rcases counterexample_traceFreeHessian_isolated k hk with ⟨ε, hε, hisolated⟩
  refine ⟨ε, hε, (continuous_traceFreeHessian_counterexample k hk).continuousOn,
    counterexample_traceFreeHessian_zero k hk, hisolated, ?_⟩
  simpa [NormedSpace.normalize, div_eq_mul_inv, mul_comm] using
    counterexample_traceFreeHessian_argument k hk ε hε


-- @@ L4749-4753 verbatim
/-- Every positive member with `k > 0` violates the index bound in the smooth Loewner
conjecture. -/
theorem counterexample_not_loewner_bound (k : ℕ) (hk : 0 < k) :
    ¬ ((2 + k : ℕ) : ℤ) ≤ 2 := by
  omega


-- @@ L4755-4755 verbatim
end CaratheodoryLoewnerCounterexample


-- @@ L4757-4757 verbatim
end CounterexampleIndexSection


-- @@ L4759-4759 verbatim
/-! ## Flattened from `FormalConjectures/Other/CaratheodoryLoewnerCounterexample/Global.lean` -/


-- @@ L4761-4761 verbatim
section CounterexampleGlobalSection


-- @@ L4763-4771 verbatim
/-!
# The global smooth Carathéodory counterexample

This file extends `counterexample 2` across the sphere and realizes it as the support function of
a smooth strictly convex body with a unique umbilic.

*Reference:*
- [L. Alpöge, X post 2089971359921156203](https://x.com/__alpoge__/status/2089971359921156203)
-/


-- @@ L4773-4773 verbatim
set_option maxHeartbeats 2000000

-- @@ L4774-4774 verbatim
set_option maxRecDepth 4000


-- @@ L4776-4776 verbatim
open scoped ContDiff EuclideanGeometry Manifold

-- @@ L4777-4777 verbatim
open Set Metric


-- @@ L4779-4779 verbatim
namespace CaratheodoryLoewnerCounterexample


-- @@ L4781-4781 verbatim
open CaratheodoryConjecture EuclideanHypersurface LoewnerConjecture


-- @@ L4783-4784 expanded
private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩


-- @@ L4786-4790 expanded
/-- The ambient-codomain manifold derivative used throughout this proof file. -/
private noncomputable def sphereAmbientMfderiv
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    TangentSpace (𝓡 2) p →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
  mvfderiv (𝓡 2) F p


-- @@ L4792-4797 verbatim
private theorem traceFreeHessian_eq_second_fderiv_global (f : ℂ → ℝ) (z : ℂ) :
    traceFreeHessian f z =
      let H := fderiv ℝ (fun w ↦ fderiv ℝ f w) z
      (H 1 1 - H Complex.I Complex.I : ℝ) +
        (2 * H 1 Complex.I : ℝ) * Complex.I := by
  simp [traceFreeHessian, iteratedFDeriv_two_apply]


-- @@ L4799-4803 expanded
/-- The complex coordinate inverse to `counterexampleSphereChart` away from the north pole. -/
private noncomputable def counterexampleSphereCoord (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    ℂ :=
  Complex.orthonormalBasisOneI.repr.symm ((2 : ℝ)⁻¹ • (stereographic' 2 counterexampleNorthPole) p)


-- @@ L4805-4808 verbatim
/-- The chosen complex coordinate is a left inverse to the spherical chart. -/
private theorem counterexampleSphereCoord_chart (z : ℂ) :
    counterexampleSphereCoord (counterexampleSphereChart z) = z := by
  apply Complex.ext <;> simp [counterexampleSphereCoord, counterexampleSphereChart]


-- @@ L4810-4821 expanded
/-- Away from the north pole, the spherical chart is also a left inverse to its chosen complex
coordinate. -/
private theorem counterexampleSphereChart_coord {p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    (hp : p ≠ counterexampleNorthPole) :
    counterexampleSphereChart (counterexampleSphereCoord p) = p :=
  by
  have hp_source : p ∈ (stereographic' 2 counterexampleNorthPole).source := by
    simpa [stereographic'_source] using hp
  rw [counterexampleSphereChart, counterexampleSphereCoord, ←
    (stereographic' 2 counterexampleNorthPole).left_inv hp_source]
  congr 1
  apply Complex.orthonormalBasisOneI.repr.symm.injective
  apply Complex.ext <;> simp


-- @@ L4823-4836 expanded
/-- The inverse complex coordinate is smooth on the complement of its projection pole. -/
private theorem counterexampleSphereCoord_contMDiffOn :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, ℂ) ∞ counterexampleSphereCoord { counterexampleNorthPole }ᶜ :=
  by
  let e := stereographic' 2 counterexampleNorthPole
  have he : e ∈ IsManifold.maximalAtlas (𝓡 2) ∞ (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    IsManifold.subset_maximalAtlas ⟨counterexampleNorthPole, rfl⟩
  have hcoord :
    ContDiff ℝ ∞
      (fun x : EuclideanSpace ℝ (Fin 2) ↦ Complex.orthonormalBasisOneI.repr.symm ((2 : ℝ)⁻¹ • x)) :=
    Complex.orthonormalBasisOneI.repr.symm.contDiff.comp (contDiff_const_smul (𝕜 := ℝ) (2 : ℝ)⁻¹)
  rw [← stereographic'_source (n := 2) counterexampleNorthPole]
  exact hcoord.contMDiff.comp_contMDiffOn (contMDiffOn_of_mem_maximalAtlas he)


-- @@ L4838-4843 expanded
/-- The pointwise extension of `counterexample 2` obtained by assigning its limiting value at the
north pole. Smoothness at that point is the substantive content of the extension theorem. -/
private noncomputable def counterexampleTwoSphereExtension
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : ℝ :=
  if p = counterexampleNorthPole then 10 ^ 10 + 3 / 160
  else counterexample 2 (counterexampleSphereCoord p)


-- @@ L4845-4856 verbatim
/-- The pointwise spherical extension agrees with the announced formula in its finite chart. -/
private theorem counterexampleTwoSphereExtension_chart (z : ℂ) :
    counterexampleTwoSphereExtension (counterexampleSphereChart z) = counterexample 2 z := by
  have hmem : counterexampleSphereChart z ∈
      (stereographic' 2 counterexampleNorthPole).source := by
    simpa [counterexampleSphereChart] using
      (stereographic' 2 counterexampleNorthPole).map_target
        (show 2 • Complex.orthonormalBasisOneI.repr z ∈
          (stereographic' 2 counterexampleNorthPole).target by simp)
  have hne : counterexampleSphereChart z ≠ counterexampleNorthPole := by
    simpa [stereographic'_source] using hmem
  simp [counterexampleTwoSphereExtension, hne, counterexampleSphereCoord_chart]


-- @@ L4858-4868 verbatim
/-- The pointwise extension is smooth away from the north pole. -/
private theorem counterexampleTwoSphereExtension_contMDiffOn :
    ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ counterexampleTwoSphereExtension
      {counterexampleNorthPole}ᶜ := by
  have hcounterexample : ContDiff ℝ ∞ (counterexample 2) :=
    counterexample_contDiff 2 (by omega)
  refine (hcounterexample.contMDiff.comp_contMDiffOn
    counterexampleSphereCoord_contMDiffOn).congr ?_
  intro p hp
  have hpne : p ≠ counterexampleNorthPole := by simpa using hp
  simp [counterexampleTwoSphereExtension, hpne]


-- @@ L4870-4880 verbatim
/-- Smoothness at the north pole is the only missing local condition for smoothness of the
pointwise extension on the whole sphere. -/
private theorem counterexampleTwoSphereExtension_contMDiff_of_contMDiffAt_north
    (hnorth : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ counterexampleTwoSphereExtension
      counterexampleNorthPole) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ counterexampleTwoSphereExtension := by
  intro p
  by_cases hp : p = counterexampleNorthPole
  · simpa [hp] using hnorth
  · exact (counterexampleTwoSphereExtension_contMDiffOn p (by simpa)).contMDiffAt
      (isOpen_compl_singleton.mem_nhds (by simpa))


-- @@ L4882-4886 verbatim
/-- The flat scalar appearing in the reciprocal chart at the north pole. On the nonnegative
half-line this is `(s / 10000) ^ (1 / 8) * exp (-10000 / s)`. -/
private noncomputable def counterexampleTwoReciprocalExponent (s : ℝ) : ℝ :=
  (10000 : ℝ) ^ (-(1 : ℝ) / 8) *
    (s ^ ((1 : ℝ) / 8) * Real.flatRpowExp 1 10000 s)


-- @@ L4888-4892 verbatim
/-- The reciprocal-chart exponent is smooth across `s = 0`. -/
private theorem counterexampleTwoReciprocalExponent_contDiff :
    ContDiff ℝ ∞ counterexampleTwoReciprocalExponent := by
  exact contDiff_const.mul
    (Real.flatRpowExp.rpow_mul_contDiff (by norm_num) (by norm_num) ((1 : ℝ) / 8))


-- @@ L4894-4910 verbatim
/-- On the positive half-line, the smooth flat extension has the reciprocal-chart formula from
the informal calculation. -/
private theorem counterexampleTwoReciprocalExponent_of_pos {s : ℝ} (hs : 0 < s) :
    counterexampleTwoReciprocalExponent s =
      (s / 10000) ^ ((1 : ℝ) / 8) * Real.exp (-10000 / s) := by
  rw [counterexampleTwoReciprocalExponent, Real.flatRpowExp.of_pos 1 10000 hs]
  have hscale :
      (10000 : ℝ) ^ (-(1 : ℝ) / 8) * s ^ ((1 : ℝ) / 8) =
        (s / 10000) ^ ((1 : ℝ) / 8) := by
    rw [show -(1 : ℝ) / 8 = -((1 : ℝ) / 8) by ring,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 10000), Real.div_rpow hs.le
      (by norm_num : (0 : ℝ) ≤ 10000)]
    field_simp
  rw [← mul_assoc, hscale]
  congr 2
  field_simp [hs.ne']
  rw [Real.rpow_neg_one, inv_mul_cancel₀ hs.ne']


-- @@ L4912-4915 verbatim
/-- The positive radial coefficient multiplying the seed in the reciprocal chart. -/
private noncomputable def counterexampleTwoReciprocalDamping (w : ℂ) : ℝ :=
  let s := ‖w‖ ^ 2
  10000 / (s + 10000) * Real.exp (-counterexampleTwoReciprocalExponent s)


-- @@ L4917-4925 verbatim
/-- The reciprocal-chart damping coefficient is smooth on the whole complex plane. -/
private theorem counterexampleTwoReciprocalDamping_contDiff :
    ContDiff ℝ ∞ counterexampleTwoReciprocalDamping := by
  have hs : ContDiff ℝ ∞ (fun w : ℂ ↦ ‖w‖ ^ 2) := contDiff_norm_sq ℝ
  have hdenom : ∀ w : ℂ, ‖w‖ ^ 2 + 10000 ≠ 0 := by
    intro w
    positivity
  exact (contDiff_const.div (hs.add contDiff_const) hdenom).mul
    ((counterexampleTwoReciprocalExponent_contDiff.comp hs).neg.exp)


-- @@ L4927-4934 verbatim
/-- Away from zero, the smooth damping coefficient has the explicit reciprocal-chart formula. -/
private theorem counterexampleTwoReciprocalDamping_of_ne_zero {w : ℂ} (hw : w ≠ 0) :
    counterexampleTwoReciprocalDamping w =
      10000 / (‖w‖ ^ 2 + 10000) *
        Real.exp (-((‖w‖ ^ 2 / 10000) ^ ((1 : ℝ) / 8) *
          Real.exp (-10000 / ‖w‖ ^ 2))) := by
  rw [counterexampleTwoReciprocalDamping,
    counterexampleTwoReciprocalExponent_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hw))]


-- @@ L4936-4938 verbatim
/-- The smooth representative of `counterexample 2` in its reciprocal chart. -/
private noncomputable def counterexampleTwoReciprocal (w : ℂ) : ℝ :=
  10 ^ 10 + counterexampleTwoReciprocalDamping w * counterexampleSeed w


-- @@ L4940-4944 verbatim
/-- The reciprocal representative is smooth, including at its origin. -/
private theorem counterexampleTwoReciprocal_contDiff :
    ContDiff ℝ ∞ counterexampleTwoReciprocal := by
  exact contDiff_const.add
    (counterexampleTwoReciprocalDamping_contDiff.mul counterexampleSeed_contDiff)


-- @@ L4946-4952 verbatim
/-- The reciprocal representative takes the limiting value used in the pointwise spherical
extension at its origin. -/
private theorem counterexampleTwoReciprocal_zero :
    counterexampleTwoReciprocal 0 = 10 ^ 10 + 3 / 160 := by
  simp [counterexampleTwoReciprocal, counterexampleTwoReciprocalDamping,
    counterexampleTwoReciprocalExponent, counterexampleSeed]
  ring


-- @@ L4954-4958 verbatim
/-- The reciprocal-star transformation used between the two complex charts is an involution. -/
private theorem hundred_div_star_involutive (w : ℂ) :
    (100 : ℂ) / star ((100 : ℂ) / star w) = w := by
  rw [star_div₀, star_star]
  norm_num


-- @@ L4960-4995 verbatim
/-- The original finite-chart formula becomes the smooth reciprocal representative under
`z = 100 / star w`. -/
private theorem counterexample_two_reciprocal {w : ℂ} (hw : w ≠ 0) :
    counterexample 2 (100 / star w) = counterexampleTwoReciprocal w := by
  have hnorm : ‖(100 : ℂ) / star w‖ = 100 / ‖w‖ := by
    simp
  have hnorm_pos : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have harg := hundred_div_star_involutive w
  have hrpow :
      (100 / ‖w‖) ^ (-((1 : ℝ) / 4)) =
        (‖w‖ ^ 2 / 10000) ^ ((1 : ℝ) / 8) := by
    calc
      (100 / ‖w‖) ^ (-((1 : ℝ) / 4)) = (‖w‖ / 100) ^ ((1 : ℝ) / 4) := by
        rw [Real.rpow_neg_eq_inv_rpow]
        congr 2
        field_simp
      _ = ((‖w‖ / 100) ^ 2) ^ ((1 : ℝ) / 8) := by
        rw [← Real.rpow_natCast_mul (div_nonneg (norm_nonneg _) (by norm_num)) 2]
        norm_num
      _ = (‖w‖ ^ 2 / 10000) ^ ((1 : ℝ) / 8) := by
        congr 2
        ring
  have hsquare : -(100 / ‖w‖) ^ 2 = -10000 / ‖w‖ ^ 2 := by
    field_simp [hnorm_pos.ne']
    ring
  have hprefactor :
      (100 / ‖w‖) ^ 2 / (1 + (100 / ‖w‖) ^ 2) =
        10000 / (‖w‖ ^ 2 + 10000) := by
    field_simp [hnorm_pos.ne']
    ring
  rw [counterexample, counterexampleTwoReciprocal,
    counterexampleTwoReciprocalDamping_of_ne_zero hw]
  simp only [hnorm, harg]
  norm_num [Complex.cpow_one]
  rw [hrpow, hsquare, ← hprefactor]
  ring


-- @@ L4997-5008 expanded
/-- The real-linear reciprocal coordinate associated to the standard chart at the north pole.
The two orthonormal bases account for the fixed basis choice in mathlib's opposite
stereographic charts. -/
private noncomputable def counterexampleTwoReciprocalLinearCoord (x : EuclideanSpace ℝ (Fin 2)) :
    ℂ :=
  let Upos :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) 2
        (ne_zero_of_mem_unit_sphere counterexampleNorthPole)).repr
  let Uneg :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) 2
        (ne_zero_of_mem_unit_sphere (-counterexampleNorthPole))).repr
  50 •
    Complex.orthonormalBasisOneI.repr.symm
      (Upos
        ((ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ.orthogonalProjection
          (Uneg.symm x : EuclideanSpace ℝ (Fin 3))))


-- @@ L5010-5016 expanded
/-- The fixed isometry from the complex reciprocal coordinate to the tangent plane at the
north pole. -/
private noncomputable def counterexampleTwoTangentEquiv :
    ℂ ≃ₗᵢ[ℝ] (ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ :=
  Complex.orthonormalBasisOneI.repr.trans
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) 2
        (ne_zero_of_mem_unit_sphere counterexampleNorthPole)).repr.symm


-- @@ L5018-5042 expanded
/-- Ambient rational formula for the finite stereographic chart used in the statement. -/
private theorem counterexampleSphereChart_coe (z : ℂ) :
    (counterexampleSphereChart z : EuclideanSpace ℝ (Fin 3)) =
      (‖z‖ ^ 2 + 1)⁻¹ •
        (2 • (counterexampleTwoTangentEquiv z : EuclideanSpace ℝ (Fin 3)) +
          (‖z‖ ^ 2 - 1) • (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))) :=
  by
  rw [counterexampleSphereChart, stereographic'_symm_apply]
  simp only [counterexampleTwoTangentEquiv, LinearIsometryEquiv.trans_apply,
    ← Nat.cast_smul_eq_nsmul ℝ 2, map_smul]
  simp only [Submodule.norm_coe, norm_smul, Real.norm_eq_abs, LinearIsometryEquiv.norm_map]
  have habs : |((2 : ℕ) : ℝ)| = 2 := by norm_num
  rw [habs]
  rw [show (2 * ‖z‖) ^ 2 = 4 * ‖z‖ ^ 2 by ring]
  simp only [Submodule.coe_smul, smul_add, smul_smul]
  have htangent : (4 * ‖z‖ ^ 2 + 4)⁻¹ * 4 * 2 = (‖z‖ ^ 2 + 1)⁻¹ * 2 := by field_simp
  have hpole : (4 * ‖z‖ ^ 2 + 4)⁻¹ * (4 * ‖z‖ ^ 2 - 4) = (‖z‖ ^ 2 + 1)⁻¹ * (‖z‖ ^ 2 - 1) := by
    field_simp
  norm_num only [Nat.cast_ofNat]
  rw [show (4 * ‖z‖ ^ 2 + 4)⁻¹ * 8 = (‖z‖ ^ 2 + 1)⁻¹ * 2 by
      calc
        _ = (4 * ‖z‖ ^ 2 + 4)⁻¹ * 4 * 2 := by ring
        _ = _ := htangent,
    hpole]


-- @@ L5044-5094 expanded
/-- At the south pole the finite chart differential is twice the fixed tangent-plane
isometry. -/
private theorem counterexampleSphereChart_fderiv_zero_apply (v : ℂ) :
    fderiv ℝ (fun z : ℂ ↦ (counterexampleSphereChart z : EuclideanSpace ℝ (Fin 3))) 0 v =
      2 • (counterexampleTwoTangentEquiv v : EuclideanSpace ℝ (Fin 3)) :=
  by
  have heq :
    (fun z : ℂ ↦ (counterexampleSphereChart z : EuclideanSpace ℝ (Fin 3))) = fun z : ℂ ↦
      (‖z‖ ^ 2 + 1)⁻¹ •
        (2 • (counterexampleTwoTangentEquiv z : EuclideanSpace ℝ (Fin 3)) +
          (‖z‖ ^ 2 - 1) • (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))) :=
    by
    funext z
    exact counterexampleSphereChart_coe z
  rw [heq]
  let T : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ.subtypeL.comp
      counterexampleTwoTangentEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hT :
    HasFDerivAt (fun z : ℂ ↦ (counterexampleTwoTangentEquiv z : EuclideanSpace ℝ (Fin 3))) T 0 :=
    T.hasFDerivAt
  have hs : HasFDerivAt (fun z : ℂ ↦ ‖z‖ ^ 2) (0 : ℂ →L[ℝ] ℝ) 0 := by
    simpa using (hasStrictFDerivAt_norm_sq (0 : ℂ)).hasFDerivAt
  have hden : HasFDerivAt (fun z : ℂ ↦ (‖z‖ ^ 2 + 1)⁻¹) (0 : ℂ →L[ℝ] ℝ) 0 := by
    with_reducible_and_instances
      convert
            (hasDerivAt_inv (by norm_num : ‖(0 : ℂ)‖ ^ 2 + (1 : ℝ) ≠ 0)).hasFDerivAt.comp 0
              (hs.add_const 1) using
            1 <;>
          ext x <;>
        simp
  have hlinear :
    HasFDerivAt (fun z : ℂ ↦ 2 • (counterexampleTwoTangentEquiv z : EuclideanSpace ℝ (Fin 3)))
      (T + T) 0 :=
    by
    convert hT.add hT using 1
    all_goals
      first
      | with_reducible_and_instances rfl
      | funext z
        simp only [Pi.add_apply, two_smul]
      | simp only [two_smul]
  have hradial :
    HasFDerivAt (fun z : ℂ ↦ (‖z‖ ^ 2 - 1) • (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))
      (0 : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3)) 0 :=
    by
    with_reducible_and_instances
      convert (hs.sub_const 1).smul_const (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)) using
            1 <;>
          ext x <;>
        simp
  have hnum :
    HasFDerivAt
      (fun z : ℂ ↦
        2 • (counterexampleTwoTangentEquiv z : EuclideanSpace ℝ (Fin 3)) +
          (‖z‖ ^ 2 - 1) • (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))
      (T + T) 0 :=
    by
    convert hlinear.add hradial using 1
    all_goals
      first
      | with_reducible_and_instances rfl
      | simp
  have hprod := hden.smul hnum
  change
    (fderiv ℝ
          (((fun z : ℂ ↦ (‖z‖ ^ 2 + 1)⁻¹) • fun z ↦
            2 • (counterexampleTwoTangentEquiv z : EuclideanSpace ℝ (Fin 3)) +
              (‖z‖ ^ 2 - 1) • (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))))
          0)
        v =
      _
  rw [hprod.fderiv]
  simp [T, two_smul]


-- @@ L5096-5124 expanded
/-- The finite chart differential at the south pole has the whole tangent plane as its range. -/
private theorem range_fderiv_counterexampleSphereChart_zero :
    (fderiv ℝ (fun z : ℂ ↦ (counterexampleSphereChart z : EuclideanSpace ℝ (Fin 3))) 0).range =
      (ℝ ∙ (counterexampleSphereChart 0 : EuclideanSpace ℝ (Fin 3)))ᗮ :=
  by
  rw [counterexampleSphereChart_zero]
  change
    (fderiv ℝ (fun z : ℂ ↦ (counterexampleSphereChart z : EuclideanSpace ℝ (Fin 3))) 0).range =
      (ℝ ∙ (-(counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))))ᗮ
  have hspan :
    ℝ ∙ (-(counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))) =
      ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)) :=
    by
    rw [Submodule.span_singleton_eq_span_singleton]
    exact ⟨(-1 : ℝˣ), by simp⟩
  rw [hspan]
  apply le_antisymm
  · intro y hy
    obtain ⟨v, rfl⟩ := hy
    change fderiv ℝ (fun z : ℂ ↦ (counterexampleSphereChart z : EuclideanSpace ℝ (Fin 3))) 0 v ∈ _
    rw [counterexampleSphereChart_fderiv_zero_apply]
    simpa only [two_nsmul] using
      Submodule.add_mem _ (counterexampleTwoTangentEquiv v).2 (counterexampleTwoTangentEquiv v).2
  · intro y hy
    let v : ℂ := counterexampleTwoTangentEquiv.symm ⟨y, hy⟩
    refine ⟨(2 : ℝ)⁻¹ • v, ?_⟩
    change
      fderiv ℝ (fun z : ℂ ↦ (counterexampleSphereChart z : EuclideanSpace ℝ (Fin 3))) 0
          ((2 : ℝ)⁻¹ • v) =
        y
    rw [counterexampleSphereChart_fderiv_zero_apply]
    simp only [v, map_smul, LinearIsometryEquiv.apply_symm_apply, Submodule.coe_smul]
    change (2 : ℕ) • ((2 : ℝ)⁻¹ • y) = y
    module


-- @@ L5126-5147 expanded
/-- The finite stereographic parametrization is smooth as a map into the sphere. -/
private theorem counterexampleSphereChart_contMDiff :
    ContMDiff 𝓘(ℝ, ℂ) (𝓡 2) ∞ counterexampleSphereChart :=
  by
  apply ContMDiff.codRestrict_sphere
  · have heq :
      (fun z : ℂ ↦ (counterexampleSphereChart z : EuclideanSpace ℝ (Fin 3))) = fun z : ℂ ↦
        (‖z‖ ^ 2 + 1)⁻¹ •
          (2 • (counterexampleTwoTangentEquiv z : EuclideanSpace ℝ (Fin 3)) +
            (‖z‖ ^ 2 - 1) • (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))) :=
      by
      funext z
      exact counterexampleSphereChart_coe z
    exact
      (show ContDiff ℝ ∞ (fun z : ℂ ↦ (counterexampleSphereChart z : EuclideanSpace ℝ (Fin 3)))
          by
          rw [heq]
          have hs : ContDiff ℝ ∞ (fun z : ℂ ↦ ‖z‖ ^ 2) := contDiff_norm_sq ℝ
          have hT :
            ContDiff ℝ ∞
              (fun z : ℂ ↦ (counterexampleTwoTangentEquiv z : EuclideanSpace ℝ (Fin 3))) :=
            ((ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ.subtypeL.contDiff.comp
              counterexampleTwoTangentEquiv.contDiff)
          have hone : ContDiff ℝ ∞ (fun _ : ℂ ↦ (1 : ℝ)) := contDiff_const
          have hnorth :
            ContDiff ℝ ∞ (fun _ : ℂ ↦ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))) :=
            contDiff_const
          exact
            ((hs.add contDiff_const).inv (fun z ↦ by positivity)).smul
              ((hT.const_smul 2).add ((hs.sub hone).smul hnorth))).contMDiff


-- @@ L5149-5161 expanded
/-- The reciprocal complex chart on the sphere. Its origin is the north pole and, away from
the origin, its finite coordinate is `100 / star w`. -/
private noncomputable def counterexampleTwoReciprocalSphereChart (w : ℂ) :
    sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
  let Uneg :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) 2
        (ne_zero_of_mem_unit_sphere (-counterexampleNorthPole))).repr
  let u : (ℝ ∙ (-(counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))))ᗮ :=
    ⟨(50 : ℝ)⁻¹ • (counterexampleTwoTangentEquiv w : EuclideanSpace ℝ (Fin 3)),
      by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
      have htangent :=
        Submodule.mem_orthogonal_singleton_iff_inner_left.mp (counterexampleTwoTangentEquiv w).2
      simp only [real_inner_smul_left, inner_neg_right, htangent, mul_zero, neg_zero]⟩
  (stereographic' 2 (-counterexampleNorthPole)).symm (Uneg u)


-- @@ L5163-5207 expanded
/-- The old north-pole chart coordinate of the reciprocal spherical chart is its defining
complex coordinate. -/
private theorem counterexampleTwoReciprocalLinearCoord_reciprocalSphereChart (w : ℂ) :
    counterexampleTwoReciprocalLinearCoord
        ((stereographic' 2 (-counterexampleNorthPole)) (counterexampleTwoReciprocalSphereChart w)) =
      w :=
  by
  let Upos :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) 2
        (ne_zero_of_mem_unit_sphere counterexampleNorthPole)).repr
  let Uneg :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) 2
        (ne_zero_of_mem_unit_sphere (-counterexampleNorthPole))).repr
  let u : (ℝ ∙ (-(counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))))ᗮ :=
    ⟨(50 : ℝ)⁻¹ • (counterexampleTwoTangentEquiv w : EuclideanSpace ℝ (Fin 3)),
      by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
      have htangent :=
        Submodule.mem_orthogonal_singleton_iff_inner_left.mp (counterexampleTwoTangentEquiv w).2
      simp only [real_inner_smul_left, inner_neg_right, htangent, mul_zero, neg_zero]⟩
  have hu :
    (u : EuclideanSpace ℝ (Fin 3)) ∈ (ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ :=
    by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    have hu' := Submodule.mem_orthogonal_singleton_iff_inner_left.mp u.2
    change
      inner ℝ (u : EuclideanSpace ℝ (Fin 3))
          (-(counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))) =
        0 at hu'
    simpa only [inner_neg_right, neg_eq_zero] using hu'
  rw [counterexampleTwoReciprocalSphereChart]
  change
    counterexampleTwoReciprocalLinearCoord
        ((stereographic' 2 (-counterexampleNorthPole))
          ((stereographic' 2 (-counterexampleNorthPole)).symm (Uneg u))) =
      w
  rw [(stereographic' 2 (-counterexampleNorthPole)).right_inv (by simp)]
  rw [counterexampleTwoReciprocalLinearCoord]
  simp only [u, Uneg, LinearIsometryEquiv.symm_apply_apply]
  change
    50 •
        Complex.orthonormalBasisOneI.repr.symm
          (Upos
            ((ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ.orthogonalProjection
              (u : EuclideanSpace ℝ (Fin 3)))) =
      w
  rw [show
      (ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ.orthogonalProjection
          (u : EuclideanSpace ℝ (Fin 3)) =
        ⟨u, hu⟩
      by
      simpa using
        (ℝ ∙
              (counterexampleNorthPole :
                EuclideanSpace ℝ (Fin 3)))ᗮ |>.orthogonalProjection_mem_subspace_eq_self
          (⟨u, hu⟩ : (ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ)]
  have hu_eq :
    (⟨u, hu⟩ : (ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ) =
      (50 : ℝ)⁻¹ • counterexampleTwoTangentEquiv w :=
    by
    apply Subtype.ext
    rfl
  rw [hu_eq, map_smul]
  simp only [counterexampleTwoTangentEquiv, Upos, LinearIsometryEquiv.trans_apply,
    LinearIsometryEquiv.apply_symm_apply]
  rw [map_smul, LinearIsometryEquiv.symm_apply_apply]
  simp only [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
  norm_num


-- @@ L5209-5223 expanded
/-- The reciprocal coordinate used at the north pole is smooth. -/
private theorem counterexampleTwoReciprocalLinearCoord_contDiff :
    ContDiff ℝ ∞ counterexampleTwoReciprocalLinearCoord :=
  by
  let Upos :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) 2
        (ne_zero_of_mem_unit_sphere counterexampleNorthPole)).repr
  let Uneg :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) 2
        (ne_zero_of_mem_unit_sphere (-counterexampleNorthPole))).repr
  let L : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℂ :=
    (50 • Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.toContinuousLinearMap).comp
      (Upos.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ.orthogonalProjection.comp
          ((ℝ ∙ (-(counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))))ᗮ.subtypeL.comp
            Uneg.symm.toContinuousLinearEquiv.toContinuousLinearMap)))
  change ContDiff ℝ ∞ L
  exact L.contDiff


-- @@ L5225-5250 expanded
/-- The reciprocal linear coordinate is a similarity of ratio `50`. -/
private theorem norm_counterexampleTwoReciprocalLinearCoord (x : EuclideanSpace ℝ (Fin 2)) :
    ‖counterexampleTwoReciprocalLinearCoord x‖ = 50 * ‖x‖ :=
  by
  let Upos :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) 2
        (ne_zero_of_mem_unit_sphere counterexampleNorthPole)).repr
  let Uneg :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) 2
        (ne_zero_of_mem_unit_sphere (-counterexampleNorthPole))).repr
  let u := Uneg.symm x
  have hu :
    (u : EuclideanSpace ℝ (Fin 3)) ∈ (ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ :=
    by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    have hu' := Submodule.mem_orthogonal_singleton_iff_inner_left.mp u.2
    change
      inner ℝ (u : EuclideanSpace ℝ (Fin 3))
          (-(counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))) =
        0 at hu'
    simpa only [inner_neg_right, neg_eq_zero] using hu'
  rw [counterexampleTwoReciprocalLinearCoord]
  change
    ‖50 •
          Complex.orthonormalBasisOneI.repr.symm
            (Upos
              ((ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ.orthogonalProjection
                (u : EuclideanSpace ℝ (Fin 3))))‖ =
      _
  rw [show
      (ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ.orthogonalProjection
          (u : EuclideanSpace ℝ (Fin 3)) =
        ⟨u, hu⟩
      by
      simpa using
        (ℝ ∙
              (counterexampleNorthPole :
                EuclideanSpace ℝ (Fin 3)))ᗮ |>.orthogonalProjection_mem_subspace_eq_self
          (⟨u, hu⟩ : (ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ),
    RCLike.norm_nsmul (K := ℂ), nsmul_eq_mul, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.norm_map]
  change (50 : ℝ) * ‖(u : EuclideanSpace ℝ (Fin 3))‖ = 50 * ‖x‖
  rw [Submodule.norm_coe, Uneg.symm.norm_map]


-- @@ L5252-5264 verbatim
/-- The reciprocal linear coordinate is injective. -/
private theorem counterexampleTwoReciprocalLinearCoord_injective :
    Function.Injective counterexampleTwoReciprocalLinearCoord := by
  intro x y hxy
  have hsub : counterexampleTwoReciprocalLinearCoord (x - y) =
      counterexampleTwoReciprocalLinearCoord x - counterexampleTwoReciprocalLinearCoord y := by
    simp only [counterexampleTwoReciprocalLinearCoord, map_sub, Submodule.coe_sub, smul_sub]
  have hnorm := norm_counterexampleTwoReciprocalLinearCoord (x - y)
  rw [hsub, hxy, sub_self, norm_zero] at hnorm
  have : x - y = 0 := by
    rw [← norm_eq_zero]
    nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.mp this


-- @@ L5266-5282 expanded
/-- Every point except the south pole occurs in the reciprocal chart. -/
private theorem exists_reciprocalSphereChart_of_ne_south
    {p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1} (hp : p ≠ counterexampleSphereChart 0) :
    ∃ w : ℂ, counterexampleTwoReciprocalSphereChart w = p :=
  by
  let e := stereographic' 2 (-counterexampleNorthPole)
  have hpole : p ∈ e.source := by
    dsimp only [e]
    rw [stereographic'_source]
    simpa [counterexampleSphereChart_zero] using hp
  let x := e p
  let w := counterexampleTwoReciprocalLinearCoord x
  have hrho : counterexampleTwoReciprocalSphereChart w ∈ e.source :=
    by
    rw [counterexampleTwoReciprocalSphereChart]
    exact e.map_target (by simp [e])
  refine ⟨w, e.injOn hrho hpole ?_⟩
  apply counterexampleTwoReciprocalLinearCoord_injective
  rw [counterexampleTwoReciprocalLinearCoord_reciprocalSphereChart]


-- @@ L5284-5367 expanded
/-- In the chart centered at the north pole, the reciprocal of the original finite coordinate is
the fixed real-linear coordinate used by the smooth reciprocal representative. -/
private theorem counterexampleSphereCoord_oppositeChart_reciprocal {x : EuclideanSpace ℝ (Fin 2)}
    (hx : x ≠ 0) :
    100 / star (counterexampleSphereCoord ((stereographic' 2 (-counterexampleNorthPole)).symm x)) =
        counterexampleTwoReciprocalLinearCoord x ∧
      counterexampleTwoReciprocalLinearCoord x ≠ 0 :=
  by
  let Upos :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) 2
        (ne_zero_of_mem_unit_sphere counterexampleNorthPole)).repr
  let Uneg :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) 2
        (ne_zero_of_mem_unit_sphere (-counterexampleNorthPole))).repr
  let u := Uneg.symm x
  have hu :
    (u : EuclideanSpace ℝ (Fin 3)) ∈ (ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ :=
    by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    have hu_neg := Submodule.mem_orthogonal_singleton_iff_inner_left.mp u.2
    change
      inner ℝ (u : EuclideanSpace ℝ (Fin 3))
          (-(counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))) =
        0 at hu_neg
    simpa only [inner_neg_right, neg_eq_zero] using hu_neg
  have hu0 : (u : EuclideanSpace ℝ (Fin 3)) ≠ 0 :=
    by
    intro h
    have hu_zero : u = 0 := Subtype.ext h
    apply hx
    rw [← Uneg.apply_symm_apply x]
    simpa only [u, map_zero] using congrArg Uneg hu_zero
  have htransition :=
    SphereSupport.stereoToFun_stereoInvFunAux_neg (norm_eq_of_mem_sphere counterexampleNorthPole) hu
      hu0
  have hchart :
    (stereographic' 2 counterexampleNorthPole)
        ((stereographic' 2 (-counterexampleNorthPole)).symm x) =
      (4 / ‖x‖ ^ 2) •
        Upos (⟨u, hu⟩ : (ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ) :=
    by
    change
      Upos
          (stereoToFun (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))
            (stereoInvFunAux (-(counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))
              (u : EuclideanSpace ℝ (Fin 3)))) =
        _
    have hunorm : ‖(u : EuclideanSpace ℝ (Fin 3))‖ = ‖x‖ := by
      rw [Submodule.norm_coe, Uneg.symm.norm_map]
    rw [htransition, map_smul, hunorm]
  let y : ℂ :=
    Complex.orthonormalBasisOneI.repr.symm
      (Upos (⟨u, hu⟩ : (ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ))
  have hcoord :
    counterexampleSphereCoord ((stereographic' 2 (-counterexampleNorthPole)).symm x) =
      (2 / ‖x‖ ^ 2) • y :=
    by
    rw [counterexampleSphereCoord, hchart]
    simp only [map_smul, smul_smul]
    apply congrArg (fun c : ℝ ↦ c • y)
    field_simp [pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)]
    ring
  have hnormy : ‖y‖ = ‖x‖ := by
    simp only [y, LinearIsometryEquiv.norm_map]
    change ‖(u : EuclideanSpace ℝ (Fin 3))‖ = ‖x‖
    rw [Submodule.norm_coe, Uneg.symm.norm_map]
  have hy0 : y ≠ 0 := by
    rw [← norm_ne_zero_iff, hnormy]
    exact norm_ne_zero_iff.mpr hx
  have hsquare : ‖x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hx)
  have hstar : star y * y = (‖x‖ ^ 2 : ℂ) :=
    by
    rw [← starRingEnd_apply, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hnormy]
    norm_num
  have hlinear : counterexampleTwoReciprocalLinearCoord x = 50 • y :=
    by
    rw [counterexampleTwoReciprocalLinearCoord]
    change
      50 •
          Complex.orthonormalBasisOneI.repr.symm
            (Upos
              ((ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ.orthogonalProjection
                (u : EuclideanSpace ℝ (Fin 3)))) =
        50 • y
    rw [show
        (ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ.orthogonalProjection
            (u : EuclideanSpace ℝ (Fin 3)) =
          ⟨u, hu⟩
        by
        simpa using
          (ℝ ∙
                (counterexampleNorthPole :
                  EuclideanSpace ℝ (Fin 3)))ᗮ |>.orthogonalProjection_mem_subspace_eq_self
            (⟨u, hu⟩ : (ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ)]
  constructor
  · rw [hcoord, hlinear]
    have hdenom : star ((2 / ‖x‖ ^ 2) • y) ≠ 0 :=
      by
      rw [star_smul]
      exact smul_ne_zero (div_ne_zero (by norm_num) hsquare) (star_ne_zero.mpr hy0)
    rw [div_eq_iff hdenom]
    rw [star_smul]
    simp only [star_trivial]
    simp only [nsmul_eq_mul, Complex.real_smul]
    change (100 : ℂ) = 50 * y * (((2 / ‖x‖ ^ 2 : ℝ) : ℂ) * star y)
    rw [show
        50 * y * (((2 / ‖x‖ ^ 2 : ℝ) : ℂ) * star y) = 50 * ((2 / ‖x‖ ^ 2 : ℝ) : ℂ) * (star y * y) by
        ring,
      hstar]
    push_cast
    field_simp [norm_ne_zero_iff.mpr hx]; norm_num
  · rw [hlinear]
    exact smul_ne_zero (by norm_num) hy0


-- @@ L5369-5376 verbatim
/-- The inverse stereographic chart based at the south pole sends its origin to the north pole. -/
private theorem counterexampleOppositeSphereChart_zero :
    (stereographic' 2 (-counterexampleNorthPole)).symm 0 = counterexampleNorthPole := by
  apply Subtype.ext
  rw [stereographic'_symm_apply]
  dsimp only
  rw [map_zero]
  simp


-- @@ L5378-5411 verbatim
/-- In the north-pole chart, the pointwise extension is exactly the smooth reciprocal
representative composed with a fixed real-linear coordinate. -/
private theorem counterexampleTwoSphereExtension_oppositeChart
    (x : EuclideanSpace ℝ (Fin 2)) :
    counterexampleTwoSphereExtension
        ((stereographic' 2 (-counterexampleNorthPole)).symm x) =
      counterexampleTwoReciprocal (counterexampleTwoReciprocalLinearCoord x) := by
  by_cases hx : x = 0
  · subst x
    have hlinear : counterexampleTwoReciprocalLinearCoord 0 = 0 := by
      simp only [counterexampleTwoReciprocalLinearCoord, map_zero, Submodule.coe_zero, smul_zero]
    rw [counterexampleOppositeSphereChart_zero, hlinear, counterexampleTwoReciprocal_zero]
    simp [counterexampleTwoSphereExtension]
  · have htransition := counterexampleSphereCoord_oppositeChart_reciprocal hx
    have hpole :
        (stereographic' 2 (-counterexampleNorthPole)).symm x ≠
          counterexampleNorthPole := by
      intro h
      have hzero := counterexampleOppositeSphereChart_zero
      exact hx ((stereographic' 2 (-counterexampleNorthPole)).symm.injOn
        (by simp) (by simp) (h.trans hzero.symm))
    have hcoord : counterexampleSphereCoord
        ((stereographic' 2 (-counterexampleNorthPole)).symm x) =
          100 / star (counterexampleTwoReciprocalLinearCoord x) := by
      calc
        counterexampleSphereCoord
            ((stereographic' 2 (-counterexampleNorthPole)).symm x) =
            100 / star (100 / star (counterexampleSphereCoord
              ((stereographic' 2 (-counterexampleNorthPole)).symm x))) :=
          (hundred_div_star_involutive _).symm
        _ = 100 / star (counterexampleTwoReciprocalLinearCoord x) := by
          rw [htransition.1]
    rw [counterexampleTwoSphereExtension, if_neg hpole, hcoord]
    exact counterexample_two_reciprocal htransition.2


-- @@ L5413-5432 verbatim
/-- The reciprocal chart pulls the spherical extension back to the explicit reciprocal
representative. -/
private theorem counterexampleTwoSphereExtension_reciprocalSphereChart (w : ℂ) :
    counterexampleTwoSphereExtension (counterexampleTwoReciprocalSphereChart w) =
      counterexampleTwoReciprocal w := by
  let e := stereographic' 2 (-counterexampleNorthPole)
  have hrho : counterexampleTwoReciprocalSphereChart w ∈ e.source := by
    rw [counterexampleTwoReciprocalSphereChart]
    exact e.map_target (by simp [e])
  calc
    counterexampleTwoSphereExtension (counterexampleTwoReciprocalSphereChart w) =
        counterexampleTwoSphereExtension
          (e.symm (e (counterexampleTwoReciprocalSphereChart w))) := by
      rw [e.left_inv hrho]
    _ = counterexampleTwoReciprocal
        (counterexampleTwoReciprocalLinearCoord
          (e (counterexampleTwoReciprocalSphereChart w))) := by
      exact counterexampleTwoSphereExtension_oppositeChart _
    _ = counterexampleTwoReciprocal w := by
      rw [counterexampleTwoReciprocalLinearCoord_reciprocalSphereChart]


-- @@ L5434-5470 expanded
/-- Ambient rational formula for the reciprocal spherical chart. -/
private theorem counterexampleTwoReciprocalSphereChart_coe (w : ℂ) :
    (counterexampleTwoReciprocalSphereChart w : EuclideanSpace ℝ (Fin 3)) =
      (‖w‖ ^ 2 + 10000)⁻¹ •
        (200 • (counterexampleTwoTangentEquiv w : EuclideanSpace ℝ (Fin 3)) +
          (10000 - ‖w‖ ^ 2) • (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))) :=
  by
  let Uneg :=
    (OrthonormalBasis.fromOrthogonalSpanSingleton (𝕜 := ℝ) (E := EuclideanSpace ℝ (Fin 3)) 2
        (ne_zero_of_mem_unit_sphere (-counterexampleNorthPole))).repr
  let u : (ℝ ∙ (-(counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))))ᗮ :=
    ⟨(50 : ℝ)⁻¹ • (counterexampleTwoTangentEquiv w : EuclideanSpace ℝ (Fin 3)),
      by
      rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
      have htangent :=
        Submodule.mem_orthogonal_singleton_iff_inner_left.mp (counterexampleTwoTangentEquiv w).2
      simp only [real_inner_smul_left, inner_neg_right, htangent, mul_zero, neg_zero]⟩
  rw [counterexampleTwoReciprocalSphereChart, stereographic'_symm_apply]
  simp only [LinearIsometryEquiv.symm_apply_apply]
  change
    (‖(u : EuclideanSpace ℝ (Fin 3))‖ ^ 2 + 4)⁻¹ • (4 : ℝ) • (u : EuclideanSpace ℝ (Fin 3)) +
        (‖(u : EuclideanSpace ℝ (Fin 3))‖ ^ 2 + 4)⁻¹ •
          (‖(u : EuclideanSpace ℝ (Fin 3))‖ ^ 2 - 4) •
            (-(counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))) =
      _
  have hunorm : ‖(u : EuclideanSpace ℝ (Fin 3))‖ ^ 2 = ‖w‖ ^ 2 / 2500 :=
    by
    simp only [u, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by norm_num : (0 : ℝ) < 50),
      Submodule.norm_coe, counterexampleTwoTangentEquiv.norm_map]
    ring
  rw [hunorm]
  simp only [u, ← Nat.cast_smul_eq_nsmul ℝ 200, smul_smul, smul_neg, smul_add]
  have htangent : (‖w‖ ^ 2 / 2500 + 4)⁻¹ * (4 * 50⁻¹) = (‖w‖ ^ 2 + 10000)⁻¹ * 200 :=
    by
    field_simp
    ring
  have hpole :
    -((‖w‖ ^ 2 / 2500 + 4)⁻¹ * (‖w‖ ^ 2 / 2500 - 4)) = (‖w‖ ^ 2 + 10000)⁻¹ * (10000 - ‖w‖ ^ 2) :=
    by
    field_simp
    ring
  rw [← neg_smul, htangent, hpole]
  norm_num [← Nat.cast_smul_eq_nsmul ℝ 200, smul_smul]


-- @@ L5472-5530 expanded
/-- Derivative of the rational reciprocal chart in ambient coordinates. -/
private theorem counterexampleTwoReciprocalSphereChart_fderiv_apply (w v : ℂ) :
    fderiv ℝ (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : EuclideanSpace ℝ (Fin 3))) w
        v =
      (200 / (‖w‖ ^ 2 + 10000)) • (counterexampleTwoTangentEquiv v : EuclideanSpace ℝ (Fin 3)) -
          (400 * inner ℝ w v / (‖w‖ ^ 2 + 10000) ^ 2) •
            (counterexampleTwoTangentEquiv w : EuclideanSpace ℝ (Fin 3)) -
        (40000 * inner ℝ w v / (‖w‖ ^ 2 + 10000) ^ 2) •
          (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)) :=
  by
  let T : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    (ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ.subtypeL.comp
      counterexampleTwoTangentEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hT :
    HasFDerivAt (fun z : ℂ ↦ (counterexampleTwoTangentEquiv z : EuclideanSpace ℝ (Fin 3))) T w :=
    T.hasFDerivAt
  have hs : HasFDerivAt (fun z : ℂ ↦ ‖z‖ ^ 2) ((2 : ℝ) • innerSL ℝ w) w := by
    simpa only [two_smul] using (hasStrictFDerivAt_norm_sq w).hasFDerivAt
  have hden :
    HasFDerivAt (fun z : ℂ ↦ (‖z‖ ^ 2 + 10000)⁻¹)
      (-((‖w‖ ^ 2 + 10000) ^ 2)⁻¹ • ((2 : ℝ) • innerSL ℝ w)) w :=
    by
    convert
      (hasDerivAt_inv (by positivity : ‖w‖ ^ 2 + 10000 ≠ 0)).hasFDerivAt.comp w
        (hs.add_const 10000) using
      1
    all_goals
      ext x
      simp <;> ring
  have hnum :
    HasFDerivAt
      (fun z : ℂ ↦
        (200 : ℝ) • (counterexampleTwoTangentEquiv z : EuclideanSpace ℝ (Fin 3)) +
          (10000 - ‖z‖ ^ 2) • (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))
      ((200 : ℝ) • T +
        (-((2 : ℝ) • innerSL ℝ w)).smulRight (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))
      w :=
    by
    convert
      (hT.const_smul 200).add
        ((hasFDerivAt_const (x := w) 10000).sub hs |>.smul_const
          (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))) using
      1
    all_goals
      ext x
      simp
  have hderiv := hden.smul hnum
  have heq :
    (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : EuclideanSpace ℝ (Fin 3))) =
      fun z : ℂ ↦
      (‖z‖ ^ 2 + 10000)⁻¹ •
        ((200 : ℝ) • (counterexampleTwoTangentEquiv z : EuclideanSpace ℝ (Fin 3)) +
          (10000 - ‖z‖ ^ 2) • (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))) :=
    by
    funext z
    simpa only [ofNat_smul_eq_nsmul] using counterexampleTwoReciprocalSphereChart_coe z
  rw [heq]
  change
    (fderiv ℝ
          (((fun z : ℂ ↦ (‖z‖ ^ 2 + 10000)⁻¹) • fun z ↦
            (200 : ℝ) • (counterexampleTwoTangentEquiv z : EuclideanSpace ℝ (Fin 3)) +
              (10000 - ‖z‖ ^ 2) • (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))))
          w)
        v =
      _
  rw [hderiv.fderiv]
  dsimp only [T]
  have hTv :
    (ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ.subtypeL
        (counterexampleTwoTangentEquiv.toContinuousLinearEquiv.toContinuousLinearMap v) =
      (counterexampleTwoTangentEquiv v : EuclideanSpace ℝ (Fin 3)) :=
    rfl
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.neg_apply, innerSL_apply_apply, smul_add, smul_smul, neg_smul]
  rw [hTv]
  change _ = _
  match_scalars <;> (try simp only [smul_eq_mul]) <;>
      field_simp [show ‖w‖ ^ 2 + 10000 ≠ 0 by positivity] <;>
    ring


-- @@ L5532-5579 expanded
/-- The reciprocal spherical chart is conformal, with scale `200 / (‖w‖² + 10000)`.
Both the inner-product and norm forms are recorded because the radius estimates use each. -/
private theorem counterexampleTwoReciprocalSphereChart_conformal (w v t : ℂ) :
    inner ℝ
          (fderiv ℝ
            (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : EuclideanSpace ℝ (Fin 3))) w v)
          (fderiv ℝ
            (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : EuclideanSpace ℝ (Fin 3))) w
            t) =
        40000 / (‖w‖ ^ 2 + 10000) ^ 2 * inner ℝ v t ∧
      ‖fderiv ℝ (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : EuclideanSpace ℝ (Fin 3)))
            w v‖ =
        200 / (‖w‖ ^ 2 + 10000) * ‖v‖ :=
  by
  have hT (a b : ℂ) :
    inner ℝ (counterexampleTwoTangentEquiv a : EuclideanSpace ℝ (Fin 3))
        (counterexampleTwoTangentEquiv b : EuclideanSpace ℝ (Fin 3)) =
      inner ℝ a b :=
    counterexampleTwoTangentEquiv.inner_map_map a b
  have hTn (a : ℂ) :
    inner ℝ (counterexampleTwoTangentEquiv a : EuclideanSpace ℝ (Fin 3))
        (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)) =
      0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.mp (counterexampleTwoTangentEquiv a).2
  have hnT (a : ℂ) :
    inner ℝ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))
        (counterexampleTwoTangentEquiv a : EuclideanSpace ℝ (Fin 3)) =
      0 :=
    by rw [real_inner_comm, hTn]
  have hnn :
    inner ℝ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))
        (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)) =
      1 :=
    by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere counterexampleNorthPole]
    norm_num
  have hinner (a b : ℂ) :
    inner ℝ
        (fderiv ℝ
          (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : EuclideanSpace ℝ (Fin 3))) w a)
        (fderiv ℝ
          (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : EuclideanSpace ℝ (Fin 3))) w b) =
      40000 / (‖w‖ ^ 2 + 10000) ^ 2 * inner ℝ a b :=
    by
    rw [counterexampleTwoReciprocalSphereChart_fderiv_apply,
      counterexampleTwoReciprocalSphereChart_fderiv_apply]
    simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right, hT,
      hTn, hnT, hnn, mul_zero, sub_zero]
    rw [real_inner_comm a w, real_inner_comm b w]
    rw [real_inner_self_eq_norm_sq]
    field_simp
    ring
  refine ⟨hinner v t, ?_⟩
  have hsquare := hinner v v
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq] at hsquare
  have hden : 0 < ‖w‖ ^ 2 + 10000 := by positivity
  have hscale : 0 ≤ 200 / (‖w‖ ^ 2 + 10000) := by positivity
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hscale (norm_nonneg _))).mp
  calc
    ‖fderiv ℝ (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : EuclideanSpace ℝ (Fin 3))) w
              v‖ ^
          2 =
        40000 / (‖w‖ ^ 2 + 10000) ^ 2 * ‖v‖ ^ 2 :=
      hsquare
    _ = (200 / (‖w‖ ^ 2 + 10000) * ‖v‖) ^ 2 :=
      by
      field_simp
      ring


-- @@ L5581-5631 expanded
/-- The ambient differential of the reciprocal chart has exactly the tangent plane as its
range. -/
private theorem range_fderiv_counterexampleTwoReciprocalSphereChart (w : ℂ) :
    (fderiv ℝ (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : EuclideanSpace ℝ (Fin 3)))
          w).range =
      (ℝ ∙ (counterexampleTwoReciprocalSphereChart w : EuclideanSpace ℝ (Fin 3)))ᗮ :=
  by
  let dρ : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    fderiv ℝ (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : EuclideanSpace ℝ (Fin 3))) w
  have hdρinj : Function.Injective dρ := by
    intro v t hvt
    have hscale := (counterexampleTwoReciprocalSphereChart_conformal w (v - t) (v - t)).2
    change ‖dρ (v - t)‖ = 200 / (‖w‖ ^ 2 + 10000) * ‖v - t‖ at hscale
    rw [map_sub, hvt, sub_self, norm_zero] at hscale
    have hpositive : 0 < 200 / (‖w‖ ^ 2 + 10000) := by positivity
    have : ‖v - t‖ = 0 := by nlinarith [norm_nonneg (v - t)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  have hdρorth (v : ℂ) :
    inner ℝ (dρ v) (counterexampleTwoReciprocalSphereChart w : EuclideanSpace ℝ (Fin 3)) = 0 :=
    by
    have hT (a b : ℂ) :
      inner ℝ (counterexampleTwoTangentEquiv a : EuclideanSpace ℝ (Fin 3))
          (counterexampleTwoTangentEquiv b : EuclideanSpace ℝ (Fin 3)) =
        inner ℝ a b :=
      counterexampleTwoTangentEquiv.inner_map_map a b
    have hTn (a : ℂ) :
      inner ℝ (counterexampleTwoTangentEquiv a : EuclideanSpace ℝ (Fin 3))
          (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)) =
        0 :=
      Submodule.mem_orthogonal_singleton_iff_inner_left.mp (counterexampleTwoTangentEquiv a).2
    have hnT (a : ℂ) :
      inner ℝ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))
          (counterexampleTwoTangentEquiv a : EuclideanSpace ℝ (Fin 3)) =
        0 :=
      by rw [real_inner_comm, hTn]
    have hnn :
      inner ℝ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))
          (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)) =
        1 :=
      by
      rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere counterexampleNorthPole]
      norm_num
    change
      inner ℝ
          (fderiv ℝ
            (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : EuclideanSpace ℝ (Fin 3))) w v)
          (counterexampleTwoReciprocalSphereChart w : EuclideanSpace ℝ (Fin 3)) =
        0
    rw [counterexampleTwoReciprocalSphereChart_fderiv_apply,
      counterexampleTwoReciprocalSphereChart_coe]
    simp only [← Nat.cast_smul_eq_nsmul ℝ 200, inner_sub_left, real_inner_smul_left,
      real_inner_smul_right, inner_add_right, hT, hTn, hnT, hnn, mul_zero]
    rw [real_inner_comm v w, real_inner_self_eq_norm_sq]
    field_simp
    ring
  apply Submodule.eq_of_le_of_finrank_eq
  · intro y hy
    obtain ⟨v, rfl⟩ := hy
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (hdρorth v)
  · have hker : dρ.ker = ⊥ := LinearMap.ker_eq_bot.mpr hdρinj
    have hrank := LinearMap.finrank_range_add_finrank_ker dρ.toLinearMap
    rw [hker, finrank_bot, add_zero, Complex.finrank_real_complex] at hrank
    rw [hrank,
      Submodule.finrank_orthogonal_span_singleton (n := 2)
        (ne_zero_of_mem_unit_sphere (counterexampleTwoReciprocalSphereChart w))]


-- @@ L5633-5656 expanded
/-- The reciprocal chart is smooth as a map into the sphere. -/
private theorem counterexampleTwoReciprocalSphereChart_contMDiff :
    ContMDiff 𝓘(ℝ, ℂ) (𝓡 2) ∞ counterexampleTwoReciprocalSphereChart :=
  by
  apply ContMDiff.codRestrict_sphere
  · have heq :
      (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : EuclideanSpace ℝ (Fin 3))) =
        fun z : ℂ ↦
        (‖z‖ ^ 2 + 10000)⁻¹ •
          (200 • (counterexampleTwoTangentEquiv z : EuclideanSpace ℝ (Fin 3)) +
            (10000 - ‖z‖ ^ 2) • (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))) :=
      by
      funext z
      exact counterexampleTwoReciprocalSphereChart_coe z
    exact
      (show
          ContDiff ℝ ∞
            (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : EuclideanSpace ℝ (Fin 3)))
          by
          rw [heq]
          have hs : ContDiff ℝ ∞ (fun z : ℂ ↦ ‖z‖ ^ 2) := contDiff_norm_sq ℝ
          have hT :
            ContDiff ℝ ∞
              (fun z : ℂ ↦ (counterexampleTwoTangentEquiv z : EuclideanSpace ℝ (Fin 3))) :=
            ((ℝ ∙ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3)))ᗮ.subtypeL.contDiff.comp
              counterexampleTwoTangentEquiv.contDiff)
          have htenThousand : ContDiff ℝ ∞ (fun _ : ℂ ↦ (10000 : ℝ)) := contDiff_const
          have hnorth :
            ContDiff ℝ ∞ (fun _ : ℂ ↦ (counterexampleNorthPole : EuclideanSpace ℝ (Fin 3))) :=
            contDiff_const
          exact
            ((hs.add contDiff_const).inv (fun z ↦ by positivity)).smul
              ((hT.const_smul 200).add ((htenThousand.sub hs).smul hnorth))).contMDiff


-- @@ L5658-5682 expanded
/-- The pointwise extension is smooth at the north pole in the opposite stereographic chart. -/
private theorem counterexampleTwoSphereExtension_contMDiffAt_north :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞ counterexampleTwoSphereExtension counterexampleNorthPole :=
  by
  let e := stereographic' 2 (-counterexampleNorthPole)
  have he : e ∈ IsManifold.maximalAtlas (𝓡 2) ∞ (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    IsManifold.subset_maximalAtlas ⟨-counterexampleNorthPole, rfl⟩
  have hnorth : counterexampleNorthPole ∈ e.source := by
    simpa [e, stereographic'_source] using ne_neg_of_mem_unit_sphere ℝ counterexampleNorthPole
  have he_smooth : ContMDiffAt (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ e counterexampleNorthPole :=
    contMDiffAt_of_mem_maximalAtlas he hnorth
  have hrepresentative :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) 𝓘(ℝ, ℝ) ∞
      (fun x ↦ counterexampleTwoReciprocal (counterexampleTwoReciprocalLinearCoord x)) :=
    (counterexampleTwoReciprocal_contDiff.comp
        counterexampleTwoReciprocalLinearCoord_contDiff).contMDiff
  have hcomp :
    ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ∞
      (fun p ↦ counterexampleTwoReciprocal (counterexampleTwoReciprocalLinearCoord (e p)))
      counterexampleNorthPole :=
    hrepresentative.contMDiffAt.comp counterexampleNorthPole he_smooth
  apply hcomp.congr_of_eventuallyEq
  filter_upwards [e.open_source.mem_nhds hnorth] with p hp
  simpa [e, e.left_inv hp] using counterexampleTwoSphereExtension_oppositeChart (e p)


-- @@ L5684-5693 expanded
/-- The planar expression `counterexample 2` extends smoothly through the missing north pole of
the stereographic chart. -/
theorem counterexample_two_sphere_extension :
    ∃ h : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ,
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h ∧ ∀ z : ℂ, h (counterexampleSphereChart z) = counterexample 2 z :=
  by
  exact
    ⟨counterexampleTwoSphereExtension,
      counterexampleTwoSphereExtension_contMDiff_of_contMDiffAt_north
        counterexampleTwoSphereExtension_contMDiffAt_north,
      counterexampleTwoSphereExtension_chart⟩


-- @@ L5695-5727 expanded
/-- The smooth spherical extension is uniquely determined by its values in the finite
stereographic chart. -/
private theorem eq_counterexampleTwoSphereExtension
    (h : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ) (hsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h)
    (hchart : ∀ z : ℂ, h (counterexampleSphereChart z) = counterexample 2 z) :
    h = counterexampleTwoSphereExtension := by
  funext p
  by_cases hp : p = counterexampleNorthPole
  · subst p
    let e := stereographic' 2 (-counterexampleNorthPole)
    have hecont : Continuous e.symm := by
      rw [← continuousOn_univ]
      simpa [e] using e.symm.continuousOn
    have heq :
      (fun x : EuclideanSpace ℝ (Fin 2) ↦ h (e.symm x)) = fun x ↦
        counterexampleTwoSphereExtension (e.symm x) :=
      by
      apply
        Continuous.ext_on (dense_compl_singleton (0 : EuclideanSpace ℝ (Fin 2)))
          (hsmooth.continuous.comp hecont)
          ((counterexampleTwoSphereExtension_contMDiff_of_contMDiffAt_north
                counterexampleTwoSphereExtension_contMDiffAt_north).continuous.comp
            hecont)
      intro x hx
      have hx0 : x ≠ 0 := by simpa using hx
      have hpole : e.symm x ≠ counterexampleNorthPole :=
        by
        intro h
        have hzero : e.symm 0 = counterexampleNorthPole := by
          simpa [e] using counterexampleOppositeSphereChart_zero
        exact hx0 (e.symm.injOn (by simp [e]) (by simp [e]) (h.trans hzero.symm))
      change h (e.symm x) = counterexampleTwoSphereExtension (e.symm x)
      rw [← counterexampleSphereChart_coord hpole, hchart, counterexampleTwoSphereExtension_chart]
    simpa [e, counterexampleOppositeSphereChart_zero] using congrFun heq 0
  · rw [← counterexampleSphereChart_coord hp, hchart, counterexampleTwoSphereExtension_chart]


-- @@ L5729-5771 verbatim
/-- The constant term dominates the oscillatory term by a vast margin. -/
private theorem counterexample_two_lower (z : ℂ) :
    (1 : ℝ) ≤ counterexample 2 z := by
  let r := ‖z‖
  let w := (100 / star z) ^ ((2 : ℂ) / 2)
  let c := r ^ 2 * Real.exp (-r ^ (-(1 : ℝ) / 4) * Real.exp (-(r ^ 2))) /
    (1 + r ^ 2)
  have hr : 0 ≤ r := norm_nonneg z
  have hc0 : 0 ≤ c := by
    dsimp [c]
    positivity
  have hexp : Real.exp (-r ^ (-(1 : ℝ) / 4) * Real.exp (-(r ^ 2))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (Real.rpow_nonneg hr _))
      (Real.exp_nonneg _)
  have hratio : r ^ 2 / (1 + r ^ 2) ≤ 1 := by
    rw [div_le_one (by positivity : 0 < 1 + r ^ 2)]
    linarith [sq_nonneg r]
  have hc1 : c ≤ 1 := by
    calc
      c = (r ^ 2 / (1 + r ^ 2)) *
          Real.exp (-r ^ (-(1 : ℝ) / 4) * Real.exp (-(r ^ 2))) := by
        dsimp [c]
        ring
      _ ≤ 1 * 1 := mul_le_mul hratio hexp (Real.exp_nonneg _) (by norm_num)
      _ = 1 := one_mul 1
  have hseed : -(253 / 160 : ℝ) ≤ counterexampleSeed w :=
    neg_le_of_abs_le (counterexampleSeed_abs_le w)
  have hproduct : -(253 / 160 : ℝ) ≤ c * counterexampleSeed w := by
    calc
      -(253 / 160 : ℝ) ≤ c * (-(253 / 160 : ℝ)) := by nlinarith
      _ ≤ c * counterexampleSeed w := mul_le_mul_of_nonneg_left hseed hc0
  have hproduct' : -(253 / 160 : ℝ) ≤
      ‖z‖ ^ 2 * Real.exp (-‖z‖ ^ (-(1 : ℝ) / 4) * Real.exp (-(‖z‖ ^ 2))) *
        counterexampleSeed ((100 / star z) ^ ((2 : ℂ) / 2)) / (1 + ‖z‖ ^ 2) := by
    calc
      -(253 / 160 : ℝ) ≤ c * counterexampleSeed w := hproduct
      _ = _ := by
        dsimp [c, r, w]
        ring
  rw [counterexample]
  norm_num at hproduct' ⊢
  linarith


-- @@ L5773-5781 expanded
/-- The explicit spherical extension is uniformly positive, so its support body contains a
unit ball. -/
private theorem counterexampleTwoSphereExtension_lower
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) : (1 : ℝ) ≤ counterexampleTwoSphereExtension p :=
  by
  by_cases hp : p = counterexampleNorthPole
  · simp [counterexampleTwoSphereExtension, hp]
    norm_num
  · rw [counterexampleTwoSphereExtension, if_neg hp]
    exact counterexample_two_lower _


-- @@ L5783-5790 expanded
/-- The homogeneous extension is nonnegative in every ambient direction. -/
private theorem counterexampleTwoRadialExtension_nonneg (x : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ SphereSupport.radialExtension counterexampleTwoSphereExtension x :=
  by
  by_cases hx : x = 0
  · simp [hx, SphereSupport.radialExtension]
  · rw [SphereSupport.radialExtension, dif_neg hx]
    exact
      mul_nonneg (norm_nonneg x) (le_trans zero_le_one (counterexampleTwoSphereExtension_lower _))


-- @@ L5792-5824 verbatim
/-- A coarse uniform bound for the power-times-exponential terms in the reciprocal-chart
estimates. The extra `1` lets the proof split at `y = 1` without optimizing a maximum. -/
private theorem rpow_mul_exp_neg_le_factorial {y c a : ℝ} (n : ℕ)
    (hy : 0 ≤ y) (hc : 0 < c) (ha : 0 ≤ a) (han : a ≤ n) :
    y ^ a * Real.exp (-c * y) ≤ 1 + n.factorial / c ^ n := by
  by_cases hy1 : y ≤ 1
  · calc
      y ^ a * Real.exp (-c * y) ≤ 1 * 1 := by
        exact mul_le_mul (Real.rpow_le_one hy hy1 ha)
          (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hy))
          (Real.exp_nonneg _) zero_le_one
      _ ≤ 1 + n.factorial / c ^ n := by
        simpa only [id_eq, one_mul] using
          (le_add_of_nonneg_right (show 0 ≤ n.factorial / c ^ n by positivity))
  · have h1y : 1 ≤ y := le_of_not_ge hy1
    have hpower : y ^ a ≤ y ^ n := by
      simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le h1y han
    have hfactorial : (0 : ℝ) < n.factorial := by positivity
    have hexp := Real.pow_div_factorial_le_exp (x := c * y) (mul_nonneg hc.le hy) n
    have hpowexp : c ^ n * y ^ n ≤ n.factorial * Real.exp (c * y) := by
      have := (div_le_iff₀ hfactorial).mp hexp
      simpa only [mul_pow, mul_comm] using this
    have hquotient : y ^ n / Real.exp (c * y) ≤ n.factorial / c ^ n := by
      rw [div_le_div_iff₀ (Real.exp_pos _) (pow_pos hc n)]
      simpa only [mul_comm] using hpowexp
    calc
      y ^ a * Real.exp (-c * y) ≤ y ^ n * Real.exp (-c * y) :=
        mul_le_mul_of_nonneg_right hpower (Real.exp_nonneg _)
      _ = y ^ n / Real.exp (c * y) := by
        rw [show -c * y = -(c * y) by ring, Real.exp_neg]
        rfl
      _ ≤ n.factorial / c ^ n := hquotient
      _ ≤ 1 + n.factorial / c ^ n := le_add_of_nonneg_left zero_le_one


-- @@ L5826-5840 verbatim
/-- The elementary exact maximum estimate for `t ^ a * exp (-t)`. It avoids introducing a
calculus maximizer into each reciprocal-chart coefficient bound. -/
private theorem rpow_mul_exp_neg_le_self {t a : ℝ} (ht : 0 ≤ t) (ha : 0 < a) :
    t ^ a * Real.exp (-t) ≤ a ^ a * Real.exp (-a) := by
  obtain rfl | ht := ht.eq_or_lt
  · simp [Real.zero_rpow ha.ne']
    positivity
  · have hlog := Real.log_le_sub_one_of_pos (div_pos ht ha)
    have hlog' : a * Real.log t - t ≤ a * Real.log a - a := by
      have h := mul_le_mul_of_nonneg_left hlog ha.le
      rw [Real.log_div ht.ne' ha.ne'] at h
      field_simp [ha.ne'] at h
      linarith
    rw [Real.rpow_def_of_pos ht, Real.rpow_def_of_pos ha, ← Real.exp_add, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)


-- @@ L5842-5855 verbatim
/-- For the exponents used below, the exact maximum admits a very simple rational upper bound. -/
private theorem self_rpow_mul_exp_neg_le_half {a : ℝ} (ha1 : 1 ≤ a) (ha2 : a ≤ 2) :
    a ^ a * Real.exp (-a) ≤ a / 2 := by
  have ha : 0 ≤ a := zero_le_one.trans ha1
  have hquot0 : 0 ≤ a / Real.exp 1 := div_nonneg ha (Real.exp_nonneg _)
  have hquot1 : a / Real.exp 1 ≤ 1 := by
    rw [div_le_one (Real.exp_pos _)]
    exact ha2.trans Real.exp_one_gt_two.le
  calc
    a ^ a * Real.exp (-a) = (a / Real.exp 1) ^ a := by
      rw [show -a = (-1) * a by ring, Real.exp_mul, Real.exp_neg,
        ← Real.mul_rpow ha (inv_nonneg.mpr (Real.exp_nonneg 1)), div_eq_mul_inv]
    _ ≤ a / Real.exp 1 := Real.rpow_le_self_of_le_one hquot0 hquot1 ha1
    _ ≤ a / 2 := div_le_div_of_nonneg_left ha (by norm_num) Real.exp_one_gt_two.le


-- @@ L5857-5865 verbatim
/-- For exponents at most one, the unscaled power-times-exponential maximum is at most one. -/
private theorem rpow_mul_exp_neg_le_one {t a : ℝ} (ht : 0 ≤ t) (ha : 0 < a) (ha1 : a ≤ 1) :
    t ^ a * Real.exp (-t) ≤ 1 := by
  refine (rpow_mul_exp_neg_le_self ht ha).trans ?_
  calc
    a ^ a * Real.exp (-a) ≤ 1 * 1 := by
      exact mul_le_mul (Real.rpow_le_one ha.le ha1 ha.le)
        (Real.exp_le_one_iff.mpr (neg_nonpos.mpr ha.le)) (Real.exp_nonneg _) zero_le_one
    _ = 1 := one_mul 1


-- @@ L5867-5887 verbatim
/-- With exponent at most four, doubling the exponential rate makes the same maximum at most
one. This single loose estimate controls the largest term in the second damping derivative. -/
private theorem rpow_mul_exp_neg_two_mul_le_one {t a : ℝ}
    (ht : 0 ≤ t) (ha : 0 < a) (ha4 : a ≤ 4) :
    t ^ a * Real.exp (-2 * t) ≤ 1 := by
  have hmax := rpow_mul_exp_neg_le_self (t := 2 * t) (a := a) (mul_nonneg (by norm_num) ht) ha
  have hself : a ^ a * Real.exp (-a) ≤ (2 : ℝ) ^ a := by
    rw [show -a = (-1) * a by ring, Real.exp_mul, Real.exp_neg,
      ← Real.mul_rpow ha.le (inv_nonneg.mpr (Real.exp_nonneg 1)), ← div_eq_mul_inv]
    exact Real.rpow_le_rpow (div_nonneg ha.le (Real.exp_nonneg _))
      (by rw [div_le_iff₀ (Real.exp_pos _)]; nlinarith [Real.exp_one_gt_two]) ha.le
  have hscaled : (2 : ℝ) ^ a * (t ^ a * Real.exp (-2 * t)) ≤ (2 : ℝ) ^ a := by
    calc
      (2 : ℝ) ^ a * (t ^ a * Real.exp (-2 * t)) =
          (2 * t) ^ a * Real.exp (-(2 * t)) := by
        rw [Real.mul_rpow (by norm_num) ht]
        ring
      _ ≤ a ^ a * Real.exp (-a) := hmax
      _ ≤ (2 : ℝ) ^ a := hself
  have hpos : 0 < (2 : ℝ) ^ a := Real.rpow_pos_of_pos (by norm_num) a
  exact le_of_mul_le_mul_left (by simpa using hscaled) hpos


-- @@ L5889-5903 verbatim
/-- The first reciprocal damping-derivative numerator is at most one. -/
private theorem reciprocalDampingFirstNumerator_bound {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-t) * ((1 / 8 : ℝ) * t ^ (3 / 8 : ℝ) + t ^ (11 / 8 : ℝ)) ≤ 1 := by
  have hsmall : t ^ (3 / 8 : ℝ) * Real.exp (-t) ≤ 1 :=
    rpow_mul_exp_neg_le_one ht (by norm_num) (by norm_num)
  have hlarge : t ^ (11 / 8 : ℝ) * Real.exp (-t) ≤ 11 / 16 :=
    (rpow_mul_exp_neg_le_self ht (by norm_num)).trans
      ((self_rpow_mul_exp_neg_le_half (a := 11 / 8) (by norm_num) (by norm_num)).trans_eq
        (by norm_num))
  calc
    Real.exp (-t) * ((1 / 8 : ℝ) * t ^ (3 / 8 : ℝ) + t ^ (11 / 8 : ℝ)) =
        (1 / 8 : ℝ) * (t ^ (3 / 8 : ℝ) * Real.exp (-t)) +
          t ^ (11 / 8 : ℝ) * Real.exp (-t) := by ring
    _ ≤ (1 / 8 : ℝ) * 1 + 11 / 16 := by gcongr
    _ ≤ 1 := by norm_num


-- @@ L5905-5948 verbatim
/-- The six terms in the second reciprocal damping-derivative numerator admit the rational
bound used in the global uniqueness and radius estimates. -/
private theorem reciprocalDampingSecondNumerator_bound {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (-2 * t) * ((1 / 64 : ℝ) * t ^ (3 / 4 : ℝ) +
        (1 / 4 : ℝ) * t ^ (7 / 4 : ℝ) + t ^ (11 / 4 : ℝ)) +
      Real.exp (-t) * ((7 / 64 : ℝ) * t ^ (7 / 8 : ℝ) +
        (7 / 4 : ℝ) * t ^ (15 / 8 : ℝ) + t ^ (23 / 8 : ℝ)) < 10 := by
  have hexp_two_le (a : ℝ) :
      t ^ a * Real.exp (-2 * t) ≤ t ^ a * Real.exp (-t) := by
    gcongr
    nlinarith
  have h₁ : t ^ (3 / 4 : ℝ) * Real.exp (-2 * t) ≤ 1 :=
    rpow_mul_exp_neg_two_mul_le_one ht (by norm_num) (by norm_num)
  have h₂ : t ^ (7 / 4 : ℝ) * Real.exp (-2 * t) ≤ 7 / 8 :=
    (hexp_two_le (7 / 4)).trans <|
      (rpow_mul_exp_neg_le_self ht (by norm_num)).trans
        ((self_rpow_mul_exp_neg_le_half (a := 7 / 4) (by norm_num) (by norm_num)).trans_eq
          (by norm_num))
  have h₃ : t ^ (11 / 4 : ℝ) * Real.exp (-2 * t) ≤ 1 :=
    rpow_mul_exp_neg_two_mul_le_one ht (by norm_num) (by norm_num)
  have h₄ : t ^ (7 / 8 : ℝ) * Real.exp (-t) ≤ 1 :=
    rpow_mul_exp_neg_le_one ht (by norm_num) (by norm_num)
  have h₅ : t ^ (15 / 8 : ℝ) * Real.exp (-t) ≤ 15 / 16 :=
    (rpow_mul_exp_neg_le_self ht (by norm_num)).trans
      ((self_rpow_mul_exp_neg_le_half (a := 15 / 8) (by norm_num) (by norm_num)).trans_eq
        (by norm_num))
  have h₆ : t ^ (23 / 8 : ℝ) * Real.exp (-t) ≤ 7 := by
    convert rpow_mul_exp_neg_le_factorial 3 ht (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) ≤ 23 / 8) (by norm_num : (23 / 8 : ℝ) ≤ 3) using 1 <;>
      norm_num [Nat.factorial]
  calc
    Real.exp (-2 * t) * ((1 / 64 : ℝ) * t ^ (3 / 4 : ℝ) +
        (1 / 4 : ℝ) * t ^ (7 / 4 : ℝ) + t ^ (11 / 4 : ℝ)) +
      Real.exp (-t) * ((7 / 64 : ℝ) * t ^ (7 / 8 : ℝ) +
        (7 / 4 : ℝ) * t ^ (15 / 8 : ℝ) + t ^ (23 / 8 : ℝ)) =
        (1 / 64 : ℝ) * (t ^ (3 / 4 : ℝ) * Real.exp (-2 * t)) +
        (1 / 4 : ℝ) * (t ^ (7 / 4 : ℝ) * Real.exp (-2 * t)) +
        t ^ (11 / 4 : ℝ) * Real.exp (-2 * t) +
        (7 / 64 : ℝ) * (t ^ (7 / 8 : ℝ) * Real.exp (-t)) +
        (7 / 4 : ℝ) * (t ^ (15 / 8 : ℝ) * Real.exp (-t)) +
        t ^ (23 / 8 : ℝ) * Real.exp (-t) := by ring
    _ ≤ (1 / 64 : ℝ) * 1 + (1 / 4 : ℝ) * (7 / 8) + 1 +
        (7 / 64 : ℝ) * 1 + (7 / 4 : ℝ) * (15 / 16) + 7 := by gcongr
    _ < 10 := by norm_num


-- @@ L5950-6005 verbatim
/-- The reciprocal-chart conformal weight times the damping factor has a deliberately coarse
global numerical bound. This is the main growth estimate behind the radius-tensor certificate. -/
private theorem reciprocalMetricDamping_bound {y : ℝ} (hy : 0 ≤ y) :
    2500 * (1 + y ^ 8) * Real.exp (-(y * Real.exp (-(y ^ (-(8 : ℝ)))))) <
      164000000 := by
  by_cases hy2 : y ≤ 2
  · have hy8 : y ^ 8 ≤ (2 : ℝ) ^ 8 := pow_le_pow_left₀ hy hy2 8
    have hpsi : 0 ≤ y * Real.exp (-(y ^ (-(8 : ℝ)))) :=
      mul_nonneg hy (Real.exp_nonneg _)
    calc
      2500 * (1 + y ^ 8) * Real.exp (-(y * Real.exp (-(y ^ (-(8 : ℝ)))))) ≤
          2500 * (1 + (2 : ℝ) ^ 8) * 1 := by
        gcongr
        exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hpsi)
      _ < 164000000 := by norm_num
  · have hy8 : (256 : ℝ) ≤ y ^ 8 := by
      convert pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) (le_of_not_ge hy2) 8 using 1
      all_goals first
        | with_reducible_and_instances rfl
        | norm_num
    have hypos : 0 < y := lt_of_lt_of_le (by norm_num) (le_of_not_ge hy2)
    have hinv : y ^ (-(8 : ℝ)) ≤ 1 / 256 := by
      rw [Real.rpow_neg hy]
      have hy8r : y ^ (8 : ℝ) = y ^ (8 : ℕ) := Real.rpow_natCast y 8
      calc
        (y ^ (8 : ℝ))⁻¹ = (y ^ (8 : ℕ))⁻¹ := by rw [hy8r]
        _ ≤ (256 : ℝ)⁻¹ :=
          (inv_le_inv₀ (pow_pos hypos 8) (by norm_num)).2 hy8
        _ = 1 / 256 := by norm_num
    have hdamping : (255 / 256 : ℝ) ≤ Real.exp (-(y ^ (-(8 : ℝ)))) := by
      calc
        (255 / 256 : ℝ) = 1 - 1 / 256 := by norm_num
        _ ≤ 1 - y ^ (-(8 : ℝ)) := sub_le_sub_left hinv 1
        _ ≤ Real.exp (-(y ^ (-(8 : ℝ)))) := Real.one_sub_le_exp_neg _
    have hexp : Real.exp (-(y * Real.exp (-(y ^ (-(8 : ℝ)))))) ≤
        Real.exp (-(255 / 256 : ℝ) * y) := by
      rw [Real.exp_le_exp]
      simpa [mul_comm] using neg_le_neg (mul_le_mul_of_nonneg_left hdamping hy)
    have hpower := rpow_mul_exp_neg_le_factorial 8 hy
      (by norm_num : (0 : ℝ) < 255 / 256) (by norm_num : (0 : ℝ) ≤ 8)
      (by norm_num : (8 : ℝ) ≤ 8)
    have hpower' : y ^ 8 * Real.exp (-(255 / 256 : ℝ) * y) ≤
        1 + (8 : ℕ).factorial / (255 / 256 : ℝ) ^ 8 := by
      convert hpower using 1 ; norm_num
    have hexp_one : Real.exp (-(255 / 256 : ℝ) * y) ≤ 1 := by
      exact Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hy)
    calc
      2500 * (1 + y ^ 8) * Real.exp (-(y * Real.exp (-(y ^ (-(8 : ℝ)))))) ≤
          2500 * (1 + y ^ 8) * Real.exp (-(255 / 256 : ℝ) * y) := by
        gcongr
      _ = 2500 * (Real.exp (-(255 / 256 : ℝ) * y) +
          y ^ 8 * Real.exp (-(255 / 256 : ℝ) * y)) := by ring
      _ ≤ 2500 * (1 + (1 + (8 : ℕ).factorial / (255 / 256 : ℝ) ^ 8)) := by
        gcongr
      _ < 164000000 := by norm_num [Nat.factorial]


-- @@ L6007-6045 verbatim
/-- The preceding one-variable estimate in the exact reciprocal-chart normalization. -/
private theorem reciprocalConformalDamping_bound (w : ℂ) :
    (‖w‖ ^ 2 + 10000) ^ 2 / 40000 * counterexampleTwoReciprocalDamping w <
      164000000 := by
  by_cases hw : w = 0
  · subst w
    simp [counterexampleTwoReciprocalDamping, counterexampleTwoReciprocalExponent]
    norm_num
  · let s := ‖w‖ ^ 2
    let y := (s / 10000) ^ ((1 : ℝ) / 8)
    have hs : 0 < s := sq_pos_of_pos (norm_pos_iff.mpr hw)
    have hy : 0 < y := Real.rpow_pos_of_pos (div_pos hs (by norm_num)) _
    have hy8 : y ^ 8 = s / 10000 := by
      dsimp only [y]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (div_nonneg hs.le (by norm_num))]
      norm_num
    have hyneg8 : y ^ (-(8 : ℝ)) = 10000 / s := by
      calc
        y ^ (-(8 : ℝ)) = (y ^ (8 : ℝ))⁻¹ := Real.rpow_neg hy.le (8 : ℝ)
        _ = (y ^ (8 : ℕ))⁻¹ := congrArg Inv.inv (Real.rpow_natCast y 8)
        _ = 10000 / s := by rw [hy8, inv_div]
    have hψ : counterexampleTwoReciprocalExponent s =
        y * Real.exp (-(y ^ (-(8 : ℝ)))) := by
      rw [counterexampleTwoReciprocalExponent_of_pos hs, hyneg8]
      dsimp only [y]
      congr 2 ; ring
    have hbound := reciprocalMetricDamping_bound hy.le
    rw [counterexampleTwoReciprocalDamping]
    change (s + 10000) ^ 2 / 40000 *
      (10000 / (s + 10000) * Real.exp (-counterexampleTwoReciprocalExponent s)) < _
    rw [hψ]
    calc
      (s + 10000) ^ 2 / 40000 *
          (10000 / (s + 10000) * Real.exp (-(y * Real.exp (-y ^ (-(8 : ℝ)))))) =
          2500 * (1 + y ^ 8) * Real.exp (-(y * Real.exp (-y ^ (-(8 : ℝ))))) := by
        rw [hy8]
        field_simp [show s + 10000 ≠ 0 by positivity]
        ring
      _ < 164000000 := hbound


-- @@ L6047-6086 expanded
/-- The degree-one radial extension of a smooth function on the sphere is smooth away from the
origin. -/
private theorem radialExtension_contDiffOn_compl_of_contMDiff
    (h : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ) (hsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h) :
    ContDiffOn ℝ ∞ (SphereSupport.radialExtension h) {0}ᶜ :=
  by
  let U : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin 3)) := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  have hnorm : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x : U ↦ ‖(x : EuclideanSpace ℝ (Fin 3))‖) :=
    by
    intro x
    exact (contDiffAt_norm ℝ x.property).contMDiffAt.comp x contMDiff_subtype_val.contMDiffAt
  have hnorm_ne : ∀ x : U, ‖(x : EuclideanSpace ℝ (Fin 3))‖ ≠ 0 := fun x ↦
    norm_ne_zero_iff.mpr x.property
  have hnorm_inv : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ (fun x : U ↦ ‖(x : EuclideanSpace ℝ (Fin 3))‖⁻¹) :=
    hnorm.inv₀ hnorm_ne
  have hnormalize_mem (x : U) :
    ‖(x : EuclideanSpace ℝ (Fin 3))‖⁻¹ • (x : EuclideanSpace ℝ (Fin 3)) ∈
      sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    by
    rw [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
      inv_mul_cancel₀ (hnorm_ne x)]
  let normalize : U → sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := fun x ↦
    ⟨‖(x : EuclideanSpace ℝ (Fin 3))‖⁻¹ • (x : EuclideanSpace ℝ (Fin 3)), hnormalize_mem x⟩
  have hnormalize : ContMDiff (𝓡 3) (𝓡 2) ∞ normalize := by
    exact (hnorm_inv.smul contMDiff_subtype_val).codRestrict_sphere hnormalize_mem
  have hradial :
    ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞
      (fun x : U ↦ SphereSupport.radialExtension h (x : EuclideanSpace ℝ (Fin 3))) :=
    by
    apply (hnorm.mul (hsmooth.comp hnormalize)).congr
    intro x
    change
      SphereSupport.radialExtension h (x : EuclideanSpace ℝ (Fin 3)) =
        ‖(x : EuclideanSpace ℝ (Fin 3))‖ * h (normalize x)
    have hx0 : (x : EuclideanSpace ℝ (Fin 3)) ≠ 0 :=
      by
      intro hx
      apply x.property
      simpa only [Set.mem_singleton_iff] using hx
    rw [SphereSupport.radialExtension, dif_neg hx0]
  intro x hx
  let xU : U := ⟨x, hx⟩
  have hx_smooth : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞ (SphereSupport.radialExtension h) x := by
    exact
      contMDiffAt_subtype_iff.mp
        (hradial.contMDiffAt :
          ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞
            (fun y : U ↦ SphereSupport.radialExtension h (y : EuclideanSpace ℝ (Fin 3))) xU)
  exact hx_smooth.contDiffAt.contDiffWithinAt


-- @@ L6088-6097 expanded
/-- The degree-one radial extension of a smooth function on the sphere is differentiable away
from the origin. This is applied only on the unit sphere below. -/
private theorem radialExtension_differentiableAt_of_contMDiff
    (h : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ) (hsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h)
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    DifferentiableAt ℝ (SphereSupport.radialExtension h) (p : EuclideanSpace ℝ (Fin 3)) := by
  exact
    (radialExtension_contDiffOn_compl_of_contMDiff h hsmooth (p : EuclideanSpace ℝ (Fin 3))
            (ne_zero_of_mem_unit_sphere p)).differentiableWithinAt
        (by simp) |>.differentiableAt
      (isOpen_compl_singleton.mem_nhds (ne_zero_of_mem_unit_sphere p))


-- @@ L6099-6107 expanded
/-- The homogeneous extension of the explicit spherical function is differentiable at every
point of the unit sphere. -/
private theorem counterexampleTwoRadialExtension_differentiableAt
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    DifferentiableAt ℝ (SphereSupport.radialExtension counterexampleTwoSphereExtension)
      (p : EuclideanSpace ℝ (Fin 3)) :=
  by
  exact
    radialExtension_differentiableAt_of_contMDiff counterexampleTwoSphereExtension
      (counterexampleTwoSphereExtension_contMDiff_of_contMDiffAt_north
        counterexampleTwoSphereExtension_contMDiffAt_north)
      p


-- @@ L6109-6128 expanded
/-- The contact map obtained from the homogeneous extension of a smooth spherical function is
smooth. -/
private theorem homogeneousGradient_contMDiff_of_contMDiff
    (h : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ) (hsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h) :
    ContMDiff (𝓡 2) (𝓡 3) ∞ (SphereSupport.homogeneousGradient (SphereSupport.radialExtension h)) :=
  by
  let H := SphereSupport.radialExtension h
  have hH : ContDiffOn ℝ ∞ H {0}ᶜ := radialExtension_contDiffOn_compl_of_contMDiff h hsmooth
  have hDf : ContDiffOn ℝ ∞ (fderiv ℝ H) {0}ᶜ :=
    hH.fderiv_of_isOpen isOpen_compl_singleton (by simp)
  have hgradient : ContDiffOn ℝ ∞ (gradient H) {0}ᶜ :=
    by
    rw [show gradient H = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm ∘ fderiv ℝ H
        by rfl]
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.contDiff.comp_contDiffOn hDf
  intro p
  have hp : (p : EuclideanSpace ℝ (Fin 3)) ∈ ({0}ᶜ : Set (EuclideanSpace ℝ (Fin 3))) :=
    ne_zero_of_mem_unit_sphere p
  have hp_gradient : ContDiffAt ℝ ∞ (gradient H) (p : EuclideanSpace ℝ (Fin 3)) :=
    (hgradient (p : EuclideanSpace ℝ (Fin 3)) hp).contDiffAt (isOpen_compl_singleton.mem_nhds hp)
  exact hp_gradient.contMDiffAt.comp p (contMDiff_coe_sphere p)


-- @@ L6130-6137 verbatim
/-- The explicit homogeneous-gradient contact map is smooth. -/
private theorem counterexampleTwoHomogeneousGradient_contMDiff :
    ContMDiff (𝓡 2) (𝓡 3) ∞
      (SphereSupport.homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension)) := by
  exact homogeneousGradient_contMDiff_of_contMDiff counterexampleTwoSphereExtension
    (counterexampleTwoSphereExtension_contMDiff_of_contMDiffAt_north
      counterexampleTwoSphereExtension_contMDiffAt_north)


-- @@ L6139-6142 verbatim
/-- The first anti-holomorphic derivative, in the normalization for which the repository's
`traceFreeHessian` is four times its second iterate. -/
private noncomputable def complexBarDeriv (u : ℂ → ℝ) (w : ℂ) : ℂ :=
  ((fderiv ℝ u w 1 : ℂ) + (fderiv ℝ u w Complex.I : ℂ) * Complex.I) / 2


-- @@ L6144-6147 verbatim
/-- The trace-free spherical Hessian in a stereographic chart whose metric denominator is
`‖w‖² + a`. Its vanishing is the coordinate form of the umbilic equation. -/
private noncomputable def sphericalTraceFreeHessian (a : ℝ) (u : ℂ → ℝ) (w : ℂ) : ℂ :=
  traceFreeHessian u w + 8 * w / (‖w‖ ^ 2 + a) * complexBarDeriv u w


-- @@ L6149-6153 verbatim
/-- The Euclidean chart Laplacian, encoded using the same second Fréchet derivative as the
trace-free Hessian. -/
private noncomputable def chartLaplacian (u : ℂ → ℝ) (w : ℂ) : ℝ :=
  let H := fderiv ℝ (fun z ↦ fderiv ℝ u z) w
  H 1 1 + H Complex.I Complex.I


-- @@ L6155-6251 unexpanded
/-- In reciprocal coordinates, the homogeneous gradient is the support value in the radial
direction plus the metric-dual of the first derivative in the tangent direction. -/
private theorem counterexampleTwoHomogeneousGradient_reciprocalSphereChart (w : ℂ) :
    let F := SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
    let dρ := fderiv ℝ
      (fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)) w
    F (counterexampleTwoReciprocalSphereChart w) =
      counterexampleTwoReciprocal w • (counterexampleTwoReciprocalSphereChart w : ℝ³) +
        ((‖w‖ ^ 2 + 10000) ^ 2 / 20000) •
          dρ (complexBarDeriv counterexampleTwoReciprocal w) := by
  let H := SphereSupport.radialExtension counterexampleTwoSphereExtension
  let F := SphereSupport.homogeneousGradient H
  let ρ : ℂ → ℝ³ := fun z ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)
  let dρ : ℂ →L[ℝ] ℝ³ := fderiv ℝ ρ w
  let p := counterexampleTwoReciprocalSphereChart w
  let G : ℝ³ := counterexampleTwoReciprocal w • (p : ℝ³) +
    ((‖w‖ ^ 2 + 10000) ^ 2 / 20000) •
      dρ (complexBarDeriv counterexampleTwoReciprocal w)
  have hρdiff : Differentiable ℝ ρ := by
    exact (contMDiff_coe_sphere.comp counterexampleTwoReciprocalSphereChart_contMDiff).contDiff
      |>.differentiable (by simp)
  have hdρrange : dρ.range = (ℝ ∙ (p : ℝ³))ᗮ := by
    simpa only [dρ, ρ, p] using range_fderiv_counterexampleTwoReciprocalSphereChart w
  have hdρorth (v : ℂ) : inner ℝ (dρ v) (p : ℝ³) = 0 := by
    rw [← Submodule.mem_orthogonal_singleton_iff_inner_left, ← hdρrange]
    exact ⟨v, rfl⟩
  have hHdiff : DifferentiableAt ℝ H (p : ℝ³) :=
    counterexampleTwoRadialExtension_differentiableAt p
  have hcontact : inner ℝ (F p) (p : ℝ³) = counterexampleTwoReciprocal w := by
    calc
      inner ℝ (F p) (p : ℝ³) = H p :=
        SphereSupport.inner_homogeneousGradient H p hHdiff
          (fun t ht ↦ SphereSupport.radialExtension_smul_of_pos _ _ ht)
      _ = counterexampleTwoReciprocal w := by
        dsimp only [H]
        rw [SphereSupport.radialExtension_coe,
          counterexampleTwoSphereExtension_reciprocalSphereChart]
  have hdifferentiate (v : ℂ) :
      fderiv ℝ counterexampleTwoReciprocal w v =
        fderiv ℝ H (p : ℝ³) (dρ v) := by
    have hcomp := hHdiff.hasFDerivAt.comp w hρdiff.differentiableAt.hasFDerivAt
    have heq : H ∘ ρ = counterexampleTwoReciprocal := by
      funext z
      dsimp only [Function.comp_apply, H, ρ]
      rw [SphereSupport.radialExtension_coe,
        counterexampleTwoSphereExtension_reciprocalSphereChart]
    rw [heq] at hcomp
    exact congr($hcomp.fderiv v)
  have hfirst (v : ℂ) : fderiv ℝ counterexampleTwoReciprocal w v =
      2 * inner ℝ (complexBarDeriv counterexampleTwoReciprocal w) v := by
    have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
      apply Complex.ext <;> simp
    rw [hv, map_add, map_smul, map_smul, complexBarDeriv]
    simp only [smul_eq_mul]
    simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.div_re, Complex.div_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.normSq_apply]
    norm_num
    ring
  have hGcontact : inner ℝ G (p : ℝ³) = counterexampleTwoReciprocal w := by
    dsimp only [G]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left,
      hdρorth, mul_zero, add_zero, real_inner_self_eq_norm_sq,
      norm_eq_of_mem_sphere p]
    ring
  have htangent (v : ℂ) : inner ℝ (F p - G) (dρ v) = 0 := by
    dsimp only [F, SphereSupport.homogeneousGradient]
    rw [inner_sub_left, inner_gradient_left, ← hdifferentiate v, hfirst]
    have hmetric := (counterexampleTwoReciprocalSphereChart_conformal w
      (complexBarDeriv counterexampleTwoReciprocal w) v).1
    change inner ℝ (dρ (complexBarDeriv counterexampleTwoReciprocal w)) (dρ v) =
      40000 / (‖w‖ ^ 2 + 10000) ^ 2 *
        inner ℝ (complexBarDeriv counterexampleTwoReciprocal w) v at hmetric
    dsimp only [G]
    have hporth : inner ℝ (p : ℝ³) (dρ v) = 0 := by
      rw [real_inner_comm, hdρorth]
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, hporth,
      mul_zero, zero_add, hmetric]
    field_simp
    ring
  have hradial : inner ℝ (F p - G) (p : ℝ³) = 0 := by
    rw [inner_sub_left, hcontact, hGcontact, sub_self]
  have hdmem : F p - G ∈ dρ.range := by
    rw [hdρrange, Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact hradial
  obtain ⟨v, hv⟩ := hdmem
  have hzero := htangent v
  rw [← hv] at hzero
  change inner ℝ (dρ v) (dρ v) = 0 at hzero
  rw [real_inner_self_eq_norm_sq] at hzero
  have hdρzero : dρ v = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hzero)
  have hdiffzero : F p - G = 0 := by
    have hzero' : (0 : ℝ³) = F p - G := by simpa [hdρzero] using hv
    exact hzero'.symm
  exact sub_eq_zero.mp hdiffzero


-- @@ L6253-6265 verbatim
/-- The real Fréchet derivative expressed through the complex bar derivative. -/
private theorem fderiv_eq_two_inner_complexBarDeriv (u : ℂ → ℝ) (w v : ℂ) :
    fderiv ℝ u w v = 2 * inner ℝ (complexBarDeriv u w) v := by
  have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
    apply Complex.ext <;> simp
  rw [hv, map_add, map_smul, map_smul]
  simp only [complexBarDeriv, smul_eq_mul]
  simp only [Complex.inner, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.div_re, Complex.div_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    Complex.normSq_apply]
  norm_num
  ring


-- @@ L6267-6322 verbatim
/-- The derivative of the complex bar derivative in terms of the two Hessian encodings. -/
private theorem complexBarDeriv_fderiv_eq (u : ℂ → ℝ) (hu : ContDiff ℝ ∞ u) (w v : ℂ) :
    fderiv ℝ (complexBarDeriv u) w v =
      ((((chartLaplacian u w : ℝ) : ℂ) * v +
        traceFreeHessian u w * star v) / 4) := by
  let M := fderiv ℝ (fun z ↦ fderiv ℝ u z) w
  have hDu : DifferentiableAt ℝ (fun z ↦ fderiv ℝ u z) w :=
    (hu.fderiv_right (m := 1)
      (show (1 : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr le_top)).differentiable
      one_ne_zero w
  have hM (t : ℂ) :
      fderiv ℝ (fun z ↦ (fderiv ℝ u z t : ℂ)) w v = (M v t : ℂ) := by
    have ht := hDu.hasFDerivAt.clm_apply (hasFDerivAt_const (x := w) t)
    have hcast := Complex.ofRealCLM.hasFDerivAt.comp w ht
    rw [show (fun z ↦ (fderiv ℝ u z t : ℂ)) =
      (Complex.ofRealCLM : ℝ →L[ℝ] ℂ) ∘ fun z ↦ fderiv ℝ u z t by funext z; rfl]
    simpa [M] using congr($hcast.fderiv v)
  have hcomponentDiff (t : ℂ) :
      DifferentiableAt ℝ (fun z ↦ (fderiv ℝ u z t : ℂ)) w := by
    have ht := hDu.hasFDerivAt.clm_apply (hasFDerivAt_const (x := w) t)
    exact (Complex.ofRealCLM.hasFDerivAt.comp w ht).differentiableAt
  rw [show complexBarDeriv u = fun z ↦
    ((fderiv ℝ u z 1 : ℂ) + (fderiv ℝ u z Complex.I : ℂ) * Complex.I) / 2 by rfl]
  simp only [div_eq_mul_inv]
  have hwhole := ((hcomponentDiff 1).hasFDerivAt.add
    ((hcomponentDiff Complex.I).hasFDerivAt.mul_const Complex.I)).mul_const (2 : ℂ)⁻¹
  have hwhole' := hwhole.fderiv
  simp only [Pi.add_apply] at hwhole'
  rw [hwhole']
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply]
  rw [hM, hM]
  · have hsymm (a b : ℂ) : M a b = M b a := by
      dsimp only [M]
      exact hu.contDiffAt.isSymmSndFDerivAt
        (by
          simpa only [minSmoothness_of_isRCLikeNormedField] using
            (show (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) by
              exact WithTop.coe_le_coe.mpr le_top)) a b
    have hv : v = v.re • (1 : ℂ) + v.im • Complex.I := by
      apply Complex.ext <;> simp
    have hMv1 : M v 1 = v.re * M 1 1 + v.im * M 1 Complex.I := by
      nth_rw 1 [hv]
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [hsymm Complex.I 1]
    have hMvI : M v Complex.I =
        v.re * M 1 Complex.I + v.im * M Complex.I Complex.I := by
      nth_rw 1 [hv]
      simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hMv1, hMvI, chartLaplacian, traceFreeHessian_eq_second_fderiv_global]
    dsimp only [M]
    simp only [smul_eq_mul]
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im] <;> ring


-- @@ L6324-6387 verbatim
/-- The complex-coordinate algebra in the reciprocal radius formula. -/
private theorem reciprocal_radius_source_vector (u : ℂ → ℝ) (w v : ℂ) (D : ℝ) (g : ℂ)
    (hDdef : D = ‖w‖ ^ 2 + 10000) (hgdef : g = complexBarDeriv u w) :
        (((u w - 10 ^ 10 : ℝ) : ℂ) * v) +
            (D / 5000 * inner ℝ w v) • g +
            (D ^ 2 / 20000) •
              ((-2 / D) • (inner ℝ w v • g + inner ℝ w g • v -
                  inner ℝ v g • w) +
                ((((chartLaplacian u w : ℝ) : ℂ) * v +
                    traceFreeHessian u w * star v) / 4)) =
          (((u w - 10 ^ 10 : ℝ) : ℂ) * v) +
            (D ^ 2 / 80000) •
              (((chartLaplacian u w : ℝ) : ℂ) * v +
                sphericalTraceFreeHessian 10000 u w * star v) := by
  have hcomplex : inner ℝ w v • g - inner ℝ w g • v +
      inner ℝ v g • w = w * g * star v := by
    apply Complex.ext <;> simp [Complex.inner, add_mul] <;> ring
  rw [hgdef] at hcomplex
  have hD : D ≠ 0 := by
    rw [hDdef]
    positivity
  have hDcast : (((‖w‖ : ℝ) : ℂ) ^ 2) + ((10000 : ℝ) : ℂ) = (D : ℂ) := by
    rw [hDdef]
    norm_cast
  have herrorVector :
      (D / 5000 * inner ℝ w v) • g +
          (D ^ 2 / 20000) •
            ((-2 / D) • (inner ℝ w v • g + inner ℝ w g • v -
              inner ℝ v g • w)) =
        (D / 10000) • (inner ℝ w v • g - inner ℝ w g • v +
          inner ℝ v g • w) := by
    have htwice : D / 5000 = 2 * (D / 10000) := by ring
    have hnegative : (D ^ 2 / 20000) * (-2 / D) = -(D / 10000) := by
      field_simp [hD]
      ring
    simp only [smul_smul, htwice, hnegative]
    module
  calc
    (((u w - 10 ^ 10 : ℝ) : ℂ) * v) +
          (D / 5000 * inner ℝ w v) • g +
          (D ^ 2 / 20000) •
            ((-2 / D) • (inner ℝ w v • g + inner ℝ w g • v -
                inner ℝ v g • w) +
              ((((chartLaplacian u w : ℝ) : ℂ) * v +
                traceFreeHessian u w * star v) / 4)) =
        (((u w - 10 ^ 10 : ℝ) : ℂ) * v) +
          ((D / 5000 * inner ℝ w v) • g +
            (D ^ 2 / 20000) •
              ((-2 / D) • (inner ℝ w v • g + inner ℝ w g • v -
                inner ℝ v g • w))) +
          (D ^ 2 / 20000) •
            ((((chartLaplacian u w : ℝ) : ℂ) * v +
              traceFreeHessian u w * star v) / 4) := by module
    _ = (((u w - 10 ^ 10 : ℝ) : ℂ) * v) +
          (D / 10000) • (inner ℝ w v • g - inner ℝ w g • v +
            inner ℝ v g • w) +
          (D ^ 2 / 20000) •
            ((((chartLaplacian u w : ℝ) : ℂ) * v +
              traceFreeHessian u w * star v) / 4) := by rw [herrorVector]
    _ = _ := by
      rw [hgdef, hcomplex, sphericalTraceFreeHessian]
      rw [hDcast]
      apply Complex.ext <;> simp [-Complex.ofReal_pow] <;>
        field_simp [hD] <;> ring


-- @@ L6389-6539 unexpanded
/-- The second derivative of the reciprocal spherical chart in ambient coordinates. -/
private theorem counterexampleTwoReciprocalSphereChart_second_fderiv (w a b : ℂ) :
    fderiv ℝ (fun z ↦ fderiv ℝ
      (fun y : ℂ ↦ (counterexampleTwoReciprocalSphereChart y : ℝ³)) z) w a b =
        fderiv ℝ (fun y : ℂ ↦ (counterexampleTwoReciprocalSphereChart y : ℝ³)) w
            ((-2 / (‖w‖ ^ 2 + 10000)) •
              (inner ℝ w a • b + inner ℝ w b • a - inner ℝ a b • w)) -
          (40000 / (‖w‖ ^ 2 + 10000) ^ 2 * inner ℝ a b) •
            (counterexampleTwoReciprocalSphereChart w : ℝ³) := by
  let ρ : ℂ → ℝ³ := fun z ↦ (counterexampleTwoReciprocalSphereChart z : ℝ³)
  let dρ : ℂ →L[ℝ] ℝ³ := fderiv ℝ ρ w
  let D : ℝ := ‖w‖ ^ 2 + 10000
  change fderiv ℝ (fun z ↦ fderiv ℝ ρ z) w a b =
    dρ ((-2 / D) • (inner ℝ w a • b + inner ℝ w b • a - inner ℝ a b • w)) -
      (40000 / D ^ 2 * inner ℝ a b) • (ρ w)
  have hρsmooth : ContDiff ℝ ∞ ρ := by
    exact (contMDiff_coe_sphere.comp counterexampleTwoReciprocalSphereChart_contMDiff).contDiff
  have hDρ : DifferentiableAt ℝ (fun z ↦ fderiv ℝ ρ z) w := by
    exact (hρsmooth.fderiv_right (m := 1)
      (show (1 : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr le_top)).differentiable
      one_ne_zero w
  have heval : fderiv ℝ (fun z ↦ fderiv ℝ ρ z b) w a =
      fderiv ℝ (fun z ↦ fderiv ℝ ρ z) w a b := by
    have ht := hDρ.hasFDerivAt.clm_apply (hasFDerivAt_const (x := w) b)
    simpa using congr($ht.fderiv a)
  rw [← heval]
  have heq : (fun z ↦ fderiv ℝ ρ z b) = fun z : ℂ ↦
      (200 / (‖z‖ ^ 2 + 10000)) • (counterexampleTwoTangentEquiv b : ℝ³) -
        (400 * inner ℝ z b / (‖z‖ ^ 2 + 10000) ^ 2) •
          (counterexampleTwoTangentEquiv z : ℝ³) -
        (40000 * inner ℝ z b / (‖z‖ ^ 2 + 10000) ^ 2) •
          (counterexampleNorthPole : ℝ³) := by
    funext z
    exact counterexampleTwoReciprocalSphereChart_fderiv_apply z b
  rw [heq]
  let S : ℂ → ℝ := fun z ↦ ‖z‖ ^ 2 + 10000
  let I : ℂ → ℝ := fun z ↦ inner ℝ z b
  let T : ℂ →L[ℝ] ℝ³ :=
    (ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ.subtypeL.comp
      counterexampleTwoTangentEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hS : HasFDerivAt S (2 • innerSL ℝ w) w := by
    dsimp only [S]
    simpa only [two_smul] using
      (hasStrictFDerivAt_norm_sq w).hasFDerivAt.add_const 10000
  have hI : HasFDerivAt I (innerSL ℝ b) w := by
    dsimp only [I]
    simpa [real_inner_comm] using (innerSL ℝ b).hasFDerivAt
  have hq : HasFDerivAt (fun z ↦ (S z)⁻¹)
      (-((S w) ^ 2)⁻¹ • (2 • innerSL ℝ w)) w := by
    convert (hasDerivAt_inv (by dsimp only [S]; positivity)).hasFDerivAt.comp w hS using 1
    all_goals first
      | with_reducible_and_instances rfl
      | ext x
        simp <;> ring
  have hT : HasFDerivAt
      (fun z : ℂ ↦ (counterexampleTwoTangentEquiv z : ℝ³)) T w := T.hasFDerivAt
  have hR := hI.mul (hq.pow 2)
  have hE := (((hq.const_mul 200).smul_const
    (counterexampleTwoTangentEquiv b : ℝ³)).sub
      ((hR.const_mul 400).smul hT)).sub
        ((hR.const_mul 40000).smul_const (counterexampleNorthPole : ℝ³))
  have hsource :
      (fun z : ℂ ↦
        (200 / (‖z‖ ^ 2 + 10000)) • (counterexampleTwoTangentEquiv b : ℝ³) -
          (400 * inner ℝ z b / (‖z‖ ^ 2 + 10000) ^ 2) •
            (counterexampleTwoTangentEquiv z : ℝ³) -
          (40000 * inner ℝ z b / (‖z‖ ^ 2 + 10000) ^ 2) •
            (counterexampleNorthPole : ℝ³)) =
        fun z ↦
          (200 * (S z)⁻¹) • (counterexampleTwoTangentEquiv b : ℝ³) -
            (400 * (I z * (S z)⁻¹ ^ 2)) •
              (counterexampleTwoTangentEquiv z : ℝ³) -
            (40000 * (I z * (S z)⁻¹ ^ 2)) •
              (counterexampleNorthPole : ℝ³) := by
    funext z
    dsimp only [S, I]
    simp only [div_eq_mul_inv, inv_pow]
    ring
  rw [hsource]
  have hfun :
      (fun z : ℂ ↦
        (200 * (S z)⁻¹) • (counterexampleTwoTangentEquiv b : ℝ³) -
          (400 * (I z * (S z)⁻¹ ^ 2)) • (counterexampleTwoTangentEquiv z : ℝ³) -
          (40000 * (I z * (S z)⁻¹ ^ 2)) • (counterexampleNorthPole : ℝ³)) =
        (((fun z : ℂ ↦
            (200 * (S z)⁻¹) • (counterexampleTwoTangentEquiv b : ℝ³)) -
          ((fun z : ℂ ↦ 400 * (I * fun x ↦ (S x)⁻¹ ^ 2) z) •
            fun z : ℂ ↦ (counterexampleTwoTangentEquiv z : ℝ³))) -
          fun z : ℂ ↦
            (40000 * (I * fun x ↦ (S x)⁻¹ ^ 2) z) •
              (counterexampleNorthPole : ℝ³)) := by
    funext z
    rfl
  rw [hfun, hE.fderiv]
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    innerSL_apply_apply]
  dsimp only [S, I, T]
  dsimp only [ρ]
  rw [counterexampleTwoReciprocalSphereChart_coe]
  dsimp only [D, dρ]
  rw [counterexampleTwoReciprocalSphereChart_fderiv_apply]
  have hTa : ((ℝ ∙ (counterexampleNorthPole : ℝ³))ᗮ.subtypeL.comp
      counterexampleTwoTangentEquiv.toContinuousLinearEquiv.toContinuousLinearMap) a =
        (counterexampleTwoTangentEquiv a : ℝ³) := rfl
  rw [hTa]
  simp only [map_add, map_sub, map_smul, Submodule.coe_add, Submodule.coe_sub,
    Submodule.coe_smul, smul_add, smul_sub, smul_smul, div_eq_mul_inv,
    ← inv_pow, Nat.reduceSub, pow_one, inner_add_right, inner_sub_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq, smul_eq_mul, Pi.mul_apply]
  rw [real_inner_comm b a]
  have hdenOrder : ‖w‖ ^ 2 + 10000 = 10000 + ‖w‖ ^ 2 := by ring
  rw [hdenOrder]
  have hden : 10000 + ‖w‖ ^ 2 ≠ 0 := by positivity
  have hcancel (X Y c k : ℝ) :
      ‖w‖ ^ 2 * X * (10000 + ‖w‖ ^ 2)⁻¹ * Y * k - ‖w‖ ^ 2 * c +
            (X * (10000 + ‖w‖ ^ 2)⁻¹ * Y * (10000 * k) - c * 10000) =
          -(‖w‖ ^ 2 * c) + (X * Y * k - c * 10000) := by
    calc
      _ = ((10000 + ‖w‖ ^ 2) * (10000 + ‖w‖ ^ 2)⁻¹) * X * Y * k -
            ‖w‖ ^ 2 * c - c * 10000 := by ring
      _ = X * Y * k - ‖w‖ ^ 2 * c - c * 10000 := by
        rw [mul_inv_cancel₀ hden]
        ring
      _ = _ := by ring
  have hcancelFour :
      ‖w‖ ^ 2 * inner ℝ w b * (10000 + ‖w‖ ^ 2)⁻¹ * inner ℝ w a * 4 -
            ‖w‖ ^ 2 * inner ℝ b a +
            (inner ℝ w b * (10000 + ‖w‖ ^ 2)⁻¹ * inner ℝ w a * 40000 -
              inner ℝ b a * 10000) =
          -(‖w‖ ^ 2 * inner ℝ b a) +
            (inner ℝ w b * inner ℝ w a * 4 - inner ℝ b a * 10000) := by
    convert hcancel (inner ℝ w b) (inner ℝ w a) (inner ℝ b a) 4 using 1
    all_goals ring
  have hcancelSixteenHundred :
      ‖w‖ ^ 2 * inner ℝ w b * (10000 + ‖w‖ ^ 2)⁻¹ * inner ℝ w a * 1600 -
            ‖w‖ ^ 2 * inner ℝ b a * 400 +
            (inner ℝ w b * (10000 + ‖w‖ ^ 2)⁻¹ * inner ℝ w a * 16000000 -
              inner ℝ b a * 4000000) =
          -(‖w‖ ^ 2 * inner ℝ b a * 400) +
            (inner ℝ w b * inner ℝ w a * 1600 - inner ℝ b a * 4000000) := by
    convert hcancel (inner ℝ w b) (inner ℝ w a) (inner ℝ b a * 400) 1600 using 1
    all_goals ring
  match_scalars <;> field_simp [hden] <;> try ring
  all_goals nlinarith [hcancelFour, hcancelSixteenHundred]

/- The product-rule part of the radius computation is kept separate from the subsequent
coordinate algebra.  Apart from making the two mathematical steps explicit, this prevents
the elaborator from retaining all of the smoothness witnesses while normalizing the final
complex expression. -/

-- @@ L6540-6630 expanded
private theorem counterexampleTwoHomogeneousGradient_reciprocalSphereChart_fderiv (w v : ℂ) :
    let u := counterexampleTwoReciprocal
    let F :=
      SphereSupport.homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension)
    let ρ : ℂ → EuclideanSpace ℝ (Fin 3) := fun z ↦
      (counterexampleTwoReciprocalSphereChart z : EuclideanSpace ℝ (Fin 3))
    let D : ℝ := ‖w‖ ^ 2 + 10000
    let g : ℂ := complexBarDeriv u w
    fderiv ℝ (fun z : ℂ ↦ F (counterexampleTwoReciprocalSphereChart z)) w v =
      (fderiv ℝ u w v) • ρ w + u w • fderiv ℝ ρ w v +
          (4 * D / 20000 * inner ℝ w v) • fderiv ℝ ρ w g +
        (D ^ 2 / 20000) •
          (fderiv ℝ (fun z ↦ fderiv ℝ ρ z) w v g +
            fderiv ℝ ρ w (fderiv ℝ (complexBarDeriv u) w v)) :=
  by
  dsimp only
  let u := counterexampleTwoReciprocal
  let H := SphereSupport.radialExtension counterexampleTwoSphereExtension
  let F := SphereSupport.homogeneousGradient H
  let ρ : ℂ → EuclideanSpace ℝ (Fin 3) := fun z ↦
    (counterexampleTwoReciprocalSphereChart z : EuclideanSpace ℝ (Fin 3))
  let D : ℝ := ‖w‖ ^ 2 + 10000
  let g : ℂ := complexBarDeriv u w
  have hu : ContDiff ℝ ∞ u := counterexampleTwoReciprocal_contDiff
  have hρsmooth : ContDiff ℝ ∞ ρ := by
    exact (contMDiff_coe_sphere.comp counterexampleTwoReciprocalSphereChart_contMDiff).contDiff
  have hρ : Differentiable ℝ ρ := hρsmooth.differentiable (by simp)
  have hFchart :
    (fun z : ℂ ↦ F (counterexampleTwoReciprocalSphereChart z)) = fun z : ℂ ↦
      u z • ρ z + ((‖z‖ ^ 2 + 10000) ^ 2 / 20000) • fderiv ℝ ρ z (complexBarDeriv u z) :=
    by
    funext z
    exact counterexampleTwoHomogeneousGradient_reciprocalSphereChart z
  have hgdiff : DifferentiableAt ℝ (complexBarDeriv u) w :=
    by
    have hDu : DifferentiableAt ℝ (fun z ↦ fderiv ℝ u z) w :=
      (hu.fderiv_right (m := 1)
            (show (1 : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) by
              exact WithTop.coe_le_coe.mpr le_top)).differentiable
        one_ne_zero w
    have hcomponent (t : ℂ) : DifferentiableAt ℝ (fun z ↦ (fderiv ℝ u z t : ℂ)) w :=
      by
      have ht := hDu.hasFDerivAt.clm_apply (hasFDerivAt_const (x := w) t)
      exact (Complex.ofRealCLM.hasFDerivAt.comp w ht).differentiableAt
    change
      DifferentiableAt ℝ
        (fun z ↦ ((fderiv ℝ u z 1 : ℂ) + (fderiv ℝ u z Complex.I : ℂ) * Complex.I) / 2) w
    convert
      (((hcomponent 1).add ((hcomponent Complex.I).mul_const Complex.I)).mul_const (2 : ℂ)⁻¹) using
      1
    all_goals
      first
      | with_reducible_and_instances rfl
      | funext z
        simp only [Pi.add_apply, div_eq_mul_inv]
  have hscale :
    HasFDerivAt (fun z : ℂ ↦ (‖z‖ ^ 2 + 10000) ^ 2 / 20000) (((4 * D / 20000) • innerSL ℝ w)) w :=
    by
    convert
      (((hasStrictFDerivAt_norm_sq w).hasFDerivAt.add_const 10000).pow 2).mul_const
        (20000 : ℝ)⁻¹ using
      1
    all_goals
      ext x
      simp [D, div_eq_mul_inv] <;> ring
  have hDρdiff : DifferentiableAt ℝ (fun z ↦ fderiv ℝ ρ z) w :=
    (hρsmooth.fderiv_right (m := 1)
          (show (1 : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) by
            exact WithTop.coe_le_coe.mpr le_top)).differentiable
      one_ne_zero w
  have hdnApply := hDρdiff.hasFDerivAt.clm_apply hgdiff.hasFDerivAt
  have huDiff : DifferentiableAt ℝ u w := hu.differentiable (by simp) w
  have hρDiff : DifferentiableAt ℝ ρ w := hρ w
  have hscaleDiff := hscale.differentiableAt
  have hdnDiff := hdnApply.differentiableAt
  change
    fderiv ℝ (fun z : ℂ ↦ F (counterexampleTwoReciprocalSphereChart z)) w v =
      (fderiv ℝ u w v) • ρ w + u w • fderiv ℝ ρ w v +
          (4 * D / 20000 * inner ℝ w v) • fderiv ℝ ρ w g +
        (D ^ 2 / 20000) •
          (fderiv ℝ (fun z ↦ fderiv ℝ ρ z) w v g + fderiv ℝ ρ w (fderiv ℝ (complexBarDeriv u) w v))
  rw [hFchart]
  change
    fderiv ℝ
        ((fun z : ℂ ↦ u z • ρ z) + fun z : ℂ ↦
          ((‖z‖ ^ 2 + 10000) ^ 2 / 20000) • fderiv ℝ ρ z (complexBarDeriv u z))
        w v =
      _
  change
    fderiv ℝ
        (fun z : ℂ ↦
          (u • ρ) z +
            (((fun y : ℂ ↦ (‖y‖ ^ 2 + 10000) ^ 2 / 20000) • fun y : ℂ ↦
                fderiv ℝ ρ y (complexBarDeriv u y))
              z))
        w v =
      _
  rw [fderiv_fun_add (huDiff.smul hρDiff) (hscaleDiff.smul hdnDiff)]
  change
    (fderiv ℝ (fun y ↦ u y • ρ y) w +
          fderiv ℝ
            (fun y : ℂ ↦ ((‖y‖ ^ 2 + 10000) ^ 2 / 20000) • fderiv ℝ ρ y (complexBarDeriv u y)) w)
        v =
      _
  rw [fderiv_fun_smul huDiff hρDiff, fderiv_fun_smul hscaleDiff hdnDiff]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [hscale.fderiv, hdnApply.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply, innerSL_apply_apply]
  dsimp only [D, g]
  match_scalars <;> try ring


-- @@ L6632-6706 expanded
/-- Exact radius-tensor formula in the reciprocal chart. The complex-linear coefficient is
the chart Laplacian, while the anti-linear coefficient is the spherical trace-free Hessian. -/
private theorem counterexampleTwoReciprocal_radius_formula (w v : ℂ) :
    let F :=
      SphereSupport.homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension)
    let ρ := fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : EuclideanSpace ℝ (Fin 3))
    let dρ := fderiv ℝ ρ w
    fderiv ℝ (fun z : ℂ ↦ F (counterexampleTwoReciprocalSphereChart z)) w v - (10 ^ 10 : ℝ) • dρ v =
      dρ
        ((((counterexampleTwoReciprocal w - 10 ^ 10 : ℝ) : ℂ) * v) +
          ((‖w‖ ^ 2 + 10000) ^ 2 / 80000 : ℝ) •
            (((chartLaplacian counterexampleTwoReciprocal w : ℝ) : ℂ) * v +
              sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w * star v)) :=
  by
  let u := counterexampleTwoReciprocal
  let H := SphereSupport.radialExtension counterexampleTwoSphereExtension
  let F := SphereSupport.homogeneousGradient H
  let ρ : ℂ → EuclideanSpace ℝ (Fin 3) := fun z ↦
    (counterexampleTwoReciprocalSphereChart z : EuclideanSpace ℝ (Fin 3))
  let dρ : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) := fderiv ℝ ρ w
  let D : ℝ := ‖w‖ ^ 2 + 10000
  let g : ℂ := complexBarDeriv u w
  have hu : ContDiff ℝ ∞ u := counterexampleTwoReciprocal_contDiff
  have hdu : fderiv ℝ u w v = 2 * inner ℝ g v := by exact fderiv_eq_two_inner_complexBarDeriv u w v
  have hdg :
    fderiv ℝ (complexBarDeriv u) w v =
      ((((chartLaplacian u w : ℝ) : ℂ) * v + traceFreeHessian u w * star v) / 4) :=
    by exact complexBarDeriv_fderiv_eq u hu w v
  have hsecond (a b : ℂ) :
    fderiv ℝ (fun z ↦ fderiv ℝ ρ z) w a b =
      dρ ((-2 / D) • (inner ℝ w a • b + inner ℝ w b • a - inner ℝ a b • w)) -
        (40000 / D ^ 2 * inner ℝ a b) • (ρ w) :=
    by simpa only [ρ, dρ, D] using counterexampleTwoReciprocalSphereChart_second_fderiv w a b
  change
    fderiv ℝ (fun z : ℂ ↦ F (counterexampleTwoReciprocalSphereChart z)) w v - (10 ^ 10 : ℝ) • dρ v =
      dρ
        ((((u w - 10 ^ 10 : ℝ) : ℂ) * v) +
          (D ^ 2 / 80000) •
            (((chartLaplacian u w : ℝ) : ℂ) * v + sphericalTraceFreeHessian 10000 u w * star v))
  rw [counterexampleTwoHomogeneousGradient_reciprocalSphereChart_fderiv]
  rw [hdu]
  rw [hsecond v g, hdg]
  have hD : D ≠ 0 := by
    dsimp only [D]
    positivity
  have hsourceVector :
    (((u w - 10 ^ 10 : ℝ) : ℂ) * v) + (D / 5000 * inner ℝ w v) • g +
        (D ^ 2 / 20000) •
          ((-2 / D) • (inner ℝ w v • g + inner ℝ w g • v - inner ℝ v g • w) +
            ((((chartLaplacian u w : ℝ) : ℂ) * v + traceFreeHessian u w * star v) / 4)) =
      (((u w - 10 ^ 10 : ℝ) : ℂ) * v) +
        (D ^ 2 / 80000) •
          (((chartLaplacian u w : ℝ) : ℂ) * v + sphericalTraceFreeHessian 10000 u w * star v) :=
    by exact reciprocal_radius_source_vector u w v D g rfl rfl
  rw [← hsourceVector]
  rw [show (((u w - 10 ^ 10 : ℝ) : ℂ) * v) = (u w - 10 ^ 10 : ℝ) • v by
      exact Complex.real_smul.symm]
  simp only [map_add, map_sub, map_smul, smul_add, smul_sub, smul_smul]
  rw [show ‖w‖ ^ 2 + 10000 = D by rfl]
  have hscaleDerivative : 4 * D / 20000 * inner ℝ w v = D / 5000 * inner ℝ w v := by ring
  rw [hscaleDerivative]
  have hradialScalar : (D ^ 2 / 20000) * (40000 / D ^ 2 * inner ℝ v g) = 2 * inner ℝ g v :=
    by
    rw [real_inner_comm v g]
    field_simp [hD]
    ring
  rw [hradialScalar]
  rw [real_inner_comm g v]
  module


-- @@ L6708-6752 verbatim
/-- Product rule for the complex encoding of the trace-free Hessian. -/
private theorem traceFreeHessian_mul (f g : ℂ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (w : ℂ) :
    traceFreeHessian (fun z ↦ f z * g z) w =
      (f w : ℂ) * traceFreeHessian g w +
        (g w : ℂ) * traceFreeHessian f w +
          8 * complexBarDeriv f w * complexBarDeriv g w := by
  have hf0 : Differentiable ℝ f := hf.differentiable (by simp)
  have hg0 : Differentiable ℝ g := hg.differentiable (by simp)
  have hDf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1)
      (show (1 : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr le_top)).differentiable
      one_ne_zero
  have hDg : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1)
      (show (1 : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr le_top)).differentiable
      one_ne_zero
  have hgradient : fderiv ℝ (fun z ↦ f z * g z) =
      fun z ↦ f z • fderiv ℝ g z + g z • fderiv ℝ f z := by
    funext z
    exact fderiv_fun_mul (hf0 z) (hg0 z)
  have hfun : (fun z ↦ f z • fderiv ℝ g z + g z • fderiv ℝ f z) =
      f • fderiv ℝ g + g • fderiv ℝ f := rfl
  have hsum : fderiv ℝ (f • fderiv ℝ g + g • fderiv ℝ f) w =
      fderiv ℝ (f • fderiv ℝ g) w + fderiv ℝ (g • fderiv ℝ f) w := by
    change fderiv ℝ (fun y ↦ (f • fderiv ℝ g) y + (g • fderiv ℝ f) y) w = _
    exact fderiv_fun_add ((hf0.smul hDg) w) ((hg0.smul hDf) w)
  have hfprod : fderiv ℝ (f • fderiv ℝ g) w =
      f w • fderiv ℝ (fderiv ℝ g) w + (fderiv ℝ f w).smulRight (fderiv ℝ g w) := by
    change fderiv ℝ (fun y ↦ f y • fderiv ℝ g y) w = _
    exact fderiv_fun_smul (hf0 w) (hDg w)
  have hgprod : fderiv ℝ (g • fderiv ℝ f) w =
      g w • fderiv ℝ (fderiv ℝ f) w + (fderiv ℝ g w).smulRight (fderiv ℝ f w) := by
    change fderiv ℝ (fun y ↦ g y • fderiv ℝ f y) w = _
    exact fderiv_fun_smul (hg0 w) (hDf w)
  rw [traceFreeHessian_eq_second_fderiv, hgradient, hfun, hsum,
    hfprod, hgprod]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rw [traceFreeHessian_eq_second_fderiv, traceFreeHessian_eq_second_fderiv,
    complexBarDeriv, complexBarDeriv]
  push_cast
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring


-- @@ L6754-6796 verbatim
/-- Product rule for the Euclidean chart Laplacian. -/
private theorem chartLaplacian_mul (f g : ℂ → ℝ)
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (w : ℂ) :
    chartLaplacian (fun z ↦ f z * g z) w =
      f w * chartLaplacian g w + g w * chartLaplacian f w +
        2 * (fderiv ℝ f w 1 * fderiv ℝ g w 1 +
          fderiv ℝ f w Complex.I * fderiv ℝ g w Complex.I) := by
  have hf0 : Differentiable ℝ f := hf.differentiable (by simp)
  have hg0 : Differentiable ℝ g := hg.differentiable (by simp)
  have hDf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1)
      (show (1 : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr le_top)).differentiable
      one_ne_zero
  have hDg : Differentiable ℝ (fderiv ℝ g) :=
    (hg.fderiv_right (m := 1)
      (show (1 : WithTop ℕ∞) + 1 ≤ (∞ : WithTop ℕ∞) by
        exact WithTop.coe_le_coe.mpr le_top)).differentiable
      one_ne_zero
  have hgradient : fderiv ℝ (fun z ↦ f z * g z) =
      fun z ↦ f z • fderiv ℝ g z + g z • fderiv ℝ f z := by
    funext z
    exact fderiv_fun_mul (hf0 z) (hg0 z)
  have hfun : (fun z ↦ f z • fderiv ℝ g z + g z • fderiv ℝ f z) =
      f • fderiv ℝ g + g • fderiv ℝ f := rfl
  have hsum : fderiv ℝ (f • fderiv ℝ g + g • fderiv ℝ f) w =
      fderiv ℝ (f • fderiv ℝ g) w + fderiv ℝ (g • fderiv ℝ f) w := by
    change fderiv ℝ (fun y ↦ (f • fderiv ℝ g) y + (g • fderiv ℝ f) y) w = _
    exact fderiv_fun_add ((hf0.smul hDg) w) ((hg0.smul hDf) w)
  have hfprod : fderiv ℝ (f • fderiv ℝ g) w =
      f w • fderiv ℝ (fderiv ℝ g) w + (fderiv ℝ f w).smulRight (fderiv ℝ g w) := by
    change fderiv ℝ (fun y ↦ f y • fderiv ℝ g y) w = _
    exact fderiv_fun_smul (hf0 w) (hDg w)
  have hgprod : fderiv ℝ (g • fderiv ℝ f) w =
      g w • fderiv ℝ (fderiv ℝ f) w + (fderiv ℝ g w).smulRight (fderiv ℝ f w) := by
    change fderiv ℝ (fun y ↦ g y • fderiv ℝ f y) w = _
    exact fderiv_fun_smul (hg0 w) (hDf w)
  rw [chartLaplacian, hgradient, hfun, hsum,
    hfprod, hgprod]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  rw [chartLaplacian, chartLaplacian]
  ring


-- @@ L6798-6807 verbatim
/-- Product rule for the first anti-holomorphic derivative. -/
private theorem complexBarDeriv_mul (f g : ℂ → ℝ)
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (w : ℂ) :
    complexBarDeriv (fun z ↦ f z * g z) w =
      (f w : ℂ) * complexBarDeriv g w + (g w : ℂ) * complexBarDeriv f w := by
  rw [complexBarDeriv, fderiv_fun_mul (hf w) (hg w)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [complexBarDeriv, complexBarDeriv]
  push_cast
  ring


-- @@ L6809-6818 verbatim
/-- Adding a constant does not change the first anti-holomorphic derivative. -/
private theorem complexBarDeriv_const_add (c : ℝ) (f : ℂ → ℝ)
    (hf : Differentiable ℝ f) (w : ℂ) :
    complexBarDeriv (fun z ↦ c + f z) w = complexBarDeriv f w := by
  have hsum := (hasFDerivAt_const (x := w) c).add (hf w).hasFDerivAt
  rw [complexBarDeriv]
  change (↑((fderiv ℝ (((fun _ : ℂ ↦ c) + f)) w) 1) +
    ↑((fderiv ℝ (((fun _ : ℂ ↦ c) + f)) w) Complex.I) * Complex.I) / 2 = _
  rw [hsum.fderiv]
  simp [complexBarDeriv]


-- @@ L6820-6831 verbatim
/-- Adding a constant does not change the trace-free Hessian. -/
private theorem traceFreeHessian_const_add (c : ℝ) (f : ℂ → ℝ)
    (hf : ContDiff ℝ ∞ f) (w : ℂ) :
    traceFreeHessian (fun z ↦ c + f z) w = traceFreeHessian f w := by
  have hgradient : fderiv ℝ (fun z ↦ c + f z) = fderiv ℝ f := by
    funext z
    change fderiv ℝ (((fun _ : ℂ ↦ c) + f)) z = _
    rw [((hasFDerivAt_const (x := z) c).add
      (hf.differentiable (by simp) z).hasFDerivAt).fderiv]
    simp
  rw [traceFreeHessian_eq_second_fderiv, hgradient,
    traceFreeHessian_eq_second_fderiv]


-- @@ L6833-6844 verbatim
/-- Adding a constant does not change the chart Laplacian. -/
private theorem chartLaplacian_const_add (c : ℝ) (f : ℂ → ℝ)
    (hf : ContDiff ℝ ∞ f) (w : ℂ) :
    chartLaplacian (fun z ↦ c + f z) w = chartLaplacian f w := by
  have hgradient : fderiv ℝ (fun z ↦ c + f z) = fderiv ℝ f := by
    funext z
    change fderiv ℝ (((fun _ : ℂ ↦ c) + f)) z = _
    rw [((hasFDerivAt_const (x := z) c).add
      (hf.differentiable (by simp) z).hasFDerivAt).fderiv]
    simp
  rw [chartLaplacian, hgradient]
  rfl


-- @@ L6846-6865 verbatim
/-- The first anti-holomorphic derivative of a radial scalar function. -/
private theorem complexBarDeriv_comp_norm_sq (β : ℝ → ℝ) (w : ℂ)
    (hβ : DifferentiableAt ℝ β (‖w‖ ^ 2)) :
    complexBarDeriv (fun z : ℂ ↦ β (‖z‖ ^ 2)) w =
      ((deriv β (‖w‖ ^ 2) : ℝ) : ℂ) * w := by
  have hre : HasFDerivAt (fun z : ℂ ↦ z.re) Complex.reCLM w := Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun z : ℂ ↦ z.im) Complex.imCLM w := Complex.imCLM.hasFDerivAt
  have hs : HasFDerivAt (fun z : ℂ ↦ ‖z‖ ^ 2)
      ((2 * w.re) • Complex.reCLM + (2 * w.im) • Complex.imCLM) w := by
    convert! (hre.pow 2).add (him.pow 2) using 1
    · funext z
      simpa only [Pi.add_apply, Complex.normSq_apply, pow_two] using Complex.sq_norm z
    · ext v
      simp
  have hcomp := hβ.hasDerivAt.hasFDerivAt.comp w hs
  rw [complexBarDeriv]
  change (↑((fderiv ℝ (β ∘ fun z : ℂ ↦ ‖z‖ ^ 2) w) 1) +
    ↑((fderiv ℝ (β ∘ fun z : ℂ ↦ ‖z‖ ^ 2) w) Complex.I) * Complex.I) / 2 = _
  rw [hcomp.fderiv]
  apply Complex.ext <;> simp <;> ring


-- @@ L6867-6921 verbatim
/-- The trace-free Hessian of a radial scalar function. -/
private theorem traceFreeHessian_comp_norm_sq (β : ℝ → ℝ) (w : ℂ)
    (hβ : ContDiffAt ℝ 2 β (‖w‖ ^ 2)) :
    traceFreeHessian (fun z : ℂ ↦ β (‖z‖ ^ 2)) w =
      4 * ((deriv (fun x ↦ deriv β x) (‖w‖ ^ 2) : ℝ) : ℂ) * w ^ 2 := by
  have hs (z : ℂ) : HasFDerivAt (fun y : ℂ ↦ ‖y‖ ^ 2)
      ((2 * z.re) • Complex.reCLM + (2 * z.im) • Complex.imCLM) z := by
    have hre : HasFDerivAt (fun y : ℂ ↦ y.re) Complex.reCLM z :=
      Complex.reCLM.hasFDerivAt
    have him : HasFDerivAt (fun y : ℂ ↦ y.im) Complex.imCLM z :=
      Complex.imCLM.hasFDerivAt
    convert! (hre.pow 2).add (him.pow 2) using 1
    · funext y
      simpa only [Pi.add_apply, Complex.normSq_apply, pow_two] using Complex.sq_norm y
    · ext v
      simp
  have hβnear : ∀ᶠ z in nhds w, ContDiffAt ℝ 2 β (‖z‖ ^ 2) :=
    (contDiff_norm_sq ℝ : ContDiff ℝ 2 (fun z : ℂ ↦ ‖z‖ ^ 2)).continuous.continuousAt.tendsto
      (hβ.eventually (by norm_num : (2 : WithTop ℕ∞) ≠ ∞))
  have hgradient : fderiv ℝ (fun z : ℂ ↦ β (‖z‖ ^ 2)) =ᶠ[nhds w] fun z ↦
      deriv β (‖z‖ ^ 2) •
        ((2 * z.re) • Complex.reCLM + (2 * z.im) • Complex.imCLM) := by
    filter_upwards [hβnear] with z hz
    have hcomp :=
      (hz.differentiableAt (by norm_num)).hasDerivAt.hasFDerivAt.comp z (hs z)
    convert! hcomp.fderiv using 1
    ext a
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hderivβ : ContDiffAt ℝ 1 (fun x ↦ deriv β x) (‖w‖ ^ 2) := by
    convert! ((hβ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const) using 1
  have hscalar : HasFDerivAt (fun z : ℂ ↦ deriv β (‖z‖ ^ 2))
      (deriv (fun x ↦ deriv β x) (‖w‖ ^ 2) •
        ((2 * w.re) • Complex.reCLM + (2 * w.im) • Complex.imCLM)) w := by
    have hcomp :=
      (hderivβ.differentiableAt (by norm_num)).hasDerivAt.hasFDerivAt.comp w (hs w)
    convert! hcomp using 1
    ext a
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hre : HasFDerivAt (fun z : ℂ ↦ z.re) Complex.reCLM w := Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun z : ℂ ↦ z.im) Complex.imCLM w := Complex.imCLM.hasFDerivAt
  have hmatrix := ((hre.const_mul 2).smul_const Complex.reCLM).add
    ((him.const_mul 2).smul_const Complex.imCLM)
  have hsecond := hscalar.smul hmatrix
  change HasFDerivAt (fun z : ℂ ↦ deriv β (‖z‖ ^ 2) •
    ((2 * z.re) • Complex.reCLM + (2 * z.im) • Complex.imCLM)) _ w at hsecond
  rw [traceFreeHessian_eq_second_fderiv, hgradient.fderiv_eq, hsecond.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, Pi.add_apply, smul_eq_mul,
    Complex.reCLM_apply, Complex.imCLM_apply]
  push_cast
  apply Complex.ext <;> simp [pow_two, Complex.mul_re, Complex.mul_im] <;> ring


-- @@ L6923-6979 verbatim
/-- The Euclidean chart Laplacian of a radial scalar function. -/
private theorem chartLaplacian_comp_norm_sq (β : ℝ → ℝ) (w : ℂ)
    (hβ : ContDiffAt ℝ 2 β (‖w‖ ^ 2)) :
    chartLaplacian (fun z : ℂ ↦ β (‖z‖ ^ 2)) w =
      4 * (deriv β (‖w‖ ^ 2) + ‖w‖ ^ 2 *
        deriv (fun x ↦ deriv β x) (‖w‖ ^ 2)) := by
  have hs (z : ℂ) : HasFDerivAt (fun y : ℂ ↦ ‖y‖ ^ 2)
      ((2 * z.re) • Complex.reCLM + (2 * z.im) • Complex.imCLM) z := by
    have hre : HasFDerivAt (fun y : ℂ ↦ y.re) Complex.reCLM z :=
      Complex.reCLM.hasFDerivAt
    have him : HasFDerivAt (fun y : ℂ ↦ y.im) Complex.imCLM z :=
      Complex.imCLM.hasFDerivAt
    convert! (hre.pow 2).add (him.pow 2) using 1
    · funext y
      simpa only [Pi.add_apply, Complex.normSq_apply, pow_two] using Complex.sq_norm y
    · ext v
      simp
  have hβnear : ∀ᶠ z in nhds w, ContDiffAt ℝ 2 β (‖z‖ ^ 2) :=
    (contDiff_norm_sq ℝ : ContDiff ℝ 2 (fun z : ℂ ↦ ‖z‖ ^ 2)).continuous.continuousAt.tendsto
      (hβ.eventually (by norm_num : (2 : WithTop ℕ∞) ≠ ∞))
  have hgradient : fderiv ℝ (fun z : ℂ ↦ β (‖z‖ ^ 2)) =ᶠ[nhds w] fun z ↦
      deriv β (‖z‖ ^ 2) •
        ((2 * z.re) • Complex.reCLM + (2 * z.im) • Complex.imCLM) := by
    filter_upwards [hβnear] with z hz
    have hcomp :=
      (hz.differentiableAt (by norm_num)).hasDerivAt.hasFDerivAt.comp z (hs z)
    convert! hcomp.fderiv using 1
    ext a
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hderivβ : ContDiffAt ℝ 1 (fun x ↦ deriv β x) (‖w‖ ^ 2) := by
    convert! ((hβ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const) using 1
  have hscalar : HasFDerivAt (fun z : ℂ ↦ deriv β (‖z‖ ^ 2))
      (deriv (fun x ↦ deriv β x) (‖w‖ ^ 2) •
        ((2 * w.re) • Complex.reCLM + (2 * w.im) • Complex.imCLM)) w := by
    have hcomp :=
      (hderivβ.differentiableAt (by norm_num)).hasDerivAt.hasFDerivAt.comp w (hs w)
    convert! hcomp using 1
    ext a
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    ring
  have hre : HasFDerivAt (fun z : ℂ ↦ z.re) Complex.reCLM w := Complex.reCLM.hasFDerivAt
  have him : HasFDerivAt (fun z : ℂ ↦ z.im) Complex.imCLM w := Complex.imCLM.hasFDerivAt
  have hmatrix := ((hre.const_mul 2).smul_const Complex.reCLM).add
    ((him.const_mul 2).smul_const Complex.imCLM)
  have hsecond := hscalar.smul hmatrix
  change HasFDerivAt (fun z : ℂ ↦ deriv β (‖z‖ ^ 2) •
    ((2 * z.re) • Complex.reCLM + (2 * z.im) • Complex.imCLM)) _ w at hsecond
  rw [chartLaplacian, hgradient.fderiv_eq, hsecond.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, Pi.add_apply, smul_eq_mul,
    Complex.reCLM_apply, Complex.imCLM_apply]
  rw [Complex.sq_norm, Complex.normSq_apply]
  norm_num
  ring


-- @@ L6981-6997 verbatim
/-- Logarithmic derivative of the one-variable reciprocal damping factor. -/
private theorem counterexampleTwoReciprocalRadialDamping_deriv {s : ℝ} (hs : -10000 < s) :
    deriv (fun x : ℝ ↦ 10000 / (x + 10000) *
      Real.exp (-counterexampleTwoReciprocalExponent x)) s =
        -(10000 / (s + 10000) * Real.exp (-counterexampleTwoReciprocalExponent s)) *
          (1 / (s + 10000) + deriv counterexampleTwoReciprocalExponent s) := by
  have hden : s + 10000 ≠ 0 := by linarith
  have hfrac := (hasDerivAt_const s 10000).div
    ((hasDerivAt_id s).add_const 10000) hden
  have hψ := (counterexampleTwoReciprocalExponent_contDiff.differentiable (by simp) s).hasDerivAt
  have hraw := hfrac.mul hψ.neg.exp
  change deriv ((((fun _ : ℝ ↦ (10000 : ℝ)) / fun x ↦ id x + 10000) *
    fun x ↦ Real.exp ((-counterexampleTwoReciprocalExponent) x))) s = _
  rw [hraw.deriv]
  dsimp only [id_eq, Pi.div_apply, Pi.mul_apply, Pi.neg_apply]
  field_simp [hden]
  ring


-- @@ L6999-7007 verbatim
/-- The scalar reciprocal damping factor is smooth wherever its rational denominator is
nonzero. -/
private theorem counterexampleTwoReciprocalRadialDamping_contDiffAt
    {s : ℝ} (hs : -10000 < s) {n : ℕ∞} :
    ContDiffAt ℝ n (fun x : ℝ ↦ 10000 / (x + 10000) *
      Real.exp (-counterexampleTwoReciprocalExponent x)) s := by
  have hden : s + 10000 ≠ 0 := by linarith
  exact (contDiffAt_const.div (contDiffAt_id.add contDiffAt_const) hden).mul
    (counterexampleTwoReciprocalExponent_contDiff.contDiffAt.neg.exp.of_le (by simp))


-- @@ L7009-7051 verbatim
/-- Second derivative of the one-variable reciprocal damping factor. -/
private theorem counterexampleTwoReciprocalRadialDamping_second_deriv
    {s : ℝ} (hs : -10000 < s) :
    deriv (fun y ↦ deriv (fun x : ℝ ↦ 10000 / (x + 10000) *
      Real.exp (-counterexampleTwoReciprocalExponent x)) y) s =
        (10000 / (s + 10000) * Real.exp (-counterexampleTwoReciprocalExponent s)) *
          ((1 / (s + 10000) + deriv counterexampleTwoReciprocalExponent s) ^ 2 +
            1 / (s + 10000) ^ 2 -
              deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) s) := by
  let β : ℝ → ℝ := fun x ↦ 10000 / (x + 10000) *
    Real.exp (-counterexampleTwoReciprocalExponent x)
  have hden : s + 10000 ≠ 0 := by linarith
  have hfrac := (hasDerivAt_const s 10000).div
    ((hasDerivAt_id s).add_const 10000) hden
  have hψ := (counterexampleTwoReciprocalExponent_contDiff.differentiable (by simp) s).hasDerivAt
  have hβ := hfrac.mul hψ.neg.exp
  have hDψ : ContDiff ℝ ∞ (fun x ↦ deriv counterexampleTwoReciprocalExponent x) := by
    simpa only [fderiv_apply_one_eq_deriv] using
      ((counterexampleTwoReciprocalExponent_contDiff.fderiv_right (m := ∞) (by simp)).clm_apply
        (contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ ↦ (1 : ℝ))))
  have hψ₂ := (hDψ.differentiable (by simp) s).hasDerivAt
  have hq := (((hasDerivAt_id s).add_const 10000).inv hden).add hψ₂
  have hright := (hβ.mul hq).neg
  have hrightFun : (fun y ↦ -β y * (1 / (y + 10000) +
      deriv counterexampleTwoReciprocalExponent y)) =
      -((((fun _ : ℝ ↦ (10000 : ℝ)) / fun x ↦ id x + 10000) *
          fun x ↦ Real.exp ((-counterexampleTwoReciprocalExponent) x)) *
        ((fun x ↦ id x + 10000)⁻¹ +
          fun x ↦ deriv counterexampleTwoReciprocalExponent x)) := by
    funext y
    dsimp only [β, id_eq, Pi.div_apply, Pi.mul_apply, Pi.neg_apply, Pi.add_apply,
      Pi.inv_apply]
    ring
  have heq : (fun y ↦ deriv (fun x : ℝ ↦ 10000 / (x + 10000) *
      Real.exp (-counterexampleTwoReciprocalExponent x)) y) =ᶠ[nhds s]
      fun y ↦ -β y * (1 / (y + 10000) + deriv counterexampleTwoReciprocalExponent y) := by
    filter_upwards [Ioi_mem_nhds hs] with y hy
    exact counterexampleTwoReciprocalRadialDamping_deriv hy
  rw [heq.deriv_eq]
  rw [hrightFun, hright.deriv]
  simp only [id_eq, Pi.div_apply, Pi.mul_apply, Pi.neg_apply, Pi.add_apply, Pi.inv_apply]
  field_simp [hden]
  ring


-- @@ L7053-7112 verbatim
/-- The stereographic trace-free Hessian of the reciprocal representative factors into its
positive damping coefficient and the explicit seed-plus-error model. -/
private theorem sphericalTraceFreeHessian_counterexampleTwoReciprocal (w : ℂ) :
    let p := deriv counterexampleTwoReciprocalExponent (‖w‖ ^ 2)
    let p' := deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) (‖w‖ ^ 2)
    sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w =
      counterexampleTwoReciprocalDamping w *
        (traceFreeHessian counterexampleSeed w -
          8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w +
          4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w) := by
  let s := ‖w‖ ^ 2
  let β : ℝ → ℝ := fun x ↦ 10000 / (x + 10000) *
    Real.exp (-counterexampleTwoReciprocalExponent x)
  have hs0 : 0 ≤ s := by
    dsimp only [s]
    positivity
  have hs : -10000 < s := by linarith
  have hβ : ContDiffAt ℝ 2 β s :=
    counterexampleTwoReciprocalRadialDamping_contDiffAt hs
  have hB : counterexampleTwoReciprocalDamping = fun z : ℂ ↦ β (‖z‖ ^ 2) := by
    rfl
  have hBbar : complexBarDeriv counterexampleTwoReciprocalDamping w =
      ((deriv β s : ℝ) : ℂ) * w := by
    rw [hB]
    exact complexBarDeriv_comp_norm_sq β w (hβ.differentiableAt (by norm_num))
  have hBtf : traceFreeHessian counterexampleTwoReciprocalDamping w =
      4 * ((deriv (fun x ↦ deriv β x) s : ℝ) : ℂ) * w ^ 2 := by
    rw [hB]
    exact traceFreeHessian_comp_norm_sq β w hβ
  have hβ' : deriv β s = -β s *
      (1 / (s + 10000) + deriv counterexampleTwoReciprocalExponent s) :=
    counterexampleTwoReciprocalRadialDamping_deriv hs
  have hβ'' : deriv (fun x ↦ deriv β x) s = β s *
      ((1 / (s + 10000) + deriv counterexampleTwoReciprocalExponent s) ^ 2 +
        1 / (s + 10000) ^ 2 -
          deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) s) :=
    counterexampleTwoReciprocalRadialDamping_second_deriv hs
  have hprodSmooth : ContDiff ℝ ∞
      (fun z ↦ counterexampleTwoReciprocalDamping z * counterexampleSeed z) :=
    counterexampleTwoReciprocalDamping_contDiff.mul counterexampleSeed_contDiff
  have hprodDiff : Differentiable ℝ
      (fun z ↦ counterexampleTwoReciprocalDamping z * counterexampleSeed z) :=
    hprodSmooth.differentiable (by simp)
  change sphericalTraceFreeHessian 10000
      (fun z ↦ 10 ^ 10 + counterexampleTwoReciprocalDamping z * counterexampleSeed z) w = _
  rw [sphericalTraceFreeHessian,
    traceFreeHessian_const_add _ _ hprodSmooth,
    complexBarDeriv_const_add _ _ hprodDiff,
    traceFreeHessian_mul _ _ counterexampleTwoReciprocalDamping_contDiff
      counterexampleSeed_contDiff,
    complexBarDeriv_mul _ _
      (counterexampleTwoReciprocalDamping_contDiff.differentiable (by simp))
      (counterexampleSeed_contDiff.differentiable (by simp)),
    hBtf, hBbar, hβ', hβ'']
  rw [hB]
  dsimp only [s]
  simp only [div_eq_mul_inv, Complex.ofReal_add, Complex.ofReal_sub,
    Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_neg,
    Complex.ofReal_inv, one_mul, ← inv_pow]
  ring_nf


-- @@ L7114-7147 expanded
/-- In a conformal complex chart, a scalar shape operator forces the anti-linear coefficient
of the radius tensor to vanish. This is the algebraic core of the umbilic criterion. -/
private theorem antiLinearCoefficient_eq_zero_of_umbilic (dρ dF : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (hdρ : Function.Injective dρ) (C r : ℝ) (A L Q : ℂ) (hr : r ≠ 0)
    (hformula : ∀ v : ℂ, dF v - C • dρ v = dρ (A * v + r • (L * v + Q * star v)))
    (humbilic : ∃ c : ℝ, dρ = c • dF) : Q = 0 :=
  by
  obtain ⟨c, hc⟩ := humbilic
  have hc0 : c ≠ 0 := by
    intro hc0
    subst c
    have hc' : dρ = 0 := hc.trans (zero_smul ℝ dF)
    exact one_ne_zero (hdρ (by rw [hc']; rfl))
  have hdF : dF = c⁻¹ • dρ := by rw [hc, inv_smul_smul₀ hc0]
  have hcoordinate (v : ℂ) : ((c⁻¹ - C : ℝ) : ℂ) * v = A * v + r • (L * v + Q * star v) :=
    by
    apply hdρ
    rw [← hformula v, hdF]
    change dρ ((c⁻¹ - C) • v) = c⁻¹ • dρ v - C • dρ v
    rw [map_smul, sub_smul]
  have h1 := hcoordinate 1
  have hI := hcoordinate Complex.I
  have : (2 * r : ℂ) * Complex.I * Q = 0 :=
    by
    have halgebra :
      (2 * r : ℂ) * Complex.I * Q =
        -((A * Complex.I + r • (L * Complex.I + Q * star Complex.I)) -
            Complex.I * (A * 1 + r • (L * 1 + Q * star (1 : ℂ)))) :=
      by apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
    rw [halgebra, ← hI, ← h1]
    ring
  exact
    (mul_eq_zero.mp this).resolve_left <|
      mul_ne_zero (by exact_mod_cast (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) hr)) Complex.I_ne_zero


-- @@ L7149-7177 expanded
/-- Norm estimate obtained from the conformal chart radius formula. -/
private theorem norm_radiusError_le_of_conformal_formula (dρ dF : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3))
    (C k r : ℝ) (A L Q : ℂ) (hk : 0 ≤ k) (hr : 0 ≤ r) (hscale : ∀ v : ℂ, ‖dρ v‖ = k * ‖v‖)
    (hformula : ∀ v : ℂ, dF v - C • dρ v = dρ (A * v + r • (L * v + Q * star v))) :
    ∀ v : ℂ, ‖dF v - C • dρ v‖ ≤ (‖A‖ + r * (‖L‖ + ‖Q‖)) * ‖dρ v‖ :=
  by
  intro v
  rw [hformula, hscale]
  calc
    k * ‖A * v + r • (L * v + Q * star v)‖ ≤ k * ((‖A‖ + r * (‖L‖ + ‖Q‖)) * ‖v‖) :=
      by
      gcongr
      calc
        ‖A * v + r • (L * v + Q * star v)‖ ≤ ‖A * v‖ + ‖r • (L * v + Q * star v)‖ := norm_add_le _ _
        _ = ‖A‖ * ‖v‖ + |r| * ‖L * v + Q * star v‖ := by rw [norm_mul, norm_smul, Real.norm_eq_abs]
        _ ≤ ‖A‖ * ‖v‖ + r * (‖L * v‖ + ‖Q * star v‖) :=
          by
          rw [abs_of_nonneg hr]
          gcongr
          exact norm_add_le _ _
        _ = (‖A‖ + r * (‖L‖ + ‖Q‖)) * ‖v‖ :=
          by
          rw [norm_mul, norm_mul, norm_star]
          ring
    _ = (‖A‖ + r * (‖L‖ + ‖Q‖)) * (k * ‖v‖) := by ring
    _ = (‖A‖ + r * (‖L‖ + ‖Q‖)) * ‖dρ v‖ := by rw [hscale]


-- @@ L7179-7250 verbatim
/-- The seed's trace-free Hessian cannot be cancelled by error terms having the two bounds
which arise from differentiating the reciprocal damping factor. -/
private theorem seedTraceFreeHessian_perturbation_ne_zero (w : ℂ) (p p' : ℝ)
    (hp : ‖w‖ * |p| ≤ 1 / 100)
    (hpp : ‖w‖ ^ 2 * (p ^ 2 + |p'|) ≤ 1 / 1000) :
    traceFreeHessian counterexampleSeed w -
        8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w +
      4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w ≠ 0 := by
  have hbar : ‖complexBarDeriv counterexampleSeed w‖ ≤ 129 / 80 := by
    have hnorm : ‖complexBarDeriv counterexampleSeed w‖ =
        ‖((fderiv ℝ counterexampleSeed w 1 : ℂ) -
          (fderiv ℝ counterexampleSeed w Complex.I : ℂ) * Complex.I) / 2‖ := by
      rw [complexBarDeriv, show
        ((fderiv ℝ counterexampleSeed w 1 : ℂ) +
            (fderiv ℝ counterexampleSeed w Complex.I : ℂ) * Complex.I) / 2 =
          star (((fderiv ℝ counterexampleSeed w 1 : ℂ) -
            (fderiv ℝ counterexampleSeed w Complex.I : ℂ) * Complex.I) / 2) by
          simp,
        norm_star]
    rw [hnorm]
    exact counterexampleSeed_wirtinger_norm_upper w
  have hseed : |counterexampleSeed w| ≤ 253 / 160 := counterexampleSeed_abs_le w
  have hpabs : |p ^ 2 - p'| ≤ p ^ 2 + |p'| := by
    calc
      |p ^ 2 - p'| ≤ |p ^ 2| + |p'| := abs_sub _ _
      _ = p ^ 2 + |p'| := by rw [abs_of_nonneg (sq_nonneg p)]
  have hpperr : ‖w‖ ^ 2 * |p ^ 2 - p'| ≤ 1 / 1000 :=
    (mul_le_mul_of_nonneg_left hpabs (sq_nonneg ‖w‖)).trans hpp
  have hfirst : ‖8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w‖ ≤
      129 / 1000 := by
    calc
      ‖8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w‖ =
          8 * (‖w‖ * |p|) * ‖complexBarDeriv counterexampleSeed w‖ := by
        simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
        ring
      _ ≤ 8 * (1 / 100) * (129 / 80) := by gcongr
      _ = 129 / 1000 := by norm_num
  have hsecond :
      ‖4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ ≤
        253 / 40000 := by
    calc
      ‖4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ =
          4 * (‖w‖ ^ 2 * |p ^ 2 - p'|) * |counterexampleSeed w| := by
        simp only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real,
          Real.norm_eq_abs]
        ring
      _ ≤ 4 * (1 / 1000) * (253 / 160) := by gcongr
      _ = 253 / 40000 := by norm_num
  have herror :
      ‖-(8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w) +
          4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ ≤
        5413 / 40000 := by
    calc
      _ ≤ ‖8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w‖ +
          ‖4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ := by
        simpa only [norm_neg] using norm_add_le
          (-(8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w))
          (4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w)
      _ ≤ 129 / 1000 + 253 / 40000 := add_le_add hfirst hsecond
      _ = 5413 / 40000 := by norm_num
  intro hzero
  have hsum : traceFreeHessian counterexampleSeed w +
      (-(8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w) +
        4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w) = 0 := by
    simpa only [sub_eq_add_neg, add_assoc] using hzero
  have hnormeq : ‖traceFreeHessian counterexampleSeed w‖ =
      ‖-(8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w) +
        4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ := by
    rw [eq_neg_of_add_eq_zero_left hsum, norm_neg]
  have hlower := counterexampleSeed_traceFreeHessian_norm_lower w
  rw [hnormeq] at hlower
  linarith


-- @@ L7252-7311 verbatim
/-- A deliberately loose upper bound for the same reciprocal trace-free model. -/
private theorem seedTraceFreeHessian_perturbation_norm_upper (w : ℂ) (p p' : ℝ)
    (hp : ‖w‖ * |p| ≤ 1 / 100)
    (hpp : ‖w‖ ^ 2 * (p ^ 2 + |p'|) ≤ 1 / 1000) :
    ‖traceFreeHessian counterexampleSeed w -
        8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w +
      4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ ≤ 20 := by
  have hbar : ‖complexBarDeriv counterexampleSeed w‖ ≤ 129 / 80 := by
    have hnorm : ‖complexBarDeriv counterexampleSeed w‖ =
        ‖((fderiv ℝ counterexampleSeed w 1 : ℂ) -
          (fderiv ℝ counterexampleSeed w Complex.I : ℂ) * Complex.I) / 2‖ := by
      rw [complexBarDeriv, show
        ((fderiv ℝ counterexampleSeed w 1 : ℂ) +
            (fderiv ℝ counterexampleSeed w Complex.I : ℂ) * Complex.I) / 2 =
          star (((fderiv ℝ counterexampleSeed w 1 : ℂ) -
            (fderiv ℝ counterexampleSeed w Complex.I : ℂ) * Complex.I) / 2) by
          simp,
        norm_star]
    rw [hnorm]
    exact counterexampleSeed_wirtinger_norm_upper w
  have hpabs : |p ^ 2 - p'| ≤ p ^ 2 + |p'| := by
    exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (sq_nonneg p)])
  have hpperr : ‖w‖ ^ 2 * |p ^ 2 - p'| ≤ 1 / 1000 :=
    (mul_le_mul_of_nonneg_left hpabs (sq_nonneg ‖w‖)).trans hpp
  have hfirst : ‖8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w‖ ≤
      129 / 1000 := by
    calc
      _ = 8 * (‖w‖ * |p|) * ‖complexBarDeriv counterexampleSeed w‖ := by
        simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs]
        ring
      _ ≤ 8 * (1 / 100) * (129 / 80) := by gcongr
      _ = 129 / 1000 := by norm_num
  have hsecond :
      ‖4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ ≤
        253 / 40000 := by
    calc
      _ = 4 * (‖w‖ ^ 2 * |p ^ 2 - p'|) * |counterexampleSeed w| := by
        simp only [norm_mul, norm_pow, Complex.norm_ofNat, Complex.norm_real,
          Real.norm_eq_abs]
        ring
      _ ≤ 4 * (1 / 1000) * (253 / 160) := by
        gcongr
        exact counterexampleSeed_abs_le w
      _ = 253 / 40000 := by norm_num
  calc
    _ ≤ ‖traceFreeHessian counterexampleSeed w‖ +
        ‖8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w‖ +
        ‖4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ := by
      calc
        _ ≤ ‖traceFreeHessian counterexampleSeed w -
              8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w‖ +
            ‖4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ :=
          norm_add_le _ _
        _ ≤ (‖traceFreeHessian counterexampleSeed w‖ +
              ‖8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w‖) +
            ‖4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ :=
          add_le_add (norm_sub_le _ _) le_rfl
    _ ≤ 47 / 10 + 129 / 1000 + 253 / 40000 :=
      add_le_add (add_le_add (counterexampleSeed_traceFreeHessian_norm_upper w) hfirst) hsecond
    _ ≤ 20 := by norm_num


-- @@ L7313-7341 verbatim
/-- The first derivative of the reciprocal exponent on the positive half-line. The formula is
kept in the original radial variable so later estimates may choose their own rescaling. -/
private theorem counterexampleTwoReciprocalExponent_deriv_of_pos {s : ℝ} (hs : 0 < s) :
    deriv counterexampleTwoReciprocalExponent s =
      ((1 / 8 : ℝ) * (s / 10000) ^ (-(7 : ℝ) / 8) / 10000) *
          Real.exp (-10000 / s) +
        (s / 10000) ^ ((1 : ℝ) / 8) * Real.exp (-10000 / s) *
          (10000 / s ^ 2) := by
  have heq : counterexampleTwoReciprocalExponent =ᶠ[nhds s]
      fun x : ℝ ↦ (x / 10000) ^ ((1 : ℝ) / 8) * Real.exp (-10000 / x) := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    exact counterexampleTwoReciprocalExponent_of_pos hx
  have hpow := ((hasDerivAt_id s).div_const 10000).rpow_const (p := (1 / 8 : ℝ))
    (Or.inl (div_ne_zero hs.ne' (by norm_num)))
  have hexp := ((hasDerivAt_const s (-10000)).div (hasDerivAt_id s) hs.ne').exp
  have hprod := hpow.mul hexp
  rw [heq.deriv_eq]
  change deriv ((fun x : ℝ ↦ (x / 10000) ^ ((1 : ℝ) / 8) *
    Real.exp (-10000 / x))) s = _
  have hfun : (fun x : ℝ ↦ (x / 10000) ^ ((1 : ℝ) / 8) *
      Real.exp (-10000 / x)) =
      ((fun y : ℝ ↦ (id y / 10000) ^ ((1 : ℝ) / 8)) *
        fun x : ℝ ↦ Real.exp
          (((fun _ : ℝ ↦ (-10000 : ℝ)) / (id : ℝ → ℝ)) x)) := by
    funext x
    rfl
  rw [hfun, hprod.deriv]
  simp only [Pi.mul_apply, Pi.div_apply, Pi.pow_apply, id_eq]
  ring


-- @@ L7343-7382 verbatim
/-- The same first derivative in the dimensionless variable `t = 10000 / s`. -/
private theorem counterexampleTwoReciprocalExponent_deriv_dimensionless {s : ℝ} (hs : 0 < s) :
    let t := 10000 / s
    deriv counterexampleTwoReciprocalExponent s =
      1 / 10000 * Real.exp (-t) *
        ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) + t ^ (15 / 8 : ℝ)) := by
  let t := 10000 / s
  change deriv counterexampleTwoReciprocalExponent s =
    1 / 10000 * Real.exp (-t) *
      ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) + t ^ (15 / 8 : ℝ))
  have ht : 0 < t := div_pos (by norm_num) hs
  have ht_inv : t = (s / 10000)⁻¹ := by
    dsimp [t]
    field_simp
  have hrpow (a : ℝ) : (s / 10000) ^ a = t ^ (-a) := by
    rw [ht_inv, ← Real.rpow_neg_eq_inv_rpow]
    congr 1
    ring
  have hs_over : 10000 / s ^ 2 = t ^ 2 / 10000 := by
    dsimp [t]
    field_simp
  rw [counterexampleTwoReciprocalExponent_deriv_of_pos hs, hrpow, hrpow, hs_over]
  have hexp : -10000 / s = -t := by
    dsimp only [t]
    ring
  rw [hexp]
  norm_num only [neg_div, neg_neg]
  have hshift : t ^ (-(1 : ℝ) / 8) * t ^ (2 : ℝ) = t ^ (15 / 8 : ℝ) := by
    rw [← Real.rpow_add ht]
    congr 1
    norm_num
  rw [← Real.rpow_two t]
  rw [show (-(1 / 8 : ℝ)) = (-(1 : ℝ) / 8) by ring]
  calc
    ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) / 10000 * Real.exp (-t) +
        t ^ (-(1 : ℝ) / 8) * Real.exp (-t) * (t ^ (2 : ℝ) / 10000)) =
        1 / 10000 * Real.exp (-t) *
          ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) +
            t ^ (-(1 : ℝ) / 8) * t ^ (2 : ℝ)) := by ring
    _ = _ := by rw [hshift]


-- @@ L7384-7459 verbatim
/-- The second reciprocal-exponent derivative in the same dimensionless variable. -/
private theorem counterexampleTwoReciprocalExponent_second_deriv_dimensionless
    {s : ℝ} (hs : 0 < s) :
    let t := 10000 / s
    deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) s =
      -(1 / 100000000 : ℝ) * Real.exp (-t) *
        ((7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
          (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ) - t ^ (31 / 8 : ℝ)) := by
  let t := 10000 / s
  change deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) s =
    -(1 / 100000000 : ℝ) * Real.exp (-t) *
      ((7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
        (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ) - t ^ (31 / 8 : ℝ))
  have ht : 0 < t := div_pos (by norm_num) hs
  let P : ℝ → ℝ := fun x ↦
    let y := 10000 / x
    1 / 10000 * Real.exp (-y) *
      ((1 / 8 : ℝ) * y ^ (7 / 8 : ℝ) + y ^ (15 / 8 : ℝ))
  have heq : (fun x ↦ deriv counterexampleTwoReciprocalExponent x) =ᶠ[nhds s] P := by
    filter_upwards [Ioi_mem_nhds hs] with x hx
    exact counterexampleTwoReciprocalExponent_deriv_dimensionless hx
  have hT₀ : HasDerivAt (fun x : ℝ ↦ 10000 / x) (-10000 / s ^ 2) s := by
    have h := ((hasDerivAt_id s).inv hs.ne').const_mul (10000 : ℝ)
    convert h using 1
    all_goals first
      | with_reducible_and_instances rfl
      | funext x
        simp only [div_eq_mul_inv, Pi.inv_apply, id_eq]
      | simp only [div_eq_mul_inv, id_eq]
        field_simp [hs.ne']
  have hcoef : -10000 / s ^ 2 = -t ^ 2 / 10000 := by
    dsimp only [t]
    field_simp [hs.ne']
  have hT : HasDerivAt (fun x : ℝ ↦ 10000 / x) (-t ^ 2 / 10000) s := by
    simpa only [hcoef] using hT₀
  have hA := ((hT.rpow_const (p := (7 / 8 : ℝ)) (Or.inl ht.ne')).const_mul
    (1 / 8 : ℝ)).add
      (hT.rpow_const (p := (15 / 8 : ℝ)) (Or.inl ht.ne'))
  have hP := (hasDerivAt_const s (1 / 10000 : ℝ)).mul (hT.neg.exp.mul hA)
  calc
    deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) s = deriv P s :=
      heq.deriv_eq
    _ = _ := by
      rw [show deriv P s = _ by
        convert hP.deriv using 1
        all_goals first
          | with_reducible_and_instances rfl
          | congr 1
            funext x
            simp [P, Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, id_eq]
            ring]
      rw [show 10000 / s = t by rfl]
      simp only [Pi.add_apply, Pi.mul_apply, Pi.neg_apply, Pi.div_apply, id_eq]
      simp only [show 10000 / s = t by rfl]
      rw [← Real.rpow_two t]
      ring_nf
      have h23 : t ^ (7 / 8 : ℝ) * t ^ (2 : ℝ) = t ^ (23 / 8 : ℝ) := by
        rw [← Real.rpow_add ht]
        congr 1
        norm_num
      have h31 : t ^ (15 / 8 : ℝ) * t ^ (2 : ℝ) = t ^ (31 / 8 : ℝ) := by
        rw [← Real.rpow_add ht]
        congr 1
        norm_num
      have h15 : t ^ (2 : ℝ) * t ^ (-(1 : ℝ) / 8) = t ^ (15 / 8 : ℝ) := by
        rw [← Real.rpow_add ht]
        congr 1
        norm_num
      have hterm23 : Real.exp (-t) * t ^ (7 / 8 : ℝ) * t ^ (2 : ℝ) =
          Real.exp (-t) * t ^ (23 / 8 : ℝ) := by rw [mul_assoc, h23]
      have hterm31 : Real.exp (-t) * t ^ (15 / 8 : ℝ) * t ^ (2 : ℝ) =
          Real.exp (-t) * t ^ (31 / 8 : ℝ) := by rw [mul_assoc, h31]
      have hterm15 : Real.exp (-t) * t ^ (2 : ℝ) * t ^ (-(1 : ℝ) / 8) =
          Real.exp (-t) * t ^ (15 / 8 : ℝ) := by rw [mul_assoc, h15]
      rw [hterm23, hterm31, hterm15]
      ring


-- @@ L7461-7528 verbatim
/-- After the substitution `t = 10000 / ‖w‖²`, the first reciprocal-exponent derivative is
exactly the numerator controlled by `reciprocalDampingFirstNumerator_bound`. -/
private theorem counterexampleTwoReciprocalExponent_deriv_rescaled {w : ℂ} (hw : w ≠ 0) :
    let t := 10000 / ‖w‖ ^ 2
    ‖w‖ * |deriv counterexampleTwoReciprocalExponent (‖w‖ ^ 2)| =
      1 / 100 * (Real.exp (-t) *
        ((1 / 8 : ℝ) * t ^ (3 / 8 : ℝ) + t ^ (11 / 8 : ℝ))) := by
  let r := ‖w‖
  let s := r ^ 2
  let t := 10000 / s
  change r * |deriv counterexampleTwoReciprocalExponent s| =
    1 / 100 * (Real.exp (-t) *
      ((1 / 8 : ℝ) * t ^ (3 / 8 : ℝ) + t ^ (11 / 8 : ℝ)))
  have hr : 0 < r := norm_pos_iff.mpr hw
  have hs : 0 < s := sq_pos_of_pos hr
  have ht : 0 < t := div_pos (by norm_num) hs
  have ht_inv : t = (s / 10000)⁻¹ := by
    dsimp [t]
    field_simp
  have hrpow (a : ℝ) : (s / 10000) ^ a = t ^ (-a) := by
    rw [ht_inv, ← Real.rpow_neg_eq_inv_rpow]
    congr 1
    ring
  have hs_over : 10000 / s ^ 2 = t ^ 2 / 10000 := by
    dsimp [t]
    field_simp
  have hr_eq : r = 100 * t ^ (-(1 : ℝ) / 2) := by
    have hsquare : r ^ 2 = (100 * t ^ (-(1 : ℝ) / 2)) ^ 2 := by
      rw [mul_pow, ← Real.rpow_mul_natCast ht.le (-(1 : ℝ) / 2) 2,
        show (-(1 : ℝ) / 2) * (2 : ℕ) = -(1 : ℝ) by norm_num,
        Real.rpow_neg ht.le, Real.rpow_one]
      dsimp [t, s]
      field_simp
      norm_num
    obtain h | h := eq_or_eq_neg_of_sq_eq_sq r
      (100 * t ^ (-(1 : ℝ) / 2)) hsquare
    · exact h
    · nlinarith [hr, Real.rpow_pos_of_pos ht (-(1 : ℝ) / 2)]
  rw [counterexampleTwoReciprocalExponent_deriv_of_pos hs, abs_of_nonneg (by positivity),
    hrpow, hrpow, hs_over, hr_eq]
  have hexp : -10000 / s = -t := by
    dsimp only [t]
    ring
  rw [hexp]
  norm_num only [neg_div, neg_neg]
  have hshift₁ : t ^ (-(1 : ℝ) / 2) * t ^ (7 / 8 : ℝ) = t ^ (3 / 8 : ℝ) := by
    rw [← Real.rpow_add ht]
    congr 1
    norm_num
  have hshift₂ : t ^ (-(1 : ℝ) / 2) *
      (t ^ (-(1 : ℝ) / 8) * t ^ (2 : ℝ)) = t ^ (11 / 8 : ℝ) := by
    rw [← Real.rpow_add ht, ← Real.rpow_add ht]
    congr 1
    norm_num
  rw [← Real.rpow_two t]
  rw [show (-(1 / 2 : ℝ)) = (-(1 : ℝ) / 2) by ring,
    show (-(1 / 8 : ℝ)) = (-(1 : ℝ) / 8) by ring]
  calc
    100 * t ^ (-(1 : ℝ) / 2) *
        ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) / 10000 * Real.exp (-t) +
          t ^ (-(1 : ℝ) / 8) * Real.exp (-t) * (t ^ (2 : ℝ) / 10000)) =
        1 / 100 * Real.exp (-t) *
          ((1 / 8 : ℝ) * (t ^ (-(1 : ℝ) / 2) * t ^ (7 / 8 : ℝ)) +
            t ^ (-(1 : ℝ) / 2) *
              (t ^ (-(1 : ℝ) / 8) * t ^ (2 : ℝ))) := by ring
    _ = _ := by
      rw [hshift₁, hshift₂]
      ring


-- @@ L7530-7537 verbatim
/-- Uniform first-derivative bound for the reciprocal exponent away from the reciprocal-chart
origin. -/
private theorem counterexampleTwoReciprocalExponent_first_bound {w : ℂ} (hw : w ≠ 0) :
    ‖w‖ * |deriv counterexampleTwoReciprocalExponent (‖w‖ ^ 2)| ≤ 1 / 100 := by
  rw [counterexampleTwoReciprocalExponent_deriv_rescaled hw]
  have ht : 0 ≤ 10000 / ‖w‖ ^ 2 := by positivity
  have h := reciprocalDampingFirstNumerator_bound ht
  nlinarith


-- @@ L7539-7715 verbatim
/-- Uniform combined first/second derivative bound for the reciprocal exponent. -/
private theorem counterexampleTwoReciprocalExponent_second_bound {w : ℂ} (hw : w ≠ 0) :
    ‖w‖ ^ 2 * (deriv counterexampleTwoReciprocalExponent (‖w‖ ^ 2) ^ 2 +
      |deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) (‖w‖ ^ 2)|) ≤
        1 / 1000 := by
  let s := ‖w‖ ^ 2
  let t := 10000 / s
  change s * (deriv counterexampleTwoReciprocalExponent s ^ 2 +
    |deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) s|) ≤ 1 / 1000
  have hs : 0 < s := sq_pos_of_pos (norm_pos_iff.mpr hw)
  have ht : 0 < t := div_pos (by norm_num) hs
  have hs_eq : s = 10000 / t := by
    dsimp [t]
    field_simp
  have hp := counterexampleTwoReciprocalExponent_deriv_dimensionless hs
  have hpp := counterexampleTwoReciprocalExponent_second_deriv_dimensionless hs
  have hp' : deriv counterexampleTwoReciprocalExponent s =
      1 / 10000 * Real.exp (-t) *
        ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) + t ^ (15 / 8 : ℝ)) := hp
  have hpp' : deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) s =
      -(1 / 100000000 : ℝ) * Real.exp (-t) *
        ((7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
          (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ) - t ^ (31 / 8 : ℝ)) := hpp
  have hbracket :
      |(7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
          (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ) - t ^ (31 / 8 : ℝ)| ≤
        (7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
          (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ) + t ^ (31 / 8 : ℝ) := by
    calc
      |(7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
          (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ) - t ^ (31 / 8 : ℝ)| ≤
          |(7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
            (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ)| + |t ^ (31 / 8 : ℝ)| := abs_sub _ _
      _ ≤ |(7 / 64 : ℝ) * t ^ (15 / 8 : ℝ)| +
          |(7 / 4 : ℝ) * t ^ (23 / 8 : ℝ)| + |t ^ (31 / 8 : ℝ)| := by
        gcongr
        exact abs_add_le _ _
      _ = (7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
          (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ) + t ^ (31 / 8 : ℝ) := by
        rw [abs_of_nonneg, abs_of_nonneg, abs_of_nonneg]
        all_goals positivity
  have hp_part : s * deriv counterexampleTwoReciprocalExponent s ^ 2 =
      1 / 10000 * (Real.exp (-2 * t) *
        ((1 / 64 : ℝ) * t ^ (3 / 4 : ℝ) +
          (1 / 4 : ℝ) * t ^ (7 / 4 : ℝ) + t ^ (11 / 4 : ℝ))) := by
    rw [hp', hs_eq]
    have h77 : t ^ (7 / 8 : ℝ) * t ^ (7 / 8 : ℝ) = t ^ (7 / 4 : ℝ) := by
      rw [← Real.rpow_add ht]
      congr 1
      norm_num
    have h715 : t ^ (7 / 8 : ℝ) * t ^ (15 / 8 : ℝ) = t ^ (11 / 4 : ℝ) := by
      rw [← Real.rpow_add ht]
      congr 1
      norm_num
    have h1515 : t ^ (15 / 8 : ℝ) * t ^ (15 / 8 : ℝ) = t ^ (15 / 4 : ℝ) := by
      rw [← Real.rpow_add ht]
      congr 1
      norm_num
    have h13 : t * t ^ (3 / 4 : ℝ) = t ^ (7 / 4 : ℝ) := by
      nth_rewrite 1 [← Real.rpow_one t]
      rw [← Real.rpow_add ht]
      congr 1
      norm_num
    have h17 : t * t ^ (7 / 4 : ℝ) = t ^ (11 / 4 : ℝ) := by
      nth_rewrite 1 [← Real.rpow_one t]
      rw [← Real.rpow_add ht]
      congr 1
      norm_num
    have h111 : t * t ^ (11 / 4 : ℝ) = t ^ (15 / 4 : ℝ) := by
      nth_rewrite 1 [← Real.rpow_one t]
      rw [← Real.rpow_add ht]
      congr 1
      norm_num
    have hc13 : t * ((1 / 64 : ℝ) * t ^ (3 / 4 : ℝ)) =
        (1 / 64 : ℝ) * t ^ (7 / 4 : ℝ) := by
      calc
        t * ((1 / 64 : ℝ) * t ^ (3 / 4 : ℝ)) =
            (1 / 64 : ℝ) * (t * t ^ (3 / 4 : ℝ)) := by ring
        _ = _ := by rw [h13]
    have hc17 : t * ((1 / 4 : ℝ) * t ^ (7 / 4 : ℝ)) =
        (1 / 4 : ℝ) * t ^ (11 / 4 : ℝ) := by
      calc
        t * ((1 / 4 : ℝ) * t ^ (7 / 4 : ℝ)) =
            (1 / 4 : ℝ) * (t * t ^ (7 / 4 : ℝ)) := by ring
        _ = _ := by rw [h17]
    have hsq :
        ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) + t ^ (15 / 8 : ℝ)) ^ 2 =
          t * ((1 / 64 : ℝ) * t ^ (3 / 4 : ℝ) +
            (1 / 4 : ℝ) * t ^ (7 / 4 : ℝ) + t ^ (11 / 4 : ℝ)) := by
      calc
        ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) + t ^ (15 / 8 : ℝ)) ^ 2 =
            (1 / 64 : ℝ) * (t ^ (7 / 8 : ℝ) * t ^ (7 / 8 : ℝ)) +
              (1 / 4 : ℝ) * (t ^ (7 / 8 : ℝ) * t ^ (15 / 8 : ℝ)) +
              t ^ (15 / 8 : ℝ) * t ^ (15 / 8 : ℝ) := by ring
        _ = (1 / 64 : ℝ) * t ^ (7 / 4 : ℝ) +
              (1 / 4 : ℝ) * t ^ (11 / 4 : ℝ) + t ^ (15 / 4 : ℝ) := by
          rw [h77, h715, h1515]
        _ = _ := by rw [mul_add, mul_add, hc13, hc17, h111]
    have hexpSq : Real.exp (-t) ^ 2 = Real.exp (-2 * t) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    calc
      10000 / t *
          (1 / 10000 * Real.exp (-t) *
            ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) + t ^ (15 / 8 : ℝ))) ^ 2 =
          10000 / t * ((1 / 10000 : ℝ) ^ 2 * Real.exp (-t) ^ 2 *
            ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) + t ^ (15 / 8 : ℝ)) ^ 2) := by
            ring
      _ = _ := by
        rw [hexpSq, hsq]
        field_simp [ht.ne']
  have hpp_part : s *
      |deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) s| ≤
      1 / 10000 * (Real.exp (-t) *
        ((7 / 64 : ℝ) * t ^ (7 / 8 : ℝ) +
          (7 / 4 : ℝ) * t ^ (15 / 8 : ℝ) + t ^ (23 / 8 : ℝ))) := by
    rw [hpp']
    rw [abs_mul, abs_mul, abs_neg,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 100000000),
      abs_of_nonneg (Real.exp_nonneg _)]
    calc
      s * (1 / 100000000 * Real.exp (-t) *
          |(7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
            (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ) - t ^ (31 / 8 : ℝ)|) ≤
          s * (1 / 100000000 * Real.exp (-t) *
            ((7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
              (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ) + t ^ (31 / 8 : ℝ))) := by
        gcongr
      _ = 1 / 10000 * (Real.exp (-t) *
          ((7 / 64 : ℝ) * t ^ (7 / 8 : ℝ) +
            (7 / 4 : ℝ) * t ^ (15 / 8 : ℝ) + t ^ (23 / 8 : ℝ))) := by
        rw [hs_eq]
        have h7 : t * t ^ (7 / 8 : ℝ) = t ^ (15 / 8 : ℝ) := by
          nth_rewrite 1 [← Real.rpow_one t]
          rw [← Real.rpow_add ht]
          congr 1
          norm_num
        have h15 : t * t ^ (15 / 8 : ℝ) = t ^ (23 / 8 : ℝ) := by
          nth_rewrite 1 [← Real.rpow_one t]
          rw [← Real.rpow_add ht]
          congr 1
          norm_num
        have h23 : t * t ^ (23 / 8 : ℝ) = t ^ (31 / 8 : ℝ) := by
          nth_rewrite 1 [← Real.rpow_one t]
          rw [← Real.rpow_add ht]
          congr 1
          norm_num
        have hshift :
            (7 / 64 : ℝ) * t ^ (15 / 8 : ℝ) +
                (7 / 4 : ℝ) * t ^ (23 / 8 : ℝ) + t ^ (31 / 8 : ℝ) =
              t * ((7 / 64 : ℝ) * t ^ (7 / 8 : ℝ) +
                (7 / 4 : ℝ) * t ^ (15 / 8 : ℝ) + t ^ (23 / 8 : ℝ)) := by
          calc
            _ = (7 / 64 : ℝ) * (t * t ^ (7 / 8 : ℝ)) +
                (7 / 4 : ℝ) * (t * t ^ (15 / 8 : ℝ)) +
                t * t ^ (23 / 8 : ℝ) := by rw [h7, h15, h23]
            _ = _ := by ring
        rw [hshift]
        field_simp [ht.ne']
        ring
  rw [mul_add, hp_part]
  calc
    1 / 10000 * (Real.exp (-2 * t) *
        ((1 / 64 : ℝ) * t ^ (3 / 4 : ℝ) +
          (1 / 4 : ℝ) * t ^ (7 / 4 : ℝ) + t ^ (11 / 4 : ℝ))) +
      s * |deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) s| ≤
        1 / 10000 * (Real.exp (-2 * t) *
          ((1 / 64 : ℝ) * t ^ (3 / 4 : ℝ) +
            (1 / 4 : ℝ) * t ^ (7 / 4 : ℝ) + t ^ (11 / 4 : ℝ)) +
          Real.exp (-t) * ((7 / 64 : ℝ) * t ^ (7 / 8 : ℝ) +
            (7 / 4 : ℝ) * t ^ (15 / 8 : ℝ) + t ^ (23 / 8 : ℝ))) := by
          nlinarith
    _ ≤ 1 / 10000 * 10 := by
      gcongr
      exact (reciprocalDampingSecondNumerator_bound ht.le).le
    _ = 1 / 1000 := by norm_num


-- @@ L7717-7757 verbatim
/-- A direct, deliberately loose bound for the first radial derivative. Unlike the rescaled
bound above, this remains useful in the Laplacian formula at the reciprocal origin. -/
private theorem counterexampleTwoReciprocalExponent_deriv_abs_le (s : ℝ) (hs : 0 ≤ s) :
    |deriv counterexampleTwoReciprocalExponent s| ≤ 1 / 1000 := by
  by_cases hs0 : s = 0
  · subst s
    let f : ℝ → ℝ := fun x ↦ x ^ ((1 : ℝ) / 8) * Real.flatRpowExp 1 10000 x
    have hflat := Real.flatRpowExp.rpow_mul_iteratedFDeriv_zero
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (0 : ℝ) < 10000) ((1 : ℝ) / 8) 1
    have hfderiv : fderiv ℝ f 0 = 0 := by
      apply ContinuousLinearMap.ext
      intro v
      have happ := congrArg (fun L : ℝ [×1]→L[ℝ] ℝ ↦ L ![v]) hflat
      simpa only [f, iteratedFDeriv_one_apply,
        ContinuousMultilinearMap.zero_apply, Matrix.cons_val_zero] using happ
    have hfcont : ContDiff ℝ ∞ f :=
      Real.flatRpowExp.rpow_mul_contDiff (by norm_num) (by norm_num) ((1 : ℝ) / 8)
    have hfDiff : DifferentiableAt ℝ f 0 := hfcont.differentiable (by simp) 0
    have hderiv : deriv f 0 = 0 := by rw [deriv, hfderiv]; rfl
    change |deriv (fun x : ℝ ↦ (10000 : ℝ) ^ (-(1 : ℝ) / 8) * f x) 0| ≤ 1 / 1000
    rw [deriv_const_mul _ hfDiff, hderiv, mul_zero, abs_zero]
    norm_num
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    let t := 10000 / s
    have ht : 0 < t := div_pos (by norm_num) hspos
    rw [counterexampleTwoReciprocalExponent_deriv_dimensionless hspos,
      abs_of_nonneg (by positivity)]
    have h₁ : t ^ (7 / 8 : ℝ) * Real.exp (-t) ≤ 1 :=
      rpow_mul_exp_neg_le_one (a := 7 / 8) ht.le (by norm_num) (by norm_num)
    have h₂ : t ^ (15 / 8 : ℝ) * Real.exp (-t) ≤ 15 / 16 :=
      (rpow_mul_exp_neg_le_self (a := 15 / 8) ht.le (by norm_num)).trans
        ((self_rpow_mul_exp_neg_le_half (a := 15 / 8) (by norm_num) (by norm_num)).trans_eq
          (by norm_num))
    calc
      1 / 10000 * Real.exp (-t) *
          ((1 / 8 : ℝ) * t ^ (7 / 8 : ℝ) + t ^ (15 / 8 : ℝ)) =
        1 / 10000 * ((1 / 8 : ℝ) *
          (t ^ (7 / 8 : ℝ) * Real.exp (-t)) +
            t ^ (15 / 8 : ℝ) * Real.exp (-t)) := by ring
      _ ≤ 1 / 10000 * ((1 / 8 : ℝ) * 1 + 15 / 16) := by gcongr
      _ ≤ 1 / 1000 := by norm_num


-- @@ L7759-7770 verbatim
/-- The conjugate Wirtinger convention used by the support calculation has the same seed bound
as the convention used in the planar index calculation. -/
private theorem complexBarDeriv_counterexampleSeed_norm_upper (w : ℂ) :
    ‖complexBarDeriv counterexampleSeed w‖ ≤ 129 / 80 := by
  have hconj :
      star (((fderiv ℝ counterexampleSeed w 1 : ℂ) -
          (fderiv ℝ counterexampleSeed w Complex.I : ℂ) * Complex.I) / 2) =
        complexBarDeriv counterexampleSeed w := by
    rw [complexBarDeriv]
    simp
  rw [← hconj, norm_star]
  exact counterexampleSeed_wirtinger_norm_upper w


-- @@ L7772-7963 verbatim
/-- The Euclidean chart Laplacian of the reciprocal representative is controlled by eight
times its positive damping factor. The argument deliberately keeps substantial numerical
slack, since only positivity of the resulting radius tensor matters. -/
private theorem chartLaplacian_counterexampleTwoReciprocal_le_of_seed
    (hSeedLaplacian : ∀ z : ℂ, |chartLaplacian counterexampleSeed z| ≤ 47 / 10)
    (w : ℂ) :
    |chartLaplacian counterexampleTwoReciprocal w| ≤
      8 * counterexampleTwoReciprocalDamping w := by
  let s : ℝ := ‖w‖ ^ 2
  let D : ℝ := s + 10000
  let p : ℝ := deriv counterexampleTwoReciprocalExponent s
  let p' : ℝ := deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) s
  let q : ℝ := 1 / D + p
  let β : ℝ → ℝ := fun x ↦ 10000 / (x + 10000) *
    Real.exp (-counterexampleTwoReciprocalExponent x)
  let B : ℂ → ℝ := counterexampleTwoReciprocalDamping
  have hs : 0 ≤ s := sq_nonneg _
  have hD : 0 < D := by dsimp only [D]; positivity
  have hBpos : 0 < B w := by
    dsimp only [B, counterexampleTwoReciprocalDamping]
    positivity
  have hβ : ContDiffAt ℝ 2 β s := by
    exact counterexampleTwoReciprocalRadialDamping_contDiffAt (by linarith [hs])
  have hβ₁ : deriv β s = -(B w) * q := by
    rw [counterexampleTwoReciprocalRadialDamping_deriv (by linarith [hs])]
    rfl
  have hβ₂ : deriv (fun x ↦ deriv β x) s =
      B w * (q ^ 2 + 1 / D ^ 2 - p') := by
    rw [counterexampleTwoReciprocalRadialDamping_second_deriv
      (by linarith [hs])]
    rfl
  have hp : |p| ≤ 1 / 1000 :=
    counterexampleTwoReciprocalExponent_deriv_abs_le s hs
  have hrp : ‖w‖ * |p| ≤ 1 / 100 := by
    by_cases hw : w = 0
    · simp [hw]
    · exact counterexampleTwoReciprocalExponent_first_bound hw
  have hpp : s * (p ^ 2 + |p'|) ≤ 1 / 1000 := by
    by_cases hw : w = 0
    · simp [hw, s]
    · simpa only [s, p, p'] using counterexampleTwoReciprocalExponent_second_bound hw
  have hrD : ‖w‖ / D ≤ 1 / 200 := by
    have hsquare := sq_nonneg (‖w‖ - 100)
    dsimp only [D, s]
    apply (div_le_iff₀ (by positivity)).2
    nlinarith
  have hsD : s / D ^ 2 ≤ 1 / 10000 := by
    dsimp only [D]
    apply (div_le_iff₀ (sq_pos_of_pos hD)).2
    nlinarith [sq_nonneg s]
  have hq : |q| ≤ 11 / 10000 := by
    calc
      |q| ≤ |1 / D| + |p| := by dsimp only [q]; exact abs_add_le ..
      _ = 1 / D + |p| := by rw [abs_of_pos (one_div_pos.mpr hD)]
      _ ≤ 1 / 10000 + 1 / 1000 := by
        gcongr
        change 10000 ≤ D
        dsimp only [D]
        linarith [hs]
      _ = 11 / 10000 := by norm_num
  have hrq : ‖w‖ * |q| ≤ 3 / 200 := by
    calc
      ‖w‖ * |q| ≤ ‖w‖ * (|1 / D| + |p|) := by
        gcongr
        dsimp only [q]
        exact abs_add_le ..
      _ = ‖w‖ / D + ‖w‖ * |p| := by
        rw [abs_of_pos (one_div_pos.mpr hD)]
        ring
      _ ≤ 1 / 200 + 1 / 100 := add_le_add hrD hrp
      _ = 3 / 200 := by norm_num
  have hinside :
      |-(q) + s * (q ^ 2 + 1 / D ^ 2 - p')| ≤ 1 / 40 := by
    calc
      |-(q) + s * (q ^ 2 + 1 / D ^ 2 - p')| ≤
          |q| + s * (q ^ 2 + 1 / D ^ 2 + |p'|) := by
        calc
          _ ≤ |-q| + |s * (q ^ 2 + 1 / D ^ 2 - p')| := abs_add_le ..
          _ = |q| + s * |q ^ 2 + 1 / D ^ 2 - p'| := by
            rw [abs_neg, abs_mul, abs_of_nonneg hs]
          _ ≤ |q| + s * (q ^ 2 + 1 / D ^ 2 + |p'|) := by
            gcongr
            calc
              |q ^ 2 + 1 / D ^ 2 - p'| ≤
                  |q ^ 2 + 1 / D ^ 2| + |p'| := abs_sub ..
              _ = q ^ 2 + 1 / D ^ 2 + |p'| := by
                rw [abs_of_nonneg]
                positivity
      _ ≤ 11 / 10000 +
          s * (2 * (1 / D ^ 2 + p ^ 2) + 1 / D ^ 2 + |p'|) := by
        gcongr
        dsimp only [q]
        have hdivsq : (1 / D) ^ 2 = 1 / D ^ 2 := by ring
        rw [← hdivsq]
        nlinarith [sq_nonneg (1 / D - p)]
      _ ≤ 11 / 10000 + 3 * (1 / 10000) + 2 * (1 / 1000) := by
        have hrewrite : s * (2 * (1 / D ^ 2 + p ^ 2) + 1 / D ^ 2 + |p'|) =
            3 * (s / D ^ 2) + 2 * (s * (p ^ 2 + |p'|)) - s * |p'| := by
          ring
        rw [hrewrite]
        nlinarith [hsD, hpp, mul_nonneg hs (abs_nonneg p')]
      _ ≤ 1 / 40 := by norm_num
  have hLaplacianB : |chartLaplacian B w| ≤ B w / 10 := by
    have hBrep : B = fun z : ℂ ↦ β (‖z‖ ^ 2) := by rfl
    rw [hBrep, chartLaplacian_comp_norm_sq β w hβ, hβ₁, hβ₂]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    change 4 * |-B w * q + ‖w‖ ^ 2 * (B w * (q ^ 2 + 1 / D ^ 2 - p'))| ≤
      β (‖w‖ ^ 2) / 10
    change 4 * |-B w * q + s * (B w * (q ^ 2 + 1 / D ^ 2 - p'))| ≤ β s / 10
    rw [show β s = B w by rfl]
    rw [show -B w * q + s * (B w * (q ^ 2 + 1 / D ^ 2 - p')) =
      B w * (-q + s * (q ^ 2 + 1 / D ^ 2 - p')) by ring,
      abs_mul, abs_of_pos hBpos]
    calc
      4 * (B w * |-(q) + s * (q ^ 2 + 1 / D ^ 2 - p')|) ≤
          4 * (B w * (1 / 40)) := by gcongr
      _ = B w / 10 := by ring
  have hDB (v : ℂ) : fderiv ℝ B w v =
      -2 * B w * q * inner ℝ w v := by
    have hβderiv : HasDerivAt β (-(B w) * q) s := by
      convert! (hβ.differentiableAt (by norm_num)).hasDerivAt using 1
      exact hβ₁.symm
    have hsderiv : HasFDerivAt (fun z : ℂ ↦ ‖z‖ ^ 2) (2 • innerSL ℝ w) w := by
      simpa only [two_smul] using (hasStrictFDerivAt_norm_sq w).hasFDerivAt
    have hcomp := hβderiv.hasFDerivAt.comp w hsderiv
    have hBrep : B = fun z : ℂ ↦ β (‖z‖ ^ 2) := by rfl
    rw [hBrep]
    change fderiv ℝ (β ∘ fun z : ℂ ↦ ‖z‖ ^ 2) w v =
      -2 * β s * q * inner ℝ w v
    rw [hcomp.fderiv]
    simp
    rw [show β s = B w by rfl]
    ring
  have hcross :
      |2 * (fderiv ℝ B w 1 * fderiv ℝ counterexampleSeed w 1 +
        fderiv ℝ B w Complex.I * fderiv ℝ counterexampleSeed w Complex.I)| ≤
          B w / 2 := by
    let g := complexBarDeriv counterexampleSeed w
    have hg : ‖g‖ ≤ 129 / 80 := complexBarDeriv_counterexampleSeed_norm_upper w
    have hidentity :
        2 * (fderiv ℝ B w 1 * fderiv ℝ counterexampleSeed w 1 +
          fderiv ℝ B w Complex.I * fderiv ℝ counterexampleSeed w Complex.I) =
            -8 * B w * q * (w * star g).re := by
      rw [hDB, hDB]
      dsimp only [g, complexBarDeriv]
      simp [Complex.inner, Complex.mul_re, Complex.mul_im]
      ring
    rw [hidentity, abs_mul, abs_mul, abs_mul, abs_of_pos hBpos]
    have hre : |(w * star g).re| ≤ ‖w‖ * ‖g‖ := by
      calc
        |(w * star g).re| ≤ ‖w * star g‖ := Complex.abs_re_le_norm _
        _ = ‖w‖ * ‖g‖ := by rw [norm_mul, norm_star]
    calc
      |(-8 : ℝ)| * B w * |q| * |(w * star g).re| ≤
        8 * B w * |q| * (‖w‖ * ‖g‖) := by
          norm_num
          exact mul_le_mul_of_nonneg_left
            (show |w.re * g.re + w.im * g.im| ≤ ‖w‖ * ‖g‖ by
              simpa [Complex.mul_re] using hre)
            (mul_nonneg (mul_nonneg (by norm_num) hBpos.le) (abs_nonneg q))
      _ = B w * (8 * (‖w‖ * |q|) * ‖g‖) := by ring
      _ ≤ B w * (8 * (3 / 200) * (129 / 80)) := by
        gcongr
      _ ≤ B w / 2 := by nlinarith [hBpos]
  have hproduct := chartLaplacian_mul B counterexampleSeed
    counterexampleTwoReciprocalDamping_contDiff counterexampleSeed_contDiff w
  have hsum : |chartLaplacian (fun z ↦ B z * counterexampleSeed z) w| ≤
      B w * (47 / 10) + (253 / 160) * (B w / 10) + B w / 2 := by
    rw [hproduct]
    calc
      |B w * chartLaplacian counterexampleSeed w +
          counterexampleSeed w * chartLaplacian B w +
            2 * (fderiv ℝ B w 1 * fderiv ℝ counterexampleSeed w 1 +
              fderiv ℝ B w Complex.I * fderiv ℝ counterexampleSeed w Complex.I)| ≤
          |B w * chartLaplacian counterexampleSeed w| +
            |counterexampleSeed w * chartLaplacian B w| +
              |2 * (fderiv ℝ B w 1 * fderiv ℝ counterexampleSeed w 1 +
                fderiv ℝ B w Complex.I * fderiv ℝ counterexampleSeed w Complex.I)| := by
        exact (abs_add_le ..).trans (add_le_add (abs_add_le ..) le_rfl)
      _ ≤ B w * (47 / 10) + (253 / 160) * (B w / 10) + B w / 2 := by
        rw [abs_mul, abs_mul, abs_of_pos hBpos]
        exact add_le_add
          (add_le_add (mul_le_mul_of_nonneg_left (hSeedLaplacian w) hBpos.le)
            (mul_le_mul (counterexampleSeed_abs_le w) hLaplacianB
              (abs_nonneg _) (by positivity))) hcross
  change |chartLaplacian
    (fun z ↦ 10 ^ 10 + B z * counterexampleSeed z) w| ≤ 8 * B w
  rw [chartLaplacian_const_add]
  · calc
      _ ≤ B w * (47 / 10) + (253 / 160) * (B w / 10) + B w / 2 := hsum
      _ ≤ 8 * B w := by nlinarith [le_of_lt hBpos]
  · exact counterexampleTwoReciprocalDamping_contDiff.mul counterexampleSeed_contDiff


-- @@ L7965-7974 verbatim
/-- The explicit reciprocal trace-free model is nonzero away from the reciprocal origin. -/
private theorem counterexampleTwoReciprocalTraceFreeModel_ne_zero {w : ℂ} (hw : w ≠ 0) :
    let p := deriv counterexampleTwoReciprocalExponent (‖w‖ ^ 2)
    let p' := deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) (‖w‖ ^ 2)
    traceFreeHessian counterexampleSeed w -
        8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w +
      4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w ≠ 0 := by
  exact seedTraceFreeHessian_perturbation_ne_zero w _ _
    (counterexampleTwoReciprocalExponent_first_bound hw)
    (counterexampleTwoReciprocalExponent_second_bound hw)


-- @@ L7976-7987 verbatim
/-- The spherical trace-free Hessian of the reciprocal representative is nonzero away from
the reciprocal origin. -/
private theorem sphericalTraceFreeHessian_counterexampleTwoReciprocal_ne_zero
    {w : ℂ} (hw : w ≠ 0) :
    sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w ≠ 0 := by
  rw [sphericalTraceFreeHessian_counterexampleTwoReciprocal]
  apply mul_ne_zero
  · change (counterexampleTwoReciprocalDamping w : ℂ) ≠ 0
    exact_mod_cast (by
      rw [counterexampleTwoReciprocalDamping]
      positivity : counterexampleTwoReciprocalDamping w ≠ 0)
  · exact counterexampleTwoReciprocalTraceFreeModel_ne_zero hw


-- @@ L7989-8006 verbatim
/-- The spherical trace-free Hessian of the reciprocal representative is nowhere zero,
including at the reciprocal origin (the north pole of the sphere). -/
private theorem sphericalTraceFreeHessian_counterexampleTwoReciprocal_ne_zero_all (w : ℂ) :
    sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w ≠ 0 := by
  by_cases hw : w = 0
  · subst w
    rw [sphericalTraceFreeHessian_counterexampleTwoReciprocal]
    apply mul_ne_zero
    · change (counterexampleTwoReciprocalDamping 0 : ℂ) ≠ 0
      exact_mod_cast (by
        rw [counterexampleTwoReciprocalDamping]
        positivity : counterexampleTwoReciprocalDamping 0 ≠ 0)
    · have hseed : traceFreeHessian counterexampleSeed 0 ≠ 0 := by
        rw [← norm_pos_iff]
        exact (by norm_num : (0 : ℝ) < 7 / 50).trans_le
          (counterexampleSeed_traceFreeHessian_norm_lower 0)
      simpa using hseed
  · exact sphericalTraceFreeHessian_counterexampleTwoReciprocal_ne_zero hw


-- @@ L8008-8041 verbatim
/-- Uniform trace-free spherical-Hessian bound in the reciprocal chart. -/
private theorem sphericalTraceFreeHessian_counterexampleTwoReciprocal_norm_upper (w : ℂ) :
    ‖sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w‖ ≤
      20 * counterexampleTwoReciprocalDamping w := by
  let p := deriv counterexampleTwoReciprocalExponent (‖w‖ ^ 2)
  let p' := deriv (fun x ↦ deriv counterexampleTwoReciprocalExponent x) (‖w‖ ^ 2)
  have hp : ‖w‖ * |p| ≤ 1 / 100 := by
    by_cases hw : w = 0
    · simp [hw]
    · exact counterexampleTwoReciprocalExponent_first_bound hw
  have hpp : ‖w‖ ^ 2 * (p ^ 2 + |p'|) ≤ 1 / 1000 := by
    by_cases hw : w = 0
    · simp [hw]
    · exact counterexampleTwoReciprocalExponent_second_bound hw
  have hBpos : 0 < counterexampleTwoReciprocalDamping w := by
    rw [counterexampleTwoReciprocalDamping]
    positivity
  rw [sphericalTraceFreeHessian_counterexampleTwoReciprocal, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hBpos]
  change counterexampleTwoReciprocalDamping w *
      ‖traceFreeHessian counterexampleSeed w -
          8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w +
        4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ ≤
    20 * counterexampleTwoReciprocalDamping w
  calc
    counterexampleTwoReciprocalDamping w *
        ‖traceFreeHessian counterexampleSeed w -
            8 * w * (p : ℂ) * complexBarDeriv counterexampleSeed w +
          4 * w ^ 2 * ((p ^ 2 - p' : ℝ) : ℂ) * counterexampleSeed w‖ ≤
        counterexampleTwoReciprocalDamping w * 20 :=
      mul_le_mul_of_nonneg_left
        (seedTraceFreeHessian_perturbation_norm_upper w p p' hp hpp) hBpos.le
    _ = 20 * counterexampleTwoReciprocalDamping w := by ring


-- @@ L8043-8095 verbatim
/-- The numerical coefficient in the reciprocal radius formula is below `3 · 10⁹` once the
Laplacian bound is supplied. The exact intermediate value is `2,296,000,002`. -/
private theorem counterexampleTwoReciprocal_radius_coefficient_lt (w : ℂ)
    (hL : |chartLaplacian counterexampleTwoReciprocal w| ≤
      8 * counterexampleTwoReciprocalDamping w) :
    ‖((counterexampleTwoReciprocal w - 10 ^ 10 : ℝ) : ℂ)‖ +
        ((‖w‖ ^ 2 + 10000) ^ 2 / 80000) *
          (‖((chartLaplacian counterexampleTwoReciprocal w : ℝ) : ℂ)‖ +
            ‖sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w‖) <
      3000000000 := by
  have hψ : 0 ≤ counterexampleTwoReciprocalExponent (‖w‖ ^ 2) := by
    rw [counterexampleTwoReciprocalExponent]
    apply mul_nonneg (Real.rpow_nonneg (by norm_num) _)
    apply mul_nonneg (Real.rpow_nonneg (sq_nonneg ‖w‖) _)
    rw [Real.flatRpowExp]
    split <;> positivity
  have hBpos : 0 < counterexampleTwoReciprocalDamping w := by
    rw [counterexampleTwoReciprocalDamping]
    positivity
  have hBle : counterexampleTwoReciprocalDamping w ≤ 1 := by
    rw [counterexampleTwoReciprocalDamping]
    have hfrac : 10000 / (‖w‖ ^ 2 + 10000) ≤ 1 := by
      apply (div_le_one₀ (by positivity)).2
      nlinarith [sq_nonneg ‖w‖]
    exact mul_le_one₀ hfrac (Real.exp_nonneg _)
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hψ))
  have hA : ‖((counterexampleTwoReciprocal w - 10 ^ 10 : ℝ) : ℂ)‖ ≤ 2 := by
    rw [counterexampleTwoReciprocal, add_sub_cancel_left, Complex.norm_real,
      Real.norm_eq_abs, abs_mul, abs_of_pos hBpos]
    calc
      counterexampleTwoReciprocalDamping w * |counterexampleSeed w| ≤
          1 * (253 / 160) := mul_le_mul hBle (counterexampleSeed_abs_le w)
            (abs_nonneg _) zero_le_one
      _ ≤ 2 := by norm_num
  have hQ := sphericalTraceFreeHessian_counterexampleTwoReciprocal_norm_upper w
  have hM := reciprocalConformalDamping_bound w
  have hsum :
      ‖((chartLaplacian counterexampleTwoReciprocal w : ℝ) : ℂ)‖ +
          ‖sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w‖ ≤
        28 * counterexampleTwoReciprocalDamping w := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    linarith
  calc
    ‖((counterexampleTwoReciprocal w - 10 ^ 10 : ℝ) : ℂ)‖ +
        ((‖w‖ ^ 2 + 10000) ^ 2 / 80000) *
          (‖((chartLaplacian counterexampleTwoReciprocal w : ℝ) : ℂ)‖ +
            ‖sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w‖) ≤
      2 + ((‖w‖ ^ 2 + 10000) ^ 2 / 80000) *
        (28 * counterexampleTwoReciprocalDamping w) := by gcongr
    _ = 2 + 14 * (((‖w‖ ^ 2 + 10000) ^ 2 / 40000) *
        counterexampleTwoReciprocalDamping w) := by ring
    _ < 2 + 14 * 164000000 := by gcongr
    _ < 3000000000 := by norm_num


-- @@ L8097-8127 expanded
/-- The exact chart formula and numerical coefficient imply the invariant radius-error bound. -/
private theorem counterexampleTwoReciprocal_radius_error_bound_of_laplacian (w : ℂ)
    (hL : |chartLaplacian counterexampleTwoReciprocal w| ≤ 8 * counterexampleTwoReciprocalDamping w)
    (v : ℂ) :
    let F :=
      SphereSupport.homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension)
    let ρ := fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : EuclideanSpace ℝ (Fin 3))
    ‖fderiv ℝ (fun z : ℂ ↦ F (counterexampleTwoReciprocalSphereChart z)) w v -
          (10 ^ 10 : ℝ) • fderiv ℝ ρ w v‖ ≤
      3000000000 * ‖fderiv ℝ ρ w v‖ :=
  by
  let F :=
    SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
  let ρ := fun z : ℂ ↦ (counterexampleTwoReciprocalSphereChart z : EuclideanSpace ℝ (Fin 3))
  let dρ : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) := fderiv ℝ ρ w
  let dF : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    fderiv ℝ (fun z : ℂ ↦ F (counterexampleTwoReciprocalSphereChart z)) w
  let A : ℂ := (counterexampleTwoReciprocal w - 10 ^ 10 : ℝ)
  let L : ℂ := chartLaplacian counterexampleTwoReciprocal w
  let Q : ℂ := sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w
  let r : ℝ := (‖w‖ ^ 2 + 10000) ^ 2 / 80000
  have hscale (t : ℂ) : ‖dρ t‖ = 200 / (‖w‖ ^ 2 + 10000) * ‖t‖ := by
    exact (counterexampleTwoReciprocalSphereChart_conformal w t t).2
  have hformula (t : ℂ) : dF t - (10 ^ 10 : ℝ) • dρ t = dρ (A * t + r • (L * t + Q * star t)) := by
    exact counterexampleTwoReciprocal_radius_formula w t
  have hnorm :=
    norm_radiusError_le_of_conformal_formula dρ dF (10 ^ 10) (200 / (‖w‖ ^ 2 + 10000)) r A L Q
      (by positivity) (by positivity) hscale hformula v
  have hcoefficient := counterexampleTwoReciprocal_radius_coefficient_lt w hL
  change ‖dF v - (10 ^ 10 : ℝ) • dρ v‖ ≤ 3000000000 * ‖dρ v‖
  exact hnorm.trans (mul_le_mul_of_nonneg_right hcoefficient.le (norm_nonneg _))


-- @@ L8129-8179 expanded
/-- The reciprocal-chart radius bound transports to the intrinsic tangent space of the sphere.
No choice of tangent coordinates remains in this statement. -/
private theorem counterexampleTwo_radius_error_bound_away_south_of_laplacian
    (hL :
      ∀ w : ℂ,
        |chartLaplacian counterexampleTwoReciprocal w| ≤ 8 * counterexampleTwoReciprocalDamping w)
    {p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1} (hp : p ≠ counterexampleSphereChart 0)
    (v : TangentSpace (𝓡 2) p) :
    let F :=
      SphereSupport.homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension)
    ‖sphereAmbientMfderiv F p v -
          (10 ^ 10 : ℝ) •
            sphereAmbientMfderiv
              (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
              v‖ ≤
      3000000000 *
        ‖sphereAmbientMfderiv
            (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
            v‖ :=
  by
  let F :=
    SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
  obtain ⟨w, rfl⟩ := exists_reciprocalSphereChart_of_ne_south hp
  let ρ := counterexampleTwoReciprocalSphereChart
  let dρ : ℂ →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    fderiv ℝ (fun z : ℂ ↦ (ρ z : EuclideanSpace ℝ (Fin 3))) w
  let dn : TangentSpace (𝓡 2) (ρ w) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    sphereAmbientMfderiv
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) (ρ w)
  let dF : TangentSpace (𝓡 2) (ρ w) →L[ℝ] EuclideanSpace ℝ (Fin 3) := sphereAmbientMfderiv F (ρ w)
  have hyv : dn v ∈ (ℝ ∙ (ρ w : EuclideanSpace ℝ (Fin 3)))ᗮ :=
    by
    rw [← range_mvfderiv_subtypeVal (n := 2) (ρ w)]
    exact ⟨v, rfl⟩
  rw [← range_fderiv_counterexampleTwoReciprocalSphereChart w] at hyv
  obtain ⟨a, ha⟩ := hyv
  have hρmd : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓡 2) ρ w :=
    counterexampleTwoReciprocalSphereChart_contMDiff.mdifferentiableAt (by simp)
  have hNmd :
    MDifferentiableAt (𝓡 2) (𝓡 3)
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) (ρ w) :=
    (contMDiff_coe_sphere (m := ∞)).mdifferentiableAt (by simp)
  have hFmd : MDifferentiableAt (𝓡 2) (𝓡 3) F (ρ w) :=
    counterexampleTwoHomogeneousGradient_contMDiff.mdifferentiableAt (by simp)
  have hchainN := mfderiv_comp_apply w hNmd hρmd a
  have hchainF := mfderiv_comp_apply w hFmd hρmd a
  rw [mfderiv_eq_fderiv] at hchainN hchainF
  change dρ a = dn (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) ρ w a) at hchainN
  change fderiv ℝ (fun z : ℂ ↦ F (ρ z)) w a = dF (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) ρ w a) at hchainF
  have ha_tangent : mfderiv 𝓘(ℝ, ℂ) (𝓡 2) ρ w a = v :=
    by
    apply injective_mvfderiv_subtypeVal_sphere (ρ w)
    change dn (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) ρ w a) = dn v
    rw [← hchainN]
    change dρ a = dn v at ha
    exact ha
  have hchart := counterexampleTwoReciprocal_radius_error_bound_of_laplacian w (hL w) a
  change ‖fderiv ℝ (fun z : ℂ ↦ F (ρ z)) w a - (10 ^ 10 : ℝ) • dρ a‖ ≤ 3000000000 * ‖dρ a‖ at hchart
  change ‖dF v - (10 ^ 10 : ℝ) • dn v‖ ≤ 3000000000 * ‖dn v‖
  simpa only [hchainF, hchainN, ha_tangent] using hchart


-- @@ L8181-8211 expanded
/-- The reciprocal radius estimate gives a positive oriented radius tensor at every point away
from the south pole. This is the invariant form used for immersion and chord convexity. -/
private theorem counterexampleTwo_radius_coercive_away_south_of_laplacian
    (hL :
      ∀ w : ℂ,
        |chartLaplacian counterexampleTwoReciprocal w| ≤ 8 * counterexampleTwoReciprocalDamping w)
    {p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1} (hp : p ≠ counterexampleSphereChart 0)
    (v : TangentSpace (𝓡 2) p) :
    7000000000 *
        ‖sphereAmbientMfderiv
              (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
              v‖ ^
          2 ≤
      inner ℝ
        (sphereAmbientMfderiv
          (SphereSupport.homogeneousGradient
            (SphereSupport.radialExtension counterexampleTwoSphereExtension))
          p v)
        (sphereAmbientMfderiv
          (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p v) :=
  by
  let F :=
    SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
  let dFv : EuclideanSpace ℝ (Fin 3) := sphereAmbientMfderiv F p v
  let dnv : EuclideanSpace ℝ (Fin 3) :=
    sphereAmbientMfderiv
      (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p v
  have herror : ‖dFv - (10 ^ 10 : ℝ) • dnv‖ ≤ 3000000000 * ‖dnv‖ :=
    counterexampleTwo_radius_error_bound_away_south_of_laplacian hL hp v
  have hcauchy : -‖dFv - (10 ^ 10 : ℝ) • dnv‖ * ‖dnv‖ ≤ inner ℝ (dFv - (10 ^ 10 : ℝ) • dnv) dnv :=
    by
    simpa only [neg_mul] using
      neg_le_of_abs_le (abs_real_inner_le_norm (dFv - (10 ^ 10 : ℝ) • dnv) dnv)
  have hdecompose : dFv = (10 ^ 10 : ℝ) • dnv + (dFv - (10 ^ 10 : ℝ) • dnv) := by module
  change 7000000000 * ‖dnv‖ ^ 2 ≤ inner ℝ dFv dnv
  rw [hdecompose, inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  nlinarith [norm_nonneg dnv]


-- @@ L8213-8389 unexpanded
/-- At the south pole, flatness of the original planar representative makes the contact-map
differential exactly the constant support value times the Gauss-map differential. -/
private theorem counterexampleTwoHomogeneousGradient_fderiv_south :
    let F := SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
    fderiv ℝ (fun z : ℂ ↦ F (counterexampleSphereChart z)) 0 =
      (10 ^ 10 : ℝ) •
        fderiv ℝ (fun z : ℂ ↦ (counterexampleSphereChart z : ℝ³)) 0 := by
  let u := counterexample 2
  let H := SphereSupport.radialExtension counterexampleTwoSphereExtension
  let F := SphereSupport.homogeneousGradient H
  let ρs := counterexampleSphereChart
  let ρ : ℂ → ℝ³ := fun z ↦ (ρs z : ℝ³)
  let p := ρs 0
  let dρ : ℂ →L[ℝ] ℝ³ := fderiv ℝ ρ 0
  let dF : ℂ →L[ℝ] ℝ³ := fderiv ℝ (fun z ↦ F (ρs z)) 0
  have hρsmooth : ContDiff ℝ ∞ ρ := by
    exact (contMDiff_coe_sphere.comp counterexampleSphereChart_contMDiff).contDiff
  have hFchartSmooth : ContDiff ℝ ∞ (fun z ↦ F (ρs z)) := by
    exact (counterexampleTwoHomogeneousGradient_contMDiff.comp
      counterexampleSphereChart_contMDiff).contDiff
  have hDρsmooth : ContDiff ℝ ∞ (fun z ↦ fderiv ℝ ρ z) :=
    hρsmooth.fderiv_right (m := ∞) (by simp)
  have huSmooth : ContDiff ℝ ∞ u := counterexample_contDiff 2 (by omega)
  have hDuSmooth : ContDiff ℝ ∞ (fun z ↦ fderiv ℝ u z) :=
    huSmooth.fderiv_right (m := ∞) (by simp)
  have hρrange : dρ.range = (ℝ ∙ (p : ℝ³))ᗮ := by
    simpa only [ρ, ρs, p, dρ] using range_fderiv_counterexampleSphereChart_zero
  have hpH : DifferentiableAt ℝ H (p : ℝ³) :=
    counterexampleTwoRadialExtension_differentiableAt p
  have hpcontact : inner ℝ (F p) (p : ℝ³) = (10 : ℝ) ^ 10 := by
    calc
      inner ℝ (F p) (p : ℝ³) = H p :=
        SphereSupport.inner_homogeneousGradient H p hpH
          (fun t ht ↦ SphereSupport.radialExtension_smul_of_pos _ _ ht)
      _ = counterexampleTwoSphereExtension p := SphereSupport.radialExtension_coe _ _
      _ = u 0 := by
        dsimp only [p, ρs, u]
        rw [counterexampleTwoSphereExtension_chart]
      _ = (10 : ℝ) ^ 10 := counterexample_zero 2
  have hpullback : H ∘ ρ = u := by
    funext z
    dsimp only [Function.comp_apply, H, ρ, ρs, u]
    rw [SphereSupport.radialExtension_coe, counterexampleTwoSphereExtension_chart]
  have hfirstIdentity (z b : ℂ) :
      inner ℝ (F (ρs z)) (fderiv ℝ ρ z b) = fderiv ℝ u z b := by
    have hHz : DifferentiableAt ℝ H (ρ z) := by
      simpa only [ρ] using counterexampleTwoRadialExtension_differentiableAt (ρs z)
    have hchain := hHz.hasFDerivAt.comp z
      (hρsmooth.differentiable (by simp) z).hasFDerivAt
    rw [hpullback] at hchain
    calc
      inner ℝ (F (ρs z)) (fderiv ℝ ρ z b) =
          fderiv ℝ H (ρ z) (fderiv ℝ ρ z b) := by
        dsimp only [F]
        rw [SphereSupport.homogeneousGradient, inner_gradient_left]
      _ = fderiv ℝ u z b := congr($hchain.fderiv b).symm
  have hnormalIdentity (z b : ℂ) :
      inner ℝ (ρ z) (fderiv ℝ ρ z b) = 0 := by
    have hnorm : (fun y : ℂ ↦ ‖ρ y‖ ^ 2) = fun _ ↦ (1 : ℝ) := by
      funext y
      rw [norm_eq_of_mem_sphere (ρs y)]
      norm_num
    have hderiv : fderiv ℝ (fun y : ℂ ↦ ‖ρ y‖ ^ 2) z b = 0 := by
      rw [hnorm]
      simp
    have hformula :=
      ((hρsmooth.differentiable (by simp) z).hasFDerivAt.norm_sq).fderiv
    rw [hformula] at hderiv
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
      innerSL_apply_apply] at hderiv
    rw [two_smul] at hderiv
    linarith
  have hdu0 : fderiv ℝ u 0 = 0 := counterexample_fderiv_zero 2 (by omega)
  have hnormalP (a : ℂ) : inner ℝ (p : ℝ³) (dρ a) = 0 := by
    simpa only [p, ρ, ρs, dρ] using hnormalIdentity 0 a
  have hFp : F p = (10 ^ 10 : ℝ) • (p : ℝ³) := by
    let G : ℝ³ := (10 ^ 10 : ℝ) • (p : ℝ³)
    have hradial : inner ℝ (F p - G) (p : ℝ³) = 0 := by
      dsimp only [G]
      rw [inner_sub_left, hpcontact, real_inner_smul_left,
        real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p]
      norm_num
    have hmem : F p - G ∈ dρ.range := by
      rw [hρrange, Submodule.mem_orthogonal_singleton_iff_inner_left]
      exact hradial
    obtain ⟨a, ha⟩ := hmem
    have htangent : inner ℝ (F p - G) (dρ a) = 0 := by
      dsimp only [G]
      rw [inner_sub_left, real_inner_smul_left]
      have hfirst := hfirstIdentity 0 a
      change inner ℝ (F p) (dρ a) - (10 ^ 10 : ℝ) * inner ℝ (p : ℝ³) (dρ a) = 0
      rw [hfirst, hdu0]
      simp [hnormalP]
    rw [← ha] at htangent
    have htangent' : inner ℝ (dρ a) (dρ a) = 0 := htangent
    rw [real_inner_self_eq_norm_sq] at htangent'
    have haZero : dρ a = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp htangent')
    have hzero : F p - G = 0 := by
      rw [← ha]
      exact haZero
    exact sub_eq_zero.mp hzero
  have hsecondU : fderiv ℝ (fun z ↦ fderiv ℝ u z) 0 = 0 :=
    counterexample_fderiv_fderiv_zero 2 (by omega)
  apply ContinuousLinearMap.ext
  intro a
  have hradial : inner ℝ (dF a - (10 ^ 10 : ℝ) • dρ a) (p : ℝ³) = 0 := by
    have hcontactFunction : (fun z ↦ inner ℝ (F (ρs z)) (ρ z)) = u := by
      funext z
      calc
        inner ℝ (F (ρs z)) (ρ z) = H (ρs z) :=
          SphereSupport.inner_homogeneousGradient H (ρs z)
            (counterexampleTwoRadialExtension_differentiableAt (ρs z))
            (fun t ht ↦ SphereSupport.radialExtension_smul_of_pos _ _ ht)
        _ = u z := by
          dsimp only [H, u]
          rw [SphereSupport.radialExtension_coe, counterexampleTwoSphereExtension_chart]
    have hderiv : fderiv ℝ (fun z ↦ inner ℝ (F (ρs z)) (ρ z)) 0 a = 0 := by
      rw [hcontactFunction, hdu0]
      simp
    rw [fderiv_inner_apply ℝ (hFchartSmooth.differentiable (by simp) 0)
      (hρsmooth.differentiable (by simp) 0) a] at hderiv
    change inner ℝ (F p) (dρ a) + inner ℝ (dF a) (p : ℝ³) = 0 at hderiv
    rw [hFp, real_inner_smul_left, hnormalIdentity 0 a, mul_zero, zero_add] at hderiv
    have hnormalRight : inner ℝ (dρ a) (p : ℝ³) = 0 := by
      rw [real_inner_comm]
      exact hnormalP a
    rw [inner_sub_left, real_inner_smul_left, hnormalRight, mul_zero, sub_zero]
    exact hderiv
  have hmem : dF a - (10 ^ 10 : ℝ) • dρ a ∈ dρ.range := by
    rw [hρrange, Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact hradial
  obtain ⟨b, hb⟩ := hmem
  have htangent : inner ℝ (dF a - (10 ^ 10 : ℝ) • dρ a) (dρ b) = 0 := by
    have hidentity : (fun z ↦ inner ℝ (F (ρs z)) (fderiv ℝ ρ z b)) =
        fun z ↦ fderiv ℝ u z b := by
      funext z
      exact hfirstIdentity z b
    have hDρb : ContDiff ℝ ∞ (fun z ↦ fderiv ℝ ρ z b) :=
      hDρsmooth.clm_apply (show ContDiff ℝ ∞ (fun _ : ℂ ↦ b) from contDiff_const)
    have hleft := fderiv_inner_apply ℝ
      (hFchartSmooth.differentiable (by simp) 0)
      (hDρb.differentiable (by simp) 0) a
    have hright : fderiv ℝ (fun z ↦ fderiv ℝ u z b) 0 a = 0 := by
      rw [fderiv_clm_apply (hDuSmooth.differentiable (by simp) 0)
        (differentiableAt_const b : DifferentiableAt ℝ (fun _ : ℂ ↦ b) 0)]
      rw [hsecondU]
      simp
    have hderivIdentity :
        fderiv ℝ (fun z ↦ inner ℝ (F (ρs z)) (fderiv ℝ ρ z b)) 0 a = 0 := by
      rw [hidentity, hright]
    rw [hleft] at hderivIdentity
    have hnormalFunction : (fun z ↦ inner ℝ (ρ z) (fderiv ℝ ρ z b)) = fun _ ↦ 0 := by
      funext z
      exact hnormalIdentity z b
    have hnormalDerivative :
        inner ℝ (p : ℝ³) (fderiv ℝ (fun z ↦ fderiv ℝ ρ z b) 0 a) +
          inner ℝ (dρ a) (dρ b) = 0 := by
      have hzero : fderiv ℝ (fun z ↦ inner ℝ (ρ z) (fderiv ℝ ρ z b)) 0 a = 0 := by
        rw [hnormalFunction]
        simp
      rw [fderiv_inner_apply ℝ (hρsmooth.differentiable (by simp) 0)
        (hDρb.differentiable (by simp) 0) a] at hzero
      exact hzero
    change inner ℝ (F p) (fderiv ℝ (fun z ↦ fderiv ℝ ρ z b) 0 a) +
      inner ℝ (dF a) (dρ b) = 0 at hderivIdentity
    rw [hFp, real_inner_smul_left] at hderivIdentity
    rw [inner_sub_left, real_inner_smul_left]
    linarith
  rw [← hb] at htangent
  have htangent' : inner ℝ (dρ b) (dρ b) = 0 := htangent
  rw [real_inner_self_eq_norm_sq] at htangent'
  have hbZero : dρ b = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp htangent')
  have hzero : dF a - (10 ^ 10 : ℝ) • dρ a = 0 := by
    rw [← hb]
    exact hbZero
  exact sub_eq_zero.mp hzero


-- @@ L8391-8441 unexpanded
/-- Intrinsic form of the exact south-pole radius identity. -/
private theorem counterexampleTwoHomogeneousGradient_mfderiv_south :
    let F := SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
    sphereAmbientMfderiv F (counterexampleSphereChart 0) =
      (10 ^ 10 : ℝ) • sphereAmbientMfderiv
        (fun p : sphere (0 : ℝ³) 1 ↦ (p : ℝ³)) (counterexampleSphereChart 0) := by
  let F := SphereSupport.homogeneousGradient
    (SphereSupport.radialExtension counterexampleTwoSphereExtension)
  let n : sphere (0 : ℝ³) 1 → ℝ³ := fun p ↦ (p : ℝ³)
  let dρ := mfderiv 𝓘(ℝ, ℂ) (𝓡 2) counterexampleSphereChart 0
  let dn : TangentSpace (𝓡 2) (counterexampleSphereChart 0) →L[ℝ] ℝ³ :=
    sphereAmbientMfderiv n (counterexampleSphereChart 0)
  let dF : TangentSpace (𝓡 2) (counterexampleSphereChart 0) →L[ℝ] ℝ³ :=
    sphereAmbientMfderiv F (counterexampleSphereChart 0)
  apply ContinuousLinearMap.ext
  intro v
  change dF v = (10 ^ 10 : ℝ) • dn v
  have hvRange : dn v ∈
      (fderiv ℝ (fun z : ℂ ↦ (counterexampleSphereChart z : ℝ³)) 0).range := by
    rw [range_fderiv_counterexampleSphereChart_zero,
      ← range_mvfderiv_subtypeVal (n := 2) (counterexampleSphereChart 0)]
    exact ⟨v, rfl⟩
  obtain ⟨a, ha⟩ := hvRange
  have hρmd : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓡 2) counterexampleSphereChart 0 :=
    counterexampleSphereChart_contMDiff.mdifferentiableAt (by simp)
  have hNmd : MDifferentiableAt (𝓡 2) (𝓡 3) n
      (counterexampleSphereChart 0) :=
    (contMDiff_coe_sphere (m := ∞)).mdifferentiableAt (by simp)
  have hFmd : MDifferentiableAt (𝓡 2) (𝓡 3) F
      (counterexampleSphereChart 0) :=
    counterexampleTwoHomogeneousGradient_contMDiff.mdifferentiableAt (by simp)
  have hchainN := mfderiv_comp_apply 0 hNmd hρmd a
  have hchainF := mfderiv_comp_apply 0 hFmd hρmd a
  rw [mfderiv_eq_fderiv] at hchainN hchainF
  change fderiv ℝ (fun z : ℂ ↦ (counterexampleSphereChart z : ℝ³)) 0 a =
    dn (dρ a) at hchainN
  change fderiv ℝ (fun z : ℂ ↦ F (counterexampleSphereChart z)) 0 a =
    dF (dρ a) at hchainF
  have haTangent : dρ a = v := by
    apply injective_mvfderiv_subtypeVal_sphere (counterexampleSphereChart 0)
    change dn (dρ a) = dn v
    rw [← hchainN]
    change (fderiv ℝ (fun z : ℂ ↦ (counterexampleSphereChart z : ℝ³)) 0) a = dn v at ha
    exact ha
  have hsouth := congr($counterexampleTwoHomogeneousGradient_fderiv_south a)
  change fderiv ℝ (fun z : ℂ ↦ F (counterexampleSphereChart z)) 0 a =
      (10 ^ 10 : ℝ) •
        fderiv ℝ (fun z : ℂ ↦ (counterexampleSphereChart z : ℝ³)) 0 a at hsouth
  rw [← haTangent, ← hchainN, ← hchainF]
  exact hsouth


-- @@ L8443-8506 unexpanded
/-- Pulling an intrinsic umbilic equation through the reciprocal chart kills the anti-linear
coefficient of the chart radius tensor. -/
private theorem sphericalTraceFreeHessian_eq_zero_of_umbilic_reciprocal
    (w : ℂ)
    (humbilic : ∃ c : ℝ,
      sphereAmbientMfderiv
        (fun p : sphere (0 : ℝ³) 1 ↦ (p : ℝ³))
        (counterexampleTwoReciprocalSphereChart w) =
      c • sphereAmbientMfderiv
        (SphereSupport.homogeneousGradient
          (SphereSupport.radialExtension counterexampleTwoSphereExtension))
        (counterexampleTwoReciprocalSphereChart w)) :
    sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w = 0 := by
  let F := SphereSupport.homogeneousGradient
    (SphereSupport.radialExtension counterexampleTwoSphereExtension)
  let ρ := counterexampleTwoReciprocalSphereChart
  let dρ : ℂ →L[ℝ] ℝ³ := fderiv ℝ (fun z : ℂ ↦ (ρ z : ℝ³)) w
  let dF : ℂ →L[ℝ] ℝ³ := fderiv ℝ (fun z : ℂ ↦ F (ρ z)) w
  let A : ℂ := (counterexampleTwoReciprocal w - 10 ^ 10 : ℝ)
  let L : ℂ := chartLaplacian counterexampleTwoReciprocal w
  let Q : ℂ := sphericalTraceFreeHessian 10000 counterexampleTwoReciprocal w
  let r : ℝ := (‖w‖ ^ 2 + 10000) ^ 2 / 80000
  have hdρ : Function.Injective dρ := by
    intro a b hab
    have hscale := (counterexampleTwoReciprocalSphereChart_conformal w (a - b) (a - b)).2
    change ‖dρ (a - b)‖ = 200 / (‖w‖ ^ 2 + 10000) * ‖a - b‖ at hscale
    rw [map_sub, hab, sub_self, norm_zero] at hscale
    have hpositive : 0 < 200 / (‖w‖ ^ 2 + 10000) := by positivity
    have hnormzero : ‖a - b‖ = 0 := by nlinarith [norm_nonneg (a - b)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnormzero)
  have hformula (a : ℂ) : dF a - (10 ^ 10 : ℝ) • dρ a =
      dρ (A * a + r • (L * a + Q * star a)) := by
    exact counterexampleTwoReciprocal_radius_formula w a
  have hchartUmbilic : ∃ c : ℝ, dρ = c • dF := by
    obtain ⟨c, hc⟩ := humbilic
    refine ⟨c, ?_⟩
    apply ContinuousLinearMap.ext
    intro a
    let dchart := mfderiv 𝓘(ℝ, ℂ) (𝓡 2) ρ w
    let dn : TangentSpace (𝓡 2) (ρ w) →L[ℝ] ℝ³ :=
      sphereAmbientMfderiv (fun p : sphere (0 : ℝ³) 1 ↦ (p : ℝ³)) (ρ w)
    let dFintrinsic : TangentSpace (𝓡 2) (ρ w) →L[ℝ] ℝ³ :=
      sphereAmbientMfderiv F (ρ w)
    have hρmd : MDifferentiableAt 𝓘(ℝ, ℂ) (𝓡 2) ρ w :=
      counterexampleTwoReciprocalSphereChart_contMDiff.mdifferentiableAt (by simp)
    have hNmd : MDifferentiableAt (𝓡 2) (𝓡 3)
        (fun p : sphere (0 : ℝ³) 1 ↦ (p : ℝ³)) (ρ w) :=
      (contMDiff_coe_sphere (m := ∞)).mdifferentiableAt (by simp)
    have hFmd : MDifferentiableAt (𝓡 2) (𝓡 3) F (ρ w) :=
      counterexampleTwoHomogeneousGradient_contMDiff.mdifferentiableAt (by simp)
    have hchainN := mfderiv_comp_apply w hNmd hρmd a
    have hchainF := mfderiv_comp_apply w hFmd hρmd a
    rw [mfderiv_eq_fderiv] at hchainN hchainF
    change dρ a = dn (dchart a) at hchainN
    change dF a = dFintrinsic (dchart a) at hchainF
    have hcApply := congr($hc (dchart a))
    change dn (dchart a) = c • dFintrinsic (dchart a) at hcApply
    rw [ContinuousLinearMap.smul_apply]
    calc
      dρ a = dn (dchart a) := hchainN
      _ = c • dFintrinsic (dchart a) := hcApply
      _ = c • dF a := by rw [hchainF]
  exact antiLinearCoefficient_eq_zero_of_umbilic dρ dF hdρ (10 ^ 10) r A L Q
    (by positivity) hformula hchartUmbilic


-- @@ L8508-8530 unexpanded
/-- The reciprocal radius estimate and the exact south-pole identity combine into global
oriented coercivity. -/
private theorem counterexampleTwo_radius_coercive_of_laplacian
    (hL : ∀ w : ℂ, |chartLaplacian counterexampleTwoReciprocal w| ≤
      8 * counterexampleTwoReciprocalDamping w) :
    ∀ (p : sphere (0 : ℝ³) 1) (v : TangentSpace (𝓡 2) p),
      7000000000 * ‖sphereAmbientMfderiv
          (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v‖ ^ 2 ≤
        inner ℝ
          (sphereAmbientMfderiv (SphereSupport.homogeneousGradient
            (SphereSupport.radialExtension counterexampleTwoSphereExtension)) p v)
          (sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v) := by
  intro p v
  by_cases hp : p = counterexampleSphereChart 0
  · subst p
    have hsouth := congr($counterexampleTwoHomogeneousGradient_mfderiv_south v)
    rw [hsouth]
    simp only [ContinuousLinearMap.smul_apply, real_inner_smul_left,
      real_inner_self_eq_norm_sq]
    nlinarith [sq_nonneg
      ‖sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³))
        (counterexampleSphereChart 0) v‖]
  · exact counterexampleTwo_radius_coercive_away_south_of_laplacian hL hp v


-- @@ L8532-8543 verbatim
/-- The half-space body cut out by the explicit extension is compact, convex, and
three-dimensional. -/
private theorem counterexampleTwoBody_geometry :
    Convex ℝ (SphereSupport.body counterexampleTwoSphereExtension) ∧
      IsCompact (SphereSupport.body counterexampleTwoSphereExtension) ∧
      (interior (SphereSupport.body counterexampleTwoSphereExtension)).Nonempty := by
  refine ⟨SphereSupport.body_convex _,
    SphereSupport.body_isCompact_of_continuous _
      (counterexampleTwoSphereExtension_contMDiff_of_contMDiffAt_north
        counterexampleTwoSphereExtension_contMDiffAt_north).continuous,
    SphereSupport.body_interior_nonempty _ zero_lt_one ?_⟩
  exact counterexampleTwoSphereExtension_lower


-- @@ L8545-8563 expanded
/-- Membership in the half-space body gives the homogeneous support inequality in every ambient
direction. -/
private theorem inner_le_counterexampleTwoRadialExtension_of_mem_body {x : EuclideanSpace ℝ (Fin 3)}
    (hx : x ∈ SphereSupport.body counterexampleTwoSphereExtension) (y : EuclideanSpace ℝ (Fin 3)) :
    inner ℝ x y ≤ SphereSupport.radialExtension counterexampleTwoSphereExtension y :=
  by
  by_cases hy : y = 0
  · simp [hy, SphereSupport.radialExtension]
  · let q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := ⟨‖y‖⁻¹ • y, by simp [norm_smul, hy]⟩
    have hq : inner ℝ (q : EuclideanSpace ℝ (Fin 3)) x ≤ counterexampleTwoSphereExtension q := hx q
    have hscale : ‖y‖ * inner ℝ (q : EuclideanSpace ℝ (Fin 3)) x = inner ℝ x y :=
      by
      change ‖y‖ * inner ℝ (‖y‖⁻¹ • y) x = inner ℝ x y
      rw [real_inner_smul_left, real_inner_comm]
      field_simp [norm_ne_zero_iff.mpr hy]
    calc
      inner ℝ x y = ‖y‖ * inner ℝ (q : EuclideanSpace ℝ (Fin 3)) x := hscale.symm
      _ ≤ ‖y‖ * counterexampleTwoSphereExtension q := (mul_le_mul_of_nonneg_left hq (norm_nonneg y))
      _ = SphereSupport.radialExtension counterexampleTwoSphereExtension y := by
        rw [SphereSupport.radialExtension, dif_neg hy]


-- @@ L8565-8576 expanded
/-- Differentiability of the homogeneous extension makes each exposed contact face a singleton. -/
private theorem eq_counterexampleTwoSupportPoint {p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1}
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ SphereSupport.body counterexampleTwoSphereExtension)
    (hface : inner ℝ (p : EuclideanSpace ℝ (Fin 3)) x = counterexampleTwoSphereExtension p)
    (hH :
      DifferentiableAt ℝ (SphereSupport.radialExtension counterexampleTwoSphereExtension)
        (p : EuclideanSpace ℝ (Fin 3))) :
    x =
      SphereSupport.homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension) p :=
  by
  apply
    SphereSupport.eq_homogeneousGradient_of_global_support _ p x hH
      (inner_le_counterexampleTwoRadialExtension_of_mem_body hx)
  simpa [real_inner_comm] using hface


-- @@ L8578-8614 expanded
/-- Convexity and differentiability of the degree-one extension supply the complete
set-theoretic support parametrization. The remaining geometric work is to verify these analytic
hypotheses and the differential properties of the resulting gradient map. -/
private theorem counterexampleTwoSupport_body_of_convex_radialExtension
    (hHdiff :
      ∀ p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        DifferentiableAt ℝ (SphereSupport.radialExtension counterexampleTwoSphereExtension)
          (p : EuclideanSpace ℝ (Fin 3)))
    (hconvex : ConvexOn ℝ univ (SphereSupport.radialExtension counterexampleTwoSphereExtension)) :
    let F :=
      SphereSupport.homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension)
    range F = frontier (SphereSupport.body counterexampleTwoSphereExtension) ∧
      IsSupportParametrization counterexampleTwoSphereExtension F
        (SphereSupport.body counterexampleTwoSphereExtension) :=
  by
  let F :=
    SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
  have hcontact :
    ∀ p, inner ℝ (F p) (p : EuclideanSpace ℝ (Fin 3)) = counterexampleTwoSphereExtension p :=
    by
    intro p
    simpa [F] using
      SphereSupport.inner_homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension) p (hHdiff p)
        (fun t ht ↦ SphereSupport.radialExtension_smul_of_pos _ _ ht)
  have hcross :
    ∀ (p q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
      inner ℝ (F p) (q : EuclideanSpace ℝ (Fin 3)) ≤ counterexampleTwoSphereExtension q :=
    by
    intro p q
    simpa [F] using
      SphereSupport.inner_homogeneousGradient_le
        (SphereSupport.radialExtension counterexampleTwoSphereExtension) p
        (q : EuclideanSpace ℝ (Fin 3)) hconvex (hHdiff p)
        (fun t ht ↦ SphereSupport.radialExtension_smul_of_pos _ _ ht)
  have hstationary :
    ∀ (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (x : EuclideanSpace ℝ (Fin 3)),
      x ∈ SphereSupport.body counterexampleTwoSphereExtension →
        inner ℝ (p : EuclideanSpace ℝ (Fin 3)) x = counterexampleTwoSphereExtension p →
          ∀ v : EuclideanSpace ℝ (Fin 3),
            v ∈ (ℝ ∙ (p : EuclideanSpace ℝ (Fin 3)))ᗮ → inner ℝ (x - F p) v = 0 :=
    by
    intro p x hx hface v _
    rw [eq_counterexampleTwoSupportPoint hx hface (hHdiff p)]
    simp [F]
  exact
    ⟨SphereSupport.range_eq_frontier_of_first_variation _ F hcontact hcross
        counterexampleTwoBody_geometry.2.2 hstationary,
      SphereSupport.contact_mem_body _ F hcontact hcross⟩


-- @@ L8616-8691 unexpanded
/-- For the explicit radial extension, the homogeneous-gradient differential is tangent to the
sphere. This follows directly by differentiating Euler's identity and does not use support
convexity. -/
private theorem counterexampleTwoHomogeneousGradient_normal :
    ∀ (p : sphere (0 : ℝ³) 1) (v : TangentSpace (𝓡 2) p),
      inner ℝ (p : ℝ³)
        (sphereAmbientMfderiv (SphereSupport.homogeneousGradient
          (SphereSupport.radialExtension counterexampleTwoSphereExtension)) p v) = 0 := by
  let H := SphereSupport.radialExtension counterexampleTwoSphereExtension
  let G : ℝ³ → ℝ³ := gradient H
  let F := SphereSupport.homogeneousGradient H
  have hHsmooth : ContDiffOn ℝ ∞ H {0}ᶜ :=
    radialExtension_contDiffOn_compl_of_contMDiff counterexampleTwoSphereExtension
      (counterexampleTwoSphereExtension_contMDiff_of_contMDiffAt_north
        counterexampleTwoSphereExtension_contMDiffAt_north)
  have hGsmooth : ContDiffOn ℝ ∞ G {0}ᶜ := by
    have hDf : ContDiffOn ℝ ∞ (fderiv ℝ H) {0}ᶜ :=
      hHsmooth.fderiv_of_isOpen isOpen_compl_singleton (by simp)
    change ContDiffOn ℝ ∞ (gradient H) {0}ᶜ
    rw [show gradient H = (InnerProductSpace.toDual ℝ ℝ³).symm ∘ fderiv ℝ H by rfl]
    exact (InnerProductSpace.toDual ℝ ℝ³).symm.contDiff.comp_contDiffOn hDf
  have hEuler (x : ℝ³) (hx : x ≠ 0) : inner ℝ (G x) x = H x := by
    have hHdiff : DifferentiableAt ℝ H x :=
      (hHsmooth x hx).differentiableWithinAt (by simp) |>.differentiableAt
        (isOpen_compl_singleton.mem_nhds hx)
    dsimp only [G]
    rw [inner_gradient_left]
    have hline : HasDerivAt (fun t : ℝ ↦ H (x + t • x)) (fderiv ℝ H x x) 0 := by
      have harg : HasDerivAt (fun t : ℝ ↦ x + t • x) x 0 := by
        simpa only [id_eq, zero_add, one_smul] using
          ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const x).const_add x
      simpa [Function.comp_def] using
        hHdiff.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) harg (by simp)
    have heq : (fun t : ℝ ↦ H (x + t • x)) =ᶠ[nhds 0]
        fun t ↦ (1 + t) * H x := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with t ht
      rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
      calc
        H (x + t • x) = H ((1 + t) • x) := by rw [add_smul, one_smul]
        _ = (1 + t) * H x := SphereSupport.radialExtension_smul_of_pos _ _
          (by linarith [(abs_lt.mp ht).1])
    have hright : HasDerivAt (fun t : ℝ ↦ (1 + t) * H x) (H x) 0 := by
      simpa only [id_eq, one_mul] using
        ((hasDerivAt_id (𝕜 := ℝ) 0).const_add 1).mul_const (H x)
    exact (hline.congr_of_eventuallyEq heq.symm).unique hright
  intro p v
  have hp : (p : ℝ³) ≠ 0 := ne_zero_of_mem_unit_sphere p
  have hpG : DifferentiableAt ℝ G (p : ℝ³) :=
    (hGsmooth (p : ℝ³) hp).differentiableWithinAt (by simp) |>.differentiableAt
      (isOpen_compl_singleton.mem_nhds hp)
  have hpH : DifferentiableAt ℝ H (p : ℝ³) :=
    (hHsmooth (p : ℝ³) hp).differentiableWithinAt (by simp) |>.differentiableAt
      (isOpen_compl_singleton.mem_nhds hp)
  have hEulerEventually : (fun x : ℝ³ ↦ inner ℝ (G x) x) =ᶠ[nhds (p : ℝ³)] H := by
    filter_upwards [eventually_ne_nhds hp] with x hx
    exact hEuler x hx
  have hnormalAmbient (a : ℝ³) :
      inner ℝ (p : ℝ³) (fderiv ℝ G (p : ℝ³) a) = 0 := by
    have hderivEq := hEulerEventually.fderiv_eq (𝕜 := ℝ)
    have happ := congr($hderivEq a)
    change (fderiv ℝ (fun t : ℝ³ ↦ inner ℝ (G t) (id t)) (p : ℝ³)) a =
      (fderiv ℝ H (p : ℝ³)) a at happ
    rw [fderiv_inner_apply ℝ hpG differentiableAt_id a,
      inner_gradient_left] at happ
    simp only [fderiv_id, ContinuousLinearMap.id_apply, id_eq] at happ
    rw [real_inner_comm]
    linarith
  have hchain := mfderiv_comp_apply p
    (hpG.mdifferentiableAt)
    ((contMDiff_coe_sphere (m := ∞) p).mdifferentiableAt (by simp)) v
  rw [mfderiv_eq_fderiv] at hchain
  change sphereAmbientMfderiv F p v =
      fderiv ℝ G (p : ℝ³)
        (sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v) at hchain
  rw [hchain]
  exact hnormalAmbient _


-- @@ L8693-8838 unexpanded
/-- Intrinsic radius-tensor coercivity is the ambient Hessian lower bound for the degree-one
radial extension. Only the tangential component of the ambient direction contributes. -/
private theorem counterexampleTwoRadialExtension_hessian_coercive
    (hCoercive : ∀ (p : sphere (0 : ℝ³) 1) (v : TangentSpace (𝓡 2) p),
      7000000000 * ‖sphereAmbientMfderiv
          (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v‖ ^ 2 ≤
        inner ℝ
          (sphereAmbientMfderiv (SphereSupport.homogeneousGradient
            (SphereSupport.radialExtension counterexampleTwoSphereExtension)) p v)
          (sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p v))
    {x d : ℝ³} (hx : x ≠ 0) :
    let p : sphere (0 : ℝ³) 1 := ⟨‖x‖⁻¹ • x, by simp [norm_smul, hx]⟩
    let τ := d - inner ℝ d (p : ℝ³) • (p : ℝ³)
    7000000000 / ‖x‖ * ‖τ‖ ^ 2 ≤
      inner ℝ
        (fderiv ℝ
          (gradient (SphereSupport.radialExtension counterexampleTwoSphereExtension)) x d) d := by
  let H := SphereSupport.radialExtension counterexampleTwoSphereExtension
  let G : ℝ³ → ℝ³ := gradient H
  let F := SphereSupport.homogeneousGradient H
  let r := ‖x‖
  let p : sphere (0 : ℝ³) 1 := ⟨r⁻¹ • x, by simp [r, norm_smul, hx]⟩
  let τ : ℝ³ := d - inner ℝ d (p : ℝ³) • (p : ℝ³)
  have hr : 0 < r := norm_pos_iff.mpr hx
  have hHsmooth : ContDiffOn ℝ ∞ H {0}ᶜ :=
    radialExtension_contDiffOn_compl_of_contMDiff counterexampleTwoSphereExtension
      (counterexampleTwoSphereExtension_contMDiff_of_contMDiffAt_north
        counterexampleTwoSphereExtension_contMDiffAt_north)
  have hGsmooth : ContDiffOn ℝ ∞ G {0}ᶜ := by
    have hDf : ContDiffOn ℝ ∞ (fderiv ℝ H) {0}ᶜ :=
      hHsmooth.fderiv_of_isOpen isOpen_compl_singleton (by simp)
    change ContDiffOn ℝ ∞ (gradient H) {0}ᶜ
    rw [show gradient H = (InnerProductSpace.toDual ℝ ℝ³).symm ∘ fderiv ℝ H by rfl]
    exact (InnerProductSpace.toDual ℝ ℝ³).symm.contDiff.comp_contDiffOn hDf
  have hGscale (y : ℝ³) (hy : y ≠ 0) (a : ℝ) (ha : 0 < a) :
      G (a • y) = G y := by
    have hay : a • y ≠ 0 := smul_ne_zero ha.ne' hy
    have hyH : DifferentiableAt ℝ H y :=
      (hHsmooth y hy).differentiableWithinAt (by simp) |>.differentiableAt
        (isOpen_compl_singleton.mem_nhds hy)
    have hayH : DifferentiableAt ℝ H (a • y) :=
      (hHsmooth (a • y) hay).differentiableWithinAt (by simp) |>.differentiableAt
        (isOpen_compl_singleton.mem_nhds hay)
    apply ext_inner_right ℝ
    intro z
    dsimp only [G]
    rw [inner_gradient_left, inner_gradient_left]
    have harg : HasFDerivAt (fun z : ℝ³ ↦ a • z)
        (a • ContinuousLinearMap.id ℝ ℝ³) y := by fun_prop
    have hleft := hayH.hasFDerivAt.comp y harg
    change HasFDerivAt (fun z : ℝ³ ↦ H (a • z))
      ((fderiv ℝ H (a • y)).comp (a • ContinuousLinearMap.id ℝ ℝ³)) y at hleft
    have hright := hyH.hasFDerivAt.const_smul a
    have heq : (fun z : ℝ³ ↦ H (a • z)) = fun z ↦ a • H z := by
      funext z
      simpa only [smul_eq_mul] using SphereSupport.radialExtension_smul_of_pos
        counterexampleTwoSphereExtension z ha
    rw [heq] at hleft
    have hderivEq := hleft.unique hright
    have happ := congr($hderivEq z)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, map_smul, smul_eq_mul] at happ
    exact (mul_left_cancel₀ ha.ne' happ)
  have hp0 : (p : ℝ³) ≠ 0 := ne_zero_of_mem_unit_sphere p
  have hpG : DifferentiableAt ℝ G (p : ℝ³) :=
    (hGsmooth (p : ℝ³) hp0).differentiableWithinAt (by simp) |>.differentiableAt
      (isOpen_compl_singleton.mem_nhds hp0)
  have hxG : DifferentiableAt ℝ G x :=
    (hGsmooth x hx).differentiableWithinAt (by simp) |>.differentiableAt
      (isOpen_compl_singleton.mem_nhds hx)
  have hradialKernel : fderiv ℝ G (p : ℝ³) (p : ℝ³) = 0 := by
    have hline : HasDerivAt (fun t : ℝ ↦ G ((p : ℝ³) + t • (p : ℝ³)))
        (fderiv ℝ G (p : ℝ³) (p : ℝ³)) 0 := by
      have harg : HasDerivAt (fun t : ℝ ↦ (p : ℝ³) + t • (p : ℝ³))
          (p : ℝ³) 0 := by
        simpa only [id_eq, zero_add, one_smul] using
          ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const (p : ℝ³)).const_add (p : ℝ³)
      simpa [Function.comp_def] using
        hpG.hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) harg (by simp)
    have heq : (fun t : ℝ ↦ G ((p : ℝ³) + t • (p : ℝ³))) =ᶠ[nhds 0]
        fun _ ↦ G (p : ℝ³) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ) < 1)] with t ht
      rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at ht
      rw [show (p : ℝ³) + t • (p : ℝ³) = (1 + t) • (p : ℝ³) by
        rw [add_smul, one_smul]]
      exact hGscale (p : ℝ³) hp0 (1 + t) (by linarith [(abs_lt.mp ht).1])
    have hzero : HasDerivAt (fun _ : ℝ ↦ G (p : ℝ³)) 0 0 := hasDerivAt_const 0 _
    exact (hline.congr_of_eventuallyEq heq.symm).unique hzero
  have hscaleHessian (z : ℝ³) :
      fderiv ℝ G x z = r⁻¹ • fderiv ℝ G (p : ℝ³) z := by
    have hrp : r • (p : ℝ³) = x := by
      dsimp only [p]
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    have hxG' : DifferentiableAt ℝ G (r • (p : ℝ³)) := by
      simpa only [hrp] using hxG
    have harg : HasFDerivAt (fun y : ℝ³ ↦ r • y)
        (r • ContinuousLinearMap.id ℝ ℝ³) (p : ℝ³) := by fun_prop
    have hleft := hxG'.hasFDerivAt.comp (p : ℝ³) harg
    have heq : (fun y : ℝ³ ↦ G (r • y)) =ᶠ[nhds (p : ℝ³)] G := by
      filter_upwards [isOpen_compl_singleton.mem_nhds hp0] with y hy
      exact hGscale y hy r hr
    have hderivEq := (hleft.congr_of_eventuallyEq heq.symm).unique hpG.hasFDerivAt
    have happ := congr($hderivEq (r⁻¹ • z))
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_smul, inv_mul_cancel₀ hr.ne', one_smul,
      map_smul] at happ
    simpa only [hrp] using happ
  have hτ : τ ∈ (ℝ ∙ (p : ℝ³))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    dsimp only [τ]
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
      norm_eq_of_mem_sphere p]
    ring
  rw [← range_mvfderiv_subtypeVal (n := 2) p] at hτ
  obtain ⟨v, hv⟩ := hτ
  let dn : TangentSpace (𝓡 2) p →L[ℝ] ℝ³ :=
    sphereAmbientMfderiv (fun q : sphere (0 : ℝ³) 1 ↦ (q : ℝ³)) p
  let dF : TangentSpace (𝓡 2) p →L[ℝ] ℝ³ :=
    sphereAmbientMfderiv F p
  have hchain := mfderiv_comp_apply p hpG.mdifferentiableAt
    ((contMDiff_coe_sphere (m := ∞) p).mdifferentiableAt (by simp)) v
  rw [mfderiv_eq_fderiv] at hchain
  change dF v = fderiv ℝ G (p : ℝ³) (dn v) at hchain
  have hv' : dn v = τ := by
    change dn v = τ at hv
    exact hv
  have hddecomp : d = inner ℝ d (p : ℝ³) • (p : ℝ³) + τ := by
    dsimp only [τ]
    module
  have hGp_d : fderiv ℝ G (p : ℝ³) d = dF v := by
    rw [hddecomp, map_add, map_smul, hradialKernel, smul_zero, zero_add, ← hv', ← hchain]
  have hnormal : inner ℝ (dF v) (p : ℝ³) = 0 := by
    rw [real_inner_comm]
    exact counterexampleTwoHomogeneousGradient_normal p v
  have hinner : inner ℝ (fderiv ℝ G x d) d =
      r⁻¹ * inner ℝ (dF v) (dn v) := by
    rw [hscaleHessian, hGp_d, hddecomp, inner_add_right]
    simp only [real_inner_smul_left, real_inner_smul_right, hnormal, mul_zero, zero_add]
    rw [← hv']
  rw [hinner]
  have hbase := hCoercive p v
  have hrinv : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
  calc
    7000000000 / ‖x‖ * ‖τ‖ ^ 2 =
        r⁻¹ * (7000000000 * ‖dn v‖ ^ 2) := by rw [← hv']; dsimp only [r]; ring
    _ ≤ r⁻¹ * inner ℝ (dF v) (dn v) := mul_le_mul_of_nonneg_left hbase hrinv


-- @@ L8840-8876 expanded
/-- Contact and cross-support represent the homogeneous extension as a supremum of linear
functionals, and therefore make it convex. -/
private theorem counterexampleTwoRadialExtension_convex_of_cross
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (hcontact :
      ∀ p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        inner ℝ (F p) (p : EuclideanSpace ℝ (Fin 3)) = counterexampleTwoSphereExtension p)
    (hcross :
      ∀ (p q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
        inner ℝ (F p) (q : EuclideanSpace ℝ (Fin 3)) ≤ counterexampleTwoSphereExtension q) :
    ConvexOn ℝ univ (SphereSupport.radialExtension counterexampleTwoSphereExtension) :=
  by
  have hFbody : ∀ p, F p ∈ SphereSupport.body counterexampleTwoSphereExtension := fun p ↦
    (SphereSupport.contact_mem_body counterexampleTwoSphereExtension F hcontact hcross p).1
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  by_cases hz : a • x + b • y = 0
  · rw [hz]
    simp only [SphereSupport.radialExtension, smul_eq_mul]
    exact
      add_nonneg (mul_nonneg ha (counterexampleTwoRadialExtension_nonneg x))
        (mul_nonneg hb (counterexampleTwoRadialExtension_nonneg y))
  · let q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
      ⟨‖a • x + b • y‖⁻¹ • (a • x + b • y), by
        rw [mem_sphere]
        simp only [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
          inv_mul_cancel₀ (norm_ne_zero_iff.mpr hz)]⟩
    have hrepresentation :
      SphereSupport.radialExtension counterexampleTwoSphereExtension (a • x + b • y) =
        inner ℝ (F q) (a • x + b • y) :=
      by
      rw [SphereSupport.radialExtension, dif_neg hz]
      change ‖a • x + b • y‖ * counterexampleTwoSphereExtension q = _
      rw [← hcontact q, real_inner_smul_right]
      field_simp [norm_ne_zero_iff.mpr hz]
    rw [hrepresentation, inner_add_right, real_inner_smul_right, real_inner_smul_right, smul_eq_mul]
    exact
      add_le_add
        (mul_le_mul_of_nonneg_left
          (inner_le_counterexampleTwoRadialExtension_of_mem_body (hFbody q) x) ha)
        (mul_le_mul_of_nonneg_left
          (inner_le_counterexampleTwoRadialExtension_of_mem_body (hFbody q) y) hb)


-- @@ L8878-8892 verbatim
/-- Positive oriented coercivity relative to an injective reference map implies injectivity. -/
private theorem continuousLinearMap_injective_of_coercive
    {E F : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (N L : E →L[ℝ] F)
    (hN : Function.Injective N) {c : ℝ} (hc : 0 < c)
    (hL : ∀ v, c * ‖N v‖ ^ 2 ≤ inner ℝ (L v) (N v)) : Function.Injective L := by
  intro v w hvw
  have hzero : L (v - w) = 0 := by rw [map_sub, hvw, sub_self]
  have hbound := hL (v - w)
  rw [hzero, inner_zero_left] at hbound
  have hnormsq : ‖N (v - w)‖ ^ 2 = 0 := by
    nlinarith [sq_nonneg ‖N (v - w)‖]
  have : N (v - w) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnormsq)
  rw [map_sub] at this
  exact hN (sub_eq_zero.mp this)


-- @@ L8894-8935 expanded
/-- Normality and oriented coercivity identify the differential range of the contact immersion
with the tangent plane supplied by the Gauss map. -/
private theorem counterexampleTwoHomogeneousGradient_range_eq_of_coercive
    (hCoercive :
      ∀ (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (v : TangentSpace (𝓡 2) p),
        7000000000 *
            ‖sphereAmbientMfderiv
                  (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3)))
                  p v‖ ^
              2 ≤
          inner ℝ
            (sphereAmbientMfderiv
              (SphereSupport.homogeneousGradient
                (SphereSupport.radialExtension counterexampleTwoSphereExtension))
              p v)
            (sphereAmbientMfderiv
              (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
              v))
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    (sphereAmbientMfderiv
          (SphereSupport.homogeneousGradient
            (SphereSupport.radialExtension counterexampleTwoSphereExtension))
          p).range =
      (sphereAmbientMfderiv
          (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3)))
          p).range :=
  by
  let F :=
    SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
  let n : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3) := fun q ↦
    (q : EuclideanSpace ℝ (Fin 3))
  let dF := sphereAmbientMfderiv F p
  let dn := sphereAmbientMfderiv n p
  change dF.range = dn.range
  have hdnInjective : Function.Injective dn :=
    by
    dsimp only [dn, n, sphereAmbientMfderiv]
    exact injective_mvfderiv_subtypeVal_sphere p
  have hdFInjective : Function.Injective dF :=
    by
    apply
      continuousLinearMap_injective_of_coercive dn dF hdnInjective (c := 7000000000) (by norm_num)
    intro v
    simpa only [dF, dn, F, n] using hCoercive p v
  have hdF_le_dn : dF.range ≤ dn.range :=
    by
    rw [show dn.range = (ℝ ∙ (p : EuclideanSpace ℝ (Fin 3)))ᗮ
        by
        dsimp only [dn, n, sphereAmbientMfderiv]
        exact range_mvfderiv_subtypeVal p]
    rintro _ ⟨v, rfl⟩
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    change inner ℝ (p : EuclideanSpace ℝ (Fin 3)) (sphereAmbientMfderiv F p v) = 0
    exact counterexampleTwoHomogeneousGradient_normal p v
  apply Submodule.eq_of_le_of_finrank_eq hdF_le_dn
  calc
    Module.finrank ℝ dF.range = Module.finrank ℝ (TangentSpace (𝓡 2) p) :=
      LinearMap.finrank_range_of_inj hdFInjective
    _ = Module.finrank ℝ dn.range := (LinearMap.finrank_range_of_inj hdnInjective).symm


-- @@ L8937-8962 expanded
/-- Positive oriented coercivity makes the canonical cross-product normal of the support
parametrization equal to its radial normal. -/
private theorem counterexampleTwoHomogeneousGradient_sphereNormal_of_coercive
    (hCoercive :
      ∀ (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (v : TangentSpace (𝓡 2) p),
        7000000000 *
            ‖sphereAmbientMfderiv
                  (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3)))
                  p v‖ ^
              2 ≤
          inner ℝ
            (sphereAmbientMfderiv
              (SphereSupport.homogeneousGradient
                (SphereSupport.radialExtension counterexampleTwoSphereExtension))
              p v)
            (sphereAmbientMfderiv
              (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
              v)) :
    let F :=
      SphereSupport.homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension)
    sphereNormal F = fun p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦
      (p : EuclideanSpace ℝ (Fin 3)) :=
  by
  let F :=
    SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
  funext p
  apply sphereNormal_eq_radial_of_coercive F p 7000000000 (by norm_num)
  · intro v
    change inner ℝ (p : EuclideanSpace ℝ (Fin 3)) (sphereAmbientMfderiv F p v) = 0
    exact counterexampleTwoHomogeneousGradient_normal p v
  · intro v
    change
      7000000000 *
          ‖sphereAmbientMfderiv
                (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
                v‖ ^
            2 ≤
        inner ℝ (sphereAmbientMfderiv F p v)
          (sphereAmbientMfderiv
            (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p v)
    exact hCoercive p v


-- @@ L8964-8988 expanded
/-- The south pole is an umbilic for the canonical cross-product normal. -/
private theorem counterexampleTwoHomogeneousGradient_umbilic_south_of_coercive
    (hCoercive :
      ∀ (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (v : TangentSpace (𝓡 2) p),
        7000000000 *
            ‖sphereAmbientMfderiv
                  (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3)))
                  p v‖ ^
              2 ≤
          inner ℝ
            (sphereAmbientMfderiv
              (SphereSupport.homogeneousGradient
                (SphereSupport.radialExtension counterexampleTwoSphereExtension))
              p v)
            (sphereAmbientMfderiv
              (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
              v)) :
    let F :=
      SphereSupport.homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension)
    EuclideanHypersurface.IsUmbilic (TangentSpace (𝓡 2) (counterexampleSphereChart 0))
      (EuclideanSpace ℝ (Fin 3)) (sphereAmbientMfderiv F (counterexampleSphereChart 0))
      (sphereAmbientMfderiv (sphereNormal F) (counterexampleSphereChart 0)) :=
  by
  let F :=
    SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
  have hnormal := counterexampleTwoHomogeneousGradient_sphereNormal_of_coercive hCoercive
  change
    sphereNormal F = fun p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦
      (p : EuclideanSpace ℝ (Fin 3)) at hnormal
  apply EuclideanHypersurface.isUmbilic_of_normal_deriv_eq_smul
  rw [hnormal]
  change
    sphereAmbientMfderiv
        (fun p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (p : EuclideanSpace ℝ (Fin 3)))
        (counterexampleSphereChart 0) =
      (10 ^ 10 : ℝ)⁻¹ • sphereAmbientMfderiv F (counterexampleSphereChart 0)
  rw [counterexampleTwoHomogeneousGradient_mfderiv_south]
  rw [smul_smul, inv_mul_cancel₀ (by norm_num : (10 ^ 10 : ℝ) ≠ 0), one_smul]


-- @@ L8990-9025 expanded
/-- Every point other than the south pole is nonumbilic in the fundamental-form sense, because
the reciprocal chart covers it and its spherical trace-free Hessian is nowhere zero. -/
private theorem counterexampleTwoHomogeneousGradient_not_umbilic_away_south
    (hCoercive :
      ∀ (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (v : TangentSpace (𝓡 2) p),
        7000000000 *
            ‖sphereAmbientMfderiv
                  (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3)))
                  p v‖ ^
              2 ≤
          inner ℝ
            (sphereAmbientMfderiv
              (SphereSupport.homogeneousGradient
                (SphereSupport.radialExtension counterexampleTwoSphereExtension))
              p v)
            (sphereAmbientMfderiv
              (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
              v))
    (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (hp : p ≠ counterexampleSphereChart 0) :
    ¬EuclideanHypersurface.IsUmbilic (TangentSpace (𝓡 2) p) (EuclideanSpace ℝ (Fin 3))
        (sphereAmbientMfderiv
          (SphereSupport.homogeneousGradient
            (SphereSupport.radialExtension counterexampleTwoSphereExtension))
          p)
        (sphereAmbientMfderiv
          (sphereNormal
            (SphereSupport.homogeneousGradient
              (SphereSupport.radialExtension counterexampleTwoSphereExtension)))
          p) :=
  by
  intro humbilic
  let F :=
    SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
  let n : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3) := fun q ↦
    (q : EuclideanSpace ℝ (Fin 3))
  let dF := sphereAmbientMfderiv F p
  let dn := sphereAmbientMfderiv n p
  have hnormal := counterexampleTwoHomogeneousGradient_sphereNormal_of_coercive hCoercive
  change sphereNormal F = n at hnormal
  rw [hnormal] at humbilic
  change
    EuclideanHypersurface.IsUmbilic (TangentSpace (𝓡 2) p) (EuclideanSpace ℝ (Fin 3)) dF
      dn at humbilic
  have hrange : dn.range ≤ dF.range := by
    rw [counterexampleTwoHomogeneousGradient_range_eq_of_coercive hCoercive p]
  have hscalar : ∃ c : ℝ, dn = c • dF :=
    (EuclideanHypersurface.isUmbilic_iff_normal_deriv_eq_smul dF dn hrange).mp humbilic
  obtain ⟨w, rfl⟩ := exists_reciprocalSphereChart_of_ne_south hp
  exact
    sphericalTraceFreeHessian_counterexampleTwoReciprocal_ne_zero_all w
      (sphericalTraceFreeHessian_eq_zero_of_umbilic_reciprocal w
        (by simpa only [dF, dn, F, n] using hscalar))


-- @@ L9027-9213 expanded
/-- Oriented coercivity of the radius tensor makes the degree-one extension strictly convex
along every chord that does not pass through the origin. -/
private theorem counterexampleTwoRadialExtension_strictConvexOn_chord
    (hCoercive :
      ∀ (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (v : TangentSpace (𝓡 2) p),
        7000000000 *
            ‖sphereAmbientMfderiv
                  (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3)))
                  p v‖ ^
              2 ≤
          inner ℝ
            (sphereAmbientMfderiv
              (SphereSupport.homogeneousGradient
                (SphereSupport.radialExtension counterexampleTwoSphereExtension))
              p v)
            (sphereAmbientMfderiv
              (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
              v))
    (p q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (hpq : p ≠ q)
    (hantipodal : (q : EuclideanSpace ℝ (Fin 3)) ≠ -(p : EuclideanSpace ℝ (Fin 3))) :
    StrictConvexOn ℝ (Icc 0 1)
      (fun t : ℝ ↦
        SphereSupport.radialExtension counterexampleTwoSphereExtension
          ((p : EuclideanSpace ℝ (Fin 3)) +
            t • ((q : EuclideanSpace ℝ (Fin 3)) - (p : EuclideanSpace ℝ (Fin 3))))) :=
  by
  let H := SphereSupport.radialExtension counterexampleTwoSphereExtension
  let G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) := gradient H
  let d : EuclideanSpace ℝ (Fin 3) :=
    (q : EuclideanSpace ℝ (Fin 3)) - (p : EuclideanSpace ℝ (Fin 3))
  let line : ℝ → EuclideanSpace ℝ (Fin 3) := fun t ↦ (p : EuclideanSpace ℝ (Fin 3)) + t • d
  let f : ℝ → ℝ := fun t ↦ H (line t)
  have hline_ne (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : line t ≠ 0 :=
    by
    intro hzero
    have heq : t • (q : EuclideanSpace ℝ (Fin 3)) = -(1 - t) • (p : EuclideanSpace ℝ (Fin 3)) :=
      by
      dsimp only [line, d] at hzero
      have hzero' :
        (1 - t) • (p : EuclideanSpace ℝ (Fin 3)) + t • (q : EuclideanSpace ℝ (Fin 3)) = 0 := by
        calc
          (1 - t) • (p : EuclideanSpace ℝ (Fin 3)) + t • (q : EuclideanSpace ℝ (Fin 3)) =
              (p : EuclideanSpace ℝ (Fin 3)) +
                t • ((q : EuclideanSpace ℝ (Fin 3)) - (p : EuclideanSpace ℝ (Fin 3))) :=
            by module
          _ = 0 := hzero
      simpa only [neg_smul] using eq_neg_of_add_eq_zero_right hzero'
    have hnorm := congrArg norm heq
    simp only [norm_smul, norm_eq_of_mem_sphere p, norm_eq_of_mem_sphere q, mul_one,
      Real.norm_eq_abs, abs_neg, abs_of_nonneg ht.1, abs_of_nonneg (sub_nonneg.mpr ht.2)] at hnorm
    have htHalf : t = 1 / 2 := by linarith
    apply hantipodal
    rw [htHalf] at heq
    norm_num at heq
    have heq' :
      (1 / 2 : ℝ) • (q : EuclideanSpace ℝ (Fin 3)) =
        (1 / 2 : ℝ) • (-(p : EuclideanSpace ℝ (Fin 3))) :=
      by simpa only [smul_neg] using heq
    have h := congrArg (fun z : EuclideanSpace ℝ (Fin 3) ↦ (2 : ℝ) • z) heq'
    norm_num [smul_smul] at h
    exact h
  have hHsmooth : ContDiffOn ℝ ∞ H {0}ᶜ :=
    radialExtension_contDiffOn_compl_of_contMDiff counterexampleTwoSphereExtension
      (counterexampleTwoSphereExtension_contMDiff_of_contMDiffAt_north
        counterexampleTwoSphereExtension_contMDiffAt_north)
  have hGsmooth : ContDiffOn ℝ ∞ G {0}ᶜ :=
    by
    have hDf : ContDiffOn ℝ ∞ (fderiv ℝ H) {0}ᶜ :=
      hHsmooth.fderiv_of_isOpen isOpen_compl_singleton (by simp)
    change ContDiffOn ℝ ∞ (gradient H) {0}ᶜ
    rw [show gradient H = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm ∘ fderiv ℝ H
        by rfl]
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin 3))).symm.contDiff.comp_contDiffOn hDf
  apply strictConvexOn_of_deriv2_pos' (convex_Icc 0 1)
  · intro t ht
    have hlineCont : ContinuousAt line t := by fun_prop
    exact
      ((hHsmooth (line t) (hline_ne t ht)).contDiffAt
            (isOpen_compl_singleton.mem_nhds
              (hline_ne t ht))).continuousAt |>.comp_continuousWithinAt
        hlineCont.continuousWithinAt
  · intro t ht
    let x := line t
    let r := ‖x‖
    let s : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
      ⟨r⁻¹ • x,
        by
        simp only [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, r]
        exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (hline_ne t ht))⟩
    let τ : EuclideanSpace ℝ (Fin 3) :=
      d - inner ℝ d (s : EuclideanSpace ℝ (Fin 3)) • (s : EuclideanSpace ℝ (Fin 3))
    have hx : x ≠ 0 := hline_ne t ht
    have hr : 0 < r := norm_pos_iff.mpr hx
    let c : ℝ := inner ℝ (p : EuclideanSpace ℝ (Fin 3)) (q : EuclideanSpace ℝ (Fin 3))
    have hcUpper : c ≤ 1 :=
      real_inner_le_one_of_norm_eq_one (norm_eq_of_mem_sphere p) (norm_eq_of_mem_sphere q)
    have hcLower : -1 ≤ c :=
      by
      have :=
        real_inner_le_one_of_norm_eq_one (norm_eq_of_mem_sphere p)
          (norm_neg (q : EuclideanSpace ℝ (Fin 3)) ▸ norm_eq_of_mem_sphere q)
      rw [inner_neg_right] at this
      dsimp only [c]
      linarith
    have hcneOne : c ≠ 1 := by
      dsimp only [c]
      intro h
      have hpq' : (p : EuclideanSpace ℝ (Fin 3)) = (q : EuclideanSpace ℝ (Fin 3)) :=
        (inner_eq_one_iff_of_norm_eq_one (norm_eq_of_mem_sphere p) (norm_eq_of_mem_sphere q)).mp h
      exact hpq (Subtype.ext hpq')
    have hcneNegOne : c ≠ -1 := by
      dsimp only [c]
      intro h
      have hpnegq : (p : EuclideanSpace ℝ (Fin 3)) = -(q : EuclideanSpace ℝ (Fin 3)) :=
        (inner_eq_neg_one_iff_of_norm_eq_one (norm_eq_of_mem_sphere p) (norm_eq_of_mem_sphere q)).mp
          h
      apply hantipodal
      have h' := congrArg Neg.neg hpnegq
      simpa using h'.symm
    have hcpos : 0 < 1 - c ^ 2 :=
      by
      rcases lt_or_eq_of_le hcUpper with hc | hc
      · rcases lt_or_eq_of_le hcLower with hc' | hc'
        · nlinarith
        · exact (hcneNegOne hc'.symm).elim
      · exact (hcneOne hc).elim
    have hgram : r ^ 2 * ‖τ‖ ^ 2 = 1 - c ^ 2 :=
      by
      have hxexpr :
        x = (1 - t) • (p : EuclideanSpace ℝ (Fin 3)) + t • (q : EuclideanSpace ℝ (Fin 3)) :=
        by
        dsimp only [x, line, d]
        module
      have hrsq : r ^ 2 = (1 - t) ^ 2 + t ^ 2 + 2 * t * (1 - t) * c :=
        by
        dsimp only [r]
        rw [← real_inner_self_eq_norm_sq x, hxexpr]
        dsimp only [c]
        simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
          real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1, norm_eq_of_mem_sphere p,
          norm_eq_of_mem_sphere q, mul_one]
        rw [real_inner_comm (q : EuclideanSpace ℝ (Fin 3)) (p : EuclideanSpace ℝ (Fin 3))]
        ring
      have hdsq : ‖d‖ ^ 2 = 2 - 2 * c :=
        by
        rw [← real_inner_self_eq_norm_sq d]
        dsimp only [d, c]
        simp only [inner_sub_left, inner_sub_right, real_inner_self_eq_norm_sq,
          norm_eq_of_mem_sphere p, norm_eq_of_mem_sphere q]
        rw [real_inner_comm (q : EuclideanSpace ℝ (Fin 3)) (p : EuclideanSpace ℝ (Fin 3))]
        ring
      have hdx : inner ℝ d x = (2 * t - 1) * (1 - c) :=
        by
        rw [hxexpr]
        dsimp only [d, c]
        simp only [inner_sub_left, inner_add_right, real_inner_smul_right,
          real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p, norm_eq_of_mem_sphere q]
        rw [real_inner_comm (q : EuclideanSpace ℝ (Fin 3)) (p : EuclideanSpace ℝ (Fin 3))]
        ring
      have hds : inner ℝ d (s : EuclideanSpace ℝ (Fin 3)) = r⁻¹ * inner ℝ d x :=
        by
        dsimp only [s]
        rw [real_inner_smul_right]
      have hτsq : ‖τ‖ ^ 2 = ‖d‖ ^ 2 - inner ℝ d (s : EuclideanSpace ℝ (Fin 3)) ^ 2 :=
        by
        rw [← real_inner_self_eq_norm_sq τ]
        dsimp only [τ]
        simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_smul_right,
          real_inner_self_eq_norm_sq]
        rw [real_inner_comm (s : EuclideanSpace ℝ (Fin 3)) d, norm_smul, norm_eq_of_mem_sphere s,
          mul_one, Real.norm_eq_abs, sq_abs]
        ring
      rw [hτsq, hds, hdsq, hdx]
      field_simp [hr.ne']
      nlinarith [hrsq]
    have hτ : τ ≠ 0 := by
      intro hτzero
      rw [hτzero, norm_zero] at hgram
      nlinarith
    have hsecond : (deriv^[2] f) t = inner ℝ (fderiv ℝ G x d) d :=
      by
      have hlineDeriv : HasDerivAt line d t :=
        by
        dsimp only [line]
        simpa only [id_eq, zero_add, one_smul] using
          ((hasDerivAt_id (𝕜 := ℝ) t).smul_const d).const_add (p : EuclideanSpace ℝ (Fin 3))
      have hxH : DifferentiableAt ℝ H x :=
        (hHsmooth x hx).differentiableWithinAt (by simp) |>.differentiableAt
          (isOpen_compl_singleton.mem_nhds hx)
      have hxG : DifferentiableAt ℝ G x :=
        (hGsmooth x hx).differentiableWithinAt (by simp) |>.differentiableAt
          (isOpen_compl_singleton.mem_nhds hx)
      have hfirst : deriv f =ᶠ[nhds t] fun y ↦ inner ℝ (G (line y)) d :=
        by
        have hlineEvent : ∀ᶠ y in nhds t, line y ≠ 0 := by
          exact (by fun_prop : ContinuousAt line t).eventually_ne (by simpa [x] using hx)
        filter_upwards [hlineEvent] with y hy
        have hyH : DifferentiableAt ℝ H (line y) :=
          (hHsmooth (line y) hy).differentiableWithinAt (by simp) |>.differentiableAt
            (isOpen_compl_singleton.mem_nhds hy)
        have hyline : HasDerivAt line d y := by
          dsimp only [line]
          simpa only [id_eq, zero_add, one_smul] using
            ((hasDerivAt_id (𝕜 := ℝ) y).smul_const d).const_add (p : EuclideanSpace ℝ (Fin 3))
        rw [(by
              simpa [Function.comp_def] using
                hyH.hasFDerivAt.comp_hasDerivAt_of_eq (x := y) hyline rfl :
              HasDerivAt f (fderiv ℝ H (line y) d) y).deriv]
        dsimp only [G]
        rw [inner_gradient_left]
      change deriv (deriv f) t = inner ℝ (fderiv ℝ G x d) d
      rw [hfirst.deriv_eq]
      have hGline : HasDerivAt (fun y ↦ G (line y)) (fderiv ℝ G x d) t := by
        simpa [Function.comp_def, x] using
          hxG.hasFDerivAt.comp_hasDerivAt_of_eq (x := t) hlineDeriv rfl
      simpa using (hGline.inner ℝ (hasDerivAt_const t d)).deriv
    rw [hsecond]
    have hbound := counterexampleTwoRadialExtension_hessian_coercive (x := x) (d := d) hCoercive hx
    change 7000000000 / ‖x‖ * ‖τ‖ ^ 2 ≤ inner ℝ (fderiv ℝ G x d) d at hbound
    exact
      lt_of_lt_of_le (mul_pos (div_pos (by norm_num) hr) (sq_pos_of_pos (norm_pos_iff.mpr hτ)))
        hbound


-- @@ L9215-9260 expanded
/-- Strict convexity of the homogeneous extension on each nonradial chord gives strict
cross-support. The antipodal chord is handled directly by positivity of the support values. -/
private theorem strictCross_of_strictConvex_chords (h : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ)
    (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
    (hHdiff :
      ∀ p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        DifferentiableAt ℝ (SphereSupport.radialExtension h) (p : EuclideanSpace ℝ (Fin 3)))
    (hF : F = SphereSupport.homogeneousGradient (SphereSupport.radialExtension h))
    (hlower : ∀ p, 1 ≤ h p)
    (hchord :
      ∀ (p q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
        p ≠ q →
          (q : EuclideanSpace ℝ (Fin 3)) ≠ -(p : EuclideanSpace ℝ (Fin 3)) →
            StrictConvexOn ℝ (Icc 0 1)
              (fun t : ℝ ↦
                SphereSupport.radialExtension h
                  ((p : EuclideanSpace ℝ (Fin 3)) +
                    t • ((q : EuclideanSpace ℝ (Fin 3)) - (p : EuclideanSpace ℝ (Fin 3)))))) :
    ∀ (p q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
      p ≠ q → inner ℝ (F p) (q : EuclideanSpace ℝ (Fin 3)) < h q :=
  by
  subst F
  intro p q hpq
  have hcontact :
    inner ℝ (SphereSupport.homogeneousGradient (SphereSupport.radialExtension h) p)
        (p : EuclideanSpace ℝ (Fin 3)) =
      h p :=
    by
    simpa using
      SphereSupport.inner_homogeneousGradient (SphereSupport.radialExtension h) p (hHdiff p)
        (fun t ht ↦ SphereSupport.radialExtension_smul_of_pos _ _ ht)
  by_cases hantipodal : (q : EuclideanSpace ℝ (Fin 3)) = -(p : EuclideanSpace ℝ (Fin 3))
  · rw [hantipodal, inner_neg_right, hcontact]
    linarith [hlower p, hlower q]
  · let line : ℝ → EuclideanSpace ℝ (Fin 3) := fun t ↦
      (p : EuclideanSpace ℝ (Fin 3)) +
        t • ((q : EuclideanSpace ℝ (Fin 3)) - (p : EuclideanSpace ℝ (Fin 3)))
    let f : ℝ → ℝ := fun t ↦ SphereSupport.radialExtension h (line t)
    have hline :
      HasDerivAt f
        (fderiv ℝ (SphereSupport.radialExtension h) (p : EuclideanSpace ℝ (Fin 3))
          ((q : EuclideanSpace ℝ (Fin 3)) - (p : EuclideanSpace ℝ (Fin 3))))
        0 :=
      by
      have harg :
        HasDerivAt line ((q : EuclideanSpace ℝ (Fin 3)) - (p : EuclideanSpace ℝ (Fin 3))) 0 := by
        simpa only [line, id_eq, zero_add, one_smul] using
          ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const
                ((q : EuclideanSpace ℝ (Fin 3)) - (p : EuclideanSpace ℝ (Fin 3)))).const_add
            (p : EuclideanSpace ℝ (Fin 3))
      simpa [f, Function.comp_def] using
        (hHdiff p).hasFDerivAt.comp_hasDerivAt_of_eq (x := (0 : ℝ)) harg (by simp [line])
    have hslope :=
      (hchord p q hpq hantipodal).deriv_lt_slope (by simp) (by simp) zero_lt_one
        hline.differentiableAt
    rw [hline.deriv] at hslope
    have hslope' :
      fderiv ℝ (SphereSupport.radialExtension h) (p : EuclideanSpace ℝ (Fin 3))
          ((q : EuclideanSpace ℝ (Fin 3)) - (p : EuclideanSpace ℝ (Fin 3))) <
        h q - h p :=
      by simpa [f, line, slope] using hslope
    rw [← inner_gradient_left] at hslope'
    change
      inner ℝ (SphereSupport.homogeneousGradient (SphereSupport.radialExtension h) p)
          ((q : EuclideanSpace ℝ (Fin 3)) - (p : EuclideanSpace ℝ (Fin 3))) <
        h q - h p at hslope'
    rw [inner_sub_right, hcontact] at hslope'
    linarith


-- @@ L9262-9283 expanded
/-- Global oriented coercivity yields the strict support inequality for distinct normals. -/
private theorem counterexampleTwo_strictCross_of_coercive
    (hCoercive :
      ∀ (p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) (v : TangentSpace (𝓡 2) p),
        7000000000 *
            ‖sphereAmbientMfderiv
                  (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3)))
                  p v‖ ^
              2 ≤
          inner ℝ
            (sphereAmbientMfderiv
              (SphereSupport.homogeneousGradient
                (SphereSupport.radialExtension counterexampleTwoSphereExtension))
              p v)
            (sphereAmbientMfderiv
              (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
              v)) :
    ∀ (p q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
      p ≠ q →
        inner ℝ
            (SphereSupport.homogeneousGradient
              (SphereSupport.radialExtension counterexampleTwoSphereExtension) p)
            (q : EuclideanSpace ℝ (Fin 3)) <
          counterexampleTwoSphereExtension q :=
  by
  exact
    strictCross_of_strictConvex_chords counterexampleTwoSphereExtension
      (SphereSupport.homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension))
      counterexampleTwoRadialExtension_differentiableAt rfl counterexampleTwoSphereExtension_lower
      (fun p q hpq hantipodal ↦
        counterexampleTwoRadialExtension_strictConvexOn_chord hCoercive p q hpq hantipodal)


-- @@ L9285-9290 verbatim
/-- The explicit seed Laplacian estimate closes the reciprocal radius certificate. -/
private theorem counterexampleTwoReciprocal_chartLaplacian_bound (w : ℂ) :
    |chartLaplacian counterexampleTwoReciprocal w| ≤
      8 * counterexampleTwoReciprocalDamping w := by
  exact chartLaplacian_counterexampleTwoReciprocal_le_of_seed
    counterexampleSeed_chartLaplacian_abs_le w


-- @@ L9292-9392 expanded
/-- The exact analytic certificate needed to finish the support geometry once the explicit
radius-tensor estimates have been established. -/
private theorem counterexampleTwoSupport_geometry_of_certificates
    (hCoercive :
      ∀ p v,
        7000000000 *
            ‖sphereAmbientMfderiv
                  (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3)))
                  p v‖ ^
              2 ≤
          inner ℝ
            (sphereAmbientMfderiv
              (SphereSupport.homogeneousGradient
                (SphereSupport.radialExtension counterexampleTwoSphereExtension))
              p v)
            (sphereAmbientMfderiv
              (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
              v))
    (hstrict :
      ∀ (p q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
        p ≠ q →
          inner ℝ
              (SphereSupport.homogeneousGradient
                (SphereSupport.radialExtension counterexampleTwoSphereExtension) p)
              (q : EuclideanSpace ℝ (Fin 3)) <
            counterexampleTwoSphereExtension q)
    (humbilic :
      EuclideanHypersurface.IsUmbilic (TangentSpace (𝓡 2) (counterexampleSphereChart 0))
        (EuclideanSpace ℝ (Fin 3))
        (sphereAmbientMfderiv
          (SphereSupport.homogeneousGradient
            (SphereSupport.radialExtension counterexampleTwoSphereExtension))
          (counterexampleSphereChart 0))
        (sphereAmbientMfderiv
          (sphereNormal
            (SphereSupport.homogeneousGradient
              (SphereSupport.radialExtension counterexampleTwoSphereExtension)))
          (counterexampleSphereChart 0)))
    (hnoUmbilic :
      ∀ p,
        p ≠ counterexampleSphereChart 0 →
          ¬EuclideanHypersurface.IsUmbilic (TangentSpace (𝓡 2) p) (EuclideanSpace ℝ (Fin 3))
              (sphereAmbientMfderiv
                (SphereSupport.homogeneousGradient
                  (SphereSupport.radialExtension counterexampleTwoSphereExtension))
                p)
              (sphereAmbientMfderiv
                (sphereNormal
                  (SphereSupport.homogeneousGradient
                    (SphereSupport.radialExtension counterexampleTwoSphereExtension)))
                p)) :
    let F :=
      SphereSupport.homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension)
    let K := SphereSupport.body counterexampleTwoSphereExtension
    IsConvexSphereOfClass ∞ F ∧
      Convex ℝ K ∧
        IsCompact K ∧
          (interior K).Nonempty ∧
            range F = frontier K ∧
              IsSupportParametrization counterexampleTwoSphereExtension F K ∧
                EuclideanHypersurface.IsUmbilic (TangentSpace (𝓡 2) (counterexampleSphereChart 0))
                    (EuclideanSpace ℝ (Fin 3))
                    (sphereAmbientMfderiv F (counterexampleSphereChart 0))
                    (sphereAmbientMfderiv (sphereNormal F) (counterexampleSphereChart 0)) ∧
                  ∀ p,
                    EuclideanHypersurface.IsUmbilic (TangentSpace (𝓡 2) p)
                        (EuclideanSpace ℝ (Fin 3)) (sphereAmbientMfderiv F p)
                        (sphereAmbientMfderiv (sphereNormal F) p) →
                      p = counterexampleSphereChart 0 :=
  by
  let F :=
    SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
  let K := SphereSupport.body counterexampleTwoSphereExtension
  have hHdiff :
    ∀ p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      DifferentiableAt ℝ (SphereSupport.radialExtension counterexampleTwoSphereExtension)
        (p : EuclideanSpace ℝ (Fin 3)) :=
    counterexampleTwoRadialExtension_differentiableAt
  have hFsmooth : ContMDiff (𝓡 2) (𝓡 3) ∞ F := by
    exact counterexampleTwoHomogeneousGradient_contMDiff
  change
    ∀ p v,
      7000000000 *
          ‖sphereAmbientMfderiv
                (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
                v‖ ^
            2 ≤
        inner ℝ (sphereAmbientMfderiv F p v)
          (sphereAmbientMfderiv
            (fun q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ↦ (q : EuclideanSpace ℝ (Fin 3))) p
            v) at hCoercive
  have hFinjective :
    ∀ p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, Function.Injective (sphereAmbientMfderiv F p) :=
    fun p ↦
    continuousLinearMap_injective_of_coercive _ _ (injective_mvfderiv_subtypeVal_sphere p)
      (by norm_num) (hCoercive p)
  change
    ∀ (p q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1),
      p ≠ q →
        inner ℝ (F p) (q : EuclideanSpace ℝ (Fin 3)) < counterexampleTwoSphereExtension q at hstrict
  change
    EuclideanHypersurface.IsUmbilic (TangentSpace (𝓡 2) (counterexampleSphereChart 0))
      (EuclideanSpace ℝ (Fin 3)) (sphereAmbientMfderiv F (counterexampleSphereChart 0))
      (sphereAmbientMfderiv (sphereNormal F) (counterexampleSphereChart 0)) at humbilic
  change
    ∀ p,
      p ≠ counterexampleSphereChart 0 →
        ¬EuclideanHypersurface.IsUmbilic (TangentSpace (𝓡 2) p) (EuclideanSpace ℝ (Fin 3))
            (sphereAmbientMfderiv F p) (sphereAmbientMfderiv (sphereNormal F) p) at hnoUmbilic
  have hunique :
    ∀ p,
      EuclideanHypersurface.IsUmbilic (TangentSpace (𝓡 2) p) (EuclideanSpace ℝ (Fin 3))
          (sphereAmbientMfderiv F p) (sphereAmbientMfderiv (sphereNormal F) p) →
        p = counterexampleSphereChart 0 :=
    by
    intro p hp
    by_contra hp0
    exact hnoUmbilic p hp0 hp
  have hcontact :
    ∀ p : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      inner ℝ (F p) (p : EuclideanSpace ℝ (Fin 3)) = counterexampleTwoSphereExtension p :=
    by
    intro p
    simpa [F] using
      SphereSupport.inner_homogeneousGradient
        (SphereSupport.radialExtension counterexampleTwoSphereExtension) p (hHdiff p)
        (fun t ht ↦ SphereSupport.radialExtension_smul_of_pos _ _ ht)
  have hcross :
    ∀ p q : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      inner ℝ (F p) (q : EuclideanSpace ℝ (Fin 3)) ≤ counterexampleTwoSphereExtension q :=
    by
    intro p q
    by_cases hpq : p = q
    · subst q
      exact (hcontact p).le
    · exact (hstrict p q hpq).le
  have hconvex : ConvexOn ℝ univ (SphereSupport.radialExtension counterexampleTwoSphereExtension) :=
    counterexampleTwoRadialExtension_convex_of_cross F hcontact hcross
  have hbody := counterexampleTwoSupport_body_of_convex_radialExtension hHdiff hconvex
  change
    range F = frontier K ∧ IsSupportParametrization counterexampleTwoSphereExtension F K at hbody
  have hK := counterexampleTwoBody_geometry
  refine
    ⟨⟨hFsmooth, SphereSupport.isEmbedding_of_strictCross _ F hFsmooth.continuous hcontact hstrict,
        hFinjective, ⟨⟨K, hK.1, hK.2.1, hK.2.2.mono interior_subset⟩, hK.2.2, hbody.1⟩⟩,
      hK.1, hK.2.1, hK.2.2, hbody.1, hbody.2, humbilic, hunique⟩


-- @@ L9394-9423 expanded
/-- A smooth spherical extension of `counterexample 2` is the support function of a
convex body whose Gauss parametrization has exactly one umbilic. -/
theorem counterexample_two_support_geometry (h : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ)
    (hsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h)
    (hchart : ∀ z : ℂ, h (counterexampleSphereChart z) = counterexample 2 z) :
    ∃ (F : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3)) (K :
      Set (EuclideanSpace ℝ (Fin 3))),
      IsConvexSphereOfClass ∞ F ∧
        Convex ℝ K ∧
          IsCompact K ∧
            (interior K).Nonempty ∧
              Set.range F = frontier K ∧
                IsSupportParametrization h F K ∧
                  EuclideanHypersurface.IsUmbilic (TangentSpace (𝓡 2) (counterexampleSphereChart 0))
                      (EuclideanSpace ℝ (Fin 3))
                      (sphereAmbientMfderiv F (counterexampleSphereChart 0))
                      (sphereAmbientMfderiv (sphereNormal F) (counterexampleSphereChart 0)) ∧
                    ∀ p,
                      EuclideanHypersurface.IsUmbilic (TangentSpace (𝓡 2) p)
                          (EuclideanSpace ℝ (Fin 3)) (sphereAmbientMfderiv F p)
                          (sphereAmbientMfderiv (sphereNormal F) p) →
                        p = counterexampleSphereChart 0 :=
  by
  have hextension := eq_counterexampleTwoSphereExtension h hsmooth hchart
  subst h
  let F :=
    SphereSupport.homogeneousGradient
      (SphereSupport.radialExtension counterexampleTwoSphereExtension)
  let K := SphereSupport.body counterexampleTwoSphereExtension
  have hCoercive :=
    counterexampleTwo_radius_coercive_of_laplacian counterexampleTwoReciprocal_chartLaplacian_bound
  have hstrict := counterexampleTwo_strictCross_of_coercive hCoercive
  refine ⟨F, K, ?_⟩
  simpa only [F, K] using
    counterexampleTwoSupport_geometry_of_certificates hCoercive hstrict
      (counterexampleTwoHomogeneousGradient_umbilic_south_of_coercive hCoercive)
      (counterexampleTwoHomogeneousGradient_not_umbilic_away_south hCoercive)


-- @@ L9425-9452 expanded
/-- **Alpöge's smooth Carathéodory counterexample.**

The function `counterexample 2` extends across the omitted north pole to a smooth function `h`
on the round two-sphere. It is the support function of a convex body `K`; `F` is its smooth
Gauss parametrization with outward normal `p`. The corresponding convex surface has exactly one
umbilic, at the point represented by `z = 0`.

The explicit compactness and nonempty-interior conditions rule out unbounded and
lower-dimensional convex sets. The range equality ensures that `F` parametrizes the boundary
of the same body whose support function is `h`. -/
theorem counterexample_two_is_support_function_with_unique_umbilic :
    ∃ (h : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ) (F :
      sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3)) (K :
      Set (EuclideanSpace ℝ (Fin 3))),
      ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ h ∧
        (∀ z : ℂ, h (counterexampleSphereChart z) = counterexample 2 z) ∧
          IsConvexSphereOfClass ∞ F ∧
            Convex ℝ K ∧
              IsCompact K ∧
                (interior K).Nonempty ∧
                  Set.range F = frontier K ∧
                    IsSupportParametrization h F K ∧
                      EuclideanHypersurface.IsUmbilic
                          (TangentSpace (𝓡 2) (counterexampleSphereChart 0))
                          (EuclideanSpace ℝ (Fin 3))
                          (sphereAmbientMfderiv F (counterexampleSphereChart 0))
                          (sphereAmbientMfderiv (sphereNormal F) (counterexampleSphereChart 0)) ∧
                        ∀ p,
                          EuclideanHypersurface.IsUmbilic (TangentSpace (𝓡 2) p)
                              (EuclideanSpace ℝ (Fin 3)) (sphereAmbientMfderiv F p)
                              (sphereAmbientMfderiv (sphereNormal F) p) →
                            p = counterexampleSphereChart 0 :=
  by
  rcases counterexample_two_sphere_extension with ⟨h, hsmooth, hchart⟩
  rcases counterexample_two_support_geometry h hsmooth hchart with ⟨F, K, hgeometry⟩
  exact ⟨h, F, K, hsmooth, hchart, hgeometry⟩


-- @@ L9454-9454 verbatim
end CaratheodoryLoewnerCounterexample


-- @@ L9456-9456 verbatim
end CounterexampleGlobalSection


-- @@ L9458-9458 verbatim
/-! ## Flattened from `FormalConjectures/Other/CaratheodoryLoewnerCounterexample.lean` -/


-- @@ L9460-9460 verbatim
section CounterexampleMainSection


-- @@ L9462-9472 verbatim
/-!
# The announced smooth counterexamples to the Carathéodory and Loewner conjectures

This module collects the formalization of the explicit counterexample family announced by Levent
Alpöge on 19 August 2026; the announcement credits John-Paul Smith and Claude with checking the
construction. The accompanying file `CaratheodoryLoewnerCounterexample.md` gives the
formalization-oriented informal proof.

*Reference:*
- [L. Alpöge, X post 2089971359921156203](https://x.com/__alpoge__/status/2089971359921156203)
-/


-- @@ L9474-9474 verbatim
open scoped ContDiff EuclideanGeometry Manifold


-- @@ L9476-9476 verbatim
namespace CaratheodoryLoewnerCounterexample


-- @@ L9478-9478 verbatim
open CaratheodoryConjecture LoewnerConjecture


-- @@ L9480-9490 verbatim
/-- Alpöge's family disproves every Loewner conjecture whose regularity is no stronger than
smoothness: its member with `k = 1` has an isolated trace-free Hessian zero of winding number
three. -/
theorem not_loewnerConjectureOfClass_of_le_infty (k : WithTop ℕ∞) (hk : k ≤ ∞) :
    ¬ LoewnerConjectureOfClass k := by
  intro h
  have hbound : (((2 + 1 : ℕ) : ℤ)) ≤ 2 :=
    h (counterexample 1) 0 (((2 + 1 : ℕ) : ℤ))
      ((counterexample_contDiff 1 (by omega)).contDiffAt.of_le hk)
      (counterexample_hasIsolatedZeroIndex 1 (by omega))
  omega


-- @@ L9492-9494 verbatim
/-- In particular, Alpöge's family disproves the smooth Loewner conjecture. -/
theorem not_loewnerConjectureOfClass_infty : ¬ LoewnerConjectureOfClass ∞ :=
  not_loewnerConjectureOfClass_of_le_infty ∞ le_rfl


-- @@ L9496-9509 verbatim
/-- Alpöge's support function disproves every Carathéodory conjecture whose regularity is no
stronger than smoothness: its convex sphere has exactly one umbilic point. -/
theorem not_caratheodoryConjectureOfClass_of_le_infty (k : WithTop ℕ∞) (hk : k ≤ ∞) :
    ¬ CaratheodoryConjectureOfClass k := by
  intro h
  rcases counterexample_two_is_support_function_with_unique_umbilic with
    ⟨_, F, _, _, _, hsurface, _, _, _, _, _, humbilic, hunique⟩
  rcases hsurface with ⟨hFsmooth, hFembedding, hFinjective, K, hKinterior, hFrange⟩
  have hsurfaceOfClass : IsConvexSphereOfClass k F :=
    ⟨hFsmooth.of_le (add_le_add hk le_rfl), hFembedding, hFinjective,
      K, hKinterior, hFrange⟩
  rcases h F hsurfaceOfClass with
    ⟨p₁, p₂, hpne, hp₁, hp₂⟩
  exact hpne ((hunique p₁ hp₁).trans (hunique p₂ hp₂).symm)


-- @@ L9511-9513 verbatim
/-- In particular, Alpöge's support function disproves the smooth Carathéodory conjecture. -/
theorem not_caratheodoryConjectureOfClass_infty : ¬ CaratheodoryConjectureOfClass ∞ :=
  not_caratheodoryConjectureOfClass_of_le_infty ∞ le_rfl


-- @@ L9515-9515 verbatim
end CaratheodoryLoewnerCounterexample


-- @@ L9517-9517 verbatim
end CounterexampleMainSection


-- @@ L9519-9519 verbatim
open scoped ContDiff


-- @@ L9521-9521 verbatim
namespace LoewnerConjecture


-- @@ L9523-9526 verbatim
/-- The smooth Loewner conjecture is false. -/
theorem loewner_conjecture : False ↔ LoewnerConjectureOfClass ∞ := by
  rw [false_iff]
  exact CaratheodoryLoewnerCounterexample.not_loewnerConjectureOfClass_infty


-- @@ L9528-9528 verbatim
end LoewnerConjecture


-- @@ L9530-9530 verbatim
namespace CaratheodoryConjecture


-- @@ L9532-9535 verbatim
/-- The smooth Carathéodory conjecture is false. -/
theorem caratheodory_conjecture : False ↔ CaratheodoryConjectureOfClass ∞ := by
  rw [false_iff]
  exact CaratheodoryLoewnerCounterexample.not_caratheodoryConjectureOfClass_infty


-- @@ L9537-9537 verbatim
end CaratheodoryConjecture
