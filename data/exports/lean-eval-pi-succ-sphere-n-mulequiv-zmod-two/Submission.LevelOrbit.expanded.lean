import Mathlib
import Submission.LevelSet


-- @@ L4-23 verbatim
/-!
# Framed level sets: flow, periodic orbits, finiteness

For `X : FramedLevelSet n` we construct a globally defined, compactly supported smooth
vector field (`TamedField`) that agrees with the oriented unit kernel field `tauField`
on a neighbourhood of the fiber `M = X.fiber` and annihilates `fderiv X.g` everywhere.
Its flow is globally defined, leaves `M` invariant, and on `M` moves with unit speed
along the kernel line field.

Main results:

* `Submission.FramedLevelSet.exists_tamedField` : existence of the tamed field;
* `Submission.TamedField.exists_flow` : global solutions of `γ' = v (γ)`;
* `Submission.TamedField.flow_unique` : global uniqueness;
* `Submission.TamedField.mem_fiber_of_solution` : invariance of the fiber;
* `Submission.TamedField.exists_flowbox` : the local straightening (flow box) lemma;
* `Submission.TamedField.exists_period` : every solution through the fiber is periodic
  with a period `≥ 1/2`;
* orbit machinery: `orbit`, `orbit_eq_or_disjoint`, `exists_finite_orbit_cover`.
-/


-- @@ L25-25 verbatim
noncomputable section


-- @@ L27-27 verbatim
namespace Submission


-- @@ L29-29 verbatim
open Set Function Metric Module

-- @@ L30-30 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L32-32 verbatim
variable {n : ℕ}


-- @@ L34-34 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L35-35 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L37-43 verbatim
/-- The unit kernel field always has norm at most one (it is either `0` or a unit
vector). -/
lemma norm_tauField_le_one (g : E → F) (x : E) : ‖tauField g x‖ ≤ 1 := by
  rcases eq_or_ne (kerCross g x) 0 with h | h
  · rw [tauField, h, smul_zero, norm_zero]; norm_num
  · rw [tauField, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]


-- @@ L45-58 verbatim
/-- A tamed version of the kernel field: a globally smooth, compactly supported vector
field of norm `≤ 1` that agrees with `tauField` on a `δ`-neighbourhood of the fiber and
annihilates `fderiv X.g` everywhere. -/
structure TamedField (X : FramedLevelSet n) where
  /-- The vector field. -/
  v : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin (n + 1))
  /-- Radius of the collar around the fiber on which `v` equals `tauField`. -/
  delta : ℝ
  delta_pos : 0 < delta
  smooth : ContDiff ℝ ∞ v
  norm_le : ∀ x, ‖v x‖ ≤ 1
  eq_tau : ∀ x ∈ Metric.cthickening delta X.fiber, v x = tauField X.g x
  fderiv_zero : ∀ x, fderiv ℝ X.g x (v x) = 0
  lipschitz : ∃ K : NNReal, LipschitzWith K v


-- @@ L60-60 verbatim
namespace FramedLevelSet


-- @@ L62-145 verbatim
/-- Construction of a tamed field via a smooth Urysohn cutoff. -/
theorem exists_tamedField (X : FramedLevelSet n) : Nonempty (TamedField X) := by
  -- choose a collar inside the regular set
  obtain ⟨δ₂, hδ₂pos, hδ₂sub⟩ :=
    X.isCompact_fiber.exists_cthickening_subset_open (isOpen_regularSet X.smooth)
      X.fiber_subset_regularSet
  set δ := δ₂ / 2 with hδdef
  have hδpos : 0 < δ := by positivity
  have h2δ : 2 * δ = δ₂ := by rw [hδdef]; ring
  have hsub : Metric.cthickening (2 * δ) X.fiber ⊆ regularSet X.g := by
    rw [h2δ]; exact hδ₂sub
  -- smooth Urysohn function: 0 outside the collar, 1 near the fiber
  have hs : IsClosed (Metric.thickening (2 * δ) X.fiber)ᶜ :=
    Metric.isOpen_thickening.isClosed_compl
  have ht : IsClosed (Metric.cthickening δ X.fiber) := Metric.isClosed_cthickening
  have hd : Disjoint (Metric.thickening (2 * δ) X.fiber)ᶜ
      (Metric.cthickening δ X.fiber) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact hx (Metric.cthickening_subset_thickening' (by positivity) (by linarith) _ hx')
  obtain ⟨f, hf0, hf1, hf01⟩ :=
    exists_contMDiffMap_zero_one_of_isClosed
      (I := modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin (n + 1))))
      (n := (⊤ : ℕ∞)) hs ht hd
  have hχ : ContDiff ℝ ∞ (⇑f) := by
    rw [← contMDiff_iff_contDiff]
    exact f.contMDiff
  -- smoothness of the field
  have hsmooth : ContDiff ℝ ∞ fun x => f x • tauField X.g x := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ regularSet X.g
    · exact hχ.contDiffAt.smul (((contDiffOn_tauField X.smooth) x hx).contDiffAt
        ((isOpen_regularSet X.smooth).mem_nhds hx))
    · -- outside the regular set the field vanishes on a neighbourhood
      have hxC : x ∈ (Metric.cthickening (2 * δ) X.fiber)ᶜ := fun hmem => hx (hsub hmem)
      have hU : IsOpen (Metric.cthickening (2 * δ) X.fiber)ᶜ :=
        Metric.isClosed_cthickening.isOpen_compl
      have hzero : ∀ y ∈ (Metric.cthickening (2 * δ) X.fiber)ᶜ,
          f y • tauField X.g y = 0 := by
        intro y hy
        have hy' : y ∈ (Metric.thickening (2 * δ) X.fiber)ᶜ := fun hmem =>
          hy (Metric.thickening_subset_cthickening _ _ hmem)
        have : f y = 0 := hf0 hy'
        rw [this, zero_smul]
      have hev : (fun y => f y • tauField X.g y) =ᶠ[𝓝 x] (fun _ => (0 : E)) :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds hxC) hzero
      exact (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq hev
  -- compact support
  have hsupp : HasCompactSupport fun x => f x • tauField X.g x := by
    have h1 : support (fun x => f x • tauField X.g x) ⊆
        Metric.thickening (2 * δ) X.fiber := by
      intro x hx
      by_contra hmem
      have : f x = 0 := hf0 hmem
      apply hx
      show f x • tauField X.g x = 0
      rw [this, zero_smul]
    have h2 : tsupport (fun x => f x • tauField X.g x) ⊆
        Metric.cthickening (2 * δ) X.fiber :=
      closure_minimal (h1.trans (Metric.thickening_subset_cthickening _ _))
        Metric.isClosed_cthickening
    exact IsCompact.of_isClosed_subset (X.isCompact_fiber.cthickening)
      isClosed_closure h2
  -- the tamed field
  refine ⟨⟨fun x => f x • tauField X.g x, δ, hδpos, hsmooth, ?_, ?_, ?_, ?_⟩⟩
  · -- norm bound
    intro x
    rw [norm_smul]
    have h1 : ‖f x‖ ≤ 1 := by
      rw [Real.norm_eq_abs, abs_le]
      exact ⟨by linarith [(hf01 x).1], (hf01 x).2⟩
    calc ‖f x‖ * ‖tauField X.g x‖ ≤ 1 * 1 :=
          mul_le_mul h1 (norm_tauField_le_one X.g x) (norm_nonneg _) zero_le_one
      _ = 1 := by norm_num
  · -- equality with `tauField` near the fiber
    intro x hx
    have : f x = 1 := hf1 hx
    rw [this, one_smul]
  · -- the field lies in the kernel of `fderiv X.g` everywhere
    intro x
    rw [map_smul, fderiv_tauField_eq_zero, smul_zero]
  · -- Lipschitz, via compact support
    exact hsmooth.lipschitzWith_of_hasCompactSupport hsupp (by simp)


-- @@ L147-147 verbatim
end FramedLevelSet


-- @@ L149-149 verbatim
/-! ## Global flow of a tamed field -/


-- @@ L151-151 verbatim
namespace TamedField


-- @@ L153-153 verbatim
variable {X : FramedLevelSet n} (V : TamedField X)


-- @@ L155-163 verbatim
/-- Global uniqueness for solutions of the tamed ODE. -/
theorem solution_unique {γ₁ γ₂ : ℝ → EuclideanSpace ℝ (Fin (n + 1))}
    (h₁ : ∀ t, HasDerivAt γ₁ (V.v (γ₁ t)) t)
    (h₂ : ∀ t, HasDerivAt γ₂ (V.v (γ₂ t)) t)
    {t₀ : ℝ} (heq : γ₁ t₀ = γ₂ t₀) : γ₁ = γ₂ := by
  obtain ⟨K, hK⟩ := V.lipschitz
  exact ODE_solution_unique_univ (v := fun _ x => V.v x) (s := fun _ => univ)
    (t₀ := t₀) (fun _ => hK.lipschitzOnWith)
    (fun t => ⟨h₁ t, mem_univ _⟩) (fun t => ⟨h₂ t, mem_univ _⟩) heq


-- @@ L165-246 verbatim
/-- Global existence for the tamed ODE: the field is bounded and globally Lipschitz,
so Picard–Lindelöf solutions on arbitrarily large intervals can be glued. -/
theorem exists_solution (p : EuclideanSpace ℝ (Fin (n + 1))) :
    ∃ γ : ℝ → EuclideanSpace ℝ (Fin (n + 1)),
      γ 0 = p ∧ ∀ t, HasDerivAt γ (V.v (γ t)) t := by
  obtain ⟨K, hK⟩ := V.lipschitz
  -- solutions on `Ioo (-(T+1)) (T+1)` for every `T : ℕ`
  have main : ∀ T : ℕ, ∃ α : ℝ → EuclideanSpace ℝ (Fin (n + 1)),
      α 0 = p ∧ ∀ t ∈ Ioo (-(T + 1 : ℝ)) (T + 1 : ℝ), HasDerivAt α (V.v (α t)) t := by
    intro T
    have h0mem : (0 : ℝ) ∈ Icc (-(T + 1 : ℝ)) (T + 1 : ℝ) := by
      constructor
      · have : (0 : ℝ) ≤ T := T.cast_nonneg
        linarith
      · have : (0 : ℝ) ≤ T := T.cast_nonneg
        linarith
    have hpl : IsPicardLindelof (fun (_ : ℝ) x => V.v x)
        (⟨0, h0mem⟩ : Icc (-(T + 1 : ℝ)) (T + 1 : ℝ)) p (T + 2 : ℕ) 0 1 K := by
      constructor
      · exact fun t _ => hK.lipschitzOnWith
      · exact fun x _ => continuousOn_const
      · intro t _ x _
        simpa using V.norm_le x
      · show (1 : ℝ) * max ((T + 1 : ℝ) - 0) (0 - -(T + 1 : ℝ)) ≤ (T + 2 : ℕ) - (0 : ℝ)
        push_cast
        have h0T : (0 : ℝ) ≤ T := T.cast_nonneg
        rw [one_mul]
        apply max_le <;> linarith
    obtain ⟨α, hα0, hα⟩ := hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt
      (mem_closedBall_self le_rfl)
    refine ⟨α, hα0, fun t ht => ?_⟩
    exact (hα t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)
  choose α hα0 hαs using main
  -- any two of the local solutions agree on the common interval
  have agree : ∀ (T S : ℕ) (t : ℝ), |t| < T + 1 → |t| < S + 1 → α T t = α S t := by
    intro T S t hT hS
    set m : ℕ := min T S with hm
    have hmT : (m : ℝ) + 1 ≤ (T : ℝ) + 1 := by
      have : (m : ℕ) ≤ T := min_le_left T S
      exact_mod_cast by omega
    have hmS : (m : ℝ) + 1 ≤ (S : ℝ) + 1 := by
      have : (m : ℕ) ≤ S := min_le_right T S
      exact_mod_cast by omega
    have htm : |t| < (m : ℝ) + 1 := by
      rcases min_choice T S with h | h <;> rw [hm, h]
      · exact hT
      · exact hS
    have hsub : Ioo (-(m + 1 : ℝ)) (m + 1 : ℝ) ⊆ Ioo (-(T + 1 : ℝ)) (T + 1 : ℝ) :=
      Ioo_subset_Ioo (by linarith) (by linarith)
    have hsub' : Ioo (-(m + 1 : ℝ)) (m + 1 : ℝ) ⊆ Ioo (-(S + 1 : ℝ)) (S + 1 : ℝ) :=
      Ioo_subset_Ioo (by linarith) (by linarith)
    have h0m : (0 : ℝ) ∈ Ioo (-(m + 1 : ℝ)) (m + 1 : ℝ) := by
      constructor
      · have : (0 : ℝ) ≤ m := m.cast_nonneg
        linarith
      · have : (0 : ℝ) ≤ m := m.cast_nonneg
        linarith
    have := ODE_solution_unique_of_mem_Ioo (v := fun (_ : ℝ) x => V.v x)
      (s := fun _ => univ) (K := K)
      (fun t _ => hK.lipschitzOnWith) h0m
      (fun u hu => ⟨hαs T u (hsub hu), mem_univ _⟩)
      (fun u hu => ⟨hαs S u (hsub' hu), mem_univ _⟩)
      ((hα0 T).trans (hα0 S).symm)
    exact this ⟨(abs_lt.mp htm).1, (abs_lt.mp htm).2⟩
  -- glue: at time `t` use the solution with index `⌊|t|⌋`
  refine ⟨fun t => α (Nat.floor |t|) t, ?_, ?_⟩
  · simpa using hα0 (Nat.floor |(0 : ℝ)|)
  · intro t
    set N : ℕ := Nat.floor |t| with hN
    have htN : |t| < (N : ℝ) + 1 := Nat.lt_floor_add_one _
    have hev : (fun s => α (Nat.floor |s|) s) =ᶠ[𝓝 t] α N := by
      have hUopen : IsOpen {s : ℝ | |s| < (N : ℝ) + 1} :=
        isOpen_lt (continuous_abs) continuous_const
      refine Filter.eventuallyEq_of_mem (hUopen.mem_nhds htN) fun s hs => ?_
      exact agree (Nat.floor |s|) N s (Nat.lt_floor_add_one _) hs
    have hder : HasDerivAt (α N) (V.v (α N t)) t := by
      apply hαs N t
      have := abs_lt.mp htN
      exact ⟨this.1, this.2⟩
    have : HasDerivAt (fun s => α (Nat.floor |s|) s) (V.v (α N t)) t :=
      (Filter.EventuallyEq.hasDerivAt_iff hev).mpr hder
    simpa [← hN] using this


-- @@ L248-250 verbatim
/-- The canonical global solution through `p`. -/
def flow (p : EuclideanSpace ℝ (Fin (n + 1))) : ℝ → EuclideanSpace ℝ (Fin (n + 1)) :=
  Classical.choose (V.exists_solution p)


-- @@ L252-253 verbatim
@[simp] lemma flow_zero (p : EuclideanSpace ℝ (Fin (n + 1))) : V.flow p 0 = p :=
  (Classical.choose_spec (V.exists_solution p)).1


-- @@ L255-257 verbatim
lemma hasDerivAt_flow (p : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    HasDerivAt (V.flow p) (V.v (V.flow p t)) t :=
  (Classical.choose_spec (V.exists_solution p)).2 t


-- @@ L259-260 verbatim
lemma continuous_flow (p : EuclideanSpace ℝ (Fin (n + 1))) : Continuous (V.flow p) :=
  continuous_iff_continuousAt.mpr fun t => (V.hasDerivAt_flow p t).continuousAt


-- @@ L262-281 verbatim
/-- Invariance: a solution of the tamed ODE starting on the fiber stays on the fiber
(the value of `X.g` is constant along any solution). -/
theorem solution_mem_fiber {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))}
    (hγ : ∀ t, HasDerivAt γ (V.v (γ t)) t) (h0 : γ 0 ∈ X.fiber) :
    ∀ t, γ t ∈ X.fiber := by
  have hcomp : ∀ t, HasDerivAt (fun s => X.g (γ s)) 0 t := by
    intro t
    have hgdiff : HasFDerivAt X.g (fderiv ℝ X.g (γ t)) (γ t) :=
      (X.smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
    have := hgdiff.comp_hasDerivAt t (hγ t)
    rwa [V.fderiv_zero (γ t)] at this
  have hconst : ∀ t, X.g (γ t) = X.g (γ 0) := by
    intro t
    exact is_const_of_deriv_eq_zero
      (fun s => (hcomp s).differentiableAt)
      (fun s => (hcomp s).deriv) t 0
  intro t
  have := hconst t
  rw [show X.g (γ 0) = 0 from h0] at this
  exact this


-- @@ L283-285 verbatim
lemma flow_mem_fiber {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ X.fiber) (t : ℝ) :
    V.flow p t ∈ X.fiber :=
  V.solution_mem_fiber (V.hasDerivAt_flow p) (by rw [V.flow_zero]; exact hp) t


-- @@ L287-290 verbatim
/-- On the fiber, the tamed field agrees with the unit kernel field. -/
lemma v_eq_tau_of_mem_fiber {x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ X.fiber) :
    V.v x = tauField X.g x :=
  V.eq_tau x (Metric.self_subset_cthickening _ hx)


-- @@ L292-292 verbatim
end TamedField


-- @@ L294-294 verbatim
/-! ## The flow box lemma -/


-- @@ L296-300 verbatim
/-- The straightening map at `q`: level of `g` paired with the displacement along the
kernel direction. -/
def straighten (X : FramedLevelSet n) (q : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n) × ℝ :=
  fun y => (X.g y, ⟪tauField X.g q, y - q⟫)


-- @@ L302-305 verbatim
/-- The derivative of the straightening map at `q`, as a continuous linear map. -/
def straightenDeriv (X : FramedLevelSet n) (q : EuclideanSpace ℝ (Fin (n + 1))) :
    EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) × ℝ :=
  (fderiv ℝ X.g q).prod (innerSL ℝ (tauField X.g q))


-- @@ L307-329 verbatim
lemma straightenDeriv_bijective (X : FramedLevelSet n)
    {q : EuclideanSpace ℝ (Fin (n + 1))} (hq : q ∈ X.fiber) :
    Function.Bijective (straightenDeriv X q) := by
  have hreg : q ∈ regularSet X.g := X.fiber_subset_regularSet hq
  have hinj : Function.Injective (straightenDeriv X q) := by
    rw [injective_iff_map_eq_zero]
    intro w hw
    have h1 : fderiv ℝ X.g q w = 0 := congrArg Prod.fst hw
    have h2 : ⟪tauField X.g q, w⟫ = 0 := congrArg Prod.snd hw
    have hmem : w ∈ Submodule.span ℝ {tauField X.g q} :=
      (fderiv_eq_zero_iff_mem_span_tauField hreg w).mp h1
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have hnorm : ‖tauField X.g q‖ = 1 := norm_tauField hreg
    rw [← ha, real_inner_smul_right, real_inner_self_eq_norm_sq, hnorm] at h2
    have : a = 0 := by simpa using h2
    rw [← ha, this, zero_smul]
  constructor
  · exact hinj
  · have hfr : finrank ℝ (EuclideanSpace ℝ (Fin (n + 1)))
        = finrank ℝ (EuclideanSpace ℝ (Fin n) × ℝ) := by
      rw [finrank_euclideanSpace_fin, Module.finrank_prod, finrank_euclideanSpace_fin,
        Module.finrank_self]
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfr).mp hinj


-- @@ L331-334 verbatim
lemma contDiff_straighten (X : FramedLevelSet n) (q : EuclideanSpace ℝ (Fin (n + 1))) :
    ContDiff ℝ ∞ (straighten X q) := by
  apply ContDiff.prodMk X.smooth
  exact ContDiff.inner ℝ contDiff_const (contDiff_id.sub contDiff_const)


-- @@ L336-343 verbatim
lemma hasFDerivAt_straighten (X : FramedLevelSet n) (q : EuclideanSpace ℝ (Fin (n + 1))) :
    HasFDerivAt (straighten X q) (straightenDeriv X q) q := by
  apply HasFDerivAt.prodMk
  · exact (X.smooth.differentiable (by simp)).differentiableAt.hasFDerivAt
  · have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin (n + 1)) => y - q)
        (ContinuousLinearMap.id ℝ _) q := (hasFDerivAt_id q).sub_const q
    have h2 := (innerSL ℝ (tauField X.g q)).hasFDerivAt.comp q h1
    simpa [Function.comp_def] using h2


-- @@ L345-479 verbatim
/-- **Flow box lemma.** Near a fiber point `q`, every fiber point in a small ball lies
on the flow line through `q`, at a time as small as desired. -/
theorem TamedField.exists_flowbox {X : FramedLevelSet n} (V : TamedField X)
    {q : EuclideanSpace ℝ (Fin (n + 1))} (hq : q ∈ X.fiber) {c : ℝ} (hc : 0 < c) :
    ∃ r > 0, ∀ x ∈ X.fiber ∩ ball q r, ∃ s : ℝ, |s| < c ∧ V.flow q s = x := by
  classical
  have hreg : q ∈ regularSet X.g := X.fiber_subset_regularSet hq
  set τq := tauField X.g q with hτq
  have hτnorm : ‖τq‖ = 1 := norm_tauField hreg
  -- inverse function theorem for the straightening map
  set L₀ : EuclideanSpace ℝ (Fin (n + 1)) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin n) × ℝ :=
    LinearEquiv.ofBijective ((straightenDeriv X q) : _ →ₗ[ℝ] _)
      (straightenDeriv_bijective X hq) with hL₀
  set L : EuclideanSpace ℝ (Fin (n + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin n) × ℝ :=
    L₀.toContinuousLinearEquiv with hL
  have hLcoe : (L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) × ℝ)
      = straightenDeriv X q := by
    apply ContinuousLinearMap.ext
    intro w
    rfl
  have hΦq : HasFDerivAt (straighten X q)
      (L : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] EuclideanSpace ℝ (Fin n) × ℝ) q := by
    rw [hLcoe]
    exact hasFDerivAt_straighten X q
  set P := (contDiff_straighten X q).contDiffAt.toOpenPartialHomeomorph
    (straighten X q) hΦq (by simp) with hP
  have hPcoe : ⇑P = straighten X q :=
    (contDiff_straighten X q).contDiffAt.toOpenPartialHomeomorph_coe hΦq (by simp)
  have hqmem : q ∈ P.source :=
    (contDiff_straighten X q).contDiffAt.mem_toOpenPartialHomeomorph_source hΦq (by simp)
  have hPinj : InjOn (straighten X q) P.source := by
    rw [← hPcoe]
    intro a ha b hb hab
    rw [← P.left_inv ha, ← P.left_inv hb, hab]
  -- the flow through `q` and the displacement function
  set γ := V.flow q with hγ
  have hγM : ∀ t, γ t ∈ X.fiber := V.flow_mem_fiber hq
  set h : ℝ → ℝ := fun s => ⟪τq, γ s - q⟫ with hh
  have hh0 : h 0 = 0 := by
    simp [hh, hγ, V.flow_zero]
  have hder : ∀ s, HasDerivAt h ⟪τq, V.v (γ s)⟫ s := by
    intro s
    have h1 : HasDerivAt (fun _ : ℝ => τq) 0 s := hasDerivAt_const s τq
    have h2 : HasDerivAt (fun u => γ u - q) (V.v (γ s)) s :=
      (V.hasDerivAt_flow q s).sub_const q
    have := h1.inner ℝ h2
    simpa using this
  have hcont' : Continuous fun s => ⟪τq, V.v (γ s)⟫ :=
    continuous_const.inner (V.smooth.continuous.comp (V.continuous_flow q))
  have hder0 : ⟪τq, V.v (γ 0)⟫ = 1 := by
    rw [hγ, V.flow_zero, V.v_eq_tau_of_mem_fiber hq, ← hτq,
      real_inner_self_eq_norm_sq, hτnorm]
    norm_num
  -- a small interval on which the flow stays in the chart and moves forward
  have hSopen : IsOpen {s : ℝ | γ s ∈ P.source ∧ 1 / 2 < ⟪τq, V.v (γ s)⟫} := by
    apply IsOpen.inter
    · exact P.open_source.preimage (V.continuous_flow q)
    · exact isOpen_lt continuous_const hcont'
  have hS0 : (0 : ℝ) ∈ {s : ℝ | γ s ∈ P.source ∧ 1 / 2 < ⟪τq, V.v (γ s)⟫} := by
    constructor
    · rw [hγ, V.flow_zero]; exact hqmem
    · rw [hder0]; norm_num
  obtain ⟨ε, hεpos, hεball⟩ := Metric.isOpen_iff.mp hSopen 0 hS0
  set c' := min (ε / 2) (c / 2) with hc'
  have hc'pos : 0 < c' := lt_min (by linarith) (by linarith)
  have hc'lt : c' < c := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hIccS : Icc (-c') c' ⊆ {s : ℝ | γ s ∈ P.source ∧ 1 / 2 < ⟪τq, V.v (γ s)⟫} := by
    intro s hs
    apply hεball
    rw [Metric.mem_ball, Real.dist_eq, sub_zero]
    have h1 : |s| ≤ c' := abs_le.mpr ⟨hs.1, hs.2⟩
    have h2 : c' ≤ ε / 2 := min_le_left _ _
    linarith
  -- lower bounds for the displacement at the interval ends
  have hdiff : ∀ s, DifferentiableAt ℝ h s := fun s => (hder s).differentiableAt
  have hderiv_gt : ∀ s ∈ interior (Icc (-c') c'), 1 / 2 < deriv h s := by
    intro s hs
    rw [interior_Icc] at hs
    have hmem : s ∈ Icc (-c') c' := Ioo_subset_Icc_self hs
    rw [(hder s).deriv]
    exact (hIccS hmem).2
  have hbound := Convex.mul_sub_lt_image_sub_of_lt_deriv (convex_Icc (-c') c')
    (fun s _ => (hdiff s).continuousAt.continuousWithinAt)
    (fun s _ => (hdiff s).differentiableWithinAt) hderiv_gt
  have hhc' : c' / 2 < h c' := by
    have := hbound 0 (by constructor <;> [linarith; linarith]) c'
      (by constructor <;> [linarith; linarith]) hc'pos
    rw [hh0] at this
    linarith
  have hhmc' : h (-c') < -(c' / 2) := by
    have := hbound (-c') (by constructor <;> [linarith; linarith]) 0
      (by constructor <;> [linarith; linarith]) (by linarith)
    rw [hh0] at this
    linarith
  -- choose the radius
  obtain ⟨r₀, hr₀pos, hr₀ball⟩ := Metric.isOpen_iff.mp P.open_source q hqmem
  refine ⟨min (c' / 2) r₀, lt_min (by linarith) hr₀pos, ?_⟩
  rintro x ⟨hxM, hxball⟩
  set σ := ⟪τq, x - q⟫ with hσ
  have hσsmall : |σ| < c' / 2 := by
    calc |σ| ≤ ‖τq‖ * ‖x - q‖ := abs_real_inner_le_norm _ _
      _ = ‖x - q‖ := by rw [hτnorm, one_mul]
      _ < min (c' / 2) r₀ := by
          rw [← dist_eq_norm]
          exact hxball
      _ ≤ c' / 2 := min_le_left _ _
  -- IVT for the displacement function
  have hcontIcc : ContinuousOn h (Icc (-c') c') :=
    fun s _ => (hdiff s).continuousAt.continuousWithinAt
  have hσmem : σ ∈ Icc (h (-c')) (h c') := by
    have h1 : -(c' / 2) < σ := by
      have := abs_lt.mp hσsmall
      linarith [this.1]
    have h2 : σ < c' / 2 := (abs_lt.mp hσsmall).2
    constructor
    · linarith
    · linarith
  obtain ⟨s, hsmem, hseq⟩ := intermediate_value_Icc (by linarith : -c' ≤ c') hcontIcc hσmem
  refine ⟨s, ?_, ?_⟩
  · have : |s| ≤ c' := abs_le.mpr ⟨hsmem.1, hsmem.2⟩
    linarith
  -- both points lie in the chart and have the same image
  · have hγsM : γ s ∈ X.fiber := hγM s
    have hγssource : γ s ∈ P.source := (hIccS hsmem).1
    have hxsource : x ∈ P.source := hr₀ball (by
      have : dist x q < min (c' / 2) r₀ := hxball
      exact Metric.mem_ball.mpr (lt_of_lt_of_le this (min_le_right _ _)))
    apply hPinj hγssource hxsource
    show straighten X q (γ s) = straighten X q x
    have e1 : X.g (γ s) = 0 := hγsM
    have e2 : X.g x = 0 := hxM
    show ((X.g (γ s), ⟪τq, γ s - q⟫) : EuclideanSpace ℝ (Fin n) × ℝ)
        = (X.g x, ⟪τq, x - q⟫)
    rw [e1, e2]
    exact congrArg (Prod.mk (0 : EuclideanSpace ℝ (Fin n))) hseq


-- @@ L481-481 verbatim
/-! ## Periodicity -/


-- @@ L483-483 verbatim
namespace TamedField


-- @@ L485-485 verbatim
variable {X : FramedLevelSet n} (V : TamedField X)


-- @@ L487-493 verbatim
/-- Time-shifts of solutions are solutions. -/
lemma hasDerivAt_shift {γ : ℝ → EuclideanSpace ℝ (Fin (n + 1))}
    (hγ : ∀ t, HasDerivAt γ (V.v (γ t)) t) (a : ℝ) (u : ℝ) :
    HasDerivAt (fun w => γ (a + w)) (V.v (γ (a + u))) u := by
  have h1 : HasDerivAt (fun w : ℝ => a + w) 1 u := (hasDerivAt_id u).const_add a
  have h2 := (hγ (a + u)).scomp u h1
  simpa [Function.comp_def] using h2


-- @@ L495-501 verbatim
/-- The flow shifted in time is the flow of the shifted starting point. -/
lemma flow_shift (p : EuclideanSpace ℝ (Fin (n + 1))) (a : ℝ) :
    V.flow (V.flow p a) = fun u => V.flow p (a + u) := by
  apply V.solution_unique (t₀ := 0)
  · exact V.hasDerivAt_flow (V.flow p a)
  · exact fun u => V.hasDerivAt_shift (V.hasDerivAt_flow p) a u
  · simp


-- @@ L503-556 verbatim
/-- **Periodicity**: the flow line through any fiber point is periodic, with a period
bounded below by `1/2`. -/
theorem exists_period {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ X.fiber) :
    ∃ T : ℝ, 1 / 2 ≤ T ∧ Function.Periodic (V.flow p) T := by
  classical
  set γ := V.flow p with hγdef
  have hγM : ∀ t, γ t ∈ X.fiber := V.flow_mem_fiber hp
  -- an accumulation point of the integer-time sequence
  obtain ⟨q, hqM, φ, hφmono, hφlim⟩ :=
    X.isCompact_fiber.tendsto_subseq (x := fun k : ℕ => γ k) (fun k => hγM k)
  -- flow box at the accumulation point
  obtain ⟨r, hrpos, hbox⟩ := V.exists_flowbox hqM (c := 1 / 4) (by norm_num)
  have hev : ∀ᶠ m in Filter.atTop, dist (γ (φ m)) q < r := by
    have := Metric.tendsto_nhds.mp hφlim r hrpos
    exact this
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
  set k₁ : ℕ := φ K with hk₁
  set k₂ : ℕ := φ (K + 1) with hk₂
  have hk₁₂ : k₁ + 1 ≤ k₂ := by
    have := hφmono (show K < K + 1 by omega)
    omega
  obtain ⟨s₁, hs₁, hγs₁⟩ := hbox (γ k₁) ⟨hγM _, Metric.mem_ball.mpr (hK K le_rfl)⟩
  obtain ⟨s₂, hs₂, hγs₂⟩ := hbox (γ k₂) ⟨hγM _, Metric.mem_ball.mpr (hK (K + 1) (by omega))⟩
  -- unique continuation along the flow through `q`
  have huniq₁ : (fun u => γ (k₁ + u)) = fun u => V.flow q (s₁ + u) := by
    apply V.solution_unique (t₀ := 0)
    · exact fun u => V.hasDerivAt_shift (V.hasDerivAt_flow p) k₁ u
    · exact fun u => V.hasDerivAt_shift (V.hasDerivAt_flow q) s₁ u
    · simpa using hγs₁.symm
  have huniq₂ : (fun u => γ (k₂ + u)) = fun u => V.flow q (s₂ + u) := by
    apply V.solution_unique (t₀ := 0)
    · exact fun u => V.hasDerivAt_shift (V.hasDerivAt_flow p) k₂ u
    · exact fun u => V.hasDerivAt_shift (V.hasDerivAt_flow q) s₂ u
    · simpa using hγs₂.symm
  set T : ℝ := ((k₂ : ℝ) - k₁) + s₁ - s₂ with hT
  have hTpos : 1 / 2 ≤ T := by
    have hcast : (k₁ : ℝ) + 1 ≤ k₂ := by exact_mod_cast hk₁₂
    have h₁ := abs_lt.mp hs₁
    have h₂ := abs_lt.mp hs₂
    rw [hT]
    linarith [h₁.1, h₂.2]
  refine ⟨T, hTpos, ?_⟩
  intro t
  -- γ t = flow q (s₁ + (t - k₁)) and γ (t + T) = flow q (s₂ + (t + T - k₂))
  have e1 : γ t = V.flow q (s₁ + (t - k₁)) := by
    have := congrFun huniq₁ (t - k₁)
    simpa using this
  have e2 : γ (t + T) = V.flow q (s₂ + (t + T - k₂)) := by
    have := congrFun huniq₂ (t + T - k₂)
    have harg : (k₂ : ℝ) + (t + T - k₂) = t + T := by ring
    rw [harg] at this
    exact this
  have e3 : s₂ + (t + T - k₂) = s₁ + (t - k₁) := by rw [hT]; ring
  rw [e2, e3, ← e1]


-- @@ L558-558 verbatim
/-! ## Orbits -/


-- @@ L560-562 verbatim
/-- The orbit of a point: the image of the flow line through it. -/
def orbit (p : EuclideanSpace ℝ (Fin (n + 1))) : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
  range (V.flow p)


-- @@ L564-565 verbatim
lemma mem_orbit_self (p : EuclideanSpace ℝ (Fin (n + 1))) : p ∈ V.orbit p :=
  ⟨0, V.flow_zero p⟩


-- @@ L567-568 verbatim
lemma flow_mem_orbit (p : EuclideanSpace ℝ (Fin (n + 1))) (t : ℝ) :
    V.flow p t ∈ V.orbit p := ⟨t, rfl⟩


-- @@ L570-573 verbatim
lemma orbit_subset_fiber {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ X.fiber) :
    V.orbit p ⊆ X.fiber := by
  rintro x ⟨t, rfl⟩
  exact V.flow_mem_fiber hp t


-- @@ L575-589 verbatim
/-- Orbits through points of an orbit coincide with the original orbit. -/
lemma orbit_eq_of_mem {p x : EuclideanSpace ℝ (Fin (n + 1))} (hx : x ∈ V.orbit p) :
    V.orbit x = V.orbit p := by
  obtain ⟨a, rfl⟩ := hx
  have hsh := V.flow_shift p a
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    rw [congrFun hsh u]
    exact ⟨a + u, rfl⟩
  · rintro ⟨t, rfl⟩
    refine ⟨t - a, ?_⟩
    rw [congrFun hsh (t - a)]
    congr 1
    ring


-- @@ L591-598 verbatim
/-- Orbits of fiber points are compact (continuous periodic image of `[0, T]`). -/
lemma isCompact_orbit {p : EuclideanSpace ℝ (Fin (n + 1))} (hp : p ∈ X.fiber) :
    IsCompact (V.orbit p) := by
  obtain ⟨T, hT, hper⟩ := V.exists_period hp
  have himg : V.flow p '' Icc 0 (0 + T) = range (V.flow p) :=
    hper.image_Icc (by linarith) 0
  rw [orbit, ← himg]
  exact (isCompact_Icc).image (V.continuous_flow p)


-- @@ L600-610 verbatim
/-- Orbits of fiber points are relatively open in the fiber. -/
lemma orbit_isOpen_in_fiber {p q : EuclideanSpace ℝ (Fin (n + 1))}
    (hp : p ∈ X.fiber) (hq : q ∈ V.orbit p) :
    ∃ r > 0, X.fiber ∩ ball q r ⊆ V.orbit p := by
  have hqM : q ∈ X.fiber := V.orbit_subset_fiber hp hq
  obtain ⟨r, hrpos, hbox⟩ := V.exists_flowbox hqM (c := 1) (by norm_num)
  refine ⟨r, hrpos, ?_⟩
  rintro x ⟨hxM, hxball⟩
  obtain ⟨s, _, hs⟩ := hbox x ⟨hxM, hxball⟩
  have : x ∈ V.orbit q := ⟨s, hs⟩
  rwa [V.orbit_eq_of_mem hq] at this


-- @@ L612-619 verbatim
/-- Two orbits of fiber points either coincide or are disjoint. -/
theorem orbit_eq_or_disjoint {p q : EuclideanSpace ℝ (Fin (n + 1))} :
    V.orbit p = V.orbit q ∨ Disjoint (V.orbit p) (V.orbit q) := by
  by_cases h : Disjoint (V.orbit p) (V.orbit q)
  · exact Or.inr h
  · left
    obtain ⟨x, hxp, hxq⟩ := Set.not_disjoint_iff.mp h
    rw [← V.orbit_eq_of_mem hxp, ← V.orbit_eq_of_mem hxq]


-- @@ L621-648 verbatim
/-- **Finiteness**: the fiber is a finite union of orbits. -/
theorem exists_finite_orbit_cover :
    ∃ s : Finset (EuclideanSpace ℝ (Fin (n + 1))),
      (∀ q ∈ s, q ∈ X.fiber) ∧ X.fiber = ⋃ q ∈ s, V.orbit q := by
  classical
  have hkey : ∀ q, q ∈ X.fiber → ∃ r, 0 < r ∧ X.fiber ∩ ball q r ⊆ V.orbit q :=
    fun q hq => by
      obtain ⟨r, hrpos, hsub⟩ := V.orbit_isOpen_in_fiber hq (V.mem_orbit_self q)
      exact ⟨r, hrpos, hsub⟩
  choose! rad hradpos hradsub using hkey
  have hcover : X.fiber ⊆ ⋃ q ∈ X.fiber, ball q (rad q) := by
    intro x hx
    exact mem_biUnion hx (Metric.mem_ball_self (hradpos x hx))
  obtain ⟨b', hb'sub, hb'fin, hb'cover⟩ :=
    X.isCompact_fiber.elim_finite_subcover_image
      (fun q _ => Metric.isOpen_ball) hcover
  refine ⟨hb'fin.toFinset, ?_, ?_⟩
  · intro q hq
    exact hb'sub (hb'fin.mem_toFinset.mp hq)
  · apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨q, hqb', hxball⟩ := mem_iUnion₂.mp (hb'cover hx)
      have hqM : q ∈ X.fiber := hb'sub hqb'
      have : x ∈ V.orbit q := hradsub q hqM ⟨hx, hxball⟩
      exact mem_biUnion (hb'fin.mem_toFinset.mpr hqb') this
    · intro x hx
      obtain ⟨q, hq, hxq⟩ := mem_iUnion₂.mp hx
      exact V.orbit_subset_fiber (hb'sub (hb'fin.mem_toFinset.mp hq)) hxq


-- @@ L650-650 verbatim
end TamedField


-- @@ L652-652 verbatim
end Submission
