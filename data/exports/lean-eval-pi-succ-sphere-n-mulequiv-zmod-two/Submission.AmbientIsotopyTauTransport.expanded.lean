import Mathlib
import Submission.IsotopyFrameTransport


-- @@ L4-34 verbatim
/-!
# Transporting the oriented unit kernel field along an ambient isotopy

`IsotopyFrameTransport` transports the `ZMod 2` frame class along an ambient
isotopy by a positive-determinant homotopy argument.  This file transports the
finer, **oriented** datum — the unit kernel field `tauField` itself — by the
same deformation idea, but applied directly to the pairing

`s ↦ ⟪tauField (A.pullbackI X s).g (A.forward s p),
      fderiv ℝ (A.forward s) p (tauField X.g p)⟫`.

That pairing is continuous in `s` (`IsotopyFrameTransport` already supplies
continuity of the tangent field along the deformation), equals `1` at `s = 0`,
and never vanishes, because the pushed-forward tangent is a nonzero element of
the kernel of the deformed presentation and the kernel line is spanned by
`kerCross`.  The intermediate value theorem then gives positivity at `s = 1`,
i.e. **the endpoint diffeomorphism carries the oriented unit kernel field of
`X` to the oriented unit kernel field of `A.pullback X`.**

Main results:

* `smul_kerCross_of_fderiv_apply_eq_zero` — the kernel line is spanned by
  `kerCross`, in a division-free form;
* `tauField_eq_of_inner_pos` — an oriented recognition principle for
  `tauField`;
* `SmoothAmbientIsotopy.inner_tauField_pullback_pos` — the deformation
  argument;
* `SmoothAmbientIsotopy.tauField_pullback_of_curve` — the usable form: if a
  curve in the fiber runs positively along the tangent field, its image under
  the endpoint diffeomorphism computes the tangent field of the pullback.
-/


-- @@ L36-36 verbatim
set_option autoImplicit false

-- @@ L37-37 verbatim
set_option maxHeartbeats 1600000


-- @@ L39-39 verbatim
noncomputable section


-- @@ L41-41 verbatim
open Set Function

-- @@ L42-42 verbatim
open scoped Topology ContDiff RealInnerProductSpace unitInterval


-- @@ L44-44 verbatim
namespace Submission


-- @@ L46-46 verbatim
/-! ## The kernel line is spanned by the cross product -/


-- @@ L48-48 verbatim
section KernelLine


-- @@ L50-50 verbatim
variable {n : ℕ}


-- @@ L52-52 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L53-53 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L55-112 verbatim
/-- Every kernel vector of the differential is a multiple of `kerCross`,
stated without division. -/
theorem smul_kerCross_of_fderiv_apply_eq_zero (g : E → F) {q : E}
    (hq : q ∈ regularSet g) {w : E} (hw : fderiv ℝ g q w = 0) :
    ‖kerCross g q‖ ^ 2 • w = ⟪kerCross g q, w⟫ • kerCross g q := by
  classical
  set v : Fin n → E := fun i => gradVec g i q with hv
  have hk : kerCross g q = crossVec v := rfl
  have hLI : LinearIndependent ℝ v :=
    (surjective_fderiv_iff_linearIndependent g q).mp hq
  have hkne : kerCross g q ≠ 0 := (kerCross_ne_zero_iff g q).mpr hq
  have hnormsq : (0 : ℝ) < ‖kerCross g q‖ ^ 2 := by
    have := norm_pos_iff.mpr hkne
    positivity
  -- the residual vector
  set zvec : E := ‖kerCross g q‖ ^ 2 • w - ⟪kerCross g q, w⟫ • kerCross g q
    with hz
  have hwperp : ∀ i : Fin n, ⟪v i, w⟫ = 0 := by
    intro i
    rw [hv]
    rw [inner_gradVec, hw]
    rfl
  have hkperp : ∀ i : Fin n, ⟪v i, kerCross g q⟫ = 0 := by
    intro i
    rw [real_inner_comm, hk]
    exact inner_crossVec_self v i
  have hzperp : ∀ i : Fin n, ⟪v i, zvec⟫ = 0 := by
    intro i
    rw [hz, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
      hwperp i, hkperp i]
    ring
  have hzk : ⟪kerCross g q, zvec⟫ = 0 := by
    rw [hz, inner_sub_right, real_inner_smul_right, real_inner_smul_right,
      real_inner_self_eq_norm_sq]
    ring
  have hcross : crossDet v zvec = 0 := by
    rw [← inner_crossVec v zvec, ← hk]
    exact hzk
  have hnotLI : ¬ LinearIndependent ℝ (Fin.cons zvec v : Fin (n + 1) → E) := by
    intro hLIcons
    exact ((crossDet_ne_zero_iff v zvec).mpr hLIcons) hcross
  have hspan : zvec ∈ Submodule.span ℝ (Set.range v) := by
    by_contra hmem
    exact hnotLI (linearIndependent_finCons.mpr ⟨hLI, hmem⟩)
  have hker : ∀ x ∈ Submodule.span ℝ (Set.range v), ⟪zvec, x⟫ = 0 := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
        obtain ⟨i, rfl⟩ := hy
        rw [real_inner_comm]
        exact hzperp i
    | zero => simp
    | add a b _ _ ha hb => rw [inner_add_right, ha, hb]; ring
    | smul t a _ ha => rw [real_inner_smul_right, ha]; ring
  have hzz : ⟪zvec, zvec⟫ = 0 := hker zvec hspan
  have hzzero : zvec = 0 := (inner_self_eq_zero (𝕜 := ℝ) (x := zvec)).mp hzz
  have := sub_eq_zero.mp (hz ▸ hzzero)
  exact this


-- @@ L114-144 verbatim
/-- **Oriented recognition principle for `tauField`.**  A kernel vector
pairing positively with the unit kernel field is a positive multiple of it. -/
theorem tauField_eq_of_inner_pos (g : E → F) {q : E}
    (hq : q ∈ regularSet g) {w : E} (hw : fderiv ℝ g q w = 0)
    (hpos : 0 < ⟪tauField g q, w⟫) :
    tauField g q = ‖w‖⁻¹ • w := by
  have hkne : kerCross g q ≠ 0 := (kerCross_ne_zero_iff g q).mpr hq
  have hnpos : (0 : ℝ) < ‖kerCross g q‖ := norm_pos_iff.mpr hkne
  have htau : tauField g q = ‖kerCross g q‖⁻¹ • kerCross g q := rfl
  have hinner : ⟪tauField g q, w⟫ = ‖kerCross g q‖⁻¹ * ⟪kerCross g q, w⟫ := by
    rw [htau, real_inner_smul_left]
  have hkw : 0 < ⟪kerCross g q, w⟫ := by
    rw [hinner] at hpos
    have hinv : (0 : ℝ) < ‖kerCross g q‖⁻¹ := by positivity
    nlinarith
  have hmain := smul_kerCross_of_fderiv_apply_eq_zero g hq hw
  have hsq : (0 : ℝ) < ‖kerCross g q‖ ^ 2 := by positivity
  set c : ℝ := ⟪kerCross g q, w⟫ / ‖kerCross g q‖ ^ 2 with hc
  have hcpos : 0 < c := by
    rw [hc]
    exact div_pos hkw hsq
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have hkn : ‖kerCross g q‖ ≠ 0 := ne_of_gt hnpos
  have hweq : w = c • kerCross g q := by
    rw [hc, div_eq_inv_mul, ← smul_smul, ← hmain, smul_smul,
      inv_mul_cancel₀ (ne_of_gt hsq), one_smul]
  have hfinal : ‖w‖⁻¹ • w = ‖kerCross g q‖⁻¹ • kerCross g q := by
    rw [hweq, norm_smul, Real.norm_eq_abs, abs_of_pos hcpos, smul_smul]
    congr 1
    field_simp
  rw [htau, hfinal]


-- @@ L146-162 verbatim
/-- A kernel vector orthogonal to the unit kernel field vanishes. -/
theorem eq_zero_of_inner_tauField_eq_zero (g : E → F) {q : E}
    (hq : q ∈ regularSet g) {w : E} (hw : fderiv ℝ g q w = 0)
    (h0 : ⟪tauField g q, w⟫ = 0) : w = 0 := by
  have hkne : kerCross g q ≠ 0 := (kerCross_ne_zero_iff g q).mpr hq
  have hnpos : (0 : ℝ) < ‖kerCross g q‖ := norm_pos_iff.mpr hkne
  have htau : tauField g q = ‖kerCross g q‖⁻¹ • kerCross g q := rfl
  have hinner : ‖kerCross g q‖⁻¹ * ⟪kerCross g q, w⟫ = 0 := by
    rw [← real_inner_smul_left, ← htau]
    exact h0
  have hkw : ⟪kerCross g q, w⟫ = 0 := by
    have hinv : (‖kerCross g q‖⁻¹ : ℝ) ≠ 0 := by positivity
    exact (mul_eq_zero.mp hinner).resolve_left hinv
  have hmain := smul_kerCross_of_fderiv_apply_eq_zero g hq hw
  rw [hkw, zero_smul] at hmain
  have hsq : (‖kerCross g q‖ ^ 2 : ℝ) ≠ 0 := by positivity
  exact (smul_eq_zero.mp hmain).resolve_left hsq


-- @@ L164-164 verbatim
end KernelLine


-- @@ L166-166 verbatim
/-! ## The oriented transport along the isotopy -/


-- @@ L168-168 verbatim
namespace SmoothAmbientIsotopy


-- @@ L170-170 verbatim
variable {n : ℕ} (A : SmoothAmbientIsotopy n) (X : FramedLevelSet n)


-- @@ L172-172 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))


-- @@ L174-181 verbatim
/-- Joint smoothness of the spatial differential of the forward family. -/
theorem contDiff_famForwardFDeriv :
    ContDiff ℝ ∞ (fun q : ℝ × E => fderiv ℝ (fun y => A.forward q.1 y) q.2) :=
  ContDiff.fderiv
    (f := fun (q : ℝ × E) (y : E) => A.forward q.1 y)
    (g := fun q : ℝ × E => q.2)
    (A.forward_smooth.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd))
    contDiff_snd (by simp)


-- @@ L183-199 verbatim
/-- The inverse differential undoes the forward differential. -/
theorem fderiv_inverse_comp_forward {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (p : E) :
    (fderiv ℝ (A.inverse s) (A.forward s p)).comp
        (fderiv ℝ (A.forward s) p) = ContinuousLinearMap.id ℝ E := by
  have hf : HasFDerivAt (A.forward s) (fderiv ℝ (A.forward s) p) p :=
    ((A.contDiff_forward_slice s).differentiable (by simp) p).hasFDerivAt
  have hg : HasFDerivAt (A.inverse s)
      (fderiv ℝ (A.inverse s) (A.forward s p)) (A.forward s p) :=
    ((A.contDiff_inverse_slice s).differentiable (by simp) _).hasFDerivAt
  have hcomp : HasFDerivAt (fun x => A.inverse s (A.forward s x))
      ((fderiv ℝ (A.inverse s) (A.forward s p)).comp
        (fderiv ℝ (A.forward s) p)) p := hg.comp p hf
  have hid : (fun x => A.inverse s (A.forward s x)) = id :=
    funext (A.left_inv s hs)
  rw [hid] at hcomp
  exact hcomp.unique (hasFDerivAt_id p)


-- @@ L201-207 verbatim
/-- The inverse differential recovers a forward-pushed vector. -/
theorem fderiv_inverse_forward_apply {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (p w : E) :
    fderiv ℝ (A.inverse s) (A.forward s p)
        (fderiv ℝ (A.forward s) p w) = w := by
  rw [← ContinuousLinearMap.comp_apply, A.fderiv_inverse_comp_forward hs p]
  rfl


-- @@ L209-217 verbatim
/-- The forward differential is injective on `[0, 1]`. -/
theorem fderiv_forward_apply_ne_zero {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (p : E) {w : E} (hw : w ≠ 0) :
    fderiv ℝ (A.forward s) p w ≠ 0 := by
  intro h
  apply hw
  have hrec := A.fderiv_inverse_forward_apply hs p w
  rw [h, map_zero] at hrec
  exact hrec.symm


-- @@ L219-226 verbatim
/-- The chain rule for the pullback family. -/
theorem fderiv_pullbackI (s : I) (q : E) :
    fderiv ℝ (A.pullbackI X s).g q =
      (fderiv ℝ X.g (A.inverse (s : ℝ) q)).comp
        (fderiv ℝ (A.inverse (s : ℝ)) q) := by
  rw [A.pullbackI_g_fun X]
  exact ((X.smooth.differentiable (by simp) _).hasFDerivAt.comp q
    ((A.contDiff_inverse_slice (s : ℝ)).differentiable (by simp) q).hasFDerivAt).fderiv


-- @@ L228-237 verbatim
/-- The forward push of the unit kernel field lies in the kernel of the
deformed presentation. -/
theorem fderiv_pullbackI_forward_tauField (s : I) (p : E) :
    fderiv ℝ (A.pullbackI X s).g (A.forward (s : ℝ) p)
        (fderiv ℝ (A.forward (s : ℝ)) p (tauField X.g p)) = 0 := by
  have hs : (s : ℝ) ∈ Set.Icc (0 : ℝ) 1 := mem_Icc_coe s
  rw [A.fderiv_pullbackI X s, ContinuousLinearMap.comp_apply,
    A.fderiv_inverse_forward_apply hs p (tauField X.g p),
    A.left_inv (s : ℝ) hs p]
  exact fderiv_tauField_eq_zero X.g p


-- @@ L239-299 verbatim
/-- **The deformation argument.**  Along the whole isotopy the unit kernel
field of the deformed presentation pairs positively with the forward push of
the unit kernel field of the source. -/
theorem inner_tauField_pullbackI_pos (s : I) {p : E} (hp : p ∈ X.fiber) :
    0 < ⟪tauField (A.pullbackI X s).g (A.forward (s : ℝ) p),
        fderiv ℝ (A.forward (s : ℝ)) p (tauField X.g p)⟫ := by
  classical
  set τ : E := tauField X.g p with hτ
  have hτne : τ ≠ 0 := by
    intro h
    have hnorm := norm_tauField (X.fiber_subset_regularSet hp)
    rw [← hτ, h, norm_zero] at hnorm
    norm_num at hnorm
  set fpath : I → ℝ := fun t =>
    ⟪tauField (A.pullbackI X t).g (A.forward (t : ℝ) p),
      fderiv ℝ (A.forward (t : ℝ)) p τ⟫ with hfpath
  have hγc : Continuous fun t : I => A.forward (t : ℝ) p :=
    A.forward_smooth.continuous.comp
      (continuous_subtype_val.prodMk continuous_const)
  have hreg : ∀ t : I, A.forward (t : ℝ) p ∈
      regularSet (A.pullbackI X t).g :=
    fun t => A.forward_mem_pullbackI_regularSet X t hp
  have hcont1 : Continuous fun t : I =>
      tauField (A.pullbackI X t).g (A.forward (t : ℝ) p) :=
    A.continuous_pullbackI_tauField X (sf := fun t : I => t)
      (γ := fun t : I => A.forward (t : ℝ) p) continuous_id hγc hreg
  have hcontL : Continuous fun t : I =>
      fderiv ℝ (fun y => A.forward (t : ℝ) y) p :=
    (A.contDiff_famForwardFDeriv).continuous.comp
      (continuous_subtype_val.prodMk continuous_const)
  have hcont2 : Continuous fun t : I => fderiv ℝ (A.forward (t : ℝ)) p τ :=
    hcontL.clm_apply continuous_const
  have hfc : Continuous fpath := hcont1.inner hcont2
  have hne : ∀ t : I, fpath t ≠ 0 := by
    intro t hzero
    have hw : fderiv ℝ (A.forward (t : ℝ)) p τ ≠ 0 :=
      A.fderiv_forward_apply_ne_zero (mem_Icc_coe t) p hτne
    exact hw (eq_zero_of_inner_tauField_eq_zero _ (hreg t)
      (A.fderiv_pullbackI_forward_tauField X t p) hzero)
  have hzero : fpath 0 = 1 := by
    have hcoe : (((0 : I) : ℝ)) = 0 := rfl
    have h1 : (A.pullbackI X 0).g = X.g := A.pullbackI_zero_g X
    have h2 : A.forward (((0 : I) : ℝ)) p = p := by
      rw [hcoe, A.forward_zero]
      rfl
    have h3 : fderiv ℝ (A.forward (((0 : I) : ℝ))) p τ = τ := by
      rw [hcoe, A.forward_zero, fderiv_id]
      rfl
    rw [hfpath]
    simp only []
    rw [h1, h2, h3, ← hτ, real_inner_self_eq_norm_sq,
      norm_tauField (X.fiber_subset_regularSet hp)]
    norm_num
  by_contra hcon
  push_neg at hcon
  have hmem : (0 : ℝ) ∈ Set.Icc (fpath s) (fpath 0) := by
    refine ⟨hcon, ?_⟩
    rw [hzero]
    norm_num
  obtain ⟨t, ht⟩ := intermediate_value_univ (s : I) (0 : I) hfc hmem
  exact hne t ht


-- @@ L301-301 verbatim
/-! ### The endpoint statements -/


-- @@ L303-306 verbatim
theorem inner_tauField_pullback_pos {p : E} (hp : p ∈ X.fiber) :
    0 < ⟪tauField (A.pullback X).g (A.forward 1 p),
        fderiv ℝ (A.forward 1) p (tauField X.g p)⟫ :=
  A.inner_tauField_pullbackI_pos X 1 hp


-- @@ L308-311 verbatim
theorem fderiv_pullback_forward_tauField (p : E) :
    fderiv ℝ (A.pullback X).g (A.forward 1 p)
        (fderiv ℝ (A.forward 1) p (tauField X.g p)) = 0 :=
  A.fderiv_pullbackI_forward_tauField X 1 p


-- @@ L313-315 verbatim
theorem forward_mem_pullback_regularSet {p : E} (hp : p ∈ X.fiber) :
    A.forward 1 p ∈ regularSet (A.pullback X).g :=
  A.forward_mem_pullbackI_regularSet X 1 hp


-- @@ L317-353 verbatim
/-- **The usable form of the oriented transport.**

If a curve in the fiber runs in the *positive* direction of the unit kernel
field of `X`, then its image under the endpoint diffeomorphism computes the
unit kernel field of the pullback — with the sign, not just up to sign. -/
theorem tauField_pullback_of_curve
    {γ δ : ℝ → E} {u a : ℝ} (ha : 0 < a)
    (hmem : γ u ∈ X.fiber)
    (hγ : HasDerivAt γ (a • tauField X.g (γ u)) u)
    (hcomp : ∀ t, δ t = A.forward 1 (γ t))
    {d : E} (hδ : HasDerivAt δ d u) :
    tauField (A.pullback X).g (δ u) = ‖d‖⁻¹ • d := by
  set τ : E := tauField X.g (γ u) with hτ
  set L : E →L[ℝ] E := fderiv ℝ (A.forward 1) (γ u) with hL
  have hfd : HasFDerivAt (A.forward 1) L (γ u) :=
    ((A.contDiff_forward_slice 1).differentiable (by simp) (γ u)).hasFDerivAt
  have hcompderiv : HasDerivAt (fun t => A.forward 1 (γ t)) (L (a • τ)) u :=
    hfd.comp_hasDerivAt u hγ
  have hδ' : HasDerivAt δ (L (a • τ)) u := by
    have hfun : δ = fun t => A.forward 1 (γ t) := funext hcomp
    rw [hfun]
    exact hcompderiv
  have hdeq : d = a • L τ := by
    rw [hδ.unique hδ', map_smul]
  have hpt : δ u = A.forward 1 (γ u) := hcomp u
  have hpos : 0 < ⟪tauField (A.pullback X).g (A.forward 1 (γ u)), L τ⟫ :=
    A.inner_tauField_pullback_pos X hmem
  have hposd : 0 < ⟪tauField (A.pullback X).g (δ u), d⟫ := by
    rw [hpt, hdeq, real_inner_smul_right]
    exact mul_pos ha hpos
  have hker : fderiv ℝ (A.pullback X).g (δ u) d = 0 := by
    rw [hpt, hdeq, map_smul, A.fderiv_pullback_forward_tauField X (γ u),
      smul_zero]
  have hreg : δ u ∈ regularSet (A.pullback X).g := by
    rw [hpt]
    exact A.forward_mem_pullback_regularSet X hmem
  exact tauField_eq_of_inner_pos _ hreg hker hposd


-- @@ L355-355 verbatim
end SmoothAmbientIsotopy


-- @@ L357-357 verbatim
end Submission
