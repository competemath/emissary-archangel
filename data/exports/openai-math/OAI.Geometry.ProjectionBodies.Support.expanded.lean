import OAI.Geometry.ProjectionBodies.SphericalCore


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uE


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open Set MeasureTheory Metric Filter Topology Function

-- @@ L9-9 verbatim
open scoped ENNReal NNReal RealInnerProductSpace Pointwise

-- @@ L10-10 verbatim
namespace PettyProjection


-- @@ L12-14 verbatim
/-- The actual support function of a compact body, not a surrogate gauge. -/
def support {n : ℕ} (K : Set (Space n)) (u : Space n) : ℝ :=
  sSup ((fun x => ⟪u,x⟫) '' K)


-- @@ L16-18 verbatim
lemma support_attained {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    (u : Space n) : ∃ x ∈ K, support K u = ⟪u,x⟫ :=
  hK.exists_sSup_image_eq hKn (by fun_prop)


-- @@ L20-22 verbatim
lemma inner_le_support {n : ℕ} {K : Set (Space n)} (hK : IsCompact K)
    {x : Space n} (hx : x ∈ K) (u : Space n) : ⟪u,x⟫ ≤ support K u := by
  exact le_csSup (hK.bddAbove_image (by fun_prop)) (mem_image_of_mem _ hx)


-- @@ L24-30 verbatim
lemma support_le_iff {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    {u : Space n} {a : ℝ} : support K u ≤ a ↔ ∀ x ∈ K, ⟪u,x⟫ ≤ a := by
  constructor
  · intro h x hx; exact (inner_le_support hK hx u).trans h
  · intro h
    obtain ⟨x,hx,he⟩ := support_attained hK hKn u
    rw [he]; exact h x hx


-- @@ L32-34 verbatim
lemma support_continuous {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) :
    Continuous (support K) :=
  hK.continuous_sSup (by fun_prop)


-- @@ L36-49 verbatim
lemma support_lipschitz {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    {R : ℝ≥0} (hR : ∀ x ∈ K, ‖x‖ ≤ R) : LipschitzWith R (support K) := by
  apply LipschitzWith.of_le_add_mul
  intro u v
  obtain ⟨x,hx,he⟩ := support_attained hK hKn u
  rw [he]
  have hi := inner_le_support hK hx v
  have hbound : ⟪u-v,x⟫ ≤ R*dist u v := by
    calc
      _ ≤ ‖u-v‖*‖x‖ := real_inner_le_norm _ _
      _ ≤ ‖u-v‖*R := mul_le_mul_of_nonneg_left (hR x hx) (norm_nonneg _)
      _ = _ := by rw [dist_eq_norm]; ring
  rw [inner_sub_left] at hbound
  linarith


-- @@ L51-60 verbatim
lemma support_smul {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    {r : ℝ} (hr : 0 ≤ r) (u : Space n) : support K (r • u) = r*support K u := by
  apply le_antisymm
  · apply (support_le_iff hK hKn).mpr
    intro x hx
    rw [real_inner_smul_left]
    exact mul_le_mul_of_nonneg_left (inner_le_support hK hx u) hr
  · obtain ⟨x,hx,he⟩ := support_attained hK hKn u
    rw [he]
    simpa only [real_inner_smul_left] using inner_le_support hK hx (r • u)


-- @@ L62-67 verbatim
lemma support_add_le {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    (u v : Space n) : support K (u+v) ≤ support K u+support K v := by
  apply (support_le_iff hK hKn).mpr
  intro x hx
  rw [inner_add_left]
  exact add_le_add (inner_le_support hK hx u) (inner_le_support hK hx v)


-- @@ L69-71 verbatim
lemma support_nonneg {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (h0 : 0 ∈ K)
    (u : Space n) : 0 ≤ support K u := by
  simpa only [inner_zero_right] using inner_le_support hK h0 u


-- @@ L73-84 verbatim
lemma support_minkowski {n : ℕ} {K L : Set (Space n)}
    (hK : IsCompact K) (hKn : K.Nonempty) (hL : IsCompact L) (hLn : L.Nonempty)
    (u : Space n) : support (K+L) u = support K u+support L u := by
  apply le_antisymm
  · apply (support_le_iff (hK.add hL) (hKn.add hLn)).mpr
    rintro _ ⟨x,hx,y,hy,rfl⟩
    rw [inner_add_right]
    exact add_le_add (inner_le_support hK hx u) (inner_le_support hL hy u)
  · obtain ⟨x,hx,hxe⟩ := support_attained hK hKn u
    obtain ⟨y,hy,hye⟩ := support_attained hL hLn u
    rw [hxe,hye,← inner_add_right]
    exact inner_le_support (hK.add hL) (add_mem_add hx hy) u


-- @@ L86-96 verbatim
lemma support_linear_image {n : ℕ} {K : Set (Space n)} (hK : IsCompact K) (hKn : K.Nonempty)
    (T : Space n →L[ℝ] Space n) (u : Space n) :
    support (T '' K) u = support K (T.adjoint u) := by
  apply le_antisymm
  · apply (support_le_iff (hK.image T.continuous) (hKn.image T)).mpr
    rintro _ ⟨x,hx,rfl⟩
    rw [← ContinuousLinearMap.adjoint_inner_left]
    exact inner_le_support hK hx _
  · obtain ⟨x,hx,he⟩ := support_attained hK hKn (T.adjoint u)
    rw [he,ContinuousLinearMap.adjoint_inner_left]
    exact inner_le_support (hK.image T.continuous) (mem_image_of_mem T hx) u


-- @@ L98-113 verbatim
lemma mem_iff_inner_le_support {n : ℕ} {K : Set (Space n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hKn : K.Nonempty) {x : Space n} :
    x ∈ K ↔ ∀ u : Space n, ⟪u,x⟫ ≤ support K u := by
  constructor
  · intro hx u; exact inner_le_support hK hx u
  · intro hx
    by_contra hn
    obtain ⟨f,a,hfa,hax⟩ := geometric_hahn_banach_closed_point hc hK.isClosed hn
    let u := (InnerProductSpace.toDual ℝ (Space n)).symm f
    have hu (y : Space n) : ⟪u,y⟫ = f y := by
      change (InnerProductSpace.toDual ℝ (Space n)) u y = f y
      rw [LinearIsometryEquiv.apply_symm_apply]
    obtain ⟨y,hy,he⟩ := support_attained hK hKn u
    have h := hx u
    rw [he,hu,hu] at h
    exact (not_lt_of_ge h) ((hfa y hy).trans hax)


-- @@ L115-123 verbatim
lemma support_eq_iff {n : ℕ} {K L : Set (Space n)}
    (hK : IsCompact K) (hcK : Convex ℝ K) (hKn : K.Nonempty)
    (hL : IsCompact L) (hcL : Convex ℝ L) (hLn : L.Nonempty) :
    support K = support L ↔ K = L := by
  constructor
  · intro h
    ext x
    rw [mem_iff_inner_le_support hK hcK hKn,mem_iff_inner_le_support hL hcL hLn,h]
  · rintro rfl; rfl


-- @@ L125-125 verbatim
end PettyProjection

-- @@ L126-126 verbatim
end


-- @@ L128-128 verbatim
noncomputable section

-- @@ L129-129 verbatim
open Set MeasureTheory Metric Filter Topology

-- @@ L130-130 verbatim
open scoped ENNReal RealInnerProductSpace Pointwise

-- @@ L131-131 verbatim
namespace PettyProjection.Spherical


-- @@ L133-141 verbatim
lemma harmonicSpace_isHilbertSum {n : ℕ} (hn : 2 ≤ n) [NeZero n] :
    IsHilbertSum ℝ (fun d : ℕ => harmonicSpace n d)
      (fun d : ℕ => (harmonicSpace n d).subtypeₗᵢ) := by
  let F : ℕ → Submodule ℝ (H n) := fun d => harmonicSpace n d
  have horth : OrthogonalFamily ℝ (fun d => F d) (fun d => (F d).subtypeₗᵢ) :=
    harmonicSpace_orthogonal hn
  have htotal : (⨆ d, F d).topologicalClosure = ⊤ := harmonicSpace_total hn
  let : ∀ d, CompleteSpace (F d) := fun d => FiniteDimensional.complete ℝ (harmonicSpace n d)
  exact IsHilbertSum.mkInternal F horth htotal.ge


-- @@ L143-143 verbatim
open MvPolynomial


-- @@ L145-150 verbatim
lemma polynomialL2_X_mul_X (n : ℕ) [NeZero n] (i j : Fin n) :
    polynomialL2 n (X i * X j) = toH n (coordinateProduct n i j) := by
  change toH n (polynomialRestriction n (X i * X j)) = _
  congr 1
  ext u
  simp [polynomialRestriction_apply, polynomialFunction, coordinateProduct]


-- @@ L152-168 verbatim
lemma polynomialL2_X_mul_mem_lowSpace {n : ℕ} [NeZero n] (i : Fin n)
    {p : MvPolynomial (Fin n) ℝ} (hp : p.IsHomogeneous 1) :
    polynomialL2 n (X i * p) ∈ lowSpace n := by
  have hmem : p ∈ Submodule.span ℝ (Set.range (X : Fin n → MvPolynomial (Fin n) ℝ)) := by
    rw [← homogeneousSubmodule_one_eq_span_X]
    exact hp
  clear hp
  induction hmem using Submodule.span_induction with
  | mem q hq =>
      obtain ⟨j, rfl⟩ := hq
      rw [polynomialL2_X_mul_X]
      exact Submodule.subset_span ⟨(i,j), rfl⟩
  | zero => simp
  | add p q _ _ hp hq =>
      simpa only [mul_add, map_add] using Submodule.add_mem (lowSpace n) hp hq
  | smul c p _ hp =>
      simpa only [mul_smul_comm, map_smul] using Submodule.smul_mem (lowSpace n) c hp


-- @@ L170-177 verbatim
lemma homogeneous_two_mem_lowSpace {n : ℕ} [NeZero n] {p : MvPolynomial (Fin n) ℝ}
    (hp : p.IsHomogeneous 2) : polynomialL2 n p ∈ lowSpace n := by
  have hsum : polynomialL2 n (∑ i : Fin n, X i * pderiv i p) ∈ lowSpace n := by
    rw [map_sum]
    exact Submodule.sum_mem _ fun i _ => polynomialL2_X_mul_mem_lowSpace i hp.pderiv
  have htwo : (2 : ℝ) • polynomialL2 n p ∈ lowSpace n := by
    simpa only [hp.sum_X_mul_pderiv, two_nsmul, map_add, two_smul ℝ] using hsum
  exact (Submodule.smul_mem_iff (lowSpace n) (by norm_num : (2 : ℝ) ≠ 0)).mp htwo


-- @@ L179-182 verbatim
lemma harmonicSpace_two_le_lowSpace (n : ℕ) [NeZero n] :
    harmonicSpace n 2 ≤ lowSpace n := by
  rintro v ⟨p, hp, rfl⟩
  exact homogeneous_two_mem_lowSpace hp.1


-- @@ L184-184 verbatim
end PettyProjection.Spherical

-- @@ L185-185 verbatim
end


-- @@ L187-187 verbatim
noncomputable section

-- @@ L188-188 verbatim
open MeasureTheory Set Filter Topology

-- @@ L189-189 verbatim
open scoped ENNReal RealInnerProductSpace

-- @@ L190-190 verbatim
namespace PettyProjection


-- @@ L192-192 verbatim
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- @@ L193-193 verbatim
variable {F : ℕ → Submodule ℝ E} [∀ i, CompleteSpace (F i)]


-- @@ L195-205 verbatim
lemma hilbertSum_component (h : IsHilbertSum ℝ (fun i => F i) (fun i => (F i).subtypeₗᵢ))
    (x : E) (i : ℕ) :
    (F i).starProjection x = (h.linearIsometryEquiv x i : E) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (h.linearIsometryEquiv x i).property
  intro w hw
  have hh := h.linearIsometryEquiv.symm.inner_map_map (h.linearIsometryEquiv x)
    (lp.single 2 i (⟨w,hw⟩ : F i))
  rw [LinearIsometryEquiv.symm_apply_apply, h.linearIsometryEquiv_symm_apply_single,
    lp.inner_single_right] at hh
  change ⟪x, w⟫ = ⟪(h.linearIsometryEquiv x i : E), w⟫ at hh
  rw [inner_sub_left, hh, sub_self]


-- @@ L207-211 verbatim
lemma hilbertSum_hasSum_projection (h : IsHilbertSum ℝ (fun i => F i) (fun i => (F i).subtypeₗᵢ))
    (x : E) : HasSum (fun i => (F i).starProjection x) x := by
  have hh := h.hasSum_linearIsometryEquiv_symm (h.linearIsometryEquiv x)
  rw [LinearIsometryEquiv.symm_apply_apply] at hh
  simpa only [hilbertSum_component h, Submodule.coe_subtypeₗᵢ, Submodule.coe_subtype] using hh


-- @@ L213-218 verbatim
lemma hilbertSum_hasSum_projection_norm_sq
    (h : IsHilbertSum ℝ (fun i => F i) (fun i => (F i).subtypeₗᵢ)) (x : E) :
    HasSum (fun i => ‖(F i).starProjection x‖ ^ 2) (‖x‖ ^ 2) := by
  have hh := lp.hasSum_norm (by norm_num : 0 < (2 : ℝ≥0∞).toReal) (h.linearIsometryEquiv x)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map,
    hilbertSum_component h, Submodule.norm_coe] using hh


-- @@ L220-220 verbatim
end PettyProjection

-- @@ L221-221 verbatim
end


-- @@ L223-223 verbatim
end OAI
