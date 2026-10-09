import OAI.Geometry.PolarProducts.StripEmbedding


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u70 u71 u72 u73


-- @@ L7-7 verbatim
section LowerBoundInline

-- @@ L8-8 verbatim
open Set Filter Function

-- @@ L9-9 verbatim
open scoped Topology ContDiff NNReal

-- @@ L10-10 verbatim
open Set Filter Metric

-- @@ L11-11 verbatim
open scoped Topology ContDiff

-- @@ L12-12 verbatim
open Set Filter Function MeasureTheory Metric

-- @@ L13-13 verbatim
open scoped Topology ContDiff NNReal

-- @@ L14-14 verbatim
open Set Filter Function

-- @@ L15-15 verbatim
open scoped Topology ContDiff

-- @@ L16-16 verbatim
open Set Filter Function

-- @@ L17-17 verbatim
open scoped Topology ContDiff NNReal

-- @@ L18-18 verbatim
open Set Filter

-- @@ L19-19 verbatim
open scoped Topology ContDiff

-- @@ L20-20 verbatim
open Set Filter Function

-- @@ L21-21 verbatim
open scoped Topology ContDiff

-- @@ L22-22 verbatim
open Set Filter Function

-- @@ L23-23 verbatim
open scoped ContDiff Topology

-- @@ L24-24 verbatim
open Set MeasureTheory

-- @@ L25-25 verbatim
open scoped ContDiff Interval Topology

-- @@ L26-26 verbatim
open Set

-- @@ L27-27 verbatim
open scoped Topology ContDiff

-- @@ L28-28 verbatim
open Set

-- @@ L29-29 verbatim
open Set MeasureTheory

-- @@ L30-30 verbatim
open scoped ContDiff Interval Topology

-- @@ L31-31 verbatim
open Set Filter Complex

-- @@ L32-32 verbatim
open scoped Topology ContDiff

-- @@ L33-33 verbatim
open MeasureTheory intervalIntegral Set

-- @@ L34-34 verbatim
open scoped Real


-- @@ L36-36 verbatim
namespace PolarStrips

-- @@ L37-37 verbatim
open Set Filter ComplexCoordinates

-- @@ L38-38 verbatim
open scoped Topology ContDiff

-- @@ L39-39 verbatim
noncomputable section

-- @@ L40-40 verbatim
variable {ι : Type u70} {κ : Type u71} [Fintype ι] [Fintype κ]


-- @@ L42-49 verbatim
theorem position_mem_interior (b : κ → R ι) (k : ℕ) {z : C ι}
    (hz : z ∈ domain (fun j => functional (b j))) :
    (phase b k z).1 ∈ interior (ConvexPolar.stripBody b) := by
  apply ConvexPolar.mem_interior_stripBody
  intro j
  change |inner (𝕜 := ℝ) (b j) (im z)| < 1
  rw [← im_functional]
  exact abs_lt.mpr (PlanarLens.im_mem_Ioo (hz j))


-- @@ L51-53 verbatim
theorem norm_re_le (z : C ι) : ‖re z‖ ≤ ‖z‖ := by
  have hh := norm_sq_parts z
  nlinarith [sq_nonneg ‖im z‖, norm_nonneg (re z), norm_nonneg z]


-- @@ L55-91 verbatim
theorem momentum_bound (b : κ → R ι) {k : ℕ} (hk : 1 ≤ k) {z : C ι}
    (hz : z ∈ domain (fun j => functional (b j))) {y : R ι}
    (hy : y ∈ ConvexPolar.stripBody b) {A B : ℝ}
    (hzA : ‖z‖ ≤ A) (hyB : ‖y‖ ≤ B) :
    inner (𝕜 := ℝ) y (phase b k z).2 / (k : ℝ) ≤
      A*B/(k : ℝ) + Real.pi/4*‖tuple (fun j => functional (b j)) k z‖^2 +
        (Fintype.card κ : ℝ)*PlanarLens.epsilon k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hu : inner (𝕜 := ℝ) y (-re z) ≤ A*B := by
    have hh := real_inner_le_norm y (-re z)
    rw [norm_neg] at hh
    have hm := mul_le_mul hyB ((norm_re_le z).trans hzA) (norm_nonneg _) (le_trans (norm_nonneg _) hyB)
    nlinarith
  have hj (j : κ) : -(PlanarLens.primitive k (functional (b j) z)*inner (𝕜 := ℝ) y (b j)) ≤
      |PlanarLens.primitive k (functional (b j) z)| := by
    have hh : |inner (𝕜 := ℝ) y (b j)| ≤ 1 := by rw [real_inner_comm]; exact hy j
    calc
      _ ≤ |PlanarLens.primitive k (functional (b j) z)*inner (𝕜 := ℝ) y (b j)| := neg_le_abs _
      _ = |PlanarLens.primitive k (functional (b j) z)| * |inner (𝕜 := ℝ) y (b j)| := abs_mul _ _
      _ ≤ _ := by simpa using mul_le_mul_of_nonneg_left hh (abs_nonneg (PlanarLens.primitive k (functional (b j) z)))
  have hsum : inner (𝕜 := ℝ) y (phase b k z).2 ≤ A*B+∑ j, |PlanarLens.primitive k (functional (b j) z)| := by
    have hh := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hj j)
    simp only [phase, inner_sub_right, inner_sum, real_inner_smul_right, Finset.sum_neg_distrib] at ⊢ hh
    linarith
  have hslice (j : κ) : |PlanarLens.primitive k (functional (b j) z)|/(k : ℝ) ≤
      Real.pi/4*‖PlanarLens.g (functional (b j) z)‖^(2*k)+PlanarLens.epsilon k := by
    simpa only [PlanarLens.primitive, Complex.re_add_im] using
      PlanarLens.uniform_slice hk (v := (functional (b j) z).re) (t := (functional (b j) z).im)
        (by simpa only [Complex.re_add_im] using hz j)
  calc
    _ ≤ (A*B+∑ j, |PlanarLens.primitive k (functional (b j) z)|)/(k : ℝ) :=
      div_le_div_of_nonneg_right hsum hkpos.le
    _ = A*B/(k : ℝ) + ∑ j, |PlanarLens.primitive k (functional (b j) z)|/(k : ℝ) := by
      rw [add_div, Finset.sum_div]
    _ ≤ A*B/(k : ℝ) + ∑ j, (Real.pi/4*‖PlanarLens.g (functional (b j) z)‖^(2*k)+PlanarLens.epsilon k) :=
      add_le_add le_rfl (Finset.sum_le_sum (fun j _ => hslice j))
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← norm_tuple_sq]; simp [add_assoc]


-- @@ L93-107 verbatim
theorem exists_uniform_momentum_bound (b : κ → R ι)
    (hb : Function.Injective (fun x : R ι => fun j => inner (𝕜 := ℝ) (b j) x)) :
    ∃ C B : ℝ, 0 ≤ C ∧ 0 ≤ B ∧ (∀ y ∈ ConvexPolar.stripBody b, ‖y‖ ≤ B) ∧
      ∀ k : ℕ, 1 ≤ k → ∀ z ∈ domain (fun j => functional (b j)),
        ∀ y ∈ ConvexPolar.stripBody b,
          inner (𝕜 := ℝ) y (phase b k z).2 / (k : ℝ) ≤
            C/(k : ℝ)+Real.pi/4*‖tuple (fun j => functional (b j)) k z‖^2 +
              (Fintype.card κ : ℝ)*PlanarLens.epsilon k := by
  obtain ⟨A, hA⟩ := (isBounded_domain _ (functional_injective b hb)).exists_norm_le
  obtain ⟨B, hB⟩ := (ConvexPolar.isCompact_stripBody b hb).isBounded.exists_norm_le
  have hA0 : 0 ≤ A := (norm_nonneg (0 : C ι)).trans (hA 0 (zero_mem_domain _))
  have hB0 : 0 ≤ B := (norm_nonneg (0 : R ι)).trans (hB 0 (interior_subset (ConvexPolar.zero_mem_interior_stripBody b)))
  refine ⟨A*B, B, mul_nonneg hA0 hB0, hB0, hB, ?_⟩
  intro k hk z hz y hy
  exact momentum_bound b hk hz hy (hA z hz) (hB y hy)


-- @@ L109-141 verbatim
theorem exists_scaled_image (b : κ → R ι)
    (hb : Function.Injective (fun x : R ι => fun j => inner (𝕜 := ℝ) (b j) x))
    {η : ℝ} (hη : 0 < η) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ z : C ι,
      z ∈ domain (fun j => functional (b j)) → ‖tuple (fun j => functional (b j)) k z‖^2 < 1 →
      (phase b k z).1 ∈ interior (ConvexPolar.stripBody b) ∧
        (((1+η)*Real.pi*(k : ℝ)/4)⁻¹ • (phase b k z).2) ∈ interior (ConvexPolar.polar (ConvexPolar.stripBody b)) := by
  obtain ⟨C, B, _hC, hB, hbound, hmoment⟩ := exists_uniform_momentum_bound b hb
  have ht : Tendsto (fun k : ℕ => C/(k : ℝ)+(Fintype.card κ : ℝ)*PlanarLens.epsilon k) atTop (𝓝 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat C).add (PlanarLens.tendsto_epsilon.const_mul (Fintype.card κ : ℝ))
  have hsmall := ht.eventually (eventually_lt_nhds (show (0 : ℝ) < η*Real.pi/4 by positivity))
  obtain ⟨k, hk, hksmall⟩ := (eventually_ge_atTop (1 : ℕ)).and hsmall |>.exists
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  let T := (1+η)*Real.pi/4
  have hT : 0 < T := by dsimp [T]; positivity
  have hTsmall : C/(k : ℝ)+Real.pi/4+(Fintype.card κ : ℝ)*PlanarLens.epsilon k < T := by dsimp [T]; nlinarith
  refine ⟨k, hk, fun z hz hτ => ⟨position_mem_interior b k hz, ?_⟩⟩
  apply ConvexPolar.mem_interior_polar_of_bound hB hbound
    (r := (C/(k : ℝ)+Real.pi/4+(Fintype.card κ : ℝ)*PlanarLens.epsilon k)/T)
  · exact (div_lt_one hT).mpr hTsmall
  · intro y hy
    have hh := hmoment k hk z hz y hy
    have hp : inner (𝕜 := ℝ) y (phase b k z).2/(k : ℝ) ≤
        C/(k : ℝ)+Real.pi/4+(Fintype.card κ : ℝ)*PlanarLens.epsilon k := by
      have hm := mul_le_mul_of_nonneg_left hτ.le (by positivity : (0 : ℝ) ≤ Real.pi/4)
      linarith
    have hd := div_le_div_of_nonneg_right hp hT.le
    calc
      _ = inner (𝕜 := ℝ) y (phase b k z).2/(k : ℝ)/T := by
        rw [real_inner_smul_right]
        dsimp only [T]
        field_simp
      _ ≤ _ := hd


-- @@ L143-143 verbatim
end

-- @@ L144-144 verbatim
end PolarStrips


-- @@ L146-146 verbatim
open Set

-- @@ L147-147 verbatim
open scoped ContDiff ENNReal


-- @@ L149-149 verbatim
namespace SymmetricPolar


-- @@ L151-151 verbatim
end SymmetricPolar


-- @@ L153-153 verbatim
namespace LocalEmbedding

-- @@ L154-154 verbatim
open Set Filter

-- @@ L155-155 verbatim
open scoped Topology ContDiff

-- @@ L156-156 verbatim
noncomputable section

-- @@ L157-158 verbatim
variable {E : Type u72} {F : Type u73} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


-- @@ L160-172 verbatim
theorem open_image {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U)
    (hD : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible) : IsOpen (f '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨x, hx, rfl⟩
  have hs := hf.contDiffAt (hU.mem_nhds hx)
  obtain ⟨e, heq⟩ := hD x hx
  have he : HasFDerivAt f e.toContinuousLinearMap x := by
    rw [heq]
    exact (hs.differentiableAt (by simp)).hasFDerivAt
  rw [← (hs.hasStrictFDerivAt' he (by simp)).map_nhds_eq_of_equiv]
  change f ⁻¹' (f '' U) ∈ 𝓝 x
  exact mem_of_superset (hU.mem_nhds hx) (fun y hy => mem_image_of_mem f hy)


-- @@ L174-186 verbatim
theorem isOpenEmbedding {U : Set E} (hU : IsOpen U) {f : E → F}
    (hf : ContDiffOn ℝ ∞ f U) (hi : InjOn f U)
    (hD : ∀ x ∈ U, (fderiv ℝ f x).IsInvertible) :
    Topology.IsOpenEmbedding (fun x : U => f x) := by
  apply Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hf.continuousOn.domRestrict
  · intro x y h; exact Subtype.ext (hi x.2 y.2 h)
  · intro V hV
    have hUV : Subtype.val '' V ⊆ U := by rintro _ ⟨x, _, rfl⟩; exact x.2
    have huV : IsOpen (Subtype.val '' V) := hU.isOpenMap_subtype_val _ hV
    have ho := open_image huV (hf.mono hUV) (fun x hx => hD x (hUV hx))
    change IsOpen ((fun x : U => f x) '' V)
    rw [image_image] at ho
    exact ho


-- @@ L188-188 verbatim
end

-- @@ L189-189 verbatim
end LocalEmbedding


-- @@ L191-191 verbatim
namespace SymmetricPolar

-- @@ L192-192 verbatim
open Set Filter

-- @@ L193-193 verbatim
open scoped ContDiff Topology

-- @@ L194-194 verbatim
noncomputable section

-- @@ L195-195 verbatim
variable {n : ℕ}


-- @@ L197-198 verbatim
theorem isOpen_capacityBall (n : ℕ) (c : ℝ) : IsOpen (capacityBall n c) :=
  isOpen_lt (by fun_prop) continuous_const


-- @@ L200-202 verbatim
def diagScale (a b : ℝ) : Phase n →L[ℝ] Phase n :=
  (a • ContinuousLinearMap.fst ℝ (Position n) (Position n)).prod
    (b • ContinuousLinearMap.snd ℝ (Position n) (Position n))


-- @@ L204-204 verbatim
@[simp] theorem diagScale_apply (a b : ℝ) (z : Phase n) : diagScale a b z = (a • z.1, b • z.2) := rfl


-- @@ L206-210 verbatim
theorem diagScale_injective {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Function.Injective (diagScale a b : Phase n → Phase n) := by
  intro x y h
  exact Prod.ext ((smul_right_injective _ ha) (congrArg Prod.fst h))
    ((smul_right_injective _ hb) (congrArg Prod.snd h))


-- @@ L212-215 verbatim
theorem omega0_diagScale (a b : ℝ) (v w : Phase n) :
    omega0 (diagScale a b v) (diagScale a b w) = (a*b)*omega0 v w := by
  simp only [omega0, diagScale_apply, real_inner_smul_left, real_inner_smul_right]
  ring


-- @@ L217-222 verbatim
theorem omega0_nondegenerate (v : Phase n) (h : ∀ w : Phase n, omega0 v w = 0) : v = 0 := by
  have hh := h (-v.2, v.1)
  simp only [omega0, inner_neg_left, real_inner_self_eq_norm_sq, sub_neg_eq_add] at hh
  have h1 : v.1 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg v.1, sq_nonneg ‖v.2‖])
  have h2 : v.2 = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg v.2, sq_nonneg ‖v.1‖])
  exact Prod.ext h1 h2


-- @@ L224-236 verbatim
theorem isInvertible_of_preserves_omega0 (L : Phase n →L[ℝ] Phase n)
    (hL : ∀ v w, omega0 (L v) (L w) = omega0 v w) : L.IsInvertible := by
  have hi : Function.Injective L := by
    intro v w hvw
    have hz : L (v-w) = 0 := by rw [map_sub, hvw, sub_self]
    apply sub_eq_zero.mp
    apply omega0_nondegenerate
    intro a
    rw [← hL, hz]
    simp [omega0]
  have hs : Function.Surjective L := LinearMap.surjective_of_injective hi
  exact ⟨ContinuousLinearEquiv.ofBijective L (LinearMap.ker_eq_bot.mpr hi)
    (LinearMap.range_eq_top.mpr hs), rfl⟩


-- @@ L238-244 verbatim
theorem hasSymplecticEmbedding_of_injOn {U V : Set (Phase n)} (hU : IsOpen U)
    {e : Phase n → Phase n} (he : ContDiffOn ℝ ∞ e U) (hi : InjOn e U)
    (hm : MapsTo e U V) (hω : ∀ z ∈ U, ∀ v w,
      omega0 (fderiv ℝ e z v) (fderiv ℝ e z w) = omega0 v w) :
    HasSymplecticEmbedding U V := by
  refine ⟨e, he, ?_, hm, hω⟩
  exact (LocalEmbedding.isOpenEmbedding hU he hi (fun z hz => isInvertible_of_preserves_omega0 _ (hω z hz))).isEmbedding


-- @@ L246-249 verbatim
theorem HasSymplecticEmbedding.mono_target {U V W : Set (Phase n)}
    (h : HasSymplecticEmbedding U V) (hVW : V ⊆ W) : HasSymplecticEmbedding U W := by
  rcases h with ⟨e, he, hi, hm, hω⟩
  exact ⟨e, he, hi, hm.mono_right hVW, hω⟩


-- @@ L251-254 verbatim
theorem HasSymplecticEmbedding.injOn {U : Set (Phase n)} {e : Phase n → Phase n}
    (he : Topology.IsEmbedding (fun z : U => e z)) : InjOn e U := by
  intro x hx y hy h
  exact congrArg Subtype.val (he.injective (show e (⟨x,hx⟩ : U) = e (⟨y,hy⟩ : U) from h))


-- @@ L256-264 verbatim
theorem mapsTo_scaled_ball {lam c : ℝ} (hlam : 0 < lam) :
    MapsTo (diagScale (Real.sqrt lam) (Real.sqrt lam) : Phase n → Phase n)
      (capacityBall n c) (capacityBall n (lam*c)) := by
  intro z hz
  change Real.pi*(‖Real.sqrt lam • z.1‖^2+‖Real.sqrt lam • z.2‖^2) < lam*c
  have hsq : |Real.sqrt lam|^2 = lam := by rw [sq_abs, Real.sq_sqrt hlam.le]
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, hsq]
  have hh := mul_lt_mul_of_pos_left hz hlam
  nlinarith


-- @@ L266-297 verbatim
theorem embedding_of_scaled_ball_map {lam c a b : ℝ} (hlam : 0 < lam) (hab : a*b = lam⁻¹)
    {V : Set (Phase n)} {e : Phase n → Phase n}
    (he : ContDiffOn ℝ ∞ e (capacityBall n (lam*c)))
    (hi : InjOn e (capacityBall n (lam*c)))
    (hm : MapsTo (fun z => diagScale a b (e z)) (capacityBall n (lam*c)) V)
    (hω : ∀ z ∈ capacityBall n (lam*c), ∀ v w,
      omega0 (fderiv ℝ e z v) (fderiv ℝ e z w) = omega0 v w) :
    HasSymplecticEmbedding (capacityBall n c) V := by
  let D : Phase n →L[ℝ] Phase n := diagScale (Real.sqrt lam) (Real.sqrt lam)
  let L : Phase n →L[ℝ] Phase n := diagScale a b
  let F : Phase n → Phase n := fun z => L (e (D z))
  have hD : MapsTo D (capacityBall n c) (capacityBall n (lam*c)) := mapsTo_scaled_ball hlam
  have hLinj : Function.Injective L := diagScale_injective (left_ne_zero_of_mul (by rw [hab]; exact inv_ne_zero hlam.ne'))
    (right_ne_zero_of_mul (by rw [hab]; exact inv_ne_zero hlam.ne'))
  have hDinj : Function.Injective D := diagScale_injective (Real.sqrt_pos.mpr hlam).ne' (Real.sqrt_pos.mpr hlam).ne'
  have hs (z : Phase n) (hz : z ∈ capacityBall n c) : ContDiffAt ℝ ∞ e (D z) :=
    he.contDiffAt ((isOpen_capacityBall _ _).mem_nhds (hD hz))
  apply hasSymplecticEmbedding_of_injOn (isOpen_capacityBall n c) (e := F)
  · intro z hz
    exact (L.contDiff.contDiffAt.comp z ((hs z hz).comp z D.contDiff.contDiffAt)).contDiffWithinAt
  · intro z hz w hw h
    exact hDinj (hi (hD hz) (hD hw) (hLinj h))
  · intro z hz
    exact hm (hD hz)
  · intro z hz v w
    have hd : HasFDerivAt F (L.comp ((fderiv ℝ e (D z)).comp D)) z :=
      L.hasFDerivAt.comp z (((hs z hz).differentiableAt (by simp)).hasFDerivAt.comp z D.hasFDerivAt)
    rw [hd.fderiv]
    change omega0 (diagScale a b (fderiv ℝ e (D z) (D v)))
      (diagScale a b (fderiv ℝ e (D z) (D w))) = _
    rw [omega0_diagScale, hω _ (hD hz), hab, omega0_diagScale]
    rw [← pow_two, Real.sq_sqrt hlam.le, ← mul_assoc, inv_mul_cancel₀ hlam.ne', one_mul]


-- @@ L299-299 verbatim
end

-- @@ L300-300 verbatim
end SymmetricPolar


-- @@ L302-302 verbatim
end LowerBoundInline


-- @@ L304-304 verbatim
end OAI
