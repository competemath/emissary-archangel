import OAI.Combinatorics.SparsestCut.ChartLinear


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u1 u2


-- @@ L7-7 verbatim
open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal

-- @@ L8-8 verbatim
open MeasureTheory ProbabilityTheory Set Filter Matrix


-- @@ L10-10 verbatim
noncomputable section


-- @@ L12-12 verbatim
namespace UniformSparsestCut.SourceCharts

-- @@ L13-13 verbatim
open scoped BigOperators RealInnerProductSpace

-- @@ L14-14 verbatim
open Filter Set

-- @@ L15-15 verbatim
noncomputable section

-- @@ L16-16 verbatim
variable {m : ℕ} (f : PivotFamily.PFamily m) (hm : 0 < m)

-- @@ L17-17 verbatim
local notation "E" => EuclideanSpace ℝ (Fin m)

-- @@ L18-18 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m^6))

-- @@ L19-19 verbatim
def u (s : Fin (m^3)) (i : Fin (m^6)) : E := (Real.sqrt m)⁻¹ • f.g s i

-- @@ L20-20 verbatim
def lower (m : ℕ) : ℝ := (m:ℝ)^6/(2*m)

-- @@ L21-21 verbatim
include hm

-- @@ L22-22 verbatim
lemma lower_pos : 0<lower m := by unfold lower; positivity

-- @@ L23-29 verbatim
lemma energy (s : Fin (m^3)) (x : E) : lower m*‖x‖^2≤‖FrameCharts.chart (u f s) x‖^2 := by
  have hc (v : E) (hv : ‖v‖=1) := f.covariance s v hv
  have h := (FrameCharts.normalized_bounds (f.g s) hm (pow_pos hm _) (by
    intro v hv
    simpa only [DirectionInterpolation.empiricalCov,real_inner_comm,div_eq_mul_inv,mul_comm] using hc v hv) x).1
  change (m:ℝ)^6/(2*m)*‖x‖^2≤‖FrameCharts.chart (fun i => (Real.sqrt m)⁻¹ • f.g s i) x‖^2
  simpa only [Nat.cast_pow] using h

-- @@ L30-31 verbatim
def B (s : Fin (m^3)) : F →L[ℝ] E :=
  ChartLinear.pseudoInverse (FrameCharts.chart (u f s)) (lower_pos hm) (energy f hm s)

-- @@ L32-34 verbatim
lemma B_left (s : Fin (m^3)) (x : E) : B f hm s (FrameCharts.chart (u f s) x)=x := by
  have h := ChartLinear.pseudoInverse_comp (FrameCharts.chart (u f s)) (lower_pos hm) (energy f hm s)
  exact congrArg (fun L : E →L[ℝ] E => L x) h

-- @@ L35-36 verbatim
lemma u_norm (s : Fin (m^3)) (i : Fin (m^6)) : 1/2≤‖u f s i‖ ∧ ‖u f s i‖≤2 :=
  FrameCharts.normalized_norms (f.g s) hm (f.norms s) i

-- @@ L37-39 verbatim
lemma u_nonzero (s : Fin (m^3)) (i : Fin (m^6)) : u f s i≠0 := by
  have h := (u_norm f hm s i).1
  intro hz; rw [hz,norm_zero] at h; norm_num at h

-- @@ L40-48 verbatim
lemma u_nonparallel (s : Fin (m^3)) (i j : Fin (m^6)) (hij : i≠j) (t : ℝ) :
    u f s i≠t • u f s j := by
  intro h
  apply f.nonparallel s i j hij t
  have hq : (Real.sqrt m)⁻¹≠0 := inv_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hm)))
  have he := congrArg (fun x : E => Real.sqrt m • x) h
  have hq0 : Real.sqrt (m:ℝ)≠0 := ne_of_gt (Real.sqrt_pos.mpr (by exact_mod_cast hm))
  have hmul : Real.sqrt (m:ℝ)*(t*(Real.sqrt (m:ℝ))⁻¹)=t := by field_simp
  simpa only [u,smul_smul,mul_inv_cancel₀ hq0,hmul,one_smul] using he

-- @@ L49-54 verbatim
lemma u_pivot (s : Fin (m^3)) (i : Fin (m^6)) (j : Fin m ) :
    1/((m:ℝ)^30*Real.sqrt m) < |u f s i j| := by
  have hq : 0<Real.sqrt m := Real.sqrt_pos.mpr (by exact_mod_cast hm)
  change _ < |(Real.sqrt m)⁻¹*(f.g s i j)|
  rw [abs_mul,abs_of_pos (inv_pos.mpr hq)]
  simpa only [one_div,mul_inv,mul_comm] using mul_lt_mul_of_pos_left (f.pivot s i j) (inv_pos.mpr hq)

-- @@ L55-61 verbatim
lemma B_column (s : Fin (m^3)) (i : Fin (m^6)) :
    ‖B f hm s (EuclideanSpace.single i 1)‖≤4*((m:ℝ)/(m:ℝ)^6) := by
  have h := ChartLinear.pseudoInverse_column (FrameCharts.chart (u f s)) (lower_pos hm) (energy f hm s) (EuclideanSpace.single i 1)
  rw [FrameCharts.chart_adjoint_single] at h
  calc
    _ ≤ 2/lower m := h.trans (div_le_div_of_nonneg_right (u_norm f hm s i).2 (lower_pos hm).le)
    _ = _ := by unfold lower; field_simp; ring

-- @@ L62-63 verbatim
lemma B_norm (s : Fin (m^3)) (x : F) : ‖B f hm s x‖≤‖x‖/Real.sqrt (lower m) :=
  ChartLinear.pseudoInverse_norm _ (lower_pos hm) (energy f hm s) x

-- @@ L64-66 verbatim
lemma residual_norm (s : Fin (m^3)) (x : F) :
    ‖x-FrameCharts.chart (u f s) (B f hm s x)‖≤‖x‖ :=
  ChartLinear.residual_norm _ (lower_pos hm) (energy f hm s) x

-- @@ L67-67 verbatim
end

-- @@ L68-68 verbatim
end UniformSparsestCut.SourceCharts


-- @@ L70-70 verbatim
namespace UniformSparsestCut.HyperplaneCount

-- @@ L71-72 verbatim
variable {E : Type u1} {ι : Type u2} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
  [Fintype ι] [DecidableEq ι]


-- @@ L74-105 verbatim
omit [FiniteDimensional ℝ E] [Fintype ι] in
lemma shattered_independent (f : ι → E →ₗ[ℝ] ℝ) (A : Finset (Finset ι))
    (hA : ∀ u ∈ A, ∃ x : E, ∀ i, f i x ≠ 0 ∧ (0 < f i x ↔ i ∈ u))
    {s : Finset ι} (hs : A.Shatters s) : LinearIndependent ℝ (fun i : s => f i) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  by_contra hj
  let t := s.filter (fun i => ∀ hi : i ∈ s, 0 < c ⟨i,hi⟩)
  obtain ⟨u,hu,htu⟩ := hs (t := t) (Finset.filter_subset _ _)
  obtain ⟨x,hx⟩ := hA u hu
  have hsign (i : s) : 0 < f i x ↔ 0 < c i := by
    rw [(hx i).2]
    have he : i.val ∈ s ∩ u ↔ i.val ∈ t := by rw [htu]
    simp only [Finset.mem_inter, i.property, true_and, t, Finset.mem_filter] at he
    exact he.trans ⟨fun h => h trivial, fun h _ => h⟩
  have hprod (i : s) : 0 ≤ c i * f i x := by
    by_cases hp : 0 < c i
    · exact le_of_lt (mul_pos hp ((hsign i).mpr hp))
    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_gt hp)
        (le_of_not_gt (mt (hsign i).mp hp))
  have hpj : 0 < c j * f j x := by
    by_cases hp : 0 < c j
    · exact mul_pos hp ((hsign j).mpr hp)
    · have hn : c j < 0 := lt_of_le_of_ne (le_of_not_gt hp) hj
      have hf : f j x < 0 := lt_of_le_of_ne (le_of_not_gt (mt (hsign j).mp hp)) (hx j).1
      exact mul_pos_of_neg_of_neg hn hf
  have hp : 0 < ∑ i : s, c i * f i x :=
    Finset.sum_pos' (fun i _ => hprod i) ⟨j, Finset.mem_univ _, hpj⟩
  have hz := congrArg (fun L : E →ₗ[ℝ] ℝ => L x) hc
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply] at hz
  linarith


-- @@ L107-114 verbatim
omit [Fintype ι] in
lemma vcDim_le (f : ι → E →ₗ[ℝ] ℝ) (A : Finset (Finset ι))
    (hA : ∀ u ∈ A, ∃ x : E, ∀ i, f i x ≠ 0 ∧ (0 < f i x ↔ i ∈ u)) :
    A.vcDim ≤ Module.finrank ℝ E := by
  apply Finset.sup_le
  intro s hs
  have h := (shattered_independent f A hA (Finset.mem_shatterer.mp hs)).fintype_card_le_finrank
  simpa using h


-- @@ L116-122 verbatim
lemma sign_patterns_bound (f : ι → E →ₗ[ℝ] ℝ) (A : Finset (Finset ι))
    (hA : ∀ u ∈ A, ∃ x : E, ∀ i, f i x ≠ 0 ∧ (0 < f i x ↔ i ∈ u)) :
    A.card ≤ ∑ k ∈ Finset.Iic (Module.finrank ℝ E), (Fintype.card ι).choose k := by
  have hv := vcDim_le f A hA
  exact (Finset.card_le_card_shatterer A).trans
    (Finset.card_shatterer_le_sum_vcDim.trans
      (Finset.sum_le_sum_of_subset (Finset.Iic_subset_Iic.mpr hv)))


-- @@ L124-124 verbatim
end UniformSparsestCut.HyperplaneCount


-- @@ L126-126 verbatim
namespace UniformSparsestCut.RoundedCharts

-- @@ L127-127 verbatim
open MeasureTheory Set Filter

-- @@ L128-128 verbatim
open scoped Topology BigOperators RealInnerProductSpace

-- @@ L129-129 verbatim
variable {m N S : ℕ}

-- @@ L130-130 verbatim
local notation "E" => EuclideanSpace ℝ (Fin m)

-- @@ L131-131 verbatim
local notation "F" => EuclideanSpace ℝ (Fin N)


-- @@ L133-133 verbatim
def cube (R : ℝ) : Set E := {θ | ∀ j, |θ j| < R}


-- @@ L135-136 verbatim
def regular (u : Fin N → E) (τ : ℝ) (θ : E) : Prop :=
  ∀ i (k : ℤ), inner ℝ (u i) θ ≠ (k:ℝ)*τ


-- @@ L138-139 verbatim
def integerLabel (u : Fin N → E) (τ : ℝ) (θ : E) (i : Fin N) : ℤ :=
  ⌊inner ℝ (u i) θ/τ⌋


-- @@ L141-142 verbatim
def rounded (u : Fin N → E) (τ : ℝ) (θ : E) : F :=
  WithLp.toLp 2 (fun i => τ*(integerLabel u τ θ i : ℝ))


-- @@ L144-145 verbatim
def Vertex (u : Fin S → Fin N → E) (τ : ℝ) :=
  {p : Fin S × (Fin N → ℤ) // ∃ θ ∈ cube 2, regular (u p.1) τ θ ∧ integerLabel (u p.1) τ θ = p.2}


-- @@ L147-148 verbatim
def coordinate (u : Fin S → Fin N → E) (τ : ℝ) (v : Vertex u τ) : F :=
  WithLp.toLp 2 (fun i => τ*(v.val.2 i : ℝ))


-- @@ L150-163 verbatim
lemma cube_norm {R : ℝ} (hR : 0 ≤ R) {θ : E} (hθ : θ ∈ cube R) :
    ‖θ‖ ≤ R*Real.sqrt m := by
  have hs : ‖θ‖^2 ≤ (m:ℝ)*R^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _j : Fin m, R^2 := by
        apply Finset.sum_le_sum; intro j _
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hθ j).le _
      _ = _ := by simp
  have hroot := Real.sq_sqrt (Nat.cast_nonneg m)
  have hp : 0 ≤ R*Real.sqrt m := mul_nonneg hR (Real.sqrt_nonneg _)
  have he : (R*Real.sqrt m)^2 = (m:ℝ)*R^2 := by rw [mul_pow,hroot]; ring
  nlinarith [norm_nonneg θ]


-- @@ L165-186 verbatim
lemma hyperplane_null (u : E) (hu : u ≠ 0) (t : ℝ) :
    volume {x : E | inner ℝ u x = t} = 0 := by
  let H : AffineSubspace ℝ E :=
    { carrier := {x | inner ℝ u x = t}
      smul_vsub_vadd_mem' := by
        intro c x y z hx hy hz
        change inner ℝ u x = t at hx
        change inner ℝ u y = t at hy
        change inner ℝ u z = t at hz
        change inner ℝ u (c • (x-y)+z) = t
        simp only [inner_add_right, inner_smul_right, inner_sub_right, hx, hy, hz]
        ring }
  have ht : H ≠ ⊤ := by
    intro he
    have hzero : (0:E) ∈ H := by rw [he]; trivial
    have hone : u ∈ H := by rw [he]; trivial
    change inner ℝ u 0 = t at hzero
    change inner ℝ u u = t at hone
    rw [inner_zero_right] at hzero
    have := ((inner_self_eq_zero (𝕜 := ℝ)).mp (hone.trans hzero.symm))
    exact hu this
  exact Measure.addHaar_affineSubspace volume H ht


-- @@ L188-195 verbatim
lemma ae_regular (u : Fin N → E) (τ : ℝ) (hu : ∀ i, u i ≠ 0) :
    ∀ᵐ θ : E, regular u τ θ := by
  have hi (i : Fin N) (k : ℤ) : ∀ᵐ θ : E, inner ℝ (u i) θ ≠ (k:ℝ)*τ := by
    rw [ae_iff]
    simpa only [not_not] using hyperplane_null (u i) (hu i) ((k:ℝ)*τ)
  have hi' (i : Fin N) : ∀ᵐ θ : E, ∀ k : ℤ, inner ℝ (u i) θ ≠ (k:ℝ)*τ :=
    ae_all_iff.mpr (hi i)
  exact ae_all_iff.mpr hi'


-- @@ L197-205 verbatim
lemma rounded_error_coordinate (u : Fin N → E) {τ : ℝ} (hτ : 0 < τ) (θ : E) (i : Fin N) :
    0 ≤ inner ℝ (u i) θ-rounded u τ θ i ∧ inner ℝ (u i) θ-rounded u τ θ i < τ := by
  have hlo := Int.floor_le (inner ℝ (u i) θ/τ)
  have hhi := Int.lt_floor_add_one (inner ℝ (u i) θ/τ)
  have hl := (le_div_iff₀ hτ).mp hlo
  have hh := (div_lt_iff₀ hτ).mp hhi
  change 0 ≤ inner ℝ (u i) θ-τ*(⌊inner ℝ (u i) θ/τ⌋:ℝ) ∧
    inner ℝ (u i) θ-τ*(⌊inner ℝ (u i) θ/τ⌋:ℝ) < τ
  constructor <;> nlinarith


-- @@ L207-221 verbatim
lemma rounded_error (u : Fin N → E) {τ : ℝ} (hτ : 0 < τ) (θ : E) :
    ‖rounded u τ θ - FrameCharts.chart u θ‖ ≤ Real.sqrt N*τ := by
  have hs : ‖rounded u τ θ - FrameCharts.chart u θ‖^2 ≤ (N:ℝ)*τ^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin N, τ^2 := by
        apply Finset.sum_le_sum; intro i _
        simp only [PiLp.sub_apply, FrameCharts.chart_apply, Real.norm_eq_abs, sq_abs]
        have hh := rounded_error_coordinate u hτ θ i
        nlinarith
      _ = _ := by simp
  have hr := Real.sq_sqrt (Nat.cast_nonneg N)
  have hp : 0 ≤ Real.sqrt N*τ := mul_nonneg (Real.sqrt_nonneg _) hτ.le
  have he : (Real.sqrt N*τ)^2 = (N:ℝ)*τ^2 := by rw [mul_pow,hr]
  nlinarith [norm_nonneg (rounded u τ θ-FrameCharts.chart u θ)]


-- @@ L223-239 verbatim
lemma integerLabel_bound (u : Fin N → E) {τ : ℝ} (hτ : 0 < τ) (hu : ∀ i, ‖u i‖ ≤ 2)
    {θ : E} (hθ : θ ∈ cube 2) (i : Fin N) :
    |(integerLabel u τ θ i : ℝ)| ≤ 4*Real.sqrt m/τ+1 := by
  have hn := cube_norm (by norm_num : (0:ℝ) ≤ 2) hθ
  have hh : |inner ℝ (u i) θ| ≤ 4*Real.sqrt m := by
    calc
      _ ≤ ‖u i‖*‖θ‖ := abs_real_inner_le_norm _ _
      _ ≤ 2*(2*Real.sqrt m) := mul_le_mul (hu i) hn (norm_nonneg θ) (by norm_num)
      _ = _ := by ring
  have hf := Int.floor_le (inner ℝ (u i) θ/τ)
  have hfl := Int.lt_floor_add_one (inner ℝ (u i) θ/τ)
  have hab : |inner ℝ (u i) θ/τ| ≤ 4*Real.sqrt m/τ := by
    rw [abs_div, abs_of_pos hτ]
    exact div_le_div_of_nonneg_right hh hτ.le
  change |(⌊inner ℝ (u i) θ/τ⌋:ℝ)| ≤ _
  rw [abs_le] at hab ⊢
  constructor <;> linarith


-- @@ L241-259 verbatim
lemma vertex_finite (u : Fin S → Fin N → E) {τ : ℝ} (hτ : 0 < τ)
    (hu : ∀ s i, ‖u s i‖ ≤ 2) : Finite (Vertex u τ) := by
  let B : ℤ := ⌈4*Real.sqrt m/τ+1⌉
  let f : Vertex u τ → Fin S × (Fin N → ↥(Finset.Icc (-B) B)) := fun v =>
    (v.val.1, fun i => ⟨v.val.2 i, by
      obtain ⟨θ,hθ,hr,hlabel⟩ := v.property
      have hb := integerLabel_bound (u v.val.1) hτ (hu v.val.1) hθ i
      have hB := Int.le_ceil (4*Real.sqrt m/τ+1)
      have hv : |(v.val.2 i:ℝ)| ≤ (B:ℝ) := by rw [← hlabel]; exact hb.trans hB
      have hlo : -B ≤ v.val.2 i := by exact_mod_cast (abs_le.mp hv).1
      have hhi : v.val.2 i ≤ B := by exact_mod_cast (abs_le.mp hv).2
      exact Finset.mem_Icc.mpr ⟨hlo,hhi⟩⟩)
  apply Finite.of_injective f
  intro v w h
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun z : Fin S × (Fin N → ↥(Finset.Icc (-B) B)) => z.1) h
  · funext i
    exact congrArg (fun z : Fin S × (Fin N → ↥(Finset.Icc (-B) B)) => (z.2 i).val) h


-- @@ L261-267 verbatim
lemma representative (u : Fin S → Fin N → E) (τ : ℝ) (v : Vertex u τ) :
    ∃ θ ∈ cube 2, regular (u v.val.1) τ θ ∧ coordinate u τ v = rounded (u v.val.1) τ θ := by
  obtain ⟨θ,hθ,hr,hl⟩ := v.property
  refine ⟨θ,hθ,hr,?_⟩
  ext i
  change τ*(v.val.2 i : ℝ) = τ*(integerLabel (u v.val.1) τ θ i : ℝ)
  rw [hl]


-- @@ L269-269 verbatim
end UniformSparsestCut.RoundedCharts


-- @@ L271-271 verbatim
namespace UniformSparsestCut.SourceCharts

-- @@ L272-272 verbatim
open scoped BigOperators RealInnerProductSpace

-- @@ L273-273 verbatim
noncomputable section

-- @@ L274-274 verbatim
variable {m : ℕ} (f : PivotFamily.PFamily m) (hm : 0 < m)

-- @@ L275-275 verbatim
local notation "E" => EuclideanSpace ℝ (Fin m)

-- @@ L276-276 verbatim
local notation "F" => EuclideanSpace ℝ (Fin (m^6))

-- @@ L277-282 verbatim
lemma lower_ge_one (hm2 : 2 ≤ m) : 1≤lower m := by
  have hx : (2:ℝ) ≤ m := by exact_mod_cast hm2
  have hp := pow_le_pow_right₀ (by linarith : (1:ℝ) ≤ m) (show 2≤6 by norm_num)
  unfold lower
  apply (le_div_iff₀ (by positivity : (0:ℝ)<2*m)).mpr
  nlinarith

-- @@ L283-284 verbatim
lemma B_norm_le (hm2 : 2 ≤ m) (s : Fin (m^3)) (x : F) : ‖B f hm s x‖≤‖x‖ := by
  exact (B_norm f hm s x).trans (div_le_self (norm_nonneg _) ((Real.one_le_sqrt).mpr (lower_ge_one hm2)))

-- @@ L285-291 verbatim
lemma rounded_B_error (hm2 : 2 ≤ m) {τ : ℝ} (hτ : 0<τ) (s : Fin (m^3)) (θ : E) :
    ‖B f hm s (RoundedCharts.rounded (u f s) τ θ)-θ‖≤Real.sqrt (m^6:ℕ)*τ := by
  have he : B f hm s (RoundedCharts.rounded (u f s) τ θ)-θ=
      B f hm s (RoundedCharts.rounded (u f s) τ θ-FrameCharts.chart (u f s) θ) := by
    rw [map_sub,B_left]
  rw [he]
  exact (B_norm_le f hm hm2 s _).trans (RoundedCharts.rounded_error _ hτ θ)

-- @@ L292-302 verbatim
lemma rounded_residual_error {τ : ℝ} (hτ : 0<τ) (s : Fin (m^3)) (θ : E) :
    ‖RoundedCharts.rounded (u f s) τ θ-FrameCharts.chart (u f s) (B f hm s (RoundedCharts.rounded (u f s) τ θ))‖≤
      Real.sqrt (m^6:ℕ)*τ := by
  let x := RoundedCharts.rounded (u f s) τ θ
  have he : x-FrameCharts.chart (u f s) (B f hm s x)=
      (x-FrameCharts.chart (u f s) θ)-FrameCharts.chart (u f s) (B f hm s (x-FrameCharts.chart (u f s) θ)) := by
    rw [map_sub,B_left,map_sub]
    abel
  change ‖x-FrameCharts.chart (u f s) (B f hm s x)‖≤_
  rw [he]
  exact (residual_norm f hm s _).trans (RoundedCharts.rounded_error _ hτ θ)

-- @@ L303-309 verbatim
lemma vertex_B_bound (hm2 : 2 ≤ m) {τ : ℝ} (hτ : 0<τ) (v : RoundedCharts.Vertex (u f) τ) :
    ‖B f hm v.val.1 (RoundedCharts.coordinate (u f) τ v)‖≤2*Real.sqrt m+Real.sqrt (m^6:ℕ)*τ := by
  obtain ⟨θ,hθ,hr,hx⟩ := RoundedCharts.representative (u f) τ v
  rw [hx]
  have h := rounded_B_error f hm hm2 hτ v.val.1 θ
  have ht := RoundedCharts.cube_norm (by norm_num : (0:ℝ)≤2) hθ
  exact (norm_le_norm_sub_add _ θ).trans (by linarith)

-- @@ L310-315 verbatim
lemma vertex_residual_bound {τ : ℝ} (hτ : 0<τ) (v : RoundedCharts.Vertex (u f) τ) :
    ‖RoundedCharts.coordinate (u f) τ v-FrameCharts.chart (u f v.val.1) (B f hm v.val.1 (RoundedCharts.coordinate (u f) τ v))‖≤
      Real.sqrt (m^6:ℕ)*τ := by
  obtain ⟨θ,hθ,hr,hx⟩ := RoundedCharts.representative (u f) τ v
  rw [hx]
  exact rounded_residual_error f hm hτ v.val.1 θ

-- @@ L316-316 verbatim
end

-- @@ L317-317 verbatim
end UniformSparsestCut.SourceCharts


-- @@ L319-319 verbatim
end


-- @@ L321-321 verbatim
end OAI
