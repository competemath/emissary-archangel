import OAI.Analysis.DirectCrouzeix.ExteriorMapping


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped Matrix Matrix.Norms.L2Operator Kronecker


-- @@ L9-9 verbatim
noncomputable section


-- @@ L11-11 verbatim
open MeasureTheory Set Filter Metric


-- @@ L13-13 verbatim
open scoped Topology Interval ENNReal NNReal ComplexConjugate


-- @@ L15-15 verbatim
noncomputable section


-- @@ L17-17 verbatim
open Filter Metric Set


-- @@ L19-19 verbatim
open scoped Topology ComplexConjugate


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
open Set Filter Metric


-- @@ L25-25 verbatim
open scoped Topology ComplexConjugate


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
open Set Filter Metric


-- @@ L31-31 verbatim
open scoped Topology ComplexConjugate


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-35 verbatim
open Set Filter Metric


-- @@ L37-37 verbatim
open scoped Topology ComplexConjugate


-- @@ L39-39 verbatim
noncomputable section


-- @@ L41-41 verbatim
open Set Filter Metric


-- @@ L43-43 verbatim
open scoped Topology ComplexConjugate


-- @@ L45-45 verbatim
noncomputable section


-- @@ L47-47 verbatim
open Set Filter Metric


-- @@ L49-49 verbatim
open scoped Topology ComplexConjugate


-- @@ L51-51 verbatim
namespace DirectCrouzeix.Geometry


-- @@ L53-77 verbatim
theorem exists_axis_net {δ : ℝ} (hδ : 0 < δ) :
    ∃ D : Finset ℂ, (∀ ν ∈ D, ‖ν‖ = 1) ∧ 1 ∈ D ∧ -1 ∈ D ∧
      Complex.I ∈ D ∧ -Complex.I ∈ D ∧
      (∀ ν : ℂ, ‖ν‖ = 1 → ∃ μ ∈ D, ‖ν-μ‖ < δ) := by
  classical
  obtain ⟨S,hS⟩ := (isCompact_sphere (0:ℂ) 1).elim_finite_subcover
    (fun ν : sphere (0:ℂ) 1 => ball (ν:ℂ) δ) (fun _ => isOpen_ball) (by
      intro ν hν
      exact mem_iUnion.mpr ⟨⟨ν,hν⟩,mem_ball_self hδ⟩)
  let D := S.image Subtype.val ∪ {1,-1,Complex.I,-Complex.I}
  refine ⟨D,?_,?_,?_,?_,?_,?_⟩
  · intro ν hν
    rcases Finset.mem_union.mp hν with hν | hν
    · obtain ⟨μ,hμ,rfl⟩ := Finset.mem_image.mp hν
      simpa only [mem_sphere,dist_zero_right] using μ.property
    · simp only [Finset.mem_insert,Finset.mem_singleton] at hν
      rcases hν with rfl | rfl | rfl | rfl <;> simp
  · simp [D]
  · simp [D]
  · simp [D]
  · simp [D]
  · intro ν hν
    obtain ⟨μ,hμ,hνμ⟩ := mem_iUnion₂.mp (hS (by simpa only [mem_sphere,dist_zero_right] using hν))
    refine ⟨μ,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨μ,hμ,rfl⟩),?_⟩
    simpa [dist_eq_norm] using hνμ


-- @@ L79-79 verbatim
def convexSupport (K : Set ℂ) (ν : ℂ) : ℝ := sSup ((fun z => inner ℝ ν z) '' K)


-- @@ L81-83 verbatim
theorem convexSupport_attained {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty) (ν : ℂ) :
    ∃ w ∈ K, inner ℝ ν w = convexSupport K ν := by
  exact (hK.image ((innerSL ℝ ν).continuous)).sSup_mem (hne.image _)


-- @@ L85-88 verbatim
theorem le_convexSupport {K : Set ℂ} (hK : IsCompact K) {z : ℂ} (hz : z ∈ K) (ν : ℂ) :
    inner ℝ ν z ≤ convexSupport K ν := by
  apply le_csSup (hK.image ((innerSL ℝ ν).continuous)).bddAbove
  exact mem_image_of_mem _ hz


-- @@ L90-94 verbatim
theorem convexSupport_le {K : Set ℂ} (hne : K.Nonempty) {M : ℝ}
    (hM : ∀ z ∈ K, ‖z‖ ≤ M) {ν : ℂ} (hν : ‖ν‖ = 1) : convexSupport K ν ≤ M := by
  apply csSup_le (hne.image _)
  rintro x ⟨z,hz,rfl⟩
  exact (real_inner_le_norm ν z).trans (by simpa only [hν,one_mul] using hM z hz)


-- @@ L96-139 verbatim
theorem direction_net_distance {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (hconv : Convex ℝ K) {D : Finset ℂ} {δ M L : ℝ} (hδ : 0 < δ)
    (hM : ∀ w ∈ K, ‖w‖ ≤ M)
    (hnet : ∀ ν : ℂ, ‖ν‖ = 1 → ∃ μ ∈ D, ‖ν-μ‖ < δ)
    {z : ℂ} (hz : ‖z‖ ≤ L)
    (hs : ∀ μ ∈ D, inner ℝ μ z ≤ convexSupport K μ+δ) :
    ∃ w ∈ K, ‖z-w‖ ≤ δ*(1+L+M) := by
  obtain ⟨w,hw,hwmin⟩ := exists_norm_eq_iInf_of_complete_convex hne hK.isClosed.isComplete hconv z
  have hM0 : 0 ≤ M := (norm_nonneg w).trans (hM w hw)
  have hL0 : 0 ≤ L := (norm_nonneg z).trans hz
  refine ⟨w,hw,?_⟩
  by_cases he : z = w
  · rw [he,sub_self,norm_zero]
    positivity
  have hn : 0 < ‖z-w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr he)
  let ν := (‖z-w‖⁻¹:ℝ) • (z-w)
  have hν : ‖ν‖ = 1 := by simp [ν,ne_of_gt hn]
  obtain ⟨μ,hμ,hνμ⟩ := hnet ν hν
  obtain ⟨u,hu,hsu⟩ := convexSupport_attained hK hne μ
  have hmin : inner ℝ ν (u-w) ≤ 0 := by
    have hh := (norm_eq_iInf_iff_real_inner_le_zero hconv hw).mp hwmin u hu
    dsimp only [ν]
    rw [real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (inv_pos.mpr hn)) hh
  have hzw : inner ℝ ν (z-w) = ‖z-w‖ := by
    dsimp only [ν]
    rw [real_inner_smul_left,real_inner_self_eq_norm_sq]
    field_simp
  have hmain : ‖z-w‖ ≤ inner ℝ ν (z-u) := by
    have heq : z-w = (z-u)+(u-w) := by abel
    rw [← hzw,heq,inner_add_right]
    linarith
  have hμbound : inner ℝ μ (z-u) ≤ δ := by
    rw [inner_sub_right,hsu]
    linarith [hs μ hμ]
  have hnorm : ‖z-u‖ ≤ L+M := (norm_sub_le z u).trans (add_le_add hz (hM u hu))
  have herror : inner ℝ (ν-μ) (z-u) ≤ δ*(L+M) := by
    calc
      inner ℝ (ν-μ) (z-u) ≤ ‖ν-μ‖*‖z-u‖ := real_inner_le_norm _ _
      _ ≤ δ*(L+M) := mul_le_mul (le_of_lt hνμ) hnorm (norm_nonneg _) (le_of_lt hδ)
  have heq : inner ℝ ν (z-u) = inner ℝ μ (z-u)+inner ℝ (ν-μ) (z-u) := by
    rw [inner_sub_left]; ring
  rw [heq] at hmain
  nlinarith


-- @@ L141-158 verbatim
theorem axis_support_bound {K : Set ℂ} (hne : K.Nonempty) {M δ : ℝ}
    (hM : ∀ w ∈ K, ‖w‖ ≤ M) {D : Finset ℂ}
    (h1 : 1 ∈ D) (hm1 : -1 ∈ D) (hI : Complex.I ∈ D) (hmI : -Complex.I ∈ D)
    {z : ℂ} (hs : ∀ μ ∈ D, inner ℝ μ z ≤ convexSupport K μ+δ) :
    ‖z‖ ≤ 2*(M+δ) := by
  have hb (μ : ℂ) (hμ : μ ∈ D) (hμN : ‖μ‖ = 1) : inner ℝ μ z ≤ M+δ :=
    (hs μ hμ).trans (add_le_add_left (convexSupport_le hne hM hμN) δ)
  have hr := hb 1 h1 (by simp)
  have hrr := hb (-1) hm1 (by simp)
  have hi := hb Complex.I hI (by simp)
  have hir := hb (-Complex.I) hmI (by simp)
  simp only [real_inner_eq_re_inner ℂ,RCLike.inner_apply] at hr hrr hi hir
  simp at hr hrr hi hir
  have ha : |z.re| ≤ M+δ := abs_le.mpr ⟨by linarith,hr⟩
  have hb : |z.im| ≤ M+δ := abs_le.mpr ⟨by linarith,hi⟩
  calc
    ‖z‖ ≤ |z.re|+|z.im| := Complex.norm_le_abs_re_add_abs_im z
    _ ≤ 2*(M+δ) := by linarith


-- @@ L160-160 verbatim
end DirectCrouzeix.Geometry


-- @@ L162-162 verbatim
noncomputable section


-- @@ L164-164 verbatim
open Set


-- @@ L166-166 verbatim
open scoped ComplexConjugate Matrix


-- @@ L168-168 verbatim
namespace DirectCrouzeix.Geometry


-- @@ L170-170 verbatim
end DirectCrouzeix.Geometry


-- @@ L172-172 verbatim
end


-- @@ L174-174 verbatim
end


-- @@ L176-176 verbatim
end


-- @@ L178-178 verbatim
end


-- @@ L180-180 verbatim
end


-- @@ L182-182 verbatim
end


-- @@ L184-184 verbatim
end


-- @@ L186-186 verbatim
end


-- @@ L188-188 verbatim
end


-- @@ L190-190 verbatim
end OAI
