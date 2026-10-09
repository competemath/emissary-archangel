import OAI.Combinatorics.SparsestCut.Mollifier


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal

-- @@ L6-6 verbatim
open MeasureTheory ProbabilityTheory Set Filter Matrix


-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
namespace UniformSparsestCut.KernelGeometry

-- @@ L11-11 verbatim
open MeasureTheory Set ProductMollifier

-- @@ L12-12 verbatim
open scoped BigOperators Topology

-- @@ L13-13 verbatim
noncomputable section

-- @@ L14-14 verbatim
variable {m : ℕ}

-- @@ L15-15 verbatim
local notation "E" => EuclideanSpace ℝ (Fin m)

-- @@ L16-16 verbatim
def κ (lam : ℝ) : E → ℝ := kernel (density lam)

-- @@ L17-17 verbatim
def L (lam : ℝ) : ℝ := lam⁻¹*(∫ t, |deriv rho t|)

-- @@ L18-19 verbatim
lemma smooth (lam : ℝ) : ContDiff ℝ (⊤:ℕ∞) (κ (m := m) lam) :=
  kernel_smooth _ (density_smooth _)

-- @@ L20-21 verbatim
lemma compact {lam : ℝ} (hlam : 0<lam) : HasCompactSupport (κ (m := m) lam) :=
  kernel_compact hlam.le (fun _ hx => (density_support hlam hx).le)

-- @@ L22-23 verbatim
lemma nonneg {lam : ℝ} (hlam : 0≤lam) (z : E) : 0≤κ lam z :=
  kernel_nonneg (density_nonneg hlam) z

-- @@ L24-25 verbatim
lemma integral_one {lam : ℝ} (hlam : 0<lam) : (∫ z : E, κ lam z)=1 := by
  rw [κ,kernel_integral,density_integral hlam,one_pow]

-- @@ L26-27 verbatim
lemma integrable {lam : ℝ} (hlam : 0<lam) : Integrable (κ (m := m) lam) :=
  (smooth lam).continuous.integrable_of_hasCompactSupport (compact hlam)

-- @@ L28-29 verbatim
lemma L_nonneg {lam : ℝ} (hlam : 0≤lam) : 0≤L lam := by
  exact mul_nonneg (inv_nonneg.mpr hlam) (integral_nonneg (fun _ => abs_nonneg _))

-- @@ L30-33 verbatim
lemma support_coord {lam : ℝ} (hlam : 0<lam) {z : E} (hz : κ lam z≠0) (j : Fin m) : |z j|<lam := by
  apply density_support hlam
  intro hj
  exact hz (Finset.prod_eq_zero (Finset.mem_univ j) hj)

-- @@ L34-36 verbatim
lemma tsupport_coord {lam : ℝ} (hlam : 0<lam) {z : E} (hz : z∈tsupport (κ lam)) (j : Fin m) : |z j|≤lam := by
  have hc : IsClosed {w : E | |w j|≤lam} := isClosed_le (by fun_prop) continuous_const
  exact (closure_minimal (fun _ h => (support_coord hlam h j).le) hc) hz

-- @@ L37-42 verbatim
lemma shifted_mem {lam : ℝ} (hlam : 0<lam) (hlam1 : lam<1) (x : E) (hx : ∀ j, |x j|≤1)
    {z : E} (hz : z∈tsupport (κ lam)) : ∀ j, |(x-z) j|<2 := by
  intro j
  have h := tsupport_coord hlam hz j
  change |x j-z j|<2
  exact (abs_sub (x j) (z j)).trans_lt (by linarith [hx j])

-- @@ L43-48 verbatim
lemma derivative_shifted_mem {lam : ℝ} (hlam : 0<lam) (hlam1 : lam<1) (x : E) (hx : ∀ j, |x j|≤1)
    {z h : E} (hz : fderiv ℝ (κ lam) z h≠0) : ∀ j, |(x-z) j|<2 := by
  apply shifted_mem hlam hlam1 x hx
  apply support_fderiv_subset ℝ
  intro he
  exact hz (by rw [he]; rfl)

-- @@ L49-50 verbatim
lemma norm_bound {lam : ℝ} (hlam : 0<lam) {z : E} (hz : κ lam z≠0) : ‖z‖≤lam*Real.sqrt m :=
  coordinate_norm_bound hlam.le z (fun j => (support_coord hlam hz j).le)

-- @@ L51-55 verbatim
lemma partial_integrable {lam : ℝ} (hlam : 0<lam) (j : Fin m) :
    Integrable (fun z : E => |fderiv ℝ (κ lam) z (EuclideanSpace.single j 1)|) := by
  have hc := (smooth (m := m) lam).continuous_fderiv (by simp)
  exact ((hc.clm_apply continuous_const).integrable_of_hasCompactSupport
    ((compact (m := m) hlam).fderiv_apply ℝ (EuclideanSpace.single j 1))).abs

-- @@ L56-61 verbatim
lemma partial_integral {lam : ℝ} (hlam : 0<lam) (j : Fin m) :
    (∫ z : E, |fderiv ℝ (κ lam) z (EuclideanSpace.single j 1)|)=L lam := by
  change (∫ z : E, |fderiv ℝ (kernel (density lam)) z (EuclideanSpace.single j 1)|)=_
  rw [kernel_partial_integral (fun t => ((density_smooth lam).differentiable (by simp) t).hasDerivAt)
    (density_nonneg hlam.le) (density_integral hlam),density_deriv_integral hlam]
  rfl

-- @@ L62-62 verbatim
end

-- @@ L63-63 verbatim
end UniformSparsestCut.KernelGeometry


-- @@ L65-65 verbatim
namespace UniformSparsestCut.SourceContraction

-- @@ L66-66 verbatim
open scoped BigOperators RealInnerProductSpace

-- @@ L67-67 verbatim
open SourceParameters SourceCharts SourceMetric

-- @@ L68-68 verbatim
open MeasureTheory

-- @@ L69-69 verbatim
noncomputable section

-- @@ L70-70 verbatim
def H : ℝ := ∫ t, |deriv ProductMollifier.rho t|

-- @@ L71-71 verbatim
lemma H_nonneg : 0≤H := integral_nonneg (fun _ => abs_nonneg _)

-- @@ L72-72 verbatim
def weight (m : ℕ) : ℝ := Real.sqrt m*(Real.log m)^2*Real.sqrt (Real.log m)

-- @@ L73-73 verbatim
def C : ℝ := 2*(KernelApprox.cstar+C₀)+Real.pi*(1100000000+C₀*H)+1

-- @@ L74-79 verbatim
lemma C_pos : 0<C := by
  have hc := KernelApprox.cstar_pos
  have hr := C₀_pos
  have hh := H_nonneg
  unfold C
  positivity

-- @@ L80-84 verbatim
lemma weight_ge_one {m : ℕ} (hm : 1 ≤ m) (hl : 1≤Real.log m) : 1≤weight m := by
  have hq : 1≤Real.sqrt m := Real.one_le_sqrt.mpr (by exact_mod_cast hm)
  have hll : 1≤(Real.log m)^2 := one_le_pow₀ hl
  have hs : 1≤Real.sqrt (Real.log m) := Real.one_le_sqrt.mpr hl
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hq hll) hs

-- @@ L85-86 verbatim
lemma scale_L {m : ℕ} (_hm : 0 < m) : KernelGeometry.L (p m 2)=(m:ℝ)^2*H := by
  simp [KernelGeometry.L,p,H]

-- @@ L87-110 verbatim
lemma small {m : ℕ} (f : PivotFamily.PFamily m) (hm : 1 ≤ m) (hH : H ≤ m)
    (s : Fin (m^3)) (i : Fin (m^6)) (j : Fin m) :
    p m 2000/|u f s i j| *KernelGeometry.L (p m 2)≤1 := by
  have hm0 : 0 < m := by omega
  have hx0 : (0:ℝ)< m := by exact_mod_cast hm0
  have hx : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hq := u_pivot f hm0 s i j
  have ha : 0 < |u f s i j| := lt_trans (by positivity) hq
  have hp : p m 31≤|u f s i j| := by
    apply le_trans _ hq.le
    apply one_div_le_one_div_of_le (by positivity)
    calc
      (m:ℝ)^30*Real.sqrt m≤(m:ℝ)^30*m := mul_le_mul_of_nonneg_left (sqrt_le hx) (by positivity)
      _ = (m:ℝ)^31 := by ring
  have hb : p m 2000*KernelGeometry.L (p m 2)≤|u f s i j| := by
    rw [scale_L hm0]
    calc
      _ ≤ p m 2000*((m:ℝ)^2*m) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hH (by positivity)) (p_nonneg hx0.le _)
      _ = p m 1997 := by unfold p; field_simp
      _ ≤ p m 31 := p_le hx (by norm_num)
      _ ≤ _ := hp
  rw [div_mul_eq_mul_div,div_le_one ha]
  exact hb

-- @@ L111-156 verbatim
lemma contraction_numeric {m : ℕ} (hm : 1 ≤ m) (hl : 1≤Real.log m) :
    2*(KernelApprox.cstar*Real.sqrt m*(p m 2*Real.sqrt m)+C₀*p m 8)+
      Real.pi*((11*Real.sqrt (Real.log m)/Real.sqrt m)*
        (((m^6:ℕ):ℝ)*(2*(50000000*p m 2000*p m 5*(Real.log m)^2)/p m 2000))+
        (m:ℝ)*(C₀*p m 8)*KernelGeometry.L (p m 2))≤C*weight m := by
  have hx : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hx0 : (0:ℝ)< m := by linarith
  have hm0 : 0 < m := by omega
  have hq0 := ne_of_gt (Real.sqrt_pos.mpr hx0)
  have hq2 := Real.sq_sqrt hx0.le
  have hR := C₀_pos.le
  have hcs := KernelApprox.cstar_pos.le
  have hH := H_nonneg
  have hw := weight_ge_one hm hl
  have he : (11*Real.sqrt (Real.log m)/Real.sqrt m)*
      (((m^6:ℕ):ℝ)*(2*(50000000*p m 2000*p m 5*(Real.log m)^2)/p m 2000))=
      1100000000*weight m := by
    have hdiv : (m:ℝ)/Real.sqrt m=Real.sqrt m := (div_eq_iff hq0).mpr (by nlinarith)
    calc
      _ = 1100000000*((m:ℝ)/Real.sqrt m)*(Real.log m)^2*Real.sqrt (Real.log m) := by
        unfold p; push_cast; field_simp ; ring
      _ = _ := by rw [hdiv]; unfold weight; ring
  have hG : KernelApprox.cstar*Real.sqrt m*(p m 2*Real.sqrt m)≤KernelApprox.cstar := by
    have he : Real.sqrt m*(p m 2*Real.sqrt m)=p m 1 := by
      calc
        _ = (Real.sqrt m)^2*p m 2 := by ring
        _ = (m:ℝ)*p m 2 := by rw [Real.sq_sqrt hx0.le]
        _ = p m 1 := p_succ hx0.ne' 1
    calc
      _ = KernelApprox.cstar*(Real.sqrt m*(p m 2*Real.sqrt m)) := by ring
      _ = KernelApprox.cstar*p m 1 := by rw [he]
      _ ≤ _ := mul_le_of_le_one_right hcs (p_one_le hx _)
  have heR : (m:ℝ)*(C₀*p m 8)*KernelGeometry.L (p m 2)=C₀*H*p m 5 := by
    rw [scale_L hm0]; unfold p; field_simp
  rw [he,heR]
  have h1 := mul_le_of_le_one_right hR (p_one_le hx 8)
  have h2 := mul_le_of_le_one_right (mul_nonneg hR hH) (p_one_le hx 5)
  have h3 := mul_le_mul_of_nonneg_left hw (mul_nonneg hR hH)
  have h4 := mul_le_mul_of_nonneg_left hw (by positivity : 0≤2*(KernelApprox.cstar+C₀))
  calc
    _ ≤ 2*(KernelApprox.cstar+C₀)+Real.pi*(1100000000*weight m+C₀*H) := add_le_add (mul_le_mul_of_nonneg_left (add_le_add hG h1) (by norm_num))
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl h2) Real.pi_pos.le)
    _ ≤ 2*(KernelApprox.cstar+C₀)*weight m+
        Real.pi*(1100000000*weight m+C₀*H*weight m) := add_le_add (by simpa using h4)
          (mul_le_mul_of_nonneg_left (add_le_add le_rfl (by simpa using h3)) Real.pi_pos.le)
    _ ≤ _ := by unfold C; nlinarith

-- @@ L157-157 verbatim
end

-- @@ L158-158 verbatim
end UniformSparsestCut.SourceContraction


-- @@ L160-160 verbatim
namespace UniformSparsestCut.SourceCharts

-- @@ L161-161 verbatim
open scoped BigOperators RealInnerProductSpace

-- @@ L162-162 verbatim
open Set

-- @@ L163-163 verbatim
noncomputable section

-- @@ L164-164 verbatim
variable {m : ℕ} (f : PivotFamily.PFamily m) (hm : 0 < m)

-- @@ L165-165 verbatim
local notation "E" => EuclideanSpace ℝ (Fin m)

-- @@ L166-166 verbatim
include hm

-- @@ L167-206 verbatim
lemma good_dual (D : StrongDual ℝ E) :
    ∃ good : Finset (Fin (m^3)), ((m^3:ℕ):ℝ)/2≤good.card ∧
      ∀ s∈good, ∀ i, |D (u f s i)|≤(11*Real.sqrt (Real.log m)/Real.sqrt m)*‖D‖ := by
  classical
  by_cases hz : D=0
  · refine ⟨Finset.univ,?_,?_⟩
    · simp only [Finset.card_univ,Fintype.card_fin]; linarith [show (0:ℝ)≤((m^3:ℕ):ℝ) by positivity]
    · intro s hs i; simp [hz]
  let w : E := (InnerProductSpace.toDual ℝ E).symm D
  have hwn : ‖w‖=‖D‖ := (InnerProductSpace.toDual ℝ E).symm.norm_map D
  have hw0 : 0<‖w‖ := by rw [hwn]; exact norm_pos_iff.mpr hz
  let v : E := ‖w‖⁻¹ • w
  have hv : ‖v‖=1 := by simp [v,norm_smul,hw0.ne']
  have hw : w=‖w‖ • v := by simp [v,smul_smul,hw0.ne']
  let Q := 11*Real.sqrt (Real.log m)
  let good : Finset (Fin (m^3)) := Finset.univ.filter (fun s => f.g s∉Directions.projectionBad Q v)
  have hb := f.good v hv
  have hcard : Directions.badCount (Directions.projectionBad Q v) f.g+good.card=m^3 := by
    simpa only [Directions.badCount,good,Finset.card_univ,Fintype.card_fin] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (m^3)))) (fun s => f.g s∈Directions.projectionBad Q v))
  refine ⟨good,?_,?_⟩
  · have hc : ((Directions.badCount (Directions.projectionBad Q v) f.g):ℝ)+(good.card:ℝ)=((m^3:ℕ):ℝ) := by exact_mod_cast hcard
    change ((Directions.badCount (Directions.projectionBad Q v) f.g):ℝ)≤((m^3:ℕ):ℝ)/2 at hb
    linarith
  · intro s hs i
    have hp : |inner ℝ v (f.g s i)|≤Q := by
      by_contra h
      exact (Finset.mem_filter.mp hs).2 ⟨i,lt_of_not_ge h⟩
    have hq : 0<Real.sqrt (m:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hm)
    have he : |D (u f s i)|=‖w‖*(Real.sqrt m)⁻¹*|inner ℝ v (f.g s i)| := by
      rw [← InnerProductSpace.toDual_symm_apply]
      change |inner ℝ w ((Real.sqrt m)⁻¹ • f.g s i)|=_
      conv_lhs => rw [hw]
      rw [real_inner_smul_left,real_inner_smul_right,abs_mul,abs_mul,
        abs_of_nonneg (norm_nonneg _),abs_of_pos (inv_pos.mpr hq)]
      ring
    rw [he]
    calc
      _ ≤ ‖w‖*(Real.sqrt m)⁻¹*Q := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by rw [hwn]; unfold Q; ring

-- @@ L207-207 verbatim
end

-- @@ L208-208 verbatim
end UniformSparsestCut.SourceCharts


-- @@ L210-210 verbatim
end


-- @@ L212-212 verbatim
end OAI
