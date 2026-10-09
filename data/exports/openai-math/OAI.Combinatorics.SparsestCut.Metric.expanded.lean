import OAI.Combinatorics.SparsestCut.Parameters


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal

-- @@ L6-6 verbatim
open MeasureTheory ProbabilityTheory Set Filter Matrix


-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
namespace UniformSparsestCut.SourceMetric

-- @@ L11-11 verbatim
open scoped BigOperators RealInnerProductSpace

-- @@ L12-12 verbatim
open SourceParameters SourceCharts

-- @@ L13-13 verbatim
noncomputable section

-- @@ L14-14 verbatim
variable {m : ℕ} (f : PivotFamily.PFamily m)

-- @@ L15-15 verbatim
local notation "E" => EuclideanSpace ℝ (Fin m)

-- @@ L16-16 verbatim
abbrev V := RoundedCharts.Vertex (u f) (p m 2000)

-- @@ L17-19 verbatim
noncomputable instance vertexFintype [NeZero m] : Fintype (V f) := by
  letI := RoundedCharts.vertex_finite (u f) (τ := p m 2000) (p_pos (by exact_mod_cast NeZero.pos m) _) (fun s i => (u_norm f (NeZero.pos m) s i).2)
  exact Fintype.ofFinite _

-- @@ L20-21 verbatim
def L : ℝ := GramMetric.localCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
  (p m 40) ((m:ℝ)^40) (p m 1997) (2/Real.sqrt m)

-- @@ L22-23 verbatim
def err : ℝ := GramMetric.macroCost (m^6) (m^3) (Real.sqrt m) (p m 5) (p m 200)
  (p m 40) ((m:ℝ)^40) (p m 1997) (3*Real.sqrt m) 0

-- @@ L24-78 verbatim
lemma realization [NeZero m] (hm : 3000 ≤ m) (hl : 1≤Real.log m) :
    ∃ Z : V f → EuclideanSpace ℝ (V f),
      (∀ v w z, ‖Z v-Z z‖^2≤‖Z v-Z w‖^2+‖Z w-Z z‖^2) ∧
      (∀ v w, |‖Z v-Z w‖^2-KernelApprox.cstar*Real.sqrt m*
         ‖B f (NeZero.pos m) v.val.1 (RoundedCharts.coordinate (u f) (p m 2000) v)-
           B f (NeZero.pos m) w.val.1 (RoundedCharts.coordinate (u f) (p m 2000) w)‖|≤err (m:=m)+8*p m 8) ∧
      (∀ v w, v.val.1=w.val.1 → (∑ i, |RoundedCharts.coordinate (u f) (p m 2000) v i-
        RoundedCharts.coordinate (u f) (p m 2000) w i|)=p m 2000 →
        ‖Z v-Z w‖^2≤50000000*p m 2000*p m 5*(Real.log m)^2) := by
  have hm0 := NeZero.pos m
  have hm1 : 1 ≤ m := by omega
  have hm2 : 2 ≤ m := by omega
  have hx : (1:ℝ) ≤ m := by exact_mod_cast hm1
  have hx0 : (0:ℝ) < m := by exact_mod_cast hm0
  have hτ := p_pos hx0 2000
  let c : V f → Fin (m^3) := fun v => v.val.1
  let x := RoundedCharts.coordinate (u f) (p m 2000)
  let θ : V f → E := fun v => B f hm0 (c v) (x v)
  have hhab : p m 40≤(m:ℝ)^40 := (p_one_le hx _).trans (one_le_pow₀ hx)
  have hb (s : Fin (m^3)) (i : Fin (m^6)) : ‖B f hm0 s (EuclideanSpace.single i 1)‖≤4*p m 5 := by
    have h := B_column f hm0 s i
    convert h using 1
    unfold p; field_simp
  have hFourier (s : Fin (m^3)) (w : E) (hw : ‖w‖≤2*(3*Real.sqrt m)/p m 40) :
      ‖Real.exp (-‖w‖^2/2) • w-((m^6:ℕ):ℝ)⁻¹ • ∑ i, Real.sin (inner ℝ (f.g s i) w) • f.g s i‖≤2/Real.sqrt m := by
    rw [norm_sub_rev]
    exact f.fourier s w (hw.trans (fourier_radius (show 6 ≤ m by omega)))
  have hB (v : V f) : ‖B f hm0 (c v) (x v)‖≤3*Real.sqrt m := by
    have h := vertex_B_bound f hm0 hm2 hτ v
    rw [rounded_radius hm0] at h
    exact h.trans (by linarith [radius_le_sqrt hm1])
  have hres (v : V f) :
      ‖ChartKernel.residual (FrameCharts.chart (fun i => (Real.sqrt m)⁻¹ • f.g (c v) i)) (B f hm0 (c v)) (x v)‖≤p m 1997 := by
    have h := vertex_residual_bound f hm0 hτ v
    rw [rounded_radius hm0] at h
    exact h
  have he := (macro_bounds hm1).1
  have her : 3*err (m:=m)/2≤p m 8 := by
    have hsmall := macro_small hm
    change err (m:=m)≤p m 8/2 at hsmall
    nlinarith [p_nonneg hx0.le 8]
  obtain ⟨Z,htri,hmac,hloc,hzero⟩ := GramMetric.realization f.g (B f hm0) c x θ
    (q:=Real.sqrt m) (k:=p m 5) (ε:=p m 200) (a:=p m 40) (b:=(m:ℝ)^40)
    (R:=p m 1997) (T:=3*Real.sqrt m) (Rpos:=0) (γ:=2/Real.sqrt m) (r:=p m 8)
    (Real.sqrt_pos.mpr hx0) (p_nonneg hx0.le 5) (p_one_le hx 5) (p_pos hx0 200) (p_pos hx0 40) hhab
    (p_nonneg hx0.le 1997) (by positivity) (by positivity)
    (by simpa only [Nat.cast_pow] using k_eq hx0)
    (fun s i => (f.norms s i).2) hb hFourier hB hres
    (fun v => by simp [θ]) he (p_pos hx0 8) her
  refine ⟨Z,htri,hmac,?_⟩
  intro v w hc hsum
  have hh := local_tau hm hl
  have h := hloc v w hc (by rw [hsum]; exact hh.1) (by rw [hsum]; exact hh.2.1)
  rw [hsum] at h
  exact h.trans hh.2.2

-- @@ L79-79 verbatim
end

-- @@ L80-80 verbatim
end UniformSparsestCut.SourceMetric


-- @@ L82-82 verbatim
namespace UniformSparsestCut.SourceMetric

-- @@ L83-83 verbatim
open scoped BigOperators RealInnerProductSpace

-- @@ L84-84 verbatim
open SourceParameters SourceCharts

-- @@ L85-85 verbatim
noncomputable section

-- @@ L86-86 verbatim
variable {m : ℕ} (f : PivotFamily.PFamily m) [NeZero m]

-- @@ L87-87 verbatim
local notation "E" => EuclideanSpace ℝ (Fin m)

-- @@ L88-88 verbatim
def C₀ : ℝ := 9+2*KernelApprox.cstar

-- @@ L89-89 verbatim
lemma C₀_pos : 0<C₀ := by unfold C₀; linarith [KernelApprox.cstar_pos]

-- @@ L90-92 verbatim
def vertex (s : Fin (m^3)) (θ : E) (hθ : θ∈RoundedCharts.cube 2)
    (hs : RoundedCharts.regular (u f s) (p m 2000) θ) : V f :=
  ⟨(s,RoundedCharts.integerLabel (u f s) (p m 2000) θ),θ,hθ,hs,rfl⟩

-- @@ L93-99 verbatim
omit [NeZero m] in
lemma near_norm (hm : 3000 ≤ m) : Real.sqrt m*p m 1997≤p m 8 := by
  have hx : (1:ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  calc
    _ ≤ (m:ℝ)*p m 1997 := mul_le_mul_of_nonneg_right (sqrt_le hx) (p_nonneg (by positivity) _)
    _ = p m 1996 := p_succ (by positivity : (m:ℝ)≠0) 1996
    _ ≤ _ := p_le hx (by norm_num)

-- @@ L100-135 verbatim
lemma macro_bound (hm : 3000 ≤ m) (Z : V f → EuclideanSpace ℝ (V f))
    (hmac : ∀ v w, |‖Z v-Z w‖^2-KernelApprox.cstar*Real.sqrt m*
         ‖B f (NeZero.pos m) v.val.1 (RoundedCharts.coordinate (u f) (p m 2000) v)-
           B f (NeZero.pos m) w.val.1 (RoundedCharts.coordinate (u f) (p m 2000) w)‖|≤err (m:=m)+8*p m 8)
    (s t : Fin (m^3)) (θ η : E) (hθ : θ∈RoundedCharts.cube 2) (hη : η∈RoundedCharts.cube 2)
    (hs : RoundedCharts.regular (u f s) (p m 2000) θ)
    (ht : RoundedCharts.regular (u f t) (p m 2000) η) :
    |‖Z (vertex f s θ hθ hs)-Z (vertex f t η hη ht)‖^2-KernelApprox.cstar*Real.sqrt m*‖θ-η‖|≤C₀*p m 8 := by
  let v := vertex f s θ hθ hs
  let w := vertex f t η hη ht
  let X := B f (NeZero.pos m) s (RoundedCharts.rounded (u f s) (p m 2000) θ)
  let Y := B f (NeZero.pos m) t (RoundedCharts.rounded (u f t) (p m 2000) η)
  have hτ : 0<p m 2000 := p_pos (by exact_mod_cast NeZero.pos m) _
  have hx : ‖X-θ‖≤p m 1997 := by
    simpa only [rounded_radius (NeZero.pos m)] using rounded_B_error f (NeZero.pos m) (show 2 ≤ m by omega) hτ s θ
  have hy : ‖Y-η‖≤p m 1997 := by
    simpa only [rounded_radius (NeZero.pos m)] using rounded_B_error f (NeZero.pos m) (show 2 ≤ m by omega) hτ t η
  have hnorm : |‖X-Y‖-‖θ-η‖|≤2*p m 1997 := by
    calc
      _ ≤ ‖(X-Y)-(θ-η)‖ := abs_norm_sub_norm_le _ _
      _ = ‖(X-θ)-(Y-η)‖ := by congr 1; abel
      _ ≤ ‖X-θ‖+‖Y-η‖ := norm_sub_le _ _
      _ ≤ _ := by linarith
  have hM := hmac v w
  change |‖Z v-Z w‖^2-KernelApprox.cstar*Real.sqrt m*‖X-Y‖|≤err (m:=m)+8*p m 8 at hM
  have hq : 0≤KernelApprox.cstar*Real.sqrt m := mul_nonneg KernelApprox.cstar_pos.le (Real.sqrt_nonneg _)
  have hh := mul_le_mul_of_nonneg_left (near_norm (m:=m) hm) (mul_nonneg (by norm_num : (0:ℝ)≤2) KernelApprox.cstar_pos.le)
  have he := macro_small hm
  change err (m:=m)≤p m 8/2 at he
  have hM' := abs_le.mp hM
  have hn' := abs_le.mp hnorm
  have hn1 := mul_le_mul_of_nonneg_left hn'.1 hq
  have hn2 := mul_le_mul_of_nonneg_left hn'.2 hq
  change |‖Z v-Z w‖^2-KernelApprox.cstar*Real.sqrt m*‖θ-η‖|≤_
  rw [abs_le]; unfold C₀
  constructor <;> nlinarith [p_nonneg (by positivity : (0:ℝ) ≤ m) 8]

-- @@ L136-149 verbatim
lemma one_step (vp vm : V f) (i : Fin (m^6))
    (hi : vp.val.2 i=vm.val.2 i+1) (hj : ∀ j, j≠i → vp.val.2 j=vm.val.2 j) :
    (∑ j, |RoundedCharts.coordinate (u f) (p m 2000) vp j-
        RoundedCharts.coordinate (u f) (p m 2000) vm j|)=p m 2000 := by
  classical
  rw [Finset.sum_eq_single i]
  · change |p m 2000*(vp.val.2 i:ℝ)-p m 2000*(vm.val.2 i:ℝ)|=_
    rw [hi,Int.cast_add,Int.cast_one]
    have h : p m 2000*((vm.val.2 i:ℝ)+1)-p m 2000*(vm.val.2 i:ℝ)=p m 2000 := by ring
    rw [h,abs_of_pos (p_pos (by exact_mod_cast NeZero.pos m) _)]
  · intro j hmem hji
    change |p m 2000*(vp.val.2 j:ℝ)-p m 2000*(vm.val.2 j:ℝ)|=0
    rw [hj j hji,sub_self,abs_zero]
  · simp

-- @@ L150-150 verbatim
end

-- @@ L151-151 verbatim
end UniformSparsestCut.SourceMetric


-- @@ L153-153 verbatim
end


-- @@ L155-155 verbatim
end OAI
