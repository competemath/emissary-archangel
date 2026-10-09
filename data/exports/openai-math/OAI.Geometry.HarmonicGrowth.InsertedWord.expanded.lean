import OAI.Geometry.HarmonicGrowth.Transmission


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open Filter MeasureTheory

-- @@ L7-7 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L8-8 verbatim
open scoped Topology

-- @@ L9-9 verbatim
open scoped Topology

-- @@ L10-10 verbatim
open scoped Topology BigOperators ContDiff InnerProductSpace

-- @@ L11-11 verbatim
open Filter MeasureTheory Set

-- @@ L12-12 verbatim
open Set

-- @@ L13-13 verbatim
open scoped Matrix.Norms.Frobenius

-- @@ L14-14 verbatim
open MeasureTheory Set

-- @@ L15-15 verbatim
open scoped Matrix.Norms.Frobenius


-- @@ L17-17 verbatim
namespace HarmonicCounterexample.FiniteControl.SmoothWord

-- @@ L18-18 verbatim
open Set

-- @@ L19-19 verbatim
open scoped BigOperators ContDiff

-- @@ L20-21 verbatim
variable {E H ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [Fintype ι]


-- @@ L23-27 verbatim
/-- Actual nonlinear angular coefficients are glued by their deviations from
roundness. This finite sum is smooth without differentiating a discontinuous
angular selector. On disjoint packet supports it is exactly the Berger model. -/
def nonlinearPacket (r : ℝ) (b : E) (D : ι → E) (q : ι → ℝ) : E :=
  b+∑ j,(PulseTaylor.angular r b (D j) (q j)-b)


-- @@ L29-37 verbatim
lemma nonlinearPacket_selected (r : ℝ) (b : E) (D : ι → E) (q : ι → ℝ)
    (d : ι) (hd : ∀ j,j ≠ d → q j=1) :
    nonlinearPacket r b D q=PulseTaylor.angular r b (D d) (q d) := by
  unfold nonlinearPacket
  rw [Finset.sum_eq_single d]
  · abel
  · intro j _ hj
    rw [hd j hj,PulseTaylor.angular_one,sub_self]
  · simp


-- @@ L39-49 verbatim
/-- Smoothness of the actual finite nonlinear coefficient, including all
round gaps. Positivity excludes the sole singularity of real-power calculus. -/
lemma nonlinearPacket_smooth (r : ℝ) (b : E) (D : ι → E) (q : ι → H → ℝ)
    (hq : ∀ j,ContDiff ℝ ∞ (q j)) (hne : ∀ j x,q j x ≠ 0) :
    ContDiff ℝ ∞ (fun x => nonlinearPacket r b D (fun j => q j x)) := by
  apply contDiff_const.add
  apply ContDiff.sum
  intro j _
  exact (((hq j).rpow_const_of_ne (hne j)).smul contDiff_const |>.add
    (((hq j).rpow_const_of_ne (hne j)).sub
      ((hq j).rpow_const_of_ne (hne j)) |>.smul contDiff_const)).sub contDiff_const


-- @@ L51-63 verbatim
/-- The full parameter jet of the true nonlinear family, not a formal
linearized coefficient supplied as an assumption. -/
lemma nonlinearPacket_hasFDerivAt (r : ℝ) (b : E) (D : ι → E) (q : ι → H → ℝ)
    (q' : ι → H →L[ℝ] ℝ) (x : H) (hq : ∀ j,HasFDerivAt (q j) (q' j) x)
    (hne : ∀ j,q j x ≠ 0) :
    HasFDerivAt (fun y => nonlinearPacket r b D (fun j => q j y))
      (∑ j,(q' j).smulRight (PulseTaylor.angularD r b (D j) (q j x))) x := by
  have hj (j : ι) : HasFDerivAt (fun y => PulseTaylor.angular r b (D j) (q j y)-b)
      ((q' j).smulRight (PulseTaylor.angularD r b (D j) (q j x))) x := by
    have he := ((PulseTaylor.angular_hasDerivAt r b (D j) (hne j)).hasFDerivAt.comp x (hq j)).sub_const b
    convert he using 1 <;> ext z <;> simp
  simpa only [nonlinearPacket, Pi.add_apply, Finset.sum_apply] using
    (HasFDerivAt.sum (u := Finset.univ) fun j _ => hj j).const_add b


-- @@ L65-74 verbatim
lemma nonlinearPacket_jet_selected (r : ℝ) (b : E) (D : ι → E) (q : ι → ℝ)
    (q' : ι → H →L[ℝ] ℝ) (d : ι) (hd : ∀ j,j ≠ d → q' j=0) :
    (∑ j,(q' j).smulRight (PulseTaylor.angularD r b (D j) (q j)))=
      (q' d).smulRight (PulseTaylor.angularD r b (D d) (q d)) := by
  apply Finset.sum_eq_single d
  · intro j _ hj
    rw [hd j hj]
    ext z
    simp
  · simp


-- @@ L76-76 verbatim
end HarmonicCounterexample.FiniteControl.SmoothWord


-- @@ L78-78 verbatim
end


-- @@ L80-80 verbatim
noncomputable section

-- @@ L81-81 verbatim
open Filter MeasureTheory

-- @@ L82-82 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L83-83 verbatim
open scoped Topology

-- @@ L84-84 verbatim
open scoped Topology

-- @@ L85-85 verbatim
open scoped Topology BigOperators ContDiff InnerProductSpace

-- @@ L86-86 verbatim
open Filter MeasureTheory Set

-- @@ L87-87 verbatim
open Set

-- @@ L88-88 verbatim
open scoped Matrix.Norms.Frobenius

-- @@ L89-89 verbatim
open MeasureTheory Set

-- @@ L90-90 verbatim
open scoped Matrix.Norms.Frobenius


-- @@ L92-92 verbatim
namespace HarmonicCounterexample.FiniteControl.SmoothWord

-- @@ L93-93 verbatim
open Set

-- @@ L94-94 verbatim
open scoped BigOperators ContDiff

-- @@ L95-95 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}


-- @@ L97-99 verbatim
/-- Stretch inside one of the disjoint unit-time packets. -/
def packetStretch (a : Fin n → ℝ) (T t : ℝ) (j : Fin n) : ℝ :=
  1+T⁻¹*(duration n)*(a j*bump j (duration n*t))


-- @@ L101-102 verbatim
def nonlinearBergerWord (r : ℝ) (b : E) (D : Fin n → E) (a : Fin n → ℝ)
    (T t : ℝ) : E := nonlinearPacket r b D (packetStretch a T t)


-- @@ L104-113 verbatim
lemma packetStretch_selected (a : Fin n → ℝ) (T t : ℝ) (d : Fin n)
    (hd : ∀ j,j ≠ d → bump j (duration n*t)=0) :
    packetStretch a T t d=1+T⁻¹*unitPacketScalar a t := by
  have hsum : ∑ j : Fin n,a j*bump j (duration n*t)=a d*bump d (duration n*t) := by
    apply Finset.sum_eq_single d
    · intro j _ hj
      rw [hd j hj,mul_zero]
    · simp
  simp only [packetStretch,unitPacketScalar,packetScalar,hsum]
  ring


-- @@ L115-125 verbatim
/-- Exact actual Berger operator on each pulse, with round interpolation
in all gaps. The scalar and angular parts are genuinely the source model. -/
lemma nonlinearBergerWord_selected (r : ℝ) (b : E) (D : Fin n → E) (a : Fin n → ℝ)
    (T t : ℝ) (d : Fin n) (hd : ∀ j,j ≠ d → bump j (duration n*t)=0) :
    nonlinearBergerWord r b D a T t=
      PulseTaylor.angular r b (D d) (1+T⁻¹*unitPacketScalar a t) := by
  unfold nonlinearBergerWord
  rw [nonlinearPacket_selected r b D (packetStretch a T t) d (by
    intro j hj
    simp only [packetStretch,hd j hj,mul_zero,add_zero])]
  rw [packetStretch_selected a T t d hd]


-- @@ L127-131 verbatim
lemma packetStretch_smooth (a : Fin n → ℝ) (T : ℝ) (j : Fin n) :
    ContDiff ℝ ∞ (fun t => packetStretch a T t j) := by
  exact contDiff_const.add (contDiff_const.mul
    (contDiff_const.mul ((bump_smooth j).comp
      (contDiff_const.mul contDiff_id))))


-- @@ L133-137 verbatim
lemma nonlinearBergerWord_smooth (r : ℝ) (b : E) (D : Fin n → E) (a : Fin n → ℝ)
    (T : ℝ) (hne : ∀ j t,packetStretch a T t j ≠ 0) :
    ContDiff ℝ ∞ (nonlinearBergerWord r b D a T) :=
  nonlinearPacket_smooth r b D (fun j t => packetStretch a T t j)
    (packetStretch_smooth a T) hne


-- @@ L139-139 verbatim
end HarmonicCounterexample.FiniteControl.SmoothWord


-- @@ L141-141 verbatim
end


-- @@ L143-143 verbatim
noncomputable section

-- @@ L144-144 verbatim
open Filter MeasureTheory

-- @@ L145-145 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L146-146 verbatim
open scoped Topology

-- @@ L147-147 verbatim
open scoped Topology

-- @@ L148-148 verbatim
open scoped Topology BigOperators ContDiff InnerProductSpace

-- @@ L149-149 verbatim
open Filter MeasureTheory Set

-- @@ L150-150 verbatim
open Set

-- @@ L151-151 verbatim
open scoped Matrix.Norms.Frobenius

-- @@ L152-152 verbatim
open MeasureTheory Set

-- @@ L153-153 verbatim
open scoped Matrix.Norms.Frobenius


-- @@ L155-155 verbatim
namespace HarmonicCounterexample.FiniteControl.SmoothWord

-- @@ L156-156 verbatim
open Set

-- @@ L157-157 verbatim
open scoped BigOperators ContDiff


-- @@ L159-190 verbatim
/-- A fixed amplitude bound gives positive stretches for all sufficiently
long physical packets. The threshold is chosen before the amplitudes and
before any incoming ODE history. -/
theorem packetStretch_uniform_positive (n : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (a : Fin n → ℝ) (U T : ℝ),0 ≤ U →
      (∀ j,|a j| ≤ U) → 0 < T → 2*C*U ≤ T → ∀ t j,
      packetStretch a T t j ∈ Icc (1/2:ℝ) (3/2) := by
  classical
  choose Cs hCs hb using fun j : Fin n => packet_functions_bounded j
  let S : ℝ := ∑ j : Fin n,Cs j
  let C : ℝ := duration n*S
  have hS : 0 ≤ S := Finset.sum_nonneg (fun j _ => hCs j)
  have hC : 0 ≤ C := mul_nonneg (duration_pos n).le hS
  refine ⟨C,hC,?_⟩
  intro a U T hU ha hT hlong t j
  have hjS : Cs j ≤ S := Finset.single_le_sum (fun k _ => hCs k) (Finset.mem_univ j)
  have hbS : |bump j (duration n*t)| ≤ S := (hb j _).1.trans hjS
  have hn : duration n*(|a j| * |bump j (duration n*t)|) ≤ C*U := by
    calc
      _ ≤ duration n*(U*S) := mul_le_mul_of_nonneg_left
        (mul_le_mul (ha j) hbS (abs_nonneg _) hU) (duration_pos n).le
      _ = C*U := by dsimp [C]; ring
  have hsmall : |T⁻¹*duration n*(a j*bump j (duration n*t))| ≤ (1/2:ℝ) := by
    calc
      _ = (duration n*(|a j| * |bump j (duration n*t)|))/T := by
        rw [abs_mul,abs_mul,abs_mul,abs_inv,abs_of_pos hT,abs_of_pos (duration_pos n)]
        ring
      _ ≤ (C*U)/T := div_le_div_of_nonneg_right hn hT.le
      _ ≤ 1/2 := (div_le_iff₀ hT).2 (by linarith)
  have hh := abs_le.1 hsmall
  dsimp [packetStretch]
  constructor <;> linarith


-- @@ L192-193 verbatim
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}


-- @@ L195-201 verbatim
lemma packetStretch_hasFDerivAt (a : Fin n → H → ℝ) (a' : Fin n → H →L[ℝ] ℝ)
    {x : H} (ha : ∀ j,HasFDerivAt (a j) (a' j) x) (T t : ℝ) (j : Fin n) :
    HasFDerivAt (fun y => packetStretch (fun k => a k y) T t j)
      ((T⁻¹*duration n*bump j (duration n*t)) • a' j) x := by
  have hh := ((ha j).mul_const (bump j (duration n*t))).const_mul (T⁻¹*duration n)
  convert hh.const_add 1 using 1 <;> ext z <;>
    simp [packetStretch,mul_assoc,mul_comm,mul_left_comm]


-- @@ L203-215 verbatim
/-- The endpoint family uses the genuine Frechet derivative of the smooth
nonlinear angular coefficient, including parameter variation in the packets. -/
lemma nonlinearBergerWord_hasFDerivAt (r : ℝ) (b : E) (D : Fin n → E)
    (a : Fin n → H → ℝ) (a' : Fin n → H →L[ℝ] ℝ) {x : H}
    (ha : ∀ j,HasFDerivAt (a j) (a' j) x) (T t : ℝ)
    (hne : ∀ j,packetStretch (fun k => a k x) T t j ≠ 0) :
    HasFDerivAt (fun y => nonlinearBergerWord r b D (fun j => a j y) T t)
      (∑ j : Fin n,((T⁻¹*duration n*bump j (duration n*t)) • a' j).smulRight
        (PulseTaylor.angularD r b (D j) (packetStretch (fun k => a k x) T t j))) x :=
  nonlinearPacket_hasFDerivAt r b D
    (fun j y => packetStretch (fun k => a k y) T t j)
    (fun j => (T⁻¹*duration n*bump j (duration n*t)) • a' j) x
    (packetStretch_hasFDerivAt a a' ha T t) hne


-- @@ L217-227 verbatim
/-- A duration threshold alone suffices for a globally smooth actual
Berger word. Nonzero stretches are proved, rather than left as assumptions. -/
theorem nonlinearBergerWord_smooth_for_long_packets (n : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (r : ℝ) (b : E) (D : Fin n → E) (a : Fin n → ℝ)
      (U T : ℝ),0 ≤ U → (∀ j,|a j| ≤ U) → 0 < T → 2*C*U ≤ T →
      ContDiff ℝ ∞ (nonlinearBergerWord r b D a T) := by
  obtain ⟨C,hC,hpos⟩ := packetStretch_uniform_positive n
  refine ⟨C,hC,?_⟩
  intro r b D a U T hU ha hT hlong
  exact nonlinearBergerWord_smooth r b D a T (fun j t =>
    ne_of_gt (lt_of_lt_of_le (by norm_num) (hpos a U T hU ha hT hlong t j).1))


-- @@ L229-229 verbatim
end HarmonicCounterexample.FiniteControl.SmoothWord


-- @@ L231-231 verbatim
end


-- @@ L233-233 verbatim
noncomputable section

-- @@ L234-234 verbatim
open Filter MeasureTheory

-- @@ L235-235 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L236-236 verbatim
open scoped Topology

-- @@ L237-237 verbatim
open scoped Topology

-- @@ L238-238 verbatim
open scoped Topology BigOperators ContDiff InnerProductSpace

-- @@ L239-239 verbatim
open Filter MeasureTheory Set

-- @@ L240-240 verbatim
open Set

-- @@ L241-241 verbatim
open scoped Matrix.Norms.Frobenius

-- @@ L242-242 verbatim
open MeasureTheory Set

-- @@ L243-243 verbatim
open scoped Matrix.Norms.Frobenius


-- @@ L245-245 verbatim
namespace HarmonicCounterexample.FiniteControl.SmoothWord

-- @@ L246-246 verbatim
open Set Filter

-- @@ L247-247 verbatim
open scoped Topology BigOperators ContDiff

-- @@ L248-248 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}


-- @@ L250-252 verbatim
lemma nonlinearPacket_round (r : ℝ) (b : E) (D : Fin n → E) :
    nonlinearPacket r b D (fun _ => 1)=b := by
  simp [nonlinearPacket,PulseTaylor.angular_one]


-- @@ L254-264 verbatim
lemma nonlinearBergerWord_round_before (r : ℝ) (b : E) (D : Fin n → E)
    (a : Fin n → ℝ) (T t : ℝ) (ht : duration n*t < 1) :
    nonlinearBergerWord r b D a T t=b := by
  have hq : packetStretch a T t=(fun _ => 1) := by
    funext j
    have hz : bump j (duration n*t)=0 := bump_zero_before (by
      have hj : (0:ℝ) ≤ j := Nat.cast_nonneg _
      linarith)
    simp [packetStretch,hz]
  unfold nonlinearBergerWord
  rw [hq,nonlinearPacket_round]


-- @@ L266-275 verbatim
lemma nonlinearBergerWord_round_after (r : ℝ) (b : E) (D : Fin n → E)
    (a : Fin n → ℝ) (T t : ℝ) (ht : 2*(n:ℝ) < duration n*t) :
    nonlinearBergerWord r b D a T t=b := by
  have hq : packetStretch a T t=(fun _ => 1) := by
    funext j
    have hj : (j:ℝ)+1 ≤ n := by exact_mod_cast j.isLt
    have hz : bump j (duration n*t)=0 := bump_zero_after (by linarith)
    simp [packetStretch,hz]
  unfold nonlinearBergerWord
  rw [hq,nonlinearPacket_round]


-- @@ L277-292 verbatim
/-- A fixed round collar at each end works for every amplitude vector and
every physical duration. This allows smooth rotation of complex structures
in the gaps without changing the angular metric. -/
theorem nonlinearBergerWord_round_collars (n : ℕ) (r : ℝ) (b : E) (D : Fin n → E) :
    (∀ᶠ t in 𝓝 (0:ℝ),∀ a T,nonlinearBergerWord r b D a T t=b) ∧
    (∀ᶠ t in 𝓝 (1:ℝ),∀ a T,nonlinearBergerWord r b D a T t=b) := by
  have hc : Continuous (fun t : ℝ => duration n*t) := continuous_const.mul continuous_id
  constructor
  · have hh : ∀ᶠ t in 𝓝 (0:ℝ),duration n*t < 1 :=
      (hc.continuousAt.eventually_lt continuousAt_const (by simp))
    filter_upwards [hh] with t ht a T
    exact nonlinearBergerWord_round_before r b D a T t ht
  · have hh : ∀ᶠ t in 𝓝 (1:ℝ),2*(n:ℝ) < duration n*t :=
      (continuousAt_const.eventually_lt hc.continuousAt (by simp [duration]))
    filter_upwards [hh] with t ht a T
    exact nonlinearBergerWord_round_after r b D a T t ht


-- @@ L294-294 verbatim
end HarmonicCounterexample.FiniteControl.SmoothWord


-- @@ L296-296 verbatim
end


-- @@ L298-298 verbatim
noncomputable section

-- @@ L299-299 verbatim
open Filter MeasureTheory

-- @@ L300-300 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L301-301 verbatim
open scoped Topology

-- @@ L302-302 verbatim
open scoped Topology

-- @@ L303-303 verbatim
open scoped Topology BigOperators ContDiff InnerProductSpace

-- @@ L304-304 verbatim
open Filter MeasureTheory Set

-- @@ L305-305 verbatim
open Set

-- @@ L306-306 verbatim
open scoped Matrix.Norms.Frobenius

-- @@ L307-307 verbatim
open MeasureTheory Set

-- @@ L308-308 verbatim
open scoped Matrix.Norms.Frobenius


-- @@ L310-310 verbatim
namespace HarmonicCounterexample.FiniteControl.SmoothWord

-- @@ L311-311 verbatim
open scoped InnerProductSpace

-- @@ L312-312 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- @@ L313-313 verbatim
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup

-- @@ L314-314 verbatim
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace


-- @@ L316-334 verbatim
/-- Positivity of the actual Berger angular operator follows from the
vertical square spectral interval [-B,0], not from a separate positivity hypothesis
on the produced perturbed operator. -/
lemma berger_angular_nonneg (r B q : ℝ) (D : E →L[ℝ] E) (hq : 0 ≤ q)
    (hD : ∀ x,inner ℝ x (D x) ≤ 0)
    (hBD : ∀ x,-(B*‖x‖^2) ≤ inner ℝ x (D x)) (x : E) :
    0 ≤ inner ℝ x (PulseTaylor.angular r (B • (1:E →L[ℝ] E)) D q x) := by
  have h₁ : 0 ≤ q^r*(B*‖x‖^2+inner ℝ x (D x)) :=
    mul_nonneg (Real.rpow_nonneg hq _) (by linarith [hBD x])
  have h₂ : 0 ≤ q^(r-1)*(-inner ℝ x (D x)) :=
    mul_nonneg (Real.rpow_nonneg hq _) (neg_nonneg.2 (hD x))
  have he : inner ℝ x (PulseTaylor.angular r (B • (1:E →L[ℝ] E)) D q x)=
      q^r*(B*‖x‖^2+inner ℝ x (D x))+q^(r-1)*(-inner ℝ x (D x)) := by
    simp only [PulseTaylor.angular,add_apply,
      smul_apply,one_apply_eq_self,
      inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq]
    ring
  rw [he]
  exact add_nonneg h₁ h₂


-- @@ L336-348 verbatim
/-- Each actual finite pulse is nonnegative for every vector. Positivity
is inherited from exact disjoint-support reduction to the source angular
formula, including the round gaps. -/
lemma nonlinearBergerWord_nonneg {n : ℕ} (r B : ℝ) (D : Fin n → E →L[ℝ] E)
    (a : Fin n → ℝ) (T t : ℝ) (d : Fin n)
    (hd : ∀ j,j ≠ d → bump j (duration n*t)=0)
    (hq : 0 ≤ packetStretch a T t d)
    (hD : ∀ j x,inner ℝ x (D j x) ≤ 0)
    (hBD : ∀ j x,-(B*‖x‖^2) ≤ inner ℝ x (D j x)) (x : E) :
    0 ≤ inner ℝ x (nonlinearBergerWord r (B • (1:E →L[ℝ] E)) D a T t x) := by
  rw [nonlinearBergerWord_selected r (B • (1:E →L[ℝ] E)) D a T t d hd]
  rw [packetStretch_selected a T t d hd] at hq
  exact berger_angular_nonneg r B _ (D d) hq (hD d) (hBD d) x


-- @@ L350-350 verbatim
end HarmonicCounterexample.FiniteControl.SmoothWord


-- @@ L352-352 verbatim
end


-- @@ L354-354 verbatim
noncomputable section

-- @@ L355-355 verbatim
open Filter MeasureTheory

-- @@ L356-356 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L357-357 verbatim
open scoped Topology

-- @@ L358-358 verbatim
open scoped Topology

-- @@ L359-359 verbatim
open scoped Topology BigOperators ContDiff InnerProductSpace

-- @@ L360-360 verbatim
open Filter MeasureTheory Set

-- @@ L361-361 verbatim
open Set

-- @@ L362-362 verbatim
open scoped Matrix.Norms.Frobenius

-- @@ L363-363 verbatim
open MeasureTheory Set

-- @@ L364-364 verbatim
open scoped Matrix.Norms.Frobenius


-- @@ L366-366 verbatim
namespace HarmonicCounterexample.FiniteControl.SmoothWord

-- @@ L367-367 verbatim
open Set

-- @@ L368-368 verbatim
open scoped ContDiff

-- @@ L369-370 verbatim
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}


-- @@ L372-376 verbatim
/-- Replace only the angular part of an incoming coefficient history on
one new pulse. The formula is global and smooth, with no piecewise selector. -/
def insertWord (history : ℝ → E) (α : ℝ → ℝ) (r : ℝ) (b : E)
    (D : Fin n → E) (amps : Fin n → ℝ) (a T t : ℝ) : E :=
  history t+α t • (nonlinearBergerWord r b D amps T ((t-a)/T)-b)


-- @@ L378-384 verbatim
lemma insertWord_before (history : ℝ → E) (α : ℝ → ℝ) (r : ℝ) (b : E)
    (D : Fin n → E) (amps : Fin n → ℝ) (a T t : ℝ) (hT : 0 < T) (ht : t ≤ a) :
    insertWord history α r b D amps a T t=history t := by
  have hu : (t-a)/T ≤ 0 := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 ht) hT.le
  have he := nonlinearBergerWord_round_before r b D amps T ((t-a)/T)
    (lt_of_le_of_lt (mul_nonpos_of_nonneg_of_nonpos (duration_pos n).le hu) (by norm_num))
  simp only [insertWord,he,sub_self,smul_zero,add_zero]


-- @@ L386-394 verbatim
lemma insertWord_after (history : ℝ → E) (α : ℝ → ℝ) (r : ℝ) (b : E)
    (D : Fin n → E) (amps : Fin n → ℝ) (a T t : ℝ) (hT : 0 < T) (ht : a+T ≤ t) :
    insertWord history α r b D amps a T t=history t := by
  have hu : 1 ≤ (t-a)/T := (le_div_iff₀ hT).2 (by linarith)
  have hu' : duration n ≤ duration n*((t-a)/T) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hu (duration_pos n).le
  have he := nonlinearBergerWord_round_after r b D amps T ((t-a)/T)
    (lt_of_lt_of_le (by simp [duration]) hu')
  simp only [insertWord,he,sub_self,smul_zero,add_zero]


-- @@ L396-402 verbatim
lemma insertWord_on_round (history : ℝ → E) (α : ℝ → ℝ) (r : ℝ) (b : E)
    (D : Fin n → E) (amps : Fin n → ℝ) (a T t : ℝ)
    (hround : history t=α t • b) :
    insertWord history α r b D amps a T t=
      α t • nonlinearBergerWord r b D amps T ((t-a)/T) := by
  simp only [insertWord,hround,smul_sub]
  abel


-- @@ L404-410 verbatim
lemma insertWord_smooth (history : ℝ → E) (α : ℝ → ℝ) (r : ℝ) (b : E)
    (D : Fin n → E) (amps : Fin n → ℝ) (a T : ℝ)
    (hh : ContDiff ℝ ∞ history) (hα : ContDiff ℝ ∞ α)
    (hq : ∀ j t,packetStretch amps T t j ≠ 0) :
    ContDiff ℝ ∞ (insertWord history α r b D amps a T) := by
  exact hh.add (hα.smul (((nonlinearBergerWord_smooth r b D amps T hq).comp
    ((contDiff_id.sub contDiff_const).div_const T)).sub contDiff_const))


-- @@ L412-423 verbatim
/-- The actual parameter jet is exactly zero throughout the preceding
history, for arbitrary parameter dependence of the new amplitudes. -/
lemma insertWord_jet_history_zero (history : ℝ → E) (α : ℝ → ℝ)
    (r : ℝ) (b : E) (D : Fin n → E) (amps : H → Fin n → ℝ)
    (a T t : ℝ) (hT : 0 < T) (ht : t ≤ a) (x : H) :
    fderiv ℝ (fun y => insertWord history α r b D (amps y) a T t) x=0 := by
  have he : (fun y => insertWord history α r b D (amps y) a T t)=
      (fun _ : H => history t) := by
    funext y
    exact insertWord_before history α r b D (amps y) a T t hT ht
  rw [he]
  exact (hasFDerivAt_const (history t) x).fderiv


-- @@ L425-425 verbatim
end HarmonicCounterexample.FiniteControl.SmoothWord


-- @@ L427-427 verbatim
end


-- @@ L429-429 verbatim
noncomputable section

-- @@ L430-430 verbatim
open Filter MeasureTheory

-- @@ L431-431 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L432-432 verbatim
open scoped Topology

-- @@ L433-433 verbatim
open scoped Topology

-- @@ L434-434 verbatim
open scoped Topology BigOperators ContDiff InnerProductSpace

-- @@ L435-435 verbatim
open Filter MeasureTheory Set

-- @@ L436-436 verbatim
open Set

-- @@ L437-437 verbatim
open scoped Matrix.Norms.Frobenius

-- @@ L438-438 verbatim
open MeasureTheory Set

-- @@ L439-439 verbatim
open scoped Matrix.Norms.Frobenius


-- @@ L441-441 verbatim
namespace HarmonicCounterexample.FiniteControl.SmoothWord

-- @@ L442-442 verbatim
open scoped BigOperators

-- @@ L443-444 verbatim
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}


-- @@ L446-471 verbatim
lemma nonlinearBergerWord_jet_selected (r : ℝ) (b : E) (D : Fin n → E)
    (a : Fin n → ℝ) (a' : Fin n → H →L[ℝ] ℝ) (T t : ℝ) (d : Fin n)
    (hd : ∀ j,j ≠ d → bump j (duration n*t)=0) (v : H) :
    (∑ j : Fin n,((T⁻¹*duration n*bump j (duration n*t)) • a' j).smulRight
      (PulseTaylor.angularD r b (D j) (packetStretch a T t j))) v=
    (T⁻¹*unitPacketScalar (fun j => a' j v) t) •
      PulseTaylor.angularD r b (D d) (1+T⁻¹*unitPacketScalar a t) := by
  have hs : (∑ j : Fin n,((T⁻¹*duration n*bump j (duration n*t)) • a' j).smulRight
      (PulseTaylor.angularD r b (D j) (packetStretch a T t j)))=
      ((T⁻¹*duration n*bump d (duration n*t)) • a' d).smulRight
        (PulseTaylor.angularD r b (D d) (packetStretch a T t d)) := by
    apply Finset.sum_eq_single d
    · intro j _ hj
      simp [hd j hj]
    · simp
  rw [hs]
  simp only [ContinuousLinearMap.smulRight_apply,smul_apply,smul_eq_mul]
  rw [packetStretch_selected a T t d hd]
  have hsum : (∑ j : Fin n,a' j v*bump j (duration n*t))=a' d v*bump d (duration n*t) := by
    apply Finset.sum_eq_single d
    · intro j _ hj
      rw [hd j hj,mul_zero]
    · simp
  simp only [unitPacketScalar,packetScalar,hsum]
  congr 1
  ring


-- @@ L473-484 verbatim
/-- The exact jet hypothesis in the actual finite Berger error theorem
is supplied by differentiation of the actual smooth coefficient family. -/
lemma nonlinearBergerWord_fderiv_ray_selected (r : ℝ) (b : E) (D : Fin n → E)
    (a : Fin n → H → ℝ) (a' : Fin n → H →L[ℝ] ℝ) {x : H}
    (ha : ∀ j,HasFDerivAt (a j) (a' j) x) (T t : ℝ)
    (hne : ∀ j,packetStretch (fun k => a k x) T t j ≠ 0)
    (d : Fin n) (hd : ∀ j,j ≠ d → bump j (duration n*t)=0) (v : H) :
    fderiv ℝ (fun y => nonlinearBergerWord r b D (fun j => a j y) T t) x v=
      (T⁻¹*unitPacketScalar (fun j => a' j v) t) •
        PulseTaylor.angularD r b (D d) (1+T⁻¹*unitPacketScalar (fun j => a j x) t) := by
  rw [(nonlinearBergerWord_hasFDerivAt r b D a a' ha T t hne).fderiv]
  exact nonlinearBergerWord_jet_selected r b D (fun j => a j x) a' T t d hd v


-- @@ L486-486 verbatim
end HarmonicCounterexample.FiniteControl.SmoothWord


-- @@ L488-488 verbatim
end


-- @@ L490-490 verbatim
noncomputable section

-- @@ L491-491 verbatim
open Filter MeasureTheory

-- @@ L492-492 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L493-493 verbatim
open scoped Topology

-- @@ L494-494 verbatim
open scoped Topology

-- @@ L495-495 verbatim
open scoped Topology BigOperators ContDiff InnerProductSpace

-- @@ L496-496 verbatim
open Filter MeasureTheory Set

-- @@ L497-497 verbatim
open Set

-- @@ L498-498 verbatim
open scoped Matrix.Norms.Frobenius

-- @@ L499-499 verbatim
open MeasureTheory Set

-- @@ L500-500 verbatim
open scoped Matrix.Norms.Frobenius


-- @@ L502-502 verbatim
namespace HarmonicCounterexample.FiniteControl.SmoothWord

-- @@ L503-503 verbatim
open Set

-- @@ L504-504 verbatim
open scoped InnerProductSpace ContDiff

-- @@ L505-505 verbatim
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

-- @@ L506-506 verbatim
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup

-- @@ L507-507 verbatim
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace


-- @@ L509-529 verbatim
/-- A uniform finite angular producer: every sufficiently long packet gives
a smooth nonnegative actual coefficient for every permitted amplitude vector.
The threshold is independent of the incoming ODE history. -/
theorem actual_smooth_positive_word (n : ℕ) [NeZero n] :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (r B : ℝ) (D : Fin n → E →L[ℝ] E)
      (a : Fin n → ℝ) (U T : ℝ),0 ≤ U → (∀ j,|a j| ≤ U) → 0 < T → 2*C*U ≤ T →
      (∀ j x,inner ℝ x (D j x) ≤ 0) →
      (∀ j x,-(B*‖x‖^2) ≤ inner ℝ x (D j x)) →
      ContDiff ℝ ∞ (nonlinearBergerWord r (B • (1:E →L[ℝ] E)) D a T) ∧
      ∀ t x,0 ≤ inner ℝ x (nonlinearBergerWord r (B • (1:E →L[ℝ] E)) D a T t x) := by
  obtain ⟨C,hC,hpos⟩ := packetStretch_uniform_positive n
  obtain ⟨d,hd⟩ := exists_packet_selector n
  refine ⟨C,hC,?_⟩
  intro r B D a U T hU ha hT hlong hD hBD
  have hq (j : Fin n) (t : ℝ) : 0 < packetStretch a T t j :=
    lt_of_lt_of_le (by norm_num) (hpos a U T hU ha hT hlong t j).1
  refine ⟨nonlinearBergerWord_smooth r (B • (1:E →L[ℝ] E)) D a T
    (fun j t => (hq j t).ne'),?_⟩
  intro t x
  exact nonlinearBergerWord_nonneg r B D a T t (d (duration n*t))
    (fun j hj => (hd _ j hj).1) (hq _ t).le hD hBD x


-- @@ L531-549 verbatim
lemma insertWord_nonneg {n : ℕ} (history : ℝ → E →L[ℝ] E) (α : ℝ → ℝ)
    (r B : ℝ) (D : Fin n → E →L[ℝ] E) (amps : Fin n → ℝ)
    (a T : ℝ) (hT : 0 < T)
    (hh : ∀ t x,0 ≤ inner ℝ x (history t x))
    (hα : ∀ t ∈ Icc a (a+T),0 ≤ α t)
    (hr : ∀ t ∈ Icc a (a+T),history t=α t • (B • (1:E →L[ℝ] E)))
    (hw : ∀ t x,0 ≤ inner ℝ x (nonlinearBergerWord r (B • (1:E →L[ℝ] E)) D amps T t x)) :
    ∀ t x,0 ≤ inner ℝ x (insertWord history α r (B • (1:E →L[ℝ] E)) D amps a T t x) := by
  intro t x
  by_cases h₀ : t ≤ a
  · rw [insertWord_before history α r (B • (1:E →L[ℝ] E)) D amps a T t hT h₀]
    exact hh t x
  by_cases h₁ : a+T ≤ t
  · rw [insertWord_after history α r (B • (1:E →L[ℝ] E)) D amps a T t hT h₁]
    exact hh t x
  have ht : t ∈ Icc a (a+T) := ⟨(lt_of_not_ge h₀).le,(lt_of_not_ge h₁).le⟩
  rw [insertWord_on_round history α r (B • (1:E →L[ℝ] E)) D amps a T t (hr t ht)]
  simp only [smul_apply,inner_smul_right]
  exact mul_nonneg (hα t ht) (hw _ x)


-- @@ L551-551 verbatim
end HarmonicCounterexample.FiniteControl.SmoothWord


-- @@ L553-553 verbatim
end


-- @@ L555-555 verbatim
noncomputable section

-- @@ L556-556 verbatim
open Filter MeasureTheory

-- @@ L557-557 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L558-558 verbatim
open scoped Topology

-- @@ L559-559 verbatim
open scoped Topology

-- @@ L560-560 verbatim
open scoped Topology BigOperators ContDiff InnerProductSpace

-- @@ L561-561 verbatim
open Filter MeasureTheory Set

-- @@ L562-562 verbatim
open Set

-- @@ L563-563 verbatim
open scoped Matrix.Norms.Frobenius

-- @@ L564-564 verbatim
open MeasureTheory Set

-- @@ L565-565 verbatim
open scoped Matrix.Norms.Frobenius


-- @@ L567-567 verbatim
namespace HarmonicCounterexample.LinearODE

-- @@ L568-568 verbatim
open Set

-- @@ L569-570 verbatim
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

-- @@ L571-571 verbatim
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup

-- @@ L572-572 verbatim
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

-- @@ L573-573 verbatim
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance

-- @@ L574-574 verbatim
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance

-- @@ L575-575 verbatim
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup

-- @@ L576-576 verbatim
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace


-- @@ L578-586 verbatim
lemma operator_history_eq {A B : ℝ → E →L[ℝ] E} {T : ℝ}
    (h : EqOn A B (Icc 0 T)) (p : ℝ → ℝ) (l : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    operatorValue A p l t=operatorValue B p l t ∧
    operatorVelocity A p l t=operatorVelocity B p l t := by
  have hblock : EqOn (block (leftAction A) p) (block (leftAction B) p) (Icc 0 T) := by
    intro s hs
    simp only [block,leftAction,h hs]
  have hh := flow_history_eq hblock (ContinuousLinearMap.id ℝ E,l • ContinuousLinearMap.id ℝ E) ht
  exact ⟨congrArg Prod.fst hh,congrArg Prod.snd hh⟩


-- @@ L588-594 verbatim
/-- The actual center-regular Riccati value is causal, even though it is
represented by one globally defined Peano--Baker sum. -/
lemma slope_history_eq {A B : ℝ → E →L[ℝ] E} {T : ℝ}
    (h : EqOn A B (Icc 0 T)) (p : ℝ → ℝ) (l : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    slope A p l t=slope B p l t := by
  obtain ⟨hv,hw⟩ := operator_history_eq h p l ht
  rw [slope,slope,hv,hw]


-- @@ L596-602 verbatim
lemma slopeJet_history_zero {A : H → ℝ → E →L[ℝ] E}
    {K : H → ℝ → H →L[ℝ] OperatorPhase E →L[ℝ] OperatorPhase E}
    {x : H} {T : ℝ} (h : ∀ t ∈ Icc 0 T,K x t=0)
    (p : ℝ → ℝ) (l : ℝ) {t : ℝ} (ht : t ∈ Icc 0 T) :
    slopeJet A p K l x t=0 := by
  have hp : phaseJet A p K l x t=0 := flowD_history_zero h (1,l • 1) t ht
  simp only [slopeJet,valueJet,velocityJet,hp,ContinuousLinearMap.comp_zero,sub_self]


-- @@ L604-613 verbatim
/-- The new control never perturbs its incoming center-regular slope. -/
lemma insertWord_incoming_slope {n : ℕ} (history : ℝ → E →L[ℝ] E) (α : ℝ → ℝ)
    (r : ℝ) (b : E →L[ℝ] E) (D : Fin n → E →L[ℝ] E)
    (amps : Fin n → ℝ) (a T : ℝ) (hT : 0 < T) (ha : 0 ≤ a)
    (p : ℝ → ℝ) (l : ℝ) :
    slope (FiniteControl.SmoothWord.insertWord history α r b D amps a T) p l a=
      slope history p l a := by
  apply slope_history_eq (T := a) (t := a) (p := p) (l := l) _ ⟨ha,le_rfl⟩
  intro s hs
  exact FiniteControl.SmoothWord.insertWord_before history α r b D amps a T s hT hs.2


-- @@ L615-634 verbatim
/-- The actual incoming parameter jet vanishes, not merely an arbitrarily
assigned initial derivative for a restarted surrogate equation. -/
lemma insertWord_incoming_slopeJet {n : ℕ} (history : ℝ → E →L[ℝ] E) (α : ℝ → ℝ)
    (r : ℝ) (b : E →L[ℝ] E) (D : Fin n → E →L[ℝ] E)
    (amps : H → Fin n → ℝ) (a T : ℝ) (hT : 0 < T) (ha : 0 ≤ a)
    (p : ℝ → ℝ) (l : ℝ) (x : H) :
    let A := fun y => FiniteControl.SmoothWord.insertWord history α r b D (amps y) a T
    let K := fun y t => fderiv ℝ (fun z => block (leftAction (A z)) p t) y
    slopeJet A p K l x a=0 := by
  dsimp only
  apply slopeJet_history_zero (T := a) (t := a) (p := p) (l := l) _ ⟨ha,le_rfl⟩
  intro t ht
  have he : (fun z => block (leftAction
      (FiniteControl.SmoothWord.insertWord history α r b D (amps z) a T)) p t)=
      (fun _ : H => block (leftAction history) p t) := by
    funext z
    simp only [block,leftAction,
      FiniteControl.SmoothWord.insertWord_before history α r b D (amps z) a T t hT ht.2]
  rw [he]
  exact (hasFDerivAt_const (block (leftAction history) p t) x).fderiv


-- @@ L636-636 verbatim
end HarmonicCounterexample.LinearODE


-- @@ L638-638 verbatim
end


-- @@ L640-640 verbatim
noncomputable section

-- @@ L641-641 verbatim
open Filter MeasureTheory

-- @@ L642-642 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L643-643 verbatim
open scoped Topology

-- @@ L644-644 verbatim
open scoped Topology

-- @@ L645-645 verbatim
open scoped Topology BigOperators ContDiff InnerProductSpace

-- @@ L646-646 verbatim
open Filter MeasureTheory Set

-- @@ L647-647 verbatim
open Set

-- @@ L648-648 verbatim
open scoped Matrix.Norms.Frobenius

-- @@ L649-649 verbatim
open MeasureTheory Set

-- @@ L650-650 verbatim
open scoped Matrix.Norms.Frobenius


-- @@ L652-652 verbatim
namespace HarmonicCounterexample.FiniteControl.SmoothWord

-- @@ L653-653 verbatim
open scoped BigOperators

-- @@ L654-655 verbatim
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}


-- @@ L657-669 verbatim
/-- The history insertion has the genuine full parameter derivative of the
nonlinear Berger coefficient; the preceding history is not differentiated. -/
lemma insertWord_hasFDerivAt (history : ℝ → E) (α : ℝ → ℝ)
    (r : ℝ) (b : E) (D : Fin n → E) (amps : Fin n → H → ℝ)
    (amps' : Fin n → H →L[ℝ] ℝ) {x : H}
    (ha : ∀ j,HasFDerivAt (amps j) (amps' j) x) (a T t : ℝ)
    (hne : ∀ j,packetStretch (fun k => amps k x) T ((t-a)/T) j ≠ 0) :
    HasFDerivAt (fun y => insertWord history α r b D (fun j => amps j y) a T t)
      (α t • ∑ j : Fin n,
        ((T⁻¹*duration n*bump j (duration n*((t-a)/T))) • amps' j).smulRight
          (PulseTaylor.angularD r b (D j)
            (packetStretch (fun k => amps k x) T ((t-a)/T) j))) x := by
  exact (((nonlinearBergerWord_hasFDerivAt r b D amps amps' ha T ((t-a)/T) hne).sub_const b).const_smul (α t)).const_add (history t)


-- @@ L671-684 verbatim
lemma insertWord_fderiv_ray_selected (history : ℝ → E) (α : ℝ → ℝ)
    (r : ℝ) (b : E) (D : Fin n → E) (amps : Fin n → H → ℝ)
    (amps' : Fin n → H →L[ℝ] ℝ) {x : H}
    (ha : ∀ j,HasFDerivAt (amps j) (amps' j) x) (a T t : ℝ)
    (hne : ∀ j,packetStretch (fun k => amps k x) T ((t-a)/T) j ≠ 0)
    (d : Fin n) (hd : ∀ j,j ≠ d → bump j (duration n*((t-a)/T))=0) (v : H) :
    fderiv ℝ (fun y => insertWord history α r b D (fun j => amps j y) a T t) x v=
      (T⁻¹*unitPacketScalar (fun j => amps' j v) ((t-a)/T)) •
        (α t • PulseTaylor.angularD r b (D d)
          (1+T⁻¹*unitPacketScalar (fun j => amps j x) ((t-a)/T))) := by
  rw [(insertWord_hasFDerivAt history α r b D amps amps' ha a T t hne).fderiv]
  simp only [smul_apply]
  rw [nonlinearBergerWord_jet_selected r b D (fun j => amps j x) amps' T ((t-a)/T) d hd v]
  exact smul_comm _ _ _


-- @@ L686-686 verbatim
end HarmonicCounterexample.FiniteControl.SmoothWord


-- @@ L688-688 verbatim
end


-- @@ L690-690 verbatim
noncomputable section

-- @@ L691-691 verbatim
open Filter MeasureTheory

-- @@ L692-692 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L693-693 verbatim
open scoped Topology

-- @@ L694-694 verbatim
open scoped Topology

-- @@ L695-695 verbatim
open scoped Topology BigOperators ContDiff InnerProductSpace

-- @@ L696-696 verbatim
open Filter MeasureTheory Set

-- @@ L697-697 verbatim
open Set

-- @@ L698-698 verbatim
open scoped Matrix.Norms.Frobenius

-- @@ L699-699 verbatim
open MeasureTheory Set

-- @@ L700-700 verbatim
open scoped Matrix.Norms.Frobenius


-- @@ L702-702 verbatim
namespace HarmonicCounterexample.LinearODE

-- @@ L703-704 verbatim
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

-- @@ L705-705 verbatim
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup

-- @@ L706-706 verbatim
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace


-- @@ L708-726 verbatim
lemma block_parameter_jet_exists {A : H → ℝ → E →L[ℝ] E}
    {A' : H →L[ℝ] E →L[ℝ] E} {x : H} (b : ℝ → ℝ) (t : ℝ)
    (hA : HasFDerivAt (fun q => A q t) A' x) :
    ∃ K : H →L[ℝ] (E×E →L[ℝ] E×E),
      HasFDerivAt (fun q => block (A q) b t) K x ∧
      ∀ h w,K h w=(0,A' h w.1) := by
  have hi := hA.clm_comp (hasFDerivAt_const (ContinuousLinearMap.fst ℝ E E) x)
  have hh := hi.sub_const (b t • ContinuousLinearMap.snd ℝ E E)
  have hj := (hasFDerivAt_const (ContinuousLinearMap.inr ℝ E E) x).clm_comp hh
  have hk := hj.const_add ((ContinuousLinearMap.inl ℝ E E).comp (ContinuousLinearMap.snd ℝ E E))
  have he : (fun q => block (A q) b t) =
      (fun q => (ContinuousLinearMap.inl ℝ E E).comp (ContinuousLinearMap.snd ℝ E E) +
        (ContinuousLinearMap.inr ℝ E E).comp
          ((A q t).comp (ContinuousLinearMap.fst ℝ E E) - b t • ContinuousLinearMap.snd ℝ E E)) :=
    funext fun q => block_eq (A q) b t
  rw [← he] at hk
  refine ⟨_,hk,?_⟩
  intro h w
  simp [ContinuousLinearMap.compL_apply]


-- @@ L728-728 verbatim
end HarmonicCounterexample.LinearODE


-- @@ L730-730 verbatim
end


-- @@ L732-732 verbatim
noncomputable section

-- @@ L733-733 verbatim
open Filter MeasureTheory

-- @@ L734-734 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L735-735 verbatim
open scoped Topology

-- @@ L736-736 verbatim
open scoped Topology

-- @@ L737-737 verbatim
open scoped Topology BigOperators ContDiff InnerProductSpace

-- @@ L738-738 verbatim
open Filter MeasureTheory Set

-- @@ L739-739 verbatim
open Set

-- @@ L740-740 verbatim
open scoped Matrix.Norms.Frobenius

-- @@ L741-741 verbatim
open MeasureTheory Set

-- @@ L742-742 verbatim
open scoped Matrix.Norms.Frobenius


-- @@ L744-744 verbatim
namespace HarmonicCounterexample.LinearODE

-- @@ L745-746 verbatim
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

-- @@ L747-747 verbatim
local instance : NormedAddCommGroup (E →L[ℝ] E) := ContinuousLinearMap.toNormedAddCommGroup

-- @@ L748-748 verbatim
local instance : NormedSpace ℝ (E →L[ℝ] E) := ContinuousLinearMap.toNormedSpace

-- @@ L749-749 verbatim
local instance : NormedAddCommGroup ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance

-- @@ L750-750 verbatim
local instance : NormedSpace ℝ ((E →L[ℝ] E)×(E →L[ℝ] E)) := inferInstance

-- @@ L751-751 verbatim
local instance : NormedAddCommGroup (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedAddCommGroup

-- @@ L752-752 verbatim
local instance : NormedSpace ℝ (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ] ((E →L[ℝ] E)×(E →L[ℝ] E))) := ContinuousLinearMap.toNormedSpace


-- @@ L754-767 verbatim
/-- The precise phase derivative required by the actual endpoint estimates is
produced from differentiation of the angular coefficient. -/
lemma operator_block_parameter_jet_exists {A : H → ℝ → E →L[ℝ] E}
    {A' : H →L[ℝ] E →L[ℝ] E} {x : H} (b : ℝ → ℝ) (t : ℝ)
    (hA : HasFDerivAt (fun q => A q t) A' x) :
    ∃ K : H →L[ℝ] (((E →L[ℝ] E)×(E →L[ℝ] E)) →L[ℝ]
       ((E →L[ℝ] E)×(E →L[ℝ] E))),
      HasFDerivAt (fun q => block (leftAction (A q)) b t) K x ∧
      ∀ h w,K h w=(0,A' h*w.1) := by
  have hleft : HasFDerivAt (fun q => leftAction (A q) t)
      ((ContinuousLinearMap.mul ℝ (E →L[ℝ] E)).comp A') x :=
    (ContinuousLinearMap.mul ℝ (E →L[ℝ] E)).hasFDerivAt.comp x hA
  obtain ⟨K,hK,he⟩ := block_parameter_jet_exists b t hleft
  exact ⟨K,hK,he⟩


-- @@ L769-769 verbatim
end HarmonicCounterexample.LinearODE


-- @@ L771-771 verbatim
end


-- @@ L773-773 verbatim
noncomputable section

-- @@ L774-774 verbatim
open Filter MeasureTheory

-- @@ L775-775 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L776-776 verbatim
open scoped Topology

-- @@ L777-777 verbatim
open scoped Topology

-- @@ L778-778 verbatim
open scoped Topology BigOperators ContDiff InnerProductSpace

-- @@ L779-779 verbatim
open Filter MeasureTheory Set

-- @@ L780-780 verbatim
open Set

-- @@ L781-781 verbatim
open scoped Matrix.Norms.Frobenius

-- @@ L782-782 verbatim
open MeasureTheory Set

-- @@ L783-783 verbatim
open scoped Matrix.Norms.Frobenius


-- @@ L785-785 verbatim
namespace HarmonicCounterexample.PulseTaylor

-- @@ L786-786 verbatim
open scoped ContDiff

-- @@ L787-787 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


-- @@ L789-794 verbatim
lemma angularD_comp_smooth (r : ℝ) (b D : E) {q : ℝ → ℝ}
    (hq : ContDiff ℝ ∞ q) (hne : ∀ t,q t ≠ 0) :
    ContDiff ℝ ∞ (fun t => angularD r b D (q t)) := by
  exact ((contDiff_const.mul (hq.rpow_const_of_ne hne)).smul contDiff_const).add
    (((contDiff_const.mul (hq.rpow_const_of_ne hne)).sub
      (contDiff_const.mul (hq.rpow_const_of_ne hne))).smul contDiff_const)


-- @@ L796-796 verbatim
end HarmonicCounterexample.PulseTaylor


-- @@ L798-798 verbatim
end


-- @@ L800-800 verbatim
noncomputable section

-- @@ L801-801 verbatim
open Filter MeasureTheory

-- @@ L802-802 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L803-803 verbatim
open scoped Topology

-- @@ L804-804 verbatim
open scoped Topology

-- @@ L805-805 verbatim
open scoped Topology BigOperators ContDiff InnerProductSpace

-- @@ L806-806 verbatim
open Filter MeasureTheory Set

-- @@ L807-807 verbatim
open Set

-- @@ L808-808 verbatim
open scoped Matrix.Norms.Frobenius

-- @@ L809-809 verbatim
open MeasureTheory Set

-- @@ L810-810 verbatim
open scoped Matrix.Norms.Frobenius


-- @@ L812-812 verbatim
namespace HarmonicCounterexample.FiniteControl.SmoothWord

-- @@ L813-813 verbatim
open scoped BigOperators ContDiff

-- @@ L814-815 verbatim
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}


-- @@ L817-829 verbatim
/-- The actual full coefficient jet is smooth in time, including the round
collars where the discrete angular selector changes. -/
lemma nonlinearBergerWord_jet_smooth (r : ℝ) (b : E) (D : Fin n → E)
    (amps : Fin n → ℝ) (amps' : Fin n → H →L[ℝ] ℝ) (T : ℝ)
    (hne : ∀ j t,packetStretch amps T t j ≠ 0) :
    ContDiff ℝ ∞ (fun t => ∑ j : Fin n,
      ((T⁻¹*duration n*bump j (duration n*t)) • amps' j).smulRight
        (PulseTaylor.angularD r b (D j) (packetStretch amps T t j))) := by
  apply ContDiff.sum
  intro j _
  apply ContDiff.smulRight
  · exact (contDiff_const.mul ((bump_smooth j).comp (contDiff_const.mul contDiff_id))).smul contDiff_const
  · exact PulseTaylor.angularD_comp_smooth r b (D j) (packetStretch_smooth amps T j) (hne j)


-- @@ L831-848 verbatim
lemma insertWord_actual_jet_smooth (history : ℝ → E) (α : ℝ → ℝ)
    (hα : ContDiff ℝ ∞ α) (r : ℝ) (b : E) (D : Fin n → E)
    (amps : Fin n → H → ℝ) (amps' : Fin n → H →L[ℝ] ℝ) {x : H}
    (ha : ∀ j,HasFDerivAt (amps j) (amps' j) x) (a T : ℝ)
    (hne : ∀ j t,packetStretch (fun k => amps k x) T t j ≠ 0) :
    ContDiff ℝ ∞ (fun t => fderiv ℝ
      (fun y => insertWord history α r b D (fun j => amps j y) a T t) x) := by
  have he : (fun t => fderiv ℝ
      (fun y => insertWord history α r b D (fun j => amps j y) a T t) x)=
      (fun t => α t • ∑ j : Fin n,
        ((T⁻¹*duration n*bump j (duration n*((t-a)/T))) • amps' j).smulRight
          (PulseTaylor.angularD r b (D j)
            (packetStretch (fun k => amps k x) T ((t-a)/T) j))) := by
    funext t
    exact (insertWord_hasFDerivAt history α r b D amps amps' ha a T t (fun j => hne j _)).fderiv
  rw [he]
  exact hα.smul ((nonlinearBergerWord_jet_smooth r b D (fun k => amps k x) amps' T hne).comp
    ((contDiff_id.sub contDiff_const).div_const T))


-- @@ L850-850 verbatim
end HarmonicCounterexample.FiniteControl.SmoothWord


-- @@ L852-852 verbatim
end


-- @@ L854-854 verbatim
noncomputable section

-- @@ L855-855 verbatim
open Filter MeasureTheory

-- @@ L856-856 verbatim
open scoped BigOperators Topology ENNReal ContDiff

-- @@ L857-857 verbatim
open scoped Topology

-- @@ L858-858 verbatim
open scoped Topology

-- @@ L859-859 verbatim
open scoped Topology BigOperators ContDiff InnerProductSpace

-- @@ L860-860 verbatim
open Filter MeasureTheory Set

-- @@ L861-861 verbatim
open Set

-- @@ L862-862 verbatim
open scoped Matrix.Norms.Frobenius

-- @@ L863-863 verbatim
open MeasureTheory Set

-- @@ L864-864 verbatim
open scoped Matrix.Norms.Frobenius


-- @@ L866-866 verbatim
namespace HarmonicCounterexample.FiniteControl.SmoothWord

-- @@ L867-867 verbatim
open Set

-- @@ L868-868 verbatim
open scoped ContDiff

-- @@ L869-870 verbatim
variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] {n : ℕ}


-- @@ L872-881 verbatim
lemma insertWord_jet_after_zero (history : ℝ → E) (α : ℝ → ℝ)
    (r : ℝ) (b : E) (D : Fin n → E) (amps : H → Fin n → ℝ)
    (a T t : ℝ) (hT : 0 < T) (ht : a+T ≤ t) (x : H) :
    fderiv ℝ (fun y => insertWord history α r b D (amps y) a T t) x=0 := by
  have he : (fun y => insertWord history α r b D (amps y) a T t)=
      (fun _ : H => history t) := by
    funext y
    exact insertWord_after history α r b D (amps y) a T t hT ht
  rw [he]
  exact (hasFDerivAt_const (history t) x).fderiv


-- @@ L883-911 verbatim
/-- A genuine global-in-time bound for the actual parameter jet. The bound
is selected before the incoming coefficient history, since that history does
not vary with the current control parameters. -/
theorem insertWord_actual_jet_bound (α : ℝ → ℝ) (hα : ContDiff ℝ ∞ α)
    (r : ℝ) (b : E) (D : Fin n → E) (amps : Fin n → H → ℝ)
    (amps' : Fin n → H →L[ℝ] ℝ) {x : H}
    (ha : ∀ j,HasFDerivAt (amps j) (amps' j) x) (a T : ℝ) (hT : 0 < T)
    (hne : ∀ j t,packetStretch (fun k => amps k x) T t j ≠ 0) :
    ∃ M : ℝ,0 ≤ M ∧ ∀ (history : ℝ → E) (t : ℝ),
      ‖fderiv ℝ (fun y => insertWord history α r b D (fun j => amps j y) a T t) x‖ ≤ M := by
  have hf := (insertWord_actual_jet_smooth (fun _ => (0:E)) α hα r b D amps amps' ha a T hne).continuous
  obtain ⟨M,hM⟩ := (isCompact_Icc (a := a) (b := a+T)).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max M 0,le_max_right _ _,?_⟩
  intro history t
  by_cases ht : t ∈ Icc a (a+T)
  · have he : fderiv ℝ (fun y => insertWord history α r b D (fun j => amps j y) a T t) x=
        fderiv ℝ (fun y => insertWord (fun _ => (0:E)) α r b D (fun j => amps j y) a T t) x := by
      rw [(insertWord_hasFDerivAt history α r b D amps amps' ha a T t (fun j => hne j _)).fderiv,
        (insertWord_hasFDerivAt (fun _ => (0:E)) α r b D amps amps' ha a T t (fun j => hne j _)).fderiv]
    rw [he]
    exact (hM t ht).trans (le_max_left _ _)
  · by_cases hbefore : t ≤ a
    · rw [insertWord_jet_history_zero history α r b D (fun y j => amps j y) a T t hT hbefore x,norm_zero]
      exact le_max_right _ _
    · have hafter : a+T ≤ t := by
        by_contra h
        exact ht ⟨(lt_of_not_ge hbefore).le,(lt_of_not_ge h).le⟩
      rw [insertWord_jet_after_zero history α r b D (fun y j => amps j y) a T t hT hafter x,norm_zero]
      exact le_max_right _ _


-- @@ L913-913 verbatim
end HarmonicCounterexample.FiniteControl.SmoothWord


-- @@ L915-915 verbatim
end


-- @@ L917-917 verbatim
end OAI
