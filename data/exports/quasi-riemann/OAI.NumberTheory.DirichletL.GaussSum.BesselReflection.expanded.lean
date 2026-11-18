import OAI.NumberTheory.DirichletL.Eisenstein.SourceMellinInversion
import OAI.NumberTheory.DirichletL.Mellin.VerticalContourShift


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
open scoped BigOperators

-- @@ L9-9 verbatim
open MulChar AddChar

-- @@ L10-10 verbatim
open scoped BigOperators

-- @@ L11-11 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L12-12 verbatim
open scoped Topology

-- @@ L13-13 verbatim
open MeasureTheory Real

-- @@ L14-14 verbatim
open scoped FourierTransform SchwartzMap

-- @@ L15-15 verbatim
open Finset Complex

-- @@ L16-16 verbatim
open scoped Classical

-- @@ L17-17 verbatim
open scoped Classical

-- @@ L18-18 verbatim
open Filter Real Asymptotics

-- @@ L19-19 verbatim
open ActualEisensteinCubic

-- @@ L20-20 verbatim
open Filter

-- @@ L21-21 verbatim
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount

-- @@ L22-22 verbatim
open ActualEisensteinCubic ShortDraftLatticeCount

-- @@ L23-23 verbatim
open Filter

-- @@ L24-24 verbatim
open scoped Topology

-- @@ L25-25 verbatim
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

-- @@ L26-26 verbatim
open MulChar AddChar

-- @@ L27-27 verbatim
open Filter Asymptotics

-- @@ L28-28 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L29-29 verbatim
open Filter

-- @@ L30-30 verbatim
open MulChar AddChar

-- @@ L31-31 verbatim
open MulChar AddChar

-- @@ L32-32 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L33-33 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L34-34 verbatim
open scoped Topology

-- @@ L35-35 verbatim
open Filter Asymptotics

-- @@ L36-36 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L37-37 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L38-38 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L39-39 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L40-40 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L41-41 verbatim
open Filter Asymptotics

-- @@ L42-42 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L43-43 verbatim
open scoped Topology

-- @@ L44-44 verbatim
open Filter Asymptotics Ideal NumberField

-- @@ L45-45 verbatim
open Filter

-- @@ L46-46 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L47-47 verbatim
open scoped Topology

-- @@ L48-48 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L49-49 verbatim
open scoped Topology

-- @@ L50-50 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L51-51 verbatim
open scoped Topology

-- @@ L52-52 verbatim
open MeasureTheory Real

-- @@ L53-53 verbatim
open scoped ContDiff FourierTransform SchwartzMap

-- @@ L54-54 verbatim
open scoped BigOperators Classical

-- @@ L55-55 verbatim
open scoped BigOperators Classical

-- @@ L56-56 verbatim
open scoped BigOperators Classical

-- @@ L57-57 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L58-58 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L59-59 verbatim
open scoped BigOperators Classical

-- @@ L60-60 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L61-61 verbatim
open scoped BigOperators Classical

-- @@ L62-62 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L63-63 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L64-64 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L65-65 verbatim
open scoped BigOperators Classical

-- @@ L66-66 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L67-67 verbatim
open MeasureTheory Set

-- @@ L68-68 verbatim
open scoped BigOperators

-- @@ L69-69 verbatim
open scoped BigOperators Classical

-- @@ L70-70 verbatim
open scoped BigOperators Classical

-- @@ L71-71 verbatim
open ActualEisensteinCubic UniqueFactorizationMonoid

-- @@ L72-72 verbatim
open scoped BigOperators

-- @@ L73-73 verbatim
open scoped BigOperators

-- @@ L74-74 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L75-75 verbatim
open scoped BigOperators Classical


-- @@ L77-77 verbatim
namespace CompletedGauss

-- @@ L78-78 verbatim
open Filter MeasureTheory

-- @@ L79-79 verbatim
open scoped Classical BigOperators Topology


-- @@ L81-81 verbatim
section

-- @@ L82-82 verbatim
open CubicEisenstein


-- @@ L84-85 verbatim
def completedBesselProfile (Ψ : ActualEisensteinCubic.O→*ℂ) (q : ℝ) : ℝ→ℂ :=
  radialBesselProfile completedMellinLength (completedMellinCoefficient Ψ) q


-- @@ L87-89 verbatim
def besselMellinFactor (q : ℝ) (s : ℂ) : ℂ :=
  ((2:ℂ)^(2*s-1)*Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))/
    ((4*Real.pi*q:ℝ):ℂ)^(2*s+1)


-- @@ L91-93 verbatim
def inverseBesselMellinFactor (q : ℝ) (s : ℂ) : ℂ :=
  ((4*Real.pi*q:ℝ):ℂ)^(2*s+1)*(2:ℂ)^(1-2*s)*
    (Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))⁻¹


-- @@ L95-107 verbatim
theorem completedBesselProfile_mellin (Ψ : ActualEisensteinCubic.O→*ℂ)
    (hΨ : ∀a,‖Ψ a‖≤1) (q : ℝ) (hq : 0<q) (s : ℂ) (hs : 3/2<s.re) :
    mellin (completedBesselProfile Ψ q) (2*s)=
      besselMellinFactor q s*completedDirichletSeries Ψ s := by
  let : Countable ActualEisensteinCubic.O :=
    ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : Countable (Ideal ActualEisensteinCubic.O) :=
    ConcretePrimeRowBridge.idealGenerator_injective.countable
  have hsum := completedMellinCoefficient_summable Ψ hΨ (s.re-1/2) (by linarith)
  have he : -(s.re-1/2)=1/2-s.re := by ring
  simp only [he] at hsum
  exact radialBesselProfile_mellin completedMellinLength completedMellinLength_pos
    (completedMellinCoefficient Ψ) q hq s (by linarith) hsum


-- @@ L109-125 verbatim
lemma inverseBesselMellinFactor_mul (q : ℝ) (hq : 0<q) (s : ℂ)
    (hs : -(1/3)<s.re) :
    inverseBesselMellinFactor q s*besselMellinFactor q s=1 := by
  have hq0 : (((4*Real.pi*q:ℝ):ℂ)^(2*s+1))≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (Complex.ofReal_ne_zero.mpr (by positivity)))
  have h1 : Complex.Gamma (s+1/3)≠0 := Complex.Gamma_ne_zero_of_re_pos (by simp;linarith)
  have h2 : Complex.Gamma (s+2/3)≠0 := Complex.Gamma_ne_zero_of_re_pos (by simp;linarith)
  have hp : (2:ℂ)^(1-2*s)*(2:ℂ)^(2*s-1)=1 := by
    rw [←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    simp
  unfold inverseBesselMellinFactor besselMellinFactor
  calc
    _=((((4*Real.pi*q:ℝ):ℂ)^(2*s+1))/(((4*Real.pi*q:ℝ):ℂ)^(2*s+1)))*
        ((2:ℂ)^(1-2*s)*(2:ℂ)^(2*s-1))*
        ((Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))⁻¹*
          (Complex.Gamma (s+1/3)*Complex.Gamma (s+2/3))) := by ring
    _=1 := by rw [div_self hq0,hp,inv_mul_cancel₀ (mul_ne_zero h1 h2)];ring


-- @@ L127-132 verbatim
theorem completedDirichletSeries_eq_mellin (Ψ : ActualEisensteinCubic.O→*ℂ)
    (hΨ : ∀a,‖Ψ a‖≤1) (q : ℝ) (hq : 0<q) (s : ℂ) (hs : 3/2<s.re) :
    completedDirichletSeries Ψ s=
      inverseBesselMellinFactor q s*mellin (completedBesselProfile Ψ q) (2*s) := by
  rw [completedBesselProfile_mellin Ψ hΨ q hq s hs,←mul_assoc,
    inverseBesselMellinFactor_mul q hq s (by linarith),one_mul]


-- @@ L134-134 verbatim
end


-- @@ L136-150 verbatim
theorem inverseBesselMellinFactor_differentiable (q : ℝ) (hq : 0<q) :
    Differentiable ℂ (inverseBesselMellinFactor q) := by
  have hq0 : ((4*Real.pi*q:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (by positivity)
  have h1 : Differentiable ℂ (fun s : ℂ=>((4*Real.pi*q:ℝ):ℂ)^(2*s+1)) :=
    (show Differentiable ℂ (fun s : ℂ=>2*s+1) from by fun_prop).const_cpow (Or.inl hq0)
  have h2 : Differentiable ℂ (fun s : ℂ=>(2:ℂ)^(1-2*s)) :=
    (show Differentiable ℂ (fun s : ℂ=>1-2*s) from by fun_prop).const_cpow
      (Or.inl (by norm_num : (2:ℂ)≠0))
  have h3 : Differentiable ℂ (fun s : ℂ=>(Complex.Gamma (s+1/3))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (by fun_prop)
  have h4 : Differentiable ℂ (fun s : ℂ=>(Complex.Gamma (s+2/3))⁻¹) :=
    Complex.differentiable_one_div_Gamma.comp (by fun_prop)
  convert (h1.mul h2).mul (h4.mul h3) using 1
  ext s
  simp only [inverseBesselMellinFactor,Pi.mul_apply,mul_inv_rev]


-- @@ L152-181 verbatim
theorem inverseBesselMellinFactor_strip_bound (q : ℝ) (hq : 0<q) (a b : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀s : ℂ,s.re∈Set.Icc a b →
      ‖inverseBesselMellinFactor q s‖≤C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨Cg,hCg,hg⟩ := CubicGammaExponential.inverse_cubic_Gamma_pair_strip_bound a b
  let Ca := (4*Real.pi*q)^(2*a+1)+(4*Real.pi*q)^(2*b+1)
  let Cb := (2:ℝ)^(1-2*b)+(2:ℝ)^(1-2*a)
  have hqpos : 0<4*Real.pi*q := by positivity
  have hCa : 0≤Ca := by dsimp [Ca];positivity
  have hCb : 0≤Cb := by dsimp [Cb];positivity
  refine ⟨Ca*Cb*Cg,by positivity,?_⟩
  intro s hs
  have hp1 : ‖((4*Real.pi*q:ℝ):ℂ)^(2*s+1)‖≤Ca := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hqpos]
    have hr : (2*s+1).re=2*s.re+1 := by simp
    rw [hr]
    exact VerticalContourShift.rpow_between_endpoints _ _ _ _ hqpos
      (by linarith [hs.1]) (by linarith [hs.2])
  have hp2 : ‖(2:ℂ)^(1-2*s)‖≤Cb := by
    change ‖((2:ℝ):ℂ)^(1-2*s)‖≤Cb
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : 0<(2:ℝ))]
    have hr : (1-2*s).re=1-2*s.re := by simp
    rw [hr]
    exact VerticalContourShift.rpow_between_endpoints _ _ _ _ (by norm_num)
      (by linarith [hs.2]) (by linarith [hs.1])
  simp only [inverseBesselMellinFactor,norm_mul]
  calc
    _≤(Ca*Cb)*(Cg*Real.exp (2*Real.pi*|s.im|)) :=
      mul_le_mul (mul_le_mul hp1 hp2 (norm_nonneg _) hCa) (hg s hs)
        (norm_nonneg _) (mul_nonneg hCa hCb)
    _=_ := by ring


-- @@ L183-184 verbatim
def continuedBesselDirichlet (F : ℝ→ℂ) (q : ℝ) (s : ℂ) : ℂ :=
  inverseBesselMellinFactor q s*mellin F (2*s)


-- @@ L186-189 verbatim
theorem continuedBesselDirichlet_differentiable (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (hF : Differentiable ℂ (mellin F)) :
    Differentiable ℂ (continuedBesselDirichlet F q) :=
  (inverseBesselMellinFactor_differentiable q hq).mul (hF.comp (by fun_prop))


-- @@ L191-206 verbatim
theorem continuedBesselDirichlet_strip_bound (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (a b : ℝ) (ha : MellinConvergent F ((2*a:ℝ):ℂ))
    (hb : MellinConvergent F ((2*b:ℝ):ℂ)) :
    ∃C : ℝ,0≤C ∧ ∀s : ℂ,s.re∈Set.Icc a b →
      ‖continuedBesselDirichlet F q s‖≤C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨Ci,hCi,hi⟩ := inverseBesselMellinFactor_strip_bound q hq a b
  obtain ⟨Cm,hCm,hm⟩ := VerticalContourShift.mellin_uniform_strip_bound F (2*a) (2*b) ha hb
  refine ⟨Ci*Cm,mul_nonneg hCi hCm,?_⟩
  intro s hs
  have hms : ‖mellin F (2*s)‖≤Cm := hm (2*s)
    (by simp;linarith [hs.1]) (by simp;linarith [hs.2])
  rw [continuedBesselDirichlet,norm_mul]
  calc
    _≤(Ci*Real.exp (2*Real.pi*|s.im|))*Cm :=
      mul_le_mul (hi s hs) hms (norm_nonneg _) (mul_nonneg hCi (Real.exp_pos _).le)
    _=_ := by ring


-- @@ L208-212 verbatim
theorem continuedBesselDirichlet_eq_initial (Ψ : ActualEisensteinCubic.O→*ℂ)
    (hΨ : ∀a,‖Ψ a‖≤1) (q : ℝ) (hq : 0<q) (s : ℂ) (hs : 3/2<s.re) :
    continuedBesselDirichlet (completedBesselProfile Ψ q) q s=
      completedDirichletSeries Ψ s :=
  (completedDirichletSeries_eq_mellin Ψ hΨ q hq s hs).symm


-- @@ L214-214 verbatim
end CompletedGauss


-- @@ L216-216 verbatim
namespace CubicEisenstein

-- @@ L217-217 verbatim
open Filter MeasureTheory Asymptotics

-- @@ L218-218 verbatim
open scoped BigOperators Classical Topology MatrixGroups


-- @@ L220-220 verbatim
section

-- @@ L221-221 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L223-239 verbatim
lemma ramifiedSource_horizontal_hasDerivAt (side:Bool) (v:ℝ) (hv:0<v)
    (z direction:ℂ) (t:ℝ) :
    HasDerivAt (fun x:ℝ => ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
      (upperPoint (z+(x:ℂ)*direction) v hv))
      (∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3)
        (z/3+(t:ℂ)*(direction/3)) (direction/3)) t := by
  have he : (fun x:ℝ => ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
      (upperPoint (z+(x:ℂ)*direction) v hv)) =
      (fun x:ℝ => (ramifiedBesselCoefficients side).series
        (v/3,z/3+(x:ℂ)*(direction/3))) := by
    funext x
    rw [ramifiedSource_eq_series]
    congr 2
    ring
  rw [he]
  exact (ramifiedBesselCoefficients side).series_horizontal_hasDerivAt
    (v/3) (by positivity) (z/3) (direction/3) t


-- @@ L241-271 verbatim
lemma ramifiedSource_wirtingerBar_cusp_decay (side:Bool) (a:ℝ) (ha:0<a) :
    ∃C:ℝ,0≤C ∧ ∀(v:ℝ)(hv:0<v)(z:ℂ),a≤v →
      ‖horizontalWirtingerBar (fun w => ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
        (upperPoint w v hv)) z‖ ≤ C*Real.exp (-(residualCuspDecayRate/3)*v) := by
  obtain ⟨C1,hC1,h1b⟩ := (ramifiedBesselCoefficients side).directionalSeries_cusp_decay
    (a/3) (by positivity) (1/3)
  obtain ⟨CI,hCI,hIb⟩ := (ramifiedBesselCoefficients side).directionalSeries_cusp_decay
    (a/3) (by positivity) (Complex.I/3)
  refine ⟨(C1+CI)/2,by positivity,?_⟩
  intro v hv z hav
  have h1 := (ramifiedSource_horizontal_hasDerivAt side v hv z 1 0).deriv
  have hI := (ramifiedSource_horizontal_hasDerivAt side v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  have he : -residualCuspDecayRate*(v/3)=-(residualCuspDecayRate/3)*v := by ring
  have hb1 := h1b (v/3) (z/3) (by linarith)
  have hbI := hIb (v/3) (z/3) (by linarith)
  rw [he] at hb1 hbI
  rw [horizontalWirtingerBar,h1,hI,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1/2:ℝ)*(‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (1/3)‖+
      ‖Complex.I*(∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (Complex.I/3))‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by norm_num)
    _ = (1/2:ℝ)*(‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (1/3)‖+
      ‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (Complex.I/3)‖) := by
        rw [norm_mul,Complex.norm_I,one_mul]
    _ ≤ (1/2:ℝ)*(C1*Real.exp (-(residualCuspDecayRate/3)*v)+
      CI*Real.exp (-(residualCuspDecayRate/3)*v)) :=
        mul_le_mul_of_nonneg_left (add_le_add hb1 hbI) (by norm_num)
    _ = _ := by ring


-- @@ L273-303 verbatim
lemma ramifiedSource_wirtingerZ_cusp_decay (side:Bool) (a:ℝ) (ha:0<a) :
    ∃C:ℝ,0≤C ∧ ∀(v:ℝ)(hv:0<v)(z:ℂ),a≤v →
      ‖horizontalWirtingerZ (fun w => ramifiedSourceFunction (ramifiedCuspRoot side:Eis)
        (upperPoint w v hv)) z‖ ≤ C*Real.exp (-(residualCuspDecayRate/3)*v) := by
  obtain ⟨C1,hC1,h1b⟩ := (ramifiedBesselCoefficients side).directionalSeries_cusp_decay
    (a/3) (by positivity) (1/3)
  obtain ⟨CI,hCI,hIb⟩ := (ramifiedBesselCoefficients side).directionalSeries_cusp_decay
    (a/3) (by positivity) (Complex.I/3)
  refine ⟨(C1+CI)/2,by positivity,?_⟩
  intro v hv z hav
  have h1 := (ramifiedSource_horizontal_hasDerivAt side v hv z 1 0).deriv
  have hI := (ramifiedSource_horizontal_hasDerivAt side v hv z Complex.I 0).deriv
  simp only [mul_one,Complex.ofReal_zero,zero_mul,add_zero] at h1 hI
  have he : -residualCuspDecayRate*(v/3)=-(residualCuspDecayRate/3)*v := by ring
  have hb1 := h1b (v/3) (z/3) (by linarith)
  have hbI := hIb (v/3) (z/3) (by linarith)
  rw [he] at hb1 hbI
  rw [horizontalWirtingerZ,h1,hI,norm_mul]
  have hhalf : ‖(1/2:ℂ)‖=(1/2:ℝ) := by norm_num
  rw [hhalf]
  calc
    _ ≤ (1/2:ℝ)*(‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (1/3)‖+
      ‖Complex.I*(∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (Complex.I/3))‖) :=
        mul_le_mul_of_nonneg_left (norm_sub_le _ _) (by norm_num)
    _ = (1/2:ℝ)*(‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (1/3)‖+
      ‖∑'h:Eis,(ramifiedBesselCoefficients side).directionalTerm h (v/3) (z/3) (Complex.I/3)‖) := by
        rw [norm_mul,Complex.norm_I,one_mul]
    _ ≤ (1/2:ℝ)*(C1*Real.exp (-(residualCuspDecayRate/3)*v)+
      CI*Real.exp (-(residualCuspDecayRate/3)*v)) :=
        mul_le_mul_of_nonneg_left (add_le_add hb1 hbI) (by norm_num)
    _ = _ := by ring


-- @@ L305-317 verbatim
lemma ramifiedConjugate_barProfile_isBigO (side:Bool) (z:ℂ) :
    cuspBarProfile (fun w => cubicSourceConjugateFunction
      (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis)) • w)) z
      =O[atTop] (fun v:ℝ => Real.exp (-(residualCuspDecayRate/3)*v)) := by
  obtain ⟨C,hC,hb⟩ := ramifiedSource_wirtingerZ_cusp_decay side 1 (by norm_num)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with v hv
  have hvp:0<v := lt_of_lt_of_le (by norm_num) hv
  rw [cuspBarProfile_positive _ _ _ hvp,Real.norm_of_nonneg (Real.exp_pos _).le]
  change ‖horizontalWirtingerBar (fun w => star (ramifiedSourceFunction
    (ramifiedCuspRoot side:Eis) (upperPoint w v hvp))) z‖ ≤ _
  rw [horizontalWirtingerBar_star,norm_star]
  exact hb v hvp z hv


-- @@ L319-331 verbatim
lemma ramifiedConjugate_zProfile_isBigO (side:Bool) (z:ℂ) :
    cuspZProfile (fun w => cubicSourceConjugateFunction
      (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis)) • w)) z
      =O[atTop] (fun v:ℝ => Real.exp (-(residualCuspDecayRate/3)*v)) := by
  obtain ⟨C,hC,hb⟩ := ramifiedSource_wirtingerBar_cusp_decay side 1 (by norm_num)
  apply Asymptotics.IsBigO.of_bound C
  filter_upwards [eventually_ge_atTop (1:ℝ)] with v hv
  have hvp:0<v := lt_of_lt_of_le (by norm_num) hv
  rw [cuspZProfile_positive _ _ _ hvp,Real.norm_of_nonneg (Real.exp_pos _).le]
  change ‖horizontalWirtingerZ (fun w => star (ramifiedSourceFunction
    (ramifiedCuspRoot side:Eis) (upperPoint w v hvp))) z‖ ≤ _
  rw [horizontalWirtingerZ_star,norm_star]
  exact hb v hvp z hv


-- @@ L333-333 verbatim
end


-- @@ L335-335 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L337-341 verbatim
lemma reflectedCuspProfile_eq_inv_square (A:ℂ) (Q:ℝ) (g:ℝ→ℂ) (v:ℝ) :
    reflectedCuspProfile A Q g v=A/(v:ℂ)^2*g ((Q*v)⁻¹) := by
  unfold reflectedCuspProfile
  rw [Complex.cpow_neg,Complex.cpow_ofNat]
  ring


-- @@ L343-353 verbatim
lemma reflectedCuspProfile_reverse (A:ℂ) (hA:A≠0) (Q:ℝ) (hQ:0<Q)
    (f g:ℝ→ℂ) (hfg:∀v:ℝ,0<v→f v=reflectedCuspProfile A Q g v)
    (v:ℝ) (hv:0<v) :
    g v=reflectedCuspProfile (A⁻¹/(Q:ℂ)^2) Q f v := by
  have he:=hfg (Q*v)⁻¹ (by positivity)
  have harg:(Q*(Q*v)⁻¹)⁻¹=v := by field_simp
  rw [reflectedCuspProfile_eq_inv_square,harg] at he
  rw [reflectedCuspProfile_eq_inv_square,he,Complex.ofReal_inv,Complex.ofReal_mul]
  have hcQ:(Q:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hQ.ne'
  have hcv:(v:ℂ)≠0:=Complex.ofReal_ne_zero.mpr hv.ne'
  field_simp


-- @@ L355-367 verbatim
theorem cusp_mellin_entire_both (f g:ℝ→ℂ) (A:ℂ) (hA:A≠0)
    (Q decayF decayG:ℝ) (hQ:0<Q) (hdecayF:0<decayF) (hdecayG:0<decayG)
    (hf:ContinuousOn f (Set.Ioi 0)) (hg:ContinuousOn g (Set.Ioi 0))
    (hfbound:f =O[atTop] (fun v:ℝ=>Real.exp (-decayF*v)))
    (hgbound:g =O[atTop] (fun v:ℝ=>Real.exp (-decayG*v)))
    (hfg:∀v:ℝ,0<v→f v=reflectedCuspProfile A Q g v) :
    ((∀s:ℂ,MellinConvergent f s) ∧ Differentiable ℂ (mellin f)) ∧
    ((∀s:ℂ,MellinConvergent g s) ∧ Differentiable ℂ (mellin g)) := by
  constructor
  · exact cusp_mellin_entire f g A Q decayF decayG hQ hdecayF hdecayG
      hf hg hfbound hgbound hfg
  · exact cusp_mellin_entire g f (A⁻¹/(Q:ℂ)^2) Q decayG decayF hQ hdecayG hdecayF
      hg hf hgbound hfbound (reflectedCuspProfile_reverse A hA Q hQ f g hfg)


-- @@ L369-404 verbatim
theorem conjugateSource_ramified_cusp_mellin_entire (side:Bool)
    (G:CubicKubota.levelThree) (g:SL(2,ℂ))
    (hfactor:g=complexMatrix G*integralComplexMatrix
      (lowerCuspMatrix (ramifiedCuspRoot side:Eis))) (hc:g 1 0≠0) :
    ((∀s:ℂ,MellinConvergent
      (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0)) s) ∧
      Differentiable ℂ (mellin (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0)))) ∧
    ((∀s:ℂ,MellinConvergent
      (cuspZProfile (fun w=>cubicSourceConjugateFunction
        (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis)) • w))
        (-g 1 1/g 1 0)) s) ∧
      Differentiable ℂ (mellin
        (cuspZProfile (fun w=>cubicSourceConjugateFunction
          (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis)) • w))
          (-g 1 1/g 1 0)))) := by
  have hchar:CubicKubota.complexCharacter G≠0 := by
    intro hz
    have hn:=CubicKubota.norm_complexCharacter G
    rw [hz,norm_zero] at hn
    norm_num at hn
  have hscalar : -star (CubicKubota.complexCharacter G)/(g 1 0)^2≠0 :=
    div_ne_zero (neg_ne_zero.mpr (star_ne_zero.mpr hchar)) (pow_ne_zero 2 hc)
  exact cusp_mellin_entire_both
    (cuspBarProfile cubicSourceConjugateFunction (g 0 0/g 1 0))
    (cuspZProfile (fun w=>cubicSourceConjugateFunction
      (integralComplexMatrix (lowerCuspMatrix (ramifiedCuspRoot side:Eis)) • w))
      (-g 1 1/g 1 0))
    (-star (CubicKubota.complexCharacter G)/(g 1 0)^2) hscalar (‖g 1 0‖^2)
    residualCuspDecayRate (residualCuspDecayRate/3)
    (sq_pos_of_pos (norm_pos_iff.mpr hc)) residualCuspDecayRate_pos
    (div_pos residualCuspDecayRate_pos (by norm_num))
    (cuspBarProfile_conjugate_continuousOn _)
    (cuspZProfile_conjugate_translate_continuousOn _ _)
    (cuspBarProfile_conjugate_isBigO _)
    (ramifiedConjugate_zProfile_isBigO side _)
    (fun v hv=>cuspBarProfile_conjugate_reflection G g _ hfactor hc v hv)


-- @@ L406-406 verbatim
end CubicEisenstein


-- @@ L408-408 verbatim
open scoped BigOperators Classical


-- @@ L410-410 verbatim
namespace CompletedGauss


-- @@ L412-412 verbatim
section

-- @@ L413-413 verbatim
open UniqueFactorizationMonoid

-- @@ L414-414 verbatim
local notation "Eis" => ActualEisensteinCubic.O


-- @@ L416-441 verbatim
theorem squarefree_cube_decomposition_unique {I J I' J':Ideal Eis}
    (hJ:J≠0) (hJ':J'≠0) (hI:Squarefree I) (hI':Squarefree I')
    (h:I*J^3=I'*J'^3) : I=I' ∧ J=J' := by
  have hf:=congrArg normalizedFactors h
  rw [normalizedFactors_mul hI.ne_zero (pow_ne_zero _ hJ),
    normalizedFactors_mul hI'.ne_zero (pow_ne_zero _ hJ'),
    normalizedFactors_pow,normalizedFactors_pow] at hf
  have hi:=(squarefree_iff_nodup_normalizedFactors hI.ne_zero).mp hI
  have hi':=(squarefree_iff_nodup_normalizedFactors hI'.ne_zero).mp hI'
  have hc (P:Ideal Eis) :
      (normalizedFactors I).count P=(normalizedFactors I').count P ∧
      (normalizedFactors J).count P=(normalizedFactors J').count P := by
    have he:=congrArg (Multiset.count P) hf
    simp only [Multiset.count_add,Multiset.count_nsmul] at he
    have h1:=Multiset.nodup_iff_count_le_one.mp hi P
    have h2:=Multiset.nodup_iff_count_le_one.mp hi' P
    omega
  constructor
  · calc
      I=(normalizedFactors I).prod:=(Ideal.prod_normalizedFactors_eq_self hI.ne_zero).symm
      _=(normalizedFactors I').prod:=congrArg Multiset.prod (Multiset.ext.mpr (fun P=>(hc P).1))
      _=I':=Ideal.prod_normalizedFactors_eq_self hI'.ne_zero
  · calc
      J=(normalizedFactors J).prod:=(Ideal.prod_normalizedFactors_eq_self hJ).symm
      _=(normalizedFactors J').prod:=congrArg Multiset.prod (Multiset.ext.mpr (fun P=>(hc P).2))
      _=J':=Ideal.prod_normalizedFactors_eq_self hJ'


-- @@ L443-467 verbatim
theorem primary_squarefree_cube_eq_iff {I J I' J':Ideal Eis}
    (hI:Squarefree I) (hI':Squarefree I')
    (hgI:primaryGenerator I≠0) (hgJ:primaryGenerator J≠0)
    (hgI':primaryGenerator I'≠0) (hgJ':primaryGenerator J'≠0) :
    primaryGenerator I*(primaryGenerator J)^3=
      primaryGenerator I'*(primaryGenerator J')^3 ↔ I=I' ∧ J=J' := by
  constructor
  · intro h
    have hleft:primaryGenerator (I*J^3)≠0:=by
      rw [primaryGenerator_mul,CubicEisenstein.primaryGenerator_pow]
      exact mul_ne_zero hgI (pow_ne_zero _ hgJ)
    have hright:primaryGenerator (I'*J'^3)≠0:=by
      rw [primaryGenerator_mul,CubicEisenstein.primaryGenerator_pow]
      exact mul_ne_zero hgI' (pow_ne_zero _ hgJ')
    have he:I*J^3=I'*J'^3:=by
      calc
        I*J^3=Ideal.span {primaryGenerator (I*J^3)}:=(primaryGenerator_spec _ hleft).1.symm
        _=Ideal.span {primaryGenerator (I'*J'^3)}:=by
          apply congrArg (fun z:Eis => (Ideal.span {z}:Ideal Eis))
          simpa only [primaryGenerator_mul,CubicEisenstein.primaryGenerator_pow] using h
        _=I'*J'^3:=(primaryGenerator_spec _ hright).1
    exact squarefree_cube_decomposition_unique
      (primaryGenerator_ne_zero_ideal J hgJ) (primaryGenerator_ne_zero_ideal J' hgJ') hI hI' he
  · rintro ⟨rfl,rfl⟩
    rfl


-- @@ L469-477 verbatim
theorem primary_squarefree_cube_injective :
    Function.Injective (fun x:
      {I:Ideal Eis // Squarefree I ∧ primaryGenerator I≠0} ×
      {J:Ideal Eis // primaryGenerator J≠0} =>
        primaryGenerator x.1.val*(primaryGenerator x.2.val)^3) := by
  intro x y he
  have h:= (primary_squarefree_cube_eq_iff x.1.property.1 y.1.property.1
    x.1.property.2 x.2.property y.1.property.2 y.2.property).mp he
  exact Prod.ext (Subtype.ext h.1) (Subtype.ext h.2)


-- @@ L479-479 verbatim
end


-- @@ L481-481 verbatim
open Filter MeasureTheory

-- @@ L482-482 verbatim
open scoped Classical BigOperators Topology ContDiff


-- @@ L484-485 verbatim
def besselSmoothingIntegrand (F : ℝ→ℂ) (q : ℝ) (V : ℝ→ℂ) (X : ℝ) (s : ℂ) : ℂ :=
  mellin V (s-1/2)*(X:ℂ)^(s-1/2)*continuedBesselDirichlet F q s


-- @@ L487-496 verbatim
lemma besselSmoothingIntegrand_differentiable (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (hF : Differentiable ℂ (mellin F)) (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hVs : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) : Differentiable ℂ (besselSmoothingIntegrand F q V X) := by
  have hm := (CubicReflectionKernel.compact_source_mellin_differentiable V a b ha hVs hV).comp
    (show Differentiable ℂ (fun s : ℂ=>s-1/2) from by fun_prop)
  have hp : Differentiable ℂ (fun s : ℂ=>(X:ℂ)^(s-1/2)) :=
    (show Differentiable ℂ (fun s : ℂ=>s-1/2) from by fun_prop).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr hX.ne'))
  exact (hm.mul hp).mul (continuedBesselDirichlet_differentiable F q hq hF)


-- @@ L498-526 verbatim
lemma besselSmoothingIntegrand_strip_bound (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (lo hi : ℝ) (hF : ∀s : ℂ,MellinConvergent F s)
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hVs : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) :
    ∃C : ℝ,0≤C ∧ ∀s : ℂ,s.re∈Set.Icc lo hi →
      ‖besselSmoothingIntegrand F q V X s‖≤C*Real.exp (2*Real.pi*|s.im|) := by
  obtain ⟨Cd,hCd,hd⟩ := continuedBesselDirichlet_strip_bound F q hq lo hi (hF _) (hF _)
  have hVc (s : ℂ) := CubicReflectionKernel.compact_source_mellin_convergent V a b ha hVs hV s
  obtain ⟨Cv,hCv,hv⟩ := VerticalContourShift.mellin_uniform_strip_bound V (lo-1/2) (hi-1/2)
    (hVc _) (hVc _)
  let Cx : ℝ := X^(lo-1/2)+X^(hi-1/2)
  have hCx : 0≤Cx := by dsimp [Cx];positivity
  refine ⟨Cv*Cx*Cd,mul_nonneg (mul_nonneg hCv hCx) hCd,?_⟩
  intro s hs
  have hvb : ‖mellin V (s-1/2)‖≤Cv := hv (s-1/2)
    (by simp;linarith [hs.1]) (by simp;linarith [hs.2])
  have hxb : ‖(X:ℂ)^(s-1/2)‖≤Cx := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
    have he : (s-1/2).re=s.re-1/2 := by simp
    rw [he]
    exact VerticalContourShift.rpow_between_endpoints X (lo-1/2) (hi-1/2) (s.re-1/2) hX
      (by linarith [hs.1]) (by linarith [hs.2])
  rw [besselSmoothingIntegrand,norm_mul,norm_mul]
  calc
    _≤(Cv*Cx)*(Cd*Real.exp (2*Real.pi*|s.im|)) :=
      mul_le_mul (mul_le_mul hvb hxb (norm_nonneg _) hCv) (hd s hs)
        (norm_nonneg _) (mul_nonneg hCv hCx)
    _=_ := by ring


-- @@ L528-548 verbatim
theorem besselSmoothingIntegrand_contour_eq (F : ℝ→ℂ) (q : ℝ) (hq : 0<q)
    (hF : ∀s : ℂ,MellinConvergent F s) (hFe : Differentiable ℂ (mellin F))
    (V : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hVs : Function.support V⊆Set.Icc a b) (hV : ContDiff ℝ ∞ V)
    (X : ℝ) (hX : 0<X) (lo hi : ℝ) (hlh : lo≤hi)
    (hl : Integrable (fun t : ℝ=>besselSmoothingIntegrand F q V X ((lo:ℂ)+t*Complex.I)))
    (hh : Integrable (fun t : ℝ=>besselSmoothingIntegrand F q V X ((hi:ℂ)+t*Complex.I))) :
    (∫t : ℝ,besselSmoothingIntegrand F q V X ((lo:ℂ)+t*Complex.I))=
      ∫t : ℝ,besselSmoothingIntegrand F q V X ((hi:ℂ)+t*Complex.I) := by
  obtain ⟨C,hC,hb⟩ := besselSmoothingIntegrand_strip_bound F q hq lo hi hF V a b ha hVs hV X hX
  apply VerticalContourShift.integral_eq_of_exponential_strip_growth
    (besselSmoothingIntegrand F q V X) lo hi (2*Real.pi) C hlh (by positivity) hC
  · intro z hz1 hz2
    exact (besselSmoothingIntegrand_differentiable F q hq hFe V a b ha hVs hV X hX) z
  · exact hl
  · exact hh
  · intro σ hσ t
    simpa only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
      Complex.I_re,Complex.I_im,zero_mul,mul_zero,sub_zero,add_zero,
      Complex.add_im,Complex.mul_im,mul_one,zero_add] using
      hb ((σ:ℂ)+t*Complex.I) (by simpa using hσ)


-- @@ L550-576 verbatim
theorem completedT_mellin_shift (Ψ : ActualEisensteinCubic.O→*ℂ) (hΨ : ∀a,‖Ψ a‖≤1)
    (q : ℝ) (hq : 0<q)
    (hF : ∀s : ℂ,MellinConvergent (completedBesselProfile Ψ q) s)
    (hFe : Differentiable ℂ (mellin (completedBesselProfile Ψ q)))
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (X : ℝ) (hX : 0<X) (lo : ℝ) (hl : lo≤2)
    (hleft : Integrable (fun t : ℝ=>
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((lo:ℂ)+t*Complex.I))) :
    completedT Ψ W X=(1/(2*Real.pi):ℂ)*∫t : ℝ,
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((lo:ℂ)+t*Complex.I) := by
  have hid (t : ℝ) :
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((2:ℂ)+t*Complex.I)=
      mellin (Vstar W) ((3/2:ℂ)+t*Complex.I)*(X:ℂ)^((3/2:ℂ)+t*Complex.I)*
        completedDirichletSeries Ψ ((2:ℂ)+t*Complex.I) := by
    rw [besselSmoothingIntegrand,continuedBesselDirichlet_eq_initial Ψ hΨ q hq _ (by norm_num)]
    rw [show (2:ℂ)+t*Complex.I-1/2=3/2+t*Complex.I by ring]
  have hr : Integrable (fun t : ℝ=>
      besselSmoothingIntegrand (completedBesselProfile Ψ q) q (Vstar W) X ((2:ℂ)+t*Complex.I)) := by
    simp only [hid]
    exact completedT_initial_mellin_integrable Ψ hΨ W a b ha hWs hW X hX
  have he := besselSmoothingIntegrand_contour_eq (completedBesselProfile Ψ q) q hq hF hFe
    (Vstar W) a b ha (Vstar_support W a b hWs) (Vstar_contDiff W a b ha hWs hW)
    X hX lo 2 hl hleft hr
  rw [he]
  simpa only [Complex.ofReal_ofNat,hid] using
    completedT_initial_mellin Ψ hΨ W a b ha hWs hW X hX


-- @@ L578-578 verbatim
end CompletedGauss


-- @@ L580-580 verbatim
open Filter MeasureTheory

-- @@ L581-581 verbatim
open scoped Classical BigOperators Topology


-- @@ L583-583 verbatim
namespace CompletedGauss

-- @@ L584-584 verbatim
open CubicEisenstein


-- @@ L586-588 verbatim
def besselReflectionFactor (q d : ℝ) (s : ℂ) : ℂ :=
  ((4*Real.pi*q:ℝ):ℂ)^(2*s+1)*(2:ℂ)^(2-4*s)/
    ((4*Real.pi*d:ℝ):ℂ)^(3-2*s)


-- @@ L590-613 verbatim
lemma besselMellinFactor_reflection (q d : ℝ) (s : ℂ) :
    inverseBesselMellinFactor q s*besselMellinFactor d (1-s)=
      besselReflectionFactor q d s*CubicReflectionKernel.gammaMultiplier (1/2-s) := by
  have hp : (2:ℂ)^(1-2*s)*(2:ℂ)^(1-2*s)=(2:ℂ)^(2-4*s) := by
    rw [←Complex.cpow_add _ _ (by norm_num : (2:ℂ)≠0)]
    congr 1
    ring
  unfold inverseBesselMellinFactor besselMellinFactor besselReflectionFactor
    CubicReflectionKernel.gammaMultiplier
  rw [show (2:ℂ)*(1-s)-1=1-2*s by ring,
    show (2:ℂ)*(1-s)+1=3-2*s by ring,
    show (1:ℂ)-s+1/3=4/3-s by ring,
    show (1:ℂ)-s+2/3=5/3-s by ring,
    show (7/6:ℂ)+(1/2-s)=5/3-s by ring,
    show (5/6:ℂ)+(1/2-s)=4/3-s by ring,
    show (7/6:ℂ)-(1/2-s)=s+2/3 by ring,
    show (5/6:ℂ)-(1/2-s)=s+1/3 by ring]
  have he := congrArg (fun z : ℂ=>
    (((4*Real.pi*q:ℝ):ℂ)^(2*s+1)*
      (Complex.Gamma (s+1/3))⁻¹*(Complex.Gamma (s+2/3))⁻¹*
      Complex.Gamma (4/3-s)*Complex.Gamma (5/3-s)*
      (((4*Real.pi*d:ℝ):ℂ)^(3-2*s))⁻¹)*z) hp
  simp only [div_eq_mul_inv,mul_inv_rev] at he ⊢
  linear_combination he


-- @@ L615-627 verbatim
lemma besselReflectionFactor_norm (q d : ℝ) (hq : 0<q) (hd : 0<d) (s : ℂ) :
    ‖besselReflectionFactor q d s‖=
      (4*Real.pi*q)^(2*s.re+1)*(2:ℝ)^(2-4*s.re)/
        (4*Real.pi*d)^(3-2*s.re) := by
  unfold besselReflectionFactor
  have h2 : ‖(2:ℂ)^(2-4*s)‖=(2:ℝ)^(2-4*s.re) := by
    simpa only [Complex.ofReal_ofNat,show (2-4*s).re=2-4*s.re by simp] using
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : 0<(2:ℝ)) (2-4*s)
  rw [norm_div,norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0<4*Real.pi*q),
    h2,
    Complex.norm_cpow_eq_rpow_re_of_pos (by positivity : 0<4*Real.pi*d)]
  norm_num


-- @@ L629-659 verbatim
theorem continuedBesselDirichlet_reflection {α : Type*} [Countable α]
    (F : ℝ→ℂ) (r : α→ℝ) (hr : ∀i,0<r i) (a : α→ℂ)
    (q d Q : ℝ) (hd : 0<d) (hQ : 0<Q) (A : ℂ)
    (hreflect : ∀v : ℝ,0<v→F v=
      A*((v:ℂ)^(-2:ℂ)*radialBesselProfile r a d ((Q*v)⁻¹)))
    (s : ℂ) (hs : s.re<4/3)
    (ha : Summable (fun i=>‖a i‖*(r i)^(s.re-1/2))) :
    continuedBesselDirichlet F q s=
      (A*(Q:ℂ)^(2-2*s)*besselReflectionFactor q d s)*
        CubicReflectionKernel.gammaMultiplier (1/2-s)*
        (∑'i,a i*(r i:ℂ)^(s-1/2)) := by
  have hs' : -(1/3)<(1-s).re := by simp;linarith
  have ha' : Summable (fun i=>‖a i‖*(r i)^(1/2-(1-s).re)) := by
    convert ha using 1
    funext i
    congr 2
    simp
    ring
  have hm := radialBesselProfile_mellin r hr a d hd (1-s) hs' ha'
  have hc := cusp_mellin_reflection_of_identity F (radialBesselProfile r a d) A s Q hQ hreflect
  have hm' : mellin (radialBesselProfile r a d) (2-2*s)=
      besselMellinFactor d (1-s)*(∑'i,a i*(r i:ℂ)^(s-1/2)) := by
    calc
      _=mellin (radialBesselProfile r a d) (2*(1-s)) := by congr 1;ring
      _=_ := by simpa only [besselMellinFactor,show (1/2:ℂ)-(1-s)=s-1/2 by ring] using hm
  rw [hm'] at hc
  rw [continuedBesselDirichlet,hc]
  calc
    _=A*(Q:ℂ)^(2-2*s)*(inverseBesselMellinFactor q s*besselMellinFactor d (1-s))*
        (∑'i,a i*(r i:ℂ)^(s-1/2)) := by ring
    _=_ := by rw [besselMellinFactor_reflection];ring


-- @@ L661-661 verbatim
end CompletedGauss


-- @@ L663-663 verbatim
end


-- @@ L665-665 verbatim
end OAI
