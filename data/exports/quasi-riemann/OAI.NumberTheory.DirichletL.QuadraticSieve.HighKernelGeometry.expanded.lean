import OAI.NumberTheory.DirichletL.QuadraticSieve.RetainedDualBounds


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators

-- @@ L8-8 verbatim
open MulChar AddChar

-- @@ L9-9 verbatim
open scoped BigOperators

-- @@ L10-10 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L11-11 verbatim
open scoped Topology

-- @@ L12-12 verbatim
open MeasureTheory Real

-- @@ L13-13 verbatim
open scoped FourierTransform SchwartzMap

-- @@ L14-14 verbatim
open Finset Complex

-- @@ L15-15 verbatim
open scoped Classical

-- @@ L16-16 verbatim
open scoped Classical

-- @@ L17-17 verbatim
open Filter Real Asymptotics

-- @@ L18-18 verbatim
open ActualEisensteinCubic

-- @@ L19-19 verbatim
open Filter

-- @@ L20-20 verbatim
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount

-- @@ L21-21 verbatim
open ActualEisensteinCubic ShortDraftLatticeCount

-- @@ L22-22 verbatim
open Filter

-- @@ L23-23 verbatim
open scoped Topology

-- @@ L24-24 verbatim
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic

-- @@ L25-25 verbatim
open MulChar AddChar

-- @@ L26-26 verbatim
open Filter Asymptotics

-- @@ L27-27 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L28-28 verbatim
open Filter

-- @@ L29-29 verbatim
open MulChar AddChar

-- @@ L30-30 verbatim
open MulChar AddChar

-- @@ L31-31 verbatim
open scoped LSeries.notation ArithmeticFunction.Moebius

-- @@ L32-32 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L33-33 verbatim
open scoped Topology

-- @@ L34-34 verbatim
open Filter Asymptotics

-- @@ L35-35 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L36-36 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L37-37 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L38-38 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L39-39 verbatim
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid

-- @@ L40-40 verbatim
open Filter Asymptotics

-- @@ L41-41 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L42-42 verbatim
open scoped Topology

-- @@ L43-43 verbatim
open Filter Asymptotics Ideal NumberField

-- @@ L44-44 verbatim
open Filter

-- @@ L45-45 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L46-46 verbatim
open scoped Topology

-- @@ L47-47 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L48-48 verbatim
open scoped Topology

-- @@ L49-49 verbatim
open Filter Asymptotics MeasureTheory

-- @@ L50-50 verbatim
open scoped Topology

-- @@ L51-51 verbatim
open MeasureTheory Real

-- @@ L52-52 verbatim
open scoped ContDiff FourierTransform SchwartzMap

-- @@ L53-53 verbatim
open scoped BigOperators Classical

-- @@ L54-54 verbatim
open scoped BigOperators Classical

-- @@ L55-55 verbatim
open scoped BigOperators Classical

-- @@ L56-56 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L57-57 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L58-58 verbatim
open scoped BigOperators Classical

-- @@ L59-59 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L60-60 verbatim
open scoped BigOperators Classical

-- @@ L61-61 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L62-62 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L63-63 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L64-64 verbatim
open scoped BigOperators Classical

-- @@ L65-65 verbatim
open scoped BigOperators Classical SchwartzMap ContDiff

-- @@ L66-66 verbatim
open MeasureTheory Set

-- @@ L67-67 verbatim
open scoped BigOperators

-- @@ L68-68 verbatim
open scoped BigOperators Classical

-- @@ L69-69 verbatim
open scoped BigOperators Classical

-- @@ L70-70 verbatim
open ActualEisensteinCubic UniqueFactorizationMonoid

-- @@ L71-71 verbatim
open scoped BigOperators


-- @@ L73-73 verbatim
open scoped BigOperators Classical

-- @@ L74-74 verbatim
namespace CanonicalQuadraticSieve

-- @@ L75-75 verbatim
open ActualEisensteinCubic


-- @@ L77-121 verbatim
theorem finite_inverse_norm_square_sum (S : Finset (Ideal O)) (H : ℝ)
    (hS : ∀ I ∈ S, I ≠ 0)
    (hH : ∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ H) :
    (∑ I ∈ S, 1/(Ideal.absNorm I : ℝ)^2) ≤ 1024 := by
  have hpos (I : Ideal O) (hI : I ∈ S) : 1 ≤ (Ideal.absNorm I : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hbin (j : Fin (columnDyadicLength H+1)) :
      (∑ I ∈ divisorDyadicBin S H j, 1/(Ideal.absNorm I : ℝ)^2) ≤
        512 * (1/(2:ℝ))^j.val := by
    have hp : 0 < (2:ℝ)^j.val := by positivity
    have hone : 1 ≤ (2:ℝ)^j.val := one_le_pow₀ (by norm_num)
    have hcount : ((divisorDyadicBin S H j).card : ℝ) ≤ 128 * (2:ℝ)^j.val := by
      apply DescentFiberCost.finite_ideal_count_real _ _ hone
      · intro I hI
        exact hS I (Finset.mem_filter.mp hI).1
      · intro I hI
        obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
        have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).2
        simpa only [hj] using hb
    have hterm (I : Ideal O) (hI : I ∈ divisorDyadicBin S H j) :
        1/(Ideal.absNorm I : ℝ)^2 ≤ 4/((2:ℝ)^j.val)^2 := by
      obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
      have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).1
      rw [hj] at hb
      have hni : 0 < (Ideal.absNorm I : ℝ) := lt_of_lt_of_le (by norm_num) (hpos I hIS)
      apply (div_le_div_iff₀ (sq_pos_of_pos hni) (sq_pos_of_pos hp)).mpr
      nlinarith
    calc
      _ ≤ ∑ _I ∈ divisorDyadicBin S H j, 4/((2:ℝ)^j.val)^2 :=
        Finset.sum_le_sum hterm
      _ = ((divisorDyadicBin S H j).card : ℝ) * (4/((2:ℝ)^j.val)^2) := by simp
      _ ≤ (128 * (2:ℝ)^j.val) * (4/((2:ℝ)^j.val)^2) := by gcongr
      _ = 512 * (1/(2:ℝ))^j.val := by
        rw [div_pow,one_pow]
        field_simp
        ; ring
  rw [sum_divisorDyadicBins S H]
  calc
    _ ≤ ∑ j : Fin (columnDyadicLength H+1), 512 * (1/(2:ℝ))^j.val :=
      Finset.sum_le_sum (fun j _ => hbin j)
    _ = 512 * ∑ j ∈ Finset.range (columnDyadicLength H+1), (1/(2:ℝ))^j := by
      rw [← Finset.mul_sum,Fin.sum_univ_eq_sum_range]
    _ ≤ 512 * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le _) (by norm_num)
    _ = 1024 := by norm_num


-- @@ L123-134 verbatim
theorem highSquareParts_card_le (M K : ℝ) (_hM : 0 ≤ M) (hK : 0 < K) :
    ((highSquareParts M K).card : ℝ) ≤ 128 * Real.sqrt (M/K) := by
  by_cases hempty : highSquareParts M K = ∅
  · simp only [hempty,Finset.card_empty,Nat.cast_zero]
    positivity
  · obtain ⟨A,hA⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hb := highSquareParts_bounds M K hK A hA
    apply DescentFiberCost.finite_ideal_count_real _ _ (hb.2.1.trans hb.2.2.1)
    · intro I hI
      exact (highSquareParts_bounds M K hK I hI).1.1
    · intro I hI
      exact (highSquareParts_bounds M K hK I hI).2.2.1


-- @@ L136-181 verbatim
theorem HasSieveExponent.high_kernel {α : ℝ} (h : HasSieveExponent α) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ M N K : ℝ,
      1 ≤ M → 1 ≤ N → 1 ≤ K →
      highKernelNorm M N K ≤ C * (M*N)^ε * (M + Real.sqrt (M/K)*N^α) := by
  intro ε hε
  obtain ⟨C,hC,hbound⟩ := h ε hε
  refine ⟨1024*C,by positivity,?_⟩
  intro M N K hM hN hK
  have hM0 : 0 ≤ M := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hK0 : 0 < K := by linarith
  let S := highSquareParts M K
  have hrow (A : Ideal O) (hA : A ∈ S) :
      sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N ≤
        C*(M*N)^ε*(M/(Ideal.absNorm A : ℝ)^2 + N^α) := by
    have hb := highSquareParts_bounds M K hK0 A hA
    have hquot : M/(Ideal.absNorm A : ℝ)^2 ≤ M :=
      div_le_self hM0 (by nlinarith [sq_nonneg ((Ideal.absNorm A : ℝ)-1)])
    apply (hbound _ N hb.2.2.2 hN).trans
    gcongr
  have hsum : (∑ A ∈ S, 1/(Ideal.absNorm A : ℝ)^2) ≤ 1024 := by
    apply finite_inverse_norm_square_sum S (Real.sqrt (M/K))
    · intro A hA
      exact (highSquareParts_bounds M K hK0 A hA).1.1
    · intro A hA
      exact (highSquareParts_bounds M K hK0 A hA).2.2.1
  have hcard : (S.card : ℝ) ≤ 128*Real.sqrt (M/K) := highSquareParts_card_le M K hM0 hK0
  have hcoeff : 0 ≤ C*(M*N)^ε := by positivity
  have hpow : 0 ≤ N^α := Real.rpow_nonneg hN0 _
  calc
    _ ≤ ∑ A ∈ S, sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N :=
      highKernelNorm_le_squarePart_sum M N K
    _ ≤ ∑ A ∈ S, C*(M*N)^ε*(M/(Ideal.absNorm A : ℝ)^2+N^α) :=
      Finset.sum_le_sum hrow
    _ = C*(M*N)^ε*(M*(∑ A ∈ S, 1/(Ideal.absNorm A : ℝ)^2)+(S.card:ℝ)*N^α) := by
      simp only [← Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
      congr 1
      rw [Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro A hA
      ring
    _ ≤ C*(M*N)^ε*(M*1024+(128*Real.sqrt (M/K))*N^α) := by gcongr
    _ ≤ (1024*C)*(M*N)^ε*(M+Real.sqrt (M/K)*N^α) := by
      have hroot : 0 ≤ Real.sqrt (M/K)*N^α := mul_nonneg (Real.sqrt_nonneg _) hpow
      nlinarith [mul_nonneg hcoeff hroot]


-- @@ L183-183 verbatim
end CanonicalQuadraticSieve


-- @@ L185-185 verbatim
namespace CubicEisenstein

-- @@ L186-186 verbatim
open Filter MeasureTheory

-- @@ L187-187 verbatim
open scoped BigOperators Classical Topology MatrixGroups Matrix


-- @@ L189-190 verbatim
def bottomRowUnitary (c d : ℂ) (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![star d/(r:ℂ),-star c/(r:ℂ);c/(r:ℂ),d/(r:ℂ)]


-- @@ L192-204 verbatim
lemma bottomRowUnitary_mem (c d : ℂ) (r : ℝ) (hr : r≠0)
    (hrow : ‖c‖^2+‖d‖^2=r^2) : bottomRowUnitary c d r∈Matrix.unitaryGroup (Fin 2) ℂ := by
  have hC : c*star c+d*star d=(r:ℂ)^2 := by
    simpa only [Complex.ofReal_add,Complex.ofReal_pow,← Complex.mul_conj',Complex.star_def] using
      congrArg (fun x : ℝ => (x:ℂ)) hrow
  have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr
  simp only [Complex.star_def] at hC
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [bottomRowUnitary,Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply,
      Complex.conj_ofReal] <;>
    field_simp [hrC] <;> first | exact hC | (simpa only [mul_comm,add_comm] using hC) | ring


-- @@ L206-217 verbatim
lemma iwasawa_z_row_identities (a b c d : ℂ) (q : ℝ)
    (hq : q≠0) (hrow : (q:ℂ)=c*star c+d*star d) (hdet : a*d-b*c=1) :
    star d/(q:ℂ)+(a*star c+b*star d)/(q:ℂ)*c=a ∧
    -star c/(q:ℂ)+(a*star c+b*star d)/(q:ℂ)*d=b := by
  have hqC : (q:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hq
  constructor
  · field_simp [hqC]
    rw [hrow]
    linear_combination -(star d)*hdet
  · field_simp [hqC]
    rw [hrow]
    linear_combination (star c)*hdet


-- @@ L219-220 verbatim
def matrixHorizontal (g : SL(2,ℂ)) : ℂ :=
  (g 0 0*star (g 1 0)+g 0 1*star (g 1 1))/(rowEnergy (complexBottomRow g):ℂ)


-- @@ L222-284 verbatim
lemma matrix_iwasawa_factor (g : SL(2,ℂ)) :
    ∃k : SL(2,ℂ), k∈compactSubgroup ∧
      g=upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g)*k := by
  let q : ℝ := rowEnergy (complexBottomRow g)
  let r : ℝ := Real.sqrt q
  have hq : 0<q := rowEnergy_pos _ (complexBottomRow_ne_zero g)
  have hr : 0<r := Real.sqrt_pos.mpr hq
  have hr2 : r^2=q := Real.sq_sqrt hq.le
  have hrow : ‖g 1 0‖^2+‖g 1 1‖^2=r^2 := by
    rw [hr2]
    rfl
  have hqC : (q:ℂ)=g 1 0*star (g 1 0)+g 1 1*star (g 1 1) := by
    simp only [q,rowEnergy,complexBottomRow,Complex.ofReal_add,Complex.ofReal_pow,
      ← Complex.mul_conj',Complex.star_def]
  have hdet : g 0 0*g 1 1-g 0 1*g 1 0=1 := by
    simpa only [Matrix.det_fin_two] using g.det_coe
  have hz := iwasawa_z_row_identities (g 0 0) (g 0 1) (g 1 0) (g 1 1) q hq.ne' hqC hdet
  let B := upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g)
  let U := bottomRowUnitary (g 1 0) (g 1 1) r
  have hroot : Real.sqrt (liftedHeight g)=r⁻¹ := by
    exact Real.sqrt_inv q
  have hrC : (r:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
  have hqrC : (r:ℂ)^2=(q:ℂ) := by exact_mod_cast hr2
  have hB : (B:Matrix (Fin 2) (Fin 2) ℂ)=
      !![(r:ℂ)⁻¹,matrixHorizontal g*(r:ℂ);0,(r:ℂ)] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [B,upperSection,hroot,Complex.ofReal_inv,div_eq_mul_inv]
  have hfactor : (B:Matrix (Fin 2) (Fin 2) ℂ)*U=(g:Matrix (Fin 2) (Fin 2) ℂ) := by
    rw [hB]
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp only [Matrix.mul_apply,Fin.sum_univ_two]
    · change (r:ℂ)⁻¹*(star (g 1 1)/(r:ℂ))+(matrixHorizontal g*(r:ℂ))*(g 1 0/(r:ℂ))=g 0 0
      calc
        _ = star (g 1 1)/(q:ℂ)+matrixHorizontal g*g 1 0 := by
          rw [← hqrC]
          field_simp [hrC]
        _ = _ := hz.1
    · change (r:ℂ)⁻¹*(-star (g 1 0)/(r:ℂ))+(matrixHorizontal g*(r:ℂ))*(g 1 1/(r:ℂ))=g 0 1
      calc
        _ = -star (g 1 0)/(q:ℂ)+matrixHorizontal g*g 1 1 := by
          rw [← hqrC]
          field_simp [hrC]
        _ = _ := hz.2
    · change 0*(star (g 1 1)/(r:ℂ))+(r:ℂ)*(g 1 0/(r:ℂ))=g 1 0
      field_simp [hrC] ; ring
    · change 0*(-star (g 1 0)/(r:ℂ))+(r:ℂ)*(g 1 1/(r:ℂ))=g 1 1
      field_simp [hrC] ; ring
  let k : SL(2,ℂ) := B⁻¹*g
  have hk : (k:Matrix (Fin 2) (Fin 2) ℂ)=U := by
    change ((B⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ) * (g:Matrix (Fin 2) (Fin 2) ℂ)=U
    rw [← hfactor,← Matrix.mul_assoc]
    have hi : ((B⁻¹:SL(2,ℂ)):Matrix (Fin 2) (Fin 2) ℂ)*(B:Matrix (Fin 2) (Fin 2) ℂ)=1 := by
      simpa only [Matrix.SpecialLinearGroup.coe_mul,Matrix.SpecialLinearGroup.coe_one] using
        congrArg (fun M : SL(2,ℂ) => (M:Matrix (Fin 2) (Fin 2) ℂ)) (inv_mul_cancel B)
    rw [hi,Matrix.one_mul]
  refine ⟨k,?_,?_⟩
  · change (k:Matrix (Fin 2) (Fin 2) ℂ)∈Matrix.unitaryGroup (Fin 2) ℂ
    rw [hk]
    exact bottomRowUnitary_mem _ _ r hr.ne' hrow
  · dsimp [k,B]
    group


-- @@ L286-302 verbatim
theorem upperPoint_surjective (w : HyperbolicSpace) :
    ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v, upperPoint z v hv=w := by
  induction w using Quotient.inductionOn with
  | _ g =>
    obtain ⟨k,hk,hg⟩ := matrix_iwasawa_factor g
    refine ⟨matrixHorizontal g,liftedHeight g,liftedHeight_pos g,?_⟩
    apply Quotient.sound
    apply QuotientGroup.leftRel_apply.mpr
    change (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*g∈compactSubgroup
    have hcancel : (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*g=k := by
      calc
        _ = (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*
            (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g)*k) :=
          congrArg (fun M => (upperSection (matrixHorizontal g) (liftedHeight g) (liftedHeight_pos g))⁻¹*M) hg
        _ = k := inv_mul_cancel_left _ _
    rw [hcancel]
    exact hk


-- @@ L304-304 verbatim
end CubicEisenstein


-- @@ L306-306 verbatim
open Filter MeasureTheory

-- @@ L307-307 verbatim
open scoped BigOperators Classical Topology


-- @@ L309-309 verbatim
namespace CubicEisenstein

-- @@ L310-310 verbatim
open ActualEisensteinCubic ConcreteTraceCRT EisensteinEmbedding

-- @@ L311-311 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L313-328 verbatim
lemma eisEmbedding_range_closed : IsClosed (Set.range eisEmbedding) := by
  let : DiscreteTopology periodLattice := by unfold periodLattice; infer_instance
  have hc : IsClosed (periodLattice : Set ℂ) :=
    periodLattice.toAddSubgroup.isClosed_of_discreteTopology
  have heq : Set.range eisEmbedding=(fun z : ℂ => 3*z) ⁻¹' (periodLattice : Set ℂ) := by
    ext z
    constructor
    · rintro ⟨n,rfl⟩
      exact three_embedding_mem n
    · intro hz
      obtain ⟨n,hn⟩ := periodPoint_bijective.2 ⟨3*z,hz⟩
      refine ⟨n,?_⟩
      have h := congrArg Subtype.val hn
      exact mul_left_cancel₀ (by norm_num : (3:ℂ)≠0) h
  rw [heq]
  exact hc.preimage (by fun_prop)


-- @@ L330-337 verbatim
lemma exists_nearest_eisenstein (z : ℂ) :
    ∃n : O, ∀m : O, ‖z-eisEmbedding n‖≤‖z-eisEmbedding m‖ := by
  obtain ⟨y,hy,heq⟩ := eisEmbedding_range_closed.exists_infDist_eq_dist
    (Set.range_nonempty eisEmbedding) z
  obtain ⟨n,rfl⟩ := hy
  refine ⟨n,fun m => ?_⟩
  rw [← dist_eq_norm,← dist_eq_norm,← heq]
  exact Metric.infDist_le_dist_of_mem ⟨m,rfl⟩


-- @@ L339-358 verbatim
lemma hexagon_norm_sq_bound (x y : ℝ)
    (hx : |x|≤1/2)
    (h₁ : x+Real.sqrt 3*y≤1) (h₂ : x-Real.sqrt 3*y≤1)
    (h₃ : -x+Real.sqrt 3*y≤1) (h₄ : -x-Real.sqrt 3*y≤1) :
    x^2+y^2≤1/3 := by
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  have ha : |x|+Real.sqrt 3*|y|≤1 := by
    rcases le_total 0 x with hxx | hxx <;> rcases le_total 0 y with hyy | hyy
    · simpa only [abs_of_nonneg hxx,abs_of_nonneg hyy] using h₁
    · simpa only [abs_of_nonneg hxx,abs_of_nonpos hyy,mul_neg,← sub_eq_add_neg] using h₂
    · simpa only [abs_of_nonpos hxx,abs_of_nonneg hyy] using h₃
    · simpa only [abs_of_nonpos hxx,abs_of_nonpos hyy,mul_neg,← sub_eq_add_neg] using h₄
  have hyprod : 0≤(1-|x|-Real.sqrt 3*|y|)*(1-|x|+Real.sqrt 3*|y|) := by
    apply mul_nonneg
    · linarith
    · have : 0≤Real.sqrt 3*|y| := mul_nonneg (Real.sqrt_nonneg 3) (abs_nonneg y)
      linarith
  have hxprod : |x| * (2*|x|-1)≤0 := mul_nonpos_of_nonneg_of_nonpos (abs_nonneg x) (by linarith)
  have hxy : (Real.sqrt 3*|y|)^2=3*y^2 := by rw [mul_pow,hs,sq_abs]
  nlinarith [sq_abs x,sq_abs y]


-- @@ L360-389 verbatim
theorem exists_eisenstein_distance_sq_le_third (z : ℂ) :
    ∃n : O, Complex.normSq (z-eisEmbedding n)≤1/3 := by
  obtain ⟨n,hn⟩ := exists_nearest_eisenstein z
  let w := z-eisEmbedding n
  have hmin (u : O) : Complex.normSq w≤Complex.normSq (w-eisEmbedding u) := by
    rw [Complex.normSq_eq_norm_sq,Complex.normSq_eq_norm_sq]
    apply pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    have h := hn (n+u)
    simpa only [map_add,sub_add_eq_sub_sub] using h
  have hre : omega3.re= -(1/2:ℝ) := by norm_num [omega3]
  have h1 := hmin 1
  have hn1 := hmin (-1)
  have hω := hmin (ActualEisensteinCoordinates.eval 0 1)
  have hnω := hmin (-(ActualEisensteinCoordinates.eval 0 1))
  have hη := hmin (ActualEisensteinCoordinates.eval 1 1)
  have hnη := hmin (-(ActualEisensteinCoordinates.eval 1 1))
  have hs : (Real.sqrt 3)^2=3 := Real.sq_sqrt (by norm_num)
  simp only [map_one,map_neg,eisEmbedding_eval,Int.cast_zero,Int.cast_one,zero_add,one_mul,
    Complex.normSq_apply,Complex.sub_re,Complex.sub_im,Complex.add_re,Complex.add_im,
    Complex.neg_re,Complex.neg_im,Complex.one_re,Complex.one_im,hre,omega3_im] at h1 hn1 hω hnω hη hnη
  refine ⟨n,?_⟩
  change Complex.normSq w≤1/3
  rw [Complex.normSq_apply,← sq,← sq]
  apply hexagon_norm_sq_bound
  · apply abs_le.mpr
    constructor <;> nlinarith
  · nlinarith [hη]
  · nlinarith [hnω]
  · nlinarith [hω]
  · nlinarith [hnη]


-- @@ L391-391 verbatim
end CubicEisenstein


-- @@ L393-393 verbatim
open Filter MeasureTheory

-- @@ L394-394 verbatim
open scoped BigOperators Classical Topology MatrixGroups


-- @@ L396-396 verbatim
namespace CubicEisenstein


-- @@ L398-398 verbatim
section

-- @@ L399-399 verbatim
open ActualEisensteinCubic ConcreteTraceCRT

-- @@ L400-400 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L402-402 verbatim
def integralBottomRow (M : SL(2,O)) : Fin 2 → O := fun j => M 1 j

-- @@ L403-404 verbatim
def integralRowEnergy (g : SL(2,ℂ)) (v : Fin 2 → O) : ℝ :=
  rowEnergy (rowOperator g (fun j => eisEmbedding (v j)))


-- @@ L406-415 verbatim
lemma integralRowEnergy_sublevel_finite (g : SL(2,ℂ)) (C : ℝ) :
    Set.Finite {v : Fin 2 → O | integralRowEnergy g v≤C} := by
  have hb : Set.Finite (Metric.closedBall (0 : (Fin 2×Fin 2)→ℤ) (rowBound g*Real.sqrt C)) :=
    (isCompact_closedBall _ _).finite_of_discrete
  apply (Set.Finite.preimage rowCoordinates_injective.injOn hb).subset
  intro v hv
  change rowCoordinates v∈Metric.closedBall 0 (rowBound g*Real.sqrt C)
  rw [Metric.mem_closedBall,dist_zero_right]
  exact (coordinates_le_transformed_energy g v).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hv) (rowBound_pos g).le)


-- @@ L417-422 verbatim
lemma integral_height_action_matrix (M : SL(2,O)) (g : SL(2,ℂ)) :
    hyperbolicHeight (integralComplexMatrix M • (QuotientGroup.mk g : HyperbolicSpace))=
      (integralRowEnergy g (integralBottomRow M))⁻¹ := by
  change (rowEnergy (complexBottomRow (integralComplexMatrix M*g)))⁻¹=_
  rw [complexBottomRow_mul]
  rfl


-- @@ L424-428 verbatim
lemma integralRowEnergy_bottom_pos (g : SL(2,ℂ)) (M : SL(2,O)) :
    0 < integralRowEnergy g (integralBottomRow M) := by
  have h := hyperbolicHeight_pos (integralComplexMatrix M • (QuotientGroup.mk g : HyperbolicSpace))
  rw [integral_height_action_matrix,inv_pos] at h
  exact h


-- @@ L430-452 verbatim
theorem exists_maximal_integral_height (w : HyperbolicSpace) :
    ∃N : SL(2,O), ∀M : SL(2,O),
      hyperbolicHeight (integralComplexMatrix M • w)≤hyperbolicHeight (integralComplexMatrix N • w) := by
  induction w using Quotient.inductionOn with
  | _ g =>
    let P : Set (Fin 2 → O) := Set.range integralBottomRow
    let C := integralRowEnergy g (integralBottomRow 1)
    let S : Set (Fin 2 → O) := {v | integralRowEnergy g v≤C} ∩ P
    have hS : Set.Finite S := (integralRowEnergy_sublevel_finite g C).inter_of_left P
    have hSne : S.Nonempty := by
      refine ⟨integralBottomRow 1,?_⟩
      change C≤C ∧ integralBottomRow 1∈Set.range integralBottomRow
      exact ⟨le_rfl,1,rfl⟩
    obtain ⟨v,hv,hmin⟩ := Set.exists_min_image S (integralRowEnergy g) hS hSne
    obtain ⟨N,hN⟩ := hv.2
    refine ⟨N,fun M => ?_⟩
    have hNM : integralRowEnergy g (integralBottomRow N)≤ integralRowEnergy g (integralBottomRow M) := by
      rw [hN]
      by_cases hM : integralRowEnergy g (integralBottomRow M)≤C
      · exact hmin _ ⟨hM,⟨M,rfl⟩⟩
      · exact hv.1.trans (le_of_not_ge hM)
    rw [integral_height_action_matrix,integral_height_action_matrix]
    exact inv_anti₀ (integralRowEnergy_bottom_pos g N) hNM


-- @@ L454-454 verbatim
end


-- @@ L456-456 verbatim
open Filter MeasureTheory

-- @@ L457-457 verbatim
open scoped BigOperators Classical Topology MatrixGroups Matrix


-- @@ L459-459 verbatim
open ActualEisensteinCubic ConcreteTraceCRT

-- @@ L460-460 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L462-463 verbatim
def integralTranslation (n : O) : SL(2,O) :=
  ⟨!![1,n;0,1],by simp [Matrix.det_fin_two]⟩

-- @@ L464-465 verbatim
def integralInversion : SL(2,O) :=
  ⟨!![0,-1;1,0],by simp [Matrix.det_fin_two]⟩


-- @@ L467-481 verbatim
lemma integralTranslation_action (n : O) (z : ℂ) (v : ℝ) (hv : 0<v) :
    integralComplexMatrix (integralTranslation n) • upperPoint z v hv=
      upperPoint (z+eisEmbedding n) v hv := by
  change (QuotientGroup.mk (integralComplexMatrix (integralTranslation n)*upperSection z v hv) : HyperbolicSpace)=
    QuotientGroup.mk (upperSection (z+eisEmbedding n) v hv)
  apply congrArg (fun g : SL(2,ℂ) => (QuotientGroup.mk g : HyperbolicSpace))
  apply Subtype.ext
  change (integralComplexMatrix (integralTranslation n) : Matrix (Fin 2) (Fin 2) ℂ) *
    (upperSection z v hv : Matrix (Fin 2) (Fin 2) ℂ) =
    (upperSection (z + eisEmbedding n) v hv : Matrix (Fin 2) (Fin 2) ℂ)
  simp only [integralComplexMatrix, Matrix.SpecialLinearGroup.map_apply_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [integralTranslation,RingHom.mapMatrix_apply,Matrix.map_apply,upperSection,Matrix.mul_apply,
      Fin.sum_univ_two,div_eq_mul_inv] ; ring


-- @@ L483-493 verbatim
lemma integralInversion_height (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicHeight (integralComplexMatrix integralInversion • upperPoint z v hv)=
      v/(‖z‖^2+v^2) := by
  have h10 : integralComplexMatrix integralInversion 1 0 = 1 := by
    change eisEmbedding 1 = 1
    exact map_one eisEmbedding
  have h11 : integralComplexMatrix integralInversion 1 1 = 0 := by
    change eisEmbedding 0 = 0
    exact map_zero eisEmbedding
  rw [hyperbolicHeight_action_upperPoint, h10, h11]
  simp


-- @@ L495-524 verbatim
theorem bianchi_ford_cover (w : HyperbolicSpace) :
    ∃M : SL(2,O), ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
      integralComplexMatrix M • w=upperPoint z v hv ∧
      Complex.normSq z≤1/3 ∧ 1≤Complex.normSq z+v^2 ∧
      ∀R : SL(2,O),hyperbolicHeight (integralComplexMatrix R • upperPoint z v hv)≤v := by
  obtain ⟨N,hN⟩ := exists_maximal_integral_height w
  obtain ⟨z,v,hv,hpoint⟩ := upperPoint_surjective (integralComplexMatrix N • w)
  obtain ⟨n,hn⟩ := exists_eisenstein_distance_sq_le_third z
  let M : SL(2,O) := integralTranslation (-n)*N
  let z' := z-eisEmbedding n
  have hMw : integralComplexMatrix M • w=upperPoint z' v hv := by
    dsimp [M]
    rw [map_mul,mul_smul,← hpoint,integralTranslation_action,map_neg]
    rfl
  have hNv : hyperbolicHeight (integralComplexMatrix N • w)=v := by
    rw [← hpoint,hyperbolicHeight_upperPoint]
  have hmax (R : SL(2,O)) :
      hyperbolicHeight (integralComplexMatrix R • upperPoint z' v hv)≤v := by
    have h := hN (R*M)
    rwa [map_mul,mul_smul,hMw,hNv] at h
  have hinv := hmax integralInversion
  rw [integralInversion_height] at hinv
  have hden : 0<‖z'‖^2+v^2 := by positivity
  have hunit : 1≤‖z'‖^2+v^2 := by
    have hm := (div_le_iff₀ hden).mp hinv
    by_contra hh
    have hlt := mul_lt_mul_of_pos_left (lt_of_not_ge hh) hv
    linarith
  refine ⟨M,z',v,hv,hMw,hn,?_,hmax⟩
  simpa only [Complex.normSq_eq_norm_sq] using hunit


-- @@ L526-533 verbatim
theorem bianchi_reduction_height_floor (w : HyperbolicSpace) :
    ∃M : SL(2,O), ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
      integralComplexMatrix M • w=upperPoint z v hv ∧
      Complex.normSq z≤1/3 ∧ Real.sqrt (2/3)≤v := by
  obtain ⟨M,z,v,hv,hMw,hz,hunit,hmax⟩ := bianchi_ford_cover w
  refine ⟨M,z,v,hv,hMw,hz,?_⟩
  apply (Real.sqrt_le_iff).mpr
  exact ⟨hv.le,by linarith⟩


-- @@ L535-536 verbatim
def truncatedFordBox (T : ℝ) : Set (ℂ×ℝ) :=
  Metric.closedBall 0 1 ×ˢ Set.Icc (Real.sqrt (2/3)) T

-- @@ L537-538 verbatim
lemma truncatedFordBox_isCompact (T : ℝ) : IsCompact (truncatedFordBox T) :=
  (isCompact_closedBall _ _).prod isCompact_Icc


-- @@ L540-546 verbatim
lemma mem_truncatedFordBox (z : ℂ) (v T : ℝ)
    (hz : Complex.normSq z≤1/3) (hv : Real.sqrt (2/3)≤v) (hT : v≤T) :
    (z,v)∈truncatedFordBox T := by
  refine ⟨?_,hv,hT⟩
  rw [Metric.mem_closedBall,dist_zero_right]
  rw [Complex.normSq_eq_norm_sq] at hz
  nlinarith [norm_nonneg z]


-- @@ L548-548 verbatim
end CubicEisenstein


-- @@ L550-550 verbatim
open Filter MeasureTheory

-- @@ L551-551 verbatim
open scoped BigOperators Classical Topology MatrixGroups


-- @@ L553-553 verbatim
namespace CubicEisenstein

-- @@ L554-554 verbatim
open CubicKubota ActualEisensteinCubic ConcreteTraceCRT

-- @@ L555-555 verbatim
local notation "O" => ActualEisensteinCubic.O


-- @@ L557-560 verbatim
lemma levelThree_finiteIndex : levelThree.FiniteIndex := by
  let : Finite (O ⧸ Ideal.span {(3:O)}) := finite_quotient_span (by norm_num)
  unfold levelThree
  infer_instance


-- @@ L562-571 verbatim
def finiteCubicMultiplier : levelThree →* rootsOfUnity 3 ℂ where
  toFun M := rootsOfUnity.mkOfPowEq (complexCharacter M) (complexCharacter_cube M)
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    simp only [rootsOfUnity.coe_mkOfPowEq,map_one,OneMemClass.coe_one,Units.val_one]
  map_mul' M N := by
    apply Subtype.ext
    apply Units.ext
    simp only [rootsOfUnity.coe_mkOfPowEq,map_mul,Subgroup.coe_mul,Units.val_mul]


-- @@ L573-573 verbatim
def globalKubotaKernel : Subgroup (SL(2,O)) := finiteCubicMultiplier.ker.map levelThree.subtype


-- @@ L575-581 verbatim
lemma globalKubotaKernel_finiteIndex : globalKubotaKernel.FiniteIndex := by
  let : levelThree.FiniteIndex := levelThree_finiteIndex
  let : finiteCubicMultiplier.ker.FiniteIndex := inferInstance
  constructor
  rw [globalKubotaKernel,Subgroup.index_map_subtype]
  exact mul_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := finiteCubicMultiplier.ker))
    (Subgroup.FiniteIndex.index_ne_zero (H := levelThree))


-- @@ L583-584 verbatim
@[simp] lemma finiteCubicMultiplier_coe (M : levelThree) :
    ((finiteCubicMultiplier M : ℂˣ) : ℂ)=complexCharacter M := rfl


-- @@ L586-595 verbatim
lemma finiteCubicMultiplier_eq_one (M : levelThree) :
    finiteCubicMultiplier M=1 ↔ complexCharacter M=1 := by
  constructor
  · intro h
    have hc := congrArg (fun x : rootsOfUnity 3 ℂ => ((x:ℂˣ):ℂ)) h
    simpa only [finiteCubicMultiplier_coe,OneMemClass.coe_one,Units.val_one] using hc
  · intro h
    apply Subtype.ext
    apply Units.ext
    simpa only [finiteCubicMultiplier_coe,OneMemClass.coe_one,Units.val_one] using h


-- @@ L597-604 verbatim
lemma globalKubotaKernel_mem (M : SL(2,O)) :
    M∈globalKubotaKernel ↔ ∃hM : M∈levelThree,complexCharacter ⟨M,hM⟩=1 := by
  constructor
  · rintro ⟨N,hN,hNM⟩
    subst M
    exact ⟨N.property,(finiteCubicMultiplier_eq_one N).mp hN⟩
  · rintro ⟨hM,hc⟩
    exact ⟨⟨M,hM⟩,(finiteCubicMultiplier_eq_one ⟨M,hM⟩).mpr hc,rfl⟩


-- @@ L606-614 verbatim
lemma finite_right_representatives {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex] :
    ∃S : Finset G, ∀g : G,∃r∈S,r⁻¹*g∈H := by
  let : Fintype (G ⧸ H) := Fintype.ofFinite _
  let S : Finset G := Finset.univ.image (fun q : G ⧸ H => Quotient.out q)
  refine ⟨S,fun g => ?_⟩
  let q : G ⧸ H := QuotientGroup.mk g
  refine ⟨Quotient.out q,?_,?_⟩
  · exact Finset.mem_image.mpr ⟨q,Finset.mem_univ _,rfl⟩
  · exact QuotientGroup.leftRel_apply.mp (Quotient.exact' (Quotient.out_eq' q))


-- @@ L616-628 verbatim
theorem finiteIndex_ford_cover (H : Subgroup (SL(2,O))) [H.FiniteIndex] :
    ∃S : Finset (SL(2,O)), ∀w : HyperbolicSpace,
      ∃h : H, ∃r∈S, ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
        integralComplexMatrix (h:SL(2,O)) • w=
          integralComplexMatrix r⁻¹ • upperPoint z v hv ∧
        Complex.normSq z≤1/3 ∧ Real.sqrt (2/3)≤v := by
  obtain ⟨S,hS⟩ := finite_right_representatives H
  refine ⟨S,fun w => ?_⟩
  obtain ⟨M,z,v,hv,hMw,hz,hfloor⟩ := bianchi_reduction_height_floor w
  obtain ⟨r,hr,hh⟩ := hS M
  refine ⟨⟨r⁻¹*M,hh⟩,r,hr,z,v,hv,?_,hz,hfloor⟩
  change integralComplexMatrix (r⁻¹*M) • w=_
  rw [map_mul,mul_smul,hMw]


-- @@ L630-636 verbatim
theorem levelThree_ford_cover :
    ∃S : Finset (SL(2,O)), ∀w : HyperbolicSpace,
      ∃h : levelThree, ∃r∈S, ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
        complexMatrix h • w=integralComplexMatrix r⁻¹ • upperPoint z v hv ∧
        Complex.normSq z≤1/3 ∧ Real.sqrt (2/3)≤v := by
  let : levelThree.FiniteIndex := levelThree_finiteIndex
  exact finiteIndex_ford_cover levelThree


-- @@ L638-644 verbatim
theorem globalKubotaKernel_ford_cover :
    ∃S : Finset (SL(2,O)), ∀w : HyperbolicSpace,
      ∃h : globalKubotaKernel, ∃r∈S, ∃z : ℂ, ∃v : ℝ, ∃hv : 0<v,
        integralComplexMatrix (h:SL(2,O)) • w=integralComplexMatrix r⁻¹ • upperPoint z v hv ∧
        Complex.normSq z≤1/3 ∧ Real.sqrt (2/3)≤v := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  exact finiteIndex_ford_cover globalKubotaKernel


-- @@ L646-646 verbatim
end CubicEisenstein


-- @@ L648-648 verbatim
end


-- @@ L650-650 verbatim
end OAI
