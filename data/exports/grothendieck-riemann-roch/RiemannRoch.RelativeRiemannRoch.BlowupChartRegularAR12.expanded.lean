/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import RiemannRoch.RelativeRiemannRoch.BlowupRegularAR12
import RiemannRoch.Chow.NormalCone.ReesBlowup
import RiemannRoch.Chow.NormalCone.QuasiRegular


-- @@ L10-15 verbatim
/-!
# AR12 (stage 2): the blow-up chart along a quasi-regular family

`y : Fin (n+1) → R`, `K = (y)`, chart at `r = y 0`.  If `y 0` is a non-zero-divisor, the chart ring
embeds in `R[1/r]` as `R[y_k/r]`; we show it is a quotient of `R[T₁..T_n]` and compute `C/rC`.
-/


-- @@ L17-17 verbatim
set_option autoImplicit false


-- @@ L19-19 verbatim
open SchemeNormalCone.AlgebraicGeometry SchemeNormalCone.AlgebraicGeometry.ReesBlowup Polynomial


-- @@ L21-21 verbatim
universe u


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace BlowupRegularAR12


-- @@ L27-27 verbatim
variable {R : Type u} [CommRing R] {n : ℕ} (y : Fin (n + 1) → R)


-- @@ L29-30 verbatim
/-- The centre ideal `(y₀, …, yₙ)`. -/
abbrev cK : Ideal R := Ideal.span (Set.range y)


-- @@ L32-32 verbatim
theorem y_mem (j : Fin (n + 1)) : y j ∈ cK y := Ideal.subset_span ⟨j, rfl⟩


-- @@ L34-35 verbatim
/-- The chart generator `r = y 0 ∈ K`. -/
def rK : cK y := ⟨y 0, y_mem y 0⟩


-- @@ L37-38 verbatim
/-- The standard blow-up chart `D₊(y₀ t)`. -/
abbrev Chart := HomogeneousLocalization.Away (grade (cK y)) (generator (cK y) (rK y))


-- @@ L40-41 verbatim
/-- The chart-to-`R[1/r]` map. -/
def eL : Chart y →+* Localization.Away (y 0) := chartLocalizationMap (cK y) (RingHom.id R) (rK y)


-- @@ L43-45 verbatim
/-- The ratio `y_{k+1}/y_0` in `R[1/y_0]`. -/
def aL (k : Fin n) : Localization.Away (y 0) :=
  IsLocalization.mk' (Localization.Away (y 0)) (y k.succ) (⟨y 0, 1, pow_one _⟩ : Submonoid.powers (y 0))


-- @@ L47-49 verbatim
/-- The evaluation of polynomials at the ratios, with values in `R[1/y_0]`. -/
def thetaL : MvPolynomial (Fin n) R →+* Localization.Away (y 0) :=
  MvPolynomial.eval₂Hom (algebraMap R (Localization.Away (y 0))) (aL y)


-- @@ L51-52 verbatim
theorem eL_injective (hr : IsRegular (y 0)) : Function.Injective (eL y) :=
  chartLocalizationMap_injective (cK y) (RingHom.id R) (rK y) (fun _ _ h => h) hr


-- @@ L54-58 verbatim
theorem aL_mul (k : Fin n) :
    aL y k * algebraMap R (Localization.Away (y 0)) (y 0) =
      algebraMap R (Localization.Away (y 0)) (y k.succ) :=
  IsLocalization.mk'_spec (Localization.Away (y 0)) (y k.succ)
    (⟨y 0, 1, pow_one _⟩ : Submonoid.powers (y 0))


-- @@ L60-68 verbatim
theorem eL_ratio (k : Fin n) :
    eL y (ratioElement (cK y) (rK y) ⟨y k.succ, y_mem y _⟩) = aL y k := by
  have h := chartLocalizationMap_mk (cK y) (RingHom.id R) (rK y) 1
    (generator (cK y) ⟨y k.succ, y_mem y _⟩) (generator_mem_grade_one _ _)
  rw [reesEval_generator] at h
  refine h.trans ?_
  rw [aL, Localization.mk_eq_mk']
  congr 1
  exact Subtype.ext (pow_one _)



-- @@ L71-71 verbatim
section Range


-- @@ L73-73 verbatim
local notation "LL" => Localization.Away (y 0)


-- @@ L75-76 verbatim
theorem thetaL_C (c : R) : thetaL y (MvPolynomial.C c) = algebraMap R LL c := by
  simp [thetaL]


-- @@ L78-79 verbatim
theorem thetaL_X (k : Fin n) : thetaL y (MvPolynomial.X k) = aL y k := by
  simp [thetaL]


-- @@ L81-82 verbatim
theorem algebraMap_mem_range (c : R) : algebraMap R LL c ∈ (thetaL y).range :=
  ⟨MvPolynomial.C c, thetaL_C y c⟩


-- @@ L84-102 verbatim
/-- `b / y₀ ∈ R[y_k/y₀]` for every `b ∈ K`. -/
theorem mk'_mem_range {b : R} (hb : b ∈ cK y) :
    IsLocalization.mk' LL b (⟨y 0, 1, pow_one _⟩ : Submonoid.powers (y 0)) ∈ (thetaL y).range := by
  induction hb using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine Fin.cases ?_ (fun k => ?_) j
    · rw [IsLocalization.mk'_self LL (x := y 0) (Submonoid.mem_powers _)]
      exact (thetaL y).range.one_mem
    · exact ⟨MvPolynomial.X k, thetaL_X y k⟩
  | zero => simp only [IsLocalization.mk'_zero]; exact (thetaL y).range.zero_mem
  | add a b _ _ ha hb =>
    rw [IsLocalization.mk'_eq_mul_mk'_one] at ha hb ⊢
    rw [map_add, add_mul]
    exact (thetaL y).range.add_mem ha hb
  | smul c a _ ha =>
    rw [IsLocalization.mk'_eq_mul_mk'_one] at ha ⊢
    rw [smul_eq_mul, map_mul, mul_assoc]
    exact (thetaL y).range.mul_mem (algebraMap_mem_range y c) ha


-- @@ L104-128 verbatim
theorem mk'_pow_mem_range (m : ℕ) : ∀ {c : R}, c ∈ cK y ^ m →
    IsLocalization.mk' LL c (⟨y 0 ^ m, m, rfl⟩ : Submonoid.powers (y 0)) ∈ (thetaL y).range := by
  induction m with
  | zero =>
    intro c _
    have : (⟨y 0 ^ 0, 0, rfl⟩ : Submonoid.powers (y 0)) = 1 := Subtype.ext (pow_zero _)
    rw [this, IsLocalization.mk'_one]
    exact algebraMap_mem_range y c
  | succ m ih =>
    intro c hc
    rw [pow_succ] at hc
    refine Submodule.mul_induction_on hc ?_ ?_
    · intro a ha b hb
      have : IsLocalization.mk' LL (a * b) (⟨y 0 ^ (m + 1), m + 1, rfl⟩ : Submonoid.powers (y 0)) =
          IsLocalization.mk' LL a (⟨y 0 ^ m, m, rfl⟩ : Submonoid.powers (y 0)) *
            IsLocalization.mk' LL b (⟨y 0, 1, pow_one _⟩ : Submonoid.powers (y 0)) := by
        rw [← IsLocalization.mk'_mul]
        congr 1
        exact Subtype.ext (pow_succ _ _)
      rw [this]
      exact (thetaL y).range.mul_mem (ih ha) (mk'_mem_range y hb)
    · intro a b ha hb
      rw [IsLocalization.mk'_eq_mul_mk'_one] at ha hb ⊢
      rw [map_add, add_mul]
      exact (thetaL y).range.add_mem ha hb


-- @@ L130-150 verbatim
theorem eL_mem_range (z : Chart y) : eL y z ∈ (thetaL y).range := by
  obtain ⟨m, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective (grade (cK y))
    (generator_mem_grade_one _ (rK y)) z
  have ha' : a ∈ grade (cK y) m := by
    convert ha using 1
    simp
  have h := chartLocalizationMap_mk (cK y) (RingHom.id R) (rK y) m a ha'
  have hae : reesEval (cK y) (RingHom.id R) a = (a : R[X]).coeff m := by
    change Polynomial.eval₂ (RingHom.id R) 1 (a : R[X]) = _
    rw [show (a : R[X]) = monomial m ((a : R[X]).coeff m) from ha']
    simp
  rw [hae] at h
  have hc : (a : R[X]).coeff m ∈ cK y ^ m := (mem_reesAlgebra_iff _ _).mp a.property m
  have h2 := mk'_pow_mem_range y m hc
  change chartLocalizationMap (cK y) (RingHom.id R) (rK y) _ ∈ _
  rw [h]
  have e : (Localization.mk ((a : R[X]).coeff m) ⟨(RingHom.id R) (rK y).1 ^ m, m, rfl⟩ :
      Localization.Away (y 0)) =
      IsLocalization.mk' LL ((a : R[X]).coeff m) (⟨y 0 ^ m, m, rfl⟩ : Submonoid.powers (y 0)) :=
    congrFun (congrFun Localization.mk_eq_mk' _) _
  exact e ▸ h2


-- @@ L152-162 verbatim
theorem thetaL_range_le_eL_range : (thetaL y).range ≤ (eL y).range := by
  rintro _ ⟨p, rfl⟩
  induction p using MvPolynomial.induction_on with
  | C a =>
    rw [thetaL_C]
    refine ⟨baseElement (cK y) (rK y) a, ?_⟩
    exact chartLocalizationMap_id_baseElement (cK y) (rK y) a
  | add p q hp hq => rw [map_add]; exact (eL y).range.add_mem hp hq
  | mul_X p k hp =>
    rw [map_mul, thetaL_X]
    exact (eL y).range.mul_mem hp ⟨_, eL_ratio y k⟩


-- @@ L164-165 verbatim
theorem eL_range_eq : (eL y).range = (thetaL y).range :=
  le_antisymm (by rintro _ ⟨z, rfl⟩; exact eL_mem_range y z) (thetaL_range_le_eL_range y)


-- @@ L167-167 verbatim
end Range


-- @@ L169-169 verbatim
section Kernel


-- @@ L171-171 verbatim
local notation "LL" => Localization.Away (y 0)


-- @@ L173-174 verbatim
theorem degree_cons (e : ℕ) (α : Fin n →₀ ℕ) : (Finsupp.cons e α).degree = e + α.degree := by
  simp [Finsupp.degree_eq_sum, Fin.sum_univ_succ, Finsupp.cons_zero, Finsupp.cons_succ]


-- @@ L176-185 verbatim
theorem key_monomial (α : Fin n →₀ ℕ) (c : R) (e : ℕ) :
    algebraMap R LL (MvPolynomial.eval y (MvPolynomial.monomial (Finsupp.cons e α) c)) =
      (algebraMap R LL (y 0)) ^ (e + α.degree) * thetaL y (MvPolynomial.monomial α c) := by
  rw [MvPolynomial.eval_monomial, thetaL, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_monomial,
    Finsupp.prod_fintype _ _ (by simp), Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_succ]
  simp only [Finsupp.cons_zero, Finsupp.cons_succ, map_mul, map_prod, map_pow]
  have h : ∀ k : Fin n, algebraMap R LL (y k.succ) = aL y k * algebraMap R LL (y 0) :=
    fun k => (aL_mul y k).symm
  simp only [h, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Finsupp.degree_eq_sum]
  ring


-- @@ L187-189 verbatim
/-- Homogenisation of `h` to degree `m` in the variable `X₀` (the chart equation). -/
def homog (m : ℕ) (h : MvPolynomial (Fin n) R) : MvPolynomial (Fin (n + 1)) R :=
  ∑ α ∈ h.support, MvPolynomial.monomial (Finsupp.cons (m - α.degree) α) (h.coeff α)


-- @@ L191-193 verbatim
theorem degree_le_of_mem_support {h : MvPolynomial (Fin n) R} {α : Fin n →₀ ℕ}
    (hα : α ∈ h.support) : α.degree ≤ h.totalDegree :=
  MvPolynomial.le_totalDegree hα


-- @@ L195-201 verbatim
theorem homog_isHomogeneous (m : ℕ) (h : MvPolynomial (Fin n) R) (hm : h.totalDegree ≤ m) :
    (homog m h).IsHomogeneous m := by
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun α hα => ?_
  apply MvPolynomial.isHomogeneous_monomial
  rw [degree_cons]
  have := degree_le_of_mem_support hα
  omega


-- @@ L203-211 verbatim
theorem algebraMap_eval_homog (m : ℕ) (h : MvPolynomial (Fin n) R) (hm : h.totalDegree ≤ m) :
    algebraMap R LL (MvPolynomial.eval y (homog m h)) =
      (algebraMap R LL (y 0)) ^ m * thetaL y h := by
  conv_rhs => rw [h.as_sum]
  rw [homog, map_sum, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [key_monomial]
  have := degree_le_of_mem_support hα
  rw [Nat.sub_add_cancel (this.trans hm)]


-- @@ L213-228 verbatim
theorem coeff_homog (m : ℕ) (h : MvPolynomial (Fin n) R) (α : Fin n →₀ ℕ) :
    (homog m h).coeff (Finsupp.cons (m - α.degree) α) = h.coeff α := by
  classical
  rw [homog, MvPolynomial.coeff_sum]
  have hiff : ∀ β : Fin n →₀ ℕ,
      (Finsupp.cons (m - β.degree) β = Finsupp.cons (m - α.degree) α) ↔ β = α := by
    intro β
    constructor
    · intro hb
      exact (Finsupp.cons_injective2 hb).2
    · rintro rfl; rfl
  simp_rw [MvPolynomial.coeff_monomial, hiff]
  rw [Finset.sum_ite_eq']
  by_cases hα : α ∈ h.support
  · simp [hα]
  · simp [hα, MvPolynomial.notMem_support_iff.mp hα]


-- @@ L230-232 verbatim
theorem algebraMap_injective (hr : IsRegular (y 0)) :
    Function.Injective (algebraMap R LL) :=
  IsLocalization.injective LL (powers_le_nonZeroDivisors_of_isRegular (y 0) hr)


-- @@ L234-246 verbatim
/-- **Kernel of the ratio evaluation.**  If `y₀` is regular and `y` quasi-regular, a polynomial
vanishing at the ratios `y_{k+1}/y₀` has all its coefficients in `K = (y)`. -/
theorem coeff_mem_of_thetaL_eq_zero (hr : IsRegular (y 0))
    (hqr : SchemeNormalCone.Algebra.IsQuasiregular y)
    (h : MvPolynomial (Fin n) R) (h0 : thetaL y h = 0) (α : Fin n →₀ ℕ) :
    h.coeff α ∈ cK y := by
  have h1 := algebraMap_eval_homog y h.totalDegree h le_rfl
  rw [h0, mul_zero] at h1
  have h2 : MvPolynomial.eval y (homog h.totalDegree h) = 0 :=
    algebraMap_injective y hr (by rw [h1, map_zero])
  have h3 := hqr h.totalDegree (homog h.totalDegree h) (homog_isHomogeneous _ h le_rfl)
    (by rw [h2]; exact Submodule.zero_mem _) (Finsupp.cons (h.totalDegree - α.degree) α)
  rwa [coeff_homog] at h3


-- @@ L248-248 verbatim
end Kernel


-- @@ L250-250 verbatim
section Assembly


-- @@ L252-252 verbatim
local notation "LL" => Localization.Away (y 0)


-- @@ L254-255 verbatim
/-- The subring `R[y_k / y₀] ⊆ R[1/y₀]`. -/
abbrev Bsub : Subring LL := (thetaL y).range


-- @@ L257-258 verbatim
/-- The surjection `R[T₁..Tₙ] ↠ R[y_k/y₀]`. -/
def thetaB : MvPolynomial (Fin n) R →+* Bsub y := (thetaL y).rangeRestrict


-- @@ L260-261 verbatim
theorem thetaB_surjective : Function.Surjective (thetaB y) :=
  RingHom.rangeRestrict_surjective _


-- @@ L263-265 verbatim
theorem thetaB_C (c : R) : thetaB y (MvPolynomial.C c) =
    ⟨algebraMap R LL c, algebraMap_mem_range y c⟩ :=
  Subtype.ext (thetaL_C y c)


-- @@ L267-268 verbatim
/-- The class of `y₀` in `R[y_k/y₀]`. -/
def rB : Bsub y := ⟨algebraMap R LL (y 0), algebraMap_mem_range y _⟩


-- @@ L270-281 verbatim
theorem rB_mem_nonZeroDivisors : rB y ∈ nonZeroDivisors (Bsub y) := by
  have hu : IsUnit (algebraMap R LL (y 0)) := IsLocalization.Away.algebraMap_isUnit (y 0)
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · apply Subtype.ext
    have := congrArg Subtype.val hx
    simp only [rB, Subring.coe_mul, Subring.coe_zero] at this
    exact (hu.mul_right_eq_zero).mp this
  · apply Subtype.ext
    have := congrArg Subtype.val hx
    simp only [rB, Subring.coe_mul, Subring.coe_zero] at this
    exact (hu.mul_left_eq_zero).mp this


-- @@ L283-289 verbatim
theorem algebraMap_mem_span_rB {c : R} (hc : c ∈ cK y) :
    (⟨algebraMap R LL c, algebraMap_mem_range y c⟩ : Bsub y) ∈ Ideal.span {rB y} := by
  rw [Ideal.mem_span_singleton']
  refine ⟨⟨_, mk'_mem_range y hc⟩, ?_⟩
  apply Subtype.ext
  simp only [rB, Subring.coe_mul]
  exact IsLocalization.mk'_spec LL c (⟨y 0, 1, pow_one _⟩ : Submonoid.powers (y 0))


-- @@ L291-315 verbatim
theorem thetaB_mem_span_rB_iff (hr : IsRegular (y 0))
    (hqr : SchemeNormalCone.Algebra.IsQuasiregular y) (h : MvPolynomial (Fin n) R) :
    thetaB y h ∈ Ideal.span {rB y} ↔ ∀ α, h.coeff α ∈ cK y := by
  constructor
  · intro hh
    rw [Ideal.mem_span_singleton'] at hh
    obtain ⟨b, hb⟩ := hh
    obtain ⟨q, rfl⟩ := thetaB_surjective y b
    have h0 : thetaL y (h - MvPolynomial.C (y 0) * q) = 0 := by
      have this : thetaL y q * algebraMap R LL (y 0) = thetaL y h := congrArg Subtype.val hb
      rw [map_sub, map_mul, thetaL_C, mul_comm, this, sub_self]
    intro α
    have := coeff_mem_of_thetaL_eq_zero y hr hqr _ h0 α
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_C_mul] at this
    have h2 : y 0 * q.coeff α ∈ cK y := Ideal.mul_mem_right _ _ (y_mem y 0)
    have := (cK y).add_mem this h2
    simpa using this
  · intro hh
    rw [h.as_sum, map_sum]
    refine Ideal.sum_mem _ fun α _ => ?_
    have hm : MvPolynomial.monomial α (h.coeff α) =
        MvPolynomial.C (h.coeff α) * MvPolynomial.monomial α 1 := by
      simp [MvPolynomial.C_mul_monomial]
    rw [hm, map_mul, thetaB_C]
    exact Ideal.mul_mem_right _ _ (algebraMap_mem_span_rB y (hh α))


-- @@ L317-319 verbatim
theorem Bsub_isNoetherianRing [IsRegularRing R] : IsNoetherianRing (Bsub y) :=
  isNoetherianRing_of_surjective (MvPolynomial (Fin n) R) (Bsub y) (thetaB y)
    (thetaB_surjective y)


-- @@ L321-340 verbatim
/-- **The exceptional divisor of the chart.**  `R[y_k/y₀] / (y₀) ≃ (R/K)[T₁..Tₙ]`. -/
noncomputable def quotEquiv (hr : IsRegular (y 0))
    (hqr : SchemeNormalCone.Algebra.IsQuasiregular y) :
    (Bsub y ⧸ Ideal.span {rB y}) ≃+* MvPolynomial (Fin n) (R ⧸ cK y) := by
  let π : MvPolynomial (Fin n) R →+* Bsub y ⧸ Ideal.span {rB y} :=
    (Ideal.Quotient.mk _).comp (thetaB y)
  have hπ : Function.Surjective π :=
    Ideal.Quotient.mk_surjective.comp (thetaB_surjective y)
  let μ : MvPolynomial (Fin n) R →+* MvPolynomial (Fin n) (R ⧸ cK y) :=
    MvPolynomial.map (Ideal.Quotient.mk (cK y))
  have hμ : Function.Surjective μ := MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective
  have hker : RingHom.ker π = RingHom.ker μ := by
    ext h
    rw [RingHom.mem_ker, RingHom.mem_ker]
    change Ideal.Quotient.mk _ (thetaB y h) = 0 ↔ _
    rw [Ideal.Quotient.eq_zero_iff_mem, thetaB_mem_span_rB_iff y hr hqr, MvPolynomial.ext_iff]
    refine forall_congr' fun α => ?_
    simp [μ, MvPolynomial.coeff_map, Ideal.Quotient.eq_zero_iff_mem]
  exact (RingHom.quotientKerEquivOfSurjective hπ).symm.trans
    ((Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hμ))


-- @@ L342-373 verbatim
/-- **Core.**  The ring `R[y_k/y₀]` is regular, provided `R` and `R/K` are regular, `y₀` is a
non-zero-divisor and `y` is quasi-regular. -/
theorem isRegularRing_Bsub [IsRegularRing R] [IsRegularRing (R ⧸ cK y)] (hr : IsRegular (y 0))
    (hqr : SchemeNormalCone.Algebra.IsQuasiregular y) : IsRegularRing (Bsub y) := by
  haveI := Bsub_isNoetherianRing y
  haveI : IsRegularRing (MvPolynomial (Fin n) (R ⧸ cK y)) :=
    isRegularRing_mvPolynomial_of_regular (R ⧸ cK y) (Fin n)
  haveI hq : IsRegularRing (Bsub y ⧸ Ideal.span {rB y}) :=
    IsRegularRing.of_ringEquiv (quotEquiv y hr hqr).symm
  refine ⟨fun Q _ => ?_⟩
  by_cases hQ : rB y ∈ Q
  · exact isRegularLocalRing_localization_of_quotient_span_singleton
      (rB_mem_nonZeroDivisors y) Q hQ
  · letI : Algebra (Bsub y) LL := (Bsub y).subtype.toAlgebra
    haveI : IsLocalization (Submonoid.powers (rB y)) LL := by
      refine ⟨?_, ?_, ?_⟩
      · rintro ⟨_, k, rfl⟩
        change IsUnit (algebraMap (Bsub y) LL (rB y ^ k))
        rw [map_pow]
        exact (IsLocalization.Away.algebraMap_isUnit (y 0)).pow k
      · intro z
        obtain ⟨⟨c, ⟨_, k, rfl⟩⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (y 0)) z
        refine ⟨(⟨algebraMap R LL c, algebraMap_mem_range y c⟩, ⟨rB y ^ k, k, rfl⟩), ?_⟩
        change z * ((rB y ^ k : Bsub y) : LL) = algebraMap R LL c
        simpa [rB, map_pow] using hz
      · intro a b hab
        exact ⟨1, by simp [Subtype.ext hab]⟩
    haveI : IsRegularRing LL := isRegularRing_of_isLocalization (A := R) (Submonoid.powers (y 0))
    refine isRegularLocalRing_of_isLocalization (T := LL) (Submonoid.powers (rB y)) Q ?_
    refine Set.disjoint_left.mpr ?_
    rintro _ ⟨k, rfl⟩ hk
    exact hQ (Ideal.IsPrime.mem_of_pow_mem inferInstance k hk)


-- @@ L375-380 verbatim
/-- The chart ring is `R[y_k / y₀]`. -/
noncomputable def chartEquivBsub (hr : IsRegular (y 0)) : Chart y ≃+* Bsub y :=
  (RingEquiv.ofBijective (eL y).rangeRestrict
    ⟨fun _ _ h => eL_injective y hr (congrArg Subtype.val h),
      RingHom.rangeRestrict_surjective _⟩).trans
    (RingEquiv.subringCongr (eL_range_eq y))


-- @@ L382-388 verbatim
/-- **AR12 core theorem (affine, chart at a regular generator).**  Let `R` be a regular ring,
`y₀,…,yₙ` a quasi-regular family with `y₀` a non-zero-divisor and `R/(y)` a regular ring.  Then the
blow-up chart `D₊(y₀ t)` of `Bl_{(y)} Spec R` is a regular ring. -/
theorem isRegularRing_chart [IsRegularRing R] [IsRegularRing (R ⧸ cK y)] (hr : IsRegular (y 0))
    (hqr : SchemeNormalCone.Algebra.IsQuasiregular y) : IsRegularRing (Chart y) := by
  haveI := isRegularRing_Bsub y hr hqr
  exact IsRegularRing.of_ringEquiv (chartEquivBsub y hr).symm


-- @@ L390-390 verbatim
end Assembly


-- @@ L392-392 verbatim
end BlowupRegularAR12


-- @@ L394-394 verbatim
end
