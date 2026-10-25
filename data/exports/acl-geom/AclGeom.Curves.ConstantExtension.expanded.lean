/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Curves.Residues
import AclGeom.Correspondence.RegularACF
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.RingTheory.Valuation.LocalSubring
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization


-- @@ L21-59 verbatim
/-!
# Integral closures under constant field extension

Let `F` be a function field of one variable over an algebraically closed field `k`, let `t ∈ F`
be transcendental with `F/k(t)` separable, and let `B` be the integral closure of `k[t]` in `F`.
For an arbitrary field extension `L/k`, the image of `L ⊗[k] B` in `Frac(L ⊗[k] F)` is the
integral closure of `L[1 ⊗ t]` (`isIntegral_adjoin_iff_mem_range`,
`range_toSubring_eq_integralClosure`). In particular it is integrally closed: normalization
commutes with constant field extension.

The places of `Frac(L ⊗[k] F)` over `L` are then described by these integral closures.
`Frac(L ⊗[k] F)` is finite separable over `L(1 ⊗ t)` (`finiteDimensional_isSeparable_adjoin`).
Every proper valuation subring `V ⊇ L` is the localization, at its centre, of the integral
closure of `L[T]` when `T = 1 ⊗ t ∈ V` (`valuationSubring_eq_ofPrime`), and of `L[T⁻¹]`
otherwise (`valuationSubring_eq_ofPrime_inv`). Consequently, a derivation preserving both
integral closures preserves every such `V`
(`derivation_mem_valuationSubring_of_integralClosure`); in particular so does every
derivation mapping `L` into itself and killing `1 ⊗ F`
(`derivation_mem_valuationSubring_of_horizontal`).

The proof has two steps.

* *Clearing denominators* (`exists_algebraMap_eq_of_monic`). An integral basis of `F/k(t)` over
  `k[t]` stays a basis of `Frac(L ⊗[k] F)` over `L(t)`, with compatible traces, so its
  discriminant `d ∈ k[t]` multiplies every element integral over `L[t]` into `L ⊗[k] F`. Since
  `d` is invertible in `F`, such elements already lie in `L ⊗[k] F`.
* *Working one place at a time* (`mem_range_integralClosure_of_monic`). At a place `P` of `F/k`,
  the reduction map `L ⊗[k] O_P → L ⊗[k] k = L` lands in a field, so an element of
  `L ⊗[k] F` outside `L ⊗[k] O_P` cannot be integral over `L ⊗[k] O_P`: a minimal power of the
  uniformizer clears its denominators, and reducing the scaled integral equation gives a
  nilpotent nonzero element of `L`. Coefficients along a `k`-basis of `L` then lie in every
  valuation ring containing `k[t]`, hence in `B`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved, with no unproved hypotheses (#21). An input of the genus argument for
Hrushovski–Weil curves.
-/


-- @@ L61-61 verbatim
namespace AclGeom


-- @@ L63-63 verbatim
open TensorProduct Polynomial


-- @@ L65-65 verbatim
noncomputable section


-- @@ L67-67 verbatim
variable {k F L : Type*} [Field k] [Field F] [Field L] [Algebra k F] [Algebra k L]


-- @@ L69-69 verbatim
/-! ### Base change of subalgebras -/


-- @@ L71-71 verbatim
section BaseChange


-- @@ L73-76 verbatim
variable (L) in
/-- The base change `L ⊗[k] O → L ⊗[k] F` of a `k`-subalgebra `O` of `F`. -/
def baseChangeIncl (O : Subalgebra k F) : L ⊗[k] O →ₐ[k] L ⊗[k] F :=
  Algebra.TensorProduct.map (AlgHom.id k L) O.val


-- @@ L78-80 verbatim
@[simp]
theorem baseChangeIncl_tmul (O : Subalgebra k F) (l : L) (o : O) :
    baseChangeIncl L O (l ⊗ₜ o) = l ⊗ₜ (o : F) := rfl


-- @@ L82-90 verbatim
theorem baseChangeIncl_injective (O : Subalgebra k F) :
    Function.Injective (baseChangeIncl L O) := by
  have h : (baseChangeIncl L O).toLinearMap = O.val.toLinearMap.lTensor L :=
    TensorProduct.ext' fun _ _ ↦ rfl
  intro x y hxy
  have hxy' : (O.val.toLinearMap.lTensor L) x = (O.val.toLinearMap.lTensor L) y := by
    rw [← h]
    exact hxy
  exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective hxy'


-- @@ L92-92 verbatim
variable {ι : Type*} [DecidableEq ι] (b : Module.Basis ι k L)


-- @@ L94-101 verbatim
theorem equivFinsuppOfBasisLeft_baseChangeIncl (O : Subalgebra k F) (z : L ⊗[k] O) (i : ι) :
    equivFinsuppOfBasisLeft b (baseChangeIncl L O z) i =
      (equivFinsuppOfBasisLeft b z i : F) := by
  induction z using TensorProduct.inductionOn with
  | tmul l o =>
    rw [baseChangeIncl_tmul, equivFinsuppOfBasisLeft_apply_tmul_apply,
      equivFinsuppOfBasisLeft_apply_tmul_apply, Subalgebra.coe_smul]
  | add z w hz hw => simp only [map_add, Finsupp.add_apply, hz, hw, Subalgebra.coe_add]


-- @@ L103-114 verbatim
/-- An element of `L ⊗[k] F` lies in `L ⊗[k] O` iff its coefficients along a basis of `L` lie
in `O`. -/
theorem mem_range_baseChangeIncl_iff (O : Subalgebra k F) (x : L ⊗[k] F) :
    x ∈ (baseChangeIncl L O).range ↔ ∀ i, equivFinsuppOfBasisLeft b x i ∈ O := by
  constructor
  · rintro ⟨z, rfl⟩ i
    change equivFinsuppOfBasisLeft b (baseChangeIncl L O z) i ∈ O
    rw [equivFinsuppOfBasisLeft_baseChangeIncl]
    exact (equivFinsuppOfBasisLeft b z i).2
  · intro h
    rw [← (equivFinsuppOfBasisLeft b).symm_apply_apply x, equivFinsuppOfBasisLeft_symm_apply]
    exact Subalgebra.sum_mem _ fun i _ ↦ ⟨b i ⊗ₜ ⟨_, h i⟩, rfl⟩


-- @@ L116-122 verbatim
theorem equivFinsuppOfBasisLeft_one_tmul_mul (a : F) (x : L ⊗[k] F) (i : ι) :
    equivFinsuppOfBasisLeft b ((1 ⊗ₜ a) * x) i = a * equivFinsuppOfBasisLeft b x i := by
  induction x using TensorProduct.inductionOn with
  | tmul l f =>
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, equivFinsuppOfBasisLeft_apply_tmul_apply,
      equivFinsuppOfBasisLeft_apply_tmul_apply, mul_smul_comm]
  | add x y hx hy => simp only [mul_add, map_add, Finsupp.add_apply, hx, hy]


-- @@ L124-124 verbatim
end BaseChange


-- @@ L126-126 verbatim
/-! ### Discriminants -/


-- @@ L128-128 verbatim
section Discriminant


-- @@ L130-130 verbatim
open Matrix Algebra


-- @@ L132-170 verbatim
/-- `discr K b • z` lies in the `R`-span of an `R`-integral basis `b`, for every `z` integral over
`R`. This is the general-basis form of `Algebra.discr_mul_isIntegral_mem_adjoin`. -/
theorem discr_smul_mem_span_of_isIntegral {R K E : Type*} [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [Field K] [Algebra R K] [IsFractionRing R K] [Field E] [Algebra K E]
    [Algebra R E] [IsScalarTower R K E] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K E) (hb : ∀ i, IsIntegral R (b i)) (hd : discr K b ≠ 0) {z : E}
    (hz : IsIntegral R z) : discr K b • z ∈ Submodule.span R (Set.range b) := by
  have _ := Module.Finite.of_basis b
  have hinv : IsUnit (traceMatrix K b).det := by
    rw [← discr_def]
    exact hd.isUnit
  have H : (traceMatrix K b).det • (traceMatrix K b) *ᵥ (b.equivFun z) =
      (traceMatrix K b).det • fun i => trace K E (z * b i) := by
    congr
    exact traceMatrix_of_basis_mulVec _ _
  have cramer := mulVec_cramer (traceMatrix K b) fun i => trace K E (z * b i)
  suffices ∀ i, ((traceMatrix K b).det • b.equivFun z) i ∈ (⊥ : Subalgebra R K) by
    rw [← b.sum_repr z, Finset.smul_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    replace this := this i
    rw [← discr_def, Pi.smul_apply, mem_bot] at this
    obtain ⟨r, hr⟩ := this
    rw [Module.Basis.equivFun_apply] at hr
    rw [← smul_assoc, ← hr, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  intro i
  rw [← H, ← mulVec_smul] at cramer
  replace cramer := congr_arg (mulVec (traceMatrix K b)⁻¹) cramer
  rw [mulVec_mulVec, nonsing_inv_mul _ hinv, mulVec_mulVec, nonsing_inv_mul _ hinv, one_mulVec,
    one_mulVec] at cramer
  rw [← congr_fun cramer i, cramer_apply, det_apply]
  refine Subalgebra.sum_mem _ fun σ _ =>
    Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun j _ => ?_) _
  by_cases hji : j = i
  · simp only [updateCol_apply, hji, ↓reduceIte]
    exact mem_bot.2 (IsIntegrallyClosed.isIntegral_iff.1 <| isIntegral_trace (hz.mul <| hb _))
  · simp only [updateCol_apply, hji, ↓reduceIte, traceMatrix_apply, traceForm_apply]
    exact mem_bot.2
      (IsIntegrallyClosed.isIntegral_iff.1 <| isIntegral_trace <| (hb _).mul (hb _))


-- @@ L172-191 verbatim
/-- Traces are compatible with a ring homomorphism carrying one basis to another and the
coefficient fields compatibly. -/
theorem trace_map_of_compatible {K₀ E₀ K E : Type*} [Field K₀] [Field E₀] [Field K] [Field E]
    [Algebra K₀ E₀] [Algebra K E] [Algebra K₀ K] {ι : Type*} [Finite ι]
    (β : Module.Basis ι K₀ E₀) (b : Module.Basis ι K E) (ψ : E₀ →+* E)
    (hψ : ∀ i, ψ (β i) = b i)
    (hcomp : ∀ a : K₀, ψ (algebraMap K₀ E₀ a) = algebraMap K E (algebraMap K₀ K a)) (c : E₀) :
    trace K E (ψ c) = algebraMap K₀ K (trace K₀ E₀ c) := by
  classical
  have := Fintype.ofFinite ι
  have hrepr : ∀ x : E₀, ∀ i, b.repr (ψ x) i = algebraMap K₀ K (β.repr x i) := by
    intro x i
    have hx : ψ x = ∑ l, algebraMap K₀ K (β.repr x l) • b l := by
      conv_lhs => rw [← β.sum_repr x]
      simp only [map_sum, Algebra.smul_def, map_mul, hcomp, hψ]
    rw [hx, Module.Basis.repr_sum_self]
  rw [trace_eq_matrix_trace b, trace_eq_matrix_trace β, Matrix.trace, Matrix.trace, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Matrix.diag_apply, Matrix.diag_apply, leftMulMatrix_eq_repr_mul,
    leftMulMatrix_eq_repr_mul, ← hψ i, ← map_mul, hrepr]


-- @@ L193-206 verbatim
/-- Discriminants are compatible with a ring homomorphism carrying one basis to another and the
coefficient fields compatibly. -/
theorem discr_map_of_compatible {K₀ E₀ K E : Type*} [Field K₀] [Field E₀] [Field K] [Field E]
    [Algebra K₀ E₀] [Algebra K E] [Algebra K₀ K] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (β : Module.Basis ι K₀ E₀) (b : Module.Basis ι K E) (ψ : E₀ →+* E)
    (hψ : ∀ i, ψ (β i) = b i)
    (hcomp : ∀ a : K₀, ψ (algebraMap K₀ E₀ a) = algebraMap K E (algebraMap K₀ K a)) :
    discr K b = algebraMap K₀ K (discr K₀ β) := by
  rw [discr_def, discr_def, RingHom.map_det]
  congr 1
  ext i j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, traceMatrix_apply, traceMatrix_apply,
    traceForm_apply, traceForm_apply, ← hψ i, ← hψ j, ← map_mul,
    trace_map_of_compatible β b ψ hψ hcomp]


-- @@ L208-208 verbatim
end Discriminant


-- @@ L210-210 verbatim
/-! ### Reduction at a place -/


-- @@ L212-212 verbatim
section Place


-- @@ L214-214 verbatim
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]


-- @@ L216-218 verbatim
/-- The valuation ring of a place, as a `k`-subalgebra. -/
def Place.subalgebra (P : Place k F) : Subalgebra k F :=
  { P.val.toSubring with algebraMap_mem' := P.algebraMap_mem }


-- @@ L220-223 verbatim
omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
theorem Place.mem_subalgebra_iff (P : Place k F) {u : F} :
    u ∈ P.subalgebra ↔ P.val.valuation u ≤ 1 :=
  P.val.valuation_le_one_iff u |>.symm


-- @@ L225-238 verbatim
omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
private theorem residue_unique (P : Place k F) {u : F} {c c' : k}
    (h : P.val.valuation (u - algebraMap k F c) < 1)
    (h' : P.val.valuation (u - algebraMap k F c') < 1) : c = c' := by
  by_contra hne
  have h1 : P.val.valuation (algebraMap k F (c' - c)) = 1 :=
    valuation_algebraMap_eq_one P.algebraMap_mem (sub_ne_zero.2 (Ne.symm hne))
  have h2 : P.val.valuation (algebraMap k F (c' - c)) < 1 := by
    have : algebraMap k F (c' - c) = (u - algebraMap k F c) - (u - algebraMap k F c') := by
      rw [map_sub]
      ring
    rw [this]
    exact lt_of_le_of_lt (Valuation.map_sub _ _ _) (max_lt h h')
  exact h2.ne h1


-- @@ L240-242 verbatim
/-- The residue of an element integral at a place: the unique constant congruent to it. -/
private def residueFun (P : Place k F) (u : P.subalgebra) : k :=
  (P.exists_residue ((P.mem_subalgebra_iff).1 u.2)).choose


-- @@ L244-246 verbatim
private theorem residueFun_spec (P : Place k F) (u : P.subalgebra) :
    P.val.valuation ((u : F) - algebraMap k F (residueFun P u)) < 1 :=
  (P.exists_residue ((P.mem_subalgebra_iff).1 u.2)).choose_spec


-- @@ L248-250 verbatim
private theorem residueFun_eq (P : Place k F) (u : P.subalgebra) {c : k}
    (h : P.val.valuation ((u : F) - algebraMap k F c) < 1) : residueFun P u = c :=
  residue_unique P (residueFun_spec P u) h


-- @@ L252-284 verbatim
/-- The residue map of a place, as a `k`-algebra homomorphism to the base field. -/
private def residue (P : Place k F) : P.subalgebra →ₐ[k] k where
  toFun := residueFun P
  map_one' := residueFun_eq P 1 (by simp)
  map_mul' u u' := residueFun_eq P (u * u') (by
    have hu := residueFun_spec P u
    have hu' := residueFun_spec P u'
    have hle : P.val.valuation (u : F) ≤ 1 := (P.mem_subalgebra_iff).1 u.2
    have hc : P.val.valuation (algebraMap k F (residueFun P u')) ≤ 1 :=
      (P.mem_subalgebra_iff).1 (P.subalgebra.algebraMap_mem _)
    have heq : ((u * u' : P.subalgebra) : F) - algebraMap k F (residueFun P u * residueFun P u') =
        (u : F) * ((u' : F) - algebraMap k F (residueFun P u')) +
          algebraMap k F (residueFun P u') * ((u : F) - algebraMap k F (residueFun P u)) := by
      rw [Subalgebra.coe_mul, map_mul]
      ring
    rw [heq]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hle) hu'
    · rw [map_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_left' hc) hu)
  map_zero' := residueFun_eq P 0 (by simp)
  map_add' u u' := residueFun_eq P (u + u') (by
    have heq : ((u + u' : P.subalgebra) : F) -
        algebraMap k F (residueFun P u + residueFun P u') =
        ((u : F) - algebraMap k F (residueFun P u)) +
          ((u' : F) - algebraMap k F (residueFun P u')) := by
      rw [Subalgebra.coe_add, map_add]
      ring
    rw [heq]
    exact lt_of_le_of_lt (Valuation.map_add _ _ _)
      (max_lt (residueFun_spec P u) (residueFun_spec P u')))
  commutes' c := residueFun_eq P _ (by simp)


-- @@ L286-288 verbatim
/-- The uniformizer of a place, as an element of its valuation ring. -/
private def piSub (P : Place k F) : P.subalgebra :=
  ⟨P.pi, (P.mem_subalgebra_iff).2 P.pi_valuation_lt_one.le⟩


-- @@ L290-291 verbatim
private theorem residue_piSub (P : Place k F) : residue P (piSub P) = 0 :=
  residueFun_eq P _ (by rw [map_zero, sub_zero]; exact P.pi_valuation_lt_one)


-- @@ L293-309 verbatim
/-- An element of residue zero is divisible by the uniformizer. -/
private theorem exists_eq_piSub_mul (P : Place k F) {u : P.subalgebra}
    (hu : residue P u = 0) : ∃ w : P.subalgebra, u = piSub P * w := by
  have hsmall : P.val.valuation (u : F) < 1 := by
    have := residueFun_spec P u
    change residue P u = 0 at hu
    rwa [show residueFun P u = residue P u from rfl, hu, map_zero, sub_zero] at this
  by_cases hu0 : (u : F) = 0
  · exact ⟨0, Subtype.ext (by rw [hu0, mul_zero, Subalgebra.coe_zero])⟩
  have hpi := P.pi_ne_zero
  refine ⟨⟨(u : F) / P.pi, (P.mem_subalgebra_iff).2 ?_⟩, Subtype.ext ?_⟩
  · have hord := (P.ord_pos_iff hu0).2 hsmall
    rw [← P.ord_nonneg_iff (div_ne_zero hu0 hpi), div_eq_mul_inv, P.ord_mul hu0 (inv_ne_zero hpi),
      P.ord_inv hpi, P.ord_pi]
    omega
  · change (u : F) = P.pi * ((u : F) / P.pi)
    field_simp


-- @@ L311-314 verbatim
/-- Reduction modulo a place: `L ⊗[k] O_P → L ⊗[k] k = L`. -/
private def reduction (P : Place k F) : L ⊗[k] P.subalgebra →ₐ[k] L :=
  Algebra.TensorProduct.lift (AlgHom.id k L) ((Algebra.ofId k L).comp (residue P))
    fun _ _ ↦ Commute.all _ _


-- @@ L316-319 verbatim
private theorem reduction_tmul (P : Place k F) (l : L) (u : P.subalgebra) :
    reduction P (l ⊗ₜ u) = residue P u • l := by
  rw [reduction, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, AlgHom.comp_apply,
    Algebra.ofId_apply, Algebra.smul_def, mul_comm]


-- @@ L321-346 verbatim
/-- The kernel of reduction is generated by the uniformizer. -/
private theorem exists_eq_mul_of_reduction_eq_zero (P : Place k F)
    {z : L ⊗[k] P.subalgebra} (hz : reduction P z = 0) :
    ∃ z' : L ⊗[k] P.subalgebra, z = (1 ⊗ₜ piSub P) * z' := by
  classical
  let b := Module.Basis.ofVectorSpace k L
  set c := equivFinsuppOfBasisLeft b z
  have hz_eq : z = c.sum fun i u ↦ b i ⊗ₜ u := by
    rw [← equivFinsuppOfBasisLeft_symm_apply]
    exact ((equivFinsuppOfBasisLeft b).symm_apply_apply z).symm
  have hred : ∀ i, residue P (c i) = 0 := by
    intro i
    have hlin : reduction P z =
        Finsupp.linearCombination k b (c.mapRange (residue P) (map_zero _)) := by
      rw [hz_eq, map_finsuppSum, Finsupp.linearCombination_apply,
        Finsupp.sum_mapRange_index (h := fun i a ↦ a • b i) (fun _ ↦ zero_smul _ _)]
      exact Finsupp.sum_congr fun j _ ↦ reduction_tmul P (b j) (c j)
    have := congrArg (fun l ↦ b.repr l i) hlin
    rw [hz, map_zero, Finsupp.zero_apply, Module.Basis.repr_linearCombination,
      Finsupp.mapRange_apply] at this
    exact this.symm
  choose w hw using fun i ↦ exists_eq_piSub_mul P (hred i)
  refine ⟨Finsupp.sum c fun i _ ↦ b i ⊗ₜ w i, ?_⟩
  rw [hz_eq, Finsupp.mul_sum]
  refine Finsupp.sum_congr fun i _ ↦ ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, ← hw i]


-- @@ L348-358 verbatim
private theorem scaleRoots_zero_eval {R : Type*} [CommRing R] (q : R[X]) (y : R) :
    (q.scaleRoots 0).eval y = q.leadingCoeff * y ^ q.natDegree := by
  have : q.scaleRoots 0 = monomial q.natDegree q.leadingCoeff := by
    ext i
    rw [coeff_scaleRoots, coeff_monomial]
    rcases lt_trichotomy i q.natDegree with hi | rfl | hi
    · simp [hi.ne', zero_pow (Nat.sub_ne_zero_of_lt hi)]
    · simp only [Nat.sub_self, pow_zero, mul_one, ↓reduceIte]
      rfl
    · simp [hi.ne, coeff_eq_zero_of_natDegree_lt hi]
  rw [this, eval_monomial]


-- @@ L360-440 verbatim
/-- **Integrality at a place.** An element of `L ⊗[k] F` which is a root of a monic polynomial
over `L ⊗[k] O_P` lies in `L ⊗[k] O_P`. -/
theorem mem_range_baseChangeIncl_of_monic (P : Place k F) {x : L ⊗[k] F}
    {p : (L ⊗[k] P.subalgebra)[X]} (hp : p.Monic)
    (hx : p.eval₂ (baseChangeIncl L P.subalgebra).toRingHom x = 0) :
    x ∈ (baseChangeIncl L P.subalgebra).range := by
  classical
  let b := Module.Basis.ofVectorSpace k L
  set ι' := baseChangeIncl L P.subalgebra
  set πL : L ⊗[k] F := 1 ⊗ₜ P.pi
  have hπ : ι' (1 ⊗ₜ piSub P) = πL := rfl
  have hπunit : IsUnit πL := by
    refine isUnit_iff_exists_inv.2 ⟨1 ⊗ₜ P.pi⁻¹, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_inv_cancel₀ P.pi_ne_zero]
    rfl
  -- Some power of the uniformizer clears the denominators of `x`.
  have hs : ∃ s : ℕ, πL ^ s * x ∈ ι'.range := by
    set c := equivFinsuppOfBasisLeft b x
    have hcoef : ∀ i, ∃ s : ℕ, P.pi ^ s * c i ∈ P.subalgebra := by
      intro i
      by_cases hci : c i = 0
      · exact ⟨0, by rw [hci, mul_zero]; exact zero_mem _⟩
      refine ⟨(-P.ord (c i)).toNat, (P.mem_subalgebra_iff).2 ?_⟩
      have hne : P.pi ^ (-P.ord (c i)).toNat * c i ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ P.pi_ne_zero) hci
      rw [← P.ord_nonneg_iff hne, P.ord_mul (pow_ne_zero _ P.pi_ne_zero) hci,
        P.ord_pow P.pi_ne_zero, P.ord_pi, mul_one]
      have := Int.self_le_toNat (-P.ord (c i))
      omega
    choose s hs using hcoef
    refine ⟨c.support.sup s, (mem_range_baseChangeIncl_iff b _ _).2 fun i ↦ ?_⟩
    have hpow : πL ^ c.support.sup s = 1 ⊗ₜ (P.pi ^ c.support.sup s) := by
      rw [Algebra.TensorProduct.tmul_pow, one_pow]
    rw [hpow, equivFinsuppOfBasisLeft_one_tmul_mul]
    by_cases hi : i ∈ c.support
    · have hle : s i ≤ c.support.sup s := Finset.le_sup hi
      rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc]
      exact mul_mem (pow_mem ((P.mem_subalgebra_iff).2 P.pi_valuation_lt_one.le) _) (hs i)
    · rw [Finsupp.notMem_support_iff.1 hi, mul_zero]
      exact zero_mem _
  -- Choose the minimal such power.
  let s₀ := Nat.find hs
  have hs₀ : πL ^ s₀ * x ∈ ι'.range := Nat.find_spec hs
  rcases Nat.eq_zero_or_pos s₀ with h0 | hpos
  · rw [h0, pow_zero, one_mul] at hs₀
    exact hs₀
  exfalso
  obtain ⟨z₀, hz₀⟩ := hs₀
  replace hz₀ : ι' z₀ = πL ^ s₀ * x := hz₀
  -- The reduction of the cleared element is nonzero, by minimality.
  have hred : reduction P z₀ ≠ 0 := by
    intro h0
    obtain ⟨z', rfl⟩ := exists_eq_mul_of_reduction_eq_zero P h0
    have hlt : s₀ - 1 < s₀ := Nat.sub_lt hpos one_pos
    refine Nat.find_min hs hlt ⟨z', ?_⟩
    have h1 : πL * (πL ^ (s₀ - 1) * x) = πL * ι' z' := by
      rw [← mul_assoc, ← pow_succ', Nat.sub_add_cancel hpos, ← hz₀, map_mul, hπ]
    exact (hπunit.mul_left_cancel h1).symm
  -- Scale the integral equation and reduce it.
  have hq : (p.scaleRoots ((1 ⊗ₜ piSub P) ^ s₀)).eval z₀ = 0 := by
    apply baseChangeIncl_injective (L := L) P.subalgebra
    change ι'.toRingHom _ = ι'.toRingHom 0
    have hz' : ι'.toRingHom z₀ = ι'.toRingHom ((1 ⊗ₜ piSub P) ^ s₀) * x := by
      rw [map_pow]
      change ι' z₀ = ι' (1 ⊗ₜ piSub P) ^ s₀ * x
      rw [hz₀, hπ]
    rw [map_zero, ← eval₂_hom, hz']
    exact scaleRoots_eval₂_eq_zero ι'.toRingHom hx
  have hmap : ((p.map (reduction P).toRingHom).scaleRoots 0).eval (reduction P z₀) = 0 := by
    have h1 := congrArg (reduction P).toRingHom hq
    rw [map_zero, ← eval₂_hom, ← eval_map, map_scaleRoots _ _ _ (by
      rw [hp.leadingCoeff, map_one]
      exact one_ne_zero)] at h1
    have h2 : (reduction (L := L) P).toRingHom (((1 : L) ⊗ₜ piSub P) ^ s₀) = 0 := by
      rw [map_pow]
      change reduction (L := L) P ((1 : L) ⊗ₜ piSub P) ^ s₀ = 0
      rw [reduction_tmul, residue_piSub, zero_smul, zero_pow hpos.ne']
    rw [h2] at h1
    exact h1
  rw [scaleRoots_zero_eval, (hp.map _).leadingCoeff, one_mul] at hmap
  exact hred (eq_zero_of_pow_eq_zero hmap)


-- @@ L442-455 verbatim
omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- An element lying in every place that contains `t` is integral over `k[t]`. -/
private theorem isIntegral_of_forall_place {t f : F}
    (h : ∀ P : Place k F, t ∈ P.val → f ∈ P.val) : IsIntegral (Algebra.adjoin k {t}) f := by
  by_contra hf
  have hfR : f ∉ (integralClosure (Algebra.adjoin k {t}) F).toSubring :=
    fun h' ↦ hf ((mem_integralClosure_iff _ _).1 h')
  obtain ⟨V, hRV, hfV⟩ := Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hfR
  have hkt : ∀ x ∈ Algebra.adjoin k ({t} : Set F), x ∈ V := fun x hx ↦
    hRV ((mem_integralClosure_iff _ _).2
      (isIntegral_algebraMap (x := (⟨x, hx⟩ : Algebra.adjoin k ({t} : Set F)))))
  have hne : V ≠ ⊤ := fun hV ↦ hfV (hV ▸ ValuationSubring.mem_top f)
  let P : Place k F := ⟨V, fun c ↦ hkt _ (Subalgebra.algebraMap_mem _ c), hne⟩
  exact hfV (h P (hkt t (Algebra.subset_adjoin rfl)))


-- @@ L457-484 verbatim
/-- **Integrality in a constant field extension.** An element of `L ⊗[k] F` which is a root of a
monic polynomial over `L ⊗[k] k[t]` lies in `L ⊗[k] B`, where `B` is the integral closure of
`k[t]` in `F`. -/
theorem mem_range_integralClosure_of_monic {t : F} {x : L ⊗[k] F}
    {p : (L ⊗[k] Algebra.adjoin k ({t} : Set F))[X]} (hp : p.Monic)
    (hx : p.eval₂ (baseChangeIncl L (Algebra.adjoin k {t})).toRingHom x = 0) :
    x ∈ (baseChangeIncl L
      ((integralClosure (Algebra.adjoin k ({t} : Set F)) F).restrictScalars k)).range := by
  classical
  let b := Module.Basis.ofVectorSpace k L
  rw [mem_range_baseChangeIncl_iff b]
  intro i
  rw [Subalgebra.mem_restrictScalars, mem_integralClosure_iff]
  refine isIntegral_of_forall_place fun P htP ↦ ?_
  have hle : Algebra.adjoin k ({t} : Set F) ≤ P.subalgebra :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 htP)
  let φ : L ⊗[k] Algebra.adjoin k ({t} : Set F) →ₐ[k] L ⊗[k] P.subalgebra :=
    Algebra.TensorProduct.map (AlgHom.id k L) (Subalgebra.inclusion hle)
  have hφ : (baseChangeIncl L P.subalgebra).toRingHom.comp φ.toRingHom =
      (baseChangeIncl L (Algebra.adjoin k {t})).toRingHom := by
    have : (baseChangeIncl L P.subalgebra).comp φ = baseChangeIncl L (Algebra.adjoin k {t}) :=
      Algebra.TensorProduct.ext' fun _ _ ↦ rfl
    rw [← this]
    rfl
  have hxP := mem_range_baseChangeIncl_of_monic P (hp.map φ.toRingHom) (by
    rw [eval₂_map, hφ]
    exact hx)
  exact (mem_range_baseChangeIncl_iff b P.subalgebra x).1 hxP i


-- @@ L486-486 verbatim
end Place


-- @@ L488-488 verbatim
/-! ### Polynomials over `L` in `1 ⊗ t` -/


-- @@ L490-490 verbatim
section Polynomial


-- @@ L492-501 verbatim
/-- Evaluation at `1 ⊗ t` factors through `L ⊗[k] k[X]`. -/
private theorem aeval_one_tmul_eq_map (t : F) (p : L[X]) :
    aeval ((1 : L) ⊗ₜ[k] t) p =
      Algebra.TensorProduct.map (AlgHom.id k L) (aeval t : k[X] →ₐ[k] F)
        (polyEquivTensor k L p) := by
  rw [polyEquivTensor_apply, aeval_def, ← AlgHom.coe_toRingHom, hom_eval₂]
  congr 1
  · ext l
    simp [Algebra.TensorProduct.algebraMap_apply]
  · simp


-- @@ L503-513 verbatim
private theorem equivFinsuppOfBasisLeft_map_mul {ι : Type*} [DecidableEq ι]
    (e : Module.Basis ι k L) (t : F) (P : L ⊗[k] k[X]) (y : F) (μ : ι) :
    equivFinsuppOfBasisLeft e
      (Algebra.TensorProduct.map (AlgHom.id k L) (aeval t : k[X] →ₐ[k] F) P * ((1 : L) ⊗ₜ y)) μ =
        aeval t (equivFinsuppOfBasisLeft e P μ) * y := by
  induction P using TensorProduct.inductionOn with
  | tmul l q =>
    rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul,
      mul_one, equivFinsuppOfBasisLeft_apply_tmul_apply,
      equivFinsuppOfBasisLeft_apply_tmul_apply, map_smul, smul_mul_assoc]
  | add P Q hP hQ => simp only [map_add, add_mul, Finsupp.add_apply, hP, hQ]


-- @@ L515-524 verbatim
private theorem map_aeval_injective {t : F} (ht : Transcendental k t) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id k L) (aeval t : k[X] →ₐ[k] F)) := by
  have h : (Algebra.TensorProduct.map (AlgHom.id k L) (aeval t : k[X] →ₐ[k] F)).toLinearMap =
      (aeval t).toLinearMap.lTensor L := TensorProduct.ext' fun _ _ ↦ rfl
  intro x y hxy
  have hxy' : ((aeval t).toLinearMap.lTensor L) x = ((aeval t).toLinearMap.lTensor L) y := by
    rw [← h]
    exact hxy
  exact Module.Flat.lTensor_preserves_injective_linearMap _
    (transcendental_iff_injective.1 ht) hxy'


-- @@ L526-531 verbatim
/-- Evaluation at `1 ⊗ t` is injective on `L[X]`. -/
theorem aeval_one_tmul_injective {t : F} (ht : Transcendental k t) :
    Function.Injective (aeval ((1 : L) ⊗ₜ[k] t) : L[X] →ₐ[L] L ⊗[k] F) := by
  intro p q hpq
  rw [aeval_one_tmul_eq_map, aeval_one_tmul_eq_map] at hpq
  exact (polyEquivTensor k L).injective (map_aeval_injective ht hpq)


-- @@ L533-548 verbatim
/-- If the `β i` are independent over `k[t]`, then the `1 ⊗ β i` are independent over `L[1 ⊗ t]`. -/
private theorem eq_zero_of_sum_aeval_one_tmul {t : F} {ι : Type*} [Fintype ι] (β : ι → F)
    (hβ : ∀ q : ι → k[X], ∑ i, aeval t (q i) * β i = 0 → ∀ i, q i = 0) (g : ι → L[X])
    (hg : ∑ i, aeval ((1 : L) ⊗ₜ[k] t) (g i) * ((1 : L) ⊗ₜ[k] β i) = 0) : ∀ i, g i = 0 := by
  classical
  let e := Module.Basis.ofVectorSpace k L
  intro i
  have hP : polyEquivTensor k L (g i) = 0 := by
    apply (equivFinsuppOfBasisLeft e).injective
    refine Finsupp.ext fun μ ↦ ?_
    rw [map_zero, Finsupp.zero_apply]
    have hμ := congrArg (fun x ↦ equivFinsuppOfBasisLeft e x μ) hg
    simp only [map_sum, Finsupp.finsetSum_apply, aeval_one_tmul_eq_map,
      equivFinsuppOfBasisLeft_map_mul, map_zero, Finsupp.zero_apply] at hμ
    exact hβ (fun j ↦ equivFinsuppOfBasisLeft e (polyEquivTensor k L (g j)) μ) hμ i
  exact (polyEquivTensor k L).injective (hP.trans (map_zero _).symm)


-- @@ L550-550 verbatim
end Polynomial


-- @@ L552-552 verbatim
/-! ### Valuation subrings dominating a Dedekind domain -/


-- @@ L554-554 verbatim
section Centre


-- @@ L556-556 verbatim
variable {K : Type*} [Field K]


-- @@ L558-568 verbatim
private theorem isUnit_iff_inv_mem {S : Subring K} (x : S) :
    IsUnit x ↔ (x : K) ≠ 0 ∧ (x : K)⁻¹ ∈ S := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.1 hx
    have h1 : (x : K) * y = 1 := congrArg Subtype.val hy
    refine ⟨left_ne_zero_of_mul_eq_one h1, ?_⟩
    rw [inv_eq_of_mul_eq_one_right h1]
    exact y.2
  · rintro ⟨h0, hinv⟩
    exact isUnit_iff_exists_inv.2 ⟨⟨_, hinv⟩, Subtype.ext (mul_inv_cancel₀ h0)⟩


-- @@ L570-586 verbatim
/-- Elements of the localization of a subring `A` of a field at a prime `P` are the fractions
`a / s` with `a, s ∈ A` and `s ∉ P`. -/
theorem mem_ofPrime_iff (A : Subring K) (P : Ideal A) [P.IsPrime] (x : K) :
    x ∈ (LocalSubring.ofPrime A P).toSubring ↔ ∃ a s : A, s ∉ P ∧ x = a / s := by
  set S := (LocalSubring.ofPrime A P).toSubring
  have hs0 : ∀ s : A, s ∉ P → (s : K) ≠ 0 := fun s hs h0 ↦
    hs (by rw [show s = 0 from Subtype.ext h0]; exact P.zero_mem)
  constructor
  · intro hx
    obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj P.primeCompl (⟨x, hx⟩ : S)
    have e' : x * s = a := congrArg Subtype.val e
    exact ⟨a, s, s.2, (eq_div_iff (hs0 s s.2)).2 e'⟩
  · rintro ⟨a, s, hs, rfl⟩
    let y : S := IsLocalization.mk' S a (⟨s, hs⟩ : P.primeCompl)
    have e : (y : K) * s = a := congrArg Subtype.val (IsLocalization.mk'_spec S a ⟨s, hs⟩)
    rw [← (eq_div_iff (hs0 s hs)).2 e]
    exact y.2


-- @@ L588-591 verbatim
/-- The centre on a subring `A` of a valuation subring `V ⊇ A`: the prime ideal `A ∩ 𝔪_V`. -/
def centre (A : Subring K) (V : ValuationSubring K) (h : A ≤ V.toSubring) : Ideal A :=
  (IsLocalRing.maximalIdeal V.toLocalSubring.toSubring).comap
    (Subring.inclusion (S := A) (T := V.toLocalSubring.toSubring) h)


-- @@ L593-596 verbatim
instance (A : Subring K) (V : ValuationSubring K) (h : A ≤ V.toSubring) :
    (centre A V h).IsPrime := by
  unfold centre
  infer_instance


-- @@ L598-601 verbatim
theorem notMem_centre_iff {A : Subring K} {V : ValuationSubring K} {h : A ≤ V.toSubring}
    (a : A) : a ∉ centre A V h ↔ (a : K) ≠ 0 ∧ (a : K)⁻¹ ∈ V := by
  rw [centre, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  exact isUnit_iff_inv_mem _


-- @@ L603-647 verbatim
/-- **A proper valuation subring dominating a Dedekind domain is a localization.** If `V` is a
proper valuation subring of the fraction field of a Dedekind domain `R ≤ V`, then the centre
of `V` on `R` is a nonzero prime and `V` is the localization of `R` there. -/
theorem centre_ne_bot_and_eq_ofPrime (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]
    (V : ValuationSubring K) (h : R ≤ V.toSubring) (hV : V ≠ ⊤) :
    centre R V h ≠ ⊥ ∧ V.toLocalSubring = LocalSubring.ofPrime R (centre R V h) := by
  set P := centre R V h
  have hunit : ∀ s : R, s ∉ P → (s : K) ≠ 0 ∧ (s : K)⁻¹ ∈ V := fun s hs ↦
    (notMem_centre_iff s).1 hs
  have hP : P ≠ ⊥ := by
    intro hP
    refine hV (ValuationSubring.ext _ _ fun x ↦ iff_of_true ?_ (ValuationSubring.mem_top x))
    obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) x
    have hs0 : s ∉ P := by
      rw [hP, Ideal.mem_bot]
      exact nonZeroDivisors.ne_zero hs
    rw [div_eq_mul_inv]
    exact mul_mem (h a.2) (hunit s hs0).2
  have _ : IsDiscreteValuationRing (LocalSubring.ofPrime R P).toSubring :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain R hP _
  have _ : IsFractionRing (LocalSubring.ofPrime R P).toSubring K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl _ K
  let W : ValuationSubring K := ValuationSubring.ofSubring (LocalSubring.ofPrime R P).toSubring
    fun x ↦ (ValuationRing.isInteger_or_isInteger (LocalSubring.ofPrime R P).toSubring x).imp
      (fun ⟨y, hy⟩ ↦ by rw [← hy]; exact y.2) (fun ⟨y, hy⟩ ↦ by rw [← hy]; exact y.2)
  have hWV : (LocalSubring.ofPrime R P).toSubring ≤ V.toSubring := by
    intro x hx
    obtain ⟨a, s, hs, rfl⟩ := (mem_ofPrime_iff R P x).1 hx
    rw [div_eq_mul_inv]
    exact mul_mem (h a.2) (hunit s hs).2
  have hdom : W.toLocalSubring ≤ V.toLocalSubring := by
    refine ⟨hWV, ⟨fun y hy ↦ ?_⟩⟩
    obtain ⟨hy0, hyinv⟩ := (isUnit_iff_inv_mem _).1 hy
    change (y : K) ≠ 0 at hy0
    change (y : K)⁻¹ ∈ V at hyinv
    obtain ⟨a, s, hs, hys⟩ := (mem_ofPrime_iff R P y).1 y.2
    have hs0 := (hunit s hs).1
    have hays : (a : K) = y * s := by rw [hys, div_mul_cancel₀ _ hs0]
    have ha : a ∉ P := by
      rw [notMem_centre_iff, hays, mul_inv]
      exact ⟨mul_ne_zero hy0 hs0, mul_mem hyinv (hunit s hs).2⟩
    refine (isUnit_iff_inv_mem y).2 ⟨hy0, (mem_ofPrime_iff R P _).2 ⟨s, a, ha, ?_⟩⟩
    rw [hys, inv_div]
  have hmax : V.toLocalSubring ≤ W.toLocalSubring := W.isMax_toLocalSubring hdom
  exact ⟨hP, LocalSubring.toSubring_injective (le_antisymm hmax.1 hWV)⟩


-- @@ L649-663 verbatim
/-- Elementwise form of `centre_ne_bot_and_eq_ofPrime`: the elements of `V` are the fractions
`a / s` with `a, s ∈ R` and `s` a unit of `V`. -/
theorem mem_valuationSubring_iff (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]
    (V : ValuationSubring K) (h : R ≤ V.toSubring) (hV : V ≠ ⊤) (x : K) :
    x ∈ V ↔ ∃ a ∈ R, ∃ s ∈ R, s ≠ 0 ∧ s⁻¹ ∈ V ∧ x = a / s := by
  have hx : x ∈ V ↔ x ∈ (LocalSubring.ofPrime R (centre R V h)).toSubring :=
    Iff.of_eq (congrArg (fun S : LocalSubring K ↦ x ∈ S.toSubring)
      (centre_ne_bot_and_eq_ofPrime R V h hV).2)
  rw [hx, mem_ofPrime_iff]
  constructor
  · rintro ⟨a, s, hs, rfl⟩
    obtain ⟨hs0, hsinv⟩ := (notMem_centre_iff s).1 hs
    exact ⟨a, a.2, s, s.2, hs0, hsinv, rfl⟩
  · rintro ⟨a, ha, s, hs, hs0, hsinv, rfl⟩
    exact ⟨⟨a, ha⟩, ⟨s, hs⟩, (notMem_centre_iff _).2 ⟨hs0, hsinv⟩, rfl⟩


-- @@ L665-678 verbatim
/-- **Derivations preserve dominating valuation subrings.** A derivation of `K` preserving a
Dedekind domain `R` with fraction field `K` preserves every proper valuation subring `V ⊇ R`,
by the quotient rule. -/
theorem derivation_mem_valuationSubring {A : Type*} [CommRing A] [Algebra A K]
    (D : Derivation A K K) (R : Subring K) [IsDedekindDomain R] [IsFractionRing R K]
    (hD : ∀ x ∈ R, D x ∈ R) (V : ValuationSubring K) (h : R ≤ V.toSubring) (hV : V ≠ ⊤)
    {x : K} (hx : x ∈ V) : D x ∈ V := by
  obtain ⟨a, ha, s, hs, hs0, hsinv, rfl⟩ := (mem_valuationSubring_iff R V h hV x).1 hx
  have hl := D.leibniz (a / s) s
  rw [div_mul_cancel₀ _ hs0, smul_eq_mul, smul_eq_mul] at hl
  have hq : D (a / s) = s⁻¹ * (D a - a / s * D s) := by
    rw [hl, add_sub_cancel_left, ← mul_assoc, inv_mul_cancel₀ hs0, one_mul]
  rw [hq]
  exact mul_mem hsinv (sub_mem (h (hD a ha)) (mul_mem hx (h (hD s hs))))


-- @@ L680-695 verbatim
/-- A valuation subring containing `K₀` and `T` contains the integral closure of `K₀[T]`. -/
theorem integralClosure_adjoin_le {K₀ : Type*} [Field K₀] [Algebra K₀ K] {T : K}
    (V : ValuationSubring K) (hK₀ : ∀ c : K₀, algebraMap K₀ K c ∈ V) (hT : T ∈ V) :
    (integralClosure (Algebra.adjoin K₀ {T}) K).toSubring ≤ V.toSubring := by
  let VK : Subalgebra K₀ K := { V.toSubring with algebraMap_mem' := hK₀ }
  have hAV : Algebra.adjoin K₀ {T} ≤ VK := Algebra.adjoin_le (Set.singleton_subset_iff.2 hT)
  intro x hx
  obtain ⟨p, hp, hpx⟩ : IsIntegral (Algebra.adjoin K₀ {T}) x := hx
  let ι : Algebra.adjoin K₀ {T} →+* V.toLocalSubring.toSubring :=
    (algebraMap (Algebra.adjoin K₀ {T}) K).codRestrict V.toLocalSubring.toSubring
      fun a ↦ hAV a.2
  refine LocalSubring.mem_of_isMax_of_isIntegral V.isMax_toLocalSubring
    ⟨p.map ι, hp.map ι, ?_⟩
  rw [eval₂_map, show (algebraMap V.toLocalSubring.toSubring K).comp ι =
    algebraMap (Algebra.adjoin K₀ {T}) K from RingHom.ext fun _ ↦ rfl]
  exact hpx


-- @@ L697-729 verbatim
/-- If `E` is finite separable over `K₀(T)`, the integral closure of `K₀[T]` in `E` is a
Dedekind domain with fraction field `E`. -/
theorem isDedekindDomain_integralClosure_adjoin {K₀ E : Type*} [Field K₀] [Field E]
    [Algebra K₀ E] (T : E) [FiniteDimensional (IntermediateField.adjoin K₀ {T}) E]
    [Algebra.IsSeparable (IntermediateField.adjoin K₀ {T}) E] :
    IsDedekindDomain (integralClosure (Algebra.adjoin K₀ {T}) E).toSubring ∧
      IsFractionRing (integralClosure (Algebra.adjoin K₀ {T}) E).toSubring E := by
  let _ : Algebra (Algebra.adjoin K₀ {T}) (IntermediateField.adjoin K₀ {T}) :=
    (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin K₀ {T})).toAlgebra
  have _ : IsScalarTower (Algebra.adjoin K₀ {T}) (IntermediateField.adjoin K₀ {T}) E :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have _ : FaithfulSMul (Algebra.adjoin K₀ {T}) (IntermediateField.adjoin K₀ {T}) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (Subalgebra.inclusion_injective _)
  have _ : IsFractionRing (Algebra.adjoin K₀ {T}) (IntermediateField.adjoin K₀ {T}) :=
    IsFractionRing.of_field _ _ fun w ↦ by
      obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff K₀ (w : E)).1 w.2
      exact ⟨⟨aeval T r, aeval_mem_adjoin_singleton K₀ T⟩,
        ⟨aeval T s, aeval_mem_adjoin_singleton K₀ T⟩,
        Subtype.ext (by rw [IntermediateField.coe_div]; exact hrs)⟩
  have hsurj : Function.Surjective
      (aeval (R := K₀) (⟨T, Algebra.self_mem_adjoin_singleton K₀ T⟩ : Algebra.adjoin K₀ {T})) := by
    rintro ⟨x, hx⟩
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
    obtain ⟨q, rfl⟩ := hx
    exact ⟨q, Subtype.ext (aeval_algHom_apply (Algebra.adjoin K₀ {T}).val _ q).symm⟩
  have _ : IsPrincipalIdealRing (Algebra.adjoin K₀ {T}) :=
    IsPrincipalIdealRing.of_surjective _ hsurj
  have _ := IsIntegralClosure.isDedekindDomain (Algebra.adjoin K₀ {T})
    (IntermediateField.adjoin K₀ {T}) E (integralClosure (Algebra.adjoin K₀ {T}) E)
  have _ := integralClosure.isFractionRing_of_finite_extension (A := Algebra.adjoin K₀ {T})
    (IntermediateField.adjoin K₀ {T}) E
  exact ⟨inferInstanceAs (IsDedekindDomain (integralClosure (Algebra.adjoin K₀ {T}) E)),
    inferInstanceAs (IsFractionRing (integralClosure (Algebra.adjoin K₀ {T}) E) E)⟩


-- @@ L731-731 verbatim
end Centre


-- @@ L733-733 verbatim
/-! ### The fraction field of a constant field extension -/


-- @@ L735-735 verbatim
section FractionField


-- @@ L737-737 verbatim
open Algebra


-- @@ L739-739 verbatim
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]


-- @@ L741-741 verbatim
attribute [local instance] isDomain_tensorProduct_of_isAlgClosed


-- @@ L743-744 verbatim
/-- The fraction field of the constant field extension `L ⊗[k] F`. -/
local notation "𝓕" => FractionRing (L ⊗[k] F)


-- @@ L746-937 verbatim
/-- **Elements of the fraction field integral over `L[1 ⊗ t]` lie in `L ⊗[k] F`.** The
discriminant of an integral basis of `F/k(t)` lies in `k[t]`, is invertible in `F`, and clears
the denominators of every integral element of `Frac(L ⊗[k] F)`. -/
theorem exists_algebraMap_eq_of_monic {t : F} (ht : Transcendental k t)
    [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F]
    {z : FractionRing (L ⊗[k] F)} {p : L[X][X]} (hp : p.Monic)
    (hz : p.eval₂ ((algebraMap (L ⊗[k] F) 𝓕).comp
      (aeval ((1 : L) ⊗ₜ[k] t)).toRingHom) z = 0) :
    ∃ y : L ⊗[k] F, algebraMap (L ⊗[k] F) 𝓕 y = z := by
  classical
  set ιE := algebraMap (L ⊗[k] F) 𝓕
  have hιE : Function.Injective ιE := IsFractionRing.injective _ _
  set Kt := IntermediateField.adjoin k ({t} : Set F)
  have _ : FiniteDimensional Kt F := finiteDimensional_adjoin_of_transcendental ht
  have htK : t ∈ Kt := IntermediateField.subset_adjoin k _ rfl
  have hinj_t : Function.Injective (aeval t : k[X] →ₐ[k] F) :=
    transcendental_iff_injective.1 ht
  -- `k[X]` acts on `k(t)` and on `F` through `t`.
  let _ : Algebra k[X] Kt := (aeval (⟨t, htK⟩ : Kt)).toRingHom.toAlgebra
  let _ : Algebra k[X] F := (aeval t).toRingHom.toAlgebra
  have hKtF : ∀ q : k[X], algebraMap Kt F (algebraMap k[X] Kt q) = aeval t q := fun q ↦
    (aeval_algHom_apply Kt.val (⟨t, htK⟩ : Kt) q).symm
  have _ : IsScalarTower k[X] Kt F := IsScalarTower.of_algebraMap_eq fun q ↦ (hKtF q).symm
  have _ : FaithfulSMul k[X] Kt := (faithfulSMul_iff_algebraMap_injective _ _).2 fun q q' h ↦
    hinj_t (by rw [← hKtF, ← hKtF, h])
  have _ : IsFractionRing k[X] Kt := IsFractionRing.of_field _ _ fun w ↦ by
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff k (w : F)).1 w.2
    refine ⟨r, s, Subtype.ext ?_⟩
    rw [IntermediateField.coe_div]
    change (w : F) = algebraMap Kt F (algebraMap k[X] Kt r) / algebraMap Kt F (algebraMap k[X] Kt s)
    rw [hKtF, hKtF]
    exact hrs
  -- An integral basis of `F/k(t)` and its discriminant.
  obtain ⟨s, β, hβint⟩ := FiniteDimensional.exists_is_basis_integral k[X] Kt F
  have hd : discr Kt β ≠ 0 := discr_not_zero_of_basis Kt β
  obtain ⟨d₀, hd₀⟩ := IsIntegrallyClosed.isIntegral_iff.1 (discr_isIntegral Kt hβint)
  have hd₀0 : d₀ ≠ 0 := by
    rintro rfl
    rw [map_zero] at hd₀
    exact hd hd₀.symm
  have hu : aeval t d₀ ≠ 0 := fun h0 ↦ hd₀0 (hinj_t (h0.trans (map_zero _).symm))
  -- `L[X]` acts on `L ⊗ F` and on its fraction field through `1 ⊗ t`.
  let _ : Algebra L[X] (L ⊗[k] F) := (aeval ((1 : L) ⊗ₜ[k] t)).toRingHom.toAlgebra
  have hLX : ∀ q : L[X], algebraMap L[X] (L ⊗[k] F) q = aeval ((1 : L) ⊗ₜ[k] t) q :=
    fun _ ↦ rfl
  have _ : FaithfulSMul L[X] 𝓕 := (faithfulSMul_iff_algebraMap_injective _ _).2 (by
    rw [IsScalarTower.algebraMap_eq L[X] (L ⊗[k] F) 𝓕]
    exact hιE.comp (aeval_one_tmul_injective ht))
  let _ : Algebra (FractionRing L[X]) 𝓕 := FractionRing.liftAlgebra L[X] 𝓕
  have _ : IsScalarTower L[X] (FractionRing L[X]) 𝓕 :=
    FractionRing.isScalarTower_liftAlgebra L[X] 𝓕
  -- `k(t) → L(X)` compatibly.
  have hg : Function.Injective
      ((algebraMap L[X] (FractionRing L[X])).comp (mapRingHom (algebraMap k L))) :=
    (IsFractionRing.injective L[X] (FractionRing L[X])).comp
      (map_injective _ (algebraMap k L).injective)
  let _ : Algebra Kt (FractionRing L[X]) := (IsFractionRing.lift hg).toAlgebra
  have hθ : ∀ q : k[X], algebraMap Kt (FractionRing L[X]) (algebraMap k[X] Kt q) =
      algebraMap L[X] (FractionRing L[X]) (q.map (algebraMap k L)) := fun q ↦
    IsFractionRing.lift_algebraMap hg q
  -- The map `F → Frac(L ⊗ F)`, `f ↦ 1 ⊗ f`.
  let ψ : F →+* 𝓕 := ιE.comp (Algebra.TensorProduct.includeRight : F →ₐ[k] L ⊗[k] F).toRingHom
  have hψ : ∀ f : F, ψ f = ιE ((1 : L) ⊗ₜ f) := fun _ ↦ rfl
  have hincl : ∀ q : k[X], aeval ((1 : L) ⊗ₜ[k] t) (q.map (algebraMap k L)) =
      (1 : L) ⊗ₜ[k] aeval t q := fun q ↦ by
    rw [aeval_map_algebraMap]
    exact aeval_algHom_apply (Algebra.TensorProduct.includeRight : F →ₐ[k] L ⊗[k] F) t q
  have hψpoly : ∀ q : k[X], ψ (aeval t q) = algebraMap L[X] 𝓕 (q.map (algebraMap k L)) := by
    intro q
    rw [hψ, IsScalarTower.algebraMap_apply L[X] (L ⊗[k] F) 𝓕, hLX, hincl]
  have hcomp : ∀ a : Kt, ψ (algebraMap Kt F a) =
      algebraMap (FractionRing L[X]) 𝓕 (algebraMap Kt (FractionRing L[X]) a) := by
    have h : ψ.comp (algebraMap Kt F) =
        (algebraMap (FractionRing L[X]) 𝓕).comp (algebraMap Kt (FractionRing L[X])) := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors k[X]) (RingHom.ext fun q ↦ ?_)
      simp only [RingHom.comp_apply]
      rw [hKtF, hψpoly, hθ, ← IsScalarTower.algebraMap_apply]
    exact fun a ↦ RingHom.congr_fun h a
  -- The images `1 ⊗ β i` form a basis of `Frac(L ⊗ F)` over `L(X)`.
  have hβk : ∀ q : s → k[X], ∑ i, aeval t (q i) * β i = 0 → ∀ i, q i = 0 := by
    intro q hq i
    have h := Fintype.linearIndependent_iff.1 β.linearIndependent
      (fun j ↦ algebraMap k[X] Kt (q j)) (by simpa only [Algebra.smul_def, hKtF] using hq)
    exact FaithfulSMul.algebraMap_injective k[X] Kt ((h i).trans (map_zero _).symm)
  have hli : LinearIndependent (FractionRing L[X]) fun i ↦ ψ (β i) := by
    rw [← LinearIndependent.iff_fractionRing L[X] (FractionRing L[X]),
      Fintype.linearIndependent_iff]
    intro g hg
    refine eq_zero_of_sum_aeval_one_tmul (L := L) β hβk g (hιE ?_)
    rw [map_zero, ← hg, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, Algebra.smul_def, IsScalarTower.algebraMap_apply L[X] (L ⊗[k] F) 𝓕, hLX]
    rfl
  have halg : ∀ x : L ⊗[k] F, IsAlgebraic L[X] x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul l f =>
      have hl : IsAlgebraic L[X] (l ⊗ₜ[k] (1 : F)) := by
        have : l ⊗ₜ[k] (1 : F) = algebraMap L[X] (L ⊗[k] F) (C l) := by
          rw [hLX, aeval_C]
          rfl
        rw [this]
        exact isAlgebraic_algebraMap _
      have hf : IsAlgebraic L[X] ((1 : L) ⊗ₜ[k] f) := by
        obtain ⟨q, hq0, hqf⟩ :=
          (IsFractionRing.isAlgebraic_iff k[X] Kt F).2 (Algebra.IsAlgebraic.isAlgebraic f)
        refine ⟨q.map (mapRingHom (algebraMap k L)),
          (Polynomial.map_ne_zero_iff (map_injective _ (algebraMap k L).injective)).2 hq0, ?_⟩
        have hcompat : (algebraMap L[X] (L ⊗[k] F)).comp (mapRingHom (algebraMap k L)) =
            (Algebra.TensorProduct.includeRight : F →ₐ[k] L ⊗[k] F).toRingHom.comp
              (algebraMap k[X] F) :=
          RingHom.ext fun r ↦ hincl r
        rw [aeval_def, eval₂_map, hcompat,
          show (1 : L) ⊗ₜ[k] f = (Algebra.TensorProduct.includeRight : F →ₐ[k] L ⊗[k] F).toRingHom f
            from rfl, ← hom_eval₂, ← aeval_def, hqf, map_zero]
      have := hl.mul hf
      rwa [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul] at this
    | add x y hx hy => exact hx.add hy
  have hspan_img : ∀ y : L ⊗[k] F,
      ιE y ∈ Submodule.span (FractionRing L[X]) (Set.range fun i ↦ ψ (β i)) := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul l f =>
      rw [← β.sum_repr f, TensorProduct.tmul_sum, map_sum]
      refine Submodule.sum_mem _ fun i _ ↦ ?_
      have hl : ιE (l ⊗ₜ[k] (1 : F)) =
          algebraMap (FractionRing L[X]) 𝓕 (algebraMap L[X] (FractionRing L[X]) (C l)) := by
        rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply L[X] (L ⊗[k] F) 𝓕,
          hLX, aeval_C]
        rfl
      have : ιE (l ⊗ₜ[k] (β.repr f i • β i)) =
          (algebraMap L[X] (FractionRing L[X]) (C l) *
            algebraMap Kt (FractionRing L[X]) (β.repr f i)) • ψ (β i) := by
        have hsplit : l ⊗ₜ[k] (β.repr f i • β i) = (l ⊗ₜ[k] (1 : F)) *
            (((1 : L) ⊗ₜ[k] algebraMap Kt F (β.repr f i)) * ((1 : L) ⊗ₜ[k] β i)) := by
          rw [Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul,
            Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one, one_mul]
        rw [hsplit, map_mul, map_mul, hl, ← hψ, ← hψ, hcomp, Algebra.smul_def, map_mul, mul_assoc]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy
  have hsp : ⊤ ≤ Submodule.span (FractionRing L[X]) (Set.range fun i ↦ ψ (β i)) := by
    rintro w -
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := L ⊗[k] F) w
    obtain ⟨r, hr0, c, hc⟩ := (halg b).exists_nonzero_dvd hb
    have hbc : ιE b * ιE c = algebraMap L[X] 𝓕 r := by
      rw [← map_mul, ← hc]
      exact (IsScalarTower.algebraMap_apply L[X] (L ⊗[k] F) 𝓕 r).symm
    have hr : algebraMap L[X] 𝓕 r ≠ 0 :=
      (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective L[X] 𝓕)).2 hr0
    have hb0 : ιE b ≠ 0 := fun h ↦ hr (by rw [← hbc, h, zero_mul])
    have hc0 : ιE c ≠ 0 := fun h ↦ hr (by rw [← hbc, h, mul_zero])
    have hw : ιE a / ιE b = (algebraMap L[X] (FractionRing L[X]) r)⁻¹ • ιE (a * c) := by
      rw [Algebra.smul_def, map_inv₀, ← IsScalarTower.algebraMap_apply, map_mul, ← hbc,
        ← div_eq_inv_mul, mul_div_mul_right _ _ hc0]
    rw [hw]
    exact Submodule.smul_mem _ _ (hspan_img _)
  let b' : Module.Basis s (FractionRing L[X]) 𝓕 := Module.Basis.mk hli hsp
  have hb' : ∀ i, b' i = ψ (β i) := fun i ↦ Module.Basis.mk_apply hli hsp i
  -- Its discriminant is the image of `d₀ ∈ k[X]`.
  have hdisc : discr (FractionRing L[X]) b' =
      algebraMap L[X] (FractionRing L[X]) (d₀.map (algebraMap k L)) := by
    rw [discr_map_of_compatible β b' ψ (fun i ↦ (hb' i).symm) hcomp, ← hd₀, hθ]
  have hb'int : ∀ i, IsIntegral L[X] (b' i) := by
    intro i
    rw [hb']
    obtain ⟨q, hq, hqβ⟩ := hβint i
    refine ⟨q.map (mapRingHom (algebraMap k L)), hq.map _, ?_⟩
    have hcompat : (algebraMap L[X] 𝓕).comp (mapRingHom (algebraMap k L)) =
        ψ.comp (algebraMap k[X] F) := RingHom.ext fun r ↦ (hψpoly r).symm
    rw [eval₂_map, hcompat, ← hom_eval₂, hqβ, map_zero]
  have hzint : IsIntegral L[X] z :=
    ⟨p, hp, by rw [IsScalarTower.algebraMap_eq L[X] (L ⊗[k] F) 𝓕]; exact hz⟩
  have hdisc0 : discr (FractionRing L[X]) b' ≠ 0 := by
    rw [hdisc]
    exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).2
      ((Polynomial.map_ne_zero_iff (algebraMap k L).injective).2 hd₀0)
  have hmem := discr_smul_mem_span_of_isIntegral b' hb'int hdisc0 hzint
  have hle : Submodule.span L[X] (Set.range b') ≤
      LinearMap.range (IsScalarTower.toAlgHom L[X] (L ⊗[k] F) 𝓕).toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨(1 : L) ⊗ₜ β i, (hb' i).symm⟩
  obtain ⟨w, hw⟩ := hle hmem
  have hdz : discr (FractionRing L[X]) b' • z = ψ (aeval t d₀) * z := by
    rw [Algebra.smul_def, hdisc, ← IsScalarTower.algebraMap_apply, hψpoly]
  refine ⟨((1 : L) ⊗ₜ (aeval t d₀)⁻¹) * w, ?_⟩
  rw [map_mul, show ιE w = discr (FractionRing L[X]) b' • z from hw, hdz, hψ, ← mul_assoc,
    ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, inv_mul_cancel₀ hu,
    ← Algebra.TensorProduct.one_def, map_one, one_mul]


-- @@ L939-945 verbatim
variable (L) in
/-- The canonical map `L ⊗[k] B → Frac(L ⊗[k] F)`, where `B` is the integral closure of `k[t]`
in `F`. -/
def integralClosureBaseChange (t : F) :
    L ⊗[k] ((integralClosure (Algebra.adjoin k ({t} : Set F)) F).restrictScalars k) →ₐ[k]
      FractionRing (L ⊗[k] F) :=
  (IsScalarTower.toAlgHom k (L ⊗[k] F) 𝓕).comp (baseChangeIncl L _)


-- @@ L947-950 verbatim
omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
theorem integralClosureBaseChange_injective (t : F) :
    Function.Injective (integralClosureBaseChange (k := k) L t) :=
  (IsFractionRing.injective (L ⊗[k] F) 𝓕).comp (baseChangeIncl_injective (L := L) _)


-- @@ L952-967 verbatim
omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
private theorem algebraMap_one_tmul_mem_adjoin {t : F} {a : F}
    (ha : a ∈ Algebra.adjoin k ({t} : Set F)) :
    algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ a) ∈
      Algebra.adjoin L {algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ t)} := by
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha ⊢
  obtain ⟨q, rfl⟩ := ha
  refine ⟨q.map (algebraMap k L), ?_⟩
  change aeval _ _ = _
  rw [show algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ t) =
      IsScalarTower.toAlgHom L (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ t) from rfl,
    aeval_algHom_apply]
  change algebraMap (L ⊗[k] F) _ _ = algebraMap (L ⊗[k] F) _ _
  congr 1
  rw [aeval_map_algebraMap]
  exact aeval_algHom_apply (Algebra.TensorProduct.includeRight : F →ₐ[k] L ⊗[k] F) t q


-- @@ L969-1075 verbatim
/-- **Normalization commutes with constant field extension.** For a transcendental `t` with
`F/k(t)` separable, an element of `Frac(L ⊗[k] F)` is integral over `L[1 ⊗ t]` iff it lies in
the image of `L ⊗[k] B`, where `B` is the integral closure of `k[t]` in `F`. -/
theorem isIntegral_adjoin_iff_mem_range {t : F} (ht : Transcendental k t)
    [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F]
    (z : FractionRing (L ⊗[k] F)) :
    IsIntegral (Algebra.adjoin L
        {algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ t)}) z ↔
      z ∈ (integralClosureBaseChange L t).range := by
  classical
  set ιE := algebraMap (L ⊗[k] F) 𝓕
  set T := ιE ((1 : L) ⊗ₜ t)
  set S := Algebra.adjoin L ({T} : Set 𝓕)
  have hT : ∀ q : L[X], aeval T q = ιE (aeval ((1 : L) ⊗ₜ[k] t) q) := fun q ↦
    aeval_algHom_apply (IsScalarTower.toAlgHom L (L ⊗[k] F) 𝓕) _ q
  have hS : S = (aeval T).range := Algebra.adjoin_singleton_eq_range_aeval L T
  constructor
  · intro hz
    -- Lift a monic equation over `S` to `L[X]`.
    let f : L[X] →ₐ[L] S := (aeval T).codRestrict S fun q ↦ by
      rw [hS]
      exact ⟨q, rfl⟩
    have hf : Function.Surjective f := by
      rintro ⟨c, hc⟩
      rw [hS] at hc
      obtain ⟨q, rfl⟩ := hc
      exact ⟨q, rfl⟩
    obtain ⟨P, hPm, hPz⟩ := hz
    obtain ⟨q, hqP, -, hqm⟩ := lifts_and_natDegree_eq_and_monic
      ((lifts_iff_coeff_lifts P).2 fun n ↦ hf (P.coeff n)) hPm
    have hq : q.eval₂ (ιE.comp (aeval ((1 : L) ⊗ₜ[k] t)).toRingHom) z = 0 := by
      have hcomp : ιE.comp (aeval ((1 : L) ⊗ₜ[k] t)).toRingHom =
          (algebraMap S 𝓕).comp f.toRingHom := RingHom.ext fun r ↦ (hT r).symm
      rw [hcomp, ← eval₂_map, hqP]
      exact hPz
    obtain ⟨y, rfl⟩ := exists_algebraMap_eq_of_monic ht hqm hq
    -- Transport the equation to `L ⊗[k] k[t]` and apply the integrality at places.
    let tA : Algebra.adjoin k ({t} : Set F) := ⟨t, Algebra.subset_adjoin rfl⟩
    let ρ : L[X] →+* L ⊗[k] Algebra.adjoin k ({t} : Set F) :=
      (Algebra.TensorProduct.map (AlgHom.id k L) (aeval tA)).toRingHom.comp
        (polyEquivTensor k L).toAlgHom.toRingHom
    have hmapA : (baseChangeIncl L (Algebra.adjoin k ({t} : Set F))).comp
        (Algebra.TensorProduct.map (AlgHom.id k L) (aeval tA)) =
          Algebra.TensorProduct.map (AlgHom.id k L) (aeval t : k[X] →ₐ[k] F) := by
      refine Algebra.TensorProduct.ext' fun l r ↦ ?_
      rw [AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
        baseChangeIncl_tmul]
      congr 1
      exact (aeval_algHom_apply (Algebra.adjoin k ({t} : Set F)).val tA r).symm
    have hρ : (baseChangeIncl L (Algebra.adjoin k ({t} : Set F))).toRingHom.comp ρ =
        (aeval ((1 : L) ⊗ₜ[k] t)).toRingHom := by
      refine RingHom.ext fun r ↦ ?_
      change baseChangeIncl L (Algebra.adjoin k ({t} : Set F))
        (Algebra.TensorProduct.map (AlgHom.id k L) (aeval tA)
        (polyEquivTensor k L r)) = aeval ((1 : L) ⊗ₜ[k] t) r
      rw [aeval_one_tmul_eq_map, ← hmapA]
      rfl
    have hιE : Function.Injective ιE := IsFractionRing.injective _ _
    have hQ : (q.map ρ).eval₂ (baseChangeIncl L (Algebra.adjoin k ({t} : Set F))).toRingHom y =
        0 := by
      rw [eval₂_map, hρ]
      apply hιE
      rw [map_zero, hom_eval₂]
      exact hq
    obtain ⟨w, hw⟩ := mem_range_integralClosure_of_monic (hqm.map ρ) hQ
    refine ⟨w, ?_⟩
    change ιE (baseChangeIncl L
      ((integralClosure (Algebra.adjoin k ({t} : Set F)) F).restrictScalars k) w) = ιE y
    rw [show baseChangeIncl L
      ((integralClosure (Algebra.adjoin k ({t} : Set F)) F).restrictScalars k) w = y from hw]
  · rintro ⟨w, rfl⟩
    induction w using TensorProduct.inductionOn with
    | tmul l b =>
      have hsplit : integralClosureBaseChange L t (l ⊗ₜ b) =
          algebraMap L 𝓕 l * ιE ((1 : L) ⊗ₜ (b : F)) := by
        change ιE (l ⊗ₜ (b : F)) = _
        rw [IsScalarTower.algebraMap_apply L (L ⊗[k] F) 𝓕, ← map_mul,
          Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
          one_mul]
        rfl
      change IsIntegral S (integralClosureBaseChange L t (l ⊗ₜ b))
      rw [hsplit]
      refine IsIntegral.mul ?_ ?_
      · exact isIntegral_algebraMap (x := (⟨_, S.algebraMap_mem l⟩ : S))
      · obtain ⟨P, hPm, hPb⟩ := (mem_integralClosure_iff _ _).1 b.2
        let χ : Algebra.adjoin k ({t} : Set F) →+* S :=
          { toFun := fun a ↦ ⟨ιE ((1 : L) ⊗ₜ (a : F)), algebraMap_one_tmul_mem_adjoin a.2⟩
            map_one' := by
              ext
              change ιE ((1 : L) ⊗ₜ (1 : F)) = 1
              rw [← Algebra.TensorProduct.one_def, map_one]
            map_mul' := fun a a' ↦ by
              ext
              change ιE ((1 : L) ⊗ₜ ((a : F) * a')) = ιE ((1 : L) ⊗ₜ (a : F)) * ιE ((1 : L) ⊗ₜ a')
              rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
            map_zero' := by ext; simp
            map_add' := fun a a' ↦ by ext; simp [TensorProduct.tmul_add] }
        refine ⟨P.map χ, hPm.map χ, ?_⟩
        have hcomp : (algebraMap S 𝓕).comp χ = (ιE.comp
            (Algebra.TensorProduct.includeRight : F →ₐ[k] L ⊗[k] F).toRingHom).comp
              (algebraMap (Algebra.adjoin k ({t} : Set F)) F) := RingHom.ext fun _ ↦ rfl
        rw [eval₂_map, hcomp, show ιE ((1 : L) ⊗ₜ (b : F)) = (ιE.comp
            (Algebra.TensorProduct.includeRight : F →ₐ[k] L ⊗[k] F).toRingHom) (b : F) from rfl,
          ← hom_eval₂, hPb, map_zero]
    | add v w hv hw =>
      rw [map_add]
      exact hv.add hw


-- @@ L1077-1087 verbatim
/-- **Normality.** The image of `L ⊗[k] B` in `Frac(L ⊗[k] F)` is the integral closure of
`L[1 ⊗ t]` there. Normality follows by rewriting along this equality with Mathlib's instance
`IsIntegrallyClosedIn (integralClosure R A).toSubring A`. -/
theorem range_toSubring_eq_integralClosure {t : F} (ht : Transcendental k t)
    [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F] :
    (integralClosureBaseChange L t).range.toSubring =
      (integralClosure (Algebra.adjoin L {algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t)})
        𝓕).toSubring :=
  Subring.ext fun z ↦ by
    rw [Subalgebra.mem_toSubring, Subalgebra.mem_toSubring, mem_integralClosure_iff,
      isIntegral_adjoin_iff_mem_range ht]


-- @@ L1089-1089 verbatim
/-! ### Places of `Frac(L ⊗[k] F)` -/


-- @@ L1091-1151 verbatim
/-- `Frac(L ⊗[k] F)` is a finite separable extension of `L(1 ⊗ t)`. -/
theorem finiteDimensional_isSeparable_adjoin {t : F} (ht : Transcendental k t)
    [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F] :
    FiniteDimensional (IntermediateField.adjoin L {algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t)})
        𝓕 ∧
      Algebra.IsSeparable
        (IntermediateField.adjoin L {algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t)}) 𝓕 := by
  classical
  set K := IntermediateField.adjoin L {algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t)}
  set Kt := IntermediateField.adjoin k ({t} : Set F)
  have _ : FiniteDimensional Kt F := finiteDimensional_adjoin_of_transcendental ht
  let ψ : F →+* 𝓕 := (algebraMap (L ⊗[k] F) 𝓕).comp
    (Algebra.TensorProduct.includeRight : F →ₐ[k] L ⊗[k] F).toRingHom
  have hAK := IntermediateField.algebra_adjoin_le_adjoin L
    ({algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t)} : Set 𝓕)
  -- `ψ` maps `k(t)` into `L(T)`.
  have hψK : ∀ c : Kt, ψ c ∈ K := by
    intro c
    obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff k (c : F)).1 c.2
    rw [hrs, map_div₀]
    exact div_mem (hAK (algebraMap_one_tmul_mem_adjoin (L := L) (aeval_mem_adjoin_singleton k t)))
      (hAK (algebraMap_one_tmul_mem_adjoin (L := L) (aeval_mem_adjoin_singleton k t)))
  let σ : Kt →+* K := (ψ.comp (algebraMap Kt F)).codRestrict K hψK
  have hσ : (algebraMap K 𝓕).comp σ = ψ.comp (algebraMap Kt F) := RingHom.ext fun _ ↦ rfl
  -- A primitive element of `F/k(t)` and its image.
  obtain ⟨α, hα⟩ := Field.exists_primitive_element Kt F
  have hαint : IsIntegral Kt α := .of_finite Kt α
  have hroot : ((minpoly Kt α).map σ).eval₂ (algebraMap K 𝓕) (ψ α) = 0 := by
    rw [eval₂_map, hσ, ← hom_eval₂, ← aeval_def, minpoly.aeval, map_zero]
  have hint : IsIntegral K (ψ α) := ⟨_, (minpoly.monic hαint).map σ, hroot⟩
  have hsepK : (minpoly K (ψ α)).Separable :=
    (Polynomial.Separable.map (Algebra.IsSeparable.isSeparable Kt α)).of_dvd
      (minpoly.dvd K (ψ α) (by rwa [aeval_def]))
  set E := IntermediateField.adjoin K ({ψ α} : Set 𝓕)
  -- `L(T)(ψ α)` is all of `Frac(L ⊗[k] F)`.
  have hF : ∀ f : F, ψ f ∈ E := by
    let E' : IntermediateField Kt F :=
      Subfield.toIntermediateField (E.toSubfield.comap ψ) fun c ↦ E.algebraMap_mem (σ c)
    have hle : IntermediateField.adjoin Kt {α} ≤ E' :=
      IntermediateField.adjoin_simple_le_iff.2 (IntermediateField.mem_adjoin_simple_self K (ψ α))
    exact fun f ↦ hle (by rw [hα]; exact IntermediateField.mem_top)
  have hLF : ∀ y : L ⊗[k] F, algebraMap (L ⊗[k] F) 𝓕 y ∈ E := fun y ↦ by
    induction y using TensorProduct.inductionOn with
    | tmul l f =>
      rw [show l ⊗ₜ[k] f = algebraMap L (L ⊗[k] F) l * ((1 : L) ⊗ₜ f) by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
          one_mul]
        rfl, map_mul]
      refine mul_mem ?_ (hF f)
      rw [← IsScalarTower.algebraMap_apply]
      exact E.algebraMap_mem ⟨algebraMap L 𝓕 l, K.algebraMap_mem l⟩
    | add y z hy hz => rw [map_add]; exact add_mem hy hz
  have hE : E = ⊤ := by
    refine eq_top_iff.2 fun x _ ↦ ?_
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := L ⊗[k] F) x
    exact div_mem (hLF a) (hLF b)
  have _ : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hint
  have _ : Algebra.IsSeparable K E :=
    (IntermediateField.isSeparable_adjoin_simple_iff_isSeparable K 𝓕).2 hsepK
  let e : E ≃ₐ[K] 𝓕 := (IntermediateField.equivOfEq hE).trans IntermediateField.topEquiv
  exact ⟨e.toLinearEquiv.finiteDimensional, Algebra.IsSeparable.of_algHom K E e.symm.toAlgHom⟩


-- @@ L1153-1168 verbatim
/-- **Places of `Frac(L ⊗[k] F)` are localizations of the integral closure.** Let `V` be a
proper valuation subring of `Frac(L ⊗[k] F)` containing `L` and `T = 1 ⊗ t`. Then `V`
contains the integral closure `R` of `L[T]`, its centre on `R` is a nonzero prime, and `V` is
the localization of `R` at that prime. -/
theorem valuationSubring_eq_ofPrime {t : F} (ht : Transcendental k t)
    [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F]
    (V : ValuationSubring 𝓕) (hLV : ∀ l : L, algebraMap L 𝓕 l ∈ V) (hV : V ≠ ⊤)
    (hT : algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t) ∈ V) :
    ∃ h : (integralClosure (Algebra.adjoin L {algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t)})
        𝓕).toSubring ≤ V.toSubring,
      centre _ V h ≠ ⊥ ∧ V.toLocalSubring = LocalSubring.ofPrime _ (centre _ V h) := by
  obtain ⟨_, _⟩ := finiteDimensional_isSeparable_adjoin (L := L) ht
  obtain ⟨_, _⟩ := isDedekindDomain_integralClosure_adjoin (K₀ := L)
    (algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t))
  have h := integralClosure_adjoin_le V hLV hT
  exact ⟨h, centre_ne_bot_and_eq_ofPrime _ V h hV⟩


-- @@ L1170-1182 verbatim
/-- Elementwise form of `valuationSubring_eq_ofPrime`. -/
theorem mem_valuationSubring_iff_of_mem {t : F} (ht : Transcendental k t)
    [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F]
    (V : ValuationSubring 𝓕) (hLV : ∀ l : L, algebraMap L 𝓕 l ∈ V) (hV : V ≠ ⊤)
    (hT : algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t) ∈ V) (x : 𝓕) :
    x ∈ V ↔ ∃ a ∈ integralClosure (Algebra.adjoin L
        {algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t)}) 𝓕,
      ∃ s ∈ integralClosure (Algebra.adjoin L {algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t)}) 𝓕,
        s ≠ 0 ∧ s⁻¹ ∈ V ∧ x = a / s := by
  obtain ⟨_, _⟩ := finiteDimensional_isSeparable_adjoin (L := L) ht
  obtain ⟨_, _⟩ := isDedekindDomain_integralClosure_adjoin (K₀ := L)
    (algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t))
  exact mem_valuationSubring_iff _ V (integralClosure_adjoin_le V hLV hT) hV x


-- @@ L1184-1194 verbatim
omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- The inverse of a transcendental element is transcendental and generates the same
field. -/
theorem transcendental_inv_and_adjoin_inv {t : F} (ht : Transcendental k t) :
    Transcendental k t⁻¹ ∧
      IntermediateField.adjoin k ({t⁻¹} : Set F) = IntermediateField.adjoin k {t} :=
  ⟨fun h ↦ ht (IsAlgebraic.inv_iff.1 h), le_antisymm
    (IntermediateField.adjoin_simple_le_iff.2
      (inv_mem (IntermediateField.mem_adjoin_simple_self k t)))
    (IntermediateField.adjoin_simple_le_iff.2 (by
      simpa using inv_mem (IntermediateField.mem_adjoin_simple_self k t⁻¹)))⟩


-- @@ L1196-1202 verbatim
omit [IsFunctionFieldOneVar k F] in
/-- `1 ⊗ t⁻¹` is the inverse of `1 ⊗ t` in `Frac(L ⊗[k] F)`. -/
theorem algebraMap_one_tmul_inv (t : F) :
    algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t⁻¹) =
      (algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t))⁻¹ :=
  map_inv₀ ((algebraMap (L ⊗[k] F) 𝓕).comp
    (Algebra.TensorProduct.includeRight : F →ₐ[k] L ⊗[k] F).toRingHom) t


-- @@ L1204-1219 verbatim
/-- `valuationSubring_eq_ofPrime` when `T = 1 ⊗ t ∉ V`: then `V` is a localization of the
integral closure of `L[T⁻¹]`. -/
theorem valuationSubring_eq_ofPrime_inv {t : F} (ht : Transcendental k t)
    [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F]
    (V : ValuationSubring 𝓕) (hLV : ∀ l : L, algebraMap L 𝓕 l ∈ V) (hV : V ≠ ⊤)
    (hT : algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t) ∉ V) :
    ∃ h : (integralClosure (Algebra.adjoin L
        {(algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t))⁻¹}) 𝓕).toSubring ≤ V.toSubring,
      centre _ V h ≠ ⊥ ∧ V.toLocalSubring = LocalSubring.ofPrime _ (centre _ V h) := by
  obtain ⟨ht', hadj⟩ := transcendental_inv_and_adjoin_inv ht
  have _ : Algebra.IsSeparable (IntermediateField.adjoin k ({t⁻¹} : Set F)) F := by
    rw [hadj]; infer_instance
  rw [← algebraMap_one_tmul_inv]
  refine valuationSubring_eq_ofPrime ht' V hLV hV ?_
  rw [algebraMap_one_tmul_inv]
  exact (V.mem_or_inv_mem _).resolve_left hT


-- @@ L1221-1237 verbatim
/-- Elementwise form of `valuationSubring_eq_ofPrime_inv`. -/
theorem mem_valuationSubring_iff_of_notMem {t : F} (ht : Transcendental k t)
    [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F]
    (V : ValuationSubring 𝓕) (hLV : ∀ l : L, algebraMap L 𝓕 l ∈ V) (hV : V ≠ ⊤)
    (hT : algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t) ∉ V) (x : 𝓕) :
    x ∈ V ↔ ∃ a ∈ integralClosure (Algebra.adjoin L
        {(algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t))⁻¹}) 𝓕,
      ∃ s ∈ integralClosure (Algebra.adjoin L
        {(algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t))⁻¹}) 𝓕,
        s ≠ 0 ∧ s⁻¹ ∈ V ∧ x = a / s := by
  obtain ⟨ht', hadj⟩ := transcendental_inv_and_adjoin_inv ht
  have _ : Algebra.IsSeparable (IntermediateField.adjoin k ({t⁻¹} : Set F)) F := by
    rw [hadj]; infer_instance
  rw [← algebraMap_one_tmul_inv]
  refine mem_valuationSubring_iff_of_mem ht' V hLV hV ?_ x
  rw [algebraMap_one_tmul_inv]
  exact (V.mem_or_inv_mem _).resolve_left hT


-- @@ L1239-1269 verbatim
/-- **Coefficient regularity.** A derivation of `Frac(L ⊗[k] F)`, over any base ring, which
preserves the integral closures of `L[T]` and of `L[T⁻¹]` (`T = 1 ⊗ t`) preserves every proper
valuation subring containing `L`. -/
theorem derivation_mem_valuationSubring_of_integralClosure {A : Type*} [CommRing A]
    [Algebra A 𝓕] {t : F} (ht : Transcendental k t)
    [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F] (D : Derivation A 𝓕 𝓕)
    (hD : ∀ x ∈ integralClosure (Algebra.adjoin L
        {algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t)}) 𝓕,
      D x ∈ integralClosure (Algebra.adjoin L {algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t)}) 𝓕)
    (hD' : ∀ x ∈ integralClosure (Algebra.adjoin L
        {(algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t))⁻¹}) 𝓕,
      D x ∈ integralClosure (Algebra.adjoin L
        {(algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t))⁻¹}) 𝓕)
    (V : ValuationSubring 𝓕) (hLV : ∀ l : L, algebraMap L 𝓕 l ∈ V) (hV : V ≠ ⊤) {x : 𝓕}
    (hx : x ∈ V) : D x ∈ V := by
  by_cases hT : algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t) ∈ V
  · obtain ⟨_, _⟩ := finiteDimensional_isSeparable_adjoin (L := L) ht
    obtain ⟨_, _⟩ := isDedekindDomain_integralClosure_adjoin (K₀ := L)
      (algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t))
    exact derivation_mem_valuationSubring D _ hD V (integralClosure_adjoin_le V hLV hT) hV hx
  · obtain ⟨ht', hadj⟩ := transcendental_inv_and_adjoin_inv ht
    have _ : Algebra.IsSeparable (IntermediateField.adjoin k ({t⁻¹} : Set F)) F := by
      rw [hadj]; infer_instance
    rw [← algebraMap_one_tmul_inv] at hD'
    have hT' : algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t⁻¹) ∈ V := by
      rw [algebraMap_one_tmul_inv]
      exact (V.mem_or_inv_mem _).resolve_left hT
    obtain ⟨_, _⟩ := finiteDimensional_isSeparable_adjoin (L := L) ht'
    obtain ⟨_, _⟩ := isDedekindDomain_integralClosure_adjoin (K₀ := L)
      (algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t⁻¹))
    exact derivation_mem_valuationSubring D _ hD' V (integralClosure_adjoin_le V hLV hT') hV hx


-- @@ L1271-1301 verbatim
private theorem derivation_mem_integralClosure_of_horizontal {A : Type*} [CommRing A]
    [Algebra A 𝓕] {t : F} (ht : Transcendental k t)
    [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F] (D : Derivation A 𝓕 𝓕)
    (hL : ∀ l : L, D (algebraMap L 𝓕 l) ∈ (algebraMap L 𝓕).range)
    (hF : ∀ f : F, D (algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] f)) = 0) :
    ∀ x ∈ integralClosure (Algebra.adjoin L {algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t)}) 𝓕,
      D x ∈ integralClosure (Algebra.adjoin L {algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] t)}) 𝓕 := by
  have hprod : ∀ (l : L)
      (b : (integralClosure (Algebra.adjoin k ({t} : Set F)) F).restrictScalars k),
      integralClosureBaseChange L t (l ⊗ₜ b) =
        algebraMap L 𝓕 l * algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ (b : F)) := fun l b ↦ by
    change algebraMap (L ⊗[k] F) 𝓕 (baseChangeIncl L
      ((integralClosure (Algebra.adjoin k ({t} : Set F)) F).restrictScalars k) (l ⊗ₜ b)) = _
    rw [baseChangeIncl_tmul, IsScalarTower.algebraMap_apply L (L ⊗[k] F) 𝓕, ← map_mul,
      Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul]
    rfl
  have key : ∀ w, D (integralClosureBaseChange L t w) ∈ (integralClosureBaseChange L t).range := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul l b =>
      obtain ⟨l', hl'⟩ := hL l
      refine (AlgHom.mem_range _).2 ⟨l' ⊗ₜ b, ?_⟩
      rw [hprod, hprod, Derivation.leibniz, hF, smul_zero, zero_add, ← hl', smul_eq_mul, mul_comm]
    | add v w hv hw =>
      rw [map_add, map_add]
      exact add_mem hv hw
  intro x hx
  rw [mem_integralClosure_iff, isIntegral_adjoin_iff_mem_range ht] at hx ⊢
  obtain ⟨w, rfl⟩ := (AlgHom.mem_range _).1 hx
  exact key w


-- @@ L1303-1319 verbatim
/-- **Horizontal derivations are regular.** A derivation of `Frac(L ⊗[k] F)`, over any base
ring, which maps `L` into `L` and kills `1 ⊗ F` preserves every proper valuation subring
containing `L`. This applies to the lift of a coefficient derivation of `L`. -/
theorem derivation_mem_valuationSubring_of_horizontal {A : Type*} [CommRing A] [Algebra A 𝓕]
    {t : F} (ht : Transcendental k t)
    [Algebra.IsSeparable (IntermediateField.adjoin k ({t} : Set F)) F] (D : Derivation A 𝓕 𝓕)
    (hL : ∀ l : L, D (algebraMap L 𝓕 l) ∈ (algebraMap L 𝓕).range)
    (hF : ∀ f : F, D (algebraMap (L ⊗[k] F) 𝓕 ((1 : L) ⊗ₜ[k] f)) = 0)
    (V : ValuationSubring 𝓕) (hLV : ∀ l : L, algebraMap L 𝓕 l ∈ V) (hV : V ≠ ⊤) {x : 𝓕}
    (hx : x ∈ V) : D x ∈ V := by
  obtain ⟨ht', hadj⟩ := transcendental_inv_and_adjoin_inv ht
  have _ : Algebra.IsSeparable (IntermediateField.adjoin k ({t⁻¹} : Set F)) F := by
    rw [hadj]; infer_instance
  have hD' := derivation_mem_integralClosure_of_horizontal ht' D hL hF
  rw [algebraMap_one_tmul_inv] at hD'
  exact derivation_mem_valuationSubring_of_integralClosure ht D
    (derivation_mem_integralClosure_of_horizontal ht D hL hF) hD' V hLV hV hx


-- @@ L1321-1321 verbatim
end FractionField


-- @@ L1323-1323 verbatim
end


-- @@ L1325-1325 verbatim
end AclGeom
