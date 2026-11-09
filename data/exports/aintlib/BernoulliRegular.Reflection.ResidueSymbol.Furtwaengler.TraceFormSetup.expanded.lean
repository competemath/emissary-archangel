module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.IntegralBridge
public import Mathlib.FieldTheory.Finite.Trace
public import Mathlib.Algebra.GroupWithZero.Units.Equiv


-- @@ L7-39 verbatim
/-!
# Trace-form Stickelberger setup (REF-18c2c4-L2c1)

Refines `ConcreteStickelbergerSetup` to additive characters of the
canonical trace form

  `ψ(x) = ζ_ℓ ^ Tr_{k/𝔽_ℓ}(c · x)`

for some scale `c ∈ kˣ`. Every primitive additive character on
`k = 𝔽_{ℓ ^ f}` has this shape, so the refinement does not lose
generality, and the trace witness pins down the exponent in the form
needed by the digit-sum Stickelberger argument (REF-18c2c4-L2c2 / L2c3).

This is REF-18c2c4-L2c1 of the Furtwängler digit-sum Stickelberger route.

## Main definitions

* `TraceFormStickelbergerSetup`: extends `ConcreteStickelbergerSetup`
  with a scale `traceScale : kˣ` and a witness that the existing
  exponent function equals `(Algebra.trace (ZMod ℓ) k (traceScale·x)).val`.
* `ConcreteStickelbergerSetup.gaussSumIntAtScale`: the integral Gauss
  sum at an arbitrary trace scale, used to state scale-removal
  independent of any bundle's specific choice of `traceScale`.

## Main theorems

* `TraceFormStickelbergerSetup.psiInt_eq_zeta_ell_int_pow_trace`: the
  integral additive character has the trace-form integer-power
  expression.
* `ConcreteStickelbergerSetup.gaussSumIntAtScale_eq_charUnit_mul_one`:
  Gauss sums at different trace scales differ by a multiplicative
  character value at the inverse scale (a unit in `𝓞 R'`).
-/


-- @@ L41-41 verbatim
@[expose] public section


-- @@ L43-43 verbatim
noncomputable section


-- @@ L45-45 verbatim
open scoped NumberField


-- @@ L47-47 verbatim
namespace BernoulliRegular


-- @@ L49-49 verbatim
namespace Furtwaengler


-- @@ L51-51 verbatim
universe u v w


-- @@ L53-81 verbatim
/-- Refinement of `ConcreteStickelbergerSetup` to additive characters of
the canonical trace form `ψ(x) = ζ_ℓ ^ Tr(c · x)` for some scale
`c ∈ kˣ`. -/
structure TraceFormStickelbergerSetup
    (ℓ p : ℕ) [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type w) [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
      [IsCyclotomicExtension {p, ℓ} ℚ R'] extends
    ConcreteStickelbergerSetup ℓ p k K R' where
  /-- Scale factor for the additive character. Every primitive additive
  character on `k = 𝔽_{ℓ ^ f}` has the form `x ↦ ζ_ℓ^{Tr(c · x)}` for some
  unit `c ∈ k×`. -/
  traceScale : kˣ
  /-- Witness that the bundle's `psiExponent` agrees with the
  natural-number lift of the absolute trace at the chosen scale. -/
  psiExponent_trace :
    ∀ x : k,
      toConcreteStickelbergerSetup.psiExponent x =
        (Algebra.trace (ZMod ℓ) k ((traceScale : k) * x)).val
  /-- Uniformizer non-degeneracy: `π = ζ_ℓ - 1` is exactly a uniformizer
  at the selected prime `Q`, i.e., `v_Q(π) = 1`. This is a ramification
  fact about the mixed cyclotomic field `R' = ℚ(ζ_p, ζ_ℓ)` that follows
  from the singleton-conductor ramification theorem
  (`IsCyclotomicExtension.Rat.ramificationIdx_eq` with `n = ℓ · p`,
  prime `ℓ`, `m = p`). It is bundled here as a structural constraint
  rather than derived inline; the derivation is tracked separately
  (see the follow-up ticket on the L2c3a board). -/
  pi_not_mem_Q_sq : toConcreteStickelbergerSetup.π ∉ toConcreteStickelbergerSetup.Q ^ 2


-- @@ L83-83 verbatim
namespace TraceFormStickelbergerSetup


-- @@ L85-85 verbatim
variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]

-- @@ L86-86 verbatim
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]

-- @@ L87-87 verbatim
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

-- @@ L88-89 verbatim
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']


-- @@ L91-91 verbatim
variable (S : TraceFormStickelbergerSetup ℓ p k K R')


-- @@ L93-97 verbatim
/-- Trace-form expression for the abstract additive character. -/
theorem psi_eq_zeta_ell_pow_trace (x : k) :
    S.psi x =
      S.zeta_ell ^ ((Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * x)).val) := by
  rw [S.psi_pow_form, S.psiExponent_trace]


-- @@ L99-104 verbatim
/-- Trace-form expression for the integral additive character. -/
theorem psiInt_eq_zeta_ell_int_pow_trace (x : k) :
    S.psiInt x =
      S.zeta_ell_int ^ ((Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * x)).val) := by
  change S.zeta_ell_int ^ S.psiExponent x = _
  rw [S.psiExponent_trace]


-- @@ L106-111 verbatim
/-- Trace-form accessor for the Teichmüller compatibility of
`residueCharInt` modulo `Q`. -/
theorem residueCharInt_residueMap_eq_pow_d (x : kˣ) :
    S.residueMap (S.residueCharInt (x : k)) =
      (x : k) ^ ((Fintype.card k - 1) / p) :=
  S.toConcreteStickelbergerSetup.residueCharInt_residueMap_eq_pow_d x


-- @@ L113-118 verbatim
/-- Unit-lift form of the Teichmüller compatibility. -/
theorem residueCharInt_residueMap_eq_pow_d_of_unit
    (x : kˣ) (u : (𝓞 R')ˣ) (hxu : (x : k) = S.residueMap (u : 𝓞 R')) :
    S.residueMap (S.residueCharInt (x : k)) =
      (S.residueMap (u : 𝓞 R')) ^ ((Fintype.card k - 1) / p) :=
  S.toConcreteStickelbergerSetup.residueCharInt_residueMap_eq_pow_d_of_unit x u hxu


-- @@ L120-120 verbatim
end TraceFormStickelbergerSetup


-- @@ L122-147 verbatim
/-- Conductor-flexible refinement of
`ConductorFlexibleConcreteStickelbergerSetup` to additive characters of the
canonical trace form.

Unlike `TraceFormStickelbergerSetup`, this structure does not require
`[IsCyclotomicExtension {p, ℓ} ℚ R']`; the necessary roots, prime, residue
map, and non-degeneracy facts are explicit fields inherited from the flexible
concrete setup. -/
structure ConductorFlexibleTraceFormStickelbergerSetup
    (ℓ p : ℕ) [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]
    (k : Type u) [Field k] [Fintype k] [Algebra (ZMod ℓ) k]
    (K : Type v) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
    (R' : Type w) [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R'] extends
    ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R' where
  /-- Scale factor for the additive character. -/
  traceScale : kˣ
  /-- Witness that the bundle's `psiExponent` agrees with the trace at the
  chosen scale. -/
  psiExponent_trace :
    ∀ x : k,
      toConductorFlexibleConcreteStickelbergerSetup.psiExponent x =
        (Algebra.trace (ZMod ℓ) k ((traceScale : k) * x)).val
  /-- Uniformizer non-degeneracy at the selected prime. -/
  pi_not_mem_Q_sq :
    toConductorFlexibleConcreteStickelbergerSetup.π ∉
      toConductorFlexibleConcreteStickelbergerSetup.Q ^ 2


-- @@ L149-149 verbatim
namespace ConductorFlexibleTraceFormStickelbergerSetup


-- @@ L151-151 verbatim
variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]

-- @@ L152-152 verbatim
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]

-- @@ L153-153 verbatim
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

-- @@ L154-154 verbatim
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']


-- @@ L156-156 verbatim
variable (S : ConductorFlexibleTraceFormStickelbergerSetup ℓ p k K R')


-- @@ L158-160 verbatim
/-- The underlying conductor-flexible concrete setup. -/
def concrete : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R' :=
  S.toConductorFlexibleConcreteStickelbergerSetup


-- @@ L162-166 verbatim
/-- Trace-form expression for the abstract additive character. -/
theorem psi_eq_zeta_ell_pow_trace (x : k) :
    S.psi x =
      S.zeta_ell ^ ((Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * x)).val) := by
  rw [S.toConductorFlexibleConcreteStickelbergerSetup.psi_pow_form, S.psiExponent_trace]


-- @@ L168-173 verbatim
/-- Trace-form expression for the integral additive character. -/
theorem psiInt_eq_zeta_ell_int_pow_trace (x : k) :
    S.psiInt x =
      S.zeta_ell_int ^ ((Algebra.trace (ZMod ℓ) k ((S.traceScale : k) * x)).val) := by
  change S.zeta_ell_int ^ S.psiExponent x = _
  rw [S.psiExponent_trace]


-- @@ L175-179 verbatim
/-- The integral Gauss sum at an arbitrary trace scale, for conductor-flexible
setups. -/
noncomputable def gaussSumIntAtScale (c : kˣ) (a : ℕ) : 𝓞 R' :=
  ∑ x : k, (S.residueCharInt ^ a) x *
    S.zeta_ell_int ^ ((Algebra.trace (ZMod ℓ) k ((c : k) * x)).val)


-- @@ L181-181 verbatim
end ConductorFlexibleTraceFormStickelbergerSetup


-- @@ L183-183 verbatim
namespace TraceFormStickelbergerSetup


-- @@ L185-185 verbatim
variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]

-- @@ L186-186 verbatim
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]

-- @@ L187-187 verbatim
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

-- @@ L188-189 verbatim
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']


-- @@ L191-199 verbatim
/-- The old exact pair-cyclotomic trace-form setup is a special case of the
conductor-flexible trace-form API. -/
noncomputable def toConductorFlexible (S : TraceFormStickelbergerSetup ℓ p k K R') :
    ConductorFlexibleTraceFormStickelbergerSetup ℓ p k K R' where
  toConductorFlexibleConcreteStickelbergerSetup :=
    S.toConcreteStickelbergerSetup.toConductorFlexible
  traceScale := S.traceScale
  psiExponent_trace := S.psiExponent_trace
  pi_not_mem_Q_sq := S.pi_not_mem_Q_sq


-- @@ L201-201 verbatim
end TraceFormStickelbergerSetup


-- @@ L203-203 verbatim
namespace ConcreteStickelbergerSetup


-- @@ L205-205 verbatim
variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]

-- @@ L206-206 verbatim
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]

-- @@ L207-207 verbatim
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

-- @@ L208-209 verbatim
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']


-- @@ L211-211 verbatim
variable (S : ConcreteStickelbergerSetup ℓ p k K R')


-- @@ L213-219 verbatim
/-- The integral Gauss sum at additive character `x ↦ ζ_ℓ ^ Tr(c · x)`,
parameterised by the trace scale `c ∈ kˣ`. This is independent of the
specific `traceScale` carried by any `TraceFormStickelbergerSetup`
instance. -/
noncomputable def gaussSumIntAtScale (c : kˣ) (a : ℕ) : 𝓞 R' :=
  ∑ x : k, (S.residueCharInt ^ a) x *
    S.zeta_ell_int ^ ((Algebra.trace (ZMod ℓ) k ((c : k) * x)).val)


-- @@ L221-275 verbatim
/-- Scale-removal: changing the trace scale multiplies the Gauss sum by
the multiplicative character value at the inverse scale, which is a
unit in `𝓞 R'`. -/
theorem gaussSumIntAtScale_eq_charUnit_mul_one
    (c : kˣ) (a : ℕ) :
    S.gaussSumIntAtScale c a =
      (S.residueCharInt ^ a) ((c⁻¹ : kˣ) : k) * S.gaussSumIntAtScale 1 a := by
  classical
  simp only [gaussSumIntAtScale]
  have hχ : (S.residueCharInt ^ a) ((c⁻¹ : kˣ) : k) *
      (S.residueCharInt ^ a) ((c : k)) = 1 := by
    rw [show
      (S.residueCharInt ^ a) ((c⁻¹ : kˣ) : k) *
        (S.residueCharInt ^ a) ((c : k)) =
      (S.residueCharInt ^ a) (((c⁻¹ : kˣ) : k) * ((c : k))) from
      (map_mul (S.residueCharInt ^ a) _ _).symm]
    rw [show ((c⁻¹ : kˣ) : k) * ((c : k)) = 1 by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]]
    exact map_one _
  calc
    ∑ x : k, (S.residueCharInt ^ a) x *
          S.zeta_ell_int ^ ((Algebra.trace (ZMod ℓ) k ((c : k) * x)).val)
      = ∑ x : k,
          ((S.residueCharInt ^ a) ((c⁻¹ : kˣ) : k) *
              (S.residueCharInt ^ a) ((c : k))) *
            ((S.residueCharInt ^ a) x *
              S.zeta_ell_int ^ ((Algebra.trace (ZMod ℓ) k ((c : k) * x)).val)) := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [hχ, one_mul]
    _ = ∑ x : k, (S.residueCharInt ^ a) ((c⁻¹ : kˣ) : k) *
          ((S.residueCharInt ^ a) ((c : k) * x) *
            S.zeta_ell_int ^ ((Algebra.trace (ZMod ℓ) k ((c : k) * x)).val)) := by
        refine Finset.sum_congr rfl fun x _ ↦ ?_
        rw [show (S.residueCharInt ^ a) ((c : k) * x) =
            (S.residueCharInt ^ a) ((c : k)) * (S.residueCharInt ^ a) x from
            map_mul (S.residueCharInt ^ a) _ _]
        ring
    _ = (S.residueCharInt ^ a) ((c⁻¹ : kˣ) : k) *
          ∑ x : k, (S.residueCharInt ^ a) ((c : k) * x) *
            S.zeta_ell_int ^ ((Algebra.trace (ZMod ℓ) k ((c : k) * x)).val) := by
        rw [Finset.mul_sum]
    _ = (S.residueCharInt ^ a) ((c⁻¹ : kˣ) : k) *
          ∑ y : k, (S.residueCharInt ^ a) y *
            S.zeta_ell_int ^ ((Algebra.trace (ZMod ℓ) k y).val) := by
        congr 1
        exact Equiv.sum_comp (Equiv.mulLeft₀ (c : k) (Units.ne_zero c))
          (fun y ↦ (S.residueCharInt ^ a) y *
            S.zeta_ell_int ^ ((Algebra.trace (ZMod ℓ) k y).val))
    _ = (S.residueCharInt ^ a) ((c⁻¹ : kˣ) : k) *
          ∑ y : k, (S.residueCharInt ^ a) y *
            S.zeta_ell_int ^
              ((Algebra.trace (ZMod ℓ) k (((1 : kˣ) : k) * y)).val) := by
        congr 1
        refine Finset.sum_congr rfl fun y _ ↦ ?_
        rw [Units.val_one, one_mul]


-- @@ L277-277 verbatim
end ConcreteStickelbergerSetup


-- @@ L279-279 verbatim
namespace TraceFormStickelbergerSetup


-- @@ L281-281 verbatim
variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]

-- @@ L282-282 verbatim
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]

-- @@ L283-283 verbatim
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

-- @@ L284-285 verbatim
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']


-- @@ L287-287 verbatim
variable (S : TraceFormStickelbergerSetup ℓ p k K R')


-- @@ L289-298 verbatim
/-- For a `TraceFormStickelbergerSetup`, the integral Gauss sum agrees
with `gaussSumIntAtScale` evaluated at the bundle's `traceScale`. -/
theorem gaussSumInt_eq_gaussSumIntAtScale_traceScale (a : ℕ) :
    S.gaussSumInt a =
      S.toConcreteStickelbergerSetup.gaussSumIntAtScale S.traceScale a := by
  simp only [ConcreteStickelbergerSetup.gaussSumIntAtScale]
  change _root_.gaussSum (S.residueCharInt ^ a) S.psiInt = _
  simp only [_root_.gaussSum]
  refine Finset.sum_congr rfl fun x _ ↦ ?_
  rw [S.psiInt_eq_zeta_ell_int_pow_trace]


-- @@ L300-300 verbatim
end TraceFormStickelbergerSetup


-- @@ L302-302 verbatim
end Furtwaengler


-- @@ L304-304 verbatim
end BernoulliRegular
