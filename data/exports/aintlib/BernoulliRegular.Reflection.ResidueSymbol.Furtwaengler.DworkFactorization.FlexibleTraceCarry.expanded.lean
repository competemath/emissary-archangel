module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FlexibleFiniteArtinHasseHomogeneous


-- @@ L5-10 verbatim
/-!
# Flexible Witt trace-carry cancellation

This file ports the scalar trace-carry input needed by the finite-log product
argument to the conductor-flexible full-Teich setup.
-/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
open scoped NumberField


-- @@ L18-18 verbatim
namespace BernoulliRegular


-- @@ L20-20 verbatim
namespace Furtwaengler


-- @@ L22-22 verbatim
universe u v w


-- @@ L24-24 verbatim
namespace ConductorFlexibleConcreteStickelbergerSetup


-- @@ L26-26 verbatim
variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]

-- @@ L27-27 verbatim
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]

-- @@ L28-28 verbatim
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

-- @@ L29-29 verbatim
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']


-- @@ L31-31 verbatim
variable (S : ConductorFlexibleConcreteStickelbergerSetup ℓ p k K R')


-- @@ L33-45 verbatim
/-- Fontaine-style `Q`-adic ghost map from Witt vectors over the flexible
residue-field model to the quotient `𝓞 R' / Q^(N+1)`. -/
noncomputable def wittThetaModQPow (N : ℕ) :
    WittVector ℓ k →+* (𝓞 R' ⧸ S.Q ^ (N + 1)) := by
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  letI : Finite k := Fintype.finite inferInstance
  haveI : PerfectRing k ℓ := inferInstance
  exact
    (wittGhostComponentModIdealPow S.Q S.hQ N).comp
      ((WittVector.map S.residueQuotientEquiv.symm.toRingHom).comp
        (WittVector.map ((_root_.iterateFrobeniusEquiv k ℓ N).symm.toRingHom)))


-- @@ L47-47 verbatim
end ConductorFlexibleConcreteStickelbergerSetup


-- @@ L49-49 verbatim
namespace ConductorFlexibleFullTeichStickelbergerSetup


-- @@ L51-51 verbatim
variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]

-- @@ L52-52 verbatim
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]

-- @@ L53-53 verbatim
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

-- @@ L54-54 verbatim
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']


-- @@ L56-56 verbatim
variable (F : ConductorFlexibleFullTeichStickelbergerSetup ℓ p k K R')


-- @@ L58-62 verbatim
/-- The flexible Teichmuller lift extended from units to all residue-field
elements by sending `0` to `0`. -/
noncomputable def teichFullVal (x : k) : 𝓞 R' := by
  classical
  exact if hx : x = 0 then 0 else F.teichUnitFullVal (Units.mk0 x hx)


-- @@ L64-68 verbatim
@[simp]
theorem teichFullVal_zero :
    F.teichFullVal (0 : k) = 0 := by
  classical
  simp [teichFullVal]


-- @@ L70-73 verbatim
theorem teichFullVal_of_ne {x : k} (hx : x ≠ 0) :
    F.teichFullVal x = F.teichUnitFullVal (Units.mk0 x hx) := by
  classical
  simp [teichFullVal, hx]


-- @@ L75-82 verbatim
theorem residueMap_teichFullVal (x : k) :
    F.concrete.residueMap (F.teichFullVal x) = x := by
  classical
  by_cases hx : x = 0
  · subst x
    simp
  · rw [F.teichFullVal_of_ne hx]
    exact F.residueMap_teichUnitFullVal (Units.mk0 x hx)


-- @@ L84-110 verbatim
/-- The extended Teichmuller lift is compatible with powers. -/
@[simp]
theorem teichFullVal_pow (x : k) (n : ℕ) :
    F.teichFullVal (x ^ n) = F.teichFullVal x ^ n := by
  classical
  by_cases hx : x = 0
  · subst x
    cases n with
    | zero =>
        rw [pow_zero, pow_zero, F.teichFullVal_of_ne one_ne_zero]
        simp
    | succ n => simp
  · have hxn : x ^ n ≠ 0 := pow_ne_zero n hx
    let xu : kˣ := Units.mk0 x hx
    have hxunit : Units.mk0 (x ^ n) hxn = xu ^ n := by
      ext
      simp [xu, Units.val_pow_eq_pow_val]
    calc
      F.teichFullVal (x ^ n)
          = F.teichUnitFullVal (Units.mk0 (x ^ n) hxn) := by
            rw [F.teichFullVal_of_ne hxn]
      _ = F.teichUnitFullVal (xu ^ n) := by
            rw [hxunit]
      _ = F.teichUnitFullVal xu ^ n := by
            rw [F.teichUnitFullVal_pow]
      _ = F.teichFullVal x ^ n := by
            rw [F.teichFullVal_of_ne hx]


-- @@ L112-147 verbatim
/-- On a Teichmuller unit, the flexible Fontaine-style Witt map recovers the
chosen integral Teichmuller lift modulo `Q^(N+1)`, provided `xN` is the
inverse-Frobenius preimage used by the map. -/
theorem wittThetaModQPow_teichmuller_unit_of_pow
    [ExpChar k ℓ] [PerfectRing k ℓ]
    (N : ℕ) (x xN : kˣ)
    (hxN :
      ((_root_.iterateFrobeniusEquiv k ℓ N).symm (x : k)) = (xN : k))
    (hxNpow : xN ^ (ℓ ^ N) = x) :
    F.concrete.wittThetaModQPow N
        (WittVector.teichmuller ℓ (x : k)) =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal x) := by
  classical
  change
    F.concrete.wittThetaModQPow N
        (WittVector.teichmuller ℓ (x : k)) =
      Ideal.Quotient.mk (F.concrete.Q ^ (N + 1)) (F.teichUnitFullVal x)
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  letI : Finite k := Fintype.finite inferInstance
  have hquot :
      F.concrete.residueQuotientEquiv.symm (xN : k) =
        Ideal.Quotient.mk F.concrete.Q (F.teichUnitFullVal xN) := by
    apply F.concrete.residueQuotientEquiv.injective
    rw [RingEquiv.apply_symm_apply, F.concrete.residueQuotientEquiv_mk]
    exact (F.residueMap_teichUnitFullVal xN).symm
  have hquot' :
      F.concrete.residueQuotientEquiv.symm.toRingHom (xN : k) =
        Ideal.Quotient.mk F.concrete.Q (F.teichUnitFullVal xN) := hquot
  have hxN' :
      (_root_.iterateFrobeniusEquiv k ℓ N).symm.toRingHom (x : k) = (xN : k) := hxN
  rw [ConductorFlexibleConcreteStickelbergerSetup.wittThetaModQPow]
  simp only [RingHom.comp_apply]
  rw [WittVector.map_teichmuller, hxN', WittVector.map_teichmuller, hquot',
    wittGhostComponentModIdealPow_teichmuller_mk, ← F.teichUnitFullVal_pow, hxNpow]


-- @@ L149-153 verbatim
omit [Fact (Nat.Prime ℓ)] [Fintype k] [Algebra (ZMod ℓ) k] in
/-- The inverse iterated Frobenius preimage of a residue-field unit. -/
noncomputable def frobeniusUnitPreimage
    [ExpChar k ℓ] [PerfectRing k ℓ] (N : ℕ) (x : kˣ) : kˣ :=
  Units.mapEquiv ((_root_.iterateFrobeniusEquiv k ℓ N).symm.toMulEquiv) x


-- @@ L155-161 verbatim
omit [Fact (Nat.Prime ℓ)] [Fintype k] [Algebra (ZMod ℓ) k] in
@[simp]
theorem frobeniusUnitPreimage_val
    [ExpChar k ℓ] [PerfectRing k ℓ] (N : ℕ) (x : kˣ) :
    (frobeniusUnitPreimage (ℓ := ℓ) N x : k) =
      (_root_.iterateFrobeniusEquiv k ℓ N).symm (x : k) := by
  rfl


-- @@ L163-171 verbatim
omit [Fact (Nat.Prime ℓ)] [Fintype k] [Algebra (ZMod ℓ) k] in
theorem frobeniusUnitPreimage_pow
    [ExpChar k ℓ] [PerfectRing k ℓ] (N : ℕ) (x : kˣ) :
    frobeniusUnitPreimage (ℓ := ℓ) N x ^ (ℓ ^ N) = x := by
  ext
  rw [Units.val_pow_eq_pow_val, frobeniusUnitPreimage_val]
  change ((_root_.iterateFrobeniusEquiv k ℓ N)
      ((_root_.iterateFrobeniusEquiv k ℓ N).symm (x : k))) = (x : k)
  rw [RingEquiv.apply_symm_apply]


-- @@ L173-183 verbatim
/-- On a Teichmuller unit, the flexible Witt map recovers the chosen integral
Teichmuller lift modulo `Q^(N+1)`. -/
theorem wittThetaModQPow_teichmuller_unit
    [ExpChar k ℓ] [PerfectRing k ℓ] (N : ℕ) (x : kˣ) :
    F.concrete.wittThetaModQPow N
        (WittVector.teichmuller ℓ (x : k)) =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal x) := by
  refine F.wittThetaModQPow_teichmuller_unit_of_pow
    N x (frobeniusUnitPreimage (ℓ := ℓ) N x) ?_ ?_
  · exact (frobeniusUnitPreimage_val (ℓ := ℓ) N x).symm
  · exact frobeniusUnitPreimage_pow (ℓ := ℓ) N x


-- @@ L185-200 verbatim
/-- On any residue-field element, the flexible Witt map recovers the extended
Teichmuller lift modulo `Q^(N+1)`. -/
theorem wittThetaModQPow_teichmuller
    [ExpChar k ℓ] [PerfectRing k ℓ] (N : ℕ) (x : k) :
    F.concrete.wittThetaModQPow N
        (WittVector.teichmuller ℓ x) =
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal x) := by
  classical
  by_cases hx : x = 0
  · subst x
    rw [WittVector.teichmuller_zero, map_zero]
    simp
    rfl
  · let xu : kˣ := Units.mk0 x hx
    have hunit := F.wittThetaModQPow_teichmuller_unit N xu
    simpa [teichFullVal, hx, xu] using hunit


-- @@ L202-234 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The flexible quotient Witt map sends the Witt-Frobenius trace of a
Teichmuller unit to the corresponding Teichmuller Frobenius sum. -/
theorem wittThetaModQPow_wittFrobeniusTrace_teichmuller_unit
    [ExpChar k ℓ] [PerfectRing k ℓ] (N f : ℕ) (x : kˣ) :
    F.concrete.wittThetaModQPow N
        (ConcreteStickelbergerSetup.wittFrobeniusTrace (ℓ := ℓ) (k := k) f
          (WittVector.teichmuller ℓ (x : k))) =
      Ideal.Quotient.mk (F.Q ^ (N + 1))
        (∑ i : Fin f, (F.teichUnitFullVal x) ^ (ℓ ^ (i : ℕ))) := by
  classical
  calc
    F.concrete.wittThetaModQPow N
        (ConcreteStickelbergerSetup.wittFrobeniusTrace (ℓ := ℓ) (k := k) f
          (WittVector.teichmuller ℓ (x : k)))
        = ∑ i : Fin f,
            F.concrete.wittThetaModQPow N
              (WittVector.teichmuller ℓ ((x : k) ^ (ℓ ^ (i : ℕ)))) := by
            rw [ConcreteStickelbergerSetup.wittFrobeniusTrace_teichmuller]
            simp
    _ = ∑ i : Fin f,
          Ideal.Quotient.mk (F.Q ^ (N + 1))
            (F.teichUnitFullVal (x ^ (ℓ ^ (i : ℕ)))) := by
            refine Finset.sum_congr rfl ?_
            intro i _hi
            simpa [Units.val_pow_eq_pow_val] using
              F.wittThetaModQPow_teichmuller_unit N (x ^ (ℓ ^ (i : ℕ)))
    _ = Ideal.Quotient.mk (F.Q ^ (N + 1))
          (∑ i : Fin f, (F.teichUnitFullVal x) ^ (ℓ ^ (i : ℕ))) := by
            rw [map_sum]
            refine Finset.sum_congr rfl ?_
            intro i _hi
            rw [F.teichUnitFullVal_pow]


-- @@ L236-351 verbatim
/-- The ordinary trace lift minus the Teichmuller Frobenius trace sum is an
`ℓ`-multiple in every flexible quotient. -/
theorem exists_traceNatCast_sub_teichFrobeniusSum_eq_natCast_ell_mul
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ∃ c : A,
      (t : A) -
          (∑ i : Fin F.concrete.f, zbar ^ (ℓ ^ (i : ℕ))) =
        (ℓ : A) * c := by
  classical
  haveI : CharP k ℓ := by
    rw [← Algebra.charP_iff (ZMod ℓ) k ℓ]
    exact ZMod.charP ℓ
  letI : Finite k := Fintype.finite inferInstance
  haveI : PerfectRing k ℓ := inferInstance
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let θ : WittVector ℓ k →+* A := F.concrete.wittThetaModQPow N
  let z : 𝓞 R' := F.teichUnitFullVal (F.traceScale * y)
  let zbar : A := Ideal.Quotient.mk (F.Q ^ (N + 1)) z
  let a : ZMod ℓ := Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))
  let traceK : k := algebraMap (ZMod ℓ) k a
  let t : ℕ := a.val
  let W : WittVector ℓ k :=
    ConcreteStickelbergerSetup.wittFrobeniusTrace (ℓ := ℓ) (k := k)
      F.concrete.f (WittVector.teichmuller ℓ ((F.traceScale : k) * (y : k)))
  let traceTeich : WittVector ℓ k := WittVector.teichmuller ℓ traceK
  have hsum_trace :
      (∑ i : Fin F.concrete.f,
          ((F.traceScale : k) * (y : k)) ^ (ℓ ^ (i : ℕ))) = traceK := by
    have hfin : Module.finrank (ZMod ℓ) k = F.concrete.f := by
      have hpow : ℓ ^ Module.finrank (ZMod ℓ) k = ℓ ^ F.concrete.f := by
        rw [FiniteField.pow_finrank_eq_card, F.concrete.card_k]
      exact Nat.pow_right_injective (Fact.out : Nat.Prime ℓ).one_lt hpow
    have h :=
      algebraMap_trace_pow_eq_traceSum_pow
        (K := ZMod ℓ) (L := k) (ℓ := ℓ) (f := F.concrete.f)
        (Nat.card_zmod ℓ) hfin ((F.traceScale : k) * (y : k)) 1
    have hrange :
        traceK =
          ∑ i ∈ Finset.range F.concrete.f,
            ((F.traceScale : k) * (y : k)) ^ (ℓ ^ i) := by
      simpa [traceK, a, traceSum] using h
    rw [← Fin.sum_univ_eq_sum_range] at hrange
    exact hrange.symm
  obtain ⟨cNat, hcNat⟩ :=
    ConcreteStickelbergerSetup.natCast_zmod_val_sub_teichmuller_dvd_prime
      (ℓ := ℓ) (k := k) a
  obtain ⟨cFrob, hcFrob0⟩ :=
    ConcreteStickelbergerSetup.wittFrobeniusTrace_teichmuller_sub_teichmuller_coeff_zero_dvd_prime
      (ℓ := ℓ) (k := k) F.concrete.f ((F.traceScale : k) * (y : k))
  have hTraceTeich :
      θ traceTeich =
        Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal traceK) :=
    F.wittThetaModQPow_teichmuller N traceK
  have hW :
      θ W =
        ∑ i : Fin F.concrete.f, zbar ^ (ℓ ^ (i : ℕ)) := by
    have h :=
      F.wittThetaModQPow_wittFrobeniusTrace_teichmuller_unit
        N F.concrete.f (F.traceScale * y)
    rw [map_sum] at h
    simp only [map_pow] at h
    exact h
  have hNatW :
      (((t : ℕ) : WittVector ℓ k) - traceTeich) =
        (ℓ : WittVector ℓ k) * cNat := by
    simpa [t, a, traceTeich, traceK] using hcNat
  have hTraceW :
      W - traceTeich = (ℓ : WittVector ℓ k) * cFrob := by
    simpa [W, traceTeich, traceK, hsum_trace] using hcFrob0
  have hNatTheta :
      (t : A) - Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal traceK) =
        (ℓ : A) * θ cNat := by
    calc
      (t : A) - Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal traceK)
          = θ (((t : ℕ) : WittVector ℓ k)) - θ traceTeich := by
              rw [map_natCast, hTraceTeich]
      _ = θ ((((t : ℕ) : WittVector ℓ k)) - traceTeich) := by
              rw [map_sub]
      _ = θ ((ℓ : WittVector ℓ k) * cNat) := by
              rw [hNatW]
      _ = (ℓ : A) * θ cNat := by
              rw [map_mul, map_natCast]
  have hTraceTheta :
      (∑ i : Fin F.concrete.f, zbar ^ (ℓ ^ (i : ℕ))) -
          Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal traceK) =
        (ℓ : A) * θ cFrob := by
    calc
      (∑ i : Fin F.concrete.f, zbar ^ (ℓ ^ (i : ℕ))) -
          Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal traceK)
          = θ W - θ traceTeich := by
              rw [hW, hTraceTeich]
      _ = θ (W - traceTeich) := by
              rw [map_sub]
      _ = θ ((ℓ : WittVector ℓ k) * cFrob) := by
              rw [hTraceW]
      _ = (ℓ : A) * θ cFrob := by
              rw [map_mul, map_natCast]
  refine ⟨θ (cNat - cFrob), ?_⟩
  calc
    (t : A) -
        (∑ i : Fin F.concrete.f, zbar ^ (ℓ ^ (i : ℕ)))
        =
          ((t : A) - Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal traceK)) -
            ((∑ i : Fin F.concrete.f, zbar ^ (ℓ ^ (i : ℕ))) -
              Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichFullVal traceK)) := by
          ring
    _ = (ℓ : A) * θ cNat - (ℓ : A) * θ cFrob := by
          rw [hNatTheta, hTraceTheta]
    _ = (ℓ : A) * θ (cNat - cFrob) := by
          rw [map_sub]
          ring


-- @@ L353-379 verbatim
/-- Sign-oriented quotient form of trace-carry divisibility by the scalar
`ℓ`. -/
theorem exists_teichFrobeniusSum_sub_traceNatCast_eq_natCast_ell_mul
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ∃ c : A,
      (∑ i : Fin F.concrete.f, zbar ^ (ℓ ^ (i : ℕ))) -
          (t : A) =
        (ℓ : A) * c := by
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  obtain ⟨c, hc⟩ := F.exists_traceNatCast_sub_teichFrobeniusSum_eq_natCast_ell_mul N y
  refine ⟨-c, ?_⟩
  calc
    (∑ i : Fin F.concrete.f, zbar ^ (ℓ ^ (i : ℕ))) - (t : A)
        = -((t : A) - ∑ i : Fin F.concrete.f, zbar ^ (ℓ ^ (i : ℕ))) := by
          ring
    _ = -((ℓ : A) * c) := by
          rw [hc]
    _ = (ℓ : A) * (-c) := by
          ring


-- @@ L381-407 verbatim
/-- Product form of trace-carry cancellation: any quotient element killed by
multiplication by `ℓ` kills the trace-carry error. -/
theorem teichFrobeniusSum_sub_traceNatCast_mul_eq_zero_of_natCast_ell_mul_eq_zero
    (N : ℕ) (y : kˣ) (h : 𝓞 R' ⧸ F.Q ^ (N + 1))
    (hh : (ℓ : 𝓞 R' ⧸ F.Q ^ (N + 1)) * h = 0) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ((∑ i : Fin F.concrete.f, zbar ^ (ℓ ^ (i : ℕ))) -
        (t : A)) * h = 0 := by
  classical
  dsimp only
  let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
  let zbar : A :=
    Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
  let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
  obtain ⟨c, hc⟩ := F.exists_teichFrobeniusSum_sub_traceNatCast_eq_natCast_ell_mul N y
  calc
    ((∑ i : Fin F.concrete.f, zbar ^ (ℓ ^ (i : ℕ))) - (t : A)) * h
        = ((ℓ : A) * c) * h := by
          rw [hc]
    _ = ((ℓ : A) * h) * c := by
          ring
    _ = 0 := by
          rw [hh]
          simp


-- @@ L409-431 verbatim
/-- The trace-carry error in the Dwork-product finite logarithm is killed by
the `ℓ`-torsion relation on the inverse-parameter Artin-Hasse logarithm. -/
theorem teichFrobeniusSum_sub_traceNatCast_mul_finiteArtinHasseLog_eq_zero
    (N : ℕ) (y : kˣ) :
    let A : Type _ := 𝓞 R' ⧸ F.Q ^ (N + 1)
    let zbar : A :=
      Ideal.Quotient.mk (F.Q ^ (N + 1)) (F.teichUnitFullVal (F.traceScale * y))
    let t : ℕ := (Algebra.trace (ZMod ℓ) k ((F.traceScale : k) * (y : k))).val
    ((∑ i : Fin F.concrete.f, zbar ^ (ℓ ^ (i : ℕ))) -
        (t : A)) *
      F.finiteArtinHasseLog N
        (F.concrete.artinHasseDworkParameterApproxTo N)
        (F.concrete.artinHasseDworkParameterApproxTo_mem_Q N) =
      0 := by
  classical
  dsimp only
  exact
    F.teichFrobeniusSum_sub_traceNatCast_mul_eq_zero_of_natCast_ell_mul_eq_zero
      N y
      (F.finiteArtinHasseLog N
        (F.concrete.artinHasseDworkParameterApproxTo N)
        (F.concrete.artinHasseDworkParameterApproxTo_mem_Q N))
      (F.finiteArtinHasseLog_inverseParameter_natCast_ell_mul_eq_zero' N)


-- @@ L433-433 verbatim
end ConductorFlexibleFullTeichStickelbergerSetup


-- @@ L435-435 verbatim
end Furtwaengler


-- @@ L437-437 verbatim
end BernoulliRegular


-- @@ L439-439 verbatim
end
