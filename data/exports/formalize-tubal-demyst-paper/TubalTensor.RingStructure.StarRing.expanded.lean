import TubalTensor.RingStructure.CommRing


-- @@ L3-9 verbatim
/-!
  TubalTensor/RingStructure/StarRing.lean
  ⋆_M-conjugate, *-ring instance.

  The ⋆_M-conjugation is defined as: a* := M⁻¹(conj(Ma))
  This makes K_M into a *-ring.
-/


-- @@ L11-11 verbatim
namespace TubalTensor


-- @@ L13-13 verbatim
open Complex Matrix


-- @@ L15-15 verbatim
variable {n : ℕ}


-- @@ L17-17 verbatim
/-! ## Complex-level conjugation: starConjC -/


-- @@ L19-21 verbatim
/-- The ⋆_M-conjugation on complex vectors: M⁻¹(conj(Ma)). -/
noncomputable def starConjC (td : TubalData n) (a : Fin n → ℂ) : Fin n → ℂ :=
  td.applyMinv (vecConj (td.applyM a))


-- @@ L23-25 verbatim
/-- The ⋆_M-conjugation on real vectors. -/
noncomputable def starConjM (td : TubalData n) (a : Fin n → ℝ) : Fin n → ℝ :=
  vecRe (starConjC td (toComplex a))


-- @@ L27-27 verbatim
/-! ## Realness: starConjC maps real vectors to real vectors -/


-- @@ L29-45 verbatim
/-- The conjugate of a vector with real-paired structure also has real-paired structure. -/
private theorem vecConj_applyM_hasPairedStructure (td : TubalData n) (a : Fin n → ℝ) :
    HasRealPairedStructure td (vecConj (td.applyM (toComplex a))) := by
  have hps := applyM_toComplex_hasPairedStructure td a
  constructor
  · intro i hreal
    simp only [vecConj_apply]
    have him := hps.1 i hreal
    rw [starRingEnd_apply, star_def, Complex.conj_im, neg_eq_zero]
    exact him
  · intro i k hki hconj
    -- Need: vecConj v k = conj(vecConj v i) where v = Ma
    -- i.e., conj(v k) = conj(conj(v i))
    -- From hps.2: v k = conj(v i), so conj(v k) = conj(conj(v i)). Done.
    show starRingEnd ℂ (td.applyM (toComplex a) k) =
      starRingEnd ℂ (starRingEnd ℂ (td.applyM (toComplex a) i))
    congr 1; exact hps.2 i k hki hconj


-- @@ L47-50 verbatim
/-- starConjC maps real vectors to real vectors. -/
theorem starConjC_real (td : TubalData n) (a : Fin n → ℝ) :
    IsRealVec (starConjC td (toComplex a)) :=
  applyMinv_real_of_pairedStructure td _ (vecConj_applyM_hasPairedStructure td a)


-- @@ L52-55 verbatim
/-- The real ⋆_M-conjugation equals the complex version on real inputs. -/
theorem starConjM_eq_starConjC (td : TubalData n) (a : Fin n → ℝ) :
    toComplex (starConjM td a) = starConjC td (toComplex a) :=
  toComplex_vecRe _ (starConjC_real td a)


-- @@ L57-57 verbatim
/-! ## StarRing axiom proofs -/


-- @@ L59-71 verbatim
/-- Complex-level: starConjC is involutive. -/
private theorem starConjC_involutive (td : TubalData n) (a : Fin n → ℂ) :
    starConjC td (starConjC td a) = a := by
  unfold starConjC
  rw [td.applyM_applyMinv]
  -- Need: M⁻¹(conj(conj(Ma))) = a
  -- conj(conj(Ma)) = Ma, so M⁻¹(Ma) = a
  have : vecConj (vecConj (td.applyM a)) = td.applyM a := by
    ext i
    show starRingEnd ℂ (starRingEnd ℂ (td.applyM a i)) = td.applyM a i
    rw [starRingEnd_apply, starRingEnd_apply, star_star]
  rw [this]
  exact td.applyMinv_applyM a


-- @@ L73-82 verbatim
/-- Complex-level: starConjC is additive. -/
private theorem starConjC_add (td : TubalData n) (a b : Fin n → ℂ) :
    starConjC td (a + b) = starConjC td a + starConjC td b := by
  unfold starConjC
  rw [td.applyM_add]
  -- conj distributes over +
  have : vecConj (td.applyM a + td.applyM b) = vecConj (td.applyM a) + vecConj (td.applyM b) := by
    ext i; simp [vecConj_apply, map_add]
  rw [this]
  exact td.applyMinv_add _ _


-- @@ L84-99 verbatim
/-- Complex-level: starConjC is antimultiplicative w.r.t. starMC.
    Since the ring is commutative, this is the same as being multiplicative. -/
private theorem starConjC_mul (td : TubalData n) (a b : Fin n → ℂ) :
    starConjC td (starMC td a b) = starMC td (starConjC td a) (starConjC td b) := by
  unfold starConjC starMC
  -- LHS: M⁻¹(conj(M(M⁻¹(Ma ∘ₕ Mb))))
  -- = M⁻¹(conj(Ma ∘ₕ Mb))           [M * M⁻¹ = I]
  -- = M⁻¹(conj(Ma) ∘ₕ conj(Mb))     [conj distributes over ∘ₕ]
  rw [td.applyM_applyMinv]
  -- RHS: M⁻¹(M(M⁻¹(conj(Ma))) ∘ₕ M(M⁻¹(conj(Mb))))
  -- = M⁻¹(conj(Ma) ∘ₕ conj(Mb))
  rw [td.applyM_applyMinv, td.applyM_applyMinv]
  -- Now both sides are M⁻¹(vecConj(Ma ∘ₕ Mb)) vs M⁻¹(vecConj(Ma) ∘ₕ vecConj(Mb))
  congr 1
  ext i
  simp [vecConj_apply, vecHadamard_apply, map_mul]


-- @@ L101-101 verbatim
/-! ## Lift to real operations -/


-- @@ L103-107 verbatim
theorem starConjM_involutive (td : TubalData n) (a : Fin n → ℝ) :
    starConjM td (starConjM td a) = a := by
  apply toComplex_injective
  rw [starConjM_eq_starConjC, starConjM_eq_starConjC]
  exact starConjC_involutive td _


-- @@ L109-113 verbatim
theorem starConjM_add (td : TubalData n) (a b : Fin n → ℝ) :
    starConjM td (a + b) = starConjM td a + starConjM td b := by
  apply toComplex_injective
  rw [starConjM_eq_starConjC, toComplex_add, starConjC_add, toComplex_add,
      starConjM_eq_starConjC, starConjM_eq_starConjC]


-- @@ L115-119 verbatim
theorem starConjM_mul (td : TubalData n) (a b : Fin n → ℝ) :
    starConjM td (starM td a b) = starM td (starConjM td a) (starConjM td b) := by
  apply toComplex_injective
  rw [starConjM_eq_starConjC, starM_eq_starMC, starConjC_mul,
      starM_eq_starMC, starConjM_eq_starConjC, starConjM_eq_starConjC]


-- @@ L121-121 verbatim
/-! ## StarRing instance for KM -/


-- @@ L123-123 verbatim
namespace KM


-- @@ L125-125 verbatim
variable {td : TubalData n}


-- @@ L127-129 verbatim
/-- The star operation on KM is ⋆_M-conjugation. -/
noncomputable instance instStar : Star (KM n td) :=
  ⟨fun a => ofFun (starConjM td (toFun a))⟩


-- @@ L131-132 verbatim
@[simp] theorem toFun_star (a : KM n td) :
    toFun (star a) = starConjM td (toFun a) := rfl


-- @@ L134-151 verbatim
/-- KM is a *-ring under ⋆_M-conjugation (Section 3.3). -/
noncomputable instance instStarRing : StarRing (KM n td) where
  star_involutive a := by
    show ofFun _ = _
    exact congr_arg ofFun (starConjM_involutive td _)
  star_mul a b := by
    show ofFun _ = ofFun _
    -- star(a * b) = star(b) * star(a)
    -- Since the ring is commutative, this is star(a) * star(b)
    have h := starConjM_mul td (toFun a) (toFun b)
    -- h : starConjM td (starM td a b) = starM td (starConjM a) (starConjM b)
    -- But star(a * b) = star(b) * star(a) = starM(star(b), star(a))
    -- = starM(starConj b, starConj a) = starM(starConj a, starConj b) by commutativity
    -- = starConjM(starM a b)
    exact congr_arg ofFun (h.trans (starM_comm td _ _))
  star_add a b := by
    show ofFun _ = ofFun _ + ofFun _
    exact congr_arg ofFun (starConjM_add td (toFun a) (toFun b))


-- @@ L153-153 verbatim
end KM


-- @@ L155-155 verbatim
end TubalTensor
