import TubalTensor.RingStructure.StarRing
import TubalTensor.Defs.VonNeumannRegular


-- @@ L4-11 verbatim
/-!
  TubalTensor/RingStructure/WeakInverse.lean
  Lemma 7 (weak inverse is real), Lemma 8 (Moore-Penrose properties),
  and VN-regularity of K_M.

  The weak inverse is defined as: a⁻ := M⁻¹((Ma)⁺)
  where (·)⁺ is the entrywise pseudo-inverse (invert nonzero entries, keep zeros).
-/


-- @@ L13-13 verbatim
namespace TubalTensor


-- @@ L15-15 verbatim
open Complex Matrix


-- @@ L17-17 verbatim
variable {n : ℕ}


-- @@ L19-19 verbatim
/-! ## Entrywise pseudo-inverse on complex vectors -/


-- @@ L21-23 verbatim
/-- Entrywise pseudo-inverse: invert nonzero entries, keep zeros. -/
noncomputable def vecPseudoInv {n : ℕ} (v : Fin n → ℂ) : Fin n → ℂ :=
  fun i => if v i = 0 then 0 else (v i)⁻¹


-- @@ L25-27 verbatim
@[simp]
theorem vecPseudoInv_apply {n : ℕ} (v : Fin n → ℂ) (i : Fin n) :
    vecPseudoInv v i = if v i = 0 then 0 else (v i)⁻¹ := rfl


-- @@ L29-29 verbatim
/-! ## Entrywise properties of pseudo-inverse -/


-- @@ L31-35 verbatim
/-- x * x⁺ * x = x entrywise. -/
theorem vecPseudoInv_mp1 {n : ℕ} (v : Fin n → ℂ) :
    v ∘ₕ vecPseudoInv v ∘ₕ v = v := by
  ext i; simp only [vecHadamard_apply, vecPseudoInv_apply]
  by_cases h : v i = 0 <;> simp [h]


-- @@ L37-41 verbatim
/-- x⁺ * x * x⁺ = x⁺ entrywise. -/
theorem vecPseudoInv_mp2 {n : ℕ} (v : Fin n → ℂ) :
    vecPseudoInv v ∘ₕ v ∘ₕ vecPseudoInv v = vecPseudoInv v := by
  ext i; simp only [vecHadamard_apply, vecPseudoInv_apply]
  by_cases h : v i = 0 <;> simp [h]


-- @@ L43-49 verbatim
/-- x * x⁺ is entrywise 0 or 1, hence real. -/
theorem vecPseudoInv_proj_real {n : ℕ} (v : Fin n → ℂ) (i : Fin n) :
    ((v ∘ₕ vecPseudoInv v) i).im = 0 := by
  simp only [vecHadamard_apply, vecPseudoInv_apply]
  by_cases h : v i = 0
  · simp [h]
  · simp [h]


-- @@ L51-56 verbatim
/-- x * x⁺ = conj(x * x⁺) (it's real, so conj is identity). -/
theorem vecPseudoInv_proj_self_conj {n : ℕ} (v : Fin n → ℂ) :
    vecConj (v ∘ₕ vecPseudoInv v) = v ∘ₕ vecPseudoInv v := by
  ext i
  show starRingEnd ℂ ((v ∘ₕ vecPseudoInv v) i) = (v ∘ₕ vecPseudoInv v) i
  rw [starRingEnd_apply, star_def, Complex.conj_eq_iff_im.mpr (vecPseudoInv_proj_real v i)]


-- @@ L58-62 verbatim
/-- x⁺ * x = x * x⁺ (both are the same 0/1 indicator). -/
theorem vecPseudoInv_comm {n : ℕ} (v : Fin n → ℂ) :
    vecPseudoInv v ∘ₕ v = v ∘ₕ vecPseudoInv v := by
  ext i; simp only [vecHadamard_apply, vecPseudoInv_apply]
  by_cases h : v i = 0 <;> simp [h]


-- @@ L64-64 verbatim
/-! ## Pseudo-inverse preserves real-paired structure -/


-- @@ L66-77 verbatim
/-- Conjugation commutes with pseudo-inverse entrywise. -/
theorem vecConj_vecPseudoInv {n : ℕ} (v : Fin n → ℂ) :
    vecConj (vecPseudoInv v) = vecPseudoInv (vecConj v) := by
  ext i
  simp only [vecConj_apply, vecPseudoInv_apply]
  by_cases h : v i = 0
  · simp [h]
  · have hc : starRingEnd ℂ (v i) ≠ 0 := by
      intro habs; apply h
      have := congr_arg (starRingEnd ℂ) habs
      rwa [map_zero, starRingEnd_apply, starRingEnd_apply, star_star] at this
    simp [h, hc, map_inv₀]


-- @@ L79-108 verbatim
/-- Pseudo-inverse of a vector with real-paired structure has real-paired structure. -/
theorem vecPseudoInv_hasPairedStructure {td : TubalData n} {v : Fin n → ℂ}
    (hv : HasRealPairedStructure td v) :
    HasRealPairedStructure td (vecPseudoInv v) := by
  constructor
  · intro i hreal
    simp only [vecPseudoInv_apply]
    split
    · simp
    · next h =>
      -- v i is real (im = 0) and nonzero, so (v i)⁻¹ is real
      have him := hv.1 i hreal
      have hre_ne : (v i).re ≠ 0 := by
        intro habs
        apply h
        exact Complex.ext habs him
      rw [Complex.inv_def, Complex.normSq_apply]
      simp [him]
  · intro i k hki hconj
    simp only [vecPseudoInv_apply]
    have hvk := hv.2 i k hki hconj
    by_cases h : v i = 0
    · have hk : v k = 0 := by rw [hvk]; simp [h]
      simp [h, hk]
    · have hk : v k ≠ 0 := by
        intro habs; apply h
        have : starRingEnd ℂ (v k) = 0 := by rw [habs]; simp
        rw [hvk, starRingEnd_apply, starRingEnd_apply, star_star] at this
        exact this
      simp [h, hvk, map_inv₀]


-- @@ L110-110 verbatim
/-! ## Weak inverse definition -/


-- @@ L112-114 verbatim
/-- The weak inverse on complex vectors: M⁻¹((Ma)⁺). -/
noncomputable def weakInvC (td : TubalData n) (a : Fin n → ℂ) : Fin n → ℂ :=
  td.applyMinv (vecPseudoInv (td.applyM a))


-- @@ L116-118 verbatim
/-- The weak inverse on real vectors. -/
noncomputable def weakInvM (td : TubalData n) (a : Fin n → ℝ) : Fin n → ℝ :=
  vecRe (weakInvC td (toComplex a))


-- @@ L120-120 verbatim
/-! ## Lemma 7: Weak inverse is real -/


-- @@ L122-126 verbatim
/-- **Lemma 7**: The weak inverse of a real vector is real. -/
theorem weakInvC_real (td : TubalData n) (a : Fin n → ℝ) :
    IsRealVec (weakInvC td (toComplex a)) :=
  applyMinv_real_of_pairedStructure td _
    (vecPseudoInv_hasPairedStructure (applyM_toComplex_hasPairedStructure td a))


-- @@ L128-131 verbatim
/-- The real weak inverse equals the complex version on real inputs. -/
theorem weakInvM_eq_weakInvC (td : TubalData n) (a : Fin n → ℝ) :
    toComplex (weakInvM td a) = weakInvC td (toComplex a) :=
  toComplex_vecRe _ (weakInvC_real td a)


-- @@ L133-144 verbatim
/-! ## Lemma 8: Moore-Penrose properties

  Strategy: We prove everything in the transform domain. The key observation is:
    starMC td a b = M⁻¹(Ma ∘ₕ Mb)
  so in the transform domain (after applying M):
    M(starMC td a b) = Ma ∘ₕ Mb
  Similarly:
    M(starConjC td a) = conj(Ma)
    M(weakInvC td a) = (Ma)⁺

  The MP conditions become purely entrywise statements about Hadamard products.
-/


-- @@ L146-149 verbatim
/-- Transform-domain form of starMC: applying M to starMC gives Hadamard product. -/
theorem applyM_starMC (td : TubalData n) (a b : Fin n → ℂ) :
    td.applyM (starMC td a b) = td.applyM a ∘ₕ td.applyM b := by
  unfold starMC; exact td.applyM_applyMinv _


-- @@ L151-154 verbatim
/-- Transform-domain form of starConjC: applying M to starConjC gives conjugation. -/
theorem applyM_starConjC (td : TubalData n) (a : Fin n → ℂ) :
    td.applyM (starConjC td a) = vecConj (td.applyM a) := by
  unfold starConjC; exact td.applyM_applyMinv _


-- @@ L156-159 verbatim
/-- Transform-domain form of weakInvC: applying M to weakInvC gives pseudo-inverse. -/
theorem applyM_weakInvC (td : TubalData n) (a : Fin n → ℂ) :
    td.applyM (weakInvC td a) = vecPseudoInv (td.applyM a) := by
  unfold weakInvC; exact td.applyM_applyMinv _


-- @@ L161-166 verbatim
/-- Complex-level MP1: a ⋆_M a⁻ ⋆_M a = a. -/
private theorem weakInvC_mp1 (td : TubalData n) (a : Fin n → ℂ) :
    starMC td (starMC td a (weakInvC td a)) a = a := by
  apply td.applyM_injective
  rw [applyM_starMC, applyM_starMC, applyM_weakInvC]
  exact vecPseudoInv_mp1 _


-- @@ L168-174 verbatim
/-- Complex-level MP2: a⁻ ⋆_M a ⋆_M a⁻ = a⁻. -/
private theorem weakInvC_mp2 (td : TubalData n) (a : Fin n → ℂ) :
    starMC td (starMC td (weakInvC td a) a) (weakInvC td a) = weakInvC td a := by
  apply td.applyM_injective
  rw [applyM_starMC, applyM_starMC]
  simp only [applyM_weakInvC]
  exact vecPseudoInv_mp2 _


-- @@ L176-181 verbatim
/-- Complex-level MP3: (a ⋆_M a⁻)* = a ⋆_M a⁻. -/
private theorem weakInvC_mp3 (td : TubalData n) (a : Fin n → ℂ) :
    starConjC td (starMC td a (weakInvC td a)) = starMC td a (weakInvC td a) := by
  apply td.applyM_injective
  rw [applyM_starConjC, applyM_starMC, applyM_weakInvC]
  exact vecPseudoInv_proj_self_conj _


-- @@ L183-188 verbatim
/-- Complex-level MP4: (a⁻ ⋆_M a)* = a⁻ ⋆_M a. -/
private theorem weakInvC_mp4 (td : TubalData n) (a : Fin n → ℂ) :
    starConjC td (starMC td (weakInvC td a) a) = starMC td (weakInvC td a) a := by
  apply td.applyM_injective
  rw [applyM_starConjC, applyM_starMC, applyM_weakInvC]
  rw [vecPseudoInv_comm, vecPseudoInv_proj_self_conj]


-- @@ L190-190 verbatim
/-! ## Lift to real operations -/


-- @@ L192-197 verbatim
/-- **Lemma 8, MP1**: a ⋆_M a⁻ ⋆_M a = a. -/
theorem weakInvM_mp1 (td : TubalData n) (a : Fin n → ℝ) :
    starM td (starM td a (weakInvM td a)) a = a := by
  apply toComplex_injective
  rw [starM_eq_starMC, starM_eq_starMC, weakInvM_eq_weakInvC]
  exact weakInvC_mp1 td _


-- @@ L199-205 verbatim
/-- **Lemma 8, MP2**: a⁻ ⋆_M a ⋆_M a⁻ = a⁻. -/
theorem weakInvM_mp2 (td : TubalData n) (a : Fin n → ℝ) :
    starM td (starM td (weakInvM td a) a) (weakInvM td a) = weakInvM td a := by
  apply toComplex_injective
  rw [starM_eq_starMC, starM_eq_starMC]
  simp only [weakInvM_eq_weakInvC]
  exact weakInvC_mp2 td _


-- @@ L207-213 verbatim
/-- **Lemma 8, MP3**: (a ⋆_M a⁻)* = a ⋆_M a⁻. -/
theorem weakInvM_mp3 (td : TubalData n) (a : Fin n → ℝ) :
    starConjM td (starM td a (weakInvM td a)) = starM td a (weakInvM td a) := by
  apply toComplex_injective
  rw [starConjM_eq_starConjC, starM_eq_starMC]
  simp only [weakInvM_eq_weakInvC]
  exact weakInvC_mp3 td _


-- @@ L215-221 verbatim
/-- **Lemma 8, MP4**: (a⁻ ⋆_M a)* = a⁻ ⋆_M a. -/
theorem weakInvM_mp4 (td : TubalData n) (a : Fin n → ℝ) :
    starConjM td (starM td (weakInvM td a) a) = starM td (weakInvM td a) a := by
  apply toComplex_injective
  rw [starConjM_eq_starConjC, starM_eq_starMC]
  simp only [weakInvM_eq_weakInvC]
  exact weakInvC_mp4 td _


-- @@ L223-223 verbatim
/-! ## Uniqueness of the Moore-Penrose pseudo-inverse (Lemma 8, part 2) -/


-- @@ L225-264 verbatim
/-- Complex-level uniqueness: if y satisfies the four MP conditions w.r.t. a, then y = a⁻. -/
private theorem weakInvC_unique (td : TubalData n) (a y : Fin n → ℂ)
    (h1 : starMC td (starMC td a y) a = a)
    (h2 : starMC td (starMC td y a) y = y)
    (_h3 : starConjC td (starMC td a y) = starMC td a y)
    (_h4 : starConjC td (starMC td y a) = starMC td y a) :
    y = weakInvC td a := by
  -- Work entirely in the transform domain
  apply td.applyM_injective
  rw [applyM_weakInvC]
  -- Extract entrywise conditions via transform domain
  have hh1 : td.applyM a ∘ₕ td.applyM y ∘ₕ td.applyM a = td.applyM a := by
    have := congr_arg td.applyM h1; rwa [applyM_starMC, applyM_starMC] at this
  have hh2 : td.applyM y ∘ₕ td.applyM a ∘ₕ td.applyM y = td.applyM y := by
    have := congr_arg td.applyM h2; rwa [applyM_starMC, applyM_starMC] at this
  -- Now prove td.applyM y = vecPseudoInv (td.applyM a) entrywise
  set u := td.applyM a
  set v := td.applyM y
  ext i
  simp only [vecPseudoInv_apply]
  -- Case split on whether u i = 0
  by_cases hu : u i = 0
  · -- From hh2: v i * u i * v i = v i, but u i = 0 so LHS = 0
    have h2i := congr_fun hh2 i
    simp only [vecHadamard_apply, hu, mul_zero, zero_mul] at h2i
    simp [hu, h2i.symm]
  · -- u i ≠ 0: from hh1, u i * v i * u i = u i
    have h1i := congr_fun hh1 i
    simp only [vecHadamard_apply] at h1i
    -- u i * v i * u i = u i, cancel u i on right (u i ≠ 0)
    have hvu : u i * v i = 1 := by
      have key : u i * v i * u i = 1 * u i := by rw [h1i, one_mul]
      exact mul_right_cancel₀ hu key
    -- From u i * v i = 1: v i = (u i)⁻¹
    simp [hu]
    calc v i = 1 * v i := (one_mul _).symm
    _ = (u i)⁻¹ * u i * v i := by rw [inv_mul_cancel₀ hu]
    _ = (u i)⁻¹ * (u i * v i) := by rw [mul_assoc]
    _ = (u i)⁻¹ * 1 := by rw [hvu]
    _ = (u i)⁻¹ := mul_one _


-- @@ L266-284 verbatim
/-- **Lemma 8 (uniqueness, real level)**: The weak inverse is the unique element
    satisfying all four Moore-Penrose conditions. -/
theorem weakInvM_unique (td : TubalData n) (a y : Fin n → ℝ)
    (h1 : starM td (starM td a y) a = a)
    (h2 : starM td (starM td y a) y = y)
    (h3 : starConjM td (starM td a y) = starM td a y)
    (h4 : starConjM td (starM td y a) = starM td y a) :
    y = weakInvM td a := by
  apply toComplex_injective
  rw [weakInvM_eq_weakInvC]
  apply weakInvC_unique
  · apply_fun toComplex at h1 using toComplex_injective
    rwa [starM_eq_starMC, starM_eq_starMC] at h1
  · apply_fun toComplex at h2 using toComplex_injective
    rwa [starM_eq_starMC, starM_eq_starMC] at h2
  · apply_fun toComplex at h3 using toComplex_injective
    rwa [starConjM_eq_starConjC, starM_eq_starMC] at h3
  · apply_fun toComplex at h4 using toComplex_injective
    rwa [starConjM_eq_starConjC, starM_eq_starMC] at h4


-- @@ L286-300 verbatim
/-- **Lemma 8 (bundled)**: The weak inverse a⁻ satisfies all four Moore-Penrose conditions,
    and is the unique element doing so. -/
theorem weakInvM_moorePenrose (td : TubalData n) (a : Fin n → ℝ) :
    starM td (starM td a (weakInvM td a)) a = a ∧
    starM td (starM td (weakInvM td a) a) (weakInvM td a) = weakInvM td a ∧
    starConjM td (starM td a (weakInvM td a)) = starM td a (weakInvM td a) ∧
    starConjM td (starM td (weakInvM td a) a) = starM td (weakInvM td a) a ∧
    (∀ y : Fin n → ℝ,
      starM td (starM td a y) a = a →
      starM td (starM td y a) y = y →
      starConjM td (starM td a y) = starM td a y →
      starConjM td (starM td y a) = starM td y a →
      y = weakInvM td a) :=
  ⟨weakInvM_mp1 td a, weakInvM_mp2 td a, weakInvM_mp3 td a, weakInvM_mp4 td a,
   weakInvM_unique td a⟩


-- @@ L302-302 verbatim
/-! ## VN-regularity of KM -/


-- @@ L304-304 verbatim
namespace KM


-- @@ L306-306 verbatim
variable {td : TubalData n}


-- @@ L308-310 verbatim
/-- The weak inverse as an operation on KM elements. -/
noncomputable def weakInv (a : KM n td) : KM n td :=
  ofFun (weakInvM td (toFun a))


-- @@ L312-313 verbatim
@[simp] theorem toFun_weakInv (a : KM n td) :
    toFun (weakInv a) = weakInvM td (toFun a) := rfl


-- @@ L315-318 verbatim
/-- **Lemma 8, MP1 (KM version)**: a * a⁻ * a = a. -/
theorem weakInv_mp1 (a : KM n td) : a * weakInv a * a = a := by
  show ofFun _ = _
  exact congr_arg ofFun (weakInvM_mp1 td _)


-- @@ L320-322 verbatim
/-- K_M is von Neumann regular. -/
noncomputable instance instVonNeumannRegular : VonNeumannRegular (KM n td) where
  vnr a := ⟨weakInv a, weakInv_mp1 a⟩


-- @@ L324-324 verbatim
end KM


-- @@ L326-326 verbatim
end TubalTensor
