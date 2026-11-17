import Mathlib


-- @@ L3-6 verbatim
/-!
  TubalTensor/Defs/Basic.lean
  Tube type, Hadamard product for vectors, embedding ℝ ↪ ℂ.
-/


-- @@ L8-8 verbatim
namespace TubalTensor


-- @@ L10-10 verbatim
open Complex Matrix


-- @@ L12-12 verbatim
/-! ## Hadamard (entrywise) product on vectors -/


-- @@ L14-16 verbatim
/-- Entrywise (Hadamard) product on `Fin n → ℂ`. -/
noncomputable def vecHadamard {n : ℕ} (a b : Fin n → ℂ) : Fin n → ℂ :=
  fun i => a i * b i


-- @@ L18-18 verbatim
scoped infixl:70 " ∘ₕ " => vecHadamard


-- @@ L20-22 verbatim
@[simp]
theorem vecHadamard_apply {n : ℕ} (a b : Fin n → ℂ) (i : Fin n) :
    (a ∘ₕ b) i = a i * b i := rfl


-- @@ L24-25 verbatim
theorem vecHadamard_comm {n : ℕ} (a b : Fin n → ℂ) : a ∘ₕ b = b ∘ₕ a := by
  ext i; simp [mul_comm]


-- @@ L27-29 verbatim
theorem vecHadamard_assoc {n : ℕ} (a b c : Fin n → ℂ) :
    a ∘ₕ b ∘ₕ c = a ∘ₕ(b ∘ₕ c) := by
  ext i; exact mul_assoc _ _ _


-- @@ L31-33 verbatim
theorem vecHadamard_left_distrib {n : ℕ} (a b c : Fin n → ℂ) :
    a ∘ₕ(b + c) = a ∘ₕ b + a ∘ₕ c := by
  ext i; simp [mul_add]


-- @@ L35-37 verbatim
theorem vecHadamard_right_distrib {n : ℕ} (a b c : Fin n → ℂ) :
    (a + b) ∘ₕ c = a ∘ₕ c + b ∘ₕ c := by
  ext i; simp [add_mul]


-- @@ L39-40 verbatim
/-- The all-ones vector in `Fin n → ℂ`. -/
def allOnes (n : ℕ) : Fin n → ℂ := fun _ => 1


-- @@ L42-43 verbatim
@[simp]
theorem allOnes_apply (n : ℕ) (i : Fin n) : allOnes n i = 1 := rfl


-- @@ L45-47 verbatim
theorem vecHadamard_allOnes_left {n : ℕ} (a : Fin n → ℂ) :
    allOnes n ∘ₕ a = a := by
  ext i; simp


-- @@ L49-51 verbatim
theorem vecHadamard_allOnes_right {n : ℕ} (a : Fin n → ℂ) :
    a ∘ₕ allOnes n = a := by
  ext i; simp


-- @@ L53-55 verbatim
theorem vecHadamard_zero_left {n : ℕ} (a : Fin n → ℂ) :
    (0 : Fin n → ℂ) ∘ₕ a = 0 := by
  ext i; simp


-- @@ L57-59 verbatim
theorem vecHadamard_zero_right {n : ℕ} (a : Fin n → ℂ) :
    a ∘ₕ(0 : Fin n → ℂ) = 0 := by
  ext i; simp


-- @@ L61-63 verbatim
theorem vecHadamard_neg_left {n : ℕ} (a b : Fin n → ℂ) :
    (-a) ∘ₕ b = -(a ∘ₕ b) := by
  ext i; simp [neg_mul]


-- @@ L65-67 verbatim
theorem vecHadamard_smul_left {n : ℕ} (r : ℂ) (a b : Fin n → ℂ) :
    (r • a) ∘ₕ b = r • (a ∘ₕ b) := by
  ext i; simp [vecHadamard, mul_assoc]


-- @@ L69-71 verbatim
theorem vecHadamard_conj {n : ℕ} (a b : Fin n → ℂ) :
    starRingEnd ℂ ∘ (a ∘ₕ b) = (starRingEnd ℂ ∘ a) ∘ₕ(starRingEnd ℂ ∘ b) := by
  ext i; simp [vecHadamard, map_mul]


-- @@ L73-73 verbatim
/-! ## Embedding ℝⁿ ↪ ℂⁿ -/


-- @@ L75-77 verbatim
/-- Componentwise embedding of real vectors into complex vectors. -/
def toComplex {n : ℕ} (a : Fin n → ℝ) : Fin n → ℂ :=
  fun i => (a i : ℂ)


-- @@ L79-81 verbatim
@[simp]
theorem toComplex_apply {n : ℕ} (a : Fin n → ℝ) (i : Fin n) :
    toComplex a i = (a i : ℂ) := rfl


-- @@ L83-88 verbatim
theorem toComplex_injective {n : ℕ} : Function.Injective (toComplex (n := n)) := by
  intro a b h
  ext i
  have hi := congr_fun h i
  simp only [toComplex_apply] at hi
  exact_mod_cast hi


-- @@ L90-92 verbatim
theorem toComplex_add {n : ℕ} (a b : Fin n → ℝ) :
    toComplex (a + b) = toComplex a + toComplex b := by
  ext i; simp


-- @@ L94-96 verbatim
theorem toComplex_neg {n : ℕ} (a : Fin n → ℝ) :
    toComplex (-a) = -toComplex a := by
  ext i; simp


-- @@ L98-100 verbatim
theorem toComplex_smul {n : ℕ} (r : ℝ) (a : Fin n → ℝ) :
    toComplex (r • a) = (r : ℂ) • toComplex a := by
  ext i; simp [Complex.ofReal_mul]


-- @@ L102-103 verbatim
theorem toComplex_zero {n : ℕ} : toComplex (0 : Fin n → ℝ) = 0 := by
  ext i; simp


-- @@ L105-107 verbatim
theorem toComplex_sub {n : ℕ} (a b : Fin n → ℝ) :
    toComplex (a - b) = toComplex a - toComplex b := by
  ext i; simp


-- @@ L109-109 verbatim
/-! ## Extracting real part of a complex vector -/


-- @@ L111-113 verbatim
/-- Componentwise real part of a complex vector. -/
def vecRe {n : ℕ} (a : Fin n → ℂ) : Fin n → ℝ :=
  fun i => (a i).re


-- @@ L115-117 verbatim
@[simp]
theorem vecRe_apply {n : ℕ} (a : Fin n → ℂ) (i : Fin n) :
    vecRe a i = (a i).re := rfl


-- @@ L119-121 verbatim
theorem vecRe_toComplex {n : ℕ} (a : Fin n → ℝ) :
    vecRe (toComplex a) = a := by
  ext i; simp


-- @@ L123-125 verbatim
theorem toComplex_vecRe {n : ℕ} (a : Fin n → ℂ) (h : ∀ i, (a i).im = 0) :
    toComplex (vecRe a) = a := by
  ext i; simp [Complex.ext_iff, h i]


-- @@ L127-129 verbatim
/-- A complex vector is real iff every component has zero imaginary part. -/
def IsRealVec {n : ℕ} (a : Fin n → ℂ) : Prop :=
  ∀ i : Fin n, (a i).im = 0


-- @@ L131-135 verbatim
theorem isRealVec_iff_eq_toComplex {n : ℕ} (a : Fin n → ℂ) :
    IsRealVec a ↔ a = toComplex (vecRe a) := by
  constructor
  · intro h; ext i; simp [Complex.ext_iff, h i]
  · intro h i; rw [h]; simp


-- @@ L137-138 verbatim
theorem isRealVec_toComplex {n : ℕ} (a : Fin n → ℝ) : IsRealVec (toComplex a) := by
  intro i; simp


-- @@ L140-142 verbatim
theorem isRealVec_add {n : ℕ} {a b : Fin n → ℂ} (ha : IsRealVec a) (hb : IsRealVec b) :
    IsRealVec (a + b) := by
  intro i; simp [ha i, hb i]


-- @@ L144-146 verbatim
theorem isRealVec_neg {n : ℕ} {a : Fin n → ℂ} (ha : IsRealVec a) :
    IsRealVec (-a) := by
  intro i; simp [ha i]


-- @@ L148-150 verbatim
theorem vecRe_add {n : ℕ} (a b : Fin n → ℂ) :
    vecRe (a + b) = vecRe a + vecRe b := by
  ext i; simp


-- @@ L152-154 verbatim
theorem vecRe_neg {n : ℕ} (a : Fin n → ℂ) :
    vecRe (-a) = -vecRe a := by
  ext i; simp


-- @@ L156-156 verbatim
/-! ## Conjugation on vectors -/


-- @@ L158-160 verbatim
/-- Componentwise complex conjugation of a vector. -/
def vecConj {n : ℕ} (a : Fin n → ℂ) : Fin n → ℂ :=
  fun i => starRingEnd ℂ (a i)


-- @@ L162-164 verbatim
@[simp]
theorem vecConj_apply {n : ℕ} (a : Fin n → ℂ) (i : Fin n) :
    vecConj a i = starRingEnd ℂ (a i) := rfl


-- @@ L166-168 verbatim
theorem vecConj_toComplex {n : ℕ} (a : Fin n → ℝ) :
    vecConj (toComplex a) = toComplex a := by
  ext i; simp [vecConj, Complex.conj_ofReal]


-- @@ L170-170 verbatim
end TubalTensor
