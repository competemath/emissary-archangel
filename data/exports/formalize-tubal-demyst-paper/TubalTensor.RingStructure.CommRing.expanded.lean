import TubalTensor.RingStructure.Realness


-- @@ L3-9 verbatim
/-!
  TubalTensor/RingStructure/CommRing.lean
  Theorem 3: K_M is a commutative unital ring.

  We define the type KM n td as a wrapper around Fin n → ℝ equipped
  with the ⋆_M product, and prove it forms a commutative ring.
-/


-- @@ L11-11 verbatim
namespace TubalTensor


-- @@ L13-13 verbatim
open Complex Matrix


-- @@ L15-15 verbatim
variable {n : ℕ}


-- @@ L17-17 verbatim
/-! ## The type KM: tubes with the ⋆_M ring structure -/


-- @@ L19-21 verbatim
/-- The type of n-tubes with the ⋆_M ring structure.
    As a set this is ℝⁿ, but it carries a different multiplication. -/
def KM (n : ℕ) (_td : TubalData n) := Fin n → ℝ


-- @@ L23-23 verbatim
namespace KM


-- @@ L25-25 verbatim
variable {td : TubalData n}


-- @@ L27-27 verbatim
noncomputable instance : DecidableEq (KM n td) := inferInstanceAs (DecidableEq (Fin n → ℝ))


-- @@ L29-30 verbatim
/-- Coerce from KM to the underlying function type. -/
def toFun (a : KM n td) : Fin n → ℝ := a


-- @@ L32-33 verbatim
/-- Construct a KM element from a function. -/
def ofFun (a : Fin n → ℝ) : KM n td := a


-- @@ L35-37 verbatim
@[ext]
theorem ext {a b : KM n td} (h : ∀ i, toFun a i = toFun b i) : a = b :=
  funext h


-- @@ L39-39 verbatim
@[simp] theorem ofFun_toFun (a : KM n td) : ofFun (toFun a) = a := rfl

-- @@ L40-40 verbatim
@[simp] theorem toFun_ofFun (a : Fin n → ℝ) : toFun (ofFun a : KM n td) = a := rfl


-- @@ L42-42 verbatim
/-! ## Additive structure (inherited from Fin n → ℝ) -/


-- @@ L44-44 verbatim
noncomputable instance : Zero (KM n td) := ⟨ofFun 0⟩

-- @@ L45-45 verbatim
noncomputable instance : Add (KM n td) := ⟨fun a b => ofFun (toFun a + toFun b)⟩

-- @@ L46-46 verbatim
noncomputable instance : Neg (KM n td) := ⟨fun a => ofFun (-toFun a)⟩

-- @@ L47-47 verbatim
noncomputable instance : Sub (KM n td) := ⟨fun a b => ofFun (toFun a - toFun b)⟩


-- @@ L49-50 verbatim
noncomputable instance : SMul ℤ (KM n td) :=
  ⟨fun z a => ofFun (z • toFun a)⟩


-- @@ L52-53 verbatim
noncomputable instance : SMul ℕ (KM n td) :=
  ⟨fun n a => ofFun (n • toFun a)⟩


-- @@ L55-55 verbatim
@[simp] theorem toFun_zero : toFun (0 : KM n td) = 0 := rfl

-- @@ L56-56 verbatim
@[simp] theorem toFun_add (a b : KM n td) : toFun (a + b) = toFun a + toFun b := rfl

-- @@ L57-57 verbatim
@[simp] theorem toFun_neg (a : KM n td) : toFun (-a) = -toFun a := rfl

-- @@ L58-58 verbatim
@[simp] theorem toFun_sub (a b : KM n td) : toFun (a - b) = toFun a - toFun b := rfl

-- @@ L59-59 verbatim
@[simp] theorem toFun_nsmul (k : ℕ) (a : KM n td) : toFun (k • a) = k • toFun a := rfl

-- @@ L60-60 verbatim
@[simp] theorem toFun_zsmul (k : ℤ) (a : KM n td) : toFun (k • a) = k • toFun a := rfl


-- @@ L62-69 verbatim
noncomputable instance : AddCommGroup (KM n td) where
  add_assoc a b c := show ofFun _ = ofFun _ from congr_arg ofFun (add_assoc _ _ _)
  zero_add a := show ofFun _ = _ from congr_arg ofFun (zero_add _)
  add_zero a := show ofFun _ = _ from congr_arg ofFun (add_zero _)
  add_comm a b := show ofFun _ = ofFun _ from congr_arg ofFun (add_comm _ _)
  neg_add_cancel a := show ofFun _ = ofFun _ from congr_arg ofFun (neg_add_cancel _)
  nsmul := (· • ·)
  zsmul := (· • ·)


-- @@ L71-71 verbatim
/-! ## Multiplicative structure via ⋆_M -/


-- @@ L73-75 verbatim
/-- The ⋆_M multiplication on KM. -/
noncomputable instance : Mul (KM n td) :=
  ⟨fun a b => ofFun (starM td (toFun a) (toFun b))⟩


-- @@ L77-78 verbatim
@[simp] theorem toFun_mul (a b : KM n td) :
    toFun (a * b) = starM td (toFun a) (toFun b) := rfl


-- @@ L80-81 verbatim
/-- The unit element of KM: eM = M⁻¹ * 1 -/
noncomputable instance : One (KM n td) := ⟨ofFun (unitTube td)⟩


-- @@ L83-83 verbatim
@[simp] theorem toFun_one : toFun (1 : KM n td) = unitTube td := rfl


-- @@ L85-85 verbatim
/-! ## Core proof: ⋆_M associativity via complex lift -/


-- @@ L87-93 verbatim
/-- Helper: the starMC complex product is associative. -/
private theorem starMC_assoc (td : TubalData n) (a b c : Fin n → ℂ) :
    starMC td (starMC td a b) c = starMC td a (starMC td b c) := by
  unfold starMC
  congr 1
  rw [td.applyM_applyMinv, td.applyM_applyMinv]
  exact vecHadamard_assoc _ _ _


-- @@ L95-100 verbatim
/-- Helper: the starMC complex product is commutative. -/
private theorem starMC_comm (td : TubalData n) (a b : Fin n → ℂ) :
    starMC td a b = starMC td b a := by
  unfold starMC
  congr 1
  exact vecHadamard_comm _ _


-- @@ L102-110 verbatim
/-- Helper: starMC distributes over addition on the left. -/
private theorem starMC_add_left (td : TubalData n) (a b c : Fin n → ℂ) :
    starMC td (a + b) c = starMC td a c + starMC td b c := by
  show td.applyMinv _ = td.applyMinv _ + td.applyMinv _
  rw [← td.applyMinv_add]
  congr 1
  show td.applyM (a + b) ∘ₕ td.applyM c =
    td.applyM a ∘ₕ td.applyM c + td.applyM b ∘ₕ td.applyM c
  rw [td.applyM_add, vecHadamard_right_distrib]


-- @@ L112-117 verbatim
/-- Helper: the unit element is indeed a left identity for starMC. -/
private theorem starMC_one_left (td : TubalData n) (a : Fin n → ℂ) :
    starMC td (td.applyMinv (allOnes n)) a = a := by
  unfold starMC
  rw [td.applyM_applyMinv, vecHadamard_allOnes_left]
  exact td.applyMinv_applyM a


-- @@ L119-126 verbatim
/-- Helper: zero is absorbing for starMC. -/
private theorem starMC_zero_left (td : TubalData n) (a : Fin n → ℂ) :
    starMC td 0 a = 0 := by
  show td.applyMinv (td.applyM (0 : Fin n → ℂ) ∘ₕ td.applyM a) = 0
  have h1 : td.applyM (0 : Fin n → ℂ) = 0 := Matrix.mulVec_zero _
  rw [h1, vecHadamard_zero_left]
  show td.M_inv *ᵥ (0 : Fin n → ℂ) = 0
  exact Matrix.mulVec_zero _


-- @@ L128-137 verbatim
/-- Helper: negation in starMC. -/
private theorem starMC_neg_left (td : TubalData n) (a b : Fin n → ℂ) :
    starMC td (-a) b = -starMC td a b := by
  show td.applyMinv (td.applyM (-a) ∘ₕ td.applyM b) =
    -td.applyMinv (td.applyM a ∘ₕ td.applyM b)
  rw [show td.applyM (-a) = -td.applyM a from Matrix.mulVec_neg _ _]
  rw [vecHadamard_neg_left]
  show td.M_inv *ᵥ -(td.applyM a ∘ₕ td.applyM b) =
    -(td.M_inv *ᵥ (td.applyM a ∘ₕ td.applyM b))
  exact Matrix.mulVec_neg _ td.M_inv


-- @@ L139-139 verbatim
/-! ## Lift to real operations via toComplex embedding -/


-- @@ L141-145 verbatim
theorem starM_assoc (td : TubalData n) (a b c : Fin n → ℝ) :
    starM td (starM td a b) c = starM td a (starM td b c) := by
  apply toComplex_injective
  rw [starM_eq_starMC, starM_eq_starMC, starM_eq_starMC, starM_eq_starMC]
  exact starMC_assoc td _ _ _


-- @@ L147-151 verbatim
theorem starM_comm (td : TubalData n) (a b : Fin n → ℝ) :
    starM td a b = starM td b a := by
  apply toComplex_injective
  rw [starM_eq_starMC, starM_eq_starMC]
  exact starMC_comm td _ _


-- @@ L153-157 verbatim
theorem starM_add_left (td : TubalData n) (a b c : Fin n → ℝ) :
    starM td (a + b) c = starM td a c + starM td b c := by
  apply toComplex_injective
  rw [toComplex_add, starM_eq_starMC, starM_eq_starMC, starM_eq_starMC, toComplex_add]
  exact starMC_add_left td _ _ _


-- @@ L159-163 verbatim
theorem starM_unitTube_left (td : TubalData n) (a : Fin n → ℝ) :
    starM td (unitTube td) a = a := by
  apply toComplex_injective
  rw [starM_eq_starMC, toComplex_unitTube]
  exact starMC_one_left td _


-- @@ L165-170 verbatim
theorem starM_zero_left (td : TubalData n) (a : Fin n → ℝ) :
    starM td 0 a = 0 := by
  apply toComplex_injective
  rw [toComplex_zero, starM_eq_starMC]
  show starMC td 0 (toComplex a) = 0
  exact starMC_zero_left td _


-- @@ L172-176 verbatim
theorem starM_neg_left (td : TubalData n) (a b : Fin n → ℝ) :
    starM td (-a) b = -(starM td a b) := by
  apply toComplex_injective
  rw [starM_eq_starMC, toComplex_neg, toComplex_neg, starM_eq_starMC]
  exact starMC_neg_left td _ _


-- @@ L178-178 verbatim
/-! ## Assembling the CommRing instance (Theorem 3) -/


-- @@ L180-208 verbatim
/-- **Theorem 3**: (KM n td, +, ⋆_M) is a commutative unital ring. -/
noncomputable instance instCommRing : CommRing (KM n td) where
  mul_assoc a b c := by
    show ofFun _ = ofFun _; exact congr_arg ofFun (starM_assoc td _ _ _)
  one_mul a := by
    show ofFun _ = _; exact congr_arg ofFun (starM_unitTube_left td _)
  mul_one a := by
    show ofFun _ = _
    have : starM td (toFun a) (unitTube td) = toFun a := by
      rw [starM_comm]; exact starM_unitTube_left td _
    exact congr_arg ofFun this
  mul_comm a b := by
    show ofFun _ = ofFun _; exact congr_arg ofFun (starM_comm td _ _)
  left_distrib a b c := by
    show ofFun _ = ofFun _
    have : starM td (toFun a) (toFun b + toFun c) =
           starM td (toFun a) (toFun b) + starM td (toFun a) (toFun c) := by
      rw [starM_comm td _ (toFun b + toFun c), starM_add_left,
          starM_comm td (toFun b), starM_comm td (toFun c)]
    exact congr_arg ofFun this
  right_distrib a b c := by
    show ofFun _ = ofFun _; exact congr_arg ofFun (starM_add_left td _ _ _)
  zero_mul a := by
    show ofFun _ = ofFun _; exact congr_arg ofFun (starM_zero_left td _)
  mul_zero a := by
    show ofFun _ = ofFun _
    have : starM td (toFun a) 0 = 0 := by
      rw [starM_comm]; exact starM_zero_left td _
    exact congr_arg ofFun this


-- @@ L210-212 verbatim
/-- KM is also an ℝ-module via the usual scalar-vector multiplication. -/
noncomputable instance instModule : Module ℝ (KM n td) :=
  inferInstanceAs (Module ℝ (Fin n → ℝ))


-- @@ L214-214 verbatim
/-! ## Algebra and finite-dimensionality -/


-- @@ L216-224 verbatim
/-- Scalar multiplication commutes with ⋆_M: (r • a) ⋆_M b = r • (a ⋆_M b). -/
private theorem smul_starM (td : TubalData n) (r : ℝ) (a b : Fin n → ℝ) :
    starM td (r • a) b = r • starM td a b := by
  apply toComplex_injective
  rw [toComplex_smul, starM_eq_starMC, starM_eq_starMC, toComplex_smul]
  show td.applyMinv (td.applyM ((r : ℂ) • toComplex a) ∘ₕ td.applyM (toComplex b)) =
    (r : ℂ) • td.applyMinv (td.applyM (toComplex a) ∘ₕ td.applyM (toComplex b))
  unfold TubalData.applyM TubalData.applyMinv
  rw [Matrix.mulVec_smul, vecHadamard_smul_left, ← Matrix.mulVec_smul]


-- @@ L226-239 verbatim
/-- **Proposition 5 prerequisite**: KM is an ℝ-algebra. -/
@[reducible] private noncomputable def mkAlgebra : Algebra ℝ (KM n td) :=
  Algebra.ofModule
    (fun r (x y : KM n td) => by
      change ofFun (starM td (r • toFun x) (toFun y)) = ofFun (r • starM td (toFun x) (toFun y))
      exact congr_arg ofFun (smul_starM td r (toFun x) (toFun y)))
    (fun r (x y : KM n td) => by
      change ofFun (starM td (toFun x) (r • toFun y)) = ofFun (r • starM td (toFun x) (toFun y))
      rw [starM_comm td (toFun x) (r • toFun y), starM_comm td (toFun x) (toFun y)]
      exact congr_arg ofFun (smul_starM td r (toFun y) (toFun x)))

-- Note: `Algebra.ofModule` is an `abbrev`, and writing `instance := Algebra.ofModule ...`
-- directly causes Lean to not register the instance in the typeclass system.
-- The workaround is to define the body as a `def` and assign it to the instance.

-- @@ L240-241 verbatim
/-- **Proposition 5**: KM is an ℝ-algebra (scalar multiplication commutes with ⋆_M). -/
noncomputable instance instAlgebra : Algebra ℝ (KM n td) := mkAlgebra


-- @@ L243-245 verbatim
/-- KM is finite-dimensional over ℝ (dimension n). -/
noncomputable instance instFiniteDimensional : FiniteDimensional ℝ (KM n td) :=
  inferInstanceAs (FiniteDimensional ℝ (Fin n → ℝ))


-- @@ L247-248 verbatim
theorem finrank_eq : Module.finrank ℝ (KM n td) = n :=
  Module.finrank_fin_fun (R := ℝ)


-- @@ L250-250 verbatim
end KM


-- @@ L252-252 verbatim
end TubalTensor
