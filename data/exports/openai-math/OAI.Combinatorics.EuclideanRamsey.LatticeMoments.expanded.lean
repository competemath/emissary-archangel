import OAI.Combinatorics.EuclideanRamsey.SmoothingMatrix


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uIndex


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
open scoped TensorProduct RealInnerProductSpace

-- @@ L10-10 verbatim
open scoped BigOperators

-- @@ L11-11 verbatim
open Real Filter Topology MeasureTheory Polynomial

-- @@ L12-12 verbatim
open Matrix MeasureTheory

-- @@ L13-13 verbatim
open MeasureTheory

-- @@ L14-14 verbatim
open Matrix

-- @@ L15-15 verbatim
open scoped MatrixOrder Matrix.Norms.L2Operator

-- @@ L16-16 verbatim
open MeasureTheory Matrix


-- @@ L18-18 verbatim
open scoped TensorProduct

-- @@ L19-19 verbatim
namespace EuclideanRamsey


-- @@ L21-21 verbatim
abbrev Lattice (k : ℕ) := Fin k → ℤ

-- @@ L22-22 verbatim
abbrev RationalSpace (k : ℕ) := Fin k → ℚ

-- @@ L23-23 verbatim
abbrev LatticeRing (k : ℕ) := AddMonoidAlgebra ℚ (Lattice k)


-- @@ L25-28 verbatim
def rationalize {k : ℕ} : Lattice k →+ RationalSpace k where
  toFun γ := fun j => (γ j : ℚ)
  map_zero' := by ext; simp
  map_add' γ δ := by ext; simp


-- @@ L30-31 verbatim
def latticeSpan {k : ℕ} (Λ : AddSubgroup (Lattice k)) : Submodule ℚ (RationalSpace k) :=
  Submodule.span ℚ (rationalize '' (Λ : Set (Lattice k)))


-- @@ L33-35 verbatim
def matrixTensor {k : ℕ} (C : Matrix (Fin k) (Fin k) ℚ) :
    RationalSpace k ⊗[ℚ] RationalSpace k :=
  ∑ a, ∑ b, C a b • ((Pi.single a (1 : ℚ)) ⊗ₜ[ℚ] (Pi.single b (1 : ℚ)))


-- @@ L37-38 verbatim
def quotientTensor {k : ℕ} (Λ : AddSubgroup (Lattice k)) :=
  TensorProduct.map (latticeSpan Λ).mkQ (latticeSpan Λ).mkQ


-- @@ L40-40 verbatim
def mass {k : ℕ} (ν : LatticeRing k) : ℚ := ν.coeff.sum fun _ q => q


-- @@ L42-43 verbatim
def firstMoment {k : ℕ} (ν : LatticeRing k) (a : Fin k) : ℚ :=
  ν.coeff.sum fun γ q => q * γ a


-- @@ L45-46 verbatim
def secondMoment {k : ℕ} (ν : LatticeRing k) (a b : Fin k) : ℚ :=
  ν.coeff.sum fun γ q => q * γ a * γ b


-- @@ L48-49 verbatim
def cosetPushforward {k : ℕ} (Λ : AddSubgroup (Lattice k)) (ν : LatticeRing k) :
    (Lattice k ⧸ Λ) →₀ ℚ := Finsupp.mapDomain (QuotientAddGroup.mk' Λ) ν.coeff


-- @@ L51-57 verbatim
def FiniteLatticeIdentity : Prop :=
  ∀ (k s : ℕ), 1 ≤ k → 1 ≤ s →
    ∀ (Λ : Fin s → AddSubgroup (Lattice k)) (C : Matrix (Fin k) (Fin k) ℚ),
      C.IsSymm → (∀ i, quotientTensor (Λ i) (matrixTensor C) = 0) →
      ∃ ν : LatticeRing k,
        (∀ i, cosetPushforward (Λ i) ν = 0) ∧ mass ν = 0 ∧
        (∀ a, firstMoment ν a = 0) ∧ (∀ a b, secondMoment ν a b = C a b)


-- @@ L59-59 verbatim
section Algebra

-- @@ L60-60 verbatim
variable {k : ℕ}


-- @@ L62-63 verbatim
instance latticeNoetherian : IsNoetherianRing (LatticeRing k) :=
  Algebra.FiniteType.isNoetherianRing ℚ (LatticeRing k)


-- @@ L65-66 verbatim
def augmentation : LatticeRing k →ₐ[ℚ] ℚ :=
  AddMonoidAlgebra.lift ℚ ℚ (Lattice k) 1


-- @@ L68-68 verbatim
def augmentationIdeal : Ideal (LatticeRing k) := RingHom.ker augmentation


-- @@ L70-71 verbatim
lemma augmentation_eq_mass (x : LatticeRing k) : augmentation x = mass x := by
  simp only [augmentation, AddMonoidAlgebra.lift_apply, MonoidHom.one_apply, smul_eq_mul, mul_one, mass]


-- @@ L73-75 verbatim
@[simp] lemma augmentation_monomial (γ : Lattice k) :
    augmentation (AddMonoidAlgebra.single γ 1) = 1 := by
  simp [augmentation]


-- @@ L77-80 verbatim
lemma monomial_sub_one_mem (γ : Lattice k) :
    AddMonoidAlgebra.single γ 1 - 1 ∈ (augmentationIdeal : Ideal (LatticeRing k)) := by
  change augmentation _ = 0
  simp


-- @@ L82-83 verbatim
def coefficientFunctional (g : Lattice k → ℚ) : LatticeRing k →ₗ[ℚ] ℚ :=
  (Finsupp.linearCombination ℚ g).comp (AddMonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap


-- @@ L85-86 verbatim
lemma coefficientFunctional_apply (g : Lattice k → ℚ) (x : LatticeRing k) :
    coefficientFunctional g x = x.coeff.sum (fun γ q => q * g γ) := rfl


-- @@ L88-90 verbatim
@[simp] lemma coefficientFunctional_single (g : Lattice k → ℚ) (γ : Lattice k) (q : ℚ) :
    coefficientFunctional g (AddMonoidAlgebra.single γ q) = q * g γ := by
  simp [coefficientFunctional, Finsupp.linearCombination_apply]


-- @@ L92-94 verbatim
lemma mass_linear : (mass : LatticeRing k → ℚ) = coefficientFunctional (fun _ => 1) := by
  funext x
  simp [coefficientFunctional_apply, mass]


-- @@ L96-97 verbatim
lemma firstMoment_linear (a : Fin k) :
    (fun x : LatticeRing k => firstMoment x a) = coefficientFunctional (fun γ => γ a) := rfl


-- @@ L99-103 verbatim
lemma secondMoment_linear (a b : Fin k) :
    (fun x : LatticeRing k => secondMoment x a b) =
      coefficientFunctional (fun γ => (γ a : ℚ) * γ b) := by
  funext x
  simp only [secondMoment, coefficientFunctional_apply, mul_assoc]


-- @@ L105-106 verbatim
@[simp] lemma mass_add (x y : LatticeRing k) : mass (x+y) = mass x + mass y := by
  simp only [mass_linear, map_add]

-- @@ L107-108 verbatim
@[simp] lemma mass_smul (r : ℚ) (x : LatticeRing k) : mass (r • x) = r * mass x := by
  simp only [mass_linear, map_smul, smul_eq_mul]

-- @@ L109-109 verbatim
@[simp] lemma mass_zero : mass (0 : LatticeRing k) = 0 := by simp only [mass_linear, map_zero]

-- @@ L110-111 verbatim
@[simp] lemma mass_single (γ : Lattice k) (q : ℚ) : mass (AddMonoidAlgebra.single γ q) = q := by
  simp [mass_linear]

-- @@ L112-113 verbatim
@[simp] lemma mass_mul (x y : LatticeRing k) : mass (x*y) = mass x * mass y := by
  simp only [← augmentation_eq_mass, map_mul]

-- @@ L114-117 verbatim
@[simp] lemma firstMoment_add (x y : LatticeRing k) (a : Fin k) :
    firstMoment (x+y) a = firstMoment x a + firstMoment y a := by
  change coefficientFunctional _ (x+y) = _ + _
  exact map_add _ _ _

-- @@ L118-121 verbatim
@[simp] lemma firstMoment_smul (r : ℚ) (x : LatticeRing k) (a : Fin k) :
    firstMoment (r • x) a = r * firstMoment x a := by
  change coefficientFunctional _ (r • x) = _ * _
  exact map_smul _ _ _

-- @@ L122-123 verbatim
@[simp] lemma firstMoment_zero (a : Fin k) : firstMoment (0 : LatticeRing k) a = 0 := by
  exact map_zero (coefficientFunctional (k := k) (fun γ => γ a))

-- @@ L124-125 verbatim
@[simp] lemma firstMoment_single (γ : Lattice k) (q : ℚ) (a : Fin k) :
    firstMoment (AddMonoidAlgebra.single γ q) a = q * γ a := coefficientFunctional_single _ _ _

-- @@ L126-129 verbatim
@[simp] lemma secondMoment_add (x y : LatticeRing k) (a b : Fin k) :
    secondMoment (x+y) a b = secondMoment x a b + secondMoment y a b := by
  have hh := congrFun (secondMoment_linear a b)
  simp only [hh, map_add]

-- @@ L130-133 verbatim
@[simp] lemma secondMoment_smul (r : ℚ) (x : LatticeRing k) (a b : Fin k) :
    secondMoment (r • x) a b = r * secondMoment x a b := by
  have hh := congrFun (secondMoment_linear a b)
  simp only [hh, map_smul, smul_eq_mul]

-- @@ L134-136 verbatim
@[simp] lemma secondMoment_zero (a b : Fin k) : secondMoment (0 : LatticeRing k) a b = 0 := by
  have hh := congrFun (secondMoment_linear a b)
  simp only [hh, map_zero]

-- @@ L137-140 verbatim
@[simp] lemma secondMoment_single (γ : Lattice k) (q : ℚ) (a b : Fin k) :
    secondMoment (AddMonoidAlgebra.single γ q) a b = q * γ a * γ b := by
  have hh := congrFun (secondMoment_linear a b)
  simp only [hh, coefficientFunctional_single, mul_assoc]


-- @@ L142-151 verbatim
lemma firstMoment_mul (x y : LatticeRing k) (a : Fin k) :
    firstMoment (x*y) a = mass x * firstMoment y a + firstMoment x a * mass y := by
  induction x using AddMonoidAlgebra.induction_on with
  | «of» γ =>
    induction y using AddMonoidAlgebra.induction_on with
    | «of» δ => simp [AddMonoidAlgebra.of_apply, AddMonoidAlgebra.single_mul_single, mul_add]; ring
    | add y z hy hz => simp only [mul_add, firstMoment_add,  mass_add, hy, hz]; ring
    | smul r y hy => simp only [mul_smul_comm, firstMoment_smul,  mass_smul, hy]; ring
  | add x z hx hz => simp only [add_mul, firstMoment_add,  mass_add, hx, hz]; ring
  | smul r x hx => simp only [smul_mul_assoc, firstMoment_smul,  mass_smul, hx]; ring


-- @@ L153-163 verbatim
lemma secondMoment_mul (x y : LatticeRing k) (a b : Fin k) :
    secondMoment (x*y) a b = mass x * secondMoment y a b + secondMoment x a b * mass y +
      firstMoment x a * firstMoment y b + firstMoment x b * firstMoment y a := by
  induction x using AddMonoidAlgebra.induction_on with
  | «of» γ =>
    induction y using AddMonoidAlgebra.induction_on with
    | «of» δ => simp [AddMonoidAlgebra.of_apply, AddMonoidAlgebra.single_mul_single, mul_add, add_mul]; ring
    | add y z hy hz => simp only [mul_add, firstMoment_add, secondMoment_add, mass_add, hy, hz]; ring
    | smul r y hy => simp only [mul_smul_comm, firstMoment_smul, secondMoment_smul, mass_smul, hy]; ring
  | add x z hx hz => simp only [add_mul, firstMoment_add, secondMoment_add, mass_add, hx, hz]; ring
  | smul r x hx => simp only [smul_mul_assoc, firstMoment_smul, secondMoment_smul, mass_smul, hx]; ring


-- @@ L165-166 verbatim
@[simp] lemma mass_sub (x y : LatticeRing k) : mass (x-y) = mass x - mass y := by
  simp only [mass_linear, map_sub]

-- @@ L167-169 verbatim
@[simp] lemma firstMoment_sub (x y : LatticeRing k) (a : Fin k) :
    firstMoment (x-y) a = firstMoment x a - firstMoment y a := by
  exact map_sub (coefficientFunctional (k := k) (fun γ => γ a)) x y

-- @@ L170-173 verbatim
@[simp] lemma secondMoment_sub (x y : LatticeRing k) (a b : Fin k) :
    secondMoment (x-y) a b = secondMoment x a b - secondMoment y a b := by
  have hh := congrFun (secondMoment_linear a b)
  simp only [hh, map_sub]

-- @@ L174-176 verbatim
@[simp] lemma mass_one : mass (1 : LatticeRing k) = 1 := by
  change mass (AddMonoidAlgebra.single 0 1) = 1
  simp

-- @@ L177-179 verbatim
@[simp] lemma firstMoment_one (a : Fin k) : firstMoment (1 : LatticeRing k) a = 0 := by
  change firstMoment (AddMonoidAlgebra.single 0 1) a = 0
  simp

-- @@ L180-182 verbatim
@[simp] lemma secondMoment_one (a b : Fin k) : secondMoment (1 : LatticeRing k) a b = 0 := by
  change secondMoment (AddMonoidAlgebra.single 0 1) a b = 0
  simp


-- @@ L184-187 verbatim
lemma mem_augmentationIdeal (x : LatticeRing k) :
    x ∈ augmentationIdeal ↔ mass x = 0 := by
  change augmentation x = 0 ↔ _
  rw [augmentation_eq_mass]


-- @@ L189-195 verbatim
def jetOne : Ideal (LatticeRing k) where
  carrier := {x | mass x = 0 ∧ ∀ a, firstMoment x a = 0}
  zero_mem' := by simp
  add_mem' hx hy := by simp [hx.1, hx.2, hy.1, hy.2]
  smul_mem' r x hx := by
    change mass (r*x) = 0 ∧ ∀ a, firstMoment (r*x) a = 0
    simp [firstMoment_mul, hx.1, hx.2]


-- @@ L197-203 verbatim
def jetTwo : Ideal (LatticeRing k) where
  carrier := {x | mass x = 0 ∧ (∀ a, firstMoment x a = 0) ∧ ∀ a b, secondMoment x a b = 0}
  zero_mem' := by simp
  add_mem' hx hy := by simp [hx.1, hx.2.1, hx.2.2, hy.1, hy.2.1, hy.2.2]
  smul_mem' r x hx := by
    change mass (r*x) = 0 ∧ (∀ a, firstMoment (r*x) a = 0) ∧ ∀ a b, secondMoment (r*x) a b = 0
    simp [firstMoment_mul, secondMoment_mul, hx.1, hx.2.1, hx.2.2]


-- @@ L205-212 verbatim
lemma augmentation_sq_le_jetOne : (augmentationIdeal : Ideal (LatticeRing k)) ^ 2 ≤ jetOne := by
  rw [pow_two]
  apply Ideal.mul_le.mpr
  intro x hx y hy
  have hx0 := (mem_augmentationIdeal x).mp hx
  have hy0 := (mem_augmentationIdeal y).mp hy
  change mass (x*y) = 0 ∧ ∀ a, firstMoment (x*y) a = 0
  simp [firstMoment_mul, hx0, hy0]


-- @@ L214-221 verbatim
lemma augmentation_cube_le_jetTwo : (augmentationIdeal : Ideal (LatticeRing k)) ^ 3 ≤ jetTwo := by
  rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ']
  apply Ideal.mul_le.mpr
  intro x hx y hy
  have hx0 := (mem_augmentationIdeal x).mp hx
  have hy0 : mass y = 0 ∧ ∀ a, firstMoment y a = 0 := augmentation_sq_le_jetOne hy
  change mass (x*y) = 0 ∧ (∀ a, firstMoment (x*y) a = 0) ∧ ∀ a b, secondMoment (x*y) a b = 0
  simp [firstMoment_mul, secondMoment_mul, hx0, hy0]


-- @@ L223-229 verbatim
lemma moments_eq_of_sub_mem_cube {x y : LatticeRing k}
    (h : x-y ∈ (augmentationIdeal : Ideal (LatticeRing k)) ^ 3) :
    mass x = mass y ∧ (∀ a, firstMoment x a = firstMoment y a) ∧
      ∀ a b, secondMoment x a b = secondMoment y a b := by
  have hh := augmentation_cube_le_jetTwo h
  change mass (x-y) = 0 ∧ (∀ a, firstMoment (x-y) a = 0) ∧ ∀ a b, secondMoment (x-y) a b = 0 at hh
  simpa only [mass_sub, firstMoment_sub, secondMoment_sub, sub_eq_zero] using hh


-- @@ L231-233 verbatim
@[simp] lemma mass_sum {ι : Type uIndex} (t : Finset ι) (x : ι → LatticeRing k) :
    mass (∑ i ∈ t, x i) = ∑ i ∈ t, mass (x i) := by
  simp only [mass_linear, map_sum]

-- @@ L234-236 verbatim
@[simp] lemma firstMoment_sum {ι : Type uIndex} (t : Finset ι) (x : ι → LatticeRing k) (a : Fin k) :
    firstMoment (∑ i ∈ t, x i) a = ∑ i ∈ t, firstMoment (x i) a := by
  exact map_sum (coefficientFunctional (k := k) (fun γ => γ a)) x t

-- @@ L237-240 verbatim
@[simp] lemma secondMoment_sum {ι : Type uIndex} (t : Finset ι) (x : ι → LatticeRing k) (a b : Fin k) :
    secondMoment (∑ i ∈ t, x i) a b = ∑ i ∈ t, secondMoment (x i) a b := by
  have hh := congrFun (secondMoment_linear a b)
  simp only [hh, map_sum]


-- @@ L242-243 verbatim
def quadraticStencil (C : Matrix (Fin k) (Fin k) ℚ) (l : Fin k → LatticeRing k) : LatticeRing k :=
  (1/2 : ℚ) • ∑ a, ∑ b, C a b • (l a * l b)


-- @@ L245-262 verbatim
lemma quadraticStencil_moments (C : Matrix (Fin k) (Fin k) ℚ) (hC : C.IsSymm)
    (l : Fin k → LatticeRing k) (hm : ∀ a, mass (l a) = 0)
    (hf : ∀ a b, firstMoment (l a) b = if a = b then 1 else 0) :
    mass (quadraticStencil C l) = 0 ∧ (∀ a, firstMoment (quadraticStencil C l) a = 0) ∧
      (∀ a b, secondMoment (quadraticStencil C l) a b = C a b) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · simp [quadraticStencil, hm]
  · intro a
    simp [quadraticStencil, firstMoment_mul, hm]
  · intro a b
    simp only [quadraticStencil, secondMoment_smul, secondMoment_sum, secondMoment_mul, hm,
      hf, zero_mul, mul_zero, zero_add]
    simp only [mul_add, Finset.sum_add_distrib]
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hs : C b a = C a b := congrFun (congrFun hC a) b
    rw [hs]
    ring


-- @@ L264-264 verbatim
end Algebra

-- @@ L265-265 verbatim
end EuclideanRamsey


-- @@ L267-267 verbatim
end


-- @@ L269-269 verbatim
end OAI
