/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Rodolfo Soldati
-/
module

public import QuantumInfo.ForMathlib.ContinuousLinearMap
public import QuantumInfo.ForMathlib.ComplexLaplaceTransform
public import QuantumInfo.ForMathlib.ContinuousSup
public import QuantumInfo.ForMathlib.Filter
public import QuantumInfo.ForMathlib.HermitianMat
public import QuantumInfo.ForMathlib.Isometry
public import QuantumInfo.ForMathlib.LinearEquiv
public import QuantumInfo.ForMathlib.MatrixNorm.TraceNorm
public import QuantumInfo.ForMathlib.Matrix
public import QuantumInfo.ForMathlib.Minimax
public import QuantumInfo.ForMathlib.Misc
public import QuantumInfo.ForMathlib.Unitary
public import QuantumInfo.ClassicalInfo.Distribution


-- @@ L22-33 verbatim
/-!
Finite dimensional quantum pure states, bra and kets. Mixed states are `MState` in that file.

These could be done with a Hilbert space of Fintype, which would look like
```lean4
(H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]
```
or by choosing a particular `Basis` and asserting it is `Fintype`. But frankly it seems easier to
mostly focus on the basis-dependent notion of `Matrix`, which has the added benefit of an obvious
"classical" interpretation (as the basis elements, or diagonal elements of a mixed state). In that
sense, this quantum theory comes with the a particular classical theory always preferred.
-/


-- @@ L35-35 verbatim
@[expose] public section


-- @@ L37-37 verbatim
noncomputable section


-- @@ L39-39 verbatim
open Classical

-- @@ L40-40 verbatim
open BigOperators

-- @@ L41-41 verbatim
open ComplexConjugate

-- @@ L42-42 verbatim
open Kronecker

-- @@ L43-43 verbatim
open scoped Matrix ComplexOrder


-- @@ L45-45 verbatim
section

-- @@ L46-46 verbatim
variable (d : Type*) [Fintype d]


-- @@ L48-54 verbatim
/-- A ket as a vector of unit norm. We follow the convention in `Matrix` of vectors as simple functions
 from a Fintype. Kets are distinctly not a vector space in our notion, as they represent only normalized
 states and so cannot (in general) be added or scaled. -/
structure Ket where
  vec : d → ℂ
  normalized' : ∑ x, ‖vec x‖ ^ 2 = 1
  --TODO: change to `vec : EuclideanSpace ℂ d` / `normalized' : ‖vec‖ = 1`


-- @@ L56-60 verbatim
/-- A bra is identical in definition to a `Ket`, but are separate to avoid complex conjugation confusion.
 They can be interconverted with the adjoint: `Ket.to_bra` and `Bra.to_ket` -/
structure Bra where
  vec : d → ℂ
  normalized' : ∑ x, ‖vec x‖ ^ 2 =1


-- @@ L62-62 verbatim
end 
-- @@ L62-62 verbatim
section


-- @@ L64-64 verbatim
namespace Braket


-- @@ L66-66 verbatim
scoped notation:max "〈" ψ:90 "∣" => (ψ : Bra _)


-- @@ L68-68 verbatim
scoped notation:max "∣" ψ:90 "〉" => (ψ : Ket _)


-- @@ L70-70 verbatim
variable {d : Type*} [Fintype d]


-- @@ L72-74 verbatim
instance instFunLikeKet : FunLike (Ket d) d ℂ where
  coe ψ := ψ.vec
  coe_injective _ _ h := by rwa [Ket.mk.injEq]


-- @@ L76-76 verbatim
lemma _root_.Ket.coe_fun_eq (ψ : Ket d) : (ψ : d → ℂ) = ψ.vec := rfl


-- @@ L78-80 verbatim
instance instFunLikeBra : FunLike (Bra d) d ℂ where
  coe ψ := ψ.vec
  coe_injective _ _ h := by rwa [Bra.mk.injEq]


-- @@ L82-82 verbatim
lemma _root_.Bra.coe_fun_eq (ψ : Bra d) : (ψ : d → ℂ) = ψ.vec := rfl


-- @@ L84-84 verbatim
def dot (ξ : Bra d) (ψ : Ket d) : ℂ := ∑ x, (ξ x) * (ψ x)


-- @@ L86-86 verbatim
scoped notation "〈" ξ:90 "‖" ψ:90 "〉" => dot (ξ : Bra _) (ψ : Ket _)


-- @@ L88-89 verbatim
theorem dot_eq_dotProduct (ψ : Bra d) (φ : Ket d) :〈ψ‖φ〉= dotProduct (m := d) ψ φ := by
  rfl


-- @@ L91-91 verbatim
end Braket


-- @@ L93-93 verbatim
section braket

-- @@ L94-94 verbatim
open Braket


-- @@ L96-96 verbatim
variable {d : Type*} [Fintype d]


-- @@ L98-99 verbatim
theorem Ket.apply (ψ : Ket d) (i : d) : ψ i = ψ.vec i :=
  rfl


-- @@ L101-102 verbatim
theorem Bra.apply (ψ : Bra d) (i : d) : ψ i = ψ.vec i :=
  rfl


-- @@ L104-106 verbatim
@[ext]
theorem Ket.ext {ξ ψ : Ket d} (h : ∀ x, ξ x = ψ x) : ξ = ψ :=
  DFunLike.ext ξ ψ h


-- @@ L108-110 verbatim
@[ext]
theorem Bra.ext {ξ ψ : Bra d} (h : ∀ x, ξ x = ψ x) : ξ = ψ :=
  DFunLike.ext ξ ψ h


-- @@ L112-115 verbatim
theorem Ket.normalized (ψ : Ket d) : ∑ x, Complex.normSq (ψ x) = 1 := by
  convert ψ.normalized'
  rw [Complex.normSq_eq_norm_sq]
  rfl


-- @@ L117-120 verbatim
theorem Bra.normalized (ψ : Bra d) : ∑ x, Complex.normSq (ψ x) = 1 := by
  convert ψ.normalized'
  rw [Complex.normSq_eq_norm_sq]
  rfl


-- @@ L122-125 verbatim
/-- Any Bra can be turned into a Ket by conjugating the elements. -/
@[coe]
def Ket.to_bra (ψ : Ket d) : Bra d :=
  ⟨conj ψ, by simp_all; exact ψ.2⟩


-- @@ L127-130 verbatim
/-- Any Ket can be turned into a Bra by conjugating the elements. -/
@[coe]
def Bra.to_ket (ψ : Bra d) : Ket d :=
  ⟨conj ψ, by simp_all; exact ψ.2⟩


-- @@ L132-132 verbatim
instance instBraOfKet : Coe (Ket d) (Bra d) := ⟨Ket.to_bra⟩


-- @@ L134-134 verbatim
instance instKetOfBra : Coe (Bra d) (Ket d) := ⟨Bra.to_ket⟩


-- @@ L136-138 verbatim
@[simp]
theorem Bra.eq_conj (ψ : Ket d) (x : d) :〈ψ∣ x = conj (∣ψ〉 x) :=
  rfl


-- @@ L140-141 verbatim
theorem Bra.apply' (ψ : Ket d) (i : d) : 〈ψ∣ i = conj (ψ.vec i) :=
  rfl


-- @@ L143-148 verbatim
theorem Ket.exists_ne_zero (ψ : Ket d) : ∃ x, ψ x ≠ 0 := by
  have hzerolt : ∑ x : d, Complex.normSq (ψ x) > ∑ x : d, 0 := by rw [ψ.normalized, Finset.sum_const_zero]; exact zero_lt_one
  have hpos : ∃ x ∈ Finset.univ, 0 < Complex.normSq (ψ x) := Finset.exists_lt_of_sum_lt hzerolt
  obtain ⟨x, _, hpos⟩ := hpos
  rw [Complex.normSq_pos] at hpos
  use x


-- @@ L150-155 verbatim
theorem Bra.exists_ne_zero (ψ : Bra d) : ∃ x, ψ x ≠ 0 := by
  have hzerolt : ∑ x : d, Complex.normSq (ψ x) > ∑ x : d, 0 := by rw [ψ.normalized, Finset.sum_const_zero]; exact zero_lt_one
  have hpos : ∃ x ∈ Finset.univ, 0 < Complex.normSq (ψ x) := Finset.exists_lt_of_sum_lt hzerolt
  obtain ⟨x, _, hpos⟩ := hpos
  rw [Complex.normSq_pos] at hpos
  use x


-- @@ L157-171 verbatim
/-- Create a ket out of a vector given it has a nonzero component -/
def Ket.normalize (v : d → ℂ) (h : ∃ x, v x ≠ 0) : Ket d :=
  { vec := fun x ↦ v x / √(∑ x : d, ‖v x‖ ^ 2),
    normalized' := by
      simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_div,
        Complex.normSq_ofReal, ←sq]
      have hnonneg : ∑ x : d, Complex.normSq (v x) ≥ 0 := Fintype.sum_nonneg (fun x => Complex.normSq_nonneg (v x))
      simp only [Real.sq_sqrt hnonneg, div_eq_inv_mul, ←Finset.mul_sum]
      apply inv_mul_cancel₀
      by_contra hzero
      rw [Fintype.sum_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg (v x))] at hzero
      obtain ⟨a, ha⟩ := h
      have h₁ : (fun x => Complex.normSq (v x)) a ≠ 0 := by simp only [ne_eq, map_eq_zero]; exact ha
      exact h₁ (congrFun hzero a)
  }


-- @@ L173-177 verbatim
/-- A ket is already normalized -/
theorem Ket.normalize_ket_eq_self (ψ : Ket d) : Ket.normalize (ψ.vec) (Ket.exists_ne_zero ψ) = ψ := by
  ext x
  unfold normalize
  simp only [apply, ψ.normalized', Real.sqrt_one, Complex.ofReal_one, div_one]


-- @@ L179-193 verbatim
/-- Create a bra out of a vector given it has a nonzero component -/
def Bra.normalize (v : d → ℂ) (h : ∃ x, v x ≠ 0) : Bra d :=
  { vec := fun x ↦ v x / √(∑ x : d, ‖v x‖ ^ 2),
    normalized' := by
      simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_div,
      Complex.normSq_ofReal, ←sq]
      have hnonneg : ∑ x : d, Complex.normSq (v x) ≥ 0 := Fintype.sum_nonneg (fun x => Complex.normSq_nonneg (v x))
      simp only [Real.sq_sqrt hnonneg, div_eq_inv_mul, ←Finset.mul_sum]
      apply inv_mul_cancel₀
      by_contra hzero
      rw [Fintype.sum_eq_zero_iff_of_nonneg (fun x => Complex.normSq_nonneg (v x))] at hzero
      obtain ⟨a, ha⟩ := h
      have h₁ : (fun x => Complex.normSq (v x)) a ≠ 0 := by simp only [ne_eq, map_eq_zero]; exact ha
      exact h₁ (congrFun hzero a)
  }


-- @@ L195-199 verbatim
/-- A bra is already normalized -/
lemma Bra.normalize_ket_eq_self (ψ : Bra d) : Bra.normalize (ψ.vec) (Bra.exists_ne_zero ψ) = ψ := by
  ext x
  unfold normalize
  simp only [apply, ψ.normalized', Real.sqrt_one, Complex.ofReal_one, div_one]


-- @@ L201-209 verbatim
/-- Ket form by the superposition of all elements in `d`.
Commonly denoted by |+⟩, especially for qubits -/
def uniform_superposition [hdne : Nonempty d] : Ket d := by
  let f : d → ℂ := fun _ ↦ 1
  have hfnezero : ∃ x, f x ≠ 0 := by
    obtain ⟨i⟩ := hdne
    use i
    simp only [f, ne_eq, one_ne_zero, not_false_eq_true]
  exact Ket.normalize f hfnezero


-- @@ L211-214 verbatim
/-- There exists a ket for every nonempty `d`.
Here, we use the uniform superposition -/
instance instInhabited [Nonempty d] : Inhabited (Ket d) where
  default := uniform_superposition


-- @@ L216-218 verbatim
/-- Construct the Ket corresponding to a basis vector, with a +1 phase. -/
def Ket.basis (i : d) : Ket d :=
  ⟨fun j ↦ if i = j then 1 else 0, by simp [apply_ite]⟩


-- @@ L220-222 verbatim
/-- Construct the Bra corresponding to a basis vector, with a +1 phase. -/
def Bra.basis (i : d) : Bra d :=
  ⟨fun j ↦ if i = j then 1 else 0, by simp [apply_ite]⟩


-- @@ L224-229 verbatim
/-- A Bra can be viewed as a function from Ket's to ℂ. -/
instance instFunLikeBraket : FunLike (Bra d) (Ket d) ℂ where
  coe ξ := dot ξ
  coe_injective x y h := by
    ext i
    simpa [Ket.basis, dot, Ket.apply] using congrFun h (Ket.basis i)


-- @@ L231-236 verbatim
/-- The inner product of any state with itself is 1. -/
@[simp]
theorem Braket.dot_self_eq_one (ψ : Ket d) :〈ψ‖ψ〉= 1 := by
  have h₁ x : conj (ψ x) * ψ x = Complex.normSq (ψ x) := by
    rw [Complex.normSq_eq_conj_mul_self]
  simpa [dot, Bra.eq_conj, h₁] using congr(Complex.ofReal $ψ.normalized)


-- @@ L238-243 verbatim
/-- Swapping the arguments conjugates the bra-ket product:
    `⟨ψ₂|ψ₁⟩ = conj(⟨ψ₁|ψ₂⟩)`. -/
lemma Braket.dot_swap_conj (ψ₁ ψ₂ : Ket d) :
    〈ψ₂‖ψ₁〉 = starRingEnd ℂ 〈ψ₁‖ψ₂〉 := by
  simp +decide [Braket.dot]
  ac_rfl


-- @@ L245-245 verbatim
section prod

-- @@ L246-246 verbatim
variable {d d₁ d₂ : Type*} [Fintype d] [Fintype d₁] [Fintype d₂]


-- @@ L248-253 verbatim
/-- The outer product of two kets, creating an unentangled state. -/
def Ket.prod (ψ₁ : Ket d₁) (ψ₂ : Ket d₂) : Ket (d₁ × d₂) where
  vec := fun (i,j) ↦ ψ₁ i * ψ₂ j
  normalized' := by
    simp [Fintype.sum_prod_type, ← Complex.normSq_eq_norm_sq, mul_pow,
      ← Finset.mul_sum, ψ₁.normalized, ψ₂.normalized]


-- @@ L255-255 verbatim
infixl:100 " ⊗ᵠ " => Ket.prod


-- @@ L257-258 expanded
/-- A Ket is a product if it's `Ket.prod` of two kets. -/
def Ket.IsProd (ψ : Ket (d₁ × d₂)) : Prop :=
  ∃ ξ φ, ψ = Ket.prod ξ φ


-- @@ L260-261 verbatim
/-- A Ket is entangled if it's not `Ket.prod` of two kets. -/
def Ket.IsEntangled (ψ : Ket (d₁ × d₂)) : Prop := ¬ψ.IsProd


-- @@ L263-266 verbatim
/-- `Ket.prod` states are product states. -/
@[simp]
theorem Ket.IsProd_prod (ψ₁ : Ket d₁) (ψ₂ : Ket d₂) : (ψ₁.prod ψ₂).IsProd :=
  ⟨ψ₁, ψ₂, rfl⟩


-- @@ L268-271 verbatim
/-- `Ket.prod` states are not entangled states. -/
@[simp]
theorem Ket.not_IsEntangled_prod (ψ₁ : Ket d₁) (ψ₂ : Ket d₂) : ¬(ψ₁.prod ψ₂).IsEntangled :=
  (· (ψ₁.IsProd_prod ψ₂))


-- @@ L273-337 verbatim
/-- A ket is a product state iff its components are cross-multiplicative. -/
theorem Ket.IsProd_iff_mul_eq_mul (ψ : Ket (d₁ × d₂)) : ψ.IsProd ↔
    ∀ i₁ i₂ j₁ j₂, ψ (i₁,j₁)  * ψ (i₂,j₂) = ψ (i₁,j₂) * ψ (i₂,j₁) := by
  constructor
  · rintro ⟨ξ,φ,rfl⟩ i₁ i₂ j₁ j₂
    simp only [prod, apply]
    ring_nf
  · intro hcrossm
    obtain ⟨⟨a, b⟩, hψnonZero⟩ := Ket.exists_ne_zero ψ
    -- May be able to simplify proof below by using Ket.normalize
    let v₁ : d₁ → ℂ := fun x => ‖ψ (a, b)‖ / (ψ (a, b)) * ((ψ (x, b)) / √(∑ i : d₁, ‖ψ (i, b)‖^2))
    let v₂ : d₂ → ℂ := fun y => ψ (a, y) / √(∑ j : d₂, ‖ψ (a, j)‖^2)
    have hv1Norm : ∑ x, ‖v₁ x‖^2 = 1 := by
      simp only [← Complex.normSq_eq_norm_sq, v₁, Complex.normSq_mul, Complex.normSq_div,
      Complex.normSq_ofReal, ← sq]
      rw [div_self _]
      have hnonneg : ∑ i : d₁, Complex.normSq (ψ (i, b)) ≥ 0 := Fintype.sum_nonneg (fun i => Complex.normSq_nonneg (ψ (i, b)))
      · simp_rw [Real.sq_sqrt hnonneg, one_mul, div_eq_inv_mul, ←Finset.mul_sum]
        apply inv_mul_cancel₀
        by_contra hzero
        rw [Fintype.sum_eq_zero_iff_of_nonneg (fun i => Complex.normSq_nonneg (ψ (i, b)))] at hzero
        have h₁ : (fun i => Complex.normSq (ψ (i,b))) a ≠ 0 := by simp only [ne_eq, map_eq_zero]; exact hψnonZero
        rw [hzero, Pi.zero_apply, ne_eq, eq_self, not_true_eq_false] at h₁
        exact h₁
      · simp_all only [ne_eq, map_eq_zero, not_false_eq_true]
    have hv2Norm : ∑ x, ‖v₂ x‖^2 = 1 := by
      simp only [← Complex.normSq_eq_norm_sq, v₂, Complex.normSq_div,
      Complex.normSq_ofReal, ← sq]
      have hnonneg : ∑ j : d₂, Complex.normSq (ψ (a, j)) ≥ 0 := Fintype.sum_nonneg (fun j => Complex.normSq_nonneg (ψ (a, j)))
      simp_rw [Real.sq_sqrt hnonneg, div_eq_inv_mul, ←Finset.mul_sum]
      apply inv_mul_cancel₀
      by_contra hzero
      rw [Fintype.sum_eq_zero_iff_of_nonneg (fun j => Complex.normSq_nonneg (ψ (a, j)))] at hzero
      have h₁ : (fun j => Complex.normSq (ψ (a, j))) b ≠ 0 := by simp only [ne_eq, map_eq_zero]; exact hψnonZero
      rw [hzero, Pi.zero_apply, ne_eq, eq_self, not_true_eq_false] at h₁
      exact h₁
    let ψ₁ : Ket d₁ := ⟨v₁, hv1Norm⟩
    let ψ₂ : Ket d₂ := ⟨v₂, hv2Norm⟩
    use ψ₁, ψ₂
    ext ⟨x, y⟩
    have hψfun : ψ (x, y) = (ψ (x, b) * ψ (a, y)) / ψ (a, b) := eq_div_of_mul_eq hψnonZero (hcrossm x a y b)
    have hψnorm : (∑ z : d₁ × d₂, Complex.normSq (ψ.vec (z.1, b) * ψ.vec (a, z.2))) = Complex.normSq (ψ (a, b)) :=
    calc
      ∑ z : d₁ × d₂, Complex.normSq (ψ.vec (z.1, b) * ψ.vec (a, z.2)) =
        ∑ z : d₁ × d₂, Complex.normSq (ψ.vec (a, b) * ψ.vec (z.1, z.2)) := by simp only [← apply, hcrossm, mul_comm]
      _ = ∑ z : d₁ × d₂, Complex.normSq (ψ.vec (a, b)) * Complex.normSq (ψ.vec (z.1, z.2)) := by simp only [Complex.normSq_mul]
      _ = Complex.normSq (ψ.vec (a, b)) * ∑ z : d₁ × d₂, Complex.normSq (ψ.vec z) := by rw [←Finset.mul_sum]
      _ = Complex.normSq (ψ.vec (a, b)) := by simp only [← apply, ψ.normalized, mul_one]
    simp [prod, apply, ψ₁, ψ₂, v₁, v₂]
    rw [mul_assoc, ←mul_div_mul_comm, ←Complex.ofReal_mul, ←Real.sqrt_mul (Finset.sum_nonneg _)]
    ·
      simp_rw [Fintype.sum_mul_sum, ←Fintype.sum_prod_type']
      simp only [← Complex.normSq_eq_norm_sq]
      simp_rw [Fintype.sum_congr _ _ (fun z : d₁ × d₂ => (Complex.normSq_mul (ψ.vec (z.1, b)) (ψ.vec (a, z.2))).symm)]
      simp_rw [hψnorm, Complex.normSq_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_norm, apply]
      ring_nf
      rw [mul_comm, ←mul_assoc, ←mul_assoc, ←mul_assoc]
      nth_rw 2 [←inv_inv (Complex.ofReal (‖ψ.vec (a, b)‖))]
      rw [Complex.mul_inv_cancel _]
      · rw [one_mul]
        ring_nf at hψfun
        simp_rw [Ket.apply, mul_comm, mul_comm (ψ.vec (a, y)) _, ←mul_assoc] at hψfun
        exact hψfun
      · simp_all [Ket.apply]
    · simp

-- @@ L338-338 verbatim
end prod


-- @@ L340-340 verbatim
section mes

-- @@ L341-347 verbatim
/-- The Maximally Entangled State, or MES, on a d×d system. In principle there are many, this
is specifically the MES with an all-positive phase. For instance on `d := Fin 2`, this is the
Bell state. -/
def Ket.MES (d) [Fintype d] [Nonempty d] : Ket (d × d) where
  vec := fun (i,j) ↦ if i = j then 1 / Real.sqrt (Fintype.card (α := d)) else 0
  normalized' := by
    simp [apply_ite, Fintype.sum_prod_type]


-- @@ L349-355 verbatim
/-- On any space of dimension at least two, the maximally entangled state `MES` is entangled. -/
theorem Ket.MES_isEntangled [Nontrivial d] : (Ket.MES d).IsEntangled := by
  obtain ⟨x, y, h⟩ := @Nontrivial.exists_pair_ne d _
  rw [IsEntangled, MES, IsProd_iff_mul_eq_mul]
  push Not
  use x, y, x, y
  simp [apply, h]


-- @@ L357-371 verbatim
/-- The transpose trick -/
theorem transposeTrick {d} [Fintype d] [Nonempty d] [DecidableEq d] {M : Matrix d d ℂ} :
    (M ⊗ₖ 1) *ᵥ (Ket.MES d).vec = (1 ⊗ₖ M.transpose) *ᵥ (Ket.MES d).vec := by
  ext i
  simp only [Ket.MES, Matrix.mulVec, dotProduct, Matrix.kroneckerMap, Matrix.one_apply]
  simp
  conv =>
    enter [1, 2, a]
    equals if (i.2, i.2) = a then (M i.1 i.2) / √(Fintype.card d) else 0 =>
      grind
  conv =>
    enter [2, 2, a]
    equals if (i.1, i.1) = a then (M i.1 i.2) / √(Fintype.card d) else 0 =>
      grind
  simp


-- @@ L373-373 verbatim
end mes


-- @@ L375-375 verbatim
section equiv


-- @@ L377-389 verbatim
/-- The equivalence relation on `Ket` where two kets equivalent if they are equal up to a
global phase, i.e. `∃ z, ‖z‖ = 1 ∧ a.vec = z • b.vec -/
def Ket.PhaseEquiv : Setoid (Ket d) where
  r a b := ∃ z : ℂ, ‖z‖ = 1 ∧ a.vec = z • b.vec
  iseqv := {
    refl := fun x ↦ ⟨1, by simp⟩,
    symm := fun ⟨z,h₁,h₂⟩ ↦ ⟨conj z,
      by simp [h₁],
      by simp [h₁, h₂, smul_smul, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]⟩,
    trans := fun ⟨z₁,h₁₁,h₁₂⟩ ⟨z₂,h₂₁,h₂₂⟩ ↦ ⟨z₁ * z₂,
      by simp [h₁₁, h₂₁],
      by simp [h₁₂, h₂₂, smul_smul]⟩
  }


-- @@ L391-395 verbatim
variable (d) in
/-- The type of `Ket`s up to a global phase equivalence, as given by `Ket.PhaseEquiv`.
In particular, `MState`s really only care about a KetUpToPhase, and not Kets themselves. -/
def KetUpToPhase :=
  @Quotient (Ket d) Ket.PhaseEquiv


-- @@ L397-399 verbatim
/-- Construct a `KetUpToPhase` from a `Ket`. -/
def KetUpToPhase.mk (ψ : Ket d) : KetUpToPhase d :=
  @Quotient.mk _ Ket.PhaseEquiv ψ


-- @@ L401-404 verbatim
/-- Lift a function on `Ket d` to `KetUpToPhase d`, given that it respects phase equivalence. -/
def KetUpToPhase.lift {α : Sort*} (f : Ket d → α)
    (hf : ∀ ψ φ, Ket.PhaseEquiv.r ψ φ → f ψ = f φ) : KetUpToPhase d → α :=
  @Quotient.lift _ _ Ket.PhaseEquiv f hf


-- @@ L406-409 verbatim
@[simp]
theorem KetUpToPhase.lift_mk {α : Sort*} (f : Ket d → α)
    (hf : ∀ ψ φ, Ket.PhaseEquiv.r ψ φ → f ψ = f φ) (ψ : Ket d) :
    KetUpToPhase.lift f hf (KetUpToPhase.mk ψ) = f ψ := rfl


-- @@ L411-413 verbatim
theorem KetUpToPhase.ind {p : KetUpToPhase d → Prop}
    (h : ∀ ψ : Ket d, p (KetUpToPhase.mk ψ)) : ∀ q, p q :=
  @Quotient.ind _ Ket.PhaseEquiv p h


-- @@ L415-416 verbatim
theorem KetUpToPhase.surjective_mk : Function.Surjective (KetUpToPhase.mk (d := d)) :=
  fun q => @Quotient.ind _ Ket.PhaseEquiv (fun q => ∃ a, KetUpToPhase.mk a = q) (fun a => ⟨a, rfl⟩) q


-- @@ L418-418 verbatim
end equiv


-- @@ L420-420 verbatim
/-! ## Norm bounds -/


-- @@ L422-422 verbatim
section norm_bounds

-- @@ L423-423 verbatim
open Braket


-- @@ L425-425 verbatim
variable {d : Type*} [Fintype d]


-- @@ L427-428 verbatim
private def ketToEuclidean (ψ : Ket d) : EuclideanSpace ℂ d :=
  (WithLp.equiv 2 _).symm ψ.vec


-- @@ L430-432 verbatim
private lemma ketToEuclidean_norm (ψ : Ket d) : ‖ketToEuclidean ψ‖ = 1 := by
  rw [EuclideanSpace.norm_eq]; convert! Real.sqrt_one
  simp only [ketToEuclidean]; convert! ψ.normalized'


-- @@ L434-441 verbatim
private lemma dot_eq_euclidean_inner (ψ₁ ψ₂ : Ket d) :
    〈ψ₁‖ψ₂〉 = @inner ℂ (EuclideanSpace ℂ d) _
      (ketToEuclidean ψ₁) (ketToEuclidean ψ₂) := by
  unfold dot ketToEuclidean
  simp only [Bra.eq_conj, PiLp.inner_apply]
  congr 1; ext x
  rw [RCLike.inner_apply']
  simp [WithLp.equiv, Ket.apply]


-- @@ L443-448 verbatim
/-- The bra-ket product of normalized states has norm at most 1 (Cauchy-Schwarz). -/
lemma Braket.norm_dot_le_one (ψ₁ ψ₂ : Ket d) : ‖〈ψ₁‖ψ₂〉‖ ≤ 1 := by
  rw [dot_eq_euclidean_inner]
  calc ‖@inner ℂ (EuclideanSpace ℂ d) _ (ketToEuclidean ψ₁) (ketToEuclidean ψ₂)‖
      ≤ ‖ketToEuclidean ψ₁‖ * ‖ketToEuclidean ψ₂‖ := norm_inner_le_norm _ _
    _ = 1 := by rw [ketToEuclidean_norm, ketToEuclidean_norm, mul_one]


-- @@ L450-450 verbatim
end norm_bounds


-- @@ L452-452 verbatim
end braket
