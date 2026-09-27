/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import LeanPool.CompositionAlgebras.Composition.Defs
public import LeanPool.CompositionAlgebras.OctonionModule
public import Mathlib.Algebra.Quaternion
public import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Tactic.Positivity.Finset



-- @@ L20-58 verbatim
/-!
# The four Euclidean composition algebras

`ℝ`, `ℂ`, `ℍ` and `𝕆` carry `CompositionAlgebra` structures, of real dimensions
`1, 2, 4, 8`. Hurwitz's theorem says there are no others.

★ **Why this file exists at all.** `Composition/Defs.lean` states a class. A class with no
witness proves nothing, and every theorem quantified over it is vacuously true — the exact
defect shape this development has been bitten by before. These four instances are what makes
the class non-vacuous, and they are also the *targets* of the classification: the statement
"`C` is one of the four" is only meaningful once the four are objects.

## The instances

* `Real.instCompositionAlgebra` — `N x = x²`.
* `Complex.instCompositionAlgebra` — `N z = |z|²`; the composition law is the
  Diophantus two-square identity.
* `Quaternion.instCompositionAlgebra` — `N q = ‖q‖²`; Euler's four-square identity, taken
  from `Mathlib`'s `Quaternion.normSq` as a `MonoidWithZeroHom`.
* `Octonion.instCompositionAlgebra` — Degen's eight-square identity, taken from the tree's
  `Octonion.norm_multiplicative`.

★ The octonion instance is the sharpest cross-check available on `Composition/Defs.lean`:
`norm_multiplicative` was proved in `Octonions.lean` from the hard-coded Fano multiplication
table, with no reference to composition algebras at all, and it discharges `B_comp` after one
rewrite — `octIp_self_eq_norm_sq`, which is `∑ xᵢxᵢ = ∑ xᵢ²` and nothing more. So the class
field really is the composition property and not a mis-transcription of it.
★ An earlier draft of this paragraph said "discharges `B_comp` **verbatim**". It does not: the
`simp only [ipBilin_apply, octIp_self_eq_norm_sq]` in front of it is load-bearing, because the
class is stated on the bilinear form and `Octonions.lean` states the identity on `normSq`.

★ `𝕆` needs `NonAssocRing Octonion`, `One Octonion`, `IsScalarTower` and `SMulCommClass`,
none of which were in the tree — `Octonions.lean` has a bare `Mul` instance and a `def one`.
They are assembled here from the distributivity and unit lemmas already proved there.

## Scope

Substrate, and the non-vacuity witness for `Composition/Defs.lean`'s class.
-/


-- @@ L60-60 verbatim
@[expose] public section


-- @@ L62-62 verbatim
noncomputable section


-- @@ L64-64 verbatim
open CompositionAlgebra

-- @@ L65-65 verbatim
open scoped Quaternion


-- @@ L67-67 verbatim
/-! ## `ℝ` -/


-- @@ L69-74 verbatim
/-- `ℝ` is a Euclidean composition algebra with `N x = x²`. -/
instance Real.instCompositionAlgebra : CompositionAlgebra ℝ where
  B := LinearMap.mul ℝ ℝ
  B_symm x y := by simp only [LinearMap.mul_apply']; ring
  B_pos x hx := by simp only [LinearMap.mul_apply']; exact mul_self_pos.mpr hx
  B_comp x y := by simp only [LinearMap.mul_apply']; ring


-- @@ L76-76 verbatim
theorem Real.nf_eq (x : ℝ) : nf x = x * x := rfl


-- @@ L78-78 verbatim
/-! ## `ℂ` -/


-- @@ L80-88 verbatim
/-- The real inner product on `ℂ`. -/
def Complex.ipBilin : ℂ →ₗ[ℝ] ℂ →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => x.re * y.re + x.im * y.im)
    (by intro x y z; simp only [Complex.add_re, Complex.add_im]; ring)
    (by intro c x y; simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, smul_eq_mul]; ring)
    (by intro x y z; simp only [Complex.add_re, Complex.add_im]; ring)
    (by intro c x y; simp only [Complex.real_smul, Complex.mul_re, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, smul_eq_mul]; ring)


-- @@ L90-91 verbatim
@[simp] theorem Complex.ipBilin_apply (x y : ℂ) :
    Complex.ipBilin x y = x.re * y.re + x.im * y.im := rfl


-- @@ L93-102 verbatim
/-- `ℂ` is a Euclidean composition algebra with `N z = |z|²`. The composition law is the
two-square identity. -/
instance Complex.instCompositionAlgebra : CompositionAlgebra ℂ where
  B := Complex.ipBilin
  B_symm x y := by simp only [Complex.ipBilin_apply]; ring
  B_pos x hx := by
    have h : 0 < Complex.normSq x := Complex.normSq_pos.mpr hx
    simpa [Complex.normSq_apply] using h
  B_comp x y := by
    simp only [Complex.ipBilin_apply, Complex.mul_re, Complex.mul_im]; ring


-- @@ L104-104 verbatim
theorem Complex.nf_eq (z : ℂ) : nf z = z.re * z.re + z.im * z.im := rfl


-- @@ L106-106 verbatim
/-! ## `ℍ` -/


-- @@ L108-111 verbatim
/-! ★ `ℍ` carries its own componentwise `SMul ℝ ℍ[ℝ]` (`Quaternion.instSMul`), which shadows
`Algebra.toSMul`. So `IsScalarTower.right` and `Algebra.to_smulCommClass` do **not** apply —
they are stated for `Algebra.toSMul` — and the two bilinearity classes have to be proved
against the componentwise action. -/


-- @@ L113-118 verbatim
instance Quaternion.instIsScalarTowerSelf : IsScalarTower ℝ ℍ[ℝ] ℍ[ℝ] where
  smul_assoc r x y := by
    ext <;>
      simp only [Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
        Quaternion.imK_smul, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul, smul_eq_mul] <;> ring


-- @@ L120-125 verbatim
instance Quaternion.instSMulCommClassSelf : SMulCommClass ℝ ℍ[ℝ] ℍ[ℝ] where
  smul_comm r x y := by
    ext <;>
      simp only [Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
        Quaternion.imK_smul, Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul,
        Quaternion.imK_mul, smul_eq_mul] <;> ring


-- @@ L127-137 verbatim
/-- The real inner product on `ℍ`. -/
def Quaternion.ipBilin : ℍ[ℝ] →ₗ[ℝ] ℍ[ℝ] →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun x y => x.re * y.re + x.imI * y.imI + x.imJ * y.imJ + x.imK * y.imK)
    (by intro x y z; simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
      Quaternion.imK_add]; ring)
    (by intro c x y; simp only [Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
      Quaternion.imK_smul, smul_eq_mul]; ring)
    (by intro x y z; simp only [Quaternion.re_add, Quaternion.imI_add, Quaternion.imJ_add,
      Quaternion.imK_add]; ring)
    (by intro c x y; simp only [Quaternion.re_smul, Quaternion.imI_smul, Quaternion.imJ_smul,
      Quaternion.imK_smul, smul_eq_mul]; ring)


-- @@ L139-140 verbatim
@[simp] theorem Quaternion.ipBilin_apply (x y : ℍ[ℝ]) :
    Quaternion.ipBilin x y = x.re * y.re + x.imI * y.imI + x.imJ * y.imJ + x.imK * y.imK := rfl


-- @@ L142-145 verbatim
theorem Quaternion.ipBilin_self (x : ℍ[ℝ]) : Quaternion.ipBilin x x = Quaternion.normSq x := by
  rw [Quaternion.normSq_def']
  simp only [Quaternion.ipBilin_apply]
  ring


-- @@ L147-157 verbatim
/-- `ℍ` is a Euclidean composition algebra. The composition law is Euler's four-square
identity, which `Mathlib` supplies as multiplicativity of `Quaternion.normSq`. -/
instance Quaternion.instCompositionAlgebra : CompositionAlgebra ℍ[ℝ] where
  B := Quaternion.ipBilin
  B_symm x y := by simp only [Quaternion.ipBilin_apply]; ring
  B_pos x hx := by
    rw [Quaternion.ipBilin_self]
    exact lt_of_le_of_ne (Quaternion.normSq_nonneg) (Ne.symm ((Quaternion.normSq_ne_zero).mpr hx))
  B_comp x y := by
    rw [Quaternion.ipBilin_self, Quaternion.ipBilin_self, Quaternion.ipBilin_self]
    exact map_mul Quaternion.normSq x y


-- @@ L159-159 verbatim
/-! ## `𝕆` -/


-- @@ L161-161 verbatim
namespace Octonion


-- @@ L163-164 verbatim
/-- The unit of `𝕆`. `Octonions.lean` has only a `def one`. -/
instance instOne : One Octonion := ⟨Octonion.one⟩


-- @@ L166-166 verbatim
theorem one_def : (1 : Octonion) = Octonion.one := rfl


-- @@ L168-176 verbatim
instance instNonAssocRing : NonAssocRing Octonion where
  __ := Octonion.instAddCommGroup
  mul := (· * ·)
  left_distrib := Octonion.mul_add'
  right_distrib := Octonion.add_mul'
  zero_mul := Octonion.zero_mul'
  mul_zero := Octonion.mul_zero'
  one_mul := Octonion.one_mul'
  mul_one := Octonion.mul_one'


-- @@ L178-179 verbatim
instance instIsScalarTower : IsScalarTower ℝ Octonion Octonion where
  smul_assoc r x y := Octonion.smul_mul r x y


-- @@ L181-182 verbatim
instance instSMulCommClass : SMulCommClass ℝ Octonion Octonion where
  smul_comm r x y := (Octonion.mul_smul' r x y).symm


-- @@ L184-188 verbatim
instance instNontrivial : Nontrivial Octonion :=
  ⟨⟨1, 0, by
    intro h
    have := congrArg (fun a => Octonion.coords a 0) h
    simp [one_def, Octonion.one] at this⟩⟩


-- @@ L190-196 verbatim
/-- The Euclidean inner product on `𝕆`, as a bilinear map. -/
def ipBilin : Octonion →ₗ[ℝ] Octonion →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ Octonion.octIp
    (by intro x y z; exact Octonion.octIp_add_left x y z)
    (by intro c x y; simp [Octonion.octIp_smul_left])
    (by intro x y z; exact Octonion.octIp_add_right x y z)
    (by intro c x y; simp [Octonion.octIp_smul_right])


-- @@ L198-198 verbatim
@[simp] theorem ipBilin_apply (x y : Octonion) : ipBilin x y = Octonion.octIp x y := rfl


-- @@ L200-201 verbatim
theorem octIp_self_eq_norm_sq (x : Octonion) : Octonion.octIp x x = Octonion.normSq x := by
  simp only [Octonion.octIp, Octonion.normSq, sq]


-- @@ L203-216 verbatim
/-- `𝕆` is a Euclidean composition algebra. The composition law is Degen's eight-square
identity, supplied by `Octonion.norm_multiplicative` — proved from the Fano multiplication table
with no reference to composition algebras — after `octIp_self_eq_norm_sq` matches the bilinear
form against `normSq`. -/
instance instCompositionAlgebra : CompositionAlgebra Octonion where
  B := ipBilin
  B_symm x y := Octonion.octIp_comm x y
  B_pos x hx := by
    simp only [ipBilin_apply]
    refine lt_of_le_of_ne (Octonion.octIp_self_nonneg x) (fun h => hx ?_)
    exact Octonion.octIp_self_eq_zero h.symm
  B_comp x y := by
    simp only [ipBilin_apply, octIp_self_eq_norm_sq]
    exact Octonion.norm_multiplicative x y


-- @@ L218-218 verbatim
end Octonion


-- @@ L220-222 verbatim
/-! ## The four dimensions

`1, 2, 4, 8`. Hurwitz's theorem is the statement that these are the only ones. -/


-- @@ L224-224 verbatim
theorem Real.finrank_comp : Module.finrank ℝ ℝ = 1 := Module.finrank_self ℝ


-- @@ L226-226 verbatim
theorem Complex.finrank_comp : Module.finrank ℝ ℂ = 2 := Complex.finrank_real_complex


-- @@ L228-228 verbatim
theorem Quaternion.finrank_comp : Module.finrank ℝ ℍ[ℝ] = 4 := Quaternion.finrank_eq_four


-- @@ L230-230 verbatim
theorem Octonion.finrank_comp : Module.finrank ℝ Octonion = 8 := Octonion.finrank_eq_eight
