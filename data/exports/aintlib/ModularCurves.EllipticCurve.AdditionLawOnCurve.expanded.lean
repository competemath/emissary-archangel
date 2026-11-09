/-
Copyright (c) 2026 The AINTLIB Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AINTLIB Authors
-/
import ModularCurves.EllipticCurve.AdditionLawField


-- @@ L8-21 verbatim
/-!
# The second Bosma–Lenstra law lands on the curve over reduced Jacobson rings (T-W7.0c-c5α)

The ring-level on-curve statement for law 2. The polynomial certificate is out of budget
(cofactors ≈ 4–8k terms); instead we evaluate at every maximal ideal — where the residue
field case is `equation_dblAddXYZ` (`AdditionLawField.lean`) — and kill the resulting
radical membership with `eq_zero_of_forall_isMaximal_mem` (`AdditionLaw.lean`), which needs
exactly `IsReduced` and `IsJacobsonRing`.

Consumers (T-W7.0c-c5β / T-W7.0c-i) instantiate `A` at the biprojective chart rings of
`E_U ×_U E_U`: those are finite type over `ℤ` (hence Jacobson, `isJacobsonRing_MvPolynomial_fin`
+ quotient) and domains (0e integrality), with `Δ` a unit by construction, and the chart
points tautologically satisfy the two curve equations. No chart plumbing enters this file.
-/


-- @@ L23-23 verbatim
local notation3 "x" => (0 : Fin 3)


-- @@ L25-25 verbatim
local notation3 "y" => (1 : Fin 3)


-- @@ L27-27 verbatim
local notation3 "z" => (2 : Fin 3)


-- @@ L29-29 verbatim
namespace WeierstrassCurve.Projective


-- @@ L31-31 verbatim
section Map


-- @@ L33-35 verbatim
local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow,
    WeierstrassCurve.map, Function.comp_apply])


-- @@ L37-37 verbatim
variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {W' : Projective R}


-- @@ L39-42 verbatim
lemma map_dblAddX (P Q : Fin 3 → R) :
    (W'.map f).dblAddX (f ∘ P) (f ∘ Q) = f (W'.dblAddX P Q) := by
  simp only [dblAddX]
  map_simp


-- @@ L44-47 verbatim
lemma map_dblAddY (P Q : Fin 3 → R) :
    (W'.map f).dblAddY (f ∘ P) (f ∘ Q) = f (W'.dblAddY P Q) := by
  simp only [dblAddY]
  map_simp


-- @@ L49-52 verbatim
lemma map_dblAddZ (P Q : Fin 3 → R) :
    (W'.map f).dblAddZ (f ∘ P) (f ∘ Q) = f (W'.dblAddZ P Q) := by
  simp only [dblAddZ]
  map_simp


-- @@ L54-63 verbatim
lemma map_dblAddXYZ (P Q : Fin 3 → R) :
    (W'.map f).dblAddXYZ (f ∘ P) (f ∘ Q) = f ∘ W'.dblAddXYZ P Q := by
  funext i
  fin_cases i
  · show (W'.map f).dblAddX (f ∘ P) (f ∘ Q) = f (W'.dblAddX P Q)
    exact map_dblAddX f P Q
  · show (W'.map f).dblAddY (f ∘ P) (f ∘ Q) = f (W'.dblAddY P Q)
    exact map_dblAddY f P Q
  · show (W'.map f).dblAddZ (f ∘ P) (f ∘ Q) = f (W'.dblAddZ P Q)
    exact map_dblAddZ f P Q


-- @@ L65-65 verbatim
end Map


-- @@ L67-67 verbatim
section ZeroArgs


-- @@ L69-69 verbatim
variable {R : Type*} [CommRing R] {W' : Projective R}


-- @@ L71-73 verbatim
lemma dblAddXYZ_zero_fst (Q : Fin 3 → R) : W'.dblAddXYZ 0 Q = 0 := by
  have h := W'.dblAddXYZ_smul_left Q Q 0
  rwa [zero_smul, zero_pow two_ne_zero, zero_smul] at h


-- @@ L75-77 verbatim
lemma dblAddX_smul_right (P Q : Fin 3 → R) (v : R) :
    W'.dblAddX P (v • Q) = v ^ 2 * W'.dblAddX P Q := by
  simpa using W'.dblAddX_smul P Q 1 v


-- @@ L79-81 verbatim
lemma dblAddY_smul_right (P Q : Fin 3 → R) (v : R) :
    W'.dblAddY P (v • Q) = v ^ 2 * W'.dblAddY P Q := by
  simpa using W'.dblAddY_smul P Q 1 v


-- @@ L83-85 verbatim
lemma dblAddZ_smul_right (P Q : Fin 3 → R) (v : R) :
    W'.dblAddZ P (v • Q) = v ^ 2 * W'.dblAddZ P Q := by
  simpa using W'.dblAddZ_smul P Q 1 v


-- @@ L87-91 verbatim
lemma dblAddXYZ_smul_right (P Q : Fin 3 → R) (v : R) :
    W'.dblAddXYZ P (v • Q) = v ^ 2 • W'.dblAddXYZ P Q := by
  funext i
  fin_cases i <;>
    simp [dblAddXYZ, dblAddX_smul_right, dblAddY_smul_right, dblAddZ_smul_right]


-- @@ L93-95 verbatim
lemma dblAddXYZ_zero_snd (P : Fin 3 → R) : W'.dblAddXYZ P 0 = 0 := by
  have h := W'.dblAddXYZ_smul_right P P 0
  rwa [zero_smul, zero_pow two_ne_zero, zero_smul] at h


-- @@ L97-97 verbatim
end ZeroArgs


-- @@ L99-99 verbatim
section Field


-- @@ L101-101 verbatim
variable {F : Type*} [Field F] {W : Projective F}


-- @@ L103-126 expanded
/-- Over a field, every nonzero solution of the homogeneous equation of an *elliptic*
Weierstrass curve is a nonsingular point representative. -/
lemma nonsingular_of_equation_of_ne_zero [W.IsElliptic] {P : Fin 3 → F} (hP : W.Equation P)
    (h0 : P ≠ 0) : W.Nonsingular P :=
  by
  by_cases hz : P (2 : Fin 3) = 0
  · have hx : P (0 : Fin 3) = 0 := X_eq_zero_of_Z_eq_zero hP hz
    have hy : P (1 : Fin 3) ≠ 0 := by
      intro hy
      refine h0 (funext fun j => ?_)
      fin_cases j
      exacts [hx, hy, hz]
    have hPy : P = P (1 : Fin 3) • ![0, 1, 0] :=
      by
      funext j
      fin_cases j
      · show P (0 : Fin 3) = P (1 : Fin 3) * 0
        rw [hx, mul_zero]
      · show P (1 : Fin 3) = P (1 : Fin 3) * 1
        rw [mul_one]
      · show P (2 : Fin 3) = P (1 : Fin 3) * 0
        rw [hz, mul_zero]
    rw [hPy, nonsingular_smul _ (Ne.isUnit hy)]
    exact nonsingular_zero
  · rw [nonsingular_of_Z_ne_zero hz, ← Affine.equation_iff_nonsingular]
    exact (equation_of_Z_ne_zero hz).mp hP


-- @@ L128-139 verbatim
/-- The field case with `Equation` hypotheses (the form evaluation at residue fields
produces): degenerate representatives are absorbed by the zero lemmas. -/
theorem equation_dblAddXYZ_of_equation [W.IsElliptic] {P Q : Fin 3 → F}
    (hP : W.Equation P) (hQ : W.Equation Q) : W.Equation (W.dblAddXYZ P Q) := by
  by_cases h0P : P = 0
  · rw [h0P, dblAddXYZ_zero_fst]
    exact equation_zero_triple
  by_cases h0Q : Q = 0
  · rw [h0Q, dblAddXYZ_zero_snd]
    exact equation_zero_triple
  exact equation_dblAddXYZ (nonsingular_of_equation_of_ne_zero hP h0P)
    (nonsingular_of_equation_of_ne_zero hQ h0Q)


-- @@ L141-141 verbatim
end Field


-- @@ L143-143 verbatim
section Main


-- @@ L145-145 verbatim
variable {A : Type*} [CommRing A] [IsReduced A] [IsJacobsonRing A] {W' : Projective A}


-- @@ L147-162 verbatim
omit [IsReduced A] [IsJacobsonRing A] in
open MvPolynomial in
/-- The field case, packaged along an arbitrary ring homomorphism into a field: the image of
the equation value of `dblAddXYZ` vanishes. Keeping the entire elaboration inside one honest
`[Field K]` world avoids the quotient-ring instance-path collision (whnf blowup) that a
direct residue-field formulation hits. -/
lemma map_polynomial_eval_dblAddXYZ_eq_zero {K : Type*} [CommRing K] (hK : IsField K)
    (φ : A →+* K) {W' : Projective A} (hΔ : IsUnit W'.Δ) {P Q : Fin 3 → A}
    (hP : W'.Equation P) (hQ : W'.Equation Q) :
    φ (eval (W'.dblAddXYZ P Q) W'.polynomial) = 0 := by
  letI := hK.toField
  haveI : (W'.map φ).IsElliptic := ⟨by rw [map_Δ]; exact hΔ.map φ⟩
  have key : (W'.map φ).Equation ((W'.map φ).dblAddXYZ (φ ∘ P) (φ ∘ Q)) :=
    equation_dblAddXYZ_of_equation (hP.map φ) (hQ.map φ)
  rw [map_dblAddXYZ] at key
  rwa [Equation, map_polynomial, eval_map, ← eval₂_comp] at key


-- @@ L164-176 verbatim
open MvPolynomial in
/-- **(T-W7.0c-c5α)** Over a reduced Jacobson ring — in particular over every chart ring of
`E_U ×_U E_U` — the second Bosma–Lenstra addition law lands on the curve. This is the
certificate-free replacement for the 4–8k-term `linear_combination` witness: evaluate at
every maximal ideal (residue fields are fields, where `equation_dblAddXYZ_of_equation`
applies) and conclude by `eq_zero_of_forall_isMaximal_mem`. -/
theorem equation_dblAddXYZ_of_isJacobsonRing (hΔ : IsUnit W'.Δ) {P Q : Fin 3 → A}
    (hP : W'.Equation P) (hQ : W'.Equation Q) : W'.Equation (W'.dblAddXYZ P Q) := by
  rw [Equation]
  refine eq_zero_of_forall_isMaximal_mem fun m hm => ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact map_polynomial_eval_dblAddXYZ_eq_zero
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient m).mp hm) (Ideal.Quotient.mk m) hΔ hP hQ


-- @@ L178-178 verbatim
end Main


-- @@ L180-184 verbatim
/-! ## The law-1 mirror: `addXYZ` lands on the curve over reduced Jacobson rings

Law 1 (mathlib's `addXYZ`) needs the same on-curve statement; its 422/584-term certificate
(`cof_I1_*.txt`) is hereby retired. The diagonal case is even easier than for law 2:
`addXYZ P P = 0` (mathlib's `add*_self`). -/


-- @@ L186-186 verbatim
section AddXYZCommRing


-- @@ L188-188 verbatim
variable {R : Type*} [CommRing R] {W' : Projective R}


-- @@ L190-198 verbatim
lemma addXYZ_self' (P : Fin 3 → R) : W'.addXYZ P P = 0 := by
  funext i
  fin_cases i
  · show W'.addX P P = 0
    exact addX_self P
  · show W'.addY P P = 0
    exact addY_self P
  · show W'.addZ P P = 0
    exact addZ_self P


-- @@ L200-209 verbatim
lemma addXYZ_smul_left (P Q : Fin 3 → R) (u : R) :
    W'.addXYZ (u • P) Q = u ^ 2 • W'.addXYZ P Q := by
  funext i
  fin_cases i
  · show W'.addX (u • P) Q = u ^ 2 * W'.addX P Q
    simpa using W'.addX_smul P Q u 1
  · show W'.addY (u • P) Q = u ^ 2 * W'.addY P Q
    simpa using W'.addY_smul P Q u 1
  · show W'.addZ (u • P) Q = u ^ 2 * W'.addZ P Q
    simpa using W'.addZ_smul P Q u 1


-- @@ L211-220 verbatim
lemma addXYZ_smul_right (P Q : Fin 3 → R) (v : R) :
    W'.addXYZ P (v • Q) = v ^ 2 • W'.addXYZ P Q := by
  funext i
  fin_cases i
  · show W'.addX P (v • Q) = v ^ 2 * W'.addX P Q
    simpa using W'.addX_smul P Q 1 v
  · show W'.addY P (v • Q) = v ^ 2 * W'.addY P Q
    simpa using W'.addY_smul P Q 1 v
  · show W'.addZ P (v • Q) = v ^ 2 * W'.addZ P Q
    simpa using W'.addZ_smul P Q 1 v


-- @@ L222-224 verbatim
lemma addXYZ_zero_fst (Q : Fin 3 → R) : W'.addXYZ 0 Q = 0 := by
  have h := W'.addXYZ_smul_left Q Q 0
  rwa [zero_smul, zero_pow two_ne_zero, zero_smul] at h


-- @@ L226-228 verbatim
lemma addXYZ_zero_snd (P : Fin 3 → R) : W'.addXYZ P 0 = 0 := by
  have h := W'.addXYZ_smul_right P P 0
  rwa [zero_smul, zero_pow two_ne_zero, zero_smul] at h


-- @@ L230-230 verbatim
end AddXYZCommRing


-- @@ L232-232 verbatim
section AddXYZField


-- @@ L234-234 verbatim
variable {F : Type*} [Field F] {W : Projective F}


-- @@ L236-253 verbatim
/-- The field case for law 1, with bare `Equation` hypotheses: the diagonal class collapses
to the zero triple (`addXYZ_self'`), and off it `nonsingular_add` applies. -/
theorem equation_addXYZ_of_equation [W.IsElliptic] {P Q : Fin 3 → F}
    (hP : W.Equation P) (hQ : W.Equation Q) : W.Equation (W.addXYZ P Q) := by
  by_cases h0P : P = 0
  · rw [h0P, addXYZ_zero_fst]
    exact equation_zero_triple
  by_cases h0Q : Q = 0
  · rw [h0Q, addXYZ_zero_snd]
    exact equation_zero_triple
  by_cases hPQ : P ≈ Q
  · rcases hPQ with ⟨u, rfl⟩
    show W.Equation (W.addXYZ ((u : F) • Q) Q)
    rw [addXYZ_smul_left, addXYZ_self', smul_zero]
    exact equation_zero_triple
  · have h := (nonsingular_add (nonsingular_of_equation_of_ne_zero hP h0P)
      (nonsingular_of_equation_of_ne_zero hQ h0Q)).left
    rwa [add_of_not_equiv hPQ] at h


-- @@ L255-255 verbatim
end AddXYZField


-- @@ L257-257 verbatim
section AddXYZMain


-- @@ L259-259 verbatim
variable {A : Type*} [CommRing A] [IsReduced A] [IsJacobsonRing A] {W' : Projective A}


-- @@ L261-274 verbatim
omit [IsReduced A] [IsJacobsonRing A] in
open MvPolynomial in
/-- Law 1's field case along an arbitrary ring homomorphism into a field (same
`IsField`-parametrization as `map_polynomial_eval_dblAddXYZ_eq_zero`). -/
lemma map_polynomial_eval_addXYZ_eq_zero {K : Type*} [CommRing K] (hK : IsField K)
    (φ : A →+* K) {W' : Projective A} (hΔ : IsUnit W'.Δ) {P Q : Fin 3 → A}
    (hP : W'.Equation P) (hQ : W'.Equation Q) :
    φ (eval (W'.addXYZ P Q) W'.polynomial) = 0 := by
  letI := hK.toField
  haveI : (W'.map φ).IsElliptic := ⟨by rw [map_Δ]; exact hΔ.map φ⟩
  have key : (W'.map φ).Equation ((W'.map φ).addXYZ (φ ∘ P) (φ ∘ Q)) :=
    equation_addXYZ_of_equation (hP.map φ) (hQ.map φ)
  rw [map_addXYZ] at key
  rwa [Equation, map_polynomial, eval_map, ← eval₂_comp] at key


-- @@ L276-286 verbatim
open MvPolynomial in
/-- **(T-W7.0c-c5β prerequisite, law-1 mirror of c5α)** Over a reduced Jacobson ring with
`Δ` a unit, mathlib's addition law `addXYZ` lands on the curve. Retires the 422/584-term
`equation_addXYZ` certificate. -/
theorem equation_addXYZ_of_isJacobsonRing (hΔ : IsUnit W'.Δ) {P Q : Fin 3 → A}
    (hP : W'.Equation P) (hQ : W'.Equation Q) : W'.Equation (W'.addXYZ P Q) := by
  rw [Equation]
  refine eq_zero_of_forall_isMaximal_mem fun m hm => ?_
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact map_polynomial_eval_addXYZ_eq_zero
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient m).mp hm) (Ideal.Quotient.mk m) hΔ hP hQ


-- @@ L288-304 verbatim
omit [IsReduced A] [IsJacobsonRing A] in
/-- **(T-W7.0c·c2, field-case non-vanishing along a ring hom)** The `φ`-parametrised form of
`addXYZ_ne_zero_or_dblAddXYZ_ne_zero`: for a ring hom `φ : A → K` into a field with `φ∘P`, `φ∘Q`
nonzero and `Δ` a unit, one of `φ∘(addXYZ P Q)`, `φ∘(dblAddXYZ P Q)` is a nonzero triple. This is
the residue-field layer of the two-law cover; instantiated at each maximal ideal of a chart-product
ring it yields the joint-unit-ideal. Mirrors `map_polynomial_eval_addXYZ_eq_zero`. -/
lemma map_addXYZ_ne_zero_or_map_dblAddXYZ_ne_zero {K : Type*} [CommRing K] (hK : IsField K)
    (φ : A →+* K) (hΔ : IsUnit W'.Δ) {P Q : Fin 3 → A}
    (hP : W'.Equation P) (hQ : W'.Equation Q) (hP0 : φ ∘ P ≠ 0) (hQ0 : φ ∘ Q ≠ 0) :
    φ ∘ W'.addXYZ P Q ≠ 0 ∨ φ ∘ W'.dblAddXYZ P Q ≠ 0 := by
  letI := hK.toField
  haveI : (W'.map φ).IsElliptic := ⟨by rw [map_Δ]; exact hΔ.map φ⟩
  have hns1 := nonsingular_of_equation_of_ne_zero (W := W'.map φ) (hP.map φ) hP0
  have hns2 := nonsingular_of_equation_of_ne_zero (W := W'.map φ) (hQ.map φ) hQ0
  rcases addXYZ_ne_zero_or_dblAddXYZ_ne_zero hns1 hns2 with h | h
  · left; rwa [map_addXYZ] at h
  · right; rwa [map_dblAddXYZ] at h


-- @@ L306-306 verbatim
end AddXYZMain


-- @@ L308-308 verbatim
end WeierstrassCurve.Projective
