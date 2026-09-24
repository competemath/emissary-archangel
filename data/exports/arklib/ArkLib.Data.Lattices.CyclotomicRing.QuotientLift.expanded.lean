/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
module

public import ArkLib.Data.Lattices.CyclotomicRing.Rq
public import ArkLib.Data.Lattices.Vectors


-- @@ L11-39 verbatim
/-!
  # Quotient-presentation laws for `Rq Φ` — the cyclotomic HMZ25 lift instance

  The Huang–Mao–Zhang ring-switching lift ([HMZ25]; Hachi [NOZ26] §4.3, Figure 4 / Lemma 9)
  is formalized generically over a *quotient presentation* `S ≅ R[X]/(φ)` in
  `ArkLib/ProofSystem/RingSwitching/Lift/` — the lifted rows, the quotient-witness
  correspondence, and the `2d`-point interpolation engine all live there, stated over any
  monic modulus.

  This file supplies the **law-discharge lemmas for the cyclotomic instance** `S := Rq Φ`
  with canonical representatives `rep := (·.1.toPoly)` and modulus `Φ.φ.toPoly` (the instance
  itself, `cyclotomicPresentation`, is assembled protocol-side in
  `Commitments/Functional/Hachi/RingSwitch/Reduction.lean`, since `Data` does not import
  `ProofSystem`):

  * `val_toPoly_injective` — representatives are injective;
  * `modulus_dvd_toPoly_add_sub` / `modulus_dvd_toPoly_mul_sub` — the coset laws: reduction
    changes the representative of a sum/product by a multiple of the modulus, via the
    semantic quotient bridge `quotientHom`.

  The remaining presentation law — representatives are degree-reduced — is
  `Rq.natDegree_val_toPoly_lt'` in `Rq.lean`, next to the other `Rq` degree lemmas.

  ## References

  * [Huang, M.-Y. M., Mao, X., and Zhang, J., *Sublinear Proofs over Polynomial Rings*][HMZ25]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/


-- @@ L41-41 verbatim
@[expose] public section


-- @@ L43-43 verbatim
open Polynomial CompPoly CompPoly.CPolynomial


-- @@ L45-45 verbatim
namespace ArkLib.Lattices.CyclotomicModulus


-- @@ L47-47 verbatim
variable {R : Type*} [Field R]


-- @@ L49-49 verbatim
variable [BEq R] [LawfulBEq R] (Φ : CyclotomicModulus R) [IsCyclotomic Φ]


-- @@ L51-51 verbatim
/-! ## Injectivity of canonical representatives -/


-- @@ L53-58 verbatim
omit [IsCyclotomic Φ] in
/-- Canonical representatives are injective: `Rq` elements with equal representative
polynomials are equal. -/
theorem val_toPoly_injective : Function.Injective (fun a : Rq Φ => a.1.toPoly) := by
  intro a b h
  exact Subtype.ext (toPoly_injective h)


-- @@ L60-66 verbatim
/-! ## Coset laws of the canonical representatives

Ring operations on `Rq Φ` reduce their result, so the representative of a sum/product differs
from the sum/product of representatives by a multiple of the modulus — exactly the
`IsPresentation` coset laws of the generic quotient-evaluation switch. Both proofs route
through the semantic quotient bridge: `quotientHom` identifies a polynomial with its
reduction. -/


-- @@ L68-74 verbatim
/-- Coset law for addition. -/
theorem modulus_dvd_toPoly_add_sub (a b : Rq Φ) :
    Φ.φ.toPoly ∣ (a + b).1.toPoly - (a.1.toPoly + b.1.toPoly) := by
  have h : Φ.quotientHom ((a + b).1) = Φ.quotientHom (a.1 + b.1) := by
    rw [show (a + b).1 = Φ.reduce (a.1 + b.1) from rfl, quotientHom_reduce]
  rw [quotientHom_apply, quotientHom_apply, toPoly_add] at h
  rwa [Ideal.Quotient.eq, modIdeal, Ideal.mem_span_singleton] at h


-- @@ L76-82 verbatim
/-- Coset law for multiplication. -/
theorem modulus_dvd_toPoly_mul_sub (a b : Rq Φ) :
    Φ.φ.toPoly ∣ (a * b).1.toPoly - a.1.toPoly * b.1.toPoly := by
  have h : Φ.quotientHom ((a * b).1) = Φ.quotientHom (a.1 * b.1) := by
    rw [show (a * b).1 = Φ.reduce (a.1 * b.1) from rfl, quotientHom_reduce]
  rw [quotientHom_apply, quotientHom_apply, toPoly_mul] at h
  rwa [Ideal.Quotient.eq, modIdeal, Ideal.mem_span_singleton] at h


-- @@ L84-84 verbatim
end ArkLib.Lattices.CyclotomicModulus
