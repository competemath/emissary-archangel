/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.RingTheory.Bialgebra.TensorProduct
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import TauCeti.Algebra.Lie.UniversalEnveloping.Antipode
public import TauCeti.Algebra.Lie.UniversalEnveloping.Bialgebra
import TauCeti.Algebra.Lie.UniversalEnveloping.Basic


-- @@ L14-42 verbatim
/-!
# The Hopf algebra structure on a universal enveloping algebra

The standard bialgebra structure on a universal enveloping algebra is a Hopf algebra. Its
antipode reverses products and negates the canonical Lie generators. This file joins the
independently useful bialgebra and antipode constructions: the antipode is a two-sided
convolution inverse of the identity.

The Hopf instance uses Mathlib's `HopfAlgebra.ofConvInverse`; multiplication of coalgebra
representations is handled by Mathlib's `Coalgebra.Repr.mul`.

## Main declarations

* `TauCeti.UniversalEnvelopingAlgebra.instHopfAlgebra`: the canonical Hopf algebra structure.
* `TauCeti.UniversalEnvelopingAlgebra.hopfAlgebraStructAntipode_eq_antipode`: the Hopf
  antipode is the previously constructed universal-enveloping antipode.

## Roadmap

This is a prerequisite for the Chevalley--Demazure construction in Layer 9 of the
ReductiveGroups roadmap. The Kostant integral form must be stable under comultiplication, counit,
and antipode before it can supply the integral Hopf data used in that construction; the ambient
Hopf structure is what those operations restrict from.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §26.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/


-- @@ L44-44 verbatim
public section


-- @@ L46-46 verbatim
open Coalgebra HopfAlgebra WithConv

-- @@ L47-47 verbatim
open scoped RingTheory.LinearMap TensorProduct


-- @@ L49-49 verbatim
namespace TauCeti.UniversalEnvelopingAlgebra


-- @@ L51-51 verbatim
universe u v


-- @@ L53-53 verbatim
variable (R : Type u) [CommRing R]

-- @@ L54-54 verbatim
variable (L : Type v) [LieRing L] [LieAlgebra R L]


-- @@ L56-56 verbatim
local notation "U" => _root_.UniversalEnvelopingAlgebra R L

-- @@ L57-57 verbatim
local notation "convAntipode" => (toConv (antipode R) : WithConv (U →ₗ[R] U))

-- @@ L58-58 verbatim
local notation "convId" => (toConv LinearMap.id : WithConv (U →ₗ[R] U))


-- @@ L60-71 verbatim
/-- The sum manipulation common to the two convolution computations below: an inner sum that
collapses to a scalar multiple of `1` factors out of the surrounding products. -/
private theorem sum_sum_mul_mul_eq_smul_sum {ια ιβ : Type*} (s : Finset ια) (t : Finset ιβ)
    (F G : ια → U) (P Q : ιβ → U) (r : R)
    (h : ∑ i ∈ s, F i * G i = r • (1 : U)) :
    ∑ j ∈ t, ∑ i ∈ s, P j * F i * (G i * Q j) = r • ∑ j ∈ t, P j * Q j := by
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hterm (i : ια) : P j * F i * (G i * Q j) = P j * (F i * G i) * Q j := by
    simp only [mul_assoc]
  simp_rw [hterm]
  rw [← Finset.sum_mul, ← Finset.mul_sum, h, mul_smul_comm, mul_one, smul_mul_assoc]


-- @@ L73-94 verbatim
private theorem antipodeConv_mul_idConv_mul_apply (a b : U)
    (ha : (convAntipode * convId) a =
      (Coalgebra.counit (R := R) a) • (1 : U)) :
    (convAntipode * convId) (a * b) =
      (Coalgebra.counit (R := R) a) •
        (convAntipode * convId) b := by
  let ra := Coalgebra.Repr.arbitrary R a
  let rb := Coalgebra.Repr.arbitrary R b
  have hra : ∑ i ∈ ra.index, antipode R (ra.left i) * ra.right i =
      (Coalgebra.counit (R := R) a) • (1 : U) := by
    rw [← ha]
    simpa using
      (ra.convMul_apply (toConv (antipode R)) (toConv LinearMap.id)).symm
  rw [Coalgebra.Repr.convMul_apply (ra.mul rb)
    convAntipode convId, rb.convMul_apply convAntipode convId]
  simp only [Coalgebra.Repr.mul_index, Coalgebra.Repr.mul_left,
    Coalgebra.Repr.mul_right,
    UniversalEnvelopingAlgebra.antipode_mul_antidistrib, LinearMap.id_apply,
    Finset.sum_product]
  rw [Finset.sum_comm]
  exact sum_sum_mul_mul_eq_smul_sum R L ra.index rb.index
    (fun i => antipode R (ra.left i)) ra.right (fun j => antipode R (rb.left j)) rb.right _ hra


-- @@ L96-117 verbatim
private theorem idConv_mul_antipodeConv_mul_apply (a b : U)
    (hb : (convId * convAntipode) b =
      (Coalgebra.counit (R := R) b) • (1 : U)) :
    (convId * convAntipode) (a * b) =
      (Coalgebra.counit (R := R) b) •
        (convId * convAntipode) a := by
  let ra := Coalgebra.Repr.arbitrary R a
  let rb := Coalgebra.Repr.arbitrary R b
  have hrb : ∑ j ∈ rb.index, rb.left j * antipode R (rb.right j) =
      (Coalgebra.counit (R := R) b) • (1 : U) := by
    rw [← hb]
    simpa using
      (rb.convMul_apply (toConv LinearMap.id) (toConv (antipode R))).symm
  rw [Coalgebra.Repr.convMul_apply (ra.mul rb)
    convId convAntipode, ra.convMul_apply convId convAntipode]
  simp only [Coalgebra.Repr.mul_index, Coalgebra.Repr.mul_left,
    Coalgebra.Repr.mul_right,
    UniversalEnvelopingAlgebra.antipode_mul_antidistrib, LinearMap.id_apply,
    Finset.sum_product]
  exact sum_sum_mul_mul_eq_smul_sum R L rb.index ra.index
    rb.left (fun j => antipode R (rb.right j)) ra.left
    (fun i => antipode R (ra.right i)) _ hrb


-- @@ L119-135 verbatim
/-- A linear endomorphism that agrees with `a ↦ ε a • 1` on scalars and on the canonical Lie
generators, and whose agreement set is closed under multiplication, agrees with it everywhere:
the elements where it agrees form a subalgebra, and the generators generate. -/
private theorem eq_counit_smul_one_of_ι (f : U →ₗ[R] U)
    (hmul : ∀ a b : U, f a = (Coalgebra.counit (R := R) a) • (1 : U) →
      f b = (Coalgebra.counit (R := R) b) • (1 : U) →
      f (a * b) = (Coalgebra.counit (R := R) (a * b)) • (1 : U))
    (halg : ∀ r : R, f (algebraMap R U r) =
      (Coalgebra.counit (R := R) (algebraMap R U r)) • (1 : U))
    (hι : ∀ x : L, f (_root_.UniversalEnvelopingAlgebra.ι R x) =
      (Coalgebra.counit (R := R) (_root_.UniversalEnvelopingAlgebra.ι R x)) • (1 : U))
    (a : U) : f a = (Coalgebra.counit (R := R) a) • (1 : U) := by
  induction a using induction_ι with
  | ι x => exact hι x
  | algebraMap r => exact halg r
  | add x y hx hy => simp only [map_add, hx, hy, add_smul]
  | mul x y hx hy => exact hmul x y hx hy


-- @@ L137-145 verbatim
private theorem antipodeConv_mul_idConv_apply (a : U) :
    (convAntipode * convId) a =
      (Coalgebra.counit (R := R) a) • (1 : U) :=
  eq_counit_smul_one_of_ι R L (convAntipode * convId).ofConv
    (fun a b ha hb => by
      rw [antipodeConv_mul_idConv_mul_apply R L a b ha, hb, Bialgebra.counit_mul]
      simp [smul_smul])
    (fun r => by simp [LinearMap.convMul_apply, Algebra.smul_def])
    (fun x => by simp [LinearMap.convMul_apply]) a


-- @@ L147-155 verbatim
private theorem idConv_mul_antipodeConv_apply (a : U) :
    (convId * convAntipode) a =
      (Coalgebra.counit (R := R) a) • (1 : U) :=
  eq_counit_smul_one_of_ι R L (convId * convAntipode).ofConv
    (fun a b ha hb => by
      rw [idConv_mul_antipodeConv_mul_apply R L a b hb, ha, Bialgebra.counit_mul]
      simp [smul_smul, mul_comm])
    (fun r => by simp [LinearMap.convMul_apply, Algebra.smul_def])
    (fun x => by simp [LinearMap.convMul_apply]) a


-- @@ L157-175 verbatim
/-- A universal enveloping algebra with its standard bialgebra structure is a Hopf algebra.

The antipode is `TauCeti.UniversalEnvelopingAlgebra.antipode`, the linear endomorphism underlying
the anti-automorphism `antipodeEquiv`: it reverses products and negates every canonical Lie
generator. -/
noncomputable instance instHopfAlgebra : HopfAlgebra R U :=
  HopfAlgebra.ofConvInverse (antipode R)
    (by
      apply WithConv.ext
      apply LinearMap.ext
      intro a
      simpa [Algebra.smul_def] using
        antipodeConv_mul_idConv_apply R L a)
    (by
      apply WithConv.ext
      apply LinearMap.ext
      intro a
      simpa [Algebra.smul_def] using
        idConv_mul_antipodeConv_apply R L a)


-- @@ L177-181 verbatim
/-- The antipode supplied by the Hopf algebra instance is the canonical universal-enveloping
antipode constructed independently of the bialgebra structure. -/
theorem hopfAlgebraStructAntipode_eq_antipode :
    HopfAlgebraStruct.antipode R (A := U) =
      UniversalEnvelopingAlgebra.antipode R := rfl


-- @@ L183-183 verbatim
end TauCeti.UniversalEnvelopingAlgebra
