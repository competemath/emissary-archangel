/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Data.Matrix.Basic


-- @@ L22-22 verbatim
public section


-- @@ L24-30 verbatim
/-!
# Regular functions between affine spaces

A *regular function* from $k^σ$ to $k^τ$ is a $τ$-indexed family of polynomials in the
variables $σ$, i.e. a vector valued polynomial function. This file provides the basic
API: the Jacobian matrix, composition, the identity, and evaluation at a point.
-/


-- @@ L32-32 verbatim
namespace MvPolynomial


-- @@ L34-34 verbatim
variable {k : Type*} [CommRing k]

-- @@ L35-35 verbatim
variable {σ τ ι : Type*}


-- @@ L37-39 verbatim
variable (k σ τ) in
/-- The type of regular functions from $k^σ$ to $k^τ$. -/
abbrev RegularFunction := τ → MvPolynomial σ k


-- @@ L41-41 verbatim
namespace RegularFunction


-- @@ L43-46 verbatim
/-- The Jacobian of a vector valued polynomial function, viewed as a polynomial. -/
noncomputable def Jacobian (F : RegularFunction k σ τ) :
    Matrix σ τ (MvPolynomial σ k) :=
  Matrix.of fun i j => MvPolynomial.pderiv i (F j)


-- @@ L48-52 verbatim
/-- The composition of two vector valued polynomial functions. -/
noncomputable def comp
    (F : RegularFunction k σ τ) (G : RegularFunction k τ ι) :
    RegularFunction k σ ι :=
  fun (i : ι) ↦ MvPolynomial.bind₁ F (G i)


-- @@ L54-55 verbatim
variable (k σ) in
noncomputable def id : RegularFunction k σ σ := MvPolynomial.X


-- @@ L57-61 verbatim
/-- The evaluation of a regular function `f` over `k` at some point `a`
with coordinates in some algebra over `k`-/
noncomputable def aeval {σ τ : Type*} {S₁ : Type*} [CommSemiring S₁] [Algebra k S₁]
    (F : RegularFunction k σ τ) : (σ → S₁) → τ → S₁ :=
  fun a t ↦ MvPolynomial.aeval a (F t)


-- @@ L63-70 verbatim
/--`aeval` is compatible with composition of regular functions. -/
lemma comp_aeval
    {σ τ ι : Type*}
    (F : RegularFunction k σ τ) (G : RegularFunction k τ ι)
    (a : σ → k) : (F.comp G).aeval a = G.aeval (F.aeval a) := by
  ext i
  rw [aeval, comp, MvPolynomial.aeval_bind₁, ←aeval]
  rfl


-- @@ L72-72 verbatim
end RegularFunction


-- @@ L74-74 verbatim
end MvPolynomial
