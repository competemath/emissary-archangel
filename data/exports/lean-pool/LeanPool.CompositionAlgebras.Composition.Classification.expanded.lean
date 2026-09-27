/-
Copyright (c) 2026 Bryan Ehrlich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Ehrlich
-/
module

public import LeanPool.CompositionAlgebras.Composition.Isomorphisms
public import LeanPool.CompositionAlgebras.Composition.Hurwitz
import Mathlib.Algebra.Order.Algebra
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.EReal.Inv
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.Tactic.Positivity.Finset


-- @@ L19-59 verbatim
/-!
# Hurwitz's theorem, classification form

`Composition/Hurwitz.lean` proves that a finite-dimensional Euclidean composition algebra has
real dimension `1`, `2`, `4` or `8`. This file upgrades that to the classification: such an
algebra is **isomorphic to** `ℝ`, `ℂ`, `ℍ` or `𝕆`.

## The missing piece, and where it goes

The dimension proof runs a chain of composition subalgebras `A₀ ⊆ A₁ ⊆ A₂ ⊆ A₃` inside `C`,
each `Aₖ₊₁ = double Aₖ uₖ₊₁`, and counts. Every object in it is a `Submodule ℝ C`; nothing in
it is a map to a named algebra. What turns the count into an identification is the transport
lemma below: an embedding of `D` onto `Aₖ` and a unit `u ⊥ Aₖ` assemble into an embedding of
the *external* double `CD D` onto `Aₖ₊₁`. Running that alongside the chain, and feeding it the
three base identifications of `Composition/Isomorphisms.lean`, names each `Aₖ`.

## Main definitions

* `CompositionAlgebra.CompEmb D C` — an `ℝ`-linear map `D → C` preserving the unit, the product
  and the norm form. It is automatically injective, and its range is a composition subalgebra.
* `CompEmb.double` — **the transport lemma.** `CompEmb D C` plus a unit normal to its range
  gives `CompEmb (CD D) C`, whose range is `double (range f) u`.

## Main results

* `CompositionAlgebra.hurwitz_classification` — a finite-dimensional Euclidean composition
  algebra is isomorphic, as a composition algebra, to `ℝ`, `ℂ`, `ℍ[ℝ]` or `Octonion`.

★ The isomorphism carried is the *strong* one: `IsCompIso` of `Composition/Isomorphisms.lean`
preserves the unit, the product **and the norm form**.

★ Where the chain stops is not re-derived here. The final branch — that a fourth doubling
cannot happen — is discharged from `finrank_eq_one_or_two_or_four_or_eight` together with
`Octonion.finrank_comp`: the third double already has dimension `8`, and `8` is the largest
value the dimension theorem allows, so it is everything. The `exfalso` branch of the dimension
proof is what makes that true, and it is not repeated.

## Scope

This file carries `hurwitz_classification`, the headline theorem of the development.
-/


-- @@ L61-61 verbatim
@[expose] public section


-- @@ L63-63 verbatim
open scoped Quaternion


-- @@ L65-65 verbatim
namespace CompositionAlgebra


-- @@ L67-67 verbatim
universe u v w


-- @@ L69-69 verbatim
/-! ### Embeddings of composition algebras -/


-- @@ L71-86 verbatim
/-- An **embedding of composition algebras**: an `ℝ`-linear map preserving the unit, the product
and the norm form. Injectivity is not assumed — it follows from `map_nf` and positive
definiteness (`CompEmb.injective`). -/
structure CompEmb (D : Type v) (C : Type u)
    [NonAssocRing D] [Module ℝ D] [IsScalarTower ℝ D D] [SMulCommClass ℝ D D]
    [CompositionAlgebra D]
    [NonAssocRing C] [Module ℝ C] [IsScalarTower ℝ C C] [SMulCommClass ℝ C C]
    [CompositionAlgebra C] where
  /-- The underlying `ℝ`-linear map. -/
  toLinearMap : D →ₗ[ℝ] C
  /-- The unit is preserved. -/
  map_one : toLinearMap 1 = 1
  /-- The product is preserved. -/
  map_mul : ∀ x y : D, toLinearMap (x * y) = toLinearMap x * toLinearMap y
  /-- The norm form is preserved. -/
  map_nf : ∀ x : D, nf (toLinearMap x) = nf x


-- @@ L88-88 verbatim
namespace CompEmb


-- @@ L90-91 verbatim
variable {C : Type u} [NonAssocRing C] [Module ℝ C] [IsScalarTower ℝ C C] [SMulCommClass ℝ C C]
  [CompositionAlgebra C] [Nontrivial C]

-- @@ L92-93 verbatim
variable {D : Type v} [NonAssocRing D] [Module ℝ D] [IsScalarTower ℝ D D] [SMulCommClass ℝ D D]
  [CompositionAlgebra D]


-- @@ L95-102 verbatim
omit [Nontrivial C] in
/-- An embedding preserves the form. This is the polarisation of `map_nf`, and it is what makes
the conjugation transport. -/
theorem map_ip (f : CompEmb D C) (x y : D) :
    ip (f.toLinearMap x) (f.toLinearMap y) = ip x y := by
  have h := f.map_nf (x + y)
  rw [map_add, nf_add, nf_add, f.map_nf, f.map_nf] at h
  linarith


-- @@ L104-113 verbatim
omit [Nontrivial C] in
/-- An embedding is injective: it preserves the norm form, which is positive definite. -/
theorem injective (f : CompEmb D C) : Function.Injective f.toLinearMap := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h := f.map_nf x
  rw [hx] at h
  refine nf_eq_zero_iff.mp ?_
  rw [← h, nf_eq_ip]
  simp


-- @@ L115-121 verbatim
omit [Nontrivial C] in
/-- An embedding preserves the conjugation. Both sides are `(2⟪x,1⟫) • 1 - f x`. -/
theorem map_cstar (f : CompEmb D C) (x : D) :
    f.toLinearMap (cstar x) = cstar (f.toLinearMap x) := by
  have h1 : ip (f.toLinearMap x) (1 : C) = ip x 1 := by
    rw [← f.map_one, f.map_ip]
  rw [cstar_apply, cstar_apply, map_sub, map_smul, f.map_one, h1]


-- @@ L123-133 verbatim
omit [Nontrivial C] in
/-- The range of an embedding is a composition subalgebra. -/
theorem range_isCompSubalgebra (f : CompEmb D C) :
    IsCompSubalgebra (LinearMap.range f.toLinearMap) where
  one_mem := ⟨1, f.map_one⟩
  mul_mem := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact ⟨x * y, f.map_mul x y⟩
  cstar_mem := by
    rintro _ ⟨x, rfl⟩
    exact ⟨cstar x, f.map_cstar x⟩


-- @@ L135-139 verbatim
omit [Nontrivial C] in
/-- The range of an embedding has the dimension of its source. -/
theorem finrank_range (f : CompEmb D C) :
    Module.finrank ℝ (LinearMap.range f.toLinearMap) = Module.finrank ℝ D :=
  LinearMap.finrank_range_of_inj f.injective


-- @@ L141-141 verbatim
/-! ### Precomposition with an isomorphism -/


-- @@ L143-144 verbatim
variable {E : Type w} [NonAssocRing E] [Module ℝ E] [IsScalarTower ℝ E E] [SMulCommClass ℝ E E]
  [CompositionAlgebra E]


-- @@ L146-157 verbatim
/-- Rename the source of an embedding along an isomorphism of composition algebras. -/
def congr (e : E ≃ₗ[ℝ] D) (he : IsCompIso e) (f : CompEmb D C) : CompEmb E C where
  toLinearMap := f.toLinearMap ∘ₗ (e : E →ₗ[ℝ] D)
  map_one := by
    change f.toLinearMap (e 1) = 1
    rw [he.map_one, f.map_one]
  map_mul x y := by
    change f.toLinearMap (e (x * y)) = f.toLinearMap (e x) * f.toLinearMap (e y)
    rw [he.map_mul, f.map_mul]
  map_nf x := by
    change nf (f.toLinearMap (e x)) = nf x
    rw [f.map_nf, he.map_nf]


-- @@ L159-161 verbatim
omit [Nontrivial C] in
@[simp] theorem congr_apply (e : E ≃ₗ[ℝ] D) (he : IsCompIso e) (f : CompEmb D C) (x : E) :
    (f.congr e he).toLinearMap x = f.toLinearMap (e x) := rfl


-- @@ L163-172 verbatim
omit [Nontrivial C] in
/-- Renaming the source does not move the range. -/
theorem range_congr (e : E ≃ₗ[ℝ] D) (he : IsCompIso e) (f : CompEmb D C) :
    LinearMap.range (f.congr e he).toLinearMap = LinearMap.range f.toLinearMap := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨e y, rfl⟩
  · rintro ⟨y, rfl⟩
    exact ⟨e.symm y, by simp⟩


-- @@ L174-174 verbatim
/-! ### From a surjective embedding to an isomorphism -/


-- @@ L176-179 verbatim
/-- An embedding whose range is everything is an isomorphism `D ≃ C`. -/
noncomputable def toEquiv (f : CompEmb D C) (h : LinearMap.range f.toLinearMap = ⊤) :
    D ≃ₗ[ℝ] C :=
  LinearEquiv.ofBijective f.toLinearMap ⟨f.injective, LinearMap.range_eq_top.mp h⟩


-- @@ L181-183 verbatim
omit [Nontrivial C] in
@[simp] theorem toEquiv_apply (f : CompEmb D C) (h : LinearMap.range f.toLinearMap = ⊤) (x : D) :
    f.toEquiv h x = f.toLinearMap x := rfl


-- @@ L185-190 verbatim
omit [Nontrivial C] in
theorem toEquiv_isCompIso (f : CompEmb D C) (h : LinearMap.range f.toLinearMap = ⊤) :
    IsCompIso (f.toEquiv h) where
  map_one := f.map_one
  map_mul := f.map_mul
  map_nf := f.map_nf


-- @@ L192-192 verbatim
end CompEmb


-- @@ L194-194 verbatim
/-! ### Inverting an isomorphism -/


-- @@ L196-197 verbatim
variable {C : Type u} [NonAssocRing C] [Module ℝ C] [IsScalarTower ℝ C C] [SMulCommClass ℝ C C]
  [CompositionAlgebra C]

-- @@ L198-199 verbatim
variable {D : Type v} [NonAssocRing D] [Module ℝ D] [IsScalarTower ℝ D D] [SMulCommClass ℝ D D]
  [CompositionAlgebra D]


-- @@ L201-210 verbatim
/-- The inverse of an isomorphism of composition algebras is one. -/
theorem IsCompIso.symm {e : C ≃ₗ[ℝ] D} (h : IsCompIso e) : IsCompIso e.symm where
  map_one := by
    apply e.injective
    rw [e.apply_symm_apply, h.map_one]
  map_mul x y := by
    apply e.injective
    rw [e.apply_symm_apply, h.map_mul, e.apply_symm_apply, e.apply_symm_apply]
  map_nf x := by
    rw [← h.map_nf (e.symm x), e.apply_symm_apply]


-- @@ L212-212 verbatim
end CompositionAlgebra


-- @@ L214-214 verbatim
/-! ### The transport lemma -/


-- @@ L216-216 verbatim
namespace CompositionAlgebra


-- @@ L218-218 verbatim
namespace CompEmb


-- @@ L220-220 verbatim
universe u v


-- @@ L222-223 verbatim
variable {C : Type u} [NonAssocRing C] [Module ℝ C] [IsScalarTower ℝ C C] [SMulCommClass ℝ C C]
  [CompositionAlgebra C] [Nontrivial C]

-- @@ L224-225 verbatim
variable {D : Type v} [Ring D] [Module ℝ D] [IsScalarTower ℝ D D] [SMulCommClass ℝ D D]
  [CompositionAlgebra D] [Nontrivial D]


-- @@ L227-237 verbatim
/-- The product of two elements of `A ⊕ A u`, in Cayley–Dickson form. This is the computation
inside `IsCompSubalgebra.isCompSubalgebra_double`, pulled out because the transport lemma needs
it as an equation rather than as a closure statement. -/
theorem _root_.CompositionAlgebra.IsCompSubalgebra.mul_add_mul_unit
    {A : Submodule ℝ C} (hA : IsCompSubalgebra A) {u : C}
    (hu : ∀ a ∈ A, ip u a = 0) (hnu : nf u = 1)
    {a : C} (ha : a ∈ A) {b : C} (hb : b ∈ A) {c : C} (hc : c ∈ A) {d : C} (hd : d ∈ A) :
    (a + b * u) * (c + d * u) = (a * c - cstar d * b) + (d * a + b * cstar c) * u := by
  rw [mul_add, add_mul, add_mul, hA.mul_mul_unit hu ha hd, hA.unit_mul_mul hu b hc,
    hA.unit_mul_unit hu hnu hb hd, add_mul]
  abel


-- @@ L239-240 verbatim
variable (f : CompEmb D C) {u : C}
  (hu : ∀ a ∈ LinearMap.range f.toLinearMap, ip u a = 0) (hnu : nf u = 1)


-- @@ L242-252 verbatim
/-- The underlying map of the transport lemma: `(a, b) ↦ f a + (f b) u`. -/
def doubleMap : CD D →ₗ[ℝ] C where
  toFun x := f.toLinearMap x.fst + (f.toLinearMap x.snd) * u
  map_add' x y := by
    change f.toLinearMap (x.fst + y.fst) + (f.toLinearMap (x.snd + y.snd)) * u = _
    rw [map_add, map_add, add_mul]
    abel
  map_smul' r x := by
    change f.toLinearMap (r • x.fst) + (f.toLinearMap (r • x.snd)) * u = _
    rw [map_smul, map_smul, smul_mul_assoc]
    simp [smul_add]


-- @@ L254-256 verbatim
omit [Nontrivial C] in
@[simp] theorem doubleMap_apply (x : CD D) :
    f.doubleMap (u := u) x = f.toLinearMap x.fst + (f.toLinearMap x.snd) * u := rfl


-- @@ L258-258 verbatim
include hu hnu


-- @@ L260-281 verbatim
/-- **The transport lemma.** An embedding of `D` into `C` and a unit vector orthogonal to its
range assemble into an embedding of the external Cayley–Dickson double `CD D`.

Multiplicativity is exactly the three Cayley–Dickson rules of `Composition/Doubling.lean`;
norm preservation is `IsCompSubalgebra.nf_add_mul_unit`. -/
def double : CompEmb (CD D) C where
  toLinearMap := f.doubleMap (u := u)
  map_one := by
    change f.toLinearMap (1 : CD D).fst + (f.toLinearMap (1 : CD D).snd) * u = 1
    rw [CD.fst_one, CD.snd_one, f.map_one, map_zero, zero_mul, add_zero]
  map_mul x y := by
    have hA := f.range_isCompSubalgebra
    change f.toLinearMap (x * y).fst + (f.toLinearMap (x * y).snd) * u
        = (f.toLinearMap x.fst + (f.toLinearMap x.snd) * u) *
          (f.toLinearMap y.fst + (f.toLinearMap y.snd) * u)
    rw [hA.mul_add_mul_unit hu hnu ⟨x.fst, rfl⟩ ⟨x.snd, rfl⟩ ⟨y.fst, rfl⟩ ⟨y.snd, rfl⟩,
      CD.fst_mul, CD.snd_mul, map_sub, map_add, f.map_mul, f.map_mul, f.map_mul, f.map_mul,
      f.map_cstar, f.map_cstar]
  map_nf x := by
    have hA := f.range_isCompSubalgebra
    change nf (f.toLinearMap x.fst + (f.toLinearMap x.snd) * u) = _
    rw [hA.nf_add_mul_unit hu hnu ⟨x.fst, rfl⟩ ⟨x.snd, rfl⟩, f.map_nf, f.map_nf, CD.nf_eq]


-- @@ L283-284 verbatim
@[simp] theorem double_apply (x : CD D) :
    (f.double hu hnu).toLinearMap x = f.toLinearMap x.fst + (f.toLinearMap x.snd) * u := rfl


-- @@ L286-296 verbatim
/-- The transported embedding lands exactly on the internal double of the range. -/
theorem range_double :
    LinearMap.range (f.double hu hnu).toLinearMap
      = _root_.CompositionAlgebra.double (LinearMap.range f.toLinearMap) u := by
  ext x
  rw [mem_double_iff]
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨f.toLinearMap y.fst, ⟨y.fst, rfl⟩, f.toLinearMap y.snd, ⟨y.snd, rfl⟩, rfl⟩
  · rintro ⟨a, ⟨p, rfl⟩, b, ⟨q, rfl⟩, rfl⟩
    exact ⟨CD.mk p q, rfl⟩


-- @@ L298-298 verbatim
end CompEmb


-- @@ L300-300 verbatim
/-! ### The base of the chain -/


-- @@ L302-303 verbatim
variable {C : Type u} [NonAssocRing C] [Module ℝ C] [IsScalarTower ℝ C C] [SMulCommClass ℝ C C]
  [CompositionAlgebra C] [Nontrivial C]


-- @@ L305-315 verbatim
/-- `ℝ` embeds as the line through the unit. -/
def realCompEmb : CompEmb ℝ C where
  toLinearMap := LinearMap.toSpanSingleton ℝ C 1
  map_one := by simp [LinearMap.toSpanSingleton]
  map_mul x y := by
    change (x * y) • (1 : C) = (x • (1 : C)) * (y • (1 : C))
    rw [smul_mul_assoc, mul_smul_comm, one_mul, smul_smul]
  map_nf x := by
    change nf (x • (1 : C)) = nf x
    rw [nf_smul, nf_one, Real.nf_eq]
    ring


-- @@ L317-318 verbatim
@[simp] theorem realCompEmb_apply (x : ℝ) :
    (realCompEmb (C := C)).toLinearMap x = x • (1 : C) := rfl


-- @@ L320-324 verbatim
/-- The range of the base embedding is the line through the unit, the `A₀` of the dimension
proof. -/
theorem range_realCompEmb :
    LinearMap.range (realCompEmb (C := C)).toLinearMap = Submodule.span ℝ {(1 : C)} :=
  (LinearMap.span_singleton_eq_range ℝ C 1).symm


-- @@ L326-326 verbatim
/-! ### Hurwitz's theorem, classification form -/


-- @@ L328-328 verbatim
variable [FiniteDimensional ℝ C]


-- @@ L330-373 verbatim
/-- **Hurwitz's theorem (classification form).** A finite-dimensional Euclidean composition
algebra is isomorphic, as a composition algebra, to `ℝ`, `ℂ`, `ℍ` or `𝕆`.

The isomorphism preserves the unit, the product and the norm form (`IsCompIso`).

The proof runs the doubling chain of `finrank_eq_one_or_two_or_four_or_eight` with an embedding
carried alongside it: `realCompEmb` starts at `A₀`, `CompEmb.double` steps it along each
`Aₖ ↦ double Aₖ uₖ₊₁`, and the three base identifications of `Composition/Isomorphisms.lean`
rename the source at each step, `CD ℝ ↦ ℂ`, `CD ℂ ↦ ℍ`, `CD ℍ ↦ 𝕆`. Each branch of the chain
ends when the range is everything; the last branch cannot fail to, because its range already
has dimension `8`. -/
theorem hurwitz_classification :
    (∃ f : C ≃ₗ[ℝ] ℝ, IsCompIso f) ∨ (∃ f : C ≃ₗ[ℝ] ℂ, IsCompIso f) ∨
      (∃ f : C ≃ₗ[ℝ] ℍ[ℝ], IsCompIso f) ∨ (∃ f : C ≃ₗ[ℝ] Octonion, IsCompIso f) := by
  -- `A₀ = ℝ ∙ 1`, named by `realCompEmb`.
  let f0 : CompEmb ℝ C := realCompEmb
  by_cases h0 : LinearMap.range f0.toLinearMap = ⊤
  · exact Or.inl ⟨(f0.toEquiv h0).symm, (f0.toEquiv_isCompIso h0).symm⟩
  obtain ⟨u1, hu1, hnu1⟩ := exists_unit_orthogonal h0
  -- `A₁ = double A₀ u₁`, named by `CD ℝ ≃ ℂ`.
  let f1 : CompEmb ℂ C :=
    (f0.double hu1 hnu1).congr cdRealEquiv.symm cdRealEquiv_isCompIso.symm
  by_cases h1 : LinearMap.range f1.toLinearMap = ⊤
  · exact Or.inr (Or.inl ⟨(f1.toEquiv h1).symm, (f1.toEquiv_isCompIso h1).symm⟩)
  obtain ⟨u2, hu2, hnu2⟩ := exists_unit_orthogonal h1
  -- `A₂ = double A₁ u₂`, named by `CD ℂ ≃ ℍ`.
  let f2 : CompEmb ℍ[ℝ] C :=
    (f1.double hu2 hnu2).congr cdComplexEquiv.symm cdComplexEquiv_isCompIso.symm
  by_cases h2 : LinearMap.range f2.toLinearMap = ⊤
  · exact Or.inr (Or.inr (Or.inl ⟨(f2.toEquiv h2).symm, (f2.toEquiv_isCompIso h2).symm⟩))
  obtain ⟨u3, hu3, hnu3⟩ := exists_unit_orthogonal h2
  -- `A₃ = double A₂ u₃`, named by `CD ℍ ≃ 𝕆`.  This one cannot be proper.
  let f3 : CompEmb Octonion C :=
    (f2.double hu3 hnu3).congr cdQuaternionEquiv.symm cdQuaternionEquiv_isCompIso.symm
  have h3 : LinearMap.range f3.toLinearMap = ⊤ := by
    have hdim : Module.finrank ℝ (LinearMap.range f3.toLinearMap) = 8 := by
      rw [CompEmb.finrank_range, Octonion.finrank_comp]
    have hle : 8 ≤ Module.finrank ℝ C := by
      rw [← hdim]
      exact Submodule.finrank_le _
    have hC : Module.finrank ℝ C = 8 := by
      rcases finrank_eq_one_or_two_or_four_or_eight (C := C) with h | h | h | h <;> omega
    exact Submodule.eq_top_of_finrank_eq (by rw [hdim, hC])
  exact Or.inr (Or.inr (Or.inr ⟨(f3.toEquiv h3).symm, (f3.toEquiv_isCompIso h3).symm⟩))


-- @@ L375-375 verbatim
end CompositionAlgebra
