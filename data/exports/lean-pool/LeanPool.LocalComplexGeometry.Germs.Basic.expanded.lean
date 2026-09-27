/-
Copyright (c) 2026 BochaoKong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BochaoKong
-/
module

public import Mathlib.Topology.Germ
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.Analysis.Analytic.Constructions
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Tactic.Positivity.Finset


-- @@ L16-23 verbatim
/-!
# Holomorphic function germs at the origin

This file defines the local analytic ring as the subring of Mathlib's
neighbourhood-function germs which have an analytic representative.  It uses
the same `Filter.Germ` model and `AnalyticAt` predicate as the pinned WPT
project.
-/


-- @@ L25-25 verbatim
@[expose] public section


-- @@ L27-27 verbatim
open Filter

-- @@ L28-28 verbatim
open scoped Topology



-- @@ L31-31 verbatim
namespace LocalComplexGeometry


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-36 verbatim
/-- The complex vector space `ℂⁿ`. -/
abbrev ComplexEuclidean (n : ℕ) := Fin n → ℂ


-- @@ L38-40 verbatim
/-- The ambient ring of all function germs at the origin of `ℂⁿ`. -/
abbrev FunctionGerm (n : ℕ) :=
  Filter.Germ (𝓝 (0 : ComplexEuclidean n)) ℂ


-- @@ L42-56 verbatim
/-- Function germs which have a representative analytic at the origin. -/
def holomorphicGermSubring (n : ℕ) : Subring (FunctionGerm n) where
  carrier := {φ | ∃ f : ComplexEuclidean n → ℂ,
    AnalyticAt ℂ f 0 ∧ (f : FunctionGerm n) = φ}
  zero_mem' := ⟨0, analyticAt_const, rfl⟩
  one_mem' := ⟨1, analyticAt_const, rfl⟩
  add_mem' := by
    rintro φ ψ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, by simp⟩
  mul_mem' := by
    rintro φ ψ ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f * g, hf.mul hg, by simp⟩
  neg_mem' := by
    rintro φ ⟨f, hf, rfl⟩
    exact ⟨-f, hf.neg, by simp⟩


-- @@ L58-59 verbatim
/-- The commutative ring `𝒪_{ℂⁿ,0}` of holomorphic germs at the origin. -/
abbrev HolomorphicGerm (n : ℕ) := holomorphicGermSubring n


-- @@ L61-64 verbatim
/-- Pass from an analytic representative to its holomorphic germ. -/
def HolomorphicGerm.ofFunction {n : ℕ} (f : ComplexEuclidean n → ℂ)
    (hf : AnalyticAt ℂ f 0) : HolomorphicGerm n :=
  ⟨(f : FunctionGerm n), ⟨f, hf, rfl⟩⟩


-- @@ L66-70 verbatim
@[simp]
theorem HolomorphicGerm.coe_ofFunction {n : ℕ} (f : ComplexEuclidean n → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    ((HolomorphicGerm.ofFunction f hf : HolomorphicGerm n) : FunctionGerm n) = f :=
  rfl


-- @@ L72-76 verbatim
/-- Every holomorphic germ has an analytic representative. -/
theorem HolomorphicGerm.exists_rep {n : ℕ} (φ : HolomorphicGerm n) :
    ∃ f : ComplexEuclidean n → ℂ,
      AnalyticAt ℂ f 0 ∧ (f : FunctionGerm n) = φ :=
  φ.property


-- @@ L78-81 verbatim
/-- Evaluation at the origin, as a ring homomorphism. -/
def evalAtOriginHom (n : ℕ) : HolomorphicGerm n →+* ℂ :=
  (Filter.Germ.valueRingHom : FunctionGerm n →+* ℂ).comp
    (holomorphicGermSubring n).subtype


-- @@ L83-85 verbatim
/-- Evaluation of a holomorphic germ at the origin. -/
abbrev evalAtOrigin {n : ℕ} (φ : HolomorphicGerm n) : ℂ :=
  evalAtOriginHom n φ


-- @@ L87-91 verbatim
@[simp]
theorem evalAtOrigin_ofFunction {n : ℕ} (f : ComplexEuclidean n → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    evalAtOrigin (HolomorphicGerm.ofFunction f hf) = f 0 :=
  rfl


-- @@ L93-97 verbatim
instance holomorphicGerm_nontrivial (n : ℕ) : Nontrivial (HolomorphicGerm n) := by
  refine ⟨⟨0, 1, ?_⟩⟩
  intro h
  exact (zero_ne_one : (0 : ℂ) ≠ 1)
    (by simpa using congrArg (evalAtOriginHom n) h)


-- @@ L99-126 verbatim
/-- A holomorphic germ is a unit exactly when its value at the origin is nonzero. -/
theorem holomorphicGerm_isUnit_iff {n : ℕ} (φ : HolomorphicGerm n) :
    IsUnit φ ↔ evalAtOrigin φ ≠ 0 := by
  constructor
  · intro hφ
    exact isUnit_iff_ne_zero.mp (hφ.map (evalAtOriginHom n))
  · intro hφ0
    obtain ⟨f, hf, hrep⟩ := φ.property
    have hf0 : f 0 ≠ 0 := by
      change Filter.Germ.value (φ : FunctionGerm n) ≠ 0 at hφ0
      rw [← hrep] at hφ0
      simpa using hφ0
    let ψ : HolomorphicGerm n :=
      ⟨((f⁻¹ : ComplexEuclidean n → ℂ) : FunctionGerm n),
        ⟨(f⁻¹ : ComplexEuclidean n → ℂ), hf.inv hf0, rfl⟩⟩
    have hne : ∀ᶠ x in 𝓝 (0 : ComplexEuclidean n), f x ≠ 0 :=
      hf.continuousAt.eventually_ne hf0
    have hmul : φ * ψ = 1 := by
      apply Subtype.ext
      change (φ : FunctionGerm n) *
        ((f⁻¹ : ComplexEuclidean n → ℂ) : FunctionGerm n) = 1
      rw [← hrep, ← Filter.Germ.coe_mul, ← Filter.Germ.coe_one]
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [hne] with x hx
      exact mul_inv_cancel₀ hx
    have hmul' : ψ * φ = 1 := by
      rw [mul_comm, hmul]
    exact ⟨⟨φ, ψ, hmul, hmul'⟩, rfl⟩


-- @@ L128-136 verbatim
/-- The holomorphic germ ring is local. -/
theorem holomorphicGerm_isLocalRing (n : ℕ) : IsLocalRing (HolomorphicGerm n) := by
  apply IsLocalRing.of_isUnit_or_isUnit_one_sub_self
  intro φ
  by_cases hφ : evalAtOrigin φ = 0
  · right
    apply (holomorphicGerm_isUnit_iff (1 - φ)).2
    simp [hφ]
  · exact Or.inl ((holomorphicGerm_isUnit_iff φ).2 hφ)


-- @@ L138-139 verbatim
instance holomorphicGerm_instIsLocalRing (n : ℕ) : IsLocalRing (HolomorphicGerm n) :=
  holomorphicGerm_isLocalRing n


-- @@ L141-148 verbatim
/-- The maximal ideal consists exactly of germs vanishing at the origin. -/
theorem holomorphicGerm_maximalIdeal (n : ℕ) :
    IsLocalRing.maximalIdeal (HolomorphicGerm n) =
      Ideal.comap (evalAtOriginHom n) ⊥ := by
  ext φ
  rw [IsLocalRing.mem_maximalIdeal]
  simp only [mem_nonunits_iff, Ideal.mem_comap, Ideal.mem_bot]
  simpa only [not_ne_iff] using not_congr (holomorphicGerm_isUnit_iff φ)


-- @@ L150-150 verbatim
end


-- @@ L152-152 verbatim
end LocalComplexGeometry
