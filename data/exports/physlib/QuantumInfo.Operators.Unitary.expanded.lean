/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg, Rodolfo Soldati
-/
module

public import QuantumInfo.States.Mixed.MState


-- @@ L10-16 verbatim
/-! # Unitary operators on quantum state

This file is intended for lemmas about unitary matrices (`Matrix.unitaryGroup`) and how they
apply to `Bra`s, `Ket`s, and `MState` mixed states.

This is imported by `CPTPMap` to define things like unitary channels, Kraus operators, and
complementary channels, so this file itself does not discuss channels yet. -/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
noncomputable section


-- @@ L22-22 verbatim
open RealInnerProductSpace

-- @@ L23-23 verbatim
open InnerProductSpace


-- @@ L25-25 verbatim
namespace MState


-- @@ L27-27 verbatim
variable {d d₁ d₂ d₃ : Type*}

-- @@ L28-28 verbatim
variable [Fintype d] [Fintype d₁] [Fintype d₂] [Fintype d₃]

-- @@ L29-29 verbatim
variable [DecidableEq d]

-- @@ L30-30 verbatim
variable {ψ φ f : Ket d}


-- @@ L32-36 expanded
/-- Conjugate a state by a unitary matrix (applying the unitary as an evolution). -/
def uConj (ρ : MState d) (U : Matrix.unitaryGroup d ℂ) : MState d
    where
  M := ρ.M.conj U.val
  nonneg := HermitianMat.conj_nonneg U.val ρ.nonneg
  tr := by simp


-- @@ L38-41 verbatim
/-- `MState.uConj`, the action of a unitary on a mixed state by conjugation.
The ◃ notation comes from the theory of racks and quandles, where this is a
conjugation-like operation. -/
scoped[MState] notation:80 U:80 " ◃ " ρ:81 => MState.uConj ρ U


-- @@ L43-51 expanded
set_option backward.isDefEq.respectTransparency false in
/-- You might think this should only be true up to permutation, so that it would read like
`∃ σ : Equiv.Perm d, (ρ.uConj U).spectrum = ρ.spectrum.relabel σ`. But since eigenvalues
of a matrix are always canonically sorted, this is actually an equality.
-/
@[simp]
theorem uConj_spectrum_eq (ρ : MState d) (U : Matrix.unitaryGroup d ℂ) :
    (ρ.uConj U).spectrum = ρ.spectrum := by simp [spectrum, uConj]


-- @@ L53-55 expanded
@[simp]
theorem inner_uConj (ρ σ : MState d) (U : Matrix.unitaryGroup d ℂ) :
    ⟪U ◃ ρ, U ◃ σ⟫_Prob = ⟪ρ, σ⟫_Prob := by simp [uConj, inner_def]


-- @@ L57-83 expanded
/-- The **No-cloning theorem**, saying that if states `ψ` and `φ` can both be perfectly cloned
using a unitary `U` and a fiducial state `f`, and they aren't identical (their inner product is
less than 1), then the two states must be orthogonal to begin with. In short: only orthogonal
states can be simultaneously cloned. -/
theorem no_cloning {U : Matrix.unitaryGroup (d × d) ℂ}
    (hψ : U ◃ pure (Ket.prod ψ f) = pure (Ket.prod ψ ψ))
    (hφ : U ◃ pure (Ket.prod φ f) = pure (Ket.prod φ φ)) (H : ⟪pure ψ, pure φ⟫_Prob < (1 : ℝ)) :
    ⟪pure ψ, pure φ⟫_Prob = (0 : ℝ) := by
  set ρψ := pure ψ
  set ρφ := pure φ
  have h1 : ⟪ρψ, ρφ⟫_Prob * ⟪ρψ, ρφ⟫_Prob = ⟪pure (Ket.prod ψ ψ), pure (Ket.prod φ φ)⟫_Prob := by
    grind only [pure_prod_pure, prod_inner_prod]
  have h2 :
    (⟪pure (Ket.prod ψ ψ), pure (Ket.prod φ φ)⟫_Prob : ℝ) =
      ⟪U ◃ pure (Ket.prod ψ f), U ◃ pure (Ket.prod φ f)⟫_Prob :=
    by grind only [pure_prod_pure]
  replace h2 :
    ((pure (Ket.prod ψ ψ)).m * (pure (Ket.prod φ φ)).m).trace.re = (ρψ.m * ρφ.m).trace.re :=
    by
    convert! ← h2
    simp +zetaDelta only [inner_uConj, pure_prod_pure, prod]
    simp [inner, ← Matrix.mul_kronecker_mul, pure_mul_self, Matrix.trace_kronecker]
  have h3 : (ρψ.m * ρφ.m).trace.re * ((ρψ.m * ρφ.m).trace.re - 1) = 0 :=
    by
    rw [mul_sub, sub_eq_zero, mul_one]
    exact congr(Subtype.val $h1).trans h2
  rw [mul_eq_zero] at h3
  apply h3.resolve_right
  exact sub_ne_zero_of_ne H.ne


-- @@ L85-85 verbatim
end MState
