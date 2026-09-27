/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import LeanPool.JacobianDiffgeo.Path.Continuation
public import Mathlib.Topology.Homotopy.Path
import LeanPool.JacobianDiffgeo.Path.HomotopySquare
import Mathlib.MeasureTheory.Integral.Bochner.Basic


-- @@ L13-27 verbatim
/-!
# Periods of a holomorphic 1-form along a loop (CC6)

Unit: paths-and-integrals (`docs/design/paths-and-integrals.md` §6). Carrier decision (CC9
alignment): based loops `Path x x`, with descent to `Path.Homotopic.Quotient x x` available via
`pathIntegralQ`. This unit does not define the period subgroup (jacobian-construction's job); it
exports the loop-algebra lemmas that make `AddSubgroup.closure (Set.range (periodVector b))`
well-behaved.

Main declarations:
* `RS.period γ η` — abbreviation for `pathIntegral γ η` on a based loop.
* `RS.period_trans/symm/refl/congr_homotopic/conj`.
* `RS.periodVector b γ` — the period vector w.r.t. a basis `b` of `Form1 X`, with
  `periodVector_trans/symm/refl`.
-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
open scoped ContDiff Manifold

-- @@ L32-32 verbatim
open IsManifold Module


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-36 verbatim
namespace RS


-- @@ L38-38 verbatim
variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

-- @@ L39-39 verbatim
variable {x x' : X}


-- @@ L41-42 verbatim
/-- The period of a 1-form along a loop. -/
noncomputable abbrev period (γ : Path x x) (η : Form1 X) : ℂ := pathIntegral γ η


-- @@ L44-45 verbatim
theorem period_trans (γ γ' : Path x x) (η : Form1 X) :
    period (γ.trans γ') η = period γ η + period γ' η := pathIntegral_trans γ γ' η


-- @@ L47-48 verbatim
theorem period_symm (γ : Path x x) (η : Form1 X) : period γ.symm η = -period γ η :=
  pathIntegral_symm γ η


-- @@ L50-50 verbatim
theorem period_refl (η : Form1 X) : period (Path.refl x) η = 0 := pathIntegral_refl x η


-- @@ L52-53 verbatim
theorem period_congr_homotopic {γ γ' : Path x x} (h : γ.Homotopic γ') (η : Form1 X) :
    period γ η = period γ' η := pathIntegral_congr_homotopic h η


-- @@ L55-60 verbatim
/-- Conjugation invariance: periods are basepoint-independent along a connecting path. -/
theorem period_conj (σ : Path x' x) (γ : Path x x) (η : Form1 X) :
    period ((σ.trans γ).trans σ.symm) η = period γ η := by
  change pathIntegral ((σ.trans γ).trans σ.symm) η = pathIntegral γ η
  rw [pathIntegral_trans, pathIntegral_trans, pathIntegral_symm]
  ring


-- @@ L62-64 verbatim
/-- Period vector w.r.t. a basis of `Form1 X` (CC9 feed). -/
noncomputable def periodVector {n : ℕ} (b : Basis (Fin n) ℂ (Form1 X)) (γ : Path x x) :
    Fin n → ℂ := fun i => period γ (b i)


-- @@ L66-70 verbatim
theorem periodVector_trans {n : ℕ} (b : Basis (Fin n) ℂ (Form1 X)) (γ γ' : Path x x) :
    periodVector b (γ.trans γ') = periodVector b γ + periodVector b γ' := by
  funext i
  change period (γ.trans γ') (b i) = period γ (b i) + period γ' (b i)
  exact period_trans γ γ' (b i)


-- @@ L72-76 verbatim
theorem periodVector_symm {n : ℕ} (b : Basis (Fin n) ℂ (Form1 X)) (γ : Path x x) :
    periodVector b γ.symm = -periodVector b γ := by
  funext i
  change period γ.symm (b i) = -period γ (b i)
  exact period_symm γ (b i)


-- @@ L78-82 verbatim
@[simp] theorem periodVector_refl {n : ℕ} (b : Basis (Fin n) ℂ (Form1 X)) :
    periodVector b (Path.refl x) = 0 := by
  funext i
  change period (Path.refl x) (b i) = 0
  exact period_refl (b i)


-- @@ L84-84 verbatim
end RS


-- @@ L86-86 verbatim
end
