/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/
module

public import LeanPool.KasamiCyclicAdditive.Phase.CharacterSums
import Mathlib.MeasureTheory.Integral.Bochner.Basic


-- @@ L11-17 verbatim
/-!
# Objects of the phase-to-root-count identity

Throughout, `K` is a finite field (in the application `K = GF(2^n)`), `ψ` is a
primitive additive character of `K` with values in `ℂ` (in the application
`ψ x = (-1)^(Tr x)`), and `D` is an exponent inverse to `m` modulo `N = #Kˣ`.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
open Finset


-- @@ L23-23 verbatim
namespace KasamiCyclicAdditive.Phase


-- @@ L25-25 verbatim
section Defs


-- @@ L27-27 verbatim
variable (K : Type*) [Field K] [Fintype K] [DecidableEq K]


-- @@ L29-30 verbatim
/-- `U = μ₃(K)`, the group of cube roots of unity of `K`, as a finset. -/
def cubeRootsOne : Finset K := {u : K | u ^ 3 = 1}


-- @@ L32-33 verbatim
/-- `c = |μ₃(K)|`. -/
def mu3Card : ℕ := (cubeRootsOne K).card


-- @@ L35-35 verbatim
end Defs


-- @@ L37-37 verbatim
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]


-- @@ L39-40 verbatim
/-- `Φ(x) = ∑_{u ∈ U} ψ(u x^D)`. -/
noncomputable def phi (ψ : AddChar K ℂ) (D : ℕ) (x : K) : ℂ := ∑ u ∈ cubeRootsOne K, ψ (u * x ^ D)


-- @@ L42-43 verbatim
/-- The additive Fourier transform `Φ̂(z) = ∑_{t ∈ K} Φ(t) ψ(z t)`. -/
noncomputable def phiHat (ψ : AddChar K ℂ) (D : ℕ) (z : K) : ℂ := ∑ t : K, phi ψ D t * ψ (z * t)


-- @@ L45-47 verbatim
/-- `W_{u,v} = ∑_{x,y ∈ K} ψ(u x^D + v (A x + B y)^D + y^D)`. -/
noncomputable def weilSum (ψ : AddChar K ℂ) (D : ℕ) (A B u v : K) : ℂ :=
  ∑ x : K, ∑ y : K, ψ (u * x ^ D + v * (A * x + B * y) ^ D + y ^ D)


-- @@ L49-50 verbatim
/-- `R_{u,v}(A,B) = #{t ∈ K : u t^D + v (A t + B)^D = 1}`. -/
def rootCount (D : ℕ) (A B u v : K) : ℕ := #{t : K | u * t ^ D + v * (A * t + B) ^ D = 1}


-- @@ L52-54 verbatim
/-- `Z(ρ) = ∑_{λ ∈ G} S(λ) S(ρ λ) S(σ λ)`. -/
noncomputable def phaseTripleSum (S : K → ℂ) (rho sigma : K) : ℂ :=
  ∑ lam : Kˣ, S (lam : K) * S (rho * (lam : K)) * S (sigma * (lam : K))


-- @@ L56-62 verbatim
/-- The all-character Walsh formula
`2 S(a) = (Q/N) ∑_χ [G(χ^e)/G(χ^3)] χ(a)` for every `a ∈ Kˣ`, stated as a
property of `S` rather than assumed. -/
def WalshCharacterFormula (ψ : AddChar K ℂ) (e : ℕ) (S : K → ℂ) : Prop :=
  ∀ a : Kˣ, 2 * S (a : K) =
    (Fintype.card K : ℂ) / (Fintype.card Kˣ : ℂ) *
      ∑ χ : MulChar K ℂ, gaussSum (χ ^ e) ψ / gaussSum (χ ^ 3) ψ * χ (a : K)


-- @@ L64-64 verbatim
end KasamiCyclicAdditive.Phase
