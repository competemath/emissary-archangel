/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.KummerPairing.Setup


-- @@ L10-18 verbatim
/-!
# Basic Kummer pairing API

This file defines the typed pairing object used by the reflection layer.  The
mathematical construction of the pairing is represented by data over a
`HilbertKummerPresentation`; the bilinearity theorems below are proved by
projecting the corresponding fields.  This keeps the interface honest while the
later reflection tickets work against a stable API.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
universe u v


-- @@ L24-24 verbatim
noncomputable section


-- @@ L26-26 verbatim
open NumberField


-- @@ L28-28 verbatim
namespace BernoulliRegular



-- @@ L31-31 verbatim
section Basic


-- @@ L33-33 verbatim
variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]


-- @@ L35-35 verbatim
namespace HilbertKummerSubgroup


-- @@ L37-37 verbatim
namespace HilbertKummerPresentation


-- @@ L39-43 verbatim
/-- The left side of the Kummer pairing: the Galois group of the presentation
field over `K`. -/
abbrev PairingLeft (P : HilbertKummerPresentation.{u, v} (p := p) (K := K)) :
    Type v :=
  P.E ≃ₐ[K] P.E


-- @@ L45-48 verbatim
/-- The right side of the Kummer pairing: the declared Kummer subgroup `C`. -/
abbrev PairingRight (P : HilbertKummerPresentation.{u, v} (p := p) (K := K)) :
    Type u :=
  P.C


-- @@ L50-50 verbatim
end HilbertKummerPresentation


-- @@ L52-52 verbatim
end HilbertKummerSubgroup


-- @@ L54-57 verbatim
/-- The target group of the pairing.  We use `Multiplicative (ZMod p)` as a
compact model for the cyclic group of `p`-th roots of unity. -/
abbrev KummerPairingValue : Type :=
  Multiplicative (ZMod p)


-- @@ L59-68 verbatim
/-- Data of a Kummer pairing on a Hilbert Kummer presentation, together with
the bilinearity laws needed downstream. -/
structure KummerPairingData
    (P : HilbertKummerSubgroup.HilbertKummerPresentation.{u, v} (p := p) (K := K)) where
  pairing :
    P.PairingLeft → P.PairingRight → KummerPairingValue p
  map_one_left : ∀ b, pairing 1 b = 1
  map_mul_left : ∀ h₁ h₂ b, pairing (h₁ * h₂) b = pairing h₁ b * pairing h₂ b
  map_one_right : ∀ h, pairing h 1 = 1
  map_mul_right : ∀ h b₁ b₂, pairing h (b₁ * b₂) = pairing h b₁ * pairing h b₂


-- @@ L70-70 verbatim
namespace KummerPairingData


-- @@ L72-72 verbatim
variable {p K}

-- @@ L73-73 verbatim
variable {P : HilbertKummerSubgroup.HilbertKummerPresentation.{u, v} (p := p) (K := K)}


-- @@ L75-78 verbatim
/-- The Kummer pairing attached to the data. -/
def apply (B : KummerPairingData (p := p) (K := K) P) :
    P.PairingLeft → P.PairingRight → KummerPairingValue p :=
  B.pairing


-- @@ L80-84 verbatim
@[simp]
theorem one_left (B : KummerPairingData (p := p) (K := K) P)
    (b : P.PairingRight) :
    B.apply 1 b = 1 :=
  B.map_one_left b


-- @@ L86-89 verbatim
theorem mul_left (B : KummerPairingData (p := p) (K := K) P)
    (h₁ h₂ : P.PairingLeft) (b : P.PairingRight) :
    B.apply (h₁ * h₂) b = B.apply h₁ b * B.apply h₂ b :=
  B.map_mul_left h₁ h₂ b


-- @@ L91-95 verbatim
@[simp]
theorem one_right (B : KummerPairingData (p := p) (K := K) P)
    (h : P.PairingLeft) :
    B.apply h 1 = 1 :=
  B.map_one_right h


-- @@ L97-100 verbatim
theorem mul_right (B : KummerPairingData (p := p) (K := K) P)
    (h : P.PairingLeft) (b₁ b₂ : P.PairingRight) :
    B.apply h (b₁ * b₂) = B.apply h b₁ * B.apply h b₂ :=
  B.map_mul_right h b₁ b₂


-- @@ L102-108 verbatim
/-- The right input is well defined as an element of the Kummer subgroup:
equal representatives in the subgroup give equal pairing values. -/
theorem right_ext (B : KummerPairingData (p := p) (K := K) P)
    (h : P.PairingLeft) {b₁ b₂ : P.PairingRight}
    (hb : ((b₁ : P.C) : KummerPowerQuotient (p := p) K) = b₂) :
    B.apply h b₁ = B.apply h b₂ :=
  congrArg (B.apply h) (Subtype.ext hb)


-- @@ L110-110 verbatim
end KummerPairingData


-- @@ L112-112 verbatim
end Basic


-- @@ L114-114 verbatim
end BernoulliRegular


-- @@ L116-116 verbatim
end
