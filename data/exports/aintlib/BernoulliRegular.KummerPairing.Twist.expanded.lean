/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.KummerPairing.Nondegenerate


-- @@ L10-17 verbatim
/-!
# Galois twist formula for the Kummer pairing

This file packages the twist identity used in the reflection argument.  The
actual cyclotomic Galois actions on the Hilbert-side Galois group and the
Kummer subgroup are supplied as data; the exported theorem states the exact
formula downstream files should use.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
universe u v


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
open NumberField


-- @@ L27-27 verbatim
namespace BernoulliRegular



-- @@ L30-30 verbatim
section Twist


-- @@ L32-32 verbatim
variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]

-- @@ L33-33 verbatim
variable {P : HilbertKummerSubgroup.HilbertKummerPresentation.{u, v} (p := p) (K := K)}


-- @@ L35-38 verbatim
/-- The exponent by which `σ_a` acts on `p`-th roots of unity, represented in
the pairing target `Multiplicative (ZMod p)`. -/
def kummerTwistExponent (a : (ZMod p)ˣ) : ℕ :=
  (a : ZMod p).val


-- @@ L40-53 verbatim
/-- Data of the cyclotomic twist actions and the Kummer pairing twist formula.

The two action fields represent `h ↦ h^{σ_a}` on the Hilbert-side Galois group
and `b ↦ b^{σ_a}` on the Kummer subgroup. -/
structure KummerPairingTwistData
    (N : NondegenerateKummerPairing (p := p) (K := K) P) where
  leftTwist : (ZMod p)ˣ → P.PairingLeft → P.PairingLeft
  rightTwist : (ZMod p)ˣ → P.PairingRight → P.PairingRight
  twist_formula :
    ∀ (a : (ZMod p)ˣ) (h : P.PairingLeft) (b : P.PairingRight),
      NondegenerateKummerPairing.pairingMap (p := p) (K := K) N
          (leftTwist a h) (rightTwist a b) =
        NondegenerateKummerPairing.pairingMap (p := p) (K := K) N h b ^
          kummerTwistExponent p a


-- @@ L55-55 verbatim
namespace KummerPairingTwistData


-- @@ L57-57 verbatim
variable {p K}

-- @@ L58-58 verbatim
variable {N : NondegenerateKummerPairing (p := p) (K := K) P}


-- @@ L60-63 verbatim
/-- The Hilbert-side twist `h ↦ h^{σ_a}`. -/
def twistLeft (T : KummerPairingTwistData (p := p) (K := K) N)
    (a : (ZMod p)ˣ) (h : P.PairingLeft) : P.PairingLeft :=
  T.leftTwist a h


-- @@ L65-68 verbatim
/-- The Kummer-subgroup twist `b ↦ b^{σ_a}`. -/
def twistRight (T : KummerPairingTwistData (p := p) (K := K) N)
    (a : (ZMod p)ˣ) (b : P.PairingRight) : P.PairingRight :=
  T.rightTwist a b


-- @@ L70-78 verbatim
/-- `T039`: the Galois twist formula for the Kummer pairing. -/
theorem pairing_twist_formula
    (T : KummerPairingTwistData (p := p) (K := K) N)
    (a : (ZMod p)ˣ) (h : P.PairingLeft) (b : P.PairingRight) :
    NondegenerateKummerPairing.pairingMap (p := p) (K := K) N
        (T.twistLeft a h) (T.twistRight a b) =
      NondegenerateKummerPairing.pairingMap (p := p) (K := K) N h b ^
        kummerTwistExponent p a :=
  T.twist_formula a h b


-- @@ L80-80 verbatim
end KummerPairingTwistData


-- @@ L82-82 verbatim
end Twist


-- @@ L84-84 verbatim
end BernoulliRegular


-- @@ L86-86 verbatim
end
