/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.KummerPairing.Basic


-- @@ L10-16 verbatim
/-!
# Kernel triviality for the Kummer pairing

This file isolates the two kernel statements for a Kummer pairing.  The
nondegeneracy theorem used later is built from these separate left and right
kernel facts.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
universe u v


-- @@ L22-22 verbatim
noncomputable section


-- @@ L24-24 verbatim
open NumberField


-- @@ L26-26 verbatim
namespace BernoulliRegular



-- @@ L29-29 verbatim
section Nondegenerate


-- @@ L31-31 verbatim
variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [NumberField K]

-- @@ L32-32 verbatim
variable {P : HilbertKummerSubgroup.HilbertKummerPresentation.{u, v} (p := p) (K := K)}


-- @@ L34-48 verbatim
/-- The left kernel of the Kummer pairing: Galois elements pairing trivially
with every Kummer class. -/
def KummerPairingData.leftKernel (B : KummerPairingData (p := p) (K := K) P) :
    Subgroup P.PairingLeft where
  carrier := {h | ∀ b : P.PairingRight, B.apply h b = 1}
  one_mem' := fun b =>
    B.one_left b
  mul_mem' := by
    intro h₁ h₂ h₁_mem h₂_mem b
    rw [B.mul_left h₁ h₂ b, h₁_mem b, h₂_mem b, one_mul]
  inv_mem' := by
    intro h h_mem b
    have hmul := B.mul_left h⁻¹ h b
    rw [inv_mul_cancel, B.one_left b, h_mem b, mul_one] at hmul
    exact hmul.symm


-- @@ L50-64 verbatim
/-- The right kernel of the Kummer pairing: Kummer classes pairing trivially
with every Galois element. -/
def KummerPairingData.rightKernel (B : KummerPairingData (p := p) (K := K) P) :
    Subgroup P.PairingRight where
  carrier := {b | ∀ h : P.PairingLeft, B.apply h b = 1}
  one_mem' := fun h =>
    B.one_right h
  mul_mem' := by
    intro b₁ b₂ b₁_mem b₂_mem h
    rw [B.mul_right h b₁ b₂, b₁_mem h, b₂_mem h, one_mul]
  inv_mem' := by
    intro b b_mem h
    have hmul := B.mul_right h b⁻¹ b
    rw [inv_mul_cancel, B.one_right h, b_mem h, mul_one] at hmul
    exact hmul.symm


-- @@ L66-71 verbatim
/-- The two kernel-triviality statements for a Kummer pairing, kept separate so
later tickets can use one side without unfolding the other. -/
structure KummerPairingKernelTrivial
    (B : KummerPairingData (p := p) (K := K) P) where
  leftKernel_eq_bot : B.leftKernel = ⊥
  rightKernel_eq_bot : B.rightKernel = ⊥


-- @@ L73-73 verbatim
namespace KummerPairingKernelTrivial


-- @@ L75-75 verbatim
variable {B : KummerPairingData (p := p) (K := K) P}


-- @@ L77-84 verbatim
/-- `T038b`, left side: a Galois element in the left kernel is trivial. -/
theorem left_eq_one (N : KummerPairingKernelTrivial (p := p) (K := K) B)
    {h : P.PairingLeft} (hh : ∀ b : P.PairingRight, B.apply h b = 1) :
    h = 1 := by
  have hmem : h ∈ B.leftKernel := hh
  have hbot : h ∈ (⊥ : Subgroup P.PairingLeft) := by
    simpa [N.leftKernel_eq_bot] using hmem
  exact Subgroup.mem_bot.mp hbot


-- @@ L86-93 verbatim
/-- `T038b`, right side: a Kummer class in the right kernel is trivial. -/
theorem right_eq_one (N : KummerPairingKernelTrivial (p := p) (K := K) B)
    {b : P.PairingRight} (hb : ∀ h : P.PairingLeft, B.apply h b = 1) :
    b = 1 := by
  have hmem : b ∈ B.rightKernel := hb
  have hbot : b ∈ (⊥ : Subgroup P.PairingRight) := by
    simpa [N.rightKernel_eq_bot] using hmem
  exact Subgroup.mem_bot.mp hbot


-- @@ L95-95 verbatim
end KummerPairingKernelTrivial


-- @@ L97-97 verbatim
/-! ### Packaged nondegenerate pairing -/


-- @@ L99-104 verbatim
/-- The packaged nondegenerate Kummer pairing API consumed by reflection:
a bilinear pairing together with separate proofs that both kernels are trivial. -/
structure NondegenerateKummerPairing
    (P : HilbertKummerSubgroup.HilbertKummerPresentation.{u, v} (p := p) (K := K)) where
  pairingData : KummerPairingData (p := p) (K := K) P
  kernelTrivial : KummerPairingKernelTrivial (p := p) (K := K) pairingData


-- @@ L106-106 verbatim
namespace NondegenerateKummerPairing


-- @@ L108-108 verbatim
variable {P : HilbertKummerSubgroup.HilbertKummerPresentation.{u, v} (p := p) (K := K)}


-- @@ L110-113 verbatim
/-- The underlying bilinear pairing data. -/
def toPairingData (N : NondegenerateKummerPairing (p := p) (K := K) P) :
    KummerPairingData (p := p) (K := K) P :=
  N.pairingData


-- @@ L115-118 verbatim
/-- The packaged pairing map. -/
def pairingMap (N : NondegenerateKummerPairing (p := p) (K := K) P) :
    P.PairingLeft → P.PairingRight → KummerPairingValue p :=
  N.pairingData.apply


-- @@ L120-124 verbatim
@[simp]
theorem one_left (N : NondegenerateKummerPairing (p := p) (K := K) P)
    (b : P.PairingRight) :
    pairingMap (p := p) (K := K) N 1 b = 1 :=
  N.pairingData.one_left b


-- @@ L126-131 verbatim
theorem mul_left (N : NondegenerateKummerPairing (p := p) (K := K) P)
    (h₁ h₂ : P.PairingLeft) (b : P.PairingRight) :
    pairingMap (p := p) (K := K) N (h₁ * h₂) b =
      pairingMap (p := p) (K := K) N h₁ b *
        pairingMap (p := p) (K := K) N h₂ b :=
  N.pairingData.mul_left h₁ h₂ b


-- @@ L133-137 verbatim
@[simp]
theorem one_right (N : NondegenerateKummerPairing (p := p) (K := K) P)
    (h : P.PairingLeft) :
    pairingMap (p := p) (K := K) N h 1 = 1 :=
  N.pairingData.one_right h


-- @@ L139-144 verbatim
theorem mul_right (N : NondegenerateKummerPairing (p := p) (K := K) P)
    (h : P.PairingLeft) (b₁ b₂ : P.PairingRight) :
    pairingMap (p := p) (K := K) N h (b₁ * b₂) =
      pairingMap (p := p) (K := K) N h b₁ *
        pairingMap (p := p) (K := K) N h b₂ :=
  N.pairingData.mul_right h b₁ b₂


-- @@ L146-151 verbatim
/-- Left nondegeneracy in elementwise form. -/
theorem left_eq_one (N : NondegenerateKummerPairing (p := p) (K := K) P)
    {h : P.PairingLeft}
    (hh : ∀ b : P.PairingRight, pairingMap (p := p) (K := K) N h b = 1) :
    h = 1 :=
  KummerPairingKernelTrivial.left_eq_one (p := p) (K := K) N.kernelTrivial hh


-- @@ L153-158 verbatim
/-- Right nondegeneracy in elementwise form. -/
theorem right_eq_one (N : NondegenerateKummerPairing (p := p) (K := K) P)
    {b : P.PairingRight}
    (hb : ∀ h : P.PairingLeft, pairingMap (p := p) (K := K) N h b = 1) :
    b = 1 :=
  KummerPairingKernelTrivial.right_eq_one (p := p) (K := K) N.kernelTrivial hb


-- @@ L160-163 verbatim
/-- Left-kernel form of nondegeneracy. -/
theorem leftKernel_eq_bot (N : NondegenerateKummerPairing (p := p) (K := K) P) :
    N.pairingData.leftKernel = ⊥ :=
  N.kernelTrivial.leftKernel_eq_bot


-- @@ L165-168 verbatim
/-- Right-kernel form of nondegeneracy. -/
theorem rightKernel_eq_bot (N : NondegenerateKummerPairing (p := p) (K := K) P) :
    N.pairingData.rightKernel = ⊥ :=
  N.kernelTrivial.rightKernel_eq_bot


-- @@ L170-170 verbatim
end NondegenerateKummerPairing


-- @@ L172-172 verbatim
end Nondegenerate


-- @@ L174-174 verbatim
end BernoulliRegular


-- @@ L176-176 verbatim
end
