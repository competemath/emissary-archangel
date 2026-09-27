/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCylinderFieldBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketShiftArithmetic
import LeanPool.NavierStokesAndEuler.Euler.PacketMajorantShift
import Mathlib.Algebra.Order.Star.Real


-- @@ L14-14 verbatim
/-! One spare factorial shift pays all finite grade sums without changing the external radius. -/


-- @@ L16-16 verbatim
@[expose] public section



-- @@ L19-19 verbatim
namespace EulerGevrey


-- @@ L21-32 verbatim
theorem finite_cost_absorbed (C R : ℝ) (hC : 0 ≤ C) (hCR : C ≤ R)
    (m d n : ℕ) (hd : 0 < d) (hm : m ≤ d ^ 2) :
    (C*(m : ℝ))*majorant R (d-1) n ≤ majorant R d n := by
  have hR : 0 ≤ R := hC.trans hCR
  have hdn : d^2 ≤ (n+d)^2 := Nat.pow_le_pow_left (by omega : d ≤ n+d) 2
  have hmn : (m : ℝ) ≤ ((n+d : ℕ) : ℝ)^2 := by exact_mod_cast hm.trans hdn
  have hcost : C*(m : ℝ) ≤ R*((n+d : ℕ) : ℝ)^2 :=
    (mul_le_mul_of_nonneg_left hmn hC).trans (mul_le_mul_of_nonneg_right hCR (sq_nonneg _))
  have h := mul_le_mul_of_nonneg_right hcost (majorant_nonneg R hR (d-1) n)
  have he := majorant_succ_identity R (d-1) n
  rw [show d-1+1=d by omega,show n+(d-1)+1=n+d by omega] at he
  exact h.trans_eq he.symm


-- @@ L34-34 verbatim
end EulerGevrey


-- @@ L36-36 verbatim
namespace EulerPacketCylinderField.Field


-- @@ L38-38 verbatim
open Set Finset EulerGevrey EulerPacketProfileRecursion


-- @@ L40-40 verbatim
variable {P T : ℝ} [Fact (0 < P)]


-- @@ L42-55 verbatim
theorem wordBound_finset_absorb {ι : Type*} (s : Finset ι) (f : ι → VectorField)
    (G : ∀ i, Field P T (f i)) (q : ℕ) (R C : ℝ) (d : ℕ) (shift : ι → ℕ)
    (hR : 1 ≤ R) (hC : 0 ≤ C) (hCR : C ≤ R) (hd : 0 < d)
    (hcount : s.card ≤ d ^ 2) (hshift : ∀ i ∈ s, shift i < d)
    (hG : ∀ i ∈ s, (G i).WordBound q R C (shift i)) :
    (Field.finsetSum s f G).WordBound q R 1 d := by
  have hs := wordBound_finsetSum s f G (fun _ => C)
    (fun i hi => (hG i hi).mono_shift hR hC (by have := hshift i hi; omega : shift i ≤ d-1))
  intro n
  have hn := hs n
  simp only [sum_const,nsmul_eq_mul] at hn
  rw [mul_comm (s.card : ℝ) C] at hn
  have hc := finite_cost_absorbed C R hC hCR s.card d n hd hcount
  simpa only [one_mul] using hn.trans hc


-- @@ L57-57 verbatim
end EulerPacketCylinderField.Field


-- @@ L59-59 verbatim
namespace EulerPacketShiftArithmetic


-- @@ L61-66 verbatim
/-- Even a padded quadratic family of grade terms is paid by the source's spare shift. -/
theorem padded_grade_count (p : ℕ) (hp : 2 ≤ p) :
    100*(p+2)^2 ≤ (meanForceShift p)^2 ∧ 100*(p+2)^2 ≤ (highForceShift p)^2 := by
  obtain ⟨hm,hh⟩ := force_shift_dominates_grade p hp
  have hpoly : 100*(p+2)^2 ≤ (25*p)^2 := by nlinarith
  exact ⟨hpoly.trans (Nat.pow_le_pow_left hm 2),hpoly.trans (Nat.pow_le_pow_left hh 2)⟩


-- @@ L68-68 verbatim
end EulerPacketShiftArithmetic
