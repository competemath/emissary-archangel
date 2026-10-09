import OAI.Algebra.AffineCancellation.RelativeClearing
import OAI.Algebra.AffineCancellation.PolynomialSlice
import OAI.Algebra.AffineCancellation.TorsorInverse


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
namespace ComplexCancellation.Torsor

-- @@ L10-10 verbatim
open LaurentPolynomial

-- @@ L11-11 verbatim
variable {P : Type*} [CommRing P] [IsDomain P] [Algebra ℂ P]

-- @@ L12-12 verbatim
variable (ρ : Degeneration.G →ₐ[ℂ] P) (Q : Frame ρ) (D : Derivation ℂ Degeneration.G Degeneration.G)

-- @@ L13-13 verbatim
variable (hρ : Function.Injective ρ)

-- @@ L14-14 verbatim
variable (hc : ∀ p, p ∈ InvariantClearing.subalgebra ρ D)

-- @@ L15-15 verbatim
include hρ hc

-- @@ L16-23 verbatim
lemma clear_C (p : P) : C p ∈ RelativeClearing.subalgebra Bundle.pullback (forward ρ Q) D := by
  obtain ⟨c,r,hc,hcn,hcr⟩ := hc p
  refine ⟨c,Bundle.pullback r,hc,hcn,?_⟩
  have h := DFunLike.congr_fun (forward_pullback ρ Q hρ) c
  have h' := DFunLike.congr_fun (forward_pullback ρ Q hρ) r
  change forward ρ Q (Bundle.pullback c)=C (ρ c) at h
  change forward ρ Q (Bundle.pullback r)=C (ρ r) at h'
  rw [h,h',← map_mul,hcr]

-- @@ L24-32 verbatim
lemma clear_T_one : T 1 ∈ RelativeClearing.subalgebra Bundle.pullback (forward ρ Q) D := by
  have he : T 1=C Q.c₀*forward ρ Q (Bundle.j Determinant.a)-C Q.b₀*forward ρ Q (Bundle.j Determinant.d) := by
    rw [forward_j,forward_j,frameMap_a,frameMap_d]
    calc _ = C (Q.a₀*Q.c₀-Q.d₀*Q.b₀)*T 1 := by rw [Q.det,map_one,one_mul]
      _ = _ := by rw [map_sub,map_mul,map_mul]; ring
  rw [he]
  apply sub_mem
  · exact mul_mem (clear_C ρ Q D hρ hc _) (RelativeClearing.image_mem _ _ _ _)
  · exact mul_mem (clear_C ρ Q D hρ hc _) (RelativeClearing.image_mem _ _ _ _)

-- @@ L33-41 verbatim
lemma clear_T_neg_one : T (-1) ∈ RelativeClearing.subalgebra Bundle.pullback (forward ρ Q) D := by
  have he : T (-1)=C Q.a₀*forward ρ Q (Bundle.j Determinant.c)-C Q.d₀*forward ρ Q (Bundle.j Determinant.b) := by
    rw [forward_j,forward_j,frameMap_c,frameMap_b]
    calc _ = C (Q.a₀*Q.c₀-Q.d₀*Q.b₀)*T (-1) := by rw [Q.det,map_one,one_mul]
      _ = _ := by rw [map_sub,map_mul,map_mul]; ring
  rw [he]
  apply sub_mem
  · exact mul_mem (clear_C ρ Q D hρ hc _) (RelativeClearing.image_mem _ _ _ _)
  · exact mul_mem (clear_C ρ Q D hρ hc _) (RelativeClearing.image_mem _ _ _ _)

-- @@ L42-49 verbatim
lemma clear_T (n : ℤ) : T n ∈ RelativeClearing.subalgebra Bundle.pullback (forward ρ Q) D := by
  by_cases hn : 0 ≤ n
  · have he : T n=(T 1 : L (P := P))^n.toNat := by rw [T_pow,Int.toNat_of_nonneg hn,mul_one]
    rw [he]
    exact pow_mem (clear_T_one ρ Q D hρ hc) _
  · have he : T n=(T (-1) : L (P := P))^(-n).toNat := by rw [T_pow,Int.toNat_of_nonneg (by omega : 0 ≤ -n)]; congr 1; omega
    rw [he]
    exact pow_mem (clear_T_neg_one ρ Q D hρ hc) _

-- @@ L50-53 verbatim
lemma clear_laurent (r : L (P := P)) : r ∈ RelativeClearing.subalgebra Bundle.pullback (forward ρ Q) D := by
  induction r using LaurentPolynomial.induction_on' with
  | add r s hr hs => exact add_mem hr hs
  | C_mul_T n p => exact mul_mem (clear_C ρ Q D hρ hc p) (clear_T ρ Q D hρ hc n)

-- @@ L54-54 verbatim
end ComplexCancellation.Torsor


-- @@ L56-56 verbatim
end


-- @@ L58-58 verbatim
end OAI
