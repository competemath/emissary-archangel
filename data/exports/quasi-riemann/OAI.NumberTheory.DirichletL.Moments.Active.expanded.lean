import OAI.NumberTheory.DirichletL.Moments.Canonical
import OAI.NumberTheory.DirichletL.Moments.FirstPoisson


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped BigOperators Classical SchwartzMap

-- @@ L8-8 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentActive

-- @@ L10-10 verbatim
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge

-- @@ L11-11 verbatim
open CanonicalRowCompletion CenteredMomentCanonical


-- @@ L13-13 verbatim
def netExponent (c d : ℕ) : ℕ := (c + 5 * d) % 6


-- @@ L15-30 verbatim
theorem local_pair_reduction (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    (c d : ℕ) (x : O ⧸ P) :
    (actualSextic P hg ^ c) x * star ((actualSextic P hg ^ d) x) =
      (actualSextic P hg ^ netExponent c d) x := by
  have h6 : actualSextic P hg ^ 6 = 1 := by
    rw [← actualSextic_order_six P hg hchar]
    exact pow_orderOf_eq_one _
  have h5 : actualSextic P hg ^ 5 = (actualSextic P hg)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    simpa only [← pow_succ] using h6
  rw [MulChar.star_apply', ← MulChar.mul_apply]
  congr 1
  unfold netExponent
  rw [← actualSextic_order_six P hg hchar, pow_mod_orderOf,
    pow_add, pow_mul, h5, inv_pow]


-- @@ L32-33 verbatim
def activeSupport {ι : Type*} (B : Finset ι) (c d : ι → ℕ) : Finset ι :=
  B.filter (fun i => netExponent (c i) (d i) ≠ 0)


-- @@ L35-36 verbatim
def principalSupport {ι : Type*} (B : Finset ι) (c d : ι → ℕ) : Finset ι :=
  B.filter (fun i => netExponent (c i) (d i) = 0)


-- @@ L38-40 verbatim
theorem netExponent_ne_zero {ι : Type*} (B : Finset ι) (c d : ι → ℕ)
    (i : activeSupport B c d) : netExponent (c i.val) (d i.val) ≠ 0 :=
  (Finset.mem_filter.mp i.property).2


-- @@ L42-42 verbatim
theorem netExponent_lt_six (c d : ℕ) : netExponent c d < 6 := Nat.mod_lt _ (by decide)


-- @@ L44-59 verbatim
theorem principal_product_eq_mask {ι : Type*}
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal] (B : Finset ι) (z : O) :
    (∏ i ∈ B, (1 : MulChar (O ⧸ P i) ℂ) (Ideal.Quotient.mk (P i) z)) =
      rowCoprimeMask P B z := by
  by_cases h : ∃ i ∈ B, z ∈ P i
  · rw [rowCoprimeMask, ite_eq_left h]
    obtain ⟨i, hi, hz⟩ := h
    apply Finset.prod_eq_zero hi
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hz, MulChar.map_zero]
  · rw [rowCoprimeMask, ite_eq_right h]
    apply Finset.prod_eq_one
    intro i hi
    apply MulChar.one_apply
    let : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
    apply isUnit_iff_ne_zero.mpr
    exact fun hz => h ⟨i, hi, Ideal.Quotient.eq_zero_iff_mem.mp hz⟩


-- @@ L61-61 verbatim
variable {ι : Type*}


-- @@ L63-92 verbatim
theorem common_ideal_pair_active (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ)
    (hc : ∀ i ∈ B, c i ≠ 0) (hd : ∀ i ∈ B, d i ≠ 0) (z : O) :
    idealRowHom z (∏ i ∈ B, P i ^ c i) *
      star (idealRowHom z (∏ i ∈ B, P i ^ d i)) =
      rowCoprimeMask P (principalSupport B c d) z *
        finiteSexticRow (fun i : activeSupport B c d => P i.val)
          (fun i => hg i.val) (fun i => netExponent (c i.val) (d i.val)) z := by
  let f := fun i => (actualSextic (P i) (hg i) ^ netExponent (c i) (d i))
    (Ideal.Quotient.mk (P i) z)
  have hlocal : idealRowHom z (∏ i ∈ B, P i ^ c i) *
      star (idealRowHom z (∏ i ∈ B, P i ^ d i)) = ∏ i ∈ B, f i := by
    simp only [map_prod, map_pow, star_prod, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [idealRowHom_prime z (P i) (hg i),
      ← MulChar.pow_apply' _ (hc i hi), ← MulChar.pow_apply' _ (hd i hi)]
    exact local_pair_reduction (P i) (hg i) (hchar i) (c i) (d i) _
  have hzero : (∏ i ∈ B.filter (fun i => netExponent (c i) (d i) = 0), f i) =
      rowCoprimeMask P (principalSupport B c d) z := by
    rw [← principal_product_eq_mask]
    apply Finset.prod_congr rfl
    intro i hi
    have he := (Finset.mem_filter.mp hi).2
    simp only [f, he, pow_zero]
  rw [hlocal, ← Finset.prod_filter_mul_prod_filter_not B
    (fun i => netExponent (c i) (d i) = 0) f, hzero]
  congr 1
  exact (Finset.prod_coe_sort (s := activeSupport B c d) (f := f)).symm


-- @@ L94-99 verbatim
theorem activePrimes_pairwise_coprime (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (B : Finset ι) (c d : ι → ℕ) :
    Pairwise (Function.onFun IsCoprime (fun i : activeSupport B c d => P i.val)) := by
  intro i j hij
  apply Ideal.isCoprime_of_isMaximal
  exact fun he => hij (Subtype.ext (hinj he))


-- @@ L101-110 verbatim
theorem active_gauss_norm (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2) (B : Finset ι) (c d : ι → ℕ) :
    ‖canonicalNormalizedGauss (fun i : activeSupport B c d => P i.val)
      (activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
      (fun i => netExponent (c i.val) (d i.val))‖ = 1 :=
  norm_canonicalNormalizedGauss (fun i : activeSupport B c d => P i.val)
    (activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => hchar i.val) (fun i => netExponent (c i.val) (d i.val))
    (netExponent_ne_zero B c d) (fun _i => netExponent_lt_six _ _)


-- @@ L112-112 verbatim
open ConcreteTraceCRT EisensteinSchwartzPoisson


-- @@ L114-141 verbatim
theorem common_ideal_pair_poisson (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hinj : Function.Injective P) (hg : ∀ i, goodLambda ∉ P i)
    (hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (B : Finset ι) (c d : ι → ℕ)
    (hc : ∀ i ∈ B, c i ≠ 0) (hd : ∀ i ∈ B, d i ≠ 0)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    let Q := fun i : activeSupport B c d => P i.val
    let row := finiteSexticRow Q (fun i => hg i.val)
      (fun i => netExponent (c i.val) (d i.val))
    let r := finitePrimeModulus Q
    (∑' z : O, (idealRowHom z (∏ i ∈ B, P i ^ c i) *
      star (idealRowHom z (∏ i ∈ B, P i ^ d i))) *
      W (‖eisEmbedding z‖ ^ 2 / K)) =
      ((K : ℂ) * canonicalNormalizedGauss Q
        (activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
        (fun i => netExponent (c i.val) (d i.val)) / (‖eisEmbedding r‖ : ℂ)) *
      ∑ E ∈ (principalSupport B c d).powerset,
        let e := primeSubsetGenerator P E
        ((UniqueFactorizationMonoid.moebius (∏ i ∈ E, P i) : ℂ) * row e /
          (‖eisEmbedding e‖ ^ 2 : ℝ)) *
        ∑' h : O, star (row h) * paperRadialFourier W
          (K * ‖eisEmbedding h‖ ^ 2 / (‖eisEmbedding e‖ ^ 2 * ‖eisEmbedding r‖ ^ 2)) := by
  simp_rw [common_ideal_pair_active P hg hchar B c d hc hd]
  exact canonical_masked_radial_poisson_collected P hinj (principalSupport B c d)
    (fun i : activeSupport B c d => P i.val)
    (activePrimes_pairwise_coprime P hinj B c d) (fun i => hg i.val)
    (fun i => hchar i.val) (fun i => netExponent (c i.val) (d i.val))
    (netExponent_ne_zero B c d) (fun i => netExponent_lt_six _ _) W K hK


-- @@ L143-143 verbatim
end SevenEighths.CenteredMomentActive

-- @@ L144-144 verbatim
end


-- @@ L146-146 verbatim
end OAI
