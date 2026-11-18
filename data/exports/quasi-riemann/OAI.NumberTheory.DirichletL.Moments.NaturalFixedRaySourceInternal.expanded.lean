import OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCharacters
import OAI.NumberTheory.DirichletL.Moments.HeckeExceptionalEnergy


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentNaturalFixedRaySource

-- @@ L10-10 verbatim
open HeckeFamily CenteredExceptionalProfile CenteredExceptionalCount

-- @@ L11-11 verbatim
open HeckeRowClosure CanonicalRowCompletion ConcretePrimeRowBridge

-- @@ L12-12 verbatim
open CenteredMomentNaturalRowSource UniqueFactorizationMonoid

-- @@ L13-13 verbatim
local notation "O" => HeckeFamily.O


-- @@ L15-15 verbatim
def internalQ (Q : Ideal O) (η₀ : Character) : Ideal O := Q⊓η₀.modulus


-- @@ L17-18 verbatim
lemma internalQ_ne_zero (Q : Ideal O) (hQ : Q≠0) (η₀ : Character) : internalQ Q η₀≠0 :=
  Ideal.inf_ne_bot_of_ne_bot hQ η₀.modulus_ne_bot


-- @@ L20-22 verbatim
lemma internalQ_ne_top (Q : Ideal O) (hQ : Q≠⊤) (η₀ : Character) : internalQ Q η₀≠⊤ := by
  intro h
  exact hQ (top_le_iff.mp (h ▸ (inf_le_left : internalQ Q η₀≤Q)))


-- @@ L24-26 verbatim
lemma internalQ_coprime (Q P : Ideal O) (η₀ : Character)
    (hQP : IsCoprime Q P) (hηP : IsCoprime η₀.modulus P) : IsCoprime (internalQ Q η₀) P :=
  (hQP.mul_left hηP).of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr Ideal.mul_le_inf)


-- @@ L28-31 verbatim
lemma natural_nonzero_base {η : Character} {z : O} (F : NaturalRow η z) (I : Ideal O)
    (h : idealCoeff F.character I≠0) : idealCoeff η I≠0 := by
  rw [F.ideal] at h
  exact left_ne_zero_of_mul h


-- @@ L33-36 verbatim
lemma coefficient_forcing_coprime (η₀ : Character) (e : O) (he : elementCoeff η₀ e≠0)
    (Q P : Ideal O) (hQP : IsCoprime Q P) (hPe : P∣Ideal.span {e}) :
    IsCoprime (internalQ Q η₀) P :=
  internalQ_coprime Q P η₀ hQP (CenteredMomentChildRows.old_coefficient_prime_coprime η₀ e he P hPe)


-- @@ L38-45 verbatim
theorem energy_split (η η₀ : Character) (Q : Ideal O) (m A : O)
    (rows : Finset O) (f : O→ℂ) :
    (∑z∈rows,‖f z‖^2)=
      (∑z∈rows.filter (fun z=>¬FixedInducingRow η (internalQ Q η₀) m A z),‖f z‖^2)+
      ∑z∈rows.filter (fun z=>FixedInducingRow η (internalQ Q η₀) m A z),‖f z‖^2 := by
  simpa only [not_not] using
    (Finset.sum_filter_add_sum_filter_not rows (fun z=>¬FixedInducingRow η (internalQ Q η₀) m A z)
      (fun z=>‖f z‖^2)).symm


-- @@ L47-67 verbatim
theorem internal_exceptional_count (η η₀ : Character) (Q : Ideal O)
    (hQ0 : Q≠0) (hQ : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)})
    (m A : O) (hm : m≠0) (hA : A≠0) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (rows : Finset O) (hrows : ∀z∈rows,z≠0)
    (D : Ideal O) (hD : Squarefree D)
    (hgood : ∀P∈normalizedFactors D,goodLambda∉P ∧ (2:O)∉P ∧
      IsCoprime Q P ∧ IsCoprime η₀.modulus P ∧ IsCoprime η.modulus P ∧ valuation (Ideal.span {A}) P%6=2)
    (Z C M F : ℝ) (hZ : 0<Z) (hC : 0≤C)
    (hDnorm : Z^(F/2)≤(D.absNorm:ℝ))
    (hN : ∀z∈rows,((Ideal.span {z}).absNorm:ℝ)≤C*Z^M) :
    ((rows.filter (fun z=>FixedInducingRow η (internalQ Q η₀) m A z)).card:ℝ)≤
      768*(6:ℝ)^(normalizedFactors (internalQ Q η₀)).toFinset.card*C^(1/6:ℝ)*Z^((M-2*F)/6) := by
  apply fixed_support_exceptional_count η (internalQ Q η₀) (internalQ_ne_zero Q hQ0 η₀)
    (internalQ_ne_top Q hQ η₀) (inf_le_left.trans hQ72) m A hm hA hmLam hm2
    (rows.filter (fun z=>FixedInducingRow η (internalQ Q η₀) m A z))
    (fun z hz=>hrows z (Finset.mem_filter.mp hz).1)
    (fun z hz=>(Finset.mem_filter.mp hz).2) D hD ?_ Z C M F hZ hC hDnorm
    (fun z hz=>hN z (Finset.mem_filter.mp hz).1)
  intro P hP
  obtain ⟨hLam,h2,hQP,hη₀,hη,hv⟩:=hgood P hP
  exact ⟨hLam,h2,internalQ_coprime Q P η₀ hQP hη₀,hη,hv⟩


-- @@ L69-69 verbatim
variable (M : Ideal O) [NeZero M]

-- @@ L70-70 verbatim
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L71-71 verbatim
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)


-- @@ L73-79 verbatim
theorem internal_sector_nonprincipal {η : Character} {z : O} (F : NaturalRow η z)
    (η₀ : Character) (θ : RayQuotient.Characters M H) (Q R : Ideal O)
    (hQM : Q≤M) (hR : R≠0) (hz : z≠0)
    (hex : ¬FixedInducingRow η (internalQ Q η₀) (CenteredMomentSecondHeightFamily.fixedBadMask*idealGenerator R) 1 z) :
    (F.character.product (relativeCharacter M H hH η₀ θ)).residue≠1 :=
  sector_nonprincipal M H hH F η₀ θ (internalQ Q η₀) R
    (inf_le_left.trans hQM) inf_le_right hR hz hex


-- @@ L81-81 verbatim
end SevenEighths.CenteredMomentNaturalFixedRaySource


-- @@ L83-83 verbatim
end


-- @@ L85-85 verbatim
end OAI
