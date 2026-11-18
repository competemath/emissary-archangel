import OAI.NumberTheory.DirichletL.Inversion.InitialOverlap


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators Classical

-- @@ L8-8 verbatim
open ActualEisensteinCubic CanonicalQuadraticSieve IdealMobiusDivisorSum UniqueFactorizationMonoid

-- @@ L9-9 verbatim
namespace SevenEighths.InverseInitialExcludedSource

-- @@ L10-10 verbatim
open InverseInitialOverlap

-- @@ L11-11 verbatim
local notation "O"=>ActualEisensteinCubic.O


-- @@ L13-14 verbatim
def columns (S:Finset (Ideal O))(P j:Ideal O):Finset (Ideal O):=
  (original S P j).image (idealQuotient j)


-- @@ L16-21 verbatim
theorem quotient_properties {P j n:Ideal O}(hn:Squarefree n)(hg:gcd n P=j):
    Squarefree (idealQuotient j n) ∧ IsCoprime (idealQuotient j n) P ∧
      j*idealQuotient j n=n := by
  have hjn:j∣n:=hg ▸ GCDMonoid.gcd_dvd_left n P
  exact ⟨hn.squarefree_of_dvd (idealQuotient_dvd hjn),by
    rw [←hg];exact squarefree_quotient_gcd_coprime n P hn,idealQuotient_mul hjn⟩


-- @@ L23-27 verbatim
theorem reconstruct_properties {P j c:Ideal O}(hP:Squarefree P)(hj:j∣P)
    (hc:Squarefree c)(hcp:IsCoprime c P):
    Squarefree (j*c) ∧ gcd (j*c) P=j := by
  exact ⟨squarefree_mul_iff.mpr ⟨(hcp.mono (dvd_refl _) hj).symm.isRelPrime,
    hP.squarefree_of_dvd hj,hc⟩,gcd_mul_of_coprime_divisor j c P hj hcp⟩


-- @@ L29-41 verbatim
theorem mem_columns {S:Finset (Ideal O)}{P j c:Ideal O}
    (hP:Squarefree P)(hj:j∣P):
    c∈columns S P j ↔ Squarefree c ∧ IsCoprime c P ∧ j*c∈S := by
  constructor
  · intro hc
    obtain ⟨n,hn,rfl⟩:=Finset.mem_image.mp hc
    obtain ⟨hnS,hns,hng⟩:=mem_original.mp hn
    obtain ⟨hcs,hcp,he⟩:=quotient_properties hns hng
    exact ⟨hcs,hcp,he.symm ▸ hnS⟩
  · rintro ⟨hcs,hcp,hnS⟩
    obtain ⟨hns,hng⟩:=reconstruct_properties hP hj hcs hcp
    refine Finset.mem_image.mpr ⟨j*c,mem_original.mpr ⟨hnS,hns,hng⟩,?_⟩
    exact quotient_mul_cancel (ne_zero_of_dvd_ne_zero hP.ne_zero hj)


-- @@ L43-53 verbatim
theorem sum_reconstruct (S:Finset (Ideal O)){P j:Ideal O}
    (_hP:Squarefree P)(_hj:j∣P)(f:Ideal O→ℂ):
    (∑n∈original S P j,f n)=∑c∈columns S P j,f (j*c) := by
  rw [columns,Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro n hn
    rw [(quotient_properties (mem_original.mp hn).2.1 (mem_original.mp hn).2.2).2.2]
  · intro n hn n' hn' he
    have h1:=(quotient_properties (mem_original.mp hn).2.1 (mem_original.mp hn).2.2).2.2
    have h2:=(quotient_properties (mem_original.mp hn').2.1 (mem_original.mp hn').2.2).2.2
    rw [←h1,←h2,he]


-- @@ L55-58 verbatim
theorem cutoff_argument (j c:Ideal O)(X:ℝ):
    ((j*c).absNorm:ℝ)/X=(c.absNorm:ℝ)/(X/(j.absNorm:ℝ)) := by
  rw [map_mul,Nat.cast_mul,div_div_eq_mul_div]
  ring


-- @@ L60-64 verbatim
theorem coefficient_identity (ψ:Ideal O→*ℂ){P j c:Ideal O}
    (hj:j∣P)(hcp:IsCoprime c P):
    (moebius (j*c):ℂ)*ψ (j*c)=(moebius j:ℂ)*ψ j*((moebius c:ℂ)*ψ c) := by
  rw [((hcp.mono (dvd_refl _) hj).symm.isRelPrime).moebius_mul,Int.cast_mul,map_mul]
  ring


-- @@ L66-75 verbatim
theorem polynomial_slice (S:Finset (Ideal O)){P j:Ideal O}
    (hP:Squarefree P)(hj:j∣P)(ψ:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(X:ℝ):
    (∑n∈original S P j,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X))=
    ((moebius j:ℂ)*ψ j)*∑c∈columns S P j,(moebius c:ℂ)*ψ c*a (j*c)*
      W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
  rw [sum_reconstruct S hP hj,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  rw [coefficient_identity ψ hj ((mem_columns hP hj).mp hc).2.1,cutoff_argument]
  ring


-- @@ L77-94 verbatim
theorem polynomial_decomposition (S:Finset (Ideal O)){P:Ideal O}(hP:Squarefree P)
    (ψ:Ideal O→*ℂ)(a:Ideal O→ℂ)(W:ℝ→ℂ)(X:ℝ):
    (∑n∈S,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X))=
    ∑j∈idealDivisors P,((moebius j:ℂ)*ψ j)*
      ∑c∈columns S P j,(moebius c:ℂ)*ψ c*a (j*c)*
        W ((c.absNorm:ℝ)/(X/(j.absNorm:ℝ))) := by
  have hs:(∑n∈S,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X))=
      ∑n∈S.filter Squarefree,(moebius n:ℂ)*ψ n*a n*W ((n.absNorm:ℝ)/X) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hs:Squarefree n
    · rw [ite_eq_left hs]
    · simp only [ite_eq_right hs,moebius_of_not_squarefree hs,Int.cast_zero,zero_mul]
  rw [hs,sum_original_partition S hP]
  apply Finset.sum_congr rfl
  intro j hj
  exact polynomial_slice S hP ((mem_idealDivisors hP.ne_zero).mp hj) ψ a W X


-- @@ L96-96 verbatim
end SevenEighths.InverseInitialExcludedSource


-- @@ L98-98 verbatim
end


-- @@ L100-100 verbatim
end OAI
