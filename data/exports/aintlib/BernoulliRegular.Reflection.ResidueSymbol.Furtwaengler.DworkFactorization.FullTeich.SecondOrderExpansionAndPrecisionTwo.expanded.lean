module

public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.Concrete
public import BernoulliRegular.Reflection.ResidueSymbol.Furtwaengler.DworkFactorization.FullTeich.TraceCarryRecursionAndConstructors


-- @@ L6-10 verbatim
/-!
# Full Teichmuller Dwork product setup

Split from `DworkFactorization.lean`.
-/


-- @@ L12-12 verbatim
@[expose] public section


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
open scoped NumberField


-- @@ L18-18 verbatim
namespace BernoulliRegular


-- @@ L20-20 verbatim
namespace Furtwaengler


-- @@ L22-22 verbatim
universe u v w


-- @@ L24-24 verbatim
namespace FullTeichStickelbergerSetup


-- @@ L26-26 verbatim
variable {ℓ p : ℕ} [Fact (Nat.Prime ℓ)] [Fact (Nat.Prime p)]

-- @@ L27-27 verbatim
variable {k : Type u} [Field k] [Fintype k] [Algebra (ZMod ℓ) k]

-- @@ L28-28 verbatim
variable {K : Type v} [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]

-- @@ L29-30 verbatim
variable {R' : Type w} [Field R'] [NumberField R'] [Algebra K R'] [IsScalarTower ℚ K R']
  [IsCyclotomicExtension {p, ℓ} ℚ R']


-- @@ L32-32 verbatim
variable (F : FullTeichStickelbergerSetup ℓ p k K R')


-- @@ L34-96 verbatim
/-- Second-order expansion of the precision-indexed Artin-Hasse theta product
before comparing with the trace-binomial expression. -/
theorem artinHasseThetaTruncProductAtTo_two_sub_secondOrderTeichExpansion_mem_Q_cubed
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (hγπ : γ - F.π ∈ F.Q ^ 2) (y : kˣ) :
    let u : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R' := fun i =>
      (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
    let a : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R' := fun i => F.π * u i
    let b : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R' := fun i =>
      (γ - F.π) * u i + dworkCoeffArtinHasseAtTo F.toConcreteStickelbergerSetup γ 2 2 *
        u i ^ 2
    artinHasseThetaTruncProductAtTo F γ 2 y -
        (1 + (∑ i : Fin F.toConcreteStickelbergerSetup.f, a i) +
          (∑ i : Fin F.toConcreteStickelbergerSetup.f, b i) +
          ∑ i : Fin F.toConcreteStickelbergerSetup.f,
            a i * ∑ j ∈ Finset.univ.filter (fun j => j < i), a j) ∈
      F.Q ^ 3 := by
  dsimp only
  let S0 : ConcreteStickelbergerSetup ℓ p k K R' :=
    F.toConcreteStickelbergerSetup
  let u : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R' := fun i =>
    (F.teichUnitFullVal (F.traceScale * y)) ^ (ℓ ^ (i : ℕ))
  let a : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R' := fun i => F.π * u i
  let b : Fin F.toConcreteStickelbergerSetup.f → 𝓞 R' := fun i =>
    (γ - F.π) * u i + dworkCoeffArtinHasseAtTo S0 γ 2 2 * u i ^ 2
  have ha : ∀ i ∈ (Finset.univ : Finset (Fin F.toConcreteStickelbergerSetup.f)),
      a i ∈ F.Q := fun i _hi =>
    Ideal.mul_mem_right _ _ F.π_mem_Q
  have hb : ∀ i ∈ (Finset.univ : Finset (Fin F.toConcreteStickelbergerSetup.f)),
      b i ∈ F.Q ^ 2 := by
    intro i _hi
    exact (F.Q ^ 2).add_mem (Ideal.mul_mem_right _ _ hγπ)
      (Ideal.mul_mem_right _ _ (dworkCoeffArtinHasseAtTo_mem_Q_pow S0 hγ 2 2))
  have hfactor :
      (∏ i : Fin F.toConcreteStickelbergerSetup.f, artinHasseThetaFactorAtTo F γ 2 y i) -
          (∏ i : Fin F.toConcreteStickelbergerSetup.f, (1 + a i + b i)) ∈
        F.Q ^ 3 :=
    fin_prod_sub_prod_mem_pow (I := F.Q)
      (fun i : Fin F.toConcreteStickelbergerSetup.f => artinHasseThetaFactorAtTo F γ 2 y i)
      (fun i : Fin F.toConcreteStickelbergerSetup.f => (1 + a i + b i)) 3
      (fun i =>
        by
          have hi :=
            S0.dworkThetaTrunc_artinHasseAtTo_two_sub_one_add_linear_quadratic_mem_Q_cubed
              γ (u i)
          simpa [artinHasseThetaFactorAtTo, a, b, u, S0, add_assoc] using hi)
  have hproduct :
      (∏ i : Fin F.toConcreteStickelbergerSetup.f, (1 + a i + b i)) -
          (1 + (∑ i : Fin F.toConcreteStickelbergerSetup.f, a i) +
            (∑ i : Fin F.toConcreteStickelbergerSetup.f, b i) +
            ∑ i : Fin F.toConcreteStickelbergerSetup.f,
              a i * ∑ j ∈ Finset.univ.filter (fun j => j < i), a j) ∈
        F.Q ^ 3 := by
    simpa using
      finset_prod_one_add_linear_quadratic_sub_mem_pow_three
        (I := F.Q) (s := (Finset.univ : Finset (Fin F.toConcreteStickelbergerSetup.f)))
        a b ha hb
  have htheta :
      artinHasseThetaTruncProductAtTo F γ 2 y -
          (∏ i : Fin F.toConcreteStickelbergerSetup.f, (1 + a i + b i)) ∈
        F.Q ^ 3 := by
    simpa [artinHasseThetaTruncProductAtTo, artinHasseThetaFactorAtTo,
      dworkThetaFrobeniusProduct, u] using hfactor
  exact sub_mem_trans (F.Q ^ 3) htheta hproduct


-- @@ L98-107 verbatim
/-- Definitional form of
`artinHasseThetaTruncProductAtTo_two_sub_secondOrderTeichExpansion_mem_Q_cubed`
using `artinHasseSecondOrderTeichExpansion`. -/
theorem artinHasseThetaTruncProductAtTo_two_sub_secondOrderTeichExpansion'_mem_Q_cubed
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (hγπ : γ - F.π ∈ F.Q ^ 2) (y : kˣ) :
    artinHasseThetaTruncProductAtTo F γ 2 y -
        artinHasseSecondOrderTeichExpansion F γ y ∈ F.Q ^ 3 := by
  simpa [artinHasseSecondOrderTeichExpansion] using
    F.artinHasseThetaTruncProductAtTo_two_sub_secondOrderTeichExpansion_mem_Q_cubed
      hγ hγπ y


-- @@ L109-131 verbatim
/-- Reduction of the precision-2 Dwork splitting check to the genuine
second-order trace/Teichmüller comparison. -/
theorem psiInt_sub_artinHasseThetaTruncProductAtTo_two_mem_Q_cubed_of_trace
    {γ : 𝓞 R'} (hγ : γ ∈ F.Q) (hγπ : γ - F.π ∈ F.Q ^ 2) (y : kˣ)
    (htrace :
      psiTraceBinomialApprox F 2 y - artinHasseSecondOrderTeichExpansion F γ y ∈
        F.Q ^ 3) :
    F.psiInt (y : k) - artinHasseThetaTruncProductAtTo F γ 2 y ∈ F.Q ^ 3 := by
  have hpsi :
      F.psiInt (y : k) - psiTraceBinomialApprox F 2 y ∈ F.Q ^ 3 := by
    simpa using F.psiInt_sub_traceBinomialApprox_mem_Q_pow_succ 2 y
  have htheta :
      artinHasseSecondOrderTeichExpansion F γ y -
          artinHasseThetaTruncProductAtTo F γ 2 y ∈ F.Q ^ 3 := by
    simpa [sub_eq_add_neg] using (F.Q ^ 3).neg_mem
      (F.artinHasseThetaTruncProductAtTo_two_sub_secondOrderTeichExpansion'_mem_Q_cubed
        hγ hγπ y)
  rw [show F.psiInt (y : k) - artinHasseThetaTruncProductAtTo F γ 2 y =
      (F.psiInt (y : k) - psiTraceBinomialApprox F 2 y) +
        (psiTraceBinomialApprox F 2 y - artinHasseSecondOrderTeichExpansion F γ y) +
          (artinHasseSecondOrderTeichExpansion F γ y -
            artinHasseThetaTruncProductAtTo F γ 2 y) by ring]
  exact (F.Q ^ 3).add_mem ((F.Q ^ 3).add_mem hpsi htrace) htheta


-- @@ L133-133 verbatim
end FullTeichStickelbergerSetup


-- @@ L135-135 verbatim
end Furtwaengler


-- @@ L137-137 verbatim
end BernoulliRegular


-- @@ L139-139 verbatim
end
