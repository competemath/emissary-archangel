import OAI.NumberTheory.DirichletL.Descent.CanonicalRankExistenceData


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L8-8 verbatim
namespace SevenEighths.InverseMoment

-- @@ L9-9 verbatim
open ActualEisensteinCubic CanonicalQuadraticSieve InverseInitialClippedColumns

-- @@ L10-10 verbatim
local notation "O"=>ActualEisensteinCubic.O


-- @@ L12-24 verbatim
theorem canonical_rank_loss_le {ι σ:Type}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M F z c eps eps' A:ℝ)(K degree:ℕ)
    (hZ:1≤Z)(hA:0≤A)(he:eps≤eps')
    (h:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps A K degree):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps' A K degree :=by
  intro Ψ hΨ m hm N V Mr Q hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  apply (h Ψ hΨ m hm N V Mr Q hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels s).trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) hA


-- @@ L26-26 verbatim
end SevenEighths.InverseMoment


-- @@ L28-28 verbatim
end


-- @@ L30-30 verbatim
end OAI
