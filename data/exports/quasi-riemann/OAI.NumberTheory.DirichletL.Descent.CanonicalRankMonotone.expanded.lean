import OAI.NumberTheory.DirichletL.Descent.CanonicalRankMoments


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L8-8 verbatim
namespace SevenEighths.InverseMoment

-- @@ L9-9 verbatim
open ActualEisensteinCubic CanonicalQuadraticSieve InverseInitialClippedColumns

-- @@ L10-10 verbatim
local notation "O"=>ActualEisensteinCubic.O

-- @@ L11-11 verbatim
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]

-- @@ L12-12 verbatim
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]

-- @@ L13-13 verbatim
variable (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))

-- @@ L14-14 verbatim
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})


-- @@ L16-22 verbatim
omit [DecidableEq σ] in
theorem canonical_rank_negative (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z Mmax Fcap z c eps A:ℝ)(K degree:ℕ)(hM:Mmax<0):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z Mmax Fcap z c eps A K degree :=by
  intro Ψ hΨ m hm N V M Qwidth hN hV hM0 hQ hMc
  exfalso
  linarith


-- @@ L24-34 verbatim
omit [DecidableEq σ] in
theorem canonical_rank_restrict (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M₁ M₂ F₁ F₂ z c₁ c₂ eps A:ℝ)(K degree:ℕ)
    (hM:M₁≤M₂)(hF:F₁≤F₂)(hc:c₂≤c₁)
    (h:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M₂ F₂ z c₂ eps A K degree):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M₁ F₁ z c₁ eps A K degree :=by
  intro Ψ hΨ m hm N V M Qwidth hN hV hM0 hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  have hmarg:CanonicalMargins (N+V) M Qwidth z c₂:=by
    unfold CanonicalMargins at *
    constructor <;> linarith [hmargin.1,hmargin.2]
  exact h Ψ hΨ m hm N V M Qwidth hN hV hM0 hQ (hMc.trans hM) (hFc.trans hF) hmarg hnorm ss hss labels hlabels s


-- @@ L36-49 verbatim
omit [DecidableEq σ] in
theorem canonical_rank_height_constant (pool:Finset ι)(base:O→*ℂ)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M F z c eps A B:ℝ)(K degree J:ℕ)
    (hZ:0<Z)(hA:0≤A)(hAB:A≤B)(hJ:degree≤J)
    (h:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps A K degree):
    CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps B K J :=by
  intro Ψ hΨ m hm N V Mr Qwidth hN hV hM0 hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  apply (h Ψ hΨ m hm N V Mr Qwidth hN hV hM0 hQ hMc hFc hmargin hnorm ss hss labels hlabels s).trans
  have hB:0≤B:=hA.trans hAB
  apply mul_le_mul
  · exact mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg hZ.le _)
  · exact pow_le_pow_right₀ (by linarith [norm_nonneg s]) (Nat.mul_le_mul_left 2 hJ)
  · positivity
  · positivity


-- @@ L51-51 verbatim
end SevenEighths.InverseMoment


-- @@ L53-53 verbatim
end


-- @@ L55-55 verbatim
end OAI
