import OAI.NumberTheory.DirichletL.Descent.CanonicalRankPuncture
import OAI.NumberTheory.DirichletL.Descent.CanonicalRankMonotone


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L9-9 verbatim
namespace SevenEighths.InverseMoment

-- @@ L10-10 verbatim
open ActualEisensteinCubic CanonicalCoefficientClass InverseTerminalWidths

-- @@ L11-11 verbatim
open ConcretePrimeRowBridge CompletedGauss

-- @@ L12-12 verbatim
local notation "O"=>ActualEisensteinCubic.O


-- @@ L14-25 verbatim
theorem actual_rank_family_period (q:ℕ)(base Ψ:O→*ℂ)
    (hbase:FactorsModulo (fixedBaseConductor q) base)
    (hΨ:IsBaseRayTwist base Ψ):
    FactorsModulo (fixedBaseConductor q) Ψ := by
  intro x y hxy
  rcases hΨ with rfl|⟨χ,rfl⟩
  · exact hbase x y hxy
  · simp only [MonoidHom.mul_apply]
    rw [hbase x y hxy]
    congr 1
    exact RayFourExpansion.rayCharacter_eq_of_mod_four χ x y
      (Ideal.mem_span_singleton.mp (Ideal.mul_le_right hxy))


-- @@ L27-32 verbatim
theorem actual_rank_family_gates (q:ℕ)(base:O→*ℂ)
    (hbase:∀x,‖base x‖≤1)(hperiod:FactorsModulo (fixedBaseConductor q) base):
    ∀Ψ:O→*ℂ,IsBaseRayTwist base Ψ→
      (∀x,‖Ψ x‖≤1) ∧ FactorsModulo (fixedBaseConductor q) Ψ := by
  intro Ψ hΨ
  exact ⟨hΨ.norm_le hbase,actual_rank_family_period q base Ψ hperiod hΨ⟩


-- @@ L34-38 verbatim
theorem actual_rank_norm_width (m:O)(Z Q:ℝ)(hZ:1<Z)
    (hn:‖ConcreteTraceCRT.eisEmbedding m‖^2=Z^Q):
    normWidth Z (Ideal.span {m})=Q := by
  rw [eisEmbedding_norm_sq_eq_absNorm_span] at hn
  rw [normWidth,hn,Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)]


-- @@ L40-57 verbatim
theorem actual_rank_state_gates (m:O)(hm:m≠0)(Z N V M Q z c L:ℝ)
    (hZ:1<Z)(hN:0≤N)(hV:0≤V)(hM:0≤M)(hQ:0≤Q)(hz:0≤z)(hc:0≤c)
    (hcap:N+V≤L)(hmargin:CanonicalMargins (N+V) M Q z c)
    (hn:‖ConcreteTraceCRT.eisEmbedding m‖^2=Z^Q):
    N≤L ∧ V≤L ∧ M≤N+V ∧ Q≤L ∧ z≤L ∧
      normWidth Z (Ideal.span {m})=Q ∧
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z c ∧
      (Ideal.absNorm (Ideal.span {m}:Ideal O):ℝ)≤Z^L ∧
      (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Q := by
  have hfirst:=hmargin.1
  have hQcap:Q≤L:=by linarith
  have he:=actual_rank_norm_width m Z Q hZ hn
  refine ⟨by linarith,by linarith,by linarith,hQcap,by linarith,he,?_,?_,?_⟩
  · rwa [he]
  · rw [eisEmbedding_norm_sq_eq_absNorm_span] at hn
    rw [hn]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le hQcap
  · simpa only [he] using actual_rank_parent_puncture m hm Z hZ


-- @@ L59-69 verbatim
theorem canonical_rank_subslots {ι σ:Type}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(base:O→*ℂ)(slots subslots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (W:𝓢(ℝ,ℂ))(Z M F z c eps A:ℝ)(K degree:ℕ)(hsub:subslots⊆slots)
    (h:CanonicalRankMoments p hp hcop hg pool base slots lists a W Z M F z c eps A K degree):
    CanonicalRankMoments p hp hcop hg pool base subslots lists a W Z M F z c eps A K degree := by
  intro Ψ hΨ m hm N V Mr Qwidth hN hV hM hQ hMc hFc hmargin hnorm ss hss labels hlabels s
  exact h Ψ hΨ m hm N V Mr Qwidth hN hV hM hQ hMc hFc hmargin hnorm ss
    (hss.trans hsub) labels hlabels s


-- @@ L71-77 verbatim
theorem canonical_rank_subslot_product {σ:Type*}[DecidableEq σ]
    (slots subslots:Finset σ)(H:σ→ℝ)(hsub:subslots⊆slots)
    (hH:∀i∈slots,1≤H i):
    (∏i∈subslots,H i)≤∏i∈slots,H i :=
  Finset.prod_le_prod_of_subset_of_one_le₀ hsub
    (fun i hi=>(zero_le_one: (0:ℝ)≤1).trans (hH i (hsub hi)))
    (fun i hi _=>hH i hi)


-- @@ L79-83 verbatim
theorem canonical_rank_subslot_cap {σ:Type*}[DecidableEq σ]
    (slots subslots:Finset σ)(H:σ→ℝ)(Z z:ℝ)(hsub:subslots⊆slots)
    (hH:∀i∈slots,1≤H i)(hcap:(∏i∈slots,H i)≤Z^z):
    (∏i∈subslots,H i)≤Z^z :=
  (canonical_rank_subslot_product slots subslots H hsub hH).trans hcap


-- @@ L85-85 verbatim
end SevenEighths.InverseMoment


-- @@ L87-87 verbatim
end


-- @@ L89-89 verbatim
end OAI
