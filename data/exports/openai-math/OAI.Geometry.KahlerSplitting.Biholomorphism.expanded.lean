import OAI.Geometry.KahlerSplitting.PathLifts


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
section


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open Set Filter Topology

-- @@ L9-9 verbatim
open scoped Manifold ContDiff

-- @@ L10-10 verbatim
namespace UniversalCoverSplitting

-- @@ L11-11 verbatim
namespace ProductRetracts

-- @@ L12-15 verbatim
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z} {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}
    [CompactSpace X.Carrier] (g : KahlerMetric X) (P : ProductRetracts π o h₁ h₂)


-- @@ L17-41 verbatim
lemma pair_homeomorph :
    ∃ Φ : Z.Carrier ≃ₜ (P.Y₁.Carrier × P.Y₂.Carrier), (Φ : Z.Carrier → _)=P.pair g := by
  let := π.connected
  let := P.simplyConnected_first g
  let := P.simplyConnected_second g
  let : SimplyConnectedSpace (P.Y₁.Carrier × P.Y₂.Carrier) := simplyConnected_product
  let : LocallyPathConnectedSpace P.Y₁.Carrier := ChartedSpace.locallyPathConnectedSpace (Model r) P.Y₁.Carrier
  let : LocallyPathConnectedSpace P.Y₂.Carrier := ChartedSpace.locallyPathConnectedSpace (Model s) P.Y₂.Carrier
  let f : C(P.Y₁.Carrier × P.Y₂.Carrier,P.Y₁.Carrier × P.Y₂.Carrier) := ContinuousMap.id _
  have hp := P.pair_isLocalHomeomorph g
  have hsep := T2Space.isSeparatedMap (P.pair g)
  obtain ⟨F,⟨hF0,hFl⟩,_⟩ := _root_.OAI.IsLocalHomeomorph.lift_of_simplyConnected hp hsep f (P.pair g o) o rfl
    (fun γ hγ ↦ P.pair_path_lift g o γ hγ)
  have hleft : (F : _ → Z.Carrier) ∘ P.pair g=id := by
    refine hsep.eq_of_comp_eq hp.isLocallyInjective (F.continuous.comp hp.continuous) continuous_id ?_ o hF0
    funext z
    exact congrFun hFl (P.pair g z)
  let Φ : Z.Carrier ≃ₜ (P.Y₁.Carrier × P.Y₂.Carrier) :=
    { toFun := P.pair g
      invFun := F
      left_inv := congrFun hleft
      right_inv := congrFun hFl
      continuous_toFun := hp.continuous
      continuous_invFun := F.continuous }
  exact ⟨Φ,rfl⟩


-- @@ L43-57 verbatim
lemma pair_biholomorph :
    ∃ Φ : Z.Carrier ≃ₜ (P.Y₁.Carrier × P.Y₂.Carrier), (Φ : Z.Carrier → _)=P.pair g ∧
      MDifferentiable (model n) ((model r).prod (model s)) Φ ∧
      MDifferentiable ((model r).prod (model s)) (model n) Φ.symm := by
  obtain ⟨Φ,hΦ⟩ := P.pair_homeomorph g
  refine ⟨Φ,hΦ,by rw [hΦ]; exact P.pair_holomorphic g,?_⟩
  intro y
  obtain ⟨e,he,heq,hd⟩ := P.pair_local_chart g (Φ.symm y)
  have hye : e (Φ.symm y)=y := (heq he).trans (by rw [←hΦ]; exact Φ.apply_symm_apply y)
  have ht : y ∈ e.target := hye ▸ e.map_source he
  have hi := hd.mdifferentiableAt_symm ht
  apply hi.congr_of_eventuallyEq
  filter_upwards [Φ.symm.continuous.continuousAt (e.open_source.mem_nhds he)] with w hw
  have hew : e (Φ.symm w)=w := (heq hw).trans (by rw [←hΦ]; exact Φ.apply_symm_apply w)
  exact (e.left_inv hw).symm.trans (congrArg e.symm hew)


-- @@ L59-59 verbatim
end ProductRetracts

-- @@ L60-60 verbatim
end UniversalCoverSplitting

-- @@ L61-61 verbatim
end

-- @@ L62-62 verbatim
end


-- @@ L64-64 verbatim
section


-- @@ L66-66 verbatim
noncomputable section

-- @@ L67-67 verbatim
open Set Filter Topology

-- @@ L68-68 verbatim
open scoped Manifold

-- @@ L69-69 verbatim
namespace UniversalCoverSplitting

-- @@ L70-71 verbatim
variable {n r s : ℕ} {X Z : ComplexManifold n} {S : HolomorphicSplitting X r s}
    {π : OrdinaryUniversalCover X Z}


-- @@ L73-88 verbatim
lemma CoverProductChart.derivative_down (e : CoverProductChart π S) {z : Z.Carrier}
    (hz : z ∈ e.chart.source) (v : Tangent Z z) :
    mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart z v=
      mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.downstairs.chart (π.projection z)
        (mfderiv (model n) (model n) π.projection z v) := by
  have heq : (e.chart : Z.Carrier → _) =ᶠ[𝓝 z] e.downstairs.chart ∘ π.projection := by
    filter_upwards [e.chart.open_source.mem_nhds hz] with w hw
    exact e.coordinates w hw
  have H := mfderiv_comp (I := model n) (I' := model n) (I'' := 𝓘(ℂ,Model r × Model s)) z
    (e.downstairs.holomorphic.mdifferentiableAt (e.downstairs.chart.open_source.mem_nhds (e.maps hz)))
    (π.liftedComplexStructure.mdifferentiable z)
  have hderiv : mfderiv (model n) 𝓘(ℂ,Model r × Model s) e.chart z =
      mfderiv (model n) 𝓘(ℂ,Model r × Model s) (e.downstairs.chart ∘ π.projection) z :=
    heq.mfderiv_eq
  rw [←hderiv] at H
  exact congrArg (fun L : Model n →L[ℂ] (Model r × Model s) ↦ L v) H


-- @@ L90-90 verbatim
namespace ProductRetracts

-- @@ L91-93 verbatim
variable {o : Z.Carrier}
    {h₁ : Integrable S.projection} {h₂ : Integrable (complementaryProjection S)}
    [CompactSpace X.Carrier] (g : KahlerMetric X) (P : ProductRetracts π o h₁ h₂)


-- @@ L95-101 verbatim
lemma first_kernel (z : Z.Carrier) (v : Tangent Z z) :
    mfderiv (model n) (model r) (P.q₁ g) z v=0 ↔
      S.projection (π.projection z) (mfderiv (model n) (model n) π.projection z v)=0 := by
  obtain ⟨e,hz,_⟩ := exists_coverProductChart π S h₁ h₂ z
  rw [e.factor_kernel (P.q₁_holomorphic g) (P.q₁_factor g e) hz (P.q₁_submersion g z) v,
    e.derivative_down hz v]
  exact (e.downstairs.vertical _ (e.maps hz) _).symm


-- @@ L103-110 verbatim
lemma second_kernel (z : Z.Carrier) (v : Tangent Z z) :
    mfderiv (model n) (model s) (P.q₂ g) z v=0 ↔
      S.projection (π.projection z) (mfderiv (model n) (model n) π.projection z v)=
        mfderiv (model n) (model n) π.projection z v := by
  obtain ⟨e,hz,_⟩ := exists_coverProductChart π S h₁ h₂ z
  rw [e.swap.factor_kernel (P.q₂_holomorphic g) (P.q₂_factor g e) hz (P.q₂_submersion g z) v,
    e.swap_derivative hz v,e.derivative_down hz v]
  exact (e.downstairs.horizontal _ (e.maps hz) _).symm


-- @@ L112-140 verbatim
lemma first_tangent (z : Z.Carrier) :
    Submodule.map (mfderiv (model n) ((model r).prod (model s)) (P.pair g) z).toLinearMap
      (Submodule.comap (mfderiv (model n) (model n) π.projection z).toLinearMap
        (LinearMap.range (S.projection (π.projection z)).toLinearMap)) =
      LinearMap.ker (ContinuousLinearMap.snd ℂ (Model r) (Model s)).toLinearMap := by
  have hd := mfderiv_prodMk (P.q₁_holomorphic g z) (P.q₂_holomorphic g z)
  change mfderiv (model n) ((model r).prod (model s)) (P.pair g) z=_ at hd
  have hmem (v : Tangent Z z) :
      mfderiv (model n) (model n) π.projection z v ∈ LinearMap.range (S.projection (π.projection z)).toLinearMap ↔
      mfderiv (model n) (model s) (P.q₂ g) z v=0 := by
    rw [P.second_kernel g]
    constructor
    · rintro ⟨w,hw⟩
      rw [←hw]
      exact S.idempotent _ _
    · intro h
      exact ⟨_,h⟩
  ext w
  constructor
  · rintro ⟨v,hv,rfl⟩
    change (mfderiv (model n) ((model r).prod (model s)) (P.pair g) z v).2=0
    rw [hd]
    exact (hmem v).mp hv
  · intro hw
    obtain ⟨v,hv⟩ := (P.pair_derivative_bijective g z).2 w
    refine ⟨v,(hmem v).mpr ?_,hv⟩
    change w.2=0 at hw
    rw [←hv,hd] at hw
    exact hw


-- @@ L142-160 verbatim
lemma second_tangent (z : Z.Carrier) :
    Submodule.map (mfderiv (model n) ((model r).prod (model s)) (P.pair g) z).toLinearMap
      (Submodule.comap (mfderiv (model n) (model n) π.projection z).toLinearMap
        (LinearMap.ker (S.projection (π.projection z)).toLinearMap)) =
      LinearMap.ker (ContinuousLinearMap.fst ℂ (Model r) (Model s)).toLinearMap := by
  have hd := mfderiv_prodMk (P.q₁_holomorphic g z) (P.q₂_holomorphic g z)
  change mfderiv (model n) ((model r).prod (model s)) (P.pair g) z=_ at hd
  ext w
  constructor
  · rintro ⟨v,hv,rfl⟩
    change (mfderiv (model n) ((model r).prod (model s)) (P.pair g) z v).1=0
    rw [hd]
    exact (P.first_kernel g z v).mpr hv
  · intro hw
    obtain ⟨v,hv⟩ := (P.pair_derivative_bijective g z).2 w
    refine ⟨v,(P.first_kernel g z v).mp ?_,hv⟩
    change w.1=0 at hw
    rw [←hv,hd] at hw
    exact hw


-- @@ L162-162 verbatim
end ProductRetracts

-- @@ L163-163 verbatim
end UniversalCoverSplitting

-- @@ L164-164 verbatim
end

-- @@ L165-165 verbatim
end


-- @@ L167-167 verbatim
end OAI
