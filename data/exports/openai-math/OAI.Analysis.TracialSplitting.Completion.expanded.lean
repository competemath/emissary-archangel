import OAI.Analysis.TracialSplitting.TensorNorms


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
universe uD uE uI uJ uX


-- @@ L9-9 verbatim
namespace Pureness


-- @@ L11-11 verbatim
open Filter


-- @@ L13-13 verbatim
open scoped Topology NNReal ENNReal


-- @@ L15-15 verbatim
namespace ClosedStarIdeal


-- @@ L17-17 verbatim
variable {D : Type uD} [CStarAlgebra D] (J : ClosedStarIdeal D)


-- @@ L19-20 verbatim
def quotientStarHom : D →⋆ₐ[ℂ] J.Quotient :=
  { J.quotientMap with map_star' := J.quotientMap_star }


-- @@ L22-25 verbatim
lemma quotientStarHom_continuous : Continuous (J.quotientStarHom) := by
  exact AddMonoidHomClass.continuous_of_bound J.quotientStarHom 1
    (fun element => by
      simpa only [quotientStarHom, StarAlgHom.coe_mk', one_mul] using J.quotientMap_norm_le element)


-- @@ L27-27 verbatim
end ClosedStarIdeal


-- @@ L29-29 verbatim
end Pureness


-- @@ L31-31 verbatim
namespace CurrentMain


-- @@ L33-33 verbatim
section


-- @@ L35-35 verbatim
open Pureness


-- @@ L37-37 verbatim
variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L39-39 verbatim
variable (τ : I → TracialState D) [Nonempty I]


-- @@ L41-41 verbatim
def familyTraceNorm (a : D) : ℝ := ⨆ i, ‖(τ i).functional a‖


-- @@ L43-45 verbatim
lemma familyTwoNorm_sub_le (a b : D) :
    familyTwoNorm τ (a - b) ≤ familyTwoNorm τ a + familyTwoNorm τ b := by
  simpa only [sub_eq_add_neg, familyTwoNorm_neg] using familyTwoNorm_add_le τ a (-b)


-- @@ L47-52 verbatim
lemma familyTwoNorm_smul_le (z : ℂ) (a : D) :
    familyTwoNorm τ (z • a) ≤ ‖z‖ * familyTwoNorm τ a := by
  apply ciSup_le
  intro i
  rw [traceTwoNorm_smul]
  exact mul_le_mul_of_nonneg_left (traceTwoNorm_le_family τ i a) (norm_nonneg z)


-- @@ L54-60 verbatim
@[simp] lemma familyTwoNorm_smul (z : ℂ) (a : D) :
    familyTwoNorm τ (z • a) = ‖z‖ * familyTwoNorm τ a := by
  apply le_antisymm (familyTwoNorm_smul_le τ z a)
  by_cases hz : z = 0
  · simp [hz]
  have hi := mul_le_mul_of_nonneg_left (familyTwoNorm_smul_le τ z⁻¹ (z • a)) (norm_nonneg z)
  simpa [smul_smul, hz, mul_assoc, norm_ne_zero_iff.mpr hz] using hi


-- @@ L62-73 verbatim
lemma familyTwoNorm_lipschitz : LipschitzWith 1 (familyTwoNorm τ) := by
  apply LipschitzWith.of_dist_le_mul
  intro a b
  rw [NNReal.coe_one, one_mul, Real.dist_eq]
  apply abs_le.mpr
  have hab := familyTwoNorm_sub_triangle τ a b 0
  have hba := familyTwoNorm_sub_triangle τ b a 0
  simp only [sub_zero] at hab hba
  have hm := familyTwoNorm_le_norm τ (a-b)
  rw [← familyTwoNorm_sub_swap τ a b] at hba
  rw [dist_eq_norm]
  constructor <;> linarith


-- @@ L75-77 verbatim
omit [Nonempty I] in
lemma familyTraceNorm_bdd (a : D) : BddAbove (Set.range (fun i => ‖(τ i).functional a‖)) :=
  ⟨‖a‖, by rintro _ ⟨i, rfl⟩; exact trace_norm_le_norm (τ i) a⟩


-- @@ L79-81 verbatim
omit [Nonempty I] in
lemma traceNorm_le_family (i : I) (a : D) :
    ‖(τ i).functional a‖ ≤ familyTraceNorm τ a := le_ciSup (familyTraceNorm_bdd τ a) i


-- @@ L83-85 verbatim
lemma familyTraceNorm_nonneg (a : D) : 0 ≤ familyTraceNorm τ a := by
  obtain ⟨i⟩ := ‹Nonempty I›
  exact (norm_nonneg _).trans (traceNorm_le_family τ i a)


-- @@ L87-90 verbatim
lemma familyTraceNorm_le_twoNorm (a : D) : familyTraceNorm τ a ≤ familyTwoNorm τ a := by
  apply ciSup_le
  intro i
  exact (trace_norm_le_twoNorm (τ i) a).trans (traceTwoNorm_le_family τ i a)


-- @@ L92-93 verbatim
lemma familyTraceNorm_le_norm (a : D) : familyTraceNorm τ a ≤ ‖a‖ :=
  (familyTraceNorm_le_twoNorm τ a).trans (familyTwoNorm_le_norm τ a)


-- @@ L95-95 verbatim
end


-- @@ L97-97 verbatim
open Pureness Filter


-- @@ L99-99 verbatim
open scoped Topology NNReal ENNReal


-- @@ L101-101 verbatim
variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L103-103 verbatim
variable (τ : I → TracialState D) [Nonempty I]


-- @@ L105-108 verbatim
omit [Nonempty I] in
lemma isFamilyCauchy_neg {u : ℕ → D} (hu : IsFamilyCauchy τ u) :
    IsFamilyCauchy τ (fun n => -u n) := by
  simpa only [IsFamilyCauchy, neg_sub_neg, neg_sub] using isFamilyNull_neg τ hu


-- @@ L110-110 verbatim
end CurrentMain


-- @@ L112-112 verbatim
namespace Pureness.ClosedStarIdeal


-- @@ L114-114 verbatim
open scoped ComplexOrder


-- @@ L116-116 verbatim
variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L118-118 verbatim
variable (J : ClosedStarIdeal D)


-- @@ L120-120 verbatim
variable (τ : TracialState D) (hτ : ∀ a ∈ J.ideal, τ.functional a = 0)


-- @@ L122-123 verbatim
lemma descendedTrace_map (u : D) :
    (J.descendedTrace τ hτ).functional (J.quotientMap u) = τ.functional u := rfl


-- @@ L125-125 verbatim
end Pureness.ClosedStarIdeal


-- @@ L127-127 verbatim
namespace CurrentMain


-- @@ L129-129 verbatim
section


-- @@ L131-131 verbatim
open Pureness Filter


-- @@ L133-133 verbatim
open scoped Topology NNReal ENNReal ComplexOrder


-- @@ L135-135 verbatim
section UltraTrace


-- @@ L137-137 verbatim
variable {D : Type uD} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]


-- @@ L139-139 verbatim
variable (θ : X → TracialState D) (U : Ultrafilter X)


-- @@ L141-144 verbatim
lemma ultraTrace_square_nonneg (u : lp (fun _ : X => D) ∞) :
    0 ≤ ultraTraceLinear θ U (star u*u) := by
  apply ge_of_tendsto (ultraTraceValue_tendsto θ U (star u*u))
  exact Eventually.of_forall (fun n => (θ n).functional.map_nonneg (star_mul_self_nonneg (u n)))


-- @@ L146-146 verbatim
end UltraTrace


-- @@ L148-148 verbatim
variable {D : Type uD} {I : Type uI} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]


-- @@ L150-150 verbatim
variable (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)


-- @@ L152-156 verbatim
lemma familyLimitTrace_tendsto (s : X → I) (u : lp (fun _ : X => D) ∞) :
    Tendsto (fun n => (τ (s n)).functional (u n)) (U : Filter X)
      (𝓝 ((familyLimitTrace τ U s).functional
        ((familyNullIdeal τ (U : Filter X)).quotientMap u))) :=
  ultraTraceValue_tendsto (fun n => τ (s n)) U u


-- @@ L158-158 verbatim
end


-- @@ L160-160 verbatim
section


-- @@ L162-162 verbatim
open Pureness Filter


-- @@ L164-164 verbatim
open scoped Topology NNReal ENNReal ComplexOrder


-- @@ L166-197 verbatim
lemma uniform_sup_ultralimit {X : Type uX} {I : Type uI} [Nonempty I]
    (U : Ultrafilter X) (f : X → I → ℝ) (M : ℝ)
    (h₀ : ∀ n i, 0 ≤ f n i) (hM : ∀ n i, f n i ≤ M) :
    (⨆ s : X → I, limUnder (U : Filter X) (fun n => f n (s n))) =
      limUnder (U : Filter X) (fun n => ⨆ i, f n i) := by
  have hb (n : X) : BddAbove (Set.range (f n)) := ⟨M, by rintro _ ⟨i,rfl⟩; exact hM n i⟩
  have hs₀ (n : X) : 0 ≤ ⨆ i, f n i := by
    obtain ⟨i⟩ := ‹Nonempty I›
    exact (h₀ n i).trans (le_ciSup (hb n) i)
  have hsM (n : X) : (⨆ i, f n i) ≤ M := ciSup_le (hM n)
  have ht (s : X → I) := bounded_ultrafilter_tendsto U (fun n => f n (s n)) M
    (fun n => by simpa only [Real.norm_eq_abs, abs_of_nonneg (h₀ n (s n))] using hM n (s n))
  have hst := bounded_ultrafilter_tendsto U (fun n => ⨆ i, f n i) M
    (fun n => by simpa only [Real.norm_eq_abs, abs_of_nonneg (hs₀ n)] using hsM n)
  have hbound : BddAbove (Set.range (fun s : X → I =>
      limUnder (U : Filter X) (fun n => f n (s n)))) := by
    refine ⟨M,?_⟩
    rintro _ ⟨s,rfl⟩
    exact le_of_tendsto (ht s) (Eventually.of_forall (fun n => hM n (s n)))
  apply le_antisymm
  · apply ciSup_le
    intro s
    exact le_of_tendsto_of_tendsto (ht s) hst
      (Eventually.of_forall (fun n => le_ciSup (hb n) (s n)))
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hex (n : X) : ∃ i, (⨆ j, f n j) - ε < f n i :=
      exists_lt_of_lt_ciSup (sub_lt_self _ hε)
    choose s hs using hex
    have hle := le_of_tendsto_of_tendsto hst ((ht s).add_const ε)
      (Eventually.of_forall (fun n => by linarith [hs n]))
    exact hle.trans (add_le_add (le_ciSup hbound s) le_rfl)


-- @@ L199-199 verbatim
variable {D : Type uD} {I : Type uI} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D] [Nontrivial D]


-- @@ L201-201 verbatim
variable (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)


-- @@ L203-209 verbatim
lemma familyQuotientMap_eq_zero (u : lp (fun _ : X => D) ∞) :
    (familyNullIdeal τ (U : Filter X)).quotientMap u = 0 ↔
      IsFamilyNull τ (U : Filter X) (fun n => u n) := by
  let J := familyNullIdeal τ (U : Filter X)
  change J.ideal.ringCon.mk' u = J.ideal.ringCon.mk' 0 ↔ _
  exact (show J.ideal.ringCon.mk' u = J.ideal.ringCon.mk' 0 ↔ u ∈ J.ideal from
    Quotient.eq).trans (familyNull_mem τ _ u)


-- @@ L211-218 verbatim
lemma traceTwoNorm_limitTrace_tendsto (s : X → I) (u : lp (fun _ : X => D) ∞) :
    Tendsto (fun n => traceTwoNorm (τ (s n)) (u n)) (U : Filter X)
      (𝓝 (traceTwoNorm (familyLimitTrace τ U s)
        ((familyNullIdeal τ (U : Filter X)).quotientMap u))) := by
  have ht := familyLimitTrace_tendsto τ U s (star u*u)
  rw [map_mul, ClosedStarIdeal.quotientMap_star] at ht
  exact Real.continuous_sqrt.continuousAt.tendsto.comp
    (Complex.continuous_re.continuousAt.tendsto.comp ht)


-- @@ L220-235 verbatim
lemma familyTwoNorm_limitTrace (u : lp (fun _ : X => D) ∞) :
    familyTwoNorm (familyLimitTrace τ U)
      ((familyNullIdeal τ (U : Filter X)).quotientMap u) =
      limUnder (U : Filter X) (fun n => familyTwoNorm τ (u n)) := by
  have he (s : X → I) : traceTwoNorm (familyLimitTrace τ U s)
      ((familyNullIdeal τ (U : Filter X)).quotientMap u) =
      limUnder (U : Filter X) (fun n => traceTwoNorm (τ (s n)) (u n)) := by
    exact tendsto_nhds_unique (traceTwoNorm_limitTrace_tendsto τ U s u)
      (bounded_ultrafilter_tendsto U _ ‖u‖ (fun n => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (traceTwoNorm_nonneg _ _)] using
          (traceTwoNorm_le_norm (τ (s n)) (u n)).trans
            (lp.norm_apply_le_norm ENNReal.top_ne_zero u n)))
  simp only [familyTwoNorm, he]
  exact uniform_sup_ultralimit U (fun n i => traceTwoNorm (τ i) (u n)) ‖u‖
    (fun _ _ => traceTwoNorm_nonneg _ _) (fun n i =>
      (traceTwoNorm_le_norm (τ i) (u n)).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero u n))


-- @@ L237-244 verbatim
lemma familyTwoNorm_limitTrace_tendsto (u : lp (fun _ : X => D) ∞) :
    Tendsto (fun n => familyTwoNorm τ (u n)) (U : Filter X)
      (𝓝 (familyTwoNorm (familyLimitTrace τ U)
        ((familyNullIdeal τ (U : Filter X)).quotientMap u))) := by
  rw [familyTwoNorm_limitTrace]
  exact bounded_ultrafilter_tendsto U _ ‖u‖ (fun n => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (familyTwoNorm_nonneg τ _)] using
      (familyTwoNorm_le_norm τ _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero u n))


-- @@ L246-260 verbatim
lemma familyTraceNorm_limitTrace (u : lp (fun _ : X => D) ∞) :
    familyTraceNorm (familyLimitTrace τ U)
      ((familyNullIdeal τ (U : Filter X)).quotientMap u) =
      limUnder (U : Filter X) (fun n => familyTraceNorm τ (u n)) := by
  have he (s : X → I) : ‖(familyLimitTrace τ U s).functional
      ((familyNullIdeal τ (U : Filter X)).quotientMap u)‖ =
      limUnder (U : Filter X) (fun n => ‖(τ (s n)).functional (u n)‖) := by
    exact tendsto_nhds_unique (familyLimitTrace_tendsto τ U s u).norm
      (bounded_ultrafilter_tendsto U _ ‖u‖ (fun n => by
        simpa only [norm_norm] using (trace_norm_le_norm (τ (s n)) (u n)).trans
          (lp.norm_apply_le_norm ENNReal.top_ne_zero u n)))
  simp only [familyTraceNorm, he]
  exact uniform_sup_ultralimit U (fun n i => ‖(τ i).functional (u n)‖) ‖u‖
    (fun _ _ => norm_nonneg _) (fun n i =>
      (trace_norm_le_norm (τ i) (u n)).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero u n))


-- @@ L262-269 verbatim
lemma familyTraceNorm_limitTrace_tendsto (u : lp (fun _ : X => D) ∞) :
    Tendsto (fun n => familyTraceNorm τ (u n)) (U : Filter X)
      (𝓝 (familyTraceNorm (familyLimitTrace τ U)
        ((familyNullIdeal τ (U : Filter X)).quotientMap u))) := by
  rw [familyTraceNorm_limitTrace]
  exact bounded_ultrafilter_tendsto U _ ‖u‖ (fun n => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (familyTraceNorm_nonneg τ _)] using
      (familyTraceNorm_le_norm τ _).trans (lp.norm_apply_le_norm ENNReal.top_ne_zero u n))


-- @@ L271-280 verbatim
lemma limitTrace_detects_zero (z : FamilyUltrapower τ U)
    (hz : ∀ s : X → I, traceTwoNorm (familyLimitTrace τ U s) z = 0) : z = 0 := by
  obtain ⟨u,rfl⟩ := (familyNullIdeal τ (U : Filter X)).quotientMap_surjective z
  apply (familyQuotientMap_eq_zero τ U u).mpr
  have ht := familyTwoNorm_limitTrace_tendsto τ U u
  have he : familyTwoNorm (familyLimitTrace τ U)
      ((familyNullIdeal τ (U : Filter X)).quotientMap u) = 0 := by
    simp only [familyTwoNorm, hz, ciSup_const]
  change Tendsto _ _ (𝓝 0)
  simpa only [he] using ht


-- @@ L282-282 verbatim
end


-- @@ L284-284 verbatim
open Pureness Filter


-- @@ L286-286 verbatim
open scoped Topology NNReal ENNReal ComplexOrder


-- @@ L288-288 verbatim
variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L290-290 verbatim
variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I]


-- @@ L292-295 verbatim
lemma completionTrace_tendsto (i : I) (u : familyCauchyAlgebra τ) :
    Tendsto (fun n : ℕ => (τ i).functional (u.1 n)) atTop
      (𝓝 ((completionTrace τ i).functional ((familyCauchyNullIdeal τ).quotientMap u))) :=
  cauchyTrace_tendsto τ i u


-- @@ L297-303 verbatim
lemma completionTwoNorm_tendsto (i : I) (u : familyCauchyAlgebra τ) :
    Tendsto (fun n : ℕ => traceTwoNorm (τ i) (u.1 n)) atTop
      (𝓝 (traceTwoNorm (completionTrace τ i) ((familyCauchyNullIdeal τ).quotientMap u))) := by
  have ht := completionTrace_tendsto τ i (star u*u)
  rw [map_mul, ClosedStarIdeal.quotientMap_star] at ht
  exact Real.continuous_sqrt.continuousAt.tendsto.comp
    (Complex.continuous_re.continuousAt.tendsto.comp ht)


-- @@ L305-307 verbatim
omit [Nontrivial D] [PartialOrder D] [StarOrderedRing D] in
@[simp] lemma boundedFamilyConstant_apply {X : Type uX} (a : D) (n : X) :
    boundedFamilyConstant a n = a := rfl


-- @@ L309-311 verbatim
lemma completionTrace_constant (i : I) (a : D) :
    (completionTrace τ i).functional (completionMap τ a) = (τ i).functional a :=
  tendsto_nhds_unique (completionTrace_tendsto τ i (cauchyConstant τ a)) tendsto_const_nhds


-- @@ L313-316 verbatim
lemma completionTwoNorm_constant (i : I) (a : D) :
    traceTwoNorm (completionTrace τ i) (completionMap τ a) = traceTwoNorm (τ i) a := by
  unfold traceTwoNorm
  rw [← map_star, ← map_mul, completionTrace_constant]


-- @@ L318-320 verbatim
lemma familyTwoNorm_completionMap (a : D) :
    familyTwoNorm (completionTrace τ) (completionMap τ a) = familyTwoNorm τ a := by
  simp only [familyTwoNorm, completionTwoNorm_constant]


-- @@ L322-335 verbatim
lemma completion_distance_tendsto_zero (u : familyCauchyAlgebra τ) :
    Tendsto (fun m : ℕ => familyTwoNorm (completionTrace τ)
      ((familyCauchyNullIdeal τ).quotientMap u - completionMap τ (u.1 m)))
      atTop (𝓝 0) := by
  apply (isFamilyNull_iff (completionTrace τ) atTop _).mpr
  intro ε hε
  obtain ⟨N,hN⟩ := (isFamilyCauchy_iff τ _).mp u.2 (ε/2) (by linarith)
  filter_upwards [eventually_ge_atTop N] with m hm
  refine lt_of_le_of_lt (ciSup_le fun i => ?_) (half_lt_self hε)
  have ht := completionTwoNorm_tendsto τ i (u-cauchyConstant τ (u.1 m))
  rw [map_sub] at ht
  apply le_of_tendsto ht
  filter_upwards [eventually_ge_atTop N] with n hn
  exact (traceTwoNorm_le_family τ i _).trans (hN n hn m hm).le


-- @@ L337-342 verbatim
theorem completion_uniform_dense (x : UniformTracialCompletion τ) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : D, familyTwoNorm (completionTrace τ) (x-completionMap τ a) < ε := by
  obtain ⟨u,rfl⟩ := (familyCauchyNullIdeal τ).quotientMap_surjective x
  obtain ⟨m,hm⟩ := ((isFamilyNull_iff (completionTrace τ) atTop _).mp
    (completion_distance_tendsto_zero τ u) ε hε).exists
  exact ⟨u.1 m,hm⟩


-- @@ L344-351 verbatim
lemma familyTwoNorm_abs_sub_le {E : Type uE} {J : Type uJ} [CStarAlgebra E] [PartialOrder E]
    [StarOrderedRing E] (σ : J → TracialState E) [Nonempty J] (a b : E) :
    |familyTwoNorm σ a - familyTwoNorm σ b| ≤ familyTwoNorm σ (a-b) := by
  have h₁ := familyTwoNorm_sub_triangle σ a b 0
  have h₂ := familyTwoNorm_sub_triangle σ b a 0
  simp only [sub_zero] at h₁ h₂
  rw [familyTwoNorm_sub_swap σ b a] at h₂
  exact abs_le.mpr ⟨by linarith,by linarith⟩


-- @@ L353-360 verbatim
lemma completion_uniformTwoNorm_tendsto (u : familyCauchyAlgebra τ) :
    Tendsto (fun n : ℕ => familyTwoNorm τ (u.1 n)) atTop
      (𝓝 (familyTwoNorm (completionTrace τ) ((familyCauchyNullIdeal τ).quotientMap u))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _)
    (fun n => ?_) (completion_distance_tendsto_zero τ u)
  rw [Real.norm_eq_abs, ← familyTwoNorm_completionMap τ (u.1 n), abs_sub_comm]
  exact familyTwoNorm_abs_sub_le (completionTrace τ) _ _


-- @@ L362-368 verbatim
lemma completionQuotientMap_eq_zero (u : familyCauchyAlgebra τ) :
    (familyCauchyNullIdeal τ).quotientMap u = 0 ↔
      IsFamilyNull τ atTop (fun n => u.1 n) := by
  let J := familyCauchyNullIdeal τ
  change J.ideal.ringCon.mk' u = J.ideal.ringCon.mk' 0 ↔ _
  have he : J.ideal.ringCon.mk' u = J.ideal.ringCon.mk' 0 ↔ u ∈ J.ideal := Quotient.eq
  exact he.trans (familyNull_mem τ atTop u.1)


-- @@ L370-377 verbatim
lemma completionTrace_detects_zero (x : UniformTracialCompletion τ)
    (hx : ∀ i, traceTwoNorm (completionTrace τ i) x = 0) : x = 0 := by
  obtain ⟨u,rfl⟩ := (familyCauchyNullIdeal τ).quotientMap_surjective x
  apply (completionQuotientMap_eq_zero τ u).mpr
  have he : familyTwoNorm (completionTrace τ) ((familyCauchyNullIdeal τ).quotientMap u) = 0 := by
    simp only [familyTwoNorm, hx, ciSup_const]
  change Tendsto _ _ (𝓝 0)
  simpa only [he] using completion_uniformTwoNorm_tendsto τ u


-- @@ L379-379 verbatim
end CurrentMain


-- @@ L381-381 verbatim
namespace Pureness.ClosedStarIdeal


-- @@ L383-383 verbatim
open scoped ComplexStarModule


-- @@ L385-385 verbatim
variable {D : Type uD} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L387-387 verbatim
variable (J : ClosedStarIdeal D)


-- @@ L389-395 verbatim
lemma quotientMap_realPart (u : D) :
    J.quotientMap (realPart u : D) = (realPart (J.quotientMap u) : J.Quotient) := by
  have hs : J.quotientMap ((2 : ℝ)⁻¹ • (u+star u)) =
      (2 : ℝ)⁻¹ • J.quotientMap (u+star u) :=
    (J.quotientMap.toLinearMap.restrictScalars ℝ).map_smul _ _
  rw [realPart_apply_coe, realPart_apply_coe, hs, map_add, J.quotientMap_star]
  rfl


-- @@ L397-404 verbatim
lemma exists_bounded_selfAdjoint_lift {p : J.Quotient} (hp : IsStarProjection p) :
    ∃ u : D, IsSelfAdjoint u ∧ ‖u‖ ≤ 2 ∧ J.quotientMap u = p := by
  obtain ⟨v,hv,hvn⟩ := J.quotient_norm_lt_rep p (show (0 : ℝ) < 1 by norm_num)
  refine ⟨realPart v,(realPart v).property,?_,?_⟩
  · exact (realPart.norm_le v).trans
      (hvn.le.trans (by linarith [hp.norm_le p]))
  · rw [J.quotientMap_realPart, hv]
    exact hp.isSelfAdjoint.coe_realPart


-- @@ L406-406 verbatim
end Pureness.ClosedStarIdeal


-- @@ L408-408 verbatim
namespace CurrentMain


-- @@ L410-410 verbatim
open Pureness Filter


-- @@ L412-412 verbatim
open scoped Topology NNReal ENNReal ComplexOrder


-- @@ L414-414 verbatim
section UltrapowerConstants


-- @@ L416-416 verbatim
variable {D : Type uD} {I : Type uI} {X : Type uX} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L418-418 verbatim
variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I] (U : Ultrafilter X)


-- @@ L420-423 verbatim
lemma familyLimitTrace_constant_tendsto (s : X → I) (a : D) :
    Tendsto (fun n => (τ (s n)).functional a) (U : Filter X)
      (𝓝 ((familyLimitTrace τ U s).functional (familyUltrapowerMap τ U a))) :=
  familyLimitTrace_tendsto τ U s (boundedFamilyConstant a)


-- @@ L425-433 verbatim
lemma familyTwoNorm_ultrapowerMap (a : D) :
    familyTwoNorm (familyLimitTrace τ U) (familyUltrapowerMap τ U a) = familyTwoNorm τ a := by
  change familyTwoNorm (familyLimitTrace τ U)
    ((familyNullIdeal τ (U : Filter X)).quotientMap (boundedFamilyConstant a)) = _
  rw [familyTwoNorm_limitTrace]
  exact tendsto_nhds_unique
    (bounded_ultrafilter_tendsto U (fun _ => familyTwoNorm τ a) ‖a‖ (fun _ => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (familyTwoNorm_nonneg τ a)] using
        familyTwoNorm_le_norm τ a)) tendsto_const_nhds


-- @@ L435-441 verbatim
instance familyUltrapowerNontrivial : Nontrivial (FamilyUltrapower τ U) := by
  obtain ⟨i⟩ := ‹Nonempty I›
  refine ⟨⟨1,0,?_⟩⟩
  intro h
  have he := congrArg (familyLimitTrace τ U (fun _ => i)).functional h
  rw [(familyLimitTrace τ U (fun _ => i)).normalized, map_zero] at he
  exact one_ne_zero he


-- @@ L443-452 verbatim
lemma familyUltrapowerMap_injective
    (hτ : ∀ a : D, (∀ i, traceTwoNorm (τ i) a = 0) → a = 0) :
    Function.Injective (familyUltrapowerMap τ U) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a ha
  apply hτ a
  intro i
  have he : familyTwoNorm τ a = 0 := by
    rw [← familyTwoNorm_ultrapowerMap τ U a, ha, familyTwoNorm_zero]
  exact le_antisymm ((traceTwoNorm_le_family τ i a).trans he.le) (traceTwoNorm_nonneg _ _)


-- @@ L454-454 verbatim
end UltrapowerConstants


-- @@ L456-456 verbatim
variable {D : Type uD} {I : Type uI} [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]


-- @@ L458-458 verbatim
variable [Nontrivial D] (τ : I → TracialState D) [Nonempty I]


-- @@ L460-462 verbatim
lemma completion_ultrapower_faithful {X : Type uX} (U : Ultrafilter X) :
    Function.Injective (familyUltrapowerMap (completionTrace τ) U) :=
  familyUltrapowerMap_injective (completionTrace τ) U (completionTrace_detects_zero τ)


-- @@ L464-464 verbatim
end CurrentMain


-- @@ L466-466 verbatim
end


-- @@ L468-468 verbatim
end OAI
