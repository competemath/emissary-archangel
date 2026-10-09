import OAI.MeasureTheory.SelfSimilar.FiniteEntropy


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uα uβ uγ


-- @@ L7-7 verbatim
section

-- @@ L8-8 verbatim
open scoped BigOperators ENNReal

-- @@ L9-9 verbatim
open MeasureTheory

-- @@ L10-10 verbatim
namespace EntropyRateDimension


-- @@ L12-17 verbatim
structure FiniteDistribution (α : Type uα) where
  weight : α → ℝ
  support : Finset α
  nonneg : ∀ a, 0 ≤ weight a
  vanish : ∀ a ∉ support, weight a=0
  sum_one : ∑ a ∈ support, weight a=1


-- @@ L19-19 verbatim
namespace FiniteDistribution


-- @@ L21-21 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L23-24 verbatim
noncomputable def entropy {α : Type uα} (p : FiniteDistribution α) : ℝ :=
  ∑' a, Real.negMulLog (p.weight a)


-- @@ L26-27 verbatim
noncomputable def tv {α : Type uα} (p q : FiniteDistribution α) : ℝ :=
  (∑' a, |p.weight a-q.weight a|)/2


-- @@ L29-32 verbatim
theorem sum_on {α : Type uα} (p : FiniteDistribution α) (s : Finset α)
    (hs : p.support ⊆ s) : ∑ a ∈ s, p.weight a=1 := by
  rw [← p.sum_one]
  exact (Finset.sum_subset hs (fun a _ ha => p.vanish a ha)).symm


-- @@ L34-38 verbatim
theorem entropy_on {α : Type uα} (p : FiniteDistribution α) (s : Finset α)
    (hs : p.support ⊆ s) : p.entropy=FiniteEntropy.entropy s p.weight := by
  apply tsum_eq_sum
  intro a ha
  rw [p.vanish a (fun h => ha (hs h)), Real.negMulLog_zero]


-- @@ L40-46 verbatim
theorem tv_on {α : Type uα} (p q : FiniteDistribution α) (s : Finset α)
    (hp : p.support ⊆ s) (hq : q.support ⊆ s) : p.tv q=FiniteEntropy.totalVariation s p.weight q.weight := by
  unfold tv FiniteEntropy.totalVariation
  congr 1
  apply tsum_eq_sum
  intro a ha
  rw [p.vanish a (fun h => ha (hp h)), q.vanish a (fun h => ha (hq h)), sub_self, abs_zero]


-- @@ L48-58 verbatim
noncomputable def mix {α : Type uα} (p q : FiniteDistribution α) : FiniteDistribution α := by
  classical
  refine ⟨fun a => (p.weight a+q.weight a)/2,p.support ∪ q.support,
    fun a => div_nonneg (add_nonneg (p.nonneg a) (q.nonneg a)) (by norm_num), ?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_union, not_or] at ha
    rw [p.vanish a ha.1, q.vanish a ha.2]
    norm_num
  · rw [← Finset.sum_div, Finset.sum_add_distrib,
      p.sum_on _ Finset.subset_union_left, q.sum_on _ Finset.subset_union_right]
    norm_num


-- @@ L60-61 verbatim
noncomputable def js {α : Type uα} (p q : FiniteDistribution α) : ℝ :=
  (p.mix q).entropy-(p.entropy+q.entropy)/2


-- @@ L63-67 verbatim
theorem js_on {α : Type uα} (p q : FiniteDistribution α) (s : Finset α)
    (hp : p.support ⊆ s) (hq : q.support ⊆ s) : p.js q=FiniteEntropy.js s p.weight q.weight := by
  classical
  rw [js, (p.mix q).entropy_on s (Finset.union_subset hp hq), p.entropy_on s hp, q.entropy_on s hq]
  rfl


-- @@ L69-73 verbatim
theorem js_nonneg {α : Type uα} (p q : FiniteDistribution α) : 0 ≤ p.js q := by
  classical
  rw [p.js_on q (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right]
  exact FiniteEntropy.js_nonneg _ _ _ (fun a _ => p.nonneg a) (fun a _ => q.nonneg a)
    (p.sum_on _ Finset.subset_union_left) (q.sum_on _ Finset.subset_union_right)


-- @@ L75-76 verbatim
theorem tv_nonneg {α : Type uα} (p q : FiniteDistribution α) : 0 ≤ p.tv q :=
  div_nonneg (tsum_nonneg (fun a => abs_nonneg _)) (by norm_num)


-- @@ L78-83 verbatim
theorem tv_sq_le_two_js {α : Type uα} (p q : FiniteDistribution α) : (p.tv q)^2 ≤ 2*p.js q := by
  classical
  rw [p.tv_on q (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right,
    p.js_on q (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right]
  exact FiniteEntropy.totalVariation_sq_le_two_js _ _ _ (fun a _ => p.nonneg a) (fun a _ => q.nonneg a)
    (p.sum_on _ Finset.subset_union_left) (q.sum_on _ Finset.subset_union_right)


-- @@ L85-90 verbatim
theorem js_le_tv {α : Type uα} (p q : FiniteDistribution α) : p.js q ≤ p.tv q*Real.log 2 := by
  classical
  rw [p.tv_on q (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right,
    p.js_on q (p.support ∪ q.support) Finset.subset_union_left Finset.subset_union_right]
  exact FiniteEntropy.js_le_tv _ _ _ (fun a _ => p.nonneg a) (fun a _ => q.nonneg a)
    (p.sum_on _ Finset.subset_union_left) (q.sum_on _ Finset.subset_union_right)


-- @@ L92-99 verbatim
theorem tv_triangle {α : Type uα} (p q r : FiniteDistribution α) : p.tv r ≤ p.tv q+q.tv r := by
  classical
  let s := p.support ∪ q.support ∪ r.support
  have hp : p.support ⊆ s := Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  have hq : q.support ⊆ s := Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left
  have hr : r.support ⊆ s := Finset.subset_union_right
  rw [p.tv_on r s hp hr, p.tv_on q s hp hq, q.tv_on r s hq hr]
  exact FiniteEntropy.totalVariation_triangle _ _ _ _


-- @@ L101-106 verbatim
noncomputable def map {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f : α → β) : FiniteDistribution β := by
  classical
  refine ⟨FiniteEntropy.mass p.support p.weight f,p.support.image f,
    FiniteEntropy.mass_nonneg _ _ _ (fun a _ => p.nonneg a), ?_, ?_⟩
  · exact fun b hb => FiniteEntropy.mass_eq_zero_of_not_mem p.support p.weight f hb
  · exact (FiniteEntropy.mass_sum ..).trans p.sum_one


-- @@ L108-112 verbatim
theorem map_weight_on {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f : α → β)
    (s : Finset α) (hs : p.support ⊆ s) (b : β) :
    (p.map f).weight b=FiniteEntropy.mass s p.weight f b := by
  classical
  exact FiniteEntropy.mass_subset p.weight f hs (fun a _ ha => p.vanish a ha) b


-- @@ L114-120 verbatim
theorem entropy_map_on {α : Type uα} {β : Type uβ} (p : FiniteDistribution α) (f : α → β)
    (s : Finset α) (hs : p.support ⊆ s) :
    (p.map f).entropy=FiniteEntropy.observableEntropy s p.weight f := by
  classical
  rw [(p.map f).entropy_on (s.image f) (Finset.image_subset_image hs)]
  unfold FiniteEntropy.observableEntropy FiniteEntropy.entropy
  exact Finset.sum_congr rfl (fun b _ => congrArg Real.negMulLog (p.map_weight_on f s hs b))


-- @@ L122-135 verbatim
theorem mix_map_entropy {α : Type uα} {β : Type uβ} (p q : FiniteDistribution α) (f : α → β)
    (s : Finset α) (hp : p.support ⊆ s) (hq : q.support ⊆ s) :
    ((p.map f).mix (q.map f)).entropy=
      FiniteEntropy.observableEntropy s (fun a => (p.weight a+q.weight a)/2) f := by
  classical
  rw [((p.map f).mix (q.map f)).entropy_on (s.image f)
    (Finset.union_subset (Finset.image_subset_image hp) (Finset.image_subset_image hq))]
  unfold FiniteEntropy.observableEntropy FiniteEntropy.entropy
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  change ((p.map f).weight b+(q.map f).weight b)/2=_
  rw [p.map_weight_on f s hp, q.map_weight_on f s hq]
  simp only [FiniteEntropy.mass, ← Finset.sum_div, Finset.sum_add_distrib]


-- @@ L137-146 verbatim
theorem js_map_le {α : Type uα} {β : Type uβ} (p q : FiniteDistribution α) (f : α → β) :
    (p.map f).js (q.map f) ≤ p.js q := by
  classical
  let s := p.support ∪ q.support
  have hp : p.support ⊆ s := Finset.subset_union_left
  have hq : q.support ⊆ s := Finset.subset_union_right
  rw [js, mix_map_entropy p q f s hp hq, p.entropy_map_on f s hp,
    q.entropy_map_on f s hq, p.js_on q s hp hq]
  exact FiniteEntropy.js_observable_le s _ _ (fun a _ => p.nonneg a) (fun a _ => q.nonneg a)
    (p.sum_on s hp) (q.sum_on s hq) f


-- @@ L148-166 verbatim
theorem tv_map_le {α : Type uα} {β : Type uβ} (p q : FiniteDistribution α) (f : α → β) :
    (p.map f).tv (q.map f) ≤ p.tv q := by
  classical
  let s := p.support ∪ q.support
  have hp : p.support ⊆ s := Finset.subset_union_left
  have hq : q.support ⊆ s := Finset.subset_union_right
  rw [(p.map f).tv_on (q.map f) (s.image f)
    (Finset.image_subset_image hp) (Finset.image_subset_image hq), p.tv_on q s hp hq]
  unfold FiniteEntropy.totalVariation
  apply div_le_div_of_nonneg_right _ (by norm_num)
  calc
    _ ≤ ∑ b ∈ s.image f, ∑ a ∈ s.filter (f ·=b), |p.weight a-q.weight a| := by
      apply Finset.sum_le_sum
      intro b _
      rw [p.map_weight_on f s hp, q.map_weight_on f s hq]
      unfold FiniteEntropy.mass
      rw [← Finset.sum_sub_distrib]
      exact Finset.abs_sum_le_sum_abs _ _
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image_of_mem f ha) _


-- @@ L168-171 verbatim
theorem entropy_congr {α : Type uα} (p q : FiniteDistribution α) (h : p.weight=q.weight) :
    p.entropy=q.entropy := by
  unfold entropy
  rw [h]


-- @@ L173-176 verbatim
theorem tv_congr {α : Type uα} (p q p' q' : FiniteDistribution α)
    (hp : p.weight=p'.weight) (hq : q.weight=q'.weight) : p.tv q=p'.tv q' := by
  unfold tv
  rw [hp,hq]


-- @@ L178-186 verbatim
theorem js_congr {α : Type uα} (p q p' q' : FiniteDistribution α)
    (hp : p.weight=p'.weight) (hq : q.weight=q'.weight) : p.js q=p'.js q' := by
  unfold js
  rw [p.entropy_congr p' hp,q.entropy_congr q' hq]
  congr 1
  apply entropy_congr
  funext a
  change (p.weight a+q.weight a)/2=(p'.weight a+q'.weight a)/2
  rw [hp,hq]


-- @@ L188-191 verbatim
theorem map_weight_comp {α : Type uα} {β : Type uβ} {γ : Type uγ} (p : FiniteDistribution α) (f : α → β) (g : β → γ) :
    ((p.map f).map g).weight=(p.map (g ∘ f)).weight := by
  funext c
  exact FiniteEntropy.mass_comp p.support p.weight f g c


-- @@ L193-201 verbatim
theorem map_weight_of_injective {α : Type uα} {β : Type uβ} (p : FiniteDistribution α)
    (f : α → β) (hf : Function.Injective f) (a : α) :
    (p.map f).weight (f a)=p.weight a := by
  change FiniteEntropy.mass p.support p.weight f (f a)=p.weight a
  simp only [FiniteEntropy.mass, Finset.sum_filter, hf.eq_iff]
  rw [Finset.sum_ite_eq']
  by_cases ha : a ∈ p.support
  · simp only [ha, ↓reduceIte]
  · simp only [ha, ↓reduceIte, p.vanish a ha]


-- @@ L203-205 verbatim
theorem map_weight_id {α : Type uα} (p : FiniteDistribution α) : (p.map id).weight=p.weight := by
  funext a
  exact p.map_weight_of_injective id Function.injective_id a


-- @@ L207-219 verbatim
theorem entropy_map_injective {α : Type uα} {β : Type uβ} (p : FiniteDistribution α)
    (f : α → β) (hf : Function.Injective f) : (p.map f).entropy=p.entropy := by
  have hn : p.support.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hh := p.sum_one
    simp only [he, Finset.sum_empty] at hh
    norm_num at hh
  obtain ⟨a,_⟩ := hn
  let : Nonempty α := ⟨a⟩
  let : Nonempty β := ⟨f a⟩
  rw [p.entropy_map_on f p.support (fun _ h => h), p.entropy_on p.support (fun _ h => h)]
  exact FiniteEntropy.observableEntropy_of_injective _ _ _ (fun a _ => p.nonneg a) hf


-- @@ L221-233 verbatim
theorem tv_map_injective {α : Type uα} {β : Type uβ} (p q : FiniteDistribution α)
    (f : α → β) (hf : Function.Injective f) : (p.map f).tv (q.map f)=p.tv q := by
  let s := p.support ∪ q.support
  have hp : p.support ⊆ s := Finset.subset_union_left
  have hq : q.support ⊆ s := Finset.subset_union_right
  rw [(p.map f).tv_on (q.map f) (s.image f)
    (Finset.image_subset_image hp) (Finset.image_subset_image hq), p.tv_on q s hp hq]
  unfold FiniteEntropy.totalVariation
  rw [Finset.sum_image (fun a _ b _ hab => hf hab)]
  congr 1
  apply Finset.sum_congr rfl
  intro a _
  rw [p.map_weight_of_injective f hf, q.map_weight_of_injective f hf]


-- @@ L235-245 verbatim
theorem js_map_equiv {α : Type uα} {β : Type uβ} (p q : FiniteDistribution α) (e : α ≃ β) :
    (p.map e).js (q.map e)=p.js q := by
  apply le_antisymm (js_map_le p q e)
  have hh := js_map_le (p.map e) (q.map e) e.symm
  have he (r : FiniteDistribution α) : ((r.map e).map e.symm).weight=r.weight := by
    rw [map_weight_comp]
    convert r.map_weight_id using 2
    congr 1
    funext a
    exact e.symm_apply_apply a
  rwa [js_congr _ _ p q (he p) (he q)] at hh


-- @@ L247-248 verbatim
noncomputable def translate (p : FiniteDistribution ℤ) (j : ℤ) : FiniteDistribution ℤ :=
  p.map (fun a => a+j)


-- @@ L250-253 verbatim
theorem translate_weight (p : FiniteDistribution ℤ) (j a : ℤ) :
    (p.translate j).weight a=p.weight (a-j) := by
  change (p.map (fun a => a+j)).weight a=p.weight (a-j)
  convert p.map_weight_of_injective (fun a => a+j) (add_left_injective j) (a-j) using 1; simp


-- @@ L255-257 verbatim
theorem tv_translate (p q : FiniteDistribution ℤ) (j : ℤ) :
    (p.translate j).tv (q.translate j)=p.tv q :=
  p.tv_map_injective q _ (add_left_injective j)


-- @@ L259-264 verbatim
theorem translate_add (p : FiniteDistribution ℤ) (i j : ℤ) :
    ((p.translate i).translate j).weight=(p.translate (i+j)).weight := by
  funext a
  rw [translate_weight,translate_weight,translate_weight]
  congr 1
  omega


-- @@ L266-273 verbatim
theorem tv_translate_two (p : FiniteDistribution ℤ) :
    p.tv (p.translate 2) ≤ 2*p.tv (p.translate 1) := by
  have hh := tv_triangle p (p.translate 1) (p.translate 2)
  have he : (p.translate 1).tv (p.translate 2)=p.tv (p.translate 1) := by
    rw [← p.tv_translate (p.translate 1) 1]
    exact tv_congr _ _ _ _ rfl (p.translate_add 1 1).symm
  rw [he] at hh
  linarith


-- @@ L275-287 verbatim
theorem js_two_step_coarsen (p : FiniteDistribution ℤ) (f : ℤ → ℤ) :
    ((p.map f).js ((p.translate 2).map f))^2 ≤
      8*(Real.log 2)^2*p.js (p.translate 1) := by
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h0 := js_nonneg (p.map f) ((p.translate 2).map f)
  have h1 := (js_map_le p (p.translate 2) f).trans (js_le_tv p (p.translate 2))
  have h2 := mul_le_mul_of_nonneg_right (tv_translate_two p) hlog
  have h3 := tv_sq_le_two_js p (p.translate 1)
  have htv := tv_nonneg p (p.translate 1)
  have hh : ((p.map f).js ((p.translate 2).map f))^2 ≤
      (2*p.tv (p.translate 1)*Real.log 2)^2 := by
    exact sq_le_sq₀ h0 (by positivity) |>.mpr (h1.trans h2)
  nlinarith [mul_le_mul_of_nonneg_left h3 (sq_nonneg (Real.log 2))]


-- @@ L289-302 verbatim
theorem tv_le_one {α : Type uα} (p q : FiniteDistribution α) : p.tv q ≤ 1 := by
  let s := p.support ∪ q.support
  have hp : p.support ⊆ s := Finset.subset_union_left
  have hq : q.support ⊆ s := Finset.subset_union_right
  rw [p.tv_on q s hp hq]
  unfold FiniteEntropy.totalVariation
  have hh : (∑ a ∈ s, |p.weight a-q.weight a|) ≤ 2 := by
    calc
      _ ≤ ∑ a ∈ s, (p.weight a+q.weight a) := by
        apply Finset.sum_le_sum
        intro a _
        exact abs_sub_le_iff.mpr ⟨by linarith [q.nonneg a], by linarith [p.nonneg a]⟩
      _ = 2 := by rw [Finset.sum_add_distrib, p.sum_on s hp, q.sum_on s hq]; norm_num
  linarith


-- @@ L304-308 verbatim
theorem js_le_log_two {α : Type uα} (p q : FiniteDistribution α) : p.js q ≤ Real.log 2 := by
  calc
    _ ≤ p.tv q*Real.log 2 := js_le_tv p q
    _ ≤ 1*Real.log 2 := mul_le_mul_of_nonneg_right (tv_le_one p q) (Real.log_nonneg (by norm_num))
    _ = _ := one_mul _


-- @@ L310-319 verbatim
theorem map_translate_div_two (p : FiniteDistribution ℤ) :
    ((p.translate 2).map (fun n => n/2)).weight=
      ((p.map (fun n => n/2)).translate 1).weight := by
  change ((p.map (fun n => n+2)).map (fun n => n/2)).weight=
    ((p.map (fun n => n/2)).map (fun n => n+1)).weight
  rw [map_weight_comp, map_weight_comp]
  congr 2
  funext n
  dsimp only [Function.comp_apply]
  omega


-- @@ L321-321 verbatim
end FiniteDistribution


-- @@ L323-323 verbatim
end EntropyRateDimension

-- @@ L324-324 verbatim
end


-- @@ L326-326 verbatim
end OAI
