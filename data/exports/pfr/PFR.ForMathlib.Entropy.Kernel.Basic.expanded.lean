module

public import Mathlib.MeasureTheory.Integral.Prod
public import PFR.ForMathlib.Entropy.Measure
public import PFR.Mathlib.Probability.Kernel.Disintegration


-- @@ L7-24 verbatim
/-!
# Entropy of a kernel with respect to a measure

## Main definitions

* `Kernel.entropy`: entropy of a kernel `κ` with respect to a measure `μ`,
  `μ[fun t ↦ measureEntropy (κ t)]`. We use the notation `Hk[κ, μ]`.

## Main statements

* `chain_rule`: `Hk[κ, μ] = Hk[fst κ, μ] + Hk[condKernel κ, μ ⊗ₘ (fst κ)]`.
* `entropy_map_le`: data-processing inequality for the kernel entropy

## Notations

* `Hk[κ, μ] = Kernel.entropy κ μ`

-/


-- @@ L26-26 verbatim
@[expose] public section


-- @@ L28-28 verbatim
open Real MeasureTheory

-- @@ L29-29 verbatim
open scoped ENNReal NNReal Topology ProbabilityTheory


-- @@ L31-31 verbatim
namespace ProbabilityTheory.Kernel


-- @@ L33-34 verbatim
variable {Ω S T U : Type*} [mΩ : MeasurableSpace Ω]
  [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]


-- @@ L36-38 expanded
/-- Entropy of a kernel with respect to a measure. -/
noncomputable def entropy (κ : Kernel T S) (μ : Measure T) :=
  μ[fun y ↦ measureEntropy (κ y)]


-- @@ L40-41 verbatim
/-- Entropy of a kernel with respect to a measure. -/
notation3:100 "Hk[" κ " , " μ "]" => ProbabilityTheory.Kernel.entropy κ μ


-- @@ L43-44 expanded
@[simp]
lemma entropy_zero_measure (κ : Kernel T S) :
    ProbabilityTheory.Kernel.entropy κ (0 : Measure T) = 0 := by simp [entropy]


-- @@ L46-47 expanded
@[simp]
lemma entropy_zero_kernel (μ : Measure T) :
    ProbabilityTheory.Kernel.entropy (0 : Kernel T S) μ = 0 := by simp [entropy]


-- @@ L49-53 expanded
lemma entropy_congr {μ} {κ η : Kernel T S} (h : κ =ᵐ[μ] η) :
    ProbabilityTheory.Kernel.entropy κ μ = ProbabilityTheory.Kernel.entropy η μ :=
  by
  simp_rw [entropy]
  refine integral_congr_ae ?_
  filter_upwards [h] with x hx
  rw [hx]


-- @@ L55-56 expanded
lemma entropy_nonneg (κ : Kernel T S) (μ : Measure T) : 0 ≤ ProbabilityTheory.Kernel.entropy κ μ :=
  integral_nonneg (fun _ ↦ measureEntropy_nonneg _)


-- @@ L58-61 expanded
@[simp]
lemma entropy_const (ν : Measure S) (μ : Measure T) :
    ProbabilityTheory.Kernel.entropy (Kernel.const T ν) μ =
      (μ Set.univ).toReal * measureEntropy ν :=
  by simp [entropy, Measure.real]


-- @@ L63-68 verbatim
/-- Constant kernels with finite support, have finite kernel support. -/
lemma finiteKernelSupport_of_const (ν : Measure S) [FiniteSupport ν] :
    FiniteKernelSupport (Kernel.const T ν) := by
  intro t
  use ν.support
  simp [measure_compl_support ν]


-- @@ L70-83 verbatim
/-- Composing a finitely supported measure with a finitely supported kernel gives a finitely
supported kernel. -/
lemma finiteSupport_of_compProd' [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    {μ : Measure T} [IsFiniteMeasure μ] {κ : Kernel T S}
    [IsZeroOrMarkovKernel κ] [FiniteSupport μ] (hκ : FiniteKernelSupport κ) :
    FiniteSupport (μ ⊗ₘ κ) := by
  let A := μ.support
  have hA := measure_compl_support μ
  rcases (local_support_of_finiteKernelSupport hκ A) with ⟨B, hB⟩
  use A ×ˢ B
  rw [Measure.ae_compProd_iff (by exact (Finset.finite_toSet _).measurableSet)]
  filter_upwards [ae_mem_support μ] with t ht
  filter_upwards [hB t ht] with s hs
  exact Finset.mk_mem_product ht hs


-- @@ L85-91 verbatim
lemma finiteSupport_of_compProd
    [MeasurableSingletonClass S] [Countable T] [MeasurableSingletonClass T]
    {μ : Measure T} [IsFiniteMeasure μ] {κ : Kernel T S}
    [IsZeroOrMarkovKernel κ] [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    FiniteSupport (μ ⊗ₘ κ) := by
  rw [Measure.compProd_congr hκ.ae_eq_mk]
  exact finiteSupport_of_compProd' hκ.finiteKernelSupport_mk


-- @@ L93-101 verbatim
lemma aefiniteKernelSupport_condDistrib
    [Nonempty S] [Countable S] [MeasurableSingletonClass S]
    [Countable T] [MeasurableSingletonClass T]
    (X : Ω → S) (Y : Ω → T) (μ : Measure Ω) [IsFiniteMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) [FiniteRange X] :
    AEFiniteKernelSupport (condDistrib X Y μ) (μ.map Y) := by
  filter_upwards [condDistrib_ae_eq hX hY μ] with a ha
  rw [ha]
  exact finiteSupport_of_finiteRange.finite


-- @@ L103-110 expanded
lemma entropy_le_log_card [MeasurableSingletonClass S] (κ : Kernel T S) (μ : Measure T) [Fintype S]
    [IsProbabilityMeasure μ] : ProbabilityTheory.Kernel.entropy κ μ ≤ log (Fintype.card S) :=
  by
  refine (integral_mono_of_nonneg ?_ (integrable_const (log (Fintype.card S))) ?_).trans ?_
  · exact ae_of_all _ (fun _ ↦ measureEntropy_nonneg _)
  · exact ae_of_all _ (fun _ ↦ measureEntropy_le_log_card _)
  · simp


-- @@ L112-116 expanded
lemma entropy_eq_integral_sum (κ : Kernel T S) [IsZeroOrMarkovKernel κ] (μ : Measure T) :
    ProbabilityTheory.Kernel.entropy κ μ = μ[fun y ↦ ∑' x, negMulLog ((κ y).real { x })] := by
  simp_rw [entropy, measureEntropy_of_isProbabilityMeasure]
    -- entropy_map_of_injective is a special case of this (see def of map)


-- @@ L117-133 expanded
lemma entropy_snd_compProd_deterministic_of_injective [MeasurableSingletonClass U] (κ : Kernel T S)
    [IsMarkovKernel κ] (μ : Measure T) {f : T × S → U}
    (hf : ∀ t, Function.Injective (fun x ↦ f (t, x))) (hmes : Measurable f) :
    ProbabilityTheory.Kernel.entropy (snd (κ ⊗ₖ deterministic f hmes)) μ =
      ProbabilityTheory.Kernel.entropy κ μ :=
  by
  have : ∀ t, snd (κ ⊗ₖ deterministic f hmes) t = map κ (fun x ↦ f (t, x)) t :=
    by
    intro t
    ext s hs
    rw [snd_apply' _ _ hs, compProd_deterministic_apply, map_apply' _ (by fun_prop) _ hs]
    · rfl
    · exact measurable_snd hs
  simp_rw [entropy]
  congr with y
  convert measureEntropy_map_of_injective (κ y) _ (hmes.comp measurable_prodMk_left) (hf y)
  rw [this y, map_apply _ (by fun_prop)]
  rfl


-- @@ L135-138 expanded
lemma entropy_map_of_injective [MeasurableSingletonClass U] (κ : Kernel T S) (μ : Measure T)
    {f : S → U} (hf : Function.Injective f) (hmes : Measurable f) :
    ProbabilityTheory.Kernel.entropy (map κ f) μ = ProbabilityTheory.Kernel.entropy κ μ := by
  simp_rw [entropy, map_apply _ hmes, measureEntropy_map_of_injective _ _ hmes hf]


-- @@ L140-143 expanded
lemma entropy_map_swap [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    (κ : Kernel T (S × U)) (μ : Measure T) :
    ProbabilityTheory.Kernel.entropy (map κ Prod.swap) μ = ProbabilityTheory.Kernel.entropy κ μ :=
  entropy_map_of_injective κ μ Prod.swap_injective measurable_swap


-- @@ L145-148 expanded
lemma entropy_swapRight [MeasurableSingletonClass S] [MeasurableSingletonClass U]
    (κ : Kernel T (S × U)) (μ : Measure T) :
    ProbabilityTheory.Kernel.entropy (swapRight κ) μ = ProbabilityTheory.Kernel.entropy κ μ := by
  rw [swapRight_eq, entropy_map_swap]


-- @@ L150-173 expanded
lemma entropy_comap [MeasurableSingletonClass T] {T' : Type*} [MeasurableSpace T']
    [MeasurableSingletonClass T'] (κ : Kernel T S) (μ : Measure T) (f : T' → T)
    (hf : MeasurableEmbedding f) (hf_range : Set.range f =ᵐ[μ] Set.univ) [IsFiniteMeasure μ]
    [IsFiniteMeasure (μ.comap f)] (hfμ : FiniteSupport (μ.comap f)) :
    ProbabilityTheory.Kernel.entropy (comap κ f hf.measurable) (μ.comap f) =
      ProbabilityTheory.Kernel.entropy κ μ :=
  by
  classical
  rcases hfμ with ⟨A, (hA : ∀ᵐ x ∂μ.comap f, x ∈ A)⟩
  have : ∀ᵐ x ∂μ, x ∈ Finset.image f A :=
    by
    change μ (Finset.image f A : Set T)ᶜ = 0
    simp only [Finset.coe_image, hf.injective.compl_image_eq, measure_union_null_iff]
    constructor
    · rwa [← Measure.comap_apply f hf.injective hf.measurableSet_image']
      exact MeasurableSet.compl (Finset.measurableSet A)
    exact ae_eq_univ.mp hf_range
  simp_rw [entropy]
  simp_rw [integral_eq_setIntegral hA, integral_eq_setIntegral this, setIntegral_finset _ .finset,
    Measure.comap_real_apply hf.injective hf.measurableSet_image' _ (.singleton _)]
  simp only [Set.image_singleton, smul_eq_mul]
  simp_rw [comap_apply]
  rw [← Finset.sum_image (f := fun x ↦ μ.real { x } * measureEntropy (κ x)) (g := f)]
  intro x _ y _ hxy
  exact hf.injective hxy


-- @@ L175-188 verbatim
lemma FiniteSupport.comap_equiv [MeasurableSingletonClass T]
    {T' : Type*} [MeasurableSpace T']
    {μ : Measure T} (f : T' ≃ᵐ T) [FiniteSupport μ] :
    FiniteSupport (μ.comap f) := by
  classical
  let A := μ.support
  have hA := measure_compl_support μ
  refine ⟨Finset.image f.symm A, ?_⟩
  change (Measure.comap (⇑f) μ) (A.image f.symm)ᶜ = 0
  rwa [Finset.coe_image, ← Set.image_compl_eq (MeasurableEquiv.bijective f.symm),
    Measure.comap_apply f (MeasurableEquiv.injective f),MeasurableEquiv.image_symm,
    MeasurableEquiv.image_preimage]
  · exact fun _ ↦ (MeasurableEquiv.measurableSet_image f).mpr
  · exact f.symm.measurableSet_image.mpr A.measurableSet.compl


-- @@ L190-195 expanded
lemma entropy_comap_equiv [MeasurableSingletonClass T] {T' : Type*} [MeasurableSpace T']
    [MeasurableSingletonClass T'] (κ : Kernel T S) {μ : Measure T} (f : T' ≃ᵐ T) [IsFiniteMeasure μ]
    [FiniteSupport μ] :
    ProbabilityTheory.Kernel.entropy (comap κ f f.measurable) (μ.comap f) =
      ProbabilityTheory.Kernel.entropy κ μ :=
  by simp [entropy_comap, f.measurableEmbedding, FiniteSupport.comap_equiv f]


-- @@ L197-201 expanded
lemma entropy_comap_swap [MeasurableSingletonClass T] {T' : Type*} [MeasurableSpace T']
    [MeasurableSingletonClass T'] (κ : Kernel (T' × T) S) {μ : Measure (T' × T)} [IsFiniteMeasure μ]
    [FiniteSupport μ] :
    ProbabilityTheory.Kernel.entropy (comap κ Prod.swap measurable_swap) (μ.comap Prod.swap) =
      ProbabilityTheory.Kernel.entropy κ μ :=
  entropy_comap_equiv κ MeasurableEquiv.prodComm


-- @@ L203-209 expanded
lemma entropy_prodMkLeft_unit [MeasurableSingletonClass T] (κ : Kernel T S) {μ : Measure T}
    [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ] :
    ProbabilityTheory.Kernel.entropy (prodMkLeft Unit κ) (μ.map (Prod.mk ())) =
      ProbabilityTheory.Kernel.entropy κ μ :=
  by
  convert entropy_comap_equiv κ (.punitProd) (μ := μ)
  · rfl
  rw [← MeasurableEquiv.map_symm]
  congr


-- @@ L211-266 expanded
lemma entropy_compProd_aux [MeasurableSingletonClass S] [MeasurableSingletonClass T]
    [MeasurableSingletonClass U] {μ} [IsFiniteMeasure μ] {κ : Kernel T S} [IsZeroOrMarkovKernel κ]
    {η : Kernel (T × S) U} [IsMarkovKernel η] [FiniteSupport μ] (hκ : FiniteKernelSupport κ)
    (hη : FiniteKernelSupport η) :
    ProbabilityTheory.Kernel.entropy (κ ⊗ₖ η) μ =
      ProbabilityTheory.Kernel.entropy κ μ +
        μ[fun t ↦
          ProbabilityTheory.Kernel.entropy (comap η (Prod.mk t) measurable_prodMk_left) (κ t)] :=
  by
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp
  let A := μ.support
  have hsum (F : T → ℝ) : ∫ (t : T), F t ∂μ = ∑ t ∈ A, (μ.real { t }) * (F t) :=
    by
    rw [integral_eq_setIntegral (ae_mem_support μ), setIntegral_finset _ .finset]
    congr with t ht
  simp_rw [entropy, hsum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro t ht
  rw [← mul_add]
  congr
  obtain ⟨B, hB⟩ := local_support_of_finiteKernelSupport hκ A
  obtain ⟨C, hC⟩ := local_support_of_finiteKernelSupport hη (A ×ˢ B)
  rw [integral_eq_setIntegral (hB t ht)]
  have hκη : ((κ ⊗ₖ η) t) (B ×ˢ C : Finset (S × U))ᶜ = 0 :=
    by
    rw [Kernel.compProd_apply (Finset.measurableSet _).compl,
      lintegral_eq_setLIntegral (ae_iff.1 <| hB t ht), setLIntegral_eq_sum]
    apply Finset.sum_eq_zero
    intro s hs
    simpa using .inr <| measure_mono_null (by simp [*]) (hC (t, s) <| by simp [ht, hs])
  rw [measureEntropy_eq_sum hκη, measureEntropy_eq_sum (hB t ht), setIntegral_finset _ .finset, ←
    Finset.sum_add_distrib, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [measure_univ, inv_one, one_smul, coe_comap, Function.comp_apply, smul_eq_mul]
  have hts : (t, s) ∈ A ×ˢ B := by simp [ht, hs]
  rw [measureEntropy_eq_sum (hC (t, s) hts)]
  simp only [measure_univ, inv_one, one_smul]
  have :
    negMulLog ((κ t).real { s }) =
      ∑ u ∈ C,
        negMulLog ((κ t).real { s }) *
          ((comap η (Prod.mk t) measurable_prodMk_left) s).real { u } :=
    by
    rw [← Finset.mul_sum]
    simp only [coe_comap, Function.comp_apply, sum_measureReal_singleton]
    suffices (η (t, s)).real ↑C = (η (t, s)).real Set.univ by simp [this]
    have := hC (t, s) hts
    rw [ae_iff, ← measureReal_eq_zero_iff] at this
    change (η (t, s)).real Cᶜ = 0 at this
    rw [← measureReal_add_measureReal_compl (s := C) _, this, add_zero]
    exact Finset.measurableSet C
  rw [this, Finset.mul_sum, ← Finset.sum_add_distrib]
  congr with u
  have : ((κ ⊗ₖ η) t).real {(s, u)} = (κ t).real { s } * (η (t, s)).real { u } :=
    by
    rw [measureReal_def, compProd_apply (.singleton _),
      lintegral_eq_setLIntegral (ae_iff.1 <| hB t ht), setLIntegral_eq_sum,
      Finset.sum_eq_single_of_mem s hs]
    · simp [measureReal_def, Set.preimage]
    intro b _ hbs
    simp [hbs, Set.preimage]
  rw [this, Kernel.comap_apply, negMulLog_mul, negMulLog, negMulLog]
  ring


-- @@ L268-280 expanded
lemma entropy_compProd' [MeasurableSingletonClass S] [Countable S] [MeasurableSingletonClass T]
    [Countable T] [MeasurableSingletonClass U] {μ} [IsFiniteMeasure μ] {κ : Kernel T S}
    [IsZeroOrMarkovKernel κ] {η : Kernel (T × S) U} [IsMarkovKernel η] [FiniteSupport μ]
    (hκ : FiniteKernelSupport κ) (hη : FiniteKernelSupport η) :
    ProbabilityTheory.Kernel.entropy (κ ⊗ₖ η) μ =
      ProbabilityTheory.Kernel.entropy κ μ + ProbabilityTheory.Kernel.entropy η (μ ⊗ₘ κ) :=
  by
  rw [entropy_compProd_aux hκ hη]
  congr
  rw [entropy, Measure.integral_compProd]
  · simp_rw [entropy]
    congr
  · have := finiteSupport_of_compProd' hκ (μ := μ)
    exact integrable_of_finiteSupport (μ ⊗ₘ κ)


-- @@ L282-296 expanded
lemma entropy_compProd [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T] [MeasurableSingletonClass U] {μ} [IsFiniteMeasure μ]
    {κ : Kernel T S} [IsZeroOrMarkovKernel κ] {η : Kernel (T × S) U} [IsMarkovKernel η]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η (μ ⊗ₘ κ)) :
    ProbabilityTheory.Kernel.entropy (κ ⊗ₖ η) μ =
      ProbabilityTheory.Kernel.entropy κ μ + ProbabilityTheory.Kernel.entropy η (μ ⊗ₘ κ) :=
  by
  have h_meas_eq : μ ⊗ₘ hκ.mk = μ ⊗ₘ κ := Measure.compProd_congr hκ.ae_eq_mk.symm
  have h_ent1 :
    ProbabilityTheory.Kernel.entropy (hκ.mk ⊗ₖ hη.mk) μ =
      ProbabilityTheory.Kernel.entropy (κ ⊗ₖ η) μ :=
    by
    refine entropy_congr <| compProd_congr_ae hκ.ae_eq_mk.symm ?_
    convert hη.ae_eq_mk.symm
  have h_ent2 : ProbabilityTheory.Kernel.entropy hκ.mk μ = ProbabilityTheory.Kernel.entropy κ μ :=
    entropy_congr hκ.ae_eq_mk.symm
  have h_ent3 :
    ProbabilityTheory.Kernel.entropy hη.mk (μ ⊗ₘ hκ.mk) =
      ProbabilityTheory.Kernel.entropy η (μ ⊗ₘ κ) :=
    by rw [h_meas_eq, entropy_congr hη.ae_eq_mk]
  rw [← h_ent1, ← h_ent2, ← h_ent3,
    entropy_compProd' hκ.finiteKernelSupport_mk hη.finiteKernelSupport_mk]


-- @@ L298-304 expanded
@[simp]
lemma entropy_deterministic [MeasurableSingletonClass S] [Countable T] [MeasurableSingletonClass T]
    (f : T → S) (μ : Measure T) :
    ProbabilityTheory.Kernel.entropy (deterministic f .of_discrete) μ = 0 :=
  by
  simp_rw [entropy]
  convert integral_zero T ℝ
  apply measureEntropy_dirac


-- @@ L306-312 expanded
@[simp]
lemma entropy_compProd_deterministic [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T] [MeasurableSingletonClass U] (κ : Kernel T S)
    [IsZeroOrMarkovKernel κ] (μ : Measure T) [IsFiniteMeasure μ] (f : T × S → U) [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    ProbabilityTheory.Kernel.entropy (κ ⊗ₖ (deterministic f .of_discrete)) μ =
      ProbabilityTheory.Kernel.entropy κ μ :=
  by simp [entropy_compProd hκ ((FiniteKernelSupport.deterministic f).aefiniteKernelSupport _)]


-- @@ L314-316 verbatim
lemma nonempty_of_isMarkovKernel {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (κ : Kernel α β) [IsMarkovKernel κ] [Nonempty α] : Nonempty β :=
  (κ <| Classical.arbitrary _).nonempty_of_neZero


-- @@ L318-322 verbatim
lemma nonempty_of_isProbabilityMeasure_of_isMarkovKernel
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) [IsProbabilityMeasure μ]
    (κ : Kernel α β) [IsMarkovKernel κ] : Nonempty β := by
  have : Nonempty α := μ.nonempty_of_neZero
  exact nonempty_of_isMarkovKernel κ


-- @@ L324-331 expanded
lemma chain_rule [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T] [Countable U] [MeasurableSingletonClass U] {κ : Kernel T (S × U)}
    [IsZeroOrMarkovKernel κ] [hU : Nonempty U] {μ : Measure T} [IsZeroOrProbabilityMeasure μ]
    [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    ProbabilityTheory.Kernel.entropy κ μ =
      ProbabilityTheory.Kernel.entropy (fst κ) μ +
        ProbabilityTheory.Kernel.entropy (condKernel κ) (μ ⊗ₘ (fst κ)) :=
  by
  conv_lhs => rw [disintegration κ]
  rw [entropy_compProd hκ.fst (aefiniteKernelSupport_of_cond _ hκ)]


-- @@ L333-340 expanded
lemma chain_rule' [Nonempty S] [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T] [Countable U] [MeasurableSingletonClass U] {κ : Kernel T (S × U)}
    [IsZeroOrMarkovKernel κ] {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    ProbabilityTheory.Kernel.entropy κ μ =
      ProbabilityTheory.Kernel.entropy (snd κ) μ +
        ProbabilityTheory.Kernel.entropy (condKernel (swapRight κ)) (μ ⊗ₘ (snd κ)) :=
  by
  rw [← entropy_swapRight, chain_rule hκ.swapRight]
  simp


-- @@ L342-350 expanded
@[simp]
lemma entropy_prodMkRight [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T] {κ : Kernel T S} {η : Kernel T U} [IsMarkovKernel κ]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) :
    ProbabilityTheory.Kernel.entropy (prodMkRight S η) (μ ⊗ₘ κ) =
      ProbabilityTheory.Kernel.entropy η μ :=
  by
  have := finiteSupport_of_compProd hκ (μ := μ)
  simp [entropy, Measure.integral_compProd, integrable_of_finiteSupport]


-- @@ L352-361 expanded
lemma entropy_prodMkRight' [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T] {η : Kernel T U} {μ : Measure T} [IsZeroOrProbabilityMeasure μ]
    {ν : Measure S} [IsProbabilityMeasure ν] [FiniteSupport μ] [FiniteSupport ν] :
    ProbabilityTheory.Kernel.entropy (prodMkRight S η) (μ.prod ν) =
      ProbabilityTheory.Kernel.entropy η μ :=
  by
  rw [← entropy_prodMkRight (μ := μ) ((finiteKernelSupport_of_const ν).aefiniteKernelSupport _)]
  congr
  ext s hs
  simp_rw [Measure.prod_apply hs, Measure.compProd_apply hs, Kernel.const_apply]


-- @@ L363-372 expanded
@[simp]
lemma entropy_prodMkLeft [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T] {η : Kernel T U} {ν : Measure S} [IsProbabilityMeasure ν]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ] [FiniteSupport ν] :
    ProbabilityTheory.Kernel.entropy (prodMkLeft S η) (ν.prod μ) =
      ProbabilityTheory.Kernel.entropy η μ :=
  by
  simp_rw [entropy, prodMkLeft_apply]
  rw [integral_prod]
  swap; · exact integrable_of_finiteSupport (ν.prod μ)
  simp


-- @@ L374-375 verbatim
variable [Countable S] [MeasurableSingletonClass S] [Countable T]
    [MeasurableSingletonClass T] [Countable U] [MeasurableSingletonClass U]


-- @@ L377-386 expanded
@[simp]
lemma entropy_prod {κ : Kernel T S} {η : Kernel T U} [IsMarkovKernel κ] [IsMarkovKernel η]
    {μ : Measure T} [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ]
    (hκ : AEFiniteKernelSupport κ μ) (hη : AEFiniteKernelSupport η μ) :
    ProbabilityTheory.Kernel.entropy (κ ×ₖ η) μ =
      ProbabilityTheory.Kernel.entropy κ μ + ProbabilityTheory.Kernel.entropy η μ :=
  by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty U := nonempty_of_isProbabilityMeasure_of_isMarkovKernel μ η
  rw [chain_rule (hκ.prod hη), fst_prod, entropy_congr (condKernel_prod_ae_eq _ _),
    entropy_prodMkRight hκ]


-- @@ L388-405 expanded
/-- Data-processing inequality for the kernel entropy. -/
lemma entropy_map_le {κ : Kernel T S} [IsZeroOrMarkovKernel κ] {μ : Measure T}
    [IsZeroOrProbabilityMeasure μ] (f : S → U) [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    ProbabilityTheory.Kernel.entropy (map κ f) μ ≤ ProbabilityTheory.Kernel.entropy κ μ :=
  by
  rcases eq_zero_or_isMarkovKernel κ with rfl | hκ'
  · simp
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp
  have : Nonempty S := nonempty_of_isProbabilityMeasure_of_isMarkovKernel μ κ
  have :
    ProbabilityTheory.Kernel.entropy κ μ =
      ProbabilityTheory.Kernel.entropy (map κ (fun x ↦ (x, f x))) μ :=
    by
    refine (entropy_map_of_injective κ μ (f := fun x ↦ (x, f x)) ?_ (by fun_prop)).symm
    intro x y hxy
    simp only [Prod.mk.injEq] at hxy
    exact hxy.1
  rw [this, chain_rule' hκ.map]
  simp_rw [snd_map_prod κ measurable_id', le_add_iff_nonneg_right]
  exact entropy_nonneg _ _


-- @@ L407-415 expanded
lemma entropy_of_map_eq_of_map {κ : Kernel T S} {η : Kernel T U} [IsZeroOrMarkovKernel κ]
    [IsZeroOrMarkovKernel η] {μ : Measure T} [IsZeroOrProbabilityMeasure μ] (f : S → U) (g : U → S)
    (h1 : η = map κ f) (h2 : κ = map η g) [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ)
    (hη : AEFiniteKernelSupport η μ) :
    ProbabilityTheory.Kernel.entropy κ μ = ProbabilityTheory.Kernel.entropy η μ :=
  by
  refine le_antisymm ?_ ?_
  · rw [h2]; exact entropy_map_le g hη
  · rw [h1]; exact entropy_map_le f hκ


-- @@ L417-422 expanded
lemma entropy_snd_le {κ : Kernel T (S × U)} [IsZeroOrMarkovKernel κ] {μ : Measure T}
    [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    ProbabilityTheory.Kernel.entropy (snd κ) μ ≤ ProbabilityTheory.Kernel.entropy κ μ :=
  by
  rw [snd_eq]
  exact entropy_map_le _ hκ


-- @@ L424-429 expanded
lemma entropy_fst_le (κ : Kernel T (S × U)) [IsZeroOrMarkovKernel κ] (μ : Measure T)
    [IsZeroOrProbabilityMeasure μ] [FiniteSupport μ] (hκ : AEFiniteKernelSupport κ μ) :
    ProbabilityTheory.Kernel.entropy (fst κ) μ ≤ ProbabilityTheory.Kernel.entropy κ μ :=
  by
  rw [fst_eq]
  exact entropy_map_le _ hκ


-- @@ L431-431 verbatim
end ProbabilityTheory.Kernel
