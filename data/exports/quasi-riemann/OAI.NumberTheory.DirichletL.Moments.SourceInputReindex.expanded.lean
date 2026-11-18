import OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput
import OAI.NumberTheory.DirichletL.Moments.OriginalCommonHarmonic


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentSourceInputReindex

-- @@ L10-10 verbatim
open HeckeFamily CanonicalQuadraticSieve

-- @@ L11-11 verbatim
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput

-- @@ L12-12 verbatim
open CenteredMomentFirstAmplificationChoice CenteredMomentOriginalChildEnergy

-- @@ L13-13 verbatim
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform

-- @@ L14-14 verbatim
open CenteredMomentCommonAllocationSum CenteredMomentCommonProfile

-- @@ L15-15 verbatim
local notation "O" => HeckeFamily.O

-- @@ L16-16 verbatim
variable {α β : Type*} [Fintype α] [Fintype β]

-- @@ L17-17 verbatim
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

-- @@ L18-18 verbatim
local instance : DecidableEq (α⊕Fin 2) := Classical.decEq _

-- @@ L19-19 verbatim
local instance : DecidableEq (β⊕Fin 2) := Classical.decEq _


-- @@ L21-69 verbatim
def reindex (e : α≃β) (s : Input α) : Input β where
  η := s.η
  m := s.m
  A := s.A
  t := s.t
  slots := fun i=>s.slots (e.symm i)
  prime := fun i=>s.prime (e.symm i)
  ν := fun i=>s.ν (e.symm i)
  W := fun i=>s.W (e.symm i)
  lo := fun i=>s.lo (e.symm i)
  hi := fun i=>s.hi (e.symm i)
  P := fun i=>s.P (e.symm i)
  lo_pos := fun i=>s.lo_pos (e.symm i)
  P_pos := fun i=>s.P_pos (e.symm i)
  support := fun i=>s.support (e.symm i)
  W₁ := s.W₁
  W₂ := s.W₂
  X₁ := s.X₁
  X₂ := s.X₂
  Y₁ := s.Y₁
  Y₂ := s.Y₂
  M := fun i=>s.M (e.symm i)
  M_ge_one := fun i=>s.M_ge_one (e.symm i)
  coefficient_bound := fun i=>s.coefficient_bound (e.symm i)
  b₁ := s.b₁
  b₂ := s.b₂
  support₁ := s.support₁
  support₂ := s.support₂
  X₁_pos := s.X₁_pos
  X₂_pos := s.X₂_pos
  Y₁_pos := s.Y₁_pos
  Y₂_pos := s.Y₂_pos
  same_product := s.same_product
  rows := s.rows
  weight := s.weight
  weight_nonneg := s.weight_nonneg
  plain₁ := s.plain₁
  plain₂ := s.plain₂
  plain₁_ne := s.plain₁_ne
  plain₂_ne := s.plain₂_ne
  coverage₁ := s.coverage₁
  coverage₂ := s.coverage₂
  ν_bound := fun i=>s.ν_bound (e.symm i)
  W_bound := fun i=>s.W_bound (e.symm i)
  lower := s.lower
  upper := s.upper
  lower_pos := s.lower_pos
  lower_le := fun i=>s.lower_le (e.symm i)
  upper_ge := fun i=>s.upper_ge (e.symm i)


-- @@ L71-72 verbatim
def tupleMap (e : α≃β) : Tuple α≃Tuple β :=
  (e.sumCongr (Equiv.refl (Fin 2))).arrowCongr (Equiv.refl (Ideal O))


-- @@ L74-76 verbatim
omit [Fintype α] [Fintype β] in
lemma tupleMap_apply (e : α≃β) (v : Tuple α) (j : β⊕Fin 2) :
    tupleMap e v j = v ((e.sumCongr (Equiv.refl (Fin 2))).symm j) := rfl


-- @@ L78-80 verbatim
lemma tupleMap_product (e : α≃β) (v : Tuple α) :
    finiteTupleProduct (tupleMap e v)=finiteTupleProduct v :=
  (e.sumCongr (Equiv.refl (Fin 2))).symm.prod_comp v


-- @@ L82-96 verbatim
lemma pools_map (e : α≃β) (s : Input α) :
    (Fintype.piFinset s.pools).image (tupleMap e) = Fintype.piFinset (reindex e s).pools := by
  ext v
  simp only [Finset.mem_image,Fintype.mem_piFinset]
  constructor
  · rintro ⟨w,hw,rfl⟩ j
    cases j with
    | inl i => exact hw (Sum.inl (e.symm i))
    | inr i => exact hw (Sum.inr i)
  · intro hv
    refine ⟨(tupleMap e).symm v,?_,(tupleMap e).apply_symm_apply v⟩
    intro j
    cases j with
    | inl i => simpa [tupleMap,Input.pools,reindex] using hv (Sum.inl (e i))
    | inr i => exact hv (Sum.inr i)


-- @@ L98-106 verbatim
lemma profile_map (e : α≃β) (s : Input α) (R seed : Ideal O) (v : Tuple α) :
    (original (reindex e s) R seed).profile (tupleMap e v) =
      (original s R seed).profile v := by
  simp only [OriginalData.profile,original,reindex,profileCoefficient,tupleMap_product,
    tupleMap_apply,Equiv.sumCongr_symm,Equiv.sumCongr_apply,Equiv.refl_symm,
    Equiv.refl_apply,Sum.map_inl,Sum.map_inr]
  congr 3
  exact e.symm.prod_comp (fun i=>s.ν i (v (Sum.inl i))*
    s.W i ((Ideal.absNorm (v (Sum.inl i)):ℝ)/s.P i))


-- @@ L108-115 verbatim
lemma columns_map (e : α≃β) (s : Input α) (R seed : Ideal O) :
    (original (reindex e s) R seed).columns=(original s R seed).columns := by
  unfold OriginalData.columns
  change finiteColumns (Fintype.piFinset (reindex e s).pools)=finiteColumns (Fintype.piFinset s.pools)
  rw [←pools_map,finiteColumns,Finset.image_image]
  congr 1
  funext v
  exact tupleMap_product e v


-- @@ L117-126 verbatim
lemma coefficient_map (e : α≃β) (s : Input α) (R seed : Ideal O) :
    (original (reindex e s) R seed).beta=(original s R seed).beta := by
  funext I
  unfold OriginalData.beta finiteColumnCoefficient
  change (∑v∈(Fintype.piFinset (reindex e s).pools).filter (fun v=>finiteTupleProduct v=I),
    (original (reindex e s) R seed).profile v)=_
  rw [←pools_map,Finset.filter_image]
  rw [Finset.sum_image (fun v _ w _ h => (tupleMap e).injective h)]
  simp only [tupleMap_product,profile_map]
  rfl


-- @@ L128-129 verbatim
lemma volume_map (e : α≃β) (s : Input α) : volume (reindex e s)=volume s := by
  simp only [volume,reindex,e.symm.prod_comp]


-- @@ L131-135 verbatim
lemma controls_map (e : α≃β) (s : Input α) :
    (∏i,(reindex e s).M i)=(∏i,s.M i) ∧
    (∏i,(reindex e s).lo i)=(∏i,s.lo i) ∧
    (∏i,(reindex e s).hi i)=(∏i,s.hi i) := by
  simp only [reindex,e.symm.prod_comp,and_self]


-- @@ L137-140 verbatim
lemma sourceRadius_map (e : α≃β) (s : Input α) :
    CenteredMomentOriginalCommonHarmonic.sourceRadius (reindex e s)=
      CenteredMomentOriginalCommonHarmonic.sourceRadius s := by
  simp only [CenteredMomentOriginalCommonHarmonic.sourceRadius,reindex,e.symm.prod_comp]


-- @@ L142-147 verbatim
theorem normalizedGaussSource_map (e : α≃β) (s : Input α) (R seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    normalizedGaussSource (reindex e s) R seed W K=normalizedGaussSource s R seed W K := by
  unfold normalizedGaussSource
  rw [columns_map,coefficient_map,volume_map]
  rfl


-- @@ L149-150 verbatim
def imageInput (e : α↪β) (T : Finset α) (s : Input T) : Input (T.map e) :=
  reindex (Finset.equivMap e T) s


-- @@ L152-155 verbatim
omit [Fintype α] [Fintype β] in
lemma imageInput_lo (e : α↪β) (T : Finset α) (s : Input T) (i : T) :
    (imageInput e T s).lo ((Finset.equivMap e T) i)=s.lo i := by
  simp only [imageInput,reindex,Equiv.symm_apply_apply]


-- @@ L157-160 verbatim
omit [Fintype α] [Fintype β] in
lemma imageInput_hi (e : α↪β) (T : Finset α) (s : Input T) (i : T) :
    (imageInput e T s).hi ((Finset.equivMap e T) i)=s.hi i := by
  simp only [imageInput,reindex,Equiv.symm_apply_apply]


-- @@ L162-166 verbatim
omit [Fintype α] [Fintype β] in
lemma imageInput_normalized (e : α↪β) (T : Finset α) (s : Input T)
    (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    normalizedGaussSource (imageInput e T s) R seed W K=normalizedGaussSource s R seed W K :=
  normalizedGaussSource_map (Finset.equivMap e T) s R seed W K


-- @@ L168-171 verbatim
def allocatedImage (e : α↪β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    Input ((liveIndices B.val).map e) :=
  imageInput e (liveIndices B.val) (child s C R B τ t)


-- @@ L173-187 verbatim
omit [Fintype β] in
lemma allocatedImage_ranges (e : α↪β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (lo hi : β→ℝ) (hlo : ∀i,s.lo i=lo (e i)) (hhi : ∀i,s.hi i=hi (e i)) :
    (∀j,(allocatedImage e s C R B τ t).lo j=lo j.val) ∧
    (∀j,(allocatedImage e s C R B τ t).hi j=hi j.val) := by
  constructor
  · intro j
    obtain ⟨i,rfl⟩:=(Finset.equivMap e (liveIndices B.val)).surjective j
    rw [allocatedImage,imageInput_lo]
    exact hlo i.val
  · intro j
    obtain ⟨i,rfl⟩:=(Finset.equivMap e (liveIndices B.val)).surjective j
    rw [allocatedImage,imageInput_hi]
    exact hhi i.val


-- @@ L189-195 verbatim
omit [Fintype β] in
theorem allocatedImage_normalized (e : α↪β) (s : Input α) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    normalizedGaussSource (allocatedImage e s C R B τ t) (R*C) seed W K =
      childNormalizedGaussSource s C R seed B τ t W K :=
  imageInput_normalized e (liveIndices B.val) (child s C R B τ t) (R*C) seed W K


-- @@ L197-197 verbatim
end SevenEighths.CenteredMomentSourceInputReindex


-- @@ L199-199 verbatim
end


-- @@ L201-201 verbatim
end OAI
