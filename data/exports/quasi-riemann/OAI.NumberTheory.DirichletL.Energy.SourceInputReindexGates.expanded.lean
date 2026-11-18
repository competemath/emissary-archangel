import OAI.NumberTheory.DirichletL.Moments.SourceInputReindex
import OAI.NumberTheory.DirichletL.Moments.AllocatedRayDictionary
import OAI.NumberTheory.DirichletL.Moments.FirstSecondInputGates
import OAI.NumberTheory.DirichletL.Moments.FirstAnnularActiveInput
import OAI.NumberTheory.DirichletL.Moments.FirstChildProfileControl


-- @@ L7-7 verbatim
namespace OAI


-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L12-12 verbatim
namespace SevenEighths.CenteredMomentEnergySourceInputReindexGates

-- @@ L13-13 verbatim
open HeckeFamily CanonicalQuadraticSieve

-- @@ L14-14 verbatim
open CenteredMomentCommonRadialData CenteredMomentAmplificationChildInput

-- @@ L15-15 verbatim
open CenteredMomentSourceInputReindex CenteredMomentCommonAllocationSum

-- @@ L16-16 verbatim
open CenteredMomentCommonProfile CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform

-- @@ L17-17 verbatim
open CenteredMomentFirstSecondInputGates CenteredMomentOriginalCommonHarmonic

-- @@ L18-18 verbatim
open CenteredMomentFirstChildProfileControl CenteredMomentFirstAnnularInput

-- @@ L19-19 verbatim
open CenteredMomentAmplificationChildSourceCaps

-- @@ L20-20 verbatim
open CenteredMomentOriginalChildEnergy

-- @@ L21-21 verbatim
local notation "O" => HeckeFamily.O

-- @@ L22-22 verbatim
variable {α β : Type*} [Fintype α] [Fintype β]

-- @@ L23-23 verbatim
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _


-- @@ L25-26 verbatim
lemma mass_map (e : α≃β) (s : Input α) : mass (reindex e s)=mass s :=
  (controls_map e s).1


-- @@ L28-31 verbatim
lemma nominal_map (e : α≃β) (s : Input α) (K : ℝ) :
    nominal (reindex e s) K=nominal s K := by
  unfold nominal
  rw [volume_map]


-- @@ L33-42 verbatim
theorem ready_map (e : α≃β) (s : Input α) (R : Ideal O) (K Z ξ B : ℝ)
    (h : Ready s R K Z ξ B) : Ready (reindex e s) R K Z ξ B := by
  rcases h with ⟨hR0,hK,hV,hs0,hs,hq,hr,hn0,hn,hf0,hf⟩
  exact ⟨hR0,hK,by simpa only [volume_map] using hV,
    by simpa only [sourceRadius_map] using hs0,
    by simpa only [sourceRadius_map] using hs,hq,hr,
    by simpa only [nominal_map] using hn0,
    by simpa only [nominal_map] using hn,
    by simpa only [nominal_map] using hf0,
    by simpa only [nominal_map] using hf⟩


-- @@ L44-44 verbatim
section Dictionary

-- @@ L45-45 verbatim
variable (M : Ideal O) [NeZero M]

-- @@ L46-46 verbatim
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L47-47 verbatim
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)


-- @@ L49-56 verbatim
theorem matches_map (e : α≃β) (s : Input α) (η₀ : Character)
    (θ : α→RayQuotient.Characters M H) (w σ freq : α→ℝ)
    (W : ℝ→ℂ) (bslot Z : ℝ)
    (h : CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ freq W bslot Z) :
    CenteredMomentAllocatedRayDictionary.Matches M H hH (reindex e s) η₀
      (θ ∘ e.symm) (w ∘ e.symm) (σ ∘ e.symm) (freq ∘ e.symm) W bslot Z :=
  ⟨fun i I=>h.character (e.symm i) I,fun i y=>h.profile (e.symm i) y,
    fun i=>h.pool (e.symm i),fun i=>h.scale (e.symm i)⟩


-- @@ L58-66 verbatim
theorem matches_child (s : Input α) (η₀ : Character)
    (θ : α→RayQuotient.Characters M H) (w σ freq : α→ℝ)
    (W : ℝ→ℂ) (bslot Z : ℝ)
    (h : CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    CenteredMomentAllocatedRayDictionary.Matches M H hH (child s C R B τ t) η₀
      (fun i=>θ i.val) (fun i=>w i.val) (fun i=>σ i.val) (fun i=>freq i.val) W bslot Z :=
  ⟨fun i I=>h.character i.val I,fun i y=>h.profile i.val y,
    fun i=>h.pool i.val,fun i=>h.scale i.val⟩


-- @@ L68-76 verbatim
omit [Fintype α] [Fintype β] in
theorem imageInput_matches (e : α↪β) (T : Finset α) (s : Input T) (η₀ : Character)
    (θ : T→RayQuotient.Characters M H) (w σ freq : T→ℝ)
    (W : ℝ→ℂ) (bslot Z : ℝ)
    (h : CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ freq W bslot Z) :
    CenteredMomentAllocatedRayDictionary.Matches M H hH (imageInput e T s) η₀
      (θ ∘ (Finset.equivMap e T).symm) (w ∘ (Finset.equivMap e T).symm)
      (σ ∘ (Finset.equivMap e T).symm) (freq ∘ (Finset.equivMap e T).symm) W bslot Z :=
  matches_map M H hH (Finset.equivMap e T) s η₀ θ w σ freq W bslot Z h


-- @@ L78-90 verbatim
omit [Fintype β] in
theorem allocatedImage_matches (e : α↪β) (s : Input α) (η₀ : Character)
    (θ : α→RayQuotient.Characters M H) (w σ freq : α→ℝ)
    (W : ℝ→ℂ) (bslot Z : ℝ)
    (h : CenteredMomentAllocatedRayDictionary.Matches M H hH s η₀ θ w σ freq W bslot Z)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    CenteredMomentAllocatedRayDictionary.Matches M H hH (allocatedImage e s C R B τ t) η₀
      (fun i=>θ ((Finset.equivMap e (liveIndices B.val)).symm i).val)
      (fun i=>w ((Finset.equivMap e (liveIndices B.val)).symm i).val)
      (fun i=>σ ((Finset.equivMap e (liveIndices B.val)).symm i).val)
      (fun i=>freq ((Finset.equivMap e (liveIndices B.val)).symm i).val) W bslot Z :=
  imageInput_matches M H hH e (liveIndices B.val) (child s C R B τ t) η₀
    _ _ _ _ W bslot Z (matches_child M H hH s η₀ θ w σ freq W bslot Z h C R B τ t)

-- @@ L91-91 verbatim
end Dictionary


-- @@ L93-94 verbatim
theorem active_map (e : α≃β) (s : Input α) :
    activeInput (reindex e s)=reindex e (activeInput s) := rfl


-- @@ L96-101 verbatim
lemma allocationLabels_map (e : α≃β) (s : Input α) (C : Ideal O) :
    (allocationLabels s.pools C).image (tupleMap e)=
      allocationLabels (reindex e s).pools C := by
  unfold allocationLabels
  rw [←pools_map,Finset.image_image,Finset.image_image]
  congr 1


-- @@ L103-109 verbatim
lemma actualAllocations_map (e : α≃β) (s : Input α) (C : Ideal O) :
    (actualAllocations s.pools C).image (tupleMap e)=
      actualAllocations (reindex e s).pools C := by
  change ((allocationLabels s.pools C).filter (fun B=>finiteTupleProduct B=C)).image (tupleMap e)=
    (allocationLabels (reindex e s).pools C).filter (fun B=>finiteTupleProduct B=C)
  rw [←allocationLabels_map e s C,Finset.filter_image]
  simp only [tupleMap_product]


-- @@ L111-122 verbatim
def allocationEquiv (e : α≃β) (s : Input α) (C : Ideal O) :
    actualAllocations s.pools C ≃ actualAllocations (reindex e s).pools C where
  toFun B := ⟨tupleMap e B.val,by
    rw [←actualAllocations_map]
    exact Finset.mem_image.mpr ⟨B.val,B.property,rfl⟩⟩
  invFun B := ⟨(tupleMap e).symm B.val,by
    have hh : B.val∈(actualAllocations s.pools C).image (tupleMap e) := by
      simpa only [actualAllocations_map e s C] using B.property
    obtain ⟨v,hv,hvB⟩:=Finset.mem_image.mp hh
    simpa only [←hvB,Equiv.symm_apply_apply] using hv⟩
  left_inv B := Subtype.ext ((tupleMap e).symm_apply_apply B.val)
  right_inv B := Subtype.ext ((tupleMap e).apply_symm_apply B.val)


-- @@ L124-126 verbatim
@[simp] lemma allocationEquiv_val (e : α≃β) (s : Input α) (C : Ideal O)
    (B : actualAllocations s.pools C) :
    (allocationEquiv e s C B).val=tupleMap e B.val := rfl


-- @@ L128-138 verbatim
def liveEquiv (e : α≃β) (B : Tuple α) : liveIndices B ≃ liveIndices (tupleMap e B) where
  toFun i := ⟨e i.val,by
    simpa only [liveIndices,Finset.mem_filter,Finset.mem_univ,true_and,
      tupleMap_apply,Equiv.sumCongr_symm,Equiv.sumCongr_apply,Sum.map_inl,
      Equiv.symm_apply_apply] using (Finset.mem_filter.mp i.property).2⟩
  invFun j := ⟨e.symm j.val,by
    simpa only [liveIndices,Finset.mem_filter,Finset.mem_univ,true_and,
      tupleMap_apply,Equiv.sumCongr_symm,Equiv.sumCongr_apply,Sum.map_inl]
      using (Finset.mem_filter.mp j.property).2⟩
  left_inv i := Subtype.ext (e.symm_apply_apply i.val)
  right_inv j := Subtype.ext (e.apply_symm_apply j.val)


-- @@ L140-141 verbatim
@[simp] lemma liveEquiv_val (e : α≃β) (B : Tuple α) (i : liveIndices B) :
    (liveEquiv e B i).val=e i.val := rfl


-- @@ L143-144 verbatim
@[simp] lemma liveEquiv_symm_val (e : α≃β) (B : Tuple α)
    (j : liveIndices (tupleMap e B)) : ((liveEquiv e B).symm j).val=e.symm j.val := rfl


-- @@ L146-149 verbatim
theorem child_map (e : α≃β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    reindex (liveEquiv e B.val) (child s C R B τ t)=
      child (reindex e s) C R (allocationEquiv e s C B) τ t := rfl


-- @@ L151-155 verbatim
theorem child_mass_map (e : α≃β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    mass (child (reindex e s) C R (allocationEquiv e s C B) τ t)=
      mass (child s C R B τ t) := by
  exact mass_map (liveEquiv e B.val) (child s C R B τ t)


-- @@ L157-161 verbatim
theorem child_volume_map (e : α≃β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    volume (child (reindex e s) C R (allocationEquiv e s C B) τ t)=
      volume (child s C R B τ t) := by
  exact volume_map (liveEquiv e B.val) (child s C R B τ t)


-- @@ L163-167 verbatim
theorem child_normalized_map (e : α≃β) (s : Input α) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    childNormalizedGaussSource (reindex e s) C R seed (allocationEquiv e s C B) τ t W K=
      childNormalizedGaussSource s C R seed B τ t W K := by
  exact normalizedGaussSource_map (liveEquiv e B.val) (child s C R B τ t) (R*C) seed W K


-- @@ L169-174 verbatim
theorem active_allocation_pullback (e : α≃β) (s : Input α) (C : Ideal O)
    (B : actualAllocations (activeInput (reindex e s)).pools C) :
    ∃A : actualAllocations (activeInput s).pools C,
      (allocationEquiv e (activeInput s) C A).val=B.val := by
  exact ⟨(allocationEquiv e (activeInput s) C).symm B,
    congrArg Subtype.val ((allocationEquiv e (activeInput s) C).apply_symm_apply B)⟩


-- @@ L176-180 verbatim
omit [Fintype α] [Fintype β] in
theorem imageInput_ready (e : α↪β) (T : Finset α) (s : Input T)
    (R : Ideal O) (K Z ξ B : ℝ) (h : Ready s R K Z ξ B) :
    Ready (imageInput e T s) R K Z ξ B :=
  ready_map (Finset.equivMap e T) s R K Z ξ B h


-- @@ L182-187 verbatim
omit [Fintype β] in
theorem allocatedImage_ready (e : α↪β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t K Z ξ bound : ℝ)
    (h : Ready (child s C R B τ t) (R*C) K Z ξ bound) :
    Ready (allocatedImage e s C R B τ t) (R*C) K Z ξ bound :=
  imageInput_ready e (liveIndices B.val) (child s C R B τ t) (R*C) K Z ξ bound h


-- @@ L189-191 verbatim
omit [Fintype α] [Fintype β] in
lemma imageInput_mass (e : α↪β) (T : Finset α) (s : Input T) :
    mass (imageInput e T s)=mass s := mass_map (Finset.equivMap e T) s


-- @@ L193-197 verbatim
omit [Fintype β] in
lemma allocatedImage_mass (e : α↪β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    mass (allocatedImage e s C R B τ t)=mass (child s C R B τ t) :=
  imageInput_mass e (liveIndices B.val) (child s C R B τ t)


-- @@ L199-203 verbatim
omit [Fintype β] in
lemma allocatedImage_volume (e : α↪β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    volume (allocatedImage e s C R B τ t)=volume (child s C R B τ t) :=
  volume_map (Finset.equivMap e (liveIndices B.val)) (child s C R B τ t)


-- @@ L205-213 verbatim
lemma source_fields_map (e : α≃β) (s : Input α) :
    (reindex e s).η=s.η ∧ (reindex e s).m=s.m ∧ (reindex e s).A=s.A ∧
    (reindex e s).t=s.t ∧ (reindex e s).W₁=s.W₁ ∧ (reindex e s).W₂=s.W₂ ∧
    (reindex e s).X₁=s.X₁ ∧ (reindex e s).X₂=s.X₂ ∧
    (reindex e s).Y₁=s.Y₁ ∧ (reindex e s).Y₂=s.Y₂ ∧
    (reindex e s).lower=s.lower ∧ (reindex e s).upper=s.upper ∧
    (reindex e s).plain₁=s.plain₁ ∧ (reindex e s).plain₂=s.plain₂ ∧
    (reindex e s).rows=s.rows ∧ (reindex e s).weight=s.weight := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩


-- @@ L215-230 verbatim
theorem active_child_pullback (e : α≃β) (s : Input α) (C R : Ideal O)
    (B : actualAllocations (activeInput (reindex e s)).pools C) (τ : Character) (t : ℝ) :
    ∃A : actualAllocations (activeInput s).pools C,
      (allocationEquiv e (activeInput s) C A).val=B.val ∧
      mass (child (activeInput (reindex e s)) C R B τ t)=
        mass (child (activeInput s) C R A τ t) ∧
      volume (child (activeInput (reindex e s)) C R B τ t)=
        volume (child (activeInput s) C R A τ t) ∧
      ∀(seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ),
        childNormalizedGaussSource (activeInput (reindex e s)) C R seed B τ t W K=
          childNormalizedGaussSource (activeInput s) C R seed A τ t W K := by
  obtain ⟨A,hA⟩:=(allocationEquiv e (activeInput s) C).surjective B
  subst B
  exact ⟨A,rfl,child_mass_map e (activeInput s) C R A τ t,
    child_volume_map e (activeInput s) C R A τ t,
    fun seed W K=>child_normalized_map e (activeInput s) C R seed A τ t W K⟩


-- @@ L232-232 verbatim
end SevenEighths.CenteredMomentEnergySourceInputReindexGates


-- @@ L234-234 verbatim
end


-- @@ L236-236 verbatim
end OAI
