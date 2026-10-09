import OAI.Analysis.C0Absorption.Frozen


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open Set Filter Topology

-- @@ L6-6 verbatim
open scoped NNReal BigOperators ZeroAtInfty

-- @@ L7-7 verbatim
open NormedSpace


-- @@ L9-9 verbatim
namespace C0Absorption

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
open Set Filter Topology

-- @@ L12-12 verbatim
open scoped NNReal BigOperators ZeroAtInfty


-- @@ L14-17 verbatim
def earlierRadiusCoordinates (lev : Level) : Finset ℕ :=
  match lev.2 with
  | 0 => ∅
  | n+1 => radiusCoordinates (lev.1,n)


-- @@ L19-21 verbatim
def correctionCoordinates (lev : Level) : Finset ℕ :=
  (Finset.range (levelJ lev) ∪ {rowIndex lev.1}) ∪
    (radiusCoordinates lev ∪ earlierRadiusCoordinates lev)


-- @@ L23-24 verbatim
theorem correctionCoordinates_nonempty (lev : Level) : (correctionCoordinates lev).Nonempty := by
  exact (radiusCoordinates_nonempty lev).mono (fun k hk => Finset.mem_union_right _ (Finset.mem_union_left _ hk))


-- @@ L26-27 verbatim
theorem correctionCoordinates_prefix (lev : Level) : Finset.range (levelJ lev) ⊆ correctionCoordinates lev :=
  fun _ hk => Finset.mem_union_left _ (Finset.mem_union_left _ hk)


-- @@ L29-30 verbatim
theorem correctionCoordinates_radius (lev : Level) : radiusCoordinates lev ⊆ correctionCoordinates lev :=
  fun _ hk => Finset.mem_union_right _ (Finset.mem_union_left _ hk)


-- @@ L32-33 verbatim
theorem correctionCoordinates_previous (i n : ℕ) : radiusCoordinates (i,n) ⊆ correctionCoordinates (i,n+1) :=
  fun _ hk => Finset.mem_union_right _ (Finset.mem_union_right _ hk)


-- @@ L35-36 verbatim
theorem correctionCoordinates_row (lev : Level) : rowIndex lev.1∈correctionCoordinates lev :=
  Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))


-- @@ L38-41 verbatim
theorem prefixRestrict_eq_of_agree {j : ℕ} {s t : C0Ball}
    (h : ∀ k<j,s.val k=t.val k) : prefixRestrict j s=prefixRestrict j t := by
  ext k
  exact h k k.isLt


-- @@ L43-51 verbatim
theorem finiteRadius_eq_of_agree {I : Finset ℕ} {x y : C0}
    (h : ∀ k∈I,x k=y k) : finiteRadius I x=finiteRadius I y := by
  unfold finiteRadius
  congr 1
  ext k
  rw [finiteProjection_apply,finiteProjection_apply]
  split_ifs with hk
  · exact h k hk
  · rfl


-- @@ L53-60 verbatim
theorem blockVector_eq_of_agree {lev : Level} {s t : C0Ball}
    (hp : ∀ k<levelJ lev,s.val k=t.val k)
    (hr : ∀ k∈radiusCoordinates lev,s.val k=t.val k) :
    blockVector lev s=blockVector lev t := by
  funext b
  have hb : prefixRestrict b.1 s=prefixRestrict b.1 t := prefixRestrict_eq_of_agree (fun k hk => hp k (lt_of_lt_of_le hk (by omega)))
  have he : localRadius lev s.val=localRadius lev t.val := finiteRadius_eq_of_agree hr
  simp only [blockVector,he,hb]


-- @@ L62-69 verbatim
theorem blockRow_eq_of_agree {lev : Level} {s t : C0Ball}
    (hp : ∀ k<levelJ lev,s.val k=t.val k)
    (hr : ∀ k∈radiusCoordinates lev,s.val k=t.val k) :
    blockRow lev s=blockRow lev t := by
  funext b
  have hb : prefixRestrict b.1 s=prefixRestrict b.1 t := prefixRestrict_eq_of_agree (fun k hk => hp k (lt_of_lt_of_le hk (by omega)))
  have he : localRadius lev s.val=localRadius lev t.val := finiteRadius_eq_of_agree hr
  simp only [blockRow,he,hb]


-- @@ L71-80 verbatim
theorem state_rowScalar_eq_of_agree {lev : Level} {s t : C0Ball}
    (hp : ∀ k<levelJ lev,s.val k=t.val k)
    (hr : ∀ k∈radiusCoordinates lev,s.val k=t.val k) :
    rowScalar (stateWeights s) lev s.val=rowScalar (stateWeights t) lev t.val := by
  simp only [rowScalar_apply,stateWeights]
  apply Finset.sum_congr rfl
  intro b _
  have hb : blockInput lev s.val b=blockInput lev t.val b :=
    hr _ (Finset.mem_union_right _ (mem_blockCoordinates.mpr ⟨blockLabel lev b,rfl,rfl⟩))
  rw [blockRow_eq_of_agree hp hr,hb]


-- @@ L82-102 verbatim
theorem correction_eq_of_agree (γ : Label) {s t : C0Ball}
    (h : ∀ k∈correctionCoordinates γ.level,s.val k=t.val k) : correction γ s=correction γ t := by
  have hp : ∀ k<levelJ γ.level,s.val k=t.val k := fun k hk => h k (correctionCoordinates_prefix γ.level (Finset.mem_range.mpr hk))
  have hr : ∀ k∈radiusCoordinates γ.level,s.val k=t.val k := fun k hk => h k (correctionCoordinates_radius γ.level hk)
  have hv := blockVector_eq_of_agree hp hr
  have ha := state_rowScalar_eq_of_agree hp hr
  have ha' : previousScalar (stateWeights s) γ.level s.val=previousScalar (stateWeights t) γ.level t.val := by
    rcases γ with ⟨⟨i,n⟩,j,ξ⟩
    cases n with
    | zero => exact h _ (correctionCoordinates_row (i,0))
    | succ n =>
      apply state_rowScalar_eq_of_agree
      · intro k hk
        apply hp k
        simp only [levelJ] at hk ⊢
        omega
      · intro k hk
        exact h k (correctionCoordinates_previous i n hk)
  change blockVector γ.level s ⟨γ.band,γ.tag⟩*(previousScalar (stateWeights s) γ.level s.val-rowScalar (stateWeights s) γ.level s.val)=
    blockVector γ.level t ⟨γ.band,γ.tag⟩*(previousScalar (stateWeights t) γ.level t.val-rowScalar (stateWeights t) γ.level t.val)
  rw [hv,ha,ha']


-- @@ L104-105 verbatim
def correctionBase (γ : Label) : Cube (correctionCoordinates γ.level) → ℝ :=
  correction γ ∘ cubeExtend (correctionCoordinates γ.level)


-- @@ L107-112 verbatim
theorem correctionBase_restrict (γ : Label) (s : C0Ball) :
    correctionBase γ (cubeRestrict (correctionCoordinates γ.level) s)=correction γ s := by
  apply correction_eq_of_agree
  intro k hk
  change extendFinite _ _ k=s.val k
  simp only [extendFinite_apply,hk,↓reduceDIte,cubeRestrict]


-- @@ L114-115 verbatim
theorem correctionBase_bound (γ : Label) (x : Cube (correctionCoordinates γ.level)) : |correctionBase γ x|≤4 :=
  correction_bound γ _


-- @@ L117-118 verbatim
theorem correctionBase_lipschitz (γ : Label) : LipschitzWith correctionL (correctionBase γ) := by
  simpa only [mul_one,correctionBase] using (correction_lipschitz γ).comp (cubeExtend_lipschitz (correctionCoordinates γ.level))


-- @@ L120-130 verbatim
def concreteBases : CylinderBases Label where
  coordinates := fun γ => correctionCoordinates γ.level
  coordinates_nonempty := fun γ => correctionCoordinates_nonempty γ.level
  band := fun γ => γ.band.val
  ell := ell
  ell_pos := ell_pos
  base := correctionBase
  A := 4
  L0 := correctionL
  base_sup := correctionBase_bound
  base_lipschitz := correctionBase_lipschitz


-- @@ L132-132 verbatim
end

-- @@ L133-133 verbatim
end C0Absorption


-- @@ L135-135 verbatim
namespace C0Absorption

-- @@ L136-136 verbatim
noncomputable section

-- @@ L137-137 verbatim
open Set Filter Topology

-- @@ L138-138 verbatim
open scoped NNReal BigOperators ZeroAtInfty


-- @@ L140-141 verbatim
def fullTag (γ : Label) (k : ℕ) : Icc (-1 : ℝ) 1 :=
  if h : k<γ.band.val then bandPoint γ.band γ.tag ⟨k,h⟩ else ⟨0,by norm_num⟩


-- @@ L143-143 verbatim
theorem band_le_level (γ : Label) : γ.band.val≤levelJ γ.level := Nat.le_of_lt_succ γ.band.isLt


-- @@ L145-155 verbatim
theorem tag_support_base (γ : Label) (k : correctionCoordinates γ.level) (hk : k.val<γ.band.val) :
    ∀ x∈tsupport (correctionBase γ), dist (x k) (fullTag γ k.val)≤2*dyadic γ.band := by
  have hc : IsClosed {x : Cube (correctionCoordinates γ.level) | dist (x k) (fullTag γ k.val)≤2*dyadic γ.band} :=
    isClosed_le ((continuous_apply k).dist continuous_const) continuous_const
  apply closure_minimal _ hc
  intro x hx
  have hb := correction_band_support (γ := γ) (s := cubeExtend (correctionCoordinates γ.level) x) hx
  have hh : dist (prefixRestrict γ.band (cubeExtend (correctionCoordinates γ.level) x) ⟨k.val,hk⟩)
      (bandPoint γ.band γ.tag ⟨k.val,hk⟩) ≤ 2*dyadic γ.band :=
    (dist_le_pi_dist _ _ ⟨k.val,hk⟩).trans hb
  simpa only [Set.mem_ofPred_eq,prefixRestrict,cubeExtend,extendFinite_apply,k.property,↓reduceDIte,fullTag,hk,Subtype.dist_eq] using hh


-- @@ L157-162 verbatim
def concreteTagLocalization : TagLocalization concreteBases where
  tag := fullTag
  contains_prefix := fun γ _index hk => correctionCoordinates_prefix γ.level
    (Finset.mem_range.mpr ((Finset.mem_range.mp hk).trans_le (band_le_level γ)))
  ell_tendsto := ell_tendsto
  base_support := tag_support_base


-- @@ L164-164 verbatim
def firstRadiusCoordinate (lev : Level) : ℕ := (radiusCoordinates lev).min' (radiusCoordinates_nonempty lev)


-- @@ L166-167 verbatim
theorem firstRadiusCoordinate_mem (lev : Level) : firstRadiusCoordinate lev∈radiusCoordinates lev :=
  Finset.min'_mem _ _


-- @@ L169-170 verbatim
theorem firstRadiusCoordinate_le (lev : Level) {k : ℕ} (hk : k∈radiusCoordinates lev) :
    firstRadiusCoordinate lev≤k := Finset.min'_le _ _ hk


-- @@ L172-177 verbatim
theorem boundedLevels_finite (j : ℕ) : {lev : Level | levelJ lev≤j}.Finite := by
  apply ((Set.finite_Iic j).prod (Set.finite_Iic j)).subset
  intro lev h
  change lev.1≤j ∧ lev.2≤j
  change lev.1+lev.2+2≤j at h
  omega


-- @@ L179-184 verbatim
theorem labels_at_level_finite (lev : Level) : {γ : Label | γ.level=lev}.Finite := by
  apply (Set.finite_range (blockLabel lev)).subset
  rintro ⟨μ,j,ξ⟩ h
  change μ=lev at h
  cases h
  exact ⟨⟨j,ξ⟩,rfl⟩


-- @@ L186-189 verbatim
theorem labels_over_finite {F : Set Level} (hF : F.Finite) : {γ : Label | γ.level∈F}.Finite := by
  apply (hF.biUnion (fun lev _ => labels_at_level_finite lev)).subset
  intro γ hγ
  exact Set.mem_iUnion.mpr ⟨γ.level,Set.mem_iUnion.mpr ⟨hγ,rfl⟩⟩


-- @@ L191-199 verbatim
theorem bounded_or_early_finite (j N : ℕ) :
    {γ : Label | γ.band.val≤j ∧ (γ.band.val=levelJ γ.level ∨ firstRadiusCoordinate γ.level≤N)}.Finite := by
  let F : Set Level := {lev | levelJ lev≤j} ∪ {lev | ∃ k≤N,k∈radiusCoordinates lev}
  have hF : F.Finite := (boundedLevels_finite j).union (radius_finite_exceptions N)
  apply (labels_over_finite hF).subset
  intro γ hγ
  rcases hγ.2 with ht|he
  · exact Or.inl (by change levelJ γ.level≤j; rw [← ht]; exact hγ.1)
  · exact Or.inr ⟨firstRadiusCoordinate γ.level,he,firstRadiusCoordinate_mem _⟩


-- @@ L201-214 verbatim
theorem radius_support_base (γ : Label) (ht : γ.band.val≠levelJ γ.level) (N : ℕ)
    (hN : N<firstRadiusCoordinate γ.level) :
    ∀ x∈tsupport (correctionBase γ), ell γ.band≤tau N (cubeExtend (correctionCoordinates γ.level) x).val := by
  have hc : Continuous (fun x : Cube (correctionCoordinates γ.level) =>
      tau N (cubeExtend (correctionCoordinates γ.level) x).val) :=
    (tau_lipschitz N).continuous.comp (continuous_subtype_val.comp (cubeExtend_lipschitz _).continuous)
  apply closure_minimal _ (isClosed_le continuous_const hc)
  intro x hx
  have hb : ell γ.band≤localRadius γ.level (cubeExtend (correctionCoordinates γ.level) x).val :=
    correction_radius_support hx (lt_of_le_of_ne (band_le_level γ) ht)
  apply hb.trans
  apply finiteRadius_le_tau N
  intro k hk
  exact hN.trans_le (firstRadiusCoordinate_le γ.level hk)


-- @@ L216-220 verbatim
def concreteRadiusLocalization : RadiusLocalization concreteBases where
  terminal := fun γ => γ.band.val=levelJ γ.level
  firstCoordinate := fun γ => firstRadiusCoordinate γ.level
  finite_exceptions := bounded_or_early_finite
  base_radius := radius_support_base


-- @@ L222-222 verbatim
abbrev ConcreteSpace := SourceSpace concreteBases


-- @@ L224-225 verbatim
theorem concrete_noLinearC0 : NoLinearC0 ConcreteSpace :=
  source_noLinearC0 concreteTagLocalization concreteRadiusLocalization


-- @@ L227-227 verbatim
end

-- @@ L228-228 verbatim
end C0Absorption


-- @@ L230-230 verbatim
end OAI
