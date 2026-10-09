import OAI.Analysis.C0Absorption.Tags


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


-- @@ L14-14 verbatim
section GeneralC0

-- @@ L15-16 verbatim
variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [DiscreteTopology A] [DiscreteTopology B]


-- @@ L18-21 verbatim
def cfunOfTendsto (f : A → ℝ) (hf : Tendsto f cofinite (nhds 0)) : C₀(A,ℝ) where
  toFun := f
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by simpa only [cocompact_eq_cofinite] using hf


-- @@ L23-24 verbatim
theorem cfun_tendsto (f : C₀(A,ℝ)) : Tendsto f cofinite (nhds 0) := by
  simpa only [cocompact_eq_cofinite] using zero_at_infty f


-- @@ L26-27 verbatim
theorem cfun_norm_apply_le {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (f : C₀(A,ℝ)) (a : A) : |f a|≤‖f‖ := f.toBCF.norm_coe_le_norm a


-- @@ L29-31 verbatim
theorem cfun_norm_le {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (f : C₀(A,ℝ)) {r : ℝ} (hr : 0≤r) (h : ∀ a,|f a|≤r) : ‖f‖≤r :=
  (f.toBCF.norm_le hr).mpr h


-- @@ L33-34 verbatim
def cfunPull (j : A → B) (hj : Tendsto j cofinite cofinite) (f : C₀(B,ℝ)) : C₀(A,ℝ) :=
  cfunOfTendsto (fun a => f (j a)) ((cfun_tendsto f).comp hj)


-- @@ L36-37 verbatim
@[simp] theorem cfunPull_apply (j : A → B) (hj : Tendsto j cofinite cofinite) (f : C₀(B,ℝ)) (a : A) :
    cfunPull j hj f a=f (j a) := rfl


-- @@ L39-46 verbatim
def cfunPullL (j : A → B) (hj : Tendsto j cofinite cofinite) : C₀(B,ℝ) →L[ℝ] C₀(A,ℝ) :=
  LinearMap.mkContinuous
    { toFun := cfunPull j hj
      map_add' := by intro f g; ext a; rfl
      map_smul' := by intro c f; ext a; rfl } 1 (fun f => by
        change ‖cfunPull j hj f‖≤1*‖f‖
        rw [one_mul]
        exact cfun_norm_le _ (norm_nonneg _) (fun a => cfun_norm_apply_le f (j a)))


-- @@ L48-49 verbatim
@[simp] theorem cfunPullL_apply (j : A → B) (hj : Tendsto j cofinite cofinite) (f : C₀(B,ℝ)) (a : A) :
    cfunPullL j hj f a=f (j a) := rfl


-- @@ L51-51 verbatim
end GeneralC0


-- @@ L53-63 verbatim
theorem tendsto_sumElim_cofinite {A B : Type*} {X : Type*} (f : A → X) (g : B → X)
    (l : Filter X) (hf : Tendsto f cofinite l) (hg : Tendsto g cofinite l) :
    Tendsto (Sum.elim f g) cofinite l := by
  intro s hs
  have h1 : {a | f a∉s}.Finite := hf hs
  have h2 : {b | g b∉s}.Finite := hg hs
  apply ((h1.image Sum.inl).union (h2.image Sum.inr)).subset
  intro x hx
  cases x with
  | inl a => exact Or.inl ⟨a,hx,rfl⟩
  | inr b => exact Or.inr ⟨b,hx,rfl⟩


-- @@ L65-65 verbatim
abbrev BlockC0 := C₀(Label,ℝ)


-- @@ L67-67 verbatim
def inputRows : C0 →L[ℝ] C0 := cfunPullL rowIndex rowIndex_injective.tendsto_cofinite


-- @@ L69-69 verbatim
def inputBlocks : C0 →L[ℝ] BlockC0 := cfunPullL labelIndex labelIndex_injective.tendsto_cofinite


-- @@ L71-71 verbatim
@[simp] theorem inputRows_apply (x : C0) (i : ℕ) : inputRows x i=x (rowIndex i) := rfl

-- @@ L72-72 verbatim
@[simp] theorem inputBlocks_apply (x : C0) (γ : Label) : inputBlocks x γ=x (labelIndex γ) := rfl


-- @@ L74-77 verbatim
def joinInputs (x : C0 × BlockC0) : C0 :=
  cfunOfTendsto (fun k => Sum.elim x.1 x.2 (coordinateEnumeration.symm k))
    ((tendsto_sumElim_cofinite x.1 x.2 (nhds 0) (cfun_tendsto x.1) (cfun_tendsto x.2)).comp
      coordinateEnumeration.symm.injective.tendsto_cofinite)


-- @@ L79-82 verbatim
@[simp] theorem joinInputs_row (x : C0 × BlockC0) (i : ℕ) : joinInputs x (rowIndex i)=x.1 i := by
  change Sum.elim x.1 x.2 (coordinateEnumeration.symm (coordinateEnumeration (Sum.inl i)))=x.1 i
  rw [Equiv.symm_apply_apply]
  rfl


-- @@ L84-87 verbatim
@[simp] theorem joinInputs_block (x : C0 × BlockC0) (γ : Label) : joinInputs x (labelIndex γ)=x.2 γ := by
  change Sum.elim x.1 x.2 (coordinateEnumeration.symm (coordinateEnumeration (Sum.inr γ)))=x.2 γ
  rw [Equiv.symm_apply_apply]
  rfl


-- @@ L89-94 verbatim
theorem joinInputs_split (x : C0) : joinInputs (inputRows x,inputBlocks x)=x := by
  ext k
  obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
  cases a with
  | inl i => exact joinInputs_row _ i
  | inr γ => exact joinInputs_block _ γ


-- @@ L96-113 verbatim
theorem joinInputs_norm (x : C0 × BlockC0) : ‖joinInputs x‖=‖x‖ := by
  apply le_antisymm
  · apply cfun_norm_le _ (norm_nonneg x)
    intro k
    obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
    cases a with
    | inl i => exact (show |joinInputs x (rowIndex i)|≤‖x.1‖ by rw [joinInputs_row]; exact cfun_norm_apply_le _ _).trans (le_max_left _ _)
    | inr γ => exact (show |joinInputs x (labelIndex γ)|≤‖x.2‖ by rw [joinInputs_block]; exact cfun_norm_apply_le _ _).trans (le_max_right _ _)
  · rw [Prod.norm_def]
    apply max_le
    · apply cfun_norm_le _ (norm_nonneg _)
      intro i
      rw [← joinInputs_row x i]
      exact cfun_norm_apply_le _ _
    · apply cfun_norm_le _ (norm_nonneg _)
      intro γ
      rw [← joinInputs_block x γ]
      exact cfun_norm_apply_le _ _


-- @@ L115-138 verbatim
def inputCoordinates : (C0 × BlockC0) ≃ₗᵢ[ℝ] C0 where
  toFun := joinInputs
  invFun := fun x => (inputRows x,inputBlocks x)
  left_inv := by
    intro x
    apply Prod.ext <;> ext k
    · exact joinInputs_row x k
    · exact joinInputs_block x k
  right_inv := joinInputs_split
  map_add' := by
    intro x y
    ext k
    obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
    cases a with
    | inl i => simp only [show coordinateEnumeration (Sum.inl i)=rowIndex i from rfl,joinInputs_row,Prod.fst_add,ZeroAtInftyContinuousMap.add_apply]
    | inr γ => simp only [show coordinateEnumeration (Sum.inr γ)=labelIndex γ from rfl,joinInputs_block,Prod.snd_add,ZeroAtInftyContinuousMap.add_apply]
  map_smul' := by
    intro c x
    ext k
    obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
    cases a with
    | inl i => simp only [show coordinateEnumeration (Sum.inl i)=rowIndex i from rfl,joinInputs_row,ZeroAtInftyContinuousMap.smul_apply]; rfl
    | inr γ => simp only [show coordinateEnumeration (Sum.inr γ)=labelIndex γ from rfl,joinInputs_block,ZeroAtInftyContinuousMap.smul_apply]; rfl
  norm_map' := joinInputs_norm


-- @@ L140-141 verbatim
theorem labelLevel_tendsto : Tendsto Label.level cofinite cofinite :=
  Filter.Tendsto.cofinite_of_finite_preimage_singleton (fun lev => labels_at_level_finite lev)


-- @@ L143-144 verbatim
theorem labelRadius_tendsto (x : C0) : Tendsto (fun γ : Label => localRadius γ.level x) cofinite (nhds 0) :=
  (localRadius_tendsto x).comp labelLevel_tendsto


-- @@ L146-149 verbatim
theorem frozenCorrection_tendsto (W : FrozenWeights) (x : C0) :
    Tendsto (fun γ => frozenCorrection W γ x) cofinite (nhds 0) := by
  apply squeeze_zero_norm (fun γ => frozenCorrection_local W γ x) _
  simpa only [mul_zero] using (labelRadius_tendsto x).const_mul 4


-- @@ L151-152 verbatim
def frozenCorrectionC0 (W : FrozenWeights) (x : C0) : BlockC0 :=
  cfunOfTendsto (fun γ => frozenCorrection W γ x) (frozenCorrection_tendsto W x)


-- @@ L154-161 verbatim
def frozenCorrectionL (W : FrozenWeights) : C0 →L[ℝ] BlockC0 :=
  LinearMap.mkContinuous
    { toFun := frozenCorrectionC0 W
      map_add' := by intro x y; ext γ; exact map_add (frozenCorrection W γ) x y
      map_smul' := by intro c x; ext γ; exact map_smul (frozenCorrection W γ) c x }
    4 (fun x => by
      change ‖frozenCorrectionC0 W x‖≤4*‖x‖
      exact cfun_norm_le _ (mul_nonneg (by norm_num) (norm_nonneg _)) (fun γ => frozenCorrection_bound W γ x))


-- @@ L163-164 verbatim
@[simp] theorem frozenCorrectionL_apply (W : FrozenWeights) (x : C0) (γ : Label) :
    frozenCorrectionL W x γ=frozenCorrection W γ x := rfl


-- @@ L166-166 verbatim
def correctionC0 (s : C0Ball) : BlockC0 := frozenCorrectionL (stateWeights s) s.val


-- @@ L168-168 verbatim
@[simp] theorem correctionC0_apply (s : C0Ball) (γ : Label) : correctionC0 s γ=correction γ s := rfl


-- @@ L170-170 verbatim
end

-- @@ L171-171 verbatim
end C0Absorption


-- @@ L173-173 verbatim
end OAI
