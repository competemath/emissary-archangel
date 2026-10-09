import OAI.Analysis.DiamondDistortion.ModelMaps


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u v


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators Classical Topology

-- @@ L9-9 verbatim
open Set


-- @@ L11-11 verbatim
namespace DiamondDistortion


-- @@ L13-13 verbatim
open scoped ENNReal


-- @@ L15-15 verbatim
namespace EquivalentNorm

-- @@ L16-16 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

-- @@ L17-22 verbatim
structure Data (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  seminorm : Seminorm ℝ E
  lowerConstant : ℝ
  upperConstant : ℝ
  lower : ∀ v,‖v‖ ≤ lowerConstant*seminorm v
  upper : ∀ v,seminorm v ≤ upperConstant*‖v‖

-- @@ L23-23 verbatim
namespace Data

-- @@ L24-24 verbatim
variable (A : Data E)

-- @@ L25-28 verbatim
lemma separates (v : E) (hv : A.seminorm v=0) : v=0 := by
  have hh := A.lower v
  rw [hv,mul_zero] at hh
  exact norm_le_zero_iff.mp hh


-- @@ L30-30 verbatim
def Space (_A : Data E) := E

-- @@ L31-31 verbatim
instance : AddCommGroup A.Space := inferInstanceAs (AddCommGroup E)

-- @@ L32-32 verbatim
instance : Module ℝ A.Space := inferInstanceAs (Module ℝ E)

-- @@ L33-34 verbatim
instance : NormedAddCommGroup A.Space := AddGroupNorm.toNormedAddCommGroup
  { A.seminorm.toAddGroupSeminorm with eq_zero_of_map_eq_zero' := A.separates }

-- @@ L35-36 verbatim
instance : NormedSpace ℝ A.Space where
  norm_smul_le t v := le_of_eq (A.seminorm.smul' t v)


-- @@ L38-38 verbatim
def of (v : E) : A.Space := v

-- @@ L39-39 verbatim
def val (v : A.Space) : E := v

-- @@ L40-40 verbatim
@[simp] lemma norm_of (v : E) : ‖A.of v‖=A.seminorm v := rfl


-- @@ L42-42 verbatim
def algebraEquiv : A.Space ≃ₗ[ℝ] E := { LinearEquiv.refl ℝ E with }

-- @@ L43-44 verbatim
def equiv : A.Space ≃L[ℝ] E :=
  A.algebraEquiv.toContinuousLinearEquivOfBounds A.lowerConstant A.upperConstant A.lower A.upper

-- @@ L45-45 verbatim
lemma equiv_apply (v : A.Space) : A.equiv v=A.val v := rfl

-- @@ L46-46 verbatim
lemma equiv_symm_apply (v : E) : A.equiv.symm v=A.of v := rfl

-- @@ L47-50 verbatim
def uniformEquiv : A.Space ≃ᵤ E where
  toEquiv := A.equiv.toEquiv
  uniformContinuous_toFun := A.equiv.toContinuousLinearMap.uniformContinuous
  uniformContinuous_invFun := A.equiv.symm.toContinuousLinearMap.uniformContinuous

-- @@ L51-52 verbatim
instance [CompleteSpace E] : CompleteSpace A.Space :=
  A.uniformEquiv.completeSpace_iff.mpr inferInstance

-- @@ L53-53 verbatim
end Data

-- @@ L54-54 verbatim
end EquivalentNorm


-- @@ L56-56 verbatim
namespace PathModel

-- @@ L57-57 verbatim
open RecursiveModel

-- @@ L58-73 verbatim
lemma quadratic_l2 (h : ℕ) (v : L2 h) :
    ‖v‖ ≤ (Real.sqrt 2*(h+1:ℝ))*cost 2 h v := by
  apply (presentation 2 h).bound v (by positivity : (0:ℝ) ≤ Real.sqrt 2*(h+1:ℝ))
  intro d hd
  change d.fst+path h d.snd=v at hd
  rw [← hd]
  have hb := (norm_add_le d.fst (path h d.snd)).trans (add_le_add le_rfl (path_norm h d.snd))
  have hhn : 1 ≤ (h+1:ℝ) := by linarith [Nat.cast_nonneg (α := ℝ) h]
  have hab : ‖d.fst‖+‖d.snd‖ ≤ Real.sqrt 2*‖d‖ := by
    rw [WithLp.prod_norm_eq_of_L2]
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt (by norm_num),Real.sq_sqrt (by positivity)]
    nlinarith [sq_nonneg (‖d.fst‖-‖d.snd‖)]
  have hc : ‖d.fst‖+(h+1:ℝ)*‖d.snd‖ ≤ (h+1:ℝ)*(‖d.fst‖+‖d.snd‖) := by
    nlinarith [norm_nonneg d.fst]
  exact (hb.trans hc).trans ((mul_le_mul_of_nonneg_left hab (by positivity)).trans_eq (by ring))


-- @@ L75-81 verbatim
/-- The original underlying ℓ² space endowed with its literal infimal path cost. -/
def linearFullData (h : ℕ) : EquivalentNorm.Data (L2 h) where
  seminorm := cost 1 h
  lowerConstant := h+1
  upperConstant := 1
  lower := linear_l2 h
  upper v := by simpa only [one_mul] using linear_le_norm h v

-- @@ L82-87 verbatim
def quadraticFullData (h : ℕ) : EquivalentNorm.Data (L2 h) where
  seminorm := cost 2 h
  lowerConstant := Real.sqrt 2*(h+1)
  upperConstant := 1
  lower := quadratic_l2 h
  upper v := by simpa only [one_mul] using quadratic_le_norm h v


-- @@ L89-89 verbatim
abbrev LinearComponent (h : ℕ) := (linearFullData h).Space

-- @@ L90-90 verbatim
abbrev QuadraticComponent (h : ℕ) := (quadraticFullData h).Space

-- @@ L91-91 verbatim
abbrev FullLinearSpace := lp (fun h : ℕ => LinearComponent (h+1)) 2

-- @@ L92-92 verbatim
abbrev FullQuadraticSpace := lp (fun h : ℕ => QuadraticComponent (h+1)) 2

-- @@ L93-93 verbatim
end PathModel


-- @@ L95-95 verbatim
namespace CoordinateCompletion.Data

-- @@ L96-97 verbatim
variable {ι E : Type*} (A : CoordinateCompletion.Data ι)
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]


-- @@ L99-101 verbatim
def finiteIsometry (j : (ι →₀ ℝ) →ₗ[ℝ] E) (hj : ∀ v,‖j v‖=A.seminorm v) : A.Finite →ₗᵢ[ℝ] E where
  toLinearMap := j
  norm_map' := hj


-- @@ L103-104 verbatim
def completionMap (j : (ι →₀ ℝ) →ₗ[ℝ] E) (hj : ∀ v,‖j v‖=A.seminorm v) : A.Space →L[ℝ] E :=
  (A.finiteIsometry j hj).toContinuousLinearMap.extend UniformSpace.Completion.toComplL

-- @@ L105-108 verbatim
lemma completionMap_coe (j : (ι →₀ ℝ) →ₗ[ℝ] E) (hj : ∀ v,‖j v‖=A.seminorm v) (v : A.Finite) :
    A.completionMap j hj v=j (A.array v) :=
  ContinuousLinearMap.extend_eq _ UniformSpace.Completion.denseRange_coe
    (UniformSpace.Completion.isUniformInducing_coe _) v

-- @@ L109-113 verbatim
lemma completionMap_norm (j : (ι →₀ ℝ) →ₗ[ℝ] E) (hj : ∀ v,‖j v‖=A.seminorm v) (x : A.Space) :
    ‖A.completionMap j hj x‖=‖x‖ := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (A.completionMap j hj).continuous.norm continuous_norm
  | ih v => rw [A.completionMap_coe,UniformSpace.Completion.norm_coe]; exact hj (A.array v)


-- @@ L115-117 verbatim
def completionIsometry (j : (ι →₀ ℝ) →ₗ[ℝ] E) (hj : ∀ v,‖j v‖=A.seminorm v) : A.Space →ₗᵢ[ℝ] E where
  toLinearMap := (A.completionMap j hj).toLinearMap
  norm_map' := A.completionMap_norm j hj

-- @@ L118-128 verbatim
lemma completionMap_surjective (j : (ι →₀ ℝ) →ₗ[ℝ] E) (hj : ∀ v,‖j v‖=A.seminorm v)
    (hdense : DenseRange j) : Function.Surjective (A.completionIsometry j hj) := by
  have hclosed := (A.completionIsometry j hj).isometry.isClosedEmbedding.isClosed_range
  have hsubset : Set.range j ⊆ Set.range (A.completionIsometry j hj) := by
    rintro _ ⟨v,rfl⟩
    refine ⟨A.embedding v,?_⟩
    exact A.completionMap_coe j hj (A.finite v)
  have hwhole : Set.univ ⊆ Set.range (A.completionIsometry j hj) := by
    rw [← hdense.closure_range]
    exact closure_minimal hsubset hclosed
  exact fun y => hwhole (Set.mem_univ y)

-- @@ L129-131 verbatim
def completionEquiv (j : (ι →₀ ℝ) →ₗ[ℝ] E) (hj : ∀ v,‖j v‖=A.seminorm v)
    (hdense : DenseRange j) : A.Space ≃ₗᵢ[ℝ] E :=
  LinearIsometryEquiv.ofSurjective (A.completionIsometry j hj) (A.completionMap_surjective j hj hdense)

-- @@ L132-132 verbatim
end CoordinateCompletion.Data


-- @@ L134-134 verbatim
namespace RecursiveModel

-- @@ L135-135 verbatim
variable {E : ℕ → Type*} [∀ h,NormedAddCommGroup (E h)] [∀ h,NormedSpace ℝ (E h)]

-- @@ L136-146 verbatim
/-- The actual outer Hilbert sum of the component embeddings. -/
def outerEmbedding (j : ∀ h,Vec (h+1) →ₗ[ℝ] E h) : ForestVec →ₗ[ℝ] lp E 2 where
  toFun v := ⟨fun h => j h (components v h),(memℓp_zero (by
    apply (v.support.image Sigma.fst).finite_toSet.subset
    intro h hh
    change j h (components v h) ≠ 0 at hh
    by_contra hn
    rw [components_zero v h hn,map_zero] at hh
    exact hh rfl)).of_exponent_ge bot_le⟩
  map_add' v w := by ext h; simp only [map_add,DFinsupp.add_apply,lp.coeFn_add,Pi.add_apply]
  map_smul' c v := by ext h; simp only [map_smul,DFinsupp.smul_apply,lp.coeFn_smul,Pi.smul_apply,RingHom.id_apply]

-- @@ L147-148 verbatim
lemma outerEmbedding_apply (j : ∀ h,Vec (h+1) →ₗ[ℝ] E h) (v : ForestVec) (h : ℕ) :
    outerEmbedding j v h=j h (components v h) := rfl

-- @@ L149-156 verbatim
lemma outerEmbedding_norm (j : ∀ h,Vec (h+1) →ₗ[ℝ] E h)
    (s : ∀ h,Seminorm ℝ (Vec (h+1))) (hj : ∀ h v,‖j h v‖=s h v) (v : ForestVec) :
    ‖outerEmbedding j v‖=outerSeminorm s v := by
  change ‖outerEmbedding j v‖=‖finiteLp 2 (outerValues s v)‖
  have he (h : ℕ) : ‖outerEmbedding j v h‖=‖finiteLp 2 (outerValues s v) h‖ := by
    rw [outerEmbedding_apply,hj,finiteLp_apply,outerValues_apply,Real.norm_eq_abs,abs_of_nonneg (apply_nonneg _ _)]
  exact le_antisymm (lp.norm_mono (by norm_num) (fun h => (he h).le))
    (lp.norm_mono (by norm_num) (fun h => (he h).ge))

-- @@ L157-164 verbatim
lemma outerEmbedding_single (j : ∀ h,Vec (h+1) →ₗ[ℝ] E h) (h : ℕ) (v : Vec (h+1)) :
    outerEmbedding j (components.symm (DFinsupp.single h v))=lp.single 2 h (j h v) := by
  ext i
  rw [outerEmbedding_apply,LinearEquiv.apply_symm_apply]
  by_cases he : h=i
  · subst i
    rw [DFinsupp.single_eq_same,lp.single_apply_self]
  · rw [DFinsupp.single_eq_of_ne (Ne.symm he),map_zero,lp.single_apply_ne _ _ _ (Ne.symm he)]

-- @@ L165-179 verbatim
lemma outerEmbedding_dense (j : ∀ h,Vec (h+1) →ₗ[ℝ] E h) (hdense : ∀ h,DenseRange (j h)) :
    DenseRange (outerEmbedding j) := by
  let K := (LinearMap.range (outerEmbedding j)).topologicalClosure
  have hK : IsClosed (K : Set (lp E 2)) := (LinearMap.range (outerEmbedding j)).isClosed_topologicalClosure
  have hfinite (h : ℕ) (v : Vec (h+1)) : lp.single 2 h (j h v) ∈ K := by
    apply subset_closure
    exact ⟨components.symm (DFinsupp.single h v),outerEmbedding_single j h v⟩
  have hsingle (h : ℕ) (x : E h) : lp.single 2 h x ∈ K := by
    induction x using (hdense h).induction_on with
    | hp => exact hK.preimage (lp.singleContinuousLinearMap (𝕜 := ℝ) (E := E) (p := 2) h).continuous
    | ih v => exact hfinite h v
  intro x
  change x ∈ K
  apply hK.mem_of_tendsto (lp.hasSum_single (by norm_num : (2:ℝ≥0∞) ≠ ⊤) x)
  exact Filter.Eventually.of_forall (fun S => K.sum_mem (fun h _ => hsingle h (x h)))

-- @@ L180-180 verbatim
end RecursiveModel


-- @@ L182-182 verbatim
namespace FiniteLpDensity

-- @@ L183-183 verbatim
variable {ι : Type*} (p : ℝ≥0∞) [Fact (1 ≤ p)]

-- @@ L184-184 verbatim
open RecursiveModel

-- @@ L185-188 verbatim
def embedding : (ι →₀ ℝ) →ₗ[ℝ] lp (fun _ : ι => ℝ) p where
  toFun := finiteLp p
  map_add' := finiteLp_add p
  map_smul' := finiteLp_smul p

-- @@ L189-200 verbatim
lemma dense (hp : p ≠ ⊤) : DenseRange (embedding (ι := ι) p) := by
  let K := (LinearMap.range (embedding (ι := ι) p)).topologicalClosure
  have hK : IsClosed (K : Set (lp (fun _ : ι => ℝ) p)) := (LinearMap.range (embedding (ι := ι) p)).isClosed_topologicalClosure
  have hs (i : ι) (c : ℝ) : lp.single p i c ∈ K := by
    apply subset_closure
    refine ⟨Finsupp.single i c,?_⟩
    ext k
    simp only [embedding,LinearMap.coe_mk,AddHom.coe_mk,finiteLp_apply,Finsupp.single_apply,lp.single_apply,Pi.single_apply,eq_comm]
  intro x
  change x ∈ K
  apply hK.mem_of_tendsto (lp.hasSum_single hp x)
  exact Filter.Eventually.of_forall (fun S => K.sum_mem (fun i _ => hs i (x i)))

-- @@ L201-201 verbatim
end FiniteLpDensity


-- @@ L203-203 verbatim
namespace EquivalentNorm.Data

-- @@ L204-204 verbatim
open RecursiveModel

-- @@ L205-205 verbatim
variable {ι : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)] (A : EquivalentNorm.Data (lp (fun _ : ι => ℝ) p))

-- @@ L206-207 verbatim
def coordinateEmbedding : (ι →₀ ℝ) →ₗ[ℝ] A.Space :=
  A.algebraEquiv.symm.toLinearMap.comp (FiniteLpDensity.embedding p)

-- @@ L208-209 verbatim
lemma coordinateEmbedding_norm (v : ι →₀ ℝ) :
    ‖A.coordinateEmbedding v‖=A.seminorm (finiteLp p v) := rfl

-- @@ L210-216 verbatim
lemma coordinateEmbedding_dense (hp : p ≠ ⊤) : DenseRange A.coordinateEmbedding := by
  intro x
  have hh (z : lp (fun _ : ι => ℝ) p) : A.equiv.symm z ∈ closure (range A.coordinateEmbedding) := by
    induction z using (FiniteLpDensity.dense (ι := ι) p hp).induction_on with
    | hp => exact isClosed_closure.preimage A.equiv.symm.continuous
    | ih v => exact subset_closure ⟨v,rfl⟩
  exact hh (A.val x)

-- @@ L217-217 verbatim
end EquivalentNorm.Data


-- @@ L219-219 verbatim
namespace PathModel

-- @@ L220-220 verbatim
open RecursiveModel

-- @@ L221-222 verbatim
def linearFullEmbedding : ForestVec →ₗ[ℝ] FullLinearSpace :=
  outerEmbedding (fun h => (linearFullData (h+1)).coordinateEmbedding)

-- @@ L223-224 verbatim
def quadraticFullEmbedding : ForestVec →ₗ[ℝ] FullQuadraticSpace :=
  outerEmbedding (fun h => (quadraticFullData (h+1)).coordinateEmbedding)

-- @@ L225-226 verbatim
lemma linearFullEmbedding_norm (v : ForestVec) : ‖linearFullEmbedding v‖=linearForestSeminorm v :=
  outerEmbedding_norm _ _ (fun h v => (linearFullData (h+1)).coordinateEmbedding_norm v) v

-- @@ L227-228 verbatim
lemma quadraticFullEmbedding_norm (v : ForestVec) : ‖quadraticFullEmbedding v‖=quadraticForestSeminorm v :=
  outerEmbedding_norm _ _ (fun h v => (quadraticFullData (h+1)).coordinateEmbedding_norm v) v

-- @@ L229-230 verbatim
lemma linearFullEmbedding_dense : DenseRange linearFullEmbedding :=
  outerEmbedding_dense _ (fun h => (linearFullData (h+1)).coordinateEmbedding_dense (by norm_num))

-- @@ L231-232 verbatim
lemma quadraticFullEmbedding_dense : DenseRange quadraticFullEmbedding :=
  outerEmbedding_dense _ (fun h => (quadraticFullData (h+1)).coordinateEmbedding_dense (by norm_num))


-- @@ L234-235 verbatim
def linearFullEquiv : linearData.Space ≃ₗᵢ[ℝ] FullLinearSpace :=
  linearData.completionEquiv linearFullEmbedding linearFullEmbedding_norm linearFullEmbedding_dense

-- @@ L236-237 verbatim
def quadraticFullEquiv : quadraticData.Space ≃ₗᵢ[ℝ] FullQuadraticSpace :=
  quadraticData.completionEquiv quadraticFullEmbedding quadraticFullEmbedding_norm quadraticFullEmbedding_dense

-- @@ L238-239 verbatim
lemma linearFullEquiv_embedding (v : ForestVec) :
    linearFullEquiv (linearData.embedding v)=linearFullEmbedding v := linearData.completionMap_coe _ _ _

-- @@ L240-241 verbatim
lemma quadraticFullEquiv_embedding (v : ForestVec) :
    quadraticFullEquiv (quadraticData.embedding v)=quadraticFullEmbedding v := quadraticData.completionMap_coe _ _ _

-- @@ L242-242 verbatim
end PathModel


-- @@ L244-244 verbatim
namespace LpBoundedMap

-- @@ L245-247 verbatim
variable {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {p : ℝ≥0∞} [Fact (1 ≤ p)]

-- @@ L248-249 verbatim
def normVector (v : lp (fun _ : ι => E) p) : lp (fun _ : ι => ℝ) p :=
  ⟨fun i => ‖v i‖,v.property.norm⟩

-- @@ L250-252 verbatim
lemma normVector_norm {ι E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ 0) (v : lp (fun _ : ι => E) p) : ‖normVector v‖=‖v‖ := by
  have he (i : ι) : ‖normVector v i‖=‖v i‖ := norm_norm _
  exact le_antisymm (lp.norm_mono hp (fun i => (he i).le)) (lp.norm_mono hp (fun i => (he i).ge))

-- @@ L253-257 verbatim
def map (f : E → F) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ x,‖f x‖ ≤ C*‖x‖)
    (v : lp (fun _ : ι => E) p) : lp (fun _ : ι => F) p :=
  ⟨fun i => f (v i),(C • normVector v).property.mono' (fun i => by
    simpa only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hC,
      normVector,abs_norm] using hf (v i))⟩

-- @@ L258-259 verbatim
lemma map_apply {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} [Fact (1 ≤ p)] (f : E → F) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ x,‖f x‖ ≤ C*‖x‖)
    (v : lp (fun _ : ι => E) p) (i : ι) : map f C hC hf v i=f (v i) := rfl

-- @@ L260-266 verbatim
lemma map_norm {ι E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ 0) (f : E → F) (C : ℝ) (hC : 0 ≤ C) (hf : ∀ x,‖f x‖ ≤ C*‖x‖)
    (v : lp (fun _ : ι => E) p) : ‖map f C hC hf v‖ ≤ C*‖v‖ := by
  calc
    _ ≤ ‖C • normVector v‖ := lp.norm_mono hp (fun i => by
      simpa only [lp.coeFn_smul,Pi.smul_apply,smul_eq_mul,Real.norm_eq_abs,abs_mul,abs_of_nonneg hC,
        normVector,abs_norm,map_apply] using hf (v i))
    _ = C*‖v‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC,normVector_norm hp]

-- @@ L267-267 verbatim
end LpBoundedMap


-- @@ L269-269 verbatim
end DiamondDistortion


-- @@ L271-271 verbatim
end


-- @@ L273-273 verbatim
end OAI
