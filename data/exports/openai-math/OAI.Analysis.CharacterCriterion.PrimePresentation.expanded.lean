import OAI.Analysis.CharacterCriterion.Definitions
import OAI.Analysis.CharacterCriterion.Projectionless


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped TensorProduct

-- @@ L8-8 verbatim
open scoped InnerProductSpace

-- @@ L9-9 verbatim
open scoped BigOperators

-- @@ L10-10 verbatim
open Set Module

-- @@ L11-11 verbatim
open Topology

-- @@ L12-12 verbatim
open NormedSpace

-- @@ L13-13 verbatim
open scoped ComplexOrder

-- @@ L14-14 verbatim
open scoped ComplexOrder

-- @@ L15-15 verbatim
open scoped InnerProductSpace

-- @@ L16-16 verbatim
open scoped InnerProductSpace

-- @@ L17-17 verbatim
open NormedSpace

-- @@ L18-18 verbatim
open scoped TensorProduct InnerProductSpace

-- @@ L19-19 verbatim
open UniformSpace

-- @@ L20-20 verbatim
variable [KirchbergRordam.GenericRW.Size]

-- @@ L21-21 verbatim
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n

-- @@ L22-22 verbatim
variable [KirchbergRordam.GenericRW.PauliData]

-- @@ L23-23 verbatim
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]

-- @@ L24-24 verbatim
open Filter Topology BoundedContinuousFunction

-- @@ L25-25 verbatim
open Filter Topology

-- @@ L26-26 verbatim
open Topology

-- @@ L27-27 verbatim
open scoped TensorProduct CStarAlgebra

-- @@ L28-28 verbatim
open scoped CStarAlgebra ComplexOrder

-- @@ L29-29 verbatim
open NormedSpace

-- @@ L30-30 verbatim
open scoped ComplexOrder

-- @@ L31-31 verbatim
open scoped ComplexOrder

-- @@ L32-32 verbatim
open scoped InnerProductSpace

-- @@ L33-33 verbatim
open scoped CStarAlgebra ComplexOrder

-- @@ L34-34 verbatim
open scoped TensorProduct InnerProductSpace

-- @@ L35-35 verbatim
open UniformSpace


-- @@ L37-37 verbatim
namespace KirchbergRordam.PrimeDropPresentation

-- @@ L38-38 verbatim
open scoped CStarAlgebra ComplexOrder

-- @@ L39-39 verbatim
variable (S : PrimeDropPresentation)

-- @@ L40-42 verbatim
lemma size_two (n : ℕ) : 2≤S.size n := by
  rw [S.size_power]
  exact Nat.le_self_pow (by omega) 2

-- @@ L43-43 verbatim
instance (n : ℕ) : NeZero (S.size n) := ⟨by have := S.size_two n; omega⟩

-- @@ L44-45 verbatim
instance (n : ℕ) : Nontrivial (S.Stage n) := inferInstanceAs
  (Nontrivial (PrimeDimensionDrop.Algebra (S.size n) (S.size n+1)))

-- @@ L46-47 verbatim
instance (n : ℕ) : TopologicalSpace.SeparableSpace (S.Stage n) := inferInstanceAs
  (TopologicalSpace.SeparableSpace (PrimeDimensionDrop.Algebra (S.size n) (S.size n+1)))

-- @@ L48-51 verbatim
lemma stage_step_norm (S : PrimeDropPresentation) :
    ∀ stage (element : S.Stage stage),
      ‖GeneralDropSystem.step (S.stepData stage) element‖ = ‖element‖ :=
  fun stage element => GeneralDropSystem.step_norm (S.stepData stage) element


-- @@ L53-53 verbatim
instance (n : ℕ) : Nontrivial (S.system.obj n) := inferInstanceAs (Nontrivial (S.Stage n))

-- @@ L54-55 verbatim
instance (n : ℕ) : TopologicalSpace.SeparableSpace (S.system.obj n) :=
  inferInstanceAs (TopologicalSpace.SeparableSpace (S.Stage n))

-- @@ L56-56 verbatim
def Algebra : Type := CStarInductiveLimit.Algebra S.system

-- @@ L57-57 verbatim
instance : CStarAlgebra S.Algebra := inferInstanceAs (CStarAlgebra (CStarInductiveLimit.Algebra S.system))

-- @@ L58-58 verbatim
instance : Nontrivial S.Algebra := inferInstanceAs (Nontrivial (CStarInductiveLimit.Algebra S.system))

-- @@ L59-59 verbatim
instance : TopologicalSpace.SeparableSpace S.Algebra := inferInstanceAs (TopologicalSpace.SeparableSpace (CStarInductiveLimit.Algebra S.system))

-- @@ L60-60 verbatim
def inclusion (n : ℕ) : S.Stage n →⋆ₐ[ℂ] S.Algebra := CStarInductiveLimit.of S.system n

-- @@ L61-62 verbatim
lemma norm_inclusion (n : ℕ) (x : S.Stage n) : ‖S.inclusion n x‖=‖x‖ :=
  CStarInductiveLimit.norm_of S.system n x

-- @@ L63-63 verbatim
lemma inclusion_isometry (n : ℕ) : Isometry (S.inclusion n) := CStarInductiveLimit.of_isometry _ _

-- @@ L64-65 verbatim
lemma inclusion_map (i j : ℕ) (hij : i≤j) (x : S.Stage i) :
    S.inclusion j (S.chain.map i j hij x)=S.inclusion i x := CStarInductiveLimit.of_map _ _ _ _ _

-- @@ L66-70 verbatim
lemma inclusion_step (n : ℕ) (x : S.Stage n) :
    S.inclusion (n+1) (GeneralDropSystem.step (S.stepData n) x)=S.inclusion n x := by
  have h := S.inclusion_map n (n+1) (Nat.le_succ n) x
  rw [S.chain.map_succ n n le_rfl,S.chain.map_self] at h
  exact h

-- @@ L71-72 verbatim
lemma denseRange_inclusion : DenseRange (fun x : Σ n, S.Stage n => S.inclusion x.1 x.2) :=
  CStarInductiveLimit.denseRange_of _

-- @@ L73-81 verbatim
theorem stage_to_central (A : Type*) [CStarAlgebra A] [Nontrivial A]
    [TopologicalSpace.SeparableSpace A] (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤Filter.cofinite)
    (hF : IsEmpty (NormUltrapower.CentralAlgebra A ω →⋆ₐ[ℂ] ℂ)) (n : ℕ) :
    Nonempty (S.Stage n →⋆ₐ[ℂ] NormUltrapower.CentralAlgebra A ω) := by
  have aux (p : ℕ) [NeZero p] (he : p=2^(S.exponent n+1)) :
      Nonempty (PrimeDimensionDrop.Algebra p (p+1) →⋆ₐ[ℂ] NormUltrapower.CentralAlgebra A ω) := by
    subst p
    exact central_prime_power_drop A ω hω hF (S.exponent n)
  exact aux (S.size n) (S.size_power n)

-- @@ L82-86 verbatim
theorem to_central (A : Type*) [CStarAlgebra A] [Nontrivial A]
    [TopologicalSpace.SeparableSpace A] (ω : Ultrafilter ℕ) (hω : (ω : Filter ℕ)≤Filter.cofinite)
    (hF : IsEmpty (NormUltrapower.CentralAlgebra A ω →⋆ₐ[ℂ] ℂ)) :
    Nonempty (S.Algebra →⋆ₐ[ℂ] NormUltrapower.CentralAlgebra A ω) :=
  CStarInductiveLimit.exists_toCentral S.system ω hω (fun n => (S.stage_to_central A ω hω hF n).some)

-- @@ L87-87 verbatim
end KirchbergRordam.PrimeDropPresentation

-- @@ L88-88 verbatim
namespace KirchbergRordam.PrimeDropPresentation.Iteration

-- @@ L89-89 verbatim
open scoped CStarAlgebra ComplexOrder

-- @@ L90-90 verbatim
open Filter Topology

-- @@ L91-91 verbatim
open MatrixDiagonalPath DiagonalIteration GeneralDropSystem

-- @@ L92-92 verbatim
variable (S : PrimeDropPresentation)


-- @@ L94-100 verbatim
abbrev diagonalSystem : DiagonalIteration.System where
  obj n := PrimeDimensionDrop.Fiber (S.size n) (S.size n+1)
  slot n := Slot (S.stepData n)
  diagonal n := (CStarMatrix.reindexₐ ℂ ℂ (zeroReindex (S.stepData n))).toStarAlgHom.comp block
  eigen n := eigenpath (S.stepData n)
  twist n := (MatrixPermutationPath.path 1
    ((zeroReindex (S.stepData n)).symm.trans (oneReindex (S.stepData n)))).toContinuousMap


-- @@ L102-103 verbatim
lemma eigen_lipschitz : ∀ n i, LipschitzWith (1/2) ((diagonalSystem S).eigen n i) :=
  fun n i => GeneralDropSystem.eigen_lipschitz (S.stepData n) i


-- @@ L105-115 verbatim
lemma iterate_full (n k : ℕ) (f : S.Stage n) (t : unitInterval) :
    (S.chain.map n (n+k) (Nat.le_add_right n k) f).val t =
      (diagonalSystem S).full n k f.val t := by
  induction k generalizing t with
  | zero => simp only [Nat.add_zero,S.chain.map_self,DiagonalIteration.System.full]; rfl
  | succ k ih =>
    erw [S.chain.map_succ n (n+k) (Nat.le_add_right n k)]
    change MatrixDiagonalPath.interpolate _ _ t
      (block (fun i => (S.chain.map n (n+k) _ f).val (eigenpath (S.stepData (n+k)) i t))) = _
    simp only [ih]
    rfl


-- @@ L117-119 verbatim
def normalizedPath (n k : ℕ) (t : unitInterval) :
    unitary (PrimeDimensionDrop.Fiber (S.size (n+k)) (S.size (n+k)+1)) :=
  (diagonalSystem S).unitaryPath n k t * star ((diagonalSystem S).unitaryPath n k 0)

-- @@ L120-121 verbatim
lemma normalizedPath_continuous (n k : ℕ) : Continuous (normalizedPath S n k) :=
  ((diagonalSystem S).unitaryPath_continuous n k).mul continuous_const

-- @@ L122-123 verbatim
@[simp] lemma normalizedPath_zero (n k : ℕ) : normalizedPath S n k 0=1 := by
  exact mul_inv_cancel _


-- @@ L125-130 verbatim
lemma untwist (n k : ℕ) (f : S.Stage n) (t : unitInterval) :
    conj (star (normalizedPath S n k t))
      ((S.chain.map n (n+k) (Nat.le_add_right n k) f).val t) =
      conj ((diagonalSystem S).unitaryPath n k 0) ((diagonalSystem S).flat n k f.val t) := by
  rw [iterate_full S,(diagonalSystem S).full_eq]
  exact DiagonalIteration.normalize_cancel _ _ _


-- @@ L132-138 verbatim
lemma untwist_norm (n k : ℕ) (f : S.Stage n) (t : unitInterval) :
    ‖conj (star (normalizedPath S n k t))
      ((S.chain.map n (n+k) (Nat.le_add_right n k) f).val t)-
      (S.chain.map n (n+k) (Nat.le_add_right n k) f).val 0‖ =
      ‖(diagonalSystem S).flat n k f.val t-(diagonalSystem S).flat n k f.val 0‖ := by
  rw [untwist S,iterate_full S,(diagonalSystem S).full_eq]
  rw [←map_sub,StarAlgEquiv.norm_map]


-- @@ L140-147 verbatim
lemma eventually_untwist_small (n : ℕ) (f : S.Stage n) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ k in atTop, ∀ t : unitInterval,
      ‖conj (star (normalizedPath S n k t))
        ((S.chain.map n (n+k) (Nat.le_add_right n k) f).val t)-
        (S.chain.map n (n+k) (Nat.le_add_right n k) f).val 0‖≤ε := by
  filter_upwards [(diagonalSystem S).flat_eventually_small (eigen_lipschitz S) n f.val ε hε] with k hk t
  rw [untwist_norm S]
  exact hk t 0

-- @@ L148-148 verbatim
end KirchbergRordam.PrimeDropPresentation.Iteration

-- @@ L149-149 verbatim
namespace KirchbergRordam.PrimeDropPresentation.HalfFlip

-- @@ L150-150 verbatim
open scoped CStarAlgebra ComplexOrder

-- @@ L151-151 verbatim
open Filter Topology

-- @@ L152-152 verbatim
open PrimeDropPresentation.Iteration

-- @@ L153-153 verbatim
open UnitaryDisplacement BalancedDropHalfFlip

-- @@ L154-157 verbatim
def mappedUnitary {A B : Type} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) (w : unitary (MaxTensor.Algebra A A)) :
    unitary (MaxTensor.Algebra B B) :=
  Unitary.map (StarMonoidHom.ofClass (squareMap φ)) w


-- @@ L159-163 verbatim
lemma mappedUnitary_control {A B : Type} [CStarAlgebra A] [CStarAlgebra B]
    (φ : A →⋆ₐ[ℂ] B) (w : unitary (MaxTensor.Algebra A A)) (a : A) :
    ‖conj (mappedUnitary φ w) (MaxTensor.includeLeft (φ a))-MaxTensor.includeRight (φ a)‖≤
      ‖conj w (MaxTensor.includeLeft a)-MaxTensor.includeRight a‖ := by
  exact control_map φ w a

-- @@ L164-164 verbatim
variable (S : PrimeDropPresentation)

-- @@ L165-186 verbatim
lemma finite_stage (n : ℕ) (F : Finset (S.Stage n)) (ε : ℝ) (hε : 0<ε) :
    ∃ w : unitary (MaxTensor.Algebra S.Algebra S.Algebra), ∀ f∈F,
      ‖conj w (MaxTensor.includeLeft (S.inclusion n f))-
        MaxTensor.includeRight (S.inclusion n f)‖≤ε := by
  have he : ∀ᶠ k in atTop, ∀ f∈F, ∀ t : unitInterval,
      ‖conj (star (normalizedPath S n k t))
        ((S.chain.map n (n+k) (Nat.le_add_right n k) f).val t)-
        (S.chain.map n (n+k) (Nat.le_add_right n k) f).val 0‖≤ε/4 := by
    apply (Filter.eventually_all_finset F).mpr
    intro f hf
    exact eventually_untwist_small S n f (ε/4) (by positivity)
  obtain ⟨k,hk⟩ := he.exists
  obtain ⟨w,hw⟩ := PrimeSquareUnitary.exists_half_flip_control (p:=S.size (n+k)) (q:=S.size (n+k)+1) (normalizedPath S n k)
    (normalizedPath_continuous S n k) (normalizedPath_zero S n k)
  refine ⟨mappedUnitary (S.inclusion (n+k)) w,fun f hf => ?_⟩
  have hc := (mappedUnitary_control (S.inclusion (n+k)) w (S.chain.map n (n+k) (Nat.le_add_right n k) f)).trans
    (hw _ (ε/4) (hk f hf))
  have hm : S.inclusion (n+k) (S.chain.map n (n+k) (Nat.le_add_right n k) f)=S.inclusion n f :=
    S.inclusion_map n (n+k) (Nat.le_add_right n k) f
  rw [hm] at hc
  have he : 4*(ε/4)=ε := by ring
  rwa [he] at hc


-- @@ L188-190 verbatim
lemma common_stage (F : Finset S.Algebra) (ε : ℝ) (hε : 0<ε) :
    ∃ n : ℕ, ∃ a : S.Algebra → S.Stage n, ∀ x∈F, ‖S.inclusion n (a x)-x‖<ε :=
  CStarInductiveLimit.approximation_common_stage S.system F ε hε


-- @@ L192-205 verbatim
lemma finite_control (F : Finset S.Algebra) (ε : ℝ) (hε : 0<ε) :
    ∃ w : unitary (MaxTensor.Algebra S.Algebra S.Algebra), ∀ x∈F,
      ‖conj w (MaxTensor.includeLeft x)-MaxTensor.includeRight x‖≤ε := by
  classical
  obtain ⟨n,a,ha⟩ := common_stage S F (ε/4) (by positivity)
  obtain ⟨w,hw⟩ := finite_stage S n (F.image a) (ε/2) (by positivity)
  refine ⟨w,fun x hx => ?_⟩
  have hb := hw (a x) (Finset.mem_image_of_mem a hx)
  have hc := FiniteHalfFlipSequence.perturbation MaxTensor.includeLeft MaxTensor.includeRight w x (S.inclusion n (a x))
  have hd := ha x hx
  rw [norm_sub_rev] at hd
  change ‖conj w (MaxTensor.includeLeft x)-MaxTensor.includeRight x‖≤
    2*‖x-S.inclusion n (a x)‖+‖conj w (MaxTensor.includeLeft (S.inclusion n (a x)))-MaxTensor.includeRight (S.inclusion n (a x))‖ at hc
  linarith



-- @@ L208-211 verbatim
theorem exists_half_flip : ∃ w : ℕ → unitary (MaxTensor.Algebra S.Algebra S.Algebra),
    ∀ x : S.Algebra, Tendsto (fun n => conj (w n) (MaxTensor.includeLeft x)) atTop
      (𝓝 (MaxTensor.includeRight x)) :=
  FiniteHalfFlipSequence.exists_sequence MaxTensor.includeLeft MaxTensor.includeRight (finite_control S)

-- @@ L212-212 verbatim
end KirchbergRordam.PrimeDropPresentation.HalfFlip

-- @@ L213-213 verbatim
namespace KirchbergRordam.PrimeDropPresentation.Channels

-- @@ L214-214 verbatim
open MatrixDiagonalPath MatrixBlockReindex DiagonalIteration GeneralEndpointMultiplicity

-- @@ L215-215 verbatim
open DropMatrixRepresentations DropChannels GeneralDropSystem

-- @@ L216-216 verbatim
open BalancedDropSystem (half)

-- @@ L217-217 verbatim
open scoped CStarAlgebra ComplexOrder

-- @@ L218-218 verbatim
variable (S : PrimeDropPresentation)

-- @@ L219-221 verbatim
lemma zeroCount (n : ℕ) :
    2≤Fintype.card (Fin (S.stepData n).zeroEnd ⊕ (Fin (S.size n+1)×Fin (S.stepData n).zeroMid)) := by
  simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using S.zero_copies n

-- @@ L222-224 verbatim
lemma oneCount (n : ℕ) :
    2≤Fintype.card (Fin (S.stepData n).oneEnd ⊕ (Fin (S.size n)×Fin (S.stepData n).oneMid)) := by
  simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] using S.one_copies n

-- @@ L225-229 verbatim
lemma block_const_left {P E : Type*} [Fintype P] [Fintype E] [DecidableEq P] [DecidableEq E]
    (a : Mat P) : block (fun _ : E => a)=MatrixTensor.leftMatrix (κ:=E) a := by
  ext ⟨i,k⟩ ⟨j,l⟩
  change (if k=l then a i j else 0)=a i j*(if k=l then 1 else 0)
  split <;> simp_all


-- @@ L231-235 verbatim
def zeroRep (n : ℕ) (v : unitary (PrimeDimensionDrop.Fiber (S.size n) (S.size n+1))) :
    DimensionDrop23 →⋆ₐ[ℂ] Mat (Fin (S.size (n+1))) :=
  (CStarMatrix.reindexₐ ℂ ℂ (zeroOuter (S.stepData n))).toStarAlgHom.comp
    (leftRep (P:=Fin (S.size n)) (Q:=Fin (S.size n+1)) (R:=Fin (S.stepData n).zeroMid)
      (E:=Fin (S.stepData n).zeroEnd) (zeroCount S n) v)

-- @@ L236-240 verbatim
def oneRep (n : ℕ) (v : unitary (PrimeDimensionDrop.Fiber (S.size n) (S.size n+1))) :
    DimensionDrop23 →⋆ₐ[ℂ] Mat (Fin (S.size (n+1)+1)) :=
  (CStarMatrix.reindexₐ ℂ ℂ (oneOuter (S.stepData n))).toStarAlgHom.comp
    (rightRep (P:=Fin (S.size n)) (Q:=Fin (S.size n+1)) (R:=Fin (S.stepData n).oneMid)
      (E:=Fin (S.stepData n).oneEnd) (oneCount S n) v)

-- @@ L241-257 verbatim
lemma zeroRep_bound (n : ℕ)
    (v : unitary (PrimeDimensionDrop.Fiber (S.size n) (S.size n+1)))
    (f : S.Stage n) (d : DimensionDrop23) {ε : ℝ}
    (hf : ‖conj (star v) (f.val half)-f.val 0‖≤ε) :
    ‖MatrixTensor.leftMatrix (κ:=Fin (S.size (n+1)+1)) (zeroRep S n v d)*(step (S.stepData n) f).val 0-
      (step (S.stepData n) f).val 0*MatrixTensor.leftMatrix (κ:=Fin (S.size (n+1)+1)) (zeroRep S n v d)‖≤2*ε*‖d‖ := by
  have he := rawStep_zero (S.stepData n) f.val _ (leftValue_spec (S.size n) (S.size n+1) f)
  change (step (S.stepData n) f).val 0=_ at he
  rw [block_const_left] at he
  rw [he]
  let φ := (MatrixTensor.leftMatrix (κ:=Fin (S.size (n+1)+1))).comp
    (CStarMatrix.reindexₐ ℂ ℂ (zeroOuter (S.stepData n))).toStarAlgHom
  apply (commutator_map_bound φ _ _).trans
  apply leftRep_bound (zeroCount S n)
  erw [leftValue_spec (S.size n) (S.size n+1) f]
  rw [norm_sub_conj]
  exact hf

-- @@ L258-274 verbatim
lemma oneRep_bound (n : ℕ)
    (v : unitary (PrimeDimensionDrop.Fiber (S.size n) (S.size n+1)))
    (f : S.Stage n) (d : DimensionDrop23) {ε : ℝ}
    (hf : ‖conj (star v) (f.val half)-f.val 1‖≤ε) :
    ‖MatrixTensor.rightMatrix (ι:=Fin (S.size (n+1))) (oneRep S n v d)*(step (S.stepData n) f).val 1-
      (step (S.stepData n) f).val 1*MatrixTensor.rightMatrix (ι:=Fin (S.size (n+1))) (oneRep S n v d)‖≤2*ε*‖d‖ := by
  have he := rawStep_one (S.stepData n) f.val _ (rightValue_spec (S.size n) (S.size n+1) f)
  change (step (S.stepData n) f).val 1=_ at he
  rw [block_const_left] at he
  rw [he]
  let φ := (MatrixTensor.rightMatrix (ι:=Fin (S.size (n+1)))).comp
    (CStarMatrix.reindexₐ ℂ ℂ (oneOuter (S.stepData n))).toStarAlgHom
  apply (commutator_map_bound φ _ _).trans
  apply rightRep_bound (oneCount S n)
  erw [rightValue_spec (S.size n) (S.size n+1) f]
  rw [norm_sub_conj]
  exact hf

-- @@ L275-275 verbatim
end KirchbergRordam.PrimeDropPresentation.Channels

-- @@ L276-276 verbatim
end


-- @@ L278-278 verbatim
end OAI
