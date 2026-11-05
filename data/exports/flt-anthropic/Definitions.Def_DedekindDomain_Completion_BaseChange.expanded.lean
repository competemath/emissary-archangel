import Definitions.Def_DedekindDomain_AdicValuation_InlineSpecific
import Definitions.Def_DedekindDomain_IntegralClosure
import Definitions.Def_Mathlib_IsModuleTopology
import Definitions.Def_Mathlib_Topology_Algebra_UniformRing
import Definitions.Def_Mathlib_RightActionInstances


-- @@ L7-7 verbatim
set_option maxHeartbeats 1200000

-- @@ L8-8 verbatim
set_option synthInstance.maxHeartbeats 400000


-- @@ L10-10 verbatim
set_option maxSynthPendingDepth 3

-- @@ L11-11 verbatim
set_option Elab.async false


-- @@ L13-13 verbatim
section


-- @@ L15-15 verbatim
variable {R S : Type*} [Ring R]


-- @@ L17-21 verbatim
def Subring.toSubmodule (S : Subring R) : Submodule S R where
  __ := S
  smul_mem' x y h := by
    rw [smul_def, smul_eq_mul]
    apply S.mul_mem (SetLike.coe_mem x) h


-- @@ L23-23 verbatim
section


-- @@ L25-30 expanded
def Pi.semialgHom {I : Type*} {R S : Type*} (f : I → Type*) [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) [s : (i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)] {A : Type*}
    [Semiring A] [Algebra R A] (g : (i : I) → SemialgHom φ A (f i)) : SemialgHom φ A ((i : I) → f i)
    where
  __ := RingHom.pi fun i ↦ (g i).toRingHom
  map_smul' r a := by ext; simp [RingHom.pi]


-- @@ L32-38 expanded
@[simp]
theorem Pi.semialgHom_apply {I : Type*} {R S : Type*} (f : I → Type*) [CommSemiring R]
    [CommSemiring S] (φ : R →+* S) [s : (i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)]
    {A : Type*} [Semiring A] [Algebra R A] (g : (i : I) → SemialgHom φ A (f i)) (a : A) (i : I) :
    (Pi.semialgHom _ φ g) a i = g i a :=
  rfl


-- @@ L40-50 expanded
def Pi.semialgHomPi {I J : Type*} {R S : Type*} (f : I → Type*) (g : J → Type*) [CommSemiring R]
    [CommSemiring S] {φ : R →+* S} [(i : I) → Semiring (f i)] [(i : I) → Algebra S (f i)]
    [(j : J) → Semiring (g j)] [(j : J) → Algebra R (g j)] {r : I → J}
    (p : (i : I) → SemialgHom φ (g (r i)) (f i)) : SemialgHom φ ((j : J) → g j) ((i : I) → f i)
    where
  toFun x w := p w (x (r w))
  map_one' := by simp [Pi.one_def]
  map_mul' x y := funext fun w => by simp [map_mul]
  map_zero' := by simp [Pi.zero_def]
  map_add' x y := funext fun w => by simp [map_add]
  map_smul' k x := funext fun w => (p w).map_smul' k (x (r w))


-- @@ L52-58 expanded
@[simp]
theorem Pi.semialgHomPi_apply {I J : Type*} {R S : Type*} (f : I → Type*) (g : J → Type*)
    [CommSemiring R] [CommSemiring S] {φ : R →+* S} [(i : I) → Semiring (f i)]
    [(i : I) → Algebra S (f i)] [(j : J) → Semiring (g j)] [(j : J) → Algebra R (g j)] {r : I → J}
    (p : (i : I) → SemialgHom φ (g (r i)) (f i)) (a : (j : J) → g j) (i : I) :
    Pi.semialgHomPi _ _ p a i = p i (a (r i)) :=
  rfl


-- @@ L60-68 verbatim
def AlgEquiv.piCongrFiberwise {α : Type*} {β : Type*} {R : Type*} {γ₁ : α → Type*} {γ₂ : β → Type*}
    {f : α → β} [CommSemiring R] [(a : α) → Semiring (γ₁ a)] [(b : β) → Semiring (γ₂ b)]
    [(a : α) → Algebra R (γ₁ a)] [(b : β) → Algebra R (γ₂ b)]
    (e : (b : β) → ((x : { x : α // f x = b }) → γ₁ x.1) ≃ₐ[R] γ₂ b) :
    ((a : α) → γ₁ a) ≃ₐ[R] ((b : β) → γ₂ b) where
  __ := Equiv.piCongrFiberwise fun _ => (e _).toEquiv
  map_add' _ _ := by funext b; simp [← Pi.add_def]
  map_mul' _ _ := by funext b; simp [← Pi.mul_def]
  commutes' r := by funext b; simp [← (e b).commutes' r, Pi.algebraMap_def]


-- @@ L70-70 verbatim
section

-- @@ L71-71 verbatim
open scoped TensorProduct

-- @@ L72-73 verbatim
variable {R S : Type*} [CommSemiring R] [CommSemiring S] {φ : R →+* S}
    {A B : Type*}


-- @@ L75-85 expanded
noncomputable def SemialgHom.baseChange_of_algebraMap [Semiring A] [Algebra R S] [Algebra R A]
    [Semiring B] [Algebra S B] (ψ : SemialgHom (algebraMap R S) A B) : S ⊗[R] A →ₐ[S] B :=
  letI : Algebra R B := Algebra.compHom _ (algebraMap R S)
  have : IsScalarTower R S B := .of_algebraMap_eq fun _ ↦ rfl
  let ρ : A →ₐ[R] B :=
    { toRingHom := ψ.toRingHom
      commutes' := ψ.commutes }
  Algebra.TensorProduct.lift (Algebra.ofId S _) ρ fun s a ↦ Algebra.commutes s (ρ a)


-- @@ L87-90 expanded
theorem SemialgHom.baseChange_of_algebraMap_tmul [Semiring A] [Algebra R S] [Algebra R A]
    [Semiring B] [Algebra S B] (ψ : SemialgHom (algebraMap R S) A B) (s : S) (a : A) :
    ψ.baseChange_of_algebraMap (s ⊗ₜ[R] a) = algebraMap _ _ s * ψ a := by
  simp [baseChange_of_algebraMap, SemialgHom.toLinearMap_eq_coe, Algebra.ofId_apply]


-- @@ L92-96 expanded
@[simp]
theorem SemialgHom.baseChange_of_algebraMap_tmul_right [Semiring A] [Algebra R S] [Algebra R A]
    [Semiring B] [Algebra S B] (ψ : SemialgHom (algebraMap R S) A B) (a : A) :
    ψ.baseChange_of_algebraMap (1 ⊗ₜ[R] a) = ψ a := by
  simp [baseChange_of_algebraMap, SemialgHom.toLinearMap_eq_coe]


-- @@ L98-102 expanded
@[simp]
theorem SemialgHom.baseChange_of_algebraMap_tmul_left [Semiring A] [Algebra R S] [Algebra R A]
    [Semiring B] [Algebra S B] (ψ : SemialgHom (algebraMap R S) A B) (s : S) :
    ψ.baseChange_of_algebraMap (s ⊗ₜ[R] 1) = algebraMap _ _ s := by
  simp [baseChange_of_algebraMap, SemialgHom.toLinearMap_eq_coe, Algebra.ofId_apply]


-- @@ L104-120 expanded
open scoped TensorProduct.RightActions in
instance [Algebra R S] [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra S B]
    (ψ : SemialgHom (algebraMap R S) A B) :
    letI := ψ.toAlgebra
    IsBiscalar S A ψ.baseChange_of_algebraMap
    where
  __ := ψ.toAlgebra
  map_smul₁ s x := ψ.baseChange_of_algebraMap.map_smul_of_tower ..
  map_smul₂ a
    x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul x
      y =>
      simp [TensorProduct.smul_tmul', -algebraMap_smul, algebra_compatible_smul B a,
        SemialgHom.baseChange_of_algebraMap_tmul, RingHom.algebraMap_toAlgebra,
        SemialgHom.toLinearMap_eq_coe]
      ring
    | add x y hx hy => simp_all


-- @@ L122-131 expanded
open scoped TensorProduct.RightActions in
noncomputable def SemialgHom.baseChangeRightOfAlgebraMap [Algebra R S] [CommSemiring A]
    [Algebra R A] [CommSemiring B] [Algebra S B] (ψ : SemialgHom (algebraMap R S) A B) :
    letI := ψ.toAlgebra
    S ⊗[R] A →ₐ[A] B :=
  letI := ψ.toAlgebra
  AlgHom.changeScalars A ψ.baseChange_of_algebraMap


-- @@ L133-139 expanded
open scoped TensorProduct.RightActions in
@[simp]
theorem SemialgHom.baseChangeRightOfAlgebraMap_apply [Algebra R S] [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra S B] (ψ : SemialgHom (algebraMap R S) A B) (x : S ⊗[R] A) :
    baseChangeRightOfAlgebraMap ψ x = baseChange_of_algebraMap ψ x := by
  simp [baseChangeRightOfAlgebraMap, AlgHom.changeScalars_apply]


-- @@ L141-147 expanded
open scoped TensorProduct.RightActions in
@[simp]
theorem SemialgHom.baseChangeRightOfAlgebraMap_coe [Algebra R S] [CommSemiring A] [Algebra R A]
    [CommSemiring B] [Algebra S B] (ψ : SemialgHom (algebraMap R S) A B) :
    ⇑ψ.baseChangeRightOfAlgebraMap = ⇑ψ.baseChange_of_algebraMap :=
  funext_iff.2 <| ψ.baseChangeRightOfAlgebraMap_apply


-- @@ L149-150 verbatim
variable (F : Type*) [CommSemiring F] {A : Type*} [Ring A]
    [Algebra F A]


-- @@ L152-158 verbatim
def _root_.LinearEquiv.mulLeft (u : Aˣ) : A ≃ₗ[F] A where
  toFun x := u * x
  invFun y := u⁻¹ * y
  left_inv x := by simp
  right_inv y := by simp
  map_add' x₁ x₂ := left_distrib ↑u x₁ x₂
  map_smul' f x := by simp


-- @@ L160-163 verbatim
@[simp]
theorem LinearEquiv.coe_mulLeft (u : Aˣ) :
    (LinearEquiv.mulLeft F u : A →ₗ[F] A) = LinearMap.mulLeft F (u : A) :=
  rfl


-- @@ L165-171 verbatim
def _root_.LinearEquiv.mulRight (u : Aˣ) : A ≃ₗ[F] A where
  toFun x := x * u
  invFun y := y * u⁻¹
  left_inv x := by simp [mul_assoc]
  right_inv y := by simp [mul_assoc]
  map_add' x₁ x₂ := right_distrib x₁ x₂ u
  map_smul' f x := by simp


-- @@ L173-176 verbatim
@[simp]
theorem LinearEquiv.coe_mulRight (u : Aˣ) :
    (LinearEquiv.mulRight F u : A →ₗ[F] A) = LinearMap.mulRight F (u : A) :=
  rfl


-- @@ L178-178 verbatim
section


-- @@ L180-180 verbatim
section Basis


-- @@ L182-182 verbatim
open scoped TensorProduct


-- @@ L184-184 verbatim
open scoped TensorProduct.RightActions


-- @@ L186-186 verbatim
variable {R : Type*} (A : Type*) {B : Type*} {ι : Type*} [CommSemiring R]

-- @@ L187-187 verbatim
variable [CommSemiring A] [Algebra R A] [Fintype ι]

-- @@ L188-188 verbatim
variable [CommSemiring B] [Algebra R B]


-- @@ L190-202 verbatim
noncomputable
def Module.Basis.rightBaseChange [DecidableEq ι] (b : Module.Basis ι R A) :
    Module.Basis ι B (A ⊗[R] B) where
  repr :=
    let comm : B ⊗[R] A ≃ₗ[B] A ⊗[R] B :=
      TensorProduct.RightActions.Algebra.TensorProduct.comm R B A
    let π : B ⊗[R] A ≃ₗ[B] (ι → B) :=
      (TensorProduct.AlgebraTensorModule.congr
        (LinearEquiv.refl B B)
        b.equivFun).trans
      (TensorProduct.piScalarRight _ _ _ _)
    let finite : (ι →₀ B) ≃ₗ[B] (ι → B) := Finsupp.linearEquivFunOnFinite B B ι
    comm.symm.trans π |>.trans finite.symm


-- @@ L204-215 verbatim
@[simp]
lemma Module.Basis.rightBaseChange_repr [DecidableEq ι] (b : Module.Basis ι R A) (i) (x : B) :
    (b.rightBaseChange A).repr (b i ⊗ₜ x) = Finsupp.single i x := by
  have : ∑ (j : ι), (Pi.single i (1 : R) : ι → R) j • (b j) = b i := by
    conv =>
      lhs
      arg 2
      intro j
      rw [Pi.single_comm, Pi.single_apply_smul]
    simp
  rw [← LinearEquiv.eq_symm_apply]
  simp [rightBaseChange, this]


-- @@ L217-221 verbatim
@[simp]
lemma Module.Basis.rightBaseChange_apply [DecidableEq ι] (b : Basis ι R A) (i) :
    b.rightBaseChange A i = b i ⊗ₜ (1 : B) := by
  rw [apply_eq_iff]
  exact rightBaseChange_repr A b i 1


-- @@ L223-223 verbatim
end Basis


-- @@ L225-225 verbatim
section Finrank


-- @@ L227-227 verbatim
namespace TensorProduct


-- @@ L229-229 verbatim
open scoped TensorProduct.RightActions


-- @@ L231-232 verbatim
variable {R : Type*} (A : Type*) {B : Type*} [CommRing R]
  [CommSemiring A] [Algebra R A] [CommRing B] [Algebra R B] [Nontrivial B]


-- @@ L234-239 verbatim
lemma finrank_rightAlgebra [Module.Finite R A] [Module.Free R A] :
    Module.finrank B (A ⊗[R] B) = Module.finrank R A := by
  have : Nontrivial R := RingHom.domain_nontrivial (algebraMap R B)
  let b := Module.Free.chooseBasis R A
  let b' : Module.Basis _ _ (A ⊗[R] B) := b.rightBaseChange A
  rw [Module.finrank_eq_card_basis b, Module.finrank_eq_card_basis b']


-- @@ L241-241 verbatim
end TensorProduct


-- @@ L243-243 verbatim
end Finrank


-- @@ L245-245 verbatim
namespace IsDedekindDomain.HeightOneSpectrum


-- @@ L247-248 verbatim
variable {A : Type*} (K : Type*) [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
    [IsDedekindDomain A] (v : HeightOneSpectrum A)


-- @@ L250-283 verbatim
open Valuation.IsRankOneDiscrete in

theorem closureAlgebraMapIntegers_eq_prodIntegers {ι : Type*}
    (v : ι → HeightOneSpectrum A)
    (injective : Function.Injective v) :
    closure (SetLike.coe (algebraMap A ((i : ι) → (v i).adicCompletion K)).range) =
    (Set.pi Set.univ (fun (i : ι) ↦ ((v i).adicCompletionIntegers K).carrier)) := by
  apply Set.Subset.antisymm
  · apply closure_minimal
    · rintro c ⟨a, ha⟩ i -
      rw [← ha]
      simp only [Pi.algebraMap_apply]
      exact coe_mem_adicCompletionIntegers (v i) a
    · apply isClosed_set_pi
      rintro w -
      apply Valued.isClosed_valuationSubring
  · intro f hf
    rw [mem_closure_iff_nhds_zero]
    intro U hU
    rw [Pi.zero_def, nhds_pi, Filter.mem_pi'] at hU
    obtain ⟨I, t, htn, hts⟩ := hU
    choose g' hg' using fun w => (Valued.is_topological_valuation (t w)).mp (htn w)
    let g := fun w ↦ Units.mapEquiv (valueGroup₀_equiv_withZeroMulInt _).toMulEquiv (g' w)
    obtain ⟨a, ha⟩ :=
      exists_forall_adicValued_sub_lt K I g v injective (fun w => ⟨f w, hf w ⟨⟩⟩)
    use algebraMap A _ a
    constructor
    · rw [RingHom.coe_range]
      exact Set.mem_range_self a
    · refine hts fun w hw ↦ hg' w ?_
      rw [Set.mem_setOf_eq, ← (valueGroup₀_equiv_withZeroMulInt_strictMono _).lt_iff_lt,
        valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
          (valuedAdicCompletion_surjective K (v w))]
      exact ha w hw


-- @@ L285-309 verbatim
theorem denseRange_of_prodAlgebraMap {ι : Type*} [Finite ι]
    {valuation : ι → HeightOneSpectrum A} (injective : Function.Injective valuation) :
    DenseRange (algebraMap K ((i : ι) → (valuation i).adicCompletion K)) := by
  rw [denseRange_iff_closure_range, Set.eq_univ_iff_forall]
  let S := Set.range (algebraMap K ((i : ι) → (valuation i).adicCompletion K))

  have hint : Set.pi Set.univ (fun (i : ι) ↦ ((valuation i).adicCompletionIntegers K).carrier)
      ⊆ closure S := by
    rw [← closureAlgebraMapIntegers_eq_prodIntegers _ _ injective]
    apply closure_mono
    exact fun _ ⟨a, ha⟩ ↦ ⟨algebraMap A K a, ha⟩

  have hmul : ∀x, x ∈ closure S → ∀k : K, k • x ∈ closure S := by
    intro x h k
    let f := fun (z : (i : ι) → (valuation i).adicCompletion K) ↦ k • z
    have hf : ContinuousAt f x := Continuous.continuousAt (continuous_const_smul k)
    apply closure_mono _ <| mem_closure_image hf h
    rintro x ⟨_, ⟨z, rfl⟩, rfl⟩
    use k • algebraMap K _ z
    ext i
    simp [Algebra.smul_def, f]

  intro x
  obtain ⟨k, y, hy, hx⟩ := adicCompletion.eq_mul_pi_adicCompletionIntegers K valuation x
  exact hx ▸ hmul y (hint hy) k


-- @@ L311-311 verbatim
end IsDedekindDomain.HeightOneSpectrum


-- @@ L313-313 verbatim
section


-- @@ L315-315 verbatim
open scoped WithZero Valued TensorProduct

-- @@ L316-316 verbatim
open Valuation.IsRankOneDiscrete WithZero


-- @@ L318-320 verbatim
variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]


-- @@ L322-322 verbatim
section assumptions


-- @@ L324-324 verbatim
variable [IsIntegralClosure B A L] [FiniteDimensional K L]


-- @@ L326-329 verbatim
example : IsDomain B := by
  have foo : Function.Injective (algebraMap B L) := IsIntegralClosure.algebraMap_injective B A _
  have bar : IsDomain L := inferInstance
  exact Function.Injective.isDomain _ foo


-- @@ L331-331 verbatim
example : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A L


-- @@ L333-334 verbatim
example [IsDomain B] [Algebra.IsSeparable K L] : IsDedekindDomain B :=
  IsIntegralClosure.isDedekindDomain A K L B


-- @@ L336-337 verbatim
example [IsDedekindDomain B] : IsFractionRing B L :=
  IsIntegralClosure.isFractionRing_of_finite_extension A K L B


-- @@ L339-341 verbatim
example [Algebra.IsSeparable K L] : Module.Finite A B :=
  have := IsIntegralClosure.isNoetherian A K L B
  Module.IsNoetherian.finite A B


-- @@ L343-343 verbatim
example : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L


-- @@ L345-345 verbatim
end assumptions


-- @@ L347-347 verbatim
variable [Algebra.IsIntegral A B] [IsFractionRing B L] [IsDedekindDomain B]


-- @@ L349-349 verbatim
namespace IsDedekindDomain.HeightOneSpectrum


-- @@ L351-351 verbatim
variable (v : HeightOneSpectrum A) {A B}


-- @@ L353-354 verbatim
local notation "σ" => fun v w => algebraMap (WithVal (HeightOneSpectrum.valuation K v))
    (WithVal (HeightOneSpectrum.valuation L w))


-- @@ L356-357 verbatim
private theorem continuousAdd_withVal_pin (w : HeightOneSpectrum B) :
    ContinuousAdd (WithVal (HeightOneSpectrum.valuation L w)) := inferInstance


-- @@ L359-363 verbatim
omit [Algebra A B] [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L]
  [Algebra.IsIntegral A B] in
private theorem addMonoidHomClass_withVal_pin (v : HeightOneSpectrum A) (w : HeightOneSpectrum B) :
    AddMonoidHomClass (WithVal (HeightOneSpectrum.valuation K v) →+* WithVal (HeightOneSpectrum.valuation L w))
      (WithVal (HeightOneSpectrum.valuation K v)) (WithVal (HeightOneSpectrum.valuation L w)) := inferInstance


-- @@ L365-366 verbatim
private theorem isTopologicalAddGroup_withVal_pin (v : HeightOneSpectrum A) :
    IsTopologicalAddGroup (WithVal (HeightOneSpectrum.valuation K v)) := inferInstance


-- @@ L368-368 verbatim
attribute [local instance] continuousAdd_withVal_pin addMonoidHomClass_withVal_pin isTopologicalAddGroup_withVal_pin


-- @@ L370-405 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma adicValued.continuous_algebraMap
   (w : HeightOneSpectrum B) (hvw : w.under A = v) :
    Continuous (σ v w) := by
  refine continuous_of_continuousAt_zero _ ?_
  rw [ContinuousAt, map_zero, (Valued.hasBasis_nhds_zero _ _).tendsto_iff
    (Valued.hasBasis_nhds_zero _ _)]
  intro γL _
  let e := v.asIdeal.ramificationIdx' w.asIdeal

  let σL := WithVal.valueGroupOrderIso₀ (w.valuation L)
  let σw := valueGroup₀_equiv_withZeroMulInt (w.valuation L)
  let m : ℤᵐ⁰ := σw (σL γL)

  let σv := valueGroup₀_equiv_withZeroMulInt (v.valuation K)
  let σK := (WithVal.valueGroupOrderIso₀ (v.valuation K))
  let γK := σK.symm (σv.symm (exp (m.log / e)))
  have hγK : γK ≠ 0 := by simp [γK]
  use .mk0 _ hγK
  simp only [Units.val_mk0, Set.mem_setOf_eq, true_and]
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx₀; · simp
  rw [σK.lt_symm_apply] at hx
  replace hx := (WithVal.valueGroupOrderIso₀_restrict (v.valuation K) x).symm.trans_lt hx
  rw [← (valueGroup₀_equiv_withZeroMulInt_strictMono _).lt_iff_lt,
    valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (v.valuation_surjective K),
    OrderMonoidIso.apply_symm_apply, ← log_lt_log (by simp_all) (by simp)] at hx
  rw [← σL.strictMono.lt_iff_lt]
  refine lt_of_eq_of_lt (WithVal.valueGroupOrderIso₀_restrict (w.valuation L) _) ?_
  rw [← (valueGroup₀_equiv_withZeroMulInt_strictMono _).lt_iff_lt,
    valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective (w.valuation_surjective L),
    WithVal.algebraMap_left_apply, WithVal.algebraMap_right_apply, ← valuation_comap A,
    ← log_lt_log (by simp_all) (by simp), log_pow, nsmul_eq_mul, mul_comm]
  subst hvw
  apply Int.mul_lt_of_lt_ediv (mod_cast pos_of_ne_zero (ramificationIdx_ne_zero A B
    (algebraMap_injective_of_field_isFractionRing A B K L) w)) hx


-- @@ L407-407 verbatim
namespace Extension


-- @@ L409-409 verbatim
variable {v} (w : v.Extension B)


-- @@ L411-418 expanded
@[simps!]
def _root_.WithVal.semialgebraMap {R S Γ₀ Γ₀' : Type*} [CommRing R] [CommRing S]
    [LinearOrderedCommGroupWithZero Γ₀] [LinearOrderedCommGroupWithZero Γ₀'] [Algebra R S]
    (v : Valuation R Γ₀) (w : Valuation S Γ₀') : SemialgHom (algebraMap R S) (WithVal v) (WithVal w)
    where
  __ := algebraMap (WithVal v) (WithVal w)
  map_smul' r
    x := by simp [WithVal.algebraMap_left_apply, WithVal.algebraMap_right_apply, Algebra.smul_def]


-- @@ L420-423 expanded
noncomputable def adicCompletionSemialgHomCompletion :
    SemialgHom (algebraMap K L) (v.valuation K).Completion (w.1.valuation L).Completion :=
  .restrictScalars (WithVal.semialgebraMap (v.valuation K) (w.1.valuation L)) <|
    UniformSpace.Completion.mapSemialgHom _ <| adicValued.continuous_algebraMap K L v w.1 w.2


-- @@ L425-442 expanded
noncomputable def adicCompletionSemialgHom :
    SemialgHom (algebraMap K L) (v.adicCompletion K) (w.1.adicCompletion L)
    where
  toFun x := .ofCompletion (adicCompletionSemialgHomCompletion K L w x.toCompletion)
  map_add' x
    y := by
    apply adicCompletion.ext
    simp only [adicCompletion.toCompletion_add, map_add, adicCompletion.toCompletion_ofCompletion]
  map_smul' k
    x := by
    apply adicCompletion.ext
    exact (adicCompletionSemialgHomCompletion K L w).map_smul k x.toCompletion
  map_zero' := by
    apply adicCompletion.ext
    simp only [adicCompletion.toCompletion_zero, map_zero, adicCompletion.toCompletion_ofCompletion]
  map_one' := by
    apply adicCompletion.ext
    simp only [adicCompletion.toCompletion_one, map_one, adicCompletion.toCompletion_ofCompletion]
  map_mul' x
    y := by
    apply adicCompletion.ext
    simp only [adicCompletion.toCompletion_mul, map_mul, adicCompletion.toCompletion_ofCompletion]


-- @@ L444-446 verbatim
lemma adicCompletionSemialgHom_apply (x : v.adicCompletion K) :
    w.adicCompletionSemialgHom K L x =
      .ofCompletion (adicCompletionSemialgHomCompletion K L w x.toCompletion) := rfl


-- @@ L448-450 verbatim
lemma toCompletion_adicCompletionSemialgHom (x : v.adicCompletion K) :
    (w.adicCompletionSemialgHom K L x).toCompletion =
      adicCompletionSemialgHomCompletion K L w x.toCompletion := rfl


-- @@ L452-454 verbatim
lemma adicCompletionSemialgHom_coe (x : WithVal (v.valuation K)) :
    w.adicCompletionSemialgHom K L x = algebraMap K L x.ofVal :=
  (w.adicCompletionSemialgHom K L).commutes _


-- @@ L456-478 verbatim
open WithZeroTopology in

lemma valued_adicCompletionSemialgHom (x) :
    Valued.v (adicCompletionSemialgHom K L w x) = Valued.v x ^
      (w.1.under A).asIdeal.ramificationIdx' w.1.asIdeal := by
  obtain ⟨y, rfl⟩ := adicCompletion.ofCompletion_surjective K v x
  revert y
  apply funext_iff.mp
  symm
  apply UniformSpace.Completion.ext
  · exact ((Valued.continuous_valuation_of_surjective (v.valuedAdicCompletion_surjective K)).comp
      (adicCompletion.continuous_ofCompletion K v)).pow _
  · exact (Valued.continuous_valuation_of_surjective (w.1.valuedAdicCompletion_surjective L)).comp
      ((adicCompletion.continuous_ofCompletion L w.1).comp
        (UniformSpace.Completion.continuous_map.comp
          ((adicCompletion.continuous_toCompletion K v).comp (adicCompletion.continuous_ofCompletion K v))))
  intro a
  change Valued.v (a : v.adicCompletion K) ^ _ = Valued.v (w.adicCompletionSemialgHom K L a)
  rw [adicCompletionSemialgHom_coe, adicCompletion.valued_coe, ← valuation_comap A K L B w.1]
  simp only [w.2]
  congr 1
  rw [adicCompletion.valued_ofCompletion, Valued.valuedCompletion_apply]
  rfl


-- @@ L480-487 verbatim
lemma adicCompletionSemialgHom_image_adicCompletionIntegers :
    w.adicCompletionSemialgHom K L '' (v.adicCompletionIntegers K) ⊆
      w.1.adicCompletionIntegers L := by
  rintro y ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_adicCompletionIntegers] at hx ⊢
  rw [w.valued_adicCompletionSemialgHom K L]
  rwa [pow_le_one_iff]
  exact ramificationIdx_ne_zero A B (algebraMap_injective_of_field_isFractionRing A B K L) w.1


-- @@ L489-491 verbatim
noncomputable
instance : Algebra (v.adicCompletion K) (w.1.adicCompletion L) :=
  (w.adicCompletionSemialgHom K L).toAlgebra


-- @@ L493-495 verbatim
lemma adicCompletionSemialgHom_continuous : Continuous (w.adicCompletionSemialgHom K L) :=
  (adicCompletion.continuous_ofCompletion L w.1).comp
    (UniformSpace.Completion.continuous_extension.comp (adicCompletion.continuous_toCompletion K v))


-- @@ L497-500 verbatim
instance : ContinuousSMul (adicCompletion K v) (adicCompletion L w.1) := by
  constructor
  have leftCts := w.adicCompletionSemialgHom_continuous K L
  exact Continuous.mul (Continuous.fst' leftCts) continuous_snd


-- @@ L502-502 verbatim
end Extension


-- @@ L504-504 verbatim
section shortcut_instances


-- @@ L506-506 verbatim
private noncomputable instance : Valued (v.adicCompletion K) ℤᵐ⁰ := inferInstance

-- @@ L507-507 verbatim
private noncomputable instance : Field (v.adicCompletion K) := inferInstance

-- @@ L508-508 verbatim
private noncomputable instance : CommRing (v.adicCompletion K) := inferInstance

-- @@ L509-509 verbatim
private noncomputable instance : Ring (v.adicCompletion K) := inferInstance

-- @@ L510-510 verbatim
private noncomputable instance : CommSemiring (v.adicCompletion K) := inferInstance

-- @@ L511-511 verbatim
private noncomputable instance : Semiring (v.adicCompletion K) := inferInstance

-- @@ L512-512 verbatim
private noncomputable instance : AddCommGroup (v.adicCompletion K) := inferInstance

-- @@ L513-513 verbatim
private noncomputable instance : AddCommMonoid (v.adicCompletion K) := inferInstance


-- @@ L515-515 verbatim
private noncomputable instance (w : v.Extension B) : Valued (w.1.adicCompletion L) ℤᵐ⁰ := inferInstance

-- @@ L516-516 verbatim
private noncomputable instance (w : v.Extension B) : Field (w.1.adicCompletion L) := inferInstance

-- @@ L517-517 verbatim
private noncomputable instance (w : v.Extension B) : CommRing (w.1.adicCompletion L) := inferInstance

-- @@ L518-518 verbatim
private noncomputable instance (w : v.Extension B) : Ring (w.1.adicCompletion L) := inferInstance

-- @@ L519-519 verbatim
private noncomputable instance (w : v.Extension B) : CommSemiring (w.1.adicCompletion L) := inferInstance

-- @@ L520-520 verbatim
private noncomputable instance (w : v.Extension B) : Semiring (w.1.adicCompletion L) := inferInstance

-- @@ L521-521 verbatim
private noncomputable instance (w : v.Extension B) : AddCommGroup (w.1.adicCompletion L) := inferInstance

-- @@ L522-522 verbatim
private noncomputable instance (w : v.Extension B) : AddCommMonoid (w.1.adicCompletion L) := inferInstance

-- @@ L523-523 verbatim
private noncomputable instance (w : v.Extension B) : Algebra (v.adicCompletion K) (w.1.adicCompletion L) := inferInstance

-- @@ L524-524 verbatim
private noncomputable instance (w : v.Extension B) : Module (v.adicCompletion K) (w.1.adicCompletion L) := inferInstance


-- @@ L526-526 verbatim
private noncomputable instance : CommRing (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance

-- @@ L527-527 verbatim
private noncomputable instance : Ring (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance

-- @@ L528-528 verbatim
private noncomputable instance : CommSemiring (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance

-- @@ L529-529 verbatim
private noncomputable instance : Semiring (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance

-- @@ L530-530 verbatim
private noncomputable instance : AddCommGroup (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance

-- @@ L531-531 verbatim
private noncomputable instance : AddCommMonoid (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance

-- @@ L532-532 verbatim
private noncomputable instance : Algebra (v.adicCompletion K) (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance

-- @@ L533-533 verbatim
private noncomputable instance : Module (v.adicCompletion K) (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance

-- @@ L534-534 verbatim
private noncomputable instance : Algebra L (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance

-- @@ L535-535 verbatim
private instance : IsTopologicalRing (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance

-- @@ L536-536 verbatim
private instance : IsTopologicalAddGroup (Π w : v.Extension B, w.1.adicCompletion L) := inferInstance


-- @@ L538-538 verbatim
end shortcut_instances


-- @@ L540-540 verbatim
namespace adicCompletion


-- @@ L542-542 verbatim
variable (B)


-- @@ L544-546 expanded
noncomputable def semialgHomPi :
    SemialgHom (algebraMap K L) (v.adicCompletion K) (∀ w : v.Extension B, w.1.adicCompletion L) :=
  Pi.semialgHom _ _ fun i ↦ i.adicCompletionSemialgHom K L


-- @@ L548-550 verbatim
noncomputable abbrev baseChange :
    L ⊗[K] adicCompletion K v →ₐ[L] Π w : v.Extension B, w.1.adicCompletion L :=
  (semialgHomPi K L B v).baseChange_of_algebraMap


-- @@ L552-553 verbatim
lemma baseChange_tmul_apply (x y w) : baseChange K L B v (x ⊗ₜ y) w =
    (algebraMap _ (w.1.adicCompletion L) x) * (algebraMap _ (w.1.adicCompletion L) y) := rfl


-- @@ L555-559 verbatim
open scoped TensorProduct.RightActions in

noncomputable abbrev baseChangeRight :
    L ⊗[K] adicCompletion K v →ₐ[adicCompletion K v] Π w : v.Extension B, w.1.adicCompletion L :=
  (semialgHomPi K L B v).baseChangeRightOfAlgebraMap


-- @@ L561-561 verbatim
section ModuleTopology


-- @@ L563-578 verbatim
open WithZeroMulInt Valued in

noncomputable local instance :
    Valuation.RankOne (Valued.v : Valuation (adicCompletion K v) ℤᵐ⁰) where
  hom' := (toNNReal (by norm_num : (2 : NNReal) ≠ 0)).comp
    (valueGroup₀_equiv_withZeroMulInt _).toMonoidWithZeroHom
  strictMono' := toNNReal_strictMono (by norm_num) |>.comp
    (valueGroup₀_equiv_withZeroMulInt_strictMono _)
  exists_val_nontrivial := by
    obtain ⟨x, hx1, hx2⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
    use algebraMap A K x
    rw [valuedAdicCompletion_eq_valuation' v (algebraMap A K x)]
    constructor
    · simpa only [ne_eq, map_eq_zero, FaithfulSMul.algebraMap_eq_zero_iff]
    · apply ne_of_lt
      rwa [valuation_of_algebraMap, intValuation_lt_one_iff_mem]


-- @@ L580-599 verbatim
attribute [local instance 9999] Algebra.toModule in
open scoped TensorProduct.RightActions in

lemma baseChangeRight_surjective [FiniteDimensional K L] :
    Function.Surjective (baseChangeRight K L B v) := by
  let s := (baseChangeRight K L B v).toLinearMap.range
  have isClosed : IsClosed s.carrier :=
    Submodule.closed_of_finiteDimensional (E := (w : Extension B v) → adicCompletion L w.val) s
  rw [← AlgHom.coe_toLinearMap, ← LinearMap.range_eq_top, Submodule.eq_top_iff']
  simp_rw [← Submodule.mem_toAddSubmonoid, ← AddSubmonoid.mem_toSubsemigroup,
      ← AddSubsemigroup.mem_carrier]
  have denseL : DenseRange (algebraMap L ((w : Extension B v) → adicCompletion L w.val)) := by
    have := Extension.finite A K L B v
    exact denseRange_of_prodAlgebraMap _ Subtype.val_injective
  rw [← isClosed.closure_eq]
  apply Dense.mono _ denseL
  rintro _ ⟨l, rfl⟩
  use (l ⊗ₜ 1)

  exact SemialgHom.baseChange_of_algebraMap_tmul_left (semialgHomPi K L B v) l


-- @@ L601-606 verbatim
attribute [local instance 9999] Algebra.toModule in
open scoped TensorProduct.RightActions in

instance [FiniteDimensional K L] :
    Module.Finite (adicCompletion K v) (Π w : v.Extension B, w.1.adicCompletion L) :=
  .of_surjective (baseChangeRight K L B v).toLinearMap (baseChangeRight_surjective K L B v)


-- @@ L608-612 verbatim
attribute [local instance 9999] Algebra.toModule in

instance [FiniteDimensional K L] (w : v.Extension B) :
    Module.Finite (adicCompletion K v) (adicCompletion L w.1) :=
  Module.Finite.of_pi (fun (w : Extension B v) => w.1.adicCompletion L) w


-- @@ L614-620 verbatim
instance instIsModuleTopology [FiniteDimensional K L] (w : v.Extension B) :
    IsModuleTopology (v.adicCompletion K) (w.1.adicCompletion L) := by
  let Kv := adicCompletion K v
  let Lw := adicCompletion L w.1
  let iso : ((Fin (Module.finrank Kv Lw)) → Kv) ≃L[Kv] Lw :=
    ContinuousLinearEquiv.ofFinrankEq (Module.finrank_fin_fun Kv)
  apply IsModuleTopology.iso iso


-- @@ L622-626 verbatim
instance instIsModuleTopologyPi [FiniteDimensional K L] :

    IsModuleTopology (v.adicCompletion K) (Π (w : v.Extension B), w.1.adicCompletion L) := by
  let := Extension.finite A K L B v
  exact IsModuleTopology.instPi


-- @@ L628-637 verbatim
open scoped TensorProduct.RightActions in

lemma baseChangeRight_isOpenQuotientMap [FiniteDimensional K L] :
    IsOpenQuotientMap (baseChangeRight K L B v) := by
  have : T2Space (L ⊗[K] adicCompletion K v) :=
    IsModuleTopology.t2Space' (K := (adicCompletion K v))
  have hsurj := baseChangeRight_surjective K L B v
  rw [← AlgHom.coe_toLinearMap]
  exact ⟨hsurj, LinearMap.continuous_of_finiteDimensional _,
    LinearMap.isOpenMap_of_finiteDimensional _ hsurj⟩


-- @@ L639-639 verbatim
end ModuleTopology


-- @@ L641-641 verbatim
end adicCompletion


-- @@ L643-643 verbatim
section ModuleTopology


-- @@ L645-645 verbatim
open Extension adicCompletion


-- @@ L647-647 verbatim
variable (B)


-- @@ L649-654 verbatim
noncomputable def tensorAdicCompletionIntegersTo :
    B ⊗[A] adicCompletionIntegers K v →ₐ[B] L ⊗[K] adicCompletion K v :=
  Algebra.TensorProduct.lift
    (Algebra.algHom _ _ _)
    ((Algebra.TensorProduct.includeRight.restrictScalars A).comp (IsScalarTower.toAlgHom _ _ _))
    (fun _ _ ↦ .all _ _)


-- @@ L656-661 verbatim
omit [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L] in
@[simp]
lemma tensorAdicCompletionIntegersTo_tmul (v : HeightOneSpectrum A) (b : B)
    (x : v.adicCompletionIntegers K) : tensorAdicCompletionIntegersTo K L B v (b ⊗ₜ x) =
      (algebraMap B L b) ⊗ₜ x.val := by
  simp [tensorAdicCompletionIntegersTo, Algebra.algHom]


-- @@ L663-716 verbatim
omit [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L] in
open scoped TensorProduct.RightActions in

lemma tensorAdicCompletionIntegersTo_range_subset_closure [FiniteDimensional K L] :
  (tensorAdicCompletionIntegersTo K L B v).range.carrier ⊆
    closure (algebraMap B (L ⊗[K] adicCompletion K v)).range := by
  rintro _ ⟨s, rfl⟩
  induction s with
    | zero =>
        apply subset_closure
        use 0
        simp
    | add x y hx hy =>

        rw [RingHom.map_add]
        apply map_mem_closure₂ _ hx hy _
        · exact (ModuleTopology.continuousAdd _ _).continuous_add
        intro _ ha _ hb
        exact add_mem ha hb
    | tmul b a' =>

        simp only [RingHom.coe_range, tensorAdicCompletionIntegersTo,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul,
          AlgHom.coe_comp, AlgHom.coe_restrictScalars', IsScalarTower.coe_toAlgHom',
          Function.comp_apply, ValuationSubring.algebraMap_apply,
          Algebra.TensorProduct.includeRight_apply]

        let f (y : ↥(adicCompletionIntegers K v)) : (L ⊗[K] adicCompletion K v) :=
          (Algebra.ofId B (L ⊗[K] adicCompletion K v)) b * (1 : L) ⊗ₜ[K] (y : adicCompletion K v)
        have hfval : f = fun (y : ↥(adicCompletionIntegers K v)) =>
              (y : adicCompletion K v) • (Algebra.ofId B (L ⊗[K] adicCompletion K v)) b := by
          ext y
          unfold f
          rw [Algebra.smul_def]
          exact mul_comm _ _
        have hcf : ContinuousAt f a' := by
          apply Continuous.continuousAt
          rw [hfval]
          exact continuous_subtype_val.fun_smul continuous_const

        have hy : a' ∈ closure (Set.range (algebraMap A _)) := by
          apply denseRange_of_integerAlgebraMap
        apply mem_closure_image hcf hy
        constructor
        · exact isClosed_closure

        rintro u ⟨_, ⟨a, rfl⟩, rfl⟩
        apply subset_closure
        use algebraMap A B a * b
        unfold f
        rw [Algebra.algebraMap_eq_smul_one (A := (adicCompletionIntegers K v)) a,
          coe_smul_adicCompletionIntegers, ← TensorProduct.smul_tmul, Algebra.ofId_apply,
          Algebra.TensorProduct.algebraMap_apply, RingHom.map_mul, ← Algebra.smul_def]
        simp


-- @@ L718-764 verbatim
open scoped TensorProduct.RightActions in
omit [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L]  in

lemma tensorAdicCompletionIntegersTo_isClopen_range
    [IsIntegralClosure B A L] [FiniteDimensional K L] :
    IsClopen (SetLike.coe (tensorAdicCompletionIntegersTo K L B v).range) := by

  have : SeparatelyContinuousAdd (L ⊗[K] v.adicCompletion K) :=
    instSeparatelyContinuousAddOfContinuousAdd
  rw [← Subalgebra.coe_toSubring, ← Subring.coe_toAddSubgroup]
  refine OpenAddSubgroup.isClopen ⟨_, ?_⟩

  apply AddSubgroup.isOpen_of_zero_mem_interior
  rw [mem_interior, Subring.coe_toAddSubgroup, Subalgebra.coe_toSubring]

  obtain ⟨ι, b, hb⟩ := FiniteDimensional.exists_is_basis_integral A K L
  let b' : Module.Basis ι (adicCompletion K v) (L ⊗[K] (adicCompletion K v)) := by
    classical
    exact b.rightBaseChange L

  let equiv : L ⊗[K] (adicCompletion K v) ≃L[v.adicCompletion K] (ι → adicCompletion K v) :=
    IsModuleTopology.continuousLinearEquiv (b'.equivFun)

  use equiv.symm '' (Set.pi Set.univ (fun _ => SetLike.coe (adicCompletionIntegers K v)))
  refine ⟨?_, ?_, by simp⟩
  · intro t ⟨g, hg, ht⟩

    have hf : ∀ (i : ι), ∃ (w : B), (algebraMap B L w) = (b i) := by
      intro i
      apply IsIntegralClosure.isIntegral_iff.mp (hb i)
    choose f hf_prop using hf
    let b : B ⊗[A] ↥(adicCompletionIntegers K v) := ∑ (i : ι), (f i) ⊗ₜ ⟨g i, hg i trivial⟩
    use b
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_sum, ← ht]
    unfold equiv
    rw [IsModuleTopology.continuousLinearEquiv_symm_apply, Module.Basis.equivFun_symm_apply]
    apply Finset.sum_congr rfl
    intro x
    simp only [Finset.univ_eq_attach, Finset.mem_attach, tensorAdicCompletionIntegersTo_tmul,
      hf_prop, Module.Basis.rightBaseChange_apply, Algebra.smul_def,
      TensorProduct.RightActions.algebraMap_eval, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      mul_one, imp_self, b']
  · rw [ContinuousLinearEquiv.image_symm_eq_preimage]
    apply IsOpen.preimage equiv.continuous
    apply isOpen_set_pi Set.finite_univ
    rintro i -
    exact Valued.isOpen_valuationSubring (v.adicCompletion K)


-- @@ L766-780 verbatim
omit [Algebra.IsIntegral A B] [IsDedekindDomain B] [IsFractionRing B L] in
open scoped TensorProduct.RightActions in

lemma range_tensorAdicCompletionIntegersTo_eq_closure_range_algebraMap
    [IsIntegralClosure B A L] [FiniteDimensional K L] :
    Set.range (tensorAdicCompletionIntegersTo K L B v) =
      closure (Set.range (algebraMap B (L ⊗[K] adicCompletion K v))) := by
  apply Set.Subset.antisymm
  · apply tensorAdicCompletionIntegersTo_range_subset_closure
  · apply closure_minimal
    · rintro _ ⟨b, rfl⟩
      use b ⊗ₜ[A] 1
      simp
    · apply IsClopen.isClosed
      apply tensorAdicCompletionIntegersTo_isClopen_range


-- @@ L782-791 verbatim
omit [Algebra A L] [IsScalarTower A B L] in

lemma pi_adicCompletionIntegers_eq_closure_range_algebraMap :
    (Set.univ.pi (fun (w : Extension B v) ↦ (w.1.adicCompletionIntegers L).carrier)) =
      closure (Set.range (algebraMap B _)) := by
  let val := fun (w : Extension B v) ↦ w.1
  have hinj : Function.Injective val :=
    (Set.injective_codRestrict Subtype.property).mp fun _ _ a ↦ a
  rw [← closureAlgebraMapIntegers_eq_prodIntegers L _ hinj]
  rfl


-- @@ L793-809 verbatim
open scoped TensorProduct.RightActions in

lemma isClosed_baseChange_image_closure_range_algebraMap [FiniteDimensional K L] :
    IsClosed ((baseChange K L B v) ''
        closure (Set.range (algebraMap B (L ⊗[K] adicCompletion K v)))) := by
  let S := AddSubgroup.map
      (baseChange K L B v).toAddMonoidHom
      (tensorAdicCompletionIntegersTo K L B v).range.toSubring.toAddSubgroup
  have hSclosed : IsClosed S.carrier := by
    apply AddSubgroup.isClosed_of_isOpen
    apply (baseChangeRight_isOpenQuotientMap K L B v).isOpenMap
    apply (tensorAdicCompletionIntegersTo_isClopen_range K L B v).isOpen
  suffices h : (baseChange K L B v) ''
    closure (Set.range (algebraMap B (L ⊗[K] adicCompletion K v))) = S.carrier by
    rwa [h]
  rw [← range_tensorAdicCompletionIntegersTo_eq_closure_range_algebraMap]
  rfl


-- @@ L811-816 verbatim
instance : MulActionHomClass
    (L ⊗[K] adicCompletion K v →ₐ[L] (w : Extension B v) → adicCompletion L w.1) B
    (L ⊗[K] adicCompletion K v) ((w : Extension B v) → adicCompletion L w.1) where
  map_smulₛₗ φ b x := by
    rw [← IsScalarTower.algebraMap_smul L, AlgHom.map_smul_of_tower,
      IsScalarTower.algebraMap_smul, id_def]


-- @@ L818-832 verbatim
open scoped TensorProduct.RightActions in

theorem range_baseChange_comp_tensorAdicCompletionTo_eq_pi [FiniteDimensional K L] :
    Set.range (baseChange K L B v ∘ tensorAdicCompletionIntegersTo K L B v) =
    Set.univ.pi (fun w ↦ (w.1.adicCompletionIntegers L).carrier) := by
  have hrange :
    Set.range (algebraMap B ((w : Extension B v) → adicCompletion L w.1)) =
      (baseChange K L B v) '' (Set.range (algebraMap B (L ⊗[K] adicCompletion K v))) := by
    ext x
    simp [Algebra.algebraMap_eq_smul_one]
  have hrange' := isClosed_baseChange_image_closure_range_algebraMap K L B v
  rw [Set.range_comp, range_tensorAdicCompletionIntegersTo_eq_closure_range_algebraMap,
    pi_adicCompletionIntegers_eq_closure_range_algebraMap, hrange, ← IsClosed.closure_eq hrange']
  exact closure_image_closure
    (baseChangeRight_isOpenQuotientMap K L B v).continuous


-- @@ L834-834 verbatim
namespace Extension


-- @@ L836-836 verbatim
variable {B} (w : v.Extension B)


-- @@ L838-841 verbatim
noncomputable def adicCompletionIntegersRingHom :
    v.adicCompletionIntegers K →+* w.1.adicCompletionIntegers L :=
  RingHom.restrict (w.adicCompletionSemialgHom K L) _ _
    fun x hx ↦ w.adicCompletionSemialgHom_image_adicCompletionIntegers K L ⟨x, hx, rfl⟩


-- @@ L843-844 verbatim
noncomputable instance : Algebra (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) :=
  (w.adicCompletionIntegersRingHom K L).toAlgebra


-- @@ L846-848 verbatim
lemma integer_algebraMap_apply (x : v.adicCompletionIntegers K) :
    algebraMap (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L) x =
      (w.adicCompletionSemialgHom K L) x.val := rfl


-- @@ L850-853 verbatim
variable {v} in

noncomputable instance : Algebra (v.adicCompletionIntegers K) (w.1.adicCompletion L) :=
  Algebra.compHom (w.1.adicCompletion L) (algebraMap _ (adicCompletion K v))


-- @@ L855-855 verbatim
end Extension


-- @@ L857-863 verbatim
open scoped TensorProduct.RightActions in
instance : IsBiscalar B (v.adicCompletionIntegers K) (tensorAdicCompletionIntegersTo K L B v) where
  map_smul₁ _ _ := map_smul ..
  map_smul₂ _ _ := by
    simp only [tensorAdicCompletionIntegersTo_tmul, Algebra.smul_def,
      TensorProduct.RightActions.algebraMap_eval, map_mul, map_one]
    rfl


-- @@ L865-867 verbatim
attribute [local instance 9999] Algebra.toModule Algebra.toSMul in
instance {w : v.Extension B} : IsScalarTower (adicCompletionIntegers K v) (adicCompletion K v)
    (w.1.adicCompletion L) := Submonoid.instIsScalarTowerSubtypeMem (adicCompletionIntegers K v)


-- @@ L869-875 verbatim
open scoped TensorProduct.RightActions in

noncomputable def tensorAdicCompletionIntegersToPiRight :
    B ⊗[A] v.adicCompletionIntegers K →ₐ[v.adicCompletionIntegers K]
        Π w : v.Extension B, w.1.adicCompletion L :=
  ((baseChangeRight K L B v).restrictScalars _).comp
    ((tensorAdicCompletionIntegersTo K L B v).changeScalars _)


-- @@ L877-877 verbatim
namespace Extension


-- @@ L879-879 verbatim
variable (w : v.Extension B)


-- @@ L881-885 verbatim
open scoped TensorProduct.RightActions in

noncomputable def tensorAdicCompletionIntegersToAdicCompletion :
    B ⊗[A] (adicCompletionIntegers K v) →ₐ[adicCompletionIntegers K v] adicCompletion L w.1 :=
  Pi.evalAlgHom _ _ w |>.comp (tensorAdicCompletionIntegersToPiRight K L B v)


-- @@ L887-912 verbatim
open scoped TensorProduct.RightActions in

lemma tensorAdicCompletionIntegersToAdicCompletion_range_eq_integers [FiniteDimensional K L] :
    Set.range (w.tensorAdicCompletionIntegersToAdicCompletion K L B v) =
      adicCompletionIntegers L w.1 := by
  ext x
  have memrange := (range_baseChange_comp_tensorAdicCompletionTo_eq_pi K L B v)
  rw [Set.ext_iff] at memrange
  constructor
  · rintro ⟨y, rfl⟩
    exact (memrange _).mp (Set.mem_range_self y) w trivial
  · intro hx
    classical
    set x' : (w : Extension B v) → adicCompletion L w.val := Pi.single w x with hx'
    obtain ⟨y, (hy : _ = x')⟩ : x' ∈ Set.range _ := by
      rw [memrange x', Set.mem_pi]
      intro w' _
      by_cases h : w = w'
      · rw [← h, hx', Pi.single_eq_same]
        exact hx
      · rw [hx', Pi.single_eq_of_ne' h]
        exact Subring.zero_mem _
    use y
    have hyw := congr_fun hy w
    simp [hx'] at hyw
    exact hyw


-- @@ L914-915 verbatim
noncomputable local instance : MulAction (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  LieAlgebra.ofAssociativeAlgebra.toMulAction


-- @@ L917-936 verbatim
attribute [local instance 9999] Algebra.toSMul Algebra.toModule in
open scoped TensorProduct.RightActions in

noncomputable instance (priority := 1001) [Module.Finite A B] [FiniteDimensional K L] :
    Module.Finite (adicCompletionIntegers K v) (adicCompletionIntegers L w.1) := by
  let integerSubmodule : Submodule (adicCompletionIntegers K v) (adicCompletion L w.1) :=
    let : Algebra (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L).toSubring :=
      inferInstanceAs (Algebra (adicCompletionIntegers K v) (adicCompletionIntegers L w.1))
    have : IsScalarTower (adicCompletionIntegers K v) (adicCompletionIntegers L w.1)
        (adicCompletion L w.1) := .of_algebraMap_smul fun _ _ ↦ rfl
    (adicCompletionIntegers L w.1).toSubmodule.restrictScalars
      (adicCompletionIntegers K v)
  have heq : (w.tensorAdicCompletionIntegersToAdicCompletion K L B v).toLinearMap.range =
      integerSubmodule := by
    ext x
    apply w.tensorAdicCompletionIntegersToAdicCompletion_range_eq_integers K L B v |> Set.ext_iff.mp
  have := Module.Finite.range (w.tensorAdicCompletionIntegersToAdicCompletion K L B v).toLinearMap
  have := w.tensorAdicCompletionIntegersToAdicCompletion_range_eq_integers K L B v
  exact Module.Finite.equiv <| LinearEquiv.ofEq
    (LinearMap.range (w.tensorAdicCompletionIntegersToAdicCompletion K L B v).toLinearMap) _ heq


-- @@ L938-938 verbatim
end Extension


-- @@ L940-940 verbatim
end ModuleTopology


-- @@ L942-942 verbatim
namespace adicCompletion


-- @@ L944-944 verbatim
open Extension


-- @@ L946-946 verbatim
section RamificationInertia


-- @@ L948-948 verbatim
variable {v} (w : v.Extension B)


-- @@ L950-952 verbatim
lemma _root_.WithZero.ofAdd_neg_ofNat_pow (n : ℕ) :
    (WithZero.coe (Multiplicative.ofAdd (-n : ℤ))) = (Multiplicative.ofAdd (-1 : ℤ)) ^ n := by
  rw [← WithZero.coe_pow, ← ofAdd_nsmul, nsmul_eq_mul, Int.mul_neg_one]


-- @@ L954-975 verbatim
theorem ramificationIdx_eq_ramificationIdx :
    (v.completionIdeal K).ramificationIdx' (w.1.completionIdeal L) =
      v.asIdeal.ramificationIdx' w.1.asIdeal := by
  apply Ideal.ramificationIdx_spec
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [mem_completionIdeal_iff'] at hx
    rw [Ideal.mem_comap, adicCompletion.mem_completionIdeal_pow, integer_algebraMap_apply,
      valued_adicCompletionSemialgHom]
    rw [WithZero.ofAdd_neg_ofNat_pow, w.2]
    apply pow_le_pow_left' hx
  · obtain ⟨ϖ, hϖ⟩ := adicCompletion.exists_uniformizer K v
    have hϖ' : ϖ ∈ v.completionIdeal K := by
      rw [mem_completionIdeal_iff, hϖ]
      decide
    rw [Ideal.map_le_iff_le_comap]
    intro h
    have hcomap := h hϖ'
    rw [Ideal.mem_comap, adicCompletion.mem_completionIdeal_pow, integer_algebraMap_apply,
      valued_adicCompletionSemialgHom, hϖ, ← WithZero.ofAdd_neg_ofNat_pow,
      WithZero.coe_le_coe, w.2, Multiplicative.ofAdd_le] at hcomap
    simp at hcomap


-- @@ L977-1008 verbatim
theorem inertiaDeg_eq_inertiaDeg :
    v.asIdeal.inertiaDeg' w.1.asIdeal = (v.completionIdeal K).inertiaDeg' (w.1.completionIdeal L) :=
  letI := Algebra.compHom (adicCompletionIntegers L w.1) (algebraMap A B)
  have : IsScalarTower A B (adicCompletionIntegers L w.1) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower A (adicCompletionIntegers K v) (adicCompletionIntegers L w.1) := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    ext
    rw [Algebra.compHom_algebraMap_eq, RingHom.coe_comp, Function.comp_apply,
      algebraMap_completionIntegers, integer_algebraMap_apply, algebraMap_completionIntegers,
      IsScalarTower.algebraMap_apply B L (adicCompletion L w.1),
      ← IsScalarTower.algebraMap_apply A B L, IsScalarTower.algebraMap_apply A K L]
    symm
    apply SemialgHom.commutes
  have : w.1.asIdeal.LiesOver v.asIdeal := ⟨by simp_rw [← w.2]; rfl⟩

  have : (completionIdeal L w.1).LiesOver (completionIdeal K v) := {
    «over» := by
      rw [Ideal.under_def]
      ext x
      rw [Ideal.mem_comap, mem_completionIdeal_iff, mem_completionIdeal_iff,
        integer_algebraMap_apply, valued_adicCompletionSemialgHom K L, pow_lt_one_iff]
      exact ramificationIdx_ne_zero A B (algebraMap_injective_of_field_isFractionRing A B K L) w.1
  }
  calc v.asIdeal.inertiaDeg' w.1.asIdeal
      = v.asIdeal.inertiaDeg' (w.1.completionIdeal L) := by
        rw [Ideal.inertiaDeg_algebra_tower v.asIdeal w.1.asIdeal (w.1.completionIdeal L),
          inertiaDeg_asIdeal_completionIdeal, mul_one]
    _ = (v.completionIdeal K).inertiaDeg' (w.1.completionIdeal L) := by
        rw [Ideal.inertiaDeg_algebra_tower v.asIdeal (v.completionIdeal K) (w.1.completionIdeal L),
          inertiaDeg_asIdeal_completionIdeal, one_mul]


-- @@ L1010-1011 verbatim
noncomputable local instance : MulAction (v.adicCompletionIntegers K) (v.adicCompletion K) :=
  LieAlgebra.ofAssociativeAlgebra.toMulAction


-- @@ L1013-1022 verbatim
theorem ramificationIdx_mul_inertiaDeg_eq_finrank [FiniteDimensional K L] [Module.Finite A B] :
    v.asIdeal.ramificationIdx' w.1.asIdeal * v.asIdeal.inertiaDeg' w.1.asIdeal =
      Module.finrank (adicCompletion K v) (adicCompletion L w.1) := by
  have : IsScalarTower (adicCompletionIntegers K v) (adicCompletionIntegers L w.1)
      (adicCompletion L w.1) := .of_algebraMap_smul fun _ _ ↦ rfl
  have : IsScalarTower (adicCompletionIntegers K v) (adicCompletion K v) (adicCompletion L w.1) :=
    .of_algebraMap_smul fun _ _ ↦ rfl
  rw [← Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing (adicCompletionIntegers L w.1)
    (adicCompletion K v) (adicCompletion L w.1) (v.completionIdeal_ne_bot K),
    ramificationIdx_eq_ramificationIdx, inertiaDeg_eq_inertiaDeg K L w]


-- @@ L1024-1024 verbatim
end RamificationInertia


-- @@ L1026-1026 verbatim
variable [FiniteDimensional K L] [Module.Finite A B] (B)

-- @@ L1027-1027 verbatim
variable (v : HeightOneSpectrum A) (w : v.Extension B)


-- @@ L1029-1030 verbatim
local instance : Module.Free (v.adicCompletion K) (adicCompletion L w.1) :=
  Module.free_of_finite_type_torsion_free'


-- @@ L1032-1046 verbatim
open scoped TensorProduct.RightActions in

lemma finrank_tensorProduct_adicCompletion_eq_finrank_pi_adicCompletion :
    Module.finrank (adicCompletion K v) (L ⊗[K] adicCompletion K v) =
      Module.finrank (adicCompletion K v) ((w : Extension B v) → adicCompletion L w.val) :=
  letI := Extension.fintype A K L B v
  calc Module.finrank (adicCompletion K v) (L ⊗[K] adicCompletion K v)
    _ = Module.finrank K L := by rw [TensorProduct.finrank_rightAlgebra]
    _ = ∑ (w : Extension B v), Ideal.ramificationIdx' v.asIdeal w.val.asIdeal *
        Ideal.inertiaDeg' v.asIdeal w.val.asIdeal := by
        rw [Ideal.sum_ramification_inertia_extensions]
    _ = ∑ (w : Extension B v), Module.finrank (adicCompletion K v) (adicCompletion L w.val) :=
        Finset.sum_congr rfl fun w _ ↦ ramificationIdx_mul_inertiaDeg_eq_finrank K L w
    _ = Module.finrank (adicCompletion K v) ((w : Extension B v) → adicCompletion L w.val) := by
        rw [Module.finrank_pi_fintype (adicCompletion K v)]


-- @@ L1048-1056 verbatim
attribute [local instance 9999] Algebra.toModule in
open scoped TensorProduct.RightActions in

theorem baseChange_bijective : Function.Bijective (baseChange K L B v) := by
  change Function.Bijective (baseChangeRight K L B v)
  have hsurj := baseChangeRight_surjective K L B v
  refine ⟨?_, hsurj⟩
  have hrank := finrank_tensorProduct_adicCompletion_eq_finrank_pi_adicCompletion K L B v
  rwa [← AlgHom.coe_toLinearMap, LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank]


-- @@ L1058-1060 verbatim
noncomputable def baseChangeAlgEquiv :
    L ⊗[K] v.adicCompletion K ≃ₐ[L] Π w : v.Extension B, w.1.adicCompletion L :=
  AlgEquiv.ofBijective (baseChange K L B v) <| baseChange_bijective K L B v


-- @@ L1062-1068 verbatim
open scoped TensorProduct.RightActions in

private lemma rightActions_smul_tmul_right {R S M : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [AddCommMonoid M] [Module R M] (s : S) (m : M) (t : S) :
    s • (m ⊗ₜ[R] t) = m ⊗ₜ[R] (s * t) := by
  rw [TensorProduct.RightActions.smul_def, TensorProduct.comm_tmul, TensorProduct.smul_tmul',
    smul_eq_mul, TensorProduct.comm_symm_tmul]


-- @@ L1070-1078 verbatim
open scoped TensorProduct.RightActions in

private lemma rightActions_smul_eq_one_tmul_mul {R S M : Type*} [CommSemiring R]
    [CommSemiring S] [Algebra R S] [CommSemiring M] [Algebra R M] (s : S) (x : M ⊗[R] S) :
    s • x = (1 ⊗ₜ[R] s) * x := by
  induction x with
  | zero => simp
  | add a b ha hb => rw [smul_add, mul_add, ha, hb]
  | tmul m t => rw [rightActions_smul_tmul_right, Algebra.TensorProduct.tmul_mul_tmul, one_mul]


-- @@ L1080-1097 verbatim
attribute [local instance 9999] Algebra.toModule in
open scoped TensorProduct.RightActions in

noncomputable def baseChangeContinuousAlgEquiv :
    L ⊗[K] v.adicCompletion K ≃A[L] Π w : v.Extension B, w.1.adicCompletion L :=

  have : IsBiscalar L (v.adicCompletion K) (baseChangeAlgEquiv K L B v).toAlgHom :=
    { map_smul₁ := fun l x => by exact (baseChange K L B v).toLinearMap.map_smul l x
      map_smul₂ := fun s x => by
        rw [rightActions_smul_eq_one_tmul_mul, map_mul]
        funext w
        rw [Pi.mul_apply, Pi.smul_apply, Algebra.smul_def]
        congr 1

        show baseChange K L B v (1 ⊗ₜ[K] s) w = algebraMap (adicCompletion K v) (adicCompletion L w.1) s
        rw [baseChange_tmul_apply, map_one, one_mul] }
  IsModuleTopology.continuousAlgEquivOfIsBiscalar (v.adicCompletion K)
    (baseChangeAlgEquiv K L B v)


-- @@ L1099-1102 verbatim
noncomputable def integerBaseChangeLinearEquiv :
    B ⊗[A] v.adicCompletion K ≃ₗ[B] ∀ w : v.Extension B, w.1.adicCompletion L :=
  (linearEquivTensorProductModuleLeft A K L B (v.adicCompletion K)).symm.trans
    ((baseChangeAlgEquiv K L B v).toLinearEquiv.restrictScalars B)


-- @@ L1104-1110 verbatim
@[simp]
lemma integerBaseChangeLinearEquiv_tmul_apply (b x) :
    integerBaseChangeLinearEquiv K L B v (b ⊗ₜ[A] x) w =
      algebraMap B _ b * algebraMap _ _ x := by
  rw [integerBaseChangeLinearEquiv, LinearEquiv.trans_apply,
    linearEquivTensorProductModuleLeft_symm_tmul]
  rfl


-- @@ L1112-1114 verbatim
noncomputable def integerSubmodule (v : HeightOneSpectrum A) : Submodule A (adicCompletion K v) :=
  let s : Submodule (adicCompletionIntegers K v) _ := (adicCompletionIntegers K v).toSubmodule
  s.restrictScalars A


-- @@ L1116-1116 verbatim
end adicCompletion


-- @@ L1118-1118 verbatim
namespace adicCompletionIntegers


-- @@ L1120-1120 verbatim
open adicCompletion


-- @@ L1122-1122 verbatim
variable (B)


-- @@ L1124-1126 verbatim
noncomputable def tensorCoe : B ⊗[A] v.adicCompletionIntegers K →ₗ[B] B ⊗[A] v.adicCompletion K :=
  TensorProduct.AlgebraTensorModule.lTensor _ _
    (Algebra.algHom A (adicCompletionIntegers K v) (adicCompletion K v))


-- @@ L1128-1131 verbatim
omit [Algebra.IsIntegral A B] [IsDedekindDomain B] in
@[simp]
lemma tensorCoe_tmul (b : B) (x : v.adicCompletionIntegers K) :
    tensorCoe K B v (b ⊗ₜ x) = b ⊗ₜ x.val := rfl


-- @@ L1133-1133 verbatim
end adicCompletionIntegers


-- @@ L1135-1135 verbatim
namespace adicCompletion


-- @@ L1137-1137 verbatim
open Extension


-- @@ L1139-1139 verbatim
variable [FiniteDimensional K L] [Module.Finite A B]


-- @@ L1141-1157 verbatim
attribute [local instance 9999] SMulCommClass.of_commMonoid TensorProduct.isScalarTower_left
  IsScalarTower.right in
theorem integerBaseChangeLinearEquiv_bijOn (v : HeightOneSpectrum A) :
    Set.BijOn (integerBaseChangeLinearEquiv K L B v)
      (Set.range (adicCompletionIntegers.tensorCoe K B v))
      (Submodule.pi Set.univ fun (w : Extension B v) ↦ integerSubmodule L w.val) := by
  suffices h : ((integerBaseChangeLinearEquiv K L B v) ''
      (LinearMap.range (adicCompletionIntegers.tensorCoe K B v))) =
      Submodule.pi .univ fun (w : Extension B v) ↦ (integerSubmodule L w.val).restrictScalars A from
    h ▸ Equiv.bijOn_image (integerBaseChangeLinearEquiv K L B v).toEquiv
  apply Eq.trans _ (range_baseChange_comp_tensorAdicCompletionTo_eq_pi K L B v)
  rw [LinearMap.coe_range, ← Set.range_comp, ← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp]
  rw [← AlgHom.coe_restrictScalars' B (baseChange K L B v), ← AlgHom.coe_comp,
    ← AlgHom.coe_toLinearMap]
  congr
  ext
  simp [baseChange_tmul_apply]


-- @@ L1159-1159 verbatim
end IsDedekindDomain.HeightOneSpectrum.adicCompletion
