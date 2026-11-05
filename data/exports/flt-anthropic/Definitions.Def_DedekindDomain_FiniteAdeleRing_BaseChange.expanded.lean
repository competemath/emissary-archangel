import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_DedekindDomain_FiniteAdeleRing_TensorRestrictedProduct
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace


-- @@ L5-5 verbatim
set_option maxSynthPendingDepth 3

-- @@ L6-6 verbatim
set_option Elab.async false


-- @@ L8-14 verbatim
/-- A `SemialgHom` (i.e., `ψ` such that `ψ (r • a) = φ r • ψ a` for some `φ : R →+* S`) that
is also continuous. -/
structure ContinuousSemialgHom {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (A B : Type*) [TopologicalSpace A] [TopologicalSpace B]
    [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    extends SemialgHom φ A B where
  continuous_toFun : Continuous toFun


-- @@ L16-17 verbatim
@[inherit_doc ContinuousSemialgHom]
infixr:25 " →SA " => ContinuousSemialgHom _


-- @@ L19-20 verbatim
@[inherit_doc]
notation:25 A " →SA[" φ:25 "] " B:0 => ContinuousSemialgHom φ A B


-- @@ L22-25 verbatim
class ContinuousSemialgHomClass (F : Type*) {R S : outParam Type*}
    [CommSemiring R] [CommSemiring S] (φ : outParam (R →+* S)) (A B : outParam Type*)
    [Semiring A] [Semiring B] [Algebra R A] [Algebra S B] [TopologicalSpace A] [TopologicalSpace B]
    [FunLike F A B] extends SemialgHomClass F φ A B where continuous_toFun (f : F) : Continuous f


-- @@ L27-27 verbatim
namespace ContinuousSemialgHom


-- @@ L29-31 verbatim
variable {R S : Type*} [CommSemiring R] [CommSemiring S] (φ : R →+* S)
    (A B : Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
    [TopologicalSpace A] [TopologicalSpace B]


-- @@ L33-39 expanded
instance instFunLike : FunLike (ContinuousSemialgHom φ A B) A B
    where
  coe f := f.toFun
  coe_injective f g
    h := by
    cases f
    cases g
    congr
    exact DFunLike.coe_injective h


-- @@ L41-42 expanded
instance : CoeOut (ContinuousSemialgHom φ A B) (SemialgHom φ A B) :=
  ⟨fun f => f.toSemialgHom⟩


-- @@ L44-46 verbatim
variable (F : Type*) (A B : outParam Type*)
  [Semiring A] [Semiring B] [Algebra R A] [Algebra S B]
  [FunLike F A B] [TopologicalSpace A] [TopologicalSpace B] [ContinuousSemialgHomClass F φ A B]


-- @@ L48-54 expanded
instance : ContinuousSemialgHomClass (ContinuousSemialgHom φ A B) φ A B
    where
  map_add ψ := ψ.map_add
  map_smulₛₗ ψ := ψ.map_smulₛₗ
  map_mul ψ := ψ.map_mul
  map_one ψ := ψ.map_one
  map_zero ψ := ψ.map_zero
  continuous_toFun ψ := ψ.continuous_toFun


-- @@ L56-59 expanded
variable {F} {φ} {A} {B} in
def _root_.ContinuousSemialgHomClass.toContinuousSemialgHom (f : F) : ContinuousSemialgHom φ A B :=
  { (f : SemialgHom φ A B) with continuous_toFun := ContinuousSemialgHomClass.continuous_toFun f }


-- @@ L61-62 expanded
instance : CoeTC F (ContinuousSemialgHom φ A B) :=
  ⟨ContinuousSemialgHomClass.toContinuousSemialgHom⟩


-- @@ L64-66 expanded
@[simp]
theorem coe_coe (f : F) : ⇑(f : ContinuousSemialgHom φ A B) = f :=
  rfl


-- @@ L68-69 expanded
theorem toSemialgHom_eq_coe (f : ContinuousSemialgHom φ A B) : f.toSemialgHom = f :=
  rfl


-- @@ L71-73 expanded
@[simp]
theorem toLinearMap_eq_coe (f : ContinuousSemialgHom φ A B) : f.toLinearMap = f := by rfl


-- @@ L75-77 expanded
@[simp]
theorem toRingHom_eq_coe (f : ContinuousSemialgHom φ A B) : f.toRingHom = f :=
  rfl


-- @@ L79-81 expanded
theorem commutes (ψ : ContinuousSemialgHom φ A B) (r : R) :
    ψ (algebraMap R A r) = algebraMap S B (φ r) :=
  ψ.toSemialgHom.commutes r


-- @@ L83-87 expanded
def prod {C : Type*} [Semiring C] [Algebra S C] [TopologicalSpace C]
    (f : ContinuousSemialgHom φ A B) (g : ContinuousSemialgHom φ A C) :
    ContinuousSemialgHom φ A (B × C)
    where
  __ := f.toSemialgHom.prod g.toSemialgHom
  continuous_toFun := f.continuous_toFun.prodMk g.continuous_toFun


-- @@ L89-95 expanded
variable {φ A B} in
def prodMap {C D : Type*} [Semiring C] [Semiring D] [Algebra S C] [Algebra S D] [TopologicalSpace C]
    [TopologicalSpace D] [Algebra R B] (f : ContinuousSemialgHom φ A C)
    (g : ContinuousSemialgHom φ B D) : ContinuousSemialgHom φ (A × B) (C × D)
    where
  __ := SemialgHom.prodMap f g
  continuous_toFun := Continuous.prodMap f.continuous_toFun g.continuous_toFun


-- @@ L97-97 verbatim
end ContinuousSemialgHom


-- @@ L99-99 verbatim
section


-- @@ L101-101 verbatim
namespace RestrictedProduct


-- @@ L103-103 verbatim
variable {ι : Type*}

-- @@ L104-104 verbatim
variable {R : ι → Type*} [Π i, Ring (R i)]

-- @@ L105-105 verbatim
variable {S : ι → Type*}

-- @@ L106-106 verbatim
variable [Π i, SetLike (S i) (R i)] [∀ i, SubringClass (S i) (R i)]

-- @@ L107-107 verbatim
variable {B : Π i, S i}

-- @@ L108-108 verbatim
variable {ℱ : Filter ι}


-- @@ L110-110 verbatim
variable {M : ι → Type*} [Π i, AddCommGroup (M i)] [Π i, Module (R i) (M i)]

-- @@ L111-111 verbatim
variable {N : ι → Type*}

-- @@ L112-112 verbatim
variable [Π i, SetLike (N i) (M i)] [∀ i, AddSubgroupClass (N i) (M i)]

-- @@ L113-113 verbatim
variable [∀ i, SMulMemClass (N i) (B i) (M i)]

-- @@ L114-114 verbatim
variable {C : Π i, N i}


-- @@ L116-118 verbatim
instance : SMul (Πʳ i, [R i, B i]_[ℱ]) (Πʳ i, [M i, C i]_[ℱ]) where
  smul r m := ⟨fun i ↦ (r i) • (m i), by
    filter_upwards [r.prop, m.prop] with i hr hm using SMulMemClass.smul_mem ⟨r i, hr⟩ hm⟩


-- @@ L120-124 verbatim
omit [Π i, AddSubgroupClass (N i) (M i)] in
@[simp]
lemma smul_apply' (r : Πʳ i, [R i, B i]_[ℱ]) (m : Πʳ i, [M i, C i]_[ℱ]) (i : ι) :
    (r • m) i = r i • m i :=
  rfl


-- @@ L126-132 verbatim
instance instModuleCoe_fLT : Module (Πʳ i, [R i, B i]_[ℱ]) (Πʳ i, [M i, C i]_[ℱ]) where
  zero_smul m := by ext; simp
  smul_zero r := by ext; simp
  one_smul m := by ext; simp
  add_smul r s m:= by ext; simp [add_smul]
  smul_add r m n := by ext; simp
  mul_smul r s m := by ext; simp [mul_smul]


-- @@ L134-140 verbatim
@[simp]
lemma single_smul [DecidableEq ι] (i : ι) (r : R i) (m : Πʳ i, [M i, C i]) :
    single B i r • m = single C i (r • m i) := by
  ext j
  obtain (rfl | hi) := em (i = j)
  · simp
  · simp [single_eq_of_ne' _ _ hi]


-- @@ L142-148 verbatim
@[simp]
lemma smul_single [DecidableEq ι] (i : ι) (r : Πʳ i, [R i, B i]) (m : M i) :
    r • single C i m = single C i (r i • m) := by
  ext j
  obtain (rfl | hi) := em (i = j)
  · simp
  · simp [single_eq_of_ne' _ _ hi]


-- @@ L150-152 verbatim
lemma single_eq_smul [DecidableEq ι] (i : ι) (m : Πʳ i, [M i, C i]) :
    single B i 1 • m = single C i (m i) := by
  simp


-- @@ L154-154 verbatim
variable {M₂ : ι → Type*} [Π i, AddCommGroup (M₂ i)] [Π i, Module (R i) (M₂ i)]

-- @@ L155-155 verbatim
variable {N₂ : ι → Type*}

-- @@ L156-156 verbatim
variable [Π i, SetLike (N₂ i) (M₂ i)] [∀ i, AddSubgroupClass (N₂ i) (M₂ i)]

-- @@ L157-157 verbatim
variable [∀ i, SMulMemClass (N₂ i) (B i) (M₂ i)]

-- @@ L158-158 verbatim
variable {C₂ : Π i, N₂ i}


-- @@ L160-160 verbatim
section components


-- @@ L162-162 verbatim
variable [DecidableEq ι]


-- @@ L164-173 verbatim
noncomputable def linearMap_component
    (f : Πʳ i, [M i, C i] →ₗ[Πʳ i, [R i, B i]] Πʳ i, [M₂ i, C₂ i]) (i : ι) : M i →ₗ[R i] M₂ i where
  toFun x :=
    f (single C i x) i
  map_add' x y := by
    simp [single_add]
  map_smul' r m := by
    let r' := single B i r
    have hr : r = r' i := by simp [r']
    rw [hr, ← smul_single, map_smul, smul_apply', RingHom.id_apply]


-- @@ L175-177 verbatim
lemma linearMap_component_apply (f : Πʳ i, [M i, C i] →ₗ[Πʳ i, [R i, B i]] Πʳ i, [M₂ i, C₂ i])
    (i : ι) (x : M i) : linearMap_component f i x = f (single C i x) i :=
  rfl


-- @@ L179-181 verbatim
lemma linearMap_apply_eq_component (f : Πʳ i, [M i, C i] →ₗ[Πʳ i, [R i, B i]] Πʳ i, [M₂ i, C₂ i])
    (x : Πʳ i, [M i, C i]) (i : ι) : f x i = (linearMap_component f i) (x i):= by
  rw [linearMap_component_apply, ← single_eq_smul, map_smul, single_smul, single_eq_same, one_smul]


-- @@ L183-183 verbatim
end components


-- @@ L185-185 verbatim
variable [Π i, TopologicalSpace (R i)] [Π i, TopologicalSpace (M i)]


-- @@ L187-187 verbatim
section continuous_smul


-- @@ L189-189 verbatim
variable [∀ i, ContinuousSMul (R i) (M i)] (T : Set ι)


-- @@ L191-194 verbatim
open scoped Filter in
instance : ContinuousSMul (Πʳ i, [R i, B i]_[𝓟 T]) (Πʳ i, [M i, C i]_[𝓟 T]) :=
  isEmbedding_coe_of_principal.continuousSMul isEmbedding_coe_of_principal.continuous
    (fun {c x} ↦ by ext; rfl)


-- @@ L196-196 verbatim
variable [hBopen : Fact (∀ i, IsOpen (B i : Set (R i)))]

-- @@ L197-197 verbatim
variable [hCopen : Fact (∀ i, IsOpen (C i : Set (M i)))]


-- @@ L199-203 verbatim
instance [∀ i, ContinuousSMul (R i) (M i)] :
    ContinuousSMul (Πʳ i, [R i, B i]) (Πʳ i, [M i, C i]) where
  continuous_smul := by
    rw [continuous_dom_prod hBopen.elim hCopen.elim]
    exact fun S hS ↦ (continuous_inclusion hS).comp continuous_smul


-- @@ L205-205 verbatim
end continuous_smul


-- @@ L207-207 verbatim
section components


-- @@ L209-209 verbatim
variable [Π i, TopologicalSpace (M₂ i)]


-- @@ L211-220 verbatim
omit [(i : ι) → TopologicalSpace (R i)] in
theorem isOpenMap_linearMap_of_surjective [DecidableEq ι]
    (hCopen : ∀ i, IsOpen (C i : Set (M i)))
    (hCopen₂ : ∀ i, IsOpen (C₂ i : Set (M₂ i)))
    (f : Πʳ i, [M i, C i] →ₗ[Πʳ i, [R i, B i]] Πʳ i, [M₂ i, C₂ i])
    (hf : ∀ i, IsOpenMap (linearMap_component f i))
    (hsurj : ∀ᶠ i in Filter.cofinite, Set.SurjOn (linearMap_component f i) (C i) (C₂ i)) :
    IsOpenMap f := by
  apply RestrictedProduct.isOpenMap_of_open_components hCopen hCopen₂ f
    (fun i ↦ linearMap_component f i) (linearMap_apply_eq_component f) hf hsurj


-- @@ L222-222 verbatim
end components


-- @@ L224-224 verbatim
section free_topology


-- @@ L226-226 verbatim
variable (n : Type*)


-- @@ L228-231 verbatim
variable (B) in

def piSubringSubmodule (i : ι) : Submodule (B i) (n → R i) :=
  Submodule.pi Set.univ fun (_ : n) ↦ Subring.toSubmodule (Subring.ofClass (B i))


-- @@ L233-247 verbatim
def _root_.LinearEquiv.restrictedProductPi [Fintype n] :
    Πʳ i, [n → R i, piSubringSubmodule B n i]_[ℱ] ≃ₗ[Πʳ i, [R i, B i]_[ℱ]]
      n → Πʳ i, [R i, B i]_[ℱ] where
  toFun x j := map (fun i y ↦ y j)
    (by
      filter_upwards with i r hr
      rw [piSubringSubmodule, Submodule.coe_pi, Set.mem_univ_pi] at hr
      exact hr j)
    x
  invFun x := ⟨fun i j ↦ x j i, by
    have h := fun j ↦ (x j).eventually
    simp [piSubringSubmodule]
    exact h⟩
  map_add' x y := rfl
  map_smul' x y := rfl


-- @@ L249-254 verbatim
lemma isOpen_piSubringSubmodule [Finite n] (hOpen : ∀ i, IsOpen (B i : Set (R i))) (i : ι) :
    IsOpen (SetLike.coe <| piSubringSubmodule B n i) := by
  rw [piSubringSubmodule, Submodule.coe_pi]
  apply isOpen_set_pi Set.finite_univ
  intro j _
  exact hOpen i


-- @@ L256-256 verbatim
variable [∀ i, IsTopologicalRing (R i)]


-- @@ L258-271 verbatim
def _root_.ContinuousLinearEquiv.restrictedProductPi [Fintype n]
    (hOpen : ∀ i, IsOpen (B i : Set (R i))) :
    Πʳ i, [n → R i, piSubringSubmodule B n i] ≃L[Πʳ i, [R i, B i]] n → Πʳ i, [R i, B i] where
  __ := LinearEquiv.restrictedProductPi n
  continuous_toFun := by
    apply continuous_pi
    intro i
    dsimp [LinearEquiv.restrictedProductPi]
    exact Continuous.restrictedProduct_congrRight _ (fun _ ↦ continuous_apply i)
  continuous_invFun := by
    have := Fact.mk hOpen
    have := Fact.mk (isOpen_piSubringSubmodule n hOpen)
    exact IsModuleTopology.continuous_of_linearMap
      (LinearEquiv.restrictedProductPi n).symm.toLinearMap


-- @@ L273-277 verbatim
lemma moduleToplogy_of_prod [Finite n] (hOpen : ∀ i, IsOpen (B i : Set (R i))) :
    IsModuleTopology (Πʳ i, [R i, B i]) (Πʳ i, [n → R i, piSubringSubmodule B n i]) :=
  let := Fintype.ofFinite n
  have := Fact.mk hOpen
  IsModuleTopology.iso (ContinuousLinearEquiv.restrictedProductPi n hOpen).symm


-- @@ L279-279 verbatim
end free_topology


-- @@ L281-281 verbatim
variable [∀ i, IsTopologicalRing (R i)]

-- @@ L282-282 verbatim
variable [∀ i, IsModuleTopology (R i) (M i)]

-- @@ L283-283 verbatim
variable [Module.Finite (Πʳ i, [R i, B i]) (Πʳ i, [M i, C i])]


-- @@ L285-305 verbatim
theorem isModuleTopology (hBOpen : ∀ i, IsOpen (B i : Set (R i)))
    (hCOpen : ∀ i, IsOpen (C i : Set (M i)))
    : IsModuleTopology (Πʳ i, [R i, B i]) (Πʳ i, [M i, C i]) := by
  have := Fact.mk hBOpen
  have := Fact.mk hCOpen
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' (Πʳ i, [R i, B i]) (Πʳ i, [M i, C i])
  let g' := ContinuousLinearEquiv.restrictedProductPi (Fin n) hBOpen
  let g := f ∘ₗ g'.toLinearMap
  have (i : ι) : ContinuousAdd (M i) := IsModuleTopology.toContinuousAdd (R i) (M i)
  have (i : ι) : ContinuousSMul (R i) (M i) := IsModuleTopology.toContinuousSMul (R i) (M i)
  have := moduleToplogy_of_prod (Fin n) hBOpen
  have hsurj : Function.Surjective g := hf.comp g'.surjective
  apply IsModuleTopology.of_isOpenMap_surjective _ g _ hsurj
  · classical
    apply isOpenMap_linearMap_of_surjective (isOpen_piSubringSubmodule (Fin n) hBOpen) hCOpen
    · intro i
      apply IsModuleTopology.isOpenMap_of_surjective
      exact surjective_components_of_surjective _ _ (linearMap_apply_eq_component g) hsurj _
        (Set.Finite.compl_mem_cofinite (Set.finite_singleton i))
    · exact eventually_surjOn_of_surjective Filter.comap_id.symm g _
        (linearMap_apply_eq_component g) hsurj


-- @@ L307-307 verbatim
end RestrictedProduct

-- @@ L308-308 verbatim
end


-- @@ L310-310 verbatim
section


-- @@ L312-317 verbatim
class Pi.FiberwiseSMul {α β : Type*} (f : α → β) (R : β → Type*) (M : α → Type*)
    [(b : β) → Semiring (R b)] [(a : α) → AddCommMonoid (M a)]
    [(b : β) → (σ : {a // f a = b}) → Module (R b) (M σ)]
    [Module ((b : β) → R b) ((a : α) → M a)] : Prop where
  map_smul (f R M) (r : (b : β) → R b) (x : (a : α) → M a) (b : β) (σ : {a // f a = b}) :
    (r • x) σ = r b • x σ


-- @@ L319-327 verbatim
def LinearEquiv.piScalarPiCongrFiberwise {α : Type*} {β : Type*} {R : β → Type*} {γ₁ : α → Type*}
    {γ₂ : β → Type*} {f : α → β} [(b : β) → Semiring (R b)] [(a : α) → AddCommMonoid (γ₁ a)]
    [(b : β) → AddCommMonoid (γ₂ b)] [(b : β) → (a : { a : α // f a = b }) → Module (R b) (γ₁ a)]
    [(b : β) → Module (R b) (γ₂ b)] [Module (∀ b, R b) (∀ a, γ₁ a)] [Pi.FiberwiseSMul f R γ₁]
    (e : (b : β) → ((σ : { a : α // f a = b }) → γ₁ σ.1) ≃ₗ[R b] γ₂ b) :
    ((a : α) → γ₁ a) ≃ₗ[∀ b, R b] ((b : β) → γ₂ b) where
  __ := Equiv.piCongrFiberwise fun b => (e b).toEquiv
  map_add' _ _ := by funext; simp [← Pi.add_def]
  map_smul' r x := by funext; simp [← (e _).map_smul, Pi.FiberwiseSMul.map_smul, Pi.smul_def]


-- @@ L329-334 verbatim
def LinearEquiv.piScalarPiComm {α β : Type*} (R : α → Type*) (φ : α → β → Type*)
    [∀ a, Semiring (R a)] [∀ a b, AddCommMonoid (φ a b)] [∀ a b, Module (R a) (φ a b)] :
    ((a : α) → (b : β) → φ a b) ≃ₗ[∀ a, R a] ((b : β) → (a : α) → φ a b) where
  __ := Equiv.piComm φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl


-- @@ L336-337 verbatim
class Prod.IsProdSMul (R S M N : Type*) [SMul R M] [SMul S N] [SMul (R × S) (M × N)] : Prop where
  map_smul (x : R × S) (y : M × N)  : x • y = (x.1 • y.1, x.2 • y.2)


-- @@ L339-341 verbatim
theorem Prod.IsProdSMul.smul_fst {R S M N : Type*} [SMul R M] [SMul S N] [SMul (R × S) (M × N)]
    [Prod.IsProdSMul R S M N] (x : R × S) (y : M × N) : (x • y).1 = x.1 • y.1 := by
  rw [Prod.IsProdSMul.map_smul x y]


-- @@ L343-345 verbatim
theorem Prod.IsProdSMul.smul_snd {R S M N : Type*} [SMul R M] [SMul S N] [SMul (R × S) (M × N)]
    [Prod.IsProdSMul R S M N] (x : R × S) (y : M × N) : (x • y).2 = x.2 • y.2 := by
  rw [Prod.IsProdSMul.map_smul x y]


-- @@ L347-354 verbatim
open scoped RestrictedProduct in

class RestrictedProduct.FiberwiseSMul {α β : Type*} (f : α → β) (R : (b : β) → Type*)
    (A : (b : β) → Set (R b)) (𝓕 : Filter β) (M : (a : α) → Type*) (B : (a : α) → Set (M a))
    (𝓖 : Filter α) [(b : β) → (σ : { a // f a = b }) → SMul (R b) (M ↑σ)]
    [SMul (Πʳ b, [R b, A b]_[𝓕]) (Πʳ a, [M a, B a]_[𝓖])] : Prop where
  map_smul (r : Πʳ b, [R b, A b]_[𝓕]) (x : Πʳ a, [M a, B a]_[𝓖]) (b : β)
    (σ : {a // f a = b}) : (r • x) σ = r b • x σ

-- @@ L355-355 verbatim
end


-- @@ L357-357 verbatim
section


-- @@ L359-359 verbatim
namespace IsDedekindDomain.FiniteAdeleRing


-- @@ L361-362 verbatim
variable (R K : Type*) [CommRing R] [Field K] [IsDedekindDomain R] [Algebra R K]
  [IsFractionRing R K]


-- @@ L364-365 verbatim
noncomputable abbrev integralAdeles : Subring (FiniteAdeleRing R K) :=
  RestrictedProduct.structureSubring _ _ _


-- @@ L367-367 verbatim
variable {R K}


-- @@ L369-369 verbatim
@[simp] lemma one_apply (v : HeightOneSpectrum R) : (1 : FiniteAdeleRing R K) v = 1 := rfl


-- @@ L371-372 verbatim
@[simp] lemma mul_apply (a b : FiniteAdeleRing R K) (v : HeightOneSpectrum R) :
    (a * b) v = a v * b v := rfl


-- @@ L374-377 verbatim
abbrev mk (f : ∀ v, HeightOneSpectrum.adicCompletion K v)
    (h : ∀ᶠ (i : HeightOneSpectrum R) in Filter.cofinite,
    f i ∈ (fun v ↦ ↑(HeightOneSpectrum.adicCompletionIntegers K v)) i) : FiniteAdeleRing R K :=
  ⟨f, h⟩


-- @@ L379-383 verbatim
@[simp]
lemma mk_apply (f : ∀ v, HeightOneSpectrum.adicCompletion K v)
    (h : ∀ᶠ (i : HeightOneSpectrum R) in Filter.cofinite,
    f i ∈ (fun v ↦ ↑(HeightOneSpectrum.adicCompletionIntegers K v)) i) (v : HeightOneSpectrum R) :
    mk f h v = f v := rfl

-- @@ L384-384 verbatim
end IsDedekindDomain.FiniteAdeleRing


-- @@ L386-386 verbatim
end


-- @@ L388-388 verbatim
section


-- @@ L390-393 verbatim
variable (A K L B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra B L] [IsDedekindDomain A]
    [Algebra K L] [Algebra A L] [IsScalarTower A B L] [IsScalarTower A K L] [Module.Finite A B]
    [IsDedekindDomain B] [IsFractionRing B L]


-- @@ L395-395 verbatim
namespace IsDedekindDomain


-- @@ L397-397 verbatim
open IsDedekindDomain HeightOneSpectrum adicCompletion Extension


-- @@ L399-399 verbatim
open scoped TensorProduct


-- @@ L401-407 verbatim
lemma tendsTo_comap_cofinite [FaithfulSMul A B] :
    Filter.Tendsto (under A (B:=B)) Filter.cofinite Filter.cofinite :=
  have : FaithfulSMul A (FractionRing B) := FractionRing.instFaithfulSMul A B
  letI : Algebra (FractionRing A) (FractionRing B) :=
    FractionRing.liftAlgebra A (FractionRing B)
  (Filter.Tendsto.cofinite_of_finite_preimage_singleton <|
    Extension.finite A (FractionRing A) (FractionRing B) B)


-- @@ L409-415 verbatim
lemma cofinite_mapsTo_adicCompletionSemialgHom :
    ∀ᶠ (w : HeightOneSpectrum B) in Filter.cofinite,
    Set.MapsTo (Extension.adicCompletionSemialgHom K L (v := under A w) ⟨w, rfl⟩)
      (adicCompletionIntegers K (under A w)) (adicCompletionIntegers L w) := by
  apply Filter.Eventually.of_forall
  intro w
  exact Set.image_subset_iff.1 <| adicCompletionSemialgHom_image_adicCompletionIntegers K L ⟨w, rfl⟩


-- @@ L417-417 verbatim
namespace FiniteAdeleRing


-- @@ L419-423 verbatim
noncomputable def mapRingHom : 𝔸ᶠ[A, K] →+* 𝔸ᶠ[B, L] :=
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  RestrictedProduct.mapAlongRingHom (adicCompletion K) (adicCompletion L) (under A)
    (tendsTo_comap_cofinite A B) (fun w ↦ adicCompletionSemialgHom K L (v := w.under A) ⟨w, rfl⟩)
    (cofinite_mapsTo_adicCompletionSemialgHom A K L B)


-- @@ L425-439 expanded
set_option backward.isDefEq.respectTransparency false in
noncomputable def mapSemialgHom : ContinuousSemialgHom (algebraMap K L) 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]
    where
  __ := FiniteAdeleRing.mapRingHom A K L B
  map_smul' k
    a := by
    ext w
    refine congrArg _ ?_
    have h := (adicCompletionSemialgHom K L (v := w.under A) ⟨w, rfl⟩).map_smul' k (a (under A w))
    simp only [Algebra.smul_def'] at h ⊢
    exact h
  continuous_toFun :=
    have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
    RestrictedProduct.mapAlong_continuous _ _ _ (tendsTo_comap_cofinite A B) _
      (cofinite_mapsTo_adicCompletionSemialgHom A K L B) fun w ↦
      adicCompletionSemialgHom_continuous K L ⟨w, rfl⟩


-- @@ L441-443 verbatim
variable {A K B} in
lemma mapSemialgHom_apply (x : 𝔸ᶠ[A, K]) (w : HeightOneSpectrum B) :
    mapSemialgHom A K L B x w = adicCompletionSemialgHom K L ⟨w, rfl⟩ (x (under A w)) := rfl


-- @@ L445-445 verbatim
open scoped TensorProduct.RightActions RestrictedProduct


-- @@ L447-447 verbatim
variable [Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]]


-- @@ L449-451 verbatim
instance : Algebra (Πʳ v : HeightOneSpectrum A, [v.adicCompletion K, v.adicCompletionIntegers K])
    (Πʳ w: HeightOneSpectrum B, [w.adicCompletion L, w.adicCompletionIntegers L]) :=
  inferInstanceAs (Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L])


-- @@ L453-457 verbatim
attribute [local instance 9999] Algebra.toSMul in

class ComapFiberwiseSMul extends RestrictedProduct.FiberwiseSMul (α := HeightOneSpectrum B)
    (under A) (adicCompletion K) (fun v ↦ adicCompletionIntegers K v) Filter.cofinite
    (adicCompletion L) (fun w ↦ adicCompletionIntegers L w) Filter.cofinite


-- @@ L459-459 verbatim
variable [ComapFiberwiseSMul A K L B]


-- @@ L461-464 verbatim
variable {A K L B} in
theorem ComapFiberwiseSMul.map_smul' (x : 𝔸ᶠ[A, K]) (y : 𝔸ᶠ[B, L]) (v : HeightOneSpectrum A)
    (w : v.Extension B) : (x • y) w.1 = x v • y w.1 :=
  ComapFiberwiseSMul.toFiberwiseSMul.map_smul x y v w


-- @@ L466-470 verbatim
variable {A K B} in
lemma BaseChange.algebraMap_apply (w : HeightOneSpectrum B) (x : 𝔸ᶠ[A, K]) :
    algebraMap _ 𝔸ᶠ[B, L] x w = adicCompletionSemialgHom K L ⟨w, rfl⟩ (x (under A w)) := by
  simp [Algebra.algebraMap_eq_smul_one, ComapFiberwiseSMul.map_smul' x 1 (w.under A) ⟨w, rfl⟩,
    RingHom.smul_toAlgebra, SemialgHom.toLinearMap_eq_coe]


-- @@ L472-472 verbatim
noncomputable section bijection


-- @@ L474-475 verbatim
def tensorEquivTensor [FiniteDimensional K L] : L ⊗[K] 𝔸ᶠ[A, K] ≃ₗ[B] B ⊗[A] 𝔸ᶠ[A, K] := by
  exact linearEquivTensorProductModuleLeft A K L B 𝔸ᶠ[A, K]


-- @@ L477-480 verbatim
omit [Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]] [ComapFiberwiseSMul A K L B] in
lemma tensorEquivTensor_tmul [FiniteDimensional K L] (b : B) (x : 𝔸ᶠ[A, K]) :
    tensorEquivTensor A K L B (algebraMap B L b ⊗ₜ[K] x) = b ⊗ₜ[A] x := by
  simp [tensorEquivTensor, linearEquivTensorProductModuleLeft_tmul]


-- @@ L482-497 verbatim
set_option synthInstance.maxHeartbeats 40000 in

set_option maxHeartbeats 400000 in

def tensorEquivRestrictedProduct : B ⊗[A] 𝔸ᶠ[A, K] ≃ₗ[B] Πʳ v, [B ⊗[A] (adicCompletion K v),
    RestrictedProduct.rangeLTensorLeft A B (adicCompletion K) (integerSubmodule K) v] := by
  have := Module.finitePresentation_of_finite A B
  have := isTorsionFree A K L B
  let f := RestrictedProduct.lTensorEquivLeft A B (adicCompletion K) (integerSubmodule K) .cofinite
  apply LinearEquiv.trans (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B B) ?_) f
  exact {
    __ := AddEquiv.refl _
    map_smul' a x := by
      ext v
      exact congrArg _ (Algebra.smul_def a (x v) |>.symm)
  }


-- @@ L499-503 verbatim
set_option backward.isDefEq.respectTransparency false in
omit [IsFractionRing B L] in
lemma tensorEquivRestrictedProduct_tmul (b : B) (x : 𝔸ᶠ[A, K]) (v : HeightOneSpectrum A) :
    tensorEquivRestrictedProduct A K L B (b ⊗ₜ[A] x) v = b ⊗ₜ[A] (x v) := by
  simp [tensorEquivRestrictedProduct]


-- @@ L505-516 verbatim
set_option synthInstance.maxHeartbeats 40000 in

set_option maxHeartbeats 400000 in

def restrictedProduct_tensorProduct_equiv_restrictedProduct_prod [FiniteDimensional K L] :
    Πʳ v, [B ⊗[A] (adicCompletion K v),
      RestrictedProduct.rangeLTensorLeft A B (adicCompletion K) (integerSubmodule K) v] ≃ₗ[B]
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.val,
      Submodule.pi Set.univ fun w : Extension B v ↦ (integerSubmodule L w.val)] :=
  LinearEquiv.restrictedProductCongrRight (R₁ := (B ⊗[A] adicCompletion K ·))
    (S₁ := fun v ↦ Submodule B (B ⊗[A] adicCompletion K v)) (integerBaseChangeLinearEquiv K L B)
      (.of_forall <| integerBaseChangeLinearEquiv_bijOn K L)


-- @@ L518-522 verbatim
omit [Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]] [ComapFiberwiseSMul A K L B] in
lemma restrictedProduct_tensorProduct_equiv_restrictedProduct_prod_apply [FiniteDimensional K L]
    (f) (v : HeightOneSpectrum A) :
    FiniteAdeleRing.restrictedProduct_tensorProduct_equiv_restrictedProduct_prod A K L B f v =
    integerBaseChangeLinearEquiv K L B v (f v) := rfl


-- @@ L524-544 verbatim
set_option synthInstance.maxHeartbeats 40000 in

set_option maxHeartbeats 400000 in

def restrictedProduct_prod_equiv :
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.val,
      Submodule.pi .univ fun w : Extension B v ↦ (integerSubmodule L w.val)] ≃ₗ[B]
    𝔸ᶠ[B, L] :=
  have : FaithfulSMul A B := FaithfulSMul.of_field_isFractionRing A B K L
  {
    __ := RestrictedProduct.flatten_equiv'
      (fun w : HeightOneSpectrum B ↦ SetLike.coe <| w.adicCompletionIntegers L)
      (tendsTo_comap_cofinite A B)
    map_add' x y := rfl
    map_smul' a x := by
      ext w
      refine congrArg _ ?_
      change a • (x (under A w) ⟨w, rfl⟩) = _
      simp [Submodule.coe_pi,Algebra.smul_def, RingHom.id_apply, Equiv.toFun_as_coe]
      rfl
  }


-- @@ L546-548 verbatim
omit [Algebra 𝔸ᶠ[A, K] 𝔸ᶠ[B, L]] [ComapFiberwiseSMul A K L B] in
lemma restrictedProduct_prod_equiv_apply (f) (w : HeightOneSpectrum B) :
    restrictedProduct_prod_equiv A K L B f w = f (under A w) ⟨w, rfl⟩ := rfl


-- @@ L550-560 verbatim
set_option synthInstance.maxHeartbeats 40000 in

set_option maxHeartbeats 400000 in

def baseChangeLinearEquiv [FiniteDimensional K L] : L ⊗[K] 𝔸ᶠ[A, K] ≃ₗ[L] 𝔸ᶠ[B, L] :=
  let f₁ := tensorEquivTensor A K L B
  let f₂ := tensorEquivRestrictedProduct A K L B
  let f₃ := restrictedProduct_tensorProduct_equiv_restrictedProduct_prod A K L B
  let f₄ := restrictedProduct_prod_equiv A K L B
  let f := f₁ ≪≫ₗ f₂ ≪≫ₗ f₃ ≪≫ₗ f₄
  LinearEquiv.extendScalarsOfIsLocalization (nonZeroDivisors B) L f


-- @@ L562-563 verbatim
lemma algebraMap_apply_eq_algebraMap (x : K) (v : HeightOneSpectrum A) :
    algebraMap K 𝔸ᶠ[A, K] x v = algebraMap K (v.adicCompletion K) x := rfl


-- @@ L565-578 verbatim
set_option synthInstance.maxHeartbeats 40000 in

set_option maxHeartbeats 400000 in
@[simp]
lemma baseChangeLinearEquiv_tmul [FiniteDimensional K L] (b : B) (x : 𝔸ᶠ[A, K]) :
    baseChangeLinearEquiv A K L B (algebraMap B L b ⊗ₜ x) =
      (algebraMap _ 𝔸ᶠ[B, L] b) * (algebraMap _ 𝔸ᶠ[B, L] x) := by
  ext w
  simp [baseChangeLinearEquiv, restrictedProduct_prod_equiv_apply, tensorEquivTensor_tmul,
    restrictedProduct_tensorProduct_equiv_restrictedProduct_prod_apply,
    tensorEquivRestrictedProduct_tmul, BaseChange.algebraMap_apply,
    IsScalarTower.algebraMap_apply B L 𝔸ᶠ[B, L],
    IsScalarTower.algebraMap_apply B L (w.adicCompletion L), -Submodule.coe_pi]
  rfl


-- @@ L580-604 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem baseChange_bijective [FiniteDimensional K L] :
    Function.Bijective (SemialgHom.baseChange_of_algebraMap <|
      (mapSemialgHom A K L B).toSemialgHom) := by
  suffices ⇑(SemialgHom.baseChange_of_algebraMap <| FiniteAdeleRing.mapSemialgHom A K L B) =
      ⇑(FiniteAdeleRing.baseChangeLinearEquiv A K L B) by
    rw [ContinuousSemialgHom.toSemialgHom_eq_coe, this]
    exact (FiniteAdeleRing.baseChangeLinearEquiv A K L B).bijective
  rw [← AlgHom.coe_toLinearMap, ← LinearEquiv.coe_toLinearMap]

  apply congr_arg _ <| LinearMap.ext fun x ↦ ?_
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul l x =>
    ext w
    refine congrArg _ ?_
    obtain ⟨⟨b, s⟩, hl : (s : B) • l = algebraMap B L b⟩ :=
      IsLocalizedModule.surj (M := B) (M' := L) (nonZeroDivisors B) (Algebra.linearMap B L) l
    rw [LinearEquiv.coe_coe, ← IsUnit.smul_left_cancel <| IsLocalization.map_units L s]
    simp only [Algebra.smul_def, ← algebraMap_apply_eq_algebraMap, ← mul_apply]
    simp only [← Algebra.smul_def, ← map_smul]
    simp [hl, baseChangeLinearEquiv_tmul, BaseChange.algebraMap_apply, mapSemialgHom_apply,
      SemialgHom.baseChange_of_algebraMap_tmul, Algebra.compHom_algebraMap_apply,
      TensorProduct.smul_tmul']
  | add => simp_all


-- @@ L606-609 verbatim
def baseChangeAlgEquiv [FiniteDimensional K L] :
    L ⊗[K] 𝔸ᶠ[A, K] ≃ₐ[L] 𝔸ᶠ[B, L] :=
  .ofBijective (SemialgHom.baseChange_of_algebraMap <| FiniteAdeleRing.mapSemialgHom A K L B)
    (FiniteAdeleRing.baseChange_bijective A K L B)


-- @@ L611-619 verbatim
def baseChangeAdeleAlgEquiv [FiniteDimensional K L] :
    L ⊗[K] 𝔸ᶠ[A, K] ≃ₐ[𝔸ᶠ[A, K]] 𝔸ᶠ[B, L] where
  __ := SemialgHom.baseChangeRightOfAlgebraMap <|
    (FiniteAdeleRing.mapSemialgHom A K L B).toSemialgHom
  __ := FiniteAdeleRing.baseChangeAlgEquiv A K L B
  commutes' x := by
    ext
    simp [BaseChange.algebraMap_apply]
    rfl


-- @@ L621-622 verbatim
instance [FiniteDimensional K L] : Module.Finite 𝔸ᶠ[A, K] 𝔸ᶠ[B, L] :=
  Module.Finite.equiv (FiniteAdeleRing.baseChangeAdeleAlgEquiv A K L B).toLinearEquiv


-- @@ L624-624 verbatim
end bijection


-- @@ L626-626 verbatim
section moduleTopology


-- @@ L628-632 verbatim
attribute [local instance 9999] Algebra.toModule in

noncomputable local instance (v : HeightOneSpectrum A) : Module (adicCompletionIntegers K v)
    ((w : Extension B v) → adicCompletion L w.val) :=
  Module.compHom _ (algebraMap (adicCompletionIntegers K v) (adicCompletion K v))


-- @@ L634-636 verbatim
noncomputable local instance (v : HeightOneSpectrum A) : SMul (adicCompletionIntegers K v)
    ((w : Extension B v) → adicCompletion L w.val) :=
  Module.toDistribMulAction.toDistribSMul.toSMul


-- @@ L638-639 verbatim
noncomputable local instance (v : HeightOneSpectrum A) : MulAction (v.adicCompletionIntegers K)
    (v.adicCompletion K) := LieAlgebra.ofAssociativeAlgebra.toMulAction


-- @@ L641-655 verbatim
attribute [local instance 9999] Algebra.toModule Algebra.toSMul in

noncomputable def piAdicIntegerSubmodule (v : HeightOneSpectrum A) :
    Submodule (adicCompletionIntegers K v) ((w : Extension B v) → adicCompletion L w.val) :=
  let module (w : Extension B v) := Module.compHom (adicCompletion L w.val)
    (algebraMap (adicCompletionIntegers K v) (adicCompletion K v))
  Submodule.pi Set.univ fun (w : Extension B v) ↦
    letI := (module w).toDistribMulAction.toDistribSMul.toSMul
    have : IsScalarTower (adicCompletionIntegers K v) (adicCompletionIntegers L w.val)
        (adicCompletion L w.val) :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    let s := (adicCompletionIntegers L w.val).toSubmodule
    letI : Algebra (v.adicCompletionIntegers K) (w.1.adicCompletionIntegers L).toSubring :=
      inferInstanceAs (Algebra (adicCompletionIntegers K v) (adicCompletionIntegers L w.1))
    s.restrictScalars (adicCompletionIntegers K v)


-- @@ L657-659 verbatim
private noncomputable local instance (priority := 9999) (v : HeightOneSpectrum A) :
    Module (adicCompletion K v) ((w : Extension B v) → adicCompletion L w.val) :=
  Algebra.toModule


-- @@ L661-668 verbatim
set_option synthInstance.maxHeartbeats 80000 in

set_option maxHeartbeats 400000 in

noncomputable local instance : Module 𝔸ᶠ[A, K]
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.1,
    ↑(piAdicIntegerSubmodule A K L B v)] :=
  RestrictedProduct.instModuleCoe_fLT


-- @@ L670-689 verbatim
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 80000 in

set_option maxHeartbeats 400000 in

noncomputable def restrictedProduct_pi_equiv :
    Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.val,
      piAdicIntegerSubmodule A K L B v] ≃L[𝔸ᶠ[A, K]] 𝔸ᶠ[B, L] :=
  have := FaithfulSMul.of_field_isFractionRing A B K L
  let f : _ ≃ₜ 𝔸ᶠ[B, L] := RestrictedProduct.flatten_homeomorph'
    (G := adicCompletion L) (fun w ↦ adicCompletionIntegers L w) (tendsTo_comap_cofinite A B)
  {
    __ := f
    map_add' x y := rfl
    map_smul' r x := by
      ext w
      rw [RingHom.id_apply, Algebra.smul_def, RestrictedProduct.mul_apply,
        BaseChange.algebraMap_apply]
      rfl
  }


-- @@ L691-691 verbatim
attribute [instance 100] RestrictedProduct.instSMulCoeOfSMulMemClass


-- @@ L693-709 verbatim
set_option synthInstance.maxHeartbeats 160000 in

set_option maxHeartbeats 800000 in
lemma restrictedProduct_pi_isModuleTopology [FiniteDimensional K L] : IsModuleTopology 𝔸ᶠ[A, K]
    (Πʳ (v : HeightOneSpectrum A), [(w : Extension B v) → adicCompletion L w.val,
      piAdicIntegerSubmodule A K L B v]) := by
  have :=
    Module.Finite.equiv (FiniteAdeleRing.restrictedProduct_pi_equiv A K L B).symm.toLinearEquiv
  unfold FiniteAdeleRing at this

  refine @RestrictedProduct.isModuleTopology _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ this ?_ ?_
  · exact fun v ↦ Valued.isOpen_integer (adicCompletion K v)
  · intro v
    simp only [piAdicIntegerSubmodule, Submodule.coe_pi, Submodule.coe_restrictScalars]
    apply isOpen_set_pi _ (fun _ _ ↦ Valued.isOpen_integer _)
    rw [Set.finite_univ_iff]
    exact Extension.finite A K L B v


-- @@ L711-716 verbatim
set_option synthInstance.maxHeartbeats 40000 in

set_option maxHeartbeats 400000 in
instance [FiniteDimensional K L] : IsModuleTopology 𝔸ᶠ[A, K] 𝔸ᶠ[B, L] :=
  have := restrictedProduct_pi_isModuleTopology A K L B
  IsModuleTopology.iso (FiniteAdeleRing.restrictedProduct_pi_equiv A K L B)


-- @@ L718-718 verbatim
end moduleTopology


-- @@ L720-722 verbatim
noncomputable def baseChangeAdeleContinuousAlgEquiv [FiniteDimensional K L] :
    L ⊗[K] 𝔸ᶠ[A, K] ≃A[𝔸ᶠ[A, K]] 𝔸ᶠ[B, L] :=
  IsModuleTopology.continuousAlgEquivOfAlgEquiv <| baseChangeAdeleAlgEquiv A K L B


-- @@ L724-727 verbatim
noncomputable def baseChangeContinuousAlgEquiv [FiniteDimensional K L] :
    L ⊗[K] 𝔸ᶠ[A, K] ≃A[L] 𝔸ᶠ[B, L] where
  __ := FiniteAdeleRing.baseChangeAlgEquiv A K L B
  __ := FiniteAdeleRing.baseChangeAdeleContinuousAlgEquiv A K L B


-- @@ L729-729 verbatim
end IsDedekindDomain.FiniteAdeleRing
