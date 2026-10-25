import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.FreeModuleStalkBasisSpan
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor


-- @@ L6-49 verbatim
/-! # The coevaluation section of a locally free sheaf

The canonical coevaluation section `coev ∈ Γ(X, M^∨ ⊗ M)` of a locally free sheaf of modules `M`:
locally, for a free basis `e_j` of `M` with dual basis `e_j^∨`, `coev|_U = Σ_j e_j^∨ ⊗ e_j`; this is
independent of the basis and glues along a cover to a global section (for a line bundle it is the
image of `1` under `O_X ≅ M^∨ ⊗ M`).

References: Stacks 01CM/01CN (duals and tensor products; the canonical isomorphism
`M^∨ ⊗ M ≅ 𝓗om(M, M)` for locally free modules); Mathlib `SheafOfModules.LocalGeneratorsData` /
`FamilyOfElementsOnObjects.IsCompatible.section_`.

## Structure of the file

* `Frame.*` (namespace `AlgebraicGeometry.Scheme.Modules.Frame`): the general theory of *frames* of `M`
  over an open `U`, i.e. `G : (M.over U).GeneratingSections` with `IsIso G.π` and finite index set.
  - `Frame.proj`, `Frame.dualHom`: coordinate projections `free I → O` and the dual basis
    `e_j^∨ = π⁻¹ ≫ proj_j : M|_U → O_U`; `Frame.id_eq_sum`: `𝟙 = Σ_j e_j^∨ ≫ ẽ_j` (coproduct `hom_ext`),
    hence the expansion `m = Σ_j e_j^∨(m) • e_j` of every local section (`Frame.frameData`).
  - `Frame.coevOfData`: the local coevaluation `Σ_j e_j^∨ ⊗ e_j ∈ Γ(M^∨ ⊗ M, Z)` of a pair (sections, functionals);
    `Frame.coevOfData_eq`: it does not depend on the frame. Proof (change-of-basis, Stacks 01CM/01CN
    linear algebra): with `a_{jk} := e_j^∨(e'_k)` one has `e'_k = Σ_j a_{jk} e_j` and
    `e_j^∨ = Σ_k a_{jk} e'^∨_k` (both from the expansion identity), so
    `Σ_j e_j^∨ ⊗ e_j = Σ_{j,k} a_{jk} e'^∨_k ⊗ e_j = Σ_k e'^∨_k ⊗ e'_k` by bilinearity of `⊗` and `Finset.sum_comm`.
  - `Frame.coevOfData_res`, `Frame.isFrameData_res`: restriction along `f : Z ⟶ U` (naturality of the
    sheafification unit of the dual presheaf and of `moduleTensorSection`).
  - `Frame.finite_of_frames`: two frames over opens with a common point have index sets that are finite
    together (rank invariance at a stalk; copies of the private lemmas `localTriv.transport` and
    `finite_index_aux` from `LocalTrivializationPullback` / `FiniteTypeRestrictFreeIndexFinite`).
* The construction proper: `locallyFreeData`, `dualBasisHom`, `dualBasisLocalHom`, `coevLocal`,
  `coevLocal_isCompatible`, `coevSection`.

## Design notes

* `dual M = moduleSheafDual M` is the sheafification of the presheaf `moduleDualPresheaf M` of
  compatible local functionals; the dual basis vectors are written as elements of
  `LocalDualSections X M U` and sent to `Γ(dual M, U)` by the sheafification unit. (Using
  `internalHomPresheaf M O`, which is definitionally but *expensively* equal to `moduleDualPresheaf M`,
  would cost about 15 s of defeq checking per use.)
* `coevLocal M i` is `Σ_j e_j^∨ ⊗ e_j` when the index set of the `i`-th frame is finite and `0` otherwise.
  For an infinite frame over a nonempty open the
  coevaluation does not exist in `M^∨ ⊗ M`, so a fallback is unavoidable; it is never hit for finite-type `M`
  (line bundles, vector bundles), and `Frame.finite_of_frames` shows the fallback is triggered consistently on
  overlaps, which is what makes `coevLocal_isCompatible` true without a finite-type hypothesis.
-/


-- @@ L51-51 verbatim
set_option autoImplicit false

-- @@ L52-52 verbatim
set_option maxHeartbeats 400000


-- @@ L54-54 verbatim
universe u v w u' v'


-- @@ L56-56 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L57-57 verbatim
open scoped AlgebraicGeometry

-- @@ L58-58 verbatim
open AlgebraicGeometry


-- @@ L60-60 verbatim
noncomputable section


-- @@ L62-64 verbatim
/-! File-local shortcuts for the two instance searches that dominate the compile time of this file
(`HasWeakSheafify` / `WEqualsLocallyBijective` on `J.over U`, needed by every `M.over U`); they are
`local`, so nothing leaks to importing files. -/

-- @@ L65-66 verbatim
local instance instHasWeakSheafifyOver (X : Scheme.{u}) (U : X.Opens) :
    HasWeakSheafify ((Opens.grothendieckTopology X).over U) AddCommGrpCat.{u} := inferInstance

-- @@ L67-68 verbatim
local instance instWEqualsLocallyBijectiveOver (X : Scheme.{u}) (U : X.Opens) :
    ((Opens.grothendieckTopology X).over U).WEqualsLocallyBijective AddCommGrpCat.{u} := inferInstance


-- @@ L70-70 verbatim
namespace AlgebraicGeometry.Scheme.Modules.Frame


-- @@ L72-72 verbatim
variable {X : Scheme.{u}} (M : X.Modules)


-- @@ L74-74 verbatim
/-! ### Sections of `M.over Z` and compatible local functionals -/


-- @@ L76-76 verbatim
section Sections


-- @@ L78-78 verbatim
variable (Z : X.Opens)


-- @@ L80-81 verbatim
/-- a section of `M.over Z` evaluated at `V : Over Z`, as a section of `M` over `V.left` -/
abbrev secAt (s : (M.over Z).sections) (V : Over Z) : Γ(M, V.left) := s.1 (op V)


-- @@ L83-84 verbatim
/-- the top object of `Over Z` -/
abbrev topZ : Over Z := Over.mk (𝟙 Z)


-- @@ L86-87 verbatim
/-- a section of `M.over Z` evaluated at the top object, as a section of `M` over `Z` -/
abbrev secTop (s : (M.over Z).sections) : Γ(M, Z) := s.1 (op (topZ Z))


-- @@ L89-90 verbatim
/-- the morphism `V ⟶ topZ` in `Over Z` -/
def toTop (V : Over Z) : V ⟶ topZ Z := Over.homMk V.hom


-- @@ L92-94 verbatim
lemma secTop_res (s : (M.over Z).sections) (V : Over Z) :
    M.presheaf.map V.hom.op (secTop M Z s) = secAt M Z s V :=
  s.2 (toTop Z V).op


-- @@ L96-97 verbatim
/-- compatible families of local functionals `M|_Z → O_Z` (`LocalDualSections`) -/
abbrev LH : Type u := AlgebraicGeometry.Scheme.Modules.LocalDualSections X M Z


-- @@ L99-102 verbatim
/-- the component at `Z` of the sheafification unit of the dual presheaf -/
def dualUnitHom :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (AlgebraicGeometry.Scheme.Modules.moduleDualPresheaf M)).app (op Z)


-- @@ L104-106 verbatim
/-- the sheafification unit `𝓗om(M,O)(Z) → (dual M)(Z)` -/
def dualUnit (ψ : LH M Z) : Γ(AlgebraicGeometry.Scheme.Modules.dual M, Z) :=
  (dualUnitHom M Z).hom ψ


-- @@ L108-109 verbatim
lemma dualUnit_add (ψ ψ' : LH M Z) : dualUnit M Z (ψ + ψ') = dualUnit M Z ψ + dualUnit M Z ψ' :=
  (dualUnitHom M Z).hom.map_add ψ ψ'


-- @@ L111-112 verbatim
lemma dualUnit_zero : dualUnit M Z 0 = 0 :=
  (dualUnitHom M Z).hom.map_zero


-- @@ L114-115 verbatim
lemma dualUnit_smul (r : Γ(X, Z)) (ψ : LH M Z) : dualUnit M Z (r • ψ) = r • dualUnit M Z ψ :=
  (dualUnitHom M Z).hom.map_smul r ψ


-- @@ L117-122 verbatim
lemma dualUnit_sum {ι : Type*} (s : Finset ι) (ψ : ι → LH M Z) :
    dualUnit M Z (∑ k ∈ s, ψ k) = ∑ k ∈ s, dualUnit M Z (ψ k) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact dualUnit_zero M Z
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dualUnit_add, ih]


-- @@ L124-125 verbatim
lemma smul_apply' (r : Γ(X, Z)) (ψ : LH M Z) (V : Over Z) (m : Γ(M, V.left)) :
    (r • ψ).1 V m = X.presheaf.map V.hom.op r * ψ.1 V m := rfl


-- @@ L127-128 verbatim
lemma add_apply' (ψ ψ' : LH M Z) (V : Over Z) (m : Γ(M, V.left)) :
    (ψ + ψ').1 V m = ψ.1 V m + ψ'.1 V m := rfl


-- @@ L130-131 verbatim
lemma zero_apply' (V : Over Z) (m : Γ(M, V.left)) :
    (0 : LH M Z).1 V m = 0 := rfl


-- @@ L133-138 verbatim
lemma sum_apply' {ι : Type*} (s : Finset ι) (ψ : ι → LH M Z) (V : Over Z) (m : Γ(M, V.left)) :
    (∑ k ∈ s, ψ k).1 V m = ∑ k ∈ s, (ψ k).1 V m := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply', ih]


-- @@ L140-143 verbatim
/-- compatibility of a local functional family with restriction -/
lemma apply_res (ψ : LH M Z) {V W : Over Z} (i : V ⟶ W) (m : Γ(M, W.left)) :
    ψ.1 V (M.presheaf.map i.left.op m) = X.presheaf.map i.left.op (ψ.1 W m) :=
  ψ.2 V W i m


-- @@ L145-148 verbatim
/-- compatibility with restriction from the top object -/
lemma apply_res_top (ψ : LH M Z) (V : Over Z) (m : Γ(M, Z)) :
    ψ.1 V (M.presheaf.map V.hom.op m) = X.presheaf.map V.hom.op (ψ.1 (topZ Z) m) :=
  ψ.2 V (topZ Z) (toTop Z V) m


-- @@ L150-152 verbatim
lemma apply_smul (ψ : LH M Z) (V : Over Z) (c : Γ(X, V.left)) (m : Γ(M, V.left)) :
    ψ.1 V (c • m) = c * ψ.1 V m :=
  LinearMap.map_smul (ψ.1 V) c m


-- @@ L154-156 verbatim
lemma apply_sum (ψ : LH M Z) (V : Over Z) {ι : Type*} (s : Finset ι) (m : ι → Γ(M, V.left)) :
    ψ.1 V (∑ k ∈ s, m k) = ∑ k ∈ s, ψ.1 V (m k) :=
  map_sum (ψ.1 V) m s


-- @@ L158-158 verbatim
/-! ### Bilinearity of `moduleTensorSection` -/


-- @@ L160-167 verbatim
lemma tensorSection_sum_left {U : X.Opens} {ι : Type*} (s : Finset ι)
    (f : ι → Γ(AlgebraicGeometry.Scheme.Modules.dual M, U)) (t : Γ(M, U)) :
    AlgebraicGeometry.Scheme.Modules.moduleTensorSection (∑ k ∈ s, f k) t = ∑ k ∈ s, AlgebraicGeometry.Scheme.Modules.moduleTensorSection (f k) t := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact AlgebraicGeometry.Scheme.Modules.moduleTensorSection_zero_left t
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, AlgebraicGeometry.Scheme.Modules.moduleTensorSection_add_left, ih]


-- @@ L169-176 verbatim
lemma tensorSection_sum_right {U : X.Opens} {ι : Type*} (s : Finset ι)
    (f : Γ(AlgebraicGeometry.Scheme.Modules.dual M, U)) (t : ι → Γ(M, U)) :
    AlgebraicGeometry.Scheme.Modules.moduleTensorSection f (∑ k ∈ s, t k) = ∑ k ∈ s, AlgebraicGeometry.Scheme.Modules.moduleTensorSection f (t k) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; exact AlgebraicGeometry.Scheme.Modules.moduleTensorSection_zero_right f
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, AlgebraicGeometry.Scheme.Modules.moduleTensorSection_add_right, ih]


-- @@ L178-182 verbatim
lemma tensorSection_smul_left {U : X.Opens} (a : Γ(X, U))
    (f : Γ(AlgebraicGeometry.Scheme.Modules.dual M, U)) (t : Γ(M, U)) :
    AlgebraicGeometry.Scheme.Modules.moduleTensorSection (a • f) t = a • AlgebraicGeometry.Scheme.Modules.moduleTensorSection f t := by
  have := AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul a 1 f t
  rwa [one_smul, mul_one] at this


-- @@ L184-188 verbatim
lemma tensorSection_smul_right {U : X.Opens} (a : Γ(X, U))
    (f : Γ(AlgebraicGeometry.Scheme.Modules.dual M, U)) (t : Γ(M, U)) :
    AlgebraicGeometry.Scheme.Modules.moduleTensorSection f (a • t) = a • AlgebraicGeometry.Scheme.Modules.moduleTensorSection f t := by
  have := AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul 1 a f t
  rwa [one_smul, one_mul] at this


-- @@ L190-190 verbatim
/-! ### Frame data and the local coevaluation -/


-- @@ L192-197 verbatim
/-- the local coevaluation `Σ_j e_j^∨ ⊗ e_j` attached to a finite family of sections `e`
and functionals `φ` over `Z` -/
def coevOfData {I : Type u} [Fintype I] (e : I → (M.over Z).sections) (φ : I → LH M Z) :
    Γ(AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M, Z) :=
  ∑ j, AlgebraicGeometry.Scheme.Modules.moduleTensorSection (M := AlgebraicGeometry.Scheme.Modules.dual M) (N := M)
    (dualUnit M Z (φ j)) (secTop M Z (e j))


-- @@ L199-202 verbatim
/-- `(e, φ)` is a frame of `M` over `Z`: every local section expands as `m = Σ_j φ_j(m) • e_j` -/
structure IsFrameData {I : Type u} [Fintype I] (e : I → (M.over Z).sections) (φ : I → LH M Z) :
    Prop where
  expand : ∀ (V : Over Z) (m : Γ(M, V.left)), m = ∑ j, (φ j).1 V m • secAt M Z (e j) V


-- @@ L204-219 verbatim
/-- change of frame: each functional of one frame is a combination of those of the other,
with coefficients `a_{jk} = φ_j(e'_k)` -/
lemma phi_eq_sum {I I' : Type u} [Fintype I] [Fintype I']
    (φ : I → LH M Z) (e' : I' → (M.over Z).sections) (φ' : I' → LH M Z)
    (h' : IsFrameData M Z e' φ') (j : I) :
    φ j = ∑ k, ((φ j).1 (topZ Z) (secTop M Z (e' k))) • φ' k := by
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro m
  change (φ j).1 V m = (∑ k, ((φ j).1 (topZ Z) (secTop M Z (e' k))) • φ' k).1 V m
  rw [sum_apply']
  simp only [smul_apply']
  conv_lhs => rw [h'.expand V m, apply_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [apply_smul, ← secTop_res M Z (e' k) V, apply_res_top, mul_comm]


-- @@ L221-245 verbatim
/-- the local coevaluation does not depend on the frame -/
theorem coevOfData_eq {I I' : Type u} [Fintype I] [Fintype I']
    (e : I → (M.over Z).sections) (φ : I → LH M Z) (h : IsFrameData M Z e φ)
    (e' : I' → (M.over Z).sections) (φ' : I' → LH M Z) (h' : IsFrameData M Z e' φ') :
    coevOfData M Z e φ = coevOfData M Z e' φ' := by
  let a : I → I' → Γ(X, Z) := fun j k => (φ j).1 (topZ Z) (secTop M Z (e' k))
  have hφ : ∀ j, φ j = ∑ k, a j k • φ' k := fun j => phi_eq_sum M Z φ e' φ' h' j
  have he' : ∀ k, secTop M Z (e' k) = ∑ j, a j k • secTop M Z (e j) :=
    fun k => h.expand (topZ Z) _
  unfold coevOfData
  calc ∑ j, AlgebraicGeometry.Scheme.Modules.moduleTensorSection (dualUnit M Z (φ j)) (secTop M Z (e j))
      = ∑ j, ∑ k, a j k • AlgebraicGeometry.Scheme.Modules.moduleTensorSection (dualUnit M Z (φ' k)) (secTop M Z (e j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hφ j, dualUnit_sum, tensorSection_sum_left]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [dualUnit_smul, tensorSection_smul_left]
    _ = ∑ k, AlgebraicGeometry.Scheme.Modules.moduleTensorSection (dualUnit M Z (φ' k)) (∑ j, a j k • secTop M Z (e j)) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [tensorSection_sum_right]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [tensorSection_smul_right]
    _ = _ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← he' k]


-- @@ L247-247 verbatim
end Sections


-- @@ L249-249 verbatim
/-! ### Frames coming from `GeneratingSections` with invertible `π` -/


-- @@ L251-251 verbatim
section Frames


-- @@ L253-253 verbatim
variable {U : X.Opens} (G : (M.over U).GeneratingSections)


-- @@ L255-258 verbatim
open Classical in
/-- j-th coordinate projection `free I → O` -/
def proj (j : G.I) : SheafOfModules.free G.I ⟶ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  Cofan.IsColimit.desc (SheafOfModules.isColimitFreeCofan _) (fun j' => if j' = j then 𝟙 _ else 0)


-- @@ L260-263 verbatim
open Classical in
lemma iota_proj (j k : G.I) :
    SheafOfModules.ιFree k ≫ proj M G j = if k = j then 𝟙 _ else 0 :=
  Cofan.IsColimit.fac (SheafOfModules.isColimitFreeCofan _) _ _


-- @@ L265-277 verbatim
open Classical in
lemma sum_proj_iota [Fintype G.I] :
    ∑ j, proj M G j ≫ SheafOfModules.ιFree j = 𝟙 (SheafOfModules.free G.I) := by
  refine Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan _) _ _ (fun k => ?_)
  change SheafOfModules.ιFree k ≫ _ = SheafOfModules.ιFree k ≫ 𝟙 _
  rw [Preadditive.comp_sum, Category.comp_id]
  have h : ∀ j, SheafOfModules.ιFree k ≫ proj M G j ≫ SheafOfModules.ιFree j =
      if k = j then SheafOfModules.ιFree j else 0 := by
    intro j
    rw [← Category.assoc, iota_proj]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun j _ => h j]
  simp


-- @@ L279-281 verbatim
/-- the dual basis morphism `e_j^∨ = π⁻¹ ≫ proj_j : M|_U → O_U` -/
def dualHom [IsIso G.π] (j : G.I) : M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U) :=
  inv G.π ≫ proj M G j


-- @@ L283-283 verbatim
lemma freeHomEquiv_pi : (M.over U).freeHomEquiv G.π = G.s := Equiv.apply_symm_apply _ _


-- @@ L285-286 verbatim
lemma iota_pi (j : G.I) : SheafOfModules.ιFree j ≫ G.π = (M.over U).unitHomEquiv.symm (G.s j) := by
  rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply, freeHomEquiv_pi]


-- @@ L288-290 verbatim
lemma iota_pi_app (j : G.I) (V : Over U) (r : Γ(X, V.left)) :
    ((SheafOfModules.ιFree j ≫ G.π).val.app (op V)) r = r • secAt M U (G.s j) V := by
  rw [iota_pi]; rfl


-- @@ L292-300 verbatim
lemma id_eq_sum [Fintype G.I] [IsIso G.π] :
    𝟙 (M.over U) = ∑ j, dualHom M G j ≫ (SheafOfModules.ιFree j ≫ G.π) := by
  have h := sum_proj_iota M G
  calc 𝟙 (M.over U) = inv G.π ≫ 𝟙 _ ≫ G.π := by simp
    _ = inv G.π ≫ (∑ j, proj M G j ≫ SheafOfModules.ιFree j) ≫ G.π := by rw [h]
    _ = _ := by
      rw [Preadditive.sum_comp, Preadditive.comp_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [dualHom, Category.assoc]


-- @@ L302-307 verbatim
/-- `φ ↦ φ.val.app V m` is additive -/
def appAddHom (N : SheafOfModules.{u} (X.ringCatSheaf.over U)) (V : Over U) (m : Γ(M, V.left)) :
    (M.over U ⟶ N) →+ (N.val.obj (op V) : Type u) where
  toFun φ := (φ.val.app (op V)) m
  map_zero' := rfl
  map_add' _ _ := rfl


-- @@ L309-312 verbatim
/-- `e_j^∨` as a compatible family of local functionals over `U` -/
def dualLocal [IsIso G.π] (j : G.I) : LH M U :=
  ⟨fun V => ((dualHom M G j).val.app (op V)).hom,
    fun _ _ f x => PresheafOfModules.naturality_apply (dualHom M G j).val f.op x⟩


-- @@ L314-321 verbatim
/-- the expansion `m = Σ_j e_j^∨(m) • e_j` for a frame -/
theorem frameData [Fintype G.I] [IsIso G.π] : IsFrameData M U G.s (dualLocal M G) := by
  refine ⟨fun V m => ?_⟩
  have h := congrArg (fun φ => appAddHom M (M.over U) V m φ) (id_eq_sum M G)
  simp only [map_sum] at h
  refine Eq.trans ?_ (h.trans (Finset.sum_congr rfl fun j _ => ?_))
  · rfl
  · exact iota_pi_app M G j V _


-- @@ L323-323 verbatim
/-! ### Restriction of frames along `f : Z ⟶ U` -/


-- @@ L325-325 verbatim
variable {Z : X.Opens} (f : Z ⟶ U)


-- @@ L327-329 verbatim
/-- restriction of a section of `M.over U` to `M.over Z` -/
def resSec (s : (M.over U).sections) : (M.over Z).sections :=
  ⟨fun V => s.1 (op ((Over.map f).obj V.unop)), fun {_ _} i => s.2 ((Over.map f).map i.unop).op⟩


-- @@ L331-336 verbatim
lemma dualUnit_res (ψ : LH M U) :
    (AlgebraicGeometry.Scheme.Modules.dual M).presheaf.map f.op (dualUnit M U ψ) =
      dualUnit M Z (AlgebraicGeometry.Scheme.Modules.localDualRestrict M f ψ) :=
  (PresheafOfModules.naturality_apply
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (AlgebraicGeometry.Scheme.Modules.moduleDualPresheaf M)) f.op ψ).symm


-- @@ L338-340 verbatim
lemma secTop_resSec (s : (M.over U).sections) :
    M.presheaf.map f.op (secTop M U s) = secTop M Z (resSec M f s) :=
  s.2 (Over.homMk (U := (Over.map f).obj (topZ Z)) (V := topZ U) f (Subsingleton.elim _ _)).op


-- @@ L342-346 verbatim
/-- restriction of sections of `N` along `f`, as an additive map between the section groups -/
def resAddHom (N : X.Modules) : Γ(N, U) →+ Γ(N, Z) where
  toFun := N.presheaf.map f.op
  map_zero' := map_zero _
  map_add' := map_add _


-- @@ L348-358 verbatim
/-- restriction of the local coevaluation along `f` -/
theorem coevOfData_res {I : Type u} [Fintype I] (e : I → (M.over U).sections) (φ : I → LH M U) :
    (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M).presheaf.map
        f.op (coevOfData M U e φ) =
      coevOfData M Z (fun j => resSec M f (e j)) (fun j => AlgebraicGeometry.Scheme.Modules.localDualRestrict M f (φ j)) := by
  unfold coevOfData
  refine (map_sum (resAddHom f
    (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M)) _ _).trans ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  refine (AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict f _ _).trans ?_
  rw [dualUnit_res, secTop_resSec]


-- @@ L360-364 verbatim
/-- a restricted frame is a frame -/
theorem isFrameData_res {I : Type u} [Fintype I] (e : I → (M.over U).sections) (φ : I → LH M U)
    (h : IsFrameData M U e φ) :
    IsFrameData M Z (fun j => resSec M f (e j)) (fun j => AlgebraicGeometry.Scheme.Modules.localDualRestrict M f (φ j)) :=
  ⟨fun V m => h.expand ((Over.map f).obj V) m⟩


-- @@ L366-366 verbatim
end Frames



-- @@ L369-369 verbatim
/-! ### Finiteness transfer between frames -/


-- @@ L371-398 verbatim
/-- (copy of the private `localTriv.transport` in `LocalTrivializationPullback`)
`overEquiv` moves `free I ⟶ M.over U` to `free I ⟶ (U.ι)^*M`, preserving epi / iso. -/
private theorem transport {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (I : Type u) (p : SheafOfModules.free I ⟶ M.over U) :
    ∃ π : (SheafOfModules.free (R := U.toScheme.ringCatSheaf) I : U.toScheme.Modules) ⟶
        (Scheme.Modules.pullback U.ι).obj M, (Epi p → Epi π) ∧ (IsIso p → IsIso π) := by
  let F : SheafOfModules.{u} (X.ringCatSheaf.over U) ⥤ SheafOfModules.{u} U.toScheme.ringCatSheaf :=
    (Scheme.Modules.overEquiv U).functor
  have : F.IsEquivalence := inferInstanceAs (Scheme.Modules.overEquiv U).functor.IsEquivalence
  have : PreservesColimitsOfShape (Discrete I) F :=
    (F.asEquivalence.toAdjunction.leftAdjoint_preservesColimits.{u, u}).preservesColimitsOfShape
  let e1 : F.obj (M.over U) ≅ (Scheme.Modules.restrictFunctor U.ι).obj M :=
    (Scheme.Modules.overFunctorEquiv U).app M
  let e2 := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M
  let η : SheafOfModules.unit U.toScheme.ringCatSheaf ≅
      F.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
    (Scheme.Modules.restrictUnitIso U.ι).symm ≪≫
      ((Scheme.Modules.overFunctorEquiv U).app (SheafOfModules.unit X.ringCatSheaf)).symm
  let e3 := SheafOfModules.mapFreeIso F I η
  let e12 : F.obj (M.over U) ≅ (Scheme.Modules.pullback U.ι).obj M := e1 ≪≫ e2
  refine ⟨e3.hom ≫ F.map p ≫ e12.hom, fun hp => ?_, fun hp => ?_⟩
  · have h1 : Epi (F.map p) := F.map_epi p
    have h0 : Epi e12.hom := @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom e12)
    have h2 : Epi (F.map p ≫ e12.hom) := epi_comp _ _
    exact epi_comp _ _
  · have h1 : IsIso (F.map p) := Functor.map_isIso F p
    have h2 : IsIso (F.map p ≫ e12.hom) := IsIso.comp_isIso' h1 (Iso.isIso_hom _)
    exact IsIso.comp_isIso' (Iso.isIso_hom _) h2


-- @@ L400-457 verbatim
/-- (copy of the private `finite_index_aux` in `FiniteTypeRestrictFreeIndexFinite`)
If `(U.ι)^*M ≅ O^{(I)}`, `x ∈ U ∩ V` and `M.over V` has finitely many generators, then `I` is finite. -/
private theorem finite_index_aux {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (I : Type u)
    (e : (Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
    (x : X) (hx : x ∈ U) (V : X.Opens) (hxV : x ∈ V)
    (G : (M.over V).GeneratingSections) [G.IsFiniteType] : Finite I := by
  let F : SheafOfModules.{u} (X.ringCatSheaf.over V) ⥤ SheafOfModules.{u} V.toScheme.ringCatSheaf :=
    (Scheme.Modules.overEquiv V).functor
  have : F.IsEquivalence := inferInstanceAs (Scheme.Modules.overEquiv V).functor.IsEquivalence
  have : PreservesColimitsOfSize.{u, u} F :=
    F.asEquivalence.toAdjunction.leftAdjoint_preservesColimits.{u, u}
  let e1 : F.obj (M.over V) ≅ (Scheme.Modules.restrictFunctor V.ι).obj M :=
    (Scheme.Modules.overFunctorEquiv V).app M
  let η : SheafOfModules.unit V.toScheme.ringCatSheaf ≅
      F.obj (SheafOfModules.unit (X.ringCatSheaf.over V)) :=
    (Scheme.Modules.restrictUnitIso V.ι).symm ≪≫
      ((Scheme.Modules.overFunctorEquiv V).app (SheafOfModules.unit X.ringCatSheaf)).symm
  have : Finite G.I := inferInstance
  let MV : SheafOfModules.{u} V.toScheme.ringCatSheaf := (Scheme.Modules.restrictFunctor V.ι).obj M
  let e1' : F.obj (M.over V) ≅ MV := e1
  let πV : SheafOfModules.free (R := V.toScheme.ringCatSheaf) G.I ⟶ MV :=
    (SheafOfModules.mapFreeIso F G.I η).hom ≫ F.map G.π ≫ e1'.hom
  have hπV : Epi πV := by
    have h1 : Epi (F.map G.π) := F.map_epi G.π
    have h2 : Epi (F.map G.π ≫ e1'.hom) := epi_comp _ _
    exact epi_comp _ _
  let W : X.Opens := U ⊓ V
  have hxW : x ∈ W := ⟨hx, hxV⟩
  let jV : W.toScheme ⟶ V.toScheme := X.homOfLE inf_le_right
  let jU : W.toScheme ⟶ U.toScheme := X.homOfLE inf_le_left
  let RV : SheafOfModules.{u} V.toScheme.ringCatSheaf ⥤ SheafOfModules.{u} W.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor jV
  let RU : SheafOfModules.{u} U.toScheme.ringCatSheaf ⥤ SheafOfModules.{u} W.toScheme.ringCatSheaf :=
    Scheme.Modules.restrictFunctor jU
  have hRV : PreservesColimitsOfSize.{u, u} RV :=
    (Scheme.Modules.restrictAdjunction jV).leftAdjoint_preservesColimits.{u, u}
  have hRU : PreservesColimitsOfSize.{u, u} RU :=
    (Scheme.Modules.restrictAdjunction jU).leftAdjoint_preservesColimits.{u, u}
  have : PreservesColimitsOfShape (Discrete G.I) RV := hRV.preservesColimitsOfShape
  have : PreservesColimitsOfShape (Discrete I) RU := hRU.preservesColimitsOfShape
  have : RV.PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (Scheme.Modules.restrictAdjunction jV)
  let πW : SheafOfModules.free (R := W.toScheme.ringCatSheaf) G.I ⟶ RV.obj MV :=
    (SheafOfModules.mapFreeIso RV G.I (Scheme.Modules.restrictUnitIso jV).symm).hom ≫ RV.map πV
  have hπW : Epi πW := by
    have h1 : Epi (RV.map πV) := RV.map_epi πV
    exact epi_comp _ _
  have hV : jV ≫ V.ι = W.ι := X.homOfLE_ι _
  have hU : jU ≫ U.ι = W.ι := X.homOfLE_ι _
  let ε1 : RV.obj MV ≅ RU.obj ((Scheme.Modules.pullback U.ι).obj M) :=
    ((Scheme.Modules.restrictFunctorComp jV V.ι).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr (hV.trans hU.symm)).app M ≪≫
    (Scheme.Modules.restrictFunctorComp jU U.ι).app M ≪≫
    (Scheme.Modules.restrictFunctor jU).mapIso ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M)
  let ε : RV.obj MV ≅ SheafOfModules.free (R := W.toScheme.ringCatSheaf) I :=
    ε1 ≪≫ RU.mapIso e ≪≫
    (SheafOfModules.mapFreeIso RU I (Scheme.Modules.restrictUnitIso jU).symm).symm
  exact @MiyaokaMori.FreeStalk.finite_of_epi_of_iso_free W.toScheme ⟨x, hxW⟩ G.I _ (RV.obj MV) πW hπW I ε


-- @@ L459-467 verbatim
/-- Two frames of `M` over opens `U`, `U'` containing a common point `z`: if one index set is
finite, so is the other (rank invariance at the stalk of `z`). -/
theorem finite_of_frames {X : Scheme.{u}} (M : X.Modules) {U U' Z : X.Opens} (f : Z ⟶ U) (g : Z ⟶ U')
    (G : (M.over U).GeneratingSections) [Finite G.I]
    (G' : (M.over U').GeneratingSections) [IsIso G'.π] (z : X) (hz : z ∈ Z) : Finite G'.I := by
  obtain ⟨π, -, hπ⟩ := transport M U' _ G'.π
  have := hπ inferInstance
  have : G.IsFiniteType := ⟨inferInstance⟩
  exact finite_index_aux M U' G'.I (asIso π).symm z (g.le hz) U (f.le hz) G



-- @@ L470-480 verbatim
end AlgebraicGeometry.Scheme.Modules.Frame

/- The canonical coevaluation section `coev ∈ Γ(X, M^∨ ⊗ M)` of a locally free `M` (for a line bundle,
   the image of `1` under `O_X ≅ M^∨ ⊗ M`).
   Construction: from `IsLocallyFree` take local freeness data (opens `U_i` covering `X`,
   `free(I_i) ≅ M|_{U_i}`, Mathlib `LocalGeneratorsData` + `IsLocallyFreeData`); on `U_i`, with the
   generators `e_j ∈ Γ(M, U_i)` and the dual basis `e_j^∨ ∈ Γ(M^∨, U_i)` (`inv π` followed by the `j`-th
   coordinate projection `free(I_i) → O`, as a section of the dual presheaf, then sheafified) put
   `t_i := Σ_j e_j^∨ ⊗ e_j ∈ Γ(M^∨ ⊗ M, U_i)`, and glue along the cover with Mathlib's
   `IsCompatible.section_`. The `t_i` agree on overlaps (independence of the basis) by
   `Frame.coevOfData_eq`. -/


-- @@ L482-485 verbatim
/-- The local freeness data extracted from the `IsLocallyFree` hypothesis. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.locallyFreeData {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) [h : M.IsLocallyFree] : SheafOfModules.LocalGeneratorsData.{u} M :=
  Classical.choose h.exists_isLocallyFreeData


-- @@ L487-490 verbatim
instance AlgebraicGeometry.Scheme.Modules.locallyFreeData_isLocallyFreeData
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) [h : M.IsLocallyFree] :
    (AlgebraicGeometry.Scheme.Modules.locallyFreeData M).IsLocallyFreeData :=
  Classical.choose_spec h.exists_isLocallyFreeData


-- @@ L492-500 verbatim
/-- The dual basis vector `e_j^∨ : M|_{U_i} ⟶ O_{U_i}` on `U_i`: `inv π` (`π : free(I_i) ≅ M|_{U_i}`)
followed by the `j`-th coordinate projection (`Frame.dualHom` of the `i`-th frame). -/
noncomputable def AlgebraicGeometry.Scheme.Modules.dualBasisHom {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) [M.IsLocallyFree] (i : (AlgebraicGeometry.Scheme.Modules.locallyFreeData M).I)
    (j : ((AlgebraicGeometry.Scheme.Modules.locallyFreeData M).generators i).I) :
    M.over ((AlgebraicGeometry.Scheme.Modules.locallyFreeData M).X i) ⟶
      SheafOfModules.unit (X.ringCatSheaf.over ((AlgebraicGeometry.Scheme.Modules.locallyFreeData M).X i)) :=
  haveI := (AlgebraicGeometry.Scheme.Modules.locallyFreeData_isLocallyFreeData M).isIso i
  AlgebraicGeometry.Scheme.Modules.Frame.dualHom M ((AlgebraicGeometry.Scheme.Modules.locallyFreeData M).generators i) j


-- @@ L502-510 verbatim
/-- `e_j^∨` as a section over `U_i` of the dual presheaf `moduleDualPresheaf M` (compatible families of
local functionals): for every open `V ⊆ U_i` take the component of `e_j^∨` at `V`
(`Frame.dualLocal` of the `i`-th frame). -/
noncomputable def AlgebraicGeometry.Scheme.Modules.dualBasisLocalHom {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) [M.IsLocallyFree] (i : (AlgebraicGeometry.Scheme.Modules.locallyFreeData M).I)
    (j : ((AlgebraicGeometry.Scheme.Modules.locallyFreeData M).generators i).I) :
    AlgebraicGeometry.Scheme.Modules.LocalDualSections X M ((AlgebraicGeometry.Scheme.Modules.locallyFreeData M).X i) :=
  haveI := (AlgebraicGeometry.Scheme.Modules.locallyFreeData_isLocallyFreeData M).isIso i
  AlgebraicGeometry.Scheme.Modules.Frame.dualLocal M ((AlgebraicGeometry.Scheme.Modules.locallyFreeData M).generators i) j


-- @@ L512-524 verbatim
open Classical in
/-- The local coevaluation `t_i = Σ_j e_j^∨ ⊗ e_j ∈ Γ(M^∨ ⊗ M, U_i)` on `U_i` (when the index set `I_i`
is finite; `0` when `I_i` is infinite, see the design notes in the module docstring). -/
noncomputable def AlgebraicGeometry.Scheme.Modules.coevLocal {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) [M.IsLocallyFree] (i : (AlgebraicGeometry.Scheme.Modules.locallyFreeData M).I) :
    Γ(AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M,
      (AlgebraicGeometry.Scheme.Modules.locallyFreeData M).X i) :=
  if _h : Finite ((AlgebraicGeometry.Scheme.Modules.locallyFreeData M).generators i).I then
    letI := Fintype.ofFinite ((AlgebraicGeometry.Scheme.Modules.locallyFreeData M).generators i).I
    AlgebraicGeometry.Scheme.Modules.Frame.coevOfData M ((AlgebraicGeometry.Scheme.Modules.locallyFreeData M).X i)
      ((AlgebraicGeometry.Scheme.Modules.locallyFreeData M).generators i).s
      (fun j => AlgebraicGeometry.Scheme.Modules.dualBasisLocalHom M i j)
  else 0


-- @@ L526-537 verbatim
/-- Sections of a sheaf of modules over the empty open set form a subsingleton
(`TopCat.Sheaf.isTerminalOfEmpty`: the empty component of a sheaf is terminal). -/
theorem AlgebraicGeometry.Scheme.Modules.subsingleton_sections_bot {X : AlgebraicGeometry.Scheme.{u}}
    (N : X.Modules) : Subsingleton Γ(N, ⊥) := by
  have t : IsTerminal (N.val.presheaf.obj (op (⊥ : X.Opens))) :=
    TopCat.Sheaf.isTerminalOfEmpty (⟨N.val.presheaf, N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} X)
  have h : (𝟙 (N.val.presheaf.obj (op (⊥ : X.Opens)))) = 0 := t.hom_ext _ _
  refine ⟨fun x y => ?_⟩
  have hx : ∀ z : Γ(N, ⊥), z = 0 := fun z => by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) z) h
    exact this
  rw [hx x, hx y]


-- @@ L539-593 verbatim
/-- The family of local coevaluations `(t_i)_i` is compatible on overlaps (the gluing obligation of
`coevSection`).

Mathematical content: `t_i = Σ_j e_j^∨ ⊗ e_j ∈ Γ(M^∨ ⊗ M, U_i)` does not depend on the choice of
free basis on `U_i`, so the restrictions of two pieces to `Z ⊆ U_i ∩ U_{i'}` agree.

Proof: for `Z = ⊥`, `Γ(·, ⊥)` is a singleton (`subsingleton_sections_bot`). Otherwise take `z ∈ Z`:
* if both index sets are finite, restrict both pieces to `Z` (`Frame.coevOfData_res`); they are the
  coevaluations of two frame data on `Z` (`Frame.isFrameData_res` + `Frame.frameData`), equal by
  `Frame.coevOfData_eq` (change of basis);
* if one index set is finite so is the other (`Frame.finite_of_frames`, rank invariance at the
  stalk), so otherwise both are infinite and both pieces are `0`. -/
theorem AlgebraicGeometry.Scheme.Modules.coevLocal_isCompatible
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) [M.IsLocallyFree] :
    CategoryTheory.Presheaf.FamilyOfElementsOnObjects.IsCompatible
      (F := (AlgebraicGeometry.Scheme.Modules.tensor
          (AlgebraicGeometry.Scheme.Modules.dual M) M).val.presheaf ⋙
        CategoryTheory.forget AddCommGrpCat)
      (Y := (AlgebraicGeometry.Scheme.Modules.locallyFreeData M).X)
      (fun i => AlgebraicGeometry.Scheme.Modules.coevLocal M i) := by
  intro Z i i' f g
  change (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M).presheaf.map
      f.op (AlgebraicGeometry.Scheme.Modules.coevLocal M i) =
    (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M).presheaf.map
      g.op (AlgebraicGeometry.Scheme.Modules.coevLocal M i')
  by_cases hZ : Z = ⊥
  · subst hZ
    have := AlgebraicGeometry.Scheme.Modules.subsingleton_sections_bot
      (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M)
    exact Subsingleton.elim _ _
  · obtain ⟨z, hz⟩ := (Opens.ne_bot_iff_nonempty Z).mp hZ
    have := (AlgebraicGeometry.Scheme.Modules.locallyFreeData_isLocallyFreeData M).isIso i
    have := (AlgebraicGeometry.Scheme.Modules.locallyFreeData_isLocallyFreeData M).isIso i'
    by_cases hi : Finite ((AlgebraicGeometry.Scheme.Modules.locallyFreeData M).generators i).I
    · have hi' : Finite ((AlgebraicGeometry.Scheme.Modules.locallyFreeData M).generators i').I :=
        AlgebraicGeometry.Scheme.Modules.Frame.finite_of_frames M f g
          ((AlgebraicGeometry.Scheme.Modules.locallyFreeData M).generators i)
          ((AlgebraicGeometry.Scheme.Modules.locallyFreeData M).generators i') z hz
      let _ := Fintype.ofFinite ((AlgebraicGeometry.Scheme.Modules.locallyFreeData M).generators i).I
      let _ := Fintype.ofFinite ((AlgebraicGeometry.Scheme.Modules.locallyFreeData M).generators i').I
      unfold AlgebraicGeometry.Scheme.Modules.coevLocal
      rw [dif_pos hi, dif_pos hi']
      exact (AlgebraicGeometry.Scheme.Modules.Frame.coevOfData_res M f _ _).trans
        ((AlgebraicGeometry.Scheme.Modules.Frame.coevOfData_eq M Z _ _
          (AlgebraicGeometry.Scheme.Modules.Frame.isFrameData_res M f _ _
            (AlgebraicGeometry.Scheme.Modules.Frame.frameData M _)) _ _
          (AlgebraicGeometry.Scheme.Modules.Frame.isFrameData_res M g _ _
            (AlgebraicGeometry.Scheme.Modules.Frame.frameData M _))).trans
        (AlgebraicGeometry.Scheme.Modules.Frame.coevOfData_res M g _ _).symm)
    · have hi' : ¬ Finite ((AlgebraicGeometry.Scheme.Modules.locallyFreeData M).generators i').I :=
        fun h => hi (AlgebraicGeometry.Scheme.Modules.Frame.finite_of_frames M g f
          ((AlgebraicGeometry.Scheme.Modules.locallyFreeData M).generators i')
          ((AlgebraicGeometry.Scheme.Modules.locallyFreeData M).generators i) z hz)
      unfold AlgebraicGeometry.Scheme.Modules.coevLocal
      rw [dif_neg hi, dif_neg hi', map_zero, map_zero]


-- @@ L595-609 verbatim
/-- The coevaluation section `coev ∈ Γ(X, M^∨ ⊗ M)`: the `t_i` glued along the cover `{U_i}`
(Mathlib `IsCompatible.section_`; compatibility is `coevLocal_isCompatible`). -/
noncomputable def AlgebraicGeometry.Scheme.Modules.coevSection {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) [M.IsLocallyFree] :
    Γ(AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M, ⊤) :=
  let T := AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M
  let q := AlgebraicGeometry.Scheme.Modules.locallyFreeData M
  let x : CategoryTheory.Presheaf.FamilyOfElementsOnObjects
      (T.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) q.X :=
    fun i => AlgebraicGeometry.Scheme.Modules.coevLocal M i
  have hx : x.IsCompatible := AlgebraicGeometry.Scheme.Modules.coevLocal_isCompatible M
  have hF : CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (T.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat) :=
    (CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget _ _ (CategoryTheory.forget AddCommGrpCat)).mp T.isSheaf
  (hx.section_ q.coversTop hF).1 (Opposite.op ⊤)


-- @@ L611-611 verbatim
end
