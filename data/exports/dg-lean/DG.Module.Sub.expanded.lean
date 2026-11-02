import DG.Algebra.Decompose
import DG.Module.Basic


-- @@ L4-19 verbatim
/-!
# dg submodules

A dg submodule of a dg `A`-module `M` is an `A`-submodule which is stable under the
differential and homogeneous (it contains the homogeneous components of each of its elements).
Such a submodule is itself a dg `A`-module, graded by `Sⁿ = S ∩ Mⁿ`, and the inclusion
`S →ᵈᵍ[A] M` is a morphism of dg modules.

* `DG.DGSubmodule A M`: the structure, extending `Submodule A M`.
* `DG.DGSubmodule.subtype`, `DG.DGSubmodule.codRestrict`: the inclusion and corestriction.
* `DG.DGModuleHom.ker`, `DG.DGModuleHom.range`: kernel and image of a morphism.

The decomposition of `S` into homogeneous components is obtained noncomputably from
`DirectSum.IsInternal`, which is proved using that the inclusion is injective of degree `0`
(`DG.coeAddMonoidHom_injective_of_injective`).
-/


-- @@ L21-21 verbatim
open DirectSum


-- @@ L23-23 verbatim
namespace DG


-- @@ L25-26 verbatim
variable {A : Type*} {M : Type*} [Ring A] [DGAddCommGroup A] [AddCommGroup M]
  [DGAddCommGroup M] [Module A M]


-- @@ L28-34 verbatim
/-- A dg submodule of a dg module: an `A`-submodule stable under `d` and containing the
homogeneous components of its elements. -/
structure DGSubmodule (A : Type*) (M : Type*) [Ring A] [DGAddCommGroup A] [AddCommGroup M]
    [DGAddCommGroup M] [Module A M] extends Submodule A M where
  d_mem' : ∀ {m : M}, m ∈ carrier → d m ∈ carrier
  decompose_mem' : ∀ (n : ℤ) {m : M}, m ∈ carrier →
    (decompose (grading (M := M)) m n : M) ∈ carrier


-- @@ L36-36 verbatim
namespace DGSubmodule


-- @@ L38-43 verbatim
instance : SetLike (DGSubmodule A M) M where
  coe S := S.carrier
  coe_injective S T h := by
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _, _⟩ := S
    obtain ⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _, _⟩ := T
    congr


-- @@ L45-45 verbatim
instance : PartialOrder (DGSubmodule A M) := .ofSetLike (DGSubmodule A M) M


-- @@ L47-49 verbatim
@[simp]
theorem mem_toSubmodule {S : DGSubmodule A M} {m : M} : m ∈ S.toSubmodule ↔ m ∈ S :=
  Iff.rfl


-- @@ L51-53 verbatim
@[simp]
theorem mem_mk {p : Submodule A M} {h₁ h₂} {m : M} : m ∈ mk p h₁ h₂ ↔ m ∈ p :=
  Iff.rfl


-- @@ L55-57 verbatim
@[ext]
theorem ext {S T : DGSubmodule A M} (h : ∀ m, m ∈ S ↔ m ∈ T) : S = T :=
  SetLike.ext h


-- @@ L59-61 verbatim
theorem toSubmodule_injective :
    Function.Injective (DGSubmodule.toSubmodule : DGSubmodule A M → Submodule A M) :=
  fun _ _ h => ext fun m => by rw [← mem_toSubmodule, h, mem_toSubmodule]


-- @@ L63-63 verbatim
variable (S : DGSubmodule A M)


-- @@ L65-66 verbatim
theorem d_mem {m : M} (hm : m ∈ S) : d m ∈ S :=
  S.d_mem' hm


-- @@ L68-70 verbatim
theorem decompose_mem (n : ℤ) {m : M} (hm : m ∈ S) :
    (decompose (grading (M := M)) m n : M) ∈ S :=
  S.decompose_mem' n hm


-- @@ L72-75 verbatim
instance : AddSubgroupClass (DGSubmodule A M) M where
  add_mem := fun {S} => S.toSubmodule.add_mem
  zero_mem S := S.toSubmodule.zero_mem
  neg_mem := fun {S} => S.toSubmodule.neg_mem


-- @@ L77-78 verbatim
instance : SMulMemClass (DGSubmodule A M) A M where
  smul_mem := fun {S} a => S.toSubmodule.smul_mem a


-- @@ L80-81 verbatim
@[simp, norm_cast]
theorem coe_add (x y : S) : ((x + y : S) : M) = x + y := rfl


-- @@ L83-84 verbatim
@[simp, norm_cast]
theorem coe_zero : ((0 : S) : M) = 0 := rfl


-- @@ L86-87 verbatim
@[simp, norm_cast]
theorem coe_smul (a : A) (x : S) : ((a • x : S) : M) = a • (x : M) := rfl


-- @@ L89-91 verbatim
/-- The homogeneous components `Sⁿ = S ∩ Mⁿ` of a dg submodule. -/
def grading (n : ℤ) : AddSubgroup S :=
  (DGAddCommGroup.grading n).comap (AddSubgroupClass.subtype S)


-- @@ L93-94 verbatim
theorem mem_grading_iff {n : ℤ} {x : S} : x ∈ S.grading n ↔ (x : M) ∈ DGAddCommGroup.grading n :=
  Iff.rfl


-- @@ L96-108 verbatim
theorem isInternal_grading : DirectSum.IsInternal S.grading := by
  classical
  refine ⟨coeAddMonoidHom_injective_of_injective S.grading (AddSubgroupClass.subtype S)
    (fun _ _ hx => hx) Subtype.val_injective, fun x => ?_⟩
  refine ⟨∑ n ∈ (decompose (DGAddCommGroup.grading (M := M)) (x : M)).support,
    DirectSum.of (fun n => S.grading n) n
      ⟨⟨decompose (DGAddCommGroup.grading (M := M)) (x : M) n, S.decompose_mem n x.2⟩,
        (decompose (DGAddCommGroup.grading (M := M)) (x : M) n).2⟩, ?_⟩
  apply Subtype.ext
  rw [map_sum]
  simp only [DirectSum.coeAddMonoidHom_of]
  rw [AddSubmonoidClass.coe_finsetSum]
  exact DirectSum.sum_support_decompose (DGAddCommGroup.grading (M := M)) (x : M)


-- @@ L110-113 verbatim
/-- The differential of a dg submodule. -/
def d : S →+ S :=
  AddMonoidHom.codRestrict ((DGAddCommGroup.d : M →+ M).comp (AddSubgroupClass.subtype S)) S
    fun x => S.d_mem x.2


-- @@ L115-116 verbatim
@[simp]
theorem coe_d_apply (x : S) : (S.d x : M) = DGAddCommGroup.d (x : M) := rfl


-- @@ L118-123 verbatim
noncomputable instance instDGAddCommGroup : DGAddCommGroup S where
  grading := S.grading
  decomposition := S.isInternal_grading.chooseDecomposition
  d := S.d
  d_mem' hx := DG.d_mem hx
  d_d' x := Subtype.ext (by simp)


-- @@ L125-126 verbatim
@[simp]
theorem coe_d (x : S) : ((DGAddCommGroup.d x : S) : M) = DGAddCommGroup.d (x : M) := rfl


-- @@ L128-131 verbatim
@[simp]
theorem mem_grading {n : ℤ} {x : S} :
    x ∈ DGAddCommGroup.grading n ↔ (x : M) ∈ DGAddCommGroup.grading n :=
  Iff.rfl


-- @@ L133-133 verbatim
variable [DGModule A M]


-- @@ L135-140 verbatim
instance instDGModule : DGModule A S where
  smul_mem _ _ _ _ ha hx := smul_mem_grading (M := M) ha hx
  d_smul' ha x := Subtype.ext (by
    rw [coe_d, coe_smul, d_smul ha (x : M)]
    simp only [coe_add, coe_smul]
    rfl)


-- @@ L142-146 expanded
/-- The inclusion of a dg submodule as a morphism of dg modules. -/
def subtype : DGModuleHom A S M where
  __ := S.toSubmodule.subtype
  map_mem' hx := hx
  map_d' _ := rfl


-- @@ L148-150 verbatim
omit [DGModule A M] in
@[simp]
theorem subtype_apply (x : S) : S.subtype x = x := rfl


-- @@ L152-154 verbatim
omit [DGModule A M] in
theorem subtype_injective : Function.Injective S.subtype :=
  Subtype.val_injective


-- @@ L156-156 verbatim
variable {S} {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N]


-- @@ L158-158 verbatim
omit [DGModule A M]


-- @@ L160-164 expanded
/-- Corestriction of a morphism of dg modules to a dg submodule containing its image. -/
def codRestrict (f : DGModuleHom A N M) (h : ∀ x, f x ∈ S) : DGModuleHom A N S
    where
  __ := LinearMap.codRestrict S.toSubmodule f.toLinearMap h
  map_mem' hx := f.map_mem hx
  map_d' x := Subtype.ext (f.map_d x)


-- @@ L166-168 expanded
@[simp]
theorem coe_codRestrict_apply (f : DGModuleHom A N M) (h : ∀ x, f x ∈ S) (x : N) :
    (codRestrict f h x : M) = f x :=
  rfl


-- @@ L170-172 expanded
@[simp]
theorem subtype_comp_codRestrict (f : DGModuleHom A N M) (h : ∀ x, f x ∈ S) :
    S.subtype.comp (codRestrict f h) = f :=
  rfl


-- @@ L174-179 verbatim
/-- The decomposition of `S` is the restriction of that of `M`. -/
theorem coe_decompose_apply (x : S) (n : ℤ) :
    ((decompose (DGAddCommGroup.grading (M := S)) x n : S) : M) =
      decompose (DGAddCommGroup.grading (M := M)) (x : M) n :=
  (coe_decompose_map_of_map_mem S.subtype.toLinearMap.toAddMonoidHom
    (fun hx => S.subtype.map_mem hx) x n).symm


-- @@ L181-181 verbatim
end DGSubmodule


-- @@ L183-183 verbatim
namespace DGModuleHom


-- @@ L185-185 expanded
variable {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N] (f : DGModuleHom A M N)


-- @@ L187-201 verbatim
/-- The kernel of a morphism of dg modules, as a dg submodule. -/
def ker : DGSubmodule A M where
  __ := LinearMap.ker f.toLinearMap
  d_mem' := fun {m} hm => by
    have hm' : f m = 0 := hm
    show f (d m) = 0
    rw [map_d, hm', d_zero]
  decompose_mem' := fun n {m} hm => by
    have hm' : f m = 0 := hm
    show f _ = 0
    refine (coe_decompose_map_of_map_mem f.toLinearMap.toAddMonoidHom
      (fun hx => f.map_mem hx) m n).symm.trans ?_
    change (decompose (grading (M := N)) (f m) n : N) = 0
    rw [hm', decompose_zero,
      DirectSum.zero_apply, ZeroMemClass.coe_zero]


-- @@ L203-205 verbatim
@[simp]
theorem mem_ker {m : M} : m ∈ f.ker ↔ f m = 0 :=
  Iff.rfl


-- @@ L207-216 verbatim
/-- The image of a morphism of dg modules, as a dg submodule. -/
def range : DGSubmodule A N where
  __ := LinearMap.range f.toLinearMap
  d_mem' := fun {x} hx => by
    obtain ⟨m, rfl⟩ : ∃ m, f m = x := hx
    exact ⟨d m, by simp⟩
  decompose_mem' := fun n {x} hx => by
    obtain ⟨m, rfl⟩ : ∃ m, f m = x := hx
    exact ⟨decompose (grading (M := M)) m n,
      (coe_decompose_map_of_map_mem f.toLinearMap.toAddMonoidHom (fun hx => f.map_mem hx) m n).symm⟩


-- @@ L218-220 verbatim
@[simp]
theorem mem_range {n : N} : n ∈ f.range ↔ ∃ m, f m = n :=
  Iff.rfl


-- @@ L222-223 verbatim
theorem apply_mem_range (m : M) : f m ∈ f.range :=
  ⟨m, rfl⟩


-- @@ L225-227 expanded
/-- A morphism of dg modules corestricted to its image. -/
def rangeRestrict : DGModuleHom A M f.range :=
  DGSubmodule.codRestrict f f.apply_mem_range


-- @@ L229-230 verbatim
@[simp]
theorem coe_rangeRestrict_apply (m : M) : (f.rangeRestrict m : N) = f m := rfl


-- @@ L232-232 verbatim
end DGModuleHom


-- @@ L234-234 verbatim
end DG
