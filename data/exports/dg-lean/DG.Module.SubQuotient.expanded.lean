import DG.Module.Sub
import DG.Module.Quotient
import Mathlib.LinearAlgebra.Quotient.Basic


-- @@ L5-13 verbatim
/-!
# Quotients of dg modules by dg submodules

For a dg submodule `S` of a dg `A`-module `M`, the quotient module `M ⧸ S.toSubmodule` is a dg
`A`-module: its homogeneous components are the images of those of `M` and its differential is
induced by `d` (`DG.DGAddCommGroup.quotient`, since `S` is a dg subgroup). The quotient map
`DG.DGSubmodule.mkQ S : M →ᵈᵍ[A] M ⧸ S.toSubmodule` is a morphism of dg modules, and a morphism
of dg modules vanishing on `S` factors through it (`DG.DGSubmodule.liftQ`).
-/


-- @@ L15-15 verbatim
namespace DG


-- @@ L17-18 verbatim
variable {A : Type*} {M : Type*} [Ring A] [DGAddCommGroup A] [AddCommGroup M]
  [DGAddCommGroup M] [Module A M]


-- @@ L20-20 verbatim
namespace DGSubmodule


-- @@ L22-22 verbatim
variable (S : DGSubmodule A M)


-- @@ L24-27 verbatim
/-- A dg submodule is a dg subgroup. -/
instance isDGAddSubgroup : IsDGAddSubgroup S.toSubmodule.toAddSubgroup where
  decompose_mem hx n := S.decompose_mem n hx
  d_mem hx := S.d_mem hx


-- @@ L29-32 verbatim
/-- The quotient of a dg module by a dg submodule is a dg abelian group, with
`(M ⧸ S)ⁿ` the image of `Mⁿ` and the induced differential. -/
noncomputable instance quotientDGAddCommGroup : DGAddCommGroup (M ⧸ S.toSubmodule) :=
  DGAddCommGroup.quotient S.toSubmodule.toAddSubgroup


-- @@ L34-37 verbatim
theorem mem_grading_quotient_iff {n : ℤ} {y : M ⧸ S.toSubmodule} :
    y ∈ DGAddCommGroup.grading n ↔
      ∃ x ∈ DGAddCommGroup.grading (M := M) n, Submodule.Quotient.mk x = y :=
  Iff.rfl


-- @@ L39-41 verbatim
theorem mk_mem_grading {n : ℤ} {x : M} (hx : x ∈ DGAddCommGroup.grading n) :
    (Submodule.Quotient.mk x : M ⧸ S.toSubmodule) ∈ DGAddCommGroup.grading n :=
  ⟨x, hx, rfl⟩


-- @@ L43-47 verbatim
@[simp]
theorem d_mk (x : M) :
    DGAddCommGroup.d (Submodule.Quotient.mk x : M ⧸ S.toSubmodule) =
      Submodule.Quotient.mk (DGAddCommGroup.d x) :=
  rfl


-- @@ L49-49 verbatim
variable [DGModule A M]


-- @@ L51-61 verbatim
/-- The quotient of a dg module by a dg submodule is a dg module. -/
instance quotientDGModule : DGModule A (M ⧸ S.toSubmodule) where
  smul_mem _ _ a _ ha hy := by
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨a • x, smul_mem_grading ha hx, rfl⟩
  d_smul' {n a} ha y := by
    induction y using Submodule.Quotient.induction_on with
    | H x =>
      rw [← Submodule.Quotient.mk_smul, d_mk, d_smul ha, d_mk, Submodule.Quotient.mk_add,
        Units.smul_def, Units.smul_def, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_smul,
        Submodule.Quotient.mk_smul]


-- @@ L63-63 verbatim
omit [DGModule A M]


-- @@ L65-69 expanded
/-- The quotient map `M → M ⧸ S` as a morphism of dg modules. -/
def mkQ : DGModuleHom A M (M ⧸ S.toSubmodule)
    where
  __ := S.toSubmodule.mkQ
  map_mem' hx := S.mk_mem_grading hx
  map_d' _ := rfl


-- @@ L71-72 verbatim
@[simp]
theorem mkQ_apply (x : M) : S.mkQ x = Submodule.Quotient.mk x := rfl


-- @@ L74-75 verbatim
theorem mkQ_surjective : Function.Surjective S.mkQ :=
  Submodule.mkQ_surjective _


-- @@ L77-78 verbatim
theorem mkQ_eq_zero_iff {x : M} : S.mkQ x = 0 ↔ x ∈ S :=
  Submodule.Quotient.mk_eq_zero _


-- @@ L80-82 verbatim
@[simp]
theorem ker_mkQ : S.mkQ.ker = S :=
  ext fun _ => S.mkQ_eq_zero_iff


-- @@ L84-84 verbatim
variable {S} {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N]


-- @@ L86-94 expanded
/-- A morphism of dg modules vanishing on `S` factors through the quotient `M ⧸ S`. -/
def liftQ (f : DGModuleHom A M N) (h : ∀ x ∈ S, f x = 0) : DGModuleHom A (M ⧸ S.toSubmodule) N
    where
  __ := S.toSubmodule.liftQ f.toLinearMap fun x hx => h x hx
  map_mem' := by
    rintro n _ ⟨x, hx, rfl⟩
    exact f.map_mem hx
  map_d'
    y := by
    induction y using Submodule.Quotient.induction_on with
    | H x => exact f.map_d x


-- @@ L96-98 expanded
@[simp]
theorem liftQ_mk (f : DGModuleHom A M N) (h : ∀ x ∈ S, f x = 0) (x : M) :
    liftQ f h (Submodule.Quotient.mk x) = f x :=
  rfl


-- @@ L100-102 expanded
@[simp]
theorem liftQ_mkQ (f : DGModuleHom A M N) (h : ∀ x ∈ S, f x = 0) (x : M) :
    liftQ f h (S.mkQ x) = f x :=
  rfl


-- @@ L104-106 expanded
@[simp]
theorem liftQ_comp_mkQ (f : DGModuleHom A M N) (h : ∀ x ∈ S, f x = 0) :
    (liftQ f h).comp S.mkQ = f :=
  rfl


-- @@ L108-113 expanded
/-- Two morphisms out of `M ⧸ S` agreeing after composition with the quotient map are equal. -/
theorem quotient_ext {f g : DGModuleHom A (M ⧸ S.toSubmodule) N} (h : f.comp S.mkQ = g.comp S.mkQ) :
    f = g :=
  DGModuleHom.ext fun y => by
    obtain ⟨x, rfl⟩ := S.mkQ_surjective y
    exact congrArg (fun φ : DGModuleHom A M N => φ x) h


-- @@ L115-115 verbatim
end DGSubmodule


-- @@ L117-117 verbatim
end DG
