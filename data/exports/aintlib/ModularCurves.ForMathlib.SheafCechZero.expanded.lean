import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
import Mathlib.Topology.Sheaves.SheafCondition.EqualizerProducts


-- @@ L5-10 verbatim
/-!
# Degree-zero exactness of the Cech complex

For a sheaf valued in an abelian category, the restriction map from sections on the
union of a family of opens is the kernel of the first Cech restriction-difference map.
-/


-- @@ L12-12 verbatim
open CategoryTheory CategoryTheory.Limits TopologicalSpace


-- @@ L14-14 verbatim
universe w v u


-- @@ L16-16 verbatim
namespace TopCat.Sheaf


-- @@ L18-18 verbatim
open Presheaf.SheafConditionEqualizerProducts


-- @@ L20-20 verbatim
variable {C : Type u} [Category.{v} C] [Abelian C] [HasProducts C]

-- @@ L21-21 verbatim
variable {X : TopCat.{w}} {ι : Type w} (F : X.Sheaf C) (U : ι → Opens X)


-- @@ L23-27 verbatim
/-- The equalizer fork from the sheaf condition, viewed as the kernel of the first
Cech restriction-difference map. -/
noncomputable def cechResSubKernelFork :
    KernelFork (leftRes F.presheaf U - rightRes F.presheaf U) :=
  Preadditive.kernelForkOfFork (fork F.presheaf U)


-- @@ L29-32 verbatim
/-- Sections on the union of the opens are the kernel of the first Cech differential. -/
noncomputable def isLimitCechResSub : IsLimit (cechResSubKernelFork F U) :=
  Preadditive.isLimitKernelForkOfFork
    ((F.presheaf.isSheaf_iff_isSheafEqualizerProducts.mp F.2 U).some)


-- @@ L34-37 verbatim
/-- The augmentation and first restriction-difference map of the Cech complex. -/
noncomputable def cechZeroShortComplex : ShortComplex C :=
  ShortComplex.mk (res F.presheaf U) (leftRes F.presheaf U - rightRes F.presheaf U)
    (by rw [Preadditive.comp_sub, w, sub_self])


-- @@ L39-43 verbatim
/-- The Cech complex of a sheaf is exact at degree zero. -/
theorem cechZeroShortComplex_exact : (cechZeroShortComplex F U).Exact := by
  apply ShortComplex.exact_of_f_is_kernel
  refine IsLimit.ofIsoLimit (isLimitCechResSub F U) ?_
  apply Fork.ext (Iso.refl _)


-- @@ L45-45 verbatim
end TopCat.Sheaf
