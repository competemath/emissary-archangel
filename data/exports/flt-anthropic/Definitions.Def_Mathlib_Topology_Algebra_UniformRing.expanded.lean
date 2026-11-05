import Mathlib
import Definitions.Def_Mathlib_Algebra_Algebra_Hom


-- @@ L4-4 verbatim
section


-- @@ L6-6 verbatim
namespace UniformSpace.Completion


-- @@ L8-10 verbatim
variable {α : Type*} [Ring α] [UniformSpace α] [IsTopologicalRing α] [IsUniformAddGroup α]
  {β : Type*} [UniformSpace β] [Ring β] [IsUniformAddGroup β] [IsTopologicalRing β]
  (f : α →+* β) (hf : Continuous f)


-- @@ L12-12 verbatim
variable {f}


-- @@ L14-24 expanded
noncomputable def mapSemialgHom {α : Type*} [CommRing α] [UniformSpace α] [IsTopologicalRing α]
    [IsUniformAddGroup α] {β : Type*} [UniformSpace β] [CommRing β] [IsUniformAddGroup β]
    [IsTopologicalRing β] (f : α →+* β) (hf : Continuous f) :
    SemialgHom f (Completion α) (Completion β)
    where
  __ := UniformSpace.Completion.mapRingHom f hf
  map_smul' m
    x :=
    by
    simp only [RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe,
      MonoidHom.coe_coe]
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    congr
    exact extensionHom_coe _ _ m


-- @@ L26-30 verbatim
theorem mapSemialgHom_apply {α : Type*} [CommRing α] [UniformSpace α]
    [IsTopologicalRing α] [IsUniformAddGroup α] {β : Type*} [UniformSpace β] [CommRing β]
    [IsUniformAddGroup β] [IsTopologicalRing β] (f : α →+* β) (hf : Continuous f)
    (x : UniformSpace.Completion α) :
    mapSemialgHom f hf x = UniformSpace.Completion.map f x := rfl


-- @@ L32-37 verbatim
theorem mapSemialgHom_coe {α : Type*} [CommRing α] [UniformSpace α]
    [IsTopologicalRing α] [IsUniformAddGroup α] {β : Type*} [UniformSpace β] [CommRing β]
    [IsUniformAddGroup β] [IsTopologicalRing β] {f : α →+* β} (hf : UniformContinuous f)
    (a : α) :
    mapSemialgHom f hf.continuous a = f a := by
  rw [mapSemialgHom_apply, map_coe hf]


-- @@ L39-39 verbatim
end UniformSpace.Completion
