import DG.Module.Corner


-- @@ L3-12 verbatim
/-!
# Universe lifts of dg abelian groups and dg modules

For a dg abelian group `A`, the universe lift `ULift A` carries the grading and differential of
`A` (`DG.ULift.instDGAddCommGroup`); for a dg module `M` over a dg ring `A`, `ULift M` is a dg
`A`-module (`DG.ULift.instDGModule`), and `ULift.up`, `ULift.down` are isomorphisms of dg modules
(`DG.ULift.upHom`, `DG.ULift.downHom`). Universe lifts are used to test K-projectivity and
lifting properties, which are stated for test modules in a single universe, against modules in a
smaller universe.
-/


-- @@ L14-14 verbatim
universe w' w u


-- @@ L16-16 verbatim
namespace DG


-- @@ L18-18 verbatim
section ULift


-- @@ L20-20 verbatim
variable (A : Type w) [AddCommGroup A] [DGAddCommGroup A]


-- @@ L22-26 verbatim
/-- `ULift.down`, as an additive map. -/
def ULift.downAddHom : ULift.{w'} A →+ A where
  toFun := ULift.down
  map_zero' := rfl
  map_add' _ _ := rfl


-- @@ L28-32 verbatim
/-- `ULift.up`, as an additive map. -/
def ULift.upAddHom : A →+ ULift.{w'} A where
  toFun := ULift.up
  map_zero' := rfl
  map_add' _ _ := rfl


-- @@ L34-38 verbatim
/-- The dg abelian group `ULift A`, with the grading and differential of `A`. -/
noncomputable instance ULift.instDGAddCommGroup : DGAddCommGroup (ULift.{w'} A) :=
  DGAddCommGroup.ofInjective (ULift.downAddHom A) (fun _ _ h => ULift.ext _ _ h)
    ((ULift.upAddHom A).comp ((d : A →+ A).comp (ULift.downAddHom A))) (fun _ => rfl)
    fun _ _ => ⟨ULift.up _, rfl⟩


-- @@ L40-40 verbatim
variable {A}


-- @@ L42-43 verbatim
theorem ULift.mem_grading_iff {n : ℤ} {a : ULift.{w'} A} : a ∈ grading n ↔ a.down ∈ grading n :=
  Iff.rfl


-- @@ L45-46 verbatim
@[simp]
theorem ULift.d_down (a : ULift.{w'} A) : (d a).down = d a.down := rfl


-- @@ L48-49 verbatim
@[simp]
theorem ULift.d_up (a : A) : d (ULift.up.{w'} a) = ULift.up (d a) := rfl


-- @@ L51-51 verbatim
end ULift


-- @@ L53-53 verbatim
section Module


-- @@ L55-56 verbatim
variable {A : Type u} [Ring A] [DGAddCommGroup A] (M : Type w) [AddCommGroup M]
  [DGAddCommGroup M] [Module A M] [DGModule A M]


-- @@ L58-61 verbatim
/-- The universe lift of a dg module is a dg module. -/
instance ULift.instDGModule : DGModule A (ULift.{w'} M) where
  smul_mem _ _ _ _ ha hx := smul_mem_grading (M := M) ha (ULift.mem_grading_iff.mp hx)
  d_smul' ha x := ULift.ext _ _ (d_smul ha x.down)


-- @@ L63-69 expanded
/-- `ULift.up`, as a morphism of dg modules. -/
def ULift.upHom : DGModuleHom A M (ULift.{w'} M)
    where
  toFun := ULift.up
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mem' h := h
  map_d' _ := rfl


-- @@ L71-77 expanded
/-- `ULift.down`, as a morphism of dg modules. -/
def ULift.downHom : DGModuleHom A (ULift.{w'} M) M
    where
  toFun := ULift.down
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_mem' h := h
  map_d' _ := rfl


-- @@ L79-83 expanded
omit [DGModule A M] in
@[simp]
theorem ULift.downHom_comp_upHom :
    (ULift.downHom.{w'} M).comp (ULift.upHom.{w'} M) = (DGModuleHom.id : DGModuleHom A M M) :=
  rfl


-- @@ L85-85 verbatim
end Module


-- @@ L87-87 verbatim
end DG
