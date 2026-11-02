import DG.Algebra.Constructions
import DG.Homotopy.Homotopy
import DG.Module.HomLinear


-- @@ L5-24 verbatim
/-!
# The endomorphism dg algebra of a cochain complex

A cochain complex `C` of `R`-modules is a dg module over `R` concentrated in degree `0`
(`DG.DGAlgebra.degreeZero R`); conversely a dg abelian group with a compatible `R`-module
structure is such a dg module (`DG.DGModule.ofGround`). Its endomorphism complex
`END_R(C) = DG.DGModule.END R C` is then a dg `R`-algebra (`DG.DGModule.END.instDGAlgebra`),
with product `f * g = (-1)^{|f||g|} g ∘ f`.

For any dg ring `A` and dg `A`-module `M`, in particular for `END_R(C)`:

* `DG.DGModule.END.cocyclesZeroAddEquiv`: the degree-`0` cocycles of `END_A(M)` are the
  morphisms of dg modules `M → M` (chain maps, when `A = R`), with `1 ↦ id`
  (`cocyclesZeroAddEquiv_id`) and composition corresponding to the (opposite) product
  (`cocyclesZeroAddEquiv_comp`);
* `DG.DGModule.END.cohomologyZeroAddEquiv`: `H⁰(END_A(M))` is the group of morphisms modulo
  null-homotopic ones (chain maps up to homotopy).

The ring `R` is given its degree-`0` dg structure through local instances in this file.
-/


-- @@ L26-26 verbatim
open DirectSum


-- @@ L28-28 verbatim
namespace DG


-- @@ L30-30 verbatim
namespace DGModule.END


-- @@ L32-33 verbatim
variable {A M : Type*} [Ring A] [DGAddCommGroup A] [AddCommGroup M] [DGAddCommGroup M]
  [Module A M] [DGModule A M]


-- @@ L35-38 expanded
variable (A M) in
/-- The degree-`0` cocycles of `END_A(M)` are the endomorphisms of the dg module `M`. -/
noncomputable def cocyclesZeroAddEquiv : (DGModuleHom A M M) ≃+ cocycles (END A M) 0 :=
  (Cocycle.equivHom A M M).trans (HOM.cocyclesAddEquiv A M M 0)


-- @@ L40-43 expanded
theorem coe_cocyclesZeroAddEquiv (f : DGModuleHom A M M) :
    (cocyclesZeroAddEquiv A M f : END A M) =
      DirectSum.of (fun n => Cochain A M M n) 0 (Cochain.ofHom f) :=
  rfl


-- @@ L45-47 verbatim
theorem cocyclesZeroAddEquiv_id :
    (cocyclesZeroAddEquiv A M DGModuleHom.id : END A M) = 1 :=
  rfl


-- @@ L49-57 expanded
/-- Composition of endomorphisms is the opposite of the product of `END_A(M)` (which is
`f * g = g ∘ f` in degree `0`). -/
theorem cocyclesZeroAddEquiv_comp (f g : DGModuleHom A M M) :
    (cocyclesZeroAddEquiv A M (g.comp f) : END A M) =
      cocyclesZeroAddEquiv A M f * cocyclesZeroAddEquiv A M g :=
  by
  rw [coe_cocyclesZeroAddEquiv, coe_cocyclesZeroAddEquiv, coe_cocyclesZeroAddEquiv, of_mul_of]
  exact
    HOM.of_congr (add_zero 0).symm fun x =>
      by
      rw [Cochain.units_smul_apply, mul_zero, koszulSign_zero, one_smul]
      rfl


-- @@ L59-64 expanded
variable (A M) in
/-- `H⁰(END_A(M))` is the group of endomorphisms of the dg module `M` modulo the
null-homotopic ones. -/
noncomputable def cohomologyZeroAddEquiv :
    ((DGModuleHom A M M) ⧸ nullHomotopic A M M) ≃+ cohomology (END A M) 0 :=
  quotientNullHomotopicAddEquivCohomology A M M


-- @@ L66-69 expanded
theorem cohomologyZeroAddEquiv_mk (f : DGModuleHom A M M) :
    cohomologyZeroAddEquiv A M (QuotientAddGroup.mk f) =
      cohomology.mk _ 0 (cocyclesZeroAddEquiv A M f) :=
  quotientNullHomotopicAddEquivCohomology_mk f


-- @@ L71-78 expanded
/-- Two endomorphisms of `M` have the same class in `H⁰(END_A(M))` if and only if they are
homotopic. -/
theorem cohomology_mk_eq_iff (f g : DGModuleHom A M M) :
    cohomology.mk _ 0 (cocyclesZeroAddEquiv A M f) =
        cohomology.mk _ 0 (cocyclesZeroAddEquiv A M g) ↔
      Homotopic f g :=
  by
  rw [← cohomologyZeroAddEquiv_mk, ← cohomologyZeroAddEquiv_mk,
    (cohomologyZeroAddEquiv A M).injective.eq_iff, QuotientAddGroup.eq_iff_sub_mem,
    homotopic_iff_sub_mem, ← neg_mem_iff, neg_sub]


-- @@ L80-80 verbatim
end DGModule.END


-- @@ L82-82 verbatim
/-! ### Cochain complexes of `R`-modules -/


-- @@ L84-84 verbatim
section Ground


-- @@ L86-86 verbatim
variable (R : Type*) [CommRing R]


-- @@ L88-89 verbatim
/-- `R` concentrated in degree `0` (local instance). -/
local instance instDGAddCommGroupGround : DGAddCommGroup R := DGAddCommGroup.degreeZero R


-- @@ L91-92 verbatim
/-- `R` concentrated in degree `0`, as a dg ring (local instance). -/
local instance instDGRingGround : DGRing R := DGRing.degreeZero R


-- @@ L94-95 verbatim
/-- `R` concentrated in degree `0`, as a dg `R`-algebra (local instance). -/
local instance instDGAlgebraGround : DGAlgebra R R := DGAlgebra.degreeZero R


-- @@ L97-97 verbatim
variable {R} (C : Type*) [AddCommGroup C] [DGAddCommGroup C] [Module R C]


-- @@ L99-113 verbatim
/-- A dg abelian group with an `R`-module structure for which the graded pieces are
`R`-submodules and the differential is `R`-linear (a cochain complex of `R`-modules) is a dg
module over `R` concentrated in degree `0`. -/
theorem DGModule.ofGround
    (hmem : ∀ (r : R) {n : ℤ} {c : C}, c ∈ grading n → r • c ∈ grading n)
    (hd : ∀ (r : R) (c : C), d (r • c) = r • d c) : DGModule R C where
  smul_mem i j r c hr hc := by
    rcases (mem_degreeZeroGrading_iff R).mp hr with rfl | rfl
    · simpa using hmem r hc
    · simp
  d_smul' {n r} hr c := by
    change d (r • c) = (0 : R →+ R) r • c + koszulSign n • (r • d c)
    rcases (mem_degreeZeroGrading_iff R).mp hr with rfl | rfl
    · simp [hd]
    · simp


-- @@ L115-115 verbatim
variable [DGModule R C]


-- @@ L117-119 verbatim
/-- The endomorphism complex `END_R(C)` of a cochain complex of `R`-modules is a dg
`R`-algebra. -/
example : DGAlgebra R (DGModule.END R C) := inferInstance


-- @@ L121-124 verbatim
theorem DGModule.END.algebraMap_ground_apply (r : R) :
    algebraMap R (DGModule.END R C) r =
      DirectSum.of (fun n => Cochain R C C n) 0 (r • Cochain.id R C) :=
  rfl


-- @@ L126-126 verbatim
end Ground


-- @@ L128-128 verbatim
end DG
