import DG.Homotopy.HomotopyCategory
import DG.Homotopy.KProjective
import DG.Homotopy.Products


-- @@ L5-27 verbatim
/-!
# Coproducts in the homotopy category of dg modules

The homotopy category `DG.HomotopyCategory A` of dg modules over a dg ring `A` has arbitrary
coproducts, and the quotient functor `DG.DGModuleCat A ⥤ DG.HomotopyCategory A` preserves them:
the coproduct of a family `X j` is (the image of) the direct sum `⨁ j, X j` of dg modules. The
key point is `DG.Homotopic.of_directSum`: two morphisms out of a direct sum are homotopic as
soon as their restrictions to all summands are, since homotopies can be glued along the
summands (`DG.Cochain.directSumDesc`).

## Main definitions and results

* `DG.HomotopyCategory.coproductCofan X` and `DG.HomotopyCategory.isColimitCoproductCofan X`:
  the direct sum is a coproduct in the homotopy category.
* `DG.HomotopyCategory.hasCoproducts`: `HasCoproducts.{w} (HomotopyCategory.{max v w} A)`.
* `DG.HomotopyCategory.quotient_preservesColimitsOfShape_discrete`: the quotient functor
  preserves coproducts.

## Universes

As for `DG.DGModuleCat` (`DG/Homotopy/Products.lean`), coproducts indexed by `J : Type w` are
constructed in `HomotopyCategory.{max v w} A`.
-/


-- @@ L29-29 verbatim
open CategoryTheory Limits DirectSum


-- @@ L31-31 verbatim
universe w v u


-- @@ L33-33 verbatim
namespace DG


-- @@ L35-35 verbatim
section DirectSum


-- @@ L37-41 verbatim
variable {A : Type*} [Ring A] [DGAddCommGroup A] {ι : Type*} [DecidableEq ι]
  {P : ι → Type*} [∀ i, AddCommGroup (P i)] [∀ i, DGAddCommGroup (P i)]
  [∀ i, Module A (P i)]
  [∀ i, DGModule A (P i)] {N : Type*} [AddCommGroup N] [DGAddCommGroup N] [Module A N]
  [DGModule A N]


-- @@ L43-58 expanded
/-- Two morphisms out of a direct sum of dg modules are homotopic if their restrictions to all
summands are homotopic. -/
theorem Homotopic.of_directSum {f g : DGModuleHom A (⨁ i, P i) N}
    (h : ∀ i, Homotopic (f.comp (DGModuleHom.lof A P i)) (g.comp (DGModuleHom.lof A P i))) :
    Homotopic f g := by
  rw [Homotopic.iff_sub]
  choose c hc using fun i => homotopic_zero_iff_exists.mp (Homotopic.iff_sub.mp (h i))
  refine
    homotopic_zero_iff_exists.mpr ⟨Cochain.directSumDesc c, Cochain.directSum_ext fun i x => ?_⟩
  have h1 :=
    congrArg (fun z : Cochain A (P i) N 0 => z x)
      (δ_ofHom_comp (DGModuleHom.lof A P i) (Cochain.directSumDesc c) 0)
  have h2 :
    (Cochain.directSumDesc c).comp (Cochain.ofHom (DGModuleHom.lof A P i)) (zero_add _) = c i :=
    Cochain.ext fun y => Cochain.directSumDesc_of c i y
  simp only [Cochain.comp_apply, Cochain.ofHom_apply, DGModuleHom.lof_apply, h2] at h1
  rw [Cochain.ofHom_apply, ← h1, ← hc i]
  rfl


-- @@ L60-60 verbatim
end DirectSum


-- @@ L62-62 verbatim
namespace HomotopyCategory


-- @@ L64-64 verbatim
variable {A : Type u} [Ring A] [DGAddCommGroup A] [DGRing A]


-- @@ L66-66 verbatim
section


-- @@ L68-68 verbatim
variable {J : Type w} [DecidableEq J] (X : J → HomotopyCategory.{max v w} A)


-- @@ L70-75 verbatim
/-- The direct sum of (representatives of) a family of objects of the homotopy category, as a
cofan. -/
noncomputable def coproductCofan : Cofan X :=
  Cofan.mk ((quotient A).obj (DGModuleCat.of A (⨁ j, ((X j).as : Type (max v w)))))
    fun j => (quotient A).map (DGModuleCat.ofHom
      (DGModuleHom.lof A (fun j => ((X j).as : Type (max v w))) j))


-- @@ L77-81 verbatim
omit [DGRing A] in
@[simp]
theorem coproductCofan_inj (j : J) :
    (coproductCofan X).inj j = (quotient A).map (DGModuleCat.ofHom
      (DGModuleHom.lof A (fun j => ((X j).as : Type (max v w))) j)) := rfl


-- @@ L83-99 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The direct sum is a coproduct in the homotopy category. -/
noncomputable def isColimitCoproductCofan : IsColimit (coproductCofan X) :=
  Cofan.IsColimit.mk _
    (fun t => (quotient A).map (DGModuleCat.ofHom
      (DGModuleHom.toModule fun j => (Quot.out (t.inj j)).hom)))
    (fun t j => by
      rw [coproductCofan_inj, ← Functor.map_comp, ← DGModuleCat.ofHom_comp,
        DGModuleHom.toModule_comp_lof, DGModuleCat.ofHom_hom, quotient_map_out])
    (fun t m hm => by
      obtain ⟨m, rfl⟩ := (quotient A).map_surjective m
      refine (quotient_map_eq_iff _ _).mpr (Homotopic.of_directSum fun j => ?_)
      have := hm j
      rw [coproductCofan_inj, ← Functor.map_comp, ← quotient_map_out (t.inj j),
        quotient_map_eq_iff] at this
      refine this.trans ?_
      rw [DGModuleCat.hom_ofHom, DGModuleHom.toModule_comp_lof])


-- @@ L101-101 verbatim
instance : HasCoproduct X := ⟨⟨_, isColimitCoproductCofan X⟩⟩


-- @@ L103-103 verbatim
variable (F : J → DGModuleCat.{max v w} A)


-- @@ L105-110 verbatim
/-- The quotient functor sends the direct sum of dg modules to a coproduct. -/
instance quotient_preservesColimit_discreteFunctor :
    PreservesColimit (Discrete.functor F) (quotient A) :=
  preservesColimit_of_preserves_colimit_cocone (DGModuleCat.coproductCoconeIsColimit F)
    ((isColimitMapCoconeCofanMkEquiv _ _ _).symm
      (isColimitCoproductCofan fun j => (quotient A).obj (F j)))


-- @@ L112-112 verbatim
end


-- @@ L114-114 verbatim
variable (A)


-- @@ L116-120 verbatim
/-- The homotopy category of dg modules has arbitrary coproducts. -/
instance hasCoproducts : HasCoproducts.{w} (HomotopyCategory.{max v w} A) := fun J =>
  { has_colimit := fun K => by
      let := Classical.decEq J
      exact hasColimit_of_iso (Discrete.natIsoFunctor (F := K)) }


-- @@ L122-123 verbatim
instance hasCoproducts' : HasCoproducts.{v} (HomotopyCategory.{v} A) :=
  hasCoproducts.{v, v} A


-- @@ L125-130 verbatim
/-- The quotient functor from dg modules to the homotopy category preserves coproducts. -/
instance quotient_preservesColimitsOfShape_discrete (J : Type w) :
    PreservesColimitsOfShape (Discrete J) (quotient.{max v w} A) where
  preservesColimit {K} := by
    let := Classical.decEq J
    exact preservesColimit_of_iso_diagram (quotient A) (Discrete.natIsoFunctor (F := K)).symm


-- @@ L132-132 verbatim
end HomotopyCategory


-- @@ L134-134 verbatim
end DG
