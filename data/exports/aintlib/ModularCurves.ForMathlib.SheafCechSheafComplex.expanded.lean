import ModularCurves.ForMathlib.SheafCechSheafDifferential


-- @@ L3-10 verbatim
/-!
# The sheaf-level Cech complex

This file packages the sheaf-level Cech terms and differentials as the native Cech complex
associated to the presheaf of restriction-pushforward factors. In particular, the relation
that two consecutive differentials compose to zero follows from the native cosimplicial
construction.
-/


-- @@ L12-12 verbatim
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite


-- @@ L14-14 verbatim
universe u


-- @@ L16-16 verbatim
namespace TopCat.Sheaf


-- @@ L18-18 verbatim
variable {X : TopCat.{u}}

-- @@ L19-19 verbatim
variable (F : Sheaf AddCommGrpCat.{u} X)


-- @@ L21-41 verbatim
/-- The presheaf on opens whose value at `A` is the pushforward of the restriction of `F`
to `A`. -/
noncomputable def cechFactorPresheaf :
    (Opens X)ᵒᵖ ⥤ Sheaf AddCommGrpCat.{u} X where
  obj A := (restrict AddCommGrpCat A.unop.isOpenEmbedding ⋙
    pushforward AddCommGrpCat A.unop.inclusion').obj F
  map f := cechTermFactorRestriction F (leOfHom f.unop)
  map_id A := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change F.obj.map _ = 𝟙 _
    rw [← F.obj.map_id]
    exact congrArg F.obj.map (Subsingleton.elim _ _)
  map_comp f g := by
    apply CategoryTheory.Sheaf.hom_ext
    apply NatTrans.ext
    funext V
    change F.obj.map _ = F.obj.map _ ≫ F.obj.map _
    rw [← F.obj.map_comp]
    exact congrArg F.obj.map (Subsingleton.elim _ _)


-- @@ L43-43 verbatim
variable {ι : Type u} (U : ι → Opens X)


-- @@ L45-47 verbatim
/-- The sheaf-level Cech complex associated to the open family `U`. -/
noncomputable def cechComplex : CochainComplex (Sheaf AddCommGrpCat.{u} X) ℕ :=
  (cechComplexFunctor U).obj (cechFactorPresheaf F)


-- @@ L49-50 verbatim
/-- The degree-`n` object of the sheaf-level Cech complex is `cechTerm F U n`. -/
theorem cechComplex_X (n : ℕ) : (cechComplex F U).X n = cechTerm F U n := rfl


-- @@ L52-59 verbatim
private theorem nativeCoface_eq_cechCoface (n : ℕ) (k : Fin (n + 2)) :
    ((FormalCoproduct.cosimplicialObjectFunctor
      (FormalCoproduct.mk _ U).cech).obj (cechFactorPresheaf F)).δ k =
      cechCoface F U n k := by
  rw [CosimplicialObject.δ,
    FormalCoproduct.cosimplicialObjectFunctor_obj_map,
    FormalCoproduct.cech_map]
  rfl


-- @@ L61-73 verbatim
/-- The native differential of `cechComplex F U` is the alternating-sum map
`cechDifferential F U n`. -/
theorem cechComplex_d (n : ℕ) :
    (cechComplex F U).d n (n + 1) = cechDifferential F U n := by
  change ((FormalCoproduct.cochainComplexFunctor
    (FormalCoproduct.mk _ U).cech).obj (cechFactorPresheaf F)).d n (n + 1) = _
  rw [FormalCoproduct.cochainComplexFunctor_obj_d]
  refine (CochainComplex.of_d _ _ n).trans ?_
  rw [AlgebraicTopology.AlternatingCofaceMapComplex.objD, cechDifferential]
  apply Finset.sum_congr rfl
  intro k _
  exact congrArg (fun f => (-1 : ℤ) ^ (k : ℕ) • f)
    (nativeCoface_eq_cechCoface F U n k)


-- @@ L75-79 verbatim
/-- Consecutive sheaf-level Cech differentials compose to zero. -/
theorem cechDifferential_comp (n : ℕ) :
    cechDifferential F U n ≫ cechDifferential F U (n + 1) = 0 := by
  rw [← cechComplex_d F U n, ← cechComplex_d F U (n + 1)]
  exact (cechComplex F U).d_comp_d n (n + 1) (n + 2)


-- @@ L81-81 verbatim
end TopCat.Sheaf
