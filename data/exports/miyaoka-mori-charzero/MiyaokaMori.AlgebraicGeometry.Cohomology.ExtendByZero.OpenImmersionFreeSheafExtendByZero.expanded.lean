import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.ExtZeroSections
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyTopIso
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.Stacks02uv
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.OpenImmersionSheafPullbackExact


-- @@ L7-32 verbatim
/-! # `j_! ℤ_Y ≅ ℤ[h_Y]^#` and `Ext` along an exact adjunction

**`j_! ℤ_Y ≅ ℤ[h_Y]^#`, and `Ext` along an exact adjunction, linearly** (Stacks 01E1, 03F3).

For an open `Y ⊆ X` of a scheme write `G := Y.ι.opensFunctor`, `j^* := G.sheafPushforwardContinuous`
(restriction of abelian sheaves to `Y`; on `M.toAddCommGrpSheaf` it is *definitionally*
`(M.restrict Y.ι).toAddCommGrpSheaf`) and `j_! := G.sheafPullback` (extension by zero, its left
adjoint; exact by `OpenImmersionSheafPullbackExact.lean`). `j^*` also has a right adjoint
(`sheafAdjunctionCocontinuous`, `G` is cocontinuous), so it preserves colimits.

1. `freeSheafIsoExtendConstant : ℤ[h_Y]^# ≅ j_! ℤ_Y`. Both objects corepresent the functor
   `F ↦ F(Y)` on abelian sheaves on `X`: `Hom(ℤ[h_Y]^#, F) ≃ F(Y)` is `Stacks09sxAux.sectionsEquiv`
   (natural in `F`: evaluation at the canonical generator), and
   `Hom(j_! ℤ_Y, F) ≃ Hom(ℤ_Y, j^* F) ≃ Hom(ℤ[h_⊤]^#, j^* F) ≃ (j^* F)(⊤) = F(Y.ι ''ᵁ ⊤) = F(Y)`
   (adjunction, `freeSheafTerminalIsoConstantSheaf` on `Y`, `sectionsEquiv` on `Y`; all natural
   in `F`). Corepresenting objects are unique up to isomorphism
   (`Functor.CorepresentableBy.uniqueUpToIso`).
2. `Adjunction.extLinearEquivOfIsoLeft`: for an adjunction `L ⊣ R` of exact functors between abelian
   categories, an iso `e : A ≅ L.obj B`, and compatible actions of a commutative ring `S` on `F` (by
   `μ s : F ⟶ F`) and on `R.obj F` (by `μ' s`, with `R.map (μ s) = μ' s`), the additive equivalence
   `Ext A F n ≃+ Ext (L.obj B) F n ≃+ Ext B (R.obj F) n` (`extAddEquivOfIsoLeft`, `adj.extAddEquiv`)
   is `S`-linear for the module structures `s • x = x ∘ mk₀ (μ s)`; this is the naturality of both
   equivalences in the second variable (`extAddEquivOfIsoLeft_naturality`, `extAddEquiv_naturality`).

Source: Stacks 01E1 (cohomology of an open), 03F3 (`j_! ⊣ j^{-1}`); Mathlib
`Sites/SheafCohomology/Basic.lean` TODO. -/


-- @@ L34-34 verbatim
set_option autoImplicit false

-- @@ L35-35 verbatim
set_option maxHeartbeats 400000


-- @@ L37-37 verbatim
universe u


-- @@ L39-39 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L40-40 verbatim
open scoped AlgebraicGeometry


-- @@ L42-42 verbatim
noncomputable section


-- @@ L44-44 verbatim
namespace CategoryTheory.Adjunction


-- @@ L46-46 verbatim
open CategoryTheory.Abelian CategoryTheory.Abelian.Ext


-- @@ L48-69 verbatim
/-- **`Ext` along an exact adjunction, linearly.** For `adj : L ⊣ R` with `L` and `R` exact,
`e : A ≅ L.obj B`, and endomorphism actions `μ` of `S` on `F` and `μ'` on `R.obj F` with
`R.map (μ s) = μ' s`, the composite `Ext A F n ≃+ Ext (L.obj B) F n ≃+ Ext B (R.obj F) n` is
`S`-linear for module structures `m₁`, `m₂` whose scalar multiplications are `x ↦ x ∘ mk₀ (μ s)`,
`y ↦ y ∘ mk₀ (μ' s)`. -/
def extLinearEquivOfIsoLeft {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasExt C] [HasExt D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    [PreservesFiniteLimits L] [PreservesFiniteColimits R]
    {A : D} {B : C} (e : A ≅ L.obj B) (F : D) (n : ℕ) {S : Type*} [CommRing S]
    (m₁ : Module S (Ext A F n)) (m₂ : Module S (Ext B (R.obj F) n))
    (μ : S → (F ⟶ F)) (μ' : S → (R.obj F ⟶ R.obj F))
    (h₁ : ∀ (s : S) (x : Ext A F n), (letI := m₁; s • x) = x.comp (mk₀ (μ s)) (add_zero n))
    (h₂ : ∀ (s : S) (y : Ext B (R.obj F) n),
      (letI := m₂; s • y) = y.comp (mk₀ (μ' s)) (add_zero n))
    (hμ : ∀ s, R.map (μ s) = μ' s) :
    letI := m₁; letI := m₂; Ext A F n ≃ₗ[S] Ext B (R.obj F) n :=
  letI := m₁; letI := m₂
  { (extAddEquivOfIsoLeft e F n).trans (adj.extAddEquiv B F n) with
    map_smul' := fun s x => by
      show adj.extAddEquiv B F n (extAddEquivOfIsoLeft e F n (s • x)) =
        s • adj.extAddEquiv B F n (extAddEquivOfIsoLeft e F n x)
      rw [h₁, h₂, extAddEquivOfIsoLeft_naturality, extAddEquiv_naturality, hμ] }


-- @@ L71-71 verbatim
end CategoryTheory.Adjunction


-- @@ L73-73 verbatim
namespace AlgebraicGeometry.Scheme.Opens


-- @@ L75-75 verbatim
open CategoryTheory.Abelian Stacks09sxAux


-- @@ L77-77 verbatim
variable {X : AlgebraicGeometry.Scheme.{u}} (Y : X.Opens)


-- @@ L79-85 verbatim
/-- `j^*`: restriction of abelian sheaves from `X` to the open `Y` (composition with
`Y.ι.opensFunctor.op`). On `M.toAddCommGrpSheaf` it is definitionally
`(M.restrict Y.ι).toAddCommGrpSheaf`. -/
abbrev restrictAb :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology (Y : AlgebraicGeometry.Scheme.{u})) AddCommGrpCat.{u} :=
  Y.ι.opensFunctor.sheafPushforwardContinuous AddCommGrpCat.{u} _ _


-- @@ L87-92 verbatim
/-- `j_!`: extension by zero of abelian sheaves from the open `Y` to `X` (Mathlib's
`sheafPullback`, the left adjoint of `restrictAb`). -/
abbrev extendAb :
    Sheaf (Opens.grothendieckTopology (Y : AlgebraicGeometry.Scheme.{u})) AddCommGrpCat.{u} ⥤
      Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  Y.ι.opensFunctor.sheafPullback AddCommGrpCat.{u} _ _


-- @@ L94-96 verbatim
/-- The adjunction `j_! ⊣ j^*`. -/
def extendRestrictAdjunction : extendAb Y ⊣ restrictAb Y :=
  Y.ι.opensFunctor.sheafAdjunctionContinuous AddCommGrpCat.{u} _ _


-- @@ L98-103 verbatim
/-- `j^*` preserves finite colimits (it is a left adjoint of `j_*`, `G` being cocontinuous). -/
theorem preservesFiniteColimits_restrictAb : PreservesFiniteColimits (restrictAb Y) :=
  have := (Y.ι.opensFunctor.sheafAdjunctionCocontinuous AddCommGrpCat.{u}
    (Opens.grothendieckTopology (Y : AlgebraicGeometry.Scheme.{u}))
    (Opens.grothendieckTopology X)).leftAdjoint_preservesColimits
  inferInstance


-- @@ L105-107 verbatim
/-- `j_!` preserves finite limits (`preservesFiniteLimits_sheafPullback_opensFunctor`). -/
theorem preservesFiniteLimits_extendAb : PreservesFiniteLimits (extendAb Y) :=
  Y.preservesFiniteLimits_sheafPullback_opensFunctor


-- @@ L109-112 verbatim
/-- The sections functor `F ↦ F(W)` (as a set) on abelian sheaves on `X`. -/
abbrev sectionsTypeAb (W : X.Opens) :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ⥤ Type u :=
  sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op W) ⋙ CategoryTheory.forget AddCommGrpCat.{u}


-- @@ L114-120 verbatim
/-- `ℤ[h_W]^#` corepresents `F ↦ F(W)` (`sectionsEquiv`, evaluation at the canonical generator). -/
def freeSheafCorepresentableBy (W : X.Opens) :
    (sectionsTypeAb W).CorepresentableBy (freeSheaf (Opens.grothendieckTopology X) W) where
  homEquiv {F} := sectionsEquiv W F
  homEquiv_comp {F F'} g f := by
    rw [sectionsEquiv_apply_eq, sectionsEquiv_apply_eq]
    rfl


-- @@ L122-126 verbatim
/-- The constant sheaf `ℤ_Y` on the open subscheme `Y` (the first variable of `Sheaf.H`). -/
abbrev constantZ :
    Sheaf (Opens.grothendieckTopology (Y : AlgebraicGeometry.Scheme.{u})) AddCommGrpCat.{u} :=
  (constantSheaf (Opens.grothendieckTopology (Y : AlgebraicGeometry.Scheme.{u}))
    AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))


-- @@ L128-138 verbatim
/-- `Hom(ℤ_Y, K) ≃ K(⊤)` for an abelian sheaf `K` on the open subscheme `Y`: through
`ℤ_Y ≅ ℤ[h_⊤]^#` (`freeSheafTerminalIsoConstantSheaf`) and `sectionsEquiv`. -/
def constantZHomEquiv
    (K : Sheaf (Opens.grothendieckTopology (Y : AlgebraicGeometry.Scheme.{u})) AddCommGrpCat.{u}) :
    (constantZ Y ⟶ K) ≃
      (K.obj ⋙ CategoryTheory.forget AddCommGrpCat.{u}).obj
        (op (⊤ : (Y : AlgebraicGeometry.Scheme.{u}).Opens)) :=
  ((freeSheafTerminalIsoConstantSheaf
      (Opens.grothendieckTopology (Y : AlgebraicGeometry.Scheme.{u})) isTerminalTop).symm.homCongr
        (Iso.refl K)).trans
    (sectionsEquiv (⊤ : (Y : AlgebraicGeometry.Scheme.{u}).Opens) K)


-- @@ L140-147 verbatim
theorem constantZHomEquiv_comp
    {K K' : Sheaf (Opens.grothendieckTopology (Y : AlgebraicGeometry.Scheme.{u})) AddCommGrpCat.{u}}
    (φ : constantZ Y ⟶ K) (g : K ⟶ K') :
    constantZHomEquiv Y K' (φ ≫ g) =
      (g.hom.app (op (⊤ : (Y : AlgebraicGeometry.Scheme.{u}).Opens))) (constantZHomEquiv Y K φ) := by
  simp only [constantZHomEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id,
    Iso.symm_inv, sectionsEquiv_apply_eq]
  rfl


-- @@ L149-156 verbatim
/-- `j_! ℤ_Y` corepresents `F ↦ F(Y.ι ''ᵁ ⊤)`:
`Hom(j_! ℤ_Y, F) ≃ Hom(ℤ_Y, j^* F) ≃ (j^* F)(⊤) = F(Y.ι ''ᵁ ⊤)`. -/
def extendConstantCorepresentableBy :
    (sectionsTypeAb (Y.ι ''ᵁ ⊤)).CorepresentableBy ((extendAb Y).obj (constantZ Y)) where
  homEquiv {F} :=
    ((extendRestrictAdjunction Y).homEquiv _ F).trans (constantZHomEquiv Y ((restrictAb Y).obj F))
  -- both sides unfold to `(unit ≫ j^*.map (f ≫ g)).hom.app (op ⊤) (gen ⊤)` (definitional).
  homEquiv_comp _ _ := rfl


-- @@ L158-162 verbatim
/-- **`ℤ[h_Y]^# ≅ j_! ℤ_Y`** (both corepresent `F ↦ F(Y)`). -/
def freeSheafIsoExtendConstant :
    freeSheaf (Opens.grothendieckTopology X) Y ≅ (extendAb Y).obj (constantZ Y) :=
  eqToIso (congrArg (freeSheaf (Opens.grothendieckTopology X)) Y.ι_image_top.symm) ≪≫
    (freeSheafCorepresentableBy (Y.ι ''ᵁ ⊤)).uniqueUpToIso (extendConstantCorepresentableBy Y)


-- @@ L164-164 verbatim
end AlgebraicGeometry.Scheme.Opens


-- @@ L166-166 verbatim
end
