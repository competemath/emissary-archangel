import OAI.CategoryTheory.Globular.CylinderContractibility


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u v w


-- @@ L7-7 verbatim
namespace Grothendieck

-- @@ L8-8 verbatim
open CategoryTheory CategoryTheory.Limits Opposite

-- @@ L9-9 verbatim
namespace GlobularTheory.Model

-- @@ L10-10 verbatim
variable {C : GlobularTheory.{v}} (hC : C.IsCoherator) (q n : ℕ)

-- @@ L11-11 verbatim
variable [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)]

-- @@ L12-13 verbatim
local instance smallColimitsShapes : HasColimitsOfSize.{0,v} (CutoffModels C q) :=
  hasColimitsOfSizeShrink.{0,v} (CutoffModels C q)


-- @@ L15-19 verbatim
omit [HasColimitsOfSize.{v,v} (CutoffModels C q)] [HasLimitsOfSize.{v,v} (CutoffModels C q)] in
theorem Cofibrant.of_iso {X Y : CutoffModels C q} (hX : Cofibrant hC q X) (e : X ≅ Y) :
    Cofibrant hC q Y := by
  intro P Q p hp f
  exact hX.retract e.inv e.hom e.inv_hom_id p hp f


-- @@ L21-22 verbatim
noncomputable def cylinderShape (S : Shape) : CutoffModels C q :=
  (cylinderFrame hC q n).realization.obj (GlobularPresheaf.liftSmall.obj S.realize)


-- @@ L24-47 verbatim
theorem cylinderShape_contractible (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1)) (S : Shape) :
    Cofibrant hC q (cylinderShape hC q n S) ∧ (cylinderShape hC q n S).obj.underlying.HasFillers := by
  let T := GlobularPresheaf.liftSmall.{v}.obj S.realize
  let e := cylinderEndpoint hC q n false
  let m := max n S.height
  have hm (j : ℕ) (hj : m < j) : IsEmpty (T.underlying.Cell j) := by
    constructor
    intro x
    exact (S.2.bounded j (lt_of_le_of_lt (Nat.le_max_right n S.height) hj)).false x.down
  let U := (cylinderCriticalData hC q n false).whiskerPresentation T.underlying
  let V := GlobularFrame.Presentation.full e T.underlying m hm
  let f := V.comparison U (Nat.le_max_left _ _)
  have hf : (sourceClass hC q (n+1)).rlp.llp f := by
    intro X Y p hp
    exact V.comparison_lifting U (Nat.le_max_left _ _) p (fun k hk _ =>
      (cylinder_oneSided_contractible hC q n hnq H k hk false).2.2 p hp)
  have hU : Cofibrant hC q U.obj := cutoffFrame_cofibrant hC q _
  have hUF : U.obj.obj.underlying.HasFillers := cutoffFrame_whisker_hasFillers hC q n hnq H S false
  have hV : Cofibrant hC q V.obj := hU.of_cofibration f
    (boundaryClass_cofibration_le hC q 0 (n+1) (Nat.zero_le _) f
      (sourceClass_cofibration_le hC q (n+1) f hf))
  have hVF : V.obj.obj.underlying.HasFillers := H f hf hU hUF
  let iso := (cylinderFrame hC q n).realization.mapIso T.underlyingPresheafIso
  exact ⟨Cofibrant.of_iso hC q hV iso, hasFillers_of_iso (q := q) iso hVF⟩


-- @@ L49-55 verbatim
theorem cylinderNode_contractible (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1)) (j : ℕ) :
    Cofibrant hC q (cylinderNode hC q n j).obj ∧
      (cylinderNode hC q n j).obj.obj.underlying.HasFillers := by
  let iso := (cylinderFrame hC q n).realization.mapIso (GlobularPresheaf.liftSmallDiskIso j) ≪≫
    (cylinderFrame hC q n).diagram.globeIso j
  have h := cylinderShape_contractible hC q n hnq H (Shape.globe j)
  exact ⟨Cofibrant.of_iso hC q h.1 iso, hasFillers_of_iso (q := q) iso h.2⟩


-- @@ L57-66 verbatim
omit [HasColimitsOfSize.{v,v} (CutoffModels C q)] in
theorem boundary_cofibration_split {r : ℕ} {X Y : CutoffModels C q} (i : X ⟶ Y)
    (hi : (boundaryClass hC q r).rlp.llp i) (hX : X.obj.underlying.HasFillers) :
    ∃ s : Y ⟶ X, i ≫ s = 𝟙 X := by
  have hp : (boundaryClass hC q r).rlp (terminal.from X) := by
    rintro A B f ⟨⟨k,hk⟩⟩
    exact (lifting_terminal_iff _ _).2 ((cutoff_hasFillers_iff hC q _).1 hX k)
  have sq : CommSq (𝟙 X) i (terminal.from X) (terminal.from Y) := ⟨terminal.hom_ext _ _⟩
  let : sq.HasLift := (hi _ hp).sq_hasLift sq
  exact ⟨sq.lift, sq.fac_left⟩


-- @@ L68-73 verbatim
theorem cylinder_oneSided_split_high (hnq : n ≤ q) (H : ExpansionContraction hC q (n+1))
    {j : ℕ} (hj : n < j) (ε : Bool) :
    ∃ s : (cylinderFrame hC q n).obj j ⟶ GlobularFrame.oneSided (cylinderEndpoint hC q n ε) j,
      GlobularFrame.oneSidedMap (cylinderEndpoint hC q n ε) j ≫ s = 𝟙 _ := by
  exact boundary_cofibration_split hC q _ (cylinderFrame_upper hC q n hj ε)
    (cylinder_oneSided_contractible hC q n hnq H j hj ε).2.1


-- @@ L75-75 verbatim
end GlobularTheory.Model

-- @@ L76-76 verbatim
end Grothendieck


-- @@ L78-78 verbatim
end OAI
