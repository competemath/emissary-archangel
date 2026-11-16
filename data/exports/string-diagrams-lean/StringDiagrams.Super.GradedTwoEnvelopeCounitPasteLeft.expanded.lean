import StringDiagrams.Super.GradedTwoEnvelopeCounitPasteCoherence


-- @@ L3-8 verbatim
/-!
# The boundary-transported left counit-paste leg

Compatibility of the actual prewhiskered leg with its chosen density comparison.
The right leg and assembly of the full composite counit coherence are separate.
-/


-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
namespace StringDiagrams

-- @@ L12-12 verbatim
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory

-- @@ L13-13 verbatim
universe w w₁ v₁ u₁

-- @@ L14-14 verbatim
variable {R : Type w} [CommRing R]

-- @@ L15-15 verbatim
namespace TwoNatTrans

-- @@ L16-17 verbatim
variable {B : GTwoSCat.{w, w₁, v₁, u₁} R} {C : QPiTwoGSCat.{w, w₁, v₁, u₁} R}
  {S T S' T' : TwoSuperfunctor R (QPiTwoEnvelope R B) C}


-- @@ L19-22 verbatim
theorem transportSource_X_heq (h : S = S') (θ : TwoNatTrans S T)
    (a : QPiTwoEnvelope R B) : HEq ((transportSource h θ).X a) (θ.X a) := by
  cases h
  rfl


-- @@ L24-28 verbatim
theorem transportSource_x_heq (h : S = S') (θ : TwoNatTrans S T)
    {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    HEq ((transportSource h θ).x f) (θ.x f) := by
  cases h
  rfl


-- @@ L30-35 verbatim
theorem transportBoundary_x_heq (h : S = S') (k : T = T') (θ : TwoNatTrans S T)
    {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    HEq ((transportBoundary h k θ).x f) (θ.x f) := by
  cases h
  cases k
  rfl


-- @@ L37-42 verbatim
/-- Equality of transformations supplies an even degree-zero supermodification. -/
theorem eqToIso_hom_isHomogeneous {θ ψ : TwoNatTrans S T} (h : θ = ψ) :
    (eqToIso h).hom.IsHomogeneous 0 0 := by
  cases h
  intro a
  exact ⟨id_mem (R := R) _, id_mem_degree (R := R) _⟩


-- @@ L44-44 verbatim
end TwoNatTrans

-- @@ L45-45 verbatim
namespace QPiTwoEnvelope

-- @@ L46-46 verbatim
set_option backward.isDefEq.respectTransparency false

-- @@ L47-47 verbatim
variable {B C D : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) (G : C ⟶ D)

-- @@ L48-49 verbatim
local instance : ∀ a b : D, QPiSupercategory R (a ⟶ b) :=
  fun a b => QPiTwoSupercategory.homQPiLeft a b


-- @@ L51-58 verbatim
/-- Equality of restrictions for precisely the normalized left-leg endpoints. -/
theorem counitPasteLeft_restrict :
    restrict ((mapQPi (F ≫ G).1).comp (counit D)) =
      restrict ((mapQPi F.1).comp ((counit C).comp G.1)) := by
  rw [← counitPaste_source F G]
  simp only [restrict_eq_comp, ← TwoSuperfunctor.comp_assoc, twoJ_naturality]
  simpa only [TwoSuperfunctor.comp_assoc, restrict_eq_comp] using
    congrArg F.1.comp (counit_naturality_restrict G)


-- @@ L60-67 verbatim
/-- The chosen density comparison with the actual left-paste boundaries. -/
def counitPasteLeftComparison : TwoNatTrans
    ((mapQPi (F ≫ G).1).comp (counit D))
    ((mapQPi F.1).comp ((counit C).comp G.1)) :=
  comparison (B := B.toGTwoSCat) _ _
    ((mapQPi_isGraded (F ≫ G).2).comp (counit_isGraded D))
    ((mapQPi_isGraded F.2).comp ((counit_isGraded C).comp G.2))
    (counitPasteLeft_restrict F G)


-- @@ L69-73 verbatim
private theorem left_pre_restrict :
    restrict ((mapQPi F.1).comp ((mapQPi G.1).comp (counit D))) =
      restrict ((mapQPi F.1).comp ((counit C).comp G.1)) := by
  rw [counitPaste_source F G]
  exact counitPasteLeft_restrict F G


-- @@ L75-89 verbatim
/-- Congruence for the full vertical-paste cell, retaining all associators. -/
private theorem densityPasteCell_heq {a b : D} {s m t : a ⟶ b}
    {l l' : s ≫ 𝟙 b ⟶ 𝟙 a ≫ m}
    {X X' : a ⟶ a} {Y Y' : b ⟶ b}
    {r : m ≫ Y ⟶ X ≫ t} {r' : m ≫ Y' ⟶ X' ≫ t}
    (hl : l = l') (hX : X = X') (hY : Y = Y') (hr : HEq r r') :
    HEq ((associator s (𝟙 b) Y).inv ≫ l ▷ Y ≫
      (associator (𝟙 a) m Y).hom ≫ (𝟙 a) ◁ r ≫ (associator (𝟙 a) X t).inv)
    ((associator s (𝟙 b) Y').inv ≫ l' ▷ Y' ≫
      (associator (𝟙 a) m Y').hom ≫ (𝟙 a) ◁ r' ≫ (associator (𝟙 a) X' t).inv) := by
  cases hX
  cases hY
  cases hl
  cases eq_of_heq hr
  rfl


-- @@ L91-150 verbatim
private theorem precompose_counitNaturality_eq_comparison :
    TwoNatTrans.precompose (mapQPi F.1) (counitNaturality G) =
      comparison (B := B.toGTwoSCat) _ _
        ((mapQPi_isGraded F.2).comp ((mapQPi_isGraded G.2).comp (counit_isGraded D)))
        ((mapQPi_isGraded F.2).comp ((counit_isGraded C).comp G.2))
        (left_pre_restrict F G) := by
  unfold counitNaturality comparison
  have hX₁ (a : QPiTwoEnvelope R C) :
      (TwoNatTrans.transportSource
        (congrArg extend (counit_naturality_restrict G).symm)
        (extendRestrictNatTrans ((counit C).comp G.1) ((counit_isGraded C).comp G.2))).X a =
      𝟙 (G.1.obj a.as.as) :=
    eq_of_heq (TwoNatTrans.transportSource_X_heq _ _ a)
  have hX₂ (a : QPiTwoEnvelope R B) :
      (TwoNatTrans.transportSource
        (congrArg extend (left_pre_restrict F G).symm)
        (extendRestrictNatTrans ((mapQPi F.1).comp ((counit C).comp G.1))
          ((mapQPi_isGraded F.2).comp ((counit_isGraded C).comp G.2)))).X a =
      𝟙 (G.1.obj (F.1.obj a.as.as)) :=
    eq_of_heq (TwoNatTrans.transportSource_X_heq _ _ a)
  have hX (a : QPiTwoEnvelope R B) :
      (TwoNatTrans.transportSource
        (congrArg extend (counit_naturality_restrict G).symm)
        (extendRestrictNatTrans ((counit C).comp G.1) ((counit_isGraded C).comp G.2))).X
          ((mapQPi F.1).obj a) =
      (TwoNatTrans.transportSource
        (congrArg extend (left_pre_restrict F G).symm)
        (extendRestrictNatTrans ((mapQPi F.1).comp ((counit C).comp G.1))
          ((mapQPi_isGraded F.2).comp ((counit_isGraded C).comp G.2)))).X a := by
    rw [hX₁, hX₂]
    rfl
  have hx {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
      HEq ((TwoNatTrans.transportSource
        (congrArg extend (counit_naturality_restrict G).symm)
        (extendRestrictNatTrans ((counit C).comp G.1) ((counit_isGraded C).comp G.2))).x
          ((mapQPi F.1).map f))
      ((TwoNatTrans.transportSource
        (congrArg extend (left_pre_restrict F G).symm)
        (extendRestrictNatTrans ((mapQPi F.1).comp ((counit C).comp G.1))
          ((mapQPi_isGraded F.2).comp ((counit_isGraded C).comp G.2)))).x f) := by
    exact (TwoNatTrans.transportSource_x_heq
      (congrArg extend (counit_naturality_restrict G).symm)
      (extendRestrictNatTrans ((counit C).comp G.1) ((counit_isGraded C).comp G.2))
      ((mapQPi F.1).map f)).trans
      ((heq_of_eq (extendRestrictX_precompose F.1 F.2
        ((counit C).comp G.1) ((counit_isGraded C).comp G.2) f).symm).trans
        (TwoNatTrans.transportSource_x_heq
          (congrArg extend (left_pre_restrict F G).symm)
          (extendRestrictNatTrans ((mapQPi F.1).comp ((counit C).comp G.1))
            ((mapQPi_isGraded F.2).comp ((counit_isGraded C).comp G.2))) f).symm)
  apply TwoEnvelope.twoNatTrans_ext
  · funext a
    simp only [TwoNatTrans.precompose_X, TwoNatTrans.vcomp_X, hX₁, hX₂]
    rfl
  · intro a b f
    have hi := (extendRestrictInvX_precompose F.1 F.2
      ((mapQPi G.1).comp (counit D))
      ((mapQPi_isGraded G.2).comp (counit_isGraded D)) f).symm
    simp only [TwoNatTrans.precompose_x, TwoNatTrans.vcomp_x]
    exact densityPasteCell_heq hi (hX a) (hX b) (hx f)


-- @@ L152-158 verbatim
/-- Equality of complete transformation records for the actual transported left leg.
The comparison has its own chosen density pair, not replacement paste data. -/
theorem counitPasteLeft_eq_comparison :
    counitPasteLeft F G = counitPasteLeftComparison F G := by
  unfold counitPasteLeft
  rw [precompose_counitNaturality_eq_comparison]
  exact comparison_transportBoundary _ _ _ _ _ _ _ _ _ _


-- @@ L160-163 verbatim
/-- The actual boundary-transported left leg has its invertible supermodification
into the matching chosen density comparison. -/
def counitPasteLeftIso : counitPasteLeft F G ≅ counitPasteLeftComparison F G :=
  eqToIso (counitPasteLeft_eq_comparison F G)


-- @@ L165-167 verbatim
theorem counitPasteLeftIso_hom_isHomogeneous :
    (counitPasteLeftIso F G).hom.IsHomogeneous 0 0 :=
  TwoNatTrans.eqToIso_hom_isHomogeneous (counitPasteLeft_eq_comparison F G)


-- @@ L169-171 verbatim
theorem counitPasteLeftIso_inv_isHomogeneous :
    (counitPasteLeftIso F G).inv.IsHomogeneous 0 0 :=
  TwoNatTrans.iso_inv_isHomogeneous _ (counitPasteLeftIso_hom_isHomogeneous F G)


-- @@ L173-180 verbatim
/-- The modification naturality equation holds for every formal 1-morphism,
with arbitrary parity label and integer shift. -/
theorem counitPasteLeftIso_naturality {a b : QPiTwoEnvelope R B} (f : a ⟶ b) :
    (counitPasteLeft F G).x f ≫ (counitPasteLeftIso F G).hom.app a ▷
        ((mapQPi F.1).comp ((counit C).comp G.1)).map f =
      ((mapQPi (F ≫ G).1).comp (counit D)).map f ◁
        (counitPasteLeftIso F G).hom.app b ≫ (counitPasteLeftComparison F G).x f :=
  (counitPasteLeftIso F G).hom.naturality f


-- @@ L182-184 verbatim
theorem counitPasteLeftIso_hom_inv_id :
    (counitPasteLeftIso F G).hom ≫ (counitPasteLeftIso F G).inv =
      𝟙 (counitPasteLeft F G) := (counitPasteLeftIso F G).hom_inv_id


-- @@ L186-188 verbatim
theorem counitPasteLeftIso_inv_hom_id :
    (counitPasteLeftIso F G).inv ≫ (counitPasteLeftIso F G).hom =
      𝟙 (counitPasteLeftComparison F G) := (counitPasteLeftIso F G).inv_hom_id


-- @@ L190-190 verbatim
end QPiTwoEnvelope

-- @@ L191-191 verbatim
end StringDiagrams
