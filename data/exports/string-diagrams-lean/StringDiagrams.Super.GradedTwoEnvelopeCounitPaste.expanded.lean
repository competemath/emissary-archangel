import StringDiagrams.Super.GradedTwoEnvelopeCounitComposition
import StringDiagrams.Super.TwoFunctorPrecomposition
import StringDiagrams.Super.TwoFunctorPostcomposition


-- @@ L5-17 verbatim
/-!
# The genuine composite-functor counit paste

The two legs are actual precomposition and postcomposition of the counit
comparisons. Equalities of complete 2-superfunctor records normalize all
three boundaries. Their vertical composite retains the target associators,
unitors, and both compositor factors in postcomposition.

This constructs a strong graded transformation with precisely the endpoints
of `counitNaturality (F ≫ G)`. An invertible supermodification identifying
these two transformations is not asserted: `comparisonCompIso` alone does
not identify the functor-whiskered legs with chosen density comparisons.
-/


-- @@ L19-19 verbatim
noncomputable section

-- @@ L20-20 verbatim
namespace StringDiagrams

-- @@ L21-21 verbatim
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory

-- @@ L22-22 verbatim
universe w w₁ v₁ u₁

-- @@ L23-23 verbatim
variable {R : Type w} [CommRing R]


-- @@ L25-25 verbatim
namespace TwoNatTrans

-- @@ L26-27 verbatim
variable {B : GTwoSCat.{w, w₁, v₁, u₁} R} {C : QPiTwoGSCat.{w, w₁, v₁, u₁} R}
  {S T S' T' : TwoSuperfunctor R (QPiTwoEnvelope R B) C}


-- @@ L29-35 verbatim
/-- Boundary equality transport preserves grading of the full transformation. -/
theorem transportBoundary_isGraded (h : S = S') (k : T = T')
    (θ : TwoNatTrans S T) (hθ : θ.IsGraded) :
    (transportBoundary h k θ).IsGraded := by
  cases h
  cases k
  exact hθ


-- @@ L37-43 verbatim
/-- Boundary equality transport preserves invertibility of every naturality cell. -/
theorem transportBoundary_isStrong (h : S = S') (k : T = T')
    (θ : TwoNatTrans S T) (hθ : θ.IsStrong) :
    (transportBoundary h k θ).IsStrong := by
  cases h
  cases k
  exact hθ

-- @@ L44-50 verbatim
/-- Transport only retypes the object component; it does not replace it. -/
theorem transportBoundary_X_heq (h : S = S') (k : T = T')
    (θ : TwoNatTrans S T) (a : QPiTwoEnvelope R B) :
    HEq ((transportBoundary h k θ).X a) (θ.X a) := by
  cases h
  cases k
  rfl

-- @@ L51-51 verbatim
end TwoNatTrans


-- @@ L53-53 verbatim
namespace QPiTwoEnvelope

-- @@ L54-54 verbatim
set_option backward.isDefEq.respectTransparency false

-- @@ L55-55 verbatim
variable {B C D : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (F : B ⟶ C) (G : C ⟶ D)


-- @@ L57-62 verbatim
/-- The left-whiskered source is the direct composite square's source. -/
theorem counitPaste_source :
    (mapQPi F.1).comp ((mapQPi G.1).comp (counit D)) =
      (mapQPi (F ≫ G).1).comp (counit D) := by
  change _ = (mapQPi (F.1.comp G.1)).comp (counit D)
  rw [mapQPi_comp, TwoSuperfunctor.comp_assoc]


-- @@ L64-68 verbatim
/-- The right-whiskered source matches the left-whiskered target. -/
theorem counitPaste_middle :
    ((mapQPi F.1).comp (counit C)).comp G.1 =
      (mapQPi F.1).comp ((counit C).comp G.1) :=
  TwoSuperfunctor.comp_assoc _ _ _


-- @@ L70-73 verbatim
/-- The right-whiskered target is the direct composite square's target. -/
theorem counitPaste_target :
    ((counit B).comp F.1).comp G.1 = (counit B).comp (F ≫ G).1 :=
  TwoSuperfunctor.comp_assoc _ _ _


-- @@ L75-80 verbatim
/-- The actual left leg, with its outer source boundary normalized. -/
def counitPasteLeft : TwoNatTrans
    ((mapQPi (F ≫ G).1).comp (counit D))
    ((mapQPi F.1).comp ((counit C).comp G.1)) :=
  TwoNatTrans.transportBoundary (counitPaste_source F G) rfl
    (TwoNatTrans.precompose (mapQPi F.1) (counitNaturality G))


-- @@ L82-87 verbatim
/-- The actual right leg, with both middle and outer boundaries normalized. -/
def counitPasteRight : TwoNatTrans
    ((mapQPi F.1).comp ((counit C).comp G.1))
    ((counit B).comp (F ≫ G).1) :=
  TwoNatTrans.transportBoundary (counitPaste_middle F G) (counitPaste_target F G)
    (TwoNatTrans.postcompose G.1 (counitNaturality F))


-- @@ L89-91 verbatim
theorem counitPasteLeft_isGraded : (counitPasteLeft F G).IsGraded :=
  TwoNatTrans.transportBoundary_isGraded _ _ _
    (TwoNatTrans.precompose_isGraded _ (counitNaturality_isGraded G))


-- @@ L93-95 verbatim
theorem counitPasteLeft_isStrong : (counitPasteLeft F G).IsStrong :=
  TwoNatTrans.transportBoundary_isStrong _ _ _
    (TwoNatTrans.precompose_isStrong _ (counitNaturality_isStrong G))


-- @@ L97-99 verbatim
theorem counitPasteRight_isGraded : (counitPasteRight F G).IsGraded :=
  TwoNatTrans.transportBoundary_isGraded _ _ _
    (TwoNatTrans.postcompose_isGraded _ G.2 (counitNaturality_isGraded F))


-- @@ L101-103 verbatim
theorem counitPasteRight_isStrong : (counitPasteRight F G).IsStrong :=
  TwoNatTrans.transportBoundary_isStrong _ _ _
    (TwoNatTrans.postcompose_isStrong _ (counitNaturality_isStrong F))


-- @@ L105-108 verbatim
/-- Paste the genuine functor-whiskered counit squares, not substitute comparisons. -/
def counitNaturalityPaste : TwoNatTrans
    ((mapQPi (F ≫ G).1).comp (counit D)) ((counit B).comp (F ≫ G).1) :=
  TwoNatTrans.vcomp (counitPasteLeft F G) (counitPasteRight F G)


-- @@ L110-112 verbatim
theorem counitPasteLeft_X (a : QPiTwoEnvelope R B) :
    (counitPasteLeft F G).X a = (counitNaturality G).X ((mapQPi F.1).obj a) :=
  eq_of_heq (TwoNatTrans.transportBoundary_X_heq _ _ _ a)


-- @@ L114-116 verbatim
theorem counitPasteRight_X (a : QPiTwoEnvelope R B) :
    (counitPasteRight F G).X a = G.1.map ((counitNaturality F).X a) :=
  eq_of_heq (TwoNatTrans.transportBoundary_X_heq _ _ _ a)


-- @@ L118-123 verbatim
/-- The object component uses precisely the two functor-whiskered components. -/
theorem counitNaturalityPaste_X (a : QPiTwoEnvelope R B) :
    (counitNaturalityPaste F G).X a =
      (counitNaturality G).X ((mapQPi F.1).obj a) ≫ G.1.map ((counitNaturality F).X a) := by
  change (counitPasteLeft F G).X a ≫ (counitPasteRight F G).X a = _
  rw [counitPasteLeft_X, counitPasteRight_X]


-- @@ L125-126 verbatim
theorem counitNaturalityPaste_isGraded : (counitNaturalityPaste F G).IsGraded :=
  TwoNatTrans.IsGraded.vcomp (counitPasteLeft_isGraded F G) (counitPasteRight_isGraded F G)


-- @@ L128-129 verbatim
theorem counitNaturalityPaste_isStrong : (counitNaturalityPaste F G).IsStrong :=
  TwoNatTrans.vcomp_isStrong (counitPasteLeft_isStrong F G) (counitPasteRight_isStrong F G)


-- @@ L131-138 verbatim
/-- The paste's naturality is for all 2-morphisms, without evenness or degree assumptions. -/
theorem counitNaturalityPaste_naturality {a b : QPiTwoEnvelope R B}
    {f g : a ⟶ b} (η : f ⟶ g) :
    ((mapQPi (F ≫ G).1).comp (counit D)).map₂ η ▷
        (counitNaturalityPaste F G).X b ≫ (counitNaturalityPaste F G).x g =
      (counitNaturalityPaste F G).x f ≫ (counitNaturalityPaste F G).X a ◁
        ((counit B).comp (F ≫ G).1).map₂ η :=
  (counitNaturalityPaste F G).naturality η


-- @@ L140-140 verbatim
end QPiTwoEnvelope

-- @@ L141-141 verbatim
end StringDiagrams
