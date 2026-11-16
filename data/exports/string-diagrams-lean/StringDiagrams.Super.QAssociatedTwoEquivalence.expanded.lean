import StringDiagrams.Super.QPiTwoSCatDUnit
import StringDiagrams.Super.QAssociatedTwoNat


-- @@ L4-25 verbatim
/-!
# The §6 analogue of Lemma 5.4 as an equivalence of categories

Following J. Brundan, A. P. Ellis, *Monoidal supercategories*, arXiv:1603.05928v3, §6: after
Definition 6.14 the paper leaves the analogues of Lemma 5.4 and Theorem 5.5 to the reader. The
analogue of Lemma 5.4 is that `𝔻 : (Q, Π)-2-Cat → (Q, Π)-2-GSCat` and
`𝔼 : (Q, Π)-2-GSCat → (Q, Π)-2-Cat` are mutually inverse equivalences of categories. Here:

* `𝕋_𝔅 : 𝔻(𝔼 𝔅) → 𝔅` (`QAssociated2.T`) is graded (`QAssociated2.T_isGraded`) and an
  isomorphism in `(Q, Π)-2-GSCat`: its inverse is the graded 2-superfunctor `QAssociated2.Tinv`,
  the identity on objects and 1-morphisms and the inverse of `𝕋_𝔅` on 2-morphisms, with identity
  coherence maps (`QAssociated2.T_comp_Tinv`, `QAssociated2.Tinv_comp_T`, `QPiTwoGSCat.TIso`).
* `𝕋` is natural, as an equality of 2-superfunctors `𝔻(𝔼 ℝ) ≫ 𝕋_𝔅' = 𝕋_𝔅 ≫ ℝ`
  (`QAssociated2.mapQ_comp_T`).

Hence `𝔼 ⋙ 𝔻 ≅ 𝟭` (`QPiTwoGSCat.counitNatIso`), and with `𝔼 ∘ 𝔻 = I` (`QPiTwoCat.unitNatIso`,
`StringDiagrams.Super.QPiTwoSCatDUnit`) the equivalence of categories
`(Q, Π)-2-Cat ≌ (Q, Π)-2-GSCat` (`QPiTwoCat.equivalence`).

`(Q, Π)`-2-functors are those of `StringDiagrams.Super.QPiTwoSCat` (with the compatibility axiom
recorded in the README, as for erratum 4 to Definition 6.12).
-/


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
namespace StringDiagrams


-- @@ L31-31 verbatim
open CategoryTheory Supercategory GradedSupercategory BicategoryStruct TwoSupercategory


-- @@ L33-33 verbatim
universe w w₁ v₁ u₁ w₂ v₂ u₂


-- @@ L35-35 verbatim
namespace QAssociated2


-- @@ L37-37 verbatim
section T


-- @@ L39-42 verbatim
variable {R : Type w} [CommRing R] {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B] [GradedTwoSupercategory R B] [QPiTwoSupercategory R B]


-- @@ L44-44 verbatim
attribute [local instance] QPiTwoSupercategory.centralShift


-- @@ L46-50 verbatim
/-- `𝕋_𝔅` is a graded 2-superfunctor. -/
theorem T_isGraded : (T R B).IsGraded where
  map₂_mem_degree hx := T_map₂_mem_degree hx
  mapComp_hom_mem_degree _ _ := id_mem_degree _
  mapId_hom_mem_degree _ := id_mem_degree _


-- @@ L52-54 verbatim
theorem T_map₂_injective {a b : QAssociated2 R (GUnderlying2 R B)} {f g : a ⟶ b} {x y : f ⟶ g}
    (h : (T R B).map₂ x = (T R B).map₂ y) : x = y :=
  (T_map₂_bijective f g).1 h


-- @@ L56-57 verbatim
instance (a b : QAssociated2 R (GUnderlying2 R B)) : ((T R B).mapFunctor a b).Faithful where
  map_injective h := T_map₂_injective h


-- @@ L59-61 verbatim
instance (a b : QAssociated2 R (GUnderlying2 R B)) :
    IsGradedSuperfunctor R ((T R B).mapFunctor a b) :=
  T_isGraded.isGradedSuperfunctor a b


-- @@ L63-63 verbatim
/-! ### `𝕋` on whiskerings and coherence maps -/


-- @@ L65-68 verbatim
theorem T_map₂_whiskerLeft {a b c : QAssociated2 R (GUnderlying2 R B)} (f : a ⟶ b) {g h : b ⟶ c}
    (η : g ⟶ h) : (T R B).map₂ (f ◁ η) = (T R B).map f ◁ (T R B).map₂ η :=
  ((Category.id_comp _).symm.trans ((T R B).mapComp_naturality_right f η).symm).trans
    (Category.comp_id _)


-- @@ L70-73 verbatim
theorem T_map₂_whiskerRight {a b c : QAssociated2 R (GUnderlying2 R B)} {f g : a ⟶ b}
    (η : f ⟶ g) (h : b ⟶ c) : (T R B).map₂ (η ▷ h) = (T R B).map₂ η ▷ (T R B).map h :=
  ((Category.id_comp _).symm.trans ((T R B).mapComp_naturality_left η h).symm).trans
    (Category.comp_id _)


-- @@ L75-83 verbatim
theorem T_map₂_associator_inv {a b c d : QAssociated2 R (GUnderlying2 R B)} (f : a ⟶ b)
    (g : b ⟶ c) (h : c ⟶ d) :
    (T R B).map₂ (associator f g h).inv =
      (associator ((T R B).map f) ((T R B).map g) ((T R B).map h)).inv := by
  have := (T R B).map₂_associator f g h
  erw [whiskerLeft_id (R := R), id_whiskerRight (R := R), Category.id_comp, Category.id_comp,
    Category.comp_id] at this
  erw [Category.comp_id] at this
  exact this


-- @@ L85-89 verbatim
theorem T_map₂_leftUnitor_hom {a b : QAssociated2 R (GUnderlying2 R B)} (f : a ⟶ b) :
    (T R B).map₂ (leftUnitor f).hom = (leftUnitor ((T R B).map f)).hom := by
  have := (T R B).map₂_leftUnitor f
  erw [id_whiskerRight (R := R), Category.id_comp, Category.id_comp] at this
  exact this


-- @@ L91-95 verbatim
theorem T_map₂_rightUnitor_hom {a b : QAssociated2 R (GUnderlying2 R B)} (f : a ⟶ b) :
    (T R B).map₂ (rightUnitor f).hom = (rightUnitor ((T R B).map f)).hom := by
  have := (T R B).map₂_rightUnitor f
  erw [whiskerLeft_id (R := R), Category.id_comp, Category.id_comp] at this
  exact this


-- @@ L97-97 verbatim
/-! ### The inverse of `𝕋` -/


-- @@ L99-100 verbatim
/-- An object of `𝔻(𝔼 𝔅)`, from an object of `𝔅`. -/
abbrev mkO (a : B) : QAssociated2 R (GUnderlying2 R B) := ⟨⟨⟨⟨a⟩⟩⟩⟩


-- @@ L102-103 verbatim
/-- A 1-morphism of `𝔻(𝔼 𝔅)`, from a 1-morphism of `𝔅`. -/
abbrev mkM {a b : B} (f : a ⟶ b) : mkO (R := R) a ⟶ mkO b := ⟨⟨⟨⟨f⟩⟩⟩⟩


-- @@ L105-108 verbatim
variable (R B) in
/-- The inverse of `𝕋_𝔅` on 2-morphisms. -/
def tinv₂ {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : mkM (R := R) f ⟶ mkM g :=
  ((T_map₂_bijective (R := R) (B := B) (mkM f) (mkM g)).2 η).choose


-- @@ L110-111 verbatim
theorem T_map₂_tinv₂ {a b : B} {f g : a ⟶ b} (η : f ⟶ g) : (T R B).map₂ (tinv₂ R B η) = η :=
  ((T_map₂_bijective (R := R) (B := B) (mkM f) (mkM g)).2 η).choose_spec


-- @@ L113-115 verbatim
theorem tinv₂_T_map₂ {a b : B} {f g : a ⟶ b} (x : mkM (R := R) f ⟶ mkM g) :
    tinv₂ R B ((T R B).map₂ x) = x :=
  (T_map₂_bijective (R := R) (B := B) (mkM f) (mkM g)).1 (T_map₂_tinv₂ ((T R B).map₂ x))


-- @@ L117-122 verbatim
theorem tinv₂_mem {a b : B} {f g : a ⟶ b} {η : f ⟶ g} {p : ZMod 2}
    (hη : η ∈ parity (R := R) f g p) : tinv₂ R B η ∈ parity (R := R) _ _ p :=
  mem_of_map_mem ((T R B).mapFunctor (mkO a) (mkO b)) (by
    change (T R B).map₂ (tinv₂ R B η) ∈ _
    rw [T_map₂_tinv₂]
    exact hη)


-- @@ L124-129 verbatim
theorem tinv₂_mem_degree {a b : B} {f g : a ⟶ b} {η : f ⟶ g} {n : ℤ}
    (hη : η ∈ degree (R := R) f g n) : tinv₂ R B η ∈ degree (R := R) _ _ n :=
  mem_degree_of_map_mem ((T R B).mapFunctor (mkO a) (mkO b)) (by
    change (T R B).map₂ (tinv₂ R B η) ∈ _
    rw [T_map₂_tinv₂]
    exact hη)


-- @@ L131-177 verbatim
variable (R B) in
/-- **The §6 analogue of Lemma 5.4.** The inverse `𝕋_𝔅⁻¹ : 𝔅 → 𝔻(𝔼 𝔅)` of `𝕋_𝔅`: the identity on
objects and 1-morphisms, the inverse of `𝕋_𝔅` on 2-morphisms, with identity coherence maps. -/
@[simps obj map map₂]
def Tinv : TwoSuperfunctor R B (QAssociated2 R (GUnderlying2 R B)) where
  obj a := ⟨⟨⟨⟨a⟩⟩⟩⟩
  map f := ⟨⟨⟨⟨f⟩⟩⟩⟩
  map₂ η := tinv₂ R B η
  map₂_id f := T_map₂_injective ((T_map₂_tinv₂ _).trans ((T R B).map₂_id (mkM f)).symm)
  map₂_comp η θ := T_map₂_injective ((T_map₂_tinv₂ _).trans (by
    rw [(T R B).map₂_comp, T_map₂_tinv₂, T_map₂_tinv₂]
    rfl))
  map₂_add η θ := T_map₂_injective ((T_map₂_tinv₂ _).trans (by
    rw [(T R B).map₂_add, T_map₂_tinv₂, T_map₂_tinv₂]
    rfl))
  map₂_smul r η := T_map₂_injective ((T_map₂_tinv₂ _).trans (by
    rw [(T R B).map₂_smul, T_map₂_tinv₂]
    rfl))
  map₂_mem hη := tinv₂_mem hη
  mapComp f g := Iso.refl _
  mapId a := Iso.refl _
  mapComp_hom_mem _ _ := id_mem _
  mapId_hom_mem _ := id_mem _
  mapComp_naturality_left {a b c f f'} η g := T_map₂_injective (by
    rw [(T R B).map₂_comp, (T R B).map₂_comp, T_map₂_whiskerRight, T_map₂_tinv₂, T_map₂_tinv₂]
    erw [(T R B).map₂_id, (T R B).map₂_id, Category.comp_id, Category.id_comp]
    rfl)
  mapComp_naturality_right {a b c} f g g' η := T_map₂_injective (by
    rw [(T R B).map₂_comp, (T R B).map₂_comp, T_map₂_whiskerLeft, T_map₂_tinv₂, T_map₂_tinv₂]
    erw [(T R B).map₂_id, (T R B).map₂_id, Category.comp_id, Category.id_comp]
    rfl)
  map₂_associator f g h := T_map₂_injective (by
    simp only [(T R B).map₂_comp, T_map₂_whiskerLeft, T_map₂_whiskerRight, T_map₂_tinv₂,
      T_map₂_associator_inv, Iso.refl_hom, (T R B).map₂_id]
    erw [whiskerLeft_id (R := R), id_whiskerRight (R := R), Category.comp_id, Category.id_comp,
      Category.comp_id, Category.id_comp]
    rfl)
  map₂_leftUnitor f := T_map₂_injective (by
    simp only [(T R B).map₂_comp, T_map₂_whiskerRight, T_map₂_tinv₂, T_map₂_leftUnitor_hom,
      Iso.refl_hom, (T R B).map₂_id]
    erw [id_whiskerRight (R := R), Category.id_comp, Category.id_comp]
    rfl)
  map₂_rightUnitor f := T_map₂_injective (by
    simp only [(T R B).map₂_comp, T_map₂_whiskerLeft, T_map₂_tinv₂, T_map₂_rightUnitor_hom,
      Iso.refl_hom, (T R B).map₂_id]
    erw [whiskerLeft_id (R := R), Category.id_comp, Category.id_comp]
    rfl)


-- @@ L179-183 verbatim
/-- `𝕋_𝔅⁻¹` is a graded 2-superfunctor. -/
theorem Tinv_isGraded : (Tinv R B).IsGraded where
  map₂_mem_degree hx := tinv₂_mem_degree hx
  mapComp_hom_mem_degree _ _ := id_mem_degree _
  mapId_hom_mem_degree _ := id_mem_degree _


-- @@ L185-206 verbatim
/-- `𝕋_𝔅⁻¹ ∘ 𝕋_𝔅 = 𝕀`. -/
theorem T_comp_Tinv : (T R B).comp (Tinv R B) = TwoSuperfunctor.id R _ := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
    (heq_of_eq ?_)
  · funext a b f g x
    obtain ⟨⟨⟨⟨a⟩⟩⟩⟩ := a
    obtain ⟨⟨⟨⟨b⟩⟩⟩⟩ := b
    obtain ⟨⟨⟨⟨f⟩⟩⟩⟩ := f
    obtain ⟨⟨⟨⟨g⟩⟩⟩⟩ := g
    exact tinv₂_T_map₂ x
  · funext a b c f g
    obtain ⟨⟨⟨⟨a⟩⟩⟩⟩ := a
    obtain ⟨⟨⟨⟨b⟩⟩⟩⟩ := b
    obtain ⟨⟨⟨⟨c⟩⟩⟩⟩ := c
    obtain ⟨⟨⟨⟨f⟩⟩⟩⟩ := f
    obtain ⟨⟨⟨⟨g⟩⟩⟩⟩ := g
    apply Iso.ext
    exact (Category.id_comp _).trans ((Tinv R B).map₂_id _)
  · funext a
    obtain ⟨⟨⟨⟨a⟩⟩⟩⟩ := a
    apply Iso.ext
    exact (Category.id_comp _).trans ((Tinv R B).map₂_id _)


-- @@ L208-219 verbatim
/-- `𝕋_𝔅 ∘ 𝕋_𝔅⁻¹ = 𝕀`. -/
theorem Tinv_comp_T : (Tinv R B).comp (T R B) = TwoSuperfunctor.id R B := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
    (heq_of_eq ?_)
  · funext a b f g x
    exact T_map₂_tinv₂ x
  · funext a b c f g
    apply Iso.ext
    exact (Category.id_comp _).trans ((T R B).map₂_id _)
  · funext a
    apply Iso.ext
    exact (Category.id_comp _).trans ((T R B).map₂_id _)


-- @@ L221-221 verbatim
end T


-- @@ L223-223 verbatim
/-! ### Naturality of `𝕋` -/


-- @@ L225-225 verbatim
section Naturality


-- @@ L227-234 verbatim
variable {R : Type w} [CommRing R] {B : Type u₁} [BicategoryStruct.{w₁, v₁} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [∀ a b : B, GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B] [GradedTwoSupercategory R B] [QPiTwoSupercategory R B]
  {B' : Type u₂} [BicategoryStruct.{w₂, v₂} B']
  [∀ a b : B', Preadditive (a ⟶ b)] [∀ a b : B', Linear R (a ⟶ b)]
  [∀ a b : B', Supercategory R (a ⟶ b)] [∀ a b : B', GradedSupercategory R (a ⟶ b)]
  [TwoSupercategory R B'] [GradedTwoSupercategory R B'] [QPiTwoSupercategory R B']


-- @@ L236-236 verbatim
attribute [local instance] QPiTwoSupercategory.centralShift


-- @@ L238-252 verbatim
/-- **Naturality of `𝕋`**, as an equality of 2-superfunctors: `𝕋_𝔅' ∘ 𝔻(𝔼 ℝ) = ℝ ∘ 𝕋_𝔅`. -/
theorem mapQ_comp_T (G : TwoSuperfunctor R B B') (hG : G.IsGraded) :
    ((G.toQPiTwoFunctor hG).mapQ).comp (T R B') = (T R B).comp G := by
  refine TwoEnvelope.twoSuperfunctor_ext rfl HEq.rfl (heq_of_eq ?_) (heq_of_eq ?_)
    (heq_of_eq ?_)
  · funext a b f g x
    exact T_map₂_mapQ G hG x
  · funext a b c f g
    apply Iso.ext
    exact (Category.id_comp _).trans ((T_map₂_mapQ_mapComp G hG f g).trans
      ((Category.comp_id _).symm.trans (congrArg _ (G.map₂_id _).symm)))
  · funext a
    apply Iso.ext
    exact (Category.id_comp _).trans ((T_map₂_mapQ_mapId G hG a).trans
      ((Category.comp_id _).symm.trans (congrArg _ (G.map₂_id _).symm)))


-- @@ L254-254 verbatim
end Naturality


-- @@ L256-256 verbatim
end QAssociated2


-- @@ L258-258 verbatim
namespace QPiTwoGSCat


-- @@ L260-260 verbatim
variable {R : Type w} [CommRing R]


-- @@ L262-265 verbatim
/-- `𝕋_𝔅` as a morphism of `(Q, Π)-2-GSCat`. -/
def THom (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    QPiTwoGSCat.of R (QAssociated2 R (GUnderlying2 R B)) ⟶ B :=
  ⟨QAssociated2.T R B, QAssociated2.T_isGraded⟩


-- @@ L267-270 verbatim
/-- `𝕋_𝔅⁻¹` as a morphism of `(Q, Π)-2-GSCat`. -/
def TinvHom (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    B ⟶ QPiTwoGSCat.of R (QAssociated2 R (GUnderlying2 R B)) :=
  ⟨QAssociated2.Tinv R B, QAssociated2.Tinv_isGraded⟩


-- @@ L272-275 verbatim
theorem THom_comp_TinvHom (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) : THom B ≫ TinvHom B = 𝟙 _ := by
  apply Subtype.ext
  rw [QPiTwoGSCat.comp_val, QPiTwoGSCat.id_val]
  exact QAssociated2.T_comp_Tinv


-- @@ L277-280 verbatim
theorem TinvHom_comp_THom (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) : TinvHom B ≫ THom B = 𝟙 B := by
  apply Subtype.ext
  rw [QPiTwoGSCat.comp_val, QPiTwoGSCat.id_val]
  exact QAssociated2.Tinv_comp_T


-- @@ L282-289 verbatim
/-- **The §6 analogue of Lemma 5.4.** `𝕋_𝔅 : 𝔻(𝔼 𝔅) ≅ 𝔅` is an isomorphism in
`(Q, Π)-2-GSCat`. -/
def TIso (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    QPiTwoGSCat.of R (QAssociated2 R (GUnderlying2 R B)) ≅ B where
  hom := THom B
  inv := TinvHom B
  hom_inv_id := THom_comp_TinvHom B
  inv_hom_id := TinvHom_comp_THom B


-- @@ L291-297 verbatim
/-! ### The counit `𝔼 ⋙ 𝔻 ≅ 𝟭`

The objects `𝔻(𝔼 𝔅)` of `(Q, Π)-2-GSCat` carry the instances of the bundled categories, while
`QAssociated2.T` and `QAssociated2.mapQ_comp_T` are stated for `QAssociated2 R (GUnderlying2 R 𝔅)`
with directly synthesized instances. Unifying the two in one step is very slow, so the statements
below pass through `QAssociated2 R (𝔼 𝔅)` (`T'`, `Tinv'`, `mapQ_comp_T'`), which is cheap to
identify with either. -/


-- @@ L299-302 verbatim
/-- `𝕋_𝔅` with domain `(𝔼 𝔅)^`. -/
abbrev T' (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    TwoSuperfunctor R (QAssociated2 R (toQPiTwoCat.obj B)) B :=
  QAssociated2.T R B


-- @@ L304-307 verbatim
/-- `𝕋_𝔅⁻¹` with codomain `(𝔼 𝔅)^`. -/
abbrev Tinv' (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    TwoSuperfunctor R B (QAssociated2 R (toQPiTwoCat.obj B)) :=
  QAssociated2.Tinv R B


-- @@ L309-313 verbatim
theorem mapQ_comp_T' {B C : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (G : B ⟶ C) :
    ((G.1.toQPiTwoFunctor G.2).mapQ :
        TwoSuperfunctor R (QAssociated2 R (toQPiTwoCat.obj B))
          (QAssociated2 R (toQPiTwoCat.obj C))).comp (T' C) = (T' B).comp G.1 :=
  QAssociated2.mapQ_comp_T G.1 G.2


-- @@ L315-318 verbatim
set_option maxHeartbeats 1000000 in
theorem T'_comp_Tinv' (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    (T' B).comp (Tinv' B) = TwoSuperfunctor.id R (QAssociated2 R (toQPiTwoCat.obj B)) :=
  QAssociated2.T_comp_Tinv


-- @@ L320-323 verbatim
set_option maxHeartbeats 1000000 in
theorem Tinv'_comp_T' (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    (Tinv' B).comp (T' B) = TwoSuperfunctor.id R B :=
  QAssociated2.Tinv_comp_T


-- @@ L325-327 verbatim
set_option maxHeartbeats 1000000 in
theorem T'_isGraded (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) : (T' B).IsGraded :=
  QAssociated2.T_isGraded


-- @@ L329-331 verbatim
set_option maxHeartbeats 1000000 in
theorem Tinv'_isGraded (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) : (Tinv' B).IsGraded :=
  QAssociated2.Tinv_isGraded


-- @@ L333-336 verbatim
/-- The component `𝕋_𝔅 : 𝔻(𝔼 𝔅) → 𝔅` of the counit. -/
def counitHom (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    QPiTwoCat.toQPiTwoGSCat.obj (toQPiTwoCat.obj B) ⟶ B :=
  ⟨T' B, T'_isGraded B⟩


-- @@ L338-341 verbatim
/-- The inverse `𝕋_𝔅⁻¹ : 𝔅 → 𝔻(𝔼 𝔅)` of the component of the counit. -/
def counitInv (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    B ⟶ QPiTwoCat.toQPiTwoGSCat.obj (toQPiTwoCat.obj B) :=
  ⟨Tinv' B, Tinv'_isGraded B⟩


-- @@ L343-350 verbatim
/-- `𝔻(𝔼 ℝ)` is `𝔻` of the `(Q, Π)`-2-functor underlying `ℝ`. -/
theorem mapQ_eq {B C : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (G : B ⟶ C) :
    ((toQPiTwoCat.map G).toQPiTwoFunctor.mapQ :
        TwoSuperfunctor R (QAssociated2 R (toQPiTwoCat.obj B))
          (QAssociated2 R (toQPiTwoCat.obj C))) =
      ((G.1.toQPiTwoFunctor G.2).mapQ : TwoSuperfunctor R (QAssociated2 R (toQPiTwoCat.obj B))
        (QAssociated2 R (toQPiTwoCat.obj C))) :=
  rfl


-- @@ L352-355 verbatim
theorem mapQ_comp_T'' {B C : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (G : B ⟶ C) :
    ((toQPiTwoCat.map G).toQPiTwoFunctor.mapQ).comp (T' C) = (T' B).comp G.1 := by
  rw [mapQ_eq]
  exact mapQ_comp_T' G


-- @@ L357-363 verbatim
/-- **Naturality of `𝕋`** in `(Q, Π)-2-GSCat`: `𝔻(𝔼 ℝ) ≫ 𝕋_𝔅' = 𝕋_𝔅 ≫ ℝ`
(`QAssociated2.mapQ_comp_T`). -/
theorem counit_naturality {B C : QPiTwoGSCat.{w, w₁, v₁, u₁} R} (G : B ⟶ C) :
    QPiTwoCat.toQPiTwoGSCat.map (toQPiTwoCat.map G) ≫ counitHom C = counitHom B ≫ G := by
  apply Subtype.ext
  rw [QPiTwoGSCat.comp_val, QPiTwoGSCat.comp_val, QPiTwoCat.toQPiTwoGSCat_map]
  exact mapQ_comp_T'' G


-- @@ L365-368 verbatim
theorem counitHom_comp_counitInv (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    counitHom B ≫ counitInv B = 𝟙 _ := by
  apply Subtype.ext
  exact T'_comp_Tinv' B


-- @@ L370-373 verbatim
theorem counitInv_comp_counitHom (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    counitInv B ≫ counitHom B = 𝟙 _ := by
  apply Subtype.ext
  exact Tinv'_comp_T' B


-- @@ L375-381 verbatim
/-- **The §6 analogue of Lemma 5.4, `𝔻 ∘ 𝔼 ≅ I` on objects**: `𝕋_𝔅 : 𝔻(𝔼 𝔅) ≅ 𝔅`. -/
def counitIso (B : QPiTwoGSCat.{w, w₁, v₁, u₁} R) :
    (toQPiTwoCat ⋙ QPiTwoCat.toQPiTwoGSCat).obj B ≅ B where
  hom := counitHom B
  inv := counitInv B
  hom_inv_id := counitHom_comp_counitInv B
  inv_hom_id := counitInv_comp_counitHom B


-- @@ L383-387 verbatim
/-- **The §6 analogue of Lemma 5.4, `𝔻 ∘ 𝔼 ≅ I`**, as a natural isomorphism `𝔼 ⋙ 𝔻 ≅ 𝟭` of
endofunctors of `(Q, Π)-2-GSCat`, with components `𝕋`. -/
def counitNatIso :
    toQPiTwoCat ⋙ QPiTwoCat.toQPiTwoGSCat ≅ 𝟭 (QPiTwoGSCat.{w, w₁, v₁, u₁} R) :=
  NatIso.ofComponents counitIso fun G => counit_naturality G


-- @@ L389-389 verbatim
end QPiTwoGSCat


-- @@ L391-391 verbatim
namespace QPiTwoCat


-- @@ L393-393 verbatim
variable {R : Type w} [CommRing R]


-- @@ L395-401 verbatim
/-- **The §6 analogue of Lemma 5.4** (after Definition 6.14). `𝔻 : (Q, Π)-2-Cat → (Q, Π)-2-GSCat`
and `𝔼 : (Q, Π)-2-GSCat → (Q, Π)-2-Cat` are mutually inverse equivalences of categories, with
unit `𝔼 ∘ 𝔻 = I` (`QPiTwoCat.unitNatIso`) and counit `𝕋 : 𝔻 ∘ 𝔼 ≅ I`
(`QPiTwoGSCat.counitNatIso`). -/
def equivalence : QPiTwoCat.{w, w₁, v₁, u₁} R ≌ QPiTwoGSCat.{w, w₁, v₁, u₁} R :=
  CategoryTheory.Equivalence.mk toQPiTwoGSCat QPiTwoGSCat.toQPiTwoCat unitNatIso
    QPiTwoGSCat.counitNatIso


-- @@ L403-404 verbatim
instance : (toQPiTwoGSCat : QPiTwoCat.{w, w₁, v₁, u₁} R ⥤ _).IsEquivalence :=
  equivalence.isEquivalence_functor


-- @@ L406-407 verbatim
instance : (QPiTwoGSCat.toQPiTwoCat : QPiTwoGSCat.{w, w₁, v₁, u₁} R ⥤ _).IsEquivalence :=
  equivalence.isEquivalence_inverse


-- @@ L409-409 verbatim
end QPiTwoCat


-- @@ L411-411 verbatim
end StringDiagrams
