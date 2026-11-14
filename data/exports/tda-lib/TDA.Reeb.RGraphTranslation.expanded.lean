import TDA.Reeb.ConstructiblePerturbation
import TDA.Reeb.IntervalTranslation
import TDA.Reeb.RGraphSmoothing


-- @@ L5-43 verbatim
/-!
# Vertical translation of finite ℝ-graphs

For `c : ℝ`, vertical translation of the real slice is `translateOver c = Over.map (· + c)`: it
keeps the total space of an object and replaces its height `f` by `f + c`
(`overBaseMap_translateOver`). It satisfies `translateOver 0 ≅ 𝟭` and
`translateOver c ⋙ translateOver d ≅ translateOver (c + d)`.

## Graph objects

On a finite realization the translate is again a finite realization: the change of levels
`levelHomeomorph S (S.translate c)` of the same finite data carries `height S` to
`height (S.translate c) - c` (`height_levelMap_translate`), so
`(translateOver c).obj (toOver S D) ≅ toOver (S.translate c) D` (`toOverTranslateIso`).
Hence translation preserves `IsRGraph` and restricts to `translateRGraph c : RGraphCat ⥤ RGraphCat`,
with `translateRGraph 0 ≅ 𝟭` and `translateRGraph c ⋙ translateRGraph d ≅ translateRGraph (c + d)`.

## Distance

The component cosheaf of the translate is the translate `translatePre c` of the component cosheaf,
by definition (`cosheafFunctor_translateRGraph_obj`). Every `ε`-interleaving of interval
precosheaves into an arbitrary category transports to their translates (`Interleaving.translatePre`),
so `translatePre c` preserves the interleaving distance (`interleavingDistance_translatePre`) and
`translateRGraph c` preserves the geometric interleaving distance
(`geometricInterleavingDistance_translateRGraph`). A graph object with nonempty total space is at
geometric interleaving distance exactly `|c|` from its translate by `c`
(`geometricInterleavingDistance_translateRGraph_self`); with empty total space the distance is `0`.

## Reeb quotient and smoothing

A height and its translate have the same Reeb relation (`reebRel_add_const_iff`), so the Reeb
quotient functor commutes with translation (`quotientTranslateIso`). The product thickening commutes
with translation by the identity of `X × [-ε, ε]` (`thickeningTranslateIso`), and therefore so does
the geometric smoothing of graph objects (`geometricSmoothingTranslateIso`).

These are library statements. De Silva–Munch–Patel, §4.1–4.4, is the context; no numbered result of
theirs states translation equivariance. Translation is the only reparametrization of heights
treated here; scaling and other affine maps are not. See `docs/math/reeb-rgraph-translation.md`.
-/


-- @@ L45-45 verbatim
open Set Topology CategoryTheory

-- @@ L46-46 verbatim
open scoped NNReal ENNReal


-- @@ L48-48 verbatim
universe v u


-- @@ L50-50 verbatim
namespace TDA.Reeb


-- @@ L52-52 verbatim
noncomputable section


-- @@ L54-54 verbatim
open OpenInterval


-- @@ L56-56 verbatim
/-! ### Transport of interleavings -/


-- @@ L58-58 verbatim
section Interleaving


-- @@ L60-60 verbatim
variable {C : Type u} [Category.{v} C]


-- @@ L62-62 verbatim
namespace Interleaving


-- @@ L64-64 verbatim
variable {ε : ℝ≥0} {F G : OpenInterval ⥤ C}


-- @@ L66-92 expanded
/-- An `ε`-interleaving of `F` and `G` gives an `ε`-interleaving of their translates by `c`, with
components `φ_(I - c)` and `ψ_(I - c)` followed by `T_ε (I - c) = T_ε I - c`. -/
def translatePre (c : ℝ) (i : Interleaving ε F G) :
    Interleaving ε (TDA.Reeb.translatePre c F) (TDA.Reeb.translatePre c G) :=
  ofApp
    { app := fun I => i.φ.app (translate c I) ≫ G.map (homOfLE (translate_thicken c ε I).ge)
      naturality := fun I J f => by
        dsimp
        erw [reassoc_of% (i.φ.naturality ((translateFunctor c).map f))]
        refine Eq.trans ?_ (Category.assoc _ _ _).symm
        congr 1
        first
        | exact map_eq_map_of_interval _ _ _
        | exact map_comp2_eq_comp2_of_interval _ _ _ _ _
        | exact map_comp3_eq_comp2_of_interval _ _ _ _ _ _
        | exact map_comp_map_of_interval _ _ _ _
        | exact map_comp_map_comp_map_of_interval _ _ _ _ _
        | exact map_comp4_of_interval _ _ _ _ _ _
        | exact map_comp5_of_interval _ _ _ _ _ _ _
        | exact map_comp6_of_interval _ _ _ _ _ _ _ _
        | exact (map_eq_map_of_interval _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
        | exact (map_comp_map_of_interval _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
        |
          exact
            (map_comp_map_comp_map_of_interval _ _ _ _ (𝟙 _)).trans
              (CategoryTheory.Functor.map_id _ _)
        |
          exact
            (map_comp6_of_interval _ _ _ _ _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _) }
    { app := fun I => i.ψ.app (translate c I) ≫ F.map (homOfLE (translate_thicken c ε I).ge)
      naturality := fun I J f => by
        dsimp
        erw [reassoc_of% (i.ψ.naturality ((translateFunctor c).map f))]
        refine Eq.trans ?_ (Category.assoc _ _ _).symm
        congr 1
        first
        | exact map_eq_map_of_interval _ _ _
        | exact map_comp2_eq_comp2_of_interval _ _ _ _ _
        | exact map_comp3_eq_comp2_of_interval _ _ _ _ _ _
        | exact map_comp_map_of_interval _ _ _ _
        | exact map_comp_map_comp_map_of_interval _ _ _ _ _
        | exact map_comp4_of_interval _ _ _ _ _ _
        | exact map_comp5_of_interval _ _ _ _ _ _ _
        | exact map_comp6_of_interval _ _ _ _ _ _ _ _
        | exact (map_eq_map_of_interval _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
        | exact (map_comp_map_of_interval _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
        |
          exact
            (map_comp_map_comp_map_of_interval _ _ _ _ (𝟙 _)).trans
              (CategoryTheory.Functor.map_id _ _)
        |
          exact
            (map_comp6_of_interval _ _ _ _ _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _) }
    (fun I => by
      dsimp
      rw [Category.assoc, i.φ_map_ψ_assoc]
      first
      | exact map_eq_map_of_interval _ _ _
      | exact map_comp2_eq_comp2_of_interval _ _ _ _ _
      | exact map_comp3_eq_comp2_of_interval _ _ _ _ _ _
      | exact map_comp_map_of_interval _ _ _ _
      | exact map_comp_map_comp_map_of_interval _ _ _ _ _
      | exact map_comp4_of_interval _ _ _ _ _ _
      | exact map_comp5_of_interval _ _ _ _ _ _ _
      | exact map_comp6_of_interval _ _ _ _ _ _ _ _
      | exact (map_eq_map_of_interval _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
      | exact (map_comp_map_of_interval _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
      |
        exact
          (map_comp_map_comp_map_of_interval _ _ _ _ (𝟙 _)).trans
            (CategoryTheory.Functor.map_id _ _)
      | exact (map_comp6_of_interval _ _ _ _ _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _))
    (fun I => by
      dsimp
      rw [Category.assoc, i.ψ_map_φ_assoc]
      first
      | exact map_eq_map_of_interval _ _ _
      | exact map_comp2_eq_comp2_of_interval _ _ _ _ _
      | exact map_comp3_eq_comp2_of_interval _ _ _ _ _ _
      | exact map_comp_map_of_interval _ _ _ _
      | exact map_comp_map_comp_map_of_interval _ _ _ _ _
      | exact map_comp4_of_interval _ _ _ _ _ _
      | exact map_comp5_of_interval _ _ _ _ _ _ _
      | exact map_comp6_of_interval _ _ _ _ _ _ _ _
      | exact (map_eq_map_of_interval _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
      | exact (map_comp_map_of_interval _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
      |
        exact
          (map_comp_map_comp_map_of_interval _ _ _ _ (𝟙 _)).trans
            (CategoryTheory.Functor.map_id _ _)
      | exact (map_comp6_of_interval _ _ _ _ _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _))


-- @@ L94-94 verbatim
end Interleaving


-- @@ L96-101 expanded
/-- Translating by `c` and then by `d` is translating by `d + c`. -/
private def translatePreTranslatePreIso (c d : ℝ) (F : OpenInterval ⥤ C) :
    translatePre c (translatePre d F) ≅ translatePre (d + c) F :=
  NatIso.ofComponents (fun I => F.mapIso (eqToIso (translate_translate d c I))) fun _ =>
    by
    simp only [translatePre_map, Functor.mapIso_hom]
    first
    | exact map_eq_map_of_interval _ _ _
    | exact map_comp2_eq_comp2_of_interval _ _ _ _ _
    | exact map_comp3_eq_comp2_of_interval _ _ _ _ _ _
    | exact map_comp_map_of_interval _ _ _ _
    | exact map_comp_map_comp_map_of_interval _ _ _ _ _
    | exact map_comp4_of_interval _ _ _ _ _ _
    | exact map_comp5_of_interval _ _ _ _ _ _ _
    | exact map_comp6_of_interval _ _ _ _ _ _ _ _
    | exact (map_eq_map_of_interval _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
    | exact (map_comp_map_of_interval _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
    |
      exact
        (map_comp_map_comp_map_of_interval _ _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)
    | exact (map_comp6_of_interval _ _ _ _ _ _ _ (𝟙 _)).trans (CategoryTheory.Functor.map_id _ _)


-- @@ L103-114 verbatim
/-- Translation preserves the interleaving distance of precosheaves into any category. -/
theorem interleavingDistance_translatePre (c : ℝ) (F G : OpenInterval ⥤ C) :
    interleavingDistance (translatePre c F) (translatePre c G) = interleavingDistance F G := by
  have key : ∀ (d : ℝ) (F G : OpenInterval ⥤ C),
      interleavingDistance (translatePre d F) (translatePre d G) ≤ interleavingDistance F G :=
    fun d _ _ => le_iInf₂ fun _ ⟨i⟩ => (i.translatePre d).interleavingDistance_le
  refine le_antisymm (key c F G) ?_
  have e : ∀ H : OpenInterval ⥤ C, translatePre (-c) (translatePre c H) ≅ H := fun H =>
    translatePreTranslatePreIso (-c) c H ≪≫ eqToIso (by rw [add_neg_cancel]) ≪≫
      translatePreZeroIso H
  rw [← interleavingDistance_congr (e F) (e G)]
  exact key (-c) _ _


-- @@ L116-116 verbatim
end Interleaving


-- @@ L118-118 verbatim
/-! ### The Reeb relation of a translated height -/


-- @@ L120-120 verbatim
section Reeb


-- @@ L122-122 verbatim
variable {X : Type u} [TopologicalSpace X]


-- @@ L124-129 verbatim
/-- A height and its translate by `c` have the same Reeb relation. -/
theorem reebRel_add_const_iff (f : C(X, ℝ)) (c : ℝ) (x x' : X) :
    ReebRel (f + ContinuousMap.const X c) x x' ↔ ReebRel f x x' := by
  constructor <;> rintro ⟨γ, hγ⟩ <;> refine ⟨γ, fun t => ?_⟩
  · simpa using hγ t
  · simp [hγ t]


-- @@ L131-135 verbatim
/-- The Reeb quotients of a height and of its translate are homeomorphic, by the identity on
representatives. -/
def ReebQuotient.addConstHomeomorph (f : C(X, ℝ)) (c : ℝ) :
    ReebQuotient (f + ContinuousMap.const X c) ≃ₜ ReebQuotient f :=
  Homeomorph.Quotient.congrRight fun x x' => reebRel_add_const_iff f c x x'


-- @@ L137-139 verbatim
@[simp] theorem ReebQuotient.addConstHomeomorph_mk (f : C(X, ℝ)) (c : ℝ) (x : X) :
    ReebQuotient.addConstHomeomorph f c (ReebQuotient.mk _ x) = ReebQuotient.mk f x :=
  rfl


-- @@ L141-141 verbatim
end Reeb


-- @@ L143-143 verbatim
namespace RGraph


-- @@ L145-145 verbatim
/-! ### Translation of the real slice -/


-- @@ L147-149 verbatim
/-- Vertical translation `x ↦ x + c` of the real line, as a morphism of spaces. -/
abbrev addConstHom (c : ℝ) : TopCat.of ℝ ⟶ TopCat.of ℝ :=
  TopCat.ofHom ⟨(· + c), continuous_add_const c⟩


-- @@ L151-154 verbatim
/-- Vertical translation of the real slice: the total space is kept and the height `f` becomes
`f + c`. -/
def translateOver (c : ℝ) : Over (TopCat.of ℝ) ⥤ Over (TopCat.of ℝ) :=
  Over.map (addConstHom c)


-- @@ L156-158 verbatim
theorem translateOver_obj_left (c : ℝ) (A : Over (TopCat.of ℝ)) :
    ((translateOver c).obj A).left = A.left :=
  rfl


-- @@ L160-162 verbatim
theorem translateOver_map_left {c : ℝ} {A B : Over (TopCat.of ℝ)} (φ : A ⟶ B) :
    ((translateOver c).map φ).left = φ.left :=
  rfl


-- @@ L164-167 verbatim
/-- The height of the translate is the translated height. -/
theorem overBaseMap_translateOver (c : ℝ) (A : Over (TopCat.of ℝ)) :
    overBaseMap ((translateOver c).obj A) = overBaseMap A + ContinuousMap.const A.left c :=
  rfl


-- @@ L169-171 verbatim
/-- Translation by `0` is the identity of the real slice. -/
def translateOverZeroIso : translateOver 0 ≅ 𝟭 (Over (TopCat.of ℝ)) :=
  Over.mapCongr _ _ (by ext x; simp) ≪≫ Over.mapId _


-- @@ L173-176 verbatim
/-- Translating by `c` and then by `d` is translating by `c + d`. -/
def translateOverCompIso (c d : ℝ) :
    translateOver c ⋙ translateOver d ≅ translateOver (c + d) :=
  (Over.mapComp _ _).symm ≪≫ Over.mapCongr _ _ (by ext x; simp [add_assoc])


-- @@ L178-178 verbatim
/-! ### Graph objects -/


-- @@ L180-191 verbatim
/-- The translate by `c` of a finite realization at the levels `S` is the realization of the same
finite data at the translated levels `S.translate c`. -/
def toOverTranslateIso {n : ℕ} (S : CriticalValues n) (D : FiniteReebData.{0} n) (c : ℝ) :
    (translateOver c).obj (toOver S D) ≅ toOver (S.translate c) D :=
  Over.isoMk
    (TopCat.isoOfHomeo
      (X := ((translateOver c).obj (toOver S D)).left)
      (Y := TopCat.of ((CylinderPresentation.ofFiniteData D).Realization (S.translate c)))
      ((CylinderPresentation.ofFiniteData D).levelHomeomorph S (S.translate c)))
    (by
      ext q
      exact (CylinderPresentation.ofFiniteData D).height_levelMap_translate S c q)


-- @@ L193-197 verbatim
/-- Translation preserves graph objects. -/
theorem isRGraph_translateOver {A : Over (TopCat.of ℝ)} (hA : IsRGraph A) (c : ℝ) :
    IsRGraph ((translateOver c).obj A) := by
  obtain ⟨m, T, D, ⟨i⟩⟩ := hA
  exact ⟨m, T.translate c, D, ⟨(translateOver c).mapIso i ≪≫ toOverTranslateIso T D c⟩⟩


-- @@ L199-201 verbatim
/-- Vertical translation of graph objects. -/
def translateRGraph (c : ℝ) : RGraphCat ⥤ RGraphCat :=
  IsRGraph.lift (IsRGraph.ι ⋙ translateOver c) fun A => isRGraph_translateOver A.property c


-- @@ L203-205 verbatim
theorem translateRGraph_comp_ι (c : ℝ) :
    translateRGraph c ⋙ IsRGraph.ι = IsRGraph.ι ⋙ translateOver c :=
  rfl


-- @@ L207-209 verbatim
theorem translateRGraph_obj_obj (c : ℝ) (A : RGraphCat) :
    ((translateRGraph c).obj A).obj = (translateOver c).obj A.obj :=
  rfl


-- @@ L211-213 verbatim
theorem translateRGraph_map_hom (c : ℝ) {A B : RGraphCat} (φ : A ⟶ B) :
    ((translateRGraph c).map φ).hom = (translateOver c).map φ.hom :=
  rfl


-- @@ L215-219 verbatim
/-- Translation of graph objects by `0` is the identity. -/
def translateRGraphZeroIso : translateRGraph 0 ≅ 𝟭 RGraphCat :=
  NatIso.ofComponents (fun A => IsRGraph.isoMk (translateOverZeroIso.app A.obj)) fun φ => by
    ext1
    exact translateOverZeroIso.hom.naturality φ.hom


-- @@ L221-226 verbatim
/-- Translating graph objects by `c` and then by `d` is translating by `c + d`. -/
def translateRGraphCompIso (c d : ℝ) :
    translateRGraph c ⋙ translateRGraph d ≅ translateRGraph (c + d) :=
  NatIso.ofComponents (fun A => IsRGraph.isoMk ((translateOverCompIso c d).app A.obj)) fun φ => by
    ext1
    exact (translateOverCompIso c d).hom.naturality φ.hom


-- @@ L228-228 verbatim
/-! ### Component cosheaves and distance -/


-- @@ L230-234 verbatim
/-- The component cosheaf of the translate is the translate of the component cosheaf. -/
theorem cosheafFunctor_translateRGraph_obj (c : ℝ) (A : RGraphCat) :
    (cosheafFunctor.obj ((translateRGraph c).obj A)).obj =
      translatePre c (cosheafFunctor.obj A).obj :=
  rfl


-- @@ L236-242 verbatim
/-- **Translation is an isometry** of the geometric interleaving distance. -/
theorem geometricInterleavingDistance_translateRGraph (c : ℝ) (A B : RGraphCat) :
    geometricInterleavingDistance ((translateRGraph c).obj A) ((translateRGraph c).obj B) =
      geometricInterleavingDistance A B := by
  rw [geometricInterleavingDistance_eq_interleavingDistance,
    geometricInterleavingDistance_eq_interleavingDistance, cosheafFunctor_translateRGraph_obj,
    cosheafFunctor_translateRGraph_obj, interleavingDistance_translatePre]


-- @@ L244-245 verbatim
private theorem coe_nnnorm_eq_ofReal_abs (c : ℝ) : ((‖c‖₊ : ℝ≥0) : ℝ≥0∞) = ENNReal.ofReal |c| :=
  Real.enorm_eq_ofReal_abs c


-- @@ L247-252 verbatim
/-- A graph object is within `|c|` of its translate by `c`. -/
theorem geometricInterleavingDistance_translateRGraph_self_le (A : RGraphCat) (c : ℝ) :
    geometricInterleavingDistance A ((translateRGraph c).obj A) ≤ ENNReal.ofReal |c| := by
  rw [geometricInterleavingDistance_eq_interleavingDistance, cosheafFunctor_translateRGraph_obj,
    ← coe_nnnorm_eq_ofReal_abs]
  exact interleavingDistance_translatePre_le c _


-- @@ L254-263 verbatim
/-- **Exact self-translation distance.** A graph object with nonempty total space is at geometric
interleaving distance exactly `|c|` from its translate by `c`. -/
theorem geometricInterleavingDistance_translateRGraph_self (A : RGraphCat)
    (hA : Nonempty A.obj.left) (c : ℝ) :
    geometricInterleavingDistance A ((translateRGraph c).obj A) = ENNReal.ofReal |c| := by
  rw [geometricInterleavingDistance_eq_interleavingDistance, cosheafFunctor_obj_obj,
    cosheafFunctor_obj_obj, translateRGraph_obj_obj, overBaseMap_translateOver]
  have := hA
  exact (interleavingDistance_intervalComponents_add_const (overBaseMap A.obj)
    (bddBelow_heightRange A) c).trans (coe_nnnorm_eq_ofReal_abs c)


-- @@ L265-269 verbatim
/-- A graph object with empty total space is at distance `0` from each of its translates. -/
theorem geometricInterleavingDistance_translateRGraph_self_of_isEmpty (A : RGraphCat)
    (hA : IsEmpty A.obj.left) (c : ℝ) :
    geometricInterleavingDistance A ((translateRGraph c).obj A) = 0 :=
  geometricInterleavingDistance_eq_zero_of_isEmpty hA hA


-- @@ L271-276 verbatim
/-- Translating the second argument by `c` increases the distance by at most `|c|`. -/
theorem geometricInterleavingDistance_translateRGraph_le (A B : RGraphCat) (c : ℝ) :
    geometricInterleavingDistance A ((translateRGraph c).obj B) ≤
      geometricInterleavingDistance A B + ENNReal.ofReal |c| :=
  (geometricInterleavingDistance_triangle A B _).trans
    (add_le_add le_rfl (geometricInterleavingDistance_translateRGraph_self_le B c))


-- @@ L278-284 verbatim
/-- Translating the second argument by `c` decreases the distance by at most `|c|`. -/
theorem geometricInterleavingDistance_le_translateRGraph_add (A B : RGraphCat) (c : ℝ) :
    geometricInterleavingDistance A B ≤
      geometricInterleavingDistance A ((translateRGraph c).obj B) + ENNReal.ofReal |c| := by
  refine (geometricInterleavingDistance_triangle A ((translateRGraph c).obj B) B).trans ?_
  rw [geometricInterleavingDistance_comm ((translateRGraph c).obj B) B]
  exact add_le_add le_rfl (geometricInterleavingDistance_translateRGraph_self_le B c)


-- @@ L286-286 verbatim
/-! ### Reeb quotient and smoothing -/


-- @@ L288-306 verbatim
/-- The Reeb quotient functor commutes with translation: the Reeb quotients of `f + c` and `f` are
identified by the identity on representatives. -/
def quotientTranslateIso (c : ℝ) :
    translateOver c ⋙ ReebQuotient.quotientFunctor ℝ ≅
      ReebQuotient.quotientFunctor ℝ ⋙ translateOver c :=
  NatIso.ofComponents
    (fun A => Over.isoMk
      (TopCat.isoOfHomeo
        (X := ((ReebQuotient.quotientFunctor ℝ).obj ((translateOver c).obj A)).left)
        (Y := ((translateOver c).obj ((ReebQuotient.quotientFunctor ℝ).obj A)).left)
        (ReebQuotient.addConstHomeomorph (overBaseMap A) c))
      (by
        ext q
        induction q using ReebQuotient.ind with
        | h x => rfl))
    fun φ => by
      ext q
      induction q using ReebQuotient.ind with
      | h x => rfl


-- @@ L308-319 verbatim
/-- The product thickening commutes with translation, by the identity of `X × [-ε, ε]`: the heights
`(f x + c) + t` and `(f x + t) + c` agree. -/
def thickeningTranslateIso (c : ℝ) (ε : ℝ≥0) :
    translateOver c ⋙ GeometricThickening.functor ε ≅
      GeometricThickening.functor ε ⋙ translateOver c :=
  NatIso.ofComponents
    (fun A => Over.isoMk (Iso.refl _) (by
      ext z
      exact add_right_comm (overBaseMap A z.1) (z.2 : ℝ) c))
    fun φ => by
      ext z
      rfl


-- @@ L321-330 verbatim
/-- **Geometric smoothing commutes with translation** of graph objects. -/
def geometricSmoothingTranslateIso (c : ℝ) (ε : ℝ≥0) :
    translateRGraph c ⋙ geometricSmoothing ε ≅ geometricSmoothing ε ⋙ translateRGraph c :=
  let e : translateOver c ⋙ GeometricThickening.functor ε ⋙ ReebQuotient.quotientFunctor ℝ ≅
      GeometricThickening.functor ε ⋙ ReebQuotient.quotientFunctor ℝ ⋙ translateOver c :=
    Functor.isoWhiskerRight (thickeningTranslateIso c ε) (ReebQuotient.quotientFunctor ℝ) ≪≫
      Functor.isoWhiskerLeft (GeometricThickening.functor ε) (quotientTranslateIso c)
  NatIso.ofComponents (fun A => IsRGraph.isoMk (e.app A.obj)) fun φ => by
    ext1
    exact e.hom.naturality φ.hom


-- @@ L332-332 verbatim
end RGraph


-- @@ L334-334 verbatim
end


-- @@ L336-336 verbatim
end TDA.Reeb
