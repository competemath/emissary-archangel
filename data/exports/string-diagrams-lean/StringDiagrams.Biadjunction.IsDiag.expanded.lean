import StringDiagrams.Biadjunction.Zigzag


-- @@ L3-21 verbatim
/-!
# 2-morphisms with prescribed layers

For a presentation `P` of an even signature, a 2-morphism `θ : x ⟶ y` of the presented
bicategory `P.Bicat` *is the class of a diagram with the layers `ls`* (`Presentation.IsDiag P θ ls`)
if `θ = P.diag d` for some diagram `d : x.obj ⟶ y.obj` with `Diagram.layers d = ls`.

Lists of layers are the natural currency for computations with composites of units, counits,
whiskerings and coherence isomorphisms: the predicate is closed under composition
(concatenation of layers, `IsDiag.comp`) and whiskering (`IsDiag.whiskerLeft`,
`IsDiag.whiskerRight`), identities, `eqToHom`s, associators and unitors have no layers
(`isDiag_id`, `isDiag_eqToHom`, `isDiag_associator_hom`, …), and two 2-morphisms with the same
layers are equal up to the identification of their boundaries (`IsDiag.eq_eqToHom`,
`IsDiag.eq`).

The tactic `isdiag_triv` proves `IsDiag P θ []` for `θ` built from identities, `eqToHom`s,
associators and unitors by composition and whiskering (in particular for the coherence
2-morphisms of `⊗≫`).
-/


-- @@ L23-23 verbatim
noncomputable section


-- @@ L25-25 verbatim
namespace StringDiagrams


-- @@ L27-27 verbatim
open CategoryTheory Bicategory


-- @@ L29-29 verbatim
universe w v u₀ u₁ u₂


-- @@ L31-31 verbatim
variable {S : Signature.{u₀, u₁, u₂}} {R : Type w} [CommRing R]


-- @@ L33-33 verbatim
namespace Presentation


-- @@ L35-35 verbatim
variable (P : Presentation.{w, v} S R) [S.IsEven] {l m n : P.Bicat}


-- @@ L37-39 verbatim
/-- The 2-morphism `θ` of `P.Bicat` is the class of a diagram with the layers `ls`. -/
def IsDiag {x y : l ⟶ m} (θ : x ⟶ y) (ls : List (Layer S)) : Prop :=
  ∃ d : x.obj ⟶ y.obj, θ = P.diag d ∧ Diagram.layers d = ls


-- @@ L41-41 verbatim
variable {P}


-- @@ L43-45 verbatim
theorem isDiag_diag {x y : l ⟶ m} (d : x.obj ⟶ y.obj) :
    IsDiag P (P.diag d : x ⟶ y) (Diagram.layers d) :=
  ⟨d, rfl, rfl⟩


-- @@ L47-48 verbatim
theorem IsDiag.congr {x y : l ⟶ m} {θ : x ⟶ y} {ls ls' : List (Layer S)} (h : IsDiag P θ ls)
    (e : ls = ls') : IsDiag P θ ls' := e ▸ h


-- @@ L50-51 verbatim
theorem IsDiag.of_eq {x y : l ⟶ m} {θ θ' : x ⟶ y} {ls : List (Layer S)} (h : IsDiag P θ ls)
    (e : θ = θ') : IsDiag P θ' ls := e ▸ h


-- @@ L53-57 verbatim
theorem IsDiag.comp {x y z : l ⟶ m} {θ : x ⟶ y} {θ' : y ⟶ z} {ls ls' : List (Layer S)}
    (h : IsDiag P θ ls) (h' : IsDiag P θ' ls') : IsDiag P (θ ≫ θ') (ls ++ ls') := by
  obtain ⟨d, rfl, rfl⟩ := h
  obtain ⟨d', rfl, rfl⟩ := h'
  exact ⟨d ≫ d', (P.diag_comp d d').symm, rfl⟩


-- @@ L59-59 verbatim
theorem isDiag_id (x : l ⟶ m) : IsDiag P (𝟙 x) [] := ⟨𝟙 x.obj, (P.diag_id _).symm, rfl⟩


-- @@ L61-62 verbatim
theorem isDiag_eqToHom {x y : l ⟶ m} (h : x = y) : IsDiag P (eqToHom h) [] := by
  subst h; exact isDiag_id x


-- @@ L64-68 verbatim
theorem IsDiag.whiskerLeft (f : l ⟶ m) {x y : m ⟶ n} {θ : x ⟶ y} {ls : List (Layer S)}
    (h : IsDiag P θ ls) : IsDiag P (f ◁ θ) (ls.map (·.wl f.obj)) := by
  obtain ⟨d, rfl, rfl⟩ := h
  exact ⟨Diagram.lwhisker f.obj d (Bicat.Hom.composable f x),
    P.wL_diag_of_composable _ _ (Bicat.Hom.composable f x), rfl⟩


-- @@ L70-74 verbatim
theorem IsDiag.whiskerRight {x y : l ⟶ m} (g : m ⟶ n) {θ : x ⟶ y} {ls : List (Layer S)}
    (h : IsDiag P θ ls) : IsDiag P (θ ▷ g) (ls.map (·.wr g.obj.word)) := by
  obtain ⟨d, rfl, rfl⟩ := h
  exact ⟨Diagram.rwhisker d g.obj (Bicat.Hom.composable x g),
    P.wRAt_diag d _ (Bicat.Hom.composable x g) _ _, rfl⟩


-- @@ L76-78 verbatim
theorem isDiag_associator_hom {k : P.Bicat} (f : l ⟶ m) (g : m ⟶ n) (h : n ⟶ k) :
    IsDiag P (α_ f g h).hom [] := by
  rw [Strict.associator_eqToIso, eqToIso.hom]; exact isDiag_eqToHom _


-- @@ L80-82 verbatim
theorem isDiag_associator_inv {k : P.Bicat} (f : l ⟶ m) (g : m ⟶ n) (h : n ⟶ k) :
    IsDiag P (α_ f g h).inv [] := by
  rw [Strict.associator_eqToIso, eqToIso.inv]; exact isDiag_eqToHom _


-- @@ L84-85 verbatim
theorem isDiag_leftUnitor_hom (f : l ⟶ m) : IsDiag P (λ_ f).hom [] := by
  rw [Strict.leftUnitor_eqToIso, eqToIso.hom]; exact isDiag_eqToHom _


-- @@ L87-88 verbatim
theorem isDiag_leftUnitor_inv (f : l ⟶ m) : IsDiag P (λ_ f).inv [] := by
  rw [Strict.leftUnitor_eqToIso, eqToIso.inv]; exact isDiag_eqToHom _


-- @@ L90-91 verbatim
theorem isDiag_rightUnitor_hom (f : l ⟶ m) : IsDiag P (ρ_ f).hom [] := by
  rw [Strict.rightUnitor_eqToIso, eqToIso.hom]; exact isDiag_eqToHom _


-- @@ L93-94 verbatim
theorem isDiag_rightUnitor_inv (f : l ⟶ m) : IsDiag P (ρ_ f).inv [] := by
  rw [Strict.rightUnitor_eqToIso, eqToIso.inv]; exact isDiag_eqToHom _


-- @@ L96-98 verbatim
theorem isDiag_comp_nil {x y z : l ⟶ m} {θ : x ⟶ y} {θ' : y ⟶ z}
    (h : IsDiag P θ []) (h' : IsDiag P θ' []) : IsDiag P (θ ≫ θ') [] :=
  (h.comp h').congr rfl


-- @@ L100-102 verbatim
theorem isDiag_whiskerLeft_nil (f : l ⟶ m) {x y : m ⟶ n} {θ : x ⟶ y}
    (h : IsDiag P θ []) : IsDiag P (f ◁ θ) [] :=
  (h.whiskerLeft f).congr rfl


-- @@ L104-106 verbatim
theorem isDiag_whiskerRight_nil {x y : l ⟶ m} (g : m ⟶ n) {θ : x ⟶ y}
    (h : IsDiag P θ []) : IsDiag P (θ ▷ g) [] :=
  (h.whiskerRight g).congr rfl


-- @@ L108-110 verbatim
theorem IsDiag.eqToHom_comp {x y z : l ⟶ m} (h : x = y) {θ : y ⟶ z} {ls : List (Layer S)}
    (hθ : IsDiag P θ ls) : IsDiag P (eqToHom h ≫ θ) ls :=
  ((isDiag_eqToHom h).comp hθ).congr rfl


-- @@ L112-114 verbatim
theorem IsDiag.comp_eqToHom {x y z : l ⟶ m} {θ : x ⟶ y} (h : y = z) {ls : List (Layer S)}
    (hθ : IsDiag P θ ls) : IsDiag P (θ ≫ eqToHom h) ls :=
  (hθ.comp (isDiag_eqToHom h)).congr (List.append_nil _)


-- @@ L116-125 verbatim
/-- Two 2-morphisms that are classes of diagrams with the same layers agree, up to the
identification of their boundaries. -/
theorem IsDiag.eq_eqToHom {x y x' y' : l ⟶ m} {θ : x ⟶ y} {θ' : x' ⟶ y'} {ls : List (Layer S)}
    (h : IsDiag P θ ls) (h' : IsDiag P θ' ls) (e : x = x') (e' : y = y') :
    θ = eqToHom e ≫ θ' ≫ eqToHom e'.symm := by
  subst e e'
  obtain ⟨d, rfl, hd⟩ := h
  obtain ⟨d', rfl, hd'⟩ := h'
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact P.diag_eq_of_layers_eq (hd.trans hd'.symm)


-- @@ L127-131 verbatim
/-- Two 2-morphisms between the same 1-morphisms that are classes of diagrams with the same
layers are equal. -/
theorem IsDiag.eq {x y : l ⟶ m} {θ θ' : x ⟶ y} {ls : List (Layer S)}
    (h : IsDiag P θ ls) (h' : IsDiag P θ' ls) : θ = θ' := by
  simpa using h.eq_eqToHom h' rfl rfl


-- @@ L133-141 verbatim
/-- A 2-morphism with no layers is an `eqToHom`. -/
theorem IsDiag.eq_eqToHom_of_nil {x y : l ⟶ m} {θ : x ⟶ y} (h : IsDiag P θ []) :
    ∃ e : x = y, θ = eqToHom e := by
  obtain ⟨d, rfl, hd⟩ := h
  have e : x = y := Bicat.Hom.ext (Diagram.eq_of_layers_eq_nil d hd)
  subst e
  refine ⟨rfl, ?_⟩
  rw [eqToHom_refl]
  exact (P.diag_eq_of_layers_eq (hd.trans (Diagram.layers_id _).symm)).trans (P.diag_id _)


-- @@ L143-143 verbatim
end Presentation


-- @@ L145-145 verbatim
end StringDiagrams


-- @@ L147-175 verbatim
/-- Proves `Presentation.IsDiag P θ []` for composites and whiskerings of identities, `eqToHom`s,
associators and unitors (for instance the coherence 2-morphisms of `⊗≫`) in a presented
bicategory. -/
macro "isdiag_triv" : tactic => `(tactic| (
  simp only [CategoryTheory.BicategoricalCoherence.refl_iso,
    CategoryTheory.BicategoricalCoherence.whiskerLeft_iso,
    CategoryTheory.BicategoricalCoherence.whiskerRight_iso,
    CategoryTheory.BicategoricalCoherence.tensorRight_iso,
    CategoryTheory.BicategoricalCoherence.tensorRight'_iso,
    CategoryTheory.BicategoricalCoherence.left_iso,
    CategoryTheory.BicategoricalCoherence.left'_iso,
    CategoryTheory.BicategoricalCoherence.right_iso,
    CategoryTheory.BicategoricalCoherence.right'_iso,
    CategoryTheory.BicategoricalCoherence.assoc_iso,
    CategoryTheory.BicategoricalCoherence.assoc'_iso, CategoryTheory.Iso.trans_hom,
    CategoryTheory.Iso.symm_hom, CategoryTheory.Iso.refl_hom,
    CategoryTheory.Bicategory.whiskerLeftIso_hom, CategoryTheory.Bicategory.whiskerRightIso_hom]
  repeat (first
    | exact StringDiagrams.Presentation.isDiag_id _
    | exact StringDiagrams.Presentation.isDiag_eqToHom _
    | exact StringDiagrams.Presentation.isDiag_associator_hom _ _ _
    | exact StringDiagrams.Presentation.isDiag_associator_inv _ _ _
    | exact StringDiagrams.Presentation.isDiag_leftUnitor_hom _
    | exact StringDiagrams.Presentation.isDiag_leftUnitor_inv _
    | exact StringDiagrams.Presentation.isDiag_rightUnitor_hom _
    | exact StringDiagrams.Presentation.isDiag_rightUnitor_inv _
    | apply StringDiagrams.Presentation.isDiag_comp_nil
    | apply StringDiagrams.Presentation.isDiag_whiskerLeft_nil
    | apply StringDiagrams.Presentation.isDiag_whiskerRight_nil)))
