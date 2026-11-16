import StringDiagrams.Horizontal
import StringDiagrams.Monoidal
import Mathlib.CategoryTheory.Bicategory.Strict.Basic


-- @@ L5-31 verbatim
/-!
# Presented 2-categories as bicategories

For a signature with arbitrary regions, the presented category `P.Presented` of a
presentation is the category of 1-cells and 2-cells of a 2-category whose 0-cells are the
regions. This file makes the horizontal structure explicit.

* On morphisms of the presented category, right whiskering `f ⊗ 1_b` is `Presentation.wRAt`
  (for objects starting in a fixed region `r`) and left whiskering `1_a ⊗ g` is
  `Presentation.wL` (from `StringDiagrams.Monoidal`, which makes no assumption on regions);
  both are induced by `Presentation.whisk`. Under composability hypotheses they are
  functorial, linear, strictly associative and unital, and they send classes of diagrams to
  classes of the diagrams `Diagram.rwhisker`, `Diagram.lwhisker`
  (`Presentation.wRAt_diag`, `Presentation.wL_diag_of_composable`). They satisfy the
  interchange law up to the Koszul sign on classes of diagrams
  (`Presentation.wRAt_diag_comp_wL_diag`) and on arbitrary morphisms for even signatures
  (`Presentation.wRAt_comp_wL`). The horizontal composite is `Presentation.hcomp`.
* For even signatures (`Signature.IsEven`), `P.Bicat` is a strict bicategory in the sense of
  Mathlib (`Bicategory`, `Bicategory.Strict`): its objects are the regions, its 1-morphisms
  from `l` to `m` are the well-formed words starting in `l` and ending in `m`
  (`Presentation.Bicat.Hom`), composed by concatenation, and its 2-morphisms from `a` to `b`
  are the morphisms `P.obj a.obj ⟶ P.obj b.obj` of the presented category. Associators and
  unitors are given by equalities of words.

For signatures with odd generators the interchange law holds only up to sign and no
bicategory is constructed.
-/


-- @@ L33-33 verbatim
noncomputable section


-- @@ L35-35 verbatim
namespace StringDiagrams


-- @@ L37-37 verbatim
open CategoryTheory


-- @@ L39-39 verbatim
universe w v u₀ u₁ u₂


-- @@ L41-41 verbatim
variable {S : Signature.{u₀, u₁, u₂}}


-- @@ L43-43 verbatim
/-! ## Objects -/


-- @@ L45-45 verbatim
namespace Obj


-- @@ L47-48 verbatim
/-- The empty word in region `r`: the identity 1-cell of `r`. -/
def nil (r : S.Region) : Obj S := ⟨r, []⟩


-- @@ L50-50 verbatim
@[simp] theorem nil_start (r : S.Region) : (nil r).start = r := rfl

-- @@ L51-51 verbatim
@[simp] theorem nil_word (r : S.Region) : (nil r).word = ([] : List S.Colour) := rfl


-- @@ L53-53 verbatim
theorem nil_wf (r : S.Region) : (nil r).WF := trivial


-- @@ L55-59 verbatim
theorem tensor_eq_whisker_nil_of_start {a : Obj S} (b : Obj S) {r : S.Region}
    (h : a.start = r) : a.tensor b = a.whisker (nil r) b.word := by
  ext
  · exact h
  · simp [tensor, whisker, nil]


-- @@ L61-64 verbatim
theorem nil_tensor {b : Obj S} {r : S.Region} (h : b.start = r) : (nil r).tensor b = b := by
  ext
  · exact h.symm
  · simp [tensor, nil]


-- @@ L66-69 verbatim
theorem tensor_nil (a : Obj S) (r : S.Region) : a.tensor (nil r) = a := by
  ext
  · rfl
  · simp [tensor, nil]


-- @@ L71-71 verbatim
variable {a b c : Obj S}


-- @@ L73-75 verbatim
theorem Composable.tensor_left (hab : a.Composable b) (hbc : b.Composable c) :
    (a.tensor b).Composable c :=
  ⟨hab.wf_tensor, by rw [hab.endR_tensor]; exact hbc.endR_eq, hbc.right_wf⟩


-- @@ L77-79 verbatim
theorem Composable.tensor_right (hab : a.Composable b) (hbc : b.Composable c) :
    a.Composable (b.tensor c) :=
  ⟨hab.left_wf, hab.endR_eq, hbc.wf_tensor⟩


-- @@ L81-83 verbatim
theorem Composable.nil_left (hb : b.WF) {r : S.Region} (h : b.start = r) :
    (nil r).Composable b :=
  ⟨trivial, h.symm, hb⟩


-- @@ L85-87 verbatim
theorem Composable.nil_right (ha : a.WF) {r : S.Region} (h : a.endR = r) :
    a.Composable (nil r) :=
  ⟨ha, h, trivial⟩


-- @@ L89-89 verbatim
end Obj


-- @@ L91-91 verbatim
/-! ## Whiskering in the presented category -/


-- @@ L93-93 verbatim
namespace Presentation


-- @@ L95-95 verbatim
variable {R : Type w} [CommRing R] (P : Presentation.{w, v} S R)


-- @@ L97-97 verbatim
variable {a a' a'' b b' b'' c c' : Obj S} {r s : S.Region}


-- @@ L99-105 verbatim
/-- Right whiskering `f ⊗ 1_b` in the presented category, for objects `a`, `a'` starting in
the region `r` (it is `0` unless `a` can be whiskered by `b`). -/
def wRAt (r : S.Region) (f : P.obj a ⟶ P.obj a') (b : Obj S) (ha : a.start = r)
    (ha' : a'.start = r) : P.obj (a.tensor b) ⟶ P.obj (a'.tensor b) :=
  eqToHom (congrArg P.obj (Obj.tensor_eq_whisker_nil_of_start b ha)) ≫
    P.whisk f (Obj.nil r) b.word ≫
      eqToHom (congrArg P.obj (Obj.tensor_eq_whisker_nil_of_start b ha').symm)


-- @@ L107-107 verbatim
section Linear


-- @@ L109-109 verbatim
variable (ha : a.start = r) (ha' : a'.start = r) (ha'' : a''.start = r)


-- @@ L111-113 verbatim
theorem wRAt_comp (f : P.obj a ⟶ P.obj a') (f' : P.obj a' ⟶ P.obj a'') (b : Obj S) :
    P.wRAt r (f ≫ f') b ha ha'' = P.wRAt r f b ha ha' ≫ P.wRAt r f' b ha' ha'' := by
  simp [wRAt, whisk_comp]


-- @@ L115-117 verbatim
theorem wRAt_add (f f' : P.obj a ⟶ P.obj a') (b : Obj S) :
    P.wRAt r (f + f') b ha ha' = P.wRAt r f b ha ha' + P.wRAt r f' b ha ha' := by
  simp [wRAt, whisk_add]


-- @@ L119-121 verbatim
theorem wRAt_smul (x : R) (f : P.obj a ⟶ P.obj a') (b : Obj S) :
    P.wRAt r (x • f) b ha ha' = x • P.wRAt r f b ha ha' := by
  simp [wRAt, whisk_smul]


-- @@ L123-124 verbatim
theorem wRAt_zero (b : Obj S) : P.wRAt r (0 : P.obj a ⟶ P.obj a') b ha ha' = 0 := by
  simp [wRAt, whisk_zero]


-- @@ L126-129 verbatim
theorem wRAt_id (b : Obj S) (hb : S.ok a.endR b.word) :
    P.wRAt r (𝟙 (P.obj a)) b ha ha = 𝟙 _ := by
  have hw : a.WhiskerOK (Obj.nil r) b.word := ⟨trivial, ha.symm, hb⟩
  simp [wRAt, P.whisk_id a _ _ hw]


-- @@ L131-131 verbatim
end Linear


-- @@ L133-137 verbatim
theorem wRAt_eqToHom (h : P.obj a = P.obj a') (b : Obj S) (hb : S.ok a.endR b.word)
    (ha : a.start = r) (ha' : a'.start = r) :
    P.wRAt r (eqToHom h) b ha ha' = eqToHom (by rw [P.obj_injective h]) := by
  obtain rfl := P.obj_injective h
  simp [P.wRAt_id ha b hb]


-- @@ L139-150 verbatim
/-- The class of `f ⊗ 1_b`. -/
theorem wRAt_diag (f : a ⟶ a') (b : Obj S) (h : a.Composable b) (ha : a.start = r)
    (ha' : a'.start = r) : P.wRAt r (P.diag f) b ha ha' = P.diag (Diagram.rwhisker f b h) := by
  have hw : a.WhiskerOK (Obj.nil r) b.word := ⟨trivial, ha.symm, h.ok_endR⟩
  rw [wRAt, P.whisk_diag f _ _ hw]
  simp only [P.eqToHom_obj, ← P.diag_comp]
  apply P.diag_eq_of_layers_eq
  simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_whisker,
    Diagram.layers_rwhisker, List.nil_append, List.append_nil]
  exact List.map_congr_left fun L hL =>
    Layer.ext (by show r = L.start; rw [(Diagram.chain f).start_of_mem hL, ha]) (List.nil_append _)
      rfl rfl


-- @@ L152-153 verbatim
theorem wL_id_of_composable (h : a.Composable b) : P.wL a (𝟙 (P.obj b)) = 𝟙 _ := by
  simp [wL, P.whisk_id b a [] ⟨h.left_wf, h.endR_eq, trivial⟩]


-- @@ L155-158 verbatim
theorem wL_eqToHom_of_composable (h : P.obj b = P.obj b') (hab : a.Composable b) :
    P.wL a (eqToHom h) = eqToHom (by rw [P.obj_injective h]) := by
  obtain rfl := P.obj_injective h
  simp [P.wL_id_of_composable hab]


-- @@ L160-168 verbatim
/-- The class of `1_a ⊗ g`. -/
theorem wL_diag_of_composable (a : Obj S) (g : b ⟶ b') (h : a.Composable b) :
    P.wL a (P.diag g) = P.diag (Diagram.lwhisker a g h) := by
  rw [wL, P.whisk_diag g a [] ⟨h.left_wf, h.endR_eq, trivial⟩]
  simp only [P.eqToHom_obj, ← P.diag_comp]
  apply P.diag_eq_of_layers_eq
  simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_lwhisker,
    List.nil_append, List.append_nil]
  exact List.map_congr_left fun L _ => Layer.ext rfl rfl rfl (List.append_nil _)


-- @@ L170-170 verbatim
/-! ### Associativity and units -/


-- @@ L172-187 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Left whiskering by a composite. -/
theorem wL_tensor (hab : a.Composable b) (hbc : b.Composable c) (g : P.obj c ⟶ P.obj c') :
    P.wL (a.tensor b) g =
      eqToHom (congrArg P.obj (Obj.tensor_assoc a b c)) ≫ P.wL a (P.wL b g) ≫
        eqToHom (congrArg P.obj (Obj.tensor_assoc a b c')).symm := by
  induction g using P.hom_induction with
  | diag d =>
    rw [P.wL_diag_of_composable _ d (hab.tensor_left hbc), P.wL_diag_of_composable _ d hbc,
      P.wL_diag_of_composable _ _ (hab.tensor_right hbc)]
    simp only [P.eqToHom_obj, ← P.diag_comp]
    apply P.diag_eq_of_layers_eq
    simp [Layer.wl, Obj.tensor]
  | zero => simp [wL_zero]
  | add f g hf hg => simp only [wL_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | smul x f hf => simp only [wL_smul, Linear.smul_comp, Linear.comp_smul, hf]


-- @@ L189-206 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Right whiskering by a composite. -/
theorem wRAt_tensor (hab : a.Composable b) (hbc : b.Composable c) (f : P.obj a ⟶ P.obj a')
    (ha : a.start = r) (ha' : a'.start = r) :
    P.wRAt r f (b.tensor c) ha ha' =
      eqToHom (congrArg P.obj (Obj.tensor_assoc a b c)).symm ≫
        P.wRAt r (P.wRAt r f b ha ha') c ha ha' ≫
          eqToHom (congrArg P.obj (Obj.tensor_assoc a' b c)) := by
  induction f using P.hom_induction with
  | diag d =>
    have h₁ : (a.tensor b).Composable c := hab.tensor_left hbc
    rw [P.wRAt_diag d _ hab, P.wRAt_diag _ c h₁, P.wRAt_diag d _ (hab.tensor_right hbc)]
    simp only [P.eqToHom_obj, ← P.diag_comp]
    apply P.diag_eq_of_layers_eq
    simp [Layer.wr, Obj.tensor]
  | zero => simp [wRAt_zero]
  | add f g hf hg => simp only [wRAt_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | smul x f hf => simp only [wRAt_smul, Linear.smul_comp, Linear.comp_smul, hf]


-- @@ L208-225 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Right whiskering of a left whiskering. -/
theorem wRAt_wL (hab : a.Composable b) (hbc : b.Composable c) (g : P.obj b ⟶ P.obj b')
    (ha : a.start = r) (hb : b.start = s) (hb' : b'.start = s) :
    P.wRAt r (P.wL a g) c ha ha =
      eqToHom (congrArg P.obj (Obj.tensor_assoc a b c)) ≫ P.wL a (P.wRAt s g c hb hb') ≫
        eqToHom (congrArg P.obj (Obj.tensor_assoc a b' c)).symm := by
  induction g using P.hom_induction with
  | diag d =>
    rw [P.wL_diag_of_composable _ d hab, P.wRAt_diag _ c (hab.tensor_left hbc),
      P.wRAt_diag d c hbc, P.wL_diag_of_composable _ _ (hab.tensor_right hbc)]
    simp only [P.eqToHom_obj, ← P.diag_comp]
    apply P.diag_eq_of_layers_eq
    simp [Layer.wr, Layer.wl, Obj.tensor]
  | zero => simp [wRAt_zero, wL_zero]
  | add f g hf hg =>
    simp only [wRAt_add, wL_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | smul x f hf => simp only [wRAt_smul, wL_smul, Linear.smul_comp, Linear.comp_smul, hf]


-- @@ L227-245 verbatim
/-- Left whiskering by an identity 1-cell. -/
theorem wL_nil (g : P.obj b ⟶ P.obj b') (hb : b.WF) (hs : b.start = r) (hs' : b'.start = r) :
    P.wL (Obj.nil r) g =
      eqToHom (congrArg P.obj (Obj.nil_tensor hs)) ≫ g ≫
        eqToHom (congrArg P.obj (Obj.nil_tensor hs')).symm := by
  induction g using P.hom_induction with
  | diag d =>
    rw [P.wL_diag_of_composable _ d (Obj.Composable.nil_left hb hs)]
    simp only [P.eqToHom_obj, ← P.diag_comp]
    apply P.diag_eq_of_layers_eq
    simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_lwhisker,
      List.nil_append, List.append_nil]
    conv_rhs => rw [← List.map_id (Diagram.layers d)]
    exact List.map_congr_left fun L hL =>
      Layer.ext (by show r = L.start; rw [(Diagram.chain d).start_of_mem hL, hs])
        (List.nil_append _) rfl rfl
  | zero => simp [wL_zero]
  | add f g hf hg => simp only [wL_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | smul x f hf => simp only [wL_smul, Linear.smul_comp, Linear.comp_smul, hf]


-- @@ L247-264 verbatim
/-- Right whiskering by an identity 1-cell. -/
theorem wRAt_nil (f : P.obj a ⟶ P.obj a') (ha : a.WF) (he : a.endR = s) (hr : a.start = r)
    (hr' : a'.start = r) :
    P.wRAt r f (Obj.nil s) hr hr' =
      eqToHom (congrArg P.obj (Obj.tensor_nil a s)) ≫ f ≫
        eqToHom (congrArg P.obj (Obj.tensor_nil a' s)).symm := by
  induction f using P.hom_induction with
  | diag d =>
    rw [P.wRAt_diag d _ (Obj.Composable.nil_right ha he)]
    simp only [P.eqToHom_obj, ← P.diag_comp]
    apply P.diag_eq_of_layers_eq
    simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_rwhisker,
      List.nil_append, List.append_nil, Obj.nil_word]
    conv_rhs => rw [← List.map_id (Diagram.layers d)]
    exact List.map_congr_left fun L _ => Layer.ext rfl rfl rfl (List.append_nil _)
  | zero => simp [wRAt_zero]
  | add f g hf hg => simp only [wRAt_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | smul x f hf => simp only [wRAt_smul, Linear.smul_comp, Linear.comp_smul, hf]


-- @@ L266-266 verbatim
/-! ### The interchange law -/


-- @@ L268-276 verbatim
/-- The interchange law on classes of diagrams, with the Koszul sign, for general regions. -/
theorem wRAt_diag_comp_wL_diag (h : a.Composable b) (f : a ⟶ a') (g : b ⟶ b')
    (ha : a.start = r) (ha' : a'.start = r) :
    P.wRAt r (P.diag f) b ha ha' ≫ P.wL a' (P.diag g) =
      ((-1 : ℤ) ^ (Diagram.oddCount f * Diagram.oddCount g)) •
        (P.wL a (P.diag g) ≫ P.wRAt r (P.diag f) b' ha ha') := by
  rw [P.wRAt_diag f b h, P.wL_diag_of_composable a' g (h.map_left f),
    P.wL_diag_of_composable a g h, P.wRAt_diag f b' (h.map_right g), ← P.diag_comp,
    ← P.diag_comp, P.diag_interchange_of_composable]


-- @@ L278-294 verbatim
/-- The interchange law for arbitrary morphisms, for even signatures and general regions. -/
theorem wRAt_comp_wL [S.IsEven] (h : a.Composable b) (f : P.obj a ⟶ P.obj a')
    (g : P.obj b ⟶ P.obj b') (ha : a.start = r) (ha' : a'.start = r) :
    P.wRAt r f b ha ha' ≫ P.wL a' g = P.wL a g ≫ P.wRAt r f b' ha ha' := by
  induction f using P.hom_induction with
  | diag d =>
    induction g using P.hom_induction with
    | diag e =>
      rw [P.wRAt_diag_comp_wL_diag h d e, Diagram.oddCount_eq_zero, zero_mul, pow_zero,
        one_smul]
    | zero => simp [wL_zero]
    | add g g' hg hg' =>
      simp only [wL_add, Preadditive.add_comp, Preadditive.comp_add, hg, hg']
    | smul x g hg => simp only [wL_smul, Linear.smul_comp, Linear.comp_smul, hg]
  | zero => simp [wRAt_zero]
  | add f f' hf hf' => simp only [wRAt_add, Preadditive.add_comp, Preadditive.comp_add, hf, hf']
  | smul x f hf => simp only [wRAt_smul, Linear.smul_comp, Linear.comp_smul, hf]


-- @@ L296-296 verbatim
/-! ### Horizontal composition -/


-- @@ L298-302 verbatim
/-- The horizontal composite `f ⊗ g = (f ⊗ 1_b) ≫ (1_{a'} ⊗ g)` of `f : a ⟶ a'` and
`g : b ⟶ b'`, for `a`, `a'` starting in the region `r`. -/
def hcomp (r : S.Region) (f : P.obj a ⟶ P.obj a') (g : P.obj b ⟶ P.obj b') (ha : a.start = r)
    (ha' : a'.start = r) : P.obj (a.tensor b) ⟶ P.obj (a'.tensor b') :=
  P.wRAt r f b ha ha' ≫ P.wL a' g


-- @@ L304-309 verbatim
/-- The class of the horizontal composite of two diagrams. -/
theorem hcomp_diag (h : a.Composable b) (f : a ⟶ a') (g : b ⟶ b') (ha : a.start = r)
    (ha' : a'.start = r) :
    P.hcomp r (P.diag f) (P.diag g) ha ha' =
      P.diag (Diagram.rwhisker f b h ≫ Diagram.lwhisker a' g (h.map_left f)) := by
  rw [hcomp, P.wRAt_diag f b h, P.wL_diag_of_composable a' g (h.map_left f), P.diag_comp]


-- @@ L311-314 verbatim
/-- Horizontal composition of identities. -/
theorem hcomp_id (h : a.Composable b) (ha : a.start = r) :
    P.hcomp r (𝟙 (P.obj a)) (𝟙 (P.obj b)) ha ha = 𝟙 _ := by
  rw [hcomp, P.wRAt_id ha b h.ok_endR, P.wL_id_of_composable h, Category.comp_id]


-- @@ L316-320 verbatim
/-- The other order of whiskering, for even signatures. -/
theorem hcomp_eq [S.IsEven] (h : a.Composable b) (f : P.obj a ⟶ P.obj a')
    (g : P.obj b ⟶ P.obj b') (ha : a.start = r) (ha' : a'.start = r) :
    P.hcomp r f g ha ha' = P.wL a g ≫ P.wRAt r f b' ha ha' :=
  P.wRAt_comp_wL h f g ha ha'


-- @@ L322-331 verbatim
/-- Functoriality of horizontal composition (the middle-four interchange law), for even
signatures. -/
theorem hcomp_comp [S.IsEven] (h : a'.Composable b) (f : P.obj a ⟶ P.obj a')
    (f' : P.obj a' ⟶ P.obj a'') (g : P.obj b ⟶ P.obj b') (g' : P.obj b' ⟶ P.obj b'')
    (ha : a.start = r) (ha' : a'.start = r) (ha'' : a''.start = r) :
    P.hcomp r (f ≫ f') (g ≫ g') ha ha'' =
      P.hcomp r f g ha ha' ≫ P.hcomp r f' g' ha' ha'' := by
  simp only [hcomp, P.wRAt_comp ha ha' ha'', wL_comp, Category.assoc]
  rw [← Category.assoc (P.wRAt r f' b ha' ha''), P.wRAt_comp_wL h f' g ha' ha'',
    Category.assoc]


-- @@ L333-333 verbatim
/-! ## The presented bicategory -/


-- @@ L335-339 verbatim
/-- The objects of the 2-category presented by `P`: the regions. -/
@[ext]
structure Bicat (P : Presentation.{w, v} S R) : Type u₀ where
  /-- The underlying region. -/
  region : S.Region


-- @@ L341-341 verbatim
namespace Bicat


-- @@ L343-343 verbatim
variable {P} {l m n k j : P.Bicat}


-- @@ L345-355 verbatim
/-- A 1-morphism from `l` to `m`: a well-formed word starting in `l` and ending in `m`. -/
@[ext]
structure Hom (l m : P.Bicat) : Type (max u₀ u₁) where
  /-- The underlying object of the free 2-category. -/
  obj : Obj S
  /-- The word starts in `l`. -/
  start_eq : obj.start = l.region
  /-- The word is well formed. -/
  wf : obj.WF
  /-- The word ends in `m`. -/
  endR_eq : obj.endR = m.region


-- @@ L357-358 verbatim
theorem Hom.composable (a : Hom l m) (b : Hom m n) : a.obj.Composable b.obj :=
  ⟨a.wf, a.endR_eq.trans b.start_eq.symm, b.wf⟩


-- @@ L360-361 verbatim
/-- The identity 1-morphism of `l`: the empty word. -/
def Hom.id (l : P.Bicat) : Hom l l := ⟨Obj.nil l.region, rfl, trivial, rfl⟩


-- @@ L363-366 verbatim
/-- Composition of 1-morphisms: concatenation of words. -/
def Hom.comp (a : Hom l m) (b : Hom m n) : Hom l n :=
  ⟨a.obj.tensor b.obj, a.start_eq, (a.composable b).wf_tensor,
    by rw [(a.composable b).endR_tensor, b.endR_eq]⟩


-- @@ L368-368 verbatim
@[simp] theorem Hom.id_obj (l : P.Bicat) : (Hom.id l).obj = Obj.nil l.region := rfl


-- @@ L370-371 verbatim
@[simp] theorem Hom.comp_obj (a : Hom l m) (b : Hom m n) :
    (a.comp b).obj = a.obj.tensor b.obj := rfl


-- @@ L373-376 verbatim
instance : CategoryStruct P.Bicat where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp


-- @@ L378-386 verbatim
/-- The 2-morphisms between 1-morphisms `a b : l ⟶ m` are the morphisms
`P.obj a.obj ⟶ P.obj b.obj` of the presented category. -/
instance homCategory (l m : P.Bicat) : Category (Hom l m) where
  Hom a b := P.obj a.obj ⟶ P.obj b.obj
  id a := 𝟙 (P.obj a.obj)
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h


-- @@ L388-395 verbatim
/-- The invertible 2-morphism given by an equality of the underlying words. -/
def isoOfEq {a b : Hom l m} (e : a.obj = b.obj) : a ≅ b where
  hom := (eqToHom (congrArg P.obj e) : P.obj a.obj ⟶ P.obj b.obj)
  inv := (eqToHom (congrArg P.obj e.symm) : P.obj b.obj ⟶ P.obj a.obj)
  hom_inv_id :=
    (eqToHom_trans (congrArg P.obj e) (congrArg P.obj e.symm)).trans (eqToHom_refl _ _)
  inv_hom_id :=
    (eqToHom_trans (congrArg P.obj e.symm) (congrArg P.obj e)).trans (eqToHom_refl _ _)


-- @@ L397-401 verbatim
theorem isoOfEq_eq_eqToIso {a b : Hom l m} (e : a.obj = b.obj) (e' : a = b) :
    isoOfEq e = eqToIso e' := by
  subst e'
  apply Iso.ext
  exact eqToHom_refl (P.obj a.obj) (congrArg P.obj e)


-- @@ L403-413 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem pentagon_aux (a : Hom l m) (b : Hom m n) (c : Hom n k) (d : Hom k j) :
    P.wRAt l.region (eqToHom (congrArg P.obj (Obj.tensor_assoc a.obj b.obj c.obj))) d.obj
        a.start_eq a.start_eq ≫
      eqToHom (congrArg P.obj (Obj.tensor_assoc a.obj (b.obj.tensor c.obj) d.obj)) ≫
        P.wL a.obj (eqToHom (congrArg P.obj (Obj.tensor_assoc b.obj c.obj d.obj))) =
      eqToHom (congrArg P.obj (Obj.tensor_assoc (a.obj.tensor b.obj) c.obj d.obj)) ≫
        eqToHom (congrArg P.obj (Obj.tensor_assoc a.obj b.obj (c.obj.tensor d.obj))) := by
  rw [P.wRAt_eqToHom _ _ (((a.comp b).comp c).composable d).ok_endR,
    P.wL_eqToHom_of_composable _ (a.composable ((b.comp c).comp d))]
  simp


-- @@ L415-423 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem triangle_aux (a : Hom l m) (b : Hom m n) :
    eqToHom (congrArg P.obj (Obj.tensor_assoc a.obj (Obj.nil m.region) b.obj)) ≫
        P.wL a.obj (eqToHom (congrArg P.obj (Obj.nil_tensor b.start_eq))) =
      P.wRAt l.region (eqToHom (congrArg P.obj (Obj.tensor_nil a.obj m.region))) b.obj
        a.start_eq a.start_eq := by
  rw [P.wRAt_eqToHom _ _ ((a.comp (Hom.id m)).composable b).ok_endR,
    P.wL_eqToHom_of_composable _ (a.composable ((Hom.id m).comp b))]
  simp


-- @@ L425-425 verbatim
end Bicat


-- @@ L427-459 verbatim
/-- For an even signature, the regions, well-formed words and morphisms of the presented
category form a bicategory. -/
instance instBicategory [S.IsEven] : Bicategory P.Bicat where
  homCategory := Bicat.homCategory
  whiskerLeft a _ _ θ := P.wL (Bicat.Hom.obj a) θ
  whiskerRight {l _ _} {a a'} η b :=
    P.wRAt l.region η (Bicat.Hom.obj b) (Bicat.Hom.start_eq a) (Bicat.Hom.start_eq a')
  associator a b c :=
    Bicat.isoOfEq (Obj.tensor_assoc (Bicat.Hom.obj a) (Bicat.Hom.obj b) (Bicat.Hom.obj c))
  leftUnitor a := Bicat.isoOfEq (Obj.nil_tensor (Bicat.Hom.start_eq a))
  rightUnitor {_ m} a := Bicat.isoOfEq (Obj.tensor_nil (Bicat.Hom.obj a) m.region)
  whiskerLeft_id a b := P.wL_id_of_composable (Bicat.Hom.composable a b)
  whiskerLeft_comp a _ _ _ η θ := P.wL_comp (Bicat.Hom.obj a) η θ
  id_whiskerLeft {_ _} {a b} η :=
    P.wL_nil η (Bicat.Hom.wf a) (Bicat.Hom.start_eq a) (Bicat.Hom.start_eq b)
  comp_whiskerLeft a b _ _ η :=
    P.wL_tensor (Bicat.Hom.composable a b) (Bicat.Hom.composable b _) η
  id_whiskerRight a b :=
    P.wRAt_id (Bicat.Hom.start_eq a) (Bicat.Hom.obj b) (Bicat.Hom.composable a b).ok_endR
  comp_whiskerRight η θ c := P.wRAt_comp _ _ _ η θ (Bicat.Hom.obj c)
  whiskerRight_id {_ _} {a a'} η :=
    P.wRAt_nil η (Bicat.Hom.wf a) (Bicat.Hom.endR_eq a) (Bicat.Hom.start_eq a)
      (Bicat.Hom.start_eq a')
  whiskerRight_comp {_ _ _ _} {a _} η b c :=
    P.wRAt_tensor (Bicat.Hom.composable a b) (Bicat.Hom.composable b c) η _ _
  whisker_assoc {_ _ _ _} a {b b'} η c :=
    P.wRAt_wL (Bicat.Hom.composable a b) (Bicat.Hom.composable b c) η (Bicat.Hom.start_eq a)
      (Bicat.Hom.start_eq b) (Bicat.Hom.start_eq b')
  whisker_exchange {_ _ _} {a a'} {b _} η θ :=
    (P.wRAt_comp_wL (Bicat.Hom.composable a b) η θ (Bicat.Hom.start_eq a)
      (Bicat.Hom.start_eq a')).symm
  pentagon a b c d := Bicat.pentagon_aux a b c d
  triangle a b := Bicat.triangle_aux a b


-- @@ L461-468 verbatim
/-- The presented bicategory is strict: associators and unitors are equalities of words. -/
instance instBicategoryStrict [S.IsEven] : Bicategory.Strict P.Bicat where
  id_comp a := Bicat.Hom.ext (Obj.nil_tensor (Bicat.Hom.start_eq a))
  comp_id _ := Bicat.Hom.ext (Obj.tensor_nil _ _)
  assoc _ _ _ := Bicat.Hom.ext (Obj.tensor_assoc _ _ _)
  leftUnitor_eqToIso _ := Bicat.isoOfEq_eq_eqToIso _ _
  rightUnitor_eqToIso _ := Bicat.isoOfEq_eq_eqToIso _ _
  associator_eqToIso _ _ _ := Bicat.isoOfEq_eq_eqToIso _ _


-- @@ L470-470 verbatim
section BicatAPI


-- @@ L472-472 verbatim
open Bicategory


-- @@ L474-474 verbatim
variable [S.IsEven] {l m n : P.Bicat}


-- @@ L476-477 verbatim
theorem Bicat.whiskerLeft_eq (a : l ⟶ m) {b b' : m ⟶ n} (θ : b ⟶ b') :
    a ◁ θ = P.wL (Bicat.Hom.obj a) θ := rfl


-- @@ L479-481 verbatim
theorem Bicat.whiskerRight_eq {a a' : l ⟶ m} (η : a ⟶ a') (b : m ⟶ n) :
    η ▷ b = P.wRAt l.region η (Bicat.Hom.obj b) (Bicat.Hom.start_eq a) (Bicat.Hom.start_eq a') :=
  rfl


-- @@ L483-483 verbatim
end BicatAPI


-- @@ L485-485 verbatim
end Presentation


-- @@ L487-487 verbatim
end StringDiagrams


-- @@ L489-489 verbatim
end
