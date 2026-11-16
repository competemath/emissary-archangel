import StringDiagrams.Interchange
import StringDiagrams.Generation
import Mathlib.CategoryTheory.Monoidal.Linear


-- @@ L5-43 verbatim
/-!
# Presented categories of even monoidal signatures are monoidal

For a monoidal signature (a single region: `[Subsingleton S.Region]`, with the region chosen
by `[Inhabited S.Region]`), the presented category `P.Presented` of any presentation `P`
carries a strict monoidal structure in the sense of Mathlib (`MonoidalCategory`) as soon as
all generators are even (`Signature.IsEven`):

* on objects, `P.obj a ⊗ P.obj b = P.obj (a.tensor b)` (`Presentation.obj_tensor`, by `rfl`),
  and the unit is the empty word (`Obj.unit`);
* whiskering is `Presentation.whisk`, retyped along the identifications
  `a.tensor b = a.whisker Obj.unit b.word` and `a.tensor b = b.whisker a []`;
* the associator and the unitors are `eqToIso`s of equalities of objects
  (`Presentation.associator_eq`, `Presentation.leftUnitor_eq`,
  `Presentation.rightUnitor_eq`): the structure is strict.

The interchange law `whisker_exchange` for arbitrary morphisms is
`Presentation.diag_interchange_diagrams` (whose Koszul sign is `1` for even signatures),
extended bilinearly with `Presentation.hom_induction`. For signatures with odd generators the
interchange law holds only up to sign, and `P.Presented` is a monoidal supercategory rather
than a monoidal category; no such structure is constructed here.

The tensor product is `R`-bilinear (`MonoidalPreadditive`, `MonoidalLinear R`).

All constructions are first made for objects of the form `P.obj a` with `a : Obj S`
(`Presentation.wR`, `Presentation.wL`); the fields of the monoidal structure are then
instances of these lemmas, up to definitional unfolding.

## Main definitions and results

* `Signature.IsEven`: every generator is even.
* `Obj.unit`, `Obj.tensor_assoc`, `Obj.unit_tensor`, `Obj.tensor_unit`.
* `Presentation.instMonoidalCategory`, `Presentation.instMonoidalPreadditive`,
  `Presentation.instMonoidalLinear`.
* `Presentation.obj_tensor`, `Presentation.obj_unit`.
* `Presentation.diag_whiskerRight`, `Presentation.diag_whiskerLeft`: the classes of the
  diagrams `Diagram.whiskerR f b` and `Diagram.whiskerL a g` are `P.diag f ▷ P.obj b` and
  `P.obj a ◁ P.diag g`.
-/


-- @@ L45-45 verbatim
noncomputable section


-- @@ L47-47 verbatim
namespace StringDiagrams


-- @@ L49-49 verbatim
open CategoryTheory MonoidalCategory


-- @@ L51-51 verbatim
universe w v u₀ u₁ u₂


-- @@ L53-56 verbatim
/-- A signature is *even* if all its generators are even. The interchange law then holds
without signs. -/
class Signature.IsEven (S : Signature.{u₀, u₁, u₂}) : Prop where
  odd_eq_false : ∀ g : S.Gen, S.odd g = false


-- @@ L58-58 verbatim
variable {S : Signature.{u₀, u₁, u₂}}


-- @@ L60-62 verbatim
theorem Diagram.oddCount_eq_zero [S.IsEven] {a b : Obj S} (f : a ⟶ b) :
    Diagram.oddCount f = 0 := by
  simp [Diagram.oddCount, Diagram.oddCountList, Signature.IsEven.odd_eq_false]


-- @@ L64-64 verbatim
/-! ## Objects -/


-- @@ L66-66 verbatim
namespace Obj


-- @@ L68-69 verbatim
/-- The empty word at the chosen region: the unit object. -/
def unit [Inhabited S.Region] : Obj S := ⟨default, []⟩


-- @@ L71-71 verbatim
@[simp] theorem unit_start [Inhabited S.Region] : (unit : Obj S).start = default := rfl

-- @@ L72-72 verbatim
@[simp] theorem unit_word [Inhabited S.Region] : (unit : Obj S).word = [] := rfl


-- @@ L74-75 verbatim
theorem tensor_assoc (a b c : Obj S) : (a.tensor b).tensor c = a.tensor (b.tensor c) := by
  ext <;> simp [tensor]


-- @@ L77-79 verbatim
theorem unit_tensor [Subsingleton S.Region] [Inhabited S.Region] (a : Obj S) :
    unit.tensor a = a :=
  Obj.ext (Subsingleton.elim _ _) (by simp [tensor])


-- @@ L81-82 verbatim
theorem tensor_unit [Inhabited S.Region] (a : Obj S) : a.tensor unit = a := by
  ext <;> simp [tensor]


-- @@ L84-87 verbatim
/-- Right whiskering by `b` is tensoring with `b` on the right. -/
theorem tensor_eq_whisker_unit [Subsingleton S.Region] [Inhabited S.Region] (a b : Obj S) :
    a.tensor b = a.whisker unit b.word :=
  Obj.ext (Subsingleton.elim _ _) (by simp [tensor])


-- @@ L89-91 verbatim
/-- Left whiskering by `a` is tensoring with `a` on the left. -/
theorem tensor_eq_whisker_nil (a b : Obj S) : a.tensor b = b.whisker a [] := by
  ext <;> simp [tensor]


-- @@ L93-93 verbatim
end Obj


-- @@ L95-95 verbatim
namespace Presentation


-- @@ L97-97 verbatim
variable {R : Type w} [CommRing R] (P : Presentation.{w, v} S R)


-- @@ L99-99 verbatim
/-! ## Generalities on objects and `eqToHom` -/


-- @@ L101-102 verbatim
/-- The object of the free 2-category underlying an object of the presented category. -/
def toObj (X : P.Presented) : Obj S := X.as


-- @@ L104-104 verbatim
@[simp] theorem toObj_obj (a : Obj S) : P.toObj (P.obj a) = a := rfl


-- @@ L106-106 verbatim
@[simp] theorem obj_toObj (X : P.Presented) : P.obj (P.toObj X) = X := rfl


-- @@ L108-108 verbatim
theorem obj_injective : Function.Injective P.obj := fun _ _ h => congrArg P.toObj h


-- @@ L110-110 verbatim
@[simp] theorem obj_inj {a b : Obj S} : P.obj a = P.obj b ↔ a = b := P.obj_injective.eq_iff


-- @@ L112-114 verbatim
theorem diag_eqToHom {a b : Obj S} (h : a = b) :
    P.diag (eqToHom h) = eqToHom (congrArg P.obj h) := by
  subst h; simp


-- @@ L116-119 verbatim
/-- Every `eqToHom` between objects `P.obj a` is the class of a (retyped) empty diagram. -/
theorem eqToHom_obj {a b : Obj S} (h : P.obj a = P.obj b) :
    eqToHom h = P.diag (eqToHom (P.obj_injective h)) := by
  rw [diag_eqToHom]


-- @@ L121-124 verbatim
theorem diag_cast {a b a' b' : Obj S} (f : a ⟶ b) (ha : a = a') (hb : b = b') :
    P.diag (Diagram.cast f ha hb) =
      eqToHom (congrArg P.obj ha.symm) ≫ P.diag f ≫ eqToHom (congrArg P.obj hb) := by
  subst ha hb; simp


-- @@ L126-131 verbatim
/-- Two diagrams with the same layers have the same class, up to retyping. -/
theorem diag_eq_of_layers_eq' {a b a' b' : Obj S} (f : a ⟶ b) (g : a' ⟶ b') (ha : a = a')
    (hb : b = b') (h : Diagram.layers f = Diagram.layers g) :
    P.diag f = eqToHom (congrArg P.obj ha) ≫ P.diag g ≫ eqToHom (congrArg P.obj hb.symm) := by
  subst ha hb; simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact P.diag_eq_of_layers_eq h


-- @@ L133-133 verbatim
/-! ## Whiskering by objects, for objects of the form `P.obj a` -/


-- @@ L135-139 verbatim
/-- Left whiskering `1_a ⊗ g`. -/
def wL (a : Obj S) {b b' : Obj S} (g : P.obj b ⟶ P.obj b') :
    P.obj (a.tensor b) ⟶ P.obj (a.tensor b') :=
  eqToHom (congrArg P.obj (Obj.tensor_eq_whisker_nil a b)) ≫ P.whisk g a [] ≫
    eqToHom (congrArg P.obj (Obj.tensor_eq_whisker_nil a b').symm)


-- @@ L141-145 verbatim
/-- Right whiskering `f ⊗ 1_b`. -/
def wR [Subsingleton S.Region] [Inhabited S.Region] {a a' : Obj S} (f : P.obj a ⟶ P.obj a')
    (b : Obj S) : P.obj (a.tensor b) ⟶ P.obj (a'.tensor b) :=
  eqToHom (congrArg P.obj (Obj.tensor_eq_whisker_unit a b)) ≫ P.whisk f Obj.unit b.word ≫
    eqToHom (congrArg P.obj (Obj.tensor_eq_whisker_unit a' b).symm)


-- @@ L147-147 verbatim
variable {a a' a'' b b' b'' c c' : Obj S}


-- @@ L149-149 verbatim
section Linear


-- @@ L151-153 verbatim
theorem wL_comp (a : Obj S) (g : P.obj b ⟶ P.obj b') (g' : P.obj b' ⟶ P.obj b'') :
    P.wL a (g ≫ g') = P.wL a g ≫ P.wL a g' := by
  simp [wL, whisk_comp]


-- @@ L155-157 verbatim
theorem wL_add (a : Obj S) (g g' : P.obj b ⟶ P.obj b') :
    P.wL a (g + g') = P.wL a g + P.wL a g' := by
  simp [wL, whisk_add]


-- @@ L159-161 verbatim
theorem wL_smul (a : Obj S) (r : R) (g : P.obj b ⟶ P.obj b') :
    P.wL a (r • g) = r • P.wL a g := by
  simp [wL, whisk_smul]


-- @@ L163-164 verbatim
theorem wL_zero (a : Obj S) : P.wL a (0 : P.obj b ⟶ P.obj b') = 0 := by
  simp [wL, whisk_zero]


-- @@ L166-166 verbatim
variable [Subsingleton S.Region] [Inhabited S.Region]


-- @@ L168-170 verbatim
theorem wR_comp (f : P.obj a ⟶ P.obj a') (f' : P.obj a' ⟶ P.obj a'') (b : Obj S) :
    P.wR (f ≫ f') b = P.wR f b ≫ P.wR f' b := by
  simp [wR, whisk_comp]


-- @@ L172-174 verbatim
theorem wR_add (f f' : P.obj a ⟶ P.obj a') (b : Obj S) :
    P.wR (f + f') b = P.wR f b + P.wR f' b := by
  simp [wR, whisk_add]


-- @@ L176-178 verbatim
theorem wR_smul (r : R) (f : P.obj a ⟶ P.obj a') (b : Obj S) :
    P.wR (r • f) b = r • P.wR f b := by
  simp [wR, whisk_smul]


-- @@ L180-181 verbatim
theorem wR_zero (b : Obj S) : P.wR (0 : P.obj a ⟶ P.obj a') b = 0 := by
  simp [wR, whisk_zero]


-- @@ L183-183 verbatim
end Linear


-- @@ L185-185 verbatim
section Whiskering


-- @@ L187-187 verbatim
variable [Subsingleton S.Region]


-- @@ L189-195 verbatim
theorem wL_diag (a : Obj S) (g : b ⟶ b') : P.wL a (P.diag g) = P.diag (Diagram.whiskerL a g) := by
  rw [wL, P.whisk_diag g _ _ (Obj.whiskerOK_of_subsingleton _ _ _)]
  simp only [P.eqToHom_obj, ← P.diag_comp]
  apply P.diag_eq_of_layers_eq
  simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_whisker,
    Diagram.layers_whiskerL, List.nil_append, List.append_nil]
  exact List.map_congr_left fun L _ => Layer.ext rfl rfl rfl (List.append_nil _)


-- @@ L197-198 verbatim
theorem wL_id (a b : Obj S) : P.wL a (𝟙 (P.obj b)) = 𝟙 _ := by
  simp [wL, P.whisk_id b _ _ (Obj.whiskerOK_of_subsingleton _ _ _)]


-- @@ L200-203 verbatim
theorem wL_eqToHom (a : Obj S) (h : P.obj b = P.obj b') :
    P.wL a (eqToHom h) = eqToHom (by rw [P.obj_injective h]) := by
  obtain rfl := P.obj_injective h
  simp [wL_id]


-- @@ L205-218 verbatim
/-- Associativity of left whiskering. -/
@[reassoc]
theorem wL_wL (a b : Obj S) (h : P.obj c ⟶ P.obj c') :
    P.wL (a.tensor b) h ≫ eqToHom (congrArg P.obj (Obj.tensor_assoc a b c')) =
      eqToHom (congrArg P.obj (Obj.tensor_assoc a b c)) ≫ P.wL a (P.wL b h) := by
  induction h using P.hom_induction with
  | diag d =>
    simp only [wL_diag, P.eqToHom_obj, ← P.diag_comp]
    apply P.diag_eq_of_layers_eq
    simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_whiskerL]
    simp [Layer.wl, Obj.tensor]
  | zero => simp [wL_zero]
  | add f g hf hg => simp only [wL_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | smul r f hf => simp only [wL_smul, Linear.smul_comp, Linear.comp_smul, hf]


-- @@ L220-220 verbatim
variable [Inhabited S.Region]


-- @@ L222-229 verbatim
theorem wR_diag (f : a ⟶ a') (b : Obj S) : P.wR (P.diag f) b = P.diag (Diagram.whiskerR f b) := by
  rw [wR, P.whisk_diag f _ _ (Obj.whiskerOK_of_subsingleton _ _ _)]
  simp only [P.eqToHom_obj, ← P.diag_comp]
  apply P.diag_eq_of_layers_eq
  simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_whisker,
    Diagram.layers_whiskerR, List.nil_append, List.append_nil]
  exact List.map_congr_left fun L _ =>
    Layer.ext (Subsingleton.elim _ _) (List.nil_append _) rfl rfl


-- @@ L231-232 verbatim
theorem wR_id (a b : Obj S) : P.wR (𝟙 (P.obj a)) b = 𝟙 _ := by
  simp [wR, P.whisk_id a _ _ (Obj.whiskerOK_of_subsingleton _ _ _)]


-- @@ L234-237 verbatim
theorem wR_eqToHom (h : P.obj a = P.obj a') (b : Obj S) :
    P.wR (eqToHom h) b = eqToHom (by rw [P.obj_injective h]) := by
  obtain rfl := P.obj_injective h
  simp [wR_id]


-- @@ L239-252 verbatim
/-- Associativity of right whiskering. -/
@[reassoc]
theorem wR_wR (f : P.obj a ⟶ P.obj a') (b c : Obj S) :
    P.wR (P.wR f b) c ≫ eqToHom (congrArg P.obj (Obj.tensor_assoc a' b c)) =
      eqToHom (congrArg P.obj (Obj.tensor_assoc a b c)) ≫ P.wR f (b.tensor c) := by
  induction f using P.hom_induction with
  | diag d =>
    simp only [wR_diag, P.eqToHom_obj, ← P.diag_comp]
    apply P.diag_eq_of_layers_eq
    simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_whiskerR]
    simp [Layer.wr, Obj.tensor]
  | zero => simp [wR_zero]
  | add f g hf hg => simp only [wR_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | smul r f hf => simp only [wR_smul, Linear.smul_comp, Linear.comp_smul, hf]


-- @@ L254-268 verbatim
/-- Right whiskering of a left whiskering (the middle associativity). -/
@[reassoc]
theorem wL_wR (a : Obj S) (g : P.obj b ⟶ P.obj b') (c : Obj S) :
    P.wR (P.wL a g) c ≫ eqToHom (congrArg P.obj (Obj.tensor_assoc a b' c)) =
      eqToHom (congrArg P.obj (Obj.tensor_assoc a b c)) ≫ P.wL a (P.wR g c) := by
  induction g using P.hom_induction with
  | diag d =>
    simp only [wL_diag, wR_diag, P.eqToHom_obj, ← P.diag_comp]
    apply P.diag_eq_of_layers_eq
    simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_whiskerL,
      Diagram.layers_whiskerR]
    simp [Layer.wr, Layer.wl]
  | zero => simp [wR_zero, wL_zero]
  | add f g hf hg => simp only [wR_add, wL_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | smul r f hf => simp only [wR_smul, wL_smul, Linear.smul_comp, Linear.comp_smul, hf]


-- @@ L270-285 verbatim
/-- Left whiskering by the unit object. -/
theorem unit_wL (g : P.obj b ⟶ P.obj b') :
    P.wL Obj.unit g ≫ eqToHom (congrArg P.obj (Obj.unit_tensor b')) =
      eqToHom (congrArg P.obj (Obj.unit_tensor b)) ≫ g := by
  induction g using P.hom_induction with
  | diag d =>
    simp only [wL_diag, P.eqToHom_obj, ← P.diag_comp]
    apply P.diag_eq_of_layers_eq
    simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_whiskerL,
      List.nil_append, List.append_nil]
    conv_rhs => rw [← List.map_id (Diagram.layers d)]
    exact List.map_congr_left fun L _ =>
      Layer.ext (Subsingleton.elim _ _) (List.nil_append _) rfl rfl
  | zero => simp [wL_zero]
  | add f g hf hg => simp only [wL_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | smul r f hf => simp only [wL_smul, Linear.smul_comp, Linear.comp_smul, hf]


-- @@ L287-301 verbatim
/-- Right whiskering by the unit object. -/
theorem wR_unit (f : P.obj a ⟶ P.obj a') :
    P.wR f Obj.unit ≫ eqToHom (congrArg P.obj (Obj.tensor_unit a')) =
      eqToHom (congrArg P.obj (Obj.tensor_unit a)) ≫ f := by
  induction f using P.hom_induction with
  | diag d =>
    simp only [wR_diag, P.eqToHom_obj, ← P.diag_comp]
    apply P.diag_eq_of_layers_eq
    simp only [Diagram.layers_comp, Diagram.layers_eqToHom, Diagram.layers_whiskerR,
      List.nil_append, List.append_nil]
    conv_rhs => rw [← List.map_id (Diagram.layers d)]
    exact List.map_congr_left fun L _ => Layer.ext rfl rfl rfl (List.append_nil _)
  | zero => simp [wR_zero]
  | add f g hf hg => simp only [wR_add, Preadditive.add_comp, Preadditive.comp_add, hf, hg]
  | smul r f hf => simp only [wR_smul, Linear.smul_comp, Linear.comp_smul, hf]


-- @@ L303-318 verbatim
/-- The interchange law for arbitrary morphisms, for even signatures. -/
theorem wR_comp_wL [S.IsEven] (f : P.obj a ⟶ P.obj a') (g : P.obj b ⟶ P.obj b') :
    P.wR f b ≫ P.wL a' g = P.wL a g ≫ P.wR f b' := by
  induction f using P.hom_induction with
  | diag d =>
    induction g using P.hom_induction with
    | diag e =>
      rw [wR_diag, wR_diag, wL_diag, wL_diag, ← diag_comp, ← diag_comp,
        P.diag_interchange_diagrams, Diagram.oddCount_eq_zero, zero_mul, pow_zero, one_smul]
    | zero => simp [wL_zero]
    | add g g' hg hg' =>
      simp only [wL_add, Preadditive.add_comp, Preadditive.comp_add, hg, hg']
    | smul r g hg => simp only [wL_smul, Linear.smul_comp, Linear.comp_smul, hg]
  | zero => simp [wR_zero]
  | add f f' hf hf' => simp only [wR_add, Preadditive.add_comp, Preadditive.comp_add, hf, hf']
  | smul r f hf => simp only [wR_smul, Linear.smul_comp, Linear.comp_smul, hf]


-- @@ L320-320 verbatim
/-! ### The axioms of a monoidal category, for objects of the form `P.obj a` -/


-- @@ L322-327 verbatim
theorem tensor_comp_aux [S.IsEven] (f₁ : P.obj a ⟶ P.obj a') (g₁ : P.obj a' ⟶ P.obj a'')
    (f₂ : P.obj b ⟶ P.obj b') (g₂ : P.obj b' ⟶ P.obj b'') :
    P.wR (f₁ ≫ g₁) b ≫ P.wL a'' (f₂ ≫ g₂) =
      (P.wR f₁ b ≫ P.wL a' f₂) ≫ (P.wR g₁ b' ≫ P.wL a'' g₂) := by
  rw [wR_comp, wL_comp, Category.assoc, Category.assoc, ← Category.assoc (P.wR g₁ b),
    P.wR_comp_wL g₁ f₂, Category.assoc]


-- @@ L329-336 verbatim
theorem associator_naturality_aux {a₁ a₂ a₃ b₁ b₂ b₃ : Obj S} (f₁ : P.obj a₁ ⟶ P.obj b₁)
    (f₂ : P.obj a₂ ⟶ P.obj b₂) (f₃ : P.obj a₃ ⟶ P.obj b₃) :
    (P.wR (P.wR f₁ a₂ ≫ P.wL b₁ f₂) a₃ ≫ P.wL (b₁.tensor b₂) f₃) ≫
        eqToHom (congrArg P.obj (Obj.tensor_assoc b₁ b₂ b₃)) =
      eqToHom (congrArg P.obj (Obj.tensor_assoc a₁ a₂ a₃)) ≫
        (P.wR f₁ (a₂.tensor a₃) ≫ P.wL b₁ (P.wR f₂ a₃ ≫ P.wL b₂ f₃)) := by
  simp only [wR_comp, wL_comp, Category.assoc]
  rw [P.wL_wL, P.wL_wR_assoc, P.wR_wR_assoc]


-- @@ L338-344 verbatim
theorem pentagon_aux (a b c d : Obj S) :
    P.wR (eqToHom (congrArg P.obj (Obj.tensor_assoc a b c))) d ≫
        eqToHom (congrArg P.obj (Obj.tensor_assoc a (b.tensor c) d)) ≫
          P.wL a (eqToHom (congrArg P.obj (Obj.tensor_assoc b c d))) =
      eqToHom (congrArg P.obj (Obj.tensor_assoc (a.tensor b) c d)) ≫
        eqToHom (congrArg P.obj (Obj.tensor_assoc a b (c.tensor d))) := by
  simp [wR_eqToHom, wL_eqToHom]


-- @@ L346-350 verbatim
theorem triangle_aux (a b : Obj S) :
    eqToHom (congrArg P.obj (Obj.tensor_assoc a Obj.unit b)) ≫
        P.wL a (eqToHom (congrArg P.obj (Obj.unit_tensor b))) =
      P.wR (eqToHom (congrArg P.obj (Obj.tensor_unit a))) b := by
  simp [wR_eqToHom, wL_eqToHom]


-- @@ L352-352 verbatim
end Whiskering


-- @@ L354-354 verbatim
/-! ## The monoidal structure -/


-- @@ L356-356 verbatim
section Monoidal


-- @@ L358-358 verbatim
variable [Subsingleton S.Region] [Inhabited S.Region]


-- @@ L360-368 verbatim
instance instMonoidalCategoryStruct : MonoidalCategoryStruct P.Presented where
  tensorObj X Y := P.obj ((P.toObj X).tensor (P.toObj Y))
  whiskerLeft X {_ _} g := P.wL (P.toObj X) g
  whiskerRight f Y := P.wR f (P.toObj Y)
  tensorHom f g := P.wR f _ ≫ P.wL _ g
  tensorUnit := P.obj Obj.unit
  associator _ _ _ := eqToIso (congrArg P.obj (Obj.tensor_assoc _ _ _))
  leftUnitor _ := eqToIso (congrArg P.obj (Obj.unit_tensor _))
  rightUnitor _ := eqToIso (congrArg P.obj (Obj.tensor_unit _))


-- @@ L370-370 verbatim
theorem obj_tensor (a b : Obj S) : P.obj a ⊗ P.obj b = P.obj (a.tensor b) := rfl


-- @@ L372-372 verbatim
theorem obj_unit : 𝟙_ P.Presented = P.obj Obj.unit := rfl


-- @@ L374-375 verbatim
theorem whiskerRight_eq {a a' : Obj S} (f : P.obj a ⟶ P.obj a') (b : Obj S) :
    f ▷ P.obj b = P.wR f b := rfl


-- @@ L377-378 verbatim
theorem whiskerLeft_eq (a : Obj S) {b b' : Obj S} (g : P.obj b ⟶ P.obj b') :
    P.obj a ◁ g = P.wL a g := rfl


-- @@ L380-382 verbatim
/-- The class of `f ⊗ 1_b` is `P.diag f ▷ P.obj b`. -/
@[simp] theorem diag_whiskerRight {a a' : Obj S} (f : a ⟶ a') (b : Obj S) :
    P.diag f ▷ P.obj b = P.diag (Diagram.whiskerR f b) := P.wR_diag f b


-- @@ L384-386 verbatim
/-- The class of `1_a ⊗ g` is `P.obj a ◁ P.diag g`. -/
@[simp] theorem diag_whiskerLeft (a : Obj S) {b b' : Obj S} (g : b ⟶ b') :
    P.obj a ◁ P.diag g = P.diag (Diagram.whiskerL a g) := P.wL_diag a g


-- @@ L388-390 verbatim
/-- The tensor product of objects is strictly associative. -/
theorem tensor_assoc_obj (X Y Z : P.Presented) : (X ⊗ Y) ⊗ Z = X ⊗ (Y ⊗ Z) :=
  congrArg P.obj (Obj.tensor_assoc _ _ _)


-- @@ L392-394 verbatim
/-- The unit is a strict left unit. -/
theorem unit_tensor_obj (X : P.Presented) : 𝟙_ P.Presented ⊗ X = X :=
  congrArg P.obj (Obj.unit_tensor _)


-- @@ L396-398 verbatim
/-- The unit is a strict right unit. -/
theorem tensor_unit_obj (X : P.Presented) : X ⊗ 𝟙_ P.Presented = X :=
  congrArg P.obj (Obj.tensor_unit _)


-- @@ L400-401 verbatim
theorem associator_eq (X Y Z : P.Presented) : α_ X Y Z = eqToIso (P.tensor_assoc_obj X Y Z) :=
  rfl


-- @@ L403-403 verbatim
theorem leftUnitor_eq (X : P.Presented) : λ_ X = eqToIso (P.unit_tensor_obj X) := rfl


-- @@ L405-405 verbatim
theorem rightUnitor_eq (X : P.Presented) : ρ_ X = eqToIso (P.tensor_unit_obj X) := rfl


-- @@ L407-409 verbatim
theorem whiskerRight_eqToHom {X X' : P.Presented} (h : X = X') (Y : P.Presented) :
    eqToHom h ▷ Y = eqToHom (congrArg (· ⊗ Y) h) := by
  subst h; exact P.wR_id (P.toObj X) (P.toObj Y)


-- @@ L411-413 verbatim
theorem whiskerLeft_eqToHom (X : P.Presented) {Y Y' : P.Presented} (h : Y = Y') :
    X ◁ eqToHom h = eqToHom (congrArg (X ⊗ ·) h) := by
  subst h; exact P.wL_id (P.toObj X) (P.toObj Y)


-- @@ L415-415 verbatim
variable [S.IsEven]


-- @@ L417-433 verbatim
instance instMonoidalCategory : MonoidalCategory P.Presented where
  tensorHom_def _ _ := rfl
  id_tensorHom_id X Y := by
    change P.wR (𝟙 (P.obj (P.toObj X))) _ ≫ P.wL _ (𝟙 (P.obj (P.toObj Y))) = _
    rw [wR_id, wL_id, Category.comp_id]; rfl
  tensorHom_comp_tensorHom {X₁ Y₁ Z₁ X₂ Y₂ Z₂} f₁ f₂ g₁ g₂ :=
    (P.tensor_comp_aux (a := P.toObj X₁) (a' := P.toObj Y₁) (a'' := P.toObj Z₁)
      (b := P.toObj X₂) (b' := P.toObj Y₂) (b'' := P.toObj Z₂) f₁ g₁ f₂ g₂).symm
  whiskerLeft_id X Y := P.wL_id (P.toObj X) (P.toObj Y)
  id_whiskerRight X Y := P.wR_id (P.toObj X) (P.toObj Y)
  associator_naturality {X₁ X₂ X₃ Y₁ Y₂ Y₃} f₁ f₂ f₃ :=
    P.associator_naturality_aux (a₁ := P.toObj X₁) (a₂ := P.toObj X₂) (a₃ := P.toObj X₃)
      (b₁ := P.toObj Y₁) (b₂ := P.toObj Y₂) (b₃ := P.toObj Y₃) f₁ f₂ f₃
  leftUnitor_naturality {X Y} f := P.unit_wL (b := P.toObj X) (b' := P.toObj Y) f
  rightUnitor_naturality {X Y} f := P.wR_unit (a := P.toObj X) (a' := P.toObj Y) f
  pentagon W X Y Z := P.pentagon_aux (P.toObj W) (P.toObj X) (P.toObj Y) (P.toObj Z)
  triangle X Y := P.triangle_aux (P.toObj X) (P.toObj Y)


-- @@ L435-439 verbatim
instance instMonoidalPreadditive : MonoidalPreadditive P.Presented where
  whiskerLeft_zero {X Y Z} := P.wL_zero (b := P.toObj Y) (b' := P.toObj Z) (P.toObj X)
  zero_whiskerRight {X Y Z} := P.wR_zero (a := P.toObj Y) (a' := P.toObj Z) (P.toObj X)
  whiskerLeft_add {X Y Z} f g := P.wL_add (b := P.toObj Y) (b' := P.toObj Z) (P.toObj X) f g
  add_whiskerRight {X Y Z} f g := P.wR_add (a := P.toObj Y) (a' := P.toObj Z) f g (P.toObj X)


-- @@ L441-443 verbatim
instance instMonoidalLinear : MonoidalLinear R P.Presented where
  whiskerLeft_smul X {Y Z} r f := P.wL_smul (b := P.toObj Y) (b' := P.toObj Z) (P.toObj X) r f
  smul_whiskerRight r {Y Z} f X := P.wR_smul (a := P.toObj Y) (a' := P.toObj Z) r f (P.toObj X)


-- @@ L445-445 verbatim
end Monoidal


-- @@ L447-447 verbatim
end Presentation


-- @@ L449-449 verbatim
end StringDiagrams


-- @@ L451-451 verbatim
end
