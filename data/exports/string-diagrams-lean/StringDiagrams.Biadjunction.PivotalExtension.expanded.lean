import StringDiagrams.Biadjunction.Presented


-- @@ L3-27 verbatim
/-!
# The pivotal extension of a presentation

Given a signature `S` with a duality `D` on its colours (compatible with regions), the pivotal
extension `S.pivotal D` has the same regions and colours, the original generators
(`PivotalGen.gen`), and for every colour `c` a cup `1 ⟶ c c*` in the left region of `c` and a
cap `c* c ⟶ 1` in the right region of `c` (`PivotalGen.cup`, `PivotalGen.cap`). The pivotal
extension `P.pivotal D` of a presentation `P` imposes the relations of `P` (on the original
diagrams, `LinDiagram.toPivotal`) and the two zigzag relations of every colour
(`Pivotal.zigL`, `Pivotal.zigR`); further relations can be added with
`Presentation.addRels`.

For an involution (`c** = c`, `Signature.ColourInvolution`) and any presentation `Q` of the
pivotal extension in which the zigzag relations hold (`Presentation.PivotalZigzags`):

* every colour is biadjoint to its dual: `c ⊣ c*` by the cup and the cap of `c`, and `c* ⊣ c`
  by the cup and the cap of `c*` (`Presentation.pivotalCupsCaps`,
  `Presentation.pivotalBiadj`); hence every word is biadjoint to its dual word;
* the cups and the caps are cyclic (`Presentation.pivotal_isCyclic_cup`,
  `Presentation.pivotal_isCyclic_cap`), because the biadjunction of `c*` is the exchange of the
  biadjunction of `c` (`Presentation.pivotalBiadj_symm_heq`);
* **rotation invariance** (`Presentation.pivotal_isCyclic`): if every original generator is
  cyclic for the biadjunctions of its boundary words, then every 2-morphism of the presented
  bicategory is cyclic, and `Presentation.pivotalStructure` is a pivotal structure on it.
-/


-- @@ L29-29 verbatim
noncomputable section


-- @@ L31-31 verbatim
namespace StringDiagrams


-- @@ L33-33 verbatim
open CategoryTheory Bicategory Biadjunction


-- @@ L35-35 verbatim
universe w v u₀ u₁ u₂


-- @@ L37-40 verbatim
/-- A duality on colours which is an involution: `c** = c`. -/
structure Signature.ColourInvolution (S : Signature.{u₀, u₁, u₂}) extends S.ColourDuality where
  /-- The dual of the dual of a colour is the colour. -/
  dual_dual : ∀ c, dual (dual c) = c


-- @@ L42-50 verbatim
/-- Generators of the pivotal extension: the original generators, and a cup and a cap for every
colour. -/
inductive PivotalGen (G : Type u₂) (C : Type u₁) : Type (max u₁ u₂)
  /-- An original generator. -/
  | gen (g : G)
  /-- The cup `1 ⟶ c c*` in the left region of `c`. -/
  | cup (c : C)
  /-- The cap `c* c ⟶ 1` in the right region of `c`. -/
  | cap (c : C)


-- @@ L52-52 verbatim
variable {S : Signature.{u₀, u₁, u₂}}


-- @@ L54-84 verbatim
/-- The pivotal extension of a signature with a duality on colours: the same regions and
colours, the original generators, and for every colour `c` a cup `1 ⟶ c c*` (in the left region
of `c`) and a cap `c* c ⟶ 1` (in the right region of `c`). -/
@[simps colourSrc colourTgt]
def Signature.pivotal (S : Signature.{u₀, u₁, u₂}) (D : S.ColourDuality) :
    Signature.{u₀, u₁, max u₁ u₂} where
  Region := S.Region
  Colour := S.Colour
  colourSrc := S.colourSrc
  colourTgt := S.colourTgt
  Gen := PivotalGen S.Gen S.Colour
  dom
    | .gen g => S.dom g
    | .cup _ => []
    | .cap c => [D.dual c, c]
  cod
    | .gen g => S.cod g
    | .cup c => [c, D.dual c]
    | .cap _ => []
  left
    | .gen g => S.left g
    | .cup c => S.colourSrc c
    | .cap c => S.colourTgt c
  right
    | .gen g => S.right g
    | .cup c => S.colourSrc c
    | .cap c => S.colourTgt c
  odd
    | .gen g => S.odd g
    | .cup _ => false
    | .cap _ => false


-- @@ L86-86 verbatim
namespace Signature


-- @@ L88-88 verbatim
variable (D : S.ColourDuality)


-- @@ L90-91 verbatim
instance pivotal_isEven [S.IsEven] : (S.pivotal D).IsEven :=
  ⟨fun g => by cases g <;> simp [pivotal, IsEven.odd_eq_false]⟩


-- @@ L93-98 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp] theorem pivotal_ok (r : S.Region) (w : List S.Colour) :
    (S.pivotal D).ok r w ↔ S.ok r w := by
  induction w generalizing r with
  | nil => simp
  | cons c w ih => exact and_congr Iff.rfl (ih _)


-- @@ L100-104 verbatim
@[simp] theorem pivotal_endR (r : S.Region) (w : List S.Colour) :
    (S.pivotal D).endR r w = S.endR r w := by
  induction w generalizing r with
  | nil => rfl
  | cons c w ih => exact ih _


-- @@ L106-106 verbatim
variable {D}


-- @@ L108-108 verbatim
@[simp] theorem pivotal_dom_gen (g : S.Gen) : (S.pivotal D).dom (.gen g) = S.dom g := rfl

-- @@ L109-109 verbatim
@[simp] theorem pivotal_cod_gen (g : S.Gen) : (S.pivotal D).cod (.gen g) = S.cod g := rfl

-- @@ L110-110 verbatim
@[simp] theorem pivotal_left_gen (g : S.Gen) : (S.pivotal D).left (.gen g) = S.left g := rfl

-- @@ L111-111 verbatim
@[simp] theorem pivotal_right_gen (g : S.Gen) : (S.pivotal D).right (.gen g) = S.right g := rfl

-- @@ L112-112 verbatim
@[simp] theorem pivotal_odd_gen (g : S.Gen) : (S.pivotal D).odd (.gen g) = S.odd g := rfl


-- @@ L114-114 verbatim
@[simp] theorem pivotal_dom_cup (c : S.Colour) : (S.pivotal D).dom (.cup c) = [] := rfl

-- @@ L115-116 verbatim
@[simp] theorem pivotal_cod_cup (c : S.Colour) :
    (S.pivotal D).cod (.cup c) = [c, D.dual c] := rfl

-- @@ L117-118 verbatim
@[simp] theorem pivotal_left_cup (c : S.Colour) :
    (S.pivotal D).left (.cup c) = S.colourSrc c := rfl

-- @@ L119-120 verbatim
@[simp] theorem pivotal_right_cup (c : S.Colour) :
    (S.pivotal D).right (.cup c) = S.colourSrc c := rfl

-- @@ L121-121 verbatim
@[simp] theorem pivotal_odd_cup (c : S.Colour) : (S.pivotal D).odd (.cup c) = false := rfl


-- @@ L123-124 verbatim
@[simp] theorem pivotal_dom_cap (c : S.Colour) :
    (S.pivotal D).dom (.cap c) = [D.dual c, c] := rfl

-- @@ L125-125 verbatim
@[simp] theorem pivotal_cod_cap (c : S.Colour) : (S.pivotal D).cod (.cap c) = [] := rfl

-- @@ L126-127 verbatim
@[simp] theorem pivotal_left_cap (c : S.Colour) :
    (S.pivotal D).left (.cap c) = S.colourTgt c := rfl

-- @@ L128-129 verbatim
@[simp] theorem pivotal_right_cap (c : S.Colour) :
    (S.pivotal D).right (.cap c) = S.colourTgt c := rfl

-- @@ L130-130 verbatim
@[simp] theorem pivotal_odd_cap (c : S.Colour) : (S.pivotal D).odd (.cap c) = false := rfl


-- @@ L132-132 verbatim
end Signature


-- @@ L134-134 verbatim
namespace Signature.ColourInvolution


-- @@ L136-136 verbatim
variable (E : S.ColourInvolution)


-- @@ L138-138 verbatim
attribute [simp] Signature.ColourInvolution.dual_dual


-- @@ L140-141 verbatim
theorem dual_injective : Function.Injective E.dual := fun c c' h => by
  rw [← E.dual_dual c, h, E.dual_dual]


-- @@ L143-144 verbatim
@[simp] theorem dual_inj {c c' : S.Colour} : E.dual c = E.dual c' ↔ c = c' :=
  E.dual_injective.eq_iff


-- @@ L146-148 verbatim
@[simp] theorem dualWord_dualWord (w : List S.Colour) :
    E.dualWord (E.dualWord w) = w := by
  simp [Signature.ColourDuality.dualWord_eq, List.map_reverse, List.map_map, Function.comp_def]


-- @@ L150-150 verbatim
end Signature.ColourInvolution


-- @@ L152-152 verbatim
/-! ## The inclusion of the original diagrams -/


-- @@ L154-154 verbatim
variable (D : S.ColourDuality)


-- @@ L156-157 verbatim
/-- An object of the free 2-category on `S`, as an object for the pivotal extension. -/
def Obj.toPivotal (a : Obj S) : Obj (S.pivotal D) := ⟨a.start, a.word⟩


-- @@ L159-160 verbatim
/-- A layer of `S`, as a layer of the pivotal extension. -/
def Layer.toPivotal (L : Layer S) : Layer (S.pivotal D) := ⟨L.start, L.left, .gen L.gen, L.right⟩


-- @@ L162-162 verbatim
variable {D}


-- @@ L164-171 verbatim
theorem Layer.Valid.toPivotal {L : Layer S} (h : L.Valid) : (L.toPivotal D).Valid where
  left_ok := (Signature.pivotal_ok D _ _).2 h.left_ok
  left_end := (Signature.pivotal_endR D _ _).trans h.left_end
  dom_ok := (Signature.pivotal_ok D _ _).2 h.dom_ok
  dom_end := (Signature.pivotal_endR D _ _).trans h.dom_end
  cod_ok := (Signature.pivotal_ok D _ _).2 h.cod_ok
  cod_end := (Signature.pivotal_endR D _ _).trans h.cod_end
  right_ok := (Signature.pivotal_ok D _ _).2 h.right_ok


-- @@ L173-179 verbatim
theorem Chain.toPivotal {a b : Obj S} {ls : List (Layer S)} (h : Chain a ls b) :
    Chain (a.toPivotal D) (ls.map (Layer.toPivotal D)) (b.toPivotal D) := by
  induction ls generalizing a with
  | nil => cases h; rfl
  | cons L ls ih =>
    obtain ⟨hv, rfl, hc⟩ := h
    exact ⟨hv.toPivotal, rfl, ih hc⟩


-- @@ L181-181 verbatim
variable (D)


-- @@ L183-185 verbatim
/-- A diagram of `S`, as a diagram of the pivotal extension. -/
def Diagram.toPivotal {a b : Obj S} (d : a ⟶ b) : a.toPivotal D ⟶ b.toPivotal D :=
  ⟨(Diagram.layers d).map (Layer.toPivotal D), (Diagram.chain d).toPivotal⟩


-- @@ L187-190 verbatim
/-- A linear combination of diagrams of `S`, as one of the pivotal extension. -/
def LinDiagram.toPivotal {R : Type w} [CommRing R] {a b : Obj S} (f : LinDiagram R a b) :
    LinDiagram R (a.toPivotal D) (b.toPivotal D) :=
  Finsupp.mapDomain (Diagram.toPivotal D) f


-- @@ L192-192 verbatim
/-! ## Cups, caps and zigzags of the pivotal extension -/


-- @@ L194-194 verbatim
namespace Pivotal


-- @@ L196-200 verbatim
/-- The cup `1 ⟶ c c*`, as a diagram of the pivotal extension. -/
def cupD (c : S.Colour) : (Obj.nil (S.colourSrc c) : Obj (S.pivotal D)) ⟶
    ⟨S.colourSrc c, [c, D.dual c]⟩ :=
  Diagram.layer ⟨S.colourSrc c, [], .cup c, []⟩
    ⟨trivial, rfl, trivial, rfl, ⟨rfl, D.src_dual c, trivial⟩, D.tgt_dual c, trivial⟩ rfl rfl


-- @@ L202-207 verbatim
/-- The cap `c* c ⟶ 1`, as a diagram of the pivotal extension. -/
def capD (c : S.Colour) : (⟨S.colourTgt c, [D.dual c, c]⟩ : Obj (S.pivotal D)) ⟶
    Obj.nil (S.colourTgt c) :=
  Diagram.layer ⟨S.colourTgt c, [], .cap c, []⟩
    ⟨trivial, rfl, ⟨D.src_dual c, (D.tgt_dual c).symm, trivial⟩, rfl, trivial, rfl, trivial⟩
    rfl rfl


-- @@ L209-210 verbatim
/-- The colour `c` as an object of the pivotal extension. -/
abbrev colourObj (c : S.Colour) : Obj (S.pivotal D) := ⟨S.colourSrc c, [c]⟩


-- @@ L212-214 verbatim
/-- The dual colour `c*`, read from the right region of `c`, as an object of the pivotal
extension. -/
abbrev dualObj (c : S.Colour) : Obj (S.pivotal D) := ⟨S.colourTgt c, [D.dual c]⟩


-- @@ L216-216 verbatim
theorem colourObj_wf (c : S.Colour) : (colourObj D c).WF := ⟨rfl, trivial⟩


-- @@ L218-218 verbatim
theorem dualObj_wf (c : S.Colour) : (dualObj D c).WF := ⟨D.src_dual c, trivial⟩


-- @@ L220-224 verbatim
/-- The left zigzag `(cup ⊗ 1) ≫ (1 ⊗ cap)` on the colour `c`. -/
def zigL (c : S.Colour) : colourObj D c ⟶ colourObj D c :=
  Diagram.leftZigzag (x := colourObj D c) (y := dualObj D c) (cupD D c) (capD D c)
    (Obj.Composable.nil_left (colourObj_wf D c) rfl)
    ⟨colourObj_wf D c, rfl, ⟨D.src_dual c, (D.tgt_dual c).symm, trivial⟩⟩ rfl


-- @@ L226-230 verbatim
/-- The right zigzag `(1 ⊗ cup) ≫ (cap ⊗ 1)` on the dual colour `c*`. -/
def zigR (c : S.Colour) : dualObj D c ⟶ dualObj D c :=
  Diagram.rightZigzag (x := colourObj D c) (y := dualObj D c) (cupD D c) (capD D c)
    (Obj.Composable.nil_right (dualObj_wf D c) (D.tgt_dual c))
    ⟨⟨D.src_dual c, (D.tgt_dual c).symm, trivial⟩, rfl, dualObj_wf D c⟩ rfl


-- @@ L232-232 verbatim
end Pivotal


-- @@ L234-234 verbatim
/-! ## The pivotal extension of a presentation -/


-- @@ L236-236 verbatim
namespace Presentation


-- @@ L238-238 verbatim
variable {R : Type w} [CommRing R]


-- @@ L240-247 verbatim
/-- A presentation with additional relations. -/
@[simps]
def addRels (Q : Presentation.{w, v} S R) (ι : Type v) (dom cod : ι → Obj S)
    (rel : ∀ i, LinDiagram R (dom i) (cod i)) : Presentation.{w, v} S R where
  Rel := Q.Rel ⊕ ι
  dom | .inl i => Q.dom i | .inr i => dom i
  cod | .inl i => Q.cod i | .inr i => cod i
  rel | .inl i => Q.rel i | .inr i => rel i


-- @@ L249-264 verbatim
/-- The pivotal extension of a presentation: the relations of `P` (on the original diagrams),
and the two zigzag relations for every colour. -/
def pivotal (P : Presentation.{w, v} S R) : Presentation.{w, max u₁ v} (S.pivotal D) R where
  Rel := P.Rel ⊕ (S.Colour ⊕ S.Colour)
  dom
    | .inl i => (P.dom i).toPivotal D
    | .inr (.inl c) => Pivotal.colourObj D c
    | .inr (.inr c) => Pivotal.dualObj D c
  cod
    | .inl i => (P.cod i).toPivotal D
    | .inr (.inl c) => Pivotal.colourObj D c
    | .inr (.inr c) => Pivotal.dualObj D c
  rel
    | .inl i => (P.rel i).toPivotal D
    | .inr (.inl c) => LinDiagram.of (Pivotal.zigL D c) - LinDiagram.of (𝟙 _)
    | .inr (.inr c) => LinDiagram.of (Pivotal.zigR D c) - LinDiagram.of (𝟙 _)


-- @@ L266-269 verbatim
/-- The zigzag identities of the cups and caps of the pivotal extension hold in a presentation
`Q` of the pivotal extension. -/
def PivotalZigzags (Q : Presentation.{w, v} (S.pivotal D) R) : Prop :=
  ∀ c, Q.diag (Pivotal.zigL D c) = 𝟙 _ ∧ Q.diag (Pivotal.zigR D c) = 𝟙 _


-- @@ L271-273 verbatim
theorem pivotal_zigzags (P : Presentation.{w, v} S R) : (P.pivotal D).PivotalZigzags D :=
  fun c => ⟨((P.pivotal D).diag_eq_of_rel (.inr (.inl c)) rfl).trans (diag_id _ _),
    ((P.pivotal D).diag_eq_of_rel (.inr (.inr c)) rfl).trans (diag_id _ _)⟩


-- @@ L275-281 verbatim
theorem pivotal_addRels_zigzags (P : Presentation.{w, v} S R) (ι : Type (max u₁ v))
    (dom cod : ι → Obj (S.pivotal D)) (rel : ∀ i, LinDiagram R (dom i) (cod i)) :
    ((P.pivotal D).addRels ι dom cod rel).PivotalZigzags D :=
  fun c => ⟨(((P.pivotal D).addRels ι dom cod rel).diag_eq_of_rel (.inl (.inr (.inl c))) rfl).trans
      (diag_id _ _),
    (((P.pivotal D).addRels ι dom cod rel).diag_eq_of_rel (.inl (.inr (.inr c))) rfl).trans
      (diag_id _ _)⟩


-- @@ L283-283 verbatim
end Presentation


-- @@ L285-290 verbatim
/-- The duality of an involution, as a duality on the colours of the pivotal extension. -/
@[simps]
def Signature.ColourDuality.pivotal (D : S.ColourDuality) : (S.pivotal D).ColourDuality where
  dual := D.dual
  src_dual := D.src_dual
  tgt_dual := D.tgt_dual


-- @@ L292-297 verbatim
set_option backward.isDefEq.respectTransparency false in
@[simp] theorem Signature.ColourDuality.pivotal_dualWord (D : S.ColourDuality)
    (w : List S.Colour) : D.pivotal.dualWord w = D.dualWord w := by
  induction w with
  | nil => rfl
  | cons c w ih => simp [ih]


-- @@ L299-299 verbatim
namespace Presentation


-- @@ L301-301 verbatim
open Pivotal


-- @@ L303-304 verbatim
variable {R : Type w} [CommRing R] [S.IsEven] (E : S.ColourInvolution)
  (Q : Presentation.{w, v} (S.pivotal E.toColourDuality) R)


-- @@ L306-329 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The cups and caps of the pivotal extension exhibit every colour as biadjoint to its dual:
`c ⊣ c*` by the cup and the cap of `c`, and `c* ⊣ c` by the cup and the cap of `c*`
(transported along `c** = c`). -/
def pivotalCupsCaps (hz : Q.PivotalZigzags E.toColourDuality) :
    ColourCupsCaps Q E.toColourDuality.pivotal where
  cup c := cupD E.toColourDuality c
  cap c := capD E.toColourDuality c
  cup' c := Diagram.cast (cupD E.toColourDuality (E.dual c))
    (by rw [E.src_dual]; rfl) (Obj.ext (E.src_dual c) (by simp [E.dual_dual]))
  cap' c := Diagram.cast (capD E.toColourDuality (E.dual c))
    (Obj.ext (E.tgt_dual c) (by simp [E.dual_dual])) (by rw [E.tgt_dual]; rfl)
  left_zigzag c := diag_eq_id_of_layers _ _ rfl rfl (hz c).1
  right_zigzag c := diag_eq_id_of_layers _ _ rfl rfl (hz c).2
  left_zigzag' c := diag_eq_id_of_layers _ (zigL E.toColourDuality (E.dual c))
    (Obj.ext (E.src_dual c).symm rfl)
    (by simp [zigL, cupD, capD, Layer.wl, Layer.wr]; exact ⟨rfl, rfl, rfl⟩)
    (hz (E.dual c)).1
  right_zigzag' c := diag_eq_id_of_layers _ (zigR E.toColourDuality (E.dual c))
    (Obj.ext (E.tgt_dual c).symm (by simp [E.dual_dual]; rfl))
    (by
      simp [zigR, cupD, capD, Layer.wl, Layer.wr]
      exact ⟨rfl, rfl⟩)
    (hz (E.dual c)).2


-- @@ L331-334 verbatim
/-- The biadjunctions `c ⊣⊢ c*` of the colours of the pivotal extension, at every placement. -/
abbrev pivotalBiadj (hz : Q.PivotalZigzags E.toColourDuality) :
    ColourBiadjunctions Q E.toColourDuality.pivotal :=
  (Q.pivotalCupsCaps E hz).biadjunctions


-- @@ L336-336 verbatim
variable (hz : Q.PivotalZigzags E.toColourDuality)


-- @@ L338-353 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The biadjunction of `c*` is the exchange of the biadjunction of `c`. -/
theorem pivotalBiadj_symm_heq (c : S.Colour) :
    HEq (pivotalBiadj E Q hz (Q.colourHom c) c rfl).symm
      (pivotalBiadj E Q hz (Q.dualColourHom E.toColourDuality.pivotal c) (E.dual c) rfl) := by
  dsimp only [pivotalBiadj, ColourCupsCaps.biadjunctions, biadjunctionOfZigzag, Biadjunction.symm]
  refine Biadjunction.heq_mk ?_ ?_ ?_
  · exact Bicat.Hom.ext (Obj.ext rfl (by show [c] = [E.dual (E.dual c)]; rw [E.dual_dual]))
  · refine adjunctionOfZigzag_heq rfl ?_ ?_ ?_ _ _ _ _
    · exact Bicat.Hom.ext (Obj.ext rfl (by show [c] = [E.dual (E.dual c)]; rw [E.dual_dual]))
    · simp [pivotalCupsCaps]
    · simp [pivotalCupsCaps]
  · refine adjunctionOfZigzag_heq ?_ rfl ?_ ?_ _ _ _ _
    · exact Bicat.Hom.ext (Obj.ext rfl (by show [c] = [E.dual (E.dual c)]; rw [E.dual_dual]))
    · simp [pivotalCupsCaps, cupD, E.dual_dual]
    · simp [pivotalCupsCaps, capD, E.dual_dual]


-- @@ L355-359 verbatim
theorem pivotalBiadj_symm_isCyclic (c : S.Colour) :
    Biadjunction.IsCyclic (pivotalBiadj E Q hz (Q.colourHom c) c rfl).symm
      (pivotalBiadj E Q hz (Q.dualColourHom E.toColourDuality.pivotal c) (E.dual c) rfl) (𝟙 _) :=
  isCyclic_eqToHom rfl (Bicat.Hom.ext (Obj.ext rfl (by
    show [c] = [E.dual (E.dual c)]; rw [E.dual_dual]))) (pivotalBiadj_symm_heq E Q hz c)


-- @@ L361-385 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The cups of the pivotal extension are cyclic. -/
theorem pivotal_isCyclic_cup (c : S.Colour) (hg : (S.pivotal E.toColourDuality).GenValid (.cup c)) :
    Biadjunction.IsCyclic (biadj (pivotalBiadj E Q hz) (Q.genDom (.cup c) hg))
      (biadj (pivotalBiadj E Q hz) (Q.genCod (.cup c) hg)) (Q.gen2 (.cup c) hg) := by
  set xc := Q.colourHom c
  set yc := Q.dualColourHom E.toColourDuality.pivotal c
  have e : biadj (pivotalBiadj E Q hz) (Q.genDom (.cup c) hg) = Biadjunction.id _ := nilBiadj_id _ rfl
  rw [e]
  have k₁ := isCyclic_left_unit (pivotalBiadj E Q hz xc c rfl)
  have k₂ := (pivotalBiadj_symm_isCyclic E Q hz c).whiskerLeft (pivotalBiadj E Q hz xc c rfl)
  have k₃ := (isCyclic_biadj_single (pivotalBiadj E Q hz) xc c rfl).inv.hcomp
    (isCyclic_biadj_single (pivotalBiadj E Q hz) yc (E.dual c) rfl).inv
  have k₄ := isCyclic_biadj_comp (pivotalBiadj E Q hz) xc yc
  have k₅ := isCyclic_biadj_eqToHom (pivotalBiadj E Q hz) (show xc ≫ yc = Q.genCod (.cup c) hg from rfl)
  have key := k₁.comp (k₂.comp (k₃.comp (k₄.comp k₅)))
  simp only [IsIso.inv_id, Bicategory.id_whiskerRight, Bicategory.whiskerLeft_id,
    Category.id_comp, Category.comp_id, eqToHom_refl] at key
  have e₃ : (pivotalBiadj E Q hz xc c rfl).left.unit = Q.gen2 (.cup c) hg := by
    show Q.diag _ = Q.diag _
    exact Q.diag_eq_of_layers_eq rfl
  have e₄ : (pivotalBiadj E Q hz xc c rfl).left.unit ≫ 𝟙 (xc ≫ yc) = Q.gen2 (.cup c) hg :=
    (Category.comp_id _).trans e₃
  rw [e₄] at key
  exact key


-- @@ L387-415 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The caps of the pivotal extension are cyclic. -/
theorem pivotal_isCyclic_cap (c : S.Colour) (hg : (S.pivotal E.toColourDuality).GenValid (.cap c)) :
    Biadjunction.IsCyclic (biadj (pivotalBiadj E Q hz) (Q.genDom (.cap c) hg))
      (biadj (pivotalBiadj E Q hz) (Q.genCod (.cap c) hg)) (Q.gen2 (.cap c) hg) := by
  set xc := Q.colourHom c
  set yc := Q.dualColourHom E.toColourDuality.pivotal c
  have e : biadj (pivotalBiadj E Q hz) (Q.genCod (.cap c) hg) = Biadjunction.id _ :=
    nilBiadj_id _ rfl
  rw [e]
  have k₀ := isCyclic_biadj_eqToHom (pivotalBiadj E Q hz)
    (show Q.genDom (.cap c) hg = yc ≫ xc from rfl)
  have k₁ := isCyclic_biadj_comp_symm (pivotalBiadj E Q hz) yc xc
  have k₂ := (isCyclic_biadj_single (pivotalBiadj E Q hz) yc (E.dual c) rfl).hcomp
    (isCyclic_biadj_single (pivotalBiadj E Q hz) xc c rfl)
  have k₃ := (pivotalBiadj_symm_isCyclic E Q hz c).inv.whiskerRight (pivotalBiadj E Q hz xc c rfl)
  have k₄ := isCyclic_left_counit (pivotalBiadj E Q hz xc c rfl)
  have key := k₀.comp (k₁.comp (k₂.comp (k₃.comp k₄)))
  simp only [IsIso.inv_id, Bicategory.id_whiskerRight, Bicategory.whiskerLeft_id,
    Category.id_comp, Category.comp_id, eqToHom_refl] at key
  have e₃ : (pivotalBiadj E Q hz xc c rfl).left.counit = Q.gen2 (.cap c) hg := by
    show Q.diag _ = Q.diag _
    exact Q.diag_eq_of_layers_eq rfl
  have e₄ : 𝟙 (Q.dualHom E.toColourDuality.pivotal (Q.colourHom c)) ▷ xc ≫
      (pivotalBiadj E Q hz xc c rfl).left.counit = Q.gen2 (.cap c) hg := by
    rw [Bicategory.id_whiskerRight]
    exact (Category.id_comp _).trans e₃
  rw [e₄] at key
  exact key


-- @@ L417-431 verbatim
/-- **Rotation invariance in the pivotal extension.** If every original generator is cyclic
for the biadjunctions of its boundary words (built from the cups and caps), then every
2-morphism of the presented bicategory is cyclic: its two mates (rotations by the cups and caps
on either side) agree. -/
theorem pivotal_isCyclic
    (hgen : ∀ (g : S.Gen) (hg : (S.pivotal E.toColourDuality).GenValid (.gen g)),
      Biadjunction.IsCyclic (biadj (pivotalBiadj E Q hz) (Q.genDom (.gen g) hg))
        (biadj (pivotalBiadj E Q hz) (Q.genCod (.gen g) hg)) (Q.gen2 (.gen g) hg))
    {l m : Q.Bicat} {x x' : l ⟶ m} (θ : x ⟶ x') :
    Biadjunction.IsCyclic (biadj (pivotalBiadj E Q hz) x) (biadj (pivotalBiadj E Q hz) x') θ :=
  isCyclic_of_generators _ (fun g hg => by
    cases g with
    | gen g => exact hgen g hg
    | cup c => exact pivotal_isCyclic_cup E Q hz c hg
    | cap c => exact pivotal_isCyclic_cap E Q hz c hg) θ


-- @@ L433-445 verbatim
/-- The pivotal structure on the bicategory presented by `Q`, when every original generator is
cyclic. -/
@[instance_reducible]
def pivotalStructure
    (hgen : ∀ (g : S.Gen) (hg : (S.pivotal E.toColourDuality).GenValid (.gen g)),
      Biadjunction.IsCyclic (biadj (pivotalBiadj E Q hz) (Q.genDom (.gen g) hg))
        (biadj (pivotalBiadj E Q hz) (Q.genCod (.gen g) hg)) (Q.gen2 (.gen g) hg)) :
    StringDiagrams.Pivotal Q.Bicat :=
  pivotalOfGenerators _ (fun g hg => by
    cases g with
    | gen g => exact hgen g hg
    | cup c => exact pivotal_isCyclic_cup E Q hz c hg
    | cap c => exact pivotal_isCyclic_cap E Q hz c hg)


-- @@ L447-447 verbatim
end Presentation


-- @@ L449-449 verbatim
end StringDiagrams
