import StringDiagrams.Biadjunction.PivotalExtension


-- @@ L3-24 verbatim
/-!
# Example: the walking biadjunction with a cyclic dot

Two regions `a`, `b`, strands `E : a → b` and `F : b → a` with `E* = F`, and one generator, a dot
`E ⟶ E`. The pivotal extension adds the four cups and caps (the cup and the cap of `E` and of
`F`) and the four zigzag relations; we add one more relation, `rotR = rotL`, saying that the two
rotations of the dot to the strand `F` (by the cup and cap of `E ⊣ F`, and by those of `F ⊣ E`)
agree.

* `biadjEF`: the biadjunction `E ⊣⊢ F`, whose units and counits are the cups and caps
  (`biadjEF_left_unit`, ...); words such as `E F E` are biadjoint to their dual words.
* `dot_isCyclic`: the dot is cyclic, from the relation; `isCyclic`: hence, by rotation
  invariance, every 2-morphism is cyclic, and `pivotal` is a pivotal structure.
* `dotF_eq_rotR`, `dotF_eq_rotL`: the mate of the dot is the class of either rotated diagram.
* `dot_slide_cup`, `dot_slide_cup'`: the dot slides along both cups to the same dot on `F`.
* `dottedBubble`: a dotted bubble, an endomorphism of the empty word `𝟙 a`;
  `bubble_eq_trace_snakes`: the plain `E`-bubble equals the trace of the endomorphism
  `snakeDown ≫ snakeUp` of `E F E`, a consequence of rotation invariance (the trace of `α ≫ β`
  equals the trace of `β ≫ α`) and the zigzag relation.

The example is generic: there are no weights and no relations beyond zigzags and cyclicity.
-/


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-28 verbatim
namespace StringDiagrams.WalkingBiadjunction


-- @@ L30-30 verbatim
open CategoryTheory Bicategory Biadjunction Presentation


-- @@ L32-36 verbatim
/-- The two regions. -/
inductive Reg
  | a
  | b
  deriving DecidableEq


-- @@ L38-42 verbatim
/-- The two strands: `E` from `a` to `b` and `F` from `b` to `a`. -/
inductive Col
  | E
  | F
  deriving DecidableEq


-- @@ L44-47 verbatim
/-- The single generator: a dot on the strand `E`. -/
inductive Gen
  | dot
  deriving DecidableEq


-- @@ L49-63 verbatim
/-- The signature: two regions, the strands `E : a → b`, `F : b → a`, and a dot `E ⟶ E`. -/
def sig : Signature where
  Region := Reg
  Colour := Col
  colourSrc
    | .E => .a
    | .F => .b
  colourTgt
    | .E => .b
    | .F => .a
  Gen := Gen
  dom _ := [.E]
  cod _ := [.E]
  left _ := .a
  right _ := .b


-- @@ L65-65 verbatim
instance : sig.IsEven := ⟨fun _ => rfl⟩


-- @@ L67-74 verbatim
/-- `E* = F` and `F* = E`. -/
def inv : sig.ColourInvolution where
  dual
    | .E => .F
    | .F => .E
  src_dual c := by cases c <;> rfl
  tgt_dual c := by cases c <;> rfl
  dual_dual c := by cases c <;> rfl


-- @@ L76-77 verbatim
/-- The pivotal extension. -/
abbrev psig : Signature := sig.pivotal inv.toColourDuality


-- @@ L79-79 verbatim
instance : DecidableEq psig.Region := inferInstanceAs (DecidableEq Reg)

-- @@ L80-80 verbatim
instance : DecidableEq psig.Colour := inferInstanceAs (DecidableEq Col)


-- @@ L82-85 verbatim
/-- The dot on `F`, rotated using the cup and the cap of `E ⊣ F`. -/
def rotR : (⟨.b, [.F]⟩ : Obj psig) ⟶ ⟨.b, [.F]⟩ :=
  Diagram.mk [⟨.b, [.F], .cup .E, []⟩, ⟨.b, [.F], .gen .dot, [.F]⟩, ⟨.b, [], .cap .E, [.F]⟩]
    (by decide)


-- @@ L87-90 verbatim
/-- The dot on `F`, rotated using the cup and the cap of `F ⊣ E`. -/
def rotL : (⟨.b, [.F]⟩ : Obj psig) ⟶ ⟨.b, [.F]⟩ :=
  Diagram.mk [⟨.b, [], .cup .F, [.F]⟩, ⟨.b, [.F], .gen .dot, [.F]⟩, ⟨.b, [.F], .cap .F, []⟩]
    (by decide)


-- @@ L92-94 verbatim
/-- No relations among the original generators. -/
def pres₀ (R : Type) [CommRing R] : Presentation.{0, 0} sig R := ⟨Empty, Empty.elim, Empty.elim,
  fun i => i.elim⟩


-- @@ L96-96 verbatim
variable (R : Type) [CommRing R]


-- @@ L98-103 verbatim
/-- The walking biadjunction with a cyclic dot: the pivotal extension of `pres₀` (four cups and
caps and the four zigzag relations), with the relation `rotR = rotL`: the two rotations of the
dot agree. -/
def pres : Presentation.{0, 0} psig R :=
  ((pres₀ R).pivotal inv.toColourDuality).addRels Unit (fun _ => ⟨.b, [.F]⟩) (fun _ => ⟨.b, [.F]⟩)
    (fun _ => LinDiagram.of rotR - LinDiagram.of rotL)


-- @@ L105-106 verbatim
theorem zigzags : (pres R).PivotalZigzags inv.toColourDuality :=
  Presentation.pivotal_addRels_zigzags inv.toColourDuality (pres₀ R) Unit _ _ _


-- @@ L108-110 verbatim
/-- The biadjunctions of the strands. -/
abbrev B : ColourBiadjunctions (pres R) inv.toColourDuality.pivotal :=
  Presentation.pivotalBiadj inv (pres R) (zigzags R)


-- @@ L112-124 verbatim
/-- The dot is cyclic, by the relation `rotR = rotL`. -/
theorem dot_isCyclic (hg : psig.GenValid (.gen .dot)) :
    Biadjunction.IsCyclic (biadj (B R) ((pres R).genDom (.gen .dot) hg))
      (biadj (B R) ((pres R).genCod (.gen .dot) hg)) ((pres R).gen2 (.gen .dot) hg) := by
  rw [isCyclic_biadj_iff_single (B R) (c := .E) (c' := .E) rfl rfl]
  refine isCyclic_diag_of_rel (B R ((pres R).genDom (.gen .dot) hg) .E rfl)
    (B R ((pres R).genCod (.gen .dot) hg) .E rfl) _ rfl _ rfl _ rfl _ rfl
    (genDiag _ hg) (.inr ()) (r₁ := rotR) (r₂ := rotL) ?_ ?_ ?_ ?_ ?_
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl


-- @@ L126-130 verbatim
/-- Every 2-morphism of the walking biadjunction with a cyclic dot is cyclic: rotating any
diagram by the cups and caps on the left or on the right gives the same result. -/
theorem isCyclic {l m : (pres R).Bicat} {x x' : l ⟶ m} (θ : x ⟶ x') :
    Biadjunction.IsCyclic (biadj (B R) x) (biadj (B R) x') θ :=
  pivotal_isCyclic inv (pres R) (zigzags R) (fun g hg => by cases g; exact dot_isCyclic R hg) θ


-- @@ L132-134 verbatim
/-- The pivotal structure. -/
abbrev pivotal : StringDiagrams.Pivotal (pres R).Bicat :=
  pivotalStructure inv (pres R) (zigzags R) (fun g hg => by cases g; exact dot_isCyclic R hg)


-- @@ L136-136 verbatim
/-! ## The strands, their adjunctions, and the dot -/


-- @@ L138-139 verbatim
/-- The region `a`. -/
abbrev A : (pres R).Bicat := ⟨.a⟩


-- @@ L141-142 verbatim
/-- The region `b`. -/
abbrev Bo : (pres R).Bicat := ⟨.b⟩


-- @@ L144-145 verbatim
/-- The strand `E : a ⟶ b`. -/
abbrev strandE : A R ⟶ Bo R := (pres R).colourHom .E


-- @@ L147-148 verbatim
/-- The strand `F : b ⟶ a`, the dual of `E`. -/
abbrev strandF : Bo R ⟶ A R := (pres R).dualHom inv.toColourDuality.pivotal (strandE R)


-- @@ L150-151 verbatim
/-- `E ⊣⊢ F`, with units and counits the four cups and caps. -/
abbrev biadjEF : strandE R ⊣⊢ strandF R := B R (strandE R) .E rfl


-- @@ L153-155 verbatim
/-- The adjunction `E ⊣ F`: its unit is the cup of `E`, its counit the cap of `E`. -/
theorem biadjEF_left_unit :
    (biadjEF R).left.unit = (pres R).diag (Pivotal.cupD inv.toColourDuality .E) := rfl


-- @@ L157-158 verbatim
theorem biadjEF_left_counit :
    (biadjEF R).left.counit = (pres R).diag (Pivotal.capD inv.toColourDuality .E) := rfl


-- @@ L160-162 verbatim
/-- The adjunction `F ⊣ E`: its unit is the cup of `F`, its counit the cap of `F`. -/
theorem biadjEF_right_unit :
    (biadjEF R).right.unit = (pres R).diag (Pivotal.cupD inv.toColourDuality .F) := rfl


-- @@ L164-165 verbatim
theorem biadjEF_right_counit :
    (biadjEF R).right.counit = (pres R).diag (Pivotal.capD inv.toColourDuality .F) := rfl


-- @@ L167-169 verbatim
/-- The word `E F E` has the biadjoint `F E F` (the reversed word of duals). -/
example : ((pres R).dualHom inv.toColourDuality.pivotal
    (strandE R ≫ strandF R ≫ strandE R)).obj.word = [.F, .E, .F] := rfl


-- @@ L171-174 verbatim
/-- The word `E F E` is biadjoint to its dual, by nested cups and caps. -/
example : strandE R ≫ strandF R ≫ strandE R ⊣⊢
    (pres R).dualHom inv.toColourDuality.pivotal (strandE R ≫ strandF R ≫ strandE R) :=
  biadj (B R) _


-- @@ L176-178 verbatim
/-- The dot, as a 2-morphism `E ⟶ E`. -/
def dot : strandE R ⟶ strandE R :=
  (pres R).gen2 (.gen .dot) ⟨⟨rfl, trivial⟩, rfl, ⟨rfl, trivial⟩, rfl⟩


-- @@ L180-181 verbatim
/-- The dot, rotated to the strand `F` (its mate). -/
def dotF : strandF R ⟶ strandF R := rightMate (biadjEF R) (biadjEF R) (dot R)


-- @@ L183-185 verbatim
/-- The dot is cyclic for the biadjunction `E ⊣⊢ F`. -/
theorem dot_isCyclic_EF : Biadjunction.IsCyclic (biadjEF R) (biadjEF R) (dot R) :=
  (isCyclic_biadj_iff_single (B R) rfl rfl (dot R)).1 (isCyclic R (dot R))


-- @@ L187-189 verbatim
/-- The dot on `F` is the class of either rotated diagram. -/
theorem dotF_eq_rotR : dotF R = (pres R).diag rotR :=
  (rightMate_diag _ _ _ rfl _ rfl _).trans ((pres R).diag_eq_of_layers_eq rfl)


-- @@ L191-193 verbatim
theorem dotF_eq_rotL : dotF R = (pres R).diag rotL := by
  rw [dotF, (dot_isCyclic_EF R).eq]
  exact (leftMate_diag _ _ _ rfl _ rfl _).trans ((pres R).diag_eq_of_layers_eq rfl)


-- @@ L195-195 verbatim
/-! ## Sliding the dot along cups and caps -/


-- @@ L197-200 verbatim
/-- Sliding the dot along the cup of `E ⊣ F`: it moves to the strand `F`. -/
theorem dot_slide_cup :
    (biadjEF R).left.unit ≫ dot R ▷ strandF R = (biadjEF R).left.unit ≫ strandE R ◁ dotF R :=
  (biadjEF R).left_unit_comp_whiskerRight (biadjEF R) (dot R)


-- @@ L202-205 verbatim
/-- Sliding the dot along the cup of `F ⊣ E`: by cyclicity it becomes the same dot on `F`. -/
theorem dot_slide_cup' :
    (biadjEF R).right.unit ≫ strandF R ◁ dot R = (biadjEF R).right.unit ≫ dotF R ▷ strandE R :=
  (dot_isCyclic_EF R).right_unit_comp_whiskerLeft


-- @@ L207-207 verbatim
/-! ## Bubbles -/


-- @@ L209-209 verbatim
attribute [local instance] pivotal


-- @@ L211-213 verbatim
/-- The clockwise bubble in the region `a` with a dot on it: the right trace of the dot, an
endomorphism of the empty word `𝟙 a`. -/
abbrev dottedBubble : 𝟙 (A R) ⟶ 𝟙 (A R) := StringDiagrams.Pivotal.rightTrace (dot R)


-- @@ L215-219 verbatim
/-- A dot can be moved around a bubble: the trace of a composite does not depend on the order
of the factors (for any `α : E ⟶ f` and `β : f ⟶ E`). -/
theorem bubble_comp_comm {f : A R ⟶ Bo R} (α : strandE R ⟶ f) (β : f ⟶ strandE R) :
    StringDiagrams.Pivotal.rightTrace (α ≫ β) = StringDiagrams.Pivotal.rightTrace (β ≫ α) :=
  StringDiagrams.Pivotal.rightTrace_comp_comm α β


-- @@ L221-223 verbatim
/-- The snake `E ⟶ E F E` (a cup to the left of `E`). -/
def snakeUp : strandE R ⟶ strandE R ≫ strandF R ≫ strandE R :=
  (λ_ _).inv ≫ (biadjEF R).left.unit ▷ strandE R ≫ (α_ _ _ _).hom


-- @@ L225-227 verbatim
/-- The snake `E F E ⟶ E` (a cap to the right of `E`). -/
def snakeDown : strandE R ≫ strandF R ≫ strandE R ⟶ strandE R :=
  strandE R ◁ (biadjEF R).left.counit ≫ (ρ_ _).hom


-- @@ L229-236 verbatim
theorem snakeUp_comp_snakeDown : snakeUp R ≫ snakeDown R = 𝟙 _ := by
  have h := (biadjEF R).left.left_triangle
  rw [leftZigzag_eq] at h
  have e : snakeUp R ≫ snakeDown R = (λ_ _).inv ≫ ((biadjEF R).left.unit ▷ strandE R ≫
      (α_ _ _ _).hom ≫ strandE R ◁ (biadjEF R).left.counit) ≫ (ρ_ _).hom := by
    simp only [snakeUp, snakeDown, Category.assoc]
  rw [e, h]
  simp


-- @@ L238-245 verbatim
/-- **A consequence of rotation invariance.** The plain `E`-bubble equals the closed diagram
obtained by closing up the endomorphism `snakeDown ≫ snakeUp` of `E F E` (a cap followed by a
cup, with a through-strand), traced with the nested cups and caps of `E F E`. -/
theorem bubble_eq_trace_snakes :
    StringDiagrams.Pivotal.rightTrace (𝟙 (strandE R)) =
      StringDiagrams.Pivotal.rightTrace (snakeDown R ≫ snakeUp R) := by
  rw [← snakeUp_comp_snakeDown R]
  exact bubble_comp_comm R _ _


-- @@ L247-247 verbatim
end StringDiagrams.WalkingBiadjunction
