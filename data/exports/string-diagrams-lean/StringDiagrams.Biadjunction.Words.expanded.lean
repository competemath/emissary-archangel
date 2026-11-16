import StringDiagrams.Biadjunction.Basic
import StringDiagrams.Biadjunction.Zigzag


-- @@ L4-25 verbatim
/-!
# Duals of words

Let `D` be a duality on the colours of a signature, compatible with regions: the dual `c*` of a
colour `c` runs from the right region of `c` to its left region (`Signature.ColourDuality`).
The dual of a word `w = c₁ ⋯ c_k` is the reversed word of duals `w* = c_k* ⋯ c₁*`
(`Signature.ColourDuality.dualWord`, `dualWord_eq`), and the dual of a 1-morphism
`x : l ⟶ m` of the presented bicategory `P.Bicat` is the 1-morphism `x* : m ⟶ l` with the dual
word (`Presentation.dualHom`); duality reverses composition (`Presentation.dualHom_comp`).

Given biadjunctions `x ⊣⊢ x*` for all 1-morphisms `x` whose word is a single colour
(`Presentation.ColourBiadjunctions`; they are required at every placement of the colour, so
that no transport between different regions is ever needed), every 1-morphism is biadjoint to
its dual (`Presentation.biadj`). The biadjunction of a word `c w` is the composite
(`Biadjunction.comp`, built from Mathlib's `Bicategory.Adjunction.comp`) of the biadjunction of
the colour `c` and the biadjunction of the word `w` (`Presentation.biadjW`); hence its units and
counits are nested cups and caps (`Presentation.biadjW_cons_left_unit`). The biadjunction of the
empty word has identities as units and counits (`Presentation.nilBiadj`).

The chosen biadjunctions of colours are typically given by cups and caps
(`Presentation.ColourCupsCaps`, in `StringDiagrams.Biadjunction.Presented`).
-/


-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-29 verbatim
namespace StringDiagrams


-- @@ L31-31 verbatim
open CategoryTheory Bicategory


-- @@ L33-33 verbatim
universe w v u₀ u₁ u₂


-- @@ L35-35 verbatim
variable {S : Signature.{u₀, u₁, u₂}} {R : Type w} [CommRing R]


-- @@ L37-45 verbatim
/-- A duality on the colours of a signature, compatible with regions: the dual `c*` of a colour
`c` runs from the right region of `c` to its left region. -/
structure Signature.ColourDuality (S : Signature.{u₀, u₁, u₂}) where
  /-- The dual colour. -/
  dual : S.Colour → S.Colour
  /-- The left region of `c*` is the right region of `c`. -/
  src_dual : ∀ c, S.colourSrc (dual c) = S.colourTgt c
  /-- The right region of `c*` is the left region of `c`. -/
  tgt_dual : ∀ c, S.colourTgt (dual c) = S.colourSrc c


-- @@ L47-47 verbatim
namespace Signature.ColourDuality


-- @@ L49-49 verbatim
variable (D : S.ColourDuality)


-- @@ L51-52 verbatim
@[simp] theorem colourSrc_dual (c : S.Colour) : S.colourSrc (D.dual c) = S.colourTgt c :=
  D.src_dual c


-- @@ L54-55 verbatim
@[simp] theorem colourTgt_dual (c : S.Colour) : S.colourTgt (D.dual c) = S.colourSrc c :=
  D.tgt_dual c


-- @@ L57-60 verbatim
/-- The dual `w* = c_k* ⋯ c_1*` of a word `w = c_1 ⋯ c_k`. -/
def dualWord : List S.Colour → List S.Colour
  | [] => []
  | c :: w => dualWord w ++ [D.dual c]


-- @@ L62-62 verbatim
@[simp] theorem dualWord_nil : D.dualWord [] = [] := rfl


-- @@ L64-65 verbatim
@[simp] theorem dualWord_cons (c : S.Colour) (w : List S.Colour) :
    D.dualWord (c :: w) = D.dualWord w ++ [D.dual c] := rfl


-- @@ L67-70 verbatim
theorem dualWord_eq (w : List S.Colour) : D.dualWord w = (w.map D.dual).reverse := by
  induction w with
  | nil => rfl
  | cons c w ih => simp [ih]


-- @@ L72-74 verbatim
@[simp] theorem dualWord_append (u w : List S.Colour) :
    D.dualWord (u ++ w) = D.dualWord w ++ D.dualWord u := by
  simp [dualWord_eq]


-- @@ L76-86 verbatim
theorem ok_dualWord (r : S.Region) (w : List S.Colour) (h : S.ok r w) :
    S.ok (S.endR r w) (D.dualWord w) ∧ S.endR (S.endR r w) (D.dualWord w) = r := by
  induction w generalizing r with
  | nil => exact ⟨trivial, rfl⟩
  | cons c w ih =>
    obtain ⟨hc, hw⟩ := h
    obtain ⟨ih₁, ih₂⟩ := ih _ hw
    simp only [Signature.endR_cons, dualWord_cons, Signature.ok_append, Signature.endR_append,
      ih₂, Signature.ok_cons, Signature.ok_nil, and_true, Signature.endR_nil, D.src_dual,
      D.tgt_dual, hc]
    exact ih₁


-- @@ L88-88 verbatim
end Signature.ColourDuality


-- @@ L90-90 verbatim
namespace Presentation


-- @@ L92-92 verbatim
variable (P : Presentation.{w, v} S R) (D : S.ColourDuality)


-- @@ L94-97 verbatim
/-- The word `w`, read from the region `r`, as a 1-morphism of `P.Bicat`. -/
def wordHom (r : S.Region) (w : List S.Colour) (h : S.ok r w) :
    (⟨r⟩ : P.Bicat) ⟶ ⟨S.endR r w⟩ :=
  ⟨⟨r, w⟩, rfl, h, rfl⟩


-- @@ L99-102 verbatim
/-- The dual word `w*` as a 1-morphism of `P.Bicat`, in the opposite direction. -/
def dualWordHom (r : S.Region) (w : List S.Colour) (h : S.ok r w) :
    (⟨S.endR r w⟩ : P.Bicat) ⟶ ⟨r⟩ :=
  ⟨⟨S.endR r w, D.dualWord w⟩, rfl, (D.ok_dualWord r w h).1, (D.ok_dualWord r w h).2⟩


-- @@ L104-106 verbatim
/-- A single colour as a 1-morphism of `P.Bicat`. -/
abbrev colourHom (c : S.Colour) : (⟨S.colourSrc c⟩ : P.Bicat) ⟶ ⟨S.colourTgt c⟩ :=
  P.wordHom (S.colourSrc c) [c] ⟨rfl, trivial⟩


-- @@ L108-110 verbatim
/-- The dual of a single colour as a 1-morphism of `P.Bicat`. -/
abbrev dualColourHom (c : S.Colour) : (⟨S.colourTgt c⟩ : P.Bicat) ⟶ ⟨S.colourSrc c⟩ :=
  P.dualWordHom D (S.colourSrc c) [c] ⟨rfl, trivial⟩


-- @@ L112-121 verbatim
/-- The dual `x*` of a 1-morphism `x : l ⟶ m` of `P.Bicat`: the dual word, from `m` to `l`. -/
def dualHom {l m : P.Bicat} (x : l ⟶ m) : m ⟶ l :=
  ⟨⟨m.region, D.dualWord x.obj.word⟩, rfl,
    by
      have := (D.ok_dualWord _ _ x.wf).1
      rwa [← Obj.endR, x.endR_eq] at this,
    by
      have := (D.ok_dualWord _ _ x.wf).2
      rw [← Obj.endR, x.endR_eq] at this
      exact this.trans x.start_eq⟩


-- @@ L123-124 verbatim
@[simp] theorem dualHom_obj {l m : P.Bicat} (x : l ⟶ m) :
    (P.dualHom D x).obj = ⟨m.region, D.dualWord x.obj.word⟩ := rfl


-- @@ L126-130 verbatim
@[simp] theorem dualHom_comp {l m n : P.Bicat} (x : l ⟶ m) (y : m ⟶ n) :
    P.dualHom D (x ≫ y) = P.dualHom D y ≫ P.dualHom D x :=
  Bicat.Hom.ext (Obj.ext rfl (by
    show D.dualWord (x.obj.word ++ y.obj.word) = D.dualWord y.obj.word ++ D.dualWord x.obj.word
    simp))


-- @@ L132-137 verbatim
/-- The first letter `c` of a 1-morphism `x : l ⟶ m` whose word is `c :: w`, as a 1-morphism
`l ⟶ c.tgt`. -/
def headHom {l m : P.Bicat} (x : l ⟶ m) (c : S.Colour) (w : List S.Colour)
    (hx : x.obj.word = c :: w) : l ⟶ ⟨S.colourTgt c⟩ :=
  ⟨⟨l.region, [c]⟩, rfl,
    ⟨by have := x.wf; rw [Obj.WF, hx, x.start_eq] at this; exact this.1, trivial⟩, rfl⟩


-- @@ L139-145 verbatim
/-- The rest `w` of a 1-morphism `x : l ⟶ m` whose word is `c :: w`, as a 1-morphism
`c.tgt ⟶ m`. -/
def tailHom {l m : P.Bicat} (x : l ⟶ m) (c : S.Colour) (w : List S.Colour)
    (hx : x.obj.word = c :: w) : (⟨S.colourTgt c⟩ : P.Bicat) ⟶ m :=
  ⟨⟨S.colourTgt c, w⟩, rfl,
    by have := x.wf; rw [Obj.WF, hx] at this; exact this.2,
    by have := x.endR_eq; rw [Obj.endR, hx] at this; exact this⟩


-- @@ L147-151 verbatim
theorem headHom_comp_tailHom {l m : P.Bicat} (x : l ⟶ m) (c : S.Colour) (w : List S.Colour)
    (hx : x.obj.word = c :: w) : P.headHom x c w hx ≫ P.tailHom x c w hx = x :=
  Bicat.Hom.ext (Obj.ext x.start_eq.symm (by
    show [c] ++ w = x.obj.word
    rw [hx]; rfl))


-- @@ L153-156 verbatim
theorem dualHom_tail_comp_head {l m : P.Bicat} (x : l ⟶ m) (c : S.Colour) (w : List S.Colour)
    (hx : x.obj.word = c :: w) :
    P.dualHom D (P.tailHom x c w hx) ≫ P.dualHom D (P.headHom x c w hx) = P.dualHom D x := by
  rw [← dualHom_comp, headHom_comp_tailHom]


-- @@ L158-158 verbatim
variable {P D} [S.IsEven]


-- @@ L160-163 verbatim
/-- Transport of a biadjunction along equalities of 1-morphisms. -/
def _root_.StringDiagrams.Biadjunction.congr {B : Type*} [Bicategory B] {a b : B}
    {f f' : a ⟶ b} {g g' : b ⟶ a} (Q : f ⊣⊢ g) (hf : f = f') (hg : g = g') : f' ⊣⊢ g' :=
  hf ▸ hg ▸ Q


-- @@ L165-166 verbatim
@[simp] theorem _root_.StringDiagrams.Biadjunction.congr_rfl {B : Type*} [Bicategory B]
    {a b : B} {f : a ⟶ b} {g : b ⟶ a} (Q : f ⊣⊢ g) : Q.congr rfl rfl = Q := rfl


-- @@ L168-184 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The biadjunction of a 1-morphism with the empty word (and its dual): all units and counits
are identities, retyped. -/
def nilBiadj {l m : P.Bicat} (x : l ⟶ m) (hx : x.obj.word = []) : x ⊣⊢ P.dualHom D x :=
  have hl : l = m := Bicat.ext (by
    have := x.endR_eq; rw [Obj.endR, hx, x.start_eq] at this; exact this)
  have e₁ : ∀ {a : Obj S} (h : a = a), P.diag (eqToHom h) = 𝟙 _ := fun h => by simp
  { left := adjunctionOfZigzag x (P.dualHom D x)
      (eqToHom (Obj.ext x.start_eq.symm (by simp [Obj.tensor, hx])))
      (eqToHom (Obj.ext rfl (by simp [Obj.tensor, hx])))
      (by rw [← P.diag_id]; exact P.diag_eq_of_layers_eq (by simp))
      (by rw [← P.diag_id]; exact P.diag_eq_of_layers_eq (by simp))
    right := adjunctionOfZigzag (P.dualHom D x) x
      (eqToHom (Obj.ext rfl (by simp [Obj.tensor, hx])))
      (eqToHom (Obj.ext (by exact x.start_eq) (by simp [Obj.tensor, hx])))
      (by rw [← P.diag_id]; exact P.diag_eq_of_layers_eq (by simp))
      (by rw [← P.diag_id]; exact P.diag_eq_of_layers_eq (by simp)) }


-- @@ L186-189 verbatim
/-- Chosen biadjunctions `c ⊣⊢ c*` for all colours, at every placement: for every 1-morphism
`x` of `P.Bicat` whose word is a single colour `c`, a biadjunction `x ⊣⊢ x*`. -/
abbrev ColourBiadjunctions (P : Presentation.{w, v} S R) (D : S.ColourDuality) : Type _ :=
  ∀ {l m : P.Bicat} (x : l ⟶ m) (c : S.Colour), x.obj.word = [c] → (x ⊣⊢ P.dualHom D x)


-- @@ L191-191 verbatim
variable (B : ColourBiadjunctions P D)


-- @@ L193-201 verbatim
/-- The biadjunction `x ⊣⊢ x*` of a 1-morphism of `P.Bicat` whose word is `w`, composed from the
biadjunctions of its colours (`Biadjunction.comp`); its units and counits are nested cups and
caps. -/
def biadjW : (w : List S.Colour) → {l m : P.Bicat} → (x : l ⟶ m) → x.obj.word = w →
    (x ⊣⊢ P.dualHom D x)
  | [], _, _, x, hx => nilBiadj x hx
  | c :: w, _, _, x, hx =>
    ((B (P.headHom x c w hx) c rfl).comp (biadjW w (P.tailHom x c w hx) rfl)).congr
      (P.headHom_comp_tailHom x c w hx) (P.dualHom_tail_comp_head D x c w hx)


-- @@ L203-204 verbatim
/-- The biadjunction `x ⊣⊢ x*` of an arbitrary 1-morphism of `P.Bicat`. -/
def biadj {l m : P.Bicat} (x : l ⟶ m) : x ⊣⊢ P.dualHom D x := biadjW B x.obj.word x rfl


-- @@ L206-206 verbatim
end Presentation


-- @@ L208-208 verbatim
end StringDiagrams
