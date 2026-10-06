/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Exponential.Copies
import DescriptiveComplexity.Exponential.Expansion


-- @@ L9-45 verbatim
/-!
# Reading a structure over its subsets: the address expansion

The construction that puts a problem *one exponential up* without saying
anything about resources: an `DescriptiveComplexity.ExpExpansion` whose block is
a single unary relation variable, so that an assignment **is** a subset of the
instance and the expanded universe is its power set.

It is written once here, for an arbitrary relational vocabulary with a
designated binary symbol read as the order on the elements, because two problems
of this library are drawn on it – the wide machine
(`DescriptiveComplexity.Problems.Wide.Expansion`) and the wide tiling
(`DescriptiveComplexity.Problems.Wide.Tiling`). What a particular problem
supplies is only its *tags* and the choice of sentence at each symbol; what is
here is everything else:

* the block and the two vocabularies a defining sentence may be written in – one
  copy of the block for a unary symbol, two for a binary one;
* the dictionary between an assignment and the address it is
  (`AddrExp.bits`, `AddrExp.assign`);
* the guards of the base vocabulary, and the atoms of the block;
* and the five sentences an expansion of this shape ever needs: a mark of the
  base (`AddrExp.markS`), a binary attribute of it (`AddrExp.binS`), being a
  singleton (`AddrExp.singleS`, the domain sentence that keeps the base universe
  visible), the binary-number order on addresses (`AddrExp.addrLeS`) and a
  relation read at the *initial segment* an element cuts (`AddrExp.inpS`).

Every quantifier in them ranges over the base – an element, never an address –
which is what keeps them first-order there.

The order on addresses is the **binary-number order**
(`DescriptiveComplexity.WMSetLe`): one subset is below another when, at the
least element where they differ, the second contains it and the first does not.
That relation and the initial segment an element cuts
(`DescriptiveComplexity.WMDown`) are stated here for an arbitrary relation on an
arbitrary type, since both the problems and their expansions read them.
-/


-- @@ L47-47 verbatim
namespace DescriptiveComplexity


-- @@ L49-49 verbatim
open FirstOrder


-- @@ L51-51 verbatim
open Language Structure


-- @@ L53-57 verbatim
/-! ### Addresses

The two things said about an address – how it compares with another, and which
initial segment it is – stated for an arbitrary order relation, so that they
transport along an equivalence without mentioning a structure. -/


-- @@ L59-59 verbatim
section Addresses


-- @@ L61-61 verbatim
variable {α : Type}


-- @@ L63-70 verbatim
/-- **The binary-number order on addresses**: the two subsets agree, or, at some
element where the first is out and the second in, they agree at every strictly
smaller element. Written with the strict order spelled out as
`Le y x ∧ ¬ Le x y`, which is the shape the defining sentence of the expansion
realizes to. -/
def WMSetLe (Le : α → α → Prop) (s t : α → Prop) : Prop :=
  (∀ x, s x ↔ t x) ∨
    ∃ x, (∀ y, (Le y x ∧ ¬Le x y) → (s y ↔ t y)) ∧ ¬s x ∧ t x


-- @@ L72-74 verbatim
/-- **The address of an element**: the initial segment it cuts, which is where
the element's input symbol is written. -/
def WMDown (Le : α → α → Prop) (s : α → Prop) (x : α) : Prop := ∀ y, s y ↔ Le y x


-- @@ L76-81 verbatim
/-- **The cell of an element on a file**: the initial segment it cuts among the
elements the file has a register for. The wide machine's register channel and
the wide tiling's bottom row are both described at these addresses – a *file* of
cells rather than the ruler of all the segments. -/
def WMFileSeg (Le : α → α → Prop) (Has : α → Prop) (s : α → Prop) (x : α) : Prop :=
  ∀ y, s y ↔ (Le y x ∧ Has y)


-- @@ L83-105 verbatim
/-- The order on addresses transports along an equivalence of the index type. -/
theorem wmSetLe_congr {β : Type} (u : α ≃ β) {LeA : α → α → Prop} {LeB : β → β → Prop}
    (hle : ∀ x y, LeA x y ↔ LeB (u x) (u y)) (s t : α → Prop) :
    WMSetLe LeA s t ↔
      WMSetLe LeB (fun y => s (u.symm y)) (fun y => t (u.symm y)) := by
  have hagree : (∀ x, s x ↔ t x) ↔ ∀ y, s (u.symm y) ↔ t (u.symm y) :=
    ⟨fun h y => h _, fun h x => by simpa using h (u x)⟩
  refine or_congr hagree ⟨fun ⟨x, hbelow, hs, ht⟩ => ⟨u x, fun y hy => ?_, ?_, ?_⟩,
    fun ⟨x, hbelow, hs, ht⟩ => ⟨u.symm x, fun y hy => ?_, hs, ht⟩⟩
  · have h1 : LeA (u.symm y) x := (hle (u.symm y) x).mpr (by
      rw [Equiv.apply_symm_apply]; exact hy.1)
    have h2 : ¬LeA x (u.symm y) := fun hc => hy.2 (by
      have h3 := (hle x (u.symm y)).mp hc
      rwa [Equiv.apply_symm_apply] at h3)
    exact hbelow (u.symm y) ⟨h1, h2⟩
  · simpa using hs
  · simpa using ht
  · have h1 : LeB (u y) x := by
      have h3 := (hle y (u.symm x)).mp hy.1
      rwa [Equiv.apply_symm_apply] at h3
    have h2 : ¬LeB x (u y) := fun hc => hy.2 ((hle (u.symm x) y).mpr (by
      rwa [Equiv.apply_symm_apply]))
    simpa using hbelow (u y) ⟨h1, h2⟩


-- @@ L107-117 verbatim
/-- The initial segment of an element transports along an equivalence. -/
theorem wmDown_congr {β : Type} (u : α ≃ β) {LeA : α → α → Prop} {LeB : β → β → Prop}
    (hle : ∀ x y, LeA x y ↔ LeB (u x) (u y)) (s : α → Prop) (x : α) :
    WMDown LeA s x ↔ WMDown LeB (fun y => s (u.symm y)) (u x) := by
  refine ⟨fun h y => ?_, fun h y => ?_⟩
  · change s (u.symm y) ↔ LeB y (u x)
    rw [h (u.symm y), hle (u.symm y) x, Equiv.apply_symm_apply]
  · have h1 : s (u.symm (u y)) ↔ LeB (u y) (u x) := h (u y)
    rw [Equiv.symm_apply_apply] at h1
    rw [h1]
    exact (hle y x).symm


-- @@ L119-119 verbatim
end Addresses


-- @@ L121-121 verbatim
namespace AddrExp


-- @@ L123-123 verbatim
variable (L : Language.{0, 0})


-- @@ L125-125 verbatim
/-! ### The vocabularies -/


-- @@ L127-129 verbatim
/-- The ordered vocabulary of wide-machine instances: what an expansion's
sentences may read besides the block. -/
abbrev aeOrd : Language.{0, 0} := L.sum Language.order


-- @@ L131-135 verbatim
/-- **The block whose assignments are the addresses**: a single unary relation
variable, so an assignment is a subset of the instance. -/
abbrev addrBlock : SOBlock where
  ι := Unit
  arity := fun _ => 1


-- @@ L137-138 verbatim
/-- The base vocabulary expanded by one copy of the block. -/
abbrev aeLang1 : Language.{0, 0} := (aeOrd L).sum addrBlock.lang


-- @@ L140-141 verbatim
/-- The base vocabulary expanded by two copies of the block. -/
abbrev aeLang2 : Language.{0, 0} := (aeLang1 L).sum addrBlock.lang


-- @@ L143-143 verbatim
variable {L}


-- @@ L145-147 verbatim
/-- A unary symbol of the instance, in the ordered vocabulary: a raw `Sum.inl`
does not elaborate at that type. -/
abbrev aeSym₁ (r : L.Relations 1) : (aeOrd L).Relations 1 := Sum.inl r


-- @@ L149-150 verbatim
/-- A binary symbol of the instance, in the ordered vocabulary. -/
abbrev aeSym₂ (r : L.Relations 2) : (aeOrd L).Relations 2 := Sum.inl r


-- @@ L152-153 verbatim
/-- The relation variable of the block, at one copy. -/
abbrev bit1 : (aeLang1 L).Relations 1 := Sum.inr ⟨(), rfl⟩


-- @@ L155-156 verbatim
/-- The relation variable of the first of two copies. -/
abbrev bitA : (aeLang2 L).Relations 1 := Sum.inl (Sum.inr ⟨(), rfl⟩)


-- @@ L158-159 verbatim
/-- The relation variable of the second of two copies. -/
abbrev bitB : (aeLang2 L).Relations 1 := Sum.inr ⟨(), rfl⟩


-- @@ L161-161 verbatim
/-! ### Addresses, as assignments of the block -/


-- @@ L163-163 verbatim
section Bits


-- @@ L165-165 verbatim
variable {A : Type}


-- @@ L167-169 verbatim
/-- **The address an assignment is**: the elements its relation variable
holds of. -/
def aeBits (ρ : addrBlock.Assignment A) : A → Prop := fun x => ρ () fun _ => x


-- @@ L171-173 verbatim
/-- **The assignment an address is**, the inverse of
`DescriptiveComplexity.AddrExp.aeBits`. -/
def aeAssign (s : A → Prop) : addrBlock.Assignment A := fun _ v => s (v 0)


-- @@ L175-176 verbatim
@[simp]
theorem aeBits_aeAssign (s : A → Prop) : aeBits (aeAssign s) = s := rfl


-- @@ L178-180 verbatim
/-- A unary relation variable is read at its only argument. -/
theorem apply₁ (f : (Fin 1 → A) → Prop) (v : Fin 1 → A) : f v ↔ f fun _ => v 0 :=
  iff_of_eq (congrArg f (funext fun j => congrArg v (Subsingleton.elim j 0)))


-- @@ L182-188 verbatim
/-- **An assignment of the block is the assignment of its address**: the single
variable being unary, nothing else is stored. -/
@[simp]
theorem aeAssign_aeBits (ρ : addrBlock.Assignment A) : aeAssign (aeBits ρ) = ρ := by
  funext i v
  match i with
  | () => exact propext (apply₁ (ρ ()) v).symm


-- @@ L190-192 verbatim
/-- Two assignments of the block holding the same address are equal. -/
theorem aeAssign_injective : Function.Injective (aeBits (A := A)) := fun ρ σ h => by
  rw [← aeAssign_aeBits ρ, ← aeAssign_aeBits σ, h]


-- @@ L194-194 verbatim
end Bits


-- @@ L196-196 verbatim
/-! ### The base's own relations, read semantically -/


-- @@ L198-198 verbatim
section Semantic


-- @@ L200-200 verbatim
variable {A : Type} [L.Structure A]


-- @@ L202-203 verbatim
/-- A unary relation of the base, at an element. -/
def aeRel₁ (r : L.Relations 1) (x : A) : Prop := RelMap r ![x]


-- @@ L205-206 verbatim
/-- A binary relation of the base, at two elements. -/
def aeRel₂ (r : L.Relations 2) (x y : A) : Prop := RelMap r ![x, y]


-- @@ L208-208 verbatim
end Semantic


-- @@ L210-210 verbatim
/-! ### The guards of the base vocabulary -/


-- @@ L212-212 verbatim
section Guards


-- @@ L214-214 verbatim
variable {γ : Type}


-- @@ L216-218 verbatim
/-- A unary mark of the instance. -/
noncomputable def markG (r : L.Relations 1) (x : γ) : (aeOrd L).Formula γ :=
  Relations.formula₁ (aeSym₁ r) (Term.var x)


-- @@ L220-222 verbatim
/-- A binary attribute of the instance. -/
noncomputable def attrG (r : L.Relations 2) (x y : γ) : (aeOrd L).Formula γ :=
  Relations.formula₂ (aeSym₂ r) (Term.var x) (Term.var y)


-- @@ L224-225 verbatim
/-- `x` and `y` are the same element. -/
noncomputable def eqG (x y : γ) : (aeOrd L).Formula γ := Term.equal (Term.var x) (Term.var y)


-- @@ L227-229 verbatim
/-- `x` is strictly below `y` in the order the instance carries. -/
noncomputable def ltG (leSym : L.Relations 2) (x y : γ) : (aeOrd L).Formula γ :=
  attrG leSym x y ⊓ ∼(attrG leSym y x)


-- @@ L231-231 verbatim
variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}


-- @@ L233-237 verbatim
@[simp]
theorem realize_markG (r : L.Relations 1) (x : γ) :
    (markG r x).Realize v ↔ RelMap r ![v x] := by
  rw [markG, Formula.realize_rel₁, relMap_sumInl]
  simp only [Term.realize_var]


-- @@ L239-243 verbatim
@[simp]
theorem realize_attrG (r : L.Relations 2) (x y : γ) :
    (attrG r x y).Realize v ↔ RelMap r ![v x, v y] := by
  rw [attrG, Formula.realize_rel₂, relMap_sumInl]
  simp only [Term.realize_var]


-- @@ L245-247 verbatim
@[simp]
theorem realize_eqG (x y : γ) : (eqG (L := L) x y).Realize v ↔ v x = v y := by
  rw [eqG, Formula.realize_equal, Term.realize_var, Term.realize_var]


-- @@ L249-253 verbatim
@[simp]
theorem realize_ltG (leSym : L.Relations 2) (x y : γ) :
    (ltG leSym x y).Realize v ↔ (aeRel₂ leSym (v x) (v y) ∧ ¬aeRel₂ leSym (v y) (v x)) := by
  rw [ltG, Formula.realize_inf, Formula.realize_not]
  exact and_congr (realize_attrG leSym x y) (not_congr (realize_attrG leSym y x))


-- @@ L255-255 verbatim
end Guards


-- @@ L257-257 verbatim
/-! ### The atoms of the block, and the lifts -/


-- @@ L259-259 verbatim
section Atoms


-- @@ L261-261 verbatim
variable {γ : Type}


-- @@ L263-264 verbatim
/-- The address of the single copy holds `x`. -/
noncomputable def bit1F (x : γ) : (aeLang1 L).Formula γ := Relations.formula₁ bit1 (Term.var x)


-- @@ L266-267 verbatim
/-- The address of the first of two copies holds `x`. -/
noncomputable def bitAF (x : γ) : (aeLang2 L).Formula γ := Relations.formula₁ bitA (Term.var x)


-- @@ L269-270 verbatim
/-- The address of the second of two copies holds `x`. -/
noncomputable def bitBF (x : γ) : (aeLang2 L).Formula γ := Relations.formula₁ bitB (Term.var x)


-- @@ L272-273 verbatim
/-- A base guard, read at one copy of the block. -/
noncomputable def lift1 (φ : (aeOrd L).Formula γ) : (aeLang1 L).Formula γ := LHom.sumInl.onFormula φ


-- @@ L275-277 verbatim
/-- A base guard, read at two copies of the block. -/
noncomputable def lift2 (φ : (aeOrd L).Formula γ) : (aeLang2 L).Formula γ :=
  LHom.sumInl.onFormula (LHom.sumInl.onFormula φ)


-- @@ L279-279 verbatim
variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}


-- @@ L281-287 verbatim
@[simp]
theorem realize_bit1F (ρ : addrBlock.Assignment A) (x : γ) :
    (@Formula.Realize (aeLang1 L) A (addrBlock.structure₁ (L := aeOrd L) ρ) _ (bit1F x) v ↔
      aeBits ρ (v x)) := by
  let := addrBlock.structure₁ (L := aeOrd L) ρ
  rw [bit1F, Formula.realize_rel₁]
  exact apply₁ _ _


-- @@ L289-295 verbatim
@[simp]
theorem realize_bitAF (ρ σ : addrBlock.Assignment A) (x : γ) :
    (@Formula.Realize (aeLang2 L) A (addrBlock.structure₂ (L := aeOrd L) ρ σ) _ (bitAF x) v ↔
      aeBits ρ (v x)) := by
  let := addrBlock.structure₂ (L := aeOrd L) ρ σ
  rw [bitAF, Formula.realize_rel₁]
  exact apply₁ _ _


-- @@ L297-303 verbatim
@[simp]
theorem realize_bitBF (ρ σ : addrBlock.Assignment A) (x : γ) :
    (@Formula.Realize (aeLang2 L) A (addrBlock.structure₂ (L := aeOrd L) ρ σ) _ (bitBF x) v ↔
      aeBits σ (v x)) := by
  let := addrBlock.structure₂ (L := aeOrd L) ρ σ
  rw [bitBF, Formula.realize_rel₁]
  exact apply₁ _ _


-- @@ L305-311 verbatim
@[simp]
theorem realize_lift1 (ρ : addrBlock.Assignment A) (φ : (aeOrd L).Formula γ) :
    (@Formula.Realize (aeLang1 L) A (addrBlock.structure₁ (L := aeOrd L) ρ) _ (lift1 φ) v ↔
      φ.Realize v) := by
  let := addrBlock.structure ρ
  rw [lift1]
  exact LHom.realize_onFormula _ φ


-- @@ L313-322 verbatim
@[simp]
theorem realize_lift2 (ρ σ : addrBlock.Assignment A) (φ : (aeOrd L).Formula γ) :
    (@Formula.Realize (aeLang2 L) A (addrBlock.structure₂ (L := aeOrd L) ρ σ) _ (lift2 φ) v ↔
      φ.Realize v) := by
  let := addrBlock.structure ρ
  let := addrBlock.structure σ
  let := addrBlock.structure₁ (L := aeOrd L) ρ
  rw [lift2]
  exact (LHom.realize_onFormula _ (LHom.sumInl.onFormula φ)).trans
    (LHom.realize_onFormula _ φ)


-- @@ L324-324 verbatim
end Atoms


-- @@ L326-328 verbatim
/-! ### The five sentences

Everything an expansion of `FirstOrder.L` has to say, once each. -/


-- @@ L330-333 verbatim
/-- **A mark of the control**: the point is the element `x`, and `x` carries the
mark `r`. -/
noncomputable def markS (r : L.Relations 1) : (aeLang1 L).Sentence :=
  Formula.iExs (Fin 1) (bit1F (Sum.inr 0) ⊓ lift1 (markG r (Sum.inr 0)))


-- @@ L335-339 verbatim
/-- **A binary attribute of the control**: the two points are the elements `x`
and `y`, and `r` holds of them. -/
noncomputable def binS (r : L.Relations 2) : (aeLang2 L).Sentence :=
  Formula.iExs (Fin 2) (bitAF (Sum.inr 0) ⊓
    (bitBF (Sum.inr 1) ⊓ lift2 (attrG r (Sum.inr 0) (Sum.inr 1))))


-- @@ L341-346 verbatim
/-- **The domain sentence of the control tag**: the address is a singleton, so
the point is an element of the instance. -/
noncomputable def singleS : (aeLang1 L).Sentence :=
  Formula.iExs (Fin 1) (bit1F (Sum.inr 0)) ⊓
    Formula.iAlls (Fin 2) ((bit1F (Sum.inr 0) ⊓ bit1F (Sum.inr 1)) ⟹
      lift1 (eqG (Sum.inr 0) (Sum.inr 1)))


-- @@ L348-356 verbatim
/-- **The order on addresses**: the two addresses agree, or, at some element the
first is out of and the second in, they agree at every strictly smaller
element. -/
noncomputable def addrLeS (leSym : L.Relations 2) : (aeLang2 L).Sentence :=
  Formula.iAlls (Fin 1) (bitAF (Sum.inr 0) ⇔ bitBF (Sum.inr 0)) ⊔
    Formula.iExs (Fin 1)
      (Formula.iAlls (Fin 1) (lift2 (ltG leSym (Sum.inr 0) (Sum.inl (Sum.inr 0))) ⟹
          (bitAF (Sum.inr 0) ⇔ bitBF (Sum.inr 0))) ⊓
        (∼(bitAF (Sum.inr 0)) ⊓ bitBF (Sum.inr 0)))


-- @@ L358-364 verbatim
/-- **The initial tape**: the first address is the initial segment cut by some
element `x`, the second point is a symbol `y`, and `y` is the input at `x`. -/
noncomputable def inpS (leSym inpSym : L.Relations 2) : (aeLang2 L).Sentence :=
  Formula.iExs (Fin 2)
    (Formula.iAlls (Fin 1)
        (bitAF (Sum.inr 0) ⇔ lift2 (attrG leSym (Sum.inr 0) (Sum.inl (Sum.inr 0)))) ⊓
      (bitBF (Sum.inr 1) ⊓ lift2 (attrG inpSym (Sum.inr 0) (Sum.inr 1))))


-- @@ L366-371 verbatim
/-- **The address lies inside a marked part of the instance**: every element it
holds carries the mark. This is what makes a *sub*-power-set the universe a
problem's grid is indexed by, when the expansion's own universe has to be bigger
than the instance to hold the problem's other objects. -/
noncomputable def subsetS (r : L.Relations 1) : (aeLang1 L).Sentence :=
  Formula.iAlls (Fin 1) (bit1F (Sum.inr 0) ⟹ lift1 (markG r (Sum.inr 0)))


-- @@ L373-376 verbatim
/-- **An element the file has a register for**, as a guard: it carries the
relation the file is described by. -/
noncomputable def hasRelG {γ : Type} (r : L.Relations 2) (x : γ) : (aeOrd L).Formula γ :=
  Formula.iExs (Fin 1) (attrG r (Sum.inl x) (Sum.inr 0))


-- @@ L378-387 verbatim
/-- **A relation read at the cells of a file**: the first address is the segment
some element `x` cuts among the elements carrying `inpSym`, the second point is
a `y`, and `inpSym` holds of `x` and `y`. This is `AddrExp.inpS` with the ruler
of all the segments replaced by the file. -/
noncomputable def regS (leSym inpSym : L.Relations 2) : (aeLang2 L).Sentence :=
  Formula.iExs (Fin 2)
    (Formula.iAlls (Fin 1)
        (bitAF (Sum.inr 0) ⇔ lift2 (attrG leSym (Sum.inr 0) (Sum.inl (Sum.inr 0)) ⊓
          hasRelG inpSym (Sum.inr 0))) ⊓
      (bitBF (Sum.inr 1) ⊓ lift2 (attrG inpSym (Sum.inr 0) (Sum.inr 1))))


-- @@ L389-389 verbatim
/-! ### What the five sentences say -/


-- @@ L391-391 verbatim
section Realize


-- @@ L393-393 verbatim
variable {A : Type} [L.Structure A] [LinearOrder A]


-- @@ L395-396 verbatim
/-- An address is a singleton: it holds something, and at most one thing. -/
def WMSingle (s : A → Prop) : Prop := (∃ x, s x) ∧ ∀ x y, s x → s y → x = y


-- @@ L398-402 verbatim
omit [L.Structure A] [LinearOrder A] in
/-- A singleton address is the address of an element. -/
theorem exists_eq_of_wmSingle {s : A → Prop} (h : WMSingle s) : ∃ x, ∀ y, s y ↔ y = x := by
  obtain ⟨⟨x, hx⟩, huniq⟩ := h
  exact ⟨x, fun y => ⟨fun hy => huniq y x hy hx, fun hy => hy ▸ hx⟩⟩


-- @@ L404-407 verbatim
omit [L.Structure A] [LinearOrder A] in
/-- The address of an element is a singleton. -/
theorem wmSingle_eq (x : A) : WMSingle (fun y => y = x) :=
  ⟨⟨x, rfl⟩, fun _ _ h1 h2 => h1.trans h2.symm⟩


-- @@ L409-413 verbatim
/-- The trivially true sentence, at one copy of the block. -/
theorem realize_topS (ρ : addrBlock.Assignment A) :
    @Sentence.Realize (aeLang1 L) A (addrBlock.structure₁ (L := aeOrd L) ρ) ⊤ := by
  let := addrBlock.structure₁ (L := aeOrd L) ρ
  exact Formula.realize_top.mpr trivial


-- @@ L415-419 verbatim
/-- The trivially false sentence, at one copy of the block. -/
theorem not_realize_botS (ρ : addrBlock.Assignment A) :
    ¬@Sentence.Realize (aeLang1 L) A (addrBlock.structure₁ (L := aeOrd L) ρ) ⊥ := by
  let := addrBlock.structure₁ (L := aeOrd L) ρ
  exact fun h => Formula.realize_bot.mp h


-- @@ L421-425 verbatim
/-- The trivially true sentence, at two copies of the block. -/
theorem realize_topS₂ (ρ σ : addrBlock.Assignment A) :
    @Sentence.Realize (aeLang2 L) A (addrBlock.structure₂ (L := aeOrd L) ρ σ) ⊤ := by
  let := addrBlock.structure₂ (L := aeOrd L) ρ σ
  exact Formula.realize_top.mpr trivial


-- @@ L427-431 verbatim
/-- The trivially false sentence, at two copies of the block. -/
theorem not_realize_botS₂ (ρ σ : addrBlock.Assignment A) :
    ¬@Sentence.Realize (aeLang2 L) A (addrBlock.structure₂ (L := aeOrd L) ρ σ) ⊥ := by
  let := addrBlock.structure₂ (L := aeOrd L) ρ σ
  exact fun h => Formula.realize_bot.mp h


-- @@ L433-440 verbatim
theorem realize_markS (r : L.Relations 1) (ρ : addrBlock.Assignment A) :
    (@Sentence.Realize (aeLang1 L) A (addrBlock.structure₁ (L := aeOrd L) ρ) (markS r) ↔
      ∃ x, aeBits ρ x ∧ RelMap r ![x]) := by
  let := addrBlock.structure₁ (L := aeOrd L) ρ
  rw [markS, Sentence.Realize]
  simp only [Formula.realize_iExs, Formula.realize_inf, realize_bit1F, realize_lift1,
    realize_markG, Sum.elim_inr]
  exact ⟨fun ⟨w, hw⟩ => ⟨w 0, hw⟩, fun ⟨x, hx⟩ => ⟨fun _ => x, hx⟩⟩


-- @@ L442-450 verbatim
theorem realize_binS (r : L.Relations 2) (ρ σ : addrBlock.Assignment A) :
    (@Sentence.Realize (aeLang2 L) A (addrBlock.structure₂ (L := aeOrd L) ρ σ) (binS r) ↔
      ∃ x y, aeBits ρ x ∧ aeBits σ y ∧ RelMap r ![x, y]) := by
  let := addrBlock.structure₂ (L := aeOrd L) ρ σ
  rw [binS, Sentence.Realize]
  simp only [Formula.realize_iExs, Formula.realize_inf, realize_bitAF, realize_bitBF,
    realize_lift2, realize_attrG, Sum.elim_inr]
  exact ⟨fun ⟨w, h1, h2, h3⟩ => ⟨w 0, w 1, h1, h2, h3⟩,
    fun ⟨x, y, h1, h2, h3⟩ => ⟨![x, y], h1, h2, h3⟩⟩


-- @@ L452-460 verbatim
theorem realize_singleS (ρ : addrBlock.Assignment A) :
    (@Sentence.Realize (aeLang1 L) A (addrBlock.structure₁ (L := aeOrd L) ρ) singleS ↔
      WMSingle (aeBits ρ)) := by
  let := addrBlock.structure₁ (L := aeOrd L) ρ
  rw [singleS, WMSingle, Sentence.Realize]
  simp only [Formula.realize_inf, Formula.realize_iExs, Formula.realize_iAlls,
    Formula.realize_imp, realize_bit1F, realize_lift1, realize_eqG, Sum.elim_inr]
  exact and_congr ⟨fun ⟨w, hw⟩ => ⟨w 0, hw⟩, fun ⟨x, hx⟩ => ⟨fun _ => x, hx⟩⟩
    ⟨fun h x y h1 h2 => h ![x, y] ⟨h1, h2⟩, fun h w hw => h (w 0) (w 1) hw.1 hw.2⟩


-- @@ L462-473 verbatim
theorem realize_addrLeS (leSym : L.Relations 2) (ρ σ : addrBlock.Assignment A) :
    (@Sentence.Realize (aeLang2 L) A (addrBlock.structure₂ (L := aeOrd L) ρ σ)
        (addrLeS leSym) ↔
      WMSetLe (aeRel₂ leSym) (aeBits ρ) (aeBits σ)) := by
  let := addrBlock.structure₂ (L := aeOrd L) ρ σ
  rw [addrLeS, WMSetLe, Sentence.Realize]
  simp only [Formula.realize_sup, Formula.realize_iAlls, Formula.realize_iExs,
    Formula.realize_inf, Formula.realize_imp, Formula.realize_iff, Formula.realize_not,
    realize_bitAF, realize_bitBF, realize_lift2, realize_ltG, Sum.elim_inl, Sum.elim_inr]
  refine or_congr ⟨fun h x => h fun _ => x, fun h w => h (w 0)⟩ ?_
  exact ⟨fun ⟨w, hb, hs, ht⟩ => ⟨w 0, fun y hy => hb (fun _ => y) hy, hs, ht⟩,
    fun ⟨x, hb, hs, ht⟩ => ⟨fun _ => x, fun w hw => hb (w 0) hw, hs, ht⟩⟩


-- @@ L475-486 verbatim
theorem realize_inpS (leSym inpSym : L.Relations 2) (ρ σ : addrBlock.Assignment A) :
    (@Sentence.Realize (aeLang2 L) A (addrBlock.structure₂ (L := aeOrd L) ρ σ)
        (inpS leSym inpSym) ↔
      ∃ x y, WMDown (aeRel₂ leSym) (aeBits ρ) x ∧ aeBits σ y ∧
        aeRel₂ inpSym x y) := by
  let := addrBlock.structure₂ (L := aeOrd L) ρ σ
  rw [inpS, Sentence.Realize]
  simp only [Formula.realize_iExs, Formula.realize_iAlls, Formula.realize_inf,
    Formula.realize_iff, realize_bitAF, realize_bitBF, realize_lift2, realize_attrG,
    Sum.elim_inl, Sum.elim_inr]
  refine ⟨fun ⟨w, hd, hb, hi⟩ => ⟨w 0, w 1, fun y => hd fun _ => y, hb, hi⟩,
    fun ⟨x, y, hd, hb, hi⟩ => ⟨![x, y], fun w => hd (w 0), hb, hi⟩⟩


-- @@ L488-493 verbatim
@[simp]
theorem realize_hasRelG {γ : Type} {v : γ → A} (r : L.Relations 2) (x : γ) :
    (hasRelG r x).Realize v ↔ ∃ z, aeRel₂ r (v x) z := by
  rw [hasRelG]
  simp only [Formula.realize_iExs, realize_attrG, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun ⟨w, hw⟩ => ⟨w 0, hw⟩, fun ⟨a, ha⟩ => ⟨fun _ => a, ha⟩⟩


-- @@ L495-503 verbatim
theorem realize_subsetS (r : L.Relations 1) (ρ : addrBlock.Assignment A) :
    (@Sentence.Realize (aeLang1 L) A (addrBlock.structure₁ (L := aeOrd L) ρ)
        (subsetS r) ↔
      ∀ x, aeBits ρ x → aeRel₁ r x) := by
  let := addrBlock.structure₁ (L := aeOrd L) ρ
  rw [subsetS, Sentence.Realize]
  simp only [Formula.realize_iAlls, Formula.realize_imp, realize_bit1F, realize_lift1,
    realize_markG, Sum.elim_inr]
  exact ⟨fun h x hx => h (fun _ => x) hx, fun h w hw => h (w 0) hw⟩


-- @@ L505-516 verbatim
theorem realize_regS (leSym inpSym : L.Relations 2) (ρ σ : addrBlock.Assignment A) :
    (@Sentence.Realize (aeLang2 L) A (addrBlock.structure₂ (L := aeOrd L) ρ σ)
        (regS leSym inpSym) ↔
      ∃ x y, WMFileSeg (aeRel₂ leSym) (fun z => ∃ w, aeRel₂ inpSym z w) (aeBits ρ) x ∧
        aeBits σ y ∧ aeRel₂ inpSym x y) := by
  let := addrBlock.structure₂ (L := aeOrd L) ρ σ
  rw [regS, Sentence.Realize]
  simp only [Formula.realize_iExs, Formula.realize_iAlls, Formula.realize_inf,
    Formula.realize_iff, realize_bitAF, realize_bitBF, realize_lift2, realize_attrG,
    realize_hasRelG, Sum.elim_inl, Sum.elim_inr]
  refine ⟨fun ⟨w, hd, hb, hi⟩ => ⟨w 0, w 1, fun y => hd fun _ => y, hb, hi⟩,
    fun ⟨x, y, hd, hb, hi⟩ => ⟨![x, y], fun w => hd (w 0), hb, hi⟩⟩


-- @@ L518-518 verbatim
end Realize


-- @@ L520-520 verbatim
/-! ### The universe, the tags and the expansion skeleton -/


-- @@ L522-522 verbatim
section Skeleton


-- @@ L524-524 verbatim
variable (A : Type)


-- @@ L526-530 verbatim
/-- **The universe a problem at this expansion runs over**: the addresses – the
subsets of the instance – together with the elements of the instance. An
`abbrev`, so that the sum structure stays visible to `rw` and to the
elaborator. -/
abbrev WPoint : Type := (A → Prop) ⊕ A


-- @@ L532-539 verbatim
/-- The two tags of the expansion: the addresses, and the elements of the
instance. -/
inductive WTag where
  /-- An address: any assignment of the block. -/
  | addr
  /-- A control element: a singleton assignment of the block. -/
  | ctrl
  deriving DecidableEq


-- @@ L541-541 verbatim
instance : Fintype WTag := ⟨{WTag.addr, WTag.ctrl}, by intro x; cases x <;> simp⟩


-- @@ L543-543 verbatim
variable {A}


-- @@ L545-549 verbatim
/-- The domain sentence of each tag: an address is unrestricted, a control
element is a singleton. -/
noncomputable def domT : WTag → (aeLang1 L).Sentence
  | .addr => ⊤
  | .ctrl => singleS


-- @@ L551-554 verbatim
/-- Reading a one-copy sentence inside the block replicated once. -/
noncomputable def onS1 (φ : (aeLang1 L).Sentence) :
    ((aeOrd L).sum (addrBlock.replicate 1).lang).Sentence :=
  (addrBlock.oneLHom (aeOrd L)).onSentence φ


-- @@ L556-559 verbatim
/-- Reading a two-copy sentence inside the block replicated twice. -/
noncomputable def onS2 (φ : (aeLang2 L).Sentence) :
    ((aeOrd L).sum (addrBlock.replicate 2).lang).Sentence :=
  (addrBlock.twoLHom (aeOrd L)).onSentence φ


-- @@ L561-579 verbatim
variable (L) in
/-- **The expansion whose points are the subsets of the instance**: two tags,
the one-variable block, and whatever defining sentences the problem supplies.
Everything below is proved of *this* expansion, so a problem drawn on it has
only to say what each of its symbols means. -/
noncomputable def addrExp (E : Language.{0, 0}) [E.IsRelational]
    (relS : ∀ {n : ℕ}, E.Relations n → (Fin n → WTag) →
      ((aeOrd L).sum (addrBlock.replicate n).lang).Sentence) :
    ExpExpansion L where
  Tag := WTag
  B := addrBlock
  E := E
  dom := domT
  relSentence := relS
  dom_nonempty := by
    intro A _ _ _ _
    refine ⟨.addr, addrBlock.botAssign A, ?_⟩
    let := addrBlock.structure₁ (L := aeOrd L) (addrBlock.botAssign A)
    exact Formula.realize_top.mpr trivial


-- @@ L581-581 verbatim
end Skeleton


-- @@ L583-583 verbatim
/-! ### The universe of the problem is the universe of the expansion -/


-- @@ L585-585 verbatim
section Embed


-- @@ L587-587 verbatim
variable {E : Language.{0, 0}} [E.IsRelational]

-- @@ L588-589 verbatim
variable {relS : ∀ {n : ℕ}, E.Relations n → (Fin n → WTag) →
  ((aeOrd L).sum (addrBlock.replicate n).lang).Sentence}

-- @@ L590-590 verbatim
variable {A : Type} [L.Structure A] [LinearOrder A]


-- @@ L592-596 verbatim
/-- An address satisfies the domain sentence of its tag, which is `⊤`. -/
theorem domHolds_addr (s : A → Prop) :
    ExpExpansion.DomHolds (X := addrExp L E relS) (WTag.addr, aeAssign s) := by
  let := (addrExp L E relS).B.structure₁ (L := aeOrd L) (aeAssign s)
  exact Formula.realize_top.mpr trivial


-- @@ L598-602 verbatim
/-- The singleton address of an element satisfies the domain sentence of the
control tag. -/
theorem domHolds_ctrl (x : A) :
    ExpExpansion.DomHolds (X := addrExp L E relS) (WTag.ctrl, aeAssign fun y => y = x) :=
  (realize_singleS _).mpr (wmSingle_eq x)


-- @@ L604-609 verbatim
/-- **The universe of the problem sits inside the expansion**: an address
becomes the point tagged `addr` carrying it, a control element the point tagged
`ctrl` carrying its singleton. -/
noncomputable def addrEmbed : WPoint A → (addrExp L E relS).Map A
  | Sum.inl s => ⟨(WTag.addr, aeAssign s), domHolds_addr s⟩
  | Sum.inr x => ⟨(WTag.ctrl, aeAssign fun y => y = x), domHolds_ctrl x⟩


-- @@ L611-613 verbatim
@[simp]
theorem addrEmbed_addr_tag (s : A → Prop) :
    (addrEmbed (L := L) (relS := relS) (Sum.inl s)).1.1 = WTag.addr := rfl


-- @@ L615-617 verbatim
@[simp]
theorem addrEmbed_ctrl_tag (x : A) :
    (addrEmbed (L := L) (relS := relS) (Sum.inr x)).1.1 = WTag.ctrl := rfl


-- @@ L619-642 verbatim
/-- **The embedding is onto the whole expanded universe**: every point tagged
`addr` is an address, and every point tagged `ctrl` is a control element,
because its domain sentence made its assignment a singleton. -/
theorem addrEmbed_bijective :
    Function.Bijective (addrEmbed (L := L) (E := E) (relS := relS) (A := A)) := by
  constructor
  · rintro (s | x) (t | y) h
    · have h1 : aeAssign s = aeAssign t := congrArg (fun p => p.1.2) h
      exact congrArg Sum.inl (by rw [← aeBits_aeAssign s, ← aeBits_aeAssign t, h1])
    · exact absurd (congrArg (fun p => p.1.1) h) (by simp)
    · exact absurd (congrArg (fun p => p.1.1) h) (by simp)
    · have h1 : (fun z => z = x) = fun z => z = y := by
        rw [← aeBits_aeAssign fun z => z = x, ← aeBits_aeAssign fun z => z = y]
        exact congrArg aeBits (congrArg (fun p => p.1.2) h)
      exact congrArg Sum.inr (by simpa using congrFun h1 x)
  · rintro ⟨⟨t, ρ⟩, hdom⟩
    match t with
    | WTag.addr => exact ⟨Sum.inl (aeBits ρ), ExpExpansion.map_ext rfl (aeAssign_aeBits ρ)⟩
    | WTag.ctrl =>
      obtain ⟨x, hx⟩ := exists_eq_of_wmSingle ((realize_singleS ρ).mp hdom)
      have h1 : (aeAssign fun z => z = x) = ρ := by
        rw [show (fun z => z = x) = aeBits ρ from (funext fun z => propext (hx z)).symm]
        exact aeAssign_aeBits ρ
      exact ⟨Sum.inr x, ExpExpansion.map_ext rfl h1⟩


-- @@ L644-646 verbatim
/-- **The points of the expansion are the universe of the problem.** -/
noncomputable def addrEquiv : WPoint A ≃ (addrExp L E relS).Map A :=
  Equiv.ofBijective _ addrEmbed_bijective


-- @@ L648-650 verbatim
@[simp]
theorem addrEquiv_apply (p : WPoint A) :
    addrEquiv (L := L) (relS := relS) p = addrEmbed p := rfl


-- @@ L652-652 verbatim
end Embed


-- @@ L654-654 verbatim
/-! ### Reading a defining sentence at the points -/


-- @@ L656-656 verbatim
section Reading


-- @@ L658-658 verbatim
variable {E : Language.{0, 0}} [E.IsRelational]

-- @@ L659-660 verbatim
variable {relS : ∀ {n : ℕ}, E.Relations n → (Fin n → WTag) →
  ((aeOrd L).sum (addrBlock.replicate n).lang).Sentence}

-- @@ L661-661 verbatim
variable {A : Type} [L.Structure A] [LinearOrder A]


-- @@ L663-671 verbatim
/-- **Reading a one-copy sentence at a point**: the replicated assignment holds
the point's address in its single copy. -/
theorem realize_onS1 (φ : (aeLang1 L).Sentence) (x : (addrExp L E relS).Map A) :
    (@Sentence.Realize _ A ((addrBlock.replicate 1).structure₁ (L := aeOrd L)
        (addrBlock.replicateAssign fun i =>
          ((![x] : Fin 1 → (addrExp L E relS).Map A) i).1.2))
      (onS1 φ) ↔
      @Sentence.Realize (aeLang1 L) A (addrBlock.structure₁ (L := aeOrd L) x.1.2) φ) :=
  addrBlock.realize_oneLHom (L := aeOrd L) _ φ


-- @@ L673-682 verbatim
/-- **Reading a two-copy sentence at two points**: the replicated assignment
holds the first point's address in copy `0` and the second's in copy `1`. -/
theorem realize_onS2 (φ : (aeLang2 L).Sentence) (x y : (addrExp L E relS).Map A) :
    (@Sentence.Realize _ A ((addrBlock.replicate 2).structure₁ (L := aeOrd L)
        (addrBlock.replicateAssign fun i =>
          ((![x, y] : Fin 2 → (addrExp L E relS).Map A) i).1.2))
      (onS2 φ) ↔
      @Sentence.Realize (aeLang2 L) A
        (addrBlock.structure₂ (L := aeOrd L) x.1.2 y.1.2) φ) :=
  addrBlock.realize_twoLHom (L := aeOrd L) _ φ


-- @@ L684-690 verbatim
variable (A) in
/-- The expanded structure, at the vocabulary the problem is written in – equal
to the expansion's own by definition, but not syntactically, so instance search
has to be handed it. -/
@[instance_reducible]
noncomputable def addrStructure : E.Structure ((addrExp L E relS).Map A) :=
  (addrExp L E relS).mapStructure A


-- @@ L692-704 verbatim
/-- Reading a unary symbol of the expanded vocabulary at one point. -/
theorem realize_one (rt : E.Relations 1) (φ : WTag → (aeLang1 L).Sentence)
    (h : ∀ τ : Fin 1 → WTag, relS rt τ = onS1 (φ (τ 0)))
    (x : (addrExp L E relS).Map A) :
    letI := addrStructure (L := L) (relS := relS) A
    (RelMap rt ![x] ↔
      @Sentence.Realize (aeLang1 L) A (addrBlock.structure₁ (L := aeOrd L) x.1.2)
        (φ x.1.1)) := by
  let := addrStructure (L := L) (relS := relS) A
  have h1 := (addrExp L E relS).relMap_map rt ![x]
  rw [show (addrExp L E relS).relSentence rt (fun i => (![x] i).1.1) =
    onS1 (φ ((![x] : Fin 1 → (addrExp L E relS).Map A) 0).1.1) from h _] at h1
  exact h1.trans (realize_onS1 _ x)


-- @@ L706-719 verbatim
/-- Reading a binary symbol of the expanded vocabulary at two points. -/
theorem realize_two (rt : E.Relations 2) (φ : WTag → WTag → (aeLang2 L).Sentence)
    (h : ∀ τ : Fin 2 → WTag, relS rt τ = onS2 (φ (τ 0) (τ 1)))
    (x y : (addrExp L E relS).Map A) :
    letI := addrStructure (L := L) (relS := relS) A
    (RelMap rt ![x, y] ↔
      @Sentence.Realize (aeLang2 L) A
        (addrBlock.structure₂ (L := aeOrd L) x.1.2 y.1.2) (φ x.1.1 y.1.1)) := by
  let := addrStructure (L := L) (relS := relS) A
  have h1 := (addrExp L E relS).relMap_map rt ![x, y]
  rw [show (addrExp L E relS).relSentence rt (fun i => (![x, y] i).1.1) =
    onS2 (φ ((![x, y] : Fin 2 → (addrExp L E relS).Map A) 0).1.1
      ((![x, y] : Fin 2 → (addrExp L E relS).Map A) 1).1.1) from h _] at h1
  exact h1.trans (realize_onS2 _ x y)


-- @@ L721-721 verbatim
end Reading


-- @@ L723-723 verbatim
end AddrExp


-- @@ L725-725 verbatim
end DescriptiveComplexity
