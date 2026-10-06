/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Problems.ThreeColorability
import DescriptiveComplexity.Problems.CliqueFamily.Defs


-- @@ L9-50 verbatim
/-!
# The coloring family: definitions

Three problems built on one generic property, `DescriptiveComplexity.ColorableOn`: a
map into `Fin k` separating the pairs related by a *conflict* relation.

* `DescriptiveComplexity.KCol k`, on `FirstOrder.Language.graph`-structures: is the
  graph `k`-colorable, for a `k` fixed once and for all? The conflict relation
  is adjacency, so a self-loop makes the instance a no-instance, and
  `DescriptiveComplexity.kCol_three` identifies `KCol 3` with
  `DescriptiveComplexity.ThreeCol`.
* `DescriptiveComplexity.ChromaticNumber`, on `FirstOrder.Language.markedGraph`-structures:
  is the chromatic number at most `k`, where `k` is the cardinality of the
  marked set (`DescriptiveComplexity.Numbers.Unary`)? This is Karp's CHROMATIC
  NUMBER, with `k` part of the instance rather than of the problem.
* `DescriptiveComplexity.CliqueCover`, on the same vocabulary: can the vertices be
  covered by at most `k` cliques? A clique cover is a proper coloring of the
  complement graph, so this is the same generic property with the conflict
  relation complemented – which is why one interpretation reduces each of the
  two threshold problems to the other, exactly as in
  `DescriptiveComplexity.Problems.CliqueFamily`.

## Loops, and why the two threshold problems ignore them

The two marked-graph problems take their conflict relation *off the diagonal*
(`x ≠ y ∧ …`), i.e., they are about the underlying loopless graph, which is the
convention of the clique family on this vocabulary. It is also what makes them
interreducible by edge complementation: complementing off the diagonal is an
involution on loopless graphs, but forgets loops. The price is paid once, in
the reduction from 3-colorability
(`DescriptiveComplexity.Problems.Coloring.Reductions`), whose input *is* loop-sensitive:
a self-looped vertex is turned into a `K₄`, which no 3-coloring survives.

## The palette form of a threshold

A `k`-coloring with `k` the cardinality of the marked set can equivalently be
given as a map into the marked set itself
(`DescriptiveComplexity.paletteColorableOn_iff`): the marked elements *are* `k` colors.
This is the form the second-order definitions guess, since it needs only a
binary relation variable, where the number `k` is not available to the
formulas.
-/


-- @@ L52-52 verbatim
namespace DescriptiveComplexity


-- @@ L54-54 verbatim
open FirstOrder


-- @@ L56-56 verbatim
open Language Structure


-- @@ L58-58 verbatim
/-! ### The generic property -/


-- @@ L60-60 verbatim
section Generic


-- @@ L62-62 verbatim
variable {A : Type}


-- @@ L64-67 verbatim
/-- A `k`-coloring for the conflict relation `Cfl`: a map into `Fin k` giving
distinct values to conflicting elements. -/
def ColorableOn (Cfl : A → A → Prop) (k : ℕ) : Prop :=
  ∃ c : A → Fin k, ∀ x y, Cfl x y → c x ≠ c y


-- @@ L69-72 verbatim
/-- A coloring whose palette is the marked set itself: a map into the
`Kp`-marked elements giving distinct values to conflicting elements. -/
def PaletteColorableOn (Cfl : A → A → Prop) (Kp : A → Prop) : Prop :=
  ∃ col : A → A, (∀ x, Kp (col x)) ∧ ∀ x y, Cfl x y → col x ≠ col y


-- @@ L74-93 verbatim
/-- **Colors are the marked elements**: on a finite universe, colorability
with as many colors as the marked set is colorability *by* the marked set.
This is the bridge between the numeric reading of the threshold and its
second-order rendering, where the coloring is guessed as a binary relation
variable. -/
theorem paletteColorableOn_iff [Finite A] (Cfl : A → A → Prop) (Kp : A → Prop) :
    PaletteColorableOn Cfl Kp ↔ ColorableOn Cfl {x | Kp x}.ncard := by
  classical
  have : Fintype A := Fintype.ofFinite A
  have hcard : Fintype.card {x // Kp x} = {x | Kp x}.ncard := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_coe_set_eq]
    rfl
  let e := Fintype.equivFinOfCardEq hcard
  constructor
  · rintro ⟨col, hcol, hproper⟩
    refine ⟨fun x => e ⟨col x, hcol x⟩, fun x y hxy hc => ?_⟩
    exact hproper x y hxy (congrArg Subtype.val (e.injective hc))
  · rintro ⟨c, hproper⟩
    refine ⟨fun x => (e.symm (c x)).1, fun x => (e.symm (c x)).2, fun x y hxy hc => ?_⟩
    exact hproper x y hxy (e.symm.injective (Subtype.ext hc))


-- @@ L95-99 verbatim
/-- `ColorableOn` only depends on the extension of the conflict relation. -/
theorem colorableOn_congr {Cfl Cfl' : A → A → Prop} {k : ℕ}
    (h : ∀ x y, Cfl x y ↔ Cfl' x y) : ColorableOn Cfl k ↔ ColorableOn Cfl' k :=
  exists_congr fun _ =>
    ⟨fun hc x y hxy => hc x y ((h x y).mpr hxy), fun hc x y hxy => hc x y ((h x y).mp hxy)⟩


-- @@ L101-101 verbatim
variable {B : Type}


-- @@ L103-110 verbatim
/-- `ColorableOn` transports along an equivalence commuting with the conflict
relations. -/
theorem ColorableOn.of_equiv (u : B ≃ A) {CflB : B → B → Prop} {CflA : A → A → Prop}
    {k : ℕ} (hcfl : ∀ b b', CflB b b' ↔ CflA (u b) (u b')) (h : ColorableOn CflB k) :
    ColorableOn CflA k := by
  obtain ⟨c, hc⟩ := h
  refine ⟨fun a => c (u.symm a), fun x y hxy => ?_⟩
  exact hc (u.symm x) (u.symm y) ((hcfl (u.symm x) (u.symm y)).mpr (by simpa using hxy))


-- @@ L112-117 verbatim
/-- `ColorableOn` transports along an equivalence, iff version. -/
theorem ColorableOn.equiv_iff (u : B ≃ A) {CflB : B → B → Prop} {CflA : A → A → Prop}
    {k : ℕ} (hcfl : ∀ b b', CflB b b' ↔ CflA (u b) (u b')) :
    ColorableOn CflB k ↔ ColorableOn CflA k :=
  ⟨ColorableOn.of_equiv u hcfl,
    ColorableOn.of_equiv u.symm fun a a' => by rw [hcfl]; simp⟩


-- @@ L119-119 verbatim
end Generic


-- @@ L121-121 verbatim
/-! ### `k`-colorability, for a fixed `k` -/


-- @@ L123-123 verbatim
section Fixed


-- @@ L125-125 verbatim
variable (k : ℕ) (V : Type) [Language.graph.Structure V]


-- @@ L127-130 verbatim
/-- A `Language.graph`-structure is `k`-colorable if the vertices can be
colored with `k` colors so that adjacent vertices get distinct colors. -/
def KColorable : Prop :=
  ColorableOn (fun x y : V => RelMap adj ![x, y]) k


-- @@ L132-132 verbatim
end Fixed


-- @@ L134-137 verbatim
private theorem kColorable_of_iso {k : ℕ} {A B : Type} [Language.graph.Structure A]
    [Language.graph.Structure B] (e : A ≃[Language.graph] B) (h : KColorable k A) :
    KColorable k B :=
  ColorableOn.of_equiv e.toEquiv (fun a b => relMap_equiv₂ e adj a b) h


-- @@ L139-143 verbatim
/-- `k`-colorability is isomorphism-invariant. -/
theorem kColorable_iso {k : ℕ} {A B : Type} [Language.graph.Structure A]
    [Language.graph.Structure B] (e : A ≃[Language.graph] B) :
    KColorable k A ↔ KColorable k B :=
  ⟨kColorable_of_iso e, kColorable_of_iso e.symm⟩


-- @@ L145-148 verbatim
/-- `k`-colorability, as a problem on `Language.graph`-structures. -/
def KCol (k : ℕ) : DecisionProblem Language.graph where
  Holds := fun V inst => @KColorable k V inst
  iso_invariant := fun e => kColorable_iso e


-- @@ L150-152 verbatim
/-- At `k = 3`, `k`-colorability *is* 3-colorability. -/
theorem kCol_three : KCol 3 = ThreeCol :=
  DecisionProblem.ext fun _ _ => Iff.rfl


-- @@ L154-154 verbatim
/-! ### Chromatic number and clique cover, with the threshold in the instance -/


-- @@ L156-156 verbatim
section Conflicts


-- @@ L158-158 verbatim
variable {A : Type} [Language.markedGraph.Structure A]


-- @@ L160-162 verbatim
/-- The conflict relation of the chromatic-number problem: adjacency off the
diagonal. -/
def MGConflict (x y : A) : Prop := x ≠ y ∧ MGAdj x y


-- @@ L164-166 verbatim
/-- The conflict relation of the clique-cover problem: non-adjacency off the
diagonal – two vertices may share a clique exactly when they are adjacent. -/
def MGCoConflict (x y : A) : Prop := x ≠ y ∧ ¬MGAdj x y


-- @@ L168-168 verbatim
end Conflicts


-- @@ L170-170 verbatim
section Threshold


-- @@ L172-172 verbatim
variable (A : Type) [Language.markedGraph.Structure A]


-- @@ L174-178 verbatim
/-- A marked graph has chromatic number at most the size of its marked set.
(Finiteness of the universe is part of the property: cardinality thresholds
are only meaningful on finite structures.) -/
def HasSmallChromaticNumber : Prop :=
  Finite A ∧ ColorableOn (MGConflict (A := A)) {x : A | MGMarked x}.ncard


-- @@ L180-183 verbatim
/-- A marked graph can be covered by at most as many cliques as its marked
set has elements. -/
def HasSmallCliqueCover : Prop :=
  Finite A ∧ ColorableOn (MGCoConflict (A := A)) {x : A | MGMarked x}.ncard


-- @@ L185-185 verbatim
end Threshold


-- @@ L187-187 verbatim
section Iso


-- @@ L189-189 verbatim
variable {A B : Type} [Language.markedGraph.Structure A] [Language.markedGraph.Structure B]


-- @@ L191-194 verbatim
private theorem mgConflict_map (e : A ≃[Language.markedGraph] B) (a b : A) :
    MGConflict a b ↔ MGConflict (e a) (e b) :=
  and_congr ⟨fun h hab => h (e.injective hab), fun h hab => h (congrArg e hab)⟩
    (relMap_equiv₂ e mgAdj a b)


-- @@ L196-199 verbatim
private theorem mgCoConflict_map (e : A ≃[Language.markedGraph] B) (a b : A) :
    MGCoConflict a b ↔ MGCoConflict (e a) (e b) :=
  and_congr ⟨fun h hab => h (e.injective hab), fun h hab => h (congrArg e hab)⟩
    (not_congr (relMap_equiv₂ e mgAdj a b))


-- @@ L201-203 verbatim
private theorem ncard_marked_map (e : A ≃[Language.markedGraph] B) :
    {x : A | MGMarked x}.ncard = {x : B | MGMarked x}.ncard :=
  ncard_setOf_equiv e.toEquiv fun a => relMap_equiv₁ e mgMarked a


-- @@ L205-210 verbatim
/-- The chromatic-number property is isomorphism-invariant. -/
theorem hasSmallChromaticNumber_iso (e : A ≃[Language.markedGraph] B) :
    HasSmallChromaticNumber A ↔ HasSmallChromaticNumber B := by
  refine and_congr e.toEquiv.finite_iff ?_
  rw [ncard_marked_map e]
  exact ColorableOn.equiv_iff e.toEquiv (mgConflict_map e)


-- @@ L212-217 verbatim
/-- The clique-cover property is isomorphism-invariant. -/
theorem hasSmallCliqueCover_iso (e : A ≃[Language.markedGraph] B) :
    HasSmallCliqueCover A ↔ HasSmallCliqueCover B := by
  refine and_congr e.toEquiv.finite_iff ?_
  rw [ncard_marked_map e]
  exact ColorableOn.equiv_iff e.toEquiv (mgCoConflict_map e)


-- @@ L219-219 verbatim
end Iso


-- @@ L221-225 verbatim
/-- CHROMATIC NUMBER, as a problem on marked graphs: can the graph be properly
colored with as many colors as the marked set has elements? -/
def ChromaticNumber : DecisionProblem Language.markedGraph where
  Holds := fun A inst => @HasSmallChromaticNumber A inst
  iso_invariant := fun e => hasSmallChromaticNumber_iso e


-- @@ L227-231 verbatim
/-- CLIQUE COVER, as a problem on marked graphs: can the vertices be covered
by at most as many cliques as the marked set has elements? -/
def CliqueCover : DecisionProblem Language.markedGraph where
  Holds := fun A inst => @HasSmallCliqueCover A inst
  iso_invariant := fun e => hasSmallCliqueCover_iso e


-- @@ L233-233 verbatim
end DescriptiveComplexity
