/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Iterate
import Mathlib.Data.Fintype.Pi


-- @@ L9-49 verbatim
/-!
# The `k`-pebble refinement, over an abstract initial relation

The combinatorial core of `k`-variable equivalence `≡ᵏ`
([Abiteboul–Vianu 1991][abiteboul1991generic];
[Ebbinghaus–Flum 1995][ebbinghaus1995finite], ch. 3), with no logic in sight:
positions are `k`-tuples over a bare type `A`, an *initial relation* `E₀`
stands in for «same atomic type», and one round of the `k`-pebble game refines
a relation `E` to `DescriptiveComplexity.pebbleRefine E₀ E` – the pairs that
are in `E₀` and survive one exchange of a pebble
(`DescriptiveComplexity.PebbleBackForth`).

`DescriptiveComplexity.EquivK E₀` is the limit of the descending refinement
chain `DescriptiveComplexity.pebbleStage`, that is, the *greatest* fixed point
of the refinement:

* the chain plateaus within the number of pairs of tuples
  (`DescriptiveComplexity.exists_pebbleStage_succ_eq`, the antitone half of
  `DescriptiveComplexity.exists_succ_eq_of_antitone_subset`), so on a finite
  type the limit is a stage and is itself a fixed point
  (`DescriptiveComplexity.equivK_iff`, the interface characterization);
* any relation below `E₀` that survives its own back-and-forth condition is
  below the limit (`DescriptiveComplexity.le_equivK`, the coinduction
  principle), which is what «greatest» means and how anything is ever proved
  `≡ᵏ`-equivalent;
* the limit is an equivalence relation whenever `E₀` is
  (`DescriptiveComplexity.equivK_equivalence`);
* refining the initial relation by anything the limit already refines does not
  change the limit (`DescriptiveComplexity.equivK_inf_eq`) – read with `E₀'`
  the agreement on a `≡ᵏ`-invariant relation, this is the *expansion* lemma:
  `≡ᵏ` is unchanged when the structure is expanded by an `≡ᵏ`-invariant
  relation. It is the lemma that carries the `≡ᵏ`-invariance of fixed-point
  logics, each stage of an induction being such an expansion.

Keeping `E₀` abstract keeps the vocabulary out: the instantiation at «same
atomic type over a structure» – necessarily over the *finitely many* symbols a
definition actually mentions – is where the logic enters, and lives with the
invariance results for the fixed-point logics, not here. The same skeleton
with rounds in place of pebbles is the Ehrenfeucht–Fraïssé refinement, a
second consumer this file is stated to serve.
-/


-- @@ L51-51 verbatim
namespace DescriptiveComplexity


-- @@ L53-53 verbatim
/-! ### Relations on `k`-tuples -/


-- @@ L55-58 verbatim
/-- A relation between `k`-tuples over `A`: the positions of the `k`-pebble
game. -/
abbrev PebbleRel (A : Type) (k : ℕ) : Type :=
  (Fin k → A) → (Fin k → A) → Prop


-- @@ L60-60 verbatim
variable {A : Type} {k : ℕ}


-- @@ L62-65 verbatim
/-- Pointwise implication of relations on `k`-tuples, spelled out (the
lattice order, kept explicit per the conventions of this library). -/
def PebbleRel.Le (E E' : PebbleRel A k) : Prop :=
  ∀ a b : Fin k → A, E a b → E' a b


-- @@ L67-67 verbatim
/-! ### One round of the game -/


-- @@ L69-75 verbatim
/-- The back-and-forth condition of the `k`-pebble game relative to a
relation `E`: whichever pebble the spoiler moves, on whichever side, the
duplicator can move the same pebble on the other side and stay in `E`. -/
def PebbleBackForth (E : PebbleRel A k) : PebbleRel A k :=
  fun a b => ∀ i : Fin k,
    (∀ c : A, ∃ d : A, E (Function.update a i c) (Function.update b i d)) ∧
    (∀ d : A, ∃ c : A, E (Function.update a i c) (Function.update b i d))


-- @@ L77-80 verbatim
/-- One round of refinement: agree initially, and survive one exchange of a
pebble relative to `E`. -/
def pebbleRefine (E₀ E : PebbleRel A k) : PebbleRel A k :=
  fun a b => E₀ a b ∧ PebbleBackForth E a b


-- @@ L82-91 verbatim
/-- The back-and-forth condition is monotone in the relation it is relative
to. -/
theorem pebbleBackForth_mono {E E' : PebbleRel A k} (h : E.Le E') :
    (PebbleBackForth E).Le (PebbleBackForth E') := by
  intro a b hab i
  refine ⟨fun c => ?_, fun d => ?_⟩
  · obtain ⟨d, hd⟩ := (hab i).1 c
    exact ⟨d, h _ _ hd⟩
  · obtain ⟨c, hc⟩ := (hab i).2 d
    exact ⟨c, h _ _ hc⟩


-- @@ L93-96 verbatim
/-- One round of refinement is monotone in the refined relation. -/
theorem pebbleRefine_mono (E₀ : PebbleRel A k) {E E' : PebbleRel A k} (h : E.Le E') :
    (pebbleRefine E₀ E).Le (pebbleRefine E₀ E') :=
  fun a b hab => ⟨hab.1, pebbleBackForth_mono h a b hab.2⟩


-- @@ L98-98 verbatim
/-! ### The refinement chain and its limit -/


-- @@ L100-104 verbatim
/-- The descending refinement chain, from the all-relation: what one round
cannot yet tell apart, twice refined, thrice refined … -/
def pebbleStage (E₀ : PebbleRel A k) : ℕ → PebbleRel A k
  | 0 => fun _ _ => True
  | n + 1 => pebbleRefine E₀ (pebbleStage E₀ n)


-- @@ L106-111 verbatim
/-- **`k`-equivalence relative to an initial relation**: the limit of the
refinement chain – equivalently (`DescriptiveComplexity.equivK_iff`,
`DescriptiveComplexity.le_equivK`) the greatest fixed point of one round of
refinement. -/
def EquivK (E₀ : PebbleRel A k) : PebbleRel A k :=
  fun a b => ∀ n, pebbleStage E₀ n a b


-- @@ L113-113 verbatim
variable {E₀ : PebbleRel A k}


-- @@ L115-120 verbatim
/-- The refinement chain descends. -/
theorem pebbleStage_succ_le (E₀ : PebbleRel A k) (n : ℕ) :
    (pebbleStage E₀ (n + 1)).Le (pebbleStage E₀ n) := by
  induction n with
  | zero => exact fun a b _ => trivial
  | succ n ih => exact pebbleRefine_mono E₀ ih


-- @@ L122-130 verbatim
/-- The refinement chain descends, monotonically. -/
theorem pebbleStage_le_of_le (E₀ : PebbleRel A k) {m n : ℕ} (hmn : m ≤ n) :
    (pebbleStage E₀ n).Le (pebbleStage E₀ m) := by
  induction n with
  | zero => rw [Nat.le_zero.mp hmn]; exact fun _ _ h => h
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with hlt | heq
    · exact fun a b h => ih (Nat.lt_succ_iff.mp hlt) a b (pebbleStage_succ_le E₀ n a b h)
    · rw [heq]; exact fun _ _ h => h


-- @@ L132-135 verbatim
/-- The limit is below every stage. -/
theorem EquivK.stage {a b : Fin k → A} (h : EquivK E₀ a b) (n : ℕ) :
    pebbleStage E₀ n a b :=
  h n


-- @@ L137-139 verbatim
/-- The limit is below the initial relation. -/
theorem EquivK.initial {a b : Fin k → A} (h : EquivK E₀ a b) : E₀ a b :=
  (h 1).1


-- @@ L141-141 verbatim
/-! ### Coinduction: the limit is the greatest post-fixed point -/


-- @@ L143-151 verbatim
/-- **The coinduction principle**: a relation below its own refinement is
below the limit. This is how tuples are ever proved `≡ᵏ`-equivalent – exhibit
a back-and-forth system containing the pair. -/
theorem le_equivK {E : PebbleRel A k} (h : E.Le (pebbleRefine E₀ E)) :
    E.Le (EquivK E₀) := by
  intro a b hab n
  induction n generalizing a b with
  | zero => trivial
  | succ n ih => exact pebbleRefine_mono E₀ ih a b (h a b hab)


-- @@ L153-153 verbatim
/-! ### Stabilization on a finite type -/


-- @@ L155-155 verbatim
section Finite


-- @@ L157-157 verbatim
variable [Finite A]


-- @@ L159-170 verbatim
/-- The refinement chain plateaus within the number of pairs of `k`-tuples:
consecutive stages agree from there on. -/
theorem exists_pebbleStage_succ_eq (E₀ : PebbleRel A k) :
    ∃ N ≤ Nat.card ((Fin k → A) × (Fin k → A)),
      pebbleStage E₀ (N + 1) = pebbleStage E₀ N := by
  obtain ⟨N, hN, heq⟩ := exists_succ_eq_of_antitone_subset
    (c := fun n => {p : (Fin k → A) × (Fin k → A) | pebbleStage E₀ n p.1 p.2})
    (fun n p hp => pebbleStage_succ_le E₀ n p.1 p.2 hp)
  refine ⟨N, hN, ?_⟩
  funext a b
  exact propext ⟨fun h => (Set.ext_iff.mp heq (a, b)).mp h,
    fun h => (Set.ext_iff.mp heq (a, b)).mpr h⟩


-- @@ L172-184 verbatim
omit [Finite A] in
private theorem pebbleStage_eq_of_succ_eq {N : ℕ}
    (hN : pebbleStage E₀ (N + 1) = pebbleStage E₀ N) {n : ℕ} (hn : N ≤ n) :
    pebbleStage E₀ n = pebbleStage E₀ N := by
  induction n with
  | zero => rw [Nat.le_zero.mp hn]
  | succ n ih =>
    rcases Nat.lt_or_ge N (n + 1) with h | h
    · have : pebbleStage E₀ n = pebbleStage E₀ N := ih (by omega)
      calc pebbleStage E₀ (n + 1) = pebbleRefine E₀ (pebbleStage E₀ n) := rfl
        _ = pebbleRefine E₀ (pebbleStage E₀ N) := by rw [this]
        _ = pebbleStage E₀ N := hN
    · rw [le_antisymm hn h]


-- @@ L186-198 verbatim
/-- **On a finite type the limit is a fixed point of the refinement** – the
greatest one, by `DescriptiveComplexity.le_equivK`. -/
theorem pebbleRefine_equivK (E₀ : PebbleRel A k) :
    pebbleRefine E₀ (EquivK E₀) = EquivK E₀ := by
  obtain ⟨N, hle, hN⟩ := exists_pebbleStage_succ_eq E₀
  have hlim : EquivK E₀ = pebbleStage E₀ N := by
    funext a b
    refine propext ⟨fun h => h N, fun h n => ?_⟩
    rcases Nat.le_total n N with hn | hn
    · exact pebbleStage_le_of_le E₀ hn a b h
    · rw [pebbleStage_eq_of_succ_eq hN hn]; exact h
  rw [hlim]
  exact hN


-- @@ L200-206 verbatim
/-- **The interface characterization of `≡ᵏ` on a finite type**: initial
agreement together with the back-and-forth condition relative to `≡ᵏ`
itself. Consumers should use this, never the stages. -/
theorem equivK_iff (E₀ : PebbleRel A k) (a b : Fin k → A) :
    EquivK E₀ a b ↔ E₀ a b ∧ PebbleBackForth (EquivK E₀) a b := by
  conv_lhs => rw [← pebbleRefine_equivK E₀]
  exact Iff.rfl


-- @@ L208-212 verbatim
/-- **The game move**: from an equivalent pair, moving a pebble on the left
can be answered on the right. -/
theorem EquivK.update {a b : Fin k → A} (h : EquivK E₀ a b) (i : Fin k) (c : A) :
    ∃ d : A, EquivK E₀ (Function.update a i c) (Function.update b i d) :=
  (((equivK_iff E₀ a b).mp h).2 i).1 c


-- @@ L214-217 verbatim
/-- The game move, from the right. -/
theorem EquivK.update_right {a b : Fin k → A} (h : EquivK E₀ a b) (i : Fin k) (d : A) :
    ∃ c : A, EquivK E₀ (Function.update a i c) (Function.update b i d) :=
  (((equivK_iff E₀ a b).mp h).2 i).2 d


-- @@ L219-225 verbatim
/-! ### Pair substructures

A tuple pair obtained by selecting, permuting and repeating coordinate pairs
of an equivalent pair is equivalent: duplicated pebbles only make the
duplicator's task easier. This is the well-definedness lemma behind every
operation on `≡ᵏ`-classes that rearranges coordinates – the substitution and
rearrangement relations of the invariant structure. -/


-- @@ L227-273 verbatim
/-- **Equivalence is inherited by pair substructures**: if every coordinate
pair of `(x, y)` is a coordinate pair of `(u, v)`, and the initial relation is
closed under this passage, then `u ≡ᵏ v` forces `x ≡ᵏ y`. Coinduction: the
spoiler's move on `(x, y)` frees a pebble of `(u, v)` (at most `k - 1` pairs
are still needed), where the duplicator answers via the game move. -/
theorem equivK_of_pairSub
    (hE₀ : ∀ {x y u v : Fin k → A}, (∀ j, ∃ i, x j = u i ∧ y j = v i) →
      E₀ u v → E₀ x y)
    {x y u v : Fin k → A} (hsub : ∀ j, ∃ i, x j = u i ∧ y j = v i)
    (huv : EquivK E₀ u v) : EquivK E₀ x y := by
  classical
  refine le_equivK (E := fun x y => ∃ u v, EquivK E₀ u v ∧
    ∀ j, ∃ i, x j = u i ∧ y j = v i) ?_ x y ⟨u, v, huv, hsub⟩
  rintro x y ⟨u, v, huv, hsub⟩
  choose I hI using hsub
  -- a pebble of `(u, v)` not needed once pebble `j` of `(x, y)` is replaced
  have hfree : ∀ j : Fin k, ∃ i : Fin k, i ∉ (Finset.univ.erase j).image I := by
    intro j
    obtain ⟨i, -, hi⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := (Finset.univ.erase j).image I) (t := Finset.univ)
      (lt_of_le_of_lt Finset.card_image_le
        (Finset.card_erase_lt_of_mem (Finset.mem_univ j)))
    exact ⟨i, hi⟩
  -- the substructure witness after a joint move at pebbles `j` and `i`
  have hwit : ∀ (j i : Fin k), i ∉ (Finset.univ.erase j).image I →
      ∀ c d : A, ∀ j' : Fin k, ∃ i',
        Function.update x j c j' = Function.update u i c i' ∧
          Function.update y j d j' = Function.update v i d i' := by
    intro j i hi c d j'
    by_cases hj : j' = j
    · subst hj
      exact ⟨i, by rw [Function.update_self, Function.update_self,
        Function.update_self, Function.update_self]; exact ⟨rfl, rfl⟩⟩
    · refine ⟨I j', ?_⟩
      have hne : I j' ≠ i := fun heq =>
        hi (heq ▸ Finset.mem_image_of_mem I (Finset.mem_erase.mpr
          ⟨hj, Finset.mem_univ j'⟩))
      rw [Function.update_of_ne hj, Function.update_of_ne hj,
        Function.update_of_ne hne, Function.update_of_ne hne]
      exact hI j'
  refine ⟨hE₀ (fun j => ⟨I j, hI j⟩) huv.initial, fun j => ⟨fun c => ?_, fun d => ?_⟩⟩
  · obtain ⟨i, hi⟩ := hfree j
    obtain ⟨d, hd⟩ := huv.update i c
    exact ⟨d, Function.update u i c, Function.update v i d, hd, hwit j i hi c d⟩
  · obtain ⟨i, hi⟩ := hfree j
    obtain ⟨c, hc⟩ := huv.update_right i d
    exact ⟨c, Function.update u i c, Function.update v i d, hc, hwit j i hi c d⟩


-- @@ L275-275 verbatim
end Finite


-- @@ L277-277 verbatim
/-! ### Equivalence -/


-- @@ L279-279 verbatim
section Equivalence


-- @@ L281-284 verbatim
/-- The back-and-forth condition preserves reflexivity. -/
theorem pebbleBackForth_refl {E : PebbleRel A k} (h : ∀ a, E a a) (a : Fin k → A) :
    PebbleBackForth E a a :=
  fun _ => ⟨fun c => ⟨c, h _⟩, fun d => ⟨d, h _⟩⟩


-- @@ L286-294 verbatim
/-- The back-and-forth condition preserves symmetry. -/
theorem pebbleBackForth_symm {E : PebbleRel A k} (h : ∀ a b, E a b → E b a)
    {a b : Fin k → A} (hab : PebbleBackForth E a b) : PebbleBackForth E b a := by
  intro i
  refine ⟨fun c => ?_, fun d => ?_⟩
  · obtain ⟨d, hd⟩ := (hab i).2 c
    exact ⟨d, h _ _ hd⟩
  · obtain ⟨c, hc⟩ := (hab i).1 d
    exact ⟨c, h _ _ hc⟩


-- @@ L296-307 verbatim
/-- The back-and-forth condition preserves transitivity. -/
theorem pebbleBackForth_trans {E : PebbleRel A k} (h : ∀ a b c, E a b → E b c → E a c)
    {a b c : Fin k → A} (hab : PebbleBackForth E a b) (hbc : PebbleBackForth E b c) :
    PebbleBackForth E a c := by
  intro i
  refine ⟨fun x => ?_, fun z => ?_⟩
  · obtain ⟨y, hy⟩ := (hab i).1 x
    obtain ⟨z, hz⟩ := (hbc i).1 y
    exact ⟨z, h _ _ _ hy hz⟩
  · obtain ⟨y, hy⟩ := (hbc i).2 z
    obtain ⟨x, hx⟩ := (hab i).2 y
    exact ⟨x, h _ _ _ hx hy⟩


-- @@ L309-320 verbatim
/-- Every stage of the refinement chain of an equivalence is an
equivalence. -/
theorem pebbleStage_equivalence (hE₀ : Equivalence E₀) (n : ℕ) :
    Equivalence (pebbleStage E₀ n) := by
  induction n with
  | zero => exact ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩
  | succ n ih =>
    exact ⟨fun a => ⟨hE₀.refl a, pebbleBackForth_refl (fun x => ih.refl x) a⟩,
      fun hab => ⟨hE₀.symm hab.1, pebbleBackForth_symm (fun _ _ h => ih.symm h) hab.2⟩,
      fun hab hbc => ⟨hE₀.trans hab.1 hbc.1,
        pebbleBackForth_trans (E := pebbleStage E₀ n)
          (fun _ _ _ h h' => ih.trans h h') hab.2 hbc.2⟩⟩


-- @@ L322-326 verbatim
/-- **`≡ᵏ` is an equivalence** whenever the initial relation is one. -/
theorem equivK_equivalence (hE₀ : Equivalence E₀) : Equivalence (EquivK E₀) :=
  ⟨fun a n => (pebbleStage_equivalence hE₀ n).refl a,
    fun h n => (pebbleStage_equivalence hE₀ n).symm (h n),
    fun hab hbc n => (pebbleStage_equivalence hE₀ n).trans (hab n) (hbc n)⟩


-- @@ L328-328 verbatim
end Equivalence


-- @@ L330-330 verbatim
/-! ### Monotonicity and the expansion lemma -/


-- @@ L332-338 verbatim
/-- The stages are monotone in the initial relation. -/
theorem pebbleStage_mono {E₀ E₀' : PebbleRel A k} (h : E₀'.Le E₀) (n : ℕ) :
    (pebbleStage E₀' n).Le (pebbleStage E₀ n) := by
  induction n with
  | zero => exact fun _ _ h => h
  | succ n ih =>
    exact fun a b hab => ⟨h a b hab.1, pebbleBackForth_mono ih a b hab.2⟩


-- @@ L340-343 verbatim
/-- `≡ᵏ` is monotone in the initial relation. -/
theorem equivK_mono {E₀ E₀' : PebbleRel A k} (h : E₀'.Le E₀) :
    (EquivK E₀').Le (EquivK E₀) :=
  fun a b hab n => pebbleStage_mono h n a b (hab n)


-- @@ L345-355 verbatim
/-- **The expansion lemma**: refining the initial relation by anything `≡ᵏ`
already refines does not change `≡ᵏ`. Read with `E₀'` the conjunction of `E₀`
and agreement on an `≡ᵏ`-invariant relation, this says `≡ᵏ` is unchanged when
the structure is expanded by an `≡ᵏ`-invariant relation – the lemma that
carries the `≡ᵏ`-invariance of the fixed-point logics, stage by stage. -/
theorem equivK_inf_eq [Finite A] {E₀ E₀' : PebbleRel A k} (hle : E₀'.Le E₀)
    (hinv : (EquivK E₀).Le E₀') : EquivK E₀' = EquivK E₀ := by
  funext a b
  refine propext ⟨fun h => equivK_mono hle a b h, fun h => ?_⟩
  refine le_equivK (E₀ := E₀') (E := EquivK E₀) (fun a b hab => ?_) a b h
  exact ⟨hinv a b hab, ((equivK_iff E₀ a b).mp hab).2⟩


-- @@ L357-357 verbatim
end DescriptiveComplexity
