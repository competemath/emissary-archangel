/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Vocabulary
import DescriptiveComplexity.Interpretation
import DescriptiveComplexity.Numbers.Unary


-- @@ L10-53 verbatim
/-!
# Clique, Independent Set and Vertex Cover: definitions

The three classical threshold problems on graphs, as decision problems on
*marked graphs*: `FirstOrder.Language.markedGraph`-structures, carrying a
binary adjacency relation and a unary mark. The marked set carries the numeric
threshold `k` of the textbook problems in the *unary representation* of
`DescriptiveComplexity.Numbers.Unary`: the threshold is the cardinality
`Set.ncard` of the marked set, order-free and isomorphism-invariant for free.

* `DescriptiveComplexity.Clique`: some clique is at least as large as the marked set;
* `DescriptiveComplexity.IndependentSet`: some independent set is at least as large as
  the marked set;
* `DescriptiveComplexity.VertexCover`: some vertex cover is at most as large as the
  marked set.

The threshold comparisons are comparisons of decoded numbers, and the
cardinality arithmetic they need is the shared kit of
`DescriptiveComplexity.Numbers.Unary`: invariance of a decoded number under an
equivalence of universes (`DescriptiveComplexity.ncard_image_equiv`) for the
isomorphism-invariance proofs, the reversal of a comparison under
complementation (`DescriptiveComplexity.ncard_compl_le_ncard_compl_iff`) for the
Vertex Cover ↔ Independent Set reductions, and the equivalence with the
existence of an injection (`DescriptiveComplexity.nonempty_embedding_iff_ncard_le`,
here `DescriptiveComplexity.cliqueOn_iff_embedding`) for the second-order definition,
which guesses that injection as a relation variable. Since cardinality
thresholds are only meaningful on finite structures, finiteness of the
universe is part of the yes-instances; by `ComplexityClass.mem_congr_finite`
this does not affect any complexity-theoretic statement.

Self-loops are ignored (all three properties are about the underlying
loopless graph), and adjacency is required in both directions on ordered
pairs, so the problems agree with their standard versions on (structures
encoding) simple graphs.

The three predicates are instances of generic properties `DescriptiveComplexity.CliqueOn`
/ `IndepOn` / `CoverOn` of a binary and a unary predicate on a type; the
generic form is shared by the isomorphism-invariance proofs and by the
reductions of `DescriptiveComplexity.Problems.CliqueFamily.Reductions`.
-/

/- The language of marked graphs lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.graph` and `Language.order` – a project-local
`Language` namespace would shadow Mathlib's under `open Language`. -/

-- @@ L54-54 verbatim
namespace FirstOrder


-- @@ L56-56 verbatim
namespace Language


-- @@ L58-64 verbatim
/-- The relational language of marked graphs: a graph together with a marked
subset of its vertices, whose cardinality serves as threshold. -/
fo_language markedGraph with mg where
  /-- `adj a b`: there is an edge from `a` to `b`. -/
  adj : 2
  /-- `marked a`: the element `a` belongs to the marked set. -/
  marked : 1


-- @@ L66-66 verbatim
end Language


-- @@ L68-68 verbatim
end FirstOrder


-- @@ L70-70 verbatim
namespace DescriptiveComplexity


-- @@ L72-72 verbatim
open FirstOrder


-- @@ L74-74 verbatim
open Language Structure


-- @@ L76-79 verbatim
/-! ### Generic threshold properties

The properties underlying the three problems, for an arbitrary binary
predicate `Adjp` (adjacency) and unary predicate `Kp` (marks) on a type. -/


-- @@ L81-81 verbatim
section Generic


-- @@ L83-83 verbatim
variable {A : Type}


-- @@ L85-90 verbatim
/-- Some set that is pairwise `Adjp`-related (off the diagonal) is at least as
large as the number encoded by the `Kp`-marked elements: “some clique is at
least as large as the marked set”. -/
def CliqueOn (Adjp : A → A → Prop) (Kp : A → Prop) : Prop :=
  ∃ S : A → Prop, (∀ x y, S x → S y → x ≠ y → Adjp x y) ∧
    {x | Kp x}.ncard ≤ {x | S x}.ncard


-- @@ L92-96 verbatim
/-- Some set that is pairwise non-`Adjp`-related (off the diagonal) is at least
as large as the number encoded by the `Kp`-marked elements: “some independent
set is at least as large as the marked set”. -/
def IndepOn (Adjp : A → A → Prop) (Kp : A → Prop) : Prop :=
  CliqueOn (fun x y => ¬Adjp x y) Kp


-- @@ L98-103 verbatim
/-- Some set meeting every (off-diagonal) `Adjp`-edge is at most as large as
the number encoded by the `Kp`-marked elements: “some vertex cover is at most
as large as the marked set”. -/
def CoverOn (Adjp : A → A → Prop) (Kp : A → Prop) : Prop :=
  ∃ C : A → Prop, (∀ x y, x ≠ y → Adjp x y → C x ∨ C y) ∧
    {x | C x}.ncard ≤ {x | Kp x}.ncard


-- @@ L105-109 verbatim
/-! #### The threshold as an injection

On a finite universe, comparing the decoded numbers is comparing sizes, so the
threshold conditions can equivalently be read as the existence of an injection.
This is the form the second-order definitions guess. -/


-- @@ L111-111 verbatim
section Embedding


-- @@ L113-113 verbatim
variable [Finite A]


-- @@ L115-120 verbatim
/-- The clique threshold as an injection of the marked set into the clique. -/
theorem cliqueOn_iff_embedding (Adjp : A → A → Prop) (Kp : A → Prop) :
    CliqueOn Adjp Kp ↔ ∃ S : A → Prop, (∀ x y, S x → S y → x ≠ y → Adjp x y) ∧
      Nonempty ({x // Kp x} ↪ {x // S x}) :=
  exists_congr fun S =>
    and_congr_right fun _ => (nonempty_embedding_iff_ncard_le Kp S).symm


-- @@ L122-122 verbatim
end Embedding


-- @@ L124-124 verbatim
variable {B : Type}


-- @@ L126-138 verbatim
/-- `CliqueOn` transports along an equivalence commuting with the two
predicates. -/
theorem CliqueOn.of_equiv (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b))
    (h : CliqueOn AdjB KB) : CliqueOn AdjA KA := by
  obtain ⟨S, hS, hcard⟩ := h
  refine ⟨fun a => S (u.symm a), fun x y hx hy hxy => ?_, ?_⟩
  · have h' := (hadj (u.symm x) (u.symm y)).mp
      (hS _ _ hx hy fun h => hxy (u.symm.injective h))
    simpa using h'
  · rw [← ncard_setOf_equiv u hK, ← ncard_setOf_symm u S]
    exact hcard


-- @@ L140-146 verbatim
/-- `IndepOn` transports along an equivalence commuting with the two
predicates. -/
theorem IndepOn.of_equiv (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b))
    (h : IndepOn AdjB KB) : IndepOn AdjA KA :=
  CliqueOn.of_equiv u (fun b b' => not_congr (hadj b b')) hK h


-- @@ L148-159 verbatim
/-- `CoverOn` transports along an equivalence commuting with the two
predicates. -/
theorem CoverOn.of_equiv (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b))
    (h : CoverOn AdjB KB) : CoverOn AdjA KA := by
  obtain ⟨C, hC, hcard⟩ := h
  refine ⟨fun a => C (u.symm a), fun x y hxy hadjA => ?_, ?_⟩
  · exact hC (u.symm x) (u.symm y) (fun h => hxy (u.symm.injective h))
      ((hadj (u.symm x) (u.symm y)).mpr (by simpa using hadjA))
  · rw [← ncard_setOf_equiv u hK, ← ncard_setOf_symm u C]
    exact hcard


-- @@ L161-165 verbatim
private theorem symm_hadj {AdjB : B → B → Prop} {AdjA : A → A → Prop} (u : B ≃ A)
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (a a' : A) :
    AdjA a a' ↔ AdjB (u.symm a) (u.symm a') := by
  rw [hadj]
  simp


-- @@ L167-170 verbatim
private theorem symm_hK {KB : B → Prop} {KA : A → Prop} (u : B ≃ A)
    (hK : ∀ b, KB b ↔ KA (u b)) (a : A) : KA a ↔ KB (u.symm a) := by
  rw [hK]
  simp


-- @@ L172-178 verbatim
/-- `CliqueOn` transports along an equivalence, iff version. -/
theorem CliqueOn.equiv_iff (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    CliqueOn AdjB KB ↔ CliqueOn AdjA KA :=
  ⟨CliqueOn.of_equiv u hadj hK,
    CliqueOn.of_equiv u.symm (symm_hadj u hadj) (symm_hK u hK)⟩


-- @@ L180-186 verbatim
/-- `IndepOn` transports along an equivalence, iff version. -/
theorem IndepOn.equiv_iff (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    IndepOn AdjB KB ↔ IndepOn AdjA KA :=
  ⟨IndepOn.of_equiv u hadj hK,
    IndepOn.of_equiv u.symm (symm_hadj u hadj) (symm_hK u hK)⟩


-- @@ L188-194 verbatim
/-- `CoverOn` transports along an equivalence, iff version. -/
theorem CoverOn.equiv_iff (u : B ≃ A) {AdjB : B → B → Prop} {KB : B → Prop}
    {AdjA : A → A → Prop} {KA : A → Prop}
    (hadj : ∀ b b', AdjB b b' ↔ AdjA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    CoverOn AdjB KB ↔ CoverOn AdjA KA :=
  ⟨CoverOn.of_equiv u hadj hK,
    CoverOn.of_equiv u.symm (symm_hadj u hadj) (symm_hK u hK)⟩


-- @@ L196-207 verbatim
/-- `CliqueOn` only depends on the off-diagonal part of the adjacency
predicate and on the extension of the mark predicate. -/
theorem cliqueOn_congr {P Q : A → A → Prop} {K K' : A → Prop}
    (hPQ : ∀ x y, x ≠ y → (P x y ↔ Q x y)) (hK : ∀ x, K x ↔ K' x) :
    CliqueOn P K ↔ CliqueOn Q K' := by
  have h : ∀ {P Q : A → A → Prop} {K K' : A → Prop},
      (∀ x y, x ≠ y → (P x y ↔ Q x y)) → (∀ x, K x ↔ K' x) →
      CliqueOn P K → CliqueOn Q K' := by
    rintro P Q K K' hPQ hK ⟨S, hS, hcard⟩
    refine ⟨S, fun x y hx hy hxy => (hPQ x y hxy).mp (hS x y hx hy hxy), ?_⟩
    rwa [show {x | K' x} = {x | K x} from Set.ext fun x => (hK x).symm]
  exact ⟨h hPQ hK, h (fun x y hxy => (hPQ x y hxy).symm) fun x => (hK x).symm⟩


-- @@ L209-214 verbatim
/-- `IndepOn` only depends on the off-diagonal part of the adjacency
predicate and on the extension of the mark predicate. -/
theorem indepOn_congr {P Q : A → A → Prop} {K K' : A → Prop}
    (hPQ : ∀ x y, x ≠ y → (P x y ↔ Q x y)) (hK : ∀ x, K x ↔ K' x) :
    IndepOn P K ↔ IndepOn Q K' :=
  cliqueOn_congr (fun x y hxy => not_congr (hPQ x y hxy)) hK


-- @@ L216-216 verbatim
end Generic


-- @@ L218-218 verbatim
/-! ### The three problems -/


-- @@ L220-220 verbatim
section Problems


-- @@ L222-222 verbatim
section Shorthands


-- @@ L224-224 verbatim
variable {A : Type} [Language.markedGraph.Structure A]


-- @@ L226-226 verbatim
fo_predicates Language.markedGraph mg


-- @@ L228-228 verbatim
end Shorthands


-- @@ L230-230 verbatim
variable (A : Type) [Language.markedGraph.Structure A]


-- @@ L232-236 verbatim
/-- A marked graph contains a clique at least as large as its marked set.
(Finiteness of the universe is part of the property: cardinality thresholds
are only meaningful on finite structures.) -/
def HasLargeClique : Prop :=
  Finite A ∧ CliqueOn (MGAdj (A := A)) (MGMarked (A := A))


-- @@ L238-241 verbatim
/-- A marked graph contains an independent set at least as large as its
marked set. -/
def HasLargeIndependentSet : Prop :=
  Finite A ∧ IndepOn (MGAdj (A := A)) (MGMarked (A := A))


-- @@ L243-246 verbatim
/-- A marked graph contains a vertex cover at most as large as its marked
set. -/
def HasSmallVertexCover : Prop :=
  Finite A ∧ CoverOn (MGAdj (A := A)) (MGMarked (A := A))


-- @@ L248-248 verbatim
end Problems


-- @@ L250-250 verbatim
/-! ### Isomorphism-invariance and the bundled problems -/


-- @@ L252-252 verbatim
section Iso


-- @@ L254-254 verbatim
variable {A B : Type} [Language.markedGraph.Structure A] [Language.markedGraph.Structure B]


-- @@ L256-258 verbatim
private theorem mgAdj_map (e : A ≃[Language.markedGraph] B) (a b : A) :
    MGAdj a b ↔ MGAdj (e a) (e b) :=
  relMap_equiv₂ e mgAdj a b


-- @@ L260-262 verbatim
private theorem mgMarked_map (e : A ≃[Language.markedGraph] B) (a : A) :
    MGMarked a ↔ MGMarked (e a) :=
  relMap_equiv₁ e mgMarked a


-- @@ L264-268 verbatim
/-- The clique threshold property is isomorphism-invariant. -/
theorem hasLargeClique_iso (e : A ≃[Language.markedGraph] B) :
    HasLargeClique A ↔ HasLargeClique B :=
  and_congr e.toEquiv.finite_iff
    (CliqueOn.equiv_iff e.toEquiv (mgAdj_map e) (mgMarked_map e))


-- @@ L270-274 verbatim
/-- The independent-set threshold property is isomorphism-invariant. -/
theorem hasLargeIndependentSet_iso (e : A ≃[Language.markedGraph] B) :
    HasLargeIndependentSet A ↔ HasLargeIndependentSet B :=
  and_congr e.toEquiv.finite_iff
    (IndepOn.equiv_iff e.toEquiv (mgAdj_map e) (mgMarked_map e))


-- @@ L276-280 verbatim
/-- The vertex-cover threshold property is isomorphism-invariant. -/
theorem hasSmallVertexCover_iso (e : A ≃[Language.markedGraph] B) :
    HasSmallVertexCover A ↔ HasSmallVertexCover B :=
  and_congr e.toEquiv.finite_iff
    (CoverOn.equiv_iff e.toEquiv (mgAdj_map e) (mgMarked_map e))


-- @@ L282-282 verbatim
end Iso


-- @@ L284-288 verbatim
/-- CLIQUE, as a problem on marked graphs: is there a clique at least as
large as the marked set? -/
def Clique : DecisionProblem Language.markedGraph where
  Holds := fun A inst => @HasLargeClique A inst
  iso_invariant := fun e => hasLargeClique_iso e


-- @@ L290-294 verbatim
/-- INDEPENDENT SET, as a problem on marked graphs: is there an independent
set at least as large as the marked set? -/
def IndependentSet : DecisionProblem Language.markedGraph where
  Holds := fun A inst => @HasLargeIndependentSet A inst
  iso_invariant := fun e => hasLargeIndependentSet_iso e


-- @@ L296-300 verbatim
/-- VERTEX COVER, as a problem on marked graphs: is there a vertex cover at
most as large as the marked set? -/
def VertexCover : DecisionProblem Language.markedGraph where
  Holds := fun A inst => @HasSmallVertexCover A inst
  iso_invariant := fun e => hasSmallVertexCover_iso e


-- @@ L302-302 verbatim
end DescriptiveComplexity
