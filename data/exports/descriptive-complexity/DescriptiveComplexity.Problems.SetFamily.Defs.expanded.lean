/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Vocabulary
import DescriptiveComplexity.Interpretation
import DescriptiveComplexity.Numbers.Unary


-- @@ L10-60 verbatim
/-!
# Set Cover, Hitting Set and Set Packing: definitions

The three classical problems on set systems ([Karp 1972][karp1972reducibility]),
as decision problems on `FirstOrder.Language.setSystem`-structures: a universe
carrying two unary marks separating the ground *elements* from the *sets* of a
family, a binary incidence relation between them, and a third unary mark
carrying the numeric threshold `k` in the *unary representation* of
`DescriptiveComplexity.Numbers.Unary` (the threshold is the cardinality
`Set.ncard` of the marked set, order-free and isomorphism-invariant for free).

* `DescriptiveComplexity.SetCover`: some subfamily of at most `k` sets covers every
  element;
* `DescriptiveComplexity.HittingSet`: some set of at most `k` elements meets every
  set of the family;
* `DescriptiveComplexity.SetPacking`: some subfamily of at least `k` pairwise
  disjoint sets exists.

They are the set-system counterparts of the clique family
(`DescriptiveComplexity.Problems.CliqueFamily`), and are organized the same way: the
semantics is carried by generic properties of predicates on a type –
`DescriptiveComplexity.CoversOn`, its transpose `DescriptiveComplexity.HitsOn` (elements
and sets exchanged, incidence read backwards) and `DescriptiveComplexity.PacksOn` –
which the isomorphism-invariance proofs and the reductions share. Set Cover
and Hitting Set being literally one property read in two directions is what
makes them inter-reducible by a single interpretation
(`DescriptiveComplexity.Problems.SetFamily.Reductions`), just as complementation
relates Clique and Independent Set.

Two conventions worth stating once:

* Nothing forces an element of the universe to be an element or a set, or
  forbids it to be both: elements outside both marks are junk that no
  condition mentions, which is what lets a first-order interpretation build a
  set system inside a tagged power of its input universe without a
  definable-subset mechanism. Junk *marked* elements would change the
  threshold, so interpretations remain responsible for the mark they define.
* Disjointness in `DescriptiveComplexity.PacksOn` is required of the ground
  elements only. This is not cosmetic: the interpretation of
  `DescriptiveComplexity.Problems.SetFamily.FromGraphs` produces junk tuples incident
  to two sets each, and those must not count as witnesses of an intersection.

As with the clique family, cardinality thresholds are only meaningful on
finite structures, so finiteness of the universe is part of the yes-instances;
by `DescriptiveComplexity.ComplexityClass.mem_congr_finite` this does not affect
any complexity-theoretic statement.
-/

/- The language of set systems lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.graph` and `Language.order` – a project-local
`Language` namespace would shadow Mathlib's under `open Language`. -/

-- @@ L61-61 verbatim
namespace FirstOrder


-- @@ L63-63 verbatim
namespace Language


-- @@ L65-76 verbatim
/-- The relational language of set systems: a bipartite incidence structure
between ground elements and sets of a family, together with a marked subset of
the universe whose cardinality serves as threshold. -/
fo_language setSystem with ss where
  /-- `elem a`: the element `a` belongs to the ground set. -/
  elem : 1
  /-- `fam a`: the element `a` is one of the sets of the family. -/
  fam : 1
  /-- `mem a b`: the ground element `a` belongs to the set `b`. -/
  mem : 2
  /-- `marked a`: the element `a` belongs to the marked set. -/
  marked : 1


-- @@ L78-78 verbatim
end Language


-- @@ L80-80 verbatim
end FirstOrder


-- @@ L82-82 verbatim
namespace DescriptiveComplexity


-- @@ L84-84 verbatim
open FirstOrder


-- @@ L86-86 verbatim
open Language Structure


-- @@ L88-92 verbatim
/-! ### The generic covering property

The property underlying both problems, for arbitrary unary predicates `Ep`
(ground elements), `Fp` (sets of the family) and `Kp` (marks), and an
arbitrary binary predicate `Mp` (incidence) on a type. -/


-- @@ L94-94 verbatim
section Generic


-- @@ L96-96 verbatim
variable {A : Type}


-- @@ L98-103 verbatim
/-- Some subfamily of the `Fp`-sets covers every `Ep`-element and is at most
as large as the number encoded by the `Kp`-marked elements: “some cover is at
most as large as the marked set”. -/
def CoversOn (Ep Fp : A → Prop) (Mp : A → A → Prop) (Kp : A → Prop) : Prop :=
  ∃ G : A → Prop, (∀ s, G s → Fp s) ∧ (∀ x, Ep x → ∃ s, G s ∧ Mp x s) ∧
    {s | G s}.ncard ≤ {x | Kp x}.ncard


-- @@ L105-110 verbatim
/-- Some set of `Ep`-elements meets every `Fp`-set and is at most as large as
the number encoded by the `Kp`-marked elements: “some hitting set is at most
as large as the marked set”. This is `DescriptiveComplexity.CoversOn` with the roles
of elements and sets exchanged and the incidence relation transposed. -/
def HitsOn (Ep Fp : A → Prop) (Mp : A → A → Prop) (Kp : A → Prop) : Prop :=
  CoversOn Fp Ep (fun s x => Mp x s) Kp


-- @@ L112-119 verbatim
/-- Some subfamily of the `Fp`-sets is pairwise disjoint – no `Ep`-element
belongs to two distinct members – and is at least as large as the number
encoded by the `Kp`-marked elements: “some packing is at least as large as the
marked set”. -/
def PacksOn (Ep Fp : A → Prop) (Mp : A → A → Prop) (Kp : A → Prop) : Prop :=
  ∃ G : A → Prop, (∀ s, G s → Fp s) ∧
    (∀ s s', G s → G s' → s ≠ s' → ∀ x, Ep x → ¬(Mp x s ∧ Mp x s')) ∧
    {x | Kp x}.ncard ≤ {s | G s}.ncard


-- @@ L121-127 verbatim
/-- Some subfamily of the `Fp`-sets covers every `Ep`-element *exactly once*:
it covers, and no element belongs to two distinct members. Unlike the three
properties above this one carries no threshold – exactness is the whole
constraint. -/
def ExactlyCoversOn (Ep Fp : A → Prop) (Mp : A → A → Prop) : Prop :=
  ∃ G : A → Prop, (∀ s, G s → Fp s) ∧ (∀ x, Ep x → ∃ s, G s ∧ Mp x s) ∧
    ∀ s s', G s → G s' → s ≠ s' → ∀ x, Ep x → ¬(Mp x s ∧ Mp x s')


-- @@ L129-135 verbatim
/-- The subfamily `G` is an exact cover: it consists of `Fp`-sets, covers every
`Ep`-element, and no element belongs to two distinct members. This is the body
of `DescriptiveComplexity.ExactlyCoversOn`, named for the statements that are about a
particular cover and not only about the existence of one. -/
def ExactCoverBy (Ep Fp : A → Prop) (Mp : A → A → Prop) (G : A → Prop) : Prop :=
  (∀ s, G s → Fp s) ∧ (∀ x, Ep x → ∃ s, G s ∧ Mp x s) ∧
    ∀ s s', G s → G s' → s ≠ s' → ∀ x, Ep x → ¬(Mp x s ∧ Mp x s')


-- @@ L137-139 verbatim
theorem exactlyCoversOn_iff_exists (Ep Fp : A → Prop) (Mp : A → A → Prop) :
    ExactlyCoversOn Ep Fp Mp ↔ ∃ G : A → Prop, ExactCoverBy Ep Fp Mp G :=
  Iff.rfl


-- @@ L141-158 verbatim
/-- Exactness of a given subfamily in the “exactly one” form: covering plus
disjointness is one covering set per element. -/
theorem exactCoverBy_iff_unique (Ep Fp : A → Prop) (Mp : A → A → Prop) (G : A → Prop) :
    ExactCoverBy Ep Fp Mp G ↔ (∀ s, G s → Fp s) ∧ ∀ x, Ep x → ∃! s, G s ∧ Mp x s := by
  refine and_congr_right fun _ => ?_
  constructor
  · rintro ⟨hcov, hdisj⟩ x hx
    obtain ⟨s, hs, hms⟩ := hcov x hx
    refine ⟨s, ⟨hs, hms⟩, fun s' hs' => ?_⟩
    by_contra hne
    exact hdisj s' s hs'.1 hs hne x hx ⟨hs'.2, hms⟩
  · intro h
    refine ⟨fun x hx => ?_, fun s s' hs hs' hne x hx => ?_⟩
    · obtain ⟨s, hs, -⟩ := h x hx
      exact ⟨s, hs⟩
    · rintro ⟨h1, h2⟩
      obtain ⟨s₀, -, huniq⟩ := h x hx
      exact hne ((huniq s ⟨hs, h1⟩).trans (huniq s' ⟨hs', h2⟩).symm)


-- @@ L160-165 verbatim
/-- Exactness in the “exactly one” form: covering plus disjointness is one
covering set per element. -/
theorem exactlyCoversOn_iff_unique (Ep Fp : A → Prop) (Mp : A → A → Prop) :
    ExactlyCoversOn Ep Fp Mp ↔ ∃ G : A → Prop, (∀ s, G s → Fp s) ∧
      ∀ x, Ep x → ∃! s, G s ∧ Mp x s :=
  exists_congr fun G => exactCoverBy_iff_unique Ep Fp Mp G


-- @@ L167-172 verbatim
/-- Some two-coloring of the ground elements *splits* every set of the
family: no set is monochromatic. Like `DescriptiveComplexity.ExactlyCoversOn` this
property carries no threshold. -/
def SplitsOn (Ep Fp : A → Prop) (Mp : A → A → Prop) : Prop :=
  ∃ S : A → Prop, ∀ f, Fp f →
    (∃ x, Ep x ∧ Mp x f ∧ S x) ∧ ∃ x, Ep x ∧ Mp x f ∧ ¬S x


-- @@ L174-178 verbatim
/-! #### The threshold as an injection

On a finite universe, comparing the decoded numbers is comparing sizes, so the
threshold condition can equivalently be read as the existence of an injection.
This is the form the second-order definitions guess. -/


-- @@ L180-180 verbatim
section Embedding


-- @@ L182-182 verbatim
variable [Finite A]


-- @@ L184-190 verbatim
/-- The cover threshold as an injection of the cover into the marked set. -/
theorem coversOn_iff_embedding (Ep Fp : A → Prop) (Mp : A → A → Prop) (Kp : A → Prop) :
    CoversOn Ep Fp Mp Kp ↔ ∃ G : A → Prop, (∀ s, G s → Fp s) ∧
      (∀ x, Ep x → ∃ s, G s ∧ Mp x s) ∧ Nonempty ({s // G s} ↪ {x // Kp x}) :=
  exists_congr fun G =>
    and_congr_right fun _ =>
      and_congr_right fun _ => (nonempty_embedding_iff_ncard_le G Kp).symm


-- @@ L192-200 verbatim
/-- The packing threshold as an injection of the marked set into the packing:
a *lower* bound, so the injection runs the other way round. -/
theorem packsOn_iff_embedding (Ep Fp : A → Prop) (Mp : A → A → Prop) (Kp : A → Prop) :
    PacksOn Ep Fp Mp Kp ↔ ∃ G : A → Prop, (∀ s, G s → Fp s) ∧
      (∀ s s', G s → G s' → s ≠ s' → ∀ x, Ep x → ¬(Mp x s ∧ Mp x s')) ∧
      Nonempty ({x // Kp x} ↪ {s // G s}) :=
  exists_congr fun G =>
    and_congr_right fun _ =>
      and_congr_right fun _ => (nonempty_embedding_iff_ncard_le Kp G).symm


-- @@ L202-202 verbatim
end Embedding


-- @@ L204-204 verbatim
variable {B : Type}


-- @@ L206-222 verbatim
/-- `CoversOn` transports along an equivalence commuting with the four
predicates. -/
theorem CoversOn.of_equiv (u : B ≃ A) {EB FB KB : B → Prop} {MB : B → B → Prop}
    {EA FA KA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b))
    (h : CoversOn EB FB MB KB) : CoversOn EA FA MA KA := by
  obtain ⟨G, hGF, hcov, hcard⟩ := h
  refine ⟨fun a => G (u.symm a), fun s hs => ?_, fun x hx => ?_, ?_⟩
  · have := (hF (u.symm s)).mp (hGF _ hs)
    simpa using this
  · obtain ⟨s, hs, hms⟩ := hcov (u.symm x) ((hE (u.symm x)).mpr (by simpa using hx))
    refine ⟨u s, by simpa using hs, ?_⟩
    have := (hM (u.symm x) s).mp hms
    simpa using this
  · rw [← ncard_setOf_equiv u hK, ← ncard_setOf_symm u G]
    exact hcard


-- @@ L224-227 verbatim
private theorem symm_hUn {PB : B → Prop} {PA : A → Prop} (u : B ≃ A)
    (hP : ∀ b, PB b ↔ PA (u b)) (a : A) : PA a ↔ PB (u.symm a) := by
  rw [hP]
  simp


-- @@ L229-233 verbatim
private theorem symm_hBin {MB : B → B → Prop} {MA : A → A → Prop} (u : B ≃ A)
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (a a' : A) :
    MA a a' ↔ MB (u.symm a) (u.symm a') := by
  rw [hM]
  simp


-- @@ L235-243 verbatim
/-- `CoversOn` transports along an equivalence, iff version. -/
theorem CoversOn.equiv_iff (u : B ≃ A) {EB FB KB : B → Prop} {MB : B → B → Prop}
    {EA FA KA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    CoversOn EB FB MB KB ↔ CoversOn EA FA MA KA :=
  ⟨CoversOn.of_equiv u hE hF hM hK,
    CoversOn.of_equiv u.symm (symm_hUn u hE) (symm_hUn u hF) (symm_hBin u hM)
      (symm_hUn u hK)⟩


-- @@ L245-251 verbatim
/-- `HitsOn` transports along an equivalence, iff version. -/
theorem HitsOn.equiv_iff (u : B ≃ A) {EB FB KB : B → Prop} {MB : B → B → Prop}
    {EA FA KA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    HitsOn EB FB MB KB ↔ HitsOn EA FA MA KA :=
  CoversOn.equiv_iff u hF hE (fun b b' => hM b' b) hK


-- @@ L253-270 verbatim
/-- `PacksOn` transports along an equivalence commuting with the four
predicates. -/
theorem PacksOn.of_equiv (u : B ≃ A) {EB FB KB : B → Prop} {MB : B → B → Prop}
    {EA FA KA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b))
    (h : PacksOn EB FB MB KB) : PacksOn EA FA MA KA := by
  obtain ⟨G, hGF, hdisj, hcard⟩ := h
  refine ⟨fun a => G (u.symm a), fun s hs => ?_, fun s s' hs hs' hne x hx => ?_, ?_⟩
  · have := (hF (u.symm s)).mp (hGF _ hs)
    simpa using this
  · rintro ⟨h1, h2⟩
    exact hdisj (u.symm s) (u.symm s') hs hs' (fun h => hne (u.symm.injective h))
      (u.symm x) ((hE (u.symm x)).mpr (by simpa using hx))
      ⟨(hM (u.symm x) (u.symm s)).mpr (by simpa using h1),
        (hM (u.symm x) (u.symm s')).mpr (by simpa using h2)⟩
  · rw [← ncard_setOf_equiv u hK, ← ncard_setOf_symm u G]
    exact hcard


-- @@ L272-292 verbatim
/-- `ExactlyCoversOn` transports along an equivalence commuting with the three
predicates. -/
theorem ExactlyCoversOn.of_equiv (u : B ≃ A) {EB FB : B → Prop} {MB : B → B → Prop}
    {EA FA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (h : ExactlyCoversOn EB FB MB) :
    ExactlyCoversOn EA FA MA := by
  obtain ⟨G, hGF, hcov, hdisj⟩ := h
  refine ⟨fun a => G (u.symm a), fun s hs => ?_, fun x hx => ?_,
    fun s s' hs hs' hne x hx => ?_⟩
  · have := (hF (u.symm s)).mp (hGF _ hs)
    simpa using this
  · obtain ⟨s, hs, hms⟩ := hcov (u.symm x) ((hE (u.symm x)).mpr (by simpa using hx))
    refine ⟨u s, by simpa using hs, ?_⟩
    have := (hM (u.symm x) s).mp hms
    simpa using this
  · rintro ⟨h1, h2⟩
    exact hdisj (u.symm s) (u.symm s') hs hs' (fun h => hne (u.symm.injective h))
      (u.symm x) ((hE (u.symm x)).mpr (by simpa using hx))
      ⟨(hM (u.symm x) (u.symm s)).mpr (by simpa using h1),
        (hM (u.symm x) (u.symm s')).mpr (by simpa using h2)⟩


-- @@ L294-311 verbatim
/-- `SplitsOn` transports along an equivalence commuting with the three
predicates. -/
theorem SplitsOn.of_equiv (u : B ≃ A) {EB FB : B → Prop} {MB : B → B → Prop}
    {EA FA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (h : SplitsOn EB FB MB) :
    SplitsOn EA FA MA := by
  obtain ⟨S, hS⟩ := h
  refine ⟨fun a => S (u.symm a), fun f hf => ?_⟩
  obtain ⟨⟨x, hx, hmx, hSx⟩, ⟨y, hy, hmy, hSy⟩⟩ :=
    hS (u.symm f) ((hF (u.symm f)).mpr (by simpa using hf))
  constructor
  · refine ⟨u x, (hE x).mp hx, ?_, by simpa using hSx⟩
    have := (hM x (u.symm f)).mp hmx
    simpa using this
  · refine ⟨u y, (hE y).mp hy, ?_, by simpa using hSy⟩
    have := (hM y (u.symm f)).mp hmy
    simpa using this


-- @@ L313-320 verbatim
/-- `SplitsOn` transports along an equivalence, iff version. -/
theorem SplitsOn.equiv_iff (u : B ≃ A) {EB FB : B → Prop} {MB : B → B → Prop}
    {EA FA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) :
    SplitsOn EB FB MB ↔ SplitsOn EA FA MA :=
  ⟨SplitsOn.of_equiv u hE hF hM,
    SplitsOn.of_equiv u.symm (symm_hUn u hE) (symm_hUn u hF) (symm_hBin u hM)⟩


-- @@ L322-329 verbatim
/-- `ExactlyCoversOn` transports along an equivalence, iff version. -/
theorem ExactlyCoversOn.equiv_iff (u : B ≃ A) {EB FB : B → Prop} {MB : B → B → Prop}
    {EA FA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) :
    ExactlyCoversOn EB FB MB ↔ ExactlyCoversOn EA FA MA :=
  ⟨ExactlyCoversOn.of_equiv u hE hF hM,
    ExactlyCoversOn.of_equiv u.symm (symm_hUn u hE) (symm_hUn u hF) (symm_hBin u hM)⟩


-- @@ L331-339 verbatim
/-- `PacksOn` transports along an equivalence, iff version. -/
theorem PacksOn.equiv_iff (u : B ≃ A) {EB FB KB : B → Prop} {MB : B → B → Prop}
    {EA FA KA : A → Prop} {MA : A → A → Prop}
    (hE : ∀ b, EB b ↔ EA (u b)) (hF : ∀ b, FB b ↔ FA (u b))
    (hM : ∀ b b', MB b b' ↔ MA (u b) (u b')) (hK : ∀ b, KB b ↔ KA (u b)) :
    PacksOn EB FB MB KB ↔ PacksOn EA FA MA KA :=
  ⟨PacksOn.of_equiv u hE hF hM hK,
    PacksOn.of_equiv u.symm (symm_hUn u hE) (symm_hUn u hF) (symm_hBin u hM)
      (symm_hUn u hK)⟩


-- @@ L341-341 verbatim
end Generic


-- @@ L343-343 verbatim
/-! ### The two problems -/


-- @@ L345-345 verbatim
section Problems


-- @@ L347-347 verbatim
section Shorthands


-- @@ L349-349 verbatim
variable {A : Type} [Language.setSystem.Structure A]


-- @@ L351-351 verbatim
fo_predicates Language.setSystem ss


-- @@ L353-353 verbatim
end Shorthands


-- @@ L355-355 verbatim
variable (A : Type) [Language.setSystem.Structure A]


-- @@ L357-361 verbatim
/-- A set system admits a cover at most as large as its marked set.
(Finiteness of the universe is part of the property: cardinality thresholds
are only meaningful on finite structures.) -/
def HasSmallSetCover : Prop :=
  Finite A ∧ CoversOn (SSElem (A := A)) SSFam SSMem SSMarked


-- @@ L363-365 verbatim
/-- A set system admits a hitting set at most as large as its marked set. -/
def HasSmallHittingSet : Prop :=
  Finite A ∧ HitsOn (SSElem (A := A)) SSFam SSMem SSMarked


-- @@ L367-369 verbatim
/-- A set system admits a packing at least as large as its marked set. -/
def HasLargeSetPacking : Prop :=
  Finite A ∧ PacksOn (SSElem (A := A)) SSFam SSMem SSMarked


-- @@ L371-375 verbatim
/-- A set system admits an exact cover: a subfamily covering every ground
element exactly once. There is no threshold here, so no finiteness
assumption either. -/
def HasExactCover : Prop :=
  ExactlyCoversOn (SSElem (A := A)) SSFam SSMem


-- @@ L377-380 verbatim
/-- A set system admits a splitting two-coloring: no set of the family is
monochromatic. -/
def HasSetSplitting : Prop :=
  SplitsOn (SSElem (A := A)) SSFam SSMem


-- @@ L382-382 verbatim
end Problems


-- @@ L384-384 verbatim
/-! ### Isomorphism-invariance and the bundled problems -/


-- @@ L386-386 verbatim
section Iso


-- @@ L388-388 verbatim
variable {A B : Type} [Language.setSystem.Structure A] [Language.setSystem.Structure B]


-- @@ L390-392 verbatim
private theorem ssElem_map (e : A ≃[Language.setSystem] B) (a : A) :
    SSElem a ↔ SSElem (e a) :=
  relMap_equiv₁ e ssElem a


-- @@ L394-396 verbatim
private theorem ssFam_map (e : A ≃[Language.setSystem] B) (a : A) :
    SSFam a ↔ SSFam (e a) :=
  relMap_equiv₁ e ssFam a


-- @@ L398-400 verbatim
private theorem ssMem_map (e : A ≃[Language.setSystem] B) (a b : A) :
    SSMem a b ↔ SSMem (e a) (e b) :=
  relMap_equiv₂ e ssMem a b


-- @@ L402-404 verbatim
private theorem ssMarked_map (e : A ≃[Language.setSystem] B) (a : A) :
    SSMarked a ↔ SSMarked (e a) :=
  relMap_equiv₁ e ssMarked a


-- @@ L406-411 verbatim
/-- The set-cover threshold property is isomorphism-invariant. -/
theorem hasSmallSetCover_iso (e : A ≃[Language.setSystem] B) :
    HasSmallSetCover A ↔ HasSmallSetCover B :=
  and_congr e.toEquiv.finite_iff
    (CoversOn.equiv_iff e.toEquiv (ssElem_map e) (ssFam_map e) (ssMem_map e)
      (ssMarked_map e))


-- @@ L413-418 verbatim
/-- The hitting-set threshold property is isomorphism-invariant. -/
theorem hasSmallHittingSet_iso (e : A ≃[Language.setSystem] B) :
    HasSmallHittingSet A ↔ HasSmallHittingSet B :=
  and_congr e.toEquiv.finite_iff
    (HitsOn.equiv_iff e.toEquiv (ssElem_map e) (ssFam_map e) (ssMem_map e)
      (ssMarked_map e))


-- @@ L420-425 verbatim
/-- The set-packing threshold property is isomorphism-invariant. -/
theorem hasLargeSetPacking_iso (e : A ≃[Language.setSystem] B) :
    HasLargeSetPacking A ↔ HasLargeSetPacking B :=
  and_congr e.toEquiv.finite_iff
    (PacksOn.equiv_iff e.toEquiv (ssElem_map e) (ssFam_map e) (ssMem_map e)
      (ssMarked_map e))


-- @@ L427-430 verbatim
/-- The exact-cover property is isomorphism-invariant. -/
theorem hasExactCover_iso (e : A ≃[Language.setSystem] B) :
    HasExactCover A ↔ HasExactCover B :=
  ExactlyCoversOn.equiv_iff e.toEquiv (ssElem_map e) (ssFam_map e) (ssMem_map e)


-- @@ L432-435 verbatim
/-- The set-splitting property is isomorphism-invariant. -/
theorem hasSetSplitting_iso (e : A ≃[Language.setSystem] B) :
    HasSetSplitting A ↔ HasSetSplitting B :=
  SplitsOn.equiv_iff e.toEquiv (ssElem_map e) (ssFam_map e) (ssMem_map e)


-- @@ L437-437 verbatim
end Iso


-- @@ L439-443 verbatim
/-- SET COVER, as a problem on set systems: is there a subfamily covering
every ground element, at most as large as the marked set? -/
def SetCover : DecisionProblem Language.setSystem where
  Holds := fun A inst => @HasSmallSetCover A inst
  iso_invariant := fun e => hasSmallSetCover_iso e


-- @@ L445-450 verbatim
/-- HITTING SET, as a problem on set systems: is there a set of ground
elements meeting every set of the family, at most as large as the marked
set? -/
def HittingSet : DecisionProblem Language.setSystem where
  Holds := fun A inst => @HasSmallHittingSet A inst
  iso_invariant := fun e => hasSmallHittingSet_iso e


-- @@ L452-456 verbatim
/-- SET PACKING, as a problem on set systems: is there a pairwise disjoint
subfamily at least as large as the marked set? -/
def SetPacking : DecisionProblem Language.setSystem where
  Holds := fun A inst => @HasLargeSetPacking A inst
  iso_invariant := fun e => hasLargeSetPacking_iso e


-- @@ L458-463 verbatim
/-- EXACT COVER, as a problem on set systems: is there a subfamily covering
every ground element exactly once? The marked set plays no role – exactness
replaces the threshold. -/
def ExactCover : DecisionProblem Language.setSystem where
  Holds := fun A inst => @HasExactCover A inst
  iso_invariant := fun e => hasExactCover_iso e


-- @@ L465-470 verbatim
/-- SET SPLITTING, as a problem on set systems: is there a two-coloring of
the ground elements leaving no set of the family monochromatic? (Also known as
hypergraph 2-colorability.) -/
def SetSplitting : DecisionProblem Language.setSystem where
  Holds := fun A inst => @HasSetSplitting A inst
  iso_invariant := fun e => hasSetSplitting_iso e


-- @@ L472-472 verbatim
end DescriptiveComplexity
