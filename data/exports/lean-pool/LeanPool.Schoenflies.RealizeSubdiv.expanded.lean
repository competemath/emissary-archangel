/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import LeanPool.Schoenflies.CellulationInvariants
public import LeanPool.Schoenflies.Subarc


-- @@ L11-100 verbatim
/-!
# Realizing an edge subdivision

`Schoenflies/GeneratedStructure.lean` performs the *abstract* edge subdivision
(`CellStructure.subdivideEdge`) and states what it means for a realization of the subdivided
structure to refine a realization of the old one (`SubdivData.IsRefinement`);
`Schoenflies/CellulationInvariants.lean` propagates assertions (i), (iv) and (vii) across such a
refinement. Nothing built such a realization. This module does.

The construction is the blueprint's own sentence — "the corresponding point is inserted into the
corresponding edge using the edge parametrization" — made into data: pick a parameter
`t ∈ (0,1)`, put the new 0-cell at `R.drawing d.edge t`, and draw the two new 1-cells with the
two halves of the old parametrization, each rescaled to `[0,1]`.

## The orientation of the drawn edge

`IsDrawing.edge_param` is deliberately orientation-free: it says
`G.IsLink e (drawing e 0) (drawing e 1)`, so `drawing d.edge 0` may be *either* `pos d.left` or
`pos d.right`. But `d.newEdge₁` runs from `d.left` to `d.newVertex` by definition of
`subdivideEdge`, so which half of the parametrization draws it is not fixed in advance.

Assuming `drawing d.edge 0 = pos d.left` would be a false hypothesis for half of all inputs, and
the caller cannot repair it (swapping `d.left` with `d.right` in the `SubdivData` also swaps the
two new edge *names*, producing a different abstract structure). So the orientation is read off
instead: `SubdivData.leftParam` is the endpoint parameter, `0` or `1`, at which the drawn edge
sits at `d.left`. Every statement below is orientation-free; only the two lemmas
`SubdivData.drawing_leftParam` and `SubdivData.drawing_rightParam` look inside.

Because of that, the construction is phrased with `Schoenflies.subarc` — the general affine
reparametrization already on `main` — rather than with `firstHalf` / `secondHalf`, which are the
two halves in the standard orientation and are recorded here as the named special case.

## No side conditions

`SubdivData.realize` takes no geometric hypothesis beyond `t ∈ Ioo 0 1`. Everything else it
needs — that `d.edge` is drawn, injectively and continuously, between the positions of `d.left`
and `d.right`, and that an interior point of a drawn edge is not a vertex — is already carried by
`CellStructure.Realization`, and is extracted here rather than assumed.

## The transported skeleton homeomorphism is not here, but it exists

**Closed, in `Schoenflies/RealizeSubdivHomeo.lean`** (`SubdivData.realizeHomeo`), on top of
`Schoenflies/ArcMonotone.lean`, which supplies the missing fact named at the end of this
section. What follows is the record of why it could not be done here.

`SkeletonHomeo.realize` is absent from *this* module. Six of its eight fields are immediate —
`skeletonSet_realize` below says the realized 1-skeleton is *literally the same set* after a
subdivision, so the map, its inverse, both continuity clauses and both inverse clauses transport
verbatim, and
`pos_apply` at the new 0-cell is the statement `g.toFun (R₁.drawing d.edge t₁) =
R₂.drawing d.edge t₂` that a caller choosing corresponding parameters supplies anyway.

What is missing is `edgeArc_image` at the two new edges: that `g` carries the *half* arc from
`R₁.pos d.left` to the new source point onto the half arc from `R₂.pos d.left` to the new target
point. This is true but is not implied by the `SkeletonHomeo` data pointwise: it needs the fact
that a homeomorphism between two arcs matching their endpoints is monotone, hence carries
initial subarcs to initial subarcs. That fact was not on `main` when this module was written,
and assuming the two clauses would have been assuming the conclusion, so nothing was stated
here. `Schoenflies/ArcMonotone.lean`
now proves it — `ArcMatch`, `transferParam`, `image_image_uIcc` — and
`Schoenflies/RealizeSubdivHomeo.lean` builds the transported homeomorphism from it, orientation
of the two realizations handled rather than assumed.

## Blueprint

* `def:generated-structure`, operation 1 (edge subdivision) — the geometric half of the
  operation, whose abstract half is `CellStructure.subdivideEdge`.
* `lem:cellulation-invariants` (i) and (iv), the paragraph "Suppose first that an open edge `e`
  is subdivided at a new vertex `v`": `SubdivData.isRefinement_realize` produces exactly the
  hypotheses that `SubdivData.IsRefinement.isCellDecomposition_and_isFaceJordan` consumes.

Declarations:

* `Schoenflies.uIcc_union_uIcc`, `Schoenflies.uIcc_inter_uIcc` — a parameter interval cut at an
  interior point.
* `Schoenflies.subarc_image_union`, `Schoenflies.subarc_image_inter` — the two subarcs of a cut
  cover the arc and meet exactly at the cut point.
* `Schoenflies.firstHalf`, `Schoenflies.secondHalf` — the two halves of a drawn edge in the
  standard orientation, with their endpoint values, continuity, injectivity, images, meet and
  union.
* `Schoenflies.CellStructure.SubdivData.leftParam` / `rightParam` — the orientation of the drawn
  edge.
* `Schoenflies.CellStructure.SubdivData.realize` — the realization of the subdivided structure.
* `Schoenflies.CellStructure.SubdivData.isRefinement_realize` — it refines the given one.
* `Schoenflies.CellStructure.SubdivData.realize_isCellDecomposition_and_isFaceJordan` — the
  induction step of `lem:cellulation-invariants` over the first constructor, now constructed
  with all necessary data constructed here.
* `Schoenflies.CellStructure.SubdivData.skeletonSet_realize` — a subdivision does not move the
  realized 1-skeleton.
-/


-- @@ L102-102 verbatim
@[expose] public section


-- @@ L104-104 verbatim
open Set unitInterval

-- @@ L105-105 verbatim
open scoped Graph


-- @@ L107-107 verbatim
namespace Schoenflies


-- @@ L109-109 verbatim
open Graph


-- @@ L111-111 verbatim
/-! ### Cutting a parameter interval at an interior point -/


-- @@ L113-113 verbatim
variable {a b t : ℝ}


-- @@ L115-121 verbatim
/-- The two halves of a parameter interval cut at a point of it cover it. -/
theorem uIcc_union_uIcc (h : t ∈ uIcc a b) : uIcc a t ∪ uIcc t b = uIcc a b := by
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab] at h ⊢
    rw [uIcc_of_le h.1, uIcc_of_le h.2, Icc_union_Icc_eq_Icc h.1 h.2]
  · rw [uIcc_of_ge hab] at h ⊢
    rw [uIcc_of_ge h.2, uIcc_of_ge h.1, union_comm, Icc_union_Icc_eq_Icc h.1 h.2]


-- @@ L123-129 verbatim
/-- …and meet exactly at the cut point. -/
theorem uIcc_inter_uIcc (h : t ∈ uIcc a b) : uIcc a t ∩ uIcc t b = {t} := by
  rcases le_total a b with hab | hab
  · rw [uIcc_of_le hab] at h
    rw [uIcc_of_le h.1, uIcc_of_le h.2, Icc_inter_Icc_eq_singleton h.1 h.2]
  · rw [uIcc_of_ge hab] at h
    rw [uIcc_of_ge h.2, uIcc_of_ge h.1, inter_comm, Icc_inter_Icc_eq_singleton h.1 h.2]


-- @@ L131-135 verbatim
/-- The far endpoint is not in the near half. -/
theorem right_notMem_uIcc_left (h : t ∈ uIcc a b) (hb : b ≠ t) : b ∉ uIcc a t := fun hmem =>
  hb (by
    have : b ∈ uIcc a t ∩ uIcc t b := ⟨hmem, right_mem_uIcc⟩
    rwa [uIcc_inter_uIcc h, mem_singleton_iff] at this)


-- @@ L137-141 verbatim
/-- …and symmetrically. -/
theorem left_notMem_uIcc_right (h : t ∈ uIcc a b) (ha : a ≠ t) : a ∉ uIcc t b := fun hmem =>
  ha (by
    have : a ∈ uIcc a t ∩ uIcc t b := ⟨left_mem_uIcc, hmem⟩
    rwa [uIcc_inter_uIcc h, mem_singleton_iff] at this)


-- @@ L143-144 verbatim
theorem uIcc_left_subset (h : t ∈ uIcc a b) : uIcc a t ⊆ uIcc a b :=
  uIcc_subset_uIcc left_mem_uIcc h


-- @@ L146-147 verbatim
theorem uIcc_right_subset (h : t ∈ uIcc a b) : uIcc t b ⊆ uIcc a b :=
  uIcc_subset_uIcc h right_mem_uIcc


-- @@ L149-149 verbatim
/-! ### The two subarcs of a cut -/


-- @@ L151-151 verbatim
variable {f : ℝ → Plane}


-- @@ L153-156 verbatim
/-- **The two subarcs of a cut cover the arc.** -/
theorem subarc_image_union (h : t ∈ uIcc a b) :
    subarc f a t '' I ∪ subarc f t b '' I = f '' uIcc a b := by
  rw [subarc_image, subarc_image, ← image_union, uIcc_union_uIcc h]


-- @@ L158-162 verbatim
/-- **The two subarcs of a cut meet exactly at the cut point.** -/
theorem subarc_image_inter (hi : InjOn f (uIcc a b)) (h : t ∈ uIcc a b) :
    subarc f a t '' I ∩ subarc f t b '' I = {f t} := by
  rw [subarc_image, subarc_image, ← hi.image_inter (uIcc_left_subset h) (uIcc_right_subset h),
    uIcc_inter_uIcc h, image_singleton]


-- @@ L164-166 verbatim
/-- The closure of an open arc is the closed arc. -/
theorem IsArcBetween.closure_diff_eq {A : Set Plane} {p q : Plane} (h : IsArcBetween A p q) :
    closure (A \ {p, q}) = A := h.closure_diff


-- @@ L168-181 verbatim
/-- The three pieces an open arc is cut into put the arc back together. -/
theorem diff_pair_union_union {A : Set Plane} {p q : Plane} (hp : p ∈ A) (hq : q ∈ A) :
    A \ {p, q} ∪ {q} ∪ {p} = A := by
  ext z
  simp only [mem_union, mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or]
  constructor
  · rintro ((⟨h, -, -⟩ | rfl) | rfl)
    exacts [h, hq, hp]
  · intro h
    by_cases h₁ : z = p
    · exact Or.inr h₁
    · by_cases h₂ : z = q
      · exact Or.inl (Or.inr h₂)
      · exact Or.inl (Or.inl ⟨h, h₁, h₂⟩)


-- @@ L183-186 verbatim
/-! ### The two halves of a drawn edge

The special case `a = 0`, `b = 1` of the previous section, in the notation a consumer holding a
`Graph.IsDrawing` writes. -/


-- @@ L188-188 verbatim
variable {β : Type*} {drawing : β → ℝ → Plane} {e : β}


-- @@ L190-190 verbatim
theorem uIcc_zero_one : uIcc (0 : ℝ) 1 = I := uIcc_of_le zero_le_one


-- @@ L192-193 verbatim
/-- The first half of a drawn edge, rescaled to `[0, 1]`. -/
def firstHalf (drawing : β → ℝ → Plane) (e : β) (t : ℝ) : ℝ → Plane := subarc (drawing e) 0 t


-- @@ L195-196 verbatim
/-- The second half of a drawn edge, rescaled to `[0, 1]`. -/
def secondHalf (drawing : β → ℝ → Plane) (e : β) (t : ℝ) : ℝ → Plane := subarc (drawing e) t 1


-- @@ L198-201 verbatim
theorem firstHalf_apply (s : ℝ) : firstHalf drawing e t s = drawing e (t * s) := by
  simp only [firstHalf, subarc, reparam]
  congr 1
  ring


-- @@ L203-206 verbatim
theorem secondHalf_apply (s : ℝ) : secondHalf drawing e t s = drawing e (t + (1 - t) * s) := by
  simp only [secondHalf, subarc, reparam]
  congr 1
  ring


-- @@ L208-208 verbatim
@[simp] theorem firstHalf_zero : firstHalf drawing e t 0 = drawing e 0 := subarc_zero


-- @@ L210-210 verbatim
@[simp] theorem firstHalf_one : firstHalf drawing e t 1 = drawing e t := subarc_one


-- @@ L212-212 verbatim
@[simp] theorem secondHalf_zero : secondHalf drawing e t 0 = drawing e t := subarc_zero


-- @@ L214-214 verbatim
@[simp] theorem secondHalf_one : secondHalf drawing e t 1 = drawing e 1 := subarc_one


-- @@ L216-217 verbatim
theorem continuousOn_firstHalf (hc : ContinuousOn (drawing e) I) (ht : t ∈ I) :
    ContinuousOn (firstHalf drawing e t) I := continuousOn_subarc hc zero_mem_I ht


-- @@ L219-220 verbatim
theorem continuousOn_secondHalf (hc : ContinuousOn (drawing e) I) (ht : t ∈ I) :
    ContinuousOn (secondHalf drawing e t) I := continuousOn_subarc hc ht one_mem_I


-- @@ L222-224 verbatim
theorem injOn_firstHalf (hi : InjOn (drawing e) I) (ht : t ∈ I) (h0 : t ≠ 0) :
    InjOn (firstHalf drawing e t) I :=
  injOn_subarc (hi.mono (uIcc_subset_I zero_mem_I ht)) (Ne.symm h0)


-- @@ L226-228 verbatim
theorem injOn_secondHalf (hi : InjOn (drawing e) I) (ht : t ∈ I) (h1 : t ≠ 1) :
    InjOn (secondHalf drawing e t) I :=
  injOn_subarc (hi.mono (uIcc_subset_I ht one_mem_I)) h1


-- @@ L230-232 verbatim
theorem image_firstHalf (ht : t ∈ I) :
    firstHalf drawing e t '' I = drawing e '' Icc 0 t := by
  rw [firstHalf, subarc_image, uIcc_of_le ht.1]


-- @@ L234-236 verbatim
theorem image_secondHalf (ht : t ∈ I) :
    secondHalf drawing e t '' I = drawing e '' Icc t 1 := by
  rw [secondHalf, subarc_image, uIcc_of_le ht.2]


-- @@ L238-241 verbatim
/-- **The two halves cover the drawn edge.** -/
theorem firstHalf_union_secondHalf (ht : t ∈ I) :
    firstHalf drawing e t '' I ∪ secondHalf drawing e t '' I = edgeArc drawing e := by
  rw [firstHalf, secondHalf, subarc_image_union (by rwa [uIcc_zero_one]), uIcc_zero_one, edgeArc]


-- @@ L243-247 verbatim
/-- **The two halves meet exactly at the cut point.** -/
theorem firstHalf_inter_secondHalf (hi : InjOn (drawing e) I) (ht : t ∈ I) :
    firstHalf drawing e t '' I ∩ secondHalf drawing e t '' I = {drawing e t} := by
  rw [firstHalf, secondHalf,
    subarc_image_inter (by rwa [uIcc_zero_one]) (by rwa [uIcc_zero_one])]


-- @@ L249-254 verbatim
/-- Each half is an arc between the corresponding endpoint and the cut point. -/
theorem isArcBetween_firstHalf (hc : ContinuousOn (drawing e) I) (hi : InjOn (drawing e) I)
    (ht : t ∈ I) (h0 : t ≠ 0) :
    IsArcBetween (firstHalf drawing e t '' I) (drawing e 0) (drawing e t) :=
  ⟨firstHalf drawing e t, continuousOn_firstHalf hc ht, injOn_firstHalf hi ht h0, rfl,
    firstHalf_zero, firstHalf_one⟩


-- @@ L256-260 verbatim
theorem isArcBetween_secondHalf (hc : ContinuousOn (drawing e) I) (hi : InjOn (drawing e) I)
    (ht : t ∈ I) (h1 : t ≠ 1) :
    IsArcBetween (secondHalf drawing e t '' I) (drawing e t) (drawing e 1) :=
  ⟨secondHalf drawing e t, continuousOn_secondHalf hc ht, injOn_secondHalf hi ht h1, rfl,
    secondHalf_zero, secondHalf_one⟩


-- @@ L262-262 verbatim
/-! ### The orientation of the drawn subdivided edge -/


-- @@ L264-264 verbatim
namespace CellStructure


-- @@ L266-266 verbatim
namespace SubdivData


-- @@ L268-268 verbatim
variable {γ : Type*} {S : CellStructure γ} (d : S.SubdivData) (R : S.Realization)


-- @@ L270-273 verbatim
/-- What the realization already knows about the subdivided edge: it is an edge of the drawn
skeleton. -/
theorem edge_mem_edgeSet_graph : d.edge ∈ E(R.graph) := by
  rw [Realization.edgeSet_graph]; exact d.edge_mem_edgeSet


-- @@ L275-276 verbatim
theorem continuousOn_drawing_edge : ContinuousOn (R.drawing d.edge) I :=
  (R.isDrawing.edge_param (d.edge_mem_edgeSet_graph R)).1


-- @@ L278-279 verbatim
theorem injOn_drawing_edge : InjOn (R.drawing d.edge) I :=
  (R.isDrawing.edge_param (d.edge_mem_edgeSet_graph R)).2.1


-- @@ L281-282 verbatim
theorem isLink_drawn_edge : R.graph.IsLink d.edge (R.pos d.left) (R.pos d.right) :=
  d.isLink.map R.pos


-- @@ L284-290 verbatim
open scoped Classical in
/-- **The orientation of the drawn subdivided edge**: the endpoint parameter, `0` or `1`, at
which `R.drawing d.edge` sits at `R.pos d.left`.

`IsDrawing.edge_param` fixes only the unordered pair of endpoint values, so this cannot be read
off the structure; it is decided by a case distinction, once, here. -/
noncomputable def leftParam : ℝ := if R.drawing d.edge 0 = R.pos d.left then 0 else 1


-- @@ L292-293 verbatim
/-- The endpoint parameter at which the drawn subdivided edge sits at `R.pos d.right`. -/
noncomputable def rightParam : ℝ := 1 - d.leftParam R


-- @@ L295-298 verbatim
theorem leftParam_eq_zero_or_one : d.leftParam R = 0 ∨ d.leftParam R = 1 := by
  unfold leftParam
  split_ifs
  exacts [Or.inl rfl, Or.inr rfl]


-- @@ L300-318 verbatim
/-- **The two endpoint parameters land on the two endpoints.** The only lemma that looks inside
`leftParam`; everything downstream is orientation-free. -/
theorem drawing_params :
    R.drawing d.edge (d.leftParam R) = R.pos d.left ∧
      R.drawing d.edge (d.rightParam R) = R.pos d.right := by
  have hd := R.isDrawing.edge_param (d.edge_mem_edgeSet_graph R)
  rcases (d.isLink_drawn_edge R).eq_and_eq_or_eq_and_eq hd.2.2 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · have hL : d.leftParam R = 0 := ite_eq_left h0.symm
    refine ⟨by rw [hL]; exact h0.symm, ?_⟩
    have hR : d.rightParam R = 1 := by rw [rightParam, hL]; ring
    rw [hR]; exact h1.symm
  · -- Here `R.pos d.left = R.drawing d.edge 1`; the other reading would collapse the two
    -- endpoint values, which injectivity forbids.
    have hne : ¬ (R.drawing d.edge 0 = R.pos d.left) := fun hcon =>
      zero_ne_one (hd.2.1 zero_mem_I one_mem_I (by rw [hcon, h0]))
    have hL : d.leftParam R = 1 := ite_eq_right hne
    refine ⟨by rw [hL]; exact h0.symm, ?_⟩
    have hR : d.rightParam R = 0 := by rw [rightParam, hL]; ring
    rw [hR]; exact h1.symm


-- @@ L320-321 verbatim
theorem drawing_leftParam : R.drawing d.edge (d.leftParam R) = R.pos d.left :=
  (d.drawing_params R).1


-- @@ L323-324 verbatim
theorem drawing_rightParam : R.drawing d.edge (d.rightParam R) = R.pos d.right :=
  (d.drawing_params R).2


-- @@ L326-328 verbatim
theorem leftParam_mem_I : d.leftParam R ∈ I := by
  rcases d.leftParam_eq_zero_or_one R with h | h <;> rw [h]
  exacts [zero_mem_I, one_mem_I]


-- @@ L330-333 verbatim
theorem rightParam_mem_I : d.rightParam R ∈ I := by
  rcases d.leftParam_eq_zero_or_one R with h | h
  · rw [rightParam, h, sub_zero]; exact one_mem_I
  · rw [rightParam, h, sub_self]; exact zero_mem_I


-- @@ L335-339 verbatim
/-- The two endpoint parameters span the whole parameter interval, in whichever order. -/
theorem uIcc_params : uIcc (d.leftParam R) (d.rightParam R) = I := by
  rcases d.leftParam_eq_zero_or_one R with h | h
  · rw [rightParam, h, sub_zero]; exact uIcc_zero_one
  · rw [rightParam, h, sub_self, uIcc_comm]; exact uIcc_zero_one


-- @@ L341-343 verbatim
theorem leftParam_ne (ht : t ∈ Ioo (0 : ℝ) 1) : d.leftParam R ≠ t := by
  rcases d.leftParam_eq_zero_or_one R with h | h <;> rw [h]
  exacts [ht.1.ne, ht.2.ne']


-- @@ L345-348 verbatim
theorem rightParam_ne (ht : t ∈ Ioo (0 : ℝ) 1) : d.rightParam R ≠ t := by
  rcases d.leftParam_eq_zero_or_one R with h | h
  · rw [rightParam, h, sub_zero]; exact ht.2.ne'
  · rw [rightParam, h, sub_self]; exact ht.1.ne


-- @@ L350-351 verbatim
theorem mem_uIcc_params (ht : t ∈ Ioo (0 : ℝ) 1) : t ∈ uIcc (d.leftParam R) (d.rightParam R) := by
  rw [d.uIcc_params R]; exact Ioo_subset_Icc_self ht


-- @@ L353-367 verbatim
/-- **An interior point of a drawn edge is not a vertex.** The one geometric fact the
construction needs that is not simply read off a field, and the reason `SubdivData.realize`
needs no side condition. -/
theorem newPos_notMem_vertexSet (ht : t ∈ Ioo (0 : ℝ) 1) :
    R.drawing d.edge t ∉ V(R.graph) := by
  intro hmem
  have harc : R.drawing d.edge t ∈ edgeArc R.drawing d.edge :=
    ⟨t, Ioo_subset_Icc_self ht, rfl⟩
  have hinj := d.injOn_drawing_edge R
  rcases R.isDrawing.vertex_mem_edgeArc (d.isLink_drawn_edge R) hmem harc with h | h
  · exact d.leftParam_ne R ht
      (hinj (d.leftParam_mem_I R) (Ioo_subset_Icc_self ht) ((d.drawing_leftParam R).trans h.symm))
  · exact d.rightParam_ne R ht
      (hinj (d.rightParam_mem_I R) (Ioo_subset_Icc_self ht)
        ((d.drawing_rightParam R).trans h.symm))


-- @@ L369-371 verbatim
theorem newPos_ne_pos (ht : t ∈ Ioo (0 : ℝ) 1) {v : γ} (hv : v ∈ V(S.skel)) :
    R.drawing d.edge t ≠ R.pos v := fun h =>
  d.newPos_notMem_vertexSet R ht (by rw [h, Realization.vertexSet_graph]; exact ⟨v, hv, rfl⟩)


-- @@ L373-373 verbatim
/-! ### Freshness of the three new names, in the forms used below -/


-- @@ L375-376 verbatim
theorem newVertex_notMem_vertexSet : d.newVertex ∉ V(S.skel) := fun h =>
  d.newVertex_notMem (S.mem_cells_of_mem_vertexSet h)


-- @@ L378-379 verbatim
theorem ne_newVertex_of_mem_cells {z : γ} (hz : z ∈ S.cells) : z ≠ d.newVertex := fun h =>
  d.newVertex_notMem (h ▸ hz)


-- @@ L381-382 verbatim
theorem ne_newEdge₁_of_mem_cells {z : γ} (hz : z ∈ S.cells) : z ≠ d.newEdge₁ := fun h =>
  d.newEdge₁_notMem (h ▸ hz)


-- @@ L384-385 verbatim
theorem ne_newEdge₂_of_mem_cells {z : γ} (hz : z ∈ S.cells) : z ≠ d.newEdge₂ := fun h =>
  d.newEdge₂_notMem (h ▸ hz)


-- @@ L387-388 verbatim
theorem newEdge₁_ne_edge : d.newEdge₁ ≠ d.edge := fun h =>
  d.newEdge₁_notMem (h ▸ d.edge_mem_cells)


-- @@ L390-391 verbatim
theorem newEdge₂_ne_edge : d.newEdge₂ ≠ d.edge := fun h =>
  d.newEdge₂_notMem (h ▸ d.edge_mem_cells)


-- @@ L393-393 verbatim
/-! ### The links of the subdivided skeleton -/


-- @@ L395-396 verbatim
theorem isLink_newEdge₁ : d.skeleton.IsLink d.newEdge₁ d.left d.newVertex :=
  d.skeleton_isLink.2 (Or.inr (Or.inl ⟨rfl, rfl⟩))


-- @@ L398-399 verbatim
theorem isLink_newEdge₂ : d.skeleton.IsLink d.newEdge₂ d.newVertex d.right :=
  d.skeleton_isLink.2 (Or.inr (Or.inr ⟨rfl, rfl⟩))


-- @@ L401-406 verbatim
/-- An old edge other than the subdivided one keeps its ends. -/
theorem skeleton_isLink_of_old {f x y : γ} (hfe : f ≠ d.edge) (h : S.skel.IsLink f x y) :
    d.skeleton.IsLink f x y :=
  d.skeleton_isLink.2 (Or.inl ⟨h, hfe,
    fun hc => d.newEdge₁_notMem_edgeSet (hc ▸ h.edge_mem),
    fun hc => d.newEdge₂_notMem_edgeSet (hc ▸ h.edge_mem)⟩)


-- @@ L408-415 verbatim
/-- …and gains none: for an old edge the two skeleta have the same links. -/
theorem skeleton_isLink_old_iff {f x y : γ} (hf : f ∈ E(S.skel)) (hfe : f ≠ d.edge) :
    d.skeleton.IsLink f x y ↔ S.skel.IsLink f x y := by
  refine ⟨fun h => ?_, d.skeleton_isLink_of_old hfe⟩
  rcases d.skeleton_isLink.1 h with ⟨h, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact h
  · exact absurd hf d.newEdge₁_notMem_edgeSet
  · exact absurd hf d.newEdge₂_notMem_edgeSet


-- @@ L417-417 verbatim
/-! ### The realization of the subdivided structure -/


-- @@ L419-423 verbatim
open scoped Classical in
/-- The positions after the subdivision: the new 0-cell goes to the point of the drawn edge at
parameter `t`, and every old 0-cell stays where it was. -/
noncomputable def realizePos (d : S.SubdivData) (R : S.Realization) (t : ℝ) : γ → Plane :=
  fun z => if z = d.newVertex then R.drawing d.edge t else R.pos z


-- @@ L425-435 verbatim
open scoped Classical in
/-- The parametrizations after the subdivision: the two new 1-cells are drawn by the two halves
of the old parametrization, cut at `t` and rescaled to `[0, 1]`; every old 1-cell keeps its own.

`d.newEdge₁` runs from `d.left`, so the half that draws it starts at `d.leftParam R`, which is
`0` or `1` according to the orientation of the old parametrization. -/
noncomputable def realizeDrawing (d : S.SubdivData) (R : S.Realization) (t : ℝ) : γ → ℝ → Plane :=
  fun f =>
    if f = d.newEdge₁ then subarc (R.drawing d.edge) (d.leftParam R) t
    else if f = d.newEdge₂ then subarc (R.drawing d.edge) t (d.rightParam R)
    else R.drawing f


-- @@ L437-447 verbatim
open scoped Classical in
/-- The open cells after the subdivision: the new 0-cell is the new point, each new open 1-cell
is its half arc without its two endpoints, and every surviving cell is unchanged. -/
noncomputable def realizeCell (d : S.SubdivData) (R : S.Realization) (t : ℝ) : γ → Set Plane :=
  fun c =>
    if c = d.newVertex then {R.drawing d.edge t}
    else if c = d.newEdge₁ then
      R.drawing d.edge '' uIcc (d.leftParam R) t \ {R.pos d.left, R.drawing d.edge t}
    else if c = d.newEdge₂ then
      R.drawing d.edge '' uIcc t (d.rightParam R) \ {R.drawing d.edge t, R.pos d.right}
    else R.cell c


-- @@ L449-451 verbatim
/-- The drawn skeleton after the subdivision. -/
noncomputable def realizeGraph (d : S.SubdivData) (R : S.Realization) (t : ℝ) : Graph Plane γ :=
  d.skeleton.map (d.realizePos R t)


-- @@ L453-453 verbatim
variable {d R}


-- @@ L455-456 verbatim
@[simp] theorem realizePos_newVertex : d.realizePos R t d.newVertex = R.drawing d.edge t :=
  ite_eq_left rfl


-- @@ L458-459 verbatim
theorem realizePos_of_ne {z : γ} (h : z ≠ d.newVertex) : d.realizePos R t z = R.pos z :=
  ite_eq_right h


-- @@ L461-462 verbatim
theorem realizePos_of_mem_cells {z : γ} (h : z ∈ S.cells) : d.realizePos R t z = R.pos z :=
  realizePos_of_ne (d.ne_newVertex_of_mem_cells h)


-- @@ L464-465 verbatim
theorem realizePos_of_mem_vertexSet {z : γ} (h : z ∈ V(S.skel)) : d.realizePos R t z = R.pos z :=
  realizePos_of_mem_cells (S.mem_cells_of_mem_vertexSet h)


-- @@ L467-468 verbatim
@[simp] theorem realizeDrawing_newEdge₁ :
    d.realizeDrawing R t d.newEdge₁ = subarc (R.drawing d.edge) (d.leftParam R) t := ite_eq_left rfl


-- @@ L470-474 verbatim
@[simp] theorem realizeDrawing_newEdge₂ :
    d.realizeDrawing R t d.newEdge₂ = subarc (R.drawing d.edge) t (d.rightParam R) := by
  rw [realizeDrawing,
      ite_eq_right d.newEdge_ne.symm,
          ite_eq_left rfl]


-- @@ L476-479 verbatim
theorem realizeDrawing_of_ne {f : γ} (h₁ : f ≠ d.newEdge₁) (h₂ : f ≠ d.newEdge₂) :
    d.realizeDrawing R t f = R.drawing f := by rw [realizeDrawing,
      ite_eq_right h₁,
      ite_eq_right h₂]


-- @@ L481-483 verbatim
theorem realizeDrawing_of_mem_cells {f : γ} (h : f ∈ S.cells) :
    d.realizeDrawing R t f = R.drawing f :=
  realizeDrawing_of_ne (d.ne_newEdge₁_of_mem_cells h) (d.ne_newEdge₂_of_mem_cells h)


-- @@ L485-486 verbatim
@[simp] theorem realizeCell_newVertex : d.realizeCell R t d.newVertex = {R.drawing d.edge t} :=
  ite_eq_left rfl


-- @@ L488-492 verbatim
@[simp] theorem realizeCell_newEdge₁ : d.realizeCell R t d.newEdge₁ =
    R.drawing d.edge '' uIcc (d.leftParam R) t \ {R.pos d.left, R.drawing d.edge t} := by
  rw [realizeCell,
      ite_eq_right d.newVertex_ne₁.symm,
          ite_eq_left rfl]


-- @@ L494-499 verbatim
@[simp] theorem realizeCell_newEdge₂ : d.realizeCell R t d.newEdge₂ =
    R.drawing d.edge '' uIcc t (d.rightParam R) \ {R.drawing d.edge t, R.pos d.right} := by
  rw [realizeCell,
      ite_eq_right d.newVertex_ne₂.symm,
      ite_eq_right d.newEdge_ne.symm,
          ite_eq_left rfl]


-- @@ L501-505 verbatim
theorem realizeCell_of_mem_cells {c : γ} (h : c ∈ S.cells) : d.realizeCell R t c = R.cell c := by
  rw [realizeCell,
      ite_eq_right (d.ne_newVertex_of_mem_cells h),
      ite_eq_right (d.ne_newEdge₁_of_mem_cells h),
    ite_eq_right (d.ne_newEdge₂_of_mem_cells h)]


-- @@ L507-507 verbatim
/-! ### The two half arcs -/


-- @@ L509-511 verbatim
theorem edgeArc_newEdge₁ : edgeArc (d.realizeDrawing R t) d.newEdge₁ =
    R.drawing d.edge '' uIcc (d.leftParam R) t := by
  rw [edgeArc, realizeDrawing_newEdge₁, subarc_image]


-- @@ L513-515 verbatim
theorem edgeArc_newEdge₂ : edgeArc (d.realizeDrawing R t) d.newEdge₂ =
    R.drawing d.edge '' uIcc t (d.rightParam R) := by
  rw [edgeArc, realizeDrawing_newEdge₂, subarc_image]


-- @@ L517-519 verbatim
theorem edgeArc_of_ne {f : γ} (h₁ : f ≠ d.newEdge₁) (h₂ : f ≠ d.newEdge₂) :
    edgeArc (d.realizeDrawing R t) f = edgeArc R.drawing f := by
  rw [edgeArc, edgeArc, realizeDrawing_of_ne h₁ h₂]


-- @@ L521-521 verbatim
/-! ### The two cell-shape fields of a realization -/


-- @@ L523-530 verbatim
/-- Every 0-cell of the subdivided structure is realized by its point. -/
theorem cell_vertex_realize ⦃v : γ⦄ (hv : v ∈ V(d.skeleton)) :
    d.realizeCell R t v = {d.realizePos R t v} := by
  rw [d.skeleton_vertexSet, mem_insert_iff] at hv
  rcases hv with rfl | hv
  · rw [realizeCell_newVertex, realizePos_newVertex]
  · rw [realizeCell_of_mem_cells (S.mem_cells_of_mem_vertexSet hv),
      realizePos_of_mem_vertexSet hv, R.cell_vertex hv]


-- @@ L532-547 verbatim
/-- Every 1-cell of the subdivided structure is realized by its open arc. -/
theorem cell_edge_realize ⦃g x y : γ⦄ (hl : d.skeleton.IsLink g x y) :
    d.realizeCell R t g =
      edgeArc (d.realizeDrawing R t) g \ {d.realizePos R t x, d.realizePos R t y} := by
  rcases d.skeleton_isLink.1 hl with ⟨hlS, -, hg₁, hg₂⟩ | ⟨rfl, hs⟩ | ⟨rfl, hs⟩
  · rw [realizeCell_of_mem_cells (S.mem_cells_of_mem_edgeSet hlS.edge_mem),
      edgeArc_of_ne hg₁ hg₂, realizePos_of_mem_vertexSet hlS.left_mem,
      realizePos_of_mem_vertexSet hlS.right_mem, R.cell_edge hlS]
  · rw [realizeCell_newEdge₁, edgeArc_newEdge₁]
    rcases Sym2.eq_iff.1 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [realizePos_of_mem_vertexSet d.isLink.left_mem, realizePos_newVertex]
    · rw [realizePos_of_mem_vertexSet d.isLink.left_mem, realizePos_newVertex, pair_comm]
  · rw [realizeCell_newEdge₂, edgeArc_newEdge₂]
    rcases Sym2.eq_iff.1 hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [realizePos_of_mem_vertexSet d.isLink.right_mem, realizePos_newVertex]
    · rw [realizePos_of_mem_vertexSet d.isLink.right_mem, realizePos_newVertex, pair_comm]


-- @@ L549-549 verbatim
section


-- @@ L551-551 verbatim
variable (ht : t ∈ Ioo (0 : ℝ) 1)

-- @@ L552-552 verbatim
include ht


-- @@ L554-568 verbatim
/-- Distinct 0-cells of the subdivided structure sit at distinct points: the new one is an
interior point of a drawn edge, so it is none of the old ones. -/
theorem injOn_realizePos : InjOn (d.realizePos R t) V(d.skeleton) := by
  intro p hp q hq hpq
  rw [d.skeleton_vertexSet, mem_insert_iff] at hp hq
  rcases hp with rfl | hp
  · rcases hq with rfl | hq
    · rfl
    · rw [realizePos_newVertex, realizePos_of_mem_vertexSet hq] at hpq
      exact absurd hpq (d.newPos_ne_pos R ht hq)
  · rcases hq with rfl | hq
    · rw [realizePos_of_mem_vertexSet hp, realizePos_newVertex] at hpq
      exact absurd hpq.symm (d.newPos_ne_pos R ht hp)
    · rw [realizePos_of_mem_vertexSet hp, realizePos_of_mem_vertexSet hq] at hpq
      exact R.injOn_pos hp hq hpq


-- @@ L570-573 verbatim
theorem edgeArc_newEdge₁_subset :
    edgeArc (d.realizeDrawing R t) d.newEdge₁ ⊆ edgeArc R.drawing d.edge := by
  rw [edgeArc_newEdge₁, edgeArc]
  exact image_mono ((uIcc_left_subset (d.mem_uIcc_params R ht)).trans (d.uIcc_params R).subset)


-- @@ L575-578 verbatim
theorem edgeArc_newEdge₂_subset :
    edgeArc (d.realizeDrawing R t) d.newEdge₂ ⊆ edgeArc R.drawing d.edge := by
  rw [edgeArc_newEdge₂, edgeArc]
  exact image_mono ((uIcc_right_subset (d.mem_uIcc_params R ht)).trans (d.uIcc_params R).subset)


-- @@ L580-584 verbatim
/-- **The two new arcs cover the old one.** -/
theorem edgeArc_new_union : edgeArc (d.realizeDrawing R t) d.newEdge₁ ∪
    edgeArc (d.realizeDrawing R t) d.newEdge₂ = edgeArc R.drawing d.edge := by
  rw [edgeArc_newEdge₁, edgeArc_newEdge₂, ← image_union,
    uIcc_union_uIcc (d.mem_uIcc_params R ht), d.uIcc_params R, edgeArc]


-- @@ L586-592 verbatim
/-- **The two new arcs meet exactly at the new point.** -/
theorem edgeArc_new_inter : edgeArc (d.realizeDrawing R t) d.newEdge₁ ∩
    edgeArc (d.realizeDrawing R t) d.newEdge₂ = {R.drawing d.edge t} := by
  rw [edgeArc_newEdge₁, edgeArc_newEdge₂,
    ← (d.injOn_drawing_edge R).mono (d.uIcc_params R).subset |>.image_inter
      (uIcc_left_subset (d.mem_uIcc_params R ht)) (uIcc_right_subset (d.mem_uIcc_params R ht)),
    uIcc_inter_uIcc (d.mem_uIcc_params R ht), image_singleton]


-- @@ L594-598 verbatim
omit ht in
theorem posLeft_mem_edgeArc_newEdge₁ :
    R.pos d.left ∈ edgeArc (d.realizeDrawing R t) d.newEdge₁ := by
  rw [edgeArc_newEdge₁, ← d.drawing_leftParam R]
  exact ⟨_, left_mem_uIcc, rfl⟩


-- @@ L600-604 verbatim
omit ht in
theorem posRight_mem_edgeArc_newEdge₂ :
    R.pos d.right ∈ edgeArc (d.realizeDrawing R t) d.newEdge₂ := by
  rw [edgeArc_newEdge₂, ← d.drawing_rightParam R]
  exact ⟨_, right_mem_uIcc, rfl⟩


-- @@ L606-609 verbatim
omit ht in
theorem newPos_mem_edgeArc_newEdge₁ :
    R.drawing d.edge t ∈ edgeArc (d.realizeDrawing R t) d.newEdge₁ := by
  rw [edgeArc_newEdge₁]; exact ⟨t, right_mem_uIcc, rfl⟩


-- @@ L611-614 verbatim
omit ht in
theorem newPos_mem_edgeArc_newEdge₂ :
    R.drawing d.edge t ∈ edgeArc (d.realizeDrawing R t) d.newEdge₂ := by
  rw [edgeArc_newEdge₂]; exact ⟨t, left_mem_uIcc, rfl⟩


-- @@ L616-624 verbatim
/-- The far endpoint of the old edge misses the near half. -/
theorem posRight_notMem_edgeArc_newEdge₁ :
    R.pos d.right ∉ edgeArc (d.realizeDrawing R t) d.newEdge₁ := by
  rw [edgeArc_newEdge₁, ← d.drawing_rightParam R]
  rintro ⟨s, hs, hseq⟩
  have hsI : s ∈ I :=
    ((uIcc_left_subset (d.mem_uIcc_params R ht)).trans (d.uIcc_params R).subset) hs
  have : s = d.rightParam R := d.injOn_drawing_edge R hsI (d.rightParam_mem_I R) hseq
  exact right_notMem_uIcc_left (d.mem_uIcc_params R ht) (d.rightParam_ne R ht) (this ▸ hs)


-- @@ L626-633 verbatim
theorem posLeft_notMem_edgeArc_newEdge₂ :
    R.pos d.left ∉ edgeArc (d.realizeDrawing R t) d.newEdge₂ := by
  rw [edgeArc_newEdge₂, ← d.drawing_leftParam R]
  rintro ⟨s, hs, hseq⟩
  have hsI : s ∈ I :=
    ((uIcc_right_subset (d.mem_uIcc_params R ht)).trans (d.uIcc_params R).subset) hs
  have : s = d.leftParam R := d.injOn_drawing_edge R hsI (d.leftParam_mem_I R) hseq
  exact left_notMem_uIcc_right (d.mem_uIcc_params R ht) (d.leftParam_ne R ht) (this ▸ hs)


-- @@ L635-641 verbatim
/-- The new point lies on no old edge but the subdivided one. -/
theorem newPos_notMem_edgeArc_of_ne {f : γ} (hf : f ∈ E(S.skel)) (hfe : f ≠ d.edge) :
    R.drawing d.edge t ∉ edgeArc R.drawing f := fun hva =>
  d.newPos_notMem_vertexSet R ht
    (R.isDrawing.arcs_meet_at_vertex (d.edge_mem_edgeSet_graph R)
      (by rw [edgeSet_map]; exact hf) (Ne.symm hfe)
      ⟨t, Ioo_subset_Icc_self ht, rfl⟩ hva)


-- @@ L643-643 verbatim
/-! ### The subdivided drawn skeleton -/


-- @@ L645-646 verbatim
omit ht in
theorem realizeGraph_edgeSet : E(d.realizeGraph R t) = E(d.skeleton) := edgeSet_map _ _


-- @@ L648-650 verbatim
omit ht in
theorem realizePos_image_vertexSet : d.realizePos R t '' V(S.skel) = R.pos '' V(S.skel) :=
  image_congr fun _ hv => realizePos_of_mem_vertexSet hv


-- @@ L652-656 verbatim
omit ht in
theorem realizeGraph_vertexSet :
    V(d.realizeGraph R t) = insert (R.drawing d.edge t) V(R.graph) := by
  rw [realizeGraph, vertexSet_map, d.skeleton_vertexSet, image_insert_eq, realizePos_newVertex,
    realizePos_image_vertexSet, Realization.vertexSet_graph]


-- @@ L658-661 verbatim
omit ht in
theorem mem_realizeGraph_vertexSet_of_mem {p : Plane} (hp : p ∈ V(R.graph)) :
    p ∈ V(d.realizeGraph R t) := by
  rw [realizeGraph_vertexSet]; exact mem_insert_of_mem _ hp


-- @@ L663-671 verbatim
omit ht in
/-- An edge of the subdivided drawn skeleton that is neither new is an old edge, and not the
subdivided one. -/
theorem mem_edgeSet_skel_of_ne {f : γ} (hf : f ∈ E(d.realizeGraph R t))
    (h₁ : f ≠ d.newEdge₁) (h₂ : f ≠ d.newEdge₂) : f ∈ E(S.skel) ∧ f ≠ d.edge := by
  rw [realizeGraph_edgeSet, d.skeleton_edgeSet] at hf
  simp only [mem_insert_iff, mem_sdiff, mem_singleton_iff] at hf
  rcases hf with rfl | rfl | h
  exacts [absurd rfl h₁, absurd rfl h₂, h]


-- @@ L673-684 verbatim
omit ht in
/-- For an old edge the two drawn skeleta have the same links. -/
theorem realizeGraph_isLink_old {f : γ} {x y : Plane} (hf : f ∈ E(S.skel)) (hfe : f ≠ d.edge) :
    (d.realizeGraph R t).IsLink f x y ↔ R.graph.IsLink f x y := by
  constructor
  · rintro ⟨p, q, hpq, rfl, rfl⟩
    rw [d.skeleton_isLink_old_iff hf hfe] at hpq
    rw [realizePos_of_mem_vertexSet hpq.left_mem, realizePos_of_mem_vertexSet hpq.right_mem]
    exact hpq.map R.pos
  · rintro ⟨p, q, hpq, rfl, rfl⟩
    exact ⟨p, q, d.skeleton_isLink_of_old hfe hpq,
      realizePos_of_mem_vertexSet hpq.left_mem, realizePos_of_mem_vertexSet hpq.right_mem⟩


-- @@ L686-689 verbatim
omit ht in
theorem realizeGraph_inc_old {f : γ} {p : Plane} (hf : f ∈ E(S.skel)) (hfe : f ≠ d.edge) :
    (d.realizeGraph R t).Inc f p ↔ R.graph.Inc f p :=
  exists_congr fun _ => realizeGraph_isLink_old hf hfe


-- @@ L691-695 verbatim
omit ht in
theorem realizeGraph_isLink_newEdge₁ :
    (d.realizeGraph R t).IsLink d.newEdge₁ (R.pos d.left) (R.drawing d.edge t) := by
  have h := d.isLink_newEdge₁.map (d.realizePos R t)
  rwa [realizePos_of_mem_vertexSet d.isLink.left_mem, realizePos_newVertex] at h


-- @@ L697-701 verbatim
omit ht in
theorem realizeGraph_isLink_newEdge₂ :
    (d.realizeGraph R t).IsLink d.newEdge₂ (R.drawing d.edge t) (R.pos d.right) := by
  have h := d.isLink_newEdge₂.map (d.realizePos R t)
  rwa [realizePos_of_mem_vertexSet d.isLink.right_mem, realizePos_newVertex] at h


-- @@ L703-713 verbatim
/-- A vertex on the first new arc is one of its two ends. -/
theorem mem_edgeArc_newEdge₁_vertex {p : Plane} (hp : p ∈ V(d.realizeGraph R t))
    (hpa : p ∈ edgeArc (d.realizeDrawing R t) d.newEdge₁) :
    p = R.pos d.left ∨ p = R.drawing d.edge t := by
  rw [realizeGraph_vertexSet, mem_insert_iff] at hp
  rcases hp with rfl | hp
  · exact Or.inr rfl
  · rcases R.isDrawing.vertex_mem_edgeArc (d.isLink_drawn_edge R) hp
      (edgeArc_newEdge₁_subset ht hpa) with h | h
    · exact Or.inl h
    · exact absurd (h ▸ hpa) (posRight_notMem_edgeArc_newEdge₁ ht)


-- @@ L715-725 verbatim
/-- A vertex on the second new arc is one of its two ends. -/
theorem mem_edgeArc_newEdge₂_vertex {p : Plane} (hp : p ∈ V(d.realizeGraph R t))
    (hpa : p ∈ edgeArc (d.realizeDrawing R t) d.newEdge₂) :
    p = R.drawing d.edge t ∨ p = R.pos d.right := by
  rw [realizeGraph_vertexSet, mem_insert_iff] at hp
  rcases hp with rfl | hp
  · exact Or.inl rfl
  · rcases R.isDrawing.vertex_mem_edgeArc (d.isLink_drawn_edge R) hp
      (edgeArc_newEdge₂_subset ht hpa) with h | h
    · exact absurd (h ▸ hpa) (posLeft_notMem_edgeArc_newEdge₂ ht)
    · exact Or.inr h


-- @@ L727-727 verbatim
/-! ### Where two edges of the subdivided drawing meet -/


-- @@ L729-740 verbatim
/-- The two new edges meet exactly at the new vertex. -/
theorem edge_inter_new_new {p : Plane}
    (hp₁ : p ∈ edgeArc (d.realizeDrawing R t) d.newEdge₁)
    (hp₂ : p ∈ edgeArc (d.realizeDrawing R t) d.newEdge₂) :
    p ∈ V(d.realizeGraph R t) ∧ (d.realizeGraph R t).Inc d.newEdge₁ p ∧
      (d.realizeGraph R t).Inc d.newEdge₂ p := by
  have hmem : p ∈ ({R.drawing d.edge t} : Set Plane) := by
    rw [← edgeArc_new_inter ht]; exact ⟨hp₁, hp₂⟩
  rw [mem_singleton_iff] at hmem
  subst hmem
  exact ⟨by rw [realizeGraph_vertexSet]; exact mem_insert _ _,
    (realizeGraph_isLink_newEdge₁).inc_right, (realizeGraph_isLink_newEdge₂).inc_left⟩


-- @@ L742-758 verbatim
/-- The first new edge meets an old edge only at the position of `d.left`. -/
theorem edge_inter_newEdge₁_old {g : γ} (hg : g ∈ E(S.skel)) (hge : g ≠ d.edge) {p : Plane}
    (hp₁ : p ∈ edgeArc (d.realizeDrawing R t) d.newEdge₁)
    (hpg : p ∈ edgeArc (d.realizeDrawing R t) g) :
    p ∈ V(d.realizeGraph R t) ∧ (d.realizeGraph R t).Inc d.newEdge₁ p ∧
      (d.realizeGraph R t).Inc g p := by
  have hgc := S.mem_cells_of_mem_edgeSet hg
  rw [edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hgc) (d.ne_newEdge₂_of_mem_cells hgc)] at hpg
  obtain ⟨hpV, -, hpgInc⟩ := R.isDrawing.edge_inter (d.edge_mem_edgeSet_graph R)
    (by rw [edgeSet_map]; exact hg) (Ne.symm hge)
    (edgeArc_newEdge₁_subset ht hp₁) hpg
  rcases mem_edgeArc_newEdge₁_vertex ht (mem_realizeGraph_vertexSet_of_mem hpV) hp₁ with
    h | h
  · subst h
    exact ⟨mem_realizeGraph_vertexSet_of_mem hpV, (realizeGraph_isLink_newEdge₁).inc_left,
      (realizeGraph_inc_old hg hge).2 hpgInc⟩
  · exact absurd (h ▸ hpV) (d.newPos_notMem_vertexSet R ht)


-- @@ L760-776 verbatim
/-- The second new edge meets an old edge only at the position of `d.right`. -/
theorem edge_inter_newEdge₂_old {g : γ} (hg : g ∈ E(S.skel)) (hge : g ≠ d.edge) {p : Plane}
    (hp₂ : p ∈ edgeArc (d.realizeDrawing R t) d.newEdge₂)
    (hpg : p ∈ edgeArc (d.realizeDrawing R t) g) :
    p ∈ V(d.realizeGraph R t) ∧ (d.realizeGraph R t).Inc d.newEdge₂ p ∧
      (d.realizeGraph R t).Inc g p := by
  have hgc := S.mem_cells_of_mem_edgeSet hg
  rw [edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hgc) (d.ne_newEdge₂_of_mem_cells hgc)] at hpg
  obtain ⟨hpV, -, hpgInc⟩ := R.isDrawing.edge_inter (d.edge_mem_edgeSet_graph R)
    (by rw [edgeSet_map]; exact hg) (Ne.symm hge)
    (edgeArc_newEdge₂_subset ht hp₂) hpg
  rcases mem_edgeArc_newEdge₂_vertex ht (mem_realizeGraph_vertexSet_of_mem hpV) hp₂ with
    h | h
  · exact absurd (h ▸ hpV) (d.newPos_notMem_vertexSet R ht)
  · subst h
    exact ⟨mem_realizeGraph_vertexSet_of_mem hpV,
      (realizeGraph_isLink_newEdge₂).inc_right, (realizeGraph_inc_old hg hge).2 hpgInc⟩


-- @@ L778-791 verbatim
omit ht in
/-- Two old edges meet where they met before. -/
theorem edge_inter_old_old {f g : γ} (hf : f ∈ E(S.skel)) (hfe : f ≠ d.edge)
    (hg : g ∈ E(S.skel)) (hge : g ≠ d.edge) (hfg : f ≠ g) {p : Plane}
    (hpf : p ∈ edgeArc (d.realizeDrawing R t) f) (hpg : p ∈ edgeArc (d.realizeDrawing R t) g) :
    p ∈ V(d.realizeGraph R t) ∧ (d.realizeGraph R t).Inc f p ∧ (d.realizeGraph R t).Inc g p := by
  have hfc := S.mem_cells_of_mem_edgeSet hf
  have hgc := S.mem_cells_of_mem_edgeSet hg
  rw [edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hfc) (d.ne_newEdge₂_of_mem_cells hfc)] at hpf
  rw [edgeArc_of_ne (d.ne_newEdge₁_of_mem_cells hgc) (d.ne_newEdge₂_of_mem_cells hgc)] at hpg
  obtain ⟨hpV, h₁, h₂⟩ := R.isDrawing.edge_inter (by rw [edgeSet_map]; exact hf)
    (by rw [edgeSet_map]; exact hg) hfg hpf hpg
  exact ⟨mem_realizeGraph_vertexSet_of_mem hpV, (realizeGraph_inc_old hf hfe).2 h₁,
    (realizeGraph_inc_old hg hge).2 h₂⟩


-- @@ L793-793 verbatim
/-! ### The subdivided drawing -/


-- @@ L795-871 verbatim
/-- **The subdivided data really is a drawing.** -/
theorem isDrawing_realize : IsDrawing (d.realizeGraph R t) (d.realizeDrawing R t) where
  edge_param := by
    intro f hf
    rw [realizeGraph_edgeSet, d.skeleton_edgeSet] at hf
    simp only [mem_insert_iff, mem_sdiff, mem_singleton_iff] at hf
    rcases hf with rfl | rfl | ⟨hfS, hfe⟩
    · rw [realizeDrawing_newEdge₁]
      refine ⟨continuousOn_subarc (d.continuousOn_drawing_edge R) (d.leftParam_mem_I R)
          (Ioo_subset_Icc_self ht),
        injOn_subarc ((d.injOn_drawing_edge R).mono
          (uIcc_subset_I (d.leftParam_mem_I R) (Ioo_subset_Icc_self ht))) (d.leftParam_ne R ht),
        ?_⟩
      rw [subarc_zero, subarc_one, d.drawing_leftParam R]
      exact realizeGraph_isLink_newEdge₁
    · rw [realizeDrawing_newEdge₂]
      refine ⟨continuousOn_subarc (d.continuousOn_drawing_edge R) (Ioo_subset_Icc_self ht)
          (d.rightParam_mem_I R),
        injOn_subarc ((d.injOn_drawing_edge R).mono
          (uIcc_subset_I (Ioo_subset_Icc_self ht) (d.rightParam_mem_I R)))
          (Ne.symm (d.rightParam_ne R ht)), ?_⟩
      rw [subarc_zero, subarc_one, d.drawing_rightParam R]
      exact realizeGraph_isLink_newEdge₂
    · have hfc := S.mem_cells_of_mem_edgeSet hfS
      rw [realizeDrawing_of_mem_cells hfc]
      have hd := R.isDrawing.edge_param
        (show f ∈ E(R.graph) by rw [Realization.edgeSet_graph]; exact hfS)
      exact ⟨hd.1, hd.2.1, (realizeGraph_isLink_old hfS hfe).2 hd.2.2⟩
  vertex_mem_edgeArc := by
    intro f x y v hl hv hva
    by_cases hf₁ : f = d.newEdge₁
    · subst hf₁
      rcases hl.eq_and_eq_or_eq_and_eq (realizeGraph_isLink_newEdge₁) with
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact mem_edgeArc_newEdge₁_vertex ht hv hva
      · exact (mem_edgeArc_newEdge₁_vertex ht hv hva).symm
    · by_cases hf₂ : f = d.newEdge₂
      · subst hf₂
        rcases hl.eq_and_eq_or_eq_and_eq (realizeGraph_isLink_newEdge₂) with
          ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact mem_edgeArc_newEdge₂_vertex ht hv hva
        · exact (mem_edgeArc_newEdge₂_vertex ht hv hva).symm
      · obtain ⟨hfS, hfe⟩ := mem_edgeSet_skel_of_ne hl.edge_mem hf₁ hf₂
        rw [edgeArc_of_ne hf₁ hf₂] at hva
        rw [realizeGraph_isLink_old hfS hfe] at hl
        rw [realizeGraph_vertexSet, mem_insert_iff] at hv
        rcases hv with rfl | hv
        · exact absurd hva (newPos_notMem_edgeArc_of_ne ht hfS hfe)
        · exact R.isDrawing.vertex_mem_edgeArc hl hv hva
  edge_inter := by
    intro f g hf hg hfg p hpf hpg
    by_cases hf₁ : f = d.newEdge₁
    · subst hf₁
      by_cases hg₂ : g = d.newEdge₂
      · subst hg₂
        exact edge_inter_new_new ht hpf hpg
      · obtain ⟨hgS, hge⟩ := mem_edgeSet_skel_of_ne hg (Ne.symm hfg) hg₂
        exact edge_inter_newEdge₁_old ht hgS hge hpf hpg
    · by_cases hf₂ : f = d.newEdge₂
      · subst hf₂
        by_cases hg₁ : g = d.newEdge₁
        · subst hg₁
          obtain ⟨h₁, h₂, h₃⟩ := edge_inter_new_new ht hpg hpf
          exact ⟨h₁, h₃, h₂⟩
        · obtain ⟨hgS, hge⟩ := mem_edgeSet_skel_of_ne hg hg₁ (Ne.symm hfg)
          exact edge_inter_newEdge₂_old ht hgS hge hpf hpg
      · obtain ⟨hfS, hfe⟩ := mem_edgeSet_skel_of_ne hf hf₁ hf₂
        by_cases hg₁ : g = d.newEdge₁
        · subst hg₁
          obtain ⟨h₁, h₂, h₃⟩ := edge_inter_newEdge₁_old ht hfS hfe hpg hpf
          exact ⟨h₁, h₃, h₂⟩
        · by_cases hg₂ : g = d.newEdge₂
          · subst hg₂
            obtain ⟨h₁, h₂, h₃⟩ := edge_inter_newEdge₂_old ht hfS hfe hpg hpf
            exact ⟨h₁, h₃, h₂⟩
          · obtain ⟨hgS, hge⟩ := mem_edgeSet_skel_of_ne hg hg₁ hg₂
            exact edge_inter_old_old hfS hfe hgS hge hfg hpf hpg


-- @@ L873-873 verbatim
/-! ### The two new open edges, as arcs -/


-- @@ L875-880 verbatim
/-- The first new edge is drawn as an arc from the position of `d.left` to the new point. -/
theorem isArcBetween_newEdge₁ : IsArcBetween (edgeArc (d.realizeDrawing R t) d.newEdge₁)
    (R.pos d.left) (R.drawing d.edge t) := by
  rw [edgeArc_newEdge₁, ← d.drawing_leftParam R]
  exact isArcBetween_subarc_of_injOn_I (d.continuousOn_drawing_edge R) (d.injOn_drawing_edge R)
    (d.leftParam_mem_I R) (Ioo_subset_Icc_self ht) (d.leftParam_ne R ht)


-- @@ L882-887 verbatim
/-- The second new edge is drawn as an arc from the new point to the position of `d.right`. -/
theorem isArcBetween_newEdge₂ : IsArcBetween (edgeArc (d.realizeDrawing R t) d.newEdge₂)
    (R.drawing d.edge t) (R.pos d.right) := by
  rw [edgeArc_newEdge₂, ← d.drawing_rightParam R]
  exact isArcBetween_subarc_of_injOn_I (d.continuousOn_drawing_edge R) (d.injOn_drawing_edge R)
    (Ioo_subset_Icc_self ht) (d.rightParam_mem_I R) (Ne.symm (d.rightParam_ne R ht))


-- @@ L889-889 verbatim
end


-- @@ L891-891 verbatim
/-! ### The realization of the subdivided structure -/


-- @@ L893-907 verbatim
/-- **The realization of an edge subdivision.** The new 0-cell goes to the point of the drawn
edge at parameter `t`, the two new 1-cells are drawn by the two halves of that parametrization,
and every surviving cell is exactly where it was.

There is no geometric side condition: everything the construction needs is already carried by
`R`, and is extracted by the lemmas above rather than assumed. -/
noncomputable def realize (d : S.SubdivData) (R : S.Realization) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) : (S.subdivideEdge d).Realization where
  pos := d.realizePos R t
  drawing := d.realizeDrawing R t
  injOn_pos := injOn_realizePos ht
  isDrawing := isDrawing_realize ht
  cell := d.realizeCell R t
  cell_vertex := cell_vertex_realize
  cell_edge := cell_edge_realize


-- @@ L909-909 verbatim
variable (ht : t ∈ Ioo (0 : ℝ) 1)


-- @@ L911-911 verbatim
@[simp] theorem realize_pos : (d.realize R t ht).pos = d.realizePos R t := rfl


-- @@ L913-913 verbatim
@[simp] theorem realize_drawing : (d.realize R t ht).drawing = d.realizeDrawing R t := rfl


-- @@ L915-915 verbatim
@[simp] theorem realize_cell : (d.realize R t ht).cell = d.realizeCell R t := rfl


-- @@ L917-917 verbatim
include ht


-- @@ L919-919 verbatim
/-! ### The realization refines the old one -/


-- @@ L921-924 verbatim
theorem closure_realizeCell_newEdge₁ :
    closure (d.realizeCell R t d.newEdge₁) = edgeArc (d.realizeDrawing R t) d.newEdge₁ := by
  rw [realizeCell_newEdge₁, ← edgeArc_newEdge₁]
  exact (isArcBetween_newEdge₁ ht).closure_diff_eq


-- @@ L926-929 verbatim
theorem closure_realizeCell_newEdge₂ :
    closure (d.realizeCell R t d.newEdge₂) = edgeArc (d.realizeDrawing R t) d.newEdge₂ := by
  rw [realizeCell_newEdge₂, ← edgeArc_newEdge₂]
  exact (isArcBetween_newEdge₂ ht).closure_diff_eq


-- @@ L931-950 verbatim
/-- **The old open edge is cut into the two new open edges and the new 0-cell.** -/
theorem realizeCell_edge_eq : R.cell d.edge = d.realizeCell R t d.newEdge₁ ∪
    d.realizeCell R t d.newVertex ∪ d.realizeCell R t d.newEdge₂ := by
  rw [R.cell_edge d.isLink, realizeCell_newEdge₁, realizeCell_newVertex, realizeCell_newEdge₂,
    ← edgeArc_newEdge₁, ← edgeArc_newEdge₂, ← edgeArc_new_union ht]
  ext p
  simp only [mem_union, mem_sdiff, mem_insert_iff, mem_singleton_iff, not_or]
  constructor
  · rintro ⟨hp | hp, hL, hR⟩
    · by_cases hM : p = R.drawing d.edge t
      · exact Or.inl (Or.inr hM)
      · exact Or.inl (Or.inl ⟨hp, hL, hM⟩)
    · by_cases hM : p = R.drawing d.edge t
      · exact Or.inl (Or.inr hM)
      · exact Or.inr ⟨hp, hM, hR⟩
  · rintro ((⟨hp, hL, hM⟩ | rfl) | ⟨hp, hM, hR⟩)
    · exact ⟨Or.inl hp, hL, fun h => posRight_notMem_edgeArc_newEdge₁ ht (h ▸ hp)⟩
    · exact ⟨Or.inl newPos_mem_edgeArc_newEdge₁, d.newPos_ne_pos R ht d.isLink.left_mem,
        d.newPos_ne_pos R ht d.isLink.right_mem⟩
    · exact ⟨Or.inr hp, fun h => posLeft_notMem_edgeArc_newEdge₂ ht (h ▸ hp), hR⟩


-- @@ L952-954 verbatim
theorem nonempty_realizeCell_newEdge₁ : (d.realizeCell R t d.newEdge₁).Nonempty := by
  rw [realizeCell_newEdge₁, ← edgeArc_newEdge₁]
  exact (isArcBetween_newEdge₁ ht).nonempty_diff


-- @@ L956-958 verbatim
theorem nonempty_realizeCell_newEdge₂ : (d.realizeCell R t d.newEdge₂).Nonempty := by
  rw [realizeCell_newEdge₂, ← edgeArc_newEdge₂]
  exact (isArcBetween_newEdge₂ ht).nonempty_diff


-- @@ L960-964 verbatim
omit ht in
theorem disjoint_newEdge₁_newVertex :
    Disjoint (d.realizeCell R t d.newEdge₁) (d.realizeCell R t d.newVertex) := by
  rw [realizeCell_newEdge₁, realizeCell_newVertex]
  exact disjoint_left.2 fun _ hp hq => hp.2 (Or.inr (mem_singleton_iff.1 hq))


-- @@ L966-970 verbatim
omit ht in
theorem disjoint_newEdge₂_newVertex :
    Disjoint (d.realizeCell R t d.newEdge₂) (d.realizeCell R t d.newVertex) := by
  rw [realizeCell_newEdge₂, realizeCell_newVertex]
  exact disjoint_left.2 fun _ hp hq => hp.2 (Or.inl (mem_singleton_iff.1 hq))


-- @@ L972-979 verbatim
theorem disjoint_newEdge₁_newEdge₂ :
    Disjoint (d.realizeCell R t d.newEdge₁) (d.realizeCell R t d.newEdge₂) := by
  refine disjoint_left.2 fun p hp hq => ?_
  rw [realizeCell_newEdge₁, ← edgeArc_newEdge₁] at hp
  rw [realizeCell_newEdge₂, ← edgeArc_newEdge₂] at hq
  have : p ∈ ({R.drawing d.edge t} : Set Plane) := by
    rw [← edgeArc_new_inter ht]; exact ⟨hp.1, hq.1⟩
  exact hp.2 (Or.inr (mem_singleton_iff.1 this))


-- @@ L981-1017 verbatim
/-- **The subdivided realization refines the given one** — every field of
`SubdivData.IsRefinement`. With `IsRefinement.isCellDecomposition_and_isFaceJordan` this hands a
consumer `IsCellDecomposition`, `IsFaceJordan` and `Refines` at the new stage. -/
theorem isRefinement_realize : d.IsRefinement R (d.realize R t ht) where
  cell_eq := fun _ hc _ => realizeCell_of_mem_cells hc
  cell_edge := realizeCell_edge_eq ht
  nonempty := by
    rintro c (rfl | rfl | rfl)
    · rw [realize_cell, realizeCell_newVertex]
      exact ⟨R.drawing d.edge t, rfl⟩
    · exact nonempty_realizeCell_newEdge₁ ht
    · exact nonempty_realizeCell_newEdge₂ ht
  disjoint := by
    rintro c τ (rfl | rfl | rfl) (rfl | rfl | rfl) hne
    · exact absurd rfl hne
    · exact (disjoint_newEdge₁_newVertex (t := t)).symm
    · exact (disjoint_newEdge₂_newVertex (t := t)).symm
    · exact disjoint_newEdge₁_newVertex
    · exact absurd rfl hne
    · exact disjoint_newEdge₁_newEdge₂ ht
    · exact disjoint_newEdge₂_newVertex
    · exact (disjoint_newEdge₁_newEdge₂ ht).symm
    · exact absurd rfl hne
  closure_newVertex := by
    simp only [realize_cell]
    rw [realizeCell_newVertex, closure_singleton]
  closure_newEdge₁ := by
    simp only [realize_cell]
    rw [closure_realizeCell_newEdge₁ ht, realizeCell_newVertex,
      R.cell_vertex d.isLink.left_mem, realizeCell_newEdge₁, ← edgeArc_newEdge₁]
    exact (diff_pair_union_union posLeft_mem_edgeArc_newEdge₁ newPos_mem_edgeArc_newEdge₁).symm
  closure_newEdge₂ := by
    simp only [realize_cell]
    rw [closure_realizeCell_newEdge₂ ht, realizeCell_newVertex,
      R.cell_vertex d.isLink.right_mem, realizeCell_newEdge₂, ← edgeArc_newEdge₂,
      pair_comm (R.drawing d.edge t) (R.pos d.right)]
    exact (diff_pair_union_union posRight_mem_edgeArc_newEdge₂ newPos_mem_edgeArc_newEdge₂).symm


-- @@ L1019-1026 verbatim
/-- **The whole induction step over the first constructor, constructed.** One edge subdivision of
a realization satisfying (i) and (vii) produces a realization satisfying (i) and (vii) and
refining it, constructing the refined realization in the conclusion. -/
theorem realize_isCellDecomposition_and_isFaceJordan (hS : S.CombInvariants) {D : Set Plane}
    (h : R.IsCellDecomposition D) (hJ : R.IsFaceJordan) :
    (d.realize R t ht).IsCellDecomposition D ∧ (d.realize R t ht).IsFaceJordan ∧
      (d.realize R t ht).Refines R d.parent :=
  (isRefinement_realize ht).isCellDecomposition_and_isFaceJordan hS h hJ


-- @@ L1028-1032 verbatim
/-! ### The subdivision does not move the skeleton

Cutting an edge in two adds a point that was already on the drawing and replaces one arc by two
whose union is that arc. So the realized 1-skeleton is literally the same set — which is what
lets a skeleton homeomorphism be transported across a subdivision without being rebuilt. -/


-- @@ L1034-1050 verbatim
theorem pointSet_realize :
    pointSet (d.realizeGraph R t) (d.realizeDrawing R t) = pointSet R.graph R.drawing := by
  have hedge : (⋃ f ∈ E(R.graph), edgeArc R.drawing f) =
      edgeArc R.drawing d.edge ∪ ⋃ f ∈ E(S.skel) \ {d.edge}, edgeArc R.drawing f := by
    rw [← biUnion_insert, insert_sdiff_singleton,
      insert_eq_of_mem (show d.edge ∈ E(S.skel) from d.edge_mem_edgeSet), Realization.edgeSet_graph]
  have hnew : (⋃ f ∈ E(d.realizeGraph R t), edgeArc (d.realizeDrawing R t) f) =
      edgeArc R.drawing d.edge ∪ ⋃ f ∈ E(S.skel) \ {d.edge}, edgeArc R.drawing f := by
    rw [realizeGraph_edgeSet, d.skeleton_edgeSet, biUnion_insert, biUnion_insert,
      iUnion₂_congr (fun f (hf : f ∈ E(S.skel) \ {d.edge}) =>
        edgeArc_of_ne (d := d) (R := R) (t := t)
          (d.ne_newEdge₁_of_mem_cells (S.mem_cells_of_mem_edgeSet hf.1))
          (d.ne_newEdge₂_of_mem_cells (S.mem_cells_of_mem_edgeSet hf.1))),
      ← union_assoc, edgeArc_new_union ht]
  have hM : R.drawing d.edge t ∈ edgeArc R.drawing d.edge := ⟨t, Ioo_subset_Icc_self ht, rfl⟩
  rw [pointSet, pointSet, hnew, hedge, realizeGraph_vertexSet, insert_union,
    insert_eq_of_mem (mem_union_right _ (mem_union_left _ hM))]


-- @@ L1052-1053 verbatim
/-- **An edge subdivision does not move the realized 1-skeleton.** -/
theorem skeletonSet_realize : (d.realize R t ht).skeletonSet = R.skeletonSet := pointSet_realize ht


-- @@ L1055-1055 verbatim
end SubdivData


-- @@ L1057-1057 verbatim
end CellStructure


-- @@ L1059-1059 verbatim
end Schoenflies
