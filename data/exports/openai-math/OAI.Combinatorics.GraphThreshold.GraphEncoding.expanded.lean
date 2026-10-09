import OAI.Combinatorics.GraphThreshold.Statement
import Mathlib.Algebra.Group.Action.Pointwise.Finset


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
open scoped Pointwise


-- @@ L10-10 verbatim
namespace LeanBlast.SecondKahnKalai


-- @@ L12-15 verbatim
/-- The non-loop edge set of an ordinary graph on `Fin n`. -/
def graphEdges {n : ℕ} (G : SimpleGraph (Fin n)) : Finset (Edge n) := by
  classical
  exact Finset.univ.filter (fun e => e.val ∈ G.edgeSet)


-- @@ L17-17 verbatim
variable {n : ℕ}


-- @@ L19-31 verbatim
/-- Vertex permutations act on unordered non-loop edges. -/
instance edgeMulAction : MulAction (Equiv.Perm (Fin n)) (Edge n) where
  smul σ e := ⟨Sym2.map σ e.val, fun h =>
    e.property ((Sym2.isDiag_map σ.injective).mp h)⟩
  one_smul e := by
    apply Subtype.ext
    change Sym2.map (1 : Equiv.Perm (Fin n)) e.val = e.val
    simp
  mul_smul σ τ e := by
    apply Subtype.ext
    change Sym2.map (σ * τ) e.val = Sym2.map σ (Sym2.map τ e.val)
    rw [Sym2.map_map]
    rfl


-- @@ L33-35 verbatim
@[simp]
theorem edge_smul_val (σ : Equiv.Perm (Fin n)) (e : Edge n) :
    (σ • e).val = Sym2.map σ e.val := rfl


-- @@ L37-41 verbatim
@[simp]
theorem mem_graphEdges (G : SimpleGraph (Fin n)) (e : Edge n) :
    e ∈ graphEdges G ↔ e.val ∈ G.edgeSet := by
  classical
  simp [graphEdges]


-- @@ L43-50 verbatim
theorem edgeSet_graphOfEdges (W : Finset (Edge n)) :
    (graphOfEdges W).edgeSet = Subtype.val '' (W : Set (Edge n)) := by
  rw [graphOfEdges, SimpleGraph.edgeSet_fromEdgeSet]
  ext e
  constructor
  · exact And.left
  · rintro ⟨a, ha, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, a.property⟩


-- @@ L52-56 verbatim
@[simp]
theorem mem_edgeSet_graphOfEdges (W : Finset (Edge n)) (e : Edge n) :
    e.val ∈ (graphOfEdges W).edgeSet ↔ e ∈ W := by
  classical
  simp [graphOfEdges, e.property, Subtype.val_injective.eq_iff]


-- @@ L58-63 verbatim
@[simp]
theorem graphEdges_graphOfEdges (W : Finset (Edge n)) :
    graphEdges (graphOfEdges W) = W := by
  classical
  ext e
  simp


-- @@ L65-73 verbatim
@[simp]
theorem graphOfEdges_graphEdges (G : SimpleGraph (Fin n)) :
    graphOfEdges (graphEdges G) = G := by
  apply SimpleGraph.edgeSet_injective
  ext e
  by_cases he : e.IsDiag
  · simp [SimpleGraph.not_mem_edgeSet_of_isDiag, he]
  · exact (mem_edgeSet_graphOfEdges (graphEdges G) ⟨e, he⟩).trans
      (mem_graphEdges G ⟨e, he⟩)


-- @@ L75-80 verbatim
/-- No graphs or edge sets are omitted or multiply represented. -/
def graphEdgeEquiv (n : ℕ) : Finset (Edge n) ≃ SimpleGraph (Fin n) where
  toFun := graphOfEdges
  invFun := graphEdges
  left_inv := graphEdges_graphOfEdges
  right_inv := graphOfEdges_graphEdges


-- @@ L82-87 verbatim
theorem graphOfEdges_smul (σ : Equiv.Perm (Fin n)) (W : Finset (Edge n)) :
    graphOfEdges (σ • W) = (graphOfEdges W).map σ.toEmbedding := by
  apply SimpleGraph.edgeSet_injective
  rw [edgeSet_graphOfEdges, SimpleGraph.edgeSet_map, edgeSet_graphOfEdges,
    Finset.smul_finset_def, Finset.coe_image, Set.image_image, Set.image_image]
  rfl


-- @@ L89-93 verbatim
theorem graphEdges_map (σ : Equiv.Perm (Fin n)) (G : SimpleGraph (Fin n)) :
    graphEdges (G.map σ.toEmbedding) = σ • graphEdges G := by
  apply (graphEdgeEquiv n).injective
  change graphOfEdges _ = graphOfEdges _
  rw [graphOfEdges_graphEdges, graphOfEdges_smul, graphOfEdges_graphEdges]


-- @@ L95-97 verbatim
@[simp]
theorem graphOfEdges_empty : graphOfEdges (∅ : Finset (Edge n)) = ⊥ := by
  simp [graphOfEdges]


-- @@ L99-103 verbatim
@[simp]
theorem graphEdges_bot : graphEdges (⊥ : SimpleGraph (Fin n)) = ∅ := by
  classical
  ext e
  simp


-- @@ L105-109 verbatim
@[simp]
theorem graphEdges_top : graphEdges (⊤ : SimpleGraph (Fin n)) = Finset.univ := by
  classical
  ext e
  simp [e.property]


-- @@ L111-113 verbatim
@[simp]
theorem graphOfEdges_univ : graphOfEdges (Finset.univ : Finset (Edge n)) = ⊤ := by
  rw [← graphEdges_top, graphOfEdges_graphEdges]


-- @@ L115-119 verbatim
theorem graphEdges_mono {G H : SimpleGraph (Fin n)} (h : G ≤ H) :
    graphEdges G ⊆ graphEdges H := by
  intro e he
  exact (mem_graphEdges H e).mpr (SimpleGraph.edgeSet_mono h
    ((mem_graphEdges G e).mp he))


-- @@ L121-124 verbatim
theorem graphOfEdges_mono {S T : Finset (Edge n)} (h : S ⊆ T) :
    graphOfEdges S ≤ graphOfEdges T := by
  apply SimpleGraph.fromEdgeSet_mono
  exact Set.image_mono h


-- @@ L126-132 verbatim
@[simp]
theorem graphOfEdges_le_iff {S T : Finset (Edge n)} :
    graphOfEdges S ≤ graphOfEdges T ↔ S ⊆ T := by
  constructor
  · intro h
    simpa using graphEdges_mono h
  · exact graphOfEdges_mono


-- @@ L134-140 verbatim
/-- Edge-set encoding preserves the ordinary unlabelled edge count. -/
def graphEdgesEquiv (G : SimpleGraph (Fin n)) : ↥(graphEdges G) ≃ G.edgeSet where
  toFun e := ⟨e.val.val, (mem_graphEdges G e.val).mp e.property⟩
  invFun e := ⟨⟨e.val, G.not_isDiag_of_mem_edgeSet e.property⟩,
    (mem_graphEdges G _).mpr e.property⟩
  left_inv _ := rfl
  right_inv _ := rfl


-- @@ L142-147 verbatim
@[simp]
theorem card_graphEdges (G : SimpleGraph (Fin n)) :
    (graphEdges G).card = edgeCount G := by
  classical
  rw [edgeCount, Nat.card_eq_fintype_card, ← Fintype.card_coe]
  exact Fintype.card_congr (graphEdgesEquiv G)


-- @@ L149-152 verbatim
@[simp]
theorem edgeCount_graphOfEdges (W : Finset (Edge n)) :
    edgeCount (graphOfEdges W) = W.card := by
  rw [← card_graphEdges, graphEdges_graphOfEdges]


-- @@ L154-158 verbatim
theorem edgeCount_eq_card_edgeFinset {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    edgeCount G = G.edgeFinset.card := by
  classical
  rw [edgeCount, Nat.card_eq_fintype_card, SimpleGraph.edgeFinset_card]


-- @@ L160-164 verbatim
theorem edgeCount_eq_zero_iff {V : Type*} [Fintype V] (G : SimpleGraph V) :
    edgeCount G = 0 ↔ G = ⊥ := by
  classical
  rw [edgeCount_eq_card_edgeFinset, Finset.card_eq_zero]
  exact G.edgeFinset_eq_empty


-- @@ L166-168 verbatim
theorem positive_copies_iff {V : Type*} (W : Finset (Edge n)) (H : SimpleGraph V) :
    0 < (graphOfEdges W).copyCount H ↔ H.IsContained (graphOfEdges W) :=
  SimpleGraph.copyCount_pos


-- @@ L170-170 verbatim
end LeanBlast.SecondKahnKalai


-- @@ L172-172 verbatim
end


-- @@ L174-174 verbatim
end OAI
