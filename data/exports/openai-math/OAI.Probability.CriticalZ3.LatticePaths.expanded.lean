import OAI.Probability.CriticalZ3.BoxGeometry


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open MeasureTheory ProbabilityTheory Classical Filter


-- @@ L7-7 verbatim
open scoped ENNReal BigOperators Matrix


-- @@ L9-9 verbatim
namespace CriticalZ3

-- @@ L10-10 verbatim
open Classical


-- @@ L12-12 verbatim
inductive Model | bond | site


-- @@ L14-14 verbatim
namespace Model

-- @@ L15-17 verbatim
abbrev Bit : Model → Type
  | bond => Bond
  | site => Vertex

-- @@ L18-18 verbatim
abbrev Config (m : Model) := m.Bit → Bool

-- @@ L19-19 verbatim
instance (m : Model) : Countable m.Bit := by cases m <;> infer_instance

-- @@ L20-20 verbatim
instance (m : Model) : DecidableEq m.Bit := by cases m <;> infer_instance

-- @@ L21-21 verbatim
end Model


-- @@ L23-23 verbatim
namespace Box

-- @@ L24-26 verbatim
noncomputable def bits (B : Box) : (m : Model) → Finset m.Bit
  | .bond => B.bonds
  | .site => B.vertices

-- @@ L27-27 verbatim
end Box


-- @@ L29-29 verbatim
namespace LatticeGraph

-- @@ L30-30 verbatim
variable (G : LatticeGraph)

-- @@ L31-33 verbatim
noncomputable def bits : (m : Model) → Finset m.Bit
  | .bond => G.edges
  | .site => G.vertices


-- @@ L35-37 verbatim
def Open : (m : Model) → m.Config → G.Node → Prop
  | .bond,_,_ => True
  | .site,ω,x => ω x.1 = true


-- @@ L39-41 verbatim
def Adj : (m : Model) → m.Config → G.Node → G.Node → Prop
  | .bond,ω,x,y => G.BondAdj ω x y
  | .site,ω,x,y => G.graph.Adj x y ∧ ω x.1 = true ∧ ω y.1 = true


-- @@ L43-45 verbatim
def Conn : (m : Model) → m.Config → G.Node → G.Node → Prop
  | .bond,ω,x,y => G.BondConn ω x y
  | .site,ω,x,y => G.SiteConn ω x y


-- @@ L47-48 verbatim
def Meets (m : Model) (ω : m.Config) (o : G.Node) (T : Set Vertex) : Prop :=
  ∃ y : G.Node, y.1 ∈ T ∧ G.Conn m ω o y


-- @@ L50-54 verbatim
theorem conn_iff (m : Model) (ω : m.Config) (x y : G.Node) :
    G.Conn m ω x y ↔ G.Open m ω x ∧ Relation.ReflTransGen (G.Adj m ω) x y := by
  cases m
  · exact ⟨fun h => ⟨trivial,h⟩,fun h => h.2⟩
  · rfl


-- @@ L56-60 verbatim
theorem adj_open (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Adj m ω x y) :
    G.Open m ω x ∧ G.Open m ω y := by
  cases m
  · exact ⟨trivial,trivial⟩
  · exact h.2


-- @@ L62-66 verbatim
theorem adj_neighbor (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Adj m ω x y) :
    NearestNeighbor x.1 y.1 := by
  cases m
  · obtain ⟨e,_,he,_⟩ := h; exact incidence_neighbor he
  · obtain ⟨⟨e,_,he⟩,_⟩ := h; exact incidence_neighbor he


-- @@ L68-72 verbatim
theorem adj_symm (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Adj m ω x y) :
    G.Adj m ω y x := by
  cases m
  · obtain ⟨e,he,hi,ho⟩ := h; exact ⟨e,he,incidence_symm hi,ho⟩
  · exact ⟨G.graph.adj_symm h.1,h.2.2,h.2.1⟩


-- @@ L74-80 verbatim
theorem conn_open (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Conn m ω x y) :
    G.Open m ω x ∧ G.Open m ω y := by
  obtain ⟨hx,h⟩ := (G.conn_iff m ω x y).mp h
  refine ⟨hx,?_⟩
  induction h with
  | refl => exact hx
  | tail _ hab _ => exact (G.adj_open m hab).2


-- @@ L82-89 verbatim
theorem conn_symm (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Conn m ω x y) :
    G.Conn m ω y x := by
  refine (G.conn_iff m ω y x).mpr ⟨(G.conn_open m h).2,?_⟩
  have hh := (G.conn_iff m ω x y).mp h |>.2
  clear h
  induction hh with
  | refl => exact .refl
  | tail _ hab ih => exact ih.head (G.adj_symm m hab)


-- @@ L91-94 verbatim
theorem conn_trans (m : Model) {ω : m.Config} {x y z : G.Node}
    (h : G.Conn m ω x y) (h' : G.Conn m ω y z) : G.Conn m ω x z := by
  exact (G.conn_iff m ω x z).mpr ⟨((G.conn_iff m ω x y).mp h).1,
    ((G.conn_iff m ω x y).mp h).2.trans ((G.conn_iff m ω y z).mp h').2⟩


-- @@ L96-97 verbatim
theorem conn_adj (m : Model) {ω : m.Config} {x y : G.Node} (h : G.Adj m ω x y) :
    G.Conn m ω x y := (G.conn_iff m ω x y).mpr ⟨(G.adj_open m h).1,.single h⟩


-- @@ L99-104 verbatim
theorem conn_determined (m : Model) (ω ω' : m.Config)
    (h : ∀ e ∈ G.bits m, ω' e = ω e) (x y : G.Node) :
    G.Conn m ω' x y ↔ G.Conn m ω x y := by
  cases m
  · exact G.bondConn_determined ω ω' h x y
  · exact G.siteConn_determined ω ω' h x y


-- @@ L106-110 verbatim
theorem meets_determined (m : Model) (o : G.Node) (T : Set Vertex) :
    ProductCylinder.DeterminedBy (F := Prop) (G.bits m) (fun ω => G.Meets m ω o T) := by
  intro ω ω' h
  apply propext
  simp only [Meets,G.conn_determined m ω ω' h]


-- @@ L112-115 verbatim
theorem measurableSet_meets (m : Model) (o : G.Node) (T : Set Vertex) :
    MeasurableSet {ω | G.Meets m ω o T} :=
  ProductCylinder.measurableSet_determined _ _ (fun ω ω' h =>
    eq_iff_iff.mp (G.meets_determined m o T ω ω' h))


-- @@ L117-124 verbatim
theorem failure_comparison (m : Model) (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (o : G.Node) (A T : Set Vertex) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ a : G.Node, a.1 ∈ A →
      1-b ≤ (ProductCylinder.law p).real {ω | G.Meets m ω a T}) :
    (ProductCylinder.law p).real {ω | G.Meets m ω o A ∧ ¬G.Meets m ω o T} ≤ b := by
  cases m
  · exact G.bond_failure_comparison p o A T hb0 hb
  · exact G.site_failure_comparison p o A T hb0 hb


-- @@ L126-126 verbatim
def ContainsBox (B : Box) : Prop := B.vertices ⊆ G.vertices ∧ B.bonds ⊆ G.edges


-- @@ L128-129 verbatim
theorem containsBox_node {B : Box} (h : G.ContainsBox B) {x : Vertex}
    (hx : B.Contains x) : x ∈ G.vertices := h.1 ((B.mem_vertices x).mpr hx)


-- @@ L131-135 verbatim
theorem neighbor_incidence {x y : Vertex} (h : NearestNeighbor x y) :
    ∃ e : Bond, Incidence e x y := by
  obtain ⟨i,h | h⟩ := h
  · exact ⟨(x,i),Or.inl ⟨rfl,h⟩⟩
  · exact ⟨(y,i),Or.inr ⟨rfl,h⟩⟩


-- @@ L137-142 verbatim
theorem incidence_internal {B : Box} {x y : Vertex} {e : Bond}
    (hx : B.Contains x) (hy : B.Contains y) (he : Incidence e x y) : e ∈ B.bonds := by
  rw [Box.mem_bonds]
  rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨hx,hy⟩
  · exact ⟨hy,hx⟩


-- @@ L144-153 verbatim
theorem open_box_adj (m : Model) {B : Box} (hB : G.ContainsBox B)
    {ω : m.Config} (ho : ∀ e ∈ B.bits m, ω e = true) {x y : G.Node}
    (hx : B.Contains x.1) (hy : B.Contains y.1) (hxy : NearestNeighbor x.1 y.1) :
    G.Adj m ω x y := by
  obtain ⟨e,he⟩ := neighbor_incidence hxy
  have heb := incidence_internal hx hy he
  cases m
  · exact ⟨e,hB.2 heb,he,ho e heb⟩
  · exact ⟨⟨e,hB.2 heb,he⟩,ho x.1 ((B.mem_vertices x.1).mpr hx),
      ho y.1 ((B.mem_vertices y.1).mpr hy)⟩


-- @@ L155-172 verbatim
/-- Lifting a vertex path into a finite graph, retaining the exact endpoints. -/
theorem lift_path {r : Vertex → Vertex → Prop} {s : G.Node → G.Node → Prop}
    (hmem : ∀ x y, r x y → y ∈ G.vertices)
    (hrel : ∀ (x y : G.Node), r x.1 y.1 → s x y)
    {x y : G.Node} (h : Relation.ReflTransGen r x.1 y.1) : Relation.ReflTransGen s x y := by
  have hh : ∀ {z : Vertex}, Relation.ReflTransGen r x.1 z →
      ∀ hz : z ∈ G.vertices, Relation.ReflTransGen s x ⟨z,hz⟩ := by
    intro z hp
    induction hp with
    | refl => intro _; exact .refl
    | @tail a b ha hab ih =>
      intro hb
      rcases ha.cases_tail with hxa | ⟨u,hu,hua⟩
      · subst a
        exact Relation.ReflTransGen.single (hrel x ⟨b,hb⟩ hab)
      · have ham := hmem u a hua
        exact (ih ham).tail (hrel ⟨a,ham⟩ ⟨b,hb⟩ hab)
  exact hh h y.2


-- @@ L174-185 verbatim
theorem open_box_conn (m : Model) {B : Box} (hB : G.ContainsBox B)
    {ω : m.Config} (ho : ∀ e ∈ B.bits m, ω e = true) {x y : G.Node}
    (hx : B.Contains x.1) (hy : B.Contains y.1) : G.Conn m ω x y := by
  apply (G.conn_iff m ω x y).mpr
  constructor
  · cases m
    · trivial
    · exact ho x.1 ((B.mem_vertices x.1).mpr hx)
  · apply G.lift_path (r := B.Within)
      (fun _ _ h => G.containsBox_node hB h.2.2)
      (fun x y h => G.open_box_adj m hB ho h.2.1 h.2.2 h.1)
    exact B.connected hx hy


-- @@ L187-187 verbatim
end LatticeGraph

-- @@ L188-188 verbatim
end CriticalZ3


-- @@ L190-190 verbatim
end OAI
