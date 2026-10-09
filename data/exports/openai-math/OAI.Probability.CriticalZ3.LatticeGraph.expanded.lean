import OAI.Probability.CriticalZ3.HyperedgeComparison


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open MeasureTheory ProbabilityTheory Classical Filter


-- @@ L7-7 verbatim
open scoped ENNReal BigOperators Matrix


-- @@ L9-9 verbatim
namespace CriticalZ3

-- @@ L10-10 verbatim
open Classical MeasureTheory ProbabilityTheory


-- @@ L12-14 verbatim
/-- An unoriented nearest-neighbor bond, in its unique positive-axis indexing. -/
def Incidence (e : Bond) (x y : Vertex) : Prop :=
  (x = e.1 ∧ y = step e.1 e.2) ∨ (y = e.1 ∧ x = step e.1 e.2)


-- @@ L16-19 verbatim
theorem step_ne (x : Vertex) (i : Fin 3) : step x i ≠ x := by
  intro h
  have := congrFun h i
  simp [step] at this


-- @@ L21-22 verbatim
theorem incidence_symm {e : Bond} {x y : Vertex} (h : Incidence e x y) :
    Incidence e y x := h.symm


-- @@ L24-27 verbatim
theorem incidence_ne {e : Bond} {x y : Vertex} (h : Incidence e x y) : x ≠ y := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact (step_ne _ _).symm
  · exact step_ne _ _


-- @@ L29-33 verbatim
theorem incidence_neighbor {e : Bond} {x y : Vertex} (h : Incidence e x y) :
    NearestNeighbor x y := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨e.2,Or.inl rfl⟩
  · exact ⟨e.2,Or.inr rfl⟩


-- @@ L35-39 verbatim
structure LatticeGraph where
  vertices : Finset Vertex
  edges : Finset Bond
  left_mem : ∀ e ∈ edges, e.1 ∈ vertices
  right_mem : ∀ e ∈ edges, step e.1 e.2 ∈ vertices


-- @@ L41-41 verbatim
namespace LatticeGraph

-- @@ L42-42 verbatim
variable (G : LatticeGraph)


-- @@ L44-44 verbatim
abbrev Node := G.vertices


-- @@ L46-49 verbatim
noncomputable def graph : SimpleGraph G.Node where
  Adj x y := ∃ e ∈ G.edges, Incidence e x y
  symm := ⟨by rintro x y ⟨e,he,h⟩; exact ⟨e,he,incidence_symm h⟩⟩
  loopless := ⟨by rintro x ⟨e,_,h⟩; exact incidence_ne h rfl⟩


-- @@ L51-52 verbatim
noncomputable def hypergraph : HyperedgeComparison.Hypergraph G.Node G.edges :=
  fun e x => x.1 = e.1.1 ∨ x.1 = step e.1.1 e.1.2


-- @@ L54-55 verbatim
def BondAdj (ω : BondConfig) (x y : G.Node) : Prop :=
  ∃ e ∈ G.edges, Incidence e x y ∧ ω e = true


-- @@ L57-58 verbatim
def BondConn (ω : BondConfig) (x y : G.Node) : Prop :=
  Relation.ReflTransGen (G.BondAdj ω) x y


-- @@ L60-61 verbatim
def SiteConn (ω : SiteConfig) (x y : G.Node) : Prop :=
  HyperedgeComparison.Site.Connected G.graph (fun z => ω z.1) x y


-- @@ L63-64 verbatim
def BondMeets (ω : BondConfig) (o : G.Node) (T : Set Vertex) : Prop :=
  ∃ y : G.Node, y.1 ∈ T ∧ G.BondConn ω o y


-- @@ L66-67 verbatim
def SiteMeets (ω : SiteConfig) (o : G.Node) (T : Set Vertex) : Prop :=
  ∃ y : G.Node, y.1 ∈ T ∧ G.SiteConn ω o y


-- @@ L69-74 verbatim
theorem bondAdj_open {ω : BondConfig} {x y : G.Node} (h : G.BondAdj ω x y) :
    BondOpen ω x.1 y.1 := by
  obtain ⟨e,_,h,he⟩ := h
  rcases h with ⟨hx,hy⟩ | ⟨hy,hx⟩
  · exact Or.inl ⟨e.2,by simpa [hx] using hy,by simpa [hx] using he⟩
  · exact Or.inr ⟨e.2,by simpa [hy] using hx,by simpa [hy] using he⟩


-- @@ L76-78 verbatim
theorem bondConn_global {ω : BondConfig} {x y : G.Node} (h : G.BondConn ω x y) :
    BondConnected ω x.1 y.1 := by
  exact h.lift Subtype.val (fun _ _ h => G.bondAdj_open h)


-- @@ L80-85 verbatim
theorem siteConn_global {ω : SiteConfig} {x y : G.Node} (h : G.SiteConn ω x y) :
    SiteConnected ω x.1 y.1 := by
  refine ⟨h.1,h.2.lift Subtype.val ?_⟩
  intro a b hab
  obtain ⟨⟨e,_,he⟩,ha,hb⟩ := hab
  exact ⟨incidence_neighbor he,ha,hb⟩


-- @@ L87-92 verbatim
theorem bondAdj_determined (ω ω' : BondConfig)
    (h : ∀ e ∈ G.edges, ω' e = ω e) (x y : G.Node) :
    G.BondAdj ω' x y ↔ G.BondAdj ω x y := by
  constructor <;> rintro ⟨e,he,hxy,ho⟩
  · exact ⟨e,he,hxy,(h e he) ▸ ho⟩
  · exact ⟨e,he,hxy,(h e he).symm ▸ ho⟩


-- @@ L94-99 verbatim
theorem bondConn_determined (ω ω' : BondConfig)
    (h : ∀ e ∈ G.edges, ω' e = ω e) (x y : G.Node) :
    G.BondConn ω' x y ↔ G.BondConn ω x y := by
  have he : G.BondAdj ω' = G.BondAdj ω := by
    funext a b; exact propext (G.bondAdj_determined ω ω' h a b)
  simp only [BondConn,he]


-- @@ L101-106 verbatim
theorem siteConn_determined (ω ω' : SiteConfig)
    (h : ∀ x ∈ G.vertices, ω' x = ω x) (x y : G.Node) :
    G.SiteConn ω' x y ↔ G.SiteConn ω x y := by
  have he : (fun z : G.Node => ω' z.1) = fun z => ω z.1 := by
    funext z; exact h z.1 z.2
  simp only [SiteConn,he]


-- @@ L108-111 verbatim
theorem bondMeets_determined (o : G.Node) (T : Set Vertex) :
    ProductCylinder.DeterminedBy (F := Prop) G.edges (fun ω => G.BondMeets ω o T) := by
  intro ω ω' h
  exact propext (exists_congr (fun y => and_congr_right (fun _ => G.bondConn_determined ω ω' h o y)))


-- @@ L113-116 verbatim
theorem siteMeets_determined (o : G.Node) (T : Set Vertex) :
    ProductCylinder.DeterminedBy (F := Prop) G.vertices (fun ω => G.SiteMeets ω o T) := by
  intro ω ω' h
  exact propext (exists_congr (fun y => and_congr_right (fun _ => G.siteConn_determined ω ω' h o y)))


-- @@ L118-142 verbatim
theorem bondConn_iff_hypergraph (ω : BondConfig) (x y : G.Node) :
    G.BondConn ω x y ↔ HyperedgeComparison.Connected G.hypergraph
      (fun e => ω e.1) ∅ x y := by
  constructor
  · intro h
    apply Relation.ReflTransGen.mono (r := G.BondAdj ω) (p := _) ?_ x y h
    intro a b hab
    obtain ⟨e,he,hxy,ho⟩ := hab
    refine ⟨⟨e,he⟩,ho,Set.disjoint_empty _,?_,?_⟩
    · rcases hxy with ⟨h,_⟩ | ⟨_,h⟩
      · exact Or.inl h
      · exact Or.inr h
    · rcases hxy with ⟨_,h⟩ | ⟨h,_⟩
      · exact Or.inr h
      · exact Or.inl h
  · intro h
    induction h with
    | refl => exact .refl
    | @tail a b _ hab ih =>
      obtain ⟨e,ho,_,ha,hb⟩ := hab
      rcases ha with ha | ha <;> rcases hb with hb | hb
      · exact (Subtype.ext (ha.trans hb.symm)) ▸ ih
      · exact ih.tail ⟨e.1,e.2,Or.inl ⟨ha,hb⟩,ho⟩
      · exact ih.tail ⟨e.1,e.2,Or.inr ⟨hb,ha⟩,ho⟩
      · exact (Subtype.ext (ha.trans hb.symm)) ▸ ih


-- @@ L144-161 verbatim
/-- Pulling the actual bond connection event down to its finite bit set. -/
theorem bondMeets_probability (p : Bond → Set.Icc (0 : ℝ) 1)
    (o : G.Node) (T : Set Vertex) :
    (ProductCylinder.law p).real {ω | G.BondMeets ω o T} =
      HyperedgeComparison.eventProb (fun e : G.edges => p e.1)
        (fun ω => HyperedgeComparison.Meets G.hypergraph ω ∅ o {y | y.1 ∈ T}) := by
  rw [Measure.real_def,ProductCylinder.probability_determined G.edges p {ω | G.BondMeets ω o T}
    (fun ω ω' h => eq_iff_iff.mp (G.bondMeets_determined o T ω ω' h))]
  rw [HyperedgeComparison.eventProb_eq_real]
  congr 1
  congr 1
  ext ξ
  change (∃ y : G.Node, y.1 ∈ T ∧ G.BondConn (ProductCylinder.extend G.edges ξ) o y) ↔ _
  simp only [G.bondConn_iff_hypergraph]
  have he : (fun e : G.edges => ProductCylinder.extend G.edges ξ e.1) = ξ := by
    funext e; simp [ProductCylinder.extend,e.2]
  rw [he]
  rfl


-- @@ L163-176 verbatim
theorem siteMeets_probability (p : Vertex → Set.Icc (0 : ℝ) 1)
    (o : G.Node) (T : Set Vertex) :
    (ProductCylinder.law p).real {ω | G.SiteMeets ω o T} =
      HyperedgeComparison.eventProb (fun x : G.Node => p x.1)
        (fun ω => HyperedgeComparison.Site.Meets G.graph ω o {y | y.1 ∈ T}) := by
  rw [Measure.real_def,ProductCylinder.probability_determined G.vertices p {ω | G.SiteMeets ω o T}
    (fun ω ω' h => eq_iff_iff.mp (G.siteMeets_determined o T ω ω' h))]
  rw [HyperedgeComparison.eventProb_eq_real]
  congr 1
  congr 1
  ext ξ
  have he : (fun x : G.Node => ProductCylinder.extend G.vertices ξ x.1) = ξ := by
    funext x; simp [ProductCylinder.extend,x.2]
  simp only [SiteMeets,SiteConn,he,HyperedgeComparison.Site.Meets,Set.mem_ofPred_eq]


-- @@ L178-203 verbatim
/-- Any observable of the finite graph's connections is a finite cylinder. -/
theorem bondObservable_probability (p : Bond → Set.Icc (0 : ℝ) 1)
    (φ : (G.Node → Set Vertex → Prop) → Prop) :
    (ProductCylinder.law p).real {ω | φ (G.BondMeets ω)} =
      HyperedgeComparison.eventProb (fun e : G.edges => p e.1)
        (fun ω => φ (fun o T => HyperedgeComparison.Meets G.hypergraph ω ∅ o {y | y.1 ∈ T})) := by
  have hd : ∀ ω ω', (∀ e ∈ G.edges, ω' e = ω e) →
      (φ (G.BondMeets ω') ↔ φ (G.BondMeets ω)) := by
    intro ω ω' he
    have hm : G.BondMeets ω' = G.BondMeets ω := by
      funext o T; exact G.bondMeets_determined o T ω ω' he
    rw [hm]
  rw [Measure.real_def,ProductCylinder.probability_determined G.edges p {ω | φ (G.BondMeets ω)} hd,
    HyperedgeComparison.eventProb_eq_real]
  congr 1
  congr 1
  ext ξ
  have he : (fun e : G.edges => ProductCylinder.extend G.edges ξ e.1) = ξ := by
    funext e; simp [ProductCylinder.extend,e.2]
  have hm : G.BondMeets (ProductCylinder.extend G.edges ξ) =
      fun o T => HyperedgeComparison.Meets G.hypergraph ξ ∅ o {y | y.1 ∈ T} := by
    funext o T
    apply propext
    simp only [BondMeets,G.bondConn_iff_hypergraph,he,
      HyperedgeComparison.Meets,Set.mem_ofPred_eq]
  simp only [Set.mem_ofPred_eq,hm]


-- @@ L205-228 verbatim
theorem siteObservable_probability (p : Vertex → Set.Icc (0 : ℝ) 1)
    (φ : (G.Node → Set Vertex → Prop) → Prop) :
    (ProductCylinder.law p).real {ω | φ (G.SiteMeets ω)} =
      HyperedgeComparison.eventProb (fun x : G.Node => p x.1)
        (fun ω => φ (fun o T => HyperedgeComparison.Site.Meets G.graph ω o {y | y.1 ∈ T})) := by
  have hd : ∀ ω ω', (∀ e ∈ G.vertices, ω' e = ω e) →
      (φ (G.SiteMeets ω') ↔ φ (G.SiteMeets ω)) := by
    intro ω ω' he
    have hm : G.SiteMeets ω' = G.SiteMeets ω := by
      funext o T; exact G.siteMeets_determined o T ω ω' he
    rw [hm]
  rw [Measure.real_def,ProductCylinder.probability_determined G.vertices p {ω | φ (G.SiteMeets ω)} hd,
    HyperedgeComparison.eventProb_eq_real]
  congr 1
  congr 1
  ext ξ
  have he : (fun x : G.Node => ProductCylinder.extend G.vertices ξ x.1) = ξ := by
    funext x; simp [ProductCylinder.extend,x.2]
  have hm : G.SiteMeets (ProductCylinder.extend G.vertices ξ) =
      fun o T => HyperedgeComparison.Site.Meets G.graph ξ o {y | y.1 ∈ T} := by
    funext o T
    apply propext
    simp only [SiteMeets,SiteConn,he,HyperedgeComparison.Site.Meets,Set.mem_ofPred_eq]
  simp only [Set.mem_ofPred_eq,hm]


-- @@ L230-240 verbatim
/-- The comparison is now attached to actual finite lattice bond paths and
arbitrary independent laws on the entire lattice, not an assumed interface. -/
theorem bond_failure_comparison (p : Bond → Set.Icc (0 : ℝ) 1)
    (o : G.Node) (A T : Set Vertex) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ a : G.Node, a.1 ∈ A →
      1-b ≤ (ProductCylinder.law p).real {ω | G.BondMeets ω a T}) :
    (ProductCylinder.law p).real {ω | G.BondMeets ω o A ∧ ¬G.BondMeets ω o T} ≤ b := by
  rw [G.bondObservable_probability p (fun M => M o A ∧ ¬M o T)]
  apply HyperedgeComparison.failure_comparison _ _ _ _ _ b hb0
  intro a ha
  simpa only [G.bondMeets_probability] using hb a ha


-- @@ L242-250 verbatim
theorem site_failure_comparison (p : Vertex → Set.Icc (0 : ℝ) 1)
    (o : G.Node) (A T : Set Vertex) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ a : G.Node, a.1 ∈ A →
      1-b ≤ (ProductCylinder.law p).real {ω | G.SiteMeets ω a T}) :
    (ProductCylinder.law p).real {ω | G.SiteMeets ω o A ∧ ¬G.SiteMeets ω o T} ≤ b := by
  rw [G.siteObservable_probability p (fun M => M o A ∧ ¬M o T)]
  apply HyperedgeComparison.site_failure_comparison _ _ _ _ _ b hb0
  intro a ha
  simpa only [G.siteMeets_probability] using hb a ha


-- @@ L252-252 verbatim
end LatticeGraph

-- @@ L253-253 verbatim
end CriticalZ3


-- @@ L255-255 verbatim
end OAI
