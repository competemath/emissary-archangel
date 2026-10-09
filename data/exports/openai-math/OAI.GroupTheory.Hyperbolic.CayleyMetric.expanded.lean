import OAI.GroupTheory.Hyperbolic.ThinTriangles


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace Release075.Discrete

-- @@ L6-6 verbatim
variable {V : Type} (X : SimpleGraph V) (hX : X.Connected)


-- @@ L8-12 verbatim
noncomputable def graphMetric : Metric V where
  dist := X.dist
  self _ := X.dist_self
  symm _ _ := X.dist_comm
  triangle _ _ _ := hX.dist_triangle


-- @@ L14-21 verbatim
noncomputable def walkPath {a b : V} (p : X.Walk a b) : Path (graphMetric X hX) a b where
  length := p.length
  point := p.getVert
  zero := p.getVert_zero
  stable _ h := p.getVert_of_length_le h
  step _ h := by
    change X.dist _ _ ≤ 1
    exact (X.dist_eq_one_iff_adj.mpr (p.adj_getVert_succ h)).le


-- @@ L23-32 verbatim
@[simp] theorem walkPath_mem {a b x : V} (p : X.Walk a b) :
    (walkPath X hX p).Mem x ↔ x ∈ p.support := by
  classical
  constructor
  · rintro ⟨i,_,rfl⟩
    exact p.getVert_mem_support i
  · intro hx
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
    refine ⟨i,by change i ≤ p.length; rw [p.length_support] at hi; omega,?_⟩
    exact (p.getVert_eq_support_getElem (by rw [p.length_support] at hi; omega)).trans he


-- @@ L34-37 verbatim
theorem graphMetric_geodesicSpace : GeodesicSpace (graphMetric X hX) := by
  intro a b
  obtain ⟨p,hp⟩ := hX.exists_walk_length_eq_dist a b
  exact ⟨walkPath X hX p,hp⟩


-- @@ L39-39 verbatim
end Release075.Discrete


-- @@ L41-41 verbatim
namespace Release075.BlockPresentation

-- @@ L42-42 verbatim
variable {I B : Type} {r : ℕ} (d : BlockPresentation I B r)


-- @@ L44-44 verbatim
abbrev cayley : SimpleGraph d.GroupType := SimpleGraph.mulCayley (Set.range d.edge)

-- @@ L45-46 verbatim
noncomputable abbrev cayleyMetric : Discrete.Metric d.GroupType :=
  Discrete.graphMetric d.cayley d.cayley_connected


-- @@ L48-62 verbatim
theorem cayley_dist_mul (g : d.GroupType) (e : d.OrientedEdge) :
    d.cayleyMetric.dist g (g*d.edgeValue e) ≤ 1 := by
  by_cases he : g = g*d.edgeValue e
  · rw [←he]
    exact (d.cayleyMetric.self g).le.trans (by omega)
  · suffices d.cayley.Adj g (g*d.edgeValue e) by
      exact (d.cayley.dist_eq_one_iff_adj.mpr this).le
    apply (SimpleGraph.mulCayley_adj' _ _ _).mpr
    refine ⟨he,d.edge e.1,⟨e.1,rfl⟩,?_⟩
    rcases e with ⟨e,s⟩
    cases s
    · right
      simp [edgeValue]
    · left
      simp [edgeValue]


-- @@ L64-67 verbatim
theorem cayley_dist_liftedEdge (e : d.LiftedEdge) :
    d.cayleyMetric.dist (d.liftedFlip e).2 e.2 ≤ 1 := by
  have h := d.cayley_dist_mul (e.2*(d.edgeValue e.1)⁻¹) e.1
  simpa only [inv_mul_cancel_right,liftedFlip] using h


-- @@ L69-70 verbatim
noncomputable def liftedForm (o a : d.GroupType) (T : ℕ) (e : d.LiftedEdge) : ℤ :=
  d.cayleyMetric.form o a T (d.liftedFlip e).2 e.2


-- @@ L72-75 verbatim
theorem liftedForm_flip (o a : d.GroupType) (T : ℕ) (e : d.LiftedEdge) :
    d.liftedForm o a T (d.liftedFlip e) = -d.liftedForm o a T e := by
  rw [liftedForm,d.liftedFlip_flip,Discrete.Metric.form_flip]
  rfl


-- @@ L77-93 verbatim
theorem liftedForm_face_bound (o z : d.GroupType) (T : ℕ)
    {a b c : d.LiftedEdge} (hf : d.LiftedFace a b c) :
    |d.liftedForm o z T a+d.liftedForm o z T b+d.liftedForm o z T c| ≤ 2 := by
  have hab := congrArg Prod.snd hf.2.1
  have hbc := congrArg Prod.snd hf.2.2.1
  have hca := congrArg Prod.snd hf.2.2.2
  change (d.liftedFlip b).2 = a.2 at hab
  change (d.liftedFlip c).2 = b.2 at hbc
  change (d.liftedFlip a).2 = c.2 at hca
  have ha := d.cayley_dist_liftedEdge a
  have hb := d.cayley_dist_liftedEdge b
  have hc := d.cayley_dist_liftedEdge c
  rw [hca] at ha
  rw [hab] at hb
  rw [hbc] at hc
  simpa only [liftedForm,hab,hbc,hca] using
    d.cayleyMetric.form_triangle_bound o z c.2 a.2 b.2 T ha hb hc


-- @@ L95-95 verbatim
end Release075.BlockPresentation


-- @@ L97-97 verbatim
namespace Release075.TriangleFilling

-- @@ L98-98 verbatim
variable {E V : Type} {flip : E → E} {color : E → V} {face : E → E → E → Prop}


-- @@ L100-124 verbatim
/-- Bounded triangular coboundary gives a bound on every actual disk boundary. -/
theorem edge_sum_bound {w : List E} (D : TriangleFilling flip color face w)
    (F : E → ℤ) (hflip : ∀ e, F (flip e) = -F e)
    (hface : ∀ a b c, face a b c → |F a+F b+F c| ≤ 2) :
    |(w.map F).sum| ≤ 2*D.activeCount := by
  classical
  have hcyc := D.full.trace_cyclic_sum (fun a ha => (D.full_triangular a ha).1)
    (fun a _ _ => F a)
  rw [D.full.trace_edge F hflip] at hcyc
  have hcard : Fintype.card D.full.Dart = D.activeCount := Fintype.card_subtype _
  have hbound : |D.full.trace (fun a b c => F a+F b+F c)| ≤ 2*D.activeCount := by
    unfold FullFilling.trace
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ _a : D.full.Dart, (2:ℤ) := by
        apply Finset.sum_le_sum
        intro a _
        split_ifs with ha
        · norm_num
        · exact hface _ _ _ (D.full_triangular a ha).2.2
      _ = 2*D.activeCount := by simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul]; ring
  rw [hcyc] at hbound
  norm_num only [nsmul_eq_mul,abs_mul,abs_neg] at hbound
  have hn := abs_nonneg ((w.map F).sum)
  omega


-- @@ L126-126 verbatim
end Release075.TriangleFilling


-- @@ L128-128 verbatim
namespace Release075.MarkedLineData

-- @@ L129-129 verbatim
variable {q r : ℕ} [Fact q.Prime] (d : MarkedLineData q r) (hr : 0 < r)


-- @@ L131-140 verbatim
theorem liftedForm_loop_bound {x : (d.presentation hr).LiftedVertex}
    {w : List (d.presentation hr).LiftedEdge}
    (hw : WordPath (d.presentation hr).liftedFlip (d.presentation hr).liftedTarget x x w)
    (o a : (d.presentation hr).GroupType) (T : ℕ) :
    |(w.map ((d.presentation hr).liftedForm o a T)).sum| ≤ 38*w.length := by
  obtain ⟨D,hD⟩ := d.exists_lifted_linear_filling hr ((d.presentation hr).lifted_closed_fillable hw)
  have h := D.edge_sum_bound ((d.presentation hr).liftedForm o a T)
    ((d.presentation hr).liftedForm_flip o a T)
    (fun _ _ _ hf => (d.presentation hr).liftedForm_face_bound o a T hf)
  omega


-- @@ L142-142 verbatim
end Release075.MarkedLineData


-- @@ L144-144 verbatim
end OAI
