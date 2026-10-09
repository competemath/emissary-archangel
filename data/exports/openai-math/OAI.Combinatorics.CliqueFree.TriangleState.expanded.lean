import OAI.Combinatorics.CliqueFree.EdgeState


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators

-- @@ L8-8 verbatim
open Finset


-- @@ L10-10 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L12-12 verbatim
namespace CliqueFreeIndependence.WeightedGraph


-- @@ L14-14 verbatim
universe u v


-- @@ L16-16 verbatim
variable {V : Type u} [Fintype V]


-- @@ L18-18 verbatim
attribute [local instance 10000] edgeStateDecEq


-- @@ L20-21 verbatim
abbrev TriangleState (G : SimpleGraph V) :=
  {t : V × V × V // G.Adj t.1 t.2.1 ∧ G.Adj t.1 t.2.2 ∧ G.Adj t.2.1 t.2.2}


-- @@ L23-24 verbatim
noncomputable instance triangleStateFintype (G : SimpleGraph V) : Fintype (TriangleState G) :=
  Subtype.fintype _


-- @@ L26-26 verbatim
namespace TriangleState

-- @@ L27-27 verbatim
variable {G : SimpleGraph V}

-- @@ L28-28 verbatim
def first (t : TriangleState G) : V := t.val.1

-- @@ L29-29 verbatim
def second (t : TriangleState G) : V := t.val.2.1

-- @@ L30-30 verbatim
def third (t : TriangleState G) : V := t.val.2.2


-- @@ L32-33 verbatim
omit [Fintype V] in
@[simp] lemma adj12 (t : TriangleState G) : G.Adj t.first t.second := t.property.1

-- @@ L34-35 verbatim
omit [Fintype V] in
@[simp] lemma adj13 (t : TriangleState G) : G.Adj t.first t.third := t.property.2.1

-- @@ L36-37 verbatim
omit [Fintype V] in
@[simp] lemma adj23 (t : TriangleState G) : G.Adj t.second t.third := t.property.2.2


-- @@ L39-39 verbatim
def edge12 (t : TriangleState G) : EdgeState G := ⟨(t.first, t.second), t.adj12⟩

-- @@ L40-40 verbatim
def edge13 (t : TriangleState G) : EdgeState G := ⟨(t.first, t.third), t.adj13⟩

-- @@ L41-41 verbatim
def edge23 (t : TriangleState G) : EdgeState G := ⟨(t.second, t.third), t.adj23⟩


-- @@ L43-44 verbatim
def swap (t : TriangleState G) : TriangleState G :=
  ⟨(t.second, t.first, t.third), t.adj12.symm, t.adj23, t.adj13⟩

-- @@ L45-46 verbatim
def rotate (t : TriangleState G) : TriangleState G :=
  ⟨(t.second, t.third, t.first), t.adj23, t.adj12.symm, t.adj13.symm⟩


-- @@ L48-52 verbatim
def swapEquiv : TriangleState G ≃ TriangleState G where
  toFun := swap
  invFun := swap
  left_inv t := by cases t; rfl
  right_inv t := by cases t; rfl


-- @@ L54-58 verbatim
def rotateEquiv : TriangleState G ≃ TriangleState G where
  toFun := rotate
  invFun := rotate ∘ rotate
  left_inv t := by cases t; rfl
  right_inv t := by cases t; rfl


-- @@ L60-61 verbatim
noncomputable def weight (w : V → ℝ) (t : TriangleState G) : ℝ :=
  w t.first * w t.second * w t.third


-- @@ L63-65 verbatim
omit [Fintype V] in
lemma weight_pos {w : V → ℝ} (hw : ∀ u, 0 < w u) (t : TriangleState G) :
    0 < weight w t := mul_pos (mul_pos (hw _) (hw _)) (hw _)


-- @@ L67-69 verbatim
omit [Fintype V] in
@[simp] lemma weight_swap (w : V → ℝ) (t : TriangleState G) :
    weight w (swap t) = weight w t := by unfold weight swap first second third; ring

-- @@ L70-72 verbatim
omit [Fintype V] in
@[simp] lemma weight_rotate (w : V → ℝ) (t : TriangleState G) :
    weight w (rotate t) = weight w t := by unfold weight rotate first second third; ring


-- @@ L74-76 verbatim
lemma sum_rotate (w : V → ℝ) (f : TriangleState G → ℝ) :
    (∑ t, weight w t * f (rotate t)) = ∑ t, weight w t * f t := by
  simpa only [rotateEquiv, Equiv.coe_fn_mk, weight_rotate] using rotateEquiv.sum_comp (fun t ↦ weight w t * f t)


-- @@ L78-80 verbatim
lemma sum_swap (w : V → ℝ) (f : TriangleState G → ℝ) :
    (∑ t, weight w t * f (swap t)) = ∑ t, weight w t * f t := by
  simpa only [swapEquiv, Equiv.coe_fn_mk, weight_swap] using swapEquiv.sum_comp (fun t ↦ weight w t * f t)


-- @@ L82-101 verbatim
lemma sum_eq (f : V → V → V → ℝ) :
    (∑ t : TriangleState G, f t.first t.second t.third) =
      ∑ u, ∑ v ∈ neighbors G u, ∑ z ∈ neighbors G u,
        if G.Adj v z then f u v z else 0 := by
  classical
  change (∑ t : {t : V × V × V // _}, f t.val.1 t.val.2.1 t.val.2.2) = _
  rw [← Finset.sum_subtype (univ.filter fun t : V × V × V ↦
    G.Adj t.1 t.2.1 ∧ G.Adj t.1 t.2.2 ∧ G.Adj t.2.1 t.2.2)
    (by simp) (fun t : V × V × V ↦ f t.1 t.2.1 t.2.2)]
  simp only [sum_filter, Fintype.sum_prod_type, neighbors]
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  by_cases huv : G.Adj u v
  · simp only [huv, true_and, ↓reduceIte]
    apply sum_congr rfl
    intro z _
    by_cases huz : G.Adj u z <;> simp [huz]
  · simp [huv]


-- @@ L103-106 verbatim
lemma sum_weight (w : V → ℝ) : (∑ t : TriangleState G, weight w t) = 6 * triangleMass G w := by
  simp only [weight]
  rw [sum_eq (fun u v z ↦ w u * w v * w z), triangleMass_eq_sum]
  simp only [triangleAt, commonMass_eq_sum, mul_sum, mul_ite, mul_zero, mul_assoc]


-- @@ L108-118 verbatim
lemma marginal (w : V → ℝ) (f : V → V → ℝ) :
    (∑ t : TriangleState G, weight w t * f t.first t.second) =
      ∑ e : EdgeState G, w e.src * w e.dst * commonMass G w e.src e.dst * f e.src e.dst := by
  simp only [weight]
  rw [sum_eq (fun u v z ↦ w u * w v * w z * f u v), EdgeState.sum_eq (fun u v ↦ w u * w v * commonMass G w u v * f u v)]
  apply sum_congr rfl
  intro u _
  apply sum_congr rfl
  intro v _
  rw [commonMass_eq_sum]
  simp only [mul_sum, sum_mul, mul_ite, ite_mul, mul_zero, zero_mul]


-- @@ L120-120 verbatim
end TriangleState


-- @@ L122-122 verbatim
namespace TriangleState

-- @@ L123-123 verbatim
variable {G : SimpleGraph V}


-- @@ L125-126 verbatim
def flip (t : TriangleState G) : TriangleState G :=
  ⟨(t.first, t.third, t.second), t.adj13, t.adj12, t.adj23.symm⟩


-- @@ L128-132 verbatim
def flipEquiv : TriangleState G ≃ TriangleState G where
  toFun := flip
  invFun := flip
  left_inv t := by cases t; rfl
  right_inv t := by cases t; rfl


-- @@ L134-136 verbatim
omit [Fintype V] in
@[simp] lemma weight_flip (w : V → ℝ) (t : TriangleState G) :
    weight w (flip t) = weight w t := by unfold weight flip first second third; ring


-- @@ L138-141 verbatim
lemma sum_flip (w : V → ℝ) (f : TriangleState G → ℝ) :
    (∑ t, weight w t * f (flip t)) = ∑ t, weight w t * f t := by
  simpa only [flipEquiv, Equiv.coe_fn_mk, weight_flip] using
    flipEquiv.sum_comp (fun t ↦ weight w t * f t)


-- @@ L143-144 verbatim
abbrev CornerPairs (G : SimpleGraph V) :=
  {p : EdgeState G × EdgeState G // p.1.src = p.2.src ∧ G.Adj p.1.dst p.2.dst}


-- @@ L146-156 verbatim
def cornerEquiv : TriangleState G ≃ CornerPairs G where
  toFun t := ⟨(t.edge12, t.edge13), rfl, t.adj23⟩
  invFun p := ⟨(p.val.1.src, p.val.1.dst, p.val.2.dst), p.val.1.adj,
    by rw [p.property.1]; exact p.val.2.adj, p.property.2⟩
  left_inv t := by cases t; rfl
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact Prod.ext p.property.1 rfl


-- @@ L158-173 verbatim
lemma corner_sum (w : V → ℝ) (f : EdgeState G → EdgeState G → ℝ) :
    (∑ t : TriangleState G, weight w t * f t.edge12 t.edge13) =
      ∑ e : EdgeState G, ∑ z : EdgeState G,
        if e.src = z.src ∧ G.Adj e.dst z.dst
          then w e.src * w e.dst * w z.dst * f e z else 0 := by
  classical
  calc
    _ = ∑ p : CornerPairs G, w p.val.1.src * w p.val.1.dst * w p.val.2.dst * f p.val.1 p.val.2 :=
      (cornerEquiv.sum_comp (fun p ↦ w p.val.1.src * w p.val.1.dst * w p.val.2.dst * f p.val.1 p.val.2))
    _ = ∑ p : EdgeState G × EdgeState G,
        if p.1.src = p.2.src ∧ G.Adj p.1.dst p.2.dst
          then w p.1.src * w p.1.dst * w p.2.dst * f p.1 p.2 else 0 := by
      rw [← Finset.sum_subtype (univ.filter fun p : EdgeState G × EdgeState G ↦
          p.1.src = p.2.src ∧ G.Adj p.1.dst p.2.dst) (by simp)
        (fun p ↦ w p.1.src * w p.1.dst * w p.2.dst * f p.1 p.2), sum_filter]
    _ = _ := Fintype.sum_prod_type _


-- @@ L175-175 verbatim
end TriangleState


-- @@ L177-177 verbatim
namespace TriangleState

-- @@ L178-178 verbatim
variable {G : SimpleGraph V}

-- @@ L179-188 verbatim
lemma sum_edge_permutations (w : V → ℝ) (g : EdgeState G → ℝ) :
    (∑ t, weight w t * g t.edge12.rev) = (∑ t, weight w t * g t.edge12) ∧
    (∑ t, weight w t * g t.edge13) = (∑ t, weight w t * g t.edge12) ∧
    (∑ t, weight w t * g t.edge13.rev) = (∑ t, weight w t * g t.edge12) ∧
    (∑ t, weight w t * g t.edge23) = (∑ t, weight w t * g t.edge12) ∧
    (∑ t, weight w t * g t.edge23.rev) = (∑ t, weight w t * g t.edge12) := by
  refine ⟨sum_swap w (fun t ↦ g t.edge12), sum_flip w (fun t ↦ g t.edge12), ?_,
    sum_rotate w (fun t ↦ g t.edge12), ?_⟩
  · exact (sum_rotate w (fun t ↦ g (rotate t).edge12)).trans (sum_rotate w (fun t ↦ g t.edge12))
  · exact (sum_rotate w (fun t ↦ g (swap t).edge12)).trans (sum_swap w (fun t ↦ g t.edge12))

-- @@ L189-189 verbatim
end TriangleState


-- @@ L191-191 verbatim
end CliqueFreeIndependence.WeightedGraph


-- @@ L193-193 verbatim
end


-- @@ L195-195 verbatim
end OAI
