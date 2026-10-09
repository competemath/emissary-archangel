import OAI.GroupTheory.UniversalGroup.TorusBundles


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open Set Metric Topology BigOperators

-- @@ L8-8 verbatim
open Set Metric Topology

-- @@ L9-9 verbatim
open Set Topology

-- @@ L10-10 verbatim
open Set Metric Topology

-- @@ L11-11 verbatim
open scoped NNReal

-- @@ L12-12 verbatim
open Set Metric Topology

-- @@ L13-13 verbatim
open scoped NNReal ENNReal

-- @@ L14-14 verbatim
open Set Metric Topology

-- @@ L15-15 verbatim
open scoped TensorProduct


-- @@ L17-17 verbatim
namespace UniversalFInfinity.PathFamilies

-- @@ L18-18 verbatim
open scoped unitInterval

-- @@ L19-19 verbatim
universe u v

-- @@ L20-20 verbatim
variable {Y : Type u} [TopologicalSpace Y] {X : Type v} [TopologicalSpace X]

-- @@ L21-21 verbatim
variable {x y z : Y}


-- @@ L23-25 verbatim
def diagonalSquare (p : Path x y) (q : Path y z) : C(I × I,Y) :=
  ⟨fun s => (p.trans q).extend (((s.1:ℝ)+(s.2:ℝ))/2),
    (p.trans q).continuous_extend.comp (by fun_prop)⟩


-- @@ L27-32 verbatim
lemma diagonalSquare_zero_left (p : Path x y) (q : Path y z) (s : I) :
    diagonalSquare p q (0,s) = p s := by
  change (p.trans q).extend (((0:ℝ)+(s:ℝ))/2) = p s
  rw [Path.extend_trans_of_le_half p q (by have := s.2.2; linarith)]
  rw [show 2*(((0:ℝ)+(s:ℝ))/2) = (s:ℝ) by ring]
  exact p.extend_apply s.2

-- @@ L33-38 verbatim
lemma diagonalSquare_one_left (p : Path x y) (q : Path y z) (s : I) :
    diagonalSquare p q (1,s) = q s := by
  change (p.trans q).extend (((1:ℝ)+(s:ℝ))/2) = q s
  rw [Path.extend_trans_of_half_le p q (by have := s.2.1; linarith)]
  rw [show 2*(((1:ℝ)+(s:ℝ))/2)-1 = (s:ℝ) by ring]
  exact q.extend_apply s.2

-- @@ L39-42 verbatim
lemma diagonalSquare_symm (p : Path x y) (q : Path y z) (t s : I) :
    diagonalSquare p q (t,s) = diagonalSquare p q (s,t) := by
  change (p.trans q).extend _ = (p.trans q).extend _
  rw [add_comm (t:ℝ) (s:ℝ)]

-- @@ L43-45 verbatim
lemma diagonalSquare_zero_right (p : Path x y) (q : Path y z) (t : I) :
    diagonalSquare p q (t,0) = p t := by
  rw [diagonalSquare_symm,diagonalSquare_zero_left]

-- @@ L46-48 verbatim
lemma diagonalSquare_one_right (p : Path x y) (q : Path y z) (t : I) :
    diagonalSquare p q (t,1) = q t := by
  rw [diagonalSquare_symm,diagonalSquare_one_left]


-- @@ L50-57 verbatim
lemma diagonalSquare_continuous {a b c : X → Y}
    (p : ∀ x,Path (a x) (b x)) (q : ∀ x,Path (b x) (c x))
    (hp : Continuous (fun z : X × I => p z.1 z.2))
    (hq : Continuous (fun z : X × I => q z.1 z.2)) :
    Continuous (fun z : X × (I × I) => diagonalSquare (p z.1) (q z.1) z.2) := by
  exact (Path.continuous_uncurry_extend_of_continuous_family
    (fun x => (p x).trans (q x)) (Path.trans_continuous_family p hp q hq)).comp
      (continuous_fst.prodMk (by fun_prop))

-- @@ L58-65 verbatim
lemma diagonalSquare_continuous_params {a b c : X → Y}
    (p : ∀ x,Path (a x) (b x)) (q : ∀ x,Path (b x) (c x))
    (hp : Continuous (fun z : X × I => p z.1 z.2))
    (hq : Continuous (fun z : X × I => q z.1 z.2)) :
    Continuous (fun z : I × (I × X) => diagonalSquare (p z.2.2) (q z.2.2) (z.1,z.2.1)) := by
  have hc : Continuous (fun z : I × (I × X) => (z.2.2,(z.1,z.2.1))) :=
    continuous_snd.snd.prodMk (continuous_fst.prodMk continuous_snd.fst)
  exact (diagonalSquare_continuous p q hp hq).comp hc

-- @@ L66-66 verbatim
end UniversalFInfinity.PathFamilies


-- @@ L68-68 verbatim
namespace UniversalFInfinity.GraphBundle


-- @@ L70-70 verbatim
section

-- @@ L71-71 verbatim
open Set Topology

-- @@ L72-72 verbatim
open scoped unitInterval

-- @@ L73-73 verbatim
universe u v

-- @@ L74-74 verbatim
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]

-- @@ L75-75 verbatim
variable {A : Type v} [TopologicalSpace A]

-- @@ L76-76 verbatim
variable (τ : C → C) (F : C → C(A,A))


-- @@ L78-78 verbatim
abbrev Homogeneous := Space τ (fun _ => ContinuousMap.id A) F


-- @@ L80-86 verbatim
def shift : C(Homogeneous τ F,Homogeneous τ F) :=
  lift τ (fun _ => .id A) F
    (fun c => (vertexMap τ (fun _ => .id A) F (τ c)).comp (F c))
    (fun c => (edgeMap τ (fun _ => .id A) F (τ c)).comp
      ⟨fun z => (z.1,F c z.2),continuous_fst.prodMk ((F c).continuous.comp continuous_snd)⟩)
    (fun c x => edge_zero τ _ F (τ c) (F c x))
    (fun c x => edge_one τ _ F (τ c) (F c x))

-- @@ L87-88 verbatim
lemma shift_vertex (c : C) (x : A) :
    shift τ F (vertex τ (fun _ => .id A) F c x) = vertex τ (fun _ => .id A) F (τ c) (F c x) := rfl

-- @@ L89-91 verbatim
lemma shift_edge (c : C) (t : I) (x : A) :
    shift τ F (edge τ (fun _ => .id A) F c t x) = edge τ (fun _ => .id A) F (τ c) t (F c x) :=
  lift_edge τ _ F _ _ _ _ c (t,x)


-- @@ L93-99 verbatim
def shiftVertexHomotopy (c : C) :
    ((ContinuousMap.id _).comp (vertexMap τ (fun _ => .id A) F c)).Homotopy
      ((shift τ F).comp (vertexMap τ (fun _ => .id A) F c)) where
  toFun z := edge τ (fun _ => .id A) F c z.1 z.2
  continuous_toFun := (edgeMap τ (fun _ => .id A) F c).continuous
  map_zero_left x := edge_zero τ _ F c x
  map_one_left x := edge_one τ _ F c x


-- @@ L101-116 verbatim
omit [DiscreteTopology C] in
lemma shiftEdge_continuous (c : C) :
    Continuous (fun z : I × (I × A) =>
      PathFamilies.diagonalSquare (edgePath τ (fun _ => .id A) F c z.2.2)
        (edgePath τ (fun _ => .id A) F (τ c) (F c z.2.2)) (z.1,z.2.1)) := by
  let p : ∀ x : A, Path (vertex τ (fun _ => .id A) F c x)
      (vertex τ (fun _ => .id A) F (τ c) (F c x)) := edgePath τ (fun _ => .id A) F c
  let q : ∀ x : A, Path (vertex τ (fun _ => .id A) F (τ c) (F c x))
      (vertex τ (fun _ => .id A) F (τ (τ c)) (F (τ c) (F c x))) :=
    fun x => edgePath τ (fun _ => .id A) F (τ c) (F c x)
  have hp : Continuous (fun z : A × I => p z.1 z.2) :=
    (edgeMap τ (fun _ => .id A) F c).continuous.comp continuous_swap
  have hq : Continuous (fun z : A × I => q z.1 z.2) :=
    (edgeMap τ (fun _ => .id A) F (τ c)).continuous.comp
      (continuous_snd.prodMk ((F c).continuous.comp continuous_fst))
  exact PathFamilies.diagonalSquare_continuous_params p q hp hq


-- @@ L118-125 verbatim
def shiftEdgeHomotopy (c : C) :
    ((ContinuousMap.id _).comp (edgeMap τ (fun _ => .id A) F c)).Homotopy
      ((shift τ F).comp (edgeMap τ (fun _ => .id A) F c)) where
  toFun z := PathFamilies.diagonalSquare (edgePath τ (fun _ => .id A) F c z.2.2)
    (edgePath τ (fun _ => .id A) F (τ c) (F c z.2.2)) (z.1,z.2.1)
  continuous_toFun := shiftEdge_continuous τ F c
  map_zero_left z := PathFamilies.diagonalSquare_zero_left _ _ z.1
  map_one_left z := (PathFamilies.diagonalSquare_one_left _ _ z.1).trans (shift_edge τ F c z.1 z.2).symm


-- @@ L127-130 verbatim
def shiftHomotopy : (ContinuousMap.id (Homogeneous τ F)).Homotopy (shift τ F) :=
  homotopy τ (fun _ => .id A) F _ _ (shiftVertexHomotopy τ F) (shiftEdgeHomotopy τ F)
    (fun _ t _ => PathFamilies.diagonalSquare_zero_right _ _ t)
    (fun _ t _ => PathFamilies.diagonalSquare_one_right _ _ t)


-- @@ L132-134 verbatim
def shiftIterate : ℕ → C(Homogeneous τ F,Homogeneous τ F)
  | 0 => .id _
  | n+1 => (shift τ F).comp (shiftIterate n)

-- @@ L135-137 verbatim
def shiftIterateHomotopy : ∀ n,(ContinuousMap.id _).Homotopy (shiftIterate τ F n)
  | 0 => .refl _
  | n+1 => (shiftIterateHomotopy n).trans ((shiftHomotopy τ F).compContinuousMap (shiftIterate τ F n))

-- @@ L138-138 verbatim
end


-- @@ L140-140 verbatim
open Set Topology

-- @@ L141-141 verbatim
open scoped unitInterval

-- @@ L142-142 verbatim
universe u v

-- @@ L143-143 verbatim
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]

-- @@ L144-144 verbatim
variable {A : Type v} [TopologicalSpace A]

-- @@ L145-145 verbatim
variable (τ : C → C) (F : C → C(A,A))


-- @@ L147-149 verbatim
def forward : ℕ → C → C(A,A)
  | 0,_ => .id _
  | n+1,c => (F (τ^[n] c)).comp (forward n c)

-- @@ L150-158 verbatim
omit [TopologicalSpace C] [DiscreteTopology C] in
lemma forward_natural (n : ℕ) (c : C) (x : A) :
    forward τ F n (τ c) (F c x) = F (τ^[n] c) (forward τ F n c x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change F (τ^[n] (τ c)) (forward τ F n (τ c) (F c x)) =
      F (τ^[n+1] c) (F (τ^[n] c) (forward τ F n c x))
    rw [ih,Function.iterate_succ_apply]

-- @@ L159-167 verbatim
lemma shiftIterate_vertex (n : ℕ) (c : C) (x : A) :
    shiftIterate τ F n (vertex τ (fun _ => .id A) F c x) =
      vertex τ (fun _ => .id A) F (τ^[n] c) (forward τ F n c x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change shift τ F (shiftIterate τ F n (vertex τ (fun _ => .id A) F c x)) = _
    rw [ih,shift_vertex,Function.iterate_succ_apply']
    rfl

-- @@ L168-176 verbatim
lemma shiftIterate_edge (n : ℕ) (c : C) (t : I) (x : A) :
    shiftIterate τ F n (edge τ (fun _ => .id A) F c t x) =
      edge τ (fun _ => .id A) F (τ^[n] c) t (forward τ F n c x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change shift τ F (shiftIterate τ F n (edge τ (fun _ => .id A) F c t x)) = _
    rw [ih,shift_edge,Function.iterate_succ_apply']
    rfl

-- @@ L177-177 verbatim
end UniversalFInfinity.GraphBundle


-- @@ L179-179 verbatim
namespace UniversalFInfinity.Milnor

-- @@ L180-180 verbatim
variable {G : Type*} [Group G]


-- @@ L182-185 verbatim
lemma iterateHom_comm (f : G →* G) (n : ℕ) (g : G) : iterateHom f n (f g) = f (iterateHom f n g) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg f ih

-- @@ L186-186 verbatim
end UniversalFInfinity.Milnor


-- @@ L188-188 verbatim
namespace UniversalFInfinity.TorusGeometry

-- @@ L189-189 verbatim
open Set Topology Milnor AscendingTorus

-- @@ L190-190 verbatim
open scoped unitInterval

-- @@ L191-191 verbatim
universe u

-- @@ L192-192 verbatim
variable {U : Type u} [Group U] (f : Monoid.End U)


-- @@ L194-196 verbatim
def forwardOffset : ℕ → Coset f → U
  | 0,_ => 1
  | n+1,c => cosetOffset f ((next f)^[n] c) * f (forwardOffset n c)

-- @@ L197-213 verbatim
lemma forward_eq (n : ℕ) (c : Coset f) (x : Milnor.Space U) :
    GraphBundle.forward (next f) (transition f) n c x =
      forwardOffset f n c • Milnor.map (iterateHom f n) id Function.injective_id x := by
  induction n with
  | zero =>
    change x = 1 • Milnor.map (id : U → U) id Function.injective_id x
    rw [one_smul,Milnor.map_id]
  | succ n ih =>
    change transition f ((next f)^[n] c) (GraphBundle.forward (next f) (transition f) n c x) = _
    rw [ih,transition_apply]
    refine (congrArg (cosetOffset f ((next f)^[n] c) • ·)
      (Milnor.map_smul f (forwardOffset f n c) _)).trans ?_
    rw [←mul_smul]
    change (cosetOffset f ((next f)^[n] c) * f (forwardOffset f n c)) •
      Milnor.map f id Function.injective_id (Milnor.map (iterateHom f n) id Function.injective_id x) = _
    rw [Milnor.map_comp]
    rfl


-- @@ L215-220 verbatim
lemma forward_naturality (n : ℕ) (c : Coset f) (x : Milnor.Space U) :
    transition f ((next f)^[n] c)
      (forwardOffset f n c • Milnor.map (iterateHom f n) id Function.injective_id x) =
      forwardOffset f n (next f c) • Milnor.map (iterateHom f n) id Function.injective_id (transition f c x) := by
  rw [←forward_eq,←forward_eq]
  exact (GraphBundle.forward_natural (next f) (transition f) n c x).symm


-- @@ L222-228 verbatim
lemma stage_shift_vertex (S : Shapes U) (n : ℕ) (c : Coset f) (x : Milnor.Stage U (vertexShapes f S)) :
    GraphBundle.shiftIterate (next f) (transition f) n
      (stageFull f S (GraphBundle.vertex _ _ _ c x)) =
    vertex f ((next f)^[n] c)
      (forwardOffset f n c • Milnor.map (iterateHom f n) id Function.injective_id (Milnor.stageFull U _ x)) := by
  rw [stageFull_vertex]
  exact (GraphBundle.shiftIterate_vertex _ _ n c _).trans (congrArg (vertex f _) (forward_eq f n c _))

-- @@ L229-234 verbatim
lemma stage_shift_edge (S : Shapes U) (n : ℕ) (c : Coset f) (t : I) (x : Milnor.Stage U S) :
    GraphBundle.shiftIterate (next f) (transition f) n
      (stageFull f S (GraphBundle.edge _ _ _ c t x)) =
    GraphBundle.edge _ _ _ ((next f)^[n] c) t
      (forwardOffset f n c • Milnor.map (iterateHom f n) id Function.injective_id (Milnor.stageFull U _ x)) := by
  rw [stageFull_edge,GraphBundle.shiftIterate_edge,forward_eq]

-- @@ L235-235 verbatim
end UniversalFInfinity.TorusGeometry


-- @@ L237-237 verbatim
namespace UniversalFInfinity.DirectedGraph

-- @@ L238-238 verbatim
open Set Metric Topology Attachment

-- @@ L239-239 verbatim
open scoped unitInterval

-- @@ L240-240 verbatim
universe u v

-- @@ L241-241 verbatim
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C] (τ : C → C)


-- @@ L243-244 verbatim
def attaching (c : C) : C(Sphere 1,C) :=
  ⟨fun x => if x.1 0 = -1 then c else τ c,continuous_of_discreteTopology⟩

-- @@ L245-245 verbatim
abbrev Graph := Space (attaching τ)

-- @@ L246-246 verbatim
def vertex (c : C) : Graph τ := base _ c


-- @@ L248-251 verbatim
lemma discrete_dimension (m : ℕ) (i : RelCWComplex.cell (Set.univ : Set C) m) : m < 1 := by
  cases m with
  | zero => omega
  | succ m => exact i.elim

-- @@ L252-252 verbatim
instance graphCW [Nonempty C] : CWComplex (Set.univ : Set (Graph τ)) := layerCW _ discrete_dimension

-- @@ L253-253 verbatim
instance : T2Space (Graph τ) := t2Space _ (realSeparated_of_tychonoff (Y := C))

-- @@ L254-255 verbatim
lemma graph_dimension [Nonempty C] (m : ℕ) (i : RelCWComplex.cell (Set.univ : Set (Graph τ)) m) : m < 2 :=
  layerCW_dimensions _ discrete_dimension m i


-- @@ L257-259 verbatim
omit [DiscreteTopology C] in
lemma cell_minus (c : C) : cell (attaching τ) c (boundary 1 Cayley.minus) = vertex τ c := by
  rw [cell_boundary]; simp only [attaching,Cayley.minus,ContinuousMap.coe_mk,ite_true]; rfl

-- @@ L260-262 verbatim
omit [DiscreteTopology C] in
lemma cell_plus (c : C) : cell (attaching τ) c (boundary 1 Cayley.plus) = vertex τ (τ c) := by
  rw [cell_boundary]; norm_num [attaching,Cayley.plus,vertex]


-- @@ L264-268 verbatim
def edge (c : C) : Path (vertex τ c) (vertex τ (τ c)) where
  toFun t := cell (attaching τ) c (Cayley.edgeParam t)
  continuous_toFun := (cell _ c).continuous.comp Cayley.continuous_edgeParam
  source' := by rw [Cayley.edgeParam_zero,cell_minus]
  target' := by rw [Cayley.edgeParam_one,cell_plus]


-- @@ L270-270 verbatim
variable {Y : Type v} [TopologicalSpace Y] (f : C(Graph τ,Y)) (y : Y)

-- @@ L271-271 verbatim
variable (p : ∀ c,Path y (f (vertex τ c)))

-- @@ L272-272 verbatim
variable (hp : ∀ c,((p c).trans ((edge τ c).map f.continuous)).Homotopic (p (τ c)))


-- @@ L274-275 verbatim
def edgeSquare (c : C) : ((edge τ c).map f.continuous).toContinuousMap.Homotopy (.const _ y) :=
  (PathSquares.edgeSquare (p c) (p (τ c)) ((edge τ c).map f.continuous) (hp c)).choose

-- @@ L276-278 verbatim
omit [DiscreteTopology C] in
lemma edgeSquare_source (c : C) (t : I) : edgeSquare τ f y p hp c (t,0) = PathSquares.pauseReverse (p c) t :=
  (PathSquares.edgeSquare (p c) (p (τ c)) ((edge τ c).map f.continuous) (hp c)).choose_spec.1 t

-- @@ L279-281 verbatim
omit [DiscreteTopology C] in
lemma edgeSquare_target (c : C) (t : I) : edgeSquare τ f y p hp c (t,1) = PathSquares.pauseReverse (p (τ c)) t :=
  (PathSquares.edgeSquare (p c) (p (τ c)) ((edge τ c).map f.continuous) (hp c)).choose_spec.2 t


-- @@ L283-286 verbatim
def edgePaths (c : C) : C(Disk 1,C(I,Y)) :=
  ContinuousMap.curry ⟨fun z => edgeSquare τ f y p hp c (z.2,Cayley.edgeTime z.1),
    (edgeSquare τ f y p hp c).continuous.comp
      (continuous_snd.prodMk (Cayley.continuous_edgeTime.comp continuous_fst))⟩

-- @@ L287-287 verbatim
def vertexPaths : C(C,C(I,Y)) := ⟨fun c => PathSquares.pauseReverse (p c),continuous_of_discreteTopology⟩

-- @@ L288-298 verbatim
lemma edgePaths_boundary (c : C) (t : Sphere 1) :
    edgePaths τ f y p hp c (boundary 1 t) = vertexPaths τ f y p (attaching τ c t) := by
  obtain rfl|rfl := Cayley.sphere_one_eq t
  · apply ContinuousMap.ext; intro z
    change edgeSquare τ f y p hp c (z,Cayley.edgeTime (boundary 1 Cayley.minus)) = _
    rw [Cayley.edgeTime_minus,edgeSquare_source]
    simp only [vertexPaths,attaching,ContinuousMap.coe_mk,Cayley.minus,ite_true]
  · apply ContinuousMap.ext; intro z
    change edgeSquare τ f y p hp c (z,Cayley.edgeTime (boundary 1 Cayley.plus)) = _
    rw [Cayley.edgeTime_plus,edgeSquare_target]
    norm_num [vertexPaths,attaching,Cayley.plus]


-- @@ L300-301 verbatim
def graphPaths : C(Graph τ,C(I,Y)) :=
  lift _ (vertexPaths τ f y p) (edgePaths τ f y p hp) (edgePaths_boundary τ f y p hp)

-- @@ L302-309 verbatim
lemma graphPaths_zero (z : Graph τ) : graphPaths τ f y p hp z 0 = f z := by
  cases z with
  | inl c => exact Path.source _
  | inr z =>
    change edgeSquare τ f y p hp z.1 (0,Cayley.edgeTime (interior 1 z.2)) = _
    rw [ContinuousMap.Homotopy.apply_zero]
    change f (cell _ z.1 (Cayley.edgeParam (Cayley.edgeTime (interior 1 z.2)))) = f _
    rw [Cayley.edgeParam_time,cell_interior]

-- @@ L310-315 verbatim
lemma graphPaths_one (z : Graph τ) : graphPaths τ f y p hp z 1 = y := by
  cases z with
  | inl c => exact Path.target _
  | inr z =>
    change edgeSquare τ f y p hp z.1 (1,Cayley.edgeTime (interior 1 z.2)) = y
    exact ContinuousMap.Homotopy.apply_one _ _


-- @@ L317-321 verbatim
def graphNullhomotopy : f.Homotopy (.const _ y) where
  toFun z := graphPaths τ f y p hp z.2 z.1
  continuous_toFun := (graphPaths τ f y p hp).uncurry.continuous.comp continuous_swap
  map_zero_left := graphPaths_zero τ f y p hp
  map_one_left := graphPaths_one τ f y p hp


-- @@ L323-323 verbatim
end UniversalFInfinity.DirectedGraph


-- @@ L325-325 verbatim
namespace UniversalFInfinity.DirectedTree

-- @@ L326-326 verbatim
universe u v

-- @@ L327-327 verbatim
variable {C : Type u} {G : Type v} [Group G]

-- @@ L328-328 verbatim
variable (τ : C → C) (h : C → ℤ) (hτ : ∀ c, h (τ c) = h c + 1)


-- @@ L330-334 verbatim
include hτ in
lemma height_iterate (c : C) (n : ℕ) : h (τ^[n] c) = h c + n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply',hτ,ih]; push_cast; omega


-- @@ L336-336 verbatim
variable (w : C → G)

-- @@ L337-339 verbatim
def rayProduct (c : C) : ℕ → G
  | 0 => 1
  | n+1 => rayProduct c n * w (τ^[n] c)


-- @@ L341-349 verbatim
lemma rayProduct_add (c : C) (n k : ℕ) :
    rayProduct τ w c (n+k) = rayProduct τ w c n * rayProduct τ w (τ^[n] c) k := by
  induction k with
  | zero => simp [rayProduct]
  | succ k ih =>
    rw [Nat.add_succ,rayProduct,ih,rayProduct,mul_assoc]
    congr 2
    rw [Function.iterate_add_apply]
    exact congrArg w ((Function.Commute.iterate_iterate (Function.Commute.refl τ) n k).eq c)


-- @@ L351-354 verbatim
lemma rayProduct_first (c : C) (n : ℕ) :
    rayProduct τ w c (n+1) = w c * rayProduct τ w (τ c) n := by
  simpa only [Nat.add_comm 1 n,rayProduct,Function.iterate_zero,Function.id_def,one_mul,
    Function.iterate_one] using rayProduct_add τ w c 1 n


-- @@ L356-373 verbatim
include h hτ in

lemma route_independent (c d : C) (p q p' q' : ℕ)
    (he : τ^[p] c = τ^[q] d) (he' : τ^[p'] c = τ^[q'] d) :
    rayProduct τ w c p * (rayProduct τ w d q)⁻¹ =
      rayProduct τ w c p' * (rayProduct τ w d q')⁻¹ := by
  have hlen : (p:ℤ) + q' = (p':ℤ) + q := by
    have ha := congrArg h he
    have hb := congrArg h he'
    rw [height_iterate τ h hτ,height_iterate τ h hτ] at ha hb
    omega
  have hlen' : p + q' = p' + q := by omega
  have enlarge (a b : C) (i j k : ℕ) (hab : τ^[i] a = τ^[j] b) :
      rayProduct τ w a i * (rayProduct τ w b j)⁻¹ =
      rayProduct τ w a (i+k) * (rayProduct τ w b (j+k))⁻¹ := by
    rw [rayProduct_add,rayProduct_add,hab,mul_inv_rev]
    group
  rw [enlarge c d p q q' he,enlarge c d p' q' q he',hlen',Nat.add_comm q' q]


-- @@ L375-375 verbatim
variable (hc : ∀ c d, ∃ p q : ℕ, τ^[p] c = τ^[q] d) (root : C)

-- @@ L376-379 verbatim
def potential (c : C) : G :=
  let p := (hc root c).choose
  let q := (hc root c).choose_spec.choose
  rayProduct τ w root p * (rayProduct τ w c q)⁻¹


-- @@ L381-384 verbatim
include h hτ in
lemma potential_route (c : C) (p q : ℕ) (he : τ^[p] root = τ^[q] c) :
    potential τ w hc root c = rayProduct τ w root p * (rayProduct τ w c q)⁻¹ := by
  exact route_independent τ h hτ w root c _ _ p q (hc root c).choose_spec.choose_spec he


-- @@ L386-393 verbatim
include h hτ in

lemma potential_edge (c : C) : potential τ w hc root c * w c = potential τ w hc root (τ c) := by
  obtain ⟨p,q,he⟩ := hc root (τ c)
  have he' : τ^[p] root = τ^[q+1] c := by simpa only [Function.iterate_succ_apply] using he
  rw [potential_route τ h hτ w hc root c p (q+1) he',
    potential_route τ h hτ w hc root (τ c) p q he,rayProduct_first]
  group


-- @@ L395-395 verbatim
end UniversalFInfinity.DirectedTree


-- @@ L397-397 verbatim
namespace UniversalFInfinity.DirectedGraph

-- @@ L398-398 verbatim
open Set Topology Attachment

-- @@ L399-399 verbatim
open scoped unitInterval

-- @@ L400-400 verbatim
universe u

-- @@ L401-401 verbatim
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C] (τ : C → C)

-- @@ L402-402 verbatim
variable (h : C → ℤ) (hτ : ∀ c, h (τ c) = h c + 1)

-- @@ L403-403 verbatim
variable (hc : ∀ c d, ∃ p q : ℕ, τ^[p] c = τ^[q] d) (root : C)


-- @@ L405-411 verbatim
omit [DiscreteTopology C] in
lemma ray_joined (c : C) (n : ℕ) : Joined (vertex τ c) (vertex τ (τ^[n] c)) := by
  induction n with
  | zero => exact Joined.refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans ⟨edge τ (τ^[n] c)⟩


-- @@ L413-419 verbatim
include hc in
omit [DiscreteTopology C] in
lemma vertex_joined (c : C) : Joined (vertex τ root) (vertex τ c) := by
  obtain ⟨p,q,he⟩ := hc root c
  have hd : Joined (vertex τ c) (vertex τ (τ^[p] root)) := by
    rw [he]; exact ray_joined τ c q
  exact (ray_joined τ root p).trans hd.symm


-- @@ L421-422 verbatim
def initialPath (c : C) : Path (vertex τ root) (vertex τ c) :=
  (vertex_joined τ hc root c).somePath


-- @@ L424-425 verbatim
def initialClass (c : C) : Path.Homotopic.Quotient (vertex τ root) (vertex τ c) :=
  Path.Homotopic.Quotient.mk (initialPath τ hc root c)


-- @@ L427-428 verbatim
def edgeClass (c : C) : Path.Homotopic.Quotient (vertex τ c) (vertex τ (τ c)) :=
  Path.Homotopic.Quotient.mk (edge τ c)


-- @@ L430-432 verbatim
def edgeWeight (c : C) : (FundamentalGroup (Graph τ) (vertex τ root))ᵐᵒᵖ :=
  MulOpposite.op (((initialClass τ hc root c).trans (edgeClass τ c)).trans
    (initialClass τ hc root (τ c)).symm)


-- @@ L434-436 verbatim
def treeClass (c : C) : Path.Homotopic.Quotient (vertex τ root) (vertex τ c) :=
  (MulOpposite.unop (DirectedTree.potential τ (edgeWeight τ hc root) hc root c)).trans
    (initialClass τ hc root c)


-- @@ L438-448 verbatim
include h hτ in
omit [DiscreteTopology C] in
lemma treeClass_edge (c : C) : (treeClass τ hc root c).trans (edgeClass τ c) =
    treeClass τ hc root (τ c) := by
  have he := DirectedTree.potential_edge τ h hτ (edgeWeight τ hc root) hc root c
  have he' := congrArg MulOpposite.unop he
  simp only [MulOpposite.unop_mul,FundamentalGroup.mul_def,edgeWeight,MulOpposite.unop_op] at he'
  have hh := congrArg (fun (k : FundamentalGroup (Graph τ) (vertex τ root)) =>
    k.trans (initialClass τ hc root (τ c))) he'
  simpa only [treeClass,Path.Homotopic.Quotient.trans_assoc,
    Path.Homotopic.Quotient.symm_trans,Path.Homotopic.Quotient.trans_refl] using hh


-- @@ L450-451 verbatim
def treePath (c : C) : Path (vertex τ root) (vertex τ c) :=
  (Path.Homotopic.Quotient.mk_surjective (treeClass τ hc root c)).choose


-- @@ L453-462 verbatim
include h hτ in
omit [DiscreteTopology C] in
lemma treePath_edge (c : C) : ((treePath τ hc root c).trans (edge τ c)).Homotopic
    (treePath τ hc root (τ c)) := by
  apply Path.Homotopic.Quotient.exact
  change (Path.Homotopic.Quotient.mk (treePath τ hc root c)).trans (edgeClass τ c) = _
  unfold treePath
  rw [(Path.Homotopic.Quotient.mk_surjective (treeClass τ hc root c)).choose_spec,
    (Path.Homotopic.Quotient.mk_surjective (treeClass τ hc root (τ c))).choose_spec]
  exact treeClass_edge τ h hτ hc root c


-- @@ L464-471 verbatim
include hτ hc root in

lemma tree_contractible : ContractibleSpace (Graph τ) := by
  apply (contractible_iff_id_nullhomotopic _).mpr
  refine ⟨vertex τ root,⟨graphNullhomotopy τ (.id _) (vertex τ root)
    (treePath τ hc root) ?_⟩⟩
  intro c
  simpa only [ContinuousMap.coe_id,Path.map_id] using treePath_edge τ h hτ hc root c

-- @@ L472-472 verbatim
end UniversalFInfinity.DirectedGraph


-- @@ L474-474 verbatim
namespace UniversalFInfinity.GraphBundle


-- @@ L476-476 verbatim
section

-- @@ L477-477 verbatim
open Set Topology

-- @@ L478-478 verbatim
open scoped unitInterval

-- @@ L479-479 verbatim
universe u v w z

-- @@ L480-480 verbatim
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]

-- @@ L481-481 verbatim
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]

-- @@ L482-482 verbatim
variable (τ : C → C) (L R : C → C(B,A))

-- @@ L483-483 verbatim
variable {Y : Type z} [TopologicalSpace Y]


-- @@ L485-489 verbatim
def treeProjection : C(Space τ L R,DirectedGraph.Graph τ) :=
  lift τ L R (fun c => .const _ (DirectedGraph.vertex τ c))
    (fun c => (DirectedGraph.edge τ c).toContinuousMap.comp (.fst))
    (fun c _ => (DirectedGraph.edge τ c).source)
    (fun c _ => (DirectedGraph.edge τ c).target)

-- @@ L490-491 verbatim
lemma treeProjection_vertex (c : C) (x : A) :
    treeProjection τ L R (vertex τ L R c x) = DirectedGraph.vertex τ c := rfl

-- @@ L492-494 verbatim
lemma treeProjection_edge (c : C) (t : I) (x : B) :
    treeProjection τ L R (edge τ L R c t x) = DirectedGraph.edge τ c t :=
  lift_edge τ L R _ _ _ _ c (t,x)


-- @@ L496-504 verbatim
omit [DiscreteTopology C] in
lemma pathMap_boundary (y : C → Y) (p : ∀ c,Path (y c) (y (τ c))) (c : C)
    (x : Attachment.Sphere 1) :
    p c (Cayley.edgeTime (Attachment.boundary 1 x)) = y (DirectedGraph.attaching τ c x) := by
  obtain rfl|rfl := Cayley.sphere_one_eq x
  · rw [Cayley.edgeTime_minus,Path.source]
    simp only [DirectedGraph.attaching,Cayley.minus,ContinuousMap.coe_mk,ite_true]
  · rw [Cayley.edgeTime_plus,Path.target]
    norm_num [DirectedGraph.attaching,Cayley.plus]


-- @@ L506-509 verbatim
def treePathMap (y : C → Y) (p : ∀ c,Path (y c) (y (τ c))) : C(DirectedGraph.Graph τ,Y) :=
  Attachment.lift _ ⟨y,continuous_of_discreteTopology⟩
    (fun c => (p c).toContinuousMap.comp ⟨Cayley.edgeTime,Cayley.continuous_edgeTime⟩)
    (pathMap_boundary τ y p)

-- @@ L510-511 verbatim
lemma treePathMap_vertex (y : C → Y) (p : ∀ c,Path (y c) (y (τ c))) (c : C) :
    treePathMap τ y p (DirectedGraph.vertex τ c) = y c := rfl

-- @@ L512-517 verbatim
lemma treePathMap_edge (y : C → Y) (p : ∀ c,Path (y c) (y (τ c))) (c : C) (t : I) :
    treePathMap τ y p (DirectedGraph.edge τ c t) = p c t := by
  change Attachment.lift _ _ _ _ (Attachment.cell _ c (Cayley.edgeParam t)) = _
  rw [Attachment.lift_cell]
  change p c (Cayley.edgeTime (Cayley.edgeParam t)) = p c t
  rw [Cayley.edgeTime_param]


-- @@ L519-533 verbatim
lemma nullhomotopic_of_fiber_constant (h : C → ℤ) (hτ : ∀ c,h (τ c) = h c+1)
    (hc : ∀ c d,∃ m n : ℕ,τ^[m] c = τ^[n] d) (root : C)
    (f : C(Space τ L R,Y)) (y : C → Y) (p : ∀ c,Path (y c) (y (τ c)))
    (hv : ∀ c x,f (vertex τ L R c x) = y c)
    (he : ∀ c t x,f (edge τ L R c t x) = p c t) : f.Nullhomotopic := by
  have := DirectedGraph.tree_contractible τ h hτ hc root
  have hf : f = (treePathMap τ y p).comp (treeProjection τ L R) := by
    apply hom_ext τ L R
    · intro c x
      simpa only [ContinuousMap.comp_apply,treeProjection_vertex,treePathMap_vertex] using hv c x
    · intro c z
      simpa only [ContinuousMap.comp_apply,treeProjection_edge,treePathMap_edge] using he c z.1 z.2
  rw [hf]
  have hn := (id_nullhomotopic (DirectedGraph.Graph τ)).comp_right (treePathMap τ y p)
  exact hn.comp_left (treeProjection τ L R)

-- @@ L534-534 verbatim
end


-- @@ L536-536 verbatim
open Set Topology

-- @@ L537-537 verbatim
open scoped unitInterval

-- @@ L538-538 verbatim
universe u v w z r

-- @@ L539-539 verbatim
variable {C : Type u} [TopologicalSpace C] [DiscreteTopology C]

-- @@ L540-540 verbatim
variable {A : Type v} [TopologicalSpace A] {B : Type w} [TopologicalSpace B]

-- @@ L541-541 verbatim
variable (τ : C → C) (L R : C → C(B,A))

-- @@ L542-542 verbatim
variable {Y : Type z} [TopologicalSpace Y] {Z : Type r} [TopologicalSpace Z]

-- @@ L543-543 verbatim
variable (f : C(Space τ L R,Y)) (y : C → Y)

-- @@ L544-544 verbatim
variable (V : ∀ c,(f.comp (vertexMap τ L R c)).Homotopy (.const _ (y c)))

-- @@ L545-545 verbatim
variable (a b : C → C(Z,Y)) (e : ∀ c z,Path (a c z) (b c z))

-- @@ L546-546 verbatim
variable (he : ∀ c,Continuous (fun p : Z × I => e c p.1 p.2))

-- @@ L547-547 verbatim
variable (H : C → C(I × B,Z))

-- @@ L548-548 verbatim
variable (Q : C → C(B,C(I,C(I,Y))))

-- @@ L549-549 verbatim
variable (hleft : ∀ c t x,a c (H c (t,x)) = V c (t,L c x))

-- @@ L550-550 verbatim
variable (qleft : ∀ c x t,Q c x t 0 = b c (H c (t,x)))

-- @@ L551-551 verbatim
variable (qright : ∀ c x t,Q c x t 1 = V (τ c) (t,R c x))


-- @@ L553-558 verbatim
def connectorPath (c : C) (p : I × B) :
    Path (b c (H c p)) (V (τ c) (p.1,R c p.2)) where
  toFun s := Q c p.2 p.1 s
  continuous_toFun := (Q c p.2 p.1).continuous
  source' := qleft c p.2 p.1
  target' := qright c p.2 p.1


-- @@ L560-565 verbatim
omit [DiscreteTopology C] in
lemma connectorPath_continuous (c : C) : Continuous (fun p : (I × B) × I =>
    connectorPath τ L R f y V b H Q qleft qright c p.1 p.2) := by
  change Continuous (fun p : (I × B) × I => Q c p.1.2 p.1.1 p.2)
  exact (Q c).uncurry.uncurry.continuous.comp
    ((continuous_fst.snd.prodMk continuous_fst.fst).prodMk continuous_snd)


-- @@ L567-568 verbatim
def gluedPath (c : C) (p : I × B) : Path (a c (H c p)) (V (τ c) (p.1,R c p.2)) :=
  (e c (H c p)).trans (connectorPath τ L R f y V b H Q qleft qright c p)


-- @@ L570-577 verbatim
include he in
omit [DiscreteTopology C] in
lemma gluedPath_continuous (c : C) : Continuous (fun p : (I × B) × I =>
    gluedPath τ L R f y V a b e H Q qleft qright c p.1 p.2) := by
  exact Path.trans_continuous_family (fun z : I × B => e c (H c z))
    ((he c).comp (((H c).continuous.comp continuous_fst).prodMk continuous_snd))
    (connectorPath τ L R f y V b H Q qleft qright c)
    (connectorPath_continuous τ L R f y V b H Q qleft qright c)


-- @@ L579-579 verbatim
variable (e0 : ∀ c x s,e c (H c (0,x)) s = f (edge τ L R c s x))

-- @@ L580-580 verbatim
variable (q0 : ∀ c x s,Q c x 0 s = f (vertex τ L R (τ c) (R c x)))

-- @@ L581-581 verbatim
variable (p : ∀ c,Path (y c) (y (τ c)))

-- @@ L582-582 verbatim
variable (e1 : ∀ c x s,gluedPath τ L R f y V a b e H Q qleft qright c (1,x) s = p c s)


-- @@ L584-594 verbatim
include e0 q0 in
lemma gluedPath_zero (c : C) (x : B) (s : I) :
    gluedPath τ L R f y V a b e H Q qleft qright c (0,x) s =
      f (pause τ L R (edge τ L R c s x)) := by
  rw [pause_edge τ L R c (s,x)]
  change ((e c (H c (0,x))).trans (connectorPath τ L R f y V b H Q qleft qright c (0,x))) s =
    f ((edgePath τ L R c x).trans (Path.refl _) s)
  rw [Path.trans_apply,Path.trans_apply]
  split_ifs with hs
  · exact e0 c x _
  · exact q0 c x _


-- @@ L596-599 verbatim
def collapsed : C(Space τ L R,Y) :=
  lift τ L R (fun c => .const _ (y c))
    (fun c => (p c).toContinuousMap.comp .fst)
    (fun c _ => (p c).source) (fun c _ => (p c).target)


-- @@ L601-603 verbatim
lemma collapsed_edge (c : C) (s : I) (x : B) :
    collapsed τ L R y p (edge τ L R c s x) = p c s :=
  lift_edge τ L R _ _ _ _ c (s,x)


-- @@ L605-612 verbatim
def gluedEdgeHomotopy (c : C) :
    ((f.comp (pause τ L R)).comp (edgeMap τ L R c)).Homotopy
      ((collapsed τ L R y p).comp (edgeMap τ L R c)) where
  toFun z := gluedPath τ L R f y V a b e H Q qleft qright c (z.1,z.2.2) z.2.1
  continuous_toFun := (gluedPath_continuous τ L R f y V a b e he H Q qleft qright c).comp
    ((continuous_fst.prodMk continuous_snd.snd).prodMk continuous_snd.fst)
  map_zero_left z := gluedPath_zero τ L R f y V a b e H Q qleft qright e0 q0 c z.2 z.1
  map_one_left z := (e1 c z.2 z.1).trans (collapsed_edge τ L R y p c z.1 z.2).symm


-- @@ L614-616 verbatim
def gluedVertexHomotopy (c : C) :
    ((f.comp (pause τ L R)).comp (vertexMap τ L R c)).Homotopy
      ((collapsed τ L R y p).comp (vertexMap τ L R c)) := V c


-- @@ L618-622 verbatim
def coherentHomotopy : (f.comp (pause τ L R)).Homotopy (collapsed τ L R y p) :=
  homotopy τ L R _ _ (gluedVertexHomotopy τ L R f y V p)
    (gluedEdgeHomotopy τ L R f y V a b e he H Q qleft qright e0 q0 p e1)
    (fun c t x => ((gluedPath τ L R f y V a b e H Q qleft qright c (t,x)).source).trans (hleft c t x))
    (fun c t x => (gluedPath τ L R f y V a b e H Q qleft qright c (t,x)).target)


-- @@ L624-635 verbatim
include he hleft e0 q0 e1 in

theorem nullhomotopic_of_coherent_contraction
    (height : C → ℤ) (hτ : ∀ c,height (τ c) = height c+1)
    (hc : ∀ c d,∃ m n : ℕ,τ^[m] c = τ^[n] d) (root : C) : f.Nullhomotopic := by
  have hn := nullhomotopic_of_fiber_constant τ L R height hτ hc root
    (collapsed τ L R y p) y p (fun _ _ => rfl) (collapsed_edge τ L R y p)
  obtain ⟨z,⟨K⟩⟩ := hn
  refine ⟨z,⟨?_⟩⟩
  have J := coherentHomotopy τ L R f y V a b e he H Q hleft qleft qright e0 q0 p e1
  have P := (ContinuousMap.Homotopy.refl f).comp (pauseHomotopy τ L R)
  exact P.symm.trans (J.trans K)

-- @@ L636-636 verbatim
end UniversalFInfinity.GraphBundle


-- @@ L638-638 verbatim
end


-- @@ L640-640 verbatim
end OAI
