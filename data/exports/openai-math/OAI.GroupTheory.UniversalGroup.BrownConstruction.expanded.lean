import OAI.GroupTheory.UniversalGroup.TowerCoverings


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
namespace UniversalFInfinity.Brown


-- @@ L19-19 verbatim
section

-- @@ L20-20 verbatim
open Set Metric Topology Cellular Attachment

-- @@ L21-21 verbatim
universe u

-- @@ L22-22 verbatim
variable (G : Type u) [Group G]


-- @@ L24-47 verbatim
structure Stage (n : ℕ) where
  E : Type u
  B : Type u
  [topE : TopologicalSpace E]
  [topB : TopologicalSpace B]
  [nonemptyE : Nonempty E]
  [nonemptyB : Nonempty B]
  sepE : RealSeparated E
  sepB : RealSeparated B
  [cwE : CWComplex (univ : Set E)]
  [cwB : CWComplex (univ : Set B)]
  [action : MulAction G E]
  [continuousAction : ContinuousConstSMul G E]
  orbits : ℕ → Type u
  orbitFinite : ∀ m,Finite (orbits m)
  equiv : ∀ m,(G × orbits m) ≃ cwE.cell m
  equiv_map : ∀ m (g h : G) (i : orbits m) (x : Fin m → ℝ),
    cwE.map m (equiv m (g*h,i)) x = g • cwE.map m (equiv m (h,i)) x
  dimE : ∀ m (_ : cwE.cell m), m ≤ n
  dimB : ∀ m (_ : cwB.cell m), m ≤ n
  finiteB : ∀ m,Finite (cwB.cell m)
  fill : LowFillable E n
  p : C(E,B)
  covering : IsQuotientCoveringMap p G


-- @@ L49-50 verbatim
attribute [instance] Stage.topE Stage.topB Stage.nonemptyE Stage.nonemptyB
  Stage.cwE Stage.cwB Stage.action Stage.continuousAction Stage.orbitFinite Stage.finiteB


-- @@ L52-52 verbatim
instance {n : ℕ} (S : Stage G n) : T2Space S.E := S.sepE.t2Space

-- @@ L53-53 verbatim
instance {n : ℕ} (S : Stage G n) : T2Space S.B := S.sepB.t2Space


-- @@ L55-55 verbatim
variable {G}


-- @@ L57-59 verbatim
def ZeroOrbits : ℕ → Type u
  | 0 => PUnit
  | _+1 => PEmpty

-- @@ L60-60 verbatim
instance (m : ℕ) : Finite (ZeroOrbits.{u} m) := by cases m <;> dsimp [ZeroOrbits] <;> infer_instance


-- @@ L62-62 verbatim
section Zero

-- @@ L63-63 verbatim
variable [TopologicalSpace G] [DiscreteTopology G]

-- @@ L64-73 verbatim
def zeroEquiv (m : ℕ) : (G × ZeroOrbits.{u} m) ≃ RelCWComplex.cell (univ : Set G) m := by
  cases m with
  | zero =>
    exact { toFun := fun p => ⟨p.1,trivial⟩
            invFun := fun p => (p.1,PUnit.unit)
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
  | succ m =>
    change (G × PEmpty.{u+1}) ≃ PEmpty
    exact Equiv.equivOfIsEmpty _ _

-- @@ L74-78 verbatim
lemma zeroEquiv_map (m : ℕ) (g h : G) (i : ZeroOrbits.{u} m) (x : Fin m → ℝ) :
    RelCWComplex.map m (zeroEquiv m (g*h,i)) x = g • RelCWComplex.map m (zeroEquiv m (h,i)) x := by
  cases m with
  | zero => rfl
  | succ m => exact i.elim

-- @@ L79-83 verbatim
lemma discrete_dim {X : Type u} [TopologicalSpace X] [DiscreteTopology X]
    (m : ℕ) (i : RelCWComplex.cell (univ : Set X) m) : m ≤ 0 := by
  cases m with
  | zero => exact le_rfl
  | succ m => exact i.elim


-- @@ L85-85 verbatim
def pointCover : C(G,PUnit.{u+1}) := .const _ PUnit.unit

-- @@ L86-101 verbatim
lemma pointCover_quotient : IsQuotientCoveringMap (pointCover (G := G)) G where
  __ := show IsQuotientMap (pointCover (G := G)) from
    (show IsOpenMap (pointCover (G := G)) from fun _ _ => isOpen_discrete _).isQuotientMap
      (by fun_prop) (fun _ => ⟨1,rfl⟩)
  __ := (inferInstance : ContinuousConstSMul G G)
  apply_eq_iff_mem_orbit := by
    intro x y
    constructor
    · intro _; exact ⟨x*y⁻¹,by simp [smul_eq_mul]⟩
    · intro _; rfl
  disjoint x := by
    refine ⟨{x},(isOpen_discrete _).mem_nhds (Set.mem_singleton x),?_⟩
    rintro g ⟨z,⟨y,hy,rfl⟩,h⟩
    simp only [Set.mem_singleton_iff] at hy h
    rw [hy] at h
    exact mul_right_cancel (show g*x=1*x by simpa only [smul_eq_mul,one_mul] using h)


-- @@ L103-136 verbatim
def zeroStage : Stage G 0 where
  E := G
  B := PUnit.{u+1}
  topE := inferInstance
  topB := inferInstance
  nonemptyE := inferInstance
  nonemptyB := inferInstance
  sepE := realSeparated_of_tychonoff
  sepB := realSeparated_of_tychonoff
  cwE := inferInstance
  cwB := inferInstance
  action := inferInstance
  continuousAction := inferInstance
  orbits := ZeroOrbits
  orbitFinite := inferInstance
  equiv := zeroEquiv
  equiv_map := zeroEquiv_map
  dimE := discrete_dim
  dimB := discrete_dim
  finiteB m := by
    cases m with
    | zero =>
      change Finite (univ : Set PUnit.{u+1})
      infer_instance
    | succ m =>
      change Finite PEmpty
      infer_instance
  fill m hm a := by
    have hm : m = 0 := Nat.eq_zero_of_le_zero hm
    subst m
    obtain ⟨e,he⟩ := SphereTopology.fill_zero a
    exact ⟨e,he⟩
  p := pointCover
  covering := pointCover_quotient

-- @@ L137-137 verbatim
end Zero


-- @@ L139-140 verbatim
variable (hunif : ∀ S : Milnor.Shapes G, ∃ (T : Milnor.Shapes G) (hST : S ⊆ T),
      (Milnor.stageIncl G S T hST).Nullhomotopic)

-- @@ L141-141 verbatim
variable {n : ℕ} (S : Stage G n)


-- @@ L143-143 verbatim
def nextIndex : Type u := (exists_finite_brown_attachment S.equiv S.equiv_map hunif n S.fill S.dimE S.sepE).choose

-- @@ L144-145 verbatim
instance : Finite (nextIndex hunif S) :=
  (exists_finite_brown_attachment S.equiv S.equiv_map hunif n S.fill S.dimE S.sepE).choose_spec.choose


-- @@ L147-148 verbatim
def attaching : nextIndex hunif S → C(Cellular.Sphere (n+1),S.E) :=
  (exists_finite_brown_attachment S.equiv S.equiv_map hunif n S.fill S.dimE S.sepE).choose_spec.choose_spec.choose

-- @@ L149-150 verbatim
lemma attaching_fill : LowFillable (Space (equivariantFamily (G := G) (attaching hunif S))) (n+1) :=
  (exists_finite_brown_attachment S.equiv S.equiv_map hunif n S.fill S.dimE S.sepE).choose_spec.choose_spec.choose_spec


-- @@ L152-152 verbatim
def downstairs (i : nextIndex hunif S) : C(Cellular.Sphere (n+1),S.B) := S.p.comp (attaching hunif S i)


-- @@ L154-155 verbatim
instance nextE_nonempty : Nonempty (Space (equivariantFamily (G := G) (attaching hunif S))) :=
  ⟨base _ (Classical.choice S.nonemptyE)⟩

-- @@ L156-156 verbatim
instance nextB_nonempty : Nonempty (Space (downstairs hunif S)) := ⟨base _ (Classical.choice S.nonemptyB)⟩

-- @@ L157-158 verbatim
instance nextE_t2 : T2Space (Space (equivariantFamily (G := G) (attaching hunif S))) :=
  (realSeparated _ S.sepE).t2Space

-- @@ L159-159 verbatim
instance nextB_t2 : T2Space (Space (downstairs hunif S)) := (realSeparated _ S.sepB).t2Space


-- @@ L161-183 verbatim
def nextStage : Stage G (n+1) where
  E := Space (equivariantFamily (G := G) (attaching hunif S))
  B := Space (downstairs hunif S)
  topE := inferInstance
  topB := inferInstance
  nonemptyE := inferInstance
  nonemptyB := inferInstance
  sepE := realSeparated _ S.sepE
  sepB := realSeparated _ S.sepB
  cwE := equivariantLayerCW S.equiv S.equiv_map (attaching hunif S) (fun m i => Nat.lt_succ_of_le (S.dimE m i))
  cwB := layerCW (downstairs hunif S) (fun m i => Nat.lt_succ_of_le (S.dimB m i))
  action := inferInstance
  continuousAction := inferInstance
  orbits := LayerOrbits (ι := S.orbits) (I := nextIndex hunif S) (n := n+1)
  orbitFinite m := by dsimp [LayerOrbits]; infer_instance
  equiv _ := Equiv.refl _
  equiv_map := equivariantLayerCW_smul S.equiv S.equiv_map (attaching hunif S) _
  dimE m i := Nat.le_of_lt_succ (equivariantLayerCW_dims S.equiv S.equiv_map (attaching hunif S) _ m i)
  dimB m i := Nat.le_of_lt_succ (layerCW_dimensions (downstairs hunif S) _ m i)
  finiteB := layerCW_finite_cells (downstairs hunif S) S.finiteB _
  fill := attaching_fill hunif S
  p := coverMap (attaching hunif S) S.p S.covering (downstairs hunif S) (fun _ _ => rfl)
  covering := coverMap_isQuotientCovering _ _ _ _ _

-- @@ L184-184 verbatim
end


-- @@ L186-186 verbatim
section

-- @@ L187-187 verbatim
open Set Metric Topology Cellular Attachment

-- @@ L188-188 verbatim
universe u

-- @@ L189-189 verbatim
variable {G : Type u} [Group G]

-- @@ L190-191 verbatim
variable (hunif : ∀ S : Milnor.Shapes G, ∃ (T : Milnor.Shapes G) (hST : S ⊆ T),
      (Milnor.stageIncl G S T hST).Nullhomotopic)

-- @@ L192-192 verbatim
variable {n : ℕ} (S : Stage G n)


-- @@ L194-194 verbatim
def nextInE : C(S.E,(nextStage hunif S).E) := ⟨base _,continuous_base _⟩

-- @@ L195-195 verbatim
def nextInB : C(S.B,(nextStage hunif S).B) := ⟨base _,continuous_base _⟩

-- @@ L196-196 verbatim
lemma nextInE_closed : IsClosedEmbedding (nextInE hunif S) := base_closedEmbedding _

-- @@ L197-197 verbatim
lemma nextInB_closed : IsClosedEmbedding (nextInB hunif S) := base_closedEmbedding _

-- @@ L198-198 verbatim
lemma nextInE_smul (g : G) (x : S.E) : nextInE hunif S (g • x) = g • nextInE hunif S x := rfl

-- @@ L199-200 verbatim
lemma next_square (x : S.E) :
    (nextStage hunif S).p (nextInE hunif S x) = nextInB hunif S (S.p x) := rfl


-- @@ L202-203 verbatim
def nextCellE (m : ℕ) : S.cwE.cell m → (nextStage hunif S).cwE.cell m :=
  layerOld S.equiv S.equiv_map (attaching hunif S) _ m

-- @@ L204-205 verbatim
lemma nextCellE_injective (m : ℕ) : Function.Injective (nextCellE hunif S m) :=
  layerOld_injective _ _ _ _ m

-- @@ L206-207 verbatim
lemma nextCellE_exhaustive (m : ℕ) (hm : m ≠ n+1) (i : (nextStage hunif S).cwE.cell m) :
    ∃ j,nextCellE hunif S m j = i := layerOld_exhaustive _ _ _ _ m hm i

-- @@ L208-210 verbatim
lemma nextCellE_map (m : ℕ) (i : S.cwE.cell m) (x : Fin m → ℝ) :
    nextInE hunif S (S.cwE.map m i x) = (nextStage hunif S).cwE.map m (nextCellE hunif S m i) x :=
  (layerOld_map _ _ _ _ m i x).symm


-- @@ L212-212 verbatim
def nextCellB (m : ℕ) : S.cwB.cell m → (nextStage hunif S).cwB.cell m := Sum.inl

-- @@ L213-213 verbatim
lemma nextCellB_injective (m : ℕ) : Function.Injective (nextCellB hunif S m) := Sum.inl_injective

-- @@ L214-218 verbatim
lemma nextCellB_exhaustive (m : ℕ) (hm : m ≠ n+1) (i : (nextStage hunif S).cwB.cell m) :
    ∃ j,nextCellB hunif S m j = i := by
  cases i with
  | inl i => exact ⟨i,rfl⟩
  | inr i => exact (hm i.down.1.down).elim

-- @@ L219-220 verbatim
lemma nextCellB_map (m : ℕ) (i : S.cwB.cell m) (x : Fin m → ℝ) :
    nextInB hunif S (S.cwB.map m i x) = (nextStage hunif S).cwB.map m (nextCellB hunif S m i) x := rfl


-- @@ L222-223 verbatim
lemma nextE_extendsReal (f : C(S.E,ℝ)) : ∃ F : C((nextStage hunif S).E,ℝ),
    ∀ x,F (nextInE hunif S x) = f x := exists_real_extension _ f

-- @@ L224-225 verbatim
lemma nextB_extendsReal (f : C(S.B,ℝ)) : ∃ F : C((nextStage hunif S).B,ℝ),
    ∀ x,F (nextInB hunif S x) = f x := exists_real_extension _ f

-- @@ L226-231 verbatim
lemma nextE_extendsSlice (U : Set S.E) (hU : IsOpen U)
    (hd : ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1) :
    ∃ V : Set (nextStage hunif S).E, IsOpen V ∧ (nextInE hunif S) ⁻¹' V = U ∧
      ∀ g : G,((g • ·) '' V ∩ V).Nonempty → g = 1 :=
  ⟨thickening _ U,thickening_isOpen _ hU,rfl,
    thickening_disjoint _ (equivariantFamily_smul (attaching hunif S)) hd⟩

-- @@ L232-232 verbatim
end


-- @@ L234-234 verbatim
open Set Metric Topology Cellular Attachment

-- @@ L235-235 verbatim
universe u

-- @@ L236-236 verbatim
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]

-- @@ L237-238 verbatim
variable (hunif : ∀ S : Milnor.Shapes G, ∃ (T : Milnor.Shapes G) (hST : S ⊆ T),
      (Milnor.stageIncl G S T hST).Nullhomotopic)


-- @@ L240-242 verbatim
def stages : (n : ℕ) → Stage G n
  | 0 => zeroStage
  | n+1 => nextStage hunif (stages n)

-- @@ L243-243 verbatim
abbrev E (n : ℕ) := (stages hunif n).E

-- @@ L244-244 verbatim
abbrev B (n : ℕ) := (stages hunif n).B


-- @@ L246-246 verbatim
def eStep (n : ℕ) : C(E hunif n,E hunif (n+1)) := nextInE hunif (stages hunif n)

-- @@ L247-247 verbatim
def bStep (n : ℕ) : C(B hunif n,B hunif (n+1)) := nextInB hunif (stages hunif n)

-- @@ L248-248 verbatim
abbrev eMap := Sequential.map (E hunif) (eStep hunif)

-- @@ L249-249 verbatim
abbrev bMap := Sequential.map (B hunif) (bStep hunif)

-- @@ L250-251 verbatim
lemma eMap_closed : ∀ i j h,IsClosedEmbedding (eMap hunif i j h) :=
  Sequential.map_closedEmbedding _ _ (fun n => nextInE_closed hunif (stages hunif n))

-- @@ L252-253 verbatim
lemma bMap_closed : ∀ i j h,IsClosedEmbedding (bMap hunif i j h) :=
  Sequential.map_closedEmbedding _ _ (fun n => nextInB_closed hunif (stages hunif n))


-- @@ L255-263 verbatim
instance : TopologicalTower.EquivariantSystem (G := G) (E hunif) (eMap hunif) where
  map_smul i j h g x := by
    induction j,h using Nat.le_induction with
    | base => simp only [eMap,Sequential.map_self,ContinuousMap.id_apply]
    | succ j h ih =>
      simp only [eMap,Sequential.map_succ _ _ i j h,ContinuousMap.comp_apply]
      change eStep hunif j (eMap hunif i j h (g • x)) = g • eStep hunif j (eMap hunif i j h x)
      rw [ih]
      exact nextInE_smul hunif (stages hunif j) g _


-- @@ L265-270 verbatim
def eCells : Sequential.CellSteps (E hunif) (eStep hunif) where
  cell n := nextCellE hunif (stages hunif n)
  injective n := nextCellE_injective hunif (stages hunif n)
  dim n := (stages hunif n).dimE
  exhaustive n := nextCellE_exhaustive hunif (stages hunif n)
  compatibility n := nextCellE_map hunif (stages hunif n)

-- @@ L271-276 verbatim
def bCells : Sequential.CellSteps (B hunif) (bStep hunif) where
  cell n := nextCellB hunif (stages hunif n)
  injective n := nextCellB_injective hunif (stages hunif n)
  dim n := (stages hunif n).dimB
  exhaustive n := nextCellB_exhaustive hunif (stages hunif n)
  compatibility n := nextCellB_map hunif (stages hunif n)


-- @@ L278-278 verbatim
abbrev Total := TopologicalTower.Space (E hunif) (eMap hunif)

-- @@ L279-279 verbatim
abbrev Base := TopologicalTower.Space (B hunif) (bMap hunif)

-- @@ L280-280 verbatim
instance : Nonempty (Total hunif) := ⟨TopologicalTower.of (E hunif) (eMap hunif) 0 (1:G)⟩

-- @@ L281-281 verbatim
instance : Nonempty (Base hunif) := ⟨TopologicalTower.of (B hunif) (bMap hunif) 0 PUnit.unit⟩


-- @@ L283-289 verbatim
lemma e_extendsReal : TopologicalTower.ExtendsReals (E hunif) (eMap hunif) := by
  intro n f
  obtain ⟨extension, hextension⟩ := nextE_extendsReal hunif (stages hunif n) f
  refine ⟨extension, ?_⟩
  intro point
  rw [eMap, Sequential.map_step]
  exact hextension point

-- @@ L290-296 verbatim
lemma b_extendsReal : TopologicalTower.ExtendsReals (B hunif) (bMap hunif) := by
  intro n f
  obtain ⟨extension, hextension⟩ := nextB_extendsReal hunif (stages hunif n) f
  refine ⟨extension, ?_⟩
  intro point
  rw [bMap, Sequential.map_step]
  exact hextension point

-- @@ L297-298 verbatim
instance totalT2 : T2Space (Total hunif) :=
  TopologicalTower.t2Space _ _ (eMap_closed hunif) (e_extendsReal hunif) (fun n => (stages hunif n).sepE)

-- @@ L299-300 verbatim
instance baseT2 : T2Space (Base hunif) :=
  TopologicalTower.t2Space _ _ (bMap_closed hunif) (b_extendsReal hunif) (fun n => (stages hunif n).sepB)

-- @@ L301-302 verbatim
instance totalCW : CWComplex (univ : Set (Total hunif)) :=
  CellularTower.cwComplex _ _ (eMap_closed hunif) (Sequential.cellSystem _ _ (eCells hunif))

-- @@ L303-304 verbatim
instance baseCW : CWComplex (univ : Set (Base hunif)) :=
  CellularTower.cwComplex _ _ (bMap_closed hunif) (Sequential.cellSystem _ _ (bCells hunif))

-- @@ L305-306 verbatim
lemma base_finite (n : ℕ) : Finite ((baseCW hunif).cell n) :=
  (stages hunif n).finiteB n


-- @@ L308-313 verbatim
lemma eventually_fills : TopologicalTower.EventuallyFills (E hunif) (eMap hunif) := by
  intro n k a
  let j := max n k
  obtain ⟨F,hF⟩ := (stages hunif j).fill n (le_max_left n k)
    ((eMap hunif k j (le_max_right n k)).comp a)
  exact ⟨j,le_max_right n k,F,hF⟩

-- @@ L314-315 verbatim
instance totalContractible : ContractibleSpace (Total hunif) :=
  TopologicalTower.contractible _ _ (eMap_closed hunif) (eventually_fills hunif)


-- @@ L317-322 verbatim
lemma e_extendsSlices : TopologicalTower.ExtendsSlices (G := G) (E hunif) (eMap hunif) := by
  intro n U
  obtain ⟨V,hV,hpre,hdis⟩ := nextE_extendsSlice hunif (stages hunif n) U.carrier U.isOpen U.disjoint
  refine ⟨⟨V,hV,hdis⟩,?_⟩
  rw [eMap, Sequential.map_step]
  exact hpre


-- @@ L324-324 verbatim
def pStage (n : ℕ) : C(E hunif n,B hunif n) := (stages hunif n).p

-- @@ L325-332 verbatim
lemma p_compat (i j : ℕ) (h : i ≤ j) (x : E hunif i) :
    pStage hunif j (eMap hunif i j h x) = bMap hunif i j h (pStage hunif i x) := by
  induction j,h using Nat.le_induction with
  | base => simp only [eMap,bMap,Sequential.map_self,ContinuousMap.id_apply]
  | succ j h ih =>
    simp only [eMap,bMap,Sequential.map_succ _ _ i j h,ContinuousMap.comp_apply]
    change pStage hunif (j+1) (eStep hunif j (eMap hunif i j h x)) = bStep hunif j (bMap hunif i j h (pStage hunif i x))
    exact (next_square hunif (stages hunif j) _).trans (congrArg (bStep hunif j) ih)


-- @@ L334-335 verbatim
def pLimit : C(Total hunif,Base hunif) :=
  TopologicalTower.limitMap _ _ _ _ (pStage hunif) (p_compat hunif)

-- @@ L336-338 verbatim
lemma pLimit_covering : IsQuotientCoveringMap (pLimit hunif) G :=
  TopologicalTower.limitMap_isQuotientCovering _ _ _ _ (pStage hunif) (p_compat hunif)
    (eMap_closed hunif) (bMap_closed hunif) (fun n => (stages hunif n).covering) (e_extendsSlices hunif)


-- @@ L340-341 verbatim
instance baseConnected : ConnectedSpace (Base hunif) :=
  (pLimit_covering hunif).surjective.connectedSpace (pLimit hunif).continuous


-- @@ L343-351 verbatim
include hunif in

theorem geometric_of_uniform : HasTypeFInfinity G := by
  refine ⟨Base hunif,inferInstance,inferInstance,inferInstance,baseCW hunif,base_finite hunif,?_,?_⟩
  · let e : Total hunif := Classical.choice inferInstance
    refine ⟨pLimit hunif e,⟨?_⟩⟩
    exact ((pLimit_covering hunif).fundamentalGroupEquiv ⟨e,rfl⟩).trans (MulEquiv.inv' G).symm
  · exact ⟨Total hunif,inferInstance,inferInstance,pLimit hunif,
      (pLimit_covering hunif).surjective,(pLimit_covering hunif).isCoveringMap⟩

-- @@ L352-352 verbatim
end UniversalFInfinity.Brown


-- @@ L354-354 verbatim
end


-- @@ L356-356 verbatim
end OAI
