import OAI.GroupTheory.UniversalGroup.CellRetractions


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


-- @@ L13-13 verbatim
open Set Metric Topology

-- @@ L14-14 verbatim
open scoped NNReal ENNReal

-- @@ L15-15 verbatim
namespace UniversalFInfinity.GeneralPosition


-- @@ L17-27 verbatim
lemma lipschitz_insertNth {n : ℕ} (i : Fin (n+1)) (c : ℝ) :
    LipschitzWith 1 (Fin.insertNth (α := fun _ : Fin (n+1) => ℝ) i c : (Fin n → ℝ) → (Fin (n+1) → ℝ)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [NNReal.coe_one,one_mul]
  rw [dist_pi_le_iff dist_nonneg]
  intro j
  refine Fin.succAboveCases i ?_ (fun k => ?_) j
  · simp only [Fin.insertNth_apply_same,dist_self,dist_nonneg]
  · simp only [Fin.insertNth_apply_succAbove]
    exact dist_le_pi_dist x y k


-- @@ L29-43 verbatim
lemma sphere_subset_faces (n : ℕ) :
    Metric.sphere (0 : Fin (n+1) → ℝ) 1 ⊆
      ⋃ i : Fin (n+1), ⋃ c ∈ ({1,-1}:Set ℝ), Set.range (Fin.insertNth (α := fun _ : Fin (n+1) => ℝ) i c : (Fin n → ℝ) → _) := by
  intro x hx
  have hxnorm : ‖x‖ = 1 := by simpa only [Metric.mem_sphere,dist_zero_right] using hx
  have hi : ∃ i, 1 ≤ ‖x i‖ := by
    by_contra! hh
    have := (pi_norm_lt_iff (by norm_num : (0:ℝ)<1)).mpr hh
    linarith
  obtain ⟨i,hi⟩ := hi
  have heq : |x i| = 1 := le_antisymm ((norm_le_pi_norm x i).trans_eq hxnorm) hi
  have hc : x i ∈ ({1,-1}:Set ℝ) := by
    rcases abs_eq (by norm_num : (0:ℝ)≤1) |>.mp heq with h | h <;> simp [h]
  refine Set.mem_iUnion.mpr ⟨i,Set.mem_iUnion.mpr ⟨x i,Set.mem_iUnion.mpr ⟨hc,?_⟩⟩⟩
  exact ⟨fun j => x (i.succAbove j),Fin.insertNth_self_removeNth _ _⟩


-- @@ L45-56 verbatim
lemma dimH_cube_boundary_le (n : ℕ) :
    dimH (Metric.sphere (0 : Fin (n+1) → ℝ) 1) ≤ n := by
  apply (dimH_mono (sphere_subset_faces n)).trans
  rw [dimH_iUnion]
  apply iSup_le
  intro i
  rw [dimH_bUnion (Set.toFinite ({1,-1}:Set ℝ)).countable]
  apply iSup_le
  intro c
  apply iSup_le
  intro _
  exact (lipschitz_insertNth i c).dimH_range_le.trans_eq (Real.dimH_univ_pi_fin n)


-- @@ L58-61 verbatim
lemma dimH_cube_boundary_subtype_le (n : ℕ) :
    dimH (Set.univ : Set (Metric.sphere (0 : Fin (n+1) → ℝ) 1)) ≤ n := by
  rw [← isometry_subtype_coe.dimH_image]
  simpa only [Subtype.range_coe_subtype,Set.image_univ,Set.ofPred_mem_eq] using dimH_cube_boundary_le n


-- @@ L63-63 verbatim
end UniversalFInfinity.GeneralPosition


-- @@ L65-65 verbatim
namespace UniversalFInfinity.Attachment


-- @@ L67-67 verbatim
section

-- @@ L68-68 verbatim
open Set Metric Topology

-- @@ L69-69 verbatim
variable {X : Type*} [TopologicalSpace X] {ι : Type*} {n : ℕ}

-- @@ L70-70 verbatim
variable (a : ι → C(Sphere n,X)) [T2Space (Space a)]


-- @@ L72-83 verbatim
lemma sphere_filling_preserved {m : ℕ} (hm : m < n)
    (hX : ∀ f : C(Sphere (m+1),X), SphereTopology.Extends f)
    (f : C(Sphere (m+1),Space a)) : SphereTopology.Extends f := by
  let := SphereTopology.sphere_nonempty m
  have hdim : dimH (Set.univ : Set (Sphere (m+1))) < n :=
    (GeneralPosition.dimH_cube_boundary_subtype_le m).trans_lt (by exact_mod_cast hm)
  obtain ⟨g,H,_⟩ := exists_deformation_into_base a f hdim
  apply SphereTopology.extends_of_homotopy H
  obtain ⟨F,hF⟩ := hX g
  refine ⟨(⟨base a,continuous_base a⟩ : C(X,Space a)).comp F,?_⟩
  ext x
  exact congrArg (base a) (ContinuousMap.congr_fun hF x)


-- @@ L85-88 verbatim
lemma dimH_disk_subtype_le (m : ℕ) : dimH (Set.univ : Set (Disk m)) ≤ m := by
  rw [← isometry_subtype_coe.dimH_image]
  have hm := dimH_mono (Set.subset_univ (closedBall (0 : Fin m → ℝ) 1))
  simpa only [Set.image_univ,Subtype.range_coe_subtype,Set.ofPred_mem_eq,Real.dimH_univ_pi_fin] using hm


-- @@ L90-102 verbatim
lemma filling_reflected {m : ℕ} (hm : m < n) (b : C(Sphere m,X))
    (hb : SphereTopology.Extends ((⟨base a,continuous_base a⟩ : C(X,Space a)).comp b)) :
    SphereTopology.Extends b := by
  obtain ⟨F,hF⟩ := hb
  have hdim : dimH (Set.univ : Set (Disk m)) < n :=
    (dimH_disk_subtype_le m).trans_lt (by exact_mod_cast hm)
  obtain ⟨g,H,hstat⟩ := exists_deformation_into_base a F hdim
  refine ⟨g,?_⟩
  ext x
  apply (base_closedEmbedding a).injective
  have hb' : F (SphereTopology.boundary m x) = base a (b x) := ContinuousMap.congr_fun hF x
  have hh := hstat 1 (SphereTopology.boundary m x) ⟨b x,hb'.symm⟩
  simpa only [ContinuousMap.Homotopy.apply_one,ContinuousMap.comp_apply,ContinuousMap.coe_mk,hb'] using hh


-- @@ L104-104 verbatim
end

-- @@ L105-105 verbatim
open Set Metric Topology

-- @@ L106-106 verbatim
variable {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]

-- @@ L107-107 verbatim
variable {ι : Type*} {n : ℕ} (a : ι → C(Sphere n,X)) [Nonempty (Sphere n)]

-- @@ L108-120 verbatim
lemma pathConnectedSpace : PathConnectedSpace (Space a) := by
  let x₀ : X := Classical.choice inferInstance
  let s₀ : Sphere n := Classical.choice inferInstance
  have hj : ∀ z : Space a, Joined (base a x₀) z := by
    intro z
    cases z with
    | inl x => exact (PathConnectedSpace.joined x₀ x).map (continuous_base a)
    | inr p =>
      have h : Joined (boundary n s₀) (interior n p.2) := PathConnectedSpace.joined _ _
      have hh := h.map (cell a p.1).continuous
      rw [cell_interior,cell_boundary] at hh
      exact ((PathConnectedSpace.joined x₀ (a p.1 s₀)).map (continuous_base a)).trans hh
  exact ⟨⟨base a x₀⟩,fun x y => (hj x).symm.trans (hj y)⟩

-- @@ L121-121 verbatim
end UniversalFInfinity.Attachment


-- @@ L123-123 verbatim
namespace UniversalFInfinity.Cayley

-- @@ L124-124 verbatim
open Set Metric Topology Attachment

-- @@ L125-125 verbatim
universe u

-- @@ L126-126 verbatim
variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]

-- @@ L127-127 verbatim
variable {S : Type u} (s : S → G) (rels : Set (FreeGroup S))

-- @@ L128-128 verbatim
variable (hrel : ∀ r ∈ rels, FreeGroup.lift s r = 1)

-- @@ L129-129 verbatim
variable (hs : Function.Surjective (FreeGroup.lift s))

-- @@ L130-130 verbatim
variable (hker : (FreeGroup.lift s).ker = Subgroup.normalClosure rels)


-- @@ L132-133 verbatim
instance presentationCoverT2 : T2Space (PresentationCover s rels hrel) :=
  t2Space _ (realSeparated _ (realSeparated_of_tychonoff (Y := G)))


-- @@ L135-136 verbatim
instance presentationCoverCW : CWComplex (Set.univ : Set (PresentationCover s rels hrel)) :=
  layerCW _ (graph_dimension s)


-- @@ L138-145 verbatim
include hs in
lemma presentationCover_pathConnected : PathConnectedSpace (PresentationCover s rels hrel) := by
  have hgen : Subgroup.closure (Set.range s) = ⊤ := by
    rw [←FreeGroup.range_lift_eq_closure,MonoidHom.range_eq_top]
    exact hs
  let := graph_pathConnected s hgen
  let := SphereTopology.sphere_nonempty 1
  exact Attachment.pathConnectedSpace _


-- @@ L147-155 verbatim
include hs hker in
lemma presentationCover_sphereFill (b : C(Sphere 2,PresentationCover s rels hrel)) : SphereTopology.Extends b := by
  let := SphereTopology.sphere_nonempty 1
  have hdim : dimH (Set.univ : Set (Sphere 2)) < 2 :=
    (GeneralPosition.dimH_cube_boundary_subtype_le 1).trans_lt (by norm_num)
  obtain ⟨g,H,_⟩ := exists_deformation_into_base _ b hdim
  apply SphereTopology.extends_of_homotopy H
  exact SphereTopology.extends_of_nullhomotopic
    (((presentationGraphNullhomotopy s rels hrel hs hker).compContinuousMap g).symm)


-- @@ L157-165 verbatim
include hs hker in
lemma presentationCover_simplyConnected : SimplyConnectedSpace (PresentationCover s rels hrel) := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨presentationCover_pathConnected s rels hrel hs,?_⟩
  intro x p
  obtain ⟨F,hF⟩ := presentationCover_sphereFill s rels hrel hs hker (LoopSphere.map p)
  apply LoopSphere.homotopic_of_fill p F
  intro z
  exact ContinuousMap.congr_fun hF z

-- @@ L166-166 verbatim
end UniversalFInfinity.Cayley


-- @@ L168-168 verbatim
namespace UniversalFInfinity

-- @@ L169-169 verbatim
universe u v

-- @@ L170-170 verbatim
variable {G : Type u} [Group G] {A : Type v} [MulAction G A]


-- @@ L172-172 verbatim
abbrev Orbits := Quotient (MulAction.orbitRel G A)


-- @@ L174-176 verbatim
lemma orbit_mk_smul (g : G) (a : A) : (Quotient.mk'' (g • a) : Orbits (G := G) (A := A)) = Quotient.mk'' a := by
  apply Quotient.sound
  exact ⟨g,rfl⟩


-- @@ L178-182 verbatim
lemma orbit_out_translate (a : A) : ∃ g : G, a = g • (Quotient.mk'' a : Orbits (G := G)).out := by
  have h := Quotient.exact (Quotient.out_eq' (q := (Quotient.mk'' a : Orbits (G := G))))
  obtain ⟨g,hg⟩ := h
  refine ⟨g⁻¹,?_⟩
  rw [←hg,inv_smul_smul]


-- @@ L184-184 verbatim
variable (hfree : ∀ (g : G) (a : A), g • a = a → g = 1)


-- @@ L186-201 verbatim
include hfree in
lemma orbitCoordinates_bijective : Function.Bijective (fun p : G × Orbits (G := G) (A := A) => p.1 • p.2.out) := by
  constructor
  · rintro ⟨g,q⟩ ⟨h,r⟩ he
    have hqr : q = r := by
      have hh := congrArg (fun a : A => (Quotient.mk'' a : Orbits (G := G))) he
      simpa only [orbit_mk_smul,Quotient.out_eq'] using hh
    subst r
    change g • q.out = h • q.out at he
    have hh : (h⁻¹*g) • q.out = q.out := by rw [mul_smul,he,inv_smul_smul]
    have hh := hfree (h⁻¹*g) q.out hh
    have hgh : g = h := (inv_mul_eq_one.mp hh).symm
    exact Prod.ext hgh rfl
  · intro a
    obtain ⟨g,hg⟩ := orbit_out_translate (G := G) a
    exact ⟨(g,Quotient.mk'' a),hg.symm⟩


-- @@ L203-204 verbatim
def orbitCoordinates : (G × Orbits (G := G) (A := A)) ≃ A :=
  Equiv.ofBijective _ (orbitCoordinates_bijective hfree)


-- @@ L206-207 verbatim
lemma orbitCoordinates_apply (g : G) (q : Orbits (G := G) (A := A)) :
    orbitCoordinates hfree (g,q) = g • q.out := rfl


-- @@ L209-209 verbatim
end UniversalFInfinity


-- @@ L211-211 verbatim
open Set Metric Topology

-- @@ L212-212 verbatim
namespace UniversalFInfinity.Cellular

-- @@ L213-213 verbatim
universe u

-- @@ L214-215 verbatim
variable {G : Type u} [Group G] {X : Type u} [TopologicalSpace X]
  [MulAction G X] [ContinuousConstSMul G X]

-- @@ L216-216 verbatim
variable [CWComplex (univ : Set X)] {ι : ℕ → Type u}

-- @@ L217-217 verbatim
variable (σ : ∀ n, (G × ι n) ≃ RelCWComplex.cell (univ : Set X) n)


-- @@ L219-220 verbatim
def actionChart (n : ℕ) (i : G × ι n) : PartialEquiv (Fin n → ℝ) X :=
  (RelCWComplex.map n (σ n (1,i.2))).trans (Homeomorph.smul i.1).toEquiv.toPartialEquiv


-- @@ L222-223 verbatim
lemma actionChart_apply (n : ℕ) (i : G × ι n) (x : Fin n → ℝ) :
    actionChart σ n i x = i.1 • RelCWComplex.map n (σ n (1,i.2)) x := rfl


-- @@ L225-227 verbatim
lemma actionChart_image (n : ℕ) (i : G × ι n) (A : Set (Fin n → ℝ)) :
    actionChart σ n i '' A = (fun x : X => i.1 • x) '' (RelCWComplex.map n (σ n (1,i.2)) '' A) :=
  Set.image_comp (fun x : X => i.1 • x) (RelCWComplex.map n (σ n (1,i.2))) A


-- @@ L229-231 verbatim
lemma actionChart_source (n : ℕ) (i : G × ι n) :
    (actionChart σ n i).source = ball 0 1 := by
  simp [actionChart,PartialEquiv.trans_source,RelCWComplex.source_eq]


-- @@ L233-235 verbatim
lemma actionChart_continuousOn (n : ℕ) (i : G × ι n) :
    ContinuousOn (actionChart σ n i) (closedBall 0 1) :=
  (continuous_const_smul i.1).comp_continuousOn (RelCWComplex.continuousOn _ _)


-- @@ L237-242 verbatim
lemma actionChart_continuousOn_symm (n : ℕ) (i : G × ι n) :
    ContinuousOn (actionChart σ n i).symm (actionChart σ n i).target := by
  change ContinuousOn (fun y => (RelCWComplex.map n (σ n (1,i.2))).symm (i.1⁻¹ • y))
    (univ ∩ (fun y : X => i.1⁻¹ • y) ⁻¹' (RelCWComplex.map n (σ n (1,i.2))).target)
  exact (RelCWComplex.continuousOn_symm _ _).comp (continuous_const_smul _).continuousOn
    (fun _ h => h.2)


-- @@ L244-248 verbatim
variable
  (ho : ∀ n (g : G) (i : ι n),
    (fun x : X => g • x) '' RelCWComplex.openCell n (σ n (1,i)) = RelCWComplex.openCell n (σ n (g,i)))
  (hc : ∀ n (g : G) (i : ι n),
    (fun x : X => g • x) '' RelCWComplex.closedCell n (σ n (1,i)) = RelCWComplex.closedCell n (σ n (g,i)))


-- @@ L250-254 verbatim
include ho in
lemma actionChart_open (n : ℕ) (i : G × ι n) :
    actionChart σ n i '' ball 0 1 = RelCWComplex.openCell n (σ n i) := by
  rw [actionChart_image]
  exact ho n i.1 i.2


-- @@ L256-260 verbatim
include hc in
lemma actionChart_closed (n : ℕ) (i : G × ι n) :
    actionChart σ n i '' closedBall 0 1 = RelCWComplex.closedCell n (σ n i) := by
  rw [actionChart_image]
  exact hc n i.1 i.2


-- @@ L262-268 verbatim
omit [ContinuousConstSMul G X] in
include hc in
lemma closedCell_smul (n : ℕ) (g h : G) (i : ι n) :
    (fun x : X => g • x) '' RelCWComplex.closedCell n (σ n (h,i)) =
      RelCWComplex.closedCell n (σ n (g*h,i)) := by
  rw [←hc n h i,←Set.image_comp]
  simpa only [Function.comp_def,mul_smul] using hc n (g*h) i


-- @@ L270-270 verbatim
variable [T2Space X]


-- @@ L272-327 verbatim
@[instance_reducible]
def actionCW : CWComplex (univ : Set X) where
  cell n := G × ι n
  map := actionChart σ
  source_eq := actionChart_source σ
  continuousOn := actionChart_continuousOn σ
  continuousOn_symm := actionChart_continuousOn_symm σ
  pairwiseDisjoint' := by
    intro p _ q _ hpq
    change Disjoint (actionChart σ p.1 p.2 '' ball 0 1) (actionChart σ q.1 q.2 '' ball 0 1)
    rw [actionChart_open σ ho,actionChart_open σ ho]
    apply CWComplex.disjoint_openCell_of_ne
    intro he
    apply hpq
    cases p with | mk n i =>
      cases q with | mk m j =>
        have hnm : n = m := congrArg Sigma.fst he
        subst m
        have hij : σ n i = σ n j := (Sigma.mk.inj he).2 |> eq_of_heq
        exact congrArg (Sigma.mk n) ((σ n).injective hij)
  mapsTo' := by
    classical
    intro n i
    obtain ⟨I,hI⟩ := CWComplex.cellFrontier_subset_finite_closedCell n (σ n (1,i.2))
    let f (m : ℕ) (j : RelCWComplex.cell (univ : Set X) m) : G × ι m :=
      (i.1 * ((σ m).symm j).1,((σ m).symm j).2)
    refine ⟨fun m => (I m).image (f m),?_⟩
    intro x hx
    have h := hI (show RelCWComplex.map n (σ n (1,i.2)) x ∈ RelCWComplex.cellFrontier n (σ n (1,i.2)) from ⟨x,hx,rfl⟩)
    simp only [Set.mem_iUnion] at h
    obtain ⟨m,hm,j,hj,hxj⟩ := h
    refine Set.mem_iUnion.mpr ⟨m,Set.mem_iUnion.mpr ⟨hm,Set.mem_iUnion.mpr
      ⟨f m j,Set.mem_iUnion.mpr ⟨Finset.mem_image.mpr ⟨j,hj,rfl⟩,?_⟩⟩⟩⟩
    rw [actionChart_closed σ hc]
    change i.1 • RelCWComplex.map n (σ n (1,i.2)) x ∈ RelCWComplex.closedCell m
      (σ m (i.1 * ((σ m).symm j).1,((σ m).symm j).2))
    rw [←closedCell_smul σ hc]
    refine ⟨_,?_,rfl⟩
    simpa only [Prod.eta,Equiv.apply_symm_apply] using hxj
  closed' := by
    intro A hA hclosed
    apply (CWComplex.closed (univ : Set X) A hA).mpr
    intro n j
    obtain ⟨i,rfl⟩ := (σ n).surjective j
    simpa only [actionChart_closed σ hc] using hclosed n i
  union' := by
    simp only [actionChart_closed σ hc]
    have he (n : ℕ) : (⋃ j : G × ι n, RelCWComplex.closedCell n (σ n j)) =
        ⋃ j : RelCWComplex.cell (univ : Set X) n, RelCWComplex.closedCell n j := by
      ext x
      simp only [mem_iUnion]
      constructor
      · rintro ⟨j,hj⟩; exact ⟨σ n j,hj⟩
      · rintro ⟨j,hj⟩; exact ⟨(σ n).symm j,by simpa only [Equiv.apply_symm_apply] using hj⟩
    simp_rw [he]
    exact CWComplex.union


-- @@ L329-332 verbatim
omit [T2Space X] in
lemma actionChart_smul (n : ℕ) (g : G) (i : G × ι n) (x : Fin n → ℝ) :
    actionChart σ n (g*i.1,i.2) x = g • actionChart σ n i x := by
  exact mul_smul _ _ _

-- @@ L333-333 verbatim
end UniversalFInfinity.Cellular


-- @@ L335-335 verbatim
namespace UniversalFInfinity.Milnor

-- @@ L336-336 verbatim
open Set Metric Topology UniversalFInfinity.Simplicial

-- @@ L337-337 verbatim
universe u

-- @@ L338-338 verbatim
variable (G : Type u) [Group G]

-- @@ L339-339 verbatim
local instance (priority := 2000) (α : Type*) : DecidableEq (ℕ × α) := Classical.decEq (ℕ × α)


-- @@ L341-346 verbatim
lemma vertexTranslate_injective (g : G) : Function.Injective (fun v : ℕ × G => (v.1,g*v.2)) := by
  rintro ⟨i,a⟩ ⟨j,b⟩ h
  change (i,g*a) = (j,g*b) at h
  apply Prod.ext
  · simpa only using congrArg (fun v : ℕ × G => v.1) h
  · exact mul_left_cancel (congrArg Prod.snd h)


-- @@ L348-349 verbatim
lemma translate_card (g : G) (s : Finset (ℕ × G)) : (translate g s).card = s.card :=
  Finset.card_image_of_injective _ (vertexTranslate_injective G g)


-- @@ L351-351 verbatim
abbrev StageCell (S : Shapes G) (n : ℕ) := Simplicial.Cell (stage G S) n


-- @@ L353-354 verbatim
def cellTranslate (S : Shapes G) (n : ℕ) (g : G) (c : StageCell G S n) : StageCell G S n :=
  ⟨⟨translate g c.1.1,orbitSpan_invariant _ g c.1.2⟩,by rw [translate_card]; exact c.2⟩


-- @@ L356-359 verbatim
instance cellAction (S : Shapes G) (n : ℕ) : MulAction G (StageCell G S n) where
  smul := cellTranslate G S n
  one_smul c := by apply Subtype.ext; apply Subtype.ext; exact translate_one _
  mul_smul g h c := by apply Subtype.ext; apply Subtype.ext; exact (translate_mul _ _ _).symm


-- @@ L361-362 verbatim
lemma cell_smul_val (S : Shapes G) (n : ℕ) (g : G) (c : StageCell G S n) :
    (g • c).1.1 = translate g c.1.1 := rfl


-- @@ L364-371 verbatim
lemma cellAction_free (S : Shapes G) (n : ℕ) (g : G) (c : StageCell G S n)
    (h : g • c = c) : g = 1 := by
  have he : translate g c.1.1 = c.1.1 := congrArg (fun c : StageCell G S n => c.1.1) h
  obtain ⟨v,hv⟩ := c.1.2.1.1
  have ht : (v.1,g*v.2) ∈ c.1.1 := he ▸ Finset.mem_image.mpr ⟨v,hv,rfl⟩
  have heq := c.1.2.1.2 ht hv rfl
  have hg : g * v.2 = v.2 := congrArg Prod.snd heq
  exact mul_right_cancel (hg.trans (one_mul _).symm)


-- @@ L373-373 verbatim
abbrev CellOrbits (S : Shapes G) (n : ℕ) := Orbits (G := G) (A := StageCell G S n)


-- @@ L375-376 verbatim
def cellCoordinates (S : Shapes G) (n : ℕ) : (G × CellOrbits G S n) ≃ StageCell G S n :=
  orbitCoordinates (cellAction_free G S n)


-- @@ L378-379 verbatim
lemma cellCoordinates_apply (S : Shapes G) (n : ℕ) (g : G) (c : CellOrbits G S n) :
    cellCoordinates G S n (g,c) = g • c.out := rfl


-- @@ L381-398 verbatim
instance cellOrbits_finite (S : Shapes G) (n : ℕ) : Finite (CellOrbits G S n) := by
  classical
  obtain ⟨T,hT⟩ := orbitSpan_finite_representatives (basedShapes G S)
  let R : Set (StageCell G S n) := {c | c.1.1 ∈ T}
  have hinj : Function.Injective (fun c : StageCell G S n => c.1.1) := by
    intro c d h; exact Subtype.ext (Subtype.ext h)
  have hR : R.Finite := T.finite_toSet.preimage hinj.injOn
  let := hR.fintype
  apply Finite.of_surjective (fun c : R => (Quotient.mk'' c.1 : CellOrbits G S n))
  intro q
  obtain ⟨s,hs,g,hg⟩ := hT q.out.1.1 q.out.1.2
  let c : StageCell G S n := g⁻¹ • q.out
  have hc : c ∈ R := by
    change translate g⁻¹ q.out.1.1 ∈ T
    rw [hg,translate_mul,inv_mul_cancel,translate_one]
    exact hs
  refine ⟨⟨c,hc⟩,?_⟩
  exact (orbit_mk_smul g⁻¹ q.out).trans (Quotient.out_eq' _)


-- @@ L400-402 verbatim
lemma stage_smul_support (S : Shapes G) (g : G) (x : Stage G S) :
    (g • x).1.support = translate g x.1.support :=
  Finsupp.mapDomain_support_of_injective (vertexTranslate_injective G g) _


-- @@ L404-406 verbatim
lemma stage_openCell (S : Shapes G) (n : ℕ) (c : StageCell G S n) :
    RelCWComplex.openCell (C := (univ : Set (Stage G S))) n c = {x : Stage G S | x.1.support = c.1.1} :=
  Simplicial.characteristicPE_open _ _


-- @@ L408-411 verbatim
lemma stage_closedCell (S : Shapes G) (n : ℕ) (c : StageCell G S n) :
    RelCWComplex.closedCell (C := (univ : Set (Stage G S))) n c = {x : Stage G S | x.1.support ⊆ c.1.1} := by
  change Simplicial.characteristicPE _ c '' closedBall 0 1 = _
  rw [Simplicial.characteristicPE_closed,Simplicial.range_faceMap]


-- @@ L413-425 verbatim
lemma stage_openCell_smul (S : Shapes G) (n : ℕ) (g : G) (c : StageCell G S n) :
    (fun x : Stage G S => g • x) '' RelCWComplex.openCell (C := (univ : Set (Stage G S))) n c = RelCWComplex.openCell (C := (univ : Set (Stage G S))) n (g • c) := by
  rw [stage_openCell,stage_openCell]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change (g • y).1.support = (g • c).1.1
    rw [stage_smul_support,cell_smul_val,hy]
  · intro hx
    refine ⟨g⁻¹ • x,?_,smul_inv_smul _ _⟩
    change (g⁻¹ • x).1.support = c.1.1
    change x.1.support = translate g c.1.1 at hx
    rw [stage_smul_support,hx,translate_mul,inv_mul_cancel,translate_one]


-- @@ L427-441 verbatim
lemma stage_closedCell_smul (S : Shapes G) (n : ℕ) (g : G) (c : StageCell G S n) :
    (fun x : Stage G S => g • x) '' RelCWComplex.closedCell (C := (univ : Set (Stage G S))) n c = RelCWComplex.closedCell (C := (univ : Set (Stage G S))) n (g • c) := by
  rw [stage_closedCell,stage_closedCell]
  ext x
  constructor
  · rintro ⟨y,hy,rfl⟩
    change (g • y).1.support ⊆ (g • c).1.1
    rw [stage_smul_support,cell_smul_val]
    exact translate_mono _ hy
  · intro hx
    refine ⟨g⁻¹ • x,?_,smul_inv_smul _ _⟩
    change (g⁻¹ • x).1.support ⊆ c.1.1
    rw [stage_smul_support]
    have h := translate_mono g⁻¹ hx
    simpa only [cell_smul_val,translate_mul,inv_mul_cancel,translate_one] using h


-- @@ L443-453 verbatim
@[instance_reducible]
def stageEquivariantCW (S : Shapes G) : CWComplex (univ : Set (Stage G S)) :=
  Cellular.actionCW (cellCoordinates G S)
    (fun n g i => by
      change (fun x : Stage G S => g • x) '' RelCWComplex.openCell (C := (univ : Set (Stage G S))) n ((1:G) • i.out) = RelCWComplex.openCell (C := (univ : Set (Stage G S))) n (g • i.out)
      rw [one_smul]
      exact stage_openCell_smul G S n g i.out)
    (fun n g i => by
      change (fun x : Stage G S => g • x) '' RelCWComplex.closedCell (C := (univ : Set (Stage G S))) n ((1:G) • i.out) = RelCWComplex.closedCell (C := (univ : Set (Stage G S))) n (g • i.out)
      rw [one_smul]
      exact stage_closedCell_smul G S n g i.out)


-- @@ L455-455 verbatim
end UniversalFInfinity.Milnor


-- @@ L457-457 verbatim
end


-- @@ L459-459 verbatim
end OAI
