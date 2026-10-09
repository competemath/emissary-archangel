import OAI.GroupTheory.UniversalGroup.CompactCells


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open Set Metric Topology BigOperators

-- @@ L6-6 verbatim
open Set Metric Topology



-- @@ L9-9 verbatim
namespace UniversalFInfinity.Cellular

-- @@ L10-10 verbatim
universe u v w


-- @@ L12-12 verbatim
abbrev Disk (n : ℕ) := closedBall (0 : Fin n → ℝ) 1

-- @@ L13-13 verbatim
abbrev Sphere (n : ℕ) := sphere (0 : Fin n → ℝ) 1


-- @@ L15-16 verbatim
def boundary (n : ℕ) : Sphere n → Disk n :=
  fun x => ⟨x.1, sphere_subset_closedBall x.2⟩


-- @@ L18-19 verbatim
lemma continuous_boundary (n : ℕ) : Continuous (boundary n) :=
  continuous_subtype_val.subtype_mk _


-- @@ L21-21 verbatim
variable {X : Type u} [TopologicalSpace X] [T2Space X]

-- @@ L22-22 verbatim
variable {C : Set X} [CWComplex C]


-- @@ L24-25 verbatim
def characteristic (n : ℕ) (i : RelCWComplex.cell C n) : C(Disk n, X) :=
  ⟨fun x => RelCWComplex.map n i x.1, (RelCWComplex.continuousOn n i).domRestrict⟩


-- @@ L27-33 verbatim
omit [T2Space X] in
lemma range_characteristic (n : ℕ) (i : RelCWComplex.cell C n) :
    Set.range (characteristic n i) = CWComplex.closedCell n i := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩; exact ⟨y.1,y.2,rfl⟩
  · rintro ⟨y,hy,rfl⟩; exact ⟨⟨y,hy⟩,rfl⟩


-- @@ L35-61 verbatim
lemma continuousOn_iff_characteristic {Y : Type v} [TopologicalSpace Y] (f : X → Y) :
    ContinuousOn f C ↔ ∀ n (i : RelCWComplex.cell C n),
      Continuous (f ∘ characteristic n i) := by
  constructor
  · intro hf n i
    exact hf.comp_continuous (characteristic n i).continuous
      (fun x => CWComplex.closedCell_subset_complex n i ⟨x.1,x.2,rfl⟩)
  · intro hf
    rw [continuousOn_iff_continuous_domRestrict, continuous_iff_isClosed]
    intro S hS
    have hclosed : IsClosed (C ∩ f ⁻¹' S) := by
      apply (CWComplex.closed C _ inter_subset_left).2
      intro n i
      have hpre : IsClosed ((f ∘ characteristic n i) ⁻¹' S) :=
        hS.preimage (hf n i)
      have hcompact := hpre.isCompact.image (characteristic n i).continuous
      convert hcompact.isClosed using 1
      ext x
      constructor
      · rintro ⟨⟨hxC,hxS⟩, y,hy,rfl⟩
        exact ⟨⟨y,hy⟩,hxS,rfl⟩
      · rintro ⟨y,hy,rfl⟩
        exact ⟨⟨CWComplex.closedCell_subset_complex n i ⟨y.1,y.2,rfl⟩,hy⟩,
          y.1,y.2,rfl⟩
    convert hclosed.preimage continuous_subtype_val using 1
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, and_iff_right x.2, Set.domRestrict_apply]


-- @@ L63-64 verbatim
abbrev Skeleton (C : Set X) [CWComplex C] (n : ℕ) : Set X :=
  CWComplex.skeletonLT C n


-- @@ L66-68 verbatim
lemma skeleton_mono {m n : ℕ} (h : m ≤ n) :
    Skeleton C m ⊆ Skeleton C n :=
  CWComplex.skeletonLT_mono (by exact_mod_cast h)


-- @@ L70-72 verbatim
lemma sphere_mem_skeleton (n : ℕ) (i : RelCWComplex.cell C n) (x : Sphere n) :
    characteristic n i (boundary n x) ∈ Skeleton C n :=
  CWComplex.cellFrontier_subset_skeletonLT n i ⟨x.1,x.2,rfl⟩


-- @@ L74-78 verbatim
lemma characteristic_mem_skeleton {m n : ℕ} (h : m < n)
    (i : RelCWComplex.cell C m) (x : Disk m) :
    characteristic m i x ∈ Skeleton C n := by
  apply skeleton_mono (Nat.succ_le_of_lt h)
  exact CWComplex.closedCell_subset_skeletonLT m i ⟨x.1,x.2,rfl⟩


-- @@ L80-82 verbatim
lemma openCell_not_skeleton (n : ℕ) (i : RelCWComplex.cell C n) {x : X}
    (hx : x ∈ CWComplex.openCell n i) : x ∉ Skeleton C n :=
  (CWComplex.disjoint_skeletonLT_openCell (C := C) (j := i) le_rfl).notMem_of_mem_right hx


-- @@ L84-88 verbatim
structure PartialLift {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E,B)) (f : C(X,B)) (n : ℕ) where
  val : X → E
  continuousOn : ContinuousOn val (Skeleton C n)
  fac : ∀ x ∈ Skeleton C n, p (val x) = f x


-- @@ L90-94 verbatim
def DiskRLP {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E,B)) : Prop :=
  ∀ n (a : C(Sphere n,E)) (b : C(Disk n,B)),
    (∀ x, p (a x) = b (boundary n x)) →
    ∃ e : C(Disk n,E), (∀ x, e (boundary n x) = a x) ∧ ∀ x, p (e x) = b x


-- @@ L96-96 verbatim
section Attach

-- @@ L97-97 verbatim
variable {E : Type v} [TopologicalSpace E] {n : ℕ}


-- @@ L99-107 verbatim
noncomputable def attachValue (a : X → E) (e : ∀ _ : RelCWComplex.cell C n, C(Disk n,E))
    (x : X) : E := by
  classical
  exact if x ∈ Skeleton C n then a x
    else if h : ∃ i : RelCWComplex.cell C n, x ∈ CWComplex.openCell n i then
      let i := h.choose
      let y := h.choose_spec.choose
      e i ⟨y,ball_subset_closedBall h.choose_spec.choose_spec.1⟩
    else a x


-- @@ L109-112 verbatim
lemma attachValue_old (a : X → E) (e : ∀ _ : RelCWComplex.cell C n, C(Disk n,E))
    {x : X} (hx : x ∈ Skeleton C n) : attachValue a e x = a x := by
  classical
  simp only [attachValue, ite_eq_left hx]


-- @@ L114-139 verbatim
lemma attachValue_interior (a : X → E) (e : ∀ _ : RelCWComplex.cell C n, C(Disk n,E))
    (i : RelCWComplex.cell C n) (y : Disk n) (hy : y.1 ∈ ball 0 1) :
    attachValue a e (characteristic n i y) = e i y := by
  classical
  have hx : characteristic n i y ∈ CWComplex.openCell n i := ⟨y.1,hy,rfl⟩
  have h : ∃ j : RelCWComplex.cell C n,
      characteristic n i y ∈ CWComplex.openCell n j := ⟨i,hx⟩
  rw [attachValue,ite_eq_right (openCell_not_skeleton n i hx),dite_eq_left h]
  have hi : h.choose = i := by
    by_contra hne
    have hd := CWComplex.disjoint_openCell_of_ne (C := C) (i := h.choose) (j := i)
      (fun hEq => hne (sigma_mk_injective hEq))
    exact Set.disjoint_left.mp hd h.choose_spec hx
  have hz := h.choose_spec.choose_spec.1
  have hmap : RelCWComplex.map n i h.choose_spec.choose = characteristic n i y := by
    calc
      RelCWComplex.map n i h.choose_spec.choose =
          RelCWComplex.map n h.choose h.choose_spec.choose :=
        congrArg (fun k => RelCWComplex.map n k h.choose_spec.choose) hi.symm
      _ = _ := h.choose_spec.choose_spec.2
  have hcoord : h.choose_spec.choose = y.1 :=
    (RelCWComplex.map n i).injOn
      (by simpa only [RelCWComplex.source_eq] using hz)
      (by simpa only [RelCWComplex.source_eq] using hy) hmap
  exact (congrArg (fun k => e k ⟨h.choose_spec.choose,ball_subset_closedBall hz⟩) hi).trans
    (congrArg (e i) (Subtype.ext hcoord))


-- @@ L141-152 verbatim
lemma attachValue_characteristic (a : X → E)
    (e : ∀ _ : RelCWComplex.cell C n, C(Disk n,E))
    (he : ∀ i (x : Sphere n), e i (boundary n x) =
      a (characteristic n i (boundary n x)))
    (i : RelCWComplex.cell C n) (y : Disk n) :
    attachValue a e (characteristic n i y) = e i y := by
  by_cases hy : y.1 ∈ ball 0 1
  · exact attachValue_interior a e i y hy
  · have hs : y.1 ∈ sphere 0 1 := le_antisymm y.2 (le_of_not_gt hy)
    have hx : characteristic n i y ∈ Skeleton C n := sphere_mem_skeleton n i ⟨y,hs⟩
    rw [attachValue_old a e hx]
    exact (he i ⟨y,hs⟩).symm


-- @@ L154-179 verbatim
lemma attachValue_continuous (a : X → E) (ha : ContinuousOn a (Skeleton C n))
    (e : ∀ _ : RelCWComplex.cell C n, C(Disk n,E))
    (he : ∀ i (x : Sphere n), e i (boundary n x) =
      a (characteristic n i (boundary n x))) :
    ContinuousOn (attachValue a e) (Skeleton C (n+1)) := by
  apply (continuousOn_iff_characteristic (C := Skeleton C (n+1)) _).2
  intro m j
  change Continuous (fun x : Disk m => attachValue a e (characteristic m j.1 x))
  have hm : m < n+1 := by
    have h : (m : ℕ∞) < ((n+1 : ℕ) : ℕ∞) := by
      simpa only [RelCWComplex.skeletonLT_I,Set.mem_ofPred_eq] using j.2
    exact_mod_cast h
  rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | hm
  · have hEq : (fun x : Disk m => attachValue a e (characteristic m j.1 x)) =
        (fun x : Disk m => a (characteristic m j.1 x)) := by
      funext x
      exact attachValue_old a e (characteristic_mem_skeleton hm j.1 x)
    rw [hEq]
    exact ha.comp_continuous (characteristic m j.1).continuous
      (characteristic_mem_skeleton hm j.1)
  · subst m
    have hEq : (fun x : Disk n => attachValue a e (characteristic n j.1 x)) = e j.1 := by
      funext x
      exact attachValue_characteristic a e he j.1 x
    rw [hEq]
    exact (e j.1).continuous


-- @@ L181-181 verbatim
end Attach


-- @@ L183-183 verbatim
namespace PartialLift

-- @@ L184-184 verbatim
variable {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B]

-- @@ L185-185 verbatim
variable {p : C(E,B)} {f : C(X,B)} {n : ℕ}


-- @@ L187-192 verbatim
def onSphere (a : PartialLift (C := C) p f n) (i : RelCWComplex.cell C n) :
    C(Sphere n,E) :=
  ⟨fun x => a.val (characteristic n i (boundary n x)),
    a.continuousOn.comp_continuous
      ((characteristic n i).continuous.comp (continuous_boundary n))
      (sphere_mem_skeleton n i)⟩


-- @@ L194-201 verbatim
lemma exists_cell_extension (a : PartialLift (C := C) p f n) (hp : DiskRLP p)
    (i : RelCWComplex.cell C n) :
    ∃ e : C(Disk n,E),
      (∀ x, e (boundary n x) = a.val (characteristic n i (boundary n x))) ∧
      ∀ x, p (e x) = f (characteristic n i x) := by
  apply hp n (a.onSphere i) (f.comp (characteristic n i))
  intro x
  exact a.fac _ (sphere_mem_skeleton n i x)


-- @@ L203-219 verbatim
noncomputable def next (a : PartialLift (C := C) p f n) (hp : DiskRLP p) :
    PartialLift (C := C) p f (n+1) := by
  choose e hb hf using fun i => a.exists_cell_extension hp i
  refine ⟨attachValue a.val e,attachValue_continuous a.val a.continuousOn e hb,?_⟩
  intro x hx
  have hdecomp : Skeleton C (n+1) = Skeleton C n ∪
      ⋃ i : RelCWComplex.cell C n, CWComplex.closedCell n i := by
    simpa only [Skeleton,Nat.cast_add,Nat.cast_one] using
      (CWComplex.skeletonLT_union_iUnion_closedCell_eq_skeletonLT_succ (C := C) n).symm
  rw [hdecomp] at hx
  rcases hx with hx | hx
  · rw [attachValue_old a.val e hx]
    exact a.fac x hx
  · obtain ⟨i,y,hy,rfl⟩ := Set.mem_iUnion.mp hx
    rw [show RelCWComplex.map n i y = characteristic n i ⟨y,hy⟩ from rfl,
      attachValue_characteristic a.val e hb]
    exact hf i ⟨y,hy⟩


-- @@ L221-224 verbatim
lemma next_eq (a : PartialLift (C := C) p f n) (hp : DiskRLP p)
    {x : X} (hx : x ∈ Skeleton C n) : (a.next hp).val x = a.val x := by
  dsimp only [next]
  exact attachValue_old a.val _ hx


-- @@ L226-231 verbatim
noncomputable def zero [Nonempty E] : PartialLift (C := C) p f 0 where
  val := fun _ => Classical.choice ‹Nonempty E›
  continuousOn := continuous_const.continuousOn
  fac := by
    intro x hx
    simp only [Skeleton,Nat.cast_zero,CWComplex.skeletonLT_zero_eq_empty,Set.mem_empty_iff_false] at hx


-- @@ L233-233 verbatim
end PartialLift


-- @@ L235-235 verbatim
section Lift

-- @@ L236-236 verbatim
variable {E : Type v} {B : Type w} [TopologicalSpace E] [TopologicalSpace B] [Nonempty E]

-- @@ L237-237 verbatim
variable {p : C(E,B)} (hp : DiskRLP p) (f : C(X,B))


-- @@ L239-241 verbatim
noncomputable def stages : ∀ n, PartialLift (C := C) p f n
  | 0 => PartialLift.zero
  | n+1 => (stages n).next hp


-- @@ L243-248 verbatim
lemma stages_agree {m n : ℕ} (h : m ≤ n) {x : X} (hx : x ∈ Skeleton C m) :
    (stages (C := C) hp f n).val x = (stages (C := C) hp f m).val x := by
  induction n,h using Nat.le_induction with
  | base => rfl
  | succ n hn ih =>
    exact ((stages (C := C) hp f n).next_eq hp (skeleton_mono hn hx)).trans ih


-- @@ L250-252 verbatim
lemma exists_skeleton {x : X} (hx : x ∈ C) : ∃ n : ℕ, x ∈ Skeleton C n := by
  rw [← CWComplex.iUnion_skeletonLT_eq_complex (C := C)] at hx
  exact Set.mem_iUnion.mp hx


-- @@ L254-257 verbatim
noncomputable def liftValue (x : X) : E := by
  classical
  exact if hx : x ∈ C then (stages (C := C) hp f (exists_skeleton (C := C) hx).choose).val x
    else Classical.choice ‹Nonempty E›


-- @@ L259-267 verbatim
lemma liftValue_eq {n : ℕ} {x : X} (hx : x ∈ Skeleton C n) :
    liftValue (C := C) hp f x = (stages (C := C) hp f n).val x := by
  classical
  have hxC : x ∈ C := (CWComplex.skeletonLT C n).subset_complex hx
  rw [liftValue,dite_eq_left hxC]
  let m := (exists_skeleton (C := C) hxC).choose
  have hm : x ∈ Skeleton C m := (exists_skeleton (C := C) hxC).choose_spec
  exact (stages_agree hp f (Nat.le_max_left m n) hm).symm.trans
    (stages_agree hp f (Nat.le_max_right m n) hx)


-- @@ L269-278 verbatim
lemma continuousOn_liftValue : ContinuousOn (liftValue (C := C) hp f) C := by
  apply (continuousOn_iff_characteristic _).2
  intro n i
  have hEq : liftValue (C := C) hp f ∘ characteristic n i =
      (stages (C := C) hp f (n+1)).val ∘ characteristic n i := by
    funext x
    exact liftValue_eq hp f (characteristic_mem_skeleton (Nat.lt_succ_self n) i x)
  rw [hEq]
  exact (stages (C := C) hp f (n+1)).continuousOn.comp_continuous (characteristic n i).continuous
    (characteristic_mem_skeleton (Nat.lt_succ_self n) i)


-- @@ L280-283 verbatim
lemma liftValue_fac {x : X} (hx : x ∈ C) : p (liftValue (C := C) hp f x) = f x := by
  obtain ⟨n,hn⟩ := exists_skeleton (C := C) hx
  rw [liftValue_eq hp f hn]
  exact (stages (C := C) hp f n).fac x hn


-- @@ L285-292 verbatim
include hp in

theorem exists_lift [CWComplex (Set.univ : Set X)] :
    ∃ g : C(X,E), ∀ x, p (g x) = f x := by
  refine ⟨⟨liftValue (C := Set.univ) hp f,
    continuousOn_univ.mp (continuousOn_liftValue (C := Set.univ) hp f)⟩,?_⟩
  intro x
  exact liftValue_fac hp f (Set.mem_univ x)


-- @@ L294-294 verbatim
end Lift


-- @@ L296-296 verbatim
noncomputable section


-- @@ L298-299 verbatim
def SphereFillable (Y : Type u) [TopologicalSpace Y] : Prop :=
  ∀ n (a : C(Sphere n,Y)), ∃ e : C(Disk n,Y), ∀ x, e (boundary n x) = a x


-- @@ L301-303 verbatim
lemma disk_coord {n : ℕ} (x : Disk n) (i : Fin n) : |x.1 i| ≤ 1 := by
  exact (pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mp
    (mem_closedBall_zero_iff.mp x.2) i


-- @@ L305-308 verbatim
lemma disk_mem {n : ℕ} {x : Fin n → ℝ} (h : ∀ i, |x i| ≤ 1) :
    x ∈ closedBall 0 1 := by
  exact mem_closedBall_zero_iff.mpr
    ((pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 1)).mpr h)


-- @@ L310-316 verbatim
def diskCons {n : ℕ} (x : Disk n) (t : unitInterval) : Disk (n+1) :=
  ⟨Fin.cons (2*t.1-1) x.1, disk_mem (by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [Fin.cons_zero,abs_le]
      constructor <;> linarith [t.2.1,t.2.2]
    · exact disk_coord x j)⟩


-- @@ L318-327 verbatim
lemma continuous_diskCons {n : ℕ} :
    Continuous (fun q : Disk n × unitInterval => diskCons q.1 q.2) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · change Continuous (fun q : Disk n × unitInterval => 2*q.2.1-1)
    fun_prop
  · change Continuous (fun q : Disk n × unitInterval => q.1.1 j)
    exact (continuous_apply j).comp (continuous_subtype_val.comp continuous_fst)


-- @@ L329-330 verbatim
def diskTail {n : ℕ} (x : Disk (n+1)) : Disk n :=
  ⟨Fin.tail x.1,disk_mem (fun i => disk_coord x i.succ)⟩


-- @@ L332-334 verbatim
lemma continuous_diskTail {n : ℕ} : Continuous (@diskTail n) := by
  apply Continuous.subtype_mk
  exact continuous_pi (fun i => (continuous_apply i.succ).comp continuous_subtype_val)


-- @@ L336-337 verbatim
def diskTime {n : ℕ} (x : Disk (n+1)) : unitInterval :=
  ⟨(x.1 0+1)/2,by have h := (abs_le.mp (disk_coord x 0)); constructor <;> linarith⟩


-- @@ L339-340 verbatim
lemma continuous_diskTime {n : ℕ} : Continuous (@diskTime n) := by
  exact (((continuous_apply 0).comp continuous_subtype_val).add continuous_const).div_const 2 |>.subtype_mk _


-- @@ L342-345 verbatim
@[simp] lemma diskTail_cons {n : ℕ} (x : Disk n) (t : unitInterval) :
    diskTail (diskCons x t) = x := by
  apply Subtype.ext
  simp only [diskTail,diskCons,Fin.tail_cons]


-- @@ L347-351 verbatim
@[simp] lemma diskTime_cons {n : ℕ} (x : Disk n) (t : unitInterval) :
    diskTime (diskCons x t) = t := by
  apply Subtype.ext
  simp only [diskTime,diskCons,Fin.cons_zero]
  ring


-- @@ L353-357 verbatim
lemma sphere_iff_coord {n : ℕ} (x : Disk n) :
    x.1 ∈ sphere 0 1 ↔ ∃ i, |x.1 i| = 1 := by
  rw [sphere_pi (0 : Fin n → ℝ) (Or.inl (by norm_num))]
  simp only [Set.mem_inter_iff,Set.mem_iUnion,Set.mem_preimage,Function.eval,
    Pi.zero_apply,mem_sphere_zero_iff_norm,Real.norm_eq_abs,and_iff_left x.2]


-- @@ L359-362 verbatim
lemma cons_mem_sphere_of_boundary {n : ℕ} (x : Sphere n) (t : unitInterval) :
    (diskCons (boundary n x) t).1 ∈ sphere 0 1 := by
  obtain ⟨i,hi⟩ := (sphere_iff_coord (boundary n x)).mp x.2
  exact (sphere_iff_coord _).mpr ⟨i.succ,hi⟩


-- @@ L364-367 verbatim
lemma cons_zero_mem_sphere {n : ℕ} (x : Disk n) :
    (diskCons x 0).1 ∈ sphere 0 1 := by
  apply (sphere_iff_coord _).mpr
  exact ⟨0,by norm_num [diskCons]⟩


-- @@ L369-372 verbatim
lemma cons_one_mem_sphere {n : ℕ} (x : Disk n) :
    (diskCons x 1).1 ∈ sphere 0 1 := by
  apply (sphere_iff_coord _).mpr
  exact ⟨0,by norm_num [diskCons]⟩


-- @@ L374-382 verbatim
lemma sphere_split {n : ℕ} (x : Sphere (n+1)) :
    x.1 0 = -1 ∨ x.1 0 = 1 ∨ (diskTail (boundary (n+1) x)).1 ∈ sphere 0 1 := by
  obtain ⟨i,hi⟩ := (sphere_iff_coord (boundary (n+1) x)).mp x.2
  refine Fin.cases ?_ (fun i hi => ?_) i hi
  · intro h
    rcases abs_eq (by norm_num : (0:ℝ) ≤ 1) |>.mp h with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
  · exact Or.inr (Or.inr ((sphere_iff_coord _).mpr ⟨i,hi⟩))


-- @@ L384-393 verbatim
lemma continuous_liftCover {A : Type u} {Y : Type v} {ι : Type w}
    [TopologicalSpace A] [TopologicalSpace Y] [Finite ι]
    (S : ι → Set A) (f : ∀ i, C(S i,Y))
    (hcompat : ∀ i j x (hi : x ∈ S i) (hj : x ∈ S j), f i ⟨x,hi⟩ = f j ⟨x,hj⟩)
    (hcover : ⋃ i, S i = Set.univ) (hclosed : ∀ i, IsClosed (S i)) :
    Continuous (Set.liftCover S (fun i => f i) hcompat hcover) := by
  rw [continuous_iff_isClosed]
  intro D hD
  rw [Set.preimage_liftCover]
  exact isClosed_iUnion_of_finite fun i => (hclosed i).isClosedMap_subtype_val _ (hD.preimage (f i).continuous)


-- @@ L395-398 verbatim
def cylinderFace (n : ℕ) : Option Bool → Set (Sphere (n+1))
  | none => {x | (diskTail (boundary (n+1) x)).1 ∈ sphere 0 1}
  | some false => {x | x.1 0 = -1}
  | some true => {x | x.1 0 = 1}


-- @@ L400-407 verbatim
lemma cylinderFace_closed (n : ℕ) (i : Option Bool) : IsClosed (cylinderFace n i) := by
  cases i with
  | none =>
    exact isClosed_sphere.preimage
      (continuous_subtype_val.comp (continuous_diskTail.comp (continuous_boundary (n+1))))
  | some b =>
    cases b <;>
      exact isClosed_eq ((continuous_apply 0).comp continuous_subtype_val) continuous_const


-- @@ L409-415 verbatim
lemma cylinderFace_cover (n : ℕ) : ⋃ i, cylinderFace n i = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  rcases sphere_split x with h | h | h
  · exact Set.mem_iUnion.mpr ⟨some false,h⟩
  · exact Set.mem_iUnion.mpr ⟨some true,h⟩
  · exact Set.mem_iUnion.mpr ⟨none,h⟩


-- @@ L417-417 verbatim
variable {Y : Type u} [TopologicalSpace Y]


-- @@ L419-420 verbatim
def pathEndpoint : C(C(unitInterval,Y), Y × Y) :=
  ⟨fun q => (q 0,q 1), (continuous_eval_const 0).prodMk (continuous_eval_const 1)⟩


-- @@ L422-422 verbatim
section CylinderMap

-- @@ L423-423 verbatim
variable {n : ℕ} (a : C(Sphere n,C(unitInterval,Y))) (b : C(Disk n,Y × Y))


-- @@ L425-427 verbatim
def faceTail (i : Option Bool) : C(cylinderFace n i,Disk n) :=
  ⟨fun x => diskTail (boundary (n+1) x.1),
    continuous_diskTail.comp ((continuous_boundary (n+1)).comp continuous_subtype_val)⟩


-- @@ L429-430 verbatim
def faceSphere : C(cylinderFace n none,Sphere n) :=
  ⟨fun x => ⟨(faceTail none x).1,x.2⟩, (continuous_subtype_val.comp (faceTail none).continuous).subtype_mk _⟩


-- @@ L432-434 verbatim
def faceTime (i : Option Bool) : C(cylinderFace n i,unitInterval) :=
  ⟨fun x => diskTime (boundary (n+1) x.1),
    continuous_diskTime.comp ((continuous_boundary (n+1)).comp continuous_subtype_val)⟩


-- @@ L436-442 verbatim
def faceMap : ∀ i : Option Bool, C(cylinderFace n i,Y)
  | none => ⟨fun x => a (faceSphere x) (faceTime none x),
      continuous_eval.comp ((a.continuous.comp faceSphere.continuous).prodMk (faceTime none).continuous)⟩
  | some false => ⟨fun x => (b (faceTail (some false) x)).1,
      continuous_fst.comp (b.continuous.comp (faceTail (some false)).continuous)⟩
  | some true => ⟨fun x => (b (faceTail (some true) x)).2,
      continuous_snd.comp (b.continuous.comp (faceTail (some true)).continuous)⟩


-- @@ L444-449 verbatim
lemma faceTime_eq_zero (x : Sphere (n+1)) (h : x.1 0 = -1) :
    diskTime (boundary (n+1) x) = 0 := by
  apply Subtype.ext
  change (x.1 0+1)/2 = 0
  rw [h]
  norm_num


-- @@ L451-456 verbatim
lemma faceTime_eq_one (x : Sphere (n+1)) (h : x.1 0 = 1) :
    diskTime (boundary (n+1) x) = 1 := by
  apply Subtype.ext
  change (x.1 0+1)/2 = 1
  rw [h]
  norm_num


-- @@ L458-458 verbatim
variable (h : ∀ x, pathEndpoint (a x) = b (boundary n x))


-- @@ L460-492 verbatim
include h in
lemma faceMap_compat (i j : Option Bool) (x : Sphere (n+1))
    (hi : x ∈ cylinderFace n i) (hj : x ∈ cylinderFace n j) :
    faceMap a b i ⟨x,hi⟩ = faceMap a b j ⟨x,hj⟩ := by
  have left (hs : x ∈ cylinderFace n none) (h0 : x.1 0 = -1) :
      faceMap a b none ⟨x,hs⟩ = (b (diskTail (boundary (n+1) x))).1 := by
    change a (faceSphere ⟨x,hs⟩) (diskTime (boundary (n+1) x)) = _
    rw [faceTime_eq_zero x h0]
    exact congrArg Prod.fst (h (faceSphere ⟨x,hs⟩))
  have right (hs : x ∈ cylinderFace n none) (h1 : x.1 0 = 1) :
      faceMap a b none ⟨x,hs⟩ = (b (diskTail (boundary (n+1) x))).2 := by
    change a (faceSphere ⟨x,hs⟩) (diskTime (boundary (n+1) x)) = _
    rw [faceTime_eq_one x h1]
    exact congrArg Prod.snd (h (faceSphere ⟨x,hs⟩))
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some c => cases c; exact left hi hj; exact right hi hj
  | some c =>
    cases c
    · cases j with
      | none => exact (left hj hi).symm
      | some d =>
        cases d
        · rfl
        · have := hi.symm.trans hj; norm_num at this
    · cases j with
      | none => exact (right hj hi).symm
      | some d =>
        cases d
        · have := hi.symm.trans hj; norm_num at this
        · rfl


-- @@ L494-497 verbatim
def cylinderBoundaryMap : C(Sphere (n+1),Y) :=
  ⟨Set.liftCover (cylinderFace n) (fun i => faceMap a b i)
    (faceMap_compat a b h) (cylinderFace_cover n),
    continuous_liftCover _ _ _ _ (cylinderFace_closed n)⟩


-- @@ L499-503 verbatim
lemma cylinderBoundaryMap_face (i : Option Bool) (x : cylinderFace n i) :
    cylinderBoundaryMap a b h x.1 = faceMap a b i x :=
  by
    apply Set.liftCover_coe (S := cylinderFace n) (f := fun i => faceMap a b i)
      (hf := faceMap_compat a b h) (hS := cylinderFace_cover n)


-- @@ L505-505 verbatim
end CylinderMap


-- @@ L507-546 verbatim
theorem pathEndpoint_RLP (hY : SphereFillable Y) : DiskRLP (@pathEndpoint Y _) := by
  intro n a b h
  obtain ⟨F,hF⟩ := hY (n+1) (cylinderBoundaryMap a b h)
  let e : C(Disk n,C(unitInterval,Y)) :=
    (F.comp ⟨fun q : Disk n × unitInterval => diskCons q.1 q.2,continuous_diskCons⟩).curry
  refine ⟨e,?_,?_⟩
  · intro x
    apply ContinuousMap.ext
    intro t
    let s : Sphere (n+1) := ⟨_,cons_mem_sphere_of_boundary x t⟩
    have hs : s ∈ cylinderFace n none := by
      change (diskTail (diskCons (boundary n x) t)).1 ∈ sphere 0 1
      rw [diskTail_cons]
      exact x.2
    change F (diskCons (boundary n x) t) = a x t
    rw [show diskCons (boundary n x) t = boundary (n+1) s from rfl,hF,
      cylinderBoundaryMap_face a b h none ⟨s,hs⟩]
    change a (faceSphere ⟨s,hs⟩) (diskTime (diskCons (boundary n x) t)) = a x t
    rw [diskTime_cons]
    congr 1
  · intro x
    apply Prod.ext
    · let s : Sphere (n+1) := ⟨_,cons_zero_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some false) := by
        change (diskCons x 0).1 0 = -1
        norm_num [diskCons]
      change F (diskCons x 0) = (b x).1
      rw [show diskCons x 0 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some false) ⟨s,hs⟩]
      change (b (diskTail (diskCons x 0))).1 = (b x).1
      rw [diskTail_cons]
    · let s : Sphere (n+1) := ⟨_,cons_one_mem_sphere x⟩
      have hs : s ∈ cylinderFace n (some true) := by
        change (diskCons x 1).1 0 = 1
        norm_num [diskCons]
      change F (diskCons x 1) = (b x).2
      rw [show diskCons x 1 = boundary (n+1) s from rfl,hF,
        cylinderBoundaryMap_face a b h (some true) ⟨s,hs⟩]
      change (b (diskTail (diskCons x 1))).2 = (b x).2
      rw [diskTail_cons]


-- @@ L548-563 verbatim
theorem contractible_of_sphereFillable {Z : Type u} [TopologicalSpace Z] [T2Space Z]
    [Nonempty Z] [CWComplex (Set.univ : Set Z)] (hZ : SphereFillable Z) :
    ContractibleSpace Z := by
  classical
  let z₀ : Z := Classical.choice ‹Nonempty Z›
  let : Nonempty C(unitInterval,Z) := ⟨ContinuousMap.const _ z₀⟩
  let f : C(Z,Z × Z) := ⟨fun z => (z,z₀),continuous_id.prodMk continuous_const⟩
  obtain ⟨g,hg⟩ := exists_lift (pathEndpoint_RLP hZ) f
  apply (contractible_iff_id_nullhomotopic Z).mpr
  refine ⟨z₀,⟨?_⟩⟩
  refine ContinuousMap.Homotopy.mk ⟨fun q => g q.2 q.1,
    continuous_eval.comp ((g.continuous.comp continuous_snd).prodMk continuous_fst)⟩ ?_ ?_
  · intro z
    exact congrArg Prod.fst (hg z)
  · intro z
    exact congrArg Prod.snd (hg z)


-- @@ L565-565 verbatim
end

-- @@ L566-566 verbatim
end UniversalFInfinity.Cellular


-- @@ L568-568 verbatim
end OAI
