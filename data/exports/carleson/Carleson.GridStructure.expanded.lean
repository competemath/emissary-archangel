module

public import Carleson.ProofData


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-7 verbatim
open Set MeasureTheory Metric Function Complex Bornology

-- @@ L8-8 verbatim
open scoped NNReal ENNReal ComplexConjugate

-- @@ L9-9 verbatim
noncomputable section


-- @@ L11-11 verbatim
section Generic

-- @@ L12-12 verbatim
universe u

-- @@ L13-13 verbatim
variable {𝕜 : Type*} [_root_.RCLike 𝕜]


-- @@ L15-44 verbatim
variable (X) in
/-- A grid structure on `X`.
We prefer `coeGrid : Grid → Set X` over `Grid : Set (Set X)`
Note: the `s` in this paper is `-s` of Christ's paper.
-/
class GridStructure {A : outParam ℝ≥0} [PseudoMetricSpace X] [DoublingMeasure X A]
    (D : outParam ℕ) (κ : outParam ℝ) (S : outParam ℕ) (o : outParam X) where
  /-- indexing set for a grid structure -/
  protected Grid : Type u
  fintype_Grid : Fintype Grid
  /-- The collection of dyadic cubes -/
  coeGrid : Grid → Set X
  /-- scale functions -/
  s : Grid → ℤ
  /-- Center functions -/
  c : Grid → X
  inj : Injective (fun i ↦ (coeGrid i, s i))
  range_s_subset : range s ⊆ Icc (-S) S
  topCube : Grid
  s_topCube : s topCube = S
  c_topCube : c topCube = o
  subset_topCube {i} : coeGrid i ⊆ coeGrid topCube
  Grid_subset_biUnion {i} : ∀ k ∈ Ico (-S : ℤ) (s i), coeGrid i ⊆ ⋃ j ∈ s ⁻¹' {k}, coeGrid j
  fundamental_dyadic' {i j} : s i ≤ s j → coeGrid i ⊆ coeGrid j ∨ Disjoint (coeGrid i) (coeGrid j)
  ball_subset_Grid {i} : ball (c i) (D ^ s i / 4) ⊆ coeGrid i --2.0.10
  Grid_subset_ball {i} : coeGrid i ⊆ ball (c i) (4 * D ^ s i) --2.0.10
  small_boundary {i} {t : ℝ≥0} (ht : D ^ (- S - s i) ≤ t) :
    volume.real { x ∈ coeGrid i | Metric.infEDist x (coeGrid i)ᶜ ≤ t * (D ^ (s i):ℝ≥0∞)} ≤
    2 * t ^ κ * volume.real (coeGrid i)
  coeGrid_measurable {i} : MeasurableSet (coeGrid i)


-- @@ L46-47 verbatim
export GridStructure (range_s_subset Grid_subset_biUnion ball_subset_Grid Grid_subset_ball small_boundary
  topCube s_topCube c_topCube subset_topCube coeGrid_measurable) -- should `X` be explicit in topCube?


-- @@ L49-49 verbatim
attribute [coe] GridStructure.coeGrid


-- @@ L51-51 verbatim
variable {X : Type u} {A : ℝ≥0} [PseudoMetricSpace X] [DoublingMeasure X A]

-- @@ L52-52 verbatim
variable {D : ℕ} {κ : ℝ} {S : ℕ} {o : X}

-- @@ L53-53 verbatim
variable [GridStructure X D κ S o]


-- @@ L55-58 verbatim
variable (X) in
/-- The indexing type of the grid structure. Elements are called (dyadic) cubes.
Note that this type has instances for both `≤` and `⊆`, but they do *not* coincide. -/
abbrev Grid : Type u := GridStructure.Grid X


-- @@ L60-60 verbatim
def s : Grid X → ℤ := GridStructure.s

-- @@ L61-61 verbatim
def c : Grid X → X := GridStructure.c


-- @@ L63-63 verbatim
variable {i j : Grid X}


-- @@ L65-65 verbatim
instance : Inhabited (Grid X) := ⟨topCube⟩

-- @@ L66-66 verbatim
instance : Fintype (Grid X) := GridStructure.fintype_Grid

-- @@ L67-67 verbatim
instance : Coe (Grid X) (Set X) := ⟨GridStructure.coeGrid⟩

-- @@ L68-68 verbatim
instance : Membership X (Grid X) := ⟨fun i x ↦ x ∈ (i : Set X)⟩

-- @@ L69-72 verbatim
instance : PartialOrder (Grid X) := PartialOrder.lift _ GridStructure.inj

/- not sure whether these should be simp lemmas, but that might be required if we want to
  conveniently rewrite/simp with Set-lemmas -/

-- @@ L73-73 verbatim
@[simp] lemma Grid.mem_def {x : X} : x ∈ i ↔ x ∈ (i : Set X) := .rfl

-- @@ L74-74 verbatim
@[simp] lemma Grid.le_def : i ≤ j ↔ (i : Set X) ⊆ (j : Set X) ∧ s i ≤ s j := .rfl


-- @@ L76-77 verbatim
lemma Grid.eq_iff : i = j ↔ (i : Set X) = (j : Set X) ∧ s i = s j :=
  ⟨fun h ↦ by simp [h], fun h ↦ by apply le_antisymm <;> simp [Grid.le_def, h]⟩


-- @@ L79-83 verbatim
lemma Grid.mem_mono {x : X} : Monotone (x ∈ · : Grid X → Prop) := by
  intro u u' hle hu
  rw [Grid.mem_def] at hu ⊢
  rw [Grid.le_def] at hle
  exact hle.left hu


-- @@ L85-87 verbatim
lemma fundamental_dyadic :
    s i ≤ s j → (i : Set X) ⊆ (j : Set X) ∨ Disjoint (i : Set X) (j : Set X) :=
  GridStructure.fundamental_dyadic'


-- @@ L89-90 verbatim
lemma le_or_disjoint (h : s i ≤ s j) : i ≤ j ∨ Disjoint (i : Set X) (j : Set X) :=
  fundamental_dyadic h |>.imp (⟨·, h⟩) id


-- @@ L92-95 verbatim
lemma le_or_ge_or_disjoint : i ≤ j ∨ j ≤ i ∨ Disjoint (i : Set X) (j : Set X) := by
  rcases le_or_gt (s i) (s j) with h | h
  · have := le_or_disjoint h; tauto
  · have := le_or_disjoint h.le; tauto


-- @@ L97-98 verbatim
lemma le_or_ge_of_mem_of_mem {c : X} (mi : c ∈ i) (mj : c ∈ j) : i ≤ j ∨ j ≤ i :=
  (or_assoc.mpr le_or_ge_or_disjoint).resolve_right (not_disjoint_iff.mpr ⟨c, mi, mj⟩)


-- @@ L100-101 verbatim
lemma le_of_mem_of_mem (h : s i ≤ s j) {c : X} (mi : c ∈ i) (mj : c ∈ j) : i ≤ j :=
  ⟨(fundamental_dyadic h).resolve_right (not_disjoint_iff.mpr ⟨c, mi, mj⟩), h⟩


-- @@ L103-105 verbatim
lemma eq_or_disjoint (hs : s i = s j) : i = j ∨ Disjoint (i : Set X) (j : Set X) :=
  Or.elim (le_or_disjoint hs.le) (fun ij ↦ Or.elim (le_or_disjoint hs.ge)
     (fun ji ↦ Or.inl (le_antisymm ij ji)) (fun h ↦ Or.inr h.symm)) (fun h ↦ Or.inr h)


-- @@ L107-115 verbatim
lemma disjoint_of_not_le_not_le {i j : Grid X} (h : ¬i ≤ j) (h' : ¬j ≤ i) :
    Disjoint (i : Set X) j := by
  -- Assume wlog that s u₁ ≤ s u₂.
  obtain (hs | hs) := le_total (s i) (s j)
  · -- If u₁ and u₂ were not disjoint, we'd have J u₁ ⊆ J u₂, contradicting h.
    by_contra hndisjoint
    exact h <| (le_or_disjoint hs).resolve_right hndisjoint
  · by_contra hdisjoint
    exact h' <| (le_or_disjoint hs).resolve_right (fun a ↦ hdisjoint a.symm)


-- @@ L117-125 verbatim
lemma subset_of_notMem_Iic_of_not_disjoint (i : Grid X) (j : Grid X)
    (h : i ∉ Iic j)
    (notDisjoint : ¬ Disjoint (i : Set X) j) :
    (j : Set X) ⊆ i := by
  by_contra hdisj
  have : ¬(j ≤ i) := by
    rw [Grid.le_def]
    exact not_and.mpr fun a a_1 ↦ hdisj a
  exact notDisjoint (disjoint_of_not_le_not_le h this)


-- @@ L127-127 verbatim
lemma scale_mem_Icc : s i ∈ Icc (-S : ℤ) S := mem_Icc.mp (range_s_subset ⟨i, rfl⟩)


-- @@ L129-133 verbatim
lemma volume_coeGrid_pos (hD : 0 < D) : 0 < volume (i : Set X) := by
  have hD : 0 < (D : ℝ) ^ GridStructure.s i / 4 := by
    simp only [Nat.ofNat_pos, div_pos_iff_of_pos_right]
    exact zpow_pos (Nat.cast_pos'.mpr hD) _
  exact measure_pos_of_superset ball_subset_Grid (ne_of_gt (measure_ball_pos _ _ hD))


-- @@ L135-137 verbatim
@[aesop (rule_sets := [finiteness]) safe apply]
lemma volume_coeGrid_lt_top : volume (i : Set X) < ⊤ :=
  measure_lt_top_of_subset Grid_subset_ball measure_ball_ne_top


-- @@ L139-139 verbatim
namespace Grid


-- @@ L141-141 verbatim
protected lemma inj : Injective (fun i : Grid X ↦ ((i : Set X), s i)) := GridStructure.inj


-- @@ L143-144 verbatim
lemma le_topCube : i ≤ topCube :=
  ⟨subset_topCube, scale_mem_Icc.2.trans_eq s_topCube.symm⟩


-- @@ L146-146 verbatim
lemma isTop_topCube : IsTop (topCube : Grid X) := fun _ ↦ le_topCube


-- @@ L148-148 verbatim
lemma isMax_iff : IsMax i ↔ i = topCube := isTop_topCube.isMax_iff


-- @@ L150-151 verbatim
/-- The set `I ↦ Iᵒ` in the blueprint. -/
def int (i : Grid X) : Set X := ball (c i) (D ^ s i / 4)


-- @@ L153-153 verbatim
postfix:max "ᵒ" => Grid.int


-- @@ L155-156 verbatim
/-- An auxiliary measure used in the well-foundedness of `Ω` in Lemma `tile_structure`. -/
def opSize (i : Grid X) : ℕ := (S - s i).toNat


-- @@ L158-158 verbatim
lemma int_subset : i.int ⊆ i := ball_subset_Grid


-- @@ L160-160 verbatim
end Grid

-- @@ L161-161 verbatim
end Generic


-- @@ L163-163 verbatim
namespace Grid


-- @@ L165-165 verbatim
open scoped ShortVariables

-- @@ L166-167 verbatim
variable {X : Type*} [PseudoMetricSpace X] {a : ℕ} {q : ℝ} {K : X → X → ℂ}
  {σ₁ σ₂ : X → ℤ} {F G : Set X} [ProofData a q K σ₁ σ₂ F G]


-- @@ L169-169 verbatim
notation "dist_{" I "}" => @dist (WithFunctionDistance (c I) (D ^ s I / 4)) _

-- @@ L170-170 verbatim
notation "nndist_{" I "}" => @nndist (WithFunctionDistance (c I) (D ^ s I / 4)) _

-- @@ L171-171 verbatim
notation "edist_{" I "}" => @edist (WithFunctionDistance (c I) (D ^ s I / 4)) _

-- @@ L172-172 verbatim
notation "ball_{" I "}" => @ball (WithFunctionDistance (c I) (D ^ s I / 4)) _


-- @@ L174-174 verbatim
section GridManipulation


-- @@ L176-176 verbatim
variable [GridStructure X D κ S o]


-- @@ L178-180 verbatim
lemma c_mem_Grid {i : Grid X} : c i ∈ (i : Set X) := by
  obtain ⟨hD⟩ := NeZero.of_pos <| zero_lt_one.trans_le (one_le_realD _)
  exact mem_of_mem_of_subset (Metric.mem_ball_self (by positivity)) ball_subset_Grid


-- @@ L182-182 verbatim
lemma nonempty (i : Grid X) : (i : Set X).Nonempty := ⟨c i, c_mem_Grid⟩


-- @@ L184-186 verbatim
lemma scale_eq_scale_topCube_iff (i : Grid X) : s i = s (topCube : Grid X) ↔ i = topCube := by
  refine ⟨(eq_or_disjoint · |>.resolve_right ?_), (· ▸ rfl)⟩
  exact Set.not_disjoint_iff.mpr ⟨c i, c_mem_Grid, subset_topCube c_mem_Grid⟩


-- @@ L188-191 verbatim
lemma scale_lt_scale_topCube {i : Grid X} (hi : i ≠ topCube) : s i < s (topCube : Grid X) := by
  have : s i ≤ s topCube (X := X) := by rw [s, s_topCube]; exact scale_mem_Icc.2
  apply this.lt_of_ne
  rwa [ne_eq, scale_eq_scale_topCube_iff]


-- @@ L193-196 verbatim
lemma eq_topCube_of_S_eq_zero (i : Grid X) (hS : S = 0) : i = topCube := by
  have hsi : s i = 0                  := by simpa [hS] using scale_mem_Icc (i := i)
  have hst : s (topCube : Grid X) = 0 := by simpa [hS] using scale_mem_Icc (i := (topCube : Grid X))
  rw [← scale_eq_scale_topCube_iff, hsi, hst]


-- @@ L198-200 verbatim
lemma le_dyadic {i j k : Grid X} (h : s i ≤ s j) (li : k ≤ i) (lj : k ≤ j) : i ≤ j := by
  obtain ⟨c, mc⟩ := k.nonempty
  exact le_of_mem_of_mem h (mem_of_mem_of_subset mc li.1) (mem_of_mem_of_subset mc lj.1)


-- @@ L202-210 verbatim
@[simp] lemma lt_def {i j : Grid X} : i < j ↔ (i : Set X) ⊆ (j : Set X) ∧ s i < s j := by
  constructor <;> intro h
  · obtain ⟨a₁, a₂⟩ := h.le
    refine ⟨a₁, lt_of_le_of_ne a₂ ?_⟩
    by_contra a₃
    have l : i < i := h.trans_le (le_dyadic a₃.ge h.le le_rfl)
    rwa [lt_self_iff_false] at l
  · apply lt_of_le_of_ne (le_def.mpr ⟨h.1, h.2.le⟩)
    by_contra a; rw [a, lt_self_iff_false] at h; exact h.2


-- @@ L212-232 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma isMin_iff {i : Grid X} : IsMin i ↔ s i = - S := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · apply le_antisymm ?_ scale_mem_Icc.1
    contrapose! h
    have : -(S : ℤ) ∈ Ico (-(S : ℤ)) (s i) := by simp [h]
    have := Grid_subset_biUnion (i := i) (-S) this c_mem_Grid
    push _ ∈ _ at this
    rcases this with ⟨j, (hj : s j = -(S : ℤ)), h'j⟩
    have sji : s j < s i := by simpa [hj] using h
    have : (j : Set X) ⊆ i := by
      rcases fundamental_dyadic sji.le with hji | h_disj
      · exact hji
      · exact (disjoint_right.1 h_disj c_mem_Grid h'j).elim
    have : j < i := by simp [this, sji]
    exact this.not_isMin
  · intro j hj
    have : s i ≤ s j := by rw [h]; exact (scale_mem_Icc (i := j)).1
    rcases le_or_disjoint this with h' | h_disj
    · exact h'
    · exact False.elim (disjoint_right.1 h_disj c_mem_Grid (hj.1 c_mem_Grid))


-- @@ L234-249 verbatim
/-- There exists a unique successor of each non-maximal cube. -/
lemma exists_unique_succ (i : Grid X) (h : ¬IsMax i) :
    ∃! j ∈ Finset.univ, i < j ∧ ∀ j', i < j' → j ≤ j' := by
  simp_rw [Finset.mem_univ, true_and]
  classical let incs : Finset (Grid X) := { j | i < j }
  have ine : incs.Nonempty := by
    use topCube; simp_rw [incs, Finset.mem_filter_univ]
    exact lt_of_le_of_ne le_topCube (isMax_iff.not.mp h)
  obtain ⟨j, mj, hj⟩ := incs.exists_minimal ine
  simp only [incs, Finset.mem_filter_univ] at mj hj
  replace hj : ∀ (x : Grid X), i < x → j ≤ x := fun x mx ↦ by
    rcases lt_or_ge (s x) (s j) with c | c
    · refine (eq_of_le_of_not_lt (le_dyadic c.le mx.le mj.le) ?_).symm.le
      exact not_lt_iff_le_imp_ge.mpr (hj mx)
    · exact le_dyadic c mj.le mx.le
  use j, ⟨mj, hj⟩, fun k ⟨hk₁, hk₂⟩ ↦ le_antisymm (hk₂ j mj) (hj k hk₁)


-- @@ L251-254 verbatim
open Classical in
/-- If `i` is not a maximal element, this is the (unique) minimal element greater than i.
This is not a `SuccOrder` since an element can be the successor of multiple other elements. -/
def succ (i : Grid X) : Grid X := if h : IsMax i then i else Finset.choose (hp := exists_unique_succ i h)


-- @@ L256-256 verbatim
variable {i j : Grid X}


-- @@ L258-260 verbatim
lemma succ_spec (h : ¬IsMax i) : i < i.succ ∧ ∀ j, i < j → i.succ ≤ j := by
  simp only [succ, h, dite_false]
  classical exact Finset.choose_spec (hp := exists_unique_succ i h).2


-- @@ L262-264 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma succ_unique (h : ¬IsMax i) : i < j → (∀ j', i < j' → j ≤ j') → i.succ = j := fun k₁ k₂ ↦
  ((exists_unique_succ i h).unique ⟨by simp, k₁, k₂⟩ ⟨by simp, succ_spec h⟩).symm


-- @@ L266-270 verbatim
set_option backward.isDefEq.respectTransparency false in
lemma le_succ : i ≤ i.succ := by
  by_cases h : IsMax i
  · simp [h, succ]
  · exact (succ_spec h).1.le


-- @@ L272-274 verbatim
lemma max_of_le_succ : i.succ ≤ i → IsMax i := fun h ↦ by
  contrapose! h; by_contra! k; have l := (succ_spec h).1.trans_le k
  rwa [lt_self_iff_false] at l


-- @@ L276-280 verbatim
lemma not_isMax_of_scale_lt {j W : Grid X} (h : s j < s W) : ¬IsMax j := by
  rw [Grid.isMax_iff]
  intro top
  rw [top, show s topCube = ↑S by exact s_topCube (X := X)] at h
  linarith [(scale_mem_Icc (i := W)).2]


-- @@ L282-285 verbatim
lemma succ_le_of_lt (h : i < j) : i.succ ≤ j := by
  by_cases k : IsMax i
  · simp only [k, succ, dite_true]; exact h.le
  · exact (succ_spec k).2 j h


-- @@ L287-293 verbatim
lemma exists_containing_subcube (l : ℤ) (h : l ∈ Icc (-S : ℤ) (s i)) {x : X} (mx : x ∈ i) :
    ∃ j, s j = l ∧ x ∈ j := by
  obtain ⟨lb, ub⟩ := h
  rcases ub.eq_or_lt with ub | ub
  · exact ⟨i, ub.symm, mx⟩
  · simpa [mem_iUnion₂, mem_preimage, mem_singleton_iff, exists_prop] using!
      Grid_subset_biUnion l ⟨lb, ub⟩ mx


-- @@ L295-305 verbatim
lemma exists_supercube (l : ℤ) (h : l ∈ Icc (s i) S) : ∃ j, s j = l ∧ i ≤ j := by
  obtain ⟨lb, ub⟩ := h
  rcases ub.eq_or_lt with ub | ub; · exact ⟨topCube, by simpa [ub] using! s_topCube, le_topCube⟩
  obtain ⟨x, hx⟩ := i.nonempty
  have bound_i : -S ≤ s i ∧ s i ≤ S := scale_mem_Icc
  have ts := Grid_subset_biUnion (X := X) (i := topCube) l
    (by rw [s_topCube, mem_Ico]; omega)
  have := mem_of_mem_of_subset hx ((le_topCube (i := i)).1.trans ts)
  push _ ∈ _ at this
  obtain ⟨j, (sj : s j = l), mj⟩ := this; use j, sj
  exact le_of_mem_of_mem (by lia) hx mj


-- @@ L307-313 verbatim
lemma exists_sandwiched (h : i ≤ j) (l : ℤ) (hl : l ∈ Icc (s i) (s j)) :
    ∃ k, s k = l ∧ i ≤ k ∧ k ≤ j := by
  have bound_q : -S ≤ s j ∧ s j ≤ S := scale_mem_Icc
  rw [mem_Icc] at hl
  obtain ⟨K, sK, lbK⟩ := exists_supercube l (by change s i ≤ _ ∧ _; lia)
  use K, sK, lbK
  exact le_dyadic (by lia) lbK h


-- @@ L315-322 verbatim
lemma scale_succ (h : ¬IsMax i) : s i.succ = s i + 1 := by
  obtain ⟨h₁, h₂⟩ := succ_spec h
  rw [lt_def] at h₁; apply le_antisymm _ (by lia)
  by_contra! h₀
  obtain ⟨z, hz₁, hz₂, hz₃⟩ :=
    exists_sandwiched (le_succ (i := i)) (s i + 1) (by rw [mem_Icc]; lia)
  have l := (lt_def.mpr ⟨hz₃.1, hz₁.symm ▸ h₀⟩).trans_le (h₂ z (lt_def.mpr ⟨hz₂.1, by lia⟩))
  rwa [lt_self_iff_false] at l


-- @@ L324-328 verbatim
lemma exists_scale_succ {j W : Grid X} (h : s j < s W) : ∃ J, j ≤ J ∧ s J = s j + 1 := by
  use j.succ
  constructor
  · exact Grid.le_succ
  · exact Grid.scale_succ (Grid.not_isMax_of_scale_lt h)


-- @@ L330-335 verbatim
lemma opSize_succ_lt (h : ¬IsMax i) : i.succ.opSize < i.opSize := by
  simp only [opSize, Int.lt_toNat]
  have : s i.succ ≤ S := (mem_Icc.mp scale_mem_Icc).2
  replace : 0 ≤ S - s i.succ := by lia
  rw [Int.toNat_of_nonneg this, scale_succ h]
  lia


-- @@ L337-344 verbatim
@[elab_as_elim]
lemma induction (P : Grid X → Prop) (base : ∀ i, IsMax i → P i)
    (ind : ∀ i, ¬IsMax i → P i.succ → P i) : ∀ i, P i := fun i ↦ by
  by_cases h : IsMax i
  · exact base i h
  · have := opSize_succ_lt h
    exact ind i h (induction P base ind i.succ)
termination_by i => i.opSize


-- @@ L346-351 verbatim
lemma succ_def (h : ¬IsMax i) : i.succ = j ↔ i ≤ j ∧ s j = s i + 1 := by
  refine ⟨fun k ↦ by subst k; exact ⟨le_succ, scale_succ h⟩, fun ⟨h₁, _⟩ ↦ ?_⟩
  replace h₁ : i < j := lt_def.mpr ⟨h₁.1, by lia⟩
  refine succ_unique h h₁ fun j' hj' ↦ ?_
  have : s i < s j' := (lt_def.mp hj').2
  exact le_dyadic (by lia) h₁.le hj'.le


-- @@ L353-353 verbatim
/-! ## Maximal elements of finsets of dyadic cubes -/


-- @@ L355-356 verbatim
open Classical in
def maxCubes (s : Finset (Grid X)) : Finset (Grid X) := s.filter fun i ↦ ∀ j ∈ s, i ≤ j → i = j


-- @@ L358-360 verbatim
lemma exists_maximal_supercube {s : Finset (Grid X)} (hi : i ∈ s) : ∃ j ∈ maxCubes s, i ≤ j := by
  obtain ⟨j, lj, maxj⟩ := s.exists_le_maximal hi; rw [maximal_iff] at maxj
  simp_rw [maxCubes, Finset.mem_filter]; exact ⟨j, maxj, lj⟩


-- @@ L362-366 verbatim
lemma maxCubes_pairwiseDisjoint {s : Finset (Grid X)} :
    PairwiseDisjoint (SetLike.coe (maxCubes s)) fun i ↦ (i : Set X) := fun i mi j mj hn ↦ by
  simp only [maxCubes, Finset.coe_filter, mem_ofPred_eq] at mi mj
  exact le_or_ge_or_disjoint.resolve_left ((mi.2 j mj.1).mt hn)
    |>.resolve_left ((mj.2 i mi.1).mt hn.symm)


-- @@ L368-368 verbatim
end GridManipulation


-- @@ L370-371 verbatim
/-- The constant appearing in Lemma 2.1.2, `2 ^ {-95a}`. -/
def _root_.C2_1_2 (a : ℕ) : ℝ := 2 ^ ((-𝕔 + 5) * a : ℝ)


-- @@ L373-382 verbatim
include q K σ₁ σ₂ F G in
variable (X) in
lemma _root_.C2_1_2_le_inv_256 : C2_1_2 a ≤ 1 / 256 := by
  rw [C2_1_2, show (1 / 256 : ℝ) = 2 ^ (-8 : ℝ) by norm_num,
    Real.rpow_le_rpow_left_iff one_lt_two, le_neg]
  simp only [add_mul, neg_mul, neg_add_rev, neg_neg, le_neg_add_iff_add_le]
  norm_cast
  have := four_le_a X
  have : 7 * a ≤ 𝕔 * a := by gcongr; exact seven_le_c
  linarith


-- @@ L384-387 verbatim
include q K σ₁ σ₂ F G in
variable (X) in
lemma _root_.C2_1_2_le_one : C2_1_2 a ≤ 1 :=
  (C2_1_2_le_inv_256 X).trans <| by norm_num


-- @@ L389-392 verbatim
include q K σ₁ σ₂ F G in
variable (X) in
lemma _root_.C2_1_2_lt_one : C2_1_2 a < 1 :=
  (C2_1_2_le_inv_256 X).trans_lt <| by norm_num


-- @@ L394-394 verbatim
variable [GridStructure X D κ S o]


-- @@ L396-431 expanded
/-- Stronger version of Lemma 2.1.2. -/
lemma dist_strictMono {I J : Grid X} (hpq : I < J) {f g : Θ X} :
    (@dist (WithFunctionDistance (c I) (D ^ s I / 4)) _) f g ≤
      C2_1_2 a * (@dist (WithFunctionDistance (c J) (D ^ s J / 4)) _) f g :=
  by
  calc
    _ ≤ (@dist (WithFunctionDistance (c I) (4 * D ^ s I)) _) f g :=
      cdist_mono (ball_subset_ball (by simp_rw [div_eq_inv_mul, defaultD]; gcongr; norm_num))
    _ ≤ 2 ^ (-𝕔 * (a : ℝ)) * (@dist (WithFunctionDistance (c I) (4 * D ^ (s I + 1))) _) f g :=
      by
      rw [← div_le_iff₀' (by positivity), neg_mul, Real.rpow_neg zero_le_two, div_inv_eq_mul,
        mul_comm]
      convert! le_cdist_iterate (x := c I) (r := 4 * D ^ s I) (by positivity) f g (𝕔 * a) using 1
      · norm_cast
      · apply dist_congr rfl
        have : (defaultA a : ℝ) ^ (𝕔 * a) = D :=
          by
          simp only [defaultD, Nat.cast_pow, Nat.cast_ofNat]
          rw [← pow_mul]; congr 1; ring
        rw [this, zpow_add_one₀ (realD_pos a).ne']; ring
    _ ≤ 2 ^ (-𝕔 * (a : ℝ)) * (@dist (WithFunctionDistance (c I) (4 * D ^ s J)) _) f g :=
      by
      gcongr
      have : s I < s J := (Grid.lt_def.mp hpq).2
      apply cdist_mono
      gcongr
      · exact one_le_realD _
      · lia
    _ ≤ 2 ^ (-𝕔 * (a : ℝ)) * (@dist (WithFunctionDistance (c J) (8 * D ^ s J)) _) f g :=
      by
      gcongr
      have : c I ∈ ball (c J) (4 * D ^ s J) :=
        mem_of_mem_of_subset c_mem_Grid ((Grid.lt_def.mp hpq).1.trans Grid_subset_ball)
      rw [mem_ball] at this
      exact cdist_mono (ball_subset_ball' (by linarith))
    _ ≤ 2 ^ (-𝕔 * (a : ℝ) + 5 * a) * (@dist (WithFunctionDistance (c J) (D ^ s J / 4)) _) f g :=
      by
      rw [Real.rpow_add zero_lt_two, mul_assoc]
      gcongr
      rw [show (2 : ℝ) ^ (5 * (a : ℝ)) = (defaultA a) ^ 5 by norm_cast; ring]
      convert! cdist_le_iterate _ f g 5 using 1
      · exact dist_congr rfl (by ring)
      · have := one_le_realD a; positivity
    _ = _ := by congr 1; rw [C2_1_2, ← add_mul]


-- @@ L433-437 expanded
/-- Weaker version of Lemma 2.1.2. -/
lemma dist_mono {I J : Grid X} (hpq : I ≤ J) {f g : Θ X} :
    (@dist (WithFunctionDistance (c I) (D ^ s I / 4)) _) f g ≤
      (@dist (WithFunctionDistance (c J) (D ^ s J / 4)) _) f g :=
  by
  rcases hpq.eq_or_lt with h | h
  · subst h; rfl
  · exact (Grid.dist_strictMono h).trans (mul_le_of_le_one_left dist_nonneg (C2_1_2_le_one X))


-- @@ L439-454 expanded
lemma dist_strictMono_iterate {I J : Grid X} {d : ℕ} (hij : I ≤ J) (hs : s I + d = s J)
    {f g : Θ X} :
    (@dist (WithFunctionDistance (c I) (D ^ s I / 4)) _) f g ≤
      C2_1_2 a ^ d * (@dist (WithFunctionDistance (c J) (D ^ s J / 4)) _) f g :=
  by
  induction d generalizing I J with
  | zero => simpa using dist_mono hij
  | succ d
    ih =>
    obtain ⟨K, sK, IK, KJ⟩ := exists_sandwiched hij (s I + d) (by rw [mem_Icc]; lia)
    replace KJ : K < J := by rw [Grid.lt_def]; exact ⟨KJ.1, by lia⟩
    calc
      _ ≤ C2_1_2 a ^ d * (@dist (WithFunctionDistance (c K) (D ^ s K / 4)) _) f g := ih IK sK.symm
      _ ≤ C2_1_2 a ^ d * (C2_1_2 a * (@dist (WithFunctionDistance (c J) (D ^ s J / 4)) _) f g) :=
        by
        gcongr
        · rw [C2_1_2]; positivity
        · exact dist_strictMono KJ
      _ = _ := by
        ring
          -- Version of `dist_strictMono_iterate` with `d` in `ℤ`


-- @@ L455-458 expanded
lemma dist_strictMono_iterate' {I J : Grid X} {d : ℤ} (hd : d ≥ 0) (hij : I ≤ J)
    (hs : s I + d = s J) {f g : Θ X} :
    (@dist (WithFunctionDistance (c I) (D ^ s I / 4)) _) f g ≤
      C2_1_2 a ^ d * (@dist (WithFunctionDistance (c J) (D ^ s J / 4)) _) f g :=
  by
  rw [← Int.toNat_of_nonneg hd] at hs ⊢
  exact dist_strictMono_iterate hij hs


-- @@ L460-462 verbatim
lemma dist_c_le_of_subset {J J' : Grid X} (subset : (J : Set X) ⊆ J') :
    dist (c J) (c J') < 4 * D ^ s J' :=
  Grid_subset_ball (subset Grid.c_mem_Grid)


-- @@ L464-464 verbatim
end Grid
