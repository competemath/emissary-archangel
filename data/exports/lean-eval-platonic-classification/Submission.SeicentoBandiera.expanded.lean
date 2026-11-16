import Submission.SeicentoVertici
import Submission.MacchinaBandiere
import Submission.FacciaArgmax
import Submission.PerturbazioneFinita


-- @@ L6-6 verbatim
open Set Metric PlatoniciL3 Real

-- @@ L7-7 verbatim
open scoped RealInnerProductSpace


-- @@ L9-9 verbatim
noncomputable section


-- @@ L11-11 verbatim
namespace LeanEval.Geometry.PlatonicClassification


-- @@ L13-13 verbatim
open ConvexPolytope


-- @@ L15-15 verbatim
private abbrev E4 := E 4


-- @@ L17-17 verbatim
private def segniC1 : Fin 3 → Bool := ![true, true, true]

-- @@ L18-18 verbatim
private def segniC2 : Fin 3 → Bool := ![true, true, false]


-- @@ L20-26 verbatim
/-- The even three-cycle `(1 3 2)` used by the fourth flag vertex. -/
def sigma3_600 : alternatingGroup (Fin 4) :=
  ⟨Equiv.swap 1 2 * Equiv.swap 1 3, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap (by omega : (1 : Fin 4) ≠ 2),
      Equiv.Perm.sign_swap (by omega : (1 : Fin 4) ≠ 3)]
    norm_num⟩


-- @@ L28-28 verbatim
def e1_600 : E4 := vertA 0 true

-- @@ L29-29 verbatim
def c1_600 : E4 := vertC 1 segniC1

-- @@ L30-30 verbatim
def c2_600 : E4 := vertC 1 segniC2

-- @@ L31-31 verbatim
def c3_600 : E4 := vertC sigma3_600 segniC1


-- @@ L33-78 verbatim
private theorem flag_vertex_coordinates :
    (∀ j : Fin 4, e1_600 j = ![(1 : ℝ), 0, 0, 0] j) ∧
    (∀ j : Fin 4, c1_600 j =
      ![aureo / 2, (1 : ℝ) / 2, (aureo - 1) / 2, 0] j) ∧
    (∀ j : Fin 4, c2_600 j =
      ![aureo / 2, (1 : ℝ) / 2, -(aureo - 1) / 2, 0] j) ∧
    (∀ j : Fin 4, c3_600 j =
      ![aureo / 2, (aureo - 1) / 2, 0, (1 : ℝ) / 2] j) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j
    fin_cases j <;> norm_num [e1_600, vertA_apply]
  · intro j
    fin_cases j
    · simpa [c1_600, segniC1, segnoC, baseC] using
        (vertC_at (1 : alternatingGroup (Fin 4)) segniC1 (0 : Fin 4))
    · simpa [c1_600, segniC1, segnoC, baseC] using
        (vertC_at (1 : alternatingGroup (Fin 4)) segniC1 (1 : Fin 4))
    · simpa [c1_600, segniC1, segnoC, baseC] using
        (vertC_at (1 : alternatingGroup (Fin 4)) segniC1 (2 : Fin 4))
    · simpa [c1_600, segniC1, segnoC, baseC] using
        (vertC_at (1 : alternatingGroup (Fin 4)) segniC1 (3 : Fin 4))
  · intro j
    fin_cases j
    · simpa [c2_600, segniC2, segnoC, baseC] using
        (vertC_at (1 : alternatingGroup (Fin 4)) segniC2 (0 : Fin 4))
    · simpa [c2_600, segniC2, segnoC, baseC] using
        (vertC_at (1 : alternatingGroup (Fin 4)) segniC2 (1 : Fin 4))
    · convert (vertC_at (1 : alternatingGroup (Fin 4)) segniC2
        (2 : Fin 4)) using 1 <;>
        simp [c2_600, segniC2, segnoC, baseC] <;> ring
    · simpa [c2_600, segniC2, segnoC, baseC] using
        (vertC_at (1 : alternatingGroup (Fin 4)) segniC2 (3 : Fin 4))
  · intro j
    fin_cases j
    · simpa [c3_600, sigma3_600, segniC1, segnoC, baseC,
        Equiv.swap_apply_def] using
        (vertC_at sigma3_600 segniC1 (0 : Fin 4))
    · simpa [c3_600, sigma3_600, segniC1, segnoC, baseC,
        Equiv.swap_apply_def] using
        (vertC_at sigma3_600 segniC1 (2 : Fin 4))
    · simpa [c3_600, sigma3_600, segniC1, segnoC, baseC,
        Equiv.swap_apply_def] using
        (vertC_at sigma3_600 segniC1 (3 : Fin 4))
    · simpa [c3_600, sigma3_600, segniC1, segnoC, baseC,
        Equiv.swap_apply_def] using
        (vertC_at sigma3_600 segniC1 (1 : Fin 4))


-- @@ L80-83 verbatim
@[simp] private theorem e1_600_coord0 : e1_600 0 = 1 := by
  rw [flag_vertex_coordinates.1 0]
  change (1 : ℝ) = 1
  rfl


-- @@ L85-88 verbatim
@[simp] private theorem e1_600_coord1 : e1_600 1 = 0 := by
  rw [flag_vertex_coordinates.1 1]
  change (0 : ℝ) = 0
  rfl


-- @@ L90-93 verbatim
@[simp] private theorem e1_600_coord2 : e1_600 2 = 0 := by
  rw [flag_vertex_coordinates.1 2]
  change (0 : ℝ) = 0
  rfl


-- @@ L95-98 verbatim
@[simp] private theorem e1_600_coord3 : e1_600 3 = 0 := by
  rw [flag_vertex_coordinates.1 3]
  change (0 : ℝ) = 0
  rfl


-- @@ L100-103 verbatim
@[simp] private theorem c1_600_coord0 : c1_600 0 = aureo / 2 := by
  rw [flag_vertex_coordinates.2.1 0]
  change aureo / 2 = aureo / 2
  rfl


-- @@ L105-108 verbatim
@[simp] private theorem c1_600_coord1 : c1_600 1 = 1 / 2 := by
  rw [flag_vertex_coordinates.2.1 1]
  change (1 : ℝ) / 2 = 1 / 2
  rfl


-- @@ L110-113 verbatim
@[simp] private theorem c1_600_coord2 : c1_600 2 = (aureo - 1) / 2 := by
  rw [flag_vertex_coordinates.2.1 2]
  change (aureo - 1) / 2 = (aureo - 1) / 2
  rfl


-- @@ L115-118 verbatim
@[simp] private theorem c1_600_coord3 : c1_600 3 = 0 := by
  rw [flag_vertex_coordinates.2.1 3]
  change (0 : ℝ) = 0
  rfl


-- @@ L120-123 verbatim
@[simp] private theorem c2_600_coord0 : c2_600 0 = aureo / 2 := by
  rw [flag_vertex_coordinates.2.2.1 0]
  change aureo / 2 = aureo / 2
  rfl


-- @@ L125-128 verbatim
@[simp] private theorem c2_600_coord1 : c2_600 1 = 1 / 2 := by
  rw [flag_vertex_coordinates.2.2.1 1]
  change (1 : ℝ) / 2 = 1 / 2
  rfl


-- @@ L130-133 verbatim
@[simp] private theorem c2_600_coord2 : c2_600 2 = -(aureo - 1) / 2 := by
  rw [flag_vertex_coordinates.2.2.1 2]
  change -(aureo - 1) / 2 = -(aureo - 1) / 2
  rfl


-- @@ L135-138 verbatim
@[simp] private theorem c2_600_coord3 : c2_600 3 = 0 := by
  rw [flag_vertex_coordinates.2.2.1 3]
  change (0 : ℝ) = 0
  rfl


-- @@ L140-143 verbatim
@[simp] private theorem c3_600_coord0 : c3_600 0 = aureo / 2 := by
  rw [flag_vertex_coordinates.2.2.2 0]
  change aureo / 2 = aureo / 2
  rfl


-- @@ L145-148 verbatim
@[simp] private theorem c3_600_coord1 : c3_600 1 = (aureo - 1) / 2 := by
  rw [flag_vertex_coordinates.2.2.2 1]
  change (aureo - 1) / 2 = (aureo - 1) / 2
  rfl


-- @@ L150-153 verbatim
@[simp] private theorem c3_600_coord2 : c3_600 2 = 0 := by
  rw [flag_vertex_coordinates.2.2.2 2]
  change (0 : ℝ) = 0
  rfl


-- @@ L155-158 verbatim
@[simp] private theorem c3_600_coord3 : c3_600 3 = 1 / 2 := by
  rw [flag_vertex_coordinates.2.2.2 3]
  change (1 : ℝ) / 2 = 1 / 2
  rfl


-- @@ L160-163 verbatim
def l3_600 : E4 →L[ℝ] ℝ :=
  (1 + 3 * aureo / 2) • EuclideanSpace.proj (0 : Fin 4) +
    (aureo ^ 2 / 2) • EuclideanSpace.proj (1 : Fin 4) +
    (1 / 2 : ℝ) • EuclideanSpace.proj (3 : Fin 4)


-- @@ L165-168 verbatim
private theorem l3_600_apply (x : E4) :
    l3_600 x = (1 + 3 * aureo / 2) * x 0 +
      (aureo ^ 2 / 2) * x 1 + (1 / 2 : ℝ) * x 3 := by
  simp [l3_600]


-- @@ L170-170 verbatim
def generatoriF0_600 : Finset E4 := {e1_600}

-- @@ L171-171 verbatim
def generatoriF1_600 : Finset E4 := {e1_600, c1_600}

-- @@ L172-172 verbatim
def generatoriF2_600 : Finset E4 := {e1_600, c1_600, c2_600}

-- @@ L173-173 verbatim
def generatoriF3_600 : Finset E4 := {e1_600, c1_600, c2_600, c3_600}


-- @@ L175-175 verbatim
def F0_600 : Set E4 := convexHull ℝ (generatoriF0_600 : Set E4)

-- @@ L176-176 verbatim
def F1_600 : Set E4 := convexHull ℝ (generatoriF1_600 : Set E4)

-- @@ L177-177 verbatim
def F2_600 : Set E4 := convexHull ℝ (generatoriF2_600 : Set E4)

-- @@ L178-178 verbatim
def F3_600 : Set E4 := convexHull ℝ (generatoriF3_600 : Set E4)


-- @@ L180-190 verbatim
private theorem flag_vertices_mem :
    e1_600 ∈ seicentoVertici ∧ c1_600 ∈ seicentoVertici ∧
      c2_600 ∈ seicentoVertici ∧ c3_600 ∈ seicentoVertici := by
  classical
  simp only [seicentoVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and]
  refine ⟨Or.inl (Or.inl ⟨(0, true), rfl⟩),
    Or.inr ?_, Or.inr ?_, Or.inr ?_⟩
  · exact ⟨(1, segniC1), rfl⟩
  · exact ⟨(1, segniC2), rfl⟩
  · exact ⟨(sigma3_600, segniC1), rfl⟩


-- @@ L192-206 verbatim
private theorem l3_flag_values :
    l3_600 e1_600 = 1 + 3 * aureo / 2 ∧
      l3_600 c1_600 = 1 + 3 * aureo / 2 ∧
      l3_600 c2_600 = 1 + 3 * aureo / 2 ∧
      l3_600 c3_600 = 1 + 3 * aureo / 2 := by
  rw [l3_600_apply, l3_600_apply, l3_600_apply, l3_600_apply]
  rw [flag_vertex_coordinates.1 0, flag_vertex_coordinates.1 1,
    flag_vertex_coordinates.1 3, flag_vertex_coordinates.2.1 0,
    flag_vertex_coordinates.2.1 1, flag_vertex_coordinates.2.1 3,
    flag_vertex_coordinates.2.2.1 0, flag_vertex_coordinates.2.2.1 1,
    flag_vertex_coordinates.2.2.1 3,
    flag_vertex_coordinates.2.2.2 0, flag_vertex_coordinates.2.2.2 1,
    flag_vertex_coordinates.2.2.2 3]
  simp
  constructor <;> nlinarith [aureo_sq]


-- @@ L208-212 verbatim
private theorem l3_vertA_le (i : Fin 4) (b : Bool) :
    l3_600 (vertA i b) ≤ 1 + 3 * aureo / 2 := by
  fin_cases i <;> cases b <;>
    norm_num [l3_600_apply, vertA_apply, Fin.ext_iff] <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]


-- @@ L214-220 verbatim
private theorem l3_vertB_lt (s : Fin 4 → Bool) :
    l3_600 (vertB s) < 1 + 3 * aureo / 2 := by
  classical
  simp only [l3_600_apply, vertB_apply]
  cases h0 : s 0 <;> cases h1 : s 1 <;> cases h3 : s 3 <;>
    norm_num <;>
    nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]


-- @@ L222-231 verbatim
private theorem vertC_coord_le_base (σ : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) (j : Fin 4) :
    vertC σ s j ≤ baseC ((σ : Equiv.Perm (Fin 4)).symm j) := by
  rw [vertC_apply]
  have hb := baseC_nonneg ((σ : Equiv.Perm (Fin 4)).symm j)
  have hs_all (k : Fin 4) : segnoC s k ≤ 1 := by
    fin_cases k <;>
      simp [segnoC] <;> split_ifs <;> norm_num
  have hs := hs_all ((σ : Equiv.Perm (Fin 4)).symm j)
  nlinarith


-- @@ L233-258 verbatim
set_option maxHeartbeats 1000000 in
private theorem l3_vertC_le (σ : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool) :
    l3_600 (vertC σ s) ≤ 1 + 3 * aureo / 2 := by
  have h0 := vertC_coord_le_base σ s (0 : Fin 4)
  have h1 := vertC_coord_le_base σ s (1 : Fin 4)
  have h3 := vertC_coord_le_base σ s (3 : Fin 4)
  have hk0 := Equiv.apply_symm_apply (σ : Equiv.Perm (Fin 4)) (0 : Fin 4)
  have hk1 := Equiv.apply_symm_apply (σ : Equiv.Perm (Fin 4)) (1 : Fin 4)
  have hk3 := Equiv.apply_symm_apply (σ : Equiv.Perm (Fin 4)) (3 : Fin 4)
  generalize he0 : (σ : Equiv.Perm (Fin 4)).symm 0 = k0 at h0 hk0
  generalize he1 : (σ : Equiv.Perm (Fin 4)).symm 1 = k1 at h1 hk1
  generalize he3 : (σ : Equiv.Perm (Fin 4)).symm 3 = k3 at h3 hk3
  rw [l3_600_apply]
  fin_cases σ
  all_goals fin_cases k0
  all_goals norm_num [Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    Fin.ext_iff] at hk0
  all_goals fin_cases k1
  all_goals norm_num [Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    Fin.ext_iff] at hk1
  all_goals fin_cases k3
  all_goals norm_num [Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    Fin.ext_iff] at hk3
  all_goals norm_num [baseC] at h0 h1 h3 ⊢
  all_goals nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]


-- @@ L260-266 verbatim
private theorem l3_vertA_eq (i : Fin 4) (b : Bool)
    (h : l3_600 (vertA i b) = 1 + 3 * aureo / 2) :
    vertA i b = e1_600 := by
  fin_cases i <;> cases b <;>
    norm_num [l3_600_apply, vertA_apply, Fin.ext_iff] at h <;>
    try nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]
  rfl


-- @@ L268-324 verbatim
set_option maxHeartbeats 2000000 in
private theorem l3_vertC_eq (σ : alternatingGroup (Fin 4))
    (s : Fin 3 → Bool)
    (h : l3_600 (vertC σ s) = 1 + 3 * aureo / 2) :
    vertC σ s = c1_600 ∨ vertC σ s = c2_600 ∨ vertC σ s = c3_600 := by
  rw [l3_600_apply, vertC_apply, vertC_apply, vertC_apply] at h
  have hk0 := Equiv.apply_symm_apply (σ : Equiv.Perm (Fin 4)) (0 : Fin 4)
  have hk1 := Equiv.apply_symm_apply (σ : Equiv.Perm (Fin 4)) (1 : Fin 4)
  have hk2 := Equiv.apply_symm_apply (σ : Equiv.Perm (Fin 4)) (2 : Fin 4)
  have hk3 := Equiv.apply_symm_apply (σ : Equiv.Perm (Fin 4)) (3 : Fin 4)
  generalize he0 : (σ : Equiv.Perm (Fin 4)).symm 0 = k0 at h hk0
  generalize he1 : (σ : Equiv.Perm (Fin 4)).symm 1 = k1 at h hk1
  generalize he2 : (σ : Equiv.Perm (Fin 4)).symm 2 = k2 at hk2
  generalize he3 : (σ : Equiv.Perm (Fin 4)).symm 3 = k3 at h hk3
  fin_cases σ
  all_goals fin_cases k0
  all_goals norm_num [Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    Fin.ext_iff] at hk0
  all_goals fin_cases k1
  all_goals norm_num [Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    Fin.ext_iff] at hk1
  all_goals fin_cases k2
  all_goals norm_num [Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    Fin.ext_iff] at hk2
  all_goals fin_cases k3
  all_goals norm_num [Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    Fin.ext_iff] at hk3
  all_goals
    cases hs0 : s 0 <;> cases hs1 : s 1 <;> cases hs2 : s 2 <;>
      norm_num [segnoC, baseC, hs0, hs1, hs2] at h
  all_goals try nlinarith [aureo_sq, aureo_bounds.1, aureo_bounds.2]
  all_goals
    first
    | left
      ext j
      fin_cases j <;>
        simp [vertC_apply, he0, he1, he2, he3, hs0, hs1, hs2,
          segnoC, baseC, c1_600, c2_600, c3_600, segniC1, segniC2,
          sigma3_600, ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv,
          Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff]
      done
    | right; left
      ext j
      fin_cases j <;>
        simp [vertC_apply, he0, he1, he2, he3, hs0, hs1, hs2,
          segnoC, baseC, c1_600, c2_600, c3_600, segniC1, segniC2,
          sigma3_600, ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv,
          Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff]
      done
    | right; right
      ext j
      fin_cases j <;>
        simp [vertC_apply, he0, he1, he2, he3, hs0, hs1, hs2,
          segnoC, baseC, c1_600, c2_600, c3_600, segniC1, segniC2,
          sigma3_600, ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv,
          Equiv.Perm.mul_apply, Equiv.swap_apply_def, Fin.ext_iff]
      done


-- @@ L326-339 verbatim
private theorem l3_vertices_le :
    ∀ v ∈ (seicento.vertices : Set E4),
      l3_600 v ≤ 1 + 3 * aureo / 2 := by
  intro v hv
  have hv' : v ∈ seicentoVertici := by exact_mod_cast hv
  simp only [seicentoVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hv'
  rcases hv' with (⟨p, hp⟩ | ⟨s, hs⟩) | ⟨p, hp⟩
  · rw [← hp]
    exact l3_vertA_le p.1 p.2
  · rw [← hs]
    exact (l3_vertB_lt s).le
  · rw [← hp]
    exact l3_vertC_le p.1 p.2


-- @@ L341-371 verbatim
private theorem argmax_l3_600 :
    {x ∈ (seicento.vertices : Set E4) |
      l3_600 x = 1 + 3 * aureo / 2} =
      (generatoriF3_600 : Set E4) := by
  ext x
  rw [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hx, hl⟩
    have hx' : x ∈ seicentoVertici := by exact_mod_cast hx
    simp only [seicentoVertici, Finset.mem_union, Finset.mem_image,
      Finset.mem_univ, true_and] at hx'
    rcases hx' with (⟨p, hp⟩ | ⟨s, hs⟩) | ⟨p, hp⟩
    · rw [← hp] at hl ⊢
      rw [l3_vertA_eq p.1 p.2 hl]
      simp [generatoriF3_600]
    · rw [← hs] at hl
      have := l3_vertB_lt s
      linarith
    · rw [← hp] at hl ⊢
      rcases l3_vertC_eq p.1 p.2 hl with h | h | h <;> rw [h] <;>
        simp [generatoriF3_600]
  · intro hx
    have hc : x = e1_600 ∨ x = c1_600 ∨ x = c2_600 ∨ x = c3_600 := by
      simpa [generatoriF3_600] using hx
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨by exact_mod_cast flag_vertices_mem.1, l3_flag_values.1⟩
    · exact ⟨by exact_mod_cast flag_vertices_mem.2.1, l3_flag_values.2.1⟩
    · exact ⟨by exact_mod_cast flag_vertices_mem.2.2.1,
        l3_flag_values.2.2.1⟩
    · exact ⟨by exact_mod_cast flag_vertices_mem.2.2.2,
        l3_flag_values.2.2.2⟩


-- @@ L373-375 verbatim
private theorem l3_toSet_le :
    ∀ x ∈ seicento.toSet, l3_600 x ≤ 1 + 3 * aureo / 2 :=
  le_su_toSet seicento l3_600 l3_vertices_le


-- @@ L377-416 verbatim
private theorem isExposed_argmax_600 (s : Finset E4) (l : E4 →L[ℝ] ℝ)
    (c : ℝ) (hs : s.Nonempty)
    (harg : {x ∈ (seicento.vertices : Set E4) | l x = c} = (s : Set E4))
    (hle : ∀ x ∈ seicento.toSet, l x ≤ c) :
    IsExposed ℝ seicento.toSet (convexHull ℝ (s : Set E4)) := by
  intro _
  have hsV : (s : Set E4) ⊆ (seicento.vertices : Set E4) := by
    intro x hx
    rw [← harg] at hx
    exact hx.1
  have hsP : (s : Set E4) ⊆ seicento.toSet := by
    intro x hx
    exact subset_convexHull ℝ _ (hsV hx)
  have hsub : convexHull ℝ (s : Set E4) ⊆ seicento.toSet :=
    convexHull_min hsP (convex_convexHull ℝ _)
  have heq : ∀ x ∈ (s : Set E4), l x = c := by
    intro x hx
    rw [← harg] at hx
    exact hx.2
  have hge : ∀ x ∈ convexHull ℝ (s : Set E4), c ≤ l x := by
    intro x hx
    exact convexHull_min (fun y hy => by change c ≤ l y; rw [heq y hy])
      (convex_halfSpace_ge (LinearMap.isLinear l.toLinearMap) c) hx
  refine ⟨l, Set.ext ?_⟩
  intro x
  constructor
  · intro hx
    have hlx : l x = c := le_antisymm (hle x (hsub hx)) (hge x hx)
    exact ⟨hsub hx, fun y hy => by rw [hlx]; exact hle y hy⟩
  · rintro ⟨hxP, hxmax⟩
    obtain ⟨a, ha⟩ := hs
    have haS : a ∈ (s : Set E4) := by exact_mod_cast ha
    have haP : a ∈ seicento.toSet := hsP haS
    have hlx : l x = c := by
      apply le_antisymm (hle x hxP)
      simpa [heq a haS] using hxmax a haP
    have hxarg := faccia_argmax seicento.vertices l hxP hxmax
    have hset : {z ∈ (seicento.vertices : Set E4) | l z = l x} =
        (s : Set E4) := by simpa [hlx] using harg
    rwa [hset] at hxarg


-- @@ L418-423 verbatim
theorem F3_600_isFace : seicento.IsFace F3_600 := by
  refine ⟨?_, ⟨e1_600, subset_convexHull ℝ _
    (by simp [generatoriF3_600])⟩⟩
  exact isExposed_argmax_600 generatoriF3_600 l3_600
    (1 + 3 * aureo / 2) (by simp [generatoriF3_600])
    argmax_l3_600 l3_toSet_le


-- @@ L425-425 verbatim
def l0_600 : E4 →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin 4)


-- @@ L427-430 verbatim
def l1_600 : E4 →L[ℝ] ℝ :=
  (1 + aureo / 2) • EuclideanSpace.proj (0 : Fin 4) +
    (1 / 2 : ℝ) • EuclideanSpace.proj (1 : Fin 4) +
    ((aureo - 1) / 2) • EuclideanSpace.proj (2 : Fin 4)


-- @@ L432-434 verbatim
def l2_600 : E4 →L[ℝ] ℝ :=
  (1 + aureo) • EuclideanSpace.proj (0 : Fin 4) +
    EuclideanSpace.proj (1 : Fin 4)


-- @@ L436-452 verbatim
private theorem small_functional_values :
    (l0_600 e1_600 = 1 ∧ l0_600 c1_600 = aureo / 2 ∧
      l0_600 c2_600 = aureo / 2 ∧ l0_600 c3_600 = aureo / 2) ∧
    (l1_600 e1_600 = 1 + aureo / 2 ∧
      l1_600 c1_600 = 1 + aureo / 2 ∧
      l1_600 c2_600 = aureo ∧ l1_600 c3_600 = aureo) ∧
    (l2_600 e1_600 = 1 + aureo ∧ l2_600 c1_600 = 1 + aureo ∧
      l2_600 c2_600 = 1 + aureo ∧ l2_600 c3_600 = 3 * aureo / 2) := by
  simp only [l0_600, l1_600, l2_600, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, PiLp.proj_apply]
  simp only [e1_600_coord0, e1_600_coord1, e1_600_coord2,
    c1_600_coord0, c1_600_coord1, c1_600_coord2,
    c2_600_coord0, c2_600_coord1, c2_600_coord2,
    c3_600_coord0, c3_600_coord1, c3_600_coord2]
  refine ⟨⟨?_, ?_, ?_, ?_⟩,
    ⟨⟨?_, ?_, ?_, ?_⟩, ⟨?_, ?_, ?_, ?_⟩⟩⟩ <;>
    norm_num <;> nlinarith [aureo_sq]


-- @@ L454-476 verbatim
private theorem argmax_l2_generators :
    {x ∈ (generatoriF3_600 : Set E4) | l2_600 x = 1 + aureo} =
      (generatoriF2_600 : Set E4) := by
  ext x
  have hne : 3 * aureo / 2 ≠ 1 + aureo := by
    intro h
    linarith [aureo_bounds.2]
  simp only [generatoriF3_600, generatoriF2_600, Set.mem_setOf_eq,
    Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hl⟩
    rcases hx with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
    · rw [small_functional_values.2.2.2.2.2] at hl
      exact (hne hl).elim
  · intro hx
    rcases hx with rfl | rfl | rfl
    · exact ⟨Or.inl rfl, small_functional_values.2.2.1⟩
    · exact ⟨Or.inr (Or.inl rfl), small_functional_values.2.2.2.1⟩
    · exact ⟨Or.inr (Or.inr (Or.inl rfl)),
        small_functional_values.2.2.2.2.1⟩


-- @@ L478-497 verbatim
private theorem argmax_l1_generators :
    {x ∈ (generatoriF2_600 : Set E4) | l1_600 x = 1 + aureo / 2} =
      (generatoriF1_600 : Set E4) := by
  ext x
  have hne : aureo ≠ 1 + aureo / 2 := by
    intro h
    linarith [aureo_bounds.2]
  simp only [generatoriF2_600, generatoriF1_600, Set.mem_setOf_eq,
    Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hl⟩
    rcases hx with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · rw [small_functional_values.2.1.2.2.1] at hl
      exact (hne hl).elim
  · intro hx
    rcases hx with rfl | rfl
    · exact ⟨Or.inl rfl, small_functional_values.2.1.1⟩
    · exact ⟨Or.inr (Or.inl rfl), small_functional_values.2.1.2.1⟩


-- @@ L499-515 verbatim
private theorem argmax_l0_generators :
    {x ∈ (generatoriF1_600 : Set E4) | l0_600 x = 1} =
      (generatoriF0_600 : Set E4) := by
  ext x
  have hne : aureo / 2 ≠ 1 := by
    intro h
    linarith [aureo_bounds.2]
  simp only [generatoriF1_600, generatoriF0_600, Set.mem_setOf_eq,
    Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hl⟩
    rcases hx with rfl | rfl
    · rfl
    · rw [small_functional_values.1.2.1] at hl
      exact (hne hl).elim
  · rintro rfl
    exact ⟨Or.inl rfl, small_functional_values.1.1⟩


-- @@ L517-560 verbatim
private theorem isExposed_hull_argmax (t s : Finset E4)
    (l : E4 →L[ℝ] ℝ) (c : ℝ) (hs : s.Nonempty)
    (harg : {x ∈ (t : Set E4) | l x = c} = (s : Set E4))
    (hleV : ∀ x ∈ (t : Set E4), l x ≤ c) :
    IsExposed ℝ (convexHull ℝ (t : Set E4))
      (convexHull ℝ (s : Set E4)) := by
  intro _
  have hsT : (s : Set E4) ⊆ (t : Set E4) := by
    intro x hx
    rw [← harg] at hx
    exact hx.1
  have hsP : (s : Set E4) ⊆ convexHull ℝ (t : Set E4) :=
    fun x hx => subset_convexHull ℝ _ (hsT hx)
  have hsub : convexHull ℝ (s : Set E4) ⊆ convexHull ℝ (t : Set E4) :=
    convexHull_min hsP (convex_convexHull ℝ _)
  have hle : ∀ x ∈ convexHull ℝ (t : Set E4), l x ≤ c := by
    intro x hx
    exact convexHull_min hleV
      (convex_halfSpace_le (LinearMap.isLinear l.toLinearMap) c) hx
  have heq : ∀ x ∈ (s : Set E4), l x = c := by
    intro x hx
    rw [← harg] at hx
    exact hx.2
  have hge : ∀ x ∈ convexHull ℝ (s : Set E4), c ≤ l x := by
    intro x hx
    exact convexHull_min (fun y hy => by change c ≤ l y; rw [heq y hy])
      (convex_halfSpace_ge (LinearMap.isLinear l.toLinearMap) c) hx
  refine ⟨l, Set.ext ?_⟩
  intro x
  constructor
  · intro hx
    have hlx : l x = c := le_antisymm (hle x (hsub hx)) (hge x hx)
    exact ⟨hsub hx, fun y hy => by rw [hlx]; exact hle y hy⟩
  · rintro ⟨hxP, hxmax⟩
    obtain ⟨a, ha⟩ := hs
    have haS : a ∈ (s : Set E4) := by exact_mod_cast ha
    have haP : a ∈ convexHull ℝ (t : Set E4) := hsP haS
    have hlx : l x = c := by
      apply le_antisymm (hle x hxP)
      simpa [heq a haS] using hxmax a haP
    have hxarg := faccia_argmax t l hxP hxmax
    have hset : {z ∈ (t : Set E4) | l z = l x} = (s : Set E4) := by
      simpa [hlx] using harg
    rwa [hset] at hxarg


-- @@ L562-576 verbatim
theorem F2_600_isFace : seicento.IsFace F2_600 := by
  apply isFace_of_isExposed_isFace seicento F3_600_isFace
  · exact isExposed_hull_argmax generatoriF3_600 generatoriF2_600
      l2_600 (1 + aureo) (by simp [generatoriF2_600])
      argmax_l2_generators (by
        intro x hx
        have hc : x = e1_600 ∨ x = c1_600 ∨ x = c2_600 ∨ x = c3_600 := by
          simpa [generatoriF3_600] using hx
        rcases hc with rfl | rfl | rfl | rfl
        · rw [small_functional_values.2.2.1]
        · rw [small_functional_values.2.2.2.1]
        · rw [small_functional_values.2.2.2.2.1]
        · rw [small_functional_values.2.2.2.2.2]
          linarith [aureo_bounds.2])
  · exact ⟨e1_600, subset_convexHull ℝ _ (by simp [generatoriF2_600])⟩


-- @@ L578-591 verbatim
theorem F1_600_isFace : seicento.IsFace F1_600 := by
  apply isFace_of_isExposed_isFace seicento F2_600_isFace
  · exact isExposed_hull_argmax generatoriF2_600 generatoriF1_600
      l1_600 (1 + aureo / 2) (by simp [generatoriF1_600])
      argmax_l1_generators (by
        intro x hx
        have hc : x = e1_600 ∨ x = c1_600 ∨ x = c2_600 := by
          simpa [generatoriF2_600] using hx
        rcases hc with rfl | rfl | rfl
        · rw [small_functional_values.2.1.1]
        · rw [small_functional_values.2.1.2.1]
        · rw [small_functional_values.2.1.2.2.1]
          linarith [aureo_bounds.2])
  · exact ⟨e1_600, subset_convexHull ℝ _ (by simp [generatoriF1_600])⟩


-- @@ L593-604 verbatim
theorem F0_600_isFace : seicento.IsFace F0_600 := by
  apply isFace_of_isExposed_isFace seicento F1_600_isFace
  · exact isExposed_hull_argmax generatoriF1_600 generatoriF0_600
      l0_600 1 (by simp [generatoriF0_600]) argmax_l0_generators (by
        intro x hx
        have hc : x = e1_600 ∨ x = c1_600 := by
          simpa [generatoriF1_600] using hx
        rcases hc with rfl | rfl
        · rw [small_functional_values.1.1]
        · rw [small_functional_values.1.2.1]
          linarith [aureo_bounds.2])
  · exact ⟨e1_600, subset_convexHull ℝ _ (by simp [generatoriF0_600])⟩


-- @@ L606-621 verbatim
/-- The six off-diagonal Gram entries of the fundamental tetrahedron. -/
theorem flag_inner_products_600 :
    ⟪e1_600, c1_600⟫ = aureo / 2 ∧
    ⟪e1_600, c2_600⟫ = aureo / 2 ∧
    ⟪e1_600, c3_600⟫ = aureo / 2 ∧
    ⟪c1_600, c2_600⟫ = aureo / 2 ∧
    ⟪c1_600, c3_600⟫ = aureo / 2 ∧
    ⟪c2_600, c3_600⟫ = aureo / 2 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp_rw [Fin.sum_univ_four]
  simp only [e1_600_coord0, e1_600_coord1, e1_600_coord2, e1_600_coord3,
    c1_600_coord0, c1_600_coord1, c1_600_coord2, c1_600_coord3,
    c2_600_coord0, c2_600_coord1, c2_600_coord2, c2_600_coord3,
    c3_600_coord0, c3_600_coord1, c3_600_coord2, c3_600_coord3]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num <;> nlinarith [aureo_sq]


-- @@ L623-623 verbatim
private def p2_600 : Fin 3 → E4 := ![e1_600, c1_600, c2_600]

-- @@ L624-624 verbatim
private def p3_600 : Fin 4 → E4 := ![e1_600, c1_600, c2_600, c3_600]


-- @@ L626-626 verbatim
@[simp] private theorem p2_600_zero : p2_600 0 = e1_600 := rfl

-- @@ L627-627 verbatim
@[simp] private theorem p2_600_one : p2_600 1 = c1_600 := rfl

-- @@ L628-628 verbatim
@[simp] private theorem p2_600_two : p2_600 2 = c2_600 := rfl

-- @@ L629-629 verbatim
@[simp] private theorem p3_600_zero : p3_600 0 = e1_600 := rfl

-- @@ L630-630 verbatim
@[simp] private theorem p3_600_one : p3_600 1 = c1_600 := rfl

-- @@ L631-631 verbatim
@[simp] private theorem p3_600_two : p3_600 2 = c2_600 := rfl

-- @@ L632-632 verbatim
@[simp] private theorem p3_600_three : p3_600 3 = c3_600 := rfl


-- @@ L634-658 verbatim
private theorem p3_600_affineIndependent : AffineIndependent ℝ p3_600 := by
  rw [affineIndependent_iff_eq_of_fintype_affineCombination_eq]
  intro a b ha hb hab
  funext i
  have hc (j : Fin 4) := congrArg (fun x : E4 => x j) hab
  rw [Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using ha),
    Finset.affineCombination_eq_linear_combination _ _ _ (by simpa using hb)] at hc
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  have h3 := hc 3
  rw [Fin.sum_univ_four] at ha hb
  norm_num [p3_600_zero, p3_600_one, p3_600_two, p3_600_three,
    Fin.sum_univ_four] at h0 h1 h2 h3
  have e3 : a 3 = b 3 := by linarith
  have e1 : a 1 = b 1 := by
    nlinarith [aureo_sub_one_pos]
  have e2 : a 2 = b 2 := by
    nlinarith [aureo_sub_one_pos]
  have e0 : a 0 = b 0 := by linarith
  fin_cases i
  · exact e0
  · exact e1
  · exact e2
  · exact e3


-- @@ L660-662 verbatim
private def fin3ToFin4 : Fin 3 ↪ Fin 4 where
  toFun i := ⟨i, by omega⟩
  inj' := by intro i j h; exact Fin.ext (Fin.mk.inj h)


-- @@ L664-666 verbatim
private theorem p2_600_eq_comp : p2_600 = p3_600 ∘ fin3ToFin4 := by
  funext i
  fin_cases i <;> rfl


-- @@ L668-670 verbatim
private theorem p2_600_affineIndependent : AffineIndependent ℝ p2_600 := by
  rw [p2_600_eq_comp]
  exact p3_600_affineIndependent.comp_embedding fin3ToFin4


-- @@ L672-684 verbatim
private theorem range_p2_600 :
    Set.range p2_600 = (generatoriF2_600 : Set E4) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [p2_600, generatoriF2_600]
  · intro hx
    have hc : x = e1_600 ∨ x = c1_600 ∨ x = c2_600 := by
      simpa [generatoriF2_600] using hx
    rcases hc with rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩


-- @@ L686-699 verbatim
private theorem range_p3_600 :
    Set.range p3_600 = (generatoriF3_600 : Set E4) := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [p3_600, generatoriF3_600]
  · intro hx
    have hc : x = e1_600 ∨ x = c1_600 ∨ x = c2_600 ∨ x = c3_600 := by
      simpa [generatoriF3_600] using hx
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩


-- @@ L701-703 verbatim
theorem faceDim_F0_600 : faceDim F0_600 = 0 := by
  rw [F0_600, generatoriF0_600]
  simpa using faceDim_singleton e1_600


-- @@ L705-709 verbatim
private theorem e1_ne_c1_600 : e1_600 ≠ c1_600 := by
  intro h
  have hc := congrArg (fun x : E4 => x (1 : Fin 4)) h
  rw [flag_vertex_coordinates.1 1, flag_vertex_coordinates.2.1 1] at hc
  norm_num at hc


-- @@ L711-719 verbatim
theorem faceDim_F1_600 : faceDim F1_600 = 1 := by
  have hgen : (generatoriF1_600 : Set E4) = {e1_600, c1_600} := by
    ext x
    simp [generatoriF1_600]
  rw [F1_600, hgen, convexHull_pair]
  unfold faceDim
  rw [vectorSpan_segment]
  apply finrank_span_singleton
  exact vsub_ne_zero.mpr e1_ne_c1_600.symm


-- @@ L721-725 verbatim
theorem faceDim_F2_600 : faceDim F2_600 = 2 := by
  unfold faceDim
  rw [F2_600, ← direction_affineSpan, affineSpan_convexHull,
    direction_affineSpan, ← range_p2_600]
  exact p2_600_affineIndependent.finrank_vectorSpan (by simp)


-- @@ L727-731 verbatim
theorem faceDim_F3_600 : faceDim F3_600 = 3 := by
  unfold faceDim
  rw [F3_600, ← direction_affineSpan, affineSpan_convexHull,
    direction_affineSpan, ← range_p3_600]
  exact p3_600_affineIndependent.finrank_vectorSpan (by simp)


-- @@ L733-744 verbatim
theorem F0_ssubset_F1_600 : F0_600 ⊂ F1_600 := by
  apply Set.ssubset_iff_subset_ne.mpr
  constructor
  · apply convexHull_mono
    intro x hx
    have hx0 : x = e1_600 := by simpa [generatoriF0_600] using hx
    subst x
    simp [generatoriF1_600]
  · intro h
    have hd := faceDim_F0_600
    rw [h, faceDim_F1_600] at hd
    omega


-- @@ L746-757 verbatim
theorem F1_ssubset_F2_600 : F1_600 ⊂ F2_600 := by
  apply Set.ssubset_iff_subset_ne.mpr
  constructor
  · apply convexHull_mono
    intro x hx
    have hc : x = e1_600 ∨ x = c1_600 := by
      simpa [generatoriF1_600] using hx
    rcases hc with rfl | rfl <;> simp [generatoriF2_600]
  · intro h
    have hd := faceDim_F1_600
    rw [h, faceDim_F2_600] at hd
    omega


-- @@ L759-770 verbatim
theorem F2_ssubset_F3_600 : F2_600 ⊂ F3_600 := by
  apply Set.ssubset_iff_subset_ne.mpr
  constructor
  · apply convexHull_mono
    intro x hx
    have hc : x = e1_600 ∨ x = c1_600 ∨ x = c2_600 := by
      simpa [generatoriF2_600] using hx
    rcases hc with rfl | rfl | rfl <;> simp [generatoriF3_600]
  · intro h
    have hd := faceDim_F2_600
    rw [h, faceDim_F3_600] at hd
    omega


-- @@ L772-796 verbatim
/-- Fundamental flag of the 600-cell. -/
def seicentoFlag : seicento.Flag where
  face i := ![F0_600, F1_600, F2_600, F3_600] i
  isFace i := by
    fin_cases i
    · exact F0_600_isFace
    · exact F1_600_isFace
    · exact F2_600_isFace
    · exact F3_600_isFace
  dim_eq i := by
    fin_cases i
    · exact faceDim_F0_600
    · exact faceDim_F1_600
    · exact faceDim_F2_600
    · exact faceDim_F3_600
  strict_mono i j hij := by
    fin_cases i <;> fin_cases j
    all_goals norm_num at hij
    · exact F0_ssubset_F1_600
    · exact F0_ssubset_F1_600.trans F1_ssubset_F2_600
    · exact F0_ssubset_F1_600.trans
        (F1_ssubset_F2_600.trans F2_ssubset_F3_600)
    · exact F1_ssubset_F2_600
    · exact F1_ssubset_F2_600.trans F2_ssubset_F3_600
    · exact F2_ssubset_F3_600


-- @@ L798-799 verbatim
private def signedBool (u : ({-1, 1} : Set ℝ)) (b : Bool) : Bool :=
  if (u : ℝ) = 1 then b else !b


-- @@ L801-805 verbatim
@[simp] private theorem segnoLinear_apply_coord_600 (d : ℕ)
    (σ : Equiv.Perm (Fin d)) (ε : Fin d → ({-1, 1} : Set ℝ))
    (x : E d) (i : Fin d) :
    segnoLinear d σ ε x (σ i) = (ε i : ℝ) * x i := by
  simp [segnoLinear]


-- @@ L807-813 verbatim
private theorem signedBool_spec (u : ({-1, 1} : Set ℝ)) (b : Bool) :
    (if signedBool u b then (1 : ℝ) else -1) =
      (u : ℝ) * (if b then 1 else -1) := by
  have hu := u.property
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
  rcases hu with hu | hu <;> cases b <;>
    simp [signedBool, hu] <;> norm_num at *


-- @@ L815-837 verbatim
private theorem signedEven_vertA (τ : alternatingGroup (Fin 4))
    (ε : Fin 4 → ({-1, 1} : Set ℝ)) (i : Fin 4) (b : Bool) :
    segnoPerm 4 (τ : Equiv.Perm (Fin 4)) ε (vertA i b) =
      vertA ((τ : Equiv.Perm (Fin 4)) i) (signedBool (ε i) b) := by
  ext j
  let k := (τ : Equiv.Perm (Fin 4)).symm j
  have hj : (τ : Equiv.Perm (Fin 4)) k = j :=
    (τ : Equiv.Perm (Fin 4)).apply_symm_apply j
  rw [← hj, segnoPerm_apply, segnoLinear_apply_coord_600]
  simp only [vertA_apply]
  change (ε k : ℝ) *
      (if k = i then (if b then 1 else -1) else 0) =
    if (τ : Equiv.Perm (Fin 4)) k = (τ : Equiv.Perm (Fin 4)) i then
      (if signedBool (ε i) b then 1 else -1) else 0
  by_cases hki : k = i
  · have hτki : (τ : Equiv.Perm (Fin 4)) k =
        (τ : Equiv.Perm (Fin 4)) i := congrArg _ hki
    rw [if_pos hki, if_pos hτki, hki]
    exact signedBool_spec (ε i) b |>.symm
  · have hτki : (τ : Equiv.Perm (Fin 4)) k ≠
        (τ : Equiv.Perm (Fin 4)) i :=
      ((τ : Equiv.Perm (Fin 4)).injective.ne hki)
    simp [hki, hτki]


-- @@ L839-858 verbatim
private theorem signedEven_vertB (τ : alternatingGroup (Fin 4))
    (ε : Fin 4 → ({-1, 1} : Set ℝ)) (s : Fin 4 → Bool) :
    segnoPerm 4 (τ : Equiv.Perm (Fin 4)) ε (vertB s) =
      vertB (fun j => signedBool (ε ((τ : Equiv.Perm (Fin 4)).symm j))
        (s ((τ : Equiv.Perm (Fin 4)).symm j))) := by
  ext j
  let k := (τ : Equiv.Perm (Fin 4)).symm j
  have hj : (τ : Equiv.Perm (Fin 4)) k = j :=
    (τ : Equiv.Perm (Fin 4)).apply_symm_apply j
  rw [← hj, segnoPerm_apply, segnoLinear_apply_coord_600]
  simp only [vertB_apply, Equiv.symm_apply_apply]
  calc
    (ε k : ℝ) * (if s k then 1 / 2 else -(1 / 2)) =
        (1 / 2 : ℝ) * ((ε k : ℝ) * (if s k then 1 else -1)) := by
          cases hsk : s k <;> simp [hsk] <;> ring
    _ = (1 / 2 : ℝ) *
        (if signedBool (ε k) (s k) then 1 else -1) := by
          rw [← signedBool_spec]
    _ = if signedBool (ε k) (s k) then 1 / 2 else -(1 / 2) := by
          cases signedBool (ε k) (s k) <;> norm_num


-- @@ L860-862 verbatim
private def signedC (ε : Fin 4 → ({-1, 1} : Set ℝ))
    (σ : alternatingGroup (Fin 4)) (s : Fin 3 → Bool) : Fin 3 → Bool :=
  fun m => signedBool (ε ((σ : Equiv.Perm (Fin 4)) ⟨m, by omega⟩)) (s m)


-- @@ L864-892 verbatim
private theorem signedEven_vertC (τ σ : alternatingGroup (Fin 4))
    (ε : Fin 4 → ({-1, 1} : Set ℝ)) (s : Fin 3 → Bool) :
    segnoPerm 4 (τ : Equiv.Perm (Fin 4)) ε (vertC σ s) =
      vertC (τ * σ) (signedC ε σ s) := by
  ext j
  let k := ((τ * σ : alternatingGroup (Fin 4)) :
    Equiv.Perm (Fin 4)).symm j
  have hj : (((τ * σ : alternatingGroup (Fin 4)) :
      Equiv.Perm (Fin 4)) k) = j :=
    ((τ * σ : alternatingGroup (Fin 4)) :
      Equiv.Perm (Fin 4)).apply_symm_apply j
  rw [← hj]
  change segnoLinear 4 (τ : Equiv.Perm (Fin 4)) ε (vertC σ s)
      ((τ : Equiv.Perm (Fin 4)) ((σ : Equiv.Perm (Fin 4)) k)) = _
  rw [segnoLinear_apply_coord_600, vertC_at, vertC_at]
  clear hj
  clear_value k
  clear j
  fin_cases k
  · simpa [signedC, segnoC] using
      congrArg (fun z : ℝ => z * baseC (0 : Fin 4))
        (signedBool_spec (ε ((σ : Equiv.Perm (Fin 4)) 0)) (s 0)).symm
  · simpa [signedC, segnoC] using
      congrArg (fun z : ℝ => z * baseC (1 : Fin 4))
        (signedBool_spec (ε ((σ : Equiv.Perm (Fin 4)) 1)) (s 1)).symm
  · simpa [signedC, segnoC] using
      congrArg (fun z : ℝ => z * baseC (2 : Fin 4))
        (signedBool_spec (ε ((σ : Equiv.Perm (Fin 4)) 2)) (s 2)).symm
  · simp [baseC]


-- @@ L894-910 verbatim
private theorem signedEven_mem_seicentoVertici
    (τ : alternatingGroup (Fin 4))
    (ε : Fin 4 → ({-1, 1} : Set ℝ)) {v : E4}
    (hv : v ∈ seicentoVertici) :
    segnoPerm 4 (τ : Equiv.Perm (Fin 4)) ε v ∈ seicentoVertici := by
  classical
  simp only [seicentoVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hv ⊢
  rcases hv with (⟨p, rfl⟩ | ⟨s, rfl⟩) | ⟨p, rfl⟩
  · exact Or.inl (Or.inl ⟨((τ : Equiv.Perm (Fin 4)) p.1,
      signedBool (ε p.1) p.2), (signedEven_vertA τ ε p.1 p.2).symm⟩)
  · exact Or.inl (Or.inr ⟨(fun j =>
      signedBool (ε ((τ : Equiv.Perm (Fin 4)).symm j))
        (s ((τ : Equiv.Perm (Fin 4)).symm j))),
      (signedEven_vertB τ ε s).symm⟩)
  · exact Or.inr ⟨(τ * p.1, signedC ε p.1 p.2),
      (signedEven_vertC τ p.1 ε p.2).symm⟩


-- @@ L912-927 verbatim
private theorem signedEven_image_seicentoVertici
    (τ : alternatingGroup (Fin 4))
    (ε : Fin 4 → ({-1, 1} : Set ℝ)) :
    (segnoPerm 4 (τ : Equiv.Perm (Fin 4)) ε : E4 → E4) ''
      (seicentoVertici : Set E4) = (seicentoVertici : Set E4) := by
  have hfin : Finset.image
      (segnoPerm 4 (τ : Equiv.Perm (Fin 4)) ε : E4 → E4)
      seicentoVertici = seicentoVertici := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      rw [Finset.mem_image] at hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact signedEven_mem_seicentoVertici τ ε hu
    · rw [Finset.card_image_of_injective _
        (segnoPerm 4 (τ : Equiv.Perm (Fin 4)) ε).injective]
  rw [← Finset.coe_image, hfin]


-- @@ L929-942 verbatim
theorem signedEven_isSymmetry_seicento (τ : alternatingGroup (Fin 4))
    (ε : Fin 4 → ({-1, 1} : Set ℝ)) :
    seicento.isSymmetry (segnoPerm 4 (τ : Equiv.Perm (Fin 4)) ε) := by
  rw [ConvexPolytope.isSymmetry, ConvexPolytope.toSet]
  calc
    (segnoPerm 4 (τ : Equiv.Perm (Fin 4)) ε : E4 → E4) ''
        convexHull ℝ ((seicento.vertices : Finset E4) : Set E4) =
      convexHull ℝ ((segnoPerm 4 (τ : Equiv.Perm (Fin 4)) ε : E4 → E4) ''
        ((seicento.vertices : Finset E4) : Set E4)) := by
          exact (segnoPerm 4 (τ : Equiv.Perm (Fin 4)) ε).toAffineEquiv.toAffineMap.image_convexHull _
    _ = convexHull ℝ ((seicento.vertices : Finset E4) : Set E4) := by
      rw [show ((seicento.vertices : Finset E4) : Set E4) =
          (seicentoVertici : Set E4) by rfl,
        signedEven_image_seicentoVertici]


-- @@ L944-945 verbatim
private def segnoTerza_600 : Fin 4 → ({-1, 1} : Set ℝ) :=
  fun i => if i = 2 then ⟨-1, by simp⟩ else ⟨1, by simp⟩


-- @@ L947-948 verbatim
private def segnoQuarta_600 : Fin 4 → ({-1, 1} : Set ℝ) :=
  fun i => if i = 3 then ⟨-1, by simp⟩ else ⟨1, by simp⟩


-- @@ L950-953 verbatim
/-- Rank-one wall: negate the third coordinate. -/
def r1_600 : Isom 4 :=
  segnoPerm 4 ((1 : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4))
    segnoTerza_600


-- @@ L955-958 verbatim
/-- Rank-three wall: negate the fourth coordinate. -/
def r3_600 : Isom 4 :=
  segnoPerm 4 ((1 : alternatingGroup (Fin 4)) : Equiv.Perm (Fin 4))
    segnoQuarta_600


-- @@ L960-963 verbatim
private theorem signedRefl_apply
    (ε : Fin 4 → ({-1, 1} : Set ℝ)) (x : E4) (i : Fin 4) :
    segnoPerm 4 (Equiv.refl (Fin 4)) ε x i = (ε i : ℝ) * x i := by
  simpa using segnoLinear_apply_coord_600 4 (Equiv.refl (Fin 4)) ε x i


-- @@ L965-966 verbatim
theorem r1_600_isSymmetry : seicento.isSymmetry r1_600 := by
  exact signedEven_isSymmetry_seicento 1 segnoTerza_600


-- @@ L968-969 verbatim
theorem r3_600_isSymmetry : seicento.isSymmetry r3_600 := by
  exact signedEven_isSymmetry_seicento 1 segnoQuarta_600


-- @@ L971-977 verbatim
private theorem r1_600_vertices :
    r1_600 e1_600 = e1_600 ∧ r1_600 c1_600 = c2_600 ∧
      r1_600 c2_600 = c1_600 ∧ r1_600 c3_600 = c3_600 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> ext k <;> fin_cases k <;>
    rw [show r1_600 _ _ = (segnoTerza_600 _ : ℝ) * _ by
      exact signedRefl_apply segnoTerza_600 _ _] <;>
    simp [segnoTerza_600] <;> ring


-- @@ L979-985 verbatim
private theorem r3_600_vertices :
    r3_600 e1_600 = e1_600 ∧ r3_600 c1_600 = c1_600 ∧
      r3_600 c2_600 = c2_600 := by
  refine ⟨?_, ?_, ?_⟩ <;> ext k <;> fin_cases k <;>
    rw [show r3_600 _ _ = (segnoQuarta_600 _ : ℝ) * _ by
      exact signedRefl_apply segnoQuarta_600 _ _] <;>
    simp [segnoQuarta_600]


-- @@ L987-989 verbatim
private theorem image_convexHull_isom600 (g : Isom 4) (s : Set E4) :
    (g : E4 → E4) '' convexHull ℝ s = convexHull ℝ ((g : E4 → E4) '' s) :=
  g.toAffineEquiv.toAffineMap.image_convexHull s


-- @@ L991-995 verbatim
private theorem r1_image_F0_600 : (r1_600 : E4 → E4) '' F0_600 = F0_600 := by
  rw [F0_600, image_convexHull_isom600]
  congr 1
  ext x
  simp [generatoriF0_600, r1_600_vertices.1]


-- @@ L997-1002 verbatim
private theorem r1_image_F2_600 : (r1_600 : E4 → E4) '' F2_600 = F2_600 := by
  rw [F2_600, image_convexHull_isom600]
  congr 1
  ext x
  simp [generatoriF2_600, r1_600_vertices.1, r1_600_vertices.2.1,
    r1_600_vertices.2.2.1] <;> tauto


-- @@ L1004-1009 verbatim
private theorem r1_image_F3_600 : (r1_600 : E4 → E4) '' F3_600 = F3_600 := by
  rw [F3_600, image_convexHull_isom600]
  congr 1
  ext x
  simp [generatoriF3_600, r1_600_vertices.1, r1_600_vertices.2.1,
    r1_600_vertices.2.2.1, r1_600_vertices.2.2.2] <;> tauto


-- @@ L1011-1015 verbatim
private theorem r3_image_F0_600 : (r3_600 : E4 → E4) '' F0_600 = F0_600 := by
  rw [F0_600, image_convexHull_isom600]
  congr 1
  ext x
  simp [generatoriF0_600, r3_600_vertices.1]


-- @@ L1017-1021 verbatim
private theorem r3_image_F1_600 : (r3_600 : E4 → E4) '' F1_600 = F1_600 := by
  rw [F1_600, image_convexHull_isom600]
  congr 1
  ext x
  simp [generatoriF1_600, r3_600_vertices.1, r3_600_vertices.2.1] <;> tauto


-- @@ L1023-1028 verbatim
private theorem r3_image_F2_600 : (r3_600 : E4 → E4) '' F2_600 = F2_600 := by
  rw [F2_600, image_convexHull_isom600]
  congr 1
  ext x
  simp [generatoriF2_600, r3_600_vertices.1, r3_600_vertices.2.1,
    r3_600_vertices.2.2] <;> tauto


-- @@ L1030-1051 verbatim
private theorem l1_eq_on_F1_600 {x : E4} (hx : x ∈ F1_600) :
    l1_600 x = 1 + aureo / 2 := by
  rw [F1_600] at hx
  exact le_antisymm
    (convexHull_min (fun y hy => by
        change l1_600 y ≤ 1 + aureo / 2
        have hc : y = e1_600 ∨ y = c1_600 := by
          simpa [generatoriF1_600] using hy
        rcases hc with rfl | rfl
        · rw [small_functional_values.2.1.1]
        · rw [small_functional_values.2.1.2.1])
      (convex_halfSpace_le (LinearMap.isLinear l1_600.toLinearMap)
        (1 + aureo / 2)) hx)
    (convexHull_min (fun y hy => by
        change 1 + aureo / 2 ≤ l1_600 y
        have hc : y = e1_600 ∨ y = c1_600 := by
          simpa [generatoriF1_600] using hy
        rcases hc with rfl | rfl
        · rw [small_functional_values.2.1.1]
        · rw [small_functional_values.2.1.2.1])
      (convex_halfSpace_ge (LinearMap.isLinear l1_600.toLinearMap)
        (1 + aureo / 2)) hx)


-- @@ L1053-1061 verbatim
private theorem r1_moves_F1_600 : (r1_600 : E4 → E4) '' F1_600 ≠ F1_600 := by
  intro h
  have hc : c2_600 ∈ (r1_600 : E4 → E4) '' F1_600 :=
    ⟨c1_600, subset_convexHull ℝ _ (by simp [generatoriF1_600]),
      r1_600_vertices.2.1⟩
  rw [h] at hc
  have hv := l1_eq_on_F1_600 hc
  rw [small_functional_values.2.1.2.2.1] at hv
  linarith [aureo_bounds.2]


-- @@ L1063-1072 verbatim
private theorem l3_r3_c3_600 :
    l3_600 (r3_600 c3_600) = 1 / 2 + 3 * aureo / 2 := by
  rw [l3_600_apply]
  have hcoord (i : Fin 4) :
      r3_600 c3_600 i = (segnoQuarta_600 i : ℝ) * c3_600 i :=
    signedRefl_apply segnoQuarta_600 c3_600 i
  rw [hcoord 0, hcoord 1, hcoord 3]
  rw [c3_600_coord0, c3_600_coord1, c3_600_coord3]
  norm_num [segnoQuarta_600, Fin.ext_iff]
  nlinarith [aureo_sq]


-- @@ L1074-1099 verbatim
private theorem l3_eq_on_F3_600 {x : E4} (hx : x ∈ F3_600) :
    l3_600 x = 1 + 3 * aureo / 2 := by
  rw [F3_600] at hx
  exact le_antisymm
    (convexHull_min (fun y hy => by
        change l3_600 y ≤ 1 + 3 * aureo / 2
        have hc : y = e1_600 ∨ y = c1_600 ∨ y = c2_600 ∨ y = c3_600 := by
          simpa [generatoriF3_600] using hy
        rcases hc with rfl | rfl | rfl | rfl
        · rw [l3_flag_values.1]
        · rw [l3_flag_values.2.1]
        · rw [l3_flag_values.2.2.1]
        · rw [l3_flag_values.2.2.2])
      (convex_halfSpace_le (LinearMap.isLinear l3_600.toLinearMap)
        (1 + 3 * aureo / 2)) hx)
    (convexHull_min (fun y hy => by
        change 1 + 3 * aureo / 2 ≤ l3_600 y
        have hc : y = e1_600 ∨ y = c1_600 ∨ y = c2_600 ∨ y = c3_600 := by
          simpa [generatoriF3_600] using hy
        rcases hc with rfl | rfl | rfl | rfl
        · rw [l3_flag_values.1]
        · rw [l3_flag_values.2.1]
        · rw [l3_flag_values.2.2.1]
        · rw [l3_flag_values.2.2.2])
      (convex_halfSpace_ge (LinearMap.isLinear l3_600.toLinearMap)
        (1 + 3 * aureo / 2)) hx)


-- @@ L1101-1108 verbatim
private theorem r3_moves_F3_600 : (r3_600 : E4 → E4) '' F3_600 ≠ F3_600 := by
  intro h
  have hc : r3_600 c3_600 ∈ (r3_600 : E4 → E4) '' F3_600 :=
    ⟨c3_600, subset_convexHull ℝ _ (by simp [generatoriF3_600]), rfl⟩
  rw [h] at hc
  have hv := l3_eq_on_F3_600 hc
  rw [l3_r3_c3_600] at hv
  norm_num at hv


-- @@ L1110-1120 verbatim
theorem r1_600_flagAdjacent :
    FlagAdjacentAt seicento seicentoFlag
      (mapFlag seicento r1_600_isSymmetry seicentoFlag) 1 := by
  constructor
  · intro j hj
    fin_cases j
    · exact r1_image_F0_600
    · exact (hj rfl).elim
    · exact r1_image_F2_600
    · exact r1_image_F3_600
  · exact r1_moves_F1_600


-- @@ L1122-1132 verbatim
theorem r3_600_flagAdjacent :
    FlagAdjacentAt seicento seicentoFlag
      (mapFlag seicento r3_600_isSymmetry seicentoFlag) 3 := by
  constructor
  · intro j hj
    fin_cases j
    · exact r3_image_F0_600
    · exact r3_image_F1_600
    · exact r3_image_F2_600
    · exact (hj rfl).elim
  · exact r3_moves_F3_600


-- @@ L1134-1138 verbatim
/-- Unit H4 root parallel to `e1_600 - c1_600`. -/
def alpha0_600 : E4 :=
  EuclideanSpace.single 0 ((aureo - 1) / 2) +
    EuclideanSpace.single 1 (-aureo / 2) +
    EuclideanSpace.single 2 (-(1 / 2 : ℝ))


-- @@ L1140-1145 verbatim
private theorem alpha0_parallel :
    e1_600 - c1_600 = (aureo - 1) • alpha0_600 := by
  ext j
  fin_cases j <;>
    simp [alpha0_600, Fin.ext_iff] <;>
    nlinarith [aureo_sq]


-- @@ L1147-1153 verbatim
private theorem norm_sq_alpha0_600 : ‖alpha0_600‖ ^ 2 = 1 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
  norm_num [alpha0_600, Fin.ext_iff]
  have hφ : 0 ≤ aureo := by linarith [aureo_bounds.1]
  have hφm : 0 ≤ aureo - 1 := by linarith [aureo_bounds.1]
  rw [abs_of_nonneg hφm, abs_of_nonneg hφ]
  nlinarith [aureo_sq]


-- @@ L1155-1156 verbatim
private theorem norm_alpha0_600 : ‖alpha0_600‖ = 1 := by
  nlinarith [norm_sq_alpha0_600, norm_nonneg alpha0_600]


-- @@ L1158-1160 verbatim
/-- Rank-zero wall: orthogonal reflection perpendicular to `e₁-c₁`. -/
def r0_600 : Isom 4 :=
  ((ℝ ∙ alpha0_600)ᗮ).reflection.toAffineIsometryEquiv


-- @@ L1162-1168 verbatim
private theorem r0_600_formula (x : E4) :
    r0_600 x = x - (2 * ⟪alpha0_600, x⟫ : ℝ) • alpha0_600 := by
  change ((ℝ ∙ alpha0_600)ᗮ).reflection x = _
  rw [Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply, norm_alpha0_600]
  norm_num
  module


-- @@ L1170-1179 verbatim
private theorem alpha0_inner_flag :
    ⟪alpha0_600, e1_600⟫ = (aureo - 1) / 2 ∧
    ⟪alpha0_600, c1_600⟫ = -(aureo - 1) / 2 ∧
    ⟪alpha0_600, c2_600⟫ = 0 ∧
    ⟪alpha0_600, c3_600⟫ = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fin.sum_univ_four] <;>
    simp [alpha0_600] <;>
    nlinarith [aureo_sq]


-- @@ L1181-1194 verbatim
private theorem r0_600_vertices :
    r0_600 e1_600 = c1_600 ∧ r0_600 c1_600 = e1_600 ∧
      r0_600 c2_600 = c2_600 ∧ r0_600 c3_600 = c3_600 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [r0_600_formula, alpha0_inner_flag.1]
    ext j
    fin_cases j <;> simp [alpha0_600] <;> nlinarith [aureo_sq]
  · rw [r0_600_formula, alpha0_inner_flag.2.1]
    ext j
    fin_cases j <;> simp [alpha0_600] <;> nlinarith [aureo_sq]
  · rw [r0_600_formula, alpha0_inner_flag.2.2.1]
    simp
  · rw [r0_600_formula, alpha0_inner_flag.2.2.2]
    simp


-- @@ L1196-1201 verbatim
private def twoSwapAlt (a b c d : Fin 4) (hab : a ≠ b) (hcd : c ≠ d) :
    alternatingGroup (Fin 4) :=
  ⟨Equiv.swap a b * Equiv.swap c d, by
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul,
      Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hcd]
    norm_num⟩


-- @@ L1203-1203 verbatim
private def tau0_600 : alternatingGroup (Fin 4) := 1

-- @@ L1204-1205 verbatim
private def tau1_600 : alternatingGroup (Fin 4) :=
  twoSwapAlt 1 2 2 3 (by omega) (by omega)

-- @@ L1206-1207 verbatim
private def tau2_600 : alternatingGroup (Fin 4) :=
  twoSwapAlt 1 3 2 3 (by omega) (by omega)

-- @@ L1208-1209 verbatim
private def tau3_600 : alternatingGroup (Fin 4) :=
  twoSwapAlt 0 1 2 3 (by omega) (by omega)

-- @@ L1210-1211 verbatim
private def tau4_600 : alternatingGroup (Fin 4) :=
  twoSwapAlt 0 1 1 2 (by omega) (by omega)

-- @@ L1212-1213 verbatim
private def tau5_600 : alternatingGroup (Fin 4) :=
  twoSwapAlt 0 1 1 3 (by omega) (by omega)

-- @@ L1214-1215 verbatim
private def tau6_600 : alternatingGroup (Fin 4) :=
  twoSwapAlt 0 2 2 3 (by omega) (by omega)

-- @@ L1216-1217 verbatim
private def tau7_600 : alternatingGroup (Fin 4) :=
  twoSwapAlt 0 2 1 2 (by omega) (by omega)

-- @@ L1218-1219 verbatim
private def tau8_600 : alternatingGroup (Fin 4) :=
  twoSwapAlt 0 2 1 3 (by omega) (by omega)

-- @@ L1220-1221 verbatim
private def tau9_600 : alternatingGroup (Fin 4) :=
  twoSwapAlt 0 3 2 3 (by omega) (by omega)

-- @@ L1222-1223 verbatim
private def tau10_600 : alternatingGroup (Fin 4) :=
  twoSwapAlt 0 3 1 2 (by omega) (by omega)

-- @@ L1224-1225 verbatim
private def tau11_600 : alternatingGroup (Fin 4) :=
  twoSwapAlt 0 3 1 3 (by omega) (by omega)


-- @@ L1227-1227 verbatim
private def bits3_600 (a b c : Bool) : Fin 3 → Bool := ![a, b, c]

-- @@ L1228-1228 verbatim
private def bits4_600 (a b c d : Bool) : Fin 4 → Bool := ![a, b, c, d]


-- @@ L1230-1232 verbatim
@[simp] private theorem bits3_600_apply0 (a b c : Bool) :
    bits3_600 a b c (0 : Fin 3) = a := by
  simp [bits3_600]


-- @@ L1234-1236 verbatim
@[simp] private theorem bits3_600_apply1 (a b c : Bool) :
    bits3_600 a b c (1 : Fin 3) = b := by
  simp [bits3_600]


-- @@ L1238-1240 verbatim
@[simp] private theorem bits3_600_apply2 (a b c : Bool) :
    bits3_600 a b c (2 : Fin 3) = c := by
  simp [bits3_600]


-- @@ L1242-1244 verbatim
@[simp] private theorem bits4_600_apply0 (a b c d : Bool) :
    bits4_600 a b c d (0 : Fin 4) = a := by
  simp [bits4_600]


-- @@ L1246-1248 verbatim
@[simp] private theorem bits4_600_apply1 (a b c d : Bool) :
    bits4_600 a b c d (1 : Fin 4) = b := by
  simp [bits4_600]


-- @@ L1250-1252 verbatim
@[simp] private theorem bits4_600_apply2 (a b c d : Bool) :
    bits4_600 a b c d (2 : Fin 4) = c := by
  simp [bits4_600]


-- @@ L1254-1256 verbatim
@[simp] private theorem bits4_600_apply3 (a b c d : Bool) :
    bits4_600 a b c d (3 : Fin 4) = d := by
  simp [bits4_600]


-- @@ L1258-1261 verbatim
@[simp] private theorem vertC_tau0_coord0 (s : Fin 3 → Bool) :
    vertC tau0_600 s (0 : Fin 4) = segnoC s (0 : Fin 4) * baseC (0 : Fin 4) := by
  simpa [tau0_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau0_600 s (0 : Fin 4)


-- @@ L1263-1266 verbatim
@[simp] private theorem vertC_tau0_coord1 (s : Fin 3 → Bool) :
    vertC tau0_600 s (1 : Fin 4) = segnoC s (1 : Fin 4) * baseC (1 : Fin 4) := by
  simpa [tau0_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau0_600 s (1 : Fin 4)


-- @@ L1268-1271 verbatim
@[simp] private theorem vertC_tau0_coord2 (s : Fin 3 → Bool) :
    vertC tau0_600 s (2 : Fin 4) = segnoC s (2 : Fin 4) * baseC (2 : Fin 4) := by
  simpa [tau0_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau0_600 s (2 : Fin 4)


-- @@ L1273-1276 verbatim
@[simp] private theorem vertC_tau0_coord3 (s : Fin 3 → Bool) :
    vertC tau0_600 s (3 : Fin 4) = segnoC s (3 : Fin 4) * baseC (3 : Fin 4) := by
  simpa [tau0_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau0_600 s (3 : Fin 4)


-- @@ L1278-1281 verbatim
@[simp] private theorem vertC_tau1_coord0 (s : Fin 3 → Bool) :
    vertC tau1_600 s (0 : Fin 4) = segnoC s (0 : Fin 4) * baseC (0 : Fin 4) := by
  simpa [tau1_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau1_600 s (0 : Fin 4)


-- @@ L1283-1286 verbatim
@[simp] private theorem vertC_tau1_coord1 (s : Fin 3 → Bool) :
    vertC tau1_600 s (1 : Fin 4) = segnoC s (3 : Fin 4) * baseC (3 : Fin 4) := by
  simpa [tau1_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau1_600 s (3 : Fin 4)


-- @@ L1288-1291 verbatim
@[simp] private theorem vertC_tau1_coord2 (s : Fin 3 → Bool) :
    vertC tau1_600 s (2 : Fin 4) = segnoC s (1 : Fin 4) * baseC (1 : Fin 4) := by
  simpa [tau1_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau1_600 s (1 : Fin 4)


-- @@ L1293-1296 verbatim
@[simp] private theorem vertC_tau1_coord3 (s : Fin 3 → Bool) :
    vertC tau1_600 s (3 : Fin 4) = segnoC s (2 : Fin 4) * baseC (2 : Fin 4) := by
  simpa [tau1_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau1_600 s (2 : Fin 4)


-- @@ L1298-1301 verbatim
@[simp] private theorem vertC_tau2_coord0 (s : Fin 3 → Bool) :
    vertC tau2_600 s (0 : Fin 4) = segnoC s (0 : Fin 4) * baseC (0 : Fin 4) := by
  simpa [tau2_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau2_600 s (0 : Fin 4)


-- @@ L1303-1306 verbatim
@[simp] private theorem vertC_tau2_coord1 (s : Fin 3 → Bool) :
    vertC tau2_600 s (1 : Fin 4) = segnoC s (2 : Fin 4) * baseC (2 : Fin 4) := by
  simpa [tau2_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau2_600 s (2 : Fin 4)


-- @@ L1308-1311 verbatim
@[simp] private theorem vertC_tau2_coord2 (s : Fin 3 → Bool) :
    vertC tau2_600 s (2 : Fin 4) = segnoC s (3 : Fin 4) * baseC (3 : Fin 4) := by
  simpa [tau2_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau2_600 s (3 : Fin 4)


-- @@ L1313-1316 verbatim
@[simp] private theorem vertC_tau2_coord3 (s : Fin 3 → Bool) :
    vertC tau2_600 s (3 : Fin 4) = segnoC s (1 : Fin 4) * baseC (1 : Fin 4) := by
  simpa [tau2_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau2_600 s (1 : Fin 4)


-- @@ L1318-1321 verbatim
@[simp] private theorem vertC_tau3_coord0 (s : Fin 3 → Bool) :
    vertC tau3_600 s (0 : Fin 4) = segnoC s (1 : Fin 4) * baseC (1 : Fin 4) := by
  simpa [tau3_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau3_600 s (1 : Fin 4)


-- @@ L1323-1326 verbatim
@[simp] private theorem vertC_tau3_coord1 (s : Fin 3 → Bool) :
    vertC tau3_600 s (1 : Fin 4) = segnoC s (0 : Fin 4) * baseC (0 : Fin 4) := by
  simpa [tau3_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau3_600 s (0 : Fin 4)


-- @@ L1328-1331 verbatim
@[simp] private theorem vertC_tau3_coord2 (s : Fin 3 → Bool) :
    vertC tau3_600 s (2 : Fin 4) = segnoC s (3 : Fin 4) * baseC (3 : Fin 4) := by
  simpa [tau3_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau3_600 s (3 : Fin 4)


-- @@ L1333-1336 verbatim
@[simp] private theorem vertC_tau3_coord3 (s : Fin 3 → Bool) :
    vertC tau3_600 s (3 : Fin 4) = segnoC s (2 : Fin 4) * baseC (2 : Fin 4) := by
  simpa [tau3_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau3_600 s (2 : Fin 4)


-- @@ L1338-1341 verbatim
@[simp] private theorem vertC_tau4_coord0 (s : Fin 3 → Bool) :
    vertC tau4_600 s (0 : Fin 4) = segnoC s (2 : Fin 4) * baseC (2 : Fin 4) := by
  simpa [tau4_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau4_600 s (2 : Fin 4)


-- @@ L1343-1346 verbatim
@[simp] private theorem vertC_tau4_coord1 (s : Fin 3 → Bool) :
    vertC tau4_600 s (1 : Fin 4) = segnoC s (0 : Fin 4) * baseC (0 : Fin 4) := by
  simpa [tau4_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau4_600 s (0 : Fin 4)


-- @@ L1348-1351 verbatim
@[simp] private theorem vertC_tau4_coord2 (s : Fin 3 → Bool) :
    vertC tau4_600 s (2 : Fin 4) = segnoC s (1 : Fin 4) * baseC (1 : Fin 4) := by
  simpa [tau4_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau4_600 s (1 : Fin 4)


-- @@ L1353-1356 verbatim
@[simp] private theorem vertC_tau4_coord3 (s : Fin 3 → Bool) :
    vertC tau4_600 s (3 : Fin 4) = segnoC s (3 : Fin 4) * baseC (3 : Fin 4) := by
  simpa [tau4_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau4_600 s (3 : Fin 4)


-- @@ L1358-1361 verbatim
@[simp] private theorem vertC_tau5_coord0 (s : Fin 3 → Bool) :
    vertC tau5_600 s (0 : Fin 4) = segnoC s (3 : Fin 4) * baseC (3 : Fin 4) := by
  simpa [tau5_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau5_600 s (3 : Fin 4)


-- @@ L1363-1366 verbatim
@[simp] private theorem vertC_tau5_coord1 (s : Fin 3 → Bool) :
    vertC tau5_600 s (1 : Fin 4) = segnoC s (0 : Fin 4) * baseC (0 : Fin 4) := by
  simpa [tau5_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau5_600 s (0 : Fin 4)


-- @@ L1368-1371 verbatim
@[simp] private theorem vertC_tau5_coord2 (s : Fin 3 → Bool) :
    vertC tau5_600 s (2 : Fin 4) = segnoC s (2 : Fin 4) * baseC (2 : Fin 4) := by
  simpa [tau5_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau5_600 s (2 : Fin 4)


-- @@ L1373-1376 verbatim
@[simp] private theorem vertC_tau5_coord3 (s : Fin 3 → Bool) :
    vertC tau5_600 s (3 : Fin 4) = segnoC s (1 : Fin 4) * baseC (1 : Fin 4) := by
  simpa [tau5_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau5_600 s (1 : Fin 4)


-- @@ L1378-1381 verbatim
@[simp] private theorem vertC_tau6_coord0 (s : Fin 3 → Bool) :
    vertC tau6_600 s (0 : Fin 4) = segnoC s (3 : Fin 4) * baseC (3 : Fin 4) := by
  simpa [tau6_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau6_600 s (3 : Fin 4)


-- @@ L1383-1386 verbatim
@[simp] private theorem vertC_tau6_coord1 (s : Fin 3 → Bool) :
    vertC tau6_600 s (1 : Fin 4) = segnoC s (1 : Fin 4) * baseC (1 : Fin 4) := by
  simpa [tau6_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau6_600 s (1 : Fin 4)


-- @@ L1388-1391 verbatim
@[simp] private theorem vertC_tau6_coord2 (s : Fin 3 → Bool) :
    vertC tau6_600 s (2 : Fin 4) = segnoC s (0 : Fin 4) * baseC (0 : Fin 4) := by
  simpa [tau6_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau6_600 s (0 : Fin 4)


-- @@ L1393-1396 verbatim
@[simp] private theorem vertC_tau6_coord3 (s : Fin 3 → Bool) :
    vertC tau6_600 s (3 : Fin 4) = segnoC s (2 : Fin 4) * baseC (2 : Fin 4) := by
  simpa [tau6_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau6_600 s (2 : Fin 4)


-- @@ L1398-1401 verbatim
@[simp] private theorem vertC_tau7_coord0 (s : Fin 3 → Bool) :
    vertC tau7_600 s (0 : Fin 4) = segnoC s (1 : Fin 4) * baseC (1 : Fin 4) := by
  simpa [tau7_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau7_600 s (1 : Fin 4)


-- @@ L1403-1406 verbatim
@[simp] private theorem vertC_tau7_coord1 (s : Fin 3 → Bool) :
    vertC tau7_600 s (1 : Fin 4) = segnoC s (2 : Fin 4) * baseC (2 : Fin 4) := by
  simpa [tau7_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau7_600 s (2 : Fin 4)


-- @@ L1408-1411 verbatim
@[simp] private theorem vertC_tau7_coord2 (s : Fin 3 → Bool) :
    vertC tau7_600 s (2 : Fin 4) = segnoC s (0 : Fin 4) * baseC (0 : Fin 4) := by
  simpa [tau7_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau7_600 s (0 : Fin 4)


-- @@ L1413-1416 verbatim
@[simp] private theorem vertC_tau7_coord3 (s : Fin 3 → Bool) :
    vertC tau7_600 s (3 : Fin 4) = segnoC s (3 : Fin 4) * baseC (3 : Fin 4) := by
  simpa [tau7_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau7_600 s (3 : Fin 4)


-- @@ L1418-1421 verbatim
@[simp] private theorem vertC_tau8_coord0 (s : Fin 3 → Bool) :
    vertC tau8_600 s (0 : Fin 4) = segnoC s (2 : Fin 4) * baseC (2 : Fin 4) := by
  simpa [tau8_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau8_600 s (2 : Fin 4)


-- @@ L1423-1426 verbatim
@[simp] private theorem vertC_tau8_coord1 (s : Fin 3 → Bool) :
    vertC tau8_600 s (1 : Fin 4) = segnoC s (3 : Fin 4) * baseC (3 : Fin 4) := by
  simpa [tau8_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau8_600 s (3 : Fin 4)


-- @@ L1428-1431 verbatim
@[simp] private theorem vertC_tau8_coord2 (s : Fin 3 → Bool) :
    vertC tau8_600 s (2 : Fin 4) = segnoC s (0 : Fin 4) * baseC (0 : Fin 4) := by
  simpa [tau8_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau8_600 s (0 : Fin 4)


-- @@ L1433-1436 verbatim
@[simp] private theorem vertC_tau8_coord3 (s : Fin 3 → Bool) :
    vertC tau8_600 s (3 : Fin 4) = segnoC s (1 : Fin 4) * baseC (1 : Fin 4) := by
  simpa [tau8_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau8_600 s (1 : Fin 4)


-- @@ L1438-1441 verbatim
@[simp] private theorem vertC_tau9_coord0 (s : Fin 3 → Bool) :
    vertC tau9_600 s (0 : Fin 4) = segnoC s (2 : Fin 4) * baseC (2 : Fin 4) := by
  simpa [tau9_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau9_600 s (2 : Fin 4)


-- @@ L1443-1446 verbatim
@[simp] private theorem vertC_tau9_coord1 (s : Fin 3 → Bool) :
    vertC tau9_600 s (1 : Fin 4) = segnoC s (1 : Fin 4) * baseC (1 : Fin 4) := by
  simpa [tau9_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau9_600 s (1 : Fin 4)


-- @@ L1448-1451 verbatim
@[simp] private theorem vertC_tau9_coord2 (s : Fin 3 → Bool) :
    vertC tau9_600 s (2 : Fin 4) = segnoC s (3 : Fin 4) * baseC (3 : Fin 4) := by
  simpa [tau9_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau9_600 s (3 : Fin 4)


-- @@ L1453-1456 verbatim
@[simp] private theorem vertC_tau9_coord3 (s : Fin 3 → Bool) :
    vertC tau9_600 s (3 : Fin 4) = segnoC s (0 : Fin 4) * baseC (0 : Fin 4) := by
  simpa [tau9_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau9_600 s (0 : Fin 4)


-- @@ L1458-1461 verbatim
@[simp] private theorem vertC_tau10_coord0 (s : Fin 3 → Bool) :
    vertC tau10_600 s (0 : Fin 4) = segnoC s (3 : Fin 4) * baseC (3 : Fin 4) := by
  simpa [tau10_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau10_600 s (3 : Fin 4)


-- @@ L1463-1466 verbatim
@[simp] private theorem vertC_tau10_coord1 (s : Fin 3 → Bool) :
    vertC tau10_600 s (1 : Fin 4) = segnoC s (2 : Fin 4) * baseC (2 : Fin 4) := by
  simpa [tau10_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau10_600 s (2 : Fin 4)


-- @@ L1468-1471 verbatim
@[simp] private theorem vertC_tau10_coord2 (s : Fin 3 → Bool) :
    vertC tau10_600 s (2 : Fin 4) = segnoC s (1 : Fin 4) * baseC (1 : Fin 4) := by
  simpa [tau10_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau10_600 s (1 : Fin 4)


-- @@ L1473-1476 verbatim
@[simp] private theorem vertC_tau10_coord3 (s : Fin 3 → Bool) :
    vertC tau10_600 s (3 : Fin 4) = segnoC s (0 : Fin 4) * baseC (0 : Fin 4) := by
  simpa [tau10_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau10_600 s (0 : Fin 4)


-- @@ L1478-1481 verbatim
@[simp] private theorem vertC_tau11_coord0 (s : Fin 3 → Bool) :
    vertC tau11_600 s (0 : Fin 4) = segnoC s (1 : Fin 4) * baseC (1 : Fin 4) := by
  simpa [tau11_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau11_600 s (1 : Fin 4)


-- @@ L1483-1486 verbatim
@[simp] private theorem vertC_tau11_coord1 (s : Fin 3 → Bool) :
    vertC tau11_600 s (1 : Fin 4) = segnoC s (3 : Fin 4) * baseC (3 : Fin 4) := by
  simpa [tau11_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau11_600 s (3 : Fin 4)


-- @@ L1488-1491 verbatim
@[simp] private theorem vertC_tau11_coord2 (s : Fin 3 → Bool) :
    vertC tau11_600 s (2 : Fin 4) = segnoC s (2 : Fin 4) * baseC (2 : Fin 4) := by
  simpa [tau11_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau11_600 s (2 : Fin 4)


-- @@ L1493-1496 verbatim
@[simp] private theorem vertC_tau11_coord3 (s : Fin 3 → Bool) :
    vertC tau11_600 s (3 : Fin 4) = segnoC s (0 : Fin 4) * baseC (0 : Fin 4) := by
  simpa [tau11_600, twoSwapAlt, Equiv.Perm.mul_apply,
    Equiv.swap_apply_def] using vertC_at tau11_600 s (0 : Fin 4)


-- @@ L1498-1540 verbatim
macro "h4_coord" : tactic =>
  `(tactic|
    (rw [r0_600_formula]
     ext j
     fin_cases j <;>
       (try simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
         Fin.sum_univ_four]) <;>
       (try simp only [vertC_tau0_coord0, vertC_tau0_coord1,
         vertC_tau0_coord2, vertC_tau0_coord3,
         vertC_tau1_coord0, vertC_tau1_coord1,
         vertC_tau1_coord2, vertC_tau1_coord3,
         vertC_tau2_coord0, vertC_tau2_coord1,
         vertC_tau2_coord2, vertC_tau2_coord3,
         vertC_tau3_coord0, vertC_tau3_coord1,
         vertC_tau3_coord2, vertC_tau3_coord3,
         vertC_tau4_coord0, vertC_tau4_coord1,
         vertC_tau4_coord2, vertC_tau4_coord3,
         vertC_tau5_coord0, vertC_tau5_coord1,
         vertC_tau5_coord2, vertC_tau5_coord3,
         vertC_tau6_coord0, vertC_tau6_coord1,
         vertC_tau6_coord2, vertC_tau6_coord3,
         vertC_tau7_coord0, vertC_tau7_coord1,
         vertC_tau7_coord2, vertC_tau7_coord3,
         vertC_tau8_coord0, vertC_tau8_coord1,
         vertC_tau8_coord2, vertC_tau8_coord3,
         vertC_tau9_coord0, vertC_tau9_coord1,
         vertC_tau9_coord2, vertC_tau9_coord3,
         vertC_tau10_coord0, vertC_tau10_coord1,
         vertC_tau10_coord2, vertC_tau10_coord3,
         vertC_tau11_coord0, vertC_tau11_coord1,
         vertC_tau11_coord2, vertC_tau11_coord3]) <;>
       (try simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply,
         bits3_600_apply0, bits3_600_apply1, bits3_600_apply2,
         bits4_600_apply0, bits4_600_apply1, bits4_600_apply2,
         bits4_600_apply3, segnoC, baseC, Fin.ext_iff,
         tau0_600, tau1_600, tau2_600, tau3_600, tau4_600, tau5_600,
         tau6_600, tau7_600, tau8_600, tau9_600, tau10_600, tau11_600,
         twoSwapAlt, ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv,
         Equiv.Perm.mul_apply, Equiv.swap_apply_def]) <;>
       (try (first
         | nlinarith [aureo_sq]
         | (left; nlinarith [aureo_sq])
         | (right; nlinarith [aureo_sq]))) <;> done))


-- @@ L1542-1545 verbatim
private theorem fun3_eq_bits (s : Fin 3 → Bool) :
    s = bits3_600 (s 0) (s 1) (s 2) := by
  funext j
  fin_cases j <;> simp [bits3_600]


-- @@ L1547-1550 verbatim
private theorem fun4_eq_bits (s : Fin 4 → Bool) :
    s = bits4_600 (s 0) (s 1) (s 2) (s 3) := by
  funext j
  fin_cases j <;> simp [bits4_600]


-- @@ L1552-1566 expanded
set_option maxHeartbeats 2000000 in
private theorem r0_vertA_mem (i : Fin 4) (b : Bool) : r0_600 (vertA i b) ∈ seicentoVertici := by
  classical
  simp only [seicentoVertici, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  fin_cases i <;> cases b
  ·
    exact
      Or.inr
        ⟨(tau0_600, bits3_600 false false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau0_600, bits3_600 true true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau7_600, bits3_600 true false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau7_600, bits3_600 false true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau4_600, bits3_600 true false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau4_600, bits3_600 false true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inl
        (Or.inl
          ⟨((3, false) : Fin 4 × Bool), by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inl
        (Or.inl
          ⟨((3, true) : Fin 4 × Bool), by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)


-- @@ L1568-1591 expanded
set_option maxHeartbeats 2000000 in
private theorem r0_vertB_mem (s : Fin 4 → Bool) : r0_600 (vertB s) ∈ seicentoVertici := by
  classical
  rw [fun4_eq_bits s]
  simp only [seicentoVertici, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  cases s0 : s 0 <;> cases s1 : s 1 <;> cases s2 : s 2 <;> cases s3 : s 3
  ·
    exact
      Or.inr
        ⟨(tau2_600, bits3_600 false false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau2_600, bits3_600 false true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inl
        (Or.inr
          ⟨bits4_600 false false true false, by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inl
        (Or.inr
          ⟨bits4_600 false false true true, by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inr
        ⟨(tau8_600, bits3_600 false false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau8_600, bits3_600 false true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau5_600, bits3_600 false false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau5_600, bits3_600 false true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau5_600, bits3_600 true false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau5_600, bits3_600 true true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau8_600, bits3_600 true false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau8_600, bits3_600 true true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inl
        (Or.inr
          ⟨bits4_600 true true false false, by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inl
        (Or.inr
          ⟨bits4_600 true true false true, by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inr
        ⟨(tau2_600, bits3_600 true false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau2_600, bits3_600 true true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩


-- @@ L1593-1696 expanded
set_option maxHeartbeats 4000000 in
private theorem r0_vertC_mem (σ : alternatingGroup (Fin 4)) (s : Fin 3 → Bool) :
    r0_600 (vertC σ s) ∈ seicentoVertici := by
  classical
  rw [fun3_eq_bits s]
  simp only [seicentoVertici, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  fin_cases σ <;> cases s0 : s 0 <;> cases s1 : s 1 <;> cases s2 : s 2
  ·
    exact
      Or.inl
        (Or.inl
          ⟨((0, false) : Fin 4 × Bool), by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inr
        ⟨(tau0_600, bits3_600 false false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau7_600, bits3_600 false false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau4_600, bits3_600 false false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau4_600, bits3_600 true true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau7_600, bits3_600 true true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau0_600, bits3_600 true true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inl
        (Or.inl
          ⟨((0, true) : Fin 4 × Bool), by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inr
        ⟨(tau1_600, bits3_600 false false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau1_600, bits3_600 false false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau3_600, bits3_600 false false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau3_600, bits3_600 false false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau3_600, bits3_600 true true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau3_600, bits3_600 true true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau1_600, bits3_600 true true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau1_600, bits3_600 true true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau2_600, bits3_600 false false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inl
        (Or.inr
          ⟨bits4_600 false false false false, by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inr
        ⟨(tau2_600, bits3_600 false true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inl
        (Or.inr
          ⟨bits4_600 false false false true, by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inl
        (Or.inr
          ⟨bits4_600 true true true false, by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inr
        ⟨(tau2_600, bits3_600 true false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inl
        (Or.inr
          ⟨bits4_600 true true true true, by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inr
        ⟨(tau2_600, bits3_600 true true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau1_600, bits3_600 false true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau1_600, bits3_600 false true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau6_600, bits3_600 true true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau6_600, bits3_600 true true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau6_600, bits3_600 false false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau6_600, bits3_600 false false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau1_600, bits3_600 true false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau1_600, bits3_600 true false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau0_600, bits3_600 false true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau4_600, bits3_600 true true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau7_600, bits3_600 true false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inl
        (Or.inl
          ⟨((2, true) : Fin 4 × Bool), by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inl
        (Or.inl
          ⟨((2, false) : Fin 4 × Bool), by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inr
        ⟨(tau7_600, bits3_600 false true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau4_600, bits3_600 false false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau0_600, bits3_600 true false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inl
        (Or.inr
          ⟨bits4_600 false true true false, by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inr
        ⟨(tau8_600, bits3_600 true false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inl
        (Or.inr
          ⟨bits4_600 false true true true, by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inr
        ⟨(tau8_600, bits3_600 true true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau8_600, bits3_600 false false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inl
        (Or.inr
          ⟨bits4_600 true false false false, by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inr
        ⟨(tau8_600, bits3_600 false true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inl
        (Or.inr
          ⟨bits4_600 true false false true, by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inr
        ⟨(tau3_600, bits3_600 true false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau3_600, bits3_600 true false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau6_600, bits3_600 false true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau6_600, bits3_600 false true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau6_600, bits3_600 true false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau6_600, bits3_600 true false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau3_600, bits3_600 false true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau3_600, bits3_600 false true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau0_600, bits3_600 false true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau7_600, bits3_600 false false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inl
        (Or.inl
          ⟨((1, true) : Fin 4 × Bool), by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inr
        ⟨(tau4_600, bits3_600 true false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau4_600, bits3_600 false true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inl
        (Or.inl
          ⟨((1, false) : Fin 4 × Bool), by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inr
        ⟨(tau7_600, bits3_600 true true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau0_600, bits3_600 true false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inl
        (Or.inr
          ⟨bits4_600 false true false false, by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inr
        ⟨(tau5_600, bits3_600 true false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inl
        (Or.inr
          ⟨bits4_600 false true false true, by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inr
        ⟨(tau5_600, bits3_600 true true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau5_600, bits3_600 false false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inl
        (Or.inr
          ⟨bits4_600 true false true false, by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inr
        ⟨(tau5_600, bits3_600 false true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inl
        (Or.inr
          ⟨bits4_600 true false true true, by
            ( rw [r0_600_formula]
              ext j
              fin_cases j <;>
                        (try
                            simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                              Fin.sum_univ_four]) <;>
                      (try
                          simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                            vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                            vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                            vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                            vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                            vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                            vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                            vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                            vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                            vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                            vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                            vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                            vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                            vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                            vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                            vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                    (try
                        simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                          bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                          bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                          tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                          tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt,
                          ← Equiv.Perm.inv_def, mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                          Equiv.swap_apply_def]) <;>
                  (try
                      (first
                        | nlinarith [aureo_sq]
                        | (left; nlinarith [aureo_sq])
                        | (right; nlinarith [aureo_sq]))) <;>
                done)⟩)
  ·
    exact
      Or.inr
        ⟨(tau11_600, bits3_600 false false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau10_600, bits3_600 false true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau10_600, bits3_600 false false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau11_600, bits3_600 false true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau11_600, bits3_600 true false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau10_600, bits3_600 true true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau10_600, bits3_600 true false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau11_600, bits3_600 true true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau9_600, bits3_600 false true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau10_600, bits3_600 false false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau10_600, bits3_600 false true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau9_600, bits3_600 false false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau9_600, bits3_600 true true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau10_600, bits3_600 true false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau10_600, bits3_600 true true false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau9_600, bits3_600 true false true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau11_600, bits3_600 false false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau9_600, bits3_600 false false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau9_600, bits3_600 false true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau11_600, bits3_600 false true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau11_600, bits3_600 true false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau9_600, bits3_600 true false false), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau9_600, bits3_600 true true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩
  ·
    exact
      Or.inr
        ⟨(tau11_600, bits3_600 true true true), by
          ( rw [r0_600_formula]
            ext j
            fin_cases j <;>
                      (try
                          simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
                            Fin.sum_univ_four]) <;>
                    (try
                        simp only [vertC_tau0_coord0, vertC_tau0_coord1, vertC_tau0_coord2,
                          vertC_tau0_coord3, vertC_tau1_coord0, vertC_tau1_coord1,
                          vertC_tau1_coord2, vertC_tau1_coord3, vertC_tau2_coord0,
                          vertC_tau2_coord1, vertC_tau2_coord2, vertC_tau2_coord3,
                          vertC_tau3_coord0, vertC_tau3_coord1, vertC_tau3_coord2,
                          vertC_tau3_coord3, vertC_tau4_coord0, vertC_tau4_coord1,
                          vertC_tau4_coord2, vertC_tau4_coord3, vertC_tau5_coord0,
                          vertC_tau5_coord1, vertC_tau5_coord2, vertC_tau5_coord3,
                          vertC_tau6_coord0, vertC_tau6_coord1, vertC_tau6_coord2,
                          vertC_tau6_coord3, vertC_tau7_coord0, vertC_tau7_coord1,
                          vertC_tau7_coord2, vertC_tau7_coord3, vertC_tau8_coord0,
                          vertC_tau8_coord1, vertC_tau8_coord2, vertC_tau8_coord3,
                          vertC_tau9_coord0, vertC_tau9_coord1, vertC_tau9_coord2,
                          vertC_tau9_coord3, vertC_tau10_coord0, vertC_tau10_coord1,
                          vertC_tau10_coord2, vertC_tau10_coord3, vertC_tau11_coord0,
                          vertC_tau11_coord1, vertC_tau11_coord2, vertC_tau11_coord3]) <;>
                  (try
                      simp [alpha0_600, vertA_apply, vertB_apply, vertC_apply, bits3_600_apply0,
                        bits3_600_apply1, bits3_600_apply2, bits4_600_apply0, bits4_600_apply1,
                        bits4_600_apply2, bits4_600_apply3, segnoC, baseC, Fin.ext_iff, tau0_600,
                        tau1_600, tau2_600, tau3_600, tau4_600, tau5_600, tau6_600, tau7_600,
                        tau8_600, tau9_600, tau10_600, tau11_600, twoSwapAlt, ← Equiv.Perm.inv_def,
                        mul_inv_rev, Equiv.swap_inv, Equiv.Perm.mul_apply,
                        Equiv.swap_apply_def]) <;>
                (try
                    (first
                      | nlinarith [aureo_sq]
                      | (left; nlinarith [aureo_sq])
                      | (right; nlinarith [aureo_sq]))) <;>
              done)⟩


-- @@ L1698-1709 verbatim
private theorem r0_mem_seicentoVertici {v : E4} (hv : v ∈ seicentoVertici) :
    r0_600 v ∈ seicentoVertici := by
  classical
  simp only [seicentoVertici, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hv
  rcases hv with (⟨p, hp⟩ | ⟨s, hs⟩) | ⟨p, hp⟩
  · rw [← hp]
    exact r0_vertA_mem p.1 p.2
  · rw [← hs]
    exact r0_vertB_mem s
  · rw [← hp]
    exact r0_vertC_mem p.1 p.2


-- @@ L1711-1722 verbatim
private theorem r0_image_seicentoVertici :
    (r0_600 : E4 → E4) '' (seicentoVertici : Set E4) =
      (seicentoVertici : Set E4) := by
  have hfin : Finset.image (r0_600 : E4 → E4) seicentoVertici =
      seicentoVertici := by
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      rw [Finset.mem_image] at hv
      obtain ⟨u, hu, rfl⟩ := hv
      exact r0_mem_seicentoVertici hu
    · rw [Finset.card_image_of_injective _ r0_600.injective]
  rw [← Finset.coe_image, hfin]


-- @@ L1724-1734 verbatim
theorem r0_600_isSymmetry : seicento.isSymmetry r0_600 := by
  rw [ConvexPolytope.isSymmetry, ConvexPolytope.toSet]
  calc
    (r0_600 : E4 → E4) ''
        convexHull ℝ ((seicento.vertices : Finset E4) : Set E4) =
      convexHull ℝ ((r0_600 : E4 → E4) ''
        ((seicento.vertices : Finset E4) : Set E4)) := by
          exact r0_600.toAffineEquiv.toAffineMap.image_convexHull _
    _ = convexHull ℝ ((seicento.vertices : Finset E4) : Set E4) := by
      rw [show ((seicento.vertices : Finset E4) : Set E4) =
          (seicentoVertici : Set E4) by rfl, r0_image_seicentoVertici]


-- @@ L1736-1740 verbatim
private theorem r0_image_F1_600 : (r0_600 : E4 → E4) '' F1_600 = F1_600 := by
  rw [F1_600, image_convexHull_isom600]
  congr 1
  ext x
  simp [generatoriF1_600, r0_600_vertices.1, r0_600_vertices.2.1] <;> tauto


-- @@ L1742-1747 verbatim
private theorem r0_image_F2_600 : (r0_600 : E4 → E4) '' F2_600 = F2_600 := by
  rw [F2_600, image_convexHull_isom600]
  congr 1
  ext x
  simp [generatoriF2_600, r0_600_vertices.1, r0_600_vertices.2.1,
    r0_600_vertices.2.2.1] <;> tauto


-- @@ L1749-1754 verbatim
private theorem r0_image_F3_600 : (r0_600 : E4 → E4) '' F3_600 = F3_600 := by
  rw [F3_600, image_convexHull_isom600]
  congr 1
  ext x
  simp [generatoriF3_600, r0_600_vertices.1, r0_600_vertices.2.1,
    r0_600_vertices.2.2.1, r0_600_vertices.2.2.2] <;> tauto


-- @@ L1756-1763 verbatim
private theorem r0_moves_F0_600 : (r0_600 : E4 → E4) '' F0_600 ≠ F0_600 := by
  intro h
  have hc : c1_600 ∈ (r0_600 : E4 → E4) '' F0_600 :=
    ⟨e1_600, subset_convexHull ℝ _ (by simp [generatoriF0_600]),
      r0_600_vertices.1⟩
  rw [h, F0_600, generatoriF0_600] at hc
  have heq : c1_600 = e1_600 := by simpa using hc
  exact e1_ne_c1_600 heq.symm


-- @@ L1765-1775 verbatim
theorem r0_600_flagAdjacent :
    FlagAdjacentAt seicento seicentoFlag
      (mapFlag seicento r0_600_isSymmetry seicentoFlag) 0 := by
  constructor
  · intro j hj
    fin_cases j
    · exact (hj rfl).elim
    · exact r0_image_F1_600
    · exact r0_image_F2_600
    · exact r0_image_F3_600
  · exact r0_moves_F0_600


-- @@ L1777-1778 verbatim
private def segnoUno_600 : Fin 4 → ({-1, 1} : Set ℝ) :=
  fun _ => ⟨1, by simp⟩


-- @@ L1780-1781 verbatim
private def g2Linear_600 : E4 ≃ₗᵢ[ℝ] E4 :=
  segnoLinear 4 (tau5_600 : Equiv.Perm (Fin 4)) segnoUno_600


-- @@ L1783-1784 verbatim
private def g2_600 : Isom 4 :=
  segnoPerm 4 (tau5_600 : Equiv.Perm (Fin 4)) segnoUno_600


-- @@ L1786-1786 verbatim
def alpha2_600 : E4 := g2Linear_600 alpha0_600


-- @@ L1788-1812 verbatim
private theorem alpha2_coordinates :
    ∀ j : Fin 4, alpha2_600 j =
      ![(0 : ℝ), (aureo - 1) / 2, -(1 / 2 : ℝ), -aureo / 2] j := by
  intro j
  fin_cases j
  · simpa [alpha2_600, g2Linear_600, tau5_600, twoSwapAlt,
      segnoUno_600, alpha0_600, Equiv.Perm.mul_apply,
      Equiv.swap_apply_def, Fin.ext_iff] using
      (segnoLinear_apply_coord_600 4 (tau5_600 : Equiv.Perm (Fin 4))
        segnoUno_600 alpha0_600 (3 : Fin 4))
  · simpa [alpha2_600, g2Linear_600, tau5_600, twoSwapAlt,
      segnoUno_600, alpha0_600, Equiv.Perm.mul_apply,
      Equiv.swap_apply_def, Fin.ext_iff] using
      (segnoLinear_apply_coord_600 4 (tau5_600 : Equiv.Perm (Fin 4))
        segnoUno_600 alpha0_600 (0 : Fin 4))
  · simpa [alpha2_600, g2Linear_600, tau5_600, twoSwapAlt,
      segnoUno_600, alpha0_600, Equiv.Perm.mul_apply,
      Equiv.swap_apply_def, Fin.ext_iff] using
      (segnoLinear_apply_coord_600 4 (tau5_600 : Equiv.Perm (Fin 4))
        segnoUno_600 alpha0_600 (2 : Fin 4))
  · simpa [alpha2_600, g2Linear_600, tau5_600, twoSwapAlt,
      segnoUno_600, alpha0_600, Equiv.Perm.mul_apply,
      Equiv.swap_apply_def, Fin.ext_iff] using
      (segnoLinear_apply_coord_600 4 (tau5_600 : Equiv.Perm (Fin 4))
        segnoUno_600 alpha0_600 (1 : Fin 4))


-- @@ L1814-1817 verbatim
@[simp] private theorem alpha2_coord0 : alpha2_600 0 = 0 := by
  rw [alpha2_coordinates 0]
  change (0 : ℝ) = 0
  rfl


-- @@ L1819-1823 verbatim
@[simp] private theorem alpha2_coord1 :
    alpha2_600 1 = (aureo - 1) / 2 := by
  rw [alpha2_coordinates 1]
  change (aureo - 1) / 2 = (aureo - 1) / 2
  rfl


-- @@ L1825-1828 verbatim
@[simp] private theorem alpha2_coord2 : alpha2_600 2 = -(1 / 2 : ℝ) := by
  rw [alpha2_coordinates 2]
  change -(1 / 2 : ℝ) = -(1 / 2 : ℝ)
  rfl


-- @@ L1830-1833 verbatim
@[simp] private theorem alpha2_coord3 : alpha2_600 3 = -aureo / 2 := by
  rw [alpha2_coordinates 3]
  change -aureo / 2 = -aureo / 2
  rfl


-- @@ L1835-1840 verbatim
private theorem alpha2_parallel :
    c2_600 - c3_600 = (aureo - 1) • alpha2_600 := by
  ext j
  fin_cases j <;>
    simp [alpha2_coordinates, Fin.ext_iff] <;>
    nlinarith [aureo_sq]


-- @@ L1842-1843 verbatim
private theorem norm_alpha2_600 : ‖alpha2_600‖ = 1 := by
  rw [alpha2_600, g2Linear_600.norm_map, norm_alpha0_600]


-- @@ L1845-1847 verbatim
/-- Rank-two wall: orthogonal reflection perpendicular to `c₂-c₃`. -/
def r2_600 : Isom 4 :=
  ((ℝ ∙ alpha2_600)ᗮ).reflection.toAffineIsometryEquiv


-- @@ L1849-1855 verbatim
private theorem r2_600_formula (x : E4) :
    r2_600 x = x - (2 * ⟪alpha2_600, x⟫ : ℝ) • alpha2_600 := by
  change ((ℝ ∙ alpha2_600)ᗮ).reflection x = _
  rw [Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply, norm_alpha2_600]
  norm_num
  module


-- @@ L1857-1866 verbatim
private theorem alpha2_inner_flag :
    ⟪alpha2_600, e1_600⟫ = 0 ∧
    ⟪alpha2_600, c1_600⟫ = 0 ∧
    ⟪alpha2_600, c2_600⟫ = (aureo - 1) / 2 ∧
    ⟪alpha2_600, c3_600⟫ = -(aureo - 1) / 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial,
      Fin.sum_univ_four] <;>
    simp <;>
    nlinarith [aureo_sq]


-- @@ L1868-1872 verbatim
private theorem span_map_g2_600 :
    (ℝ ∙ alpha0_600).map
      (g2Linear_600.toLinearEquiv : E4 →ₗ[ℝ] E4) = ℝ ∙ alpha2_600 := by
  rw [Submodule.map_span]
  simp [alpha2_600]


-- @@ L1874-1878 verbatim
private theorem wall_map_g2_600 :
    ((ℝ ∙ alpha0_600)ᗮ).map
      (g2Linear_600.toLinearEquiv : E4 →ₗ[ℝ] E4) =
      (ℝ ∙ alpha2_600)ᗮ := by
  rw [Submodule.map_orthogonal_equiv, span_map_g2_600]


-- @@ L1880-1887 verbatim
private theorem r2_conjugate :
    r2_600 = g2_600.symm.trans (r0_600.trans g2_600) := by
  apply AffineIsometryEquiv.ext
  intro x
  change ((ℝ ∙ alpha2_600)ᗮ).reflection x =
    g2Linear_600 (((ℝ ∙ alpha0_600)ᗮ).reflection (g2Linear_600.symm x))
  simpa only [wall_map_g2_600] using
    (Submodule.reflection_map_apply g2Linear_600 ((ℝ ∙ alpha0_600)ᗮ) x)


-- @@ L1889-1890 verbatim
private theorem g2_600_isSymmetry : seicento.isSymmetry g2_600 :=
  signedEven_isSymmetry_seicento tau5_600 segnoUno_600


-- @@ L1892-1895 verbatim
theorem r2_600_isSymmetry : seicento.isSymmetry r2_600 := by
  rw [r2_conjugate]
  exact symmetry_transN (symmetry_symmN g2_600_isSymmetry)
    (symmetry_transN r0_600_isSymmetry g2_600_isSymmetry)


-- @@ L1897-1910 verbatim
private theorem r2_600_vertices :
    r2_600 e1_600 = e1_600 ∧ r2_600 c1_600 = c1_600 ∧
      r2_600 c2_600 = c3_600 ∧ r2_600 c3_600 = c2_600 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [r2_600_formula, alpha2_inner_flag.1]
    simp
  · rw [r2_600_formula, alpha2_inner_flag.2.1]
    simp
  · rw [r2_600_formula, alpha2_inner_flag.2.2.1]
    ext j
    fin_cases j <;> simp <;> nlinarith [aureo_sq]
  · rw [r2_600_formula, alpha2_inner_flag.2.2.2]
    ext j
    fin_cases j <;> simp <;> nlinarith [aureo_sq]


-- @@ L1912-1916 verbatim
private theorem r2_image_F0_600 : (r2_600 : E4 → E4) '' F0_600 = F0_600 := by
  rw [F0_600, image_convexHull_isom600]
  congr 1
  ext x
  simp [generatoriF0_600, r2_600_vertices.1]


-- @@ L1918-1922 verbatim
private theorem r2_image_F1_600 : (r2_600 : E4 → E4) '' F1_600 = F1_600 := by
  rw [F1_600, image_convexHull_isom600]
  congr 1
  ext x
  simp [generatoriF1_600, r2_600_vertices.1, r2_600_vertices.2.1] <;> tauto


-- @@ L1924-1929 verbatim
private theorem r2_image_F3_600 : (r2_600 : E4 → E4) '' F3_600 = F3_600 := by
  rw [F3_600, image_convexHull_isom600]
  congr 1
  ext x
  simp [generatoriF3_600, r2_600_vertices.1, r2_600_vertices.2.1,
    r2_600_vertices.2.2.1, r2_600_vertices.2.2.2] <;> tauto


-- @@ L1931-1954 verbatim
private theorem l2_eq_on_F2_600 {x : E4} (hx : x ∈ F2_600) :
    l2_600 x = 1 + aureo := by
  rw [F2_600] at hx
  exact le_antisymm
    (convexHull_min (fun y hy => by
        change l2_600 y ≤ 1 + aureo
        have hc : y = e1_600 ∨ y = c1_600 ∨ y = c2_600 := by
          simpa [generatoriF2_600] using hy
        rcases hc with rfl | rfl | rfl
        · rw [small_functional_values.2.2.1]
        · rw [small_functional_values.2.2.2.1]
        · rw [small_functional_values.2.2.2.2.1])
      (convex_halfSpace_le (LinearMap.isLinear l2_600.toLinearMap)
        (1 + aureo)) hx)
    (convexHull_min (fun y hy => by
        change 1 + aureo ≤ l2_600 y
        have hc : y = e1_600 ∨ y = c1_600 ∨ y = c2_600 := by
          simpa [generatoriF2_600] using hy
        rcases hc with rfl | rfl | rfl
        · rw [small_functional_values.2.2.1]
        · rw [small_functional_values.2.2.2.1]
        · rw [small_functional_values.2.2.2.2.1])
      (convex_halfSpace_ge (LinearMap.isLinear l2_600.toLinearMap)
        (1 + aureo)) hx)


-- @@ L1956-1964 verbatim
private theorem r2_moves_F2_600 : (r2_600 : E4 → E4) '' F2_600 ≠ F2_600 := by
  intro h
  have hc : c3_600 ∈ (r2_600 : E4 → E4) '' F2_600 :=
    ⟨c2_600, subset_convexHull ℝ _ (by simp [generatoriF2_600]),
      r2_600_vertices.2.2.1⟩
  rw [h] at hc
  have hv := l2_eq_on_F2_600 hc
  rw [small_functional_values.2.2.2.2.2] at hv
  linarith [aureo_bounds.2]


-- @@ L1966-1976 verbatim
theorem r2_600_flagAdjacent :
    FlagAdjacentAt seicento seicentoFlag
      (mapFlag seicento r2_600_isSymmetry seicentoFlag) 2 := by
  constructor
  · intro j hj
    fin_cases j
    · exact r2_image_F0_600
    · exact r2_image_F1_600
    · exact (hj rfl).elim
    · exact r2_image_F3_600
  · exact r2_moves_F2_600


-- @@ L1978-1978 verbatim
end LeanEval.Geometry.PlatonicClassification
