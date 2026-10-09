import OAI.Combinatorics.SecondNeighborhood.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SeymourSecondNeighborhood


-- @@ L7-7 verbatim
variable {V : Type*}


-- @@ L9-12 verbatim
theorem IsOriented.of_asymmetric {r : V → V → Prop}
    (h : ∀ {u v}, r u v → ¬ r v u) : IsOriented r where
  loopless _ hv := h hv hv
  asymmetric := h


-- @@ L14-17 verbatim
theorem IsOriented.mono {r s : V → V → Prop}
    (hr : IsOriented r) (h : ∀ u v, s u v → r u v) : IsOriented s where
  loopless v hv := hr.loopless v (h v v hv)
  asymmetric huv hvu := hr.asymmetric (h _ _ huv) (h _ _ hvu)


-- @@ L19-19 verbatim
variable [Fintype V] [DecidableEq V]


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-25 verbatim
def image (r : V → V → Prop) (S : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter (fun y => ∃ x ∈ S, r x y)


-- @@ L27-28 verbatim
def SecondNeighborhoodConjecture (r : V → V → Prop) : Prop :=
  ∃ v, GoodVertex r v


-- @@ L30-34 verbatim
omit [DecidableEq V] in
@[simp] theorem mem_image {r : V → V → Prop} {S : Finset V} {y : V} :
    y ∈ image r S ↔ ∃ x ∈ S, r x y := by
  classical
  simp [image]


-- @@ L36-40 verbatim
omit [DecidableEq V] in
@[simp] theorem mem_firstNeighbors {r : V → V → Prop} {v w : V} :
    w ∈ firstNeighbors r v ↔ r v w := by
  classical
  simp [firstNeighbors]


-- @@ L42-45 verbatim
@[simp] theorem mem_secondNeighbors {r : V → V → Prop} {v w : V} :
    w ∈ secondNeighbors r v ↔ w ≠ v ∧ ¬ r v w ∧ ∃ u, r v u ∧ r u w := by
  classical
  simp [secondNeighbors]


-- @@ L47-51 verbatim
omit [DecidableEq V] in
@[simp] theorem image_empty (r : V → V → Prop) : image r ∅ = ∅ := by
  classical
  ext y
  simp


-- @@ L53-58 verbatim
omit [DecidableEq V] in
@[simp] theorem image_singleton (r : V → V → Prop) (v : V) :
    image r {v} = firstNeighbors r v := by
  classical
  ext y
  simp


-- @@ L60-65 verbatim
omit [DecidableEq V] in
theorem image_mono (r : V → V → Prop) {S T : Finset V} (h : S ⊆ T) :
    image r S ⊆ image r T := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := mem_image.mp hy
  exact mem_image.mpr ⟨x, h hx, hxy⟩


-- @@ L67-72 verbatim
omit [DecidableEq V] in
theorem image_relation_mono {r s : V → V → Prop}
    (h : ∀ x y, r x y → s x y) (S : Finset V) : image r S ⊆ image s S := by
  intro y hy
  obtain ⟨x, hx, hxy⟩ := mem_image.mp hy
  exact mem_image.mpr ⟨x, hx, h x y hxy⟩


-- @@ L74-89 verbatim
@[simp] theorem image_union (r : V → V → Prop) (S T : Finset V) :
    image r (S ∪ T) = image r S ∪ image r T := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, hxy⟩ := mem_image.mp hy
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union.mpr (Or.inl (mem_image.mpr ⟨x, hx, hxy⟩))
    · exact Finset.mem_union.mpr (Or.inr (mem_image.mpr ⟨x, hx, hxy⟩))
  · intro hy
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨x, hx, hxy⟩ := mem_image.mp hy
      exact mem_image.mpr ⟨x, Finset.mem_union.mpr (Or.inl hx), hxy⟩
    · obtain ⟨x, hx, hxy⟩ := mem_image.mp hy
      exact mem_image.mpr ⟨x, Finset.mem_union.mpr (Or.inr hx), hxy⟩


-- @@ L91-101 verbatim
omit [DecidableEq V] in
theorem image_univ_eq_univ (r : V → V → Prop) (h : ∀ v, ∃ u, r u v) :
    image r Finset.univ = Finset.univ := by
  classical
  ext y
  constructor
  · intro _
    exact Finset.mem_univ y
  · intro _
    obtain ⟨x, hxy⟩ := h y
    exact mem_image.mpr ⟨x, Finset.mem_univ x, hxy⟩


-- @@ L103-107 verbatim
omit [DecidableEq V] in
theorem firstNeighbors_subset_image {r : V → V → Prop} {S : Finset V}
    {v : V} (hv : v ∈ S) : firstNeighbors r v ⊆ image r S := by
  intro w hw
  exact mem_image.mpr ⟨v, hv, mem_firstNeighbors.mp hw⟩


-- @@ L109-113 verbatim
omit [DecidableEq V] in
@[simp] theorem self_not_mem_firstNeighbors {r : V → V → Prop}
    (hr : IsOriented r) (v : V) : v ∉ firstNeighbors r v := by
  intro hv
  exact hr.loopless v (mem_firstNeighbors.mp hv)


-- @@ L115-118 verbatim
@[simp] theorem self_not_mem_secondNeighbors (r : V → V → Prop) (v : V) :
    v ∉ secondNeighbors r v := by
  intro hv
  exact (mem_secondNeighbors.mp hv).1 rfl


-- @@ L120-124 verbatim
theorem first_second_disjoint (r : V → V → Prop) (v : V) :
    Disjoint (firstNeighbors r v) (secondNeighbors r v) := by
  apply Finset.disjoint_left.mpr
  intro w hfirst hsecond
  exact (mem_secondNeighbors.mp hsecond).2.1 (mem_firstNeighbors.mp hfirst)


-- @@ L126-130 verbatim
omit [Fintype V] [DecidableEq V] in
theorem no_two_step_self {r : V → V → Prop} (hr : IsOriented r) (v : V) :
    ¬ ∃ u, r v u ∧ r u v := by
  rintro ⟨u, hvu, huv⟩
  exact hr.asymmetric hvu huv


-- @@ L132-136 verbatim
omit [DecidableEq V] in
theorem mem_image_image_singleton {r : V → V → Prop} {v w : V} :
    w ∈ image r (image r {v}) ↔ ∃ u, r v u ∧ r u w := by
  classical
  simp


-- @@ L138-157 verbatim
theorem secondNeighbors_eq_image_sdiff {r : V → V → Prop}
    (hr : IsOriented r) (v : V) :
    secondNeighbors r v = image r (image r {v}) \ image r {v} := by
  classical
  ext w
  constructor
  · intro hw
    obtain ⟨_, hnot, hpath⟩ := mem_secondNeighbors.mp hw
    apply Finset.mem_sdiff.mpr
    refine ⟨mem_image_image_singleton.mpr hpath, ?_⟩
    simpa using hnot
  · intro hw
    obtain ⟨hpath, hnot⟩ := Finset.mem_sdiff.mp hw
    have hpath' := mem_image_image_singleton.mp hpath
    apply mem_secondNeighbors.mpr
    refine ⟨?_, ?_, hpath'⟩
    · intro heq
      subst w
      exact no_two_step_self hr v hpath'
    · simpa using hnot


-- @@ L159-164 verbatim
omit [DecidableEq V] in
theorem sink_firstNeighbors_eq_empty {r : V → V → Prop} {v : V}
    (hsink : ∀ w, ¬ r v w) : firstNeighbors r v = ∅ := by
  classical
  ext w
  simp [hsink w]


-- @@ L166-172 verbatim
theorem sink_secondNeighbors_eq_empty {r : V → V → Prop} {v : V}
    (hsink : ∀ w, ¬ r v w) : secondNeighbors r v = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨_, _, u, hvu, _⟩ := mem_secondNeighbors.mp hw
  exact hsink u hvu


-- @@ L174-178 verbatim
theorem sink_goodVertex {r : V → V → Prop} {v : V}
    (hsink : ∀ w, ¬ r v w) : GoodVertex r v := by
  unfold GoodVertex
  rw [sink_firstNeighbors_eq_empty hsink, Finset.card_empty]
  exact Nat.zero_le _


-- @@ L180-183 verbatim
theorem exists_sink_implies_conjecture {r : V → V → Prop}
    (hsink : ∃ v, ∀ w, ¬ r v w) : SecondNeighborhoodConjecture r := by
  obtain ⟨v, hv⟩ := hsink
  exact ⟨v, sink_goodVertex hv⟩


-- @@ L185-185 verbatim
end

-- @@ L186-186 verbatim
end SeymourSecondNeighborhood


-- @@ L188-188 verbatim
end OAI
