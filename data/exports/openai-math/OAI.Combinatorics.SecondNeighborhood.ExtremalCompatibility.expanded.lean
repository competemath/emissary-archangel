import OAI.Combinatorics.SecondNeighborhood.ExtremalImages


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace SeymourSecondNeighborhood.Extremal


-- @@ L7-7 verbatim
open Pruning


-- @@ L9-9 verbatim
variable {V : Type*} [Fintype V] [DecidableEq V]


-- @@ L11-11 verbatim
noncomputable section


-- @@ L13-14 verbatim
abbrev Compatible (r : V → V → Prop) (P Q : Finset (V × V)) : Prop :=
  ConflictFree r P Q


-- @@ L16-19 verbatim
structure Admissible (r : V → V → Prop) (P Q : Finset (V × V)) : Prop where
  compatible : Compatible r P Q
  diagonal_left : diagonal ⊆ P
  diagonal_right : diagonal ⊆ Q


-- @@ L21-22 verbatim
def leftCandidate (r : V → V → Prop) (Q : Finset (V × V)) : Finset (V × V) :=
  Finset.univ \ rightImage r (rightImage r Q)


-- @@ L24-25 verbatim
def rightCandidate (r : V → V → Prop) (P : Finset (V × V)) : Finset (V × V) :=
  Finset.univ \ leftImage r (leftImage r P)


-- @@ L27-28 verbatim
def uncovered (r : V → V → Prop) (P Q : Finset (V × V)) : Finset (V × V) :=
  Finset.univ \ (leftImage r P ∪ rightImage r Q)


-- @@ L30-33 verbatim
@[simp] theorem mem_leftCandidate {r : V → V → Prop} {Q : Finset (V × V)}
    {z : V × V} : z ∈ leftCandidate r Q ↔ z ∉ rightImage r (rightImage r Q) := by
  classical
  simp [leftCandidate]


-- @@ L35-38 verbatim
@[simp] theorem mem_rightCandidate {r : V → V → Prop} {P : Finset (V × V)}
    {z : V × V} : z ∈ rightCandidate r P ↔ z ∉ leftImage r (leftImage r P) := by
  classical
  simp [rightCandidate]


-- @@ L40-43 verbatim
@[simp] theorem mem_uncovered {r : V → V → Prop} {P Q : Finset (V × V)}
    {z : V × V} : z ∈ uncovered r P Q ↔ ¬ Covered r P Q z := by
  classical
  simp [uncovered, Covered]


-- @@ L45-52 verbatim
theorem diagonal_compatible {r : V → V → Prop} (hr : IsOriented r) :
    Compatible r (diagonal : Finset (V × V)) diagonal := by
  intro a ha b hb hc
  have ha' := mem_diagonal.mp ha
  have hb' := mem_diagonal.mp hb
  have hreverse : r b.1 a.1 := by
    simpa only [← ha', ← hb'] using hc.2
  exact hr.asymmetric hc.1 hreverse


-- @@ L54-58 verbatim
theorem diagonal_admissible {r : V → V → Prop} (hr : IsOriented r) :
    Admissible r (diagonal : Finset (V × V)) diagonal where
  compatible := diagonal_compatible hr
  diagonal_left := fun _ h => h
  diagonal_right := fun _ h => h


-- @@ L60-63 verbatim
theorem column_nonempty_of_diagonal {P : Finset (V × V)}
    (hP : diagonal ⊆ P) (j : V) : (column P j).Nonempty := by
  refine ⟨j, mem_column.mpr ?_⟩
  exact hP (diagonal_mem j)


-- @@ L65-68 verbatim
theorem row_nonempty_of_diagonal {Q : Finset (V × V)}
    (hQ : diagonal ⊆ Q) (i : V) : (row Q i).Nonempty := by
  refine ⟨i, mem_row.mpr ?_⟩
  exact hQ (diagonal_mem i)


-- @@ L70-80 verbatim
theorem column_ne_univ_of_compatible {r : V → V → Prop} {P Q : Finset (V × V)}
    (hc : Compatible r P Q) (hQ : diagonal ⊆ Q)
    (hpos : PositiveIndegree r) (j : V) : column P j ≠ Finset.univ := by
  intro hfull
  obtain ⟨w, hwj⟩ := hpos j
  obtain ⟨p, hpw⟩ := hpos w
  have hp : (p, j) ∈ P := by
    apply mem_column.mp
    rw [hfull]
    exact Finset.mem_univ p
  exact hc (p, j) hp (w, w) (hQ (diagonal_mem w)) ⟨hpw, hwj⟩


-- @@ L82-92 verbatim
theorem row_ne_univ_of_compatible {r : V → V → Prop} {P Q : Finset (V × V)}
    (hc : Compatible r P Q) (hP : diagonal ⊆ P)
    (hpos : PositiveIndegree r) (i : V) : row Q i ≠ Finset.univ := by
  intro hfull
  obtain ⟨w, hwi⟩ := hpos i
  obtain ⟨s, hsw⟩ := hpos w
  have hs : (i, s) ∈ Q := by
    apply mem_row.mp
    rw [hfull]
    exact Finset.mem_univ s
  exact hc (w, w) (hP (diagonal_mem w)) (i, s) hs ⟨hwi, hsw⟩


-- @@ L94-100 verbatim
theorem Admissible.strict_leftImage_growth [Nonempty V]
    {r : V → V → Prop} {P Q : Finset (V × V)} (h : Admissible r P Q)
    (hpos : PositiveIndegree r) (hgrowth : StrictSubsetGrowth r) :
    P.card + (leftImage r (leftImage r P)).card < 2 * (leftImage r P).card :=
  Extremal.strict_leftImage_growth r P hgrowth
    (column_nonempty_of_diagonal h.diagonal_left)
    (column_ne_univ_of_compatible h.compatible h.diagonal_right hpos)


-- @@ L102-108 verbatim
theorem Admissible.strict_rightImage_growth [Nonempty V]
    {r : V → V → Prop} {P Q : Finset (V × V)} (h : Admissible r P Q)
    (hpos : PositiveIndegree r) (hgrowth : StrictSubsetGrowth r) :
    Q.card + (rightImage r (rightImage r Q)).card < 2 * (rightImage r Q).card :=
  Extremal.strict_rightImage_growth r Q hgrowth
    (row_nonempty_of_diagonal h.diagonal_right)
    (row_ne_univ_of_compatible h.compatible h.diagonal_left hpos)


-- @@ L110-122 verbatim
theorem diagonal_subset_leftCandidate {r : V → V → Prop}
    {P Q : Finset (V × V)} (hc : Compatible r P Q) (hP : diagonal ⊆ P) :
    diagonal ⊆ leftCandidate r Q := by
  intro z hz
  rcases z with ⟨v, w⟩
  have heq : v = w := mem_diagonal.mp hz
  subst w
  apply mem_leftCandidate.mpr
  intro hsecond
  obtain ⟨s, hvs, hsv⟩ := mem_rightImage.mp hsecond
  have hleft : (v, s) ∈ leftImage r P :=
    mem_leftImage.mpr ⟨s, hP (diagonal_mem s), hsv⟩
  exact Finset.disjoint_left.mp (conflictFree_iff_disjoint.mp hc) hleft hvs


-- @@ L124-136 verbatim
theorem diagonal_subset_rightCandidate {r : V → V → Prop}
    {P Q : Finset (V × V)} (hc : Compatible r P Q) (hQ : diagonal ⊆ Q) :
    diagonal ⊆ rightCandidate r P := by
  intro z hz
  rcases z with ⟨v, w⟩
  have heq : v = w := mem_diagonal.mp hz
  subst w
  apply mem_rightCandidate.mpr
  intro hsecond
  obtain ⟨p, hpv, hpvArc⟩ := mem_leftImage.mp hsecond
  have hright : (p, v) ∈ rightImage r Q :=
    mem_rightImage.mpr ⟨p, hQ (diagonal_mem p), hpvArc⟩
  exact Finset.disjoint_left.mp (conflictFree_iff_disjoint.mp hc) hpv hright


-- @@ L138-148 verbatim
theorem diagonal_left_conflictFree {r : V → V → Prop} {P : Finset (V × V)}
    (hP : diagonal ⊆ P) {a : V × V} (ha : a ∈ diagonal) :
    ∀ b ∈ rightCandidate r P, ¬ Conflict r a b := by
  rcases a with ⟨v, w⟩
  have heq : v = w := mem_diagonal.mp ha
  subst w
  intro b hb hc
  apply mem_rightCandidate.mp hb
  apply mem_leftImage.mpr
  refine ⟨v, ?_, hc.1⟩
  exact mem_leftImage.mpr ⟨b.2, hP (diagonal_mem b.2), hc.2⟩


-- @@ L150-160 verbatim
theorem diagonal_right_conflictFree {r : V → V → Prop} {Q : Finset (V × V)}
    (hQ : diagonal ⊆ Q) {b : V × V} (hb : b ∈ diagonal) :
    ∀ a ∈ leftCandidate r Q, ¬ Conflict r a b := by
  rcases b with ⟨v, w⟩
  have heq : v = w := mem_diagonal.mp hb
  subst w
  intro a ha hc
  apply mem_leftCandidate.mp ha
  apply mem_rightImage.mpr
  refine ⟨v, ?_, hc.2⟩
  exact mem_rightImage.mpr ⟨a.1, hQ (diagonal_mem a.1), hc.1⟩


-- @@ L162-172 verbatim
theorem H_candidates_subset_uncovered (r : V → V → Prop) (P Q : Finset (V × V)) :
    H r (leftCandidate r Q) (rightCandidate r P) ⊆ uncovered r P Q := by
  intro z hz
  obtain ⟨i, j, hleft, hright, hpi, hsj⟩ := mem_H.mp hz
  apply mem_uncovered.mpr
  intro hcovered
  rcases hcovered with hcovered | hcovered
  · apply mem_rightCandidate.mp hright
    exact mem_leftImage.mpr ⟨z.1, hcovered, hpi⟩
  · apply mem_leftCandidate.mp hleft
    exact mem_rightImage.mpr ⟨z.2, hcovered, hsj⟩


-- @@ L174-176 verbatim
theorem H_candidates_card_le_uncovered (r : V → V → Prop) (P Q : Finset (V × V)) :
    (H r (leftCandidate r Q) (rightCandidate r P)).card ≤ (uncovered r P Q).card :=
  Finset.card_le_card (H_candidates_subset_uncovered r P Q)


-- @@ L178-181 verbatim
theorem uncoveredZ_subset_uncovered (r : V → V → Prop)
    (R C P' Q' : Finset (V × V)) : uncoveredZ r R C P' Q' ⊆ uncovered r P' Q' := by
  intro z hz
  exact mem_uncovered.mpr (mem_uncoveredZ.mp hz).2


-- @@ L183-186 verbatim
theorem uncoveredZ_card_le_uncovered (r : V → V → Prop)
    (R C P' Q' : Finset (V × V)) :
    (uncoveredZ r R C P' Q').card ≤ (uncovered r P' Q').card :=
  Finset.card_le_card (uncoveredZ_subset_uncovered r R C P' Q')


-- @@ L188-202 verbatim
theorem pruning_preserves_diagonal {r : V → V → Prop}
    {P Q P' Q' : Finset (V × V)} (h : Admissible r P Q)
    (hp : PruningResult r (leftCandidate r Q) (rightCandidate r P) P' Q') :
    Admissible r P' Q' where
  compatible := hp.no_conflicts
  diagonal_left := by
    intro a ha
    exact hp.retain_left a
      (diagonal_subset_leftCandidate h.compatible h.diagonal_left ha)
      (diagonal_left_conflictFree h.diagonal_left ha)
  diagonal_right := by
    intro b hb
    exact hp.retain_right b
      (diagonal_subset_rightCandidate h.compatible h.diagonal_right hb)
      (diagonal_right_conflictFree h.diagonal_right hb)


-- @@ L204-204 verbatim
end

-- @@ L205-205 verbatim
end SeymourSecondNeighborhood.Extremal


-- @@ L207-207 verbatim
end OAI
