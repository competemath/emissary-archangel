/-
Copyright (c) 2026 Alfie Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alfie Davies
-/
module

public import LeanPool.MisereGames.Misere.Ambient
public import LeanPool.MisereGames.Misere.Universe
public import LeanPool.MisereGames.Misere.Hereditary.MaintenanceProviso


-- @@ L12-14 verbatim
/-!
Misere combinatorial games.
-/


-- @@ L16-16 verbatim
namespace MisereGames


-- @@ L18-45 verbatim
/-!
# Comparison modulo a set

We study when comparison of ambient forms modulo `A` is decided by the
*maintenance–proviso test* (`Promain.Test`). A set is `Promain` when the test
entirely characterises comparison. We split this into the two respective
directions, since each can be meaningful on its own:

* `Promain.Necessary`, when comparison implies the test; and
* `Promain.Sufficient`, when the test implies comparison.

Strikingly, sufficiency needs only that `A` is `Form.Hereditary`. Necessity,
however, is the more complicated of the two: it holds when `A` is
`Downlinking`, a property guaranteed for dicotically closed sets containing a
root, and in particular for every `Universe`.

Note that we are providing sufficient conditions for `Promain.Necessary` and
`Promain.Sufficient`; it remains unclear what structure can be inferred about a
set `A` that has either of these two properties.

The main result of this section is `Promain.ofDicoticOfNonempty`, which
states that every nonempty, hereditary, dicotically closed set is promain.

## References

* [A. N. Siegel, *On the general dead-ending universe of partizan games*
(Section 5 on pp. 207–222)][siegel:GeneralDeadendingUniverse:2025]
-/


-- @@ L47-47 verbatim
universe u


-- @@ L49-49 verbatim
variable {G : Type (u + 1)} [Form G]


-- @@ L51-51 verbatim
open Form

-- @@ L52-52 verbatim
open Form.Misere.Outcome

-- @@ L53-53 verbatim
open Form.Misere.Adjoint

-- @@ L54-54 verbatim
open Separation


-- @@ L56-56 verbatim
public section


-- @@ L58-58 verbatim
namespace Form


-- @@ L60-62 verbatim
/-!
### The maintenance–proviso test
-/


-- @@ L64-70 verbatim
/--
The *maintenance–proviso test* for `g` and `h` modulo `A`, simply requiring
both the maintenance and the proviso to be satisfied.
-/
@[expose] def Promain.Test (A : G → Prop) (g h : G) : Prop :=
  Maintenance A g h .right ∧ Maintenance A g h .left ∧
  Proviso A g h .right ∧ Proviso A h g .left


-- @@ L72-78 expanded
/-- A set `A` is *promain* (within the ambient `IsAmbient`) when comparison of
ambient forms modulo `A` is decided entirely by the maintenance–proviso test
(i.e. by `Test`).
-/
@[expose]
def Promain (IsAmbient A : G → Prop) : Prop :=
  ∀ ⦃g h : G⦄, IsAmbient g → IsAmbient h → (MisereGE A g h ↔ Promain.Test A g h)


-- @@ L80-85 expanded
/-- The necessary/'forward' direction of `Promain`, for when comparison forces the
test.
-/
@[expose]
def Promain.Necessary (IsAmbient A : G → Prop) : Prop :=
  ∀ ⦃g h : G⦄, IsAmbient g → IsAmbient h → MisereGE A g h → Promain.Test A g h


-- @@ L87-92 expanded
/-- The sufficient/'backward' direction of `Promain`, for when the test forces
comparison.
-/
@[expose]
def Promain.Sufficient (IsAmbient A : G → Prop) : Prop :=
  ∀ ⦃g h : G⦄, IsAmbient g → IsAmbient h → Promain.Test A g h → MisereGE A g h


-- @@ L94-94 verbatim
variable {IsAmbient A : G → Prop}


-- @@ L96-97 verbatim
theorem Promain.necessary (hp : Promain IsAmbient A) : Promain.Necessary IsAmbient A := by
  intro g h hg hh; exact (hp hg hh).mp


-- @@ L99-100 verbatim
theorem Promain.sufficient (hp : Promain IsAmbient A) : Promain.Sufficient IsAmbient A := by
  intro g h hg hh; exact (hp hg hh).mpr


-- @@ L102-104 verbatim
theorem Promain.mk (hn : Promain.Necessary IsAmbient A) (hs : Promain.Sufficient IsAmbient A) :
    Promain IsAmbient A := by
  intro g h hg hh; exact ⟨hn hg hh, hs hg hh⟩


-- @@ L106-108 verbatim
theorem Promain.iff_necessary_and_sufficient :
    Promain IsAmbient A ↔ Promain.Necessary IsAmbient A ∧ Promain.Sufficient IsAmbient A :=
  ⟨fun hp => ⟨hp.necessary, hp.sufficient⟩, fun ⟨hn, hs⟩ => Promain.mk hn hs⟩


-- @@ L110-112 verbatim
/-!
### Separating and downlinking sets
-/


-- @@ L114-124 expanded
/-- A set `A` is *separating* (within the ambient `IsAmbient`) when incomparable
ambient forms are separated from both sides. This is essentially [Siegel, Lemma
5.8][siegel:GeneralDeadendingUniverse:2025] extracted into a property.
-/
class Separating (IsAmbient : G → Prop) (A : G → Prop) where
  /-- If `g ≱ h` modulo `A`, then `g` and `h` are both Left- and
    Right-separating. -/
  separating_pair_of_not_misereGE {g h : G} :
    IsAmbient g →
      IsAmbient h → ¬(MisereGE A g h) → AreLeftSeparating A g h ∧ AreRightSeparating A g h


-- @@ L126-141 expanded
/-- A set `A` is *downlinking* (within the ambient `IsAmbient`) when we can
conclude two ambient forms are downlinked in the following way: if no Left
option of `g` is better than `h`, and `g` is better than no Right option of
`h`, then `g` is downlinked to `h`. This is essentially an extraction of
[Siegel, Lemma 5.10][siegel:GeneralDeadendingUniverse:2025]

This is currently the crux of proving a set is `Promain.Necessary` (see
`Promain.Necessary.of_downlinking`).
-/
class Downlinking (IsAmbient : G → Prop) (A : G → Prop) extends Hereditary IsAmbient where
  downlinked_of_not_exists_moves_misereGE {g h : G} :
    IsAmbient g →
      IsAmbient h →
        (¬∃ gl ∈ moves .left g, MisereGE A gl h) →
          (¬∃ hr ∈ moves .right h, MisereGE A g hr) → Downlinked A g h


-- @@ L143-147 verbatim
/-!
Currently, the auxiliary separating and downlinking forms used in our proofs
are all grown dicotically from rooted adjoints with a fixed root, so they live
in any dicotically closed `A` containing a root.
-/


-- @@ L149-149 verbatim
section


-- @@ L151-151 verbatim
variable [Ambient IsAmbient] [ClosedUnderDicotic IsAmbient A] {r : G}


-- @@ L153-212 expanded
/-- The rooted adjoint of an ambient form lies in any dicotically closed `A`
containing the root `r`.
-/
theorem rootedAdjoint_mem_of_isAmbient (h_root : A r) (h_sub : A ≤ IsAmbient) {g : G}
    (hg : IsAmbient g) : A (rootedAdjoint r g) :=
  by
  have h_root_mem : ∀ a ∈ ({ r } : Set G), A a := by simp_all
  have h_root_nonempty : ({ r } : Set G).Nonempty := Set.singleton_nonempty r
  have hAdjAmbient := Ambient.isAmbient_rootedAdjoint (h_sub r h_root) hg
  have hAdjRange : ∀ p, ∀ a ∈ Set.range (fun gp : moves p g => rootedAdjoint r (gp : G)), A a :=
    by
    intro p a ha
    simp only [Set.mem_range, Subtype.exists, exists_prop] at ha
    obtain ⟨gp, hgp, rfl⟩ := ha
    exact
      rootedAdjoint_mem_of_isAmbient h_root h_sub
        (Hereditary.has_option hg (IsOption.of_mem_moves hgp))
  have hAdjRange_nonempty :
    ∀ {p}, ¬IsEnd p g → (Set.range fun gp : moves p g => rootedAdjoint r (gp : G)).Nonempty :=
    by
    intro p hp
    obtain ⟨gp, hgp⟩ := not_isEnd_exists_move hp
    exact ⟨rootedAdjoint r gp, ⟨⟨gp, hgp⟩, rfl⟩⟩
  unfold rootedAdjoint
  by_cases hleft : IsEnd .left g
  · by_cases hright : IsEnd .right g
    · rw [ite_eq_left ⟨hleft, hright⟩]
      apply ClosedUnderDicotic.closed_dicotic (IsAmbient := IsAmbient)
      · exact h_root_mem
      · exact h_root_mem
      · exact h_root_nonempty
      · exact h_root_nonempty
      · unfold rootedAdjoint at hAdjAmbient
        simpa [hleft, hright] using hAdjAmbient
    · rw [ite_eq_right (fun h => hright h.2), ite_eq_left hleft]
      apply ClosedUnderDicotic.closed_dicotic (IsAmbient := IsAmbient)
      · exact hAdjRange .right
      · exact h_root_mem
      · exact hAdjRange_nonempty hright
      · exact h_root_nonempty
      · unfold rootedAdjoint at hAdjAmbient
        simpa [hleft, hright] using hAdjAmbient
  · by_cases hright : IsEnd .right g
    · rw [ite_eq_right (fun h => hleft h.1), ite_eq_right hleft, ite_eq_left hright]
      apply ClosedUnderDicotic.closed_dicotic (IsAmbient := IsAmbient)
      · exact h_root_mem
      · exact hAdjRange .left
      · exact h_root_nonempty
      · exact hAdjRange_nonempty hleft
      · unfold rootedAdjoint at hAdjAmbient
        simpa [hleft, hright] using hAdjAmbient
    · rw [ite_eq_right (fun h => hleft h.1), ite_eq_right hleft, ite_eq_right hright]
      apply ClosedUnderDicotic.closed_dicotic (IsAmbient := IsAmbient)
      · exact hAdjRange .right
      · exact hAdjRange .left
      · exact hAdjRange_nonempty hright
      · exact hAdjRange_nonempty hleft
      · unfold rootedAdjoint at hAdjAmbient
        simpa [hleft, hright] using hAdjAmbient
termination_by g
decreasing_by
  all_goals
    all_goals
      solve_by_elim (maxDepth := 8) [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left,
        PSigma.Lex.right, Subposition.of_mem_moves, Subposition.trans, Subtype.prop]


-- @@ L214-222 verbatim
private theorem rightSeparatorLeftSet_mem (h_root : A r) (h_sub : A ≤ IsAmbient)
    {h : G} (hh : IsAmbient h) :
    ∀ b ∈ rightSeparatorLeftSet r h, A b := by
  intro b hb
  simp only [rightSeparatorLeftSet, Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at hb
  rcases hb with rfl | ⟨hr, rfl⟩
  · exact h_root
  · exact rootedAdjoint_mem_of_isAmbient h_root h_sub
      (Hereditary.has_option hh (IsOption.of_mem_moves hr.prop))


-- @@ L224-233 verbatim
private theorem rightSeparatorCandidate_mem (h_root : A r) (h_sub : A ≤ IsAmbient)
    {h x : G} (hh : IsAmbient h) (hx : A x) :
    A (rightSeparatorCandidate r h x) := by
  unfold rightSeparatorCandidate
  apply ClosedUnderDicotic.closed_dicotic (IsAmbient := IsAmbient)
  · exact rightSeparatorLeftSet_mem h_root h_sub hh
  · simp_all
  · exact ⟨r, Or.inl rfl⟩
  · exact Set.singleton_nonempty x
  · exact Ambient.isAmbient_rightSeparatorCandidate (h_sub r h_root) hh (h_sub x hx)


-- @@ L235-243 verbatim
private theorem leftSeparatorRightSet_mem (h_root : A r) (h_sub : A ≤ IsAmbient)
    {g : G} (hg : IsAmbient g) :
    ∀ b ∈ leftSeparatorRightSet r g, A b := by
  intro b hb
  simp only [leftSeparatorRightSet, Set.mem_union, Set.mem_singleton_iff, Set.mem_range] at hb
  rcases hb with rfl | ⟨gl, rfl⟩
  · exact h_root
  · exact rootedAdjoint_mem_of_isAmbient h_root h_sub
      (Hereditary.has_option hg (IsOption.of_mem_moves gl.prop))


-- @@ L245-254 verbatim
private theorem leftSeparatorCandidate_mem (h_root : A r) (h_sub : A ≤ IsAmbient)
    {g x : G} (hg : IsAmbient g) (hx : A x) :
    A (leftSeparatorCandidate r g x) := by
  unfold leftSeparatorCandidate
  apply ClosedUnderDicotic.closed_dicotic (IsAmbient := IsAmbient)
  · simp_all
  · exact leftSeparatorRightSet_mem h_root h_sub hg
  · exact Set.singleton_nonempty x
  · exact ⟨r, Or.inl rfl⟩
  · exact Ambient.isAmbient_leftSeparatorCandidate (h_sub r h_root) hg (h_sub x hx)


-- @@ L256-267 verbatim
private theorem downlinkOptions_mem (h_root : A r) (h_sub : A ≤ IsAmbient)
    {p : Player} {g h : G} {z : moves (-p) h → G}
    (hg : IsAmbient g) (hzA : ∀ hp, A (z hp)) :
    ∀ a ∈ downlinkOptions r p g h z, A a := by
  intro a ha
  simp only [downlinkOptions, downlinkZero, Set.mem_union, Set.mem_range, Subtype.exists,
    exists_prop, Set.mem_ite_empty_right, Set.mem_singleton_iff] at ha
  rcases ha with (⟨hp, hhp, rfl⟩ | ⟨gp, hgp, rfl⟩) | ha0
  · exact hzA ⟨hp, hhp⟩
  · exact rootedAdjoint_mem_of_isAmbient h_root h_sub
      (Hereditary.has_option hg (IsOption.of_mem_moves hgp))
  · simp_all


-- @@ L269-287 expanded
private theorem downlinkWitness_mem (h_root : A r) (h_sub : A ≤ IsAmbient) {g h : G}
    {x : moves .left g → G} {y : moves .right h → G} [Small (downlinkLeftSet r g h y)]
    [Small (downlinkRightSet r g h x)] (hg : IsAmbient g) (hh : IsAmbient h) (hxA : ∀ gl, A (x gl))
    (hyA : ∀ hr, A (y hr)) : A (downlinkWitness r g h x y) :=
  by
  let L : Set G := downlinkLeftSet r g h y
  let R : Set G := downlinkRightSet r g h x
  change
    A
      (OfSets.ofSets (Player.cases L R)
        (by
          first
          | done
          | trivial
          | assumption
          | aesop
          |
            fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
              where `h` is a proof that sets are valid"))
  apply ClosedUnderDicotic.closed_dicotic (IsAmbient := IsAmbient)
  · exact downlinkOptions_mem h_root h_sub (p := .left) hg hyA
  · exact downlinkOptions_mem h_root h_sub (p := .right) hh hxA
  · exact downlinkOptions_nonempty r .left g h y
  · exact downlinkOptions_nonempty r .right h g x
  ·
    exact
      Ambient.isAmbient_downlinkWitness (h_sub r h_root) hg hh (fun gl => h_sub _ (hxA gl))
        (fun hr => h_sub _ (hyA hr))


-- @@ L289-313 verbatim
/--
If every Left option of `g` is separated from `h`, and every Right option of
`h` from `g`, then `g` is downlinked to `h`.
-/
theorem Downlinked.of_separating (h_root : A r) (h_isRoot : IsRoot IsAmbient r)
    (h_sub : A ≤ IsAmbient)
    {g h : G} (hg : IsAmbient g) (hh : IsAmbient h)
    (h_left_sep : ∀ gl : moves .left g, AreLeftSeparating A (gl : G) h)
    (h_right_sep : ∀ hr : moves .right h, AreRightSeparating A g (hr : G)) :
    Downlinked A g h := by
  classical
  choose x hxA hxLose hxWin using h_left_sep
  choose y hyA hyWin hyLose using h_right_sep
  have : Small.{u} (downlinkZero r .left g h) := by
    by_cases hz : IsEnd .right g ∧ IsEnd .right h
    · simpa [downlinkZero, hz] using (inferInstance : Small.{u} ({r} : Set G))
    · simpa [downlinkZero, hz] using (inferInstance : Small.{u} (∅ : Set G))
  have : Small.{u} (downlinkZero r .right h g) := by
    by_cases hz : IsEnd .left h ∧ IsEnd .left g
    · simpa [downlinkZero, hz] using (inferInstance : Small.{u} ({r} : Set G))
    · simpa [downlinkZero, hz] using (inferInstance : Small.{u} (∅ : Set G))
  have : Small.{u} (downlinkLeftSet r g h y) := inferInstance
  have : Small.{u} (downlinkRightSet r g h x) := inferInstance
  exact downlinked_of_downlinkWitness_mem h_isRoot hg hh
    (downlinkWitness_mem h_root h_sub hg hh hxA hyA) hxLose hxWin hyWin hyLose


-- @@ L315-332 expanded
/-- If `g ≱ h` modulo `A`, then `g` and `h` are both Left- and Right-separating.
-/
theorem Separating.pair_of_not_misereGE (h_root : A r) (h_isRoot : IsRoot IsAmbient r)
    (h_sub : A ≤ IsAmbient) {g h : G} (hg : IsAmbient g) (hh : IsAmbient h)
    (h_not_ge : ¬(MisereGE A g h)) : AreLeftSeparating A g h ∧ AreRightSeparating A g h := by
  cases not_misereGE_iff_separating.mp h_not_ge with
  | inl h_left =>
    refine ⟨h_left, ?_⟩
    refine rightSeparating_of_leftSeparating_of_rightSeparatorCandidate_mem h_isRoot hh ?_ h_left
    intro x hx
    exact rightSeparatorCandidate_mem h_root h_sub hh hx
  | inr h_right =>
    refine ⟨?_, h_right⟩
    refine leftSeparating_of_rightSeparating_of_leftSeparatorCandidate_mem h_isRoot hg ?_ h_right
    intro x hx
    exact leftSeparatorCandidate_mem h_root h_sub hg hx


-- @@ L334-343 verbatim
/--
A dicotically closed `A` lying in the ambient space and containing a *root* `r`
(see `Form.Misere.Adjoint.IsRoot`) is `Separating` (no further closure
properties required!).
-/
theorem Separating.ofDicotic (h_root : A r) (h_isRoot : IsRoot IsAmbient r)
    (h_sub : A ≤ IsAmbient) :
    Separating IsAmbient A where
  separating_pair_of_not_misereGE hg hh h_not_ge :=
    Separating.pair_of_not_misereGE h_root h_isRoot h_sub hg hh h_not_ge


-- @@ L345-354 verbatim
/--
A nonempty, hereditary, dicotically closed `A` lying in the ambient space is
`Separating`. Note that this is strictly weaker than `ofDicotic`; it is
mainly included for convenience.
-/
theorem Separating.ofDicoticOfNonempty [Hereditary A] (h_ne : ∃ g, A g)
    (h_sub : A ≤ IsAmbient) :
    Separating IsAmbient A :=
  let ⟨_, hr, hr_zero⟩ := exists_isZeroLike h_ne
  .ofDicotic hr (isRoot_of_isZeroLike IsAmbient hr_zero) h_sub


-- @@ L356-372 expanded
private theorem downlinked_of_not_exists_moves_of_separating [Separating IsAmbient A] (h_root : A r)
    (h_isRoot : IsRoot IsAmbient r) (h_sub : A ≤ IsAmbient) {g h : G} (hg : IsAmbient g)
    (hh : IsAmbient h) (h_left : ¬∃ gl ∈ moves .left g, MisereGE A gl h)
    (h_right : ¬∃ hr ∈ moves .right h, MisereGE A g hr) : Downlinked A g h :=
  by
  have h_left_sep : ∀ gl : moves .left g, AreLeftSeparating A (gl : G) h :=
    by
    intro gl
    have h_not_ge : ¬(MisereGE A (gl : G) h) := fun hge => h_left ⟨gl, gl.prop, hge⟩
    exact
      (Separating.separating_pair_of_not_misereGE
          (Hereditary.has_option hg (IsOption.of_mem_moves gl.prop)) hh h_not_ge).left
  have h_right_sep : ∀ hr : moves .right h, AreRightSeparating A g (hr : G) :=
    by
    intro hr
    have h_not_ge : ¬(MisereGE A g (hr : G)) := fun hge => h_right ⟨hr, hr.prop, hge⟩
    exact
      (Separating.separating_pair_of_not_misereGE hg
          (Hereditary.has_option hh (IsOption.of_mem_moves hr.prop)) h_not_ge).right
  exact Downlinked.of_separating h_root h_isRoot h_sub hg hh h_left_sep h_right_sep


-- @@ L374-382 verbatim
/--
A separating, dicotically closed `A` in the ambient space with a root is
downlinking (`Separating` supplies what the downlink construction needs).
-/
theorem Downlinking.ofDicoticSeparating [Separating IsAmbient A]
    (h_root : A r) (h_isRoot : IsRoot IsAmbient r) (h_sub : A ≤ IsAmbient) :
    Downlinking IsAmbient A where
  downlinked_of_not_exists_moves_misereGE hg hh h_left h_right :=
    downlinked_of_not_exists_moves_of_separating h_root h_isRoot h_sub hg hh h_left h_right


-- @@ L384-394 verbatim
/--
A dicotically closed `A` lying in the ambient space and containing a *root* `r`
(see `Form.Misere.Adjoint.IsRoot`) is `Downlinking` (no further closure
properties required!). Taking `r = 0` recovers the usual case where `A`
contains `0`.
-/
theorem Downlinking.ofDicotic
    (h_root : A r) (h_isRoot : IsRoot IsAmbient r) (h_sub : A ≤ IsAmbient) :
    Downlinking IsAmbient A :=
  letI := Separating.ofDicotic h_root h_isRoot h_sub
  Downlinking.ofDicoticSeparating h_root h_isRoot h_sub


-- @@ L396-405 verbatim
/--
A nonempty, hereditary, dicotically closed `A` lying in the ambient space is
`Downlinking`. The zero-like form it must contain (`Form.exists_isZeroLike`)
serves as the required root.
-/
theorem Downlinking.ofDicoticOfNonempty [Hereditary A] (h_ne : ∃ g, A g)
    (h_sub : A ≤ IsAmbient) :
    Downlinking IsAmbient A :=
  let ⟨_, hr, hr_zero⟩ := exists_isZeroLike h_ne
  Downlinking.ofDicotic hr (isRoot_of_isZeroLike IsAmbient hr_zero) h_sub


-- @@ L407-407 verbatim
end


-- @@ L409-409 verbatim
/-! ### Necessity -/


-- @@ L411-411 verbatim
section


-- @@ L413-413 verbatim
variable [Downlinking IsAmbient A]


-- @@ L415-420 expanded
private lemma not_misereGE_of_right_left_outcomes {g h t : G} (hge : MisereGE A g h) (ht : A t)
    (p : Player) (hgt : MiserePlayerOutcome (g + t) p = .right)
    (hht : MiserePlayerOutcome (h + t) p = .left) : False :=
  by
  have h_cmp := misereOutcome_ge_iff_miserePlayerOutcome_ge.mp (hge t ht) p
  simp_all


-- @@ L422-438 expanded
/-- Comparison forbids downlinking to options: if `g ≥m A h`, then `g` is not
downlinked to any Left option of `h`.
-/
theorem not_downlinked_left_option_of_misereGE {g h hl : G} (hge : MisereGE A g h)
    (hhl : hl ∈ moves .left h) : ¬Downlinked A g hl :=
  by
  rintro ⟨t, ht, hgt, hhlt⟩
  have hgt_out : MiserePlayerOutcome (g + t) .left = .right :=
    by
    unfold MiserePlayerOutcome
    simp [hgt]
  have hhlt_out : MiserePlayerOutcome (hl + t) .right = .left :=
    by
    unfold MiserePlayerOutcome
    simp [hhlt]
  have hht : MiserePlayerOutcome (h + t) .left = .left :=
    miserePlayerOutcome_of_leftMoves (add_right_mem_moves_add hhl t) hhlt_out
  exact not_misereGE_of_right_left_outcomes hge ht .left hgt_out hht


-- @@ L440-456 expanded
/-- Comparison forbids downlinking to options: if `g ≥m A h`, then no Right option
of `g` is downlinked to `h`.
-/
theorem not_downlinked_right_option_of_misereGE {g h gr : G} (hge : MisereGE A g h)
    (hgr : gr ∈ moves .right g) : ¬Downlinked A gr h :=
  by
  rintro ⟨t, ht, hgrt, hht⟩
  have hgrt_out : MiserePlayerOutcome (gr + t) .left = .right :=
    by
    unfold MiserePlayerOutcome
    simp [hgrt]
  have hgt : MiserePlayerOutcome (g + t) .right = .right :=
    miserePlayerOutcome_of_rightMoves (add_right_mem_moves_add hgr t) hgrt_out
  have hht_out : MiserePlayerOutcome (h + t) .right = .left :=
    by
    unfold MiserePlayerOutcome
    simp [hht]
  exact not_misereGE_of_right_left_outcomes hge ht .right hgt hht_out


-- @@ L458-478 expanded
private lemma maintenance_of_misereGE_downlinking {g h : G} (p : Player) (hg : IsAmbient g)
    (hh : IsAmbient h) (hge : MisereGE A g h) : Maintenance A g h p :=
  by
  cases p
  · intro hl hhl
    by_contra h_not
    have h_downlinked : Downlinked A g hl :=
      by
      apply
        Downlinking.downlinked_of_not_exists_moves_misereGE hg
          (Hereditary.has_option hh (IsOption.of_mem_moves hhl))
      · simp_all
      · simp_all
    exact not_downlinked_left_option_of_misereGE hge hhl h_downlinked
  · intro gr hgr
    by_contra h_not
    have h_downlinked : Downlinked A gr h :=
      by
      apply
        Downlinking.downlinked_of_not_exists_moves_misereGE
          (Hereditary.has_option hg (IsOption.of_mem_moves hgr)) hh
      · simp_all
      · simp_all
    exact not_downlinked_right_option_of_misereGE hge hgr h_downlinked


-- @@ L480-489 verbatim
/--
If `A` is downlinking, then comparison forces the maintenance–proviso test;
i.e. `Test` is *necessary* for comparison.
-/
theorem Promain.Necessary.of_downlinking : Promain.Necessary IsAmbient A := by
  intro g h hg hh hge
  exact ⟨maintenance_of_misereGE_downlinking .right hg hh hge,
    maintenance_of_misereGE_downlinking .left hg hh hge,
    proviso_right_of_misereGE hge,
    proviso_left_of_misereGE hge⟩


-- @@ L491-491 verbatim
end


-- @@ L493-493 verbatim
section


-- @@ L495-495 verbatim
variable [Ambient IsAmbient] [ClosedUnderDicotic IsAmbient A]


-- @@ L497-505 verbatim
/--
A concrete sufficient condition for necessity: a dicotically closed set in the
ambient space containing a root.
-/
theorem Promain.Necessary.ofDicotic {r : G}
    (h_root : A r) (h_isRoot : IsRoot IsAmbient r) (h_sub : A ≤ IsAmbient) :
    Promain.Necessary IsAmbient A :=
  letI := Downlinking.ofDicotic h_root h_isRoot h_sub
  Promain.Necessary.of_downlinking


-- @@ L507-515 verbatim
/--
A nonempty, hereditary, dicotically closed set in the ambient space has the
necessity direction.
-/
theorem Promain.Necessary.ofDicoticOfNonempty [Hereditary A]
    (h_ne : ∃ g, A g) (h_sub : A ≤ IsAmbient) :
    Promain.Necessary IsAmbient A :=
  letI := Downlinking.ofDicoticOfNonempty h_ne h_sub
  Promain.Necessary.of_downlinking


-- @@ L517-517 verbatim
end


-- @@ L519-521 verbatim
/-!
### Sufficiency
-/


-- @@ L523-529 verbatim
/--
If `A` is hereditary, then the maintenance–proviso test (`Test`) is sufficient
for comparison.
-/
theorem Promain.Sufficient.of_hereditary [Hereditary A] : Promain.Sufficient IsAmbient A := by
  intro g h _ _ ⟨h2, h3, h4, h5⟩
  exact Hereditary.misereGE_of_maintenance_proviso A h2 h3 h4 h5


-- @@ L531-533 verbatim
/-!
### Comparison
-/


-- @@ L535-541 verbatim
/--
If `A` is downlinking and hereditary, comparison modulo `A` is characterised by
the maintenance–proviso test.
-/
theorem Promain.of_downlinking_of_hereditary [Downlinking IsAmbient A] [Hereditary A] :
    Promain IsAmbient A :=
  Promain.mk Promain.Necessary.of_downlinking Promain.Sufficient.of_hereditary


-- @@ L543-550 verbatim
/--
A nonempty, hereditary, dicotically closed set in the ambient space is promain.
-/
theorem Promain.ofDicoticOfNonempty [Ambient IsAmbient] [ClosedUnderDicotic IsAmbient A]
    [Hereditary A] (h_ne : ∃ g, A g) (h_sub : A ≤ IsAmbient) :
    Promain IsAmbient A :=
  letI := Downlinking.ofDicoticOfNonempty h_ne h_sub
  Promain.of_downlinking_of_hereditary


-- @@ L552-558 verbatim
/--
Every universe is separating.
-/
instance instSeparatingUniverse [Ambient IsAmbient] [Universe IsAmbient A] :
    Separating IsAmbient A :=
  .ofDicoticOfNonempty ⟨0, Universe.zero_mem IsAmbient⟩
    (fun _ ha => Universe.isAmbient_of_mem ha)


-- @@ L560-566 verbatim
/--
Every universe is downlinking.
-/
instance instDownlinkingUniverse [Ambient IsAmbient] [Universe IsAmbient A] :
    Downlinking IsAmbient A :=
  .ofDicoticOfNonempty ⟨0, Universe.zero_mem IsAmbient⟩
    (fun _ ha => Universe.isAmbient_of_mem ha)


-- @@ L568-574 verbatim
/--
Comparison modulo a universe is characterised by the maintenance–proviso test
(`Test`).
-/
theorem Promain.of_universe [Ambient IsAmbient] [Universe IsAmbient A] :
    Promain IsAmbient A :=
  Promain.of_downlinking_of_hereditary


-- @@ L576-578 verbatim
/-!
### Maintenance under refinement
-/


-- @@ L580-580 verbatim
namespace Maintenance


-- @@ L582-592 expanded
/-- If `B` is a subset of `A`, then any pair of games passing the `A`-maintenance
necessarily also passes the `B`-maintenance.
-/
theorem of_subset {A B : G → Prop} (h_subset : ∀ g, B g → A g) {g h : G} {p : Player}
    (h_maintenance : Maintenance A g h p) : Maintenance B g h p :=
  by
  have h_ge {x y : G} (hxy : MisereGE A x y) : MisereGE B x y :=
    misereGE_of_subset A h_subset x y hxy
  cases p <;>
    exact fun y hy =>
      (h_maintenance y hy).imp (Exists.imp fun _ => And.imp_right h_ge)
        (Exists.imp fun _ => And.imp_right h_ge)


-- @@ L594-594 verbatim
end Maintenance


-- @@ L596-596 verbatim
end Form


-- @@ L598-598 verbatim
end


-- @@ L600-600 verbatim
end MisereGames
