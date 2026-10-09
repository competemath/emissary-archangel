import OAI.Combinatorics.GraphThreshold.ProbabilityTreePaths


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
/-! Deterministic removal of initial zero-capacity levels. -/


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
namespace LeanBlast.SecondKahnKalai.ProbabilityTree


-- @@ L11-11 verbatim
variable {X : Type}


-- @@ L13-15 verbatim
/-- Choose one child deterministically from the actual nonempty child law. -/
def firstChild : {d : ℕ} → ProbabilityTree X (d + 1) → ProbabilityTree X d
  | _, @node _ _ _ _ law _ _ child => child (Classical.choice (branch_nonempty law))


-- @@ L17-18 verbatim
def firstLabel : {d : ℕ} → ProbabilityTree X (d + 1) → Finset X
  | _, @node _ _ _ _ law _ label _ => label (Classical.choice (branch_nonempty law))


-- @@ L20-23 verbatim
/-- Prepend the chosen incoming arc to a path of the chosen child. -/
def prependChosen : {d : ℕ} → (T : ProbabilityTree X (d + 1)) →
    (firstChild T).Path → T.Path
  | _, @node _ _ _ _ law _ _ _, p => ⟨Classical.choice (branch_nonempty law), p⟩


-- @@ L25-28 verbatim
/-- Remove `k` initial levels. The additive depth form avoids subtraction casts. -/
def drop : (k : ℕ) → {d : ℕ} → ProbabilityTree X (d + k) → ProbabilityTree X d
  | 0, _, T => T
  | k + 1, _, T => drop k (firstChild T)


-- @@ L30-34 verbatim
/-- Lift a retained path through the fixed choices on the removed prefix. -/
def liftDropPath : (k : ℕ) → {d : ℕ} → (T : ProbabilityTree X (d + k)) →
    (drop k T).Path → T.Path
  | 0, _, _, p => p
  | k + 1, _, T, p => prependChosen T (liftDropPath k (firstChild T) p)


-- @@ L36-37 verbatim
/-- Reindex a tree along equality of depths, without changing its data. -/
def castDepth {d e : ℕ} (h : d = e) (T : ProbabilityTree X d) : ProbabilityTree X e := h ▸ T


-- @@ L39-42 verbatim
def castPath {d e : ℕ} (h : d = e) (T : ProbabilityTree X d) :
    T.Path ≃ (castDepth h T).Path := by
  cases h
  exact Equiv.refl _


-- @@ L44-47 verbatim
/-- Subtraction-indexed convenience wrapper for removing an initial prefix. -/
def dropPrefix {d : ℕ} (T : ProbabilityTree X d) (k : ℕ) (hk : k ≤ d) :
    ProbabilityTree X (d - k) :=
  drop k (castDepth (Nat.sub_add_cancel hk).symm T)


-- @@ L49-52 verbatim
def liftDropPrefixPath {d : ℕ} (T : ProbabilityTree X d) (k : ℕ) (hk : k ≤ d)
    (p : (dropPrefix T k hk).Path) : T.Path :=
  (castPath (Nat.sub_add_cancel hk).symm T).symm
    (liftDropPath k (castDepth (Nat.sub_add_cancel hk).symm T) p)


-- @@ L54-54 verbatim
section Properties


-- @@ L56-56 verbatim
variable [DecidableEq X]


-- @@ L58-62 verbatim
theorem pathUnion_prependChosen {d : ℕ} (T : ProbabilityTree X (d + 1))
    (p : (firstChild T).Path) :
    T.pathUnion (prependChosen T p) = firstLabel T ∪ (firstChild T).pathUnion p := by
  cases T
  rfl


-- @@ L64-68 verbatim
theorem firstChild_support_subset {d : ℕ} (T : ProbabilityTree X (d + 1)) :
    (firstChild T).support ⊆ T.support := by
  cases T with
  | node B law positive label child =>
      exact child_support_subset law positive label child _


-- @@ L70-73 verbatim
theorem firstChild_isDisjoint {d : ℕ} {T : ProbabilityTree X (d + 1)}
    (hT : T.IsDisjoint) : (firstChild T).IsDisjoint := by
  cases T
  exact hT.2 _


-- @@ L75-79 verbatim
omit [DecidableEq X] in
theorem firstChild_hasCapacities {d : ℕ} {T : ProbabilityTree X (d + 1)} {m : ℕ → ℕ}
    (hT : T.HasCapacities m) : (firstChild T).HasCapacities (fun i => m (i + 1)) := by
  cases T
  exact hT.2 _


-- @@ L81-84 verbatim
theorem firstChild_hasSpread {d : ℕ} {T : ProbabilityTree X (d + 1)} {a : ℕ → ℝ}
    (hT : T.HasSpread a) : (firstChild T).HasSpread (fun i => a (i + 1)) := by
  cases T
  exact hT.2 _


-- @@ L86-90 verbatim
omit [DecidableEq X] in
theorem firstLabel_card_le {d : ℕ} {T : ProbabilityTree X (d + 1)} {m : ℕ → ℕ}
    (hT : T.HasCapacities m) : (firstLabel T).card ≤ m 0 := by
  cases T
  exact hT.1 _


-- @@ L92-97 verbatim
omit [DecidableEq X] in
theorem firstLabel_eq_empty {d : ℕ} {T : ProbabilityTree X (d + 1)} {m : ℕ → ℕ}
    (hT : T.HasCapacities m) (hm : m 0 = 0) : firstLabel T = ∅ := by
  apply Finset.card_eq_zero.mp
  have h := firstLabel_card_le hT
  omega


-- @@ L99-102 verbatim
/-- Labels committed by the deterministic choices on the removed prefix. -/
def prefixUnion : (k : ℕ) → {d : ℕ} → ProbabilityTree X (d + k) → Finset X
  | 0, _, _ => ∅
  | k + 1, _, T => firstLabel T ∪ prefixUnion k (firstChild T)


-- @@ L104-112 verbatim
theorem pathUnion_liftDropPath (k : ℕ) {d : ℕ} (T : ProbabilityTree X (d + k))
    (p : (drop k T).Path) :
    T.pathUnion (liftDropPath k T p) = prefixUnion k T ∪ (drop k T).pathUnion p := by
  induction k generalizing d with
  | zero => simp [liftDropPath, prefixUnion, drop]
  | succ k ih =>
      change T.pathUnion (prependChosen T (liftDropPath k T.firstChild p)) =
        (T.firstLabel ∪ prefixUnion k T.firstChild) ∪ (drop k T.firstChild).pathUnion p
      rw [pathUnion_prependChosen, ih T.firstChild p, Finset.union_assoc]


-- @@ L114-118 verbatim
theorem drop_support_subset (k : ℕ) {d : ℕ} (T : ProbabilityTree X (d + k)) :
    (drop k T).support ⊆ T.support := by
  induction k generalizing d with
  | zero => exact Finset.Subset.refl _
  | succ k ih => exact (ih (firstChild T)).trans (firstChild_support_subset T)


-- @@ L120-124 verbatim
theorem drop_isDisjoint (k : ℕ) {d : ℕ} {T : ProbabilityTree X (d + k)}
    (hT : T.IsDisjoint) : (drop k T).IsDisjoint := by
  induction k generalizing d with
  | zero => exact hT
  | succ k ih => exact ih (firstChild_isDisjoint hT)


-- @@ L126-133 verbatim
omit [DecidableEq X] in
theorem drop_hasCapacities (k : ℕ) {d : ℕ} {T : ProbabilityTree X (d + k)}
    {m : ℕ → ℕ} (hT : T.HasCapacities m) :
    (drop k T).HasCapacities (fun i => m (i + k)) := by
  induction k generalizing d m with
  | zero => simpa [drop] using hT
  | succ k ih =>
      simpa [drop, Nat.add_assoc] using ih (firstChild_hasCapacities hT)


-- @@ L135-141 verbatim
theorem drop_hasSpread (k : ℕ) {d : ℕ} {T : ProbabilityTree X (d + k)}
    {a : ℕ → ℝ} (hT : T.HasSpread a) :
    (drop k T).HasSpread (fun i => a (i + k)) := by
  induction k generalizing d a with
  | zero => simpa [drop] using hT
  | succ k ih =>
      simpa [drop, Nat.add_assoc] using ih (firstChild_hasSpread hT)


-- @@ L143-150 verbatim
theorem prefixUnion_eq_empty_of_capacities (k : ℕ) {d : ℕ}
    {T : ProbabilityTree X (d + k)} {m : ℕ → ℕ} (hT : T.HasCapacities m)
    (hm : ∀ i, i < k → m i = 0) : prefixUnion k T = ∅ := by
  induction k generalizing d m with
  | zero => rfl
  | succ k ih =>
      rw [prefixUnion, firstLabel_eq_empty hT (hm 0 (by omega)), Finset.empty_union]
      exact ih (firstChild_hasCapacities hT) (fun i hi => hm (i + 1) (by omega))


-- @@ L152-156 verbatim
/-- Removing zero-capacity levels preserves every retained full path union exactly. -/
theorem pathUnion_liftDropPath_eq (k : ℕ) {d : ℕ} {T : ProbabilityTree X (d + k)}
    {m : ℕ → ℕ} (hT : T.HasCapacities m) (hm : ∀ i, i < k → m i = 0)
    (p : (drop k T).Path) : T.pathUnion (liftDropPath k T p) = (drop k T).pathUnion p := by
  rw [pathUnion_liftDropPath, prefixUnion_eq_empty_of_capacities k hT hm, Finset.empty_union]


-- @@ L158-159 verbatim
@[simp] theorem support_castDepth {d e : ℕ} (h : d = e) (T : ProbabilityTree X d) :
    (castDepth h T).support = T.support := by cases h; rfl


-- @@ L161-162 verbatim
@[simp] theorem isDisjoint_castDepth {d e : ℕ} (h : d = e) (T : ProbabilityTree X d) :
    (castDepth h T).IsDisjoint ↔ T.IsDisjoint := by cases h; rfl


-- @@ L164-166 verbatim
omit [DecidableEq X] in
@[simp] theorem hasCapacities_castDepth {d e : ℕ} (h : d = e) (T : ProbabilityTree X d)
    (m : ℕ → ℕ) : (castDepth h T).HasCapacities m ↔ T.HasCapacities m := by cases h; rfl


-- @@ L168-169 verbatim
@[simp] theorem hasSpread_castDepth {d e : ℕ} (h : d = e) (T : ProbabilityTree X d)
    (a : ℕ → ℝ) : (castDepth h T).HasSpread a ↔ T.HasSpread a := by cases h; rfl


-- @@ L171-173 verbatim
theorem pathUnion_castPath_symm {d e : ℕ} (h : d = e) (T : ProbabilityTree X d)
    (p : (castDepth h T).Path) :
    T.pathUnion ((castPath h T).symm p) = (castDepth h T).pathUnion p := by cases h; rfl


-- @@ L175-178 verbatim
theorem dropPrefix_support_subset {d : ℕ} (T : ProbabilityTree X d) (k : ℕ) (hk : k ≤ d) :
    (dropPrefix T k hk).support ⊆ T.support := by
  simpa only [dropPrefix, support_castDepth] using
    drop_support_subset k (castDepth (Nat.sub_add_cancel hk).symm T)


-- @@ L180-183 verbatim
theorem dropPrefix_isDisjoint {d : ℕ} {T : ProbabilityTree X d} (hT : T.IsDisjoint)
    (k : ℕ) (hk : k ≤ d) : (dropPrefix T k hk).IsDisjoint := by
  apply drop_isDisjoint
  simpa using hT


-- @@ L185-190 verbatim
omit [DecidableEq X] in
theorem dropPrefix_hasCapacities {d : ℕ} {T : ProbabilityTree X d} {m : ℕ → ℕ}
    (hT : T.HasCapacities m) (k : ℕ) (hk : k ≤ d) :
    (dropPrefix T k hk).HasCapacities (fun i => m (i + k)) := by
  apply drop_hasCapacities
  simpa using hT


-- @@ L192-196 verbatim
theorem dropPrefix_hasSpread {d : ℕ} {T : ProbabilityTree X d} {a : ℕ → ℝ}
    (hT : T.HasSpread a) (k : ℕ) (hk : k ≤ d) :
    (dropPrefix T k hk).HasSpread (fun i => a (i + k)) := by
  apply drop_hasSpread
  simpa using hT


-- @@ L198-206 verbatim
/-- Every path after zero-prefix trimming is an original full path with exactly the same union. -/
theorem pathUnion_liftDropPrefixPath_eq {d : ℕ} {T : ProbabilityTree X d} {m : ℕ → ℕ}
    (hT : T.HasCapacities m) (k : ℕ) (hk : k ≤ d)
    (hm : ∀ i, i < k → m i = 0) (p : (dropPrefix T k hk).Path) :
    T.pathUnion (liftDropPrefixPath T k hk p) = (dropPrefix T k hk).pathUnion p := by
  unfold liftDropPrefixPath
  rw [pathUnion_castPath_symm]
  apply pathUnion_liftDropPath_eq k _ hm
  simpa using hT


-- @@ L208-214 verbatim
theorem coveredBy_of_dropPrefix {d : ℕ} {T : ProbabilityTree X d} {m : ℕ → ℕ}
    (hT : T.HasCapacities m) (k : ℕ) (hk : k ≤ d)
    (hm : ∀ i, i < k → m i = 0) {W : Finset X}
    (hW : (dropPrefix T k hk).CoveredBy W) : T.CoveredBy W := by
  obtain ⟨p, hp⟩ := hW
  refine ⟨liftDropPrefixPath T k hk p, ?_⟩
  rwa [pathUnion_liftDropPrefixPath_eq hT k hk hm p]


-- @@ L216-216 verbatim
end Properties


-- @@ L218-218 verbatim
end LeanBlast.SecondKahnKalai.ProbabilityTree


-- @@ L220-220 verbatim
end


-- @@ L222-222 verbatim
end OAI
