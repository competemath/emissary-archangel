import Mathlib.Combinatorics.SimpleGraph.Metric


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uX uι uLabel


-- @@ L7-14 verbatim
/-!
# Partition graphs and their extended distances

An edge records equality of one selected label. Distances take values in `ℕ∞`,
so vertices in different connected components have infinite distance. The
pivot comparison and finite-walk characterization control the paths
between vertices with common labels.
-/


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace MetricEntropyDuality.PartitionGraph


-- @@ L20-20 verbatim
variable {X : Type uX} {ι : Type uι} {Label : ι → Type uLabel}

-- @@ L21-21 verbatim
variable (L : (i : ι) → X → Label i) (T : Finset ι)


-- @@ L23-33 verbatim
/-- Distinct vertices are adjacent when a selected label agrees. -/
def graph : SimpleGraph X where
  Adj x y := x ≠ y ∧ ∃ i ∈ T, L i x = L i y
  symm := by
    constructor
    rintro x y ⟨hxy, i, hi, heq⟩
    exact ⟨hxy.symm, i, hi, heq.symm⟩
  loopless := by
    constructor
    intro x hx
    exact hx.1 rfl


-- @@ L35-36 verbatim
@[simp] theorem adj_iff {x y : X} :
    (graph L T).Adj x y ↔ x ≠ y ∧ ∃ i ∈ T, L i x = L i y := Iff.rfl


-- @@ L38-39 verbatim
/-- The genuine extended shortest-path distance, including infinity. -/
def distance (x y : X) : ℕ∞ := (graph L T).edist x y


-- @@ L41-42 verbatim
/-- Membership in a closed graph ball of finite natural radius. -/
def near (k : ℕ) (x y : X) : Prop := distance L T x y ≤ (k : ℕ∞)


-- @@ L44-45 verbatim
@[simp] theorem distance_self (x : X) : distance L T x x = 0 :=
  SimpleGraph.edist_self


-- @@ L47-48 verbatim
@[simp] theorem distance_eq_zero_iff {x y : X} :
    distance L T x y = 0 ↔ x = y := SimpleGraph.edist_eq_zero_iff


-- @@ L50-51 verbatim
theorem distance_comm (x y : X) : distance L T x y = distance L T y x :=
  SimpleGraph.edist_comm


-- @@ L53-55 verbatim
theorem distance_triangle (x y z : X) :
    distance L T x z ≤ distance L T x y + distance L T y z :=
  SimpleGraph.edist_triangle


-- @@ L57-59 verbatim
theorem distance_eq_top_of_not_reachable {x y : X}
    (h : ¬ (graph L T).Reachable x y) : distance L T x y = ⊤ :=
  SimpleGraph.edist_eq_top_of_not_reachable h


-- @@ L61-62 verbatim
@[simp] theorem near_zero_iff {x y : X} : near L T 0 x y ↔ x = y := by
  simp [near]


-- @@ L64-65 verbatim
@[simp] theorem near_self (k : ℕ) (x : X) : near L T k x x := by
  simp [near]


-- @@ L67-71 verbatim
theorem near_symm {k : ℕ} {x y : X} (h : near L T k x y) :
    near L T k y x := by
  change distance L T y x ≤ (k : ℕ∞)
  rw [distance_comm L T y x]
  exact h


-- @@ L73-75 verbatim
theorem near_mono {j k : ℕ} {x y : X} (hjk : j ≤ k)
    (h : near L T j x y) : near L T k x y :=
  h.trans (ENat.natCast_le_natCast.mpr hjk)


-- @@ L77-82 verbatim
theorem near_triangle {j k : ℕ} {x y z : X}
    (hxy : near L T j x y) (hyz : near L T k y z) :
    near L T (j + k) x z := by
  change distance L T x z ≤ ((j + k : ℕ) : ℕ∞)
  simpa only [Nat.cast_add] using
    (distance_triangle L T x y z).trans (add_le_add hxy hyz)


-- @@ L84-91 verbatim
/-- A label match gives distance at most one, including coincident vertices. -/
theorem distance_le_one_of_label_eq {i : ι} {x y : X}
    (hi : i ∈ T) (heq : L i x = L i y) : distance L T x y ≤ 1 := by
  by_cases hxy : x = y
  · subst y
    simp
  · have hadj : (graph L T).Adj x y := ⟨hxy, i, hi, heq⟩
    exact (SimpleGraph.edist_eq_one_iff_adj.mpr hadj).le


-- @@ L93-95 verbatim
theorem near_one_of_label_eq {i : ι} {x y : X}
    (hi : i ∈ T) (heq : L i x = L i y) : near L T 1 x y :=
  distance_le_one_of_label_eq L T hi heq


-- @@ L97-104 verbatim
/-- Every finite distance bound is witnessed by an actual walk. -/
theorem exists_walk_of_le {k : ℕ} {x y : X}
    (h : distance L T x y ≤ (k : ℕ∞)) :
    ∃ p : (graph L T).Walk x y, p.length ≤ k := by
  have htop : (graph L T).edist x y ≠ ⊤ :=
    ne_top_of_le_ne_top (ENat.natCast_ne_top k) h
  obtain ⟨p, hp⟩ := SimpleGraph.exists_walk_of_edist_ne_top htop
  exact ⟨p, ENat.natCast_le_natCast.mp (hp.trans_le h)⟩


-- @@ L106-112 verbatim
theorem distance_le_iff_exists_walk {k : ℕ} {x y : X} :
    distance L T x y ≤ (k : ℕ∞) ↔
      ∃ p : (graph L T).Walk x y, p.length ≤ k := by
  constructor
  · exact exists_walk_of_le L T
  · rintro ⟨p, hp⟩
    exact (SimpleGraph.edist_le p).trans (ENat.natCast_le_natCast.mpr hp)


-- @@ L114-116 verbatim
theorem near_iff_exists_walk {k : ℕ} {x y : X} :
    near L T k x y ↔ ∃ p : (graph L T).Walk x y, p.length ≤ k :=
  distance_le_iff_exists_walk L T


-- @@ L118-125 verbatim
/-- To separate vertices beyond radius `k`, it suffices to rule out short walks. -/
theorem lt_distance_of_forall_walk {k : ℕ} {x y : X}
    (h : ∀ p : (graph L T).Walk x y, k < p.length) :
    (k : ℕ∞) < distance L T x y := by
  apply lt_of_not_ge
  intro hle
  obtain ⟨p, hp⟩ := exists_walk_of_le L T hle
  exact (Nat.not_lt_of_ge hp) (h p)


-- @@ L127-131 verbatim
/-- Replacing a pivot by a vertex with the same selected label costs one step. -/
theorem pivot_replacement {i : ι} {j : ℕ} {v z z' : X}
    (hi : i ∈ T) (heq : L i z' = L i z) (hvz : near L T j v z) :
    near L T (j + 1) v z' :=
  near_triangle L T hvz (near_one_of_label_eq L T hi heq.symm)


-- @@ L133-137 verbatim
theorem pivot_forward {i : ι} {j : ℕ} {v z z' x : X}
    (hi : i ∈ T) (heq : L i z' = L i z) (hvz : near L T j v z)
    (hxv : near L T j x v) : near L T (2 * j + 1) x z' := by
  have h := near_triangle L T hxv (pivot_replacement L T hi heq hvz)
  simpa only [two_mul, add_assoc] using h


-- @@ L139-145 verbatim
theorem pivot_backward {i : ι} {j : ℕ} {v z z' x : X}
    (hi : i ∈ T) (heq : L i z' = L i z) (hvz : near L T j v z)
    (hxz' : near L T (2 * j + 1) x z') : near L T (3 * j + 2) x v := by
  have h := near_triangle L T hxz'
    (near_symm L T (pivot_replacement L T hi heq hvz))
  have hradius : (2 * j + 1) + (j + 1) = 3 * j + 2 := by omega
  rwa [hradius] at h


-- @@ L147-154 verbatim
/-- The replacement and the forward/backward comparisons for one fixed label. -/
theorem pivot_comparison {i : ι} {j : ℕ} {v z z' x : X}
    (hi : i ∈ T) (heq : L i z' = L i z) (hvz : near L T j v z) :
    near L T (j + 1) v z' ∧
      (near L T j x v → near L T (2 * j + 1) x z') ∧
      (near L T (2 * j + 1) x z' → near L T (3 * j + 2) x v) :=
  ⟨pivot_replacement L T hi heq hvz,
    pivot_forward L T hi heq hvz, pivot_backward L T hi heq hvz⟩


-- @@ L156-156 verbatim
end MetricEntropyDuality.PartitionGraph


-- @@ L158-158 verbatim
end


-- @@ L160-160 verbatim
end OAI
