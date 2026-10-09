import OAI.Combinatorics.GotsmanLinial.Model


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open scoped BigOperators


-- @@ L7-7 verbatim
namespace LeanBlast.GotsmanLinial


-- @@ L9-11 verbatim
@[simp] theorem flip_apply_same {n : ℕ} (i : Fin n) (x : Cube n) :
    flip i x i = !(x i) := by
  simp [flip]


-- @@ L13-15 verbatim
theorem flip_apply_ne {n : ℕ} (i : Fin n) (x : Cube n) (j : Fin n) (h : j ≠ i) :
    flip i x j = x j := by
  simp [flip, h]


-- @@ L17-23 verbatim
@[simp] theorem flip_flip {n : ℕ} (i : Fin n) (x : Cube n) :
    flip i (flip i x) = x := by
  funext j
  by_cases h : j = i
  · subst j
    simp [flip]
  · simp [flip, h]


-- @@ L25-28 verbatim
theorem flip_ne_self {n : ℕ} (i : Fin n) (x : Cube n) : flip i x ≠ x := by
  intro h
  have hi := congrFun h i
  cases hxi : x i <;> simp [flip, hxi] at hi


-- @@ L30-35 verbatim
theorem flip_injective_direction {n : ℕ} (x : Cube n) :
    Function.Injective (fun i : Fin n => flip i x) := by
  intro i j h
  by_contra hij
  have hi := congrFun h i
  cases hxi : x i <;> simp [flip, hij, hxi] at hi


-- @@ L37-38 verbatim
theorem flip_involutive {n : ℕ} (i : Fin n) : Function.Involutive (flip i) :=
  flip_flip i


-- @@ L40-41 verbatim
theorem flip_bijective {n : ℕ} (i : Fin n) : Function.Bijective (flip i) :=
  (flip_involutive i).bijective


-- @@ L43-45 verbatim
@[simp] theorem cubeCoord_flip_same {n : ℕ} (x : Cube n) (i : Fin n) :
    cubeCoord (flip i x) i = -cubeCoord x i := by
  cases hxi : x i <;> simp [cubeCoord, flip, hxi]


-- @@ L47-49 verbatim
theorem cubeCoord_flip_ne {n : ℕ} (x : Cube n) (i j : Fin n) (h : j ≠ i) :
    cubeCoord (flip i x) j = cubeCoord x j := by
  simp [cubeCoord, flip, h]


-- @@ L51-53 verbatim
theorem cubeCoord_cases {n : ℕ} (x : Cube n) (i : Fin n) :
    cubeCoord x i = 1 ∨ cubeCoord x i = -1 := by
  cases hxi : x i <;> simp [cubeCoord, hxi]


-- @@ L55-57 verbatim
@[simp] theorem cubeCoord_sq {n : ℕ} (x : Cube n) (i : Fin n) :
    (cubeCoord x i) ^ 2 = 1 := by
  cases hxi : x i <;> simp [cubeCoord, hxi]


-- @@ L59-60 verbatim
@[simp] theorem thresholdSign_zero : thresholdSign 0 = 1 := by
  simp [thresholdSign]


-- @@ L62-65 verbatim
theorem thresholdSign_eq_one_iff (t : ℝ) : thresholdSign t = 1 ↔ 0 ≤ t := by
  by_cases h : 0 ≤ t
  · simp [thresholdSign, h]
  · simp [thresholdSign, h, show (-1 : ℝ) ≠ 1 by norm_num]


-- @@ L67-70 verbatim
theorem thresholdSign_eq_neg_one_iff (t : ℝ) : thresholdSign t = -1 ↔ t < 0 := by
  by_cases h : 0 ≤ t
  · simp [thresholdSign, h, not_lt.mpr h, show (1 : ℝ) ≠ -1 by norm_num]
  · simp [thresholdSign, h, lt_of_not_ge h]


-- @@ L72-74 verbatim
theorem thresholdSign_cases (t : ℝ) : thresholdSign t = 1 ∨ thresholdSign t = -1 := by
  unfold thresholdSign
  split <;> simp


-- @@ L76-77 verbatim
@[simp] theorem thresholdSign_sq (t : ℝ) : thresholdSign t ^ 2 = 1 := by
  rcases thresholdSign_cases t with h | h <;> simp [h]


-- @@ L79-80 verbatim
@[simp] theorem card_cube (n : ℕ) : Fintype.card (Cube n) = 2 ^ n := by
  simp [Cube]


-- @@ L82-98 verbatim
/-- The Boolean encoding represents every sign vector exactly once. -/
noncomputable def cubeEquivSignVectors (n : ℕ) :
    Cube n ≃ {x : Fin n → ℝ // ∀ i, x i = 1 ∨ x i = -1} := by
  classical
  exact
    { toFun := fun x => ⟨cubeCoord x, cubeCoord_cases x⟩
      invFun := fun x i => decide (x.1 i = 1)
      left_inv := by
        intro x
        funext i
        cases hxi : x i <;> simp [cubeCoord, hxi, show (-1 : ℝ) ≠ 1 by norm_num]
      right_inv := by
        intro x
        apply Subtype.ext
        funext i
        rcases x.2 i with hxi | hxi <;>
          simp [cubeCoord, hxi, show (-1 : ℝ) ≠ 1 by norm_num] }


-- @@ L100-102 verbatim
theorem averageSensitivity_eq_count {n : ℕ} (f : Cube n → ℝ) :
    averageSensitivity f = (sensitiveEdgeCount f : ℝ) / (2 : ℝ) ^ n := by
  simp [averageSensitivity, sensitiveEdgeCount, Finset.sum_div]


-- @@ L104-107 verbatim
theorem averageSensitivity_eq_uniform {n : ℕ} (f : Cube n → ℝ) :
    averageSensitivity f =
      ∑ i : Fin n, ((sensitiveVertices f i).card : ℝ) / (Fintype.card (Cube n) : ℝ) := by
  simp [averageSensitivity]


-- @@ L109-109 verbatim
end LeanBlast.GotsmanLinial


-- @@ L111-111 verbatim
end OAI
