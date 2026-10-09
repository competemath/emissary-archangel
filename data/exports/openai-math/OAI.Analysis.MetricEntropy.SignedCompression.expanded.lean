import OAI.Analysis.MetricEntropy.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
universe uX uY


-- @@ L9-17 verbatim
/-!
# Signed compression and actual coefficient-ball clusters

A common finite approximation list for nonnegative combinations of mass at
most one gives a difference list for the literal `l1Ball`. A chosen pair of
positive approximants labels each actual coefficient vector; equal labels
give a uniform diameter bound. The list may have centers outside the column
hull, while the fibers consist of actual coefficient vectors.
-/


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
namespace MetricEntropyDuality.SignedCompression


-- @@ L23-23 verbatim
open scoped BigOperators


-- @@ L25-25 verbatim
variable {X : Type uX} {Y : Type uY} [Fintype Y]


-- @@ L27-27 verbatim
def positivePart (lam : RealSpace Y) : RealSpace Y := fun y => max (lam y) 0


-- @@ L29-29 verbatim
def negativePart (lam : RealSpace Y) : RealSpace Y := fun y => max (-lam y) 0


-- @@ L31-33 verbatim
omit [Fintype Y] in
theorem positivePart_nonneg (lam : RealSpace Y) (y : Y) :
    0 ≤ positivePart lam y := le_max_right _ _


-- @@ L35-37 verbatim
omit [Fintype Y] in
theorem negativePart_nonneg (lam : RealSpace Y) (y : Y) :
    0 ≤ negativePart lam y := le_max_right _ _


-- @@ L39-46 verbatim
omit [Fintype Y] in
theorem parts_sub (lam : RealSpace Y) : positivePart lam - negativePart lam = lam := by
  funext y
  change max (lam y) 0 - max (-lam y) 0 = lam y
  by_cases h : 0 ≤ lam y
  · simp [max_eq_left h, max_eq_right (neg_nonpos.mpr h)]
  · have hle : lam y ≤ 0 := le_of_lt (lt_of_not_ge h)
    simp [max_eq_right hle, max_eq_left (neg_nonneg.mpr hle)]


-- @@ L48-55 verbatim
theorem sum_positivePart_le_one (lam : RealSpace Y) (hlam : lam ∈ l1Ball Y) :
    ∑ y, positivePart lam y ≤ 1 := by
  calc
    ∑ y, positivePart lam y ≤ l1Norm lam := by
      apply Finset.sum_le_sum
      intro y _
      exact max_le (le_abs_self (lam y)) (abs_nonneg (lam y))
    _ ≤ 1 := hlam


-- @@ L57-64 verbatim
theorem sum_negativePart_le_one (lam : RealSpace Y) (hlam : lam ∈ l1Ball Y) :
    ∑ y, negativePart lam y ≤ 1 := by
  calc
    ∑ y, negativePart lam y ≤ l1Norm lam := by
      apply Finset.sum_le_sum
      intro y _
      exact max_le (neg_le_abs (lam y)) (abs_nonneg (lam y))
    _ ≤ 1 := hlam


-- @@ L66-76 verbatim
theorem sub_close {ε η : ℝ} {f f' a a' : RealSpace X}
    (hf : UniformClose ε f a) (hf' : UniformClose η f' a') :
    UniformClose (ε + η) (f - f') (a - a') := by
  intro x
  change |(f x - f' x) - (a x - a' x)| ≤ ε + η
  calc
    |(f x - f' x) - (a x - a' x)| = |(f x - a x) - (f' x - a' x)| := by
      congr 1
      ring
    _ ≤ |f x - a x| + |f' x - a' x| := abs_sub _ _
    _ ≤ ε + η := add_le_add (hf x) (hf' x)


-- @@ L78-81 verbatim
/-- The literal difference list, including any duplicated outputs only once. -/
def differenceList (A : Finset (RealSpace X)) : Finset (RealSpace X) := by
  classical
  exact (A.product A).image (fun ab => ab.1 - ab.2)


-- @@ L83-88 verbatim
theorem differenceList_card_le (A : Finset (RealSpace X)) :
    (differenceList A).card ≤ A.card ^ 2 := by
  classical
  calc
    (differenceList A).card ≤ (A.product A).card := Finset.card_image_le
    _ = A.card ^ 2 := by rw [Finset.product_eq_sprod, Finset.card_product, pow_two]


-- @@ L90-91 verbatim
/-- A pair of members of the positive approximation list. -/
abbrev Code (A : Finset (RealSpace X)) := {a // a ∈ A} × {a // a ∈ A}


-- @@ L93-94 verbatim
def decode {A : Finset (RealSpace X)} (c : Code A) : RealSpace X :=
  c.1.val - c.2.val


-- @@ L96-99 verbatim
theorem card_code (A : Finset (RealSpace X)) :
    Fintype.card (Code A) = A.card ^ 2 := by
  classical
  simp [Code, pow_two]


-- @@ L101-105 verbatim
theorem decode_mem_differenceList {A : Finset (RealSpace X)} (c : Code A) :
    decode c ∈ differenceList A := by
  classical
  apply Finset.mem_image.mpr
  exact ⟨(c.1.val, c.2.val), Finset.mem_product.mpr ⟨c.1.property, c.2.property⟩, rfl⟩


-- @@ L107-107 verbatim
variable (g : Y → X → ℝ) (θ : ℝ) (A : Finset (RealSpace X))


-- @@ L109-112 verbatim
/-- The positive compression premise, stated on the actual coefficients. -/
def PositiveApproximation : Prop :=
  ∀ μ : RealSpace Y, (∀ y, 0 ≤ μ y) → (∑ y, μ y) ≤ 1 →
    ∃ a ∈ A, UniformClose (3 * θ) (columnCombination g μ) a


-- @@ L114-126 verbatim
theorem exists_code_approximation (hpos : PositiveApproximation g θ A)
    (lam : RealSpace Y) (hlam : lam ∈ l1Ball Y) :
    ∃ c : Code A, UniformClose (6 * θ) (columnCombination g lam) (decode c) := by
  obtain ⟨a, ha, hapos⟩ := hpos (positivePart lam) (positivePart_nonneg lam)
    (sum_positivePart_le_one lam hlam)
  obtain ⟨b, hb, haneg⟩ := hpos (negativePart lam) (negativePart_nonneg lam)
    (sum_negativePart_le_one lam hlam)
  refine ⟨(⟨a, ha⟩, ⟨b, hb⟩), ?_⟩
  change UniformClose (6 * θ) (columnCombination g lam) (a - b)
  have h := sub_close hapos haneg
  rw [← columnCombination_sub, parts_sub] at h
  have hsum : 3 * θ + 3 * θ = 6 * θ := by ring
  simpa only [hsum] using h


-- @@ L128-133 verbatim
/-- Signed combinations are approximated by the actual finite difference list. -/
theorem uniformApproximation (hpos : PositiveApproximation g θ A) :
    UniformApproximation g (6 * θ) (differenceList A) := by
  intro lam hlam
  obtain ⟨c, hc⟩ := exists_code_approximation g θ A hpos lam hlam
  exact ⟨decode c, decode_mem_differenceList c, hc⟩


-- @@ L135-159 verbatim
/-- Every coefficient vector receives a finite pair code. Its nonempty fibers
form clusters of actual vectors in the coefficient ball, with diameter `12θ`. -/
theorem exists_code (hpos : PositiveApproximation g θ A) :
    ∃ c : l1Ball Y → Code A,
      (∀ lam, UniformClose (6 * θ) (columnCombination g lam.val) (decode (c lam))) ∧
      ∀ lam lam', c lam = c lam' →
        UniformClose (12 * θ) (columnCombination g lam.val) (columnCombination g lam'.val) := by
  classical
  have hex (lam : l1Ball Y) :
      ∃ a : Code A, UniformClose (6 * θ) (columnCombination g lam.val) (decode a) :=
    exists_code_approximation g θ A hpos lam.val lam.property
  let c : l1Ball Y → Code A := fun lam => Classical.choose (hex lam)
  have hc (lam : l1Ball Y) :
      UniformClose (6 * θ) (columnCombination g lam.val) (decode (c lam)) :=
    Classical.choose_spec (hex lam)
  refine ⟨c, hc, ?_⟩
  intro lam lam' heq x
  have hright := (hc lam').symm
  rw [← heq] at hright
  calc
    |columnCombination g lam.val x - columnCombination g lam'.val x| ≤
        |columnCombination g lam.val x - decode (c lam) x| +
          |decode (c lam) x - columnCombination g lam'.val x| := abs_sub_le _ _ _
    _ ≤ 6 * θ + 6 * θ := add_le_add (hc lam x) (hright x)
    _ = 12 * θ := by ring


-- @@ L161-161 verbatim
end MetricEntropyDuality.SignedCompression


-- @@ L163-163 verbatim
end


-- @@ L165-165 verbatim
end OAI
