import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open Filter

-- @@ L7-7 verbatim
open scoped Topology


-- @@ L9-9 verbatim
namespace WeakPinned

-- @@ L10-10 verbatim
abbrev Plane := EuclideanSpace ℝ (Fin 2)


-- @@ L12-13 verbatim
def distanceFiber (P : Finset Plane) (x y : Plane) : Finset Plane :=
  (P.erase x).filter (fun z => dist z x = dist y x)


-- @@ L15-16 verbatim
def k (P : Finset Plane) (x y : Plane) : ℕ :=
  (distanceFiber P x y).card


-- @@ L18-20 verbatim
def richPairs (P : Finset Plane) (s : ℝ) : Finset (Plane × Plane) :=
  (P ×ˢ P).filter (fun xy => xy.1 ≠ xy.2 ∧
    (P.card : ℝ) ^ s ≤ (k P xy.1 xy.2 : ℝ))


-- @@ L22-23 verbatim
def pairFraction (P : Finset Plane) (s : ℝ) : ℝ :=
  (richPairs P s).card / ((P.card : ℝ) * ((P.card : ℝ) - 1))


-- @@ L25-27 verbatim
def F (n : ℕ) (s : ℝ) : ℝ :=
  if 2 ≤ n then sSup {a : ℝ | ∃ P : Finset Plane, P.card = n ∧ a = pairFraction P s}
  else 0


-- @@ L29-30 verbatim
def distances (P : Finset Plane) (x : Plane) : Finset ℝ :=
  (P.erase x).image (fun y => dist y x)


-- @@ L32-33 verbatim
def badPins (P : Finset Plane) (ε : ℝ) : Finset Plane :=
  P.filter (fun x => ((distances P x).card : ℝ) < (P.card : ℝ) ^ (1 - ε))


-- @@ L35-36 verbatim
def badPinFraction (P : Finset Plane) (ε : ℝ) : ℝ :=
  (badPins P ε).card / (P.card : ℝ)


-- @@ L38-42 verbatim
def B (n : ℕ) (ε : ℝ) : ℝ :=
  if 0 < n then sSup {a : ℝ | ∃ P : Finset Plane, P.card = n ∧ a = badPinFraction P ε}
  else 0

/- Uniform multiplicity and pinned-distance convergence statements. -/

-- @@ L43-44 verbatim
def MainStatement : Prop :=
  ∀ s : ℝ, 0 < s → Tendsto (fun n : ℕ => F n s) atTop (nhds 0)


-- @@ L46-47 verbatim
def PinsStatement : Prop :=
  ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => B n ε) atTop (nhds 0)


-- @@ L49-49 verbatim
end WeakPinned


-- @@ L51-51 verbatim
end


-- @@ L53-53 verbatim
end OAI
