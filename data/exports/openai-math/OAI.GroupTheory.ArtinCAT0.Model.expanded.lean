import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace ArtinCAT0


-- @@ L7-7 verbatim
universe uS uG uX


-- @@ L9-9 verbatim
abbrev Letters := Fin 116

-- @@ L10-10 verbatim
abbrev Label := WithTop ℕ


-- @@ L12-15 verbatim
def blockLetter (b : Fin 3) (i : Fin 39) : Letters :=
  if h₀ : i.val = 0 then ⟨b.val, by omega⟩
  else if h₁ : i.val = 1 then ⟨(b.val + 1) % 3, by omega⟩
  else ⟨5 + 37 * b.val + (i.val - 2), by omega⟩


-- @@ L17-19 verbatim
def Adjacent (s t : Letters) : Prop :=
  ∃ (b : Fin 3) (i j : Fin 39), s = blockLetter b i ∧ t = blockLetter b j ∧
    (i.val + 1 = j.val ∨ j.val + 1 = i.val)


-- @@ L21-23 verbatim
def Distant (s t : Letters) : Prop :=
  ∃ (b : Fin 3) (i j : Fin 39), s = blockLetter b i ∧ t = blockLetter b j ∧
    (i.val + 2 ≤ j.val ∨ j.val + 2 ≤ i.val)


-- @@ L25-27 verbatim
def Sentinel (s t : Letters) : Prop :=
  ((s.val = 3 ∨ s.val = 4) ∧ t.val < 3) ∨
  ((t.val = 3 ∨ t.val = 4) ∧ s.val < 3)


-- @@ L29-32 verbatim
noncomputable def explicitMatrix (s t : Letters) : Label := by
  classical
  exact if s = t then 1 else if Adjacent s t then 3
    else if Distant s t ∨ Sentinel s t then 2 else ⊤


-- @@ L34-37 verbatim
/-- Alternating word of length n, starting with s. -/
def alternating {S : Type uS} (s t : S) : ℕ → FreeGroup S
  | 0 => 1
  | n + 1 => FreeGroup.of s * alternating t s n


-- @@ L39-42 verbatim
/-- Infinity imposes no relation. Diagonal entries impose only trivial relations. -/
def artinRelators {S : Type uS} (M : S → S → Label) : Set (FreeGroup S) :=
  {w | ∃ (s t : S) (n : ℕ), M s t = (n : Label) ∧
    w = alternating s t n * (alternating t s n)⁻¹}


-- @@ L44-44 verbatim
abbrev ArtinGroup {S : Type uS} (M : S → S → Label) := PresentedGroup (artinRelators M)


-- @@ L46-51 verbatim
/-- A geodesic parametrized proportionally to length on the closed unit interval.
Values outside [0,1] are irrelevant. -/
def Segment {X : Type uX} [MetricSpace X] (x y : X) (γ : ℝ → X) : Prop :=
  γ 0 = x ∧ γ 1 = y ∧
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      dist (γ s) (γ t) = |s - t| * dist x y


-- @@ L53-64 verbatim
/-- Geodesic Euclidean triangle comparison. For points of parameters t and u
on the sides xy and xz, the right hand side is the squared Euclidean comparison
distance, expanded by the law of cosines. All geodesic sides, also degenerate
ones, are quantified. Any pair of triangle sides has a common vertex, so this
is the full triangle-comparison convention, not a midpoint-only condition. -/
def CAT0 (X : Type uX) [MetricSpace X] : Prop :=
  (∀ x y : X, ∃ γ : ℝ → X, Segment x y γ) ∧
  ∀ (x y z : X) (γ η : ℝ → X), Segment x y γ → Segment x z η →
    ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      dist (γ t) (η u) ^ 2 ≤
        (t ^ 2 - t * u) * dist x y ^ 2 +
        (u ^ 2 - t * u) * dist x z ^ 2 + t * u * dist y z ^ 2


-- @@ L66-72 verbatim
/-- Proper and cocompact isometric action. Properness of the metric space and
nonemptiness are separate standing hypotheses in the theorem below. -/
def GeometricAction (G : Type uG) (X : Type uX) [Group G] [MetricSpace X] [MulAction G X] : Prop :=
  CAT0 X ∧
  (∀ g : G, Isometry (fun x : X => g • x)) ∧
  (∀ K : Set X, IsCompact K → {g : G | ((fun x : X => g • x) '' K ∩ K).Nonempty}.Finite) ∧
  ∃ K : Set X, IsCompact K ∧ ∀ x : X, ∃ g : G, ∃ k ∈ K, g • k = x


-- @@ L74-74 verbatim
end ArtinCAT0


-- @@ L76-76 verbatim
end OAI
