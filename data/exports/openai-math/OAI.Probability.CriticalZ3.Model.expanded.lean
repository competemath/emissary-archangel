import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open MeasureTheory ProbabilityTheory


-- @@ L7-7 verbatim
namespace CriticalZ3


-- @@ L9-9 verbatim
abbrev Vertex := Fin 3 → ℤ

-- @@ L10-10 verbatim
abbrev Bond := Vertex × Fin 3

-- @@ L11-11 verbatim
abbrev BondConfig := Bond → Bool

-- @@ L12-12 verbatim
abbrev SiteConfig := Vertex → Bool


-- @@ L14-14 verbatim
def step (x : Vertex) (i : Fin 3) : Vertex := fun j => x j + if i = j then 1 else 0


-- @@ L16-17 verbatim
def NearestNeighbor (x y : Vertex) : Prop :=
  ∃ i : Fin 3, y = step x i ∨ x = step y i


-- @@ L19-21 verbatim
def BondOpen (ω : BondConfig) (x y : Vertex) : Prop :=
  (∃ i : Fin 3, y = step x i ∧ ω (x, i) = true) ∨
  (∃ i : Fin 3, x = step y i ∧ ω (y, i) = true)


-- @@ L23-24 verbatim
def SiteOpen (ω : SiteConfig) (x y : Vertex) : Prop :=
  NearestNeighbor x y ∧ ω x = true ∧ ω y = true


-- @@ L26-27 verbatim
def BondConnected (ω : BondConfig) (x y : Vertex) : Prop :=
  Relation.ReflTransGen (BondOpen ω) x y


-- @@ L29-30 verbatim
def SiteConnected (ω : SiteConfig) (x y : Vertex) : Prop :=
  ω x = true ∧ Relation.ReflTransGen (SiteOpen ω) x y


-- @@ L32-33 verbatim
def bondCluster (ω : BondConfig) (x : Vertex) : Set Vertex :=
  {y | BondConnected ω x y}


-- @@ L35-36 verbatim
def siteCluster (ω : SiteConfig) (x : Vertex) : Set Vertex :=
  {y | SiteConnected ω x y}


-- @@ L38-38 verbatim
def bondInfiniteAt (x : Vertex) : Set BondConfig := {ω | (bondCluster ω x).Infinite}

-- @@ L39-39 verbatim
def siteInfiniteAt (x : Vertex) : Set SiteConfig := {ω | (siteCluster ω x).Infinite}


-- @@ L41-42 verbatim
noncomputable def parameter (p : ℝ) : Set.Icc (0 : ℝ) 1 :=
  ⟨max 0 (min 1 p), le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩


-- @@ L44-45 verbatim
noncomputable def bondLaw (p : ℝ) : Measure BondConfig :=
  Measure.infinitePi (fun _ : Bond => bernoulliMeasure true false (parameter p))


-- @@ L47-48 verbatim
noncomputable def siteLaw (p : ℝ) : Measure SiteConfig :=
  Measure.infinitePi (fun _ : Vertex => bernoulliMeasure true false (parameter p))


-- @@ L50-51 verbatim
noncomputable def bondCritical : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < bondLaw p (bondInfiniteAt 0)}


-- @@ L53-54 verbatim
noncomputable def siteCritical : ℝ :=
  sInf {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < siteLaw p (siteInfiniteAt 0)}


-- @@ L56-56 verbatim
end CriticalZ3


-- @@ L58-58 verbatim
end OAI
