module

public import Carleson.TileStructure


-- @@ L5-5 verbatim
public section


-- @@ L7-7 verbatim
open Set MeasureTheory Metric Function Complex Bornology

-- @@ L8-8 verbatim
open scoped NNReal ENNReal ComplexConjugate

-- @@ L9-9 verbatim
noncomputable section


-- @@ L11-11 verbatim
open scoped ShortVariables

-- @@ L12-13 verbatim
variable {X : Type*} [PseudoMetricSpace X] {a : ℕ} {q : ℝ} {K : X → X → ℂ}
  {σ₁ σ₂ : X → ℤ} {F G : Set X} [ProofData a q K σ₁ σ₂ F G]

-- @@ L14-15 expanded
variable [TileStructure Q (defaultD a) (defaultκ a) (defaultS X) (cancelPt X)] {u u' p p' : 𝔓 X}
  {f g : Θ X} {C C' : Set (𝔓 X)} {x x' : X}


-- @@ L17-17 verbatim
namespace TileStructure


-- @@ L19-33 expanded
variable (X) in
/-- An `n`-forest -/
structure Forest (n : ℕ) where
  𝔘 : Set (𝔓 X)
  /-- The value of `𝔗 u` only matters when `u ∈ 𝔘`. -/
  𝔗 : 𝔓 X → Set (𝔓 X)
  nonempty' {u : _} (hu : u ∈ 𝔘) : (𝔗 u).Nonempty
  ordConnected' {u : _} (hu : u ∈ 𝔘) :
    OrdConnected
      (𝔗 u) -- (2.0.33)
        
  𝓘_ne_𝓘' {u : _} (hu : u ∈ 𝔘) {p} (hp : p ∈ 𝔗 u) : 𝓘 p ≠ 𝓘 u
  smul_four_le' {u : _} (hu : u ∈ 𝔘) {p} (hp : p ∈ 𝔗 u) : smul 4 p ≤ smul 1 u
  stackSize_le' {x : _} : stackSize 𝔘 x ≤ 2 ^ n
  dens₁_𝔗_le' {u : _} (hu : u ∈ 𝔘) :
    dens₁ (𝔗 u) ≤
      2 ^
        (4 * (a : ℝ) - n + 1) -- (2.0.35)
          
  lt_dist' {u u' : _} (hu : u ∈ 𝔘) (hu' : u' ∈ 𝔘) (huu' : u ≠ u') {p} (hp : p ∈ 𝔗 u')
    (h : 𝓘 p ≤ 𝓘 u) :
    2 ^ (defaultZ a * (n + 1)) <
      (@dist (WithFunctionDistance (𝔠 p) (defaultD a ^ 𝔰 p / 4)) _) (𝒬 p)
        (𝒬 u) -- (2.0.36)
          
  ball_subset' {u : _} (hu : u ∈ 𝔘) {p} (hp : p ∈ 𝔗 u) : ball (𝔠 p) (8 * defaultD a ^ 𝔰 p) ⊆ 𝓘 u


-- @@ L35-35 verbatim
namespace Forest


-- @@ L37-37 verbatim
variable {n : ℕ} (t : Forest X n)


-- @@ L39-39 verbatim
instance : CoeHead (Forest X n) (Set (𝔓 X)) := ⟨Forest.𝔘⟩

-- @@ L40-40 verbatim
instance : Membership (𝔓 X) (Forest X n) := ⟨fun t x ↦ x ∈ (t : Set (𝔓 X))⟩

-- @@ L41-41 verbatim
instance : CoeFun (Forest X n) (fun _ ↦ 𝔓 X → Set (𝔓 X)) := ⟨fun t x ↦ t.𝔗 x⟩


-- @@ L43-44 verbatim
@[simp] lemma mem_mk (n 𝔘 𝔗 a b c d e f g h) (p : 𝔓 X) :
    p ∈ Forest.mk (n := n) 𝔘 𝔗 a b c d e f g h ↔ p ∈ 𝔘 := Iff.rfl


-- @@ L46-46 verbatim
@[simp] lemma mem_𝔘 : u ∈ t.𝔘 ↔ u ∈ t := .rfl

-- @@ L47-47 verbatim
@[simp] lemma mem_𝔗 : p ∈ t.𝔗 u ↔ p ∈ t u := .rfl


-- @@ L49-49 verbatim
lemma nonempty (hu : u ∈ t) : (t u).Nonempty := t.nonempty' hu

-- @@ L50-50 verbatim
lemma ordConnected (hu : u ∈ t) : OrdConnected (t u) := t.ordConnected' hu

-- @@ L51-51 verbatim
lemma 𝓘_ne_𝓘 (hu : u ∈ t) (hp : p ∈ t u) : 𝓘 p ≠ 𝓘 u := t.𝓘_ne_𝓘' hu hp

-- @@ L52-52 verbatim
lemma smul_four_le (hu : u ∈ t) (hp : p ∈ t u) : smul 4 p ≤ smul 1 u := t.smul_four_le' hu hp

-- @@ L53-53 verbatim
lemma stackSize_le : stackSize t x ≤ 2 ^ n := t.stackSize_le'

-- @@ L54-54 verbatim
lemma dens₁_𝔗_le (hu : u ∈ t) : dens₁ (t u) ≤ 2 ^ (4 * (a : ℝ) - n + 1) := t.dens₁_𝔗_le' hu

-- @@ L55-56 expanded
lemma lt_dist (hu : u ∈ t) (hu' : u' ∈ t) (huu' : u ≠ u') {p} (hp : p ∈ t u') (h : 𝓘 p ≤ 𝓘 u) :
    2 ^ (defaultZ a * (n + 1)) <
      (@dist (WithFunctionDistance (𝔠 p) (defaultD a ^ 𝔰 p / 4)) _) (𝒬 p) (𝒬 u) :=
  t.lt_dist' hu hu' huu' hp h


-- @@ L57-60 expanded
lemma ball_subset (hu : u ∈ t) (hp : p ∈ t u) : ball (𝔠 p) (8 * defaultD a ^ 𝔰 p) ⊆ 𝓘 u :=
  t.ball_subset' hu hp


-- @@ L61-65 expanded
variable {t} in
lemma ball_subset_of_mem_𝓘 (hu : u ∈ t) {p : 𝔓 X} (hp : p ∈ t u) {x : X} (hx : x ∈ 𝓘 p) :
    ball x (4 * defaultD a ^ (𝔰 p)) ⊆ 𝓘 u :=
  by
  refine (ball_subset_ball' ?_).trans (t.ball_subset hu hp)
  linarith [show dist x (𝔠 p) < 4 * defaultD a ^ (𝔰 p) from Grid_subset_ball hx]


-- @@ L67-68 verbatim
lemma 𝓘_le_𝓘 (hu : u ∈ t) (hp : p ∈ t u) : 𝓘 p ≤ 𝓘 u :=
  (t.smul_four_le hu hp).1


-- @@ L70-71 expanded
lemma cball_subset_cball (hu : u ∈ t) (hp : p ∈ t u) :
    (@ball (WithFunctionDistance (𝔠 u) (defaultD a ^ 𝔰 u / 4)) _) (𝒬 u) 1 ⊆
      (@ball (WithFunctionDistance (𝔠 p) (defaultD a ^ 𝔰 p / 4)) _) (𝒬 p) 4 :=
  (t.smul_four_le hu hp).2


-- @@ L73-74 expanded
lemma 𝒬_mem_cball (hu : u ∈ t) (hp : p ∈ t u) :
    𝒬 u ∈ (@ball (WithFunctionDistance (𝔠 p) (defaultD a ^ 𝔰 p / 4)) _) (𝒬 p) 4 :=
  (t.cball_subset_cball hu hp) (mem_ball_self zero_lt_one)


-- @@ L76-77 expanded
lemma dist_lt_four (hu : u ∈ t) (hp : p ∈ t u) :
    (@dist (WithFunctionDistance (𝔠 p) (defaultD a ^ 𝔰 p / 4)) _) (𝒬 p) (𝒬 u) < 4 :=
  mem_ball'.mp (t.𝒬_mem_cball hu hp)


-- @@ L79-80 expanded
lemma dist_lt_four' (hu : u ∈ t) (hp : p ∈ t u) :
    (@dist (WithFunctionDistance (𝔠 p) (defaultD a ^ 𝔰 p / 4)) _) (𝒬 u) (𝒬 p) < 4 :=
  mem_ball.mp (t.𝒬_mem_cball hu hp)


-- @@ L82-82 verbatim
end Forest


-- @@ L84-87 verbatim
variable (X) in
/-- An `n`-row -/
structure Row (n : ℕ) extends Forest X n where
  pairwiseDisjoint' : 𝔘.PairwiseDisjoint (fun u ↦ (𝓘 u : Set X))


-- @@ L89-89 verbatim
namespace Row


-- @@ L91-91 verbatim
variable {n : ℕ} (t : Row X n)


-- @@ L93-93 verbatim
instance : CoeHead (Row X n) (Set (𝔓 X)) := ⟨fun t ↦ t.𝔘⟩

-- @@ L94-94 verbatim
instance : Membership (𝔓 X) (Row X n) := ⟨fun t x ↦ x ∈ (t : Set (𝔓 X))⟩

-- @@ L95-95 verbatim
instance : CoeFun (Row X n) (fun _ ↦ 𝔓 X → Set (𝔓 X)) := ⟨fun t x ↦ t.𝔗 x⟩


-- @@ L97-97 verbatim
@[simp] lemma mem_𝔘 : u ∈ t.𝔘 ↔ u ∈ t := .rfl

-- @@ L98-98 verbatim
@[simp] lemma mem_𝔗 : p ∈ t.𝔗 u ↔ p ∈ t u := .rfl


-- @@ L100-101 verbatim
lemma pairwiseDisjoint : Set.PairwiseDisjoint (t : Set (𝔓 X)) (fun u ↦ (𝓘 u : Set X)) :=
  t.pairwiseDisjoint'


-- @@ L103-103 verbatim
end Row

-- @@ L104-104 verbatim
end TileStructure
