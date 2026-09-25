module

public import Carleson.TileStructure
public import Carleson.ToMathlib.MinLayer


-- @@ L6-6 verbatim
public section


-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
open Set

-- @@ L11-11 verbatim
open scoped ShortVariables

-- @@ L12-13 verbatim
variable {X : Type*} [PseudoMetricSpace X] {a : ℕ} {q : ℝ} {K : X → X → ℂ}
  {σ₁ σ₂ : X → ℤ} {F G : Set X} [ProofData a q K σ₁ σ₂ F G] [TileStructure Q D κ S o]

-- @@ L14-14 verbatim
variable {A : Set (𝔓 X)} {p : 𝔓 X} {n : ℕ}


-- @@ L16-26 verbatim
lemma exists_scale_add_le_of_mem_minLayer (hp : p ∈ A.minLayer n) :
    ∃ p' ∈ A.minLayer 0, p' ≤ p ∧ 𝔰 p' + n ≤ 𝔰 p := by
  induction n generalizing p with
  | zero => use p, hp, le_rfl, by lia
  | succ n ih =>
    obtain ⟨p', mp', lp'⟩ := exists_le_in_minLayer_of_le hp (show n ≤ n + 1 by lia)
    obtain ⟨q, mq, lq, _⟩ := ih mp'; use q, mq, lq.trans lp'; suffices 𝔰 p' < 𝔰 p by lia
    have l : 𝓘 p' < 𝓘 p := by
      apply 𝓘_strictMono
      exact lt_of_le_of_ne lp' <| (disjoint_minLayer_of_ne (by lia)).ne_of_mem mp' hp
    rw [Grid.lt_def] at l; exact l.2


-- @@ L28-38 verbatim
lemma exists_le_add_scale_of_mem_maxLayer (hp : p ∈ A.maxLayer n) :
    ∃ p' ∈ A.maxLayer 0, p ≤ p' ∧ 𝔰 p + n ≤ 𝔰 p' := by
  induction n generalizing p with
  | zero => use p, hp, le_rfl, by lia
  | succ n ih =>
    obtain ⟨p', mp', lp'⟩ := exists_le_in_maxLayer_of_le hp (show n ≤ n + 1 by lia)
    obtain ⟨q, mq, lq, _⟩ := ih mp'; use q, mq, lp'.trans lq; suffices 𝔰 p < 𝔰 p' by lia
    have l : 𝓘 p < 𝓘 p' := by
      apply 𝓘_strictMono
      exact lt_of_le_of_ne lp' <| (disjoint_maxLayer_of_ne (by lia)).ne_of_mem hp mp'
    rw [Grid.lt_def] at l; exact l.2


-- @@ L40-44 verbatim
lemma exists_scale_add_le_of_mem_layersAbove (hp : p ∈ A.layersAbove n) :
    ∃ p' ∈ A.minLayer 0, p' ≤ p ∧ 𝔰 p' + n ≤ 𝔰 p := by
  obtain ⟨p', mp', lp'⟩ := exists_le_in_layersAbove_of_le hp le_rfl
  obtain ⟨q, mq, lq, sq⟩ := exists_scale_add_le_of_mem_minLayer mp'
  use q, mq, lq.trans lp', sq.trans lp'.1.2


-- @@ L46-50 verbatim
lemma exists_le_add_scale_of_mem_layersBelow (hp : p ∈ A.layersBelow n) :
    ∃ p' ∈ A.maxLayer 0, p ≤ p' ∧ 𝔰 p + n ≤ 𝔰 p' := by
  obtain ⟨p', mp', lp'⟩ := exists_le_in_layersBelow_of_le hp le_rfl
  obtain ⟨q, mq, lq, sq⟩ := exists_le_add_scale_of_mem_maxLayer mp'
  use q, mq, lp'.trans lq, (add_le_add_left lp'.1.2 _).trans sq


-- @@ L52-52 verbatim
end
