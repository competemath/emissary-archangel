import CharacteristicSet.CharacteristicSet
import CharacteristicSet.WeakAscendingSet


-- @@ L4-4 verbatim
open MvPolynomial WeakAscendingSet


-- @@ L6-6 verbatim
scoped[MvPolynomial] notation:9000 R "[" σ "]" => MvPolynomial σ R


-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
namespace em1


-- @@ L12-12 expanded
def p₁ : ℚ[Fin 2] :=
  X 0 + X 1


-- @@ L13-13 expanded
def p₂ : ℚ[Fin 2] :=
  X 0 * X 1 - 1


-- @@ L15-15 expanded
def l : List ℚ[Fin 2] :=
  [p₁, p₂]


-- @@ L17-17 verbatim
lemma hc₁ : p₁.vars.max = 1 := sorry

-- @@ L18-18 verbatim
example : p₁.mainDegree = 1 := sorry

-- @@ L19-19 verbatim
example : p₂.vars.max = 1 := sorry

-- @@ L20-20 verbatim
example : p₂.mainDegree = 1 := sorry


-- @@ L22-23 verbatim
def AS₁ : AscendingSet (Fin 2) ℚ :=
  ⟨TriangularSet.single p₁, TriangularSet.isAscendingSet_single p₁⟩

-- @@ L24-25 verbatim
def AS₂ : AscendingSet (Fin 2) ℚ :=
  ⟨TriangularSet.single p₂, TriangularSet.isAscendingSet_single p₂⟩


-- @@ L27-27 expanded
def p₃ : ℚ[Fin 2] :=
  X 0 ^ 2 + 1


-- @@ L28-28 verbatim
lemma hc₃ : p₃.vars.max = 0 := sorry

-- @@ L29-29 verbatim
example : p₃.mainDegree = 2 := sorry


-- @@ L31-31 expanded
def lCS : List ℚ[Fin 2] :=
  [p₃, p₁]


-- @@ L32-32 verbatim
lemma lCS_non_zero : 0 ∉ lCS := sorry

-- @@ L33-34 verbatim
lemma lCS_isChain : lCS.IsChain fun p q ↦ p.vars.max < q.vars.max := by
  simpa [lCS, hc₁, hc₃] using compareOfLessAndEq_eq_lt.mp rfl


-- @@ L36-36 verbatim
def CS : TriangularSet (Fin 2) ℚ := TriangularSet.mk lCS lCS_non_zero lCS_isChain


-- @@ L38-73 unexpanded
example : CS.IsCharacteristicSet ℚ l := by
  constructor
  · intro g hg
    unfold IsSetRemainder
    constructor
    · exact MvPolynomial.zero_reducedToSet
    simp only [l, List.mem_cons, List.not_mem_nil, or_false, p₁, p₂] at hg
    ----------
    use [0, 0]
    rcases hg with hg | hg
    · use [0, 1]
      sorry
    use [-1, X 0]
    sorry
    ----------
  rw [vanishingSet_eq_zeroLocus_span', vanishingSet_eq_zeroLocus_span']
  apply zeroLocus_anti_mono
  have : {p | p ∈ CS} = {p | p ∈ lCS} := by
    ext p
    simp only [SetLike.setOf_mem_eq, SetLike.mem_coe, Set.mem_setOf_eq]
    have : lCS = CS.toList := rfl
    rw [this, TriangularSet.mem_toList_iff]
  rw [l, this, lCS]
  simp only [List.mem_cons, List.not_mem_nil, or_false, ge_iff_le]
  have (p q : ℚ[Fin 2]) : {r | r = p ∨ r = q} = {p, q} := Set.insert_def ..
  rw [this, this]
  ----------
  rw [p₁, p₂, p₃]
  apply Ideal.span_le.mpr
  refine Set.pair_subset ?_ ?_
  <;> apply Ideal.mem_span_pair.mpr
  · use X 0, -1
    ring
  use 1, 0
  ring
  ----------


-- @@ L75-75 verbatim
example : l.zeroDecomposition = [CS] := sorry


-- @@ L77-77 verbatim
end em1


-- @@ L79-79 verbatim
namespace em2


-- @@ L81-81 expanded
def p₁ : ℚ[Fin 3] :=
  X 0 * X 1 * X 2 - X 1 * X 2 ^ 2 - X 0 - X 1 - X 2


-- @@ L82-82 expanded
def p₂ : ℚ[Fin 3] :=
  X 0 * X 1 - X 1 ^ 2 - X 0 + X 1 - X 2


-- @@ L83-83 expanded
def p₃ : ℚ[Fin 3] :=
  X 0 ^ 2 - X 1 ^ 2 - X 2 ^ 2


-- @@ L85-85 expanded
def l : List ℚ[Fin 3] :=
  [p₁, p₂, p₃]


-- @@ L87-88 verbatim
def AS₁ : AscendingSet (Fin 3) ℚ :=
  ⟨TriangularSet.single p₁, TriangularSet.isAscendingSet_single p₁⟩

-- @@ L89-90 verbatim
def AS₂ : AscendingSet (Fin 3) ℚ :=
  ⟨TriangularSet.single p₂, TriangularSet.isAscendingSet_single p₂⟩

-- @@ L91-92 verbatim
def AS₃ : AscendingSet (Fin 3) ℚ :=
  ⟨TriangularSet.single p₃, TriangularSet.isAscendingSet_single p₃⟩


-- @@ L94-94 expanded
def c₁ : ℚ[Fin 3] :=
  X 1 * (X 0 - 1) ^ 2 * (X 0 + 1) * (X 0 - 5)


-- @@ L95-95 expanded
def c₂ : ℚ[Fin 3] :=
  -X 2 - X 1 ^ 2 + X 1 * X 0 + X 1 - X 0


-- @@ L97-97 verbatim
lemma hIc₁ : c₁.initial = (X 0 - 1) ^ 2 * (X 0 + 1) * (X 0 - 5) := sorry

-- @@ L98-98 verbatim
lemma hIc₂ : c₂.initial = -1 := sorry


-- @@ L100-100 expanded
def lCS₁ : List ℚ[Fin 3] :=
  [c₁, c₂]


-- @@ L101-101 verbatim
lemma lCS₁_non_zero : 0 ∉ lCS₁ := sorry

-- @@ L102-102 verbatim
lemma lCS₁_isChain : lCS₁.IsChain fun p q ↦ p.vars.max < q.vars.max := sorry


-- @@ L104-104 verbatim
def CS₁ : TriangularSet (Fin 3) ℚ := TriangularSet.mk lCS₁ lCS₁_non_zero lCS₁_isChain


-- @@ L106-134 unexpanded
example : CS₁.IsCharacteristicSet ℚ l := by
  constructor
  · intro g hg
    unfold IsSetRemainder
    constructor
    · exact MvPolynomial.zero_reducedToSet
    simp only [l, List.mem_cons, List.not_mem_nil, or_false] at hg
    ----------
    sorry
    ----------
  rw [vanishingSet_eq_zeroLocus_span', vanishingSet_eq_zeroLocus_span']
  apply zeroLocus_anti_mono
  have : {p | p ∈ CS₁} = {p | p ∈ lCS₁} := by
    ext p
    simp only [SetLike.setOf_mem_eq, SetLike.mem_coe, Set.mem_setOf_eq]
    have : lCS₁ = CS₁.toList := rfl
    rw [this, TriangularSet.mem_toList_iff]
  rw [l, this, lCS₁]
  simp only [List.mem_cons, List.not_mem_nil, or_false, ge_iff_le]
  have this₁ (p q : ℚ[Fin 3]) : {t | t = p ∨ t = q} = {p, q} := Set.insert_def ..
  have this₂ (p q r : ℚ[Fin 3]) : {t | t = p ∨ t = q ∨ t = r} = {p, q, r} := Set.insert_def ..
  rw [this₁, this₂]
  ----------
  rw [p₁, p₂, p₃]
  apply Ideal.span_le.mpr
  refine Set.insert_subset_iff.mpr ?_

  ----------
  sorry


-- @@ L136-136 verbatim
example : l.zeroDecomposition = sorry := sorry


-- @@ L138-138 verbatim
end em2

-- @@ L139-139 verbatim
end
