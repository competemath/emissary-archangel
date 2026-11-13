import Mathlib
import Submission.MorseEventBracketExistence
import Submission.SignedMorseBridge


-- @@ L5-15 verbatim
/-!
# Regularity of the positive sheet at a negative Morse event

An isolating Morse bracket may fail to be a regular slab because it contains its
distinguished critical point.  If that point lies on the negative sheet, however,
the whole positive part of the zero fibre is regular throughout the bracket.

This file records the closed compact positive core used to tame the time field,
and proves that this core is contained in `slabRegularSet`.  It is the geometric
input needed to flow only the positive sheet across a negative event.
-/


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
namespace Submission


-- @@ L21-21 verbatim
open Set Function Metric

-- @@ L22-22 verbatim
open scoped RealInnerProductSpace Topology


-- @@ L24-24 verbatim
variable {n : ℕ}

-- @@ L25-25 verbatim
variable {X₀ X₁ : FramedLevelSet n}

-- @@ L26-26 verbatim
variable {S₀ : FiberSign X₀} {S₁ : FiberSign X₁}


-- @@ L28-28 verbatim
local notation "E'" => EuclideanSpace ℝ (Fin (n + 2))


-- @@ L30-30 verbatim
namespace SignedFramedLevelCobordism


-- @@ L32-37 verbatim
/-- The closed positive part of the zero fibre over a time slab.  Nonvanishing
of the sign on the zero fibre turns the weak inequality into strict positivity,
while the weak form makes closedness immediate. -/
def positiveSlabCore (C : SignedFramedLevelCobordism S₀ S₁)
    (a b : ℝ) : Set E' :=
  {v | C.cobordism.G v = 0 ∧ tcoord v ∈ Icc a b ∧ 0 ≤ C v}


-- @@ L39-52 verbatim
theorem positiveSlabCore_eq
    (C : SignedFramedLevelCobordism S₀ S₁) (a b : ℝ) :
    C.positiveSlabCore a b =
      slabFiber C.cobordism.toLevelCobordismData a b ∩ C ⁻¹' Ici 0 := by
  ext v
  simp only [positiveSlabCore, slabFiber, LevelCobordismData.fiber,
    Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Ici]
  change (C.cobordism.G v = 0 ∧ tcoord v ∈ Icc a b ∧ 0 ≤ C v) ↔
    ((C.cobordism.G v = 0 ∧ tcoord v ∈ Icc a b) ∧ 0 ≤ C v)
  constructor
  · rintro ⟨hv, ht, hs⟩
    exact ⟨⟨hv, ht⟩, hs⟩
  · rintro ⟨⟨hv, ht⟩, hs⟩
    exact ⟨hv, ht, hs⟩


-- @@ L54-61 verbatim
/-- The selected slab core is compact: it is a closed sign half-space inside
the compact spatially bounded slab fibre. -/
theorem isCompact_positiveSlabCore
    (C : SignedFramedLevelCobordism S₀ S₁) (a b : ℝ) :
    IsCompact (C.positiveSlabCore a b) := by
  rw [C.positiveSlabCore_eq]
  exact (isCompact_slabFiber C.cobordism.toLevelCobordismData a b).inter_right
    (isClosed_Ici.preimage C.continuous)


-- @@ L63-68 verbatim
/-- Membership in the closed core has genuinely positive sign on the zero
fibre. -/
theorem positive_of_mem_positiveSlabCore
    (C : SignedFramedLevelCobordism S₀ S₁) {a b : ℝ} {v : E'}
    (hv : v ∈ C.positiveSlabCore a b) : 0 < C v := by
  exact lt_of_le_of_ne hv.2.2 (C.nonzero v hv.1).symm


-- @@ L70-70 verbatim
end SignedFramedLevelCobordism


-- @@ L72-72 verbatim
namespace MorsePosition


-- @@ L74-74 verbatim
variable {C : SignedFramedLevelCobordism S₀ S₁}


-- @@ L76-96 verbatim
/-- Inside the canonical bracket of a negative event, every positive zero-fibre
point has surjective spatial derivative.  Otherwise it would be a time-critical
point, isolation would identify it with the negative centre, and the two sign
inequalities would contradict each other. -/
theorem spatialDeriv_surjective_on_positive_of_negative_event
    (P : MorsePosition C.cobordism) {t : ℝ} (ht : t ∈ P.eventTimes)
    (hnegative : P.eventCenter t ht ∈
      (C.labelMorsePosition P).negativeCenters)
    {v : E'} (hvzero : C.cobordism.G v = 0)
    (hvtime : tcoord v ∈
      Icc (P.eventBracket t ht).before (P.eventBracket t ht).after)
    (hvpositive : 0 < C v) :
    Surjective (spatialDeriv C.cobordism.G v) := by
  by_contra hsurj
  have hvcritical : v ∈ timeCritical C.cobordism.G := ⟨hvzero, hsurj⟩
  have hcenter : v = P.eventCenter t ht :=
    (P.eventBracket t ht).isolates v hvcritical hvtime
  have hcenter_negative : C (P.eventCenter t ht) < 0 := by
    exact ((C.labelMorsePosition P).mem_negativeCenters_iff.mp hnegative).2
  rw [hcenter] at hvpositive
  linarith


-- @@ L98-112 verbatim
/-- Consequently the compact positive core of a negative event lies in the
domain of the normalized time field. -/
theorem positiveSlabCore_subset_slabRegularSet_of_negative_event
    (P : MorsePosition C.cobordism) {t : ℝ} (ht : t ∈ P.eventTimes)
    (hnegative : P.eventCenter t ht ∈
      (C.labelMorsePosition P).negativeCenters) :
    C.positiveSlabCore (P.eventBracket t ht).before
        (P.eventBracket t ht).after ⊆
      slabRegularSet C.cobordism.G := by
  intro v hv
  have hspatial : Surjective (spatialDeriv C.cobordism.G v) :=
    P.spatialDeriv_surjective_on_positive_of_negative_event ht hnegative
      hv.1 hv.2.1 (C.positive_of_mem_positiveSlabCore hv)
  exact mem_slabRegularSet_of_spatial_surjective
    (C.cobordism.regular v hv.1) hspatial


-- @@ L114-114 verbatim
end MorsePosition


-- @@ L116-116 verbatim
end Submission
