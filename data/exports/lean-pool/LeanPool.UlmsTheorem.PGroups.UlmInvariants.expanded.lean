/-
Copyright (c) 2026 Elan Roth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elan Roth
-/
module

public import Mathlib.Algebra.Field.ZMod
public import LeanPool.UlmsTheorem.PGroups.Socle
public import LeanPool.UlmsTheorem.PGroups.Heights
public import Mathlib.LinearAlgebra.Dimension.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dimension.DivisionRing


-- @@ L15-37 verbatim
/-!
# Ulm invariants

For a prime p and a reduced abelian p-group G, the **Ulm invariant** at ordinal α is
  f_G(α) = dim_{ℤ/pℤ} (P_α / P_{α+1}),
where `P_α = G[p] ∩ p^α·G = pSocleAt p α`.

We also keep the raw filtration quotient `G_α / G_{α+1}` available as
`layerQuotient` / `layerInvariant`; this is useful auxiliary data, but it is
not the classical Ulm invariant used in Ulm's theorem.

## Main definitions

- `layerQuotient p α G` : the quotient group `(p^α·G) / (p^(α+1)·G)`
- `layerInvariant p α G` : the cardinal rank of `layerQuotient` as a `ℤ/pℤ`-module
- `ulmQuotient p α G` : the quotient group `P_α / P_{α+1}`
- `ulmInvariant p α G` : the cardinal rank of `ulmQuotient` as a `ℤ/pℤ`-module
- `ulmLength p G` : the least ordinal α with `p^α·G = 0`  (exists for reduced groups)

## References
- Fuchs, "Abelian Groups", Chapter 11, §1
- Kaplansky, "Infinite Abelian Groups", Theorem 14
-/


-- @@ L39-39 verbatim
@[expose] public section


-- @@ L41-41 verbatim
namespace UlmsTheorem


-- @@ L43-43 verbatim
open Ordinal Cardinal


-- @@ L45-45 verbatim
variable (p : ℕ) [hp : Fact p.Prime]


-- @@ L47-47 verbatim
/-! ### The raw filtration quotient `G_α / G_{α+1}` -/


-- @@ L49-54 verbatim
/-- `G_(α+1)` as a subgroup of `G_α`. -/
noncomputable def layerSuccIncl {G : Type*} [AddCommGroup G] (α : Ordinal) :
    ulmSubgroup p (Order.succ α) (G := G) →+ ulmSubgroup p α (G := G) := by
  refine AddSubgroup.subtype _ |>.codRestrict _ ?_
  intro x
  exact ulmSubgroup_antitone p (Order.le_succ α) x.property


-- @@ L56-62 verbatim
/-- The quotient `G_α / G_{α+1}`. This is useful auxiliary filtration data, but
it is not the classical Ulm invariant. -/
noncomputable def layerQuotient {G : Type*} [AddCommGroup G] (α : Ordinal) :
    Type _ :=
  (ulmSubgroup p α (G := G)) ⧸
    ((ulmSubgroup p (Order.succ α) (G := G)).comap
      (ulmSubgroup p α (G := G)).subtype)


-- @@ L64-67 verbatim
noncomputable instance {G : Type*} [AddCommGroup G] (α : Ordinal) :
    AddCommGroup (layerQuotient p α (G := G)) := by
  unfold layerQuotient
  infer_instance


-- @@ L69-86 verbatim
omit hp in
/-- Every element of `G_α / G_{α+1}` has order `p`. -/
lemma layerQuotient_orderOf_dvd_p {G : Type*} [AddCommGroup G] (α : Ordinal)
    (x : layerQuotient p α (G := G)) : p • x = 0 := by
  refine Quotient.inductionOn x ?_
  intro a
  change QuotientAddGroup.mk'
      ((ulmSubgroup p (Order.succ α) (G := G)).comap (ulmSubgroup p α (G := G)).subtype)
      (p • a) =
    QuotientAddGroup.mk'
      ((ulmSubgroup p (Order.succ α) (G := G)).comap (ulmSubgroup p α (G := G)).subtype)
      0
  have hmem : (p • (a : G)) ∈ ulmSubgroup p (Order.succ α) (G := G) := by
    rw [ulmSubgroup_succ]
    exact ⟨a, a.property, rfl⟩
  apply (QuotientAddGroup.mk'_eq_mk' _).2
  refine ⟨-(p • a), ?_, by simp⟩
  exact (ulmSubgroup p (Order.succ α) (G := G)).neg_mem hmem


-- @@ L88-93 verbatim
noncomputable instance layerQuotientModule {G : Type*} [AddCommGroup G]
    (α : Ordinal) : Module (ZMod p) (layerQuotient p α (G := G)) := by
  classical
  refine AddCommGroup.zmodModule (n := p) (G := layerQuotient p α (G := G)) ?_
  intro x
  simpa using layerQuotient_orderOf_dvd_p p α x


-- @@ L95-98 verbatim
/-- The raw filtration-layer rank `dim_{ℤ/pℤ}(G_α / G_{α+1})`. -/
noncomputable def layerInvariant {G : Type*} [AddCommGroup G]
    (α : Ordinal) : Cardinal :=
  Module.rank (ZMod p) (layerQuotient p α (G := G))


-- @@ L100-100 verbatim
/-! ### The classical Ulm quotient `P_α / P_{α+1}` -/


-- @@ L102-105 verbatim
/-- `P_(α+1)` as a `ZMod p`-submodule of `P_α`. -/
noncomputable def ulmDenSubmodule {G : Type*} [AddCommGroup G] (α : Ordinal) :
    Submodule (ZMod p) (pSocleAt p α (G := G)) :=
  AddSubgroup.toZModSubmodule p (pSocleAtSuccSubgroupOf p α)


-- @@ L107-110 verbatim
/-- The classical Ulm quotient at `α`: `P_α / P_{α+1}`. -/
abbrev ulmQuotient {G : Type*} [AddCommGroup G] (α : Ordinal) :
    Type _ :=
  (pSocleAt p α (G := G)) ⧸ ulmDenSubmodule p α


-- @@ L112-122 verbatim
/-- Every element of the classical Ulm quotient has order `p`. -/
lemma ulmQuotient_orderOf_dvd_p {G : Type*} [AddCommGroup G] (α : Ordinal)
    (x : ulmQuotient p α (G := G)) : p • x = 0 := by
  refine Quotient.inductionOn x ?_
  intro a
  have hp0 : p • a = 0 := by
    ext
    simpa using (mem_pSocleAt p α (a : G)).1 a.property |>.1
  change (Submodule.Quotient.mk (p • a) : ulmQuotient p α (G := G)) = 0
  rw [hp0]
  rfl


-- @@ L124-127 verbatim
/-- The classical Ulm invariant `f_G(α) = dim_{ℤ/pℤ}(P_α / P_{α+1})`. -/
noncomputable def ulmInvariant {G : Type*} [AddCommGroup G]
    (α : Ordinal) : Cardinal :=
  Module.rank (ZMod p) (ulmQuotient p α (G := G))


-- @@ L129-129 verbatim
/-! ### Hill, marked-graded, and overhang invariants -/


-- @@ L131-131 verbatim
section RelativeInvariants


-- @@ L133-133 verbatim
variable {G : Type*} [AddCommGroup G]


-- @@ L135-140 verbatim
/-- The marked-graded denominator
`P_(α+1) + (S ∩ P_α)`, viewed as a subgroup of `P_α`. -/
noncomputable def markedGradedDen (S : AddSubgroup G) (α : Ordinal) :
    AddSubgroup (pSocleAt p α (G := G)) :=
  (pSocleAt p (Order.succ α) ⊔ (S ⊓ pSocleAt p α)).comap
    (pSocleAt p α).subtype


-- @@ L142-145 verbatim
/-- The marked-graded denominator as a `ZMod p`-submodule of `P_α`. -/
noncomputable def markedGradedSubmodule (S : AddSubgroup G) (α : Ordinal) :
    Submodule (ZMod p) (pSocleAt p α (G := G)) :=
  AddSubgroup.toZModSubmodule p (markedGradedDen p S α)


-- @@ L147-150 verbatim
/-- The marked-graded socle space
`P_α / (P_(α+1) + (S ∩ P_α))`. -/
abbrev markedGradedQuotient (S : AddSubgroup G) (α : Ordinal) : Type _ :=
  (pSocleAt p α (G := G)) ⧸ markedGradedSubmodule p S α


-- @@ L152-155 verbatim
/-- The rank of the marked-graded socle space
`dim_(ZMod p) P_α / (P_(α+1) + (S ∩ P_α))`. -/
noncomputable def markedGradedInvariant (S : AddSubgroup G) (α : Ordinal) : Cardinal :=
  Module.rank (ZMod p) (markedGradedQuotient p S α)


-- @@ L157-170 verbatim
/-- With no marked subgroup, the marked-graded invariant is the ordinary Ulm invariant. -/
theorem markedGradedInvariant_bot (α : Ordinal) :
    markedGradedInvariant p (⊥ : AddSubgroup G) α = ulmInvariant p α (G := G) := by
  have hden :
      markedGradedSubmodule p (⊥ : AddSubgroup G) α = ulmDenSubmodule p α := by
    ext x
    simp [markedGradedSubmodule, markedGradedDen, ulmDenSubmodule,
      pSocleAtSuccSubgroupOf]
  unfold markedGradedInvariant ulmInvariant
  change Module.rank (ZMod p)
      ((pSocleAt p α (G := G)) ⧸ markedGradedSubmodule p (⊥ : AddSubgroup G) α) =
    Module.rank (ZMod p)
      ((pSocleAt p α (G := G)) ⧸ ulmDenSubmodule p α)
  rw [hden]


-- @@ L172-177 verbatim
/-- The Fuchs/Walker Hill denominator
`P_α ∩ (S + G_(α+1))`, viewed inside `P_α`. -/
noncomputable def hillDen (S : AddSubgroup G) (α : Ordinal) :
    AddSubgroup (pSocleAt p α (G := G)) :=
  (pSocleAt p α ⊓ (S ⊔ ulmSubgroup p (Order.succ α))).comap
    (pSocleAt p α).subtype


-- @@ L179-182 verbatim
/-- The Hill denominator as a `ZMod p`-submodule of `P_α`. -/
noncomputable def hillSubmodule (S : AddSubgroup G) (α : Ordinal) :
    Submodule (ZMod p) (pSocleAt p α (G := G)) :=
  AddSubgroup.toZModSubmodule p (hillDen p S α)


-- @@ L184-187 verbatim
/-- The Fuchs/Walker Hill (relative Ulm) space
`P_α / (P_α ∩ (S + G_(α+1)))`. -/
abbrev hillQuotient (S : AddSubgroup G) (α : Ordinal) : Type _ :=
  (pSocleAt p α (G := G)) ⧸ hillSubmodule p S α


-- @@ L189-192 verbatim
/-- The Fuchs/Walker Hill invariant. Its nonzero classes are exactly the
order-`p`, exact-height-`α` elements proper with respect to `S`. -/
noncomputable def hillInvariant (S : AddSubgroup G) (α : Ordinal) : Cardinal :=
  Module.rank (ZMod p) (hillQuotient p S α)


-- @@ L194-216 verbatim
/-- With no marked subgroup, the Hill invariant is the ordinary Ulm invariant. -/
theorem hillInvariant_bot (α : Ordinal) :
    hillInvariant p (⊥ : AddSubgroup G) α = ulmInvariant p α (G := G) := by
  have hden :
      hillSubmodule p (⊥ : AddSubgroup G) α = ulmDenSubmodule p α := by
    ext x
    change
      ((x : G) ∈ pSocleAt p α ⊓
        ((⊥ : AddSubgroup G) ⊔ ulmSubgroup p (Order.succ α))) ↔
      (x : G) ∈ pSocleAt p (Order.succ α)
    simp only [bot_sup_eq, AddSubgroup.mem_inf]
    constructor
    · rintro ⟨_, hxSucc⟩
      exact (mem_pSocleAt p (Order.succ α) (x : G)).2
        ⟨(mem_pSocleAt p α (x : G)).1 x.property |>.1, hxSucc⟩
    · intro hx
      exact ⟨x.property, (mem_pSocleAt p (Order.succ α) (x : G)).1 hx |>.2⟩
  unfold hillInvariant ulmInvariant
  change Module.rank (ZMod p)
      ((pSocleAt p α (G := G)) ⧸ hillSubmodule p (⊥ : AddSubgroup G) α) =
    Module.rank (ZMod p)
      ((pSocleAt p α (G := G)) ⧸ ulmDenSubmodule p α)
  rw [hden]


-- @@ L218-221 verbatim
/-- BCM's "relative Ulm" terminology names the same quotient as the
Fuchs/Walker Hill invariant. -/
noncomputable abbrev relativeUlmDen (S : AddSubgroup G) (α : Ordinal) :=
  hillDen p S α


-- @@ L223-225 verbatim
/-- The relative Ulm submodule, in the equivalent Hill-invariant formulation. -/
noncomputable abbrev relativeUlmSubmodule (S : AddSubgroup G) (α : Ordinal) :=
  hillSubmodule p S α


-- @@ L227-229 verbatim
/-- The relative Ulm quotient by the Hill denominator. -/
abbrev relativeUlmQuotient (S : AddSubgroup G) (α : Ordinal) :=
  hillQuotient p S α


-- @@ L231-233 verbatim
/-- The relative Ulm invariant, expressed as the rank of the Hill quotient. -/
noncomputable abbrev relativeUlmInvariant (S : AddSubgroup G) (α : Ordinal) :=
  hillInvariant p S α


-- @@ L235-251 verbatim
/-- The marked-graded denominator is contained in the Hill denominator. -/
lemma markedGradedSubmodule_le_hillSubmodule (S : AddSubgroup G) (α : Ordinal) :
    markedGradedSubmodule p S α ≤ hillSubmodule p S α := by
  intro x hx
  change (x : G) ∈ pSocleAt p α ⊓ (S ⊔ ulmSubgroup p (Order.succ α))
  change (x : G) ∈
    pSocleAt p (Order.succ α) ⊔ (S ⊓ pSocleAt p α) at hx
  refine ⟨x.property, ?_⟩
  have hle :
      pSocleAt p (Order.succ α) ⊔ (S ⊓ pSocleAt p α) ≤
        S ⊔ ulmSubgroup p (Order.succ α) := by
    apply sup_le
    · intro y hy
      exact AddSubgroup.mem_sup_right hy.2
    · intro y hy
      exact AddSubgroup.mem_sup_left hy.1
  exact hle hx


-- @@ L253-259 verbatim
/-- The ordinary Ulm denominator `P_(α+1)` is contained in the Hill denominator. -/
lemma ulmDenSubmodule_le_hillSubmodule (S : AddSubgroup G) (α : Ordinal) :
    ulmDenSubmodule p α ≤ hillSubmodule p S α := by
  intro x hx
  change (x : G) ∈ pSocleAt p α ⊓ (S ⊔ ulmSubgroup p (Order.succ α))
  change (x : G) ∈ pSocleAt p (Order.succ α) at hx
  exact ⟨x.property, AddSubgroup.mem_sup_right hx.2⟩


-- @@ L261-264 verbatim
/-- The subspace of the ordinary Ulm layer occupied by the marked subgroup `S`. -/
noncomputable def relativeOccupiedSubmodule (S : AddSubgroup G) (α : Ordinal) :
    Submodule (ZMod p) (ulmQuotient p α (G := G)) :=
  (hillSubmodule p S α).map (ulmDenSubmodule p α).mkQ


-- @@ L266-273 verbatim
/-- Quotienting the ordinary Ulm layer by its occupied subspace gives the
relative Ulm space. -/
noncomputable def occupiedQuotientEquivRelative (S : AddSubgroup G) (α : Ordinal) :
    (ulmQuotient p α (G := G) ⧸ relativeOccupiedSubmodule p S α) ≃ₗ[ZMod p]
      hillQuotient p S α :=
  Submodule.quotientQuotientEquivQuotient
    (ulmDenSubmodule p α) (hillSubmodule p S α)
    (ulmDenSubmodule_le_hillSubmodule p S α)


-- @@ L275-284 verbatim
/-- The occupied-space equation underlying the Barwise–Eklof room criterion:
`relative room + occupied = the ordinary Ulm invariant`. -/
theorem relativeUlmInvariant_add_occupiedInvariant
    (S : AddSubgroup G) (α : Ordinal) :
    relativeUlmInvariant p S α +
        Module.rank (ZMod p) (relativeOccupiedSubmodule p S α) =
      ulmInvariant p α (G := G) := by
  unfold relativeUlmInvariant hillInvariant ulmInvariant
  rw [← (occupiedQuotientEquivRelative p S α).rank_eq]
  exact Submodule.rank_quotient_add_rank (relativeOccupiedSubmodule p S α)


-- @@ L286-290 verbatim
/-- The BCM overhang, as the kernel subspace inside the marked-graded quotient.
This ordinal-indexed definition extends BCM's finite-level construction. -/
noncomputable def overhangSubmodule (S : AddSubgroup G) (α : Ordinal) :
    Submodule (ZMod p) (markedGradedQuotient p S α) :=
  (hillSubmodule p S α).map (markedGradedSubmodule p S α).mkQ


-- @@ L292-294 verbatim
/-- The dimension of the BCM overhang space. -/
noncomputable def overhangInvariant (S : AddSubgroup G) (α : Ordinal) : Cardinal :=
  Module.rank (ZMod p) (overhangSubmodule (p := p) S α)


-- @@ L296-299 verbatim
/-- The canonical quotient map from the marked-graded space onto the Hill space. -/
noncomputable def markedGradedToHill (S : AddSubgroup G) (α : Ordinal) :
    markedGradedQuotient p S α →ₗ[ZMod p] hillQuotient p S α :=
  Submodule.factor (markedGradedSubmodule_le_hillSubmodule p S α)


-- @@ L301-303 verbatim
theorem markedGradedToHill_surjective (S : AddSubgroup G) (α : Ordinal) :
    Function.Surjective (markedGradedToHill (p := p) S α) := by
  exact Submodule.factor_surjective (markedGradedSubmodule_le_hillSubmodule p S α)


-- @@ L305-316 verbatim
/-- BCM's exact-sequence dimension equation:
the marked-graded invariant is the Hill invariant plus the overhang dimension. -/
theorem hillInvariant_add_overhangInvariant
    (S : AddSubgroup G) (α : Ordinal) :
    hillInvariant p S α + overhangInvariant (p := p) S α =
      markedGradedInvariant p S α := by
  unfold hillInvariant overhangInvariant markedGradedInvariant
  unfold hillQuotient markedGradedQuotient overhangSubmodule
  rw [← (Submodule.quotientQuotientEquivQuotient
    (markedGradedSubmodule p S α) (hillSubmodule p S α)
    (markedGradedSubmodule_le_hillSubmodule p S α)).rank_eq]
  exact Submodule.rank_quotient_add_rank (overhangSubmodule p S α)


-- @@ L318-323 verbatim
/-- The same BCM equation in relative-Ulm terminology. -/
theorem relativeUlmInvariant_add_overhangInvariant
    (S : AddSubgroup G) (α : Ordinal) :
    relativeUlmInvariant p S α + overhangInvariant (p := p) S α =
      markedGradedInvariant p S α :=
  hillInvariant_add_overhangInvariant p S α


-- @@ L325-325 verbatim
end RelativeInvariants


-- @@ L327-327 verbatim
/-! ### Ulm length -/


-- @@ L329-332 verbatim
/-- The least ordinal α at which p^α·G = 0, or zero if no such ordinal exists.
    Reducedness guarantees that this infimum is attained. -/
noncomputable def ulmLength {G : Type*} [AddCommGroup G] : Ordinal.{0} :=
  sInf {α : Ordinal.{0} | ulmSubgroup p α (G := G) = ⊥}


-- @@ L334-334 verbatim
namespace ulmLength


-- @@ L336-336 verbatim
variable {G : Type*} [AddCommGroup G]


-- @@ L338-342 verbatim
omit hp in
/-- The set `{α | p^α·G = 0}` is nonempty for a reduced p-group. -/
lemma exists_zero (hred' : IsPReduced p G) :
    ∃ α : Ordinal.{0}, ulmSubgroup p α (G := G) = ⊥ := by
  exact hred'


-- @@ L344-348 verbatim
omit hp in
/-- p^(ulmLength)·G = 0. -/
lemma at_ulmLength (hred : IsPReduced p G) :
    ulmSubgroup p (ulmLength p (G := G)) (G := G) = ⊥ :=
  csInf_mem (exists_zero (p := p) (G := G) hred)


-- @@ L350-373 verbatim
/-- Ulm invariants vanish above the Ulm length. -/
lemma inv_zero_of_ge (hred : IsPReduced p G)
    (α : Ordinal) (hα : ulmLength p (G := G) ≤ α) :
    ulmInvariant p α (G := G) = 0 := by
  have hzero : ulmSubgroup p α (G := G) = ⊥ := by
    apply le_bot_iff.mp
    simpa [at_ulmLength (p := p) (hred := hred)] using
      (ulmSubgroup_antitone p hα : ulmSubgroup p α (G := G) ≤
        ulmSubgroup p (ulmLength p (G := G)) (G := G))
  have hpzero : pSocleAt p α (G := G) = ⊥ := by
    rw [pSocleAt, hzero]
    simp
  let _ : Subsingleton (pSocleAt p α (G := G)) := by
    rw [hpzero]
    infer_instance
  let _ : Subsingleton (ulmQuotient p α (G := G)) := by
    refine ⟨?_⟩
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    obtain rfl : a = b := Subsingleton.elim _ _
    rfl
  rw [ulmInvariant]
  exact rank_subsingleton' (R := ZMod p) (M := ulmQuotient p α (G := G))


-- @@ L375-375 verbatim
end ulmLength


-- @@ L377-377 verbatim
/-! ### Ulm sequence as a function ℕ → Cardinal (for successor-length groups) -/


-- @@ L379-383 verbatim
/-- For groups of Ulm length `ω·γ + n`, the tail Ulm invariants are those at
`ω·γ`, `ω·γ+1`, ..., `ω·γ+(n-1)`. -/
noncomputable def tailInvariants {G : Type*} [AddCommGroup G]
    (γ : Ordinal) (n : ℕ) : Fin n → Cardinal :=
  fun k ↦ ulmInvariant p (ω * γ + k.1) (G := G)


-- @@ L385-385 verbatim
end UlmsTheorem
