/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.SuperSymmetry.SU5.ChargeSpectrum.MinimallyAllowsTerm.OfFinset
public import Physlib.StringTheory.FTheory.SU5.Fluxes.NoExotics.Completeness

-- @@ L10-83 verbatim
/-!

# Quanta of 5-d representations

## i. Overview

The 5-bar representations of the `SU(5)×U(1)` carry
the quantum numbers of their `U(1)` charges and their fluxes.

In this module we define the data structure for these quanta and
properties thereof.

## ii. Key results

- `FiveQuanta` is the type of quanta of 5-bar representations.
- `FiveQuanta.toFluxesFive` is the underlying `FluxesFive` of a `FiveQuanta`.
- `FiveQuanta.toCharges` is the underlying Multiset charges of a `FiveQuanta`.
- `FiveQuanta.reduce` is the reduction of a `FiveQuanta` which adds together
  all the fluxes corresponding to the same charge (i.e. representation).
- `FiveQuanta.liftCharges` given a charge `c` the `FiveQuanta` which have
  charge `c` and no exotics or zero fluxes.
- `FiveQuanta.anomalyCoefficient` is the anomaly coefficient associated with a `FiveQuanta`.

## iii. Table of contents

- A. The definition of `FiveQuanta`
  - A.1. The map to underlying fluxes
  - A.2. The map to underlying charges
  - A.3. The map from charges to fluxes
- B. The reduction of a `FiveQuanta`
  - B.1. The reduced `FiveQuanta` has no duplicate elements
  - B.2. The underlying charges of the reduced `FiveQuanta` are the deduped charges
  - B.3. Membership condition on the reduced `FiveQuanta`
  - B.4. Filter of the reduced `FiveQuanta` by a charge
  - B.5. The reduction is idempotent
  - B.6. Preservation of certain sums under reduction
  - B.7. Reduction does nothing if no duplicate charges
  - B.8. The charge map is preserved by reduction
  - B.9. A fluxes in the reduced `FiveQuanta` is a sum of fluxes in the original `FiveQuanta`
  - B.10. No exotics condition on the reduced `FiveQuanta`
    - B.10.1. Number of chiral `L`
    - B.10.2. Number of anti-chiral `L`
    - B.10.3. Number of chiral `D`
    - B.10.4. Number of anti-chiral `D`
    - B.10.5. The `NoExotics` condition on the reduced `FiveQuanta`
  - B.11. Reduce member of `FluxesFive.elemsNoExotics`
- C. Decomposition of a `FiveQuanta` into basic fluxes
  - C.1. Decomposition of fluxes
  - C.2. Decomposition of a `FiveQuanta` (with no exotics)
    - C.2.1. Decomposition distributes over addition
    - C.2.2. Decomposition commutes with filtering charges
    - C.2.3. Decomposition preserves the charge map
    - C.2.4. Decomposition preserves the charges
    - C.2.5. Decomposition preserves the reduction
    - C.2.6. Fluxes of the decomposition of a `FiveQuanta`
- D. Lifting charges to `FiveQuanta`
  - D.1. `liftCharge c`: multiset of five-quanta for a finite set of charges `c` with no exotics
  - D.2. FiveQuanta in `liftCharge c` have a finite set of charges `c`
  - D.3. FiveQuanta in `liftCharge c` have no duplicate charges
  - D.4. Membership in `liftCharge c` iff is reduction of `FiveQuanta` with given fluxes
  - D.5. FiveQuanta in `liftCharge c` do not have zero fluxes
  - D.6. FiveQuanta in `liftCharge c` have no exotics
  - D.7. Membership in `liftCharge c` iff have no exotics, no zero fluxes, and charges `c`
  - D.8. `liftCharge c` is preserved under a map if reduced
- E. Anomaly cancellation coefficients
  - E.1. Anomaly coefficients of a `FiveQuanta`
  - E.2. Anomaly coefficients under a map
  - E.3. Anomaly coefficients is preserved under `reduce`

## iv. References

* Rational F-Theory GUTs without exotics (arXiv:1401.5084), Anomaly cancellation
  conditions. [ref: arxiv_1401_5084]
-/


-- @@ L85-85 verbatim
@[expose] public section

-- @@ L86-86 verbatim
namespace FTheory


-- @@ L88-88 verbatim
namespace SU5

-- @@ L89-89 verbatim
open SU5


-- @@ L91-95 verbatim
/-!

## A. The definition of `FiveQuanta`

-/


-- @@ L97-99 verbatim
/-- The quanta of 5-bar representations corresponding to a multiset of
  `(q, M, N)` for each particle. `(M, N)` are defined in the `FluxesFive` module. -/
abbrev FiveQuanta (𝓩 : Type := ℤ) : Type := Multiset (𝓩 × Fluxes)


-- @@ L101-101 verbatim
namespace FiveQuanta


-- @@ L103-103 verbatim
variable {𝓩 : Type}


-- @@ L105-109 verbatim
/-!

### A.1. The map to underlying fluxes

-/


-- @@ L111-112 verbatim
/-- The underlying `FluxesFive` from a `FiveQuanta`. -/
def toFluxesFive (x : FiveQuanta 𝓩) : FluxesFive := x.map Prod.snd


-- @@ L114-118 verbatim
/-!

### A.2. The map to underlying charges

-/


-- @@ L120-121 verbatim
/-- The underlying Multiset charges from a `FiveQuanta`. -/
def toCharges (x : FiveQuanta 𝓩) : Multiset 𝓩 := x.map Prod.fst


-- @@ L123-127 verbatim
/-!

### A.3. The map from charges to fluxes

-/


-- @@ L129-132 verbatim
/-- The map which takes a charge to the overall flux it
  corresponds to in a `FiveQuanta`. -/
def toChargeMap [DecidableEq 𝓩] (x : FiveQuanta 𝓩) : 𝓩 → Fluxes :=
  fun z => ((x.filter fun p => p.1 = z).map Prod.snd).sum


-- @@ L134-140 verbatim
lemma toChargeMap_of_not_mem [DecidableEq 𝓩] (x : FiveQuanta 𝓩) {z : 𝓩} (h : z ∉ x.toCharges) :
    x.toChargeMap z = 0 := by
  have hl : Multiset.filter (fun p => p.1 = z) x = 0 := by
    rw [Multiset.filter_eq_nil]
    rintro ⟨a, b⟩ hab rfl
    exact h (Multiset.mem_map_of_mem Prod.fst hab)
  simp [toChargeMap, hl]


-- @@ L142-146 verbatim
/-!

## B. The reduction of a `FiveQuanta`

-/


-- @@ L148-148 verbatim
section reduce


-- @@ L150-150 verbatim
variable [DecidableEq 𝓩]


-- @@ L152-155 verbatim
/-- The `reduce` of `FiveQuanta` is a new `FiveQuanta` with all the fluxes
  corresponding to the same charge (i.e. representation) added together. -/
def reduce (x : FiveQuanta 𝓩) : FiveQuanta 𝓩 :=
  x.toCharges.dedup.map fun q5 => (q5, ((x.filter (fun f => f.1 = q5)).map (fun y => y.2)).sum)


-- @@ L157-161 verbatim
/-!

### B.1. The reduced `FiveQuanta` has no duplicate elements

-/


-- @@ L163-165 verbatim
lemma reduce_nodup (x : FiveQuanta 𝓩) : x.reduce.Nodup := by
  rw [reduce]
  exact Multiset.Nodup.map (fun _ _ h => congrArg Prod.fst h) (Multiset.nodup_dedup x.toCharges)


-- @@ L167-169 verbatim
@[simp]
lemma reduce_dedup (x : FiveQuanta 𝓩) : x.reduce.dedup = x.reduce :=
  Multiset.Nodup.dedup x.reduce_nodup


-- @@ L171-175 verbatim
/-!

### B.2. The underlying charges of the reduced `FiveQuanta` are the deduped charges

-/


-- @@ L177-178 verbatim
lemma reduce_toCharges (x : FiveQuanta 𝓩) : x.reduce.toCharges = x.toCharges.dedup := by
  simp [reduce, toCharges]


-- @@ L180-184 verbatim
/-!

### B.3. Membership condition on the reduced `FiveQuanta`

-/


-- @@ L186-190 verbatim
lemma mem_reduce_iff (x : FiveQuanta 𝓩) (p : 𝓩 × Fluxes) :
    p ∈ x.reduce ↔ p.1 ∈ x.toCharges ∧
      p.2 = ((x.filter (fun f => f.1 = p.1)).map (fun y => y.2)).sum := by
  simp [reduce]
  aesop


-- @@ L192-196 verbatim
/-!

### B.4. Filter of the reduced `FiveQuanta` by a charge

-/


-- @@ L198-201 verbatim
lemma reduce_filter (x : FiveQuanta 𝓩) (q : 𝓩) (h : q ∈ x.toCharges) :
    x.reduce.filter (fun f => f.1 = q) =
    {(q, ((x.filter (fun f => f.1 = q)).map (fun y => y.2)).sum)} := by
  simp [reduce, Multiset.filter_map, Function.comp, Multiset.filter_eq', h]


-- @@ L203-207 verbatim
/-!

### B.5. The reduction is idempotent

-/


-- @@ L209-219 verbatim
@[simp]
lemma reduce_reduce (x : FiveQuanta 𝓩) :
    x.reduce.reduce = x.reduce := by
  refine Multiset.Nodup.toFinset_inj (reduce_nodup x.reduce) (reduce_nodup x) ?_
  ext p
  simp only [Multiset.mem_toFinset]
  rw [mem_reduce_iff, reduce_toCharges, mem_reduce_iff]
  simp only [Multiset.mem_dedup, and_congr_right_iff]
  intro hp
  rw [reduce_filter x p.1 hp]
  simp


-- @@ L221-225 verbatim
/-!

### B.6. Preservation of certain sums under reduction

-/


-- @@ L227-284 verbatim
lemma reduce_sum_eq_sum_toCharges {M} [AddCommMonoid M] (x : FiveQuanta 𝓩) (f : 𝓩 → Fluxes →+ M) :
    (x.reduce.map fun (q5, x) => f q5 x).sum = (x.map fun (q5, x) => f q5 x).sum := by
  calc _
      _ = ∑ q5 ∈ x.toCharges.toFinset,
          f q5 ((x.filter (fun f => f.1 = q5)).map (fun y => y.2)).sum := by
        rw [reduce]
        simp [Finset.sum]
      _ = ∑ q5 ∈ x.toCharges.toFinset,
          (((x.filter (fun f => f.1 = q5)).map (fun y => f q5 y.2))).sum := by
        congr
        funext q5
        rw [AddMonoidHom.map_multiset_sum, Multiset.map_map]
        rfl
      _ = (x.toCharges.dedup.bind fun q5 =>
          ((x.filter (fun f => f.1 = q5)).map (fun y => f q5 y.2))).sum := by
        rw [Multiset.sum_bind]
        simp [Finset.sum]
      _ = (((x.toCharges.dedup.bind fun q5 =>
          ((x.filter (fun f => f.1 = q5)))).map (fun y => f y.1 y.2))).sum := by
        congr
        rw [Multiset.map_bind]
        congr
        funext q5
        refine Multiset.map_congr rfl ?_
        intro y hy
        simp at hy
        rw [hy.2]
      _ = ((x.map (fun y => f y.1 y.2))).sum := by
        congr
        apply Multiset.ext.mpr
        intro p
        trans ((x.map Prod.fst).dedup.map (fun y => if p.1 = y then x.count p else 0)).sum
        · rw [@Multiset.count_bind]
          congr
          funext q5
          rw [Multiset.count_filter]
        by_cases h_mem : p.1 ∈ x.map Prod.fst
        · have h_mem_dedup : p.1 ∈ (x.map Prod.fst).dedup := by rwa [Multiset.mem_dedup]
          rw [Multiset.sum_map_eq_nsmul_single p.1]
          simp only [↓reduceIte, smul_eq_mul]
          have h_count_one : Multiset.count p.1 (Multiset.map Prod.fst x).dedup = 1 := by
            refine Multiset.count_eq_one_of_mem ?_ h_mem_dedup
            exact Multiset.nodup_dedup (Multiset.map Prod.fst x)
          simp [h_count_one]
          intro q5' h h2
          simp_all [eq_comm]
        · rw [Multiset.sum_eq_zero]
          refine Eq.symm (Multiset.count_eq_zero_of_notMem ?_)
          intro h
          have h_mem : p.1 ∈ Multiset.map Prod.fst x := by
            simp_all
          (expose_names; exact h_mem_1 h_mem)
          intro p' hp
          simp at hp
          obtain ⟨q5', ⟨f1, hf⟩, hp'⟩ := hp
          by_cases h_eq : p.1 = q5'
          · simp_all
          · simp_all


-- @@ L286-290 verbatim
/-!

### B.7. Reduction does nothing if no duplicate charges

-/


-- @@ L292-315 verbatim
lemma reduce_eq_self_of_ofCharges_nodup (x : FiveQuanta 𝓩) (h : x.toCharges.Nodup) :
    x.reduce = x := by
  rw [reduce, Multiset.Nodup.dedup h]
  simp [toCharges]
  conv_rhs => rw [← Multiset.map_id x]
  apply Multiset.map_congr rfl
  intro p hp
  simp only [id_eq]
  have x_noDup : x.Nodup := Multiset.Nodup.of_map Prod.fst h
  suffices (Multiset.filter (fun f => f.1 = p.1) x) = {p} by simp [this]
  refine (Multiset.Nodup.ext (Multiset.Nodup.filter (fun f => f.1 = p.1) x_noDup)
    (Multiset.nodup_singleton p)).mpr ?_
  intro p'
  simp only [Multiset.mem_filter, Multiset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    simp [toCharges] at h
    rw [propext (Multiset.nodup_map_iff_inj_on x_noDup)] at h
    apply h
    · exact h1
    · exact hp
    · exact h2
  · rintro ⟨rfl⟩
    simp_all


-- @@ L317-321 verbatim
/-!

### B.8. The charge map is preserved by reduction

-/


-- @@ L323-332 verbatim
lemma reduce_toChargeMap_eq (x : FiveQuanta 𝓩) :
    x.reduce.toChargeMap = x.toChargeMap := by
  funext q
  by_cases h : q ∈ x.toCharges
  · rw [toChargeMap, reduce_filter x q h]
    simp
    rfl
  · rw [toChargeMap_of_not_mem, toChargeMap_of_not_mem]
    · exact h
    · simpa [reduce_toCharges] using h


-- @@ L334-338 verbatim
/-!

### B.9. A fluxes in the reduced `FiveQuanta` is a sum of fluxes in the original `FiveQuanta`

-/


-- @@ L340-350 verbatim
lemma mem_powerset_sum_of_mem_reduce_toFluxesFive {F : FiveQuanta 𝓩}
    {f : Fluxes} (hf : f ∈ F.reduce.toFluxesFive) :
    f ∈ (Multiset.powerset F.toFluxesFive).map fun s => s.sum := by
  rw [toFluxesFive, Multiset.mem_map] at hf
  obtain ⟨⟨q, f⟩, hp, rfl⟩ := hf
  rw [mem_reduce_iff] at hp
  simp at hp
  obtain ⟨hq, rfl⟩ := hp
  simp only [Multiset.mem_map, Multiset.mem_powerset]
  use (Multiset.map (fun x => x.2) (Multiset.filter (fun x => x.1 = q) F))
  exact ⟨Multiset.map_le_map (Multiset.filter_le _ F), rfl⟩


-- @@ L352-370 verbatim
lemma mem_powerset_sum_of_mem_reduce_toFluxesFive_filter {F : FiveQuanta 𝓩}
    {f : Fluxes} (hf : f ∈ F.reduce.toFluxesFive) :
    f ∈ (F.toFluxesFive.powerset.filter fun s => s ≠ ∅).map fun s => s.sum := by
  rw [toFluxesFive, Multiset.mem_map] at hf
  obtain ⟨⟨q, f⟩, hp, rfl⟩ := hf
  rw [mem_reduce_iff] at hp
  simp at hp
  obtain ⟨hq, rfl⟩ := hp
  simp only [Multiset.mem_map]
  use (Multiset.map (fun x => x.2) (Multiset.filter (fun x => x.1 = q) F))
  simp only [and_true]
  rw [Multiset.mem_filter]
  apply And.intro
  exact Multiset.mem_powerset.mpr (Multiset.map_le_map (Multiset.filter_le (fun x => x.1 = q) F))
  simp [Multiset.empty_eq_zero, ne_eq, Multiset.map_eq_zero, Multiset.filter_eq_nil,
    Prod.forall, not_forall, Decidable.not_not]
  rw [toCharges, Multiset.mem_map] at hq
  obtain ⟨a, ha, rfl⟩ := hq
  use a.2


-- @@ L372-376 verbatim
/-!

### B.10. No exotics condition on the reduced `FiveQuanta`

-/


-- @@ L378-382 verbatim
/-!

#### B.10.1. Number of chiral `L`

-/


-- @@ L384-401 verbatim
lemma reduce_numChiralL_of_mem_elemsNoExotics {F : FiveQuanta 𝓩}
    (hx : F.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    F.reduce.toFluxesFive.numChiralL = 3 := by
  have hE : F.toFluxesFive.NoExotics := ((FluxesFive.noExotics_iff_mem_elemsNoExotics _).mpr hx).1
  have hnn : ∀ a ∈ F.reduce.toFluxesFive.map (fun f => f.M + f.N), 0 ≤ a := by
    intro a ha
    obtain ⟨f, hf, rfl⟩ := Multiset.mem_map.mp ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesFive hf
    clear ha hE
    generalize F.toFluxesFive = G at *
    revert f
    revert G
    decide
  rw [FluxesFive.numChiralL, FluxesFive.chiralIndicesOfL, Multiset.filter_eq_self.mpr hnn,
    ← FluxesFive.chiralIndicesOfL_sum_eq_three_of_noExotics _ hE, FluxesFive.chiralIndicesOfL,
    toFluxesFive, toFluxesFive, Multiset.map_map, Multiset.map_map]
  exact reduce_sum_eq_sum_toCharges F (fun _ =>
    ⟨⟨fun f => f.M + f.N, by simp⟩, fun x y => by simp [add_add_add_comm]⟩)


-- @@ L403-407 verbatim
/-!

#### B.10.2. Number of anti-chiral `L`

-/


-- @@ L409-421 verbatim
lemma reduce_numAntiChiralL_of_mem_elemsNoExotics {F : FiveQuanta 𝓩}
    (hx : F.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    F.reduce.toFluxesFive.numAntiChiralL = 0 := by
  rw [FluxesFive.numAntiChiralL, FluxesFive.chiralIndicesOfL,
    Multiset.filter_eq_nil.mpr ?_, Multiset.sum_zero]
  intro a ha
  obtain ⟨f, hf, rfl⟩ := Multiset.mem_map.mp ha
  replace hf := mem_powerset_sum_of_mem_reduce_toFluxesFive hf
  clear ha
  generalize F.toFluxesFive = G at *
  revert f
  revert G
  decide


-- @@ L423-427 verbatim
/-!

#### B.10.3. Number of chiral `D`

-/


-- @@ L429-445 verbatim
lemma reduce_numChiralD_of_mem_elemsNoExotics {F : FiveQuanta 𝓩}
    (hx : F.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    F.reduce.toFluxesFive.numChiralD = 3 := by
  have hE : F.toFluxesFive.NoExotics := ((FluxesFive.noExotics_iff_mem_elemsNoExotics _).mpr hx).1
  have hnn : ∀ a ∈ F.reduce.toFluxesFive.map (fun f => f.M), 0 ≤ a := by
    intro a ha
    obtain ⟨f, hf, rfl⟩ := Multiset.mem_map.mp ha
    replace hf := mem_powerset_sum_of_mem_reduce_toFluxesFive hf
    clear ha hE
    generalize F.toFluxesFive = G at *
    revert f
    revert G
    decide
  rw [FluxesFive.numChiralD, FluxesFive.chiralIndicesOfD, Multiset.filter_eq_self.mpr hnn,
    ← FluxesFive.chiralIndicesOfD_sum_eq_three_of_noExotics _ hE, FluxesFive.chiralIndicesOfD,
    toFluxesFive, toFluxesFive, Multiset.map_map, Multiset.map_map]
  exact reduce_sum_eq_sum_toCharges F (fun _ => ⟨⟨fun f => f.M, by simp⟩, fun x y => by simp⟩)


-- @@ L447-451 verbatim
/-!

#### B.10.4. Number of anti-chiral `D`

-/


-- @@ L453-465 verbatim
lemma reduce_numAntiChiralD_of_mem_elemsNoExotics {F : FiveQuanta 𝓩}
    (hx : F.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    F.reduce.toFluxesFive.numAntiChiralD = 0 := by
  rw [FluxesFive.numAntiChiralD, FluxesFive.chiralIndicesOfD,
    Multiset.filter_eq_nil.mpr ?_, Multiset.sum_zero]
  intro a ha
  obtain ⟨f, hf, rfl⟩ := Multiset.mem_map.mp ha
  replace hf := mem_powerset_sum_of_mem_reduce_toFluxesFive hf
  clear ha
  generalize F.toFluxesFive = G at *
  revert f
  revert G
  decide


-- @@ L467-471 verbatim
/-!

#### B.10.5. The `NoExotics` condition on the reduced `FiveQuanta`

-/

-- @@ L472-477 verbatim
lemma reduce_noExotics_of_mem_elemsNoExotics {F : FiveQuanta 𝓩}
    (hx : F.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    F.reduce.toFluxesFive.NoExotics := by
  simp [FluxesFive.NoExotics, reduce_numChiralL_of_mem_elemsNoExotics hx,
    reduce_numAntiChiralL_of_mem_elemsNoExotics hx, reduce_numChiralD_of_mem_elemsNoExotics hx,
    reduce_numAntiChiralD_of_mem_elemsNoExotics hx]


-- @@ L479-483 verbatim
/-!

### B.11. Reduce member of `FluxesFive.elemsNoExotics`

-/


-- @@ L485-493 verbatim
lemma reduce_mem_elemsNoExotics {F : FiveQuanta 𝓩}
    (hx : F.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    F.reduce.toFluxesFive ∈ FluxesFive.elemsNoExotics := by
  rw [← FluxesFive.noExotics_iff_mem_elemsNoExotics]
  refine ⟨reduce_noExotics_of_mem_elemsNoExotics hx, fun h => ?_⟩
  replace h := mem_powerset_sum_of_mem_reduce_toFluxesFive_filter h
  generalize F.toFluxesFive = G at *
  revert G
  decide


-- @@ L495-495 verbatim
end reduce


-- @@ L497-501 verbatim
/-!

## C. Decomposition of a `FiveQuanta` into basic fluxes

-/


-- @@ L503-507 verbatim
/-!

### C.1. Decomposition of fluxes

-/


-- @@ L509-512 verbatim
/-- The decomposition of a flux into `⟨1, -1⟩` and `⟨0, 1⟩`. -/
def decomposeFluxes (f : Fluxes) : Multiset Fluxes :=
  Multiset.replicate (Int.natAbs f.M) ⟨1, -1⟩ +
  Multiset.replicate (Int.natAbs (f.M + f.N)) ⟨0, 1⟩


-- @@ L514-519 verbatim
lemma decomposeFluxes_sum_of_noExotics (f : Fluxes) (hf : ∃ F ∈ FluxesFive.elemsNoExotics, f ∈ F) :
    (decomposeFluxes f).sum = f := by
  obtain ⟨F, hF, hfF⟩ := hf
  revert f
  revert F
  decide


-- @@ L521-525 verbatim
/-!

### C.2. Decomposition of a `FiveQuanta` (with no exotics)

-/


-- @@ L527-530 verbatim
/-- The decomposition of a `FiveQuanta` into a `FiveQuanta` which has the
  same `reduce` by has fluxes `⟨1, -1⟩` and `⟨0,1⟩` only. -/
def decompose (x : FiveQuanta 𝓩) : FiveQuanta 𝓩 :=
  x.bind fun p => (decomposeFluxes p.2).map fun f => (p.1, f)


-- @@ L532-536 verbatim
/-!

#### C.2.1. Decomposition distributes over addition

-/


-- @@ L538-540 verbatim
lemma decompose_add (x y : FiveQuanta 𝓩) :
    (x + y).decompose = x.decompose + y.decompose := by
  simp [decompose]


-- @@ L542-546 verbatim
/-!

#### C.2.2. Decomposition commutes with filtering charges

-/


-- @@ L548-576 verbatim
lemma decompose_filter_charge [DecidableEq 𝓩] (x : FiveQuanta 𝓩) (q : 𝓩) :
    (x.decompose).filter (fun p => p.1 = q) =
    decompose (x.filter (fun p => p.1 = q)) := by
  rw [decompose]
  revert x
  apply Multiset.induction
  · simp [decompose]
  · intro a x ih
    simp only [Multiset.cons_bind, Multiset.filter_add]
    rw [Multiset.filter_cons, decompose_add, ih]
    congr
    match a with
    | (q', f) =>
    simp [decomposeFluxes]
    by_cases h : q' = q
    · subst h
      simp [decompose, decomposeFluxes]
      congr
      all_goals
      · refine Multiset.filter_eq_self.mpr ?_
        intro a ha
        simp [Multiset.mem_replicate] at ha
        rw [ha.2]
    · simp [h, decompose]
      apply And.intro
      all_goals
      · intro a b h
        simp [Multiset.mem_replicate] at h
        simp_all


-- @@ L578-582 verbatim
/-!

#### C.2.3. Decomposition preserves the charge map

-/


-- @@ L584-598 verbatim
lemma decompose_toChargeMap [DecidableEq 𝓩] (x : FiveQuanta 𝓩)
    (hx : x.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    x.decompose.toChargeMap = x.toChargeMap := by
  ext q
  rw [toChargeMap, decompose_filter_charge]
  simp [decompose]
  rw [Multiset.map_bind]
  simp only [Multiset.map_map, Function.comp_apply, Multiset.map_id', Multiset.sum_bind]
  rw [toChargeMap]
  congr 1
  apply Multiset.map_congr
  · rfl
  intro a ha
  exact decomposeFluxes_sum_of_noExotics a.2
    ⟨x.toFluxesFive, hx, Multiset.mem_map_of_mem Prod.snd (Multiset.mem_filter.mp ha).1⟩


-- @@ L600-604 verbatim
/-!

#### C.2.4. Decomposition preserves the charges

-/


-- @@ L606-627 verbatim
lemma decompose_toCharges_dedup [DecidableEq 𝓩] (x : FiveQuanta 𝓩)
    (hx : x.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    x.decompose.toCharges.dedup = x.toCharges.dedup := by
  refine Multiset.dedup_ext.mpr ?_
  intro q
  simp [decompose, toCharges, -existsAndEq]
  constructor
  · rintro ⟨a, b, c, h1, h2, rfl⟩
    exact ⟨c, h1⟩
  · rintro ⟨c, h1⟩
    have hn : (decomposeFluxes c) ≠ 0 := by
      have c_mem_f : c ∈ x.toFluxesFive := by
        simp [toFluxesFive]
        use q
      generalize x.toFluxesFive = F at *
      clear h1
      revert c
      revert F
      decide
    apply Multiset.exists_mem_of_ne_zero at hn
    obtain ⟨c', h⟩ := hn
    use c', q, c


-- @@ L629-633 verbatim
/-!

#### C.2.5. Decomposition preserves the reduction

-/


-- @@ L635-643 verbatim
lemma decompose_reduce (x : FiveQuanta 𝓩) [DecidableEq 𝓩]
    (hx : x.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    x.decompose.reduce = x.reduce := by
  rw [reduce, reduce]
  apply Multiset.map_congr
  · rw [decompose_toCharges_dedup x hx]
  · intro q hx'
    simp only [Prod.mk.injEq, true_and]
    exact congrFun (decompose_toChargeMap x hx) q


-- @@ L645-649 verbatim
/-!

#### C.2.6. Fluxes of the decomposition of a `FiveQuanta`

-/


-- @@ L651-662 verbatim
lemma decompose_toFluxesFive (x : FiveQuanta 𝓩)
    (hx : x.toFluxesFive ∈ FluxesFive.elemsNoExotics) :
    x.decompose.toFluxesFive = {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩} := by
  rw [toFluxesFive, decompose]
  rw [Multiset.map_bind]
  simp only [Multiset.map_map, Function.comp_apply, Multiset.map_id', Int.reduceNeg,
    Multiset.insert_eq_cons]
  trans (Multiset.bind x.toFluxesFive fun a => decomposeFluxes a)
  · rw [toFluxesFive, Multiset.bind_map]
  · generalize x.toFluxesFive = F at *
    revert F
    decide


-- @@ L664-668 verbatim
/-!

## D. Lifting charges to `FiveQuanta`

-/


-- @@ L670-670 verbatim
section ofChargesExpand


-- @@ L672-672 verbatim
open SuperSymmetry.SU5.ChargeSpectrum


-- @@ L674-674 verbatim
variable [DecidableEq 𝓩]


-- @@ L676-682 verbatim
/-!

### D.1. `liftCharge c`: multiset of five-quanta for a finite set of charges `c` with no exotics

This is an efficient definition, we will later show that it gives the correct answer

-/


-- @@ L684-695 verbatim
/-- Given a finite set of charges `c` the `FiveQuanta`
  which do not have exotics, duplicate charges or zero fluxes, which map down to `c`. -/
def liftCharge (c : Finset 𝓩) : Multiset (FiveQuanta 𝓩) :=
  /- The multisets of cardinality 3 containing 3 elements of `c`. -/
  let S53 : Multiset (Multiset 𝓩) := toMultisetsThree c
  /- Pairs of multisets (s1, s2) such that s1 and s2 are cardinality of `3` containing
    elements of `c` and that all elements of `c` are in `s1 + s2`. -/
  let S5p : Multiset (Multiset 𝓩 × Multiset 𝓩) :=
    (S53 ×ˢ S53).filter fun (s1, s2) => c.val ≤ s1 + s2
  let Fp : Multiset (FiveQuanta 𝓩) :=
    S5p.map (fun y => y.1.map (fun z => (z, ⟨1, -1⟩)) + y.2.map (fun z => (z, ⟨0, 1⟩)))
  Fp.map reduce


-- @@ L697-701 verbatim
/-!

### D.2. FiveQuanta in `liftCharge c` have a finite set of charges `c`

-/


-- @@ L703-711 verbatim
lemma toCharges_toFinset_of_mem_liftCharge (c : Finset 𝓩) {x : FiveQuanta 𝓩}
    (h : x ∈ liftCharge c) : x.toCharges.toFinset = c := by
  simp [liftCharge] at h
  obtain ⟨s1, s2, ⟨⟨⟨s1_subset, s1_card⟩, ⟨s2_subset, s2_card⟩⟩, hsum⟩, rfl⟩ := h
  rw [← Multiset.toFinset_dedup, reduce_toCharges]
  simp only [Int.reduceNeg, Multiset.dedup_idem, Multiset.toFinset_dedup]
  simp [toCharges]
  refine Finset.Subset.antisymm (Finset.union_subset s1_subset s2_subset) fun a ha => ?_
  simpa using Multiset.mem_of_le hsum ha


-- @@ L713-717 verbatim
/-!

### D.3. FiveQuanta in `liftCharge c` have no duplicate charges

-/


-- @@ L719-723 verbatim
lemma toCharges_nodup_of_mem_liftCharge (c : Finset 𝓩) {x : FiveQuanta 𝓩}
    (h : x ∈ liftCharge c) : x.toCharges.Nodup := by
  rw [liftCharge, Multiset.mem_map] at h
  obtain ⟨x, h, rfl⟩ := h
  simp [reduce_toCharges]


-- @@ L725-729 verbatim
/-!

### D.4. Membership in `liftCharge c` iff is reduction of `FiveQuanta` with given fluxes

-/


-- @@ L731-745 verbatim
lemma exists_toCharges_toFluxesFive_of_mem_liftCharge (c : Finset 𝓩) {x : FiveQuanta 𝓩}
    (h : x ∈ liftCharge c) :
    ∃ a : FiveQuanta 𝓩, a.reduce = x ∧ a.toCharges.toFinset = c ∧ a.toFluxesFive =
      {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩} := by
  have h' := h
  rw [liftCharge, Multiset.mem_map] at h
  obtain ⟨a, h, rfl⟩ := h
  use a
  simp only [Int.reduceNeg, Multiset.insert_eq_cons, true_and]
  apply And.intro
  · simpa [reduce_toCharges] using toCharges_toFinset_of_mem_liftCharge c h'
  · simp at h
    obtain ⟨s1, s2, ⟨⟨⟨s1_subset, s1_card⟩, ⟨s2_subset, s2_card⟩⟩, hsum⟩, rfl⟩ := h
    simp [toFluxesFive, s1_card, s2_card]
    decide


-- @@ L747-796 verbatim
lemma mem_liftCharge_of_exists_toCharges_toFluxesFive (c : Finset 𝓩) {x : FiveQuanta 𝓩}
    (h : ∃ a : FiveQuanta 𝓩, a.reduce = x ∧ a.toCharges.toFinset = c ∧ a.toFluxesFive =
      {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩}) :
    x ∈ liftCharge c := by
  obtain ⟨x, rfl, h, h2⟩ := h
  rw [liftCharge, Multiset.mem_map]
  use x
  simp only [Int.reduceNeg, Multiset.mem_map, Multiset.mem_filter, Multiset.mem_product,
    mem_toMultisetsThree_iff, Prod.exists, and_true]
  let s1 := (x.filter (fun y => y.2 = ⟨1, -1⟩)).map Prod.fst
  let s2 := (x.filter (fun y => y.2 = ⟨0, 1⟩)).map Prod.fst
  use s1, s2
  have hcard : ∀ v : Fluxes, (x.filter (fun y => y.2 = v)).card =
      (x.toFluxesFive.filter (fun y => y = v)).card := by
    intro v
    rw [toFluxesFive, Multiset.filter_map]
    simp
  have hmap : ∀ v : Fluxes, Multiset.map (fun y => (y.1, v)) (x.filter (fun y => y.2 = v)) =
      x.filter (fun y => y.2 = v) := by
    intro v
    refine (Multiset.map_congr rfl fun y hy => ?_).trans (Multiset.map_id _)
    simp [← (Multiset.mem_filter.mp hy).2]
  have hx : Multiset.filter (fun y => y.2 = ⟨0, 1⟩) x
        = Multiset.filter (fun y => ¬ y.2 = ⟨1, -1⟩) x := by
    refine Multiset.filter_congr ?_
    intro p hp
    have h1 : p.2 ∈ x.toFluxesFive := by simp [toFluxesFive]; use p.1
    rw [h2] at h1
    simp_all
    rcases h1 with hp | hp <;> simp [hp]
  refine ⟨⟨⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩, ?_⟩, ?_⟩
  · simp [s1, ← h, toCharges]
  · simp [s1]
    rw [hcard ⟨1, -1⟩, h2]
    decide
  · simp [s2, ← h, toCharges]
  · simp [s2]
    rw [hcard ⟨0, 1⟩, h2]
    decide
  · rw [← h]
    simp [s1, s2, toCharges]
    rw [← Multiset.map_add]
    refine (Multiset.le_iff_subset (Multiset.nodup_dedup (Multiset.map Prod.fst x))).mpr ?_
    simp only [Multiset.dedup_subset']
    refine Multiset.map_subset_map ?_
    rw [hx, Multiset.filter_add_not]
    exact fun ⦃a⦄ a => a
  · simp [s1, s2]
    rw [hmap ⟨1, -1⟩, hmap ⟨0, 1⟩, hx]
    exact Multiset.filter_add_not (fun y => y.2 = ⟨1, -1⟩) x


-- @@ L798-803 verbatim
lemma mem_liftCharge_iff_exists (c : Finset 𝓩) {x : FiveQuanta 𝓩} :
    x ∈ liftCharge c ↔ ∃ a : FiveQuanta 𝓩, a.reduce = x ∧
      a.toCharges.toFinset = c ∧ a.toFluxesFive =
      {⟨1, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩} :=
  ⟨exists_toCharges_toFluxesFive_of_mem_liftCharge c,
    mem_liftCharge_of_exists_toCharges_toFluxesFive c⟩


-- @@ L805-809 verbatim
/-!

### D.5. FiveQuanta in `liftCharge c` do not have zero fluxes

-/


-- @@ L811-819 verbatim
lemma hasNoZero_of_mem_liftCharge (c : Finset 𝓩) {x : FiveQuanta 𝓩}
    (h : x ∈ liftCharge c) : x.toFluxesFive.HasNoZero := by
  rw [mem_liftCharge_iff_exists] at h
  obtain ⟨x, rfl, h1, h2⟩ := h
  intro hf
  have hx := mem_powerset_sum_of_mem_reduce_toFluxesFive_filter hf
  rw [h2] at hx
  revert hx
  decide


-- @@ L821-825 verbatim
/-!

### D.6. FiveQuanta in `liftCharge c` have no exotics

-/


-- @@ L827-834 verbatim
lemma noExotics_of_mem_liftCharge (c : Finset 𝓩) (F : FiveQuanta 𝓩)
    (h : F ∈ liftCharge c) :
    F.toFluxesFive.NoExotics := by
  rw [mem_liftCharge_iff_exists] at h
  obtain ⟨x, rfl, h1, h2⟩ := h
  apply reduce_noExotics_of_mem_elemsNoExotics
  rw [h2]
  decide


-- @@ L836-840 verbatim
/-!

### D.7. Membership in `liftCharge c` iff have no exotics, no zero fluxes, and charges `c`

-/


-- @@ L842-858 verbatim
lemma mem_liftCharge_of_mem_noExotics_hasNoZero (c : Finset 𝓩) {x : FiveQuanta 𝓩}
    (h1 : x.toFluxesFive.NoExotics) (h2 : x.toFluxesFive.HasNoZero)
    (h3 : x.toCharges.toFinset = c) (h4 : x.toCharges.Nodup) :
    x ∈ liftCharge c := by
  have hf : x.toFluxesFive ∈ FluxesFive.elemsNoExotics :=
    (FluxesFive.noExotics_iff_mem_elemsNoExotics _).mp ⟨h1, h2⟩
  rw [mem_liftCharge_iff_exists]
  use x.decompose
  apply And.intro
  · rw [decompose_reduce x hf]
    exact reduce_eq_self_of_ofCharges_nodup x h4
  · constructor
    · trans x.decompose.toCharges.dedup.toFinset
      · simp
      · rw [decompose_toCharges_dedup x hf, ← h3]
        simp
    · rw [decompose_toFluxesFive x hf]


-- @@ L860-872 verbatim
lemma mem_liftCharge_iff (c : Finset 𝓩) (x : FiveQuanta 𝓩) :
    x ∈ liftCharge c ↔ x.toFluxesFive ∈ FluxesFive.elemsNoExotics
      ∧ x.toCharges.toFinset = c ∧ x.toCharges.Nodup := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · rw [← FluxesFive.noExotics_iff_mem_elemsNoExotics]
      exact ⟨noExotics_of_mem_liftCharge c x h, hasNoZero_of_mem_liftCharge c h⟩
    · exact toCharges_toFinset_of_mem_liftCharge c h
    · exact toCharges_nodup_of_mem_liftCharge c h
  · intro ⟨h1, h2, h3⟩
    rw [← FluxesFive.noExotics_iff_mem_elemsNoExotics] at h1
    exact mem_liftCharge_of_mem_noExotics_hasNoZero c h1.1 h1.2 h2 h3


-- @@ L874-878 verbatim
/-!

### D.8. `liftCharge c` is preserved under a map if reduced

-/


-- @@ L880-889 verbatim
lemma map_liftCharge {𝓩 𝓩1 : Type}[DecidableEq 𝓩] [DecidableEq 𝓩1] [CommRing 𝓩] [CommRing 𝓩1]
    (f : 𝓩 →+* 𝓩1) (c : Finset 𝓩) (F : FiveQuanta 𝓩) (h : F ∈ liftCharge c) :
    FiveQuanta.reduce (F.map fun y => (f y.1, y.2)) ∈ liftCharge (c.image f) := by
  rw [mem_liftCharge_iff] at h ⊢
  refine ⟨?_, ?_, ?_⟩
  · apply reduce_mem_elemsNoExotics
    simpa [toFluxesFive, Multiset.map_map] using h.1
  · rw [reduce_toCharges]
    simp [← h.2.1, ← Multiset.toFinset_map, toCharges]
  · simp [reduce_toCharges]


-- @@ L891-891 verbatim
end ofChargesExpand


-- @@ L893-897 verbatim
/-!

## E. Anomaly cancellation coefficients

-/


-- @@ L899-899 verbatim
section ACCs


-- @@ L901-901 verbatim
variable [CommRing 𝓩]


-- @@ L903-907 verbatim
/-!

### E.1. Anomaly coefficients of a `FiveQuanta`

-/


-- @@ L909-918 verbatim
/--
  The anomaly coefficient of a `FiveQuanta` is given by the pair of integers:
  `(∑ᵢ qᵢ Nᵢ, ∑ᵢ qᵢ² Nᵢ)`.

  The first components is for the mixed U(1)-MSSM, see equation (22) of arXiv:1401.5084
  [ref: arxiv_1401_5084]. The second component is for the mixed U(1)Y-U(1)-U(1) gauge anomaly,
  see equation (23) of arXiv:1401.5084 [ref: arxiv_1401_5084].
-/
def anomalyCoefficient (F : FiveQuanta 𝓩) : 𝓩 × 𝓩 :=
  ((F.map fun x => x.2.2 • x.1).sum, (F.map fun x => x.2.2 • (x.1 * x.1)).sum)


-- @@ L920-924 verbatim
/-!

### E.2. Anomaly coefficients under a map

-/


-- @@ L926-931 verbatim
@[simp]
lemma anomalyCoefficient_of_map {𝓩 𝓩1 : Type} [CommRing 𝓩] [CommRing 𝓩1]
    (f : 𝓩 →+* 𝓩1) (F : FiveQuanta 𝓩) :
    FiveQuanta.anomalyCoefficient (F.map fun y => (f y.1, y.2) : FiveQuanta 𝓩1) =
    (f.prodMap f) F.anomalyCoefficient := by
  simp [FiveQuanta.anomalyCoefficient, map_multiset_sum, Multiset.map_map]


-- @@ L933-937 verbatim
/-!

### E.3. Anomaly coefficients is preserved under `reduce`

-/


-- @@ L939-952 verbatim
lemma anomalyCoefficient_of_reduce (F : FiveQuanta 𝓩) [DecidableEq 𝓩] :
    F.reduce.anomalyCoefficient = F.anomalyCoefficient := by
  have reduce_sum_N_mul_eq : ∀ h : 𝓩 → 𝓩, (F.reduce.map fun x => (x.2.N : 𝓩) * h x.1).sum =
      (F.map fun x => (x.2.N : 𝓩) * h x.1).sum := by
    intro h
    let f : 𝓩 → Fluxes →+ 𝓩 := fun q5 =>
      { toFun := fun x => x.N • h q5
        map_zero' := by simp
        map_add' := by
          intros x y
          simp [add_mul] }
    simpa [f] using reduce_sum_eq_sum_toCharges F f
  simp [anomalyCoefficient]
  exact ⟨reduce_sum_N_mul_eq fun q => q, reduce_sum_N_mul_eq fun q => q * q⟩


-- @@ L954-954 verbatim
end ACCs


-- @@ L956-956 verbatim
end FiveQuanta


-- @@ L958-958 verbatim
end SU5

-- @@ L959-959 verbatim
end FTheory
