/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Formalisation.HansenCograph.HDAFinite


-- @@ L8-16 verbatim
/-!
# Section-weight operation kernels for the cograph HDA tensor

The raw `sectionWeight` array has polynomial binomial kernels under cotree
operations.  This module proves those one-section identities without relying
on private implementation details of the existing `q` operation proofs.  They
are the normalization layer needed before the coupled deletion tensor can be
reindexed at a cotree node.
-/


-- @@ L18-18 verbatim
open scoped BigOperators Pointwise

-- @@ L19-19 verbatim
open Set

-- @@ L20-20 verbatim
open MeasureTheory

-- @@ L21-21 verbatim
open SimpleGraph


-- @@ L23-23 verbatim
universe u v


-- @@ L25-25 verbatim
namespace HansenCograph


-- @@ L27-27 verbatim
section SectionWeightKernels


-- @@ L29-29 verbatim
variable {V : Type u} {W : Type v}

-- @@ L30-30 verbatim
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


-- @@ L32-35 verbatim
/-- The raw-section kernel for a disjoint union. -/
noncomputable def sumSectionKernel (a b i j : ℕ) : ℝ :=
  (Nat.choose (i + j) i : ℝ) *
    (Nat.choose ((a - i) + (b - j)) (a - i) : ℝ)


-- @@ L37-38 verbatim
/-- The raw-section kernel for a graph join. -/
noncomputable def joinSectionKernel (_a _b _i _j : ℕ) : ℝ := 1


-- @@ L40-47 verbatim
/-- The cardinality of a `sumFinset` is the sum of the component cardinalities. -/
@[simp]
theorem card_sumFinset_hda (s : Finset V) (t : Finset W) :
    (sumFinset s t).card = s.card + t.card := by
  unfold sumFinset
  rw [Finset.card_union_of_disjoint]
  · simp
  · simp [Finset.disjoint_left]


-- @@ L49-53 verbatim
/-- Complementation commutes with `sumFinset` on the common sum carrier. -/
theorem compl_sumFinset_hda (s : Finset V) (t : Finset W) :
    (sumFinset s t)ᶜ = sumFinset sᶜ tᶜ := by
  ext z
  cases z <;> simp


-- @@ L55-65 verbatim
/-- A raw section weight is its normalized coefficient times its factorial mass. -/
theorem sectionWeight_eq_qCoeff_mul_factorials
    (G : SimpleGraph V) (s : Finset V) :
    sectionWeight G s =
      qCoeff G s *
        ((s.card.factorial : ℝ) *
          ((Fintype.card V - s.card).factorial : ℝ)) := by
  unfold sectionWeight qCoeff
  have hleft : (s.card.factorial : ℝ) ≠ 0 := by positivity
  have hright : ((Fintype.card V - s.card).factorial : ℝ) ≠ 0 := by positivity
  field_simp [hleft, hright]


-- @@ L67-98 verbatim
/--
The unnormalised section weight of a union factors with the two binomial
selection kernels, one for the selected set and one for its complement.
-/
theorem sectionWeight_sumFinset
    (A : SimpleGraph V) (B : SimpleGraph W)
    (s : Finset V) (t : Finset W) :
    sectionWeight (A ⊕g B) (sumFinset s t) =
      sumSectionKernel (Fintype.card V) (Fintype.card W) s.card t.card *
        sectionWeight A s * sectionWeight B t := by
  classical
  have hsle : s.card ≤ Fintype.card V := Finset.card_le_univ s
  have htle : t.card ≤ Fintype.card W := Finset.card_le_univ t
  have hremaining :
      Fintype.card V + Fintype.card W - (s.card + t.card) =
        (Fintype.card V - s.card) + (Fintype.card W - t.card) := by
    omega
  have hfac (a b : ℕ) :
      (((a + b).factorial : ℕ) : ℝ) =
        (Nat.choose (a + b) a : ℝ) * a.factorial * b.factorial := by
    norm_cast
    simpa using
      (Nat.choose_mul_factorial_mul_factorial
        (show a ≤ a + b by omega)).symm
  rw [sectionWeight_eq_qCoeff_mul_factorials (A ⊕g B) (sumFinset s t)]
  rw [qCoeff_sumFinset, card_sumFinset_hda, Fintype.card_sum, hremaining,
    hfac s.card t.card,
    hfac (Fintype.card V - s.card) (Fintype.card W - t.card)]
  rw [sectionWeight_eq_qCoeff_mul_factorials A s,
    sectionWeight_eq_qCoeff_mul_factorials B t]
  unfold sumSectionKernel
  ring


-- @@ L100-135 expanded
/-- The unnormalised section weight of a join has unit kernel: both selected and
complementary induced volumes factor by `nu_join` without a binomial term.
-/
theorem sectionWeight_joinFinset (A : SimpleGraph V) (B : SimpleGraph W) (s : Finset V)
    (t : Finset W) :
    sectionWeight (graphJoin A B) (sumFinset s t) =
      joinSectionKernel (Fintype.card V) (Fintype.card W) s.card t.card * sectionWeight A s *
        sectionWeight B t :=
  by
  classical
  have hsle : s.card ≤ Fintype.card V := Finset.card_le_univ s
  have htle : t.card ≤ Fintype.card W := Finset.card_le_univ t
  have hremaining :
    Fintype.card V + Fintype.card W - (s.card + t.card) =
      (Fintype.card V - s.card) + (Fintype.card W - t.card) :=
    by omega
  have hfac (a b : ℕ) :
    (((a + b).factorial : ℕ) : ℝ) = (Nat.choose (a + b) a : ℝ) * a.factorial * b.factorial :=
    by
    norm_cast
    simpa using (Nat.choose_mul_factorial_mul_factorial (show a ≤ a + b by omega)).symm
  have hchoose (a b : ℕ) : (Nat.choose (a + b) a : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.choose_pos (by omega : a ≤ a + b)))
  rw [sectionWeight_eq_qCoeff_mul_factorials (graphJoin A B) (sumFinset s t)]
  rw [qCoeff_joinFinset, card_sumFinset_hda, Fintype.card_sum, hremaining, hfac s.card t.card,
    hfac (Fintype.card V - s.card) (Fintype.card W - t.card)]
  rw [sectionWeight_eq_qCoeff_mul_factorials A s, sectionWeight_eq_qCoeff_mul_factorials B t]
  unfold joinSectionKernel
  field_simp [hchoose s.card t.card,
      hchoose (Fintype.card V - s.card) (Fintype.card W - t.card)] <;>
    ring


-- @@ L137-137 verbatim
end SectionWeightKernels


-- @@ L139-139 verbatim
section PowersetCardReindexing


-- @@ L141-141 verbatim
variable {V : Type u} {W : Type v}

-- @@ L142-142 verbatim
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


-- @@ L144-148 verbatim
/-- Taking the left part after `sumFinset` recovers the left input finset. -/
theorem sumLeftPart_sumFinset_hda (s : Finset V) (t : Finset W) :
    sumLeftPart (sumFinset s t) = s := by
  ext v
  simp


-- @@ L150-154 verbatim
/-- Taking the right part after `sumFinset` recovers the right input finset. -/
theorem sumRightPart_sumFinset_hda (s : Finset V) (t : Finset W) :
    sumRightPart (sumFinset s t) = t := by
  ext w
  simp


-- @@ L156-160 verbatim
/-- Splitting a finite set of sum vertices and recombining its two parts is exact. -/
theorem sumFinset_parts_hda (s : Finset (V ⊕ W)) :
    sumFinset (sumLeftPart s) (sumRightPart s) = s := by
  ext z
  cases z <;> simp


-- @@ L162-202 verbatim
/--
Reindex one cardinality fibre of the powerset of a sum type by the two
component powersets, retaining the exact cardinality equation as a filter.
This is the finite bijection needed to turn the section-weight kernels into a
tensor recurrence.
-/
theorem sum_powersetCard_sumFinset_filter
    (p : ℕ) (f : Finset (V ⊕ W) → ℝ) :
    ∑ u ∈ (Finset.univ : Finset (V ⊕ W)).powersetCard p, f u =
      ∑ st ∈
          (((Finset.univ : Finset V).powerset ×ˢ
            (Finset.univ : Finset W).powerset).filter
              (fun st => st.1.card + st.2.card = p)),
        f (sumFinset st.1 st.2) := by
  classical
  apply Finset.sum_bij (fun u _ => (sumLeftPart u, sumRightPart u))
  · intro u hu
    refine Finset.mem_filter.mpr ⟨by simp, ?_⟩
    calc
      (sumLeftPart u).card + (sumRightPart u).card =
          (sumFinset (sumLeftPart u) (sumRightPart u)).card :=
        (card_sumFinset_hda _ _).symm
      _ = u.card := congrArg Finset.card (sumFinset_parts_hda u)
      _ = p := (Finset.mem_powersetCard.mp hu).2
  · intro u₁ hu₁ u₂ hu₂ h
    have hleft : sumLeftPart u₁ = sumLeftPart u₂ := congrArg Prod.fst h
    have hright : sumRightPart u₁ = sumRightPart u₂ := congrArg Prod.snd h
    calc
      u₁ = sumFinset (sumLeftPart u₁) (sumRightPart u₁) :=
        (sumFinset_parts_hda u₁).symm
      _ = sumFinset (sumLeftPart u₂) (sumRightPart u₂) := by
        rw [hleft, hright]
      _ = u₂ := sumFinset_parts_hda u₂
  · rintro ⟨s, t⟩ hst
    have hmem := Finset.mem_filter.mp hst
    refine ⟨sumFinset s t, ?_, ?_⟩
    · refine Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩
      simpa [card_sumFinset_hda] using hmem.2
    · simp [sumLeftPart_sumFinset_hda, sumRightPart_sumFinset_hda]
  · intro u hu
    rw [sumFinset_parts_hda]


-- @@ L204-215 verbatim
/--
The finite sigma-index used to regroup filtered pairs of subsets by their two
cardinalities.  Its second component is a pair of exact powerset-card fibres.
-/
noncomputable def cardFiberPairs (p : ℕ) :
    Finset (Σ _ij : ℕ × ℕ, Finset V × Finset W) :=
  (((Finset.range (Fintype.card V + 1) ×ˢ
      Finset.range (Fintype.card W + 1)).filter
      (fun ij => ij.1 + ij.2 = p)).sigma
    (fun ij =>
      (Finset.univ : Finset V).powersetCard ij.1 ×ˢ
        (Finset.univ : Finset W).powersetCard ij.2))


-- @@ L217-262 verbatim
/--
Regroup a filtered pair of arbitrary component subsets by its exact pair of
cardinalities.  This is the remaining finite reindexing step between the
filter expansions and the `dArray` convolutions.
-/
theorem filtered_pair_sum_eq_cardFiberPairs
    (p : ℕ) (f : Finset V → Finset W → ℝ) :
    ∑ st ∈
        (((Finset.univ : Finset V).powerset ×ˢ
          (Finset.univ : Finset W).powerset).filter
            (fun st => st.1.card + st.2.card = p)),
      f st.1 st.2 =
      ∑ z ∈ cardFiberPairs (V := V) (W := W) p, f z.2.1 z.2.2 := by
  classical
  unfold cardFiberPairs
  apply Finset.sum_bij (fun st _ => ⟨(st.1.card, st.2.card), st⟩)
  · intro st hst
    rcases Finset.mem_filter.mp hst with ⟨hstmem, hcard⟩
    refine Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨?_, hcard⟩, ?_⟩
    · refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · exact Finset.mem_range.mpr
          (Nat.lt_succ_of_le (Finset.card_le_univ st.1))
      · exact Finset.mem_range.mpr
          (Nat.lt_succ_of_le (Finset.card_le_univ st.2))
    · exact Finset.mem_product.mpr ⟨
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩,
        Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, rfl⟩⟩
  · intro st₁ hst₁ st₂ hst₂ h
    exact eq_of_heq (Sigma.mk.inj_iff.mp h).2
  · rintro ⟨ij, st⟩ h
    rcases ij with ⟨i, j⟩
    rcases Finset.mem_sigma.mp h with ⟨hij, hst⟩
    rcases Finset.mem_filter.mp hij with ⟨hijrange, hijcard⟩
    rcases Finset.mem_product.mp hst with ⟨hs, ht⟩
    refine ⟨st, Finset.mem_filter.mpr ⟨?_, ?_⟩, ?_⟩
    · refine Finset.mem_product.mpr ⟨?_, ?_⟩
      · simpa using (Finset.mem_powersetCard.mp hs).1
      · simpa using (Finset.mem_powersetCard.mp ht).1
    · have hscard : st.1.card = i := (Finset.mem_powersetCard.mp hs).2
      have htcard : st.2.card = j := (Finset.mem_powersetCard.mp ht).2
      simpa [hscard, htcard] using hijcard
    · have hscard : st.1.card = i := (Finset.mem_powersetCard.mp hs).2
      have htcard : st.2.card = j := (Finset.mem_powersetCard.mp ht).2
      simp [hscard, htcard]
  · intro st hst
    rfl


-- @@ L264-264 verbatim
end PowersetCardReindexing


-- @@ L266-266 verbatim
section DArrayKernelExpansions


-- @@ L268-268 verbatim
variable {V : Type u} {W : Type v}

-- @@ L269-269 verbatim
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


-- @@ L271-320 verbatim
/--
Factor a finite product of exact cardinality fibres into the two `dArray`
entries.  The kernel is allowed to depend on the concrete subset cardinalities
so the membership equations of `powersetCard` are used explicitly.
-/
theorem cardinal_fiber_product_factor
    (A : SimpleGraph V) (B : SimpleGraph W) (κ : ℕ → ℕ → ℝ)
    (i j : ℕ) :
    ∑ s ∈ (Finset.univ : Finset V).powersetCard i,
      ∑ t ∈ (Finset.univ : Finset W).powersetCard j,
        κ s.card t.card * sectionWeight A s * sectionWeight B t =
      κ i j * dArray A i * dArray B j := by
  classical
  calc
    ∑ s ∈ (Finset.univ : Finset V).powersetCard i,
        ∑ t ∈ (Finset.univ : Finset W).powersetCard j,
          κ s.card t.card * sectionWeight A s * sectionWeight B t =
        ∑ s ∈ (Finset.univ : Finset V).powersetCard i,
          ∑ t ∈ (Finset.univ : Finset W).powersetCard j,
            κ i j * sectionWeight A s * sectionWeight B t := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro t ht
      have hscard : s.card = i := (Finset.mem_powersetCard.mp hs).2
      have htcard : t.card = j := (Finset.mem_powersetCard.mp ht).2
      simp [hscard, htcard]
    _ = ∑ s ∈ (Finset.univ : Finset V).powersetCard i,
          (κ i j * sectionWeight A s) *
            ∑ t ∈ (Finset.univ : Finset W).powersetCard j,
              sectionWeight B t := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.mul_sum]
    _ = ∑ s ∈ (Finset.univ : Finset V).powersetCard i,
          (κ i j *
            ∑ t ∈ (Finset.univ : Finset W).powersetCard j,
              sectionWeight B t) * sectionWeight A s := by
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ = (κ i j *
          ∑ t ∈ (Finset.univ : Finset W).powersetCard j,
            sectionWeight B t) *
          ∑ s ∈ (Finset.univ : Finset V).powersetCard i,
            sectionWeight A s := by
      rw [← Finset.mul_sum]
    _ = κ i j * dArray A i * dArray B j := by
      unfold dArray
      ring


-- @@ L322-342 verbatim
/--
The exact raw-section expansion of one `dArray` fibre under disjoint union.
The components are still indexed by concrete finsets; the next regrouping
step will package them as the cardinal arrays `dArray A` and `dArray B`.
-/
theorem dArray_sum_filter_expansion
    (A : SimpleGraph V) (B : SimpleGraph W) (p : ℕ) :
    dArray (A ⊕g B) p =
      ∑ st ∈
          (((Finset.univ : Finset V).powerset ×ˢ
            (Finset.univ : Finset W).powerset).filter
              (fun st => st.1.card + st.2.card = p)),
        sumSectionKernel (Fintype.card V) (Fintype.card W)
            st.1.card st.2.card *
          sectionWeight A st.1 * sectionWeight B st.2 := by
  classical
  unfold dArray
  rw [sum_powersetCard_sumFinset_filter]
  apply Finset.sum_congr rfl
  intro st hst
  rw [sectionWeight_sumFinset]


-- @@ L344-363 expanded
/-- The exact raw-section expansion of one `dArray` fibre under graph join.
The join kernel is explicitly retained, even though it reduces to one.
-/
theorem dArray_join_filter_expansion (A : SimpleGraph V) (B : SimpleGraph W) (p : ℕ) :
    dArray (graphJoin A B) p =
      ∑
        st ∈
          (((Finset.univ : Finset V).powerset ×ˢ (Finset.univ : Finset W).powerset).filter
            (fun st => st.1.card + st.2.card = p)),
        joinSectionKernel (Fintype.card V) (Fintype.card W) st.1.card st.2.card *
            sectionWeight A st.1 *
          sectionWeight B st.2 :=
  by
  classical
  unfold dArray
  rw [sum_powersetCard_sumFinset_filter]
  apply Finset.sum_congr rfl
  intro st hst
  rw [sectionWeight_joinFinset]


-- @@ L365-373 verbatim
/-- The finite cardinal-array convolution target for a disjoint union. -/
noncomputable def sumDArrayRhs
    (A : SimpleGraph V) (B : SimpleGraph W) (p : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (Fintype.card V + 1),
    ∑ j ∈ Finset.range (Fintype.card W + 1),
      if i + j = p then
        sumSectionKernel (Fintype.card V) (Fintype.card W) i j *
          dArray A i * dArray B j
      else 0


-- @@ L375-383 verbatim
/-- The finite cardinal-array convolution target for a graph join. -/
noncomputable def joinDArrayRhs
    (A : SimpleGraph V) (B : SimpleGraph W) (p : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (Fintype.card V + 1),
    ∑ j ∈ Finset.range (Fintype.card W + 1),
      if i + j = p then
        joinSectionKernel (Fintype.card V) (Fintype.card W) i j *
          dArray A i * dArray B j
      else 0


-- @@ L385-409 verbatim
/-- The exact cardinal-array convolution for a disjoint union. -/
theorem dArray_sum
    (A : SimpleGraph V) (B : SimpleGraph W) (p : ℕ) :
    dArray (A ⊕g B) p = sumDArrayRhs A B p := by
  classical
  unfold sumDArrayRhs
  rw [dArray_sum_filter_expansion]
  rw [filtered_pair_sum_eq_cardFiberPairs
    (V := V) (W := W) p
    (fun s t =>
      sumSectionKernel (Fintype.card V) (Fintype.card W) s.card t.card *
        sectionWeight A s * sectionWeight B t)]
  unfold cardFiberPairs
  rw [Finset.sum_sigma]
  simp_rw [Finset.sum_product]
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : i + j = p
  · simpa only [if_pos h, Prod.fst, Prod.snd] using
      (cardinal_fiber_product_factor A B
        (sumSectionKernel (Fintype.card V) (Fintype.card W)) i j)
  · simp [h]


-- @@ L411-435 expanded
/-- The exact cardinal-array convolution for a graph join. -/
theorem dArray_join (A : SimpleGraph V) (B : SimpleGraph W) (p : ℕ) :
    dArray (graphJoin A B) p = joinDArrayRhs A B p := by
  classical
  unfold joinDArrayRhs
  rw [dArray_join_filter_expansion]
  rw [filtered_pair_sum_eq_cardFiberPairs (V := V) (W := W) p
      (fun s t =>
        joinSectionKernel (Fintype.card V) (Fintype.card W) s.card t.card * sectionWeight A s *
          sectionWeight B t)]
  unfold cardFiberPairs
  rw [Finset.sum_sigma]
  simp_rw [Finset.sum_product]
  rw [Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : i + j = p
  ·
    simpa only [if_pos h, Prod.fst, Prod.snd] using
      (cardinal_fiber_product_factor A B (joinSectionKernel (Fintype.card V) (Fintype.card W)) i j)
  · simp [h]


-- @@ L437-443 verbatim
/-!
The one-array operation kernels are now stated as `dArray_sum` and
`dArray_join`.  The coupled tensor recurrence uses these exact finite
convolutions after transport along the four deletion graph isomorphisms.  Its
only additional reindexing is a Fubini interchange between the deleted vertex
and these bounded cardinality fibres.
-/


-- @@ L445-445 verbatim
end DArrayKernelExpansions


-- @@ L447-447 verbatim
section TensorRecurrenceTargets


-- @@ L449-449 verbatim
variable {V : Type u} {W : Type v}

-- @@ L450-450 verbatim
variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]


-- @@ L452-457 verbatim
/-- Transport the left union deletion array across its explicit graph isomorphism. -/
theorem dArray_delete_sum_inl
    (A : SimpleGraph V) (B : SimpleGraph W) (x : V) (i : ℕ) :
    dArray (deleteVertex (A ⊕g B) (Sum.inl x)) i =
      dArray (deleteVertex A x ⊕g B) i :=
  dArray_iso (deleteVertex_sum_inl_iso A B x) i


-- @@ L459-464 verbatim
/-- Transport the right union deletion array across its explicit graph isomorphism. -/
theorem dArray_delete_sum_inr
    (A : SimpleGraph V) (B : SimpleGraph W) (y : W) (i : ℕ) :
    dArray (deleteVertex (A ⊕g B) (Sum.inr y)) i =
      dArray (A ⊕g deleteVertex B y) i :=
  dArray_iso (deleteVertex_sum_inr_iso A B y) i


-- @@ L466-471 expanded
/-- Transport the left join deletion array across its explicit graph isomorphism. -/
theorem dArray_delete_join_inl (A : SimpleGraph V) (B : SimpleGraph W) (x : V) (i : ℕ) :
    dArray (deleteVertex (graphJoin A B) (Sum.inl x)) i =
      dArray (graphJoin (deleteVertex A x) B) i :=
  dArray_iso (deleteVertex_join_inl_iso A B x) i


-- @@ L473-478 expanded
/-- Transport the right join deletion array across its explicit graph isomorphism. -/
theorem dArray_delete_join_inr (A : SimpleGraph V) (B : SimpleGraph W) (y : W) (i : ℕ) :
    dArray (deleteVertex (graphJoin A B) (Sum.inr y)) i =
      dArray (graphJoin A (deleteVertex B y)) i :=
  dArray_iso (deleteVertex_join_inr_iso A B y) i


-- @@ L480-495 verbatim
/--
The left-summand contribution to the coupled deletion tensor of a union.
The two finite equality tests implement the equations `i + j = p` and
`h + k = r` without any subtraction transport.
-/
noncomputable def sumDeletionTensorLeft
    (A : SimpleGraph V) (B : SimpleGraph W) (p r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (Fintype.card V),
    ∑ h ∈ Finset.range (Fintype.card V),
      ∑ j ∈ Finset.range (Fintype.card W + 1),
        ∑ k ∈ Finset.range (Fintype.card W + 1),
          if i + j = p ∧ h + k = r then
            deletionTensor A i h * dArray B j * dArray Bᶜ k *
              sumSectionKernel (Fintype.card V - 1) (Fintype.card W) i j *
              joinSectionKernel (Fintype.card V - 1) (Fintype.card W) h k
          else 0


-- @@ L497-508 verbatim
/-- The right-summand contribution to the coupled deletion tensor of a union. -/
noncomputable def sumDeletionTensorRight
    (A : SimpleGraph V) (B : SimpleGraph W) (p r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (Fintype.card V + 1),
    ∑ h ∈ Finset.range (Fintype.card V + 1),
      ∑ j ∈ Finset.range (Fintype.card W),
        ∑ k ∈ Finset.range (Fintype.card W),
          if i + j = p ∧ h + k = r then
            dArray A i * dArray Aᶜ h * deletionTensor B j k *
              sumSectionKernel (Fintype.card V) (Fintype.card W - 1) i j *
              joinSectionKernel (Fintype.card V) (Fintype.card W - 1) h k
          else 0


-- @@ L510-513 verbatim
/-- The explicit finite target for the union deletion-tensor recurrence. -/
noncomputable def sumDeletionTensorRhs
    (A : SimpleGraph V) (B : SimpleGraph W) (p r : ℕ) : ℝ :=
  sumDeletionTensorLeft A B p r + sumDeletionTensorRight A B p r


-- @@ L515-529 verbatim
/--
The left-summand contribution to the coupled deletion tensor of a join.
Only the selected/complementary kernels are exchanged relative to union.
-/
noncomputable def joinDeletionTensorLeft
    (A : SimpleGraph V) (B : SimpleGraph W) (p r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (Fintype.card V),
    ∑ h ∈ Finset.range (Fintype.card V),
      ∑ j ∈ Finset.range (Fintype.card W + 1),
        ∑ k ∈ Finset.range (Fintype.card W + 1),
          if i + j = p ∧ h + k = r then
            deletionTensor A i h * dArray B j * dArray Bᶜ k *
              joinSectionKernel (Fintype.card V - 1) (Fintype.card W) i j *
              sumSectionKernel (Fintype.card V - 1) (Fintype.card W) h k
          else 0


-- @@ L531-542 verbatim
/-- The right-summand contribution to the coupled deletion tensor of a join. -/
noncomputable def joinDeletionTensorRight
    (A : SimpleGraph V) (B : SimpleGraph W) (p r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (Fintype.card V + 1),
    ∑ h ∈ Finset.range (Fintype.card V + 1),
      ∑ j ∈ Finset.range (Fintype.card W),
        ∑ k ∈ Finset.range (Fintype.card W),
          if i + j = p ∧ h + k = r then
            dArray A i * dArray Aᶜ h * deletionTensor B j k *
              joinSectionKernel (Fintype.card V) (Fintype.card W - 1) i j *
              sumSectionKernel (Fintype.card V) (Fintype.card W - 1) h k
          else 0


-- @@ L544-547 verbatim
/-- The explicit finite target for the join deletion-tensor recurrence. -/
noncomputable def joinDeletionTensorRhs
    (A : SimpleGraph V) (B : SimpleGraph W) (p r : ℕ) : ℝ :=
  joinDeletionTensorLeft A B p r + joinDeletionTensorRight A B p r


-- @@ L549-562 verbatim
/-!
The next theorems are intentionally not declared until the reindexing maps
between `powersetCard` fibres of `sumFinset` are present as public lemmas:

```
deletionTensor (A ⊕g B) p r = sumDeletionTensorRhs A B p r
deletionTensor (A ⊗g B) p r = joinDeletionTensorRhs A B p r
```

The four `deleteVertex_*_iso` maps in `HDADelete` resolve the graph carrier
transport.  The remaining formal blocker is a cardinality-preserving
`Finset.sum_bij` between a `powersetCard` fibre of `sumFinset` and its two
component fibres, including the `i + j = p` equality encoded above.
-/


-- @@ L564-564 verbatim
end TensorRecurrenceTargets


-- @@ L566-566 verbatim
end HansenCograph
