import OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileParents


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped Classical BigOperators SchwartzMap

-- @@ L7-7 verbatim
namespace SevenEighths.InverseMomentFirstOriginalProfile

-- @@ L8-8 verbatim
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic

-- @@ L9-9 verbatim
open InverseMomentFirstChildWindows

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
variable {ι : Type*} [DecidableEq ι]

-- @@ L12-12 verbatim
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]


-- @@ L14-16 verbatim
def refinedOuter (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex)
    (gate : FirstOriginalOuter ι→Prop) : Finset (FirstOriginalOuter ι) :=
  (originalOuterCell p pool Q k).filter gate


-- @@ L18-23 verbatim
def refinedSource (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Y : ℝ) (k : SourceIndex) (gate : FirstOriginalOuter ι→Prop) : Finset (OriginalIndex ι) :=
  (sourceCell (originalNorms p)
    (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k).filter
      (fun x=>gate x.1 ∧ firstOriginalWeight p β cutoff x.1 x.2≠0)


-- @@ L25-31 verbatim
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma refinedSource_subset (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Y : ℝ) (k : SourceIndex) (gate : FirstOriginalOuter ι→Prop) :
    refinedSource p pool Q labels β cutoff Y k gate⊆sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k :=
  Finset.filter_subset _ _


-- @@ L33-39 verbatim
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma original_weight_frequency (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (x : OriginalIndex ι) (hx : firstOriginalWeight p β cutoff x.1 x.2≠0) :
    x.2.2∈reopenedPhysicalCutoff p x.1.1 x.2.1 (cutoff x.1.1 x.1.2.1 x.2.1) x.1.2.2 := by
  by_contra hh
  exact hx (by simp [firstOriginalWeight,hh])


-- @@ L41-63 verbatim
theorem refined_source_radius (hp : ∀i,p i≠0)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ysource Ychild : ℝ) (k : SourceIndex) (gate : FirstOriginalOuter ι→Prop)
    (hn : ∀I∈labels,I≠0)
    (hcut : ∀x∈refinedOuter p pool Q k gate,∀I∈labels,cutoff x.1 x.2.1 I x.2.2≤Ychild) :
    refinedSource p pool Q labels β cutoff Ysource k gate⊆
      firstGlobalRetainedSource p (refinedOuter p pool Q k gate) (fun _=>labels) (fun x=>x.1) Ychild := by
  intro x hx
  obtain ⟨hxcell,hgate,hweight⟩ := Finset.mem_filter.mp hx
  have hxold := original_cell_subset p pool Q labels Ysource k hxcell
  obtain ⟨ho,hf⟩ := Finset.mem_sigma.mp hxold
  have hm := (mem_firstRetainedSource p labels x.1.1 Ysource x.2).mp hf
  have houter : x.1∈refinedOuter p pool Q k gate := Finset.mem_filter.mpr ⟨ho,hgate⟩
  have hE := firstPhysicalMultiplier_ne_zero p hp x.1.1.support x.1.1.leftExponent x.1.1.rightExponent
    x.1.1.leftBit x.1.1.rightBit x.2.1 (hn x.2.1 hm.1)
  apply Finset.mem_sigma.mpr
  refine ⟨houter,(mem_firstRetainedSource p labels x.1.1 Ychild x.2).mpr ⟨hm.1,?_⟩⟩
  apply Finset.mem_erase.mpr
  refine ⟨(Finset.mem_erase.mp hm.2).1,?_⟩
  apply (mem_childFrequencyBall _ hE Ychild x.2.2).mpr
  exact ((mem_childFrequencyBall _ hE _ x.2.2).mp
    (original_weight_frequency p β cutoff x hweight)).trans (hcut x.1 houter x.2.1 hm.1)


-- @@ L65-66 verbatim
def labelGate (j : ℕ) (x : FirstOriginalOuter ι) : Prop :=
  InverseSecondSourceBlocks.dyadIndex (InverseFirstGlobalCaps.jNorm p x)=j


-- @@ L68-75 verbatim
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma refinedOuter_label (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (j : ℕ) :
    refinedOuter p pool Q k (labelGate p j)=
      (InverseFirstGlobalCaps.outerCell p pool Q k).filter
        (fun x=>InverseSecondSourceBlocks.dyadIndex (InverseFirstGlobalCaps.jNorm p x)=j) := by
  rw [refinedOuter,originalOuterCell_eq_caps]
  ext x
  simp [labelGate]


-- @@ L77-77 verbatim
end SevenEighths.InverseMomentFirstOriginalProfile

-- @@ L78-78 verbatim
end


-- @@ L80-80 verbatim
end OAI
