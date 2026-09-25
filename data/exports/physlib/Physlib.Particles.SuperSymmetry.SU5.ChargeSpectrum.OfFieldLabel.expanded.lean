/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.Particles.SuperSymmetry.SU5.ChargeSpectrum.Basic
public import Physlib.Particles.SuperSymmetry.SU5.FieldLabels

-- @@ L10-42 verbatim
/-!

# Charges associated with a field label

## i. Overview

Recall that a `FieldLabel` is one of the seven possible superfields in the SU(5) GUT,
corresponding to the fields present and their conjugates.

Given a charge spectrum `x : ChargeSpectrum 𝓩`, we are interested in the finite set of
charges carried by representations associated with a given `FieldLabel`.

Results in this module will be used to find the charges associated with
terms in the potential.

## ii. Key results

- `ofFieldLabel` : Given a charge spectrum `x : ChargeSpectrum 𝓩`,
  `ofFieldLabel x F` is the finite set of charges associated with representations
  corresponding to the field label `F`.

## iii. Table of contents

- A. Charges associated with a field label
  - A.1. The field labels for the empty charge spectrum
  - A.2. Monotonicity of `ofFieldLabel`
  - A.3. Membership of conjugate charges
  - A.4. Extensionality of charge spectra via `ofFieldLabel`

## iv. References

* None.
-/


-- @@ L44-44 verbatim
@[expose] public section


-- @@ L46-46 verbatim
namespace SuperSymmetry

-- @@ L47-47 verbatim
namespace SU5


-- @@ L49-49 verbatim
namespace ChargeSpectrum

-- @@ L50-50 verbatim
open SuperSymmetry.SU5


-- @@ L52-52 verbatim
variable {𝓩 : Type} [InvolutiveNeg 𝓩]


-- @@ L54-62 verbatim
/-!

## A. Charges associated with a field label

We first define `ofFieldLabel`, which given a charge spectrum `x : ChargeSpectrum 𝓩` and
a `FieldLabel`, returns the finite set of charges associated with representations
corresponding to that `FieldLabel`.

-/

-- @@ L63-71 verbatim
/-- Given an `x : ChargeSpectrum 𝓩`, the charges associated with a given `FieldLabel`. -/
def ofFieldLabel (x : ChargeSpectrum 𝓩) : FieldLabel → Finset 𝓩
  | .fiveBarHd => x.qHd.toFinset
  | .fiveBarHu => x.qHu.toFinset
  | .fiveBarMatter => x.Q5
  | .tenMatter => x.Q10
  | .fiveHd => x.qHd.toFinset.map ⟨Neg.neg, neg_injective⟩
  | .fiveHu => x.qHu.toFinset.map ⟨Neg.neg, neg_injective⟩
  | .fiveMatter => x.Q5.map ⟨Neg.neg, neg_injective⟩


-- @@ L73-80 verbatim
/-!

### A.1. The field labels for the empty charge spectrum

We show that the charges associated with any field label for the empty charge spectrum is empty.
This follows directly from the definition.

-/


-- @@ L82-86 verbatim
/-- `ofFieldLabel ∅ F` is empty for any field label `F`. -/
@[simp]
lemma ofFieldLabel_empty (F : FieldLabel) :
    ofFieldLabel (∅ : ChargeSpectrum 𝓩) F = ∅ := by
  cases F <;> rfl


-- @@ L88-96 verbatim
/-!

### A.2. Monotonicity of `ofFieldLabel`

We show that the function `ofFieldLabel` is monotone in the charge spectrum, with relation to
the subset relation. That is for a fixed field label `F`, if `x ⊆ y` are charge spectra,
then `ofFieldLabel x F ⊆ ofFieldLabel y F`.

-/


-- @@ L98-101 verbatim
/-- The function `ofFieldLabel` is monotone in the charge spectrum. -/
lemma ofFieldLabel_mono {x y : ChargeSpectrum 𝓩} (h : x ⊆ y) (F : FieldLabel) :
    x.ofFieldLabel F ⊆ y.ofFieldLabel F := by
  cases F <;> simp_all [ofFieldLabel, subset_def]


-- @@ L103-110 verbatim
/-!

### A.3. Membership of conjugate charges

We show that a charge is a member of the finite sets associated with a field label if and only if
its negative is a member of the finite set associated with the conjugate field label.

-/


-- @@ L112-115 verbatim
@[simp]
lemma mem_ofFieldLabel_fiveHd (x : 𝓩) (y : ChargeSpectrum 𝓩) :
    x ∈ y.ofFieldLabel FieldLabel.fiveHd ↔ -x ∈ y.ofFieldLabel .fiveBarHd := by
  simp [ofFieldLabel, Finset.mem_map, neg_eq_iff_eq_neg]


-- @@ L117-120 verbatim
@[simp]
lemma mem_ofFieldLabel_fiveHu (x : 𝓩) (y : ChargeSpectrum 𝓩) :
    x ∈ y.ofFieldLabel FieldLabel.fiveHu ↔ -x ∈ y.ofFieldLabel .fiveBarHu := by
  simp [ofFieldLabel, Finset.mem_map, neg_eq_iff_eq_neg]


-- @@ L122-125 verbatim
@[simp]
lemma mem_ofFieldLabel_fiveMatter (x : 𝓩) (y : ChargeSpectrum 𝓩) :
    x ∈ y.ofFieldLabel FieldLabel.fiveMatter ↔ -x ∈ y.ofFieldLabel .fiveBarMatter := by
  simp [ofFieldLabel, Finset.mem_map, neg_eq_iff_eq_neg]


-- @@ L127-136 verbatim
/-!

### A.4. Extensionality of charge spectra via `ofFieldLabel`

We show that two charge spectra are equal if they are equal on all field labels.

This extensionality lemma is actually overkill in most cases, as there are a lot more
direct ways to show that two charge spectra are equal.

-/


-- @@ L138-142 verbatim
/-- Two charges are equal if they are equal on all field labels. -/
lemma ext_ofFieldLabel {x y : ChargeSpectrum 𝓩} (h : ∀ F, x.ofFieldLabel F = y.ofFieldLabel F) :
    x = y := by
  exact eq_of_parts (Option.toFinset_inj.mpr (h .fiveBarHd))
    (Option.toFinset_inj.mpr (h .fiveBarHu)) (h .fiveBarMatter) (h .tenMatter)


-- @@ L144-144 verbatim
end ChargeSpectrum


-- @@ L146-146 verbatim
end SU5

-- @@ L147-147 verbatim
end SuperSymmetry
