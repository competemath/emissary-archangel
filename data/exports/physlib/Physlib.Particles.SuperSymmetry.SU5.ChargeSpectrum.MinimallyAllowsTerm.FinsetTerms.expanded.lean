/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Tactic.FinCases
public import Physlib.Particles.SuperSymmetry.SU5.ChargeSpectrum.MinimallyAllowsTerm.Basic

-- @@ L10-47 verbatim
/-!

# Minimally allows a set of terms

## i. Overview

In this module we consider those charge spectra which minimally allow a
finite set of potential terms.
That is, they those charge spectra which allow each term in the set, but no proper subset of the
charge spectra allows each term in that set.

We have special focus on those charge spectra which minimally allow a top and bottom Yukawa term.

## ii. Key results

- `MinimallyAllowsFinsetTerms`: the proposition that a charge spectrum
  minimally allows a given finite set of potential terms.
- `minTopBottom`: a finite set of charge spectra which contains every
  charge spectrum which minimally allows a top and bottom Yukawa term, given
  finite sets of possible `5`-bar and `10` charges.

## iii. Table of contents

- A. Charge spectra which minimally allow a finite set of potential terms
  - A.1. `MinimallyAllowsFinsetTerms`: Prop of minimally allowing a finset of potential terms
  - A.2. The prop `MinimallyAllowsFinsetTerms` is decidable
  - A.3. Every element of `MinimallyAllowsFinsetTerms` allows each term in the finset
  - A.4. `MinimallyAllowsFinsetTerms` for the singleton set is equivalent to `MinimallyAllowsTerm`
- B. Minimally allowing the top and bottom Yukawa
  - B.1. Finset of charge spectra containing those which minimally allow top and bottom Yukawa
  - B.2. Every element of `minTopBottom` allows a top Yukawa
  - B.3. Every element of `minTopBottom` allows a bottom Yukawa
  - B.4. Every charge spectrum minimally allowing a top and bottom Yukawa in `minTopBottom`

## iv. References

* None.
-/


-- @@ L49-49 verbatim
@[expose] public section


-- @@ L51-51 verbatim
namespace SuperSymmetry

-- @@ L52-52 verbatim
namespace SU5


-- @@ L54-54 verbatim
namespace ChargeSpectrum


-- @@ L56-56 verbatim
variable {𝓩 : Type} [AddCommGroup 𝓩] [DecidableEq 𝓩]

-- @@ L57-57 verbatim
open SuperSymmetry.SU5

-- @@ L58-58 verbatim
open PotentialTerm

-- @@ L59-66 verbatim
/-!

## A. Charge spectra which minimally allow a finite set of potential terms

We start by defining the proposition that a charge spectrum minimally allows a
finite set of potential terms, and prove some basic properties there of.

-/


-- @@ L68-72 verbatim
/-!

### A.1. `MinimallyAllowsFinsetTerms`: Prop of minimally allowing a finset of potential terms

-/

-- @@ L73-77 verbatim
/-- A collection of charge spectra is said to minimally allow
  a finite set of potential terms `Ts` if it allows
  all terms in `Ts` and no strict subset of it allows all terms in `Ts`. -/
def MinimallyAllowsFinsetTerms (x : ChargeSpectrum 𝓩) (Ts : Finset PotentialTerm) : Prop :=
  ∀ y ∈ x.powerset, y = x ↔ ∀ T ∈ Ts, y.AllowsTerm T


-- @@ L79-83 verbatim
/-!

### A.2. The prop `MinimallyAllowsFinsetTerms` is decidable

-/


-- @@ L85-87 verbatim
instance (x : ChargeSpectrum 𝓩) (Ts : Finset PotentialTerm) :
    Decidable (x.MinimallyAllowsFinsetTerms Ts) :=
  inferInstanceAs (Decidable (∀ y ∈ powerset x, y = x ↔ ∀ T ∈ Ts, y.AllowsTerm T))


-- @@ L89-93 verbatim
/-!

### A.3. Every element of `MinimallyAllowsFinsetTerms` allows each term in the finset

-/


-- @@ L95-95 verbatim
variable {Ts : Finset PotentialTerm} {x : ChargeSpectrum 𝓩}


-- @@ L97-99 verbatim
lemma allowsTerm_of_minimallyAllowsFinsetTerms {T : PotentialTerm}
    (h : x.MinimallyAllowsFinsetTerms Ts) (hT : T ∈ Ts) : x.AllowsTerm T :=
  (h x (self_mem_powerset x)).mp rfl T hT


-- @@ L101-105 verbatim
/-!

### A.4. `MinimallyAllowsFinsetTerms` for the singleton set is equivalent to `MinimallyAllowsTerm`

-/


-- @@ L107-110 verbatim
@[simp]
lemma minimallyAllowsFinsetTerms_singleton {T : PotentialTerm} :
    x.MinimallyAllowsFinsetTerms {T} ↔ x.MinimallyAllowsTerm T := by
  simp [MinimallyAllowsFinsetTerms, MinimallyAllowsTerm]


-- @@ L112-123 verbatim
/-!

## B. Minimally allowing the top and bottom Yukawa

We now consider the special case of those charge spectra which minimally allow
a top and bottom Yukawa term.

We construct a finite set of such charge spectra given finite sets of
possible `5`-bar and `10` charges which contains every charge
spectrum which minimally allows a top and bottom Yukawa term.

-/


-- @@ L125-131 verbatim
/-!

### B.1. Finset of charge spectra containing those which minimally allow top and bottom Yukawa

Here we define `minTopBottom` in a way which is computationally efficient.

-/


-- @@ L133-137 verbatim
/-- The set of charges of the form `(qHd, qHu, {q5}, {-qHd-q5, q10, qHu - q10})`
  This includes every charge which minimally allows for the top and bottom Yukawas. -/
def minTopBottom (S5 S10 : Finset 𝓩) : Multiset (ChargeSpectrum 𝓩) := Multiset.dedup <|
  (S5.val ×ˢ S5.val ×ˢ S5.val ×ˢ S10.val).map
    (fun x => ⟨x.1, x.2.1, {x.2.2.1}, {- x.1 - x.2.2.1, x.2.2.2, x.2.1 - x.2.2.2}⟩)


-- @@ L139-143 verbatim
/-!

### B.2. Every element of `minTopBottom` allows a top Yukawa

-/


-- @@ L145-151 verbatim
lemma allowsTerm_topYukawa_of_mem_minTopBottom {S5 S10 : Finset 𝓩}
    {x : ChargeSpectrum 𝓩} (h : x ∈ minTopBottom S5 S10) :
    x.AllowsTerm topYukawa := by
  simp [minTopBottom] at h
  obtain ⟨qHd, qHu, q5, q10, _, rfl⟩ := h
  simp [allowsTerm_iff_subset_allowsTermForm, allowsTermForm, subset_def]
  exact ⟨-qHu, by simp, q10, by simp⟩


-- @@ L153-157 verbatim
/-!

### B.3. Every element of `minTopBottom` allows a bottom Yukawa

-/


-- @@ L159-164 verbatim
lemma allowsTerm_bottomYukawa_of_mem_minTopBottom {S5 S10 : Finset 𝓩}
    {x : ChargeSpectrum 𝓩} (h : x ∈ minTopBottom S5 S10) :
    x.AllowsTerm bottomYukawa := by
  simp [minTopBottom] at h
  obtain ⟨qHd, qHu, q5, q10, _, rfl⟩ := h
  simp [allowsTerm_iff_subset_allowsTermForm, allowsTermForm, subset_def]


-- @@ L166-170 verbatim
/-!

### B.4. Every charge spectrum minimally allowing a top and bottom Yukawa in `minTopBottom`

-/


-- @@ L172-199 verbatim
lemma mem_minTopBottom_of_minimallyAllowsFinsetTerms
    {x : ChargeSpectrum 𝓩} {S5 S10 : Finset 𝓩}
    (h : x.MinimallyAllowsFinsetTerms {topYukawa, bottomYukawa})
    (hx : x ∈ ofFinset S5 S10) :
    x ∈ minTopBottom S5 S10 := by
  simp [minTopBottom]
  have hTop : x.AllowsTerm topYukawa := allowsTerm_of_minimallyAllowsFinsetTerms h (by simp)
  have hBottom : x.AllowsTerm bottomYukawa := allowsTerm_of_minimallyAllowsFinsetTerms h (by simp)
  match x with
  | ⟨none, qHu, Q5, Q10⟩ =>
    simp [allowsTerm_iff_subset_allowsTermForm, allowsTermForm, subset_def] at hBottom
  | ⟨qHd, none, Q5, Q10⟩ =>
    simp [allowsTerm_iff_subset_allowsTermForm, allowsTermForm, subset_def] at hTop
  | ⟨some qHd, some qHu, Q5, Q10⟩ =>
  simp [allowsTerm_iff_subset_allowsTermForm, allowsTermForm, subset_def] at hTop hBottom
  obtain ⟨n, hn, q10, h10⟩ := hTop
  obtain ⟨q5, h5⟩ := hBottom
  use qHd, qHu, q5, q10
  simp [mem_ofFinset_iff] at hx
  refine ⟨⟨hx.1, hx.2.1, hx.2.2.1 h5.1, hx.2.2.2 (h10 (Finset.mem_insert_self _ _))⟩, ?_⟩
  refine (h _ ?_).mpr ?_
  · simp [subset_def]
    exact ⟨h5.1, Finset.insert_subset h5.2 (hn ▸ h10)⟩
  · intro T hT
    fin_cases hT
    · simp [allowsTerm_iff_subset_allowsTermForm, allowsTermForm, subset_def]
      exact ⟨-qHu, by simp, q10, by simp⟩
    · simp [allowsTerm_iff_subset_allowsTermForm, allowsTermForm, subset_def]


-- @@ L201-201 verbatim
end ChargeSpectrum


-- @@ L203-203 verbatim
end SU5

-- @@ L204-204 verbatim
end SuperSymmetry
