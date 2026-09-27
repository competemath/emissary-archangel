/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Continuity.Init


-- @@ L14-14 verbatim
/-! TODO: Add doc-string. -/


-- @@ L16-16 verbatim
@[expose] public section


-- @@ L18-18 verbatim
noncomputable section


-- @@ L20-20 verbatim
open Ideal IsDedekindDomain UniqueFactorizationMonoid


-- @@ L22-22 verbatim
namespace NumberField.Odlyzko


-- @@ L24-24 verbatim
variable (K : Type*) [Field K] [NumberField K]


-- @@ L26-28 verbatim
/-- A nonzero ideal used in the Odlyzko-bound argument. -/
abbrev NonzeroIdeal :=
  {I : Ideal (𝓞 K) // I ≠ 0}


-- @@ L30-37 verbatim
/-- An ideal prime factors used in the Odlyzko-bound argument. -/
noncomputable def idealPrimeFactors (I : NonzeroIdeal K) :
    Multiset (HeightOneSpectrum (𝓞 K)) :=
  Multiset.pmap
    (p := fun P : Ideal (𝓞 K) ↦ Prime P)
    (fun _ hP ↦ HeightOneSpectrum.ofPrime hP)
    (normalizedFactors (I : Ideal (𝓞 K)))
    prime_of_normalized_factor


-- @@ L39-45 verbatim
/-- An ideal of prime factors used in the Odlyzko-bound argument. -/
noncomputable def idealOfPrimeFactors
    (m : Multiset (HeightOneSpectrum (𝓞 K))) : NonzeroIdeal K :=
  ⟨(m.map HeightOneSpectrum.asIdeal).prod, by
    exact Multiset.prod_ne_zero fun h ↦
      let ⟨P, hP, heq⟩ := Multiset.mem_map.mp h
      P.ne_bot (heq ▸ rfl)⟩


-- @@ L47-52 verbatim
omit [NumberField K] in
@[simp] theorem idealOfPrimeFactors_coe
    (m : Multiset (HeightOneSpectrum (𝓞 K))) :
    (idealOfPrimeFactors K m : Ideal (𝓞 K)) =
      (m.map HeightOneSpectrum.asIdeal).prod :=
  rfl


-- @@ L54-69 verbatim
theorem idealOfPrimeFactors_idealPrimeFactors (I : NonzeroIdeal K) :
    idealOfPrimeFactors K (idealPrimeFactors K I) = I := by
  apply Subtype.ext
  simp only [idealOfPrimeFactors_coe, idealPrimeFactors, Multiset.map_pmap]
  rw [show Multiset.pmap
      (fun _ hP ↦ (HeightOneSpectrum.ofPrime hP).asIdeal)
      (normalizedFactors (I : Ideal (𝓞 K))) prime_of_normalized_factor =
      normalizedFactors (I : Ideal (𝓞 K)) by
        calc
          _ = Multiset.pmap (fun P (_ : Prime P) ↦ P)
              (normalizedFactors (I : Ideal (𝓞 K)))
              prime_of_normalized_factor := by simp
          _ = Multiset.map id (normalizedFactors (I : Ideal (𝓞 K))) :=
                Multiset.pmap_eq_map _ _ _ _
          _ = normalizedFactors (I : Ideal (𝓞 K)) := Multiset.map_id _]
  simpa only [normalize_eq] using prod_normalizedFactors_eq I.2


-- @@ L71-92 verbatim
theorem idealPrimeFactors_idealOfPrimeFactors
    (m : Multiset (HeightOneSpectrum (𝓞 K))) :
    idealPrimeFactors K (idealOfPrimeFactors K m) = m := by
  rw [idealPrimeFactors]
  have hprime :
      ∀ P ∈ m.map HeightOneSpectrum.asIdeal, Prime P := by
    intro P hP
    obtain ⟨Q, -, rfl⟩ := Multiset.mem_map.mp hP
    exact Q.prime
  have hpmap :
      Multiset.pmap (fun _ hP ↦ HeightOneSpectrum.ofPrime hP)
        (m.map HeightOneSpectrum.asIdeal) hprime = m := by
    induction m using Multiset.induction_on with
    | empty => simp
    | cons P m ih =>
        simp_all
  have hnorm : normalizedFactors
      (idealOfPrimeFactors K m : Ideal (𝓞 K)) =
      m.map HeightOneSpectrum.asIdeal := by
    rw [idealOfPrimeFactors_coe]
    exact normalizedFactors_prod_of_prime hprime
  simp_all


-- @@ L94-100 verbatim
/-- A nonzero ideal equiv prime factors used in the Odlyzko-bound argument. -/
noncomputable def nonzeroIdealEquivPrimeFactors :
    NonzeroIdeal K ≃ Multiset (HeightOneSpectrum (𝓞 K)) where
  toFun := idealPrimeFactors K
  invFun := idealOfPrimeFactors K
  left_inv := idealOfPrimeFactors_idealPrimeFactors K
  right_inv := idealPrimeFactors_idealOfPrimeFactors K


-- @@ L102-102 verbatim
end NumberField.Odlyzko
