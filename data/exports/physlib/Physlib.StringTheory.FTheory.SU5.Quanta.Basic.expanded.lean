/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Physlib.StringTheory.FTheory.SU5.Quanta.FiveQuanta
public import Physlib.StringTheory.FTheory.SU5.Quanta.TenQuanta

-- @@ L10-51 verbatim
/-!

# Quanta of representations

## i. Overview

In SU(5) × U(1) F-theory theory, each 5-bar and 10d representation
carries with it the quantum numbers of their U(1) charges and their fluxes.

In this module we define the data structure for these quanta and
properties thereof.

## ii. Key results

- `Quanta` : The structure containing the quantum numbers of the 5-bar and 10d
  representations, as well as the charges of the `Hd` and `Hu` particles.
- `Quanta.liftCharge` : Lifting a `ChargeSpectrum` to a multiset of `Quanta`
  which have no chiral exotics and no zero fluxes.
- `Quanta.AnomalyCancellation` : The anomaly cancellation conditions on a `Quanta`.

## iii. Table of contents

- A. The Quanta structure
  - A.1. Repr instance on `Quanta`
  - A.2. Extensionality lemma
  - A.3. Decidable equality instance
  - A.4. Map to the underlying `ChargeSpectrum`
- B. The reduction of a `Quanta`
- C. Lifting a charge spectrum to quanta with no exotics or zero fluxes
  - C.1. Simplification of membership in the liftCharge multiset
  - C.2. Charge spectrum of a lifted quanta
- D. Anomaly cancellation conditions
  - D.1. The anomaly coefficient of Hd
  - D.2. The anomaly coefficient of Hu
  - D.3. The anomaly cancellation condition propositions
    - D.3.1. The propositions are decidable

## iv. References

* Rational F-Theory GUTs without exotics (arXiv:1401.5084), Anomaly cancellation conditions,
  equation 22. [ref: arxiv_1401_5084]
-/


-- @@ L53-53 verbatim
@[expose] public section

-- @@ L54-54 verbatim
namespace FTheory


-- @@ L56-56 verbatim
namespace SU5

-- @@ L57-57 verbatim
open SU5

-- @@ L58-58 verbatim
variable {I : CodimensionOneConfig}


-- @@ L60-64 verbatim
/-!

## A. The Quanta structure

-/


-- @@ L66-80 verbatim
/-- The quanta associated with the representations in a `SU(5) x U(1)` F-theory.
  This contains the value of the charges and the flux integers `(M, N)` for the
  5-bar matter content and the 10d matter content, and the charges of the `Hd` and
  `Hu` particles (there values of `(M,N)` are not included as they are
  forced to be `(0, 1)` and `(0, -1)` respectively. -/
structure Quanta (𝓩 : Type := ℤ) where
  /-- The charge of the Hd matter field. -/
  qHd : Option 𝓩
  /-- The negative charge of the Hu matter field.
    In other words the charge of the Hu considered as a 5-bar field. -/
  qHu : Option 𝓩
  /-- The quanta carried by the 5-bar matter fields. -/
  F : FiveQuanta 𝓩
  /-- The quanta carried by the 10d matter fields. -/
  T : TenQuanta 𝓩


-- @@ L82-82 verbatim
namespace Quanta

-- @@ L83-83 verbatim
open SuperSymmetry.SU5

-- @@ L84-84 verbatim
open PotentialTerm ChargeSpectrum


-- @@ L86-86 verbatim
variable {𝓩 : Type}


-- @@ L88-92 verbatim
/-!

### A.1. Repr instance on `Quanta`

-/


-- @@ L94-100 verbatim
unsafe instance [Repr 𝓩] : Repr (Quanta 𝓩) where
  reprPrec x _ := "⟨" ++
    repr x.qHd ++ ", " ++
    repr x.qHu ++ ", " ++
    repr x.F ++ ", " ++
    repr x.T ++
    "⟩"


-- @@ L102-106 verbatim
/-!

### A.2. Extensionality lemma

-/


-- @@ L108-112 verbatim
@[ext]
lemma ext {𝓩 : Type} {x y : Quanta 𝓩} (h1 : x.qHd = y.qHd) (h2 : x.qHu = y.qHu)
    (h3 : x.F = y.F) (h4 : x.T = y.T) : x = y := by
  cases x; cases y;
  simp_all


-- @@ L114-118 verbatim
/-!

### A.3. Decidable equality instance

-/


-- @@ L120-121 verbatim
instance [DecidableEq 𝓩] : DecidableEq (Quanta 𝓩) := fun x y =>
  decidable_of_iff (x.qHd = y.qHd ∧ x.qHu = y.qHu ∧ x.F = y.F ∧ x.T = y.T) Quanta.ext_iff.symm


-- @@ L123-127 verbatim
/-!

### A.4. Map to the underlying `ChargeSpectrum`

-/

-- @@ L128-133 verbatim
/-- The underlying `ChargeSpectrum` of a `Quanta`. -/
def toCharges [DecidableEq 𝓩] (x : Quanta 𝓩) : ChargeSpectrum 𝓩 where
  qHd := x.qHd
  qHu := x.qHu
  Q5 := x.F.toCharges.toFinset
  Q10 := x.T.toCharges.toFinset


-- @@ L135-135 verbatim
lemma toCharges_qHd [DecidableEq 𝓩] (x : Quanta 𝓩) : (toCharges x).qHd = x.qHd := rfl


-- @@ L137-137 verbatim
lemma toCharges_qHu [DecidableEq 𝓩] (x : Quanta 𝓩) : (toCharges x).qHu = x.qHu := rfl


-- @@ L139-143 verbatim
/-!

## B. The reduction of a `Quanta`

-/


-- @@ L145-151 verbatim
/-- The reduce of `Quanta` is a new `Quanta` with all the fluxes corresponding to the same
  charge (i.e. representation) added together. -/
def reduce [DecidableEq 𝓩] (x : Quanta 𝓩) : Quanta 𝓩 where
  qHd := x.qHd
  qHu := x.qHu
  F := x.F.reduce
  T := x.T.reduce


-- @@ L153-157 verbatim
/-!

## C. Lifting a charge spectrum to quanta with no exotics or zero fluxes

-/


-- @@ L159-166 verbatim
/-- Lifting a charge spectrum to quanta which do not have exotics and
  which have no zero flux. -/
def liftCharge [DecidableEq 𝓩] (c : ChargeSpectrum 𝓩) : Multiset (Quanta 𝓩) :=
  let Q5s := FiveQuanta.liftCharge c.Q5
  let Q10s := TenQuanta.liftCharge c.Q10
  Q5s.bind <| fun Q5 =>
  Q10s.map <| fun Q10 =>
    ⟨c.qHd, c.qHu, Q5, Q10⟩


-- @@ L168-172 verbatim
/-!

### C.1. Simplification of membership in the liftCharge multiset

-/

-- @@ L173-182 verbatim
lemma mem_liftCharge_iff [DecidableEq 𝓩] {c : ChargeSpectrum 𝓩}
    {x : Quanta 𝓩} :
    x ∈ liftCharge c ↔ x.qHd = c.qHd ∧ x.qHu = c.qHu ∧
    x.F ∈ FiveQuanta.liftCharge c.Q5 ∧ x.T ∈ TenQuanta.liftCharge c.Q10:= by
  simp only [liftCharge, Multiset.mem_bind, Multiset.mem_map]
  constructor
  · rintro ⟨Q5, h1, Q10, h2, rfl⟩
    exact ⟨rfl, rfl, h1, h2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨x.F, h3, x.T, h4, by rw [← h1, ← h2]⟩


-- @@ L184-188 verbatim
/-!

### C.2. Charge spectrum of a lifted quanta

-/


-- @@ L190-197 verbatim
lemma toCharges_of_mem_liftCharge [DecidableEq 𝓩] {c : ChargeSpectrum 𝓩}
    {x : Quanta 𝓩} (h : x ∈ liftCharge c) :
    x.toCharges = c := by
  rw [mem_liftCharge_iff] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  rw [FiveQuanta.mem_liftCharge_iff] at h3
  rw [TenQuanta.mem_liftCharge_iff] at h4
  exact ChargeSpectrum.eq_of_parts h1 h2 h3.2.1 h4.2.1


-- @@ L199-214 verbatim
/-!

## D. Anomaly cancellation conditions

There are two anomaly cancellation conditions in the SU(5)×U(1) model which involve the
`U(1)` charges. These are

- `∑ᵢ qᵢ Nᵢ + ∑ₐ qₐ Nₐ = 0` where the first sum is over all 5-bar representations and the second
  is over all 10d representations.
- `∑ᵢ qᵢ² Nᵢ + 3 * ∑ₐ qₐ² Nₐ = 0` where the first sum is over all 5-bar representations and the
  second is over all 10d representations.

According to arXiv:1401.5084 [ref: arxiv_1401_5084] it is unclear whether this second condition
should necessarily be imposed.

-/


-- @@ L216-220 verbatim
/-!

### D.1. The anomaly coefficient of Hd

-/


-- @@ L222-226 verbatim
/-- The pair of anomaly cancellation coefficients associated with the `Hd` particle. -/
def HdAnomalyCoefficient [CommRing 𝓩] (qHd : Option 𝓩) : 𝓩 × 𝓩 :=
  match qHd with
  | none => (0, 0)
  | some qHd => (qHd, qHd ^ 2)


-- @@ L228-232 verbatim
@[simp]
lemma HdAnomalyCoefficient_map {𝓩 𝓩1 : Type} [CommRing 𝓩] [CommRing 𝓩1]
    (f : 𝓩 →+* 𝓩1) (qHd : Option 𝓩) :
    HdAnomalyCoefficient (qHd.map f) = (f.prodMap f) (HdAnomalyCoefficient qHd) := by
  cases qHd <;> simp [HdAnomalyCoefficient]


-- @@ L234-238 verbatim
/-!

### D.2. The anomaly coefficient of Hu

-/


-- @@ L240-244 verbatim
/-- The pair of anomaly cancellation coefficients associated with the `Hu` particle. -/
def HuAnomalyCoefficient [CommRing 𝓩] (qHu : Option 𝓩) : 𝓩 × 𝓩 :=
  match qHu with
  | none => (0, 0)
  | some qHu => (-qHu, -qHu ^ 2)


-- @@ L246-250 verbatim
@[simp]
lemma HuAnomalyCoefficient_map {𝓩 𝓩1 : Type} [CommRing 𝓩] [CommRing 𝓩1]
    (f : 𝓩 →+* 𝓩1) (qHu : Option 𝓩) :
    HuAnomalyCoefficient (qHu.map f) = (f.prodMap f) (HuAnomalyCoefficient qHu) := by
  cases qHu <;> simp [HuAnomalyCoefficient]


-- @@ L252-256 verbatim
/-!

### D.3. The anomaly cancellation condition propositions

-/


-- @@ L258-263 verbatim
/-- The linear anomaly cancellation condition, corresponding to
`∑ᵢ qᵢ Nᵢ + ∑ₐ qₐ Nₐ = 0` where the first sum is over all 5-bar representations and the second
  is over all 10d representations. -/
def LinearAnomalyCancellation [CommRing 𝓩] (Q : Quanta 𝓩) : Prop :=
  (HdAnomalyCoefficient Q.qHd).1 + (HuAnomalyCoefficient Q.qHu).1 + Q.F.anomalyCoefficient.1 +
  Q.T.anomalyCoefficient.1 = 0


-- @@ L265-272 verbatim
/-- The quartic anomaly cancellation condition, corresponding to
`∑ᵢ qᵢ² Nᵢ + 3 * ∑ₐ qₐ² Nₐ = 0` where the first sum is over all 5-bar representations and the
  second is over all 10d representations.
-/
def QuarticAnomalyCancellation [CommRing 𝓩] (Q : Quanta 𝓩) :
    Prop :=
  (HdAnomalyCoefficient Q.qHd).2 + (HuAnomalyCoefficient Q.qHu).2 + Q.F.anomalyCoefficient.2 +
    Q.T.anomalyCoefficient.2 = 0


-- @@ L274-278 verbatim
/-!

#### D.3.1. The propositions are decidable

-/


-- @@ L280-282 verbatim
instance [CommRing 𝓩] [DecidableEq 𝓩] (Q : Quanta 𝓩) : Decidable Q.LinearAnomalyCancellation :=
    inferInstanceAs (Decidable ((HdAnomalyCoefficient Q.qHd).1 +
    (HuAnomalyCoefficient Q.qHu).1 + Q.F.anomalyCoefficient.1 + Q.T.anomalyCoefficient.1 = 0))


-- @@ L284-286 verbatim
instance [CommRing 𝓩] [DecidableEq 𝓩] (Q : Quanta 𝓩) : Decidable Q.QuarticAnomalyCancellation :=
    inferInstanceAs (Decidable ((HdAnomalyCoefficient Q.qHd).2 +
    (HuAnomalyCoefficient Q.qHu).2 + Q.F.anomalyCoefficient.2 + Q.T.anomalyCoefficient.2 = 0))


-- @@ L288-288 verbatim
end Quanta


-- @@ L290-290 verbatim
end SU5


-- @@ L292-292 verbatim
end FTheory
