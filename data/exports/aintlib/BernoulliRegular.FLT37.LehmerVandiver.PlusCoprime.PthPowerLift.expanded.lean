/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekLog.PthPower


-- @@ L10-36 verbatim
/-!
# `p`-th power lift: mod `𝔩` ⇒ in `R` (LV005a)

Trivial direction lemmas for `IsPthPowerModPrime`. If `x : R` is a `p`-th
power in the ambient ring `R` (i.e. `x = α ^ p` for some `α : R`), then
`x` is a `p`-th power modulo any ideal `𝔩 ⊂ R`. The contrapositive — if
`x` is **not** a `p`-th power modulo `𝔩`, then `x` is not a `p`-th power
in `R` — is the form consumed by LV005c/e.

The unit-group specialisation `Rˣ` is also packaged here, since downstream
arguments (LV005b symmetrisation, LV005c Kummer-pairing) work with units
of `𝓞 K` and `𝓞 K⁺`.

## Main results

* `IsPthPowerModPrime.of_pow` — `x = α ^ p ⟹ IsPthPowerModPrime p 𝔩 x`.
* `IsPthPowerModPrime.of_isPthPower_unit` — for `u : Rˣ`, if `(u : R)`
  equals `(α : R) ^ p` for some unit `α : Rˣ`, then `IsPthPowerModPrime`.
* `not_pow_of_not_isPthPowerModPrime` — contrapositive of `of_pow`.
* `not_isPthPower_unit_of_not_isPthPowerModPrime` — contrapositive at
  the unit-group level.

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer GTM 83),
  Corollary 8.19 (p. 158).
-/


-- @@ L38-38 verbatim
@[expose] public section


-- @@ L40-40 verbatim
namespace BernoulliRegular


-- @@ L42-42 verbatim
variable {R : Type*} [CommRing R] {p : ℕ} {𝔩 : Ideal R}


-- @@ L44-44 verbatim
namespace IsPthPowerModPrime


-- @@ L46-50 verbatim
/-- **`p`-th power lift**: if `x = α ^ p` in `R`, then `x` is a `p`-th
power modulo any ideal `𝔩`. -/
theorem of_pow {x α : R} (h : x = α ^ p) : IsPthPowerModPrime p 𝔩 x := by
  subst h
  exact pow_self α


-- @@ L52-57 verbatim
/-- **Unit-group form of the `p`-th power lift**: if `(u : R) = (α : R) ^ p`
for units `u α : Rˣ`, then `(u : R)` is a `p`-th power modulo any ideal
`𝔩`. -/
theorem of_isPthPower_unit {u α : Rˣ} (h : (u : R) = (α : R) ^ p) :
    IsPthPowerModPrime p 𝔩 (u : R) :=
  of_pow h


-- @@ L59-59 verbatim
end IsPthPowerModPrime


-- @@ L61-67 verbatim
/-- **Contrapositive of the lift**: if `x` is not a `p`-th power modulo
`𝔩`, then there is no `α : R` with `x = α ^ p`. -/
theorem not_pow_of_not_isPthPowerModPrime {x : R}
    (hx : ¬ IsPthPowerModPrime p 𝔩 x) :
    ∀ α : R, x ≠ α ^ p := by
  intro α hα
  exact hx (IsPthPowerModPrime.of_pow hα)


-- @@ L69-76 verbatim
/-- **Contrapositive at the unit-group level**: if `(u : R)` is not a
`p`-th power modulo `𝔩`, then there is no unit `α : Rˣ` with
`(u : R) = (α : R) ^ p`. -/
theorem not_isPthPower_unit_of_not_isPthPowerModPrime {u : Rˣ}
    (hu : ¬ IsPthPowerModPrime p 𝔩 (u : R)) :
    ∀ α : Rˣ, (u : R) ≠ (α : R) ^ p := by
  intro α hα
  exact hu (IsPthPowerModPrime.of_isPthPower_unit hα)


-- @@ L78-78 verbatim
end BernoulliRegular


-- @@ L80-80 verbatim
end
