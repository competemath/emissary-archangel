module

public import BernoulliRegular.FLT37.LehmerVandiver.PollaczekUnit


-- @@ L5-30 verbatim
/-!
# σ-symmetrisation of `pollaczekUnit`

The Pollaczek unit `pollaczekUnit p K i ∈ (𝓞 K)ˣ` is not literally fixed by
the unit-group complex conjugation `unitsComplexConj K`: the factor-wise
σ-twist
`σ((1 - ζ^b)/(1 - ζ)) = ζ^{1 - b} · (1 - ζ^b)/(1 - ζ)` introduces an
explicit ζ-power. The standard remedy is the symmetrised real combination

  `pollaczekUnitPlus p K i := pollaczekUnit p K i · σ(pollaczekUnit p K i)`,

which is σ-fixed and underlies the descent to the maximal real subfield `K⁺`.

This file packages just the bare arithmetic:

* `pollaczekUnitPlus` — the symmetrised unit in `(𝓞 K)ˣ`.
* `pollaczekUnitPlus_complexConj` — σ-fixedness.
* `pollaczekUnitPlus_norm` — `Algebra.norm ℤ` is `1` (square of
  `pollaczekUnit_norm`, after using that `Algebra.norm` is fixed by
  Galois).

## References

* Washington, *Introduction to Cyclotomic Fields*, 2nd ed. (Springer
  GTM 83), §8.3 (Pollaczek units, p. 158); Corollary 8.19 (p. 158).
-/


-- @@ L32-32 verbatim
@[expose] public section


-- @@ L34-34 verbatim
noncomputable section


-- @@ L36-36 verbatim
open NumberField NumberField.IsCMField IsCyclotomicExtension

-- @@ L37-37 verbatim
open scoped NumberField


-- @@ L39-39 verbatim
namespace BernoulliRegular


-- @@ L41-41 verbatim
namespace FLT37


-- @@ L43-44 verbatim
variable (p : ℕ) [hp : Fact p.Prime]
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]


-- @@ L46-46 verbatim
section PollaczekUnitPlus


-- @@ L48-48 verbatim
variable (i : ℕ)


-- @@ L50-56 verbatim
/-- The symmetrised Pollaczek unit
`pollaczekUnitPlus p K i := pollaczekUnit p K i · σ(pollaczekUnit p K i)`,
where `σ = unitsComplexConj K`. This is a unit of `𝓞 K` that is fixed by
complex conjugation (hence underlies a unit of `𝓞 K⁺`) and has integer
norm `1`. -/
noncomputable def pollaczekUnitPlus [IsCMField K] : (𝓞 K)ˣ :=
  pollaczekUnit p K i * unitsComplexConj K (pollaczekUnit p K i)


-- @@ L58-63 verbatim
/-- σ-fixedness of the symmetrised Pollaczek unit: complex conjugation
fixes `pollaczekUnitPlus`. Direct repackage of `pollaczekUnit_complexConj`
behind the `pollaczekUnitPlus` definition. -/
theorem pollaczekUnitPlus_complexConj [IsCMField K] :
    unitsComplexConj K (pollaczekUnitPlus p K i) = pollaczekUnitPlus p K i :=
  pollaczekUnit_complexConj p K i


-- @@ L65-93 verbatim
/-- The integer norm of `pollaczekUnitPlus` is `1`. The symmetrised unit
is a product of two `Algebra.norm ℤ`-trivial factors: `pollaczekUnit` and its
complex conjugate. The conjugate has the same `Algebra.norm ℤ` since
`ringOfIntegersComplexConj K` is a `𝓞 K⁺`-AlgEquiv (and a fortiori a
`ℤ`-AlgEquiv) of `𝓞 K`, so `Algebra.norm_eq_of_algEquiv` applies after
`restrictScalars`. -/
theorem pollaczekUnitPlus_norm [IsCMField K] (hp_odd : p ≠ 2) :
    Algebra.norm ℤ ((pollaczekUnitPlus p K i : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
  simp only [pollaczekUnitPlus]
  rw [Units.val_mul, map_mul]
  have h_E := pollaczekUnit_norm p K i hp_odd
  have h_σE :
      Algebra.norm ℤ
        ((unitsComplexConj K (pollaczekUnit p K i) : (𝓞 K)ˣ) : 𝓞 K) = 1 := by
    rw [show ((unitsComplexConj K (pollaczekUnit p K i) :
          (𝓞 K)ˣ) : 𝓞 K) =
        ringOfIntegersComplexConj K
          ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) from rfl]
    -- Algebra.norm ℤ is preserved by ringOfIntegersComplexConj (a 𝓞 K⁺-AlgEquiv,
    -- hence ℤ-linear via restrictScalars).
    have h_alg :
        Algebra.norm ℤ
            ((ringOfIntegersComplexConj K).restrictScalars ℤ
              ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K)) =
          Algebra.norm ℤ ((pollaczekUnit p K i : (𝓞 K)ˣ) : 𝓞 K) :=
      Algebra.norm_eq_of_algEquiv
        ((ringOfIntegersComplexConj K).restrictScalars ℤ) _
    exact h_alg.trans h_E
  rw [h_E, h_σE, mul_one]


-- @@ L95-95 verbatim
end PollaczekUnitPlus


-- @@ L97-97 verbatim
end FLT37


-- @@ L99-99 verbatim
end BernoulliRegular


-- @@ L101-101 verbatim
end
