module

public import Mathlib.NumberTheory.NumberField.Basic

public import BernoulliRegular.ClassGroupExtension
public import BernoulliRegular.FLT37.LehmerVandiver.PlusCoprime.Sinnott.ClassGroupMinus


-- @@ L8-13 verbatim
/-!
# K-side Stickelberger annihilators

This file packages the `K`-side Stickelberger annihilator conditions used to
trivialize the minus part of the class group in the Lehmer--Vandiver route.
-/


-- @@ L15-15 verbatim
@[expose] public section


-- @@ L17-17 verbatim
noncomputable section


-- @@ L19-19 verbatim
open NumberField


-- @@ L21-21 verbatim
namespace BernoulliRegular


-- @@ L23-23 verbatim
namespace FLT37


-- @@ L25-25 verbatim
namespace Sinnott


-- @@ L27-27 verbatim
variable (p : ℕ) [hp : Fact p.Prime]

-- @@ L28-29 verbatim
variable (K : Type) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K]
  [NumberField.IsCMField K]


-- @@ L31-36 verbatim
/-- The `K`-side Stickelberger annihilator condition on `Cl(K)⁻`. -/
def KSideStickelbergerAnnihilator : Prop :=
  ∀ c ∈ classGroupMinus p K,
    ∃ (θ_K : ClassGroup (𝓞 K)),
      θ_K * c = 1 ∧
      θ_K = 1


-- @@ L38-40 verbatim
/-- The minus eigenspace of the `K`-side class group is trivial. -/
def KSideMinusTrivial : Prop :=
  ∀ c ∈ classGroupMinus p K, c = 1


-- @@ L42-52 verbatim
set_option backward.isDefEq.respectTransparency false in
omit [IsCMField K] in
/-- The Stickelberger annihilator condition is equivalent to minus-part triviality. -/
theorem kSideStickelbergerAnnihilator_iff_minusTrivial :
    KSideStickelbergerAnnihilator p K ↔ KSideMinusTrivial p K := by
  constructor
  · intro h c hc
    obtain ⟨θ, hθ_mul, hθ_one⟩ := h c hc
    simpa [hθ_one] using hθ_mul
  · intro h c hc
    exact ⟨1, by simpa using h c hc, rfl⟩


-- @@ L54-57 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Only the `p`-torsion of `Cl(K)⁻` is annihilated. -/
def KSidePtorsionMinusTrivial : Prop :=
  ∀ c ∈ classGroupMinus p K, c ^ p = 1 → c = 1


-- @@ L59-59 verbatim
end Sinnott


-- @@ L61-61 verbatim
end FLT37


-- @@ L63-63 verbatim
end BernoulliRegular


-- @@ L65-65 verbatim
end
