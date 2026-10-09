import OAI.RepresentationTheory.FoulkesHowe.TensorPresentation


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
universe u


-- @@ L8-8 verbatim
namespace Problem346


-- @@ L10-14 verbatim
/-- Every homogeneous symmetric power of a finite-dimensional complex space is
finite dimensional. The proof uses its tensor-power presentation. -/
instance finiteDimensional_symPow (n : ℕ) (V : Type u) [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] : FiniteDimensional ℂ (SymPow n V) :=
  Module.Finite.of_surjective (tensorToSymPow n V) (tensorToSymPow_surjective n V)


-- @@ L16-16 verbatim
end Problem346


-- @@ L18-18 verbatim
end


-- @@ L20-20 verbatim
end OAI
