import OAI.Algebra.AffineCancellation.Cylinder


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace ComplexCancellation


-- @@ L9-9 verbatim
theorem finiteType : Algebra.FiniteType ℂ A := inferInstance


-- @@ L11-17 verbatim
instance domain : IsDomain A :=
  Function.Injective.isDomain Cylinder.coefficientMap (by
    intro r s hrs
    apply Polynomial.C_injective
    apply Cylinder.equivalence.injective
    simpa only [Cylinder.equivalence, AlgEquiv.ofAlgHom_apply,
      Cylinder.forward_C] using hrs)


-- @@ L19-19 verbatim
instance noetherian : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℂ A


-- @@ L21-40 verbatim
theorem dimension : ringKrullDim A = 4 := by
  have hd : ringKrullDim A + 1 = 5 := by
    rw [← Polynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_of_ringEquiv Cylinder.equivalence.toRingEquiv,
      MvPolynomial.ringKrullDim_of_isNoetherianRing,
      ringKrullDim_eq_zero_of_field, zero_add]
    simp
  generalize ringKrullDim A = d at *
  induction d using WithBot.recBotCoe with
  | bot => simp at hd
  | coe d =>
    have hd' : d + 1 = 5 := WithBot.coe_inj.mp (by
      simpa only [WithBot.coe_add, WithBot.coe_one, WithBot.coe_ofNat] using hd)
    induction d using ENat.recTopCoe with
    | top => simp at hd'
    | coe n =>
      have hd'' : n + 1 = 5 := by exact_mod_cast hd'
      have hn : n = 4 := by omega
      subst n
      rfl


-- @@ L42-43 verbatim
theorem stabilization : Nonempty (Polynomial A ≃ₐ[ℂ] MvPolynomial (Fin 5) ℂ) :=
  ⟨Cylinder.equivalence⟩


-- @@ L45-45 verbatim
end ComplexCancellation


-- @@ L47-47 verbatim
end


-- @@ L49-49 verbatim
end OAI
