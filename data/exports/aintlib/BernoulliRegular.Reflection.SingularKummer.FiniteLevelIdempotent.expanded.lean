module

public import BernoulliRegular.Reflection.SingularKummer.FiniteLevelProjectionBridge


-- @@ L5-27 verbatim
/-!
# Singular Kummer: exact finite-level character idempotents

This file proves the finite-level algebra behind the exact component
projection.  Let `D` be a finite group, let

```text
  chi : D -> (ZMod m)^*
```

be a multiplicative character, and let `rho` be a linear action of `D` on a
`ZMod m`-module `M`.  If `|D|` is a unit in `ZMod m`, then the averaged
operator

```text
  |D|^{-1} * sum_d chi(d)^{-1} rho(d)
```

acts as the identity on its own range and is therefore an exact idempotent.

The cyclotomic application will take `D = (ZMod p)^*` and `m = p^N`, with
`chi` the Teichmuller lift modulo `p^N`.
-/


-- @@ L29-29 verbatim
@[expose] public section


-- @@ L31-31 verbatim
noncomputable section


-- @@ L33-33 verbatim
namespace BernoulliRegular

-- @@ L34-34 verbatim
namespace Reflection

-- @@ L35-35 verbatim
namespace SingularKummer


-- @@ L37-37 verbatim
namespace FiniteLevelIdempotent


-- @@ L39-39 verbatim
variable {m : ℕ}

-- @@ L40-40 verbatim
variable {D M : Type*} [Group D] [Fintype D]

-- @@ L41-41 verbatim
variable [AddCommGroup M] [Module (ZMod m) M]


-- @@ L43-45 verbatim
/-- Coefficient of the finite-level character projection attached to `chi`. -/
def coefficient (chi : D →* (ZMod m)ˣ) (d : D) : ZMod m :=
  (Fintype.card D : ZMod m)⁻¹ * (chi d⁻¹ : ZMod m)


-- @@ L47-52 verbatim
/-- The exact finite-level character projection attached to a multiplicative
character `chi`. -/
def projection
    (rho : D →* M ≃ₗ[ZMod m] M) (chi : D →* (ZMod m)ˣ) :
    M →ₗ[ZMod m] M :=
  ∑ d : D, coefficient (m := m) chi d • (rho d : M →ₗ[ZMod m] M)


-- @@ L54-59 verbatim
@[simp]
theorem projection_apply
    (rho : D →* M ≃ₗ[ZMod m] M) (chi : D →* (ZMod m)ˣ) (x : M) :
    projection (m := m) rho chi x =
      ∑ d : D, coefficient (m := m) chi d • rho d x := by
  simp [projection]


-- @@ L61-66 verbatim
theorem coefficient_inv_mul
    (chi : D →* (ZMod m)ˣ) (b a : D) :
    coefficient (m := m) chi (b⁻¹ * a) =
      (chi b : ZMod m) * coefficient (m := m) chi a := by
  rw [coefficient, coefficient, mul_inv_rev, inv_inv, map_mul, Units.val_mul]
  ring


-- @@ L68-83 verbatim
/-- The projection range is contained in the eigenspace for `chi`. -/
theorem apply_projection
    (rho : D →* M ≃ₗ[ZMod m] M) (chi : D →* (ZMod m)ˣ)
    (b : D) (x : M) :
    rho b (projection (m := m) rho chi x) =
      (chi b : ZMod m) • projection (m := m) rho chi x := by
  calc
    rho b (projection (m := m) rho chi x)
        = ∑ a : D, coefficient (m := m) chi a • rho (b * a) x := by
          simp [projection, map_mul]
    _ = ∑ a : D, coefficient (m := m) chi (b⁻¹ * a) • rho a x := by
          refine Fintype.sum_equiv (Equiv.mulLeft b) _ _ ?_
          intro a
          simp [map_mul]
    _ = (chi b : ZMod m) • projection (m := m) rho chi x := by
          simp [projection, coefficient_inv_mul, smul_smul, Finset.smul_sum]


-- @@ L85-93 verbatim
/-- Elementwise eigenspace statement for the range of the exact finite-level
projection. -/
theorem mem_range_apply
    (rho : D →* M ≃ₗ[ZMod m] M) (chi : D →* (ZMod m)ˣ)
    (b : D) {x : M}
    (hx : x ∈ LinearMap.range (projection (m := m) rho chi)) :
    rho b x = (chi b : ZMod m) • x := by
  obtain ⟨y, rfl⟩ := hx
  exact apply_projection (m := m) rho chi b y


-- @@ L95-100 verbatim
theorem coefficient_mul_character
    (chi : D →* (ZMod m)ˣ) (d : D) :
    coefficient (m := m) chi d * (chi d : ZMod m) =
      (Fintype.card D : ZMod m)⁻¹ := by
  rw [coefficient, mul_assoc, ← Units.val_mul, ← map_mul, inv_mul_cancel, map_one,
    Units.val_one, mul_one]


-- @@ L102-122 verbatim
/-- A finite-level character projection acts as the identity on its own range. -/
theorem projection_apply_eq_self_of_mem_range
    (hcard : IsUnit (Fintype.card D : ZMod m))
    (rho : D →* M ≃ₗ[ZMod m] M) (chi : D →* (ZMod m)ˣ)
    {x : M}
    (hx : x ∈ LinearMap.range (projection (m := m) rho chi)) :
    projection (m := m) rho chi x = x := by
  calc
    projection (m := m) rho chi x
        = ∑ d : D, coefficient (m := m) chi d • rho d x := by
          simp [projection]
    _ = ∑ d : D, coefficient (m := m) chi d •
            ((chi d : ZMod m) • x) := by
          apply Finset.sum_congr rfl
          intro d _hd
          rw [mem_range_apply (m := m) rho chi d hx]
    _ = ∑ _d : D, (Fintype.card D : ZMod m)⁻¹ • x := by
          simp [smul_smul, coefficient_mul_character]
    _ = x := by
          rw [Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul (ZMod m), smul_smul,
            ZMod.mul_inv_of_unit _ hcard, one_smul]


-- @@ L124-131 verbatim
/-- Idempotence of the finite-level character projection. -/
theorem projection_apply_projection
    (hcard : IsUnit (Fintype.card D : ZMod m))
    (rho : D →* M ≃ₗ[ZMod m] M) (chi : D →* (ZMod m)ˣ) (x : M) :
    projection (m := m) rho chi (projection (m := m) rho chi x) =
      projection (m := m) rho chi x :=
  projection_apply_eq_self_of_mem_range
    (m := m) hcard rho chi ⟨x, rfl⟩


-- @@ L133-133 verbatim
end FiniteLevelIdempotent


-- @@ L135-135 verbatim
end SingularKummer

-- @@ L136-136 verbatim
end Reflection

-- @@ L137-137 verbatim
end BernoulliRegular


-- @@ L139-139 verbatim
end


-- @@ L141-141 verbatim
end
