import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Data.ZMod.Basic


-- @@ L8-8 verbatim
set_option autoImplicit false


-- @@ L10-10 verbatim
namespace LanglandsTunnell


-- @@ L12-12 verbatim
local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)


-- @@ L14-15 verbatim
variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
  [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower ℚ L (AlgebraicClosure ℚ)]


-- @@ L17-19 verbatim
noncomputable def galRep (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Γℚ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  e.toMonoidHom.comp (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) L)


-- @@ L21-23 verbatim
@[simp] theorem galRep_apply (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (σ : Γℚ) :
    galRep e σ = e (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) L σ) := rfl


-- @@ L25-26 verbatim
def IsRelDegree {G : Type*} [Group G] (H : Subgroup G) (σ : G) (n : ℕ) : Prop :=
  0 < n ∧ σ ^ n ∈ H ∧ ∀ m : ℕ, 0 < m → m < n → σ ^ m ∉ H


-- @@ L28-29 verbatim
theorem isRelDegree_one_top {G : Type*} [Group G] (σ : G) : IsRelDegree (⊤ : Subgroup G) σ 1 :=
  ⟨Nat.one_pos, trivial, fun m _ hm => absurd hm (by omega)⟩


-- @@ L31-31 verbatim
end LanglandsTunnell
