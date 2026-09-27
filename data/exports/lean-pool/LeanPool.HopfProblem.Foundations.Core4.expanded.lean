/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import LeanPool.HopfProblem.Prelude
public import LeanPool.HopfProblem.Toric.CuspHoneycombHexagon
import all LeanPool.HopfProblem.Toric.CuspHoneycombHexagon


-- @@ L12-16 verbatim
/-!
# Hopf problem: foundations · core 4

Supporting definitions and proofs for this stage of the six-sphere construction.
-/



-- @@ L19-19 verbatim
open Set Function Filter Manifold Topology


-- @@ L21-24 verbatim
open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane


-- @@ L26-26 verbatim
universe u v


-- @@ L28-28 verbatim
noncomputable section


-- @@ L30-30 verbatim
namespace Mathoverflow1973


-- @@ L32-32 verbatim
local infixr:80 " ≫ₚ " => Path.trans


-- @@ L34-34 verbatim
local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f


-- @@ L36-63 verbatim
private theorem
    covering_monodromy_naturality {E F X Y : Type*} [TopologicalSpace E] [TopologicalSpace F]
    [TopologicalSpace X] [TopologicalSpace Y] {p : E → X} {q : F → Y} (hp : IsCoveringMap p)
    (hq : IsCoveringMap q) (r : ContinuousMap E F) (f : ContinuousMap X Y)
    (hcomm : ∀ z, q (r z) = f (p z)) (e : E) (γ : Path.Homotopic.Quotient (p e) (p e)) :
    (hq.monodromy (γ.map f) ⟨r e, hcomm e⟩ : F) = r (hp.monodromy γ ⟨e, rfl⟩ : E) := by
  let e' : p ⁻¹' {p e} := hp.monodromy γ ⟨e, rfl⟩
  let f' : q ⁻¹' {f (p e)} := ⟨r e', (hcomm e').trans (congrArg f e'.property)⟩
  have hc : (ContinuousMap.mk q hq.continuous).comp r = f.comp ⟨p, hp.continuous⟩ :=
    ContinuousMap.ext hcomm
  have he : hq.monodromy (γ.map f) ⟨r e, hcomm e⟩ = f' := by
    apply hq.monodromy_eq_of_map_eq ((hp.liftPathQuotient γ ⟨e, rfl⟩).map r)
    apply eq_of_heq
    have hmap {f₁ f₂ : ContinuousMap E Y} (h : f₁ = f₂) :
      HEq ((hp.liftPathQuotient γ ⟨e, rfl⟩).map f₁) ((hp.liftPathQuotient γ ⟨e, rfl⟩).map f₂) := by
      subst f₂
      rfl
    apply (heq_of_eq Path.Homotopic.Quotient.map_comp.symm).trans
    apply (hmap hc).trans
    rw [Path.Homotopic.Quotient.map_comp, hp.map_liftPathQuotient]
    have hm :
      (γ.cast rfl (show p e' = p e from e'.property)).map f =
        (γ.map f).cast rfl (congrArg f e'.property) :=
      Path.Homotopic.Quotient.map_cast γ
    apply (heq_of_eq hm).trans
    exact
      Path.Homotopic.Quotient.cast_heq _ _ |>.trans (Path.Homotopic.Quotient.cast_heq _ _).symm
  exact congrArg Subtype.val he


-- @@ L65-85 verbatim
/-- The multiplicative equivalence on fundamental groups induced by a homeomorphism. -/
public
def homeomorphFundamentalGroupEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (x : X) : FundamentalGroup X x ≃* FundamentalGroup Y (e x)
    where
  __ := FundamentalGroup.map ⟨e, e.continuous⟩ x
  invFun := FundamentalGroup.mapOfEq ⟨e.symm, e.symm.continuous⟩ (e.symm_apply_apply x)
  left_inv
    γ := by
    rw [FundamentalGroup.mapOfEq_apply]
    obtain ⟨γ⟩ := γ
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact e.symm_apply_apply (γ t)
  right_inv
    γ := by
    rw [FundamentalGroup.mapOfEq_apply]
    obtain ⟨γ⟩ := γ
    apply congrArg Path.Homotopic.Quotient.mk
    ext t
    exact e.apply_symm_apply (γ t)


-- @@ L87-87 verbatim
end Mathoverflow1973


-- @@ L89-89 verbatim
end
