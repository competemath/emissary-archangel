/-
Copyright (c) 2026 Aluna Rizzoli and Adam R. Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aluna Rizzoli, Adam R. Thomas
-/
module

public import LeanPool.CommonNeighbourConjecture.Saxl.PermWreath.Defs


-- @@ L10-16 verbatim
/-!
# The product action of a permutation wreath product

For `g = (f, q)` the action on `ι → Δ` is

`(g • x) i = f i • x (q⁻¹ • i)`.
-/


-- @@ L18-18 verbatim
@[expose] public section


-- @@ L20-20 verbatim
namespace Saxl


-- @@ L22-22 verbatim
variable (X Q ι Δ : Type*)

-- @@ L23-23 verbatim
variable [Group X] [Group Q] [MulAction Q ι]


-- @@ L25-25 verbatim
section Action


-- @@ L27-27 verbatim
variable [MulAction X Δ]


-- @@ L29-43 verbatim
/-- The product action of an arbitrary permutation wreath product. -/
instance permWreathMulAction : MulAction (PermWreath X Q ι) (ι → Δ) where
  smul g x i := g.left i • x (g.right⁻¹ • i)
  one_smul x := by
    funext i
    change (1 : X) • x ((1 : Q)⁻¹ • i) = x i
    simp only [inv_one, one_smul]
  mul_smul g h x := by
    funext i
    change
      (g.left i * h.left (g.right⁻¹ • i)) •
          x ((g.right * h.right)⁻¹ • i) =
        g.left i • (h.left (g.right⁻¹ • i) •
          x (h.right⁻¹ • (g.right⁻¹ • i)))
    simp only [mul_inv_rev, mul_smul]


-- @@ L45-45 verbatim
end Action


-- @@ L47-47 verbatim
section Additive


-- @@ L49-49 verbatim
variable [AddMonoid Δ] [DistribMulAction X Δ]


-- @@ L51-62 verbatim
/-- The product action is additive whenever the component action is additive. -/
instance permWreathDistribMulAction :
    DistribMulAction (PermWreath X Q ι) (ι → Δ) where
  toMulAction := permWreathMulAction X Q ι Δ
  smul_zero g := by
    funext i
    change g.left i • (0 : Δ) = 0
    exact smul_zero _
  smul_add g x y := by
    funext i
    change g.left i • (x (g.right⁻¹ • i) + y (g.right⁻¹ • i)) = _
    exact smul_add _ _ _


-- @@ L64-64 verbatim
end Additive


-- @@ L66-66 verbatim
section Scalars


-- @@ L68-68 verbatim
variable {F : Type*} [MulAction X Δ] [SMul F Δ]

-- @@ L69-69 verbatim
variable [SMulCommClass X F Δ]


-- @@ L71-78 verbatim
/-- The product action commutes with scalars whenever the component action does. -/
instance permWreathSMulCommClass :
    SMulCommClass (PermWreath X Q ι) F (ι → Δ) where
  smul_comm g a x := by
    funext i
    change g.left i • (a • x (g.right⁻¹ • i)) =
      a • (g.left i • x (g.right⁻¹ • i))
    exact smul_comm _ _ _


-- @@ L80-80 verbatim
end Scalars


-- @@ L82-82 verbatim
section CoordinateLemmas


-- @@ L84-84 verbatim
variable [MulAction X Δ]


-- @@ L86-89 verbatim
/-- The defining coordinate formula for the product action. -/
@[simp]
theorem permWreath_smul_apply (g : PermWreath X Q ι) (x : ι → Δ) (i : ι) :
    (g • x) i = g.left i • x (g.right⁻¹ • i) := rfl


-- @@ L91-94 verbatim
/-- Coordinate form of the identity law. -/
theorem one_smul_coord (x : ι → Δ) (i : ι) :
    ((1 : PermWreath X Q ι) • x) i = x i := by
  simp


-- @@ L96-101 verbatim
/-- Fully expanded coordinate form of the multiplication law. -/
theorem mul_smul_coord (g h : PermWreath X Q ι) (x : ι → Δ) (i : ι) :
    ((g * h) • x) i =
      g.left i • (h.left (g.right⁻¹ • i) •
        x (h.right⁻¹ • (g.right⁻¹ • i))) := by
  simp [mul_smul]


-- @@ L103-106 verbatim
/-- A base-group element acts independently in each coordinate. -/
theorem base_smul_coord (f : ι → X) (x : ι → Δ) (i : ι) :
    (PermWreath.base X Q ι f • x) i = f i • x i := by
  simp


-- @@ L108-111 verbatim
/-- A top-group element acts by reindexing the coordinates. -/
theorem top_smul_coord (q : Q) (x : ι → Δ) (i : ι) :
    (PermWreath.top X Q ι q • x) i = x (q⁻¹ • i) := by
  simp


-- @@ L113-113 verbatim
end CoordinateLemmas


-- @@ L115-115 verbatim
end Saxl
