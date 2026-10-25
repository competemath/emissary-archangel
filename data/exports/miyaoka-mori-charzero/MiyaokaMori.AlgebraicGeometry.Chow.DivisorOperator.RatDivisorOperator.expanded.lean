import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.ChowGroupRatCongr
import MiyaokaMori.Algebra.ChowRatExtend
import MiyaokaMori.AlgebraicGeometry.Chow.CapCommutes
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupRational
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle


-- @@ L10-16 verbatim
/-! # ℚ-divisor operators on Chow groups

Divisor classes with ℚ-coefficients as dimension-lowering operators `RatDivisorOp X` on the Chow groups
(both `H^sp` and `π^*c_1(Q_i)` of Proposition 2.4 of the paper are such operators; their
sums are no longer the `c_1` of a line bundle, hence this layer), with addition, ℚ-scalar
multiplication, powers `capPow` and finite products `capProd`. Source: Fulton, Intersection Theory,
Chapter 2. -/


-- @@ L18-18 verbatim
set_option autoImplicit false

-- @@ L19-19 verbatim
set_option maxHeartbeats 400000


-- @@ L21-21 verbatim
universe u v w u' v'


-- @@ L23-23 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L24-24 verbatim
open scoped AlgebraicGeometry


-- @@ L26-26 verbatim
noncomputable section


-- @@ L28-30 verbatim
/-- A ℚ-divisor operator: a family of ℚ-linear maps `CH_{d+1}(X)_ℚ → CH_d(X)_ℚ`, one for each `d`. -/
abbrev AlgebraicGeometry.RatDivisorOp (X : AlgebraicGeometry.Scheme.{u}) : Type u :=
  ∀ d : ℕ, AlgebraicGeometry.ChowGroupRat X (d + 1) →ₗ[ℚ] AlgebraicGeometry.ChowGroupRat X d


-- @@ L32-33 verbatim
noncomputable instance (X : AlgebraicGeometry.Scheme.{u}) :
    Module ℚ (AlgebraicGeometry.RatDivisorOp X) := inferInstance


-- @@ L35-39 verbatim
/-- The first Chern class of a line bundle as a ℚ-divisor operator. -/

noncomputable def AlgebraicGeometry.ratDivisorOpOfLineBundle {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] : AlgebraicGeometry.RatDivisorOp X :=
  fun d => (AlgebraicGeometry.firstChernClass L (d + 1)).ratExtend


-- @@ L41-47 verbatim
/-- The power `H^e` of a single operator: by recursion on `e`, lowering the dimension from `d + e` to `d`. -/

noncomputable def AlgebraicGeometry.RatDivisorOp.capPow {X : AlgebraicGeometry.Scheme.{u}}
    (D : AlgebraicGeometry.RatDivisorOp X) : (e d : ℕ) →
    AlgebraicGeometry.ChowGroupRat X (d + e) →ₗ[ℚ] AlgebraicGeometry.ChowGroupRat X d
  | 0, _ => LinearMap.id
  | e + 1, d => (AlgebraicGeometry.RatDivisorOp.capPow D e d).comp (D (d + e))


-- @@ L49-56 verbatim
/-- Successive caps with a list of operators: the list `[D_1, …, D_ℓ]` lowers the dimension from `d + ℓ`
to `d` (the head of the list acts first). -/

noncomputable def AlgebraicGeometry.RatDivisorOp.capList {X : AlgebraicGeometry.Scheme.{u}} :
    (l : List (AlgebraicGeometry.RatDivisorOp X)) → (d : ℕ) →
    AlgebraicGeometry.ChowGroupRat X (d + l.length) →ₗ[ℚ] AlgebraicGeometry.ChowGroupRat X d
  | [], _ => LinearMap.id
  | D :: l, d => (AlgebraicGeometry.RatDivisorOp.capList l d).comp (D (d + l.length))


-- @@ L58-66 verbatim
/-- The product of a finite family: successive caps in the order of `Finset.univ.toList`, lowering the
dimension from `d + card ι` to `d`. -/

noncomputable def AlgebraicGeometry.RatDivisorOp.capProd {X : AlgebraicGeometry.Scheme.{u}}
    {ι : Type*} [Fintype ι] [DecidableEq ι] (D : ι → AlgebraicGeometry.RatDivisorOp X) (d : ℕ) :
    AlgebraicGeometry.ChowGroupRat X (d + Fintype.card ι) →ₗ[ℚ]
      AlgebraicGeometry.ChowGroupRat X d :=
  (AlgebraicGeometry.RatDivisorOp.capList ((Finset.univ : Finset ι).toList.map D) d).comp
    (AlgebraicGeometry.ChowGroupRat.congr X (by simp [Finset.length_toList]))


-- @@ L68-68 verbatim
end
