import OAI.NumberTheory.DirichletL.Inversion.InitialCommonTuples


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators Classical

-- @@ L8-8 verbatim
open ActualEisensteinCubic CanonicalQuadraticSieve

-- @@ L9-9 verbatim
namespace SevenEighths.InverseInitialCommonRatios

-- @@ L10-10 verbatim
open InverseInitialOverlap InverseInitialKernelBridge

-- @@ L11-11 verbatim
local notation "Eis"=>ActualEisensteinCubic.O

-- @@ L12-12 verbatim
variable {σ:Type*} [DecidableEq σ]


-- @@ L14-15 verbatim
def survivingProduct (I:Finset σ)(q:∀i∈I,Ideal Eis) : Ideal Eis :=
  ∏i∈I.attach,q i.val i.property


-- @@ L17-20 verbatim
omit [DecidableEq σ] in
theorem actual_residual_product (I:Finset σ)(q:∀i∈I,Ideal Eis)
    (j:Ideal Eis)(hj:j≠0) : residual (j*survivingProduct I q) j=survivingProduct I q :=
  quotient_mul_cancel hj


-- @@ L22-34 verbatim
omit [DecidableEq σ] in
theorem residual_ratio_product (I:Finset σ)(q:∀i∈I,Ideal Eis)
    (j:Ideal Eis)(hj:j≠0)(ell:σ→ℝ)(Z z G:ℝ)(hZ:0<Z)
    (hell:∑i∈I,ell i=z-G) :
    ((residual (j*survivingProduct I q) j).absNorm:ℝ)/Z^(z-G)=
      ∏i∈I.attach,((q i.val i.property).absNorm:ℝ)/Z^(ell i.val) := by
  rw [actual_residual_product I q j hj,Finset.prod_div_distrib]
  have hp : (∏i∈I.attach,Z^(ell i.val))=Z^(z-G) := by
    rw [←Real.rpow_sum_of_pos hZ]
    rw [Finset.sum_attach,hell]
  rw [hp]
  congr 1
  simp only [survivingProduct,map_prod,Nat.cast_prod]


-- @@ L36-45 verbatim
omit [DecidableEq σ] in
theorem original_residual_window (I:Finset σ)(q:∀i∈I,Ideal Eis)
    (j:Ideal Eis)(hj:j≠0)(ell:σ→ℝ)(W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0<Z)
    (hell:∑i∈I,ell i=z-G)(c:Ideal Eis) :
    residualOverlapWindow (j*survivingProduct I q) j W Z z G
      ((c.absNorm:ℝ)/Z^(r+z-2*G))=
      W (((j.absNorm:ℝ)/Z^G)*((c.absNorm:ℝ)/Z^(r+z-2*G))/
        (∏i∈I.attach,((q i.val i.property).absNorm:ℝ)/Z^(ell i.val))) := by
  unfold residualOverlapWindow
  rw [residual_ratio_product I q j hj ell Z z G hZ hell]


-- @@ L47-47 verbatim
end SevenEighths.InverseInitialCommonRatios


-- @@ L49-49 verbatim
end


-- @@ L51-51 verbatim
end OAI
