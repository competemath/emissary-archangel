import OAI.NumberTheory.DirichletL.Descent.CanonicalLongParent


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
open scoped BigOperators Classical

-- @@ L8-8 verbatim
namespace SevenEighths.InverseMoment

-- @@ L9-9 verbatim
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic

-- @@ L10-10 verbatim
open InverseFirstGlobalCaps InverseSecondSourceBlocks

-- @@ L11-11 verbatim
open InverseMomentFirstOriginalProfile CompletedHeight

-- @@ L12-12 verbatim
local notation "O"=>ActualEisensteinCubic.O


-- @@ L14-28 verbatim
def actualLongSourceKeys {ι σ:Type}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))(Ψ:O→*ℂ)(m mCoef:O)
    (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)(om:ℝ→ℂ)
    (Z M r ell V H₀ ξ Lcap eta tau:ℝ) :=
  let mark:=fun v U=>primeMark slots lists weights (v.support∪U)
  let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=>
    firstDyadicRadius p q C D Z M r ell V eta tau
  let W:=fun y=>normTwistedSource om ξ (y/Z^r)
  let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels)
    (fun x=>x.1) (Z^(2*Lcap+15*eta+tau))
  liveJointKeys p source pool (sourceSummand p hp hcop hg
    (actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) cutoff Ψ m mark W rowMajorant (Z^M))


-- @@ L30-30 verbatim
end SevenEighths.InverseMoment


-- @@ L32-32 verbatim
end


-- @@ L34-34 verbatim
end OAI
