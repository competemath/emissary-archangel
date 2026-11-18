import OAI.NumberTheory.DirichletL.Inversion.InitialResidualTupleEnergy
import OAI.NumberTheory.DirichletL.Inversion.InitialUniformFresh
import OAI.NumberTheory.DirichletL.Inversion.InitialResidualPool


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-7 verbatim
noncomputable section


-- @@ L9-9 verbatim
open scoped Classical BigOperators SchwartzMap ContDiff

-- @@ L10-10 verbatim
namespace SevenEighths.InverseInitialResidualUniformEnergy

-- @@ L11-11 verbatim
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT

-- @@ L12-12 verbatim
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass

-- @@ L13-13 verbatim
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile

-- @@ L14-14 verbatim
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows

-- @@ L15-15 verbatim
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState

-- @@ L16-16 verbatim
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter

-- @@ L17-17 verbatim
local notation "O"=>ActualEisensteinCubic.O


-- @@ L19-19 verbatim
open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment

-- @@ L20-20 verbatim
open MeasureTheory FourierBridge JointLogSeparation InverseInitialOverlapFourier

-- @@ L21-21 verbatim
open InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonTuples

-- @@ L22-22 verbatim
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialExcludedPool

-- @@ L23-23 verbatim
open InverseInitialCommonProfile InverseInitialEnergyCallerWindow

-- @@ L24-92 verbatim
theorem original_residual_uniform_energy
    (Woriginal:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hso:Function.support Woriginal⊆Set.Icc ao bo)(hWo:ContDiff ℝ ∞ Woriginal)
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(L:σ→Finset (Ideal O))(Hslot:σ→ℝ)(coeff:σ→Ideal O→ℂ),
      (all:Set σ).PairwiseDisjoint L→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈L i,(P.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈L i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀χ:Ideal O→*ℂ,(∀u,‖elementCharacter χ u‖≤1)→
      FactorsModulo (fixedBaseConductor q) (elementCharacter χ)→
      (∀c,¬outside (reflectionExcludedPrimes q) c→χ c=0)→
    ∀(D m r:ℝ),0≤m→m≤cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤cap→
    ∀(rows:Finset O),(∀u∈rows,‖eisEmbedding u‖^2≤Z^m)→
    ∀(j:Ideal O),Admissible j→Ideal.span {assignedElement assigned qelem}=j→
      ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))∈Set.Icc (1:ℝ) ((2:ℝ)^K)→
      (∀i∈all\assigned,∀P∈L i,Prime P)→
      (∀i∈all\assigned,∀P∈L i,coeff i P≠0→slotRatio Z z i P∈Set.Icc (1:ℝ) 2)→
      (∀t∈(all\assigned).pi L,Admissible (j*survivingProduct (all\assigned) t))→
      (∀t∈(all\assigned).pi L,Pairwise (Function.onFun IsCoprime
        (fun i:↥(all\assigned)=>t i.val i.property)))→
      (∀t∈(all\assigned).pi L,outside (reflectionExcludedPrimes q)
        (j*survivingProduct (all\assigned) t))→
    ∀θ:ℝ,
      (∑u∈rows,‖∑t∈(all\assigned).pi L,
        (∏i∈(all\assigned).attach,coeff i.val (t i.val i.property))*
        residualNormalizedPolynomial (originalSource Z r bo)
          (j*survivingProduct (all\assigned) t) j χ (fun _=>1)
          (childLogTest Woriginal θ) Z r (assignedCenter all z) (assignedCenter assigned z) u‖^2)≤
        C*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨W,A,B,Bnorm,hA,hAB,hBn,hWc,hWs,hWb,hFresh⟩:=
    InverseInitialUniformFresh.exists_uniform_fresh K ao bo hao hab
  have hs:Function.support (W:ℝ→ℂ)⊆Set.Icc A B:=(subset_tsupport (W:ℝ→ℂ)).trans hWs
  obtain ⟨J,Btree,hBtree,henergy⟩:=InverseInitialResidualTupleEnergy.original_residual_tuple_energy
    Woriginal W ao bo hao hso hWo A B 1 hA le_rfl hs (W.smooth ⊤) Φ hΦ hone Bnorm hBn hWb
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  refine ⟨J,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩:=henergy q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ σ dec all assigned hassigned hK L Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive χ hχ hperiod hout
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows
    j hj hspan hjratio hL hcoeff hP hcopTuple hPE θ
  have hZp:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  obtain ⟨Dpool,hfloor,hcover⟩:=InverseInitialResidualPool.exists_original_complete_pool
    q Z r bo cap Btree hZp (zero_le_one.trans hBtree) ((all\assigned).pi L)
    (fun t=>j*survivingProduct (all\assigned) t) j hP (fun t _=>dvd_mul_right j _) hPE
  exact henergy Z hZ Dpool hfloor all assigned hassigned hK L Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive χ hχ hperiod hout
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows
    j hj hspan (fun _=>1) (fun _=>2) 1 ((2:ℝ)^K) hjratio hL hcoeff
    (hFresh (all\assigned) ((Finset.card_le_card Finset.sdiff_subset).trans hK) Woriginal hso)
    hP hcopTuple hPE hcover θ


-- @@ L94-94 verbatim
end SevenEighths.InverseInitialResidualUniformEnergy


-- @@ L96-96 verbatim
end


-- @@ L98-98 verbatim
end OAI
