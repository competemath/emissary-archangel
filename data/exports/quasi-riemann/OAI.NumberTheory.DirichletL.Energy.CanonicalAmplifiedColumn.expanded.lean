import OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedFourCoefficients
import OAI.NumberTheory.DirichletL.Moments.FirstAnnularMajorant


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators SchwartzMap


-- @@ L9-9 verbatim
namespace SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn

-- @@ L10-10 verbatim
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT ConcretePrimeRowBridge

-- @@ L11-11 verbatim
open CenteredMomentAmplificationChildInput CenteredMomentCommonRadialData

-- @@ L12-12 verbatim
open CenteredMomentFirstPhysicalSource CenteredMomentCommonAllocationSum

-- @@ L13-13 verbatim
open CenteredMomentFirstCommonReferencePower CenteredMomentFirstAmplifiedFourCoefficients

-- @@ L14-14 verbatim
open CenteredMomentPrimeElements CenteredMomentFirstAmplificationChoice

-- @@ L15-15 verbatim
open CenteredMomentSectorLocalization CenteredMomentSecondChildPowerBudget

-- @@ L16-16 verbatim
open CenteredMomentSourceLiveColumn

-- @@ L17-17 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L18-18 verbatim
local notation "Ray"=>RayFourExpansion.RayCharacter

-- @@ L19-19 verbatim
local instance {ι:Type*}:DecidableEq (ι⊕Fin 2):=Classical.decEq _


-- @@ L21-24 verbatim
lemma main_coefficients_nonneg (q Z K ell deficit paid saving r:ℝ)
    (hq:0≤q)(hZ:0≤Z)(hK:0≤K):∀j,0≤mainPowers q Z K ell deficit paid saving r j:=by
  intro j
  fin_cases j <;> simp only [mainPowers,Matrix.cons_val,Fin.reduceFinMk] <;> positivity


-- @@ L26-29 verbatim
lemma error_coefficients_nonneg (p:O)(k:ℕ)(q Z K deficit paid saving r:ℝ)
    (hq:0≤q)(hZ:0≤Z)(hK:0≤K):∀j,0≤errorPowers p k q Z K deficit paid saving r j:=by
  intro j
  fin_cases j <;> simp only [errorPowers,Matrix.cons_val,Fin.reduceFinMk] <;> positivity


-- @@ L31-82 verbatim
theorem common_annular_reference_powers (N:ℕ)(a b ε:ℝ)(ha:0<a)(hb:1≤b)(hε:0<ε):
    ∃Cb:ℝ,0<Cb ∧ ∀{ι:Type*}[Fintype ι],∀s:Input ι,
    Fintype.card ι≤N→a≤s.lower→s.upper≤b→
    ∀(C R seed:Ideal O)(hC:Supported C),seed∣C→
    ∀(τ:Character)(t:ℝ)(L:Ideal O)(H0 Z allowance:ℝ),0<H0→0<Z→
    ∀(P:Finset (Ideal O))(mainFactor:ℝ)(H:Fin 4→ℝ),0≤mainFactor→(∀j,0≤H j)→
    ∀(Kmain ell deficit paid saving rmain:ℝ),0≤Kmain→
    ∀(Kerror rerror:elementPool P→Fin 3→Ray→ℝ),(∀p i χ,0≤Kerror p i χ)→
    let q:ℝ:=τ.modulus.absNorm;
    let amain:=fun j=>H j*mainPowers q Z Kmain ell deficit paid saving rmain j;
    let aerror:=fun (p:elementPool P)(i:Fin 3)(χ:Ray)(j:Fin 4)=>
      H j*errorPowers p (errorIndex i+1) q Z (Kerror p i χ) deficit paid saving (rerror p i χ) j;
    (∀B:actualAllocations s.pools C,frozenCoefficient B.val C R s.ν s.W s.P≠0→
      childNormalizedGaussSource s C R L B τ t CenteredMomentFirstAnnularMajorant.profile H0≤
        (∑j,sourceCoefficients P mainFactor amain aerror (powers ε) j*
          (volume (child s C R B τ t))^(powers ε j))*
          CenteredMomentFirstChildProfileControl.mass (child s C R B τ t)^2)→
    (commonEnergy (original s R seed) C hC τ t L CenteredMomentFirstAnnularMajorant.profile H0).re≤
      reference q (volume s) (C.absNorm:ℝ) Z allowance*
        (Cb*CenteredMomentFirstChildProfileControl.mass s^2*
          ∑j,(C.absNorm:ℝ)^ε*(b^N)^(powers ε j)*
            averagedCoefficients P mainFactor H
              (mainCores q (volume s) (C.absNorm:ℝ) Z allowance Kmain ell deficit paid ε saving rmain)
              (fun p i χ=>errorCores p (errorIndex i+1) q (volume s) (C.absNorm:ℝ)
                Z allowance (Kerror p i χ) deficit paid ε saving (rerror p i χ)) j):=by
  obtain ⟨Cb,hCb,hbound⟩:=common_energy_reference_powers N a b ε ha hb hε
  refine ⟨Cb,hCb,?_⟩
  intro ι _ s hc hlo hhi C R seed hC hseed τ t L H0 Z allowance hH0 hZ
    P mainFactor H hmain hH Kmain ell deficit paid saving rmain hKmain Kerror rerror hKerror
  dsimp only
  intro hchildren
  have hq:0<(τ.modulus.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ τ.modulus_ne_bot
  have hNC:0<(C.absNorm:ℝ):=CenteredMomentFirstScale.norm_pos _ hC.1
  have hcoeff:=source_coefficients_nonneg P mainFactor hmain
    (fun j=>H j*mainPowers (τ.modulus.absNorm:ℝ) Z Kmain ell deficit paid saving rmain j)
    (fun p i χ j=>H j*errorPowers p (errorIndex i+1) (τ.modulus.absNorm:ℝ) Z
      (Kerror p i χ) deficit paid saving (rerror p i χ) j) (powers ε)
    (fun j=>mul_nonneg (hH j) (main_coefficients_nonneg _ _ _ _ _ _ _ _ hq.le hZ.le hKmain j))
    (fun p i χ j=>mul_nonneg (hH j) (error_coefficients_nonneg _ _ _ _ _ _ _ _ _
      hq.le hZ.le (hKerror p i χ) j))
  have hh:=hbound s hc hlo hhi C R seed hC hseed τ t L
    CenteredMomentFirstAnnularMajorant.profile H0 Z allowance hH0 hZ
    (fun z=>CenteredMomentFirstAnnularMajorant.profile_nonneg _) 4 _ (powers ε)
    hcoeff (powers_nonneg ε hε.le) hchildren
  apply hh.trans_eq
  unfold reference
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  exact actual_power_reference_identity P mainFactor b (volume s) (C.absNorm:ℝ)
    (τ.modulus.absNorm:ℝ) Z allowance ε N H Kmain ell deficit paid saving rmain Kerror rerror
    (volume_pos s) hNC hq hZ j


-- @@ L84-84 verbatim
end SevenEighths.CenteredMomentEnergyCanonicalAmplifiedColumn


-- @@ L86-86 verbatim
end


-- @@ L88-88 verbatim
end OAI
