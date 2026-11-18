import OAI.NumberTheory.DirichletL.PrimeRows.DetectorReady
import OAI.NumberTheory.DirichletL.Hecke.DetectorSupportedWitness


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical Topology

-- @@ L8-8 verbatim
open Filter

-- @@ L9-9 verbatim
namespace SevenEighths.ProbeHighRowFamily

-- @@ L10-10 verbatim
open HeckeFamily HeckeInverseAmplification ProbePhysical

-- @@ L11-11 verbatim
open HeckeDetectorSupportedWitness

-- @@ L12-12 verbatim
local notation "O" => HeckeFamily.O

-- @@ L13-13 verbatim
variable (M : Ideal O) [NeZero M]

-- @@ L14-14 verbatim
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L15-15 verbatim
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

-- @@ L16-16 verbatim
variable (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal) (η : Character)


-- @@ L18-49 verbatim
theorem supported_witnesses_from_source_cube (dmin dmax τ ε e κ heightCost margin : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*heightCost)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤heightCost)
    (hmargin : 0<margin)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠ Z : ℝ in atTop,∀ d : ℝ,dmin≤d → d≤dmax →
      ∀ (U : ℝ) (rows : Finset FreeRow),rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤Z^(d-margin)) →
      let χ := fun u : rows => sourceDetectorFamily S hS.prime η u.val (rayCubeFamily M H hH u.val)
      ∀(a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
        (∀u : rows,detectorMaximum (χ u) (3*(i+1 : ℕ)*(Z^τ))<a+2*e) →
        (∀u : rows,a≤detectorMaximum (χ u) ((3*i : ℕ)*Z^τ)) →
        ∀ tstar : ℝ,1≤tstar → tstar≤3/2 →
          Nonempty (∀u : rows,SupportedWitness (χ u) (Z^d) a ε tstar (Z^τ)
            ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z0,hdet⟩ := actual_supported_witness_family dmin dmax τ ε e κ heightCost I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hheightCost hbudget
  filter_upwards [eventually_ge_atTop Z0,
    source_ray_nonprincipal_eventually M H hH S hS hmax η (1/100) (by norm_num),
    source_ray_conductor_eventually M H hH S hS.prime η margin hmargin] with Z hZ hnp hcond
  intro d hd hd' U rows hrows hcal hrow
  dsimp only
  intro a i hi ha ha' hnext hcurrent tstar ht ht'
  let χ := fun u : rows => sourceDetectorFamily S hS.prime η u.val (rayCubeFamily M H hH u.val)
  have hχ : ∀u j,(χ u j).residue≠1 := fun u=>hnp U u.val (hrows u.property) (hcal u.val u.property)
  have heq (u : rows) := detectorMaximum_eq_nonprincipal (χ u) (hχ u)
  exact hdet Z hZ d hd hd' χ hχ a i hi ha ha'
    (fun u=>by rw [←heq u];exact hnext u)
    (fun u=>by rw [←heq u];exact hcurrent u)
    (fun u=>hcond u.val d (hrow u.val u.property)) tstar ht ht'


-- @@ L51-51 verbatim
end SevenEighths.ProbeHighRowFamily


-- @@ L53-53 verbatim
end


-- @@ L55-55 verbatim
end OAI
