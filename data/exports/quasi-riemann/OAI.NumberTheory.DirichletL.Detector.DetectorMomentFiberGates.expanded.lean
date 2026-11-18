import OAI.NumberTheory.DirichletL.Detector.DetectorMomentGates
import OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
open scoped Classical BigOperators Topology

-- @@ L9-9 verbatim
open Filter

-- @@ L10-10 verbatim
namespace SevenEighths.ProbeHighRowFamily

-- @@ L11-11 verbatim
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource

-- @@ L12-12 verbatim
open HeckeDetectorBatch HeckeDetectorRawFiber HeckeDetectorFiberPartition

-- @@ L13-13 verbatim
local notation "O"=>HeckeFamily.O

-- @@ L14-14 verbatim
variable (M:Ideal O)[NeZero M]

-- @@ L15-15 verbatim
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

-- @@ L16-16 verbatim
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)


-- @@ L18-33 verbatim
theorem sourceMoment_fiber_large_eventually
    (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character)
    {Slot:Type*}[Fintype Slot](ell:Slot→ℝ)(hell:∀s,0<ell s):
    ∀ᶠZ:ℝ in atTop,1≤Z ∧ ∀d:ℝ,0<d→
      ∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch M H (Sum Bool (RayQuotient.Characters M H)) Slot (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S hS η→B.widths=(fun s=>ell s/d)→
      ∀bin j J K,∀hne:(B.fiberRows bin j J K).Nonempty,∀s:Slot,
        ((baseCharacter (B.fiber bin j J K hne).rowData).modulus.absNorm:ℝ)<
          1*(Z^d)^((B.fiber bin j J K hne).widths s):=by
  filter_upwards [sourceMoment_large_eventually M H hH S hS η ell hell] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d hd a ε tstar T allowance i B hdata hw bin j J K hne s
  change ((baseCharacter (B.data j)).modulus.absNorm:ℝ)<1*(Z^d)^(B.widths s)
  rw [hdata,hw,one_mul]
  exact hZ.2 d hd j s


-- @@ L35-50 verbatim
theorem sourceMoment_fiber_support {Δ:ℝ}{D:Parameters.HighData Δ}
    (F:ProbeFinalAssembly.SourceData D)
    {Slot:Type*}{U a ε tstar T allowance:ℝ}{i:ℕ}
    (B:Batch M H (Sum Bool (RayQuotient.Characters M H)) Slot U a ε tstar T allowance i)
    (hprofile:B.profile=(fun _=>(F.W:ℝ→ℂ)))(hupper:B.upper=(fun _=>2))
    (bin:B.Bin)(j:Sum Bool (RayQuotient.Characters M H))
    (J K:Fin (HeckeDetectorWitnessRows.dyadicLength U))
    (hne:(B.fiberRows bin j J K).Nonempty):
    ∀s x,(B.fiber bin j J K hne).profile s x≠0→
      x∈Set.Icc 1 ((B.fiber bin j J K hne).upper s):=by
  intro s x hx
  change B.profile s x≠0 at hx
  change x∈Set.Icc 1 (B.upper s)
  rw [hprofile] at hx
  rw [hupper]
  exact F.complex_support hx


-- @@ L52-52 verbatim
end SevenEighths.ProbeHighRowFamily


-- @@ L54-54 verbatim
end


-- @@ L56-56 verbatim
end OAI
