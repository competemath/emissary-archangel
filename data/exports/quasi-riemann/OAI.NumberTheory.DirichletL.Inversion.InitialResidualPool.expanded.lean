import OAI.NumberTheory.DirichletL.Inversion.InitialExcludedPool
import OAI.NumberTheory.DirichletL.Inversion.InitialEnergyCallerWindow


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section


-- @@ L8-8 verbatim
open scoped Classical BigOperators

-- @@ L9-9 verbatim
namespace SevenEighths.InverseInitialResidualPool

-- @@ L10-10 verbatim
open ActualEisensteinCubic CanonicalQuadraticSieve CanonicalRowCompletion

-- @@ L11-11 verbatim
open InverseInitialExcludedPool InverseInitialCommonTuples InverseInitialEnergyCallerWindow

-- @@ L12-12 verbatim
local notation "O"=>ActualEisensteinCubic.O


-- @@ L14-25 verbatim
theorem exists_original_complete_pool {κ:Type*}
    (q:ℕ)(Z r b cap Btree:ℝ)(hZ:0<Z)(hBtree:0≤Btree)
    (T:Finset κ)(P:κ→Ideal O)(j:Ideal O)
    (hP:∀k∈T,Admissible (P k))(hj:∀k∈T,j∣P k)
    (hPE:∀k∈T,outside (reflectionExcludedPrimes q) (P k)):
    ∃Dpool:ℕ,Btree*Z^(cap+1)≤Dpool ∧
      tupleColumns (originalOutside (originalSource Z r b) (reflectionExcludedPrimes q)) T P j⊆
        InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool:=by
  obtain ⟨D,hcover,hsize⟩:=exists_excluded_complete_pool (originalSource Z r b)
    (reflectionExcludedPrimes q) T P j (reflectionExcludedPrimes_prime q) hP hj hPE
    (originalSource_supported Z r b) Btree (Z^(cap+1)) hBtree (Real.rpow_nonneg hZ.le _)
  exact ⟨D,hsize Btree (Z^(cap+1)) hBtree le_rfl (Real.rpow_nonneg hZ.le _) le_rfl,hcover⟩


-- @@ L27-27 verbatim
end SevenEighths.InverseInitialResidualPool


-- @@ L29-29 verbatim
end


-- @@ L31-31 verbatim
end OAI
