import OAI.NumberTheory.DirichletL.Detector.SourceAmplitudeClasses
import OAI.NumberTheory.DirichletL.Detector.CentralClassPartition


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
namespace SevenEighths.ProbeHighRowFamily

-- @@ L9-9 verbatim
open HeckeFamily HeckeInverseAmplification HeckeDetectorPhysicalSelection

-- @@ L10-10 verbatim
open HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

-- @@ L11-11 verbatim
local notation "O" => HeckeFamily.O

-- @@ L12-12 verbatim
variable (M : Ideal O)

-- @@ L13-13 verbatim
variable (H : Subgroup (O ⧸ M)ˣ)


-- @@ L15-20 verbatim
lemma source_physical_amplitude {N : ℕ} (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d b : ℝ) (z : ℂ) (hZ : 0<Z) (hd : d≠0) (u : FreeRow) (j : Fin N) :
    physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d) u j=
      HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Z^(ell j)) z := by
  unfold physical
  rw [physical_slot_scale ell Z d hZ hd j]


-- @@ L22-31 verbatim
lemma source_rowMean_eq {N : ℕ} (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d b a mesh : ℝ) (z : ℂ) (hZ : 0<Z) (hd : d≠0) (u : FreeRow) :
    rowMean Finset.univ (Z^d) ((2*a-1)/2) mesh (fun j=>ell j/d)
      (physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d)) u=
      weightedMean Finset.univ (fun j=>ell j/d)
        (fun j=>HeckePrimeAmplitudeBins.amplitude (Z^(ell j)) (a-1/2) mesh
          (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Z^(ell j)) z)) := by
  unfold rowMean
  simp_rw [physical_slot_scale ell Z d hZ hd,source_physical_amplitude M H ell W Z d b z hZ hd]
  rw [show (2*a-1)/2=a-1/2 by ring]


-- @@ L33-44 verbatim
lemma source_amplitude_class_mean {N : ℕ} (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d b a mesh : ℝ) (z : ℂ) (hZ : 0<Z) (hd : d≠0) (hm : 0<mesh)
    (rows : Finset FreeRow) (bin : BinLabel (Finset.univ : Finset (Fin N)) ((2*a-1)/2) mesh)
    (u : FreeRow)
    (hu : u∈amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) mesh hm (fun j=>ell j/d)
      (physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d)) bin) :
    weightedMean Finset.univ (fun j=>ell j/d)
      (fun j=>HeckePrimeAmplitudeBins.amplitude (Z^(ell j)) (a-1/2) mesh
        (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Z^(ell j)) z))=
      classMean Finset.univ ((2*a-1)/2) mesh (fun j=>ell j/d) bin := by
  rw [←source_rowMean_eq M H ell W Z d b a mesh z hZ hd u]
  exact rowMean_eq rows Finset.univ (Z^d) ((2*a-1)/2) mesh hm (fun j=>ell j/d) _ bin u hu


-- @@ L46-46 verbatim
end SevenEighths.ProbeHighRowFamily


-- @@ L48-48 verbatim
end


-- @@ L50-50 verbatim
end OAI
