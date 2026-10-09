import OAI.RepresentationTheory.FoulkesHowe.FirstLabels
import OAI.RepresentationTheory.FoulkesHowe.FlattenedForm
import OAI.RepresentationTheory.FoulkesHowe.MultilinearPolynomial
import OAI.RepresentationTheory.FoulkesHowe.EncodingHomogeneous
import OAI.RepresentationTheory.FoulkesHowe.BlockWeight


-- @@ L7-7 verbatim
namespace OAI


-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
open scoped BigOperators

-- @@ L11-11 verbatim
namespace Problem346

-- @@ L12-12 verbatim
universe u v

-- @@ L13-13 verbatim
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

-- @@ L14-14 verbatim
variable {κ : Type v} [Fintype κ]


-- @@ L16-20 verbatim
/-- The scalar polynomial at the k-th stage of the first transfer sequence. -/
def firstPolynomial {r m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (e : κ → V) (k : ℕ) :
    MvPolynomial (FirstBlock m × κ) ℂ :=
  multilinearPolynomial (flattenedForm T) e (firstLabel r m k)


-- @@ L22-33 verbatim
/-- Direct block degrees of every intermediate polynomial, by counting its labels. -/
theorem firstPolynomial_blockHomogeneous {r m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (e : κ → V)
    (k : ℕ) (u : FirstBlock m) :
    PolynomialWeights.IsBlockHomogeneous u (firstPolynomial T e k)
      (Finset.univ.filter (fun p => firstLabel r m k p = u)).card := by
  classical
  let : DecidableEq (Fin (r+1) × Fin (r+m)) := Classical.decEq _
  unfold PolynomialWeights.IsBlockHomogeneous PolynomialWeights.blockWeight
  simpa only [firstPolynomial, multilinearPolynomial] using
    (EncodingDegree.blockHomogeneous_expansion
      (fun z => flattenedForm T (fun p => e (z p))) (firstLabel r m k) u)


-- @@ L35-35 verbatim
end Problem346


-- @@ L37-37 verbatim
end


-- @@ L39-39 verbatim
end OAI
