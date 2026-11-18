import OAI.NumberTheory.DirichletL.Reflection.Reindex
import OAI.NumberTheory.DirichletL.Descent.ReflectedDual


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
namespace SevenEighths.InverseReflectedPhase

-- @@ L7-7 verbatim
open scoped Classical BigOperators

-- @@ L8-8 verbatim
open ActualEisensteinCubic CubicEisenstein CompletedGauss InverseMoment

-- @@ L9-9 verbatim
noncomputable section

-- @@ L10-10 verbatim
local notation "Eis" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

-- @@ L12-12 verbatim
variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ι→Eis} {N a c : Eis} {mode : Bool}


-- @@ L14-17 verbatim
lemma reindexControlled_matrix_one (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι) :
    (reindexControlled D e).matrix (fun _ => 1)=D.matrix (fun _ => 1) := by
  change D.matrix (unitFrequencyEquiv p e (fun _ => 1))=_
  rw [unitFrequencyEquiv_one]


-- @@ L19-22 verbatim
lemma reindexControlled_fixedFactor (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι) :
    (reindexControlled D e).fixedFactor=D.fixedFactor := by
  unfold ControlledStratumArithmetic.fixedFactor
  rw [reindexControlled_matrix_one]


-- @@ L24-25 verbatim
lemma reindexControlled_U (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι) :
    (reindexControlled D e).U=D.U := rfl


-- @@ L27-27 verbatim
def reindexMarks (e : κ≃ι) (S : Finset ι) : Finset κ := Finset.univ.filter (fun k => e k∈S)


-- @@ L29-31 verbatim
omit [Fintype ι] in
lemma mem_reindexMarks (e : κ≃ι) (S : Finset ι) (k : κ) : k∈reindexMarks e S ↔ e k∈S := by
  simp [reindexMarks]


-- @@ L33-40 verbatim
lemma mixedActiveBracket_reindex [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι)
    (hp : ∀ i, p i≠0) (hg : ∀ i, λ₀∉Ideal.span {p i})
    (j : ι→ℕ) (S : Finset ι) (k : κ) (x : Eis) :
    mixedActiveBracket (fun k => hp (e k)) (fun k => hg (e k)) (fun k => j (e k))
      (reindexMarks e S) (reindexControlled D e) k x =mixedActiveBracket hp hg j S D (e k) x := by
  simp only [mixedActiveBracket,mem_reindexMarks]
  rfl


-- @@ L42-55 verbatim
theorem mixedReflectedValue_reindex [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode) (e : κ≃ι)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i≠0) (hc : c≠0) (hg : ∀ i, λ₀∉Ideal.span {p i})
    (j : ι→ℕ) (S : Finset ι) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (reindexControlled D e) s (fun k => hp (e k)) hc (fun k => hg (e k))
      (fun k => j (e k)) (reindexMarks e S) W X =mixedReflectedValue D s hp hc hg j S W X := by
  have hprod (x : Eis) :
      (∏ k, mixedActiveBracket (fun k => hp (e k)) (fun k => hg (e k)) (fun k => j (e k))
        (reindexMarks e S) (reindexControlled D e) k x)=∏ i, mixedActiveBracket hp hg j S D i x := by
    simp_rw [mixedActiveBracket_reindex]
    exact e.prod_comp (fun i => mixedActiveBracket hp hg j S D i x)
  simp only [mixedReflectedValue,e.prod_comp p,reindexControlled_fixedFactor,
    reindexControlled_matrix_one,reindexControlled_U,hprod]

-- @@ L56-56 verbatim
end

-- @@ L57-57 verbatim
end SevenEighths.InverseReflectedPhase


-- @@ L59-59 verbatim
end OAI
