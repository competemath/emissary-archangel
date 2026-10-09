import OAI.RepresentationTheory.FoulkesHowe.Multiplication


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace Problem346


-- @@ L9-9 verbatim
universe u

-- @@ L10-10 verbatim
variable {V : Type u} [AddCommGroup V] [Module ℂ V]


-- @@ L12-22 verbatim
/-- Splitting a list of equal factors at a cutoff is graded multiplication of two pure powers. -/
theorem symMonomial_cut (r m : ℕ) (x y : V) :
    symMonomial (r+m) V (fun j => if j.val < r then x else y) =
      symPowMul r m (symMonomial r V (fun _ => x))
        (symMonomial m V (fun _ => y)) := by
  rw [symPowMul_symMonomial]
  congr 1
  ext j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp
  · simp


-- @@ L24-30 verbatim
/-- Cast-free raw form of the cutoff identity. -/
theorem symMonomialRaw_cut (r m : ℕ) (x y : V) :
    symMonomialRaw (r+m) V (fun j => if j.val < r then x else y) =
      SymmetricAlgebra.ι ℂ V x ^ r * SymmetricAlgebra.ι ℂ V y ^ m := by
  have h := congrArg (fun z : SymPow (r+m) V => (z : SymmetricAlgebra ℂ V))
    (symMonomial_cut r m x y)
  simpa [symMonomial, symPowMul_coe, symMonomialRaw_const] using h


-- @@ L32-41 verbatim
/-- The all-row terminal cutoff in the second transfer matches its common-power product form. -/
theorem multilinear_cut_endpoint (r m : ℕ)
    (T : SymmetricMultilinearForm (r+1) (r+m) V)
    (x t : V) (v : Fin r → V) :
    T (Fin.cons (symMonomial (r+m) V (fun _ => t))
      (fun i => symMonomial (r+m) V (fun j => if j.val < r then x else v i))) =
    T (Fin.cons (symMonomial (r+m) V (fun _ => t))
      (fun i => symPowMul r m (symMonomial r V (fun _ => x))
        (symMonomial m V (fun _ => v i)))) := by
  simp only [symMonomial_cut]


-- @@ L43-53 verbatim
/-- Vanishing on arbitrary residual products gives vanishing on the terminal cutoff. -/
theorem multilinear_cut_endpoint_zero (r m : ℕ)
    (T : SymmetricMultilinearForm (r+1) (r+m) V)
    (h : ∀ x t : V, ∀ Q : Fin r → SymPow m V,
      T (Fin.cons (symMonomial (r+m) V (fun _ => t))
        (fun i => symPowMul r m (symMonomial r V (fun _ => x)) (Q i))) = 0)
    (x t : V) (v : Fin r → V) :
    T (Fin.cons (symMonomial (r+m) V (fun _ => t))
      (fun i => symMonomial (r+m) V (fun j => if j.val < r then x else v i))) = 0 := by
  rw [multilinear_cut_endpoint]
  exact h x t (fun i => symMonomial m V (fun _ => v i))


-- @@ L55-55 verbatim
end Problem346


-- @@ L57-57 verbatim
end


-- @@ L59-59 verbatim
end OAI
