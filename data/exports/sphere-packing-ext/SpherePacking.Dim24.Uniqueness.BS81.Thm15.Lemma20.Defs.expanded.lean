module
public import SpherePacking.Dim24.Uniqueness.BS81.LatticeL


-- @@ L4-14 verbatim
/-!
# Induction data for BS81 Lemma 20

This file defines the structure `ContainsDn C n`, which packages an embedded copy of the root
lattice `Dₙ` inside `L := span_ℤ (2 • C)`:
an orthonormal frame `e : Fin n → ℝ²⁴` together with the membership of the minimal vectors
`√2 (e i ± e j)` in the shell `latticeShell4 C`.

## Main definition
* `ContainsDn`
-/



-- @@ L17-17 verbatim
namespace SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20


-- @@ L19-19 verbatim
noncomputable section


-- @@ L21-21 verbatim
open scoped RealInnerProductSpace


-- @@ L23-23 verbatim
local notation "ℝ²⁴" => EuclideanSpace ℝ (Fin 24)


-- @@ L25-33 verbatim
/-- An embedded copy of `Dₙ` inside `latticeL C`, given by an orthonormal frame `e₁,...,eₙ`
and the associated minimal vectors `√2 (±e_i ± e_j)` living in `latticeShell4 C`. -/
public structure ContainsDn (C : Set ℝ²⁴) (n : ℕ) where
  e : Fin n → ℝ²⁴
  ortho : Orthonormal ℝ e
  minVec_mem :
    ∀ (i j : Fin n), i ≠ j →
      (Real.sqrt 2 • (e i + e j)) ∈ latticeShell4 C ∧
      (Real.sqrt 2 • (e i - e j)) ∈ latticeShell4 C


-- @@ L35-38 verbatim
/-- Negation preserves membership in the shell `latticeShell4 C`. -/
public lemma latticeShell4_neg_mem {C : Set ℝ²⁴} {v : ℝ²⁴} (hv : v ∈ latticeShell4 C) :
    -v ∈ latticeShell4 C :=
  ⟨(latticeL C).neg_mem hv.1, by simpa [norm_neg] using hv.2⟩


-- @@ L40-40 verbatim
end


-- @@ L42-42 verbatim
end SpherePacking.Dim24.Uniqueness.BS81.Thm15.Lemma20
