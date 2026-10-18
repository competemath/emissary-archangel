import OAI.AlgebraicGeometry.StableCoordinate.Definitions
import OAI.AlgebraicGeometry.StableCoordinate.MatrixChange
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases


-- @@ L6-6 verbatim
namespace OAI


-- @@ L8-15 verbatim
/-!
# Polynomial presentation, with arbitrary additional independent variables

The source variables in `P n` are `p,s,u,F,J`, in that order, followed by
`n` independent variables.  The matrix transformation leaves those extra
variables fixed.  In particular `n=0` gives the unstabilized presentation and
`n=1` supplies the presentation needed in the one-variable stabilization.
-/


-- @@ L17-17 verbatim
namespace StableCoordinate.Presentation


-- @@ L19-19 verbatim
open MvPolynomial MatrixChange


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
abbrev P (n : ℕ) := R (5 + n)


-- @@ L25-25 verbatim
def p (n : ℕ) : P n := X ((0 : Fin 5).castAdd n)

-- @@ L26-26 verbatim
def s (n : ℕ) : P n := X ((1 : Fin 5).castAdd n)

-- @@ L27-27 verbatim
def u (n : ℕ) : P n := X ((2 : Fin 5).castAdd n)

-- @@ L28-28 verbatim
def F (n : ℕ) : P n := X ((3 : Fin 5).castAdd n)

-- @@ L29-29 verbatim
def J (n : ℕ) : P n := X ((4 : Fin 5).castAdd n)

-- @@ L30-30 verbatim
def x (n : ℕ) : P n := quad (p n) (s n) (u n) (F n)

-- @@ L31-31 verbatim
def H (n : ℕ) : P n := relation (p n) (s n) (u n) (F n) (J n)

-- @@ L32-32 verbatim
def relationIdeal (n : ℕ) : Ideal (P n) := Ideal.span {H n}

-- @@ L33-33 verbatim
abbrev A (n : ℕ) := P n ⧸ relationIdeal n


-- @@ L35-39 verbatim
def changeCoords (n : ℕ) (t : ℂ) : Fin 5 → P n :=
  ![pChange (C t) (p n) (s n) (u n) (F n) (J n),
    sChange (C t) (p n) (s n) (u n) (F n) (J n),
    uChange (C t) (p n) (s n) (u n) (F n) (J n),
    FChange (C t) (p n) (s n) (u n) (F n) (J n), J n]


-- @@ L41-42 verbatim
def changeHom (n : ℕ) (t : ℂ) : P n →ₐ[ℂ] P n :=
  aeval (Fin.addCases (changeCoords n t) (fun i : Fin n => X (i.natAdd 5)))


-- @@ L44-45 verbatim
@[simp] lemma changeHom_C (n : ℕ) (t c : ℂ) : changeHom n t (C c) = C c := by
  simp [changeHom]


-- @@ L47-49 verbatim
@[simp] lemma changeHom_X_left (n : ℕ) (t : ℂ) (i : Fin 5) :
    changeHom n t (X (i.castAdd n)) = changeCoords n t i := by
  simp [changeHom]


-- @@ L51-53 verbatim
@[simp] lemma changeHom_X_right (n : ℕ) (t : ℂ) (i : Fin n) :
    changeHom n t (X (i.natAdd 5)) = X (i.natAdd 5) := by
  simp [changeHom]


-- @@ L55-57 verbatim
@[simp] lemma changeHom_p (n : ℕ) (t : ℂ) :
    changeHom n t (p n) = pChange (C t) (p n) (s n) (u n) (F n) (J n) := by
  simp [p, changeCoords]

-- @@ L58-60 verbatim
@[simp] lemma changeHom_s (n : ℕ) (t : ℂ) :
    changeHom n t (s n) = sChange (C t) (p n) (s n) (u n) (F n) (J n) := by
  simp [s, changeCoords]

-- @@ L61-63 verbatim
@[simp] lemma changeHom_u (n : ℕ) (t : ℂ) :
    changeHom n t (u n) = uChange (C t) (p n) (s n) (u n) (F n) (J n) := by
  simp [u, changeCoords]

-- @@ L64-66 verbatim
@[simp] lemma changeHom_F (n : ℕ) (t : ℂ) :
    changeHom n t (F n) = FChange (C t) (p n) (s n) (u n) (F n) (J n) := by
  simp [F, changeCoords]

-- @@ L67-68 verbatim
@[simp] lemma changeHom_J (n : ℕ) (t : ℂ) : changeHom n t (J n) = J n := by
  simp [J, changeCoords]


-- @@ L70-78 verbatim
lemma changeHom_comp (n : ℕ) (t r : ℂ) :
    (changeHom n t).comp (changeHom n r) = changeHom n (r + t) := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · fin_cases j <;>
      simp [AlgHom.comp_apply, changeCoords,
        pChange_add, sChange_add, uChange_add, FChange_add, map_add]
  · simp


-- @@ L80-85 verbatim
lemma changeHom_zero (n : ℕ) : changeHom n 0 = AlgHom.id ℂ (P n) := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · fin_cases j <;> simp [changeCoords, p, s, u, F, J]
  · simp


-- @@ L87-92 verbatim
/-- The source's inverse matrix substitution, regarded as an algebra automorphism.
It carries the original hypersurface equation to `-J-u`. -/
def matrixEquiv (n : ℕ) : P n ≃ₐ[ℂ] P n :=
  AlgEquiv.ofAlgHom (changeHom n (-1)) (changeHom n 1)
    (by rw [changeHom_comp]; simpa using changeHom_zero n)
    (by rw [changeHom_comp]; simpa using changeHom_zero n)


-- @@ L94-95 verbatim
@[simp] lemma matrixEquiv_apply (n : ℕ) (v : P n) :
    matrixEquiv n v = changeHom n (-1) v := rfl


-- @@ L97-98 verbatim
@[simp] lemma matrixEquiv_symm_apply (n : ℕ) (v : P n) :
    (matrixEquiv n).symm v = changeHom n 1 v := rfl


-- @@ L100-101 verbatim
lemma matrixEquiv_H (n : ℕ) : matrixEquiv n (H n) = -J n - u n := by
  simp [H, relation_change_neg_one]


-- @@ L103-104 verbatim
lemma matrixEquiv_x (n : ℕ) : matrixEquiv n (x n) = x n := by
  simp [x, quad_change]



-- @@ L107-112 verbatim
/-- Set the transformed variable `u` equal to `-J` and retain all other variables. -/
def eliminateHom (n : ℕ) : P n →ₐ[ℂ] R (4 + n) :=
  aeval (Fin.addCases
    ![X ((0 : Fin 4).castAdd n), X ((1 : Fin 4).castAdd n),
      -X ((3 : Fin 4).castAdd n), X ((2 : Fin 4).castAdd n), X ((3 : Fin 4).castAdd n)]
    (fun i : Fin n => X (i.natAdd 4)))


-- @@ L114-116 verbatim
/-- Include the four retained variables and all the extra variables. -/
def includeHom (n : ℕ) : R (4 + n) →ₐ[ℂ] P n :=
  aeval (Fin.addCases ![p n, s n, F n, J n] (fun i : Fin n => X (i.natAdd 5)))


-- @@ L118-119 verbatim
@[simp] lemma eliminateHom_p (n : ℕ) : eliminateHom n (p n) = X ((0 : Fin 4).castAdd n) := by
  simp [eliminateHom, p]

-- @@ L120-121 verbatim
@[simp] lemma eliminateHom_s (n : ℕ) : eliminateHom n (s n) = X ((1 : Fin 4).castAdd n) := by
  simp [eliminateHom, s]

-- @@ L122-123 verbatim
@[simp] lemma eliminateHom_u (n : ℕ) : eliminateHom n (u n) = -X ((3 : Fin 4).castAdd n) := by
  simp [eliminateHom, u]

-- @@ L124-125 verbatim
@[simp] lemma eliminateHom_F (n : ℕ) : eliminateHom n (F n) = X ((2 : Fin 4).castAdd n) := by
  simp [eliminateHom, F]

-- @@ L126-127 verbatim
@[simp] lemma eliminateHom_J (n : ℕ) : eliminateHom n (J n) = X ((3 : Fin 4).castAdd n) := by
  simp [eliminateHom, J]


-- @@ L129-131 verbatim
@[simp] lemma eliminateHom_X_right (n : ℕ) (i : Fin n) :
    eliminateHom n (X (i.natAdd 5)) = X (i.natAdd 4) := by
  simp [eliminateHom]

-- @@ L132-134 verbatim
@[simp] lemma includeHom_X_right (n : ℕ) (i : Fin n) :
    includeHom n (X (i.natAdd 4)) = X (i.natAdd 5) := by
  simp [includeHom]


-- @@ L136-142 verbatim
lemma eliminateHom_includeHom (n : ℕ) :
    (eliminateHom n).comp (includeHom n) = AlgHom.id ℂ (R (4+n)) := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · fin_cases j <;> simp [includeHom]
  · simp


-- @@ L144-145 verbatim
/-- Quotient projection for the source hypersurface. -/
def mk (n : ℕ) : P n →ₐ[ℂ] A n := Ideal.Quotient.mkₐ ℂ (relationIdeal n)


-- @@ L147-149 verbatim
@[simp] lemma mk_H (n : ℕ) : mk n (H n) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.subset_span (by simp)


-- @@ L151-153 verbatim
/-- Evaluation in the explicit four-variable polynomial presentation. -/
def polynomialMap (n : ℕ) : P n →ₐ[ℂ] R (4+n) :=
  (eliminateHom n).comp (matrixEquiv n).toAlgHom


-- @@ L155-158 verbatim
@[simp] lemma polynomialMap_H (n : ℕ) : polynomialMap n (H n) = 0 := by
  change eliminateHom n (matrixEquiv n (H n)) = 0
  rw [matrixEquiv_H]
  simp


-- @@ L160-164 verbatim
/-- The source quotient maps to the four-variable polynomial presentation. -/
def toPolynomial (n : ℕ) : A n →ₐ[ℂ] R (4+n) :=
  Ideal.Quotient.liftₐ (relationIdeal n) (polynomialMap n) (by
    apply (Ideal.span_singleton_le_iff_mem (RingHom.ker (polynomialMap n).toRingHom)).mpr
    exact polynomialMap_H n)


-- @@ L166-167 verbatim
@[simp] lemma toPolynomial_mk (n : ℕ) (v : P n) :
    toPolynomial n (mk n v) = polynomialMap n v := rfl


-- @@ L169-171 verbatim
/-- The inverse polynomial presentation uses the forward matrix coordinates upstairs. -/
def fromPolynomial (n : ℕ) : R (4+n) →ₐ[ℂ] A n :=
  (mk n).comp ((matrixEquiv n).symm.toAlgHom.comp (includeHom n))


-- @@ L173-180 verbatim
lemma toPolynomial_fromPolynomial (n : ℕ) :
    (toPolynomial n).comp (fromPolynomial n) = AlgHom.id ℂ (R (4+n)) := by
  apply AlgHom.ext
  intro r
  simp only [AlgHom.comp_apply, fromPolynomial, toPolynomial_mk, polynomialMap, AlgHom.id_apply]
  change eliminateHom n ((matrixEquiv n) ((matrixEquiv n).symm (includeHom n r))) = r
  rw [AlgEquiv.apply_symm_apply]
  exact DFunLike.congr_fun (eliminateHom_includeHom n) r


-- @@ L182-202 verbatim
lemma mk_matrix_symm_include_eliminate (n : ℕ) :
    ((mk n).comp (matrixEquiv n).symm.toAlgHom).comp
      ((includeHom n).comp (eliminateHom n)) =
    (mk n).comp (matrixEquiv n).symm.toAlgHom := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · fin_cases j
    · simp [AlgHom.comp_apply, eliminateHom, includeHom, p]
    · simp [AlgHom.comp_apply, eliminateHom, includeHom, s]
    · change mk n ((matrixEquiv n).symm (includeHom n (eliminateHom n (u n)))) =
        mk n ((matrixEquiv n).symm (u n))
      have hj : includeHom n (X ((3 : Fin 4).castAdd n)) = J n := by simp [includeHom]
      rw [eliminateHom_u, map_neg, hj]
      simp only [map_neg, matrixEquiv_symm_apply, changeHom_J, changeHom_u, map_one]
      rw [uChange_one]
      change -(mk n (J n)) = mk n (-H n - J n)
      simp
    · simp [AlgHom.comp_apply, eliminateHom, includeHom, F]
    · simp [AlgHom.comp_apply, eliminateHom, includeHom, J]
  · simp [AlgHom.comp_apply]


-- @@ L204-214 verbatim
lemma fromPolynomial_toPolynomial (n : ℕ) :
    (fromPolynomial n).comp (toPolynomial n) = AlgHom.id ℂ (A n) := by
  apply Ideal.Quotient.algHom_ext ℂ
  apply AlgHom.ext
  intro v
  change fromPolynomial n (toPolynomial n (mk n v)) = mk n v
  rw [toPolynomial_mk]
  change mk n ((matrixEquiv n).symm (includeHom n
    (eliminateHom n ((matrixEquiv n) v)))) = mk n v
  have h := DFunLike.congr_fun (mk_matrix_symm_include_eliminate n) ((matrixEquiv n) v)
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using h


-- @@ L216-219 verbatim
/-- Proposition 2.1, stable under adjoining any number of independent variables. -/
def polynomialPresentation (n : ℕ) : A n ≃ₐ[ℂ] R (4+n) :=
  AlgEquiv.ofAlgHom (toPolynomial n) (fromPolynomial n)
    (toPolynomial_fromPolynomial n) (fromPolynomial_toPolynomial n)


-- @@ L221-222 verbatim
@[simp] lemma polynomialPresentation_mk (n : ℕ) (v : P n) :
    polynomialPresentation n (mk n v) = polynomialMap n v := rfl



-- @@ L225-232 verbatim
/-- The distinguished source variable is exactly the polynomial in the question,
renamed into the first four variables; the extra variables are not involved. -/
lemma polynomialPresentation_p (n : ℕ) :
    polynomialPresentation n (mk n (p n)) =
      MvPolynomial.rename (Fin.castAdd n : Fin 4 → Fin (4+n)) StableCoordinate.f := by
  rw [polynomialPresentation_mk]
  simp [polynomialMap, pChange, quad, StableCoordinate.f, StableCoordinate.Q, map_ofNat]
  ring


-- @@ L234-236 verbatim
@[simp] lemma polynomialPresentation_extra (n : ℕ) (i : Fin n) :
    polynomialPresentation n (mk n (X (i.natAdd 5))) = X (i.natAdd 4) := by
  simp [polynomialMap]


-- @@ L238-239 verbatim
/-- The unstabilized polynomial presentation. -/
abbrev originalPresentation : A 0 ≃ₐ[ℂ] R 4 := polynomialPresentation 0


-- @@ L241-242 verbatim
lemma originalPresentation_p : originalPresentation (mk 0 (p 0)) = StableCoordinate.f := by
  simpa using polynomialPresentation_p 0


-- @@ L244-245 verbatim
/-- The same presentation after adjoining one independent variable. -/
abbrev stabilizedPresentation : A 1 ≃ₐ[ℂ] R 5 := polynomialPresentation 1


-- @@ L247-253 verbatim
lemma stabilizedPresentation_p :
    stabilizedPresentation (mk 1 (p 1)) = stabilize StableCoordinate.f := by
  have hi : (Fin.castAdd 1 : Fin 4 → Fin 5) = Fin.castSucc := by
    funext i
    apply Fin.ext
    rfl
  simpa [stabilize, hi] using polynomialPresentation_p 1


-- @@ L255-255 verbatim
end

-- @@ L256-256 verbatim
end StableCoordinate.Presentation


-- @@ L258-258 verbatim
end OAI
