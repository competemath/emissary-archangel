import OAI.AlgebraicGeometry.AbhyankarSathaye.Lifting
import OAI.AlgebraicGeometry.AbhyankarSathaye.Plane
import Mathlib.Algebra.Algebra.Tower


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-12 verbatim
/-!
# Elimination of auxiliary variables

Explicit mutually inverse complex algebra maps identify the lifting presentation
with the quotient of the original polynomial ring by `(F)`.
-/


-- @@ L14-14 verbatim
noncomputable section

-- @@ L15-15 verbatim
namespace AbhyankarSathaye.Presentation

-- @@ L16-16 verbatim
open MvPolynomial


-- @@ L18-18 verbatim
abbrev B := Plane.Q ℂ

-- @@ L19-19 verbatim
abbrev hB : B := Plane.qvar ℂ 0

-- @@ L20-20 verbatim
abbrev xB : B := Plane.qvar ℂ 1

-- @@ L21-21 verbatim
abbrev yB : B := Plane.qvar ℂ 2

-- @@ L22-22 verbatim
abbrev sB : B := Plane.qvar ℂ 3

-- @@ L23-23 verbatim
abbrev L := Lifting.Q hB xB yB sB

-- @@ L24-24 verbatim
abbrev D := R ⧸ Ideal.span {F}


-- @@ L26-26 verbatim
def dmap : R →ₐ[ℂ] D := Ideal.Quotient.mkₐ ℂ (Ideal.span {F})

-- @@ L27-27 verbatim
def lcoef : B →ₐ[ℂ] L := IsScalarTower.toAlgHom ℂ B L

-- @@ L28-28 verbatim
def lvar (i : Fin 3) : L := Lifting.qvar hB xB yB sB i


-- @@ L30-31 verbatim
theorem dmap_F : dmap F = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))


-- @@ L33-33 verbatim
def auxValues : Fin 4 → D := ![dmap h, dmap x, dmap y, dmap s]

-- @@ L34-34 verbatim
def auxEval : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] D := aeval auxValues


-- @@ L36-40 verbatim
theorem auxEval_h : auxEval (Plane.relH ℂ) = 0 := by
  calc
    _ = dmap (h-1-p) := by simp [Plane.relH, auxEval, auxValues, p]
    _ = dmap F := by congr 1; unfold F; ring
    _ = 0 := dmap_F


-- @@ L42-45 verbatim
theorem auxEval_cusp : auxEval (Plane.relCusp ℂ) = 0 := by
  calc
    _ = dmap (x^2+y^3-s*h) := by simp [Plane.relCusp, auxEval, auxValues]
    _ = 0 := by rw [cusp]; simp [mul_comm]


-- @@ L47-48 verbatim
def auxToD : B →ₐ[ℂ] D :=
  lift_pair (Plane.relH ℂ) (Plane.relCusp ℂ) auxEval auxEval_h auxEval_cusp


-- @@ L50-52 verbatim
@[simp] theorem auxToD_qvar (i : Fin 4) : auxToD (Plane.qvar ℂ i) = auxValues i := by
  change aeval auxValues (X i) = auxValues i
  exact aeval_X _ _


-- @@ L54-54 verbatim
def liftValues : Fin 3 → D := ![dmap u, dmap v, dmap w]

-- @@ L55-55 verbatim
def liftEval : MvPolynomial (Fin 3) B →ₐ[ℂ] D := aevalTower auxToD liftValues


-- @@ L57-58 verbatim
theorem liftEval_x : liftEval (Lifting.relX hB xB) = 0 := by
  simp [liftEval, Lifting.relX, liftValues, auxValues, x]


-- @@ L60-61 verbatim
theorem liftEval_y : liftEval (Lifting.relY hB yB) = 0 := by
  simp [liftEval, Lifting.relY, liftValues, auxValues, y]


-- @@ L63-64 verbatim
theorem liftEval_s : liftEval (Lifting.relS hB sB) = 0 := by
  simp [liftEval, Lifting.relS, liftValues, auxValues, s]


-- @@ L66-68 verbatim
def toOriginal : L →ₐ[ℂ] D :=
  lift_triple (Lifting.relX hB xB) (Lifting.relY hB yB) (Lifting.relS hB sB)
    liftEval liftEval_x liftEval_y liftEval_s


-- @@ L70-72 verbatim
@[simp] theorem toOriginal_lvar (i : Fin 3) : toOriginal (lvar i) = liftValues i := by
  change aevalTower auxToD liftValues (X i) = liftValues i
  exact aevalTower_X _ _ _


-- @@ L74-76 verbatim
@[simp] theorem toOriginal_lcoef (b : B) : toOriginal (lcoef b) = auxToD b := by
  change aevalTower auxToD liftValues (C b) = auxToD b
  simp


-- @@ L78-78 verbatim
def originalValues : Fin 4 → L := ![lcoef hB, lvar 0, lvar 1, lvar 2]

-- @@ L79-79 verbatim
def originalEval : R →ₐ[ℂ] L := aeval originalValues


-- @@ L81-82 verbatim
@[simp] theorem originalEval_h : originalEval h = lcoef hB := by
  simp [originalEval, originalValues, h]

-- @@ L83-84 verbatim
@[simp] theorem originalEval_u : originalEval u = lvar 0 := by
  simp [originalEval, originalValues, u]

-- @@ L85-86 verbatim
@[simp] theorem originalEval_v : originalEval v = lvar 1 := by
  simp [originalEval, originalValues, v]

-- @@ L87-88 verbatim
@[simp] theorem originalEval_w : originalEval w = lvar 2 := by
  simp [originalEval, originalValues, w]


-- @@ L90-91 verbatim
@[simp] theorem originalEval_x : originalEval x = lcoef xB := by
  simpa [x, lcoef, lvar] using (Lifting.quotient_relations hB xB yB sB).1

-- @@ L92-93 verbatim
@[simp] theorem originalEval_y : originalEval y = lcoef yB := by
  simpa [y, lcoef, lvar] using (Lifting.quotient_relations hB xB yB sB).2.1

-- @@ L94-95 verbatim
@[simp] theorem originalEval_s : originalEval s = lcoef sB := by
  simpa [s, lcoef, lvar] using (Lifting.quotient_relations hB xB yB sB).2.2


-- @@ L97-100 verbatim
theorem originalEval_F : originalEval F = 0 := by
  have hh : hB = 1+P xB yB sB := Plane.relation_h ℂ
  have he : hB-P xB yB sB-1 = 0 := by rw [hh]; ring
  simpa [F, p] using congrArg lcoef he


-- @@ L102-109 verbatim
def fromOriginal : D →ₐ[ℂ] L := by
  have hi : Ideal.span {F} ≤ RingHom.ker originalEval := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact originalEval_F
  exact Ideal.Quotient.liftₐ _ originalEval (fun z hz => hi hz)


-- @@ L111-111 verbatim
@[simp] theorem fromOriginal_dmap (f : R) : fromOriginal (dmap f) = originalEval f := rfl


-- @@ L113-119 verbatim
theorem to_from : toOriginal.comp fromOriginal = AlgHom.id ℂ D := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change toOriginal (fromOriginal (dmap (X i))) = dmap (X i)
  rw [fromOriginal_dmap]
  fin_cases i <;> simp [originalEval, originalValues, auxValues, liftValues, h, u, v, w]


-- @@ L121-127 verbatim
theorem from_auxToD : fromOriginal.comp auxToD = lcoef := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  change fromOriginal (auxToD (Plane.qvar ℂ i)) = lcoef (Plane.qvar ℂ i)
  rw [auxToD_qvar]
  fin_cases i <;> simp [auxValues]


-- @@ L129-140 verbatim
theorem from_to : fromOriginal.comp toOriginal = AlgHom.id ℂ L := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext'
  · apply AlgHom.ext
    intro b
    change fromOriginal (toOriginal (lcoef b)) = lcoef b
    rw [toOriginal_lcoef]
    exact AlgHom.congr_fun from_auxToD b
  · intro i
    change fromOriginal (toOriginal (lvar i)) = lvar i
    rw [toOriginal_lvar]
    fin_cases i <;> simp [liftValues]


-- @@ L142-143 verbatim
def eliminationEquiv : L ≃ₐ[ℂ] D :=
  AlgEquiv.ofAlgHom toOriginal fromOriginal to_from from_to


-- @@ L145-145 verbatim
end AbhyankarSathaye.Presentation


-- @@ L147-147 verbatim
end


-- @@ L149-149 verbatim
end OAI
