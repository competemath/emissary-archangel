import OAI.AlgebraicGeometry.AbhyankarSathaye.Quotient
import OAI.AlgebraicGeometry.AbhyankarSathaye.Reconstruction
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases


-- @@ L7-7 verbatim
namespace OAI


-- @@ L9-15 verbatim
/-!
# Lifting a cusp relation

If `x² + y³ = h * s` and `α * h + β * y = 1`, the quotient defined by
`U³ + h * V = x`, `-U² + h * W = y`, and `S h U V W = s` is a polynomial
algebra in one variable. This includes the zero ring and rings with zero divisors.
-/


-- @@ L17-17 verbatim
noncomputable section

-- @@ L18-18 verbatim
namespace AbhyankarSathaye.Lifting

-- @@ L19-19 verbatim
open MvPolynomial


-- @@ L21-21 verbatim
variable {B : Type*} [CommRing B]


-- @@ L23-23 verbatim
def relX (h x : B) : MvPolynomial (Fin 3) B := X 0^3+C h*X 1-C x

-- @@ L24-24 verbatim
def relY (h y : B) : MvPolynomial (Fin 3) B := -X 0^2+C h*X 2-C y

-- @@ L25-25 verbatim
def relS (h s : B) : MvPolynomial (Fin 3) B := S (C h) (X 0) (X 1) (X 2)-C s

-- @@ L26-27 verbatim
def ideal (h x y s : B) : Ideal (MvPolynomial (Fin 3) B) :=
  Ideal.span {relX h x, relY h y, relS h s}

-- @@ L28-28 verbatim
abbrev Q (h x y s : B) := MvPolynomial (Fin 3) B ⧸ ideal h x y s

-- @@ L29-30 verbatim
def qmap (h x y s : B) : MvPolynomial (Fin 3) B →ₐ[B] Q h x y s :=
  Ideal.Quotient.mkₐ B (ideal h x y s)

-- @@ L31-31 verbatim
def qvar (h x y s : B) (i : Fin 3) : Q h x y s := qmap h x y s (X i)


-- @@ L33-52 verbatim
theorem quotient_relations (h x y s : B) :
    let c := algebraMap B (Q h x y s)
    let U := qvar h x y s 0
    let V := qvar h x y s 1
    let W := qvar h x y s 2
    U^3+c h*V = c x ∧ -U^2+c h*W = c y ∧ S (c h) U V W = c s := by
  dsimp only
  have hx : qmap h x y s (relX h x) = 0 :=
    quotient_triple_first (relX h x) (relY h y) (relS h s)
  have hy : qmap h x y s (relY h y) = 0 :=
    quotient_triple_second (relX h x) (relY h y) (relS h s)
  have hs : qmap h x y s (relS h s) = 0 :=
    quotient_triple_third (relX h x) (relY h y) (relS h s)
  refine ⟨?_, ?_, ?_⟩
  · apply sub_eq_zero.mp
    simpa [relX, qvar] using hx
  · apply sub_eq_zero.mp
    simpa [relY, qvar] using hy
  · apply sub_eq_zero.mp
    simpa [relS, qvar] using hs


-- @@ L54-55 verbatim
def polyU (h x β : B) : Polynomial B := inverseU (Polynomial.C h) (Polynomial.C x)
  (Polynomial.C β) Polynomial.X

-- @@ L56-57 verbatim
def polyG (x y α : B) : Polynomial B := inverseG (Polynomial.C x) (Polynomial.C y)
  (Polynomial.C α) Polynomial.X

-- @@ L58-60 verbatim
def polyW (h x y s α β : B) : Polynomial B :=
  inverseW (Polynomial.C h) (Polynomial.C y) (Polynomial.C s) (Polynomial.C α)
    (Polynomial.C β) (polyU h x β) (polyG x y α)

-- @@ L61-62 verbatim
def polyV (h x y s α β : B) : Polynomial B :=
  inverseV (polyU h x β) (polyG x y α) (polyW h x y s α β)

-- @@ L63-64 verbatim
def values (h x y s α β : B) : Fin 3 → Polynomial B :=
  ![polyU h x β, polyV h x y s α β, polyW h x y s α β]


-- @@ L66-84 verbatim
theorem values_relations (h x y s α β : B)
    (hc : x^2+y^3 = h*s) (hb : α*h+β*y = 1) :
    (aeval (values h x y s α β)) (relX h x) = 0 ∧
    (aeval (values h x y s α β)) (relY h y) = 0 ∧
    (aeval (values h x y s α β)) (relS h s) = 0 := by
  have hc' : (Polynomial.C x)^2+(Polynomial.C y)^3 = Polynomial.C h*Polynomial.C s := by
    simpa using congrArg (Polynomial.C : B →+* Polynomial B) hc
  have hb' : Polynomial.C α*Polynomial.C h+Polynomial.C β*Polynomial.C y = 1 := by
    simpa using congrArg (Polynomial.C : B →+* Polynomial B) hb
  have hr := inverse_relations (Polynomial.C h) (Polynomial.C x) (Polynomial.C y)
    (Polynomial.C s) (Polynomial.C α) (Polynomial.C β) Polynomial.X hc' hb'
  dsimp only at hr
  refine ⟨?_, ?_, ?_⟩
  · simpa [relX, values, polyU, polyV, polyG, polyW, Polynomial.algebraMap_eq]
      using sub_eq_zero.mpr hr.1
  · simpa [relY, values, polyU, polyV, polyG, polyW, Polynomial.algebraMap_eq]
      using sub_eq_zero.mpr hr.2.1
  · simpa [relS, values, polyU, polyV, polyG, polyW, Polynomial.algebraMap_eq]
      using sub_eq_zero.mpr hr.2.2


-- @@ L86-91 verbatim
def forward (h x y s α β : B) (hc : x^2+y^3 = h*s) (hb : α*h+β*y = 1) :
    Q h x y s →ₐ[B] Polynomial B :=
  lift_triple (relX h x) (relY h y) (relS h s) (aeval (values h x y s α β))
    (values_relations h x y s α β hc hb).1
    (values_relations h x y s α β hc hb).2.1
    (values_relations h x y s α β hc hb).2.2


-- @@ L93-96 verbatim
@[simp] theorem forward_qvar (h x y s α β : B) (hc hb) (i : Fin 3) :
    forward h x y s α β hc hb (qvar h x y s i) = values h x y s α β i := by
  change aeval (values h x y s α β) (X i) = values h x y s α β i
  exact aeval_X _ _


-- @@ L98-100 verbatim
def backward (h x y s α β : B) : Polynomial B →ₐ[B] Q h x y s :=
  Polynomial.aeval (parameter (algebraMap B _ α) (algebraMap B _ β)
    (qvar h x y s 0) (qvar h x y s 1) (qvar h x y s 2))


-- @@ L102-109 verbatim
theorem forward_backward (h x y s α β : B) (hc hb) :
    (forward h x y s α β hc hb).comp (backward h x y s α β) = AlgHom.id B _ := by
  apply Polynomial.algHom_ext
  have hb' : Polynomial.C α*Polynomial.C h+Polynomial.C β*Polynomial.C y = 1 := by
    simpa using congrArg (Polynomial.C : B →+* Polynomial B) hb
  simpa [backward, values, polyU, polyV, polyW, polyG, Polynomial.algebraMap_eq]
    using inverse_parameter (Polynomial.C h) (Polynomial.C x) (Polynomial.C y)
      (Polynomial.C s) (Polynomial.C α) (Polynomial.C β) Polynomial.X hb'


-- @@ L111-131 verbatim
theorem backward_forward (h x y s α β : B) (hc hb) :
    (backward h x y s α β).comp (forward h x y s α β hc hb) = AlgHom.id B _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  have hb' : algebraMap B (Q h x y s) α*algebraMap B _ h+
      algebraMap B _ β*algebraMap B _ y = 1 := by
    simpa using congrArg (algebraMap B (Q h x y s)) hb
  obtain ⟨hx, hy, hs⟩ := quotient_relations h x y s
  have hr := original_reconstruction (algebraMap B (Q h x y s) h)
    (algebraMap B _ x) (algebraMap B _ y) (algebraMap B _ s)
    (algebraMap B _ α) (algebraMap B _ β)
    (qvar h x y s 0) (qvar h x y s 1) (qvar h x y s 2) hb' hx hy hs
  dsimp only at hr
  change backward h x y s α β (forward h x y s α β hc hb (qvar h x y s i)) =
    qvar h x y s i
  rw [forward_qvar]
  fin_cases i
  · simpa [values, polyU, backward] using hr.1
  · simpa [values, polyU, polyV, polyG, polyW, backward] using hr.2.1
  · simpa [values, polyU, polyV, polyG, polyW, backward] using hr.2.2


-- @@ L133-136 verbatim
def equivalence (h x y s α β : B) (hc : x^2+y^3 = h*s) (hb : α*h+β*y = 1) :
    Q h x y s ≃ₐ[B] Polynomial B :=
  AlgEquiv.ofAlgHom (forward h x y s α β hc hb) (backward h x y s α β)
    (forward_backward h x y s α β hc hb) (backward_forward h x y s α β hc hb)


-- @@ L138-138 verbatim
end AbhyankarSathaye.Lifting


-- @@ L140-140 verbatim
end


-- @@ L142-142 verbatim
end OAI
