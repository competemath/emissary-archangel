import OAI.AlgebraicGeometry.CommutingDerivations.ParameterBezout
import OAI.AlgebraicGeometry.AbhyankarSathaye.Reconstruction
import OAI.AlgebraicGeometry.AbhyankarSathaye.Quotient
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases


-- @@ L7-7 verbatim
namespace OAI


-- @@ L9-15 verbatim
/-!
Explicit relative polynomial coordinates with an invertible parameter.

The coefficient ring is arbitrary, including the zero ring. In the localization
application it is the Laurent coefficient ring `ℂ[c,c⁻¹]`. The relative
presentation is explicitly isomorphic to a polynomial algebra in three variables.
-/

-- @@ L16-16 verbatim
noncomputable section

-- @@ L17-17 verbatim
namespace AbhyankarSathaye.CommutingDerivations.ParameterBridge

-- @@ L18-18 verbatim
open MvPolynomial


-- @@ L20-22 verbatim
variable (K : Type*) [CommRing K]

-- Original independent variable order: h,u,v,w.

-- @@ L23-23 verbatim
def rawH : MvPolynomial (Fin 4) K := X 0

-- @@ L24-24 verbatim
def rawU : MvPolynomial (Fin 4) K := X 1

-- @@ L25-25 verbatim
def rawV : MvPolynomial (Fin 4) K := X 2

-- @@ L26-26 verbatim
def rawW : MvPolynomial (Fin 4) K := X 3

-- @@ L27-27 verbatim
def rawX : MvPolynomial (Fin 4) K := rawU K^3+rawH K*rawV K

-- @@ L28-28 verbatim
def rawY : MvPolynomial (Fin 4) K := -rawU K^2+rawH K*rawW K

-- @@ L29-29 verbatim
def rawS : MvPolynomial (Fin 4) K := S (rawH K) (rawU K) (rawV K) (rawW K)

-- @@ L30-31 verbatim
def relation (c : K) : MvPolynomial (Fin 4) K :=
  rawH K-P (rawX K) (rawY K) (rawS K)-C c

-- @@ L32-32 verbatim
abbrev Q (c : K) := MvPolynomial (Fin 4) K ⧸ Ideal.span {relation K c}

-- @@ L33-34 verbatim
def qmap (c : K) : MvPolynomial (Fin 4) K →ₐ[K] Q K c :=
  Ideal.Quotient.mkₐ K (Ideal.span {relation K c})

-- @@ L35-35 verbatim
def coeff (c : K) : K →+* Q K c := algebraMap K _

-- @@ L36-36 verbatim
def qH (c : K) : Q K c := qmap K c (rawH K)

-- @@ L37-37 verbatim
def qU (c : K) : Q K c := qmap K c (rawU K)

-- @@ L38-38 verbatim
def qV (c : K) : Q K c := qmap K c (rawV K)

-- @@ L39-39 verbatim
def qW (c : K) : Q K c := qmap K c (rawW K)

-- @@ L40-40 verbatim
def qX (c : K) : Q K c := qmap K c (rawX K)

-- @@ L41-41 verbatim
def qY (c : K) : Q K c := qmap K c (rawY K)

-- @@ L42-42 verbatim
def qS (c : K) : Q K c := qmap K c (rawS K)

-- @@ L43-44 verbatim
def qAlpha (c d : K) : Q K c :=
  coeff K c d^2*parameterA (coeff K c c) (qX K c) (qS K c)

-- @@ L45-46 verbatim
def qBeta (c d : K) : Q K c :=
  coeff K c d^2*parameterB (coeff K c c) (qX K c) (qY K c) (qS K c)

-- @@ L47-48 verbatim
def qT (c d : K) : Q K c :=
  parameter (qAlpha K c d) (qBeta K c d) (qU K c) (qV K c) (qW K c)


-- @@ L50-59 verbatim
theorem quotient_relation (c : K) :
    qH K c = coeff K c c+P (qX K c) (qY K c) (qS K c) := by
  have hz : qmap K c (relation K c) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have he : qH K c-P (qX K c) (qY K c) (qS K c)-coeff K c c = 0 := by
    simpa [relation, qH, qX, qY, qS, coeff] using hz
  calc
    _ = (qH K c-P (qX K c) (qY K c) (qS K c)-coeff K c c)+
        (coeff K c c+P (qX K c) (qY K c) (qS K c)) := by ring
    _ = _ := by rw [he, zero_add]


-- @@ L61-64 verbatim
theorem quotient_cusp (c : K) : (qX K c)^2+(qY K c)^3 = qS K c*qH K c := by
  have he := congrArg (qmap K c)
    (cusp_universal (rawH K) (rawU K) (rawV K) (rawW K))
  simpa [qX, qY, qS, qH, rawX, rawY, rawS, mul_comm] using he


-- @@ L66-71 verbatim
theorem quotient_bezout (c d : K) (hunit : c*d=1) :
    qAlpha K c d*qH K c+qBeta K c d*qY K c = 1 := by
  have hu : coeff K c c*coeff K c d=1 := by
    simpa using congrArg (coeff K c) hunit
  exact parameter_bezout_unit _ _ _ _ _ _
    (quotient_cusp K c) (quotient_relation K c) hu


-- @@ L73-80 verbatim
theorem quotient_recover_s (c d : K) (hunit : c*d=1) :
    coeff K c d*((qX K c+(qS K c)^3)^2+(qY K c-(qS K c)^2)^3) = qS K c := by
  have hu : coeff K c c*coeff K c d=1 := by
    simpa using congrArg (coeff K c) hunit
  exact parameter_recover_s _ _ _ _ _ _
    (quotient_cusp K c) (quotient_relation K c) hu

-- Free independent variable order: X,Y,T.

-- @@ L81-81 verbatim
def freeS (d : K) : MvPolynomial (Fin 3) K := C d*(X 0^2+X 1^3)

-- @@ L82-82 verbatim
def freeX (d : K) : MvPolynomial (Fin 3) K := X 0-(freeS K d)^3

-- @@ L83-83 verbatim
def freeY (d : K) : MvPolynomial (Fin 3) K := X 1+(freeS K d)^2

-- @@ L84-85 verbatim
def freeH (c d : K) : MvPolynomial (Fin 3) K :=
  C c+P (freeX K d) (freeY K d) (freeS K d)

-- @@ L86-87 verbatim
def freeAlpha (c d : K) : MvPolynomial (Fin 3) K :=
  C d^2*parameterA (C c) (freeX K d) (freeS K d)

-- @@ L88-89 verbatim
def freeBeta (c d : K) : MvPolynomial (Fin 3) K :=
  C d^2*parameterB (C c) (freeX K d) (freeY K d) (freeS K d)

-- @@ L90-91 verbatim
def freeU (c d : K) : MvPolynomial (Fin 3) K :=
  inverseU (freeH K c d) (freeX K d) (freeBeta K c d) (X 2)

-- @@ L92-93 verbatim
def freeG (c d : K) : MvPolynomial (Fin 3) K :=
  inverseG (freeX K d) (freeY K d) (freeAlpha K c d) (X 2)

-- @@ L94-96 verbatim
def freeW (c d : K) : MvPolynomial (Fin 3) K :=
  inverseW (freeH K c d) (freeY K d) (freeS K d) (freeAlpha K c d)
    (freeBeta K c d) (freeU K c d) (freeG K c d)

-- @@ L97-98 verbatim
def freeV (c d : K) : MvPolynomial (Fin 3) K :=
  inverseV (freeU K c d) (freeG K c d) (freeW K c d)


-- @@ L100-113 verbatim
theorem free_cusp (c d : K) (hunit : c*d=1) :
    (freeX K d)^2+(freeY K d)^3=freeS K d*freeH K c d := by
  have hu : (C c : MvPolynomial (Fin 3) K)*C d=1 := by
    simpa using congrArg (C : K →+* MvPolynomial (Fin 3) K) hunit
  have hs : C c*freeS K d=X 0^2+X 1^3 := by
    rw [freeS, ← mul_assoc, hu, one_mul]
  have he := shift_universal (freeX K d) (freeY K d) (freeS K d)
  have hx : freeX K d+(freeS K d)^3=X 0 := by unfold freeX; ring
  have hy : freeY K d-(freeS K d)^2=X 1 := by unfold freeY; ring
  rw [hx, hy, ← hs] at he
  calc
    _ = C c*freeS K d+freeS K d*P (freeX K d) (freeY K d) (freeS K d) :=
      (eq_sub_iff_add_eq.mp he).symm
    _ = _ := by unfold freeH; ring


-- @@ L115-119 verbatim
theorem free_bezout (c d : K) (hunit : c*d=1) :
    freeAlpha K c d*freeH K c d+freeBeta K c d*freeY K d=1 := by
  have hu : (C c : MvPolynomial (Fin 3) K)*C d=1 := by
    simpa using congrArg (C : K →+* MvPolynomial (Fin 3) K) hunit
  exact parameter_bezout_unit _ _ _ _ _ _ (free_cusp K c d hunit) rfl hu


-- @@ L121-126 verbatim
theorem free_relations (c d : K) (hunit : c*d=1) :
    (freeU K c d)^3+freeH K c d*freeV K c d=freeX K d ∧
    -(freeU K c d)^2+freeH K c d*freeW K c d=freeY K d ∧
    S (freeH K c d) (freeU K c d) (freeV K c d) (freeW K c d)=freeS K d := by
  exact inverse_relations _ _ _ _ _ _ _
    (by simpa [mul_comm] using free_cusp K c d hunit) (free_bezout K c d hunit)


-- @@ L128-129 verbatim
def values (c d : K) : Fin 4 → MvPolynomial (Fin 3) K :=
  ![freeH K c d, freeU K c d, freeV K c d, freeW K c d]

-- @@ L130-131 verbatim
def evaluation (c d : K) : MvPolynomial (Fin 4) K →ₐ[K] MvPolynomial (Fin 3) K :=
  aeval (values K c d)


-- @@ L133-134 verbatim
@[simp] theorem evaluation_h (c d : K) : evaluation K c d (rawH K)=freeH K c d := by
  simp [evaluation, values, rawH]

-- @@ L135-136 verbatim
@[simp] theorem evaluation_u (c d : K) : evaluation K c d (rawU K)=freeU K c d := by
  simp [evaluation, values, rawU]

-- @@ L137-138 verbatim
@[simp] theorem evaluation_v (c d : K) : evaluation K c d (rawV K)=freeV K c d := by
  simp [evaluation, values, rawV]

-- @@ L139-140 verbatim
@[simp] theorem evaluation_w (c d : K) : evaluation K c d (rawW K)=freeW K c d := by
  simp [evaluation, values, rawW]

-- @@ L141-143 verbatim
@[simp] theorem evaluation_x (c d : K) (hunit : c*d=1) :
    evaluation K c d (rawX K)=freeX K d := by
  simpa [rawX] using (free_relations K c d hunit).1

-- @@ L144-146 verbatim
@[simp] theorem evaluation_y (c d : K) (hunit : c*d=1) :
    evaluation K c d (rawY K)=freeY K d := by
  simpa [rawY] using (free_relations K c d hunit).2.1

-- @@ L147-149 verbatim
@[simp] theorem evaluation_s (c d : K) (hunit : c*d=1) :
    evaluation K c d (rawS K)=freeS K d := by
  simpa [rawS] using (free_relations K c d hunit).2.2


-- @@ L151-155 verbatim
theorem evaluation_relation (c d : K) (hunit : c*d=1) :
    evaluation K c d (relation K c)=0 := by
  simp only [relation, map_sub, map_P, evaluation_h, evaluation_x K c d hunit,
    evaluation_y K c d hunit, evaluation_s K c d hunit]
  simp [evaluation, freeH]


-- @@ L157-164 verbatim
def forward (c d : K) (hunit : c*d=1) : Q K c →ₐ[K] MvPolynomial (Fin 3) K := by
  have hi : Ideal.span {relation K c} ≤ RingHom.ker (evaluation K c d) := by
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact evaluation_relation K c d hunit
  exact Ideal.Quotient.liftₐ _ (evaluation K c d) (fun z hz => hi hz)


-- @@ L166-167 verbatim
@[simp] theorem forward_qmap (c d : K) (hunit : c*d=1) (f) :
    forward K c d hunit (qmap K c f)=evaluation K c d f := rfl


-- @@ L169-170 verbatim
def backward (c d : K) : MvPolynomial (Fin 3) K →ₐ[K] Q K c :=
  aeval ![qX K c+(qS K c)^3, qY K c-(qS K c)^2, qT K c d]


-- @@ L172-173 verbatim
@[simp] theorem backward_X2 (c d : K) :
    backward K c d (X 2)=qT K c d := by simp [backward]


-- @@ L175-177 verbatim
@[simp] theorem backward_freeS (c d : K) (hunit : c*d=1) :
    backward K c d (freeS K d)=qS K c := by
  simpa [backward, freeS, coeff] using quotient_recover_s K c d hunit

-- @@ L178-181 verbatim
@[simp] theorem backward_freeX (c d : K) (hunit : c*d=1) :
    backward K c d (freeX K d)=qX K c := by
  simp only [freeX, map_sub, map_pow, backward_freeS K c d hunit]
  simp [backward]

-- @@ L182-185 verbatim
@[simp] theorem backward_freeY (c d : K) (hunit : c*d=1) :
    backward K c d (freeY K d)=qY K c := by
  simp only [freeY, map_add, map_pow, backward_freeS K c d hunit]
  simp [backward]

-- @@ L186-189 verbatim
@[simp] theorem backward_freeH (c d : K) (hunit : c*d=1) :
    backward K c d (freeH K c d)=qH K c := by
  simpa [freeH, backward_freeX K c d hunit, backward_freeY K c d hunit,
    backward_freeS K c d hunit, coeff] using (quotient_relation K c).symm

-- @@ L190-193 verbatim
@[simp] theorem backward_freeAlpha (c d : K) (hunit : c*d=1) :
    backward K c d (freeAlpha K c d)=qAlpha K c d := by
  simp [freeAlpha, qAlpha, coeff, backward_freeX K c d hunit,
    backward_freeS K c d hunit]

-- @@ L194-197 verbatim
@[simp] theorem backward_freeBeta (c d : K) (hunit : c*d=1) :
    backward K c d (freeBeta K c d)=qBeta K c d := by
  simp [freeBeta, qBeta, coeff, backward_freeX K c d hunit,
    backward_freeY K c d hunit, backward_freeS K c d hunit]


-- @@ L199-214 verbatim
theorem backward_free_original (c d : K) (hunit : c*d=1) :
    backward K c d (freeU K c d)=qU K c ∧
    backward K c d (freeV K c d)=qV K c ∧
    backward K c d (freeW K c d)=qW K c := by
  have hx : (qU K c)^3+qH K c*qV K c=qX K c := by
    simp [qU, qH, qV, qX, rawX]
  have hy : -(qU K c)^2+qH K c*qW K c=qY K c := by
    simp [qU, qH, qW, qY, rawY]
  have hs : S (qH K c) (qU K c) (qV K c) (qW K c)=qS K c := by
    simp [qH, qU, qV, qW, qS, rawS]
  have he := original_reconstruction _ _ _ _ _ _ _ _ _
    (quotient_bezout K c d hunit) hx hy hs
  simpa [freeU, freeV, freeW, freeG, backward_freeH K c d hunit,
    backward_freeX K c d hunit, backward_freeY K c d hunit,
    backward_freeS K c d hunit, backward_freeAlpha K c d hunit,
    backward_freeBeta K c d hunit, backward_X2, qT] using he


-- @@ L216-229 verbatim
theorem forward_backward (c d : K) (hunit : c*d=1) :
    (forward K c d hunit).comp (backward K c d)=AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i
  have ht := inverse_parameter (freeH K c d) (freeX K d) (freeY K d) (freeS K d)
    (freeAlpha K c d) (freeBeta K c d) (X 2) (free_bezout K c d hunit)
  fin_cases i
  · simp [backward, qX, qS, evaluation_x K c d hunit, evaluation_s K c d hunit,
      freeX]
  · simp [backward, qY, qS, evaluation_y K c d hunit, evaluation_s K c d hunit,
      freeY]
  · simpa [backward, qT, qAlpha, qBeta, coeff, qH, qU, qV, qW, qX, qY, qS,
      evaluation_x K c d hunit, evaluation_y K c d hunit, evaluation_s K c d hunit,
      freeAlpha, freeBeta, freeU, freeV, freeW, freeG] using ht


-- @@ L231-243 verbatim
theorem backward_forward (c d : K) (hunit : c*d=1) :
    (backward K c d).comp (forward K c d hunit)=AlgHom.id K _ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  obtain ⟨hu, hv, hw⟩ := backward_free_original K c d hunit
  change backward K c d (forward K c d hunit (qmap K c (X i)))=qmap K c (X i)
  rw [forward_qmap]
  fin_cases i
  · simpa [evaluation, values, qH, rawH] using backward_freeH K c d hunit
  · simpa [evaluation, values, qU, rawU] using hu
  · simpa [evaluation, values, qV, rawV] using hv
  · simpa [evaluation, values, qW, rawW] using hw


-- @@ L245-250 verbatim
/-- The complete explicit relative bridge. For a Laurent coefficient ring,
`c` is its Laurent variable and `d` its inverse. Both composites are proved. -/
def equivalence (c d : K) (hunit : c*d=1) :
    Q K c ≃ₐ[K] MvPolynomial (Fin 3) K :=
  AlgEquiv.ofAlgHom (forward K c d hunit) (backward K c d)
    (forward_backward K c d hunit) (backward_forward K c d hunit)


-- @@ L252-252 verbatim
end AbhyankarSathaye.CommutingDerivations.ParameterBridge


-- @@ L254-254 verbatim
end


-- @@ L256-256 verbatim
end OAI
