import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators ContDiff


-- @@ L8-8 verbatim
namespace ArnoldCounterexample


-- @@ L10-10 verbatim
abbrev CV := Fin 5 → ℂ


-- @@ L12-12 verbatim
def quadricPolynomial (z : CV) : ℂ := ∑ j, z j ^ 2


-- @@ L14-14 verbatim
def normSquared (z : CV) : ℝ := ∑ j, Complex.normSq (z j)


-- @@ L16-17 verbatim
def IsUnitQuadric (z : CV) : Prop :=
  normSquared z = 1 ∧ quadricPolynomial z = 0


-- @@ L19-19 verbatim
abbrev UnitQuadric := {z : CV // IsUnitQuadric z}


-- @@ L21-24 verbatim
lemma unitQuadric_ne_zero (z : UnitQuadric) : (z : CV) ≠ 0 := by
  intro h
  have hz := z.property.1
  simp [normSquared, h] at hz


-- @@ L26-29 verbatim
/-- The literal projective quadric sum z_j^2 = 0 in CP^4. -/
def Q3 := {q : Projectivization ℂ CV //
  ∃ (z : CV) (hz : z ≠ 0), Projectivization.mk ℂ z hz = q ∧
    quadricPolynomial z = 0}


-- @@ L31-36 verbatim
def project (z : UnitQuadric) : Q3 := by
  have hz : (z : CV) ≠ 0 := by
    intro h
    have hunit := z.property.1
    simp [normSquared, h] at hunit
  exact ⟨Projectivization.mk ℂ z hz, z, hz, rfl, z.property.2⟩


-- @@ L38-40 verbatim
/-- Horizontal lifts of the real tangent of Q3 at [z]. -/
def Horizontal (z v : CV) : Prop :=
  (∑ j, star (z j) * v j) = 0 ∧ (∑ j, z j * v j) = 0


-- @@ L42-43 verbatim
/-- The restricted Fubini--Study form, evaluated on horizontal lifts. -/
def omega (v w : CV) : ℝ := 2 * (∑ j, star (v j) * w j).im


-- @@ L45-49 verbatim
/-- A local smooth extension of the pullback of h to the unit isotropic cone. -/
def LocalFunctionLift (h : Q3 → ℝ) (z : UnitQuadric)
    (U : Set CV) (g : CV → ℝ) : Prop :=
  IsOpen U ∧ (z : CV) ∈ U ∧ ContDiffOn ℝ ∞ g U ∧
    ∀ y : UnitQuadric, (y : CV) ∈ U → g y = h (project y)


-- @@ L51-52 verbatim
def IsSmoothFunction (h : Q3 → ℝ) : Prop :=
  ∀ z : UnitQuadric, ∃ (U : Set CV) (g : CV → ℝ), LocalFunctionLift h z U g


-- @@ L54-56 verbatim
structure SmoothFunction where
  toFun : Q3 → ℝ
  smooth : IsSmoothFunction toFun


-- @@ L58-62 verbatim
/-- dh_q = 0, expressed using all local lifts, independent of normal extensions. -/
def IsCritical (h : Q3 → ℝ) (q : Q3) : Prop :=
  ∀ z : UnitQuadric, project z = q →
    ∀ (U : Set CV) (g : CV → ℝ), LocalFunctionLift h z U g →
      ∀ v : CV, Horizontal z v → fderiv ℝ g z v = 0


-- @@ L64-64 verbatim
def criticalSet (h : SmoothFunction) : Set Q3 := {q | IsCritical h.toFun q}


-- @@ L66-67 verbatim
/-- The minimum critical number, including degenerate functions (ENat allows infinity). -/
def criticalNumber : ℕ∞ := ⨅ h : SmoothFunction, (criticalSet h).encard


-- @@ L69-98 verbatim
/-- An explicit smooth lift of a Hamiltonian isotopy, with inverse and generator.
The Hamiltonian equation uses i_X omega = dH. -/
structure HamiltonianPath (φ : Q3 ≃ Q3) where
  forward : ℝ × CV → CV
  backward : ℝ × CV → CV
  hamiltonian : ℝ × CV → ℝ
  forward_smooth : ContDiff ℝ ∞ forward
  backward_smooth : ContDiff ℝ ∞ backward
  hamiltonian_smooth : ContDiff ℝ ∞ hamiltonian
  forward_preserves : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric,
    IsUnitQuadric (forward (t, z))
  backward_preserves : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric,
    IsUnitQuadric (backward (t, z))
  forward_phase : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric,
    ∀ a : ℂ, Complex.normSq a = 1 → forward (t, a • (z : CV)) = a • forward (t, z)
  backward_phase : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric,
    ∀ a : ℂ, Complex.normSq a = 1 → backward (t, a • (z : CV)) = a • backward (t, z)
  hamiltonian_phase : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric,
    ∀ a : ℂ, Complex.normSq a = 1 → hamiltonian (t, a • (z : CV)) = hamiltonian (t, z)
  left_inverse : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric,
    backward (t, forward (t, z)) = z
  right_inverse : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric,
    forward (t, backward (t, z)) = z
  start : ∀ z : UnitQuadric, forward (0, z) = z
  finish : ∀ z : UnitQuadric,
    project ⟨forward (1, z), forward_preserves 1 (by norm_num) z⟩ = φ (project z)
  equation : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ z : UnitQuadric, ∀ v : CV,
    Horizontal (forward (t, z)) v →
      omega (deriv (fun s : ℝ => forward (s, z)) t) v =
        fderiv ℝ (fun w : CV => hamiltonian (t, w)) (forward (t, z)) v


-- @@ L100-100 verbatim
def IsHamiltonian (φ : Q3 ≃ Q3) : Prop := Nonempty (HamiltonianPath φ)


-- @@ L102-102 verbatim
def fixedSet (φ : Q3 ≃ Q3) : Set Q3 := {q | φ q = q}


-- @@ L104-112 verbatim
/-- Eigenvalue 1 in the derivative on the quotient tangent, not an ambient
  spurious vertical eigenvector. v is nonzero and horizontal. -/
def HasDegenerateFixedPoint (φ : Q3 ≃ Q3) : Prop :=
  ∃ (z : UnitQuadric) (v : CV), φ (project z) = project z ∧ v ≠ 0 ∧
    Horizontal z v ∧ ∃ (U : Set CV) (G : CV → CV),
      IsOpen U ∧ (z : CV) ∈ U ∧ ContDiffOn ℝ ∞ G U ∧ G z = z ∧
      (∀ y : UnitQuadric, (y : CV) ∈ U →
        ∃ hy : IsUnitQuadric (G y), project ⟨G y, hy⟩ = φ (project y)) ∧
      ∃ a : ℝ, fderiv ℝ G z v - v = a • (Complex.I • (z : CV))


-- @@ L114-114 verbatim
end ArnoldCounterexample


-- @@ L116-116 verbatim
end


-- @@ L118-118 verbatim
end OAI
