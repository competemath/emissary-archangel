import Mathlib
import Submission.FrameGaugeNormalization
import Submission.AmbientLocalizedRotation


-- @@ L5-17 verbatim
/-!
# Relative product control for normalization cobordisms

Componentwise normalization is useful only if every later move leaves the
components already put in standard position literally unchanged.  This file
records that invariant at the level of the actual space-time defining map and
sign label, proves that it survives cobordism gluing, and carries it through the
three stages of `signedNormalizationCobordism`.

In particular, a localized ambient rotation supported in the ball of squared
radius two can be used in a normalization step while the final glued signed
cobordism remains a product over every component outside that ball.
-/


-- @@ L19-19 verbatim
set_option autoImplicit false


-- @@ L21-21 verbatim
noncomputable section


-- @@ L23-23 verbatim
open Set Function

-- @@ L24-24 verbatim
open scoped Topology ContDiff RealInnerProductSpace


-- @@ L26-26 verbatim
namespace Submission


-- @@ L28-28 verbatim
variable {n : ℕ}


-- @@ L30-30 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L31-31 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L33-33 verbatim
/-! ## Product regions survive gluing -/


-- @@ L35-35 verbatim
namespace FramedLevelCobordism


-- @@ L37-39 verbatim
/-- The space-time defining map is literally the product of `g` over `K`. -/
def ProductOn (C : FramedLevelCobordism n) (K : Set E) (g : E → F) : Prop :=
  ∀ x ∈ K, ∀ t : ℝ, C.G (spaceTime x t) = g x


-- @@ L41-53 verbatim
/-- Gluing two product cobordisms over the same set produces another literal
product there. -/
theorem ProductOn.trans {C₁ C₂ : FramedLevelCobordism n} {K : Set E}
    {g : E → F} (h₁ : C₁.ProductOn K g) (h₂ : C₂.ProductOn K g)
    (hmid : C₁.X₁ = C₂.X₀) : (C₁.trans C₂ hmid).ProductOn K g := by
  intro x hx t
  change transFun C₁ C₂ (spaceTime x t) = g x
  rw [transFun, vertC_spaceTime]
  by_cases ht : t < 1 / 2
  · rw [if_pos ht, reparamMap, initCLM_spaceTime, vertC_spaceTime]
    exact h₁ x hx (3 * t + -(1 / 2))
  · rw [if_neg ht, reparamMap, initCLM_spaceTime, vertC_spaceTime]
    exact h₂ x hx (3 * t + -(3 / 2))


-- @@ L55-55 verbatim
end FramedLevelCobordism


-- @@ L57-57 verbatim
namespace SignedFramedLevelCobordism


-- @@ L59-64 verbatim
/-- Both the defining map and sign extension are literal products over `K`. -/
def ProductOn {X₀ X₁ : FramedLevelSet n} {S₀ : FiberSign X₀}
    {S₁ : FiberSign X₁} (C : SignedFramedLevelCobordism S₀ S₁)
    (K : Set E) (g : E → F) (σ : E → ℝ) : Prop :=
  C.cobordism.ProductOn K g ∧
    ∀ x ∈ K, ∀ t : ℝ, C (spaceTime x t) = σ x


-- @@ L66-83 verbatim
/-- Signed gluing preserves a common literal product region. -/
theorem ProductOn.trans {X₀ X₁ X₂ : FramedLevelSet n}
    {S₀ : FiberSign X₀} {S₁ : FiberSign X₁} {S₂ : FiberSign X₂}
    {C₁ : SignedFramedLevelCobordism S₀ S₁}
    {C₂ : SignedFramedLevelCobordism S₁ S₂}
    {K : Set E} {g : E → F} {σ : E → ℝ}
    (h₁ : C₁.ProductOn K g σ) (h₂ : C₂.ProductOn K g σ) :
    (SignedFramedLevelCobordism.trans C₁ C₂).ProductOn K g σ := by
  constructor
  · exact h₁.1.trans h₂.1 (C₁.target_eq.trans C₂.source_eq.symm)
  · intro x hx t
    change SignedFramedLevelCobordism.transFun C₁ C₂ (spaceTime x t) = σ x
    rw [SignedFramedLevelCobordism.transFun, vertC_spaceTime]
    by_cases ht : t < 1 / 2
    · rw [if_pos ht, reparamMap, initCLM_spaceTime, vertC_spaceTime]
      exact h₁.2 x hx (3 * t + -(1 / 2))
    · rw [if_neg ht, reparamMap, initCLM_spaceTime, vertC_spaceTime]
      exact h₂.2 x hx (3 * t + -(3 / 2))


-- @@ L85-85 verbatim
end SignedFramedLevelCobordism


-- @@ L87-87 verbatim
/-! ## Relative ambient and defining-map stages -/


-- @@ L89-89 verbatim
namespace SmoothAmbientIsotopy


-- @@ L91-100 verbatim
/-- A relative ambient sweep is a literal signed product on its fixed set. -/
theorem FixedOn.signedCobordism_productOn {A : SmoothAmbientIsotopy n}
    {K : Set E} (hA : A.FixedOn K) {X : FramedLevelSet n}
    (S : FiberSign X) :
    (A.signedCobordism S).ProductOn K X.g S := by
  constructor
  · intro x hx t
    exact hA.cobordism_product X hx t
  · intro x hx t
    exact hA.signedCobordism_product S hx t


-- @@ L102-102 verbatim
end SmoothAmbientIsotopy


-- @@ L104-104 verbatim
namespace DefiningMapHomotopy


-- @@ L106-110 verbatim
/-- A defining-map homotopy is stationary over `K` when all its maps agree
there with one fixed defining map. -/
def FixedOn {X₀ X₁ : FramedLevelSet n} (D : DefiningMapHomotopy X₀ X₁)
    (K : Set E) (g : E → F) : Prop :=
  ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ K, D.H s x = g x


-- @@ L112-125 verbatim
/-- The signed cobordism of a stationary defining-map homotopy is a literal
product over its stationary set. -/
theorem FixedOn.signedCobordism_productOn {X₀ X₁ : FramedLevelSet n}
    {D : DefiningMapHomotopy X₀ X₁} {K : Set E} {g : E → F}
    (hD : D.FixedOn K g) (S : FiberSign X₀) :
    (D.signedCobordism S).ProductOn K g S := by
  constructor
  · intro x hx t
    change D.cobMap (spaceTime x t) = g x
    rw [D.cobMap_spaceTime]
    exact hD (normRamp t) ⟨normRamp_nonneg t, normRamp_le_one t⟩ x hx
  · intro x hx t
    change S (initCLM (n + 1) (spaceTime x t)) = S x
    rw [initCLM_spaceTime]


-- @@ L127-140 verbatim
/-- A gauge family which is the identity over `K` gives a stationary
defining-map homotopy there. -/
theorem FixedOn.ofGauge (X : FramedLevelSet n)
    (Q : ℝ → E → F →L[ℝ] F)
    (hQ : ContDiff ℝ ∞ (fun p : ℝ × E => Q p.1 p.2))
    (hQzero : ∀ x, Q 0 x = ContinuousLinearMap.id ℝ F)
    (hQbij : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x, Bijective (Q s x))
    {K : Set E}
    (hQK : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x ∈ K,
      Q s x = ContinuousLinearMap.id ℝ F) :
    (ofGauge X Q hQ hQzero hQbij).FixedOn K X.g := by
  intro s hs x hx
  rw [ofGauge_H, hQK s hs x hx]
  rfl


-- @@ L142-142 verbatim
end DefiningMapHomotopy


-- @@ L144-144 verbatim
/-! ## The full three-stage normalization -/


-- @@ L146-146 verbatim
namespace SmoothAmbientIsotopy


-- @@ L148-194 verbatim
/-- If the ambient move and the frame homotopy preserve `K`, and the target
label agrees there, then the complete ambient/frame/sign normalization
cobordism is a literal product over `K`, even after both gluings. -/
theorem signedNormalizationCobordism_productOn
    (A : SmoothAmbientIsotopy n) {X Y : FramedLevelSet n}
    (D : DefiningMapHomotopy (A.pullback X) Y)
    (S : FiberSign X) (T : FiberSign Y)
    (hpos : ∀ x ∈ Y.fiber,
      (0 < (A.pullbackSign S).restrict D.fiber_subset x ↔ 0 < T x))
    {K : Set E} (hA : A.FixedOn K)
    (hD : D.FixedOn K X.g) (hT : ∀ x ∈ K, T x = S x) :
    (signedNormalizationCobordism A D S T hpos).ProductOn K X.g S := by
  let C₁ := A.signedCobordism S
  let C₂ := D.signedCobordism (A.pullbackSign S)
  let C₃ := signInterpolationCobordism
    ((A.pullbackSign S).restrict D.fiber_subset) T hpos
  have hC₁ : C₁.ProductOn K X.g S :=
    hA.signedCobordism_productOn S
  have hC₂ : C₂.ProductOn K X.g S := by
    constructor
    · intro x hx t
      change D.cobMap (spaceTime x t) = X.g x
      rw [D.cobMap_spaceTime]
      exact hD (normRamp t) ⟨normRamp_nonneg t, normRamp_le_one t⟩ x hx
    · intro x hx t
      change A.pullbackSign S (initCLM (n + 1) (spaceTime x t)) = S x
      rw [initCLM_spaceTime]
      exact hA.pullbackSign_eq S hx
  have hYg : ∀ x ∈ K, Y.g x = X.g x := by
    intro x hx
    rw [← congrFun D.H_one x]
    exact hD 1 ⟨zero_le_one, le_rfl⟩ x hx
  have hC₃ : C₃.ProductOn K X.g S := by
    constructor
    · intro x hx t
      change Y.g (initCLM (n + 1) (spaceTime x t)) = X.g x
      rw [initCLM_spaceTime, hYg x hx]
    · intro x hx t
      change
        (1 - normRamp (vertC (spaceTime x t))) *
              A.pullbackSign S (initCLM (n + 1) (spaceTime x t)) +
            normRamp (vertC (spaceTime x t)) *
              T (initCLM (n + 1) (spaceTime x t)) = S x
      rw [vertC_spaceTime, initCLM_spaceTime,
        hA.pullbackSign_eq S hx, hT x hx]
      ring
  exact hC₁.trans (hC₂.trans hC₃)


-- @@ L196-196 verbatim
end SmoothAmbientIsotopy


-- @@ L198-198 verbatim
/-! ## Localized rotation specialization -/


-- @@ L200-200 verbatim
namespace SmoothAmbientIsotopy


-- @@ L202-202 verbatim
variable {m : ℕ}


-- @@ L204-225 verbatim
/-- A normalization step whose ambient part is the explicit localized plane
rotation is a product over any set outside its support, provided the subsequent
frame and sign steps are stationary there as well. -/
theorem localizedPlaneRotation_signedNormalization_productOn
    (θ : ℝ) {X Y : FramedLevelSet (m + 1)}
    (D : DefiningMapHomotopy
      ((localizedPlaneRotation (m := m) θ).pullback X) Y)
    (S : FiberSign X) (T : FiberSign Y)
    (hpos : ∀ x ∈ Y.fiber,
      (0 < ((localizedPlaneRotation (m := m) θ).pullbackSign S).restrict
          D.fiber_subset x ↔ 0 < T x))
    {K : Set (EuclideanSpace ℝ (Fin (m + 2)))}
    (hK : K ⊆ {x | 2 ≤ localRadialSq x})
    (hD : D.FixedOn K X.g) (hT : ∀ x ∈ K, T x = S x) :
    (signedNormalizationCobordism (localizedPlaneRotation (m := m) θ)
      D S T hpos).ProductOn K X.g S := by
  apply signedNormalizationCobordism_productOn
    (A := localizedPlaneRotation (m := m) θ) (D := D)
    (S := S) (T := T) hpos
  · exact (localizedPlaneRotation_fixedOn (m := m) θ).mono hK
  · exact hD
  · exact hT


-- @@ L227-227 verbatim
end SmoothAmbientIsotopy


-- @@ L229-229 verbatim
end Submission
