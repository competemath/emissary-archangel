/-
# Sofa/Motion.lean — building upstream motions `I → E(2)` (M2 / M-H infrastructure)

* `continuous_motion_of_continuous_apply`: a family of rigid motions is continuous for the
  upstream topology on `E(2)` as soon as every orbit `x ↦ m x q` is continuous.
* coordinates of clockwise rotations, continuity of `u`, `v`, `rot`,
  and `rotateTranslate` in terms of `rot`.

STATUS: [PROOF-C-local] [AXIOM-CHECK] round 1 (2026-09-17, Opus 5): compiled in the cloud dev tree
(Lean 4.33.1, Mathlib v4.33.1 with subset imports), no `sorry`; full `import Mathlib` re-check pending.
-/
import Sofa.RotationAngle


-- @@ L14-14 verbatim
noncomputable section


-- @@ L16-16 verbatim
open Real Set MovingSofa

-- @@ L17-17 verbatim
open scoped EuclideanGeometry RealInnerProductSpace unitInterval


-- @@ L19-19 verbatim
namespace Sofa


-- @@ L21-48 expanded
/-- A family of rigid motions is continuous (for the upstream topology on `E(2)`) as soon as
every orbit `x ↦ m x q` is continuous (`ℝ²` is finite dimensional). -/
theorem continuous_motion_of_continuous_apply {X : Type*} [TopologicalSpace X]
    {m : X → EuclideanSpace ℝ (Fin 2) ≃ᵃⁱ[ℝ] EuclideanSpace ℝ (Fin 2)}
    (h : ∀ q, Continuous fun x => m x q) : Continuous m :=
  by
  rw [continuous_induced_rng]
  let D :=
    ContinuousAffineMap.decompLinearIsometryEquiv ℝ ℝ (EuclideanSpace ℝ (Fin 2))
      (EuclideanSpace ℝ (Fin 2))
  have hsymm :
    ∀ (f : EuclideanSpace ℝ (Fin 2) →ᴬ[ℝ] EuclideanSpace ℝ (Fin 2)) (y : EuclideanSpace ℝ (Fin 2)),
      f y = (D f).2 y + (D f).1 :=
    by
    intro f y
    have e :=
      ContinuousAffineMap.decompLinearIsometryEquiv_symm_apply ℝ ℝ (EuclideanSpace ℝ (Fin 2))
        (EuclideanSpace ℝ (Fin 2)) (D f) y
    rwa [LinearIsometryEquiv.symm_apply_apply] at e
  have hfst : ∀ f : EuclideanSpace ℝ (Fin 2) →ᴬ[ℝ] EuclideanSpace ℝ (Fin 2), (D f).1 = f 0 :=
    fun _ => rfl
  have hcoe :
    ∀ (x : X) (y : EuclideanSpace ℝ (Fin 2)),
      (m x).toAffineIsometry.toContinuousAffineMap y = m x y :=
    fun _ _ => rfl
  have h1 : Continuous fun x => (D (m x).toAffineIsometry.toContinuousAffineMap).1 :=
    by
    simp only [hfst, hcoe]
    exact h 0
  have h2 : Continuous fun x => (D (m x).toAffineIsometry.toContinuousAffineMap).2 :=
    by
    refine continuous_clm_apply.2 fun y => ?_
    have key : ∀ x, (D (m x).toAffineIsometry.toContinuousAffineMap).2 y = m x y - m x 0 :=
      by
      intro x
      have e := hsymm (m x).toAffineIsometry.toContinuousAffineMap y
      rw [hfst, hcoe, hcoe] at e
      rw [e]; abel
    simp only [key]
    exact (h y).sub (h 0)
  have h3 := D.symm.continuous.comp (h1.prodMk h2)
  refine h3.congr fun x => ?_
  simp only [Function.comp_apply, Prod.mk.eta, LinearIsometryEquiv.symm_apply_apply]


-- @@ L50-50 verbatim
/-! ## Rotations in coordinates -/


-- @@ L52-53 verbatim
lemma u_eq_smul (t : ℝ) : u t = cos t • e₀ + sin t • e₁ := by
  ext i; fin_cases i <;> simp [u, e₀, e₁]


-- @@ L55-56 verbatim
lemma v_eq_smul (t : ℝ) : v t = (-sin t) • e₀ + cos t • e₁ := by
  ext i; fin_cases i <;> simp [v, e₀, e₁]


-- @@ L58-60 verbatim
lemma continuous_u : Continuous u := by
  have : u = fun t => cos t • e₀ + sin t • e₁ := funext u_eq_smul
  rw [this]; fun_prop


-- @@ L62-64 verbatim
lemma continuous_v : Continuous v := by
  have : v = fun t => (-sin t) • e₀ + cos t • e₁ := funext v_eq_smul
  rw [this]; fun_prop


-- @@ L66-66 expanded
lemma continuous_coord (i : Fin 2) : Continuous fun p : EuclideanSpace ℝ (Fin 2) => p i := by
  fun_prop


-- @@ L68-75 expanded
lemma continuous_rot_apply {X : Type*} [TopologicalSpace X] {θ : X → ℝ}
    {p : X → EuclideanSpace ℝ (Fin 2)} (hθ : Continuous θ) (hp : Continuous p) :
    Continuous fun x => rot (θ x) (p x) :=
  by
  have : (fun x => rot (θ x) (p x)) = fun x => p x 0 • u (θ x) + p x 1 • v (θ x) := by funext x;
    exact rot_eq_smul _ _
  rw [this]
  have h0 : Continuous fun x => p x 0 := (continuous_coord 0).comp hp
  have h1 : Continuous fun x => p x 1 := (continuous_coord 1).comp hp
  exact (h0.smul (continuous_u.comp hθ)).add (h1.smul (continuous_v.comp hθ))


-- @@ L77-79 expanded
/-- `R_{-t} w = (⟪w, u_t⟫, ⟪w, v_t⟫)`. -/
lemma rot_neg_coord_zero (t : ℝ) (w : EuclideanSpace ℝ (Fin 2)) : rot (-t) w 0 = ⟪w, u t⟫ := by
  rw [rot_coord_zero, inner_eq, u_coord_zero, u_coord_one, cos_neg, sin_neg]; ring


-- @@ L81-82 expanded
lemma rot_neg_coord_one (t : ℝ) (w : EuclideanSpace ℝ (Fin 2)) : rot (-t) w 1 = ⟪w, v t⟫ := by
  rw [rot_coord_one, inner_eq, v_coord_zero, v_coord_one, cos_neg, sin_neg]; ring


-- @@ L84-87 expanded
/-- The upstream `rotateTranslate` in terms of `rot`. -/
lemma rotateTranslate_apply_eq_rot (t : ℝ) (p q : EuclideanSpace ℝ (Fin 2)) :
    rotateTranslate (t : Real.Angle) p q = rot t (q + p) := by
  rw [rotateTranslate_apply, rot_eq_rotation]


-- @@ L89-89 verbatim
/-! ## Points of the plane -/


-- @@ L91-92 expanded
/-- The point `(a, b)`. -/
def pt (a b : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  a • e₀ + b • e₁


-- @@ L94-94 verbatim
@[simp] lemma pt_zero (a b : ℝ) : pt a b 0 = a := by simp [pt, e₀, e₁]

-- @@ L95-95 verbatim
@[simp] lemma pt_one (a b : ℝ) : pt a b 1 = b := by simp [pt, e₀, e₁]


-- @@ L97-97 expanded
lemma eq_pt (p : EuclideanSpace ℝ (Fin 2)) : p = pt (p 0) (p 1) :=
  decomp_e p


-- @@ L99-99 verbatim
lemma continuous_pt : Continuous fun ab : ℝ × ℝ => pt ab.1 ab.2 := by unfold pt; fun_prop

-- @@ L100-100 verbatim
lemma continuous_pt_left (b : ℝ) : Continuous fun a => pt a b := by unfold pt; fun_prop

-- @@ L101-101 verbatim
lemma continuous_pt_right (a : ℝ) : Continuous fun b => pt a b := by unfold pt; fun_prop


-- @@ L103-103 verbatim
lemma le_one_of_sq_le_one {a : ℝ} (h : a ^ 2 ≤ 1) : a ≤ 1 := by nlinarith


-- @@ L105-105 verbatim
end Sofa
