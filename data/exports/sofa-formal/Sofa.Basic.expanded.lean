/-
# Sofa/Basic.lean — M1 foundations (Baek, *Optimality of Gerver's Sofa*, §2.1–2.3 notation)

STATUS: round 4 (2026-09-17, Opus 5): [PROOF-C-local] [AXIOM-CHECK] — the last `sorry`
(`rot_eq_rotation`) is replaced by a proof via `Orientation.areaForm` / `volumeForm_robust`
(two fixes were needed: pass `o` explicitly to `volumeForm_robust`; `Basis` is now `Module.Basis`).
Earlier: round 2 (2026-09-16). Round 1 failed only because Mathlib's scoped notation is `⟪x, y⟫`
(no `_ℝ` suffix); the parse errors cascaded.  Fixed here together with the renamed lemmas
(`le_of_not_gt`, `Set.mem_sdiff`, `Set.sdiff_eq`).  Round 3: only `rot_smul` (needs `ring`) and
`rot_u` (`simp` already closes it) were left; everything else compiled in round 2.
Design (see PLAN.md §3.2): angles are real numbers, rotations are explicit coordinate formulas,
inner products are expanded with `inner_eq` and finished with `ring`/`linear_combination`.
-/
import Sofa.Hammersley


-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
open Real Set

-- @@ L19-19 verbatim
open scoped EuclideanGeometry RealInnerProductSpace


-- @@ L21-21 verbatim
namespace Sofa


-- @@ L23-23 verbatim
/-! ## Coordinates -/


-- @@ L25-27 expanded
/-- The inner product of `ℝ²` in coordinates. -/
lemma inner_eq (p q : EuclideanSpace ℝ (Fin 2)) : ⟪p, q⟫ = p 0 * q 0 + p 1 * q 1 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, mul_comm]


-- @@ L29-29 expanded
@[simp]
lemma vec_coord_zero (x y : ℝ) : (!₂[x, y] : EuclideanSpace ℝ (Fin 2)) 0 = x :=
  rfl


-- @@ L30-30 expanded
@[simp]
lemma vec_coord_one (x y : ℝ) : (!₂[x, y] : EuclideanSpace ℝ (Fin 2)) 1 = y :=
  rfl


-- @@ L32-32 verbatim
/-! ## Unit vectors `u_t = (cos t, sin t)` and `v_t = (-sin t, cos t)` (Def 2.1.3) -/


-- @@ L34-35 expanded
/-- `u_t = (cos t, sin t)`. -/
def u (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[cos t, sin t]


-- @@ L37-38 expanded
/-- `v_t = (-sin t, cos t)`. -/
def v (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  !₂[-sin t, cos t]


-- @@ L40-40 verbatim
@[simp] lemma u_coord_zero (t : ℝ) : u t 0 = cos t := rfl

-- @@ L41-41 verbatim
@[simp] lemma u_coord_one (t : ℝ) : u t 1 = sin t := rfl

-- @@ L42-42 verbatim
@[simp] lemma v_coord_zero (t : ℝ) : v t 0 = -sin t := rfl

-- @@ L43-43 verbatim
@[simp] lemma v_coord_one (t : ℝ) : v t 1 = cos t := rfl


-- @@ L45-47 verbatim
lemma inner_u_u (t : ℝ) : ⟪u t, u t⟫ = 1 := by
  rw [inner_eq, u_coord_zero, u_coord_one]
  linear_combination cos_sq_add_sin_sq t


-- @@ L49-51 verbatim
lemma inner_v_v (t : ℝ) : ⟪v t, v t⟫ = 1 := by
  rw [inner_eq, v_coord_zero, v_coord_one]
  linear_combination cos_sq_add_sin_sq t


-- @@ L53-54 verbatim
lemma inner_u_v (t : ℝ) : ⟪u t, v t⟫ = 0 := by
  rw [inner_eq, u_coord_zero, u_coord_one, v_coord_zero, v_coord_one]; ring


-- @@ L56-57 verbatim
lemma inner_v_u (t : ℝ) : ⟪v t, u t⟫ = 0 := by
  rw [real_inner_comm]; exact inner_u_v t


-- @@ L59-63 verbatim
lemma norm_u (t : ℝ) : ‖u t‖ = 1 := by
  have h := real_inner_self_eq_norm_sq (u t)
  rw [inner_u_u] at h
  have h2 : (‖u t‖ - 1) * (‖u t‖ + 1) = 0 := by linear_combination (-1 : ℝ) * h
  rcases mul_eq_zero.1 h2 with h3 | h3 <;> linarith [norm_nonneg (u t)]


-- @@ L65-66 verbatim
lemma u_add_pi_div_two (t : ℝ) : u (t + π / 2) = v t := by
  ext i; fin_cases i <;> simp [u, v, cos_add_pi_div_two, sin_add_pi_div_two]


-- @@ L68-69 verbatim
lemma v_add_pi_div_two (t : ℝ) : v (t + π / 2) = -u t := by
  ext i; fin_cases i <;> simp [u, v, cos_add_pi_div_two, sin_add_pi_div_two]


-- @@ L71-72 verbatim
lemma u_add_pi (t : ℝ) : u (t + π) = -u t := by
  ext i; fin_cases i <;> simp [u, cos_add_pi, sin_add_pi]


-- @@ L74-75 verbatim
lemma u_add_two_pi (t : ℝ) : u (t + 2 * π) = u t := by
  ext i; fin_cases i <;> simp [u, cos_add_two_pi, sin_add_two_pi]


-- @@ L77-77 verbatim
lemma u_zero : u 0 = !₂[1, 0] := by ext i; fin_cases i <;> simp [u]


-- @@ L79-79 verbatim
lemma u_pi_div_two : u (π / 2) = !₂[0, 1] := by ext i; fin_cases i <;> simp [u]


-- @@ L81-82 expanded
/-- `⟪p, u 0⟫ = p 0` and `⟪p, u (π/2)⟫ = p 1`. -/
lemma inner_u_zero (p : EuclideanSpace ℝ (Fin 2)) : ⟪p, u 0⟫ = p 0 := by rw [inner_eq]; simp


-- @@ L83-83 expanded
lemma inner_u_pi_div_two (p : EuclideanSpace ℝ (Fin 2)) : ⟪p, u (π / 2)⟫ = p 1 := by rw [inner_eq];
  simp


-- @@ L85-90 expanded
/-- Every vector decomposes along the orthonormal frame `(u_t, v_t)`. -/
lemma decomp_u_v (t : ℝ) (p : EuclideanSpace ℝ (Fin 2)) : p = ⟪p, u t⟫ • u t + ⟪p, v t⟫ • v t :=
  by
  ext i
  fin_cases i
  · simp [inner_eq, u, v]; linear_combination (-(p 0)) * cos_sq_add_sin_sq t
  · simp [inner_eq, u, v]; linear_combination (-(p 1)) * cos_sq_add_sin_sq t


-- @@ L92-95 verbatim
/-! ## Frame vectors at two angles

Every inner product between `u`, `v` at two angles, in the forms used downstream.  Round 42
collected these here; before, several modules re-proved them under other names. -/


-- @@ L97-98 expanded
lemma inner_u_decomp (q : EuclideanSpace ℝ (Fin 2)) (t : ℝ) :
    ⟪q, u t⟫ = q 0 * cos t + q 1 * sin t := by simp only [inner_eq, u_coord_zero, u_coord_one]


-- @@ L100-102 verbatim
/-- `⟪u_t, u_s⟫ = cos (t - s)`. -/
lemma inner_u_u_eq_cos (t s : ℝ) : ⟪u t, u s⟫ = cos (t - s) := by
  rw [inner_eq, u_coord_zero, u_coord_one, u_coord_zero, u_coord_one, cos_sub]


-- @@ L104-107 verbatim
lemma inner_u_u_add (s d : ℝ) : ⟪u s, u (s + d)⟫ = cos d := by
  rw [inner_eq, u_coord_zero, u_coord_one, u_coord_zero, u_coord_one,
    show s + d = d + s by ring, Real.cos_add, Real.sin_add]
  linear_combination (cos d) * sin_sq_add_cos_sq s


-- @@ L109-112 verbatim
lemma inner_v_u_add (s d : ℝ) : ⟪v s, u (s + d)⟫ = sin d := by
  rw [inner_eq, v_coord_zero, v_coord_one, u_coord_zero, u_coord_one,
    show s + d = d + s by ring, Real.cos_add, Real.sin_add]
  linear_combination (sin d) * sin_sq_add_cos_sq s


-- @@ L114-116 verbatim
lemma inner_u_u_sub (s r : ℝ) : ⟪u s, u r⟫ = cos (r - s) := by
  have h := inner_u_u_add s (r - s)
  rwa [show s + (r - s) = r by ring] at h


-- @@ L118-119 verbatim
lemma inner_v_u_eq_sin (t s : ℝ) : ⟪v t, u s⟫ = sin (s - t) := by
  rw [inner_eq, u_coord_zero, u_coord_one, v_coord_zero, v_coord_one, sin_sub]; ring


-- @@ L121-122 verbatim
lemma inner_v_v_eq_cos (t s : ℝ) : ⟪v t, v s⟫ = cos (s - t) := by
  rw [inner_eq, v_coord_zero, v_coord_one, v_coord_zero, v_coord_one, cos_sub]; ring


-- @@ L124-125 verbatim
lemma inner_u_v_eq_sin (θ t : ℝ) : ⟪u θ, v t⟫ = sin (θ - t) := by
  rw [inner_eq, u_coord_zero, u_coord_one, v_coord_zero, v_coord_one, sin_sub]; ring


-- @@ L127-129 verbatim
lemma inner_u_v_eq_neg_sin (τ s : ℝ) : ⟪u τ, v s⟫ = -sin (s - τ) := by
  rw [inner_eq]; simp only [u_coord_zero, u_coord_one, v_coord_zero, v_coord_one]; rw [sin_sub]
  ring


-- @@ L131-132 verbatim
lemma inner_add_smul_u_v (a b t : ℝ) : ⟪a • u t + b • v t, u t⟫ = a := by
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_u, inner_v_u]; ring


-- @@ L134-135 verbatim
lemma inner_add_smul_v_v (a b t : ℝ) : ⟪a • u t + b • v t, v t⟫ = b := by
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left, inner_u_v, inner_v_v]; ring


-- @@ L137-137 verbatim
lemma v_zero_eq : v 0 = u (π / 2) := by rw [← u_add_pi_div_two, zero_add]


-- @@ L139-144 expanded
/-- Coordinatewise extensionality in `ℝ²`. -/
lemma ext_two {p q : EuclideanSpace ℝ (Fin 2)} (h0 : p 0 = q 0) (h1 : p 1 = q 1) : p = q :=
  by
  ext i
  fin_cases i
  · exact h0
  · exact h1


-- @@ L146-148 verbatim
lemma sin_cos_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ π / 2) : 0 ≤ sin t ∧ 0 ≤ cos t :=
  ⟨sin_nonneg_of_nonneg_of_le_pi ht0 (by linarith [pi_pos]),
    cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], ht1⟩⟩


-- @@ L150-150 verbatim
/-! ## Lines and half-planes (Def 2.1.4, 2.1.5) -/


-- @@ L152-153 expanded
/-- `l(t,h)`: the line with normal angle `t` and signed distance `h` from the origin. -/
def line (t h : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | ⟪p, u t⟫ = h}


-- @@ L154-155 expanded
/-- `H₋(t,h)`: closed half-plane with normal angle `t` (outward normal `u_t`). -/
def hpLe (t h : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | ⟪p, u t⟫ ≤ h}


-- @@ L156-157 expanded
/-- `H₋°(t,h)`: open version of `hpLe`. -/
def hpLt (t h : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | ⟪p, u t⟫ < h}


-- @@ L158-159 expanded
/-- `H₊(t,h)`: closed half-plane with normal angle `t + π`. -/
def hpGe (t h : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | h ≤ ⟪p, u t⟫}


-- @@ L160-161 expanded
/-- `H₊°(t,h)`: open version of `hpGe`. -/
def hpGt (t h : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | h < ⟪p, u t⟫}


-- @@ L163-164 verbatim
lemma hpGe_eq_hpLe_neg (t h : ℝ) : hpGe t h = hpLe (t + π) (-h) := by
  ext p; simp [hpGe, hpLe, u_add_pi, inner_neg_right]


-- @@ L166-167 verbatim
lemma hpGt_eq_hpLt_neg (t h : ℝ) : hpGt t h = hpLt (t + π) (-h) := by
  ext p; simp [hpGt, hpLt, u_add_pi, inner_neg_right]


-- @@ L169-170 expanded
lemma continuous_inner_u (t : ℝ) : Continuous fun p : EuclideanSpace ℝ (Fin 2) => ⟪p, u t⟫ := by
  fun_prop


-- @@ L172-173 verbatim
lemma isClosed_hpLe (t h : ℝ) : IsClosed (hpLe t h) := by
  unfold hpLe; exact isClosed_le (continuous_inner_u t) continuous_const

-- @@ L174-175 verbatim
lemma isClosed_hpGe (t h : ℝ) : IsClosed (hpGe t h) := by
  unfold hpGe; exact isClosed_le continuous_const (continuous_inner_u t)

-- @@ L176-177 verbatim
lemma isOpen_hpLt (t h : ℝ) : IsOpen (hpLt t h) := by
  unfold hpLt; exact isOpen_lt (continuous_inner_u t) continuous_const

-- @@ L178-179 verbatim
lemma isOpen_hpGt (t h : ℝ) : IsOpen (hpGt t h) := by
  unfold hpGt; exact isOpen_lt continuous_const (continuous_inner_u t)

-- @@ L180-181 verbatim
lemma isClosed_line (t h : ℝ) : IsClosed (line t h) := by
  unfold line; exact isClosed_eq (continuous_inner_u t) continuous_const


-- @@ L183-185 expanded
lemma isLinearMap_inner_u (t : ℝ) : IsLinearMap ℝ fun p : EuclideanSpace ℝ (Fin 2) => ⟪p, u t⟫ :=
  ⟨fun x y => inner_add_left x y (u t), fun c x => by simp only [real_inner_smul_left, smul_eq_mul]⟩


-- @@ L187-188 verbatim
lemma convex_hpLe (t h : ℝ) : Convex ℝ (hpLe t h) := by
  unfold hpLe; exact convex_halfSpace_le (isLinearMap_inner_u t) h

-- @@ L189-190 verbatim
lemma convex_hpGe (t h : ℝ) : Convex ℝ (hpGe t h) := by
  unfold hpGe; exact convex_halfSpace_ge (isLinearMap_inner_u t) h

-- @@ L191-192 verbatim
lemma convex_hpLt (t h : ℝ) : Convex ℝ (hpLt t h) := by
  unfold hpLt; exact convex_halfSpace_lt (isLinearMap_inner_u t) h


-- @@ L194-196 verbatim
/-- The complement of `hpLe` is `hpGt`. -/
lemma compl_hpLe (t h : ℝ) : (hpLe t h)ᶜ = hpGt t h := by
  ext p; simp [hpLe, hpGt]


-- @@ L198-198 verbatim
/-! ## Rotation (Def 2.3.1) -/


-- @@ L200-202 expanded
/-- Counterclockwise rotation by `t` about the origin, in coordinates. -/
def rot (t : ℝ) (p : EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 2) :=
  !₂[cos t * p 0 - sin t * p 1, sin t * p 0 + cos t * p 1]


-- @@ L204-204 expanded
@[simp]
lemma rot_coord_zero (t : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    rot t p 0 = cos t * p 0 - sin t * p 1 :=
  rfl


-- @@ L205-205 expanded
@[simp]
lemma rot_coord_one (t : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    rot t p 1 = sin t * p 0 + cos t * p 1 :=
  rfl


-- @@ L207-208 expanded
lemma rot_zero (p : EuclideanSpace ℝ (Fin 2)) : rot 0 p = p := by ext i; fin_cases i <;> simp


-- @@ L210-211 expanded
lemma rot_add (t : ℝ) (p q : EuclideanSpace ℝ (Fin 2)) : rot t (p + q) = rot t p + rot t q := by
  ext i; fin_cases i <;> simp <;> ring


-- @@ L213-214 expanded
lemma rot_smul (t c : ℝ) (p : EuclideanSpace ℝ (Fin 2)) : rot t (c • p) = c • rot t p := by ext i;
  fin_cases i <;> simp <;> ring


-- @@ L216-218 verbatim
lemma rot_u (t s : ℝ) : rot t (u s) = u (t + s) := by
  ext i
  fin_cases i <;> simp [cos_add, sin_add]


-- @@ L220-223 expanded
/-- Rotations preserve the inner product. -/
lemma inner_rot_rot (t : ℝ) (p q : EuclideanSpace ℝ (Fin 2)) : ⟪rot t p, rot t q⟫ = ⟪p, q⟫ :=
  by
  rw [inner_eq, inner_eq]
  simp; linear_combination (p 0 * q 0 + p 1 * q 1) * cos_sq_add_sin_sq t


-- @@ L225-228 expanded
/-- `⟪R_t p, u_s⟫ = ⟪p, u_{s-t}⟫`. -/
lemma inner_rot_u (t s : ℝ) (p : EuclideanSpace ℝ (Fin 2)) : ⟪rot t p, u s⟫ = ⟪p, u (s - t)⟫ :=
  by
  rw [inner_eq, inner_eq]
  simp [cos_sub, sin_sub]; ring


-- @@ L230-232 expanded
lemma rot_rot (t s : ℝ) (p : EuclideanSpace ℝ (Fin 2)) : rot t (rot s p) = rot (t + s) p :=
  by
  ext i
  fin_cases i <;> (simp [cos_add, sin_add]; ring)


-- @@ L234-235 expanded
lemma rot_neg_rot (t : ℝ) (p : EuclideanSpace ℝ (Fin 2)) : rot (-t) (rot t p) = p := by
  rw [rot_rot, neg_add_cancel, rot_zero]


-- @@ L237-240 verbatim
lemma rot_injective (t : ℝ) : Function.Injective (rot t) := by
  intro p q h
  have := congrArg (rot (-t)) h
  rwa [rot_neg_rot, rot_neg_rot] at this


-- @@ L242-242 verbatim
/-! ### Bridge to the upstream (Mathlib) rotation used in `MovingSofa.rotateTranslate` -/


-- @@ L244-252 expanded
/-- The area form of the standard orientation of `ℝ²`, in coordinates. -/
lemma areaForm_eq (x y : EuclideanSpace ℝ (Fin 2)) :
    (EuclideanGeometry.o : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2)).areaForm x y =
      x 0 * y 1 - x 1 * y 0 :=
  by
  rw [Orientation.areaForm_to_volumeForm,
    Orientation.volumeForm_robust
      (EuclideanGeometry.o : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2))
      (EuclideanSpace.basisFun (Fin 2) ℝ) rfl,
    Module.Basis.det_apply, Matrix.det_fin_two]
  simp [Module.Basis.toMatrix_apply]
  ring


-- @@ L254-269 expanded
/-- The right-angle rotation `J` of the standard orientation is `(x, y) ↦ (-y, x)`. -/
lemma rightAngleRotation_eq (x : EuclideanSpace ℝ (Fin 2)) :
    (EuclideanGeometry.o : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2)).rightAngleRotation x =
      !₂[-x 1, x 0] :=
  by
  have h0 :
    ((EuclideanGeometry.o : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2)).rightAngleRotation x)
        0 =
      -x 1 :=
    by
    have h :=
      (EuclideanGeometry.o :
            Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2)).inner_rightAngleRotation_left
        x (u 0)
    rw [areaForm_eq, inner_u_zero] at h
    simpa using h
  have h1 :
    ((EuclideanGeometry.o : Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2)).rightAngleRotation x)
        1 =
      x 0 :=
    by
    have h :=
      (EuclideanGeometry.o :
            Orientation ℝ (EuclideanSpace ℝ (Fin 2)) (Fin 2)).inner_rightAngleRotation_left
        x (u (π / 2))
    rw [areaForm_eq, inner_u_pi_div_two] at h
    simpa using h
  ext i; fin_cases i
  · simpa using h0
  · simpa using h1


-- @@ L271-276 expanded
/-- **Bridge**: our coordinate rotation is Mathlib's `Orientation.rotation` for the standard
orientation (the one used by upstream `MovingSofa.rotateTranslate`). -/
theorem rot_eq_rotation (t : ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    rot t p = EuclideanGeometry.o.rotation (t : Real.Angle) p :=
  by
  rw [Orientation.rotation_apply, Real.Angle.cos_coe, Real.Angle.sin_coe, rightAngleRotation_eq]
  ext i; fin_cases i <;> simp <;> ring


-- @@ L278-278 verbatim
/-! ## Strips, parallelogram, fan, hallway (Def 2.3.2, 2.3.5, §2.4, Def 2.2.1) -/


-- @@ L280-281 expanded
/-- The horizontal strip `H = ℝ × [0,1]`. -/
def Hstrip : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | 0 ≤ p 1 ∧ p 1 ≤ 1}


-- @@ L283-284 expanded
/-- `V_ω = R_ω([0,1] × ℝ) = {p : 0 ≤ ⟪p, u_ω⟫ ≤ 1}`. -/
def Vstrip (ω : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | 0 ≤ ⟪p, u ω⟫ ∧ ⟪p, u ω⟫ ≤ 1}


-- @@ L286-287 expanded
/-- The parallelogram `P_ω = H ∩ V_ω`. -/
def para (ω : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  Hstrip ∩ Vstrip ω


-- @@ L289-290 expanded
/-- The fan `F_ω = {y ≥ 0, x cos ω + y sin ω ≥ 0}`. -/
def fan (ω : ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | 0 ≤ p 1 ∧ 0 ≤ ⟪p, u ω⟫}


-- @@ L292-293 verbatim
lemma Vstrip_pi_div_two : Vstrip (π / 2) = Hstrip := by
  ext p; simp [Vstrip, Hstrip, inner_u_pi_div_two]


-- @@ L295-296 verbatim
lemma Vstrip_zero : Vstrip 0 = {p | 0 ≤ p 0 ∧ p 0 ≤ 1} := by
  ext p; simp [Vstrip, inner_u_zero]


-- @@ L298-301 verbatim
lemma Hstrip_eq_hpLe_inter : Hstrip = hpLe (π / 2) 1 ∩ hpGe (π / 2) 0 := by
  ext p
  simp only [Hstrip, hpLe, hpGe, Set.mem_inter_iff, Set.mem_ofPred_eq, inner_u_pi_div_two]
  exact and_comm


-- @@ L303-304 verbatim
lemma isClosed_Hstrip : IsClosed Hstrip := by
  rw [Hstrip_eq_hpLe_inter]; exact (isClosed_hpLe _ _).inter (isClosed_hpGe _ _)


-- @@ L306-307 verbatim
lemma convex_Hstrip : Convex ℝ Hstrip := by
  rw [Hstrip_eq_hpLe_inter]; exact (convex_hpLe _ _).inter (convex_hpGe _ _)


-- @@ L309-312 verbatim
lemma Vstrip_eq (ω : ℝ) : Vstrip ω = hpLe ω 1 ∩ hpGe ω 0 := by
  ext p
  simp only [Vstrip, hpLe, hpGe, Set.mem_inter_iff, Set.mem_ofPred_eq]
  exact and_comm


-- @@ L314-315 verbatim
lemma isClosed_Vstrip (ω : ℝ) : IsClosed (Vstrip ω) := by
  rw [Vstrip_eq]; exact (isClosed_hpLe _ _).inter (isClosed_hpGe _ _)


-- @@ L317-318 verbatim
lemma convex_Vstrip (ω : ℝ) : Convex ℝ (Vstrip ω) := by
  rw [Vstrip_eq]; exact (convex_hpLe _ _).inter (convex_hpGe _ _)


-- @@ L320-321 expanded
/-- Outer quarter-plane `Q_L⁺ = (-∞,1]²` of the hallway. -/
def Qplus : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | p 0 ≤ 1 ∧ p 1 ≤ 1}


-- @@ L322-323 expanded
/-- Inner open quarter-plane `Q_L⁻ = (-∞,0)²` of the hallway. -/
def Qminus : Set (EuclideanSpace ℝ (Fin 2)) :=
  {p | p 0 < 0 ∧ p 1 < 0}


-- @@ L324-325 expanded
/-- Inner corner `x_L = (0,0)` and outer corner `y_L = (1,1)`. -/
def xL : EuclideanSpace ℝ (Fin 2) :=
  !₂[0, 0]


-- @@ L326-326 expanded
def yL : EuclideanSpace ℝ (Fin 2) :=
  !₂[1, 1]


-- @@ L328-344 verbatim
/-- **Baek Def 1.1.1 / Def 2.2.1**: the upstream hallway equals `Q⁺ \ Q⁻`. -/
theorem hallway_eq_diff : MovingSofa.hallway = Qplus \ Qminus := by
  ext p
  unfold MovingSofa.hallway
  rw [Set.mem_union, MovingSofa.mem_horizontalHallway_iff, MovingSofa.mem_verticalHallway_iff,
    Set.mem_sdiff]
  show _ ↔ (p 0 ≤ 1 ∧ p 1 ≤ 1) ∧ ¬ (p 0 < 0 ∧ p 1 < 0)
  constructor
  · rintro (⟨h0, hp, h1⟩ | ⟨hp0, h0, h1⟩)
    · exact ⟨⟨h0, h1⟩, fun h => absurd hp (not_le.mpr h.2)⟩
    · exact ⟨⟨h0, h1⟩, fun h => absurd hp0 (not_le.mpr h.1)⟩
  · rintro ⟨⟨h0, h1⟩, h⟩
    by_cases hp : 0 ≤ p 1
    · exact Or.inl ⟨h0, hp, h1⟩
    · refine Or.inr ⟨?_, h0, h1⟩
      by_contra h0'
      exact h ⟨not_le.mp h0', not_le.mp hp⟩


-- @@ L346-347 verbatim
lemma Qplus_eq : Qplus = hpLe 0 1 ∩ hpLe (π / 2) 1 := by
  ext p; simp [Qplus, hpLe, inner_u_zero, inner_u_pi_div_two]


-- @@ L349-350 verbatim
lemma Qminus_eq : Qminus = hpLt 0 0 ∩ hpLt (π / 2) 0 := by
  ext p; simp [Qminus, hpLt, inner_u_zero, inner_u_pi_div_two]


-- @@ L352-353 verbatim
lemma isClosed_Qplus : IsClosed Qplus := by
  rw [Qplus_eq]; exact (isClosed_hpLe _ _).inter (isClosed_hpLe _ _)


-- @@ L355-356 verbatim
lemma isOpen_Qminus : IsOpen Qminus := by
  rw [Qminus_eq]; exact (isOpen_hpLt _ _).inter (isOpen_hpLt _ _)


-- @@ L358-359 verbatim
lemma isClosed_hallway : IsClosed MovingSofa.hallway := by
  rw [hallway_eq_diff, Set.sdiff_eq]; exact isClosed_Qplus.inter isOpen_Qminus.isClosed_compl


-- @@ L361-361 verbatim
end Sofa
