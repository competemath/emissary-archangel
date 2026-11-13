import Mathlib


-- @@ L3-28 verbatim
/-!
# Framed level sets: the oriented unit kernel field

For a smooth map `g : ℝ^{n+1} → ℝⁿ` we study the open set `W` of points where
`fderiv ℝ g` is surjective, and construct on `W` the *oriented unit kernel field*
`tauField g : E → E`:

* `crossDet v w` is the determinant of the `(n+1) × (n+1)` matrix whose first row is
  `w` and whose remaining rows are the family `v : Fin n → E` (all in coordinates);
* `crossVec v` is the generalized cross product of the family `v`, characterized by
  `⟪crossVec v, w⟫ = crossDet v w`;
* `gradVec g i x` is the gradient of the `i`-th component of `g` at `x`;
* `kerCross g x = crossVec (fun i => gradVec g i x)` and
  `tauField g x` is its normalization.

Main statements (for `x` with `Function.Surjective (fderiv ℝ g x)` and `g` smooth):

* `Submission.isOpen_regularSet` : `W` is open;
* `Submission.tauField_mem_ker`, `Submission.norm_tauField`,
  `Submission.crossDet_grad_tauField_pos` (orientation),
  `Submission.fderiv_eq_zero_iff_mem_span_tauField` (the kernel is the line `ℝ ∙ τ`),
  `Submission.contDiffOn_tauField` (smoothness of `τ` on `W`).

Everything is stated for `E := EuclideanSpace ℝ (Fin (n+1))`,
`F := EuclideanSpace ℝ (Fin n)`.
-/


-- @@ L30-30 verbatim
noncomputable section


-- @@ L32-32 verbatim
namespace Submission


-- @@ L34-34 verbatim
open Set Function Metric Module Submodule

-- @@ L35-35 verbatim
open scoped RealInnerProductSpace ContDiff Topology


-- @@ L37-37 verbatim
variable {n : ℕ}


-- @@ L39-39 verbatim
local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

-- @@ L40-40 verbatim
local notation "F" => EuclideanSpace ℝ (Fin n)


-- @@ L42-42 verbatim
/-! ## The generalized cross product -/


-- @@ L44-47 verbatim
/-- The `(n+1) × (n+1)` matrix whose row `0` is `w` and whose row `i.succ` is `v i`
(in coordinates). -/
def crossRows (v : Fin n → E) (w : E) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of (Fin.cons (WithLp.ofLp w) fun i => WithLp.ofLp (v i))


-- @@ L49-51 verbatim
/-- Determinant of the matrix with first row `w` and remaining rows `v`. -/
def crossDet (v : Fin n → E) (w : E) : ℝ :=
  (crossRows v w).det


-- @@ L53-59 verbatim
lemma updateRow_crossRows (v : Fin n → E) (w w' : E) :
    (crossRows v w).updateRow 0 (WithLp.ofLp w') = crossRows v w' := by
  unfold crossRows
  ext i j
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩
  · simp
  · simp


-- @@ L61-66 verbatim
lemma crossDet_add (v : Fin n → E) (w w' : E) :
    crossDet v (w + w') = crossDet v w + crossDet v w' := by
  have h := Matrix.det_updateRow_add (crossRows v w) 0
    (WithLp.ofLp w) (WithLp.ofLp w')
  rw [show WithLp.ofLp w + WithLp.ofLp w' = WithLp.ofLp (w + w') from rfl] at h
  simpa only [crossDet, updateRow_crossRows] using h


-- @@ L68-72 verbatim
lemma crossDet_smul (v : Fin n → E) (c : ℝ) (w : E) :
    crossDet v (c • w) = c * crossDet v w := by
  have h := Matrix.det_updateRow_smul (crossRows v w) 0 c (WithLp.ofLp w)
  rw [show c • WithLp.ofLp w = WithLp.ofLp (c • w) from rfl] at h
  simpa only [crossDet, updateRow_crossRows] using h


-- @@ L74-78 verbatim
/-- `crossDet v` as a linear map. -/
def crossLM (v : Fin n → E) : E →ₗ[ℝ] ℝ where
  toFun := crossDet v
  map_add' := crossDet_add v
  map_smul' := crossDet_smul v


-- @@ L80-80 verbatim
@[simp] lemma crossLM_apply (v : Fin n → E) (w : E) : crossLM v w = crossDet v w := rfl


-- @@ L82-89 verbatim
/-- The determinant vanishes when the first row equals one of the other rows. -/
lemma crossDet_apply_self (v : Fin n → E) (i : Fin n) :
    crossDet v (v i) = 0 := by
  apply Matrix.det_zero_of_row_eq (i := (0 : Fin (n + 1))) (j := i.succ)
  · exact (Fin.succ_ne_zero i).symm
  · show crossRows v (v i) 0 = crossRows v (v i) i.succ
    funext j
    simp [crossRows]


-- @@ L91-94 verbatim
/-- The generalized cross product of `n` vectors in `ℝ^{n+1}`: the unique vector with
`⟪crossVec v, w⟫ = crossDet v w` for all `w`. Defined coordinatewise via cofactors. -/
def crossVec (v : Fin n → E) : E :=
  WithLp.toLp 2 fun j => crossDet v (EuclideanSpace.single j 1)


-- @@ L96-97 verbatim
@[simp] lemma crossVec_apply (v : Fin n → E) (j : Fin (n + 1)) :
    crossVec v j = crossDet v (EuclideanSpace.single j 1) := rfl


-- @@ L99-110 verbatim
/-- Fundamental property of the cross product. -/
lemma inner_crossVec (v : Fin n → E) (w : E) :
    ⟪crossVec v, w⟫ = crossDet v w := by
  have hw : w = ∑ j, w j • EuclideanSpace.single j (1 : ℝ) := by
    have h := (EuclideanSpace.basisFun (Fin (n + 1)) ℝ).sum_repr w
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using h.symm
  calc ⟪crossVec v, w⟫ = ∑ j, w j * crossDet v (EuclideanSpace.single j 1) := by
        simp [PiLp.inner_apply, RCLike.inner_apply]
    _ = crossLM v (∑ j, w j • EuclideanSpace.single j (1 : ℝ)) := by
        rw [map_sum]
        simp
    _ = crossDet v w := by rw [← hw]; rfl


-- @@ L112-114 verbatim
lemma crossVec_inner (v : Fin n → E) (w : E) :
    ⟪w, crossVec v⟫ = crossDet v w := by
  rw [real_inner_comm, inner_crossVec]


-- @@ L116-119 verbatim
/-- The cross product is orthogonal to each of the input vectors. -/
lemma inner_crossVec_self (v : Fin n → E) (i : Fin n) :
    ⟪crossVec v, v i⟫ = 0 := by
  rw [inner_crossVec, crossDet_apply_self]


-- @@ L121-124 verbatim
/-- Orientation: pairing the cross product with itself gives the norm squared. -/
lemma crossDet_crossVec (v : Fin n → E) :
    crossDet v (crossVec v) = ‖crossVec v‖ ^ 2 := by
  rw [← inner_crossVec, real_inner_self_eq_norm_sq]


-- @@ L126-126 verbatim
/-! ## Nonvanishing of the cross product -/


-- @@ L128-131 verbatim
lemma row_crossRows (v : Fin n → E) (w : E) :
    (crossRows v w).row = fun i => WithLp.ofLp ((Fin.cons w v : Fin (n + 1) → E) i) := by
  funext i j
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨k, rfl⟩ <;> simp [crossRows, Matrix.row]


-- @@ L133-138 verbatim
lemma linearIndependent_rows_iff (v : Fin n → E) (w : E) :
    LinearIndependent ℝ (crossRows v w).row ↔
      LinearIndependent ℝ (Fin.cons w v : Fin (n + 1) → E) := by
  rw [row_crossRows]
  exact (WithLp.linearEquiv 2 ℝ (Fin (n + 1) → ℝ)).toLinearMap.linearIndependent_iff
    (LinearEquiv.ker _) (v := (Fin.cons w v : Fin (n + 1) → E))


-- @@ L140-144 verbatim
lemma crossDet_ne_zero_iff (v : Fin n → E) (w : E) :
    crossDet v w ≠ 0 ↔ LinearIndependent ℝ (Fin.cons w v : Fin (n + 1) → E) := by
  rw [← linearIndependent_rows_iff, Matrix.linearIndependent_rows_iff_isUnit,
    Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  rfl


-- @@ L146-157 verbatim
lemma crossVec_eq_zero_of_not_linearIndependent {v : Fin n → E}
    (hv : ¬ LinearIndependent ℝ v) : crossVec v = 0 := by
  have h0 : ∀ w : E, crossDet v w = 0 := by
    intro w
    by_contra h
    have hcomp := ((crossDet_ne_zero_iff v w).mp h).comp Fin.succ (Fin.succ_injective n)
    rw [show (Fin.cons w v : Fin (n + 1) → E) ∘ Fin.succ = v from
      funext fun i => by simp] at hcomp
    exact hv hcomp
  apply (WithLp.equiv 2 _).injective
  funext j
  simpa using h0 (EuclideanSpace.single j 1)


-- @@ L159-175 verbatim
lemma crossVec_ne_zero_of_linearIndependent {v : Fin n → E}
    (hv : LinearIndependent ℝ v) : crossVec v ≠ 0 := by
  -- the span of `n` vectors is a proper subspace of `ℝ^{n+1}`; pick `w` outside it
  have hlt : finrank ℝ (span ℝ (range v)) < finrank ℝ E := by
    have h1 : finrank ℝ (span ℝ (range v)) ≤ n := by
      simpa [Set.finrank] using finrank_range_le_card v
    have h2 : finrank ℝ E = n + 1 := finrank_euclideanSpace_fin
    omega
  obtain ⟨w, hw⟩ := (span ℝ (range v)).exists_of_finrank_lt hlt
  have hwmem : w ∉ span ℝ (range v) := by
    simpa using hw 1 one_ne_zero
  have hcons : LinearIndependent ℝ (Fin.cons w v : Fin (n + 1) → E) :=
    hv.finCons hwmem
  have hdet : crossDet v w ≠ 0 := (crossDet_ne_zero_iff v w).mpr hcons
  intro hzero
  apply hdet
  rw [← inner_crossVec, hzero, inner_zero_left]


-- @@ L177-183 verbatim
lemma crossVec_ne_zero_iff (v : Fin n → E) :
    crossVec v ≠ 0 ↔ LinearIndependent ℝ v := by
  constructor
  · intro h
    by_contra hv
    exact h (crossVec_eq_zero_of_not_linearIndependent hv)
  · exact crossVec_ne_zero_of_linearIndependent


-- @@ L185-185 verbatim
/-! ## Gradients of the components -/


-- @@ L187-191 verbatim
/-- The gradient of the `i`-th component of `g` at `x`, i.e. the vector representing
the linear functional `w ↦ (fderiv ℝ g x w) i`. -/
def gradVec (g : E → F) (i : Fin n) (x : E) : E :=
  (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin (n + 1)))).symm
    ((EuclideanSpace.proj i).comp (fderiv ℝ g x))


-- @@ L193-195 verbatim
lemma inner_gradVec (g : E → F) (i : Fin n) (x : E) (w : E) :
    ⟪gradVec g i x, w⟫ = fderiv ℝ g x w i :=
  InnerProductSpace.toDual_symm_apply


-- @@ L197-204 verbatim
/-- Pairing a coefficient vector with `fderiv g` corresponds to pairing the
associated combination of gradients. -/
lemma inner_sum_gradVec (g : E → F) (x : E) (c : F) (w : E) :
    ⟪∑ i, c i • gradVec g i x, w⟫ = ⟪c, fderiv ℝ g x w⟫ := by
  rw [sum_inner]
  simp only [real_inner_smul_left, inner_gradVec]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _


-- @@ L206-250 verbatim
/-- Surjectivity of the derivative is equivalent to linear independence of the
component gradients. -/
lemma surjective_fderiv_iff_linearIndependent (g : E → F) (x : E) :
    Surjective (fderiv ℝ g x) ↔ LinearIndependent ℝ (fun i => gradVec g i x) := by
  constructor
  · intro hsurj
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    set c' : F := WithLp.toLp 2 c with hc'
    have hzero : ∀ y : F, ⟪c', y⟫ = 0 := by
      intro y
      obtain ⟨w, rfl⟩ := hsurj y
      rw [← inner_sum_gradVec]
      have : (∑ j, c' j • gradVec g j x) = 0 := hc
      rw [this, inner_zero_left]
    have : c' = 0 := by
      have := hzero c'
      rwa [inner_self_eq_zero] at this
    have : c' i = 0 := by rw [this]; rfl
    exact this
  · intro hind
    -- if the range were proper, a nonzero orthogonal covector would contradict independence
    by_contra hsurj
    have hrange : LinearMap.range ((fderiv ℝ g x) : E →ₗ[ℝ] F) ≠ ⊤ := by
      intro h
      exact hsurj (LinearMap.range_eq_top.mp h)
    have hbot : (LinearMap.range ((fderiv ℝ g x) : E →ₗ[ℝ] F))ᗮ ≠ ⊥ := by
      intro h
      exact hrange (Submodule.orthogonal_eq_bot_iff.mp h)
    obtain ⟨c', hc'mem, hc'ne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have hzero : ∀ w : E, ⟪c', fderiv ℝ g x w⟫ = 0 := fun w => by
      rw [Submodule.mem_orthogonal'] at hc'mem
      exact hc'mem (fderiv ℝ g x w) (LinearMap.mem_range_self _ w)
    have hsum : (∑ i, c' i • gradVec g i x) = 0 := by
      have h := hzero
      have : ⟪∑ i, c' i • gradVec g i x, ∑ i, c' i • gradVec g i x⟫ = 0 := by
        rw [inner_sum_gradVec, hzero]
      rwa [inner_self_eq_zero] at this
    have hall : ∀ i, c' i = 0 := by
      rw [Fintype.linearIndependent_iff] at hind
      exact hind (fun i => c' i) hsum
    apply hc'ne
    apply (WithLp.equiv 2 _).injective
    funext i
    exact hall i


-- @@ L252-252 verbatim
/-! ## Smoothness -/


-- @@ L254-282 verbatim
/-- The cross product of a smooth family of vectors is smooth (it is polynomial in
the coordinates of the family). -/
lemma contDiff_crossVec_comp {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {v : X → Fin n → E} (hv : ∀ i, ContDiff ℝ ∞ fun x => v x i) :
    ContDiff ℝ ∞ fun x => crossVec (v x) := by
  have : (fun x => crossVec (v x)) = fun x =>
      (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm
        (fun j => crossDet (v x) (EuclideanSpace.single j 1)) := rfl
  rw [this]
  apply (EuclideanSpace.equiv (Fin (n + 1)) ℝ).symm.contDiff.comp
  rw [contDiff_pi]
  intro j
  -- each coordinate is a polynomial in the entries
  simp only [crossDet, Matrix.det_apply']
  apply ContDiff.sum
  intro σ _
  apply ContDiff.mul contDiff_const
  apply contDiff_prod
  intro i _
  show ContDiff ℝ ∞ fun x => crossRows (v x) (EuclideanSpace.single j 1) (σ i) i
  have hentry : ∀ (m : Fin (n + 1)), ContDiff ℝ ∞
      fun x => crossRows (v x) (EuclideanSpace.single j 1) m i := by
    intro m
    rcases Fin.eq_zero_or_eq_succ m with rfl | ⟨k, rfl⟩
    · simp only [crossRows, Matrix.of_apply, Fin.cons_zero]
      exact contDiff_const
    · simp only [crossRows, Matrix.of_apply, Fin.cons_succ]
      exact (EuclideanSpace.proj i).contDiff.comp (hv k)
  exact hentry (σ i)


-- @@ L284-293 verbatim
/-- Gradients of a smooth map are smooth. -/
lemma contDiff_gradVec (g : E → F) (hg : ContDiff ℝ ∞ g) (i : Fin n) :
    ContDiff ℝ ∞ (gradVec g i) := by
  apply (InnerProductSpace.toDual ℝ
    (EuclideanSpace ℝ (Fin (n + 1)))).symm.contDiff.comp
  have : (fun x => (EuclideanSpace.proj i).comp (fderiv ℝ g x)) =
      fun x => (ContinuousLinearMap.compL ℝ (EuclideanSpace ℝ (Fin (n + 1)))
        (EuclideanSpace ℝ (Fin n)) ℝ (EuclideanSpace.proj i)) (fderiv ℝ g x) := rfl
  rw [this]
  exact (ContinuousLinearMap.contDiff _).comp (hg.fderiv_right (by simp))


-- @@ L295-295 verbatim
/-! ## The kernel field -/


-- @@ L297-299 verbatim
/-- The (unnormalized) kernel vector field: the cross product of the gradients. -/
def kerCross (g : E → F) (x : E) : E :=
  crossVec fun i => gradVec g i x


-- @@ L301-303 verbatim
/-- The oriented unit kernel field. Away from the regular set it takes junk values. -/
def tauField (g : E → F) (x : E) : E :=
  ‖kerCross g x‖⁻¹ • kerCross g x


-- @@ L305-307 verbatim
/-- The set of points where the derivative of `g` is surjective. -/
def regularSet (g : E → F) : Set E :=
  {x | Surjective (fderiv ℝ g x)}


-- @@ L309-311 verbatim
lemma contDiff_kerCross {g : E → F} (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (kerCross g) :=
  contDiff_crossVec_comp fun i => contDiff_gradVec g hg i


-- @@ L313-316 verbatim
lemma kerCross_ne_zero_iff (g : E → F) (x : E) :
    kerCross g x ≠ 0 ↔ x ∈ regularSet g := by
  rw [kerCross, crossVec_ne_zero_iff]
  exact (surjective_fderiv_iff_linearIndependent g x).symm


-- @@ L318-325 verbatim
lemma isOpen_regularSet {g : E → F} (hg : ContDiff ℝ ∞ g) :
    IsOpen (regularSet g) := by
  have : regularSet g = kerCross g ⁻¹' ({0}ᶜ) := by
    ext x
    simp only [mem_preimage, mem_compl_iff, mem_singleton_iff]
    exact (kerCross_ne_zero_iff g x).symm
  rw [this]
  exact (contDiff_kerCross hg).continuous.isOpen_preimage _ isOpen_compl_singleton


-- @@ L327-331 verbatim
lemma norm_tauField {g : E → F} {x : E} (hx : x ∈ regularSet g) :
    ‖tauField g x‖ = 1 := by
  have h : kerCross g x ≠ 0 := (kerCross_ne_zero_iff g x).mpr hx
  rw [tauField, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]


-- @@ L333-338 verbatim
lemma tauField_ne_zero {g : E → F} {x : E} (hx : x ∈ regularSet g) :
    tauField g x ≠ 0 := by
  intro h
  have := norm_tauField hx
  rw [h, norm_zero] at this
  norm_num at this


-- @@ L340-349 verbatim
/-- The kernel field lies in the kernel of the derivative. -/
lemma fderiv_kerCross_eq_zero (g : E → F) (x : E) :
    fderiv ℝ g x (kerCross g x) = 0 := by
  apply (WithLp.equiv 2 _).injective
  funext i
  have h : ⟪kerCross g x, gradVec g i x⟫ = 0 :=
    inner_crossVec_self (fun j => gradVec g j x) i
  rw [real_inner_comm] at h
  rw [inner_gradVec] at h
  exact h


-- @@ L351-353 verbatim
lemma fderiv_tauField_eq_zero (g : E → F) (x : E) :
    fderiv ℝ g x (tauField g x) = 0 := by
  rw [tauField, map_smul, fderiv_kerCross_eq_zero, smul_zero]


-- @@ L355-365 verbatim
/-- Orientation: the determinant of the matrix with first row `τ` and remaining rows
the gradients is positive. -/
lemma crossDet_tauField_pos {g : E → F} {x : E} (hx : x ∈ regularSet g) :
    0 < crossDet (fun i => gradVec g i x) (tauField g x) := by
  have h : kerCross g x ≠ 0 := (kerCross_ne_zero_iff g x).mpr hx
  rw [tauField, crossDet_smul]
  have h2 : crossDet (fun i => gradVec g i x) (kerCross g x) = ‖kerCross g x‖ ^ 2 :=
    crossDet_crossVec _
  rw [h2]
  have hpos : (0 : ℝ) < ‖kerCross g x‖ := norm_pos_iff.mpr h
  exact mul_pos (inv_pos.mpr hpos) (pow_pos hpos 2)


-- @@ L367-395 verbatim
/-- The kernel of the derivative at a regular point is exactly the line spanned by
the unit kernel field. -/
lemma fderiv_eq_zero_iff_mem_span_tauField {g : E → F} {x : E} (hx : x ∈ regularSet g)
    (w : E) :
    fderiv ℝ g x w = 0 ↔ w ∈ Submodule.span ℝ {tauField g x} := by
  have hker : LinearMap.ker ((fderiv ℝ g x) : E →ₗ[ℝ] F)
      = Submodule.span ℝ {tauField g x} := by
    have hle : Submodule.span ℝ {tauField g x} ≤
        LinearMap.ker ((fderiv ℝ g x) : E →ₗ[ℝ] F) := by
      rw [Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
      exact fderiv_tauField_eq_zero g x
    apply (Submodule.eq_of_le_of_finrank_le hle ?_).symm
    -- rank-nullity: the kernel is 1-dimensional
    have hrn := LinearMap.finrank_range_add_finrank_ker ((fderiv ℝ g x) : E →ₗ[ℝ] F)
    have hrange : LinearMap.range ((fderiv ℝ g x) : E →ₗ[ℝ] F) = ⊤ :=
      LinearMap.range_eq_top.mpr hx
    rw [hrange, finrank_top] at hrn
    have hF : finrank ℝ F = n := finrank_euclideanSpace_fin
    have hE : finrank ℝ E = n + 1 := finrank_euclideanSpace_fin
    have hker1 : finrank ℝ (LinearMap.ker ((fderiv ℝ g x) : E →ₗ[ℝ] F)) = 1 := by
      omega
    rw [hker1, finrank_span_singleton (tauField_ne_zero hx)]
  constructor
  · intro h
    rw [← hker]
    exact LinearMap.mem_ker.mpr h
  · intro h
    rw [← hker] at h
    exact LinearMap.mem_ker.mp h


-- @@ L397-408 verbatim
/-- The unit kernel field is smooth on the regular set. -/
lemma contDiffOn_tauField {g : E → F} (hg : ContDiff ℝ ∞ g) :
    ContDiffOn ℝ ∞ (tauField g) (regularSet g) := by
  intro x hx
  apply ContDiffWithinAt.mono_of_mem_nhdsWithin
    (s := regularSet g) ?_ (self_mem_nhdsWithin)
  have h : kerCross g x ≠ 0 := (kerCross_ne_zero_iff g x).mpr hx
  have hker : ContDiffAt ℝ ∞ (kerCross g) x := (contDiff_kerCross hg).contDiffAt
  have hnorm : ContDiffAt ℝ ∞ (fun y => ‖kerCross g y‖) x := hker.norm ℝ h
  have hinv : ContDiffAt ℝ ∞ (fun y => ‖kerCross g y‖⁻¹) x := hnorm.inv
    (norm_ne_zero_iff.mpr h)
  exact (hinv.smul hker).contDiffWithinAt


-- @@ L410-410 verbatim
/-! ## Framed level sets -/


-- @@ L412-422 verbatim
/-- A framed level set presentation: a smooth map `g : ℝ^{n+1} → ℝⁿ` with bounded
zero fiber, `0` being a regular value. -/
structure FramedLevelSet (n : ℕ) where
  /-- The defining map. -/
  g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n)
  /-- Smoothness. -/
  smooth : ContDiff ℝ ∞ g
  /-- The zero fiber is bounded. -/
  fiber_bounded : Bornology.IsBounded {v | g v = 0}
  /-- `0` is a regular value. -/
  regular : ∀ v, g v = 0 → Function.Surjective (fderiv ℝ g v)


-- @@ L424-424 verbatim
namespace FramedLevelSet


-- @@ L426-426 verbatim
variable (X : FramedLevelSet n)


-- @@ L428-429 verbatim
/-- The zero fiber of the presentation. -/
def fiber : Set (EuclideanSpace ℝ (Fin (n + 1))) := {v | X.g v = 0}


-- @@ L431-432 verbatim
lemma isClosed_fiber : IsClosed X.fiber :=
  isClosed_singleton.preimage X.smooth.continuous


-- @@ L434-435 verbatim
lemma isCompact_fiber : IsCompact X.fiber :=
  Metric.isCompact_of_isClosed_isBounded X.isClosed_fiber X.fiber_bounded


-- @@ L437-438 verbatim
lemma fiber_subset_regularSet : X.fiber ⊆ regularSet X.g :=
  fun v hv => X.regular v hv


-- @@ L440-440 verbatim
end FramedLevelSet


-- @@ L442-442 verbatim
end Submission
