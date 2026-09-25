import SphereEversion.Notations
import SphereEversion.ToMathlib.Equivariant
import SphereEversion.ToMathlib.MeasureTheory.ParametricIntervalIntegral


-- @@ L5-7 verbatim
/-!
# Basic definitions and properties of loops
-/


-- @@ L9-9 verbatim
open Set Function FiniteDimensional Int TopologicalSpace


-- @@ L11-11 verbatim
open scoped Topology unitInterval


-- @@ L13-13 verbatim
noncomputable section


-- @@ L15-17 verbatim
variable {K X X' Y Z : Type*}

-- variable [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Z]

-- @@ L18-19 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']


-- @@ L21-21 verbatim
/-! ## Definition and periodicity lemmas -/



-- @@ L24-24 verbatim
variable (X)


-- @@ L26-29 verbatim
/-- A loop is a function with domain `ℝ` and is periodic with period 1. -/
structure Loop where
  toFun : ℝ → X
  per' : ∀ t, toFun (t + 1) = toFun t


-- @@ L31-31 verbatim
attribute [coe] Loop.toFun


-- @@ L33-34 verbatim
instance : CoeFun (Loop X) fun _ ↦ ℝ → X :=
  ⟨fun γ ↦ γ.toFun⟩


-- @@ L36-36 verbatim
initialize_simps_projections Loop (toFun → apply)


-- @@ L38-40 verbatim
/-- Any function `φ : α → loop X` can be seen as a function `α × ℝ → X`. -/
instance hasUncurryLoop {α : Type*} : HasUncurry (α → Loop X) (α × ℝ) X :=
  ⟨fun φ p ↦ φ p.1 p.2⟩


-- @@ L42-42 verbatim
variable {X}


-- @@ L44-44 verbatim
namespace Loop


-- @@ L46-47 verbatim
protected theorem coe_mk {γ : ℝ → X} (h : ∀ t, γ (t + 1) = γ t) : ⇑(⟨γ, h⟩ : Loop X) = γ :=
  rfl


-- @@ L49-51 verbatim
@[ext]
protected theorem ext : ∀ {γ₁ γ₂ : Loop X}, (γ₁ : ℝ → X) = γ₂ → γ₁ = γ₂
  | ⟨_x, _h1⟩, ⟨.(_x), _h2⟩, rfl => rfl


-- @@ L53-56 verbatim
/-- The constant loop. -/
@[simps]
def const (f : X) : Loop X :=
  ⟨fun _ ↦ f, fun _ ↦ rfl⟩


-- @@ L58-59 verbatim
instance Zero [Zero X] : Zero (Loop X) :=
  ⟨const 0⟩


-- @@ L61-65 verbatim
@[simp]
theorem zero_fun [_root_.Zero X] : ((0 : Loop X) : ℝ → X) = (0 : ℝ → X) :=
  rfl

-- unused

-- @@ L66-68 verbatim
@[simp]
theorem const_zero [_root_.Zero X] : const (0 : X) = (0 : Loop X) :=
  rfl


-- @@ L70-71 verbatim
instance [Inhabited X] : Inhabited (Loop X) :=
  ⟨Loop.const default⟩


-- @@ L73-75 verbatim
/-- Periodicity of loops restated in terms of the function coercion. -/
theorem per (γ : Loop X) : ∀ t, γ (t + 1) = γ t :=
  Loop.per' γ


-- @@ L77-78 verbatim
theorem periodic (γ : Loop X) : Function.Periodic γ 1 :=
  Loop.per' γ


-- @@ L80-82 verbatim
protected theorem one (γ : Loop X) : γ 1 = γ 0 := by convert γ.per 0; rw [zero_add]

-- unused

-- @@ L83-85 verbatim
theorem add_nat_eq (γ : Loop X) (t : ℝ) : ∀ n : ℕ, γ (t + n) = γ t
  | 0 => by rw [Nat.cast_zero, add_zero]
  | Nat.succ n => by rw [← γ.add_nat_eq t n, Nat.cast_succ, ← add_assoc, γ.per]


-- @@ L87-91 verbatim
theorem add_int_eq (γ : Loop X) (t : ℝ) (n : ℤ) : γ (t + n) = γ t := by
  induction n using Int.induction_on with
  | zero => norm_cast; rw [add_zero]
  | succ n hn => rw [← hn, Int.cast_add, ← add_assoc, Int.cast_one, γ.per]
  | pred n hn => rw [← hn, Int.cast_sub, add_sub, Int.cast_one, ← γ.per, sub_add_cancel]


-- @@ L93-97 verbatim
theorem fract_eq (γ : Loop X) : ∀ t, γ (fract t) = γ t := by
  intro t
  unfold fract
  rw [sub_eq_add_neg, ← Int.cast_neg]
  exact γ.add_int_eq ..


-- @@ L99-104 verbatim
theorem range_eq_image (γ : Loop X) : range γ = γ '' I := by
  apply eq_of_subset_of_subset
  · rw [range_subset_iff]
    exact fun y ↦ ⟨fract y, unitInterval.fract_mem y, γ.fract_eq _⟩
  · rintro y ⟨x, -, hxy⟩
    exact ⟨x, hxy⟩


-- @@ L106-109 verbatim
/-- Transforming a loop by applying function `f`. -/
@[simps]
def transform (γ : Loop X) (f : X → X') : Loop X' :=
  ⟨fun t ↦ f (γ t), fun t ↦ by rw [γ.per]⟩


-- @@ L111-114 verbatim
/-- Adding two loops pointwise. -/
@[simps]
instance Add [Add X] : Add (Loop X) :=
  ⟨fun γ₁ γ₂ ↦ ⟨fun t ↦ γ₁ t + γ₂ t, fun t ↦ by simp_rw [Loop.per]⟩⟩


-- @@ L116-118 verbatim
@[simps]
instance Neg [Neg X] : Neg (Loop X) :=
  ⟨fun γ ↦ ⟨fun t ↦ -γ t, fun t ↦ by simp_rw [Loop.per]⟩⟩


-- @@ L120-128 verbatim
instance [AddCommGroup X] : AddCommGroup (Loop X) :=
  { Loop.Add, Loop.Zero, Loop.Neg with
    add_assoc := fun γ₁ γ₂ γ₃ ↦ by ext t; apply add_assoc
    add_comm := fun γ₁ γ₂ ↦ by ext t; apply add_comm
    zero_add := fun γ ↦ by ext t; apply zero_add
    add_zero := fun γ ↦ by ext t; apply add_zero
    neg_add_cancel := fun γ ↦ by ext t; apply neg_add_cancel
    nsmul := nsmulRec
    zsmul := zsmulRec }


-- @@ L130-132 verbatim
/-- Shifting a loop, or equivalently, adding a constant value to a loop. -/
instance [_root_.Add X] : VAdd X (Loop X) :=
  ⟨fun x γ ↦ γ.transform fun y ↦ x + y⟩


-- @@ L134-136 verbatim
@[simp]
theorem vadd_apply [_root_.Add X] {x : X} {γ : Loop X} {t : ℝ} : (x +ᵥ γ) t = x + γ t :=
  rfl


-- @@ L138-140 verbatim
/-- Multiplying a loop by a scalar value. -/
instance [SMul K X] : SMul K (Loop X) :=
  ⟨fun k γ ↦ γ.transform fun y ↦ k • y⟩


-- @@ L142-148 verbatim
instance [Semiring K] [AddCommGroup X] [Module K X] : Module K (Loop X) where
  one_smul γ := by ext t; apply one_smul
  mul_smul k₁ k₂ γ := by ext t; apply mul_smul
  smul_zero k := by ext; apply smul_zero
  smul_add k γ₁ γ₂ := by ext t; apply smul_add
  add_smul k₁ k₂ γ := by ext t; apply add_smul
  zero_smul γ := by ext t; apply zero_smul


-- @@ L150-152 verbatim
@[simp]
theorem smul_apply [SMul K X] {k : K} {γ : Loop X} {t : ℝ} : (k • γ) t = k • γ t :=
  rfl


-- @@ L154-158 verbatim
/-- Reparametrizing loop `γ` using an equivariant map `φ`. -/
@[simps +simpRhs]
def reparam {F : Type*} (γ : Loop F) (φ : EquivariantMap) : Loop F where
  toFun := γ ∘ φ
  per' t := by rw [comp_apply, φ.eqv, γ.per]; rfl


-- @@ L160-160 verbatim
/-! ## Support of a loop family -/



-- @@ L163-167 verbatim
/-- A loop is constant if it takes the same value at every time.
See also `Loop.isConst_iff_forall_avg` and `Loop.isConst_iff_const_avg` for characterizations in
terms of average values. -/
def IsConst (γ : Loop X) :=
  ∀ t s, γ t = γ s


-- @@ L169-170 verbatim
theorem isConst_of_eq {γ : Loop X} {f : X} (H : ∀ t, γ t = f) : γ.IsConst := fun t t' ↦ by
  rw [H, H]


-- @@ L172-172 verbatim
variable [TopologicalSpace X] [TopologicalSpace X'] [TopologicalSpace Y] [TopologicalSpace Z]


-- @@ L174-177 verbatim
/-- The support of a loop family is the closure of the set of parameters where
the loop is not constant. -/
def support (γ : X → Loop X') : Set X :=
  closure {x | ¬(γ x).IsConst}


-- @@ L179-185 verbatim
omit [TopologicalSpace X'] in
theorem not_mem_support {γ : X → Loop X'} {x : X} (h : ∀ᶠ y in 𝓝 x, (γ y).IsConst) :
    x ∉ Loop.support γ := by
  intro hx
  rw [support, mem_closure_iff_nhds] at hx
  rcases hx _ h with ⟨z, hz, hz'⟩
  exact hz' hz


-- @@ L187-187 verbatim
/-! ## From paths to loops -/



-- @@ L190-194 verbatim
/-- Turn a path into a loop. -/
@[simps]
noncomputable def ofPath {x : X} (γ : Path x x) : Loop X where
  toFun t := γ.extend (fract t)
  per' t := by rw [fract_add_one]


-- @@ L196-212 verbatim
@[simp]
theorem range_ofPath {x : X} (γ : Path x x) : range (ofPath γ) = range γ := by
  rw [Loop.range_eq_image, ofPath, image_eq_range]
  apply congrArg
  ext t
  by_cases ht1 : t.val = 1
  · have : t = ⟨1, right_mem_Icc.mpr zero_le_one⟩ := Subtype.ext ht1
    rw [this]
    norm_cast
    simp only [fract, floor_one, Path.extend_zero, Int.cast_one, sub_self]
    exact γ.target.symm
  · change (t : ℝ) ≠ 1 at ht1
    have : fract ↑t = t.val := by
      rw [fract_eq_iff]
      refine ⟨t.2.1, t.2.2.lt_of_ne ht1, ⟨0, ?_⟩⟩
      rw [Int.cast_zero, sub_self]
    simp only [this, γ.extend_apply t.2]


-- @@ L214-224 verbatim
/-- `Loop.ofPath` is continuous, general version. -/
@[fun_prop]
theorem _root_.Continuous.ofPath (x : X → Y) (t : X → ℝ) (γ : ∀ i, Path (x i) (x i))
    (hγ : Continuous ↿γ) (ht : Continuous t) : Continuous fun i ↦ ofPath (γ i) (t i) := by
  change Continuous fun i ↦ (fun s ↦ (γ s).extend) i (fract (t i))
  refine ContinuousOn.comp_fract ?_ ht ?_
  · have : Continuous (fun x : X × ℝ ↦ (x.1, projIcc 0 1 zero_le_one x.2)) :=
      continuous_id.prodMap continuous_projIcc
    exact (hγ.comp this).continuousOn
  · simp only [Icc.mk_zero, zero_le_one, Path.target, Path.extend_apply, imp_true_iff,
      Path.source, right_mem_Icc, left_mem_Icc, Icc.mk_one]


-- @@ L226-231 verbatim
/-- `Loop.ofPath` is continuous, where the endpoints of `γ` are fixed. TODO: remove -/
@[fun_prop]
theorem ofPath_continuous_family {x : Y} (γ : X → Path x x) (h : Continuous ↿γ) :
    Continuous ↿fun s ↦ ofPath <| γ s :=
  Continuous.ofPath _ _ (fun i : X × ℝ ↦ γ i.1) (h.comp <| continuous_fst.prodMap continuous_id)
    continuous_snd


-- @@ L233-233 verbatim
/-! ## Round trips -/



-- @@ L236-238 verbatim
/-- The round-trip defined by `γ` is `γ` followed by `γ⁻¹`. -/
def roundTrip {x y : X} (γ : Path x y) : Loop X :=
  ofPath (γ.trans γ.symm)


-- @@ L240-241 verbatim
theorem roundTrip_range {x y : X} {γ : Path x y} : range (roundTrip γ) = range γ := by
  simp [roundTrip, range_ofPath, Path.trans_range, Path.symm_range]


-- @@ L243-244 verbatim
theorem roundTrip_based_at {x y : X} {γ : Path x y} : roundTrip γ 0 = x := by
  simp [roundTrip, ofPath, fract_zero]


-- @@ L246-251 verbatim
theorem roundTrip_eq {x y x' y' : X} {γ : Path x y} {γ' : Path x' y'} (h : ∀ s, γ s = γ' s) :
    roundTrip γ = roundTrip γ' := by
  obtain rfl : x = x' := γ.source.symm.trans ((h 0).trans γ'.source)
  obtain rfl : y = y' := γ.target.symm.trans ((h 1).trans γ'.target)
  obtain rfl : γ = γ' := by ext; apply h
  rfl


-- @@ L253-257 verbatim
/-- The round trip loop family associated to a path `γ`. For each parameter `t`,
the loop `roundTripFamily γ t` backtracks at `γ t`. -/
noncomputable def roundTripFamily {x y : X} (γ : Path x y) : ℝ → Loop X :=
  have key : ∀ {t}, x = γ.extend (min 0 t) := (γ.extend_of_le_zero <| min_le_left _ _).symm
  fun t ↦ roundTrip ((γ.truncate 0 t).cast key rfl)


-- @@ L259-259 verbatim
attribute [fun_prop] Path.trans_continuous_family


-- @@ L261-267 verbatim
@[fun_prop]
theorem roundTripFamily_continuous {x y : X} {γ : Path x y} : Continuous ↿(roundTripFamily γ) :=
  ofPath_continuous_family _
    (Path.trans_continuous_family _ (γ.truncate_const_continuous_family 0) _ <|
      Path.symm_continuous_family _ <|
        -- Was `fun_prop` before v4.21.0
        (by continuity))


-- @@ L269-270 verbatim
theorem roundTripFamily_based_at {x y : X} {γ : Path x y} : ∀ t, (roundTripFamily γ) t 0 = x :=
  fun _ ↦ roundTrip_based_at


-- @@ L272-276 verbatim
theorem roundTripFamily_zero {x y : X} {γ : Path x y} :
    (roundTripFamily γ) 0 = ofPath (Path.refl x) := by
  simp only [roundTripFamily, roundTrip, Path.truncate_zero_zero, ofPath]
  congr with t
  simp [← Path.cast_symm, ← Path.cast_trans]


-- @@ L278-280 verbatim
theorem roundTripFamily_one {x y : X} {γ : Path x y} : (roundTripFamily γ) 1 = roundTrip γ := by
  simp only [roundTripFamily, roundTrip, Path.truncate_zero_one, ofPath]
  rfl


-- @@ L282-282 verbatim
/-! ## Average value of a loop -/

-- @@ L283-283 verbatim
section Average


-- @@ L285-289 verbatim
/-- The average value of a loop. -/
noncomputable def average (γ : Loop F) : F :=
  ∫ x in (0 : ℝ)..1, γ x

-- unused

-- @@ L290-292 verbatim
@[simp]
theorem zero_average : average (0 : Loop F) = 0 :=
  intervalIntegral.integral_zero


-- @@ L294-303 verbatim
theorem isConst_iff_forall_avg [CompleteSpace F] {γ : Loop F} :
    γ.IsConst ↔ ∀ t, γ t = γ.average := by
  constructor <;> intro h
  · intro t
    have : γ = Loop.const (γ t) := by
      ext s
      exact h s t
    rw [this]
    simp [average, const_apply, intervalIntegral.integral_const, one_smul, sub_zero]
  · exact isConst_of_eq h


-- @@ L305-306 verbatim
@[simp]
theorem average_const [CompleteSpace F] {f : F} : (const f).average = f := by simp [Loop.average]


-- @@ L308-308 verbatim
open MeasureTheory


-- @@ L310-313 verbatim
@[simp]
theorem average_add {γ₁ γ₂ : Loop F} (hγ₁ : IntervalIntegrable γ₁ volume 0 1)
    (hγ₂ : IntervalIntegrable γ₂ volume 0 1) : (γ₁ + γ₂).average = γ₁.average + γ₂.average := by
  simp [Loop.average, intervalIntegral.integral_add hγ₁ hγ₂]


-- @@ L315-317 verbatim
@[simp]
theorem average_smul {γ : Loop F} {c : ℝ} : (c • γ).average = c • γ.average := by
  simp [Loop.average, intervalIntegral.integral_smul]


-- @@ L319-320 verbatim
theorem isConst_iff_const_avg [CompleteSpace F] {γ : Loop F} : γ.IsConst ↔ γ = const γ.average := by
  rw [Loop.isConst_iff_forall_avg, Loop.ext_iff, funext_iff]; rfl


-- @@ L322-326 verbatim
omit [NormedAddCommGroup F] [NormedSpace ℝ F] in
theorem isConst_of_not_mem_support {γ : X → Loop F} {x : X} (hx : x ∉ support γ) :
    (γ x).IsConst := by
  by_contra H
  exact hx (subset_closure H)


-- @@ L328-332 verbatim
@[fun_prop]
theorem continuous_average {E : Type*} [TopologicalSpace E]
    {γ : E → Loop F} (hγ_cont : Continuous ↿γ) :
    Continuous fun x ↦ (γ x).average :=
  intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (by apply hγ_cont) _ _


-- @@ L334-337 verbatim
/-- The normalization of a loop `γ` is the loop `γ - γ.average`. -/
def normalize (γ : Loop F) : Loop F where
  toFun t := γ t - γ.average
  per' t := by simp [γ.per]


-- @@ L339-341 verbatim
@[simp]
theorem normalize_apply (γ : Loop F) (t : ℝ) : Loop.normalize γ t = γ t - γ.average :=
  rfl


-- @@ L343-346 verbatim
@[simp]
theorem normalize_of_isConst [CompleteSpace F] {γ : Loop F} (h : γ.IsConst) : γ.normalize = 0 := by
  ext t
  simp [isConst_iff_forall_avg.mp h]


-- @@ L348-348 verbatim
end Average


-- @@ L350-350 verbatim
end Loop


-- @@ L352-352 verbatim
section C1


-- @@ L354-354 verbatim
/-! ## Differentiation of loop families -/



-- @@ L357-357 verbatim
@[inherit_doc] local notation "∂₁" => partialFDerivFst ℝ


-- @@ L359-359 verbatim
variable (π : E → ℝ) (N : ℝ) (γ : E → Loop F) (hγ : IsCompact (Loop.support γ))


-- @@ L361-364 verbatim
/-- Differential of a loop family with respect to the parameter. -/
def Loop.diff (γ : E → Loop F) (e : E) : Loop (E →L[ℝ] F) where
  toFun t := ∂₁ (fun e t ↦ γ e t) e t
  per' t := by simp only [partialFDerivFst, Loop.per]


-- @@ L366-369 verbatim
@[simp]
theorem Loop.diff_apply (γ : E → Loop F) (e : E) (t : ℝ) :
    Loop.diff γ e t = ∂₁ (fun e t ↦ γ e t) e t :=
  rfl


-- @@ L371-373 expanded
@[fun_prop]
theorem Loop.continuous_diff {γ : E → Loop F} (h : (ContDiff ℝ) 1 ↿γ) : Continuous ↿(Loop.diff γ) :=
  ContDiff.continuous_partial_fst (h : _)


-- @@ L375-377 expanded
theorem ContDiff.partial_loop {γ : E → Loop F} {n : ℕ∞} (hγ_diff : (ContDiff ℝ) n ↿γ) :
    ∀ t, (ContDiff ℝ) n fun e ↦ γ e t := by fun_prop


-- @@ L379-379 verbatim
variable [FiniteDimensional ℝ F]


-- @@ L381-395 expanded
set_option backward.isDefEq.respectTransparency.types false in
theorem Loop.support_diff {γ : E → Loop F} : Loop.support (Loop.diff γ) ⊆ Loop.support γ :=
  by
  unfold Loop.support
  erw [closure_compl, closure_compl]
  rw [compl_subset_compl]
  intro x hx
  rw [mem_interior_iff_mem_nhds] at *
  rcases mem_nhds_iff.mp hx with ⟨U, hU, U_op, hxU⟩
  apply Filter.mem_of_superset (U_op.mem_nhds hxU) fun y hy ↦ ?_
  have Hy : ∀ t, (fun z ↦ γ z t) =ᶠ[𝓝 y] fun z ↦ (γ z).average := fun t ↦
    Filter.mem_of_superset (U_op.mem_nhds hy) (fun z hz ↦ Loop.isConst_iff_forall_avg.mp (hU hz) t)
  have : ∀ t : ℝ, Loop.diff γ y t = (fderiv ℝ) (fun z : E ↦ (γ z).average) y := fun t ↦
    (Hy t).fderiv_eq
  intro t s
  simp only [this]


-- @@ L398-398 verbatim
variable [FiniteDimensional ℝ E]


-- @@ L400-404 expanded
theorem Loop.average_diff {γ : E → Loop F} (hγ_diff : (ContDiff ℝ) 1 ↿γ) (e : E) :
    (Loop.diff γ e).average = (fderiv ℝ) (fun e ↦ (γ e).average) e :=
  by
  change (ContDiff ℝ) 1 ↿fun (e : E) (t : ℝ) ↦ γ e t at hγ_diff
  simp only [Loop.average, hγ_diff.fderiv_parametric_integral]
  rfl


-- @@ L406-406 verbatim
attribute [fun_prop] contDiff_parametric_integral_of_contDiff

-- @@ L407-409 expanded
theorem ContDiff.loop_average {γ : E → Loop F} {n : ℕ∞} (hγ_diff : (ContDiff ℝ) n ↿γ) :
    (ContDiff ℝ) n fun e ↦ (γ e).average := by unfold Loop.average; fun_prop


-- @@ L411-417 expanded
theorem Loop.diff_normalize {γ : E → Loop F} (hγ_diff : (ContDiff ℝ) 1 ↿γ) (e : E) :
    (Loop.diff γ e).normalize = Loop.diff (fun e ↦ (γ e).normalize) e :=
  by
  ext t x
  simp only [Loop.diff_apply, Loop.normalize_apply, partialFDerivFst]
  rw [fderiv_fun_sub ((hγ_diff.partial_loop t).differentiable (by simp)).differentiableAt,
    Loop.average_diff hγ_diff]
  exact (hγ_diff.loop_average.differentiable (by simp)).differentiableAt


-- @@ L419-419 verbatim
variable {γ}


-- @@ L421-422 expanded
theorem contDiff_average {n : ℕ∞} (hγ_diff : (ContDiff ℝ) n ↿γ) :
    (ContDiff ℝ) n fun x ↦ (γ x).average := by unfold Loop.average; fun_prop


-- @@ L424-426 expanded
theorem contDiff_sub_average {n : ℕ∞} (hγ_diff : (ContDiff ℝ) n ↿γ) :
    (ContDiff ℝ) n ↿fun (x : E) (t : ℝ) ↦ (γ x) t - (γ x).average := by unfold Loop.average;
  fun_prop


-- @@ L428-428 verbatim
end C1
