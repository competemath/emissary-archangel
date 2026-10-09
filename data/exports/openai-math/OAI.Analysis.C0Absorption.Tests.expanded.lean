import OAI.Analysis.C0Absorption.Triangular


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
open Set Filter Topology

-- @@ L6-6 verbatim
open scoped NNReal BigOperators ZeroAtInfty

-- @@ L7-7 verbatim
open NormedSpace


-- @@ L9-9 verbatim
namespace C0Absorption

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
open Set Filter Topology

-- @@ L12-12 verbatim
open scoped NNReal BigOperators ZeroAtInfty


-- @@ L14-17 verbatim
structure CylinderOperation (I : Finset ℕ) where
  scaleIndex : ℕ
  center : OperationGrid I scaleIndex
  isG : Bool


-- @@ L19-19 verbatim
namespace CylinderOperation

-- @@ L20-20 verbatim
variable {I : Finset ℕ}

-- @@ L21-21 verbatim
def scale (r : CylinderOperation I) : ℝ := dyadic r.scaleIndex

-- @@ L22-22 verbatim
def point (r : CylinderOperation I) : Cube I := operationGridPoint I r.scaleIndex r.center

-- @@ L23-24 verbatim
def act (r : CylinderOperation I) : (Cube I → ℝ) →ₗ[ℝ] (Cube I → ℝ) :=
  localOp r.isG r.point r.scale


-- @@ L26-26 verbatim
theorem scale_pos (r : CylinderOperation I) : 0 < r.scale := dyadic_pos r.scaleIndex


-- @@ L28-32 verbatim
theorem act_lipschitz (r : CylinderOperation I) {K : ℝ≥0} {u : Cube I → ℝ}
    (hu : LipschitzWith K u) : LipschitzWith (4*K) (r.act u) := by
  cases hr : r.isG <;> simp only [act, localOp, hr, Bool.false_eq_true, ↓reduceIte]
  · exact (localR_lipschitz r.point r.scale_pos u hu).weaken (by nlinarith)
  · exact localG_lipschitz r.point r.scale_pos u hu


-- @@ L34-39 verbatim
theorem act_sup (r : CylinderOperation I) {A : ℝ} (hA : 0 ≤ A)
    {u : Cube I → ℝ} (hu : ∀ x, |u x| ≤ A) : ∀ x, |r.act u x| ≤ 2*A := by
  intro x
  cases hr : r.isG <;> simp only [act, localOp, hr, Bool.false_eq_true, ↓reduceIte]
  · exact localR_sup r.point r.scale u A hu x
  · exact (localG_sup r.point r.scale u A hu x).trans (by linarith)


-- @@ L41-41 verbatim
end CylinderOperation


-- @@ L43-47 verbatim
def applyOperations {I : Finset ℕ} (ops : List (CylinderOperation I)) :
    (Cube I → ℝ) →ₗ[ℝ] (Cube I → ℝ) :=
  match ops with
  | [] => LinearMap.id
  | r :: rs => (applyOperations rs).comp r.act


-- @@ L49-49 verbatim
@[simp] theorem applyOperations_nil {I : Finset ℕ} (u : Cube I → ℝ) : applyOperations [] u = u := rfl

-- @@ L50-52 verbatim
@[simp] theorem applyOperations_cons {I : Finset ℕ} (r : CylinderOperation I)
    (rs : List (CylinderOperation I)) (u : Cube I → ℝ) :
    applyOperations (r::rs) u = applyOperations rs (r.act u) := rfl


-- @@ L54-58 verbatim
theorem applyOperations_append {I : Finset ℕ} (rs ss : List (CylinderOperation I))
    (u : Cube I → ℝ) : applyOperations (rs++ss) u = applyOperations ss (applyOperations rs u) := by
  induction rs generalizing u with
  | nil => rfl
  | cons r rs ih => simpa using ih (r.act u)


-- @@ L60-67 verbatim
theorem applyOperations_lipschitz {I : Finset ℕ} (ops : List (CylinderOperation I))
    {K : ℝ≥0} {u : Cube I → ℝ} (hu : LipschitzWith K u) :
    LipschitzWith (4^ops.length*K) (applyOperations ops u) := by
  induction ops generalizing K u with
  | nil => simpa using hu
  | cons r rs ih =>
    have hh := ih (r.act_lipschitz hu)
    simpa only [applyOperations_cons, List.length_cons, pow_succ, mul_assoc] using hh


-- @@ L69-76 verbatim
theorem applyOperations_sup {I : Finset ℕ} (ops : List (CylinderOperation I))
    {A : ℝ} (hA : 0 ≤ A) {u : Cube I → ℝ} (hu : ∀ x, |u x| ≤ A) :
    ∀ x, |applyOperations ops u x| ≤ 2^ops.length*A := by
  induction ops generalizing A u with
  | nil => simpa using hu
  | cons r rs ih =>
    have hh := ih (by positivity : 0 ≤ 2*A) (r.act_sup hA hu)
    simpa only [applyOperations_cons, List.length_cons, pow_succ, mul_assoc] using hh


-- @@ L78-88 verbatim
theorem applyOperations_support_bound {I : Finset ℕ} (ops : List (CylinderOperation I))
    (u : Cube I → ℝ) {φ : Cube I → ℝ} (hφ : LipschitzWith 1 φ) {b : ℝ}
    (hu : ∀ x ∈ tsupport u, φ x ≤ b) :
    ∀ x ∈ tsupport (applyOperations ops u), φ x ≤ b+(ops.map CylinderOperation.scale).sum := by
  induction ops generalizing u b with
  | nil => simpa using hu
  | cons r rs ih =>
    have hnew : ∀ x ∈ tsupport (r.act u), φ x ≤ b+r.scale := by
      simpa only [CylinderOperation.act, NNReal.coe_one, mul_one] using localOp_support_bound r.isG r.point r.scale_pos u φ hφ b hu
    have hh := ih (r.act u) hnew
    simpa only [List.map_cons, List.sum_cons, applyOperations_cons, add_assoc] using hh


-- @@ L90-100 verbatim
structure CylinderBases (Γ : Type*) where
  coordinates : Γ → Finset ℕ
  coordinates_nonempty : ∀ γ, (coordinates γ).Nonempty
  band : Γ → ℕ
  ell : ℕ → ℝ
  ell_pos : ∀ j, 0 < ell j
  base : (γ : Γ) → Cube (coordinates γ) → ℝ
  A : ℝ≥0
  L0 : ℝ≥0
  base_sup : ∀ γ x, |base γ x| ≤ A
  base_lipschitz : ∀ γ, LipschitzWith L0 (base γ)


-- @@ L102-105 verbatim
structure GeneratedRepresentation {Γ : Type*} (B : CylinderBases Γ) (γ : Γ) where
  operations : List (CylinderOperation (B.coordinates γ))
  ordered : operations.Pairwise (fun p q => q.scale ≤ p.scale)
  budget : (operations.map CylinderOperation.scale).sum < B.ell (B.band γ)/2


-- @@ L107-107 verbatim
namespace GeneratedRepresentation

-- @@ L108-108 verbatim
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}


-- @@ L110-111 verbatim
def cubeValue (r : GeneratedRepresentation B γ) : Cube (B.coordinates γ) → ℝ :=
  applyOperations r.operations (B.base γ)


-- @@ L113-114 verbatim
def value (r : GeneratedRepresentation B γ) : C0Ball → ℝ :=
  r.cubeValue ∘ cubeRestrict (B.coordinates γ)


-- @@ L116-117 verbatim
def baseRepresentation (B : CylinderBases Γ) (γ : Γ) : GeneratedRepresentation B γ :=
  ⟨[], by simp, by simpa using half_pos (B.ell_pos (B.band γ))⟩


-- @@ L119-121 verbatim
theorem cubeValue_lipschitz (r : GeneratedRepresentation B γ) :
    LipschitzWith (4^r.operations.length*B.L0) r.cubeValue :=
  applyOperations_lipschitz _ (B.base_lipschitz γ)


-- @@ L123-125 verbatim
theorem value_lipschitz (r : GeneratedRepresentation B γ) :
    LipschitzWith (4^r.operations.length*B.L0) r.value := by
  simpa only [value, mul_one] using r.cubeValue_lipschitz.comp (cubeRestrict_lipschitz (B.coordinates γ))


-- @@ L127-129 verbatim
theorem cubeValue_sup (r : GeneratedRepresentation B γ) :
    ∀ x, |r.cubeValue x| ≤ (2 : ℝ)^r.operations.length*B.A :=
  applyOperations_sup _ B.A.coe_nonneg (B.base_sup γ)


-- @@ L131-133 verbatim
theorem value_sup (r : GeneratedRepresentation B γ) :
    ∀ x, |r.value x| ≤ (2 : ℝ)^r.operations.length*B.A :=
  fun point => r.cubeValue_sup (cubeRestrict (B.coordinates γ) point)


-- @@ L135-135 verbatim
end GeneratedRepresentation


-- @@ L137-138 verbatim
def TClass {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) : Set (C0Ball → ℝ) :=
  {f | ∃ γ, ∃ r : GeneratedRepresentation B γ, r.operations.length ≤ h ∧ f = r.value}


-- @@ L140-143 verbatim
structure TailOperation where
  scaleIndex : ℕ
  tailIndex : ℕ
  isBasic : Bool


-- @@ L145-145 verbatim
namespace TailOperation


-- @@ L147-149 verbatim
def factor (t : TailOperation) (s : C0Ball) : ℝ :=
  if t.isBasic then tailFactor (dyadic t.scaleIndex) (t.tailIndex+1) s.val
  else tailFactor (dyadic t.scaleIndex) (t.tailIndex+1) s.val-1


-- @@ L151-156 verbatim
theorem factor_abs_le (t : TailOperation) (s : C0Ball) : |t.factor s| ≤ 1 := by
  have hl := tailFactor_nonneg (dyadic t.scaleIndex) (t.tailIndex+1) s.val
  have hu := tailFactor_le_one (dyadic t.scaleIndex) (t.tailIndex+1) s.val
  rw [abs_le]
  unfold factor
  split <;> constructor <;> linarith


-- @@ L158-169 verbatim
theorem factor_lipschitz (t : TailOperation) : LipschitzWith (2^t.scaleIndex) t.factor := by
  apply LipschitzWith.of_dist_le_mul
  intro s u
  have hh := (tailFactor_lipschitz (dyadic_pos t.scaleIndex) (t.tailIndex+1)).dist_le_mul s.val u.val
  change dist (tailFactor (dyadic t.scaleIndex) (t.tailIndex+1) s.val)
      (tailFactor (dyadic t.scaleIndex) (t.tailIndex+1) u.val) ≤
      (dyadic t.scaleIndex)⁻¹ * dist s u at hh
  simp only [dyadic, inv_inv] at hh
  simp only [NNReal.coe_pow, NNReal.coe_ofNat]
  cases ht : t.isBasic
  · simpa only [factor, dyadic, ht, Bool.false_eq_true, ↓reduceIte, dist_sub_right] using hh
  · simpa only [factor, dyadic, ht, ↓reduceIte] using hh


-- @@ L171-171 verbatim
end TailOperation


-- @@ L173-173 verbatim
def tailProduct (ts : List TailOperation) (s : C0Ball) : ℝ := (ts.map (fun t => t.factor s)).prod


-- @@ L175-175 verbatim
@[simp] theorem tailProduct_nil (s : C0Ball) : tailProduct [] s = 1 := rfl

-- @@ L176-177 verbatim
@[simp] theorem tailProduct_cons (t : TailOperation) (ts : List TailOperation) (s : C0Ball) :
    tailProduct (t::ts) s = t.factor s * tailProduct ts s := rfl


-- @@ L179-184 verbatim
theorem tailProduct_abs_le (ts : List TailOperation) (s : C0Ball) : |tailProduct ts s| ≤ 1 := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [tailProduct_cons, abs_mul]
    exact (mul_le_mul (t.factor_abs_le s) ih (abs_nonneg _) zero_le_one).trans_eq (one_mul 1)


-- @@ L186-201 verbatim
theorem bounded_product_lipschitz {X : Type*} [PseudoMetricSpace X]
    {f g : X → ℝ} {K L A B : ℝ≥0} (hf : LipschitzWith K f) (hg : LipschitzWith L g)
    (hfB : ∀ x, |f x| ≤ A) (hgB : ∀ x, |g x| ≤ B) :
    LipschitzWith (A*L+B*K) (fun x => f x*g x) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [Real.dist_eq]
  have he : f x*g x-f y*g y = f x*(g x-g y)+g y*(f x-f y) := by ring
  rw [he]
  calc
    _ ≤ |f x*(g x-g y)|+|g y*(f x-f y)| := abs_add_le _ _
    _ = |f x| * |g x-g y|+|g y| * |f x-f y| := by rw [abs_mul, abs_mul]
    _ ≤ A*(L*dist x y)+B*(K*dist x y) := add_le_add
      (mul_le_mul (hfB x) (hg.dist_le_mul x y) (abs_nonneg _) A.coe_nonneg)
      (mul_le_mul (hgB y) (hf.dist_le_mul x y) (abs_nonneg _) B.coe_nonneg)
    _ = _ := by push_cast; ring


-- @@ L203-211 verbatim
theorem tailProduct_lipschitz (ts : List TailOperation) :
    LipschitzWith ((ts.map (fun t => (2 : ℝ≥0)^t.scaleIndex)).sum) (tailProduct ts) := by
  induction ts with
  | nil =>
    change LipschitzWith 0 (fun _ : C0Ball => (1 : ℝ))
    exact LipschitzWith.const 1
  | cons t ts ih =>
    have hh := bounded_product_lipschitz (A := 1) (B := 1) t.factor_lipschitz ih t.factor_abs_le (tailProduct_abs_le ts)
    convert hh using 1 <;> first | rfl | simp only [List.map_cons, List.sum_cons, one_mul, add_comm]


-- @@ L213-222 verbatim
theorem tailProduct_lipschitz_bound (ts : List TailOperation) (h : ℕ)
    (hlen : ts.length ≤ h) (hscale : ∀ t ∈ ts, t.scaleIndex ≤ h) :
    LipschitzWith ((h : ℝ≥0)*2^h) (tailProduct ts) := by
  apply (tailProduct_lipschitz ts).weaken
  calc
    (ts.map (fun t => (2 : ℝ≥0)^t.scaleIndex)).sum ≤
        (ts.map (fun _ => (2 : ℝ≥0)^h)).sum := List.sum_le_sum
          (fun t ht => pow_le_pow_right₀ (by norm_num) (hscale t ht))
    _ = (ts.length : ℝ≥0)*2^h := by simp
    _ ≤ (h : ℝ≥0)*2^h := mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) (by positivity)


-- @@ L224-227 verbatim
def VClass {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) : Set (C0Ball → ℝ) :=
  {f | ∃ γ, ∃ r : GeneratedRepresentation B γ, ∃ ts : List TailOperation,
    r.operations.length ≤ h ∧ B.band γ ≤ h ∧ ts.length ≤ h ∧
      (∀ t ∈ ts, t.scaleIndex ≤ h) ∧ f = fun s => r.value s*tailProduct ts s}


-- @@ L229-233 verbatim
theorem TClass_lipschitz {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) {f : C0Ball → ℝ}
    (hf : f ∈ TClass B h) : LipschitzWith (4^h*B.L0) f := by
  obtain ⟨γ,r,hlen,rfl⟩ := hf
  apply r.value_lipschitz.weaken
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hlen) B.L0.coe_nonneg


-- @@ L235-240 verbatim
theorem TClass_sup {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) {f : C0Ball → ℝ}
    (hf : f ∈ TClass B h) : ∀ s, |f s| ≤ (2 : ℝ)^h*B.A := by
  obtain ⟨γ,r,hlen,rfl⟩ := hf
  intro s
  exact (r.value_sup s).trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num) hlen) B.A.coe_nonneg)


-- @@ L242-255 verbatim
theorem VClass_lipschitz {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) {f : C0Ball → ℝ}
    (hf : f ∈ VClass B h) : LipschitzWith (4^h*B.L0+h*4^h*B.A) f := by
  obtain ⟨γ,r,ts,hren,hband,hlen,hscale,rfl⟩ := hf
  have hu : LipschitzWith (4^h*B.L0) r.value := TClass_lipschitz B h ⟨γ,r,hren,rfl⟩
  have hb := tailProduct_lipschitz_bound ts h hlen hscale
  have hsup : ∀ s, |r.value s| ≤ ((2 : ℝ≥0)^h*B.A : ℝ≥0) := by
    intro s
    simpa only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat] using TClass_sup B h ⟨γ,r,hren,rfl⟩ s
  have hh := bounded_product_lipschitz (B := 1) hu hb hsup (tailProduct_abs_le ts)
  convert hh using 1 ; try rfl
  rw [one_mul]
  have hp : (4 : ℝ≥0)^h = 2^h*2^h := by rw [← mul_pow]; norm_num
  rw [hp]
  ring


-- @@ L257-263 verbatim
theorem VClass_sup {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) {f : C0Ball → ℝ}
    (hf : f ∈ VClass B h) : ∀ s, |f s| ≤ (2 : ℝ)^h*B.A := by
  obtain ⟨γ,r,ts,hren,hband,hlen,hscale,rfl⟩ := hf
  intro s
  rw [abs_mul]
  exact (mul_le_mul (TClass_sup B h ⟨γ,r,hren,rfl⟩ s) (tailProduct_abs_le ts s)
    (abs_nonneg _) (by positivity)).trans_eq (mul_one _)


-- @@ L265-266 verbatim
def sourceClasses {Γ : Type*} (B : CylinderBases Γ) (n : ℕ) : Set (C0Ball → ℝ) :=
  if n % 2 = 0 then TClass B (n/2+1) else VClass B (n/2+1)


-- @@ L268-269 verbatim
@[simp] theorem sourceClasses_even {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) :
    sourceClasses B (2*h) = TClass B (h+1) := by simp [sourceClasses]


-- @@ L271-274 verbatim
@[simp] theorem sourceClasses_odd {Γ : Type*} (B : CylinderBases Γ) (h : ℕ) :
    sourceClasses B (2*h+1) = VClass B (h+1) := by
  have hh : (2*h+1)/2 = h := by omega
  simp [sourceClasses, hh]


-- @@ L276-281 verbatim
theorem tsupport_comp_subset {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : Y → ℝ) {π : X → Y} (hπ : Continuous π) :
    tsupport (f ∘ π) ⊆ π ⁻¹' tsupport f := by
  apply closure_minimal
  · intro x hx; exact subset_tsupport f hx
  · exact (isClosed_tsupport f).preimage hπ


-- @@ L283-287 verbatim
theorem tsupport_product_subset_left {X : Type*} [TopologicalSpace X] (f g : X → ℝ) :
    tsupport (fun x => f x*g x) ⊆ tsupport f := by
  apply closure_minimal _ (isClosed_tsupport f)
  intro x hx
  exact subset_tsupport f (left_ne_zero_of_mul (show f x*g x ≠ 0 from hx))


-- @@ L289-289 verbatim
namespace GeneratedRepresentation

-- @@ L290-290 verbatim
variable {Γ : Type*} {B : CylinderBases Γ} {γ : Γ}


-- @@ L292-298 verbatim
theorem support_bound (r : GeneratedRepresentation B γ) {φ : Cube (B.coordinates γ) → ℝ}
    (hφ : LipschitzWith 1 φ) {b : ℝ} (hu : ∀ x ∈ tsupport (B.base γ), φ x ≤ b) :
    ∀ s ∈ tsupport r.value,
      φ (cubeRestrict (B.coordinates γ) s) ≤ b+(r.operations.map CylinderOperation.scale).sum := by
  intro s hs
  have hm := tsupport_comp_subset r.cubeValue (cubeRestrict_lipschitz (B.coordinates γ)).continuous hs
  exact applyOperations_support_bound r.operations (B.base γ) hφ hu _ hm


-- @@ L300-308 verbatim
def append (r : GeneratedRepresentation B γ) (op : CylinderOperation (B.coordinates γ))
    (hord : ∀ p ∈ r.operations, op.scale ≤ p.scale)
    (hbudget : (r.operations.map CylinderOperation.scale).sum+op.scale < B.ell (B.band γ)/2) :
    GeneratedRepresentation B γ where
  operations := r.operations++[op]
  ordered := List.pairwise_append.mpr ⟨r.ordered, by simp, by
    intro p hp q hq; have hq' : q=op := by simpa using hq
    subst q; exact hord p hp⟩
  budget := by simpa using hbudget


-- @@ L310-314 verbatim
@[simp] theorem append_cubeValue (r : GeneratedRepresentation B γ) (op : CylinderOperation (B.coordinates γ))
    (hord : ∀ p ∈ r.operations, op.scale ≤ p.scale)
    (hbudget : (r.operations.map CylinderOperation.scale).sum+op.scale < B.ell (B.band γ)/2) :
    (r.append op hord hbudget).cubeValue = op.act r.cubeValue := by
  exact applyOperations_append r.operations [op] (B.base γ)


-- @@ L316-326 verbatim
theorem eventually_append_allowed (r : GeneratedRepresentation B γ) :
    ∀ᶠ a in atTop, (∀ p ∈ r.operations, dyadic a ≤ p.scale) ∧
      (r.operations.map CylinderOperation.scale).sum+dyadic a < B.ell (B.band γ)/2 := by
  have h1 : ∀ᶠ a in atTop, ∀ p ∈ r.operations, dyadic a ≤ p.scale := by
    apply r.operations.finite_toSet.eventually_all.mpr
    intro p hp
    exact dyadic_tendsto.eventually (eventually_le_nhds p.scale_pos)
  have h2 : ∀ᶠ a in atTop, dyadic a < B.ell (B.band γ)/2-(r.operations.map CylinderOperation.scale).sum :=
    dyadic_tendsto.eventually (eventually_lt_nhds (sub_pos.mpr r.budget))
  filter_upwards [h1,h2] with a ha hb
  exact ⟨ha, by linarith⟩


-- @@ L328-328 verbatim
end GeneratedRepresentation


-- @@ L330-330 verbatim
end

-- @@ L331-331 verbatim
end C0Absorption


-- @@ L333-333 verbatim
end OAI
