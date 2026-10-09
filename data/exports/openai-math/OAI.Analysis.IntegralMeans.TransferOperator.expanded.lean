import OAI.Analysis.IntegralMeans.TransportBoxes


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open Set MeasureTheory Filter Function InnerProductSpace

-- @@ L7-7 verbatim
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical

-- @@ L8-8 verbatim
open MeasureTheory Function

-- @@ L9-9 verbatim
open Set Filter

-- @@ L10-10 verbatim
open Set MeasureTheory Filter Function

-- @@ L11-11 verbatim
open Set MeasureTheory Filter Function InnerProductSpace

-- @@ L12-12 verbatim
open TopologicalSpace

-- @@ L13-13 verbatim
open scoped CompactlySupported

-- @@ L14-14 verbatim
open scoped ENNReal

-- @@ L15-15 verbatim
open scoped Manifold

-- @@ L16-16 verbatim
open scoped Topology CompactlySupported ComplexConjugate

-- @@ L17-17 verbatim
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical

-- @@ L18-18 verbatim
open scoped Topology ENNReal NNReal

-- @@ L19-19 verbatim
namespace Brennan


-- @@ L21-21 verbatim
attribute [local irreducible] classWeight

-- @@ L22-22 verbatim
attribute [local irreducible] classFun


-- @@ L24-24 verbatim
def halfMul (z w : halfPlane) : halfPlane := ⟨affine z w,affine_mem z.2 w.2⟩


-- @@ L26-27 verbatim
def halfPoint (x y : ℝ) (hy : 0 < y) : halfPlane :=
  ⟨(x : ℂ)+(y : ℂ)*Complex.I,by simpa [halfPlane]⟩


-- @@ L29-29 verbatim
def horizontal (x : ℝ) : halfPlane := halfPoint x 1 zero_lt_one


-- @@ L31-34 verbatim
lemma halfPoint_mul (x y u v : ℝ) (hy : 0 < y) (hv : 0 < v) :
    halfMul (halfPoint x y hy) (halfPoint u v hv) = halfPoint (x+y*u) (y*v) (mul_pos hy hv) := by
  apply Subtype.ext
  apply Complex.ext <;> simp [halfMul,halfPoint,affine]


-- @@ L36-37 verbatim
lemma halfMul_assoc (z w u : halfPlane) : halfMul (halfMul z w) u = halfMul z (halfMul w u) :=
  Subtype.ext (affine_assoc z w u)


-- @@ L39-39 verbatim
lemma halfOne_mul (z : halfPlane) : halfMul halfOne z = z := Subtype.ext (I_affine z)


-- @@ L41-41 verbatim
lemma halfMul_one (z : halfPlane) : halfMul z halfOne = z := Subtype.ext (affine_I z)


-- @@ L43-46 verbatim
lemma continuous_halfPoint.{u_1} {Y : Type u_1} [TopologicalSpace Y] {x y : Y → ℝ}
    (hx : Continuous x) (hy : Continuous y) (hp : ∀ a, 0 < y a) :
    Continuous (fun a => halfPoint (x a) (y a) (hp a)) :=
  ((Complex.continuous_ofReal.comp hx).add ((Complex.continuous_ofReal.comp hy).mul continuous_const)).subtype_mk _


-- @@ L48-52 verbatim
lemma rerootClass_one (g : DiskClass) : rerootClass g halfOne = g := by
  apply class_ext
  intro z hz
  rw [classFun_rerootClass _ _ hz]
  simp [reroot,halfOne,(classFun_schlicht g).2.1,(classFun_schlicht g).2.2]


-- @@ L54-55 verbatim
lemma classWeight_one (g : DiskClass) : classWeight g halfOne = 1 := by
  simp [classWeight,reciprocalDeriv,halfOne,(classFun_schlicht g).2.2]


-- @@ L57-57 verbatim
attribute [local irreducible] rerootClass


-- @@ L59-62 verbatim
def weightAt (z : halfPlane) : C(DiskClass,ℝ) :=
  ⟨fun g => classWeight g z,by
    have hc : Continuous (fun g : DiskClass => (g,z)) := continuous_id.prodMk continuous_const
    exact continuous_classWeight.comp hc⟩


-- @@ L64-67 verbatim
def actionAt (z : halfPlane) : C(DiskClass,DiskClass) :=
  ⟨fun g => rerootClass g z,by
    have hc : Continuous (fun g : DiskClass => (g,z)) := continuous_id.prodMk continuous_const
    exact continuous_rerootClass.comp hc⟩


-- @@ L69-70 verbatim
def affineOperator (z : halfPlane) : C(DiskClass,ℝ) →L[ℝ] C(DiskClass,ℝ) :=
  (ContinuousLinearMap.mul ℝ C(DiskClass,ℝ) (weightAt z)).comp (ContinuousMap.compCLM ℝ ℝ (actionAt z))


-- @@ L72-73 verbatim
lemma affineOperator_apply (z : halfPlane) (f : C(DiskClass,ℝ)) (g : DiskClass) :
    affineOperator z f g = classWeight g z * f (rerootClass g z) := rfl


-- @@ L75-76 verbatim
lemma affineOperator_pos (z : halfPlane) (f : C(DiskClass,ℝ)) (hf : 0 ≤ f) :
    0 ≤ affineOperator z f := fun g => mul_nonneg (classWeight_pos g z).le (hf _)


-- @@ L78-83 verbatim
lemma affineOperator_mul (z w : halfPlane) :
    affineOperator z * affineOperator w = affineOperator (halfMul z w) := by
  ext f g
  change classWeight g z * (classWeight (rerootClass g z) w * f (rerootClass (rerootClass g z) w)) = _
  rw [← mul_assoc,classWeight_cocycle,rerootClass_comp]
  rfl


-- @@ L85-88 verbatim
lemma affineOperator_one : affineOperator halfOne = 1 := by
  ext f g
  simp only [affineOperator_apply,classWeight_one,rerootClass_one,one_mul]
  rfl


-- @@ L90-97 verbatim
lemma continuous_affineOperator_apply (f : C(DiskClass,ℝ)) :
    Continuous (fun z : halfPlane => affineOperator z f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hw : Continuous (fun p : halfPlane × DiskClass => classWeight p.2 p.1) :=
    continuous_classWeight.comp (continuous_swap : Continuous (Prod.swap : halfPlane × DiskClass → DiskClass × halfPlane))
  have ht : Continuous (fun p : halfPlane × DiskClass => rerootClass p.2 p.1) :=
    continuous_rerootClass.comp (continuous_swap : Continuous (Prod.swap : halfPlane × DiskClass → DiskClass × halfPlane))
  exact hw.mul (f.continuous.comp ht)


-- @@ L99-106 verbatim
lemma affineOperator_norm_le {z : halfPlane} {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ g : DiskClass, classWeight g z ≤ B) : ‖affineOperator z‖ ≤ B := by
  apply (affineOperator z).opNorm_le_bound hB
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg hB (norm_nonneg f))).mpr
  intro g
  rw [affineOperator_apply,norm_mul,Real.norm_of_nonneg (classWeight_pos g z).le]
  exact mul_le_mul (hw g) (ContinuousMap.norm_coe_le_norm f _) (norm_nonneg _) hB


-- @@ L108-109 verbatim
lemma classFun_identityClass : EqOn (classFun identityClass) identityHalf halfPlane :=
  classFun_classOfHalf identityHalf_schlicht


-- @@ L111-114 verbatim
lemma classWeight_identityClass (z : halfPlane) : classWeight identityClass z = 1 := by
  have hd := classFun_identityClass.deriv isOpen_halfPlane z.2
  have hi : deriv identityHalf z = 1 := ((hasDerivAt_id (z : ℂ)).sub_const Complex.I).deriv
  simp [classWeight,reciprocalDeriv,hd,hi]


-- @@ L116-125 verbatim
lemma reroot_identityClass (z : halfPlane) : rerootClass identityClass z = identityClass := by
  apply class_ext
  intro w hw
  rw [classFun_rerootClass _ _ hw,reroot_congr classFun_identityClass z.2 hw,classFun_identityClass hw]
  have hd : deriv identityHalf z = 1 := ((hasDerivAt_id (z : ℂ)).sub_const Complex.I).deriv
  have he : (z.val.re : ℂ)+(z.val.im : ℂ)*Complex.I = z := by apply Complex.ext <;> simp
  dsimp [reroot,identityHalf,affine]
  rw [hd,mul_one]
  apply (div_eq_iff (Complex.ofReal_ne_zero.mpr (ne_of_gt z.2))).mpr
  linear_combination he


-- @@ L127-127 verbatim
def dyadicLeft : halfPlane := halfPoint (-1/2) (1/2) (by norm_num)


-- @@ L129-129 verbatim
def dyadicRight : halfPlane := halfPoint (1/2) (1/2) (by norm_num)


-- @@ L131-132 verbatim
def transferOperator : C(DiskClass,ℝ) →L[ℝ] C(DiskClass,ℝ) :=
  (1/2 : ℝ) • (affineOperator dyadicLeft+affineOperator dyadicRight)


-- @@ L134-137 verbatim
lemma transferOperator_pos (f : C(DiskClass,ℝ)) (hf : 0 ≤ f) : 0 ≤ transferOperator f := by
  intro g
  change 0 ≤ (1/2 : ℝ)*(affineOperator dyadicLeft f g+affineOperator dyadicRight f g)
  exact mul_nonneg (by norm_num) (add_nonneg (affineOperator_pos _ f hf g) (affineOperator_pos _ f hf g))


-- @@ L139-142 verbatim
lemma transferOperator_identityClass (f : C(DiskClass,ℝ)) : transferOperator f identityClass = f identityClass := by
  change (1/2 : ℝ)*(affineOperator dyadicLeft f identityClass+affineOperator dyadicRight f identityClass) = _
  simp only [affineOperator_apply,classWeight_identityClass,reroot_identityClass,one_mul]
  ring


-- @@ L144-147 verbatim
lemma transferOperator_pow_identityClass (n : ℕ) : (transferOperator^n) 1 identityClass = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [pow_succ',mul_apply_eq_comp,transferOperator_identityClass] using ih


-- @@ L149-152 verbatim
lemma transferOperator_pow_norm_ge_one (n : ℕ) : 1 ≤ ‖transferOperator^n‖ := by
  have hv := (ContinuousMap.norm_coe_le_norm ((transferOperator^n) 1) identityClass).trans
    ((transferOperator^n).le_opNorm 1)
  simpa only [transferOperator_pow_identityClass,norm_one,mul_one] using hv


-- @@ L154-161 verbatim
lemma diskCayley_norm_sq_identity {z : ℂ} (hz : z ∈ halfPlane) :
    (1-‖diskCayley z‖^2)*‖z+Complex.I‖^2 = 4*z.im := by
  have hd : ‖z+Complex.I‖ ≠ 0 := norm_ne_zero_iff.mpr (cayley_den_ne_zero hz)
  rw [diskCayley,norm_div,div_pow]
  field_simp
  rw [Complex.sq_norm,Complex.sq_norm]
  simp [Complex.normSq_apply]
  ring


-- @@ L163-168 verbatim
lemma classFun_deriv_norm (g : DiskClass) (z : halfPlane) :
    ‖deriv (classFun g) z‖ = 4*‖deriv (diskExtend g.1) (diskCayley z)‖/‖z.val+Complex.I‖^2 := by
  have hd := (hasDerivAt_diskToHalf g.2.1.1 z.2).deriv
  rw [classFun]
  rw [hd,norm_div,norm_mul,norm_neg,norm_pow]
  norm_num


-- @@ L170-173 verbatim
lemma classFun_reciprocal_norm (g : DiskClass) (z : halfPlane) :
    ‖reciprocalDeriv (classFun g) z‖ = ‖z.val+Complex.I‖^2/
      (4*‖deriv (diskExtend g.1) (diskCayley z)‖) := by
  rw [reciprocalDeriv,norm_inv,classFun_deriv_norm,inv_div]


-- @@ L175-202 verbatim
lemma classFun_reciprocal_bound (g : DiskClass) (z : halfPlane) :
    ‖reciprocalDeriv (classFun g) z‖ ≤ ‖z.val+Complex.I‖^4/z.val.im := by
  let r := ‖diskCayley z‖
  let D := ‖z.val+Complex.I‖^2
  let a := ‖deriv (diskExtend g.1) (diskCayley z)‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r < 1 := by simpa [r,disk] using diskCayley_maps z.2
  have hD0 : 0 < D := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (cayley_den_ne_zero z.2))
  have ha0 : 0 < a := norm_pos_iff.mpr (univalent_deriv_ne_zero Metric.isOpen_ball g.2.1 (diskCayley_maps z.2))
  have he : (1-r^2)*D = 4*z.val.im := diskCayley_norm_sq_identity z.2
  have hlo : (1-r)/(1+r)^3 ≤ a := (schlicht_deriv_bounds g.2 (diskCayley_maps z.2)).1
  have hden : 0 < (1+r)^3 := pow_pos (by linarith) 3
  have h8 : (1+r)^3 ≤ 8 := by nlinarith [sq_nonneg (1-r),sq_nonneg r,mul_nonneg hr0 (sq_nonneg (1-r))]
  have hl : 1-r ≤ 8*a := by
    have hh := (div_le_iff₀ hden).mp hlo
    nlinarith [mul_le_mul_of_nonneg_left h8 ha0.le]
  have hD : 2*z.val.im ≤ (1-r)*D := by
    have hh : (1-r^2) ≤ 2*(1-r) := by nlinarith [sq_nonneg (1-r)]
    nlinarith [mul_le_mul_of_nonneg_right hh hD0.le]
  have hDa : z.val.im ≤ 4*a*D := by
    have hh := mul_le_mul_of_nonneg_right hl hD0.le
    nlinarith
  rw [classFun_reciprocal_norm]
  change D/(4*a) ≤ ‖z.val+Complex.I‖^4/z.val.im
  rw [div_le_div_iff₀ (by positivity : 0 < 4*a) z.2]
  have hh := mul_le_mul_of_nonneg_right hDa hD0.le
  dsimp [D] at *
  nlinarith


-- @@ L204-218 verbatim
lemma classFun_strip_bound (g : DiskClass) {C₀ : ℝ} (hC : 0 ≤ C₀) (z : halfPlane)
    (hx : |z.val.re| ≤ C₀) (hy : z.val.im ≤ 1) :
    ‖reciprocalDeriv (classFun g) z‖ ≤ (C₀^2+4)^2/z.val.im := by
  apply (classFun_reciprocal_bound g z).trans
  apply div_le_div_of_nonneg_right _ z.2.le
  have hD : ‖z.val+Complex.I‖^2 = z.val.re^2+(z.val.im+1)^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  have hxr : z.val.re^2 ≤ C₀^2 := by nlinarith [sq_abs z.val.re,(sq_le_sq₀ (abs_nonneg _) hC).mpr hx]
  have hDle : ‖z.val+Complex.I‖^2 ≤ C₀^2+4 := by
    have hz0 : 0 < z.val.im := z.2
    rw [hD]
    nlinarith [mul_nonneg hz0.le (sub_nonneg.mpr hy)]
  nlinarith [sq_nonneg (‖z.val+Complex.I‖^2-(C₀^2+4))]


-- @@ L220-224 verbatim
lemma classFun_strip_bound_two (g : DiskClass) (z : halfPlane)
    (hx : |z.val.re| ≤ 2) (hy : z.val.im ≤ 1) :
    ‖reciprocalDeriv (classFun g) z‖ ≤ 64/z.val.im := by
  convert classFun_strip_bound g (by norm_num : (0 : ℝ) ≤ 2) z hx hy using 1
  norm_num


-- @@ L226-226 verbatim
end Brennan


-- @@ L228-228 verbatim
end


-- @@ L230-230 verbatim
end OAI
