import OAI.Geometry.ProjectionBodies.RankContinuity


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open Set MeasureTheory Metric Filter Topology

-- @@ L7-7 verbatim
open scoped NNReal RealInnerProductSpace

-- @@ L8-8 verbatim
namespace PettyProjection

-- @@ L9-9 verbatim
open Spherical (Sphere objective)

-- @@ L10-10 verbatim
namespace RelativeGauge

-- @@ L11-11 verbatim
variable {n : ℕ} [NeZero n] {μ : Measure (Space n)}


-- @@ L13-13 verbatim
abbrev NonzeroMap (n : ℕ) := {A : Space n →L[ℝ] Space n // LinearMap.range A.toLinearMap≠⊥}


-- @@ L15-18 verbatim
def optimizer (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x) (b : Bool) (A : NonzeroMap n) :
    RelativeGauge (LinearMap.range A.val.toLinearMap) :=
  (exists_minimizer (norm_integrable_map hμ A) A.property (cosine_map_pos hμ hq A) b).choose


-- @@ L20-23 verbatim
lemma optimizer_normalized (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x) (b : Bool) (A : NonzeroMap n) :
    supportFunctional (μ.map A.val) (optimizer hμ hq b A).body=1 :=
  (exists_minimizer (norm_integrable_map hμ A) A.property (cosine_map_pos hμ hq A) b).choose_spec.1


-- @@ L25-29 verbatim
lemma optimizer_minimal (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x) (b : Bool) (A : NonzeroMap n)
    (g : RelativeGauge (LinearMap.range A.val.toLinearMap)) (hg : supportFunctional (μ.map A.val) g.body=1) :
    objective b (optimizer hμ hq b A).toSeminorm≤ objective b g.toSeminorm :=
  (exists_minimizer (norm_integrable_map hμ A) A.property (cosine_map_pos hμ hq A) b).choose_spec.2 g hg


-- @@ L31-35 verbatim
def optimizerSphere (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x) (b : Bool) (A : NonzeroMap n) :
    BoundedContinuousFunction (Sphere n) ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨fun u => optimizer hμ hq b A u,
    (Spherical.seminorm_continuous n _).comp continuous_subtype_val⟩


-- @@ L37-53 verbatim
/-- Rank-continuity of the actual canonical variational optimizer. The
codomain carries the uniform norm on the entire ambient sphere. -/
theorem optimizerSphere_continuous (hμ : Integrable (fun x : Space n => ‖x‖) μ)
    (hq : ∀ x : Space n,x≠0 → 0< cosineSeminorm μ hμ x) (b : Bool) :
    Continuous (optimizerSphere hμ hq b) := by
  apply continuous_iff_seqContinuous.mpr
  intro Aj A hA
  apply Filter.tendsto_of_subseq_tendsto
  intro ns hns
  have hAv : Tendsto (fun i => (Aj (ns i)).val) atTop (𝓝 A.val) :=
    (continuous_subtype_val.tendsto A).comp (hA.comp hns)
  obtain ⟨φ,_,ht⟩ := minimizers_subsequence hμ hq hAv A.property (fun i => (Aj (ns i)).property) b
    (fun i => optimizer hμ hq b (Aj (ns i))) (fun i => optimizer_normalized hμ hq b (Aj (ns i)))
    (fun i => optimizer_minimal hμ hq b (Aj (ns i))) (optimizer hμ hq b A)
    (optimizer_normalized hμ hq b A) (optimizer_minimal hμ hq b A)
  refine ⟨φ,BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mpr ?_⟩
  exact ht


-- @@ L55-55 verbatim
end RelativeGauge

-- @@ L56-56 verbatim
end PettyProjection

-- @@ L57-57 verbatim
end


-- @@ L59-59 verbatim
noncomputable section

-- @@ L60-60 verbatim
open Set MeasureTheory Metric Filter Topology Function

-- @@ L61-61 verbatim
open scoped ENNReal NNReal RealInnerProductSpace

-- @@ L62-62 verbatim
namespace PettyProjection

-- @@ L63-63 verbatim
open Spherical (Sphere norm_coe surface sigma mean)


-- @@ L65-76 verbatim
lemma gaussian_real_second_moment :
    (∫ t : ℝ,t^2*Real.exp (-(t^2)))=(1/2:ℝ)*(∫ t : ℝ,Real.exp (-(t^2))) := by
  have h0 := integral_fun_norm_addHaar (volume : Measure ℝ) (fun r : ℝ => Real.exp (-(r^2)))
  have h2 := integral_fun_norm_addHaar (volume : Measure ℝ) (fun r : ℝ => r^2*Real.exp (-(r^2)))
  simp only [Module.finrank_self,Nat.sub_self,pow_zero,one_smul,Real.norm_eq_abs,sq_abs] at h0 h2
  have he : (∫ r in Ioi (0:ℝ),Real.exp (-(r^2)))=gaussianRadial 0 := by simp [gaussianRadial]
  change _=volume.real (ball (0:ℝ) 1)*gaussianRadial 2 at h2
  rw [he] at h0
  change _=volume.real (ball (0:ℝ) 1)*gaussianRadial 0 at h0
  rw [h2,h0,show (2:ℕ)=0+2 from rfl,gaussianRadial_add_two]
  norm_num
  ring


-- @@ L78-85 verbatim
lemma seminorm_add_kernel {n : ℕ} (g : Seminorm ℝ (Space n)) {e : Space n}
    (he : g e=0) (x : Space n) (t : ℝ) : g (x+t • e)=g x := by
  have h1 := map_add_le_add g x (t • e)
  have h2 := map_add_le_add g (x+t • e) (-(t • e))
  have hz : g (t • e)=0 := by rw [map_smul_eq_mul,he,mul_zero]
  rw [hz,add_zero] at h1
  rw [add_neg_cancel_right,map_neg_eq_map,hz,add_zero] at h2
  exact le_antisymm h1 h2


-- @@ L87-91 verbatim
lemma gaussian_shadow_norm {n : ℕ} (e : Sphere n) (z : perpendicular (e:Space n)) (t : ℝ) :
    ‖(z:Space n)+t • (e:Space n)‖^2=‖z‖^2+t^2 := by
  rw [norm_add_sq_real,inner_smul_right,real_inner_comm,perpendicular_inner,norm_smul,
    Real.norm_eq_abs,mul_pow,norm_coe,one_pow,mul_one,sq_abs]
  simp


-- @@ L93-126 verbatim
/-- Genuine Gaussian independence in a seminorm kernel, proved by the
measure-preserving orthogonal coordinate map and Fubini product integrals. -/
lemma gaussian_kernel_moment {n : ℕ} (g : Seminorm ℝ (Space n)) (k : ℕ)
    (e : Sphere n) (he : g e=0) :
    (∫ x : Space n,g x^k*⟪(e:Space n),x⟫^2*Real.exp (-(‖x‖^2)))=
      (1/2:ℝ)*(∫ x : Space n,g x^k*Real.exp (-(‖x‖^2))) := by
  let F : perpendicular (e:Space n) → ℝ := fun z => g z^k*Real.exp (-(‖z‖^2))
  have he0 : (fun z : perpendicular (e:Space n) × ℝ =>
      g (shadowMeasurableEquiv e z)^k*Real.exp (-(‖shadowMeasurableEquiv e z‖^2)))=
      (fun z => F z.1*Real.exp (-(z.2^2))) := by
    funext z
    change g ((z.1:Space n)+z.2 • (e:Space n))^k*Real.exp (-‖(z.1:Space n)+z.2 • (e:Space n)‖^2)=_
    rw [seminorm_add_kernel g he,gaussian_shadow_norm,neg_add,Real.exp_add]
    dsimp only [F]
    ring
  have he2 : (fun z : perpendicular (e:Space n) × ℝ =>
      g (shadowMeasurableEquiv e z)^k*⟪(e:Space n),shadowMeasurableEquiv e z⟫^2*
        Real.exp (-(‖shadowMeasurableEquiv e z‖^2)))=
      (fun z => F z.1*(z.2^2*Real.exp (-(z.2^2)))) := by
    funext z
    change g ((z.1:Space n)+z.2 • (e:Space n))^k*⟪(e:Space n),(z.1:Space n)+z.2 • (e:Space n)⟫^2*
      Real.exp (-‖(z.1:Space n)+z.2 • (e:Space n)‖^2)=_
    rw [seminorm_add_kernel g he,gaussian_shadow_norm,neg_add,Real.exp_add,
      inner_add_right,perpendicular_inner,inner_smul_right,real_inner_self_eq_norm_sq,norm_coe]
    dsimp only [F]
    ring
  rw [← (shadowMeasurableEquiv_measurePreserving e).integral_comp (shadowMeasurableEquiv e).measurableEmbedding
    (fun x : Space n => g x^k*⟪(e:Space n),x⟫^2*Real.exp (-(‖x‖^2))),
    ← (shadowMeasurableEquiv_measurePreserving e).integral_comp (shadowMeasurableEquiv e).measurableEmbedding
    (fun x : Space n => g x^k*Real.exp (-(‖x‖^2)))]
  rw [he0,he2,Measure.volume_eq_prod,
    integral_prod_mul F (fun t : ℝ => t^2*Real.exp (-(t^2))),
    integral_prod_mul F (fun t : ℝ => Real.exp (-(t^2))),gaussian_real_second_moment]
  ring


-- @@ L128-152 verbatim
/-- The boundary moment ratio, for every seminorm and every natural
homogeneity degree, including all singular and nonsmooth cases. -/
theorem sphere_kernel_moment {n : ℕ} [NeZero n] (g : Seminorm ℝ (Space n)) (k : ℕ)
    (e : Sphere n) (he : g e=0) :
    ((n:ℝ)+k)*mean (fun u : Sphere n => g u^k*⟪(e:Space n),(u:Space n)⟫^2)=
      mean (fun u : Sphere n => g u^k) := by
  have hh0 : ∀ r : ℝ,0<r → ∀ x : Space n,g (r • x)^k=r^k*g x^k := by
    intro r hr x
    rw [map_smul_eq_mul,Real.norm_of_nonneg hr.le,mul_pow]
  have hh2 : ∀ r : ℝ,0<r → ∀ x : Space n,g (r • x)^k*⟪(e:Space n),r • x⟫^2=
      r^(k+2)*(g x^k*⟪(e:Space n),x⟫^2) := by
    intro r hr x
    rw [hh0 r hr,inner_smul_right,mul_pow,pow_add]
    ring
  have hG := gaussian_kernel_moment g k e he
  rw [homogeneous_gaussian_integral (k+2) _ hh2,homogeneous_gaussian_integral k _ hh0] at hG
  rw [show n-1+(k+2)=(n-1+k)+2 by omega,gaussianRadial_add_two] at hG
  have hn : ((n-1+k:ℕ):ℝ)+1=(n:ℝ)+k := by
    have hh : n-1+k+1=n+k := by have := NeZero.pos n;omega
    exact_mod_cast hh
  rw [hn] at hG
  have hc : (n:ℝ)*kappa n*gaussianRadial (n-1+k)≠0 :=
    mul_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne n)) (kappa_pos n).ne') (gaussianRadial_pos _).ne'
  apply (mul_left_cancel₀ hc)
  nlinarith only [hG]


-- @@ L154-154 verbatim
end PettyProjection

-- @@ L155-155 verbatim
end


-- @@ L157-157 verbatim
noncomputable section

-- @@ L158-158 verbatim
open Set MeasureTheory Metric Filter Topology

-- @@ L159-159 verbatim
open scoped RealInnerProductSpace

-- @@ L160-160 verbatim
namespace PettyProjection.Position

-- @@ L161-161 verbatim
abbrev Mat (n : ℕ) := EuclideanSpace ℝ (Fin n × Fin n)

-- @@ L162-162 verbatim
variable {n : ℕ}

-- @@ L163-163 verbatim
def matrix (A : Mat n) : Matrix (Fin n) (Fin n) ℝ := fun i j => A (i,j)

-- @@ L164-164 verbatim
def op (A : Mat n) : Space n →L[ℝ] Space n := (matrix A).toEuclideanLin.toContinuousLinearMap

-- @@ L165-165 verbatim
def tr (A : Mat n) : ℝ := ∑ i,A (i,i)

-- @@ L166-166 verbatim
def quad (A : Mat n) (x : Space n) : ℝ := ⟪x,op A x⟫

-- @@ L167-167 verbatim
def Symmetric (A : Mat n) : Prop := ∀ i j,A (i,j)=A (j,i)

-- @@ L168-168 verbatim
def PSD (A : Mat n) : Prop := Symmetric A ∧ ∀ x,0≤quad A x

-- @@ L169-169 verbatim
def domain (n : ℕ) : Set (Mat n) := {A | PSD A ∧ tr A=1}


-- @@ L171-171 verbatim
lemma op_apply (A : Mat n) (x : Space n) (i : Fin n) : op A x i=∑ j,A (i,j)*x j := rfl

-- @@ L172-176 verbatim
lemma quad_eq (A : Mat n) (x : Space n) : quad A x=∑ i,∑ j,A (i,j)*x i*x j := by
  simp only [quad,EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,op_apply,Finset.sum_mul]
  congr 1; funext i
  apply Finset.sum_congr rfl
  intro j _; ring

-- @@ L177-182 verbatim
lemma op_continuous : Continuous (op : Mat n → Space n →L[ℝ] Space n) := by
  let L : Mat n →ₗ[ℝ] (Space n →L[ℝ] Space n) :=
    { toFun := op
      map_add' := by intro A B; ext x i; simp [op_apply,add_mul,Finset.sum_add_distrib]
      map_smul' := by intro a A; ext x i; simp [op_apply,Finset.mul_sum,mul_assoc] }
  exact L.continuous_of_finiteDimensional

-- @@ L183-184 verbatim
lemma quad_continuous : Continuous (fun p : Mat n × Space n => quad p.1 p.2) := by
  exact continuous_snd.inner (op_continuous.fst'.clm_apply continuous_snd)

-- @@ L185-187 verbatim
lemma tr_continuous : Continuous (tr : Mat n → ℝ) := by
  unfold tr
  fun_prop

-- @@ L188-189 verbatim
lemma quad_add (A B : Mat n) (x : Space n) : quad (A+B) x=quad A x+quad B x := by
  simp [quad_eq,add_mul,Finset.sum_add_distrib]

-- @@ L190-191 verbatim
lemma quad_smul (a : ℝ) (A : Mat n) (x : Space n) : quad (a • A) x=a*quad A x := by
  simp [quad_eq,mul_assoc,Finset.mul_sum]

-- @@ L192-193 verbatim
lemma quad_sub (A B : Mat n) (x : Space n) : quad (A-B) x=quad A x-quad B x := by
  simp [quad_eq,sub_mul,Finset.sum_sub_distrib]

-- @@ L194-197 verbatim
lemma symmetric_op {A : Mat n} (hA : Symmetric A) : (op A).toLinearMap.IsSymmetric := by
  apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
  ext i j
  exact hA j i

-- @@ L198-223 verbatim
lemma op_kernel_of_quad_zero {A : Mat n} (hA : PSD A) {x : Space n} (hx : quad A x=0) : op A x=0 := by
  have hs := symmetric_op hA.1
  have hxy (y : Space n) : ⟪y,op A x⟫=0 := by
    have hh (t : ℝ) := hA.2 (x+t • y)
    have he (t : ℝ) : quad A (x+t • y)=2*t*⟪y,op A x⟫+t^2*quad A y := by
      simp only [quad,map_add,map_smul,inner_add_left,inner_add_right,inner_smul_left,
        inner_smul_right,conj_trivial] at *
      have hi : ⟪x,op A y⟫=⟪y,op A x⟫ := by
        have h := hs x y
        change ⟪op A x,y⟫=⟪x,op A y⟫ at h
        rw [← h,real_inner_comm]
      rw [hx,hi]; ring
    simp_rw [he] at hh
    let a := quad A y
    let b := ⟪y,op A x⟫
    have ha : 0≤a := hA.2 y
    have han : a+1≠0 := by linarith
    have hv := mul_nonneg (hh (-b/(a+1))) (sq_nonneg (a+1))
    have heval : (2*(-b/(a+1))*b+(-b/(a+1))^2*a)*(a+1)^2= -b^2*(a+2) := by
      field_simp
      ring
    change 0≤(2*(-b/(a+1))*b+(-b/(a+1))^2*a)*(a+1)^2 at hv
    rw [heval] at hv
    change b=0
    nlinarith [sq_nonneg b,mul_nonneg ha (sq_nonneg b)]
  exact inner_self_eq_zero.mp (hxy (op A x))


-- @@ L225-233 verbatim
lemma symmetric_closed : IsClosed {A : Mat n | Symmetric A} := by
  have he : {A : Mat n | Symmetric A}=⋂ i : Fin n,⋂ j : Fin n,{A : Mat n | A (i,j)=A (j,i)} := by
    ext A; simp [Symmetric]
  rw [he]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  exact isClosed_eq (by fun_prop) (by fun_prop)

-- @@ L234-237 verbatim
lemma quad_nonneg_closed (x : Space n) : IsClosed {A : Mat n | 0≤quad A x} := by
  have hc : Continuous (fun A : Mat n => quad A x) :=
    by simp_rw [quad_eq]; fun_prop
  exact isClosed_le (continuous_const : Continuous (fun _ : Mat n => (0:ℝ))) hc

-- @@ L238-244 verbatim
lemma psd_closed : IsClosed {A : Mat n | PSD A} := by
  have hq : IsClosed (⋂ x : Space n,{A : Mat n | 0≤quad A x}) :=
    isClosed_iInter (fun x : Space n => quad_nonneg_closed x)
  have h := (symmetric_closed (n := n)).inter hq
  convert h using 1
  ext A
  simp only [mem_inter_iff,mem_ofPred_eq,mem_iInter,PSD]

-- @@ L245-246 verbatim
lemma domain_closed : IsClosed (domain n) :=
  (psd_closed (n := n)).inter (isClosed_eq (tr_continuous (n := n)) continuous_const)

-- @@ L247-259 verbatim
lemma domain_convex : Convex ℝ (domain n) := by
  intro A hA B hB a b ha hb hab
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro i j
    change a*A (i,j)+b*B (i,j)=a*A (j,i)+b*B (j,i)
    rw [hA.1.1 i j,hB.1.1 i j]
  · intro x
    rw [quad_add,quad_smul,quad_smul]
    exact add_nonneg (mul_nonneg ha (hA.1.2 x)) (mul_nonneg hb (hB.1.2 x))
  · change (∑ i,(a*A (i,i)+b*B (i,i)))=1
    rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
    change a*tr A+b*tr B=1
    rw [hA.2,hB.2,mul_one,mul_one,hab]


-- @@ L261-262 verbatim
lemma quad_basis (A : Mat n) (i : Fin n) : quad A (EuclideanSpace.single i 1)=A (i,i) := by
  simp [quad_eq]

-- @@ L263-267 verbatim
lemma quad_basis_add (A : Mat n) (i j : Fin n) (a b : ℝ) :
    quad A (a • EuclideanSpace.single i 1+b • EuclideanSpace.single j 1)=
      a^2*A (i,i)+a*b*(A (i,j)+A (j,i))+b^2*A (j,j) := by
  simp [quad_eq,add_mul,mul_add,Finset.sum_add_distrib]
  ring

-- @@ L268-276 verbatim
lemma domain_entry_bound {A : Mat n} (hA : A∈domain n) (i j : Fin n) : |A (i,j)|≤1 := by
  have hd (i : Fin n) : 0≤A (i,i) := by simpa only [quad_basis] using hA.1.2 (EuclideanSpace.single i 1)
  have hd1 (i : Fin n) : A (i,i)≤1 := by
    rw [← hA.2]
    exact Finset.single_le_sum (fun j _ => hd j) (Finset.mem_univ i)
  have hp := hA.1.2 ((1:ℝ) • EuclideanSpace.single i 1+(1:ℝ) • EuclideanSpace.single j 1)
  have hm := hA.1.2 ((1:ℝ) • EuclideanSpace.single i 1+(-1:ℝ) • EuclideanSpace.single j 1)
  rw [quad_basis_add,hA.1.1 j i] at hp hm
  exact abs_le.mpr ⟨by nlinarith [hd1 i,hd1 j],by nlinarith [hd1 i,hd1 j]⟩

-- @@ L277-290 verbatim
lemma domain_compact : IsCompact (domain n) := by
  apply (isCompact_closedBall (0:Mat n) (n:ℝ)).of_isClosed_subset domain_closed
  intro A hA
  rw [mem_closedBall,dist_zero_right]
  have hn : (0:ℝ)≤n := Nat.cast_nonneg _
  rw [← sq_le_sq₀ (norm_nonneg A) hn,EuclideanSpace.norm_sq_eq]
  calc
    ∑ i : Fin n × Fin n,‖A i‖^2 ≤ ∑ _ : Fin n × Fin n,(1:ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have hh := domain_entry_bound hA i.1 i.2
      dsimp only [Real.norm_eq_abs]
      nlinarith [abs_nonneg (A i)]
    _ = (n:ℝ)^2 := by simp [sq]

-- @@ L291-304 verbatim
lemma domain_nonempty [NeZero n] : (domain n).Nonempty := by
  let A : Mat n := WithLp.toLp 2 (fun ij => if ij.1=ij.2 then (n:ℝ)⁻¹ else 0)
  refine ⟨A,⟨?_,?_⟩,?_⟩
  · intro i j
    dsimp [A]
    simp only [eq_comm]
  · intro x
    rw [quad_eq]
    dsimp [A]
    simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
    apply Finset.sum_nonneg
    intro i _
    simpa only [sq,mul_assoc] using mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n : (0:ℝ)≤n)) (sq_nonneg (x i))
  · simp [tr,A,NeZero.ne n]

-- @@ L305-313 verbatim
lemma domain_range_ne_bot {A : Mat n} (hA : A∈domain n) : LinearMap.range (op A).toLinearMap≠⊥ := by
  intro h
  have hz : op A=0 := by
    apply ContinuousLinearMap.ext
    intro x
    exact (Submodule.mem_bot ℝ).mp (h ▸ LinearMap.mem_range_self _ x)
  have hdiag (i : Fin n) : A (i,i)=0 := by rw [← quad_basis,quad,hz]; simp
  have : tr A=0 := by simp [tr,hdiag]
  linarith [hA.2]

-- @@ L314-314 verbatim
end PettyProjection.Position

-- @@ L315-315 verbatim
end


-- @@ L317-317 verbatim
noncomputable section

-- @@ L318-318 verbatim
open Set MeasureTheory Metric Filter Topology

-- @@ L319-319 verbatim
open scoped RealInnerProductSpace

-- @@ L320-320 verbatim
namespace PettyProjection.Position

-- @@ L321-321 verbatim
open Spherical (Sphere mean sigma norm_coe continuous_integrable seminorm_continuous)

-- @@ L322-322 verbatim
variable {n : ℕ} [NeZero n]


-- @@ L324-324 verbatim
def identity (n : ℕ) : Mat n := WithLp.toLp 2 (fun ij => if ij.1=ij.2 then 1 else 0)

-- @@ L325-327 verbatim
def momentField (g : Seminorm ℝ (Space n)) (k : ℕ) : Mat n :=
  WithLp.toLp 2 (fun ij => mean (fun u : Sphere n => g u^k*(u:Space n) ij.1*(u:Space n) ij.2)/
    mean (fun u : Sphere n => g u^k)-(if ij.1=ij.2 then 1 else 0)/(n:ℝ))


-- @@ L329-337 verbatim
lemma mean_power_pos (g : Seminorm ℝ (Space n)) (hg : g≠0) (k : ℕ) :
    0 < mean (fun u : Sphere n => g u^k) := by
  obtain ⟨R,e,hR,_,hb⟩ := Spherical.seminorm_coordinate_minorant g hg
  have he := hb e
  simp only [real_inner_self_eq_norm_sq,norm_coe,one_pow,abs_one,mul_one] at he
  have hc : Continuous (fun u : Sphere n => g u^k) := ((seminorm_continuous n g).comp continuous_subtype_val).pow k
  apply integral_pos_of_integrable_nonneg_nonzero (x := e) hc (continuous_integrable hc)
    (fun u => pow_nonneg (apply_nonneg g (u:Space n)) k)
  exact (pow_pos (hR.trans_le he) k).ne'


-- @@ L339-345 verbatim
omit [NeZero n] in
lemma field_symmetric (g : Seminorm ℝ (Space n)) (k : ℕ) : Symmetric (momentField g k) := by
  intro i j
  change mean _ / _ - _ / _=mean _ / _ - _ / _
  congr 2
  · congr 1; funext u; ring
  · simp only [eq_comm]


-- @@ L347-364 verbatim
lemma field_trace (g : Seminorm ℝ (Space n)) (hg : g≠0) (k : ℕ) : tr (momentField g k)=0 := by
  have hc (i : Fin n) : Continuous (fun u : Sphere n => g u^k*(u:Space n) i*(u:Space n) i) := by
    exact (((seminorm_continuous n g).comp continuous_subtype_val).pow k).mul (by fun_prop) |>.mul (by fun_prop)
  have hsum : (∑ i : Fin n,mean (fun u : Sphere n => g u^k*(u:Space n) i*(u:Space n) i))=
      mean (fun u : Sphere n => g u^k) := by
    rw [← Spherical.mean_sum _ (fun i _ => hc i)]
    congr 1
    funext u
    have hh := EuclideanSpace.real_norm_sq_eq (u:Space n)
    rw [norm_coe,one_pow] at hh
    calc
      (∑ i : Fin n,g u^k*(u:Space n) i*(u:Space n) i)=g u^k*(∑ i : Fin n,(u:Space n) i^2) := by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
      _ = g u^k := by rw [← hh,mul_one]
  simp only [tr,momentField,ite_true]
  change (∑ i : Fin n,(mean (fun u : Sphere n => g u^k*(u:Space n) i*(u:Space n) i)/mean (fun u : Sphere n => g u^k)-1/(n:ℝ)))=0
  rw [Finset.sum_sub_distrib,← Finset.sum_div,hsum,div_self (mean_power_pos g hg k).ne']
  simp [NeZero.ne n]


-- @@ L366-404 verbatim
lemma field_quad (g : Seminorm ℝ (Space n)) (k : ℕ) (x : Space n) :
    quad (momentField g k) x=mean (fun u : Sphere n => g u^k*⟪x,(u:Space n)⟫^2)/
      mean (fun u : Sphere n => g u^k)-‖x‖^2/(n:ℝ) := by
  have hc (i j : Fin n) : Continuous (fun u : Sphere n =>
      g u^k*(u:Space n) i*(u:Space n) j*x i*x j) := by
    exact (((((seminorm_continuous n g).comp continuous_subtype_val).pow k).mul (by fun_prop)).mul (by fun_prop)).mul continuous_const |>.mul continuous_const
  have hnum : (∑ i : Fin n,∑ j : Fin n,
      mean (fun u : Sphere n => g u^k*(u:Space n) i*(u:Space n) j)*x i*x j)=
      mean (fun u : Sphere n => g u^k*⟪x,(u:Space n)⟫^2) := by
    have hi (i : Fin n) : (∑ j : Fin n,mean (fun u : Sphere n => g u^k*(u:Space n) i*(u:Space n) j)*x i*x j)=
        mean (fun u : Sphere n => ∑ j : Fin n,g u^k*(u:Space n) i*(u:Space n) j*x i*x j) := by
      simp_rw [mean,← integral_mul_const]
      exact (integral_finsetSum _ (fun j _ => continuous_integrable (hc i j))).symm
    simp_rw [hi]
    rw [← Spherical.mean_sum _ (fun i _ => continuous_finsetSum _ (fun j _ => hc i j))]
    congr 1
    funext u
    simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial,sq,Finset.sum_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [quad_eq]
  simp only [momentField,sub_mul,Finset.sum_sub_distrib]
  have hdiv : (∑ i : Fin n,∑ j : Fin n,
      mean (fun u : Sphere n => g u^k*(u:Space n) i*(u:Space n) j)/mean (fun u : Sphere n => g u^k)*x i*x j)=
      mean (fun u : Sphere n => g u^k*⟪x,(u:Space n)⟫^2)/mean (fun u : Sphere n => g u^k) := by
    simp_rw [div_mul_eq_mul_div,← Finset.sum_div]
    rw [hnum]
  rw [hdiv]
  congr 1
  simp only [ite_div,zero_div,ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
  rw [EuclideanSpace.real_norm_sq_eq]
  rw [Finset.sum_div]
  simp only [one_div,sq]
  apply Finset.sum_congr rfl
  intro i _
  ring


-- @@ L406-417 verbatim
lemma field_kernel {g : Seminorm ℝ (Space n)} (hg : g≠0) {k : ℕ} (hk : 0<k)
    (e : Sphere n) (he : g e=0) : quad (momentField g k) e<0 := by
  rw [field_quad,norm_coe,one_pow]
  have hm := sphere_kernel_moment g k e he
  have hp := mean_power_pos g hg k
  have hn : (0:ℝ)<n := Nat.cast_pos.mpr (NeZero.pos n)
  have hk' : (0:ℝ)<k := Nat.cast_pos.mpr hk
  apply sub_neg.mpr
  apply (div_lt_iff₀ hp).mpr
  rw [one_div,mul_comm,← div_eq_mul_inv,lt_div_iff₀ hn]
  have hnon : 0 < mean (fun u : Sphere n => g u^k*⟪(e:Space n),(u:Space n)⟫^2) := by nlinarith
  nlinarith

-- @@ L418-418 verbatim
end PettyProjection.Position

-- @@ L419-419 verbatim
end


-- @@ L421-421 verbatim
end OAI
