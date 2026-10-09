import OAI.GroupTheory.Hyperbolic.Chains


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace Release075

-- @@ L6-6 verbatim
namespace FreeChain

-- @@ L7-7 verbatim
attribute [local instance] Classical.propDecidable Classical.decEq

-- @@ L8-8 verbatim
variable {A G : Type} [Group G]


-- @@ L10-12 verbatim
@[simp] theorem shift_apply (g : G) (c : FreeChain A G) (a : A) (x : G) :
    chainShift g c (a,x) = c (a,g⁻¹*x) := by
  simp [chainShift,Finsupp.domLCongr_apply]


-- @@ L14-15 verbatim
@[simp] theorem shift_one (c : FreeChain A G) : chainShift (1 : G) c = c := by
  ext ⟨a,x⟩; simp


-- @@ L17-19 verbatim
@[simp] theorem shift_mul (g h : G) (c : FreeChain A G) :
    chainShift (g*h) c = chainShift g (chainShift h c) := by
  ext ⟨a,x⟩; simp [mul_assoc]


-- @@ L21-21 verbatim
abbrev RightCosets (H : Subgroup G) := Quotient (QuotientGroup.rightRel H)


-- @@ L23-23 verbatim
def coset (H : Subgroup G) (x : G) : RightCosets H := Quotient.mk _ x


-- @@ L25-27 verbatim
noncomputable def cosetCoord (H : Subgroup G) (x : G) : H :=
  ⟨x * (coset H x).out⁻¹, QuotientGroup.rightRel_apply.mp
    (Quotient.exact (Quotient.out_eq (coset H x)))⟩


-- @@ L29-34 verbatim
@[simp] theorem coset_mul (H : Subgroup G) (h : H) (x : G) :
    coset H ((h : G)*x) = coset H x := by
  apply Quotient.sound
  change QuotientGroup.rightRel H ((h:G)*x) x
  rw [QuotientGroup.rightRel_apply]
  simp [mul_inv_rev]


-- @@ L36-47 verbatim
noncomputable def rightCosetEquiv (H : Subgroup G) : G ≃ RightCosets H × H where
  toFun x := (coset H x,cosetCoord H x)
  invFun q := q.2 * q.1.out
  left_inv x := by simp [cosetCoord]
  right_inv q := by
    rcases q with ⟨q,h⟩
    have hc : coset H ((h:G)*q.out) = q := by
      rw [coset_mul]; exact Quotient.out_eq q
    apply Prod.ext hc
    apply Subtype.ext
    simp only [cosetCoord, hc]
    simp


-- @@ L49-54 verbatim
noncomputable def chainCosetEquiv (H : Subgroup G) :
    FreeChain A G ≃ₗ[ℤ] (A × RightCosets H) →₀ MonoidAlgebra ℤ H :=
  (Finsupp.domLCongr ((Equiv.prodCongr (Equiv.refl A) (rightCosetEquiv H)).trans
    (Equiv.prodAssoc A (RightCosets H) H).symm)).trans
    ((Finsupp.curryLinearEquiv ℤ).trans
      (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv ℤ).symm))


-- @@ L56-59 verbatim
@[simp] theorem chainCosetEquiv_coeff (H : Subgroup G) (c : FreeChain A G)
    (a : A) (q : RightCosets H) (h : H) :
    ((chainCosetEquiv H c) (a,q)).coeff h = c (a,(h:G)*q.out) := by
  rfl


-- @@ L61-69 verbatim
@[simp] theorem chainCosetEquiv_shift (H : Subgroup G) (h : H) (c : FreeChain A G)
    (i : A × RightCosets H) :
    chainCosetEquiv H (chainShift (h:G) c) i =
      Representation.leftRegular ℤ H h (chainCosetEquiv H c i) := by
  apply MonoidAlgebra.ext
  ext k
  rcases i with ⟨a,q⟩
  simp only [chainCosetEquiv_coeff,shift_apply,Representation.coeff_ofMulAction]
  simp [mul_assoc]


-- @@ L71-72 verbatim
noncomputable def subgroupNorm (H : Subgroup G) [Fintype H] :
    FreeChain A G →ₗ[ℤ] FreeChain A G := ∑ h : H, (chainShift (h:G)).toLinearMap


-- @@ L74-82 verbatim
@[simp] theorem chainCosetEquiv_norm (H : Subgroup G) [Fintype H] (c : FreeChain A G)
    (i : A × RightCosets H) :
    chainCosetEquiv H (subgroupNorm H c) i =
      (Representation.leftRegular ℤ H).norm (chainCosetEquiv H c i) := by
  simp only [subgroupNorm,LinearMap.sum_apply,map_sum,Representation.norm]
  rw [Finsupp.coe_finsetSum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro h _
  exact chainCosetEquiv_shift H h c i


-- @@ L84-84 verbatim
end FreeChain

-- @@ L85-85 verbatim
end Release075


-- @@ L87-87 verbatim
namespace Release075

-- @@ L88-88 verbatim
open CategoryTheory

-- @@ L89-89 verbatim
attribute [local instance] Classical.propDecidable Classical.decEq


-- @@ L91-102 verbatim
private theorem finsupp_preimages {J M N : Type} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (f : M →ₗ[ℤ] N) (c : J →₀ N)
    (h : ∀ i, ∃ b, f b = c i) : ∃ b : J →₀ M, ∀ i, f (b i) = c i := by
  choose b hb using h
  let w : J →₀ M := Finsupp.onFinset c.support
    (fun i => if i ∈ c.support then b i else 0)
    (by intro i; split_ifs <;> simp_all)
  refine ⟨w,fun i => ?_⟩
  change f (if i ∈ c.support then b i else 0) = c i
  split_ifs with hi
  · exact hb i
  · simpa only [map_zero] using (Finsupp.notMem_support_iff.mp hi).symm


-- @@ L104-112 verbatim
private theorem regular_invariant_norm {H : Type} [CommGroup H] [Fintype H]
    (g : H) (hg : ∀ x, x ∈ Subgroup.zpowers g) (c : MonoidAlgebra ℤ H)
    (hc : Representation.leftRegular ℤ H g c = c) :
    ∃ b, (Representation.leftRegular ℤ H).norm b = c := by
  have hm : c ∈ LinearMap.ker
      (Rep.applyAsHom (Rep.leftRegular ℤ H) g - 𝟙 _).hom.toLinearMap := by
    simpa [Rep.sub_hom,Rep.applyAsHom,sub_eq_zero] using hc
  rw [← Rep.FiniteCyclicGroup.leftRegular.range_norm_eq_ker_applyAsHom_sub ℤ g hg] at hm
  exact hm


-- @@ L114-121 verbatim
private theorem regular_norm_zero {H : Type} [CommGroup H] [Fintype H]
    (g : H) (hg : ∀ x, x ∈ Subgroup.zpowers g) (c : MonoidAlgebra ℤ H)
    (hc : (Representation.leftRegular ℤ H).norm c = 0) :
    ∃ b, Representation.leftRegular ℤ H g b - b = c := by
  have hm : c ∈ LinearMap.ker (Rep.leftRegular ℤ H).norm.hom.toLinearMap := hc
  rw [← Rep.FiniteCyclicGroup.leftRegular.range_applyAsHom_sub_eq_ker_norm ℤ g hg] at hm
  obtain ⟨b,hb⟩ := hm
  exact ⟨b, by simpa [Rep.sub_hom,Rep.applyAsHom] using hb⟩


-- @@ L123-123 verbatim
namespace FreeChain

-- @@ L124-125 verbatim
variable {A G : Type} [Group G] (H : Subgroup G) [Fintype H] [IsCyclic H]
    (g : H) (hg : ∀ x, x ∈ Subgroup.zpowers g)


-- @@ L127-140 verbatim
include hg in
theorem invariant_is_norm (c : FreeChain A G) (hc : chainShift (g:G) c = c) :
    ∃ b, subgroupNorm H b = c := by
  let : CommGroup H := IsCyclic.commGroup
  have hi (i : A × RightCosets H) : Representation.leftRegular ℤ H g
      (chainCosetEquiv H c i) = chainCosetEquiv H c i := by
    rw [← chainCosetEquiv_shift,hc]
  obtain ⟨b,hb⟩ := finsupp_preimages (Representation.leftRegular ℤ H).norm
    (chainCosetEquiv H c) (fun i => regular_invariant_norm g hg _ (hi i))
  refine ⟨(chainCosetEquiv H).symm b,?_⟩
  apply (chainCosetEquiv H).injective
  apply Finsupp.ext
  intro i
  rw [chainCosetEquiv_norm,LinearEquiv.apply_symm_apply,hb]


-- @@ L142-156 verbatim
include hg in
theorem norm_zero_is_difference (c : FreeChain A G) (hc : subgroupNorm H c = 0) :
    ∃ b, chainShift (g:G) b - b = c := by
  let : CommGroup H := IsCyclic.commGroup
  have hi (i : A × RightCosets H) : (Representation.leftRegular ℤ H).norm
      (chainCosetEquiv H c i) = 0 := by
    rw [← chainCosetEquiv_norm,hc,map_zero,Finsupp.zero_apply]
  obtain ⟨b,hb⟩ := finsupp_preimages (Representation.leftRegular ℤ H g - LinearMap.id)
    (chainCosetEquiv H c) (fun i => regular_norm_zero g hg _ (hi i))
  refine ⟨(chainCosetEquiv H).symm b,?_⟩
  apply (chainCosetEquiv H).injective
  apply Finsupp.ext
  intro i
  rw [map_sub,Finsupp.sub_apply,chainCosetEquiv_shift,LinearEquiv.apply_symm_apply]
  exact hb i


-- @@ L158-158 verbatim
end FreeChain

-- @@ L159-159 verbatim
end Release075


-- @@ L161-161 verbatim
namespace Release075.FreeChain

-- @@ L162-162 verbatim
attribute [local instance] Classical.propDecidable Classical.decEq

-- @@ L163-163 verbatim
variable {A B G : Type} [Group G]


-- @@ L165-166 verbatim
noncomputable def augmentation : FreeChain A G →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ => (1:ℤ))


-- @@ L168-171 verbatim
omit [Group G] in
@[simp] theorem augmentation_single (a : A) (x : G) (n : ℤ) :
    augmentation (Finsupp.single (a,x) n) = n := by
  simp [augmentation]


-- @@ L173-179 verbatim
@[simp] theorem augmentation_shift (g : G) (c : FreeChain A G) :
    augmentation (chainShift g c) = augmentation c := by
  have he : (augmentation (A:=A)).comp (chainShift g).toLinearMap = augmentation := by
    apply Finsupp.lhom_ext
    intro ⟨a,x⟩ n
    simp [chainShift]
  exact LinearMap.congr_fun he c


-- @@ L181-186 verbatim
theorem norm_map (H : Subgroup G) [Fintype H]
    (f : FreeChain A G →ₗ[ℤ] FreeChain B G)
    (hf : ∀ (h : H) c, f (chainShift (h:G) c) = chainShift (h:G) (f c))
    (c : FreeChain A G) : subgroupNorm H (f c) = f (subgroupNorm H c) := by
  simp only [subgroupNorm,LinearMap.sum_apply,map_sum,LinearEquiv.coe_coe]
  simp only [hf]


-- @@ L188-190 verbatim
@[simp] theorem augmentation_norm (H : Subgroup G) [Fintype H] (c : FreeChain A G) :
    augmentation (subgroupNorm H c) = (Fintype.card H : ℤ) * augmentation c := by
  simp [subgroupNorm,LinearMap.sum_apply]


-- @@ L192-223 verbatim
theorem cyclic_chain_obstruction {A₀ A₁ A₂ : Type} (H : Subgroup G)
    [Fintype H] [IsCyclic H] (g : H) (hg : ∀ x, x ∈ Subgroup.zpowers g)
    (b₁ : FreeChain A₁ G →ₗ[ℤ] FreeChain A₀ G)
    (b₂ : FreeChain A₂ G →ₗ[ℤ] FreeChain A₁ G)
    (h₁ : ∀ (h : H) c, b₁ (chainShift (h:G) c) = chainShift (h:G) (b₁ c))
    (h₂ : ∀ (h : H) c, b₂ (chainShift (h:G) c) = chainShift (h:G) (b₂ c))
    (hbb : ∀ c, b₁ (b₂ c) = 0)
    (haug : ∀ c, augmentation (b₁ c) = 0)
    (v : FreeChain A₀ G) (hv : augmentation v = 1)
    (c : FreeChain A₁ G) (hc : b₁ c = chainShift (g:G) v - v)
    (D : FreeChain A₂ G) (hD : b₂ D = subgroupNorm H c)
    (hDi : chainShift (g:G) D = D) : (g:G) = 1 := by
  obtain ⟨B,hB⟩ := invariant_is_norm H g hg D hDi
  have hz : subgroupNorm H (c - b₂ B) = 0 := by
    rw [map_sub,norm_map H b₂ h₂,hB,← hD,sub_self]
  obtain ⟨E,hE⟩ := norm_zero_is_difference H g hg (c-b₂ B) hz
  have hi : chainShift (g:G) (v - b₁ E) = v - b₁ E := by
    have he := congrArg b₁ hE
    rw [map_sub,h₁,map_sub,hbb,sub_zero,hc] at he
    rw [map_sub]
    rw [sub_eq_iff_eq_add.mp he]
    abel
  obtain ⟨w,hw⟩ := invariant_is_norm H g hg (v-b₁ E) hi
  have ha : (Fintype.card H : ℤ) * augmentation w = 1 := by
    rw [← augmentation_norm,hw,map_sub,hv,haug,sub_zero]
  have hcard : Fintype.card H = 1 := by
    have hd : (Fintype.card H : ℤ) ∣ 1 := ⟨augmentation w,ha.symm⟩
    have := Int.natCast_nonneg (Fintype.card H)
    have hpm := Int.eq_one_or_neg_one_of_mul_eq_one ha
    omega
  have : Subsingleton H := Fintype.card_le_one_iff_subsingleton.mp (hcard.le)
  exact congrArg (fun h : H => (h:G)) (Subsingleton.elim g 1)


-- @@ L225-225 verbatim
end Release075.FreeChain


-- @@ L227-227 verbatim
end OAI
