import OAI.Analysis.CharacterCriterion.AmplifiedComparison


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped TensorProduct

-- @@ L7-7 verbatim
open scoped InnerProductSpace

-- @@ L8-8 verbatim
open scoped BigOperators

-- @@ L9-9 verbatim
open Set Module

-- @@ L10-10 verbatim
open Topology

-- @@ L11-11 verbatim
open NormedSpace

-- @@ L12-12 verbatim
open scoped ComplexOrder

-- @@ L13-13 verbatim
open scoped ComplexOrder

-- @@ L14-14 verbatim
open scoped InnerProductSpace

-- @@ L15-15 verbatim
open scoped InnerProductSpace

-- @@ L16-16 verbatim
open NormedSpace

-- @@ L17-17 verbatim
open scoped TensorProduct InnerProductSpace

-- @@ L18-18 verbatim
open UniformSpace

-- @@ L19-19 verbatim
variable [instSize : KirchbergRordam.GenericRW.Size]

-- @@ L20-20 verbatim
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n

-- @@ L21-21 verbatim
variable [instPauliData : KirchbergRordam.GenericRW.PauliData]



-- @@ L24-24 verbatim
namespace KirchbergRordam.GenericRW.FullComparison

-- @@ L25-25 verbatim
open scoped BigOperators WithCStarModule InnerProductSpace CStarAlgebra

-- @@ L26-26 verbatim
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]


-- @@ L28-63 verbatim
omit instSize instPauliData in
lemma mem_span_list.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    [PartialOrder A]
    [StarOrderedRing A]
    {c x : A} (hx : x ∈ TwoSidedIdeal.span {c}) :
    ∃ L : List (A × A), x = (L.map fun p => p.1 * c * p.2).sum := by
  induction hx using TwoSidedIdeal.span_induction with
  | mem x hx =>
    have he : x = c := hx
    subst x
    exact ⟨[(1,1)], by simp⟩
  | zero => exact ⟨[], by simp⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨L,hL⟩ := ihx
    obtain ⟨M,hM⟩ := ihy
    exact ⟨L++M, by simp [hL,hM]⟩
  | neg x hx ih =>
    obtain ⟨L,hL⟩ := ih
    refine ⟨L.map fun p => (-p.1,p.2), ?_⟩
    simp only [List.map_map, Function.comp_def, neg_mul, hL]
    clear hL
    induction L with
    | nil => simp
    | cons p L ih => simpa [neg_add, add_comm] using congrArg (fun y => -(p.1*c*p.2)+y) ih
  | left_absorb a x hx ih =>
    obtain ⟨L,hL⟩ := ih
    refine ⟨L.map fun p => (a*p.1,p.2), ?_⟩
    simp only [List.map_map, Function.comp_def, mul_assoc, ← List.sum_map_mul_left, hL]
  | right_absorb a x hx ih =>
    obtain ⟨L,hL⟩ := ih
    refine ⟨L.map fun p => (p.1,p.2*a), ?_⟩
    simp only [List.map_map, Function.comp_def, ← mul_assoc, ← List.sum_map_mul_right, hL]


-- @@ L65-76 verbatim
lemma finite_presentation {c : A} (hc : Fullness.IsFull c) :
    ∃ n : ℕ, ∃ h l : Fin n → A, ∑ i, h i*c*l i = 1 := by
  have hm : (1:A) ∈ TwoSidedIdeal.span {c} := by
    rw [show TwoSidedIdeal.span {c}=⊤ from hc]
    exact TwoSidedIdeal.mem_top A
  obtain ⟨L,hL⟩ := mem_span_list hm
  refine ⟨L.length, fun i => (L.get i).1, fun i => (L.get i).2, ?_⟩
  have he := congrArg (fun M : List (A × A) => (M.map fun p => p.1*c*p.2).sum)
    (List.ofFn_get L)
  have hh : (∑ i, (L.get i).1*c*(L.get i).2) = (L.map fun p => p.1*c*p.2).sum := by
    simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_def] using he
  exact hh.trans hL.symm



-- @@ L79-79 verbatim
end KirchbergRordam.GenericRW.FullComparison


-- @@ L81-81 verbatim
namespace KirchbergRordam.GenericRW.FullComparison

-- @@ L82-82 verbatim
open scoped BigOperators

-- @@ L83-83 verbatim
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

-- @@ L84-132 verbatim
lemma exists_full_perturbation {b : A} (hfull : Fullness.IsFull b)
    (c : ℝ → A) (hn : ∀ δ,0≤δ → ‖b-c δ‖≤δ) :
    ∃ δ : ℝ, 0<δ ∧ δ<1 ∧ Fullness.IsFull (c δ) := by
  classical
  obtain ⟨n,h,l,h1⟩ := finite_presentation hfull
  let K : ℝ := ∑ i, ‖h i‖*‖l i‖
  have hK : 0 ≤ K := Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  let δ : ℝ := 1/(2*(K+1))
  have hδ : 0 < δ := div_pos zero_lt_one (by positivity)
  have hδ1 : δ < 1 := by dsimp [δ]; apply (div_lt_one (by positivity)).mpr; linarith
  refine ⟨δ,hδ,hδ1,?_⟩
  let S := ∑ i, h i*c δ*l i
  have hnear : ‖1-S‖ < 1 := by
    have he : 1-S = ∑ i, h i*(b-c δ)*l i := by
      rw [← h1, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      noncomm_ring
    have hnorm : ‖1-S‖ ≤ K*δ := by
      rw [he]
      apply (norm_sum_le _ _).trans
      calc
        ∑ i, ‖h i*(b-c δ)*l i‖ ≤ ∑ i, (‖h i‖*‖l i‖)*δ := by
          apply Finset.sum_le_sum
          intro i _
          calc
            _ ≤ (‖h i‖*‖b-c δ‖)*‖l i‖ := (norm_mul_le _ _).trans
              (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
            _ ≤ (‖h i‖*δ)*‖l i‖ := by
              gcongr
              exact hn δ hδ.le
            _ = _ := by ring
        _ = _ := by rw [Finset.sum_mul]
    apply hnorm.trans_lt
    dsimp only [δ]
    rw [one_div, ← div_eq_mul_inv]
    exact (div_lt_one (by positivity)).mpr (by linarith)
  have hunit : IsUnit S := by
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hnear
  have hmem : S ∈ TwoSidedIdeal.span {c δ} := by
    apply (TwoSidedIdeal.span {c δ}).asIdeal.sum_mem
    intro i _
    exact TwoSidedIdeal.mul_mem_right _ _ _
      (TwoSidedIdeal.mul_mem_left _ _ _ (TwoSidedIdeal.subset_span rfl))
  apply TwoSidedIdeal.eq_top
  show (1:A) ∈ TwoSidedIdeal.span {c δ}
  obtain ⟨u,hu⟩ := hunit
  have hm := TwoSidedIdeal.mul_mem_left (TwoSidedIdeal.span {c δ}) (↑u⁻¹) S hmem
  simpa only [← hu, Units.inv_mul] using hm

-- @@ L133-133 verbatim
end KirchbergRordam.GenericRW.FullComparison


-- @@ L135-135 verbatim
namespace KirchbergRordam.GenericRW.FullComparison

-- @@ L136-136 verbatim
open scoped BigOperators WithCStarModule InnerProductSpace CStarAlgebra

-- @@ L137-137 verbatim
variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]



-- @@ L140-188 verbatim
theorem full_comparison {c : A} (hc : 0 ≤ c) (hfull : Fullness.IsFull c) :
    ∃ n : ℕ, ∃ v : Fin n → A, ∑ i, star (v i)*c*v i = 1 := by
  classical
  obtain ⟨n,h,l,h1⟩ := finite_presentation hfull
  let X : C⋆ᵐᵒᵈ(A, Fin n → A) := (WithCStarModule.equiv A _).symm fun i => h i*CFC.sqrt c
  let Y : C⋆ᵐᵒᵈ(A, Fin n → A) := (WithCStarModule.equiv A _).symm fun i => star (l i)*CFC.sqrt c
  let d : A := ∑ i, star (l i)*c*l i
  have hs := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg c)).star_eq
  have hprod : inner A X Y = 1 := by
    simp only [X,Y,WithCStarModule.pi_inner, WithCStarModule.equiv_symm_pi_apply,
      WithCStarModule.inner_def, star_mul, hs]
    have hh : (∑ i, star (l i)*CFC.sqrt c*(CFC.sqrt c*star (h i))) =
        star (∑ i, h i*c*l i) := by
      rw [star_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [star_mul, star_mul, (IsSelfAdjoint.of_nonneg hc).star_eq]
      calc
        _ = star (l i)*(CFC.sqrt c*CFC.sqrt c)*star (h i) := by noncomm_ring
        _ = _ := by rw [CFC.sqrt_mul_sqrt_self c hc]; noncomm_ring
    rw [hh,h1,star_one]
  have hYY : inner A Y Y = d := by
    simp only [Y,WithCStarModule.pi_inner, WithCStarModule.equiv_symm_pi_apply,
      WithCStarModule.inner_def, star_mul, hs, star_star]
    apply Finset.sum_congr rfl
    intro i _
    calc
      _ = star (l i)*(CFC.sqrt c*CFC.sqrt c)*l i := by noncomm_ring
      _ = _ := by rw [CFC.sqrt_mul_sqrt_self c hc]
  have hdom : (1:A) ≤ ‖X‖^2 • d := by
    have hh := CStarModule.inner_mul_inner_swap_le (A := A) (x := X) (y := Y)
    rw [← CStarModule.star_inner X Y, hprod, star_one, one_mul, hYY] at hh
    exact hh
  have hd : IsStrictlyPositive (‖X‖^2 • d) := IsStrictlyPositive.of_le isStrictlyPositive_one hdom
  let r := (‖X‖^2 • d) ^ (-(1/2):ℝ)
  have hr : IsSelfAdjoint r := IsSelfAdjoint.of_nonneg (CFC.rpow_nonneg (a := ‖X‖^2 • d) (y := (-(1/2):ℝ)))
  refine ⟨n, fun i => ‖X‖ • (l i*r), ?_⟩
  calc
    ∑ i, star (‖X‖ • (l i*r))*c*(‖X‖ • (l i*r)) = r*(‖X‖^2 • d)*r := by
      simp only [star_smul, star_trivial, star_mul, hr.star_eq, smul_mul_assoc,
        mul_smul_comm, smul_smul]
      rw [← Finset.smul_sum, ← pow_two]
      congr 1
      dsimp only [d]
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      noncomm_ring
    _ = 1 := CFC.conjugate_rpow_neg_one_half _ hd

-- @@ L189-189 verbatim
end KirchbergRordam.GenericRW.FullComparison


-- @@ L191-191 verbatim
namespace KirchbergRordam.GenericRW.ConeCut

-- @@ L192-192 verbatim
open scoped CStarAlgebra ComplexOrder BigOperators

-- @@ L193-193 verbatim
open ConeModel MatrixMix

-- @@ L194-194 verbatim
local instance : PartialOrder Cone := CStarAlgebra.spectralOrder _

-- @@ L195-195 verbatim
local instance : LE Cone := (CStarAlgebra.spectralOrder Cone).toLE

-- @@ L196-196 verbatim
local instance : StarOrderedRing Cone := CStarAlgebra.spectralOrderedRing _


-- @@ L198-199 verbatim
lemma unit_norm (i j : Fin Size.n) : ‖unit i j‖≤1 :=
  CubeField.norm_matrix_unit CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom i j

-- @@ L200-211 verbatim
omit instSize instPauliData in
lemma coeff_difference
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {δ : ℝ} (hδ : 0≤δ) (t : unitInterval) : |coeff 0 t-coeff δ t|≤δ := by
  rw [coeff,sub_zero,max_eq_left t.2.1,coeff]
  apply abs_le.mpr
  constructor <;> by_cases h : (t:ℝ)-δ≤0
  · rw [max_eq_right h]; linarith [t.2.1]
  · rw [max_eq_left (le_of_not_ge h)]; linarith
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left (le_of_not_ge h)]; linarith

-- @@ L212-219 verbatim
lemma norm_sub_q {δ : ℝ} (hδ : 0≤δ) : ‖q 0 (le_refl 0)-q δ hδ‖≤δ := by
  change ‖((q 0 (le_refl 0):Cone):C(unitInterval,M2))-(q δ hδ:C(unitInterval,M2))‖≤δ
  apply (ContinuousMap.norm_le _ hδ).mpr
  intro t
  change ‖coeff 0 t • unit 0 0-coeff δ t • unit 0 0‖≤δ
  rw [← sub_smul, ← IsScalarTower.algebraMap_smul ℂ, norm_smul,
    norm_algebraMap', Real.norm_eq_abs]
  exact (mul_le_of_le_one_right (abs_nonneg _) (unit_norm 0 0)).trans (coeff_difference hδ t)


-- @@ L221-221 verbatim
variable {P : Type*} [CStarAlgebra P] [PartialOrder P] [StarOrderedRing P]

-- @@ L222-230 verbatim
lemma exists_full_cut (η : Cone →⋆ₐ[ℂ] P) (hfull : Fullness.IsFull (η (q 0 (le_refl 0)))) :
    ∃ δ : ℝ, ∃ hδ : 0<δ, δ<1 ∧ Fullness.IsFull (η (q δ hδ.le)) := by
  let c : ℝ → P := fun δ => if hδ : 0≤δ then η (q δ hδ) else η (q 0 (le_refl 0))
  have hn (δ : ℝ) (hδ : 0≤δ) : ‖η (q 0 (le_refl 0))-c δ‖≤δ := by
    dsimp only [c]
    rw [dite_eq_left hδ,← map_sub]
    exact (NonUnitalStarAlgHom.norm_apply_le η _).trans (norm_sub_q hδ)
  obtain ⟨δ,hδ,hδ1,hc⟩ := FullComparison.exists_full_perturbation hfull c hn
  exact ⟨δ,hδ,hδ1,by simpa [c,hδ.le] using hc⟩

-- @@ L231-231 verbatim
end KirchbergRordam.GenericRW.ConeCut


-- @@ L233-233 verbatim
namespace KirchbergRordam.GenericRW.MaxTensor

-- @@ L234-234 verbatim
open scoped CStarAlgebra BigOperators

-- @@ L235-235 verbatim
variable {P : Type*} [CStarAlgebra P]

-- @@ L236-236 verbatim
variable {I : Type*} [Fintype I]

-- @@ L237-253 verbatim
lemma word_sum_coordinate (n : ℕ) (j : Fin (n+1)) (a : I→P) (f : Fin (n+1)→P) :
    (∑ k,word n (fun i => if i=j then a k else f i))=
      word n (fun i => if i=j then ∑ k,a k else f i) := by
  induction n with
  | zero =>
    simp only [word,Fin.eq_zero j,ite_true]
    rfl
  | succ n ih =>
    induction j using Fin.cases with
    | zero =>
      simp only [word,ite_true,Fin.succ_ne_zero,ite_false]
      exact (pure_sum_left a (word n (fun i => f i.succ))).symm
    | succ j =>
      have hj : (0 : Fin (n+2)) ≠ j.succ := (Fin.succ_ne_zero j).symm
      simp only [word,ite_eq_right hj,Fin.succ_inj]
      exact (pure_sum_right (f 0) (fun k => word n (fun i => if i=j then a k else f i.succ))).symm.trans
        (congrArg (pure (f 0)) (ih j (fun i => f i.succ)))


-- @@ L255-255 verbatim
local instance (n : ℕ) : PartialOrder (powerPack P n) := CStarAlgebra.spectralOrder _

-- @@ L256-256 verbatim
local instance (n : ℕ) : StarOrderedRing (powerPack P n) := CStarAlgebra.spectralOrderedRing _

-- @@ L257-257 verbatim
variable [PartialOrder P] [StarOrderedRing P]

-- @@ L258-265 verbatim
lemma word_nonneg (n : ℕ) (f : Fin (n+1)→P) (hf : ∀ i,0≤f i) : 0≤word n f := by
  have he : star (word n (fun i=>CFC.sqrt (f i)))*word n (fun i=>CFC.sqrt (f i))=word n f := by
    rw [word_star,word_mul]
    congr 1
    funext i
    rw [(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg (f i))).star_eq,CFC.sqrt_mul_sqrt_self _ (hf i)]
  rw [← he]
  exact star_mul_self_nonneg _


-- @@ L267-267 verbatim
def defectWord (n : ℕ) (G : P) : powerPack P n := word n (fun _=>G)

-- @@ L268-269 verbatim
def cornerWord (n : ℕ) (c G : P) (j : Fin (n+1)) : powerPack P n :=
  word n (fun i=>if i=j then c else G)

-- @@ L270-271 verbatim
def columnWord (n : ℕ) (G : P) (j : Fin (n+1)) (v : P) : powerPack P n :=
  word n (fun i=>if i=j then v*CFC.sqrt G else 1)


-- @@ L273-274 verbatim
lemma cornerWord_nonneg (n : ℕ) {c G : P} (hc : 0≤c) (hG : 0≤G) (j : Fin (n+1)) :
    0≤cornerWord n c G j := word_nonneg n _ (by intro i; split_ifs <;> assumption)

-- @@ L275-280 verbatim
omit [PartialOrder P] [StarOrderedRing P] in
lemma cornerWord_orthogonal (n : ℕ) {c G : P} (hcG : c*G=0) (j k : Fin (n+1)) (hjk : j≠k) :
    cornerWord n c G j*cornerWord n c G k=0 := by
  rw [cornerWord,cornerWord,word_mul]
  apply word_zero_coordinate n _ j
  simp [hjk,hcG]

-- @@ L281-297 verbatim
lemma columnWord_comparison (n : ℕ) {c G : P} (hG : 0≤G) (v : I→P)
    (hv : ∑ i,star (v i)*c*v i=1) (j : Fin (n+1)) :
    ∑ i,star (columnWord n G j (v i))*cornerWord n c G j*columnWord n G j (v i)=defectWord n G := by
  have he (i : I) : star (columnWord n G j (v i))*cornerWord n c G j*columnWord n G j (v i)=
      word n (fun k => if k=j then CFC.sqrt G*(star (v i)*c*v i)*CFC.sqrt G else G) := by
    simp only [columnWord,cornerWord,word_star,word_mul]
    congr 1
    funext k
    by_cases hk : k=j
    · simp only [ite_eq_left hk,star_mul,(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg G)).star_eq]
      noncomm_ring
    · simp [hk]
  simp_rw [he]
  rw [word_sum_coordinate]
  have hc : (∑ i,CFC.sqrt G*(star (v i)*c*v i)*CFC.sqrt G)=G := by
    rw [← Finset.sum_mul,← Finset.mul_sum,hv,mul_one,CFC.sqrt_mul_sqrt_self G hG]
  simp only [hc,ite_self,defectWord]

-- @@ L298-298 verbatim
end KirchbergRordam.GenericRW.MaxTensor


-- @@ L300-300 verbatim
namespace KirchbergRordam.GenericRW.MaxTensor

-- @@ L301-301 verbatim
universe u

-- @@ L302-302 verbatim
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

-- @@ L303-314 verbatim
omit instSize instPauliData in
lemma lift_pure
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {E F : Type u} {G : Type*} [CStarAlgebra E] [CStarAlgebra F] [CStarAlgebra G]
    (φ : E →⋆ₐ[ℂ] G) (ψ : F →⋆ₐ[ℂ] G) (hc : ∀ a b,Commute (φ a) (ψ b)) (a : E) (b : F) :
    lift φ ψ hc (pure a b)=φ a*ψ b := by
  have hl := DFunLike.congr_fun (lift_includeLeft φ ψ hc) a
  have hr := DFunLike.congr_fun (lift_includeRight φ ψ hc) b
  change lift φ ψ hc (includeLeft a)=φ a at hl
  change lift φ ψ hc (includeRight b)=ψ b at hr
  rw [pure,map_mul,hl,hr]

-- @@ L315-318 verbatim
def powerHom (φ : A →⋆ₐ[ℂ] B) : (n : ℕ) → powerPack A n →⋆ₐ[ℂ] powerPack B n
  | 0 => φ
  | n+1 => lift (includeLeft.comp φ) (includeRight.comp (powerHom φ n))
      (fun a b => legs_commute (φ a) (powerHom φ n b))

-- @@ L319-321 verbatim
lemma powerHom_pure (φ : A →⋆ₐ[ℂ] B) (n : ℕ) (a : A) (b : powerPack A n) :
    powerHom φ (n+1) (pure a b)=pure (φ a) (powerHom φ n b) := by
  exact lift_pure _ _ _ a b


-- @@ L323-327 verbatim
lemma powerHom_word (φ : A →⋆ₐ[ℂ] B) (n : ℕ) (f : Fin (n+1)→A) :
    powerHom φ n (word n f)=word n (fun i=>φ (f i)) := by
  induction n with
  | zero => rfl
  | succ n ih => change powerHom φ (n+1) (pure (f 0) (word n _))=_; rw [powerHom_pure,ih]; rfl

-- @@ L328-328 verbatim
end KirchbergRordam.GenericRW.MaxTensor


-- @@ L330-330 verbatim
namespace KirchbergRordam.GenericRW.OrderZero.WeightedUnits

-- @@ L331-331 verbatim
open scoped BigOperators

-- @@ L332-332 verbatim
variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

-- @@ L333-333 verbatim
variable [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]

-- @@ L334-334 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

-- @@ L335-342 verbatim
def map (W : WeightedUnits ι A) (φ : A →⋆ₐ[ℂ] B) : WeightedUnits ι B where
  h := φ W.h
  x i j := φ (W.x i j)
  nonneg := map_nonneg φ W.nonneg
  norm_le := (NonUnitalStarAlgHom.norm_apply_le φ _).trans W.norm_le
  star_x i j := by rw [← map_star,W.star_x]
  mul_x i j k l := by rw [← map_mul,W.mul_x]; split_ifs <;> simp [map_mul]
  diagonal := by rw [← map_sum,W.diagonal]

-- @@ L343-343 verbatim
end KirchbergRordam.GenericRW.OrderZero.WeightedUnits


-- @@ L345-345 verbatim
namespace KirchbergRordam.GenericRW

-- @@ L346-346 verbatim
open scoped CStarAlgebra

-- @@ L347-347 verbatim
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] [PartialOrder A] [StarOrderedRing A]

-- @@ L348-363 verbatim
omit [Nontrivial A] [PartialOrder A] [StarOrderedRing A] in
omit instSize instPauliData in
lemma support_cut_cfc.{contextLevel1}
    [KirchbergRordam.GenericRW.Size]
    [KirchbergRordam.GenericRW.PauliData]
    {A : Type contextLevel1}
    [CStarAlgebra A]
    {a : A} (ha : IsSelfAdjoint a) (δ : ℝ) :
    ExactCut.cut a δ = cfc (fun t : ℝ => max (t-δ) 0) a := by
  rw [ExactCut.cut, CFC.posPart_def, cfcₙ_eq_cfc]
  have hd : cfc (fun t : ℝ => t-δ) a = a-algebraMap ℝ A δ := by
    rw [cfc_sub ..]
    change cfc id a - cfc (fun _ : ℝ => δ) a = _
    rw [cfc_id ℝ a ha, cfc_const _ _ ha]
  rw [← hd, ← cfc_comp (fun t : ℝ => t⁺) (fun t : ℝ => t-δ) a ha]
  rfl


-- @@ L365-387 verbatim
omit [Nontrivial A] in
lemma support_cut_comparison {a Y : A} (ha : IsSelfAdjoint a) (hY : 0≤Y) (hfix : a*Y=Y) :
    CuntzBelow Y (ExactCut.cut a (1/2)) := by
  have hz : (a-1)*Y=0 := by rw [sub_mul,hfix,one_mul,sub_self]
  have hsz := Intertwining.mul_sqrt_eq_zero hY hz
  have has : a*CFC.sqrt Y=CFC.sqrt Y := by
    simpa only [sub_mul,one_mul,sub_eq_zero] using hsz
  have hs : CFC.sqrt Y*1=a*CFC.sqrt Y := by simpa only [mul_one] using has.symm
  have hc := Intertwining.cfc (A:=A) (v:=CFC.sqrt Y) (a:=1) (b:=a)
    (IsSelfAdjoint.one A) ha hs (fun t : ℝ => max (t-1/2) 0) (by fun_prop)
  rw [← support_cut_cfc ha (1/2)] at hc
  have hone : cfc (fun t : ℝ => max (t-1/2) 0) (1:A)=(1/2:ℝ) • (1:A) := by
    rw [cfc_apply_one,Algebra.algebraMap_eq_smul_one]
    norm_num
  rw [hone,mul_smul_comm,mul_one] at hc
  let v : A := Real.sqrt 2 • CFC.sqrt Y
  have hv : star v*ExactCut.cut a (1/2)*v=Y := by
    dsimp only [v]
    rw [star_smul,star_trivial,(IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg Y)).star_eq,
      smul_mul_assoc,smul_mul_smul_comm,Real.mul_self_sqrt (by norm_num),mul_assoc,← hc,mul_smul_comm,
      CFC.sqrt_mul_sqrt_self Y hY,smul_smul]
    norm_num
  exact CuntzBelow.of_eq hv

-- @@ L388-388 verbatim
end KirchbergRordam.GenericRW

-- @@ L389-389 verbatim
end


-- @@ L391-391 verbatim
end OAI
