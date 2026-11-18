import OAI.NumberTheory.DirichletL.Moments.AllocationCost


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open scoped BigOperators Classical


-- @@ L8-8 verbatim
namespace SevenEighths.CenteredMomentCommonRawScale

-- @@ L9-9 verbatim
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform

-- @@ L10-10 verbatim
local notation "O" => ActualEisensteinCubic.O

-- @@ L11-11 verbatim
variable {ι : Type*} [Fintype ι]


-- @@ L13-14 verbatim
def frozenScale (B : Tuple ι) (P : ι → ℝ) (i : ι) : ℝ :=
  if B (Sum.inl i)=1 then 1 else P i


-- @@ L16-17 verbatim
def plainNorm (B : Tuple ι) : ℝ :=
  (Ideal.absNorm (B (Sum.inr 0)):ℝ)*Ideal.absNorm (B (Sum.inr 1))


-- @@ L19-19 verbatim
def rawReduction (B : Tuple ι) (P : ι → ℝ) : ℝ := plainNorm B*∏ i,frozenScale B P i


-- @@ L21-22 verbatim
def remainingRaw (B : Tuple ι) (T : ℝ) (P : ι → ℝ) : ℝ :=
  (T/plainNorm B)*∏ i : liveIndices B,P i


-- @@ L24-27 verbatim
omit [Fintype ι] in
theorem plainNorm_pos (B : Tuple ι) (hB : ∀ i,B i≠0) : 0<plainNorm B := by
  unfold plainNorm
  apply mul_pos <;> exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hB _))


-- @@ L29-35 verbatim
omit [Fintype ι] in
theorem frozenScale_pos (B : Tuple ι) (P : ι → ℝ) (hP : ∀ i,0<P i) (i : ι) :
    0<frozenScale B P i := by
  unfold frozenScale
  split_ifs
  · exact zero_lt_one
  · exact hP i


-- @@ L37-38 verbatim
theorem rawReduction_pos (B : Tuple ι) (hB : ∀ i,B i≠0) (P : ι → ℝ) (hP : ∀ i,0<P i) :
    0<rawReduction B P := mul_pos (plainNorm_pos B hB) (Finset.prod_pos (fun i _ => frozenScale_pos B P hP i))


-- @@ L40-47 verbatim
theorem slot_scale_split (B : Tuple ι) (P : ι → ℝ) :
    (∏ i,frozenScale B P i)*(∏ i : liveIndices B,P i)=∏ i,P i := by
  rw [Finset.prod_coe_sort (liveIndices B) P]
  rw [← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun i => B (Sum.inl i)=1) P]
  unfold frozenScale liveIndices
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one,one_mul]
  ring


-- @@ L49-56 verbatim
theorem raw_scale_identity (B : Tuple ι) (hB : ∀ i,B i≠0) (T : ℝ) (P : ι → ℝ) :
    remainingRaw B T P*rawReduction B P=T*∏ i,P i := by
  unfold remainingRaw rawReduction
  have h := slot_scale_split B P
  calc
    _ = T*((∏ i,frozenScale B P i)*(∏ i : liveIndices B,P i)) := by
      field_simp [(plainNorm_pos B hB).ne']
    _ = _ := by rw [h]


-- @@ L58-65 verbatim
theorem remainingRaw_source (B : Tuple ι) (_hB : ∀ i,B i≠0)
    (B₁ B₂ : Ideal O) (_hB₁ : B₁≠0) (_hB₂ : B₂≠0) (T : ℝ) (P : ι → ℝ) :
    remainingRaw B (T/((Ideal.absNorm B₁:ℝ)*Ideal.absNorm B₂)) P=
      (T/((Ideal.absNorm (B₁*B (Sum.inr 0)):ℝ)*Ideal.absNorm (B₂*B (Sum.inr 1))))*
        ∏ i : liveIndices B,P i := by
  unfold remainingRaw plainNorm
  simp only [map_mul,Nat.cast_mul]
  ring


-- @@ L67-71 verbatim
theorem product_norm (B : Tuple ι) :
    (Ideal.absNorm (finiteTupleProduct B):ℝ)=plainNorm B*∏ i,(Ideal.absNorm (B (Sum.inl i)):ℝ) := by
  simp only [finiteTupleProduct,Fintype.prod_sum_type,Fin.prod_univ_two,map_mul,map_prod,
    Nat.cast_mul,Nat.cast_prod,plainNorm]
  ring


-- @@ L73-79 verbatim
theorem frozen_window_ne_zero (B : Tuple ι) (C R : Ideal O) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
    (hne : frozenCoefficient B C R ν Wslot P≠0) (i : ι) (hi : B (Sum.inl i)≠1) :
    Wslot i ((Ideal.absNorm (B (Sum.inl i)):ℝ)/P i)≠0 := by
  have hp := (mul_ne_zero_iff.mp hne).1
  have hx := Finset.prod_ne_zero_iff.mp hp i (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩)
  exact (mul_ne_zero_iff.mp hx).2


-- @@ L81-111 verbatim
theorem actual_reduction_norm (B : Tuple ι) (hB : ∀ i,B i≠0) (C R : Ideal O)
    (hprod : finiteTupleProduct B=C) (ν : ι → Ideal O → ℂ)
    (Wslot : ι → ℝ → ℂ) (P : ι → ℝ) (hP : ∀ i,0<P i)
    (a b : ℝ) (ha : 0<a) (hW : ∀ i,Function.support (Wslot i)⊆Set.Icc a b)
    (hne : frozenCoefficient B C R ν Wslot P≠0) :
    (min 1 a)^Fintype.card ι*rawReduction B P≤(Ideal.absNorm C:ℝ) ∧
      (Ideal.absNorm C:ℝ)≤(max 1 b)^Fintype.card ι*rawReduction B P := by
  have hi (i : ι) : min 1 a*frozenScale B P i≤(Ideal.absNorm (B (Sum.inl i)):ℝ) ∧
      (Ideal.absNorm (B (Sum.inl i)):ℝ)≤max 1 b*frozenScale B P i := by
    by_cases h : B (Sum.inl i)=1
    · simp only [frozenScale,h,ite_true,map_one,Nat.cast_one,mul_one]
      exact ⟨min_le_left _ _,le_max_left _ _⟩
    · have hs := hW i (frozen_window_ne_zero B C R ν Wslot P hne i h)
      rw [frozenScale,ite_eq_right h]
      exact ⟨le_trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (hP i).le)
          ((le_div_iff₀ (hP i)).mp hs.1),
        le_trans ((div_le_iff₀ (hP i)).mp hs.2)
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (hP i).le)⟩
  rw [←hprod,product_norm]
  constructor
  · have hh := Finset.prod_le_prod₀ (s:=Finset.univ)
      (fun i _ => mul_nonneg (le_of_lt (lt_min zero_lt_one ha)) (frozenScale_pos B P hP i).le)
      (fun i _ => (hi i).1)
    simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (plainNorm_pos B hB).le
    simpa only [rawReduction,mul_left_comm,mul_assoc] using hh'
  · have hh := Finset.prod_le_prod₀ (s:=Finset.univ) (fun i _ => Nat.cast_nonneg (Ideal.absNorm (B (Sum.inl i))))
      (fun i _ => (hi i).2)
    simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (plainNorm_pos B hB).le
    simpa only [rawReduction,mul_left_comm,mul_assoc] using hh'


-- @@ L113-113 verbatim
end SevenEighths.CenteredMomentCommonRawScale


-- @@ L115-115 verbatim
end


-- @@ L117-117 verbatim
end OAI
