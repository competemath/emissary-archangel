import OAI.InformationTheory.AmplitudeDamping.TensorEntropy


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
universe u_1 u_2 u_3 u_4


-- @@ L9-9 verbatim
namespace GAD


-- @@ L11-11 verbatim
section

-- @@ L12-12 verbatim
open scoped BigOperators ComplexOrder MatrixOrder

-- @@ L13-13 verbatim
open Matrix

-- @@ L14-14 verbatim
variable {ι : Type u_1} [Fintype ι]


-- @@ L16-16 verbatim
def vecMass (ψ : ι → ℂ) : ℝ := ∑ i, Complex.normSq (ψ i)


-- @@ L18-19 verbatim
theorem vecMass_nonneg (ψ : ι → ℂ) : 0 ≤ vecMass ψ :=
  Finset.sum_nonneg (fun i _ ↦ Complex.normSq_nonneg (ψ i))


-- @@ L21-22 verbatim
theorem pure_posSemidef (ψ : ι → ℂ) : (pure ψ).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star ψ


-- @@ L24-25 verbatim
theorem pure_trace (ψ : ι → ℂ) : (pure ψ).trace = (vecMass ψ : ℂ) := by
  simp [Matrix.trace, pure, vecMass, Complex.mul_conj]


-- @@ L27-28 verbatim
theorem pure_state [DecidableEq ι] {ψ : ι → ℂ} (hψ : vecMass ψ = 1) : IsState (pure ψ) := by
  exact ⟨pure_posSemidef ψ, by rw [pure_trace,hψ]; rfl⟩


-- @@ L30-38 verbatim
theorem vecMass_eq_zero {ψ : ι → ℂ} : vecMass ψ = 0 ↔ ψ = 0 := by
  constructor
  · intro h
    funext i
    apply Complex.normSq_eq_zero.mp
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ Complex.normSq_nonneg (ψ i))).mp h i
      (Finset.mem_univ i)
  · rintro rfl
    simp [vecMass]


-- @@ L40-40 verbatim
variable [DecidableEq ι]


-- @@ L42-42 verbatim
def unitVec [Inhabited ι] : ι → ℂ := fun i ↦ if i = default then 1 else 0


-- @@ L44-45 verbatim
@[simp] theorem vecMass_unitVec [Inhabited ι] : vecMass (unitVec (ι := ι)) = 1 := by
  simp [vecMass, unitVec]


-- @@ L47-50 verbatim
omit [DecidableEq ι] in
theorem vecMass_smul (z : ℂ) (ψ : ι → ℂ) :
    vecMass (z • ψ) = Complex.normSq z * vecMass ψ := by
  simp [vecMass, Complex.normSq_mul, Finset.mul_sum]


-- @@ L52-53 verbatim
def normalize [Inhabited ι] (ψ : ι → ℂ) : ι → ℂ :=
  if vecMass ψ = 0 then unitVec else ((Real.sqrt (vecMass ψ) : ℂ)⁻¹) • ψ


-- @@ L55-62 verbatim
theorem sqrt_mass_normalize [Inhabited ι] (ψ : ι → ℂ) :
    (Real.sqrt (vecMass ψ) : ℂ) • normalize ψ = ψ := by
  by_cases h : vecMass ψ = 0
  · have hz := vecMass_eq_zero.mp h
    simp [normalize,hz,vecMass]
  · have hs : (Real.sqrt (vecMass ψ) : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_ne_zero'.mpr (lt_of_le_of_ne (vecMass_nonneg ψ) (Ne.symm h)))
    simp [normalize,h,smul_smul,hs]


-- @@ L64-69 verbatim
theorem normalize_mass [Inhabited ι] (ψ : ι → ℂ) : vecMass (normalize ψ) = 1 := by
  by_cases h : vecMass ψ = 0
  · simp [normalize,h]
  · have hs : Real.sqrt (vecMass ψ)*Real.sqrt (vecMass ψ) = vecMass ψ := Real.mul_self_sqrt (vecMass_nonneg ψ)
    simp only [normalize, ite_eq_right h, vecMass_smul, map_inv₀, Complex.normSq_ofReal, hs]
    exact inv_mul_cancel₀ h


-- @@ L71-76 verbatim
theorem normSq_normalize [Inhabited ι] (ψ : ι → ℂ) (i : ι) :
    Complex.normSq (ψ i) = vecMass ψ * Complex.normSq (normalize ψ i) := by
  calc
    Complex.normSq (ψ i) = Complex.normSq (((Real.sqrt (vecMass ψ) : ℂ) • normalize ψ) i) :=
      congrArg (fun f : ι → ℂ ↦ Complex.normSq (f i)) (sqrt_mass_normalize ψ).symm
    _ = _ := by simp [Complex.normSq_mul, Real.mul_self_sqrt (vecMass_nonneg ψ)]


-- @@ L78-78 verbatim
end


-- @@ L80-80 verbatim
section

-- @@ L81-81 verbatim
open scoped BigOperators ComplexOrder

-- @@ L82-82 verbatim
open Matrix


-- @@ L84-85 verbatim
def branch {n : ℕ} (ψ : Basis (n+1) → ℂ) (b : Fin 2) : Basis n → ℂ :=
  fun i ↦ ψ (Fin.cons b i)


-- @@ L87-88 verbatim
def population {n : ℕ} (ψ : Basis n → ℂ) (j : Fin n) : ℝ :=
  ∑ i, if i j = 1 then Complex.normSq (ψ i) else 0


-- @@ L90-96 verbatim
theorem population_nonneg {n : ℕ} (ψ : Basis n → ℂ) (j : Fin n) :
    0 ≤ population ψ j := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact Complex.normSq_nonneg _
  · rfl


-- @@ L98-104 verbatim
theorem population_le_mass {n : ℕ} (ψ : Basis n → ℂ) (j : Fin n) :
    population ψ j ≤ vecMass ψ := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · rfl
  · exact Complex.normSq_nonneg _


-- @@ L106-108 verbatim
theorem population_mem {n : ℕ} {ψ : Basis n → ℂ} (hψ : vecMass ψ = 1) (j : Fin n) :
    population ψ j ∈ Set.Icc (0:ℝ) 1 :=
  ⟨population_nonneg ψ j, hψ ▸ population_le_mass ψ j⟩


-- @@ L110-114 verbatim
theorem vecMass_branches {n : ℕ} (ψ : Basis (n+1) → ℂ) :
    vecMass ψ = vecMass (branch ψ 0) + vecMass (branch ψ 1) := by
  unfold vecMass
  rw [sum_fin_cons]
  simp [Fin.sum_univ_two,branch]


-- @@ L116-120 verbatim
theorem population_zero {n : ℕ} (ψ : Basis (n+1) → ℂ) :
    population ψ 0 = vecMass (branch ψ 1) := by
  unfold population
  rw [sum_fin_cons]
  simp [vecMass,branch]


-- @@ L122-126 verbatim
theorem population_succ {n : ℕ} (ψ : Basis (n+1) → ℂ) (j : Fin n) :
    population ψ j.succ = population (branch ψ 0) j + population (branch ψ 1) j := by
  unfold population
  rw [sum_fin_cons]
  simp [Fin.sum_univ_two,branch]


-- @@ L128-135 verbatim
theorem population_normalize {n : ℕ} (ψ : Basis n → ℂ) (j : Fin n) :
    population ψ j = vecMass ψ * population (normalize ψ) j := by
  simp only [population,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs with h
  · exact normSq_normalize ψ i
  · exact (mul_zero _).symm


-- @@ L137-144 verbatim
def basisSplit (n : ℕ) : Basis n ⊕ Basis n ≃ Basis (n+1) where
  toFun := Sum.elim (fun i : Basis n ↦ Fin.cons 0 i) (fun i : Basis n ↦ Fin.cons 1 i)
  invFun i := if i 0 = 0 then Sum.inl (Fin.tail i) else Sum.inr (Fin.tail i)
  left_inv i := by cases i <;> simp
  right_inv i := by
    have h := Fin.cons_self_tail i
    have hi : i 0 = 0 ∨ i 0 = 1 := by have := (i 0).isLt; omega
    rcases hi with hi | hi <;> simp [hi] at * <;> exact h


-- @@ L146-146 verbatim
@[simp] theorem basisSplit_inl {n : ℕ} (i : Basis n) : basisSplit n (Sum.inl i) = Fin.cons 0 i := rfl

-- @@ L147-147 verbatim
@[simp] theorem basisSplit_inr {n : ℕ} (i : Basis n) : basisSplit n (Sum.inr i) = Fin.cons 1 i := rfl


-- @@ L149-149 verbatim
end


-- @@ L151-151 verbatim
open scoped BigOperators ComplexOrder MatrixOrder

-- @@ L152-152 verbatim
open Matrix


-- @@ L154-157 verbatim
theorem channel_pure_apply (γ ν : ℝ) (n : ℕ) (ψ : Basis n → ℂ) (i j : Basis n) :
    channel γ ν n (pure ψ) i j =
      ∑ r, (tensorKraus γ ν n r *ᵥ ψ) i * star ((tensorKraus γ ν n r *ᵥ ψ) j) := by
  simp only [channel,mul_pure_mul_conjTranspose,Matrix.sum_apply,pure]


-- @@ L159-166 verbatim
theorem tensorKraus_mulVec_cons (γ ν : ℝ) {n : ℕ} (r : Fin 4) (R : Fin n → Fin 4)
    (ψ : Basis (n+1) → ℂ) (b : Fin 2) (i : Basis n) :
    (tensorKraus γ ν (n+1) (Fin.cons r R) *ᵥ ψ) (Fin.cons b i) =
      ∑ a : Fin 2, kraus γ ν r b a * (tensorKraus γ ν n R *ᵥ branch ψ a) i := by
  simp only [Matrix.mulVec,dotProduct]
  rw [sum_fin_cons]
  simp only [tensorKraus,Fin.prod_univ_succ,Fin.cons_zero,Fin.cons_succ]
  simp only [branch,Finset.mul_sum,mul_assoc]


-- @@ L168-195 verbatim
theorem channel_first_site_entry (γ ν : ℝ) {n : ℕ} (ψ : Basis (n+1) → ℂ)
    (b c : Fin 2) (i j : Basis n) :
    channel γ ν (n+1) (pure ψ) (Fin.cons b i) (Fin.cons c j) =
      applyKraus (kraus γ ν)
        (fun a d ↦ (columns (tensorKraus γ ν n) (branch ψ a) *
          (columns (tensorKraus γ ν n) (branch ψ d)).conjTranspose) i j) b c := by
  rw [channel_pure_apply,sum_fin_cons]
  simp only [tensorKraus_mulVec_cons]
  let u (R : Fin n → Fin 4) (a : Fin 2) (k : Basis n) :=
    (tensorKraus γ ν n R *ᵥ branch ψ a) k
  change (∑ r : Fin 4, ∑ R : Fin n → Fin 4,
      (∑ a : Fin 2, kraus γ ν r b a * u R a i) *
        star (∑ d : Fin 2, kraus γ ν r c d * u R d j)) =
    ∑ r : Fin 4, ∑ d : Fin 2,
      (∑ a : Fin 2, kraus γ ν r b a * (∑ R : Fin n → Fin 4, u R a i * star (u R d j))) *
        star (kraus γ ν r c d)
  simp only [star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro R _
  ring


-- @@ L197-211 verbatim
theorem channel_branch_blocks (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (ψ : Basis (n+1) → ℂ) :
    Matrix.reindex (basisSplit n).symm (basisSplit n).symm (channel γ ν (n+1) (pure ψ)) =
      thermal (columns (tensorKraus γ ν n) (branch ψ 0))
        (columns (tensorKraus γ ν n) (branch ψ 1))
        (1-γ*ν) (γ*(1-ν)) (γ*ν) (1-γ*(1-ν)) (Real.sqrt (1-γ)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_symm,basisSplit_inl,basisSplit_inr,
      channel_first_site_entry]
  all_goals
    rw [local_channel γ ν hγ hν (fun a d ↦
      (columns (tensorKraus γ ν n) (branch ψ a) *
        (columns (tensorKraus γ ν n) (branch ψ d)).conjTranspose) i j)]
    simp [thermal,gram]


-- @@ L213-213 verbatim
end GAD


-- @@ L215-215 verbatim
open scoped BigOperators ComplexOrder MatrixOrder

-- @@ L216-216 verbatim
open Matrix

-- @@ L217-217 verbatim
namespace GAD


-- @@ L219-220 verbatim
variable {ι : Type u_2} {κ : Type u_3} {ρ : Type u_4} [Fintype ι] [Fintype κ] [Fintype ρ]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ]


-- @@ L222-226 verbatim
omit [Fintype ι] [Fintype ρ] [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ] in
theorem columns_smul (L : ρ → Matrix ι κ ℂ) (ψ : κ → ℂ) (z : ℂ) :
    columns L (z • ψ) = z • columns L ψ := by
  ext i r
  simp [columns, Matrix.mulVec_smul]


-- @@ L228-231 verbatim
omit [Fintype ι] [Fintype ρ] [DecidableEq ι] [DecidableEq ρ] in
theorem columns_normalize [Inhabited κ] (L : ρ → Matrix ι κ ℂ) (ψ : κ → ℂ) :
    columns L ψ = Real.sqrt (vecMass ψ) • columns L (normalize ψ) := by
  rw [← Complex.coe_smul, ← columns_smul, sqrt_mass_normalize]


-- @@ L233-235 verbatim
omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] [DecidableEq ρ] in
theorem gram_columns (L : ρ → Matrix ι κ ℂ) (ψ : κ → ℂ) :
    gram (columns L ψ) = applyKraus L (pure ψ) := columns_pure L ψ


-- @@ L237-243 verbatim
theorem mass_channel_columns (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) (ψ : Basis n → ℂ) :
    mass (columns (tensorKraus γ ν n) ψ) = vecMass ψ := by
  unfold mass
  rw [gram_columns]
  change (channel γ ν n (pure ψ)).trace.re = _
  rw [channel_trace γ ν hγ hν, pure_trace,Complex.ofReal_re]


-- @@ L245-254 verbatim
omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
theorem thermal_sqrt_smul (X Y : Matrix ι κ ℂ) (a b c d K : ℝ)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    thermal (Real.sqrt x • X) (Real.sqrt y • Y) a b c d K =
      thermal X Y (a*x) (b*y) (c*x) (d*y) (K*Real.sqrt x*Real.sqrt y) := by
  simp only [thermal,gram_sqrt_smul hx,gram_sqrt_smul hy,smul_smul,
    Matrix.conjTranspose_smul, star_trivial,Matrix.smul_mul,Matrix.mul_smul]
  congr 1
  · congr 1; ring
  · congr 1; ring


-- @@ L256-259 verbatim
theorem channel_state (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) (n : ℕ) {P : QMatrix n} (hP : IsState P) :
    IsState (channel γ ν n P) :=
  ⟨channel_posSemidef _ _ _ hP.1, (channel_trace γ ν hγ hν n P).trans hP.2⟩


-- @@ L261-306 verbatim
theorem output_entropy_recursion (γ ν : ℝ) (hγ : γ ∈ Set.Icc (0:ℝ) 1)
    (hν : ν ∈ Set.Icc (0:ℝ) 1) {n : ℕ} (ψ : Basis (n+1) → ℂ)
    (hψ : vecMass ψ = 1) :
    vecMass (branch ψ 0) * entropy (channel γ ν n (pure (normalize (branch ψ 0)))) +
      vecMass (branch ψ 1) * entropy (channel γ ν n (pure (normalize (branch ψ 1)))) +
      g (v γ ν (population ψ 0)) ≤ entropy (channel γ ν (n+1) (pure ψ)) := by
  let x := vecMass (branch ψ 0)
  let y := vecMass (branch ψ 1)
  let X := columns (tensorKraus γ ν n) (normalize (branch ψ 0))
  let Y := columns (tensorKraus γ ν n) (normalize (branch ψ 1))
  have hx : 0 ≤ x := vecMass_nonneg _
  have hy : 0 ≤ y := vecMass_nonneg _
  have hxy : x+y=1 := (vecMass_branches ψ).symm.trans hψ
  have hxy' : x=1-y := by linarith
  have hX : mass X = 1 := (mass_channel_columns γ ν hγ hν n _).trans (normalize_mass _)
  have hY : mass Y = 1 := (mass_channel_columns γ ν hγ hν n _).trans (normalize_mass _)
  have h1ν : 0 ≤ 1-ν := sub_nonneg.mpr hν.2
  have h1γ : 0 ≤ 1-γ := sub_nonneg.mpr hγ.2
  have h1γν : 0 ≤ 1-γ*ν := by nlinarith [hγ.2, mul_nonneg hγ.1 h1ν]
  have h1γν' : 0 ≤ 1-γ*(1-ν) := by nlinarith [hγ.2, mul_nonneg hγ.1 hν.1]
  have hKsq : (Real.sqrt (1-γ)*Real.sqrt x*Real.sqrt y)^2 = (1-γ)*x*y := by
    rw [mul_pow,mul_pow,Real.sq_sqrt h1γ,Real.sq_sqrt hx,Real.sq_sqrt hy]
  have hh := thermal_entropy X Y hX hY
    (mul_nonneg h1γν hx) (mul_nonneg (mul_nonneg hγ.1 h1ν) hy)
    (mul_nonneg (mul_nonneg hγ.1 hν.1) hx) (mul_nonneg h1γν' hy)
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))
    (show (1-γ*ν)*x+γ*(1-ν)*y+γ*ν*x+(1-γ*(1-ν))*y=1 by nlinarith only [hxy])
    (show ((1-γ*ν)*x)*((1-γ*(1-ν))*y)-(γ*(1-ν)*y)*(γ*ν*x)=
      (Real.sqrt (1-γ)*Real.sqrt x*Real.sqrt y)^2 by rw [hKsq]; ring)
  have hcolx : (1-γ*ν)*x+γ*ν*x=x := by ring
  have hcoly : γ*(1-ν)*y+(1-γ*(1-ν))*y=y := by ring
  have hu : ((1-γ*ν)*x+γ*(1-ν)*y)*(γ*ν*x+(1-γ*(1-ν))*y)-
      (Real.sqrt (1-γ)*Real.sqrt x*Real.sqrt y)^2 = v γ ν y := by
    rw [hKsq,hxy']; unfold v; ring
  have heq : Matrix.reindex (basisSplit n).symm (basisSplit n).symm
      (channel γ ν (n+1) (pure ψ)) =
        thermal X Y ((1-γ*ν)*x) (γ*(1-ν)*y) (γ*ν*x) ((1-γ*(1-ν))*y)
          (Real.sqrt (1-γ)*Real.sqrt x*Real.sqrt y) := by
    rw [channel_branch_blocks γ ν hγ hν,columns_normalize _ (branch ψ 0),
      columns_normalize _ (branch ψ 1),thermal_sqrt_smul _ _ _ _ _ _ _ hx hy]
  have hent := entropy_reindex (basisSplit n).symm
    (channel_posSemidef γ ν (n+1) (pure_posSemidef ψ)).isHermitian
  rw [heq] at hent
  have hbound := hh.2.2
  rw [hcolx,hcoly,hu,hent] at hbound
  simpa only [x,y,X,Y,gram_columns,population_zero,channel,applyKraus] using hbound


-- @@ L308-308 verbatim
end GAD


-- @@ L310-310 verbatim
end


-- @@ L312-312 verbatim
end OAI
