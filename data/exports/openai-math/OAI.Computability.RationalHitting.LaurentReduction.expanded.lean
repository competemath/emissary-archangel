import OAI.Computability.RationalHitting.Wronskian


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace RationalHitting.LaurentReduction

-- @@ L6-6 verbatim
open Module

-- @@ L7-7 verbatim
open scoped BigOperators LaurentSeries PowerSeries

-- @@ L8-8 verbatim
noncomputable section


-- @@ L10-10 verbatim
variable {K : Type*} [Field K]

-- @@ L11-11 verbatim
abbrev F (K : Type*) [Field K] := LaurentSeries K


-- @@ L13-14 verbatim
/-- Membership in K[[t]], inside K((t)). -/
def Integral (x : F K) : Prop := ∃ p : PowerSeries K, HahnSeries.ofPowerSeries ℤ K p = x


-- @@ L16-16 verbatim
def reduction (x : F K) : K := x.coeff 0


-- @@ L18-18 verbatim
def reduce {ι : Type*} (x : ι → F K) : ι → K := fun i => reduction (x i)


-- @@ L20-21 verbatim
lemma integral_iff (x : F K) : Integral x ↔ Valued.v x ≤ 1 :=
  (LaurentSeries.val_le_one_iff_eq_coe K x).symm


-- @@ L23-23 verbatim
lemma integral_zero : Integral (0 : F K) := ⟨0, map_zero _⟩

-- @@ L24-24 verbatim
lemma integral_one : Integral (1 : F K) := ⟨1, map_one _⟩

-- @@ L25-28 verbatim
lemma Integral.add {x y : F K} (hx : Integral x) (hy : Integral y) : Integral (x + y) := by
  obtain ⟨p, rfl⟩ := hx
  obtain ⟨q, rfl⟩ := hy
  exact ⟨p + q, map_add _ _ _⟩

-- @@ L29-31 verbatim
lemma Integral.neg {x : F K} (hx : Integral x) : Integral (-x) := by
  obtain ⟨p, rfl⟩ := hx
  exact ⟨-p, map_neg _ _⟩

-- @@ L32-33 verbatim
lemma Integral.sub {x y : F K} (hx : Integral x) (hy : Integral y) : Integral (x - y) := by
  simpa only [sub_eq_add_neg] using hx.add hy.neg

-- @@ L34-37 verbatim
lemma Integral.mul {x y : F K} (hx : Integral x) (hy : Integral y) : Integral (x * y) := by
  obtain ⟨p, rfl⟩ := hx
  obtain ⟨q, rfl⟩ := hy
  exact ⟨p * q, map_mul _ _ _⟩


-- @@ L39-39 verbatim
@[simp] lemma reduction_zero : reduction (0 : F K) = 0 := by simp [reduction]

-- @@ L40-40 verbatim
@[simp] lemma reduction_one : reduction (1 : F K) = 1 := by simp [reduction]

-- @@ L41-42 verbatim
lemma reduction_add (x y : F K) : reduction (x + y) = reduction x + reduction y := by
  simp [reduction]

-- @@ L43-53 verbatim
lemma reduction_mul {x y : F K} (hx : Integral x) (hy : Integral y) :
    reduction (x * y) = reduction x * reduction y := by
  obtain ⟨p, rfl⟩ := hx
  obtain ⟨q, rfl⟩ := hy
  rw [← map_mul]
  have hc : ∀ s : PowerSeries K, reduction (HahnSeries.ofPowerSeries ℤ K s) =
      PowerSeries.constantCoeff s := by
    intro s
    simpa only [reduction, Int.natCast_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply] using
      (LaurentSeries.coeff_coe_powerSeries s 0)
  rw [hc, hc, hc, map_mul]


-- @@ L55-71 verbatim
lemma normalize_vector {ι : Type*} [Fintype ι] (x : ι → F K) (hx : x ≠ 0) :
    ∃ (c : ι) (u : F K), u ≠ 0 ∧ (∀ i, Integral (u * x i)) ∧ u * x c = 1 := by
  classical
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hx
  change x j ≠ 0 at hj
  obtain ⟨c, _, hc⟩ := Finset.exists_max_image Finset.univ (fun i => Valued.v (x i))
    ⟨j, Finset.mem_univ _⟩
  have hxc : x c ≠ 0 := by
    intro hz
    have hh := hc j (Finset.mem_univ _)
    rw [hz, map_zero] at hh
    exact hj ((Valuation.zero_iff _).mp (le_antisymm hh zero_le))
  refine ⟨c, (x c)⁻¹, inv_ne_zero hxc, ?_, inv_mul_cancel₀ hxc⟩
  intro i
  rw [integral_iff, mul_comm, ← div_eq_mul_inv, Valuation.map_div]
  apply (div_le_one₀ (pos_iff_ne_zero.mpr ((map_ne_zero _).mpr hxc))).mpr
  exact hc i (Finset.mem_univ _)


-- @@ L73-74 verbatim
/-- Coefficientwise integrality, not an arbitrary sublattice. -/
def IntegralVector {ι : Type*} (x : ι → F K) : Prop := ∀ i, Integral (x i)


-- @@ L76-76 verbatim
lemma IntegralVector.zero {ι : Type*} : IntegralVector (0 : ι → F K) := fun _ => integral_zero

-- @@ L77-79 verbatim
lemma IntegralVector.add {ι : Type*} {x y : ι → F K}
    (hx : IntegralVector x) (hy : IntegralVector y) : IntegralVector (x + y) :=
  fun i => (hx i).add (hy i)

-- @@ L80-82 verbatim
lemma IntegralVector.sub {ι : Type*} {x y : ι → F K}
    (hx : IntegralVector x) (hy : IntegralVector y) : IntegralVector (x - y) :=
  fun i => (hx i).sub (hy i)

-- @@ L83-85 verbatim
lemma IntegralVector.smul {ι : Type*} {x : ι → F K} {a : F K}
    (ha : Integral a) (hx : IntegralVector x) : IntegralVector (a • x) :=
  fun i => ha.mul (hx i)


-- @@ L87-90 verbatim
/-- A coordinate functional which is defined integrally on the full ambient
integral lattice. -/
def IntegralFunctional {ι : Type*} (f : (ι → F K) →ₗ[F K] F K) : Prop :=
  ∀ x, IntegralVector x → Integral (f x)


-- @@ L92-100 verbatim
structure IntegralFrame {ι : Type*} (U : Submodule (F K) (ι → F K)) where
  length : ℕ
  vector : Fin length → (ι → F K)
  coordinate : Fin length → ((ι → F K) →ₗ[F K] F K)
  span_eq : Submodule.span (F K) (Set.range vector) = U
  vector_integral : ∀ j, IntegralVector (vector j)
  coordinate_integral : ∀ j, IntegralFunctional (coordinate j)
  pairing : ∀ i j, coordinate i (vector j) = if i = j then 1 else 0
  reduced_independent : LinearIndependent K (fun j => reduce (vector j))



-- @@ L103-207 verbatim
/-- Valuation-adapted Gaussian elimination constructs an integral frame for
any Laurent-series subspace. The coordinate functionals guarantee saturation. -/
theorem exists_integralFrame {ι : Type*} [Fintype ι]
    (U : Submodule (F K) (ι → F K)) : Nonempty (IntegralFrame U) := by
  classical
  suffices ∀ k, ∀ U : Submodule (F K) (ι → F K),
      Module.finrank (F K) U = k → Nonempty (IntegralFrame U) from
    this _ U rfl
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro U hdim
    by_cases hU : U = ⊥
    · subst U
      exact ⟨{ length := 0
               vector := Fin.elim0
               coordinate := Fin.elim0
               span_eq := by simp
               vector_integral := fun j => Fin.elim0 j
               coordinate_integral := fun j => Fin.elim0 j
               pairing := fun i => Fin.elim0 i
               reduced_independent := linearIndependent_empty_type }⟩
    obtain ⟨v, hvU, hv⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU
    obtain ⟨c, u, hu, hxint, hxc⟩ := normalize_vector v hv
    let x : ι → F K := u • v
    have hxU : x ∈ U := U.smul_mem u hvU
    have hxI : IntegralVector x := hxint
    have hxc' : x c = 1 := hxc
    let π : (ι → F K) →ₗ[F K] F K := LinearMap.proj c
    let W := U ⊓ LinearMap.ker π
    have hWU : W < U := by
      refine lt_of_le_of_ne inf_le_left ?_
      intro he
      have hxW : x ∈ W := he.symm ▸ hxU
      have hh : x c = 0 := hxW.2
      exact one_ne_zero (hxc'.symm.trans hh)
    have hdimW : Module.finrank (F K) W < k := by
      rw [← hdim]
      exact Submodule.finrank_lt_finrank_of_lt hWU
    obtain ⟨b⟩ := ih _ hdimW W rfl
    have hbW : ∀ j, b.vector j ∈ W := by
      intro j
      exact b.span_eq.le (Submodule.subset_span ⟨j, rfl⟩)
    have hbc : ∀ j, b.vector j c = 0 := fun j => (hbW j).2
    let φ : Fin b.length → ((ι → F K) →ₗ[F K] F K) := fun j =>
      b.coordinate j - b.coordinate j x • π
    refine ⟨{ length := b.length + 1
              vector := Fin.cons x b.vector
              coordinate := Fin.cons π φ
              span_eq := ?_
              vector_integral := ?_
              coordinate_integral := ?_
              pairing := ?_
              reduced_independent := ?_ }⟩
    · apply le_antisymm
      · apply Submodule.span_le.mpr
        rintro _ ⟨j, rfl⟩
        exact Fin.cases hxU (fun i => (hbW i).1) j
      · intro y hy
        have hr : y - y c • x ∈ W := by
          refine ⟨U.sub_mem hy (U.smul_mem _ hxU), ?_⟩
          change y c - y c * x c = 0
          simp [hxc']
        have hsub : W ≤ Submodule.span (F K) (Set.range (Fin.cons x b.vector)) := by
          apply le_trans b.span_eq.ge
          apply Submodule.span_mono
          rw [Fin.range_cons]
          exact Set.subset_insert x _
        have hxspan : x ∈ Submodule.span (F K) (Set.range (Fin.cons x b.vector)) :=
          Submodule.subset_span ⟨0, by simp⟩
        have hh := (Submodule.span (F K) (Set.range (Fin.cons x b.vector))).add_mem
          (hsub hr) ((Submodule.span (F K) (Set.range (Fin.cons x b.vector))).smul_mem (y c) hxspan)
        simpa only [sub_add_cancel] using hh
    · intro j
      exact Fin.cases hxI b.vector_integral j
    · intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · exact fun y hy => hy c
      · intro y hy
        change Integral (b.coordinate i y - b.coordinate i x * y c)
        exact (b.coordinate_integral i y hy).sub
          ((b.coordinate_integral i x hxI).mul (hy c))
    · intro i j
      refine Fin.cases ?_ (fun a => ?_) i <;>
        refine Fin.cases ?_ (fun z => ?_) j
      · simp [π, hxc']
      · simp [π, hbc, Ne.symm (Fin.succ_ne_zero _)]
      · simp [φ, π, hxc']
      · simp [φ, π, hbc, b.pairing]
    · have he : (fun j : Fin (b.length + 1) => reduce ((Fin.cons x b.vector : Fin (b.length + 1) → (ι → F K)) j)) =
          Fin.cons (reduce x) (fun j => reduce (b.vector j)) := by
        funext j
        exact Fin.cases rfl (fun _ => rfl) j
      rw [he, linearIndependent_finCons]
      refine ⟨b.reduced_independent, ?_⟩
      have hsp : Submodule.span K (Set.range (fun j => reduce (b.vector j))) ≤
          LinearMap.ker (LinearMap.proj c : (ι → K) →ₗ[K] K) := by
        apply Submodule.span_le.mpr
        rintro _ ⟨j, rfl⟩
        change reduction (b.vector j c) = 0
        rw [hbc, reduction_zero]
      intro hx
      have hh : reduction (x c) = 0 := hsp hx
      rw [hxc', reduction_one] at hh
      exact one_ne_zero hh


-- @@ L209-209 verbatim
namespace IntegralFrame


-- @@ L211-211 verbatim
variable {ι : Type*} {U : Submodule (F K) (ι → F K)} (b : IntegralFrame U)


-- @@ L213-219 verbatim
lemma linearIndependent : LinearIndependent (F K) b.vector := by
  classical
  rw [linearIndependent_iff']
  intro s c hc j hj
  have hh := congrArg (b.coordinate j) hc
  simpa only [map_sum, map_smul, b.pairing, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, hj, ite_true, map_zero] using hh


-- @@ L221-222 verbatim
lemma vector_mem (j : Fin b.length) : b.vector j ∈ U := by
  exact b.span_eq.le (Submodule.subset_span ⟨j, rfl⟩)


-- @@ L224-227 verbatim
/-- Full integral-lattice saturation: every integral member has integral
basis coordinates, explicitly given by the constructed functionals. -/
lemma integral_coordinates (x : ι → F K) (hx : IntegralVector x) :
    ∀ j, Integral (b.coordinate j x) := fun j => b.coordinate_integral j x hx


-- @@ L229-237 verbatim
lemma sum_coordinates (x : ι → F K) (hx : x ∈ U) :
    ∑ j, b.coordinate j x • b.vector j = x := by
  classical
  have hx := b.span_eq.ge hx
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (F K)).mp hx
  congr 1
  funext j
  simp only [map_sum, map_smul, b.pairing, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]


-- @@ L239-242 verbatim
lemma length_eq_finrank : b.length = finrank (F K) U := by
  have hh := finrank_span_eq_card b.linearIndependent
  rw [b.span_eq] at hh
  simpa using hh.symm


-- @@ L244-244 verbatim
end IntegralFrame


-- @@ L246-247 verbatim
lemma integral_C (a : K) : Integral (HahnSeries.C a : F K) :=
  ⟨PowerSeries.C a, PowerSeries.coe_C a⟩


-- @@ L249-250 verbatim
@[simp] lemma reduction_C (a : K) : reduction (HahnSeries.C a : F K) = a := by
  simp [reduction, HahnSeries.C_apply]


-- @@ L252-255 verbatim
lemma reduce_sum {ι τ : Type*} (s : Finset τ) (v : τ → (ι → F K)) :
    reduce (∑ j ∈ s, v j) = ∑ j ∈ s, reduce (v j) := by
  ext i
  simp [reduce, reduction]


-- @@ L257-261 verbatim
lemma reduce_smul {ι : Type*} {a : F K} {v : ι → F K}
    (ha : Integral a) (hv : IntegralVector v) :
    reduce (a • v) = reduction a • reduce v := by
  ext i
  exact reduction_mul ha (hv i)


-- @@ L263-268 verbatim
lemma reduce_C_smul {ι : Type*} (a : K) (v : ι → F K) :
    reduce ((HahnSeries.C a : F K) • v) = a • reduce v := by
  ext i
  change reduction (HahnSeries.C a * v i) = a * reduction (v i)
  rw [HahnSeries.C_mul_eq_smul]
  rfl


-- @@ L270-272 verbatim
/-- The reduction uses every integral member of U. -/
def ReducedSet {ι : Type*} (U : Submodule (F K) (ι → F K)) : Set (ι → K) :=
  { y | ∃ x ∈ U, IntegralVector x ∧ reduce x = y }


-- @@ L274-275 verbatim
def reducedSubspace {ι : Type*} (U : Submodule (F K) (ι → F K)) : Submodule K (ι → K) :=
  Submodule.span K (ReducedSet U)


-- @@ L277-300 verbatim
lemma reducedSet_eq_span {ι : Type*} {U : Submodule (F K) (ι → F K)}
    (b : IntegralFrame U) :
    ReducedSet U = (Submodule.span K (Set.range (fun j => reduce (b.vector j))) : Set (ι → K)) := by
  classical
  ext y
  constructor
  · rintro ⟨x, hxU, hxI, rfl⟩
    have he := congrArg reduce (b.sum_coordinates x hxU)
    rw [reduce_sum] at he
    simp_rw [reduce_smul (b.integral_coordinates x hxI _) (b.vector_integral _)] at he
    rw [← he]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨j, rfl⟩)
  · intro hy
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hy
    refine ⟨∑ j, (HahnSeries.C (c j) : F K) • b.vector j, ?_, ?_, ?_⟩
    · exact U.sum_mem fun j _ => U.smul_mem _ (b.vector_mem j)
    · intro i
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_induction _ _ (fun _ _ => Integral.add) integral_zero
      intro j _
      exact (integral_C _).mul (b.vector_integral j i)
    · rw [reduce_sum]
      simp_rw [reduce_C_smul]


-- @@ L302-305 verbatim
lemma reducedSubspace_eq_span {ι : Type*} {U : Submodule (F K) (ι → F K)}
    (b : IntegralFrame U) :
    reducedSubspace U = Submodule.span K (Set.range (fun j => reduce (b.vector j))) := by
  rw [reducedSubspace, reducedSet_eq_span b, Submodule.span_eq]


-- @@ L307-313 verbatim
/-- Full integral reduction preserves dimension. -/
theorem finrank_reducedSubspace {ι : Type*} [Fintype ι]
    (U : Submodule (F K) (ι → F K)) :
    finrank K (reducedSubspace U) = finrank (F K) U := by
  obtain ⟨b⟩ := exists_integralFrame U
  rw [reducedSubspace_eq_span b, finrank_span_eq_card b.reduced_independent,
    Fintype.card_fin, b.length_eq_finrank]



-- @@ L316-322 verbatim
lemma Integral.order_nonneg {x : F K} (hx : Integral x) : 0 ≤ x.order := by
  by_cases hz : x = 0
  · simp [hz]
  apply (HahnSeries.le_order_iff_forall hz).mpr
  have hv := (integral_iff x).mp hx
  have hh : Valued.v x ≤ WithZero.exp (-(0 : ℤ)) := by simpa using hv
  exact (LaurentSeries.valuation_le_iff_coeff_lt_eq_zero K).mp hh


-- @@ L324-326 verbatim
lemma Integral.order_eq_zero {x : F K} (hx : Integral x) (hr : reduction x ≠ 0) :
    x.order = 0 :=
  le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hr) hx.order_nonneg


-- @@ L328-332 verbatim
/-- Multiplication by t^a, written as its identical Laurent monomial. -/
def weightMap {ι : Type*} (w : ι → ℕ) : (ι → F K) →ₗ[F K] (ι → F K) where
  toFun x i := HahnSeries.single (w i : ℤ) 1 * x i
  map_add' := by intros; ext; simp [mul_add]
  map_smul' := by intros; ext; simp [mul_left_comm]


-- @@ L334-341 verbatim
lemma weightMap_injective {ι : Type*} (w : ι → ℕ) :
    Function.Injective (weightMap (K := K) w) := by
  intro x y h
  funext i
  have he := congrFun h i
  change HahnSeries.single (w i : ℤ) (1 : K) * x i =
    HahnSeries.single (w i : ℤ) 1 * y i at he
  exact mul_left_cancel₀ (HahnSeries.single_ne_zero one_ne_zero) he


-- @@ L343-368 verbatim
/-- The key valuation step of order reversal: an integral normalized input
having a nonzero low reduction cannot give a high leading output coefficient. -/
lemma weighted_high_reduction_zero {ι : Type*} (w : ι → ℕ) (A : ℕ)
    (x : ι → F K) (hx : IntegralVector x)
    (hlow : ∃ j, w j ≤ A ∧ reduction (x j) ≠ 0)
    (c : F K) (hc : c ≠ 0)
    (hy : IntegralVector (c • weightMap w x)) :
    ∀ i, A < w i → reduction ((c • weightMap w x) i) = 0 := by
  obtain ⟨j, hjA, hj⟩ := hlow
  have hxj : x j ≠ 0 := by intro he; simp [he] at hj
  have ht (i : ι) : (HahnSeries.single (w i : ℤ) (1 : K) : F K) ≠ 0 :=
    HahnSeries.single_ne_zero one_ne_zero
  have hj0 := (hy j).order_nonneg
  change 0 ≤ (c * (HahnSeries.single (w j : ℤ) 1 * x j)).order at hj0
  rw [HahnSeries.order_mul hc (mul_ne_zero (ht j) hxj),
    HahnSeries.order_mul (ht j) hxj, HahnSeries.order_single one_ne_zero,
    (hx j).order_eq_zero hj, add_zero] at hj0
  intro i hi
  by_cases hxi : x i = 0
  · simp [weightMap, hxi, reduction]
  change (c * (HahnSeries.single (w i : ℤ) 1 * x i)).coeff 0 = 0
  apply HahnSeries.coeff_eq_zero_of_lt_order
  rw [HahnSeries.order_mul hc (mul_ne_zero (ht i) hxi),
    HahnSeries.order_mul (ht i) hxi, HahnSeries.order_single one_ne_zero]
  have hxi0 := (hx i).order_nonneg
  omega


-- @@ L370-398 verbatim
/-- Low coordinates detect reduction throughout U. This controls its full
integral image lattice, not only the images of an arbitrary integral basis. -/
theorem reduction_weighted_supported {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (A : ℕ) (U : Submodule (F K) (ι → F K))
    (hdetect : ∀ x ∈ U, IntegralVector x →
      (∀ i, w i ≤ A → reduction (x i) = 0) → reduce x = 0)
    (y : ι → F K) (hyU : y ∈ U.map (weightMap w)) (hyI : IntegralVector y) :
    ∀ i, A < w i → reduction (y i) = 0 := by
  classical
  obtain ⟨x, hxU, rfl⟩ := hyU
  by_cases hx : x = 0
  · subst x
    simp [weightMap, reduction]
  obtain ⟨c, u, hu, hnI, hnc⟩ := normalize_vector x hx
  have hnU : u • x ∈ U := U.smul_mem u hxU
  have hnI' : IntegralVector (u • x) := hnI
  have hr : reduce (u • x) ≠ 0 := by
    intro he
    have hh := congrFun he c
    change reduction (u * x c) = 0 at hh
    rw [hnc, reduction_one] at hh
    exact one_ne_zero hh
  have hd : ∃ j, w j ≤ A ∧ reduction ((u • x) j) ≠ 0 := by
    by_contra! hh
    exact hr (hdetect _ hnU hnI' hh)
  have he : u⁻¹ • weightMap w (u • x) = weightMap w x := by
    rw [map_smul, smul_smul, inv_mul_cancel₀ hu, one_smul]
  exact he ▸ weighted_high_reduction_zero w A (u • x) hnI' hd u⁻¹
    (inv_ne_zero hu) (he.symm ▸ hyI)



-- @@ L401-419 verbatim
lemma exists_independent_subfamily {V : Type*} [AddCommGroup V] [Module K V]
    {h : ℕ} (v : Fin h → V) :
    ∃ (k : ℕ) (a : Fin k → Fin h), Function.Injective a ∧
      Submodule.span K (Set.range (v ∘ a)) = Submodule.span K (Set.range v) ∧
      LinearIndependent K (v ∘ a) := by
  classical
  obtain ⟨κ, a, ha, hs, hi⟩ := exists_linearIndependent' K v
  let : Fintype κ := Fintype.ofInjective a ha
  let e := (Fintype.equivFin κ).symm
  refine ⟨Fintype.card κ, a ∘ e, ha.comp e.injective, ?_, hi.comp e e.injective⟩
  have he : Set.range (v ∘ a ∘ e) = Set.range (v ∘ a) := by
    ext y
    constructor
    · rintro ⟨j, rfl⟩; exact ⟨e j, rfl⟩
    · rintro ⟨j, rfl⟩
      obtain ⟨r, rfl⟩ := e.surjective j
      exact ⟨r, rfl⟩
  change Submodule.span K (Set.range (v ∘ a ∘ e)) = _
  rw [he, hs]


-- @@ L421-434 verbatim
def IntegralFrame.subframe {ι : Type*} {U : Submodule (F K) (ι → F K)}
    (b : IntegralFrame U) {k : ℕ} (a : Fin k → Fin b.length)
    (ha : Function.Injective a) :
    IntegralFrame (Submodule.span (F K) (Set.range (b.vector ∘ a))) where
  length := k
  vector := b.vector ∘ a
  coordinate := b.coordinate ∘ a
  span_eq := rfl
  vector_integral := fun j => b.vector_integral (a j)
  coordinate_integral := fun j => b.coordinate_integral (a j)
  pairing := by
    intro i j
    simp only [Function.comp_apply, b.pairing, ha.eq_iff]
  reduced_independent := b.reduced_independent.comp a ha


-- @@ L436-440 verbatim
lemma reducedSubspace_mono {ι : Type*} {U V : Submodule (F K) (ι → F K)}
    (h : U ≤ V) : reducedSubspace U ≤ reducedSubspace V := by
  apply Submodule.span_mono
  rintro y ⟨x, hx, hI, rfl⟩
  exact ⟨x, h hx, hI, rfl⟩


-- @@ L442-480 verbatim
/-- Choose an integral-lattice subspace on whose reduction a specified
projection is injective, of dimension equal to that projection's rank. -/
theorem exists_projection_subspace {ι : Type*} [Fintype ι]
    {V : Type*} [AddCommGroup V] [Module K V]
    (U : Submodule (F K) (ι → F K)) (P : (ι → K) →ₗ[K] V) :
    ∃ U' : Submodule (F K) (ι → F K), U' ≤ U ∧
      finrank (F K) U' = finrank K ((reducedSubspace U).map P) ∧
      ∀ x ∈ U', IntegralVector x → P (reduce x) = 0 → reduce x = 0 := by
  classical
  obtain ⟨b⟩ := exists_integralFrame U
  obtain ⟨k, a, ha, hs, hi⟩ := exists_independent_subfamily (K := K)
    (fun j => P (reduce (b.vector j)))
  let b' := b.subframe a ha
  let U' := Submodule.span (F K) (Set.range (b.vector ∘ a))
  refine ⟨U', ?_, ?_, ?_⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    exact b.vector_mem (a j)
  · rw [reducedSubspace_eq_span b, Submodule.map_span, ← Set.range_comp]
    change finrank (F K) U' = finrank K (Submodule.span K
      (Set.range (fun j => P (reduce (b.vector j)))))
    rw [← hs, finrank_span_eq_card hi, Fintype.card_fin]
    exact b'.length_eq_finrank.symm
  · intro x hxU hxI hxP
    have hx : reduce x ∈ Submodule.span K (Set.range (fun j => reduce (b'.vector j))) := by
      change reduce x ∈ (Submodule.span K (Set.range (fun j => reduce (b'.vector j))) : Set (ι → K))
      rw [← reducedSet_eq_span b']
      exact ⟨x, hxU, hxI, rfl⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp hx
    have hh : ∑ j, c j • (P (reduce (b.vector (a j)))) = 0 := by
      rw [← hxP, ← hc, map_sum]
      simp only [map_smul]
      rfl
    have hz := (Fintype.linearIndependent_iff.mp hi) c hh
    rw [← hc]
    apply Finset.sum_eq_zero
    intro i _
    have hci : c i = 0 := hz i
    rw [hci, zero_smul]


-- @@ L482-487 verbatim
/-- Low coordinate projection and its complementary support subspace. -/
def lowProjection {ι : Type*} (w : ι → ℕ) (A : ℕ) :
    (ι → K) →ₗ[K] ({i : ι // w i ≤ A} → K) where
  toFun x i := x i
  map_add' := by intros; rfl
  map_smul' := by intros; rfl


-- @@ L489-493 verbatim
def lowSupported {ι : Type*} (w : ι → ℕ) (A : ℕ) : Submodule K (ι → K) where
  carrier := {x | ∀ i, A < w i → x i = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy i hi; simp [hx i hi, hy i hi]
  smul_mem' := by intro c x hx i hi; simp [hx i hi]


-- @@ L495-505 verbatim
lemma finrank_map_injective {L : Type*} [Field L] {V W : Type*}
    [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    (f : V →ₗ[L] W) (hf : Function.Injective f) (U : Submodule L V) :
    finrank L (U.map f) = finrank L U := by
  have he : (f.domRestrict U).range = U.map f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  rw [← he]
  exact LinearMap.finrank_range_of_inj (hf.comp Subtype.val_injective)


-- @@ L507-527 verbatim
/-- Filtration version of order reversal, before a constant coordinate change.
This uses the whole integral lattice on both sides. -/
theorem weighted_filtration_rank {ι : Type*} [Fintype ι]
    (w : ι → ℕ) (A : ℕ) (U : Submodule (F K) (ι → F K))
    (W : Submodule (F K) (ι → F K)) (hW : U.map (weightMap w) ≤ W) :
    finrank K ((reducedSubspace U).map (lowProjection w A)) ≤
      finrank K ↥(reducedSubspace W ⊓ lowSupported w A) := by
  obtain ⟨U', hU, hdim, hdetect⟩ := exists_projection_subspace U (lowProjection w A)
  have hs : reducedSubspace (U'.map (weightMap w)) ≤ lowSupported w A := by
    apply Submodule.span_le.mpr
    rintro _ ⟨y, hyU, hyI, rfl⟩
    apply reduction_weighted_supported w A U' ?_ y hyU hyI
    intro x hx hxI hh
    apply hdetect x hx hxI
    funext i
    exact hh i i.property
  have hw : reducedSubspace (U'.map (weightMap w)) ≤ reducedSubspace W :=
    reducedSubspace_mono ((Submodule.map_mono hU).trans hW)
  have hh := Submodule.finrank_mono (le_inf hw hs)
  rw [finrank_reducedSubspace, finrank_map_injective _ (weightMap_injective w), hdim] at hh
  exact hh



-- @@ L530-530 verbatim
section ConstantChanges

-- @@ L531-532 verbatim
variable {ι κ τ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Fintype τ] [DecidableEq τ]


-- @@ L534-535 verbatim
def liftMap (P : (ι → K) →ₗ[K] (κ → K)) : (ι → F K) →ₗ[F K] (κ → F K) :=
  Matrix.toLin' ((LinearMap.toMatrix' P).map HahnSeries.C)


-- @@ L537-541 verbatim
lemma liftMap_apply.{v_1, v_2, v_3} {K : Type v_1} [Field K]
  {ι : Type v_2} {κ : Type v_3} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (P : (ι → K) →ₗ[K] κ → K) (x : ι → RationalHitting.LaurentReduction.F K) (j : κ) :
  (RationalHitting.LaurentReduction.liftMap P) x j =
    ∑ i, HahnSeries.C (LinearMap.toMatrix' P j i) * x i := rfl


-- @@ L543-549 verbatim
lemma liftMap_comp.{v_1, v_2, v_3, v_4} {K : Type v_1} [Field K]
  {ι : Type v_2} {κ : Type v_3} {τ : Type v_4} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ] [Fintype τ] [DecidableEq τ] (P : (κ → K) →ₗ[K] τ → K)
  (Q : (ι → K) →ₗ[K] κ → K) :
  RationalHitting.LaurentReduction.liftMap (P ∘ₗ Q) =
    RationalHitting.LaurentReduction.liftMap P ∘ₗ RationalHitting.LaurentReduction.liftMap Q := by
  simp only [liftMap, LinearMap.toMatrix'_comp, Matrix.map_mul, Matrix.toLin'_mul]


-- @@ L551-553 verbatim
lemma liftMap_id : liftMap (LinearMap.id : (ι → K) →ₗ[K] (ι → K)) = LinearMap.id := by
  simp only [liftMap, LinearMap.toMatrix'_id, Matrix.map_one _ (map_zero _) (map_one _),
    Matrix.toLin'_one]


-- @@ L555-561 verbatim
lemma liftMap_integral (P : (ι → K) →ₗ[K] (κ → K)) {x : ι → F K}
    (hx : IntegralVector x) : IntegralVector (liftMap P x) := by
  intro j
  rw [liftMap_apply]
  apply Finset.sum_induction _ _ (fun _ _ => Integral.add) integral_zero
  intro i _
  exact (integral_C _).mul (hx i)


-- @@ L563-576 verbatim
lemma reduction_liftMap.{v_1, v_2, v_3} {K : Type v_1} [Field K]
  {ι : Type v_2} {κ : Type v_3} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  (P : (ι → K) →ₗ[K] κ → K) (x : ι → RationalHitting.LaurentReduction.F K) :
  RationalHitting.LaurentReduction.reduce ((RationalHitting.LaurentReduction.liftMap P) x) =
    P (RationalHitting.LaurentReduction.reduce x) := by
  have hc (a : K) (z : F K) : reduction (HahnSeries.C a * z) = a * reduction z := by
    rw [HahnSeries.C_mul_eq_smul]; rfl
  funext j
  conv_rhs => rw [← Matrix.toLin'_toMatrix' P]
  change reduction (∑ i, HahnSeries.C (LinearMap.toMatrix' P j i) * x i) = _
  simp only [reduction, HahnSeries.coeff_sum] -- constant multiplication commutes with reduction
  change (∑ i, reduction (HahnSeries.C (LinearMap.toMatrix' P j i) * x i)) = _
  simp only [hc]
  rfl


-- @@ L578-592 verbatim
def liftEquiv (E : (ι → K) ≃ₗ[K] (κ → K)) : (ι → F K) ≃ₗ[F K] (κ → F K) :=
  { liftMap E.toLinearMap with
    invFun := liftMap E.symm.toLinearMap
    left_inv := by
      intro x
      have he := liftMap_comp E.symm.toLinearMap E.toLinearMap
      have hh : E.symm.toLinearMap.comp E.toLinearMap = LinearMap.id := by ext x; simp
      rw [hh, liftMap_id] at he
      exact (LinearMap.congr_fun he x).symm
    right_inv := by
      intro x
      have he := liftMap_comp E.toLinearMap E.symm.toLinearMap
      have hh : E.toLinearMap.comp E.symm.toLinearMap = LinearMap.id := by ext x; simp
      rw [hh, liftMap_id] at he
      exact (LinearMap.congr_fun he x).symm }


-- @@ L594-595 verbatim
@[simp] lemma liftEquiv_toLinearMap (E : (ι → K) ≃ₗ[K] (κ → K)) :
    (liftEquiv E).toLinearMap = liftMap E.toLinearMap := rfl


-- @@ L597-600 verbatim
lemma liftEquiv_symm (E : (ι → K) ≃ₗ[K] (κ → K)) :
    (liftEquiv E).symm = liftEquiv E.symm := by
  ext x j
  rfl


-- @@ L602-609 verbatim
lemma integral_liftEquiv_iff (E : (ι → K) ≃ₗ[K] (κ → K)) (x : ι → F K) :
    IntegralVector (liftEquiv E x) ↔ IntegralVector x := by
  constructor
  · intro h
    have hh := liftMap_integral E.symm.toLinearMap h
    change IntegralVector ((liftEquiv E).symm (liftEquiv E x)) at hh
    simpa using hh
  · exact liftMap_integral E.toLinearMap


-- @@ L611-624 verbatim
lemma reducedSubspace_liftEquiv (E : (ι → K) ≃ₗ[K] (κ → K))
    (U : Submodule (F K) (ι → F K)) :
    reducedSubspace (U.map (liftEquiv E).toLinearMap) =
      (reducedSubspace U).map E.toLinearMap := by
  rw [reducedSubspace, reducedSubspace, Submodule.map_span]
  congr 1
  ext y
  constructor
  · rintro ⟨z, ⟨x, hxU, rfl⟩, hzI, rfl⟩
    have hxI := (integral_liftEquiv_iff E x).mp hzI
    exact ⟨reduce x, ⟨x, hxU, hxI, rfl⟩, (reduction_liftMap E.toLinearMap x).symm⟩
  · rintro ⟨z, ⟨x, hxU, hxI, rfl⟩, rfl⟩
    exact ⟨liftEquiv E x, ⟨x, hxU, rfl⟩, liftMap_integral E.toLinearMap hxI,
      reduction_liftMap E.toLinearMap x⟩


-- @@ L626-626 verbatim
end ConstantChanges



-- @@ L629-635 verbatim
/-- Constant coordinates on the input and output may differ (Taylor on the
input, reverse Taylor on the output in the application). -/
def conjugatedWeight {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Ein Eout : (ι → K) ≃ₗ[K] (ι → K)) (w : ι → ℕ) :
    (ι → F K) →ₗ[F K] (ι → F K) :=
  (liftEquiv Eout).symm.toLinearMap.comp
    ((weightMap w).comp (liftEquiv Ein).toLinearMap)


-- @@ L637-640 verbatim
lemma conjugatedWeight_injective {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Ein Eout : (ι → K) ≃ₗ[K] (ι → K)) (w : ι → ℕ) :
    Function.Injective (conjugatedWeight Ein Eout w) :=
  (liftEquiv Eout).symm.injective.comp ((weightMap_injective w).comp (liftEquiv Ein).injective)


-- @@ L642-655 verbatim
theorem conjugated_filtration_rank {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Ein Eout : (ι → K) ≃ₗ[K] (ι → K)) (w : ι → ℕ) (A : ℕ)
    (U W : Submodule (F K) (ι → F K))
    (hW : U.map (conjugatedWeight Ein Eout w) ≤ W) :
    finrank K (((reducedSubspace U).map Ein.toLinearMap).map (lowProjection w A)) ≤
      finrank K ↥((reducedSubspace W).map Eout.toLinearMap ⊓ lowSupported w A) := by
  have hh : (U.map (liftEquiv Ein).toLinearMap).map (weightMap w) ≤
      W.map (liftEquiv Eout).toLinearMap := by
    rintro y ⟨z, ⟨x, hxU, rfl⟩, rfl⟩
    refine ⟨conjugatedWeight Ein Eout w x, hW ⟨x, hxU, rfl⟩, ?_⟩
    exact (liftEquiv Eout).apply_symm_apply _
  have h := weighted_filtration_rank w A (U.map (liftEquiv Ein).toLinearMap)
    (W.map (liftEquiv Eout).toLinearMap) hh
  rwa [reducedSubspace_liftEquiv, reducedSubspace_liftEquiv] at h


-- @@ L657-673 verbatim
lemma finrank_map_add_finrank_inf_ker {L : Type*} [Field L] {V W : Type*}
    [AddCommGroup V] [Module L V] [AddCommGroup W] [Module L W]
    (f : V →ₗ[L] W) (U : Submodule L V) [FiniteDimensional L U] :
    finrank L (U.map f) + finrank L ↥(U ⊓ f.ker) = finrank L U := by
  have hr : (f.domRestrict U).range = U.map f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  have hk : ((f.domRestrict U).ker).map U.subtype = U ⊓ f.ker := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨y.property, hy⟩
    · rintro ⟨hx, hf⟩; exact ⟨⟨x, hx⟩, hf, rfl⟩
  have hd := (f.domRestrict U).finrank_range_add_finrank_ker
  rw [hr, ← finrank_map_injective U.subtype Subtype.val_injective, hk] at hd
  exact hd


-- @@ L675-675 verbatim
end

-- @@ L676-676 verbatim
end RationalHitting.LaurentReduction


-- @@ L678-678 verbatim
end OAI
