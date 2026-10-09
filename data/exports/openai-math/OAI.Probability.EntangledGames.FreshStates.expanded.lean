import OAI.Probability.EntangledGames.BlockStates


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u_X u_Y u_I u_E u_R u_m u_n u_u u_v u_Z


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
open scoped BigOperators MatrixOrder ComplexOrder

-- @@ L9-9 verbatim
open Matrix

-- @@ L10-10 verbatim
namespace ThresholdParallelRepetition.FiniteProbability.Law

-- @@ L11-11 verbatim
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {E : Type u_E} [DecidableEq I]

-- @@ L12-15 verbatim
lemma ignoresRight_update {f : Profile I X Y → E} {i : I} (hf : IgnoresRight f i)
    (z : Profile I X Y) (x : X) (y y' : Y) :
    f (Function.update z i (x,y)) = f (Function.update z i (x,y')) := by
  simpa [updateRight] using hf (Function.update z i (x,y')) y

-- @@ L16-19 verbatim
lemma ignoresLeft_update {f : Profile I X Y → E} {i : I} (hf : IgnoresLeft f i)
    (z : Profile I X Y) (x x' : X) (y : Y) :
    f (Function.update z i (x,y)) = f (Function.update z i (x',y)) := by
  simpa [updateLeft] using hf (Function.update z i (x',y)) x

-- @@ L20-24 verbatim
lemma ignores_update {f : Profile I X Y → E} {i : I} (hL : IgnoresLeft f i) (hR : IgnoresRight f i)
    (z : Profile I X Y) (q : X×Y) : f (Function.update z i q) = f z := by
  obtain ⟨x,y⟩ := q
  rw [ignoresRight_update hR z x y (z i).2]
  exact hL z x

-- @@ L25-25 verbatim
end ThresholdParallelRepetition.FiniteProbability.Law

-- @@ L26-26 verbatim
namespace ThresholdParallelRepetition.MixedExposure

-- @@ L27-27 verbatim
open QuantumSampling FiniteProbability Law

-- @@ L28-29 verbatim
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} [Fintype X] [Fintype Y] [Fintype I] [DecidableEq I]
  [Fintype R] [DecidableEq R] [DecidableEq X] [DecidableEq Y]

-- @@ L30-45 verbatim
omit [DecidableEq R] [DecidableEq X] [DecidableEq Y] in
lemma fresh_avg_weighted (μ : Law (X×Y)) (i : I) (θ : R → Profile I X Y → ℝ)
    (hθL : ∀ r, IgnoresLeft (θ r) i) (hθR : ∀ r, IgnoresRight (θ r) i)
    (g : R → Profile I X Y → ℝ) :
    μ.avg (fun q => ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z*g r (Function.update z i q))) =
      ∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z*g r z) := by
  rw [avg_sum]
  apply Finset.sum_congr rfl; intro r _
  have he : (fun q => (pi (fun _ : I => μ)).avg (fun z => θ r z*g r (Function.update z i q))) =
      (fun q => (pi (fun _ : I => μ)).avg (fun z => θ r (Function.update z i q)*g r (Function.update z i q))) := by
    funext q
    congr 1
    funext z
    rw [ignores_update (hθL r) (hθR r)]
  rw [he, avg_comm]
  exact pi_avg_update _ i (fun z => θ r z*g r z)


-- @@ L47-47 verbatim
variable {m : Type u_m} {n : Type u_n} {u : Type u_u} {v : Type u_v} [Fintype m] [Fintype n] [Fintype u] [Fintype v]

-- @@ L48-53 verbatim
def stateAt (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ) (p : ℝ) (i : I)
    (C : Matrix m n ℂ) (U : R → Profile I X Y → Matrix u m ℂ)
    (V : R → Profile I X Y → Matrix v n ℂ) (q : X×Y) :
    Matrix (u×(R×Profile I X Y)) (v×(R×Profile I X Y)) ℂ :=
  weightedBlock (fun t : R×Profile I X Y => (pi (fun _ : I => μ)).weight t.2 * θ t.1 t.2 / p)
    (fun t => U t.1 (Function.update t.2 i q)*C*(V t.1 (Function.update t.2 i q))ᵀ)


-- @@ L55-66 verbatim
lemma stateAt_norm (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ)
    (hθ : ∀ r z, 0 ≤ θ r z) {p : ℝ} (hp : 0 < p) (i : I)
    (C : Matrix m n ℂ) (U : R → Profile I X Y → Matrix u m ℂ)
    (V : R → Profile I X Y → Matrix v n ℂ) (q : X×Y) :
    hsSq (stateAt μ θ p i C U V q) = (1/p)*∑ r, (pi (fun _ : I => μ)).avg
      (fun z => θ r z * hsSq (U r (Function.update z i q)*C*(V r (Function.update z i q))ᵀ)) := by
  rw [stateAt, hsSq_weightedBlock _ (fun t => div_nonneg (mul_nonneg ((pi _).nonneg _) (hθ _ _)) hp.le),
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro r _
  simp only [avg, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro z _
  ring


-- @@ L68-81 verbatim
lemma stateAt_distance_left (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ)
    (hθ : ∀ r z, 0 ≤ θ r z) {p : ℝ} (hp : 0 < p) (i : I)
    (C : Matrix m n ℂ) (U U' : R → Profile I X Y → Matrix u m ℂ)
    (V : R → Profile I X Y → Matrix v n ℂ) (q : X×Y) :
    hsSq (stateAt μ θ p i C U V q-stateAt μ θ p i C U' V q) =
      (1/p)*∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z * hsSq
        ((U r (Function.update z i q)-U' r (Function.update z i q))*C*(V r (Function.update z i q))ᵀ)) := by
  simp only [stateAt]
  rw [hsSq_weightedBlock_sub _ (fun t => div_nonneg (mul_nonneg ((pi _).nonneg _) (hθ _ _)) hp.le),
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro r _
  simp only [avg, smul_eq_mul, Finset.mul_sum, Matrix.sub_mul]
  apply Finset.sum_congr rfl; intro z _
  ring


-- @@ L83-96 verbatim
lemma stateAt_distance_right (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ)
    (hθ : ∀ r z, 0 ≤ θ r z) {p : ℝ} (hp : 0 < p) (i : I)
    (C : Matrix m n ℂ) (U : R → Profile I X Y → Matrix u m ℂ)
    (V V' : R → Profile I X Y → Matrix v n ℂ) (q : X×Y) :
    hsSq (stateAt μ θ p i C U V q-stateAt μ θ p i C U V' q) =
      (1/p)*∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z * hsSq
        (U r (Function.update z i q)*C*(V r (Function.update z i q)-V' r (Function.update z i q))ᵀ)) := by
  simp only [stateAt]
  rw [hsSq_weightedBlock_sub _ (fun t => div_nonneg (mul_nonneg ((pi _).nonneg _) (hθ _ _)) hp.le),
    Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro r _
  simp only [avg, smul_eq_mul, Finset.mul_sum, Matrix.transpose_sub, Matrix.mul_sub]
  apply Finset.sum_congr rfl; intro z _
  ring

-- @@ L97-106 verbatim
omit [Fintype R] [Fintype u] [Fintype v] in
lemma stateAt_right_local (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ) (p : ℝ) (i : I)
    (C : Matrix m n ℂ) (U : R → Profile I X Y → Matrix u m ℂ)
    (V : R → Profile I X Y → Matrix v n ℂ)
    (hU : ∀ r, IgnoresRight (U r) i) (hV : ∀ r, IgnoresRight (V r) i)
    (x : X) (y y' : Y) : stateAt μ θ p i C U V (x,y) = stateAt μ θ p i C U V (x,y') := by
  unfold stateAt
  congr 1
  funext t
  rw [ignoresRight_update (hU t.1) t.2 x y y', ignoresRight_update (hV t.1) t.2 x y y']


-- @@ L108-117 verbatim
omit [Fintype R] [Fintype u] [Fintype v] in
lemma stateAt_left_local (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ) (p : ℝ) (i : I)
    (C : Matrix m n ℂ) (U : R → Profile I X Y → Matrix u m ℂ)
    (V : R → Profile I X Y → Matrix v n ℂ)
    (hU : ∀ r, IgnoresLeft (U r) i) (hV : ∀ r, IgnoresLeft (V r) i)
    (x x' : X) (y : Y) : stateAt μ θ p i C U V (x,y) = stateAt μ θ p i C U V (x',y) := by
  unfold stateAt
  congr 1
  funext t
  rw [ignoresLeft_update (hU t.1) t.2 x x' y, ignoresLeft_update (hV t.1) t.2 x x' y]


-- @@ L119-119 verbatim
variable [DecidableEq m] [DecidableEq n] [DecidableEq u] [DecidableEq v]

-- @@ L120-130 verbatim
omit [DecidableEq m] [DecidableEq n] in
lemma stateAt_norm_gram (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ)
    (hθ : ∀ r z, 0 ≤ θ r z) {p : ℝ} (hp : 0 < p) (i : I)
    (C : Matrix m n ℂ) (U : R → Profile I X Y → Matrix u m ℂ)
    (V : R → Profile I X Y → Matrix v n ℂ)
    (F : R → Profile I X Y → Matrix m m ℂ) (H : R → Profile I X Y → Matrix n n ℂ)
    (hU : ∀ r z, (U r z)ᴴ*U r z=F r z) (hV : ∀ r z, (V r z)ᴴ*V r z=H r z) (q : X×Y) :
    hsSq (stateAt μ θ p i C U V q) = (1/p)*∑ r, (pi (fun _ : I => μ)).avg
      (fun z => θ r z*prob C (F r (Function.update z i q)) (H r (Function.update z i q))) := by
  rw [stateAt_norm μ θ hθ hp]
  simp only [← prob_gram, hU, hV]

-- @@ L131-131 verbatim
end ThresholdParallelRepetition.MixedExposure


-- @@ L133-133 verbatim
end


-- @@ L135-135 verbatim
noncomputable section

-- @@ L136-136 verbatim
open scoped BigOperators MatrixOrder ComplexOrder

-- @@ L137-137 verbatim
open Matrix

-- @@ L138-138 verbatim
namespace ThresholdParallelRepetition.MixedExposure

-- @@ L139-139 verbatim
open QuantumSampling Resolvent OperatorEntropy FiniteProbability Law

-- @@ L140-142 verbatim
variable {X : Type u_X} {Y : Type u_Y} {I : Type u_I} {R : Type u_R} {m : Type u_m} {n : Type u_n} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  [Fintype R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]


-- @@ L144-171 verbatim
omit [DecidableEq m] [DecidableEq n] in
lemma chain_fixed_mass (μ : Law (X×Y)) (x₀ : X) (y₀ : Y) (l : List I) (hN : l.Nodup)
    (C : Matrix m n ℂ) (F : R → Profile I X Y → Matrix m m ℂ)
    (H : R → Profile I X Y → Matrix n n ℂ)
    (hF : ∀ r i, IgnoresRight (F r) i) (hH : ∀ r i, IgnoresLeft (H r) i)
    (θ : R → Profile I X Y → ℝ)
    (hθL : ∀ r i, i ∈ l → IgnoresLeft (θ r) i) (hθR : ∀ r i, i ∈ l → IgnoresRight (θ r) i)
    (p : ℝ) (j : Fin l.length) (q : X×Y) :
    massAt μ θ p l[j.val] C (chainLeft μ x₀ l F (j+1)) (chainRight μ y₀ l H j) q =
      massAt μ θ p l[j.val] C F H q := by
  unfold massAt
  congr 1
  apply Finset.sum_congr rfl; intro r _
  have hθi (z : Profile I X Y) : θ r (Function.update z l[j.val] q) = θ r z :=
    ignores_update (hθL r _ (List.getElem_mem j.isLt)) (hθR r _ (List.getElem_mem j.isLt)) z q
  have he (G : Profile I X Y → ℝ) :
      (pi (fun _ : I => μ)).avg (fun z => θ r z*G (Function.update z l[j.val] q)) =
      (pi (fun _ : I => μ)).avg (fun z => θ r (Function.update z l[j.val] q)*G (Function.update z l[j.val] q)) := by
    simp only [hθi]
  rw [he (fun z => prob C (chainLeft μ x₀ l F (j+1) r z) (chainRight μ y₀ l H j r z)),
    he (fun z => prob C (F r z) (H r z))]
  apply fixed_mixed_pairing μ x₀ y₀ _ _ _ C (F r) (H r)
    (fun i _ => hF r i) (fun i _ => hH r i) (θ r)
    (fun i hi => hθL r i (List.mem_of_mem_drop hi))
    (fun i hi => hθR r i (List.mem_of_mem_take (List.mem_reverse.mp hi)))
    l[j.val] (list_fresh_not_suffix l hN j j.isLt) (list_fresh_not_prefix l hN j j.isLt) q
  intro i hi
  exact list_suffix_prefix_disjoint l hN j i (List.drop_subset_drop_left l (Nat.le_succ j) hi)


-- @@ L173-175 verbatim
def eventDensity (θ : R → Profile I X Y → ℝ) (p : ℝ) (C : Matrix m n ℂ)
    (F : R → Profile I X Y → Matrix m m ℂ) (H : R → Profile I X Y → Matrix n n ℂ)
    (z : Profile I X Y) : ℝ := (1/p)*∑ r, θ r z*prob C (F r z) (H r z)


-- @@ L177-188 verbatim
omit [DecidableEq X] [DecidableEq Y] [DecidableEq m] [DecidableEq n] in
lemma massAt_eq_coordDensity (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ) (p : ℝ)
    (C : Matrix m n ℂ) (F : R → Profile I X Y → Matrix m m ℂ)
    (H : R → Profile I X Y → Matrix n n ℂ) (i : I)
    (hθL : ∀ r, IgnoresLeft (θ r) i) (hθR : ∀ r, IgnoresRight (θ r) i) (q : X×Y) :
    massAt μ θ p i C F H q = coordDensity (fun _ : I => μ) (eventDensity θ p C F H) i q := by
  unfold massAt coordDensity eventDensity
  simp only [ignores_update (hθL _) (hθR _)]
  rw [show (fun z => (1/p)*∑ r, θ r z*prob C (F r (Function.update z i q)) (H r (Function.update z i q))) =
    (fun z => (1/p) • ∑ r, θ r z*prob C (F r (Function.update z i q)) (H r (Function.update z i q))) from rfl,
    avg_smul, avg_sum]
  rfl


-- @@ L190-197 verbatim
omit [Fintype X] [Fintype Y] [Fintype I] [DecidableEq X] [DecidableEq Y] [DecidableEq I] [DecidableEq m] [DecidableEq n] in
lemma eventDensity_nonneg (θ : R → Profile I X Y → ℝ) (hθ : ∀ r z, 0 ≤ θ r z)
    {p : ℝ} (hp : 0 < p) (C : Matrix m n ℂ)
    (F : R → Profile I X Y → Matrix m m ℂ) (H : R → Profile I X Y → Matrix n n ℂ)
    (hF : ∀ r z, (F r z).PosSemidef) (hH : ∀ r z, (H r z).PosSemidef) (z : Profile I X Y) :
    0 ≤ eventDensity θ p C F H z :=
  mul_nonneg (div_nonneg zero_le_one hp.le)
    (Finset.sum_nonneg (fun r _ => mul_nonneg (hθ r z) (prob_nonneg (hF r z) (hH r z))))


-- @@ L199-206 verbatim
omit [DecidableEq X] [DecidableEq Y] [DecidableEq m] [DecidableEq n] in
lemma eventDensity_total (μ : Law (X×Y)) (θ : R → Profile I X Y → ℝ)
    {p : ℝ} (hp : 0 < p) (C : Matrix m n ℂ)
    (F : R → Profile I X Y → Matrix m m ℂ) (H : R → Profile I X Y → Matrix n n ℂ)
    (hm : (∑ r, (pi (fun _ : I => μ)).avg (fun z => θ r z*prob C (F r z) (H r z))) = p) :
    (pi (fun _ : I => μ)).avg (eventDensity θ p C F H) = 1 := by
  change (pi (fun _ : I => μ)).avg (fun z => (1/p) • ∑ r, θ r z*prob C (F r z) (H r z)) = 1
  rw [avg_smul, avg_sum, hm, smul_eq_mul, one_div, inv_mul_cancel₀ hp.ne']

-- @@ L207-207 verbatim
end ThresholdParallelRepetition.MixedExposure


-- @@ L209-209 verbatim
end


-- @@ L211-211 verbatim
noncomputable section

-- @@ L212-212 verbatim
open scoped BigOperators MatrixOrder ComplexOrder

-- @@ L213-213 verbatim
open Matrix

-- @@ L214-214 verbatim
namespace ThresholdParallelRepetition.QuantumSampling

-- @@ L215-215 verbatim
open FiniteProbability Law ScalarEntropy

-- @@ L216-216 verbatim
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

-- @@ L217-217 verbatim
def basisState (i : m) (j : n) : Matrix m n ℂ := fun a b => if a=i ∧ b=j then 1 else 0

-- @@ L218-223 verbatim
lemma hsSq_basisState (i : m) (j : n) : hsSq (basisState i j) = 1 := by
  have he : basisState i j = fun a b => if a=i then (if b=j then 1 else 0) else 0 := by
    ext a b
    by_cases h : a=i <;> simp [basisState, h]
  rw [he]
  simp [hsSq, apply_ite]


-- @@ L225-228 verbatim
omit [DecidableEq m] [DecidableEq n] in
lemma hsSq_triangle (C D E : Matrix m n ℂ) : hsSq (C-E) ≤ 2*(hsSq (C-D)+hsSq (D-E)) := by
  have h := hsSq_add_le (C-D) (D-E)
  simpa only [sub_add_sub_cancel] using h


-- @@ L230-239 verbatim
omit [DecidableEq m] [DecidableEq n] in
lemma avg_unitize_triangle {Z : Type u_Z} [Fintype Z] (μ : Law Z)
    (C D : Z → Matrix m n ℂ) (E : Matrix m n ℂ) :
    μ.avg (fun z => hsSq (C z-unitize (D z) E)) ≤
      2*(μ.avg (fun z => hsSq (C z-D z))+μ.avg (fun z => hsSq (D z-unitize (D z) E))) := by
  have h := μ.avg_mono (fun z => hsSq_triangle (C z) (D z) (unitize (D z) E))
  apply h.trans_eq
  change μ.avg (fun z => (2:ℝ) • (hsSq (C z-D z)+hsSq (D z-unitize (D z) E))) = _
  rw [avg_smul, avg_add]
  rfl


-- @@ L241-241 verbatim
variable {X : Type u_X} {Y : Type u_Y} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

-- @@ L242-253 verbatim
omit [DecidableEq m] [DecidableEq n] [DecidableEq X] in
lemma first_unitize_cost (μ : Law (X×Y)) (y₀ : Y) (f : X×Y → ℝ)
    (hf : ∀ z, 0 ≤ f z) (ht : μ.avg f = 1) (M : X → Matrix m n ℂ)
    (hM : ∀ x, hsSq (M x) = (μ.givenFirst y₀ x).avg (fun y => f (x,y)))
    (E : Matrix m n ℂ) (hE : hsSq E = 1) :
    μ.avg (fun z => hsSq (M z.1-unitize (M z.1) E)) ≤ μ.avg (fun z => f z*Real.log (f z)) := by
  rw [disintegrate_first μ y₀]
  simp only [avg_const, unitize_distance _ _ hE, hM]
  have hmean : μ.first.avg (fun x => (μ.givenFirst y₀ x).avg (fun y => f (x,y))) = 1 := by
    rw [← disintegrate_first]; exact ht
  exact (avg_hellinger_le_entropy μ.first _ (fun x => (μ.givenFirst y₀ x).avg_nonneg (fun y => hf (x,y))) hmean).trans
    (first_density_entropy_le μ y₀ f hf)


-- @@ L255-266 verbatim
omit [DecidableEq m] [DecidableEq n] [DecidableEq Y] in
lemma second_unitize_cost (μ : Law (X×Y)) (x₀ : X) (f : X×Y → ℝ)
    (hf : ∀ z, 0 ≤ f z) (ht : μ.avg f = 1) (N : Y → Matrix m n ℂ)
    (hN : ∀ y, hsSq (N y) = (μ.givenSecond x₀ y).avg (fun x => f (x,y)))
    (E : Matrix m n ℂ) (hE : hsSq E = 1) :
    μ.avg (fun z => hsSq (N z.2-unitize (N z.2) E)) ≤ μ.avg (fun z => f z*Real.log (f z)) := by
  rw [disintegrate_second μ x₀]
  simp only [avg_const, unitize_distance _ _ hE, hN]
  have hmean : μ.second.avg (fun y => (μ.givenSecond x₀ y).avg (fun x => f (x,y))) = 1 := by
    rw [← disintegrate_second]; exact ht
  exact (avg_hellinger_le_entropy μ.second _ (fun y => (μ.givenSecond x₀ y).avg_nonneg (fun x => hf (x,y))) hmean).trans
    (second_density_entropy_le μ x₀ f hf)

-- @@ L267-267 verbatim
end ThresholdParallelRepetition.QuantumSampling


-- @@ L269-269 verbatim
end


-- @@ L271-271 verbatim
end OAI
