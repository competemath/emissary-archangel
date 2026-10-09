import OAI.Analysis.Steinitz.FilteredBody


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
/-! Normalized predictors and backward-forward shifted walks. -/


-- @@ L7-7 verbatim
section


-- @@ L9-9 verbatim
open Matrix GaussianTail

-- @@ L10-10 verbatim
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace

-- @@ L11-11 verbatim
namespace EuclideanSteinitz.Filter

-- @@ L12-12 verbatim
variable {ι ν : Type*} [Fintype ι] [DecidableEq ι] [Fintype ν] [DecidableEq ν]


-- @@ L14-14 verbatim
noncomputable def initialMatrix (ι ν : Type*) [DecidableEq ι] : Matrix ι (ι⊕ν) ℝ := Matrix.fromCols 1 0

-- @@ L15-17 verbatim
omit [DecidableEq ν] in
lemma initialMatrix_coisometry : initialMatrix ι ν*(initialMatrix ι ν).transpose=1 := by
  simp [initialMatrix,Matrix.transpose_fromCols,Matrix.fromCols_mul_fromRows]

-- @@ L18-23 verbatim
lemma initialMatrix_eval (x : EuclideanSpace ℝ (ι⊕ν)) (hx : ∀ i,x (Sum.inl i)=0) :
    matrixMap (initialMatrix ι ν) x=0 := by
  apply WithLp.ofLp_injective
  change (Matrix.fromCols 1 0)*ᵥx=0
  simp only [Matrix.fromCols_mulVec,Matrix.one_mulVec,Matrix.zero_mulVec,add_zero]
  exact funext hx


-- @@ L25-26 verbatim
noncomputable def familySteps {n : ℕ} (b : Fin n → ι → ℝ) : List (Step ι (ι⊕Fin n)) :=
  List.ofFn (fun i => symmetricStep (b i) (Sum.inr i))

-- @@ L27-29 verbatim
noncomputable def familyPredictor {n : ℕ} (b : Fin n → ι → ℝ) (i : Fin n) : ι⊕Fin n → ℝ :=
  noiseRow ((predictorRows (initialMatrix ι (Fin n)) (familySteps b))[i.val]'
    (by rw [predictorRows_length]; simpa only [familySteps,List.length_ofFn] using i.isLt))


-- @@ L31-35 verbatim
lemma familySteps_good {n : ℕ} {b : Fin n → ι → ℝ} (hb : ∀ i,vectorMass (b i)<1) :
    ∀ p∈familySteps b,p.Good := by
  intro p hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  exact symmetricStep_good (hb i) _

-- @@ L36-40 verbatim
lemma familySteps_symmetric {n : ℕ} (b : Fin n → ι → ℝ) :
    ∀ p∈familySteps b,p.C=symmetricContraction p.b := by
  intro p hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  rfl

-- @@ L41-45 verbatim
lemma familySteps_mass {n : ℕ} {b : Fin n → ι → ℝ} {B : ℝ} (hb : ∀ i,vectorMass (b i)≤B) :
    ∀ p∈familySteps b,vectorMass p.b≤B := by
  intro p hp
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  exact hb i

-- @@ L46-49 verbatim
lemma familySteps_fresh {n : ℕ} (b : Fin n → ι → ℝ) : Fresh (initialMatrix ι (Fin n)) (familySteps b) := by
  intro p hp k
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hp
  simp [initialMatrix,symmetricStep]

-- @@ L50-52 verbatim
lemma familySteps_nodup {n : ℕ} (b : Fin n → ι → ℝ) : ((familySteps b).map Step.j).Nodup := by
  simpa only [familySteps,List.map_ofFn,Function.comp_def,symmetricStep] using
    (List.nodup_ofFn.mpr (Sum.inr_injective : Function.Injective (Sum.inr : Fin n → ι⊕Fin n)))


-- @@ L54-58 verbatim
lemma familyPredictor_form {n : ℕ} (b : Fin n → ι → ℝ) (i : Fin n) :
    familyPredictor b i=noiseRow (rawRow (run (initialMatrix ι (Fin n)) ((familySteps b).take i.val)) (b i)) := by
  unfold familyPredictor
  rw [predictorRows_get _ _ _ (by simpa only [familySteps,List.length_ofFn] using i.isLt)]
  simp only [familySteps,List.getElem_ofFn,symmetricStep]


-- @@ L60-64 verbatim
lemma familyPredictor_future {n : ℕ} (b : Fin n → ι → ℝ) (i l : Fin n) (hil : i≤l) :
    familyPredictor b i (Sum.inr l)=0 := by
  have hh := predictor_future_zero (familySteps_fresh b) (familySteps_nodup b) i.val l.val hil
    (by simpa only [familySteps,List.length_ofFn] using l.isLt)
  simpa only [familyPredictor,noiseRow,Sum.elim_inr,familySteps,List.getElem_ofFn,symmetricStep] using hh


-- @@ L66-72 verbatim
lemma familyPredictor_mass {n : ℕ} {b : Fin n → ι → ℝ} (hb : ∀ i,vectorMass (b i)<1) (i : Fin n) :
    vectorMass (familyPredictor b i)≤vectorMass (b i) := by
  apply (noiseRow_mass _).trans
  have hh := predictor_row_bound (initialMatrix_coisometry (ι := ι) (ν := Fin n))
    (familySteps_good hb) (familySteps_fresh b) (familySteps_nodup b) i.val
    (by simpa only [familySteps,List.length_ofFn] using i.isLt)
  simpa only [familySteps,List.getElem_ofFn,symmetricStep] using hh


-- @@ L74-77 verbatim
lemma sum_getElem_of_length {α : Type*} (L : List α) {n : ℕ} (hL : L.length=n) (f : α → ℝ) :
    (∑ i : Fin n,f (L[i.val]'(by omega)))=(L.map f).sum := by
  subst n
  rw [← List.sum_ofFn,List.ofFn_getElem_eq_map]


-- @@ L79-90 verbatim
lemma familyPredictor_column {n : ℕ} {b : Fin n → ι → ℝ} (hb : ∀ i,vectorMass (b i)<1)
    {B : ℝ} (hB : 0≤B) (hbB : ∀ i,vectorMass (b i)≤B) (k : ι⊕Fin n) :
    (∑ i,(familyPredictor b i k)^2)≤B := by
  cases k with
  | inl k => simpa only [familyPredictor,noiseRow,Sum.elim_inl,zero_pow (by norm_num : 2≠0),Finset.sum_const_zero] using hB
  | inr k =>
    have hh := predictor_column_bound (familySteps_symmetric b) (familySteps_mass (fun i => (hb i).le))
      (familySteps_fresh b) (familySteps_nodup b) hB (familySteps_mass hbB) (Sum.inr k)
      (by intro i; simp [initialMatrix])
    have hlen : (predictorRows (initialMatrix ι (Fin n)) (familySteps b)).length=n := by
      rw [predictorRows_length]; simp [familySteps]
    simpa only [familyPredictor,noiseRow,Sum.elim_inr,sum_getElem_of_length _ hlen (fun m => m (Sum.inr k)^2)] using hh


-- @@ L92-92 verbatim
noncomputable def signingScale : ℝ := 1/(8*bodyScale*GaussianAR.slabRadius)

-- @@ L93-93 verbatim
lemma signingScale_pos : 0 < signingScale := div_pos (by norm_num) (mul_pos (mul_pos (by norm_num) bodyScale_pos) GaussianAR.slabRadius_pos)

-- @@ L94-98 verbatim
lemma signingScale_lt_one : signingScale<1 := by
  unfold signingScale
  apply (div_lt_one (mul_pos (mul_pos (by norm_num) bodyScale_pos) GaussianAR.slabRadius_pos)).mpr
  have hs : 1≤GaussianAR.slabRadius := by norm_num [GaussianAR.slabRadius]
  nlinarith [bodyScale_ge_one]

-- @@ L99-102 verbatim
lemma signingScale_cancel : 2*bodyScale*GaussianAR.slabRadius*signingScale=1/4 := by
  unfold signingScale
  field_simp [bodyScale_pos.ne',GaussianAR.slabRadius_pos.ne']
  ring


-- @@ L104-105 verbatim
noncomputable def normalizedPredictor {n : ℕ} (b : Fin n → ι → ℝ) (i : Fin n) : Matrix Unit (ι⊕Fin n) ℝ :=
  fun _ k => familyPredictor b i k / signingScale


-- @@ L107-113 verbatim
lemma normalizedPredictor_mass {n : ℕ} {b : Fin n → ι → ℝ}
    (hb : ∀ i,vectorMass (b i)≤ signingScale^2) (i : Fin n) : squareMass (normalizedPredictor b i)≤1 := by
  have hlt : ∀ i,vectorMass (b i)<1 := fun i => (hb i).trans_lt (by nlinarith [signingScale_pos,signingScale_lt_one])
  change (∑ _ : Unit,∑ k,(familyPredictor b i k/signingScale)^2)≤1
  simp only [Fintype.sum_unique,div_pow,← Finset.sum_div]
  apply (div_le_one (sq_pos_of_pos signingScale_pos)).mpr
  exact (familyPredictor_mass hlt i).trans (hb i)


-- @@ L115-121 verbatim
lemma normalizedPredictor_column {n : ℕ} {b : Fin n → ι → ℝ}
    (hb : ∀ i,vectorMass (b i)≤ signingScale^2) (k : ι⊕Fin n) :
    (∑ i,(normalizedPredictor b i () k)^2)≤1 := by
  have hlt : ∀ i,vectorMass (b i)<1 := fun i => (hb i).trans_lt (by nlinarith [signingScale_pos,signingScale_lt_one])
  simp only [normalizedPredictor,div_pow,← Finset.sum_div]
  apply (div_le_one (sq_pos_of_pos signingScale_pos)).mpr
  exact familyPredictor_column hlt (sq_nonneg _) hb k


-- @@ L123-127 verbatim
lemma normalizedPredictor_norm {n : ℕ} (b : Fin n → ι → ℝ) (i : Fin n) (x : EuclideanSpace ℝ (ι⊕Fin n)) :
    ‖matrixMap (normalizedPredictor b i) x‖=|rowMap (familyPredictor b i) x|/signingScale := by
  change ‖matrixMap (fun _ : Unit => fun k => familyPredictor b i k/signingScale) x‖=_
  rw [rowMatrix_norm,rowMap_apply,rowMap_apply]
  simp only [dotProduct,div_mul_eq_mul_div,← Finset.sum_div,abs_div,abs_of_pos signingScale_pos]


-- @@ L129-129 verbatim
end EuclideanSteinitz.Filter


-- @@ L131-131 verbatim
end


-- @@ L133-133 verbatim
section


-- @@ L135-135 verbatim
open MeasureTheory Set

-- @@ L136-136 verbatim
namespace ShiftedSections

-- @@ L137-137 verbatim
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


-- @@ L139-139 verbatim
noncomputable def clip (u : ℝ) : ℝ := max (-(1/4)) (min u (1/4))

-- @@ L140-142 verbatim
lemma clip_bound (u : ℝ) : |clip u|≤1/4 := by
  rw [abs_le]
  exact ⟨le_max_left _ _,max_le (by norm_num) (min_le_right _ _)⟩

-- @@ L143-145 verbatim
lemma clip_eq {u : ℝ} (hu : |u|<1/4) : clip u=u := by
  obtain ⟨hl,hr⟩ := abs_lt.mp hu
  rw [clip,min_eq_left hr.le,max_eq_right hl.le]


-- @@ L147-155 verbatim
omit [Fintype ι] in
lemma walk_linear_invariant {n : ℕ} (j : Fin n → ι) (q : Fin n → Coeff (ι := ι) → ℝ)
    (ε : Fin n → ℝ) (x : Coeff (ι := ι)) (f : Coeff (ι := ι) →L[ℝ] ℝ)
    (hf : ∀ i,f (EuclideanSpace.single (j i) 1)=0) : f (walk j q ε x)=f x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [walk,ih (fun i => j i.succ) (fun i => q i.succ) (fun i => ε i.succ) _ (fun i => hf i.succ)]
    simp only [map_add,map_smul,hf 0,smul_zero,add_zero]


-- @@ L157-161 verbatim
omit [Fintype ι] in
lemma walk_coordinate_outside {n : ℕ} (j : Fin n → ι) (q : Fin n → Coeff (ι := ι) → ℝ)
    (ε : Fin n → ℝ) (x : Coeff (ι := ι)) (k : ι) (hk : ∀ i,k≠j i) :
    (walk j q ε x) k=x k := by
  exact walk_linear_invariant j q ε x (EuclideanSpace.proj k) (by intro i; simp [hk i])


-- @@ L163-202 verbatim
omit [Fintype ι] in
lemma walk_coordinate_equations {n : ℕ} (j : Fin n → ι) (hj : Function.Injective j)
    (m : Fin n → Coeff (ι := ι) →L[ℝ] ℝ)
    (hm : ∀ i l : Fin n,i≤l → m i (EuclideanSpace.single (j l) 1)=0)
    (ε : Fin n → ℝ) (x : Coeff (ι := ι)) :
    ∀ i,(walk j (fun i y => clip (m i y)) ε x) (j i)=x (j i)+clip (m i (walk j (fun i y => clip (m i y)) ε x))+ε i := by
  induction n generalizing x with
  | zero => intro i; exact i.elim0
  | succ n ih =>
    let jt := fun i : Fin n => j i.succ
    let mt := fun i : Fin n => m i.succ
    let et := fun i : Fin n => ε i.succ
    let x' := x+(clip (m 0 x)+ε 0) • EuclideanSpace.single (j 0) 1
    have htail : Function.Injective jt := fun i l h => Fin.succ_injective n (hj h)
    have hmt : ∀ i l : Fin n,i≤l → mt i (EuclideanSpace.single (jt l) 1)=0 :=
      fun i l h => hm i.succ l.succ (Fin.succ_le_succ_iff.mpr h)
    have hx0 : ∀ i : Fin n,j 0≠jt i := by
      intro i he
      exact Fin.succ_ne_zero i (hj he).symm
    have hout := walk_coordinate_outside jt (fun i y => clip (mt i y)) et x' (j 0) hx0
    have hinv := walk_linear_invariant jt (fun i y => clip (mt i y)) et x' (m 0)
      (fun i => hm 0 i.succ (Fin.zero_le _))
    have hzero : m 0 x'=m 0 x := by
      simp only [x',map_add,map_smul,hm 0 0 le_rfl,smul_zero,add_zero]
    have hrec := ih jt htail mt hmt et x'
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · change (walk jt (fun i y => clip (mt i y)) et x') (j 0) = _
      rw [hout]
      change x' (j 0)=x (j 0)+clip (m 0 (walk jt (fun i y => clip (mt i y)) et x'))+ε 0
      rw [hinv,hzero]
      simp only [x',PiLp.add_apply,PiLp.smul_apply,PiLp.single_apply,ite_true,smul_eq_mul,mul_one]
      ring
    · change (walk jt (fun i y => clip (mt i y)) et x') (jt i)= _
      rw [hrec i]
      have he : x' (jt i)=x (j i.succ) := by
        simp only [x',PiLp.add_apply,PiLp.smul_apply,PiLp.single_apply,ite_eq_right (Ne.symm (hx0 i)),smul_eq_mul,mul_zero,add_zero]
        rfl
      rw [he]
      rfl


-- @@ L204-219 verbatim
lemma adaptive_linear_equations {n : ℕ} (j : Fin n → ι) (hj : Function.Injective j)
    (m : Fin n → Coeff (ι := ι) →L[ℝ] ℝ)
    (hm : ∀ i l : Fin n,i≤l → m i (EuclideanSpace.single (j l) 1)=0)
    {K : Set (Coeff (ι := ι))} (hK : Good K) (hslab : ∀ x∈K,∀ i,|m i x|<1/4) :
    ∃ ε : Fin n → ℝ,∃ x : Coeff (ι := ι),
      (∀ i,ε i = -1 ∨ ε i=1) ∧ x∈K ∧
      (∀ k,(∀ i,k≠j i) → x k=0) ∧ (∀ i,x (j i)=m i x+ε i) := by
  obtain ⟨ε,hε,hx⟩ := adaptive_signs j (fun i y => clip (m i y)) (fun i y => clip_bound _) hK
  let x := walk j (fun i y => clip (m i y)) ε 0
  refine ⟨ε,x,hε,hx,?_,?_⟩
  · intro k hk
    exact walk_coordinate_outside j (fun i y => clip (m i y)) ε 0 k hk
  · intro i
    have hh := walk_coordinate_equations j hj m hm ε 0 i
    change x (j i)=(0:Coeff) (j i)+clip (m i x)+ε i at hh
    simpa only [PiLp.zero_apply,zero_add,clip_eq (hslab x hx i)] using hh


-- @@ L221-221 verbatim
end ShiftedSections


-- @@ L223-223 verbatim
end


-- @@ L225-225 verbatim
end OAI
