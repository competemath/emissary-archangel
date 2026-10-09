import OAI.Analysis.TreePotential.SegmentMidpoint


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
open Set

-- @@ L7-7 verbatim
open scoped ENNReal

-- @@ L8-8 verbatim
open Set Filter Topology

-- @@ L9-9 verbatim
open scoped Classical


-- @@ L11-11 verbatim
/-! Segment start costs. -/




-- @@ L15-15 verbatim
namespace BoundedTreePotentials.Segments


-- @@ L17-18 verbatim
/-- Extended Euclidean aggregation, with no finiteness assumption. -/
def eTwo {I : Type*} (f : I → ℝ≥0∞) : ℝ≥0∞ := (∑' i,f i^2)^(1/2:ℝ)


-- @@ L20-22 verbatim
lemma eTwo_sq {I : Type*} (f : I → ℝ≥0∞) : (eTwo f)^2=∑' i,f i^2 := by
  rw [eTwo,← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
  norm_num


-- @@ L24-24 verbatim
@[simp] lemma eTwo_zero (I : Type*) : eTwo (0 : I → ℝ≥0∞)=0 := by simp [eTwo]


-- @@ L26-28 verbatim
lemma eTwo_mono {I : Type*} {f g : I → ℝ≥0∞} (h : ∀ i,f i ≤ g i) : eTwo f ≤ eTwo g := by
  apply ENNReal.rpow_le_rpow _ (by norm_num : (0:ℝ) ≤ 1/2)
  exact ENNReal.tsum_le_tsum (fun i => pow_le_pow_left' (h i) 2)


-- @@ L30-35 verbatim
lemma eTwo_mul {I : Type*} (a : ℝ≥0∞) (f : I → ℝ≥0∞) :
    eTwo (fun i => a*f i)=a*eTwo f := by
  simp only [eTwo,mul_pow,ENNReal.tsum_mul_left]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2)]
  rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
  norm_num


-- @@ L37-39 verbatim
lemma enn_sqrt_iSup {I : Type*} (f : I → ℝ≥0∞) :
    (⨆ i,f i)^(1/2:ℝ)=⨆ i,(f i)^(1/2:ℝ) :=
  (ENNReal.orderIsoRpow (1/2:ℝ) (by norm_num)).map_iSup f


-- @@ L41-44 verbatim
lemma enn_sq_iSup {I : Type*} (f : I → ℝ≥0∞) : (⨆ i,f i)^2=⨆ i,(f i)^2 := by
  have h := (ENNReal.orderIsoRpow (2:ℝ) (by norm_num)).map_iSup f
  change ((⨆ i,f i)^(2:ℝ))=(⨆ i,(f i)^(2:ℝ)) at h
  simpa only [ENNReal.rpow_two] using h


-- @@ L46-48 verbatim
lemma eTwo_eq_iSup {I : Type*} (f : I → ℝ≥0∞) :
    eTwo f=⨆ E : Finset I,(∑ i ∈ E,f i^2)^(1/2:ℝ) := by
  rw [eTwo,ENNReal.tsum_eq_iSup_sum,enn_sqrt_iSup]


-- @@ L50-59 verbatim
lemma eTwo_add {I : Type*} (f g : I → ℝ≥0∞) :
    eTwo (f+g) ≤ eTwo f+eTwo g := by
  rw [eTwo_eq_iSup]
  apply iSup_le
  intro E
  have hh := ENNReal.Lp_add_le E f g (by norm_num : (1:ℝ) ≤ 2)
  simp only [ENNReal.rpow_two] at hh
  exact hh.trans (add_le_add
    (ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum E) (by norm_num : (0:ℝ) ≤ 1/2))
    (ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum E) (by norm_num : (0:ℝ) ≤ 1/2)))


-- @@ L61-64 verbatim
lemma eTwo_component {I : Type*} (f : I → ℝ≥0∞) (i : I) : f i ≤ eTwo f := by
  apply (ENNReal.rpow_le_rpow_iff (by norm_num : (0:ℝ)<2)).mp
  simp only [ENNReal.rpow_two,eTwo_sq]
  exact ENNReal.le_tsum (f := fun index => f index ^ 2) i


-- @@ L66-74 verbatim
lemma enn_finset_sum_iSup {I J : Type*} [Preorder J] [IsDirectedOrder J]
    (E : Finset I) (f : J → I → ℝ≥0∞) (hf : Monotone f) :
    (∑ i ∈ E,⨆ j,f j i)=⨆ j,∑ i ∈ E,f j i := by
  induction E using Finset.induction_on with
  | empty => simp
  | @insert i E hi ih =>
    simp only [Finset.sum_insert hi,ih]
    exact ENNReal.iSup_add_iSup_of_monotone (fun j k hjk => hf hjk i)
      (fun j k hjk => Finset.sum_le_sum (fun i hi => hf hjk i))


-- @@ L76-82 verbatim
lemma enn_tsum_iSup {I J : Type*} [Preorder J] [IsDirectedOrder J]
    (f : J → I → ℝ≥0∞) (hf : Monotone f) :
    (∑' i,⨆ j,f j i)=⨆ j,∑' i,f j i := by
  rw [ENNReal.tsum_eq_iSup_sum]
  simp_rw [enn_finset_sum_iSup _ f hf]
  rw [iSup_comm]
  simp_rw [← ENNReal.tsum_eq_iSup_sum]


-- @@ L84-89 verbatim
lemma eTwo_iSup {I J : Type*} [Preorder J] [IsDirectedOrder J]
    (f : J → I → ℝ≥0∞) (hf : Monotone f) :
    eTwo (fun i => ⨆ j,f j i)=⨆ j,eTwo (f j) := by
  unfold eTwo
  simp_rw [enn_sq_iSup]
  rw [enn_tsum_iSup _ (fun j k hjk i => pow_le_pow_left' (hf hjk i) 2),enn_sqrt_iSup]


-- @@ L91-98 verbatim
lemma startCost_mul (n : ℕ) (a : ℝ≥0∞) (m : List ℕ → ℝ≥0∞) :
    startCost n (fun s => a*m s)=a*startCost n m := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    change a*m []+eTwo (fun j => startCost n (fun s => a*m (j::s)))=
      a*(m []+eTwo (fun j => startCost n (fun s => m (j::s))))
    simp only [ih,eTwo_mul,mul_add]


-- @@ L100-116 verbatim
lemma startCost_add (n : ℕ) (m r : List ℕ → ℝ≥0∞) :
    startCost n (m+r) ≤ startCost n m+startCost n r := by
  induction n generalizing m r with
  | zero => exact le_rfl
  | succ n ih =>
    change m []+r []+eTwo (fun j => startCost n (fun s => m (j::s)+r (j::s)))≤
      (m []+eTwo (fun j => startCost n (fun s => m (j::s))))+
      (r []+eTwo (fun j => startCost n (fun s => r (j::s))))
    have hh := (eTwo_mono (fun j => ih (fun s => m (j::s)) (fun s => r (j::s)))).trans
      (eTwo_add (fun j => startCost n (fun s => m (j::s))) (fun j => startCost n (fun s => r (j::s))))
    calc
      _ ≤ m []+r []+(eTwo (fun j => startCost n (fun s => m (j::s)))+
        eTwo (fun j => startCost n (fun s => r (j::s)))) := by
          have hh2 : eTwo (fun j => startCost n (fun s => m (j::s)+r (j::s))) ≤
            eTwo (fun j => startCost n (fun s => m (j::s)))+eTwo (fun j => startCost n (fun s => r (j::s))) := hh
          exact add_le_add le_rfl hh2
      _ = _ := by ac_rfl


-- @@ L118-131 verbatim
lemma startCost_iSup {J : Type*} [Preorder J] [IsDirectedOrder J]
    (n : ℕ) (m : J → List ℕ → ℝ≥0∞) (hm : Monotone m) :
    startCost n (fun s => ⨆ j,m j s)=⨆ j,startCost n (m j) := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    change (⨆ j,m j [])+eTwo (fun k => startCost n (fun s => ⨆ j,m j (k::s)))=_
    have he (k : ℕ) : startCost n (fun s => ⨆ j,m j (k::s))=
        ⨆ j,startCost n (fun s => m j (k::s)) :=
      ih _ (fun j l hjl s => hm hjl (k::s))
    simp_rw [he]
    rw [eTwo_iSup _ (fun j l hjl k => startCost_mono n (fun s => hm hjl (k::s)))]
    exact ENNReal.iSup_add_iSup_of_monotone (fun j l hjl => hm hjl [])
      (fun j l hjl => eTwo_mono (fun k => startCost_mono n (fun s => hm hjl (k::s))))


-- @@ L133-146 verbatim
lemma enn_positive_energy_scalar (a b A B C : ℝ≥0∞)
    (hA : A ≤ C) (hB : B ≤ C) (hs : A^2+B^2 ≤ C^2) :
    (a+A)^2+(b+B)^2 ≤ (a+b+C)^2 := by
  have hab : a^2+b^2 ≤ (a+b)^2 := by
    calc
      _ ≤ a^2+b^2+2*a*b := le_self_add
      _ = _ := by ring
  have hh : a*A+b*B ≤ (a+b)*C := by
    rw [add_mul]
    exact add_le_add ((show a*A ≤ a*C by simpa only [mul_comm] using mul_le_mul_left hA a)) ((show b*B ≤ b*C by simpa only [mul_comm] using mul_le_mul_left hB b))
  calc
    _ = (a^2+b^2)+(A^2+B^2)+2*(a*A+b*B) := by ring
    _ ≤ (a+b)^2+C^2+2*((a+b)*C) := add_le_add (add_le_add hab hs) ((show 2*(a*A+b*B) ≤ 2*((a+b)*C) by simpa only [mul_comm] using mul_le_mul_left hh 2))
    _ = _ := by ring


-- @@ L148-167 verbatim
/-- Positive energy holds even before restricting the recursion to finite costs. -/
lemma startCost_positive_energy (n : ℕ) (m r : List ℕ → ℝ≥0∞) :
    (startCost n m)^2+(startCost n r)^2 ≤ (startCost n (m+r))^2 := by
  induction n generalizing m r with
  | zero =>
    change (m [])^2+(r [])^2 ≤ (m []+r [])^2
    calc
      _ ≤ (m [])^2+(r [])^2+2*m []*r [] := le_self_add
      _ = _ := by ring
  | succ n ih =>
    let A := fun j => startCost n (fun s => m (j::s))
    let B := fun j => startCost n (fun s => r (j::s))
    let C := fun j => startCost n (fun s => m (j::s)+r (j::s))
    have hA : eTwo A ≤ eTwo C := eTwo_mono (fun j => startCost_mono n (fun s => le_self_add))
    have hB : eTwo B ≤ eTwo C := eTwo_mono (fun j => startCost_mono n (fun s => le_add_self))
    have hs : (eTwo A)^2+(eTwo B)^2 ≤ (eTwo C)^2 := by
      simp only [eTwo_sq]
      rw [← ENNReal.tsum_add]
      exact ENNReal.tsum_le_tsum (fun j => ih (fun s => m (j::s)) (fun s => r (j::s)))
    exact enn_positive_energy_scalar (m []) (r []) (eTwo A) (eTwo B) (eTwo C) hA hB hs


-- @@ L169-172 verbatim
/-- Nonnegative forest aggregation, with components indexed by root-inclusive heights n+1. -/

def forestCost (m : (n : ℕ) → List ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  eTwo (fun n => startCost (n+1) (m n))


-- @@ L174-175 verbatim
lemma forestCost_mono {m r : (n : ℕ) → List ℕ → ℝ≥0∞} (h : m ≤ r) : forestCost m ≤ forestCost r :=
  eTwo_mono (fun n => startCost_mono (n+1) (h n))


-- @@ L177-178 verbatim
lemma forestCost_add (m r : (n : ℕ) → List ℕ → ℝ≥0∞) : forestCost (m+r) ≤ forestCost m+forestCost r :=
  (eTwo_mono (fun n => startCost_add (n+1) (m n) (r n))).trans (eTwo_add _ _)


-- @@ L180-182 verbatim
lemma forestCost_mul (a : ℝ≥0∞) (m : (n : ℕ) → List ℕ → ℝ≥0∞) :
    forestCost (fun n s => a*m n s)=a*forestCost m := by
  simp only [forestCost,startCost_mul,eTwo_mul]


-- @@ L184-188 verbatim
lemma forestCost_positive_energy (m r : (n : ℕ) → List ℕ → ℝ≥0∞) :
    (forestCost m)^2+(forestCost r)^2 ≤ (forestCost (m+r))^2 := by
  simp only [forestCost,eTwo_sq]
  rw [← ENNReal.tsum_add]
  exact ENNReal.tsum_le_tsum (fun n => startCost_positive_energy (n+1) (m n) (r n))


-- @@ L190-195 verbatim
lemma forestCost_iSup {J : Type*} [Preorder J] [IsDirectedOrder J]
    (m : J → (n : ℕ) → List ℕ → ℝ≥0∞) (hm : Monotone m) :
    forestCost (fun n s => ⨆ j,m j n s)=⨆ j,forestCost (m j) := by
  simp only [forestCost]
  simp_rw [startCost_iSup _ _ (fun j k hjk s => hm hjk _ s)]
  exact eTwo_iSup _ (fun j k hjk n => startCost_mono (n+1) (hm hjk n))


-- @@ L197-220 verbatim
/-- Independent choices may be made in each summand; no monotonicity of
those choices is imposed. -/
lemma enn_sum_iSup_le {I : Type*} {J : I → Type*} [∀ i, Nonempty (J i)]
    (E : Finset I) (f : (i : I) → J i → ℝ≥0∞) {c : ℝ≥0∞}
    (h : ∀ a : (i : I) → J i, (∑ i ∈ E,f i (a i)) ≤ c) :
    (∑ i ∈ E,⨆ j,f i j) ≤ c := by
  have he : ∀ E : Finset I, (∑ i ∈ E,⨆ j,f i j) ≤ ⨆ a : (i : I) → J i, ∑ i ∈ E,f i (a i) := by
    intro E
    induction E using Finset.induction_on with
    | empty => simp
    | @insert i E hi ih =>
      rw [Finset.sum_insert hi]
      apply (add_le_add le_rfl ih).trans
      apply ENNReal.iSup_add_iSup_le
      intro x a
      apply le_iSup_of_le (Function.update a i x)
      rw [Finset.sum_insert hi,Function.update_self]
      apply add_le_add le_rfl
      apply le_of_eq
      apply Finset.sum_congr rfl
      intro k hk
      have hki : k ≠ i := fun hki => hi (hki ▸ hk)
      rw [Function.update_of_ne hki]
  exact (he E).trans (iSup_le h)


-- @@ L222-232 verbatim
lemma eTwo_inner_le {I : Type*} (f g : I → ℝ≥0∞) :
    (∑' i,f i*g i) ≤ eTwo f*eTwo g := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro E
  have hh := ENNReal.inner_le_Lp_mul_Lq E f g (p:=2) (q:=2) (by norm_num [Real.holderConjugate_iff])
  simp only [ENNReal.rpow_two] at hh
  apply hh.trans
  exact mul_le_mul
    (ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum E) (by norm_num : (0:ℝ) ≤ 1/2))
    (ENNReal.rpow_le_rpow (ENNReal.sum_le_tsum E) (by norm_num : (0:ℝ) ≤ 1/2)) zero_le zero_le


-- @@ L234-237 verbatim
/-- Literal summation over all nodes up to height n. -/
def treeSum : ℕ → (List ℕ → ℝ≥0∞) → ℝ≥0∞
  | 0, m => m []
  | n+1, m => m []+∑' j : ℕ,treeSum n (fun s => m (j::s))


-- @@ L239-244 verbatim
@[simp] lemma treeSum_zero (n : ℕ) : treeSum n 0=0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (0:ℝ≥0∞)+(∑' j : ℕ,treeSum n 0)=0
    simp [ih]


-- @@ L246-249 verbatim
lemma treeSum_mono (n : ℕ) {m r : List ℕ → ℝ≥0∞} (h : ∀ s,m s≤ r s) : treeSum n m≤ treeSum n r := by
  induction n generalizing m r with
  | zero => exact h []
  | succ n ih => exact add_le_add (h []) (ENNReal.tsum_le_tsum (fun j => ih (fun s => h (j::s))))


-- @@ L251-259 verbatim
lemma treeSum_tsum {I : Type*} (n : ℕ) (m : I → List ℕ → ℝ≥0∞) :
    treeSum n (fun s => ∑' i,m i s)=∑' i,treeSum n (m i) := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    change (∑' i,m i [])+(∑' j : ℕ,treeSum n (fun s => ∑' i,m i (j::s)))=_
    simp_rw [ih]
    rw [ENNReal.tsum_comm,← ENNReal.tsum_add]
    rfl


-- @@ L261-268 verbatim
lemma treeSum_mul (n : ℕ) (a : ℝ≥0∞) (m : List ℕ → ℝ≥0∞) :
    treeSum n (fun s => a*m s)=a*treeSum n m := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    change a*m []+(∑' j : ℕ,treeSum n (fun s => a*m (j::s)))=_
    simp_rw [ih]
    rw [ENNReal.tsum_mul_left,treeSum,mul_add]


-- @@ L270-296 verbatim
lemma treeSum_single (n : ℕ) (s : List ℕ) (hs : s.length ≤ n) (a : ℝ≥0∞) :
    treeSum n (fun t => if t=s then a else 0)=a := by
  induction n generalizing s with
  | zero =>
    have hz : s=[] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hs)
    subst s
    simp [treeSum]
  | succ n ih =>
    cases s with
    | nil =>
      change (if ([] : List ℕ)=[] then a else 0)+(∑' j : ℕ,treeSum n (fun t => if j::t=[] then a else 0))=a
      simp only [List.cons_ne_nil,ite_false,ite_true]
      change a+(∑' j : ℕ,treeSum n 0)=a
      simp [treeSum_zero]
    | cons k s =>
      change (if ([] : List ℕ)=k::s then a else 0)+(∑' j : ℕ,treeSum n (fun t => if j::t=k::s then a else 0))=a
      have hn : ([] : List ℕ) ≠ k::s := by simp
      simp only [hn,ite_false,zero_add]
      have he (j : ℕ) : treeSum n (fun t => if j::t=k::s then a else 0)=if j=k then a else 0 := by
        by_cases hj : j=k
        · subst j
          simp only [List.cons.injEq,true_and]
          simpa only [ite_true] using ih s (by simpa only [List.length_cons,Nat.add_le_add_iff_right] using hs)
        · simp only [List.cons.injEq,hj,false_and,ite_false]
          exact treeSum_zero n
      simp_rw [he]
      simp


-- @@ L298-315 verbatim
/-- Squaring and discarding nonnegative cross terms gives the exact lower
Hilbert comparison before any tensor/quotient norm is introduced. -/
lemma treeSum_sq_le_startCost_sq (n : ℕ) (m : List ℕ → ℝ≥0∞) :
    treeSum n (fun s => (m s)^2) ≤ (startCost n m)^2 := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    change (m [])^2+(∑' j : ℕ,treeSum n (fun s => (m (j::s))^2)) ≤
      (m []+eTwo (fun j => startCost n (fun s => m (j::s))))^2
    calc
      _ ≤ (m [])^2+(eTwo (fun j => startCost n (fun s => m (j::s))))^2 := by
        rw [eTwo_sq]
        exact add_le_add le_rfl (ENNReal.tsum_le_tsum (fun j => ih _))
      _ ≤ _ := by
        calc
          _ ≤ (m [])^2+(eTwo (fun j => startCost n (fun s => m (j::s))))^2+
            2*m []*eTwo (fun j => startCost n (fun s => m (j::s))) := le_self_add
          _ = _ := by ring


-- @@ L317-320 verbatim
/-- A nonnegative potential has Euclidean child values bounded by its parent. -/
def IsPotential : ℕ → (List ℕ → ℝ≥0∞) → Prop
  | 0, _ => True
  | n+1, b => eTwo (fun j : ℕ => b [j]) ≤ b [] ∧ ∀ j, IsPotential n (fun s => b (j::s))


-- @@ L322-336 verbatim
lemma treeSum_pair_le (n : ℕ) (m b : List ℕ → ℝ≥0∞) (hb : IsPotential n b) :
    treeSum n (fun s => m s*b s) ≤ startCost n m*b [] := by
  induction n generalizing m b with
  | zero => rfl
  | succ n ih =>
    change m []*b []+(∑' j : ℕ,treeSum n (fun s => m (j::s)*b (j::s)))≤
      (m []+eTwo (fun j => startCost n (fun s => m (j::s))))*b []
    calc
      _ ≤ m []*b []+(∑' j : ℕ,startCost n (fun s => m (j::s))*b [j]) :=
        add_le_add le_rfl (ENNReal.tsum_le_tsum (fun j => ih _ _ (hb.2 j)))
      _ ≤ m []*b []+eTwo (fun j => startCost n (fun s => m (j::s)))*eTwo (fun j => b [j]) :=
        add_le_add le_rfl (eTwo_inner_le _ _)
      _ ≤ m []*b []+eTwo (fun j => startCost n (fun s => m (j::s)))*b [] :=
        add_le_add le_rfl (mul_le_mul le_rfl hb.1 zero_le zero_le)
      _ = _ := by rw [add_mul]


-- @@ L338-352 verbatim
lemma startCost_congr (n : ℕ) {m r : List ℕ → ℝ≥0∞}
    (h : ∀ s,s.length ≤ n → m s=r s) : startCost n m=startCost n r := by
  induction n generalizing m r with
  | zero => exact h [] (by simp)
  | succ n ih =>
    change m [] + (∑' j : ℕ, (startCost n (fun s => m (j::s)))^2)^(1/2:ℝ) =
      r [] + (∑' j : ℕ, (startCost n (fun s => r (j::s)))^2)^(1/2:ℝ)
    rw [h [] (by simp)]
    congr 1
    congr 1
    apply tsum_congr
    intro j
    rw [ih]
    intro s hs
    exact h (j::s) (by simpa using Nat.succ_le_succ hs)


-- @@ L354-366 verbatim
lemma treeSum_congr (n : ℕ) {m r : List ℕ → ℝ≥0∞}
    (h : ∀ s,s.length ≤ n → m s=r s) : treeSum n m=treeSum n r := by
  induction n generalizing m r with
  | zero => exact h [] (by simp)
  | succ n ih =>
    change m []+(∑' j : ℕ,treeSum n (fun s => m (j::s)))=r []+(∑' j : ℕ,treeSum n (fun s => r (j::s)))
    rw [h [] (by simp)]
    congr 1
    apply tsum_congr
    intro j
    apply ih
    intro s hs
    exact h (j::s) (by simpa using Nat.succ_le_succ hs)


-- @@ L368-369 verbatim
def AntichainMass (n : ℕ) (m : List ℕ → ℝ≥0∞) : Prop :=
  ∀ s t,s.length ≤ n → t.length ≤ n → m s≠0 → m t≠0 → s <+: t → s=t


-- @@ L371-376 verbatim
lemma antichainMass_child {n : ℕ} {m : List ℕ → ℝ≥0∞} (h : AntichainMass (n+1) m) (j : ℕ) :
    AntichainMass n (fun s => m (j::s)) := by
  intro s t hs ht hms hmt hp
  have hh := h (j::s) (j::t) (by simpa using Nat.succ_le_succ hs)
    (by simpa using Nat.succ_le_succ ht) hms hmt (by simpa using hp)
  exact (List.cons.inj hh).2


-- @@ L378-406 verbatim
/-- Incomparable start masses combine in exact Euclidean norm. This is proved
from the literal cost recursion, not used as a replacement definition. -/
lemma startCost_antichain_sq (n : ℕ) (m : List ℕ → ℝ≥0∞) (hm : AntichainMass n m) :
    (startCost n m)^2=treeSum n (fun s => (m s)^2) := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    by_cases hz : m []=0
    · change (m []+eTwo (fun j => startCost n (fun s => m (j::s))))^2=
        (m [])^2+(∑' j : ℕ,treeSum n (fun s => (m (j::s))^2))
      rw [hz,zero_add,zero_pow (by decide : 2≠0),zero_add,eTwo_sq]
      apply tsum_congr
      intro j
      exact ih _ (antichainMass_child hm j)
    · have hzero (j : ℕ) (s : List ℕ) (hs : s.length ≤ n) : m (j::s)=0 := by
        by_contra hn
        have he := hm [] (j::s) (by simp) (by simpa using Nat.succ_le_succ hs) hz hn List.nil_prefix
        simp at he
      have hq (j : ℕ) : startCost n (fun s => m (j::s))=0 :=
        (startCost_congr n (r:=0) (hzero j)).trans (startCost_zero n)
      have hs (j : ℕ) : treeSum n (fun s => (m (j::s))^2)=0 := by
        apply (treeSum_congr n (r:=0) _).trans (treeSum_zero n)
        intro s hs
        simp [hzero j s hs]
      change (m []+eTwo (fun j => startCost n (fun s => m (j::s))))^2=
        (m [])^2+(∑' j : ℕ,treeSum n (fun s => (m (j::s))^2))
      simp only [hq,hs,tsum_zero,add_zero]
      change (m []+eTwo (0 : ℕ → ℝ≥0∞))^2=(m [])^2
      rw [eTwo_zero,add_zero]


-- @@ L408-414 verbatim
lemma forestCost_antichain_sq (m : (n : ℕ) → List ℕ → ℝ≥0∞)
    (hm : ∀ n,AntichainMass (n+1) (m n)) :
    (forestCost m)^2=∑' n : ℕ,treeSum (n+1) (fun s => (m n s)^2) := by
  rw [forestCost,eTwo_sq]
  apply tsum_congr
  intro n
  exact startCost_antichain_sq (n+1) (m n) (hm n)


-- @@ L416-428 verbatim
lemma startCost_node_le (n : ℕ) (m : List ℕ → ℝ≥0∞) (s : List ℕ) (hs : s.length ≤ n) :
    m s ≤ startCost n m := by
  induction n generalizing m s with
  | zero =>
    have hz : s=[] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hs)
    subst s
    rfl
  | succ n ih =>
    cases s with
    | nil => exact le_self_add
    | cons j s =>
      apply (ih (fun t => m (j::t)) s (by simpa using hs)).trans
      exact (eTwo_component (fun k => startCost n (fun t => m (k::t))) j).trans le_add_self


-- @@ L430-432 verbatim
lemma forestCost_node_le (m : (n : ℕ) → List ℕ → ℝ≥0∞) (n : ℕ) (s : List ℕ) (hs : s.length ≤ n+1) :
    m n s ≤ forestCost m :=
  (startCost_node_le (n+1) (m n) s hs).trans (eTwo_component (fun n => startCost (n+1) (m n)) n)


-- @@ L434-444 verbatim
lemma forestCost_finset_sum {I : Type*} (E : Finset I) (m : I → (n : ℕ) → List ℕ → ℝ≥0∞) :
    forestCost (∑ i ∈ E,m i) ≤ ∑ i ∈ E,forestCost (m i) := by
  induction E using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    change eTwo (fun n : ℕ => startCost (n+1) 0)≤0
    simp only [startCost_zero]
    exact (eTwo_zero ℕ).le
  | @insert i E hi ih =>
    rw [Finset.sum_insert hi,Finset.sum_insert hi]
    exact (forestCost_add _ _).trans (add_le_add le_rfl ih)


-- @@ L446-462 verbatim
/-- Countable subadditivity follows from finite subadditivity and monotone
continuity; the arrays need not have finite individual or total costs. -/
lemma forestCost_tsum {I : Type*} (m : I → (n : ℕ) → List ℕ → ℝ≥0∞) :
    forestCost (fun n s => ∑' i,m i n s) ≤ ∑' i,forestCost (m i) := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  rw [forestCost_iSup]
  · apply iSup_le
    intro E
    calc
      _ = forestCost (∑ i ∈ E,m i) := by
        congr 1
        funext n s
        simp
      _ ≤ ∑ i ∈ E,forestCost (m i) := forestCost_finset_sum E m
      _ ≤ _ := le_iSup (fun E : Finset I => ∑ i ∈ E,forestCost (m i)) E
  · intro E F hEF n s
    exact Finset.sum_le_sum_of_subset hEF


-- @@ L464-466 verbatim
def pathMass : (List ℕ → ℝ≥0∞) → List ℕ → ℝ≥0∞
  | m, [] => m []
  | m, j::s => m []+pathMass (fun t => m (j::t)) s


-- @@ L468-481 verbatim
lemma pathMass_le_startCost (n : ℕ) (m : List ℕ → ℝ≥0∞) (s : List ℕ) (hs : s.length ≤ n) :
    pathMass m s ≤ startCost n m := by
  induction n generalizing m s with
  | zero =>
    have hz : s=[] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hs)
    subst s
    rfl
  | succ n ih =>
    cases s with
    | nil => exact le_self_add
    | cons j s =>
      apply add_le_add le_rfl
      exact (ih (fun t => m (j::t)) s (by simpa using hs)).trans
        (eTwo_component (fun k => startCost n (fun t => m (k::t))) j)


-- @@ L483-483 verbatim
end BoundedTreePotentials.Segments


-- @@ L485-485 verbatim
end


-- @@ L487-487 verbatim
end OAI
