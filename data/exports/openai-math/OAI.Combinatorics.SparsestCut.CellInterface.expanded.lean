import OAI.Combinatorics.SparsestCut.SliceIntegration


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe u1 u2 u3 u4 u5 u6 u7 u8


-- @@ L7-7 verbatim
open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal

-- @@ L8-8 verbatim
open MeasureTheory ProbabilityTheory Set Filter Matrix


-- @@ L10-10 verbatim
noncomputable section


-- @@ L12-12 verbatim
namespace UniformSparsestCut.CellInterface

-- @@ L13-14 verbatim
variable {E : Type u1} {I : Type u2} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype I] [DecidableEq I]


-- @@ L16-22 verbatim
omit [NormedSpace ℝ E] in
lemma floor_locally_constant {f : E → ℝ} {x : E} (hf : ContinuousAt f x)
    (hn : ∀ k : ℤ, f x ≠ k) : ∀ᶠ y in 𝓝 x, ⌊f y⌋ = ⌊f x⌋ := by
  have hlo : (⌊f x⌋:ℝ) < f x := lt_of_le_of_ne (Int.floor_le _) (Ne.symm (hn _))
  have hu := Int.lt_floor_add_one (f x)
  filter_upwards [hf.eventually_lt_const hu, hf.eventually_const_lt hlo] with y hy hy'
  exact Int.floor_eq_iff.mpr ⟨hy'.le,hy⟩


-- @@ L24-103 verbatim
lemma neighboring_labels (ell : I → E →L[ℝ] ℝ) {τ : ℝ} (hτ : 0<τ)
    {U : Set E} (hU : IsOpen U) {x : E} (hx : x∈U) (i : I) (k : ℤ)
    (heq : ell i x=(k:ℝ)*τ)
    (hother : ∀ j, j≠i → ∀ l : ℤ, ell j x≠(l:ℝ)*τ)
    (v : E) (hv : ell i v>0) :
    ∃ xp xm : E, xp∈U ∧ xm∈U ∧
      (∀ j (l : ℤ), ell j xp≠(l:ℝ)*τ) ∧
      (∀ j (l : ℤ), ell j xm≠(l:ℝ)*τ) ∧
      (∀ j, j≠i → ⌊ell j xp/τ⌋=⌊ell j x/τ⌋ ∧ ⌊ell j xm/τ⌋=⌊ell j x/τ⌋) ∧
      ⌊ell i xp/τ⌋=k ∧ ⌊ell i xm/τ⌋=k-1 := by
  let f (t : ℝ) := x+t • v
  have hf : Continuous f := (continuous_const.add (continuous_id.smul continuous_const))
  have h0 : f 0=x := by simp [f]
  have hmem : ∀ᶠ t in 𝓝 (0:ℝ), f t∈U := by
    have h := hf.continuousAt.eventually (hU.mem_nhds (show f 0∈U by simpa only [h0] using hx))
    exact h
  have ho : ∀ᶠ t in 𝓝 (0:ℝ), ∀ j, j≠i →
      (∀ l : ℤ, ell j (f t)≠(l:ℝ)*τ) ∧ ⌊ell j (f t)/τ⌋=⌊ell j x/τ⌋ := by
    apply eventually_all.mpr
    intro j
    by_cases hji : j=i
    · simp [hji]
    have hc : ContinuousAt (fun t => ell j (f t)/τ) (0:ℝ) :=
      (((ell j).continuous.comp hf).div_const τ).continuousAt
    have hn : ∀ l : ℤ, ell j (f 0)/τ≠(l:ℝ) := by
      intro l h
      apply hother j hji l
      simpa only [h0] using (div_eq_iff hτ.ne').mp h
    have ha : (⌊ell j (f 0)/τ⌋:ℝ)<ell j (f 0)/τ :=
      lt_of_le_of_ne (Int.floor_le _) (Ne.symm (hn _))
    have hb := Int.lt_floor_add_one (ell j (f 0)/τ)
    filter_upwards [hc.eventually_const_lt ha, hc.eventually_lt_const hb] with t ht ht'
    intro _
    have hfloor := Int.floor_eq_iff.mpr ⟨ht.le,ht'⟩
    refine ⟨?_, by simpa only [h0] using hfloor⟩
    intro l he
    have hl : ell j (f t)/τ=(l:ℝ) := by rw [he,mul_div_cancel_right₀ _ hτ.ne']
    rw [hl] at ht ht'
    have hli : ⌊ell j (f 0)/τ⌋<l := by exact_mod_cast ht
    have hli' : l<⌊ell j (f 0)/τ⌋+1 := by exact_mod_cast ht'
    omega
  have hsmall : ∀ᶠ t in 𝓝 (0:ℝ), |t|<τ/ell i v :=
    isOpen_lt continuous_abs continuous_const |>.mem_nhds (by simpa using div_pos hτ hv)
  have both := hmem.and (ho.and hsmall)
  obtain ⟨d,hd,hdsub⟩ := Metric.mem_nhds_iff.mp both
  let t := d/2
  have ht : 0<t := half_pos hd
  have htm : t<d := half_lt_self hd
  have hp := hdsub (show t∈Metric.ball (0:ℝ) d by simpa [Real.dist_eq,abs_of_pos ht] using htm)
  have hm := hdsub (show -t∈Metric.ball (0:ℝ) d by simpa [Real.dist_eq,abs_neg,abs_of_pos ht] using htm)
  have hb : t*ell i v<τ := (lt_div_iff₀ hv).mp (by simpa [abs_of_pos ht] using hp.2.2)
  have htpos : 0<t*ell i v := mul_pos ht hv
  have hep : ell i (f t)/τ=(k:ℝ)+t*ell i v/τ := by
    simp only [f,map_add,map_smul,smul_eq_mul,heq,add_div,mul_div_cancel_right₀ _ hτ.ne']
  have hem : ell i (f (-t))/τ=(k:ℝ)-t*ell i v/τ := by
    simp only [f,map_add,map_smul,smul_eq_mul,heq,add_div,mul_div_cancel_right₀ _ hτ.ne']
    ring
  have hfrac : 0<t*ell i v/τ ∧ t*ell i v/τ<1 := ⟨div_pos htpos hτ,(div_lt_one hτ).mpr hb⟩
  have hfp : ⌊ell i (f t)/τ⌋=k := Int.floor_eq_iff.mpr (by rw [hep]; constructor <;> linarith [hfrac.1,hfrac.2])
  have hfm : ⌊ell i (f (-t))/τ⌋=k-1 := Int.floor_eq_iff.mpr (by rw [hem]; push_cast; constructor <;> linarith [hfrac.1,hfrac.2])
  refine ⟨f t,f (-t),hp.1,hm.1,?_,?_,?_,hfp,hfm⟩
  · intro j l he
    by_cases hji : j=i
    · subst j
      have hl : ell i (f t)/τ=(l:ℝ) := by rw [he,mul_div_cancel_right₀ _ hτ.ne']
      have hkl : l=k := by simpa [hl] using hfp
      rw [hl,hkl] at hep
      linarith [hfrac.1]
    · exact (hp.2.1 j hji).1 l he
  · intro j l he
    by_cases hji : j=i
    · subst j
      have hl : ell i (f (-t))/τ=(l:ℝ) := by rw [he,mul_div_cancel_right₀ _ hτ.ne']
      have hkl : l=k-1 := by simpa [hl] using hfm
      rw [hl,hkl] at hem
      push_cast at hem
      linarith [hfrac.2]
    · exact (hm.2.1 j hji).1 l he
  · intro j hji
    exact ⟨(hp.2.1 j hji).2,(hm.2.1 j hji).2⟩


-- @@ L105-105 verbatim
end UniformSparsestCut.CellInterface


-- @@ L107-107 verbatim
namespace UniformSparsestCut.CellInterface

-- @@ L108-108 verbatim
open Filter Set

-- @@ L109-109 verbatim
open scoped Topology BigOperators

-- @@ L110-110 verbatim
noncomputable section

-- @@ L111-112 verbatim
variable {E : Type u3} {I : Type u4} {A : Type u5} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype I] [DecidableEq I]


-- @@ L114-115 verbatim
def regular (ell : I → E →L[ℝ] ℝ) (τ : ℝ) (x : E) : Prop :=
  ∀ i (k : ℤ), ell i x≠(k:ℝ)*τ


-- @@ L117-117 verbatim
def label (ell : I → E →L[ℝ] ℝ) (τ : ℝ) (x : E) : I → ℤ := fun i => ⌊ell i x/τ⌋


-- @@ L119-120 verbatim
def LabelVertex (ell : I → E →L[ℝ] ℝ) (τ : ℝ) (U : Set E) :=
  {l : I → ℤ // ∃ x∈U, regular ell τ x ∧ label ell τ x=l}


-- @@ L122-123 verbatim
def vertex (ell : I → E →L[ℝ] ℝ) (τ : ℝ) {U : Set E} (x : E) (hx : x∈U)
    (hr : regular ell τ x) : LabelVertex ell τ U := ⟨label ell τ x,x,hx,hr,rfl⟩


-- @@ L125-130 verbatim
omit [Fintype I] [DecidableEq I] in
lemma regular_floor_le (ell : I → E →L[ℝ] ℝ) {τ : ℝ} (hτ : 0<τ)
    {x : E} (hr : regular ell τ x) (i : I) (k : ℤ) :
    k≤label ell τ x i ↔ (k:ℝ)*τ<ell i x := by
  rw [label,Int.le_floor,le_div_iff₀ hτ]
  exact ⟨fun h => lt_of_le_of_ne h (Ne.symm (hr i k)),le_of_lt⟩

-- @@ L131-134 verbatim
omit [Fintype I] [DecidableEq I] in
lemma floor_lt (ell : I → E →L[ℝ] ℝ) {τ : ℝ} (hτ : 0<τ) (x : E) (i : I) (k : ℤ) :
    label ell τ x i<k ↔ ell i x<(k:ℝ)*τ := by
  rw [label,Int.floor_lt,div_lt_iff₀ hτ]


-- @@ L136-137 verbatim
def pattern (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (τ : ℝ) (s : Finset ℤ) (x : E) : Finset (I × s) :=
  Finset.univ.filter (fun p => (ell p.1 x-(p.2.val:ℝ)*τ)/pivot p.1<0)

-- @@ L138-139 verbatim
def weakPattern (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (τ : ℝ) (s : Finset ℤ) (x : E) : Finset (I × s) :=
  Finset.univ.filter (fun p => (ell p.1 x-(p.2.val:ℝ)*τ)/pivot p.1≤0)


-- @@ L141-153 verbatim
omit [DecidableEq I] in
lemma mem_pattern (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    {τ : ℝ} (hτ : 0<τ) (s : Finset ℤ) {x : E} (hr : regular ell τ x) (i : I) (k : s) :
    (i,k)∈pattern ell pivot τ s x ↔ if 0<pivot i then label ell τ x i<k.val else k.val≤label ell τ x i := by
  simp only [pattern,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hpi : 0<pivot i
  · rw [ite_eq_left hpi,div_neg_iff]
    simp only [hpi,not_lt_of_gt hpi,and_false,false_or,and_true]
    exact sub_neg.trans (floor_lt ell hτ x i k.val).symm
  · have hpn : pivot i<0 := lt_of_le_of_ne (le_of_not_gt hpi) (hp i)
    rw [ite_eq_right hpi,div_neg_iff]
    simp only [hpn,hpi,and_false,or_false,and_true]
    exact sub_pos.trans (regular_floor_le ell hτ hr i k.val).symm


-- @@ L155-169 verbatim
omit [DecidableEq I] in
lemma pattern_labels (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    {τ : ℝ} (hτ : 0<τ) (s : Finset ℤ) {x y : E}
    (hx : regular ell τ x) (hy : regular ell τ y)
    (hbx : ∀ i, label ell τ x i∈s) (hby : ∀ i, label ell τ y i∈s)
    (he : pattern ell pivot τ s x=pattern ell pivot τ s y) : label ell τ x=label ell τ y := by
  funext i
  have hiff (k : s) : (k.val≤label ell τ x i) ↔ (k.val≤label ell τ y i) := by
    have h : (i,k)∈pattern ell pivot τ s x ↔ (i,k)∈pattern ell pivot τ s y := by rw [he]
    rw [mem_pattern ell pivot hp hτ s hx,mem_pattern ell pivot hp hτ s hy] at h
    by_cases hpi : 0<pivot i
    · simp only [hpi,ite_true] at h
      exact not_lt.symm.trans ((not_congr h).trans not_lt)
    · simpa only [hpi,ite_false] using h
  exact le_antisymm ((hiff ⟨_,hbx i⟩).mp le_rfl) ((hiff ⟨_,hby i⟩).mpr le_rfl)


-- @@ L171-176 verbatim
def extension (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (τ : ℝ) (s : Finset ℤ)
    (U : Set E) (F : LabelVertex ell τ U → A → ℝ) (P : Finset (I × s)) : A → ℝ := by
  classical
  exact if h : ∃ x : E, ∃ hx : x∈U, ∃ hr : regular ell τ x, pattern ell pivot τ s x=P then
    F (vertex ell τ h.choose (h.choose_spec.choose) (h.choose_spec.choose_spec.choose))
  else fun _ => 0


-- @@ L178-192 verbatim
omit [DecidableEq I] in
lemma extension_eq (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    {τ : ℝ} (hτ : 0<τ) (s : Finset ℤ) (U : Set E)
    (hb : ∀ x∈U, regular ell τ x → ∀ i, label ell τ x i∈s)
    (F : LabelVertex ell τ U → A → ℝ) (x : E) (hx : x∈U) (hr : regular ell τ x) :
    extension ell pivot τ s U F (pattern ell pivot τ s x)=F (vertex ell τ x hx hr) := by
  classical
  unfold extension
  split_ifs with h
  · congr 1
    apply Subtype.ext
    exact pattern_labels ell pivot hp hτ s h.choose_spec.choose_spec.choose hr
      (hb _ h.choose_spec.choose h.choose_spec.choose_spec.choose) (hb x hx hr)
      h.choose_spec.choose_spec.choose_spec
  · exact False.elim (h ⟨x,hx,hr,rfl⟩)


-- @@ L194-203 verbatim
omit [DecidableEq I] in
lemma extension_bounded (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (τ : ℝ) (s : Finset ℤ)
    (U : Set E) (F : LabelVertex ell τ U → A → ℝ) {M : ℝ} (hM0 : 0≤M)
    (hM : ∀ v a, |F v a|≤M) (P : Finset (I × s)) (a : A) :
    |extension ell pivot τ s U F P a|≤M := by
  classical
  unfold extension
  split_ifs
  · exact hM _ _
  · simpa using hM0


-- @@ L205-205 verbatim
end

-- @@ L206-206 verbatim
end UniformSparsestCut.CellInterface


-- @@ L208-208 verbatim
namespace UniformSparsestCut.CellInterface

-- @@ L209-209 verbatim
open Filter Set

-- @@ L210-210 verbatim
open scoped Topology BigOperators

-- @@ L211-211 verbatim
noncomputable section

-- @@ L212-213 verbatim
variable {E : Type u6} {I : Type u7} {A : Type u8} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Fintype I] [DecidableEq I]


-- @@ L215-232 verbatim
omit [DecidableEq I] in
lemma mem_pattern_at (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    {τ : ℝ} (hτ : 0<τ) (s : Finset ℤ) {x : E} (i : I)
    (hr : ∀ k : ℤ, ell i x≠(k:ℝ)*τ) (k : s) :
    (i,k)∈pattern ell pivot τ s x ↔ if 0<pivot i then label ell τ x i<k.val else k.val≤label ell τ x i := by
  simp only [pattern,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases hpi : 0<pivot i
  · rw [ite_eq_left hpi,div_neg_iff]
    simp only [hpi,not_lt_of_gt hpi,and_false,false_or,and_true]
    exact sub_neg.trans (floor_lt ell hτ x i k.val).symm
  · have hpn : pivot i<0 := lt_of_le_of_ne (le_of_not_gt hpi) (hp i)
    rw [ite_eq_right hpi,div_neg_iff]
    simp only [hpn,hpi,and_false,or_false,and_true]
    rw [sub_pos]
    symm
    change k.val≤⌊ell i x/τ⌋ ↔ _
    rw [Int.le_floor,le_div_iff₀ hτ]
    exact ⟨fun h => lt_of_le_of_ne h (Ne.symm (hr k.val)),le_of_lt⟩


-- @@ L234-239 verbatim
omit [DecidableEq I] in
lemma mem_weakPattern_at (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    (τ : ℝ) (s : Finset ℤ) (x : E) (i : I) (k : s) (hr : ell i x≠(k.val:ℝ)*τ) :
    (i,k)∈weakPattern ell pivot τ s x ↔ (i,k)∈pattern ell pivot τ s x := by
  simp only [weakPattern,pattern,Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨fun h => lt_of_le_of_ne h (div_ne_zero (sub_ne_zero.mpr hr) (hp i)), le_of_lt⟩


-- @@ L241-261 verbatim
omit [DecidableEq I] in
lemma boundary_pattern (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    {τ : ℝ} (hτ : 0<τ) (s : Finset ℤ) {x : E} (i : I) (k : ℤ)
    (heq : ell i x=(k:ℝ)*τ) (l : s) :
    ((i,l)∈pattern ell pivot τ s x ↔ if 0<pivot i then k<l.val else l.val<k) ∧
    ((i,l)∈weakPattern ell pivot τ s x ↔ if 0<pivot i then k≤l.val else l.val≤k) := by
  simp only [pattern,weakPattern,Finset.mem_filter,Finset.mem_univ,true_and,heq]
  by_cases hpi : 0<pivot i
  · simp only [hpi,ite_true]
    rw [div_neg_iff,div_nonpos_iff]
    simp only [hpi,hpi.le,not_le_of_gt hpi,not_lt_of_gt hpi,and_false,false_or,and_true]
    constructor
    · rw [sub_neg,mul_lt_mul_iff_left₀ hτ]; exact_mod_cast Iff.rfl
    · rw [sub_nonpos,mul_le_mul_iff_left₀ hτ]; exact_mod_cast Iff.rfl
  · have hpn : pivot i<0 := lt_of_le_of_ne (le_of_not_gt hpi) (hp i)
    simp only [hpi,ite_false]
    rw [div_neg_iff,div_nonpos_iff]
    simp only [hpi,hpn,hpn.le,not_le_of_gt hpn,and_false,or_false,and_true]
    constructor
    · rw [sub_pos,mul_lt_mul_iff_left₀ hτ]; exact_mod_cast Iff.rfl
    · rw [sub_nonneg,mul_le_mul_iff_left₀ hτ]; exact_mod_cast Iff.rfl


-- @@ L263-335 verbatim
lemma interface_extension_traces (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    {τ : ℝ} (hτ : 0<τ) (s : Finset ℤ) {U : Set E} (hU : IsOpen U)
    (hb : ∀ x∈U, regular ell τ x → ∀ i, label ell τ x i∈s)
    (F : LabelVertex ell τ U → A → ℝ) {x : E} (hx : x∈U) (i : I) (k : ℤ)
    (heq : ell i x=(k:ℝ)*τ) (hother : ∀ j, j≠i → ∀ l : ℤ, ell j x≠(l:ℝ)*τ)
    (v : E) (hv : ell i v>0) :
    ∃ vp vm : LabelVertex ell τ U,
      vp.val i=k ∧ vm.val i=k-1 ∧ (∀ j, j≠i → vp.val j=vm.val j) ∧
      (if 0<pivot i then
        extension ell pivot τ s U F (pattern ell pivot τ s x)=F vp ∧
        extension ell pivot τ s U F (weakPattern ell pivot τ s x)=F vm
      else
        extension ell pivot τ s U F (pattern ell pivot τ s x)=F vm ∧
        extension ell pivot τ s U F (weakPattern ell pivot τ s x)=F vp) := by
  obtain ⟨xp,xm,hxp,hxm,hrp,hrm,ho,hp0,hm0⟩ := neighboring_labels ell hτ hU hx i k heq hother v hv
  let vp := vertex ell τ xp hxp hrp
  let vm := vertex ell τ xm hxm hrm
  have hpv : vp.val i=k := hp0
  have hmv : vm.val i=k-1 := hm0
  refine ⟨vp,vm,hpv,hmv,(fun j hj => (ho j hj).1.trans (ho j hj).2.symm),?_⟩
  have hpp := extension_eq ell pivot hp hτ s U hb F xp hxp hrp
  have hpm := extension_eq ell pivot hp hτ s U hb F xm hxm hrm
  have hotherp (j : I) (hj : j≠i) (l : s) :
      ((j,l)∈pattern ell pivot τ s x ↔ (j,l)∈pattern ell pivot τ s xp) ∧
      ((j,l)∈pattern ell pivot τ s x ↔ (j,l)∈pattern ell pivot τ s xm) := by
    rw [mem_pattern_at ell pivot hp hτ s j (hother j hj),
      mem_pattern ell pivot hp hτ s hrp,mem_pattern ell pivot hp hτ s hrm]
    change (_ ↔ if _ then ⌊ell j xp/τ⌋<_ else _≤⌊ell j xp/τ⌋) ∧ _
    simp only [(ho j hj).1,(ho j hj).2,label]
    trivial
  by_cases hpi : 0<pivot i
  · rw [ite_eq_left hpi]
    have ep : pattern ell pivot τ s x=pattern ell pivot τ s xp := by
      ext ⟨j,l⟩
      by_cases hj : j=i
      · subst j
        rw [(boundary_pattern ell pivot hp hτ s i k heq l).1,mem_pattern ell pivot hp hτ s hrp]
        simp only [hpi,ite_true]
        change k<l.val ↔ ⌊ell i xp/τ⌋<l.val
        rw [hp0]
      · exact (hotherp j hj l).1
    have em : weakPattern ell pivot τ s x=pattern ell pivot τ s xm := by
      ext ⟨j,l⟩
      by_cases hj : j=i
      · subst j
        rw [(boundary_pattern ell pivot hp hτ s i k heq l).2,mem_pattern ell pivot hp hτ s hrm]
        simp only [hpi,ite_true]
        change k≤l.val ↔ ⌊ell i xm/τ⌋<l.val
        rw [hm0]; omega
      · rw [mem_weakPattern_at ell pivot hp τ s x j l (hother j hj l.val)]
        exact (hotherp j hj l).2
    rw [ep,em]; exact ⟨hpp,hpm⟩
  · rw [ite_eq_right hpi]
    have em : pattern ell pivot τ s x=pattern ell pivot τ s xm := by
      ext ⟨j,l⟩
      by_cases hj : j=i
      · subst j
        rw [(boundary_pattern ell pivot hp hτ s i k heq l).1,mem_pattern ell pivot hp hτ s hrm]
        simp only [hpi,ite_false]
        change l.val<k ↔ l.val≤⌊ell i xm/τ⌋
        rw [hm0]; omega
      · exact (hotherp j hj l).2
    have ep : weakPattern ell pivot τ s x=pattern ell pivot τ s xp := by
      ext ⟨j,l⟩
      by_cases hj : j=i
      · subst j
        rw [(boundary_pattern ell pivot hp hτ s i k heq l).2,mem_pattern ell pivot hp hτ s hrp]
        simp only [hpi,ite_false]
        change l.val≤k ↔ l.val≤⌊ell i xp/τ⌋
        rw [hp0]
      · rw [mem_weakPattern_at ell pivot hp τ s x j l (hother j hj l.val)]
        exact (hotherp j hj l).1
    rw [em,ep]; exact ⟨hpm,hpp⟩


-- @@ L337-356 verbatim
lemma interface_jump_bound [Fintype A]
    (ell : I → E →L[ℝ] ℝ) (pivot : I → ℝ) (hp : ∀ i, pivot i≠0)
    {τ : ℝ} (hτ : 0<τ) (s : Finset ℤ) {U : Set E} (hU : IsOpen U)
    (hb : ∀ x∈U, regular ell τ x → ∀ i, label ell τ x i∈s)
    (F : LabelVertex ell τ U → A → ℝ) {J : ℝ}
    (hF : ∀ (vp vm : LabelVertex ell τ U) (i : I), vp.val i=vm.val i+1 →
      (∀ j, j≠i → vp.val j=vm.val j) → ∑ a, |F vp a-F vm a|≤J)
    {x : E} (hx : x∈U) (i : I) (k : ℤ)
    (heq : ell i x=(k:ℝ)*τ) (hother : ∀ j, j≠i → ∀ l : ℤ, ell j x≠(l:ℝ)*τ)
    (v : E) (hv : ell i v>0) :
    ∑ a, |extension ell pivot τ s U F (weakPattern ell pivot τ s x) a-
      extension ell pivot τ s U F (pattern ell pivot τ s x) a|≤J := by
  obtain ⟨vp,vm,hvp,hvm,ho,htr⟩ := interface_extension_traces ell pivot hp hτ s hU hb F hx i k heq hother v hv
  have hbnd := hF vp vm i (by rw [hvp,hvm]; omega) ho
  by_cases hpi : 0<pivot i
  · rw [ite_eq_left hpi] at htr
    rw [htr.1,htr.2]
    simpa only [abs_sub_comm] using hbnd
  · rw [ite_eq_right hpi] at htr
    rwa [htr.1,htr.2]


-- @@ L358-358 verbatim
end

-- @@ L359-359 verbatim
end UniformSparsestCut.CellInterface


-- @@ L361-361 verbatim
end


-- @@ L363-363 verbatim
end OAI
