import OAI.Analysis.FourierLLogL.Dyadic.Circle


-- @@ L3-3 verbatim
/-! # Finite dyadic blocks and probabilities -/

-- @@ L4-4 verbatim
open Function Set Filter

-- @@ L5-5 verbatim
open scoped Topology BigOperators ComplexConjugate Real


-- @@ L7-7 verbatim
noncomputable section

-- @@ L8-8 verbatim
namespace OAI


-- @@ L10-10 verbatim
namespace FourierLLogL.Dyadic

-- @@ L11-11 verbatim
open Period Law

-- @@ L12-12 verbatim
namespace Node


-- @@ L14-14 verbatim
variable {M : ℕ}


-- @@ L16-16 verbatim
def invlen (p : Node) : ℝ := 2^p.lev


-- @@ L18-18 verbatim
lemma rinv (p : Node) : invlen p = p.len⁻¹ := by rw [len,side_pow_two,inv_inv]; rfl


-- @@ L20-20 verbatim
lemma invlen_ge (p : Node) : 1 ≤ invlen p := one_le_pow₀ (by norm_num)


-- @@ L22-22 verbatim
lemma invlen_pos (p : Node) : 0 < invlen p := lt_of_lt_of_le zero_lt_one p.invlen_ge


-- @@ L24-28 verbatim
lemma descale {p : Node} (h : p.lev ≤ M) :
    p.len = side M * (2:ℝ)^(M-p.lev) := by
  rw [len,side_pow_two,side_pow_two]
  conv_rhs => lhs; rw [show M=p.lev+(M-p.lev) by omega]
  rw [pow_add]; field_simp


-- @@ L30-38 verbatim
lemma mem_block_iff {p : Node} (h : p.lev ≤ M) (x : Grid M) :
    x ∈ p.block M ↔ p.ix*2^(M-p.lev) ≤ x.val ∧ x.val < (p.ix+1)*2^(M-p.lev) := by
  change p.a ≤ pos x ∧ _ < p.a+p.len ↔ _
  have he (i : ℕ) : (i:ℝ)*p.len = (i*2^(M-p.lev) : ℕ) * side M := by
    rw [descale h]; push_cast; ring
  unfold a pos
  rw [show p.ix*p.len+p.len=↑(p.ix+1)*p.len by push_cast; ring, he,he,
    mul_le_mul_iff_left₀ (side_pos _),mul_lt_mul_iff_left₀ (side_pos _)]
  norm_cast


-- @@ L40-41 verbatim
/-- First grid index in a fitting node. -/
def idx (p : Node) (M : ℕ) := p.ix * 2^(M-p.lev)

-- @@ L42-42 verbatim
def wid (p : Node) (M : ℕ) := 2^(M-p.lev)


-- @@ L44-50 verbatim
lemma fitting (p : Node) (hv : p.valid) (h : p.lev ≤ M) :
    p.idx M+p.wid M ≤ 2^M := by
  unfold idx wid
  calc
    _ = (p.ix+1)*2^(M-p.lev) := by ring
    _ ≤ 2^p.lev*2^(M-p.lev) := Nat.mul_le_mul_right _ hv
    _ = _ := by rw [← pow_add]; congr 1; omega


-- @@ L52-52 verbatim
lemma wid_pos (p : Node) (M : ℕ) : 0 < p.wid M := pow_pos (by omega) _


-- @@ L54-54 verbatim
def start (p : Node) (M : ℕ) : Grid M := (p.idx M : Grid M)


-- @@ L56-61 verbatim
lemma start_val {p : Node} (hv : p.valid) (h : p.lev ≤ M) :
    (p.start M).val = p.idx M := by
  apply ZMod.val_natCast_of_lt
  have HH := p.fitting hv h
  have HH' := p.wid_pos M
  omega


-- @@ L63-66 verbatim
lemma start_pos {p : Node} (hv : p.valid) (h : p.lev ≤ M) :
    pos (p.start M) = p.a := by
  rw [pos, start_val hv h,a,descale h]
  unfold idx; push_cast; ring


-- @@ L68-74 verbatim
lemma start_mem {p : Node} (hv : p.valid) (h : p.lev ≤ M) :
    p.start M ∈ p.block M := by
  rw [mem_block_iff h,start_val hv h]
  unfold idx
  constructor
  · exact le_rfl
  · gcongr; omega


-- @@ L76-76 verbatim
open scoped Classical

-- @@ L77-78 verbatim
/-- Finset of vertices. -/
def group (p : Node) (M : ℕ) := (p.block M).toFinset


-- @@ L80-80 verbatim
lemma mem_group (p : Node) (x : Grid M) : x ∈ p.group M ↔ x ∈ p.block M := by simp [group]


-- @@ L82-85 verbatim
lemma group_range {p : Node} (h : p.lev ≤ M) :
    p.group M = first M (p.idx M+p.wid M) \ first M (p.idx M) := by
  ext i; simp only [mem_group, Finset.mem_sdiff, mem_first, mem_block_iff h]
  unfold idx wid; rw [add_mul,one_mul]; omega


-- @@ L87-95 verbatim
lemma group_card {p : Node} (hv : p.valid) (h : p.lev ≤ M) :
    (p.group M).card = p.wid M := by
  have hh := p.fitting hv h
  rw [group_range h,Finset.card_sdiff_of_subset ?sub,first_card _ hh,first_card _ (by omega)]
  · omega
  case sub =>
    intro x hx
    simp_rw [mem_first] at *
    omega


-- @@ L97-100 verbatim
lemma group_size {p : Node} (hv : p.valid) (h : p.lev ≤ M) :
    (p.group M).card * side M = p.len := by
  rw [group_card hv h,descale h]
  unfold wid; push_cast; ring


-- @@ L102-106 verbatim
lemma block_separate (p : Node) (M : ℕ) :
    Disjoint (p.L.block M) (p.R.block M) := by
  refine Set.disjoint_left.mpr fun x hx hy => ?_
  exact Set.disjoint_left.mp (cells_dis (k:=p.ix*2) (l:=p.ix*2+1) (by omega)
    (n:=p.lev+1)) hx hy


-- @@ L108-109 verbatim
lemma block_union (p : Node) (M : ℕ) :
    p.block M = p.L.block M ∪ p.R.block M := by rw [block,p.cells_split]; rfl


-- @@ L111-114 verbatim
lemma group_dis (p : Node) (M : ℕ) :
    Disjoint (p.L.group M) (p.R.group M) :=
  Finset.disjoint_left.mpr fun _ hx hy => Set.disjoint_left.mp (p.block_separate _)
      ((mem_group _ _).mp hx) ((mem_group _ _).mp hy)


-- @@ L116-117 verbatim
lemma group_union (p : Node) (M : ℕ) :
    p.group M = p.L.group M ∪ p.R.group M := by ext x; simp only [Finset.mem_union,mem_group]; rw [p.block_union]; rfl


-- @@ L119-119 verbatim
def ok (p : Node) (M : ℕ) : Prop := p.valid ∧ p.lev ≤ M


-- @@ L121-121 verbatim
lemma root_ok (M : ℕ) : ok root M := by simp [ok,valid,root]

-- @@ L122-122 verbatim
lemma len_top : root.len = 1 := by simp [len,root,side]

-- @@ L123-123 verbatim
lemma invlen_top : root.invlen = 1 := by simp [invlen,root]

-- @@ L124-127 verbatim
lemma group_top (M : ℕ) : root.group M = Finset.univ := by
  ext x; rw [mem_group,mem_block_iff (root_ok M).2]
  simp only [root, Nat.zero_mul, Nat.zero_le, true_and, zero_add,one_mul,Nat.sub_zero]
  simp [ZMod.val_lt]


-- @@ L129-129 verbatim
open scoped Classical


-- @@ L131-142 verbatim
/-- Local averages as sums. -/
lemma avg_sum {E : Type*} [AddCommMonoid E] [SMul ℝ E] (p : Node)
    (f : Grid M → E) :
    p.avg f = p.len⁻¹ • (side M • ∑ x ∈ p.group M, f x) := by
  unfold avg expU
  congr 2
  calc
    _ = ∑ x ∈ p.group M, (p.block M).indicator f x := by
      refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
      intro i _ hi
      apply Set.indicator_of_notMem ((mem_group _ _).not.mp hi) f
    _ = _ := Finset.sum_congr rfl fun i hi => Set.indicator_of_mem ((mem_group _ _).mp hi) f


-- @@ L144-148 verbatim
lemma avg_nonneg (p : Node) {f : Grid M → ℝ} (h : ∀ x, x∈p.block M → 0 ≤ f x) :
    0 ≤ p.avg f := by
  rw [avg_sum, smul_eq_mul, smul_eq_mul]
  exact mul_nonneg (inv_nonneg.mpr p.len_pos.le) <| mul_nonneg (side_pos _).le
    (Finset.sum_nonneg fun i hi => h _ ((mem_group _ _).mp hi))


-- @@ L150-152 verbatim
lemma avg_split_real (p : Node) (f : Grid M → ℝ) :
    p.avg f = (p.L.avg f+p.R.avg f)/2 := by
  rw [avg_sum,avg_sum,avg_sum,p.group_union,Finset.sum_union (p.group_dis M),p.len_L,p.len_R]; simp; ring


-- @@ L154-157 verbatim
lemma avg_split_complex (p : Node) (f : Grid M → ℂ) :
    p.avg f = (p.L.avg f+p.R.avg f)/2 := by
  rw [avg_sum,avg_sum,avg_sum,p.group_union,Finset.sum_union (p.group_dis M),p.len_L,p.len_R]
  simp_rw [Complex.real_smul]; push_cast; ring_nf


-- @@ L159-160 verbatim
/-- Uniform conditional law on a block (total default law if not fitting). -/
def dice (p : Node) (M : ℕ) : Law (Grid M) := (uniform _).condP fun x => x ∈ p.block M


-- @@ L162-168 verbatim
lemma prob_block {p : Node} (h : p.ok M) :
    (uniform (Grid M)).prob (fun x => x∈p.block M) = p.len := by
  rw [prob_eq]
  have He : Finset.univ.filter (fun x : Grid M => x∈p.block M)=p.group M := by
    ext x; simp [mem_group]
  rw [← Finset.sum_filter, He]
  simp_rw [uniform_side,Finset.sum_const,nsmul_eq_mul,group_size h.1 h.2]


-- @@ L170-174 verbatim
lemma dice_apply {p : Node} (h : p.ok M) (x : Grid M) :
    p.dice M x = if x∈p.block M then side M * p.len⁻¹ else 0 := by
  unfold dice
  rw [condP_pos_apply _ _ (by rw [prob_block h]; exact p.len_pos),prob_block h,uniform_side]
  split_ifs <;> simp [div_eq_mul_inv]

-- @@ L175-179 verbatim
lemma dice_positive {p : Node} (h : p.ok M) {x : Grid M} :
    0 < p.dice M x ↔ x ∈ p.block M := by
  rw [dice_apply h]; split_ifs with hh
  · exact iff_of_true (mul_pos (side_pos _) (inv_pos.mpr p.len_pos)) hh
  · simp [hh]


-- @@ L181-187 verbatim
lemma avg_ex {p : Node} (h : p.ok M) (f : Grid M → ℝ) :
    p.avg f = (p.dice M).Ex f := by
  simp_rw [avg,smul_eq_mul,expU_ex,Ex,dice_apply h,uniform_side,Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [Set.indicator_of_mem hi]; ring
  rw [Set.indicator_of_notMem hi]; ring


-- @@ L189-195 verbatim
lemma avg_cx {p : Node} (h : p.ok M) (f : Grid M → ℂ) :
    p.avg f = (p.dice M).Cx f := by
  simp_rw [avg,Complex.real_smul,expU_cx,Cx,dice_apply h,uniform_side,Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs with hi
  · rw [Set.indicator_of_mem hi]; push_cast; ring
  rw [Set.indicator_of_notMem hi]; push_cast; ring


-- @@ L197-203 verbatim
lemma dice_child (p : Node) (hv : p.valid) (h : p.lev < M) (f : Grid M → ℝ) :
    (p.dice M).Ex f = ((p.L.dice M).Ex f + (p.R.dice M).Ex f)/2 := by
  have H : ok p M := ⟨hv,h.le⟩
  have H1 : ok p.L M := ⟨p.valid_L.mpr hv,h⟩
  have H2 : ok p.R M := ⟨p.valid_R.mpr hv,h⟩
  rw [← avg_ex H,← avg_ex H1,← avg_ex H2]
  exact p.avg_split_real _


-- @@ L205-206 verbatim
/-- Called branching. -/
def below (p q : Node) : Prop := p.lev ≥ q.lev ∧ p.cells ⊆ q.cells


-- @@ L208-210 verbatim
lemma below_left (p : Node) : p.L.below p := by
  refine ⟨Nat.le_add_right _ 1,?_⟩
  rw [cells_split p]; exact subset_union_left

-- @@ L211-213 verbatim
lemma below_right (p : Node) : p.R.below p := by
  refine ⟨Nat.le_add_right _ 1,?_⟩
  rw [cells_split p]; exact subset_union_right


-- @@ L215-215 verbatim
lemma below_refl (p : Node) : p.below p := ⟨le_rfl,Subset.rfl⟩


-- @@ L217-218 verbatim
lemma below_trans {p q r : Node} (h : p.below q) (h' : q.below r) : p.below r :=
  ⟨h'.1.trans h.1,h.2.trans h'.2⟩


-- @@ L220-221 verbatim
lemma block_of_below {p q : Node} (h : p.below q) (M : ℕ) : p.block M ⊆ q.block M :=
  Set.preimage_mono h.2


-- @@ L223-224 verbatim
lemma scale_below {p q : Node} (h : p.below q) : q.invlen ≤ p.invlen :=
  pow_le_pow_right₀ (by norm_num) h.1


-- @@ L226-227 verbatim
lemma diam_block {p : Node} {x y : Grid M} (hx : x ∈ p.block M) (hy : y ∈ p.block M) :
    |pos x-pos y| ≤ p.len := by rw [abs_le]; constructor <;> linarith [hx.1,hx.2,hy.1,hy.2]


-- @@ L229-229 verbatim
end Node

-- @@ L230-230 verbatim
end FourierLLogL.Dyadic


-- @@ L232-232 verbatim
end OAI
