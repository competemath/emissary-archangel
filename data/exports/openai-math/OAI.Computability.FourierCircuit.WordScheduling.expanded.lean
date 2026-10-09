import OAI.Computability.FourierCircuit.MultiWord


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
section

-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
namespace ExactFourier.Packing

-- @@ L8-10 verbatim
variable {τ : Type} {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
  {A : ∀ t,Matrix (D t) (D t) ℂ}
  {α : Type} [Fintype α] [DecidableEq α]


-- @@ L12-13 verbatim
def scheduledStep (W : Word D A α) {T : ℕ} (time : Fin W.length→Fin T) : Fin T→Step D A α :=
  Function.extend time W.get (fun _=>.mono 1 MonomialMatrix.one)


-- @@ L15-22 verbatim
theorem scheduledStep_matrix (W : Word D A α) {T : ℕ} (time : Fin W.length→Fin T)
    (hinj : Function.Injective time) (t : Fin T) :
    (scheduledStep W time t).matrix=Function.extend time (fun i=>(W.get i).matrix) (fun _=>1) t := by
  classical
  by_cases h : ∃ i,time i=t
  · obtain ⟨i,rfl⟩ := h
    simp only [scheduledStep,hinj.extend_apply]
  · simp [scheduledStep,Function.extend_apply' _ _ _ h,Step.matrix]


-- @@ L24-31 verbatim
theorem scheduledStep_product (W : Word D A α) {T : ℕ} (time : Fin W.length→Fin T)
    (ht : StrictMono time) :
    (List.ofFn (fun t=>(scheduledStep W time t).matrix)).prod=W.matrix := by
  simp_rw [scheduledStep_matrix W time ht.injective]
  rw [ordered_padding time ht]
  change (List.ofFn (Step.matrix∘W.get)).prod=(W.map Step.matrix).prod
  rw [← List.map_ofFn]
  simp


-- @@ L33-34 verbatim
variable {π : Type} [Fintype π] [DecidableEq π]
  {β : π→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]


-- @@ L36-38 verbatim
def scheduledLayer (W : ∀ p,Word D A (β p)) {T : ℕ}
    (time : ∀ p,Fin (W p).length→Fin T) (t : Fin T) : Matrix (Σ p,β p) (Σ p,β p) ℂ :=
  Matrix.blockDiagonal' (fun p=>(scheduledStep (W p) (time p) t).matrix)


-- @@ L40-54 verbatim
/-- Schedule correctness on fixed, disjoint physical supports, including every monomial. -/
theorem scheduledLayer_product (W : ∀ p,Word D A (β p)) {T : ℕ}
    (time : ∀ p,Fin (W p).length→Fin T) (ht : ∀ p,StrictMono (time p)) :
    (List.ofFn (scheduledLayer W time)).prod=Matrix.blockDiagonal' (fun p=>(W p).matrix) := by
  let φ := Matrix.blockDiagonal'RingHom (m' := β) (α := ℂ)
  let f := fun t p=>(scheduledStep (W p) (time p) t).matrix
  change (List.ofFn (φ∘f)).prod=φ (fun p=>(W p).matrix)
  rw [← List.map_ofFn,← map_list_prod]
  congr 1
  funext p
  have he := map_list_prod (Pi.evalMonoidHom (fun p=>Matrix (β p) (β p) ℂ) p) (List.ofFn f)
  rw [List.map_ofFn] at he
  change (List.ofFn f).prod p=(List.ofFn (fun t=>f t p)).prod at he
  rw [he]
  exact scheduledStep_product (W p) (time p) (ht p)


-- @@ L56-56 verbatim
end ExactFourier.Packing


-- @@ L58-58 verbatim
end

-- @@ L59-59 verbatim
end


-- @@ L61-61 verbatim
section

-- @@ L62-62 verbatim
noncomputable section

-- @@ L63-63 verbatim
namespace ExactFourier.Packing

-- @@ L64-69 verbatim
variable {τ σ : Type}
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {E : σ→Type} [∀ t,Fintype (E t)] [∀ t,DecidableEq (E t)]
 {B : ∀ t,Matrix (E t) (E t) ℂ}
 {α : Type} [Fintype α] [DecidableEq α]


-- @@ L71-74 verbatim
def Word.substitute (V : ∀ t,Word E B (D t)) : Word D A α→Word E B α
 | [] => []
 | .mono M h::W => .mono M h::Word.substitute V W
 | .call t e::W => (V t).embed e++Word.substitute V W


-- @@ L76-83 verbatim
@[simp] theorem Word.matrix_substitute (V : ∀ t,Word E B (D t))
 (hV : ∀ t,(V t).matrix=A t) (W : Word D A α) : (W.substitute V).matrix=W.matrix := by
 induction W with
 | nil => rfl
 | cons s W ih =>
  cases s with
  | mono M h => simp only [Word.substitute,Word.matrix_cons,ih,Step.matrix]
  | call t e => simp only [Word.substitute,Word.matrix_append,Word.matrix_embed,hV,ih,Word.matrix_cons,Step.matrix]


-- @@ L85-85 verbatim
def Word.weight (p : τ→ℝ) (W : Word D A α) : ℝ := (W.calls.map p).sum


-- @@ L87-87 verbatim
@[simp] theorem Word.weight_nil (p : τ→ℝ) : Word.weight p ([] : Word D A α)=0 := rfl

-- @@ L88-89 verbatim
@[simp] theorem Word.weight_cons_mono (p : τ→ℝ) (M : Matrix α α ℂ) (h : MonomialMatrix M) (W : Word D A α) :
 Word.weight p (.mono M h::W)=W.weight p := rfl

-- @@ L90-91 verbatim
@[simp] theorem Word.weight_cons_call (p : τ→ℝ) (t : τ) (e : D t ↪ α) (W : Word D A α) :
 Word.weight p (.call t e::W)=p t+W.weight p := rfl

-- @@ L92-93 verbatim
@[simp] theorem Word.weight_append (p : τ→ℝ) (W V : Word D A α) :
 (W++V).weight p=W.weight p+V.weight p := by simp [Word.weight]

-- @@ L94-95 verbatim
@[simp] theorem Word.weight_embed {β : Type} [Fintype β] [DecidableEq β]
 (p : τ→ℝ) (e : α ↪ β) (W : Word D A α) : (W.embed e).weight p=W.weight p := by simp [Word.weight]

-- @@ L96-98 verbatim
@[simp] theorem Word.weight_reindex {β : Type} [Fintype β] [DecidableEq β]
 (p : τ→ℝ) (e : α≃β) (W : Word D A α) : (W.reindex e).weight p=W.weight p := by
 simp [Word.weight,Word.reindex]


-- @@ L100-107 verbatim
@[simp] theorem Word.weight_substitute (V : ∀ t,Word E B (D t)) (p : σ→ℝ) (W : Word D A α) :
 (W.substitute V).weight p=W.weight (fun t=>(V t).weight p) := by
 induction W with
 | nil => rfl
 | cons s W ih =>
  cases s with
  | mono M h => simpa only [Word.substitute,Word.weight_cons_mono] using ih
  | call t e => simp only [Word.substitute,Word.weight_append,Word.weight_embed,ih,Word.weight_cons_call]


-- @@ L109-122 verbatim
theorem Word.weight_count [Fintype τ] [DecidableEq τ] (p : τ→ℝ) (W : Word D A α) :
 W.weight p=∑ t,(W.count t : ℝ)*p t := by
 induction W with
 | nil => simp [Word.weight,Word.count,Word.calls]
 | cons s W ih =>
  cases s with
  | mono M h =>
   change Word.weight p W=∑ t : τ,(Word.count W t : ℝ)*p t
   exact ih
  | call t e =>
   rw [Word.weight_cons_call,ih]
   simp only [Word.count,Word.calls,List.filterMap_cons,Step.kind,List.count_eq_countP,
     List.countP_cons,Nat.cast_add,Nat.cast_ite,Nat.cast_one,Nat.cast_zero,add_mul,Finset.sum_add_distrib]
   simp [mul_comm,add_comm]


-- @@ L124-124 verbatim
end ExactFourier.Packing


-- @@ L126-126 verbatim
end

-- @@ L127-127 verbatim
end


-- @@ L129-129 verbatim
section

-- @@ L130-130 verbatim
noncomputable section

-- @@ L131-131 verbatim
namespace ExactFourier.MonomialMatrix

-- @@ L132-132 verbatim
variable {α : Type} [Fintype α] [DecidableEq α]


-- @@ L134-146 verbatim
theorem inverse {A : Matrix α α ℂ} (hA : MonomialMatrix A) : MonomialMatrix A⁻¹ := by
 obtain ⟨s,d,hd,hs⟩ := hA
 let B : Matrix α α ℂ := fun i j=>if i=s.symm j then (d (s.symm j))⁻¹ else 0
 have hB : MonomialMatrix B := ⟨s.symm,fun j=>(d (s.symm j))⁻¹,fun j=>inv_ne_zero (hd _),fun _ _=>rfl⟩
 have he : A*B=1 := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [B,mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true,hs,s.apply_symm_apply]
  by_cases h : i=j
  · subst j; simp [hd]
  · simp [h]
 rw [Matrix.inv_eq_right_inv he]
 exact hB


-- @@ L148-191 verbatim
/-- A unit square submatrix of a monomial matrix is monomial. -/
theorem submatrix_unit {β : Type} [Fintype β] [DecidableEq β]
 {B : Matrix β β ℂ} (hB : MonomialMatrix B) (e f : α ↪ β)
 (hA : IsUnit (B.submatrix e f)) : MonomialMatrix (B.submatrix e f) := by
 let A := B.submatrix e f
 have hi := Matrix.nonsing_inv_mul A ((Matrix.isUnit_iff_isUnit_det A).mp hA)
 have hc : ∀ k,∃ i,A⁻¹ k i*A i k≠0 := by
  intro k
  have he := congrArg (fun M : Matrix α α ℂ=>M k k) hi
  simp only [Matrix.mul_apply,Matrix.one_apply,ite_true] at he
  by_contra hn
  push Not at hn
  rw [Finset.sum_eq_zero (fun i _=>hn i)] at he
  exact zero_ne_one he
 choose σ hσ using hc
 have hc₁ : ∀ k,A⁻¹ k (σ k)≠0 := fun k=>(mul_ne_zero_iff.mp (hσ k)).1
 have hc₂ : ∀ k,A (σ k) k≠0 := fun k=>(mul_ne_zero_iff.mp (hσ k)).2
 obtain ⟨s,d,hd,hs⟩ := hB
 have hz : ∀ k i,i≠σ k → A i k=0 := by
  intro k i hik
  have he : e (σ k)=s (f k) := by
   by_contra h
   exact hc₂ k (by simp [A,Matrix.submatrix_apply,hs,h])
  have hn : e i≠s (f k) := by intro hh; exact hik (e.injective (hh.trans he.symm))
  simp [A,Matrix.submatrix_apply,hs,hn]
 have hinj : Function.Injective σ := by
  intro k l hkl
  by_contra hne
  have hh := congrArg (fun M : Matrix α α ℂ=>M k l) hi
  simp only [Matrix.mul_apply,Matrix.one_apply,ite_eq_right hne] at hh
  have hsum : (∑ i,A⁻¹ k i*A i l)=A⁻¹ k (σ l)*A (σ l) l := by
   apply Finset.sum_eq_single (σ l)
   · intro i _ hne; rw [hz l i hne,mul_zero]
   · simp
  rw [hsum] at hh
  apply mul_ne_zero (hc₁ k) (hc₂ l)
  simpa only [hkl] using hh
 let g : Equiv.Perm α := Equiv.ofBijective σ ⟨hinj,Finite.surjective_of_injective hinj⟩
 refine ⟨g,fun k=>A (σ k) k,hc₂,?_⟩
 intro i k
 change A i k=if i=σ k then A (σ k) k else 0
 split_ifs with h
 · subst i; rfl
 · exact hz k i h


-- @@ L193-193 verbatim
end ExactFourier.MonomialMatrix


-- @@ L195-195 verbatim
end

-- @@ L196-196 verbatim
end


-- @@ L198-198 verbatim
section

-- @@ L199-199 verbatim
noncomputable section

-- @@ L200-200 verbatim
namespace ExactFourier.Packing

-- @@ L201-204 verbatim
variable {τ : Type}
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {α : Type} [Fintype α] [DecidableEq α]


-- @@ L206-218 verbatim
theorem pattern_from_word (V : Word D A α) {H : Matrix α α ℂ} {h : ℕ}
 (hp : PositiveGeneration.Pattern V.matrix h H) :
 ∃ W : Word D A α,W.matrix=H ∧ ∀ p : τ→ℝ,W.weight p=(h : ℝ)*V.weight p := by
 induction hp with
 | zero M hm => exact ⟨monoWord M hm,by simp,fun p=>by simp [Word.weight]⟩
 | @succ h H hp M hm ih =>
  obtain ⟨W,hW,hp⟩ := ih
  refine ⟨W++V++monoWord M hm,by simp [hW,mul_assoc],?_⟩
  intro p
  rw [Word.weight_append,Word.weight_append,hp]
  change (h : ℝ)*V.weight p+V.weight p+0=_
  push_cast
  ring


-- @@ L220-224 verbatim
theorem word_generates (V : Word D A α) (hu : IsUnit V.matrix) (hn : ¬MonomialMatrix V.matrix)
 (H : Matrix α α ℂ) (hH : IsUnit H) :
 ∃ h : ℕ,0<h ∧ ∃ W : Word D A α,W.matrix=H ∧ ∀ p : τ→ℝ,W.weight p=(h : ℝ)*V.weight p := by
 obtain ⟨h,hh,hg⟩ := PositiveGeneration.positive_generation V.matrix hu hn
 exact ⟨h,hh,pattern_from_word V (hg H hH)⟩


-- @@ L226-238 verbatim
theorem monomial_of_subsingleton [Subsingleton α] (H : Matrix α α ℂ) (hH : IsUnit H) : MonomialMatrix H := by
 have he : H=Matrix.diagonal (fun i=>H i i) := by
  ext i j
  have h : i=j := Subsingleton.elim _ _
  subst j
  simp
 have hu : ∀ i,H i i≠0 := by
  rw [he] at hH
  have hh := Pi.isUnit_iff.mp (Matrix.isUnit_diagonal.mp hH)
  intro i
  exact isUnit_iff_ne_zero.mp (hh i)
 rw [he]
 exact MonomialMatrix.diagonal _ hu


-- @@ L240-240 verbatim
def shearU : Matrix (Fin 2) (Fin 2) ℂ := Matrix.transvection 1 0 1


-- @@ L242-242 verbatim
theorem shearU_unit : IsUnit shearU := MatrixPrice.transvection_isUnit 1 0 (by decide) 1


-- @@ L244-255 verbatim
theorem shearU_not_monomial : ¬MonomialMatrix shearU := by
 rintro ⟨s,d,hd,hs⟩
 have h0 : (0 : Fin 2)=s 0 := by
  by_contra h
  have hh := hs 0 0
  simp [shearU,Matrix.transvection,h] at hh
 have h1 : (1 : Fin 2)=s 0 := by
  by_contra h
  have hh := hs 1 0
  simp [shearU,Matrix.transvection,h] at hh
 have hh : (0 : Fin 2)=1 := h0.trans h1.symm
 exact (by decide : (0 : Fin 2)≠1) hh


-- @@ L257-288 verbatim
theorem shear_word_exists (u : τ) (eu : D u≃Fin 2)
 (hAu : Matrix.reindex eu eu (A u)=shearU)
 (H : Matrix α α ℂ) (hH : IsUnit H) :
 ∃ C : ℕ,∃ W : Word D A α,W.matrix=H ∧ ∀ p : τ→ℝ,W.weight p=(C : ℝ)*p u := by
 classical
 by_cases hc : 2≤Fintype.card α
 · let e : D u ↪ α := eu.toEmbedding.trans
    ((Fin.castLEEmb hc).trans (Fintype.equivFin α).symm.toEmbedding)
   let V : Word D A α := callWord u e
   have hu : IsUnit (A u) := by
    have hh := TensorTools.unit_reindex eu.symm _ shearU_unit
    rw [← hAu] at hh
    convert hh using 1
    ext i j
    simp [Matrix.reindex_apply]
   have hn : ¬MonomialMatrix (A u) := by
    intro hh; exact shearU_not_monomial (hAu ▸ hh.reindex eu)
   have hV : V.matrix=Embedded.matrix e (A u) := matrix_callWord u e
   have hVm : ¬MonomialMatrix V.matrix := by
    intro hh
    rw [hV] at hh
    have he : (Embedded.matrix e (A u)).submatrix e e=A u := by
     ext i j; exact Embedded.matrix_on e _ i j
    apply hn
    rw [← he]
    exact hh.submatrix_unit e e (he.symm ▸ hu)
   obtain ⟨h,hh,W,hm,hp⟩ := word_generates V (hV.symm ▸ Embedded.unit e _ hu) hVm H hH
   exact ⟨h,W,hm,fun p=>by simpa [V,Word.weight] using hp p⟩
 · have hcard : Fintype.card α≤1 := by omega
   let : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp hcard
   have hm := monomial_of_subsingleton H hH
   exact ⟨0,monoWord H hm,by simp,fun p=>by simp [Word.weight]⟩


-- @@ L290-290 verbatim
end ExactFourier.Packing


-- @@ L292-292 verbatim
end

-- @@ L293-293 verbatim
end


-- @@ L295-295 verbatim
section

-- @@ L296-296 verbatim
namespace ExactFourier

-- @@ L297-298 verbatim
variable {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ]


-- @@ L300-302 verbatim
theorem reindex_comp
    {α : Type} {β : Type} {γ : Type} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] (e : α≃β) (f : β≃γ) (M : Matrix α α ℂ) :
 Matrix.reindex f f (Matrix.reindex e e M)=Matrix.reindex (e.trans f) (e.trans f) M := rfl


-- @@ L304-309 verbatim
theorem reindex_sum
    {α : Type} {β : Type} {γ : Type} {δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ] (e : α≃β) (f : γ≃δ) (M : Matrix α α ℂ) (N : Matrix γ γ ℂ) :
 Matrix.reindex (e.sumCongr f) (e.sumCongr f) (Matrix.fromBlocks M 0 0 N)=
 Matrix.fromBlocks (Matrix.reindex e e M) 0 0 (Matrix.reindex f f N) := by
 ext x y
 cases x <;> cases y <;> rfl


-- @@ L311-316 verbatim
theorem reindex_tensor
    {α : Type} {β : Type} {γ : Type} {δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [DecidableEq α] [DecidableEq β] [DecidableEq γ] [DecidableEq δ] (e : α≃β) (f : γ≃δ) (M : Matrix α α ℂ) (N : Matrix γ γ ℂ) :
 Matrix.reindex (e.prodCongr f) (e.prodCongr f) (Matrix.kronecker M N)=
 Matrix.kronecker (Matrix.reindex e e M) (Matrix.reindex f f N) := by
 ext x y
 rfl


-- @@ L318-321 verbatim
theorem reindex_inverse
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (e : α≃β) (M : Matrix α α ℂ) :
 Matrix.reindex e.symm e.symm (Matrix.reindex e e M)=M := by
 ext i j; simp [Matrix.reindex_apply]

-- @@ L322-322 verbatim
end ExactFourier


-- @@ L324-324 verbatim
end


-- @@ L326-326 verbatim
section

-- @@ L327-327 verbatim
noncomputable section

-- @@ L328-328 verbatim
namespace ExactFourier

-- @@ L329-329 verbatim
namespace Embedded

-- @@ L330-331 verbatim
variable {α β γ : Type} [Fintype α] [Fintype β] [Fintype γ]
 [DecidableEq α] [DecidableEq β] [DecidableEq γ]

-- @@ L332-349 verbatim
theorem matrix_domain (e : α≃β) (f : α ↪ γ) (M : Matrix α α ℂ) :
 matrix (e.symm.toEmbedding.trans f) (Matrix.reindex e e M)=matrix f M := by
 classical
 ext i j
 by_cases hi : ∃ a,f a=i
 · obtain ⟨a,rfl⟩ := hi
   by_cases hj : ∃ b,f b=j
   · obtain ⟨b,rfl⟩ := hj
     have ha : (e.symm.toEmbedding.trans f) (e a)=f a := by simp
     have hb : (e.symm.toEmbedding.trans f) (e b)=f b := by simp
     rw [← ha,← hb,matrix_on]
     simp only [ha,hb,matrix_on,Matrix.reindex_apply,Matrix.submatrix_apply,Equiv.symm_apply_apply]
   · have hj' : ¬∃ b,(e.symm.toEmbedding.trans f) b=j := by
      rintro ⟨b,hb⟩; exact hj ⟨e.symm b,hb⟩
     rw [matrix_off_col _ _ _ _ hj',matrix_off_col _ _ _ _ hj]
 · have hi' : ¬∃ a,(e.symm.toEmbedding.trans f) a=i := by
    rintro ⟨a,ha⟩; exact hi ⟨e.symm a,ha⟩
   rw [matrix_off_row _ _ _ _ hi',matrix_off_row _ _ _ _ hi]

-- @@ L350-350 verbatim
end Embedded

-- @@ L351-351 verbatim
namespace Packing

-- @@ L352-357 verbatim
variable {τ σ : Type}
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {E : σ→Type} [∀ t,Fintype (E t)] [∀ t,DecidableEq (E t)]
 {B : ∀ t,Matrix (E t) (E t) ℂ}
 {α : Type} [Fintype α] [DecidableEq α]


-- @@ L359-361 verbatim
def Step.rename (f : τ→σ) (e : ∀ t,D t≃E (f t)) : Step D A α→Step E B α
 | .mono M h => .mono M h
 | .call t a => .call (f t) ((e t).symm.toEmbedding.trans a)

-- @@ L362-363 verbatim
def Word.rename (f : τ→σ) (e : ∀ t,D t≃E (f t)) (W : Word D A α) : Word E B α :=
 W.map (Step.rename f e)

-- @@ L364-377 verbatim
theorem Word.matrix_rename (f : τ→σ) (e : ∀ t,D t≃E (f t))
 (he : ∀ t,Matrix.reindex (e t) (e t) (A t)=B (f t)) (W : Word D A α) :
 (W.rename (B := B) f e).matrix=W.matrix := by
 induction W with
 | nil => rfl
 | cons s W ih =>
  simp only [Word.rename,List.map_cons,Word.matrix_cons]
  rw [← Word.rename,ih]
  congr 1
  cases s with
  | mono M h => rfl
  | call t a =>
   change Embedded.matrix _ (B (f t))=Embedded.matrix a (A t)
   rw [← he t,Embedded.matrix_domain]

-- @@ L378-385 verbatim
@[simp] theorem Word.weight_rename (f : τ→σ) (e : ∀ t,D t≃E (f t))
 (p : σ→ℝ) (W : Word D A α) : (W.rename (B := B) f e).weight p=W.weight (p∘f) := by
 induction W with
 | nil => rfl
 | cons s W ih =>
  cases s with
  | mono M h => simpa only [Word.rename,List.map_cons,Step.rename,Word.weight_cons_mono] using ih
  | call t a => simpa only [Word.rename,List.map_cons,Step.rename,Word.weight_cons_call,Function.comp_apply] using congrArg (fun x=>p (f t)+x) ih

-- @@ L386-386 verbatim
end Packing

-- @@ L387-387 verbatim
end ExactFourier


-- @@ L389-389 verbatim
end

-- @@ L390-390 verbatim
end


-- @@ L392-392 verbatim
end OAI
