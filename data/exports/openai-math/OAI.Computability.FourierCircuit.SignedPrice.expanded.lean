import OAI.Computability.FourierCircuit.RawPositive


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
section

-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
namespace ExactFourier.SignedBits

-- @@ L8-8 verbatim
open scoped Matrix Kronecker


-- @@ L10-10 verbatim
local instance (m : ℕ) : LinearOrder (Bits m ⊕ Bits m) := bitsLinearOrder (m+1)

-- @@ L11-11 verbatim
local instance (m : ℕ) : LT (Bits m ⊕ Bits m) := (bitsLinearOrder (m+1)).toLT


-- @@ L13-14 verbatim
def start (m : ℕ) : Matrix (Bits (m+1)) (Bits (m+1)) ℂ :=
  Matrix.fromBlocks (T m) 0 (T m) (T m)

-- @@ L15-16 verbatim
def oldInputs (m : ℕ) : Matrix (Bits (m+1)) (Bits (m+1)) ℂ :=
  Matrix.fromBlocks (1 : Matrix (Bits m) (Bits m) ℂ) 0 (T m) (T m)

-- @@ L17-18 verbatim
def oldOutputs (m : ℕ) : Matrix (Bits (m+1)) (Bits (m+1)) ℂ :=
  Matrix.fromBlocks (T m) 0 0 (1 : Matrix (Bits m) (Bits m) ℂ)

-- @@ L19-20 verbatim
def transition (m : ℕ) : Matrix (Bits (m+1)) (Bits (m+1)) ℂ :=
  Matrix.fromBlocks (T m) 0 (-1) (T m)⁻¹


-- @@ L22-31 verbatim
theorem start_lower (m : ℕ) : (start m).IsLowerTriangular := by
  intro i j hij
  change (toLex i : Bits m ⊕ₗ Bits m) < toLex j at hij
  rcases i with i|i <;> rcases j with j|j
  · have hh : i<j := Sum.Lex.inl_lt_inl_iff.mp hij
    exact T_lower m hh
  · rfl
  · exact False.elim (Sum.Lex.not_inr_lt_inl hij)
  · have hh : i<j := Sum.Lex.inr_lt_inr_iff.mp hij
    exact T_lower m hh


-- @@ L33-34 verbatim
theorem start_diag (m : ℕ) : ∀ i,start m i i=1 := by
  intro i; rcases i with i|i <;> simp [start,T_diag]


-- @@ L36-36 verbatim
def bottom (m : ℕ) : Finset (Bits (m+1)) := Finset.univ.filter (fun i => i.isRight = true)


-- @@ L38-40 verbatim
theorem input_rows (m : ℕ) : BasisExchange.rows (start m) (bottom m)=oldInputs m := by
  ext i j; rcases i with i|i <;> rcases j with j|j <;>
    simp [BasisExchange.rows,start,oldInputs,bottom,Matrix.one_apply]


-- @@ L42-44 verbatim
theorem output_rows (m : ℕ) : BasisExchange.rows (start m) (bottom m)ᶜ=oldOutputs m := by
  ext i j; rcases i with i|i <;> rcases j with j|j <;>
    simp [BasisExchange.rows,start,oldOutputs,bottom,Matrix.one_apply]


-- @@ L46-48 verbatim
theorem transition_solve (m : ℕ) : transition m*oldInputs m=oldOutputs m := by
  simp [transition,oldInputs,oldOutputs,Matrix.fromBlocks_multiply,
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (T_unit m))]


-- @@ L50-52 verbatim
theorem transition_eq (m : ℕ) : transition m=oldOutputs m*(oldInputs m)⁻¹ := by
  have hU : IsUnit (oldInputs m) := Matrix.isUnit_fromBlocks_zero₁₂.mpr ⟨isUnit_one,T_unit m⟩
  rw [← transition_solve,Matrix.mul_nonsing_inv_cancel_right _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)]


-- @@ L54-55 verbatim
def zdiag (m : ℕ) : Matrix (Bits (m+1)) (Bits (m+1)) ℂ :=
  Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1))


-- @@ L57-59 verbatim
theorem zdiag_monomial (m : ℕ) : MonomialMatrix (zdiag m) := by
  apply MonomialMatrix.diagonal
  intro i; rcases i with i|i <;> norm_num


-- @@ L61-64 verbatim
theorem transition_sign (m : ℕ) : zdiag m*transition m*zdiag m=T (m+1) := by
  rw [T_succ]
  ext i j; rcases i with i|i <;> rcases j with j|j <;>
    simp [zdiag,transition,Matrix.diagonal_mul,Matrix.mul_diagonal]


-- @@ L66-69 verbatim
theorem start_tensor (m : ℕ) : start m=Matrix.reindex (twoProdEquiv (Bits m)) (twoProdEquiv (Bits m))
    (Matrix.transvection (1 : Fin 2) 0 (1 : ℂ)⊗ₖT m) := by
  ext i j; rcases i with i|i <;> rcases j with j|j <;>
    simp [start,Matrix.reindex_apply,twoProdEquiv,Matrix.transvection,Matrix.single]


-- @@ L71-82 verbatim
theorem price_step (p : MatrixPrice) (m : ℕ) :
    p.value (T (m+1))=2^m+2*p.value (T m) := by
  have hp := BasisExchange.price_triangular p (start m) (start_lower m) (start_diag m) (bottom m)
  rw [input_rows,output_rows,← transition_eq] at hp
  have hW : IsUnit (transition m) := Matrix.isUnit_fromBlocks_zero₁₂.mpr
    ⟨T_unit m,Matrix.isUnit_nonsing_inv_iff.mpr (T_unit m)⟩
  have hm := p.monomial (transition m) (zdiag m) (zdiag m) hW (zdiag_monomial m) (zdiag_monomial m)
  rw [transition_sign,hp,start_tensor,p.reindex _ _ (TensorTools.unit_tensor _ _
      (MatrixPrice.transvection_isUnit _ _ (by decide) _) (T_unit m)),
    p.tensor _ _ (MatrixPrice.transvection_isUnit _ _ (by decide) _) (T_unit m),p.normalized,bits_card] at hm
  norm_num at hm
  exact hm


-- @@ L84-88 verbatim
theorem price (p : MatrixPrice) (m : ℕ) :
    2*p.value (T m)=(m : ℝ)*2^m := by
  induction m with
  | zero => simp [T,D,p.one]
  | succ m ih => rw [price_step,pow_succ]; push_cast; nlinarith


-- @@ L90-90 verbatim
end ExactFourier.SignedBits


-- @@ L92-92 verbatim
end

-- @@ L93-93 verbatim
end


-- @@ L95-95 verbatim
section

-- @@ L96-96 verbatim
noncomputable section

-- @@ L97-97 verbatim
namespace ExactFourier.SignedBits

-- @@ L98-98 verbatim
open scoped Matrix Kronecker


-- @@ L100-103 verbatim
def J : (m : ℕ) → Bool → Matrix (Bits m) (Bits m) ℂ
  | 0, _ => 1
  | m+1, false => Matrix.fromBlocks 0 (J m true) (J m true) 0
  | m+1, true => Matrix.fromBlocks 0 (J m false) (-J m false) 0


-- @@ L105-111 verbatim
theorem J_commute (m : ℕ) (b : Bool) :
    J m b*D m=(if b then -(D m).transpose else (D m).transpose)*J m b := by
  induction m generalizing b with
  | zero => simp [J,D]
  | succ m ih =>
    cases b <;>
      simp [J,D,Matrix.fromBlocks_multiply,Matrix.fromBlocks_transpose,ih true,ih false,Matrix.fromBlocks_neg]


-- @@ L113-119 verbatim
theorem J_orthogonal (m : ℕ) (b : Bool) : J m b*(J m b).transpose=1 := by
  induction m generalizing b with
  | zero => simp [J]
  | succ m ih =>
    cases b <;>
      simp [J,Matrix.fromBlocks_multiply,Matrix.fromBlocks_transpose,ih,
        ← Matrix.fromBlocks_one]


-- @@ L121-131 verbatim
theorem J_sign (m : ℕ) (b : Bool) : ∃ s : ℂ,s*s=1 ∧ (J m b).transpose=s•J m b := by
  induction m generalizing b with
  | zero => exact ⟨1,by simp,by simp [J]⟩
  | succ m ih =>
    cases b
    · obtain ⟨s,hs,he⟩ := ih true
      refine ⟨s,hs,?_⟩
      simp [J,Matrix.fromBlocks_transpose,he,Matrix.fromBlocks_smul]
    · obtain ⟨s,hs,he⟩ := ih false
      refine ⟨-s,by simpa using hs,?_⟩
      simp [J,Matrix.fromBlocks_transpose,he,Matrix.fromBlocks_smul,Matrix.fromBlocks_neg]


-- @@ L133-141 verbatim
theorem offDiagonal_monomial {α : Type} [DecidableEq α]
    {A : Matrix α α ℂ} (hA : MonomialMatrix A) (s : ℂ) (hs : s≠0) :
    MonomialMatrix (Matrix.fromBlocks 0 A (s•A) 0) := by
  obtain ⟨σ,d,hd,ha⟩ := hA
  let e : Equiv.Perm (α⊕α) := (Equiv.sumCongr σ σ).trans (Equiv.sumComm α α)
  refine ⟨e,Sum.elim (fun i => s*d i) d,?_,?_⟩
  · intro j; cases j <;> simp [hd,hs]
  · intro i j; rcases i with i|i <;> rcases j with j|j <;>
      simp [Matrix.fromBlocks,ha,e,mul_ite]


-- @@ L143-149 verbatim
theorem J_monomial (m : ℕ) (b : Bool) : MonomialMatrix (J m b) := by
  induction m generalizing b with
  | zero => exact MonomialMatrix.one
  | succ m ih =>
    cases b
    · simpa [J] using offDiagonal_monomial (ih true) 1 one_ne_zero
    · simpa [J] using offDiagonal_monomial (ih false) (-1) (neg_ne_zero.mpr one_ne_zero)


-- @@ L151-152 verbatim
def Gamma (m : ℕ) : Matrix (Bits (m+1)) (Bits (m+1)) ℂ :=
  Matrix.fromBlocks (D m) 1 1 (-D m)


-- @@ L154-155 verbatim
theorem Gamma_square (m : ℕ) : Gamma m*Gamma m=1 := by
  simp [Gamma,Matrix.fromBlocks_multiply,D_square,← Matrix.fromBlocks_one]

-- @@ L156-157 verbatim
theorem Gamma_unit (m : ℕ) : IsUnit (Gamma m) := by
  rw [isUnit_iff_exists_inv']; exact ⟨Gamma m,Gamma_square m⟩


-- @@ L159-160 verbatim
theorem Gamma_symmetry (m : ℕ) : J (m+1) false*Gamma m=(Gamma m).transpose*J (m+1) false := by
  simp [J,Gamma,Matrix.fromBlocks_multiply,Matrix.fromBlocks_transpose,J_commute m true]


-- @@ L162-167 verbatim
theorem D_star (m : ℕ) : ∀ i j,star (D m i j)=D m i j := by
  induction m with
  | zero => simp [D]
  | succ m ih =>
    intro i j; rcases i with i|i <;> rcases j with j|j <;>
      simp [D,Matrix.one_apply,ih]


-- @@ L169-174 verbatim
theorem J_star (m : ℕ) (b : Bool) : ∀ i j,star (J m b i j)=J m b i j := by
  induction m generalizing b with
  | zero => simp [J]
  | succ m ih =>
    cases b <;> intro i j <;> rcases i with i|i <;> rcases j with j|j <;>
      simp [J,ih]


-- @@ L176-178 verbatim
theorem Gamma_star (m : ℕ) : ∀ i j,star (Gamma m i j)=Gamma m i j := by
  intro i j; rcases i with i|i <;> rcases j with j|j <;>
    simp [Gamma,D_star,Matrix.one_apply]


-- @@ L180-180 verbatim
end ExactFourier.SignedBits


-- @@ L182-182 verbatim
end

-- @@ L183-183 verbatim
end


-- @@ L185-185 verbatim
section

-- @@ L186-186 verbatim
noncomputable section

-- @@ L187-187 verbatim
namespace ExactFourier

-- @@ L188-188 verbatim
open scoped Kronecker

-- @@ L189-189 verbatim
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]


-- @@ L191-191 verbatim
def support (A : Matrix α β ℂ) : Finset (α×β) := Finset.univ.filter (fun ij=>A ij.1 ij.2≠0)

-- @@ L192-192 verbatim
def nnz (A : Matrix α β ℂ) : ℕ := (support A).card


-- @@ L194-195 verbatim
@[simp] theorem mem_support
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (A : Matrix α β ℂ) (ij : α×β) : ij∈support A ↔ A ij.1 ij.2≠0 := by simp [support]

-- @@ L196-197 verbatim
@[simp] theorem nnz_zero
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] : nnz (0 : Matrix α β ℂ)=0 := by simp [nnz,support]


-- @@ L199-200 verbatim
@[simp] theorem nnz_neg
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (A : Matrix α β ℂ) : nnz (-A)=nnz A := by simp [nnz,support]


-- @@ L202-209 verbatim
theorem nnz_add_le (A B : Matrix α β ℂ) : nnz (A+B)≤nnz A+nnz B := by
  apply (Finset.card_le_card (show support (A+B)⊆support A∪support B from ?_)).trans (Finset.card_union_le _ _)
  intro ij hij
  simp only [mem_support,Matrix.add_apply] at hij
  simp only [Finset.mem_union,mem_support]
  by_contra h
  push Not at h
  exact hij (by simp [h.1,h.2])


-- @@ L211-212 verbatim
theorem nnz_sub_le (A B : Matrix α β ℂ) : nnz (A-B)≤nnz A+nnz B := by
  simpa [sub_eq_add_neg] using nnz_add_le A (-B)


-- @@ L214-218 verbatim
@[simp] theorem nnz_one : nnz (1 : Matrix α α ℂ)=Fintype.card α := by
  have he : support (1 : Matrix α α ℂ)=Finset.univ.image (fun i : α => (i,i)) := by
    ext ⟨i,j⟩; simp [support,Matrix.one_apply]
  rw [nnz,he,Finset.card_image_of_injective _ (by intro i j h; exact (Prod.mk.inj h).1)]
  exact Finset.card_univ


-- @@ L220-228 verbatim
theorem nnz_kronecker
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (A : Matrix α α ℂ) (B : Matrix β β ℂ) : nnz (A⊗ₖB)=nnz A*nnz B := by
  classical
  let e : (α×α)×(β×β) ≃ (α×β)×(α×β) := Equiv.prodProdProdComm α α β β
  have he : support (A⊗ₖB)=(support A×ˢsupport B).map e.toEmbedding := by
    ext ⟨⟨i,k⟩,⟨j,l⟩⟩
    simp [support,e,Equiv.prodProdProdComm_apply]
  rw [nnz,he,Finset.card_map,Finset.card_product]
  rfl


-- @@ L230-242 verbatim
theorem nnz_monomial_mul (A B : Matrix α α ℂ) (hA : MonomialMatrix A) : nnz (A*B)=nnz B := by
  classical
  obtain ⟨σ,d,hd,hA⟩ := hA
  have he (i j : α) : (A*B) (σ i) j=d i*B i j := by
    rw [Matrix.mul_apply]
    simp_rw [hA]
    simp
  let e : α×α ≃ α×α := σ.prodCongr (Equiv.refl α)
  have hs : support (A*B)=(support B).map e.toEmbedding := by
    ext ij
    obtain ⟨⟨i,j⟩,rfl⟩ := e.surjective ij
    simp [e,he,hd]
  rw [nnz,hs,Finset.card_map]; rfl


-- @@ L244-244 verbatim
end ExactFourier


-- @@ L246-246 verbatim
end

-- @@ L247-247 verbatim
end


-- @@ L249-249 verbatim
section

-- @@ L250-250 verbatim
noncomputable section

-- @@ L251-251 verbatim
namespace ExactFourier

-- @@ L252-252 verbatim
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]


-- @@ L254-257 verbatim
theorem nnz_sum
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (A : Matrix α β ℂ) : nnz A=∑ i,∑ j,if A i j=0 then 0 else 1 := by
  rw [nnz,Finset.card_eq_sum_ones]
  simp only [support,Finset.sum_filter,Fintype.sum_prod_type,ite_not]


-- @@ L259-263 verbatim
theorem nnz_fromBlocks (A : Matrix α α ℂ) (B : Matrix α β ℂ)
    (C : Matrix β α ℂ) (D : Matrix β β ℂ) :
    nnz (Matrix.fromBlocks A B C D)=nnz A+nnz B+nnz C+nnz D := by
  simp [nnz_sum,Fintype.sum_sum_type,Finset.sum_add_distrib,add_assoc,add_left_comm]
  rfl


-- @@ L265-265 verbatim
namespace SignedBits


-- @@ L267-273 verbatim
theorem D_count (m : ℕ) : 2*nnz (D m)=m*2^m := by
  induction m with
  | zero => simp [D]
  | succ m ih =>
    rw [D,nnz_fromBlocks,nnz_zero,nnz_one,nnz_neg,bits_card]
    rw [pow_succ]
    nlinarith


-- @@ L275-278 verbatim
theorem Gamma_count (m : ℕ) : nnz (Gamma m)=(m+2)*2^m := by
  rw [Gamma,nnz_fromBlocks,nnz_one,nnz_neg,bits_card]
  have hh := D_count m
  nlinarith


-- @@ L280-280 verbatim
end SignedBits

-- @@ L281-281 verbatim
end ExactFourier


-- @@ L283-283 verbatim
end

-- @@ L284-284 verbatim
end


-- @@ L286-286 verbatim
section

-- @@ L287-287 verbatim
namespace ExactFourier.Similarity

-- @@ L288-288 verbatim
variable {α : Type} [Fintype α] [DecidableEq α]


-- @@ L290-290 verbatim
noncomputable def conj (U A : Matrix α α ℂ) : Matrix α α ℂ := U*A*U⁻¹


-- @@ L292-293 verbatim
theorem one (U : Matrix α α ℂ) (hU : IsUnit U) : conj U 1=1 := by
  rw [conj,mul_one,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)]


-- @@ L295-296 verbatim
theorem add (U A B : Matrix α α ℂ) : conj U (A+B)=conj U A+conj U B := by
  simp [conj,mul_add,add_mul]

-- @@ L297-298 verbatim
theorem sub (U A B : Matrix α α ℂ) : conj U (A-B)=conj U A-conj U B := by
  simp [conj,mul_sub,sub_mul]

-- @@ L299-300 verbatim
theorem smul (U A : Matrix α α ℂ) (c : ℂ) : conj U (c•A)=c•conj U A := by
  simp [conj]

-- @@ L301-301 verbatim
theorem zero (U : Matrix α α ℂ) : conj U 0=0 := by simp [conj]


-- @@ L303-307 verbatim
theorem mul (U A B : Matrix α α ℂ) (hU : IsUnit U) :
    conj U A*conj U B=conj U (A*B) := by
  calc
    _ = U*A*(U⁻¹*U)*B*U⁻¹ := by simp only [conj]; noncomm_ring
    _ = _ := by rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)]; simp [conj,mul_assoc]


-- @@ L309-310 verbatim
theorem unit (U A : Matrix α α ℂ) (hU : IsUnit U) (hA : IsUnit A) : IsUnit (conj U A) :=
  (hU.mul hA).mul (Matrix.isUnit_nonsing_inv_iff.mpr hU)


-- @@ L312-316 verbatim
theorem diagonal_linear (U : Matrix α α ℂ) (hU : IsUnit U) (a : α → ℂ) (t : ℂ) :
    1+t•conj U (Matrix.diagonal a)=conj U (Matrix.diagonal (fun i=>1+t*a i)) := by
  have he : Matrix.diagonal (fun i=>1+t*a i)=(1 : Matrix α α ℂ)+t•Matrix.diagonal a := by
    ext i j; by_cases h : i=j <;> simp [Matrix.diagonal,h]
  rw [he,add,smul,one U hU]


-- @@ L318-320 verbatim
theorem diagonal_linear_sub (U : Matrix α α ℂ) (hU : IsUnit U) (a : α → ℂ) (t : ℂ) :
    1-t•conj U (Matrix.diagonal a)=conj U (Matrix.diagonal (fun i=>1-t*a i)) := by
  simpa [sub_eq_add_neg] using diagonal_linear U hU a (-t)


-- @@ L322-322 verbatim
end ExactFourier.Similarity


-- @@ L324-324 verbatim
end


-- @@ L326-326 verbatim
section

-- @@ L327-327 verbatim
noncomputable section

-- @@ L328-328 verbatim
namespace ExactFourier.RealMatrix

-- @@ L329-329 verbatim
variable {α : Type} [Fintype α] [DecidableEq α]


-- @@ L331-331 verbatim
def complex (A : Matrix α α ℝ) : Matrix α α ℂ := A.map Complex.ofReal


-- @@ L333-335 verbatim
theorem map_mul
    {α : Type} [Fintype α] [DecidableEq α] (A B : Matrix α α ℝ) : complex (A*B)=complex A*complex B := by
  exact Matrix.map_mul (f := Complex.ofRealHom)

-- @@ L336-337 verbatim
@[simp] theorem map_one
    {α : Type} [Fintype α] [DecidableEq α] : complex (1 : Matrix α α ℝ)=1 := by ext i j; by_cases h : i=j <;> simp [complex,Matrix.one_apply,h]

-- @@ L338-339 verbatim
@[simp] theorem map_zero
    {α : Type} [Fintype α] [DecidableEq α] : complex (0 : Matrix α α ℝ)=0 := rfl

-- @@ L340-341 verbatim
@[simp] theorem map_transpose
    {α : Type} [Fintype α] [DecidableEq α] (A : Matrix α α ℝ) : complex A.transpose=(complex A).transpose := rfl

-- @@ L342-344 verbatim
@[simp] theorem map_diagonal
    {α : Type} [Fintype α] [DecidableEq α] (d : α → ℝ) : complex (Matrix.diagonal d)=Matrix.diagonal (fun i => (d i : ℂ)) := by
  ext i j; by_cases h : i=j <;> simp [complex,Matrix.diagonal,h]

-- @@ L345-347 verbatim
@[simp] theorem map_add
    {α : Type} [Fintype α] [DecidableEq α] (A B : Matrix α α ℝ) : complex (A+B)=complex A+complex B := by
  ext i j; simp [complex]

-- @@ L348-350 verbatim
@[simp] theorem map_sub
    {α : Type} [Fintype α] [DecidableEq α] (A B : Matrix α α ℝ) : complex (A-B)=complex A-complex B := by
  ext i j; simp [complex]


-- @@ L352-356 verbatim
theorem unit (A : Matrix α α ℝ) (h : IsUnit A) : IsUnit (complex A) := by
  obtain ⟨B,hB⟩ := isUnit_iff_exists_inv'.mp h
  apply isUnit_iff_exists_inv'.mpr
  refine ⟨complex B,?_⟩
  rw [← map_mul,hB,map_one]


-- @@ L358-361 verbatim
theorem inv (A : Matrix α α ℝ) (h : IsUnit A) : complex A⁻¹=(complex A)⁻¹ := by
  apply (unit A h).mul_right_cancel
  rw [← map_mul,Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp h),map_one]
  rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (unit A h))]


-- @@ L363-381 verbatim
theorem diagonalization (A : Matrix α α ℝ) (hA : A.IsSymm) :
    ∃ U : Matrix α α ℝ,∃ a : α → ℝ,IsUnit U ∧ U⁻¹=U.transpose ∧
      A=U*Matrix.diagonal a*U⁻¹ := by
  have ha : A.IsHermitian := by
    change A.conjTranspose=A
    ext i j
    simpa [Matrix.conjTranspose] using congrFun (congrFun hA i) j
  let U : Matrix α α ℝ := ha.eigenvectorUnitary
  have ho : U*U.transpose=1 := by
    simpa only [Unitary.coe_star,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using Unitary.coe_mul_star_self ha.eigenvectorUnitary
  have hU : IsUnit U := isUnit_iff_exists_inv.mpr ⟨U.transpose,ho⟩
  have hi : U⁻¹=U.transpose := by
    apply hU.mul_left_cancel
    rw [Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hU)]
    exact ho.symm
  refine ⟨U,ha.eigenvalues,hU,hi,?_⟩
  rw [hi]
  simpa only [Unitary.conjStarAlgAut_apply,Function.comp_def,RCLike.ofReal_real_eq_id, id_eq,
    Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial] using ha.spectral_theorem


-- @@ L383-392 verbatim
theorem complex_re
    {α : Type} [Fintype α] [DecidableEq α] (A : Matrix α α ℂ) (hA : ∀ i j,star (A i j)=A i j) :
    complex (A.map Complex.re)=A := by
  ext i j
  apply Complex.ext
  · simp [complex]
  · have hh := congrArg Complex.im (hA i j)
    simp only [Complex.star_def,Complex.conj_im] at hh
    simp only [complex,Matrix.map_apply,Complex.ofReal_im]
    linarith


-- @@ L394-397 verbatim
theorem re_symm
    {α : Type} [Fintype α] [DecidableEq α] (A : Matrix α α ℂ) (hA : A.IsSymm) : (A.map Complex.re).IsSymm := by
  ext i j
  exact congrArg Complex.re (congrFun (congrFun hA i) j)


-- @@ L399-399 verbatim
end ExactFourier.RealMatrix


-- @@ L401-401 verbatim
end

-- @@ L402-402 verbatim
end


-- @@ L404-404 verbatim
end OAI
