import OAI.Computability.FourierCircuit.RawWordBound


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
section

-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
namespace ExactFourier.Packing.RawPrice

-- @@ L8-8 verbatim
variable (p : RawPrice) {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]


-- @@ L10-13 verbatim
theorem embedded (e : α ↪ β) (M : Matrix α α ℂ) (hM : IsUnit M) :
 p.value (Embedded.matrix e M)=p.value M := by
 rw [Embedded.matrix,p.reindex _ _ (Matrix.isUnit_fromBlocks_zero₂₁.mpr ⟨hM,isUnit_one⟩),
  p.directSum _ _ hM isUnit_one,p.one,add_zero]


-- @@ L15-32 verbatim
theorem zero_iff (M : Matrix α α ℂ) (hM : IsUnit M) : p.value M=0 ↔ MonomialMatrix M := by
 refine ⟨?_,p.monomial_zero M⟩
 intro hz
 by_contra hn
 have ha : 2≤Fintype.card α := by
  by_contra h
  have : Subsingleton α := Fintype.card_le_one_iff_subsingleton.mp (by omega)
  exact hn (monomial_of_subsingleton M hM)
 let e : Fin 2 ↪ α := (Fin.castLEEmb ha).trans (Fintype.equivFin α).symm.toEmbedding
 let V : Word (fun _:Unit=>α) (fun _=>M) α := callWord () (Function.Embedding.refl _)
 have hv : V.matrix=M := by rw [matrix_callWord,Embedded.matrix_refl]
 obtain ⟨h,hh,W,hW,hw⟩ := word_generates V (hv.symm ▸ hM) (hv.symm ▸ hn)
  (Embedded.matrix e shearU) (Embedded.unit e shearU shearU_unit)
 have hb := p.word_bound (fun _:Unit=>hM) W (Embedded.matrix e shearU) hW
 rw [hw] at hb
 have hweight : V.weight (fun _:Unit=>p.value M)=p.value M := by simp [V,Word.weight]
 rw [hweight,hz,mul_zero,p.embedded e shearU shearU_unit,p.normalized] at hb
 norm_num at hb

-- @@ L33-33 verbatim
end ExactFourier.Packing.RawPrice


-- @@ L35-35 verbatim
end

-- @@ L36-36 verbatim
end


-- @@ L38-38 verbatim
section

-- @@ L39-39 verbatim
noncomputable section

-- @@ L40-40 verbatim
open scoped Kronecker

-- @@ L41-41 verbatim
namespace ExactFourier

-- @@ L42-42 verbatim
namespace MonomialMatrix

-- @@ L43-43 verbatim
variable {α : Type} [Fintype α] [DecidableEq α]

-- @@ L44-54 verbatim
theorem transpose
    {α : Type} [Fintype α] [DecidableEq α] {M : Matrix α α ℂ} (hM : MonomialMatrix M) : MonomialMatrix M.transpose := by
 obtain ⟨s,d,hd,hs⟩ := hM
 refine ⟨s.symm,fun j=>d (s.symm j),fun j=>hd _,?_⟩
 intro i j
 change M j i=_
 rw [hs]
 by_cases h : i=s.symm j
 · subst i; simp
 · have hh : j≠s i := by intro he; exact h (by rw [he,s.symm_apply_apply])
   simp [h,hh]

-- @@ L55-55 verbatim
end MonomialMatrix

-- @@ L56-56 verbatim
namespace MatrixSymmetry

-- @@ L57-57 verbatim
variable {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]

-- @@ L58-60 verbatim
theorem unit_transpose (M : Matrix α α ℂ) (hM : IsUnit M) : IsUnit M.transpose := by
 apply (Matrix.isUnit_iff_isUnit_det _).mpr
 simpa using (Matrix.isUnit_iff_isUnit_det M).mp hM


-- @@ L62-66 verbatim
theorem inverse_tensor (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 (M⊗ₖN)⁻¹=M⁻¹⊗ₖN⁻¹ := by
 apply Matrix.inv_eq_right_inv
 rw [← Matrix.mul_kronecker_mul,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hM),
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hN),Matrix.one_kronecker_one]


-- @@ L68-73 verbatim
theorem inverse_sum (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 (Matrix.fromBlocks M 0 0 N)⁻¹=Matrix.fromBlocks M⁻¹ 0 0 N⁻¹ := by
 apply Matrix.inv_eq_right_inv
 simp only [Matrix.fromBlocks_multiply,Matrix.mul_zero,Matrix.zero_mul,add_zero,zero_add,
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hM),
  Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hN),Matrix.fromBlocks_one]


-- @@ L75-80 verbatim
theorem inverse_reindex (e : α≃β) (M : Matrix α α ℂ) (hM : IsUnit M) :
 (Matrix.reindex e e M)⁻¹=Matrix.reindex e e M⁻¹ := by
 apply Matrix.inv_eq_right_inv
 change (Matrix.reindexAlgEquiv ℂ ℂ e) M*(Matrix.reindexAlgEquiv ℂ ℂ e) M⁻¹=1
 rw [← map_mul,Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hM)]
 exact (Matrix.reindexAlgEquiv ℂ ℂ e).map_one

-- @@ L81-83 verbatim
theorem transpose_tensor
    {α : Type} {β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β] (M : Matrix α α ℂ) (N : Matrix β β ℂ) :
 (M⊗ₖN).transpose=M.transpose⊗ₖN.transpose := rfl


-- @@ L85-85 verbatim
end MatrixSymmetry

-- @@ L86-86 verbatim
end ExactFourier


-- @@ L88-88 verbatim
end

-- @@ L89-89 verbatim
end


-- @@ L91-91 verbatim
section

-- @@ L92-92 verbatim
noncomputable section

-- @@ L93-93 verbatim
open scoped Kronecker

-- @@ L94-94 verbatim
namespace ExactFourier.Packing.RawPrice

-- @@ L95-95 verbatim
open MatrixSymmetry

-- @@ L96-96 verbatim
variable (p : RawPrice) {α β : Type} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]


-- @@ L98-99 verbatim
def symValue (M : Matrix α α ℂ) : ℝ :=
 (p.value M+p.value M⁻¹+p.value M.transpose+p.value M.transpose⁻¹)/4


-- @@ L101-107 verbatim
theorem sym_nonneg (M : Matrix α α ℂ) (hM : IsUnit M) : 0≤p.symValue M := by
 have h1 := p.nonneg M hM
 have h2 := p.nonneg M⁻¹ (Matrix.isUnit_nonsing_inv_iff.mpr hM)
 have h3 := p.nonneg M.transpose (unit_transpose M hM)
 have h4 := p.nonneg M.transpose⁻¹ (Matrix.isUnit_nonsing_inv_iff.mpr (unit_transpose M hM))
 dsimp [symValue]
 positivity


-- @@ L109-122 verbatim
theorem sym_zero (M : Matrix α α ℂ) (hM : IsUnit M) : p.symValue M=0 ↔ MonomialMatrix M := by
 constructor
 · intro hz
   have h1 := p.nonneg M hM
   have h2 := p.nonneg M⁻¹ (Matrix.isUnit_nonsing_inv_iff.mpr hM)
   have h3 := p.nonneg M.transpose (unit_transpose M hM)
   have h4 := p.nonneg M.transpose⁻¹ (Matrix.isUnit_nonsing_inv_iff.mpr (unit_transpose M hM))
   apply (p.zero_iff M hM).mp
   dsimp [symValue] at hz
   linarith
 · intro hm
   simp only [symValue,p.monomial_zero M hm,p.monomial_zero _ hm.inverse,
    p.monomial_zero _ hm.transpose,p.monomial_zero _ hm.transpose.inverse]
   norm_num


-- @@ L124-130 verbatim
theorem sym_reindex (e : α≃β) (M : Matrix α α ℂ) (hM : IsUnit M) :
 p.symValue (Matrix.reindex e e M)=p.symValue M := by
 simp only [symValue,inverse_reindex e M hM,Matrix.transpose_reindex,
  inverse_reindex e M.transpose (unit_transpose M hM)]
 rw [p.reindex e M hM,p.reindex e M⁻¹ (Matrix.isUnit_nonsing_inv_iff.mpr hM),
  p.reindex e M.transpose (unit_transpose M hM),
  p.reindex e M.transpose⁻¹ (Matrix.isUnit_nonsing_inv_iff.mpr (unit_transpose M hM))]


-- @@ L132-145 verbatim
theorem sym_mul (M N : Matrix α α ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 p.symValue (M*N)≤p.symValue M+p.symValue N := by
 have hiM := Matrix.isUnit_nonsing_inv_iff.mpr hM
 have hiN := Matrix.isUnit_nonsing_inv_iff.mpr hN
 have htM := unit_transpose M hM
 have htN := unit_transpose N hN
 have hitM := Matrix.isUnit_nonsing_inv_iff.mpr htM
 have hitN := Matrix.isUnit_nonsing_inv_iff.mpr htN
 have h1 := p.mul_le M N hM hN
 have h2 := p.mul_le N⁻¹ M⁻¹ hiN hiM
 have h3 := p.mul_le N.transpose M.transpose htN htM
 have h4 := p.mul_le M.transpose⁻¹ N.transpose⁻¹ hitM hitN
 simp only [symValue,Matrix.mul_inv_rev,Matrix.transpose_mul]
 linarith


-- @@ L147-164 verbatim
theorem sym_monomial (M L R : Matrix α α ℂ) (hM : IsUnit M)
 (hL : MonomialMatrix L) (hR : MonomialMatrix R) : p.symValue (L*M*R)=p.symValue M := by
 have hm := (hL.unit _).mul hM |>.mul (hR.unit _)
 have one_side : ∀ (M L R : Matrix α α ℂ),IsUnit M→MonomialMatrix L→MonomialMatrix R→
  p.symValue (L*M*R)≤p.symValue M := by
  intro M L R hM hL hR
  have h1 := p.sym_mul L M (hL.unit _) hM
  have h2 := p.sym_mul (L*M) R ((hL.unit _).mul hM) (hR.unit _)
  rw [(p.sym_zero L (hL.unit _)).mpr hL] at h1
  rw [(p.sym_zero R (hR.unit _)).mpr hR] at h2
  linarith
 apply le_antisymm (one_side M L R hM hL hR)
 have hh := one_side (L*M*R) L⁻¹ R⁻¹ hm hL.inverse hR.inverse
 have he : L⁻¹*(L*M*R)*R⁻¹=M := by
  simp only [← mul_assoc,Matrix.nonsing_inv_mul L ((Matrix.isUnit_iff_isUnit_det L).mp (hL.unit _)),one_mul]
  rw [mul_assoc,Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).mp (hR.unit _)),mul_one]
 rw [he] at hh
 exact hh


-- @@ L166-177 verbatim
theorem sym_tensor (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 p.symValue (M⊗ₖN)=(Fintype.card β : ℝ)*p.symValue M+(Fintype.card α : ℝ)*p.symValue N := by
 have hiM := Matrix.isUnit_nonsing_inv_iff.mpr hM
 have hiN := Matrix.isUnit_nonsing_inv_iff.mpr hN
 have htM := unit_transpose M hM
 have htN := unit_transpose N hN
 have hitM := Matrix.isUnit_nonsing_inv_iff.mpr htM
 have hitN := Matrix.isUnit_nonsing_inv_iff.mpr htN
 simp only [symValue,inverse_tensor M N hM hN,transpose_tensor,inverse_tensor _ _ htM htN]
 rw [p.tensor M N hM hN,p.tensor M⁻¹ N⁻¹ hiM hiN,p.tensor M.transpose N.transpose htM htN,
  p.tensor M.transpose⁻¹ N.transpose⁻¹ hitM hitN]
 ring


-- @@ L179-191 verbatim
theorem sym_sum (M : Matrix α α ℂ) (N : Matrix β β ℂ) (hM : IsUnit M) (hN : IsUnit N) :
 p.symValue (Matrix.fromBlocks M 0 0 N)=p.symValue M+p.symValue N := by
 have hiM := Matrix.isUnit_nonsing_inv_iff.mpr hM
 have hiN := Matrix.isUnit_nonsing_inv_iff.mpr hN
 have htM := unit_transpose M hM
 have htN := unit_transpose N hN
 have hitM := Matrix.isUnit_nonsing_inv_iff.mpr htM
 have hitN := Matrix.isUnit_nonsing_inv_iff.mpr htN
 simp only [symValue,inverse_sum M N hM hN,Matrix.fromBlocks_transpose,Matrix.transpose_zero,
  inverse_sum _ _ htM htN]
 rw [p.directSum M N hM hN,p.directSum M⁻¹ N⁻¹ hiM hiN,p.directSum M.transpose N.transpose htM htN,
  p.directSum M.transpose⁻¹ N.transpose⁻¹ hitM hitN]
 ring


-- @@ L193-198 verbatim
theorem sym_inverse (M : Matrix α α ℂ) (hM : IsUnit M) : p.symValue M⁻¹=p.symValue M := by
 have hdet := (Matrix.isUnit_iff_isUnit_det M).mp hM
 have htdet := (Matrix.isUnit_iff_isUnit_det M.transpose).mp (unit_transpose M hM)
 simp only [symValue,Matrix.nonsing_inv_nonsing_inv M hdet,Matrix.transpose_nonsing_inv,
  Matrix.nonsing_inv_nonsing_inv M.transpose htdet]
 ring


-- @@ L200-202 verbatim
theorem sym_transpose (M : Matrix α α ℂ) : p.symValue M.transpose=p.symValue M := by
 simp only [symValue,Matrix.transpose_transpose]
 ring

-- @@ L203-203 verbatim
end ExactFourier.Packing.RawPrice


-- @@ L205-205 verbatim
end

-- @@ L206-206 verbatim
end


-- @@ L208-208 verbatim
section

-- @@ L209-209 verbatim
noncomputable section

-- @@ L210-210 verbatim
namespace ExactFourier.Packing.RawPrice

-- @@ L211-211 verbatim
variable (p : RawPrice)


-- @@ L213-223 verbatim
theorem shear_inverse : p.value shearU⁻¹=1 := by
 let d : Fin 2→ℂ := ![1,-1]
 let L := Matrix.diagonal d
 have hL : MonomialMatrix L := MonomialMatrix.diagonal d (by intro i; fin_cases i <;> norm_num [d])
 have he : shearU⁻¹=L*shearU*L := by
  apply Matrix.inv_eq_right_inv
  ext i j
  fin_cases i <;> fin_cases j <;>
   norm_num [L,d,shearU,Matrix.mul_apply,Fin.sum_univ_two,Matrix.transvection,
    Matrix.diagonal,Matrix.single,Matrix.one_apply]
 rw [he,p.monomial _ L L shearU_unit hL hL,p.normalized]


-- @@ L225-229 verbatim
theorem shear_transpose : p.value shearU.transpose=1 := by
 have he : Matrix.reindex (Fin.revPerm (n := 2)) (Fin.revPerm (n := 2)) shearU=shearU.transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.reindex_apply,shearU,Matrix.transvection,Fin.revPerm,Fin.rev,Matrix.single]
 rw [← he,p.reindex _ _ shearU_unit,p.normalized]


-- @@ L231-236 verbatim
theorem shear_transpose_inverse : p.value shearU.transpose⁻¹=1 := by
 have he : Matrix.reindex (Fin.revPerm (n := 2)) (Fin.revPerm (n := 2)) shearU=shearU.transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Matrix.reindex_apply,shearU,Matrix.transvection,Fin.revPerm,Fin.rev,Matrix.single]
 rw [← he,MatrixSymmetry.inverse_reindex _ _ shearU_unit,
  p.reindex _ _ (Matrix.isUnit_nonsing_inv_iff.mpr shearU_unit),p.shear_inverse]


-- @@ L238-240 verbatim
theorem sym_normalized : p.symValue shearU=1 := by
 rw [symValue,p.normalized,p.shear_inverse,p.shear_transpose,p.shear_transpose_inverse]
 norm_num


-- @@ L242-253 verbatim
def toMatrixPrice : MatrixPrice where
 value := p.symValue
 nonneg := p.sym_nonneg
 zero_iff := p.sym_zero
 reindex := p.sym_reindex
 monomial := p.sym_monomial
 mul_le := p.sym_mul
 tensor := p.sym_tensor
 directSum := p.sym_sum
 inverse := p.sym_inverse
 transpose := fun M _=>p.sym_transpose M
 normalized := p.sym_normalized

-- @@ L254-254 verbatim
end ExactFourier.Packing.RawPrice


-- @@ L256-256 verbatim
end

-- @@ L257-257 verbatim
end


-- @@ L259-259 verbatim
section

-- @@ L260-260 verbatim
namespace ExactFourier.BasisExchange

-- @@ L261-261 verbatim
variable {ι : Type} [Fintype ι] [DecidableEq ι]


-- @@ L263-264 verbatim
def rows (K : Matrix ι ι ℂ) (H : Finset ι) : Matrix ι ι ℂ :=
  fun i j => if i∈H then K i j else (1 : Matrix ι ι ℂ) i j


-- @@ L266-273 verbatim
theorem rows_insert (K : Matrix ι ι ℂ) (H : Finset ι) (j : ι) (hj : j∉H) :
    (rows K H).updateRow j (rows K Hᶜ j)=rows K (insert j H) ∧
    (rows K Hᶜ).updateRow j (rows K H j)=rows K (insert j H)ᶜ := by
  constructor <;> ext a b
  all_goals
    by_cases ha : a=j
    · subst a; simp [rows,Matrix.updateRow_apply,hj]
    · simp [rows,Matrix.updateRow_apply,ha]


-- @@ L275-287 verbatim
theorem price_many (p : MatrixPrice) (K : Matrix ι ι ℂ)
    (hU : ∀ H : Finset ι,IsUnit (rows K H)) (H : Finset ι) :
    p.value (rows K Hᶜ*(rows K H)⁻¹)=p.value K := by
  induction H using Finset.induction_on with
  | empty =>
    have he : rows K ∅=1 := by ext i j; simp [rows]
    have hu : rows K Finset.univ=K := by ext i j; simp [rows]
    simp only [Finset.compl_empty,he,hu,inv_one,mul_one]
  | @insert j H hj ih =>
    have he := BasisExchange.price p (rows K H) (rows K Hᶜ) j (hU H) (hU Hᶜ)
      (by rw [(rows_insert K H j hj).1]; exact hU _) (by rw [(rows_insert K H j hj).2]; exact hU _)
    rw [(rows_insert K H j hj).1,(rows_insert K H j hj).2] at he
    exact he.trans ih


-- @@ L289-289 verbatim
variable [LinearOrder ι]


-- @@ L291-301 verbatim
theorem rows_unit (K : Matrix ι ι ℂ) (hl : K.IsLowerTriangular)
    (hd : ∀ i,K i i=1) (H : Finset ι) : IsUnit (rows K H) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  have hl' : (rows K H).IsLowerTriangular := by
    intro i j hij
    by_cases hi : i∈H
    · simp [rows,hi,hl hij]
    · have hij' : i<j := hij
      simp [rows,hi,ne_of_lt hij']
  rw [Matrix.det_of_isLowerTriangular _ hl']
  simp [rows,hd]


-- @@ L303-306 verbatim
theorem price_triangular (p : MatrixPrice) (K : Matrix ι ι ℂ) (hl : K.IsLowerTriangular)
    (hd : ∀ i,K i i=1) (H : Finset ι) :
    p.value (rows K Hᶜ*(rows K H)⁻¹)=p.value K :=
  price_many p K (rows_unit K hl hd) H


-- @@ L308-308 verbatim
end ExactFourier.BasisExchange


-- @@ L310-310 verbatim
end


-- @@ L312-312 verbatim
section

-- @@ L313-313 verbatim
noncomputable section

-- @@ L314-314 verbatim
namespace ExactFourier.SignedBits

-- @@ L315-315 verbatim
open scoped Matrix Kronecker


-- @@ L317-319 verbatim
abbrev Bits : ℕ → Type
  | 0 => PUnit
  | m+1 => Bits m ⊕ Bits m

-- @@ L320-322 verbatim
@[reducible] instance bitsFintype : (m : ℕ) → Fintype (Bits m)
  | 0 => inferInstanceAs (Fintype PUnit)
  | m+1 => letI := bitsFintype m; inferInstanceAs (Fintype (Bits m ⊕ Bits m))

-- @@ L323-325 verbatim
@[reducible] instance bitsDecidableEq : (m : ℕ) → DecidableEq (Bits m)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | m+1 => letI := bitsDecidableEq m; inferInstanceAs (DecidableEq (Bits m ⊕ Bits m))

-- @@ L326-328 verbatim
@[reducible] instance bitsLinearOrder : (m : ℕ) → LinearOrder (Bits m)
  | 0 => inferInstanceAs (LinearOrder PUnit)
  | m+1 => @Sum.Lex.linearOrder (Bits m) (Bits m) (bitsLinearOrder m) (bitsLinearOrder m)


-- @@ L330-331 verbatim
@[reducible] instance (priority := 2000) bitsLT (m : ℕ) : LT (Bits m) :=
  (bitsLinearOrder m).toLT


-- @@ L333-336 verbatim
@[simp] theorem bits_card (m : ℕ) : Fintype.card (Bits m)=2^m := by
  induction m with
  | zero => simp [Bits]
  | succ m ih => simpa [Bits,pow_succ,mul_two] using congrArg (fun n => n+n) ih


-- @@ L338-340 verbatim
def D : (m : ℕ) → Matrix (Bits m) (Bits m) ℂ
  | 0 => 0
  | m+1 => Matrix.fromBlocks (D m) 0 1 (-D m)

-- @@ L341-341 verbatim
def T (m : ℕ) : Matrix (Bits m) (Bits m) ℂ := 1+D m


-- @@ L343-346 verbatim
theorem D_square (m : ℕ) : D m*D m=0 := by
  induction m with
  | zero => simp [D]
  | succ m ih => simp [D,Matrix.fromBlocks_multiply,ih]


-- @@ L348-350 verbatim
theorem T_inv_mul (m : ℕ) : (1-D m)*T m=1 := by
  rw [T,mul_add,sub_mul,sub_mul,one_mul,one_mul,mul_one,D_square]
  abel


-- @@ L352-355 verbatim
theorem T_unit (m : ℕ) : IsUnit (T m) :=
  by
    rw [isUnit_iff_exists_inv']
    exact ⟨1-D m,T_inv_mul m⟩


-- @@ L357-357 verbatim
theorem T_inv (m : ℕ) : (T m)⁻¹=1-D m := Matrix.inv_eq_left_inv (T_inv_mul m)


-- @@ L359-372 verbatim
theorem D_lower (m : ℕ) : (D m).IsLowerTriangular := by
  induction m with
  | zero => intro i j hij; rfl
  | succ m ih =>
    intro i j hij
    change (toLex i : Bits m ⊕ₗ Bits m) < toLex j at hij
    rcases i with i|i <;> rcases j with j|j
    · have hh : i<j := Sum.Lex.inl_lt_inl_iff.mp hij
      exact ih hh
    · rfl
    · exact False.elim (Sum.Lex.not_inr_lt_inl hij)
    · change -(D m i j)=0
      have hh : i<j := Sum.Lex.inr_lt_inr_iff.mp hij
      rw [ih hh,neg_zero]


-- @@ L374-377 verbatim
theorem D_diag (m : ℕ) : ∀ i,D m i i=0 := by
  induction m with
  | zero => intro i; rfl
  | succ m ih => intro i; rcases i with i|i <;> simp [D,ih]


-- @@ L379-382 verbatim
theorem T_lower (m : ℕ) : (T m).IsLowerTriangular := by
  intro i j hij
  have h : i<j := hij
  simp [T,ne_of_lt h,D_lower m hij]


-- @@ L384-384 verbatim
theorem T_diag (m : ℕ) : ∀ i,T m i i=1 := by simp [T,D_diag]


-- @@ L386-389 verbatim
theorem T_succ (m : ℕ) : T (m+1)=Matrix.fromBlocks (T m) 0 1 (T m)⁻¹ := by
  rw [T_inv]
  ext i j; rcases i with i|i <;> rcases j with j|j <;>
    simp [T,D,Matrix.one_apply,Matrix.fromBlocks,sub_eq_add_neg]


-- @@ L391-391 verbatim
end ExactFourier.SignedBits


-- @@ L393-393 verbatim
end

-- @@ L394-394 verbatim
end


-- @@ L396-396 verbatim
end OAI
