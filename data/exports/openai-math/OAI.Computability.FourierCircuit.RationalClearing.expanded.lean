import OAI.Computability.FourierCircuit.DiagonalBlocks


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
section

-- @@ L6-8 verbatim
/-! Entrywise regular rational matrices and a common scalar denominator.
Regularity is absence of a pole: the reduced polynomial denominator is nonzero
at the point. Evaluation is only claimed on this domain. -/

-- @@ L9-9 verbatim
namespace ExactFourier.RationalMatrix

-- @@ L10-10 verbatim
open Polynomial

-- @@ L11-11 verbatim
open scoped BigOperators

-- @@ L12-12 verbatim
variable {α : Type} [Fintype α] [DecidableEq α]


-- @@ L14-15 verbatim
noncomputable def eval (X : Matrix α α (RatFunc ℂ)) (s : ℂ) : Matrix α α ℂ :=
  X.map (RatFunc.eval (RingHom.id ℂ) s)


-- @@ L17-18 verbatim
def RegularAt (X : Matrix α α (RatFunc ℂ)) (s : ℂ) : Prop :=
  ∀ i j, (X i j).denom.eval s≠0


-- @@ L20-21 verbatim
noncomputable def denominator (X : Matrix α α (RatFunc ℂ)) : Polynomial ℂ :=
  ∏ v : α×α, (X v.1 v.2).denom


-- @@ L23-24 verbatim
noncomputable def numerator (X : Matrix α α (RatFunc ℂ)) : Matrix α α (Polynomial ℂ) :=
  fun i j => (X i j).num * ∏ v ∈ (Finset.univ : Finset (α×α)).erase (i,j), (X v.1 v.2).denom


-- @@ L26-29 verbatim
theorem denominator_factor (X : Matrix α α (RatFunc ℂ)) (i j : α) :
    denominator X=(X i j).denom *
      ∏ v ∈ (Finset.univ : Finset (α×α)).erase (i,j),(X v.1 v.2).denom :=
  (Finset.mul_prod_erase _ _ (Finset.mem_univ (i,j))).symm


-- @@ L31-35 verbatim
theorem denominator_eval_ne_zero
    {α : Type} [Fintype α] [DecidableEq α] (X : Matrix α α (RatFunc ℂ)) (s : ℂ)
    (hX : RegularAt X s) : (denominator X).eval s≠0 := by
  rw [denominator,Polynomial.eval_prod]
  exact Finset.prod_ne_zero_iff.mpr (fun v _ => hX v.1 v.2)


-- @@ L37-41 verbatim
theorem regular_of_denominator (X : Matrix α α (RatFunc ℂ)) (s : ℂ)
    (hX : (denominator X).eval s≠0) : RegularAt X s := by
  intro i j
  rw [denominator_factor X i j,Polynomial.eval_mul] at hX
  exact (mul_ne_zero_iff.mp hX).1


-- @@ L43-50 verbatim
theorem eval_clearing (X : Matrix α α (RatFunc ℂ)) (s : ℂ)
    (hX : RegularAt X s) :
    (numerator X).map (Polynomial.eval s)=(denominator X).eval s • eval X s := by
  ext i j
  simp only [numerator,Matrix.map_apply,Polynomial.eval_mul,Matrix.smul_apply,smul_eq_mul,
    eval,RatFunc.eval,Polynomial.eval₂_id]
  rw [denominator_factor X i j,Polynomial.eval_mul]
  field_simp [hX i j]


-- @@ L52-52 verbatim
end ExactFourier.RationalMatrix


-- @@ L54-54 verbatim
end


-- @@ L56-56 verbatim
section

-- @@ L57-57 verbatim
namespace ExactFourier.MatrixPrice

-- @@ L58-58 verbatim
open Polynomial

-- @@ L59-59 verbatim
variable {α : Type} [Fintype α] [DecidableEq α]


-- @@ L61-78 verbatim
theorem specialize_polynomial (p : MatrixPrice) (G : Matrix α α (Polynomial ℂ)) (z0 : ℂ)
    (hG0 : IsUnit (G.map (eval z0))) (E : Finset ℂ) (C0 : ℝ)
    (hG : ∀ s : ℂ,s∉E → IsUnit (G.map (eval s)) ∧ p.value (G.map (eval s))≤C0) :
    p.value (G.map (eval z0))≤C0 := by
  classical
  let T := G.map (taylor z0)
  have he (s : ℂ) : T.map (eval s)=G.map (eval (s+z0)) := by
    ext i j; simp [T,taylor_eval]
  have ht0 : T.map (eval 0)=G.map (eval z0) := by simpa using he 0
  rw [← ht0]
  apply p.specialize_polynomial_zero T (by rw [ht0]; exact hG0)
    (E.image (fun s => s-z0)) C0
  intro s hs
  rw [he]
  apply hG
  intro hh
  apply hs
  exact Finset.mem_image.mpr ⟨s+z0,hh,by ring⟩


-- @@ L80-111 verbatim
/-- Literal algebraic specialization (06-feedback:383--393), including a finite
exceptional set which may contain the specialization point itself. -/
theorem specialization (p : MatrixPrice) (X : Matrix α α (RatFunc ℂ)) (z0 : ℂ)
    (hreg : RationalMatrix.RegularAt X z0) (hX0 : IsUnit (RationalMatrix.eval X z0))
    (E : Finset ℂ) (C0 : ℝ)
    (hX : ∀ s : ℂ,s∉E → RationalMatrix.RegularAt X s ∧
      IsUnit (RationalMatrix.eval X s) ∧ p.value (RationalMatrix.eval X s)≤C0) :
    p.value (RationalMatrix.eval X z0)≤C0 := by
  classical
  let q := RationalMatrix.denominator X
  let G := RationalMatrix.numerator X
  have hq0 : q.eval z0≠0 := RationalMatrix.denominator_eval_ne_zero X z0 hreg
  have hq : q≠0 := by intro he; simp [he] at hq0
  have he0 : G.map (eval z0)=q.eval z0 • RationalMatrix.eval X z0 :=
    RationalMatrix.eval_clearing X z0 hreg
  have hGu : IsUnit (G.map (eval z0)) := by rw [he0]; exact scalar_unit _ hX0 _ hq0
  have hGp : p.value (G.map (eval z0))=p.value (RationalMatrix.eval X z0) := by
    rw [he0,p.scalar _ hX0 _ hq0]
  rw [← hGp]
  apply p.specialize_polynomial G z0 hGu (E∪q.roots.toFinset) C0
  intro s hs
  have hsE : s∉E := fun h => hs (Finset.mem_union_left _ h)
  have hqs : q.eval s≠0 := by
    intro hh
    apply hs
    apply Finset.mem_union_right
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hq).mpr hh)
  obtain ⟨hr,hu,hp⟩ := hX s hsE
  have he : G.map (eval s)=q.eval s • RationalMatrix.eval X s :=
    RationalMatrix.eval_clearing X s hr
  rw [he]
  exact ⟨scalar_unit _ hu _ hqs,by rw [p.scalar _ hu _ hqs]; exact hp⟩


-- @@ L113-113 verbatim
end ExactFourier.MatrixPrice


-- @@ L115-115 verbatim
end


-- @@ L117-117 verbatim
section

-- @@ L118-118 verbatim
noncomputable section

-- @@ L119-119 verbatim
namespace ExactFourier.MatrixPrice

-- @@ L120-120 verbatim
open Polynomial

-- @@ L121-121 verbatim
variable {α : Type} [Fintype α] [DecidableEq α]


-- @@ L123-182 verbatim
theorem cayley_tangent (p : MatrixPrice) (Q : Matrix α α (Polynomial ℂ))
    (E : Finset ℂ) (C0 : ℝ)
    (hQ : ∀ s : ℂ,s∉E → IsUnit (1+s•Q.map (eval s)) ∧ p.value (1+s•Q.map (eval s))≤C0)
    (t : ℂ) (hp : IsUnit (1+t•Q.map (eval 0))) (hm : IsUnit (1-t•Q.map (eval 0))) :
    p.value (cayley (Q.map (eval 0)) t)≤C0+2*Fintype.card α := by
  classical
  let P : Matrix α α (Polynomial ℂ) := 1+Polynomial.C t•Q
  let M : Matrix α α (Polynomial ℂ) := 1-Polynomial.C t•Q
  have hP (s : ℂ) : P.map (eval s)=1+t•Q.map (eval s) := by
    change P.map (evalRingHom s)=_
    dsimp only [P]
    rw [Matrix.map_add _ (map_add (evalRingHom s)),CellPoly.map_smul]
    simp
  have hM (s : ℂ) : M.map (eval s)=1-t•Q.map (eval s) := by
    change M.map (evalRingHom s)=_
    dsimp only [M]
    rw [Matrix.map_sub _ (map_sub (evalRingHom s)),CellPoly.map_smul]
    simp
  have hp0 : IsUnit (P.map (eval 0)) := by rw [hP]; exact hp
  have hm0 : IsUnit (M.map (eval 0)) := by rw [hM]; exact hm
  have hpd := det_ne_zero_of_eval_unit P 0 hp0
  have hmd := det_ne_zero_of_eval_unit M 0 hm0
  let G : Matrix α α (Polynomial ℂ) := P*M.adjugate
  have he (s : ℂ) (hmu : IsUnit (1-t•Q.map (eval s))) :
      G.map (eval s)=(1-t•Q.map (eval s)).det•cayley (Q.map (eval s)) t := by
    change G.map (evalRingHom s)=_
    dsimp only [G]
    rw [Matrix.map_mul]
    have hh := RingHom.map_adjugate (evalRingHom s) M
    change (M.adjugate).map (evalRingHom s)=(M.map (evalRingHom s)).adjugate at hh
    rw [hh]
    change P.map (eval s)*(M.map (eval s)).adjugate=_
    rw [hP,hM,CellPoly.adjugate_eq_det_smul_inv _ hmu,Matrix.mul_smul]
    rfl
  have hc0 := cayley_unit (Q.map (eval 0)) t hp hm
  have hd0 : (1-t•Q.map (eval 0)).det≠0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hm)
  have hg0 : IsUnit (G.map (eval 0)) := by rw [he 0 hm]; exact scalar_unit _ hc0 _ hd0
  have hprice0 : p.value (G.map (eval 0))=p.value (cayley (Q.map (eval 0)) t) := by
    rw [he 0 hm,p.scalar _ hc0 _ hd0]
  rw [← hprice0]
  apply p.specialize_polynomial_zero G hg0 (E∪P.det.roots.toFinset∪M.det.roots.toFinset∪{0,t,-t})
    (C0+2*Fintype.card α)
  intro s hs
  have hse : s∉E := by intro h; apply hs; simp [h]
  have hsp : s∉P.det.roots.toFinset := by intro h; apply hs; simp [h]
  have hsm : s∉M.det.roots.toFinset := by intro h; apply hs; simp [h]
  have hs0 : s≠0 := by intro h; apply hs; simp [h]
  have hst : s-t≠0 := by intro h; apply hs; simp [sub_eq_zero.mp h]
  have hst' : s+t≠0 := by intro h; apply hs; simp [eq_neg_of_add_eq_zero_left h]
  have hpu : IsUnit (1+t•Q.map (eval s)) := by
    rw [← hP]; exact unit_eval_of_not_mem_roots P hpd s hsp
  have hmu : IsUnit (1-t•Q.map (eval s)) := by
    rw [← hM]; exact unit_eval_of_not_mem_roots M hmd s hsm
  have hcu := cayley_unit (Q.map (eval s)) t hpu hmu
  have hd : (1-t•Q.map (eval s)).det≠0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hmu)
  obtain ⟨hku,hkp⟩ := hQ s hse
  rw [he s hmu]
  refine ⟨scalar_unit _ hcu _ hd,?_⟩
  rw [p.scalar _ hcu _ hd]
  exact (p.cayley_feedback (Q.map (eval s)) s t hs0 hst' hst hku hpu hmu).trans (add_le_add hkp le_rfl)


-- @@ L184-184 verbatim
end ExactFourier.MatrixPrice


-- @@ L186-186 verbatim
end

-- @@ L187-187 verbatim
end


-- @@ L189-189 verbatim
section

-- @@ L190-190 verbatim
noncomputable section

-- @@ L191-191 verbatim
namespace ExactFourier.CayleyLimit

-- @@ L192-192 verbatim
open Polynomial

-- @@ L193-193 verbatim
variable {α : Type} [Fintype α] [DecidableEq α]


-- @@ L195-195 verbatim
def active (a : α → ℂ) : Finset α := Finset.univ.filter (fun i=>a i≠0)

-- @@ L196-196 verbatim
def denominator (a : α → ℂ) : Polynomial ℂ := ∏ i∈active a,(X-Polynomial.C (a i))

-- @@ L197-197 verbatim
def except (a : α → ℂ) (i : α) : Polynomial ℂ := ∏ j∈(active a).erase i,(X-Polynomial.C (a j))

-- @@ L198-199 verbatim
def numerator (a : α → ℂ) (i : α) : Polynomial ℂ :=
  if a i=0 then denominator a else (X+Polynomial.C (a i))*except a i

-- @@ L200-200 verbatim
def sign (a : α → ℂ) (i : α) : ℂ := if a i=0 then 1 else -1


-- @@ L202-204 verbatim
theorem denominator_factor (a : α → ℂ) (i : α) (hi : a i≠0) :
    denominator a=(X-Polynomial.C (a i))*except a i := by
  exact (Finset.mul_prod_erase _ _ (by simp [active,hi])).symm


-- @@ L206-212 verbatim
theorem denominator_zero
    {α : Type} [Fintype α] [DecidableEq α] (a : α → ℂ) : (denominator a).eval 0≠0 := by
  rw [denominator,Polynomial.eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  have h : a i≠0 := (Finset.mem_filter.mp hi).2
  simpa using neg_ne_zero.mpr h


-- @@ L214-219 verbatim
theorem numerator_zero (a : α → ℂ) (i : α) :
    (numerator a i).eval 0=(denominator a).eval 0*sign a i := by
  by_cases hi : a i=0
  · simp [numerator,sign,hi]
  · rw [numerator,ite_eq_right hi,denominator_factor a i hi]
    simp [sign,hi]


-- @@ L221-227 verbatim
theorem numerator_identity (a : α → ℂ) (i : α) (s : ℂ) (hs : s≠0) :
    (numerator a i).eval s*(1-s⁻¹*a i)=(denominator a).eval s*(1+s⁻¹*a i) := by
  by_cases hi : a i=0
  · simp [numerator,hi]
  · rw [numerator,ite_eq_right hi,denominator_factor a i hi]
    simp only [eval_mul,eval_add,eval_sub,eval_X,eval_C]
    field_simp



-- @@ L230-231 verbatim
def polynomial (U : Matrix α α ℂ) (a : α → ℂ) : Matrix α α (Polynomial ℂ) :=
  U.map Polynomial.C*Matrix.diagonal (numerator a)*(U⁻¹).map Polynomial.C


-- @@ L233-239 verbatim
theorem eval_polynomial (U : Matrix α α ℂ) (a : α → ℂ) (s : ℂ) :
    (polynomial U a).map (evalRingHom s)=Similarity.conj U (Matrix.diagonal (fun i=>(numerator a i).eval s)) := by
  have hc (V : Matrix α α ℂ) : (V.map Polynomial.C).map (evalRingHom s)=V := by ext i j; simp
  rw [polynomial,Matrix.map_mul,Matrix.map_mul,hc,hc]
  have hd : (Matrix.diagonal (numerator a)).map (evalRingHom s)=Matrix.diagonal (fun i=>(numerator a i).eval s) := by
    ext i j; by_cases h : i=j <;> simp [Matrix.diagonal,h]
  rw [hd]; rfl


-- @@ L241-247 verbatim
theorem eval_zero (U : Matrix α α ℂ) (a : α → ℂ) :
    (polynomial U a).map (evalRingHom 0)=(denominator a).eval 0•Similarity.conj U (Matrix.diagonal (sign a)) := by
  rw [eval_polynomial]
  simp_rw [numerator_zero]
  rw [← Similarity.smul]
  congr 1
  ext i j; by_cases h : i=j <;> simp [Matrix.diagonal,h]


-- @@ L249-263 verbatim
theorem eval_as_cayley (U : Matrix α α ℂ) (hU : IsUnit U) (a : α → ℂ)
    (s : ℂ) (hs : s≠0)
    (hm : IsUnit (1-s⁻¹•Similarity.conj U (Matrix.diagonal a))) :
    (polynomial U a).map (evalRingHom s)=(denominator a).eval s•
      MatrixPrice.cayley (Similarity.conj U (Matrix.diagonal a)) s⁻¹ := by
  apply hm.mul_right_cancel
  rw [eval_polynomial,Similarity.diagonal_linear_sub U hU,Similarity.mul U _ _ hU]
  rw [MatrixPrice.cayley,Matrix.smul_mul,← Similarity.diagonal_linear_sub U hU,Matrix.nonsing_inv_mul_cancel_right _ _ ((Matrix.isUnit_iff_isUnit_det _).mp hm),
    Similarity.diagonal_linear U hU,← Similarity.smul]
  congr 1
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i=j
  · subst j; simpa using numerator_identity a i s hs
  · simp [Matrix.diagonal,h]


-- @@ L265-265 verbatim
def bad (a : α → ℂ) : Finset ℂ := insert 0 (Finset.univ.image a∪Finset.univ.image (fun i=>-a i))


-- @@ L267-290 verbatim
theorem generic_units (U : Matrix α α ℂ) (hU : IsUnit U) (a : α → ℂ)
    (s : ℂ) (hs : s∉bad a) : s≠0 ∧ (denominator a).eval s≠0 ∧
    IsUnit (1+s⁻¹•Similarity.conj U (Matrix.diagonal a)) ∧
    IsUnit (1-s⁻¹•Similarity.conj U (Matrix.diagonal a)) := by
  classical
  have hs0 : s≠0 := by intro h; exact hs (by simp [bad,h])
  have hspos (i : α) : s≠a i := by intro h; exact hs (by simp [bad,h])
  have hsneg (i : α) : s≠-a i := by intro h; exact hs (by simp [bad,h])
  have hq : (denominator a).eval s≠0 := by
    rw [denominator,Polynomial.eval_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => by simpa using sub_ne_zero.mpr (hspos i))
  have hp (i : α) : 1+s⁻¹*a i≠0 := by
    intro hh
    have he : s+a i=0 := by field_simp [hs0] at hh; simpa using hh
    exact hsneg i (eq_neg_of_add_eq_zero_left he)
  have hm (i : α) : 1-s⁻¹*a i≠0 := by
    intro hh
    have he : s-a i=0 := by field_simp [hs0] at hh; simpa using hh
    exact hspos i (sub_eq_zero.mp he)
  refine ⟨hs0,hq,?_,?_⟩
  · rw [Similarity.diagonal_linear U hU]
    exact Similarity.unit _ _ hU (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr (fun i=>isUnit_iff_ne_zero.mpr (hp i))))
  · rw [Similarity.diagonal_linear_sub U hU]
    exact Similarity.unit _ _ hU (Matrix.isUnit_diagonal.mpr (Pi.isUnit_iff.mpr (fun i=>isUnit_iff_ne_zero.mpr (hm i))))


-- @@ L292-317 verbatim
/-- The second specialization; no priced use of the diagonalizing basis is made. -/
theorem price (p : MatrixPrice) (U : Matrix α α ℂ) (hU : IsUnit U) (a : α → ℂ)
    (C0 : ℝ)
    (hp : ∀ t : ℂ,IsUnit (1+t•Similarity.conj U (Matrix.diagonal a)) →
      IsUnit (1-t•Similarity.conj U (Matrix.diagonal a)) →
      p.value (MatrixPrice.cayley (Similarity.conj U (Matrix.diagonal a)) t)≤C0) :
    p.value (Similarity.conj U (Matrix.diagonal (sign a)))≤C0 := by
  have hR : IsUnit (Similarity.conj U (Matrix.diagonal (sign a))) := by
    apply Similarity.unit _ _ hU
    apply Matrix.isUnit_diagonal.mpr
    apply Pi.isUnit_iff.mpr
    intro i
    simp only [sign]
    split_ifs <;> simp
  have hG0 : IsUnit ((polynomial U a).map (evalRingHom 0)) := by
    rw [eval_zero]; exact MatrixPrice.scalar_unit _ hR _ (denominator_zero a)
  have he0 : p.value ((polynomial U a).map (evalRingHom 0))=p.value (Similarity.conj U (Matrix.diagonal (sign a))) := by
    rw [eval_zero,p.scalar _ hR _ (denominator_zero a)]
  rw [← he0]
  apply p.specialize_polynomial_zero (polynomial U a) hG0 (bad a) C0
  intro s hs
  obtain ⟨hs0,hds,hpu,hmu⟩ := generic_units U hU a s hs
  have hcu := MatrixPrice.cayley_unit _ _ hpu hmu
  change IsUnit ((polynomial U a).map (evalRingHom s)) ∧ p.value ((polynomial U a).map (evalRingHom s))≤C0
  rw [eval_as_cayley U hU a s hs0 hmu]
  exact ⟨MatrixPrice.scalar_unit _ hcu _ hds,by rw [p.scalar _ hcu _ hds]; exact hp s⁻¹ hpu hmu⟩


-- @@ L319-319 verbatim
end ExactFourier.CayleyLimit


-- @@ L321-321 verbatim
end

-- @@ L322-322 verbatim
end


-- @@ L324-324 verbatim
section

-- @@ L325-325 verbatim
noncomputable section

-- @@ L326-326 verbatim
namespace ExactFourier.CayleyLimit

-- @@ L327-327 verbatim
variable {α : Type} [Fintype α] [DecidableEq α]


-- @@ L329-329 verbatim
def reciprocal (a : α → ℂ) (i : α) : ℂ := if a i=0 then 0 else 2/(a i)


-- @@ L331-336 verbatim
theorem sign_square (a : α → ℂ) : Matrix.diagonal (sign a)*Matrix.diagonal (sign a)=(1 : Matrix α α ℂ) := by
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i=j
  · subst j; simp [sign]; split_ifs <;> norm_num
  · simp [Matrix.diagonal,h]


-- @@ L338-340 verbatim
theorem reflection_square (U : Matrix α α ℂ) (hU : IsUnit U) (a : α → ℂ) :
    Similarity.conj U (Matrix.diagonal (sign a))*Similarity.conj U (Matrix.diagonal (sign a))=1 := by
  rw [Similarity.mul U _ _ hU,sign_square,Similarity.one U hU]


-- @@ L342-351 verbatim
theorem killed_sum (U : Matrix α α ℂ) (hU : IsUnit U) (a : α → ℂ) :
    Similarity.conj U (Matrix.diagonal a)*(1+Similarity.conj U (Matrix.diagonal (sign a)))=0 := by
  rw [← Similarity.one U hU,← Similarity.add,Similarity.mul U _ _ hU]
  rw [mul_add,mul_one,Matrix.diagonal_mul_diagonal]
  have hh : Matrix.diagonal a+Matrix.diagonal (fun i=>a i*sign a i)=0 := by
    ext i j
    by_cases h : i=j
    · subst j; simp [sign]; split_ifs <;> simp_all
    · simp [Matrix.diagonal,h]
  rw [hh,Similarity.zero]


-- @@ L353-365 verbatim
theorem difference_factor (U : Matrix α α ℂ) (hU : IsUnit U) (a : α → ℂ) :
    1-Similarity.conj U (Matrix.diagonal (sign a))=
      Similarity.conj U (Matrix.diagonal a)*Similarity.conj U (Matrix.diagonal (reciprocal a)) := by
  rw [Similarity.mul U _ _ hU,← Similarity.one U hU,← Similarity.sub]
  congr 1
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases h : i=j
  · subst j
    by_cases hi : a i=0 <;> simp [sign,reciprocal,hi]
    field_simp
    ring
  · simp [Matrix.diagonal,h]


-- @@ L367-370 verbatim
theorem reflection_symm (U : Matrix α α ℂ) (hi : U⁻¹=U.transpose) (a : α → ℂ) :
    (Similarity.conj U (Matrix.diagonal (sign a))).IsSymm := by
  change (Similarity.conj U (Matrix.diagonal (sign a))).transpose=_
  simp [Similarity.conj,hi,Matrix.transpose_mul,mul_assoc]


-- @@ L372-372 verbatim
end ExactFourier.CayleyLimit


-- @@ L374-374 verbatim
end

-- @@ L375-375 verbatim
end


-- @@ L377-377 verbatim
end OAI
