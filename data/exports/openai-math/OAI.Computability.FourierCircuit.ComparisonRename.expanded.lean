import OAI.Computability.FourierCircuit.SlotAssembly


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
section

-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped Kronecker

-- @@ L8-8 verbatim
namespace ExactFourier.Packing

-- @@ L9-13 verbatim
variable {τ σ : Type}
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {E : σ→Type} [∀ t,Fintype (E t)] [∀ t,DecidableEq (E t)]
 {B : ∀ t,Matrix (E t) (E t) ℂ}


-- @@ L15-22 verbatim
abbrev mapPair (f : τ→σ) (p : LivePair τ) : LivePair σ :=
 ⟨(p.1.1.map f,p.1.2.map f),by
   rcases p with ⟨⟨a,b⟩,h⟩
   cases a with
   | none => cases b with
     | none => exact (h rfl).elim
     | some b => simp
   | some a => simp⟩

-- @@ L23-26 verbatim
def speciesEquiv (f : τ→σ) (e : ∀ t,D t≃E (f t)) :
 ∀ s : Option τ,SpeciesDomain D s≃SpeciesDomain E (s.map f)
 | none => Equiv.refl _
 | some t => e t

-- @@ L27-29 verbatim
abbrev pairEquiv (f : τ→σ) (e : ∀ t,D t≃E (f t)) (p : LivePair τ) :
 PairDomain D p≃PairDomain E (mapPair f p) :=
 (speciesEquiv f e p.1.1).prodCongr (speciesEquiv f e p.1.2)


-- @@ L31-38 verbatim
theorem speciesEquiv_matrix
    {τ : Type} {σ : Type} {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} {E : σ → Type} [(t : σ) → Fintype (E t)] [(t : σ) → DecidableEq (E t)] {B : (t : σ) → Matrix (E t) (E t) ℂ} (f : τ→σ) (e : ∀ t,D t≃E (f t))
 (he : ∀ t,Matrix.reindex (e t) (e t) (A t)=B (f t)) (s : Option τ) :
 Matrix.reindex (speciesEquiv f e s) (speciesEquiv f e s) (speciesMatrix (A := A) s)=
 speciesMatrix (A := B) (s.map f) := by
 cases s with
 | none => rfl
 | some t => exact he t


-- @@ L40-45 verbatim
theorem pairEquiv_matrix (f : τ→σ) (e : ∀ t,D t≃E (f t))
 (he : ∀ t,Matrix.reindex (e t) (e t) (A t)=B (f t)) (p : LivePair τ) :
 Matrix.reindex (pairEquiv f e p) (pairEquiv f e p) (pairMatrix (A := A) p)=
 pairMatrix (A := B) (mapPair f p) := by
 dsimp only [pairEquiv,pairMatrix]
 rw [ExactFourier.reindex_tensor,speciesEquiv_matrix f e he,speciesEquiv_matrix f e he]


-- @@ L47-53 verbatim
abbrev PairComparison.rename (f : τ→σ) (e : ∀ t,D t≃E (f t))
 (he : ∀ t,Matrix.reindex (e t) (e t) (A t)=B (f t)) (c : PairComparison (A := A)) :
 PairComparison (A := B) where
 pair := mapPair f c.pair
 word := (c.word.rename f e).reindex (pairEquiv f e c.pair)
 correct := by
  rw [Word.matrix_reindex,Word.matrix_rename f e he,c.correct,pairEquiv_matrix f e he]


-- @@ L55-63 verbatim
theorem pairPrice_map
    {τ : Type} {σ : Type} {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {E : σ → Type} [(t : σ) → Fintype (E t)] [(t : σ) → DecidableEq (E t)] (f : τ→σ) (e : ∀ t,D t≃E (f t)) (v : σ→ℝ) (p : LivePair τ) :
 pairPrice (D := E) v (mapPair f p)=pairPrice (D := D) (v∘f) p := by
 have hc : ∀ s : Option τ,Fintype.card (SpeciesDomain E (s.map f))=Fintype.card (SpeciesDomain D s) :=
  fun s=>(Fintype.card_congr (speciesEquiv f e s)).symm
 have hp : ∀ s : Option τ,speciesPrice v (s.map f)=speciesPrice (v∘f) s := by
  intro s; cases s <;> rfl
 dsimp [pairPrice,mapPair]
 rw [hc,hc,hp,hp]


-- @@ L65-70 verbatim
@[simp] theorem PairComparison.rename_ineq (f : τ→σ) (e : ∀ t,D t≃E (f t))
 (he : ∀ t,Matrix.reindex (e t) (e t) (A t)=B (f t)) (c : PairComparison (A := A)) (v : σ→ℝ) :
 (pairPrice (D := E) v (c.rename f e he).pair≤(c.rename f e he).word.weight v) ↔
 pairPrice (D := D) (v∘f) c.pair≤c.word.weight (v∘f) := by
 dsimp only [PairComparison.rename]
 rw [pairPrice_map f e,Word.weight_reindex,Word.weight_rename]

-- @@ L71-71 verbatim
end ExactFourier.Packing


-- @@ L73-73 verbatim
end

-- @@ L74-74 verbatim
end


-- @@ L76-76 verbatim
section

-- @@ L77-77 verbatim
noncomputable section

-- @@ L78-78 verbatim
namespace ExactFourier.Packing

-- @@ L79-82 verbatim
structure GMatrix where
 width : ℕ
 mat : Matrix (Fin width) (Fin width) ℂ
 unit : IsUnit mat

-- @@ L83-83 verbatim
abbrev GMatrix.domain (g : GMatrix) := Fin g.width


-- @@ L85-85 verbatim
def shearG : GMatrix := ⟨2,shearU,shearU_unit⟩

-- @@ L86-86 verbatim
abbrev shearD (_ : Unit) := Fin 2

-- @@ L87-87 verbatim
abbrev shearA (_ : Unit) := shearU


-- @@ L89-92 verbatim
theorem GMatrix.upper_exists (g : GMatrix) :
 ∃ C : ℕ,∃ W : Word shearD shearA g.domain,W.matrix=g.mat ∧
 ∀ p : Unit→ℝ,W.weight p=(C : ℝ)*p () :=
 shear_word_exists () (Equiv.refl _) (by rfl) g.mat g.unit


-- @@ L94-94 verbatim
def GMatrix.upperCost (g : GMatrix) : ℕ := g.upper_exists.choose

-- @@ L95-95 verbatim
def GMatrix.upperWord (g : GMatrix) : Word shearD shearA g.domain := g.upper_exists.choose_spec.choose

-- @@ L96-97 verbatim
@[simp] theorem GMatrix.upperWord_matrix (g : GMatrix) : g.upperWord.matrix=g.mat :=
 g.upper_exists.choose_spec.choose_spec.1

-- @@ L98-99 verbatim
@[simp] theorem GMatrix.upperWord_weight (g : GMatrix) (p : Unit→ℝ) :
 g.upperWord.weight p=(g.upperCost : ℝ)*p () := g.upper_exists.choose_spec.choose_spec.2 p


-- @@ L101-104 verbatim
structure GlobalComparison where
 num : ℕ
 family : Fin num→GMatrix
 comparison : PairComparison (D := fun t=>(family t).domain) (A := fun t=>(family t).mat)


-- @@ L106-108 verbatim
def GlobalComparison.holds (c : GlobalComparison) (p : GMatrix→ℝ) : Prop :=
 pairPrice (D := fun t=>(c.family t).domain) (p∘c.family) c.comparison.pair≤
 c.comparison.word.weight (p∘c.family)


-- @@ L110-110 verbatim
def GlobalConstraints (p : GMatrix→ℝ) : Prop := ∀ c : GlobalComparison,c.holds p


-- @@ L112-121 verbatim
theorem Word.continuous_weight {τ : Type} {D : τ→Type}
 [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ} {α : Type} [Fintype α] [DecidableEq α]
 (f : τ→GMatrix) (W : Word D A α) : Continuous (fun p : GMatrix→ℝ=>W.weight (p∘f)) := by
 induction W with
 | nil => exact continuous_const
 | cons s W ih =>
  cases s with
  | mono M h => exact ih
  | call t e => exact (continuous_apply (f t)).add ih


-- @@ L123-129 verbatim
theorem GlobalComparison.closed (c : GlobalComparison) : IsClosed {p : GMatrix→ℝ|c.holds p} := by
 apply isClosed_le _ (Word.continuous_weight c.family c.comparison.word)
 have hp : ∀ s : Option (Fin c.num),Continuous (fun p : GMatrix→ℝ=>speciesPrice (p∘c.family) s) := by
  intro s; cases s with
  | none => exact continuous_const
  | some t => exact continuous_apply (c.family t)
 exact (continuous_const.mul (hp _)).add (continuous_const.mul (hp _))


-- @@ L131-132 verbatim
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 (f : τ→GMatrix)


-- @@ L134-139 verbatim
theorem family_cast_matrix
    {τ : Type} [Fintype τ] [DecidableEq τ] (f : τ → ExactFourier.Packing.GMatrix) {t u : τ} (h : t=u) :
 Matrix.reindex (Equiv.cast (congrArg (fun t=>(f t).domain) h))
  (Equiv.cast (congrArg (fun t=>(f t).domain) h)) (f t).mat=(f u).mat := by
 cases h
 rfl


-- @@ L141-146 verbatim
abbrev toGlobalComparison (c : PairComparison (D := fun t=>(f t).domain) (A := fun t=>(f t).mat)) : GlobalComparison where
 num := Fintype.card τ
 family := f∘(Fintype.equivFin τ).symm
 comparison := c.rename (Fintype.equivFin τ)
  (fun t=>Equiv.cast (congrArg (fun t=>(f t).domain) ((Fintype.equivFin τ).symm_apply_apply t).symm))
  (fun t=>family_cast_matrix f ((Fintype.equivFin τ).symm_apply_apply t).symm)


-- @@ L148-157 verbatim
theorem GlobalConstraints.apply {p : GMatrix→ℝ} (hp : GlobalConstraints p)
 (c : PairComparison (D := fun t=>(f t).domain) (A := fun t=>(f t).mat)) :
 pairPrice (D := fun t=>(f t).domain) (p∘f) c.pair≤c.word.weight (p∘f) := by
 have hh := hp (toGlobalComparison f c)
 dsimp only [GlobalComparison.holds,toGlobalComparison] at hh
 have hh' := (PairComparison.rename_ineq (Fintype.equivFin τ)
  (fun t=>Equiv.cast (congrArg (fun t=>(f t).domain) ((Fintype.equivFin τ).symm_apply_apply t).symm))
  (fun t=>family_cast_matrix f ((Fintype.equivFin τ).symm_apply_apply t).symm)
  c (p∘f∘(Fintype.equivFin τ).symm)).mp hh
 simpa only [Function.comp_def,Equiv.symm_apply_apply] using hh'

-- @@ L158-158 verbatim
end ExactFourier.Packing


-- @@ L160-160 verbatim
end

-- @@ L161-161 verbatim
end


-- @@ L163-163 verbatim
section

-- @@ L164-164 verbatim
noncomputable section

-- @@ L165-165 verbatim
namespace ExactFourier.Packing

-- @@ L166-167 verbatim
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]


-- @@ L169-221 verbatim
theorem pair_baseline_sum
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] (k : τ→ℕ) (I : ℕ) (t : τ) :
 (∑ p : LivePair τ,speciesCopies k I p.1.1*speciesCopies k I p.1.2*
    pairBaseline (D := D) p t)=2*k t*((∑ i,k i*Fintype.card (D i))+I) := by
 let f : (Option τ×Option τ)→ℕ := fun p=>
  speciesCopies k I p.1*speciesCopies k I p.2*
   (Fintype.card (SpeciesDomain D p.2)*(if p.1=some t then 1 else 0)+
    Fintype.card (SpeciesDomain D p.1)*(if p.2=some t then 1 else 0))
 have he : (∑ p : LivePair τ,f p.val)=∑ p,f p := by
  have h := Fintype.sum_subtype_add_sum_subtype (fun p : Option τ×Option τ=>p≠(none,none)) f
  have hz : (∑ p : {p : Option τ×Option τ // ¬p≠(none,none)},f p.val)=0 := by
   apply Finset.sum_eq_zero
   intro p hp
   have h : p.val=(none,none) := Classical.not_not.mp p.property
   simp [h,f,speciesCopies]
  rw [hz,add_zero] at h
  exact h
 change (∑ p : LivePair τ,f p.val)=_
 rw [he,Fintype.sum_prod_type]
 simp only [f,mul_add,Finset.sum_add_distrib]
 have hleft : (∑ s : Option τ,∑ r : Option τ,
    speciesCopies k I s*speciesCopies k I r*
     (Fintype.card (SpeciesDomain D r)*(if s=some t then 1 else 0)))=
    k t*((∑ i,k i*Fintype.card (D i))+I) := by
  have he : ∀ s r : Option τ,
      speciesCopies k I s*speciesCopies k I r*
       (Fintype.card (SpeciesDomain D r)*(if s=some t then 1 else 0))=
      if s=some t then k t*(speciesCopies k I r*Fintype.card (SpeciesDomain D r)) else 0 := by
   intro s r
   by_cases h : s=some t
   · subst s; simp only [ite_true,speciesCopies,mul_one]; ring
   · simp [h]
  simp_rw [he]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [← Finset.mul_sum,Fintype.sum_option]
  simp only [speciesCopies,SpeciesDomain,Fintype.card_unit,mul_one]
  congr 1
  omega
 rw [hleft]
 have hright : (∑ s : Option τ,∑ r : Option τ,
    speciesCopies k I s*speciesCopies k I r*
     (Fintype.card (SpeciesDomain D s)*(if r=some t then 1 else 0)))=
    k t*((∑ i,k i*Fintype.card (D i))+I) := by
  rw [Finset.sum_comm]
  convert hleft using 1
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  ring
 rw [hright]
 ring


-- @@ L223-223 verbatim
end ExactFourier.Packing


-- @@ L225-225 verbatim
end

-- @@ L226-226 verbatim
end


-- @@ L228-228 verbatim
section

-- @@ L229-229 verbatim
noncomputable section

-- @@ L230-230 verbatim
namespace ExactFourier.Packing

-- @@ L231-234 verbatim
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {ρ : Type} [Fintype ρ] [DecidableEq ρ]


-- @@ L236-238 verbatim
abbrev familyKey (c : ρ→PairComparison (A := A)) : LivePair τ⊕ρ→LivePair τ
 | .inl p => p
 | .inr r => (c r).pair


-- @@ L240-243 verbatim
def familyProgram (c : ρ→PairComparison (A := A)) :
 ∀ p : LivePair τ⊕ρ,FramedWord D (PairDomain D (familyKey c p))
 | .inl p => (standardPair (A := A) p).framed
 | .inr r => (c r).word.framed


-- @@ L245-248 verbatim
def familyMultiplicity (c : ρ→PairComparison (A := A)) (n : LivePair τ→ℕ) (a : ρ→ℕ) :
 LivePair τ⊕ρ→ℕ
 | .inl p => n p-∑ r,if (c r).pair=p then a r else 0
 | .inr r => a r


-- @@ L250-255 verbatim
theorem familyProgram_matrix
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} {ρ : Type} [Fintype ρ] [DecidableEq ρ] (c : ρ→PairComparison (A := A)) (p : LivePair τ⊕ρ) :
 (familyProgram c p).matrix (A := A)=pairMatrix (A := A) (familyKey c p) := by
 cases p with
 | inl p => exact (Word.matrix_framed _).trans (standardPair_matrix p)
 | inr r => exact (Word.matrix_framed _).trans (c r).correct


-- @@ L257-264 verbatim
theorem familyMultiplicity_key
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} {ρ : Type} [Fintype ρ] [DecidableEq ρ] (c : ρ→PairComparison (A := A)) (n : LivePair τ→ℕ) (a : ρ→ℕ)
 (h : ∀ p,(∑ r,if (c r).pair=p then a r else 0)≤n p) (s : LivePair τ) :
 (∑ p,if familyKey c p=s then familyMultiplicity c n a p else 0)=n s := by
 rw [Fintype.sum_sum_type]
 simp only [familyKey,familyMultiplicity]
 simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true]
 exact Nat.sub_add_cancel (h s)


-- @@ L266-279 verbatim
theorem familyMultiplicity_scale
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} {ρ : Type} [Fintype ρ] [DecidableEq ρ] (c : ρ→PairComparison (A := A))
 (n : LivePair τ→ℕ) (a : ρ→ℕ) (u : ℕ) (p : LivePair τ⊕ρ) :
 familyMultiplicity c (fun p=>n p*u) (fun r=>a r*u) p=familyMultiplicity c n a p*u := by
 cases p with
 | inl p =>
  simp only [familyMultiplicity]
  rw [Nat.sub_mul]
  congr 1
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  split_ifs <;> simp
 | inr r => rfl


-- @@ L281-301 verbatim
theorem family_saving
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} {ρ : Type} [Fintype ρ] [DecidableEq ρ] (c : ρ→PairComparison (A := A)) (n : LivePair τ→ℕ) (a : ρ→ℕ)
 (h : ∀ p,(∑ r,if (c r).pair=p then a r else 0)≤n p) (t : τ) :
 (∑ p,(n p : ℤ)*pairBaseline (D := D) p t)-
 (∑ p,(familyMultiplicity c n a p : ℤ)*(familyProgram c p).types.count t)=
 ∑ r,(a r : ℤ)*(c r).delta t := by
 rw [Fintype.sum_sum_type]
 simp only [familyMultiplicity,familyProgram,Word.types_framed]
 simp only [show ∀ p : LivePair τ,((standardPair (A := A) p).calls).count t=pairBaseline (D := D) p t from fun p=>standardPair_count p t]
 simp only [Nat.cast_sub (h _),Finset.sum_sub_distrib,sub_mul]
 have hswap : (∑ p,(∑ r,if (c r).pair=p then (a r : ℤ) else 0)*pairBaseline (D := D) p t)=
      ∑ r,(a r : ℤ)*pairBaseline (D := D) (c r).pair t := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.mem_univ,ite_true]
 simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_zero] at *
 rw [hswap]
 simp only [PairComparison.delta,Word.count,mul_sub,Finset.sum_sub_distrib]
 ring


-- @@ L303-310 verbatim
theorem family_total_scale (c : ρ→PairComparison (A := A))
 (n : LivePair τ→ℕ) (a : ρ→ℕ) (u : ℕ) (t : τ) :
 (∑ p,familyMultiplicity c (fun p=>n p*u) (fun r=>a r*u) p*(familyProgram c p).types.count t)=
 (∑ p,familyMultiplicity c n a p*(familyProgram c p).types.count t)*u := by
 simp only [familyMultiplicity_scale,Finset.sum_mul]
 apply Finset.sum_congr rfl
 intros
 ring


-- @@ L312-312 verbatim
end ExactFourier.Packing


-- @@ L314-314 verbatim
end

-- @@ L315-315 verbatim
end


-- @@ L317-317 verbatim
section

-- @@ L318-318 verbatim
noncomputable section

-- @@ L319-319 verbatim
namespace ExactFourier.Packing

-- @@ L320-323 verbatim
variable {τ : Type} [Fintype τ] [DecidableEq τ]
 {D : τ→Type} [∀ t,Fintype (D t)] [∀ t,DecidableEq (D t)]
 {A : ∀ t,Matrix (D t) (D t) ℂ}
 {α : Type} [Fintype α] [DecidableEq α]


-- @@ L325-326 verbatim
def framedSlot (W : FramedWord D α) {T : ℕ} (time : Fin W.frames.length→Fin T) (t : Fin T) : Option (Frame D α) :=
 Function.extend time (fun i=>some (W.frames.get i)) (fun _=>none) t


-- @@ L328-330 verbatim
def slotCall : Option (Frame D α)→Step D A α
 | none => .mono 1 MonomialMatrix.one
 | some f => .call f.type f.tuple


-- @@ L332-334 verbatim
def slotMono : Option (Frame D α)→Matrix α α ℂ
 | none => 1
 | some f => f.mono


-- @@ L336-340 verbatim
theorem slotMono_monomial
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {α : Type} [Fintype α] [DecidableEq α] (f : Option (Frame D α)) : MonomialMatrix (slotMono f) := by
 cases f with
 | none => exact MonomialMatrix.one
 | some f => exact f.monomial


-- @@ L342-342 verbatim
def slotMatrix (f : Option (Frame D α)) : Matrix α α ℂ := slotMono f*(slotCall (A := A) f).matrix


-- @@ L344-353 verbatim
theorem slotMatrix_extend
    {τ : Type} [Fintype τ] [DecidableEq τ] {D : τ → Type} [(t : τ) → Fintype (D t)] [(t : τ) → DecidableEq (D t)] {A : (t : τ) → Matrix (D t) (D t) ℂ} {α : Type} [Fintype α] [DecidableEq α] (W : FramedWord D α) {T : ℕ} (time : Fin W.frames.length→Fin T)
 (ht : Function.Injective time) (t : Fin T) :
 slotMatrix (A := A) (framedSlot W time t)=
   Function.extend time (fun i=>(W.frames.get i).matrix (A := A)) (fun _=>1) t := by
 classical
 by_cases h : ∃ i,time i=t
 · obtain ⟨i,rfl⟩ := h
   simp [framedSlot,ht.extend_apply,slotMatrix,slotMono,slotCall,Step.matrix,Frame.matrix]
 · simp [framedSlot,Function.extend_apply' _ _ _ h,slotMatrix,slotMono,slotCall,Step.matrix]


-- @@ L355-362 verbatim
theorem slotMatrix_product (W : FramedWord D α) {T : ℕ} (time : Fin W.frames.length→Fin T)
 (ht : StrictMono time) :
 (List.ofFn (fun t=>slotMatrix (A := A) (framedSlot W time t))).prod * W.tail=W.matrix (A := A) := by
 simp_rw [slotMatrix_extend W time ht.injective]
 rw [ordered_padding time ht]
 change (List.ofFn (Frame.matrix∘W.frames.get)).prod*W.tail=(W.frames.map Frame.matrix).prod*W.tail
 rw [← List.map_ofFn]
 simp


-- @@ L364-365 verbatim
variable {π : Type} [Fintype π] [DecidableEq π]
 {β : π→Type} [∀ p,Fintype (β p)] [∀ p,DecidableEq (β p)]


-- @@ L367-369 verbatim
def framedLayer (W : ∀ p,FramedWord D (β p)) {T : ℕ}
 (time : ∀ p,Fin (W p).frames.length→Fin T) (t : Fin T) : Matrix (Σ p,β p) (Σ p,β p) ℂ :=
 Matrix.blockDiagonal' (fun p=>slotMatrix (A := A) (framedSlot (W p) (time p) t))


-- @@ L371-386 verbatim
theorem framedLayer_product (W : ∀ p,FramedWord D (β p)) {T : ℕ}
 (time : ∀ p,Fin (W p).frames.length→Fin T) (ht : ∀ p,StrictMono (time p)) :
 (List.ofFn (framedLayer (A := A) W time)).prod * Matrix.blockDiagonal' (fun p=>(W p).tail)=
   Matrix.blockDiagonal' (fun p=>(W p).matrix (A := A)) := by
 let φ := Matrix.blockDiagonal'RingHom (m' := β) (α := ℂ)
 let f := fun t p=>slotMatrix (A := A) (framedSlot (W p) (time p) t)
 change (List.ofFn (φ∘f)).prod*φ (fun p=>(W p).tail)=φ (fun p=>(W p).matrix)
 rw [← List.map_ofFn,← map_list_prod,← map_mul]
 apply congrArg φ
 funext p
 change (List.ofFn f).prod p*(W p).tail=_
 have he := map_list_prod (Pi.evalMonoidHom (fun p=>Matrix (β p) (β p) ℂ) p) (List.ofFn f)
 rw [List.map_ofFn] at he
 change (List.ofFn f).prod p=(List.ofFn (fun t=>f t p)).prod at he
 rw [he]
 exact slotMatrix_product (W p) (time p) (ht p)


-- @@ L388-388 verbatim
variable {ν : Type} [Fintype ν] [DecidableEq ν]


-- @@ L390-400 verbatim
theorem gather_framed_slot (k : τ→ℕ) (S : ∀ p,Option (Frame D (β p)))
 (hc : ∀ t,Fintype.card {p // (slotCall (A := A) (S p)).kind=some t}=k t)
 (hw : Fintype.card (ActiveSpace D k ⊕ ν)≤Fintype.card (Σ p,β p)) :
 ∃ (M : Matrix (Σ p,β p) (Σ p,β p) ℂ) (e : ActiveSpace D k ⊕ ν ↪ (Σ p,β p)),
 MonomialMatrix M ∧ Matrix.blockDiagonal' (fun p=>slotMatrix (A := A) (S p))=
   M*Embedded.matrix e (inventoryWithIdentity (A := A) (ν := ν) k) := by
 obtain ⟨M,e,hM,he⟩ := assemble_slot (ν := ν) k (fun p=>slotCall (S p)) hc hw
 refine ⟨Matrix.blockDiagonal' (fun p=>slotMono (S p))*M,e,
   (MonomialMatrix.blockDiagonal' _ (fun p=>slotMono_monomial (S p))).mul hM,?_⟩
 change Matrix.blockDiagonal' (fun p=>slotMono (S p)*(slotCall (A := A) (S p)).matrix)=_
 rw [Matrix.blockDiagonal'_mul,he,mul_assoc]


-- @@ L402-402 verbatim
end ExactFourier.Packing


-- @@ L404-404 verbatim
end

-- @@ L405-405 verbatim
end


-- @@ L407-407 verbatim
end OAI
