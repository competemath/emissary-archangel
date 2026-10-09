import OAI.Algebra.Drinfeld.Transport


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace DeligneDrinfeld

-- @@ L8-8 verbatim
namespace AlphabetTransport

-- @@ L9-9 verbatim
open AssociativeElimination UniversalEmbedding

-- @@ L10-10 verbatim
variable {R α β γ : Type*} [CommRing R]


-- @@ L12-13 verbatim
@[simp] theorem renameAssoc_atom (f : α → β) (a : α) : renameAssoc (R:=R) f (atom a)=atom (f a) := by
  simp [renameAssoc]


-- @@ L15-19 verbatim
theorem assoc_comp (f : α → β) (g : β → γ) :
    (renameAssoc (R:=R) g).comp (renameAssoc f)=renameAssoc (g ∘ f) := by
  apply hom_ext
  intro a
  simp


-- @@ L21-27 verbatim
theorem assoc_retract (f : α → β) (g : β → α) (h : Function.LeftInverse g f) (p : A R α) :
    renameAssoc g (renameAssoc f p)=p := by
  have he : (renameAssoc (R:=R) g).comp (renameAssoc f)=AlgHom.id R (A R α) := by
    apply hom_ext
    intro a
    simp [h a]
  exact AlgHom.congr_fun he p


-- @@ L29-32 verbatim
theorem assoc_injective (f : α → β) (g : β → α) (h : Function.LeftInverse g f) :
    Function.Injective (renameAssoc (R:=R) f) := by
  intro p q hp
  simpa only [assoc_retract f g h] using congrArg (renameAssoc g) hp


-- @@ L34-34 verbatim
end AlphabetTransport

-- @@ L35-35 verbatim
namespace QuadraticLeading

-- @@ L36-36 verbatim
open AssociativeElimination UniversalEmbedding WordGrading AlphabetTransport

-- @@ L37-37 verbatim
open RowTwo RowKernel ExactPentagon

-- @@ L38-38 verbatim
abbrev K := ZMod 2

-- @@ L39-39 verbatim
attribute [local instance] LieRing.ofAssociativeRing


-- @@ L41-45 verbatim
def bitOption : Bool ≃ Option Unit where
  toFun := fun b => if b then some () else none
  invFun := fun o => o.isSome
  left_inv b := by cases b <;> rfl
  right_inv o := by cases o with | none => rfl | some u => cases u; rfl


-- @@ L47-51 verbatim
def letters : Slot ≃ QuadraticAlphabet.Letter where
  toFun := fun | .A => .a | .C => .c | .B => .b
  invFun := fun | .a => .A | .c => .C | .b => .B
  left_inv s := by cases s <;> rfl
  right_inv s := by cases s <;> rfl


-- @@ L53-53 verbatim
def under : FreeLieAlgebra K Slot →ₗ⁅K⁆ A K Bool := quad.toLieHom.comp embed


-- @@ L55-55 verbatim
@[simp] theorem under_apply (p : FreeLieAlgebra K Slot) : under p=quad (embed p) := rfl


-- @@ L57-62 verbatim
theorem quad_transport : (renameAssoc bitOption).comp quad=
    QuadraticAlphabet.substitution.comp (renameAssoc letters) := by
  apply hom_ext
  intro k
  cases k <;> simp [quad,letters,bitOption,QuadraticAlphabet.substitution,
    QuadraticAlphabet.x,QuadraticAlphabet.y,Ring.lie_def]


-- @@ L64-69 verbatim
theorem quad_transport_inv : (renameAssoc bitOption.symm).comp QuadraticAlphabet.substitution=
    quad.comp (renameAssoc letters.symm) := by
  apply hom_ext
  intro k
  cases k <;> simp [quad,letters,bitOption,QuadraticAlphabet.substitution,
    QuadraticAlphabet.x,QuadraticAlphabet.y,Ring.lie_def]


-- @@ L71-76 verbatim
theorem quad_injective : Function.Injective quad := by
  intro p q hp
  apply assoc_injective letters letters.symm letters.left_inv
  apply QuadraticAlphabet.substitution_injective
  have h := congrArg (renameAssoc bitOption) hp
  exact (AlgHom.congr_fun quad_transport p).symm.trans (h.trans (AlgHom.congr_fun quad_transport q))


-- @@ L78-80 verbatim
theorem under_injective : Function.Injective under := by
  intro p q h
  exact UniversalEmbedding.injective (quad_injective h)


-- @@ L82-83 verbatim
theorem degree_length {α : Type*} (w : FreeMonoid α) : degree (fun _ : α => 1) w=w.toList.length := by
  simp [degree]


-- @@ L85-87 verbatim
theorem tree_degree_length {α : Type*} (t : UniversalEmbedding.Tree α) :
    LieGrading.treeDegree (fun _ : α => 1) t=t.leaves.length := by
  simp [LieGrading.treeDegree]


-- @@ L89-115 verbatim
theorem representation {ψ : FreeLieAlgebra K Bool} {n : ℕ} (hn : 1<n)
    (hψ : embed ψ∈homogeneous (fun _ => 1) n) :
    ∃! p : FreeLieAlgebra K Slot,under p=embed ψ := by
  have ho : embed (rename bitOption ψ)∈homogeneous (fun _ => 1) n := by
    rw [rename_embed]
    apply algHom_homogeneous (renameAssoc bitOption) (fun _ => 1) (fun _ => 1) ?_ hψ
    intro a
    rw [renameAssoc_atom]
    exact word_mem (FreeMonoid.of (bitOption a)) (degree_of _ _)
  have hl : rename bitOption ψ∈QuadraticAlphabet.homogeneous n := by
    have h := LieGrading.homogeneous_iff.mpr ho
    apply (show (LieGrading.homogeneousLie (fun _ : Option Unit => 1) n :
        Submodule K (FreeLieAlgebra K (Option Unit))) ≤ QuadraticAlphabet.homogeneous n from ?_) h
    apply Submodule.span_le.mpr
    rintro p ⟨t,ht,rfl⟩
    exact Submodule.subset_span ⟨t,(tree_degree_length t) ▸ ht,rfl⟩
  obtain ⟨p,hp,_⟩ := QuadraticAlphabet.homogeneous_representation hn hl
  refine ⟨rename letters.symm p,?_,fun q hq => under_injective (hq.trans ?_)⟩
  · change quad (embed (rename letters.symm p))=embed ψ
    rw [rename_embed]
    rw [← AlgHom.comp_apply,← quad_transport_inv,AlgHom.comp_apply]
    change renameAssoc bitOption.symm (QuadraticAlphabet.under p)=embed ψ
    rw [hp,rename_embed,assoc_retract bitOption bitOption.symm bitOption.left_inv]
  · change embed ψ=quad (embed (rename letters.symm p))
    rw [rename_embed,← AlgHom.comp_apply,← quad_transport_inv,AlgHom.comp_apply]
    change embed ψ=renameAssoc bitOption.symm (QuadraticAlphabet.under p)
    rw [hp,rename_embed,assoc_retract bitOption bitOption.symm bitOption.left_inv]


-- @@ L117-130 verbatim
theorem quad_homogeneous (a : Slot) : quad (atom a)∈homogeneous (fun _ => 1) (weight a) := by
  have hx : (atom false : A K Bool)∈homogeneous (fun _ => 1) 1 := word_mem _ rfl
  have hy : (atom true : A K Bool)∈homogeneous (fun _ => 1) 1 := word_mem _ rfl
  cases a with
  | A =>
    rw [quad,lift_atom]
    have h := homogeneous_mul hx hx
    exact h
  | C =>
    rw [quad,lift_atom]
    have h1 := homogeneous_mul hx hy
    have h2 := homogeneous_mul hy hx
    exact (homogeneous _ 2).sub_mem h1 h2
  | B => simpa only [quad,lift_atom,weight] using hy


-- @@ L132-138 verbatim
theorem representation_weight {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot} {n : ℕ}
    (hψ : embed ψ∈homogeneous (fun _ => 1) n) (hp : under p=embed ψ) :
    embed p∈homogeneous weight n := by
  apply homogeneous_reflect quad weight (fun _ => 1) quad_homogeneous quad_injective
  change under p∈_
  rw [hp]
  exact hψ


-- @@ L140-145 verbatim
theorem weight_count (w : FreeMonoid Slot) : degree weight w=2*degree acCount w+degree bCount w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih =>
    simp only [degree_mul,degree_of,ih]
    cases a <;> simp [weight,acCount,bCount,aCount,cCount] <;> omega


-- @@ L147-154 verbatim
theorem leading_ac {p : A K Slot} {n r m : ℕ} (hp : p∈homogeneous weight n)
    (hb : p∈homogeneous bCount r) (hn : n=2*m+r) : p∈homogeneous acCount m := by
  apply mem_space
  intro w hw
  have h1 := mem_space_iff.mp hp w hw
  have h2 := mem_space_iff.mp hb w hw
  have h3 := weight_count w
  omega


-- @@ L156-164 verbatim
theorem leading_rows {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot} {n r : ℕ}
    (hp : under p=embed ψ) (hw : embed p∈homogeneous weight n)
    (hr : r<n) (hb : embed p∈above bCount r) (he : BaseChangeEquations.pentagon ψ=0)
    (s : List Slot) (hs : degree bCount (FreeMonoid.ofList s)=r) :
    RowKernel.Equation (embed (LieGrading.piece bCount r p)) s := by
  rw [LieGrading.embed_piece]
  apply ExactPentagon.row_equation hw hr (piece_mem bCount r (embed p))
    (subtract_piece_above hb) ?_ s hs
  exact full_zero hp.symm he


-- @@ L166-178 verbatim
theorem leading_no_C {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot} {n r m : ℕ}
    (hp : under p=embed ψ) (hw : embed p∈homogeneous weight n) (hr : r<n)
    (hb : embed p∈above bCount r) (he : BaseChangeEquations.pentagon ψ=0)
    (hn : n=2*m+r)
    (hz : LetterRetraction.lie (fun a => a≠Slot.A) (LieGrading.piece bCount r p)=0) :
    LieGrading.piece bCount r p∈LetterRetraction.sub (fun a => a≠Slot.C) := by
  refine RowKernel.kernel_no_C _ m r ?_ ?_ hz ?_
  · rw [LieGrading.embed_piece]
    exact leading_ac (project_preserves hw) (piece_mem bCount r (embed p)) hn
  · rw [LieGrading.embed_piece]
    exact piece_mem bCount r (embed p)
  · intro s _ hs
    exact leading_rows hp hw hr hb he s hs


-- @@ L180-180 verbatim
end QuadraticLeading


-- @@ L182-182 verbatim
namespace BaseChangeEquations

-- @@ L183-183 verbatim
open AssociativeEvaluation

-- @@ L184-184 verbatim
variable {R S : Type*} [CommRing R] [CommRing S]


-- @@ L186-187 verbatim
def special (q : FreeLieAlgebra R Bool) : FreeLieAlgebra R Bool :=
  ⁅(x : FreeLieAlgebra R Bool),eval y x q⁆+⁅(-x-y : FreeLieAlgebra R Bool),eval y (-x-y) q⁆


-- @@ L189-191 verbatim
theorem cast_special (q : FreeLieAlgebra ℤ Bool) :
    IntegralBaseChange.lie (S:=S) (special q)=special (IntegralBaseChange.lie q) := by
  simp only [special,map_add,LieHom.map_lie,cast_eval_lie,map_sub,map_neg,cast_x,cast_y]


-- @@ L193-201 verbatim
theorem reduce_special (q : FreeLieAlgebra ℤ Bool) {n : ℕ}
    (hq : (IntegralBaseChange.lie q : L)∈W)
    (hw : (IntegralBaseChange.lie q : L)∈Ln n) (hn : 2<n) :
    special (IntegralBaseChange.lie (S:=S) q)=0 := by
  have hi : special q=0 := by
    apply IntegralBaseChange.lie_rational_injective
    rw [cast_special,map_zero]
    exact Differentiation.special_identity hq hw hn DeligneDrinfeld.x DeligneDrinfeld.y
  rw [← cast_special,hi,map_zero]


-- @@ L203-204 verbatim
theorem eval_comp (a b c d : FreeLieAlgebra R Bool) (q : FreeLieAlgebra R Bool) :
    eval a b (eval c d q)=eval (eval a b c) (eval a b d) q := AssociativeEvaluation.map_eval _ _ _ _


-- @@ L206-211 verbatim
theorem eval_self (q : FreeLieAlgebra R Bool) : eval x y q=q := by
  have h : eval (R:=R) x y=LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro b
    cases b <;> simp [eval,x,y]
  exact LieHom.congr_fun h q


-- @@ L213-216 verbatim
theorem swapped {q : FreeLieAlgebra R Bool} (hq : antisymmetry q=0)
    (a b : FreeLieAlgebra R Bool) : eval a b q+eval b a q=0 := by
  have h := congrArg (eval a b) hq
  simpa only [antisymmetry,map_add,eval_comp,eval_y,eval_x,map_zero] using h


-- @@ L218-218 verbatim
end BaseChangeEquations

-- @@ L219-219 verbatim
namespace TwoModule

-- @@ L220-220 verbatim
variable {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]

-- @@ L221-223 verbatim
theorem add_self (a : M) : a+a=0 := by
  calc a+a=((1 : ZMod 2)+1) • a := by rw [add_smul,one_smul]
       _=0 := by rw [show (1 : ZMod 2)+1=0 from by decide,zero_smul]


-- @@ L225-227 verbatim
theorem neg_eq (a : M) : -a=a := by
  apply neg_eq_iff_add_eq_zero.mpr
  exact add_self a


-- @@ L229-229 verbatim
theorem sub_eq_add (a b : M) : a-b=a+b := by rw [sub_eq_add_neg,neg_eq]


-- @@ L231-233 verbatim
theorem eq_of_add_zero {a b : M} (h : a+b=0) : a=b := by
  have := eq_neg_of_add_eq_zero_left h
  simpa only [neg_eq] using this

-- @@ L234-234 verbatim
end TwoModule

-- @@ L235-235 verbatim
namespace BaseChangeEquations

-- @@ L236-236 verbatim
abbrev K := ZMod 2


-- @@ L238-246 verbatim
theorem deletion_special {q : FreeLieAlgebra K Bool}
    (ha : antisymmetry q=0) (hs : special q=0) :
    ⁅(x : FreeLieAlgebra K Bool),q+eval (x+y) y q⁆+⁅(y : FreeLieAlgebra K Bool),eval (x+y) y q⁆=0 := by
  have hswap : eval y x q=q := by
    exact (TwoModule.eq_of_add_zero ha).symm
  have hswap2 : eval y (x+y) q=eval (x+y) y q :=
    TwoModule.eq_of_add_zero (swapped ha y (x+y))
  simp only [special,TwoModule.neg_eq,TwoModule.sub_eq_add,hswap,hswap2,add_lie] at hs
  simpa only [lie_add,add_assoc] using hs

-- @@ L247-247 verbatim
end BaseChangeEquations


-- @@ L249-249 verbatim
namespace WordGrading

-- @@ L250-250 verbatim
open AssociativeElimination

-- @@ L251-251 verbatim
variable {R α : Type*} [CommRing R]


-- @@ L253-253 verbatim
def lower (wt : α → ℕ) (c n : ℕ) : Submodule R (A R α) := space (fun w => degree wt w+c=n)


-- @@ L255-257 verbatim
theorem lower_mul_homogeneous {wt : α → ℕ} {c n m : ℕ} {p q : A R α}
    (hp : p∈lower wt c n) (hq : q∈homogeneous wt m) : p*q∈lower wt c (n+m) :=
  mul_mem (by intro u v hu hv; simp only [degree_mul]; omega) hp hq


-- @@ L259-261 verbatim
theorem homogeneous_mul_lower {wt : α → ℕ} {c n m : ℕ} {p q : A R α}
    (hp : p∈homogeneous wt n) (hq : q∈lower wt c m) : p*q∈lower wt c (n+m) :=
  mul_mem (by intro u v hu hv; simp only [degree_mul]; omega) hp hq


-- @@ L263-275 verbatim
theorem deriv_lower (wt : α → ℕ) (c : ℕ) (f : α → A R α)
    (hf : ∀ a,f a∈lower wt c (wt a)) {n : ℕ} {p : A R α}
    (hp : p∈homogeneous wt n) : deriv f p∈lower wt c n := by
  have hw (w : FreeMonoid α) : deriv f (word w)∈lower wt c (degree wt w) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [word_mul,word_of,AssociativeElimination.deriv_mul,deriv_atom]
      simp only [degree_mul,degree_of]
      exact (lower wt c _).add_mem
        (lower_mul_homogeneous (hf a) (word_mem w rfl))
        (homogeneous_mul_lower (word_mem (FreeMonoid.of a) (degree_of wt a)) ih)
  exact map_space (deriv f) _ (by intro w h; simpa only [h] using hw w) hp


-- @@ L277-285 verbatim
theorem deriv_lowers_above (wt : α → ℕ) (c : ℕ) (f : α → A R α)
    (hf : ∀ a,f a∈lower wt c (wt a)) {n : ℕ} {p : A R α}
    (hp : p∈above wt n) : deriv f p∈above wt (n-c) := by
  apply map_space (deriv f) _ ?_ hp
  intro w hw
  apply space_mono (P:=fun v => degree wt v+c=degree wt w) ?_
    (deriv_lower wt c f hf (word_mem w rfl))
  intro v hv
  omega


-- @@ L287-289 verbatim
theorem lower_homogeneous {wt : α → ℕ} {c n : ℕ} {p : A R α}
    (hp : p∈lower wt c n) : p∈homogeneous wt (n-c) :=
  space_mono (by intro w hw; omega) hp


-- @@ L291-293 verbatim
theorem piece_zero_of_above {wt : α → ℕ} {n k : ℕ} {p : A R α}
    (hp : p∈above wt n) (hkn : k<n) : piece wt k p=0 :=
  project_eq_zero hp (by intro w hw hk; omega)


-- @@ L295-299 verbatim
theorem homogeneous_add_high_zero {wt : α → ℕ} {n k : ℕ} {p q : A R α}
    (hp : p∈homogeneous wt k) (hq : q∈above wt n) (hkn : k<n) (hz : p+q=0) : p=0 := by
  have h := congrArg (piece wt k) hz
  rw [map_add,piece_homogeneous hp,ite_eq_left rfl,piece_zero_of_above hq hkn,add_zero,map_zero] at h
  exact h


-- @@ L301-301 verbatim
end WordGrading


-- @@ L303-303 verbatim
namespace ResidualKernel


-- @@ L305-305 verbatim
section

-- @@ L306-306 verbatim
open AssociativeElimination UniversalEmbedding WordGrading RowTwo RowKernel ExactPentagon

-- @@ L307-307 verbatim
abbrev K := ZMod 2

-- @@ L308-308 verbatim
attribute [local instance] LieRing.ofAssociativeRing


-- @@ L310-310 verbatim
def low : Slot → A K Slot | .B => atom .C | _ => 0

-- @@ L311-311 verbatim
def high : Slot → A K Slot | .C => atom .A*atom .B-atom .B*atom .A | _ => 0

-- @@ L312-312 verbatim
def delta : Slot → A K Slot := fun a => low a+high a


-- @@ L314-315 verbatim
def tau : A K Slot →ₐ[K] A K Slot := lift (fun
  | .A => atom .A+atom .C+atom .B*atom .B | .C => atom .C | .B => atom .B)

-- @@ L316-317 verbatim
def tau0 : A K Slot →ₐ[K] A K Slot := lift (fun
  | .A => atom .A+atom .C | .C => atom .C | .B => atom .B)


-- @@ L319-321 verbatim
theorem deriv_add (f g : Slot → A K Slot) (p : A K Slot) :
    deriv (fun a => f a+g a) p=deriv f p+deriv g p := by
  simpa only [TwoModule.sub_eq_add] using WordGrading.deriv_sub f g p


-- @@ L323-323 verbatim
theorem delta_split (p : A K Slot) : deriv delta p=deriv low p+deriv high p := deriv_add low high p


-- @@ L325-345 verbatim
theorem quad_delta (p : A K Slot) :
    quad (deriv delta p)=atom false*quad p-quad p*atom false := by
  have hg (a : Slot) : quad (delta a)=atom false*quad (atom a)-quad (atom a)*atom false := by
    cases a <;> simp only [delta,low,high,quad,lift_atom,map_add,map_mul,map_zero,
      zero_add,add_zero,TwoModule.sub_eq_add,mul_add,add_mul]
    · simp [mul_assoc,TwoModule.add_self]
    · have h : (atom false*atom true*atom false : A K Bool)+atom false*atom true*atom false=0 := TwoModule.add_self _
      simp only [mul_assoc] at h ⊢
      apply eq_of_sub_eq_zero
      calc _ = -(atom false*(atom true*atom false)+atom false*(atom true*atom false)) := by abel
           _ = 0 := by rw [h,neg_zero]
  have hw (w : FreeMonoid Slot) : quad (deriv delta (word w))=atom false*quad (word w)-quad (word w)*atom false := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      rw [word_mul,word_of,AssociativeElimination.deriv_mul,map_add,map_mul,map_mul,deriv_atom,hg,ih,map_mul]
      noncomm_ring
  induction p using MonoidAlgebra.induction_on with
  | of w => exact hw w
  | add p q hp hq => simp only [map_add,hp,hq,mul_add,add_mul]; abel
  | smul c p hp => simp only [map_smul,hp,mul_smul_comm,smul_mul_assoc,smul_sub]


-- @@ L347-356 verbatim
theorem quad_tau : quad.comp tau=(algEval (atom false+atom true) (atom true)).comp quad := by
  apply hom_ext
  intro a
  cases a <;> simp only [AlgHom.comp_apply,tau,quad,algEval,lift_atom,map_add,map_mul,
    Bool.false_eq_true,↓reduceIte,TwoModule.sub_eq_add,mul_add,add_mul]
  · abel
  · have h : (atom true*atom true : A K Bool)+atom true*atom true=0 := TwoModule.add_self _
    apply eq_of_sub_eq_zero
    calc _ = -(atom true*atom true+atom true*atom true) := by abel
         _ = 0 := by rw [h,neg_zero]


-- @@ L358-361 verbatim
theorem embed_eval (a b : FreeLieAlgebra K Bool) (ψ : FreeLieAlgebra K Bool) :
    embed (BaseChangeEquations.eval a b ψ)=algEval (embed a) (embed b) (embed ψ) := by
  rw [AssociativeEvaluation.map_eval,algEval,AssociativeEvaluation.lift_embed]
  rfl


-- @@ L363-376 verbatim
theorem full_equation {ψ : FreeLieAlgebra K Bool} {p : A K Slot}
    (hp : quad p=embed ψ) (ha : BaseChangeEquations.antisymmetry ψ=0)
    (hs : BaseChangeEquations.special ψ=0) :
    deriv delta (p+tau p)+(atom .B*tau p-tau p*atom .B)=0 := by
  apply QuadraticLeading.quad_injective
  rw [map_zero,map_add,quad_delta,map_add,map_sub,map_mul,map_mul]
  have hτ : quad (tau p)=embed (BaseChangeEquations.eval
      (BaseChangeEquations.x+BaseChangeEquations.y) BaseChangeEquations.y ψ) := by
    rw [← AlgHom.comp_apply,quad_tau,AlgHom.comp_apply,hp,embed_eval]
    simp only [map_add,BaseChangeEquations.x,BaseChangeEquations.y,embed_of]
  rw [hp,hτ]
  have h := congrArg embed (BaseChangeEquations.deletion_special ha hs)
  simpa only [map_add,LieHom.map_lie,Ring.lie_def,map_zero,BaseChangeEquations.x,
    BaseChangeEquations.y,embed_of,quad,lift_atom] using h


-- @@ L378-382 verbatim
theorem low_degree (a : Slot) : low a∈lower bCount 1 (bCount a) := by
  cases a <;> simp only [low,bCount]
  · exact (lower bCount 1 0).zero_mem
  · exact (lower bCount 1 0).zero_mem
  · exact word_mem (FreeMonoid.of Slot.C) rfl


-- @@ L384-393 verbatim
theorem high_degree (a : Slot) : high a∈homogeneous bCount (bCount a+1) := by
  have hA : (atom Slot.A : A K Slot)∈homogeneous bCount 0 := word_mem _ rfl
  have hB : (atom Slot.B : A K Slot)∈homogeneous bCount 1 := word_mem _ rfl
  cases a with
  | A => exact (homogeneous bCount 1).zero_mem
  | C =>
    have h1 := homogeneous_mul hA hB
    have h2 := homogeneous_mul hB hA
    exact (homogeneous bCount 1).sub_mem h1 h2
  | B => exact (homogeneous bCount 2).zero_mem


-- @@ L395-399 verbatim
theorem tau0_degree (a : Slot) : tau0 (atom a)∈homogeneous bCount (bCount a) := by
  cases a <;> simp only [tau0,lift_atom,bCount]
  · exact (homogeneous bCount 0).add_mem (word_mem _ rfl) (word_mem _ rfl)
  · exact word_mem _ rfl
  · exact word_mem _ rfl


-- @@ L401-410 verbatim
theorem tau_difference (a : Slot) : tau (atom a)-tau0 (atom a)∈above bCount (bCount a+1) := by
  cases a <;> simp only [tau,tau0,lift_atom,add_sub_cancel_left,sub_self,bCount]
  · have hB : (atom Slot.B : A K Slot)∈homogeneous bCount 1 := word_mem _ rfl
    have h := homogeneous_mul hB hB
    apply space_mono (P:=fun w => degree bCount w=2) ?_ h
    intro w hw
    simp only [ reduceCtorEq,↓reduceIte]
    omega
  · exact (above bCount 1).zero_mem
  · exact (above bCount 2).zero_mem


-- @@ L412-418 verbatim
theorem tau_degree (a : Slot) : tau (atom a)∈above bCount (bCount a) := by
  have h1 := homogeneous_above (tau0_degree a)
  have h2 : tau (atom a)-tau0 (atom a)∈above bCount (bCount a) :=
    space_mono (by intro w hw; omega) (tau_difference a)
  have he : tau (atom a)=(tau (atom a)-tau0 (atom a))+tau0 (atom a) := by abel
  rw [he]
  exact (above bCount _).add_mem h2 h1


-- @@ L420-451 verbatim
theorem leading_equation {p q : A K Slot} {r : ℕ} (hr : 0<r)
    (hq : q∈homogeneous bCount r) (hh : p-q∈above bCount (r+1))
    (he : deriv delta (p+tau p)+(atom .B*tau p-tau p*atom .B)=0) :
    deriv low (q+tau0 q)=0 := by
  have hqt := algHom_homogeneous tau0 bCount bCount tau0_degree hq
  have hlead : deriv low (q+tau0 q)∈homogeneous bCount (r-1) :=
    lower_homogeneous (deriv_lower bCount 1 low low_degree ((homogeneous bCount r).add_mem hq hqt))
  have hdiff : tau p-tau0 q∈above bCount (r+1) := by
    have ht := algHom_above tau bCount bCount tau_degree hh
    have hd := algHom_difference_above tau tau0 bCount bCount tau_degree tau0_degree tau_difference hq
    rw [map_sub] at ht
    have heq : tau p-tau0 q=(tau p-tau q)+(tau q-tau0 q) := by abel
    rw [heq]
    exact (above bCount _).add_mem ht hd
  have hp : p∈above bCount r := by
    have hh' : p-q∈above bCount r := space_mono (by intro w hw; omega) hh
    have heq : p=(p-q)+q := by abel
    rw [heq]
    exact (above bCount _).add_mem hh' (homogeneous_above hq)
  have hpt := algHom_above tau bCount bCount tau_degree hp
  have hdt := (above bCount (r+1)).add_mem hh hdiff
  have hl := deriv_lowers_above bCount 1 low low_degree hdt
  have hhg := deriv_above (fun a => homogeneous_above (high_degree a)) ((above bCount r).add_mem hp hpt)
  have hB : (atom Slot.B : A K Slot)∈above bCount 1 := homogeneous_above (word_mem _ rfl)
  have hbr : atom Slot.B*tau p-tau p*atom Slot.B∈above bCount (r+1) := by
    exact (above bCount _).sub_mem (by simpa only [Nat.add_comm] using above_mul hB hpt) (above_mul hpt hB)
  have hhg' : deriv high (p+tau p)∈above bCount r := space_mono (by intro w hw; omega) hhg
  have hbr' : atom Slot.B*tau p-tau p*atom Slot.B∈above bCount r := space_mono (by intro w hw; omega) hbr
  have hl' : deriv low ((p-q)+(tau p-tau0 q))∈above bCount r := by simpa using hl
  apply homogeneous_add_high_zero hlead ((above bCount r).add_mem ((above bCount r).add_mem hl' hhg') hbr') (by omega)
  rw [delta_split] at he
  convert he using 1; simp only [map_add,map_sub]; abel


-- @@ L453-453 verbatim
end


-- @@ L455-455 verbatim
open AssociativeElimination WordGrading RowTwo RowKernel


-- @@ L457-457 verbatim
def coeff (p : A K Slot) (s : List Slot) : K := p.coeff (FreeMonoid.ofList s)

-- @@ L458-458 verbatim
def monomial (s : List Slot) : A K Slot := word (FreeMonoid.ofList s)


-- @@ L460-460 verbatim
@[simp] theorem monomial_nil : monomial []=1 := rfl

-- @@ L461-462 verbatim
@[simp] theorem monomial_cons (a : Slot) (s : List Slot) : monomial (a::s)=atom a*monomial s := by
  exact word_mul (FreeMonoid.of a) (FreeMonoid.ofList s)

-- @@ L463-463 verbatim
@[simp] theorem coeff_add (p q : A K Slot) (s : List Slot) : coeff (p+q) s=coeff p s+coeff q s := rfl

-- @@ L464-464 verbatim
@[simp] theorem coeff_smul (c : K) (p : A K Slot) (s : List Slot) : coeff (c • p) s=c*coeff p s := rfl

-- @@ L465-465 verbatim
@[simp] theorem coeff_zero (s : List Slot) : coeff 0 s=0 := rfl

-- @@ L466-470 verbatim
@[simp] theorem coeff_monomial (s t : List Slot) : coeff (monomial s) t=if s=t then 1 else 0 := by
  classical
  change (Finsupp.single (FreeMonoid.ofList s) (1 : K)) (FreeMonoid.ofList t)=_
  rw [Finsupp.single_apply]
  simp only [Equiv.apply_eq_iff_eq]

-- @@ L471-473 verbatim
@[simp] theorem coeff_monomial_fun (s : List Slot) : coeff (monomial s)=(fun t => if s=t then 1 else 0) := by
  funext t
  exact coeff_monomial s t

-- @@ L474-474 verbatim
@[simp] theorem coeff_one_nil : coeff 1 []=1 := by exact coeff_monomial [] []

-- @@ L475-476 verbatim
@[simp] theorem coeff_one_cons (a : Slot) (s : List Slot) : coeff 1 (a::s)=0 := by
  simpa using coeff_monomial [] (a::s)


-- @@ L478-482 verbatim
@[simp] theorem coeff_atom_mul_nil (a : Slot) (p : A K Slot) : coeff (atom a*p) []=0 := by
  apply MonoidAlgebra.coeff_single_mul_of_forall_mul_ne
  intro v hv
  have h := congrArg FreeMonoid.toList hv
  simp at h


-- @@ L484-497 verbatim
@[simp] theorem coeff_atom_mul_cons (a b : Slot) (p : A K Slot) (s : List Slot) :
    coeff (atom a*p) (b::s)=if a=b then coeff p s else 0 := by
  by_cases h : a=b
  · subst b
    change (MonoidAlgebra.single (FreeMonoid.of a) 1*p).coeff (FreeMonoid.of a*FreeMonoid.ofList s)=_
    rw [MonoidAlgebra.coeff_single_mul_mul]
    simp only [one_mul]
    rfl
  · rw [ite_eq_right h]
    apply MonoidAlgebra.coeff_single_mul_of_forall_mul_ne
    intro v hv
    have he := congrArg FreeMonoid.toList hv
    simp only [FreeMonoid.toList_mul,FreeMonoid.toList_of,FreeMonoid.toList_ofList,List.singleton_append] at he
    exact h (List.cons.inj he).1


-- @@ L499-499 verbatim
def collapse : Slot → Slot | .C => .A | a => a


-- @@ L501-503 verbatim
def fills : List Slot → List (List Slot)
  | [] => []
  | a::s => (if a=.C then [Slot.B::s.map collapse] else []) ++ (fills s).map (collapse a :: ·)


-- @@ L505-505 verbatim
def noC (s : List Slot) : Prop := ∀ a∈s,a≠Slot.C


-- @@ L507-507 verbatim
@[simp] theorem noC_nil : noC [] := by simp [noC]

-- @@ L508-508 verbatim
@[simp] theorem noC_cons (a : Slot) (s : List Slot) : noC (a::s) ↔ a≠Slot.C ∧ noC s := by simp [noC]

-- @@ L509-509 verbatim
@[simp] theorem noC_append (s t : List Slot) : noC (s++t) ↔ noC s ∧ noC t := by simp only [noC,List.mem_append,or_imp,forall_and]


-- @@ L511-512 verbatim
@[simp] theorem tau0_atom (a : Slot) : tau0 (atom a)=match a with
    | .A => atom .A+atom .C | .C => atom .C | .B => atom .B := lift_atom _ a


-- @@ L514-529 verbatim
theorem tau0_monomial_coeff (v : List Slot) (hv : noC v) (s : List Slot) :
    coeff (tau0 (monomial v)) s=coeff (monomial v) (s.map collapse) := by
  induction v generalizing s with
  | nil => cases s <;> simp
  | cons a v ih =>
    obtain ⟨ha,hv'⟩ := noC_cons _ _ |>.mp hv
    cases a with
    | C => exact (ha rfl).elim
    | A =>
      cases s with
      | nil => simp [add_mul]
      | cons b s => cases b <;> simp [add_mul,ih hv' s,collapse]
    | B =>
      cases s with
      | nil => simp
      | cons b s => cases b <;> simp [ih hv' s,collapse]


-- @@ L531-554 verbatim
theorem deriv_tau0_monomial_coeff (v : List Slot) (hv : noC v) (s : List Slot) :
    coeff (deriv low (tau0 (monomial v))) s=((fills s).map (coeff (monomial v))).sum := by
  induction v generalizing s with
  | nil =>
    cases s with
    | nil => simp [fills]
    | cons a s =>
      cases a <;> simp [fills,collapse,List.map_map,Function.comp_def]
  | cons a v ih =>
    obtain ⟨ha,hv'⟩ := noC_cons _ _ |>.mp hv
    cases a with
    | C => exact (ha rfl).elim
    | A =>
      cases s with
      | nil => simp [AssociativeElimination.deriv_mul,add_mul,low,fills]
      | cons b s =>
        cases b <;> simp [AssociativeElimination.deriv_mul,add_mul,low,fills,
          ih hv' s,collapse,List.map_map,Function.comp_def]
    | B =>
      cases s with
      | nil => simp [AssociativeElimination.deriv_mul,low,fills]
      | cons b s =>
        cases b <;> simp [AssociativeElimination.deriv_mul,low,fills,
          ih hv' s,collapse,List.map_map,Function.comp_def,tau0_monomial_coeff v hv' s]


-- @@ L556-571 verbatim
theorem deriv_tau0_coeff {p : A K Slot} (hp : p∈space (fun w => noC w.toList)) (s : List Slot) :
    coeff (deriv low (tau0 p)) s=((fills s).map (coeff p)).sum := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    exact deriv_tau0_monomial_coeff w.toList hw s
  | zero =>
    simp only [map_zero]
    change 0=(List.map (fun _ => (0 : K)) (fills s)).sum
    simp
  | add p q _ _ hp hq =>
    simp only [map_add,coeff_add,hp,hq]
    exact (List.sum_map_add ..).symm
  | smul c p _ hp =>
    simp only [map_smul,coeff_smul,hp]
    exact (List.sum_map_mul_left ..).symm


-- @@ L573-573 verbatim
theorem collapse_eq {a : Slot} (ha : a≠Slot.C) : collapse a=a := by cases a <;> simp_all [collapse]

-- @@ L574-579 verbatim
theorem collapse_noC {s : List Slot} (hs : noC s) : s.map collapse=s := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    obtain ⟨ha,hs'⟩ := (noC_cons a s).mp hs
    simp [collapse_eq ha,ih hs']


-- @@ L581-586 verbatim
theorem fills_noC {s : List Slot} (hs : noC s) : fills s=[] := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    obtain ⟨ha,hs'⟩ := (noC_cons a s).mp hs
    simp [fills,ha,ih hs']


-- @@ L588-593 verbatim
theorem fills_prefix (u s : List Slot) (hu : noC u) : fills (u++s)=(fills s).map (u++·) := by
  induction u with
  | nil => simp
  | cons a u ih =>
    obtain ⟨ha,hu'⟩ := (noC_cons a u).mp hu
    simp [fills,ha,collapse_eq ha,ih hu',List.map_map,Function.comp_def]


-- @@ L595-598 verbatim
theorem fills_two (u v : List Slot) (hu : noC u) (hv : noC v) :
    fills (u++[Slot.C,Slot.C]++v)=[u++[Slot.B,Slot.A]++v,u++[Slot.A,Slot.B]++v] := by
  rw [List.append_assoc,fills_prefix u _ hu]
  simp [fills,collapse,collapse_noC hv,fills_noC hv]


-- @@ L600-604 verbatim
theorem fills_three (u v : List Slot) (hu : noC u) (hv : noC v) :
    fills (u++[Slot.C,Slot.C,Slot.C]++v)=
      [u++[Slot.B,Slot.A,Slot.A]++v,u++[Slot.A,Slot.B,Slot.A]++v,u++[Slot.A,Slot.A,Slot.B]++v] := by
  rw [List.append_assoc,fills_prefix u _ hu]
  simp [fills,collapse,collapse_noC hv,fills_noC hv]


-- @@ L606-606 verbatim
def count (a : Slot) (s : List Slot) : ℕ := degree (fun b => if b=a then 1 else 0) (FreeMonoid.ofList s)

-- @@ L607-607 verbatim
@[simp] theorem count_nil (a : Slot) : count a []=0 := rfl

-- @@ L608-608 verbatim
@[simp] theorem count_cons (a b : Slot) (s : List Slot) : count a (b::s)=(if b=a then 1 else 0)+count a s := rfl

-- @@ L609-610 verbatim
@[simp] theorem count_append (a : Slot) (s t : List Slot) : count a (s++t)=count a s+count a t := by
  exact degree_mul _ _ _


-- @@ L612-617 verbatim
theorem noC_count {s : List Slot} (hs : noC s) : count .C s=0 := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    obtain ⟨ha,hs'⟩ := (noC_cons a s).mp hs
    simp [ha,ih hs']


-- @@ L619-623 verbatim
theorem low_c_degree (a : Slot) : low a∈homogeneous cCount (cCount a+1) := by
  cases a with
  | A => exact (homogeneous cCount _).zero_mem
  | C => exact (homogeneous cCount _).zero_mem
  | B => exact word_mem (FreeMonoid.of Slot.C) rfl


-- @@ L625-634 verbatim
theorem low_noC_coeff {p : A K Slot} (hp : p∈space (fun w => noC w.toList))
    (s : List Slot) (hs : 2≤count .C s) : coeff (deriv low p) s=0 := by
  have h0 : p∈homogeneous cCount 0 := by
    apply space_mono ?_ hp
    intro w hw
    exact noC_count hw
  have h1 := deriv_homogeneous low_c_degree h0
  apply coeff_support h1
  change ¬count .C s=0+1
  omega


-- @@ L636-641 verbatim
theorem fills_sum_zero {p : A K Slot} (hp : p∈space (fun w => noC w.toList))
    (he : deriv low (p+tau0 p)=0) (s : List Slot) (hs : 2≤count .C s) :
    ((fills s).map (coeff p)).sum=0 := by
  have h := congrArg (fun q => coeff q s) he
  rw [map_add,coeff_add,low_noC_coeff hp s hs,zero_add,deriv_tau0_coeff hp s,coeff_zero] at h
  exact h


-- @@ L643-650 verbatim
theorem adjacent_exchange {p : A K Slot} (hp : p∈space (fun w => noC w.toList))
    (he : deriv low (p+tau0 p)=0) (u v : List Slot) (hu : noC u) (hv : noC v) :
    coeff p (u++[Slot.A,Slot.B]++v)=coeff p (u++[Slot.B,Slot.A]++v) := by
  have hc : 2≤count .C (u++[Slot.C,Slot.C]++v) := by simp; omega
  have h := fills_sum_zero hp he _ hc
  rw [fills_two u v hu hv] at h
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at h
  exact (TwoModule.eq_of_add_zero h).symm


-- @@ L652-653 verbatim
theorem noC_perm {s t : List Slot} (h : s.Perm t) : noC s ↔ noC t := by
  simp only [noC,h.mem_iff]


-- @@ L655-672 verbatim
theorem coefficient_perm {p : A K Slot} (hp : p∈space (fun w => noC w.toList))
    (he : deriv low (p+tau0 p)=0) {s t : List Slot} (h : s.Perm t) (hs : noC s)
    (u : List Slot) (hu : noC u) : coeff p (u++s)=coeff p (u++t) := by
  induction h generalizing u with
  | nil => rfl
  | @cons a s t h ih =>
    obtain ⟨ha,hs'⟩ := (noC_cons a s).mp hs
    have huv : noC (u++[a]) := (noC_append _ _).mpr ⟨hu,by simpa using ha⟩
    simpa only [List.append_assoc,List.singleton_append] using ih hs' (u++[a]) huv
  | swap a b s =>
    obtain ⟨ha,hbs⟩ := (noC_cons b (a::s)).mp hs
    obtain ⟨hb,hss⟩ := (noC_cons a s).mp hbs
    cases a <;> cases b
    all_goals try first | exact (ha rfl).elim | exact (hb rfl).elim | rfl
    · simpa only [List.append_assoc,List.cons_append,List.nil_append] using (adjacent_exchange hp he u s hu hss).symm
    · simpa only [List.append_assoc,List.cons_append,List.nil_append] using adjacent_exchange hp he u s hu hss
  | @trans s t v h₁ h₂ ih₁ ih₂ =>
    exact (ih₁ hs u hu).trans (ih₂ ((noC_perm h₁).mp hs) u hu)


-- @@ L674-674 verbatim
attribute [local instance] LieRing.ofAssociativeRing


-- @@ L676-681 verbatim
theorem count_list (a : Slot) (s : List Slot) : count a s=s.count a := by
  induction s with
  | nil => rfl
  | cons b s ih =>
    rw [count_cons,ih,List.count_cons]
    split_ifs with h <;> simp_all [Nat.add_comm]


-- @@ L683-686 verbatim
@[simp] theorem count_replicate (a b : Slot) (n : ℕ) : count a (List.replicate n b)=if b=a then n else 0 := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ,ih]; split_ifs <;> omega


-- @@ L688-696 verbatim
theorem perm_of_counts {s t : List Slot} (hs : noC s) (ht : noC t)
    (ha : count .A s=count .A t) (hb : count .B s=count .B t) : s.Perm t := by
  apply List.perm_iff_count.mpr
  intro a
  rw [← count_list,← count_list]
  cases a with
  | A => exact ha
  | C => rw [noC_count hs,noC_count ht]
  | B => exact hb


-- @@ L698-701 verbatim
theorem coefficient_eq_counts {p : A K Slot} (hp : p∈space (fun w => noC w.toList))
    (he : deriv low (p+tau0 p)=0) {s t : List Slot} (hs : noC s) (ht : noC t)
    (ha : count .A s=count .A t) (hb : count .B s=count .B t) : coeff p s=coeff p t := by
  exact coefficient_perm hp he (perm_of_counts hs ht ha hb) hs [] noC_nil


-- @@ L703-716 verbatim
theorem triple_zero {p : A K Slot} (hp : p∈space (fun w => noC w.toList))
    (he : deriv low (p+tau0 p)=0) (u : List Slot) (hu : noC u) :
    coeff p (u++[Slot.B,Slot.A,Slot.A])=0 := by
  have hc : 2≤count .C (u++[Slot.C,Slot.C,Slot.C]++[]) := by simp
  have h := fills_sum_zero hp he _ hc
  rw [fills_three u [] hu noC_nil] at h
  simp only [List.append_nil,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero] at h
  have hn1 : noC (u++[Slot.A,Slot.B,Slot.A]) := by simpa using hu
  have hn2 : noC (u++[Slot.A,Slot.A,Slot.B]) := by simpa using hu
  have hn3 : noC (u++[Slot.B,Slot.A,Slot.A]) := by simpa using hu
  have h1 := coefficient_eq_counts hp he hn1 hn3 (by simp) (by simp)
  have h2 := coefficient_eq_counts hp he hn2 hn3 (by simp) (by simp)
  rw [h1,h2,TwoModule.add_self,add_zero] at h
  exact h


-- @@ L718-730 verbatim
theorem coefficient_zero_two_As {p : A K Slot} (hp : p∈space (fun w => noC w.toList))
    (he : deriv low (p+tau0 p)=0) (s : List Slot) (hs : noC s)
    (ha : 2≤count .A s) (hb : 1≤count .B s) : coeff p s=0 := by
  let u := List.replicate (count .A s-2) Slot.A ++ List.replicate (count .B s-1) Slot.B
  have hu : noC u := by
    intro a ha
    simp only [u,List.mem_append,List.mem_replicate] at ha
    rcases ha with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> decide
  have ht : noC (u++[Slot.B,Slot.A,Slot.A]) := by simpa using hu
  have hA : count .A s=count .A (u++[Slot.B,Slot.A,Slot.A]) := by simp [u]; omega
  have hB : count .B s=count .B (u++[Slot.B,Slot.A,Slot.A]) := by simp [u]; omega
  rw [coefficient_eq_counts hp he hs ht hA hB]
  exact triple_zero hp he u hu


-- @@ L732-745 verbatim
theorem residual_zero {p : A K Slot} {m r : ℕ}
    (hp : p∈space (fun w => noC w.toList))
    (hm : p∈homogeneous aCount m) (hr : p∈homogeneous bCount r)
    (hm2 : 2 ≤ m) (hr1 : 1 ≤ r) (he : deriv low (p+tau0 p)=0) : p=0 := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  by_contra hn
  have hw : p.coeff w≠0 := hn
  have h1 := mem_space_iff.mp hp w hw
  have h2 := mem_space_iff.mp hm w hw
  have h3 := mem_space_iff.mp hr w hw
  exact hw (coefficient_zero_two_As hp he w.toList h1 (by unfold count; rw [FreeMonoid.ofList_toList]; change 2 ≤ degree aCount w; omega)
    (by unfold count; rw [FreeMonoid.ofList_toList]; change 1 ≤ degree bCount w; omega))


-- @@ L747-770 verbatim
theorem lie_palindrome_zero (q : FreeLieAlgebra K Slot) (s : List Slot)
    (hs : s.reverse=s) (hlen : s.length≠1) : coeff (embed q) s=0 := by
  induction q using freeLie_induction with
  | h0 => simp
  | hg a =>
    rw [embed_of]
    change coeff (monomial [a]) s=0
    rw [coeff_monomial,ite_eq_right]
    intro h
    exact hlen (h ▸ rfl)
  | ha p q hp hq => simp only [map_add,coeff_add,hp,hq,add_zero]
  | hs c p hp => simp only [map_smul,coeff_smul,hp,mul_zero]
  | hl p q _ _ =>
    rw [LieHom.map_lie]
    change coeff (embed p*embed q-embed q*embed p) s=0
    have h : coeff (embed p*embed q) s=coeff (embed q*embed p) s := by
      have hr := WordReversal.rev_coeff (embed p*embed q) (FreeMonoid.ofList s)
      rw [WordReversal.rev_mul,WordReversal.rev_lie_charTwo,WordReversal.rev_lie_charTwo] at hr
      have hs' : (FreeMonoid.ofList s).reverse=FreeMonoid.ofList s := by
        exact congrArg FreeMonoid.ofList hs
      rw [hs'] at hr
      exact hr.symm
    change coeff (embed p*embed q) s-coeff (embed q*embed p) s=0
    exact sub_eq_zero.mpr h


-- @@ L772-772 verbatim
end ResidualKernel


-- @@ L774-774 verbatim
namespace LetterRetraction

-- @@ L775-775 verbatim
open AssociativeElimination WordGrading

-- @@ L776-776 verbatim
attribute [local instance] LieRing.ofAssociativeRing

-- @@ L777-777 verbatim
variable {R α : Type*} [CommRing R]

-- @@ L778-778 verbatim
variable (P : α → Prop) [DecidablePred P]


-- @@ L780-801 verbatim
omit [DecidablePred P] in
theorem support_of_mem {q : FreeLieAlgebra R α} (hq : q∈sub P) :
    embed q∈space (fun w => ∀ a∈w.toList,P a) := by
  have hm {p q : A R α}
      (hp : p∈space (fun w => ∀ a∈w.toList,P a))
      (hq : q∈space (fun w => ∀ a∈w.toList,P a)) :
      p*q∈space (fun w => ∀ a∈w.toList,P a) := by
    apply mul_mem ?_ hp hq
    intro u v hu hv a ha
    simp only [FreeMonoid.toList_mul,List.mem_append] at ha
    exact ha.elim (hu a) (hv a)
  induction hq using LieSubalgebra.lieSpan_induction with
  | mem q hq =>
    obtain ⟨a,ha,rfl⟩ := hq
    rw [embed_of]
    exact word_mem _ (by simpa using ha)
  | zero => simp
  | add p q _ _ hp hq => simpa only [map_add] using (space _).add_mem hp hq
  | smul c p _ hp => simpa only [map_smul] using (space _).smul_mem c hp
  | lie p q _ _ hp hq =>
    rw [LieHom.map_lie]
    exact (space _).sub_mem (hm hp hq) (hm hq hp)


-- @@ L803-821 verbatim
theorem single_letter (a : α) (q : FreeLieAlgebra R α) [DecidableEq α] :
    ∃ c : R,lie (fun b => b=a) q=c • FreeLieAlgebra.of R a := by
  induction q using freeLie_induction with
  | h0 => exact ⟨0,by simp⟩
  | hg b =>
    by_cases h : b=a
    · subst b; exact ⟨1,by simp⟩
    · exact ⟨0,by simp [h]⟩
  | ha p q hp hq =>
    obtain ⟨c,hc⟩ := hp
    obtain ⟨d,hd⟩ := hq
    exact ⟨c+d,by rw [map_add,hc,hd,add_smul]⟩
  | hs r p hp =>
    obtain ⟨c,hc⟩ := hp
    exact ⟨r*c,by rw [map_smul,hc,mul_smul]⟩
  | hl p q hp hq =>
    obtain ⟨c,hc⟩ := hp
    obtain ⟨d,hd⟩ := hq
    exact ⟨0,by simp only [LieHom.map_lie,hc,hd,lie_smul,smul_lie,lie_self,smul_zero,zero_smul]⟩


-- @@ L823-838 verbatim
theorem homogeneous_single_zero [DecidableEq α] (a : α) {q : FreeLieAlgebra R α}
    {wt : α → ℕ} {n : ℕ} (hn : n≠wt a)
    (hq : embed q∈space (fun w => ∀ b∈w.toList,b=a))
    (hw : embed q∈homogeneous wt n) : q=0 := by
  obtain ⟨c,hc⟩ := single_letter a q
  rw [lie_eq_self (fun b => b=a) hq] at hc
  have hdeg : embed q∈homogeneous wt (wt a) := by
    rw [hc,map_smul,embed_of]
    exact (homogeneous wt (wt a)).smul_mem c (word_mem _ (degree_of wt a))
  apply UniversalEmbedding.injective
  rw [map_zero]
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  by_contra h
  exact hn ((mem_space_iff.mp hw w h).symm.trans (mem_space_iff.mp hdeg w h))


-- @@ L840-840 verbatim
end LetterRetraction


-- @@ L842-842 verbatim
namespace ProjectionKernel

-- @@ L843-843 verbatim
open AssociativeElimination WordGrading RowTwo RowKernel ExactPentagon QuadraticLeading ResidualKernel

-- @@ L844-844 verbatim
attribute [local instance] LieRing.ofAssociativeRing

-- @@ L845-845 verbatim
abbrev K := ZMod 2


-- @@ L847-851 verbatim
theorem degree_congr_word {α : Type*} {f g : α → ℕ} (w : FreeMonoid α)
    (h : ∀ a∈w.toList,f a=g a) : degree f w=degree g w := by
  unfold degree
  congr 1
  exact List.map_congr_left h


-- @@ L853-857 verbatim
theorem degree_scale {α : Type*} (f : α → ℕ) (c : ℕ) (w : FreeMonoid α) :
    degree (fun a => c*f a) w=c*degree f w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih => simp only [degree_mul,degree_of,ih,mul_add]


-- @@ L859-866 verbatim
theorem ac_zero (w : FreeMonoid Slot) (hw : degree acCount w=0) :
    ∀ a∈w.toList,a=Slot.B := by
  have he : acCount=(fun a : Slot => if a≠Slot.B then 1 else 0) := by funext a; cases a <;> rfl
  rw [he] at hw
  have h := (degree_indicator_zero (fun a : Slot => a≠Slot.B) w.toList).mp
    (by simpa using hw)
  intro a ha
  exact not_ne_iff.mp (h a ha)


-- @@ L868-871 verbatim
theorem b_zero (w : FreeMonoid Slot) (hw : degree bCount w=0) :
    ∀ a∈w.toList,a≠Slot.B := by
  exact (degree_indicator_zero (fun a : Slot => a=Slot.B) w.toList).mp
    (by rw [FreeMonoid.ofList_toList]; exact hw)


-- @@ L873-878 verbatim
theorem a_from_ac_noC (w : FreeMonoid Slot) (hw : noC w.toList) :
    degree aCount w=degree acCount w := by
  apply degree_congr_word
  intro a ha
  have hn := hw a ha
  cases a <;> simp_all [aCount,acCount,cCount]


-- @@ L880-893 verbatim
theorem higher_single_B {p q : FreeLieAlgebra K Slot} {n r : ℕ}
    (hn : n=r+2) (hn2 : 2<n)
    (hp : embed p∈homogeneous weight n) (hq : embed q∈homogeneous weight n)
    (hh : embed p-embed q∈above bCount (r+1)) : p=q := by
  have hw : embed (p-q)∈homogeneous weight n := by
    simpa only [map_sub] using (homogeneous weight n).sub_mem hp hq
  have hs : embed (p-q)∈space (fun w => ∀ a∈w.toList,a=Slot.B) := by
    apply mem_space
    intro w hc
    have h1 := mem_space_iff.mp hw w hc
    have h2 := mem_space_iff.mp hh w (by simpa using hc)
    have h3 := weight_count w
    exact ac_zero w (by omega)
  exact sub_eq_zero.mp (LetterRetraction.homogeneous_single_zero Slot.B (by simpa only [weight] using (by omega : n≠1)) hs hw)


-- @@ L895-895 verbatim
def yWeight (b : Bool) : ℕ := if b then 1 else 0

-- @@ L896-896 verbatim
def xSlot : Slot → ℕ | .A => 2 | .C => 1 | .B => 0

-- @@ L897-897 verbatim
def ySlot : Slot → ℕ | .A => 0 | .C => 1 | .B => 1


-- @@ L899-899 verbatim
def swap : A K Bool →ₐ[K] A K Bool := algEval (atom true) (atom false)


-- @@ L901-902 verbatim
@[simp] theorem swap_atom (b : Bool) : swap (atom b)=atom (!b) := by
  cases b <;> simp [swap,algEval]


-- @@ L904-917 verbatim
theorem quad_y (a : Slot) : quad (atom a)∈homogeneous yWeight (ySlot a) := by
  have hx : (atom false : A K Bool)∈homogeneous yWeight 0 := word_mem _ rfl
  have hy : (atom true : A K Bool)∈homogeneous yWeight 1 := word_mem _ rfl
  cases a with
  | A =>
    rw [quad,lift_atom]
    have h := homogeneous_mul hx hx
    exact h
  | C =>
    rw [quad,lift_atom]
    have h1 := homogeneous_mul hx hy
    have h2 := homogeneous_mul hy hx
    exact (homogeneous yWeight 1).sub_mem h1 h2
  | B => simpa only [quad,lift_atom,ySlot] using hy


-- @@ L919-932 verbatim
theorem swap_quad_y (a : Slot) : swap (quad (atom a))∈homogeneous yWeight (xSlot a) := by
  have hx : (atom false : A K Bool)∈homogeneous yWeight 0 := word_mem _ rfl
  have hy : (atom true : A K Bool)∈homogeneous yWeight 1 := word_mem _ rfl
  cases a with
  | A =>
    simp only [quad,lift_atom,map_mul,swap_atom]
    have h := homogeneous_mul hy hy
    exact h
  | C =>
    simp only [quad,lift_atom,map_sub,map_mul,swap_atom]
    have h1 := homogeneous_mul hy hx
    have h2 := homogeneous_mul hx hy
    exact (homogeneous yWeight 1).sub_mem h1 h2
  | B => simpa only [quad,lift_atom,swap_atom,xSlot,Bool.not_true] using hx


-- @@ L934-972 verbatim
theorem symmetry_r_two {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot} {r : ℕ}
    (hp : under p=embed ψ) (hn : p≠0)
    (hs : embed p∈space (fun w => noC w.toList))
    (ha : embed p∈homogeneous acCount 1) (hb : embed p∈homogeneous bCount r)
    (hanti : BaseChangeEquations.antisymmetry ψ=0) : r=2 := by
  have hY : embed p∈homogeneous ySlot r := by
    apply mem_space
    intro w hw
    rw [degree_congr_word w (g:=bCount) ?_]
    · exact mem_space_iff.mp hb w hw
    · intro a ha
      have h := (mem_space_iff.mp hs w hw) a ha
      cases a <;> simp_all [ySlot,bCount]
  have hX : embed p∈homogeneous xSlot 2 := by
    apply mem_space
    intro w hw
    rw [degree_congr_word w (g:=fun a => 2*acCount a) ?_,degree_scale]
    · rw [mem_space_iff.mp ha w hw]
    · intro a ha
      have h := (mem_space_iff.mp hs w hw) a ha
      cases a <;> simp_all [xSlot,acCount,aCount,cCount]
  have h1 := algHom_homogeneous quad ySlot yWeight quad_y hY
  have h2 := algHom_homogeneous (swap.comp quad) xSlot yWeight swap_quad_y hX
  have he : swap (under p)=under p := by
    rw [hp]
    change ψ+BaseChangeEquations.eval BaseChangeEquations.y BaseChangeEquations.x ψ=0 at hanti
    have h := congrArg embed ((TwoModule.eq_of_add_zero hanti).symm)
    simpa only [ResidualKernel.embed_eval,BaseChangeEquations.x,BaseChangeEquations.y,embed_of,swap] using h
  change swap (under p)∈_ at h2
  rw [he] at h2
  by_contra hne
  apply hn
  apply under_injective
  rw [map_zero]
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  by_contra hw
  exact hne ((mem_space_iff.mp h1 w hw).symm.trans (mem_space_iff.mp h2 w hw))


-- @@ L974-998 verbatim
theorem one_A_two_B_zero {p : FreeLieAlgebra K Slot}
    (hs : embed p∈space (fun w => noC w.toList))
    (ha : embed p∈homogeneous acCount 1) (hb : embed p∈homogeneous bCount 2)
    (he : deriv low (embed p+tau0 (embed p))=0) : p=0 := by
  apply UniversalEmbedding.injective
  rw [map_zero]
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  by_contra hw
  have hno := mem_space_iff.mp hs w hw
  have hA : count .A w.toList=1 := by
    unfold count
    rw [FreeMonoid.ofList_toList]
    change degree aCount w=1
    rw [a_from_ac_noC w hno]
    exact mem_space_iff.mp ha w hw
  have hB : count .B w.toList=2 := by
    unfold count
    rw [FreeMonoid.ofList_toList]
    exact mem_space_iff.mp hb w hw
  have hc := coefficient_eq_counts hs he hno (t:=[Slot.B,Slot.A,Slot.B]) (by simp)
    (by simpa using hA) (by simpa using hB)
  have hz := lie_palindrome_zero p [Slot.B,Slot.A,Slot.B] (by rfl) (by decide)
  exact hw (hc.trans hz)


-- @@ L1000-1065 verbatim
theorem leading_projection_kernel {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot}
    {n r : ℕ} (hn : 2<n) (hp : under p=embed ψ)
    (hw : embed p∈homogeneous weight n) (hfilter : embed p∈above bCount r)
    (hanti : BaseChangeEquations.antisymmetry ψ=0)
    (hspecial : BaseChangeEquations.special ψ=0)
    (hpent : BaseChangeEquations.pentagon ψ=0)
    (hzero : LetterRetraction.lie (fun a => a≠Slot.A) (LieGrading.piece bCount r p)=0) :
    LieGrading.piece bCount r p=0 := by
  let q := LieGrading.piece bCount r p
  have hq : embed q=WordGrading.piece bCount r (embed p) := LieGrading.embed_piece _ _ _
  have hqw : embed q∈homogeneous weight n := by rw [hq]; exact project_preserves hw
  have hqb : embed q∈homogeneous bCount r := by rw [hq]; exact piece_mem _ _ _
  have hh : embed p-embed q∈above bCount (r+1) := by rw [hq]; exact subtract_piece_above hfilter
  change q=0
  by_contra hqne
  have hen : embed q≠0 := by intro hz; exact hqne (UniversalEmbedding.injective (hz.trans (map_zero _).symm))
  have hex : ∃ w,(embed q).coeff w≠0 := by
    by_contra h
    push Not at h
    exact hen (MonoidAlgebra.ext (Finsupp.ext h))
  obtain ⟨w,hwne⟩ := hex
  let m := degree acCount w
  have hnr : n=2*m+r := by
    have h1 := mem_space_iff.mp hqw w hwne
    have h2 := mem_space_iff.mp hqb w hwne
    have h3 := weight_count w
    omega
  have hqa : embed q∈homogeneous acCount m := leading_ac hqw hqb hnr
  have hm : 0 < m := by
    by_contra hm
    have hm0 : m=0 := by omega
    have hs : embed q∈space (fun w => ∀ a∈w.toList,a=Slot.B) := by
      apply space_mono ?_ hqa
      intro v hv
      exact ac_zero v (hv.trans hm0)
    exact hqne (LetterRetraction.homogeneous_single_zero Slot.B (by change n≠1; omega) hs hqw)
  have hrn : r < n := by omega
  have hno : embed q∈space (fun w => noC w.toList) :=
    LetterRetraction.support_of_mem (fun a => a≠Slot.C)
      (leading_no_C hp hw hrn hfilter hpent hnr hzero)
  have hr : 0 < r := by
    by_contra hr
    have hr0 : r=0 := by omega
    have hs : embed q∈space (fun w => ∀ a∈w.toList,a=Slot.A) := by
      apply mem_space
      intro v hv a hav
      have hb := b_zero v ((mem_space_iff.mp hqb v hv).trans hr0) a hav
      have hc := (mem_space_iff.mp hno v hv) a hav
      cases a <;> simp_all
    exact hqne (LetterRetraction.homogeneous_single_zero Slot.A (by change n≠2; omega) hs hqw)
  have he := leading_equation hr hqb hh (full_equation hp hanti hspecial)
  by_cases hm2 : 2 ≤ m
  · have ha : embed q∈homogeneous aCount m := by
      apply mem_space
      intro v hv
      rw [a_from_ac_noC v (mem_space_iff.mp hno v hv)]
      exact mem_space_iff.mp hqa v hv
    exact hen (residual_zero hno ha hqb hm2 hr he)
  · have hm1 : m=1 := by omega
    have hn2 : n=r+2 := by omega
    have hpq := higher_single_B hn2 hn hw hqw hh
    have hqψ : under q=embed ψ := by rw [← hpq]; exact hp
    have hqa1 : embed q∈homogeneous acCount 1 := by simpa only [hm1] using hqa
    have hr2 := symmetry_r_two hqψ hqne hno hqa1 hqb hanti
    have hqb2 : embed q∈homogeneous bCount 2 := by simpa only [hr2] using hqb
    exact hqne (one_A_two_B_zero hno hqa1 hqb2 he)


-- @@ L1067-1067 verbatim
end ProjectionKernel


-- @@ L1069-1069 verbatim
namespace WordGrading

-- @@ L1070-1070 verbatim
open AssociativeElimination

-- @@ L1071-1071 verbatim
variable {R α β : Type*} [CommRing R]


-- @@ L1073-1080 verbatim
theorem above_reflect (f : A R α →ₐ[R] A R β) (wa : α → ℕ) (wb : β → ℕ)
    (hf : ∀ a,f (atom a)∈homogeneous wb (wa a)) (hi : Function.Injective f)
    {n : ℕ} {p : A R α} (hp : f p∈above wb n) : p∈above wa n := by
  have h1 := algHom_project f wa wb hf (fun k => n≤k) p
  rw [project_eq_self hp] at h1
  have h2 := hi h1
  rw [← h2]
  exact project_mem _ _


-- @@ L1082-1082 verbatim
end WordGrading

-- @@ L1083-1083 verbatim
namespace EliminationGraded

-- @@ L1084-1084 verbatim
open AssociativeElimination UniversalEmbedding WordGrading

-- @@ L1085-1085 verbatim
attribute [local instance] LieRing.ofAssociativeRing

-- @@ L1086-1086 verbatim
variable {R α : Type*} [CommRing R]


-- @@ L1088-1089 verbatim
def collapse : A R (ℕ×α) →ₐ[R] A R (Option α) :=
  lift (fun (n,a) => embed (Elimination.adWord n a))


-- @@ L1091-1092 verbatim
@[simp] theorem collapse_atom (n : ℕ) (a : α) :
    collapse (atom (n,a) : A R (ℕ×α))=embed (Elimination.adWord n a) := by simp [collapse]


-- @@ L1094-1100 verbatim
theorem collapse_embed (p : Elimination.F R α) :
    collapse (embed p)=embed (Elimination.collapseFiber p) := by
  have h : collapse.toLieHom.comp embed=(embed : Elimination.G R α →ₗ⁅R⁆ A R (Option α)).comp Elimination.collapseFiber := by
    apply FreeLieAlgebra.hom_ext
    rintro ⟨n,a⟩
    simp [Elimination.collapseFiber]
  exact LieHom.congr_fun h p


-- @@ L1102-1108 verbatim
theorem operator_collapse (p : A R (ℕ×α)) : operator (collapse p)=leftMul p := by
  have h : operator.comp collapse=(leftMul : A R (ℕ×α) →ₐ[R] Module.End R (A R (ℕ×α))) := by
    apply hom_ext
    rintro ⟨n,a⟩
    simp only [AlgHom.comp_apply,collapse_atom,operator_embed,Elimination.expand_adWord,representation_inl]
    simp [Elimination.E]
  exact AlgHom.congr_fun h p


-- @@ L1110-1112 verbatim
theorem extract_collapse (p : A R (ℕ×α)) : extract (collapse p)=p := by
  change operator (collapse p) 1=p
  rw [operator_collapse,leftMul_apply,mul_one]


-- @@ L1114-1115 verbatim
theorem collapse_injective : Function.Injective (collapse : A R (ℕ×α) →ₐ[R] A R (Option α)) :=
  Function.LeftInverse.injective extract_collapse


-- @@ L1117-1134 verbatim
theorem adWord_degree (n : ℕ) (a : α) (wt : Option α → ℕ) :
    embed (Elimination.adWord n a : Elimination.G R α)∈homogeneous wt (n*wt none+wt (some a)) := by
  induction n with
  | zero =>
    simp only [Elimination.adWord_zero,Elimination.Y,embed_of,zero_mul,zero_add]
    exact word_mem _ rfl
  | succ n ih =>
    rw [Elimination.adWord_succ,LieHom.map_lie]
    have hx : embed (Elimination.X : Elimination.G R α)∈homogeneous wt (wt none) := by
      rw [Elimination.X,embed_of]
      exact word_mem _ (degree_of wt _)
    have h1 := homogeneous_mul hx ih
    have h2 := homogeneous_mul ih hx
    change embed Elimination.X*embed (Elimination.adWord n a)-embed (Elimination.adWord n a)*embed Elimination.X∈_
    have he : wt none+(n*wt none+wt (some a))=(n+1)*wt none+wt (some a) := by
      simp only [Nat.add_mul,one_mul]; omega
    rw [← he]
    exact (homogeneous wt _).sub_mem h1 (by simpa only [Nat.add_comm] using h2)


-- @@ L1136-1141 verbatim
theorem embed_decompose (p : Elimination.G R α) :
    embed p=collapse (embed (Elimination.expand p).left)+(Elimination.expand p).right • atom none := by
  rw [collapse_embed]
  have hx : atom none=embed (Elimination.X : Elimination.G R α) := (embed_of none).symm
  rw [hx,← map_smul,← map_add]
  exact congrArg embed (Elimination.collapse_expand p).symm


-- @@ L1143-1159 verbatim
theorem trace_homogeneous_zero {p : Elimination.G R α} {wt : Option α → ℕ} {n : ℕ}
    (hn : n≠wt none) (hp : embed p∈homogeneous wt n) : (Elimination.expand p).right=0 := by
  have hL : p∈LieGrading.homogeneousLie wt n := LieGrading.homogeneous_iff.mpr hp
  clear hp
  change p∈Submodule.span R {p | ∃ t : UniversalEmbedding.Tree (Option α),LieGrading.treeDegree wt t=n ∧ t.eval=p} at hL
  induction hL using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t,ht,rfl⟩ := hp
    cases t with
    | leaf a =>
      cases a with
      | none => exact (hn (ht.symm)).elim
      | some a => simp [Tree.eval,Elimination.expand]
    | node t u => simp [Tree.eval,LieHom.map_lie,Ring.lie_def,mul_comm]
  | zero => simp
  | add p q _ _ hp hq => simp [hp,hq]
  | smul c p _ hp => simp [hp]


-- @@ L1161-1161 verbatim
end EliminationGraded


-- @@ L1163-1163 verbatim
namespace OreShift


-- @@ L1165-1165 verbatim
section

-- @@ L1166-1166 verbatim
open AssociativeElimination WordGrading

-- @@ L1167-1167 verbatim
attribute [local instance] LieRing.ofAssociativeRing

-- @@ L1168-1168 verbatim
variable {R : Type*} [CommRing R]

-- @@ L1169-1173 verbatim
local instance {α : Type*} [CharP R 2] : CharP (A R α) 2 :=
  charP_of_injective_ringHom (show Function.Injective (algebraMap R (A R α)) from by
    intro r s h
    have hc := congrArg (fun p : A R α => p.coeff 1) h
    simpa using hc) 2

-- @@ L1174-1174 verbatim
abbrev S (R : Type*) [CommRing R] := A R Bool


-- @@ L1176-1176 verbatim
def C : S R := atom false

-- @@ L1177-1177 verbatim
def B : S R := atom true

-- @@ L1178-1178 verbatim
def wt (b : Bool) : ℕ := if b then 1 else 0


-- @@ L1180-1180 verbatim
def D : S R →ₗ[R] S R := deriv (fun b => if b then C else 0)

-- @@ L1181-1181 verbatim
@[simp] theorem D_C : D (C : S R)=0 := by simp [D,C]

-- @@ L1182-1182 verbatim
@[simp] theorem D_B : D (B : S R)=C := by simp [D,B]

-- @@ L1183-1183 verbatim
@[simp] theorem D_one : D (1 : S R)=0 := deriv_one _

-- @@ L1184-1184 verbatim
theorem D_mul (p q : S R) : D (p*q)=D p*q+p*D q := deriv_mul _ _ _

-- @@ L1185-1185 verbatim
theorem D_lie (p q : S R) : D ⁅p,q⁆=⁅D p,q⁆+⁅p,D q⁆ := deriv_lie _ _ _


-- @@ L1187-1195 verbatim
theorem D_square [CharP R 2] (p : S R) : D (D p)=0 := by
  induction p using QuadraticAlphabet.algebra_induction with
  | h1 => simp
  | ha b => cases b <;> simp [D,C]
  | hadd p q hp hq => simp [hp,hq]
  | hs c p hp => simp [hp]
  | hm p q hp hq =>
    rw [D_mul,map_add,D_mul,D_mul,hp,hq]
    simp only [zero_mul,mul_zero,zero_add,add_zero,CharTwo.add_self_eq_zero]


-- @@ L1197-1198 verbatim
theorem above_zero (p : S R) : p∈above wt 0 := by
  exact mem_space (by intro w _; exact Nat.zero_le _)

-- @@ L1199-1202 verbatim
theorem above_lie {a b : ℕ} {p q : S R} (hp : p∈above wt a) (hq : q∈above wt b) :
    ⁅p,q⁆∈above wt (a+b) := by
  change p*q-q*p∈_
  exact (above wt _).sub_mem (above_mul hp hq) (by simpa only [Nat.add_comm] using above_mul hq hp)


-- @@ L1204-1206 verbatim
def P (s : S R) : ℕ → S R
  | 0 => C
  | n+1 => ⁅B+s,P s n⁆


-- @@ L1208-1208 verbatim
@[simp] theorem P_zero (s : S R) : P s 0=C := rfl

-- @@ L1209-1209 verbatim
@[simp] theorem P_succ (s : S R) (n : ℕ) : P s (n+1)=⁅B+s,P s n⁆ := rfl


-- @@ L1211-1211 verbatim
variable {s : S R}


-- @@ L1213-1213 verbatim
@[simp] theorem D_F (hs : D s=0) : D (B+s)=C := by rw [map_add,D_B,hs,add_zero]


-- @@ L1215-1218 verbatim
theorem P_one (hc : ⁅(C : S R),s⁆=0) : P s 1=⁅(B : S R),C⁆ := by
  rw [P_succ,P_zero,add_lie]
  have hsc : ⁅s,(C : S R)⁆=0 := by rw [←lie_skew,hc,neg_zero]
  rw [hsc,add_zero]


-- @@ L1220-1230 verbatim
theorem P_above (hc : ⁅(C : S R),s⁆=0) (n : ℕ) : P s (n+1)∈above wt 1 := by
  induction n with
  | zero =>
    rw [P_one hc]
    have hb : (B : S R)∈above wt 1 := word_mem _ (by simp [degree_of,wt])
    have hh := above_lie hb (above_zero (C : S R))
    simpa only [Nat.add_zero] using hh
  | succ n ih =>
    rw [P_succ]
    have h := above_lie (above_zero (B+s)) ih
    exact h


-- @@ L1232-1232 verbatim
theorem DP_one (hc : ⁅(C : S R),s⁆=0) : D (P s 1)=0 := by rw [P_one hc,D_lie,D_B,D_C,lie_self,lie_zero,add_zero]


-- @@ L1234-1244 verbatim
theorem DP_above (hs : D s=0) (hc : ⁅(C : S R),s⁆=0) (n : ℕ) : D (P s n)∈above wt 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    cases n with
    | zero => rw [DP_one hc]; exact (above wt 1).zero_mem
    | succ n =>
      rw [P_succ,D_lie,D_F hs]
      have h1 := above_lie (above_zero (C : S R)) (P_above hc n)
      have h2 := above_lie (above_zero (B+s)) ih
      exact (above wt 1).add_mem h1 h2


-- @@ L1246-1256 verbatim
theorem D_lie_square [CharP R 2] (hs : D s=0) (p : S R) : D ⁅B+s,⁅B+s,p⁆⁆=⁅⁅(C : S R),B+s⁆,p⁆+⁅B+s,⁅B+s,D p⁆⁆ := by
  rw [D_lie,D_lie,D_F hs,lie_add]
  have he := leibniz_lie (B+s) (C : S R) p
  have hsk : ⁅B+s,C⁆=⁅(C : S R),B+s⁆ := by rw [←lie_skew,CharTwo.neg_eq]
  rw [hsk] at he
  rw [he]
  have hz : ⁅(C : S R),⁅B+s,p⁆⁆+⁅(C : S R),⁅B+s,p⁆⁆=0 := CharTwo.add_self_eq_zero _
  calc
    _ = ⁅⁅(C : S R),B+s⁆,p⁆+⁅B+s,⁅B+s,D p⁆⁆+
        (⁅(C : S R),⁅B+s,p⁆⁆+⁅(C : S R),⁅B+s,p⁆⁆) := by abel
    _ = _ := by rw [hz,add_zero]


-- @@ L1258-1269 verbatim
theorem DP_even [CharP R 2] (hs : D s=0) (hc : ⁅(C : S R),s⁆=0) (n : ℕ) : D (P s (2*n+1))∈above wt 2 := by
  induction n with
  | zero => rw [Nat.mul_zero,Nat.zero_add,DP_one hc]; exact (above wt 2).zero_mem
  | succ n ih =>
    have hn : 2*(n+1)+1=(2*n+1)+1+1 := by omega
    rw [hn,P_succ,P_succ,D_lie_square hs]
    have hcb : ⁅(C : S R),B+s⁆=⁅(C : S R),B⁆ := by rw [lie_add,hc,add_zero]
    rw [hcb]
    have hB : (B : S R)∈above wt 1 := word_mem _ (by simp [degree_of,wt])
    have h1 := above_lie (above_lie (above_zero (C : S R)) hB) (P_above hc (2*n))
    have h2 := above_lie (above_zero (B+s)) (above_lie (above_zero (B+s)) ih)
    exact (above wt 2).add_mem h1 h2


-- @@ L1271-1271 verbatim
end


-- @@ L1273-1273 verbatim
open AssociativeElimination WordGrading

-- @@ L1274-1274 verbatim
attribute [local instance] LieRing.ofAssociativeRing

-- @@ L1275-1275 verbatim
variable {R : Type*} [CommRing R]


-- @@ L1277-1277 verbatim
def indexWt (a : ℕ×Unit) : ℕ := if a.1%2=0 then 1 else 0


-- @@ L1279-1281 verbatim
def factor (s : S R) : ℕ → Module.End R (S R)
  | 0 => D
  | n+1 => leftMul (P s n)


-- @@ L1283-1283 verbatim
def operators (s : S R) : A R (ℕ×Unit) →ₐ[R] Module.End R (S R) := lift (fun a => factor s a.1)

-- @@ L1284-1285 verbatim
def constant (s : S R) : A R (ℕ×Unit) →ₗ[R] S R :=
  (LinearMap.applyₗ 1).comp (operators s).toLinearMap


-- @@ L1287-1287 verbatim
@[simp] theorem constant_one (s : S R) : constant s 1=1 := by simp [constant]

-- @@ L1288-1290 verbatim
@[simp] theorem constant_atom_mul (s : S R) (n : ℕ) (p : A R (ℕ×Unit)) :
    constant s (atom (n,())*p)=factor s n (constant s p) := by
  simp [constant,operators,Module.End.mul_apply]


-- @@ L1292-1292 verbatim
variable {s : S R} [CharP R 2]

-- @@ L1293-1305 verbatim
theorem factor_bounds (hs : D s=0) (hc : ⁅(C : S R),s⁆=0) (n : ℕ) :
    P s n∈above wt (indexWt (n+1,())) ∧
    D (P s n)∈above wt (indexWt (n+1,())+1) := by
  by_cases he : (n+1)%2=0
  · have hn : n=n/2*2+1 := by omega
    have hP := P_above hc (n/2*2)
    have hD := DP_even hs hc (n/2)
    have hn' : n=2*(n/2)+1 := by omega
    constructor
    · simpa only [←hn,indexWt,ite_eq_left he] using hP
    · simpa only [←hn',indexWt,ite_eq_left he] using hD
  · simp only [indexWt,ite_eq_right he,zero_add]
    exact ⟨above_zero _,DP_above hs hc n⟩


-- @@ L1307-1335 verbatim
theorem word_bound (hs : D s=0) (hc : ⁅(C : S R),s⁆=0) (w : FreeMonoid (ℕ×Unit)) :
    constant s (word w)∈above wt (degree indexWt w) ∧
    D (constant s (word w))∈above wt (degree indexWt w+1) := by
  induction w using FreeMonoid.inductionOn' with
  | one =>
    simp only [word_one,constant_one,D_one,degree_one,Nat.zero_add]
    exact ⟨above_zero _,(above wt 1).zero_mem⟩
  | of_mul a w ih =>
    obtain ⟨n,u⟩ := a
    cases u
    rw [word_mul,word_of,constant_atom_mul,degree_mul,degree_of]
    cases n with
    | zero =>
      change D (constant s (word w))∈above wt (1+degree indexWt w) ∧
        D (D (constant s (word w)))∈above wt (1+degree indexWt w+1)
      constructor
      · simpa only [Nat.add_comm] using ih.2
      · rw [D_square]; exact (above wt _).zero_mem
    | succ n =>
      simp only [factor,leftMul_apply]
      obtain ⟨hp,hd⟩ := factor_bounds hs hc n
      constructor
      · exact above_mul hp ih.1
      · rw [D_mul]
        have h1 := above_mul hd ih.1
        have h2 := above_mul hp ih.2
        apply (above wt (indexWt (n+1,())+degree indexWt w+1)).add_mem
        · simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h1
        · simpa only [Nat.add_assoc] using h2


-- @@ L1337-1341 verbatim
theorem constant_bound (hs : D s=0) (hc : ⁅(C : S R),s⁆=0) {r : ℕ} {p : A R (ℕ×Unit)}
    (hp : p∈above indexWt r) : constant s p∈above wt r := by
  apply map_space (constant s) _ ?_ hp
  intro w hw
  exact space_mono (by intro v hv; exact hw.trans hv) (word_bound hs hc w).1


-- @@ L1343-1343 verbatim
end OreShift


-- @@ L1345-1345 verbatim
namespace EvenIndex


-- @@ L1347-1347 verbatim
section

-- @@ L1348-1348 verbatim
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading

-- @@ L1349-1349 verbatim
open RowTwo RowKernel ExactPentagon AlphabetTransport

-- @@ L1350-1350 verbatim
attribute [local instance] LieRing.ofAssociativeRing

-- @@ L1351-1351 verbatim
abbrev K := ZMod 2


-- @@ L1353-1354 verbatim
theorem map_lie {R α β : Type*} [CommRing R] (f : A R α →ₐ[R] A R β) (p q : A R α) :
    f ⁅p,q⁆=⁅f p,f q⁆ := by simp only [Ring.lie_def,map_sub,map_mul]


-- @@ L1356-1360 verbatim
def abc : Option Bool ≃ Slot where
  toFun := fun | none => .A | some false => .B | some true => .C
  invFun := fun | .A => none | .B => some false | .C => some true
  left_inv a := by cases a with | none => rfl | some b => cases b <;> rfl
  right_inv a := by cases a <;> rfl


-- @@ L1362-1362 verbatim
def idx (a : ℕ×Unit) : ℕ×Bool := (a.1/2,decide (a.1%2=1))

-- @@ L1363-1363 verbatim
def unidx (a : ℕ×Bool) : ℕ×Unit := (2*a.1+if a.2 then 1 else 0,())


-- @@ L1365-1369 verbatim
theorem idx_left : Function.LeftInverse unidx idx := by
  rintro ⟨n,u⟩
  cases u
  dsimp [idx,unidx]
  split_ifs <;> simp_all only [decide_eq_true_eq] <;> congr <;> omega


-- @@ L1371-1372 verbatim
def intoABC : A K (ℕ×Unit) →ₐ[K] A K Slot :=
  (renameAssoc abc).comp (EliminationGraded.collapse.comp (renameAssoc idx))


-- @@ L1374-1376 verbatim
theorem intoABC_injective : Function.Injective intoABC := by
  exact (assoc_injective abc abc.symm abc.left_inv).comp
    (EliminationGraded.collapse_injective.comp (assoc_injective idx unidx idx_left))


-- @@ L1378-1380 verbatim
@[simp] theorem intoABC_atom (n : ℕ) : intoABC (atom (n,()))=
    renameAssoc abc (embed (Elimination.adWord (n/2) (decide (n%2=1)) : Elimination.G K Bool)) := by
  simp [intoABC,idx]


-- @@ L1382-1382 verbatim
def evenWt (a : ℕ×Unit) : ℕ := if a.1%2=0 then 1 else 0


-- @@ L1384-1400 verbatim
theorem intoABC_degree (a : ℕ×Unit) : intoABC (atom a)∈homogeneous bCount (evenWt a) := by
  obtain ⟨n,u⟩ := a
  cases u
  rw [intoABC_atom]
  have h := EliminationGraded.adWord_degree (R:=K) (n/2) (decide (n%2=1)) (bCount ∘ abc)
  have hg : ∀ a : Option Bool,renameAssoc (R:=K) abc (atom a)∈homogeneous bCount ((bCount ∘ abc) a) := by
    intro a
    rw [renameAssoc_atom]
    exact word_mem _ (degree_of _ _)
  have hh := algHom_homogeneous (renameAssoc abc) (bCount ∘ abc) bCount hg h
  have he : n/2*(bCount ∘ abc) none+(bCount ∘ abc) (some (decide (n%2=1)))=evenWt (n,()) := by
    simp only [Function.comp_apply,abc,bCount,evenWt]
    by_cases hn : n%2=1
    · simp [hn]
    · have hn0 : n%2=0 := by omega
      simp [hn0]
  exact he ▸ hh


-- @@ L1402-1403 verbatim
def input : A K (ℕ×Unit) →ₐ[K] A K Bool :=
  (renameAssoc bitOption.symm).comp EliminationGraded.collapse


-- @@ L1405-1407 verbatim
@[simp] theorem input_atom (n : ℕ) : input (atom (n,()))=
    renameAssoc bitOption.symm (embed (Elimination.adWord n () : Elimination.G K Unit)) := by
  simp [input]


-- @@ L1409-1410 verbatim
theorem intoABC_atom_zero : intoABC (atom (0,()))=atom Slot.B := by
  simp [intoABC_atom,Elimination.Y,abc]

-- @@ L1411-1412 verbatim
theorem intoABC_atom_one : intoABC (atom (1,()))=atom Slot.C := by
  simp [intoABC_atom,Elimination.Y,abc]

-- @@ L1413-1420 verbatim
theorem intoABC_atom_two (n : ℕ) : intoABC (atom (n+2,()))=⁅(atom Slot.A : A K Slot),intoABC (atom (n,()))⁆ := by
  have hd : (n+2)/2=n/2+1 := by omega
  have hm : (n+2)%2=n%2 := by omega
  rw [intoABC_atom,intoABC_atom,hd,hm]
  rw [Elimination.adWord_succ,LieHom.map_lie]
  change renameAssoc abc ⁅embed (Elimination.X : Elimination.G K Bool),_⁆=_
  rw [map_lie]
  simp [Elimination.X,abc]


-- @@ L1422-1423 verbatim
theorem input_atom_zero : input (atom (0,()))=atom true := by
  simp [input_atom,Elimination.Y,bitOption]

-- @@ L1424-1427 verbatim
theorem input_atom_succ (n : ℕ) : input (atom (n+1,()))=⁅(atom false : A K Bool),input (atom (n,()))⁆ := by
  rw [input_atom,input_atom,Elimination.adWord_succ,LieHom.map_lie]
  rw [map_lie]
  simp [Elimination.X,bitOption]


-- @@ L1429-1446 verbatim
theorem quad_intoABC : quad.comp intoABC=input := by
  apply hom_ext
  rintro ⟨n,u⟩
  cases u
  induction n using Nat.twoStepInduction with
  | zero => rw [AlgHom.comp_apply,intoABC_atom_zero,input_atom_zero]; simp only [quad,lift_atom]
  | one => rw [AlgHom.comp_apply,intoABC_atom_one,input_atom_succ,input_atom_zero]; simp only [quad,lift_atom,Ring.lie_def]
  | more n ih _ =>
    simp only [AlgHom.comp_apply] at ih ⊢
    rw [intoABC_atom_two,map_lie,ih,input_atom_succ,input_atom_succ]
    simp only [quad,lift_atom]
    change ⁅(atom false : A K Bool)*atom false,input (atom (n,()))⁆=⁅atom false,⁅atom false,_⁆⁆
    simp only [Ring.lie_def,sub_eq_add_neg,CharTwo.neg_eq,mul_add,add_mul,mul_assoc]
    symm
    calc
      _ = atom false*(atom false*input (atom (n,())))+input (atom (n,()))*(atom false*atom false)+
          (atom false*(input (atom (n,()))*atom false)+atom false*(input (atom (n,()))*atom false)) := by abel
      _ = _ := by rw [CharTwo.add_self_eq_zero,add_zero]


-- @@ L1448-1449 verbatim
def fiber (ψ : FreeLieAlgebra K Bool) : A K (ℕ×Unit) :=
  embed (Elimination.expand (rename bitOption ψ)).left


-- @@ L1451-1464 verbatim
theorem input_fiber {ψ : FreeLieAlgebra K Bool} {n : ℕ} (hn : 1 < n)
    (hψ : embed ψ∈homogeneous (fun _ => 1) n) : input (fiber ψ)=embed ψ := by
  have ho : embed (rename bitOption ψ)∈homogeneous (fun _ => 1) n := by
    rw [rename_embed]
    apply algHom_homogeneous (renameAssoc bitOption) (fun _ => 1) (fun _ => 1) ?_ hψ
    intro b
    rw [renameAssoc_atom]
    exact word_mem _ (degree_of _ _)
  have hz := EliminationGraded.trace_homogeneous_zero (by omega) ho
  have hd := EliminationGraded.embed_decompose (rename bitOption ψ)
  rw [hz,zero_smul,add_zero] at hd
  have h := congrArg (renameAssoc bitOption.symm) hd
  rw [rename_embed,assoc_retract bitOption bitOption.symm bitOption.left_inv] at h
  exact h.symm


-- @@ L1466-1473 verbatim
theorem intoABC_fiber {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot} {n : ℕ}
    (hn : 1 < n) (hψ : embed ψ∈homogeneous (fun _ => 1) n) (hp : under p=embed ψ) :
    intoABC (fiber ψ)=embed p := by
  apply quad_injective
  calc
    quad (intoABC (fiber ψ)) = input (fiber ψ) := AlgHom.congr_fun quad_intoABC _
    _ = embed ψ := input_fiber hn hψ
    _ = quad (embed p) := hp.symm


-- @@ L1475-1480 verbatim
theorem termwise_bound {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot} {n r : ℕ}
    (hn : 1 < n) (hψ : embed ψ∈homogeneous (fun _ => 1) n) (hp : under p=embed ψ)
    (hr : embed p∈above bCount r) : fiber ψ∈above evenWt r := by
  apply above_reflect intoABC evenWt bCount intoABC_degree intoABC_injective
  rw [intoABC_fiber hn hψ hp]
  exact hr


-- @@ L1482-1482 verbatim
end


-- @@ L1484-1484 verbatim
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading

-- @@ L1485-1485 verbatim
open RowTwo RowKernel ExactPentagon AlphabetTransport ProjectionKernel

-- @@ L1486-1486 verbatim
attribute [local instance] LieRing.ofAssociativeRing


-- @@ L1488-1488 verbatim
def xWeight (b : Bool) : ℕ := if b then 0 else 1

-- @@ L1489-1489 verbatim
def swappedInput : A K (ℕ×Unit) →ₐ[K] A K Bool := swap.comp input


-- @@ L1491-1506 verbatim
theorem swappedInput_degree (a : ℕ×Unit) :
    swappedInput (atom a)∈homogeneous xWeight 1 := by
  obtain ⟨n,u⟩ := a
  cases u
  induction n with
  | zero =>
    rw [swappedInput,AlgHom.comp_apply,input_atom_zero,swap_atom]
    exact word_mem _ rfl
  | succ n ih =>
    rw [swappedInput,AlgHom.comp_apply,input_atom_succ,map_lie,swap_atom]
    have hy : (atom true : A K Bool)∈homogeneous xWeight 0 := word_mem _ rfl
    change ⁅atom true,swappedInput (atom (n,()))⁆∈_
    change atom true*swappedInput (atom (n,()))-swappedInput (atom (n,()))*atom true∈_
    have h1 := homogeneous_mul hy ih
    have h2 := homogeneous_mul ih hy
    exact (homogeneous xWeight 1).sub_mem h1 h2


-- @@ L1508-1521 verbatim
theorem quad_x (a : Slot) : quad (atom a)∈homogeneous xWeight (xSlot a) := by
  have hx : (atom false : A K Bool)∈homogeneous xWeight 1 := word_mem _ rfl
  have hy : (atom true : A K Bool)∈homogeneous xWeight 0 := word_mem _ rfl
  cases a with
  | A =>
    rw [quad,lift_atom]
    have h := homogeneous_mul hx hx
    exact h
  | C =>
    rw [quad,lift_atom]
    have h1 := homogeneous_mul hx hy
    have h2 := homogeneous_mul hy hx
    exact (homogeneous xWeight 1).sub_mem h1 h2
  | B => simpa only [quad,lift_atom,xSlot] using hy


-- @@ L1523-1527 verbatim
theorem swapped_solution {ψ : FreeLieAlgebra K Bool}
    (hanti : BaseChangeEquations.antisymmetry ψ=0) : swap (embed ψ)=embed ψ := by
  change ψ+BaseChangeEquations.eval BaseChangeEquations.y BaseChangeEquations.x ψ=0 at hanti
  have h := congrArg embed ((TwoModule.eq_of_add_zero hanti).symm)
  simpa only [ResidualKernel.embed_eval,BaseChangeEquations.x,BaseChangeEquations.y,embed_of,swap] using h


-- @@ L1529-1537 verbatim
theorem selected_expression {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot} {n : ℕ}
    (hn : 1 < n) (hψ : embed ψ∈homogeneous (fun _ => 1) n) (hp : under p=embed ψ)
    (hanti : BaseChangeEquations.antisymmetry ψ=0) (m : ℕ) :
    swappedInput (piece (fun _ => 1) m (fiber ψ))=quad (piece xSlot m (embed p)) := by
  rw [algHom_piece swappedInput (fun _ => 1) xWeight swappedInput_degree]
  have he : swappedInput (fiber ψ)=quad (embed p) := by
    change swap (input (fiber ψ))=under p
    rw [input_fiber hn hψ,swapped_solution hanti,hp]
  rw [he,← algHom_piece quad xSlot xWeight quad_x]


-- @@ L1539-1539 verbatim
end EvenIndex


-- @@ L1541-1541 verbatim
namespace OreShift


-- @@ L1543-1543 verbatim
section

-- @@ L1544-1544 verbatim
open AssociativeElimination WordGrading

-- @@ L1545-1545 verbatim
open QuadraticLeading RowTwo RowKernel AlphabetTransport ProjectionKernel ExactPentagon

-- @@ L1546-1546 verbatim
attribute [local instance] LieRing.ofAssociativeRing

-- @@ L1547-1547 verbatim
variable {R : Type*} [CommRing R]

-- @@ L1548-1552 verbatim
local instance {α : Type*} [CharP R 2] : CharP (A R α) 2 :=
  charP_of_injective_ringHom (show Function.Injective (algebraMap R (A R α)) from by
    intro r s h
    have hc := congrArg (fun p : A R α => p.coeff 1) h
    simpa using hc) 2


-- @@ L1554-1555 verbatim
def evaluate (s : S R) : A R Bool →ₐ[R] Module.End R (S R) :=
  lift (fun b => if b then leftMul (B+s) else D)


-- @@ L1557-1557 verbatim
@[simp] theorem evaluate_x (s : S R) : evaluate s (atom false)=D := by simp [evaluate]

-- @@ L1558-1558 verbatim
@[simp] theorem evaluate_y (s : S R) : evaluate s (atom true)=leftMul (B+s) := by simp [evaluate]


-- @@ L1560-1561 verbatim
def eraseShift (s : S R) : A R Slot →ₐ[R] S R :=
  lift (fun | .A => 0 | .C => C | .B => B+s)


-- @@ L1563-1567 verbatim
theorem comm_D_left (p : S R) : ⁅(D : Module.End R (S R)),leftMul p⁆=leftMul (D p) := by
  apply LinearMap.ext
  intro q
  change D (p*q)-p*D q=D p*q
  rw [D_mul,add_sub_cancel_right]


-- @@ L1569-1571 verbatim
theorem left_comm_D [CharP R 2] {s : S R} (hs : D s=0) :
    ⁅leftMul (B+s),(D : Module.End R (S R))⁆=leftMul C := by
  rw [←lie_skew,comm_D_left,D_F hs,←map_neg,CharTwo.neg_eq]


-- @@ L1573-1588 verbatim
theorem evaluate_quad {s : S (ZMod 2)} (hs : D s=0) :
    (evaluate s).comp quad=leftMul.comp (eraseShift s) := by
  apply hom_ext
  intro a
  cases a with
  | A =>
    simp only [AlgHom.comp_apply,quad,lift_atom,map_mul,eraseShift,map_zero,evaluate_x]
    apply LinearMap.ext
    intro q
    change D (D q)=0
    exact D_square q
  | C =>
    simp only [AlgHom.comp_apply,quad,lift_atom,map_sub,map_mul,eraseShift,evaluate_x,evaluate_y]
    change ⁅(D : Module.End (ZMod 2) (S (ZMod 2))),leftMul (B+s)⁆=leftMul C
    rw [comm_D_left,D_F hs]
  | B => simp [quad,eraseShift,evaluate]


-- @@ L1590-1592 verbatim
theorem evaluate_lie (s : S R) (p q : A R Bool) :
    evaluate s ⁅p,q⁆=⁅evaluate s p,evaluate s q⁆ := by
  simp only [Ring.lie_def,map_sub,map_mul]


-- @@ L1594-1614 verbatim
theorem evaluate_swapped {s : S (ZMod 2)} (hs : D s=0) :
    (evaluate s).comp EvenIndex.swappedInput=operators s := by
  apply hom_ext
  rintro ⟨n,u⟩
  cases u
  simp only [AlgHom.comp_apply,operators,lift_atom]
  induction n with
  | zero =>
    rw [EvenIndex.swappedInput,AlgHom.comp_apply,EvenIndex.input_atom_zero,swap_atom]
    simp [evaluate,factor]
  | succ n ih =>
    rw [EvenIndex.swappedInput,AlgHom.comp_apply,EvenIndex.input_atom_succ,EvenIndex.map_lie,swap_atom]
    rw [evaluate_lie]
    simp only [Bool.not_false,evaluate_y]
    change ⁅leftMul (B+s),evaluate s (EvenIndex.swappedInput (atom (n,())))⁆=leftMul (P s n)
    rw [ih]
    cases n with
    | zero => exact left_comm_D hs
    | succ n =>
      change ⁅leftMul (B+s),leftMul (P s n)⁆=leftMul ⁅B+s,P s n⁆
      simp only [Ring.lie_def,map_sub,map_mul]


-- @@ L1616-1616 verbatim
end


-- @@ L1618-1618 verbatim
open AssociativeElimination WordGrading UniversalEmbedding

-- @@ L1619-1619 verbatim
open QuadraticLeading RowTwo RowKernel ExactPentagon ProjectionKernel

-- @@ L1620-1620 verbatim
attribute [local instance] LieRing.ofAssociativeRing

-- @@ L1621-1621 verbatim
variable {R : Type*} [CommRing R]


-- @@ L1623-1627 verbatim
theorem eraseShift_retract (s : S R) :
    (eraseShift s).comp (LetterRetraction.assoc (fun a => a≠Slot.A))=eraseShift s := by
  apply hom_ext
  intro a
  cases a <;> simp [eraseShift]


-- @@ L1629-1632 verbatim
theorem eraseShift_word (s : S R) (w : FreeMonoid Slot) (h : ¬∀ a∈w.toList,a≠Slot.A) :
    eraseShift s (word w)=0 := by
  rw [←AlgHom.congr_fun (eraseShift_retract s) (word w),AlgHom.comp_apply,
    LetterRetraction.assoc_word,ite_eq_right h,map_zero]


-- @@ L1634-1653 verbatim
theorem erase_selector (s : S R) {n m r : ℕ} (hn : n=2*m+r) {p : A R Slot}
    (hp : p∈homogeneous weight n) :
    eraseShift s (piece xSlot m p)=eraseShift s (piece bCount r p) := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    by_cases hno : ∀ a∈w.toList,a≠Slot.A
    · have he : degree xSlot w=degree acCount w := by
        apply degree_congr_word
        intro a ha
        have h := hno a ha
        cases a <;> simp_all [xSlot,acCount,aCount,cCount]
      have hwc := weight_count w
      have hi : degree xSlot w=m ↔ degree bCount w=r := by omega
      simp only [piece,project_word,hi]
    · simp only [piece,project_word]
      split_ifs <;> simp [eraseShift_word s w hno]
  | zero => simp
  | add p q _ _ hp hq => simp only [map_add,hp,hq]
  | smul c p _ hp => simp only [map_smul,hp]


-- @@ L1655-1655 verbatim
def translate (s : S R) : S R →ₐ[R] S R := lift (fun b => if b then B+s else C)


-- @@ L1657-1657 verbatim
@[simp] theorem translate_C (s : S R) : translate s C=C := by simp [translate,C]

-- @@ L1658-1658 verbatim
@[simp] theorem translate_B (s : S R) : translate s B=B+s := by simp [translate,B]


-- @@ L1660-1663 verbatim
theorem translate_erase (s : S R) : (translate s).comp (eraseShift 0)=eraseShift s := by
  apply hom_ext
  intro a
  cases a <;> simp [eraseShift]


-- @@ L1665-1672 verbatim
theorem selected_constant {s : S (ZMod 2)} (hs : D s=0)
    {q : A (ZMod 2) (ℕ×Unit)} {p : A (ZMod 2) Slot}
    (he : EvenIndex.swappedInput q=quad p) : constant s q=eraseShift s p := by
  change operators s q 1=eraseShift s p
  have h := AlgHom.congr_fun (evaluate_swapped hs) q
  rw [←h,AlgHom.comp_apply,he]
  have h' := AlgHom.congr_fun (evaluate_quad hs) p
  rw [←AlgHom.comp_apply,h',AlgHom.comp_apply,leftMul_apply,mul_one]


-- @@ L1674-1683 verbatim
theorem shifted_leading_bound {ψ : FreeLieAlgebra (ZMod 2) Bool}
    {p : FreeLieAlgebra (ZMod 2) Slot} {n m r : ℕ}
    (hn : 1<n) (hnm : n=2*m+r) (hψ : embed ψ∈homogeneous (fun _ => 1) n)
    (hp : under p=embed ψ) (hanti : BaseChangeEquations.antisymmetry ψ=0)
    (hr : embed p∈above bCount r) {s : S (ZMod 2)} (hs : D s=0) (hc : ⁅(C : S (ZMod 2)),s⁆=0) :
    eraseShift s (piece bCount r (embed p))∈above wt r := by
  rw [←erase_selector s hnm (representation_weight hψ hp)]
  rw [←selected_constant hs (EvenIndex.selected_expression hn hψ hp hanti m)]
  apply constant_bound hs hc
  exact project_preserves (EvenIndex.termwise_bound hn hψ hp hr)


-- @@ L1685-1685 verbatim
end OreShift


-- @@ L1687-1687 verbatim
namespace PositionalDeletion

-- @@ L1688-1688 verbatim
open AssociativeElimination WordGrading

-- @@ L1689-1689 verbatim
attribute [local instance] LieRing.ofAssociativeRing

-- @@ L1690-1690 verbatim
variable {R : Type*} [CommRing R]

-- @@ L1691-1691 verbatim
local notation "S" => A R Bool


-- @@ L1693-1697 verbatim
def replaceWord (u : S) : ℕ → List Bool → S
  | _,[] => 0
  | i,false::w => atom false*replaceWord u i w
  | 0,true::w => u*word (FreeMonoid.ofList w)
  | i+1,true::w => atom true*replaceWord u i w


-- @@ L1699-1701 verbatim
def replace (u : S) (i : ℕ) : S →ₗ[R] S :=
  (Finsupp.linearCombination R (fun w : FreeMonoid Bool => replaceWord u i w.toList)).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap


-- @@ L1703-1705 verbatim
@[simp] theorem replace_word (u : S) (i : ℕ) (w : FreeMonoid Bool) :
    replace u i (word w)=replaceWord u i w.toList := by
  change Finsupp.linearCombination R (fun monoidWord : FreeMonoid Bool => replaceWord u i monoidWord.toList) (Finsupp.single w 1) = _; simp


-- @@ L1707-1710 verbatim
@[simp] theorem replace_one (u : S) (i : ℕ) : replace u i 1=0 := by
  change replace u i (word 1)=0
  rw [replace_word]
  rfl


-- @@ L1712-1720 verbatim
theorem replace_C_mul (u : S) (i : ℕ) (p : S) :
    replace u i (atom false*p)=atom false*replace u i p := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change replace u i (word (FreeMonoid.of false)*word w)=word (FreeMonoid.of false)*replace u i (word w)
    rw [←word_mul,replace_word,replace_word]
    rfl
  | add p q hp hq => simp only [mul_add,map_add,hp,hq]
  | smul c p hp => simp only [mul_smul_comm,map_smul,hp]


-- @@ L1722-1729 verbatim
theorem replace_B_mul_zero (u p : S) : replace u 0 (atom true*p)=u*p := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change replace u 0 (word (FreeMonoid.of true)*word w)=u*word w
    rw [←word_mul,replace_word]
    rfl
  | add p q hp hq => simp only [mul_add,map_add,hp,hq]
  | smul c p hp => simp only [mul_smul_comm,map_smul,hp]


-- @@ L1731-1739 verbatim
theorem replace_B_mul_succ (u : S) (i : ℕ) (p : S) :
    replace u (i+1) (atom true*p)=atom true*replace u i p := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change replace u (i+1) (word (FreeMonoid.of true)*word w)=word (FreeMonoid.of true)*replace u i (word w)
    rw [←word_mul,replace_word,replace_word]
    rfl
  | add p q hp hq => simp only [mul_add,map_add,hp,hq]
  | smul c p hp => simp only [mul_smul_comm,map_smul,hp]


-- @@ L1741-1741 verbatim
def countB (w : List Bool) : ℕ := w.count true


-- @@ L1743-1743 verbatim
@[simp] theorem countB_nil : countB []=0 := rfl

-- @@ L1744-1744 verbatim
@[simp] theorem countB_false (w : List Bool) : countB (false::w)=countB w := by simp [countB]

-- @@ L1745-1745 verbatim
@[simp] theorem countB_true (w : List Bool) : countB (true::w)=countB w+1 := by simp [countB]


-- @@ L1747-1759 verbatim
theorem replaceWord_missing (u : S) (i : ℕ) (w : List Bool) (h : countB w ≤ i) :
    replaceWord u i w=0 := by
  induction w generalizing i with
  | nil => rfl
  | cons b w ih =>
    cases b with
    | false => simp only [countB_false] at h; simp only [replaceWord,ih i h,mul_zero]
    | true =>
      cases i with
      | zero => simp only [countB_true] at h; omega
      | succ i =>
        simp only [countB_true] at h
        simp only [replaceWord,ih i (by omega),mul_zero]


-- @@ L1761-1763 verbatim
theorem word_cons (b : Bool) (w : List Bool) :
    word (R:=R) (FreeMonoid.ofList (b::w))=atom b*word (FreeMonoid.ofList w) :=
  word_mul (FreeMonoid.of b) (FreeMonoid.ofList w)


-- @@ L1765-1784 verbatim
theorem replaceWord_append (u : S) (i : ℕ) (v w : List Bool) :
    replaceWord u i (v++w)=if i<countB v then
      replaceWord u i v*word (FreeMonoid.ofList w) else
      word (FreeMonoid.ofList v)*replaceWord u (i-countB v) w := by
  induction v generalizing i with
  | nil => simp
  | cons b v ih =>
    cases b with
    | false =>
      simp only [List.cons_append,replaceWord,countB_false,ih,word_cons]
      split_ifs <;> simp only [mul_assoc]
    | true =>
      cases i with
      | zero =>
        simp only [List.cons_append,replaceWord,countB_true,Nat.zero_lt_succ,ite_true]
        rw [show FreeMonoid.ofList (v++w)=FreeMonoid.ofList v*FreeMonoid.ofList w from rfl,word_mul,mul_assoc]
      | succ i =>
        simp only [List.cons_append,replaceWord,countB_true,Nat.add_lt_add_iff_right,
          Nat.add_sub_add_right,ih,word_cons]
        split_ifs <;> simp only [mul_assoc]


-- @@ L1786-1786 verbatim
end PositionalDeletion


-- @@ L1788-1788 verbatim
namespace GapWord


-- @@ L1790-1790 verbatim
abbrev G := ℕ × List ℕ


-- @@ L1792-1792 verbatim
def prepend (a : ℕ) (g : G) : G := (a,g.1::g.2)

-- @@ L1793-1793 verbatim
def bump (a : ℕ) (g : G) : G := (a+g.1,g.2)


-- @@ L1795-1797 verbatim
def encode : G → List Bool
  | (a,[]) => List.replicate a false
  | (a,b::v) => List.replicate a false ++ true::encode (b,v)


-- @@ L1799-1802 verbatim
def decode : List Bool → G
  | [] => (0,[])
  | false::w => bump 1 (decode w)
  | true::w => prepend 0 (decode w)


-- @@ L1804-1808 verbatim
theorem decode_false_prefix (a : ℕ) (w : List Bool) :
    decode (List.replicate a false++w)=bump a (decode w) := by
  induction a with
  | zero => simp [bump]
  | succ a ih => simp [List.replicate_succ,decode,ih,bump,Nat.add_assoc,Nat.add_left_comm]


-- @@ L1810-1814 verbatim
theorem decode_encode (g : G) : decode (encode g)=g := by
  obtain ⟨a,v⟩ := g
  induction v generalizing a with
  | nil => simpa [encode,decode,bump] using decode_false_prefix a []
  | cons b v ih => simp [encode,decode_false_prefix,decode,ih,bump,prepend]


-- @@ L1816-1819 verbatim
theorem encode_bump (a : ℕ) (g : G) :
    encode (bump a g)=List.replicate a false++encode g := by
  obtain ⟨b,v⟩ := g
  cases v <;> simp only [bump,encode,List.replicate_add,List.append_assoc]


-- @@ L1821-1824 verbatim
theorem encode_prepend (a : ℕ) (g : G) :
    encode (prepend a g)=List.replicate a false++true::encode g := by
  obtain ⟨b,v⟩ := g
  simp [prepend,encode]


-- @@ L1826-1830 verbatim
theorem encode_decode (w : List Bool) : encode (decode w)=w := by
  induction w with
  | nil => simp [encode,decode]
  | cons b w ih =>
    cases b <;> simp [decode,encode_bump,encode_prepend,ih]


-- @@ L1832-1832 verbatim
def size (g : G) : ℕ := g.1+g.2.sum


-- @@ L1834-1834 verbatim
theorem size_bump (a : ℕ) (g : G) : size (bump a g)=a+size g := by simp [size,bump,Nat.add_assoc]

-- @@ L1835-1835 verbatim
theorem size_prepend (a : ℕ) (g : G) : size (prepend a g)=a+size g := by simp [size,prepend]


-- @@ L1837-1841 verbatim
theorem size_decode (w : List Bool) : size (decode w)=w.count false := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b <;> simp [decode,size_bump,size_prepend,ih,Nat.add_comm]


-- @@ L1843-1846 verbatim
def merge (j : ℕ) : ℕ → G → Option G
  | _,(_,[]) => none
  | 0,(a,b::v) => some (a+j+b,v)
  | i+1,(a,b::v) => (merge j i (b,v)).map (prepend a)


-- @@ L1848-1851 verbatim
def erase (j : ℕ) : ℕ → G → Option G
  | 0,(a,v) => if j≤a then some (a-j,v) else none
  | _+1,(_,[]) => none
  | i+1,(a,b::v) => (erase j i (b,v)).map (prepend a)


-- @@ L1853-1864 verbatim
theorem erase_small (j i : ℕ) (g : G) (h : size g<j) : erase j i g=none := by
  obtain ⟨a,v⟩ := g
  induction v generalizing a i with
  | nil => cases i <;> simp_all [erase,size]
  | cons b v ih =>
    cases i with
    | zero =>
      have ha : ¬j≤a := by simp only [size,List.sum_cons] at h; omega
      simp only [erase,ite_eq_right ha]
    | succ i =>
      have hb : size (b,v)<j := by simp only [size,List.sum_cons] at *; omega
      simp only [erase,ih i b hb,Option.map_none]


-- @@ L1866-1908 verbatim
theorem erase_merge (j i k : ℕ) (g : G) (h : size g<j) :
    (merge j k g).bind (erase j i)=if i=k then merge 0 k g else none := by
  obtain ⟨a,v⟩ := g
  induction v generalizing a i k with
  | nil => simp [merge]
  | cons b v ih =>
    have ha : a<j := by simp only [size,List.sum_cons] at h; omega
    have hb : size (b,v)<j := by simp only [size,List.sum_cons] at *; omega
    cases k with
    | zero =>
      cases i with
      | zero =>
        simp only [merge,Option.bind_some,erase]
        rw [ite_eq_left (by omega)]
        congr 2; omega
      | succ i =>
        simp only [merge,Option.bind_some,Nat.succ_ne_zero,ite_false]
        cases v with
        | nil => rfl
        | cons c v =>
          have hv : size (c,v)<j := by simp only [size,List.sum_cons] at hb ⊢; omega
          simp only [erase,erase_small j i (c,v) hv,Option.map_none]
    | succ k =>
      cases i with
      | zero =>
        simp only [merge,Nat.zero_ne_add_one,ite_false]
        cases hm : merge j k (b,v) with
        | none => rfl
        | some u => simp [Option.map,prepend,erase,show ¬j≤a by omega]
      | succ i =>
        simp only [merge,Nat.add_right_cancel_iff]
        have hi := ih i k b hb
        cases hm : merge j k (b,v) with
        | none =>
          rw [hm] at hi
          split_ifs at hi ⊢ with he
          · rw [← hi]; rfl
          · rfl
        | some u =>
          rw [hm,Option.bind_some] at hi
          change ((erase j i u).map (prepend a))=if i=k then (merge 0 k (b,v)).map (prepend a) else none
          rw [hi]
          split_ifs <;> rfl


-- @@ L1910-1910 verbatim
end GapWord


-- @@ L1912-1912 verbatim
namespace GapAlgebra

-- @@ L1913-1913 verbatim
open AssociativeElimination WordGrading GapWord PositionalDeletion

-- @@ L1914-1914 verbatim
variable {R : Type*} [CommRing R]

-- @@ L1915-1915 verbatim
local notation "S" => A R Bool

-- @@ L1916-1916 verbatim
local notation "C" => (OreShift.C : S)

-- @@ L1917-1917 verbatim
local notation "B" => (OreShift.B : S)


-- @@ L1919-1919 verbatim
def alg (g : G) : S := word (FreeMonoid.ofList (encode g))

-- @@ L1920-1920 verbatim
def optionAlg (g : Option G) : S := g.elim 0 alg


-- @@ L1922-1922 verbatim
@[simp] theorem optionAlg_none : optionAlg (R:=R) none=0 := rfl

-- @@ L1923-1923 verbatim
@[simp] theorem optionAlg_some (g : G) : optionAlg (R:=R) (some g)=alg g := rfl


-- @@ L1925-1928 verbatim
theorem word_false_pow (a : ℕ) : word (R:=R) (FreeMonoid.ofList (List.replicate a false))=C^a := by
  induction a with
  | zero => rfl
  | succ a ih => rw [List.replicate_succ,word_cons,ih,pow_succ']; rfl


-- @@ L1930-1934 verbatim
theorem alg_bump (a : ℕ) (g : G) : alg (R:=R) (bump a g)=C^a*alg g := by
  rw [alg,encode_bump]
  change word (FreeMonoid.ofList (List.replicate a false)*FreeMonoid.ofList (encode g))=_
  rw [word_mul,word_false_pow]
  rfl


-- @@ L1936-1940 verbatim
theorem alg_prepend (a : ℕ) (g : G) : alg (R:=R) (prepend a g)=C^a*(B*alg g) := by
  rw [alg,encode_prepend]
  change word (FreeMonoid.ofList (List.replicate a false)*FreeMonoid.ofList (true::encode g))=_
  rw [word_mul,word_false_pow,word_cons]
  rfl


-- @@ L1942-1946 verbatim
theorem optionAlg_prepend (a : ℕ) (g : Option G) :
    optionAlg (R:=R) (g.map (prepend a))=C^a*(B*optionAlg g) := by
  cases g with
  | none => simp
  | some g => exact alg_prepend a g


-- @@ L1948-1949 verbatim
theorem alg_nil (a : ℕ) : alg (R:=R) (a,[])=C^a := by
  simp only [alg,encode,word_false_pow]


-- @@ L1951-1952 verbatim
theorem alg_cons (a b : ℕ) (g : List ℕ) : alg (R:=R) (a,b::g)=C^a*(B*alg (b,g)) :=
  alg_prepend a (b,g)


-- @@ L1954-1962 verbatim
theorem replace_C_pow_mul (u : S) (i a : ℕ) (p : S) :
    replace u i (C^a*p)=C^a*replace u i p := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ',mul_assoc]
    change replace u i (atom false*(C^a*p))=_
    rw [replace_C_mul,ih,mul_assoc]
    rfl


-- @@ L1964-1983 verbatim
theorem replace_alg (j i : ℕ) (g : G) :
    replace (C^j) i (alg g)=optionAlg (merge j i g) := by
  obtain ⟨a,v⟩ := g
  induction v generalizing i a with
  | nil =>
    rw [alg_nil,show C^a=C^a*1 by rw [mul_one],replace_C_pow_mul,replace_one,mul_zero]
    simp only [merge,optionAlg_none]
  | cons b v ih =>
    rw [alg_cons,replace_C_pow_mul]
    cases i with
    | zero =>
      change C^a*replace (C^j) 0 (atom true*alg (b,v))=_
      rw [replace_B_mul_zero]
      simp only [merge,optionAlg_some]
      change C^a*(C^j*alg (b,v))=alg (bump (a+j) (b,v))
      rw [alg_bump,pow_add,mul_assoc]
    | succ i =>
      change C^a*replace (C^j) (i+1) (atom true*alg (b,v))=_
      rw [replace_B_mul_succ,ih,merge]
      exact (optionAlg_prepend a (merge j i (b,v))).symm


-- @@ L1985-1987 verbatim
def eraseLinear (j i : ℕ) : S →ₗ[R] S :=
  (Finsupp.linearCombination R (fun w : FreeMonoid Bool => optionAlg (erase j i (decode w.toList)))).comp
    (MonoidAlgebra.coeffLinearEquiv R).toLinearMap


-- @@ L1989-1991 verbatim
@[simp] theorem eraseLinear_word (j i : ℕ) (w : FreeMonoid Bool) :
    eraseLinear j i (word w : S)=optionAlg (erase j i (decode w.toList)) := by
  change Finsupp.linearCombination R (fun monoidWord : FreeMonoid Bool => optionAlg (erase j i (decode monoidWord.toList))) (Finsupp.single w 1) = _; simp


-- @@ L1993-1995 verbatim
theorem eraseLinear_alg (j i : ℕ) (g : G) :
    eraseLinear j i (alg g : S)=optionAlg (erase j i g) := by
  simp [alg,decode_encode]


-- @@ L1997-2001 verbatim
theorem eraseLinear_optionAlg (j i : ℕ) (g : Option G) :
    eraseLinear j i (optionAlg g : S)=optionAlg (g.bind (erase j i)) := by
  cases g with
  | none => simp
  | some g => exact eraseLinear_alg j i g


-- @@ L2003-2008 verbatim
theorem eraseLinear_replace_alg (j i k : ℕ) (g : G) (h : size g<j) :
    eraseLinear j i (replace (C^j) k (alg g))=if i=k then replace 1 k (alg g) else 0 := by
  rw [replace_alg,eraseLinear_optionAlg,erase_merge j i k g h]
  split_ifs with he
  · simpa only [pow_zero] using (replace_alg (R:=R) 0 k g).symm
  · rfl


-- @@ L2010-2015 verbatim
theorem eraseLinear_replace_word (j i k : ℕ) (w : FreeMonoid Bool)
    (h : w.toList.count false<j) :
    eraseLinear j i (replace (C^j) k (word w))=if i=k then replace 1 k (word w) else 0 := by
  have hg : word (R:=R) w=alg (decode w.toList) := by simp [alg,encode_decode]
  rw [hg]
  exact eraseLinear_replace_alg j i k _ (by simpa only [size_decode] using h)


-- @@ L2017-2017 verbatim
end GapAlgebra


-- @@ L2019-2019 verbatim
namespace WordGrading

-- @@ L2020-2020 verbatim
open AssociativeElimination

-- @@ L2021-2021 verbatim
variable {R α β : Type*} [CommRing R]


-- @@ L2023-2044 verbatim
theorem algHom_difference_lower (f g : A R α →ₐ[R] A R β)
    (wa : α → ℕ) (wb : β → ℕ)
    (hf : ∀ a,f (atom a)∈below wb (wa a))
    (hg : ∀ a,g (atom a)∈homogeneous wb (wa a))
    (he : ∀ a,f (atom a)-g (atom a)∈space (fun w => degree wb w<wa a))
    {n : ℕ} {p : A R α} (hp : p∈homogeneous wa n) :
    f p-g p∈space (fun w => degree wb w<n) := by
  have hw (w : FreeMonoid α) : f (word w)-g (word w)∈space (fun v => degree wb v<degree wa w) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp
    | of_mul a w ih =>
      simp only [word_mul,word_of,map_mul,degree_mul,degree_of]
      have hfw : f (word w)∈below wb (degree wa w) :=
        algHom_below f wa wb hf (word_mem w (le_refl _))
      have h1 : (f (atom a)-g (atom a))*f (word w)∈space (fun v => degree wb v<wa a+degree wa w) := mul_mem (by intro u v hu hv; simp only [degree_mul]; omega) (he a) hfw
      have h2 : g (atom a)*(f (word w)-g (word w))∈space (fun v => degree wb v<wa a+degree wa w) := mul_mem (by intro u v hu hv; simp only [degree_mul]; omega) (hg a) ih
      have eq : f (atom a)*f (word w)-g (atom a)*g (word w)=
          (f (atom a)-g (atom a))*f (word w)+g (atom a)*(f (word w)-g (word w)) := by noncomm_ring
      rw [eq]
      exact (space (fun v => degree wb v<wa a+degree wa w)).add_mem h1 h2
  exact map_space (f.toLinearMap-g.toLinearMap) _
    (by intro w hw'; simpa only [LinearMap.sub_apply,AlgHom.toLinearMap_apply,hw'] using hw w) hp


-- @@ L2046-2055 verbatim
theorem above_lower_zero {wt : α → ℕ} {n : ℕ} {p : A R α}
    (hp : p∈above wt n) (hl : p∈space (fun w => degree wt w<n)) : p=0 := by
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  by_contra hn
  have hne : p.coeff w≠0 := by simpa using hn
  have h1 := mem_space_iff.mp hp w hne
  have h2 := mem_space_iff.mp hl w hne
  omega


-- @@ L2057-2057 verbatim
end WordGrading

-- @@ L2058-2058 verbatim
namespace OreShift


-- @@ L2060-2060 verbatim
section

-- @@ L2061-2061 verbatim
open AssociativeElimination WordGrading UniversalEmbedding

-- @@ L2062-2062 verbatim
open QuadraticLeading RowTwo RowKernel ExactPentagon

-- @@ L2063-2063 verbatim
attribute [local instance] LieRing.ofAssociativeRing

-- @@ L2064-2064 verbatim
variable {R : Type*} [CommRing R]


-- @@ L2066-2091 verbatim
theorem translate_difference {s : S R} (hs : s∈homogeneous wt 0) {r : ℕ} {p : S R}
    (hp : p∈homogeneous wt r) : translate s p-p∈space (fun w => degree wt w<r) := by
  apply algHom_difference_lower (translate s) (AlgHom.id R (S R)) wt wt ?_ ?_ ?_ hp
  · intro b
    cases b with
    | false =>
      change translate s C∈below wt 0
      rw [translate_C]
      exact homogeneous_below (word_mem _ rfl)
    | true =>
      change translate s B∈below wt 1
      rw [translate_B]
      exact (below wt 1).add_mem (word_mem _ (by simp [degree_of,wt]))
        (space_mono (by intro w hw; omega) hs)
  · intro b
    exact word_mem _ (degree_of wt b)
  · intro b
    cases b with
    | false =>
      change translate s C-C∈_
      rw [translate_C,sub_self]
      exact Submodule.zero_mem _
    | true =>
      change translate s B-B∈space (fun w => degree wt w<1)
      rw [translate_B,add_sub_cancel_left]
      exact space_mono (by intro w hw; omega) hs


-- @@ L2093-2097 verbatim
theorem erase_degree (a : Slot) : eraseShift (0 : S R) (atom a)∈homogeneous wt (bCount a) := by
  cases a <;> simp only [eraseShift,lift_atom,add_zero]
  · exact Submodule.zero_mem _
  · exact word_mem _ rfl
  · exact word_mem _ rfl


-- @@ L2099-2112 verbatim
theorem shift_invariant {ψ : FreeLieAlgebra (ZMod 2) Bool}
    {p : FreeLieAlgebra (ZMod 2) Slot} {n m r : ℕ}
    (hn : 1<n) (hnm : n=2*m+r) (hψ : embed ψ∈homogeneous (fun _ => 1) n)
    (hp : under p=embed ψ) (hanti : BaseChangeEquations.antisymmetry ψ=0)
    (hr : embed p∈above bCount r) {s : S (ZMod 2)}
    (hs : D s=0) (hc : ⁅(C : S (ZMod 2)),s⁆=0) (hdeg : s∈homogeneous wt 0) :
    eraseShift s (piece bCount r (embed p))=eraseShift 0 (piece bCount r (embed p)) := by
  have hf := algHom_homogeneous (eraseShift (0 : S (ZMod 2))) bCount wt erase_degree
    (piece_mem bCount r (embed p))
  have hd := translate_difference hdeg hf
  rw [←AlgHom.comp_apply,translate_erase] at hd
  apply sub_eq_zero.mp
  exact above_lower_zero ((above wt r).sub_mem
    (shifted_leading_bound hn hnm hψ hp hanti hr hs hc) (homogeneous_above hf)) hd


-- @@ L2114-2114 verbatim
end


-- @@ L2116-2116 verbatim
open AssociativeElimination WordGrading

-- @@ L2117-2117 verbatim
variable {R : Type*} [CommRing R]


-- @@ L2119-2119 verbatim
def shiftDeriv (s : S R) : S R →ₗ[R] S R := deriv (fun b => if b then s else 0)


-- @@ L2121-2121 verbatim
@[simp] theorem shiftDeriv_C (s : S R) : shiftDeriv s C=0 := by simp [shiftDeriv,C]

-- @@ L2122-2122 verbatim
@[simp] theorem shiftDeriv_B (s : S R) : shiftDeriv s B=s := by simp [shiftDeriv,B]

-- @@ L2123-2123 verbatim
@[simp] theorem shiftDeriv_one (s : S R) : shiftDeriv s 1=0 := deriv_one _

-- @@ L2124-2125 verbatim
theorem shiftDeriv_mul (s p q : S R) :
    shiftDeriv s (p*q)=shiftDeriv s p*q+p*shiftDeriv s q := deriv_mul _ _ _


-- @@ L2127-2133 verbatim
theorem shiftDeriv_degree {s : S R} (hs : s∈homogeneous wt 0) {r : ℕ} {p : S R}
    (hp : p∈homogeneous wt r) : shiftDeriv s p∈lower wt 1 r := by
  apply deriv_lower wt 1 _ ?_ hp
  intro b
  cases b with
  | false => exact Submodule.zero_mem _
  | true => exact space_mono (by intro w hw; change degree wt w+1=1; omega) hs


-- @@ L2135-2173 verbatim
theorem taylor_remainder {s : S R} (hs : s∈homogeneous wt 0) {r : ℕ} {p : S R}
    (hp : p∈homogeneous wt r) :
    translate s p-p-shiftDeriv s p∈space (fun w => degree wt w+1<r) := by
  let E : S R →ₗ[R] S R := (translate s).toLinearMap-LinearMap.id-shiftDeriv s
  have hw (w : FreeMonoid Bool) : E (word w)∈space (fun v => degree wt v+1<degree wt w) := by
    induction w using FreeMonoid.inductionOn' with
    | one => simp [E]
    | of_mul b w ih =>
      have hh : word (R:=R) w∈homogeneous wt (degree wt w) := word_mem w rfl
      have hd := translate_difference hs hh
      cases b with
      | false =>
        have he : E (word (FreeMonoid.of false*w))=C*E (word w) := by
          simp only [E,LinearMap.sub_apply,AlgHom.toLinearMap_apply,LinearMap.id_apply,
            word_mul,word_of]
          change translate s (C*word w)-C*word w-shiftDeriv s (C*word w)=_
          rw [map_mul,translate_C,shiftDeriv_mul,shiftDeriv_C,zero_mul,zero_add]
          noncomm_ring
        rw [he]
        have hc : (C : S R)∈homogeneous wt 0 := word_mem _ rfl
        have h1 : C*E (word w)∈space (fun v => degree wt v+1<0+degree wt w) :=
          mul_mem (by intro u v hu hv; simp only [degree_mul]; omega) hc ih
        exact h1
      | true =>
        have he : E (word (FreeMonoid.of true*w))=
            B*E (word w)+s*(translate s (word w)-word w) := by
          simp only [E,LinearMap.sub_apply,AlgHom.toLinearMap_apply,LinearMap.id_apply,
            word_mul,word_of]
          change translate s (B*word w)-B*word w-shiftDeriv s (B*word w)=_
          rw [map_mul,translate_B,shiftDeriv_mul,shiftDeriv_B]
          noncomm_ring
        rw [he]
        have hb : (B : S R)∈homogeneous wt 1 := word_mem _ rfl
        have h1 : B*E (word w)∈space (fun v => degree wt v+1<1+degree wt w) :=
          mul_mem (by intro u v hu hv; simp only [degree_mul]; omega) hb ih
        have h2 : s*(translate s (word w)-word w)∈space (fun v => degree wt v+1<1+degree wt w) :=
          mul_mem (by intro u v hu hv; simp only [degree_mul]; omega) hs hd
        exact (space _).add_mem h1 h2
  exact map_space E _ (by intro w hw'; simpa only [hw'] using hw w) hp


-- @@ L2175-2189 verbatim
theorem shiftDeriv_zero {s : S R} (hs : s∈homogeneous wt 0) {r : ℕ} {p : S R}
    (hp : p∈homogeneous wt r) (he : translate s p=p) : shiftDeriv s p=0 := by
  have hd := shiftDeriv_degree hs hp
  have hl := taylor_remainder hs hp
  rw [he,sub_self,zero_sub] at hl
  have hl' := (space (fun w => degree wt w+1<r)).neg_mem hl
  rw [neg_neg] at hl'
  apply MonoidAlgebra.ext
  apply Finsupp.ext
  intro w
  by_contra hn
  have hne : (shiftDeriv s p).coeff w≠0 := by simpa using hn
  have h1 := mem_space_iff.mp hd w hne
  have h2 := mem_space_iff.mp hl' w hne
  omega


-- @@ L2191-2191 verbatim
end OreShift


-- @@ L2193-2193 verbatim
namespace PositionalDeletion

-- @@ L2194-2194 verbatim
open AssociativeElimination WordGrading

-- @@ L2195-2195 verbatim
variable {R : Type*} [CommRing R]

-- @@ L2196-2196 verbatim
local notation "S" => A R Bool


-- @@ L2198-2203 verbatim
theorem degree_countB (w : FreeMonoid Bool) : degree OreShift.wt w=countB w.toList := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | of_mul b w ih =>
    rw [degree_mul,degree_of,ih]
    cases b <;> simp [OreShift.wt,countB,FreeMonoid.toList_mul,Nat.add_comm]


-- @@ L2205-2222 verbatim
theorem replace_mul (u : S) (i : ℕ) (p q : S) {r : ℕ} (hp : p∈homogeneous OreShift.wt r) :
    replace u i (p*q)=if i<r then replace u i p*q else p*replace u (i-r) q := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨v,hv,rfl⟩ := hp
    have hv' : countB v.toList=r := (degree_countB v).symm.trans hv
    induction q using MonoidAlgebra.induction_on with
    | of w =>
      change replace u i (word v*word w)=if i<r then replace u i (word v)*word w else word v*replace u (i-r) (word w)
      rw [←word_mul,replace_word,replace_word,replace_word]
      change replaceWord u i (v.toList++w.toList)=_
      rw [replaceWord_append,hv']
      simp only [FreeMonoid.ofList_toList]
    | add p q hp hq => simp only [mul_add,map_add,hp,hq]; split_ifs <;> simp
    | smul c p hp => simp only [mul_smul_comm,map_smul,hp]; split_ifs <;> simp
  | zero => simp
  | add p q _ _ hp hq => simp only [add_mul,map_add,hp,hq]; split_ifs <;> simp
  | smul c p _ hp => simp only [smul_mul_assoc,map_smul,hp]; split_ifs <;> simp


-- @@ L2224-2240 verbatim
theorem shiftDeriv_word (u : S) (w : List Bool) :
    OreShift.shiftDeriv u (word (FreeMonoid.ofList w))=
      ∑ i∈Finset.range (countB w), replaceWord u i w := by
  induction w with
  | nil => simp [countB]
  | cons b w ih =>
    rw [word_cons,OreShift.shiftDeriv_mul,ih]
    cases b with
    | false =>
      change OreShift.shiftDeriv u OreShift.C*word (FreeMonoid.ofList w)+_= _
      rw [OreShift.shiftDeriv_C,zero_mul,zero_add]
      simp only [countB_false,replaceWord,Finset.mul_sum]
    | true =>
      change OreShift.shiftDeriv u OreShift.B*word (FreeMonoid.ofList w)+_= _
      rw [OreShift.shiftDeriv_B,countB_true,Finset.sum_range_succ']
      simp only [replaceWord,Finset.mul_sum]
      abel


-- @@ L2242-2251 verbatim
theorem shiftDeriv_eq_sum (u : S) (p : S) {r : ℕ} (hp : p∈homogeneous OreShift.wt r) :
    OreShift.shiftDeriv u p=∑ i∈Finset.range r, replace u i p := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    have hw' : countB w.toList=r := (degree_countB w).symm.trans hw
    simpa only [replace_word,FreeMonoid.ofList_toList,hw'] using shiftDeriv_word u w.toList
  | zero => simp
  | add p q _ _ hp hq => simp [map_add,hp,hq,Finset.sum_add_distrib]
  | smul c p _ hp => simp [map_smul,hp,Finset.smul_sum]


-- @@ L2253-2253 verbatim
end PositionalDeletion


-- @@ L2255-2255 verbatim
namespace WordGrading

-- @@ L2256-2256 verbatim
open AssociativeElimination

-- @@ L2257-2257 verbatim
variable {R α : Type*} [CommRing R]


-- @@ L2259-2267 verbatim
theorem exists_below (wt : α → ℕ) (p : A R α) : ∃ n,p∈below wt n := by
  induction p using MonoidAlgebra.induction_on with
  | of w => exact ⟨degree wt w,word_mem w (le_refl _)⟩
  | add p q hp hq =>
    obtain ⟨n,hn⟩ := hp
    obtain ⟨m,hm⟩ := hq
    exact ⟨n+m,(below wt _).add_mem (space_mono (by intro w hw; omega) hn)
      (space_mono (by intro w hw; omega) hm)⟩
  | smul c p hp => obtain ⟨n,hn⟩ := hp; exact ⟨n,(below wt n).smul_mem _ hn⟩


-- @@ L2269-2269 verbatim
end WordGrading

-- @@ L2270-2270 verbatim
namespace GapSelection

-- @@ L2271-2271 verbatim
open AssociativeElimination WordGrading PositionalDeletion GapAlgebra

-- @@ L2272-2272 verbatim
variable {R : Type*} [CommRing R]

-- @@ L2273-2273 verbatim
local notation "S" => A R Bool

-- @@ L2274-2274 verbatim
local notation "C" => (OreShift.C : S)


-- @@ L2276-2276 verbatim
def cwt (b : Bool) : ℕ := if b then 0 else 1


-- @@ L2278-2283 verbatim
theorem degree_countC (w : FreeMonoid Bool) : degree cwt w=w.toList.count false := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | of_mul b w ih =>
    rw [degree_mul,degree_of,ih]
    cases b <;> simp [cwt,FreeMonoid.toList_mul,Nat.add_comm]


-- @@ L2285-2293 verbatim
theorem eraseLinear_replace {p : S} {m j : ℕ} (hp : p∈below cwt m) (hj : m<j) (i k : ℕ) :
    eraseLinear j i (replace (C^j) k p)=if i=k then replace 1 k p else 0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    exact eraseLinear_replace_word j i k w (by rw [degree_countC] at hw; omega)
  | zero => simp
  | add p q _ _ hp hq => simp only [map_add,hp,hq]; split_ifs <;> simp
  | smul c p _ hp => simp only [map_smul,hp]; split_ifs <;> simp


-- @@ L2295-2304 verbatim
theorem replace_missing_homogeneous {p : S} {r i : ℕ} (hp : p∈homogeneous OreShift.wt r) (hi : r ≤ i) :
    replace 1 i p=0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨w,hw,rfl⟩ := hp
    rw [replace_word]
    exact replaceWord_missing _ _ _ (by rw [←degree_countB,hw]; exact hi)
  | zero => exact map_zero _
  | add p q _ _ hp hq => simp [hp,hq]
  | smul c p _ hp => simp [hp]


-- @@ L2306-2314 verbatim
theorem Cpow_degree (j : ℕ) : C^j∈homogeneous OreShift.wt 0 := by
  induction j with
  | zero =>
      rw [pow_zero]
      exact word_mem (1 : FreeMonoid Bool) (show degree OreShift.wt 1=0 from rfl)
  | succ j ih =>
    rw [pow_succ]
    have hc : C∈homogeneous OreShift.wt 0 := word_mem (FreeMonoid.of false) rfl
    exact homogeneous_mul (wt:=OreShift.wt) (n:=0) (m:=0) ih hc


-- @@ L2316-2327 verbatim
theorem all_deletions_zero {p : S} {r : ℕ} (hp : p∈homogeneous OreShift.wt r)
    (hinv : ∀ j,OreShift.translate (C^j) p=p) (i : ℕ) : replace 1 i p=0 := by
  by_cases hi : i<r
  · obtain ⟨m,hm⟩ := exists_below cwt p
    let j := m+1
    have hj : m<j := Nat.lt_succ_self m
    have hd := OreShift.shiftDeriv_zero (Cpow_degree (R:=R) j) hp (hinv j)
    have h := congrArg (eraseLinear j i) hd
    rw [shiftDeriv_eq_sum _ _ hp,map_sum,map_zero] at h
    simp_rw [eraseLinear_replace hm hj i] at h
    simpa [hi] using h
  · exact replace_missing_homogeneous hp (by omega)


-- @@ L2329-2329 verbatim
end GapSelection


-- @@ L2331-2331 verbatim
namespace GeneratorDeletion


-- @@ L2333-2333 verbatim
section

-- @@ L2334-2334 verbatim
open AssociativeElimination WordGrading UniversalEmbedding AlphabetTransport PositionalDeletion QuadraticLeading

-- @@ L2335-2335 verbatim
attribute [local instance] LieRing.ofAssociativeRing

-- @@ L2336-2336 verbatim
abbrev K := ZMod 2

-- @@ L2337-2337 verbatim
abbrev I := ℕ × Unit

-- @@ L2338-2338 verbatim
abbrev Q := A K I


-- @@ L2340-2343 verbatim
def removeWord : ℕ → List I → Q
  | _,[] => 0
  | 0,a::w => if a.1=0 then word (FreeMonoid.ofList w) else 0
  | i+1,a::w => atom a*removeWord i w


-- @@ L2345-2347 verbatim
def remove (i : ℕ) : Q →ₗ[K] Q :=
  (Finsupp.linearCombination K (fun w : FreeMonoid I => removeWord i w.toList)).comp
    (MonoidAlgebra.coeffLinearEquiv K).toLinearMap


-- @@ L2349-2351 verbatim
@[simp] theorem remove_word (i : ℕ) (w : FreeMonoid I) :
    remove i (word w)=removeWord i w.toList := by
  change Finsupp.linearCombination K (fun monoidWord : FreeMonoid I => removeWord i monoidWord.toList) (Finsupp.single w 1) = _; simp


-- @@ L2353-2356 verbatim
def zeroAt : ℕ → List I → Bool
  | _,[] => false
  | 0,a::_ => decide (a.1=0)
  | i+1,_::w => zeroAt i w


-- @@ L2358-2361 verbatim
def insertList : ℕ → List I → List I
  | 0,w => (0,())::w
  | _+1,[] => [(0,())]
  | i+1,a::w => a::insertList i w


-- @@ L2363-2365 verbatim
def insert (i : ℕ) : Q →ₗ[K] Q :=
  (Finsupp.linearCombination K (fun w : FreeMonoid I => word (FreeMonoid.ofList (insertList i w.toList)))).comp
    (MonoidAlgebra.coeffLinearEquiv K).toLinearMap


-- @@ L2367-2369 verbatim
@[simp] theorem insert_word (i : ℕ) (w : FreeMonoid I) :
    insert i (word w)=word (FreeMonoid.ofList (insertList i w.toList)) := by
  change Finsupp.linearCombination K (fun monoidWord : FreeMonoid I => word (FreeMonoid.ofList (insertList i monoidWord.toList))) (Finsupp.single w 1) = _; simp


-- @@ L2371-2379 verbatim
theorem insert_succ_atom_mul (i : ℕ) (a : I) (p : Q) :
    insert (i+1) (atom a*p)=atom a*insert i p := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change insert (i+1) (word (FreeMonoid.of a)*word w)=word (FreeMonoid.of a)*insert i (word w)
    rw [←word_mul,insert_word,insert_word,←word_mul]
    rfl
  | add p q hp hq => simp only [mul_add,map_add,hp,hq]
  | smul c p hp => simp only [mul_smul_comm,map_smul,hp]


-- @@ L2381-2402 verbatim
theorem insert_remove_word (i : ℕ) (w : List I) :
    insert i (removeWord i w)=if zeroAt i w then word (FreeMonoid.ofList w) else 0 := by
  induction w generalizing i with
  | nil => simp [removeWord,zeroAt]
  | cons a w ih =>
    cases i with
    | zero =>
      simp only [removeWord,zeroAt,decide_eq_true_eq]
      split_ifs with h
      · rw [insert_word]
        obtain ⟨n,u⟩ := a
        cases u
        simp only at h
        subst n
        rfl
      · exact map_zero _
    | succ i =>
      rw [removeWord,insert_succ_atom_mul,ih]
      rw [zeroAt]
      split_ifs
      · exact (word_mul (FreeMonoid.of a) (FreeMonoid.ofList w)).symm
      · exact mul_zero _


-- @@ L2404-2411 verbatim
theorem insert_remove (i : ℕ) (p : Q) :
    insert i (remove i p)=project (fun w => zeroAt i w.toList=true) p := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change insert i (remove i (word w))=project _ (word w)
    rw [remove_word,project_word,insert_remove_word,FreeMonoid.ofList_toList]
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul c p hp => simp only [map_smul,hp]


-- @@ L2413-2414 verbatim
theorem input_injective : Function.Injective EvenIndex.input :=
  (assoc_injective bitOption.symm bitOption bitOption.right_inv).comp EliminationGraded.collapse_injective


-- @@ L2416-2426 verbatim
theorem input_degree (a : I) : EvenIndex.input (atom a)∈homogeneous OreShift.wt 1 := by
  obtain ⟨n,u⟩ := a
  cases u
  rw [EvenIndex.input_atom]
  have hg : ∀ a : Option Unit,renameAssoc (R:=K) bitOption.symm (atom a)∈homogeneous OreShift.wt ((OreShift.wt ∘ bitOption.symm) a) := by
    intro a
    rw [renameAssoc_atom]
    exact word_mem _ (degree_of _ _)
  have hd : embed (Elimination.adWord n () : Elimination.G K Unit)∈homogeneous (OreShift.wt ∘ bitOption.symm) 1 := by
    simpa [OreShift.wt,bitOption] using EliminationGraded.adWord_degree (R:=K) n () (OreShift.wt ∘ bitOption.symm)
  exact algHom_homogeneous (renameAssoc bitOption.symm) (OreShift.wt ∘ bitOption.symm) OreShift.wt hg hd


-- @@ L2428-2438 verbatim
theorem replace_input_atom_zero (n : ℕ) :
    replace 1 0 (EvenIndex.input (atom (n,())))=if n=0 then 1 else 0 := by
  induction n with
  | zero =>
    rw [EvenIndex.input_atom_zero,ite_eq_left rfl]
    simpa only [mul_one] using replace_B_mul_zero (R:=K) 1 1
  | succ n ih =>
    rw [EvenIndex.input_atom_succ]
    change replace 1 0 ((atom false : A K Bool)*EvenIndex.input (atom (n,()))-EvenIndex.input (atom (n,()))*atom false)=_
    rw [map_sub,replace_C_mul,replace_mul 1 0 _ _ (input_degree (n,())),ite_eq_left (by omega),ih]
    by_cases hn : n=0 <;> simp [hn]


-- @@ L2440-2457 verbatim
theorem replace_input_word (i : ℕ) (w : FreeMonoid I) :
    replace 1 i (EvenIndex.input (word w))=EvenIndex.input (remove i (word w)) := by
  rw [remove_word]
  induction w using FreeMonoid.inductionOn' generalizing i with
  | one => simp [removeWord]
  | of_mul a w ih =>
    rw [word_mul,word_of,map_mul,replace_mul 1 i _ _ (input_degree a)]
    obtain ⟨n,u⟩ := a
    cases u
    cases i with
    | zero =>
      rw [ite_eq_left (by omega),replace_input_atom_zero]
      change (if n=0 then 1 else 0)*EvenIndex.input (word w)=EvenIndex.input (if n=0 then word w else 0)
      split_ifs <;> simp
    | succ i =>
      rw [ite_eq_right (by omega),Nat.add_sub_cancel,ih]
      change EvenIndex.input (atom (n,()))*EvenIndex.input (removeWord i w.toList)=EvenIndex.input (atom (n,())*removeWord i w.toList)
      rw [map_mul]


-- @@ L2459-2464 verbatim
theorem replace_input (i : ℕ) (p : Q) :
    replace 1 i (EvenIndex.input p)=EvenIndex.input (remove i p) := by
  induction p using MonoidAlgebra.induction_on with
  | of w => exact replace_input_word i w
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul c p hp => simp only [map_smul,hp]


-- @@ L2466-2466 verbatim
end


-- @@ L2468-2468 verbatim
open AssociativeElimination WordGrading UniversalEmbedding

-- @@ L2469-2469 verbatim
attribute [local instance] LieRing.ofAssociativeRing


-- @@ L2471-2471 verbatim
def noZero (w : List I) : Prop := ∀ a∈w,a.1≠0


-- @@ L2473-2482 verbatim
theorem noZero_of_zeroAt_false (w : List I) (h : ∀ i,zeroAt i w=false) : noZero w := by
  induction w with
  | nil => simp [noZero]
  | cons a w ih =>
    have ha : a.1≠0 := by simpa [zeroAt] using h 0
    have ht : noZero w := ih (fun i => by simpa only [zeroAt] using h (i+1))
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hb
    · exact ha
    · exact ht b hb


-- @@ L2484-2498 verbatim
theorem support_noZero {p : Q} (h : ∀ i,remove i p=0) :
    p∈space (fun w => noZero w.toList) := by
  apply mem_space
  intro w hw
  apply noZero_of_zeroAt_false
  intro i
  have hp : project (fun w => zeroAt i w.toList=true) p=0 := by
    rw [←insert_remove,h i,map_zero]
  have hc := congrArg (fun q : Q => q.coeff w) hp
  rw [project_coeff] at hc
  cases hi : zeroAt i w.toList with
  | false => rfl
  | true =>
    simp only [hi,MonoidAlgebra.coeff_zero,Finsupp.zero_apply] at hc
    exact False.elim (hw hc)


-- @@ L2500-2500 verbatim
def retain : Q →ₐ[K] Q := lift (fun a => if a.1=0 then 0 else atom a)


-- @@ L2502-2502 verbatim
@[simp] theorem retain_atom (a : I) : retain (atom a)=if a.1=0 then 0 else atom a := by simp [retain]


-- @@ L2504-2510 verbatim
theorem retain_word (w : FreeMonoid I) (h : noZero w.toList) : retain (word w)=word w := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul a w ih =>
    have ha : a.1≠0 := h a (List.mem_cons_self)
    have ht : noZero w.toList := fun b hb => h b (List.mem_cons_of_mem a hb)
    rw [word_mul,word_of,map_mul,retain_atom,ite_eq_right ha,ih ht]


-- @@ L2512-2519 verbatim
theorem retain_eq_self {p : Q} (h : ∀ i,remove i p=0) : retain p=p := by
  have hp := support_noZero h
  clear h
  induction hp using Submodule.span_induction with
  | mem p hp => obtain ⟨w,hw,rfl⟩ := hp; exact retain_word w hw
  | zero => exact map_zero _
  | add p q _ _ hp hq => simp only [map_add,hp,hq]
  | smul c p _ hp => simp only [map_smul,hp]


-- @@ L2521-2522 verbatim
def cutLie : FreeLieAlgebra K I →ₗ⁅K⁆ FreeLieAlgebra K ℕ :=
  FreeLieAlgebra.lift K (fun a => match a.1 with | 0 => 0 | n+1 => FreeLieAlgebra.of K n)

-- @@ L2523-2524 verbatim
def includeLie : FreeLieAlgebra K ℕ →ₗ⁅K⁆ FreeLieAlgebra K I :=
  FreeLieAlgebra.lift K (fun n => FreeLieAlgebra.of K (n+1,()))


-- @@ L2526-2526 verbatim
def cutAssoc : Q →ₐ[K] A K ℕ := lift (fun a => match a.1 with | 0 => 0 | n+1 => atom n)

-- @@ L2527-2527 verbatim
def includeAssoc : A K ℕ →ₐ[K] Q := lift (fun n => atom (n+1,()))


-- @@ L2529-2535 verbatim
theorem cut_embed (p : FreeLieAlgebra K I) : cutAssoc (embed p)=embed (cutLie p) := by
  have h : cutAssoc.toLieHom.comp embed=embed.comp cutLie := by
    apply FreeLieAlgebra.hom_ext
    rintro ⟨n,u⟩
    cases u
    cases n <;> simp [cutAssoc,cutLie]
  exact LieHom.congr_fun h p


-- @@ L2537-2542 verbatim
theorem include_embed (p : FreeLieAlgebra K ℕ) : includeAssoc (embed p)=embed (includeLie p) := by
  have h : includeAssoc.toLieHom.comp embed=embed.comp includeLie := by
    apply FreeLieAlgebra.hom_ext
    intro n
    simp [includeAssoc,includeLie]
  exact LieHom.congr_fun h p


-- @@ L2544-2548 verbatim
theorem include_cut : includeAssoc.comp cutAssoc=retain := by
  apply hom_ext
  rintro ⟨n,u⟩
  cases u
  cases n <;> simp [includeAssoc,cutAssoc,retain]


-- @@ L2550-2560 verbatim
theorem positive_generation {p : FreeLieAlgebra K I}
    (h : ∀ i,PositionalDeletion.replace 1 i (EvenIndex.input (embed p))=0) :
    ∃ q : FreeLieAlgebra K ℕ,EvenIndex.input (embed p)=EvenIndex.input (embed (includeLie q)) := by
  have hr (i : ℕ) : remove i (embed p)=0 := by
    apply input_injective
    rw [←replace_input,h i,map_zero]
  refine ⟨cutLie p,?_⟩
  rw [←include_embed,←cut_embed]
  have he : includeAssoc (cutAssoc (embed p))=embed p :=
    (AlgHom.congr_fun include_cut _).trans (retain_eq_self hr)
  rw [he]


-- @@ L2562-2562 verbatim
end GeneratorDeletion


-- @@ L2564-2564 verbatim
namespace ImageBound


-- @@ L2566-2566 verbatim
section

-- @@ L2567-2567 verbatim
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading

-- @@ L2568-2568 verbatim
open RowTwo RowKernel ExactPentagon AlphabetTransport

-- @@ L2569-2569 verbatim
attribute [local instance] LieRing.ofAssociativeRing

-- @@ L2570-2570 verbatim
abbrev K := ZMod 2


-- @@ L2572-2586 verbatim
theorem input_fiber_of_bcount {p : FreeLieAlgebra K Bool} {r : ℕ} (hr : r≠0)
    (hp : embed p∈homogeneous OreShift.wt r) : EvenIndex.input (EvenIndex.fiber p)=embed p := by
  have ho : embed (rename bitOption p)∈homogeneous (OreShift.wt ∘ bitOption.symm) r := by
    rw [rename_embed]
    apply algHom_homogeneous (renameAssoc bitOption) OreShift.wt (OreShift.wt ∘ bitOption.symm) ?_ hp
    intro b
    rw [renameAssoc_atom]
    apply word_mem
    simp [degree_of]
  have hz := EliminationGraded.trace_homogeneous_zero (wt:=OreShift.wt ∘ bitOption.symm) (by simpa [bitOption,OreShift.wt] using hr) ho
  have hd := EliminationGraded.embed_decompose (rename bitOption p)
  rw [hz,zero_smul,add_zero] at hd
  have h := congrArg (renameAssoc bitOption.symm) hd
  rw [rename_embed,assoc_retract bitOption bitOption.symm bitOption.left_inv] at h
  exact h.symm


-- @@ L2588-2588 verbatim
def positiveInput : A K ℕ →ₐ[K] A K Bool := EvenIndex.input.comp GeneratorDeletion.includeAssoc


-- @@ L2590-2596 verbatim
theorem positiveInput_injective : Function.Injective positiveInput := by
  apply GeneratorDeletion.input_injective.comp
  have hc : GeneratorDeletion.cutAssoc.comp GeneratorDeletion.includeAssoc=AlgHom.id K (A K ℕ) := by
    apply hom_ext
    intro n
    simp [GeneratorDeletion.cutAssoc,GeneratorDeletion.includeAssoc]
  exact Function.LeftInverse.injective (f:=GeneratorDeletion.includeAssoc) (g:=GeneratorDeletion.cutAssoc) (fun p => AlgHom.congr_fun hc p)


-- @@ L2598-2599 verbatim
@[simp] theorem positiveInput_atom (n : ℕ) : positiveInput (atom n)=EvenIndex.input (atom (n+1,())) := by
  simp [positiveInput,GeneratorDeletion.includeAssoc]


-- @@ L2601-2613 verbatim
theorem shift_invariant_generation {p : FreeLieAlgebra K Bool} {r : ℕ}
    (hr : r≠0) (hp : embed p∈homogeneous OreShift.wt r)
    (hinv : ∀ j,OreShift.translate ((OreShift.C : A K Bool)^j) (embed p)=embed p) :
    ∃ q : FreeLieAlgebra K ℕ,positiveInput (embed q)=embed p := by
  have hi := input_fiber_of_bcount hr hp
  have hd := GapSelection.all_deletions_zero hp hinv
  obtain ⟨q,hq⟩ := GeneratorDeletion.positive_generation (p:=(Elimination.expand (rename bitOption p)).left)
    (by intro i; change PositionalDeletion.replace 1 i (EvenIndex.input (EvenIndex.fiber p))=0; rw [hi]; exact hd i)
  refine ⟨q,?_⟩
  change EvenIndex.input (EvenIndex.fiber p)=_ at hq
  rw [hi] at hq
  rw [←GeneratorDeletion.include_embed] at hq
  exact hq.symm


-- @@ L2615-2617 verbatim
def eraseLie : FreeLieAlgebra K Slot →ₗ⁅K⁆ FreeLieAlgebra K Bool :=
  FreeLieAlgebra.lift K (fun a => match a with
    | .A => 0 | .B => FreeLieAlgebra.of K true | .C => FreeLieAlgebra.of K false)


-- @@ L2619-2624 verbatim
theorem erase_embed (p : FreeLieAlgebra K Slot) : embed (eraseLie p)=OreShift.eraseShift 0 (embed p) := by
  have h : embed.comp eraseLie=(OreShift.eraseShift (0 : A K Bool)).toLieHom.comp embed := by
    apply FreeLieAlgebra.hom_ext
    intro a
    cases a <;> simp [eraseLie,OreShift.eraseShift,OreShift.B,OreShift.C]
  exact LieHom.congr_fun h p


-- @@ L2626-2627 verbatim
def leading (r : ℕ) (p : FreeLieAlgebra K Slot) : FreeLieAlgebra K Bool :=
  eraseLie (LieGrading.piece bCount r p)


-- @@ L2629-2631 verbatim
@[simp] theorem embed_leading (r : ℕ) (p : FreeLieAlgebra K Slot) :
    embed (leading r p)=OreShift.eraseShift 0 (WordGrading.piece bCount r (embed p)) := by
  rw [leading,erase_embed,LieGrading.embed_piece]


-- @@ L2633-2636 verbatim
theorem leading_bcount (r : ℕ) (p : FreeLieAlgebra K Slot) :
    embed (leading r p)∈homogeneous OreShift.wt r := by
  rw [embed_leading]
  exact algHom_homogeneous _ bCount OreShift.wt OreShift.erase_degree (piece_mem bCount r (embed p))


-- @@ L2638-2638 verbatim
def cbWeight (b : Bool) : ℕ := if b then 1 else 2


-- @@ L2640-2645 verbatim
theorem erase_weight_degree (a : Slot) :
    OreShift.eraseShift (0 : A K Bool) (atom a)∈homogeneous cbWeight (weight a) := by
  cases a <;> simp only [OreShift.eraseShift,lift_atom,add_zero]
  · exact Submodule.zero_mem _
  · exact word_mem (FreeMonoid.of false) rfl
  · exact word_mem (FreeMonoid.of true) rfl


-- @@ L2647-2650 verbatim
theorem leading_weight {p : FreeLieAlgebra K Slot} {n : ℕ}
    (hp : embed p∈homogeneous weight n) (r : ℕ) : embed (leading r p)∈homogeneous cbWeight n := by
  rw [embed_leading]
  exact algHom_homogeneous _ weight cbWeight erase_weight_degree (project_preserves hp)


-- @@ L2652-2657 verbatim
theorem weight_count (w : FreeMonoid Bool) : degree cbWeight w=2*degree GapSelection.cwt w+degree OreShift.wt w := by
  induction w using FreeMonoid.inductionOn' with
  | one => rfl
  | of_mul b w ih =>
    simp only [degree_mul,degree_of]
    cases b <;> simp only [cbWeight,GapSelection.cwt,OreShift.wt,Bool.false_eq_true,ite_false,ite_true] <;> omega


-- @@ L2659-2669 verbatim
theorem weight_split {p : A K Bool} {n r : ℕ} (hp : p≠0)
    (hn : p∈homogeneous cbWeight n) (hr : p∈homogeneous OreShift.wt r) : ∃ m,n=2*m+r := by
  obtain ⟨w,hw⟩ : ∃ w,p.coeff w≠0 := by
    by_contra h
    apply hp
    ext w
    have := not_exists.mp h w
    simpa using this
  have h1 := mem_space_iff.mp hn w hw
  have h2 := mem_space_iff.mp hr w hw
  exact ⟨degree GapSelection.cwt w,by rw [←h1,weight_count,h2]⟩


-- @@ L2671-2674 verbatim
theorem D_Cpow (j : ℕ) : OreShift.D ((OreShift.C : A K Bool)^j)=0 := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ,OreShift.D_mul,ih,OreShift.D_C,zero_mul,mul_zero,add_zero]


-- @@ L2676-2678 verbatim
theorem C_lie_Cpow (j : ℕ) : ⁅(OreShift.C : A K Bool),(OreShift.C : A K Bool)^j⁆=0 := by
  change (OreShift.C : A K Bool)*OreShift.C^j-OreShift.C^j*OreShift.C=0
  rw [←pow_succ',←pow_succ,sub_self]


-- @@ L2680-2689 verbatim
theorem leading_shift_invariant {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot} {n r : ℕ}
    (hn : 1<n) (hψ : embed ψ∈homogeneous (fun _ => 1) n)
    (hp : under p=embed ψ) (hanti : BaseChangeEquations.antisymmetry ψ=0)
    (hr : embed p∈above bCount r) (j : ℕ) :
    OreShift.translate ((OreShift.C : A K Bool)^j) (embed (leading r p))=embed (leading r p) := by
  by_cases hz : embed (leading r p)=0
  · rw [hz,map_zero]
  obtain ⟨m,hm⟩ := weight_split hz (leading_weight (representation_weight hψ hp) r) (leading_bcount r p)
  rw [embed_leading,←AlgHom.comp_apply,OreShift.translate_erase]
  exact OreShift.shift_invariant hn hm hψ hp hanti hr (D_Cpow j) (C_lie_Cpow j) (GapSelection.Cpow_degree j)


-- @@ L2691-2696 verbatim
theorem actual_image_positive {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot} {n r : ℕ}
    (hn : 1<n) (hψ : embed ψ∈homogeneous (fun _ => 1) n)
    (hp : under p=embed ψ) (hanti : BaseChangeEquations.antisymmetry ψ=0)
    (hr : embed p∈above bCount r) (hr0 : r≠0) :
    ∃ q : FreeLieAlgebra K ℕ,positiveInput (embed q)=embed (leading r p) :=
  shift_invariant_generation hr0 (leading_bcount r p) (leading_shift_invariant hn hψ hp hanti hr)


-- @@ L2698-2698 verbatim
end


-- @@ L2700-2700 verbatim
open AssociativeElimination UniversalEmbedding WordGrading QuadraticLeading

-- @@ L2701-2701 verbatim
open RowTwo RowKernel ExactPentagon AlphabetTransport

-- @@ L2702-2702 verbatim
attribute [local instance] LieRing.ofAssociativeRing


-- @@ L2704-2715 verbatim
theorem degree_bcount_zero (w : FreeMonoid Bool) (hw : degree OreShift.wt w=0) :
    ∀ b∈w.toList,b=false := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp
  | of_mul b w ih =>
    rw [degree_mul,degree_of] at hw
    have hb : b=false := by cases b <;> simp_all [OreShift.wt]
    have ht : degree OreShift.wt w=0 := by omega
    intro c hc
    rcases List.mem_cons.mp hc with h | h
    · exact h.trans hb
    · exact ih ht c h


-- @@ L2717-2720 verbatim
theorem leading_zero_count {p : FreeLieAlgebra K Slot} {n : ℕ} (hn : n≠2)
    (hp : embed p∈homogeneous weight n) : leading 0 p=0 := by
  apply LetterRetraction.homogeneous_single_zero false (wt:=cbWeight) hn ?_ (leading_weight hp 0)
  exact space_mono (fun w hw => degree_bcount_zero w hw) (leading_bcount 0 p)


-- @@ L2722-2729 verbatim
theorem positiveInput_degree (wt : Bool → ℕ) (n : ℕ) :
    positiveInput (atom n)∈homogeneous wt ((n+1)*wt false+wt true) := by
  rw [positiveInput_atom,EvenIndex.input_atom]
  have h := EliminationGraded.adWord_degree (R:=K) (n+1) () (wt ∘ bitOption.symm)
  apply algHom_homogeneous (renameAssoc bitOption.symm) (wt ∘ bitOption.symm) wt ?_ h
  intro b
  rw [renameAssoc_atom]
  exact word_mem _ (degree_of wt _)


-- @@ L2731-2732 verbatim
theorem positiveInput_bcount (n : ℕ) : positiveInput (atom n)∈homogeneous OreShift.wt 1 := by
  simpa only [OreShift.wt,Bool.false_eq_true,ite_false,ite_true,mul_zero,zero_add] using positiveInput_degree OreShift.wt n


-- @@ L2734-2734 verbatim
def oddWeight (n : ℕ) : ℕ := 2*(n+1)+1


-- @@ L2736-2737 verbatim
theorem positiveInput_weight (n : ℕ) : positiveInput (atom n)∈homogeneous cbWeight (oddWeight n) := by
  simpa only [oddWeight,cbWeight,Bool.false_eq_true,ite_false,ite_true,Nat.mul_comm] using positiveInput_degree cbWeight n


-- @@ L2739-2747 verbatim
theorem image_graded {p : FreeLieAlgebra K Bool} {n r : ℕ}
    (hw : embed p∈homogeneous cbWeight n) (hr : embed p∈homogeneous OreShift.wt r)
    {q : FreeLieAlgebra K ℕ} (hq : positiveInput (embed q)=embed p) :
    embed q∈homogeneous oddWeight n ∧ embed q∈homogeneous (fun _ => 1) r := by
  constructor
  · apply homogeneous_reflect positiveInput oddWeight cbWeight positiveInput_weight positiveInput_injective
    rw [hq]; exact hw
  · apply homogeneous_reflect positiveInput (fun _ => 1) OreShift.wt positiveInput_bcount positiveInput_injective
    rw [hq]; exact hr


-- @@ L2749-2761 verbatim
theorem actual_image {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot} {n r : ℕ}
    (hn : 2<n) (hψ : embed ψ∈homogeneous (fun _ => 1) n)
    (hp : under p=embed ψ) (hanti : BaseChangeEquations.antisymmetry ψ=0)
    (hr : embed p∈above bCount r) :
    ∃ q : FreeLieAlgebra K ℕ,positiveInput (embed q)=embed (leading r p) ∧
      embed q∈homogeneous oddWeight n ∧ embed q∈homogeneous (fun _ => 1) r := by
  by_cases hr0 : r=0
  · subst r
    refine ⟨0,?_,by simp,by simp⟩
    rw [leading_zero_count (by omega) (representation_weight hψ hp)]
    simp
  · obtain ⟨q,hq⟩ := actual_image_positive (by omega) hψ hp hanti hr hr0
    exact ⟨q,hq,image_graded (leading_weight (representation_weight hψ hp) r) (leading_bcount r p) hq⟩


-- @@ L2763-2772 verbatim
theorem leading_D_zero {ψ : FreeLieAlgebra K Bool} {p : FreeLieAlgebra K Slot} {n r : ℕ}
    (hn : 1<n) (hψ : embed ψ∈homogeneous (fun _ => 1) n)
    (hp : under p=embed ψ) (hanti : BaseChangeEquations.antisymmetry ψ=0)
    (hr : embed p∈above bCount r) : OreShift.D (embed (leading r p))=0 := by
  have h := OreShift.shiftDeriv_zero (GapSelection.Cpow_degree (R:=K) 1) (leading_bcount r p)
    (leading_shift_invariant hn hψ hp hanti hr 1)
  have he : OreShift.shiftDeriv ((OreShift.C : A K Bool)^1)=OreShift.D := by
    simp only [pow_one,OreShift.shiftDeriv,OreShift.D]
  rw [he] at h
  exact h


-- @@ L2774-2774 verbatim
end ImageBound

-- @@ L2775-2775 verbatim
end DeligneDrinfeld


-- @@ L2777-2777 verbatim
end


-- @@ L2779-2779 verbatim
end OAI
