import OAI.Algebra.Drinfeld.RealBraid


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section


-- @@ L7-7 verbatim
namespace RealDeligneDrinfeld.FreeCutoffCategory

-- @@ L8-8 verbatim
open DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading

-- @@ L9-9 verbatim
open DeligneDrinfeld.TruncatedWords

-- @@ L10-10 verbatim
attribute [local instance] LieRing.ofAssociativeRing

-- @@ L11-11 verbatim
abbrev P : Set (DeligneDrinfeld.AssociativeElimination.A ℝ Bool) := ∅

-- @@ L12-12 verbatim
abbrev Q (N : ℕ) := DeligneDrinfeld.TruncatedWords.Q P N

-- @@ L13-13 verbatim
abbrev F (N n : ℕ) := filtration P N n

 
-- @@ L15-15 verbatim
def j (N : ℕ) : L →ₗ⁅ℝ⁆ Q N := (quotient P N).toLieHom.comp embed
 
-- @@ L16-18 verbatim
@[simp] theorem j_of (N : ℕ) (a : Bool) : j N (FreeLieAlgebra.of ℝ a)=DeligneDrinfeld.TruncatedDerivation.gen P N a := by
  change quotient P N (embed (FreeLieAlgebra.of ℝ a))=_
  rw [embed_of]; rfl
 
-- @@ L19-21 verbatim
theorem j_mem {N n : ℕ} {q : L} (hq : q∈Ln n) : j N q∈F N n := by
  refine ⟨embed q,?_,rfl⟩
  exact space_mono (by intro w hw; exact le_of_eq hw.symm) (WeightBridge.embed_homogeneous hq)
 
-- @@ L22-24 verbatim
theorem lie_mem {N r s : ℕ} {a b : Q N} (ha : a∈F N r) (hb : b∈F N s) : ⁅a,b⁆∈F N (r+s) :=
  (F N (r+s)).sub_mem (filtration_mul P N r s ha hb)
    (by simpa only [Nat.add_comm s r] using filtration_mul P N s r hb ha)

 
-- @@ L26-26 verbatim
def velocity (N : ℕ) (q : L) (a : Bool) : Q N := j N (RealDeligneDrinfeld.derivation q (FreeLieAlgebra.of ℝ a))
 
-- @@ L27-33 verbatim
theorem velocity_mem {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) (a : Bool) : velocity N q a∈F N (n+1) := by
  cases a
  · change j N (RealDeligneDrinfeld.derivation q x)∈_
    simp only [derivation_apply,D_x,map_zero,Submodule.zero_mem]
  · change j N (RealDeligneDrinfeld.derivation q y)∈_
    rw [derivation_apply,D_y,LieHom.map_lie]
    simpa only [Nat.add_comm 1 n] using lie_mem (j_mem (N:=N) WeightBridge.y_mem) (j_mem (N:=N) hq)

 
-- @@ L35-36 verbatim
def d {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) : Module.End ℝ (Q N) :=
  DeligneDrinfeld.TruncatedDerivation.derivation P N n (velocity N q) (velocity_mem N hq) (by intros p hp; exact False.elim hp)

 
-- @@ L38-39 verbatim
theorem d_one {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) : d N hq 1=0 :=
  DeligneDrinfeld.TruncatedDerivation.derivation_one P N n _ _ _
 
-- @@ L40-42 verbatim
theorem d_mul {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) (a b : Q N) :
    d N hq (a*b)=d N hq a*b+a*d N hq b :=
  DeligneDrinfeld.TruncatedDerivation.derivation_mul P N n _ _ _ a b
 
-- @@ L43-44 verbatim
theorem d_mem {n m : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) {a : Q N} (ha : a∈F N m) :
    d N hq a∈F N (m+n) := DeligneDrinfeld.TruncatedDerivation.derivation_mem P N n _ _ _ ha
 
-- @@ L45-48 verbatim
theorem d_j {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) (p : L) :
    d N hq (j N p)=j N (RealDeligneDrinfeld.derivation q p) :=
  DeligneDrinfeld.PresentedCutoff.derivation_embed P N n _ _ _ (RealDeligneDrinfeld.derivation q)
    (LieHom.id) (j N) (j_of N) (fun _ => rfl) p

 
-- @@ L50-50 verbatim
def h (N : ℕ) (q : L) (p : Fin 3) : Q N := j N ((ThreeSolutionCategory.data q).h p)
 
-- @@ L51-58 verbatim
theorem h_mem {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) (p : Fin 3) : h N q p∈F N n := by
  have hr : CategoricalValues.rotateLie q∈Ln n :=
    WeightBridge.eval_mem hq WeightBridge.y_mem ((Ln 1).sub_mem ((Ln 1).neg_mem WeightBridge.x_mem) WeightBridge.y_mem)
  unfold h ThreeSolutionCategory.data
  fin_cases p
  · change j N 0∈F N n; rw [map_zero]; exact Submodule.zero_mem _
  · exact j_mem hq
  · exact j_mem ((Ln n).add_mem hq hr)

 
-- @@ L60-61 verbatim
def data {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) : DeligneDrinfeld.CategoryExp.Data ℝ (Q N) (Fin 3) :=
  DeligneDrinfeld.CategoryExp.gauge (d N hq) (d_mul N hq) (d_one N hq) (h N q)

 
-- @@ L63-68 verbatim
theorem loop_j {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) (p : Fin 3) (a : L) :
    (data N hq).D p p (j N a)=j N (DeligneDrinfeld.CategoryGauge.loop (ThreeSolutionCategory.data q) p a) := by
  change d N hq (j N a)+h N q p*j N a-j N a*h N q p=_
  rw [d_j,DeligneDrinfeld.CategoryGauge.loop_apply,map_add,LieHom.map_lie,Ring.lie_def]
  change _=j N (RealDeligneDrinfeld.derivation q a)+(h N q p*j N a-j N a*h N q p)
  abel
 
-- @@ L69-73 verbatim
theorem unit_all {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) (p s : Fin 3) :
    (data N hq).D p s 1=j N (DeligneDrinfeld.CategoryGauge.unit (ThreeSolutionCategory.data q) p s) := by
  change d N hq 1+h N q s*1-1*h N q p=_
  rw [d_one,zero_add,mul_one,one_mul,DeligneDrinfeld.CategoryGauge.unit,map_sub]
  rfl

 
-- @@ L75-78 verbatim
theorem raises {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) (p s : Fin 3)
    (m : ℕ) (a : Q N) (ha : a∈F N m) : (data N hq).D p s a∈F N (m+n) :=
  DeligneDrinfeld.CutoffCategory.raises P N (d N hq) (d_mul N hq) (d_one N hq) (h N q) n
    (fun _ _ ha => d_mem N hq ha) (h_mem N hq) p s m a ha

 
-- @@ L80-83 verbatim
theorem nilpotent {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) (hn : 0<n) (p s : Fin 3) :
    IsNilpotent ((data N hq).D p s) :=
  DeligneDrinfeld.CutoffCategory.nilpotent P N (d N hq) (d_mul N hq) (d_one N hq) (h N q) n hn
    (fun _ _ ha => d_mem N hq ha) (h_mem N hq) p s

 
-- @@ L85-88 verbatim
theorem unit {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) : (data N hq).D 0 1 1=j N q := by
  change (d N hq 1+h N q 1*1)-1*h N q 0=_
  rw [d_one]
  simp [h,ThreeSolutionCategory.data]

 
-- @@ L90-95 verbatim
theorem leading {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) (hn : 0<n)
    {a : Q N} (ha : a-1∈F N 1) :
    DeligneDrinfeld.CategoryExp.act (data N hq) 0 1 a-a-j N q∈F N (n+1) := by
  rw [←unit N hq]
  exact DeligneDrinfeld.CategoryExp.unit_leading (DeligneDrinfeld.CutoffCategory.filtration P N)
    _ n (raises N hq 0 1) hn (filtration_one P N) ha


-- @@ L97-97 verbatim
end RealDeligneDrinfeld.FreeCutoffCategory


-- @@ L99-99 verbatim
namespace RealDeligneDrinfeld.BraidCutoff

-- @@ L100-100 verbatim
open DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading

-- @@ L101-101 verbatim
open DeligneDrinfeld.TruncatedWords

-- @@ L102-102 verbatim
attribute [local instance] LieRing.ofAssociativeRing


-- @@ L104-105 verbatim
def presentation : Set (DeligneDrinfeld.AssociativeElimination.A ℝ Edge) :=
  DeligneDrinfeld.AssociativeElimination.embed '' braidRelations

-- @@ L106-106 verbatim
abbrev Q (N : ℕ) := DeligneDrinfeld.TruncatedWords.Q presentation N

-- @@ L107-107 verbatim
abbrev F (N n : ℕ) := filtration presentation N n


-- @@ L109-110 verbatim
def freeMap (N : ℕ) : BraidFree →ₗ⁅ℝ⁆ Q N :=
  (quotient presentation N).toLieHom.comp DeligneDrinfeld.AssociativeElimination.embed


-- @@ L112-113 verbatim
theorem freeMap_relation (N : ℕ) {p : BraidFree} (hp : p∈braidRelations) : freeMap N p=0 :=
  quotient_relation presentation N ⟨p,hp,rfl⟩


-- @@ L115-125 verbatim
def lieMap (N : ℕ) : T4 →ₗ⁅ℝ⁆ Q N := by
  have hk : braidIdeal ≤ (freeMap N).ker := by
    rw [braidIdeal,LieSubmodule.lieSpan_le]
    intro p hp
    exact freeMap_relation N hp
  exact { braidIdeal.toSubmodule.liftQ (freeMap N).toLinearMap hk with
    map_lie' := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | _ a =>
        induction b using Submodule.Quotient.induction_on with | _ b =>
          exact (freeMap N).map_lie a b }


-- @@ L127-129 verbatim
def projection : BraidFree →ₗ⁅ℝ⁆ T4 where
  toLinearMap := braidIdeal.toSubmodule.mkQ
  map_lie' := rfl


-- @@ L131-131 verbatim
@[simp] theorem lieMap_projection (N : ℕ) (p : BraidFree) : lieMap N (projection p)=freeMap N p := rfl

-- @@ L132-133 verbatim
@[simp] theorem projection_of (a : Edge) : projection (FreeLieAlgebra.of ℝ a)=t a.val.1 a.val.2 := by
  simp only [t,chord,dite_eq_left a.property]; rfl
 
-- @@ L134-138 verbatim
theorem lieMap_of (N : ℕ) (a : Edge) : lieMap N (projection (FreeLieAlgebra.of ℝ a))=
    DeligneDrinfeld.TruncatedDerivation.gen presentation N a := by
  rw [lieMap_projection]
  change quotient presentation N (DeligneDrinfeld.AssociativeElimination.embed (FreeLieAlgebra.of ℝ a))=_
  rw [DeligneDrinfeld.AssociativeElimination.embed_of]; rfl

 
-- @@ L140-141 verbatim
theorem projection_relation {p : BraidFree} (hp : p∈braidRelations) : projection p=0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (LieSubmodule.subset_lieSpan hp)

 
-- @@ L143-145 verbatim
theorem lie_mem {N r s : ℕ} {a b : Q N} (ha : a∈F N r) (hb : b∈F N s) : ⁅a,b⁆∈F N (r+s) := by
  exact (F N (r+s)).sub_mem (filtration_mul presentation N r s ha hb)
    (by simpa only [Nat.add_comm s r] using filtration_mul presentation N s r hb ha)
 
-- @@ L146-155 verbatim
theorem t_mem (N : ℕ) (i j : Fin 4) : lieMap N (t i j)∈F N 1 := by
  unfold t chord
  split_ifs with hij hji
  · change lieMap N (projection (FreeLieAlgebra.of ℝ ⟨(i,j),hij⟩))∈_
    rw [lieMap_of]
    exact DeligneDrinfeld.TruncatedDerivation.gen_mem presentation N _
  · change lieMap N (projection (FreeLieAlgebra.of ℝ ⟨(j,i),hji⟩))∈_
    rw [lieMap_of]
    exact DeligneDrinfeld.TruncatedDerivation.gen_mem presentation N _
  · change lieMap N 0∈_; rw [map_zero]; exact Submodule.zero_mem _

 
-- @@ L157-170 verbatim
theorem weight_mem {α : Type*} (N : ℕ) (e : FreeLieAlgebra ℝ α →ₗ⁅ℝ⁆ Q N)
    (he : ∀ a,e (FreeLieAlgebra.of ℝ a)∈F N 1) {n : ℕ} {q : FreeLieAlgebra ℝ α}
    (hq : q∈weightPiece (fun _ : α => 1) n) : e q∈F N n := by
  have hw : ∀ n p,WeightedWord (fun _ : α => 1) n p → e p∈F N n := by
    intro n p hp
    induction hp with
    | generator a => exact he a
    | bracket hp hr ihp ihr => rw [LieHom.map_lie]; exact lie_mem ihp ihr
  apply Submodule.span_induction (p:=fun q _ => e q∈F N n) ?_ ?_ ?_ ?_ hq
  · intro p hp
    exact hw n p hp
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro p r _ _ hp hr; rw [map_add]; exact Submodule.add_mem _ hp hr
  · intro s p _ hp; rw [map_smul]; exact Submodule.smul_mem _ s hp

 
-- @@ L172-175 verbatim
theorem eval_mem {N n : ℕ} {q : L} (hq : q∈Ln n) {a b : T4}
    (ha : lieMap N a∈F N 1) (hb : lieMap N b∈F N 1) : lieMap N (eval a b q)∈F N n := by
  apply weight_mem N ((lieMap N).comp (eval a b)) (fun i => ?_) hq
  cases i <;> simpa [eval] using (by assumption : lieMap N _∈F N 1)


-- @@ L177-177 verbatim
open T4Basic T4SolutionData

-- @@ L178-178 verbatim
variable {n : ℕ} {q : L}
 
-- @@ L179-180 verbatim
theorem A_mem (N : ℕ) (hq : q∈Ln n) : lieMap N (A q)∈F N n :=
  eval_mem hq (t_mem N 0 1) (t_mem N 1 2)
 
-- @@ L181-182 verbatim
theorem D_mem (N : ℕ) (hq : q∈Ln n) : lieMap N (T4SolutionData.D q)∈F N n :=
  eval_mem hq (by rw [map_add]; exact Submodule.add_mem _ (t_mem N 0 2) (t_mem N 1 2)) (t_mem N 2 3)
 
-- @@ L183-184 verbatim
theorem E_mem (N : ℕ) (hq : q∈Ln n) : lieMap N (E q)∈F N n :=
  eval_mem hq (t_mem N 0 1) (by rw [map_add]; exact Submodule.add_mem _ (t_mem N 1 2) (t_mem N 1 3))

 
-- @@ L186-187 verbatim
def velocity (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (a : Edge) : Q N :=
  lieMap N (T4Derivation.derivation hq hqn hn (projection (FreeLieAlgebra.of ℝ a)))

 
-- @@ L189-220 verbatim
theorem velocity_mem (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (ij : Edge) :
    velocity N hq hqn hn ij∈F N (n+1) := by
  have hA := A_mem N hqn
  have hD := D_mem N hqn
  have hE := E_mem N hqn
  have hb : lieMap N b∈F N 1 := t_mem N 1 2
  have hc : lieMap N c∈F N 1 := t_mem N 2 3
  have he : lieMap N e∈F N 1 := t_mem N 1 3
  have hbA : ⁅lieMap N b,lieMap N (A q)⁆∈F N (n+1) := by simpa [Nat.add_comm] using lie_mem hb hA
  have hcD : ⁅lieMap N c,lieMap N (T4SolutionData.D q)⁆∈F N (n+1) := by simpa [Nat.add_comm] using lie_mem hc hD
  have heDE : ⁅lieMap N (b+e),lieMap N (T4SolutionData.D q+E q)⁆∈F N (n+1) := by
    rw [map_add,map_add]
    simpa [Nat.add_comm] using lie_mem (Submodule.add_mem _ hb he) (Submodule.add_mem _ hD hE)
  have hall (i j : Fin 4) : lieMap N (T4Derivation.derivation hq hqn hn (t i j))∈F N (n+1) := by
    have ha : lieMap N (T4Derivation.derivation hq hqn hn a)∈F N (n+1) := by simp
    have hb' : lieMap N (T4Derivation.derivation hq hqn hn b)∈F N (n+1) := by
      rw [T4Derivation.derivation_b,LieHom.map_lie]; exact hbA
    have hc' : lieMap N (T4Derivation.derivation hq hqn hn c)∈F N (n+1) := by
      rw [T4Derivation.derivation_c,LieHom.map_lie]; exact hcD
    have hd' : lieMap N (T4Derivation.derivation hq hqn hn d)∈F N (n+1) := by
      rw [T4Derivation.derivation_d,map_neg,LieHom.map_lie]; exact Submodule.neg_mem _ hbA
    have he' : lieMap N (T4Derivation.derivation hq hqn hn e)∈F N (n+1) := by
      rw [T4Derivation.derivation_e,map_sub,LieHom.map_lie,LieHom.map_lie]
      exact Submodule.sub_mem _ heDE hbA
    have hf' : lieMap N (T4Derivation.derivation hq hqn hn f)∈F N (n+1) := by
      rw [T4Derivation.derivation_f,map_sub,map_neg,LieHom.map_lie,map_sub,LieHom.map_lie,LieHom.map_lie]
      exact Submodule.sub_mem _ (Submodule.neg_mem _ hcD) (Submodule.sub_mem _ heDE hbA)
    fin_cases i <;> fin_cases j
    all_goals first | simpa only [t_self,map_zero] using (Submodule.zero_mem (F N (n+1))) | exact ha | exact hb' | exact hc' | exact hd' | exact he' | exact hf'
  unfold velocity
  rw [projection_of]
  exact hall _ _

 
-- @@ L222-228 verbatim
theorem relations_killed (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n)
    (p : DeligneDrinfeld.AssociativeElimination.A ℝ Edge) (hp : p∈presentation) :
    DeligneDrinfeld.TruncatedDerivation.raw presentation N (velocity N hq hqn hn) p=0 := by
  obtain ⟨p,hp,rfl⟩ := hp
  unfold velocity
  rw [DeligneDrinfeld.PresentedCutoff.raw_embed presentation N (T4Derivation.derivation hq hqn hn)
    projection (lieMap N) (lieMap_of N) p,projection_relation hp,map_zero,map_zero]

 
-- @@ L230-232 verbatim
def derivation (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : Module.End ℝ (Q N) :=
  DeligneDrinfeld.TruncatedDerivation.derivation presentation N n (velocity N hq hqn hn)
    (velocity_mem N hq hqn hn) (relations_killed N hq hqn hn)

 
-- @@ L234-238 verbatim
theorem derivation_lieMap (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (p : T4) :
    derivation N hq hqn hn (lieMap N p)=lieMap N (T4Derivation.derivation hq hqn hn p) := by
  induction p using Submodule.Quotient.induction_on with | _ p =>
    exact DeligneDrinfeld.PresentedCutoff.derivation_embed presentation N n _ _ _ _ projection
      (lieMap N) (lieMap_of N) (fun _ => rfl) p


-- @@ L240-240 verbatim
end RealDeligneDrinfeld.BraidCutoff


-- @@ L242-242 verbatim
namespace RealDeligneDrinfeld.BraidCategoryExp

-- @@ L243-243 verbatim
open DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading

-- @@ L244-244 verbatim
open DeligneDrinfeld.TruncatedWords BraidCutoff T4Basic T4SolutionData

-- @@ L245-245 verbatim
attribute [local instance] LieRing.ofAssociativeRing

-- @@ L246-246 verbatim
variable {n : ℕ} {q : L}
 
-- @@ L247-249 verbatim
theorem B_mem (N : ℕ) (hq : q∈Ln n) : lieMap N (B q)∈BraidCutoff.F N n :=
  eval_mem hq (by rw [map_add]; exact Submodule.add_mem _ (t_mem N 0 1) (t_mem N 0 2))
    (by rw [map_add]; exact Submodule.add_mem _ (t_mem N 1 3) (t_mem N 2 3))

 
-- @@ L251-252 verbatim
def h (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (p : Fin 5) : BraidCutoff.Q N :=
  lieMap N ((FourSolutionCategory.data hq hqn hn).h p)
 
-- @@ L253-262 verbatim
theorem h_mem (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (p : Fin 5) : h N hq hqn hn p∈BraidCutoff.F N n := by
  unfold h FourSolutionCategory.data
  fin_cases p
  · change lieMap N 0∈BraidCutoff.F N n; rw [map_zero]; exact Submodule.zero_mem _
  · exact A_mem N hqn
  · change lieMap N (A q+B q)∈_; rw [map_add]
    exact Submodule.add_mem _ (A_mem N hqn) (B_mem N hqn)
  · exact D_mem N hqn
  · change lieMap N (T4SolutionData.D q+E q)∈_; rw [map_add]
    exact Submodule.add_mem _ (D_mem N hqn) (E_mem N hqn)

 
-- @@ L264-265 verbatim
theorem d_one (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : BraidCutoff.derivation N hq hqn hn 1=0 :=
  DeligneDrinfeld.TruncatedDerivation.derivation_one presentation N n _ _ _
 
-- @@ L266-268 verbatim
theorem d_mul (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (a b : BraidCutoff.Q N) :
    BraidCutoff.derivation N hq hqn hn (a*b)=BraidCutoff.derivation N hq hqn hn a*b+a*BraidCutoff.derivation N hq hqn hn b :=
  DeligneDrinfeld.TruncatedDerivation.derivation_mul presentation N n _ _ _ a b
 
-- @@ L269-271 verbatim
theorem d_mem (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) {m : ℕ} {a : BraidCutoff.Q N} (ha : a∈BraidCutoff.F N m) :
    BraidCutoff.derivation N hq hqn hn a∈BraidCutoff.F N (m+n) :=
  DeligneDrinfeld.TruncatedDerivation.derivation_mem presentation N n _ _ _ ha

 
-- @@ L273-274 verbatim
def data (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) : DeligneDrinfeld.CategoryExp.Data ℝ (BraidCutoff.Q N) (Fin 5) :=
  DeligneDrinfeld.CategoryExp.gauge (BraidCutoff.derivation N hq hqn hn) (d_mul N hq hqn hn) (d_one N hq hqn hn) (h N hq hqn hn)

 
-- @@ L276-279 verbatim
theorem raises (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (p s : Fin 5) (m : ℕ) (a : BraidCutoff.Q N)
    (ha : a∈BraidCutoff.F N m) : (data N hq hqn hn).D p s a∈BraidCutoff.F N (m+n) :=
  DeligneDrinfeld.CutoffCategory.raises presentation N _ _ _ _ n
    (fun _ _ ha => d_mem N hq hqn hn ha) (h_mem N hq hqn hn) p s m a ha

 
-- @@ L281-284 verbatim
theorem nilpotent (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (p s : Fin 5) :
    IsNilpotent ((data N hq hqn hn).D p s) :=
  DeligneDrinfeld.CutoffCategory.nilpotent presentation N _ _ _ _ n (by omega)
    (fun _ _ ha => d_mem N hq hqn hn ha) (h_mem N hq hqn hn) p s

 
-- @@ L286-295 verbatim
theorem loop_lieMap (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (p : Fin 5) (a : T4) :
    (data N hq hqn hn).D p p (lieMap N a)=
      lieMap N (DeligneDrinfeld.CategoryGauge.loop (FourSolutionCategory.data hq hqn hn) p a) := by
  change BraidCutoff.derivation N hq hqn hn (lieMap N a)+h N hq hqn hn p*lieMap N a-lieMap N a*h N hq hqn hn p=_
  rw [derivation_lieMap]
  rw [DeligneDrinfeld.CategoryGauge.loop_apply,map_add,LieHom.map_lie,Ring.lie_def]
  change _= _+(h N hq hqn hn p*lieMap N a-lieMap N a*h N hq hqn hn p)
  change lieMap N (T4Derivation.derivation hq hqn hn a)+h N hq hqn hn p*lieMap N a-lieMap N a*h N hq hqn hn p=
    lieMap N (T4Derivation.derivation hq hqn hn a)+(h N hq hqn hn p*lieMap N a-lieMap N a*h N hq hqn hn p)
  abel

 
-- @@ L297-301 verbatim
theorem unit (N : ℕ) (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n) (p s : Fin 5) :
    (data N hq hqn hn).D p s 1=lieMap N (DeligneDrinfeld.CategoryGauge.unit (FourSolutionCategory.data hq hqn hn) p s) := by
  change BraidCutoff.derivation N hq hqn hn 1+h N hq hqn hn s*1-1*h N hq hqn hn p=_
  rw [d_one,zero_add,mul_one,one_mul,DeligneDrinfeld.CategoryGauge.unit,map_sub]
  rfl

-- @@ L302-302 verbatim
end RealDeligneDrinfeld.BraidCategoryExp


-- @@ L304-304 verbatim
namespace RealDeligneDrinfeld.BraidInsertionExp

-- @@ L305-305 verbatim
open DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading

-- @@ L306-306 verbatim
open DeligneDrinfeld.TruncatedWords DeligneDrinfeld.CategoryGauge

-- @@ L307-307 verbatim
attribute [local instance] LieRing.ofAssociativeRing

-- @@ L308-309 verbatim
variable (N : ℕ) (X Y : T4)
  (hX : BraidCutoff.lieMap N X∈BraidCutoff.F N 1) (hY : BraidCutoff.lieMap N Y∈BraidCutoff.F N 1)
 
-- @@ L310-310 verbatim
def family (a : Bool) : BraidCutoff.Q N := if a then BraidCutoff.lieMap N Y else BraidCutoff.lieMap N X

-- @@ L311-313 verbatim
include hX hY in
 theorem family_mem (a : Bool) : family N X Y a∈BraidCutoff.F N 1 := by
  cases a <;> assumption
 
-- @@ L314-315 verbatim
def insert : FreeCutoffCategory.Q N →ₐ[ℝ] BraidCutoff.Q N :=
  DeligneDrinfeld.PresentedSubstitution.subst BraidCutoff.presentation N (family N X Y) (family_mem N X Y hX hY)
 
-- @@ L316-317 verbatim
theorem insert_gen (a : Bool) : insert N X Y hX hY (DeligneDrinfeld.TruncatedDerivation.gen ∅ N a)=family N X Y a :=
  DeligneDrinfeld.PresentedSubstitution.subst_gen _ _ _ _ a
 
-- @@ L318-326 verbatim
theorem insert_j (p : L) : insert N X Y hX hY (FreeCutoffCategory.j N p)=BraidCutoff.lieMap N (eval X Y p) := by
  have he : (insert N X Y hX hY).toLieHom.comp (FreeCutoffCategory.j N)=
      (BraidCutoff.lieMap N).comp (eval X Y) := by
    apply FreeLieAlgebra.hom_ext
    intro a
    change insert N X Y hX hY (FreeCutoffCategory.j N (FreeLieAlgebra.of ℝ a))=_
    rw [FreeCutoffCategory.j_of,insert_gen]
    cases a <;> simp [family,eval]
  exact LieHom.congr_fun he p

 
-- @@ L328-328 verbatim
variable {n : ℕ} {q : L} (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n)
 
-- @@ L329-339 verbatim
theorem edge (s t : Fin 5)
    (he : EdgeCompatible (eval X Y) 0 1 s t (ThreeSolutionCategory.data q) (FourSolutionCategory.data hq hqn hn))
    (a : FreeCutoffCategory.Q N) :
    DeligneDrinfeld.CategoryExp.act (BraidCategoryExp.data N hq hqn hn) s t (insert N X Y hX hY a)=
      insert N X Y hX hY (DeligneDrinfeld.CategoryExp.act (FreeCutoffCategory.data N hqn) 0 1 a) := by
  apply DeligneDrinfeld.CutoffCategory.exp_edge FreeCutoffCategory.P N
    (FreeCutoffCategory.data N hqn) (BraidCategoryExp.data N hq hqn hn) (insert N X Y hX hY) 0 s
    (FreeCutoffCategory.nilpotent N hqn (by omega)) (BraidCategoryExp.nilpotent N hq hqn hn) 1 t
  · rw [BraidCategoryExp.unit,FreeCutoffCategory.unit_all,insert_j,he.1]
  · intro b
    rw [←FreeCutoffCategory.j_of,insert_j,BraidCategoryExp.loop_lieMap,FreeCutoffCategory.loop_j,insert_j,he.2]

 
-- @@ L341-341 verbatim
open T4Basic
 
-- @@ L342-342 verbatim
abbrev IAB := insert N a b (BraidCutoff.t_mem N 0 1) (BraidCutoff.t_mem N 1 2)
 
-- @@ L343-343 verbatim
abbrev IAD := insert N (d+b) c (by rw [map_add]; exact Submodule.add_mem _ (BraidCutoff.t_mem N 0 2) (BraidCutoff.t_mem N 1 2)) (BraidCutoff.t_mem N 2 3)
 
-- @@ L344-344 verbatim
abbrev IDE := insert N a (b+e) (BraidCutoff.t_mem N 0 1) (by rw [map_add]; exact Submodule.add_mem _ (BraidCutoff.t_mem N 1 2) (BraidCutoff.t_mem N 1 3))
 
-- @@ L345-346 verbatim
abbrev IBC := insert N (a+d) (e+c) (by rw [map_add]; exact Submodule.add_mem _ (BraidCutoff.t_mem N 0 1) (BraidCutoff.t_mem N 0 2))
   (by rw [map_add]; exact Submodule.add_mem _ (BraidCutoff.t_mem N 1 3) (BraidCutoff.t_mem N 2 3))
 
-- @@ L347-347 verbatim
abbrev ICE := insert N b c (BraidCutoff.t_mem N 1 2) (BraidCutoff.t_mem N 2 3)

 
-- @@ L349-367 verbatim
include hq hn in
 theorem pentagon_preserved (a : FreeCutoffCategory.Q N)
    (ha : IDE N a*IAD N a=ICE N a*IBC N a*IAB N a) :
    let a' := DeligneDrinfeld.CategoryExp.act (FreeCutoffCategory.data N hqn) 0 1 a
    IDE N a'*IAD N a'=ICE N a'*IBC N a'*IAB N a' := by
  let F := DeligneDrinfeld.CategoryExp.act (BraidCategoryExp.data N hq hqn hn)
  have hh := congrArg (F 0 4) ha
  have hn' := BraidCategoryExp.nilpotent N hq hqn hn
  rw [DeligneDrinfeld.CategoryExp.composition _ hn' 0 3 4,
    DeligneDrinfeld.CategoryExp.composition _ hn' 0 1 4,
    DeligneDrinfeld.CategoryExp.composition _ hn' 1 2 4] at hh
  let a' := DeligneDrinfeld.CategoryExp.act (FreeCutoffCategory.data N hqn) 0 1 a
  have hDE : F 3 4 (IDE N a)=IDE N a' := edge N _ _ _ _ hq hqn hn 3 4 (FourSolutionCategory.DE hq hqn hn) a
  have hAD : F 0 3 (IAD N a)=IAD N a' := edge N _ _ _ _ hq hqn hn 0 3 (FourSolutionCategory.AD hq hqn hn) a
  have hCE : F 2 4 (ICE N a)=ICE N a' := edge N _ _ _ _ hq hqn hn 2 4 (FourSolutionCategory.CE hq hqn hn) a
  have hBC : F 1 2 (IBC N a)=IBC N a' := edge N _ _ _ _ hq hqn hn 1 2 (FourSolutionCategory.BC hq hqn hn) a
  have hAB : F 0 1 (IAB N a)=IAB N a' := edge N _ _ _ _ hq hqn hn 0 1 (FourSolutionCategory.AB hq hqn hn) a
  rw [hDE,hAD,hCE,hBC,hAB] at hh
  exact hh

-- @@ L368-368 verbatim
end RealDeligneDrinfeld.BraidInsertionExp


-- @@ L370-370 verbatim
namespace DeligneDrinfeld.CategoryExp

-- @@ L371-372 verbatim
variable {R A B O P I : Type*} [CommRing R] [Ring A] [Algebra R A]
  [Ring B] [Algebra R B]
 
-- @@ L373-381 verbatim
def sum (s : Finset I) (g : I → Data R A O) : Data R A O where
  D p q := ∑ i∈s,(g i).D p q
  comp p q r a b := by
    simp only [LinearMap.sum_apply]
    rw [Finset.sum_mul,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _hi
    exact (g i).comp p q r a b
  one p := by simp only [LinearMap.sum_apply,Data.one,Finset.sum_const_zero]
 
-- @@ L382-383 verbatim
theorem sum_apply (s : Finset I) (g : I → Data R A O) (p q : O) (a : A) :
    (sum s g).D p q a=∑ i∈s,(g i).D p q a := LinearMap.sum_apply _ _ _
 
-- @@ L384-390 verbatim
theorem sum_raises {N : ℕ} (F : FilteredComparison.Filtration R A N)
    (s : Finset I) (g : I → Data R A O)
    (hg : ∀ i∈s,∀ p q m a,a∈F.step m → (g i).D p q a∈F.step (m+1))
    (p q : O) (m : ℕ) (a : A) (ha : a∈F.step m) :
    (sum s g).D p q a∈F.step (m+1) := by
  rw [sum_apply]
  exact Submodule.sum_mem _ (fun i hi => hg i hi p q m a ha)
 
-- @@ L391-395 verbatim
theorem sum_nilpotent {N : ℕ} (F : FilteredComparison.Filtration R A N)
    (s : Finset I) (g : I → Data R A O)
    (hg : ∀ i∈s,∀ p q m a,a∈F.step m → (g i).D p q a∈F.step (m+1))
    (p q : O) : IsNilpotent ((sum s g).D p q) :=
  nilpotent F _ (sum_raises F s g hg p q)
 
-- @@ L396-401 verbatim
theorem sum_natural (s : Finset I) (g : I → Data R A O) (k : I → Data R B P)
    (f : A →ₗ[R] B) (p q : O) (r t : P)
    (hf : ∀ i∈s,∀ a,(k i).D r t (f a)=f ((g i).D p q a)) (a : A) :
    (sum s k).D r t (f a)=f ((sum s g).D p q a) := by
  rw [sum_apply,sum_apply,map_sum]
  exact Finset.sum_congr rfl (fun i hi => hf i hi a)
 
-- @@ L402-408 verbatim
theorem exp_sum_natural [Module ℚ A] [Module ℚ B]
    (s : Finset I) (g : I → Data R A O) (k : I → Data R B P)
    (f : A →ₗ[R] B) (p q : O) (r t : P)
    (hg : IsNilpotent ((sum s g).D p q)) (hk : IsNilpotent ((sum s k).D r t))
    (hf : ∀ i∈s,∀ a,(k i).D r t (f a)=f ((g i).D p q a)) (a : A) :
    act (sum s k) r t (f a)=f (act (sum s g) p q a) :=
  OperatorExp.natural _ _ hg hk f (sum_natural s g k f p q r t hf) a

-- @@ L409-409 verbatim
end DeligneDrinfeld.CategoryExp


-- @@ L411-411 verbatim
section

-- @@ L412-412 verbatim
namespace RealDeligneDrinfeld.BraidInsertionExp

-- @@ L413-413 verbatim
open DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading

-- @@ L414-414 verbatim
open DeligneDrinfeld.TruncatedWords DeligneDrinfeld.CategoryGauge

-- @@ L415-417 verbatim
variable (N : ℕ) (X Y : T4)
  (hX : BraidCutoff.lieMap N X∈BraidCutoff.F N 1) (hY : BraidCutoff.lieMap N Y∈BraidCutoff.F N 1)
  {n : ℕ} {q : L} (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n)
 
-- @@ L418-427 verbatim
theorem edge_derivative (s t : Fin 5)
    (he : EdgeCompatible (eval X Y) 0 1 s t (ThreeSolutionCategory.data q) (FourSolutionCategory.data hq hqn hn))
    (a : FreeCutoffCategory.Q N) :
    (BraidCategoryExp.data N hq hqn hn).D s t (insert N X Y hX hY a)=
      insert N X Y hX hY ((FreeCutoffCategory.data N hqn).D 0 1 a) := by
  apply DeligneDrinfeld.CutoffCategory.edge_natural FreeCutoffCategory.P N
    (FreeCutoffCategory.data N hqn) (BraidCategoryExp.data N hq hqn hn) (insert N X Y hX hY) 0 s 1 t
  · rw [BraidCategoryExp.unit,FreeCutoffCategory.unit_all,insert_j,he.1]
  · intro b
    rw [←FreeCutoffCategory.j_of,insert_j,BraidCategoryExp.loop_lieMap,FreeCutoffCategory.loop_j,insert_j,he.2]

-- @@ L428-428 verbatim
end RealDeligneDrinfeld.BraidInsertionExp


-- @@ L430-430 verbatim
namespace RealDeligneDrinfeld.BraidInsertionSum

-- @@ L431-431 verbatim
open DeligneDrinfeld.CategoryExp

-- @@ L432-432 verbatim
open BraidInsertionExp

-- @@ L433-434 verbatim
variable {I : Type*} (N : ℕ) (s : Finset I) (q : I → L) (n : I → ℕ)
  (hq : ∀ i,q i∈W) (hqn : ∀ i,q i∈Ln (n i)) (hn : ∀ i,2<n i)
 
-- @@ L435-435 verbatim
def free : Data ℝ (FreeCutoffCategory.Q N) (Fin 3) := sum s (fun i => FreeCutoffCategory.data N (hqn i))
 
-- @@ L436-436 verbatim
def braid : Data ℝ (BraidCutoff.Q N) (Fin 5) := sum s (fun i => BraidCategoryExp.data N (hq i) (hqn i) (hn i))
 
-- @@ L437-443 verbatim
include hn in
 theorem free_raises (p r : Fin 3) (m : ℕ) (a : FreeCutoffCategory.Q N) (ha : a∈FreeCutoffCategory.F N m) :
    (free N s q n hqn).D p r a∈FreeCutoffCategory.F N (m+1) := by
  apply sum_raises (DeligneDrinfeld.CutoffCategory.filtration ∅ N) s _ _ p r m a ha
  intro i _hi p r m a ha
  exact DeligneDrinfeld.TruncatedWords.filtration_antitone ∅ N (by have := hn i; omega)
    (FreeCutoffCategory.raises N (hqn i) p r m a ha)
 
-- @@ L444-449 verbatim
theorem braid_raises (p r : Fin 5) (m : ℕ) (a : BraidCutoff.Q N) (ha : a∈BraidCutoff.F N m) :
    (braid N s q n hq hqn hn).D p r a∈BraidCutoff.F N (m+1) := by
  apply sum_raises (DeligneDrinfeld.CutoffCategory.filtration BraidCutoff.presentation N) s _ _ p r m a ha
  intro i _hi p r m a ha
  exact DeligneDrinfeld.TruncatedWords.filtration_antitone _ N (by have := hn i; omega)
    (BraidCategoryExp.raises N (hq i) (hqn i) (hn i) p r m a ha)
 
-- @@ L450-452 verbatim
include hn in
 theorem free_nilpotent (p r : Fin 3) : IsNilpotent ((free N s q n hqn).D p r) :=
  nilpotent (DeligneDrinfeld.CutoffCategory.filtration ∅ N) _ (free_raises N s q n hqn hn p r)
 
-- @@ L453-454 verbatim
theorem braid_nilpotent (p r : Fin 5) : IsNilpotent ((braid N s q n hq hqn hn).D p r) :=
  nilpotent (DeligneDrinfeld.CutoffCategory.filtration BraidCutoff.presentation N) _ (braid_raises N s q n hq hqn hn p r)
 
-- @@ L455-465 verbatim
theorem edge (X Y : T4)
    (hX : BraidCutoff.lieMap N X∈BraidCutoff.F N 1) (hY : BraidCutoff.lieMap N Y∈BraidCutoff.F N 1)
    (p r : Fin 5)
    (he : ∀ i,DeligneDrinfeld.CategoryGauge.EdgeCompatible (eval X Y) 0 1 p r
      (ThreeSolutionCategory.data (q i)) (FourSolutionCategory.data (hq i) (hqn i) (hn i)))
    (a : FreeCutoffCategory.Q N) :
    act (braid N s q n hq hqn hn) p r (insert N X Y hX hY a)=
      insert N X Y hX hY (act (free N s q n hqn) 0 1 a) := by
  exact exp_sum_natural s _ _ (insert N X Y hX hY).toLinearMap 0 1 p r
    (free_nilpotent N s q n hqn hn 0 1) (braid_nilpotent N s q n hq hqn hn p r)
    (fun i _hi a => edge_derivative N X Y hX hY (hq i) (hqn i) (hn i) p r (he i) a) a
 
-- @@ L466-482 verbatim
include hq hn in
 theorem pentagon (a : FreeCutoffCategory.Q N)
    (ha : IDE N a*IAD N a=ICE N a*IBC N a*IAB N a) :
    let a' := act (free N s q n hqn) 0 1 a
    IDE N a'*IAD N a'=ICE N a'*IBC N a'*IAB N a' := by
  let F := act (braid N s q n hq hqn hn)
  let a' := act (free N s q n hqn) 0 1 a
  have hh := congrArg (F 0 4) ha
  have hn' := braid_nilpotent N s q n hq hqn hn
  rw [composition _ hn' 0 3 4,composition _ hn' 0 1 4,composition _ hn' 1 2 4] at hh
  have hDE : F 3 4 (IDE N a)=IDE N a' := edge N s q n hq hqn hn _ _ _ _ 3 4 (fun i => FourSolutionCategory.DE (hq i) (hqn i) (hn i)) a
  have hAD : F 0 3 (IAD N a)=IAD N a' := edge N s q n hq hqn hn _ _ _ _ 0 3 (fun i => FourSolutionCategory.AD (hq i) (hqn i) (hn i)) a
  have hCE : F 2 4 (ICE N a)=ICE N a' := edge N s q n hq hqn hn _ _ _ _ 2 4 (fun i => FourSolutionCategory.CE (hq i) (hqn i) (hn i)) a
  have hBC : F 1 2 (IBC N a)=IBC N a' := edge N s q n hq hqn hn _ _ _ _ 1 2 (fun i => FourSolutionCategory.BC (hq i) (hqn i) (hn i)) a
  have hAB : F 0 1 (IAB N a)=IAB N a' := edge N s q n hq hqn hn _ _ _ _ 0 1 (fun i => FourSolutionCategory.AB (hq i) (hqn i) (hn i)) a
  rw [hDE,hAD,hCE,hBC,hAB] at hh
  exact hh
 
-- @@ L483-485 verbatim
theorem unit : (free N s q n hqn).D 0 1 1=FreeCutoffCategory.j N (∑ i∈s,q i) := by
  rw [free,DeligneDrinfeld.CategoryExp.sum_apply,map_sum]
  exact Finset.sum_congr rfl (fun i _hi => FreeCutoffCategory.unit N (hqn i))
 
-- @@ L486-490 verbatim
theorem edge_formula (a : FreeCutoffCategory.Q N) :
    (free N s q n hqn).D 0 1 a=(free N s q n hqn).D 0 0 a+FreeCutoffCategory.j N (∑ i∈s,q i)*a := by
  have hh := (free N s q n hqn).comp 0 0 1 a 1
  rw [one_mul,one_mul,unit] at hh
  rw [hh,add_comm]

-- @@ L491-491 verbatim
end RealDeligneDrinfeld.BraidInsertionSum


-- @@ L493-493 verbatim
end


-- @@ L495-495 verbatim
namespace DeligneDrinfeld.CategoryExp

-- @@ L496-496 verbatim
open IsNilpotent

-- @@ L497-498 verbatim
variable {R V : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup V]
  [Module R V] [Module ℚ V] [IsScalarTower ℚ R V]

-- @@ L499-503 verbatim
variable {N : ℕ} (F : FilteredComparison.Filtration R V N)
  (A B : Module.End R V) (k : ℕ)
  (hA : ∀ m a,a∈F.step m → A a∈F.step (m+1))
  (hB : ∀ m a,a∈F.step m → B a∈F.step (m+1))
  (hD : ∀ m a,a∈F.step m → A a-B a∈F.step (m+k))

-- @@ L504-504 verbatim
include hA hB hD
 
-- @@ L505-518 verbatim
omit [Algebra ℚ R] [Module ℚ V] [IsScalarTower ℚ R V] in
 theorem pow_difference (i m : ℕ) {a : V} (ha : a∈F.step m) :
    (A^(i+1)) a-(B^(i+1)) a∈F.step (m+k+i) := by
  induction i with
  | zero => simpa only [zero_add,pow_one,Nat.add_zero] using hD m a ha
  | succ i ih =>
    have h₁ := hA (m+k+i) _ ih
    rw [map_sub] at h₁
    have hp := pow_mem_shift F B 1 hB (i+1) m ha
    simp only [Nat.mul_one] at hp
    have h₂ := hD (m+(i+1)) _ hp
    have hh := (F.step (m+k+i+1)).add_mem h₁ (by convert h₂ using 1; congr 1; omega)
    rw [pow_succ' A (i+1),pow_succ' B (i+1),Module.End.mul_apply,Module.End.mul_apply]
    convert hh using 1; abel

 
-- @@ L520-545 verbatim
theorem exp_difference (m : ℕ) {a : V} (ha : a∈F.step m) :
    exp A a-exp B a-(A a-B a)∈F.step (m+k+1) := by
  have hnil (d : Module.End R V) (hd : ∀ m a,a∈F.step m → d a∈F.step (m+1)) : d^(N+1)=0 := by
    apply LinearMap.ext
    intro x
    have hh := pow_mem_shift F d 1 hd (N+1) 0 (a:=x) (by rw [F.initial]; trivial)
    simpa only [Nat.mul_one,Nat.zero_add,F.terminal,Submodule.mem_bot,LinearMap.zero_apply] using hh
  let r := N+1
  let s := N+1
  have hr : A^r=0 := hnil A hA
  have hs : B^s=0 := hnil B hB
  have hr' : A^(2+(r+s))=0 := pow_eq_zero_of_le (by omega) hr
  have hs' : B^(2+(r+s))=0 := pow_eq_zero_of_le (by omega) hs
  rw [exp_eq_sum hr',exp_eq_sum hs',LinearMap.sum_apply,LinearMap.sum_apply,
    ←Finset.sum_sub_distrib,Finset.sum_range_add]
  have ht : (∑ i∈Finset.range 2,(((↑i.factorial:ℚ)⁻¹ • A^i) a-((↑i.factorial:ℚ)⁻¹ • B^i) a))=A a-B a := by
    simp [Finset.sum_range_succ]
  rw [ht,add_sub_cancel_left]
  apply Submodule.sum_mem
  intro i hi
  simp only [LinearMap.smul_apply,←smul_sub]
  apply ((F.step (m+k+1)).restrictScalars ℚ).smul_mem
  have hh := pow_difference F A B k hA hB hD (i+1) m ha
  have he : 2+i=i+1+1 := by omega
  rw [he]
  exact F.decreasing (by omega) hh

 
-- @@ L547-554 verbatim
theorem exp_difference_unit {a u : V} (ha : a-u∈F.step 1) :
    exp A a-exp B a-(A u-B u)∈F.step (k+1) := by
  have h₁ := exp_difference F A B k hA hB hD 0 (a:=a) (by rw [F.initial]; trivial)
  have h₂ := hD 1 (a-u) ha
  rw [map_sub,map_sub] at h₂
  have h₁' : exp A a-exp B a-(A a-B a)∈F.step (k+1) := by simpa only [Nat.zero_add] using h₁
  have h₂' : A a-A u-(B a-B u)∈F.step (k+1) := by simpa only [Nat.add_comm 1 k] using h₂
  convert (F.step (k+1)).add_mem h₁' h₂' using 1; abel

-- @@ L555-555 verbatim
end DeligneDrinfeld.CategoryExp


-- @@ L557-557 verbatim
end


-- @@ L559-559 verbatim
end OAI
