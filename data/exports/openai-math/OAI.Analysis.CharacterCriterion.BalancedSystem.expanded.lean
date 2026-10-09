import OAI.Analysis.CharacterCriterion.Definitions
import OAI.Analysis.CharacterCriterion.MatrixPaths


-- @@ L4-4 verbatim
namespace OAI


-- @@ L6-6 verbatim
noncomputable section

-- @@ L7-7 verbatim
open scoped TensorProduct

-- @@ L8-8 verbatim
open scoped InnerProductSpace

-- @@ L9-9 verbatim
open scoped BigOperators

-- @@ L10-10 verbatim
open Set Module

-- @@ L11-11 verbatim
open Topology

-- @@ L12-12 verbatim
open NormedSpace

-- @@ L13-13 verbatim
open scoped ComplexOrder

-- @@ L14-14 verbatim
open scoped ComplexOrder

-- @@ L15-15 verbatim
open scoped InnerProductSpace

-- @@ L16-16 verbatim
open scoped InnerProductSpace

-- @@ L17-17 verbatim
open NormedSpace

-- @@ L18-18 verbatim
open scoped TensorProduct InnerProductSpace

-- @@ L19-19 verbatim
open UniformSpace

-- @@ L20-20 verbatim
variable [KirchbergRordam.GenericRW.Size]

-- @@ L21-21 verbatim
local notation "rankNum" => KirchbergRordam.GenericRW.Size.n

-- @@ L22-22 verbatim
variable [KirchbergRordam.GenericRW.PauliData]

-- @@ L23-23 verbatim
omit [KirchbergRordam.GenericRW.Size] [KirchbergRordam.GenericRW.PauliData]

-- @@ L24-24 verbatim
open Filter Topology BoundedContinuousFunction

-- @@ L25-25 verbatim
open Filter Topology

-- @@ L26-26 verbatim
open Topology

-- @@ L27-27 verbatim
open scoped TensorProduct CStarAlgebra

-- @@ L28-28 verbatim
open scoped CStarAlgebra ComplexOrder



-- @@ L31-31 verbatim
namespace KirchbergRordam.BalancedDropMultiplicity


-- @@ L33-33 verbatim
def upper (p : ℕ) : ℕ := p*p

-- @@ L34-34 verbatim
def lower (p : ℕ) : ℕ := p*p-p+1

-- @@ L35-35 verbatim
def middle (p : ℕ) : ℕ := upper p * lower p - upper p - lower p


-- @@ L37-37 verbatim
def next (p : ℕ) : ℕ := p*p*p


-- @@ L39-41 verbatim
lemma lower_eq {p : ℕ} (hp : 2 ≤ p) : lower p + p = p*p + 1 := by
  have : p ≤ p*p := by nlinarith
  unfold lower; omega

-- @@ L42-42 verbatim
lemma upper_pos {p : ℕ} (hp : 2 ≤ p) : 0 < upper p := by unfold upper; positivity

-- @@ L43-45 verbatim
lemma lower_pos {p : ℕ} (hp : 2 ≤ p) : 0 < lower p := by
  have lowerIdentity := lower_eq hp
  nlinarith

-- @@ L46-48 verbatim
lemma lower_two {p : ℕ} (hp : 2 ≤ p) : 2 ≤ lower p := by
  have h := lower_eq hp
  nlinarith

-- @@ L49-52 verbatim
lemma sum_le_product {p : ℕ} (hp : 2 ≤ p) : upper p + lower p ≤ upper p * lower p := by
  have ha : 2 ≤ upper p := by unfold upper; nlinarith
  have hb := lower_two hp
  nlinarith

-- @@ L53-55 verbatim
lemma total {p : ℕ} (hp : 2 ≤ p) : lower p + upper p + middle p = upper p * lower p := by
  have := sum_le_product hp
  unfold middle; omega

-- @@ L56-56 verbatim
lemma next_two {p : ℕ} (hp : 2 ≤ p) : 2 ≤ next p := by unfold next; nlinarith

-- @@ L57-57 verbatim
lemma mul_upper (p : ℕ) : p * upper p = next p := by unfold upper next; ring

-- @@ L58-60 verbatim
lemma mul_lower {p : ℕ} (hp : 2 ≤ p) : (p+1) * lower p = next p+1 := by
  have := lower_eq hp
  unfold next; nlinarith

-- @@ L61-68 verbatim
lemma at_zero {p : ℕ} (hp : 2 ≤ p) : upper p + middle p = (p-1)*(next p+1) := by
  have ht := total hp
  have hl := mul_lower hp
  have he : upper p * lower p = lower p + (p-1)*(next p+1) := by
    rw [← hl]
    have hp' : p-1+1=p := by omega
    unfold upper; nlinarith
  omega

-- @@ L69-78 verbatim
lemma at_one {p : ℕ} (hp : 2 ≤ p) : lower p + middle p = next p*(p-1) := by
  have ht := total hp
  have hl := lower_eq hp
  have he : upper p * lower p = upper p + next p*(p-1) := by
    have hp' : p-1+1=p := by omega
    have hl' : lower p = p*(p-1)+1 := by nlinarith
    rw [hl']
    unfold upper next
    ring
  omega

-- @@ L79-81 verbatim
lemma zero_space {p : ℕ} (hp : 2 ≤ p) : p + p*(p+1)*(p-1) = next p := by
  have hp' : p-1+1=p := by omega
  unfold next; nlinarith

-- @@ L82-84 verbatim
lemma one_space {p : ℕ} (hp : 2 ≤ p) : (p+1) + p*(p+1)*(p-1) = next p+1 := by
  have := zero_space hp
  omega


-- @@ L86-88 verbatim
def stage : ℕ → ℕ
  | 0 => 2
  | n+1 => next (stage n)

-- @@ L89-89 verbatim
@[simp] lemma stage_zero : stage 0 = 2 := rfl

-- @@ L90-91 verbatim
@[simp] lemma stage_succ (n : ℕ) : stage (n+1) = next (stage n) :=
  rfl

-- @@ L92-95 verbatim
lemma stage_two (n : ℕ) : 2 ≤ stage n := by
  induction n with
  | zero => simp
  | succ n ih => rw [stage_succ]; exact next_two ih

-- @@ L96-96 verbatim
lemma stage_coprime (n : ℕ) : (stage n).Coprime (stage n+1) := by simp


-- @@ L98-98 verbatim
end KirchbergRordam.BalancedDropMultiplicity


-- @@ L100-100 verbatim
namespace KirchbergRordam.MatrixBlockReindex

-- @@ L101-101 verbatim
open MatrixDiagonalPath

-- @@ L102-102 verbatim
open MatrixTensor (leftMatrix rightMatrix)

-- @@ L103-103 verbatim
open scoped ComplexOrder CStarAlgebra Matrix

-- @@ L104-105 verbatim
variable {P Q R S : Type*} [Fintype P] [Fintype Q] [Fintype R] [Fintype S]
  [instDecidableEqP : DecidableEq P] [instDecidableEqQ : DecidableEq Q] [DecidableEq R] [DecidableEq S]

-- @@ L106-117 verbatim
omit instDecidableEqP instDecidableEqQ in
lemma reindex_trans.{contextLevel1, contextLevel2}
    {P : Type contextLevel1}
    {Q : Type contextLevel2}
    [Fintype P]
    [Fintype Q]
    [DecidableEq P]
    [DecidableEq Q]
    {T : Type*} [Fintype T] [DecidableEq T]
    (e : P ≃ Q) (f : Q ≃ T) (a : Mat P) :
    CStarMatrix.reindexₐ ℂ ℂ (e.trans f) a =
      CStarMatrix.reindexₐ ℂ ℂ f (CStarMatrix.reindexₐ ℂ ℂ e a) := rfl

-- @@ L118-125 verbatim
lemma reindex_block (e : P ≃ Q) (a : P → Mat R) :
    CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr (Equiv.refl R) e) (block a) =
      block (fun i => a (e.symm i)) := by
  ext i j
  rcases i with ⟨r,p⟩; rcases j with ⟨s,q⟩
  change (if e.symm p=e.symm q then a (e.symm p) r s else 0) =
    (if p=q then a (e.symm p) r s else 0)
  simp only [e.symm.injective.eq_iff]

-- @@ L126-133 verbatim
lemma reindex_left (e : P ≃ Q) (f : R ≃ S) (a : Mat P) :
    CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr e f) (leftMatrix (κ:=R) a) =
      leftMatrix (κ:=S) (CStarMatrix.reindexₐ ℂ ℂ e a) := by
  ext i j
  rcases i with ⟨p,r⟩; rcases j with ⟨q,s⟩
  change leftMatrix a (e.symm p,f.symm r) (e.symm q,f.symm s) = _
  simp only [left_apply, f.symm.injective.eq_iff]
  rfl

-- @@ L134-141 verbatim
lemma reindex_right (e : P ≃ Q) (f : R ≃ S) (a : Mat R) :
    CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr e f) (rightMatrix (ι:=P) a) =
      rightMatrix (ι:=Q) (CStarMatrix.reindexₐ ℂ ℂ f a) := by
  ext i j
  rcases i with ⟨p,r⟩; rcases j with ⟨q,s⟩
  change rightMatrix a (e.symm p,f.symm r) (e.symm q,f.symm s) = _
  simp only [right_apply, e.symm.injective.eq_iff]
  rfl

-- @@ L142-142 verbatim
end KirchbergRordam.MatrixBlockReindex


-- @@ L144-144 verbatim
namespace KirchbergRordam.BalancedDropSystem

-- @@ L145-145 verbatim
open MatrixDiagonalPath

-- @@ L146-146 verbatim
open MatrixTensor (leftMatrix rightMatrix)

-- @@ L147-147 verbatim
open MatrixBlockReindex

-- @@ L148-148 verbatim
open BalancedDropMultiplicity

-- @@ L149-149 verbatim
open scoped ComplexOrder CStarAlgebra Matrix


-- @@ L151-151 verbatim
abbrev P (p : ℕ) := Fin p

-- @@ L152-152 verbatim
abbrev Q (p : ℕ) := Fin (p+1)

-- @@ L153-153 verbatim
abbrev Low (p : ℕ) := Fin (lower p)

-- @@ L154-154 verbatim
abbrev High (p : ℕ) := Fin (upper p)

-- @@ L155-155 verbatim
abbrev Mid (p : ℕ) := Fin (middle p)

-- @@ L156-156 verbatim
abbrev Slot (p : ℕ) := Low p ⊕ (High p ⊕ Mid p)

-- @@ L157-157 verbatim
abbrev Index (p : ℕ) := (P p × Q p) × Slot p

-- @@ L158-158 verbatim
abbrev ZeroSpace (p : ℕ) := P p ⊕ ((P p × Q p) × Fin (p-1))

-- @@ L159-159 verbatim
abbrev OneSpace (p : ℕ) := Q p ⊕ ((P p × Q p) × Fin (p-1))



-- @@ L162-163 verbatim
def zeroLow (p : ℕ) (hp : 2 ≤ p) : Q p × Low p ≃ Q (next p) :=
  cardEquiv (by simpa only [Fintype.card_prod, Fintype.card_fin] using mul_lower hp)

-- @@ L164-165 verbatim
def zeroMid (p : ℕ) (hp : 2 ≤ p) : High p ⊕ Mid p ≃ Fin (p-1) × Q (next p) :=
  cardEquiv (by simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] using at_zero hp)

-- @@ L166-167 verbatim
def zeroOuter (p : ℕ) (hp : 2 ≤ p) : ZeroSpace p ≃ P (next p) :=
  cardEquiv (by simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] using zero_space hp)

-- @@ L168-169 verbatim
def oneLow (p : ℕ) : P p × High p ≃ P (next p) :=
  cardEquiv (by simpa only [Fintype.card_prod, Fintype.card_fin] using mul_upper p)

-- @@ L170-171 verbatim
def oneMid (p : ℕ) (hp : 2 ≤ p) : Low p ⊕ Mid p ≃ P (next p) × Fin (p-1) :=
  cardEquiv (by simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] using at_one hp)

-- @@ L172-173 verbatim
def oneOuter (p : ℕ) (hp : 2 ≤ p) : OneSpace p ≃ Q (next p) :=
  cardEquiv (by simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] using one_space hp)



-- @@ L176-180 verbatim
def slotSwap (p : ℕ) : Slot p ≃ High p ⊕ (Low p ⊕ Mid p) where
  toFun := Sum.elim (Sum.inr ∘ Sum.inl) (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr))
  invFun := Sum.elim (Sum.inr ∘ Sum.inl) (Sum.elim Sum.inl (Sum.inr ∘ Sum.inr))
  left_inv x := by rcases x with x|x|x <;> rfl
  right_inv x := by rcases x with x|x|x <;> rfl


-- @@ L182-184 verbatim
def zeroReindex (p : ℕ) (hp : 2 ≤ p) : Index p ≃ P (next p) × Q (next p) :=
  (repackLeft (zeroLow p hp) (zeroMid p hp)).trans
    (Equiv.prodCongr (zeroOuter p hp) (Equiv.refl _))

-- @@ L185-188 verbatim
def oneReindex (p : ℕ) (hp : 2 ≤ p) : Index p ≃ P (next p) × Q (next p) :=
  (Equiv.prodCongr (Equiv.refl _) (slotSwap p)).trans
    ((repackRight (oneLow p) (oneMid p hp)).trans
      (Equiv.prodCongr (Equiv.refl _) (oneOuter p hp)))


-- @@ L190-191 verbatim
lemma half_mem : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
  constructor <;> norm_num


-- @@ L193-194 verbatim
def eigenpath (p : ℕ) : Slot p → C(unitInterval, unitInterval) :=
  Sum.elim (fun _ => lowerPath) (Sum.elim (fun _ => upperPath) (fun _ => ContinuousMap.const _ half))


-- @@ L196-199 verbatim
@[simp] lemma lower_zero : lowerPath 0 = 0 := by
  apply Subtype.ext
  change (0 : ℝ) / 2 = 0
  norm_num

-- @@ L200-203 verbatim
@[simp] lemma lower_one : lowerPath 1 = half := by
  apply Subtype.ext
  change (1 : ℝ) / 2 = (1 : ℝ) / 2
  rfl

-- @@ L204-207 verbatim
@[simp] lemma upper_zero : upperPath 0 = half := by
  apply Subtype.ext
  change ((0 : ℝ) + 1) / 2 = (1 : ℝ) / 2
  rw [zero_add]

-- @@ L208-211 verbatim
@[simp] lemma upper_one : upperPath 1 = 1 := by
  apply Subtype.ext
  change ((1 : ℝ) + 1) / 2 = 1
  norm_num


-- @@ L213-223 verbatim
lemma eigen_cover (p : ℕ) (hp : 2 ≤ p) (s : unitInterval) :
    ∃ i t, eigenpath p i t = s := by
  by_cases hs : (s:ℝ) ≤ 1/2
  · refine ⟨.inl ⟨0,lower_pos hp⟩, ⟨2*s,by constructor <;> linarith [s.property.1]⟩, ?_⟩
    apply Subtype.ext
    change 2*(s:ℝ)/2=(s:ℝ)
    ring
  · refine ⟨.inr (.inl ⟨0,upper_pos hp⟩), ⟨2*s-1,by constructor <;> linarith [s.property.2]⟩, ?_⟩
    apply Subtype.ext
    change ((2*(s:ℝ)-1)+1)/2=(s:ℝ)
    ring



-- @@ L226-230 verbatim
def fiberMap (p : ℕ) (hp : 2 ≤ p) (t : unitInterval) :
    C(unitInterval, PrimeDimensionDrop.Fiber p (p+1)) →⋆ₐ[ℂ]
      PrimeDimensionDrop.Fiber (next p) (next p+1) :=
  (interpolate (zeroReindex p hp) (oneReindex p hp) t).toStarAlgHom.comp
    (evaluationBlock (eigenpath p) t)



-- @@ L233-243 verbatim
def rawStep (p : ℕ) (hp : 2 ≤ p) :
    C(unitInterval, PrimeDimensionDrop.Fiber p (p+1)) →⋆ₐ[ℂ]
      C(unitInterval, PrimeDimensionDrop.Fiber (next p) (next p+1)) where
  toFun f := ⟨fun t => fiberMap p hp t f,
    interpolate_continuous _ _ _ (evaluationBlock_continuous _ _)⟩
  map_zero' := by apply ContinuousMap.ext; intro t; exact (fiberMap p hp t).map_zero
  map_one' := by apply ContinuousMap.ext; intro t; exact (fiberMap p hp t).map_one
  map_add' f g := by apply ContinuousMap.ext; intro t; exact (fiberMap p hp t).map_add f g
  map_mul' f g := by apply ContinuousMap.ext; intro t; exact (fiberMap p hp t).map_mul f g
  commutes' z := by apply ContinuousMap.ext; intro t; exact (fiberMap p hp t).commutes z
  map_star' f := by apply ContinuousMap.ext; intro t; exact map_star (fiberMap p hp t) f


-- @@ L245-247 verbatim
@[simp] lemma rawStep_apply (p : ℕ) (hp : 2 ≤ p) (f) (t : unitInterval) :
    rawStep p hp f t = interpolate (zeroReindex p hp) (oneReindex p hp) t
      (evaluationBlock (eigenpath p) t f) := rfl


-- @@ L249-256 verbatim
lemma zero_eval (p : ℕ) (f : C(unitInterval, PrimeDimensionDrop.Fiber p (p+1)))
    (a : Mat (P p)) (ha : leftMatrix a = f 0) :
    evaluationBlock (eigenpath p) 0 f =
      block (Sum.elim (fun _ : Low p => leftMatrix (κ:=Q p) a)
        (fun _ : High p ⊕ Mid p => f half)) := by
  apply congrArg block
  funext k
  rcases k with k|k|k <;> simp [eigenpath,ha]


-- @@ L258-268 verbatim
lemma one_eval (p : ℕ) (f : C(unitInterval, PrimeDimensionDrop.Fiber p (p+1)))
    (b : Mat (Q p)) (hb : rightMatrix b = f 1) :
    CStarMatrix.reindexₐ ℂ ℂ (Equiv.prodCongr (Equiv.refl (P p × Q p)) (slotSwap p))
      (evaluationBlock (eigenpath p) 1 f) =
      block (Sum.elim (fun _ : High p => rightMatrix (ι:=P p) b)
        (fun _ : Low p ⊕ Mid p => f half)) := by
  change CStarMatrix.reindexₐ ℂ ℂ _ (block _) = _
  rw [reindex_block]
  apply congrArg block
  funext k
  rcases k with k|k|k <;> simp [slotSwap,eigenpath,hb]


-- @@ L270-278 verbatim
lemma rawStep_zero (p : ℕ) (hp : 2 ≤ p)
    (f : C(unitInterval, PrimeDimensionDrop.Fiber p (p+1)))
    (a : Mat (P p)) (ha : leftMatrix a = f 0) :
    rawStep p hp f 0 = leftMatrix (κ := Q (next p))
      (CStarMatrix.reindexₐ ℂ ℂ (zeroOuter p hp)
        (sumBlock (a,block (fun _ : Fin (p-1) => f half)))) := by
  rw [rawStep_apply,interpolate_zero,zero_eval p f a ha]
  unfold zeroReindex
  rw [reindex_trans,repackLeft_matrix,reindex_left]


-- @@ L280-288 verbatim
lemma rawStep_one (p : ℕ) (hp : 2 ≤ p)
    (f : C(unitInterval, PrimeDimensionDrop.Fiber p (p+1)))
    (b : Mat (Q p)) (hb : rightMatrix b = f 1) :
    rawStep p hp f 1 = rightMatrix (ι := P (next p))
      (CStarMatrix.reindexₐ ℂ ℂ (oneOuter p hp)
        (sumBlock (b,block (fun _ : Fin (p-1) => f half)))) := by
  rw [rawStep_apply,interpolate_one]
  unfold oneReindex
  rw [reindex_trans,one_eval p f b hb,reindex_trans,repackRight_matrix,reindex_right]



-- @@ L291-302 verbatim
def step (p : ℕ) (hp : 2 ≤ p) : PrimeDimensionDrop.Algebra p (p+1) →⋆ₐ[ℂ]
    PrimeDimensionDrop.Algebra (next p) (next p+1) where
  toFun f := ⟨rawStep p hp f.val, by
    obtain ⟨⟨a,ha⟩,⟨b,hb⟩⟩ := f.property
    exact ⟨⟨_, (rawStep_zero p hp f.val a ha).symm⟩,
      ⟨_, (rawStep_one p hp f.val b hb).symm⟩⟩⟩
  map_zero' := by apply Subtype.ext; exact (rawStep p hp).map_zero
  map_one' := by apply Subtype.ext; exact (rawStep p hp).map_one
  map_add' f g := by apply Subtype.ext; exact (rawStep p hp).map_add f.val g.val
  map_mul' f g := by apply Subtype.ext; exact (rawStep p hp).map_mul f.val g.val
  commutes' z := by apply Subtype.ext; exact (rawStep p hp).commutes z
  map_star' f := by apply Subtype.ext; exact map_star (rawStep p hp) f.val


-- @@ L304-310 verbatim
lemma rawStep_injective (p : ℕ) (hp : 2 ≤ p) : Function.Injective (rawStep p hp) := by
  intro f g h
  apply diagonal_injective (eigenpath p) (eigen_cover p hp)
  apply ContinuousMap.ext
  intro t
  exact (interpolate (zeroReindex p hp) (oneReindex p hp) t).injective
    (DFunLike.congr_fun h t)


-- @@ L312-315 verbatim
lemma step_injective (p : ℕ) (hp : 2 ≤ p) : Function.Injective (step p hp) := by
  intro f g h
  apply Subtype.ext
  exact rawStep_injective p hp (congrArg Subtype.val h)


-- @@ L317-318 verbatim
lemma step_norm (p : ℕ) (hp : 2 ≤ p) (f : PrimeDimensionDrop.Algebra p (p+1)) :
    ‖step p hp f‖ = ‖f‖ := NonUnitalStarAlgHom.norm_map _ (step_injective p hp) f


-- @@ L320-320 verbatim
end KirchbergRordam.BalancedDropSystem



-- @@ L323-323 verbatim
end


-- @@ L325-325 verbatim
end OAI
