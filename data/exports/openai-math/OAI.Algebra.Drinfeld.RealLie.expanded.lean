import OAI.Algebra.Drinfeld.Logarithm


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
noncomputable section

-- @@ L6-6 verbatim
namespace RealDeligneDrinfeld


-- @@ L8-28 verbatim
theorem freeLie_induction {R α : Type*} [CommRing R]
    {P : FreeLieAlgebra R α → Prop} (h0 : P 0)
    (hg : ∀ a, P (FreeLieAlgebra.of R a))
    (ha : ∀ a b, P a → P b → P (a+b))
    (hs : ∀ (r : R) a, P a → P (r • a))
    (hl : ∀ a b, P a → P b → P ⁅a,b⁆) (q : FreeLieAlgebra R α) : P q := by
  let K : LieSubalgebra R (FreeLieAlgebra R α) :=
    { carrier := {a | P a}
      zero_mem' := h0
      add_mem' := fun ha' hb' => ha _ _ ha' hb'
      smul_mem' := fun r a h => hs r a h
      lie_mem' := fun ha' hb' => hl _ _ ha' hb' }
  let f : FreeLieAlgebra R α →ₗ⁅R⁆ K :=
    FreeLieAlgebra.lift R (fun a => ⟨FreeLieAlgebra.of R a, hg a⟩)
  have hf : K.incl.comp f = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp [f]
  have h := (f q).property
  change P ((K.incl.comp f) q) at h
  simpa only [hf, LieHom.id_apply] using h


-- @@ L30-30 verbatim
abbrev L := FreeLieAlgebra ℝ Bool

-- @@ L31-31 verbatim
def x : L := FreeLieAlgebra.of ℝ false

-- @@ L32-32 verbatim
def y : L := FreeLieAlgebra.of ℝ true


-- @@ L34-35 verbatim
def eval {M : Type*} [LieRing M] [LieAlgebra ℝ M] (a b : M) : L →ₗ⁅ℝ⁆ M :=
  FreeLieAlgebra.lift ℝ (fun i => if i then b else a)


-- @@ L37-37 verbatim
abbrev Edge := {p : Fin 4 × Fin 4 // p.1 < p.2}

-- @@ L38-38 verbatim
abbrev BraidFree := FreeLieAlgebra ℝ Edge


-- @@ L40-42 verbatim
def chord (i j : Fin 4) : BraidFree :=
  if h : i < j then FreeLieAlgebra.of ℝ ⟨(i, j), h⟩
  else if h : j < i then FreeLieAlgebra.of ℝ ⟨(j, i), h⟩ else 0


-- @@ L44-49 verbatim
def braidRelations : Set BraidFree :=
  {z | (∃ i j k l : Fin 4,
    i ≠ j ∧ i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l ∧ k ≠ l ∧
      z = ⁅chord i j, chord k l⁆) ∨
    (∃ i j k : Fin 4, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      z = ⁅chord i j, chord i k + chord j k⁆)}


-- @@ L51-52 verbatim
def braidIdeal : LieIdeal ℝ BraidFree :=
  LieSubmodule.lieSpan ℝ BraidFree braidRelations


-- @@ L54-54 verbatim
abbrev T4 := BraidFree ⧸ braidIdeal

-- @@ L55-55 verbatim
def t (i j : Fin 4) : T4 := LieSubmodule.Quotient.mk (chord i j)


-- @@ L57-62 verbatim
def IsSolution (p : L) : Prop :=
  p + eval y x p = 0 ∧
  p + eval y (-x-y) p + eval (-x-y) x p = 0 ∧
  eval (t 0 1) (t 1 2 + t 1 3) p + eval (t 0 2 + t 1 2) (t 2 3) p =
    eval (t 1 2) (t 2 3) p + eval (t 0 1 + t 0 2) (t 1 3 + t 2 3) p +
      eval (t 0 1) (t 1 2) p


-- @@ L64-95 verbatim
def W : Submodule ℝ L where
  carrier := {p | IsSolution p}
  zero_mem' := by simp [IsSolution]
  add_mem' := by
    intro p q hp hq
    rcases hp with ⟨hp1, hp2, hp3⟩
    rcases hq with ⟨hq1, hq2, hq3⟩
    refine ⟨?_, ?_, ?_⟩
    · simp only [map_add]
      calc
        _ = (p + eval y x p) + (q + eval y x q) := by abel
        _ = 0 := by rw [hp1, hq1, add_zero]
    · simp only [map_add]
      calc
        _ = (p + eval y (-x-y) p + eval (-x-y) x p) +
            (q + eval y (-x-y) q + eval (-x-y) x q) := by abel
        _ = 0 := by rw [hp2, hq2, add_zero]
    · simp only [map_add]
      calc
        _ = (eval (t 0 1) (t 1 2 + t 1 3) p + eval (t 0 2 + t 1 2) (t 2 3) p) +
            (eval (t 0 1) (t 1 2 + t 1 3) q + eval (t 0 2 + t 1 2) (t 2 3) q) := by abel
        _ = _ := by rw [hp3, hq3]; abel
  smul_mem' := by
    intro a p hp
    rcases hp with ⟨hp1, hp2, hp3⟩
    change IsSolution (a • p)
    simp only [IsSolution, map_smul]
    constructor
    · simpa only [smul_add, smul_zero] using congrArg (a • ·) hp1
    constructor
    · simpa only [smul_add, smul_zero] using congrArg (a • ·) hp2
    · simpa only [smul_add] using congrArg (a • ·) hp3


-- @@ L97-99 verbatim
structure Tangent where
  base : L
  velocity : L


-- @@ L101-105 verbatim
def Tangent.equiv : Tangent ≃ L × L where
  toFun z := (z.base, z.velocity)
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl


-- @@ L107-107 verbatim
instance : AddCommGroup Tangent := Tangent.equiv.addCommGroup

-- @@ L108-108 verbatim
instance : Module ℝ Tangent := Tangent.equiv.addEquiv.module ℝ

-- @@ L109-111 verbatim
instance : Bracket Tangent Tangent :=
  ⟨fun a b => ⟨⁅a.base, b.base⁆,
    ⁅a.velocity, b.base⁆ + ⁅a.base, b.velocity⁆⟩⟩


-- @@ L113-114 verbatim
@[ext] theorem Tangent.ext {a b : Tangent} (h : a.base = b.base)
    (k : a.velocity = b.velocity) : a = b := by cases a; cases b; simp_all


-- @@ L116-116 verbatim
@[simp] theorem Tangent.base_zero : (0 : Tangent).base = 0 := rfl

-- @@ L117-117 verbatim
@[simp] theorem Tangent.velocity_zero : (0 : Tangent).velocity = 0 := rfl

-- @@ L118-118 verbatim
@[simp] theorem Tangent.base_add (a b : Tangent) : (a+b).base = a.base+b.base := rfl

-- @@ L119-120 verbatim
@[simp] theorem Tangent.velocity_add (a b : Tangent) :
    (a+b).velocity = a.velocity+b.velocity := rfl

-- @@ L121-121 verbatim
@[simp] theorem Tangent.base_smul (q : ℝ) (a : Tangent) : (q • a).base = q • a.base := rfl

-- @@ L122-123 verbatim
@[simp] theorem Tangent.velocity_smul (q : ℝ) (a : Tangent) :
    (q • a).velocity = q • a.velocity := rfl

-- @@ L124-124 verbatim
@[simp] theorem Tangent.base_lie (a b : Tangent) : ⁅a,b⁆.base = ⁅a.base,b.base⁆ := rfl

-- @@ L125-126 verbatim
@[simp] theorem Tangent.velocity_lie (a b : Tangent) :
    ⁅a,b⁆.velocity = ⁅a.velocity,b.base⁆ + ⁅a.base,b.velocity⁆ := rfl


-- @@ L128-150 verbatim
instance : LieRing Tangent where
  add_lie a b c := by
    ext
    · simp [add_lie]
    · simp only [Tangent.velocity_lie, Tangent.velocity_add, Tangent.base_add, add_lie]
      abel
  lie_add a b c := by
    ext
    · simp [lie_add]
    · simp only [Tangent.velocity_lie, Tangent.velocity_add, Tangent.base_add, lie_add]
      abel
  lie_self a := by
    ext
    · simp
    · change ⁅a.velocity, a.base⁆ + ⁅a.base, a.velocity⁆ = 0
      rw [← lie_skew a.velocity a.base]
      exact neg_add_cancel _
  leibniz_lie a b c := by
    ext
    · simp [lie_lie]
    · simp only [Tangent.velocity_lie, Tangent.velocity_add, Tangent.base_lie,
        lie_add, add_lie, lie_lie]
      abel

-- @@ L151-152 verbatim
instance : LieAlgebra ℝ Tangent where
  lie_smul q a b := by ext <;> simp [lie_smul, smul_add]


-- @@ L154-155 verbatim
def tangentLift (p : L) : L →ₗ⁅ℝ⁆ Tangent :=
  FreeLieAlgebra.lift ℝ (fun i => if i then ⟨y, ⁅y,p⁆⟩ else ⟨x, 0⟩)


-- @@ L157-157 verbatim
def D (p q : L) : L := (tangentLift p q).velocity


-- @@ L159-159 verbatim
def ihara (p q : L) : L := D p q - D q p + ⁅p,q⁆


-- @@ L161-162 verbatim
@[simp] theorem eval_x {M : Type*} [LieRing M] [LieAlgebra ℝ M] (a b : M) :
    eval a b x = a := by simp [eval, x]

-- @@ L163-164 verbatim
@[simp] theorem eval_y {M : Type*} [LieRing M] [LieAlgebra ℝ M] (a b : M) :
    eval a b y = b := by simp [eval, y]


-- @@ L166-170 verbatim
def Tangent.baseHom : Tangent →ₗ⁅ℝ⁆ L where
  toFun := Tangent.base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' := rfl


-- @@ L172-177 verbatim
@[simp] theorem tangentLift_base (p q : L) : (tangentLift p q).base = q := by
  have h : Tangent.baseHom.comp (tangentLift p) = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro i
    cases i <;> simp [tangentLift, Tangent.baseHom, x, y] <;> rfl
  exact LieHom.congr_fun h q


-- @@ L179-179 verbatim
@[simp] theorem D_x (p : L) : D p x = 0 := by simp [D, tangentLift, x]

-- @@ L180-180 verbatim
@[simp] theorem D_y (p : L) : D p y = ⁅y,p⁆ := by simp [D, tangentLift, y]

-- @@ L181-181 verbatim
@[simp] theorem D_zero (p : L) : D p 0 = 0 := by simp [D]

-- @@ L182-182 verbatim
@[simp] theorem D_add (p q r : L) : D p (q+r) = D p q + D p r := by simp [D]

-- @@ L183-183 verbatim
@[simp] theorem D_smul (p q : L) (a : ℝ) : D p (a • q) = a • D p q := by simp [D]

-- @@ L184-185 verbatim
theorem D_lie (p q r : L) : D p ⁅q,r⁆ = ⁅D p q,r⁆ + ⁅q,D p r⁆ := by
  simp [D, LieHom.map_lie]


-- @@ L187-193 verbatim
def derivation (p : L) : LieDerivation ℝ L L where
  toFun := D p
  map_add' := D_add p
  map_smul' a q := D_smul p q a
  leibniz' a b := by
    change D p ⁅a,b⁆ = ⁅a,D p b⁆ - ⁅b,D p a⁆
    rw [D_lie, sub_eq_add_neg, lie_skew, add_comm]


-- @@ L195-195 verbatim
@[simp] theorem derivation_apply (p q : L) : derivation p q = D p q := rfl


-- @@ L197-206 verbatim
theorem derivation_ext {d₁ d₂ : LieDerivation ℝ L L}
    (hx : d₁ x = d₂ x) (hy : d₁ y = d₂ y) : d₁ = d₂ := by
  apply DFunLike.ext
  intro q
  induction q using freeLie_induction with
  | h0 => simp
  | hg i => cases i; exact hx; exact hy
  | ha a b ha hb => simp [ha, hb]
  | hs r a ha => simp [ha]
  | hl a b ha hb => simp [ha, hb]


-- @@ L208-211 verbatim
@[simp] theorem D_zero_left (q : L) : D 0 q = 0 := by
  have h : derivation 0 = 0 := by
    apply derivation_ext <;> simp
  exact LieDerivation.congr_fun h q


-- @@ L213-216 verbatim
@[simp] theorem D_add_left (p q r : L) : D (p+q) r = D p r + D q r := by
  have h : derivation (p+q) = derivation p + derivation q := by
    apply derivation_ext <;> simp [lie_add]
  exact LieDerivation.congr_fun h r


-- @@ L218-221 verbatim
@[simp] theorem D_smul_left (p q : L) (a : ℝ) : D (a • p) q = a • D p q := by
  have h : derivation (a • p) = a • derivation p := by
    apply derivation_ext <;> simp
  exact LieDerivation.congr_fun h q


-- @@ L223-226 verbatim
inductive WeightedWord {α : Type*} (wt : α → ℕ) : ℕ → FreeLieAlgebra ℝ α → Prop
  | generator (a : α) : WeightedWord wt (wt a) (FreeLieAlgebra.of ℝ a)
  | bracket {n m a b} : WeightedWord wt n a → WeightedWord wt m b →
      WeightedWord wt (n+m) ⁅a,b⁆


-- @@ L228-229 verbatim
def weightPiece {α : Type*} (wt : α → ℕ) (n : ℕ) : Submodule ℝ (FreeLieAlgebra ℝ α) :=
  Submodule.span ℝ {p | WeightedWord wt n p}


-- @@ L231-231 verbatim
abbrev OddFree := FreeLieAlgebra ℝ ℕ

-- @@ L232-232 verbatim
def oddWeight (k : ℕ) : ℕ := 2*k+3

-- @@ L233-233 verbatim
abbrev Fn (n : ℕ) := weightPiece oddWeight n

-- @@ L234-234 verbatim
abbrev Ln (n : ℕ) := weightPiece (fun _ : Bool => 1) n

-- @@ L235-235 verbatim
abbrev Wn (n : ℕ) : Submodule ℝ L := W ⊓ Ln n


-- @@ L237-238 verbatim
def Graded (e : OddFree ≃ₗ[ℝ] W) : Prop :=
  ∀ n a, (e a : L) ∈ Ln n ↔ a ∈ Fn n


-- @@ L240-240 verbatim
abbrev OddCompletion := (n : ℕ) → Fn n

-- @@ L241-241 verbatim
abbrev WCompletion := (n : ℕ) → Wn n


-- @@ L243-243 verbatim
instance : TopologicalSpace L := ⊥

-- @@ L244-244 verbatim
instance : TopologicalSpace OddFree := ⊥


-- @@ L246-247 verbatim
def completed (e : OddFree ≃ₗ[ℝ] W) (h : Graded e) : OddCompletion → WCompletion :=
  fun a n => ⟨e (a n), (e (a n)).property, (h n (a n)).2 (a n).property⟩


-- @@ L249-253 verbatim
def completedInv (e : OddFree ≃ₗ[ℝ] W) (h : Graded e) : WCompletion → OddCompletion :=
  fun a n => ⟨e.symm ⟨a n, (a n).property.1⟩,
    (h n (e.symm ⟨a n, (a n).property.1⟩)).1 (by
      rw [LinearEquiv.apply_symm_apply]
      exact (a n).property.2)⟩


-- @@ L255-264 verbatim
def MainStatement : Prop :=
  ∃ (e : OddFree ≃ₗ[ℝ] W) (h : Graded e),
    (∀ a b, (e ⁅a,b⁆ : L) = ihara (e a) (e b)) ∧
    Function.LeftInverse (completedInv e h) (completed e h) ∧
    Function.RightInverse (completedInv e h) (completed e h) ∧
    Continuous (completed e h) ∧ Continuous (completedInv e h) ∧
    (∀ (a b : OddCompletion) n,
      (e (∑ i ∈ Finset.range (n+1), ⁅(a i : OddFree), (b (n-i) : OddFree)⁆) : L) =
      ∑ i ∈ Finset.range (n+1),
        ihara (completed e h a i) (completed e h b (n-i)))


-- @@ L266-266 verbatim
namespace AssociativeModel


-- @@ L268-268 verbatim
variable {α : Type*}

-- @@ L269-269 verbatim
abbrev FL (α : Type*) := FreeLieAlgebra ℝ α

-- @@ L270-270 verbatim
abbrev A (α : Type*) := MonoidAlgebra ℝ (FreeMonoid α)

-- @@ L271-271 verbatim
attribute [local instance] LieRing.ofAssociativeRing


-- @@ L273-273 verbatim
def atom (a : α) : A α := MonoidAlgebra.single (FreeMonoid.of a) 1


-- @@ L275-275 verbatim
def embed : FL α →ₗ⁅ℝ⁆ A α := FreeLieAlgebra.lift ℝ atom


-- @@ L277-278 verbatim
@[simp] theorem embed_of (a : α) : embed (FreeLieAlgebra.of ℝ a) = atom a := by
  simp [embed]


-- @@ L280-283 verbatim
def dynkinWord : List α → FL α
  | [] => 0
  | [a] => FreeLieAlgebra.of ℝ a
  | a :: b :: w => ⁅FreeLieAlgebra.of ℝ a, dynkinWord (b :: w)⁆


-- @@ L285-289 verbatim
theorem dynkinWord_cons (a : α) (w : List α) (hw : w ≠ []) :
    dynkinWord (a::w) = ⁅FreeLieAlgebra.of ℝ a, dynkinWord w⁆ := by
  cases w with
  | nil => contradiction
  | cons b w => rfl


-- @@ L291-293 verbatim
def wordLinear {M : Type*} [AddCommGroup M] [Module ℝ M]
    (f : FreeMonoid α → M) : A α →ₗ[ℝ] M :=
  (Finsupp.linearCombination ℝ f).comp (MonoidAlgebra.coeffLinearEquiv ℝ).toLinearMap


-- @@ L295-298 verbatim
@[simp] theorem wordLinear_single {M : Type*} [AddCommGroup M] [Module ℝ M]
    (f : FreeMonoid α → M) (w : FreeMonoid α) (c : ℝ) :
    wordLinear f (MonoidAlgebra.single w c) = c • f w := by
  change Finsupp.linearCombination ℝ f (Finsupp.single w c) = _; simp


-- @@ L300-300 verbatim
def dynkin : A α →ₗ[ℝ] FL α := wordLinear (fun w => dynkinWord w.toList)


-- @@ L302-303 verbatim
def wordAct : FreeMonoid α →* Module.End ℝ (FL α) :=
  FreeMonoid.lift (fun a => LieAlgebra.ad ℝ (FL α) (FreeLieAlgebra.of ℝ a))


-- @@ L305-306 verbatim
def act : A α →ₐ[ℝ] Module.End ℝ (FL α) :=
  MonoidAlgebra.lift ℝ (Module.End ℝ (FL α)) (FreeMonoid α) wordAct


-- @@ L308-309 verbatim
@[simp] theorem act_single (w : FreeMonoid α) (c : ℝ) :
    act (MonoidAlgebra.single w c) = c • wordAct w := by simp [act]


-- @@ L311-313 verbatim
@[simp] theorem wordAct_of_apply (a : α) (q : FL α) :
    wordAct (FreeMonoid.of a) q = ⁅FreeLieAlgebra.of ℝ a,q⁆ := by
  simp [wordAct, LieAlgebra.ad_apply]


-- @@ L315-320 verbatim
@[simp] theorem act_embed (p q : FL α) : act (embed p) q = ⁅p,q⁆ := by
  have h : act.toLieHom.comp embed = LieAlgebra.ad ℝ (FL α) := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp [atom, wordAct]
  exact LinearMap.congr_fun (LieHom.congr_fun h p) q


-- @@ L322-328 verbatim
theorem dynkinWord_append (u v : List α) (hv : v ≠ []) :
    dynkinWord (u++v) = wordAct (FreeMonoid.ofList u) (dynkinWord v) := by
  induction u with
  | nil => simp
  | cons a u ih =>
    rw [List.cons_append, dynkinWord_cons _ _ (List.append_ne_nil_of_right_ne_nil u hv),
      ih, FreeMonoid.ofList_cons, map_mul, Module.End.mul_apply, wordAct_of_apply]


-- @@ L330-332 verbatim
def homogeneous (n : ℕ) : Submodule ℝ (A α) :=
  Submodule.span ℝ {p | ∃ w : FreeMonoid α,
    w.toList.length = n ∧ p = MonoidAlgebra.single w 1}


-- @@ L334-336 verbatim
theorem single_mem_homogeneous (w : FreeMonoid α) (n : ℕ)
    (hn : w.toList.length = n) : MonoidAlgebra.single w 1 ∈ homogeneous (α := α) n :=
  Submodule.subset_span ⟨w, hn, rfl⟩


-- @@ L338-353 verbatim
theorem mul_homogeneous {n m : ℕ} {a b : A α}
    (ha : a ∈ homogeneous n) (hb : b ∈ homogeneous m) : a*b ∈ homogeneous (n+m) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases ha with ⟨v,hv,rfl⟩
    induction hb using Submodule.span_induction with
    | mem b hb =>
      rcases hb with ⟨w,hw,rfl⟩
      simpa only [MonoidAlgebra.single_mul_single, one_mul] using
        single_mem_homogeneous (v*w) (n+m) (by simp [hv,hw])
    | zero => simp
    | add b c _ _ hb hc => simpa only [mul_add] using (homogeneous (n+m)).add_mem hb hc
    | smul r b _ hb => simpa only [mul_smul_comm] using (homogeneous (n+m)).smul_mem r hb
  | zero => simp
  | add a c _ _ ha hc => simpa only [add_mul] using (homogeneous (n+m)).add_mem ha hc
  | smul r a _ ha => simpa only [smul_mul_assoc] using (homogeneous (n+m)).smul_mem r ha


-- @@ L355-368 verbatim
theorem dynkin_mul {n : ℕ} (hn : n > 0) (a : A α) {b : A α}
    (hb : b ∈ homogeneous n) : dynkin (a*b) = act a (dynkin b) := by
  induction a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add a c ha hc => simp [add_mul, ha, hc]
  | single v r =>
    induction hb using Submodule.span_induction with
    | mem b hb =>
      rcases hb with ⟨w,hw,rfl⟩
      have hw' : w.toList ≠ [] := by intro h; simp [h] at hw; omega
      simp [dynkin, dynkinWord_append _ _ hw']
    | zero => simp
    | add b c _ _ hb hc => simp [mul_add, hb, hc]
    | smul r b _ hb => simp [hb]


-- @@ L370-392 verbatim
theorem dynkin_embed_word {n : ℕ} {p : FL α}
    (hp : WeightedWord (fun _ : α => 1) n p) :
    0 < n ∧ embed p ∈ homogeneous n ∧ dynkin (embed p) = (n : ℝ) • p := by
  induction hp with
  | generator a =>
    refine ⟨by omega, ?_, ?_⟩
    · simpa [atom] using single_mem_homogeneous (FreeMonoid.of a) 1 rfl
    · simp [dynkin, atom, dynkinWord]
  | @bracket n m p q hp hq ihp ihq =>
    rcases ihp with ⟨hn,hn',hpn⟩
    rcases ihq with ⟨hm,hm',hqm⟩
    refine ⟨by omega, ?_, ?_⟩
    · rw [LieHom.map_lie]
      change embed p * embed q - embed q * embed p ∈ homogeneous (n+m)
      exact (homogeneous (n+m)).sub_mem (mul_homogeneous hn' hm')
        (by simpa [Nat.add_comm] using mul_homogeneous hm' hn')
    · rw [LieHom.map_lie]
      change dynkin (embed p * embed q - embed q * embed p) = _
      rw [map_sub, dynkin_mul hm _ hm', dynkin_mul hn _ hn', hqm, hpn]
      simp only [map_smul, act_embed]
      rw [← lie_skew q p]
      simp only [smul_neg, sub_neg_eq_add, Nat.cast_add, add_smul]
      exact add_comm _ _


-- @@ L394-395 verbatim
def normalizedDynkin : A α →ₗ[ℝ] FL α :=
  wordLinear (fun w => (w.toList.length : ℝ)⁻¹ • dynkinWord w.toList)


-- @@ L397-406 verbatim
theorem normalizedDynkin_homogeneous {n : ℕ} {a : A α}
    (ha : a ∈ homogeneous n) : normalizedDynkin a = (n : ℝ)⁻¹ • dynkin a := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    rcases ha with ⟨w,hw,rfl⟩
    simp [normalizedDynkin, dynkin, hw]
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb, smul_add]
  | smul r a _ ha =>
    rw [map_smul, map_smul, ha, smul_comm]


-- @@ L408-412 verbatim
theorem normalizedDynkin_embed_word {n : ℕ} {p : FL α}
    (hp : WeightedWord (fun _ : α => 1) n p) : normalizedDynkin (embed p) = p := by
  obtain ⟨hn,hn',hp'⟩ := dynkin_embed_word hp
  rw [normalizedDynkin_homogeneous hn', hp', smul_smul, inv_mul_cancel₀, one_smul]
  exact_mod_cast (Nat.ne_of_gt hn)


-- @@ L414-436 verbatim
theorem mem_word_span (wt : α → ℕ) (p : FL α) :
    p ∈ Submodule.span ℝ {q | ∃ n, WeightedWord wt n q} := by
  let S : Submodule ℝ (FL α) := Submodule.span ℝ {q | ∃ n, WeightedWord wt n q}
  change p ∈ S
  induction p using freeLie_induction with
  | h0 => exact S.zero_mem
  | hg a => exact Submodule.subset_span ⟨wt a, WeightedWord.generator a⟩
  | ha a b ha hb => exact S.add_mem ha hb
  | hs r a ha => exact S.smul_mem r ha
  | hl a b ha hb =>
    induction ha using Submodule.span_induction with
    | mem a ha =>
      rcases ha with ⟨n, hn⟩
      induction hb using Submodule.span_induction with
      | mem b hb =>
        rcases hb with ⟨m, hm⟩
        exact Submodule.subset_span ⟨n+m, WeightedWord.bracket hn hm⟩
      | zero => simp
      | add b c _ _ hb hc => simpa only [lie_add] using S.add_mem hb hc
      | smul r b _ hb => simpa only [lie_smul] using S.smul_mem r hb
    | zero => simp
    | add a c _ _ ha hc => simpa only [add_lie] using S.add_mem ha hc
    | smul r a _ ha => simpa only [smul_lie] using S.smul_mem r ha


-- @@ L438-446 verbatim
theorem normalizedDynkin_embed (p : FL α) : normalizedDynkin (embed p) = p := by
  have hp := mem_word_span (fun _ : α => 1) p
  induction hp using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨n,hn⟩ := ha
    exact normalizedDynkin_embed_word hn
  | zero => simp
  | add a b _ _ ha hb => simp [ha, hb]
  | smul r a _ ha => simp [ha]


-- @@ L448-449 verbatim
theorem embed_injective : Function.Injective (embed (α := α)) :=
  Function.LeftInverse.injective normalizedDynkin_embed


-- @@ L451-451 verbatim
end AssociativeModel


-- @@ L453-453 verbatim
namespace FreeDerivations


-- @@ L455-455 verbatim
variable {R : Type*} [CommRing R]

-- @@ L456-456 verbatim
variable {M : Type*} [LieRing M] [LieAlgebra R M]


-- @@ L458-460 verbatim
structure Jet (R M : Type*) [CommRing R] [LieRing M] [LieAlgebra R M] where
  base : M
  velocity : M


-- @@ L462-466 verbatim
def Jet.equiv : Jet R M ≃ M × M where
  toFun z := (z.base, z.velocity)
  invFun z := ⟨z.1, z.2⟩
  left_inv _ := rfl
  right_inv _ := rfl


-- @@ L468-468 verbatim
instance : AddCommGroup (Jet R M) := Jet.equiv.addCommGroup

-- @@ L469-469 verbatim
instance : Module R (Jet R M) := Jet.equiv.addEquiv.module R

-- @@ L470-472 verbatim
instance : Bracket (Jet R M) (Jet R M) :=
  ⟨fun a b => ⟨⁅a.base, b.base⁆,
    ⁅a.velocity, b.base⁆ + ⁅a.base, b.velocity⁆⟩⟩


-- @@ L474-475 verbatim
@[ext] theorem Jet.ext {a b : Jet R M} (h : a.base = b.base)
    (k : a.velocity = b.velocity) : a = b := by cases a; cases b; simp_all


-- @@ L477-477 verbatim
@[simp] theorem Jet.base_zero : (0 : Jet R M).base = 0 := rfl

-- @@ L478-478 verbatim
@[simp] theorem Jet.velocity_zero : (0 : Jet R M).velocity = 0 := rfl

-- @@ L479-479 verbatim
@[simp] theorem Jet.base_add (a b : Jet R M) : (a+b).base = a.base+b.base := rfl

-- @@ L480-481 verbatim
@[simp] theorem Jet.velocity_add (a b : Jet R M) :
    (a+b).velocity = a.velocity+b.velocity := rfl

-- @@ L482-482 verbatim
@[simp] theorem Jet.base_smul (q : R) (a : Jet R M) : (q • a).base = q • a.base := rfl

-- @@ L483-484 verbatim
@[simp] theorem Jet.velocity_smul (q : R) (a : Jet R M) :
    (q • a).velocity = q • a.velocity := rfl

-- @@ L485-485 verbatim
@[simp] theorem Jet.base_lie (a b : Jet R M) : ⁅a,b⁆.base = ⁅a.base,b.base⁆ := rfl

-- @@ L486-487 verbatim
@[simp] theorem Jet.velocity_lie (a b : Jet R M) :
    ⁅a,b⁆.velocity = ⁅a.velocity,b.base⁆ + ⁅a.base,b.velocity⁆ := rfl


-- @@ L489-498 verbatim
instance : LieRing (Jet R M) where
  add_lie a b c := by (ext <;> simp [add_lie]); abel
  lie_add a b c := by (ext <;> simp [lie_add]); abel
  lie_self a := by
    ext
    · simp
    · change ⁅a.velocity, a.base⁆ + ⁅a.base, a.velocity⁆ = 0
      rw [← lie_skew a.velocity a.base]
      exact neg_add_cancel _
  leibniz_lie a b c := by (ext <;> simp [lie_add, add_lie, lie_lie]); abel

-- @@ L499-500 verbatim
instance : LieAlgebra R (Jet R M) where
  lie_smul q a b := by ext <;> simp [lie_smul, smul_add]


-- @@ L502-506 verbatim
def Jet.baseHom : Jet R M →ₗ⁅R⁆ M where
  toFun := Jet.base
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_lie' {_ _} := rfl


-- @@ L508-508 verbatim
variable {α : Type*}

-- @@ L509-509 verbatim
local notation "F" => FreeLieAlgebra R α


-- @@ L511-512 verbatim
def jetLift (f : α → F) : F →ₗ⁅R⁆ Jet R F :=
  FreeLieAlgebra.lift R (fun a => ⟨FreeLieAlgebra.of R a, f a⟩)


-- @@ L514-521 verbatim
@[simp] theorem jetLift_base (f : α → F) (p : F) :
    (jetLift f p).base = p := by
  have h : Jet.baseHom.comp (jetLift f) = LieHom.id := by
    apply FreeLieAlgebra.hom_ext
    intro a
    simp [jetLift, Jet.baseHom]
    rfl
  exact LieHom.congr_fun h p


-- @@ L523-536 verbatim
def extend (f : α → F) : LieDerivation R F F where
  toFun q := (jetLift f q).velocity
  map_add' a b := by
    change (jetLift f (a+b)).velocity = _
    rw [map_add]
    rfl
  map_smul' r a := by
    change (jetLift f (r • a)).velocity = _
    rw [map_smul]
    rfl
  leibniz' a b := by
    change (jetLift f ⁅a,b⁆).velocity = ⁅a,(jetLift f b).velocity⁆ - ⁅b,(jetLift f a).velocity⁆
    rw [LieHom.map_lie, Jet.velocity_lie, jetLift_base, jetLift_base]
    rw [sub_eq_add_neg, lie_skew, add_comm]


-- @@ L538-541 verbatim
@[simp] theorem extend_of (f : α → F) (a : α) :
    extend f (FreeLieAlgebra.of R a) = f a := by
  change (jetLift f (FreeLieAlgebra.of R a)).velocity = _
  simp [jetLift]


-- @@ L543-552 verbatim
@[ext] theorem ext {d₁ d₂ : LieDerivation R F F}
    (h : ∀ a, d₁ (FreeLieAlgebra.of R a) = d₂ (FreeLieAlgebra.of R a)) : d₁ = d₂ := by
  apply DFunLike.ext
  intro q
  induction q using freeLie_induction with
  | h0 => simp
  | hg a => exact h a
  | ha a b ha hb => simp [ha, hb]
  | hs r a ha => simp [ha]
  | hl a b ha hb => simp [ha, hb]


-- @@ L554-558 verbatim
theorem extend_unique (f : α → F) (d : LieDerivation R F F)
    (h : ∀ a, d (FreeLieAlgebra.of R a) = f a) : d = extend f := by
  apply ext
  intro a
  simpa using h a


-- @@ L560-560 verbatim
variable [DecidableEq α]

-- @@ L561-563 verbatim
def pair (i j : α) : LieDerivation R F F :=
  extend (fun k => if k = i then ⁅FreeLieAlgebra.of R i, FreeLieAlgebra.of R j⁆
    else if k = j then ⁅FreeLieAlgebra.of R j, FreeLieAlgebra.of R i⁆ else 0)


-- @@ L565-567 verbatim
@[simp] theorem pair_of_left (i j : α) :
    pair (R := R) i j (FreeLieAlgebra.of R i) = ⁅FreeLieAlgebra.of R i,FreeLieAlgebra.of R j⁆ := by
  simp [pair]


-- @@ L569-573 verbatim
@[simp] theorem pair_of_right (i j : α) :
    pair (R := R) i j (FreeLieAlgebra.of R j) = ⁅FreeLieAlgebra.of R j,FreeLieAlgebra.of R i⁆ := by
  by_cases h : j = i
  · subst j; simp
  · simp [pair, h]


-- @@ L575-577 verbatim
@[simp] theorem pair_of_other (i j k : α) (hi : k ≠ i) (hj : k ≠ j) :
    pair (R := R) i j (FreeLieAlgebra.of R k) = 0 := by
  simp [pair, hi, hj]


-- @@ L579-586 verbatim
theorem pair_comm (i j : α) : pair (R := R) i j = pair j i := by
  apply ext
  intro a
  by_cases hi : a=i
  · subst a; simp
  by_cases hj : a=j
  · subst a; simp
  simp [hi,hj]


-- @@ L588-593 verbatim
theorem pair_self (i : α) : pair (R := R) i i = 0 := by
  apply ext
  intro a
  by_cases hi : a=i
  · subst a; simp
  simp [hi]


-- @@ L595-608 verbatim
theorem pair_disjoint (i j k l : α)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    ⁅pair (R := R) i j,pair (R := R) k l⁆ = 0 := by
  apply ext
  intro a
  by_cases hai : a=i
  · subst a; simp [hik,hil,hjk,hjl]
  by_cases haj : a=j
  · subst a; simp [hik,hil,hjk,hjl]
  by_cases hak : a=k
  · subst a; simp [hik.symm,hjk.symm,hil.symm,hjl.symm]
  by_cases hal : a=l
  · subst a; simp [hik.symm,hjk.symm,hil.symm,hjl.symm]
  simp [hai,haj,hak,hal]


-- @@ L610-626 verbatim
theorem pair_three (i j k : α) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅pair (R := R) i j, pair (R := R) i k + pair (R := R) j k⁆ = 0 := by
  apply ext
  intro a
  by_cases hai : a=i
  · subst a
    simp [hik,hij,hjk,hij.symm,hik.symm,hjk.symm]
    grind [lie_skew, lie_lie]
  by_cases haj : a=j
  · subst a
    simp [hik,hij,hjk,hij.symm,hik.symm,hjk.symm]
    grind [lie_skew, lie_lie]
  by_cases hak : a=k
  · subst a
    simp [hik.symm,hjk.symm]
    grind [lie_skew, lie_lie]
  simp [hai,haj,hak]


-- @@ L628-628 verbatim
end FreeDerivations


-- @@ L630-630 verbatim
namespace BraidRepresentation

-- @@ L631-631 verbatim
open FreeDerivations LieAlgebra

-- @@ L632-632 verbatim
variable {R α : Type*} [CommRing R] [DecidableEq α]

-- @@ L633-633 verbatim
local notation "F" => FreeLieAlgebra R α

-- @@ L634-634 verbatim
local notation "Der" => LieDerivation R F F

-- @@ L635-635 verbatim
local notation "SD" => SemiDirectSum F Der (LieHom.id : Der →ₗ⁅R⁆ Der)


-- @@ L637-637 verbatim
def fiber (i : α) : SD := SemiDirectSum.inl LieHom.id (FreeLieAlgebra.of R i)

-- @@ L638-638 verbatim
def base (i j : α) : SD := SemiDirectSum.inr LieHom.id (pair i j)


-- @@ L640-644 verbatim
def chord : Option α → Option α → SD
  | none, none => 0
  | none, some j => fiber j
  | some i, none => fiber i
  | some i, some j => base i j


-- @@ L646-646 verbatim
@[simp] theorem chord_none_none : chord (R := R) (α := α) none none = 0 := rfl

-- @@ L647-647 verbatim
@[simp] theorem chord_none_some (j : α) : chord (R := R) none (some j) = fiber j := rfl

-- @@ L648-648 verbatim
@[simp] theorem chord_some_none (i : α) : chord (R := R) (some i) none = fiber i := rfl

-- @@ L649-649 verbatim
@[simp] theorem chord_some_some (i j : α) : chord (R := R) (some i) (some j) = base i j := rfl


-- @@ L651-652 verbatim
theorem chord_comm (i j : Option α) : chord (R := R) i j = chord j i := by
  cases i <;> cases j <;> simp [base, pair_comm]


-- @@ L654-655 verbatim
@[simp] theorem chord_self (i : Option α) : chord (R := R) i i = 0 := by
  cases i <;> simp [base, pair_self]


-- @@ L657-660 verbatim
theorem base_fiber (i j k : α) :
    ⁅base (R := R) i j, fiber k⁆ = SemiDirectSum.inl LieHom.id
      (pair (R := R) i j (FreeLieAlgebra.of R k)) := by
  simp [base, fiber]


-- @@ L662-665 verbatim
theorem fiber_base (i j k : α) :
    ⁅fiber (R := R) k, base i j⁆ = - SemiDirectSum.inl LieHom.id
      (pair (R := R) i j (FreeLieAlgebra.of R k)) := by
  rw [← lie_skew, base_fiber]


-- @@ L667-672 verbatim
theorem chord_disjoint (i j k l : Option α)
    (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) :
    ⁅chord (R := R) i j, chord (R := R) k l⁆ = 0 := by
  cases i <;> cases j <;> cases k <;> cases l <;>
    simp_all [base, fiber, pair_disjoint]
  all_goals apply pair_of_other <;> intro h <;> subst_vars <;> contradiction


-- @@ L674-707 verbatim
theorem chord_three (i j k : Option α)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅chord (R := R) i j, chord (R := R) i k + chord (R := R) j k⁆ = 0 := by
  cases i with
  | none =>
    cases j with
    | none => exact (hij rfl).elim
    | some j =>
      cases k with
      | none => exact (hik rfl).elim
      | some k =>
        rw [chord_none_some, chord_none_some, chord_some_some, lie_add, fiber_base]
        simp [fiber]
        grind [lie_skew]
  | some i =>
    cases j with
    | none =>
      cases k with
      | none => exact (hjk rfl).elim
      | some k =>
        rw [chord_some_none, chord_some_some, chord_none_some, lie_add, fiber_base]
        simp [fiber]
        grind [lie_skew]
    | some j =>
      cases k with
      | none =>
        rw [chord_some_some, chord_some_none, chord_some_none, lie_add,
          base_fiber, base_fiber]
        simp only [pair_of_left, pair_of_right, ← map_add]
        grind [lie_skew]
      | some k =>
        simp only [chord_some_some, base, ← map_add, ← LieHom.map_lie]
        rw [pair_three _ _ _ (fun h => hij (congrArg some h))
          (fun h => hik (congrArg some h)) (fun h => hjk (congrArg some h)), map_zero]


-- @@ L709-709 verbatim
end BraidRepresentation


-- @@ L711-711 verbatim
namespace BraidModel

-- @@ L712-712 verbatim
open LieAlgebra

-- @@ L713-713 verbatim
abbrev Fiber := FreeLieAlgebra ℝ (Fin 3)

-- @@ L714-714 verbatim
abbrev Der := LieDerivation ℝ Fiber Fiber

-- @@ L715-715 verbatim
abbrev Model := SemiDirectSum Fiber Der (LieHom.id : Der →ₗ⁅ℝ⁆ Der)

-- @@ L716-717 verbatim
def chord (i j : Fin 4) : Model :=
  BraidRepresentation.chord (finSuccEquiv' (1 : Fin 4) i) (finSuccEquiv' (1 : Fin 4) j)


-- @@ L719-720 verbatim
theorem chord_comm (i j : Fin 4) : chord i j = chord j i :=
  BraidRepresentation.chord_comm _ _


-- @@ L722-723 verbatim
@[simp] theorem chord_self (i : Fin 4) : chord i i = 0 :=
  BraidRepresentation.chord_self _


-- @@ L725-725 verbatim
def preMap : BraidFree →ₗ⁅ℝ⁆ Model := FreeLieAlgebra.lift ℝ (fun e => chord e.val.1 e.val.2)


-- @@ L727-734 verbatim
@[simp] theorem preMap_chord (i j : Fin 4) : preMap (RealDeligneDrinfeld.chord i j) = chord i j := by
  unfold RealDeligneDrinfeld.chord
  split_ifs with hij hji
  · simp [preMap]
  · simp [preMap, chord_comm j i]
  · have h : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
    subst j
    simp


-- @@ L736-748 verbatim
theorem ideal_le_ker : braidIdeal ≤ preMap.ker := by
  rw [braidIdeal, LieSubmodule.lieSpan_le]
  intro z hz
  change preMap z = 0
  rcases hz with ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩ | ⟨i,j,k,hij,hik,hjk,rfl⟩
  · rw [LieHom.map_lie, preMap_chord, preMap_chord]
    exact BraidRepresentation.chord_disjoint _ _ _ _
      ((finSuccEquiv' (1 : Fin 4)).injective.ne hik) ((finSuccEquiv' (1 : Fin 4)).injective.ne hil)
      ((finSuccEquiv' (1 : Fin 4)).injective.ne hjk) ((finSuccEquiv' (1 : Fin 4)).injective.ne hjl)
  · rw [LieHom.map_lie, map_add, preMap_chord, preMap_chord, preMap_chord]
    exact BraidRepresentation.chord_three _ _ _
      ((finSuccEquiv' (1 : Fin 4)).injective.ne hij) ((finSuccEquiv' (1 : Fin 4)).injective.ne hik)
      ((finSuccEquiv' (1 : Fin 4)).injective.ne hjk)


-- @@ L750-756 verbatim
def map : T4 →ₗ⁅ℝ⁆ Model :=
  { braidIdeal.toSubmodule.liftQ preMap.toLinearMap ideal_le_ker with
    map_lie' := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | _ a =>
        induction b using Submodule.Quotient.induction_on with | _ b =>
          exact preMap.map_lie a b }


-- @@ L758-758 verbatim
@[simp] theorem map_t (i j : Fin 4) : map (t i j) = chord i j := preMap_chord i j


-- @@ L760-760 verbatim
end BraidModel


-- @@ L762-762 verbatim
namespace AssociativeModel

-- @@ L763-763 verbatim
attribute [local instance] LieRing.ofAssociativeRing

-- @@ L764-764 verbatim
variable {α : Type*}


-- @@ L766-775 verbatim
theorem coeff_rotate {P : A α} {b : α} (h : atom b * P = P * atom b) (w : List α) :
    P.coeff (FreeMonoid.ofList (b :: w)) = P.coeff (FreeMonoid.ofList (w ++ [b])) := by
  calc
    P.coeff (FreeMonoid.ofList (b :: w)) =
        (P * atom b).coeff ((FreeMonoid.of b * FreeMonoid.ofList w) * FreeMonoid.of b) := by
      simp [atom, FreeMonoid.ofList_cons]
    _ = (atom b * P).coeff (FreeMonoid.of b * (FreeMonoid.ofList w * FreeMonoid.of b)) := by
      rw [h, mul_assoc]
    _ = P.coeff (FreeMonoid.ofList (w ++ [b])) := by
      simp [atom, FreeMonoid.ofList_append]


-- @@ L777-785 verbatim
theorem coeff_starts_ne {P : A α} {b a : α} (h : atom b * P = P * atom b)
    (hab : a ≠ b) (v : List α) : P.coeff (FreeMonoid.ofList (a :: v)) = 0 := by
  have hz : (atom b * P).coeff (FreeMonoid.ofList (a::v) * FreeMonoid.of b) = 0 := by
    apply MonoidAlgebra.coeff_single_mul_of_forall_mul_ne
    intro d hd
    have hh := congrArg (fun w : FreeMonoid α => w.toList.head?) hd
    exact hab (by simpa using hh.symm)
  rw [h] at hz
  simpa [atom] using hz


-- @@ L787-796 verbatim
theorem coeff_contains_ne {P : A α} {b a : α} (h : atom b * P = P * atom b)
    (hab : a ≠ b) (u v : List α) : P.coeff (FreeMonoid.ofList (u ++ a :: v)) = 0 := by
  induction u generalizing v with
  | nil => exact coeff_starts_ne h hab v
  | cons c u ih =>
    by_cases hc : c = b
    · subst c
      rw [List.cons_append, coeff_rotate h]
      simpa [List.append_assoc] using ih (v ++ [b])
    · exact coeff_starts_ne h hc (u ++ a :: v)


-- @@ L798-802 verbatim
theorem coeff_eq_zero_of_letter_ne {P : A α} {b a : α}
    (h : atom b * P = P * atom b) {w : List α} (ha : a ∈ w) (hab : a ≠ b) :
    P.coeff (FreeMonoid.ofList w) = 0 := by
  obtain ⟨u,v,rfl⟩ := List.append_of_mem ha
  exact coeff_contains_ne h hab u v


-- @@ L804-818 verbatim
theorem dynkinWord_all_eq (b : α) (w : List α) (hw : ∀ a ∈ w, a = b) :
    dynkinWord w ∈ Submodule.span ℝ {FreeLieAlgebra.of ℝ b} := by
  induction w with
  | nil => simp [dynkinWord]
  | cons a w ih =>
    have ha : a = b := hw a (by simp)
    subst a
    cases w with
    | nil => exact Submodule.subset_span (by simp [dynkinWord])
    | cons c w =>
      rw [dynkinWord]
      have hmem := ih (fun a ha => hw a (by simp [ha]))
      obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp hmem
      rw [← hr, lie_smul, lie_self, smul_zero]
      exact Submodule.zero_mem _


-- @@ L820-840 verbatim
theorem centralizer_generator {p : FL α} (b : α) (h : ⁅FreeLieAlgebra.of ℝ b,p⁆ = 0) :
    p ∈ Submodule.span ℝ {FreeLieAlgebra.of ℝ b} := by
  classical
  have hc : atom b * embed p = embed p * atom b := by
    have ht := congrArg embed h
    rw [LieHom.map_lie, embed_of, map_zero] at ht
    exact sub_eq_zero.mp ht
  rw [← normalizedDynkin_embed p, ← MonoidAlgebra.sum_coeff_single (embed p)]
  unfold Finsupp.sum
  rw [map_sum]
  apply Submodule.sum_mem
  intro w hw
  rw [normalizedDynkin, wordLinear_single]
  apply Submodule.smul_mem
  apply Submodule.smul_mem
  apply dynkinWord_all_eq
  intro a ha
  by_contra hab
  have hz := coeff_eq_zero_of_letter_ne hc ha hab
  have hn := Finsupp.mem_support_iff.mp hw
  exact hn (by simpa using hz)


-- @@ L842-842 verbatim
end AssociativeModel


-- @@ L844-851 verbatim
theorem map_eval {M N : Type*} [LieRing M] [LieAlgebra ℝ M]
    [LieRing N] [LieAlgebra ℝ N] (f : M →ₗ⁅ℝ⁆ N) (a b : M) (p : L) :
    f (eval a b p) = eval (f a) (f b) p := by
  have h : f.comp (eval a b) = eval (f a) (f b) := by
    apply FreeLieAlgebra.hom_ext
    intro i
    cases i <;> simp [eval]
  exact LieHom.congr_fun h p


-- @@ L853-856 verbatim
theorem eval_self : eval x y = LieHom.id := by
  apply FreeLieAlgebra.hom_ext
  intro i
  cases i <;> simp [eval, x, y]


-- @@ L858-866 verbatim
theorem eval_commutes {M : Type*} [LieRing M] [LieAlgebra ℝ M]
    (a b z : M) (ha : ⁅z,a⁆ = 0) (hb : ⁅z,b⁆ = 0) (p : L) :
    ⁅z,eval a b p⁆ = 0 := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [eval, ha, hb]
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hl p q hp hq => simp [LieHom.map_lie, leibniz_lie, hp, hq]


-- @@ L868-870 verbatim
@[simp] theorem chord_comm (i j : Fin 4) : chord i j = chord j i := by
  unfold chord
  split_ifs <;> first | rfl | omega


-- @@ L872-874 verbatim
@[simp] theorem t_comm (i j : Fin 4) : t i j = t j i := by
  unfold t
  rw [chord_comm]


-- @@ L876-881 verbatim
theorem t_disjoint (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ⁅t i j,t k l⁆ = 0 := by
  rw [t, t, ← LieSubmodule.Quotient.mk_bracket, LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan (Or.inl ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩)


-- @@ L883-887 verbatim
theorem t_three (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅t i j,t i k + t j k⁆ = 0 := by
  change LieSubmodule.Quotient.mk (⁅chord i j, chord i k + chord j k⁆) = (0 : T4)
  rw [LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan (Or.inr ⟨i,j,k,hij,hik,hjk,rfl⟩)


-- @@ L889-889 verbatim
namespace BraidModel


-- @@ L891-892 verbatim
def inclusion : Fiber →ₗ⁅ℝ⁆ T4 := FreeLieAlgebra.lift ℝ
  (fun i => t 1 ((finSuccEquiv' (1 : Fin 4)).symm (some i)))


-- @@ L894-897 verbatim
theorem map_inclusion : map.comp inclusion = LieAlgebra.SemiDirectSum.inl LieHom.id := by
  apply FreeLieAlgebra.hom_ext
  intro i
  simp [inclusion, chord, BraidRepresentation.fiber]


-- @@ L899-905 verbatim
theorem inclusion_injective : Function.Injective inclusion := by
  intro a b hab
  have h := congrArg map hab
  have hm (c : Fiber) : map (inclusion c) = LieAlgebra.SemiDirectSum.inl LieHom.id c :=
    LieHom.congr_fun map_inclusion c
  rw [hm,hm] at h
  exact LieAlgebra.SemiDirectSum.inl_injective _ h


-- @@ L907-907 verbatim
end BraidModel


-- @@ L909-910 verbatim
theorem commute_symm {M : Type*} [LieRing M] {a b : M} (h : ⁅a,b⁆ = 0) : ⁅b,a⁆ = 0 := by
  rw [← lie_skew, h, neg_zero]


-- @@ L912-918 verbatim
theorem evals_commute {M : Type*} [LieRing M] [LieAlgebra ℝ M]
    (a b c d : M) (hac : ⁅a,c⁆ = 0) (had : ⁅a,d⁆ = 0)
    (hbc : ⁅b,c⁆ = 0) (hbd : ⁅b,d⁆ = 0) (p q : L) :
    ⁅eval a b p,eval c d q⁆ = 0 := by
  apply eval_commutes
  · exact commute_symm (eval_commutes a b c (commute_symm hac) (commute_symm hbc) p)
  · exact commute_symm (eval_commutes a b d (commute_symm had) (commute_symm hbd) p)


-- @@ L920-933 verbatim
theorem eval_add_of_commuting {M : Type*} [LieRing M] [LieAlgebra ℝ M]
    (a b c d : M) (hac : ⁅a,c⁆ = 0) (had : ⁅a,d⁆ = 0)
    (hbc : ⁅b,c⁆ = 0) (hbd : ⁅b,d⁆ = 0) (p : L) :
    eval (a+c) (b+d) p = eval a b p + eval c d p := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [eval]
  | ha p q hp hq => simp [hp,hq]; abel
  | hs r p hp => simp [hp,smul_add]
  | hl p q hp hq =>
    simp only [LieHom.map_lie, hp, hq, add_lie, lie_add]
    rw [evals_commute a b c d hac had hbc hbd p q,
      commute_symm (evals_commute a b c d hac had hbc hbd q p)]
    simp


-- @@ L935-947 verbatim
theorem eval_vanish_of_commuting {M : Type*} [LieRing M] [LieAlgebra ℝ M]
    (a b : M) (hab : ⁅a,b⁆ = 0) {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1 < n) :
    eval a b p = 0 := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    cases hp with
    | generator i => omega
    | @bracket n m p q hp hq =>
      rw [LieHom.map_lie]
      exact evals_commute a b a b (lie_self a) hab (commute_symm hab) (lie_self b) p q
  | zero => simp
  | add p q _ _ hp hq => simp [hp,hq]
  | smul r p _ hp => simp [hp]


-- @@ L949-954 verbatim
theorem eval_central_shift {M : Type*} [LieRing M] [LieAlgebra ℝ M]
    (a b c : M) (hac : ⁅a,c⁆ = 0) (hbc : ⁅b,c⁆ = 0)
    {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1 < n) :
    eval a (b+c) p = eval a b p := by
  have h := eval_add_of_commuting a b 0 c (lie_zero a) hac (lie_zero b) hbc p
  simpa [eval_vanish_of_commuting 0 c (zero_lie c) hp hn] using h


-- @@ L956-956 verbatim
namespace T4Universal

-- @@ L957-957 verbatim
variable {M : Type*} [LieRing M] [LieAlgebra ℝ M]


-- @@ L959-960 verbatim
def pre (f : Fin 4 → Fin 4 → M) : BraidFree →ₗ⁅ℝ⁆ M :=
  FreeLieAlgebra.lift ℝ (fun e => f e.val.1 e.val.2)


-- @@ L962-971 verbatim
theorem pre_chord (f : Fin 4 → Fin 4 → M)
    (hs : ∀ i j, f i j = f j i) (hz : ∀ i, f i i = 0) (i j : Fin 4) :
    pre f (chord i j) = f i j := by
  unfold chord
  split_ifs with hij hji
  · simp [pre]
  · simp [pre, hs j i]
  · have h : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
    subst j
    simp [hz]


-- @@ L973-990 verbatim
def lift (f : Fin 4 → Fin 4 → M)
    (hs : ∀ i j, f i j = f j i) (hz : ∀ i, f i i = 0)
    (hd : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      ⁅f i j,f k l⁆ = 0)
    (ht : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ⁅f i j,f i k+f j k⁆ = 0) : T4 →ₗ⁅ℝ⁆ M := by
  have hker : braidIdeal ≤ (pre f).ker := by
    rw [braidIdeal, LieSubmodule.lieSpan_le]
    intro z hz'
    change pre f z = 0
    rcases hz' with ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩ | ⟨i,j,k,hij,hik,hjk,rfl⟩
    · simpa only [LieHom.map_lie, pre_chord f hs hz] using hd i j k l hij hik hil hjk hjl hkl
    · simpa only [LieHom.map_lie, map_add, pre_chord f hs hz] using ht i j k hij hik hjk
  exact { braidIdeal.toSubmodule.liftQ (pre f).toLinearMap hker with
    map_lie' := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | _ a =>
        induction b using Submodule.Quotient.induction_on with | _ b =>
          exact (pre f).map_lie a b }


-- @@ L992-993 verbatim
@[simp] theorem lift_t (f : Fin 4 → Fin 4 → M) (hs hz hd ht) (i j : Fin 4) :
    lift f hs hz hd ht (t i j) = f i j := pre_chord f hs hz i j


-- @@ L995-995 verbatim
end T4Universal


-- @@ L997-997 verbatim
@[simp] theorem t_self (i : Fin 4) : t i i = 0 := by simp [t, chord]


-- @@ L999-1006 verbatim
def t4Rename (e : Equiv.Perm (Fin 4)) : T4 →ₗ⁅ℝ⁆ T4 :=
  T4Universal.lift (fun i j => t (e i) (e j))
    (fun _ _ => t_comm _ _) (fun _ => t_self _)
    (fun _ _ _ _ hij hik hil hjk hjl hkl => t_disjoint _ _ _ _
      (e.injective.ne hij) (e.injective.ne hik) (e.injective.ne hil)
      (e.injective.ne hjk) (e.injective.ne hjl) (e.injective.ne hkl))
    (fun _ _ _ hij hik hjk => t_three _ _ _
      (e.injective.ne hij) (e.injective.ne hik) (e.injective.ne hjk))


-- @@ L1008-1009 verbatim
@[simp] theorem t4Rename_t (e : Equiv.Perm (Fin 4)) (i j : Fin 4) :
    t4Rename e (t i j) = t (e i) (e j) := T4Universal.lift_t _ _ _ _ _ _ _


-- @@ L1011-1016 verbatim
theorem solution_swap {p : L} (hp : p ∈ W)
    {M : Type*} [LieRing M] [LieAlgebra ℝ M] (a b : M) :
    eval a b p = - eval b a p := by
  have h := congrArg (eval a b) hp.1
  simp only [map_add, map_zero, map_eval, eval_x, eval_y] at h
  exact eq_neg_of_add_eq_zero_left h


-- @@ L1018-1022 verbatim
theorem solution_three {p : L} (hp : p ∈ W)
    {M : Type*} [LieRing M] [LieAlgebra ℝ M] (a b : M) :
    eval a b p + eval b (-a-b) p + eval (-a-b) a p = 0 := by
  have h := congrArg (eval a b) hp.2.1
  simpa only [map_add, map_zero, map_eval, map_sub, map_neg, eval_x, eval_y] using h


-- @@ L1024-1050 verbatim
theorem free_action_inner {R α β Z : Type*} [CommRing R]
    [LieRing Z] [LieAlgebra R Z]
    (f : FreeLieAlgebra R α →ₗ⁅R⁆ Z) (g : FreeLieAlgebra R β →ₗ⁅R⁆ Z)
    (h : FreeLieAlgebra R β →ₗ⁅R⁆ LieDerivation R (FreeLieAlgebra R α) (FreeLieAlgebra R α))
    (hg : ∀ b a, f (h (FreeLieAlgebra.of R b) (FreeLieAlgebra.of R a)) =
      ⁅g (FreeLieAlgebra.of R b),f (FreeLieAlgebra.of R a)⁆)
    (q : FreeLieAlgebra R β) (p : FreeLieAlgebra R α) :
    f (h q p) = ⁅g q,f p⁆ := by
  have H : ∀ q : FreeLieAlgebra R β, ∀ p : FreeLieAlgebra R α,
      f (h q p) = ⁅g q,f p⁆ := by
    intro q
    induction q using freeLie_induction with
    | h0 => intro p; simp
    | hg b =>
      intro p
      induction p using freeLie_induction with
      | h0 => simp
      | hg a => exact hg b a
      | ha p r hp hr => simp [hp,hr]
      | hs c p hp => simp [hp]
      | hl p r hp hr =>
        simp [hp,hr,LieHom.map_lie]
        grind [lie_lie,lie_skew]
    | ha q r hq hr => intro p; simp [hq,hr]
    | hs c q hq => intro p; simp [hq]
    | hl q r hq hr => intro p; simp [LieHom.map_lie,hq,hr,lie_lie]
  exact H q p


-- @@ L1052-1052 verbatim
namespace InnerSemiDirect

-- @@ L1053-1053 verbatim
open LieAlgebra

-- @@ L1054-1056 verbatim
variable {R K B Z : Type*} [CommRing R]
  [LieRing K] [LieAlgebra R K] [LieRing B] [LieAlgebra R B]
  [LieRing Z] [LieAlgebra R Z]

-- @@ L1057-1059 verbatim
variable (action : B →ₗ⁅R⁆ LieDerivation R K K)
  (f : K →ₗ⁅R⁆ Z) (g : B →ₗ⁅R⁆ Z)
  (h : ∀ q p, f (action q p) = ⁅g q,f p⁆)


-- @@ L1061-1069 verbatim
def lift : SemiDirectSum K B action →ₗ⁅R⁆ Z where
  toFun z := f z.left + g z.right
  map_add' z t := by simp; abel
  map_smul' c z := by simp [smul_add]
  map_lie' {z t} := by
    simp only [SemiDirectSum.lie_eq_mk, map_sub, map_add, LieHom.map_lie, h,
      add_lie, lie_add]
    rw [sub_eq_add_neg, lie_skew]
    abel


-- @@ L1071-1072 verbatim
@[simp] theorem lift_inl (p : K) : lift action f g h (SemiDirectSum.inl action p) = f p := by
  simp [lift]

-- @@ L1073-1074 verbatim
@[simp] theorem lift_inr (p : B) : lift action f g h (SemiDirectSum.inr action p) = g p := by
  simp [lift]

-- @@ L1075-1075 verbatim
end InnerSemiDirect


-- @@ L1077-1077 verbatim
namespace SpecialFiber

-- @@ L1078-1078 verbatim
open LieAlgebra FreeDerivations

-- @@ L1079-1079 verbatim
abbrev F := FreeLieAlgebra ℝ (Fin 3)

-- @@ L1080-1080 verbatim
def fa : F := FreeLieAlgebra.of ℝ 0

-- @@ L1081-1081 verbatim
def fb : F := FreeLieAlgebra.of ℝ 1

-- @@ L1082-1082 verbatim
def fc : F := FreeLieAlgebra.of ℝ 2


-- @@ L1084-1084 verbatim
def action : L →ₗ⁅ℝ⁆ LieDerivation ℝ F F := eval (pair 0 1) (pair 1 2)

-- @@ L1085-1085 verbatim
abbrev M := SemiDirectSum F L action


-- @@ L1087-1087 verbatim
def a : M := SemiDirectSum.inl action fa

-- @@ L1088-1088 verbatim
def b : M := SemiDirectSum.inl action fb

-- @@ L1089-1089 verbatim
def c : M := SemiDirectSum.inl action fc

-- @@ L1090-1090 verbatim
def u : M := SemiDirectSum.inr action x

-- @@ L1091-1091 verbatim
def v : M := SemiDirectSum.inr action y

-- @@ L1092-1092 verbatim
def w : M := -a-b-c-u-v


-- @@ L1094-1096 verbatim
theorem au : ⁅a,u⁆ = -⁅a,b⁆ := by
  simp only [a,u,b, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk, SemiDirectSum.neg_eq_mk]
  ext <;> simp [action,fa,fb]

-- @@ L1097-1099 verbatim
theorem bu : ⁅b,u⁆ = ⁅a,b⁆ := by
  simp only [a,u,b, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk]
  ext <;> simp [action,fa,fb]

-- @@ L1100-1102 verbatim
theorem cu : ⁅c,u⁆ = 0 := by
  simp only [c,u, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk]
  ext <;> simp [action,fc]

-- @@ L1103-1105 verbatim
theorem av : ⁅a,v⁆ = 0 := by
  simp only [a,v, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk]
  ext <;> simp [action,fa]

-- @@ L1106-1108 verbatim
theorem bv : ⁅b,v⁆ = -⁅b,c⁆ := by
  simp only [b,v,c, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk, SemiDirectSum.neg_eq_mk]
  ext <;> simp [action,fb,fc]

-- @@ L1109-1111 verbatim
theorem cv : ⁅c,v⁆ = ⁅b,c⁆ := by
  simp only [b,v,c, SemiDirectSum.lie_eq_mk, SemiDirectSum.inl_eq_mk, SemiDirectSum.inr_eq_mk]
  ext <;> simp [action,fb,fc]


-- @@ L1113-1121 verbatim
def chord (i j : Fin 4) : M :=
  match i.val, j.val with
  | 0,1 | 1,0 => a
  | 0,2 | 2,0 => u
  | 0,3 | 3,0 => w
  | 1,2 | 2,1 => b
  | 1,3 | 3,1 => c
  | 2,3 | 3,2 => v
  | _,_ => 0


-- @@ L1123-1124 verbatim
private theorem chord_symm (i j : Fin 4) : chord i j = chord j i := by
  fin_cases i <;> fin_cases j <;> rfl


-- @@ L1126-1126 verbatim
private theorem chord_zero (i : Fin 4) : chord i i = 0 := by fin_cases i <;> rfl


-- @@ L1128-1137 verbatim
private theorem chord_disjoint (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) : ⁅chord i j,chord k l⁆ = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all only [ne_eq, not_true_eq_false]
  all_goals fin_cases k <;> simp_all only [not_true_eq_false]
  all_goals fin_cases l <;> simp_all only [not_true_eq_false]
  all_goals dsimp only [chord]
  all_goals simp only [w, lie_sub, sub_lie, lie_neg, neg_lie,
    bu,cu,av,bv,lie_self]
  all_goals grind [lie_skew, au,bu,cu,av,bv,cv]


-- @@ L1139-1147 verbatim
private theorem chord_three (i j k : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅chord i j,chord i k+chord j k⁆ = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all only [ne_eq, not_true_eq_false]
  all_goals fin_cases k <;> simp_all only [not_true_eq_false]
  all_goals dsimp only [chord]
  all_goals simp only [w, lie_sub, sub_lie, lie_neg, neg_lie, lie_add,
    au,bu,cu,av,bv,cv,lie_self]
  all_goals grind [lie_skew, au,bu,cu,av,bv,cv]


-- @@ L1149-1150 verbatim
def representation : T4 →ₗ⁅ℝ⁆ M :=
  T4Universal.lift chord chord_symm chord_zero chord_disjoint chord_three


-- @@ L1152-1153 verbatim
@[simp] theorem representation_t (i j : Fin 4) : representation (t i j) = chord i j :=
  T4Universal.lift_t _ _ _ _ _ _ _


-- @@ L1155-1156 verbatim
def fiberSpec : F →ₗ⁅ℝ⁆ L := FreeLieAlgebra.lift ℝ
  (fun i => if i = 0 then x else if i = 1 then y else -x-y)

-- @@ L1157-1157 verbatim
def baseSpec : L →ₗ⁅ℝ⁆ L := eval (-x-y) x


-- @@ L1159-1159 verbatim
@[simp] theorem fiberSpec_fa : fiberSpec fa = x := by simp [fiberSpec,fa]

-- @@ L1160-1160 verbatim
@[simp] theorem fiberSpec_fb : fiberSpec fb = y := by simp [fiberSpec,fb]

-- @@ L1161-1161 verbatim
@[simp] theorem fiberSpec_fc : fiberSpec fc = -x-y := by simp [fiberSpec,fc]

-- @@ L1162-1162 verbatim
@[simp] theorem baseSpec_x : baseSpec x = -x-y := eval_x _ _

-- @@ L1163-1163 verbatim
@[simp] theorem baseSpec_y : baseSpec y = x := eval_y _ _


-- @@ L1165-1171 verbatim
theorem spec_equivariant (q : L) (p : F) :
    fiberSpec (action q p) = ⁅baseSpec q,fiberSpec p⁆ := by
  apply free_action_inner
  intro i j
  cases i <;> fin_cases j <;>
    simp [action, eval, baseSpec, fiberSpec, FreeDerivations.pair,
      x,y,sub_lie,neg_lie,lie_sub,lie_neg]


-- @@ L1173-1173 verbatim
def specialize : M →ₗ⁅ℝ⁆ L := InnerSemiDirect.lift action fiberSpec baseSpec spec_equivariant


-- @@ L1175-1175 verbatim
@[simp] theorem specialize_a : specialize a = x := by simp [specialize,a, InnerSemiDirect.lift]

-- @@ L1176-1176 verbatim
@[simp] theorem specialize_b : specialize b = y := by simp [specialize,b, InnerSemiDirect.lift]

-- @@ L1177-1177 verbatim
@[simp] theorem specialize_c : specialize c = -x-y := by simp [specialize,c, InnerSemiDirect.lift]

-- @@ L1178-1178 verbatim
@[simp] theorem specialize_u : specialize u = -x-y := by simp [specialize,u, InnerSemiDirect.lift]

-- @@ L1179-1179 verbatim
@[simp] theorem specialize_v : specialize v = x := by simp [specialize,v, InnerSemiDirect.lift]


-- @@ L1181-1183 verbatim
@[simp] theorem eval_right (d e : M) (p : L) :
    (eval d e p).right = eval d.right e.right p :=
  map_eval (SemiDirectSum.projr action) d e p


-- @@ L1185-1185 verbatim
def Fa (p : L) : F := (eval (u+b) v p - eval u v p).left

-- @@ L1186-1186 verbatim
def Fb (p : L) : F := (eval (u+a) (v+c) p - eval u v p).left

-- @@ L1187-1187 verbatim
def Fc (p : L) : F := (eval u (v+b) p - eval u v p).left

 
-- @@ L1189-1192 verbatim
theorem Fa_inl (p : L) : SemiDirectSum.inl action (Fa p) = eval (u+b) v p - eval u v p := by
  ext
  · rfl
  · simp [eval_right, u,b,v]
 
-- @@ L1193-1196 verbatim
theorem Fb_inl (p : L) : SemiDirectSum.inl action (Fb p) = eval (u+a) (v+c) p - eval u v p := by
  ext
  · rfl
  · simp [eval_right, u,a,v,c]
 
-- @@ L1197-1200 verbatim
theorem Fc_inl (p : L) : SemiDirectSum.inl action (Fc p) = eval u (v+b) p - eval u v p := by
  ext
  · rfl
  · simp [eval_right, u,b,v]


-- @@ L1202-1205 verbatim
theorem eval_comm_a (p : L) : ⁅a,eval (u+b) v p⁆ = 0 := by
  apply eval_commutes
  · rw [lie_add,au]; exact neg_add_cancel _
  · exact av

-- @@ L1206-1209 verbatim
theorem eval_comm_b (p : L) : ⁅b,eval (u+a) (v+c) p⁆ = 0 := by
  apply eval_commutes
  · rw [lie_add,bu]; grind [lie_skew]
  · rw [lie_add,bv]; exact neg_add_cancel _

-- @@ L1210-1213 verbatim
theorem eval_comm_c (p : L) : ⁅c,eval u (v+b) p⁆ = 0 := by
  apply eval_commutes
  · exact cu
  · rw [lie_add,cv]; grind [lie_skew]

-- @@ L1214-1217 verbatim
theorem eval_comm_sum (p : L) : ⁅a+b+c,eval u v p⁆ = 0 := by
  apply eval_commutes
  · rw [add_lie,add_lie,au,bu,cu]; abel
  · rw [add_lie,add_lie,av,bv,cv]; abel


-- @@ L1219-1228 verbatim
theorem fiber_identity (p : L) :
    ⁅fa+fb+fc,Fb p⁆ = ⁅fa,Fb p-Fa p⁆ + ⁅fc,Fb p-Fc p⁆ := by
  apply SemiDirectSum.inl_injective action
  simp only [LieHom.map_lie, map_add, map_sub, Fa_inl,Fb_inl,Fc_inl]
  change ⁅a+b+c,eval (u+a) (v+c) p - eval u v p⁆ =
    ⁅a,(eval (u+a) (v+c) p - eval u v p) - (eval (u+b) v p - eval u v p)⁆ +
    ⁅c,(eval (u+a) (v+c) p - eval u v p) - (eval u (v+b) p - eval u v p)⁆
  rw [lie_sub,eval_comm_sum]
  simp only [lie_sub,add_lie,eval_comm_a,eval_comm_b,eval_comm_c]
  abel


-- @@ L1230-1239 verbatim
theorem Fb_specialize {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1<n) :
    fiberSpec (Fb p) = -eval (-x-y) x p := by
  have H := congrArg specialize (Fb_inl p)
  rw [show specialize (SemiDirectSum.inl action (Fb p)) = fiberSpec (Fb p) from
    InnerSemiDirect.lift_inl _ _ _ _ _] at H
  simp only [map_sub,map_eval,map_add,specialize_u,specialize_a,specialize_v,specialize_c] at H
  have ha : -x-y+x = -y := by abel
  have hb : x+(-x-y) = -y := by abel
  rw [ha,hb,eval_vanish_of_commuting (-y) (-y) (lie_self _) hp hn,zero_sub] at H
  exact H


-- @@ L1241-1245 verbatim
theorem pentagon {p : L} (hp : p ∈ W) :
    eval a (b+c) p + eval (u+b) v p =
    eval b v p + eval (a+u) (c+v) p + eval a b p := by
  have h := congrArg representation hp.2.2
  simpa [map_eval,chord] using h


-- @@ L1247-1252 verbatim
theorem pentagon_reverse {p : L} (hp : p ∈ W) :
    eval c (b+a) p + eval (v+b) u p =
    eval b u p + eval (c+v) (a+u) p + eval c b p := by
  have h := congrArg (representation.comp (t4Rename (Equiv.swap 0 3))) hp.2.2
  simp only [LieHom.comp_apply,map_add,map_eval,t4Rename_t,representation_t] at h
  exact h


-- @@ L1254-1262 verbatim
theorem eval_bv_shift {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1<n) :
    eval b v p = eval b (-b-c) p := by
  have H := eval_central_shift b (-b-c) (v+b+c) (p := p) (n := n) ?_ ?_ hp hn
  · have he : -b-c+(v+b+c) = v := by abel
    simpa only [he] using H
  · simp only [lie_add,lie_self,bv]
    abel
  · simp only [sub_lie,neg_lie,lie_add,lie_self,bv,cv]
    grind [lie_skew]


-- @@ L1264-1272 verbatim
theorem eval_bu_shift {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1<n) :
    eval b u p = eval b (-b-a) p := by
  have H := eval_central_shift b (-b-a) (u+b+a) (p := p) (n := n) ?_ ?_ hp hn
  · have he : -b-a+(u+b+a) = u := by abel
    simpa only [he] using H
  · simp only [lie_add,lie_self,bu]
    grind [lie_skew]
  · simp only [sub_lie,neg_lie,lie_add,lie_self,bu,au]
    grind [lie_skew]


-- @@ L1274-1282 verbatim
theorem delta_a {n : ℕ} {p : L} (hp : p ∈ W) (hpn : p ∈ Ln n) (hn : 1<n) :
    Fb p-Fa p = eval fa (fb+fc) p - eval fa fb p - eval fb (-fb-fc) p := by
  apply SemiDirectSum.inl_injective action
  simp only [map_sub,map_eval,map_add,map_neg,Fb_inl,Fa_inl]
  change (eval (u+a) (v+c) p - eval u v p) - (eval (u+b) v p - eval u v p) =
    eval a (b+c) p - eval a b p - eval b (-b-c) p
  have H := pentagon hp
  rw [eval_bv_shift hpn hn,add_comm a u,add_comm c v] at H
  grind only


-- @@ L1284-1293 verbatim
theorem delta_c {n : ℕ} {p : L} (hp : p ∈ W) (hpn : p ∈ Ln n) (hn : 1<n) :
    Fb p-Fc p = -eval fc (fa+fb) p + eval fc fb p + eval fb (-fb-fa) p := by
  apply SemiDirectSum.inl_injective action
  simp only [map_sub,map_eval,map_add,map_neg,Fb_inl,Fc_inl]
  change (eval (u+a) (v+c) p - eval u v p) - (eval u (v+b) p - eval u v p) =
    -eval c (a+b) p + eval c b p + eval b (-b-a) p
  have H := pentagon_reverse hp
  rw [eval_bu_shift hpn hn,solution_swap hp (v+b) u,solution_swap hp (c+v) (a+u),
    add_comm b a,add_comm a u,add_comm c v] at H
  grind only


-- @@ L1295-1295 verbatim
end SpecialFiber


-- @@ L1297-1297 verbatim
namespace Differentiation

-- @@ L1298-1298 verbatim
open FreeDerivations


-- @@ L1300-1300 verbatim
variable {M N : Type} [LieRing M] [LieAlgebra ℝ M] [LieRing N] [LieAlgebra ℝ N]


-- @@ L1302-1302 verbatim
@[simp] theorem Jet.base_neg (p : Jet ℝ M) : (-p).base = -p.base := rfl

-- @@ L1303-1303 verbatim
@[simp] theorem Jet.velocity_neg (p : Jet ℝ M) : (-p).velocity = -p.velocity := rfl

-- @@ L1304-1304 verbatim
@[simp] theorem Jet.base_sub (p q : Jet ℝ M) : (p-q).base = p.base-q.base := rfl

-- @@ L1305-1305 verbatim
@[simp] theorem Jet.velocity_sub (p q : Jet ℝ M) : (p-q).velocity = p.velocity-q.velocity := rfl


-- @@ L1307-1308 verbatim
@[simp] theorem Jet.mk_add (a b da db : M) :
    (Jet.mk a da : Jet ℝ M) + Jet.mk b db = Jet.mk (a+b) (da+db) := rfl

-- @@ L1309-1310 verbatim
@[simp] theorem Jet.mk_neg (a da : M) :
    -(Jet.mk a da : Jet ℝ M) = Jet.mk (-a) (-da) := rfl

-- @@ L1311-1312 verbatim
@[simp] theorem Jet.mk_sub (a b da db : M) :
    (Jet.mk a da : Jet ℝ M) - Jet.mk b db = Jet.mk (a-b) (da-db) := rfl


-- @@ L1314-1315 verbatim
@[simp] theorem eval_base (a b : Jet ℝ M) (p : L) :
    (eval a b p).base = eval a.base b.base p := map_eval Jet.baseHom a b p


-- @@ L1317-1319 verbatim
def adPower (a : M) : ℕ → M → M
  | 0, t => t
  | n+1, t => ⁅a,adPower a n t⁆


-- @@ L1321-1322 verbatim
omit [LieAlgebra ℝ M] in
@[simp] theorem adPower_zero (a t : M) : adPower a 0 t = t := rfl

-- @@ L1323-1324 verbatim
omit [LieAlgebra ℝ M] in
@[simp] theorem adPower_succ (a t : M) (n : ℕ) : adPower a (n+1) t = ⁅a,adPower a n t⁆ := rfl

-- @@ L1325-1327 verbatim
@[simp] theorem adPower_smul (a t : M) (n : ℕ) (r : ℝ) :
    adPower a n (r • t) = r • adPower a n t := by
  induction n <;> simp_all

-- @@ L1328-1330 verbatim
omit [LieAlgebra ℝ M] in
@[simp] theorem adPower_zero_right (a : M) (n : ℕ) : adPower a n 0 = 0 := by
  induction n <;> simp_all

-- @@ L1331-1338 verbatim
omit [LieAlgebra ℝ M] in
@[simp] theorem adPower_self (a : M) {n : ℕ} (hn : 0<n) : adPower a n a = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    induction n with
    | zero => simp
    | succ n ih => simp_all

-- @@ L1339-1341 verbatim
omit [LieAlgebra ℝ M] in
@[simp] theorem adPower_zero_left (t : M) {n : ℕ} (hn : 0<n) : adPower (0:M) n t = 0 := by
  cases n <;> simp_all


-- @@ L1343-1344 verbatim
def slope (p : L) (a b da db : M) : M :=
  (eval (Jet.mk a da : Jet ℝ M) (Jet.mk b db) p).velocity


-- @@ L1346-1346 verbatim
@[simp] theorem slope_x (a b da db : M) : slope x a b da db = da := by simp [slope]

-- @@ L1347-1347 verbatim
@[simp] theorem slope_y (a b da db : M) : slope y a b da db = db := by simp [slope]

-- @@ L1348-1348 verbatim
@[simp] theorem slope_zero (a b da db : M) : slope 0 a b da db = 0 := by simp [slope]

-- @@ L1349-1350 verbatim
@[simp] theorem slope_add (p q : L) (a b da db : M) :
    slope (p+q) a b da db = slope p a b da db + slope q a b da db := by simp [slope]

-- @@ L1351-1352 verbatim
@[simp] theorem slope_smul (r : ℝ) (p : L) (a b da db : M) :
    slope (r • p) a b da db = r • slope p a b da db := by simp [slope]

-- @@ L1353-1355 verbatim
@[simp] theorem slope_lie (p q : L) (a b da db : M) :
    slope ⁅p,q⁆ a b da db = ⁅slope p a b da db,eval a b q⁆ +
      ⁅eval a b p,slope q a b da db⁆ := by simp [slope,LieHom.map_lie]


-- @@ L1357-1363 verbatim
@[simp] theorem slope_zero_direction (p : L) (a b : M) : slope p a b 0 0 = 0 := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [slope,eval]
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [hp]
  | hl p q hp hq => simp [hp,hq]


-- @@ L1365-1372 verbatim
theorem slope_add_direction (p : L) (a b da db ea eb : M) :
    slope p a b (da+ea) (db+eb) = slope p a b da db + slope p a b ea eb := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [slope,eval]
  | ha p q hp hq => simp [hp,hq]; abel
  | hs r p hp => simp [hp,smul_add]
  | hl p q hp hq => simp [hp,hq,add_lie,lie_add]; abel


-- @@ L1374-1381 verbatim
theorem slope_smul_direction (p : L) (a b da db : M) (r : ℝ) :
    slope p a b (r • da) (r • db) = r • slope p a b da db := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [slope,eval]
  | ha p q hp hq => simp [hp,hq,smul_add]
  | hs s p hp => simp [hp,smul_comm s r]
  | hl p q hp hq => simp [hp,hq,smul_add]


-- @@ L1383-1386 verbatim
theorem word_pos {n : ℕ} {p : L} (hp : WeightedWord (fun _:Bool => 1) n p) : 0<n := by
  induction hp with
  | generator => omega
  | bracket hp hq ihp ihq => omega


-- @@ L1388-1391 verbatim
def DiagonalData (n : ℕ) (p : L) (s k : ℝ) : Prop :=
  (n ≠ 1 → s = 0) ∧ ∀ (M : Type) [LieRing M] [LieAlgebra ℝ M] (a t : M),
    eval (Jet.mk a 0 : Jet ℝ M) (Jet.mk (-a) t) p =
      Jet.mk (s • a) (k • adPower a (n-1) t)


-- @@ L1393-1439 verbatim
theorem diagonal_bracket {n m : ℕ} {p q : L} {s k t l : ℝ}
    (hn : 0 < n) (hm : 0 < m) (hp : DiagonalData n p s k) (hq : DiagonalData m q t l) :
    ∃ r : ℝ, DiagonalData (n+m) ⁅p,q⁆ 0 r := by
  rcases hp with ⟨hs,hp⟩
  rcases hq with ⟨ht,hq⟩
  by_cases hn1 : n=1 <;> by_cases hm1 : m=1
  · subst n; subst m
    refine ⟨s*l-t*k, fun _ => rfl, ?_⟩
    intro M _ _ a b
    rw [LieHom.map_lie,hp,hq]
    ext
    · simp
    · change ⁅k • b,t • a⁆ + ⁅s • a,l • b⁆ = (s*l-t*k) • ⁅a,b⁆
      rw [smul_lie,lie_smul,←lie_skew b a,smul_neg,smul_lie,lie_smul]
      simp only [sub_smul,mul_smul]
      module
  · subst n
    have ht0 := ht hm1
    subst t
    refine ⟨s*l, fun _ => rfl, ?_⟩
    intro M _ _ a b
    rw [LieHom.map_lie,hp,hq]
    ext
    · simp
    · have he : 1+m-1 = (m-1)+1 := by omega
      simp [he,mul_smul,smul_comm l s]
  · subst m
    have hs0 := hs hn1
    subst s
    refine ⟨-(t*k), fun _ => rfl, ?_⟩
    intro M _ _ a b
    rw [LieHom.map_lie,hp,hq]
    ext
    · simp
    · have he : n+1-1 = (n-1)+1 := by omega
      simp only [Jet.velocity_lie,zero_smul,zero_lie,he,adPower_succ,
        smul_lie,lie_smul,neg_smul,mul_smul]
      rw [←lie_skew (adPower a (n-1) b) a,smul_neg,smul_neg]
      rw [smul_comm]
      simp
  · have hs0 := hs hn1
    have ht0 := ht hm1
    subst s; subst t
    refine ⟨0, fun _ => rfl, ?_⟩
    intro M _ _ a b
    rw [LieHom.map_lie,hp,hq]
    ext <;> simp


-- @@ L1441-1458 verbatim
theorem diagonal_word {n : ℕ} {p : L} (hp : WeightedWord (fun _:Bool => 1) n p) :
    ∃ s k : ℝ, DiagonalData n p s k := by
  induction hp with
  | generator i =>
    cases i
    · refine ⟨1,0, ?_⟩
      constructor
      · simp
      · intro M _ _ a b; simp [eval]
    · refine ⟨-1,1, ?_⟩
      constructor
      · simp
      · intro M _ _ a b; simp [eval]
  | bracket hp hq ihp ihq =>
    rcases ihp with ⟨s,k,hp'⟩
    rcases ihq with ⟨t,l,hq'⟩
    obtain ⟨r,hr⟩ := diagonal_bracket (word_pos hp) (word_pos hq) hp' hq'
    exact ⟨0,r,hr⟩


-- @@ L1460-1480 verbatim
theorem diagonal_homogeneous {n : ℕ} {p : L} (hp : p ∈ Ln n) :
    ∃ s k : ℝ, DiagonalData n p s k := by
  induction hp using Submodule.span_induction with
  | mem p hp => exact diagonal_word hp
  | zero =>
    refine ⟨0,0,fun _ => rfl,?_⟩
    intro M _ _ a b
    ext <;> simp
  | add p q _ _ hp hq =>
    rcases hp with ⟨s,k,hs,hp⟩
    rcases hq with ⟨t,l,ht,hq⟩
    refine ⟨s+t,k+l,fun hn => by simp [hs hn,ht hn],?_⟩
    intro M _ _ a b
    rw [map_add,hp,hq]
    ext <;> simp [add_smul]
  | smul r p _ hp =>
    rcases hp with ⟨s,k,hs,hp⟩
    refine ⟨r*s,r*k,fun hn => by simp [hs hn],?_⟩
    intro M _ _ a b
    rw [map_smul,hp]
    ext <;> simp [mul_smul]

 
-- @@ L1482-1484 verbatim
theorem slope_neg_direction (p : L) (a b da db : M) :
    slope p a b (-da) (-db) = -slope p a b da db := by
  simpa using slope_smul_direction p a b da db (-1)

 
-- @@ L1486-1493 verbatim
theorem slope_inner (p : L) (a b t : M) :
    slope p a b ⁅t,a⁆ ⁅t,b⁆ = ⁅t,eval a b p⁆ := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg i => cases i <;> simp [slope,eval]
  | ha p q hp hq => simp [hp,hq,lie_add]
  | hs r p hp => simp [hp]
  | hl p q hp hq => simp [hp,hq,LieHom.map_lie,lie_lie]

 
-- @@ L1495-1497 verbatim
theorem slope_swap {p : L} (hp : p ∈ W) (a b da db : M) :
    slope p a b da db = -slope p b a db da := by
  exact congrArg Jet.velocity (solution_swap hp (Jet.mk a da : Jet ℝ M) (Jet.mk b db))

 
-- @@ L1499-1502 verbatim
theorem diagonal_slope {n : ℕ} {p : L} {s k : ℝ}
    (hp : DiagonalData n p s k) (a t : M) :
    slope p a (-a) 0 t = k • adPower a (n-1) t :=
  congrArg Jet.velocity (hp.2 M a t)

 
-- @@ L1504-1513 verbatim
theorem diagonal_first {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1<n) (a t : M) :
    slope p a (-a) t 0 = slope p a (-a) 0 t := by
  have H := congrArg Jet.velocity (eval_vanish_of_commuting
    (Jet.mk a t : Jet ℝ M) (-Jet.mk a t) (by rw [lie_neg,lie_self,neg_zero]) hp hn)
  change slope p a (-a) t (-t) = 0 at H
  have hs := slope_add_direction p a (-a) t 0 0 (-t)
  have hneg := slope_neg_direction p a (-a) 0 t
  simp only [neg_zero] at hneg
  simp only [add_zero,zero_add,hneg,H] at hs
  exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg] using hs.symm)

 
-- @@ L1515-1515 verbatim
def G (p : L) : L := ⁅x,eval y x p⁆ + ⁅-x-y,eval y (-x-y) p⁆

 
-- @@ L1517-1519 verbatim
theorem eval_G (p : L) (a b : M) :
    eval a b (G p) = ⁅a,eval b a p⁆ + ⁅-a-b,eval b (-a-b) p⁆ := by
  simp only [G,map_add,LieHom.map_lie,map_eval,eval_x,eval_y,map_sub,map_neg]

 
-- @@ L1521-1535 verbatim
theorem slope_G (p : L) (a b t : M) :
    slope (G p) a b t 0 =
      ⁅t,eval b a p-eval b (-a-b) p⁆ +
      ⁅a,slope p b a 0 t⁆ - ⁅-a-b,slope p b (-a-b) 0 t⁆ := by
  have hh := congrArg Jet.velocity (eval_G p (Jet.mk a t : Jet ℝ M) (Jet.mk b 0))
  change slope (G p) a b t 0 = _ at hh
  simp only [Jet.mk_neg,Jet.mk_sub,sub_zero] at hh
  simp only [Jet.velocity_add,Jet.velocity_lie,eval_base] at hh
  have he : slope p b (-a-b) 0 (-t) = -slope p b (-a-b) 0 t := by
    simpa only [neg_zero] using slope_neg_direction p b (-a-b) 0 t
  change slope (G p) a b t 0 = ⁅t,eval b a p⁆ + ⁅a,slope p b a 0 t⁆ +
    (⁅-t,eval b (-a-b) p⁆ + ⁅-a-b,slope p b (-a-b) 0 (-t)⁆) at hh
  rw [he,neg_lie,lie_neg] at hh
  rw [lie_sub]
  grind only

 
-- @@ L1537-1538 verbatim
def fiberEval (a b c : M) : SpecialFiber.F →ₗ⁅ℝ⁆ M :=
  FreeLieAlgebra.lift ℝ (fun i => if i=0 then a else if i=1 then b else c)

-- @@ L1539-1540 verbatim
@[simp] theorem fiberEval_fa (a b c : M) : fiberEval a b c SpecialFiber.fa = a := by
  simp [fiberEval,SpecialFiber.fa]

-- @@ L1541-1542 verbatim
@[simp] theorem fiberEval_fb (a b c : M) : fiberEval a b c SpecialFiber.fb = b := by
  simp [fiberEval,SpecialFiber.fb]

-- @@ L1543-1544 verbatim
@[simp] theorem fiberEval_fc (a b c : M) : fiberEval a b c SpecialFiber.fc = c := by
  simp [fiberEval,SpecialFiber.fc]

 
-- @@ L1546-1552 verbatim
theorem fiberEval_spec (a b : M) (z : SpecialFiber.F) :
    fiberEval a b (-a-b) z = eval a b (SpecialFiber.fiberSpec z) := by
  have h : fiberEval a b (-a-b) = (eval a b).comp SpecialFiber.fiberSpec := by
    apply FreeLieAlgebra.hom_ext
    intro i
    fin_cases i <;> simp [fiberEval,SpecialFiber.fiberSpec]
  exact LieHom.congr_fun h z


-- @@ L1554-1560 verbatim
@[simp] theorem fiberEval_base (a b c : Jet ℝ M) (z : SpecialFiber.F) :
    (fiberEval a b c z).base = fiberEval a.base b.base c.base z := by
  have h : Jet.baseHom.comp (fiberEval a b c) = fiberEval a.base b.base c.base := by
    apply FreeLieAlgebra.hom_ext
    intro i
    fin_cases i <;> simp [fiberEval,Jet.baseHom] <;> rfl
  exact LieHom.congr_fun h z

 
-- @@ L1562-1565 verbatim
theorem fiberEval_Fb {n : ℕ} {p : L} (hp : p ∈ Ln n) (hn : 1<n) (a b : M) :
    fiberEval a b (-a-b) (SpecialFiber.Fb p) = - eval (-a-b) a p := by
  rw [fiberEval_spec,SpecialFiber.Fb_specialize hp hn]
  simp [map_eval]

 
-- @@ L1567-1611 verbatim
theorem transverse {n : ℕ} {p : L} {k : ℝ} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 1<n) (hdiag : DiagonalData n p 0 k) (a b t : M) :
    -⁅t,eval (-a-b) a p⁆ = k • (adPower a n t-adPower (-a-b) n t) +
       ⁅a,slope p b a 0 t⁆ - ⁅-a-b,slope p b (-a-b) 0 t⁆ := by
  have H := congrArg (fiberEval (Jet.mk a 0 : Jet ℝ M) (Jet.mk b 0)
    (Jet.mk (-a-b) t)) (SpecialFiber.fiber_identity p)
  rw [SpecialFiber.delta_a hp hpn hn,SpecialFiber.delta_c hp hpn hn] at H
  simp only [LieHom.map_lie,map_add,map_sub,map_neg,map_eval,
    fiberEval_fa,fiberEval_fb,fiberEval_fc] at H
  have hc : (Jet.mk a 0 : Jet ℝ M) + Jet.mk b 0 + Jet.mk (-a-b) t = Jet.mk 0 t := by
    ext <;> simp
  rw [hc] at H
  simp only [Jet.mk_add,Jet.mk_neg,Jet.mk_sub,zero_add,add_zero,neg_zero,sub_zero,zero_sub] at H
  have Hv := congrArg Jet.velocity H
  simp only [Jet.velocity_lie,Jet.velocity_sub,Jet.velocity_add,Jet.velocity_neg,
    Jet.base_add,Jet.base_sub,Jet.base_neg,eval_base,fiberEval_base] at Hv
  have hdiagNeg : -(-a-b) = a+b := by abel
  have hba : b+(-a-b) = -a := by abel
  have hab : -b-(-a-b) = a := by abel
  have hc0 : eval (-a-b) (a+b) p = 0 := by
    have h := eval_vanish_of_commuting (-a-b) (-(-a-b)) (by simp only [lie_neg,lie_self,neg_zero]) hpn hn
    simpa only [hdiagNeg] using h
  have hdelc : -eval (-a-b) (a+b) p + eval (-a-b) b p + eval b (-b-a) p = 0 := by
    rw [hc0,neg_zero,zero_add,solution_swap hp (-a-b) b]
    have he : -b-a = -a-b := by abel
    rw [he,neg_add_cancel]
  have hdp : slope p (-a-b) (a+b) t 0 = k • adPower (-a-b) (n-1) t := by
    rw [← hdiagNeg,diagonal_first hpn hn,diagonal_slope hdiag]
  have hdm : slope p b a 0 (-t) = -slope p b a 0 t := by
    simpa only [neg_zero] using slope_neg_direction p b a 0 t
  have hswap := slope_swap hp (-a-b) b t 0
  have hnp : n=(n-1)+1 := by omega
  change ⁅t,fiberEval a b (-a-b) (SpecialFiber.Fb p)⁆ + ⁅(0:M),_⁆ =
    (⁅(0:M),_⁆ + ⁅a,slope p a (b+(-a-b)) 0 t - slope p a b 0 0 -
      slope p b (-b-(-a-b)) 0 (-t)⁆) +
    (⁅t,-eval (-a-b) (a+b) p + eval (-a-b) b p + eval b (-b-a) p⁆ +
      ⁅-a-b,-slope p (-a-b) (a+b) t 0 + slope p (-a-b) b t 0 +
        slope p b (-b-a) 0 0⁆) at Hv
  rw [fiberEval_Fb hpn hn,hdelc,hba,hab,slope_zero_direction,slope_zero_direction,
    diagonal_slope hdiag,hdp,hdm,hswap] at Hv
  simp only [zero_lie,lie_zero,add_zero,zero_add,sub_zero,lie_neg,lie_sub,lie_add,lie_smul] at Hv
  rw [show ⁅a,adPower a (n-1) t⁆ = adPower a n t by rw [hnp]; rfl,
    show ⁅-a-b,adPower (-a-b) (n-1) t⁆ = adPower (-a-b) n t by rw [hnp]; rfl] at Hv
  rw [smul_sub]
  grind only

 
-- @@ L1613-1621 verbatim
theorem slope_G_formula {n : ℕ} {p : L} {k : ℝ} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 1<n) (hdiag : DiagonalData n p 0 k) (a b t : M) :
    slope (G p) a b t 0 = - k • (adPower a n t-adPower (-a-b) n t) := by
  have H := transverse hp hpn hn hdiag a b t
  have h3 := solution_three hp a b
  rw [solution_swap hp a b] at h3
  have he : eval b a p - eval b (-a-b) p = eval (-a-b) a p := by grind only
  rw [slope_G,he,neg_smul]
  grind only


-- @@ L1623-1630 verbatim
def swapJet : Jet ℝ (Jet ℝ M) →ₗ⁅ℝ⁆ Jet ℝ (Jet ℝ M) where
  toFun z := ⟨⟨z.base.base,z.velocity.base⟩,⟨z.base.velocity,z.velocity.velocity⟩⟩
  map_add' a b := by apply Jet.ext <;> apply Jet.ext <;> rfl
  map_smul' r a := by apply Jet.ext <;> apply Jet.ext <;> rfl
  map_lie' {a b} := by
    apply Jet.ext <;> apply Jet.ext
    all_goals simp only [Jet.base_lie,Jet.velocity_lie,Jet.base_add,Jet.velocity_add]
    all_goals first | rfl | abel


-- @@ L1632-1637 verbatim
theorem mixed_slope (p : L) (a b u v : M) :
    (slope p (Jet.mk a u : Jet ℝ M) (Jet.mk b 0) (Jet.mk v 0) 0).velocity =
    (slope p (Jet.mk a v : Jet ℝ M) (Jet.mk b 0) (Jet.mk u 0) 0).velocity := by
  have h := map_eval (swapJet : Jet ℝ (Jet ℝ M) →ₗ⁅ℝ⁆ Jet ℝ (Jet ℝ M))
    (Jet.mk (Jet.mk a u) (Jet.mk v 0)) (Jet.mk (Jet.mk b 0) 0) p
  exact congrArg (fun z => z.velocity.velocity) h


-- @@ L1639-1641 verbatim
@[simp] theorem adPower_base (a t : Jet ℝ M) (n : ℕ) :
    (adPower a n t).base = adPower a.base n t.base := by
  induction n <;> simp_all


-- @@ L1643-1651 verbatim
theorem adPower_radial (a t : M) (n : ℕ) :
    (adPower (Jet.mk a a : Jet ℝ M) n (Jet.mk t 0)).velocity =
      (n : ℝ) • adPower a n t := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [adPower_succ,Jet.velocity_lie,adPower_base,ih,lie_smul,
      Nat.cast_add,Nat.cast_one,add_smul,one_smul]
    abel


-- @@ L1653-1665 verbatim
theorem adPower_transverse_self (a t : M) {n : ℕ} (hn : 0<n) :
    (adPower (Jet.mk a t : Jet ℝ M) n (Jet.mk a 0)).velocity = -adPower a n t := by
  cases n with
  | zero => omega
  | succ n =>
    induction n with
    | zero => simp [lie_skew]
    | succ n ih =>
      rw [adPower_succ,Jet.velocity_lie,adPower_base]
      change ⁅t,adPower a (n+1) a⁆ +
        ⁅a,(adPower (Jet.mk a t : Jet ℝ M) (n+1) (Jet.mk a 0)).velocity⁆ = _
      rw [adPower_self a (n := n+1) (by omega),lie_zero,zero_add,ih (by omega),lie_neg]
      rfl


-- @@ L1667-1673 verbatim
theorem adPower_zero_base (a t : M) {n : ℕ} (hn : 1<n) :
    (adPower (Jet.mk 0 a : Jet ℝ M) n (Jet.mk t 0)).velocity = 0 := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [adPower_succ,Jet.velocity_lie,adPower_base,zero_lie,add_zero]
    rw [adPower_zero_left t (by omega),lie_zero]

 
-- @@ L1675-1698 verbatim
theorem mixed_scalar {n : ℕ} {p : L} {k : ℝ} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 2<n) (hdiag : DiagonalData n p 0 k) (a t : M) :
    (((n : ℝ)+1)*k) • adPower a n t = 0 := by
  have H1 := congrArg Jet.velocity (slope_G_formula hp hpn (by omega) hdiag
    (Jet.mk a a : Jet ℝ M) (Jet.mk (-a) 0) (Jet.mk t 0))
  have H2 := congrArg Jet.velocity (slope_G_formula hp hpn (by omega) hdiag
    (Jet.mk a t : Jet ℝ M) (Jet.mk (-a) 0) (Jet.mk a 0))
  have hc1 : -(Jet.mk a a : Jet ℝ M) - Jet.mk (-a) 0 = Jet.mk 0 (-a) := by
    ext <;> simp
  have hc2 : -(Jet.mk a t : Jet ℝ M) - Jet.mk (-a) 0 = Jet.mk 0 (-t) := by
    ext <;> simp
  rw [hc1] at H1
  rw [hc2] at H2
  simp only [Jet.velocity_smul,Jet.velocity_sub,adPower_radial,
    adPower_zero_base (-a) t (n := n) (by omega),sub_zero] at H1
  simp only [Jet.velocity_smul,Jet.velocity_sub,
    adPower_transverse_self a t (n := n) (by omega),adPower_zero_base (-t) a (n := n) (by omega),sub_zero] at H2
  have hm := mixed_slope (G p) a (-a) a t
  rw [H1,H2] at hm
  have hz : (-k) • ((n:ℝ) • adPower a n t) - (-k) • (-adPower a n t) = 0 := sub_eq_zero.mpr hm
  calc
    (((n : ℝ)+1)*k) • adPower a n t =
        -((-k) • ((n:ℝ) • adPower a n t) - (-k) • (-adPower a n t)) := by module
    _ = 0 := by rw [hz,neg_zero]

 
-- @@ L1700-1717 verbatim
theorem diagonal_scalar_zero {n : ℕ} {p : L} {k : ℝ} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 2<n) (hdiag : DiagonalData n p 0 k) : k=0 := by
  let := LieRing.ofAssociativeRing (A := Matrix (Fin 2) (Fin 2) ℝ)
  let a : Matrix (Fin 2) (Fin 2) ℝ := !![1,0;0,0]
  let t : Matrix (Fin 2) (Fin 2) ℝ := !![0,1;0,0]
  have hbr : ⁅a,t⁆ = t := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [a,t,Ring.lie_def,Matrix.mul_apply,Fin.sum_univ_two]
  have had (m : ℕ) : adPower a m t = t := by
    induction m with
    | zero => rfl
    | succ m ih => rw [adPower_succ,ih,hbr]
  have H := mixed_scalar hp hpn hn hdiag a t
  rw [had] at H
  have hc := congrArg (fun z => z 0 1) H
  change (((n : ℝ)+1)*k) * 1 = 0 at hc
  rw [mul_one] at hc
  exact (mul_eq_zero.mp hc).resolve_left (by positivity)

 
-- @@ L1719-1725 verbatim
theorem special_linearization {n : ℕ} {p : L} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 2<n) (a t : M) : slope p a (-a) 0 t = 0 := by
  obtain ⟨s,k,hd⟩ := diagonal_homogeneous hpn
  have hs := hd.1 (by omega)
  subst s
  have hk := diagonal_scalar_zero hp hpn hn hd
  rw [diagonal_slope hd,hk,zero_smul]

 
-- @@ L1727-1749 verbatim
theorem special_G_zero {n : ℕ} {p : L} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 2<n) : G p = 0 := by
  obtain ⟨s,k,hd⟩ := diagonal_homogeneous hpn
  have hs := hd.1 (by omega)
  subst s
  have hk := diagonal_scalar_zero hp hpn hn hd
  subst k
  have hder (t : L) : slope (G p) x y t 0 = 0 := by
    rw [slope_G_formula hp hpn (by omega) hd]
    simp
  have hcomm : ⁅y,G p⁆ = 0 := by
    have h := slope_inner (G p) x y y
    rw [lie_self,eval_self,LieHom.id_apply] at h
    rw [← h,hder]
  obtain ⟨r,hr⟩ := Submodule.mem_span_singleton.mp
    (AssociativeModel.centralizer_generator true hcomm)
  change r • y = G p at hr
  have he : eval (0 : L) y (G p) = 0 := by
    rw [eval_G]
    simp only [zero_lie,neg_zero,zero_sub,zero_add]
    rw [eval_vanish_of_commuting y (-y) (by simp) hpn (by omega),lie_zero]
  rw [← hr,map_smul,eval_y] at he
  exact hr.symm.trans he

 
-- @@ L1751-1753 verbatim
theorem special_identity {n : ℕ} {p : L} (hp : p ∈ W) (hpn : p ∈ Ln n)
    (hn : 2<n) (a b : M) : ⁅a,eval b a p⁆ + ⁅-a-b,eval b (-a-b) p⁆ = 0 := by
  rw [← eval_G,special_G_zero hp hpn hn,map_zero]


-- @@ L1755-1755 verbatim
end Differentiation

-- @@ L1756-1756 verbatim
end RealDeligneDrinfeld


-- @@ L1758-1758 verbatim
end


-- @@ L1760-1760 verbatim
end OAI
