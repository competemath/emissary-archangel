import Lean4AnalysisTao.Util
import Lean4AnalysisTao.C02_NaturalNumbers.S02_Addition

-- Definition 3.1.1

-- @@ L5-9 verbatim
axiom MySet.mem
    {α γ : Type}
    (S : γ)
    (x : α) :
    Prop

-- @@ L10-10 verbatim
notation:50 x:50 " ∈ " S:50 => MySet.mem S x

-- @@ L11-13 expanded
notation:50 x:50 " ∉ " S:50 =>
  ¬(x ∈ S)
      -- Axiom 3.1


-- @@ L14-18 verbatim
axiom MySet
    (α : Type) :
    Type

-- Axiom 3.2

-- @@ L19-24 expanded
axiom MySet.ext {α γ : Type} (A B : γ) :
    A = B ↔
      (∀ (x : α), x ∈ A ↔ x ∈ B)
        -- Axiom 3.3


-- @@ L25-27 verbatim
axiom MySet.empty
    {γ : Type} :
    γ

-- @@ L28-28 verbatim
notation:max "∅" => MySet.empty


-- @@ L30-33 expanded
axiom MySet.not_mem_empty {α γ : Type} (x : α) : x ∉ (∅ : γ)


-- @@ L35-40 expanded
def MySet.nonempty (S : MySet α) : Prop :=
  S ≠
    ∅
      -- Lemma 3.1.5


-- @@ L41-64 unexpanded
theorem MySet.single_choice
    (A : MySet α)
    (h : MySet.nonempty A) :
    ∃ (x : α), x ∈ A := by
  by_contra hxnA
  have hxnA'
      (x : α)
      (hx : x ∈ A) :
      False :=
    hxnA (Exists.intro x hx)
  have hxnemp
      (x : α) :
      ¬x ∈ (∅ : MySet α) :=
    MySet.not_mem_empty x
  have hiff
      (x : α) :
      x ∈ A ↔ x ∈ (∅ : MySet α) :=
    iff_of_false (hxnA' x) (hxnemp x)
  have hAemp :
      A = ∅ :=
    Iff.mpr (MySet.ext A ∅) hiff
  exact h hAemp

-- Axiom 3.4

-- @@ L65-68 verbatim
axiom MySet.singleton
    {α γ : Type}
    (a : α) :
    γ

-- @@ L69-69 verbatim
notation:max "⦃" a:max "⦄" => MySet.singleton a


-- @@ L71-75 expanded
axiom MySet.mem_singleton {α γ : Type} (a : α) (y : α) : y ∈ (MySet.singleton a : γ) ↔ y = a


-- @@ L77-80 verbatim
axiom MySet.pair
    {α γ : Type}
    (a b : α) :
    γ

-- @@ L81-81 verbatim
notation:max "⦃" a:max ", " b:max "⦄" => MySet.pair a b


-- @@ L83-89 expanded
axiom MySet.mem_pair {α γ : Type} (a b : α) (y : α) : y ∈ (MySet.pair a b : γ) ↔ y = a ∨ y = b


-- @@ L90-95 expanded
example (a : α) (S : MySet α) (h : ∀ (y : α), y ∈ S ↔ y = a) : S = MySet.singleton a := by sorry


-- @@ L97-100 expanded
example (a b : α) : (MySet.pair a b : MySet α) = MySet.pair b a := by sorry


-- @@ L102-107 expanded
example (a : α) : (MySet.pair a a : MySet α) = MySet.singleton a := by
  sorry
    -- Example 3.1.9


-- @@ L108-110 expanded
example : (∅ : γ) ≠ MySet.singleton (∅ : γ) := by sorry


-- @@ L112-114 expanded
example : (∅ : γ) ≠ MySet.singleton (MySet.singleton (∅ : γ) : γ) := by sorry


-- @@ L116-118 expanded
example : (∅ : γ) ≠ MySet.pair (∅ : γ) (MySet.singleton (∅ : γ) : γ) := by sorry


-- @@ L120-122 expanded
example : (MySet.singleton (∅ : γ) : γ) ≠ MySet.singleton (MySet.singleton (∅ : γ) : γ) := by sorry


-- @@ L124-126 expanded
example : (MySet.singleton (∅ : γ) : γ) ≠ MySet.pair (∅ : γ) (MySet.singleton (∅ : γ)) := by sorry


-- @@ L128-132 expanded
example :
    (MySet.singleton (MySet.singleton (∅ : γ) : γ) : γ) ≠
      MySet.pair (∅ : γ) (MySet.singleton (∅ : γ) : γ) :=
  by
  sorry
    -- Axiom 3.5


-- @@ L133-136 verbatim
axiom MySet.union
    {γ : Type}
    (A B : γ) :
    γ

-- @@ L137-137 verbatim
infixl:65 " ∪ " => MySet.union


-- @@ L139-145 expanded
axiom MySet.mem_union {α γ : Type} (A B : γ) (x : α) : x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B


-- @@ L146-150 expanded
example (A A' B : MySet α) (h : A = A') : A ∪ B = A' ∪ B := by sorry


-- @@ L152-158 expanded
example (A B B' : MySet α) (h : B = B') : A ∪ B = A ∪ B' := by
  sorry
    -- Lemma 3.1.12


-- @@ L159-162 expanded
theorem MySet.pair_eq_union_singleton (a b : α) :
    (MySet.pair a b : MySet α) = MySet.singleton a ∪ MySet.singleton b := by sorry


-- @@ L164-167 expanded
theorem MySet.union_comm (A B : MySet α) : A ∪ B = B ∪ A := by sorry


-- @@ L169-202 expanded
theorem MySet.union_assoc (A B C : MySet α) : (A ∪ B) ∪ C = A ∪ (B ∪ C) :=
  by
  have hiff (x : α) : x ∈ (A ∪ B) ∪ C ↔ x ∈ A ∪ (B ∪ C) :=
    by
    constructor
    · intro h
      rw [MySet.mem_union (A ∪ B) C x] at h
      rcases h with (h | h)
      · rw [MySet.mem_union A B x] at h
        rcases h with (h | h)
        · rw [MySet.mem_union A (B ∪ C) x]
          exact Or.inl h
        · rw [MySet.mem_union A (B ∪ C) x]
          rw [MySet.mem_union B C x]
          exact Or.inr (Or.inl h)
      · rw [MySet.mem_union A (B ∪ C) x]
        rw [MySet.mem_union B C x]
        exact Or.inr (Or.inr h)
    · intro h
      rw [MySet.mem_union A (B ∪ C) x] at h
      rcases h with (h | h)
      · rw [MySet.mem_union (A ∪ B) C x]
        rw [MySet.mem_union A B x]
        exact Or.inl (Or.inl h)
      · rw [MySet.mem_union B C x] at h
        rcases h with (h | h)
        · rw [MySet.mem_union (A ∪ B) C x]
          rw [MySet.mem_union A B x]
          exact Or.inl (Or.inr h)
        · rw [MySet.mem_union (A ∪ B) C x]
          exact Or.inr h
  exact Iff.mpr (MySet.ext ((A ∪ B) ∪ C) (A ∪ (B ∪ C))) hiff


-- @@ L204-207 expanded
theorem MySet.union_self (A : MySet α) : A ∪ A = A := by sorry


-- @@ L209-212 expanded
theorem MySet.union_empty (A : MySet α) : A ∪ ∅ = A := by sorry


-- @@ L214-219 expanded
theorem MySet.empty_union (A : MySet α) : ∅ ∪ A = A := by
  sorry
    -- Definition 3.1.14


-- @@ L220-224 expanded
def MySet.subset {α : Type} (A B : MySet α) : Prop :=
  ∀ (x : α), x ∈ A → x ∈ B


-- @@ L225-225 verbatim
infix:50 " ⊆ " => MySet.subset

-- @@ L226-228 expanded
notation A:50 " ⊊ " B:50 => A ⊆ B ∧ A ≠ B


-- @@ L229-235 expanded
example (A A' B : MySet α) (h : A = A') : A ⊆ B ↔ A' ⊆ B := by
  rw [h]
    -- Example 3.1.16


-- @@ L236-239 expanded
example (A : MySet α) : A ⊆ A := by sorry


-- @@ L241-246 expanded
example (A : MySet α) : ∅ ⊆ A := by
  sorry
    -- Proposition 3.1.17


-- @@ L247-262 unexpanded
theorem MySet.subset_trans
    (A B C : MySet α)
    (hAB : A ⊆ B)
    (hBC : B ⊆ C) :
    A ⊆ C := by
  rw [MySet.subset] at hAB
  rw [MySet.subset] at hBC
  rw [MySet.subset]
  intro x hxA
  have hxB :
      x ∈ B :=
    hAB x hxA
  have hxC :
      x ∈ C :=
    hBC x hxB
  exact hxC


-- @@ L264-269 unexpanded
theorem MySet.subset_antisymm
    (A B : MySet α)
    (hAB : A ⊆ B)
    (hBA : B ⊆ A) :
    A = B := by
  sorry


-- @@ L271-278 expanded
theorem MySet.proper_ss_of_proper_ss_of_proper_ss (A B C : MySet α) (hAB : A ⊆ B ∧ A ≠ B)
    (hBC : B ⊆ C ∧ B ≠ C) : A ⊆ C ∧ A ≠ C := by
  sorry
    -- Axiom 3.6


-- @@ L279-283 verbatim
axiom MySet.spec
    {α γ : Type}
    (A : γ)
    (P : α → Prop) :
    γ

-- @@ L284-284 verbatim
notation "⦃" S:max " | " P:max "⦄" => MySet.spec S P


-- @@ L286-291 expanded
axiom MySet.mem_spec {α : Type} (A : MySet α) (P : α → Prop) (y : α) :
    y ∈ MySet.spec A P ↔ y ∈ A ∧ P y


-- @@ L293-297 expanded
theorem MySet.spec_ss (A : MySet α) (P : α → Prop) : MySet.spec A P ⊆ A := by sorry


-- @@ L299-306 expanded
theorem MySet.spec_eq_spec_of_eq (A A' : MySet α) (P : α → Prop) (h : A = A') :
    MySet.spec A P = MySet.spec A' P := by
  sorry
    -- Example 3.1.21


-- @@ L307-307 verbatim
namespace Example_3_1_21


-- @@ L309-310 expanded
noncomputable def S : MySet MyNat :=
  MySet.singleton MyNat.one ∪ MySet.singleton MyNat.two ∪ MySet.singleton MyNat.three ∪
      MySet.singleton MyNat.four ∪
    MySet.singleton MyNat.five


-- @@ L312-315 expanded
example :
    (MySet.spec S fun (x : MyNat) => x < MyNat.four) =
      MySet.singleton MyNat.one ∪ MySet.singleton MyNat.two ∪ MySet.singleton MyNat.three :=
  by sorry


-- @@ L317-319 expanded
example : (MySet.spec S fun (x : MyNat) => x < MyNat.seven) = S := by sorry


-- @@ L321-323 expanded
example : (MySet.spec S fun (x : MyNat) => x < MyNat.one) = ∅ := by sorry


-- @@ L325-327 verbatim
end Example_3_1_21

-- Definition 3.1.22

-- @@ L328-332 expanded
noncomputable def MySet.inter {α : Type} (S₁ S₂ : MySet α) : MySet α :=
  MySet.spec S₁ fun x => (x : α) ∈ S₂


-- @@ L333-333 verbatim
infixl:70 " ∩ " => MySet.inter


-- @@ L335-340 expanded
theorem MySet.mem_inter (S₁ S₂ : MySet α) (x : α) : x ∈ S₁ ∩ S₂ ↔ x ∈ S₁ ∧ x ∈ S₂ :=
  by
  dsimp only [MySet.inter]
  rw [MySet.mem_spec S₁ (fun x => x ∈ S₂) x]


-- @@ L342-345 expanded
def MySet.disjoint (A B : MySet α) : Prop :=
  A ∩ B = ∅


-- @@ L347-351 expanded
example : MySet.disjoint (∅ : MySet α) ∅ := by
  sorry
    -- Definition 3.1.26


-- @@ L352-356 expanded
noncomputable def MySet.diff {α : Type} (A B : MySet α) : MySet α :=
  MySet.spec A fun x => (x : α) ∉ B


-- @@ L357-360 verbatim
infix:70 " \\ " => MySet.diff

-- Proposition 3.1.27
-- (a) `MySet.union_empty`: see Lemma 3.1.12

-- @@ L361-366 expanded
theorem MySet.inter_empty (A : MySet α) : A ∩ ∅ = ∅ := by
  sorry
    -- (b)


-- @@ L367-371 unexpanded
theorem MySet.union_superset
    (X A : MySet α)
    (hA : A ⊆ X) :
    A ∪ X = X := by
  sorry


-- @@ L373-379 unexpanded
theorem MySet.inter_superset
    (X A : MySet α)
    (hA : A ⊆ X) :
    A ∩ X = A := by
  sorry

-- (c) `MySet.union_self`: see Lemma 3.1.12

-- @@ L380-385 expanded
theorem MySet.inter_self (A : MySet α) : A ∩ A = A := by
  sorry
    -- (d) `MySet.union_comm`: see Lemma 3.1.12


-- @@ L386-391 expanded
theorem MySet.inter_comm (A B : MySet α) : A ∩ B = B ∩ A := by
  sorry
    -- (e) `MySet.union_assoc`: see Lemma 3.1.12


-- @@ L392-397 expanded
theorem MySet.inter_assoc (A B C : MySet α) : (A ∩ B) ∩ C = A ∩ (B ∩ C) := by
  sorry
    -- (f)


-- @@ L398-401 expanded
theorem MySet.inter_union_distrib (A B C : MySet α) : A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C) := by sorry


-- @@ L403-408 expanded
theorem MySet.union_inter_distrib (A B C : MySet α) : A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C) := by
  sorry
    -- (g)


-- @@ L409-413 unexpanded
theorem MySet.union_diff_superset
    (X A : MySet α)
    (hA : A ⊆ X) :
    A ∪ (X \ A) = X := by
  sorry


-- @@ L415-418 expanded
theorem MySet.inter_diff (X A : MySet α) : A ∩ (X \ A) = ∅ := by sorry


-- @@ L420-423 expanded
theorem MySet.diff_union (X A B : MySet α) : X \ (A ∪ B) = (X \ A) ∩ (X \ B) := by sorry


-- @@ L425-430 expanded
theorem MySet.diff_inter (X A B : MySet α) : X \ (A ∩ B) = (X \ A) ∪ (X \ B) := by
  sorry
    -- Axiom 3.7


-- @@ L431-437 expanded
axiom MySet.replace {α β : Type} (A : MySet α) (P : α → β → Prop)
    (hP : ∀ (x : α), x ∈ A → (∃ (y : β), (P x y ∧ (∀ (z : β), P x z → z = y)))) : MySet β


-- @@ L438-439 verbatim
notation
  "⦃" A:max " ← " hP:max "⦄" => MySet.replace A _ hP


-- @@ L441-450 expanded
axiom MySet.mem_replace {α β : Type} (A : MySet α) (P : α → β → Prop)
    (hP : ∀ (x : α), x ∈ A → (∃ (y : β), (P x y ∧ (∀ (z : β), P x z → z = y)))) (z : β) :
    z ∈ MySet.replace A _ hP ↔
      (∃ (x : α), x ∈ A ∧ P x z)
        -- Example 3.1.30


-- @@ L451-451 verbatim
namespace Example_3_1_30


-- @@ L453-454 expanded
noncomputable def A : MySet MyNat :=
  MySet.singleton MyNat.three ∪ MySet.singleton MyNat.five ∪ MySet.singleton MyNat.nine


-- @@ L456-460 expanded
def P (x : MyNat) (y : MyNat) : Prop :=
  y = x + MyNat.one


-- @@ L462-471 unexpanded
theorem hP
    (x : MyNat)
    (hxA : x ∈ A) :
    ∃ (y : MyNat), (P x y ∧ (∀ (z : MyNat), P x z → z = y)) := by
  use (x + 𝟙)
  constructor
  · rw [P]
  · intro z hz
    rw [P] at hz
    rw [hz]


-- @@ L473-475 expanded
example :
    MySet.replace A _ hP =
      MySet.singleton MyNat.four ∪ MySet.singleton MyNat.six ∪ MySet.singleton MyNat.ten :=
  by sorry


-- @@ L477-479 verbatim
end Example_3_1_30

-- Example 3.1.31

-- @@ L480-480 verbatim
namespace Example_3_1_31


-- @@ L482-483 expanded
noncomputable def A : MySet MyNat :=
  MySet.singleton MyNat.three ∪ MySet.singleton MyNat.five ∪ MySet.singleton MyNat.nine


-- @@ L485-489 expanded
def P (x : MyNat) (y : MyNat) : Prop :=
  y = MyNat.one


-- @@ L491-500 unexpanded
theorem hP
    (x : MyNat)
    (hxA : x ∈ A) :
    ∃ (y : MyNat), (P x y ∧ (∀ (z : MyNat), P x z → z = y)) := by
  use 𝟙
  constructor
  · rw [P]
  · intro z hz
    rw [P] at hz
    rw [hz]


-- @@ L502-522 expanded
example : MySet.replace A _ hP = MySet.singleton MyNat.one :=
  by
  rw [MySet.ext (α := MyNat) (γ := MySet MyNat) (MySet.replace A _ hP) (MySet.singleton MyNat.one)]
  intro y
  rw [MySet.mem_replace A P hP y]
  rw [MySet.mem_singleton (γ := MySet MyNat) MyNat.one y]
  constructor
  · intro h
    rcases h with ⟨x, hxA, hPxy⟩
    rw [P] at hPxy
    exact hPxy
  · intro h
    refine ⟨MyNat.nine, ?_⟩
    constructor
    · rw [A]
      rw [MySet.mem_union (MySet.singleton MyNat.three ∪ MySet.singleton MyNat.five)
          (MySet.singleton MyNat.nine) MyNat.nine]
      rw [MySet.mem_singleton (γ := MySet MyNat) MyNat.nine MyNat.nine]
      exact Or.inr rfl
    · rw [P]
      exact h


-- @@ L524-526 verbatim
end Example_3_1_31

-- Axiom 3.8

-- @@ L527-527 verbatim
axiom MySet.Nat.set : MySet MyNat


-- @@ L529-531 expanded
axiom MySet.Nat.is_nat (n : MyNat) : n ∈ MySet.Nat.set


-- @@ L533-535 verbatim
section Exercises

-- Exercise 3.1.1

-- @@ L536-542 expanded
example (a b c d : α) (h : (MySet.pair a b : MySet MyNat) = MySet.pair c d) :
    (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  sorry
    -- Exercise 3.1.5


-- @@ L543-549 expanded
example (A B : MySet α) : ((A ⊆ B) ↔ (A ∪ B = B)) ∧ ((A ⊆ B) ↔ (A ∩ B = A)) := by
  sorry
    -- Exercise 3.1.7


-- @@ L550-553 expanded
example (A B : MySet α) : A ∩ B ⊆ A := by sorry


-- @@ L555-558 expanded
example (A B : MySet α) : A ∩ B ⊆ B := by sorry


-- @@ L560-563 expanded
example (A B C : MySet α) : C ⊆ A ∧ C ⊆ B ↔ C ⊆ A ∩ B := by sorry


-- @@ L565-568 expanded
example (A B : MySet α) : A ⊆ A ∪ B := by sorry


-- @@ L570-573 expanded
example (A B : MySet α) : B ⊆ A ∪ B := by sorry


-- @@ L575-580 expanded
example (A B C : MySet α) : A ⊆ C ∧ B ⊆ C ↔ A ∪ B ⊆ C := by
  sorry
    -- Exercise 3.1.8


-- @@ L581-584 expanded
example (A B : MySet α) : A ∩ (A ∪ B) = A := by sorry


-- @@ L586-591 expanded
example (A B : MySet α) : A ∪ (A ∩ B) = A := by
  sorry
    -- Exercise 3.1.9


-- @@ L592-597 expanded
example (A B X : MySet α) (hu : A ∪ B = X) (hi : A ∩ B = ∅) : A = X \ B := by sorry


-- @@ L599-606 expanded
example (A B X : MySet α) (hu : A ∪ B = X) (hi : A ∩ B = ∅) : B = X \ A := by
  sorry
    -- Exercise 3.1.10


-- @@ L607-610 expanded
example (A B : MySet α) : MySet.disjoint (A \ B) (A ∩ B) := by sorry


-- @@ L612-615 expanded
example (A B : MySet α) : MySet.disjoint (A \ B) (B \ A) := by sorry


-- @@ L617-620 expanded
example (A B : MySet α) : MySet.disjoint (A ∩ B) (B \ A) := by sorry


-- @@ L622-627 expanded
example (A B : MySet α) : (A \ B) ∪ (A ∩ B) ∪ (B \ A) = A ∪ B := by
  sorry
    -- Exercise 3.1.11


-- @@ L628-642 expanded
example {α : Type}
    (hrep :
      ∀ (A : MySet α) {β : Type} (P : α → β → Prop),
        (∀ (x : α), x ∈ A → (∃ (y : β), P x y ∧ (∀ (z : β), P x z → y = z))) →
          (∃ (S : MySet β), ∀ (y : β), y ∈ S ↔ ∃ (x : α), x ∈ A ∧ P x y))
    (A : MySet α) (P : α → Prop) : ∃ (S : MySet α), ∀ (x : α), x ∈ S ↔ x ∈ A ∧ P x := by
  sorry
    -- Exercise 3.1.12
    -- (a)


-- @@ L643-648 unexpanded
example
    (A B A' B' : MySet α)
    (hA : A' ⊆ A)
    (hB : B' ⊆ B) :
    A' ∪ B' ⊆ A ∪ B := by
  sorry


-- @@ L650-657 unexpanded
example
    (A B A' B' : MySet α)
    (hA : A' ⊆ A)
    (hB : B' ⊆ B) :
    A' ∩ B' ⊆ A ∩ B := by
  sorry

-- (b)

-- @@ L658-663 expanded
example : ∃ (A B A' B' : MySet MyNat), A' ⊆ A ∧ B' ⊆ B ∧ ¬(A' \ B' ⊆ A \ B) := by
  sorry
    -- Exercise 3.1.13


-- @@ L664-668 expanded
example (A : MySet α) (hA : MySet.nonempty A) :
    ¬(∃ (B : MySet α), MySet.nonempty B ∧ B ⊆ A ∧ B ≠ A) ↔ (∃ (x : α), A = MySet.singleton x) := by
  sorry


-- @@ L670-670 verbatim
end Exercises
