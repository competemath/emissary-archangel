import Lean4AnalysisTao.Util
import Lean4AnalysisTao.C02_NaturalNumbers.S01_PeanoAxioms

-- Definition 2.2.1

-- @@ L5-5 verbatim
axiom MyNat.add : MyNat → MyNat → MyNat

-- @@ L6-6 verbatim
infixl:65 " + " => MyNat.add


-- @@ L8-10 expanded
axiom MyNat.zero_add (m : MyNat) : MyNat.zero + m = m


-- @@ L12-16 expanded
axiom MyNat.succ_add (n m : MyNat) : MyNat.succ n + m = MyNat.succ (n + m)


-- @@ L17-31 expanded
theorem MyNat.add_zero (n : MyNat) : n + MyNat.zero = n :=
  by
  have hbase : MyNat.zero + MyNat.zero = MyNat.zero := by rw [MyNat.zero_add MyNat.zero]
  have hind (n : MyNat) (hn : n + MyNat.zero = n) : MyNat.succ n + MyNat.zero = MyNat.succ n :=
    by
    rw [MyNat.succ_add n MyNat.zero]
    rw [hn]
  exact MyNat.induction (fun n => n + MyNat.zero = n) hbase hind n


-- @@ L32-50 expanded
theorem MyNat.add_succ (n m : MyNat) : n + MyNat.succ m = MyNat.succ (n + m) :=
  by
  have hbase (m : MyNat) : MyNat.zero + MyNat.succ m = MyNat.succ (MyNat.zero + m) :=
    by
    rw [MyNat.zero_add m]
    rw [MyNat.zero_add (MyNat.succ m)]
  have hind (n : MyNat) (hn : ∀ (m : MyNat), n + MyNat.succ m = MyNat.succ (n + m)) (m : MyNat) :
    MyNat.succ n + MyNat.succ m = MyNat.succ (MyNat.succ n + m) :=
    by
    rw [MyNat.succ_add n m]
    rw [MyNat.succ_add n (MyNat.succ m)]
    rw [hn m]
  exact
    MyNat.induction (fun n => ∀ (m : MyNat), n + MyNat.succ m = MyNat.succ (n + m)) hbase hind n m


-- @@ L51-69 expanded
theorem MyNat.add_comm (n m : MyNat) : n + m = m + n :=
  by
  have hbase (m : MyNat) : MyNat.zero + m = m + MyNat.zero :=
    by
    rw [MyNat.zero_add m]
    rw [MyNat.add_zero m]
  have hind (n : MyNat) (hn : ∀ (m : MyNat), n + m = m + n) (m : MyNat) :
    MyNat.succ n + m = m + MyNat.succ n :=
    by
    rw [MyNat.succ_add n m]
    rw [MyNat.add_succ m n]
    rw [hn m]
  exact MyNat.induction (fun n => ∀ (m : MyNat), n + m = m + n) hbase hind n m


-- @@ L70-75 expanded
theorem MyNat.add_assoc (a b c : MyNat) : (a + b) + c = a + (b + c) := by
  sorry
    -- Proposition 2.2.6


-- @@ L76-98 expanded
theorem MyNat.add_left_cancel (a b c : MyNat) (h : a + b = a + c) : b = c :=
  by
  have hbase (b c : MyNat) (h : MyNat.zero + b = MyNat.zero + c) : b = c :=
    by
    rw [MyNat.zero_add b] at h
    rw [MyNat.zero_add c] at h
    exact h
  have hind (a : MyNat) (ha : ∀ (b c : MyNat), a + b = a + c → b = c) (b c : MyNat)
    (h : MyNat.succ a + b = MyNat.succ a + c) : b = c :=
    by
    rw [MyNat.succ_add a b] at h
    rw [MyNat.succ_add a c] at h
    exact ha b c (MyNat.succ_inj (a + b) (a + c) h)
  exact MyNat.induction (fun a => ∀ (b c : MyNat), a + b = a + c → b = c) hbase hind a b c h


-- @@ L99-104 expanded
def MyNat.is_positive (n : MyNat) : Prop :=
  n ≠ MyNat.zero


-- @@ L105-124 expanded
theorem MyNat.pos_add (a : MyNat) (ha : MyNat.is_positive a) (b : MyNat) :
    (MyNat.is_positive (a + b)) :=
  by
  have hall (b : MyNat) : (MyNat.is_positive (a + b)) :=
    by
    have hbase : (MyNat.is_positive (a + MyNat.zero)) :=
      by
      rw [MyNat.add_zero a]
      exact ha
    have hind (b : MyNat) (hb : (MyNat.is_positive (a + b))) :
      (MyNat.is_positive (a + MyNat.succ b)) :=
      by
      rw [MyNat.add_succ a b]
      exact MyNat.succ_ne_zero (a + b)
    exact MyNat.induction (fun b => (MyNat.is_positive (a + b))) hbase hind b
  exact hall b


-- @@ L126-134 expanded
theorem MyNat.pos_add' (a : MyNat) (ha : MyNat.is_positive a) (b : MyNat) :
    (MyNat.is_positive (b + a)) := by
  rw [MyNat.add_comm b a]
  exact MyNat.pos_add a ha b


-- @@ L135-147 expanded
theorem MyNat.zero_zero_of_add_zero (a b : MyNat) (hab : a + b = MyNat.zero) :
    a = MyNat.zero ∧ b = MyNat.zero :=
  by
  first
  | intro hne
  | refine MyClassical.byContradiction _ (fun hne => ?_)
  rw [not_and_or (a = MyNat.zero) (b = MyNat.zero)] at hne
  rcases hne with (ha | hb)
  · have hpos : (MyNat.is_positive (a + b)) := MyNat.pos_add a ha b
    exact hpos hab
  · have hpos : (MyNat.is_positive (a + b)) := MyNat.pos_add' b hb a
    exact hpos hab


-- @@ L148-154 expanded
theorem MyNat.unique_pred_of_pos (a : MyNat) (ha : MyNat.is_positive a) :
    ∃ (b : MyNat), MyNat.succ b = a ∧ (∀ (c : MyNat), MyNat.succ c = a → b = c) := by
  sorry
    -- Definition 2.2.11


-- @@ L155-158 expanded
def MyNat.ge (n m : MyNat) : Prop :=
  ∃ (a : MyNat), n = m + a


-- @@ L159-159 verbatim
infixl:50 " ≥ " => MyNat.ge


-- @@ L161-164 expanded
def MyNat.le (n m : MyNat) : Prop :=
  m ≥ n


-- @@ L165-165 verbatim
infixl:50 " ≤ " => MyNat.le


-- @@ L167-170 expanded
def MyNat.gt (n m : MyNat) : Prop :=
  n ≥ m ∧ n ≠ m


-- @@ L171-171 verbatim
infixl:50 " > " => MyNat.gt


-- @@ L173-176 expanded
def MyNat.lt (n m : MyNat) : Prop :=
  m > n


-- @@ L177-180 verbatim
infixl:50 " < " => MyNat.lt

-- Proposition 2.2.12
-- (a)

-- @@ L181-186 expanded
theorem MyNat.ge_refl (a : MyNat) : a ≥ a := by
  sorry
    -- (b)


-- @@ L187-194 unexpanded
theorem MyNat.ge_trans
    (a b c : MyNat)
    (hab : a ≥ b)
    (hbc : b ≥ c) :
    a ≥ c := by
  sorry

-- (c)

-- @@ L195-202 unexpanded
theorem MyNat.ge_antisymm
    (a b : MyNat)
    (hab : a ≥ b)
    (hba : b ≥ a) :
    a = b := by
  sorry

-- (d)

-- @@ L203-208 expanded
theorem MyNat.ge_iff_add_ge (a b c : MyNat) : a ≥ b ↔ a + c ≥ b + c := by
  sorry
    -- (e)


-- @@ L209-214 expanded
theorem MyNat.lt_iff_succ_le (a b : MyNat) : a < b ↔ MyNat.succ a ≤ b := by
  sorry
    -- (f)


-- @@ L215-220 expanded
theorem MyNat.lt_iff_eq_add (a b : MyNat) :
    a < b ↔ ∃ (d : MyNat), MyNat.is_positive d ∧ b = a + d := by
  sorry
    -- Proposition 2.2.13


-- @@ L221-310 expanded
theorem MyNat.order_trichotomy (a b : MyNat) :
    ((a < b) ∧ ¬(a = b) ∧ ¬(a > b)) ∨
      (¬(a < b) ∧ (a = b) ∧ ¬(a > b)) ∨ (¬(a < b) ∧ ¬(a = b) ∧ (a > b)) :=
  by
  have h12 : ¬((a < b) ∧ (a = b)) := by
    intro ⟨h1, h2⟩
    dsimp only [MyNat.lt] at h1
    dsimp only [MyNat.gt] at h1
    exact Ne.symm (And.right h1) h2
  have h23 : ¬((a = b) ∧ (a > b)) := by
    intro ⟨h2, h3⟩
    dsimp only [MyNat.gt] at h3
    exact And.right h3 h2
  have h13 : ¬((a < b) ∧ (a > b)) := by
    intro ⟨h1, h3⟩
    dsimp only [MyNat.lt] at h1
    dsimp only [MyNat.gt] at h1
    dsimp only [MyNat.gt] at h3
    have heq : a = b := MyNat.ge_antisymm a b (And.left h3) (And.left h1)
    exact And.right h3 heq
  have h123 (a b : MyNat) : (a < b) ∨ (a = b) ∨ (a > b) :=
    by
    have hbase (b : MyNat) : (MyNat.zero < b) ∨ (MyNat.zero = b) ∨ (MyNat.zero > b) :=
      by
      have hle (b : MyNat) : MyNat.zero ≤ b := by sorry
      have heq_or_lt : MyNat.zero = b ∨ MyNat.zero < b :=
        by
        by_cases heq : MyNat.zero = b
        · exact Or.inl heq
        · rw [← Ne.eq_def] at heq
          exact Or.inr (And.intro (hle b) (Ne.symm heq))
      rcases heq_or_lt with (h1 | h2)
      · exact Or.inr (Or.inl h1)
      · exact Or.inl h2
    have hind (a : MyNat) (ha : ∀ (b : MyNat), (a < b) ∨ (a = b) ∨ (a > b)) (b : MyNat) :
      (MyNat.succ a < b) ∨ (MyNat.succ a = b) ∨ (MyNat.succ a > b) :=
      by
      rcases ha b with (h1 | h2 | h3)
      · have hle : MyNat.succ a ≤ b := Iff.mp (MyNat.lt_iff_succ_le a b) h1
        by_cases heq : MyNat.succ a = b
        · exact Or.inr (Or.inl heq)
        · rw [← Ne.eq_def] at heq
          exact Or.inl (And.intro hle (Ne.symm heq))
      · have hgt : MyNat.succ a > b := by sorry
        exact Or.inr (Or.inr hgt)
      · have hgt : MyNat.succ a > b := by sorry
        exact Or.inr (Or.inr hgt)
    exact MyNat.induction (fun a => ∀ (b : MyNat), (a < b) ∨ (a = b) ∨ (a > b)) hbase hind a b
  rcases h123 a b with (h1 | h2 | h3)
  · have h2 : ¬(a = b) := by
      rw [@not_and (a < b) (a = b)] at h12
      exact h12 h1
    have h3 : ¬(a > b) := by
      rw [@not_and (a < b) (a > b)] at h13
      exact h13 h1
    exact Or.inl (And.intro h1 (And.intro h2 h3))
  · have h1 : ¬(a < b) := by
      rw [@not_and' (a < b) (a = b)] at h12
      exact h12 h2
    have h3 : ¬(a > b) := by
      rw [@not_and (a = b) (a > b)] at h23
      exact h23 h2
    exact Or.inr (Or.inl (And.intro h1 (And.intro h2 h3)))
  · have h1 : ¬(a < b) := by
      rw [@not_and' (a < b) (a > b)] at h13
      exact h13 h3
    have h2 : ¬(a = b) := by
      rw [@not_and' (a = b) (a > b)] at h23
      exact h23 h3
    exact
      Or.inr
        (Or.inr (And.intro h1 (And.intro h2 h3)))
          -- Proposition 2.2.14


-- @@ L311-317 expanded
theorem MyNat.strong_induction (m₀ : MyNat) (P : MyNat → Prop)
    (hind : ∀ (m : MyNat), m ≥ m₀ → ((∀ (m' : MyNat), m₀ ≤ m' → m' < m → P m') → P m)) :
    ∀ (m : MyNat), m ≥ m₀ → P m := by sorry


-- @@ L319-321 verbatim
section Exercises

-- Exercise 2.2.6

-- @@ L322-330 expanded
example (n : MyNat) (P : MyNat → Prop) (hbase : P n)
    (hind : ∀ (m : MyNat), P (MyNat.succ m) → P m) : ∀ (m : MyNat), m ≤ n → P m := by
  sorry
    -- Exercise 2.2.7


-- @@ L331-337 expanded
example (n : MyNat) (P : MyNat → Prop) (hind : ∀ (m : MyNat), P m → P (MyNat.succ m)) (hn : P n) :
    ∀ (m : MyNat), m ≥ n → P m := by sorry


-- @@ L339-339 verbatim
end Exercises
