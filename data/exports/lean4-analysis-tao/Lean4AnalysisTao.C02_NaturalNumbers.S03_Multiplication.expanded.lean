import Lean4AnalysisTao.C02_NaturalNumbers.S02_Addition

-- Definition 2.3.1

-- @@ L4-4 verbatim
axiom MyNat.mul : MyNat → MyNat → MyNat

-- @@ L5-5 verbatim
infixl:70 " * " => MyNat.mul


-- @@ L7-9 expanded
axiom MyNat.zero_mul (m : MyNat) : MyNat.zero * m = MyNat.zero


-- @@ L11-15 expanded
axiom MyNat.succ_mul (n m : MyNat) : (MyNat.succ n) * m = n * m + m


-- @@ L16-19 expanded
theorem MyNat.mul_zero (n : MyNat) : n * MyNat.zero = MyNat.zero := by sorry


-- @@ L21-24 expanded
theorem MyNat.mul_succ (n m : MyNat) : n * MyNat.succ m = n * m + n := by sorry


-- @@ L26-31 expanded
theorem MyNat.mul_comm (n m : MyNat) : n * m = m * n := by
  sorry
    -- Lemma 2.3.3


-- @@ L32-37 expanded
theorem MyNat.mul_pos (n m : MyNat) (hn : MyNat.is_positive n) (hm : MyNat.is_positive m) :
    (MyNat.is_positive (n * m)) := by sorry


-- @@ L39-44 expanded
theorem MyNat.mul_eq_zero (n m : MyNat) : n * m = MyNat.zero ↔ n = MyNat.zero ∨ m = MyNat.zero := by
  sorry
    -- Proposition 2.3.4


-- @@ L45-66 expanded
theorem MyNat.mul_distrib (a b c : MyNat) : a * (b + c) = a * b + a * c :=
  by
  have hall (c : MyNat) : a * (b + c) = a * b + a * c :=
    by
    have hbase : a * (b + MyNat.zero) = a * b + a * MyNat.zero :=
      by
      rw [MyNat.add_zero b]
      rw [MyNat.mul_zero a]
      rw [MyNat.add_zero (a * b)]
    have hind (c : MyNat) (hc : a * (b + c) = a * b + a * c) :
      a * (b + MyNat.succ c) = a * b + a * (MyNat.succ c) :=
      by
      rw [MyNat.add_succ b c]
      rw [MyNat.mul_succ a (b + c)]
      rw [MyNat.mul_succ a c]
      rw [← MyNat.add_assoc (a * b) (a * c) a]
      rw [← hc]
    exact MyNat.induction (fun c => a * (b + c) = a * b + a * c) hbase hind c
  exact hall c


-- @@ L68-76 expanded
theorem MyNat.mul_distrib' (a b c : MyNat) : (b + c) * a = b * a + c * a :=
  by
  rw [MyNat.mul_comm (b + c) a]
  rw [MyNat.mul_distrib a b c]
  rw [MyNat.mul_comm a b]
  rw [MyNat.mul_comm a c]
    -- Proposition 2.3.5


-- @@ L77-82 expanded
theorem MyNat.mul_assoc (a b c : MyNat) : (a * b) * c = a * (b * c) := by
  sorry
    -- Proposition 2.3.6


-- @@ L83-98 unexpanded
theorem MyNat.mul_lt_mul_of_pos_right
    (a b c : MyNat)
    (hab : a < b)
    (hc : MyNat.is_positive c) :
    a * c < b * c := by
  rcases Iff.mp (MyNat.lt_iff_eq_add a b) hab with ⟨d, hd, h⟩
  have h' : b * c = a * c + d * c := by
    rw [h]
    rw [MyNat.mul_distrib' c a d]
  have hdcpos :
      (MyNat.is_positive (d * c)) :=
    MyNat.mul_pos d c hd hc
  exact Iff.mpr (MyNat.lt_iff_eq_add (a * c) (b * c))
    (Exists.intro (d * c) (And.intro hdcpos h'))

-- Corollary 2.3.7

-- @@ L99-121 expanded
theorem MyNat.mul_cancel_of_pos (a b : MyNat) (c : MyNat) (hc : c ≠ MyNat.zero)
    (h : a * c = b * c) : a = b :=
  by
  rcases MyNat.order_trichotomy a b with (h | h | h)
  · rcases h with ⟨hlt, hne, hngt⟩
    first
    | intro hne_ab
    | refine MyClassical.byContradiction _ (fun hne_ab => ?_)
    have hltmul : a * c < b * c := MyNat.mul_lt_mul_of_pos_right a b c hlt hc
    exact And.right hltmul (Eq.symm h)
  · rcases h with ⟨hngt, heq, hnlt⟩
    exact heq
  · rcases h with ⟨hnlt, hne, hgt⟩
    first
    | intro hne_ab
    | refine MyClassical.byContradiction _ (fun hne_ab => ?_)
    have hltmul : b * c < a * c := MyNat.mul_lt_mul_of_pos_right b a c hgt hc
    exact And.right hltmul h


-- @@ L122-129 expanded
theorem MyNat.euclid_division (n : MyNat) (q : MyNat) (hqpos : MyNat.is_positive q) :
    ∃ (m r : MyNat), MyNat.zero ≤ r ∧ r < q ∧ n = m * q + r := by
  sorry
    -- Definition 2.3.11


-- @@ L130-130 verbatim
axiom MyNat.exp : MyNat → MyNat → MyNat

-- @@ L131-131 verbatim
infixr:80 " ^ " => MyNat.exp


-- @@ L133-135 expanded
axiom MyNat.exp_zero (m : MyNat) : m ^ MyNat.zero = MyNat.one


-- @@ L137-141 expanded
axiom MyNat.exp_succ (m n : MyNat) : m ^ (MyNat.succ n) = m ^ n * m


-- @@ L142-151 expanded
theorem MyNat.exp_one (x : MyNat) : x ^ MyNat.one = x :=
  by
  dsimp only [MyNat.one]
  rw [MyNat.exp_succ x MyNat.zero]
  rw [MyNat.exp_zero x]
  dsimp only [MyNat.one]
  rw [MyNat.succ_mul MyNat.zero x]
  rw [MyNat.zero_mul x]
  rw [MyNat.zero_add x]


-- @@ L153-158 expanded
theorem MyNat.exp_two (x : MyNat) : x ^ MyNat.two = x * x :=
  by
  dsimp only [MyNat.two]
  rw [MyNat.exp_succ x MyNat.one]
  rw [MyNat.exp_one x]


-- @@ L160-162 verbatim
section Exercises

-- Exercise 2.3.4

-- @@ L163-166 expanded
theorem Exercise_2_3_4 (a b : MyNat) :
    (a + b) ^ MyNat.two = a ^ MyNat.two + MyNat.two * a * b + b ^ MyNat.two := by sorry


-- @@ L168-168 verbatim
end Exercises
