import Mathlib.Tactic


-- @@ L3-9 verbatim
/-!
# Analysis I, Appendix B.1: The decimal representation of natural numbers

Am implementation of the decimal representation of Mathlib's natural numbers {lean}`ℕ`.

This is separate from the way decimal numerals are already represenated in Mathlib via the {name}`OfNat` typeclass.
-/


-- @@ L11-13 verbatim
namespace AppendixB

/- The ten digits, together with the base 10 -/

-- @@ L14-14 verbatim
example : 0 = Nat.zero := rfl

-- @@ L15-15 verbatim
example : 1 = (0:Nat).succ := rfl

-- @@ L16-16 verbatim
example : 2 = (1:Nat).succ := rfl

-- @@ L17-17 verbatim
example : 3 = (2:Nat).succ := rfl

-- @@ L18-18 verbatim
example : 4 = (3:Nat).succ := rfl

-- @@ L19-19 verbatim
example : 5 = (4:Nat).succ := rfl

-- @@ L20-20 verbatim
example : 6 = (5:Nat).succ := rfl

-- @@ L21-21 verbatim
example : 7 = (6:Nat).succ := rfl

-- @@ L22-22 verbatim
example : 8 = (7:Nat).succ := rfl

-- @@ L23-23 verbatim
example : 9 = (8:Nat).succ := rfl

-- @@ L24-24 verbatim
example : 10 = (9:Nat).succ := rfl


-- @@ L26-27 verbatim
/-- Definition B.1.1 -/
def Digit := Fin 10


-- @@ L29-29 verbatim
instance Digit.instZero : Zero Digit := ⟨0, by decide⟩

-- @@ L30-30 verbatim
instance Digit.instOne : One Digit := ⟨1, by decide⟩

-- @@ L31-31 verbatim
instance Digit.instTwo : OfNat Digit 2 := ⟨2, by decide⟩

-- @@ L32-32 verbatim
instance Digit.instThree : OfNat Digit 3 := ⟨3, by decide⟩

-- @@ L33-33 verbatim
instance Digit.instFour : OfNat Digit 4 := ⟨4, by decide⟩

-- @@ L34-34 verbatim
instance Digit.instFive : OfNat Digit 5 := ⟨5, by decide⟩

-- @@ L35-35 verbatim
instance Digit.instSix : OfNat Digit 6 := ⟨6, by decide⟩

-- @@ L36-36 verbatim
instance Digit.instSeven : OfNat Digit 7 := ⟨7, by decide⟩

-- @@ L37-37 verbatim
instance Digit.instEight : OfNat Digit 8 := ⟨8, by decide⟩

-- @@ L38-38 verbatim
instance Digit.instNine : OfNat Digit 9 := ⟨9, by decide⟩


-- @@ L40-40 verbatim
instance Digit.instFintype : Fintype Digit := Fin.fintype 10

-- @@ L41-41 verbatim
instance Digit.instDecidableEq : DecidableEq Digit := instDecidableEqFin 10


-- @@ L43-43 verbatim
instance Digit.instInhabited : Inhabited Digit := ⟨ 0 ⟩


-- @@ L45-46 verbatim
@[coe]
abbrev Digit.toNat (d:Digit) : ℕ := d.val


-- @@ L48-49 verbatim
instance Digit.instCoeNat : Coe Digit Nat where
  coe := toNat


-- @@ L51-51 verbatim
theorem Digit.lt (d:Digit) : (d:ℕ) < 10 := d.isLt


-- @@ L53-53 verbatim
abbrev Digit.mk {n:ℕ} (h: n < 10) : Digit := ⟨n, h⟩


-- @@ L55-56 verbatim
@[simp]
theorem Digit.toNat_mk {n:ℕ} (h: n < 10) : (Digit.mk h:ℕ) = n := rfl


-- @@ L58-59 verbatim
@[simp]
theorem Digit.inj (d d':Digit) : d = d' ↔ (d:ℕ) = d' := by grind


-- @@ L61-62 verbatim
theorem Digit.mk_eq_iff (d:Digit) {n:ℕ} (h: n < 10) : d = mk h ↔ (d:ℕ) = n := by
  convert Digit.inj d (mk h)

-- @@ L63-63 verbatim
#check (0:Digit)

-- @@ L64-64 verbatim
#check (1:Digit)

-- @@ L65-65 verbatim
#check (2:Digit)

-- @@ L66-66 verbatim
#check (3:Digit)

-- @@ L67-67 verbatim
#check (4:Digit)

-- @@ L68-68 verbatim
#check (5:Digit)

-- @@ L69-69 verbatim
#check (6:Digit)

-- @@ L70-70 verbatim
#check (7:Digit)

-- @@ L71-71 verbatim
#check (8:Digit)

-- @@ L72-72 verbatim
#check (9:Digit)


-- @@ L74-75 verbatim
theorem Digit.eq (n: Digit) : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by
  fin_cases n <;> simp +decide


-- @@ L77-81 verbatim
/-- Definition B.1.2 -/
structure PosintDecimal where
  digits : List Digit
  nonempty : digits ≠ []
  nonzero : digits.head nonempty ≠ 0


-- @@ L83-86 verbatim
theorem PosintDecimal.congr' {p q:PosintDecimal} (h: p.digits = q.digits) : p = q := by
  obtain ⟨ pd, _, _ ⟩ := p
  obtain ⟨ qd, _, _ ⟩ := q
  congr


-- @@ L88-91 verbatim
theorem PosintDecimal.congr {p q:PosintDecimal} (h: p.digits.length = q.digits.length)
  (h': ∀ (n:ℕ) (h₁ : n < p.digits.length) (h₂: n < q.digits.length), p.digits.get ⟨ n, h₁ ⟩ = q.digits.get ⟨ n, h₂ ⟩) : p = q := by
  apply congr'
  simp_all [List.ext_get_iff]


-- @@ L93-93 verbatim
abbrev PosintDecimal.head (p:PosintDecimal): Digit := p.digits.head p.nonempty


-- @@ L95-95 verbatim
theorem PosintDecimal.head_ne_zero (p:PosintDecimal) : p.head ≠ 0 := p.nonzero


-- @@ L97-100 verbatim
theorem PosintDecimal.head_ne_zero' (p:PosintDecimal) : (p.head:ℕ) ≠ 0 := by
  by_contra!
  apply head_ne_zero p
  simp_all [Digit.toNat, Digit.inj]; rfl


-- @@ L102-103 verbatim
theorem PosintDecimal.length_pos (p:PosintDecimal) : 0 < p.digits.length := by
  simp [List.length_pos_iff, p.nonempty]


-- @@ L105-112 verbatim
/-- A slightly clunky way of creating decimals. -/
def PosintDecimal.mk' (head:Digit) (tail:List Digit) (h: head ≠ 0) : PosintDecimal := {
  digits := head :: tail
  nonempty := by aesop
  nonzero := h
}

-- the positive integer decimal 314

-- @@ L113-115 verbatim
#check PosintDecimal.mk' 3 [1, 4] (by decide)

-- the positive integer decimal 3

-- @@ L116-118 verbatim
#check PosintDecimal.mk' 3 [] (by decide)

-- the positive integer decimal 10

-- @@ L119-119 verbatim
#check PosintDecimal.mk' 1 [0] (by decide)


-- @@ L121-124 verbatim
/-- We are indexing digits in a decimal from left to right rather than from right to left, thus necessitating a reversal here. -/
@[coe]
def PosintDecimal.toNat (p:PosintDecimal) : Nat :=
  ∑ i:Fin p.digits.length, p.digits[p.digits.length - 1 - ↑i].toNat * 10 ^ (i:ℕ)


-- @@ L126-127 verbatim
instance PosintDecimal.instCoeNat : Coe PosintDecimal Nat where
  coe := toNat


-- @@ L129-129 verbatim
example : (PosintDecimal.mk' 3 [1, 4] (by decide):ℕ) = 314 := by decide


-- @@ L131-134 verbatim
/-- Remark B.1.3 -/
@[simp]
theorem PosintDecimal.ten_eq_ten : (mk' 1 [0] (by decide):ℕ) = 10 := by
  decide


-- @@ L136-137 verbatim
theorem PosintDecimal.digit_eq {d:Digit} (h: d ≠ 0) : (mk' d [] h:ℕ) = d := by
  simp [toNat, mk']


-- @@ L139-151 verbatim
theorem PosintDecimal.pos (p:PosintDecimal) : 0 < (p:ℕ) := by
  simp [toNat]
  calc
    _ < (p.head:ℕ) * 10 ^ (p.digits.length - 1) := by
      have := p.head_ne_zero'
      positivity
    _ ≤ _ := by
      have := p.length_pos
      set a : Fin p.digits.length := ⟨ p.digits.length - 1, by omega ⟩
      convert Finset.single_le_sum _ (Finset.mem_univ a)
      . simp [a, head, List.head_eq_getElem]
      . infer_instance
      grind


-- @@ L153-155 verbatim
/-- An operation implicit in the proof of Theorem B.1.4: -/
abbrev PosintDecimal.append (p:PosintDecimal) (d:Digit) : PosintDecimal :=
  mk' p.head (p.digits.tail ++ [d]) p.head_ne_zero


-- @@ L157-173 verbatim
/-- {name}`toNat` equals Horner (left-fold) evaluation of the digit list. -/
theorem PosintDecimal.toNat_eq_foldl (q : PosintDecimal) :
    q.toNat = q.digits.foldl (fun acc (d : Digit) => acc * 10 + d.toNat) 0 := by
  suffices h : ∀ (L : List Digit) (acc : ℕ),
      L.foldl (fun a (d : Digit) => a * 10 + d.toNat) acc =
      acc * 10 ^ L.length + ∑ i : Fin L.length, (L[L.length - 1 - ↑i]).toNat * 10 ^ (↑i : ℕ)
    from by simp [toNat, h q.digits 0]
  intro L; induction L with
  | nil => simp
  | cons a t ih =>
    intro acc; simp only [List.foldl_cons, List.length_cons]
    -- Decompose the Fin (t.length+1) sum: last term is a*10^|t|, rest matches the Fin t.length sum
    have : ∑ x : Fin (t.length + 1), ((a :: t)[t.length - ↑x] : ℕ) * 10 ^ (↑x : ℕ) =
        (∑ x : Fin t.length, (t[t.length - 1 - ↑x] : ℕ) * 10 ^ (↑x : ℕ)) + a * 10 ^ t.length := by
      refine (Fin.sum_univ_castSucc _).trans ?_
      congr 1 <;> grind
    grind


-- @@ L175-181 verbatim
@[simp]
theorem PosintDecimal.append_toNat (p:PosintDecimal) (d:Digit) :
  (p.append d:ℕ) = d.toNat + 10 * p.toNat  := by
  rw [toNat_eq_foldl, toNat_eq_foldl]; simp only [append, mk']
  rw [show p.head :: (p.digits.tail ++ [d]) = p.digits ++ [d] from by
    simp [head, ← List.cons_append, List.cons_head_tail]]
  rw [List.foldl_append]; simp [List.foldl]; ring


-- @@ L183-191 verbatim
theorem PosintDecimal.eq_append {p:PosintDecimal} (h: 2 ≤ p.digits.length) : ∃ (q:PosintDecimal) (d:Digit), p = q.append d := by
  use mk' p.head (p.digits.tail.dropLast) p.head_ne_zero
  set a := p.digits.getLast p.nonempty; use a
  apply congr'
  simp [mk']
  rw [←p.digits.cons_head_tail p.nonempty]
  congr 1
  convert (List.dropLast_append_getLast _).symm using 2; grind
  simp [←List.length_pos_iff]; omega


-- @@ L193-250 verbatim
/-- Theorem B.1.4 (Uniqueness and existence of decimal representations) -/
theorem PosintDecimal.exists_unique (n:ℕ) : n > 0 → ∃! p:PosintDecimal, (p:ℕ) = n := by
  -- this proof is written to follow the structure of the original text.
  apply n.case_strong_induction_on
  . simp
  -- note: the variable `m` in the text is referred to as `m+1` here.
  clear n; intro m hind _
  obtain hm | hm := lt_or_ge m 9
  . apply ExistsUnique.intro (mk' (.mk (show m+1 < 10 by omega)) [] (by simp [Digit.mk]))
    . simp [mk', Digit.mk, toNat, Digit.toNat]
    intro d hd
    obtain hdl | hdl := lt_or_ge d.digits.length 2
    . replace hdl : d.digits.length = 1 := by linarith [d.length_pos]
      have _subsing : Subsingleton (Fin d.digits.length) := by simp [Fin.subsingleton_iff_le_one, hdl]
      let zero : Fin d.digits.length := ⟨ 0, by omega ⟩
      simp [toNat, hdl, Fintype.sum_subsingleton _ zero, zero, Digit.toNat] at hd
      apply congr
      . simp [hdl, mk']
      intro i hi₁ hi₂
      replace hi₁ : i = 0 := by omega
      simp [hi₁, mk', Digit.mk, hd]
    have : d.toNat ≥ 10 := calc
      _ ≥ (d.head:ℕ) * 10^(d.digits.length-1) := by
        set a : Fin d.digits.length := ⟨ d.digits.length - 1, by omega ⟩
        convert Finset.single_le_sum _ (Finset.mem_univ a)
        . simp [a, head, List.head_eq_getElem]
        . infer_instance
        intros; positivity
      _ ≥ 1 * 10^(2-1) := by
        gcongr
        . have := d.head_ne_zero'; omega
        norm_num
      _ = 10 := by norm_num
    linarith
  have := (m+1).mod_add_div 10
  set s := (m+1)/10
  set r := (m+1) % 10
  have hr : r < 10 := by grind
  specialize hind s _ _ <;> try linarith
  choose b hb huniq using hind; simp at huniq
  apply ExistsUnique.intro (b.append (.mk hr))
  . simp [←this, hb]
  intro a ha
  obtain hal | hal := lt_or_ge a.digits.length 2
  . replace hal : a.digits.length = 1 := by linarith [a.length_pos]
    have _subsing : Subsingleton (Fin a.digits.length) := by simp [Fin.subsingleton_iff_le_one, hal]
    let zero : Fin a.digits.length := ⟨ 0, by linarith ⟩
    simp [toNat, hal, Fintype.sum_subsingleton _ zero, zero, Digit.toNat] at ha
    observe : a.digits[0].val < 10
    linarith
  obtain ⟨ b', b'₀, rfl ⟩ := eq_append hal
  simp [←this] at ha
  observe : (b'₀:ℕ) < 10
  replace : (s:ℤ) = (b':ℕ) := by omega
  have hb'₀r: (b'₀:ℕ) = (r:ℤ) := by omega
  simp at *
  rw [←b'₀.mk_eq_iff hr] at hb'₀r
  rw [huniq b' this.symm, hb'₀r]


-- @@ L252-256 verbatim
@[simp]
theorem PosintDecimal.coe_inj (p q:PosintDecimal) : (p:ℕ) = (q:ℕ) ↔ p = q := by
  constructor <;> intro h
  . exact (exists_unique _ q.pos).unique h rfl
  rw [h]



-- @@ L259-262 verbatim
inductive IntDecimal where
  | zero : IntDecimal
  | pos : PosintDecimal → IntDecimal
  | neg : PosintDecimal → IntDecimal


-- @@ L264-267 verbatim
def IntDecimal.toInt : IntDecimal → Int
  | zero => 0
  | pos p => p.toNat
  | neg p => -p.toNat


-- @@ L269-270 verbatim
instance IntDecimal.instCoeInt : Coe IntDecimal Int where
  coe := toInt


-- @@ L272-272 verbatim
example : (IntDecimal.neg (PosintDecimal.mk' 3 [1, 4] (by decide)):ℤ) = -314 := by decide


-- @@ L274-301 verbatim
theorem IntDecimal.Int_bij : Function.Bijective IntDecimal.toInt := by
  constructor
  . intro p q hpq
    cases p with
    | zero => cases q with
      | zero => rfl
      | pos q => simp [toInt] at hpq; linarith [q.pos]
      | neg q => simp [toInt] at hpq; linarith [q.pos]
    | pos p => cases q with
      | zero => simp [toInt] at hpq; linarith [p.pos]
      | pos q => simpa [toInt] using hpq
      | neg q => simp [toInt] at hpq; linarith [q.pos]
    | neg p => cases q with
      | zero => simp [toInt] at hpq; linarith [p.pos]
      | pos q => simp [toInt] at hpq; linarith [q.pos]
      | neg q => simpa [toInt] using hpq
  intro n
  obtain h | rfl | h := lt_trichotomy n 0
  . generalize e: -n = m
    lift m to Nat using (by omega)
    choose p hp _ using PosintDecimal.exists_unique _ (show 0 < m by omega)
    use neg p
    simp [toInt, hp, ←e]
  . use zero; simp [toInt]
  lift n to Nat using (by omega); simp at h
  choose p hp _ using PosintDecimal.exists_unique _ h
  use pos p
  simp [toInt, hp]


-- @@ L303-304 verbatim
abbrev PosintDecimal.digit (p:PosintDecimal) (i:ℕ) : Digit :=
  if h: i < p.digits.length then p.digits[p.digits.length - i - 1] else 0


-- @@ L306-306 verbatim
abbrev PosintDecimal.carry (p q:PosintDecimal) : ℕ → ℕ := Nat.rec 0 (fun i ε ↦ if ((p.digit i:ℕ) + (q.digit i:ℕ) + ε) < 10 then 0 else 1)


-- @@ L308-308 verbatim
theorem PosintDecimal.carry_zero (p q:PosintDecimal) : p.carry q 0 = 0 := by convert Nat.rec_zero _ _


-- @@ L310-311 verbatim
theorem PosintDecimal.carry_succ (p q:PosintDecimal) (i:ℕ) : p.carry q (i+1) = if ((p.digit i:ℕ) + (q.digit i:ℕ) + p.carry q i < 10) then 0 else 1 :=
  Nat.rec_add_one 0 (fun i ε ↦ if ((p.digit i:ℕ) + (q.digit i:ℕ) + ε) < 10 then 0 else 1) i


-- @@ L313-317 verbatim
abbrev PosintDecimal.sum_digit (p q:PosintDecimal) (i:ℕ) : ℕ :=
  if (p.digit i + q.digit i + (p.carry q) i < 10) then
    p.digit i + q.digit i + (p.carry q) i
  else
    p.digit i + q.digit i + (p.carry q) i - 10


-- @@ L319-321 verbatim
/-- Exercise B.1.1 -/
theorem PosintDecimal.sum_digit_lt (p q:PosintDecimal) (i:ℕ) :
  p.sum_digit q i < 10 := by sorry


-- @@ L323-324 verbatim
/-- Define this number such that it satisfies the two following theorems. -/
def PosintDecimal.sum_digit_top (p q:PosintDecimal) : ℕ := by sorry


-- @@ L326-327 verbatim
theorem PosintDecimal.leading_nonzero (p q:PosintDecimal) :
    p.sum_digit q (p.sum_digit_top q) ≠ 0 := sorry


-- @@ L329-330 verbatim
theorem PosintDecimal.out_of_range_eq_zero (p q:PosintDecimal) :
    ∀ i > ↑(p.sum_digit_top q), p.sum_digit q i = 0 := sorry


-- @@ L332-335 verbatim
def PosintDecimal.longAddition (p q : PosintDecimal) : PosintDecimal where
  digits := sorry
  nonempty := sorry
  nonzero := sorry


-- @@ L337-338 verbatim
theorem PosintDecimal.sum_eq (p q:PosintDecimal) (i:ℕ) :
    (((p.longAddition q).digit i):ℕ) = p.sum_digit q i ∧ (p.longAddition q:ℕ) = p + q := by sorry
