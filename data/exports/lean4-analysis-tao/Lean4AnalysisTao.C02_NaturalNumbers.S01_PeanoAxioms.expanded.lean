import Lean4AnalysisTao.Util


-- @@ L3-5 verbatim
axiom MyNat : Type

-- Axiom 2.1

-- @@ L6-6 verbatim
axiom MyNat.zero : MyNat

-- @@ L7-9 verbatim
notation "𝟘" => MyNat.zero

-- Axiom 2.2

-- @@ L10-10 verbatim
axiom MyNat.succ : MyNat → MyNat

-- @@ L11-13 verbatim
postfix:max "++" => MyNat.succ

-- Definition 2.1.3

-- @@ L14-14 expanded
noncomputable def MyNat.one : MyNat :=
  MyNat.succ MyNat.zero


-- @@ L15-15 verbatim
notation "𝟙" => MyNat.one


-- @@ L17-17 expanded
noncomputable def MyNat.two : MyNat :=
  MyNat.succ MyNat.one


-- @@ L18-18 verbatim
notation "𝟚" => MyNat.two


-- @@ L20-20 expanded
noncomputable def MyNat.three : MyNat :=
  MyNat.succ MyNat.two


-- @@ L21-21 verbatim
notation "𝟛" => MyNat.three


-- @@ L23-23 expanded
noncomputable def MyNat.four : MyNat :=
  MyNat.succ MyNat.three


-- @@ L24-24 verbatim
notation "𝟜" => MyNat.four


-- @@ L26-26 expanded
noncomputable def MyNat.five : MyNat :=
  MyNat.succ MyNat.four


-- @@ L27-27 verbatim
notation "𝟝" => MyNat.five


-- @@ L29-29 expanded
noncomputable def MyNat.six : MyNat :=
  MyNat.succ MyNat.five


-- @@ L30-30 verbatim
notation "𝟞" => MyNat.six


-- @@ L32-32 expanded
noncomputable def MyNat.seven : MyNat :=
  MyNat.succ MyNat.six


-- @@ L33-33 verbatim
notation "𝟟" => MyNat.seven


-- @@ L35-35 expanded
noncomputable def MyNat.eight : MyNat :=
  MyNat.succ MyNat.seven


-- @@ L36-36 verbatim
notation "𝟠" => MyNat.eight


-- @@ L38-38 expanded
noncomputable def MyNat.nine : MyNat :=
  MyNat.succ MyNat.eight


-- @@ L39-39 verbatim
notation "𝟡" => MyNat.nine


-- @@ L41-41 expanded
noncomputable def MyNat.ten : MyNat :=
  MyNat.succ MyNat.nine


-- @@ L42-46 verbatim
notation "𝟙𝟘" => MyNat.ten

-- Example 2.1.4

-- Example 2.1.5

-- @@ L47-47 verbatim
namespace Example_2_1_5


-- @@ L49-49 verbatim
axiom Wrap : Type


-- @@ L51-51 verbatim
axiom Wrap.zero : Wrap

-- @@ L52-52 verbatim
axiom Wrap.one : Wrap

-- @@ L53-53 verbatim
axiom Wrap.two : Wrap

-- @@ L54-54 verbatim
axiom Wrap.three : Wrap


-- @@ L56-56 verbatim
axiom Wrap.succ : Wrap → Wrap


-- @@ L58-58 verbatim
axiom Wrap.succ_zero : Wrap.succ Wrap.zero = Wrap.one

-- @@ L59-59 verbatim
axiom Wrap.succ_one : Wrap.succ Wrap.one = Wrap.two

-- @@ L60-60 verbatim
axiom Wrap.succ_two : Wrap.succ Wrap.two = Wrap.three

-- @@ L61-61 verbatim
axiom Wrap.succ_three : Wrap.succ Wrap.three = Wrap.zero


-- @@ L63-63 verbatim
example : Wrap.succ Wrap.three = Wrap.zero := Wrap.succ_three


-- @@ L65-67 verbatim
end Example_2_1_5

-- Axiom 2.3

-- @@ L68-72 expanded
axiom MyNat.succ_ne_zero (n : MyNat) : MyNat.succ n ≠ MyNat.zero


-- @@ L73-77 expanded
theorem Proposition_2_1_6 : MyNat.four ≠ MyNat.zero :=
  MyNat.succ_ne_zero MyNat.three


-- @@ L78-78 verbatim
namespace Example_2_1_7


-- @@ L80-80 verbatim
axiom Ceil : Type


-- @@ L82-82 verbatim
axiom Ceil.zero : Ceil

-- @@ L83-83 verbatim
axiom Ceil.one : Ceil

-- @@ L84-84 verbatim
axiom Ceil.two : Ceil

-- @@ L85-85 verbatim
axiom Ceil.three : Ceil

-- @@ L86-86 verbatim
axiom Ceil.four : Ceil


-- @@ L88-88 verbatim
axiom Ceil.succ : Ceil → Ceil


-- @@ L90-90 verbatim
axiom Ceil.succ_zero : Ceil.succ Ceil.zero = Ceil.one

-- @@ L91-91 verbatim
axiom Ceil.succ_one : Ceil.succ Ceil.one = Ceil.two

-- @@ L92-92 verbatim
axiom Ceil.succ_two : Ceil.succ Ceil.two = Ceil.three

-- @@ L93-93 verbatim
axiom Ceil.succ_three : Ceil.succ Ceil.three = Ceil.four

-- @@ L94-94 verbatim
axiom Ceil.succ_four : Ceil.succ Ceil.four = Ceil.four


-- @@ L96-98 verbatim
end Example_2_1_7

-- Axiom 2.4

-- @@ L99-102 expanded
axiom MyNat.succ_inj (n m : MyNat) (h : MyNat.succ n = MyNat.succ m) : n = m


-- @@ L104-111 expanded
theorem MyNat.succ_inj' (n m : MyNat) (h : n ≠ m) : MyNat.succ n ≠ MyNat.succ m :=
  by
  first
  | intro hcontra
  | refine MyClassical.byContradiction _ (fun hcontra => ?_)
  exact
    h
      (MyNat.succ_inj n m hcontra)
        -- Proposition 2.1.8


-- @@ L112-122 expanded
example : MyNat.six ≠ MyNat.two :=
  by
  first
  | intro h62
  | refine MyClassical.byContradiction _ (fun h62 => ?_)
  dsimp only [MyNat.six] at h62
  dsimp only [MyNat.two] at h62
  have h51 : MyNat.five = MyNat.one := MyNat.succ_inj MyNat.five MyNat.one h62
  dsimp only [MyNat.five] at h51
  dsimp only [MyNat.one] at h51
  have h40 : MyNat.four = MyNat.zero := MyNat.succ_inj MyNat.four MyNat.zero h51
  exact Proposition_2_1_6 h40


-- @@ L123-129 expanded
axiom MyNat.induction (P : MyNat → Prop) (hbase : P MyNat.zero)
    (hind : ∀ (n : MyNat), P n → P (MyNat.succ n)) : ∀ (n : MyNat), P n


-- @@ L130-210 expanded
theorem Proposition_2_1_16 (f : MyNat → MyNat → MyNat) (c : MyNat) :
    ∃ (a : MyNat → MyNat),
      a MyNat.zero = c ∧
        (∀ (n : MyNat), a (MyNat.succ n) = f n (a n)) ∧
          (∀ (a' : MyNat → MyNat),
            a' MyNat.zero = c →
              (∀ (n : MyNat), a' (MyNat.succ n) = f n (a' n)) → ∀ (n : MyNat), a' n = a n) :=
  by
  let G : MyNat → MyNat → Prop := fun n v =>
    ∀ (R : MyNat → MyNat → Prop),
      R MyNat.zero c → (∀ (m w : MyNat), R m w → R (MyNat.succ m) (f m w)) → R n v
  have hexuniq : ∀ (n : MyNat), ∃ (v : MyNat), G n v ∧ (∀ (w : MyNat), G n w → w = v) :=
    by
    refine MyNat.induction (fun n => ∃ (v : MyNat), G n v ∧ (∀ (w : MyNat), G n w → w = v)) ?_ ?_
    · refine Exists.intro c (And.intro ?_ ?_)
      · intro R hR0 _hRs
        exact hR0
      · intro w hGw
        let R : MyNat → MyNat → Prop := fun m v => m = MyNat.zero → v = c
        have hR0 : R MyNat.zero c := fun _ => rfl
        have hRs : ∀ (m w : MyNat), R m w → R (MyNat.succ m) (f m w) :=
          by
          intro m _w _hRmw hsucc
          exact False.elim (MyNat.succ_ne_zero m hsucc)
        exact hGw R hR0 hRs rfl
    · intro n ihn
      rcases ihn with ⟨v, hGv, huniq⟩
      refine Exists.intro (f n v) (And.intro ?_ ?_)
      · intro R hR0 hRs
        exact hRs n v (hGv R hR0 hRs)
      · intro w hGw
        let R : MyNat → MyNat → Prop := fun m u => G m u ∧ (m = MyNat.succ n → u = f n v)
        have hR0 : R MyNat.zero c := by
          refine And.intro ?_ ?_
          · intro R' hR0' _hRs'
            exact hR0'
          · intro h0eq
            exact False.elim (MyNat.succ_ne_zero n (Eq.symm h0eq))
        have hRs : ∀ (m u : MyNat), R m u → R (MyNat.succ m) (f m u) :=
          by
          intro m u hRmu
          rcases hRmu with ⟨hGmu, _⟩
          refine And.intro ?_ ?_
          · intro R' hR0' hRs'
            exact hRs' m u (hGmu R' hR0' hRs')
          · intro hmsucc
            have hmn : m = n := MyNat.succ_inj m n hmsucc
            rw [hmn] at hGmu
            have hun : u = v := huniq u hGmu
            rw [hmn]
            rw [hun]
        exact And.right (hGw R hR0 hRs) rfl
  let a : MyNat → MyNat := fun n =>
    MyClassical.choose (fun v => G n v ∧ (∀ (w : MyNat), G n w → w = v)) (hexuniq n)
  have ha_spec : ∀ (n : MyNat), G n (a n) ∧ (∀ (w : MyNat), G n w → w = a n) := fun n =>
    MyClassical.choose_spec (fun v => G n v ∧ (∀ (w : MyNat), G n w → w = v)) (hexuniq n)
  refine Exists.intro a (And.intro ?_ (And.intro ?_ ?_))
  · exact Eq.symm ((And.right (ha_spec MyNat.zero)) c (fun _ hR0 _ => hR0))
  · intro n
    have hGsucc : G (MyNat.succ n) (f n (a n)) := fun R hR0 hRs =>
      hRs n (a n) (And.left (ha_spec n) R hR0 hRs)
    exact Eq.symm ((And.right (ha_spec (MyNat.succ n))) (f n (a n)) hGsucc)
  · intro a' ha'0 ha'succ n
    have hGa'n : ∀ (m : MyNat), G m (a' m) :=
      by
      refine MyNat.induction (fun m => G m (a' m)) ?_ ?_
      · intro R hR0 _hRs
        rw [ha'0]
        exact hR0
      · intro m ihm R hR0 hRs
        rw [ha'succ m]
        exact hRs m (a' m) (ihm R hR0 hRs)
    exact (And.right (ha_spec n)) (a' n) (hGa'n n)

