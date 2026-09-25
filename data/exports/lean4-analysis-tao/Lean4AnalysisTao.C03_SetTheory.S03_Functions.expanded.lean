import Lean4AnalysisTao.Util
import Lean4AnalysisTao.C02_NaturalNumbers.S03_Multiplication
import Lean4AnalysisTao.C03_SetTheory.S01_Fundamentals

-- Definition 3.3.1

-- @@ L6-12 expanded
structure MyFun (α β : Type) where
  domain : MySet α
  codomain : MySet β
  prop : α → β → Prop
  isValidProp :
    ∀ (x : α),
      x ∈ domain →
        ∃ (y : β), y ∈ codomain ∧ prop x y ∧ (∀ (y' : β), y' ∈ codomain → prop x y' → y = y')


-- @@ L14-21 expanded
noncomputable def MyFun.eval {α β : Type} (f : MyFun α β) : (x : α) → x ∈ MyFun.domain f → β :=
  fun x hx =>
  MyClassical.choose
    (fun y =>
      y ∈ MyFun.codomain f ∧
        MyFun.prop f x y ∧ (∀ (y' : β), y' ∈ MyFun.codomain f → MyFun.prop f x y' → y = y'))
    ((MyFun.isValidProp f) x hx)


-- @@ L23-32 unexpanded
theorem MyFun.eval_codomain
    {α β : Type}
    (f : MyFun α β)
    (x : α)
    (hx : x ∈ MyFun.domain f) :
    MyFun.eval f x hx ∈ MyFun.codomain f := by
  exact And.left (MyClassical.choose_spec
    (fun y => y ∈ MyFun.codomain f ∧ MyFun.prop f x y ∧
      (∀ (y' : β), y' ∈ MyFun.codomain f → MyFun.prop f x y' → y = y'))
    ((MyFun.isValidProp f) x hx))


-- @@ L34-62 unexpanded
theorem MyFun.def
    {α β : Type}
    (f : MyFun α β)
    (x : α)
    (y : β)
    (hx : x ∈ MyFun.domain f)
    (hy : y ∈ MyFun.codomain f) :
    y = MyFun.eval f x hx ↔ MyFun.prop f x y := by
  have hfxY :
      MyFun.eval f x hx ∈ MyFun.codomain f :=
    MyFun.eval_codomain f x hx
  have hPxfx :
      MyFun.prop f x (MyFun.eval f x hx) := by
    exact And.left (And.right (MyClassical.choose_spec
      (fun y => y ∈ MyFun.codomain f ∧ MyFun.prop f x y ∧
        (∀ (y' : β), y' ∈ MyFun.codomain f → MyFun.prop f x y' → y = y'))
      ((MyFun.isValidProp f) x hx)))
  constructor
  · intro hyfx
    rw [hyfx]
    exact hPxfx
  · intro hPxy
    rcases (MyFun.isValidProp f) x hx with ⟨y', hy', hPxy', hy'!⟩
    have hy'x : y' = y :=
      hy'! y hy hPxy
    have hy'fx : y' = MyFun.eval f x hx :=
      hy'! (MyFun.eval f x hx) hfxY hPxfx
    rw [← hy'fx]
    exact Eq.symm hy'x


-- @@ L64-87 unexpanded
def MyFun.from_fun
    {α β : Type}
    (X : MySet α)
    (Y : MySet β)
    (f : (x : α) → x ∈ X → β)
    (h : ∀ (x : α) (hx : x ∈ X), f x hx ∈ Y) :
    MyFun α β where
  domain := X
  codomain := Y
  prop := fun x y => by
    by_cases hx : x ∈ X
    · exact y = f x hx
    · exact False
  isValidProp := by
    intro x hx
    use f x hx
    constructor
    · exact h x hx
    · constructor
      · dsimp only [prop]
        rw [dif_pos hx]
      · intro y' hy' hP
        rw [dif_pos hx] at hP
        exact Eq.symm hP


-- @@ L89-105 unexpanded
theorem MyFun.from_fun.eval
    {α β : Type}
    (X : MySet α)
    (Y : MySet β)
    (f : (x : α) → x ∈ X → β)
    (h : ∀ (x : α) (hx : x ∈ X), f x hx ∈ Y)
    (x : α)
    (hx : x ∈ X) :
    (MyFun.eval (MyFun.from_fun X Y f h)) x hx = f x hx := by
  have heq :
      f x hx = (MyFun.eval (MyFun.from_fun X Y f h)) x hx := by
    rw [MyFun.def (MyFun.from_fun X Y f h) x (f x hx) hx (h x hx)]
    dsimp only [MyFun.from_fun]
    rw [dif_pos hx]
  exact Eq.symm heq

-- Example 3.3.3

-- @@ L106-106 verbatim
namespace Example_3_3_3


-- @@ L108-108 verbatim
namespace Example_3_3_3_a


-- @@ L110-111 verbatim
private noncomputable def X : MySet MyNat :=
  MySet.Nat.set


-- @@ L113-114 verbatim
private noncomputable def Y : MySet MyNat :=
  MySet.Nat.set


-- @@ L116-129 expanded
private noncomputable def f : MyFun MyNat MyNat
    where
  domain := X
  codomain := Y
  prop := fun x y => y = (MyNat.succ x)
  isValidProp := by
    intro x _hx
    refine ⟨(MyNat.succ x), ?_⟩
    constructor
    · dsimp only [Y]
      exact MySet.Nat.is_nat (MyNat.succ x)
    · constructor
      · dsimp only [MyFun.prop]
      · intro y' _hy' h
        exact Eq.symm h


-- @@ L131-145 unexpanded
example
    (x : MyNat)
    (hx : x ∈ X) :
    MyFun.eval f x hx = x++ := by
  have hy :
      x++ ∈ Y := by
    dsimp only [Y]
    exact MySet.Nat.is_nat (x++)
  have hPx :
      MyFun.prop f x (x++) := by
    dsimp only [f]
  have hfx :
      x++ = MyFun.eval f x hx :=
    Iff.mpr (MyFun.def f x (x++) hx hy) hPx
  exact Eq.symm hfx


-- @@ L147-147 verbatim
end Example_3_3_3_a


-- @@ L149-149 verbatim
namespace Example_3_3_3_b


-- @@ L151-152 expanded
private noncomputable def X : MySet MyNat :=
  MySet.Nat.set \ MySet.singleton MyNat.zero


-- @@ L154-155 verbatim
private noncomputable def Y : MySet MyNat :=
  MySet.Nat.set


-- @@ L157-179 expanded
private noncomputable def f : MyFun MyNat MyNat
    where
  domain := X
  codomain := Y
  prop := fun x y => MyNat.succ y = x
  isValidProp := by
    intro x hx
    dsimp only [X] at hx
    rw [MySet.diff] at hx
    rw [MySet.mem_spec MySet.Nat.set (fun z => ¬(z ∈ (MySet.singleton MyNat.zero : MySet MyNat)))
        x] at hx
    rw [MySet.mem_singleton MyNat.zero x] at hx
    have hxpos : (MyNat.is_positive (x : MyNat)) := fun heq => And.right hx heq
    rcases MyNat.unique_pred_of_pos x hxpos with ⟨y, hy, huniq⟩
    refine ⟨y, ?_⟩
    constructor
    · dsimp only [Y]
      exact MySet.Nat.is_nat y
    · constructor
      · exact hy
      · intro y' _hy' hP
        exact huniq y' hP


-- @@ L181-191 expanded
private theorem aux : MyNat.four ∈ X := by
  dsimp only [X]
  rw [MySet.diff]
  rw [MySet.mem_spec MySet.Nat.set (fun z => ¬(z ∈ (MySet.singleton MyNat.zero : MySet MyNat)))
      MyNat.four]
  constructor
  · exact MySet.Nat.is_nat MyNat.four
  · rw [MySet.mem_singleton MyNat.zero MyNat.four]
    intro h4eq0
    exact MyNat.succ_ne_zero MyNat.three h4eq0


-- @@ L193-204 expanded
example : MyFun.eval f MyNat.four aux = MyNat.three :=
  by
  have h : MyNat.three ∈ Y := by
    dsimp only [Y]
    exact MySet.Nat.is_nat MyNat.three
  have hprop : MyFun.prop f MyNat.four MyNat.three :=
    by
    dsimp only [f]
    dsimp only [MyNat.four]
  rw [← MyFun.def f MyNat.four MyNat.three aux h] at hprop
  exact Eq.symm hprop


-- @@ L206-206 verbatim
end Example_3_3_3_b


-- @@ L208-208 verbatim
end Example_3_3_3


-- @@ L210-220 unexpanded
theorem MyFun.substitute
    {α β : Type}
    (f : MyFun α β)
    (x x' : α)
    (hx : x ∈ MyFun.domain f)
    (hx' : x' ∈ MyFun.domain f)
    (hxx' : x = x') :
    MyFun.eval f x hx = MyFun.eval f x' hx' := by
  sorry

-- Example 3.3.5

-- @@ L221-291 unexpanded
example :
    ∃ (α β : Type) (f : MyFun α β) (x x' : α)
      (hx : x ∈ MyFun.domain f) (hx' : x' ∈ MyFun.domain f),
      ¬ ((x ≠ x') → (MyFun.eval f x hx ≠ MyFun.eval f x' hx')) := by
  let α :=
    MyNat
  let β :=
    MyNat
  let f :
      MyFun α β :=
    {
    domain := MySet.Nat.set
    codomain := MySet.Nat.set
    prop := fun _x y => y = 𝟟
    isValidProp := by
      intro x _hx
      use 𝟟
      constructor
      · exact MySet.Nat.is_nat 𝟟
      · constructor
        · dsimp only [MyFun.prop]
        · intro y' _hy' hP
          exact Eq.symm hP
  }
  let x :
      α :=
    𝟘
  let x' :
      α :=
    𝟙
  let hx :
      x ∈ MyFun.domain f := by
    dsimp only [x]
    dsimp only [f]
    exact MySet.Nat.is_nat 𝟘
  let hx' :
      x' ∈ MyFun.domain f := by
    dsimp only [x']
    dsimp only [f]
    exact MySet.Nat.is_nat 𝟙
  use α, β
  use f
  use x, x', hx, hx'
  intro himp
  have hne :
      x ≠ x' := by
    dsimp only [x]
    dsimp only [x']
    have hne' : 𝟘 ≠ 𝟙 :=
      fun heq => MyNat.succ_ne_zero 𝟘 (Eq.symm heq)
    exact hne'
  have hall
      (a : α)
      (ha : a ∈ MyFun.domain f) :
      MyFun.eval f a ha = 𝟟 := by
    have h7 :
        𝟟 ∈ MyFun.codomain f := by
      dsimp only [f]
      exact MySet.Nat.is_nat 𝟟
    have hPa :
        MyFun.prop f a 𝟟 := by
      dsimp only [f]
    rw [← MyFun.def f a 𝟟 ha h7] at hPa
    exact Eq.symm hPa
  have heval :
      MyFun.eval f x hx = MyFun.eval f x' hx' := by
    rw [hall x hx]
    rw [hall x' hx']
  exact himp hne heval

-- Definition 3.3.8

-- @@ L292-299 unexpanded
def MyFun.eq
    {α β : Type}
    (f g : MyFun α β) :
    Prop :=
  MyFun.domain f = MyFun.domain g
  ∧ MyFun.codomain f = MyFun.codomain g
  ∧ ∀ (x : α) (hxf : x ∈ MyFun.domain f) (hxg : x ∈ MyFun.domain g),
    MyFun.eval f x hxf = MyFun.eval g x hxg

-- @@ L300-302 verbatim
notation f " ≃ " g => MyFun.eq f g

-- Example 3.3.10

-- @@ L303-303 verbatim
namespace Example_3_3_10


-- @@ L305-306 verbatim
private noncomputable def X : MySet MyNat :=
  MySet.Nat.set


-- @@ L308-309 verbatim
private noncomputable def Y : MySet MyNat :=
  MySet.Nat.set


-- @@ L311-317 unexpanded
private theorem aux
    (f : MyNat → MyNat)
    (x : MyNat)
    (_hx : x ∈ X) :
    f x ∈ Y := by
  dsimp only [Y]
  exact MySet.Nat.is_nat (f x)


-- @@ L319-320 expanded
private noncomputable def _f_fn : (x : MyNat) → x ∈ X → MyNat := fun n _h =>
  n ^ MyNat.two + MyNat.two * n + MyNat.one


-- @@ L322-326 unexpanded
private theorem _f_mem
    (x : MyNat)
    (hx : x ∈ X) :
    _f_fn x hx ∈ Y :=
  MySet.Nat.is_nat (_f_fn x hx)


-- @@ L328-329 verbatim
private noncomputable def f : MyFun MyNat MyNat :=
  MyFun.from_fun X Y _f_fn _f_mem


-- @@ L331-332 expanded
private noncomputable def _g_fn : (x : MyNat) → x ∈ X → MyNat := fun n _h =>
  (n + MyNat.one) ^ MyNat.two


-- @@ L334-338 unexpanded
private theorem _g_mem
    (x : MyNat)
    (hx : x ∈ X) :
    _g_fn x hx ∈ Y :=
  MySet.Nat.is_nat (_g_fn x hx)


-- @@ L340-341 verbatim
private noncomputable def g : MyFun MyNat MyNat :=
  MyFun.from_fun X Y _g_fn _g_mem


-- @@ L343-354 expanded
private theorem sq_eq (n : MyNat) :
    n ^ MyNat.two + MyNat.two * n + MyNat.one = (n + MyNat.one) ^ MyNat.two :=
  by
  rw [Exercise_2_3_4 n MyNat.one]
  dsimp only [MyNat.one]
  rw [MyNat.mul_succ (MyNat.two * n) MyNat.zero]
  rw [MyNat.mul_zero (MyNat.two * n)]
  rw [MyNat.zero_add (MyNat.two * n)]
  rw [MyNat.exp_two (MyNat.succ MyNat.zero)]
  rw [MyNat.succ_mul MyNat.zero (MyNat.succ MyNat.zero)]
  rw [MyNat.zero_mul (MyNat.succ MyNat.zero)]
  rw [MyNat.zero_add (MyNat.succ MyNat.zero)]


-- @@ L356-373 expanded
private example : MyFun.eq f g := by
  dsimp only [MyFun.eq]
  refine And.intro rfl (And.intro rfl ?_)
  intro x hxf hxg
  have hfeval : MyFun.eval f x hxf = _f_fn x hxf :=
    by
    dsimp only [f]
    rw [MyFun.from_fun.eval X Y _f_fn _f_mem x hxf]
  have hgeval : MyFun.eval g x hxg = _g_fn x hxg :=
    by
    dsimp only [g]
    rw [MyFun.from_fun.eval X Y _g_fn _g_mem x hxg]
  rw [hfeval]
  rw [hgeval]
  dsimp only [_f_fn]
  dsimp only [_g_fn]
  exact sq_eq x


-- @@ L375-377 verbatim
end Example_3_3_10

-- Example 3.3.11

-- @@ L378-386 expanded
noncomputable def empty_fun (X : MySet β) : MyFun α β
    where
  domain := ∅
  codomain := X
  prop := fun x y => True
  isValidProp := by
    intro x hx
    exact False.elim (MySet.not_mem_empty x hx)


-- @@ L388-405 expanded
example (X : MySet β) (g : MyFun α β) (hgdom : MyFun.domain g = ∅)
    (hgcodom : MyFun.codomain g = X) : MyFun.eq g (empty_fun X) :=
  by
  dsimp only [MyFun.eq]
  constructor
  · dsimp only [empty_fun]
    rw [hgdom]
  · constructor
    · dsimp only [empty_fun]
      rw [hgcodom]
    · intro x hxf hxg
      rw [hgdom] at hxf
      exact
        False.elim
          (MySet.not_mem_empty x hxf)
            -- Definition 3.3.13


-- @@ L406-426 unexpanded
noncomputable def MyFun.comp
    {α β γ : Type}
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g) :
    MyFun α γ := by
  have aux
      (x : α)
      (hx : x ∈ MyFun.domain f) :
      MyFun.eval f x hx ∈ MyFun.domain g := by
    rw [← hfg]
    exact MyFun.eval_codomain f x hx
  let gf :
      (x : α) → x ∈ MyFun.domain f → γ :=
    fun x h => MyFun.eval g (MyFun.eval f x h) (aux x h)
  have aux'
      (x : α)
      (hx : x ∈ MyFun.domain f) :
      gf x hx ∈ MyFun.codomain g :=
    MyFun.eval_codomain g (MyFun.eval f x hx) (aux x hx)
  exact MyFun.from_fun (MyFun.domain f) (MyFun.codomain g) gf aux'


-- @@ L428-439 unexpanded
theorem MyFun.comp.eval
    {α β γ : Type}
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (x : α)
    (hxf : x ∈ MyFun.domain f)
    (hfxg : MyFun.eval f x hxf ∈ MyFun.domain g)
    (hfgx : x ∈ (MyFun.domain (MyFun.comp f g hfg))) :
    (MyFun.eval (MyFun.comp f g hfg)) x hfgx = MyFun.eval g (MyFun.eval f x hxf) hfxg := by
  dsimp only [MyFun.comp]
  rw [MyFun.from_fun.eval (X := MyFun.domain f) (Y := MyFun.codomain g) (x := x) (hx := hxf)]


-- @@ L441-448 verbatim
theorem MyFun.comp.eval.domain
    {α β γ : Type}
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g) :
    (MyFun.domain (MyFun.comp f g hfg)) = MyFun.domain f := by
  dsimp only [MyFun.comp]
  dsimp only [MyFun.from_fun]


-- @@ L450-459 verbatim
theorem MyFun.comp.eval.codomain
    {α β γ : Type}
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g) :
    (MyFun.codomain (MyFun.comp f g hfg)) = MyFun.codomain g := by
  dsimp only [MyFun.comp]
  dsimp only [MyFun.from_fun]

-- Example 3.3.14

-- @@ L460-460 verbatim
namespace Example_3_3_14


-- @@ L462-463 expanded
private noncomputable def _f : MyNat → MyNat := fun n => MyNat.two * n


-- @@ L465-466 expanded
private noncomputable def _g : MyNat → MyNat := fun n => n + MyNat.three


-- @@ L468-469 verbatim
private noncomputable def X : MySet MyNat :=
  MySet.Nat.set


-- @@ L471-472 verbatim
private noncomputable def Y : MySet MyNat :=
  MySet.Nat.set


-- @@ L474-475 verbatim
private noncomputable def Z : MySet MyNat :=
  MySet.Nat.set


-- @@ L477-484 unexpanded
private theorem aux
    (f : MyNat → MyNat)
    (X : MySet MyNat)
    (x : MyNat)
    (_hx : x ∈ X) :
    f x ∈ Y := by
  dsimp only [Y]
  exact MySet.Nat.is_nat (f x)


-- @@ L486-487 verbatim
private noncomputable def f : MyFun MyNat MyNat :=
  MyFun.from_fun X Y (fun x _ => _f x) (fun x hx => aux _f X x hx)


-- @@ L489-490 verbatim
private noncomputable def g : MyFun MyNat MyNat :=
  MyFun.from_fun Y Z (fun x _ => _g x) (fun x hx => aux _g Y x hx)


-- @@ L492-493 verbatim
private noncomputable def gf : MyFun MyNat MyNat :=
  MyFun.comp f g rfl


-- @@ L495-510 expanded
example (x : MyNat) : MyFun.eval gf x (MySet.Nat.is_nat x) = MyNat.two * x + MyNat.three :=
  by
  dsimp only [gf]
  have hfxg : MyFun.eval f x (MySet.Nat.is_nat x) ∈ MyFun.domain g :=
    MyFun.eval_codomain f x (MySet.Nat.is_nat x)
  rw [MyFun.comp.eval f g rfl x (MySet.Nat.is_nat x) hfxg (MySet.Nat.is_nat x)]
  dsimp only [g]
  rw [MyFun.from_fun.eval Y Z (fun x _ => _g x) (fun x hx => aux _g Y x hx)
      (MyFun.eval f x (MySet.Nat.is_nat x)) hfxg]
  dsimp only [f]
  rw [MyFun.from_fun.eval X Y (fun x _ => _f x) (fun x hx => aux _f X x hx) x (MySet.Nat.is_nat x)]
  dsimp only [_f]
  dsimp only [_g]


-- @@ L512-513 verbatim
private noncomputable def fg : MyFun MyNat MyNat :=
  MyFun.comp g f rfl


-- @@ L515-557 expanded
example (x : MyNat) : MyFun.eval fg x (MySet.Nat.is_nat x) = MyNat.two * x + MyNat.six :=
  by
  dsimp only [fg]
  have hgxf : MyFun.eval g x (MySet.Nat.is_nat x) ∈ MyFun.domain f :=
    MyFun.eval_codomain g x (MySet.Nat.is_nat x)
  rw [MyFun.comp.eval g f rfl x (MySet.Nat.is_nat x) hgxf (MySet.Nat.is_nat x)]
  dsimp only [f]
  rw [MyFun.from_fun.eval X Y (fun x _ => _f x) (fun x hx => aux _f X x hx)
      (MyFun.eval g x (MySet.Nat.is_nat x)) hgxf]
  dsimp only [g]
  rw [MyFun.from_fun.eval Y Z (fun x _ => _g x) (fun x hx => aux _g Y x hx) x (MySet.Nat.is_nat x)]
  dsimp only [_f]
  dsimp only [_g]
  rw [MyNat.mul_distrib MyNat.two x MyNat.three]
  have h23 : MyNat.two * MyNat.three = MyNat.six :=
    by
    have h2 : MyNat.two = MyNat.succ (MyNat.succ MyNat.zero) := rfl
    have h3 : MyNat.three = MyNat.succ (MyNat.succ (MyNat.succ MyNat.zero)) := rfl
    have h6 :
      MyNat.six =
        (MyNat.succ (MyNat.succ (MyNat.succ (MyNat.succ (MyNat.succ (MyNat.succ MyNat.zero)))))) :=
      rfl
    rw [h2]
    rw [h3]
    rw [h6]
    rw [MyNat.mul_succ (MyNat.succ (MyNat.succ MyNat.zero)) (MyNat.succ (MyNat.succ MyNat.zero))]
    rw [MyNat.mul_succ (MyNat.succ (MyNat.succ MyNat.zero)) (MyNat.succ MyNat.zero)]
    rw [MyNat.mul_succ (MyNat.succ (MyNat.succ MyNat.zero)) MyNat.zero]
    rw [MyNat.mul_zero (MyNat.succ (MyNat.succ MyNat.zero))]
    rw [MyNat.zero_add (MyNat.succ (MyNat.succ MyNat.zero))]
    rw [MyNat.add_succ ((MyNat.succ (MyNat.succ MyNat.zero)) + (MyNat.succ (MyNat.succ MyNat.zero)))
        (MyNat.succ MyNat.zero)]
    rw [MyNat.add_succ ((MyNat.succ (MyNat.succ MyNat.zero)) + (MyNat.succ (MyNat.succ MyNat.zero)))
        MyNat.zero]
    rw [MyNat.add_zero
        ((MyNat.succ (MyNat.succ MyNat.zero)) + (MyNat.succ (MyNat.succ MyNat.zero)))]
    rw [MyNat.add_succ (MyNat.succ (MyNat.succ MyNat.zero)) (MyNat.succ MyNat.zero)]
    rw [MyNat.add_succ (MyNat.succ (MyNat.succ MyNat.zero)) MyNat.zero]
    rw [MyNat.add_zero (MyNat.succ (MyNat.succ MyNat.zero))]
  rw [h23]


-- @@ L559-561 verbatim
end Example_3_3_14

-- Lemma 3.3.15

-- @@ L562-621 expanded
theorem MyFun.comp_assoc {α β γ δ : Type} (f : MyFun γ δ) (g : MyFun β γ) (h : MyFun α β)
    (hgh : MyFun.codomain h = MyFun.domain g) (hfg : MyFun.codomain g = MyFun.domain f) :
    MyFun.eq ((MyFun.comp (MyFun.comp h g hgh)) f hfg) (MyFun.comp h (MyFun.comp g f hfg) hgh) :=
  by
  dsimp only [MyFun.eq]
  constructor
  · dsimp only [MyFun.comp]
    dsimp only [MyFun.from_fun]
  · constructor
    · dsimp only [MyFun.comp]
      dsimp only [MyFun.from_fun]
    · intro x hxh hxg
      dsimp only [MyFun.comp] at hxh
      dsimp only [MyFun.from_fun] at hxh
      have hf_gh : (MyFun.codomain (MyFun.comp h g hgh)) = MyFun.domain f :=
        by
        rw [MyFun.comp.eval.codomain h g hgh]
        exact hfg
      have hghxf : (MyFun.eval (MyFun.comp h g hgh)) x hxh ∈ MyFun.domain f :=
        by
        rw [← hfg]
        rw [← MyFun.comp.eval.codomain h g hgh]
        exact MyFun.eval_codomain (MyFun.comp h g hgh) x hxh
      rw [MyFun.comp.eval (MyFun.comp h g hgh) f hf_gh x hxh hghxf hxh]
      have hhxg : MyFun.eval h x hxh ∈ MyFun.domain g :=
        by
        rw [← hgh]
        exact MyFun.eval_codomain h x hxh
      have hg_hxf : MyFun.eval g (MyFun.eval h x hxh) hhxg ∈ MyFun.domain f :=
        by
        rw [← hfg]
        exact MyFun.eval_codomain g (MyFun.eval h x hxh) hhxg
      have hcompeval :
        (MyFun.eval (MyFun.comp h g hgh)) x hxh = MyFun.eval g (MyFun.eval h x hxh) hhxg := by
        rw [MyFun.comp.eval h g hgh x hxh hhxg hxh]
      rw [MyFun.substitute f ((MyFun.eval (MyFun.comp h g hgh)) x hxh)
          (MyFun.eval g (MyFun.eval h x hxh) hhxg) hghxf hg_hxf hcompeval]
      have hfg_h : MyFun.codomain h = (MyFun.domain (MyFun.comp g f hfg)) :=
        by
        rw [MyFun.comp.eval.domain g f hfg]
        exact hgh
      have hhxfg : MyFun.eval h x hxh ∈ (MyFun.domain (MyFun.comp g f hfg)) :=
        by
        rw [MyFun.comp.eval.domain g f hfg]
        rw [← hgh]
        exact MyFun.eval_codomain h x hxh
      rw [MyFun.comp.eval h (MyFun.comp g f hfg) hfg_h x hxh hhxfg hxh]
      rw [MyFun.comp.eval g f hfg (MyFun.eval h x hxh) hhxg hg_hxf hhxg]
        -- Definition 3.3.17


-- @@ L622-627 unexpanded
def MyFun.isInjective
    {α β : Type}
    (f : MyFun α β) :
    Prop :=
  ∀ (x x' : α) (hx : x ∈ MyFun.domain f) (hx' : x' ∈ MyFun.domain f),
    x ≠ x' → MyFun.eval f x hx ≠ MyFun.eval f x' hx'


-- @@ L629-634 unexpanded
def MyFun.isInjective'
    {α β : Type}
    (f : MyFun α β) :
    Prop :=
  ∀ (x x' : α) (hx : x ∈ MyFun.domain f) (hx' : x' ∈ MyFun.domain f),
    MyFun.eval f x hx = MyFun.eval f x' hx' → x = x'


-- @@ L636-653 expanded
theorem MyFun.isInjective_iff {α β : Type} (f : MyFun α β) :
    MyFun.isInjective f ↔ (MyFun.isInjective' f) :=
  by
  constructor
  · intro h
    dsimp only [MyFun.isInjective] at h
    dsimp only [MyFun.isInjective']
    intro x x' hx hx' hff'
    first
    | intro h'
    | refine MyClassical.byContradiction _ (fun h' => ?_)
    exact h x x' hx hx' h' hff'
  · intro h
    dsimp only [MyFun.isInjective'] at h
    dsimp only [MyFun.isInjective]
    intro x x' hx hx' hxx' hff'
    exact
      hxx'
        (h x x' hx hx' hff')
          -- Example 3.3.18


-- @@ L654-654 verbatim
namespace Example_3_3_18


-- @@ L656-657 expanded
private noncomputable def _f_fn : (x : MyNat) → x ∈ MySet.Nat.set → MyNat := fun n _h =>
  n ^ MyNat.two


-- @@ L659-663 unexpanded
private theorem _f_mem
    (x : MyNat)
    (hx : x ∈ MySet.Nat.set) :
    _f_fn x hx ∈ MySet.Nat.set :=
  MySet.Nat.is_nat (_f_fn x hx)


-- @@ L665-666 verbatim
private noncomputable def f : MyFun MyNat MyNat :=
  MyFun.from_fun MySet.Nat.set MySet.Nat.set _f_fn _f_mem


-- @@ L668-670 verbatim
example :
    MyFun.isInjective f := by
  sorry


-- @@ L672-674 verbatim
end Example_3_3_18

-- Definition 3.3.20

-- @@ L675-682 expanded
def MyFun.isSurjective {α β : Type} (f : MyFun α β) : Prop :=
  ∀ (y : β), y ∈ MyFun.codomain f → ∃ (x : α) (hx : x ∈ MyFun.domain f), MyFun.eval f x hx = y


-- @@ L683-683 verbatim
namespace Example_3_3_21


-- @@ L685-688 expanded
private def P (x y : MyNat) : Prop :=
  y = x ^ MyNat.two


-- @@ L690-700 unexpanded
private theorem hP_unique
    (x : MyNat)
    (_hx : x ∈ MySet.Nat.set) :
    ∃ (y : MyNat), P x y ∧ (∀ (z : MyNat), P x z → z = y) := by
  have huniq
      (z : MyNat)
      (hz : P x z) :
      z = x ^ 𝟚 := by
    dsimp only [P] at hz
    exact hz
  exact Exists.intro (x ^ 𝟚) (And.intro rfl huniq)


-- @@ L702-703 expanded
private noncomputable def Y : MySet MyNat :=
  MySet.replace MySet.Nat.set _ hP_unique


-- @@ L705-711 unexpanded
private theorem _f_mem
    (x : MyNat)
    (_hx : x ∈ MySet.Nat.set) :
    x ^ 𝟚 ∈ Y := by
  dsimp only [Y]
  rw [MySet.mem_replace MySet.Nat.set P hP_unique (x ^ 𝟚)]
  exact Exists.intro x (And.intro (MySet.Nat.is_nat x) rfl)


-- @@ L713-714 expanded
private noncomputable def f : MyFun MyNat MyNat :=
  MyFun.from_fun MySet.Nat.set Y (fun x _ => x ^ MyNat.two) _f_mem


-- @@ L716-732 expanded
example : MyFun.isSurjective f := by
  dsimp only [MyFun.isSurjective]
  intro y hy
  dsimp only [f] at hy
  dsimp only [MyFun.from_fun] at hy
  dsimp only [Y] at hy
  rw [MySet.mem_replace MySet.Nat.set P hP_unique y] at hy
  rcases hy with ⟨x, hxnat, hPxy⟩
  dsimp only [P] at hPxy
  have hfxeq : MyFun.eval f x (MySet.Nat.is_nat x) = y :=
    by
    dsimp only [f]
    rw [MyFun.from_fun.eval MySet.Nat.set Y (fun x _ => x ^ MyNat.two) _f_mem x
        (MySet.Nat.is_nat x)]
    exact Eq.symm hPxy
  exact Exists.intro x (Exists.intro (MySet.Nat.is_nat x) hfxeq)


-- @@ L734-736 verbatim
end Example_3_3_21

-- Definition 3.3.23

-- @@ L737-743 verbatim
def MyFun.isBijective
    {α β : Type}
    (f : MyFun α β) :
    Prop :=
  MyFun.isInjective f ∧ MyFun.isSurjective f

-- Example 3.3.25

-- @@ L744-744 verbatim
namespace Example_3_3_25


-- @@ L746-747 verbatim
private noncomputable def X : MySet MyNat :=
  MySet.Nat.set


-- @@ L749-750 expanded
private noncomputable def Y : MySet MyNat :=
  MySet.Nat.set \ MySet.singleton MyNat.zero


-- @@ L752-753 expanded
private noncomputable def _f_fn : (x : MyNat) → x ∈ X → MyNat := fun n _h => MyNat.succ n


-- @@ L755-767 unexpanded
private theorem _f_mem
    (x : MyNat)
    (hx : x ∈ X) :
    _f_fn x hx ∈ Y := by
  dsimp only [Y]
  dsimp only [_f_fn]
  rw [MySet.diff]
  rw [MySet.mem_spec MySet.Nat.set (fun z => z ∉ ⦃𝟘⦄) (x++)]
  constructor
  · exact MySet.Nat.is_nat (x++)
  · intro h
    rw [MySet.mem_singleton (γ := MySet MyNat) 𝟘 (x++)] at h
    exact MyNat.succ_ne_zero x h


-- @@ L769-770 verbatim
private noncomputable def f : MyFun MyNat MyNat :=
  MyFun.from_fun X Y _f_fn _f_mem


-- @@ L772-802 expanded
example : MyFun.isBijective f := by
  dsimp only [MyFun.isBijective]
  constructor
  · dsimp only [MyFun.isInjective]
    intro x x' hx hx' hxx'
    dsimp only [f]
    rw [MyFun.from_fun.eval X Y _f_fn _f_mem x hx]
    rw [MyFun.from_fun.eval X Y _f_fn _f_mem x' hx']
    dsimp only [_f_fn]
    exact MyNat.succ_inj' x x' hxx'
  · dsimp only [MyFun.isSurjective]
    intro y hy
    dsimp only [f] at hy
    dsimp only [MyFun.from_fun] at hy
    dsimp only [Y] at hy
    rw [MySet.diff] at hy
    have hmem : y ∈ MySet.Nat.set ∧ ¬y ∈ MySet.singleton MyNat.zero :=
      Iff.mp (MySet.mem_spec MySet.Nat.set (fun z => ¬z ∈ MySet.singleton MyNat.zero) y) hy
    rcases hmem with ⟨_hy, hny⟩
    rw [MySet.mem_singleton (γ := MySet MyNat) MyNat.zero y] at hny
    have hpos : MyNat.is_positive y := hny
    rcases MyNat.unique_pred_of_pos y hpos with ⟨x, hx, _⟩
    refine Exists.intro x (Exists.intro (MySet.Nat.is_nat x) ?_)
    dsimp only [f]
    rw [MyFun.from_fun.eval X Y _f_fn _f_mem x (MySet.Nat.is_nat x)]
    dsimp only [_f_fn]
    exact hx


-- @@ L804-806 verbatim
end Example_3_3_25

-- Remark 3.3.27

-- @@ L807-824 unexpanded
theorem MyFun.exists_unique_of_bijective
    {α β : Type}
    (f : MyFun α β)
    (hf : MyFun.isBijective f)
    (y : β)
    (hy : y ∈ MyFun.codomain f) :
    ∃ (x : α) (hx : x ∈ MyFun.domain f), MyFun.eval f x hx = y ∧
      ∀ (x' : α) (hx' : x' ∈ MyFun.domain f), MyFun.eval f x' hx' = y → x = x' := by
  dsimp only [MyFun.isBijective] at hf
  rcases hf with ⟨hinj, hsurj⟩
  dsimp only [MyFun.isSurjective] at hsurj
  rcases hsurj y hy with ⟨x, hx, hxy⟩
  use x, hx, hxy
  intro x' hx' hxy'
  rw [MyFun.isInjective_iff f] at hinj
  dsimp only [MyFun.isInjective'] at hinj
  rw [← hxy'] at hxy
  exact hinj x x' hx hx' hxy


-- @@ L826-856 unexpanded
noncomputable def MyFun.inv
    {α β : Type}
    (f : MyFun α β)
    (hf : MyFun.isBijective f) :
    MyFun β α := by
  let X :
      MySet β :=
    MyFun.codomain f
  let Y :
      MySet α :=
    MyFun.domain f
  let finv
      (y : β)
      (hy : y ∈ X) :
      α :=
    MyClassical.choose
      (fun x => ∃ (hx : x ∈ MyFun.domain f), MyFun.eval f x hx = y ∧
        ∀ (x' : α) (hx' : x' ∈ MyFun.domain f), MyFun.eval f x' hx' = y → x = x')
      (MyFun.exists_unique_of_bijective f hf y hy)
  let aux
      (y : β)
      (hy : y ∈ X) :
      finv y hy ∈ Y := by
    dsimp only [Y]
    dsimp only [finv]
    rcases MyClassical.choose_spec
      (fun x => ∃ (hx : x ∈ MyFun.domain f), MyFun.eval f x hx = y ∧
        ∀ (x' : α) (hx' : x' ∈ MyFun.domain f), MyFun.eval f x' hx' = y → x = x')
      (MyFun.exists_unique_of_bijective f hf y hy) with ⟨hx, _hspec⟩
    exact hx
  exact MyFun.from_fun X Y finv aux


-- @@ L858-860 verbatim
section Exercises

-- Exercise 3.3.1

-- @@ L861-864 expanded
example (f : MyFun α β) : MyFun.eq f f := by sorry


-- @@ L866-870 expanded
example (f g : MyFun α β) (hfg : MyFun.eq f g) : MyFun.eq g f := by sorry


-- @@ L872-877 expanded
example (f g h : MyFun α β) (hfg : MyFun.eq f g) (hgh : MyFun.eq g h) : MyFun.eq f h := by sorry


-- @@ L879-889 expanded
example (f f' : MyFun α β) (g g' : MyFun β γ) (hfg : MyFun.codomain f = MyFun.domain g)
    (hf'g' : MyFun.codomain f' = MyFun.domain g') (hff' : MyFun.eq f f') (hgg' : MyFun.eq g g') :
    MyFun.eq (MyFun.comp f g hfg) (MyFun.comp f' g' hf'g') := by
  sorry
    -- Exercise 3.3.2


-- @@ L890-897 verbatim
example
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hf : MyFun.isInjective f)
    (hg : MyFun.isInjective g) :
    (MyFun.isInjective (MyFun.comp f g hfg)) := by
  sorry


-- @@ L899-911 verbatim
example
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hf : MyFun.isSurjective f)
    (hg : MyFun.isSurjective g) :
    (MyFun.isSurjective (MyFun.comp f g hfg)) := by
  sorry

-- Exercise 3.3.3
-- TODO: When is the empty function into a given set X injective? surjective? bijective?

-- Exercise 3.3.4

-- @@ L912-922 expanded
example (f f' : MyFun α β) (g : MyFun β γ) (hfg : MyFun.codomain f = MyFun.domain g)
    (hf'g : MyFun.codomain f' = MyFun.domain g)
    (hcomp : MyFun.eq (MyFun.comp f g hfg) (MyFun.comp f' g hf'g)) (hg : MyFun.isInjective g) :
    MyFun.eq f f' := by
  sorry
    -- TODO: Is the same statement true if g is not injective?


-- @@ L924-936 expanded
example (f : MyFun α β) (g g' : MyFun β γ) (hfg : MyFun.codomain f = MyFun.domain g)
    (hfg' : MyFun.codomain f = MyFun.domain g')
    (hcomp : MyFun.eq (MyFun.comp f g hfg) (MyFun.comp f g' hfg')) (hf : MyFun.isSurjective f) :
    MyFun.eq g g' := by
  sorry
    -- TODO: Is the same statement true if f is not surjective?
    
    -- Exercise 3.3.5


-- @@ L937-945 verbatim
example
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hcomp : (MyFun.isInjective (MyFun.comp f g hfg))) :
    MyFun.isInjective f := by
  sorry

-- TODO: Is it true that g must also be injective?


-- @@ L947-957 verbatim
example
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hcomp : (MyFun.isSurjective (MyFun.comp f g hfg))) :
    MyFun.isSurjective g := by
  sorry

-- TODO: Is it true that f must also be surjective?

-- Exercise 3.3.6

-- @@ L958-958 verbatim
section Exercise_3_3_6


-- @@ L960-964 verbatim
example
    (f : MyFun α β)
    (hf : MyFun.isBijective f) :
    (MyFun.isBijective (MyFun.inv f hf)) := by
  sorry


-- @@ L966-971 expanded
example (f : MyFun α β) (hf : MyFun.isBijective f) (hfi : (MyFun.isBijective (MyFun.inv f hf))) :
    MyFun.eq ((MyFun.inv (MyFun.inv f hf)) hfi) f := by sorry


-- @@ L973-975 verbatim
end Exercise_3_3_6

-- Exercise 3.3.7

-- @@ L976-976 verbatim
section Exercise_3_3_7


-- @@ L978-985 verbatim
example
    (f : MyFun α β)
    (g : MyFun β γ)
    (hfg : MyFun.codomain f = MyFun.domain g)
    (hf : MyFun.isBijective f)
    (hg : MyFun.isBijective g) :
    (MyFun.isBijective (MyFun.comp f g hfg)) := by
  sorry


-- @@ L987-997 expanded
example (f : MyFun α β) (g : MyFun β γ) (hfg : MyFun.codomain f = MyFun.domain g)
    (hf : MyFun.isBijective f) (hg : MyFun.isBijective g)
    (hgf : (MyFun.isBijective (MyFun.comp f g hfg)))
    (hgfinv_cod_finvdom : (MyFun.codomain (MyFun.inv g hg)) = (MyFun.domain (MyFun.inv f hf))) :
    MyFun.eq ((MyFun.inv (MyFun.comp f g hfg)) hgf)
      ((MyFun.comp (MyFun.inv g hg)) (MyFun.inv f hf) hgfinv_cod_finvdom) :=
  by sorry


-- @@ L999-1001 verbatim
end Exercise_3_3_7

-- Exercise 3.3.8

-- @@ L1002-1002 verbatim
section Exercise_3_3_8


-- @@ L1004-1017 unexpanded
private def ι'
    {α : Type}
    (X Y : MySet α)
    (hXY : X ⊆ Y) :
    MyFun α α := by
  let f :
      α → α :=
    fun x => x
  have h
      (x : α)
      (hx : x ∈ X) :
      f x ∈ Y :=
    hXY x hx
  exact MyFun.from_fun X Y (fun x _ => f x) h


-- @@ L1019-1028 unexpanded
private theorem aux'
    {α : Type}
    (X : MySet α) :
    X ⊆ X := by
  have h
      (x : α)
      (hx : x ∈ X) :
      x ∈ X :=
    hx
  exact h


-- @@ L1030-1034 verbatim
private def ι_id'
    {α : Type}
    (X : MySet α) :
    MyFun α α :=
  ι' X X (aux' X)


-- @@ L1036-1043 unexpanded
example
    {X Y Z : MySet α}
    (hXY : X ⊆ Y)
    (hYZ : Y ⊆ Z)
    (h₁ : (MyFun.codomain (ι' X Y hXY)) = (MyFun.domain (ι' Y Z hYZ)))
    (h₂ : X ⊆ Z) :
    (MyFun.comp (ι' X Y hXY)) (ι' Y Z hYZ) h₁ ≃ ι' X Z h₂ := by
  sorry


-- @@ L1045-1051 expanded
example (A : MySet α) (f : MyFun α β) (hfdom : MyFun.domain f = A)
    (h₁ : (MyFun.codomain (ι_id' A)) = MyFun.domain f) : MyFun.eq f ((MyFun.comp (ι_id' A)) f h₁) :=
  by sorry


-- @@ L1053-1059 expanded
example (B : MySet β) (f : MyFun α β) (hfcodom : MyFun.codomain f = B)
    (h₁ : MyFun.codomain f = (MyFun.domain (ι_id' B))) : MyFun.eq f (MyFun.comp f (ι_id' B) h₁) :=
  by sorry


-- @@ L1061-1069 expanded
example (f : MyFun α β) (hf : MyFun.isBijective f)
    (h₁ : (MyFun.codomain (MyFun.inv f hf)) = MyFun.domain f)
    (h₂ : MyFun.codomain f = (MyFun.domain (MyFun.inv f hf))) (B : MySet β)
    (hfcodom : MyFun.codomain f = B) : MyFun.eq ((MyFun.comp (MyFun.inv f hf)) f h₁) (ι_id' B) := by
  sorry


-- @@ L1071-1078 expanded
example (f : MyFun α β) (hf : MyFun.isBijective f)
    (h₁ : MyFun.codomain f = (MyFun.domain (MyFun.inv f hf))) (A : MySet α)
    (hfdom : MyFun.domain f = A) : MyFun.eq (MyFun.comp f (MyFun.inv f hf) h₁) (ι_id' A) := by sorry


-- @@ L1080-1091 expanded
example (X Y : MySet α) (Z : MySet β) (hXY : MySet.disjoint X Y) (f : MyFun α β)
    (hfdom : MyFun.domain f = X) (hfcodom : MyFun.codomain f = Z) (g : MyFun α β)
    (hgdom : MyFun.domain g = Y) (hgcodom : MyFun.codomain g = Z) :
    ∃ (h : MyFun α β), MyFun.domain h = X ∪ Y ∧ MyFun.codomain h = Z := by sorry


-- @@ L1093-1093 verbatim
end Exercise_3_3_8


-- @@ L1095-1095 verbatim
end Exercises
