import OAI.Computability.Superstring.Combinators


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace Superstring.BitCode


-- @@ L7-7 verbatim
attribute [fun_prop] Poly

-- @@ L8-8 verbatim
attribute [fun_prop] Poly.id Poly.const Poly.comp Poly.pair Poly.fst Poly.snd

-- @@ L9-9 verbatim
attribute [fun_prop] Poly.cons Poly.ite Poly.reverse Poly.append Poly.length Poly.size

-- @@ L10-10 verbatim
attribute [fun_prop] Poly.not Poly.and Poly.or Poly.eqBool Poly.eq Poly.succ Poly.pred Poly.isZero Poly.add

-- @@ L11-11 verbatim
attribute [fun_prop] Poly.flatten Poly.tail Poly.headD Poly.isEmpty Poly.encoding


-- @@ L13-13 verbatim
namespace Poly


-- @@ L15-18 verbatim
@[fun_prop] theorem mapFn {α β γ : Type} [Coded α] [Coded β] [Coded γ]
    {f : γ × α → β} {xs : γ → List α} (hf : Poly f) (hxs : Poly xs) :
    Poly (fun c => (xs c).map (fun x => f (c, x))) :=
  (mapWith hf).comp (id.pair hxs)


-- @@ L20-23 verbatim
@[fun_prop] theorem filterFn {α γ : Type} [Coded α] [Coded γ]
    {p : γ × α → Bool} {xs : γ → List α} (hp : Poly p) (hxs : Poly xs) :
    Poly (fun c => (xs c).filter (fun x => p (c, x))) :=
  (filterWith hp).comp (id.pair hxs)

 
-- @@ L25-36 verbatim
theorem sub : Poly (fun p : ℕ × ℕ => p.1 - p.2) := by
   have he : ∀ j a : ℕ, Nat.pred^[j] a = a - j := by
     intro j; induction j with
     | zero => simp
     | succ j ih => intro a; rw [Function.iterate_succ_apply', ih]; simp only [Nat.pred_eq_sub_one]; omega
   have hi := pred.iterate Polynomial.X (by
     intro n a j _
     rw [he]
     simp only [Polynomial.eval_X, bitSize_prod, bitSize_nat]
     omega)
   convert hi.comp (snd.pair fst) using 1
   funext p; simp only [Function.comp_apply, he]


-- @@ L38-38 verbatim
attribute [fun_prop] sub

 
-- @@ L40-43 verbatim
theorem le : Poly (fun p : ℕ × ℕ => decide (p.1 ≤ p.2)) := by
   have h := isZero.comp sub
   convert h using 1
   funext p; simp only [Function.comp_apply, decide_eq_decide]; omega

 
-- @@ L45-48 verbatim
theorem lt : Poly (fun p : ℕ × ℕ => decide (p.1 < p.2)) := by
   have h := not.comp (le.comp (snd.pair fst))
   convert h using 1
   funext p; simp only [Function.comp_apply, ← decide_not, decide_eq_decide]; omega


-- @@ L50-50 verbatim
attribute [fun_prop] le lt

 
-- @@ L52-57 verbatim
theorem max : Poly (fun p : ℕ × ℕ => max p.1 p.2) := by
   have h : Poly (fun p : ℕ × ℕ => if decide (p.1 ≤ p.2) then p.2 else p.1) := by fun_prop
   convert h using 1
   funext p; by_cases hh : p.1 ≤ p.2
   · simp [hh]
   · simp [hh, max_eq_left (Nat.le_of_not_ge hh)]

 
-- @@ L59-64 verbatim
theorem min : Poly (fun p : ℕ × ℕ => min p.1 p.2) := by
   have h : Poly (fun p : ℕ × ℕ => if decide (p.1 ≤ p.2) then p.1 else p.2) := by fun_prop
   convert h using 1
   funext p; by_cases hh : p.1 ≤ p.2
   · simp [hh]
   · simp [hh, min_eq_right (Nat.le_of_not_ge hh)]


-- @@ L66-66 verbatim
attribute [fun_prop] max min

 
-- @@ L68-83 verbatim
theorem mul : Poly (fun p : ℕ × ℕ => p.1 * p.2) := by
   let step : ℕ × ℕ → ℕ × ℕ := fun p => (p.1, p.2 + p.1)
   have hs : Poly step := by dsimp [step]; fun_prop
   have he : ∀ j (a b : ℕ), step^[j] (a, b) = (a, b + j * a) := by
     intro j; induction j with
     | zero => simp
     | succ j ih => intro a b; rw [Function.iterate_succ_apply', ih]; dsimp [step]; congr 1; ring
   have hi := hs.iterate (Polynomial.X + Polynomial.X * Polynomial.X) (by
     intro n p j hj
     rcases p with ⟨a, b⟩
     rw [he]
     simp only [bitSize_prod, bitSize_nat, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X]
     nlinarith)
   have hp := snd.comp (hi.comp (fst.pair (snd.pair (const 0))))
   convert hp using 1
   funext p; simp only [Function.comp_apply, he, Nat.zero_add]


-- @@ L85-85 verbatim
attribute [fun_prop] mul

 
-- @@ L87-98 verbatim
theorem drop {α : Type} [Coded α] : Poly (fun p : ℕ × List α => p.2.drop p.1) := by
   have he : ∀ n (xs : List α), List.tail^[n] xs = xs.drop n := by
     intro n; induction n with
     | zero => simp
     | succ n ih => intro xs; rw [Function.iterate_succ_apply', ih]; simp [List.tail_drop]
   have hi := (tail : Poly (List.tail : List α → List α)).iterate Polynomial.X (by
     intro n xs j _
     rw [he]
     have h := bitSize_sublist (List.drop_sublist j xs)
     simp only [Polynomial.eval_X, bitSize_prod]; omega)
   convert hi using 1
   funext p; exact (he _ _).symm


-- @@ L100-100 verbatim
attribute [fun_prop] drop

 
-- @@ L102-106 verbatim
theorem take {α : Type} [Coded α] : Poly (fun p : ℕ × List α => p.2.take p.1) := by
   have h : Poly (fun p : ℕ × List α => (p.2.reverse.drop (p.2.length - p.1)).reverse) := by fun_prop
   convert h using 1
   funext p
   simp only [List.drop_reverse, List.reverse_reverse, List.take_eq_take_iff]; omega


-- @@ L108-108 verbatim
attribute [fun_prop] take

 
-- @@ L110-115 verbatim
theorem getD {α : Type} [Coded α] (d : α) :
     Poly (fun p : List α × ℕ => p.1[p.2]?.getD d) := by
   have h := (headD d).comp (drop.comp (snd.pair fst))
   convert h using 1
   funext p
   simp only [Function.comp_apply, List.headD_eq_head?_getD, List.head?_drop]


-- @@ L117-117 verbatim
end Poly


-- @@ L119-119 verbatim
end Superstring.BitCode


-- @@ L121-121 verbatim
namespace Superstring.BitCode

-- @@ L122-122 verbatim
namespace Poly


-- @@ L124-126 verbatim
@[fun_prop] theorem eqFn {α β : Type} [Coded α] [Coded β] [DecidableEq β]
    {f g : α → β} (hf : Poly f) (hg : Poly g) : Poly (fun a => decide (f a = g a)) :=
  eq.comp (hf.pair hg)


-- @@ L128-129 verbatim
@[fun_prop] theorem leFn {α : Type} [Coded α] {f g : α → ℕ}
    (hf : Poly f) (hg : Poly g) : Poly (fun a => decide (f a ≤ g a)) := le.comp (hf.pair hg)


-- @@ L131-132 verbatim
@[fun_prop] theorem ltFn {α : Type} [Coded α] {f g : α → ℕ}
    (hf : Poly f) (hg : Poly g) : Poly (fun a => decide (f a < g a)) := lt.comp (hf.pair hg)

 
-- @@ L134-144 verbatim
theorem anyB : Poly (fun xs : List Bool => xs.any _root_.id) := by
   have hs : ∀ (a x : Bool), bitSize (a || x) ≤ bitSize a + (0 : Polynomial ℕ).eval (bitSize x) := by
     intros; simp only [bitSize, bits_bool, List.length_singleton, Polynomial.eval_zero, Nat.add_zero, le_refl]
   have hp := (foldl_additive or 0 hs).comp ((id : Poly (_root_.id : List Bool → List Bool)).pair (const false))
   convert hp using 1
   funext xs
   have he : ∀ b : Bool, xs.foldl (· || ·) b = (b || xs.any _root_.id) := by
     intro b; induction xs generalizing b with
     | nil => simp
     | cons x xs ih => simp [ih, Bool.or_assoc]
   simp only [Function.comp_apply, _root_.id, he, Bool.false_or]

 
-- @@ L146-151 verbatim
theorem allB : Poly (fun xs : List Bool => xs.all _root_.id) := by
   have hp := not.comp (anyB.comp (map not))
   convert hp using 1
   funext xs
   simp only [Function.comp_apply, List.any_map, Function.comp_def, _root_.id]
   exact List.all_eq_not_any_not


-- @@ L153-158 verbatim
@[fun_prop] theorem anyFn {α γ : Type} [Coded α] [Coded γ] {p : γ × α → Bool}
    {xs : γ → List α} (hp : Poly p) (hxs : Poly xs) :
    Poly (fun c => (xs c).any (fun x => p (c, x))) := by
   have h := anyB.comp (mapFn hp hxs)
   convert h using 1
   funext c; simp


-- @@ L160-165 verbatim
@[fun_prop] theorem allFn {α γ : Type} [Coded α] [Coded γ] {p : γ × α → Bool}
    {xs : γ → List α} (hp : Poly p) (hxs : Poly xs) :
    Poly (fun c => (xs c).all (fun x => p (c, x))) := by
   have h := allB.comp (mapFn hp hxs)
   convert h using 1
   funext c; simp

 
-- @@ L167-176 verbatim
theorem mem {α : Type} [Coded α] [DecidableEq α] :
    Poly (fun p : α × List α => decide (p.1 ∈ p.2)) := by
   have hf : Poly (fun q : (α × List α) × α => decide (q.1.1 = q.2)) :=
     eq.comp ((fst.comp fst).pair snd)
   have hp := anyFn hf (snd : Poly (Prod.snd : α × List α → List α))
   convert hp using 1
   funext p
   apply Bool.eq_iff_iff.mpr
   simp only [decide_eq_true_eq, List.any_eq_true]
   simp


-- @@ L178-180 verbatim
@[fun_prop] theorem memFn {α γ : Type} [Coded α] [Coded γ] [DecidableEq α]
    {x : γ → α} {xs : γ → List α} (hx : Poly x) (hxs : Poly xs) :
    Poly (fun c => decide (x c ∈ xs c)) := mem.comp (hx.pair hxs)

 
-- @@ L182-189 verbatim
theorem sum : Poly (List.sum : List ℕ → ℕ) := by
   have hs : ∀ (a x : ℕ), bitSize (a + x) ≤ bitSize a +
       (Polynomial.X : Polynomial ℕ).eval (bitSize x) := by intros; simp only [bitSize_nat, Polynomial.eval_X]; omega
   have hp := (foldl_additive add Polynomial.X hs).comp
     ((id : Poly (_root_.id : List ℕ → List ℕ)).pair (const 0))
   convert hp using 1
   funext xs
   simp [List.sum_eq_foldl]


-- @@ L191-191 verbatim
attribute [fun_prop] sum

 
-- @@ L193-198 verbatim
theorem maxFold : Poly (fun xs : List ℕ => xs.foldl Max.max 0) := by
   have hs : ∀ (a x : ℕ), bitSize (Max.max a x) ≤ bitSize a +
       (Polynomial.X : Polynomial ℕ).eval (bitSize x) := by
     intros; simp only [bitSize_nat, Polynomial.eval_X]; omega
   exact (foldl_additive max Polynomial.X hs).comp
     ((id : Poly (_root_.id : List ℕ → List ℕ)).pair (const 0))


-- @@ L200-200 verbatim
attribute [fun_prop] maxFold


-- @@ L202-202 verbatim
end Poly

 
-- @@ L204-204 verbatim
def rangeStep (p : ℕ × List ℕ) : ℕ × List ℕ := (p.1 + 1, p.1 :: p.2)

 
-- @@ L206-214 verbatim
theorem iterate_rangeStep (j a : ℕ) (out : List ℕ) :
     rangeStep^[j] (a, out) = (a + j, (List.range' a j).reverse ++ out) := by
   induction j with
   | zero => simp
   | succ j ih =>
     rw [Function.iterate_succ_apply', ih]
     simp only [rangeStep, List.range'_1_concat, List.reverse_append, List.reverse_singleton,
       List.cons_append]
     congr 1


-- @@ L216-216 verbatim
namespace Poly

 
-- @@ L218-236 verbatim
theorem range : Poly (List.range : ℕ → List ℕ) := by
   have hs : Poly rangeStep := by unfold rangeStep; fun_prop
   have hi := hs.iterate (4 * Polynomial.X * Polynomial.X + 4 * Polynomial.X + 4) (by
     intro n p j hj
     rcases p with ⟨a, out⟩
     rw [iterate_rangeStep]
     have hh := bitSize_map_le (List.range' a j) (_root_.id : ℕ → ℕ) (a + j + 1)
       (fun x hx => by simp only [_root_.id, bitSize_nat]; have := List.mem_range'.mp hx; omega)
     simp only [List.map_id, List.length_range'] at hh
     have ha := bitSize_append (List.range' a j).reverse out
     rw [bitSize_reverse] at ha
     simp only [bitSize_prod, bitSize_nat, Polynomial.eval_add, Polynomial.eval_mul,
       Polynomial.eval_ofNat, Polynomial.eval_X]
     nlinarith)
   have hp := reverse.comp (snd.comp (hi.comp ((id : Poly (_root_.id : ℕ → ℕ)).pair (const (0, ([] : List ℕ))))))
   convert hp using 1
   funext n
   simp only [Function.comp_apply, _root_.id, iterate_rangeStep, Nat.zero_add,
     List.append_nil, List.reverse_reverse, ← List.range_eq_range']


-- @@ L238-238 verbatim
attribute [fun_prop] range getD


-- @@ L240-240 verbatim
end Poly

-- @@ L241-241 verbatim
end Superstring.BitCode


-- @@ L243-243 verbatim
namespace Superstring.BitCode

 
-- @@ L245-245 verbatim
def equal {α : Type} [DecidableEq α] (a b : α) : Bool := decide (a = b)
 
-- @@ L246-246 verbatim
def less (a b : ℕ) : Bool := decide (a < b)
 
-- @@ L247-247 verbatim
def lessEq (a b : ℕ) : Bool := decide (a ≤ b)


-- @@ L249-249 verbatim
namespace Poly


-- @@ L251-252 verbatim
@[fun_prop] theorem equal {α : Type} [Coded α] [DecidableEq α] :
    Poly (fun p : α × α => Superstring.BitCode.equal p.1 p.2) := eq

-- @@ L253-253 verbatim
@[fun_prop] theorem less : Poly (fun p : ℕ × ℕ => Superstring.BitCode.less p.1 p.2) := lt

-- @@ L254-254 verbatim
@[fun_prop] theorem lessEq : Poly (fun p : ℕ × ℕ => Superstring.BitCode.lessEq p.1 p.2) := le


-- @@ L256-262 verbatim
/-- Output reinterpretation executes exactly the same bits, not a hidden function. -/
 theorem recode {α β γ : Type} [Coded α] [Coded β] [Coded γ]
    {f : α → β} {g : α → γ} (hf : Poly f) (he : ∀ a, bits (g a) = bits (f a)) : Poly g := by
   obtain ⟨K, inst, i, o, b, P, hb⟩ := hf
   refine ⟨K, inst, i, o, b, P, ?_⟩
   intro a
   simpa only [he] using hb a


-- @@ L264-265 verbatim
@[fun_prop] theorem inl {α β : Type} [Coded α] [Coded β] : Poly (Sum.inl : α → α ⊕ β) := by
   exact ((const false).pair (id : Poly (_root_.id : α → α))).recode (fun a => rfl)


-- @@ L267-268 verbatim
@[fun_prop] theorem inr {α β : Type} [Coded α] [Coded β] : Poly (Sum.inr : β → α ⊕ β) := by
   exact ((const true).pair (id : Poly (_root_.id : β → β))).recode (fun a => rfl)

 
-- @@ L270-273 verbatim
theorem headDWith {α : Type} [Coded α] : Poly (fun p : List α × α => p.1.headD p.2) := by
   convert listCasesWith (id : Poly (_root_.id : α → α))
     (fst : Poly (Prod.fst : α × (List α × α) → α)) using 1
   funext p; rcases p with ⟨xs, a⟩; cases xs <;> rfl


-- @@ L275-275 verbatim
attribute [fun_prop] headDWith


-- @@ L277-277 verbatim
end Poly

 
-- @@ L279-280 verbatim
def cappedStep {α : Type} [Coded α] (f : α → α) (p : ℕ × α) : ℕ × α :=
   (p.1, if lessEq (bitSize (f p.2)) p.1 then f p.2 else p.2)

 
-- @@ L282-290 verbatim
theorem iterate_cappedStep_size {α : Type} [Coded α] (f : α → α) (n B : ℕ) (a : α) :
     ((cappedStep f)^[n] (B, a)).1 = B ∧
     bitSize (((cappedStep f)^[n] (B, a)).2) ≤ max B (bitSize a) := by
   induction n with
   | zero => exact ⟨rfl, le_max_right _ _⟩
   | succ n ih =>
     rw [Function.iterate_succ_apply']
     simp only [cappedStep, ih.1, lessEq, decide_eq_true_eq]
     exact ⟨True.intro, by split <;> omega⟩

 
-- @@ L292-301 verbatim
theorem iterate_cappedStep_eq {α : Type} [Coded α] (f : α → α) (n B : ℕ) (a : α)
     (h : ∀ j, 1 ≤ j → j ≤ n → bitSize (f^[j] a) ≤ B) :
     (cappedStep f)^[n] (B, a) = (B, f^[n] a) := by
   induction n with
   | zero => rfl
   | succ n ih =>
     rw [Function.iterate_succ_apply', ih (fun j hj hjn => h j hj (by omega))]
     have hh := h (n + 1) (by omega) le_rfl
     rw [Function.iterate_succ_apply'] at hh ⊢
     simp only [cappedStep, lessEq, decide_eq_true_eq, ite_eq_left hh]


-- @@ L303-303 verbatim
namespace Poly

 
-- @@ L305-307 verbatim
theorem cappedStep {α : Type} [Coded α] {f : α → α} (hf : Poly f) : Poly (cappedStep f) := by
   unfold Superstring.BitCode.cappedStep
   fun_prop


-- @@ L309-320 verbatim
/-- A genuine bounded-workspace loop. The clock and workspace cap are unary
input data. Every attempted step is executed/charged before its size check. -/
 theorem cappedIterate {α : Type} [Coded α] {f : α → α} (hf : Poly f) :
     Poly (fun p : ℕ × (ℕ × α) => ((Superstring.BitCode.cappedStep f)^[p.1] p.2).2) := by
   apply snd.comp
   apply (cappedStep hf).iterate (2 * Polynomial.X)
   intro n p j _
   rcases p with ⟨B, a⟩
   have hh := iterate_cappedStep_size f j B a
   rw [← Prod.eta ((Superstring.BitCode.cappedStep f)^[j] (B, a)), bitSize_prod, hh.1]
   simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X, bitSize_prod, bitSize_nat]
   omega


-- @@ L322-322 verbatim
end Poly

 
-- @@ L324-325 verbatim
def uniqueStep {α : Type} [DecidableEq α] (a : List α) (x : α) : List α :=
   if x ∈ a then a else x :: a
 
-- @@ L326-326 verbatim
def unique {α : Type} [DecidableEq α] (xs : List α) : List α := xs.foldl uniqueStep []

 
-- @@ L328-334 verbatim
theorem mem_foldl_uniqueStep {α : Type} [DecidableEq α] (xs a : List α) (x : α) :
     x ∈ xs.foldl uniqueStep a ↔ x ∈ xs ∨ x ∈ a := by
   induction xs generalizing a with
   | nil => simp
   | cons y ys ih =>
     simp only [List.foldl_cons, ih, List.mem_cons, uniqueStep]
     by_cases hy : y ∈ a <;> simp only [hy, ite_true, ite_false, List.mem_cons] <;> aesop

 
-- @@ L336-345 verbatim
theorem nodup_foldl_uniqueStep {α : Type} [DecidableEq α] (xs a : List α) (ha : a.Nodup) :
     (xs.foldl uniqueStep a).Nodup := by
   induction xs generalizing a with
   | nil => exact ha
   | cons x xs ih =>
     apply ih
     unfold uniqueStep
     split
     · exact ha
     · exact List.nodup_cons.mpr ⟨‹_›, ha⟩


-- @@ L347-348 verbatim
@[simp] theorem mem_unique {α : Type} [DecidableEq α] (xs : List α) (x : α) :
     x ∈ unique xs ↔ x ∈ xs := by simp [unique, mem_foldl_uniqueStep]
 
-- @@ L349-350 verbatim
theorem nodup_unique {α : Type} [DecidableEq α] (xs : List α) : (unique xs).Nodup :=
   nodup_foldl_uniqueStep xs [] List.nodup_nil


-- @@ L352-352 verbatim
namespace Poly

 
-- @@ L354-368 verbatim
theorem unique {α : Type} [Coded α] [DecidableEq α] : Poly (unique : List α → List α) := by
   have hf : Poly (fun p : List α × α => uniqueStep p.1 p.2) := by
     have hp : Poly (fun p : List α × α => decide (p.2 ∈ p.1)) := mem.comp (snd.pair fst)
     simpa only [uniqueStep, decide_eq_true_eq, Function.comp_apply] using
       ite hp fst (cons.comp (snd.pair fst))
   have hs : ∀ (a : List α) (x : α), bitSize (uniqueStep a x) ≤ bitSize a +
       (Polynomial.X + 1 : Polynomial ℕ).eval (bitSize x) := by
     intro a x
     unfold uniqueStep
     simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
     split
     · omega
     · simp only [bitSize_cons]; omega
   exact (foldl_additive hf (Polynomial.X + 1) hs).comp
     ((id : Poly (_root_.id : List α → List α)).pair (const []))


-- @@ L370-370 verbatim
attribute [fun_prop] unique

 
-- @@ L372-385 verbatim
theorem product {α β : Type} [Coded α] [Coded β] :
     Poly (fun p : List α × List β => p.1.product p.2) := by
   have hi : Poly (fun q : (List α × List β) × α =>
       q.1.2.map (fun b => (q.2,b))) :=
     mapFn ((snd.comp fst).pair snd) (snd.comp fst)
   have hp : Poly (fun p : List α × List β =>
       (p.1.map (fun a => p.2.map (fun b => (a,b)))).flatten) :=
     flatten.comp (mapFn hi fst)
   convert hp using 1
   funext p
   induction p.1 with
   | nil => rfl
   | cons a as ih => simpa only [List.product, List.flatMap_cons, List.map_cons,
       List.flatten_cons] using congrArg (p.2.map (Prod.mk a) ++ ·) ih


-- @@ L387-387 verbatim
attribute [fun_prop] product


-- @@ L389-389 verbatim
end Poly

-- @@ L390-390 verbatim
end Superstring.BitCode


-- @@ L392-392 verbatim
namespace Superstring.BitCode


-- @@ L394-395 verbatim
def residueStep (q : ℕ × ℕ) : ℕ × ℕ :=
  (q.1, if equal (q.2 + 1) q.1 then 0 else q.2 + 1)


-- @@ L397-404 verbatim
theorem iterate_residueStep_bound (p r n : ℕ) :
    (residueStep^[n] (p,r)).1 = p ∧ (residueStep^[n] (p,r)).2 ≤ r + n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    simp only [residueStep, ih.1]
    exact ⟨True.intro, by split <;> omega⟩


-- @@ L406-421 verbatim
theorem iterate_residueStep (p n : ℕ) : residueStep^[n] (p,0) = (p,n % p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [residueStep, equal, decide_eq_true_eq]
    congr 1
    by_cases hp : p = 0
    · subst p; simp
    · have hp' : 0 < p := Nat.pos_of_ne_zero hp
      have hr := Nat.mod_lt n hp'
      rw [← Nat.mod_add_mod n p 1]
      by_cases he : n % p + 1 = p
      · simp [he]
      · rw [ite_eq_right he]
        exact (Nat.mod_eq_of_lt (show n % p + 1 < p by omega)).symm


-- @@ L423-423 verbatim
namespace Poly


-- @@ L425-438 verbatim
@[fun_prop] theorem mod : Poly (fun q : ℕ × ℕ => q.1 % q.2) := by
  have hs : Poly residueStep := by unfold residueStep; fun_prop
  have hi := hs.iterate (2 * Polynomial.X) (by
    intro n q j hj
    rcases q with ⟨p,r⟩
    have hh := iterate_residueStep_bound p r j
    rw [← Prod.eta (residueStep^[j] (p,r)), bitSize_prod, hh.1]
    simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_X,
      bitSize_prod, bitSize_nat]
    omega)
  have hp := snd.comp (hi.comp (fst.pair (snd.pair (const 0))))
  convert hp using 1
  funext q
  simp only [Function.comp_apply, iterate_residueStep]


-- @@ L440-440 verbatim
end Poly


-- @@ L442-444 verbatim
def intView : ℤ → ℕ ⊕ ℕ
  | .ofNat n => .inl n
  | .negSucc n => .inr n


-- @@ L446-449 verbatim
theorem Parses.precomp {α β : Type} {e : β → List Bool} (h : Parses e) (f : α → β) :
    Parses (e ∘ f) := by
  obtain ⟨K, i, b, c, hb⟩ := h
  exact ⟨K, i, b, c, fun a t z => hb (f a) t z⟩


-- @@ L451-460 verbatim
instance codedInt : Coded ℤ where
  code := bits ∘ intView
  parses := Coded.parses.precomp intView
  injective := by
    intro a b h
    have hh := Coded.injective h
    cases a <;> cases b <;> simp only [intView, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, Sum.inr_ne_inl] at hh
    · exact congrArg Int.ofNat hh
    · exact congrArg Int.negSucc hh


-- @@ L462-462 verbatim
namespace Poly

 
-- @@ L464-467 verbatim
theorem intCases {β : Type} [Coded β] {f g : ℕ → β} (hf : Poly f) (hg : Poly g) :
    Poly (fun z : ℤ => match z with | .ofNat n => f n | .negSucc n => g n) := by
  convert (sumCases hf hg).reencode intView (fun _ => rfl) using 1
  funext z; cases z <;> rfl

 
-- @@ L469-477 verbatim
theorem intCasesWith {β γ : Type} [Coded β] [Coded γ]
     {f g : ℕ × γ → β} (hf : Poly f) (hg : Poly g) :
     Poly (fun q : ℤ × γ => match q.1 with | .ofNat n => f (n,q.2) | .negSucc n => g (n,q.2)) := by
   let view : ℤ × γ → (ℕ × γ) ⊕ (ℕ × γ) := fun q => match q.1 with
     | .ofNat n => .inl (n,q.2)
     | .negSucc n => .inr (n,q.2)
   convert (sumCases hf hg).reencode view (by
     intro q; rcases q with ⟨z,c⟩; cases z <;> rfl) using 1
   funext q; rcases q with ⟨z,c⟩; cases z <;> rfl


-- @@ L479-480 verbatim
@[fun_prop] theorem ofNat : Poly (Int.ofNat : ℕ → ℤ) :=
  (inl : Poly (Sum.inl : ℕ → ℕ ⊕ ℕ)).recode (fun _ => rfl)

-- @@ L481-482 verbatim
@[fun_prop] theorem negSucc : Poly (Int.negSucc : ℕ → ℤ) :=
  (inr : Poly (Sum.inr : ℕ → ℕ ⊕ ℕ)).recode (fun _ => rfl)

-- @@ L483-483 verbatim
@[fun_prop] theorem toNat : Poly (Int.toNat : ℤ → ℕ) := intCases id (const 0)

-- @@ L484-484 verbatim
@[fun_prop] theorem natAbs : Poly (Int.natAbs : ℤ → ℕ) := intCases id succ


-- @@ L486-486 verbatim
end Poly

-- @@ L487-487 verbatim
end Superstring.BitCode


-- @@ L489-489 verbatim
namespace Superstring.BitCode.Poly


-- @@ L491-497 verbatim
@[fun_prop] theorem subNatNat : Poly (fun q : ℕ × ℕ => Int.subNatNat q.1 q.2) := by
  have h : Poly (fun q : ℕ × ℕ =>
      if BitCode.less q.1 q.2 then Int.negSucc (q.2 - q.1 - 1) else Int.ofNat (q.1 - q.2)) := by fun_prop
  convert h using 1
  funext q
  simp only [BitCode.less, decide_eq_true_eq, Int.subNatNat_eq_coe, Int.ofNat_eq_natCast]
  split <;> omega


-- @@ L499-502 verbatim
@[fun_prop] theorem negInt : Poly (fun z : ℤ => -z) := by
  have hf : Poly (fun n : ℕ => Int.subNatNat 0 n) := by fun_prop
  convert intCases hf (ofNat.comp succ) using 1
  funext z; cases z <;> simp [Int.subNatNat_eq_coe]


-- @@ L504-519 verbatim
@[fun_prop] theorem addInt : Poly (fun q : ℤ × ℤ => q.1 + q.2) := by
  have hf : Poly (fun q : ℤ × ℕ => match q.1 with
      | .ofNat n => Int.ofNat (q.2 + n)
      | .negSucc n => Int.subNatNat q.2 (n+1)) := by
    exact intCasesWith
      (show Poly (fun q : ℕ × ℕ => Int.ofNat (q.2 + q.1)) by fun_prop)
      (show Poly (fun q : ℕ × ℕ => Int.subNatNat q.2 (q.1+1)) by fun_prop)
  have hg : Poly (fun q : ℤ × ℕ => match q.1 with
      | .ofNat n => Int.subNatNat n (q.2+1)
      | .negSucc n => Int.negSucc (q.2+n+1)) := by
    exact intCasesWith
      (show Poly (fun q : ℕ × ℕ => Int.subNatNat q.1 (q.2+1)) by fun_prop)
      (show Poly (fun q : ℕ × ℕ => Int.negSucc (q.2+q.1+1)) by fun_prop)
  have hh := intCasesWith (hf.comp (snd.pair fst)) (hg.comp (snd.pair fst))
  convert hh using 1
  funext q; rcases q with ⟨a,b⟩; cases a <;> cases b <;> rfl


-- @@ L521-524 verbatim
@[fun_prop] theorem subInt : Poly (fun q : ℤ × ℤ => q.1 - q.2) := by
  convert addInt.comp (fst.pair (negInt.comp snd)) using 1
  funext q
  exact sub_eq_add_neg q.1 q.2


-- @@ L526-532 verbatim
@[fun_prop] theorem modIntNat : Poly (fun q : ℤ × ℕ => (q.1 % (q.2 : ℤ)).toNat) := by
  have hf : Poly (fun q : ℕ × ℕ => q.1 % q.2) := mod
  have hg : Poly (fun q : ℕ × ℕ => q.2 - (q.1 % q.2 + 1)) := by fun_prop
  convert intCasesWith hf hg using 1
  funext q; rcases q with ⟨a,b⟩; cases a with
  | ofNat n => rfl
  | negSucc n => simp only [Int.negSucc_emod_ofNat, Int.subNatNat_eq_coe, Int.toNat_sub]


-- @@ L534-534 verbatim
end Superstring.BitCode.Poly


-- @@ L536-536 verbatim
namespace Superstring.BitCode.Poly

-- @@ L537-537 verbatim
@[fun_prop] theorem natCastInt : Poly (fun n : ℕ => (n : ℤ)) := ofNat

-- @@ L538-538 verbatim
end Superstring.BitCode.Poly


-- @@ L540-540 verbatim
namespace Superstring.BitCode

-- @@ L541-543 verbatim
/-- Freeze the equality implementation at the abstract element type. Nested
lists may otherwise elaborate different, extensionally equal BEq instances. -/
def member {α : Type} [DecidableEq α] (a : α) (xs : List α) : Bool := decide (a ∈ xs)

-- @@ L544-545 verbatim
@[simp] theorem member_eq {α : Type} [DecidableEq α] (a : α) (xs : List α) :
    member a xs = true ↔ a ∈ xs := decide_eq_true_iff

-- @@ L546-546 verbatim
namespace Poly

-- @@ L547-548 verbatim
@[fun_prop] theorem member {α : Type} [Coded α] [DecidableEq α] :
    Poly (fun q : α × List α => BitCode.member q.1 q.2) := mem

-- @@ L549-549 verbatim
end Poly

-- @@ L550-550 verbatim
end Superstring.BitCode


-- @@ L552-552 verbatim
end OAI
