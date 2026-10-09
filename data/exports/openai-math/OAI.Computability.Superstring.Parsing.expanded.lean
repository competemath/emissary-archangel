import OAI.Computability.Superstring.PolynomialTime


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
namespace Superstring.BitCode


-- @@ L7-8 verbatim
/-- A pair of public bit-stack ports and a private register bank. -/
abbrev Ports (K : Type) := Bool ⊕ K


-- @@ L10-10 verbatim
def inputPort {K : Type} : Ports K := .inl false

-- @@ L11-11 verbatim
def outputPort {K : Type} : Ports K := .inl true


-- @@ L13-14 verbatim
def portStore {K : Type} (x y : List Bool) (z : Store K) : Store (Ports K) :=
  Sum.elim (fun b => if b then y else x) z


-- @@ L16-16 verbatim
def pairStore {K : Type} (x y : List Bool) : Store (Ports K) := portStore x y (fun _ => [])


-- @@ L18-19 verbatim
@[simp] theorem portStore_input {K : Type} (x y : List Bool) (z : Store K) :
    portStore x y z inputPort = x := rfl

-- @@ L20-21 verbatim
@[simp] theorem portStore_output {K : Type} (x y : List Bool) (z : Store K) :
    portStore x y z outputPort = y := rfl

-- @@ L22-23 verbatim
@[simp] theorem portStore_private {K : Type} (x y : List Bool) (z : Store K) (k : K) :
    portStore x y z (.inr k) = z k := rfl


-- @@ L25-30 verbatim
@[simp] theorem update_input {K : Type} [DecidableEq K] (x y w : List Bool) (z : Store K) :
    Function.update (portStore x y z) inputPort w = portStore w y z := by
  funext k
  cases k with
  | inl b => cases b <;> simp [inputPort, portStore]
  | inr k => simp [inputPort, portStore]


-- @@ L32-37 verbatim
@[simp] theorem update_output {K : Type} [DecidableEq K] (x y w : List Bool) (z : Store K) :
    Function.update (portStore x y z) outputPort w = portStore x w z := by
  funext k
  cases k with
  | inl b => cases b <;> simp [outputPort, portStore]
  | inr k => simp [outputPort, portStore]


-- @@ L39-41 verbatim
@[simp] theorem update_private {K : Type} [DecidableEq K] (x y w : List Bool) (z : Store K) (j : K) :
    Function.update (portStore x y z) (.inr j) w = portStore x y (Function.update z j w) :=
  Block.update_right _ _ _ _


-- @@ L43-43 verbatim
namespace Block


-- @@ L45-48 verbatim
/-- Move exactly one bit, leaving the suffix and the old output accumulator in
place. Empty input is a no-op, but valid parser calls always supply the bit. -/
def readBit {K : Type} (i o : K) : Block K := .branch i .skip
  (.seq (.pop i) (.push o false)) (.seq (.pop i) (.push o true))


-- @@ L50-61 verbatim
theorem readBit_exec {K : Type} [DecidableEq K] (x : Bool) (xs ys : List Bool)
    (z : Store K) :
    (readBit inputPort outputPort).Exec (portStore (x :: xs) ys z)
      (portStore xs (x :: ys) z) 3 := by
  have hpop : Exec (.pop inputPort) (portStore (x :: xs) ys z) (portStore xs ys z) 1 := by
    simpa only [portStore_input, List.tail_cons, update_input] using
      Exec.pop inputPort (portStore (x :: xs) ys z)
  have hpush : Exec (.push outputPort x) (portStore xs ys z) (portStore xs (x :: ys) z) 1 := by
    simpa only [portStore_output, update_output] using Exec.push outputPort x (portStore xs ys z)
  cases x with
  | false => exact .branch_false rfl (.seq hpop hpush)
  | true => exact .branch_true rfl (.seq hpop hpush)


-- @@ L63-82 verbatim
/-- Lift a two-port clean routine while leaving an arbitrary disjoint private
bank untouched. Public input/output ports are deliberately shared. -/
theorem Exec.ports {K L : Type} [DecidableEq K] [DecidableEq L]
    {b : Block (Ports K)} {x y x' y' : List Bool} {n : ℕ}
    (h : b.Exec (pairStore x y) (pairStore x' y') n)
    (f : K → L) (hf : Function.Injective f) (z : Store L) (hz : ∀ k, z (f k) = []) :
    (b.rename (Sum.map id f)).Exec (portStore x y z) (portStore x' y' z) n := by
  apply h.transport (Sum.map id f) (Sum.map_injective.mpr ⟨Function.injective_id, hf⟩)
  · intro k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => exact hz k
  · intro k
    cases k with
    | inl k => cases k <;> rfl
    | inr k => exact hz k
  · intro k hk
    cases k with
    | inl k => exact False.elim (hk (.inl k) rfl)
    | inr k => rfl


-- @@ L84-84 verbatim
end Block


-- @@ L86-92 verbatim
/-- A linear-time prefix scanner for an explicit encoding. It consumes exactly
one encoded value, pushes its reversal onto an accumulator, and restores every
private stack to empty, independently of the untouched input suffix. -/
def Parses {α : Type} (e : α → List Bool) : Prop :=
  ∃ (K : Type) (_ : DecidableEq K) (b : Block (Ports K)) (c : ℕ),
    ∀ a tail acc, ∃ n ≤ c * ((e a).length + 1),
      b.Exec (pairStore (e a ++ tail) acc) (pairStore tail ((e a).reverse ++ acc)) n


-- @@ L94-94 verbatim
namespace Parses


-- @@ L96-101 verbatim
theorem bit : Parses (fun b : Bool => [b]) := by
  refine ⟨Unit, inferInstance, Block.readBit inputPort outputPort, 3, ?_⟩
  intro b tail acc
  refine ⟨3, by simp, ?_⟩
  simpa only [List.singleton_append, List.reverse_singleton, pairStore] using
    Block.readBit_exec b tail acc (fun _ : Unit => [])


-- @@ L103-120 verbatim
/-- A fixed code word is a prefix encoding of a unit value. -/
theorem const (w : List Bool) : Parses (fun _ : Unit => w) := by
  induction w with
  | nil =>
    refine ⟨Unit, inferInstance, .skip, 1, ?_⟩
    intro a tail acc
    exact ⟨1, by simp, by simpa only [List.nil_append, List.reverse_nil] using Block.Exec.skip (pairStore tail acc)⟩
  | cons x xs ih =>
    obtain ⟨K, inst, b, c, hb⟩ := ih
    refine ⟨K, inst, .seq (Block.readBit inputPort outputPort) b, c + 3, ?_⟩
    intro a tail acc
    obtain ⟨n, hn, hh⟩ := hb a tail (x :: acc)
    refine ⟨3 + n, ?_, ?_⟩
    · simp only [List.length_cons]
      nlinarith
    · simpa only [List.cons_append, List.reverse_cons, List.append_assoc, List.singleton_append,
        List.nil_append, pairStore] using
        Block.Exec.seq (Block.readBit_exec x (xs ++ tail) acc (fun _ : K => [])) hh


-- @@ L122-139 verbatim
/-- Consecutive self-delimiting values can be parsed in succession without
scanning or copying the remaining suffix. -/
theorem prod {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    (ha : Parses ea) (hb : Parses eb) : Parses (fun p : α × β => ea p.1 ++ eb p.2) := by
  obtain ⟨K, instK, b, c, hparse⟩ := ha
  obtain ⟨L, instL, d, e, hd⟩ := hb
  let code : Block (Ports (K ⊕ L)) := .seq (b.rename (Sum.map id Sum.inl))
    (d.rename (Sum.map id Sum.inr))
  refine ⟨K ⊕ L, inferInstance, code, c + e, ?_⟩
  intro p tail acc
  obtain ⟨n, hn, h₁⟩ := hparse p.1 (eb p.2 ++ tail) acc
  obtain ⟨m, hm, h₂⟩ := hd p.2 tail ((ea p.1).reverse ++ acc)
  have h₁' := h₁.ports (Sum.inl : K → K ⊕ L) Sum.inl_injective (fun _ => []) (fun _ => rfl)
  have h₂' := h₂.ports (Sum.inr : L → K ⊕ L) Sum.inr_injective (fun _ => []) (fun _ => rfl)
  refine ⟨n + m, ?_, ?_⟩
  · simp only [List.length_append]
    nlinarith
  · simpa only [List.append_assoc, List.reverse_append, pairStore, code] using Block.Exec.seq h₁' h₂'


-- @@ L141-141 verbatim
end Parses


-- @@ L143-143 verbatim
end Superstring.BitCode


-- @@ L145-145 verbatim
namespace Superstring.BitCode



-- @@ L148-150 verbatim
def listCode {α : Type} (e : α → List Bool) : List α → List Bool
  | [] => [true]
  | x :: xs => false :: (e x ++ listCode e xs)


-- @@ L152-152 verbatim
namespace Parses


-- @@ L154-218 verbatim
/-- Lists of a linearly parsable self-delimiting type are themselves linearly
parsable. Exactly one fixed-size private flag is added, not an infinite alphabet
or uncharged whole-value operation. -/
theorem list {α : Type} {e : α → List Bool} (hp : Parses e) : Parses (listCode e) := by
  obtain ⟨K, instK, b, c, hb⟩ := hp
  let flag : Ports (K ⊕ Unit) := .inr (.inr ())
  let z : Store (K ⊕ Unit) := single (.inr ()) [true]
  let inner : Block (Ports (K ⊕ Unit)) := b.rename (Sum.map id Sum.inl)
  let step : Block (Ports (K ⊕ Unit)) := .branch inputPort
    (.pop flag)
    (.seq (Block.readBit inputPort outputPort) inner)
    (.seq (Block.readBit inputPort outputPort) (.pop flag))
  let loop : Block (Ports (K ⊕ Unit)) := .loop flag step
  let code : Block (Ports (K ⊕ Unit)) := .seq (.push flag true) loop
  have hz : z (.inr ()) = [true] := by simp [z, single]
  have hzleft : ∀ k : K, z (.inl k) = [] := by intro k; simp [z, single]
  have hzend : Function.update z (.inr ()) [] = fun _ => [] := by
    funext k
    by_cases hk : k = Sum.inr () <;> simp [z, single, hk]
  have hloop (xs : List α) (tail acc : List Bool) :
      ∃ n ≤ (c + 7) * (listCode e xs).length,
        loop.Exec (portStore (listCode e xs ++ tail) acc z)
          (pairStore tail ((listCode e xs).reverse ++ acc)) n := by
    induction xs generalizing acc with
    | nil =>
      have hread := Block.readBit_exec true tail acc z
      have hpop : Block.Exec (.pop flag) (portStore tail (true :: acc) z)
          (pairStore tail (true :: acc)) 1 := by
        simpa only [flag, portStore_private, hz, List.tail_cons, update_private,
          hzend, pairStore] using Block.Exec.pop flag (portStore tail (true :: acc) z)
      have hbody : step.Exec (portStore (true :: tail) acc z)
          (pairStore tail (true :: acc)) (3 + 1 + 1) :=
        Block.Exec.branch_true rfl (Block.Exec.seq hread hpop)
      have hend : loop.Exec (pairStore tail (true :: acc)) (pairStore tail (true :: acc)) 1 :=
        Block.Exec.loop_nil rfl
      have hh := Block.Exec.loop_cons (by simp [flag, hz]) hbody hend
      refine ⟨7, ?_, ?_⟩
      · simp [listCode]
      · simpa only [listCode, List.singleton_append, List.reverse_singleton] using hh
    | cons x xs ih =>
      obtain ⟨n, hn, hinner⟩ := hb x (listCode e xs ++ tail) (false :: acc)
      have hin := hinner.ports (Sum.inl : K → K ⊕ Unit) Sum.inl_injective z hzleft
      obtain ⟨m, hm, hrest⟩ := ih ((e x).reverse ++ false :: acc)
      have hread := Block.readBit_exec false (e x ++ (listCode e xs ++ tail)) acc z
      have hbody : step.Exec (portStore (false :: (e x ++ (listCode e xs ++ tail))) acc z)
          (portStore (listCode e xs ++ tail) ((e x).reverse ++ false :: acc) z) (3 + n + 1) :=
        Block.Exec.branch_false rfl (Block.Exec.seq hread hin)
      have hh := Block.Exec.loop_cons (by simp [flag, hz]) hbody hrest
      refine ⟨3 + n + 1 + m + 1, ?_, ?_⟩
      · simp only [listCode, List.length_cons, List.length_append]
        nlinarith
      · simpa only [listCode, List.cons_append, List.append_assoc, List.reverse_cons,
          List.reverse_append, List.singleton_append, List.nil_append] using hh
  refine ⟨K ⊕ Unit, inferInstance, code, c + 8, ?_⟩
  intro xs tail acc
  obtain ⟨n, hn, hh⟩ := hloop xs tail acc
  have hstart : Block.Exec (.push flag true) (pairStore (listCode e xs ++ tail) acc)
      (portStore (listCode e xs ++ tail) acc z) 1 := by
    have he : Function.update (fun _ : K ⊕ Unit => ([] : List Bool)) (.inr ()) [true] = z := by
      funext k
      by_cases hk : k = Sum.inr () <;> simp [z, single, hk]
    simpa only [pairStore, flag, portStore_private, update_private, he] using
      Block.Exec.push flag true (pairStore (listCode e xs ++ tail) acc)
  refine ⟨1 + n, ?_, Block.Exec.seq hstart hh⟩
  nlinarith


-- @@ L220-220 verbatim
end Parses


-- @@ L222-222 verbatim
end Superstring.BitCode


-- @@ L224-224 verbatim
namespace Superstring.BitCode


-- @@ L226-231 verbatim
@[simp] theorem pairStore_input {K : Type} [DecidableEq K] (w : List Bool) :
    (pairStore w [] : Store (Ports K)) = single inputPort w := by
  funext k
  cases k with
  | inl b => cases b <;> simp [pairStore, portStore, single, inputPort]
  | inr k => simp [pairStore, portStore, single, inputPort]


-- @@ L233-238 verbatim
@[simp] theorem pairStore_output {K : Type} [DecidableEq K] (w : List Bool) :
    (pairStore [] w : Store (Ports K)) = single outputPort w := by
  funext k
  cases k with
  | inl b => cases b <;> simp [pairStore, portStore, single, outputPort]
  | inr k => simp [pairStore, portStore, single, outputPort]


-- @@ L240-240 verbatim
namespace Block


-- @@ L242-245 verbatim
/-- Write a fixed finite bit word, in the correct order. -/
def pushWord {K : Type} (i : K) : List Bool → Block K
  | [] => .skip
  | b :: bs => .seq (pushWord i bs) (.push i b)


-- @@ L247-254 verbatim
theorem pushWord_exec {K : Type} [DecidableEq K] (i : K) (w : List Bool) (s : Store K) :
    (pushWord i w).Exec s (Function.update s i (w ++ s i)) (w.length + 1) := by
  induction w with
  | nil => simpa only [pushWord, List.nil_append, List.length_nil, Function.update_eq_self] using Exec.skip s
  | cons x xs ih =>
    have hh := Exec.seq ih (Exec.push i x (Function.update s i (xs ++ s i)))
    simpa only [Function.update_self, Function.update_idem, List.cons_append,
      pushWord, List.length_cons, Nat.add_assoc] using hh


-- @@ L256-256 verbatim
end Block


-- @@ L258-258 verbatim
namespace RunsInPolyTime


-- @@ L260-278 verbatim
theorem const {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (b : β) :
    RunsInPolyTime ea eb (fun _ => b) := by
  let code : Block Unit := .seq (Block.clear ()) (Block.pushWord () (eb b))
  refine ⟨Unit, inferInstance, (), (), code,
    2 * Polynomial.X + Polynomial.C ((eb b).length + 2), ?_⟩
  intro a
  have h₁ := Block.clear_exec () (single () (ea a))
  have h₂ := Block.pushWord_exec () (eb b) (Function.update (single () (ea a)) () [])
  have he : Function.update (Function.update (single () (ea a)) () []) () (eb b) =
      single () (eb b) := by funext k; cases k; simp [single]
  simp only [Function.update_self, List.append_nil] at h₂
  rw [he] at h₂
  have hh := Block.Exec.seq h₁ h₂
  have hlen : (single () (ea a) ()).length = (ea a).length := by simp [single]
  rw [hlen] at hh
  refine ⟨2 * (ea a).length + 1 + ((eb b).length + 1), ?_, hh⟩
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_C]
  omega


-- @@ L280-287 verbatim
theorem reverseEncoding {α : Type} (e : α → List Bool) :
    RunsInPolyTime (fun a => (e a).reverse) e _root_.id := by
  refine ⟨Bool, inferInstance, false, true, Block.transfer false true,
    4 * Polynomial.X + 1, ?_⟩
  intro a
  refine ⟨4 * (e a).length + 1, by simp, ?_⟩
  simpa only [List.length_reverse, List.reverse_reverse, _root_.id] using
    Block.transfer_single false true Bool.false_ne_true (e a).reverse


-- @@ L289-303 verbatim
/-- First projection from two consecutive self-delimiting values. -/
theorem fst {α β : Type} {ea : α → List Bool} (eb : β → List Bool) (hp : Parses ea) :
    RunsInPolyTime (fun p : α × β => ea p.1 ++ eb p.2) ea Prod.fst := by
  obtain ⟨K, inst, b, c, hb⟩ := hp
  have hrev : RunsInPolyTime (fun p : α × β => ea p.1 ++ eb p.2)
      (fun a => (ea a).reverse) Prod.fst := by
    apply of_observed b inputPort outputPort (Polynomial.C c * (Polynomial.X + 1))
    intro p
    obtain ⟨n, hn, hh⟩ := hb p.1 (eb p.2) []
    simp only [pairStore_input, List.append_nil] at hh
    refine ⟨n, pairStore (eb p.2) (ea p.1).reverse, ?_, hh, rfl⟩
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
      Polynomial.eval_X, Polynomial.eval_one, List.length_append]
    exact hn.trans (Nat.mul_le_mul_left _ (by omega))
  exact (reverseEncoding ea).comp hrev


-- @@ L305-317 verbatim
/-- Second projection consumes just the first value; it does not copy or
re-parse the tail. Accumulated garbage is explicitly erased by of_observed. -/
theorem snd {α β : Type} {ea : α → List Bool} (eb : β → List Bool) (hp : Parses ea) :
    RunsInPolyTime (fun p : α × β => ea p.1 ++ eb p.2) eb Prod.snd := by
  obtain ⟨K, inst, b, c, hb⟩ := hp
  apply of_observed b inputPort inputPort (Polynomial.C c * (Polynomial.X + 1))
  intro p
  obtain ⟨n, hn, hh⟩ := hb p.1 (eb p.2) []
  simp only [pairStore_input, List.append_nil] at hh
  refine ⟨n, pairStore (eb p.2) (ea p.1).reverse, ?_, hh, rfl⟩
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_one, List.length_append]
  exact hn.trans (Nat.mul_le_mul_left _ (by omega))


-- @@ L319-329 verbatim
theorem cons {α : Type} (e : α → List Bool) :
    RunsInPolyTime (fun p : α × List α => e p.1 ++ listCode e p.2)
      (listCode e) (fun p => p.1 :: p.2) := by
  refine ⟨Unit, inferInstance, (), (), .push () false, 1, ?_⟩
  intro p
  refine ⟨1, by simp, ?_⟩
  have he : Function.update (single () (e p.1 ++ listCode e p.2)) ()
      (false :: (e p.1 ++ listCode e p.2)) = single () (listCode e (p.1 :: p.2)) := by
    funext k; cases k; simp [single, listCode]
  simpa only [single, ↓reduceIte, he] using
    Block.Exec.push () false (single () (e p.1 ++ listCode e p.2))


-- @@ L331-331 verbatim
end RunsInPolyTime


-- @@ L333-333 verbatim
end Superstring.BitCode


-- @@ L335-335 verbatim
namespace Superstring.BitCode.Block


-- @@ L337-337 verbatim
variable {K : Type} [DecidableEq K]


-- @@ L339-361 verbatim
/-- Destructive linear concatenation, preserving every unrelated register. -/
theorem move_exec (i j scratch : K) (hij : i ≠ j) (hit : i ≠ scratch) (hjt : j ≠ scratch)
    (s : Store K) (ht : s scratch = []) :
    (move i j scratch).Exec s
      (Function.update (Function.update s i []) j (s i ++ s j)) (8 * (s i).length + 2) := by
  let t := Function.update (Function.update s i []) scratch (s i).reverse
  have h₁ := transfer_exec i scratch hit s
  rw [ht, List.append_nil] at h₁
  have h₂ := transfer_exec scratch j hjt.symm t
  have htt : t scratch = (s i).reverse := by simp [t]
  have htj : t j = s j := by simp [t, hjt, hij.symm]
  rw [htt, htj, List.reverse_reverse, List.length_reverse] at h₂
  have he : Function.update (Function.update t scratch []) j (s i ++ s j) =
      Function.update (Function.update s i []) j (s i ++ s j) := by
    funext k
    by_cases hkj : k = j
    · subst k; simp
    · by_cases hkt : k = scratch
      · subst k; simp [hjt.symm, hit.symm, ht]
      · simp [t, hkj, hkt]
  rw [he] at h₂
  have hh := Exec.seq h₁ h₂
  convert hh using 1 <;> first | rfl | omega


-- @@ L363-363 verbatim
end Superstring.BitCode.Block


-- @@ L365-365 verbatim
end OAI
