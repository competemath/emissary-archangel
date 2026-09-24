module

public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Cases
public import Mathlib.Tactic.TautoSet



-- @@ L9-12 verbatim
@[expose]
public section

lemma eq_finZeroElim {α : Sort u} (x : Fin 0 → α) : x = finZeroElim := funext (by rintro ⟨_, _⟩; contradiction)



-- @@ L15-16 verbatim
@[simp, grind .]
lemma Nat.sub_one_lt' [NeZero n] : n - 1 < n := sub_one_lt $ NeZero.ne n



-- @@ L19-19 verbatim
namespace Fin


-- @@ L21-25 verbatim
variable {n : ℕ} {i : Fin n}

lemma isEmpty_embedding_lt (hn : n > m) : IsEmpty (Fin n ↪ Fin m) := by
  apply Function.Embedding.isEmpty_of_card_lt;
  simpa;


-- @@ L27-31 verbatim
@[simp, grind .]
lemma lt_last : n < Fin.last (n + 1) := by
  induction n with
  | zero => simp;
  | succ n ih => simp;


-- @@ L33-36 verbatim
@[grind <=]
lemma lt_sub_one_of_pos {a : Fin n} (hn : 0 < n) : a ≤ ⟨n - 1, by omega⟩ := by
  apply Nat.le_sub_one_of_lt;
  omega;



-- @@ L39-39 verbatim
section last'


-- @@ L41-41 verbatim
variable [NeZero n]


-- @@ L43-44 verbatim
/-- The last element of `Fin n` when `n` is `NeZero`. -/
def last' : Fin n := ⟨n - 1, Nat.sub_one_lt'⟩


-- @@ L46-49 verbatim
@[simp, grind .]
lemma lt_last' : i ≤ Fin.last' := by
  apply Nat.le_sub_one_of_lt;
  apply Fin.is_lt;


-- @@ L51-51 verbatim
end last'



-- @@ L54-56 verbatim
section

lemma pos_of_coe_ne_zero {i : Fin (n + 1)} (h : (i : ℕ) ≠ 0) : 0 < i := Nat.pos_of_ne_zero h


-- @@ L58-58 verbatim
@[simp] lemma one_pos'' : (0 : Fin (n + 2)) < 1 := pos_of_coe_ne_zero (Nat.succ_ne_zero 0)


-- @@ L60-60 verbatim
@[simp] lemma two_pos : (0 : Fin (n + 3)) < 2 := pos_of_coe_ne_zero (Nat.succ_ne_zero 1)


-- @@ L62-62 verbatim
@[simp] lemma three_pos : (0 : Fin (n + 4)) < 3 := pos_of_coe_ne_zero (Nat.succ_ne_zero 2)


-- @@ L64-64 verbatim
@[simp] lemma four_pos : (0 : Fin (n + 5)) < 4 := pos_of_coe_ne_zero (Nat.succ_ne_zero 3)


-- @@ L66-66 verbatim
@[simp] lemma five_pos : (0 : Fin (n + 6)) < 5 := pos_of_coe_ne_zero (Nat.succ_ne_zero 4)


-- @@ L68-95 verbatim
end


lemma forall_fin_iff_zero_and_forall_succ {P : Fin (k + 1) → Prop} : (∀ i, P i) ↔ P 0 ∧ ∀ i : Fin k, P i.succ :=
  ⟨fun h ↦ ⟨h 0, fun i ↦ h i.succ⟩, by
    rintro ⟨hz, hs⟩ i
    cases' i using Fin.cases with i
    · exact hz
    · exact hs i⟩

lemma exists_fin_iff_zero_or_exists_succ {P : Fin (k + 1) → Prop} : (∃ i, P i) ↔ P 0 ∨ ∃ i : Fin k, P i.succ :=
  ⟨by rintro ⟨i, hi⟩
      cases i using Fin.cases
      · left; exact hi
      · right; exact ⟨_, hi⟩,
   by rintro (hz | ⟨i, h⟩)
      · exact ⟨0, hz⟩
      · exact ⟨_, h⟩⟩

lemma funext_two {α : Type*} {f g : Fin (k + 2) → α}
    (h0 : f 0 = g 0) (h1 : f (Fin.succ 0) = g (Fin.succ 0))
    (hs : ∀ i : Fin k, f i.succ.succ = g i.succ.succ) : f = g := by
  funext i
  cases' i using Fin.cases with i
  . exact h0
  . cases' i using Fin.cases with i
    . exact h1
    . exact hs i




-- @@ L99-99 verbatim
@[inline] def addCast (m) : Fin n → Fin (m + n) := castLE <| Nat.le_add_left n m


-- @@ L101-101 verbatim
@[simp] lemma addCast_val (i : Fin n) : (i.addCast m : ℕ) = i := rfl



-- @@ L104-104 verbatim
namespace Fin1


-- @@ L106-109 verbatim
variable {n : Fin 1}

-- `n` is intentionally kept as a global simp lemma (every `Fin 1` element is `0`);
-- scoping it would break implicit uses elsewhere.

-- @@ L110-111 verbatim
set_option warning.simp.varHead false in
@[simp] lemma eq_one : n = 0 := by cases n; omega;

-- @@ L112-112 verbatim
@[simp] lemma not_lt_zero : ¬0 < n := by simp [eq_one];


-- @@ L114-114 verbatim
end Fin1



-- @@ L117-117 verbatim
end Fin


-- @@ L119-119 verbatim
end
