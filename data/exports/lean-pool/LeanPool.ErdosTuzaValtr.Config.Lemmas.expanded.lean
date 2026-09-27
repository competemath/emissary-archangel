/-
Copyright (c) 2026 Jineon Baek. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jineon Baek
-/
module

public import LeanPool.ErdosTuzaValtr.Config.Defs
import LeanPool.ErdosTuzaValtr.Lib.List.Chain3
import LeanPool.ErdosTuzaValtr.Lib.List.Lemmas
import Mathlib.Data.List.Chain
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow


-- @@ L18-22 verbatim
/-!
# LeanPool.ErdosTuzaValtr.Config.Lemmas

Imported Lean Pool material for `LeanPool.ErdosTuzaValtr.Config.Lemmas`.
-/


-- @@ L24-24 verbatim
@[expose] public section



-- @@ L27-27 verbatim
variable {α : Type _} [LinearOrder α] {C : Config α}


-- @@ L29-29 verbatim
namespace Config


-- @@ L31-31 verbatim
namespace Cap


-- @@ L33-34 verbatim
@[simp]
protected theorem nil : C.Cap [] := by rw [Config.Cap]; tauto


-- @@ L36-37 verbatim
@[simp]
protected theorem singleton (a : α) : C.Cap [a] := by rw [Config.Cap]; simp


-- @@ L39-40 verbatim
@[simp]
protected theorem pair {a b : α} : C.Cap [a, b] ↔ a < b := by rw [Config.Cap]; simp


-- @@ L42-46 verbatim
@[simp]
protected theorem cons3 {a b c : α} {l : List α} :
    C.Cap (a::b::c::l) ↔ a < b ∧ C.Cap3 a b c ∧ C.Cap (b::c::l) := by
  simp only [Config.Cap, List.isChain_cons_cons, List.chain3'_cons]
  tauto


-- @@ L48-53 verbatim
@[simp]
protected theorem append_cons3 {a b c : α} {l1 l2 : List α} :
    C.Cap (l1 ++ a::b::c::l2) ↔ C.Cap (l1 ++ [a, b]) ∧ C.Cap3 a b c ∧ C.Cap (b::c::l2) := by
  simp only [Config.Cap, List.chain3'_append_cons3, List.isChain_append_cons_cons,
    List.isChain_cons_cons]
  tauto


-- @@ L55-56 verbatim
protected theorem dropLast {l : List α} (h : C.Cap l) : C.Cap l.dropLast :=
  ⟨h.left.dropLast, h.right.dropLast⟩


-- @@ L58-59 verbatim
protected theorem tail {l : List α} (h : C.Cap l) : C.Cap l.tail :=
  ⟨h.left.tail, h.right.tail⟩


-- @@ L61-61 verbatim
end Cap


-- @@ L63-63 verbatim
namespace NCap


-- @@ L65-66 verbatim
protected theorem dropLast {n : ℕ} {l : List α} (h : C.NCap (n + 1) l) : C.NCap n l.dropLast :=
  ⟨h.1.dropLast, by rw [List.length_dropLast, h.2, Nat.add_sub_cancel]⟩


-- @@ L68-69 verbatim
protected theorem tail {n : ℕ} {l : List α} (h : C.NCap (n + 1) l) : C.NCap n l.tail :=
  ⟨h.1.tail, by rw [List.length_tail, h.2, Nat.add_sub_cancel]⟩


-- @@ L71-71 verbatim
end NCap


-- @@ L73-73 verbatim
namespace Cup


-- @@ L75-76 verbatim
@[simp]
protected theorem nil : C.Cup [] := by rw [Config.Cup]; tauto


-- @@ L78-79 verbatim
@[simp]
protected theorem singleton (a : α) : C.Cup [a] := by rw [Config.Cup]; simp


-- @@ L81-82 verbatim
@[simp]
protected theorem pair {a b : α} : C.Cup [a, b] ↔ a < b := by rw [Config.Cup]; simp


-- @@ L84-88 verbatim
@[simp]
protected theorem cons3 {a b c : α} {l : List α} :
    C.Cup (a::b::c::l) ↔ a < b ∧ C.Cup3 a b c ∧ C.Cup (b::c::l) := by
  simp only [Config.Cup, List.isChain_cons_cons, List.chain3'_cons]
  tauto


-- @@ L90-95 verbatim
@[simp]
protected theorem append_cons3 {a b c : α} {l1 l2 : List α} :
    C.Cup (l1 ++ a::b::c::l2) ↔ C.Cup (l1 ++ [a, b]) ∧ C.Cup3 a b c ∧ C.Cup (b::c::l2) := by
  simp only [Config.Cup, List.chain3'_append_cons3, List.isChain_append_cons_cons,
    List.isChain_cons_cons]
  tauto


-- @@ L97-98 verbatim
protected theorem dropLast {l : List α} (h : C.Cup l) : C.Cup l.dropLast :=
  ⟨h.left.dropLast, h.right.dropLast⟩


-- @@ L100-101 verbatim
protected theorem take {l : List α} (h : C.Cup l) (n : ℕ) : C.Cup (l.take n) :=
  ⟨h.left.take n, h.right.take n⟩


-- @@ L103-104 verbatim
protected theorem drop {l : List α} (h : C.Cup l) (n : ℕ) : C.Cup (l.drop n) :=
  ⟨h.left.drop n, h.right.drop n⟩


-- @@ L106-107 verbatim
protected theorem tail {l : List α} (h : C.Cup l) : C.Cup l.tail :=
  ⟨h.left.tail, h.right.tail⟩


-- @@ L109-122 verbatim
theorem head_lt_getLast {l : List α} (l_cup : C.Cup l) (p q : α) (hl : 2 ≤ l.length)
    (hp : p ∈ l.head?) (hq : q ∈ l.getLast?) : p < q := by
  cases l with
  | nil => exact absurd hp (Option.not_mem_none p)
  | cons x l =>
    rw [List.head?_cons, Option.mem_some_iff] at hp
    subst hp
    have l_nnil : l ≠ [] := by
      rintro rfl
      simp_all
    rcases List.takeLast l_nnil with ⟨q', l', eq_l⟩
    rw [eq_l, ← List.cons_append, List.getLast?_concat, Option.mem_some_iff] at hq
    have l_sorted := List.isChain_iff_pairwise.mp l_cup.left
    simp_all


-- @@ L124-126 verbatim
/-- Compatibility alias for the upstream theorem name. -/
theorem «head?_lt_getLast?» {l : List α} (l_cup : C.Cup l) (p q : α) (hl : 2 ≤ l.length)
    (hp : p ∈ l.head?) (hq : q ∈ l.getLast?) : p < q := head_lt_getLast l_cup p q hl hp hq


-- @@ L128-128 verbatim
end Cup


-- @@ L130-130 verbatim
namespace NCup


-- @@ L132-133 verbatim
@[simp]
protected theorem nil : C.NCup 0 [] := by rw [Config.NCup, Config.Cup]; tauto


-- @@ L135-136 verbatim
@[simp]
protected theorem singleton (a : α) : C.NCup 1 [a] := by rw [Config.NCup, Config.Cup]; simp


-- @@ L138-140 verbatim
@[simp]
protected theorem pair {a b : α} : C.NCup 2 [a, b] ↔ a < b := by
  rw [Config.NCup, Config.Cup]; simp


-- @@ L142-146 verbatim
@[simp]
protected theorem cons3 {n : ℕ} {a b c : α} {l : List α} :
    C.NCup (n + 1) (a::b::c::l) ↔ a < b ∧ C.Cup3 a b c ∧ C.NCup n (b::c::l) := by
  simp only [Config.NCup, Cup.cons3, List.length_cons, Nat.add_right_cancel_iff]
  tauto


-- @@ L148-149 verbatim
protected theorem dropLast {n : ℕ} {l : List α} (h : C.NCup (n + 1) l) : C.NCup n l.dropLast :=
  ⟨h.1.dropLast, by rw [List.length_dropLast, h.2, Nat.add_sub_cancel]⟩


-- @@ L151-157 verbatim
protected theorem dropLast_append_last {n : ℕ} {l : List α} (h : C.NCup (n + 1) l) :
    ∃ (l' : List α) (a : α), l = l' ++ [a] ∧ C.NCup n l' := by
  have nnil : l ≠ [] := by
    rintro rfl
    rw [Config.NCup] at h
    simp_all
  exact ⟨l.dropLast, l.getLast nnil, (List.dropLast_append_getLast nnil).symm, h.dropLast⟩


-- @@ L159-160 verbatim
protected theorem tail {n : ℕ} {l : List α} (h : C.NCup (n + 1) l) : C.NCup n l.tail :=
  ⟨h.1.tail, by rw [List.length_tail, h.2, Nat.add_sub_cancel]⟩


-- @@ L162-168 verbatim
protected theorem cons_head_tail {n : ℕ} {l : List α} (h : C.NCup (n + 1) l) :
    ∃ (a : α) (l' : List α), (l = a::l') ∧ C.NCup n l' := by
  cases l with
  | nil =>
    rw [Config.NCup] at h
    simp_all
  | cons a l => exact ⟨a, l, rfl, h.tail⟩


-- @@ L170-174 verbatim
protected theorem take_head_last {n : ℕ} {l : List α} (h : C.NCup (n + 2) l) :
    ∃ (a : α) (l' : List α) (b : α), l = (a::l') ++ [b] ∧ C.NCup n l' := by
  rcases h.cons_head_tail with ⟨a, l', eq_l, cup_l'⟩
  rcases cup_l'.dropLast_append_last with ⟨l'', b, eq_l', cup_l''⟩
  simp_all


-- @@ L176-188 verbatim
theorem take_left_with_head {n : ℕ} {l : List α} (h : C.NCup n l) (m : ℕ) (p : α) :
    1 ≤ m → m ≤ n → p ∈ l.head? → ∃ l' : List α, l' ⊆ l ∧ C.NCup m l' ∧ p ∈ l'.head? := by
  intro one_le_m m_le_n l_last
  refine ⟨l.take m, List.take_subset m l, ⟨h.left.take m, ?_⟩, ?_⟩
  · rw [List.length_take, h.right, Nat.min_eq_left m_le_n]
  · rw [← List.take_append_drop m l] at l_last
    rw [List.head?_append_of_ne_nil] at l_last
    · exact l_last
    · intro hnil
      rw [List.take_eq_nil_iff] at hnil
      rcases hnil with hm | hl
      · omega
      · simp_all


-- @@ L190-202 verbatim
theorem take_right_with_last {n : ℕ} {l : List α} (h : C.NCup n l) (m : ℕ) (p : α) :
    1 ≤ m → m ≤ n → p ∈ l.getLast? → ∃ l' : List α, l' ⊆ l ∧ C.NCup m l' ∧ p ∈ l'.getLast? := by
  intro one_le_m m_le_n l_last
  refine ⟨l.drop (n - m), List.drop_subset (n - m) l, ⟨h.left.drop (n - m), ?_⟩, ?_⟩
  · rw [List.length_drop, h.right]
    omega
  · rw [← List.take_append_drop (n - m) l] at l_last
    rw [List.getLast?_append_of_ne_nil] at l_last
    · exact l_last
    · intro hnil
      have hlen : (l.drop (n - m)).length = 0 := by rw [hnil, List.length_nil]
      rw [List.length_drop, h.right] at hlen
      omega


-- @@ L204-206 verbatim
theorem head_lt_getLast {n : ℕ} {l : List α} (l_ncup : C.NCup (n + 2) l) (p q : α)
    (hp : p ∈ l.head?) (hq : q ∈ l.getLast?) : p < q :=
  l_ncup.left.head_lt_getLast p q (by rw [l_ncup.right]; omega) hp hq


-- @@ L208-210 verbatim
/-- Compatibility alias for the upstream theorem name. -/
theorem «head?_lt_getLast?» {n : ℕ} {l : List α} (l_ncup : C.NCup (n + 2) l) (p q : α)
    (hp : p ∈ l.head?) (hq : q ∈ l.getLast?) : p < q := head_lt_getLast l_ncup p q hp hq


-- @@ L212-226 verbatim
theorem head_le_getLast {n : ℕ} {l : List α} (l_ncup : C.NCup n l) (p q : α) (hp : p ∈ l.head?)
    (hq : q ∈ l.getLast?) : p ≤ q := by
  have l_sorted : l.Pairwise (· < ·) := List.isChain_iff_pairwise.mp l_ncup.left.left
  cases l with
  | nil => exact absurd hp (Option.not_mem_none p)
  | cons x rest =>
    rw [List.head?_cons, Option.mem_some_iff] at hp
    subst hp
    cases rest with
    | nil =>
      simp_all
    | cons p' rest =>
      rw [List.getLast?_cons_cons] at hq
      rw [List.pairwise_cons] at l_sorted
      exact le_of_lt (l_sorted.1 q (List.mem_of_mem_getLast? hq))


-- @@ L228-230 verbatim
/-- Compatibility alias for the upstream theorem name. -/
theorem «head?_le_getLast?» {n : ℕ} {l : List α} (l_ncup : C.NCup n l) (p q : α)
    (hp : p ∈ l.head?) (hq : q ∈ l.getLast?) : p ≤ q := head_le_getLast l_ncup p q hp hq


-- @@ L232-232 verbatim
end NCup


-- @@ L234-234 verbatim
end Config


-- @@ L236-261 verbatim
theorem ncup_is_ngon {n : ℕ} {S : Finset α} (hn : 2 ≤ n) (h : C.HasNCup n S) : C.HasNGon n S := by
  rcases h with ⟨c, ⟨⟨c_cup, c_length⟩, c_in_S⟩⟩
  have hc : c ≠ [] := by
    rintro rfl
    rw [List.length_nil] at c_length
    omega
  rcases List.takeLast hc with ⟨y, c, eq_c⟩; subst eq_c
  have hc : c ≠ [] := by
    rintro rfl
    simp only [List.nil_append, List.length_cons, List.length_nil] at c_length
    omega
  rcases List.takeHead hc with ⟨x, c, eq_c⟩; subst eq_c
  clear hc
  have hxy : x < y :=
    c_cup.head_lt_getLast x y (by rw [c_length]; omega) (by simp) (by simp)
  refine ⟨[x, y], (x :: c) ++ [y], ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · simp
  · simp_all
  · simp_all
  · exact c_cup
  · simp
  · simp
  · simp only [List.length_cons, List.length_append, List.length_nil] at c_length ⊢
    omega
  · simp_all
  · exact c_in_S


-- @@ L263-266 verbatim
theorem hasNCap_supset {n : ℕ} {S1 S2 : Finset α} (h : S1 ⊆ S2) (h1 : C.HasNCap n S1) :
    C.HasNCap n S2 := by
  obtain ⟨c1, h1⟩ := h1
  exact ⟨c1, h1.left, fun a a_c1 => h (h1.right a a_c1)⟩


-- @@ L268-271 verbatim
theorem hasNCup_supset {n : ℕ} {S1 S2 : Finset α} (h : S1 ⊆ S2) (h1 : C.HasNCup n S1) :
    C.HasNCup n S2 := by
  obtain ⟨c1, h1⟩ := h1
  exact ⟨c1, h1.left, fun a a_c1 => h (h1.right a a_c1)⟩


-- @@ L273-276 verbatim
theorem hasNGon_supset {n : ℕ} {S1 S2 : Finset α} (h : S1 ⊆ S2) (h1 : C.HasNGon n S1) :
    C.HasNGon n S2 := by
  rcases h1 with ⟨c1, c2, ⟨gon, c1_in, c2_in⟩⟩
  exact ⟨c1, c2, gon, fun a a_c1 => h (c1_in a a_c1), fun a a_c2 => h (c2_in a a_c2)⟩


-- @@ L278-281 verbatim
theorem hasNCup_le {n m : ℕ} {S : Finset α} (h : n ≤ m) : C.HasNCup m S → C.HasNCup n S := by
  rintro ⟨c, ⟨⟨c_cup, c_length⟩, c_in⟩⟩
  refine ⟨c.take n, ⟨c_cup.take n, ?_⟩, fun a ha => c_in a (List.take_subset _ _ ha)⟩
  rw [List.length_take, c_length, Nat.min_eq_left h]
