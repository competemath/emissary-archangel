module

public import Foundation.FirstOrder.Arithmetic.PeanoMinus.Basic


-- @@ L5-13 verbatim
@[expose] public section
lemma Nat.iff_lt_exists_add_succ : n < m ↔ ∃ k, m = n + (k + 1) := by
  constructor;
  . intro h;
    use m - n - 1;
    omega;
  . rintro ⟨k, rfl⟩;
    apply Nat.lt_add_of_pos_right;
    omega;


-- @@ L15-15 verbatim
namespace FFL.FirstOrder.Arithmetic


-- @@ L17-17 verbatim
namespace Countermodel


-- @@ L19-19 verbatim
def OmegaAddOne := Option ℕ


-- @@ L21-21 verbatim
namespace OmegaAddOne


-- @@ L23-23 verbatim
instance : NatCast OmegaAddOne := ⟨fun i ↦ .some i⟩


-- @@ L25-25 verbatim
instance (n : ℕ) : OfNat OmegaAddOne n := ⟨.some n⟩


-- @@ L27-27 verbatim
instance : Top OmegaAddOne := ⟨.none⟩


-- @@ L29-45 verbatim
instance : ORingStructure OmegaAddOne where
  add a b :=
    match a, b with
    | .some n, .some m => n + m
    |       ⊤,       _ => ⊤
    |       _,       ⊤ => ⊤
  mul a b :=
    match a, b with
    | .some n, .some m => n * m
    | .some 0,       ⊤ => 0
    |       ⊤, .some 0 => 0
    |       _,       _ => ⊤
  lt a b :=
    match a, b with
    | .some n, .some m => n < m
    |       _,       ⊤ => True
    |       ⊤, .some _ => False



-- @@ L48-48 verbatim
@[simp] lemma coe_zero : (↑(0 : ℕ) : OmegaAddOne) = 0 := rfl


-- @@ L50-50 verbatim
@[simp] lemma coe_one : (↑(1 : ℕ) : OmegaAddOne) = 1 := rfl


-- @@ L52-54 verbatim
@[simp] lemma coe_add (a b : ℕ) : ↑(a + b) = ((↑a + ↑b) : OmegaAddOne) := rfl

-- @[simp] lemma coe_mul (a b : ℕ) : ↑(a * b) = ((↑a * ↑b) : OmegaAddOne) := sorry


-- @@ L56-56 verbatim
@[simp] lemma lt_coe_iff (n m : ℕ) : (n : OmegaAddOne) < (m : OmegaAddOne) ↔ n < m := by rfl


-- @@ L58-58 verbatim
@[simp] lemma not_top_lt (n : ℕ) : ¬⊤ < (n : OmegaAddOne) := by rintro ⟨⟩


-- @@ L60-60 verbatim
@[simp] lemma lt_top {n : ℕ} : (n : OmegaAddOne) < ⊤ := by trivial


-- @@ L62-62 verbatim
@[simp] lemma top_add_zero : (⊤ : OmegaAddOne) + 0 = ⊤ := by rfl


-- @@ L64-64 verbatim
@[simp] lemma top_lt_top : (⊤ : OmegaAddOne) < ⊤ := by trivial


-- @@ L66-66 verbatim
@[simp] lemma top_add : (⊤ : OmegaAddOne) + a = ⊤ := by match a with | ⊤ | .some n => rfl


-- @@ L68-68 verbatim
@[simp] lemma add_top : a + (⊤ : OmegaAddOne) = ⊤ := by match a with | ⊤ | .some n => rfl



-- @@ L71-71 verbatim
variable {a b : OmegaAddOne}


-- @@ L73-73 verbatim
@[simp] lemma add_zero : a + 0 = a := by match a with | ⊤ | .some n => trivial;


-- @@ L75-75 verbatim
@[simp] lemma add_succ : a + (b + 1) = a + b + 1 := by match a, b with | ⊤, ⊤ | ⊤, .some n | .some m, ⊤ | .some n, .some m => tauto;


-- @@ L77-77 verbatim
@[simp] lemma mul_zero : a * 0 = 0 := by match a with | ⊤ | .some 0 | .some (n + 1) => rfl;


-- @@ L79-97 verbatim
@[simp]
lemma mul_succ : a * (b + 1) = a * b + a := by
  match a, b with
  | ⊤            , ⊤
  | ⊤            , .some 0
  | ⊤            , .some (n + 1)
  | .some 0      , .some n
  | .some 0      , ⊤
  | .some (m + 1), .some n
  | .some (m + 1), ⊤
  => rfl

lemma succ_inj : a + 1 = b + 1 → a = b := by
  match a, b with
  | ⊤, ⊤ | ⊤, .some m | .some n, ⊤ => simp;
  | .some n, .some m =>
    intro h;
    apply Option.mem_some_iff.mpr;
    simpa using Option.mem_some_iff.mp h;


-- @@ L99-103 verbatim
@[simp]
lemma succ_ne_zero : a + 1 ≠ 0 := by
  match a with
  | ⊤       => simp;
  | .some n => apply Option.mem_some_iff.not.mpr; simp;


-- @@ L105-110 verbatim
@[simp]
lemma zero_or_succ : a = 0 ∨ ∃ b, a = b + 1 := by
  match a with
  | .some 0 => left; rfl;
  | .some (n + 1) => right; use n; rfl;
  | ⊤ => right; use ⊤; rfl;


-- @@ L112-135 verbatim
@[simp]
lemma lt_def : a < b ↔ ∃ c, a + c + 1 = b := by
  match a, b with
  | ⊤, ⊤ => simp;
  | ⊤, .some n => simp [(show ¬(⊤ : OmegaAddOne) < .some n by tauto)];
  | .some m, ⊤ =>
    simp only [(show .some m < (⊤ : OmegaAddOne) by tauto), true_iff];
    use ⊤;
    rfl;
  | .some m, .some n =>
    apply Iff.trans (show some m < some n ↔ m < n by rfl);
    apply Iff.trans Nat.iff_lt_exists_add_succ;
    constructor;
    . intro h;
      obtain ⟨k, rfl⟩ : ∃ k : ℕ, m + (k + 1) = n := by tauto;
      use k;
      tauto;
    . rintro ⟨c, hc⟩;
      match c with
      | .none => simp at hc;
      | .some c => use c; exact Option.mem_some_iff.mp hc |>.symm;

lemma exists_add_one_eq_self : ∃ x : OmegaAddOne, x + 1 = x :=
  ⟨⊤, rfl⟩


-- @@ L137-137 verbatim
end OmegaAddOne


-- @@ L139-150 verbatim
set_option linter.flexible false in
instance : OmegaAddOne↓[ℒₒᵣ] ⊧* 𝗤 := ⟨by
  intro σ h;
  rcases h;
  case equal h =>
    have : OmegaAddOne↓[ℒₒᵣ] ⊧* 𝗘𝗤 ℒₒᵣ := inferInstance
    exact models_theory_iff.mp this _ h
  case succInj =>
    suffices ∀ a b : OmegaAddOne, a + 1 = b + 1 → a = b by simpa [models_iff];
    intro _; apply OmegaAddOne.succ_inj;
  all_goals simp [models_iff];
⟩


-- @@ L152-156 verbatim
end Countermodel

lemma RobinsonQ.unprovable_neSucc : 𝗤 ⊬ “∀ x, x + 1 ≠ x” :=
  unprovable_of_countermodel (M := Countermodel.OmegaAddOne) 𝗤 <| by
    simpa [notModels_iff] using Countermodel.OmegaAddOne.exists_add_one_eq_self


-- @@ L158-160 verbatim
instance : 𝗤 ⪱ 𝗣𝗔⁻ :=
  Entailment.StrictlyWeakerThan.of_unprovable_provable RobinsonQ.unprovable_neSucc
    <| complete.{0} _ _ fun _ _ _ ↦ by simp [models_iff]


-- @@ L162-162 verbatim
end FFL.FirstOrder.Arithmetic
