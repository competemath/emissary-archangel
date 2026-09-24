module

public import Foundation.FirstOrder.Basic
public import Mathlib.SetTheory.Cardinal.Basic


-- @@ L6-6 verbatim
@[expose] public section

-- @@ L7-7 verbatim
/-! # Skolem hull -/


-- @@ L9-9 verbatim
namespace FFL.FirstOrder


-- @@ L11-14 verbatim
/-- Skolem function of rank 1 -/
def Language.skolemFunction₁ (L : Language) : Language where
  Func k := Semisentence L (k + 1)
  Rel _ := PEmpty


-- @@ L16-16 verbatim
abbrev Semisentence.skolem₁ {L : Language} (φ : Semisentence L (k + 1)) : L.skolemFunction₁.Func k := φ


-- @@ L18-20 verbatim
instance (L : Language) [L.Encodable] : L.skolemFunction₁.Encodable where
  func k := inferInstanceAs (Encodable (Semisentence L (k + 1)))
  rel _ := inferInstanceAs (Encodable PEmpty)


-- @@ L22-22 verbatim
namespace Structure


-- @@ L24-24 verbatim
variable (L : Language.{u})


-- @@ L26-26 verbatim
variable (M : Type v) [Nonempty M] [𝓼 : Structure L M]


-- @@ L28-30 expanded
noncomputable instance skolem : Structure L.skolemFunction₁ M
    where
  func _ φ v := Classical.epsilon fun z ↦ φ.Evalb (vecCons z v)
  rel _ r _ := PEmpty.elim r


-- @@ L32-32 verbatim
variable {L M}


-- @@ L34-35 expanded
@[simp]
lemma val_skolem_func (φ : Semisentence L (k + 1)) :
    (skolem L M).func φ.skolem₁ v = Classical.epsilon fun z ↦ φ.Evalb (vecCons z v) :=
  rfl


-- @@ L37-37 verbatim
variable (L)


-- @@ L39-40 verbatim
/-- The Skolem hull of subset of structure. -/
def SkolemHull (s : Set M) : Set M := Set.range fun t : Term L.skolemFunction₁ s ↦ t.val ![] (↑)


-- @@ L42-42 verbatim
variable (M)


-- @@ L44-44 verbatim
abbrev SkolemHull₀ := SkolemHull L (M := M) ∅


-- @@ L46-46 verbatim
variable {L M}


-- @@ L48-48 verbatim
namespace SkolemHull


-- @@ L50-50 verbatim
open Semiformula


-- @@ L52-52 verbatim
variable {s : Set M}


-- @@ L54-56 verbatim
lemma mem_iff :
    x ∈ SkolemHull L s ↔ ∃ t : Term L.skolemFunction₁ s, t.val ![] (↑) = x := by
  simp [SkolemHull]


-- @@ L58-58 verbatim
@[simp] lemma val_mem (t : Term L.skolemFunction₁ s) : t.val ![] (↑) ∈ SkolemHull L s := by simp [SkolemHull]


-- @@ L60-63 verbatim
lemma subset : s ⊆ SkolemHull L s := fun x hx ↦ by
  let t : Term L.skolemFunction₁ s := &⟨x, hx⟩
  have : x = t.val ![] (↑) := by simp [t]
  simp [this]


-- @@ L65-73 expanded
lemma closed {v : Fin k → M} (hv : ∀ i, v i ∈ SkolemHull L s) {φ : Semisentence L (k + 1)}
    (H : ∃ z, φ.Evalb (vecCons z v)) : ∃ z ∈ SkolemHull L s, φ.Evalb (vecCons z v) :=
  by
  choose u hu using fun i ↦ mem_iff.mp (hv i)
  let t : Term L.skolemFunction₁ s := .func φ.skolem₁ u
  refine ⟨t.val ![] (↑), by simp, ?_⟩
  suffices φ.Evalb (vecCons (Classical.epsilon fun z ↦ φ.Evalb (vecCons z v)) v) by
    simpa [t, Semiterm.val_func, Function.comp_def, hu]
  exact Classical.epsilon_spec H


-- @@ L75-75 verbatim
variable [L.Eq] [Structure.Eq L M]


-- @@ L77-84 expanded
lemma closed_func {v : Fin k → M} (hv : ∀ i, v i ∈ SkolemHull L s) {f : L.Func k} :
    Structure.func f v ∈ SkolemHull L s :=
  by
  have :
    ∃ z ∈ SkolemHull L s,
      (Semiformula.Operator.operator Operator.Eq.eq ![#0, (Semiterm.func f fun i ↦ #i.succ)]).Evalb
        (vecCons z v) :=
    closed hv (φ :=
      Semiformula.Operator.operator Operator.Eq.eq ![#0, (Semiterm.func f fun i ↦ #i.succ)])
      (by simp [Semiterm.val_func]; simp [Function.comp_def])
  rcases this with ⟨z, hz, e⟩
  have : z = func f v := by simpa [Semiterm.val_func] using! e
  rcases this; assumption


-- @@ L86-86 verbatim
variable (𝓼 s)


-- @@ L88-90 verbatim
instance (priority := 50) str : Structure L (SkolemHull L s) where
  func k f v := ⟨func f fun i ↦ (v i : M), closed_func (by simp)⟩
  rel k R v := Structure.rel R fun i ↦ (v i : M)


-- @@ L92-97 verbatim
omit [L.Eq] [Structure.Eq L M] in
lemma set_nonempty : (SkolemHull L s).Nonempty := by
  have : ∃ z : M, (⊤ : Semisentence L 1).Evalb ![z] := by simp
  have : ∃ z, z ∈ SkolemHull L s := by
    simpa using closed (s := s) (by simp) this
  exact this


-- @@ L99-100 verbatim
instance nonempty : Nonempty (SkolemHull L s) :=
  Set.Nonempty.to_subtype (set_nonempty _ _)


-- @@ L102-102 verbatim
variable {𝓼 s}


-- @@ L104-105 verbatim
@[simp] lemma str_func_def (f : L.Func k) (v : Fin k → SkolemHull L s) :
    (str 𝓼 s).func f v = ⟨𝓼.func f fun i ↦ (v i : M), closed_func (by simp)⟩ := rfl


-- @@ L107-108 verbatim
@[simp] lemma str_rel_def (R : L.Rel k) (v : Fin k → SkolemHull L s) :
    (str 𝓼 s).rel R v ↔ 𝓼.rel R fun i ↦ (v i : M) := by rfl


-- @@ L110-115 verbatim
@[simp] lemma str_val (t : Semiterm L ξ n) (b : Fin n → SkolemHull L s) (f : ξ → SkolemHull L s) :
    (t.val (M := SkolemHull L s) (s := str 𝓼 s) b f : M) = t.val (s := 𝓼) (b ·) (f ·) :=
  match t with
  |        #x => by simp
  |        &x => by simp
  | .func F v => by simp [Semiterm.val_func, str_val, Function.comp_def]


-- @@ L117-141 expanded
@[simp]
lemma str_eval {φ : Semisentence L n} : φ.Evalb (M := SkolemHull L s) b ↔ φ.Evalb (M := M) (b ·) :=
  match φ with
  | .rel R v | .nrel R v => by
    simp [Semiformula.eval_rel, Semiformula.eval_nrel, Empty.eq_elim, Function.comp_def]
  | ⊤ | ⊥ => by simp
  | binop% HWedge.hWedge φ ψ | binop% HVee.hVee φ ψ => by
    simp [str_eval (φ := φ), str_eval (φ := ψ)]
  | UnivQuantifier.all φ =>
    by
    suffices
      (∃ x ∈ SkolemHull L s, (unop% HTilde.hTilde φ).Evalb (vecCons x (b ·))) ↔
        (∃ x : M, (unop% HTilde.hTilde φ).Evalb (vecCons x (b ·)))
      by
      apply not_iff_not.mp
      simpa [str_eval (φ := φ), Matrix.comp_vecCons']
    constructor
    · rintro ⟨x, _, H⟩
      exact ⟨x, H⟩
    · intro h
      exact closed (s := s) (by simp) h
  | ExsQuantifier.exs φ =>
    by
    suffices
      (∃ x ∈ SkolemHull L s, φ.Evalb (vecCons x (b ·))) ↔ (∃ x : M, φ.Evalb (vecCons x (b ·))) by
      simpa [str_eval (φ := φ), Matrix.comp_vecCons']
    constructor
    · rintro ⟨x, _, H⟩
      exact ⟨x, H⟩
    · intro h
      exact closed (s := s) (by simp) h


-- @@ L143-145 expanded
/-- Downward Löwenheim-Skolem theorem for countable language (1) -/
instance (priority := 50) elementaryEquiv : ElementaryEquiv L (SkolemHull L s) M where
  models {φ} := by simp [models_iff, Matrix.empty_eq]


-- @@ L147-149 verbatim
instance (priority := 50) eq : Structure.Eq L (SkolemHull L s) := ⟨fun x y ↦ by
  rw [Subtype.ext_iff]
  simpa [Operator.val, Matrix.fun_eq_vec_two] using Structure.Eq.eq (L := L) (M := M) x.val y.val⟩


-- @@ L151-151 verbatim
section mem


-- @@ L153-153 verbatim
variable [Operator.Mem L] [Membership M M] [Structure.Mem L M]


-- @@ L155-156 verbatim
instance (priority := 50) membership :
  Membership (SkolemHull L s) (SkolemHull L s) := ⟨fun y x ↦ x.val ∈ y.val⟩


-- @@ L158-160 verbatim
instance (priority := 50) mem :
    Structure.Mem L (SkolemHull L s) := ⟨fun x y ↦ by
  simpa [Operator.val, Matrix.fun_eq_vec_two] using! Structure.Mem.mem (L := L) (M := M) x.val y.val⟩


-- @@ L162-162 verbatim
end mem


-- @@ L164-164 verbatim
end SkolemHull


-- @@ L166-166 verbatim
namespace SkolemHull


-- @@ L168-168 verbatim
open Cardinal


-- @@ L170-170 verbatim
variable [L.Encodable] {s : Set M}


-- @@ L172-175 verbatim
lemma set_countable (hs : s.Countable) : (SkolemHull L s).Countable := by
  have : Countable s := hs
  have : Countable (Term L.skolemFunction₁ s) := Semiterm.countable
  exact Set.countable_range _


-- @@ L177-177 verbatim
lemma countable (hs : s.Countable) : Countable (SkolemHull L s) := set_countable hs


-- @@ L179-179 verbatim
instance countable₀ : Countable (SkolemHull₀ L M) := set_countable (by simp)


-- @@ L181-184 verbatim
/-- Downward Löwenheim-Skolem theorem for countable language (2) -/
lemma card_le_aleph0 (hs : s.Countable) : #(SkolemHull L s) ≤ ℵ₀ :=
  have : Countable (SkolemHull L s) := countable hs
  Set.Countable.le_aleph0 this


-- @@ L186-186 verbatim
end SkolemHull


-- @@ L188-188 verbatim
end Structure


-- @@ L190-190 verbatim
end FFL.FirstOrder
