module

public import Foundation.FirstOrder.Basic.Semantics.Elementary
public import Foundation.FirstOrder.Basic.BinderNotation
public import Foundation.FirstOrder.Basic.AesopInit
public import Foundation.Vorspiel.Finset.Card
public import Foundation.Vorspiel.Graph


-- @@ L9-9 verbatim
@[expose] public section


-- @@ L11-13 verbatim
/-!
# Relations and functions defined by a first-order formula (with parameter)
-/


-- @@ L15-15 verbatim
namespace FFL.FirstOrder


-- @@ L17-17 verbatim
variable {L : Language} {M : Type*} [Structure L M]


-- @@ L19-20 verbatim
abbrev IsDefinedBy (R : (Fin k → M) → Prop) (φ : Semisentence L k) : Prop :=
  ∀ v, φ.Evalb v ↔ R v


-- @@ L22-23 verbatim
class Defined (R : outParam ((Fin k → M) → Prop)) (φ : Semisentence L k) : Prop where
  iff : IsDefinedBy R φ


-- @@ L25-30 verbatim
/--
The relation `R` is definable by a formula `φ` with parameters over the domain `M`.
Here, the free variables of `φ` are indexed by the type `M`, so that `φ` may contain finitely many parameters, which are interpreted by using `id : M → M` for the valuation of free variables.
-/
abbrev IsDefinedByWithParam (R : (Fin k → M) → Prop) (φ : Semiformula L M k) : Prop :=
  ∀ v, φ.Eval v id ↔ R v


-- @@ L32-36 verbatim
@[simp] lemma Defined.eval_iff {R : (Fin k → M) → Prop} {φ : Semisentence L k} [h : Defined R φ] (v) :
    φ.Evalb v ↔ R v := h.iff v

lemma IsDefinedByWithParam.iff {R : (Fin k → M) → Prop} {φ : Semiformula L M k} (h : IsDefinedByWithParam R φ) (v) :
    φ.Eval v id ↔ R v := h v


-- @@ L38-39 verbatim
abbrev DefinedFunction (f : (Fin k → M) → M) (φ : Semisentence L (k + 1)) : Prop :=
  Defined (fun v ↦ v 0 = f (v ·.succ)) φ


-- @@ L41-42 verbatim
abbrev DefinedPred (P : M → Prop) (φ : Semisentence L 1) : Prop :=
  Defined (fun v ↦ P (v 0)) φ


-- @@ L44-45 verbatim
abbrev DefinedRel (R : M → M → Prop) (φ : Semisentence L 2) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1)) φ


-- @@ L47-48 verbatim
abbrev DefinedRel₃ (R : M → M → M → Prop) (φ : Semisentence L 3) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1) (v 2)) φ


-- @@ L50-51 verbatim
abbrev DefinedRel₄ (R : M → M → M → M → Prop) (φ : Semisentence L 4) : Prop :=
  Defined (fun v ↦ R (v 0) (v 1) (v 2) (v 3)) φ


-- @@ L53-54 verbatim
abbrev DefinedFunction₀ (c : M) (φ : Semisentence L 1) : Prop :=
  DefinedFunction (fun _ => c) φ


-- @@ L56-57 verbatim
abbrev DefinedFunction₁ (f : M → M) (φ : Semisentence L 2) : Prop :=
  DefinedFunction (fun v ↦ f (v 0)) φ


-- @@ L59-60 verbatim
abbrev DefinedFunction₂ (f : M → M → M) (φ : Semisentence L 3) : Prop :=
  DefinedFunction (fun v ↦ f (v 0) (v 1)) φ


-- @@ L62-63 verbatim
abbrev DefinedFunction₃ (f : M → M → M → M) (φ : Semisentence L 4) : Prop :=
  DefinedFunction (fun v ↦ f (v 0) (v 1) (v 2)) φ


-- @@ L65-66 verbatim
abbrev DefinedFunction₄ (f : M → M → M → M → M) (φ : Semisentence L 5) : Prop :=
  DefinedFunction (fun v ↦ f (v 0) (v 1) (v 2) (v 3)) φ


-- @@ L68-69 verbatim
abbrev DefinedFunction₅ (f : M → M → M → M → M → M) (φ : Semisentence L 6) : Prop :=
  DefinedFunction (fun v ↦ f (v 0) (v 1) (v 2) (v 3) (v 4)) φ


-- @@ L71-71 verbatim
notation K "-relation " P " via " φ => DefinedRel (L := K) P φ


-- @@ L73-73 verbatim
notation K "-relation₃ " P " via " φ => DefinedRel₃ (L := K) P φ


-- @@ L75-75 verbatim
notation K "-relation₄ " P " via " φ => DefinedRel₄ (L := K) P φ


-- @@ L77-77 verbatim
notation K "-function₀ " c " via " φ => DefinedFunction₀ (L := K) c φ


-- @@ L79-79 verbatim
notation K "-function₁ " f " via " φ => DefinedFunction₁ (L := K) f φ


-- @@ L81-81 verbatim
notation K "-function₂ " f " via " φ => DefinedFunction₂ (L := K) f φ


-- @@ L83-83 verbatim
notation K "-function₃ " f " via " φ => DefinedFunction₃ (L := K) f φ


-- @@ L85-85 verbatim
notation K "-function₄ " f " via " φ => DefinedFunction₄ (L := K) f φ


-- @@ L87-87 verbatim
notation K "-function₅ " f " via " φ => DefinedFunction₅ (L := K) f φ


-- @@ L89-89 verbatim
notation K "-predicate[" N "] " P " via " φ => DefinedPred (L := K) (M := N) P φ


-- @@ L91-91 verbatim
notation K "-relation[" N "] " P " via " φ => DefinedRel (L := K) (M := N) P φ


-- @@ L93-93 verbatim
notation K "-relation₃[" N "] " P " via " φ => DefinedRel₃ (L := K) (M := N) P φ


-- @@ L95-95 verbatim
notation K "-relation₄[" N "] " P " via " φ => DefinedRel₄ (L := K) (M := N) P φ


-- @@ L97-97 verbatim
notation K "-function₀[" N "] " c " via " φ => DefinedFunction₀ (L := K) (M := N) c φ


-- @@ L99-99 verbatim
notation K "-function₁[" N "] " f " via " φ => DefinedFunction₁ (L := K) (M := N) f φ


-- @@ L101-101 verbatim
notation K "-function₂[" N "] " f " via " φ => DefinedFunction₂ (L := K) (M := N) f φ


-- @@ L103-103 verbatim
notation K "-function₃[" N "] " f " via " φ => DefinedFunction₃ (L := K) (M := N) f φ


-- @@ L105-105 verbatim
notation K "-function₄[" N "] " f " via " φ => DefinedFunction₄ (L := K) (M := N) f φ


-- @@ L107-107 verbatim
notation K "-function₅[" N "] " f " via " φ => DefinedFunction₅ (L := K) (M := N) f φ


-- @@ L109-109 verbatim
namespace Language


-- @@ L111-111 verbatim
variable (L)


-- @@ L113-114 verbatim
class Definable {k} (P : (Fin k → M) → Prop) : Prop where
  definable : ∃ φ : Semiformula L M k, IsDefinedByWithParam P φ


-- @@ L116-116 verbatim
abbrev DefinablePred (P : M → Prop) : Prop := L.Definable (k := 1) fun v ↦ P (v 0)


-- @@ L118-118 verbatim
abbrev DefinableRel (P : M → M → Prop) : Prop := L.Definable (k := 2) (fun v ↦ P (v 0) (v 1))


-- @@ L120-120 verbatim
abbrev DefinableRel₃ (P : M → M → M → Prop) : Prop := L.Definable (k := 3) (fun v ↦ P (v 0) (v 1) (v 2))


-- @@ L122-122 verbatim
abbrev DefinableRel₄ (P : M → M → M → M → Prop) : Prop := L.Definable (k := 4) (fun v ↦ P (v 0) (v 1) (v 2) (v 3))


-- @@ L124-124 verbatim
abbrev DefinableRel₅ (P : M → M → M → M → M → Prop) : Prop := L.Definable (k := 5) (fun v ↦ P (v 0) (v 1) (v 2) (v 3) (v 4))


-- @@ L126-126 verbatim
abbrev DefinableRel₆ (P : M → M → M → M → M → M → Prop) : Prop := L.Definable (k := 6) (fun v ↦ P (v 0) (v 1) (v 2) (v 3) (v 4) (v 5))


-- @@ L128-128 verbatim
abbrev DefinableFunction (f : (Fin k → M) → M) : Prop := Definable (k := k + 1) L fun v ↦ v 0 = f (v ·.succ)


-- @@ L130-130 verbatim
abbrev DefinableFunction₀ (c : M) : Prop := L.DefinableFunction (k := 0) (fun _ ↦ c)


-- @@ L132-132 verbatim
abbrev DefinableFunction₁ (f : M → M) : Prop := L.DefinableFunction (k := 1) (fun v ↦ f (v 0))


-- @@ L134-134 verbatim
abbrev DefinableFunction₂ (f : M → M → M) : Prop := L.DefinableFunction (k := 2) (fun v ↦ f (v 0) (v 1))


-- @@ L136-136 verbatim
abbrev DefinableFunction₃ (f : M → M → M → M) : Prop := L.DefinableFunction (k := 3) (fun v ↦ f (v 0) (v 1) (v 2))


-- @@ L138-138 verbatim
abbrev DefinableFunction₄ (f : M → M → M → M → M) : Prop := L.DefinableFunction (k := 4) (fun v ↦ f (v 0) (v 1) (v 2) (v 3))


-- @@ L140-140 verbatim
abbrev DefinableFunction₅ (f : M → M → M → M → M → M) : Prop := L.DefinableFunction (k := 5) (fun v ↦ f (v 0) (v 1) (v 2) (v 3) (v 4))


-- @@ L142-142 verbatim
variable {L}


-- @@ L144-144 verbatim
notation L "-predicate " P => DefinablePred L P


-- @@ L146-146 verbatim
notation L "-relation " P => DefinableRel L P


-- @@ L148-148 verbatim
notation L "-relation₃ " P => DefinableRel₃ L P


-- @@ L150-150 verbatim
notation L "-relation₄ " P => DefinableRel₄ L P


-- @@ L152-152 verbatim
notation L "-relation₅ " P => DefinableRel₅ L P


-- @@ L154-154 verbatim
notation L "-function₁ " f => DefinableFunction₁ L f


-- @@ L156-156 verbatim
notation L "-function₂ " f => DefinableFunction₂ L f


-- @@ L158-158 verbatim
notation L "-function₃ " f => DefinableFunction₃ L f


-- @@ L160-160 verbatim
notation L "-function₄ " f => DefinableFunction₄ L f


-- @@ L162-162 verbatim
notation L "-predicate[" N "] " P => DefinablePred (M := N) L P


-- @@ L164-164 verbatim
notation L "-relation[" N "] " P => DefinableRel (M := N) L P


-- @@ L166-166 verbatim
notation L "-relation₃[" N "] " P => DefinableRel₃ (M := N) L P


-- @@ L168-168 verbatim
notation L "-relation₄[" N "] " P => DefinableRel₄ (M := N) L P


-- @@ L170-170 verbatim
notation L "-relation₅[" N "] " P => DefinableRel₅ (M := N) L P


-- @@ L172-172 verbatim
notation L "-function₁[" N "] " f => DefinableFunction₁ (M := N) L f


-- @@ L174-174 verbatim
notation L "-function₂[" N "] " f => DefinableFunction₂ (M := N) L f


-- @@ L176-176 verbatim
notation L "-function₃[" N "] " f => DefinableFunction₃ (M := N) L f


-- @@ L178-178 verbatim
notation L "-function₄[" N "] " f => DefinableFunction₄ (M := N) L f


-- @@ L180-180 verbatim
end Language


-- @@ L182-191 verbatim
namespace IsDefinedBy

lemma of_vec_one {R : (Fin 1 → M) → Prop} {φ : Semisentence L 1} (h : ∀ x, φ.Evalb ![x] ↔ R ![x]) : IsDefinedBy R φ := by
  intro v; simpa [←Matrix.fun_eq_vec_one] using h (v 0)

lemma of_vec_two {R : (Fin 2 → M) → Prop} {φ : Semisentence L 2} (h : ∀ x y, φ.Evalb ![x, y] ↔ R ![x, y]) : IsDefinedBy R φ := by
  intro v; simpa [←Matrix.fun_eq_vec_two] using h (v 0) (v 1)

lemma of_vec_three {R : (Fin 3 → M) → Prop} {φ : Semisentence L 3} (h : ∀ x y z, φ.Evalb ![x, y, z] ↔ R ![x, y, z]) : IsDefinedBy R φ := by
  intro v; simpa [←Matrix.fun_eq_vec_three] using h (v 0) (v 1) (v 2)


-- @@ L193-193 verbatim
end IsDefinedBy


-- @@ L195-198 verbatim
namespace Defined

lemma to_definable {R : (Fin k → M) → Prop} {φ : Semisentence L k} (hR : Defined R φ) : L.Definable R :=
  ⟨Rewriting.emb φ, fun v ↦ by simp [Semiformula.eval_emb]⟩


-- @@ L200-200 verbatim
end Defined


-- @@ L202-205 verbatim
namespace DefinedFunction

lemma to_definable {f : (Fin k → M) → M} {φ : Semisentence L (k + 1)} (hf : DefinedFunction f φ) : L.DefinableFunction f :=
  Defined.to_definable hf


-- @@ L207-207 verbatim
end DefinedFunction


-- @@ L209-209 verbatim
namespace Language


-- @@ L211-211 verbatim
namespace Definable


-- @@ L213-216 verbatim
variable {P Q R : (Fin k → M) → Prop}

lemma of_iff {P Q : (Fin k → M) → Prop} (H : L.Definable Q) (h : ∀ x, P x ↔ Q x) : L.Definable P := by
  rwa [show P = Q from by funext v; simp [h]]


-- @@ L218-221 verbatim
@[simp] lemma const (p : Prop) : L.Definable fun _ : Fin k → M ↦ p := by
  by_cases hp : p
  · exact ⟨⊤, by intro _; simp [hp]⟩
  · exact ⟨⊥, by intro _; simp [hp]⟩


-- @@ L223-227 verbatim
@[grind .] lemma and {R S : (Fin k → M) → Prop} (hR : L.Definable R) (hS : L.Definable S) :
    L.Definable fun v : Fin k → M ↦ R v ∧ S v := by
  rcases hR with ⟨φ, hR⟩
  rcases hS with ⟨ψ, hS⟩
  exact ⟨φ ⋏ ψ, by intro _; simp [hR.iff, hS.iff]⟩


-- @@ L229-233 verbatim
@[grind .] lemma or {R S : (Fin k → M) → Prop} (hR : L.Definable R) (hS : L.Definable S) :
    L.Definable fun v : Fin k → M ↦ R v ∨ S v := by
  rcases hR with ⟨φ, hR⟩
  rcases hS with ⟨ψ, hS⟩
  exact ⟨φ ⋎ ψ, by intro _; simp [hR.iff, hS.iff]⟩


-- @@ L235-239 verbatim
@[grind .] lemma imp {R S : (Fin k → M) → Prop} (hR : L.Definable R) (hS : L.Definable S) :
    L.Definable fun v : Fin k → M ↦ R v → S v := by
  rcases hR with ⟨φ, hR⟩
  rcases hS with ⟨ψ, hS⟩
  exact ⟨φ 🡒 ψ, by intro _; simp [hR.iff, hS.iff]⟩


-- @@ L241-244 verbatim
@[grind .] lemma not {R : (Fin k → M) → Prop} (hR : L.Definable R) :
    L.Definable fun v : Fin k → M ↦ ¬R v := by
  rcases hR with ⟨φ, hR⟩
  exact ⟨∼φ, by intro _; simp [hR.iff]⟩


-- @@ L246-260 verbatim
@[grind .] lemma biconditional {R S : (Fin k → M) → Prop} (hR : L.Definable R) (hS : L.Definable S) :
    L.Definable fun v : Fin k → M ↦ R v ↔ S v := by
  rcases hR with ⟨φ, hR⟩
  rcases hS with ⟨ψ, hS⟩
  exact ⟨φ 🡘 ψ, by intro _; simp [hR.iff, hS.iff]⟩

lemma all {R : (Fin k → M) → M → Prop} (hR : L.Definable fun w ↦ R (w ·.succ) (w 0)) :
    L.Definable fun v : Fin k → M ↦ ∀ x, R v x := by
  rcases hR with ⟨φ, hR⟩
  exact ⟨∀¹ φ, fun v ↦ by simp [hR.iff]⟩

lemma exs {R : (Fin k → M) → M → Prop} (hR : L.Definable fun w ↦ R (w ·.succ) (w 0)) :
    L.Definable fun v : Fin k → M ↦ ∃ x, R v x := by
  rcases hR with ⟨φ, hR⟩
  exact ⟨∃¹ φ, fun v ↦ by simp [hR.iff]⟩


-- @@ L262-262 verbatim
instance eq [L.Eq] [Structure.Eq L M] : L-relation[M] Eq := ⟨“x y. x = y”, fun _ ↦ by simp⟩


-- @@ L264-264 verbatim
instance lt [L.LT] [LT M] [Structure.LT L M] : L-relation[M] _root_.LT.lt := ⟨“x y. x < y”, fun _ ↦ by simp⟩


-- @@ L266-352 verbatim
instance mem [L.Mem] [Membership M M] [Structure.Mem L M] : L-relation[M] Membership.mem := ⟨“x y. y ∈ x”, fun _ ↦ by simp⟩

lemma fconj {P : ι → (Fin k → M) → Prop} (s : Finset ι)
    (h : ∀ i, L.Definable fun w : Fin k → M ↦ P i w) : L.Definable fun v : Fin k → M ↦ ∀ i ∈ s, P i v := by
  have : ∀ i, ∃ φ, IsDefinedByWithParam (P i) φ := fun i ↦ (h i).definable
  rcases Classical.axiomOfChoice this with ⟨φ, H⟩
  exact ⟨⩕ i ∈ s, φ i, fun v ↦ by simp [fun i ↦ (H i).iff]⟩

lemma fdisj {P : ι → (Fin k → M) → Prop} (s : Finset ι)
    (h : ∀ i, L.Definable fun w : Fin k → M ↦ P i w) : L.Definable fun v : Fin k → M ↦ ∃ i ∈ s, P i v := by
  have : ∀ i, ∃ φ, IsDefinedByWithParam (P i) φ := fun i ↦ (h i).definable
  rcases Classical.axiomOfChoice this with ⟨φ, H⟩
  exact ⟨⩖ i ∈ s, φ i, fun v ↦ by simp [fun i ↦ (H i).iff]⟩

lemma fintype_all [Fintype ι] {P : ι → (Fin k → M) → Prop}
    (h : ∀ i, L.Definable fun w : Fin k → M ↦ P i w) : L.Definable fun v : Fin k → M ↦ ∀ i, P i v := by
  simpa using fconj Finset.univ h

lemma fintype_exs [Fintype ι] {P : ι → (Fin k → M) → Prop}
    (h : ∀ i, L.Definable fun w : Fin k → M ↦ P i w) : L.Definable fun v : Fin k → M ↦ ∃ i, P i v := by
  simpa using fdisj Finset.univ h

lemma retraction (h : L.Definable P) {n} (f : Fin k → Fin n) :
    L.Definable fun v ↦ P (fun i ↦ v (f i)) := by
  rcases h with ⟨φ, hφ⟩
  exact ⟨(Rew.subst fun i ↦ #(f i)) ▹ φ, fun v ↦ by simp [←hφ.iff, Function.comp_def]⟩

lemma exsVec {k l} {P : (Fin k → M) → (Fin l → M) → Prop}
    (h : L.Definable fun w : Fin (k + l) → M ↦ P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    L.Definable fun v : Fin k → M ↦ ∃ ys : Fin l → M, P v ys := by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq] using h
  case succ l ih =>
    suffices L.Definable fun v : Fin k → M ↦ ∃ y, ∃ ys : Fin l → M, P v (y :> ys) by
      apply of_iff this; intro x
      constructor
      · rintro ⟨ys, h⟩; exact ⟨ys 0, (ys ·.succ), by simpa using h⟩
      · rintro ⟨y, ys, h⟩; exact ⟨_, h⟩
    apply exs; apply ih
    let g : Fin (k + (l + 1)) → Fin (k + 1 + l) := Matrix.vecAppend rfl (fun x ↦ x.succ.castAdd l) (Fin.castAdd l 0 :> fun j ↦ j.natAdd (k + 1))
    exact of_iff (retraction h g) (by
      intro v; simp only [g]
      apply iff_of_eq; congr
      · ext i; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
      · ext i
        cases' i using Fin.cases with i
        · simp only [Matrix.cons_val_zero]; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
        · simp only [Matrix.cons_val_succ]; congr 1; ext; simp [Matrix.vecAppend_eq_ite])

lemma allVec {k l} {P : (Fin k → M) → (Fin l → M) → Prop}
    (h : L.Definable fun w : Fin (k + l) → M ↦ P (fun i ↦ w (i.castAdd l)) (fun j ↦ w (j.natAdd k))) :
    L.Definable fun v : Fin k → M ↦ ∀ ys : Fin l → M, P v ys := by
  induction l generalizing k
  case zero => simpa [Matrix.empty_eq] using h
  case succ l ih =>
    suffices L.Definable fun v : Fin k → M ↦ ∀ y, ∀ ys : Fin l → M, P v (y :> ys) by
      apply of_iff this; intro x
      constructor
      · intro h y ys; apply h
      · intro h ys; simpa using h (ys 0) (ys ·.succ)
    apply all; apply ih
    let g : Fin (k + (l + 1)) → Fin (k + 1 + l) := Matrix.vecAppend rfl (fun x ↦ x.succ.castAdd l) (Fin.castAdd l 0 :> fun j ↦ j.natAdd (k + 1))
    exact of_iff (retraction h g) (by
      intro v; simp only [g]
      apply iff_of_eq; congr
      · ext i; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
      · ext i
        cases' i using Fin.cases with i
        · simp only [Matrix.cons_val_zero]; congr 1; ext; simp [Matrix.vecAppend_eq_ite]
        · simp only [Matrix.cons_val_succ]; congr 1; ext; simp [Matrix.vecAppend_eq_ite])

lemma substitution {P : (Fin k → M) → Prop} {f : Fin k → (Fin l → M) → M}
    (hP : L.Definable P) (hf : ∀ i, L.DefinableFunction (f i)) :
    L.Definable fun z ↦ P (f · z) := by
  have : L.Definable fun z ↦ ∃ ys : Fin k → M, (∀ i, ys i = f i z) ∧ P ys := by
    apply exsVec; apply and
    · apply fintype_all; intro i
      simpa using retraction (hf i) (i.natAdd l :> fun i ↦ i.castAdd k)
    · exact retraction hP (Fin.natAdd l)
  exact of_iff this <| by
    intro v
    constructor
    · intro hP
      exact ⟨(f · v), by simp, hP⟩
    · rintro ⟨ys, hys, hP⟩
      have : ys = fun i ↦ f i v := funext hys
      rcases this; exact hP


-- @@ L354-391 verbatim
end Definable

lemma DefinablePred.comp {P : M → Prop} {k} {f : (Fin k → M) → M}
    [hP : L.DefinablePred P] (hf : L.DefinableFunction f) :
    L.Definable (fun v ↦ P (f v)) :=
  Definable.substitution (f := ![f]) hP (by simpa using hf)

lemma DefinableRel.comp {P : M → M → Prop} {k} {f g : (Fin k → M) → M}
    [hP : L.DefinableRel P]
    (hf : L.DefinableFunction f) (hg : L.DefinableFunction g) :
    L.Definable fun v ↦ P (f v) (g v) :=
  Definable.substitution (f := ![f, g]) hP (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf, hg])

lemma DefinableRel₃.comp {k} {P : M → M → M → Prop} {f₁ f₂ f₃ : (Fin k → M) → M}
    [hP : L.DefinableRel₃ P]
    (hf₁ : L.DefinableFunction f₁) (hf₂ : L.DefinableFunction f₂)
    (hf₃ : L.DefinableFunction f₃) :
    L.Definable (fun v ↦ P (f₁ v) (f₂ v) (f₃ v)) :=
  Definable.substitution (f := ![f₁, f₂, f₃]) hP (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃])

lemma DefinableRel₄.comp {k} {P : M → M → M → M → Prop} {f₁ f₂ f₃ f₄ : (Fin k → M) → M}
    [hP : L.DefinableRel₄ P]
    (hf₁ : L.DefinableFunction f₁) (hf₂ : L.DefinableFunction f₂)
    (hf₃ : L.DefinableFunction f₃) (hf₄ : L.DefinableFunction f₄) :
    L.Definable (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v)) :=
  Definable.substitution (f := ![f₁, f₂, f₃, f₄]) hP (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃, hf₄])

lemma DefinableRel₅.comp {k} {P : M → M → M → M → M → Prop} {f₁ f₂ f₃ f₄ f₅ : (Fin k → M) → M}
    [hP : L.DefinableRel₅ P]
    (hf₁ : L.DefinableFunction f₁) (hf₂ : L.DefinableFunction f₂)
    (hf₃ : L.DefinableFunction f₃) (hf₄ : L.DefinableFunction f₄)
    (hf₅ : L.DefinableFunction f₅) :
    L.Definable (fun v ↦ P (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v)) :=
  Definable.substitution (f := ![f₁, f₂, f₃, f₄, f₅]) hP (by simp [Fin.forall_fin_iff_zero_and_forall_succ, hf₁, hf₂, hf₃, hf₄, hf₅])

lemma DefinablePred.of_iff {P Q : M → Prop}
    (H : L.DefinablePred Q) (h : ∀ x, P x ↔ Q x) : L.DefinablePred P := by
  rwa [show P = Q from by funext v; simp [h]]


-- @@ L393-394 verbatim
instance DefinableFunction₁.graph {f : M → M} [h : L.DefinableFunction₁ f] :
  L.DefinableRel (Function.Graph f) := h


-- @@ L396-397 verbatim
instance DefinableFunction₂.graph {f : M → M → M} [h : L.DefinableFunction₂ f] :
  L.DefinableRel₃ (Function.Graph₂ f) := h


-- @@ L399-400 verbatim
instance DefinableFunction₃.graph {f : M → M → M → M} [h : L.DefinableFunction₃ f] :
  L.DefinableRel₄ (Function.Graph₃ f) := h


-- @@ L402-404 verbatim
/-!
### Definable functions
-/


-- @@ L406-406 verbatim
variable [L.Eq] [Structure.Eq L M]


-- @@ L408-408 verbatim
namespace DefinableFunction


-- @@ L410-411 verbatim
instance projection (i : Fin k) : L.DefinableFunction fun w : Fin k → M ↦ w i :=
  ⟨“x. x = #i.succ”, fun _ ↦ by simp⟩


-- @@ L413-423 verbatim
instance const (c : M) :  L.DefinableFunction fun _ : Fin k → M ↦ c :=
  ⟨“x. x = &c”, fun _ ↦ by simp⟩

lemma substitution {f : Fin k → (Fin l → M) → M}
    (hF : L.DefinableFunction F) (hf : ∀ i, L.DefinableFunction (f i)) :
    L.DefinableFunction fun z ↦ F (fun i ↦ f i z) := by
  simpa using Definable.substitution (f := (· 0) :> fun i w ↦ f i (w ·.succ)) hF <| by
    intro i
    cases' i using Fin.cases with i
    · simpa using projection _
    · simpa using Definable.retraction (hf i) (0 :> (·.succ.succ))


-- @@ L425-425 verbatim
instance hAdd [L.Add] [Add M] [Structure.Add L M] : L-function₂[M] HAdd.hAdd := ⟨“x y z. x = y + z”, fun _ ↦ by simp⟩


-- @@ L427-427 verbatim
instance hMul [L.Mul] [Mul M] [Structure.Mul L M] : L-function₂[M] HMul.hMul := ⟨“x y z. x = y * z”, fun _ ↦ by simp⟩


-- @@ L429-462 verbatim
end DefinableFunction

lemma DefinableFunction₁.comp {k} {F : M → M} {f : (Fin k → M) → M}
    [hF : L.DefinableFunction₁ F] (hf : L.DefinableFunction f) :
    L.DefinableFunction (fun v ↦ F (f v)) :=
  DefinableFunction.substitution (f := ![f]) hF (by simp [hf])

lemma DefinableFunction₂.comp {k} {F : M → M → M} {f₁ f₂ : (Fin k → M) → M}
    [hF : L.DefinableFunction₂ F]
    (hf₁ : L.DefinableFunction f₁) (hf₂ : L.DefinableFunction f₂) :
    L.DefinableFunction (fun v ↦ F (f₁ v) (f₂ v)) :=
  DefinableFunction.substitution (f := ![f₁, f₂]) hF (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma DefinableFunction₃.comp {k} {F : M → M → M → M} {f₁ f₂ f₃ : (Fin k → M) → M}
    [hF : L.DefinableFunction₃ F]
    (hf₁ : L.DefinableFunction f₁) (hf₂ : L.DefinableFunction f₂)
    (hf₃ : L.DefinableFunction f₃) :
    L.DefinableFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v)) :=
  DefinableFunction.substitution (f := ![f₁, f₂, f₃]) hF (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma DefinableFunction₄.comp {k} {F : M → M → M → M → M} {f₁ f₂ f₃ f₄ : (Fin k → M) → M}
    [hF : L.DefinableFunction₄ F]
    (hf₁ : L.DefinableFunction f₁) (hf₂ : L.DefinableFunction f₂)
    (hf₃ : L.DefinableFunction f₃) (hf₄ : L.DefinableFunction f₄) :
    L.DefinableFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v) (f₄ v)) :=
  DefinableFunction.substitution (f := ![f₁, f₂, f₃, f₄]) hF (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])

lemma DefinableFunction₅.comp {k} {F : M → M → M → M → M → M} {f₁ f₂ f₃ f₄ f₅ : (Fin k → M) → M}
    [hF : L.DefinableFunction₅ F]
    (hf₁ : L.DefinableFunction f₁) (hf₂ : L.DefinableFunction f₂)
    (hf₃ : L.DefinableFunction f₃) (hf₄ : L.DefinableFunction f₄)
    (hf₅ : L.DefinableFunction f₅) :
    L.DefinableFunction (fun v ↦ F (f₁ v) (f₂ v) (f₃ v) (f₄ v) (f₅ v)) :=
  DefinableFunction.substitution (f := ![f₁, f₂, f₃, f₄, f₅]) hF (by simp [Fin.forall_fin_iff_zero_and_forall_succ, *])


-- @@ L464-466 verbatim
section aesop

-- https://github.com/leanprover-community/mathlib4/blob/77d078e25cc501fae6907bfbcd80821920125266/Mathlib/Tactic/Measurability.lean#L25-L26

-- @@ L467-467 verbatim
open Lean.Parser.Tactic (config)


-- @@ L469-470 verbatim
attribute [aesop (rule_sets := [Definability]) norm]
  Function.comp_def


-- @@ L472-475 verbatim
attribute [aesop 4 (rule_sets := [Definability]) safe]
  DefinableFunction.const
  DefinableFunction.projection
  Definable.const


-- @@ L477-480 verbatim
attribute [aesop 5 (rule_sets := [Definability]) safe]
  DefinableFunction₁.comp
  DefinableFunction₂.comp
  DefinableFunction₃.comp


-- @@ L482-486 verbatim
attribute [aesop 6 (rule_sets := [Definability]) safe]
  DefinablePred.comp
  DefinableRel.comp
  DefinableRel₃.comp
  DefinableRel₄.comp


-- @@ L488-491 verbatim
attribute [aesop 10 (rule_sets := [Definability]) safe]
  Definable.not
  Definable.imp
  Definable.biconditional


-- @@ L493-497 verbatim
attribute [aesop 11 (rule_sets := [Definability]) safe]
  Definable.and
  Definable.or
  Definable.all
  Definable.exs


-- @@ L499-500 verbatim
macro "definability" : attr =>
  `(attr|aesop 10 (rule_sets := [$(Lean.mkIdent `Definability):ident]) safe)


-- @@ L502-503 verbatim
macro "definability" (config)? : tactic =>
  `(tactic| aesop (config := { terminal := true }) (rule_sets := [$(Lean.mkIdent `Definability):ident]))


-- @@ L505-506 verbatim
macro "definability?" (config)? : tactic =>
  `(tactic| aesop? (config := { terminal := true }) (rule_sets := [$(Lean.mkIdent `Definability):ident]))


-- @@ L508-510 verbatim
example {f : M → M} {g : M → M → M} [L.DefinableFunction₁ f] [L.DefinableFunction₂ g] (c : M) :
    L.DefinableRel fun x y : M ↦ ∀ z, f x = g y (g (f z) c) := by
  definability


-- @@ L512-514 verbatim
example [L.Mem] [Membership M M] [Structure.Mem L M] {f : M → M} [L.DefinableFunction₁ f] :
    L.DefinableRel fun x y : M ↦ f x = y ↔ ∀ z, z ∈ f x ↔ z ∈ y := by
  definability


-- @@ L516-516 verbatim
end aesop


-- @@ L518-518 verbatim
end Language


-- @@ L520-520 verbatim
end FFL.FirstOrder


-- @@ L522-522 verbatim
end
