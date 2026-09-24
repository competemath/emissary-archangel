module

public import Foundation.FirstOrder.SetTheory.Basic
public import Foundation.FirstOrder.Skolemization.Hull


-- @@ L6-6 verbatim
@[expose] public section

-- @@ L7-9 verbatim
/-!
# Downward Löwenheim-Skolem theorem for models of set theory
-/


-- @@ L11-11 verbatim
namespace FFL.FirstOrder.SetTheory


-- @@ L13-13 verbatim
variable {V : Type*} [SetStructure V] [Nonempty V] (s : Set V)


-- @@ L15-15 verbatim
def Hull : Set V := Structure.SkolemHull ℒₛₑₜ s


-- @@ L17-17 verbatim
variable (V)


-- @@ L19-19 verbatim
abbrev Collapse : Set V := Hull ∅


-- @@ L21-21 verbatim
variable {V}


-- @@ L23-23 verbatim
namespace Hull


-- @@ L25-30 verbatim
@[simp] lemma mk_mem_mk_iff {x y : V} {hx hy} : (⟨x, hx⟩ : Hull s) ∈ (⟨y, hy⟩ : Hull s) ↔ x ∈ y := by rfl

lemma str_eq : Structure.SkolemHull.str (standardStructure V) s = standardStructure (Hull s) := by
  have : (Structure.SkolemHull.str (standardStructure V) s).Eq ℒₛₑₜ (Hull s) := Structure.SkolemHull.eq
  have : (Structure.SkolemHull.str (standardStructure V) s).Mem ℒₛₑₜ (Hull s) := Structure.SkolemHull.mem
  exact standardStructure_unique (Hull s) (Structure.SkolemHull.str (standardStructure V) s)


-- @@ L32-37 verbatim
@[simp] lemma subset : s ⊆ Hull s := Structure.SkolemHull.subset

lemma closed {v : Fin k → V} (hv : ∀ i, v i ∈ Hull s)
    {φ : SetTheorySemisentence (k + 1)} (H : ∃ z, V ⊧/(z :> v) φ) :
    ∃ z ∈ Hull s, V ⊧/(z :> v) φ :=
  Structure.SkolemHull.closed hv H


-- @@ L39-48 verbatim
@[simp] lemma hull_models_iff {φ : SetTheorySemisentence n} :
    (Hull s) ⊧/b φ ↔ V ⊧/(b ·) φ := by
  have :
      φ.Evalb (s := Structure.SkolemHull.str (standardStructure V) s) b ↔
      V ⊧/(b ·) φ :=
    Structure.SkolemHull.str_eval (𝓼 := standardStructure V) (φ := φ) (b := b)
  rw [str_eq] at this
  exact this

lemma set_nonempty : (Hull s).Nonempty := Structure.SkolemHull.set_nonempty _ _


-- @@ L50-50 verbatim
instance nonempty : Nonempty (Hull s) := Structure.SkolemHull.nonempty _ _


-- @@ L52-55 verbatim
instance elementaryEquiv : (Hull s) ≡ₑ[ℒₛₑₜ] V  where
  models {φ} := by simp [models_iff, Matrix.empty_eq]

lemma set_countable [hs : Countable s] : (Hull s).Countable := Structure.SkolemHull.set_countable hs


-- @@ L57-57 verbatim
instance countable [hs : Countable s] : Countable (Hull s) := Structure.SkolemHull.set_countable hs


-- @@ L59-59 verbatim
instance countable₀ : Countable (Collapse V) := Structure.SkolemHull.countable₀


-- @@ L61-61 verbatim
instance small [hs : Countable s] : Small.{w} ↑(Hull s) := Countable.toSmall (Hull s)


-- @@ L63-63 verbatim
end Hull


-- @@ L65-65 verbatim
end FFL.FirstOrder.SetTheory
