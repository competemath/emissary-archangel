module

public import Mathlib.Order.PFilter
public import Mathlib.Data.Set.Countable


-- @@ L6-6 verbatim
@[expose] public section


-- @@ L8-21 verbatim
namespace Nat

lemma monotone_of_succ_monotone {r : ℕ → ℕ → Prop} (rfx : Std.Refl r) (tr : IsTrans ℕ r)
    (succ : ∀ n, r n (n + 1)) : n ≤ m → r n m := by
  revert n m
  suffices ∀ n d, r n (n + d) by
    intro n m hnm
    have := this n (m - n)
    grind
  intro n d
  induction d
  case zero => simp [rfx.refl n]
  case succ d ih =>
    simpa using! tr.trans _ _ _ ih (succ (n + d))


-- @@ L23-23 verbatim
end Nat


-- @@ L25-25 verbatim
namespace DirectedOn


-- @@ L27-27 verbatim
variable {α : Type*} {r : α → α → Prop}


-- @@ L29-51 verbatim
private lemma vector_le (tr : IsTrans α r) {s : Set α} (hs : s.Nonempty) (h : DirectedOn r s) (v : Fin n → α) (hv : ∀ i, v i ∈ s) :
    ∃ z ∈ s, ∀ i, r (v i) z :=
  match n with
  | 0     => by
    rcases hs with ⟨x, hx⟩; exact ⟨x, hx, fun i ↦ IsEmpty.elim inferInstance i⟩
  | n + 1 => by
    have : ∃ z ∈ s, ∀ i : Fin n, r (v i.succ) z := h.vector_le tr hs (n := n) (fun i ↦ v i.succ) fun i ↦ hv i.succ
    rcases this with ⟨x, hx, hr⟩
    have : ∃ z ∈ s, r x z ∧ r (v 0) z := h x hx (v 0) (hv 0)
    rcases this with ⟨z, hz, hrxz, hrz⟩
    refine ⟨z, hz, ?_⟩
    intro i
    cases i using Fin.cases
    case zero => assumption
    case succ i =>
      exact tr.trans _ _ _ (hr i) hrxz

lemma fintype_colimit [Fintype ι] (tr : IsTrans α r)
    {s : Set α} (hs : s.Nonempty) (h : DirectedOn r s) (v : ι → α) (hv : ∀ i, v i ∈ s) :
    ∃ z ∈ s, ∀ i, r (v i) z := by
  let f : Fin (Fintype.card ι) → α := fun x ↦ v ((Fintype.equivFin ι).symm x)
  rcases DirectedOn.vector_le tr hs h f (by intro; simp [f, hv]) with ⟨z, hzs, hz⟩
  exact ⟨z, hzs, fun i ↦ by simpa [f] using hz ((Fintype.equivFin ι) i)⟩


-- @@ L53-53 verbatim
end DirectedOn


-- @@ L55-55 verbatim
namespace Order


-- @@ L57-57 verbatim
variable {α : Type*} [Preorder α]


-- @@ L59-59 verbatim
/-! ### Compatibility and incompatibility -/


-- @@ L61-61 verbatim
def IsCompatiblePair (a b : α) : Prop := ∃ c, c ≤ a ∧ c ≤ b


-- @@ L63-63 verbatim
scoped infix:50 " ‖ " => IsCompatiblePair


-- @@ L65-65 verbatim
@[simp, refl] protected lemma IsCompatiblePair.refl (a : α) : a ‖ a := ⟨a, by simp⟩


-- @@ L67-72 verbatim
@[symm] protected lemma IsCompatiblePair.symm_iff {a b : α} : a ‖ b ↔ b ‖ a := by
  constructor
  · rintro ⟨c, hca, hcb⟩; exact ⟨c, hcb, hca⟩
  · rintro ⟨c, hcb, hca⟩; exact ⟨c, hca, hcb⟩

alias ⟨IsCompatiblePair.symm, _⟩ := IsCompatiblePair.symm_iff


-- @@ L74-74 verbatim
@[grind <-] lemma IsCompatiblePair.of_le {a b : α} (h : a ≤ b) : a ‖ b := ⟨a, by simp [h]⟩


-- @@ L76-76 verbatim
def IsIncompatiblePair (a b : α) : Prop := ¬(a ‖ b)


-- @@ L78-81 verbatim
scoped infix:50 " ⟂ " => IsIncompatiblePair

lemma isIncompatiblePair_iff {a b : α} : a ⟂ b ↔ ∀ c ≤ a, ¬c ≤ b := by
  simp [IsIncompatiblePair, IsCompatiblePair]


-- @@ L83-92 verbatim
@[simp] lemma IsIncompatiblePair.antirefl (a : α) : ¬(a ⟂ a) := by simp [IsIncompatiblePair]

lemma IsIncompatiblePair.symm_iff {a b : α} : a ⟂ b ↔ b ⟂ a := by
  contrapose; simpa [IsIncompatiblePair] using IsCompatiblePair.symm_iff

alias ⟨IsIncompatiblePair.symm, _⟩ := IsIncompatiblePair.symm_iff

lemma IsIncompatiblePair.lower {a a' b b' : α} (h : a ⟂ b) (ha'a : a' ≤ a) (hb'b : b' ≤ b) : a' ⟂ b' := by
  rintro ⟨c, hca, hcb⟩
  exact h ⟨c, le_trans hca ha'a, le_trans hcb hb'b⟩


-- @@ L94-95 verbatim
@[simp, grind =] lemma not_isCompatiblePair_iff_isIncompatiblePair {a b : α} : ¬(a ‖ b) ↔ a ⟂ b := by
  rfl


-- @@ L97-98 verbatim
@[simp, grind =] lemma not_isIncompatiblePair_iff_isCompatiblePair {a b : α} : ¬(a ⟂ b) ↔ a ‖ b := by
  simp [IsIncompatiblePair, IsCompatiblePair]


-- @@ L100-100 verbatim
/-! ### Density -/


-- @@ L102-102 verbatim
def IsDense (s : Set α) : Prop := ∀ p, ∃ q ≤ p, q ∈ s


-- @@ L104-104 verbatim
def IsDenseBelow (s : Set α) (a : α) : Prop := ∀ p ≤ a, ∃ q ≤ p, q ∈ s


-- @@ L106-106 verbatim
variable (α)


-- @@ L108-110 verbatim
@[ext] structure DenseSet where
  set : Set α
  is_dense : IsDense set


-- @@ L112-112 verbatim
variable {α}


-- @@ L114-114 verbatim
namespace DenseSet


-- @@ L116-118 verbatim
instance : SetLike (DenseSet α) α where
  coe s := s.set
  coe_injective s t e := by ext; simp_all


-- @@ L120-120 verbatim
noncomputable def choose (d : DenseSet α) (a : α) : α := (d.is_dense a).choose


-- @@ L122-122 verbatim
@[simp] lemma choose_le (d : DenseSet α) (a : α) : d.choose a ≤ a := (d.is_dense a).choose_spec.1


-- @@ L124-124 verbatim
@[simp] lemma choose_mem (d : DenseSet α) (a : α) : d.choose a ∈ d := (d.is_dense a).choose_spec.2


-- @@ L126-126 verbatim
end DenseSet


-- @@ L128-128 verbatim
namespace PFilter


-- @@ L130-140 verbatim
def ofDescendingChain (s : ℕ → α) (hs : ∀ i j, i ≤ j → s i ≥ s j) : PFilter α :=
  IsPFilter.toPFilter <| Order.IsPFilter.of_def (F := {x | ∃ i, s i ≤ x})
    ⟨s 0, 0, by rfl⟩
    (by rintro x₁ ⟨i₁, h₁⟩ x₂ ⟨i₂, h₂⟩
        wlog hi : i₁ ≤ i₂
        · have z : i₂ ≤ i₁ := by exact Nat.le_of_not_ge hi
          rcases this s hs x₂ i₂ h₂ x₁ i₁ h₁ (Nat.le_of_not_ge hi) with ⟨z, hz⟩
          exact ⟨z, hz.1, hz.2.2, hz.2.1⟩
        exact ⟨s i₂, ⟨i₂, by rfl⟩, le_trans (hs i₁ i₂ hi) h₁, by simp [h₂]⟩)
    (by rintro x y hxy ⟨i, hix⟩
        exact ⟨i, le_trans hix hxy⟩)


-- @@ L142-143 verbatim
@[simp] lemma mem_descendingChain_iff (s : ℕ → α) (hs : ∀ i j, i ≤ j → s i ≥ s j) :
    x ∈ ofDescendingChain s hs ↔ ∃ i, s i ≤ x := by rfl


-- @@ L145-146 verbatim
class IsGeneric (F : PFilter α) (𝓓 : Set (DenseSet α)) where
  isGeneric : ∀ d ∈ 𝓓, ∃ a ∈ F, a ∈ d


-- @@ L148-148 verbatim
@[simp] instance IsGeneric.empty (F : PFilter α) : F.IsGeneric ∅ := ⟨by simp⟩


-- @@ L150-172 verbatim
theorem exists_genericFilter_of_countable
    (𝓓 : Set (DenseSet α)) (ctb : Set.Countable 𝓓) (a : α) :
    ∃ G : PFilter α, G.IsGeneric 𝓓 ∧ a ∈ G := by
  by_cases emp : 𝓓.Nonempty
  case neg =>
    exact ⟨principal a, by simp [Set.not_nonempty_iff_eq_empty.mp emp], by simp⟩
  have : ∃ D : ℕ → 𝓓, Function.Surjective D := ctb.exists_surjective emp
  rcases this with ⟨D, hD⟩
  let s (n : ℕ) : α := n.rec a fun i ↦ (D i).val.choose
  have hs : ∀ i j, i ≤ j → s i ≥ s j := fun i j hij ↦
    Nat.monotone_of_succ_monotone (r := fun i j ↦ s i ≥ s j)
      ⟨fun _ ↦ le_refl _⟩
      ⟨fun _ _ _ ↦ ge_trans⟩
      (by simp [s]) hij
  refine ⟨ofDescendingChain s hs, ⟨?_⟩, ?_⟩
  · intro d hd
    rcases show ∃ i, D i = ⟨d, hd⟩ from hD ⟨d, hd⟩ with ⟨i, hi⟩
    refine ⟨s (i + 1), ?_, ?_⟩
    · simp only [mem_descendingChain_iff]
      exact ⟨i + 1, by rfl⟩
    · simp [s, hi]
  · suffices ∃ i, s i ≤ a by simpa
    refine ⟨0, by simp [s]⟩


-- @@ L174-174 verbatim
end PFilter


-- @@ L176-176 verbatim
end Order
