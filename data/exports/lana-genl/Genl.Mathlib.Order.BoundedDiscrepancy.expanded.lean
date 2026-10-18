/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Function
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring


-- @@ L14-38 verbatim
/-!
# Bounded discrepancy classes of real valued functions

Given real valued functions `f g : α → ℝ` and a set `s : Set α`, we say that `f` is
*dominated up to bounded discrepancy* by `g` on `s`, written `f ≲[s] g`, if there exists
a constant `C : ℝ` such that `f x ≤ g x + C` for all `x ∈ s`. If both `f ≲[s] g` and
`g ≲[s] f` hold, we write `f ≈[s] g` and say that `f` and `g` are *equal up to bounded
discrepancy* on `s`. The equivalence classes of `≈[s]` are the *BD-classes* of
[mochizuki2010], Definition 1.2 (ii).

These notions are ubiquitous in the theory of height functions in diophantine geometry,
where all interesting statements about heights only hold up to a bounded discrepancy,
e.g. the height function associated to a line bundle is only well defined up to bounded
discrepancy.

## Main definitions

- `DiscrepancyLE f g s` (notation: `f ≲[s] g`): `f ≤ g + C` on `s` for some constant `C`.
- `DiscrepancyEquiv f g s` (notation: `f ≈[s] g`): `f ≲[s] g` and `g ≲[s] f`.

## References

- [mochizuki2010] S. Mochizuki, *Arithmetic elliptic curves in general position*,
  Math. J. Okayama Univ. **52** (2010), 1–28.
-/


-- @@ L40-40 verbatim
variable {α β : Type*}


-- @@ L42-46 verbatim
/-- `DiscrepancyLE f g s`, denoted `f ≲[s] g`, means that `f` is bounded above by `g` up
to a bounded discrepancy on `s`, i.e. there exists a constant `C` such that
`f x ≤ g x + C` for all `x ∈ s`. -/
def DiscrepancyLE (f g : α → ℝ) (s : Set α) : Prop :=
  ∃ C : ℝ, ∀ x ∈ s, f x ≤ g x + C


-- @@ L48-52 verbatim
/-- `DiscrepancyEquiv f g s`, denoted `f ≈[s] g`, means that `f` and `g` agree up to a
bounded discrepancy on `s`, i.e. `|f x - g x|` is bounded on `s`. The equivalence classes
of this relation are called *BD-classes*. -/
def DiscrepancyEquiv (f g : α → ℝ) (s : Set α) : Prop :=
  DiscrepancyLE f g s ∧ DiscrepancyLE g f s


-- @@ L54-55 verbatim
@[inherit_doc]
notation:50 f:51 " ≲[" s "] " g:51 => DiscrepancyLE f g s


-- @@ L57-58 verbatim
@[inherit_doc]
notation:50 f:51 " ≈[" s "] " g:51 => DiscrepancyEquiv f g s


-- @@ L60-60 verbatim
namespace DiscrepancyLE


-- @@ L62-62 verbatim
variable {f f₁ f₂ g g₁ g₂ h : α → ℝ} {s t : Set α}


-- @@ L64-65 expanded
theorem of_forall_le (hfg : ∀ x ∈ s, f x ≤ g x) : DiscrepancyLE f g s :=
  ⟨0, fun x hx ↦ by simpa using hfg x hx⟩


-- @@ L67-68 expanded
protected theorem refl (f : α → ℝ) (s : Set α) : DiscrepancyLE f f s :=
  of_forall_le fun _ _ ↦ le_rfl


-- @@ L70-73 expanded
protected theorem trans (h₁ : DiscrepancyLE f g s) (h₂ : DiscrepancyLE g h s) :
    DiscrepancyLE f h s := by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  exact ⟨C₁ + C₂, fun x hx ↦ by have := hC₁ x hx; have := hC₂ x hx; linarith⟩


-- @@ L75-77 expanded
theorem mono (hst : t ⊆ s) (hfg : DiscrepancyLE f g s) : DiscrepancyLE f g t :=
  by
  obtain ⟨C, hC⟩ := hfg
  exact ⟨C, fun x hx ↦ hC x (hst hx)⟩


-- @@ L79-81 expanded
@[simp]
theorem empty : DiscrepancyLE f g (∅ : Set α) :=
  ⟨0, by simp⟩


-- @@ L83-89 expanded
theorem union (hs : DiscrepancyLE f g s) (ht : DiscrepancyLE f g t) : DiscrepancyLE f g (s ∪ t) :=
  by
  obtain ⟨C₁, hC₁⟩ := hs
  obtain ⟨C₂, hC₂⟩ := ht
  refine ⟨max C₁ C₂, fun x hx ↦ ?_⟩
  rcases hx with hx | hx
  · exact (hC₁ x hx).trans (by gcongr; exact le_max_left C₁ C₂)
  · exact (hC₂ x hx).trans (by gcongr; exact le_max_right C₁ C₂)


-- @@ L91-98 expanded
protected theorem add (h₁ : DiscrepancyLE f₁ g₁ s) (h₂ : DiscrepancyLE f₂ g₂ s) :
    DiscrepancyLE (f₁ + f₂) (g₁ + g₂) s :=
  by
  obtain ⟨C₁, hC₁⟩ := h₁
  obtain ⟨C₂, hC₂⟩ := h₂
  refine ⟨C₁ + C₂, fun x hx ↦ ?_⟩
  have := hC₁ x hx
  have := hC₂ x hx
  simp only [Pi.add_apply]
  linarith


-- @@ L100-106 expanded
protected theorem smul {c : ℝ} (hc : 0 ≤ c) (hfg : DiscrepancyLE f g s) :
    DiscrepancyLE (c • f) (c • g) s := by
  obtain ⟨C, hC⟩ := hfg
  refine ⟨c * C, fun x hx ↦ ?_⟩
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    c * f x ≤ c * (g x + C) := by exact mul_le_mul_of_nonneg_left (hC x hx) hc
    _ = c * g x + c * C := by ring


-- @@ L108-113 expanded
theorem sub_right (hfg : DiscrepancyLE f g s) (h : α → ℝ) : DiscrepancyLE (f - h) (g - h) s :=
  by
  obtain ⟨C, hC⟩ := hfg
  refine ⟨C, fun x hx ↦ ?_⟩
  have := hC x hx
  simp only [Pi.sub_apply]
  linarith


-- @@ L115-116 expanded
theorem add_right (hfg : DiscrepancyLE f g s) (h : α → ℝ) : DiscrepancyLE (f + h) (g + h) s := by
  simpa using hfg.add (DiscrepancyLE.refl h s)


-- @@ L118-122 expanded
/-- Bounded discrepancy inequalities are stable under precomposition. -/
theorem comp (hfg : DiscrepancyLE f g s) (φ : β → α) {t : Set β} (hφ : Set.MapsTo φ t s) :
    DiscrepancyLE (f ∘ φ) (g ∘ φ) t := by
  obtain ⟨C, hC⟩ := hfg
  exact ⟨C, fun x hx ↦ hC (φ x) (hφ hx)⟩


-- @@ L124-131 expanded
/-- A bounded discrepancy inequality descends along a map that is surjective onto the
base set. -/
theorem of_comp_surjOn {φ : β → α} {t : Set β} (hφ : Set.SurjOn φ t s)
    (hfg : DiscrepancyLE (f ∘ φ) (g ∘ φ) t) : DiscrepancyLE f g s :=
  by
  obtain ⟨C, hC⟩ := hfg
  refine ⟨C, fun x hx ↦ ?_⟩
  obtain ⟨y, hy, rfl⟩ := hφ hx
  exact hC y hy


-- @@ L133-133 verbatim
end DiscrepancyLE


-- @@ L135-135 verbatim
namespace DiscrepancyEquiv


-- @@ L137-137 verbatim
variable {f f₁ f₂ g g₁ g₂ h : α → ℝ} {s t : Set α}


-- @@ L139-139 expanded
theorem le (hfg : DiscrepancyEquiv f g s) : DiscrepancyLE f g s :=
  hfg.1


-- @@ L141-141 expanded
theorem ge (hfg : DiscrepancyEquiv f g s) : DiscrepancyLE g f s :=
  hfg.2


-- @@ L143-144 expanded
protected theorem refl (f : α → ℝ) (s : Set α) : DiscrepancyEquiv f f s :=
  ⟨.refl f s, .refl f s⟩


-- @@ L146-147 expanded
protected theorem symm (hfg : DiscrepancyEquiv f g s) : DiscrepancyEquiv g f s :=
  ⟨hfg.2, hfg.1⟩


-- @@ L149-150 expanded
protected theorem trans (h₁ : DiscrepancyEquiv f g s) (h₂ : DiscrepancyEquiv g h s) :
    DiscrepancyEquiv f h s :=
  ⟨h₁.le.trans h₂.le, h₂.ge.trans h₁.ge⟩


-- @@ L152-153 expanded
theorem mono (hst : t ⊆ s) (hfg : DiscrepancyEquiv f g s) : DiscrepancyEquiv f g t :=
  ⟨hfg.le.mono hst, hfg.ge.mono hst⟩


-- @@ L155-156 expanded
protected theorem add (h₁ : DiscrepancyEquiv f₁ g₁ s) (h₂ : DiscrepancyEquiv f₂ g₂ s) :
    DiscrepancyEquiv (f₁ + f₂) (g₁ + g₂) s :=
  ⟨h₁.le.add h₂.le, h₁.ge.add h₂.ge⟩


-- @@ L158-159 expanded
protected theorem smul {c : ℝ} (hc : 0 ≤ c) (hfg : DiscrepancyEquiv f g s) :
    DiscrepancyEquiv (c • f) (c • g) s :=
  ⟨hfg.le.smul hc, hfg.ge.smul hc⟩


-- @@ L161-162 expanded
theorem sub_right (hfg : DiscrepancyEquiv f g s) (h : α → ℝ) : DiscrepancyEquiv (f - h) (g - h) s :=
  ⟨hfg.le.sub_right h, hfg.ge.sub_right h⟩


-- @@ L164-166 expanded
theorem comp (hfg : DiscrepancyEquiv f g s) (φ : β → α) {t : Set β} (hφ : Set.MapsTo φ t s) :
    DiscrepancyEquiv (f ∘ φ) (g ∘ φ) t :=
  ⟨hfg.le.comp φ hφ, hfg.ge.comp φ hφ⟩


-- @@ L168-168 verbatim
end DiscrepancyEquiv


-- @@ L170-170 verbatim
namespace DiscrepancyLE


-- @@ L172-172 verbatim
variable {f g h : α → ℝ} {s : Set α}


-- @@ L174-175 expanded
theorem trans_equiv (h₁ : DiscrepancyLE f g s) (h₂ : DiscrepancyEquiv g h s) :
    DiscrepancyLE f h s :=
  h₁.trans h₂.le


-- @@ L177-178 expanded
theorem equiv_trans (h₁ : DiscrepancyEquiv f g s) (h₂ : DiscrepancyLE g h s) :
    DiscrepancyLE f h s :=
  h₁.le.trans h₂


-- @@ L180-180 verbatim
end DiscrepancyLE
