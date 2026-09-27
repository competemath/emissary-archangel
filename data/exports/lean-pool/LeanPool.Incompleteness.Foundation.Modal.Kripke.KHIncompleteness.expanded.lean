/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Foundation.Modal.Hilbert.WellKnown
public import LeanPool.Incompleteness.Foundation.Modal.Kripke.Basic
import LeanPool.Incompleteness.Foundation.Modal.Kripke.AxiomL
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.TautoSet


-- @@ L15-15 verbatim
/-! # KHIncompleteness -/


-- @@ L17-17 verbatim
@[expose] public section



-- @@ L20-20 verbatim
namespace LO

-- @@ L21-21 verbatim
namespace Modal


-- @@ L23-23 verbatim
open System

-- @@ L24-24 verbatim
open Kripke

-- @@ L25-25 verbatim
open Formula

-- @@ L26-26 verbatim
open Formula.Kripke


-- @@ L28-28 verbatim
namespace Kripke


-- @@ L30-30 verbatim
variable {F : Kripke.Frame} {a : ℕ}


-- @@ L32-37 expanded
lemma valid_atomic_H_of_valid_atomic_L :
    Realize F (Axioms.L (atom a)) → Realize F (Axioms.H (atom a)) :=
  by
  intro h V x hx;
  have : Satisfies ⟨F, V⟩ x (Box.box (Arrow.arrow (Box.box a) a)) := by intro y Rxy;
    exact (Satisfies.and_def.mp <| @hx y Rxy) |>.1;
  exact @h V x this;


-- @@ L39-71 expanded
lemma valid_atomic_L_of_valid_atomic_H :
    Realize F (Axioms.H (atom a)) → Realize F (Axioms.L (atom a)) :=
  by
  intro hH V x hx; let V' : Valuation F := fun w a => ∀ n : ℕ, Satisfies ⟨F, V⟩ w (multibox n a);
  have h₁ : Satisfies ⟨F, V'⟩ x (Box.box (LogicalConnective.iff (Box.box a) a)) :=
    by
    intro y Rxy;
    have : Satisfies ⟨F, V'⟩ y a ↔ Satisfies ⟨F, V'⟩ y (Box.box a) :=
      calc
        _ ↔ ∀ n, Satisfies ⟨F, V⟩ y (multibox n a) := by simp [Satisfies, V'];
        _ ↔ ∀ n, Satisfies ⟨F, V⟩ y (multibox (n + 1) a) :=
          by
          constructor; · intro h n; apply h;
          · intro h n;
            have h₁ :
              Satisfies ⟨F, V⟩ y
                (Arrow.arrow (Box.box (multibox n (atom a))) (multibox n (atom a))) :=
              by
              induction n with
              | zero => apply @hx y Rxy;
              | succ n => intro _; apply h;
            apply h₁; simpa using h n;
        _ ↔ ∀ n, ∀ z, Frame.Rel' y z → Satisfies ⟨F, V⟩ z (multibox n a) :=
          by
          constructor
          · intro h n z hz
            have hn : ∀ z, Frame.Rel' y z → Satisfies ⟨F, V⟩ z (multibox n (atom a)) := by
              have := h n; rw [Box.multibox_succ] at this; exact this
            exact hn z hz
          · intro h n
            rw [Box.multibox_succ]; exact h n;
        _ ↔ ∀ z, Frame.Rel' y z → ∀ n : ℕ, Satisfies ⟨F, V⟩ z (multibox n a) := by aesop;
        _ ↔ ∀ z, Frame.Rel' y z → Satisfies ⟨F, V'⟩ z (atom a) := by simp [Satisfies, V'];
        _ ↔ Satisfies ⟨F, V'⟩ y (Box.box (atom a)) := by simp [Satisfies];
    simp [Satisfies, V']; tauto;
  have h₂ : Satisfies ⟨F, V'⟩ x (Box.box (atom a)) := @hH V' x h₁; intro w Rxw; exact @h₂ w Rxw 0;


-- @@ L73-76 expanded
lemma valid_atomic_L_iff_valid_atomic_H :
    Realize F (Axioms.L (atom 0)) ↔ Realize F (Axioms.H (atom 0)) :=
  by
  constructor; · exact valid_atomic_H_of_valid_atomic_L;
  · exact valid_atomic_L_of_valid_atomic_H;


-- @@ L78-81 expanded
lemma valid_atomic_4_of_valid_atomic_L :
    Realize F (Axioms.L (atom 0)) → Realize F (Axioms.Four (atom 0)) := by
  intro h V x h₂ y Rxy z Ryz; refine h₂ z ?_; exact (trans_of_validate_L h).trans _ _ _ Rxy Ryz;


-- @@ L83-86 expanded
lemma valid_atomic_Four_of_valid_atomic_H :
    Realize F (Axioms.H (atom 0)) → Realize F (Axioms.Four (atom 0)) :=
  by
  trans; · exact valid_atomic_L_iff_valid_atomic_H.mpr;
  · exact valid_atomic_4_of_valid_atomic_L;


-- @@ L88-96 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev cresswellFrame : Kripke.Frame where
  World := ℕ × Fin 2
  Rel n m :=
    match n, m with
    | (n, 0), (m, 0) => n ≤ m + 1
    | (n, 1), (m, 1) => n > m
    | (_, 0), (_, 1) => True
    | _, _ => False


-- @@ L98-98 verbatim
namespace cresswellFrame


-- @@ L100-101 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[match_pattern] abbrev sharp (n : ℕ) : cresswellFrame.World := (n, 0)

-- @@ L102-103 verbatim
/-- Imported notation from the Incompleteness formalization. -/
postfix:max "♯" => sharp



-- @@ L106-107 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
@[match_pattern] abbrev flat (n : ℕ) : cresswellFrame.World := (n, 1)

-- @@ L108-109 verbatim
/-- Imported notation from the Incompleteness formalization. -/
postfix:max "♭" => flat


-- @@ L111-111 verbatim
variable {n m : ℕ} {x y : cresswellFrame.World}


-- @@ L113-119 expanded
/-- Imported declaration from the Incompleteness formalization. -/
lemma trichonomy : Frame.Rel' x y ∨ x = y ∨ Frame.Rel' y x := by
  match x, y with
  | sharp x, sharp y => simp [cresswellFrame, Frame.Rel']; omega;
  | flat x, sharp y => simp [cresswellFrame, Frame.Rel'];
  | sharp x, flat y => simp [cresswellFrame, Frame.Rel'];
  | flat x, flat y => simp [cresswellFrame, Frame.Rel']; omega;


-- @@ L121-121 expanded
lemma sharp_to_flat : Frame.Rel' (sharp n) (flat m) := by simp [Frame.Rel']


-- @@ L123-123 expanded
@[simp]
lemma not_flat_to_sharp : ¬(Frame.Rel' (flat n) (sharp m)) := by simp [Frame.Rel'];


-- @@ L125-125 expanded
lemma sharp_to_sharp : Frame.Rel' (sharp n) (sharp m) ↔ n ≤ m + 1 := by simp [Frame.Rel']


-- @@ L127-127 expanded
lemma flat_to_flat : Frame.Rel' (flat n) (flat m) ↔ n > m := by simp [Frame.Rel'];


-- @@ L129-132 expanded
lemma exists_flat_of_from_flat (h : Frame.Rel' (flat n) x) : ∃ m, x = ⟨m, 1⟩ ∧ n > m := by
  match x with
  | ⟨m, 0⟩ => aesop;
  | ⟨m, 1⟩ => exact ⟨m, rfl, flat_to_flat.mp h⟩;


-- @@ L134-134 verbatim
end cresswellFrame




-- @@ L138-139 expanded
/-- Imported declaration from the Incompleteness formalization. -/
abbrev cresswellModel : Kripke.Model :=
  ⟨cresswellFrame, fun w _ => w ≠ sharp 0⟩


-- @@ L141-141 verbatim
namespace cresswellModel


-- @@ L143-143 verbatim
end cresswellModel



-- @@ L146-146 verbatim
open cresswellFrame cresswellModel


-- @@ L148-165 expanded
lemma not_valid_axiomFour_in_cresswellModel :
    ¬(Satisfies cresswellModel (sharp 2) (Axioms.Four (atom 0))) :=
  by
  apply Satisfies.imp_def.not.mpr; push Not; constructor;
  · intro x;
    match x with
    | sharp n =>
      intro h2n; suffices n ≠ 0 by simpa [Satisfies];
      simp only [sharp_to_sharp] at h2n; omega;
    | flat n => simp [Satisfies];
  · apply Satisfies.box_def.not.mpr
    push Not; refine ⟨sharp 1, sharp_to_sharp.mpr (by omega), ?_⟩; apply Satisfies.box_def.not.mpr;
    push Not; exact ⟨sharp 0, sharp_to_sharp.mpr (by omega), by tauto⟩;


-- @@ L167-169 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
abbrev _root_.LO.Modal.Kripke.cresswellModel.truthset (φ : Formula _) := { x :
    cresswellModel.World | Satisfies cresswellModel x φ }

-- @@ L170-170 verbatim
local notation "‖" φ "‖" => cresswellModel.truthset φ


-- @@ L172-172 verbatim
namespace cresswellModel

-- @@ L173-173 verbatim
namespace truthset


-- @@ L175-179 expanded
lemma infinite_of_all_flat (h : ∀ n, flat n ∈ ‖φ‖) : (‖φ‖.Infinite) :=
  Set.infinite_coe_iff.mp <|
    Infinite.of_injective (fun n => ⟨flat n, h n⟩) <| by
      simp [Function.Injective]
        -- TODO: need golf


-- @@ L180-199 expanded
lemma exists_max_sharp (h₁ : ∀ n, flat n ∈ ‖φ‖) (h₂ : ‖φ‖ᶜ.Finite) (h₃ : ‖φ‖ᶜ.Nonempty) :
    ∃ n, sharp n ∉ ‖φ‖ ∧ (∀ m > n, sharp m ∈ ‖φ‖) :=
  by
  obtain ⟨s, hs⟩ := Set.Finite.exists_finset (s := (fun x => x.1) '' ‖φ‖ᶜ) <| Set.Finite.image _ h₂;
  have se : s.Nonempty := by let ⟨x, hx⟩ := h₃; use x.1; apply hs _ |>.mpr; use x;
  use (s.max' se); constructor;
  · have hmem := (@hs _).mp (Finset.max'_mem _ se)
    simp_all
  · intro m hm; by_contra hC; have : m < m := Finset.max'_lt_iff (H := se) |>.mp hm m (by simp_all);
    simp at this;
    -- TODO: need golf


-- @@ L200-219 expanded
open Classical in
lemma exists_min_flat (h₁ : ∃ n, flat n ∉ ‖φ‖) : ∃ n, flat n ∉ ‖φ‖ ∧ (∀ m < n, flat m ∈ ‖φ‖) :=
  by
  obtain ⟨n, hn⟩ := h₁; let s := Finset.Icc 0 n |>.filter (fun k => flat k ∉ ‖φ‖);
  have hse : s.Nonempty := by use n; simpa [s];
  use (s.min' hse); have ⟨h₁, h₂⟩ := Finset.mem_filter |>.mp <| @Finset.min'_mem (s := s) _ _ hse;
  constructor; · exact h₂;
  · intro m hm; by_contra hC;
    have :=
      Finset.lt_min'_iff _ _ |>.mp hm m <|
        by
        simp only [Set.mem_ofPred_eq, Finset.mem_filter, Finset.mem_Icc, zero_le, true_and, s];
        constructor;
        · simp only [Finset.lt_min'_iff, s] at hm; have := hm n <| by simpa [s];
          omega;
        · exact hC;
    simp at this;


-- @@ L221-279 expanded
lemma either_finite_cofinite : (‖φ‖.Finite) ∨ (‖φ‖ᶜ.Finite) := by
  induction φ using Formula.rec' with
  | hatom a => simp [truthset, Satisfies];
  | hfalsum => simp [truthset, Satisfies];
  | himp φ ψ ihφ
    ihψ =>
    rw [(show ‖Arrow.arrow φ ψ‖ = ‖φ‖ᶜ ∪ ‖ψ‖ by tauto_set), Set.compl_union, compl_compl];
    rcases ihφ with (_ | _) <;> rcases ihψ with (_ | _);
    · right; apply Set.Finite.inter_of_left; assumption;
    · right; apply Set.Finite.inter_of_left; assumption;
    · simp_all
    · right; apply Set.Finite.inter_of_right; assumption;
  | hbox φ ihφ =>
    by_cases h : ∀ n, flat n ∈ ‖φ‖;
    · have tsφc_finite : ‖φ‖ᶜ.Finite :=
        or_iff_not_imp_left.mp ihφ <| truthset.infinite_of_all_flat h; wlog tsφc_ne : ‖φ‖ᶜ.Nonempty;
      · have : ‖Box.box φ‖ᶜ = ∅ := by
          simp only [Set.compl_empty_iff, Set.eq_univ_iff_forall, Set.mem_ofPred_eq]; intro x y Rxy;
          match x, y with
          | sharp m,
            sharp
              k =>
            have : ∀ x, Satisfies cresswellModel x φ := by
              simpa [Set.compl_empty, Set.Nonempty] using tsφc_ne;
            apply this;
          | flat m, sharp k => simp at Rxy;
          | sharp m, flat k => apply h;
          | flat m, flat k => apply h;
        simp_all
      obtain ⟨n, hn, hn_max⟩ := exists_max_sharp h tsφc_finite tsφc_ne; right;
      apply @Set.Finite.subset (s := (sharp ·) '' Set.Icc 0 (n + 1)); · apply Set.toFinite
      · intro x hx; replace := Satisfies.box_def.not.mp hx; push Not at this;
        obtain ⟨y, Rxy, _⟩ := this;
        match x, y with
        | sharp m, sharp k => by_contra hC; simp at hC; replace Rxy := sharp_to_sharp.mp Rxy;
          have : sharp k ∈ ‖φ‖ := @hn_max k (by omega); contradiction;
        | flat m, sharp k => simp at Rxy;
        | sharp _, flat k => have := h k; contradiction;
        | flat _, flat k => have := h k; contradiction;
    · left; push Not at h; obtain ⟨n, hn⟩ := h;
      apply @Set.Finite.subset (s := (flat ·) '' Set.Icc 0 n); · apply Set.toFinite
      · intro x hx;
        match x with
        | sharp m => have := hx (flat n) sharp_to_flat; contradiction;
        | flat m => by_contra hC;
          have := hx (flat n) <| (cresswellFrame.flat_to_flat.mpr <| by simpa using hC);
          contradiction;


-- @@ L281-281 verbatim
end truthset

-- @@ L282-282 verbatim
end cresswellModel


-- @@ L284-352 expanded
open Classical in
lemma valid_axiomH_in_cresswellModel :
    Realize cresswellModel
      (Arrow.arrow (Box.box (LogicalConnective.iff (Box.box φ) φ)) (Box.box φ)) :=
  by
  rintro x; by_cases h : ∀ n, flat n ∈ ‖φ‖;
  · have tsφc_fin : ‖φ‖ᶜ.Finite :=
      or_iff_not_imp_left.mp truthset.either_finite_cofinite <| truthset.infinite_of_all_flat h;
    wlog tsφc_ne : ‖φ‖ᶜ.Nonempty;
    · apply Satisfies.imp_def₂.mpr; right; intro y Rxy;
      have : ∀ x, Satisfies cresswellModel x φ := by
        simpa [Set.compl_empty, Set.Nonempty] using tsφc_ne;
      apply this;
    obtain ⟨n, hn, hn_max⟩ := truthset.exists_max_sharp h tsφc_fin tsφc_ne;
    match x with
    | flat m => apply Satisfies.imp_def₂.mpr; right; rintro y Rny;
      obtain ⟨k, ⟨rfl, _⟩⟩ := exists_flat_of_from_flat Rny; apply h;
    | sharp m =>
      by_cases hnm : n + 2 ≤ m;
      · apply Satisfies.imp_def₂.mpr; right; rintro y Rny;
        match y with
        | flat _ => apply h;
        | sharp _ => apply hn_max; simp only [sharp_to_sharp] at Rny; omega;
      · apply Satisfies.imp_def₂.mpr; left; apply Satisfies.box_def.not.mpr; push Not;
        refine ⟨sharp (n + 1), sharp_to_sharp.mpr (by omega), ?_⟩;
        have : Satisfies cresswellModel (sharp (n + 1)) φ := hn_max (n + 1) (by omega);
        have : ¬Satisfies cresswellModel (sharp (n + 1)) (Box.box φ) := by
          apply Satisfies.box_def.not.mpr; push Not;
          exact ⟨sharp n, sharp_to_sharp.mpr (by omega), hn⟩;
        apply Satisfies.iff_def.not.mpr; tauto;
  · push Not at h; obtain ⟨n, hn, hn_max⟩ := truthset.exists_min_flat h;
    have hn₁ : Satisfies cresswellModel (flat n) (Box.box φ) := by intro x Rnx;
      obtain ⟨m, ⟨rfl, hnm⟩⟩ := exists_flat_of_from_flat Rnx; exact hn_max m hnm;
    have hn₂ : ¬Satisfies cresswellModel (flat n) (LogicalConnective.iff (Box.box φ) φ) := by
      apply Satisfies.iff_def.not.mpr; push Not; tauto;
    match x with
    | sharp m => apply Satisfies.imp_def₂.mpr; left; apply Satisfies.box_def.not.mpr; push Not;
      exact ⟨flat n, sharp_to_flat, hn₂⟩;
    | flat m =>
      by_cases hmn : m > n; · intro h; have := @h (flat n) <| (flat_to_flat.mpr hmn); contradiction;
      · apply Satisfies.imp_def₂.mpr; right; rintro y Rmy;
        obtain ⟨k, ⟨rfl, hk₂⟩⟩ := exists_flat_of_from_flat Rmy; apply hn_max; omega;


-- @@ L354-365 expanded
lemma provable_KH_of_valid_cresswellModel : Provable Hilbert.KH φ → Realize cresswellModel φ := by
  intro h;
  induction h using Hilbert.Deduction.rec! with
  | maxm h =>
    rcases (by simpa using h) with (⟨_, rfl⟩ | ⟨_, rfl⟩); · exact Kripke.ValidOnModel.axiomK;
    · exact valid_axiomH_in_cresswellModel;
  | mdp ihφψ ihφ => exact Kripke.ValidOnModel.mdp ihφψ ihφ;
  | nec ihφ => exact Kripke.ValidOnModel.nec ihφ;
  | imply₁ => exact Kripke.ValidOnModel.imply₁;
  | imply₂ => exact Kripke.ValidOnModel.imply₂;
  | ec => exact Kripke.ValidOnModel.elimContra;


-- @@ L367-368 expanded
lemma KH_unprov_axiomFour : Unprovable Hilbert.KH (Axioms.Four (atom 0)) := fun hC =>
  not_valid_axiomFour_in_cresswellModel (provable_KH_of_valid_cresswellModel hC (sharp 2))


-- @@ L370-375 expanded
theorem KH_KripkeIncomplete :
    ¬∃ C : Kripke.FrameClass, ∀ φ, (Provable Hilbert.KH φ ↔ Realize C φ) :=
  by
  rintro ⟨C, h⟩; have : Realize C (Axioms.H (atom 0)) := @h (Axioms.H (atom 0)) |>.mp <| by simp;
  have : Realize C (Axioms.Four (atom 0)) := fun {F} hF =>
    valid_atomic_Four_of_valid_atomic_H (this hF);
  have : Provable Hilbert.KH (Axioms.Four (atom 0)) := @h (Axioms.Four (atom 0)) |>.mpr this;
  exact @KH_unprov_axiomFour this;


-- @@ L377-377 verbatim
end Kripke


-- @@ L379-379 verbatim
end Modal

-- @@ L380-380 verbatim
end LO
