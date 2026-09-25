module

public import FltRegular.NumberTheory.CyclotomicRing


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-7 verbatim
open FiniteDimensional

-- @@ L8-8 verbatim
open NumberField


-- @@ L10-10 verbatim
variable (p : ℕ) (hp : Nat.Prime p)


-- @@ L12-12 verbatim
open Module Finset

-- @@ L13-13 verbatim
variable (G : Type*) [AddCommGroup G] (s : ℕ) (hf : finrank ℤ G = s * (p - 1))


-- @@ L15-15 verbatim
local notation "A" => (CyclotomicIntegers p)


-- @@ L17-17 verbatim
section


-- @@ L19-19 verbatim
variable [Module (CyclotomicIntegers p) G]


-- @@ L21-26 expanded
/-- A system of `s` units represented by a linearly independent family over cyclotomic integers. -/
structure systemOfUnits (s : ℕ) where
  /-- The family of units in the system. -/
  units : Fin s → G
  /-- The linear independence of the family over cyclotomic integers. -/
  linearIndependent : LinearIndependent (CyclotomicIntegers p) units


-- @@ L28-28 verbatim
namespace systemOfUnits


-- @@ L30-31 verbatim
lemma existence0 : Nonempty (systemOfUnits p G 0) :=
  ⟨⟨fun _ ↦ 0, linearIndependent_empty_type⟩⟩


-- @@ L33-33 verbatim
include hp


-- @@ L35-41 expanded
lemma finrank_spanA {R : ℕ} (f : Fin R → G) (hf : LinearIndependent (CyclotomicIntegers p) f) :
    finrank ℤ (Submodule.span (CyclotomicIntegers p) (Set.range f)) = (p - 1) * R :=
  by
  have := Fact.mk hp
  have := Module.Free.of_basis (Basis.span hf)
  have := Module.Finite.of_basis (Basis.span hf)
  rw [← finrank_mul_finrank ℤ (CyclotomicIntegers p), finrank_span_eq_card hf, Fintype.card_fin,
    PowerBasis.finrank (CyclotomicIntegers.powerBasis p), CyclotomicIntegers.powerBasis_dim]


-- @@ L43-43 verbatim
include hf


-- @@ L45-55 expanded
set_option backward.isDefEq.respectTransparency false in
lemma ex_not_mem [Module.Free ℤ G] {R : ℕ} (S : systemOfUnits p G R) (hR : R < s) :
    ∃ g, ∀ (k : ℤ), k ≠ 0 → ¬(k • g ∈ Submodule.span (CyclotomicIntegers p) (Set.range S.units)) :=
  by
  have := Fact.mk hp
  have : Module.Finite ℤ G :=
    Module.finite_of_finrank_pos (by simp [hf, R.zero_le.trans_lt hR, hp.one_lt])
  refine
    Submodule.exists_of_finrank_lt
      ((Submodule.span (CyclotomicIntegers p) (Set.range S.units)).restrictScalars ℤ) ?_
  change finrank ℤ (Submodule.span (CyclotomicIntegers p) _) < _
  rw [finrank_spanA p hp G S.units S.linearIndependent, hf, mul_comm]
  exact Nat.mul_lt_mul_of_lt_of_le hR rfl.le hp.pred_pos


-- @@ L57-57 verbatim
end systemOfUnits


-- @@ L59-59 verbatim
end


-- @@ L61-61 verbatim
namespace systemOfUnits


-- @@ L63-63 verbatim
include hp hf


-- @@ L65-65 verbatim
variable [Module.Free ℤ G]


-- @@ L67-80 expanded
lemma existence' [Module (CyclotomicIntegers p) G] {R : ℕ} (S : systemOfUnits p G R) (hR : R < s) :
    Nonempty (systemOfUnits p G (R + 1)) :=
  by
  obtain ⟨g, hg⟩ := ex_not_mem p hp G s hf S hR
  refine ⟨⟨Fin.cases g S.units, ?_⟩⟩
  refine LinearIndependent.finCons' g S.units S.linearIndependent (fun a y hy ↦ ?_)
  by_contra! ha
  have := Fact.mk hp
  obtain ⟨n, h0, f, Hf⟩ := CyclotomicIntegers.exists_dvd_int p _ ha.2
  have hy' := congr_arg (f • ·) ha.1
  rw [smul_zero, smul_add, smul_smul, mul_comm f, ← Hf, ← eq_neg_iff_add_eq_zero,
    Int.cast_smul_eq_zsmul] at hy'
  apply hg _ h0
  rw [hy']
  exact Submodule.neg_mem _ (Submodule.smul_mem _ _ hy)


-- @@ L82-87 expanded
lemma existence'' [Module (CyclotomicIntegers p) G] {R : ℕ} (hR : R ≤ s) :
    Nonempty (systemOfUnits p G R) := by
  induction R with
  | zero => exact existence0 p G
  | succ n ih =>
    obtain ⟨S⟩ := ih (le_trans (Nat.le_succ n) hR)
    exact existence' p hp G s hf S (lt_of_lt_of_le (Nat.lt_add_one n) hR)


-- @@ L89-89 expanded
lemma existence [Module (CyclotomicIntegers p) G] : Nonempty (systemOfUnits p G s) :=
  existence'' p hp G s hf rfl.le


-- @@ L91-91 verbatim
end systemOfUnits
