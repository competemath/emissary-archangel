module

public import Foundation.FirstOrder.Incompleteness.Examples
public import Foundation.Vorspiel.ENat


-- @@ L6-6 verbatim
@[expose] public section

-- @@ L7-7 verbatim
namespace FFL.FirstOrder


-- @@ L9-9 verbatim
variable {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L}


-- @@ L11-11 verbatim
open ProvabilityAbstraction

-- @@ L12-12 verbatim
open Classical


-- @@ L14-14 verbatim
namespace ProvabilityAbstraction


-- @@ L16-16 verbatim
variable {𝔅 : Provability T₀ T}


-- @@ L18-18 verbatim
noncomputable def Provability.height (𝔅 : Provability T₀ T) : ENat := ENat.find (T ⊢ 𝔅^[·] ⊥)


-- @@ L20-47 verbatim
@[simp]
lemma neg_iterated_prov (φ : Sentence L) : ∼(𝔅^[n] φ) = 𝔅.dia^[n] (∼φ) := by
  induction n generalizing φ <;> simp [Provability.dia, *]

lemma boxBot_monotone [T₀ ⪯ T] [𝔅.HBL] : n ≤ m → T ⊢ 𝔅^[n] ⊥ 🡒 𝔅^[m] ⊥ := by
  revert m
  suffices ∀ k, T ⊢ 𝔅^[n] ⊥ 🡒 𝔅^[n + k] ⊥ by
    intro m hnm
    simpa [Nat.add_sub_of_le hnm] using this (m - n)
  intro k
  induction k
  case zero => simp
  case succ k ih =>
    simp only [← add_assoc, Function.iterate_succ_apply']
    have b₀ : T ⊢ 𝔅^[n] ⊥ 🡒 𝔅 (𝔅^[n] ⊥) := by
      match n with
      | 0 => simp;
      | n + 1 =>
        have : T ⊢ 𝔅 ((𝔅)^[n] ⊥) 🡒 𝔅 (𝔅 ((𝔅)^[n] ⊥)) := Entailment.WeakerThan.pbl $ 𝔅.D3;
        simpa only [Function.iterate_succ_apply'] using this
    have b₁ : T ⊢ 𝔅 (𝔅^[n] ⊥) 🡒 𝔅 (𝔅^[n + k] ⊥) := Entailment.WeakerThan.pbl $ 𝔅.mono ih;
    cl_prover [b₀, b₁]

lemma iIncon_unprovable_of_sigma1_sound [𝔅.Kreisel] [Entailment.Consistent T] : ∀ n, T ⊬ 𝔅^[n] ⊥
  |     0 => Entailment.consistent_iff_unprovable_bot.mp inferInstance
  | n + 1 => fun h ↦
    have : T ⊢ 𝔅 (𝔅^[n] ⊥) := by simpa [Function.iterate_succ_apply'] using h
    iIncon_unprovable_of_sigma1_sound n <| 𝔅.KR this



-- @@ L50-78 verbatim
namespace Provability


lemma height_eq_top_iff : 𝔅.height = ⊤ ↔ ∀ n, T ⊬ 𝔅^[n] ⊥ := ENat.find_eq_top_iff _

lemma height_le_of_boxBot {n : ℕ} (h : T ⊢ 𝔅^[n] ⊥) : 𝔅.height ≤ n :=
  ENat.find_le (T ⊢ 𝔅^[·] ⊥) n h

lemma height_lt_pos_of_boxBot (hSound : ∀ {σ}, T₀ ⊢ 𝔅 σ → T ⊢ σ)
  {n : ℕ} (pos : 0 < n) (h : T₀ ⊢ 𝔅^[n] ⊥) : 𝔅.height < n := by
  have e : n.pred.succ = n := Eq.symm <| (Nat.sub_eq_iff_eq_add pos).mp rfl
  have : T₀ ⊢ 𝔅 (𝔅^[n.pred] ⊥) := by rwa [←Function.iterate_succ_apply' (f := 𝔅), e];
  have : 𝔅.height ≤ n.pred := height_le_of_boxBot $ hSound this
  have : 𝔅.height < n := by
    rw [←e]
    exact lt_of_le_of_lt this <| ENat.natCast_lt_natCast.mpr <| by simp
  exact this

lemma height_le_iff_boxBot [T₀ ⪯ T] [𝔅.HBL] {n : ℕ} :
    𝔅.height ≤ n ↔ T ⊢ 𝔅^[n] ⊥ := by
  constructor
  · intro h
    have : ∃ m ≤ n, T ⊢ (↑𝔅)^[m] ⊥ := ENat.exists_of_find_le _ n h
    rcases this with ⟨m, hmn, hm⟩
    exact boxBot_monotone hmn ⨀ hm
  · exact height_le_of_boxBot

lemma height_eq_top_of_sound_and_consistent [𝔅.Kreisel] [Entailment.Consistent T] : 𝔅.height = ⊤ :=
  height_eq_top_iff.mpr iIncon_unprovable_of_sigma1_sound


-- @@ L80-83 verbatim
@[grind =>]
lemma height_eq_zero_of_inconsistent (h : Entailment.Inconsistent T) : 𝔅.height = 0 := by
  suffices 𝔅.height ≤ 0 from nonpos_iff_eq_zero.mp this
  simpa using height_le_of_boxBot (n := 0) (h ⊥)


-- @@ L85-85 verbatim
end Provability


-- @@ L87-87 verbatim
end ProvabilityAbstraction



-- @@ L90-90 verbatim
open ProvabilityAbstraction


-- @@ L92-92 verbatim
noncomputable abbrev ArithmeticTheory.height (T : ArithmeticTheory) [T.Δ₁] : ℕ∞ := T.standardProvability.height


-- @@ L94-94 verbatim
namespace Arithmetic


-- @@ L96-98 verbatim
@[grind =]
lemma height_eq_top_of_sigma1_sound (T : ArithmeticTheory) [T.Δ₁] [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : T.height = ⊤ :=
  T.standardProvability.height_eq_top_of_sound_and_consistent


-- @@ L100-101 verbatim
@[simp, grind =]
lemma ISigma1_height_eq_top : 𝗜𝚺₁.height = ⊤ := height_eq_top_of_sigma1_sound 𝗜𝚺₁


-- @@ L103-104 verbatim
@[simp, grind =]
lemma Peano_height_eq_top : 𝗣𝗔.height = ⊤ := height_eq_top_of_sigma1_sound 𝗣𝗔


-- @@ L106-106 verbatim
end Arithmetic


-- @@ L108-108 verbatim
end FFL.FirstOrder
