module

public import Foundation.FirstOrder.Incompleteness.RosserProvability


-- @@ L5-5 verbatim
@[expose] public section


-- @@ L7-7 verbatim
namespace FFL.FirstOrder


-- @@ L9-9 verbatim
namespace ProvabilityAbstraction


-- @@ L11-11 verbatim
open FFL.Entailment FirstOrder Diagonalization Provability


-- @@ L13-13 verbatim
variable {L₀ L : Language}


-- @@ L15-17 verbatim
structure Refutability [L.ReferenceableBy L₀] (T₀ : Theory L₀) (T : Theory L) where
  refu : Semisentence L₀ 1
  refu_def {σ : Sentence L} : T ⊢ ∼σ → T₀ ⊢ refu/[⌜σ⌝]


-- @@ L19-19 verbatim
namespace Refutability


-- @@ L21-21 verbatim
variable [L.ReferenceableBy L₀] {T₀ : Theory L₀} {T : Theory L}


-- @@ L23-23 verbatim
@[coe] def rf (𝔚 : Refutability T₀ T) (σ : Sentence L) : Sentence L₀ := 𝔚.refu/[⌜σ⌝]

-- @@ L24-24 verbatim
instance : CoeFun (Refutability T₀ T) (fun _ ↦ Sentence L → Sentence L₀) := ⟨rf⟩


-- @@ L26-26 verbatim
end Refutability



-- @@ L29-29 verbatim
section


-- @@ L31-39 verbatim
variable
  {L₀ L : Language} [L.ReferenceableBy L₀]
  {T₀ : Theory L₀} {T : Theory L}

lemma R1 {𝔚 : Refutability T₀ T} {σ : Sentence L} : T ⊢ ∼σ → T₀ ⊢ 𝔚 σ := fun h ↦ 𝔚.refu_def h

lemma R1' {L : Language} [L.ReferenceableBy L] {T₀ T : Theory L}
  {𝔚 : Refutability T₀ T} {σ : Sentence L} [T₀ ⪯ T] : T ⊢ ∼σ → T ⊢ 𝔚 σ := fun h ↦
  WeakerThan.pbl $ R1 h


-- @@ L41-41 verbatim
end



-- @@ L44-44 verbatim
section


-- @@ L46-49 verbatim
variable
  [L.ReferenceableBy L] {T₀ T : Theory L}
  [Diagonalization T₀]
  {𝔚 : Refutability T₀ T}


-- @@ L51-56 verbatim
/-- This sentence is refutable. -/
def jeroslow (𝔚 : Refutability T₀ T) : Sentence L := fixedpoint T₀ 𝔚.refu

lemma jeroslow_def : T₀ ⊢ jeroslow 𝔚 🡘 𝔚 (jeroslow 𝔚) := Diagonalization.diag _

lemma jeroslow_def' [T₀ ⪯ T] : T ⊢ jeroslow 𝔚 🡘 𝔚 (jeroslow 𝔚) := WeakerThan.pbl $ jeroslow_def



-- @@ L59-61 verbatim
class Refutability.SoundOn (𝔚 : Refutability T₀ T) (σ : Sentence L) where
  sound_on : T ⊢ 𝔚 σ → T ⊢ ∼σ
alias Refutability.sound_on := Refutability.SoundOn.sound_on


-- @@ L63-63 verbatim
end



-- @@ L66-66 verbatim
section


-- @@ L68-77 verbatim
variable
  [L.ReferenceableBy L] {T₀ T : Theory L}
  [Diagonalization T₀]
  {𝔚 : Refutability T₀ T}

lemma unprovable_jeroslow [T₀ ⪯ T] [Consistent T] [𝔚.SoundOn (jeroslow 𝔚)] : T ⊬ jeroslow 𝔚 := by
  by_contra hC;
  apply Entailment.Consistent.not_bot (𝓢 := T);
  have : T ⊢ ∼(jeroslow 𝔚) := Refutability.sound_on $ (Entailment.iff_of_E $ jeroslow_def') |>.mp hC;
  exact (N_iff_CO.mp this) ⨀ hC;


-- @@ L79-79 verbatim
end



-- @@ L82-82 verbatim
section


-- @@ L84-87 verbatim
variable
  [L.ReferenceableBy L] {T₀ T : Theory L}
  [Diagonalization T₀]
  {𝔅 : Provability T₀ T} {𝔚 : Refutability T₀ T}


-- @@ L89-90 verbatim
/-- Formalized Law of Noncontradiction holds on `x` -/
def safe (𝔅 : Provability T₀ T) (𝔚 : Refutability T₀ T) : Semisentence L 1 := “x. ¬(!𝔅.prov x ∧ !𝔚.refu x)”


-- @@ L92-93 verbatim
/-- Formalized Law of Noncontradiction -/
def flon (𝔅 : Provability T₀ T) (𝔚 : Refutability T₀ T) : Sentence L := “∀ x, !(safe 𝔅 𝔚) x”


-- @@ L95-95 verbatim
end



-- @@ L98-98 verbatim
section


-- @@ L100-103 verbatim
variable
  [L.DecidableEq] [L.ReferenceableBy L] {T₀ T : Theory L}
  [Diagonalization T₀] [T₀ ⪯ T]
  {𝔅 : Provability T₀ T} {𝔚 : Refutability T₀ T}


-- @@ L105-110 verbatim
local notation "𝐉" => jeroslow 𝔚

lemma jeroslow_not_safe [𝔅.FormalizedCompleteOn 𝐉] : T ⊢ 𝐉 🡒 (𝔅 𝐉 ⋏ 𝔚 𝐉) := by
  have h₁ : T ⊢ 𝐉 🡒 𝔅 𝐉 := Entailment.WeakerThan.pbl $ 𝔅.formalized_complete_on;
  have h₂ : T ⊢ 𝐉 🡘 𝔚 𝐉 := jeroslow_def';
  cl_prover [h₁, h₂];


-- @@ L112-125 verbatim
/--
  Formalized law of noncontradiction cannot be proved.
  Alternative formulation of Gödel's second incompleteness theorem.
-/
lemma unprovable_flon [consis : Consistent T] [𝔅.FormalizedCompleteOn 𝐉] : T ⊬ flon 𝔅 𝔚 := by
  contrapose! consis;
  replace consis : T ⊢ ∀¹ safe 𝔅 𝔚 := by simpa [flon] using consis;
  have h₁ : T ⊢ ∼(𝔅 𝐉 ⋏ 𝔚 𝐉) := by simpa [safe] using! FirstOrder.Theory.Proof.specialize _ _ ⨀ consis;
  have h₂ : T ⊢ ∼𝐉 := (contra jeroslow_not_safe) ⨀ h₁;
  have h₃ : T ⊢ 𝐉 🡘 𝔚 𝐉 := jeroslow_def';
  have h₄ : T ⊢ 𝔚 𝐉 := R1' h₂;
  have h₅ : T ⊢ 𝔚 𝐉 🡒 𝐉 := by cl_prover [h₃];
  have h₆ : T ⊢ 𝐉 := h₅ ⨀ h₄;
  exact not_consistent_iff_inconsistent.mpr <| inconsistent_iff_provable_bot.mpr $ (N_iff_CO.mp h₂) ⨀ h₆;


-- @@ L127-127 verbatim
end


-- @@ L129-129 verbatim
end ProvabilityAbstraction


-- @@ L131-131 verbatim
end FFL.FirstOrder


-- @@ L133-133 verbatim
end
