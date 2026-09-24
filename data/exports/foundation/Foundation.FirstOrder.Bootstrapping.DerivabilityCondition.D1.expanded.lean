module

public import Foundation.FirstOrder.Bootstrapping.Syntax


-- @@ L5-5 verbatim
@[expose] public section

-- @@ L6-8 verbatim
/-!
# Hilbert-Bernays-Löb derivability condition $\mathbf{D1}$ and soundness of internal provability.
-/


-- @@ L10-10 verbatim
namespace FFL.FirstOrder.Arithmetic.Bootstrapping


-- @@ L12-12 verbatim
open Classical FirstOrder


-- @@ L14-14 verbatim
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]


-- @@ L16-16 verbatim
variable {L : Language} [L.Encodable] [L.LORDefinable]


-- @@ L18-21 verbatim
variable {T : Theory L} [T.Δ₁]

lemma derivable_quote {Γ : Finset (Proposition L)} (d : T ⟹₂ Γ) : Derivable T (⌜Γ⌝ : V) :=
  ⟨⌜d⌝, by simpa [Semiformula.quote_def] using! (⌜d⌝ : Theory.internalize V T ⊢!ᵈᵉʳ ⌜Γ⌝).derivationOf⟩


-- @@ L23-25 verbatim
/-- Hilbert–Bernays provability condition D1 -/
theorem internalize_provability {φ} : T ⊢ φ → Provable T (⌜φ⌝ : V) := fun h ↦ by
  simpa using! derivable_quote (V := V) (provable_iff_derivable2.mp h).some


-- @@ L27-28 verbatim
theorem internal_provable_of_outer_provable {φ} : T ⊢ φ → T.internalize V ⊢ ⌜φ⌝ := fun h ↦ by
  simpa [TProvable.iff_provable] using! internalize_provability (V := V) h


-- @@ L30-32 verbatim
@[simp] lemma Provable.complete {φ : Sentence L} :
    T.internalize ℕ ⊢ ⌜φ⌝ ↔ T ⊢ φ :=
  ⟨by simpa [TProvable.iff_provable] using! Provable.sound, internal_provable_of_outer_provable⟩


-- @@ L34-35 verbatim
@[simp] lemma provable_iff_provable {T : Theory L} [T.Δ₁] {φ : Sentence L} :
    Provable T (⌜φ⌝ : ℕ) ↔ T ⊢ φ := by simpa [TProvable.iff_provable] using! Provable.complete


-- @@ L37-37 verbatim
end FFL.FirstOrder.Arithmetic.Bootstrapping
