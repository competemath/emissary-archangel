import OAI.Analysis.Unitarizability.Main
import Mathlib.Algebra.Group.Shrink
import Mathlib.Basic.Countable.Small


-- @@ L5-5 verbatim
namespace OAI


-- @@ L7-9 verbatim
/-! Countability lets a group be represented in any universe.
Transport by group equivalences preserves the positive normalized invariant mean
and the bounded nonunitarizable witness. -/

-- @@ L10-10 verbatim
noncomputable section

-- @@ L11-11 verbatim
namespace Dixmier

-- @@ L12-12 verbatim
universe u v w

-- @@ L13-13 verbatim
open scoped BoundedContinuousFunction

-- @@ L14-14 verbatim
variable {G : Type u} {Q : Type v} [Group G] [Group Q]

-- @@ L15-15 verbatim
variable [TopologicalSpace G] [DiscreteTopology G]

-- @@ L16-16 verbatim
variable [TopologicalSpace Q] [DiscreteTopology Q]


-- @@ L18-21 verbatim
def meanPullback (e : G ≃* Q) : (G →ᵇ ℂ) →ₗ[ℂ] (Q →ᵇ ℂ) where
  toFun f := f.compContinuous ⟨e.symm, continuous_of_discreteTopology⟩
  map_add' f h := by ext q; rfl
  map_smul' z f := by ext q; rfl


-- @@ L23-25 verbatim
omit [DiscreteTopology G] in
@[simp] theorem meanPullback_apply (e : G ≃* Q) (f : G →ᵇ ℂ) (q : Q) :
    meanPullback e f q = f (e.symm q) := rfl


-- @@ L27-40 verbatim
/-- Amenability transport uses the same positive normalized invariant mean. -/
theorem amenable_of_mulEquiv (e : G ≃* Q) (hQ : Amenable Q) : Amenable G := by
  rcases hQ with ⟨m, h1, hp, hi⟩
  refine ⟨m.comp (meanPullback e), ?_, ?_, ?_⟩
  · have hc : meanPullback e (BoundedContinuousFunction.const G 1) =
        BoundedContinuousFunction.const Q 1 := by ext q; rfl
    simpa only [LinearMap.comp_apply, hc] using h1
  · intro f hf
    exact hp _ (fun q => hf (e.symm q))
  · intro g f
    have hc : meanPullback e (leftTranslate g f) = leftTranslate (e g) (meanPullback e f) := by
      ext q
      simp [meanPullback_apply, leftTranslate, map_mul, map_inv]
    simpa only [LinearMap.comp_apply, hc] using hi (e g) (meanPullback e f)


-- @@ L42-52 verbatim
omit [TopologicalSpace G] [DiscreteTopology G] [TopologicalSpace Q] [DiscreteTopology Q] in
/-- Reindexing the group does not change the Hilbert space, bound or similarities. -/
theorem witness_of_mulEquiv (e : G ≃* Q) (hQ : NonamenableWitness.{v,w} Q) :
    NonamenableWitness.{u,w} G := by
  rcases hQ with ⟨H, hnorm, hinner, hcomplete, hsep, π, hb, hn⟩
  refine ⟨H, hnorm, hinner, hcomplete, hsep, π.comp e.toMonoidHom, fun g => hb (e g), ?_⟩
  rintro ⟨S, hS⟩
  apply hn
  refine ⟨S, ?_⟩
  intro q x
  simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, e.apply_symm_apply] using hS (e.symm q) x


-- @@ L54-63 verbatim
/-- The main theorem with independent group and Hilbert-space universes. -/
theorem main_theorem_all_universes : MainTheorem.{u,v} := by
  intro G _ _ _ _ hG
  let Q := Shrink.{v} G
  let e : G ≃* Q := Shrink.mulEquiv.symm
  let : Countable Q := e.surjective.countable
  let : TopologicalSpace Q := ⊥
  let : DiscreteTopology Q := ⟨rfl⟩
  have hQ : ¬ Amenable Q := fun h => hG (amenable_of_mulEquiv e h)
  exact witness_of_mulEquiv e (nonamenable_witness hQ)


-- @@ L65-69 verbatim
/-- Unitarizability implies amenability, with no uniform similarity bound. -/
theorem amenable_of_unitarizable_all_universes [Countable G]
    (h : Unitarizable.{u,v} G) : Amenable G := by
  by_contra hn
  exact witness_not_unitarizable (main_theorem_all_universes G hn) h


-- @@ L71-71 verbatim
end Dixmier


-- @@ L73-73 verbatim
end


-- @@ L75-75 verbatim
end OAI
