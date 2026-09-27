/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import LeanPool.JacobianDiffgeo.JacFunctorial.PullbackMaps
public import LeanPool.JacobianDiffgeo.ProperDegree.ChallengeDegree
import LeanPool.JacobianDiffgeo.JacFunctorial.TraceLaws
import Mathlib.CategoryTheory.Category.Init
import Mathlib.Combinatorics.Matroid.Init


-- @@ L14-30 verbatim
/-!
# Challenge-signature functoriality laws and the projection formula (jacobian-functoriality §9)

Unit: jacobian-functoriality. The remaining challenge exports
(`docs/Jacobian_challenge.lean:104-153`):

* `Jacobian.pullback_contMDiff` (free from `Jacobian.contMDiff_inducedHom`, inheriting the
  `[DiscreteTopology (periodSubgroup _).topologicalClosure]` gate transparently).
* `Jacobian.pushforward_id_apply` / `Jacobian.pushforward_comp_apply` and
  `Jacobian.pullback_id_apply` / `Jacobian.pullback_comp_apply` — via representative-level
  computation (`RS.Jacobian.inducedHom_apply_up_mk`) and the `Form1`-level laws
  (`Form1.pullback_id/comp`, `Form1.trace_id/comp`) transported through `dualMap`.
* `Jacobian.pushforward_pullback` — the projection formula, from
  `Form1.trace_pullback` (`Tr_f ∘ f^* = deg f`).

Same-universe convention throughout (see `PeriodMaps.lean`'s universe warning).
-/


-- @@ L32-32 verbatim
@[expose] public section


-- @@ L34-34 verbatim
open scoped ContDiff Manifold

-- @@ L35-35 verbatim
open IsManifold Module


-- @@ L37-37 verbatim
noncomputable section


-- @@ L39-39 verbatim
namespace RS


-- @@ L41-41 verbatim
universe u


-- @@ L43-44 verbatim
variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

-- @@ L45-46 verbatim
variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]


-- @@ L48-48 verbatim
/-! ### `pullback_contMDiff` -/


-- @@ L50-56 verbatim
/-- The pullback map on Jacobians is holomorphic (§9.1 — free from
`Jacobian.contMDiff_inducedHom`, same inherited gate as `pushforward_contMDiff`). -/
theorem Jacobian.pullback_contMDiff (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    [DiscreteTopology (RS.periodSubgroup X).topologicalClosure]
    [DiscreteTopology (RS.periodSubgroup Y).topologicalClosure] :
    ContMDiff 𝓘(ℂ, Fin (genus Y) → ℂ) 𝓘(ℂ, Fin (genus X) → ℂ) ω (Jacobian.pullback f hf) :=
  Jacobian.contMDiff_inducedHom (periodSubgroup_le_comap_pullbackT f hf)


-- @@ L58-58 verbatim
/-! ### Representative-level computation -/


-- @@ L60-64 verbatim
/-- Every point of the Jacobian is (the lift of) a residue class of an ambient vector. -/
theorem Jacobian.exists_rep (P : Jacobian X) :
    ∃ v : Fin (genus X) → ℂ, P = ULift.up (QuotientAddGroup.mk v) := by
  obtain ⟨v, hv⟩ := QuotientAddGroup.mk_surjective P.down
  exact ⟨v, by rw [hv]⟩


-- @@ L66-81 verbatim
/-- `Jacobian.inducedHom` on representatives. -/
theorem Jacobian.inducedHom_apply_up_mk
    {T : (Fin (genus X) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ)}
    (hT : RS.periodSubgroup X ≤ (RS.periodSubgroup Y).topologicalClosure.comap
      T.toAddMonoidHom) (v : Fin (genus X) → ℂ) :
    Jacobian.inducedHom hT (ULift.up (QuotientAddGroup.mk v))
      = ULift.up (QuotientAddGroup.mk (T v)) := by
  have h : Jacobian.inducedHom hT (ULift.up (QuotientAddGroup.mk v))
      = RS.uliftUpHom (RS.inducedHom (RS.periodSubgroup X).topologicalClosure
          (RS.periodSubgroup Y).topologicalClosure T
          (AddSubgroup.topologicalClosure_minimal (RS.periodSubgroup X) hT
            (((RS.periodSubgroup Y).isClosed_topologicalClosure).preimage
              T.continuous_of_finiteDimensional))
          (RS.uliftDownHom ((ULift.up (QuotientAddGroup.mk v)) : Jacobian X))) := rfl
  rw [h]
  simp [RS.inducedHom_apply_mk]


-- @@ L83-83 verbatim
/-! ### `T`-level functoriality -/


-- @@ L85-90 verbatim
omit [ConnectedSpace X] in
theorem pushforwardT_id : pushforwardT (id : X → X) contMDiff_id = LinearMap.id := by
  unfold pushforwardT
  rw [Form1.pullback_id, LinearMap.dualMap_id]
  ext v i
  simp


-- @@ L92-96 verbatim
theorem pullbackT_id : pullbackT (id : X → X) contMDiff_id = LinearMap.id := by
  unfold pullbackT
  rw [Form1.trace_id, LinearMap.dualMap_id]
  ext v i
  simp


-- @@ L98-99 verbatim
variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ) ω Z]


-- @@ L101-108 verbatim
omit [ConnectedSpace X] [ConnectedSpace Y] [ConnectedSpace Z] in
theorem pushforwardT_comp (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    pushforwardT (g ∘ f) (hg.comp hf) = (pushforwardT g hg).comp (pushforwardT f hf) := by
  unfold pushforwardT
  rw [Form1.pullback_comp f hf g hg, ← LinearMap.dualMap_comp_dualMap]
  ext v i
  simp


-- @@ L110-117 verbatim
omit [ConnectedSpace Z] in
theorem pullbackT_comp (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) :
    pullbackT (g ∘ f) (hg.comp hf) = (pullbackT f hf).comp (pullbackT g hg) := by
  unfold pullbackT
  rw [Form1.trace_comp f hf g hg, ← LinearMap.dualMap_comp_dualMap]
  ext v i
  simp


-- @@ L119-134 verbatim
/-- The composed period map of `pullback` then `pushforward` is multiplication by the degree
(the `T`-level projection formula, from `Form1.trace_pullback`). -/
theorem pushforwardT_pullbackT_apply (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (v : Fin (genus Y) → ℂ) :
    pushforwardT f hf (pullbackT f hf v) = (ContMDiff.degree f hf : ℂ) • v := by
  funext i
  change periodCoordEquiv Y ((Form1.pullback f hf).dualMap
      ((periodCoordEquiv X).symm (periodCoordEquiv X ((Form1.trace f hf).dualMap
        ((periodCoordEquiv Y).symm v))))) i = _
  rw [(periodCoordEquiv X).symm_apply_apply, periodCoordEquiv_apply,
    LinearMap.dualMap_apply, LinearMap.dualMap_apply, Form1.trace_pullback f hf (basis Y i),
    map_smul]
  have hbase : ((periodCoordEquiv Y).symm v) (RS.basis Y i) = v i := by
    rw [← periodCoordEquiv_apply, (periodCoordEquiv Y).apply_symm_apply]
  rw [hbase]
  simp


-- @@ L136-136 verbatim
/-! ### The challenge laws -/


-- @@ L138-143 verbatim
theorem Jacobian.pushforward_id_apply (P : Jacobian X) :
    Jacobian.pushforward id contMDiff_id P = P := by
  obtain ⟨v, rfl⟩ := Jacobian.exists_rep P
  change Jacobian.inducedHom _ (ULift.up (QuotientAddGroup.mk v)) = _
  rw [Jacobian.inducedHom_apply_up_mk, pushforwardT_id]
  rfl


-- @@ L145-150 verbatim
theorem Jacobian.pullback_id_apply (P : Jacobian X) :
    Jacobian.pullback id contMDiff_id P = P := by
  obtain ⟨v, rfl⟩ := Jacobian.exists_rep P
  change Jacobian.inducedHom _ (ULift.up (QuotientAddGroup.mk v)) = _
  rw [Jacobian.inducedHom_apply_up_mk, pullbackT_id]
  rfl


-- @@ L152-162 verbatim
theorem Jacobian.pushforward_comp_apply (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) (P : Jacobian X) :
    Jacobian.pushforward (g ∘ f) (hg.comp hf) P
      = Jacobian.pushforward g hg (Jacobian.pushforward f hf P) := by
  obtain ⟨v, rfl⟩ := Jacobian.exists_rep P
  change Jacobian.inducedHom _ (ULift.up (QuotientAddGroup.mk v))
    = Jacobian.pushforward g hg (Jacobian.inducedHom _ (ULift.up (QuotientAddGroup.mk v)))
  rw [Jacobian.inducedHom_apply_up_mk, Jacobian.inducedHom_apply_up_mk]
  change _ = Jacobian.inducedHom _ (ULift.up (QuotientAddGroup.mk (pushforwardT f hf v)))
  rw [Jacobian.inducedHom_apply_up_mk, pushforwardT_comp f hf g hg]
  rfl


-- @@ L164-174 verbatim
theorem Jacobian.pullback_comp_apply (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω g) (P : Jacobian Z) :
    Jacobian.pullback (g.comp f) (hg.comp hf) P
      = Jacobian.pullback f hf (Jacobian.pullback g hg P) := by
  obtain ⟨v, rfl⟩ := Jacobian.exists_rep P
  change Jacobian.inducedHom _ (ULift.up (QuotientAddGroup.mk v))
    = Jacobian.pullback f hf (Jacobian.inducedHom _ (ULift.up (QuotientAddGroup.mk v)))
  rw [Jacobian.inducedHom_apply_up_mk, Jacobian.inducedHom_apply_up_mk]
  change _ = Jacobian.inducedHom _ (ULift.up (QuotientAddGroup.mk (pullbackT g hg v)))
  rw [Jacobian.inducedHom_apply_up_mk, pullbackT_comp f hf g hg]
  rfl


-- @@ L176-196 verbatim
/-- **The projection formula on Jacobians**: `pushforward f ∘ pullback f = deg f`
(`docs/Jacobian_challenge.lean:151-152`). -/
theorem Jacobian.pushforward_pullback (f : X → Y) (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f)
    (P : Jacobian Y) :
    Jacobian.pushforward f hf (Jacobian.pullback f hf P) = (ContMDiff.degree f hf) • P := by
  obtain ⟨v, rfl⟩ := Jacobian.exists_rep P
  change Jacobian.pushforward f hf (Jacobian.inducedHom _ (ULift.up (QuotientAddGroup.mk v)))
    = _
  rw [Jacobian.inducedHom_apply_up_mk]
  change Jacobian.inducedHom _ (ULift.up (QuotientAddGroup.mk (pullbackT f hf v))) = _
  rw [Jacobian.inducedHom_apply_up_mk, pushforwardT_pullbackT_apply f hf v,
    Nat.cast_smul_eq_nsmul]
  have h1 : QuotientAddGroup.mk (s := (RS.periodSubgroup Y).topologicalClosure)
      (ContMDiff.degree f hf • v)
      = ContMDiff.degree f hf • QuotientAddGroup.mk
          (s := (RS.periodSubgroup Y).topologicalClosure) v := by
    exact map_nsmul (QuotientAddGroup.mk' _) (ContMDiff.degree f hf) v
  rw [h1]
  exact map_nsmul (RS.uliftUpHom.toAddMonoidHom
    (A := (Fin (genus Y) → ℂ) ⧸ (RS.periodSubgroup Y).topologicalClosure))
    (ContMDiff.degree f hf) _


-- @@ L198-198 verbatim
end RS


-- @@ L200-200 verbatim
end
