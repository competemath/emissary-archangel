/-
Copyright (c) 2025 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import QuantumInfo.Channels.Unbundled
public import QuantumInfo.States.Mixed.MState

public import Mathlib.Topology.Order.Hom.Basic


-- @@ L13-23 verbatim
/-! # Classes of Matrix Maps

The bundled `MatrixMap`s: `HPMap`, `UnitalMap`, `TPMap`, `PMap`, and `CPMap`.
These are defined over the bare minimum rings (`Semiring` or `RCLike`, respectively).

The combinations `PTPMap` (positive trace-preserving), `CPTPMap`, and `CPUMap`
(CP unital maps) take ℂ as the default class.

The majority of quantum theory revolves around `CPTPMap`s, so those are explored more
thoroughly in their file CPTP.lean.
-/


-- @@ L25-25 verbatim
@[expose] public section



-- @@ L28-28 verbatim
variable (dIn dOut R : Type*) (𝕜 : Type := ℂ)

-- @@ L29-29 verbatim
variable [Semiring R] [RCLike 𝕜]


-- @@ L31-33 verbatim
/-- Hermitian-preserving linear maps. -/
structure HPMap extends MatrixMap dIn dOut 𝕜 where
  HP : MatrixMap.IsHermitianPreserving toLinearMap


-- @@ L35-38 verbatim
/-- Unital linear maps. -/
structure UnitalMap [DecidableEq dIn] [DecidableEq dOut]
    extends MatrixMap dIn dOut R where
  unital : MatrixMap.Unital toLinearMap


-- @@ L40-46 verbatim
/-- Trace-preserving linear maps. -/
structure TPMap [Fintype dIn] [Fintype dOut] extends MatrixMap dIn dOut R where
  TP : MatrixMap.IsTracePreserving toLinearMap

--Mark this as [simp] so that simp lemmas requiring `IsTracePreserving` can pick it up.
--In theory this could be making "IsTracePreserving" a typeclass ... or more realistically,
--defining a `TracePreservingClass` similar to `AddHomClass`

-- @@ L47-47 verbatim
attribute [simp] TPMap.TP


-- @@ L49-53 verbatim
/-- Positive linear maps. -/
structure PMap [Fintype dIn] [Fintype dOut]
    extends HPMap dIn dOut 𝕜 where
  pos : MatrixMap.IsPositive toLinearMap
  HP := pos.IsHermitianPreserving


-- @@ L55-59 verbatim
/-- Completely positive linear maps. -/
structure CPMap [Fintype dIn] [Fintype dOut] [DecidableEq dIn]
    extends PMap dIn dOut 𝕜 where
  cp : MatrixMap.IsCompletelyPositive toLinearMap
  pos := cp.IsPositive


-- @@ L61-64 verbatim
/-- Positive trace-preserving linear maps. These includes all channels, but aren't
  necessarily *completely* positive, see `CPTPMap`. -/
structure PTPMap [Fintype dIn] [Fintype dOut]
  extends PMap dIn dOut 𝕜, TPMap dIn dOut 𝕜


-- @@ L66-69 verbatim
/-- Positive unital maps. These are important because they are the
  dual to `PTPMap`: they are the most general way to map *observables*. -/
structure PUMap [Fintype dIn] [Fintype dOut] [DecidableEq dIn] [DecidableEq dOut]
  extends PMap dIn dOut 𝕜, UnitalMap dIn dOut 𝕜


-- @@ L71-71 verbatim
attribute [simp] PTPMap.TP


-- @@ L73-77 verbatim
/-- Completely positive trace-preserving linear maps. This is the most common
  meaning of "channel", often described as "the most general physically realizable
  quantum operation". -/
structure CPTPMap [Fintype dIn] [Fintype dOut] [DecidableEq dIn]
  extends PTPMap dIn dOut (𝕜 := 𝕜), CPMap dIn dOut 𝕜 where


-- @@ L79-82 verbatim
/-- Completely positive unital maps. These are important because they are the
  dual to `CPTPMap`: they are the physically realizable ways to map *observables*. -/
structure CPUMap [Fintype dIn] [Fintype dOut] [DecidableEq dIn] [DecidableEq dOut]
  extends CPMap dIn dOut 𝕜, PUMap dIn dOut 𝕜


-- @@ L84-84 verbatim
variable {dIn dOut R} {𝕜 : Type} [RCLike 𝕜]


-- @@ L86-92 verbatim
/-!

## Hermitian-preserving maps

-/

--Hermitian-presering maps: continuous linear maps on HermitianMats.

-- @@ L93-93 verbatim
namespace HPMap

-- @@ L94-94 verbatim
variable {Λ₁ Λ₂ : HPMap dIn dOut 𝕜}

-- @@ L95-95 verbatim
variable {CΛ₁ CΛ₂ : HPMap dIn dOut ℂ}


-- @@ L97-97 verbatim
abbrev map (M : HPMap dIn dOut 𝕜) : MatrixMap dIn dOut 𝕜 := M.toLinearMap


-- @@ L99-101 verbatim
@[ext]
theorem ext (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rwa [HPMap.mk.injEq]


-- @@ L103-111 verbatim
/-- Two maps are equal if they agree on all Hermitian inputs. -/
theorem funext_hermitian (h : ∀ M : HermitianMat dIn ℂ, CΛ₁.map M = CΛ₂.map M) :
    CΛ₁ = CΛ₂ := by
  ext M : 2
  have hH := h (realPart M)
  have hA := h (imaginaryPart M)
  convert congr($hH + Complex.I • $hA)
  <;> rw (occs := [1]) [← realPart_add_I_smul_imaginaryPart M, map_add, map_smul]
  <;> rfl


-- @@ L113-121 verbatim
/-- Two maps are equal if they agree on all positive inputs. -/
theorem funext_pos [Fintype dIn] (h : ∀ M : HermitianMat dIn ℂ, 0 ≤ M → CΛ₁.map M = CΛ₂.map M) :
    CΛ₁ = CΛ₂ := by
  classical
  open scoped HermitianMat in
  apply funext_hermitian
  intro M
  rw [← M.posPart_add_negPart]
  simp [HermitianMat.posPart_nonneg, HermitianMat.negPart_nonneg, h]


-- @@ L123-142 verbatim
/-- Two maps are equal if they agree on all positive inputs with trace one -/
theorem funext_pos_trace [Fintype dIn]
  (h : ∀ M : HermitianMat dIn ℂ, 0 ≤ M → M.trace = 1 → CΛ₁.map M = CΛ₂.map M) :
    CΛ₁ = CΛ₂ := by
  apply funext_pos
  intro M hM'
  rcases hM'.eq_or_lt with rfl | hM
  · simp
  have h_tr : 0 < M.trace := M.trace_pos hM
  have := h (M.trace⁻¹ • M) ?_ ?_
  · simp only [HermitianMat.mat_smul, LinearMap.map_smul_of_tower] at this
    convert congr(M.trace • $this)
    · rw [smul_smul]
      field_simp
      simp
    · rw [smul_smul]
      field_simp
      simp
  · apply smul_nonneg (by positivity) hM'
  · simp [field]


-- @@ L144-148 verbatim
/-- Two maps are equal if they agree on all `MState`s. -/
theorem funext_mstate [Fintype dIn] [DecidableEq dIn] {Λ₁ Λ₂ : HPMap dIn dOut ℂ}
  (h : ∀ ρ : MState dIn, Λ₁.map ρ.m = Λ₂.map ρ.m) :
    Λ₁ = Λ₂ :=
  funext_pos_trace fun M hM_pos hM_tr ↦ h ⟨M, hM_pos, hM_tr⟩


-- @@ L150-154 verbatim
/-- Hermitian-preserving maps are functions from `HermitianMat`s to `HermitianMat`s. -/
noncomputable instance instFunLike : FunLike (HPMap dIn dOut ℂ) (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  coe Λ ρ := ⟨Λ.map ρ.1, Λ.HP ρ.2⟩
  coe_injective x y h := funext_hermitian fun M ↦
    by simpa using congrFun h M


-- @@ L156-157 verbatim
lemma apply_hermitianMat_eq (Λ : HPMap dIn dOut ℂ) (ρ : HermitianMat dIn ℂ) :
    Λ ρ = ⟨Λ.map ρ.1, Λ.HP ρ.2⟩ := rfl


-- @@ L159-164 verbatim
set_option backward.isDefEq.respectTransparency false in
instance [Fintype dIn] : ContinuousLinearMapClass
    (HPMap dIn dOut ℂ) ℝ (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.toLinearMap x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp [apply_hermitianMat_eq]
  map_continuous f := .subtype_mk (by fun_prop) _


-- @@ L166-166 verbatim
end HPMap


-- @@ L168-168 verbatim
variable [Fintype dIn] [Fintype dOut]


-- @@ L170-176 verbatim
/-!

## Positive-preserving maps

-/

--Positive-preserving maps: continuous linear order-preserving maps on HermitianMats.

-- @@ L177-177 verbatim
namespace PMap


-- @@ L179-182 verbatim
@[ext]
theorem ext {Λ₁ Λ₂ : PMap dIn dOut 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rw [PMap.mk.injEq]
  exact HPMap.ext h


-- @@ L184-185 verbatim
theorem injective_toHPMap : (PMap.toHPMap (dIn := dIn) (dOut := dOut) (𝕜 := 𝕜)).Injective :=
  fun _ _ ↦ (mk.injEq _ _ _ _).mpr


-- @@ L187-190 verbatim
/-- Positive maps are functions from `HermitianMat`s to `HermitianMat`s. -/
noncomputable instance instFunLike : FunLike (PMap dIn dOut ℂ) (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  coe := DFunLike.coe ∘ toHPMap
  coe_injective := DFunLike.coe_injective.comp injective_toHPMap


-- @@ L192-193 verbatim
lemma apply_hermitianMat_eq (Λ : PMap dIn dOut ℂ) (ρ : HermitianMat dIn ℂ) :
    Λ ρ = ⟨Λ.map ρ.1, Λ.HP ρ.2⟩ := rfl


-- @@ L195-199 verbatim
set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 40000 in
instance instLinearMapClass : LinearMapClass (PMap dIn dOut ℂ) ℝ (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.toLinearMap x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp [apply_hermitianMat_eq]


-- @@ L201-207 verbatim
instance instContinuousOrderHomClass : ContinuousOrderHomClass (PMap dIn dOut ℂ)
    (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_continuous f := ContinuousMapClass.map_continuous f.toHPMap
  map_monotone f x y h := by
    have h1 := f.pos h
    simp_all only [HermitianMat.val_eq_coe, map_sub, ge_iff_le]
    exact h1


-- @@ L209-212 verbatim
/-- Positive-presering maps also preserve positivity on, specifically, Hermitian matrices. -/
@[simp]
theorem pos_Hermitian (M : PMap dIn dOut ℂ) {x : HermitianMat dIn ℂ} (h : 0 ≤ x) : 0 ≤ M x := by
  simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h


-- @@ L214-214 verbatim
end PMap


-- @@ L216-216 verbatim
namespace CPMap


-- @@ L218-220 verbatim
def of_kraus_CPMap {κ : Type*} [Fintype κ] [DecidableEq dIn] (M : κ → Matrix dOut dIn 𝕜) : CPMap dIn dOut 𝕜 where
  toLinearMap := MatrixMap.of_kraus M M
  cp := MatrixMap.of_kraus_isCompletelyPositive M


-- @@ L222-222 verbatim
end CPMap


-- @@ L224-231 verbatim
/-!

## Positive trace-preserving maps

-/
--Positive trace-preserving maps:
--  * Continuous linear order-preserving maps on HermitianMats.
--  * Continuous maps on MStates.

-- @@ L232-232 verbatim
namespace PTPMap


-- @@ L234-237 verbatim
@[ext]
theorem ext {Λ₁ Λ₂ : PTPMap dIn dOut 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rw [PTPMap.mk.injEq]
  exact PMap.ext h


-- @@ L239-240 verbatim
theorem injective_toPMap : (PTPMap.toPMap (dIn := dIn) (dOut := dOut) (𝕜 := 𝕜)).Injective :=
  fun _ _ ↦ (mk.injEq _ _ _ _).mpr


-- @@ L242-245 verbatim
/-- Positive trace-preserving maps are functions from `HermitianMat`s to `HermitianMat`s. -/
noncomputable instance instFunLike : FunLike (PTPMap dIn dOut ℂ) (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  coe := DFunLike.coe ∘ toPMap
  coe_injective := DFunLike.coe_injective.comp injective_toPMap


-- @@ L247-248 verbatim
lemma apply_hermitianMat_eq_toPMap (Λ : PTPMap dIn dOut ℂ) (ρ : HermitianMat dIn ℂ) :
    Λ ρ = Λ.toPMap ρ := rfl


-- @@ L250-252 verbatim
instance instLinearMapClass : LinearMapClass (PTPMap dIn dOut ℂ) ℝ (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_add f x y := by simp [apply_hermitianMat_eq_toPMap]
  map_smulₛₗ f c x := by simp [apply_hermitianMat_eq_toPMap]


-- @@ L254-260 verbatim
instance instHContinuousOrderHomClass : ContinuousOrderHomClass (PTPMap dIn dOut ℂ)
    (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_continuous f := ContinuousMapClass.map_continuous f.toPMap
  map_monotone f x y h := by
    have := f.pos h
    simp_all only [HermitianMat.val_eq_coe, map_sub, ge_iff_le]
    exact this


-- @@ L262-265 verbatim
/-- PTP maps also preserve positivity on Hermitian matrices. -/
@[simp]
theorem pos_Hermitian (M : PTPMap dIn dOut ℂ) {x : HermitianMat dIn ℂ} (h : 0 ≤ x) : 0 ≤ M x := by
  simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h


-- @@ L267-277 verbatim
/-- `PTPMap`s are functions from `MState`s to `MState`s. -/
noncomputable instance instMFunLike [DecidableEq dIn] [DecidableEq dOut] :
    FunLike (PTPMap dIn dOut) (MState dIn) (MState dOut) where
  coe Λ ρ := MState.mk
    (Λ.toHPMap ρ.M) (HermitianMat.zero_le_iff.mpr (Λ.pos ρ.psd)) (by
      rw [HermitianMat.trace_eq_one_iff, ← ρ.tr']
      exact Λ.TP ρ)
  coe_injective x y h := injective_toPMap <| PMap.injective_toHPMap <|
    HPMap.funext_mstate fun ρ ↦ by
      have := congr($h ρ);
      rwa [MState.ext_iff, HermitianMat.ext_iff] at this


-- @@ L279-283 verbatim
lemma apply_mstate_eq [DecidableEq dIn] [DecidableEq dOut] (Λ : PTPMap dIn dOut ℂ) (ρ : MState dIn) :
    Λ ρ = MState.mk
      (Λ.toHPMap ρ.M) (HermitianMat.zero_le_iff.mpr (Λ.pos ρ.psd)) (by
        rw [HermitianMat.trace_eq_one_iff, ← ρ.tr']
        exact Λ.TP ρ) := rfl


-- @@ L285-291 verbatim
instance instMContinuousMapClass [DecidableEq dIn] [DecidableEq dOut] :
    ContinuousMapClass (PTPMap dIn dOut) (MState dIn) (MState dOut) where
  map_continuous f := by
    rw [continuous_induced_rng]
    exact (map_continuous f.toHPMap).comp MState.Continuous_HermitianMat

-- @[norm_cast]

-- @@ L292-298 verbatim
theorem val_apply_MState [DecidableEq dIn] (M : PTPMap dIn dOut) (ρ : MState dIn) :
    (M ρ : HermitianMat dOut ℂ) = (instFunLike.coe M) ρ := by
  rfl

--If we have a PTPMap, the input and output dimensions are always both nonempty (otherwise
--we can't preserve trace) - or they're both empty. So `[Nonempty dIn]` will always suffice.
-- This would be nice as an `instance` but that would leave `dIn` as a metavariable.

-- @@ L299-307 verbatim
theorem nonemptyOut (Λ : PTPMap dIn dOut) [hIn : Nonempty dIn] [DecidableEq dIn] : Nonempty dOut := by
  by_contra h
  simp only [not_nonempty_iff] at h
  let M := (1 : Matrix dIn dIn ℂ)
  have := calc (Finset.univ.card (α := dIn) : ℂ)
    _ = M.trace := by simp [Matrix.trace, M]
    _ = (Λ.map M).trace := (Λ.TP M).symm
    _ = 0 := by simp only [Matrix.trace_eq_zero_of_isEmpty]
  norm_num [Finset.univ_eq_empty_iff] at this


-- @@ L309-309 verbatim
end PTPMap


-- @@ L311-315 verbatim
/-!

## Completely positive trace-preserving linear maps

-/


-- @@ L317-317 verbatim
namespace CPTPMap

-- @@ L318-318 verbatim
variable [DecidableEq dIn]


-- @@ L320-324 verbatim
/-- Two `CPTPMap`s are equal if their `MatrixMap`s are equal. -/
@[ext]
theorem ext {Λ₁ Λ₂ : CPTPMap dIn dOut 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rw [CPTPMap.mk.injEq]
  exact PTPMap.ext h


-- @@ L326-348 verbatim
theorem injective_toPTPMap : (CPTPMap.toPTPMap (dIn := dIn) (dOut := dOut) (𝕜 := 𝕜)).Injective :=
  fun _ _ ↦ (mk.injEq _ _ _ _).mpr

-- /-- Positive trace-preserving maps are functions from `HermitianMat`s to `HermitianMat`s. -/
-- instance instFunLike : FunLike (CPTPMap dIn dOut 𝕜) (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
--   coe :=  DFunLike.coe ∘ toPTPMap
--   coe_injective' := DFunLike.coe_injective'.comp injective_toPTPMap

-- set_option synthInstance.maxHeartbeats 40000 in
-- instance instLinearMapClass : LinearMapClass (CPTPMap dIn dOut 𝕜) ℝ (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
--   map_add f x y := by simp [instFunLike]
--   map_smulₛₗ f c x := by simp [instFunLike]

-- instance instContinuousOrderHomClass : ContinuousOrderHomClass (CPTPMap dIn dOut 𝕜)
--     (HermitianMat dIn 𝕜) (HermitianMat dOut 𝕜) where
--   map_continuous f := ContinuousMapClass.map_continuous f.toPMap
--   map_monotone f x y h := by
    -- simpa using f.pos h

-- /-- PTP maps also preserve positivity on Hermitian matrices. -/
-- @[simp]
-- theorem pos_Hermitian (M : CPTPMap dIn dOut 𝕜) {x : HermitianMat dIn 𝕜} (h : 0 ≤ x) : 0 ≤ M x := by
--   simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h


-- @@ L350-353 verbatim
/-- `CPTPMap`s are functions from `MState`s to `MState`s. -/
noncomputable instance instMFunLike [DecidableEq dOut] : FunLike (CPTPMap dIn dOut) (MState dIn) (MState dOut) where
  coe := DFunLike.coe ∘ toPTPMap
  coe_injective := DFunLike.coe_injective.comp injective_toPTPMap


-- @@ L355-361 verbatim
lemma apply_mState_eq_toPTPMap [DecidableEq dOut] (Λ : CPTPMap dIn dOut) (ρ : MState dIn) :
    Λ ρ = Λ.toPTPMap ρ := rfl

-- @[norm_cast]
-- theorem val_apply_MState [DecidableEq dOut] (M : CPTPMap dIn dOut) (ρ : MState dIn) :
--     (M ρ : HermitianMat dOut ℂ) = (instFunLike.coe M) ρ := by
--   rfl


-- @@ L363-365 verbatim
@[simp]
theorem IsTracePreserving (Λ : CPTPMap dIn dOut 𝕜) : Λ.map.IsTracePreserving :=
  Λ.TP


-- @@ L367-372 verbatim
def of_kraus_CPTPMap {κ : Type*} [Fintype κ]
  (M : κ → Matrix dOut dIn 𝕜)
  (hTP : (∑ k, (M k).conjTranspose * (M k)) = 1) : CPTPMap dIn dOut 𝕜 where
  toLinearMap := MatrixMap.of_kraus M M
  cp := MatrixMap.of_kraus_isCompletelyPositive M
  TP := MatrixMap.IsTracePreserving.of_kraus_isTracePreserving M M hTP


-- @@ L374-374 verbatim
end CPTPMap


-- @@ L376-376 verbatim
namespace PUMap

-- @@ L377-377 verbatim
variable [DecidableEq dIn] [DecidableEq dOut]


-- @@ L379-382 verbatim
@[ext]
theorem ext {Λ₁ Λ₂ : PUMap dIn dOut 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rw [PUMap.mk.injEq]
  exact PMap.ext h


-- @@ L384-386 verbatim
theorem injective_toPMap : (PUMap.toPMap (dIn := dIn) (dOut := dOut) (𝕜 := 𝕜)).Injective := by
  intro _ _ _
  rwa [PUMap.mk.injEq]


-- @@ L388-391 verbatim
/-- `PUMap`s are functions from `HermitianMat`s to `HermitianMat`s. -/
noncomputable instance instFunLike : FunLike (PUMap dIn dOut ℂ) (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  coe Λ := Λ.toPMap
  coe_injective := (DFunLike.coe_injective (F := PMap dIn dOut ℂ)).comp injective_toPMap


-- @@ L393-394 verbatim
lemma apply_hermitianMat_eq_toPMap (Λ : PUMap dIn dOut ℂ) (ρ : HermitianMat dIn ℂ) :
    Λ ρ = Λ.toPMap ρ := rfl


-- @@ L396-398 verbatim
instance instLinearMapClass : LinearMapClass (PUMap dIn dOut ℂ) ℝ (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.toLinearMap x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp [apply_hermitianMat_eq_toPMap]


-- @@ L400-406 verbatim
instance instHContinuousOrderHomClass : ContinuousOrderHomClass (PUMap dIn dOut ℂ)
    (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_continuous f := ContinuousMapClass.map_continuous f.toPMap
  map_monotone f x y h := by
    have := f.pos h
    simp_all only [HermitianMat.val_eq_coe, map_sub, ge_iff_le]
    exact this


-- @@ L408-410 verbatim
instance instOneHomClass : OneHomClass (PUMap dIn dOut ℂ)
    (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_one f := HermitianMat.ext (f.unital)


-- @@ L412-415 verbatim
/-- CPTP maps also preserve positivity on Hermitian matrices. -/
@[simp]
theorem pos_Hermitian (M : PUMap dIn dOut ℂ) {x : HermitianMat dIn ℂ} (h : 0 ≤ x) : 0 ≤ M x := by
  simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h


-- @@ L417-417 verbatim
end PUMap


-- @@ L419-419 verbatim
namespace CPUMap

-- @@ L420-420 verbatim
variable [DecidableEq dIn] [DecidableEq dOut]


-- @@ L422-425 verbatim
@[ext]
theorem ext {Λ₁ Λ₂ : CPUMap dIn dOut 𝕜} (h : Λ₁.map = Λ₂.map) : Λ₁ = Λ₂ := by
  rw [CPUMap.mk.injEq, CPMap.mk.injEq]
  exact PMap.ext h


-- @@ L427-429 verbatim
theorem injective_toPMap : (CPMap.toPMap ∘ CPUMap.toCPMap (dIn := dIn) (dOut := dOut) (𝕜 := 𝕜)).Injective := by
  intro _ _ _
  rwa [CPUMap.mk.injEq, CPMap.mk.injEq]


-- @@ L431-434 verbatim
/-- `CPUMap`s are functions from `HermitianMat`s to `HermitianMat`s. -/
noncomputable instance instFunLike : FunLike (CPUMap dIn dOut ℂ) (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  coe Λ := Λ.toPMap
  coe_injective := (DFunLike.coe_injective (F := PMap dIn dOut ℂ)).comp injective_toPMap


-- @@ L436-437 verbatim
lemma apply_hermitianMat_eq_toPMap (Λ : CPUMap dIn dOut ℂ) (ρ : HermitianMat dIn ℂ) :
    Λ ρ = Λ.toPMap ρ := rfl


-- @@ L439-441 verbatim
instance instLinearMapClass : LinearMapClass (CPUMap dIn dOut ℂ) ℝ (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_add f x y := HermitianMat.ext <| LinearMap.map_add f.toLinearMap x y
  map_smulₛₗ f c x := HermitianMat.ext <| by simp [apply_hermitianMat_eq_toPMap]


-- @@ L443-449 verbatim
instance instHContinuousOrderHomClass : ContinuousOrderHomClass (CPUMap dIn dOut ℂ)
    (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_continuous f := ContinuousMapClass.map_continuous f.toPMap
  map_monotone f x y h := by
    have := f.pos h
    simp_all only [HermitianMat.val_eq_coe, map_sub, ge_iff_le]
    exact this


-- @@ L451-453 verbatim
instance instOneHomClass : OneHomClass (CPUMap dIn dOut ℂ)
    (HermitianMat dIn ℂ) (HermitianMat dOut ℂ) where
  map_one f := HermitianMat.ext (f.unital)


-- @@ L455-458 verbatim
/-- CPTP maps also preserve positivity on Hermitian matrices. -/
@[simp]
theorem pos_Hermitian (M : CPUMap dIn dOut ℂ) {x : HermitianMat dIn ℂ} (h : 0 ≤ x) : 0 ≤ M x := by
  simpa only [map_zero] using ContinuousOrderHomClass.map_monotone M h


-- @@ L460-462 verbatim
end CPUMap

--Tests to make sure that our `simp`s and classes are all working like we want them too


-- @@ L464-464 verbatim
section test

-- @@ L465-465 verbatim
variable [DecidableEq dIn] [DecidableEq dOut]


-- @@ L467-468 verbatim
#guard_msgs in
example (M : HPMap dIn dOut ℂ) : (M (Real.pi • 1)) = Real.pi • M 1 := by simp


-- @@ L470-471 verbatim
#guard_msgs in
example (M : PTPMap dIn dOut ℂ) : (M.toHPMap (Real.pi • 1)) = Real.pi • M.toHPMap 1 := by simp


-- @@ L473-474 verbatim
#guard_msgs in
example (M : CPTPMap dIn dOut 𝕜) (ρ : Matrix dIn dIn 𝕜) : (M.map ρ).trace = ρ.trace := by simp


-- @@ L476-477 verbatim
#guard_msgs in
example (M : CPUMap dIn dOut ℂ) (T : HermitianMat dIn ℂ) : M (1 + 2 • T) = 1 + 2 • M T := by simp


-- @@ L479-479 verbatim
end test
