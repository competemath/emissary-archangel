/-
Copyright (c) 2026 Etienne Marion. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Etienne Marion
-/
module

public import Mathlib.MeasureTheory.Measure.MeasureSpaceDef


-- @@ L10-10 verbatim
public section


-- @@ L12-12 verbatim
open MeasureTheory


-- @@ L14-14 verbatim
namespace ProbabilityTheory


-- @@ L16-16 verbatim
variable {ι Ω E : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {X Y Z : ι → Ω → E}


-- @@ L18-21 verbatim
/-- Two processes are indistinguishable if almost surely they agree everywhere. -/
@[expose]
def Indistinguishable (P : Measure Ω) (X Y : ι → Ω → E) : Prop :=
  ∀ᵐ ω ∂P, ∀ t, X t ω = Y t ω


-- @@ L23-24 verbatim
/-- Two processes are indistinguishable if almost surely they agree everywhere. -/
notation3:50 X " ≡ᵐ[" P:50 "] " Y:50 => Indistinguishable P X Y


-- @@ L26-26 verbatim
namespace Indistinguishable


-- @@ L28-30 expanded
@[refl, simp]
protected lemma refl (P : Measure Ω) (X : ι → Ω → E) : Indistinguishable P X X :=
  .of_forall fun _ _ ↦ rfl


-- @@ L32-32 expanded
protected lemma rfl : Indistinguishable P X X := by rfl


-- @@ L34-36 expanded
@[symm]
protected lemma symm (h : Indistinguishable P X Y) : Indistinguishable P Y X := by
  filter_upwards [h] with ω h t using (h t).symm


-- @@ L38-41 expanded
@[trans]
protected lemma trans (h1 : Indistinguishable P X Y) (h2 : Indistinguishable P Y Z) :
    Indistinguishable P X Z := by
  filter_upwards [h1, h2] with ω h t
  grind


-- @@ L43-43 expanded
instance : IsTrans (ι → Ω → E) (Indistinguishable P · ·) :=
  ⟨fun _ _ _ ↦ .trans⟩


-- @@ L45-48 expanded
protected lemma fun_comp {F : Type*} (h : Indistinguishable P X Y) (f : E → F) :
    Indistinguishable P (fun t ω ↦ f (X t ω)) (fun t ω ↦ f (Y t ω)) :=
  by
  filter_upwards [h] with ω h t
  rw [h]


-- @@ L50-54 expanded
protected lemma fun_comp₂ {F G : Type*} {Z T : ι → Ω → F} (h1 : Indistinguishable P X Y)
    (h2 : Indistinguishable P Z T) (f : E → F → G) :
    Indistinguishable P (fun t ω ↦ f (X t ω) (Z t ω)) (fun t ω ↦ f (Y t ω) (T t ω)) :=
  by
  filter_upwards [h1, h2] with ω h1 h2 t
  rw [h1, h2]


-- @@ L56-58 expanded
@[to_additive (attr := to_fun, gcongr)]
protected lemma inv [Inv E] (h : Indistinguishable P X Y) : Indistinguishable P X⁻¹ Y⁻¹ :=
  h.fun_comp _


-- @@ L60-62 expanded
@[to_additive (attr := to_fun, gcongr)]
protected lemma mul [Mul E] {Z T : ι → Ω → E} (h1 : Indistinguishable P X Y)
    (h2 : Indistinguishable P Z T) : Indistinguishable P (X * Z) (Y * T) :=
  h1.fun_comp₂ h2 _


-- @@ L64-66 expanded
@[to_additive (attr := to_fun, gcongr)]
protected lemma div [Div E] {Z T : ι → Ω → E} (h1 : Indistinguishable P X Y)
    (h2 : Indistinguishable P Z T) : Indistinguishable P (X / Z) (Y / T) :=
  h1.fun_comp₂ h2 _


-- @@ L68-71 expanded
@[to_additive (attr := to_fun, gcongr)]
protected lemma smul {F : Type*} {Z T : ι → Ω → F} [SMul F E] (h1 : Indistinguishable P X Y)
    (h2 : Indistinguishable P Z T) : Indistinguishable P (Z • X) (T • Y) :=
  h2.fun_comp₂ h1 _


-- @@ L73-75 expanded
@[to_additive (attr := to_fun, gcongr)]
protected lemma const_smul {F : Type*} [SMul F E] {c : F} (h : Indistinguishable P X Y) :
    Indistinguishable P (c • X) (c • Y) :=
  h.fun_comp _


-- @@ L77-79 expanded
protected lemma prodMk {F : Type*} {Z T : ι → Ω → F} (h1 : Indistinguishable P X Y)
    (h2 : Indistinguishable P Z T) :
    Indistinguishable P (fun t ω ↦ (X t ω, Z t ω)) (fun t ω ↦ (Y t ω, T t ω)) :=
  h1.fun_comp₂ h2 _


-- @@ L81-84 expanded
protected lemma ae_eq (h : Indistinguishable P X Y) : (fun ω t ↦ X t ω) =ᵐ[P] (fun ω t ↦ Y t ω) :=
  by
  filter_upwards [h] with ω h
  ext
  rw [h]


-- @@ L86-88 expanded
lemma ae_eq_eval (h : Indistinguishable P X Y) (t : ι) : X t =ᵐ[P] Y t :=
  by
  filter_upwards [h] with ω h
  rw [h]


-- @@ L90-93 expanded
lemma _root_.Filter.EventuallyEq.indist (h : (fun ω t ↦ X t ω) =ᵐ[P] (fun ω t ↦ Y t ω)) :
    Indistinguishable P X Y := by
  filter_upwards [h] with ω h
  rwa [funext_iff] at h


-- @@ L95-95 verbatim
end Indistinguishable


-- @@ L97-97 verbatim
end ProbabilityTheory
