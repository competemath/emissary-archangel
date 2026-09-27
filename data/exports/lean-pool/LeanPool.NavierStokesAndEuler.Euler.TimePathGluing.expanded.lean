/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.VolterraConvolution


-- @@ L11-11 verbatim
/-! Exact pasting of actual continuous solution paths on adjacent compact time intervals. -/


-- @@ L13-13 verbatim
@[expose] public section



-- @@ L16-16 verbatim
noncomputable section


-- @@ L18-18 verbatim
namespace EulerTimePathGluing


-- @@ L20-20 verbatim
open Set EulerVolterraConvolution

-- @@ L21-21 verbatim
open scoped Topology


-- @@ L23-23 verbatim
variable {E : Type*} [NormedAddCommGroup E]


-- @@ L25-28 verbatim
/-- The literal adjacent-interval pasting of two actual clamped paths. -/
def glueFunction (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (u : C(Icc (0 : ℝ) a, E)) (v : C(Icc (0 : ℝ) b, E)) (t : ℝ) : E :=
  if t ≤ a then extendPath a ha u t else extendPath b hb v (t-a)


-- @@ L30-35 verbatim
/-- Matching endpoint traces are exactly the equality needed by the clamped pasting. -/
theorem endpoint_match (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (u : C(Icc (0 : ℝ) a, E)) (v : C(Icc (0 : ℝ) b, E))
    (hmatch : u ⟨a, ha, le_rfl⟩ = v ⟨0, le_rfl, hb⟩) :
    extendPath a ha u a = extendPath b hb v 0 := by
  simpa only [extendPath, projIcc_of_mem ha ⟨ha,le_rfl⟩, projIcc_of_mem hb ⟨le_rfl,hb⟩] using hmatch


-- @@ L37-49 verbatim
/-- Matching actual endpoint traces make the pasted path continuous. -/
theorem glueFunction_continuous (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (u : C(Icc (0 : ℝ) a, E)) (v : C(Icc (0 : ℝ) b, E))
    (hmatch : u ⟨a, ha, le_rfl⟩ = v ⟨0, le_rfl, hb⟩) : Continuous (glueFunction a b ha hb u v) := by
  apply Continuous.if_le (extendPath_continuous a ha u)
    ((extendPath_continuous b hb v).comp (continuous_id.sub continuous_const)) continuous_id
        continuous_const
  intro t ht
  change t = a at ht
  subst t
  change extendPath a ha u a = extendPath b hb v (a-a)
  rw [sub_self]
  exact endpoint_match a b ha hb u v hmatch


-- @@ L51-56 verbatim
/-- The actual continuous path on the union of the two adjacent time intervals. -/
def gluePath (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (u : C(Icc (0 : ℝ) a, E)) (v : C(Icc (0 : ℝ) b, E))
    (hmatch : u ⟨a, ha, le_rfl⟩ = v ⟨0, le_rfl, hb⟩) : C(Icc (0 : ℝ) (a+b), E) :=
  ⟨fun t => glueFunction a b ha hb u v t.val, (glueFunction_continuous a b ha hb u v hmatch).comp
      continuous_subtype_val⟩


-- @@ L58-61 verbatim
/-- The pasted function preserves the original solution before the restart time. -/
theorem glueFunction_left (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (u : C(Icc (0 : ℝ) a, E)) (v : C(Icc (0 : ℝ) b, E)) (t : ℝ) (ht : t ≤ a) :
    glueFunction a b ha hb u v t = extendPath a ha u t := ite_eq_left ht


-- @@ L63-73 verbatim
/-- The pasted function is the restarted solution after its matching endpoint. -/
theorem glueFunction_right (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (u : C(Icc (0 : ℝ) a, E)) (v : C(Icc (0 : ℝ) b, E))
    (hmatch : u ⟨a, ha, le_rfl⟩ = v ⟨0, le_rfl, hb⟩) (t : ℝ) (ht : a ≤ t) :
    glueFunction a b ha hb u v t = extendPath b hb v (t-a) := by
  by_cases hta : t ≤ a
  · have he : t = a := le_antisymm hta ht
    subst t
    rw [glueFunction_left a b ha hb u v a le_rfl, sub_self]
    exact endpoint_match a b ha hb u v hmatch
  · exact ite_eq_right hta


-- @@ L75-84 verbatim
/-- On the old interval the actual clamped union path is identical to the old clamped path. -/
theorem gluePath_left (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (u : C(Icc (0 : ℝ) a, E)) (v : C(Icc (0 : ℝ) b, E))
    (hmatch : u ⟨a, ha, le_rfl⟩ = v ⟨0, le_rfl, hb⟩) (t : ℝ) (ht : t ∈ Icc 0 a) :
    extendPath (a+b) (add_nonneg ha hb) (gluePath a b ha hb u v hmatch) t = extendPath a ha u t :=
        by
  have htu : t ∈ Icc 0 (a+b) := ⟨ht.1, by linarith [ht.2]⟩
  change glueFunction a b ha hb u v (projIcc 0 (a+b) (add_nonneg ha hb) t).val = _
  rw [projIcc_of_mem (add_nonneg ha hb) htu]
  exact glueFunction_left a b ha hb u v t ht.2


-- @@ L86-96 verbatim
/-- On the new interval the actual clamped union path is identical to the elapsed-time restart path.
-/
theorem gluePath_right (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (u : C(Icc (0 : ℝ) a, E)) (v : C(Icc (0 : ℝ) b, E))
    (hmatch : u ⟨a, ha, le_rfl⟩ = v ⟨0, le_rfl, hb⟩) (t : ℝ) (ht : t ∈ Icc 0 b) :
    extendPath (a+b) (add_nonneg ha hb) (gluePath a b ha hb u v hmatch) (a+t) = extendPath b hb v t
        := by
  have htu : a+t ∈ Icc 0 (a+b) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  change glueFunction a b ha hb u v (projIcc 0 (a+b) (add_nonneg ha hb) (a+t)).val = _
  rw [projIcc_of_mem (add_nonneg ha hb) htu, glueFunction_right a b ha hb u v hmatch (a+t) (by
      linarith [ht.1]), add_sub_cancel_left]


-- @@ L98-108 verbatim
/-- The actual pasted path is bounded by any common uniform bound for its two pieces. -/
theorem gluePath_norm_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (u : C(Icc (0 : ℝ) a, E)) (v : C(Icc (0 : ℝ) b, E))
    (hmatch : u ⟨a, ha, le_rfl⟩ = v ⟨0, le_rfl, hb⟩) (R : ℝ) (hR : 0 ≤ R)
    (hu : ‖u‖ ≤ R) (hv : ‖v‖ ≤ R) : ‖gluePath a b ha hb u v hmatch‖ ≤ R := by
  apply (ContinuousMap.norm_le _ hR).mpr
  intro t
  change ‖if t.val ≤ a then extendPath a ha u t.val else extendPath b hb v (t.val-a)‖ ≤ R
  split
  · exact (extendPath_norm_le a ha u t.val).trans hu
  · exact (extendPath_norm_le b hb v (t.val-a)).trans hv


-- @@ L110-110 verbatim
end EulerTimePathGluing
