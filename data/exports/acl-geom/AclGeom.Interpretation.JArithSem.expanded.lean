/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Config.JCoordinates
import AclGeom.Geometry.Representatives
import AclGeom.Interpretation.JArith
import AclGeom.Interpretation.FrobClass


-- @@ L11-42 verbatim
/-!
# Point-valued semantics of the meet/join `j`-arithmetic

`AclGeom.Interpretation.JArith` computes the EH95 operations `jSub` and `jDiv` on five-tuples of
closed subfields.  This file transports them to five-tuples of points of the geometry:

* `jCoords u` is the tuple of closed subfields underlying a point tuple `u`; semantic `j`-tuples
  are exactly the tuples with `jCoords u = jC x a` for an independent pair (`jSem_iff_jCoords`);
* `JSubRel u v w` and `JDivRel u v w` say that `w` is the meet/join difference or quotient of
  `u, v`; both relations are functional;
* for independent `x, y, a`, the unique output on `j(x, a), j(y, a)` is `j(x - y, a)`, resp.
  `j(x / y, a)` (`jSubRel_jTupleOf_iff`, `jDivRel_jTupleOf_iff`), again a semantic `j`-tuple;
* the derived relations `JNegRel`, `JInvRel`, `JAddRel` and `JMulRel` are functional and have the
  unique outputs `j(-y, a)`, `j(y⁻¹, a)`, `j(x + y, a)` and `j(x y, a)` on generic inputs;
* membership of the output in the geometric `J`-locus is stated only under the rank-five
  soundness hypotheses of `jGeom_of_jSem_of_five_le_trdeg`.

**Status:** the displayed generic semantics and function properties are proved (#23).
`ClassArithmetic` proves generic fixed-class correctness under explicit ACF J-completeness.
`Ratio` proves corrected ratio semantics under the same explicit inputs.
`Decode` packages the ratio quotient and bijective nonzero decoding.
`Interp` adjoins zero and gives full carrier decoding under the same inputs.
`Field` proves corrected total geometric graphs, a named transported field structure and the
actual decoding ring equivalence under the same explicit inputs. Conditional carrier/graph
naturality is proved in `Interpretation.Naturality`
under explicit carrier inputs. The rank-five ACF input is supplied by `jCompletenessACF`;
these internal interfaces keep it explicit. `Main` supplies both inputs internally for the
public reconstruction theorem. Original literal construction obligations remain on #23.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin reconstruction
theorem; the source of truth is `sources/blueprint.tex`.
-/


-- @@ L44-44 verbatim
namespace AclGeom


-- @@ L46-46 verbatim
open ClosedIF


-- @@ L48-48 verbatim
variable {k K : Type*} [Field k] [Field K] [Algebra k K]


-- @@ L50-50 verbatim
section Coordinates


-- @@ L52-54 verbatim
/-- The closed subfields underlying a five-tuple of points. -/
def jCoords (u : Fin 5 → Point k K) : Fin 5 → ClosedIF k K :=
  fun i ↦ (u i).1


-- @@ L56-57 verbatim
theorem jCoords_injective : Function.Injective (jCoords (k := k) (K := K)) :=
  fun _ _ h ↦ funext fun i ↦ Subtype.ext (congrFun h i)


-- @@ L59-74 verbatim
/-- Semantic `j`-tuples are exactly the point tuples with coordinates `jC x a` for an
independent pair `x, a`. -/
theorem jSem_iff_jCoords {X : Fin 5 → Point k K} :
    JSem X ↔ ∃ x a : K, AlgebraicIndependent k ![x, a] ∧ jCoords X = jC x a := by
  constructor
  · rintro ⟨x, a, h, h0, h1, h2, h3, h4⟩
    refine ⟨x, a, h, funext fun i ↦ ?_⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
  · rintro ⟨x, a, h, hX⟩
    exact ⟨x, a, h, congrFun hX 0, congrFun hX 1, congrFun hX 2, congrFun hX 3,
      congrFun hX 4⟩


-- @@ L76-78 verbatim
/-- `w` is the EH95 meet/join difference of `u` and `v` (Fig. 4). -/
def JSubRel (u v w : Fin 5 → Point k K) : Prop :=
  jCoords w = jSub (jCoords u) (jCoords v)


-- @@ L80-82 verbatim
/-- `w` is the EH95 meet/join quotient of `u` and `v` (Fig. 5). -/
def JDivRel (u v w : Fin 5 → Point k K) : Prop :=
  jCoords w = jDiv (jCoords u) (jCoords v)


-- @@ L84-87 verbatim
/-- The meet/join difference is functional. -/
theorem JSubRel.functional {u v w w' : Fin 5 → Point k K} (h : JSubRel u v w)
    (h' : JSubRel u v w') : w = w' :=
  jCoords_injective (h.trans h'.symm)


-- @@ L89-92 verbatim
/-- The meet/join quotient is functional. -/
theorem JDivRel.functional {u v w w' : Fin 5 → Point k K} (h : JDivRel u v w)
    (h' : JDivRel u v w') : w = w' :=
  jCoords_injective (h.trans h'.symm)


-- @@ L94-94 verbatim
end Coordinates


-- @@ L96-96 verbatim
section Points


-- @@ L98-98 verbatim
variable {x y a : K}


-- @@ L100-104 verbatim
/-- The closed subfields underlying `j(x, a)` form the closed-lattice `j`-tuple `jC x a`. -/
@[simp] theorem jCoords_jTupleOf (h : AlgebraicIndependent k ![x, a]) :
    jCoords (jTupleOf x a h) = jC x a := by
  funext i
  fin_cases i <;> rfl


-- @@ L106-106 verbatim
variable (h : AlgebraicIndependent k ![x, y, a])

-- @@ L107-107 verbatim
include h


-- @@ L109-109 verbatim
namespace JArith


-- @@ L111-116 expanded
/-- The parameter pairs of the outputs are independent. -/
theorem pair_sub_a : AlgebraicIndependent k ![x - y, a] :=
  AlgebraicIndependent.pair_zero_two
    (triple_of_span (u := x - y) (v := y) (w := a) h
      (by
        repeat'
          (first
            | (refine subset_racl _ _ ?_; simp; done)
            | exact one_mem _
            | apply add_mem
            | apply sub_mem
            | apply mul_mem
            | apply div_mem
            | apply inv_mem
            | apply neg_mem))
      (by
        repeat'
          (first
            | (refine subset_racl _ _ ?_; simp; done)
            | exact one_mem _
            | apply add_mem
            | apply sub_mem
            | apply mul_mem
            | apply div_mem
            | apply inv_mem
            | apply neg_mem))
      (by
        repeat'
          (first
            | (refine subset_racl _ _ ?_; simp; done)
            | exact one_mem _
            | apply add_mem
            | apply sub_mem
            | apply mul_mem
            | apply div_mem
            | apply inv_mem
            | apply neg_mem))
      (mem_racl_of_eq (show x = (x - y) + y by ring)
        (by
          repeat'
            (first
              | (refine subset_racl _ _ ?_; simp; done)
              | exact one_mem _
              | apply add_mem
              | apply sub_mem
              | apply mul_mem
              | apply div_mem
              | apply inv_mem
              | apply neg_mem)))
      (by
        repeat'
          (first
            | (refine subset_racl _ _ ?_; simp; done)
            | exact one_mem _
            | apply add_mem
            | apply sub_mem
            | apply mul_mem
            | apply div_mem
            | apply inv_mem
            | apply neg_mem))
      (by
        repeat'
          (first
            | (refine subset_racl _ _ ?_; simp; done)
            | exact one_mem _
            | apply add_mem
            | apply sub_mem
            | apply mul_mem
            | apply div_mem
            | apply inv_mem
            | apply neg_mem)))


-- @@ L118-123 expanded
theorem pair_div_a : AlgebraicIndependent k ![x / y, a] :=
  by
  have hy := y_ne_zero h
  exact
    AlgebraicIndependent.pair_zero_two
      (triple_of_span (u := x / y) (v := y) (w := a) h
        (by
          repeat'
            (first
              | (refine subset_racl _ _ ?_; simp; done)
              | exact one_mem _
              | apply add_mem
              | apply sub_mem
              | apply mul_mem
              | apply div_mem
              | apply inv_mem
              | apply neg_mem))
        (by
          repeat'
            (first
              | (refine subset_racl _ _ ?_; simp; done)
              | exact one_mem _
              | apply add_mem
              | apply sub_mem
              | apply mul_mem
              | apply div_mem
              | apply inv_mem
              | apply neg_mem))
        (by
          repeat'
            (first
              | (refine subset_racl _ _ ?_; simp; done)
              | exact one_mem _
              | apply add_mem
              | apply sub_mem
              | apply mul_mem
              | apply div_mem
              | apply inv_mem
              | apply neg_mem))
        (mem_racl_of_eq (show x = (x / y) * y by field_simp)
          (by
            repeat'
              (first
                | (refine subset_racl _ _ ?_; simp; done)
                | exact one_mem _
                | apply add_mem
                | apply sub_mem
                | apply mul_mem
                | apply div_mem
                | apply inv_mem
                | apply neg_mem)))
        (by
          repeat'
            (first
              | (refine subset_racl _ _ ?_; simp; done)
              | exact one_mem _
              | apply add_mem
              | apply sub_mem
              | apply mul_mem
              | apply div_mem
              | apply inv_mem
              | apply neg_mem))
        (by
          repeat'
            (first
              | (refine subset_racl _ _ ?_; simp; done)
              | exact one_mem _
              | apply add_mem
              | apply sub_mem
              | apply mul_mem
              | apply div_mem
              | apply inv_mem
              | apply neg_mem)))


-- @@ L125-125 verbatim
end JArith


-- @@ L127-127 verbatim
open JArith


-- @@ L129-136 verbatim
/-- **EH95 Fig. 4, point form.** The meet/join difference of `j(x, a)` and `j(y, a)` is
`j(x - y, a)`. -/
theorem jSubRel_jTupleOf :
    JSubRel (jTupleOf x a (AlgebraicIndependent.pair_zero_two h))
        (jTupleOf y a (AlgebraicIndependent.pair_one_two h))
      (jTupleOf (x - y) a (pair_sub_a h)) := by
  simp only [JSubRel.eq_def, jCoords_jTupleOf]
  exact (jSub_jC h).symm


-- @@ L138-145 verbatim
/-- **EH95 Fig. 5, point form.** The meet/join quotient of `j(x, a)` and `j(y, a)` is
`j(x / y, a)`. -/
theorem jDivRel_jTupleOf :
    JDivRel (jTupleOf x a (AlgebraicIndependent.pair_zero_two h))
        (jTupleOf y a (AlgebraicIndependent.pair_one_two h))
      (jTupleOf (x / y) a (pair_div_a h)) := by
  simp only [JDivRel.eq_def, jCoords_jTupleOf]
  exact (jDiv_jC h).symm


-- @@ L147-153 verbatim
/-- On generic `j`-tuples with a common parameter, `JSubRel` has exactly one output,
`j(x - y, a)`. -/
theorem jSubRel_jTupleOf_iff {w : Fin 5 → Point k K} :
    JSubRel (jTupleOf x a (AlgebraicIndependent.pair_zero_two h))
        (jTupleOf y a (AlgebraicIndependent.pair_one_two h)) w ↔
      w = jTupleOf (x - y) a (pair_sub_a h) :=
  ⟨fun hw ↦ hw.functional (jSubRel_jTupleOf h), fun hw ↦ hw ▸ jSubRel_jTupleOf h⟩


-- @@ L155-161 verbatim
/-- On generic `j`-tuples with a common parameter, `JDivRel` has exactly one output,
`j(x / y, a)`. -/
theorem jDivRel_jTupleOf_iff {w : Fin 5 → Point k K} :
    JDivRel (jTupleOf x a (AlgebraicIndependent.pair_zero_two h))
        (jTupleOf y a (AlgebraicIndependent.pair_one_two h)) w ↔
      w = jTupleOf (x / y) a (pair_div_a h) :=
  ⟨fun hw ↦ hw.functional (jDivRel_jTupleOf h), fun hw ↦ hw ▸ jDivRel_jTupleOf h⟩


-- @@ L163-168 verbatim
/-- Semantic form: whenever `u, v` are presented as `j(x, a), j(y, a)` with `x, y, a`
independent, every `JSubRel`-output is the semantic `j`-tuple `j(x - y, a)`. -/
theorem JSubRel.jCoords_eq {u v w : Fin 5 → Point k K} (hu : jCoords u = jC x a)
    (hv : jCoords v = jC y a) (hw : JSubRel u v w) : jCoords w = jC (x - y) a := by
  rw [JSubRel.eq_def, hu, hv, jSub_jC h] at hw
  exact hw


-- @@ L170-174 verbatim
/-- Semantic form of the quotient. -/
theorem JDivRel.jCoords_eq {u v w : Fin 5 → Point k K} (hu : jCoords u = jC x a)
    (hv : jCoords v = jC y a) (hw : JDivRel u v w) : jCoords w = jC (x / y) a := by
  rw [JDivRel.eq_def, hu, hv, jDiv_jC h] at hw
  exact hw


-- @@ L176-178 verbatim
theorem JSubRel.jSem {u v w : Fin 5 → Point k K} (hu : jCoords u = jC x a)
    (hv : jCoords v = jC y a) (hw : JSubRel u v w) : JSem w :=
  jSem_iff_jCoords.2 ⟨x - y, a, pair_sub_a h, hw.jCoords_eq h hu hv⟩


-- @@ L180-182 verbatim
theorem JDivRel.jSem {u v w : Fin 5 → Point k K} (hu : jCoords u = jC x a)
    (hv : jCoords v = jC y a) (hw : JDivRel u v w) : JSem w :=
  jSem_iff_jCoords.2 ⟨x / y, a, pair_div_a h, hw.jCoords_eq h hu hv⟩


-- @@ L184-188 verbatim
/-- Geometric membership of the difference, under the rank-five soundness hypotheses only. -/
theorem JSubRel.isJTuple (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {u v w : Fin 5 → Point k K} (hu : jCoords u = jC x a) (hv : jCoords v = jC y a)
    (hw : JSubRel u v w) : IsJTuple w :=
  jGeom_of_jSem_of_five_le_trdeg htr (hw.jSem h hu hv)


-- @@ L190-194 verbatim
/-- Geometric membership of the quotient, under the rank-five soundness hypotheses only. -/
theorem JDivRel.isJTuple (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {u v w : Fin 5 → Point k K} (hu : jCoords u = jC x a) (hv : jCoords v = jC y a)
    (hw : JDivRel u v w) : IsJTuple w :=
  jGeom_of_jSem_of_five_le_trdeg htr (hw.jSem h hu hv)


-- @@ L196-196 verbatim
end Points


-- @@ L198-198 verbatim
section DerivedPoints


-- @@ L200-202 verbatim
/-- `w` is the negation of `v` through the auxiliary tuple `z`. -/
def JNegRel (v z w : Fin 5 → Point k K) : Prop :=
  jCoords w = jNeg (jCoords v) (jCoords z)


-- @@ L204-206 verbatim
/-- `w` is the inverse of `v` through the auxiliary tuple `z`. -/
def JInvRel (v z w : Fin 5 → Point k K) : Prop :=
  jCoords w = jInv (jCoords v) (jCoords z)


-- @@ L208-210 verbatim
/-- `w` is the meet/join sum of `u` and `v`. -/
def JAddRel (u v w : Fin 5 → Point k K) : Prop :=
  jCoords w = jAdd (jCoords u) (jCoords v)


-- @@ L212-214 verbatim
/-- `w` is the meet/join product of `u` and `v`. -/
def JMulRel (u v w : Fin 5 → Point k K) : Prop :=
  jCoords w = jMul (jCoords u) (jCoords v)


-- @@ L216-219 verbatim
/-- The derived relations are functional. -/
theorem JNegRel.functional {v z w w' : Fin 5 → Point k K} (h : JNegRel v z w)
    (h' : JNegRel v z w') : w = w' :=
  jCoords_injective (h.trans h'.symm)


-- @@ L221-224 verbatim
/-- The derived relations are functional. -/
theorem JInvRel.functional {v z w w' : Fin 5 → Point k K} (h : JInvRel v z w)
    (h' : JInvRel v z w') : w = w' :=
  jCoords_injective (h.trans h'.symm)


-- @@ L226-229 verbatim
/-- The derived relations are functional. -/
theorem JAddRel.functional {u v w w' : Fin 5 → Point k K} (h : JAddRel u v w)
    (h' : JAddRel u v w') : w = w' :=
  jCoords_injective (h.trans h'.symm)


-- @@ L231-234 verbatim
/-- The derived relations are functional. -/
theorem JMulRel.functional {u v w w' : Fin 5 → Point k K} (h : JMulRel u v w)
    (h' : JMulRel u v w') : w = w' :=
  jCoords_injective (h.trans h'.symm)


-- @@ L236-236 verbatim
variable {x y a : K} (h : AlgebraicIndependent k ![x, y, a])

-- @@ L237-237 verbatim
include h


-- @@ L239-239 verbatim
namespace JArith


-- @@ L241-243 verbatim
/-- Parameter pairs of the derived outputs. -/
theorem pair_neg_a : AlgebraicIndependent k ![-y, a] :=
  AlgebraicIndependent.pair_one_two (triple_x_neg h)


-- @@ L245-246 verbatim
theorem pair_inv_a : AlgebraicIndependent k ![y⁻¹, a] :=
  AlgebraicIndependent.pair_one_two (triple_x_inv h)


-- @@ L248-252 expanded
theorem pair_add_a : AlgebraicIndependent k ![x + y, a] :=
  AlgebraicIndependent.pair_zero_two
    (triple_of_span (u := x + y) (v := y) (w := a) h
      (by
        repeat'
          (first
            | (refine subset_racl _ _ ?_; simp; done)
            | exact one_mem _
            | apply add_mem
            | apply sub_mem
            | apply mul_mem
            | apply div_mem
            | apply inv_mem
            | apply neg_mem))
      (by
        repeat'
          (first
            | (refine subset_racl _ _ ?_; simp; done)
            | exact one_mem _
            | apply add_mem
            | apply sub_mem
            | apply mul_mem
            | apply div_mem
            | apply inv_mem
            | apply neg_mem))
      (by
        repeat'
          (first
            | (refine subset_racl _ _ ?_; simp; done)
            | exact one_mem _
            | apply add_mem
            | apply sub_mem
            | apply mul_mem
            | apply div_mem
            | apply inv_mem
            | apply neg_mem))
      (mem_racl_of_eq (show x = (x + y) - y by ring)
        (by
          repeat'
            (first
              | (refine subset_racl _ _ ?_; simp; done)
              | exact one_mem _
              | apply add_mem
              | apply sub_mem
              | apply mul_mem
              | apply div_mem
              | apply inv_mem
              | apply neg_mem)))
      (by
        repeat'
          (first
            | (refine subset_racl _ _ ?_; simp; done)
            | exact one_mem _
            | apply add_mem
            | apply sub_mem
            | apply mul_mem
            | apply div_mem
            | apply inv_mem
            | apply neg_mem))
      (by
        repeat'
          (first
            | (refine subset_racl _ _ ?_; simp; done)
            | exact one_mem _
            | apply add_mem
            | apply sub_mem
            | apply mul_mem
            | apply div_mem
            | apply inv_mem
            | apply neg_mem)))


-- @@ L254-259 expanded
theorem pair_mul_a : AlgebraicIndependent k ![x * y, a] :=
  by
  have hy := y_ne_zero h
  exact
    AlgebraicIndependent.pair_zero_two
      (triple_of_span (u := x * y) (v := y) (w := a) h
        (by
          repeat'
            (first
              | (refine subset_racl _ _ ?_; simp; done)
              | exact one_mem _
              | apply add_mem
              | apply sub_mem
              | apply mul_mem
              | apply div_mem
              | apply inv_mem
              | apply neg_mem))
        (by
          repeat'
            (first
              | (refine subset_racl _ _ ?_; simp; done)
              | exact one_mem _
              | apply add_mem
              | apply sub_mem
              | apply mul_mem
              | apply div_mem
              | apply inv_mem
              | apply neg_mem))
        (by
          repeat'
            (first
              | (refine subset_racl _ _ ?_; simp; done)
              | exact one_mem _
              | apply add_mem
              | apply sub_mem
              | apply mul_mem
              | apply div_mem
              | apply inv_mem
              | apply neg_mem))
        (mem_racl_of_eq (show x = (x * y) / y by field_simp)
          (by
            repeat'
              (first
                | (refine subset_racl _ _ ?_; simp; done)
                | exact one_mem _
                | apply add_mem
                | apply sub_mem
                | apply mul_mem
                | apply div_mem
                | apply inv_mem
                | apply neg_mem)))
        (by
          repeat'
            (first
              | (refine subset_racl _ _ ?_; simp; done)
              | exact one_mem _
              | apply add_mem
              | apply sub_mem
              | apply mul_mem
              | apply div_mem
              | apply inv_mem
              | apply neg_mem))
        (by
          repeat'
            (first
              | (refine subset_racl _ _ ?_; simp; done)
              | exact one_mem _
              | apply add_mem
              | apply sub_mem
              | apply mul_mem
              | apply div_mem
              | apply inv_mem
              | apply neg_mem)))


-- @@ L261-261 verbatim
end JArith


-- @@ L263-263 verbatim
open JArith


-- @@ L265-270 verbatim
/-- On generic inputs, the negation of `j(y, a)` through `j(x, a)` is `j(-y, a)`. -/
theorem jNegRel_jTupleOf :
    JNegRel (jTupleOf y a (AlgebraicIndependent.pair_one_two h))
      (jTupleOf x a (AlgebraicIndependent.pair_zero_two h)) (jTupleOf (-y) a (pair_neg_a h)) := by
  simp only [JNegRel.eq_def, jCoords_jTupleOf]
  exact (jNeg_jC h).symm


-- @@ L272-277 verbatim
/-- On generic inputs, the negation of `j(y, a)` through `j(x, a)` is exactly `j(-y, a)`. -/
theorem jNegRel_jTupleOf_iff {w : Fin 5 → Point k K} :
    JNegRel (jTupleOf y a (AlgebraicIndependent.pair_one_two h))
        (jTupleOf x a (AlgebraicIndependent.pair_zero_two h)) w ↔
      w = jTupleOf (-y) a (pair_neg_a h) :=
  ⟨fun hw ↦ hw.functional (jNegRel_jTupleOf h), fun hw ↦ hw ▸ jNegRel_jTupleOf h⟩


-- @@ L279-284 verbatim
/-- On generic inputs, the inverse of `j(y, a)` through `j(x, a)` is `j(y⁻¹, a)`. -/
theorem jInvRel_jTupleOf :
    JInvRel (jTupleOf y a (AlgebraicIndependent.pair_one_two h))
      (jTupleOf x a (AlgebraicIndependent.pair_zero_two h)) (jTupleOf y⁻¹ a (pair_inv_a h)) := by
  simp only [JInvRel.eq_def, jCoords_jTupleOf]
  exact (jInv_jC h).symm


-- @@ L286-291 verbatim
/-- On generic inputs, the inverse of `j(y, a)` through `j(x, a)` is exactly `j(y⁻¹, a)`. -/
theorem jInvRel_jTupleOf_iff {w : Fin 5 → Point k K} :
    JInvRel (jTupleOf y a (AlgebraicIndependent.pair_one_two h))
        (jTupleOf x a (AlgebraicIndependent.pair_zero_two h)) w ↔
      w = jTupleOf y⁻¹ a (pair_inv_a h) :=
  ⟨fun hw ↦ hw.functional (jInvRel_jTupleOf h), fun hw ↦ hw ▸ jInvRel_jTupleOf h⟩


-- @@ L293-298 verbatim
/-- On generic inputs, the meet/join sum of `j(x, a)` and `j(y, a)` is `j(x + y, a)`. -/
theorem jAddRel_jTupleOf :
    JAddRel (jTupleOf x a (AlgebraicIndependent.pair_zero_two h))
      (jTupleOf y a (AlgebraicIndependent.pair_one_two h)) (jTupleOf (x + y) a (pair_add_a h)) := by
  simp only [JAddRel.eq_def, jCoords_jTupleOf]
  exact (jAdd_jC h).symm


-- @@ L300-305 verbatim
/-- On generic inputs, the meet/join sum of `j(x, a)` and `j(y, a)` is exactly `j(x + y, a)`. -/
theorem jAddRel_jTupleOf_iff {w : Fin 5 → Point k K} :
    JAddRel (jTupleOf x a (AlgebraicIndependent.pair_zero_two h))
        (jTupleOf y a (AlgebraicIndependent.pair_one_two h)) w ↔
      w = jTupleOf (x + y) a (pair_add_a h) :=
  ⟨fun hw ↦ hw.functional (jAddRel_jTupleOf h), fun hw ↦ hw ▸ jAddRel_jTupleOf h⟩


-- @@ L307-312 verbatim
/-- On generic inputs, the meet/join product of `j(x, a)` and `j(y, a)` is `j(x y, a)`. -/
theorem jMulRel_jTupleOf :
    JMulRel (jTupleOf x a (AlgebraicIndependent.pair_zero_two h))
      (jTupleOf y a (AlgebraicIndependent.pair_one_two h)) (jTupleOf (x * y) a (pair_mul_a h)) := by
  simp only [JMulRel.eq_def, jCoords_jTupleOf]
  exact (jMul_jC h).symm


-- @@ L314-320 verbatim
/-- On generic inputs, the meet/join product of `j(x, a)` and `j(y, a)` is exactly
`j(x y, a)`. -/
theorem jMulRel_jTupleOf_iff {w : Fin 5 → Point k K} :
    JMulRel (jTupleOf x a (AlgebraicIndependent.pair_zero_two h))
        (jTupleOf y a (AlgebraicIndependent.pair_one_two h)) w ↔
      w = jTupleOf (x * y) a (pair_mul_a h) :=
  ⟨fun hw ↦ hw.functional (jMulRel_jTupleOf h), fun hw ↦ hw ▸ jMulRel_jTupleOf h⟩


-- @@ L322-327 verbatim
/-- Semantic form of the sum: any presentation of the inputs as `j(x, a), j(y, a)` with
`x, y, a` independent forces the output `j(x + y, a)`. -/
theorem JAddRel.jCoords_eq {u v w : Fin 5 → Point k K} (hu : jCoords u = jC x a)
    (hv : jCoords v = jC y a) (hw : JAddRel u v w) : jCoords w = jC (x + y) a := by
  rw [JAddRel.eq_def, hu, hv, jAdd_jC h] at hw
  exact hw


-- @@ L329-333 verbatim
/-- Semantic form of the product. -/
theorem JMulRel.jCoords_eq {u v w : Fin 5 → Point k K} (hu : jCoords u = jC x a)
    (hv : jCoords v = jC y a) (hw : JMulRel u v w) : jCoords w = jC (x * y) a := by
  rw [JMulRel.eq_def, hu, hv, jMul_jC h] at hw
  exact hw


-- @@ L335-339 verbatim
/-- Semantic form of the negation. -/
theorem JNegRel.jCoords_eq {v z w : Fin 5 → Point k K} (hv : jCoords v = jC y a)
    (hz : jCoords z = jC x a) (hw : JNegRel v z w) : jCoords w = jC (-y) a := by
  rw [JNegRel.eq_def, hv, hz, jNeg_jC h] at hw
  exact hw


-- @@ L341-345 verbatim
/-- Semantic form of the inversion. -/
theorem JInvRel.jCoords_eq {v z w : Fin 5 → Point k K} (hv : jCoords v = jC y a)
    (hz : jCoords z = jC x a) (hw : JInvRel v z w) : jCoords w = jC y⁻¹ a := by
  rw [JInvRel.eq_def, hv, hz, jInv_jC h] at hw
  exact hw


-- @@ L347-349 verbatim
theorem JAddRel.jSem {u v w : Fin 5 → Point k K} (hu : jCoords u = jC x a)
    (hv : jCoords v = jC y a) (hw : JAddRel u v w) : JSem w :=
  jSem_iff_jCoords.2 ⟨x + y, a, pair_add_a h, hw.jCoords_eq h hu hv⟩


-- @@ L351-353 verbatim
theorem JMulRel.jSem {u v w : Fin 5 → Point k K} (hu : jCoords u = jC x a)
    (hv : jCoords v = jC y a) (hw : JMulRel u v w) : JSem w :=
  jSem_iff_jCoords.2 ⟨x * y, a, pair_mul_a h, hw.jCoords_eq h hu hv⟩


-- @@ L355-357 verbatim
theorem JNegRel.jSem {v z w : Fin 5 → Point k K} (hv : jCoords v = jC y a)
    (hz : jCoords z = jC x a) (hw : JNegRel v z w) : JSem w :=
  jSem_iff_jCoords.2 ⟨-y, a, pair_neg_a h, hw.jCoords_eq h hv hz⟩


-- @@ L359-361 verbatim
theorem JInvRel.jSem {v z w : Fin 5 → Point k K} (hv : jCoords v = jC y a)
    (hz : jCoords z = jC x a) (hw : JInvRel v z w) : JSem w :=
  jSem_iff_jCoords.2 ⟨y⁻¹, a, pair_inv_a h, hw.jCoords_eq h hv hz⟩


-- @@ L363-367 verbatim
/-- Geometric membership of the sum, under the rank-five soundness hypotheses only. -/
theorem JAddRel.isJTuple (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {u v w : Fin 5 → Point k K} (hu : jCoords u = jC x a) (hv : jCoords v = jC y a)
    (hw : JAddRel u v w) : IsJTuple w :=
  jGeom_of_jSem_of_five_le_trdeg htr (hw.jSem h hu hv)


-- @@ L369-373 verbatim
/-- Geometric membership of the product, under the rank-five soundness hypotheses only. -/
theorem JMulRel.isJTuple (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {u v w : Fin 5 → Point k K} (hu : jCoords u = jC x a) (hv : jCoords v = jC y a)
    (hw : JMulRel u v w) : IsJTuple w :=
  jGeom_of_jSem_of_five_le_trdeg htr (hw.jSem h hu hv)


-- @@ L375-379 verbatim
/-- Geometric membership of the negation, under the rank-five soundness hypotheses only. -/
theorem JNegRel.isJTuple (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {v z w : Fin 5 → Point k K} (hv : jCoords v = jC y a) (hz : jCoords z = jC x a)
    (hw : JNegRel v z w) : IsJTuple w :=
  jGeom_of_jSem_of_five_le_trdeg htr (hw.jSem h hv hz)


-- @@ L381-385 verbatim
/-- Geometric membership of the inversion, under the rank-five soundness hypotheses only. -/
theorem JInvRel.isJTuple (htr : (5 : Cardinal) ≤ Algebra.trdeg k K)
    {v z w : Fin 5 → Point k K} (hv : jCoords v = jC y a) (hz : jCoords z = jC x a)
    (hw : JInvRel v z w) : IsJTuple w :=
  jGeom_of_jSem_of_five_le_trdeg htr (hw.jSem h hv hz)


-- @@ L387-387 verbatim
end DerivedPoints


-- @@ L389-389 verbatim
end AclGeom
