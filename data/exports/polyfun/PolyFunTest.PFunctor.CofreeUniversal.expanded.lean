/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Cofree.Universal
public import PolyFunTest.PFunctor.CofreePolynomial
public import PolyFunTest.PFunctor.Comonoid.Category


-- @@ L12-20 verbatim
/-!
# Regression tests for the cofree polynomial universal property

The tests keep generic coiteration universe-independent, make coiterated
branching observable on a three-state category, and use the non-thin Boolean
list category to distinguish root, one-edge, and two-edge path pulls.  Both
round trips and both naturality variables of the hom-set equivalence are
exercised through exported declarations.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
universe uA uB uCA uCB


-- @@ L26-26 verbatim
namespace PFunctor

-- @@ L27-27 verbatim
namespace CofreeUniversalTest


-- @@ L29-29 verbatim
open CofreePolynomialTest

-- @@ L30-30 verbatim
open ComonoidCategoryTest


-- @@ L32-32 verbatim
/-! ## Universe and cogenerator canaries -/


-- @@ L34-38 verbatim
/-- Generic coiteration keeps the comonoid and generator universe pairs
independent. -/
example (P : PFunctor.{uA, uB}) (C : Comonoid.{uCA, uCB})
    (lens : Lens C.carrier P) : Lens C.carrier (CofreeP P) :=
  CofreeP.unfoldLens C lens


-- @@ L40-46 expanded
/-- The underlying cogenerator square retains the heterogeneous universe
boundary of cofree mapping, even though `mapHom` later specializes it. -/
example (P : PFunctor.{uA, uB}) (Q : PFunctor.{uCA, uCB}) (lens : Lens P Q) :
    comp (CofreeP.cogenerator Q) (CofreeP.map lens) = comp lens (CofreeP.cogenerator P) :=
  CofreeP.cogenerator_comp_map lens


-- @@ L48-57 verbatim
/-- The semantic subtree equation is available at the same fully
heterogeneous boundary. -/
example (P : PFunctor.{uA, uB}) (C : Comonoid.{uCA, uCB})
    (lens : Lens C.carrier P) (object : C.carrier.A)
    (vertex : M.Vertex (CofreeP.unfoldShape C lens object)) :
    M.Vertex.subtree vertex =
      CofreeP.unfoldShape C lens
        (Comonoid.target C object
          (CofreeP.unfoldDirection C lens object vertex)) :=
  CofreeP.subtree_unfoldShape C lens object vertex


-- @@ L59-65 verbatim
/-- Homomorphism packaging is localized to the homogeneous maximum occupied
by `CofreeP P`. -/
example (P : PFunctor.{uA, uB})
    (C : Comonoid.{max uA uB, max uA uB})
    (lens : Lens C.carrier P) :
    Comonoid.Hom C (CofreeP.comonoid P) :=
  CofreeP.extend C lens


-- @@ L67-70 verbatim
example (P : PFunctor.{uA, uB})
    (C : Comonoid.{max uA uB, max uA uB}) :
    Comonoid.Hom C (CofreeP.comonoid P) ≃ Lens C.carrier P :=
  CofreeP.homEquiv C


-- @@ L72-75 verbatim
/-- The cogenerator exposes the root label. -/
example : (CofreeP.cogenerator binaryP).toFunA binaryTree =
    M.head binaryTree :=
  rfl


-- @@ L77-80 verbatim
/-- Its backward map really selects the requested depth-one vertex. -/
example : (CofreeP.cogenerator binaryP).toFunB binaryTree false =
    .child false (.root (M.children binaryTree false)) :=
  rfl


-- @@ L82-82 verbatim
/-! ## Observable three-state unfolding -/


-- @@ L84-98 verbatim
/-- A state-category generator whose two source branches enter states with
different exposed labels. -/
def branchingLens : Lens (stateComonoid ThreeState).carrier binaryP where
  toFunA
    | .source => false
    | .middle => true
    | .final => false
  toFunB state direction :=
    match state, direction with
    | .source, false => .middle
    | .source, true => .final
    | .middle, false => .source
    | .middle, true => .final
    | .final, false => .source
    | .final, true => .middle


-- @@ L100-101 verbatim
def branchingTree : M binaryP :=
  CofreeP.unfoldShape (stateComonoid ThreeState) branchingLens .source


-- @@ L103-104 verbatim
example : M.head branchingTree = false :=
  CofreeP.head_unfoldShape (stateComonoid ThreeState) branchingLens .source


-- @@ L106-111 verbatim
/-- The `false` branch enters `middle`, whose label is observably `true`. -/
example : M.head (M.children branchingTree false) = true := by
  unfold branchingTree
  rw [CofreeP.children_unfoldShape]
  exact CofreeP.head_unfoldShape
    (stateComonoid ThreeState) branchingLens .middle


-- @@ L113-118 verbatim
/-- The other branch enters `final`, whose label remains distinct. -/
example : M.head (M.children branchingTree true) = false := by
  unfold branchingTree
  rw [CofreeP.children_unfoldShape]
  exact CofreeP.head_unfoldShape
    (stateComonoid ThreeState) branchingLens .final


-- @@ L120-120 verbatim
/-! ## Non-thin path-order model -/


-- @@ L122-125 verbatim
/-- Fix the otherwise unconstrained position universe of the test-local pure
power comonoid. -/
abbrev boolListComonoid : Comonoid.{0, 0} :=
  listMonoidComonoid


-- @@ L127-130 expanded
/-- Interpret a Boolean generator direction as the corresponding singleton
arrow in the one-object Boolean-list category. -/
def bitGenerator : Lens boolListComonoid.carrier binaryP :=
  Lens.mk (fun _ => false) (fun _ direction => [direction])


-- @@ L132-134 verbatim
def listExtension : Comonoid.Hom
    boolListComonoid (CofreeP.comonoid binaryP) :=
  CofreeP.extend boolListComonoid bitGenerator


-- @@ L136-137 verbatim
def listObject : boolListComonoid.carrier.A :=
  PUnit.unit


-- @@ L139-140 verbatim
def listTree : M binaryP :=
  listExtension.toLens.toFunA listObject


-- @@ L142-143 verbatim
def falseVertex : M.Vertex listTree :=
  .child false (.root _)


-- @@ L145-146 verbatim
def innerTrueVertex : M.Vertex (M.Vertex.subtree falseVertex) :=
  .child true (.root _)


-- @@ L148-149 verbatim
def falseThenTrueVertex : M.Vertex listTree :=
  M.Vertex.append falseVertex innerTrueVertex


-- @@ L151-154 verbatim
/-- The concrete extension uses the generic coiterated shape. -/
example : listTree =
    CofreeP.unfoldShape boolListComonoid bitGenerator listObject :=
  rfl


-- @@ L156-165 verbatim
/-- The root path is the identity arrow, hence the empty list. -/
example : listExtension.toLens.toFunB listObject (.root listTree) = [] := by
  -- Lean 4.33: `calc` cannot synthesize its `Trans` instance across the
  -- list-monoid carrier at instance transparency, so `Eq.trans` is applied
  -- directly.
  have h : listExtension.toLens.toFunB listObject (.root listTree) =
      Comonoid.identity boolListComonoid listObject := by
    rw [← CofreeP.comonoid_identity]
    exact listExtension.map_identity listObject
  exact h.trans rfl


-- @@ L167-180 verbatim
/-- Every one-edge path pulls back to the corresponding singleton arrow. -/
theorem listExtension_oneLayer (object : boolListComonoid.carrier.A)
    (direction : Bool) :
    listExtension.toLens.toFunB object
        (.child direction (.root
          (M.children (listExtension.toLens.toFunA object) direction))) =
      [direction] := by
  have h := congrArg
    (fun lens : Lens boolListComonoid.carrier binaryP =>
      lens.toFunB object direction)
    (CofreeP.restrict_extend boolListComonoid bitGenerator)
  change (CofreeP.restrict boolListComonoid listExtension).toFunB
    object direction = [direction]
  simpa [listExtension, bitGenerator] using h


-- @@ L182-184 verbatim
/-- A concrete one-edge path exposes the `false` singleton. -/
example : listExtension.toLens.toFunB listObject falseVertex = [false] :=
  listExtension_oneLayer listObject false


-- @@ L186-217 verbatim
/-- A two-edge path records both arrows in outer-then-inner order. -/
example : listExtension.toLens.toFunB listObject falseThenTrueVertex =
    [false, true] := by
  have hmap := listExtension.map_compose
    listObject falseVertex innerTrueVertex
  let nextObject := Comonoid.target boolListComonoid listObject
    (listExtension.toLens.toFunB listObject falseVertex)
  let nextTrueVertex : M.Vertex
      (listExtension.toLens.toFunA nextObject) :=
    .child true (.root _)
  have htree : M.Vertex.subtree falseVertex =
      listExtension.toLens.toFunA nextObject :=
    (listExtension.map_target listObject falseVertex).symm
  have hraw : innerTrueVertex ≍ nextTrueVertex := by
    cases htree
    rfl
  have htailAny (vertex : M.Vertex
      (listExtension.toLens.toFunA nextObject))
      (hvertex : vertex ≍ nextTrueVertex) :
      listExtension.toLens.toFunB nextObject vertex = [true] := by
    have hvertexEq : vertex = nextTrueVertex := eq_of_heq hvertex
    rw [hvertexEq]
    exact listExtension_oneLayer nextObject true
  have hfirst :
      listExtension.toLens.toFunB listObject falseVertex = [false] :=
    listExtension_oneLayer listObject false
  change listExtension.toLens.toFunB listObject
    (M.Vertex.append falseVertex innerTrueVertex) = [false, true]
  refine hmap.trans ?_
  rw [hfirst]
  change [false] ++ _ = [false] ++ [true]
  congr 1


-- @@ L219-219 verbatim
/-! ## Universal-property round trips -/


-- @@ L221-222 verbatim
example : CofreeP.restrict boolListComonoid listExtension = bitGenerator := by
  simp [listExtension]


-- @@ L224-228 verbatim
example (hom : Comonoid.Hom
    boolListComonoid (CofreeP.comonoid binaryP)) :
    CofreeP.extend boolListComonoid
        (CofreeP.restrict boolListComonoid hom) = hom := by
  simp


-- @@ L230-233 verbatim
example : (CofreeP.homEquiv boolListComonoid).symm
      ((CofreeP.homEquiv boolListComonoid) listExtension) =
    listExtension :=
  (CofreeP.homEquiv boolListComonoid).symm_apply_apply _


-- @@ L235-238 verbatim
example : CofreeP.homEquiv boolListComonoid
      ((CofreeP.homEquiv boolListComonoid).symm bitGenerator) =
    bitGenerator :=
  (CofreeP.homEquiv boolListComonoid).apply_symm_apply _


-- @@ L240-247 verbatim
/-- Extending the canonical cogenerator recovers the identity retrofunctor. -/
example : CofreeP.extend (CofreeP.comonoid binaryP)
      (CofreeP.cogenerator binaryP) =
    Comonoid.Hom.id (CofreeP.comonoid binaryP) := by
  simpa [CofreeP.restrict] using
    CofreeP.extend_restrict
      (C := CofreeP.comonoid binaryP)
      (Comonoid.Hom.id (CofreeP.comonoid binaryP))


-- @@ L249-249 verbatim
/-! ## Naturality canaries -/


-- @@ L251-261 expanded
/-- Source-side naturality is exercised with the nontrivial state projection
retrofunctor. -/
example :
    CofreeP.homEquiv (stateComonoid (ThreeState × Bool))
        (fstHom.comp (CofreeP.extend (stateComonoid ThreeState) branchingLens)) =
      comp
        (CofreeP.homEquiv (stateComonoid ThreeState)
          (CofreeP.extend (stateComonoid ThreeState) branchingLens))
        fstHom.toLens :=
  CofreeP.homEquiv_naturality_left fstHom (CofreeP.extend (stateComonoid ThreeState) branchingLens)


-- @@ L263-270 expanded
/-- Generator-side naturality is exercised with a branch-reversing lens. -/
example :
    CofreeP.homEquiv boolListComonoid (listExtension.comp (CofreeP.mapHom reverseBranchLens)) =
      comp reverseBranchLens (CofreeP.homEquiv boolListComonoid listExtension) :=
  CofreeP.homEquiv_naturality_right boolListComonoid reverseBranchLens listExtension


-- @@ L272-272 verbatim
end CofreeUniversalTest

-- @@ L273-273 verbatim
end PFunctor
