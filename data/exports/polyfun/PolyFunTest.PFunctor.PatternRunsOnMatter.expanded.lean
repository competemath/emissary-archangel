/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.PatternRunsOnMatter.Module
public import PolyFun.PFunctor.Cofree.FiniteProjection


-- @@ L11-18 verbatim
/-!
# Regression tests for pattern running on matter

The decisive example below uses different branching types in the pattern and
matter and follows two different directions in each. It detects a swapped
tensor factor, a repeated root, a discarded continuation, or a backward map
that records only the final edge.
-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-22 verbatim
universe pA pB pA' pB' qA qB qA' qB' u


-- @@ L24-24 verbatim
namespace PFunctor

-- @@ L25-25 verbatim
namespace PatternRunsOnMatterTest


-- @@ L27-31 verbatim
/-- The executable interaction does not identify any of the four generator
universes. -/
example (P : PFunctor.{pA, pB}) (Q : PFunctor.{qA, qB}) :
    Lens (FreeP P ⊗ CofreeP Q) (FreeP (P ⊗ Q)) :=
  FreeP.runOn P Q


-- @@ L33-40 verbatim
/-- Naturality likewise preserves all eight source/target generator
universes. -/
example {P : PFunctor.{pA, pB}} {P' : PFunctor.{pA', pB'}}
    {Q : PFunctor.{qA, qB}} {Q' : PFunctor.{qA', qB'}}
    (f : Lens P P') (g : Lens Q Q') :
    FreeP.runOn P' Q' ∘ₗ (FreeP.map f ⊗ₗ CofreeP.map g) =
      FreeP.map (f ⊗ₗ g) ∘ₗ FreeP.runOn P Q :=
  FreeP.runOn_natural f g


-- @@ L42-46 verbatim
/-- The convolution/free-universal construction needs only the direction
ceiling induced by the matter polynomial, not a square category. -/
example (P : PFunctor.{pA, max qA qB}) (Q : PFunctor.{qA, qB}) :
    Lens (FreeP P ⊗ CofreeP Q) (FreeP (P ⊗ Q)) :=
  FreeP.xi P Q


-- @@ L48-50 verbatim
example (P : PFunctor.{pA, max qA qB}) (Q : PFunctor.{qA, qB}) :
    FreeP.runOn P Q = FreeP.xi P Q :=
  FreeP.runOn_eq_xi P Q


-- @@ L52-58 verbatim
example {P : PFunctor.{pA, max qA qB}}
    {P' : PFunctor.{pA', max qA' qB'}}
    {Q : PFunctor.{qA, qB}} {Q' : PFunctor.{qA', qB'}}
    (f : Lens P P') (g : Lens Q Q') :
    FreeP.xi P' Q' ∘ₗ (FreeP.map f ⊗ₗ CofreeP.map g) =
      FreeP.map (f ⊗ₗ g) ∘ₗ FreeP.xi P Q :=
  FreeP.xi_natural f g


-- @@ L60-64 verbatim
/-- A square category remains an important specialization for the module
coherence laws. -/
example (P Q : PFunctor.{u, u}) :
    Lens (FreeP P ⊗ CofreeP Q) (FreeP (P ⊗ Q)) :=
  FreeP.xi P Q


-- @@ L66-68 verbatim
example (P Q : PFunctor.{u, u}) :
    FreeP.runOn P Q = FreeP.xi P Q :=
  FreeP.runOn_eq_xi P Q


-- @@ L70-75 verbatim
example (P : PFunctor.{u, u}) :
    (FreeP.map (Lens.Equiv.tensorY (P := P)).toLens ∘ₗ
        FreeP.runOn P y.{u, u}) ∘ₗ
        (Lens.id (FreeP P) ⊗ₗ CofreeP.laxUnit.{u, u}) =
      (Lens.Equiv.tensorY (P := FreeP P)).toLens :=
  FreeP.runOn_unit P


-- @@ L77-88 verbatim
example (P Q R : PFunctor.{u, u}) :
    (FreeP.runOn P (Q ⊗ R) ∘ₗ
        (Lens.id (FreeP P) ⊗ₗ CofreeP.laxTensor Q R)) ∘ₗ
        (Lens.Equiv.tensorAssoc
          (P := FreeP P) (Q := CofreeP Q)
          (R := CofreeP R)).toLens =
      (FreeP.map
          (Lens.Equiv.tensorAssoc
            (P := P) (Q := Q) (R := R)).toLens ∘ₗ
        FreeP.runOn (P ⊗ Q) R) ∘ₗ
        (FreeP.runOn P Q ⊗ₗ Lens.id (CofreeP R)) :=
  FreeP.runOn_assoc P Q R


-- @@ L90-90 verbatim
abbrev patternP : PFunctor := ⟨Bool, fun _ => Bool⟩


-- @@ L92-97 verbatim
inductive MatterLabel where
  | initial
  | afterZero
  | afterOne
  | afterTwo
  deriving DecidableEq


-- @@ L99-99 verbatim
abbrev matterP : PFunctor := ⟨MatterLabel, fun _ => Fin 3⟩


-- @@ L101-104 verbatim
def pattern : (FreeP patternP).A :=
  .liftBind false fun first =>
    .liftBind first fun _ =>
      .pure PUnit.unit


-- @@ L106-112 verbatim
def matterStep (history : List (Fin 3)) : matterP (List (Fin 3)) :=
  ⟨match history.head? with
    | none => .initial
    | some 0 => .afterZero
    | some 1 => .afterOne
    | some _ => .afterTwo,
    fun direction => direction :: history⟩


-- @@ L114-114 verbatim
def matter : (CofreeP matterP).A := M.corec matterStep []


-- @@ L116-117 verbatim
def oneNode : (FreeP patternP).A :=
  .liftBind false fun _ : Bool => .pure PUnit.unit


-- @@ L119-121 verbatim
def oneNodeOutputPath : FreeM.Path
    ((FreeP.runOn patternP matterP).toFunA (oneNode, matter)) :=
  ⟨(true, 2), ⟨⟩⟩


-- @@ L123-126 verbatim
/-- Observe the root operation label of a nonempty free tree. -/
def rootLabel {P : PFunctor} {α : Type} : FreeM P α → Option P.A
  | .pure _ => none
  | .liftBind operation _ => some operation


-- @@ L128-133 verbatim
/-- The forward one-node run synchronizes the pattern and matter root labels
in the advertised tensor order. -/
example : rootLabel
    ((FreeP.runOn patternP matterP).toFunA (oneNode, matter)) =
      some (false, .initial) :=
  rfl


-- @@ L135-141 verbatim
/-- One synchronized step pairs the two root labels and preserves the order
of the pattern and matter directions in the backward result. -/
example :
    (FreeP.runOn patternP matterP).toFunB
      (oneNode, matter) oneNodeOutputPath =
      (⟨true, ⟨⟩⟩, .child 2 (.root _)) :=
  rfl


-- @@ L143-150 verbatim
/-- A leaf pattern terminates immediately and returns the unadvanced matter
root through the backward map. -/
example :
    (FreeP.runOn patternP matterP).toFunB
        ((FreeM.pure PUnit.unit : (FreeP patternP).A), matter)
        ⟨⟩ =
      (⟨⟩, .root matter) :=
  rfl


-- @@ L152-156 verbatim
/-- The chosen output path takes pattern branches `[false, true]` and matter
branches `[2, 0]`. -/
def outputPath : FreeM.Path
    ((FreeP.runOn patternP matterP).toFunA (pattern, matter)) :=
  ⟨(false, 2), ⟨(true, 0), ⟨⟩⟩⟩


-- @@ L158-159 verbatim
def expectedPatternPath : FreeM.Path pattern :=
  ⟨false, ⟨true, ⟨⟩⟩⟩


-- @@ L161-162 verbatim
def expectedMatterVertex : M.Vertex matter :=
  .child 2 (.child 0 (.root _))


-- @@ L164-169 verbatim
/-- The complete dependent backward result records both synchronized steps in
the correct factor order. -/
example :
    (FreeP.runOn patternP matterP).toFunB (pattern, matter) outputPath =
      (expectedPatternPath, expectedMatterVertex) :=
  rfl


-- @@ L171-173 verbatim
/-- The synchronized traversal consumes exactly two matter edges before the
finite pattern terminates. -/
example : M.Vertex.depth expectedMatterVertex = 2 := rfl


-- @@ L175-178 verbatim
/-- Change both operation labels and pull target branches back through a
nonidentity permutation. -/
def patternFlip : Lens patternP patternP :=
  (fun label => !label) ⇆ (fun _ direction => !direction)


-- @@ L180-187 verbatim
/-- Rotate ternary directions while changing the visible matter state. -/
def matterRotate : Lens matterP matterP :=
  (fun label => match label with
    | .initial => .afterOne
    | .afterZero => .afterTwo
    | .afterOne => .initial
    | .afterTwo => .afterZero) ⇆
  (fun _ direction => (direction + 1) % 3)


-- @@ L189-192 verbatim
def mappedAction : Lens (FreeP patternP ⊗ CofreeP matterP)
    (FreeP (patternP ⊗ matterP)) :=
  FreeP.runOn patternP matterP ∘ₗ
    (FreeP.map patternFlip ⊗ₗ CofreeP.map matterRotate)


-- @@ L194-196 verbatim
def mappedOutputPath : FreeM.Path
    (mappedAction.toFunA (pattern, matter)) :=
  ⟨(false, 2), ⟨(true, 0), ⟨⟩⟩⟩


-- @@ L198-203 verbatim
/-- Read a pattern path as its root-to-leaf direction sequence. -/
def patternDirections : (tree : (FreeP patternP).A) →
    FreeM.Path tree → List Bool
  | .pure _, _ => []
  | .liftBind _ rest, path =>
      path.1 :: patternDirections (rest path.1) path.2


-- @@ L205-210 verbatim
/-- Observe the first direction of a matter vertex without exposing its
dependent tail. -/
def matterFirst : {tree : (CofreeP matterP).A} →
    M.Vertex tree → Option (Fin 3)
  | _, .root _ => none
  | _, .child direction _ => some direction


-- @@ L212-216 verbatim
/-- Read every matter direction, erasing only the dependent subtree indices. -/
def matterDirections : {tree : (CofreeP matterP).A} →
    M.Vertex tree → List (Fin 3)
  | _, .root _ => []
  | _, .child direction next => direction :: matterDirections next


-- @@ L218-223 verbatim
/-- The nonidentity pattern map is observable in the complete pulled-back
pattern path: both Boolean directions are flipped. -/
example :
    let pulled := mappedAction.toFunB (pattern, matter) mappedOutputPath
    patternDirections pattern pulled.1 = [true, false] := by
  rfl


-- @@ L225-228 verbatim
/-- The mapped forward root observes both nonidentity label maps. -/
example : rootLabel (mappedAction.toFunA (pattern, matter)) =
    some (true, .afterOne) := by
  rfl


-- @@ L230-238 verbatim
/-- The mapped matter vertex starts with the rotated source direction. -/
example :
    let pulled := mappedAction.toFunB (pattern, matter) mappedOutputPath
    matterFirst pulled.2 = some 0 := by
  change matterFirst
      (M.Vertex.pullMapLens matterRotate matter
        (.child 2 (.child 0 (.root _)))) = some 0
  rw [M.Vertex.pullMapLens_child]
  rfl


-- @@ L240-249 verbatim
/-- Pulling through the nonidentity matter map preserves the complete
two-edge traversal rather than truncating its dependent tail. -/
example :
    let pulled := mappedAction.toFunB (pattern, matter) mappedOutputPath
    M.Vertex.depth pulled.2 = 2 := by
  change M.Vertex.depth
      (M.Vertex.pullMapLens matterRotate matter
        (.child 2 (.child 0 (.root _)))) = 2
  rw [M.Vertex.depth_pullMapLens]
  rfl


-- @@ L251-253 verbatim
/-- Both generator-level direction rotations used by the depth-two mapped
path are pinned independently. -/
example : matterRotate.toFunB .initial 2 = 0 := rfl


-- @@ L255-255 verbatim
example : matterRotate.toFunB .afterZero 0 = 1 := rfl


-- @@ L257-258 verbatim
def mappedMatter : (CofreeP matterP).A :=
  (CofreeP.map matterRotate).toFunA matter


-- @@ L260-263 verbatim
def mappedMatterDirection :
    (compNth matterP 2).B
      ((CofreeP.projectionN matterP 2).toFunA mappedMatter) :=
  ⟨2, ⟨0, PUnit.unit⟩⟩


-- @@ L265-267 verbatim
def mappedMatterVertex : M.Vertex mappedMatter :=
  (CofreeP.projectionN matterP 2).toFunB
    mappedMatter mappedMatterDirection


-- @@ L269-295 verbatim
/-- Both rotated directions occur in the actual mapped cofree traversal. -/
theorem mappedMatterDirections :
    matterDirections
      ((CofreeP.map matterRotate).toFunB matter mappedMatterVertex) =
        [0, 1] := by
  let F := CofreeP.mapHom matterRotate
  have h := congrArg
    (fun lens : Lens (CofreeP.comonoid matterP).carrier
        (compNth matterP 2) =>
      lens.toFunB matter mappedMatterDirection)
    (CofreeP.hom_comp_projectionN F 2)
  dsimp only [mappedMatterVertex]
  change matterDirections
      ((F.toLens ⨟ CofreeP.projectionN matterP 2).toFunB
        matter mappedMatterDirection) = [0, 1]
  have hdirections := congrArg matterDirections h
  have hrestrict :
      CofreeP.restrict (CofreeP.comonoid matterP) F =
        matterRotate ∘ₗ CofreeP.cogenerator matterP := by
    dsimp only [F, CofreeP.restrict]
    exact CofreeP.cogenerator_comp_map matterRotate
  exact hdirections.trans (by
    rw [hrestrict]
    simp only [CofreeP.comonoid_carrier, compNth,
      Lens.compNthMap_succ, Lens.compNthMap_zero,
      Comonoid.comultN_succ, Comonoid.comultN_zero]
    rfl)


-- @@ L297-304 verbatim
/-- The mapped interaction uses that complete cofree pullback, not merely its
first edge and depth. -/
example :
    let pulled := mappedAction.toFunB (pattern, matter) mappedOutputPath
    matterDirections pulled.2 = [0, 1] := by
  change matterDirections
      ((CofreeP.map matterRotate).toFunB matter mappedMatterVertex) = [0, 1]
  exact mappedMatterDirections


-- @@ L306-313 verbatim
/-- Proposition 3.3 is exercised with observable nonidentity maps in both
factors, rather than only identities or unit signatures. -/
example :
    FreeP.runOn patternP matterP ∘ₗ
        (FreeP.map patternFlip ⊗ₗ CofreeP.map matterRotate) =
      FreeP.map (patternFlip ⊗ₗ matterRotate) ∘ₗ
        FreeP.runOn patternP matterP :=
  FreeP.runOn_natural patternFlip matterRotate


-- @@ L315-323 verbatim
/-- The universal construction computes the same complete labelled object on
the decisive depth-two input, including its backward map. -/
example :
    FreeP.runObj pattern matter =
      Lens.mapObj (FreeP.xi patternP matterP)
        (⟨(pattern, matter), id⟩ :
          (FreeP patternP ⊗ CofreeP matterP).Obj
            (FreeM.Path pattern × M.Vertex matter)) :=
  FreeP.runObj_eq_xi_mapObj patternP matterP pattern matter


-- @@ L325-334 verbatim
/-- Unit coherence is operationally nontrivial on the two-node pattern. -/
example :
    ((FreeP.map (Lens.Equiv.tensorY (P := patternP)).toLens ∘ₗ
        FreeP.runOn patternP y) ∘ₗ
        (Lens.id (FreeP patternP) ⊗ₗ CofreeP.laxUnit)).toFunA
        (pattern, PUnit.unit) = pattern :=
  congrArg
    (fun lens : Lens (FreeP patternP ⊗ y) (FreeP patternP) =>
      lens.toFunA (pattern, PUnit.unit))
    (FreeP.runOn_unit patternP)


-- @@ L336-339 verbatim
def unitAction : Lens (FreeP patternP ⊗ y.{0, 0}) (FreeP patternP) :=
  (FreeP.map (Lens.Equiv.tensorY (P := patternP)).toLens ∘ₗ
      FreeP.runOn patternP y) ∘ₗ
    (Lens.id (FreeP patternP) ⊗ₗ CofreeP.laxUnit)


-- @@ L341-346 verbatim
/-- Unit coherence preserves a complete nonempty pattern path through the
backward map, including the unit direction discarded by tensor unitor. -/
example :
    unitAction.toFunB (pattern, PUnit.unit) expectedPatternPath =
      (expectedPatternPath, PUnit.unit) :=
  rfl


-- @@ L348-348 verbatim
abbrev auxiliaryP : PFunctor := ⟨Bool, fun _ => Bool⟩


-- @@ L350-351 verbatim
def auxiliaryStep (history : List Bool) : auxiliaryP (List Bool) :=
  ⟨history.head?.getD false, fun direction => direction :: history⟩


-- @@ L353-354 verbatim
def auxiliaryMatter : (CofreeP auxiliaryP).A :=
  M.corec auxiliaryStep []


-- @@ L356-364 verbatim
def assocLhs :
    Lens ((FreeP patternP ⊗ CofreeP matterP) ⊗ CofreeP auxiliaryP)
      (FreeP (patternP ⊗ (matterP ⊗ auxiliaryP))) :=
  (FreeP.runOn patternP (matterP ⊗ auxiliaryP) ∘ₗ
      (Lens.id (FreeP patternP) ⊗ₗ
        CofreeP.laxTensor matterP auxiliaryP)) ∘ₗ
    (Lens.Equiv.tensorAssoc
      (P := FreeP patternP) (Q := CofreeP matterP)
      (R := CofreeP auxiliaryP)).toLens


-- @@ L366-373 verbatim
def assocRhs :
    Lens ((FreeP patternP ⊗ CofreeP matterP) ⊗ CofreeP auxiliaryP)
      (FreeP (patternP ⊗ (matterP ⊗ auxiliaryP))) :=
  (FreeP.map
      (Lens.Equiv.tensorAssoc
        (P := patternP) (Q := matterP) (R := auxiliaryP)).toLens ∘ₗ
      FreeP.runOn (patternP ⊗ matterP) auxiliaryP) ∘ₗ
    (FreeP.runOn patternP matterP ⊗ₗ Lens.id (CofreeP auxiliaryP))


-- @@ L375-377 verbatim
def assocOutputPath : FreeM.Path
    (assocRhs.toFunA ((pattern, matter), auxiliaryMatter)) :=
  ⟨(false, (2, true)), ⟨(true, (0, false)), ⟨⟩⟩⟩


-- @@ L379-380 verbatim
def expectedAuxiliaryVertex : M.Vertex auxiliaryMatter :=
  .child true (.child false (.root _))


-- @@ L382-386 verbatim
/-- Read every auxiliary direction, erasing only dependent subtree indices. -/
def auxiliaryDirections : {tree : (CofreeP auxiliaryP).A} →
    M.Vertex tree → List Bool
  | _, .root _ => []
  | _, .child direction next => direction :: auxiliaryDirections next


-- @@ L388-390 verbatim
def synchronizedMatter : (CofreeP (matterP ⊗ auxiliaryP)).A :=
  (CofreeP.laxTensor matterP auxiliaryP).toFunA
    (matter, auxiliaryMatter)


-- @@ L392-396 verbatim
def synchronizedDirection :
    (compNth (matterP ⊗ auxiliaryP) 2).B
      ((CofreeP.projectionN (matterP ⊗ auxiliaryP) 2).toFunA
        synchronizedMatter) :=
  ⟨(2, true), ⟨(0, false), PUnit.unit⟩⟩


-- @@ L398-400 verbatim
def synchronizedVertex : M.Vertex synchronizedMatter :=
  (CofreeP.projectionN (matterP ⊗ auxiliaryP) 2).toFunB
    synchronizedMatter synchronizedDirection


-- @@ L402-443 verbatim
/-- The cofree laxator's finite projection independently exposes both
component direction streams through its cast-free universal equation. -/
theorem synchronizedBackwardDirections :
    let pulled := (CofreeP.laxTensor matterP auxiliaryP).toFunB
      (matter, auxiliaryMatter) synchronizedVertex
    matterDirections pulled.1 = [2, 0] ∧
      auxiliaryDirections pulled.2 = [true, false] := by
  let F := CofreeP.laxTensorHom matterP auxiliaryP
  have h := congrArg
    (fun lens : Lens
        ((CofreeP.comonoid matterP).tensor
          (CofreeP.comonoid auxiliaryP)).carrier
        (compNth (matterP ⊗ auxiliaryP) 2) =>
      lens.toFunB (matter, auxiliaryMatter) synchronizedDirection)
    (CofreeP.hom_comp_projectionN F 2)
  dsimp only [synchronizedVertex]
  change
    matterDirections
        ((F.toLens ⨟
          CofreeP.projectionN (matterP ⊗ auxiliaryP) 2).toFunB
          (matter, auxiliaryMatter) synchronizedDirection).1 = [2, 0] ∧
      auxiliaryDirections
        ((F.toLens ⨟
          CofreeP.projectionN (matterP ⊗ auxiliaryP) 2).toFunB
          (matter, auxiliaryMatter) synchronizedDirection).2 = [true, false]
  have hmatter := congrArg (fun pair => matterDirections pair.1) h
  have hauxiliary := congrArg (fun pair => auxiliaryDirections pair.2) h
  constructor
  · exact hmatter.trans (by
      dsimp only [F, CofreeP.laxTensorHom]
      rw [CofreeP.restrict_extend]
      simp only [CofreeP.comonoid_carrier, Comonoid.tensor_carrier, compNth,
        Lens.compNthMap_succ, Lens.compNthMap_zero,
        Comonoid.comultN_succ, Comonoid.comultN_zero]
      rfl)
  · exact hauxiliary.trans (by
      dsimp only [F, CofreeP.laxTensorHom]
      rw [CofreeP.restrict_extend]
      simp only [CofreeP.comonoid_carrier, Comonoid.tensor_carrier, compNth,
        Lens.compNthMap_succ, Lens.compNthMap_zero,
        Comonoid.comultN_succ, Comonoid.comultN_zero]
      rfl)


-- @@ L445-448 verbatim
/-- The two parenthesizations compute the same depth-two output position. -/
example : assocLhs.toFunA ((pattern, matter), auxiliaryMatter) =
    assocRhs.toFunA ((pattern, matter), auxiliaryMatter) :=
  rfl


-- @@ L450-452 verbatim
def assocLhsOutputPath : FreeM.Path
    (assocLhs.toFunA ((pattern, matter), auxiliaryMatter)) :=
  ⟨(false, (2, true)), ⟨(true, (0, false)), ⟨⟩⟩⟩


-- @@ L454-471 verbatim
/-- The cast-heavy combined route is evaluated directly, independently of
`runOn_assoc`: it preserves the complete pattern path and both distinguishable
matter streams. -/
example :
    let pulled := assocLhs.toFunB
      ((pattern, matter), auxiliaryMatter) assocLhsOutputPath
    patternDirections pattern pulled.1.1 = [false, true] ∧
      matterDirections pulled.1.2 = [2, 0] ∧
      auxiliaryDirections pulled.2 = [true, false] := by
  dsimp only [assocLhs, assocLhsOutputPath]
  change [false, true] = [false, true] ∧
    matterDirections
        ((CofreeP.laxTensor matterP auxiliaryP).toFunB
          (matter, auxiliaryMatter) synchronizedVertex).1 = [2, 0] ∧
      auxiliaryDirections
        ((CofreeP.laxTensor matterP auxiliaryP).toFunB
          (matter, auxiliaryMatter) synchronizedVertex).2 = [true, false]
  exact ⟨rfl, synchronizedBackwardDirections⟩


-- @@ L473-481 verbatim
/-- The decisive associativity canary independently evaluates the sequential
route, distinguishing all three direction streams. Together with the explicit
full-lens theorem surface above, this pins the combined route as well. -/
example :
    assocRhs.toFunB ((pattern, matter), auxiliaryMatter)
        assocOutputPath =
      ((expectedPatternPath, expectedMatterVertex),
        expectedAuxiliaryVertex) :=
  rfl


-- @@ L483-483 verbatim
end PatternRunsOnMatterTest

-- @@ L484-484 verbatim
end PFunctor
