/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import PolyFun.PFunctor.Cofree.LaxMonoidal
public import PolyFun.PFunctor.Cofree.FiniteProjection


-- @@ L11-22 verbatim
/-!
# Regression tests for cofree lax monoidality

The generic canaries keep every generator universe pair independent and pin
naturality plus all three lax-monoidal coherence equations.  The concrete
tests synchronize two observably different behavior trees.  Their backward
maps distinguish the two factors and two different depth-two direction
sequences, so a copied, swapped, reversed, or root-only implementation fails.

This is the concrete lax-monoidal structure of Spivak–Niu, Proposition 8.79
in the current edition (Proposition 8.81 in the earlier-edition notes).
-/


-- @@ L24-24 verbatim
@[expose] public section


-- @@ L26-26 verbatim
universe pA₁ pB₁ qA₁ qB₁ rA₁ rB₁


-- @@ L28-28 verbatim
namespace PFunctor

-- @@ L29-34 verbatim
namespace CofreeLaxMonoidalTest

/- Lean 4.33 compares assigned metavariable types at implicit transparency;
the lax-monoidal examples below unfold these constants there.  The `unfold*`
family, `Lens.tensorMap`, and the comonoid tensor and unit carry the attribute
at their definition sites. -/

-- @@ L35-38 verbatim
attribute [local implicit_reducible] PFunctor.y PFunctor.monomial PFunctor.tensor
  Comonoid.Hom.ofCategoryLaws CofreeP.comonoid CofreeP.cogenerator
  CofreeP.extend CofreeP.laxUnitHom CofreeP.laxUnit CofreeP.laxTensorHom
  CofreeP.laxTensor


-- @@ L40-40 verbatim
/-! ## Universe and theorem-surface canaries -/


-- @@ L42-47 verbatim
/-- The unit comparison preserves the generator's independent position and
direction universes and lands in the diagonal universe of `CofreeP`. -/
example :
    Lens y.{max pA₁ pB₁, max pA₁ pB₁}
      (CofreeP y.{pA₁, pB₁}) :=
  CofreeP.laxUnit


-- @@ L49-52 verbatim
/-- The binary laxator leaves both input universe pairs independent. -/
example (P : PFunctor.{pA₁, pB₁}) (Q : PFunctor.{qA₁, qB₁}) :
    Lens (CofreeP P ⊗ CofreeP Q) (CofreeP (P ⊗ Q)) :=
  CofreeP.laxTensor P Q


-- @@ L54-63 verbatim
/-- Naturality is nontrivial in both factors while retaining separate
universe pairs for the two functor arguments. -/
example
    {P₁ P₂ : PFunctor.{pA₁, pB₁}}
    {Q₁ Q₂ : PFunctor.{qA₁, qB₁}}
    (f : Lens P₁ P₂) (g : Lens Q₁ Q₂) :
    CofreeP.laxTensor P₂ Q₂ ∘ₗ
        (CofreeP.map f ⊗ₗ CofreeP.map g) =
      CofreeP.map (f ⊗ₗ g) ∘ₗ CofreeP.laxTensor P₁ Q₁ :=
  CofreeP.laxTensor_natural f g


-- @@ L65-72 verbatim
/-- Left- and right-unit coherence do not identify the generator's position
and direction universes. -/
example (P : PFunctor.{pA₁, pB₁}) :
    CofreeP.map (Lens.Equiv.yTensor (P := P)).toLens ∘ₗ
        CofreeP.laxTensor y.{pA₁, pB₁} P ∘ₗ
        (CofreeP.laxUnit.{pA₁, pB₁} ⊗ₗ Lens.id (CofreeP P)) =
      (Lens.Equiv.yTensor (P := CofreeP P)).toLens :=
  CofreeP.laxTensor_unit_left P


-- @@ L74-79 verbatim
example (P : PFunctor.{pA₁, pB₁}) :
    CofreeP.map (Lens.Equiv.tensorY (P := P)).toLens ∘ₗ
        CofreeP.laxTensor P y.{pA₁, pB₁} ∘ₗ
        (Lens.id (CofreeP P) ⊗ₗ CofreeP.laxUnit.{pA₁, pB₁}) =
      (Lens.Equiv.tensorY (P := CofreeP P)).toLens :=
  CofreeP.laxTensor_unit_right P


-- @@ L81-94 verbatim
/-- Associativity retains all six position/direction universes belonging to
the three independent polynomial arguments. -/
example
    (P : PFunctor.{pA₁, pB₁}) (Q : PFunctor.{qA₁, qB₁})
    (R : PFunctor.{rA₁, rB₁}) :
    CofreeP.laxTensor P (Q ⊗ R) ∘ₗ
        (Lens.id (CofreeP P) ⊗ₗ CofreeP.laxTensor Q R) ∘ₗ
        (Lens.Equiv.tensorAssoc
          (P := CofreeP P) (Q := CofreeP Q) (R := CofreeP R)).toLens =
      CofreeP.map
          (Lens.Equiv.tensorAssoc (P := P) (Q := Q) (R := R)).toLens ∘ₗ
        CofreeP.laxTensor (P ⊗ Q) R ∘ₗ
        (CofreeP.laxTensor P Q ⊗ₗ Lens.id (CofreeP R)) :=
  CofreeP.laxTensor_assoc P Q R


-- @@ L96-96 verbatim
/-! ## Observable synchronized trees -/


-- @@ L98-102 verbatim
inductive LeftLabel where
  | initial
  | afterFalse
  | afterTrue
  deriving DecidableEq, Repr


-- @@ L104-109 verbatim
inductive RightLabel where
  | initial
  | afterZero
  | afterOne
  | afterTwo
  deriving DecidableEq, Repr


-- @@ L111-112 verbatim
/-- A binary behavior signature whose node labels remember the last branch. -/
abbrev leftP : PFunctor := ⟨LeftLabel, fun _ => Bool⟩


-- @@ L114-116 verbatim
/-- A ternary behavior signature, making the right factor's directions
definitionally different from the left factor's. -/
abbrev rightP : PFunctor := ⟨RightLabel, fun _ => Fin 3⟩


-- @@ L118-125 verbatim
/-- Reverse the observable Boolean branch of the left signature.  This is
nonidentity on both the remembered node label and the pulled-back direction. -/
def leftFlip : Lens leftP leftP where
  toFunA
    | .initial => .initial
    | .afterFalse => .afterTrue
    | .afterTrue => .afterFalse
  toFunB _ direction := !direction


-- @@ L127-135 verbatim
/-- Naturality is exercised with an actual nonidentity map in the left factor,
not only with abstract lens variables. -/
example :
    CofreeP.laxTensor leftP rightP ∘ₗ
        (CofreeP.map leftFlip ⊗ₗ
          CofreeP.map (Lens.id rightP)) =
      CofreeP.map (leftFlip ⊗ₗ Lens.id rightP) ∘ₗ
        CofreeP.laxTensor leftP rightP :=
  CofreeP.laxTensor_natural leftFlip (Lens.id rightP)


-- @@ L137-142 verbatim
def leftStep (history : List Bool) : leftP (List Bool) :=
  ⟨match history.head? with
    | none => .initial
    | some false => .afterFalse
    | some true => .afterTrue,
    fun direction => direction :: history⟩


-- @@ L144-150 verbatim
def rightStep (history : List (Fin 3)) : rightP (List (Fin 3)) :=
  ⟨match history.head? with
    | none => .initial
    | some 0 => .afterZero
    | some 1 => .afterOne
    | some _ => .afterTwo,
    fun direction => direction :: history⟩


-- @@ L152-152 verbatim
def leftTree : M leftP := M.corec leftStep []


-- @@ L154-154 verbatim
def rightTree : M rightP := M.corec rightStep []


-- @@ L156-169 verbatim
/-- The concrete map used above is observably nonidentity: a target `false`
edge is pulled back to a source `true` edge. -/
example :
    match (CofreeP.map leftFlip).toFunB leftTree
        (.child false (.root _)) with
    | .child direction _ => direction = true
    | .root _ => False := by
  change
    match M.Vertex.pullMapLens leftFlip leftTree
        (.child false (.root _)) with
    | .child direction _ => direction = true
    | .root _ => False
  rw [M.Vertex.pullMapLens_child]
  rfl


-- @@ L171-174 verbatim
/-- The synchronized tree advances the two inputs only along paired
directions. -/
def synchronizedTree : M (leftP ⊗ rightP) :=
  (CofreeP.laxTensor leftP rightP).toFunA (leftTree, rightTree)


-- @@ L176-185 verbatim
/-- The two different root-label types and values make factor order visible. -/
example : M.head synchronizedTree = (.initial, .initial) := by
  change M.head
      (CofreeP.unfoldShape
        (Comonoid.tensor (CofreeP.comonoid leftP)
          (CofreeP.comonoid rightP))
        (CofreeP.cogenerator leftP ⊗ₗ CofreeP.cogenerator rightP)
        (leftTree, rightTree)) = _
  rw [CofreeP.head_unfoldShape]
  rfl


-- @@ L187-201 verbatim
/-- Pulling back the synchronized root returns both source roots, not a copied
or swapped component. -/
example :
    (CofreeP.laxTensor leftP rightP).toFunB
        (leftTree, rightTree) (.root synchronizedTree) =
      (.root leftTree, .root rightTree) := by
  calc
    _ = Comonoid.identity
          (Comonoid.tensor (CofreeP.comonoid leftP)
            (CofreeP.comonoid rightP))
          (leftTree, rightTree) := by
      simpa [synchronizedTree] using
        (CofreeP.laxTensorHom leftP rightP).map_identity
          (leftTree, rightTree)
    _ = (.root leftTree, .root rightTree) := rfl


-- @@ L203-213 verbatim
/-- One synchronized edge pulls back to the matching edge in each source
tree.  This is the executable content of the laxator's generator equation. -/
theorem laxTensor_oneLayer (left : M leftP) (right : M rightP)
    (direction : Bool × Fin 3) :
    (CofreeP.laxTensor leftP rightP).toFunB (left, right)
        (.child direction (.root _)) =
      (.child direction.1 (.root _), .child direction.2 (.root _)) := by
  exact congrArg
    (fun lens : Lens (CofreeP leftP ⊗ CofreeP rightP) (leftP ⊗ rightP) =>
      lens.toFunB (left, right) direction)
    (CofreeP.cogenerator_comp_laxTensor leftP rightP)


-- @@ L215-217 verbatim
/-- The first edge of the decisive synchronized path. -/
def synchronizedOuter : M.Vertex synchronizedTree :=
  .child (false, 2) (.root _)


-- @@ L219-221 verbatim
/-- The second edge starts in the subtree selected by `synchronizedOuter`. -/
def synchronizedInner : M.Vertex (M.Vertex.subtree synchronizedOuter) :=
  .child (true, 0) (.root _)


-- @@ L223-225 verbatim
/-- A depth-two synchronized vertex with different component paths. -/
def synchronizedVertex : M.Vertex synchronizedTree :=
  M.Vertex.append synchronizedOuter synchronizedInner


-- @@ L227-230 verbatim
/-- Read the directions of a finite left-hand vertex from root to leaf. -/
def leftDirections : {tree : M leftP} → M.Vertex tree → List Bool
  | _, .root _ => []
  | _, .child direction next => direction :: leftDirections next


-- @@ L232-235 verbatim
/-- Read the directions of a finite right-hand vertex from root to leaf. -/
def rightDirections : {tree : M rightP} → M.Vertex tree → List (Fin 3)
  | _, .root _ => []
  | _, .child direction next => direction :: rightDirections next


-- @@ L237-245 verbatim
/-- The depth-two composite direction selecting the decisive synchronized
path. -/
def synchronizedDirection :
    (compNth (leftP ⊗ rightP) 2).B
      ((CofreeP.projectionN (leftP ⊗ rightP) 2).toFunA synchronizedTree) :=
  by
    refine ⟨(false, 2), ?_⟩
    refine ⟨(true, 0), ?_⟩
    exact PUnit.unit


-- @@ L247-252 verbatim
/-- The finite depth-two projection selects exactly the append-built vertex
used by the executable behavior test. -/
example :
    (CofreeP.projectionN (leftP ⊗ rightP) 2).toFunB
      synchronizedTree synchronizedDirection = synchronizedVertex :=
  rfl


-- @@ L254-295 verbatim
/-- The backward map preserves both component sequences in outer-to-inner
order.  This detects swapped factors, copied directions, reversed paths, and
an implementation that only handles the root or first layer. -/
example :
    let pulled := (CofreeP.laxTensor leftP rightP).toFunB
      (leftTree, rightTree)
      ((CofreeP.projectionN (leftP ⊗ rightP) 2).toFunB
        synchronizedTree synchronizedDirection)
    leftDirections pulled.1 = [false, true] ∧
      rightDirections pulled.2 = [2, 0] := by
  let F := CofreeP.laxTensorHom leftP rightP
  have h := congrArg
    (fun lens : Lens
        ((CofreeP.comonoid leftP).tensor (CofreeP.comonoid rightP)).carrier
        (compNth (leftP ⊗ rightP) 2) =>
      lens.toFunB (leftTree, rightTree) synchronizedDirection)
    (CofreeP.hom_comp_projectionN F 2)
  dsimp only
  change
    leftDirections
        ((F.toLens ⨟ CofreeP.projectionN (leftP ⊗ rightP) 2).toFunB
          (leftTree, rightTree) synchronizedDirection).1 = [false, true] ∧
      rightDirections
        ((F.toLens ⨟ CofreeP.projectionN (leftP ⊗ rightP) 2).toFunB
          (leftTree, rightTree) synchronizedDirection).2 = [2, 0]
  have hleft := congrArg (fun pair => leftDirections pair.1) h
  have hright := congrArg (fun pair => rightDirections pair.2) h
  constructor
  · exact hleft.trans (by
      dsimp only [F, CofreeP.laxTensorHom]
      rw [CofreeP.restrict_extend]
      simp only [CofreeP.comonoid_carrier, Comonoid.tensor_carrier, compNth,
        Lens.compNthMap_succ, Lens.compNthMap_zero,
        Comonoid.comultN_succ, Comonoid.comultN_zero]
      rfl)
  · exact hright.trans (by
      dsimp only [F, CofreeP.laxTensorHom]
      rw [CofreeP.restrict_extend]
      simp only [CofreeP.comonoid_carrier, Comonoid.tensor_carrier, compNth,
        Lens.compNthMap_succ, Lens.compNthMap_zero,
        Comonoid.comultN_succ, Comonoid.comultN_zero]
      rfl)


-- @@ L297-297 verbatim
/-! ## Observable lax unit -/


-- @@ L299-300 verbatim
def unitTree : M y :=
  CofreeP.laxUnit.toFunA PUnit.unit


-- @@ L302-307 verbatim
/-- A non-root unit vertex is an elaboration and totality canary for finite
paths.  Its output is necessarily unobservable because every direction of the
tensor unit is `PUnit`. -/
def unitDepthTwo : M.Vertex unitTree :=
  .child PUnit.unit
    (.child PUnit.unit (.root _))


-- @@ L309-309 verbatim
example : CofreeP.laxUnit.toFunB PUnit.unit unitDepthTwo = PUnit.unit := rfl


-- @@ L311-311 verbatim
end CofreeLaxMonoidalTest

-- @@ L312-312 verbatim
end PFunctor
