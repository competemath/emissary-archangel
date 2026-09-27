/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import LeanPool.Kurosh.KuroshTree


-- @@ L10-20 verbatim
/-! The universal cover of the quotient graph of groups.

The source group is the explicit free product of the vertex stabilizers and
the quotient free part.  A cover vertex is a quotient-graph vertex together
with a right coset of its source vertex group.  This is the standard
Bass--Serre construction, with the edge group trivial.

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/


-- @@ L22-22 verbatim
@[expose] public section


-- @@ L24-24 verbatim
open Set Function

-- @@ L25-25 verbatim
open CategoryTheory

-- @@ L26-26 verbatim
open scoped Pointwise

-- @@ L27-27 verbatim
noncomputable section


-- @@ L29-31 verbatim
/-- Classical equality used locally in this part of the Kurosh construction. -/
local instance GraphCoveringTheory.Kurosh.kuroshCoverDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α


-- @@ L33-33 verbatim
universe u v w


-- @@ L35-35 verbatim
namespace GraphCoveringTheory.Kurosh


-- @@ L37-37 verbatim
open Monoid.CoprodI


-- @@ L39-42 verbatim
/-- The tree Kurosh product acting on the auxiliary covering graph. -/
abbrev CoverSource {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :=
  @TreeKuroshProduct.{u, v, 0} ι G _ H


-- @@ L44-48 verbatim
/-- Cosets of the image of a vertex stabilizer in the tree Kurosh product. -/
abbrev CoverVertexCoset {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) :=
  RightCoset (MonoidHom.range (treeKuroshVertexInclusion G H a))


-- @@ L50-53 verbatim
/-- Vertices of the auxiliary cover, given by a quotient vertex and a stabilizer coset. -/
abbrev CoverVertex {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :=
  Σ a : RawBassSerreOrbitVertex G H, CoverVertexCoset G H a


-- @@ L55-58 verbatim
/-- An edge of the quotient graph, bundled with its endpoints. -/
abbrev CoverEdge {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :=
  Σ a b : RawBassSerreOrbitVertex G H, a ⟶ b


-- @@ L60-64 verbatim
/-- The based loop of a quotient edge included in the free factor of the covering group. -/
noncomputable def coverEdgeLetter {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (e : CoverEdge G H) : CoverSource G H :=
  treeKuroshFreeInclusion G H (quotientEdgeLoop G H e.2.2)


-- @@ L66-71 verbatim
/-- The source coset of an edge labeled by a covering-group element. -/
def coverEdgeSource {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (d : CoverSource G H × CoverEdge G H) : CoverVertex G H :=
  ⟨d.2.1, rightCosetMk (MonoidHom.range
    (treeKuroshVertexInclusion G H d.2.1)) d.1⟩


-- @@ L73-79 verbatim
/-- The target coset after multiplication by the inverse edge letter. -/
def coverEdgeTarget {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (d : CoverSource G H × CoverEdge G H) : CoverVertex G H :=
  ⟨d.2.2.1, rightCosetMk (MonoidHom.range
    (treeKuroshVertexInclusion G H d.2.2.1))
      (d.1 * (coverEdgeLetter G H d.2)⁻¹)⟩


-- @@ L81-85 verbatim
/-- The auxiliary quiver of stabilizer cosets and labeled quotient edges. -/
@[reducible] def coverQuiver {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) : Quiver (CoverVertex G H) where
  Hom x y := {d : CoverSource G H × CoverEdge G H //
    coverEdgeSource G H d = x ∧ coverEdgeTarget G H d = y}


-- @@ L87-89 verbatim
instance coverQuiverInst {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    Quiver (CoverVertex G H) := coverQuiver G H


-- @@ L91-133 verbatim
instance coverSourceMulAction {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    MulAction (CoverSource G H) (CoverVertex G H) where
  smul p x := ⟨x.1, rightCosetMk (MonoidHom.range
    (treeKuroshVertexInclusion G H x.1)) (p * Quotient.out x.2)⟩
  one_smul x := by
    cases x with
    | mk a q =>
      change (⟨a, rightCosetMk (MonoidHom.range
        (treeKuroshVertexInclusion G H a)) (1 * Quotient.out q)⟩ :
        CoverVertex G H) = (⟨a, q⟩ : CoverVertex G H)
      apply congrArg (Sigma.mk a)
      change rightCosetMk (MonoidHom.range
        (treeKuroshVertexInclusion G H a)) (1 * Quotient.out q) = q
      rw [one_mul]
      exact Quotient.out_eq q
  mul_smul p q x := by
    cases x with
    | mk a r =>
      change (⟨a, rightCosetMk (MonoidHom.range
        (treeKuroshVertexInclusion G H a)) ((p * q) * Quotient.out r)⟩ :
        CoverVertex G H) =
        (⟨a, rightCosetMk (MonoidHom.range
          (treeKuroshVertexInclusion G H a))
          (p * Quotient.out (rightCosetMk (MonoidHom.range
            (treeKuroshVertexInclusion G H a)) (q * Quotient.out r)))⟩ :
          CoverVertex G H)
      apply congrArg (Sigma.mk a)
      let K := MonoidHom.range (treeKuroshVertexInclusion G H a)
      let c := rightCosetMk K (q * Quotient.out r)
      have hc : rightCosetMk K (q * Quotient.out r) =
          rightCosetMk K (Quotient.out c) := by
        exact (Quotient.out_eq c).symm
      rcases (rightCosetMk_eq_iff K _ _).1 hc with ⟨k, hk⟩
      apply (rightCosetMk_eq_iff K _ _).2
      refine ⟨k, ?_⟩
      change (p * q) * Quotient.out r * (k : CoverSource G H) =
        p * Quotient.out c
      calc
        (p * q) * Quotient.out r * (k : CoverSource G H) =
            p * (q * Quotient.out r * (k : CoverSource G H)) := by
              simp [mul_assoc]
        _ = p * Quotient.out c := by rw [hk]


-- @@ L135-141 verbatim
@[simp] theorem coverSourceMulAction_mk {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (p : CoverSource G H) (a : RawBassSerreOrbitVertex G H)
    (q : CoverVertexCoset G H a) :
    p • (⟨a, q⟩ : CoverVertex G H) =
      ⟨a, rightCosetMk (MonoidHom.range
        (treeKuroshVertexInclusion G H a)) (p * Quotient.out q)⟩ := rfl


-- @@ L143-151 verbatim
theorem coverSource_vertexRange_smul {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H)
    (k : MonoidHom.range (treeKuroshVertexInclusion G H a)) :
    (treeKuroshProductToH G H k.1).1 •
        rawTreeRepresentative G H a = rawTreeRepresentative G H a := by
  rcases k.property with ⟨x, hx⟩
  rw [← hx, treeKuroshProductToH_vertex]
  exact x.property


-- @@ L153-182 verbatim
/-- Evaluate a covering coset on the chosen representative in the Bass-Serre graph. -/
noncomputable def coverVertexMap {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    CoverVertex G H → RawBassSerreVertex G
  | ⟨a, c⟩ => Quotient.lift
      (fun p : CoverSource G H =>
        (treeKuroshProductToH G H p).1 • rawTreeRepresentative G H a)
      (by
        intro p q hpq
        rcases hpq with ⟨k, hk⟩
        rcases k.property with ⟨x, hx⟩
        rw [← hk, map_mul, ← hx, treeKuroshProductToH_vertex]
        change (treeKuroshProductToH G H p).1 •
            rawTreeRepresentative G H a =
          ((treeKuroshProductToH G H p).1 * x.1) •
            rawTreeRepresentative G H a
        calc
          (treeKuroshProductToH G H p).1 •
              rawTreeRepresentative G H a =
            (treeKuroshProductToH G H p).1 •
              (x.1 • rawTreeRepresentative G H a) := by
                rw [x.property]
          _ = ((treeKuroshProductToH G H p).1 * x.1) •
              rawTreeRepresentative G H a := by
                change (treeKuroshProductToH G H p).1 •
                    (x.1 : FreeProduct G) • rawTreeRepresentative G H a =
                  ((treeKuroshProductToH G H p).1 *
                    (x.1 : FreeProduct G)) • rawTreeRepresentative G H a
                exact smul_smul _ _ _)
      c


-- @@ L184-190 verbatim
@[simp] theorem coverVertexMap_mk {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) (p : CoverSource G H) :
    coverVertexMap G H
      (⟨a, rightCosetMk (MonoidHom.range
        (treeKuroshVertexInclusion G H a)) p⟩ : CoverVertex G H) =
      (treeKuroshProductToH G H p).1 • rawTreeRepresentative G H a := rfl


-- @@ L192-272 verbatim
/-- Project an auxiliary covering edge to the Bass-Serre graph. -/
noncomputable def coverEdgeMap {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {x y : CoverVertex G H}
    (d : @Quiver.Hom (CoverVertex G H) (coverQuiver G H) x y) :
    @Quiver.Hom (RawBassSerreVertex G) (rawBassSerreQuiver G)
      (coverVertexMap G H x) (coverVertexMap G H y) := by
  let p : CoverSource G H := d.1.1
  let e : CoverEdge G H := d.1.2
  let r : rawBassSerreEdgeData G := quotientEdgeRawData G H e.2.2
  let s : H := quotientEdgeCoherentSourceAlign G H e.2.2
  let l : H := quotientEdgeLabel G H e.2.2
  let h : H := treeKuroshProductToH G H p * s
  let base : @Quiver.Hom (RawBassSerreVertex G) (rawBassSerreQuiver G)
      (rawBassSerreEdgeDataSource G r)
      (rawBassSerreEdgeDataTarget G r) :=
    RawBassSerreEdge.centralFactor r.1 r.2
  have hsource_map :
      coverVertexMap G H x =
        (treeKuroshProductToH G H p).1 • rawTreeRepresentative G H e.1 := by
    rw [← d.2.1]
    rfl
  have hsource_raw :
      h.1 • rawBassSerreEdgeDataSource G r =
        (treeKuroshProductToH G H p).1 • rawTreeRepresentative G H e.1 := by
    change ((treeKuroshProductToH G H p).1 * (s.1 : FreeProduct G)) •
        rawBassSerreEdgeDataSource G r = _
    calc
      ((treeKuroshProductToH G H p).1 * (s.1 : FreeProduct G)) •
          rawBassSerreEdgeDataSource G r =
          (treeKuroshProductToH G H p).1 •
            (s.1 • rawBassSerreEdgeDataSource G r) := by
              exact (smul_smul _ _ _).symm
      _ = (treeKuroshProductToH G H p).1 •
          rawTreeRepresentative G H e.1 := by
            rw [quotientEdgeCoherentSourceAlign_spec G H e.2.2]
  have hsl :
      s.1 • rawBassSerreEdgeDataTarget G r =
        l.1⁻¹ • rawTreeRepresentative G H e.2.1 := by
    apply smul_left_cancel l.1
    rw [quotientEdgeLabel_transport_coherent G H e.2.2]
    simp [smul_smul]
  have htarget_map :
      coverVertexMap G H y =
        (treeKuroshProductToH G H (p * (coverEdgeLetter G H e)⁻¹)).1 •
          rawTreeRepresentative G H e.2.1 := by
    rw [← d.2.2]
    rfl
  have hletter :
      treeKuroshProductToH G H (coverEdgeLetter G H e) = l := by
    change treeKuroshProductToH G H
        (treeKuroshFreeInclusion G H (quotientEdgeLoop G H e.2.2)) = l
    rw [treeKuroshProductToH_free]
    exact kuroshFreePartHom_quotientEdgeLoop G H e.2.2
  have htarget_raw :
      h.1 • rawBassSerreEdgeDataTarget G r =
        (treeKuroshProductToH G H (p * (coverEdgeLetter G H e)⁻¹)).1 •
          rawTreeRepresentative G H e.2.1 := by
    change ((treeKuroshProductToH G H p).1 * (s.1 : FreeProduct G)) •
        rawBassSerreEdgeDataTarget G r = _
    calc
      ((treeKuroshProductToH G H p).1 * (s.1 : FreeProduct G)) •
          rawBassSerreEdgeDataTarget G r =
          (treeKuroshProductToH G H p).1 •
            (s.1 • rawBassSerreEdgeDataTarget G r) := by
              exact (smul_smul _ _ _).symm
      _ = (treeKuroshProductToH G H p).1 •
          (l.1⁻¹ • rawTreeRepresentative G H e.2.1) := by
            rw [hsl]
      _ = ((treeKuroshProductToH G H p).1 * (l.1⁻¹ : FreeProduct G)) •
          rawTreeRepresentative G H e.2.1 := by
            exact smul_smul _ _ _
      _ = (treeKuroshProductToH G H
          (p * (coverEdgeLetter G H e)⁻¹)).1 •
          rawTreeRepresentative G H e.2.1 := by
            rw [map_mul, map_inv, hletter]
            simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact Quiver.Hom.cast
    (hsource_raw.trans hsource_map.symm)
    (htarget_raw.trans htarget_map.symm)
    (rawBassSerreEdgeAction G h.1 base)


-- @@ L274-280 verbatim
/-- Construct an auxiliary covering vertex from a quotient vertex and a group element. -/
def coverVertexMk {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) (p : CoverSource G H) :
    CoverVertex G H :=
  ⟨a, rightCosetMk (MonoidHom.range
    (treeKuroshVertexInclusion G H a)) p⟩


-- @@ L282-287 verbatim
/-- Bundle a quotient edge with its source and target. -/
def coverBaseEdge {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H} (e : a ⟶ b) :
    CoverEdge G H :=
  ⟨a, b, e⟩


-- @@ L289-298 verbatim
/-- Lift a positively oriented quotient edge from a specified group representative. -/
noncomputable def coverPositiveLiftEdge {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H} (e : a ⟶ b)
    (p : CoverSource G H) :
    @Quiver.Hom (CoverVertex G H) (coverQuiver G H)
      (coverVertexMk G H a p)
      (coverVertexMk G H b
        (p * (coverEdgeLetter G H (coverBaseEdge G H e))⁻¹)) := by
  exact ⟨(p, coverBaseEdge G H e), rfl, rfl⟩


-- @@ L300-320 verbatim
/-- Lift a negatively oriented quotient edge from a specified group representative. -/
noncomputable def coverNegativeLiftEdge {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H} (e : a ⟶ b)
    (p : CoverSource G H) :
    @Quiver.Hom (Quiver.Symmetrify (CoverVertex G H)) _
      (coverVertexMk G H b p)
      (coverVertexMk G H a
        (p * coverEdgeLetter G H (coverBaseEdge G H e))) := by
  let q := p * coverEdgeLetter G H (coverBaseEdge G H e)
  let pos := coverPositiveLiftEdge G H e q
  have hsource :
      coverVertexMk G H b (q *
        (coverEdgeLetter G H (coverBaseEdge G H e))⁻¹) =
        coverVertexMk G H b p := by
    apply congrArg (Sigma.mk b)
    apply (rightCosetMk_eq_iff
      (MonoidHom.range (treeKuroshVertexInclusion G H b)) _ _).2
    refine ⟨1, ?_⟩
    simp [q, mul_assoc]
  exact Quiver.Hom.cast hsource rfl (Quiver.Hom.toNeg pos)


-- @@ L322-329 verbatim
/-- Label quotient edges in the opposite covering group to respect path composition. -/
def coverGraphLabelPrefunctor {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    RawBassSerreOrbitVertex G H ⥤q
      CategoryTheory.SingleObj (CoverSource G H)ᵐᵒᵖ where
  obj := fun _ => ()
  map := fun e => MulOpposite.op
    (coverEdgeLetter G H (coverBaseEdge G H e))⁻¹


-- @@ L331-350 verbatim
/-- Interpret a raw symmetrified quotient path in its free groupoid. -/
def coverFreeGroupoidPathHom {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a : RawBassSerreOrbitVertex G H} :
    ∀ {b : RawBassSerreOrbitVertex G H},
      @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
        (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H)) a b →
      @Quiver.Hom (Quiver.FreeGroupoid (RawBassSerreOrbitVertex G H)) _
        ((Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj a)
        ((Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).obj b)
  | _, Quiver.Path.nil => 𝟙 _
  | _, Quiver.Path.cons p e =>
      coverFreeGroupoidPathHom G H p ≫
        (match e with
        | Sum.inl f =>
            (Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).map f
        | Sum.inr f =>
            Groupoid.inv
              ((Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).map f))


-- @@ L352-374 verbatim
theorem coverFreeGroupoidPathHom_cons {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b c : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) a b)
    (e : @Quiver.Hom (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) b c) :
    coverFreeGroupoidPathHom G H (p.cons e) =
      coverFreeGroupoidPathHom G H p ≫
        (match e with
        | Sum.inl f =>
            (Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).map f
        | Sum.inr f =>
            Groupoid.inv
              ((Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).map f)) := by
  cases p with
  | nil =>
      cases e using Sum.casesOn <;> simp [coverFreeGroupoidPathHom]
  | cons p e' =>
      cases e using Sum.casesOn <;> cases e' using Sum.casesOn <;>
        simp [coverFreeGroupoidPathHom, Category.assoc]


-- @@ L376-385 verbatim
/-- Evaluate a quotient path in the opposite covering group. -/
noncomputable def coverPathValueOpp {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) a b) :
    (CoverSource G H)ᵐᵒᵖ :=
  (Quiver.FreeGroupoid.lift (coverGraphLabelPrefunctor G H)).map
    (coverFreeGroupoidPathHom G H p)


-- @@ L387-402 verbatim
/-- The covering-group value obtained by evaluating a quotient path. -/
noncomputable def coverPathValue {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H)) a b) :
  CoverSource G H :=
  match p with
  | Quiver.Path.nil => 1
  | Quiver.Path.cons p (Sum.inl e) =>
      coverPathValue G H p *
        (coverEdgeLetter G H (coverBaseEdge G H e))⁻¹
  | Quiver.Path.cons p (Sum.inr e) =>
      coverPathValue G H p *
        coverEdgeLetter G H (coverBaseEdge G H e)


-- @@ L404-411 verbatim
theorem coverPathValueOpp_nil {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a : RawBassSerreOrbitVertex G H} :
    coverPathValueOpp G H
        (Quiver.Path.nil : @Quiver.Path
          (Quiver.Symmetrify (RawBassSerreOrbitVertex G H)) _ a a) = 1 := by
  simp [coverPathValueOpp, coverFreeGroupoidPathHom,
    CategoryTheory.SingleObj.id_as_one]


-- @@ L413-428 verbatim
theorem coverPathValueOpp_pos {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H))
      (rawBassSerreOrbitRoot G H) a)
    (e : a ⟶ b) :
    coverPathValueOpp G H (p.cons (Quiver.Hom.toPos e)) =
      MulOpposite.op
          (coverEdgeLetter G H (coverBaseEdge G H e))⁻¹ *
        coverPathValueOpp G H p := by
  unfold coverPathValueOpp
  rw [coverFreeGroupoidPathHom_cons, Functor.map_comp,
    CategoryTheory.SingleObj.comp_as_mul]
  rfl


-- @@ L430-482 verbatim
theorem coverPathValueOpp_neg {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H))
      (rawBassSerreOrbitRoot G H) b)
    (e : a ⟶ b) :
    coverPathValueOpp G H (p.cons (Quiver.Hom.toNeg e)) =
      MulOpposite.op
          (coverEdgeLetter G H (coverBaseEdge G H e)) *
        coverPathValueOpp G H p := by
  unfold coverPathValueOpp
  rw [coverFreeGroupoidPathHom_cons, Functor.map_comp,
    CategoryTheory.SingleObj.comp_as_mul]
  dsimp
  rw [Groupoid.inv_eq_inv, Functor.map_inv]
  have hs := Prefunctor.congr_hom
    (Quiver.FreeGroupoid.lift_spec (coverGraphLabelPrefunctor G H)) e
  have hs' :
      (Quiver.FreeGroupoid.lift (coverGraphLabelPrefunctor G H)).map
          ((Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).map e) =
        MulOpposite.op
          (coverEdgeLetter G H (coverBaseEdge G H e))⁻¹ := by
    simpa [coverGraphLabelPrefunctor, Quiver.homOfEq] using
      congrArg (fun z => (z : (CoverSource G H)ᵐᵒᵖ)) hs
  change ((Quiver.FreeGroupoid.lift (coverGraphLabelPrefunctor G H)).map
      ((Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).map e) :
        (CoverSource G H)ᵐᵒᵖ) = _ at hs'
  let m : (CoverSource G H)ᵐᵒᵖ :=
    (Quiver.FreeGroupoid.lift (coverGraphLabelPrefunctor G H)).map
      ((Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).map e)
  have hm : m = MulOpposite.op
      (coverEdgeLetter G H (coverBaseEdge G H e))⁻¹ := by
    simpa [m] using hs'
  have hmi : m⁻¹ = MulOpposite.op
      (coverEdgeLetter G H (coverBaseEdge G H e)) := by
    rw [hm]
    simp
  have hmi' :
      Groupoid.inv
          ((Quiver.FreeGroupoid.lift (coverGraphLabelPrefunctor G H)).map
            ((Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).map e)) =
        MulOpposite.op (coverEdgeLetter G H (coverBaseEdge G H e)) := by
    simpa [m, Groupoid.inv_eq_inv,
      CategoryTheory.SingleObj.inv_as_inv] using hmi
  have hmi'' :
      inv
          ((Quiver.FreeGroupoid.lift (coverGraphLabelPrefunctor G H)).map
            ((Quiver.FreeGroupoid.of (RawBassSerreOrbitVertex G H)).map e)) =
        MulOpposite.op (coverEdgeLetter G H (coverBaseEdge G H e)) := by
    simpa only [Groupoid.inv_eq_inv] using hmi'
  rw [hmi'']


-- @@ L484-494 verbatim
theorem coverPathValue_nil {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a : RawBassSerreOrbitVertex G H} :
    coverPathValue G H
        (Quiver.Path.nil : @Quiver.Path
          (Quiver.Symmetrify (RawBassSerreOrbitVertex G H)) _ a a) = 1 := by
  change (coverPathValueOpp G H
    (Quiver.Path.nil : @Quiver.Path
      (Quiver.Symmetrify (RawBassSerreOrbitVertex G H)) _ a a)).unop = 1
  rw [coverPathValueOpp_nil]
  rfl


-- @@ L496-507 verbatim
theorem coverPathValue_pos {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H))
      (rawBassSerreOrbitRoot G H) a)
    (e : a ⟶ b) :
    coverPathValue G H (p.cons (Quiver.Hom.toPos e)) =
      coverPathValue G H p *
        (coverEdgeLetter G H (coverBaseEdge G H e))⁻¹ := by
  rfl


-- @@ L509-519 verbatim
theorem coverPathValue_neg {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a b : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H))
      (rawBassSerreOrbitRoot G H) b)
    (e : a ⟶ b) :
    coverPathValue G H (p.cons (Quiver.Hom.toNeg e)) =
      coverPathValue G H p * coverEdgeLetter G H (coverBaseEdge G H e) := by
  rfl


-- @@ L521-531 verbatim
/-- The free-part loop determined by a path based at the quotient root. -/
noncomputable def coverPathFreeLoop {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H))
      (rawBassSerreOrbitRoot G H) a) :
    KuroshFreePart G H :=
  coverFreeGroupoidPathHom G H p ≫
    Groupoid.inv (quotientTreePathHom G H a)


-- @@ L533-552 verbatim
theorem coverQuotientTreePathHom_root {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    quotientTreePathHom G H (rawBassSerreOrbitRoot G H) = 𝟙 _ := by
  rw [quotientTreePathHom_eq_rawTreePathAtRoot]
  let : Unique (@Quiver.Path (RawBassSerreOrbitVertex G H)
      (rawTreeQuiver G H) (rawBassSerreOrbitRoot G H)
      (rawBassSerreOrbitRoot G H)) := by
    exact @Quiver.Arborescence.uniquePath
      (RawBassSerreOrbitVertex G H) (rawTreeQuiver G H)
      (rawTreeQuiverArborescence G H) (rawBassSerreOrbitRoot G H)
  let : Quiver (RawBassSerreOrbitVertex G H) := rawTreeQuiver G H
  have hp : rawTreePathAtRoot G H (rawBassSerreOrbitRoot G H) =
      Quiver.Path.nil := by
    exact Subsingleton.elim _ _
  rw [hp]
  simp only [rawTreePathMap]
  exact @freeGroupoidPathHom_nil_public
    (RawBassSerreOrbitVertex G H)
    (rawBassSerreOrbitQuiver.inst G H)
    (rawBassSerreOrbitRoot G H)


-- @@ L554-624 verbatim
theorem coverPathValue_formula {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    {a : RawBassSerreOrbitVertex G H}
    (p : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H))
      (rawBassSerreOrbitRoot G H) a) :
      coverPathValue G H p =
      (treeKuroshFreeInclusion G H (coverPathFreeLoop G H p))⁻¹ := by
  refine @Quiver.Path.rec _
    (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
      (rawBassSerreOrbitQuiver.inst G H))
    (rawBassSerreOrbitRoot G H)
    (motive := fun a p =>
      coverPathValue G H p =
        (treeKuroshFreeInclusion G H (coverPathFreeLoop G H p))⁻¹)
    ?_ ?_ _ p
  · have h := (treeKuroshFreeInclusion G H).map_one
    simpa [coverPathValue, coverPathFreeLoop, coverFreeGroupoidPathHom,
      coverQuotientTreePathHom_root] using h
  · intro b c p e ih
    change RawBassSerreOrbitVertex G H at b c
    cases e using Sum.casesOn with
    | inl f =>
      have hloop :
          coverPathFreeLoop G H (p.cons (Sum.inl f)) =
            quotientEdgeLoop G H f * coverPathFreeLoop G H p := by
        unfold coverPathFreeLoop
        rw [coverFreeGroupoidPathHom_cons]
        rw [quotientEdgeLoop, CategoryTheory.End.mul_def]
        change
          (coverFreeGroupoidPathHom G H p ≫
              (Quiver.FreeGroupoid.of
                (RawBassSerreOrbitVertex G H)).map f) ≫
              Groupoid.inv (quotientTreePathHom G H c) =
            ((coverFreeGroupoidPathHom G H p ≫
              Groupoid.inv (quotientTreePathHom G H b)) ≫
              (quotientTreePathHom G H b ≫
                ((Quiver.FreeGroupoid.of
                  (RawBassSerreOrbitVertex G H)).map f ≫
                  Groupoid.inv (quotientTreePathHom G H c))))
        simp only [Groupoid.inv_eq_inv, Category.assoc,
          IsIso.inv_hom_id_assoc]
      dsimp [coverPathValue]
      rw [hloop, map_mul, mul_inv_rev, ih]
      rfl
    | inr f =>
      have hloop :
          coverPathFreeLoop G H (p.cons (Sum.inr f)) =
            (quotientEdgeLoop G H f)⁻¹ * coverPathFreeLoop G H p := by
        unfold coverPathFreeLoop
        rw [coverFreeGroupoidPathHom_cons]
        rw [quotientEdgeLoop, CategoryTheory.End.mul_def]
        change
          (coverFreeGroupoidPathHom G H p ≫
              Groupoid.inv
                ((Quiver.FreeGroupoid.of
                  (RawBassSerreOrbitVertex G H)).map f)) ≫
              Groupoid.inv (quotientTreePathHom G H c) =
            ((coverFreeGroupoidPathHom G H p ≫
              Groupoid.inv (quotientTreePathHom G H b)) ≫
              Groupoid.inv
                (quotientTreePathHom G H c ≫
                  (Quiver.FreeGroupoid.of
                    (RawBassSerreOrbitVertex G H)).map f ≫
                  Groupoid.inv (quotientTreePathHom G H b)))
        simp only [Groupoid.inv_eq_inv, IsIso.inv_comp, IsIso.inv_inv,
          IsIso.inv_hom_id_assoc, Category.assoc]
      dsimp [coverPathValue]
      rw [hloop, map_mul, map_inv, mul_inv_rev, ih]
      simp [coverEdgeLetter, coverBaseEdge]


-- @@ L626-651 verbatim
/-- Lift a quotient path starting from the coset of a given covering-group element. -/
noncomputable def coverPathLift {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (p : CoverSource G H) :
    ∀ {a : RawBassSerreOrbitVertex G H},
      @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
        (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
          (rawBassSerreOrbitQuiver.inst G H))
        (rawBassSerreOrbitRoot G H) a →
      Σ q : CoverSource G H,
        @Quiver.Path (Quiver.Symmetrify (CoverVertex G H)) _
          (coverVertexMk G H (rawBassSerreOrbitRoot G H) p)
          (coverVertexMk G H a q)
  | _, Quiver.Path.nil => ⟨p, Quiver.Path.nil⟩
  | _, @Quiver.Path.cons _ _ _ b c q e => by
      let ih := coverPathLift G H p q
      let r : CoverSource G H := ih.1
      cases e using Sum.casesOn with
      | inl f =>
          exact ⟨r * (coverEdgeLetter G H (coverBaseEdge G H f))⁻¹,
            Quiver.Path.cons ih.2
              (Quiver.Hom.toPos (coverPositiveLiftEdge G H f r))⟩
      | inr f =>
          exact ⟨r * coverEdgeLetter G H (coverBaseEdge G H f),
            Quiver.Path.cons ih.2
              (coverNegativeLiftEdge G H f r)⟩


-- @@ L653-684 verbatim
theorem coverPathLift_value {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (p : CoverSource G H)
    {a : RawBassSerreOrbitVertex G H}
    (q : @Quiver.Path (Quiver.Symmetrify (RawBassSerreOrbitVertex G H))
      (@Quiver.symmetrifyQuiver (RawBassSerreOrbitVertex G H)
        (rawBassSerreOrbitQuiver.inst G H))
      (rawBassSerreOrbitRoot G H) a) :
    (coverPathLift G H p q).1 = p * coverPathValue G H q := by
  induction q with
  | nil =>
      dsimp [coverPathLift]
      change p = p * 1
      simp
  | @cons b c q e ih =>
      cases e using Sum.casesOn with
      | inl f =>
          dsimp [coverPathLift]
          rw [ih]
          change p * coverPathValue G H q *
              (coverEdgeLetter G H (coverBaseEdge G H f))⁻¹ =
            p * (coverPathValue G H q *
              (coverEdgeLetter G H (coverBaseEdge G H f))⁻¹)
          rw [mul_assoc]
      | inr f =>
          dsimp [coverPathLift]
          rw [ih]
          change p * coverPathValue G H q *
              coverEdgeLetter G H (coverBaseEdge G H f) =
            p * (coverPathValue G H q *
              coverEdgeLetter G H (coverBaseEdge G H f))
          rw [mul_assoc]


-- @@ L686-691 verbatim
/-- The projection from the auxiliary covering quiver to the Bass-Serre quiver. -/
noncomputable def coverPrefunctor {ι : Type v} (G : ι → Type u)
    [∀ i, Group (G i)] (H : Subgroup (FreeProduct G)) :
    CoverVertex G H ⥤q RawBassSerreVertex G where
  obj := coverVertexMap G H
  map := coverEdgeMap G H


-- @@ L693-710 verbatim
theorem treeKuroshVertexInclusion_injective {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (a : RawBassSerreOrbitVertex G H) :
    Function.Injective (treeKuroshVertexInclusion G H a) := by
  intro x y h
  have hu :
      (ULift.up x : TreeKuroshComponent G H
        (Sum.inl a : TreeKuroshComponentIndex G H)) = ULift.up y := by
    change (Monoid.CoprodI.of :
      TreeKuroshComponent G H (Sum.inl a : TreeKuroshComponentIndex G H) →*
        TreeKuroshProduct G H) (ULift.up x) =
      (Monoid.CoprodI.of :
        TreeKuroshComponent G H (Sum.inl a : TreeKuroshComponentIndex G H) →*
          TreeKuroshProduct G H) (ULift.up y) at h
    exact (Monoid.CoprodI.of_injective
      (M := TreeKuroshComponent G H)
      (Sum.inl a : TreeKuroshComponentIndex G H)) h
  exact ULift.up_injective hu


-- @@ L712-712 verbatim
end GraphCoveringTheory.Kurosh
