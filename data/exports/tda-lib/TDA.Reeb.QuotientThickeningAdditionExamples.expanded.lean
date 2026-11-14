import TDA.Reeb.QuotientThickeningAddition
import TDA.Reeb.GeometricThickeningAdditionExamples
import TDA.Reeb.RGraphSmoothingExamples
import TDA.Reeb.RGraphCosheafEquivalenceExamples


-- @@ L6-24 verbatim
/-!
# Fixtures for the Reeb quotient of the thickening addition map

Acceptance fixtures for `TDA.Reeb.QuotientThickeningAddition`, on the thickening, the Reeb quotient and the realizations of finite data:

* **One point.** `ℛ T_1 T_1 P ≅ ℛ T_(1+1) P` holds, next to the merged `T_1 T_1 P ≇ T_(1+1) P`.
  The height-`0` segment `s ↦ ((*, s), -s)` collapses to one class, proved along the segment and by
  injectivity of the homeomorphism, and the height-`0` fibre of `ℛ T_1 T_1 P` is a subsingleton.
* **Boundary control.** At `ε = 0` on the point, the left unit law sends `[(*, s), 0]` to
  `[(*, s)]`, and the section keeps the band coordinate `u` in the inner factor and `0` in the
  outer one.
* **One edge.** At `ε = δ = 1/4`, `[(q, 1/4), 1/4] ↦ [(q, 1/2)]`, the inverse returns
  `[(q, 1/4), 1/4]` (the clamp of `1/2` is `1/4`), `[(q, 1/4), -1/4] = [(q, 0), 0]`, and
  associativity at `[((q, 1/4), 1/4), 1/4]` gives band coordinate `3/4` on both sides.
* **Two merging edges.** At `1/4 + 1/4` the classes of the two edge points at height `1/2` are
  equal, although the points differ; at `1/8 + 1/8` the height-`1/2` fibre is not a subsingleton.
* **Naturality and packaging.** The edge-swap square of `geometricSmoothingAddIso` and the graph
  object `ℛ T_(1/4) T_(1/4)` of the parallel edges.
-/


-- @@ L26-26 verbatim
open Set Topology CategoryTheory

-- @@ L27-27 verbatim
open scoped NNReal


-- @@ L29-29 verbatim
namespace TDA.Reeb


-- @@ L31-31 verbatim
noncomputable section


-- @@ L33-33 verbatim
namespace Examples.QuotientThickeningAddition


-- @@ L35-35 verbatim
open OpenInterval TDA.Reeb.GeometricThickening RGraph

-- @@ L36-36 verbatim
open TDA.Reeb.Examples.Cylinder (S01 parallelData)

-- @@ L37-37 verbatim
open TDA.Reeb.RGraph.Examples (swap)

-- @@ L38-40 verbatim
open TDA.Reeb.Examples.GeometricThickeningAddition (one₁ zero₁ quarter coe_quarter quarterPt
  negQuarterPt edgeObj edgePt edgeZ parObj parPt parZ parW height_parZ parPt_false_ne_true
  swap_addNatTrans_square_apply)

-- @@ L41-41 verbatim
open TDA.Reeb.Examples.RGraphCosheafEquivalence (parallelGraph swapGraph)

-- @@ L42-43 verbatim
open TDA.Reeb.Examples.RGraphSmoothing (parallel_smoothed_fiber_subsingleton
  parallel_quarter_fiber_not_subsingleton)


-- @@ L45-45 verbatim
local notation "ℛ" => ReebQuotient.quotientFunctor ℝ


-- @@ L47-47 verbatim
/-! ### One point -/


-- @@ L49-55 verbatim
/-- **The contrast.** After the Reeb quotient, `T_1 T_1 P` and `T_(1+1) P` are isomorphic over `ℝ`;
before it they are not. -/
theorem point_reeb_iso_not_iso :
    Nonempty ((ℛ).obj ((functor 1).obj ((functor 1).obj onePoint)) ≅
        (ℛ).obj ((functor (1 + 1)).obj onePoint)) ∧
      IsEmpty ((functor 1).obj ((functor 1).obj onePoint) ≅ (functor (1 + 1)).obj onePoint) :=
  ⟨⟨(reebAddIso 1 1).app onePoint⟩, not_iso_one_one⟩


-- @@ L57-65 verbatim
/-- The segment `r ↦ ((*, r), -r)`, `r ∈ [0, 1]`, from `((*, 0), 0)` to `((*, 1), -1)`. -/
def pointSegmentPath : Path (fiberSegment zero₁) (fiberSegment one₁) where
  toFun r := fiberSegment ⟨r, ⟨by rw [NNReal.coe_one]; linarith [r.2.1],
    by rw [NNReal.coe_one]; exact r.2.2⟩⟩
  continuous_toFun := (continuous_const.prodMk (continuous_subtype_val.subtype_mk _)).prodMk
    (continuous_subtype_val.neg.subtype_mk _)
  source' := Prod.ext (Prod.ext rfl (Subtype.ext rfl)) (Subtype.ext (by simp [fiberSegment, zero₁]))
  target' := Prod.ext (Prod.ext rfl (Subtype.ext (by simp [fiberSegment, one₁])))
    (Subtype.ext (by simp [fiberSegment, one₁]))


-- @@ L67-72 verbatim
/-- **The segment collapses**, directly along the segment, which stays at height `0`. -/
theorem point_segment_collapse :
    ReebQuotient.mk (height (height (overBaseMap onePoint) 1) 1) (fiberSegment zero₁) =
      ReebQuotient.mk (height (height (overBaseMap onePoint) 1) 1) (fiberSegment one₁) :=
  ReebQuotient.mk_eq_mk_of_path _ pointSegmentPath fun _ =>
    (fiber_zero_injective.2 _).trans (fiber_zero_injective.2 zero₁).symm


-- @@ L74-82 verbatim
/-- Every point of the segment has image `[(*, 0)]` under the homeomorphism. -/
theorem point_segment_image (s : Band 1) :
    quotientAddHomeomorph (overBaseMap onePoint) 1 1
        (ReebQuotient.mk (height (height (overBaseMap onePoint) 1) 1) (fiberSegment s)) =
      ReebQuotient.mk (height (overBaseMap onePoint) (1 + 1))
        (PUnit.unit, ⟨0, zero_mem_band (1 + 1)⟩) := by
  exact (quotientAddHomeomorph_mk _ 1 1 (fiberSegment s)).trans
    (congrArg (ReebQuotient.mk (height (overBaseMap onePoint) (1 + 1)))
      (Prod.ext rfl (Subtype.ext (show (s : ℝ) + -s = 0 by ring))))


-- @@ L84-89 verbatim
/-- **The segment collapses**, by injectivity of the homeomorphism from equal images. -/
theorem point_segment_collapse' :
    ReebQuotient.mk (height (height (overBaseMap onePoint) 1) 1) (fiberSegment zero₁) =
      ReebQuotient.mk (height (height (overBaseMap onePoint) 1) 1) (fiberSegment one₁) :=
  (quotientAddHomeomorph (overBaseMap onePoint) 1 1).injective
    ((point_segment_image zero₁).trans (point_segment_image one₁).symm)


-- @@ L91-114 verbatim
/-- **The height-`0` fibre of `ℛ T_1 T_1 P` is a subsingleton**, transported from the height-`0`
fibre of `T_(1+1) P` through the height-preserving homeomorphism. -/
theorem point_quotient_fiber_zero_subsingleton :
    Subsingleton {q : ReebQuotient (height (height (overBaseMap onePoint) 1) 1) //
      ReebQuotient.height _ q = 0} := by
  have hinj : Function.Injective (height (overBaseMap onePoint) (1 + 1)) := by
    rintro ⟨a, s⟩ ⟨b, t⟩ h
    have h' : (0 : ℝ) + s = 0 + t := h
    exact Prod.ext (Subsingleton.elim (α := PUnit.{1}) _ _) (Subtype.ext (by linarith))
  let e := (quotientAddHomeomorph (overBaseMap onePoint) 1 1).trans
    (ReebQuotient.homeomorphOfInjective hinj)
  have hh : ∀ p : ReebQuotient (height (overBaseMap onePoint) (1 + 1)),
      overBaseMap ((functor (1 + 1)).obj onePoint) (ReebQuotient.homeomorphOfInjective hinj p) =
        ReebQuotient.height _ p := by
    intro p
    induction p using ReebQuotient.ind with
    | h w => rfl
  have he : ∀ q, overBaseMap ((functor (1 + 1)).obj onePoint) (e q) = ReebQuotient.height _ q :=
    fun q => (hh _).trans (height_quotientAddHomeomorph _ 1 1 q)
  constructor
  rintro ⟨q₁, h₁⟩ ⟨q₂, h₂⟩
  have h := (fiber_zero_subsingleton (1 + 1)).elim ⟨e q₁, (he q₁).trans h₁⟩
    ⟨e q₂, (he q₂).trans h₂⟩
  exact Subtype.ext (e.injective (congrArg Subtype.val h))


-- @@ L116-116 verbatim
/-! ### Boundary control: `ε = 0` -/


-- @@ L118-127 verbatim
/-- **Left unit law at a representative.** On the point, `ℛ μ_(0,1)` followed by `ℛ` of the band
inclusion `0 + 1 ≤ 1` sends `[(*, s), 0]` to `[(*, s)]`. -/
theorem point_zero_left_apply (s : Band 1) :
    ((reebAddIso 0 1 ≪≫ Functor.isoWhiskerRight (bandEqIso (zero_add 1)) ℛ).hom.app
        onePoint).left.hom
        (ReebQuotient.mk (height (height (overBaseMap onePoint) 1) 0)
          ((PUnit.unit, s), ⟨0, zero_mem_band 0⟩)) =
      ReebQuotient.mk (height (overBaseMap onePoint) 1) (PUnit.unit, s) := by
  rw [reebAddIso_zero_left]
  rfl


-- @@ L129-136 verbatim
/-- At `ε = 0`, the section keeps the band coordinate `u` in the inner factor and returns `0` in
the outer factor: the clamp of `u ∈ [-1, 1]` onto `[-1, 1]` is `u`. -/
theorem point_addSection_zero (w : PUnit.{1} × Band (0 + 1)) :
    ((addSection PUnit.{1} 0 1 w).1.2 : ℝ) = w.2 ∧ ((addSection PUnit.{1} 0 1 w).2 : ℝ) = 0 := by
  have h01 : (((0 + 1 : ℝ≥0)) : ℝ) = ((1 : ℝ≥0) : ℝ) := by rw [zero_add]
  have hw : (w.2 : ℝ) ∈ Band 1 := ⟨by linarith [w.2.2.1], by linarith [w.2.2.2]⟩
  exact ⟨congrArg Subtype.val (projIcc_of_mem (neg_le_band 1) hw),
    eq_zero_of_mem_band_zero (addSection PUnit.{1} 0 1 w).2.2⟩


-- @@ L138-138 verbatim
/-! ### One edge -/


-- @@ L140-142 verbatim
/-- The band point `1/2 ∈ [-(1/4 + 1/4), 1/4 + 1/4]`. -/
def halfPt : Band (quarter + quarter) :=
  ⟨1 / 2, by rw [Band, NNReal.coe_add, coe_quarter]; norm_num⟩


-- @@ L144-145 verbatim
/-- The band point `0 ∈ [-1/4, 1/4]`. -/
def zeroQ : Band quarter := ⟨0, zero_mem_band quarter⟩


-- @@ L147-153 verbatim
/-- `[(q, 1/4), 1/4] ↦ [(q, 1/2)]`. -/
theorem edge_quotientAddHomeomorph :
    quotientAddHomeomorph (overBaseMap edgeObj) quarter quarter (ReebQuotient.mk _ edgeZ) =
      ReebQuotient.mk _ (edgePt, halfPt) := by
  rw [quotientAddHomeomorph_mk]
  exact congrArg (ReebQuotient.mk _) (Prod.ext rfl (Subtype.ext
    (show (quarter : ℝ) + quarter = 1 / 2 by rw [coe_quarter]; norm_num)))


-- @@ L155-169 verbatim
/-- The inverse returns `[(q, 1/4), 1/4]`: the clamp of `1/2` onto `[-1/4, 1/4]` is `1/4`. -/
theorem edge_quotientAddHomeomorph_symm :
    (quotientAddHomeomorph (overBaseMap edgeObj) quarter quarter).symm
        (ReebQuotient.mk _ (edgePt, halfPt)) =
      ReebQuotient.mk _ ((edgePt, quarterPt), quarterPt) := by
  rw [quotientAddHomeomorph_symm_mk]
  have hc : (projIcc (-(quarter : ℝ)) quarter (neg_le_band quarter) (1 / 2) : ℝ) = 1 / 4 := by
    rw [coe_projIcc, coe_quarter, min_eq_left (by norm_num), max_eq_right (by norm_num)]
  refine congrArg (ReebQuotient.mk _) (Prod.ext (Prod.ext rfl (Subtype.ext ?_)) (Subtype.ext ?_))
  · show (projIcc (-(quarter : ℝ)) quarter (neg_le_band quarter) (1 / 2) : ℝ) = quarter
    rw [hc, coe_quarter]
  · show (1 / 2 : ℝ) - (projIcc (-(quarter : ℝ)) quarter (neg_le_band quarter) (1 / 2) : ℝ) =
      quarter
    rw [hc, coe_quarter]
    norm_num


-- @@ L171-191 verbatim
/-- **A non-trivial identification**: `[(q, 1/4), -1/4] = [(q, 0), 0]`, along the fibre path. -/
theorem edge_reebRel_identification :
    ReebQuotient.mk (height (height (overBaseMap edgeObj) quarter) quarter)
        ((edgePt, quarterPt), negQuarterPt) =
      ReebQuotient.mk (height (height (overBaseMap edgeObj) quarter) quarter)
        ((edgePt, zeroQ), zeroQ) := by
  have hc : (projIcc (-(quarter : ℝ)) quarter (neg_le_band quarter)
      ((quarter : ℝ) + -(quarter : ℝ)) : ℝ) = 0 := by
    rw [add_neg_cancel, coe_projIcc, min_eq_right quarter.coe_nonneg,
      max_eq_right (neg_nonpos.2 quarter.coe_nonneg)]
  have hσ : addSection edgeObj.left quarter quarter
      (addMap edgeObj.left quarter quarter ((edgePt, quarterPt), negQuarterPt)) =
        ((edgePt, zeroQ), zeroQ) := by
    refine Prod.ext (Prod.ext rfl (Subtype.ext ?_)) (Subtype.ext ?_)
    · exact hc
    · show (quarter : ℝ) + -(quarter : ℝ) -
          (projIcc (-(quarter : ℝ)) quarter (neg_le_band quarter)
            ((quarter : ℝ) + -(quarter : ℝ)) : ℝ) = 0
      rw [hc, add_neg_cancel, sub_zero]
  rw [← hσ]
  exact (ReebQuotient.mk_eq_mk_iff _).2 (reebRel_addSection_addMap _ _)


-- @@ L193-195 verbatim
/-- The band point `3/4 ∈ [-(1/4 + (1/4 + 1/4)), 1/4 + (1/4 + 1/4)]`. -/
def threeQuarterPt : Band (quarter + (quarter + quarter)) :=
  ⟨3 / 4, by rw [Band, NNReal.coe_add, NNReal.coe_add, coe_quarter]; norm_num⟩


-- @@ L197-225 verbatim
/-- **Associativity at a representative.** At `[((q, 1/4), 1/4), 1/4]` both sides of
`reebAddIso_assoc` give the class of `(q, 3/4)`. -/
theorem edge_reebAddIso_assoc :
    ((Functor.whiskerLeft (functor quarter) (reebAddIso quarter quarter).hom ≫
        (reebAddIso (quarter + quarter) quarter).hom ≫
          Functor.whiskerRight (bandEqIso (add_assoc quarter quarter quarter)).hom ℛ).app
          edgeObj).left.hom
        (ReebQuotient.mk (height (height (height (overBaseMap edgeObj) quarter) quarter) quarter)
          (((edgePt, quarterPt), quarterPt), quarterPt)) =
        ReebQuotient.mk (height (overBaseMap edgeObj) (quarter + (quarter + quarter)))
          (edgePt, threeQuarterPt) ∧
      ((Functor.whiskerRight (Functor.whiskerRight (addNatTrans quarter quarter) (functor quarter))
          ℛ ≫ (reebAddIso quarter (quarter + quarter)).hom).app edgeObj).left.hom
        (ReebQuotient.mk (height (height (height (overBaseMap edgeObj) quarter) quarter) quarter)
          (((edgePt, quarterPt), quarterPt), quarterPt)) =
        ReebQuotient.mk (height (overBaseMap edgeObj) (quarter + (quarter + quarter)))
          (edgePt, threeQuarterPt) := by
  have hR : ((Functor.whiskerRight (Functor.whiskerRight (addNatTrans quarter quarter)
      (functor quarter)) ℛ ≫ (reebAddIso quarter (quarter + quarter)).hom).app edgeObj).left.hom
        (ReebQuotient.mk (height (height (height (overBaseMap edgeObj) quarter) quarter) quarter)
          (((edgePt, quarterPt), quarterPt), quarterPt)) =
        ReebQuotient.mk (height (overBaseMap edgeObj) (quarter + (quarter + quarter)))
          (edgePt, threeQuarterPt) :=
    congrArg (ReebQuotient.mk _) (Prod.ext rfl (Subtype.ext
      (show (quarter : ℝ) + quarter + quarter = 3 / 4 by rw [coe_quarter]; norm_num)))
  exact ⟨(congrArg (fun φ => φ.left.hom
    (ReebQuotient.mk (height (height (height (overBaseMap edgeObj) quarter) quarter) quarter)
      (((edgePt, quarterPt), quarterPt), quarterPt)))
    (NatTrans.congr_app (reebAddIso_assoc quarter quarter quarter) edgeObj)).trans hR, hR⟩


-- @@ L227-227 verbatim
/-! ### Two merging edges -/


-- @@ L229-248 verbatim
/-- **The loop dies at `1/4 + 1/4`.** The classes of the two distinct edge points at height `1/2`
are equal in `ℛ T_(1/4) T_(1/4)`: their images lie in the height-`1/2` fibre of
`U_(1/4 + 1/4)` of the parallel edges, which is a subsingleton, and the homeomorphism is
injective. -/
theorem par_quarter_classes_eq :
    parZ false ≠ parZ true ∧
      ReebQuotient.mk (height (height (overBaseMap parObj) quarter) quarter) (parZ false) =
        ReebQuotient.mk (height (height (overBaseMap parObj) quarter) quarter) (parZ true) := by
  refine ⟨fun h => parPt_false_ne_true (congrArg (fun z => z.1.1) h), ?_⟩
  have hε : 1 / 2 ≤ ((quarter + quarter : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_add, coe_quarter]
    norm_num
  have hsub := parallel_smoothed_fiber_subsingleton hε (1 / 2)
  have hb : ∀ b, overBaseMap ((geometricSmoothing (quarter + quarter)).obj parallelGraph).obj
      (ReebQuotient.mk (height (overBaseMap parObj) (quarter + quarter)) (parPt b, parW)) =
        1 / 2 :=
    fun b => (height_addMap _ quarter quarter (parZ b)).trans (height_parZ b)
  have himg := congrArg Subtype.val (hsub.elim ⟨_, hb false⟩ ⟨_, hb true⟩)
  exact (quotientAddHomeomorph (overBaseMap parObj) quarter quarter).injective
    (a₁ := ReebQuotient.mk _ (parZ false)) (a₂ := ReebQuotient.mk _ (parZ true)) himg


-- @@ L250-251 verbatim
/-- The parameter `1/8`. -/
def eighth : ℝ≥0 := ⟨1 / 8, by norm_num⟩


-- @@ L253-257 verbatim
theorem eighth_add_eighth : eighth + eighth = Examples.ConstructibleSmoothing.quarter :=
  NNReal.eq (by
    rw [NNReal.coe_add]
    show (1 / 8 : ℝ) + 1 / 8 = 1 / 4
    norm_num)


-- @@ L259-278 verbatim
/-- **The loop survives at `1/8 + 1/8`.** The height-`1/2` fibre of `ℛ T_(1/8) T_(1/8)` of the
parallel edges is not a subsingleton, transported through the height-preserving homeomorphism from
the merged statement for `U_(1/4)`. -/
theorem par_eighth_fiber_not_subsingleton :
    ¬ Subsingleton (overBaseMap ((ℛ).obj ((functor eighth).obj ((functor eighth).obj parObj))) ⁻¹'
      {1 / 2}) := by
  intro h
  apply parallel_quarter_fiber_not_subsingleton
  rw [← eighth_add_eighth]
  let e := quotientAddHomeomorph (overBaseMap parObj) eighth eighth
  have k : ∀ p : ReebQuotient (height (overBaseMap parObj) (eighth + eighth)),
      ReebQuotient.height _ p = 1 / 2 → ReebQuotient.height _ (e.symm p) = 1 / 2 := by
    intro p hp
    have := height_quotientAddHomeomorph (overBaseMap parObj) eighth eighth (e.symm p)
    rw [Homeomorph.apply_symm_apply] at this
    exact this.symm.trans hp
  constructor
  rintro ⟨p₁, h₁⟩ ⟨p₂, h₂⟩
  exact Subtype.ext (e.symm.injective (congrArg Subtype.val
    (h.elim ⟨e.symm p₁, k p₁ h₁⟩ ⟨e.symm p₂, k p₂ h₂⟩)))


-- @@ L280-280 verbatim
/-! ### Naturality on the edge swap -/


-- @@ L282-288 verbatim
/-- The slice naturality square of `reebAddIso` for the swap. -/
theorem swap_reebAddIso_square :
    ((functor quarter ⋙ functor quarter) ⋙ ℛ).map swapGraph.hom ≫
        (reebAddIso quarter quarter).hom.app parObj =
      (reebAddIso quarter quarter).hom.app parObj ≫
        (functor (quarter + quarter) ⋙ ℛ).map swapGraph.hom :=
  (reebAddIso quarter quarter).hom.naturality swapGraph.hom


-- @@ L290-309 verbatim
/-- **The swap square of `geometricSmoothingAddIso`** at the class of the point over edge `true`:
both composites give the class of the point over edge `false`, which differs from the image under
the identity. -/
theorem swap_geometricSmoothingAddIso_square_apply :
    ((doubleThickeningQuotient quarter quarter).map swapGraph ≫
        (geometricSmoothingAddIso quarter quarter).hom.app parallelGraph).hom.left.hom
        (ReebQuotient.mk (height (height (overBaseMap parObj) quarter) quarter) (parZ true)) =
        ReebQuotient.mk (height (overBaseMap parObj) (quarter + quarter)) (parPt false, parW) ∧
      ((geometricSmoothingAddIso quarter quarter).hom.app parallelGraph ≫
        (geometricSmoothing (quarter + quarter)).map swapGraph).hom.left.hom
        (ReebQuotient.mk (height (height (overBaseMap parObj) quarter) quarter) (parZ true)) =
        ReebQuotient.mk (height (overBaseMap parObj) (quarter + quarter)) (parPt false, parW) := by
  have h₁ : ((doubleThickeningQuotient quarter quarter).map swapGraph ≫
      (geometricSmoothingAddIso quarter quarter).hom.app parallelGraph).hom.left.hom
        (ReebQuotient.mk (height (height (overBaseMap parObj) quarter) quarter) (parZ true)) =
        ReebQuotient.mk (height (overBaseMap parObj) (quarter + quarter)) (parPt false, parW) :=
    congrArg (ReebQuotient.mk _) swap_addNatTrans_square_apply.1
  exact ⟨h₁, (congrArg (fun φ => φ.hom.left.hom
    (ReebQuotient.mk (height (height (overBaseMap parObj) quarter) quarter) (parZ true)))
    ((geometricSmoothingAddIso quarter quarter).hom.naturality swapGraph)).symm.trans h₁⟩


-- @@ L311-311 verbatim
/-! ### Graph packaging -/


-- @@ L313-316 verbatim
/-- `ℛ T_(1/4) T_(1/4)` of the parallel edges is a graph object. -/
theorem par_isRGraph :
    IsRGraph ((ℛ).obj ((functor quarter).obj ((functor quarter).obj parObj))) :=
  isRGraph_quotient_thickening_thickening parallelGraph.property quarter quarter


-- @@ L318-323 verbatim
/-- The explicit isomorphism `ℛ T_(1/4) T_(1/4) ≅ U_(1/4 + 1/4)` of the parallel edges in
`RGraphCat`. -/
def parAddIso :
    (doubleThickeningQuotient quarter quarter).obj parallelGraph ≅
      (geometricSmoothing (quarter + quarter)).obj parallelGraph :=
  (geometricSmoothingAddIso quarter quarter).app parallelGraph


-- @@ L325-325 verbatim
end Examples.QuotientThickeningAddition


-- @@ L327-327 verbatim
end


-- @@ L329-329 verbatim
end TDA.Reeb
