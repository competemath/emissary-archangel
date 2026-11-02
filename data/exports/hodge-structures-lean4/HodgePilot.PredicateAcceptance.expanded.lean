import HodgePilot.HodgeFlagProper
import HodgePilot.ProjectiveLineGraded
import HodgePilot.ProjectiveLineSmooth


-- @@ L5-96 verbatim
/-! # The projective line: the Betti-side edge class and the acceptance
# shape of the Hodge-class predicate (golden-path G4 rung)

Golden-path acceptance module.  For the projective line
`p1 = Proj ℂ[X₀, X₁]` of `HodgePilot.ProjectiveLine`, whose structure
morphism carries the binder-free instance pair
`SmoothOfRelativeDimension 1` / `IsProper`
(`HodgePilot.ProjectiveLineSmooth`), this module:

**Leg 1 (the Betti-side class).**  Constructs a degree-2 class
`bettiEdgeClass : H²(SPoints structMor, ℚ)` on the analytic point-space of
the projective line, in the constant-sheaf carrier of `HodgePilot.Betti`
(the exact Betti slot of the proper-scope predicate), by the same
Mayer–Vietoris edge construction as `HodgePilot.ProjectiveLineGraded`, run
on the **analytic space site**: the two chart-image opens `V0, V1` cover
the space; their overlap is covered by two slit opens `W0, W1` whose
double overlap `W0 ⊓ W1` splits into two disjoint opens `AUp ⊔ BLo`
(classically the upper and lower half-planes of the overlap coordinate); a
section of the constant sheaf which is `1` on `AUp` and `0` on `BLo` is
glued by the pin's Mayer–Vietoris sheaf condition, and the class is the
image of that section under two connecting maps `δ` of Riou's
Mayer–Vietoris sequence, re-anchored at `⊤` and carried into Mathlib's
`Sheaf.H` along the terminal-anchor identification of
`HodgePilot.ProjectiveLineGraded` Part 1 (generic; instantiated, not
rebuilt).  **`bettiEdgeClass` is NOT claimed to be nonzero**: its
nonvanishing is recorded as the named unproved `Prop`
`BettiEdgeNonvanishing` (the analytic flavor of the chart-interference
wall; registry style — stated, never proved, never assumed, never used).

**Leg 2 (the acceptance shape).**  States the predicate-acceptance target
`IsHodgeClassProper structMor 1 1 bettiEdgeClass` and proves it **up to
two named receipts**, both stated as named unproved `Prop`s and consumed
only as the explicit hypotheses of the conditional theorem
`isHodgeClassProper_bettiEdge_of_receipts`:

* `DinfSpaceFiltration` — the space-side presentation
  `dinfCycleClassSpace` of wave 1's divisor-level cycle class
  `dinfCycleClass` (transported along the proven P3 site agreement
  `DeRhamSpaceAgree.hyperHdRSpaceEquiv`) lies in the space-side naive
  filtration `dRSpaceFiltrationC` cut at `1` — the filtration-transport
  receipt (the site-level membership `dinfCycleClass_mem` is by
  construction; its transport along the P3 equivalence is not proved
  here);
* `DinfJunctionEvaluation` — the junction at the constructed forms input
  (`HodgeFlagProper.formsInputProper`) sends `dinfCycleClassSpace` to the
  certified-equivalence image of the ℚ→ℂ image of `bettiEdgeClass` — the
  **junction-evaluation receipt**, the exact P2-instance computation this
  module does not perform.  The repo ships naturality for every map in
  the junction composite but no section-level evaluation receipts
  (`HodgePilot.HodgeFlagAffine` §12, `HodgePilot.HodgeFlagProper` §§1–3);
  the same blocking spelling was documented at degree 0 by the golden-path
  auxiliary wave (three nested adjunction transposes — sheafification,
  dense subsite, pull–push — plus a chart-realization evaluation lemma).

Given the two receipts, acceptance is immediate
(`AddSubgroup.mem_map`): the conditional theorem is the acceptance SHAPE
with every remaining ingredient proved.

## What is and is not proved (entitlement, in full)

PROVED: the Betti-side class `bettiEdgeClass` is constructed in the
predicate's exact carrier `bettiQ (TopCat.of (SPoints structMor)) 2`, with
restriction receipts pinning its input section to the glued `1`/`0` datum;
the smooth-proper binder pair of the predicate synthesizes on `p1` with no
hypothesized binder; and `IsHodgeClassProper structMor 1 1 bettiEdgeClass`
follows from the two named receipts above.  NOT PROVED, NOT CLAIMED:
nonvanishing of `bettiEdgeClass` (named gap `BettiEdgeNonvanishing`);
either named receipt; any unconditional acceptance of a (possibly zero)
class beyond `HodgePilot.CalibrationZero`'s zero class; any comparison
between the constant-sheaf carrier and singular cohomology (*Betti* is, as
everywhere in this project, a gloss for sheaf cohomology of a constant
sheaf); any claim that any junction map is an isomorphism or
quasi-isomorphism (that is exactly P2 of `HodgePilot.HodgePredicate`).
The honest sentence for this module: *the Hodge-class predicate's
acceptance of the constructed Betti edge class on the projective line is
proved up to two named receipts (filtration transport and junction
evaluation at wave 1's cycle class), each stated verbatim as a `Prop`.*
Nothing here makes the Hodge conjecture statable.

## Credits

The Mayer–Vietoris square, its sheaf condition, its long-exact-sequence
`δ`, `Sheaf.H`/`Sheaf.H'` and the `Ext` infrastructure are Joël Riou's;
`Proj`, its charts and `awayι` are Andrew Yang's and Jujian Zhang's; the
analytic gluing layer is `HodgePilot.AnalyticGlue`; the degree-0-sections
and terminal-anchor layer is `HodgePilot.ProjectiveLineGraded` Part 1; the
predicate tower is `HodgePilot.HodgePredicate` /
`HodgePilot.HodgeFlagAffine` / `HodgePilot.HodgeFlagCertified` /
`HodgePilot.HodgeFlagProper`; the P3 site agreement is
`HodgePilot.DeRhamSpaceAgree`; the divisor datum and its cycle class are
`HodgePilot.ProjectiveLine` (wave 1).
-/


-- @@ L98-98 verbatim
set_option maxHeartbeats 1000000

-- @@ L99-99 verbatim
set_option synthInstance.maxHeartbeats 1000000


-- @@ L101-101 verbatim
noncomputable section


-- @@ L103-103 verbatim
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

-- @@ L104-104 verbatim
open AlgebraicGeometry HomogeneousLocalization Abelian Topology


-- @@ L106-106 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L108-108 verbatim
namespace HodgePilot


-- @@ L110-110 verbatim
namespace PredicateAcceptance


-- @@ L112-112 verbatim
open HodgePilot.Analytic HodgePilot.Betti HodgePilot.Hyper

-- @@ L113-113 verbatim
open HodgePilot.HodgeFlagAffine HodgePilot.HodgeFlagCertified

-- @@ L114-114 verbatim
open HodgePilot.HodgeFlagProper HodgePilot.Junction

-- @@ L115-115 verbatim
open HodgePilot.AnalyticFormsCharts HodgePilot.ChartsResolution

-- @@ L116-116 verbatim
open HodgePilot.ProjectiveLine HodgePilot.ProjectiveLineUnits

-- @@ L117-117 verbatim
open HodgePilot.ProjectiveLineGraded


-- @@ L119-120 verbatim
/-- The standard grading of `ℂ[X₀, X₁]` by total degree. -/
local notation "𝒜₂" => MvPolynomial.homogeneousSubmodule (Fin 2) ℂ


-- @@ L122-128 verbatim
/-! ## 1. The analytic point-space, and chart probes hit `toSpace`-preimages

The generic lemma `range_probe` (any ℂ-scheme, any chart): the range of a
chart probe on ℂ-points is the `toSpace`-preimage of the chart's image.
The forward inclusion is `toSpace_probe`; the backward one factors the
scheme-theoretic point through the open immersion (`Spec ℂ` has a unique
point). -/


-- @@ L130-130 verbatim
section ProbeRange


-- @@ L132-132 verbatim
variable {X : Scheme} (sX : X ⟶ Spec (CommRingCat.of ℂ))


-- @@ L134-142 verbatim
/-- The underlying-space range of a scheme-theoretic ℂ-point is its single
Zariski image point (`Spec ℂ` has a unique point). -/
theorem range_val_subset (p : SPoints sX) :
    Set.range ⇑p.1 ⊆ {toSpace sX p} := by
  rintro _ ⟨x, rfl⟩
  have hx : x = IsLocalRing.closedPoint ℂ :=
    Subsingleton.elim (α := PrimeSpectrum ℂ) x _
  rw [hx]
  rfl


-- @@ L144-169 verbatim
/-- **Chart probes hit exactly the `toSpace`-preimage of the chart's
image**: the range of a chart probe on ℂ-points is the preimage, under the
comparison map to the Zariski space, of the chart's image. -/
theorem range_probe (c : Chart sX) :
    Set.range (probe sX c.hom c.over) = toSpace sX ⁻¹' Set.range ⇑c.hom := by
  apply Set.Subset.antisymm
  · rintro _ ⟨φ, rfl⟩
    show toSpace sX (probe sX c.hom c.over φ) ∈ Set.range ⇑c.hom
    rw [toSpace_probe]
    exact ⟨toZariski φ, rfl⟩
  · intro p hp
    have hsub : Set.range ⇑p.1 ⊆ Set.range ⇑c.hom := fun y hy => by
      rw [Set.mem_singleton_iff.mp (range_val_subset sX p hy)]
      exact hp
    have hfac : IsOpenImmersion.lift c.hom p.1 hsub ≫ c.hom = p.1 :=
      IsOpenImmersion.lift_fac c.hom p.1 hsub
    have hover : IsOpenImmersion.lift c.hom p.1 hsub ≫ Analytic.structMor c.A =
        𝟙 _ := by
      rw [← c.over, ← Category.assoc, hfac]
      exact p.2
    refine ⟨(bridge c.A).symm ⟨IsOpenImmersion.lift c.hom p.1 hsub, hover⟩, ?_⟩
    refine Subtype.ext ?_
    show ((bridge c.A) ((bridge c.A).symm
      ⟨IsOpenImmersion.lift c.hom p.1 hsub, hover⟩)).1 ≫ c.hom = p.1
    rw [Equiv.apply_symm_apply]
    exact hfac


-- @@ L171-171 verbatim
end ProbeRange


-- @@ L173-173 verbatim
section AnalyticSpace


-- @@ L175-178 verbatim
/-- The analytic point-space of the projective line, as a `TopCat` — the
`T`-slot of the proper-scope predicate (`T := SPoints structMor`, with the
final topology from all affine charts, `HodgePilot.AnalyticGlue`). -/
abbrev anP1 : TopCat.{0} := TopCat.of (SPoints ProjectiveLine.structMor)


-- @@ L180-182 verbatim
/-- The analytic site: the Grothendieck topology of opens of the analytic
point-space. -/
abbrev JAn := Opens.grothendieckTopology anP1


-- @@ L184-187 verbatim
/-- The constant sheaf `ℚ` on the analytic point-space — the sheaf-Betti
carrier of the predicate's class slot (`HodgePilot.Betti`; never called
singular cohomology). -/
abbrev FqAn : Sheaf JAn AddCommGrpCat.{0} := bettiSheafQ anP1


-- @@ L189-192 verbatim
/-- The analytic chart-image open of the chart `D₊(X₀)`: the
`toSpace`-preimage of `U0`. -/
def V0 : Opens ↑anP1 :=
  (Opens.map (sPointsToZariski ProjectiveLine.structMor)).obj U0


-- @@ L194-196 verbatim
/-- The analytic chart-image open of the chart `D₊(X₁)`. -/
def V1 : Opens ↑anP1 :=
  (Opens.map (sPointsToZariski ProjectiveLine.structMor)).obj U1


-- @@ L198-207 verbatim
/-- The two analytic chart opens cover the analytic point-space (wave 1's
`U0_sup_U1`, pulled back). -/
theorem V0_sup_V1 : V0 ⊔ V1 = ⊤ := by
  apply Opens.ext
  rw [Opens.coe_sup, Opens.coe_top]
  have h : (U0 : Set p1) ∪ (U1 : Set p1) = Set.univ := by
    rw [← Opens.coe_sup, U0_sup_U1, Opens.coe_top]
  show ⇑(sPointsToZariski ProjectiveLine.structMor) ⁻¹' (U0 : Set p1) ∪
      ⇑(sPointsToZariski ProjectiveLine.structMor) ⁻¹' (U1 : Set p1) = Set.univ
  rw [← Set.preimage_union, h, Set.preimage_univ]


-- @@ L209-209 verbatim
end AnalyticSpace


-- @@ L211-211 verbatim
/-! ## 2. The overlap chart and its analytic coordinate -/


-- @@ L213-213 verbatim
section OverlapChart


-- @@ L215-227 verbatim
/-- The chart-to-base composite for the overlap chart `D₊(X₀X₁)` is
`Spec.map` of the constants map (the degree-2 analogue of
`ProjectiveLineSmooth.awayι_structMor`). -/
theorem awayι_overlap_structMor :
    Proj.awayι 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) hX01 two_pos ≫
        ProjectiveLine.structMor =
      Analytic.structMor (Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)) := by
  show Proj.awayι 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) hX01 two_pos ≫
      (Proj.toSpecZero 𝒜₂ ≫ Spec.map gradeZeroEquiv.toCommRingCatIso.hom) =
    Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1))))
  rw [Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
  congr 1


-- @@ L229-235 verbatim
/-- The overlap chart `D₊(X₀X₁)` as a chart of the analytic gluing layer:
ring `(ℂ[X₀,X₁]_{X₀X₁})₀` (wave 1's overlap ring, with wave 2's single
`ℂ`-structure), open immersion `Proj.awayι`. -/
def overlapChart : Chart ProjectiveLine.structMor :=
  { A := Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)
    hom := Proj.awayι 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) hX01 two_pos
    «over» := awayι_overlap_structMor }


-- @@ L237-241 verbatim
/-- The overlap-chart probe into the analytic point-space. -/
abbrev prb :
    CPoints (Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)) →
      SPoints ProjectiveLine.structMor :=
  probe ProjectiveLine.structMor overlapChart.hom overlapChart.over


-- @@ L243-244 verbatim
theorem prb_isOpenEmbedding : IsOpenEmbedding prb :=
  isOpenEmbedding_probeChart ProjectiveLine.structMor overlapChart


-- @@ L246-247 verbatim
theorem prb_injective : Function.Injective prb :=
  injective_probeChart ProjectiveLine.structMor overlapChart


-- @@ L249-260 verbatim
/-- The range of the overlap probe is the analytic overlap `V0 ⊓ V1`. -/
theorem range_prb : Set.range prb = ((V0 ⊓ V1 : Opens ↑anP1) : Set ↑anP1) := by
  have h0 : Set.range prb =
      toSpace ProjectiveLine.structMor ⁻¹' Set.range ⇑overlapChart.hom :=
    range_probe ProjectiveLine.structMor overlapChart
  have h1 : Set.range ⇑overlapChart.hom = ((U0 ⊓ U1 : p1.Opens) : Set p1) := by
    rw [U0_inf_U1,
      ← Proj.opensRange_awayι 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)
        hX01 two_pos]
    rfl
  rw [h0, h1, Opens.coe_inf, Set.preimage_inter]
  rfl


-- @@ L262-267 verbatim
/-- The analytic overlap coordinate: evaluation of a ℂ-point of the
overlap chart ring at wave 1's fraction `awayNum` (the realization of
"`X₁/X₀`" on the overlap). -/
def evCoord (φ : CPoints (Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1))) :
    ℂ :=
  φ awayNum


-- @@ L269-270 verbatim
theorem continuous_evCoord : Continuous evCoord :=
  continuous_ev awayNum


-- @@ L272-279 verbatim
/-- The coordinate never vanishes: `awayNum` is a unit of the overlap ring
(wave 1's `awayUnit`). -/
theorem evCoord_ne_zero
    (φ : CPoints (Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1))) :
    evCoord φ ≠ 0 :=
  left_ne_zero_of_mul_eq_one (b := φ awayNumInv)
    (by show φ awayNum * φ awayNumInv = 1
        rw [← map_mul, awayNum_mul_awayNumInv, map_one])


-- @@ L281-281 verbatim
end OverlapChart


-- @@ L283-283 verbatim
/-! ## 3. The slit opens and the disconnected double overlap -/


-- @@ L285-285 verbatim
section SlitOpens


-- @@ L287-288 verbatim
/-- The plane slit region avoiding the closed negative real ray. -/
def slit0 : Set ℂ := {z | 0 < z.re} ∪ {z | z.im ≠ 0}


-- @@ L290-291 verbatim
/-- The plane slit region avoiding the closed positive real ray. -/
def slit1 : Set ℂ := {z | z.re < 0} ∪ {z | z.im ≠ 0}


-- @@ L293-294 verbatim
/-- The open upper half-plane. -/
def upperSet : Set ℂ := {z | 0 < z.im}


-- @@ L296-297 verbatim
/-- The open lower half-plane. -/
def lowerSet : Set ℂ := {z | z.im < 0}


-- @@ L299-301 verbatim
theorem isOpen_slit0 : IsOpen slit0 :=
  (isOpen_lt continuous_const Complex.continuous_re).union
    (isOpen_ne_fun Complex.continuous_im continuous_const)


-- @@ L303-305 verbatim
theorem isOpen_slit1 : IsOpen slit1 :=
  (isOpen_lt Complex.continuous_re continuous_const).union
    (isOpen_ne_fun Complex.continuous_im continuous_const)


-- @@ L307-308 verbatim
theorem isOpen_upperSet : IsOpen upperSet :=
  isOpen_lt continuous_const Complex.continuous_im


-- @@ L310-311 verbatim
theorem isOpen_lowerSet : IsOpen lowerSet :=
  isOpen_lt Complex.continuous_im continuous_const


-- @@ L313-322 verbatim
/-- Every nonzero complex number lies in one of the two slit regions. -/
theorem mem_slit_union {z : ℂ} (hz : z ≠ 0) : z ∈ slit0 ∪ slit1 := by
  by_cases him : z.im = 0
  · have hre : z.re ≠ 0 := fun h =>
      hz (Complex.ext_iff.mpr ⟨h.trans Complex.zero_re.symm,
        him.trans Complex.zero_im.symm⟩)
    rcases lt_or_gt_of_ne hre with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl (Or.inl h)
  · exact Or.inl (Or.inr him)


-- @@ L324-344 verbatim
/-- The two slit regions meet exactly off the real axis: the union of the
open half-planes. -/
theorem slit_inter : slit0 ∩ slit1 = upperSet ∪ lowerSet := by
  ext z
  simp only [slit0, slit1, upperSet, lowerSet, Set.mem_inter_iff,
    Set.mem_union, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h0 | h0, h1 | h1⟩
    · exact absurd (h1.trans h0) (lt_irrefl z.re)
    · rcases lt_or_gt_of_ne h1 with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rcases lt_or_gt_of_ne h0 with h | h
      · exact Or.inr h
      · exact Or.inl h
    · rcases lt_or_gt_of_ne h0 with h | h
      · exact Or.inr h
      · exact Or.inl h
  · rintro (h | h)
    · exact ⟨Or.inr (ne_of_gt h), Or.inr (ne_of_gt h)⟩
    · exact ⟨Or.inr (ne_of_lt h), Or.inr (ne_of_lt h)⟩


-- @@ L346-352 verbatim
/-- The two open half-planes are disjoint. -/
theorem upper_inter_lower : upperSet ∩ lowerSet = ∅ := by
  ext z
  simp only [upperSet, lowerSet, Set.mem_inter_iff, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false, not_and]
  intro h0 h1
  exact absurd (h0.trans h1) (lt_irrefl (0 : ℝ))


-- @@ L354-357 verbatim
/-- The first slit open of the analytic overlap. -/
def W0 : Opens ↑anP1 :=
  ⟨prb '' (evCoord ⁻¹' slit0),
    prb_isOpenEmbedding.isOpenMap _ (isOpen_slit0.preimage continuous_evCoord)⟩


-- @@ L359-362 verbatim
/-- The second slit open of the analytic overlap. -/
def W1 : Opens ↑anP1 :=
  ⟨prb '' (evCoord ⁻¹' slit1),
    prb_isOpenEmbedding.isOpenMap _ (isOpen_slit1.preimage continuous_evCoord)⟩


-- @@ L364-368 verbatim
/-- The upper component of the double overlap. -/
def AUp : Opens ↑anP1 :=
  ⟨prb '' (evCoord ⁻¹' upperSet),
    prb_isOpenEmbedding.isOpenMap _
      (isOpen_upperSet.preimage continuous_evCoord)⟩


-- @@ L370-374 verbatim
/-- The lower component of the double overlap. -/
def BLo : Opens ↑anP1 :=
  ⟨prb '' (evCoord ⁻¹' lowerSet),
    prb_isOpenEmbedding.isOpenMap _
      (isOpen_lowerSet.preimage continuous_evCoord)⟩


-- @@ L376-384 verbatim
/-- The two slit opens cover the analytic overlap. -/
theorem W0_sup_W1 : W0 ⊔ W1 = V0 ⊓ V1 := by
  apply Opens.ext
  rw [Opens.coe_sup]
  show prb '' (evCoord ⁻¹' slit0) ∪ prb '' (evCoord ⁻¹' slit1) = _
  rw [← Set.image_union, ← Set.preimage_union,
    Set.eq_univ_of_forall
      (fun φ => Set.mem_preimage.mpr (mem_slit_union (evCoord_ne_zero φ))),
    Set.image_univ, range_prb]


-- @@ L386-394 verbatim
/-- The double overlap of the slit opens is the disjoint union of the two
half-plane opens. -/
theorem W0_inf_W1 : W0 ⊓ W1 = AUp ⊔ BLo := by
  apply Opens.ext
  rw [Opens.coe_inf, Opens.coe_sup]
  show prb '' (evCoord ⁻¹' slit0) ∩ prb '' (evCoord ⁻¹' slit1) =
    prb '' (evCoord ⁻¹' upperSet) ∪ prb '' (evCoord ⁻¹' lowerSet)
  rw [← Set.image_inter prb_injective, ← Set.image_union,
    ← Set.preimage_inter, ← Set.preimage_union, slit_inter]


-- @@ L396-402 verbatim
/-- The two half-plane opens are disjoint. -/
theorem AUp_inf_BLo : AUp ⊓ BLo = ⊥ := by
  apply Opens.ext
  rw [Opens.coe_inf, Opens.coe_bot]
  show prb '' (evCoord ⁻¹' upperSet) ∩ prb '' (evCoord ⁻¹' lowerSet) = ∅
  rw [← Set.image_inter prb_injective, ← Set.preimage_inter,
    upper_inter_lower, Set.preimage_empty, Set.image_empty]


-- @@ L404-404 verbatim
end SlitOpens


-- @@ L406-406 verbatim
/-! ## 4. The mixed section over the disconnected double overlap -/


-- @@ L408-408 verbatim
section MixedSection


-- @@ L410-416 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The canonical constant section of the constant sheaf: the
sheafification-unit image of the rational constant `1` over `W`. -/
def constOne (W : Opens ↑anP1) : FqAn.obj.obj (op W) :=
  ((sheafificationAdjunction JAn AddCommGrpCat.{0}).unit.app
    ((Functor.const (Opens ↑anP1)ᵒᵖ).obj
      (AddCommGrpCat.of (ULift.{0} ℚ)))).app (op W) (ULift.up 1)


-- @@ L418-422 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The left gluing datum: the constant-`1` section over the upper
component (stated at the Type-valued `forget` spelling the Mayer–Vietoris
glue consumes). -/
def mixLeft : ((FqAn.obj ⋙ forget AddCommGrpCat).obj (op AUp)) := constOne AUp


-- @@ L424-427 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The right gluing datum: the zero section over the lower component. -/
def mixRight : ((FqAn.obj ⋙ forget AddCommGrpCat).obj (op BLo)) :=
  (0 : FqAn.obj.obj (op BLo))


-- @@ L429-445 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **The overlap agreement is vacuous**: the two gluing data agree over
`AUp ⊓ BLo = ⊥` — two sections of a sheaf over the empty open are equal
(separatedness with no points to check,
`TopCat.Presheaf.IsSheaf.section_ext`). -/
theorem mix_overlap :
    (FqAn.obj ⋙ forget AddCommGrpCat).map
        ((Opens.mayerVietorisSquare AUp BLo).f₁₂).op mixLeft =
      (FqAn.obj ⋙ forget AddCommGrpCat).map
        ((Opens.mayerVietorisSquare AUp BLo).f₁₃).op mixRight := by
  show FqAn.obj.map ((Opens.mayerVietorisSquare AUp BLo).f₁₂).op mixLeft =
    FqAn.obj.map ((Opens.mayerVietorisSquare AUp BLo).f₁₃).op mixRight
  apply TopCat.Presheaf.IsSheaf.section_ext FqAn.property
  intro x hx
  have hx' : x ∈ AUp ⊓ BLo := hx
  rw [AUp_inf_BLo] at hx'
  exact absurd hx' (by simp)


-- @@ L447-454 verbatim
/-- The glued mixed datum over the union `AUp ⊔ BLo` (the pin's
Mayer–Vietoris sheaf condition, at the Type-valued `forget` spelling). -/
def mixGlued :
    ((FqAn.obj ⋙ forget AddCommGrpCat).obj
      (op ((Opens.mayerVietorisSquare AUp BLo).toSquare.X₄))) :=
  ((Opens.mayerVietorisSquare AUp BLo).sheafCondition_of_sheaf
    ((sheafCompose JAn (forget AddCommGrpCat)).obj FqAn)).glue
    mixLeft mixRight mix_overlap


-- @@ L456-459 verbatim
/-- Receipt: the components square's fourth object is the union,
definitionally. -/
theorem mixSquare_X₄ :
    (Opens.mayerVietorisSquare AUp BLo).toSquare.X₄ = AUp ⊔ BLo := rfl


-- @@ L461-466 verbatim
/-- Receipt: the glued datum restricts to the constant-`1` section on the
upper component. -/
theorem mixGlued_restrict_left :
    (FqAn.obj ⋙ forget AddCommGrpCat).map
        ((Opens.mayerVietorisSquare AUp BLo).f₂₄).op mixGlued = mixLeft :=
  GrothendieckTopology.MayerVietorisSquare.SheafCondition.map_f₂₄_op_glue _ _ _ _


-- @@ L468-473 verbatim
/-- Receipt: the glued datum restricts to the zero section on the lower
component. -/
theorem mixGlued_restrict_right :
    (FqAn.obj ⋙ forget AddCommGrpCat).map
        ((Opens.mayerVietorisSquare AUp BLo).f₃₄).op mixGlued = mixRight :=
  GrothendieckTopology.MayerVietorisSquare.SheafCondition.map_f₃₄_op_glue _ _ _ _


-- @@ L475-483 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **The mixed section** over the disconnected double overlap
`W0 ⊓ W1 = AUp ⊔ BLo` — classically `1` on the upper component and `0` on
the lower.  (A globally constant section would be the restriction of a
section of a covering chart and would die under the edge map below; the
mixed section is the honest δ-input.) -/
def mixSection : FqAn.obj.obj (op (W0 ⊓ W1)) :=
  FqAn.obj.map (homOfLE (le_of_eq W0_inf_W1)).op
    (mixGlued : FqAn.obj.obj (op (AUp ⊔ BLo)))


-- @@ L485-485 verbatim
end MixedSection


-- @@ L487-487 verbatim
/-! ## 5. The Betti-side edge class -/


-- @@ L489-489 verbatim
section EdgeClass


-- @@ L491-496 verbatim
/-- The mixed section as a degree-0 `Sheaf.H'` class over the double
overlap (the generic degree-0-sections identification of
`HodgePilot.ProjectiveLineGraded` Part 1, instantiated on the analytic
site). -/
def mixH0 : Ext (freeYonedaSheaf JAn (W0 ⊓ W1)) FqAn 0 :=
  (h0SectionsEquiv FqAn (W0 ⊓ W1)).symm mixSection


-- @@ L498-502 verbatim
/-- The inner edge: the connecting map of Riou's Mayer–Vietoris sequence
for the slit cover, applied to the mixed section — a degree-1 class of
the constant sheaf over `W0 ⊔ W1`. -/
def edgeOneRaw : Ext (freeYonedaSheaf JAn (W0 ⊔ W1)) FqAn 1 :=
  (Opens.mayerVietorisSquare W0 W1).δ FqAn 0 1 rfl mixH0


-- @@ L504-507 verbatim
/-- Receipt: the slit square's fourth object is the union,
definitionally. -/
theorem slitSquare_X₄ :
    (Opens.mayerVietorisSquare W0 W1).toSquare.X₄ = W0 ⊔ W1 := rfl


-- @@ L509-513 verbatim
/-- The inner edge class, re-anchored at the analytic overlap
(`W0_sup_W1`). -/
def edgeOne : Ext (freeYonedaSheaf JAn (V0 ⊓ V1)) FqAn 1 :=
  CycCarrier.extReanchorLeft
    (eqToIso (congrArg (freeYonedaSheaf JAn) W0_sup_W1)) 1 edgeOneRaw


-- @@ L515-519 verbatim
/-- The outer edge: the connecting map for the two-chart cover of the
analytic point-space, applied to the inner edge class — a degree-2 class
of the constant sheaf over `V0 ⊔ V1`. -/
def edgeTwoRaw : Ext (freeYonedaSheaf JAn (V0 ⊔ V1)) FqAn 2 :=
  (Opens.mayerVietorisSquare V0 V1).δ FqAn 1 2 rfl edgeOne


-- @@ L521-524 verbatim
/-- Receipt: the chart square's fourth object is the union,
definitionally. -/
theorem chartSquare_X₄ :
    (Opens.mayerVietorisSquare V0 V1).toSquare.X₄ = V0 ⊔ V1 := rfl


-- @@ L526-529 verbatim
/-- The outer edge class, re-anchored at `⊤` (`V0_sup_V1`). -/
def edgeTwo : Ext (freeYonedaSheaf JAn (⊤ : Opens ↑anP1)) FqAn 2 :=
  CycCarrier.extReanchorLeft
    (eqToIso (congrArg (freeYonedaSheaf JAn) V0_sup_V1)) 2 edgeTwoRaw


-- @@ L531-542 verbatim
/-- **The Betti-side degree-2 edge class on the analytic point-space of
the projective line**, in the predicate's exact carrier
`bettiQ (TopCat.of (SPoints structMor)) 2`: the double Mayer–Vietoris
edge of the mixed `1`/`0` section, carried into Mathlib's `Sheaf.H` along
the terminal-anchor identification of `HodgePilot.ProjectiveLineGraded`
Part 1.  **Not claimed to be nonzero HERE** (the named gap
`BettiEdgeNonvanishing` below; since 2026-07-15 PROVED unconditionally at
`AnalyticWallB.bettiEdgeNonvanishing`).  *Betti* is, as everywhere in this
project, a gloss for sheaf cohomology of the constant sheaf, never
singular cohomology.  Nothing here makes the Hodge conjecture statable. -/
def bettiEdgeClass : bettiQ anP1 2 :=
  hPrimeTopEquivH (⊤ : Opens ↑anP1) (opensTopTerminal anP1) FqAn 2 edgeTwo


-- @@ L544-554 verbatim
/-- **Named unproved `Prop` (registry style): nonvanishing of the Betti
edge class** — the analytic flavor of the chart-interference wall.  A
proof needs exactly the recon's H⁰-on-connected-opens analysis
(connectedness of the analytic chart opens and the two-component
structure of the double overlap, through the Mayer–Vietoris exactness),
which is deliberately not attempted here.  Stated, never proved, never
assumed, never used.  **Since proved (2026-07-15):** discharged
unconditionally by `AnalyticWallB.bettiEdgeNonvanishing`; the sentences
above are kept as the pre-closure record (never assumed or used by this
module). -/
def BettiEdgeNonvanishing : Prop := bettiEdgeClass ≠ 0


-- @@ L556-589 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **Negative control, general form** (the wave-3 falsifier pattern on the
analytic site): any degree-0 class restricted from the first slit open maps
to zero under the same inner edge route (`fromBiprod_δ` — data extending to
a covering open has vanishing edge class). -/
theorem edgeRoute_restriction_eq_zero
    (y : Ext (freeYonedaSheaf JAn W0) FqAn 0) :
    (Opens.mayerVietorisSquare W0 W1).δ FqAn 0 1 rfl
      ((FqAn.cohomologyPresheaf 0).map
        ((Opens.mayerVietorisSquare W0 W1).f₁₂).op y) = 0 := by
  have h1 : (FqAn.cohomologyPresheaf 0).map
      ((Opens.mayerVietorisSquare W0 W1).f₁₂).op y =
      (Opens.mayerVietorisSquare W0 W1).fromBiprod FqAn 0
        ((AddCommGrpCat.biprodIsoProd _ _).inv
          ((y, 0) : (FqAn.H' 0 (Opens.mayerVietorisSquare W0 W1).toSquare.X₂) ×
            (FqAn.H' 0 (Opens.mayerVietorisSquare W0 W1).toSquare.X₃))) := by
    rw [(Opens.mayerVietorisSquare W0 W1).fromBiprod_biprodIsoProd_inv_apply
      FqAn y 0, map_zero, sub_zero]
  rw [h1]
  have h2 := congrArg
    (fun (t : ((FqAn.H' 0 (Opens.mayerVietorisSquare W0 W1).toSquare.X₂) ⊞
        (FqAn.H' 0 (Opens.mayerVietorisSquare W0 W1).toSquare.X₃) :
          AddCommGrpCat.{0}) ⟶
        FqAn.H' 1 (Opens.mayerVietorisSquare W0 W1).toSquare.X₄) =>
      t ((AddCommGrpCat.biprodIsoProd _ _).inv
          ((y, 0) : (FqAn.H' 0 (Opens.mayerVietorisSquare W0 W1).toSquare.X₂) ×
            (FqAn.H' 0 (Opens.mayerVietorisSquare W0 W1).toSquare.X₃))))
    ((Opens.mayerVietorisSquare W0 W1).fromBiprod_δ FqAn 0 1 rfl)
  refine h2.trans ?_
  show ((0 : _ ⟶ FqAn.H' 1 (Opens.mayerVietorisSquare W0 W1).toSquare.X₄))
    ((AddCommGrpCat.biprodIsoProd _ _).inv
          ((y, 0) : (FqAn.H' 0 (Opens.mayerVietorisSquare W0 W1).toSquare.X₂) ×
            (FqAn.H' 0 (Opens.mayerVietorisSquare W0 W1).toSquare.X₃))) = 0
  rfl


-- @@ L591-611 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **Negative control, concrete instance**: the restriction to the double
overlap of the constant-`1` section over the first slit open dies under the
same edge route that carries the mixed section — the inner edge only
detects data that does not extend to a covering open.  (A construction
that secretly sent every overlap section to the same class would collide
with this receipt.) -/
theorem edgeRoute_constOne_eq_zero :
    (Opens.mayerVietorisSquare W0 W1).δ FqAn 0 1 rfl
      ((h0SectionsEquiv FqAn (W0 ⊓ W1)).symm
        (FqAn.obj.map ((Opens.mayerVietorisSquare W0 W1).f₁₂).op
          (constOne W0))) = 0 := by
  have hres : (h0SectionsEquiv FqAn (W0 ⊓ W1)).symm
      (FqAn.obj.map ((Opens.mayerVietorisSquare W0 W1).f₁₂).op (constOne W0)) =
    (FqAn.cohomologyPresheaf 0).map ((Opens.mayerVietorisSquare W0 W1).f₁₂).op
      ((h0SectionsEquiv FqAn W0).symm (constOne W0)) := by
    rw [h0SectionsEquiv_symm_apply, h0SectionsEquiv_symm_apply,
      cohomologyPresheaf_map_eq]
    exact mk₀_sheafHomOfSection_natural FqAn _ (constOne W0)
  rw [hres]
  exact edgeRoute_restriction_eq_zero _


-- @@ L613-613 verbatim
end EdgeClass


-- @@ L615-616 verbatim
/-! ## 6. The acceptance shape: the predicate at the Betti edge class,
proved up to two named receipts -/


-- @@ L618-618 verbatim
section Acceptance


-- @@ L620-620 verbatim
open HodgePilot.HodgePredicate HodgePilot.DeRhamPresheaf

-- @@ L621-621 verbatim
open HodgePilot.CartierClass HodgePilot.CycCarrier


-- @@ L623-625 verbatim
/-- Receipt (golden-path smoothness wave): the predicate's binder pair
synthesizes on the projective line with no hypothesized binder. -/
example : SmoothOfRelativeDimension 1 ProjectiveLine.structMor := inferInstance


-- @@ L627-627 verbatim
example : AlgebraicGeometry.IsProper ProjectiveLine.structMor := inferInstance


-- @@ L629-638 verbatim
/-- **The space-side presentation of wave 1's divisor-level cycle class**:
the underlying `ℍ²_dR` class of `dinfCycleClass`, moved to the space-side
presentation along the proven site agreement (P3,
`DeRhamSpaceAgree.hyperHdRSpaceEquiv`).  The intended acceptance
witness. -/
def dinfCycleClassSpace :
    DeRhamSheaf.hyperHdRSpace (cRingHom ProjectiveLine.structMor) 2 :=
  DeRhamSpaceAgree.hyperHdRSpaceEquiv (cRingHom ProjectiveLine.structMor) 2
    (dinfCycleClass :
      DeRhamSheaf.hyperHdR (cRingHom ProjectiveLine.structMor) 2)


-- @@ L640-647 verbatim
/-- Drift-guard receipt: the intended witness is literally wave 1's
construction chain — `cdivCycleClassC` at the site-moved divisor datum
`dinf` — transported along P3. -/
theorem dinfCycleClassSpace_receipt :
    dinfCycleClassSpace =
      DeRhamSpaceAgree.hyperHdRSpaceEquiv (cRingHom ProjectiveLine.structMor) 2
        (cdivCycleClassC ProjectiveLine.structMor (cdivSiteEquiv p1 dinf) :
          DeRhamSheaf.hyperHdR (cRingHom ProjectiveLine.structMor) 2) := rfl


-- @@ L649-658 verbatim
/-- **Named unproved `Prop` — the filtration-transport receipt**: the
space-side witness lies in the space-side naive (brutal-truncation)
filtration cut at `1`, in degree `2`.  (The site-level membership is wave
1's by-construction `dinfCycleClass_mem`; what is not proved here is its
transport along the P3 site agreement.)  Stated, never proved, never
assumed; consumed only as an explicit hypothesis of
`isHodgeClassProper_bettiEdge_of_receipts`. -/
def DinfSpaceFiltration : Prop :=
  dinfCycleClassSpace ∈
    dRSpaceFiltrationC ProjectiveLine.structMor ((1 : ℕ) : ℤ) ((2 * 1 : ℕ) : ℤ)


-- @@ L660-687 verbatim
/-- **Named unproved `Prop` — the junction-evaluation receipt** (the
priced P2-instance computation): the junction at the constructed forms
input (`HodgeFlagProper.formsInputProper`) sends the space-side
cycle-class witness to the certified-equivalence image of the ℚ→ℂ image
of the Betti edge class.  This is the exact evaluation this module does
not perform: the repo ships naturality for every map in the junction
composite but no section-level evaluation receipts
(`HodgePilot.HodgeFlagAffine` §12, `HodgePilot.HodgeFlagProper` §§1–3);
the same blocking spelling — three nested adjunction transposes
(sheafification, dense subsite, pull–push) plus a chart-realization
evaluation lemma — was documented at degree `0` by the golden-path
auxiliary wave.  Stated, never proved, never assumed; consumed only as an
explicit hypothesis of `isHodgeClassProper_bettiEdge_of_receipts`.

**Legacy v1 (untwisted)** — per the 2026-07-15 Tate-twist rebase (outside
review #8), the official computational goal is the twisted receipt
`HodgePilot.TateTwistLayer.OfficialJunctionEvaluation`; this untwisted
spelling is kept verbatim as the historical variant (see
`TateTwistLayer.HistoricalUntwistedJunctionEvaluation`). -/
def DinfJunctionEvaluation : Prop :=
  deRhamJunction (cRingHom ProjectiveLine.structMor)
      (sPointsToZariski ProjectiveLine.structMor)
      (analyticDeRhamComplexChartsZ ProjectiveLine.structMor 1)
      (formsInputProper ProjectiveLine.structMor 1) ((2 * 1 : ℕ) : ℤ)
      dinfCycleClassSpace =
    analyticDeRhamChartsEquiv ProjectiveLine.structMor 1 (2 * 1)
      (toComplexCoeffs (TopCat.of (SPoints ProjectiveLine.structMor)) (2 * 1)
        bettiEdgeClass)


-- @@ L689-710 verbatim
/-- **The acceptance shape, proved up to the two named receipts**: given
the filtration-transport receipt and the junction-evaluation receipt, the
Hodge-class predicate at smooth-proper scope — every input constructed,
the analytic input certified, the binder pair synthesized with no
hypothesized binder — **accepts the Betti edge class at `p = 1` on the
projective line**.  The entitled sentence for this theorem: *the
predicate accepts the constructed class, with the two named receipts as
the exactly-remaining gap*.  It does NOT assert either receipt, it does
NOT assert the class is nonzero, and nothing here makes the Hodge
conjecture statable.

**Legacy v1 (untwisted)** — per the 2026-07-15 Tate-twist rebase (outside
review #8), the official-convention twin is
`HodgePilot.TwistedPredicate.isHodgeClassProperTwisted_bettiEdge_of_official`;
this untwisted acceptance is kept verbatim as the historical variant. -/
theorem isHodgeClassProper_bettiEdge_of_receipts
    (hmem : DinfSpaceFiltration) (heval : DinfJunctionEvaluation) :
    IsHodgeClassProper ProjectiveLine.structMor 1 1 bettiEdgeClass := by
  show analyticDeRhamChartsEquiv ProjectiveLine.structMor 1 (2 * 1)
      (toComplexCoeffs (TopCat.of (SPoints ProjectiveLine.structMor)) (2 * 1)
        bettiEdgeClass) ∈ _
  exact AddSubgroup.mem_map.mpr ⟨dinfCycleClassSpace, hmem, heval⟩


-- @@ L712-726 verbatim
/-- Definitional receipt: the acceptance target unfolds to exactly the
membership whose witness the two named receipts supply. -/
theorem isHodgeClassProper_bettiEdge_iff :
    IsHodgeClassProper ProjectiveLine.structMor 1 1 bettiEdgeClass ↔
      analyticDeRhamChartsEquiv ProjectiveLine.structMor 1 (2 * 1)
          (toComplexCoeffs (TopCat.of (SPoints ProjectiveLine.structMor))
            (2 * 1) bettiEdgeClass) ∈
        (dRSpaceFiltrationC ProjectiveLine.structMor ((1 : ℕ) : ℤ)
            ((2 * 1 : ℕ) : ℤ)).map
          (deRhamJunction (cRingHom ProjectiveLine.structMor)
            (sPointsToZariski ProjectiveLine.structMor)
            (analyticDeRhamComplexChartsZ ProjectiveLine.structMor 1)
            (formsInputProper ProjectiveLine.structMor 1)
            ((2 * 1 : ℕ) : ℤ)) :=
  Iff.rfl


-- @@ L728-728 verbatim
end Acceptance


-- @@ L730-730 verbatim
end PredicateAcceptance


-- @@ L732-732 verbatim
end HodgePilot


-- @@ L734-734 verbatim
end
