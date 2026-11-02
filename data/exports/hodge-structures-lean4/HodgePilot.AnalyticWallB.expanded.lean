import HodgePilot.CechGoursat
import HodgePilot.AnalyticWallA
import HodgePilot.AffineVanishing


-- @@ L5-87 verbatim
/-! # The analytic chart-interference wall, Leg B: degree-1 vanishing on the
# chart opens — the two parked receipts discharged, and the wall closed

Wall Leg B closing wave.  `HodgePilot.AnalyticWallA` proved Leg A
unconditionally and Leg C conditional on exactly two parked named receipts,
`AnalyticChartOneVanishingV0` / `AnalyticChartOneVanishingV1` — degree-1
constant-sheaf cohomology vanishing on the two analytic chart opens of the
projective line's analytic point-space.  This module **proves both receipts**
and ships the unconditional forms.

**The engine (chart-generic).**  For any open `V` of the analytic point-space
`anP1` that is the range of an open embedding `e : ℂ → anP1`:

* `isSectionsSurjectiveKernel_chartOpen` — every short exact sequence of
  abelian sheaves out of the constant-sheaf carrier `FqAn` has surjective
  sections over `V`: the Kempf/Nugent Γ-surjectivity assembly of
  `HodgePilot.AffineVanishing.isSectionsSurjectiveKernel_affine`, transposed
  from a finite basic-open cover of an affine open to the (infinite)
  ball-image cover of a chart open.  Local lifts shrink to `e`-images of
  metric balls; kernel-valued differences on the pairwise overlaps are
  constant sections by the Leg-A section-value layer (ball-image overlaps are
  preconnected, being homeomorphic images of intersections of convex sets);
  the resulting ℚ-valued Čech cocycle on the ball cover of `ℂ` is corrected
  by the Čech–Goursat coboundary theorem of `HodgePilot.CechGoursat`
  (consumed through the receipt `cechCoboundary`); the corrected lifts glue,
  and locality closes the verification.  No finiteness, no quasi-compactness
  and no ring language is used anywhere — the affine template's finite
  subcover and Serre-style Čech correction are replaced by the arbitrary-index
  gluing of Mathlib's sheaf API and the Goursat coboundary.
* `subsingleton_hPrimeOne_chartOpen` — hence `H'¹(V, FqAn) = 0` in the sense
  of Mathlib's `Sheaf.H'` (`Ext` at the free-Yoneda anchor of `V`), by the
  degree-one brick through the injective presentation of `FqAn`.

**The receipts, discharged.**  `chartEmbedV0` / `chartEmbedV1` — the wave-2
chart isomorphisms `chartPolyEquiv` transported to ℂ-points
(`cpointsCongr`), composed with `mvPolynomialHomeomorph` and the chart
probes — are open embeddings of `ℂ` with ranges exactly `V0` and `V1`, so
`analyticChartOneVanishingV0` / `analyticChartOneVanishingV1` hold at the
literal parked spellings of `HodgePilot.AnalyticWallA`.

**The wall, closed (unconditional).**  With both receipts discharged, the
Leg-C conditional theorems of `HodgePilot.AnalyticWallA` fire:

* `edgeTwoRaw_ne_zero`, `bettiEdgeClass_ne_zero`;
* `bettiEdgeNonvanishing : PredicateAcceptance.BettiEdgeNonvanishing` — the
  named gap retired at its literal spelling;
* `toComplexCoeffs_bettiEdge_ne_zero` — the fork-closing form: the ℂ-image
  of the Betti edge class under the (injective) coefficient change is
  nonzero.

## What is and is not proved (entitlement, in full)

PROVED, unconditional: the Γ-surjectivity predicate of
`HodgePilot.AcyclicClassC` for `FqAn` over every chart-image open; degree-1
vanishing `Subsingleton (Ext (freeYonedaSheaf JAn V) FqAn 1)` over every
chart-image open, in particular both parked receipts; and the four
unconditional wall forms listed above.  NOT PROVED, NOT CLAIMED: any
computation of any `Sheaf.H`/`Sheaf.H'` group of any carrier (vanishing
statements are `Subsingleton`s, never identifications); any comparison
between the constant-sheaf carriers and singular cohomology (*Betti* is, as
everywhere in this project, a gloss for sheaf cohomology of the constant
sheaf, never singular cohomology); any general contractibility-implies-
vanishing principle (the statement is exactly at chart-image opens of this
space, through the exhibited embeddings); anything about the parked junction
evaluation or the 2πi-fork normalization (this module does not import,
consume, or restate any junction spelling).  No claim that any constructed
map is an isomorphism beyond the proven `≃ₜ`/`≃ₐ` cited from shipped
modules.  Nothing here makes the Hodge conjecture statable.

## Credits

The Γ-surjectivity architecture is Brian Nugent's affine-vanishing chain
(mathlib4 PR #36345 and its chain, after G. Kempf 1980), as shipped in
`HodgePilot.AffineVanishing` — this module is its transposition to the
analytic site; the degree-one brick and the sections-surjectivity predicate
are `HodgePilot.AcyclicClassC`; `Sheaf.H'`/`Ext`, the sites machinery and
sheafification are Joël Riou's and Mathlib's; the section-value layer is
`HodgePilot.AnalyticWallA`; the coboundary input is
`HodgePilot.CechGoursat` (Goursat's bisection); the chart rings and
`chartPolyEquiv` are wave 2 / `HodgePilot.ProjectiveLineUnits` (on Jujian
Zhang's and the 2025 Proj cluster's Mathlib work), and the ℂ-points
plumbing is `HodgePilot.Analytic` / `HodgePilot.AnalyticGlue`.
-/


-- @@ L89-89 verbatim
set_option maxHeartbeats 1000000

-- @@ L90-90 verbatim
set_option synthInstance.maxHeartbeats 1000000


-- @@ L92-92 verbatim
noncomputable section


-- @@ L94-94 verbatim
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

-- @@ L95-95 verbatim
open CategoryTheory.Abelian AlgebraicGeometry HomogeneousLocalization Topology


-- @@ L97-97 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L99-99 verbatim
namespace HodgePilot


-- @@ L101-101 verbatim
namespace AnalyticWallB


-- @@ L103-103 verbatim
open HodgePilot.Betti HodgePilot.PredicateAcceptance

-- @@ L104-104 verbatim
open HodgePilot.ProjectiveLineGraded HodgePilot.ProjectiveLine

-- @@ L105-105 verbatim
open HodgePilot.ProjectiveLineUnits HodgePilot.Analytic

-- @@ L106-106 verbatim
open HodgePilot.AnalyticWallA


-- @@ L108-109 verbatim
/-- The standard grading of `ℂ[X₀, X₁]` by total degree. -/
local notation "𝒜₂" => MvPolynomial.homogeneousSubmodule (Fin 2) ℂ


-- @@ L111-114 verbatim
/-! ## 1. Generic analytic-site plumbing

The sheaf-level restriction/lift/gluing devices of the affine template
(`HodgePilot.AffineVanishing` Parts 3–6), re-keyed at the analytic site. -/


-- @@ L116-116 verbatim
section SitePlumbing


-- @@ L118-125 verbatim
/-- Restriction composition for an arbitrary abelian sheaf on the analytic
point-space (the analytic sibling of `AffineVanishing.smap_smap`). -/
theorem smap_smap (F : Sheaf JAn AddCommGrpCat.{0}) {V W T : Opens ↑anP1}
    (h1 : W ≤ T) (h2 : V ≤ W) (h3 : V ≤ T) (s : F.obj.obj (op T)) :
    F.obj.map (homOfLE h2).op (F.obj.map (homOfLE h1).op s) =
      F.obj.map (homOfLE h3).op s := by
  rw [← CategoryTheory.comp_apply, ← F.obj.map_comp, ← op_comp]
  exact congrArg (fun (t : V ⟶ T) => F.obj.map t.op s) (Subsingleton.elim _ _)


-- @@ L127-136 verbatim
/-- Componentwise injectivity of a sheaf monomorphism at the analytic site. -/
theorem app_injective_of_mono {F G : Sheaf JAn AddCommGrpCat.{0}} (ι : F ⟶ G)
    [Mono ι] (V : Opens ↑anP1) : Function.Injective (ι.hom.app (op V)) := by
  haveI : Mono ((sheafToPresheaf JAn AddCommGrpCat.{0}).map ι) :=
    (sheafToPresheaf JAn AddCommGrpCat.{0}).map_mono ι
  haveI : Mono (((sheafToPresheaf JAn AddCommGrpCat.{0}).map ι).app (op V)) :=
    inferInstance
  exact (AddCommGrpCat.mono_iff_injective (ι.hom.app (op V))).mp
    (inferInstanceAs
      (Mono (((sheafToPresheaf JAn AddCommGrpCat.{0}).map ι).app (op V))))


-- @@ L138-149 verbatim
/-- Local lifts against an epimorphism (epi ⟹ locally surjective at the
analytic site). -/
theorem exists_localLift {B R : Sheaf JAn AddCommGrpCat.{0}} (g : B ⟶ R)
    (hepi : Epi g) {V : Opens ↑anP1} (r : R.obj.obj (op V)) (x : ↑anP1)
    (hx : x ∈ V) :
    ∃ (W : Opens ↑anP1) (hWV : W ≤ V) (t : B.obj.obj (op W)), x ∈ W ∧
      g.hom.app (op W) t = R.obj.map (homOfLE hWV).op r := by
  have hls : TopCat.Presheaf.IsLocallySurjective g.hom :=
    (TopCat.Sheaf.isLocallySurjective_iff_epi (F := B) (G := R) g).mpr hepi
  obtain ⟨W, hWle, ⟨t0, ht0⟩, hxW⟩ :=
    (TopCat.Presheaf.isLocallySurjective_iff g.hom).mp hls V r x hx
  exact ⟨W, hWle, t0, hxW, ht0⟩


-- @@ L151-157 verbatim
/-- Kernel-valued differences: a section of the middle killed by the quotient
comes from the kernel (left exactness of sections at the analytic site). -/
theorem exists_kernelDiff {S : ShortComplex (Sheaf JAn AddCommGrpCat.{0})}
    (hex : S.Exact) (hmono : Mono S.f) {V : Opens ↑anP1}
    (t : S.X₂.obj.obj (op V)) (ht : S.g.hom.app (op V) t = 0) :
    ∃ w : S.X₁.obj.obj (op V), S.f.hom.app (op V) w = t :=
  TopCat.Sheaf.sections_exact_of_left_exact hex hmono t ht


-- @@ L159-168 verbatim
/-- Arbitrary-index gluing at the analytic site. -/
theorem exists_gluing {κ : Type} (Us : κ → Opens ↑anP1) (V : Opens ↑anP1)
    (hle : ∀ i, Us i ≤ V) (hcov : V ≤ iSup Us)
    (B : Sheaf JAn AddCommGrpCat.{0})
    (sf : ∀ i : κ, B.obj.obj (op (Us i)))
    (hcomp : TopCat.Presheaf.IsCompatible B.1 Us sf) :
    ∃ s : B.obj.obj (op V), ∀ i, B.obj.map (homOfLE (hle i)).op s = sf i := by
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := B) Us V
    (fun i => homOfLE (hle i)) hcov sf hcomp
  exact ⟨s, hs⟩


-- @@ L170-176 verbatim
/-- Arbitrary-index locality at the analytic site. -/
theorem sections_locality {κ : Type} (Us : κ → Opens ↑anP1) (V : Opens ↑anP1)
    (hle : ∀ i, Us i ≤ V) (hcov : V ≤ iSup Us)
    (R : Sheaf JAn AddCommGrpCat.{0}) (s t : R.obj.obj (op V))
    (h : ∀ i, R.obj.map (homOfLE (hle i)).op s =
      R.obj.map (homOfLE (hle i)).op t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq' R Us V (fun i => homOfLE (hle i)) hcov s t h


-- @@ L178-189 verbatim
/-- Sections over an open with empty carrier are unique (locality along the
empty cover). -/
theorem sections_eq_of_empty (B : Sheaf JAn AddCommGrpCat.{0})
    {O : Opens ↑anP1} (hO : (O : Set ↑anP1) = ∅) (s t : B.obj.obj (op O)) :
    s = t := by
  have hbot : O ≤ iSup (fun i : Empty => (i.elim : Opens ↑anP1)) := by
    intro p hp
    have hp' : p ∈ (O : Set ↑anP1) := hp
    rw [hO] at hp'
    exact absurd hp' (Set.notMem_empty p)
  exact sections_locality (fun i : Empty => i.elim) O (fun i => i.elim) hbot
    B s t (fun i => i.elim)


-- @@ L191-191 verbatim
end SitePlumbing


-- @@ L193-197 verbatim
/-! ## 2. Section-level constancy on preconnected opens

The Leg-A section-value engine (`HodgePilot.AnalyticWallA` §11) upgraded from
pointwise values to section-level constancy — the joint that turns
kernel-valued difference sections into a genuine ℚ-valued Čech cocycle. -/


-- @@ L199-199 verbatim
section Constancy


-- @@ L201-212 verbatim
/-- A section with the same local value at every point IS the constant
section (sheaf locality on the `hasVal` witnesses). -/
theorem eq_constSec_of_forall_hasVal {V : Opens ↑anP1}
    (s : FqAn.obj.obj (op V)) (r : ℚ)
    (h : ∀ (x : ↑anP1) (_hx : x ∈ V), hasVal V s x r) : s = constSec r V := by
  choose W hWV hxW hres using h
  apply TopCat.Sheaf.eq_of_locally_eq' (F := FqAn)
    (fun p : {x : ↑anP1 // x ∈ V} => W p.1 p.2) V
    (fun p => homOfLE (hWV p.1 p.2))
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxW x hx⟩)
  intro p
  rw [hres p.1 p.2, constSec_res]


-- @@ L214-225 verbatim
/-- **Section-level constancy on preconnected opens**: over a preconnected
open with a point, every section of the constant-sheaf carrier is the
constant section at its section value. -/
theorem eq_constSec_of_preconnected {V : Opens ↑anP1}
    (hV : IsPreconnected (V : Set ↑anP1)) (s : FqAn.obj.obj (op V))
    {x₀ : ↑anP1} (hx₀ : x₀ ∈ V) :
    s = constSec (secVal V s x₀ hx₀) V := by
  apply eq_constSec_of_forall_hasVal
  intro x hx
  have h1 : secVal V s x hx = secVal V s x₀ hx₀ := secVal_congr_pt hV s hx hx₀
  have h2 := secVal_spec V s hx
  rwa [h1] at h2


-- @@ L227-234 verbatim
/-- Constant sections subtract by subtracting values. -/
theorem constSec_sub (q r : ℚ) (W : Opens ↑anP1) :
    constSec q W - constSec r W = constSec (q - r) W := by
  have h := constSec_add (q - r) r W
  have h2 : q - r + r = q := by ring
  rw [h2] at h
  rw [← h]
  abel


-- @@ L236-236 verbatim
end Constancy


-- @@ L238-238 verbatim
/-! ## 3. Ball-image cover geometry through an open embedding -/


-- @@ L240-240 verbatim
section BallGeometry


-- @@ L242-248 verbatim
/-- Images of convex sets under an open embedding have preconnected
intersections. -/
theorem image_inter_preconnected (e : ℂ → ↑anP1) (he : IsOpenEmbedding e)
    {s t : Set ℂ} (hs : Convex ℝ s) (ht : Convex ℝ t) :
    IsPreconnected (e '' s ∩ e '' t) := by
  rw [← Set.image_inter he.injective]
  exact (hs.inter ht).isPreconnected.image e he.continuous.continuousOn


-- @@ L250-253 verbatim
/-- Ball images under an open embedding are open. -/
theorem image_ball_isOpen (e : ℂ → ↑anP1) (he : IsOpenEmbedding e)
    (z : ℂ) (r : ℝ) : IsOpen (e '' Metric.ball z r) :=
  he.isOpenMap _ Metric.isOpen_ball


-- @@ L255-259 verbatim
/-- The ball-image cover element at center `x` and radius `ε`, as an open of
the analytic point-space. -/
def ballImg (e : ℂ → ↑anP1) (he : IsOpenEmbedding e) (x : ℂ) (ε : ℝ) :
    Opens ↑anP1 :=
  ⟨e '' Metric.ball x ε, image_ball_isOpen e he x ε⟩


-- @@ L261-263 verbatim
@[simp] theorem coe_ballImg (e : ℂ → ↑anP1) (he : IsOpenEmbedding e)
    (x : ℂ) (ε : ℝ) : (ballImg e he x ε : Set ↑anP1) = e '' Metric.ball x ε :=
  rfl


-- @@ L265-267 verbatim
theorem mem_ballImg {e : ℂ → ↑anP1} (he : IsOpenEmbedding e) {x : ℂ} {ε : ℝ}
    {p : ℂ} (hp : p ∈ Metric.ball x ε) : e p ∈ ballImg e he x ε :=
  ⟨p, hp, rfl⟩


-- @@ L269-273 verbatim
theorem mem_ballImg_inf {e : ℂ → ↑anP1} (he : IsOpenEmbedding e)
    {x y : ℂ} {εx εy : ℝ} {p : ℂ}
    (hp : p ∈ Metric.ball x εx ∩ Metric.ball y εy) :
    e p ∈ ballImg e he x εx ⊓ ballImg e he y εy :=
  ⟨mem_ballImg he hp.1, mem_ballImg he hp.2⟩


-- @@ L275-279 verbatim
theorem coe_ballImg_inf (e : ℂ → ↑anP1) (he : IsOpenEmbedding e)
    (x y : ℂ) (εx εy : ℝ) :
    ((ballImg e he x εx ⊓ ballImg e he y εy : Opens ↑anP1) : Set ↑anP1) =
      e '' (Metric.ball x εx ∩ Metric.ball y εy) := by
  rw [Opens.coe_inf, coe_ballImg, coe_ballImg, ← Set.image_inter he.injective]


-- @@ L281-286 verbatim
theorem preconnected_ballImg_inf (e : ℂ → ↑anP1) (he : IsOpenEmbedding e)
    (x y : ℂ) (εx εy : ℝ) :
    IsPreconnected
      ((ballImg e he x εx ⊓ ballImg e he y εy : Opens ↑anP1) : Set ↑anP1) := by
  rw [Opens.coe_inf, coe_ballImg, coe_ballImg]
  exact image_inter_preconnected e he (convex_ball x εx) (convex_ball y εy)


-- @@ L288-292 verbatim
theorem ballImg_inf_empty {e : ℂ → ↑anP1} (he : IsOpenEmbedding e)
    {x y : ℂ} {εx εy : ℝ}
    (h : ¬ (Metric.ball x εx ∩ Metric.ball y εy).Nonempty) :
    ((ballImg e he x εx ⊓ ballImg e he y εy : Opens ↑anP1) : Set ↑anP1) = ∅ := by
  rw [coe_ballImg_inf, Set.not_nonempty_iff_eq_empty.mp h, Set.image_empty]


-- @@ L294-294 verbatim
end BallGeometry


-- @@ L296-299 verbatim
/-! ## 4. The two chart embeddings: `ℂ` onto `V0` and onto `V1`

The wave-2 chart isomorphism `chartPolyEquiv` transported to ℂ-points,
composed with `mvPolynomialHomeomorph` and the chart probes. -/


-- @@ L301-301 verbatim
section ChartEmbeddings


-- @@ L303-316 verbatim
/-- The ℂ-points homeomorphism along an algebra isomorphism (contravariant
`comap` in both directions). -/
def cpointsCongr {A B : Type} [CommRing A] [Algebra ℂ A] [CommRing B]
    [Algebra ℂ B] (e : A ≃ₐ[ℂ] B) : CPoints B ≃ₜ CPoints A where
  toFun := Analytic.comap e.toAlgHom
  invFun := Analytic.comap e.symm.toAlgHom
  left_inv φ := by
    show (φ.comp e.toAlgHom).comp e.symm.toAlgHom = φ
    exact AlgHom.ext fun b => by simp
  right_inv φ := by
    show (φ.comp e.symm.toAlgHom).comp e.toAlgHom = φ
    exact AlgHom.ext fun a => by simp
  continuous_toFun := continuous_comap e.toAlgHom
  continuous_invFun := continuous_comap e.symm.toAlgHom


-- @@ L318-323 verbatim
/-- The chart `D₊(X₀)` as a chart of the analytic gluing layer (the degree-1
sibling of `PredicateAcceptance.overlapChart`). -/
def chart0 : Chart ProjectiveLine.structMor :=
  { A := Away 𝒜₂ (MvPolynomial.X 0)
    hom := Proj.awayι 𝒜₂ (MvPolynomial.X 0) (X_mem_grade_one 0) one_pos
    «over» := HodgePilot.ProjectiveLineSmooth.awayι_structMor 0 }


-- @@ L325-328 verbatim
/-- The X₀-chart probe into the analytic point-space. -/
abbrev prb0 :
    CPoints (Away 𝒜₂ (MvPolynomial.X 0)) → SPoints ProjectiveLine.structMor :=
  probe ProjectiveLine.structMor chart0.hom chart0.over


-- @@ L330-331 verbatim
theorem prb0_isOpenEmbedding : IsOpenEmbedding prb0 :=
  isOpenEmbedding_probeChart ProjectiveLine.structMor chart0


-- @@ L333-344 verbatim
/-- The range of the X₀-chart probe is the analytic chart open `V0`. -/
theorem range_prb0 : Set.range prb0 = (V0 : Set ↑anP1) := by
  have h0 : Set.range prb0 =
      toSpace ProjectiveLine.structMor ⁻¹' Set.range ⇑chart0.hom :=
    PredicateAcceptance.range_probe ProjectiveLine.structMor chart0
  have hU0 : (U0 : p1.Opens) = Proj.basicOpen 𝒜₂ (MvPolynomial.X 0) := rfl
  have h1 : Set.range ⇑chart0.hom = ((U0 : p1.Opens) : Set p1) := by
    rw [hU0, ← Proj.opensRange_awayι 𝒜₂ (MvPolynomial.X 0) (X_mem_grade_one 0)
      one_pos]
    rfl
  rw [h0, h1]
  rfl


-- @@ L346-352 verbatim
/-- The chart coordinate homeomorphism at `D₊(X₀)`: `ℂ ≃ₜ` the ℂ-points of
the chart ring (wave-2 chart iso + `mvPolynomialHomeomorph` +
`Homeomorph.funUnique`). -/
def chartHomeoV0 : ℂ ≃ₜ CPoints (Away 𝒜₂ (MvPolynomial.X 0)) :=
  ((Homeomorph.funUnique (Fin 1) ℂ).symm.trans
    (mvPolynomialHomeomorph (Fin 1)).symm).trans
    (cpointsCongr ProjectiveLineUnits.awayXZeroPolyEquiv)


-- @@ L354-355 verbatim
/-- **The first chart embedding**: `ℂ` onto the analytic chart open `V0`. -/
def chartEmbedV0 : ℂ → ↑anP1 := prb0 ∘ chartHomeoV0


-- @@ L357-358 verbatim
theorem chartEmbedV0_isOpenEmbedding : IsOpenEmbedding chartEmbedV0 :=
  prb0_isOpenEmbedding.comp chartHomeoV0.isOpenEmbedding


-- @@ L360-363 verbatim
theorem range_chartEmbedV0 : Set.range chartEmbedV0 = (V0 : Set ↑anP1) := by
  show Set.range (prb0 ∘ chartHomeoV0) = (V0 : Set ↑anP1)
  rw [Set.range_comp, chartHomeoV0.surjective.range_eq, Set.image_univ,
    range_prb0]


-- @@ L365-369 verbatim
/-- The chart `D₊(X₁)` as a chart of the analytic gluing layer. -/
def chart1 : Chart ProjectiveLine.structMor :=
  { A := Away 𝒜₂ (MvPolynomial.X 1)
    hom := Proj.awayι 𝒜₂ (MvPolynomial.X 1) (X_mem_grade_one 1) one_pos
    «over» := HodgePilot.ProjectiveLineSmooth.awayι_structMor 1 }


-- @@ L371-374 verbatim
/-- The X₁-chart probe into the analytic point-space. -/
abbrev prb1 :
    CPoints (Away 𝒜₂ (MvPolynomial.X 1)) → SPoints ProjectiveLine.structMor :=
  probe ProjectiveLine.structMor chart1.hom chart1.over


-- @@ L376-377 verbatim
theorem prb1_isOpenEmbedding : IsOpenEmbedding prb1 :=
  isOpenEmbedding_probeChart ProjectiveLine.structMor chart1


-- @@ L379-390 verbatim
/-- The range of the X₁-chart probe is the analytic chart open `V1`. -/
theorem range_prb1 : Set.range prb1 = (V1 : Set ↑anP1) := by
  have h0 : Set.range prb1 =
      toSpace ProjectiveLine.structMor ⁻¹' Set.range ⇑chart1.hom :=
    PredicateAcceptance.range_probe ProjectiveLine.structMor chart1
  have hU1 : (U1 : p1.Opens) = Proj.basicOpen 𝒜₂ (MvPolynomial.X 1) := rfl
  have h1 : Set.range ⇑chart1.hom = ((U1 : p1.Opens) : Set p1) := by
    rw [hU1, ← Proj.opensRange_awayι 𝒜₂ (MvPolynomial.X 1) (X_mem_grade_one 1)
      one_pos]
    rfl
  rw [h0, h1]
  rfl


-- @@ L392-397 verbatim
/-- The chart coordinate homeomorphism at `D₊(X₁)` (the wave-2 chart iso at
the mirrored index pair). -/
def chartHomeoV1 : ℂ ≃ₜ CPoints (Away 𝒜₂ (MvPolynomial.X 1)) :=
  ((Homeomorph.funUnique (Fin 1) ℂ).symm.trans
    (mvPolynomialHomeomorph (Fin 1)).symm).trans
    (cpointsCongr (ProjectiveLineUnits.chartPolyEquiv 1 0 (by decide)))


-- @@ L399-400 verbatim
/-- **The second chart embedding**: `ℂ` onto the analytic chart open `V1`. -/
def chartEmbedV1 : ℂ → ↑anP1 := prb1 ∘ chartHomeoV1


-- @@ L402-403 verbatim
theorem chartEmbedV1_isOpenEmbedding : IsOpenEmbedding chartEmbedV1 :=
  prb1_isOpenEmbedding.comp chartHomeoV1.isOpenEmbedding


-- @@ L405-408 verbatim
theorem range_chartEmbedV1 : Set.range chartEmbedV1 = (V1 : Set ↑anP1) := by
  show Set.range (prb1 ∘ chartHomeoV1) = (V1 : Set ↑anP1)
  rw [Set.range_comp, chartHomeoV1.surjective.range_eq, Set.image_univ,
    range_prb1]


-- @@ L410-410 verbatim
end ChartEmbeddings


-- @@ L412-412 verbatim
/-! ## 5. The coboundary input -/


-- @@ L414-423 verbatim
/-- **The Čech–Goursat coboundary receipt**: the main theorem of
`HodgePilot.CechGoursat`, in exactly the slot shape the assembly consumes —
a ℚ-valued Čech `1`-cocycle on an open convex cover of `ℂ` is a coboundary. -/
theorem cechCoboundary : ∀ {κ : Type} (Us : κ → Set ℂ) (qc : κ → κ → ℚ),
    (∀ i, IsOpen (Us i)) → (∀ i, Convex ℝ (Us i)) →
    (⋃ i, Us i) = Set.univ →
    (∀ i j k, (Us i ∩ Us j ∩ Us k).Nonempty → qc i j + qc j k = qc i k) →
    ∃ b : κ → ℚ, ∀ i j, (Us i ∩ Us j).Nonempty → qc i j = b j - b i :=
  fun Us qc hop hconv hcov hcoc =>
    HodgePilot.CechGoursat.exists_coboundary Us qc hop hconv hcov hcoc


-- @@ L425-426 verbatim
/-! ## 6. Γ-surjectivity over chart-image opens: the transposed
Kempf/Nugent assembly -/


-- @@ L428-428 verbatim
section GammaSurj


-- @@ L430-661 verbatim
/-- **Γ-surjectivity of every short exact sequence out of the constant-sheaf
carrier, over every chart-image open**: `FqAn` satisfies the
sections-surjectivity predicate of `HodgePilot.AcyclicClassC` over every open
of the analytic point-space that is the range of an open embedding of `ℂ`.
(The Kempf/Nugent assembly on the ball-image cover; the Čech correction is
the Goursat coboundary.) -/
theorem isSectionsSurjectiveKernel_chartOpen {V : Opens ↑anP1}
    (e : ℂ → ↑anP1) (he : IsOpenEmbedding e)
    (hrange : Set.range e = (V : Set ↑anP1)) :
    HodgePilot.AcyclicClassC.IsSectionsSurjectiveKernel (J := JAn) V FqAn := by
  intro B R fι g hfg hSE r
  classical
  haveI hmono : Mono fι := hSE.mono_f
  -- 1. pointwise lifts, shrunk to ball images of the chart coordinates
  have hlift : ∀ x : ℂ, ∃ (ε : ℝ) (t : B.obj.obj (op (ballImg e he x ε)))
      (hle : ballImg e he x ε ≤ V), 0 < ε ∧
      g.hom.app (op (ballImg e he x ε)) t = R.obj.map (homOfLE hle).op r := by
    intro x
    have hx : e x ∈ V := by
      have h1 : e x ∈ Set.range e := Set.mem_range_self x
      rwa [hrange] at h1
    obtain ⟨W, hWV, t0, hxW, ht0⟩ := exists_localLift g hSE.epi_g r (e x) hx
    have hopen : IsOpen (e ⁻¹' (W : Set ↑anP1)) :=
      W.isOpen.preimage he.continuous
    have hmem : x ∈ e ⁻¹' (W : Set ↑anP1) := hxW
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp hopen x hmem
    have hleW : ballImg e he x ε ≤ W := by
      rintro p ⟨p', hp', rfl⟩
      exact hsub hp'
    refine ⟨ε, B.obj.map (homOfLE hleW).op t0, hleW.trans hWV, hε, ?_⟩
    have hnat : g.hom.app (op (ballImg e he x ε))
        (B.obj.map (homOfLE hleW).op t0) =
        R.obj.map (homOfLE hleW).op (g.hom.app (op W) t0) := by
      rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
        g.hom.naturality]
    rw [hnat, ht0]
    exact smap_smap R hWV hleW (hleW.trans hWV) r
  choose εf tf hleV hεf htf using hlift
  -- 2. the cover facts
  have hcov : V ≤ iSup (fun x : ℂ => ballImg e he x (εf x)) := by
    intro p hp
    have hpr : p ∈ Set.range e := by rw [hrange]; exact hp
    obtain ⟨x, rfl⟩ := hpr
    exact Opens.mem_iSup.mpr ⟨x, mem_ballImg he (Metric.mem_ball_self (hεf x))⟩
  have hOV : ∀ x y : ℂ,
      ballImg e he x (εf x) ⊓ ballImg e he y (εf y) ≤ V :=
    fun x y => inf_le_left.trans (hleV x)
  -- 3. kernel-valued differences on pairwise overlaps
  have hdiff : ∀ x y : ℂ,
      g.hom.app (op (ballImg e he x (εf x) ⊓ ballImg e he y (εf y)))
        (B.obj.map (homOfLE (inf_le_left : ballImg e he x (εf x) ⊓
            ballImg e he y (εf y) ≤ ballImg e he x (εf x))).op (tf x) -
          B.obj.map (homOfLE (inf_le_right : ballImg e he x (εf x) ⊓
            ballImg e he y (εf y) ≤ ballImg e he y (εf y))).op (tf y)) = 0 := by
    intro x y
    rw [map_sub]
    have hnL : g.hom.app (op (ballImg e he x (εf x) ⊓ ballImg e he y (εf y)))
        (B.obj.map (homOfLE (inf_le_left : ballImg e he x (εf x) ⊓
          ballImg e he y (εf y) ≤ ballImg e he x (εf x))).op (tf x)) =
        R.obj.map (homOfLE (inf_le_left : ballImg e he x (εf x) ⊓
          ballImg e he y (εf y) ≤ ballImg e he x (εf x))).op
          (g.hom.app (op (ballImg e he x (εf x))) (tf x)) := by
      rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
        g.hom.naturality]
    have hnR : g.hom.app (op (ballImg e he x (εf x) ⊓ ballImg e he y (εf y)))
        (B.obj.map (homOfLE (inf_le_right : ballImg e he x (εf x) ⊓
          ballImg e he y (εf y) ≤ ballImg e he y (εf y))).op (tf y)) =
        R.obj.map (homOfLE (inf_le_right : ballImg e he x (εf x) ⊓
          ballImg e he y (εf y) ≤ ballImg e he y (εf y))).op
          (g.hom.app (op (ballImg e he y (εf y))) (tf y)) := by
      rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
        g.hom.naturality]
    rw [hnL, hnR, htf x, htf y,
      smap_smap R (hleV x) inf_le_left (hOV x y) r,
      smap_smap R (hleV y) inf_le_right (hOV x y) r, sub_self]
  have hker : ∀ x y : ℂ, ∃ w : FqAn.obj.obj
      (op (ballImg e he x (εf x) ⊓ ballImg e he y (εf y))),
      fι.hom.app (op (ballImg e he x (εf x) ⊓ ballImg e he y (εf y))) w =
        B.obj.map (homOfLE (inf_le_left : ballImg e he x (εf x) ⊓
          ballImg e he y (εf y) ≤ ballImg e he x (εf x))).op (tf x) -
        B.obj.map (homOfLE (inf_le_right : ballImg e he x (εf x) ⊓
          ballImg e he y (εf y) ≤ ballImg e he y (εf y))).op (tf y) :=
    fun x y => exists_kernelDiff hSE.exact hSE.mono_f _ (hdiff x y)
  choose w hw using hker
  -- 4. the differences are constant sections (preconnected overlaps)
  have hqcex : ∀ x y : ℂ, ∃ qv : ℚ,
      (Metric.ball x (εf x) ∩ Metric.ball y (εf y)).Nonempty →
      w x y = constSec qv (ballImg e he x (εf x) ⊓ ballImg e he y (εf y)) := by
    intro x y
    by_cases h : (Metric.ball x (εf x) ∩ Metric.ball y (εf y)).Nonempty
    · exact ⟨secVal (ballImg e he x (εf x) ⊓ ballImg e he y (εf y)) (w x y)
        (e h.choose) (mem_ballImg_inf he h.choose_spec), fun _ =>
        eq_constSec_of_preconnected
          (preconnected_ballImg_inf e he x y (εf x) (εf y)) (w x y)
          (mem_ballImg_inf he h.choose_spec)⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose qc hqc using hqcex
  -- 5. the cocycle identity on nonempty triple overlaps
  have hcoc : ∀ x y z : ℂ, (Metric.ball x (εf x) ∩ Metric.ball y (εf y) ∩
      Metric.ball z (εf z)).Nonempty → qc x y + qc y z = qc x z := by
    intro x y z htrip
    obtain ⟨p, hp⟩ := htrip
    have hpxy : p ∈ Metric.ball x (εf x) ∩ Metric.ball y (εf y) := hp.1
    have hpyz : p ∈ Metric.ball y (εf y) ∩ Metric.ball z (εf z) :=
      ⟨hp.1.2, hp.2⟩
    have hpxz : p ∈ Metric.ball x (εf x) ∩ Metric.ball z (εf z) :=
      ⟨hp.1.1, hp.2⟩
    have hle_xy : ballImg e he x (εf x) ⊓ ballImg e he y (εf y) ⊓
        ballImg e he z (εf z) ≤ ballImg e he x (εf x) ⊓ ballImg e he y (εf y) :=
      inf_le_left
    have hle_yz : ballImg e he x (εf x) ⊓ ballImg e he y (εf y) ⊓
        ballImg e he z (εf z) ≤ ballImg e he y (εf y) ⊓ ballImg e he z (εf z) :=
      le_inf (inf_le_left.trans inf_le_right) inf_le_right
    have hle_xz : ballImg e he x (εf x) ⊓ ballImg e he y (εf y) ⊓
        ballImg e he z (εf z) ≤ ballImg e he x (εf x) ⊓ ballImg e he z (εf z) :=
      le_inf (inf_le_left.trans inf_le_left) inf_le_right
    -- the FqAn-level identity on the triple overlap
    have hwT : FqAn.obj.map (homOfLE hle_xy).op (w x y) +
        FqAn.obj.map (homOfLE hle_yz).op (w y z) =
        FqAn.obj.map (homOfLE hle_xz).op (w x z) := by
      apply app_injective_of_mono fι
        (ballImg e he x (εf x) ⊓ ballImg e he y (εf y) ⊓ ballImg e he z (εf z))
      rw [map_add]
      have hpair : ∀ (u v : ℂ) (hle : ballImg e he x (εf x) ⊓
          ballImg e he y (εf y) ⊓ ballImg e he z (εf z) ≤
          ballImg e he u (εf u) ⊓ ballImg e he v (εf v)),
          fι.hom.app (op (ballImg e he x (εf x) ⊓ ballImg e he y (εf y) ⊓
            ballImg e he z (εf z)))
            (FqAn.obj.map (homOfLE hle).op (w u v)) =
          B.obj.map (homOfLE (hle.trans inf_le_left)).op (tf u) -
            B.obj.map (homOfLE (hle.trans inf_le_right)).op (tf v) := by
        intro u v hle
        have hnat : fι.hom.app (op (ballImg e he x (εf x) ⊓
            ballImg e he y (εf y) ⊓ ballImg e he z (εf z)))
            (FqAn.obj.map (homOfLE hle).op (w u v)) =
            B.obj.map (homOfLE hle).op
              (fι.hom.app (op (ballImg e he u (εf u) ⊓ ballImg e he v (εf v)))
                (w u v)) := by
          rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
            fι.hom.naturality]
        rw [hnat, hw u v, map_sub,
          smap_smap B inf_le_left hle (hle.trans inf_le_left) (tf u),
          smap_smap B inf_le_right hle (hle.trans inf_le_right) (tf v)]
      rw [hpair x y hle_xy, hpair y z hle_yz, hpair x z hle_xz]
      have hnormB : ∀ (u : ℂ) (h h' : ballImg e he x (εf x) ⊓
          ballImg e he y (εf y) ⊓ ballImg e he z (εf z) ≤
          ballImg e he u (εf u)),
          B.obj.map (homOfLE h).op (tf u) = B.obj.map (homOfLE h').op (tf u) :=
        fun u h h' => congrArg
          (fun (hh : ballImg e he x (εf x) ⊓ ballImg e he y (εf y) ⊓
            ballImg e he z (εf z) ⟶ ballImg e he u (εf u)) =>
            B.obj.map hh.op (tf u)) (Subsingleton.elim _ _)
      rw [hnormB y (hle_xy.trans inf_le_right) (hle_yz.trans inf_le_left),
        hnormB z (hle_yz.trans inf_le_right) (hle_xz.trans inf_le_right),
        hnormB x (hle_xz.trans inf_le_left) (hle_xy.trans inf_le_left)]
      abel
    -- separate the constant values at the (image of the) triple point
    rw [hqc x y ⟨p, hpxy⟩, hqc y z ⟨p, hpyz⟩, hqc x z ⟨p, hpxz⟩,
      constSec_res, constSec_res, constSec_res, constSec_add] at hwT
    exact constSec_inj
      (⟨mem_ballImg_inf he hp.1, mem_ballImg he hp.2⟩ :
        (e p) ∈ ballImg e he x (εf x) ⊓ ballImg e he y (εf y) ⊓
          ballImg e he z (εf z)) hwT
  -- 6. the Goursat coboundary corrects the cocycle
  obtain ⟨bC, hbC⟩ := cechCoboundary (fun x : ℂ => Metric.ball x (εf x)) qc
    (fun x => Metric.isOpen_ball) (fun x => convex_ball x (εf x))
    (Set.iUnion_eq_univ_iff.mpr fun p => ⟨p, Metric.mem_ball_self (hεf p)⟩)
    hcoc
  -- 7. corrected lifts agree on overlaps
  have hucompat : ∀ x y : ℂ,
      B.obj.map (homOfLE (inf_le_left : ballImg e he x (εf x) ⊓
        ballImg e he y (εf y) ≤ ballImg e he x (εf x))).op
        (tf x - fι.hom.app (op (ballImg e he x (εf x)))
          (constSec (- bC x) (ballImg e he x (εf x)))) =
      B.obj.map (homOfLE (inf_le_right : ballImg e he x (εf x) ⊓
        ballImg e he y (εf y) ≤ ballImg e he y (εf y))).op
        (tf y - fι.hom.app (op (ballImg e he y (εf y)))
          (constSec (- bC y) (ballImg e he y (εf y)))) := by
    intro x y
    by_cases hne : (Metric.ball x (εf x) ∩ Metric.ball y (εf y)).Nonempty
    · have hwc : w x y = constSec (- bC x - - bC y)
          (ballImg e he x (εf x) ⊓ ballImg e he y (εf y)) := by
        rw [hqc x y hne]
        congr 1
        rw [hbC x y hne]
        ring
      have hnatc : ∀ (u : ℂ) (h : ballImg e he x (εf x) ⊓
          ballImg e he y (εf y) ≤ ballImg e he u (εf u)),
          B.obj.map (homOfLE h).op
            (fι.hom.app (op (ballImg e he u (εf u)))
              (constSec (- bC u) (ballImg e he u (εf u)))) =
          fι.hom.app (op (ballImg e he x (εf x) ⊓ ballImg e he y (εf y)))
            (FqAn.obj.map (homOfLE h).op
              (constSec (- bC u) (ballImg e he u (εf u)))) := by
        intro u h
        rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
          fι.hom.naturality]
      rw [map_sub, map_sub, hnatc x inf_le_left, hnatc y inf_le_right,
        constSec_res, constSec_res, sub_eq_sub_iff_sub_eq_sub, ← hw x y,
        ← map_sub, constSec_sub, ← hwc]
    · exact sections_eq_of_empty B (ballImg_inf_empty he hne) _ _
  have hcomp : TopCat.Presheaf.IsCompatible B.1
      (fun x : ℂ => ballImg e he x (εf x))
      (fun x : ℂ => tf x - fι.hom.app (op (ballImg e he x (εf x)))
        (constSec (- bC x) (ballImg e he x (εf x)))) :=
    fun x y => hucompat x y
  -- 8. glue and verify by locality
  obtain ⟨tglue, htglue⟩ := exists_gluing
    (fun x : ℂ => ballImg e he x (εf x)) V hleV hcov B
    (fun x : ℂ => tf x - fι.hom.app (op (ballImg e he x (εf x)))
      (constSec (- bC x) (ballImg e he x (εf x)))) hcomp
  refine ⟨tglue, ?_⟩
  apply sections_locality (fun x : ℂ => ballImg e he x (εf x)) V hleV hcov R
  intro x
  have hnat : R.obj.map (homOfLE (hleV x)).op (g.hom.app (op V) tglue) =
      g.hom.app (op (ballImg e he x (εf x)))
        (B.obj.map (homOfLE (hleV x)).op tglue) := by
    rw [← CategoryTheory.comp_apply, ← CategoryTheory.comp_apply,
      g.hom.naturality]
  rw [hnat, htglue x, map_sub]
  have hzero : g.hom.app (op (ballImg e he x (εf x)))
      (fι.hom.app (op (ballImg e he x (εf x)))
        (constSec (- bC x) (ballImg e he x (εf x)))) = 0 := by
    rw [← CategoryTheory.comp_apply]
    have h0 : fι.hom.app (op (ballImg e he x (εf x))) ≫
        g.hom.app (op (ballImg e he x (εf x))) = 0 := by
      have h1 := congrArg
        (fun (z : FqAn ⟶ R) => z.hom.app (op (ballImg e he x (εf x)))) hfg
      simpa using h1
    rw [h0]
    rfl
  rw [hzero, sub_zero, htf x]


-- @@ L663-663 verbatim
end GammaSurj


-- @@ L665-665 verbatim
/-! ## 7. Degree-1 vanishing on chart-image opens: the receipts discharged -/


-- @@ L667-667 verbatim
section Vanishing


-- @@ L669-685 verbatim
/-- **Degree-1 vanishing of the constant-sheaf carrier at every chart-image
open**: `H'¹(V, FqAn) = Ext (freeYonedaSheaf JAn V) FqAn 1` is a subsingleton
whenever `V` is the range of an open embedding of `ℂ`, in the sense of
Mathlib's `Sheaf.H'`.  Nothing here makes the Hodge conjecture statable. -/
theorem subsingleton_hPrimeOne_chartOpen {V : Opens ↑anP1}
    (e : ℂ → ↑anP1) (he : IsOpenEmbedding e)
    (hrange : Set.range e = (V : Set ↑anP1)) :
    Subsingleton (Ext (freeYonedaSheaf JAn V) FqAn 1) := by
  have hS : (ShortComplex.mk (Injective.ι FqAn)
      (cokernel.π (Injective.ι FqAn)) (cokernel.condition _)).ShortExact :=
    { exact := ShortComplex.cokernelSequence_exact _
      mono_f := inferInstanceAs (Mono (Injective.ι FqAn))
      epi_g := inferInstanceAs (Epi (cokernel.π (Injective.ι FqAn))) }
  haveI : Injective (Injective.under FqAn) := Injective.injective_under FqAn
  exact HodgePilot.AffineVanishing.subsingleton_ext_one_of_app_surjective hS V
    (isSectionsSurjectiveKernel_chartOpen e he hrange _ _ _ hS)
    (Ext.subsingleton_of_injective _ _ 0)


-- @@ L687-692 verbatim
/-- **The first parked Leg-B receipt, discharged**:
`AnalyticChartOneVanishingV0` holds at its literal spelling. -/
theorem analyticChartOneVanishingV0 :
    HodgePilot.AnalyticWallA.AnalyticChartOneVanishingV0 :=
  subsingleton_hPrimeOne_chartOpen chartEmbedV0 chartEmbedV0_isOpenEmbedding
    range_chartEmbedV0


-- @@ L694-699 verbatim
/-- **The second parked Leg-B receipt, discharged**:
`AnalyticChartOneVanishingV1` holds at its literal spelling. -/
theorem analyticChartOneVanishingV1 :
    HodgePilot.AnalyticWallA.AnalyticChartOneVanishingV1 :=
  subsingleton_hPrimeOne_chartOpen chartEmbedV1 chartEmbedV1_isOpenEmbedding
    range_chartEmbedV1


-- @@ L701-704 verbatim
/-- Drift guard: the discharged receipt is literally the parked `Prop`. -/
theorem analyticChartOneVanishingV0_pin :
    HodgePilot.AnalyticWallA.AnalyticChartOneVanishingV0 =
      Subsingleton (Ext (freeYonedaSheaf JAn V0) FqAn 1) := rfl


-- @@ L706-709 verbatim
/-- Drift guard: the discharged receipt is literally the parked `Prop`. -/
theorem analyticChartOneVanishingV1_pin :
    HodgePilot.AnalyticWallA.AnalyticChartOneVanishingV1 =
      Subsingleton (Ext (freeYonedaSheaf JAn V1) FqAn 1) := rfl


-- @@ L711-711 verbatim
end Vanishing


-- @@ L713-717 verbatim
/-! ## 8. The wall closed: the unconditional forms

With both receipts discharged, the Leg-C conditional theorems of
`HodgePilot.AnalyticWallA` fire — each of the following is one application
of the corresponding `_of_receipts` theorem. -/


-- @@ L719-719 verbatim
section WallClosed


-- @@ L721-724 verbatim
/-- **The outer (raw) edge is nonzero, unconditionally.** -/
theorem edgeTwoRaw_ne_zero : PredicateAcceptance.edgeTwoRaw ≠ 0 :=
  HodgePilot.AnalyticWallA.edgeTwoRaw_ne_zero_of_receipts
    analyticChartOneVanishingV0 analyticChartOneVanishingV1


-- @@ L726-729 verbatim
/-- **The Betti-side edge class is nonzero, unconditionally.** -/
theorem bettiEdgeClass_ne_zero : PredicateAcceptance.bettiEdgeClass ≠ 0 :=
  HodgePilot.AnalyticWallA.bettiEdgeClass_ne_zero_of_receipts
    analyticChartOneVanishingV0 analyticChartOneVanishingV1


-- @@ L731-736 verbatim
/-- **THE NAMED GAP RETIRED**: `PredicateAcceptance.BettiEdgeNonvanishing`
holds at its literal spelling, unconditionally.  Nothing here makes the
Hodge conjecture statable. -/
theorem bettiEdgeNonvanishing : PredicateAcceptance.BettiEdgeNonvanishing :=
  HodgePilot.AnalyticWallA.bettiEdgeNonvanishing_of_receipts
    analyticChartOneVanishingV0 analyticChartOneVanishingV1


-- @@ L738-747 verbatim
/-- **The fork-closing form, unconditional**: the ℂ-image of the Betti edge
class under the (injective) ℚ→ℂ coefficient change is nonzero — exactly the
hypothesis shape whose *negation* governs the degenerate branch of the
2πi-fork trichotomy.  (This module does not consume or restate any junction
spelling; the fork itself is untouched.) -/
theorem toComplexCoeffs_bettiEdge_ne_zero :
    Betti.toComplexCoeffs (TopCat.of (SPoints ProjectiveLine.structMor)) 2
      PredicateAcceptance.bettiEdgeClass ≠ 0 :=
  HodgePilot.AnalyticWallA.toComplexCoeffs_bettiEdge_ne_zero_of_receipts
    analyticChartOneVanishingV0 analyticChartOneVanishingV1


-- @@ L749-752 verbatim
/-- Drift guard: the retired gap is literally the nonvanishing statement. -/
theorem bettiEdgeNonvanishing_pin :
    PredicateAcceptance.BettiEdgeNonvanishing =
      (PredicateAcceptance.bettiEdgeClass ≠ 0) := rfl


-- @@ L754-754 verbatim
end WallClosed


-- @@ L756-756 verbatim
end AnalyticWallB


-- @@ L758-758 verbatim
end HodgePilot


-- @@ L760-760 verbatim
end
