import HodgePilot.PredicateAcceptance


-- @@ L3-92 verbatim
/-! # The analytic chart-interference wall, Leg A: the H⁰/connectedness half
# (`edgeOne ≠ 0`), with the conditional assembly to the ℂ-image of the edge

Analytic-wall wave, Leg A (recon `analyticwall_recon_2026-07-15.md` §5),
Opus-draft/Fable-finish pipeline.  For the analytic point-space `anP1` of the
projective line and the constant-sheaf carrier `FqAn` of
`HodgePilot.PredicateAcceptance`, this module:

**LANDED, unconditional.**
* **`edgeOne_ne_zero`** — the inner Mayer–Vietoris edge class
  `PredicateAcceptance.edgeOne` is **nonzero**: the mixed `1`-on-`AUp` /
  `0`-on-`BLo` δ-input is not a restriction-difference from the connected slit
  opens `W0`, `W1`, because a section of the constant sheaf over a connected
  open determines a single rational value at every point (the section-value
  layer `secVal` below), while the mixed section evaluates to `1` at a point of
  the upper component and `0` at a point of the lower.  This retires the
  "is the δ-input even detected" risk for the whole edge tower.
* the two half-plane components are **inhabited by constructed points**
  (`upPt`, `loPt` — the characters of the overlap chart ring at `±i`,
  realized through the wave-1 localization plumbing), and the slit opens are
  **preconnected** (`Complex.slitPlane` star-convexity, transported through the
  overlap probe).
* **`toComplexCoeffs_injective`** — the ℚ→ℂ coefficient-change map of
  `HodgePilot.Betti` is **injective in every degree on every space**: the
  coefficient inclusion `ULift ℚ → ULift ℂ` admits an additive retraction (a
  choice of ℚ-linear projection `ℂ → ℚ`), functors preserve retractions, and
  `Sheaf.H.map` is functorial.  Consequence: the recon §4(c) fork-closing
  target (nonvanishing of the ℂ-image of the Betti edge class) is
  **equivalent** to the rational nonvanishing — no parallel ℂ-coefficient
  Mayer–Vietoris tower and no δ-naturality-in-coefficients argument is needed.

**PARKED (the H¹ wall, Leg B), with exact residual spellings.**
* `AnalyticChartOneVanishingV0` / `AnalyticChartOneVanishingV1` — the named
  unproved `Prop`s `Subsingleton (Ext (freeYonedaSheaf JAn V0/V1) FqAn 1)`:
  degree-1 constant-sheaf cohomology vanishing on the analytic chart opens
  (classically `V0 ≅ ℂ` is contractible; the recon's Leg B, priced 3–5u via a
  probe-gated Čech–Goursat correction, or as a corollary of the singular
  subdivision campaign).  Stated, never proved, never assumed; consumed only
  as the explicit hypotheses of the conditional theorems below.

**CONDITIONAL on exactly those two receipts (Leg C, assembly proved).**
* `edgeTwoRaw_ne_zero_of_receipts`, `bettiEdgeClass_ne_zero_of_receipts`,
  `bettiEdgeNonvanishing_of_receipts` — the outer-edge squeeze (the
  `InterferenceProof.subsingleton_hPrimeOne_sup` idiom transposed) and the
  `≃+`-transport up the re-anchor tower: given the two parked receipts,
  `PredicateAcceptance.BettiEdgeNonvanishing` holds at its literal spelling.
* `toComplexCoeffs_bettiEdge_ne_zero_of_receipts` — the **fork-closing form**:
  given the same two receipts, the ℂ-image
  `toComplexCoeffs (TopCat.of (SPoints structMor)) 2 bettiEdgeClass` is
  nonzero (via `toComplexCoeffs_injective`; this is the exact hypothesis shape
  whose *negation* governs the degenerate branch of the 2πi fork).

## What is and is not proved (entitlement, in full)

PROVED, unconditional: `edgeOne ≠ 0` (Leg A complete); injectivity of the
constructed coefficient-change `toComplexCoeffs X n` for every `X`, `n`; the
restriction receipts, separation functional, exactness routing and re-anchor
below; preconnectedness of the slit opens and the constructed points of the
half-plane components.  PROVED, conditional on the two parked receipts: the
outer-edge nonvanishing, `BettiEdgeNonvanishing`, and the nonvanishing of the
ℂ-image of `bettiEdgeClass`.  NOT PROVED, NOT CLAIMED: either parked receipt
(the H¹ wall itself); any computation of any `Sheaf.H`/`Sheaf.H'` group of any
carrier (no `H⁰(W0) ≅ ℚ`-style identification is stated — only evaluation
*data* constructed from local constancy); any comparison between the
constant-sheaf carriers and singular cohomology (*Betti* is, as everywhere in
this project, a gloss for sheaf cohomology of the constant sheaf, never
singular cohomology); anything about the parked junction evaluation or the
2πi-fork normalization (this module does not import, consume, or restate any
junction spelling).  No claim that any constructed map is an isomorphism
beyond the proven `≃+`s cited from shipped modules.  Nothing here makes the
Hodge conjecture statable.

## Credits

The Mayer–Vietoris square, its `δ`/`toBiprod`/`fromBiprod`, `sequence_exact`,
`Sheaf.H`/`Sheaf.H'`, `Sheaf.H.map` and the `Ext` infrastructure are Joël
Riou's; sheafification, its adjunction unit and the local
surjectivity/injectivity of `toSheafify` are Mathlib's sites library; the
analytic edge construction (`W0/W1/AUp/BLo`, `mixSection`, `mixGlued`,
`edgeOne`, `bettiEdgeClass`) is `HodgePilot.PredicateAcceptance`; the slit
opens are `Complex.slitPlane` and its mirror (star-convexity from Mathlib);
the ℂ-points/localization plumbing is `HodgePilot.Analytic` /
`HodgePilot.AnalyticGlue`; the overlap ring, `awayNum`/`awayNumInv` and the
`Away` generation theorem are wave 1 / `HodgePilot.ProjectiveLineUnits` /
Jujian Zhang's and the 2025 Proj cluster's Mathlib work; the degree-0-sections
and re-anchor layer are `HodgePilot.ProjectiveLineGraded` /
`HodgePilot.CycCarrier`; the exactness-and-sections idiom transposed here is
`HodgePilot.InterferenceProof`; the coefficient carriers are
`HodgePilot.Betti`.
-/


-- @@ L94-94 verbatim
set_option maxHeartbeats 1000000

-- @@ L95-95 verbatim
set_option synthInstance.maxHeartbeats 1000000


-- @@ L97-97 verbatim
noncomputable section


-- @@ L99-99 verbatim
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

-- @@ L100-100 verbatim
open CategoryTheory.Abelian AlgebraicGeometry HomogeneousLocalization


-- @@ L102-102 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L104-104 verbatim
namespace HodgePilot


-- @@ L106-106 verbatim
namespace AnalyticWallA


-- @@ L108-108 verbatim
open HodgePilot.Betti HodgePilot.PredicateAcceptance

-- @@ L109-109 verbatim
open HodgePilot.ProjectiveLineGraded HodgePilot.ProjectiveLine

-- @@ L110-110 verbatim
open HodgePilot.ProjectiveLineUnits HodgePilot.Analytic


-- @@ L112-113 verbatim
/-- The standard grading of `ℂ[X₀, X₁]` by total degree. -/
local notation "𝒜₂" => MvPolynomial.homogeneousSubmodule (Fin 2) ℂ


-- @@ L115-117 verbatim
/-- The overlap localizing element `X₀X₁`. -/
local notation "X01" =>
  (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ)


-- @@ L119-122 verbatim
/-! ## 1. The sub-open lattice of the double overlap

The two half-plane components `AUp`, `BLo` sit below the double overlap
`W0 ⊓ W1 = AUp ⊔ BLo` (`W0_inf_W1`), hence below each slit open `W0`, `W1`. -/


-- @@ L124-124 verbatim
section Lattice


-- @@ L126-127 verbatim
/-- The upper component lies in the double overlap. -/
theorem aUp_le_infW : AUp ≤ W0 ⊓ W1 := le_of_le_of_eq le_sup_left W0_inf_W1.symm


-- @@ L129-130 verbatim
/-- The lower component lies in the double overlap. -/
theorem bLo_le_infW : BLo ≤ W0 ⊓ W1 := le_of_le_of_eq le_sup_right W0_inf_W1.symm


-- @@ L132-132 verbatim
theorem aUp_le_W0 : AUp ≤ W0 := aUp_le_infW.trans inf_le_left

-- @@ L133-133 verbatim
theorem aUp_le_W1 : AUp ≤ W1 := aUp_le_infW.trans inf_le_right

-- @@ L134-134 verbatim
theorem bLo_le_W0 : BLo ≤ W0 := bLo_le_infW.trans inf_le_left

-- @@ L135-135 verbatim
theorem bLo_le_W1 : BLo ≤ W1 := bLo_le_infW.trans inf_le_right


-- @@ L137-137 verbatim
end Lattice


-- @@ L139-143 verbatim
/-! ## 2. Restriction-composition on the constant sheaf

`FqAn.obj.map` of a composite `homOfLE` is the composite restriction; the
component arrows are unique in the preorder site, so any two nested restrictions
collapse to the direct one. -/


-- @@ L145-145 verbatim
section ResComp


-- @@ L147-155 verbatim
/-- Nested restrictions of the constant sheaf compose to the direct
restriction (the arrows agree by `Subsingleton.elim` in the preorder site). -/
theorem res_comp {A B D : Opens ↑anP1} (h1 : A ≤ B) (h2 : B ≤ D)
    (x : FqAn.obj.obj (op D)) :
    FqAn.obj.map (homOfLE h1).op (FqAn.obj.map (homOfLE h2).op x) =
      FqAn.obj.map (homOfLE (h1.trans h2)).op x := by
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp, ← op_comp]
  exact congrArg (fun (a : op D ⟶ op A) => FqAn.obj.map a x)
    (congrArg Quiver.Hom.op (Subsingleton.elim _ _))


-- @@ L157-157 verbatim
end ResComp


-- @@ L159-163 verbatim
/-! ## 3. The mixed section restricts to `1` on `AUp` and `0` on `BLo`

`mixSection` is the restriction of the glued datum `mixGlued`; the shipped
receipts `mixGlued_restrict_left/right` pin those restrictions to
`mixLeft = constOne AUp` and `mixRight = 0`. -/


-- @@ L165-165 verbatim
section MixRestrict


-- @@ L167-176 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The mixed section restricts to the constant `1` on the upper component. -/
theorem mixSection_res_AUp :
    FqAn.obj.map (homOfLE aUp_le_infW).op mixSection = constOne AUp := by
  show FqAn.obj.map (homOfLE aUp_le_infW).op
      (FqAn.obj.map (homOfLE (le_of_eq W0_inf_W1)).op mixGlued) = constOne AUp
  rw [res_comp aUp_le_infW (le_of_eq W0_inf_W1) mixGlued,
    Subsingleton.elim (homOfLE (aUp_le_infW.trans (le_of_eq W0_inf_W1)))
      ((Opens.mayerVietorisSquare AUp BLo).f₂₄)]
  exact mixGlued_restrict_left


-- @@ L178-187 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The mixed section restricts to `0` on the lower component. -/
theorem mixSection_res_BLo :
    FqAn.obj.map (homOfLE bLo_le_infW).op mixSection = 0 := by
  show FqAn.obj.map (homOfLE bLo_le_infW).op
      (FqAn.obj.map (homOfLE (le_of_eq W0_inf_W1)).op mixGlued) = 0
  rw [res_comp bLo_le_infW (le_of_eq W0_inf_W1) mixGlued,
    Subsingleton.elim (homOfLE (bLo_le_infW.trans (le_of_eq W0_inf_W1)))
      ((Opens.mayerVietorisSquare AUp BLo).f₃₄)]
  exact mixGlued_restrict_right


-- @@ L189-189 verbatim
end MixRestrict


-- @@ L191-195 verbatim
/-! ## 4. The wall interface: component-evaluation data + connectedness

`WallInput` packages the connectedness content of Leg A; §§9–12 below
construct the instance, and everything in §§5–8 is proved against the
interface. -/


-- @@ L197-216 verbatim
/-- **The Leg-A wall interface.**  `valA`/`valB` evaluate a section of the
constant sheaf over the components `AUp`/`BLo` at a rational value;
`valA_constOne` reads the constant-`1` section; `compat_W0`/`compat_W1` are the
connectedness compatibilities: a section over the connected slit open `W0`
(resp. `W1`) produces the same value on `AUp` and on `BLo`. -/
structure WallInput where
  /-- Component evaluation on the upper half-plane component. -/
  valA : (FqAn.obj.obj (op AUp)) →+ ℚ
  /-- Component evaluation on the lower half-plane component. -/
  valB : (FqAn.obj.obj (op BLo)) →+ ℚ
  /-- The constant-`1` section evaluates to `1`. -/
  valA_constOne : valA (constOne AUp) = 1
  /-- Connectedness over `W0`: one value on both components. -/
  compat_W0 : ∀ s : FqAn.obj.obj (op W0),
    valA (FqAn.obj.map (homOfLE aUp_le_W0).op s) =
      valB (FqAn.obj.map (homOfLE bLo_le_W0).op s)
  /-- Connectedness over `W1`: one value on both components. -/
  compat_W1 : ∀ s : FqAn.obj.obj (op W1),
    valA (FqAn.obj.map (homOfLE aUp_le_W1).op s) =
      valB (FqAn.obj.map (homOfLE bLo_le_W1).op s)


-- @@ L218-218 verbatim
/-! ## 5. The separation functional and its two receipts -/


-- @@ L220-220 verbatim
section Separation


-- @@ L222-222 verbatim
variable (W : WallInput)


-- @@ L224-227 verbatim
/-- The restriction of the constant sheaf as a bare additive hom. -/
def resHom {A B : Opens ↑anP1} (h : A ≤ B) :
    (FqAn.obj.obj (op B)) →+ (FqAn.obj.obj (op A)) :=
  (FqAn.obj.map (homOfLE h).op).hom


-- @@ L229-231 verbatim
@[simp] theorem resHom_apply {A B : Opens ↑anP1} (h : A ≤ B)
    (x : FqAn.obj.obj (op B)) :
    resHom h x = FqAn.obj.map (homOfLE h).op x := rfl


-- @@ L233-236 verbatim
/-- **The separation functional** `Γ(W0 ⊓ W1) →+ ℚ`: the difference of the two
component evaluations. -/
def sepFun : (FqAn.obj.obj (op (W0 ⊓ W1))) →+ ℚ :=
  W.valA.comp (resHom aUp_le_infW) - W.valB.comp (resHom bLo_le_infW)


-- @@ L238-241 verbatim
theorem sepFun_apply (x : FqAn.obj.obj (op (W0 ⊓ W1))) :
    sepFun W x =
      W.valA (FqAn.obj.map (homOfLE aUp_le_infW).op x) -
        W.valB (FqAn.obj.map (homOfLE bLo_le_infW).op x) := rfl


-- @@ L243-246 verbatim
/-- **Receipt (a): the functional detects the mixed section.** -/
theorem sepFun_mixSection : sepFun W mixSection = 1 := by
  rw [sepFun_apply, mixSection_res_AUp, mixSection_res_BLo, W.valA_constOne,
    map_zero, sub_zero]


-- @@ L248-257 verbatim
/-- **Receipt (b₀): the functional kills a restriction from the connected
`W0`.** -/
theorem sepFun_res_W0 (s : FqAn.obj.obj (op W0)) :
    sepFun W (FqAn.obj.map (homOfLE (inf_le_left : W0 ⊓ W1 ≤ W0)).op s) = 0 := by
  rw [sepFun_apply,
    res_comp aUp_le_infW (inf_le_left : W0 ⊓ W1 ≤ W0) s,
    res_comp bLo_le_infW (inf_le_left : W0 ⊓ W1 ≤ W0) s,
    Subsingleton.elim (aUp_le_infW.trans inf_le_left) aUp_le_W0,
    Subsingleton.elim (bLo_le_infW.trans inf_le_left) bLo_le_W0,
    W.compat_W0 s, sub_self]


-- @@ L259-268 verbatim
/-- **Receipt (b₁): the functional kills a restriction from the connected
`W1`.** -/
theorem sepFun_res_W1 (s : FqAn.obj.obj (op W1)) :
    sepFun W (FqAn.obj.map (homOfLE (inf_le_right : W0 ⊓ W1 ≤ W1)).op s) = 0 := by
  rw [sepFun_apply,
    res_comp aUp_le_infW (inf_le_right : W0 ⊓ W1 ≤ W1) s,
    res_comp bLo_le_infW (inf_le_right : W0 ⊓ W1 ≤ W1) s,
    Subsingleton.elim (aUp_le_infW.trans inf_le_right) aUp_le_W1,
    Subsingleton.elim (bLo_le_infW.trans inf_le_right) bLo_le_W1,
    W.compat_W1 s, sub_self]


-- @@ L270-270 verbatim
end Separation


-- @@ L272-277 verbatim
/-! ## 6. `mixH0` is not in the image of `fromBiprod` (the H⁰ core)

Reading `fromBiprod` through the degree-0-sections identification
`h0SectionsEquiv` (mirroring `InterferenceProof.fromBiprodO_surjective`), any
class in its image has section-form `res s0 - res s1`; the separation functional
sends that to `0` but sends `mixSection` (i.e. `mixH0`) to `1`. -/


-- @@ L279-279 verbatim
section H0Core


-- @@ L281-289 verbatim
/-- Naturality of the H⁰-sections identification against a `cohomologyPresheaf`
restriction map (repackaging `h0ToSections_natural` + `cohomologyPresheaf_map_eq`
into `h0SectionsEquiv` form). -/
theorem h0SE_res {V U : Opens ↑anP1} (i : V ⟶ U)
    (a : Ext (freeYonedaSheaf JAn U) FqAn 0) :
    h0SectionsEquiv FqAn V ((FqAn.cohomologyPresheaf 0).map i.op a) =
      FqAn.obj.map i.op (h0SectionsEquiv FqAn U a) := by
  rw [h0SectionsEquiv_apply, h0SectionsEquiv_apply, cohomologyPresheaf_map_eq]
  exact (h0ToSections_natural FqAn i a).symm


-- @@ L291-323 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **The H⁰ core**: the mixed class is not the `fromBiprod`-image of any biprod
element — the separation functional kills the whole image but sends `mixH0`
(i.e. `mixSection`) to `1`. -/
theorem mixH0_not_mem_range (W : WallInput) :
    ¬ ∃ b, (Opens.mayerVietorisSquare W0 W1).fromBiprod FqAn 0 b = mixH0 := by
  rintro ⟨b, hb⟩
  have hmix : h0SectionsEquiv FqAn (Opens.mayerVietorisSquare W0 W1).X₁ mixH0 =
      mixSection :=
    (h0SectionsEquiv FqAn (Opens.mayerVietorisSquare W0 W1).X₁).apply_symm_apply
      mixSection
  obtain ⟨⟨a0, a1⟩, rfl⟩ :=
    (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.symm.surjective b
  rw [Iso.addCommGroupIsoToAddEquiv_symm_apply,
    (Opens.mayerVietorisSquare W0 W1).fromBiprod_biprodIsoProd_inv_apply FqAn a0 a1]
    at hb
  have hL : sepFun W (h0SectionsEquiv FqAn (Opens.mayerVietorisSquare W0 W1).X₁
      ((FqAn.cohomologyPresheaf 0).map
        (Opens.mayerVietorisSquare W0 W1).f₁₂.op a0)) = 0 := by
    rw [h0SE_res]
    exact sepFun_res_W0 W
      (h0SectionsEquiv FqAn (Opens.mayerVietorisSquare W0 W1).X₂ a0)
  have hR : sepFun W (h0SectionsEquiv FqAn (Opens.mayerVietorisSquare W0 W1).X₁
      ((FqAn.cohomologyPresheaf 0).map
        (Opens.mayerVietorisSquare W0 W1).f₁₃.op a1)) = 0 := by
    rw [h0SE_res]
    exact sepFun_res_W1 W
      (h0SectionsEquiv FqAn (Opens.mayerVietorisSquare W0 W1).X₃ a1)
  have hsec := congrArg (h0SectionsEquiv FqAn (Opens.mayerVietorisSquare W0 W1).X₁) hb
  rw [map_sub, hmix] at hsec
  have hval := congrArg (sepFun W) hsec
  rw [map_sub, hL, hR, sub_zero, sepFun_mixSection] at hval
  exact one_ne_zero hval.symm


-- @@ L325-325 verbatim
end H0Core


-- @@ L327-331 verbatim
/-! ## 7. Exactness routing: `edgeOneRaw ≠ 0`

The transpose of `InterferenceProof.subsingleton_hPrimeOne_sup`: at the H⁰ node
(`.exact 1`) of Riou's Mayer–Vietoris sequence, `ker δ = im fromBiprod`, so a
class outside the image is not killed by `δ`. -/


-- @@ L333-333 verbatim
section Raw


-- @@ L335-343 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **The inner (raw) edge is nonzero.**  `edgeOneRaw = δ(mixH0)`, and `mixH0`
is not in `im fromBiprod`, so by exactness at the H⁰ node it is not in `ker δ`. -/
theorem edgeOneRaw_ne_zero (W : WallInput) : edgeOneRaw ≠ 0 := by
  intro h0
  have hδ : (Opens.mayerVietorisSquare W0 W1).δ FqAn 0 1 rfl mixH0 = 0 := h0
  have hex := ((Opens.mayerVietorisSquare W0 W1).sequence_exact FqAn 0 1 rfl).exact 1
  obtain ⟨b, hb⟩ := (ShortComplex.ab_exact_iff _).mp hex mixH0 hδ
  exact mixH0_not_mem_range W ⟨b, hb⟩


-- @@ L345-345 verbatim
end Raw


-- @@ L347-350 verbatim
/-! ## 8. The re-anchor: `edgeOne ≠ 0` from a wall input

`edgeOne = extReanchorLeft (eqToIso …) 1 edgeOneRaw` is the image of `edgeOneRaw`
under an `AddEquiv`, which is injective and sends `0` to `0`. -/


-- @@ L352-352 verbatim
section Reanchor


-- @@ L354-365 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **Leg A, conditional form**: given the connectedness data, the analytic
inner (H⁰) edge class is nonzero. -/
theorem edgeOne_ne_zero_of_wallInput (W : WallInput) :
    PredicateAcceptance.edgeOne ≠ 0 := by
  intro h
  apply edgeOneRaw_ne_zero W
  have he : (CycCarrier.extReanchorLeft (Y := FqAn)
      (eqToIso (congrArg (freeYonedaSheaf JAn) W0_sup_W1)) 1) edgeOneRaw = 0 := h
  have hz := congrArg (CycCarrier.extReanchorLeft (Y := FqAn)
      (eqToIso (congrArg (freeYonedaSheaf JAn) W0_sup_W1)) 1).symm he
  rwa [AddEquiv.symm_apply_apply, map_zero] at hz


-- @@ L367-367 verbatim
end Reanchor


-- @@ L369-376 verbatim
/-! ## 9. Points of the half-plane components

Characters of the overlap chart ring `(ℂ[X₀,X₁]_{X₀X₁})₀` at a nonzero
coordinate value `z`: evaluate `ℂ[X₀,X₁]` at `(1, z)`, lift to the localization
away from `X₀X₁` (`AnalyticGlue.awayLift`), and restrict along the
degree-zero-inclusion algebra map.  Every ℂ-point of the overlap ring arises
this way (`realizePt_evCoord`), which transports connectedness of the slit
regions of `ℂ` to the slit opens of the analytic point-space. -/


-- @@ L378-378 verbatim
section OverlapPoints


-- @@ L380-382 verbatim
/-- The base character of `ℂ[X₀,X₁]` at the affine point `(1, z)`. -/
def basePt (w : {z : ℂ // z ≠ 0}) : CPoints (MvPolynomial (Fin 2) ℂ) :=
  MvPolynomial.aeval ![1, w.1]


-- @@ L384-387 verbatim
theorem basePt_X01 (w : {z : ℂ // z ≠ 0}) : basePt w (X01) = w.1 := by
  show MvPolynomial.aeval ![1, w.1] (X01) = w.1
  rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_zero, one_mul]


-- @@ L389-390 verbatim
theorem basePt_X01_ne_zero (w : {z : ℂ // z ≠ 0}) : basePt w (X01) ≠ 0 := by
  rw [basePt_X01]; exact w.2


-- @@ L392-395 verbatim
theorem basePt_X1_sq (w : {z : ℂ // z ≠ 0}) :
    basePt w (MvPolynomial.X 1 * MvPolynomial.X 1) = w.1 * w.1 := by
  show MvPolynomial.aeval ![1, w.1] (MvPolynomial.X 1 * MvPolynomial.X 1) = _
  rw [map_mul, MvPolynomial.aeval_X, Matrix.cons_val_one, Matrix.cons_val_zero]


-- @@ L397-400 verbatim
theorem basePt_X0_sq (w : {z : ℂ // z ≠ 0}) :
    basePt w (MvPolynomial.X 0 * MvPolynomial.X 0) = 1 := by
  show MvPolynomial.aeval ![1, w.1] (MvPolynomial.X 0 * MvPolynomial.X 0) = 1
  rw [map_mul, MvPolynomial.aeval_X, Matrix.cons_val_zero, one_mul]


-- @@ L402-418 verbatim
/-- The degree-zero part of the localization includes into the full
localization, as a `ℂ`-algebra map (underlying ring map: the canonical
`algebraMap`, i.e. `val`). -/
def valAlgHom : Away 𝒜₂ (X01) →ₐ[ℂ] Localization.Away (X01) :=
  { algebraMap (Away 𝒜₂ (X01)) (Localization.Away (X01)) with
    commutes' := fun c => by
      have hval : (algebraMap ℂ (Away 𝒜₂ (X01)) c).val =
          algebraMap (MvPolynomial (Fin 2) ℂ) (Localization.Away (X01))
            (MvPolynomial.C c) := by
        rw [algebraMap_away_apply]
        show Localization.mk _ 1 = _
        rw [Localization.mk_one_eq_algebraMap, SetLike.GradeZero.coe_algebraMap,
          MvPolynomial.algebraMap_eq]
      show algebraMap (Away 𝒜₂ (X01)) (Localization.Away (X01))
          (algebraMap ℂ (Away 𝒜₂ (X01)) c) = algebraMap ℂ (Localization.Away (X01)) c
      rw [HomogeneousLocalization.algebraMap_apply, hval, ← MvPolynomial.algebraMap_eq,
        ← IsScalarTower.algebraMap_apply] }


-- @@ L420-421 verbatim
theorem valAlgHom_apply (x : Away 𝒜₂ (X01)) : valAlgHom x = x.val :=
  HomogeneousLocalization.algebraMap_apply x


-- @@ L423-428 verbatim
/-- **The point realization**: the character of the overlap chart ring at the
nonzero coordinate value `w`. -/
def realizePt (w : {z : ℂ // z ≠ 0}) : CPoints (Away 𝒜₂ (X01)) :=
  Analytic.comap valAlgHom
    (Analytic.awayLift (X01) (Localization.Away (X01)) (basePt w)
      (basePt_X01_ne_zero w))


-- @@ L430-436 verbatim
theorem realizePt_apply (w : {z : ℂ // z ≠ 0}) (x : Away 𝒜₂ (X01)) :
    realizePt w x =
      Analytic.awayLift (X01) (Localization.Away (X01)) (basePt w)
        (basePt_X01_ne_zero w) x.val := by
  show Analytic.awayLift (X01) (Localization.Away (X01)) (basePt w)
      (basePt_X01_ne_zero w) (valAlgHom x) = _
  rw [valAlgHom_apply]


-- @@ L438-459 verbatim
/-- The realized point has coordinate value `w`. -/
theorem realizePt_awayNum (w : {z : ℂ // z ≠ 0}) : realizePt w awayNum = w.1 := by
  have hval : awayNum.val =
      Localization.mk (MvPolynomial.X 1 * MvPolynomial.X 1)
        (⟨(X01) ^ 1, 1, rfl⟩ : Submonoid.powers (X01)) := by
    unfold ProjectiveLine.awayNum
    rw [HomogeneousLocalization.Away.val_mk]
  have hspec := congrArg
    (Analytic.awayLift (X01) (Localization.Away (X01)) (basePt w)
      (basePt_X01_ne_zero w))
    (IsLocalization.mk'_spec (Localization.Away (X01))
      (MvPolynomial.X 1 * MvPolynomial.X 1)
      (⟨(X01) ^ 1, 1, rfl⟩ : Submonoid.powers (X01)))
  rw [map_mul, Analytic.awayLift_algebraMap, Analytic.awayLift_algebraMap] at hspec
  have hpow : basePt w
      (((⟨(X01) ^ 1, 1, rfl⟩ : Submonoid.powers (X01)) : Submonoid.powers (X01)) :
        MvPolynomial (Fin 2) ℂ) = w.1 := by
    show basePt w ((X01) ^ 1) = w.1
    rw [pow_one, basePt_X01]
  rw [hpow, basePt_X1_sq] at hspec
  rw [realizePt_apply, hval, Localization.mk_eq_mk'_apply]
  exact mul_right_cancel₀ w.2 hspec


-- @@ L461-483 verbatim
/-- The realized point inverts the coordinate on the inverse fraction. -/
theorem realizePt_awayNumInv (w : {z : ℂ // z ≠ 0}) :
    realizePt w awayNumInv = (w.1)⁻¹ := by
  have hval : awayNumInv.val =
      Localization.mk (MvPolynomial.X 0 * MvPolynomial.X 0)
        (⟨(X01) ^ 1, 1, rfl⟩ : Submonoid.powers (X01)) := by
    unfold ProjectiveLine.awayNumInv
    rw [HomogeneousLocalization.Away.val_mk]
  have hspec := congrArg
    (Analytic.awayLift (X01) (Localization.Away (X01)) (basePt w)
      (basePt_X01_ne_zero w))
    (IsLocalization.mk'_spec (Localization.Away (X01))
      (MvPolynomial.X 0 * MvPolynomial.X 0)
      (⟨(X01) ^ 1, 1, rfl⟩ : Submonoid.powers (X01)))
  rw [map_mul, Analytic.awayLift_algebraMap, Analytic.awayLift_algebraMap] at hspec
  have hpow : basePt w
      (((⟨(X01) ^ 1, 1, rfl⟩ : Submonoid.powers (X01)) : Submonoid.powers (X01)) :
        MvPolynomial (Fin 2) ℂ) = w.1 := by
    show basePt w ((X01) ^ 1) = w.1
    rw [pow_one, basePt_X01]
  rw [hpow, basePt_X0_sq] at hspec
  rw [realizePt_apply, hval, Localization.mk_eq_mk'_apply]
  exact eq_inv_of_mul_eq_one_left hspec


-- @@ L485-518 verbatim
set_option maxHeartbeats 4000000 in
/-- The point realization is continuous (rides `AnalyticGlue`'s
`continuous_awayLift` and `continuous_comap`). -/
theorem continuous_realizePt : Continuous realizePt := by
  have hcons : Continuous fun w : {z : ℂ // z ≠ 0} => (![1, w.1] : Fin 2 → ℂ) := by
    refine continuous_pi fun i => ?_
    refine Fin.cases ?_ (fun j => ?_) i
    · have h : (fun w : {z : ℂ // z ≠ 0} => (![1, w.1] : Fin 2 → ℂ) 0) =
          fun _ => (1 : ℂ) := by
        funext w; rw [Matrix.cons_val_zero]
      rw [h]; exact continuous_const
    · have h : (fun w : {z : ℂ // z ≠ 0} => (![1, w.1] : Fin 2 → ℂ) j.succ) =
          fun w => w.1 := by
        funext w; rw [Matrix.cons_val_succ, Matrix.cons_val_fin_one]
      rw [h]; exact continuous_subtype_val
  have hbase : Continuous fun w : {z : ℂ // z ≠ 0} => basePt w := by
    refine continuous_induced_rng.2 ?_
    have h2 : (Analytic.toPi (MvPolynomial (Fin 2) ℂ) ∘
        fun w : {z : ℂ // z ≠ 0} => basePt w) =
        fun w : {z : ℂ // z ≠ 0} => fun p => MvPolynomial.eval ![1, w.1] p := by
      funext w p
      show MvPolynomial.aeval ![1, w.1] p = MvPolynomial.eval ![1, w.1] p
      rw [MvPolynomial.aeval_def, Algebra.algebraMap_self, MvPolynomial.eval₂_id]
    rw [h2]
    exact continuous_pi fun p => (MvPolynomial.continuous_eval p).comp hcons
  have hmk : Continuous fun w : {z : ℂ // z ≠ 0} =>
      (⟨basePt w, basePt_X01_ne_zero w⟩ :
        {φ : CPoints (MvPolynomial (Fin 2) ℂ) // φ (X01) ≠ 0}) :=
    Continuous.subtype_mk hbase _
  have hlift : Continuous fun w : {z : ℂ // z ≠ 0} =>
      Analytic.awayLift (X01) (Localization.Away (X01)) (basePt w)
        (basePt_X01_ne_zero w) :=
    (Analytic.continuous_awayLift (X01) (Localization.Away (X01))).comp hmk
  exact (Analytic.continuous_comap valAlgHom).comp hlift


-- @@ L520-621 verbatim
/-- The overlap chart ring is generated over `ℂ` by the coordinate fraction and
its inverse (the pin's `Away` generation theorem, the
`InterferenceProof.overlapAlgHom_surjective` case analysis re-keyed to
membership). -/
theorem adjoin_away_units :
    Algebra.adjoin ℂ (Set.range ![awayNum, awayNumInv]) = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  have htop := HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top
    (𝒜 := 𝒜₂) hX01 (Fin 2) MvPolynomial.X adjoin_range_X_eq_top
    (fun _ => 1) (fun k => X_mem_grade_one k)
  have hx := htop.ge (Algebra.mem_top (x := x))
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨a, ai, hai, hle, rfl⟩ := hy
    have h3 : ai 0 + ai 1 = a * 2 := by
      simpa [Fin.sum_univ_two, smul_eq_mul, mul_comm] using hai
    have hle0 : ai 0 ≤ 2 := hle 0
    have hle1 : ai 1 ≤ 2 := hle 1
    have ha2 : a ≤ 2 := by omega
    have hprod : (∏ i, MvPolynomial.X i ^ ai i : MvPolynomial (Fin 2) ℂ) =
        MvPolynomial.X 0 ^ ai 0 * MvPolynomial.X 1 ^ ai 1 :=
      Fin.prod_univ_two _
    interval_cases a
    · -- a = 0 : the generator is 1
      have hk0 : ai 0 = 0 := by omega
      have hk1 : ai 1 = 0 := by omega
      have hgen : ∀ prf, HomogeneousLocalization.Away.mk 𝒜₂ hX01 0
          (∏ i, MvPolynomial.X i ^ ai i) prf = 1 := by
        intro prf
        apply HomogeneousLocalization.val_injective
        rw [HomogeneousLocalization.val_one, HomogeneousLocalization.Away.val_mk,
          ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
        use 1
        simp only [OneMemClass.coe_one, one_mul, hprod, hk0, hk1, pow_zero]
        try ring
      rw [hgen _]
      exact Subalgebra.one_mem _
    · -- a = 1 : the generator is awayNum, 1 or awayNumInv
      have hk : ai 0 = 0 ∨ ai 0 = 1 ∨ ai 0 = 2 := by omega
      rcases hk with hk0 | hk0 | hk0
      · have hk1 : ai 1 = 2 := by omega
        have hgen : ∀ prf, HomogeneousLocalization.Away.mk 𝒜₂ hX01 1
            (∏ i, MvPolynomial.X i ^ ai i) prf = awayNum := by
          intro prf
          apply HomogeneousLocalization.val_injective
          unfold ProjectiveLine.awayNum
          rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
            Localization.mk_eq_mk_iff, Localization.r_iff_exists]
          use 1
          simp only [OneMemClass.coe_one, one_mul, hprod, hk0, hk1, pow_zero]
          try ring
        rw [hgen _]
        exact Algebra.subset_adjoin ⟨0, rfl⟩
      · have hk1 : ai 1 = 1 := by omega
        have hgen : ∀ prf, HomogeneousLocalization.Away.mk 𝒜₂ hX01 1
            (∏ i, MvPolynomial.X i ^ ai i) prf = 1 := by
          intro prf
          apply HomogeneousLocalization.val_injective
          rw [HomogeneousLocalization.val_one, HomogeneousLocalization.Away.val_mk,
            ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
          use 1
          simp only [OneMemClass.coe_one, one_mul, hprod, hk0, hk1, pow_one]
          try ring
        rw [hgen _]
        exact Subalgebra.one_mem _
      · have hk1 : ai 1 = 0 := by omega
        have hgen : ∀ prf, HomogeneousLocalization.Away.mk 𝒜₂ hX01 1
            (∏ i, MvPolynomial.X i ^ ai i) prf = awayNumInv := by
          intro prf
          apply HomogeneousLocalization.val_injective
          unfold ProjectiveLine.awayNumInv
          rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
            Localization.mk_eq_mk_iff, Localization.r_iff_exists]
          use 1
          simp only [OneMemClass.coe_one, one_mul, hprod, hk0, hk1, pow_zero]
          try ring
        rw [hgen _]
        exact Algebra.subset_adjoin ⟨1, rfl⟩
    · -- a = 2 : the generator is 1 again
      have hk0 : ai 0 = 2 := by omega
      have hk1 : ai 1 = 2 := by omega
      have hgen : ∀ prf, HomogeneousLocalization.Away.mk 𝒜₂ hX01 2
          (∏ i, MvPolynomial.X i ^ ai i) prf = 1 := by
        intro prf
        apply HomogeneousLocalization.val_injective
        rw [HomogeneousLocalization.val_one, HomogeneousLocalization.Away.val_mk,
          ← Localization.mk_one, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
        use 1
        simp only [OneMemClass.coe_one, one_mul, hprod, hk0, hk1]
        try ring
      rw [hgen _]
      exact Subalgebra.one_mem _
  | algebraMap r =>
    obtain ⟨c, rfl⟩ := gradeZero_algebraMap_bijective.2 r
    have hc : algebraMap (𝒜₂ 0) (Away 𝒜₂ (X01)) (algebraMap ℂ (𝒜₂ 0) c) =
        algebraMap ℂ (Away 𝒜₂ (X01)) c :=
      (IsScalarTower.algebraMap_apply ℂ (𝒜₂ 0) (Away 𝒜₂ (X01)) c).symm
    rw [hc]
    exact Subalgebra.algebraMap_mem _ c
  | add y w _ _ hy hw => exact Subalgebra.add_mem _ hy hw
  | mul y w _ _ hy hw => exact Subalgebra.mul_mem _ hy hw


-- @@ L623-641 verbatim
/-- **Determination**: every ℂ-point of the overlap chart ring is the
realization of its own coordinate value. -/
theorem realizePt_evCoord (φ : CPoints (Away 𝒜₂ (X01))) :
    realizePt ⟨evCoord φ, evCoord_ne_zero φ⟩ = φ := by
  apply Analytic.injective_evalGen ![awayNum, awayNumInv] adjoin_away_units
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · show realizePt ⟨evCoord φ, evCoord_ne_zero φ⟩
        ((![awayNum, awayNumInv] : Fin 2 → _) 0) =
      φ ((![awayNum, awayNumInv] : Fin 2 → _) 0)
    rw [Matrix.cons_val_zero, realizePt_awayNum]
    rfl
  · show realizePt ⟨evCoord φ, evCoord_ne_zero φ⟩
        ((![awayNum, awayNumInv] : Fin 2 → _) j.succ) =
      φ ((![awayNum, awayNumInv] : Fin 2 → _) j.succ)
    rw [Matrix.cons_val_succ, Matrix.cons_val_fin_one, realizePt_awayNumInv]
    have hmul : φ awayNum * φ awayNumInv = 1 := by
      rw [← map_mul, awayNum_mul_awayNumInv, map_one]
    exact (eq_inv_of_mul_eq_one_right hmul).symm


-- @@ L643-645 verbatim
theorem evCoord_realizePt (w : {z : ℂ // z ≠ 0}) :
    evCoord (realizePt w) = w.1 :=
  realizePt_awayNum w


-- @@ L647-658 verbatim
/-- The coordinate preimage of any set of values is the realization image of
that set. -/
theorem preimage_evCoord_eq (S : Set ℂ) :
    evCoord ⁻¹' S = realizePt '' (Subtype.val ⁻¹' S) := by
  ext φ
  constructor
  · intro hφ
    exact ⟨⟨evCoord φ, evCoord_ne_zero φ⟩, hφ, realizePt_evCoord φ⟩
  · rintro ⟨w, hw, rfl⟩
    show evCoord (realizePt w) ∈ S
    rw [evCoord_realizePt]
    exact hw


-- @@ L660-660 verbatim
end OverlapPoints


-- @@ L662-662 verbatim
/-! ## 10. Preconnectedness of the slit opens, and the two component points -/


-- @@ L664-664 verbatim
section Connectivity


-- @@ L666-670 verbatim
/-- The first slit region is literally Mathlib's `Complex.slitPlane`. -/
theorem slit0_eq_slitPlane : slit0 = Complex.slitPlane := by
  ext z
  rw [Complex.mem_slitPlane_iff]
  exact Iff.rfl


-- @@ L672-677 verbatim
theorem isPreconnected_slit0 : IsPreconnected slit0 := by
  rw [slit0_eq_slitPlane]
  haveI : ContractibleSpace Complex.slitPlane :=
    Complex.starConvex_one_slitPlane.contractibleSpace
      ⟨1, by rw [Complex.mem_slitPlane_iff, Complex.one_re]; exact Or.inl one_pos⟩
  exact isPreconnected_iff_preconnectedSpace.mpr inferInstance


-- @@ L679-695 verbatim
/-- The second slit region is the negation image of the first. -/
theorem slit1_eq_neg_image : slit1 = (fun z : ℂ => -z) '' slit0 := by
  ext z
  constructor
  · intro hz
    refine ⟨-z, ?_, neg_neg z⟩
    rcases hz with h | h
    · exact Or.inl (show (0 : ℝ) < (-z).re by
        rw [Complex.neg_re]; exact neg_pos.mpr h)
    · exact Or.inr (show (-z).im ≠ 0 by
        rw [Complex.neg_im]; exact neg_ne_zero.mpr h)
  · rintro ⟨u, hu, rfl⟩
    rcases hu with h | h
    · exact Or.inl (show (-u).re < 0 by
        rw [Complex.neg_re]; exact neg_lt_zero.mpr h)
    · exact Or.inr (show (-u).im ≠ 0 by
        rw [Complex.neg_im]; exact neg_ne_zero.mpr h)


-- @@ L697-699 verbatim
theorem isPreconnected_slit1 : IsPreconnected slit1 := by
  rw [slit1_eq_neg_image]
  exact isPreconnected_slit0.image _ continuous_neg.continuousOn


-- @@ L701-706 verbatim
theorem slit0_subset : slit0 ⊆ {z : ℂ | z ≠ 0} := by
  rintro z (h | h) rfl
  · have h' : (0 : ℝ) < (0 : ℂ).re := h
    rw [Complex.zero_re] at h'
    exact lt_irrefl 0 h'
  · exact h Complex.zero_im


-- @@ L708-713 verbatim
theorem slit1_subset : slit1 ⊆ {z : ℂ | z ≠ 0} := by
  rintro z (h | h) rfl
  · have h' : ((0 : ℂ)).re < 0 := h
    rw [Complex.zero_re] at h'
    exact lt_irrefl 0 h'
  · exact h Complex.zero_im


-- @@ L715-733 verbatim
/-- Preconnectedness of the coordinate preimage of a preconnected set of
nonzero values. -/
theorem isPreconnected_preimage_evCoord {S : Set ℂ} (hS : IsPreconnected S)
    (hsub : S ⊆ {z : ℂ | z ≠ 0}) :
    IsPreconnected (evCoord ⁻¹' S) := by
  have h1 : IsPreconnected (Subtype.val ⁻¹' S : Set {z : ℂ // z ≠ 0}) := by
    have himg : Subtype.val '' (Subtype.val ⁻¹' S : Set {z : ℂ // z ≠ 0}) = S := by
      apply Set.Subset.antisymm
      · rintro y ⟨w, hw, rfl⟩
        exact hw
      · intro z hz
        exact ⟨⟨z, hsub hz⟩, hz, rfl⟩
    have hind : Topology.IsInducing (Subtype.val : {z : ℂ // z ≠ 0} → ℂ) :=
      Topology.IsInducing.subtypeVal
    refine hind.isPreconnected_image.mp ?_
    rw [himg]
    exact hS
  rw [preimage_evCoord_eq]
  exact h1.image _ continuous_realizePt.continuousOn


-- @@ L735-739 verbatim
/-- The first slit open of the analytic point-space is preconnected. -/
theorem isPreconnected_coe_W0 : IsPreconnected (W0 : Set ↑anP1) := by
  show IsPreconnected (prb '' (evCoord ⁻¹' slit0))
  exact (isPreconnected_preimage_evCoord isPreconnected_slit0 slit0_subset).image _
    prb_isOpenEmbedding.continuous.continuousOn


-- @@ L741-745 verbatim
/-- The second slit open of the analytic point-space is preconnected. -/
theorem isPreconnected_coe_W1 : IsPreconnected (W1 : Set ↑anP1) := by
  show IsPreconnected (prb '' (evCoord ⁻¹' slit1))
  exact (isPreconnected_preimage_evCoord isPreconnected_slit1 slit1_subset).image _
    prb_isOpenEmbedding.continuous.continuousOn


-- @@ L747-748 verbatim
/-- **The upper witness point**: the probe image of the character at `i`. -/
def upPt : ↑anP1 := prb (realizePt ⟨Complex.I, Complex.I_ne_zero⟩)


-- @@ L750-751 verbatim
/-- **The lower witness point**: the probe image of the character at `-i`. -/
def loPt : ↑anP1 := prb (realizePt ⟨-Complex.I, neg_ne_zero.mpr Complex.I_ne_zero⟩)


-- @@ L753-760 verbatim
theorem upPt_mem_AUp : upPt ∈ AUp := by
  show upPt ∈ prb '' (evCoord ⁻¹' upperSet)
  refine ⟨realizePt ⟨Complex.I, Complex.I_ne_zero⟩, ?_, rfl⟩
  show evCoord (realizePt ⟨Complex.I, Complex.I_ne_zero⟩) ∈ upperSet
  rw [evCoord_realizePt]
  show (0 : ℝ) < Complex.I.im
  rw [Complex.I_im]
  exact zero_lt_one


-- @@ L762-769 verbatim
theorem loPt_mem_BLo : loPt ∈ BLo := by
  show loPt ∈ prb '' (evCoord ⁻¹' lowerSet)
  refine ⟨realizePt ⟨-Complex.I, neg_ne_zero.mpr Complex.I_ne_zero⟩, ?_, rfl⟩
  show evCoord (realizePt ⟨-Complex.I, neg_ne_zero.mpr Complex.I_ne_zero⟩) ∈ lowerSet
  rw [evCoord_realizePt]
  show (-Complex.I).im < 0
  rw [Complex.neg_im, Complex.I_im]
  exact neg_lt_zero.mpr zero_lt_one


-- @@ L771-771 verbatim
end Connectivity


-- @@ L773-783 verbatim
/-! ## 11. The section-value layer

Every section of the sheafified constant presheaf is *locally* a unit-image
constant (the sheafification unit is locally surjective), and the local
constant is unique on nonempty opens (the unit is locally injective and the
constant presheaf has identity restrictions).  This produces, for each section
`s` over `U` and each point `x ∈ U`, a well-defined rational value
`secVal U s x hx`, additive in `s`, compatible with restriction, locally
constant in `x` — hence constant on preconnected opens.  **No identification
of any section group with `ℚ` (or with anything else) is stated or implied**:
this is evaluation *data* constructed from local constancy, nothing more. -/


-- @@ L785-785 verbatim
section SectionValues


-- @@ L787-790 verbatim
/-- The constant presheaf at `ULift ℚ` — the exact presheaf whose
sheafification is `FqAn` (the spelling inside `PredicateAcceptance.constOne`). -/
abbrev constPresheafQ : (Opens ↑anP1)ᵒᵖ ⥤ AddCommGrpCat.{0} :=
  (Functor.const (Opens ↑anP1)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{0} ℚ))


-- @@ L792-795 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The unit-image constant section with value `q` over `W`. -/
def constSec (q : ℚ) (W : Opens ↑anP1) : FqAn.obj.obj (op W) :=
  (toSheafify JAn constPresheafQ).app (op W) (ULift.up q)


-- @@ L797-800 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- `PredicateAcceptance.constOne` is the value-`1` constant section (the
sheafification unit is `toSheafify`, definitionally). -/
theorem constOne_eq_constSec (W : Opens ↑anP1) : constOne W = constSec 1 W := rfl


-- @@ L802-812 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Constant sections restrict to constant sections (naturality of the unit;
the constant presheaf has identity restrictions). -/
theorem constSec_res (q : ℚ) {W V : Opens ↑anP1} (h : W ≤ V) :
    FqAn.obj.map (homOfLE h).op (constSec q V) = constSec q W := by
  have hnat := (toSheafify JAn constPresheafQ).naturality (homOfLE h).op
  have := congrArg
    (fun (g : constPresheafQ.obj (op V) ⟶ FqAn.obj.obj (op W)) => g (ULift.up q))
    hnat
  rw [CategoryTheory.comp_apply, CategoryTheory.comp_apply] at this
  exact this.symm


-- @@ L814-821 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Constant sections add by adding values. -/
theorem constSec_add (q r : ℚ) (W : Opens ↑anP1) :
    constSec q W + constSec r W = constSec (q + r) W := by
  show _ = (toSheafify JAn constPresheafQ).app (op W) (ULift.up (q + r))
  rw [show (ULift.up (q + r) : ULift.{0} ℚ) = ULift.up q + ULift.up r from rfl,
    map_add]
  rfl


-- @@ L823-841 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **Value separation on inhabited opens**: two constant sections with equal
sheaf images over an open containing a point have equal values (local
injectivity of the sheafification unit; the constant presheaf has identity
restrictions). -/
theorem constSec_inj {W : Opens ↑anP1} {x : ↑anP1} (hx : x ∈ W) {q r : ℚ}
    (h : constSec q W = constSec r W) : q = r := by
  have hmem0 : Presheaf.equalizerSieve (F := constPresheafQ)
      (ULift.up q) (ULift.up r) ∈ JAn W :=
    Presheaf.equalizerSieve_mem JAn (toSheafify JAn constPresheafQ)
      (X := op W) (ULift.up q) (ULift.up r) h
  have hmem : ∀ y ∈ W, ∃ (V : Opens ↑anP1) (f : V ⟶ W),
      Presheaf.equalizerSieve (F := constPresheafQ)
        (ULift.up q) (ULift.up r) f ∧ y ∈ V := hmem0
  obtain ⟨V, f, harr, -⟩ := hmem x hx
  have harr' : constPresheafQ.map f.op (ULift.up q) =
      constPresheafQ.map f.op (ULift.up r) := harr
  have hup : (ULift.up q : ULift.{0} ℚ) = ULift.up r := harr'
  exact congrArg ULift.down hup


-- @@ L843-848 verbatim
/-- The local-value relation: `s` has value `q` near `x` (on some sub-open
containing `x`). -/
def hasVal (U : Opens ↑anP1) (s : FqAn.obj.obj (op U)) (x : ↑anP1) (q : ℚ) :
    Prop :=
  ∃ (V : Opens ↑anP1) (hVU : V ≤ U), x ∈ V ∧
    FqAn.obj.map (homOfLE hVU).op s = constSec q V


-- @@ L850-862 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **Local existence of values** (the sheafification unit is locally
surjective). -/
theorem exists_hasVal (U : Opens ↑anP1) (s : FqAn.obj.obj (op U)) {x : ↑anP1}
    (hx : x ∈ U) : ∃ q : ℚ, hasVal U s x q := by
  have hmem : ∀ y ∈ U, ∃ (V : Opens ↑anP1) (f : V ⟶ U),
      Presheaf.imageSieve (toSheafify JAn constPresheafQ) s f ∧ y ∈ V :=
    Presheaf.imageSieve_mem JAn (toSheafify JAn constPresheafQ) s
  obtain ⟨V, f, ⟨t, ht⟩, hxV⟩ := hmem x hx
  refine ⟨t.down, V, f.le, hxV, ?_⟩
  have harr : (homOfLE f.le : V ⟶ U) = f := Subsingleton.elim _ _
  rw [harr]
  exact ht.symm


-- @@ L864-878 verbatim
/-- **Uniqueness of values** (restrict both witnesses to their inhabited
intersection and separate). -/
theorem hasVal_unique {U : Opens ↑anP1} {s : FqAn.obj.obj (op U)} {x : ↑anP1}
    {q r : ℚ} (hq : hasVal U s x q) (hr : hasVal U s x r) : q = r := by
  obtain ⟨V, hVU, hxV, hres⟩ := hq
  obtain ⟨V', hVU', hxV', hres'⟩ := hr
  have h1 : FqAn.obj.map
      (homOfLE ((inf_le_left : V ⊓ V' ≤ V).trans hVU)).op s =
      constSec q (V ⊓ V') := by
    rw [← res_comp (inf_le_left : V ⊓ V' ≤ V) hVU s, hres, constSec_res]
  have h2 : FqAn.obj.map
      (homOfLE ((inf_le_right : V ⊓ V' ≤ V').trans hVU')).op s =
      constSec r (V ⊓ V') := by
    rw [← res_comp (inf_le_right : V ⊓ V' ≤ V') hVU' s, hres', constSec_res]
  exact constSec_inj (⟨hxV, hxV'⟩ : x ∈ V ⊓ V') (h1.symm.trans h2)


-- @@ L880-884 verbatim
/-- **The section value at a point** (well-defined by
`exists_hasVal`/`hasVal_unique`). -/
def secVal (U : Opens ↑anP1) (s : FqAn.obj.obj (op U)) (x : ↑anP1)
    (hx : x ∈ U) : ℚ :=
  (exists_hasVal U s hx).choose


-- @@ L886-888 verbatim
theorem secVal_spec (U : Opens ↑anP1) (s : FqAn.obj.obj (op U)) {x : ↑anP1}
    (hx : x ∈ U) : hasVal U s x (secVal U s x hx) :=
  (exists_hasVal U s hx).choose_spec


-- @@ L890-895 verbatim
/-- Any local witness computes the section value. -/
theorem secVal_eq_of_witness {U V : Opens ↑anP1} (hVU : V ≤ U)
    {s : FqAn.obj.obj (op U)} {q : ℚ}
    (hres : FqAn.obj.map (homOfLE hVU).op s = constSec q V) {z : ↑anP1}
    (hz : z ∈ V) : secVal U s z (hVU hz) = q :=
  hasVal_unique (secVal_spec U s (hVU hz)) ⟨V, hVU, hz, hres⟩


-- @@ L897-903 verbatim
/-- The section value of a constant section is its value. -/
theorem secVal_constSec (q : ℚ) (U : Opens ↑anP1) {x : ↑anP1} (hx : x ∈ U) :
    secVal U (constSec q U) x hx = q := by
  refine hasVal_unique (secVal_spec U (constSec q U) hx) ⟨U, le_refl U, hx, ?_⟩
  rw [show (homOfLE (le_refl U) : U ⟶ U) = 𝟙 U from rfl, op_id,
    CategoryTheory.Functor.map_id]
  rfl


-- @@ L905-914 verbatim
/-- Section values are restriction-compatible. -/
theorem secVal_res {V U : Opens ↑anP1} (hVU : V ≤ U) (s : FqAn.obj.obj (op U))
    {x : ↑anP1} (hxV : x ∈ V) :
    secVal V (FqAn.obj.map (homOfLE hVU).op s) x hxV =
      secVal U s x (hVU hxV) := by
  refine hasVal_unique (secVal_spec V _ hxV) ?_
  obtain ⟨W, hWU, hxW, hres⟩ := secVal_spec U s (hVU hxV)
  refine ⟨W ⊓ V, inf_le_right, ⟨hxW, hxV⟩, ?_⟩
  rw [res_comp (inf_le_right : W ⊓ V ≤ V) hVU s,
    ← res_comp (inf_le_left : W ⊓ V ≤ W) hWU s, hres, constSec_res]


-- @@ L916-932 verbatim
/-- Section values are additive. -/
theorem secVal_add (U : Opens ↑anP1) (s t : FqAn.obj.obj (op U)) {x : ↑anP1}
    (hx : x ∈ U) :
    secVal U (s + t) x hx = secVal U s x hx + secVal U t x hx := by
  refine hasVal_unique (secVal_spec U (s + t) hx) ?_
  obtain ⟨V, hVU, hxV, hres⟩ := secVal_spec U s hx
  obtain ⟨V', hVU', hxV', hres'⟩ := secVal_spec U t hx
  refine ⟨V ⊓ V', (inf_le_left : V ⊓ V' ≤ V).trans hVU, ⟨hxV, hxV'⟩, ?_⟩
  have hs : FqAn.obj.map
      (homOfLE ((inf_le_left : V ⊓ V' ≤ V).trans hVU)).op s =
      constSec (secVal U s x hx) (V ⊓ V') := by
    rw [← res_comp (inf_le_left : V ⊓ V' ≤ V) hVU s, hres, constSec_res]
  have ht : FqAn.obj.map
      (homOfLE ((inf_le_right : V ⊓ V' ≤ V').trans hVU')).op t =
      constSec (secVal U t x hx) (V ⊓ V') := by
    rw [← res_comp (inf_le_right : V ⊓ V' ≤ V') hVU' t, hres', constSec_res]
  rw [map_add, hs, ht, constSec_add]


-- @@ L934-953 verbatim
/-- **Constancy on preconnected opens**: the pointwise section value is
locally constant, hence constant on a preconnected open. -/
theorem secVal_congr_pt {U : Opens ↑anP1}
    (hU : IsPreconnected (U : Set ↑anP1)) (s : FqAn.obj.obj (op U))
    {x y : ↑anP1} (hx : x ∈ U) (hy : y ∈ U) :
    secVal U s x hx = secVal U s y hy := by
  haveI := Subtype.preconnectedSpace hU
  have hlc : IsLocallyConstant
      (fun p : (U : Set ↑anP1) => secVal U s p.1 p.2) := by
    refine (IsLocallyConstant.iff_exists_open _).mpr fun p => ?_
    obtain ⟨V, hVU, hpV, hres⟩ := secVal_spec U s p.2
    refine ⟨Subtype.val ⁻¹' (V : Set ↑anP1),
      V.isOpen.preimage continuous_subtype_val, hpV, fun z hz => ?_⟩
    have h1 : secVal U s z.1 z.2 = secVal U s z.1 (hVU hz) := rfl
    have h2 : secVal U s p.1 p.2 = secVal U s p.1 (hVU hpV) := rfl
    rw [h1, h2, secVal_eq_of_witness hVU hres hz, secVal_eq_of_witness hVU hres hpV]
  have := hlc.apply_eq_of_isPreconnected isPreconnected_univ
    (Set.mem_univ (⟨x, hx⟩ : (U : Set ↑anP1)))
    (Set.mem_univ (⟨y, hy⟩ : (U : Set ↑anP1)))
  exact this


-- @@ L955-955 verbatim
end SectionValues


-- @@ L957-957 verbatim
/-! ## 12. The wall input, closed: `edgeOne ≠ 0` unconditionally -/


-- @@ L959-959 verbatim
section WallClosure


-- @@ L961-964 verbatim
/-- Evaluation at the upper witness point, as an additive hom. -/
def valA : (FqAn.obj.obj (op AUp)) →+ ℚ :=
  AddMonoidHom.mk' (fun s => secVal AUp s upPt upPt_mem_AUp)
    (fun s t => secVal_add AUp s t upPt_mem_AUp)


-- @@ L966-969 verbatim
/-- Evaluation at the lower witness point, as an additive hom. -/
def valB : (FqAn.obj.obj (op BLo)) →+ ℚ :=
  AddMonoidHom.mk' (fun s => secVal BLo s loPt loPt_mem_BLo)
    (fun s t => secVal_add BLo s t loPt_mem_BLo)


-- @@ L971-974 verbatim
theorem valA_constOne : valA (constOne AUp) = 1 := by
  show secVal AUp (constOne AUp) upPt upPt_mem_AUp = 1
  rw [constOne_eq_constSec]
  exact secVal_constSec 1 AUp upPt_mem_AUp


-- @@ L976-983 verbatim
/-- Connectedness compatibility over `W0`. -/
theorem valA_valB_compat_W0 (s : FqAn.obj.obj (op W0)) :
    valA (FqAn.obj.map (homOfLE aUp_le_W0).op s) =
      valB (FqAn.obj.map (homOfLE bLo_le_W0).op s) := by
  show secVal AUp _ upPt upPt_mem_AUp = secVal BLo _ loPt loPt_mem_BLo
  rw [secVal_res aUp_le_W0 s upPt_mem_AUp, secVal_res bLo_le_W0 s loPt_mem_BLo]
  exact secVal_congr_pt isPreconnected_coe_W0 s
    (aUp_le_W0 upPt_mem_AUp) (bLo_le_W0 loPt_mem_BLo)


-- @@ L985-992 verbatim
/-- Connectedness compatibility over `W1`. -/
theorem valA_valB_compat_W1 (s : FqAn.obj.obj (op W1)) :
    valA (FqAn.obj.map (homOfLE aUp_le_W1).op s) =
      valB (FqAn.obj.map (homOfLE bLo_le_W1).op s) := by
  show secVal AUp _ upPt upPt_mem_AUp = secVal BLo _ loPt loPt_mem_BLo
  rw [secVal_res aUp_le_W1 s upPt_mem_AUp, secVal_res bLo_le_W1 s loPt_mem_BLo]
  exact secVal_congr_pt isPreconnected_coe_W1 s
    (aUp_le_W1 upPt_mem_AUp) (bLo_le_W1 loPt_mem_BLo)


-- @@ L994-1001 verbatim
/-- **The wall input, constructed** — the connectedness content of Leg A,
closed. -/
def wallInput : WallInput where
  valA := valA
  valB := valB
  valA_constOne := valA_constOne
  compat_W0 := valA_valB_compat_W0
  compat_W1 := valA_valB_compat_W1


-- @@ L1003-1009 verbatim
/-- **LEG A — the analytic inner (H⁰) edge class is nonzero,
unconditionally.**  This is the H⁰ half of the chart-interference wall; the
outer H¹ wall (Leg B) is parked below as two named receipts, and the assembly
to `bettiEdgeClass` and its ℂ-image (Leg C) is proved conditional on exactly
those receipts.  Nothing here makes the Hodge conjecture statable. -/
theorem edgeOne_ne_zero : PredicateAcceptance.edgeOne ≠ 0 :=
  edgeOne_ne_zero_of_wallInput wallInput


-- @@ L1011-1011 verbatim
end WallClosure


-- @@ L1013-1022 verbatim
/-! ## 13. Leg B parked (exact residual spellings) and Leg C proved
conditional on it

The outer H¹ wall is degree-1 constant-sheaf cohomology vanishing on the two
analytic chart opens — classically `V0 ≅ V1 ≅ ℂ` are contractible.  At this
pin it is a genuine wall (recon §5, Leg B: probe-gated Čech–Goursat
correction, 3–5u, or the subdivision campaign); it is parked here as two named
unproved `Prop`s at their exact residual spellings, stated, never proved,
never assumed, and consumed only as the explicit hypotheses of the conditional
theorems below (the `InterferenceExclusion` retirement pattern). -/


-- @@ L1024-1024 verbatim
section LegC


-- @@ L1026-1030 verbatim
/-- **PARKED (Leg B receipt, first chart)**: degree-1 vanishing of the
constant-sheaf carrier on the analytic chart open `V0`.  Stated, never proved,
never assumed. -/
def AnalyticChartOneVanishingV0 : Prop :=
  Subsingleton (Ext (freeYonedaSheaf JAn V0) FqAn 1)


-- @@ L1032-1036 verbatim
/-- **PARKED (Leg B receipt, second chart)**: degree-1 vanishing of the
constant-sheaf carrier on the analytic chart open `V1`.  Stated, never proved,
never assumed. -/
def AnalyticChartOneVanishingV1 : Prop :=
  Subsingleton (Ext (freeYonedaSheaf JAn V1) FqAn 1)


-- @@ L1038-1065 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **Leg C, raw form**: given the two parked receipts, the outer (raw) edge
is nonzero — the `H¹`-squeeze of `InterferenceProof.subsingleton_hPrimeOne_sup`
transposed: the outer terms vanish, so by exactness at the `H'¹(V0 ⊓ V1)`-node
the inner edge would have to come from the (trivial) biprod if `δ` killed it. -/
theorem edgeTwoRaw_ne_zero_of_receipts (h0 : AnalyticChartOneVanishingV0)
    (h1 : AnalyticChartOneVanishingV1) : edgeTwoRaw ≠ 0 := by
  intro hz
  have hδ : (Opens.mayerVietorisSquare V0 V1).δ FqAn 1 2 rfl
      PredicateAcceptance.edgeOne = 0 := hz
  have hex := ((Opens.mayerVietorisSquare V0 V1).sequence_exact FqAn 1 2 rfl).exact 1
  obtain ⟨b, hb⟩ := (ShortComplex.ab_exact_iff _).mp hex
    PredicateAcceptance.edgeOne hδ
  have hb' : (Opens.mayerVietorisSquare V0 V1).fromBiprod FqAn 1 b =
      PredicateAcceptance.edgeOne := hb
  obtain ⟨⟨a0, a1⟩, rfl⟩ :=
    (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.symm.surjective b
  rw [Iso.addCommGroupIsoToAddEquiv_symm_apply,
    (Opens.mayerVietorisSquare V0 V1).fromBiprod_biprodIsoProd_inv_apply FqAn a0 a1]
    at hb'
  haveI hs2 : Subsingleton
      (FqAn.H' 1 (Opens.mayerVietorisSquare V0 V1).X₂) := h0
  haveI hs3 : Subsingleton
      (FqAn.H' 1 (Opens.mayerVietorisSquare V0 V1).X₃) := h1
  have ha0 : a0 = 0 := @Subsingleton.elim _ hs2 a0 0
  have ha1 : a1 = 0 := @Subsingleton.elim _ hs3 a1 0
  rw [ha0, ha1, map_zero, map_zero, sub_zero] at hb'
  exact edgeOne_ne_zero hb'.symm


-- @@ L1067-1086 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **Leg C, class form**: given the two parked receipts, the Betti-side edge
class is nonzero in the predicate's exact carrier (transport of the raw
nonvanishing up the `≃+` re-anchor tower). -/
theorem bettiEdgeClass_ne_zero_of_receipts (h0 : AnalyticChartOneVanishingV0)
    (h1 : AnalyticChartOneVanishingV1) :
    PredicateAcceptance.bettiEdgeClass ≠ 0 := by
  intro h
  apply edgeTwoRaw_ne_zero_of_receipts h0 h1
  have h2 : PredicateAcceptance.edgeTwo = 0 := by
    have h' : hPrimeTopEquivH (⊤ : Opens ↑anP1) (opensTopTerminal anP1) FqAn 2
        PredicateAcceptance.edgeTwo = 0 := h
    have hz := congrArg
      (hPrimeTopEquivH (⊤ : Opens ↑anP1) (opensTopTerminal anP1) FqAn 2).symm h'
    rwa [AddEquiv.symm_apply_apply, map_zero] at hz
  have h2' : (CycCarrier.extReanchorLeft (Y := FqAn)
      (eqToIso (congrArg (freeYonedaSheaf JAn) V0_sup_V1)) 2) edgeTwoRaw = 0 := h2
  have h3 := congrArg (CycCarrier.extReanchorLeft (Y := FqAn)
      (eqToIso (congrArg (freeYonedaSheaf JAn) V0_sup_V1)) 2).symm h2'
  rwa [AddEquiv.symm_apply_apply, map_zero] at h3


-- @@ L1088-1094 verbatim
/-- **The named gap, conditional retirement**: given the two parked Leg-B
receipts, `PredicateAcceptance.BettiEdgeNonvanishing` holds at its literal
spelling. -/
theorem bettiEdgeNonvanishing_of_receipts (h0 : AnalyticChartOneVanishingV0)
    (h1 : AnalyticChartOneVanishingV1) :
    PredicateAcceptance.BettiEdgeNonvanishing :=
  bettiEdgeClass_ne_zero_of_receipts h0 h1


-- @@ L1096-1096 verbatim
end LegC


-- @@ L1098-1106 verbatim
/-! ## 14. Injectivity of the ℚ→ℂ coefficient change

The coefficient inclusion `ULift ℚ → ULift ℂ` splits additively (a ℚ-linear
projection `ℂ → ℚ` exists by `Classical.choice` — no canonical choice is
claimed), functors preserve split monomorphisms, and `Sheaf.H.map` is
functorial: `toComplexCoeffs X n` is injective for every space and degree.
This retires, for this development, the recon's caveat that ℂ-image
nonvanishing might be strictly stronger than rational nonvanishing: for the
constructed carriers they are equivalent. -/


-- @@ L1108-1108 verbatim
section CoefficientInjectivity


-- @@ L1110-1110 verbatim
universe u


-- @@ L1112-1117 verbatim
/-- A ℚ-linear projection `ℂ → ℚ` splitting the inclusion (`Classical.choice`
through the existence of left inverses over a field; no canonicity, no
continuity, and no ring structure is claimed for it). -/
def ratProj : ℂ →ₗ[ℚ] ℚ :=
  (LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ℚ ℂ)
    (LinearMap.ker_eq_bot.mpr (RingHom.injective (algebraMap ℚ ℂ)))).choose


-- @@ L1119-1122 verbatim
theorem ratProj_comp :
    ratProj.comp (Algebra.linearMap ℚ ℂ) = LinearMap.id :=
  (LinearMap.exists_leftInverse_of_injective (Algebra.linearMap ℚ ℂ)
    (LinearMap.ker_eq_bot.mpr (RingHom.injective (algebraMap ℚ ℂ)))).choose_spec


-- @@ L1124-1127 verbatim
theorem ratProj_cast (q : ℚ) : ratProj (q : ℂ) = q := by
  have h1 := LinearMap.congr_fun ratProj_comp q
  rw [LinearMap.comp_apply, LinearMap.id_apply, Algebra.linearMap_apply] at h1
  rwa [eq_ratCast (algebraMap ℚ ℂ) q] at h1


-- @@ L1129-1134 verbatim
/-- The additive retraction of `Betti.coeffHom`. -/
def coeffRetract :
    AddCommGrpCat.of (ULift.{u} ℂ) ⟶ AddCommGrpCat.of (ULift.{u} ℚ) :=
  AddCommGrpCat.ofHom
    (AddEquiv.ulift.symm.toAddMonoidHom.comp
      ((ratProj.toAddMonoidHom).comp AddEquiv.ulift.toAddMonoidHom))


-- @@ L1136-1143 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem coeffHom_comp_coeffRetract :
    Betti.coeffHom.{u} ≫ coeffRetract.{u} = 𝟙 (AddCommGrpCat.of (ULift.{u} ℚ)) := by
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro x
  show ULift.up (ratProj ((x.down : ℚ) : ℂ)) = x
  rw [ratProj_cast]


-- @@ L1145-1178 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **The ℚ→ℂ coefficient change on sheaf-Betti cohomology is injective**, in
every degree, on every space: `Sheaf.H.map` of a retract pair collapses to the
identity.  (Constructed-carrier statement only; no comparison with any other
cohomology theory is stated or implied.) -/
theorem toComplexCoeffs_injective (X : TopCat.{u}) (n : ℕ) :
    Function.Injective (Betti.toComplexCoeffs X n) := by
  intro x y h
  have hid : (constantSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).map Betti.coeffHom ≫
      (constantSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{u}).map coeffRetract =
      𝟙 ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℚ))) := by
    rw [← Functor.map_comp, coeffHom_comp_coeffRetract,
      CategoryTheory.Functor.map_id]
  have hx := Sheaf.H.map_comp_apply
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      Betti.coeffHom)
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      coeffRetract) x
  have hy := Sheaf.H.map_comp_apply
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      Betti.coeffHom)
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
      coeffRetract) y
  rw [hid, Sheaf.H.map_id_apply] at hx hy
  calc x = Sheaf.H.map
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
          coeffRetract) n (Betti.toComplexCoeffs X n x) := hx
    _ = Sheaf.H.map
        ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).map
          coeffRetract) n (Betti.toComplexCoeffs X n y) := by rw [h]
    _ = y := hy.symm


-- @@ L1180-1180 verbatim
end CoefficientInjectivity


-- @@ L1182-1182 verbatim
/-! ## 15. The fork-closing form: the ℂ-image of the edge class -/


-- @@ L1184-1184 verbatim
section Primary


-- @@ L1186-1199 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **The ℂ-image of the Betti edge class is nonzero, given the two parked
Leg-B receipts** — the recon §4(c) fork-closing target, in exactly the shape
whose *negation* governs the degenerate branch of the 2πi-fork trichotomy.
(This module does not consume or restate any junction spelling; the fork
itself is untouched.)  Nothing here makes the Hodge conjecture statable. -/
theorem toComplexCoeffs_bettiEdge_ne_zero_of_receipts
    (h0 : AnalyticChartOneVanishingV0) (h1 : AnalyticChartOneVanishingV1) :
    Betti.toComplexCoeffs (TopCat.of (SPoints ProjectiveLine.structMor)) 2
      PredicateAcceptance.bettiEdgeClass ≠ 0 := by
  intro h
  refine bettiEdgeClass_ne_zero_of_receipts h0 h1 ?_
  refine toComplexCoeffs_injective (TopCat.of (SPoints ProjectiveLine.structMor)) 2 ?_
  rw [h, map_zero]


-- @@ L1201-1201 verbatim
end Primary


-- @@ L1203-1209 verbatim
/-! ## 16. Falsifier receipts (drift guards and negative controls)

`rfl`-pins to the imported literals the routing consumes (a drift in the edge
construction breaks these), plus the module-level negative control: the same
constructed functional that detects the mixed section kills every
globally-constant input (the class-level control is the shipped
`PredicateAcceptance.edgeRoute_constOne_eq_zero`). -/


-- @@ L1211-1211 verbatim
section Falsifiers


-- @@ L1213-1215 verbatim
/-- Drift guard: the inner edge is the MV connecting map at the mixed class. -/
theorem edgeOneRaw_pin :
    edgeOneRaw = (Opens.mayerVietorisSquare W0 W1).δ FqAn 0 1 rfl mixH0 := rfl


-- @@ L1217-1221 verbatim
/-- Drift guard: the inner edge is the re-anchor of the raw inner edge. -/
theorem edgeOne_pin :
    PredicateAcceptance.edgeOne =
      CycCarrier.extReanchorLeft
        (eqToIso (congrArg (freeYonedaSheaf JAn) W0_sup_W1)) 1 edgeOneRaw := rfl


-- @@ L1223-1224 verbatim
/-- Drift guard: the double overlap splits as the two half-plane components. -/
theorem overlap_split_pin : W0 ⊓ W1 = AUp ⊔ BLo := W0_inf_W1


-- @@ L1226-1231 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Drift guard: the mixed section is the restriction of the literal glued
datum `mixGlued`. -/
theorem mixSection_pin :
    mixSection = FqAn.obj.map (homOfLE (le_of_eq W0_inf_W1)).op
      (mixGlued : FqAn.obj.obj (op (AUp ⊔ BLo))) := rfl


-- @@ L1233-1238 verbatim
/-- Drift guard: the Betti edge class is the terminal-anchor image of the
outer edge. -/
theorem bettiEdgeClass_pin :
    PredicateAcceptance.bettiEdgeClass =
      hPrimeTopEquivH (⊤ : Opens ↑anP1) (opensTopTerminal anP1) FqAn 2
        PredicateAcceptance.edgeTwo := rfl


-- @@ L1240-1243 verbatim
/-- **Negative control (module level)**: the constructed separation functional
scores the honest mixed input at `1` … -/
theorem sepFun_wallInput_mixSection : sepFun wallInput mixSection = 1 :=
  sepFun_mixSection wallInput


-- @@ L1245-1251 verbatim
/-- … and kills a globally-constant input restricted from a covering slit open
(chart-extendable data is invisible to the wall functional, matching the
shipped class-level control `edgeRoute_constOne_eq_zero`). -/
theorem sepFun_wallInput_constOne_res :
    sepFun wallInput
      (FqAn.obj.map (homOfLE (inf_le_left : W0 ⊓ W1 ≤ W0)).op (constOne W0)) = 0 :=
  sepFun_res_W0 wallInput (constOne W0)


-- @@ L1253-1258 verbatim
/-- Value receipt: the wall input reads the upper restriction of the mixed
section as `1` (through the constructed point `upPt`). -/
theorem wallInput_valA_mix :
    wallInput.valA (FqAn.obj.map (homOfLE aUp_le_infW).op mixSection) = 1 := by
  rw [mixSection_res_AUp]
  exact valA_constOne


-- @@ L1260-1265 verbatim
/-- Value receipt: the wall input reads the lower restriction of the mixed
section as `0`. -/
theorem wallInput_valB_mix :
    wallInput.valB (FqAn.obj.map (homOfLE bLo_le_infW).op mixSection) = 0 := by
  rw [mixSection_res_BLo]
  exact map_zero _


-- @@ L1267-1267 verbatim
end Falsifiers


-- @@ L1269-1269 verbatim
end AnalyticWallA


-- @@ L1271-1271 verbatim
end HodgePilot


-- @@ L1273-1273 verbatim
end
