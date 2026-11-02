import HodgePilot.CyclePairing


-- @@ L3-107 verbatim
/-! # The projective plane: the p = 2 calibration object, two line-divisor
# data, and their paired class

The second named variety of this development, and the object to which the
outside reviews routed all future positive product tests (classically
`H^4` of the projective plane is nonzero, unlike `H^4` of the projective
line, which vanishes; **no such computation is performed or claimed
here**).  This module re-keys the golden-path wave-1 ladder
(`HodgePilot.ProjectiveLine`) at three variables: for
`p2 := Proj ℂ[X₀, X₁, X₂]` (the pin's only ℙⁿ-shaped object; standard
grading) it constructs:

**Part 1 — the object and its instances** (the wave-1 recipes, one
variable up).

* `p2 : Scheme.{0}` and the structure morphism
  `structMor : p2 ⟶ Spec ℂ` — the pin's `Proj.toSpecZero` composed with
  `Spec` of the grade-zero identification `gradeZeroEquiv : ℂ ≃+* 𝒜 0`;
* `AlgebraicGeometry.IsProper structMor` — the pin instance
  `IsProper (Proj.toSpecZero 𝒜)`, gated on the `Algebra.FiniteType`
  instance proved here, transported along the `Spec` of the iso;
* `IsIntegral p2` — irreducibility by the generic point and reducedness
  stalkwise;
* `AlgebraicGeometry.IsNoetherian p2`;
* the **three-chart standard cover** `chart 0, chart 1, chart 2`
  (`D₊(X₀), D₊(X₁), D₊(X₂)`), with `⨆ i, chart i = ⊤`.

**Part 2 — two line-divisor data** (the new work over wave 1: the
three-chart glue).

* Chart-overlap units `overlapUnit i j` realizing "`Xⱼ/Xᵢ`" on
  `chart i ⊓ chart j`, and their germs `zElt i j` in the unit group of
  the function field — the wave-1 overlap-unit construction at generic
  indices;
* **the cocycle** `zElt 0 1 + zElt 1 2 = zElt 0 2` — the genuinely new
  ingredient of the three-chart case, proved by restricting all three
  units to the triple overlap `D₊(X₀X₁X₂)` and computing in the
  homogeneous localization `ℂ[X₀,X₁,X₂]_{(X₀X₁X₂)}` via the pin's
  `HomogeneousLocalization.awayMap` and `Proj.awayMap_awayToSection`;
* `lineOne, lineTwo : CDiv p2` — two global Cartier divisor data glued
  from the transition data "`X₁/X₀`" and "`X₂/X₀`" respectively, over
  the three-chart cover, via the pin's sheaf-condition unique gluing
  (`TopCat.Sheaf.existsUnique_gluing'`), with restriction and uniqueness
  receipts.  Classically these data present the two coordinate lines
  `{X₁ = 0}` and `{X₂ = 0}`; **no such identification is stated**: no
  Weil divisor is attached to either (`CartierClass.CartierWeilComparison`
  remains an unproved named `Prop`), no order of vanishing is computed,
  and neither datum is claimed to be nonzero, nor are the two claimed to
  be distinct as elements of `CDiv p2`.

**Part 3 — the divisor classes and cycle classes (all BY CONSTRUCTION).**

* `lineOneClass`/`lineTwoClass` in `H¹(p2, O^*)` and
  `lineOneCycleClass`/`lineTwoCycleClass` in `F¹ ℍ²_dR(p2)` — pure
  applications of the shipped divisor-level cycle class machinery; the
  `F¹`-membership receipts hold **by construction**.

**Part 4 — the point of the module: the two-line paired class.**

* `linesPairedDivClass = pairedDivClass p2 lineOne lineTwo` and the
  landed `linesPairedInto` in `F²` of the degree-4 hypercohomology — the
  shipped `CyclePairing` machinery evaluated at the pair
  `(lineOne, lineTwo)` of **distinct glue data**: the honest
  pairing-shaped value at `p = 2` on a named surface-shaped object.
  Classically, two distinct lines in the projective plane meet in
  exactly one point (Bézout for two degree-1 curves; Hartshorne,
  *Algebraic Geometry*, I.7.8 — a citation-only referent), which is why
  the reviews routed positive product tests here; **nothing of the sort
  is computed, claimed, or approached in this module**.  As in
  `HodgePilot.CyclePairing`, whose ceilings apply verbatim: this is a
  constructed pairing-shaped assignment evaluated at one input pair; it
  is **not** the cup product, it is **not** identified with any
  classical intersection pairing or intersection number, and **no
  canonicity is claimed** for the exhibited choices.

## Claim discipline

**No nonvanishing of any class is claimed anywhere in this module**: not
of `lineOne` or `lineTwo`, not of their `H¹(O^*)` classes, not of their
cycle classes, not of `linesPairedDivClass` or `linesPairedInto` — every
one of them could, for all this module proves, be zero, and the two line
data are not claimed to be distinct as divisor classes.  All membership
statements are **by construction** (the shipped maps land in the
filtration subtypes by their codomains) and are labelled as such; they
are definitional receipts, not computations.  No comparison map is
claimed to be an isomorphism or quasi-isomorphism, and no comparison
theorem with any other cohomology theory is stated, implied, or
approached.  The filtrations are the **naive** (brutal-truncation)
filtrations throughout.  `H¹(p2, O^*)` is *classically* the Picard
group; no Picard group is constructed and no such identification is
claimed.  Properness of `structMor` is this pin's weakening of the
classical projectivity of the plane; no projectivity claim is made.  No
smoothness statement is made.  Nothing here makes the Hodge conjecture
statable.

## Credits

`Proj`, its charts, `toSpecZero` and its properness are Andrew Yang's
and Jujian Zhang's Mathlib infrastructure; homogeneous localizations and
`awayMap` are Jujian Zhang's; the unique-gluing sheaf condition is
Justus Springer's; the Cartier-divisor machinery consumed here is
`HodgePilot.CartierClass`/`HodgePilot.CycCarrier`, the pairing is
`HodgePilot.CyclePairing`, and the ladder re-keyed here is
`HodgePilot.ProjectiveLine` (golden-path wave 1).
-/


-- @@ L109-109 verbatim
set_option maxHeartbeats 1000000

-- @@ L110-110 verbatim
set_option synthInstance.maxHeartbeats 1000000


-- @@ L112-112 verbatim
noncomputable section


-- @@ L114-114 verbatim
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

-- @@ L115-115 verbatim
open AlgebraicGeometry HomogeneousLocalization


-- @@ L117-117 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L119-119 verbatim
namespace HodgePilot


-- @@ L121-121 verbatim
namespace ProjectivePlane


-- @@ L123-123 verbatim
open HodgePilot.DLog HodgePilot.CartierClass HodgePilot.CycCarrier

-- @@ L124-124 verbatim
open HodgePilot.CyclePairing HodgePilot.Hyper HodgePilot.DeRhamPresheaf

-- @@ L125-125 verbatim
open HodgePilot.DeRhamSheaf HodgePilot.DeRhamWedgeChain


-- @@ L127-128 verbatim
/-- The standard grading of `ℂ[X₀, X₁, X₂]` by total degree. -/
local notation "𝒜₃" => MvPolynomial.homogeneousSubmodule (Fin 3) ℂ


-- @@ L130-130 verbatim
/-! ## Part 1(pre). The object -/


-- @@ L132-135 verbatim
/-- **The projective plane** `ℙ² = Proj ℂ[X₀, X₁, X₂]` (standard grading),
at `Scheme.{0}`.  The pin's `Proj` is the only ℙⁿ-shaped scheme in this
Mathlib; a definition, not a claim. -/
abbrev p2 : Scheme.{0} := Proj 𝒜₃


-- @@ L137-140 verbatim
/-- Drift-guard receipt: the object is the same `Proj`-spelling as the
wave-1 projective line, one variable up. -/
theorem p2_receipt :
    p2 = Proj (MvPolynomial.homogeneousSubmodule (Fin 3) ℂ) := rfl


-- @@ L142-147 verbatim
/-! ## Part 1(a). The `Algebra.FiniteType` gate

The pin instance `IsProper (Proj.toSpecZero 𝒜)` is gated only on
`Algebra.FiniteType (𝒜 0) A`; this section closes the gate via
`Algebra.FiniteType.of_restrictScalars_finiteType` and the grade-zero
scalar tower — the wave-1 recipe, index-generic. -/


-- @@ L149-153 verbatim
instance instIsScalarTowerGradeZero :
    IsScalarTower ℂ (𝒜₃ 0) (MvPolynomial (Fin 3) ℂ) :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := 𝒜₃ 0)
    (A := MvPolynomial (Fin 3) ℂ) fun c => by
      rw [SetLike.GradeZero.algebraMap_apply, SetLike.GradeZero.coe_algebraMap]


-- @@ L155-160 verbatim
/-- The `FiniteType` gate of the pin's `Proj.toSpecZero` instances:
`ℂ[X₀, X₁, X₂]` is of finite type over its degree-zero part. -/
instance instFiniteTypeGradeZero :
    Algebra.FiniteType (𝒜₃ 0) (MvPolynomial (Fin 3) ℂ) :=
  Algebra.FiniteType.of_restrictScalars_finiteType ℂ (𝒜₃ 0)
    (MvPolynomial (Fin 3) ℂ)


-- @@ L162-166 verbatim
/-- Receipt: with the gate closed, the pin's properness instance for the
structure map to `Spec (𝒜 0)` synthesizes with no hypothesized binder. -/
theorem isProper_toSpecZero :
    AlgebraicGeometry.IsProper (Proj.toSpecZero 𝒜₃) :=
  inferInstance


-- @@ L168-168 verbatim
/-! ## Part 1(b). The grade-zero identification and the structure morphism -/


-- @@ L170-181 verbatim
theorem gradeZero_algebraMap_bijective :
    Function.Bijective (algebraMap ℂ (𝒜₃ 0)) := by
  constructor
  · intro a b hab
    exact MvPolynomial.C_injective (Fin 3) ℂ (congrArg Subtype.val hab)
  · intro x
    have hx : (x : MvPolynomial (Fin 3) ℂ) ∈
        (1 : Submodule ℂ (MvPolynomial (Fin 3) ℂ)) := by
      rw [← MvPolynomial.homogeneousSubmodule_zero]
      exact x.2
    obtain ⟨c, hc⟩ := Submodule.mem_one.mp hx
    exact ⟨c, Subtype.ext hc⟩


-- @@ L183-186 verbatim
/-- **Degree-zero homogeneous polynomials are the constants**:
`ℂ ≃+* (𝒜 0)` via the algebra map. -/
def gradeZeroEquiv : ℂ ≃+* (𝒜₃ 0) :=
  RingEquiv.ofBijective (algebraMap ℂ (𝒜₃ 0)) gradeZero_algebraMap_bijective


-- @@ L188-192 verbatim
/-- **The structure morphism of the projective plane**: the pin's
`Proj.toSpecZero` followed by `Spec` of the grade-zero identification.
One exhibited choice of presentation; no canonicity is claimed. -/
def structMor : p2 ⟶ Spec (CommRingCat.of ℂ) :=
  Proj.toSpecZero 𝒜₃ ≫ Spec.map (gradeZeroEquiv.toCommRingCatIso.hom)


-- @@ L194-199 verbatim
/-- Drift-guard receipt: the structure morphism is the same
`toSpecZero ≫ Spec.map`-spelling as wave 1's. -/
theorem structMor_receipt :
    structMor =
      Proj.toSpecZero 𝒜₃ ≫ Spec.map (gradeZeroEquiv.toCommRingCatIso.hom) :=
  rfl


-- @@ L201-211 verbatim
/-- **The structure morphism is proper**: the pin instance
`IsProper (Proj.toSpecZero 𝒜)` (gated on `instFiniteTypeGradeZero`)
composed with the isomorphism `Spec ℂ ≅ Spec (𝒜 0)`.  Properness is this
pin's weakening of the classical projectivity hypothesis (the pin has no
projectivity predicate); no projectivity claim is made. -/
instance instIsProperStructMor : AlgebraicGeometry.IsProper structMor := by
  haveI : AlgebraicGeometry.IsProper
      (Spec.map (gradeZeroEquiv.toCommRingCatIso.hom)) :=
    MorphismProperty.of_isIso @AlgebraicGeometry.IsProper _
  exact inferInstanceAs (AlgebraicGeometry.IsProper
    (Proj.toSpecZero 𝒜₃ ≫ Spec.map (gradeZeroEquiv.toCommRingCatIso.hom)))


-- @@ L213-213 verbatim
/-! ## Part 1(c). Integrality -/


-- @@ L215-229 verbatim
/-- The zero ideal of `ℂ[X₀, X₁, X₂]` as a point of the projective
spectrum: prime (the ring is a domain) and relevant (`X₀` is a nonzero
element of the irrelevant ideal). -/
def botPoint : ProjectiveSpectrum 𝒜₃ :=
  ⟨⊥, by rw [HomogeneousIdeal.toIdeal_bot]; exact Ideal.isPrime_bot,
    fun hle => by
      have hmem : (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℂ) ∈
          HomogeneousIdeal.irrelevant 𝒜₃ :=
        HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos
          ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
            (MvPolynomial.isHomogeneous_X ℂ 0))
      have h0 : (MvPolynomial.X 0 : MvPolynomial (Fin 3) ℂ) ∈
          ((⊥ : HomogeneousIdeal 𝒜₃) : Set (MvPolynomial (Fin 3) ℂ)) := hle hmem
      rw [HomogeneousIdeal.coe_bot] at h0
      exact MvPolynomial.X_ne_zero (R := ℂ) 0 (Set.mem_zero.mp h0)⟩


-- @@ L231-239 verbatim
/-- Every point of the projective spectrum lies in the closure of the
zero ideal: the space is the closure of a point. -/
theorem closure_botPoint :
    closure ({botPoint} : Set (ProjectiveSpectrum 𝒜₃)) = Set.univ := by
  rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    ProjectiveSpectrum.vanishingIdeal_singleton,
    show botPoint.asHomogeneousIdeal = (⊥ : HomogeneousIdeal 𝒜₃) from rfl,
    HomogeneousIdeal.coe_bot, ← Set.singleton_zero]
  exact ProjectiveSpectrum.zeroLocus_singleton_zero 𝒜₃


-- @@ L241-250 verbatim
/-- The projective plane is an irreducible space (its topology is the
closure of the zero-ideal point). -/
instance instIrreducibleSpaceP2 : IrreducibleSpace p2 where
  isPreirreducible_univ := by
    have h : IsIrreducible
        (closure ({botPoint} : Set (ProjectiveSpectrum 𝒜₃))) :=
      isIrreducible_singleton.closure
    rw [closure_botPoint] at h
    exact h.2
  toNonempty := ⟨botPoint⟩


-- @@ L252-267 verbatim
/-- The stalks of the projective plane are integral domains: they are
homogeneous localizations of `ℂ[X₀, X₁, X₂]` at relevant primes, embedded
by `HomogeneousLocalization.val` in localizations of a domain at
submonoids of nonzerodivisors. -/
instance instIsDomainStalkP2 (x : p2) : IsDomain (p2.presheaf.stalk x) := by
  haveI : IsDomain (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) :=
    IsLocalization.isDomain_localization
      (Ideal.primeCompl_le_nonZeroDivisors _)
  haveI : IsDomain (AtPrime 𝒜₃ x.asHomogeneousIdeal.toIdeal) :=
    Function.Injective.isDomain
      (algebraMap (AtPrime 𝒜₃ x.asHomogeneousIdeal.toIdeal)
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
      (HomogeneousLocalization.val_injective _)
  exact Function.Injective.isDomain
    ((Proj.stalkIso 𝒜₃ x).commRingCatIsoToRingEquiv.toRingHom)
    (Proj.stalkIso 𝒜₃ x).commRingCatIsoToRingEquiv.injective


-- @@ L269-270 verbatim
instance instIsReducedP2 : IsReduced p2 :=
  isReduced_of_isReduced_stalk p2


-- @@ L272-275 verbatim
/-- **The projective plane is an integral scheme** (irreducible and
reduced; the pin's `isIntegral_of_irreducibleSpace_of_isReduced`). -/
instance instIsIntegralP2 : IsIntegral p2 :=
  isIntegral_of_irreducibleSpace_of_isReduced p2


-- @@ L277-277 verbatim
/-! ## Part 1(d). Noetherianity -/


-- @@ L279-280 verbatim
instance instIsNoetherianRingGradeZero : IsNoetherianRing (𝒜₃ 0) :=
  isNoetherianRing_of_ringEquiv ℂ gradeZeroEquiv


-- @@ L282-283 verbatim
instance instIsLocallyNoetherianP2 : IsLocallyNoetherian p2 :=
  LocallyOfFiniteType.isLocallyNoetherian (Proj.toSpecZero 𝒜₃)


-- @@ L285-286 verbatim
instance instCompactSpaceP2 : CompactSpace p2 :=
  QuasiCompact.compactSpace_of_compactSpace (Proj.toSpecZero 𝒜₃)


-- @@ L288-292 verbatim
/-- **The projective plane is a Noetherian scheme** (locally Noetherian
along the pin's `LocallyOfFiniteType (Proj.toSpecZero 𝒜)` over the
Noetherian base `𝒜 0 ≃ ℂ`, compact by the pin's
`QuasiCompact (Proj.toSpecZero 𝒜)`). -/
instance instIsNoetherianP2 : AlgebraicGeometry.IsNoetherian p2 where


-- @@ L294-294 verbatim
/-! ## Part 1(e). The three-chart standard cover -/


-- @@ L296-297 verbatim
/-- The standard chart `D₊(Xᵢ)` of the projective plane. -/
def chart (i : Fin 3) : p2.Opens := Proj.basicOpen 𝒜₃ (MvPolynomial.X i)


-- @@ L299-303 verbatim
/-- The overlap of two standard charts is the basic open of `XᵢXⱼ`. -/
theorem chart_inf (i j : Fin 3) :
    chart i ⊓ chart j =
      Proj.basicOpen 𝒜₃ (MvPolynomial.X i * MvPolynomial.X j) :=
  (Proj.basicOpen_mul 𝒜₃ (MvPolynomial.X i) (MvPolynomial.X j)).symm


-- @@ L305-320 verbatim
/-- **The three standard charts cover the projective plane.** -/
theorem iSup_chart_eq_top : (⨆ i : Fin 3, chart i) = ⊤ :=
  Proj.iSup_basicOpen_eq_top' 𝒜₃
    (MvPolynomial.X : Fin 3 → MvPolynomial (Fin 3) ℂ)
    (fun i => ⟨1, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (MvPolynomial.isHomogeneous_X ℂ i)⟩)
    (top_le_iff.mp fun a _ => by
      have ha : a ∈ Algebra.adjoin ℂ
          (Set.range (MvPolynomial.X : Fin 3 → MvPolynomial (Fin 3) ℂ)) := by
        rw [MvPolynomial.adjoin_range_X]; trivial
      have hle : Algebra.adjoin ℂ
          (Set.range (MvPolynomial.X : Fin 3 → MvPolynomial (Fin 3) ℂ)) ≤
          Subalgebra.restrictScalars ℂ (Algebra.adjoin (𝒜₃ 0)
            (Set.range (MvPolynomial.X : Fin 3 → MvPolynomial (Fin 3) ℂ))) :=
        Algebra.adjoin_le fun s hs => Algebra.subset_adjoin hs
      exact (Subalgebra.mem_restrictScalars ℂ).mp (hle ha))


-- @@ L322-330 verbatim
/-- Receipt: the cover in binary-supremum form. -/
theorem chart_cover_receipt : chart 0 ⊔ chart 1 ⊔ chart 2 = ⊤ := by
  rw [← iSup_chart_eq_top]
  exact le_antisymm
    (sup_le (sup_le (le_iSup chart 0) (le_iSup chart 1)) (le_iSup chart 2))
    (iSup_le fun i => match i with
      | 0 => le_sup_left.trans le_sup_left
      | 1 => le_sup_right.trans le_sup_left
      | 2 => le_sup_right)


-- @@ L332-333 verbatim
/-- The zero-ideal point, typed at the scheme carrier. -/
def botPt : Proj 𝒜₃ := botPoint


-- @@ L335-341 verbatim
theorem botPt_mem_basicOpen {f : MvPolynomial (Fin 3) ℂ} (hf : f ≠ 0) :
    botPt ∈ Proj.basicOpen 𝒜₃ f := by
  rw [Proj.mem_basicOpen]
  intro h
  have h' : f ∈ ((⊥ : HomogeneousIdeal 𝒜₃) : Set (MvPolynomial (Fin 3) ℂ)) := h
  rw [HomogeneousIdeal.coe_bot] at h'
  exact hf (Set.mem_zero.mp h')


-- @@ L343-347 verbatim
/-- The generic point lies in every nonempty open (`IsGenericPoint`). -/
theorem genericPoint_mem {W : p2.Opens} (hW : (W : Set p2).Nonempty) :
    genericPoint p2 ∈ W := by
  refine ((genericPoint_spec p2).mem_open_set_iff W.isOpen).mpr ?_
  simpa using hW


-- @@ L349-351 verbatim
theorem genericPoint_mem_chart (i : Fin 3) : genericPoint p2 ∈ chart i :=
  genericPoint_mem
    ⟨botPt, botPt_mem_basicOpen (MvPolynomial.X_ne_zero (R := ℂ) i)⟩


-- @@ L353-358 verbatim
theorem genericPoint_mem_chartInf (i j : Fin 3) :
    genericPoint p2 ∈ chart i ⊓ chart j :=
  genericPoint_mem ⟨botPt, by
    rw [chart_inf]
    exact botPt_mem_basicOpen (mul_ne_zero
      (MvPolynomial.X_ne_zero (R := ℂ) i) (MvPolynomial.X_ne_zero (R := ℂ) j))⟩


-- @@ L360-363 verbatim
/-! ## Part 2(a). Chart-overlap units at generic indices

The wave-1 overlap-unit construction (`X₁²/(X₀X₁)` realizing "`X₁/X₀`" on
`D₊(X₀X₁)`), parametrized by the pair of indices. -/


-- @@ L365-368 verbatim
theorem hXdeg (i : Fin 3) :
    (MvPolynomial.X i : MvPolynomial (Fin 3) ℂ) ∈ 𝒜₃ 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
    (MvPolynomial.isHomogeneous_X ℂ i)


-- @@ L370-373 verbatim
/-- `XᵢXⱼ` is homogeneous of degree 2. -/
theorem hX (i j : Fin 3) :
    (MvPolynomial.X i * MvPolynomial.X j : MvPolynomial (Fin 3) ℂ) ∈ 𝒜₃ 2 :=
  SetLike.mul_mem_graded (hXdeg i) (hXdeg j)


-- @@ L375-378 verbatim
private theorem hXsq (j : Fin 3) :
    (MvPolynomial.X j * MvPolynomial.X j : MvPolynomial (Fin 3) ℂ) ∈
      𝒜₃ ((1 : ℕ) • 2) :=
  (one_smul ℕ 2).symm ▸ SetLike.mul_mem_graded (hXdeg j) (hXdeg j)


-- @@ L380-385 verbatim
/-- The degree-zero fraction `Xⱼ²/(XᵢXⱼ)` on the overlap chart ring —
"`Xⱼ/Xᵢ` where defined". -/
def awayNum (i j : Fin 3) :
    Away 𝒜₃ (MvPolynomial.X i * MvPolynomial.X j) :=
  HomogeneousLocalization.Away.mk 𝒜₃ (hX i j) 1
    (MvPolynomial.X j * MvPolynomial.X j) (hXsq j)


-- @@ L387-391 verbatim
/-- The degree-zero fraction `Xᵢ²/(XᵢXⱼ)` — the inverse of `awayNum`. -/
def awayNumInv (i j : Fin 3) :
    Away 𝒜₃ (MvPolynomial.X i * MvPolynomial.X j) :=
  HomogeneousLocalization.Away.mk 𝒜₃ (hX i j) 1
    (MvPolynomial.X i * MvPolynomial.X i) (hXsq i)


-- @@ L393-403 verbatim
theorem awayNum_mul_awayNumInv (i j : Fin 3) :
    awayNum i j * awayNumInv i j = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one]
  unfold awayNum awayNumInv
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  use 1
  simp only [OneMemClass.coe_one, one_mul, Submonoid.mk_mul_mk]
  ring


-- @@ L405-408 verbatim
/-- The overlap unit of the chart ring `(ℂ[X₀,X₁,X₂]_{XᵢXⱼ})₀`. -/
def awayUnit (i j : Fin 3) :
    (Away 𝒜₃ (MvPolynomial.X i * MvPolynomial.X j))ˣ :=
  Units.mkOfMulEqOne (awayNum i j) (awayNumInv i j) (awayNum_mul_awayNumInv i j)


-- @@ L410-417 verbatim
/-- The chart-ring-to-sections map, restricted to the chart overlap
`chart i ⊓ chart j` (equal to `D₊(XᵢXⱼ)` by `chart_inf`). -/
def overlapRingHom (i j : Fin 3) :
    Away 𝒜₃ (MvPolynomial.X i * MvPolynomial.X j) →+*
      Γ(p2, chart i ⊓ chart j) :=
  RingHom.comp
    ((p2.presheaf.map (homOfLE (le_of_eq (chart_inf i j))).op).hom)
    ((Proj.awayToSection 𝒜₃ (MvPolynomial.X i * MvPolynomial.X j)).hom)


-- @@ L419-422 verbatim
/-- **The realized overlap unit**: a unit of `Γ(p2, chart i ⊓ chart j)`,
the image of `Xⱼ²/(XᵢXⱼ)` under the chart-ring-to-sections map. -/
def overlapUnit (i j : Fin 3) : (Γ(p2, chart i ⊓ chart j))ˣ :=
  Units.map (overlapRingHom i j).toMonoidHom (awayUnit i j)


-- @@ L424-428 verbatim
/-- The overlap unit as a section of the units sheaf `O^*` over
`chart i ⊓ chart j` (additively written). -/
def overlapUnitAb (i j : Fin 3) :
    ((unitsAb p2).obj.obj (op (chart i ⊓ chart j))) :=
  Additive.ofMul (overlapUnit i j)


-- @@ L430-433 verbatim
/-- **The germ of the overlap unit** in the unit group of the function
field (classically "`Xⱼ/Xᵢ`"). -/
def zElt (i j : Fin 3) : (functionFieldUnitsAb p2) :=
  germUnitsHom p2 (genericPoint_mem_chartInf i j) (overlapUnitAb i j)


-- @@ L435-438 verbatim
/-- Receipt (definitional): `zElt` is the germ of the overlap unit. -/
theorem zElt_def (i j : Fin 3) :
    (germUnitsHom p2 (genericPoint_mem_chartInf i j)).hom
      (overlapUnitAb i j) = zElt i j := rfl


-- @@ L440-446 verbatim
/-! ## Part 2(b). The cocycle on the triple overlap

The genuinely new ingredient over wave 1: `zElt 0 1 + zElt 1 2 = zElt 0 2`
(multiplicatively "`(X₁/X₀)·(X₂/X₁) = X₂/X₀`"), proved by restricting the
three overlap units to the triple overlap `D₊(X₀X₁X₂)` and computing in
`ℂ[X₀,X₁,X₂]_{(X₀X₁X₂)}` via the pin's `HomogeneousLocalization.awayMap`
and `Proj.awayMap_awayToSection`. -/


-- @@ L448-450 verbatim
/-- The product `X₀X₁X₂` cutting out the triple overlap. -/
def x3 : MvPolynomial (Fin 3) ℂ :=
  MvPolynomial.X 0 * MvPolynomial.X 1 * MvPolynomial.X 2


-- @@ L452-453 verbatim
theorem hx01 : x3 = (MvPolynomial.X 0 * MvPolynomial.X 1) * MvPolynomial.X 2 :=
  rfl

-- @@ L454-455 verbatim
theorem hx12 : x3 = (MvPolynomial.X 1 * MvPolynomial.X 2) * MvPolynomial.X 0 := by
  unfold x3; ring

-- @@ L456-457 verbatim
theorem hx02 : x3 = (MvPolynomial.X 0 * MvPolynomial.X 2) * MvPolynomial.X 1 := by
  unfold x3; ring


-- @@ L459-464 verbatim
theorem x3_ne_zero : x3 ≠ 0 := by
  unfold x3
  exact mul_ne_zero
    (mul_ne_zero (MvPolynomial.X_ne_zero (R := ℂ) 0)
      (MvPolynomial.X_ne_zero (R := ℂ) 1))
    (MvPolynomial.X_ne_zero (R := ℂ) 2)


-- @@ L466-467 verbatim
/-- The triple overlap `D₊(X₀X₁X₂)`. -/
def T : p2.Opens := Proj.basicOpen 𝒜₃ x3


-- @@ L469-470 verbatim
theorem genericPoint_mem_T : genericPoint p2 ∈ T :=
  genericPoint_mem ⟨botPt, botPt_mem_basicOpen x3_ne_zero⟩


-- @@ L472-476 verbatim
/-- The triple overlap is contained in each pairwise chart overlap. -/
theorem T_le_chartInf {i j k : Fin 3}
    (hx : x3 = (MvPolynomial.X i * MvPolynomial.X j) * MvPolynomial.X k) :
    T ≤ chart i ⊓ chart j :=
  le_of_le_of_eq (Proj.basicOpen_mono _ _ _ ⟨_, hx⟩) (chart_inf i j).symm


-- @@ L478-495 verbatim
/-- **The cocycle in the triple-overlap chart ring**: the images of the
three overlap fractions under the pin's `awayMap` into
`ℂ[X₀,X₁,X₂]_{(X₀X₁X₂)}` satisfy "`(X₁/X₀)·(X₂/X₁) = X₂/X₀`". -/
theorem awayMap_cocycle :
    awayMap 𝒜₃ (hXdeg 2) hx01 (awayNum 0 1) *
      awayMap 𝒜₃ (hXdeg 0) hx12 (awayNum 1 2) =
    awayMap 𝒜₃ (hXdeg 1) hx02 (awayNum 0 2) := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul]
  unfold awayNum HomogeneousLocalization.Away.mk
  rw [HomogeneousLocalization.val_awayMap_mk,
    HomogeneousLocalization.val_awayMap_mk,
    HomogeneousLocalization.val_awayMap_mk]
  rw [Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  use 1
  simp only [OneMemClass.coe_one, one_mul, Submonoid.mk_mul_mk]
  unfold x3
  ring


-- @@ L497-520 verbatim
/-- Restriction of a realized chart-overlap section to the triple overlap
is the section of the `awayMap`-image (the pin's
`Proj.awayMap_awayToSection`, composed with the chart-overlap
identification). -/
theorem overlapRingHom_res {i j k : Fin 3}
    (hx : x3 = (MvPolynomial.X i * MvPolynomial.X j) * MvPolynomial.X k)
    (a : Away 𝒜₃ (MvPolynomial.X i * MvPolynomial.X j)) :
    (p2.presheaf.map (homOfLE (T_le_chartInf hx)).op).hom
        (overlapRingHom i j a) =
      (Proj.awayToSection 𝒜₃ x3).hom (awayMap 𝒜₃ (hXdeg k) hx a) := by
  have hcomp : p2.presheaf.map ((homOfLE (le_of_eq (chart_inf i j))).op) ≫
      p2.presheaf.map ((homOfLE (T_le_chartInf hx)).op) =
      p2.presheaf.map
        ((homOfLE (Proj.basicOpen_mono _ _ _ ⟨_, hx⟩)).op) := by
    rw [← Functor.map_comp]
    rfl
  have h1 := congrArg
    (fun F : Γ(p2, Proj.basicOpen 𝒜₃ (MvPolynomial.X i * MvPolynomial.X j)) ⟶
        Γ(p2, T) =>
      F.hom ((Proj.awayToSection 𝒜₃
        (MvPolynomial.X i * MvPolynomial.X j)).hom a)) hcomp
  have h2 := DFunLike.congr_fun (congrArg CommRingCat.Hom.hom
    (Proj.awayMap_awayToSection (𝒜 := 𝒜₃) (g_deg := hXdeg k) (hx := hx))) a
  exact h1.trans h2.symm


-- @@ L522-527 verbatim
/-- Receipt (definitional): the value of the realized overlap unit is the
image of the overlap fraction. -/
theorem overlapUnit_val (i j : Fin 3) :
    ((overlapUnit i j : (Γ(p2, chart i ⊓ chart j))ˣ) :
        Γ(p2, chart i ⊓ chart j)) =
      overlapRingHom i j (awayNum i j) := rfl


-- @@ L529-544 verbatim
/-- **The cocycle at the level of restricted units of `Γ(p2, T)`**. -/
theorem overlapUnit_res_cocycle :
    Units.map ((p2.presheaf.map (homOfLE (T_le_chartInf hx01)).op).hom :
        Γ(p2, chart 0 ⊓ chart 1) →* Γ(p2, T)) (overlapUnit 0 1) *
      Units.map ((p2.presheaf.map (homOfLE (T_le_chartInf hx12)).op).hom :
        Γ(p2, chart 1 ⊓ chart 2) →* Γ(p2, T)) (overlapUnit 1 2) =
    Units.map ((p2.presheaf.map (homOfLE (T_le_chartInf hx02)).op).hom :
        Γ(p2, chart 0 ⊓ chart 2) →* Γ(p2, T)) (overlapUnit 0 2) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.coe_map, Units.coe_map, Units.coe_map]
  simp only [MonoidHom.coe_coe, overlapUnit_val]
  exact (congrArg₂ (· * ·) (overlapRingHom_res hx01 (awayNum 0 1))
      (overlapRingHom_res hx12 (awayNum 1 2))).trans
    ((map_mul (Proj.awayToSection 𝒜₃ x3).hom _ _).symm.trans
      ((DFunLike.congr_arg (Proj.awayToSection 𝒜₃ x3).hom
        awayMap_cocycle).trans (overlapRingHom_res hx02 (awayNum 0 2)).symm))


-- @@ L546-556 verbatim
/-- Transport of `zElt` along restriction: the germ of the restricted
overlap unit over any smaller open containing the generic point is
`zElt` (the germ-restriction naturality of
`CartierClass.germUnitsHom_naturality`). -/
theorem zElt_eq_germ {W' : p2.Opens} (h' : genericPoint p2 ∈ W')
    (i j : Fin 3) (hle : W' ≤ chart i ⊓ chart j) :
    (germUnitsHom p2 h').hom
        (((unitsAb p2).obj.map (homOfLE hle).op).hom (overlapUnitAb i j)) =
      zElt i j := by
  have h := germUnitsHom_naturality p2 (homOfLE hle).op h'
  exact congrArg (fun F => F.hom (overlapUnitAb i j)) h


-- @@ L558-577 verbatim
/-- **The cocycle of germs**: `zElt 0 1 + zElt 1 2 = zElt 0 2`
(multiplicatively, "`(X₁/X₀)·(X₂/X₁) = X₂/X₀`" in the unit group of the
function field). -/
theorem zElt_cocycle : zElt 0 1 + zElt 1 2 = zElt 0 2 := by
  rw [← zElt_eq_germ genericPoint_mem_T 0 1 (T_le_chartInf hx01),
    ← zElt_eq_germ genericPoint_mem_T 1 2 (T_le_chartInf hx12),
    ← zElt_eq_germ genericPoint_mem_T 0 2 (T_le_chartInf hx02),
    ← map_add]
  refine congrArg _ ?_
  show Additive.ofMul (Units.map ((p2.presheaf.map
        (homOfLE (T_le_chartInf hx01)).op).hom :
        Γ(p2, chart 0 ⊓ chart 1) →* Γ(p2, T)) (overlapUnit 0 1)) +
      Additive.ofMul (Units.map ((p2.presheaf.map
        (homOfLE (T_le_chartInf hx12)).op).hom :
        Γ(p2, chart 1 ⊓ chart 2) →* Γ(p2, T)) (overlapUnit 1 2)) =
    Additive.ofMul (Units.map ((p2.presheaf.map
        (homOfLE (T_le_chartInf hx02)).op).hom :
        Γ(p2, chart 0 ⊓ chart 2) →* Γ(p2, T)) (overlapUnit 0 2))
  rw [← ofMul_mul]
  exact congrArg Additive.ofMul overlapUnit_res_cocycle


-- @@ L579-582 verbatim
/-! ## Part 2(c). Sections of `K^*/O^*` from function-field units

The wave-1 skyscraper-section and cokernel-endgame idioms, generalized
from one fixed element to an arbitrary function-field unit. -/


-- @@ L584-588 verbatim
/-- The section of `K^*` over an open containing the generic point given
by a function-field unit (the skyscraper sections identification). -/
def zSection {W : p2.Opens} (h : genericPoint p2 ∈ W)
    (v : functionFieldUnitsAb p2) : ((KUnitsAb p2).obj.obj (op W)) :=
  eqToHom (KUnitsAb_obj_of_mem p2 h).symm v


-- @@ L590-594 verbatim
/-- The class of a function-field unit in `K^*/O^*` over an open
containing the generic point. -/
def divSection {W : p2.Opens} (h : genericPoint p2 ∈ W)
    (v : functionFieldUnitsAb p2) : ((divisorsAb p2).obj.obj (op W)) :=
  (divisorsπ p2).hom.app (op W) (zSection h v)


-- @@ L596-617 verbatim
/-- Restriction of `divSection` between opens containing the generic
point is `divSection` (the wave-1 naturality-plus-skyscraper argument at
arbitrary opens). -/
theorem divSection_res {U V : (p2.Opens)ᵒᵖ} (f : U ⟶ V)
    (hU : genericPoint p2 ∈ U.unop) (hV : genericPoint p2 ∈ V.unop)
    (v : functionFieldUnitsAb p2) :
    ((divisorsAb p2).obj.map f).hom (divSection hU v) = divSection hV v := by
  have hnat : ((divisorsAb p2).obj.map f).hom
      ((divisorsπ p2).hom.app U (zSection hU v)) =
      (divisorsπ p2).hom.app V
        (((KUnitsAb p2).obj.map f).hom (zSection hU v)) := by
    show ((divisorsπ p2).hom.app U ≫ (divisorsAb p2).obj.map f)
        (zSection hU v) = _
    rw [← (divisorsπ p2).hom.naturality]
    rfl
  have hres : ((KUnitsAb p2).obj.map f).hom (zSection hU v) =
      zSection hV v := by
    rw [KUnitsAb_map_of_mem p2 f hV]
    show (eqToHom (KUnitsAb_obj_of_mem p2 hU).symm ≫ eqToHom _) v = _
    rw [eqToHom_trans]
    rfl
  exact hnat.trans (congrArg ((divisorsπ p2).hom.app V) hres)


-- @@ L619-646 verbatim
/-- **The agreement engine**: two function-field units whose difference is
the germ of a genuine unit of the structure sheaf over `W` have the same
class in `K^*/O^*` over `W` — the image of a unit dies in `K^*/O^*`
sectionwise (`divisorsπ ∘ unitsToK = 0`, the cokernel condition; the
wave-1 overlap argument at arbitrary data). -/
theorem divSection_eq_of_unit {W : p2.Opens} (h : genericPoint p2 ∈ W)
    (v v' : functionFieldUnitsAb p2) (u : ((unitsAb p2).obj.obj (op W)))
    (huv : v = v' + (germUnitsHom p2 h).hom u) :
    divSection h v = divSection h v' := by
  have hz : zSection h v =
      zSection h v' + zSection h ((germUnitsHom p2 h).hom u) := by
    rw [huv]
    exact map_add (eqToHom (KUnitsAb_obj_of_mem p2 h).symm).hom _ _
  have hu : zSection h ((germUnitsHom p2 h).hom u) =
      (unitsToK p2).hom.app (op W) u := by
    rw [unitsToK_app_of_mem p2 h]
    rfl
  have h0 : ((divisorsπ p2).hom.app (op W)).hom
      ((unitsToK p2).hom.app (op W) u) = 0 := by
    have h1 : ((divisorsπ p2).hom.app (op W)).hom
        ((unitsToK p2).hom.app (op W) u) =
        ((unitsToK p2 ≫ divisorsπ p2).hom.app (op W)) u := rfl
    rw [h1, show unitsToK p2 ≫ divisorsπ p2 = 0 from
      cokernel.condition (unitsToK p2)]
    rfl
  show ((divisorsπ p2).hom.app (op W)).hom (zSection h v) = _
  rw [hz, map_add, hu, h0, add_zero]
  rfl


-- @@ L648-652 verbatim
/-! ## Part 2(d). The two line-divisor data

For each line datum, a function `Fin 3 → functionFieldUnitsAb p2` of
transition germs, its pairwise compatibility (through the cocycle), and
the glued global section via the pin's unique-gluing sheaf condition. -/


-- @@ L654-661 verbatim
/-- The transition data of the first line datum (classically the line
`{X₁ = 0}`, transition function "`X₁/X₀`" on the leading chart): `X₁/X₀`
on `chart 0`, trivial on `chart 1`, `(X₂/X₁)⁻¹ = X₁/X₂` on `chart 2`. -/
def lineOneDatum : Fin 3 → functionFieldUnitsAb p2 := fun i =>
  match i with
  | 0 => zElt 0 1
  | 1 => 0
  | 2 => -zElt 1 2


-- @@ L663-670 verbatim
/-- The transition data of the second line datum (classically the line
`{X₂ = 0}`, transition function "`X₂/X₀`" on the leading chart): `X₂/X₀`
on `chart 0`, `X₂/X₁` on `chart 1`, trivial on `chart 2`. -/
def lineTwoDatum : Fin 3 → functionFieldUnitsAb p2 := fun i =>
  match i with
  | 0 => zElt 0 2
  | 1 => zElt 1 2
  | 2 => 0


-- @@ L672-676 verbatim
/-- Drift-guard receipts: the first datum's values, definitionally. -/
theorem lineOneDatum_receipt :
    lineOneDatum 0 = zElt 0 1 ∧ lineOneDatum 1 = 0 ∧
      lineOneDatum 2 = -zElt 1 2 :=
  ⟨rfl, rfl, rfl⟩


-- @@ L678-682 verbatim
/-- Drift-guard receipts: the second datum's values, definitionally. -/
theorem lineTwoDatum_receipt :
    lineTwoDatum 0 = zElt 0 2 ∧ lineTwoDatum 1 = zElt 1 2 ∧
      lineTwoDatum 2 = 0 :=
  ⟨rfl, rfl, rfl⟩


-- @@ L684-689 verbatim
/-- The restriction of an overlap unit to the transposed overlap. -/
def overlapUnitAbSwap (i j : Fin 3) :
    ((unitsAb p2).obj.obj (op (chart j ⊓ chart i))) :=
  ((unitsAb p2).obj.map
      (homOfLE (le_of_eq (inf_comm (chart j) (chart i)))).op).hom
    (overlapUnitAb i j)


-- @@ L691-696 verbatim
/-- The germ of the transposed restriction is still `zElt`. -/
theorem germ_overlapUnitAbSwap (i j : Fin 3) :
    (germUnitsHom p2 (genericPoint_mem_chartInf j i)).hom
      (overlapUnitAbSwap i j) = zElt i j :=
  zElt_eq_germ (genericPoint_mem_chartInf j i) i j
    (le_of_eq (inf_comm (chart j) (chart i)))


-- @@ L698-734 verbatim
/-- **Pairwise agreement data for the first line datum**: on each chart
overlap the difference of transition germs is the germ of a genuine unit
of the structure sheaf.  The `(0,2)`-cases are the cocycle. -/
theorem lineOneDatum_diff (i j : Fin 3) :
    ∃ u : ((unitsAb p2).obj.obj (op (chart i ⊓ chart j))),
      lineOneDatum i = lineOneDatum j +
        (germUnitsHom p2 (genericPoint_mem_chartInf i j)).hom u := by
  match i, j with
  | 0, 0 => exact ⟨0, by rw [map_zero, add_zero]⟩
  | 1, 1 => exact ⟨0, by rw [map_zero, add_zero]⟩
  | 2, 2 => exact ⟨0, by rw [map_zero, add_zero]⟩
  | 0, 1 => exact ⟨overlapUnitAb 0 1, by
      rw [zElt_def]
      show zElt 0 1 = 0 + zElt 0 1
      rw [zero_add]⟩
  | 1, 0 => exact ⟨-overlapUnitAbSwap 0 1, by
      rw [map_neg, germ_overlapUnitAbSwap]
      show (0 : functionFieldUnitsAb p2) = zElt 0 1 + -zElt 0 1
      rw [add_neg_cancel]⟩
  | 1, 2 => exact ⟨overlapUnitAb 1 2, by
      rw [zElt_def]
      show (0 : functionFieldUnitsAb p2) = -zElt 1 2 + zElt 1 2
      rw [neg_add_cancel]⟩
  | 2, 1 => exact ⟨-overlapUnitAbSwap 1 2, by
      rw [map_neg, germ_overlapUnitAbSwap]
      show -zElt 1 2 = 0 + -zElt 1 2
      rw [zero_add]⟩
  | 0, 2 => exact ⟨overlapUnitAb 0 2, by
      rw [zElt_def]
      show zElt 0 1 = -zElt 1 2 + zElt 0 2
      rw [← zElt_cocycle]
      abel⟩
  | 2, 0 => exact ⟨-overlapUnitAbSwap 0 2, by
      rw [map_neg, germ_overlapUnitAbSwap]
      show -zElt 1 2 = zElt 0 1 + -zElt 0 2
      rw [← zElt_cocycle]
      abel⟩


-- @@ L736-771 verbatim
/-- **Pairwise agreement data for the second line datum.**  The
`(0,1)`-cases are the cocycle. -/
theorem lineTwoDatum_diff (i j : Fin 3) :
    ∃ u : ((unitsAb p2).obj.obj (op (chart i ⊓ chart j))),
      lineTwoDatum i = lineTwoDatum j +
        (germUnitsHom p2 (genericPoint_mem_chartInf i j)).hom u := by
  match i, j with
  | 0, 0 => exact ⟨0, by rw [map_zero, add_zero]⟩
  | 1, 1 => exact ⟨0, by rw [map_zero, add_zero]⟩
  | 2, 2 => exact ⟨0, by rw [map_zero, add_zero]⟩
  | 0, 2 => exact ⟨overlapUnitAb 0 2, by
      rw [zElt_def]
      show zElt 0 2 = 0 + zElt 0 2
      rw [zero_add]⟩
  | 2, 0 => exact ⟨-overlapUnitAbSwap 0 2, by
      rw [map_neg, germ_overlapUnitAbSwap]
      show (0 : functionFieldUnitsAb p2) = zElt 0 2 + -zElt 0 2
      rw [add_neg_cancel]⟩
  | 1, 2 => exact ⟨overlapUnitAb 1 2, by
      rw [zElt_def]
      show zElt 1 2 = 0 + zElt 1 2
      rw [zero_add]⟩
  | 2, 1 => exact ⟨-overlapUnitAbSwap 1 2, by
      rw [map_neg, germ_overlapUnitAbSwap]
      show (0 : functionFieldUnitsAb p2) = zElt 1 2 + -zElt 1 2
      rw [add_neg_cancel]⟩
  | 0, 1 => exact ⟨overlapUnitAb 0 1, by
      rw [zElt_def]
      show zElt 0 2 = zElt 1 2 + zElt 0 1
      rw [← zElt_cocycle]
      abel⟩
  | 1, 0 => exact ⟨-overlapUnitAbSwap 0 1, by
      rw [map_neg, germ_overlapUnitAbSwap]
      show zElt 1 2 = zElt 0 2 + -zElt 0 1
      rw [← zElt_cocycle]
      abel⟩


-- @@ L773-775 verbatim
/-- The chart sections of the first line datum. -/
def lineOneSection (i : Fin 3) : ((divisorsAb p2).obj.obj (op (chart i))) :=
  divSection (genericPoint_mem_chart i) (lineOneDatum i)


-- @@ L777-779 verbatim
/-- The chart sections of the second line datum. -/
def lineTwoSection (i : Fin 3) : ((divisorsAb p2).obj.obj (op (chart i))) :=
  divSection (genericPoint_mem_chart i) (lineTwoDatum i)


-- @@ L781-790 verbatim
/-- The first line datum is compatible on all chart overlaps. -/
theorem lineOneCompatible :
    TopCat.Presheaf.IsCompatible (divisorsAb p2).obj chart lineOneSection := by
  intro i j
  obtain ⟨u, hu⟩ := lineOneDatum_diff i j
  exact (divSection_res (Opens.infLELeft (chart i) (chart j)).op
      (genericPoint_mem_chart i) (genericPoint_mem_chartInf i j) _).trans
    ((divSection_eq_of_unit (genericPoint_mem_chartInf i j) _ _ u hu).trans
      (divSection_res (Opens.infLERight (chart i) (chart j)).op
        (genericPoint_mem_chart j) (genericPoint_mem_chartInf i j) _).symm)


-- @@ L792-801 verbatim
/-- The second line datum is compatible on all chart overlaps. -/
theorem lineTwoCompatible :
    TopCat.Presheaf.IsCompatible (divisorsAb p2).obj chart lineTwoSection := by
  intro i j
  obtain ⟨u, hu⟩ := lineTwoDatum_diff i j
  exact (divSection_res (Opens.infLELeft (chart i) (chart j)).op
      (genericPoint_mem_chart i) (genericPoint_mem_chartInf i j) _).trans
    ((divSection_eq_of_unit (genericPoint_mem_chartInf i j) _ _ u hu).trans
      (divSection_res (Opens.infLERight (chart i) (chart j)).op
        (genericPoint_mem_chart j) (genericPoint_mem_chartInf i j) _).symm)


-- @@ L803-811 verbatim
/-- **The unique-gluing statement for the first line datum** (the pin's
`TopCat.Sheaf.existsUnique_gluing'` over the three-chart cover). -/
theorem lineOneGlue :
    ∃! s : ((divisorsAb p2).obj.obj (op (⊤ : p2.Opens))),
      ∀ i : Fin 3,
        (divisorsAb p2).obj.map (homOfLE le_top).op s = lineOneSection i :=
  TopCat.Sheaf.existsUnique_gluing' (divisorsAb p2) chart (⊤ : p2.Opens)
    (fun _ => homOfLE le_top) iSup_chart_eq_top.ge lineOneSection
    lineOneCompatible


-- @@ L813-820 verbatim
/-- **The unique-gluing statement for the second line datum.** -/
theorem lineTwoGlue :
    ∃! s : ((divisorsAb p2).obj.obj (op (⊤ : p2.Opens))),
      ∀ i : Fin 3,
        (divisorsAb p2).obj.map (homOfLE le_top).op s = lineTwoSection i :=
  TopCat.Sheaf.existsUnique_gluing' (divisorsAb p2) chart (⊤ : p2.Opens)
    (fun _ => homOfLE le_top) iSup_chart_eq_top.ge lineTwoSection
    lineTwoCompatible


-- @@ L822-824 verbatim
/-- The glued global datum of the first line. -/
def lineOneTop : ((divisorsAb p2).obj.obj (op (⊤ : p2.Opens))) :=
  lineOneGlue.exists.choose


-- @@ L826-828 verbatim
/-- The glued global datum of the second line. -/
def lineTwoTop : ((divisorsAb p2).obj.obj (op (⊤ : p2.Opens))) :=
  lineTwoGlue.exists.choose


-- @@ L830-835 verbatim
/-- Receipt: the glued datum of the first line restricts to its chart
sections. -/
theorem lineOneTop_restrict (i : Fin 3) :
    (divisorsAb p2).obj.map (homOfLE le_top).op lineOneTop =
      lineOneSection i :=
  lineOneGlue.exists.choose_spec i


-- @@ L837-842 verbatim
/-- Receipt: the glued datum of the second line restricts to its chart
sections. -/
theorem lineTwoTop_restrict (i : Fin 3) :
    (divisorsAb p2).obj.map (homOfLE le_top).op lineTwoTop =
      lineTwoSection i :=
  lineTwoGlue.exists.choose_spec i


-- @@ L844-850 verbatim
/-- Receipt (uniqueness): any global section restricting to the first
line's chart sections is the glued datum. -/
theorem lineOneTop_unique (s : ((divisorsAb p2).obj.obj (op (⊤ : p2.Opens))))
    (hs : ∀ i : Fin 3,
      (divisorsAb p2).obj.map (homOfLE le_top).op s = lineOneSection i) :
    s = lineOneTop :=
  lineOneGlue.unique hs (fun i => lineOneTop_restrict i)


-- @@ L852-858 verbatim
/-- Receipt (uniqueness): any global section restricting to the second
line's chart sections is the glued datum. -/
theorem lineTwoTop_unique (s : ((divisorsAb p2).obj.obj (op (⊤ : p2.Opens))))
    (hs : ∀ i : Fin 3,
      (divisorsAb p2).obj.map (homOfLE le_top).op s = lineTwoSection i) :
    s = lineTwoTop :=
  lineTwoGlue.unique hs (fun i => lineTwoTop_restrict i)


-- @@ L860-870 verbatim
/-- **The first line-divisor datum**: the Cartier divisor datum on the
projective plane glued from the transition data "`X₁/X₀`" (the class of
`zElt 0 1` over `chart 0`, the trivial class over `chart 1`, the class of
`-zElt 1 2` over `chart 2`).

Classically this datum presents the coordinate line `{X₁ = 0}`; **no such
identification is stated**: no Weil divisor is attached to it, no order
of vanishing is computed, and `lineOne` is **not** claimed to be
nonzero. -/
def lineOne : CDiv p2 :=
  (cdivSectionsEquiv p2).symm lineOneTop


-- @@ L872-880 verbatim
/-- **The second line-divisor datum**: glued from the transition data
"`X₂/X₀`" (the class of `zElt 0 2` over `chart 0`, the class of
`zElt 1 2` over `chart 1`, the trivial class over `chart 2`).

Classically this datum presents the coordinate line `{X₂ = 0}`; **no such
identification is stated**, and `lineTwo` is **not** claimed to be
nonzero, nor distinct from `lineOne` as an element of `CDiv p2`. -/
def lineTwo : CDiv p2 :=
  (cdivSectionsEquiv p2).symm lineTwoTop


-- @@ L882-882 verbatim
/-! ## Part 3. The divisor classes and the cycle classes, by construction -/


-- @@ L884-888 verbatim
/-- The class of `lineOne` in `H¹(p2, O^*)` — an application of the
shipped connecting-map machinery.  **Not claimed to be nonzero.**
(`H¹(X, O^*)` is *classically* the Picard group; no such identification
is claimed.) -/
def lineOneClass : unitsH1 p2 := cdivClass p2 lineOne


-- @@ L890-892 verbatim
/-- The class of `lineTwo` in `H¹(p2, O^*)`.  **Not claimed to be
nonzero.** -/
def lineTwoClass : unitsH1 p2 := cdivClass p2 lineTwo


-- @@ L894-896 verbatim
/-- The first line datum moved to the small affine Zariski site (the home
of the first Chern class map), along the shipped site equivalence. -/
def lineOneAffine : CDivAffine p2 := cdivSiteEquiv p2 lineOne


-- @@ L898-899 verbatim
/-- The second line datum on the small affine Zariski site. -/
def lineTwoAffine : CDivAffine p2 := cdivSiteEquiv p2 lineTwo


-- @@ L901-908 verbatim
/-- **The divisor-level cycle class of the first line datum in
`F¹ ℍ²_dR(p2)`** — the shipped `cdivCycleClassC` at the structure
morphism, evaluated at `lineOneAffine`.  A pure application: the codomain
of the shipped map is the filtration step, so membership is by
construction (`lineOneCycleClass_mem`).  **Not claimed to be nonzero**,
and the filtration is the naive (brutal-truncation) filtration. -/
def lineOneCycleClass : (hodgeFiltrationDRC structMor 1 2) :=
  cdivCycleClassC structMor lineOneAffine


-- @@ L910-913 verbatim
/-- The divisor-level cycle class of the second line datum in
`F¹ ℍ²_dR(p2)`.  **Not claimed to be nonzero.** -/
def lineTwoCycleClass : (hodgeFiltrationDRC structMor 1 2) :=
  cdivCycleClassC structMor lineTwoAffine


-- @@ L915-923 verbatim
/-- **`F¹`-membership, by construction**: the underlying `ℍ²_dR(p2)`
class of `lineOneCycleClass` lies in the first step of the naive
filtration — the witness is the codomain of the shipped map itself
(`CartierClass.cdivCycleClass_mem`); a definitional receipt, not a
computation, and it does **not** assert that the class is nonzero. -/
theorem lineOneCycleClass_mem :
    (lineOneCycleClass : hyperHdR (cRingHom structMor) 2) ∈
      hodgeFiltrationDR (cRingHom structMor) 1 2 :=
  cdivCycleClass_mem p2 (cRingHom structMor) lineOneAffine


-- @@ L925-929 verbatim
/-- **`F¹`-membership for the second line datum, by construction.** -/
theorem lineTwoCycleClass_mem :
    (lineTwoCycleClass : hyperHdR (cRingHom structMor) 2) ∈
      hodgeFiltrationDR (cRingHom structMor) 1 2 :=
  cdivCycleClass_mem p2 (cRingHom structMor) lineTwoAffine


-- @@ L931-937 verbatim
/-! ## Part 4. The two-line paired class, by construction

**The point of the module.**  Every ceiling of `HodgePilot.CyclePairing`
applies verbatim: the pairing is a constructed pairing-shaped assignment;
it is **not** the cup product, it is **not** identified with any
classical intersection pairing or intersection number, and **no
canonicity is claimed** for the exhibited choices. -/


-- @@ L939-941 verbatim
/-- The divisor data of `lineOne` for the pairing's first slot (the
shipped `pairData` at `lineOne`). -/
def linesPairData : pairAnchor p2 ⟶ divisorsMod p2 := pairData p2 lineOne


-- @@ L943-947 verbatim
/-- The second-slot input of the landed pairing at `lineTwo`: the moved
divisor class (`CycCarrier.cdivClass_moveIn` identifies it with the
transported `cdivClass p2 lineTwo`). -/
def linesSecondSlot : Abelian.Ext (pairAnchor p2) (unitsMod p2) 1 :=
  (cdivMoveIn p2 lineTwo).comp (cartierδMod p2) (zero_add 1)


-- @@ L949-962 verbatim
/-- **The paired class of the two line data** — the shipped
`pairedDivClass` at the pair `(lineOne, lineTwo)` of **distinct glue
data**: the honest `p = 2` pairing-shaped value on the projective plane.

Classically, two distinct lines in the projective plane meet in exactly
one point (Bézout for two degree-1 curves; Hartshorne, *Algebraic
Geometry*, I.7.8) — a **citation-only referent** recording why the
reviews routed positive product tests to this object; no intersection,
no intersection number, and no nonvanishing is computed, claimed, or
approached here.  An application of shipped machinery; **not claimed to
be nonzero**; not the cup product; not any classical intersection
pairing; no canonicity claimed. -/
def linesPairedDivClass : Abelian.Ext (pairAnchor p2) (pairedTarget p2) 2 :=
  pairedDivClass p2 lineOne lineTwo


-- @@ L964-967 verbatim
/-- Drift-guard receipt: the paired class is the wave-1 `pairedDivClass`
spelling, evaluated at the two line data. -/
theorem linesPairedDivClass_receipt :
    linesPairedDivClass = pairedDivClass p2 lineOne lineTwo := rfl


-- @@ L969-984 verbatim
/-- **The landed two-line pairing in `F²` of the degree-4
hypercohomology** — the shipped `pairedClassInto` at the structure
morphism, evaluated at the divisor data of `lineOne` in the first slot
and the moved class of `lineTwo` in the second.  A pure application: the
codomain is the filtration subtype, so membership is by construction
(`linesPairedInto_mem`).  **Not claimed to be nonzero**; the filtration
is the naive (brutal-truncation) filtration; not the cup product; not
any classical intersection pairing; no canonicity claimed.  (On the
projective line the classical expectation for the analogous degree-4
value is zero, `H⁴(ℙ¹) = 0`; on the plane the classical expectation is
nonzero — **neither expectation is formalized, computed, or claimed
here**; nonvanishing is a separately-priced, probe-gated rung.) -/
def linesPairedInto :
    (affineZHodgeFiltration p2 (pairAnchorAffine p2)
      (reindexZ (deRhamSheafZComplexN (cRingHom structMor))) 2 4) :=
  pairedClassInto (cRingHom structMor) linesPairData linesSecondSlot


-- @@ L986-996 verbatim
/-- **`F²`-membership, by construction**: the underlying degree-4
hypercohomology class of `linesPairedInto` lies in the second step of the
naive filtration — the witness is the codomain of the shipped landing
itself (`CyclePairing.pairedIntoFull_mem`); a definitional receipt, not a
computation, and it does **not** assert that the class is nonzero. -/
theorem linesPairedInto_mem :
    (linesPairedInto : affineZHyperH p2 (pairAnchorAffine p2)
        (reindexZ (deRhamSheafZComplexN (cRingHom structMor))) 4) ∈
      affineZHodgeFiltration p2 (pairAnchorAffine p2)
        (reindexZ (deRhamSheafZComplexN (cRingHom structMor))) 2 4 :=
  linesPairedInto.2


-- @@ L998-998 verbatim
end ProjectivePlane


-- @@ L1000-1000 verbatim
end HodgePilot


-- @@ L1002-1002 verbatim
end
