import HodgePilot.CyclePairing


-- @@ L3-83 verbatim
/-! # The projective line: the golden-path object, its point-divisor datum,
# and their classes

The first named variety of this development (golden-path wave 1).  This
module constructs, for `p1 := Proj ℂ[X₀, X₁]` (the pin's only ℙⁿ-shaped
object; standard grading):

**Part 1 — the object and its instances.**

* `p1 : Scheme.{0}` and the structure morphism
  `structMor : p1 ⟶ Spec ℂ` — the pin's `Proj.toSpecZero` composed with
  `Spec` of the grade-zero identification `gradeZeroEquiv : ℂ ≃+* 𝒜 0`
  (degree-zero homogeneous polynomials are the constants);
* `AlgebraicGeometry.IsProper structMor` — the pin instance
  `IsProper (Proj.toSpecZero 𝒜)`, gated on the `Algebra.FiniteType`
  instance proved here, transported along the `Spec` of the iso;
* `IsIntegral p1` — irreducibility by the generic point (`botPoint`, the
  zero ideal) and reducedness stalkwise (stalks are homogeneous
  localizations of a polynomial ring, hence domains);
* `AlgebraicGeometry.IsNoetherian p1` — locally Noetherian along
  `toSpecZero` over the Noetherian base, compact by quasi-compactness of
  `toSpecZero`.

**Part 2 — the divisor datum and its classes (all BY CONSTRUCTION).**

* `dinf : CDiv p1` — a global Cartier divisor datum glued, via the pin's
  Mayer–Vietoris sheaf condition
  (`MayerVietorisSquare.SheafCondition.glue`, at the Type-valued `forget`
  spelling), from the class of a rational function over the chart
  `D₊(X₀)` and the trivial class over the chart `D₊(X₁)`; the rational
  function is the germ of the overlap unit `X₁²/(X₀X₁)` (the unit
  realizing "`X₁/X₀`" on `D₊(X₀X₁) = D₊(X₀) ⊓ D₊(X₁)`), so the overlap
  agreement is exactly "the image of a unit dies in `K^*/O^*`",
  sectionwise.  Classically this datum presents the divisor of a point;
  **no such identification is stated**: no Weil divisor is attached to it
  (`CartierClass.CartierWeilComparison` remains an unproved named
  `Prop`), no order of vanishing is computed, and `dinf` is **not**
  claimed to be nonzero;
* `dinfClass = cdivClass p1 dinf` in `H¹(p1, O^*)` and
  `dinfCycleClass = cdivCycleClassC structMor (cdivSiteEquiv p1 dinf)`
  in `F¹ ℍ²_dR(p1)` — pure applications of the shipped divisor-level
  cycle class machinery; the `F¹`-membership receipt
  `dinfCycleClass_mem` holds **by construction** (the codomain of the
  shipped map is the filtration step; `CartierClass.cdivCycleClass_mem`);
* `dinfPairedDivClass = pairedDivClass p1 dinf dinf` and the landed
  `dinfPairedInto` in `F²` of the degree-4 hypercohomology — pure
  applications of the shipped `CyclePairing` machinery at the pair
  `(dinf, dinf)`; the `F²`-membership receipt `dinfPairedInto_mem` holds
  **by construction** (`CyclePairing.pairedIntoFull_mem`).  As in
  `HodgePilot.CyclePairing`, whose ceilings apply verbatim: this is a
  constructed pairing-shaped assignment evaluated at one input pair; it
  is **not** the cup product, it is **not** identified with any classical
  intersection pairing, and **no canonicity is claimed** for the
  exhibited choices.

## Claim discipline

**No nonvanishing of any class is claimed anywhere in this module**: not
of `dinf`, not of `dinfClass`, not of `dinfCycleClass`, not of
`dinfPairedDivClass` — every one of them could, for all this module
proves, be zero.  (Nonvanishing on `p1` is downstream work with its own
required machinery; nothing here starts it.)  All membership statements
are **by construction** — the shipped maps land in the filtration
subtypes by their codomains — and are labelled as such; they are
definitional receipts, not computations.  No comparison map is claimed
to be an isomorphism or quasi-isomorphism, and no comparison theorem
with any other cohomology theory is stated, implied, or approached.  The
filtrations are the **naive** (brutal-truncation) filtrations
throughout.  `H¹(p1, O^*)` is *classically* the Picard group; no Picard
group is constructed and no such identification is claimed.  Nothing
here makes the Hodge conjecture statable.

## Credits

`Proj`, its charts, `toSpecZero` and its properness are Andrew Yang's
and Jujian Zhang's Mathlib infrastructure; the Mayer–Vietoris square and
its sheaf condition are Joël Riou's; homogeneous localizations are
Jujian Zhang's; the Cartier-divisor machinery consumed here is
`HodgePilot.CartierClass`/`HodgePilot.CycCarrier`, and the pairing is
`HodgePilot.CyclePairing`.
-/


-- @@ L85-85 verbatim
set_option maxHeartbeats 1000000

-- @@ L86-86 verbatim
set_option synthInstance.maxHeartbeats 1000000


-- @@ L88-88 verbatim
noncomputable section


-- @@ L90-90 verbatim
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

-- @@ L91-91 verbatim
open AlgebraicGeometry HomogeneousLocalization


-- @@ L93-93 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L95-95 verbatim
namespace HodgePilot


-- @@ L97-97 verbatim
namespace ProjectiveLine


-- @@ L99-99 verbatim
open HodgePilot.DLog HodgePilot.CartierClass HodgePilot.CycCarrier

-- @@ L100-100 verbatim
open HodgePilot.CyclePairing HodgePilot.Hyper HodgePilot.DeRhamPresheaf

-- @@ L101-101 verbatim
open HodgePilot.DeRhamSheaf HodgePilot.DeRhamWedgeChain


-- @@ L103-104 verbatim
/-- The standard grading of `ℂ[X₀, X₁]` by total degree. -/
local notation "𝒜₂" => MvPolynomial.homogeneousSubmodule (Fin 2) ℂ


-- @@ L106-106 verbatim
/-! ## Part 1(pre). The object -/


-- @@ L108-111 verbatim
/-- **The projective line** `ℙ¹ = Proj ℂ[X₀, X₁]` (standard grading), at
`Scheme.{0}`.  The pin's `Proj` is the only ℙⁿ-shaped scheme in this
Mathlib; a definition, not a claim. -/
abbrev p1 : Scheme.{0} := Proj 𝒜₂


-- @@ L113-118 verbatim
/-! ## Part 1(a). The `Algebra.FiniteType` gate

The pin instance `IsProper (Proj.toSpecZero 𝒜)` is gated only on
`Algebra.FiniteType (𝒜 0) A`; this section closes the gate via
`Algebra.FiniteType.of_restrictScalars_finiteType` and the grade-zero
scalar tower. -/


-- @@ L120-124 verbatim
instance instIsScalarTowerGradeZero :
    IsScalarTower ℂ (𝒜₂ 0) (MvPolynomial (Fin 2) ℂ) :=
  IsScalarTower.of_algebraMap_eq (R := ℂ) (S := 𝒜₂ 0)
    (A := MvPolynomial (Fin 2) ℂ) fun c => by
      rw [SetLike.GradeZero.algebraMap_apply, SetLike.GradeZero.coe_algebraMap]


-- @@ L126-132 verbatim
/-- The `FiniteType` gate of the pin's `Proj.toSpecZero` instances:
`ℂ[X₀, X₁]` is of finite type over its degree-zero part (restriction of
scalars along `ℂ → 𝒜 0` from finite type over `ℂ`). -/
instance instFiniteTypeGradeZero :
    Algebra.FiniteType (𝒜₂ 0) (MvPolynomial (Fin 2) ℂ) :=
  Algebra.FiniteType.of_restrictScalars_finiteType ℂ (𝒜₂ 0)
    (MvPolynomial (Fin 2) ℂ)


-- @@ L134-137 verbatim
/-- Receipt: with the gate closed, the pin's properness instance for the
structure map to `Spec (𝒜 0)` synthesizes with no hypothesized binder. -/
theorem isProper_toSpecZero : AlgebraicGeometry.IsProper (Proj.toSpecZero 𝒜₂) :=
  inferInstance


-- @@ L139-139 verbatim
/-! ## Part 1(b). The grade-zero identification and the structure morphism -/


-- @@ L141-152 verbatim
theorem gradeZero_algebraMap_bijective :
    Function.Bijective (algebraMap ℂ (𝒜₂ 0)) := by
  constructor
  · intro a b hab
    exact MvPolynomial.C_injective (Fin 2) ℂ (congrArg Subtype.val hab)
  · intro x
    have hx : (x : MvPolynomial (Fin 2) ℂ) ∈
        (1 : Submodule ℂ (MvPolynomial (Fin 2) ℂ)) := by
      rw [← MvPolynomial.homogeneousSubmodule_zero]
      exact x.2
    obtain ⟨c, hc⟩ := Submodule.mem_one.mp hx
    exact ⟨c, Subtype.ext hc⟩


-- @@ L154-157 verbatim
/-- **Degree-zero homogeneous polynomials are the constants**:
`ℂ ≃+* (𝒜 0)` via the algebra map. -/
def gradeZeroEquiv : ℂ ≃+* (𝒜₂ 0) :=
  RingEquiv.ofBijective (algebraMap ℂ (𝒜₂ 0)) gradeZero_algebraMap_bijective


-- @@ L159-163 verbatim
/-- **The structure morphism of the projective line**: the pin's
`Proj.toSpecZero` followed by `Spec` of the grade-zero identification.
One exhibited choice of presentation; no canonicity is claimed. -/
def structMor : p1 ⟶ Spec (CommRingCat.of ℂ) :=
  Proj.toSpecZero 𝒜₂ ≫ Spec.map (gradeZeroEquiv.toCommRingCatIso.hom)


-- @@ L165-175 verbatim
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
    (Proj.toSpecZero 𝒜₂ ≫ Spec.map (gradeZeroEquiv.toCommRingCatIso.hom)))


-- @@ L177-177 verbatim
/-! ## Part 1(c). Integrality -/


-- @@ L179-193 verbatim
/-- The zero ideal of `ℂ[X₀, X₁]` as a point of the projective spectrum:
prime (the ring is a domain) and relevant (`X₀` is a nonzero element of
the irrelevant ideal). -/
def botPoint : ProjectiveSpectrum 𝒜₂ :=
  ⟨⊥, by rw [HomogeneousIdeal.toIdeal_bot]; exact Ideal.isPrime_bot,
    fun hle => by
      have hmem : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ∈
          HomogeneousIdeal.irrelevant 𝒜₂ :=
        HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos
          ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
            (MvPolynomial.isHomogeneous_X ℂ 0))
      have h0 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ∈
          ((⊥ : HomogeneousIdeal 𝒜₂) : Set (MvPolynomial (Fin 2) ℂ)) := hle hmem
      rw [HomogeneousIdeal.coe_bot] at h0
      exact MvPolynomial.X_ne_zero (R := ℂ) 0 (Set.mem_zero.mp h0)⟩


-- @@ L195-203 verbatim
/-- Every point of the projective spectrum lies in the closure of the
zero ideal: the space is the closure of a point. -/
theorem closure_botPoint :
    closure ({botPoint} : Set (ProjectiveSpectrum 𝒜₂)) = Set.univ := by
  rw [← ProjectiveSpectrum.zeroLocus_vanishingIdeal_eq_closure,
    ProjectiveSpectrum.vanishingIdeal_singleton,
    show botPoint.asHomogeneousIdeal = (⊥ : HomogeneousIdeal 𝒜₂) from rfl,
    HomogeneousIdeal.coe_bot, ← Set.singleton_zero]
  exact ProjectiveSpectrum.zeroLocus_singleton_zero 𝒜₂


-- @@ L205-213 verbatim
/-- The projective line is an irreducible space (its topology is the
closure of the zero-ideal point). -/
instance instIrreducibleSpaceP1 : IrreducibleSpace p1 where
  isPreirreducible_univ := by
    have h : IsIrreducible (closure ({botPoint} : Set (ProjectiveSpectrum 𝒜₂))) :=
      isIrreducible_singleton.closure
    rw [closure_botPoint] at h
    exact h.2
  toNonempty := ⟨botPoint⟩


-- @@ L215-230 verbatim
/-- The stalks of the projective line are integral domains: they are
homogeneous localizations of `ℂ[X₀, X₁]` at relevant primes, embedded by
`HomogeneousLocalization.val` in localizations of a domain at submonoids
of nonzerodivisors. -/
instance instIsDomainStalkP1 (x : p1) : IsDomain (p1.presheaf.stalk x) := by
  haveI : IsDomain (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) :=
    IsLocalization.isDomain_localization
      (Ideal.primeCompl_le_nonZeroDivisors _)
  haveI : IsDomain (AtPrime 𝒜₂ x.asHomogeneousIdeal.toIdeal) :=
    Function.Injective.isDomain
      (algebraMap (AtPrime 𝒜₂ x.asHomogeneousIdeal.toIdeal)
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl))
      (HomogeneousLocalization.val_injective _)
  exact Function.Injective.isDomain
    ((Proj.stalkIso 𝒜₂ x).commRingCatIsoToRingEquiv.toRingHom)
    (Proj.stalkIso 𝒜₂ x).commRingCatIsoToRingEquiv.injective


-- @@ L232-233 verbatim
instance instIsReducedP1 : IsReduced p1 :=
  isReduced_of_isReduced_stalk p1


-- @@ L235-238 verbatim
/-- **The projective line is an integral scheme** (irreducible and
reduced; the pin's `isIntegral_of_irreducibleSpace_of_isReduced`). -/
instance instIsIntegralP1 : IsIntegral p1 :=
  isIntegral_of_irreducibleSpace_of_isReduced p1


-- @@ L240-240 verbatim
/-! ## Part 1(d). Noetherianity -/


-- @@ L242-243 verbatim
instance instIsNoetherianRingGradeZero : IsNoetherianRing (𝒜₂ 0) :=
  isNoetherianRing_of_ringEquiv ℂ gradeZeroEquiv


-- @@ L245-246 verbatim
instance instIsLocallyNoetherianP1 : IsLocallyNoetherian p1 :=
  LocallyOfFiniteType.isLocallyNoetherian (Proj.toSpecZero 𝒜₂)


-- @@ L248-249 verbatim
instance instCompactSpaceP1 : CompactSpace p1 :=
  QuasiCompact.compactSpace_of_compactSpace (Proj.toSpecZero 𝒜₂)


-- @@ L251-255 verbatim
/-- **The projective line is a Noetherian scheme** (locally Noetherian
along the pin's `LocallyOfFiniteType (Proj.toSpecZero 𝒜)` over the
Noetherian base `𝒜 0 ≃ ℂ`, compact by the pin's
`QuasiCompact (Proj.toSpecZero 𝒜)`). -/
instance instIsNoetherianP1 : AlgebraicGeometry.IsNoetherian p1 where


-- @@ L257-257 verbatim
/-! ## Part 2(a). The charts, the overlap unit, and the divisor datum -/


-- @@ L259-260 verbatim
/-- The chart `D₊(X₀)`. -/
abbrev U0 : p1.Opens := Proj.basicOpen 𝒜₂ (MvPolynomial.X 0)


-- @@ L262-263 verbatim
/-- The chart `D₊(X₁)`. -/
abbrev U1 : p1.Opens := Proj.basicOpen 𝒜₂ (MvPolynomial.X 1)


-- @@ L265-287 verbatim
/-- The two charts cover the projective line. -/
theorem U0_sup_U1 : U0 ⊔ U1 = ⊤ := by
  have h : (⨆ i : Fin 2, Proj.basicOpen 𝒜₂ (MvPolynomial.X i)) = ⊤ :=
    Proj.iSup_basicOpen_eq_top' 𝒜₂
      (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℂ)
      (fun i => ⟨1, (MvPolynomial.mem_homogeneousSubmodule _ _).mpr
        (MvPolynomial.isHomogeneous_X ℂ i)⟩)
      (top_le_iff.mp fun a _ => by
        have ha : a ∈ Algebra.adjoin ℂ
            (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℂ)) := by
          rw [MvPolynomial.adjoin_range_X]; trivial
        have hle : Algebra.adjoin ℂ
            (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℂ)) ≤
            Subalgebra.restrictScalars ℂ (Algebra.adjoin (𝒜₂ 0)
              (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℂ))) :=
          Algebra.adjoin_le fun s hs => Algebra.subset_adjoin hs
        exact (Subalgebra.mem_restrictScalars ℂ).mp (hle ha))
  rw [← h]
  exact le_antisymm
    (sup_le
      (le_iSup (fun i : Fin 2 => Proj.basicOpen 𝒜₂ (MvPolynomial.X i)) 0)
      (le_iSup (fun i : Fin 2 => Proj.basicOpen 𝒜₂ (MvPolynomial.X i)) 1))
    (iSup_le (Fin.forall_fin_two.mpr ⟨le_sup_left, le_sup_right⟩))


-- @@ L289-292 verbatim
/-- The chart overlap is the basic open of `X₀X₁`. -/
theorem U0_inf_U1 :
    U0 ⊓ U1 = Proj.basicOpen 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) :=
  (Proj.basicOpen_mul 𝒜₂ (MvPolynomial.X 0) (MvPolynomial.X 1)).symm


-- @@ L294-297 verbatim
/-- The zero-ideal point, typed at the scheme carrier (one fixed coercion
point, so that every membership statement below elaborates at the scheme's
`SetLike` instance). -/
def botPt : Proj 𝒜₂ := botPoint


-- @@ L299-305 verbatim
theorem botPt_mem_basicOpen {f : MvPolynomial (Fin 2) ℂ} (hf : f ≠ 0) :
    botPt ∈ Proj.basicOpen 𝒜₂ f := by
  rw [Proj.mem_basicOpen]
  intro h
  have h' : f ∈ ((⊥ : HomogeneousIdeal 𝒜₂) : Set (MvPolynomial (Fin 2) ℂ)) := h
  rw [HomogeneousIdeal.coe_bot] at h'
  exact hf (Set.mem_zero.mp h')


-- @@ L307-311 verbatim
/-- The generic point lies in every nonempty open (`IsGenericPoint`). -/
theorem genericPoint_mem {W : p1.Opens} (hW : (W : Set p1).Nonempty) :
    genericPoint p1 ∈ W := by
  refine ((genericPoint_spec p1).mem_open_set_iff W.isOpen).mpr ?_
  simpa using hW


-- @@ L313-314 verbatim
theorem genericPoint_mem_U0 : genericPoint p1 ∈ U0 :=
  genericPoint_mem ⟨botPt, botPt_mem_basicOpen (MvPolynomial.X_ne_zero 0)⟩


-- @@ L316-320 verbatim
theorem genericPoint_mem_U01 : genericPoint p1 ∈ U0 ⊓ U1 :=
  genericPoint_mem ⟨botPt, by
    rw [U0_inf_U1]
    exact botPt_mem_basicOpen
      (mul_ne_zero (MvPolynomial.X_ne_zero 0) (MvPolynomial.X_ne_zero 1))⟩


-- @@ L322-322 verbatim
section OverlapUnit


-- @@ L324-331 verbatim
/-- `X₀X₁` is homogeneous of degree 2. -/
theorem hX01 :
    (MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) ∈ 𝒜₂ 2 :=
  SetLike.mul_mem_graded
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (MvPolynomial.isHomogeneous_X ℂ 0))
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (MvPolynomial.isHomogeneous_X ℂ 1))


-- @@ L333-340 verbatim
private theorem hXsq (i : Fin 2) :
    (MvPolynomial.X i * MvPolynomial.X i : MvPolynomial (Fin 2) ℂ) ∈
      𝒜₂ ((1 : ℕ) • 2) :=
  (one_smul ℕ 2).symm ▸ SetLike.mul_mem_graded
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (MvPolynomial.isHomogeneous_X ℂ i))
    ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr
      (MvPolynomial.isHomogeneous_X ℂ i))


-- @@ L342-346 verbatim
/-- The degree-zero fraction `X₁²/(X₀X₁)` on the overlap chart ring —
"`X₁/X₀` where defined". -/
def awayNum : Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) :=
  HomogeneousLocalization.Away.mk 𝒜₂ hX01 1
    (MvPolynomial.X 1 * MvPolynomial.X 1) (hXsq 1)


-- @@ L348-351 verbatim
/-- The degree-zero fraction `X₀²/(X₀X₁)` — the inverse of `awayNum`. -/
def awayNumInv : Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) :=
  HomogeneousLocalization.Away.mk 𝒜₂ hX01 1
    (MvPolynomial.X 0 * MvPolynomial.X 0) (hXsq 0)


-- @@ L353-362 verbatim
theorem awayNum_mul_awayNumInv : awayNum * awayNumInv = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_one]
  unfold awayNum awayNumInv
  rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
    Localization.mk_mul, ← Localization.mk_one, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  use 1
  simp only [OneMemClass.coe_one, one_mul, Submonoid.mk_mul_mk]
  ring


-- @@ L364-366 verbatim
/-- The overlap unit of the chart ring `(ℂ[X₀,X₁]_{X₀X₁})₀`. -/
def awayUnit : (Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1))ˣ :=
  Units.mkOfMulEqOne awayNum awayNumInv awayNum_mul_awayNumInv


-- @@ L368-374 verbatim
/-- The chart-ring-to-sections map, restricted to the chart overlap
`U0 ⊓ U1` (equal to `D₊(X₀X₁)` by `U0_inf_U1`). -/
def overlapRingHom :
    Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) →+* Γ(p1, U0 ⊓ U1) :=
  RingHom.comp
    ((p1.presheaf.map (homOfLE (le_of_eq U0_inf_U1)).op).hom)
    ((Proj.awayToSection 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)).hom)


-- @@ L376-379 verbatim
/-- **The realized overlap unit**: a unit of `Γ(p1, U0 ⊓ U1)`, the image
of `X₁²/(X₀X₁)` under the chart-ring-to-sections map. -/
def overlapUnit : (Γ(p1, U0 ⊓ U1))ˣ :=
  Units.map overlapRingHom.toMonoidHom awayUnit


-- @@ L381-381 verbatim
end OverlapUnit


-- @@ L383-383 verbatim
/-! ### The gluing data -/


-- @@ L385-388 verbatim
/-- The overlap unit as a section of the units sheaf `O^*` over `U0 ⊓ U1`
(additively written; `DLog.unitsAb_sections` is a `rfl`). -/
def overlapUnitAb : ((unitsAb p1).obj.obj (op (U0 ⊓ U1))) :=
  Additive.ofMul overlapUnit


-- @@ L390-393 verbatim
/-- **The rational function to glue**: the germ of the overlap unit in the
unit group of the function field (classically "`X₁/X₀`"). -/
def zElt : (functionFieldUnitsAb p1) :=
  germUnitsHom p1 genericPoint_mem_U01 overlapUnitAb


-- @@ L395-399 verbatim
/-- The section of `K^*` given by `zElt` over any open containing the
generic point (the skyscraper sections identification). -/
def zSectionK {W : p1.Opens} (h : genericPoint p1 ∈ W) :
    ((KUnitsAb p1).obj.obj (op W)) :=
  eqToHom (KUnitsAb_obj_of_mem p1 h).symm zElt


-- @@ L401-406 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The left gluing datum: the class of `zElt` in `K^*/O^*` over `U0`
(stated at the Type-valued `forget` spelling the Mayer–Vietoris glue
consumes). -/
def dinfLeft : ((divisorsAb p1).obj ⋙ forget AddCommGrpCat).obj (op U0) :=
  (divisorsπ p1).hom.app (op U0) (zSectionK genericPoint_mem_U0)


-- @@ L408-411 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The right gluing datum: the trivial class over `U1`. -/
def dinfRight : ((divisorsAb p1).obj ⋙ forget AddCommGrpCat).obj (op U1) :=
  (0 : (divisorsAb p1).obj.obj (op U1))


-- @@ L413-462 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **The overlap agreement**: on `U0 ⊓ U1` the class of `zElt` is
trivial — `zElt` is there the image of a genuine unit of the structure
sheaf (`overlapUnit`), and the image of a unit dies in `K^*/O^*`
sectionwise (`divisorsπ ∘ unitsToK = 0`, the cokernel condition; no
sheaf-level section extraction is used anywhere). -/
theorem dinf_overlap :
    ((divisorsAb p1).obj ⋙ forget AddCommGrpCat).map
        ((Opens.mayerVietorisSquare U0 U1).f₁₂).op dinfLeft =
      ((divisorsAb p1).obj ⋙ forget AddCommGrpCat).map
        ((Opens.mayerVietorisSquare U0 U1).f₁₃).op dinfRight := by
  show (divisorsAb p1).obj.map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op
      ((divisorsπ p1).hom.app (op U0) (zSectionK genericPoint_mem_U0)) =
    (divisorsAb p1).obj.map ((Opens.mayerVietorisSquare U0 U1).f₁₃).op
      (0 : (divisorsAb p1).obj.obj (op U1))
  have hz : (divisorsAb p1).obj.map ((Opens.mayerVietorisSquare U0 U1).f₁₃).op
      (0 : (divisorsAb p1).obj.obj (op U1)) = 0 :=
    map_zero ((divisorsAb p1).obj.map
      ((Opens.mayerVietorisSquare U0 U1).f₁₃).op).hom
  rw [hz]
  have hnat : (divisorsAb p1).obj.map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op
      ((divisorsπ p1).hom.app (op U0) (zSectionK genericPoint_mem_U0)) =
      (divisorsπ p1).hom.app (op (U0 ⊓ U1))
        ((KUnitsAb p1).obj.map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op
          (zSectionK genericPoint_mem_U0)) := by
    show ((divisorsπ p1).hom.app (op U0) ≫
        (divisorsAb p1).obj.map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op)
        (zSectionK genericPoint_mem_U0) = _
    rw [← (divisorsπ p1).hom.naturality]
    rfl
  rw [hnat]
  have hres : (KUnitsAb p1).obj.map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op
      (zSectionK genericPoint_mem_U0) = zSectionK genericPoint_mem_U01 := by
    rw [KUnitsAb_map_of_mem p1 _ genericPoint_mem_U01]
    show (eqToHom (KUnitsAb_obj_of_mem p1 genericPoint_mem_U0).symm ≫
      eqToHom _) zElt = _
    rw [eqToHom_trans]
    rfl
  rw [hres]
  have hunit : zSectionK genericPoint_mem_U01 =
      (unitsToK p1).hom.app (op (U0 ⊓ U1)) overlapUnitAb := by
    rw [unitsToK_app_of_mem p1 genericPoint_mem_U01]
    rfl
  rw [hunit]
  have h1 : (divisorsπ p1).hom.app (op (U0 ⊓ U1))
      ((unitsToK p1).hom.app (op (U0 ⊓ U1)) overlapUnitAb) =
      ((unitsToK p1 ≫ divisorsπ p1).hom.app (op (U0 ⊓ U1))) overlapUnitAb := rfl
  rw [h1, show unitsToK p1 ≫ divisorsπ p1 = 0 from
    cokernel.condition (unitsToK p1)]
  rfl


-- @@ L464-474 verbatim
/-- **The glued global datum** over the fourth object of the pin's
Mayer–Vietoris square (Riou's `MayerVietorisSquare.SheafCondition.glue`,
at the Type-valued `forget` spelling — the sheaf condition of the
composed Type-valued sheaf). -/
def dinfGlued :
    ((divisorsAb p1).obj ⋙ forget AddCommGrpCat).obj
      (op ((Opens.mayerVietorisSquare U0 U1).toSquare.X₄)) :=
  ((Opens.mayerVietorisSquare U0 U1).sheafCondition_of_sheaf
    ((sheafCompose (Opens.grothendieckTopology (p1 : TopCat))
      (forget AddCommGrpCat)).obj (divisorsAb p1))).glue
    dinfLeft dinfRight dinf_overlap


-- @@ L476-478 verbatim
/-- Receipt: the square's fourth object is the union, definitionally. -/
theorem mayerVietorisSquare_X₄ :
    (Opens.mayerVietorisSquare U0 U1).toSquare.X₄ = U0 ⊔ U1 := rfl


-- @@ L480-484 verbatim
/-- Receipt: the glued datum restricts to the left gluing datum on `U0`. -/
theorem dinfGlued_restrict_left :
    ((divisorsAb p1).obj ⋙ forget AddCommGrpCat).map
        ((Opens.mayerVietorisSquare U0 U1).f₂₄).op dinfGlued = dinfLeft :=
  GrothendieckTopology.MayerVietorisSquare.SheafCondition.map_f₂₄_op_glue _ _ _ _


-- @@ L486-490 verbatim
/-- Receipt: the glued datum restricts to the trivial datum on `U1`. -/
theorem dinfGlued_restrict_right :
    ((divisorsAb p1).obj ⋙ forget AddCommGrpCat).map
        ((Opens.mayerVietorisSquare U0 U1).f₃₄).op dinfGlued = dinfRight :=
  GrothendieckTopology.MayerVietorisSquare.SheafCondition.map_f₃₄_op_glue _ _ _ _


-- @@ L492-497 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The glued datum as a global section of `K^*/O^*` (the union is the
whole space, `U0_sup_U1`). -/
def dinfTopSection : ((divisorsAb p1).obj.obj (op (⊤ : p1.Opens))) :=
  (divisorsAb p1).obj.map (homOfLE U0_sup_U1.ge).op
    (dinfGlued : (divisorsAb p1).obj.obj (op (U0 ⊔ U1)))


-- @@ L499-513 verbatim
/-- **The point-divisor datum `D∞`**: the Cartier divisor on the
projective line glued from the class of the rational function `zElt`
(classically "`X₁/X₀`") over the chart `D₊(X₀)` and the trivial class
over the chart `D₊(X₁)`.

By construction a global section of `K^*/O^*` under `cdivSectionsEquiv`.
Classically this datum presents the divisor of a point, but no Weil
divisor is attached to it here and no order of vanishing is computed —
so the honest, chart-convention-free name is **the standard nontrivial
Cartier class obtained from the transition function `X₁/X₀`**; "the
point at infinity" is informal nomenclature only (which point it names
depends on chart convention). Nontriviality of its `H¹(O^*)` class is
proved downstream (`ProjectiveLineUnits.dinfClass_ne_zero`). -/
def dinf : CDiv p1 :=
  (cdivSectionsEquiv p1).symm dinfTopSection


-- @@ L515-515 verbatim
/-! ## Part 2(b). The divisor class and the cycle class, by construction -/


-- @@ L517-520 verbatim
/-- The class of `dinf` in `H¹(p1, O^*)` — an application of the shipped
connecting-map machinery.  **Not claimed to be nonzero.**  (`H¹(X, O^*)`
is *classically* the Picard group; no such identification is claimed.) -/
def dinfClass : unitsH1 p1 := cdivClass p1 dinf


-- @@ L522-524 verbatim
/-- The divisor datum moved to the small affine Zariski site (the home of
the first Chern class map), along the shipped site equivalence. -/
def dinfAffine : CDivAffine p1 := cdivSiteEquiv p1 dinf


-- @@ L526-533 verbatim
/-- **The divisor-level cycle class of `D∞` in `F¹ ℍ²_dR(p1)`** — the
shipped `cdivCycleClassC` at the structure morphism, evaluated at
`dinfAffine`.  A pure application: the codomain of the shipped map is the
filtration step, so membership is by construction
(`dinfCycleClass_mem`).  **Not claimed to be nonzero**, and the
filtration is the naive (brutal-truncation) filtration. -/
def dinfCycleClass : (hodgeFiltrationDRC structMor 1 2) :=
  cdivCycleClassC structMor dinfAffine


-- @@ L535-543 verbatim
/-- **`F¹`-membership, by construction**: the underlying `ℍ²_dR(p1)`
class of `dinfCycleClass` lies in the first step of the naive filtration
— the witness is the codomain of the shipped map itself
(`CartierClass.cdivCycleClass_mem`); this is a definitional receipt, not
a computation, and it does **not** assert that the class is nonzero. -/
theorem dinfCycleClass_mem :
    (dinfCycleClass : hyperHdR (cRingHom structMor) 2) ∈
      hodgeFiltrationDR (cRingHom structMor) 1 2 :=
  cdivCycleClass_mem p1 (cRingHom structMor) dinfAffine


-- @@ L545-550 verbatim
/-! ## Part 2(c). The pairing at `(D∞, D∞)`, by construction

Every ceiling of `HodgePilot.CyclePairing` applies verbatim: the pairing
is a constructed pairing-shaped assignment; it is **not** the cup
product, it is **not** identified with any classical intersection
pairing, and **no canonicity is claimed** for the exhibited choices. -/


-- @@ L552-554 verbatim
/-- The divisor data of `D∞` for the pairing's first slot (the shipped
`pairData` at `dinf`). -/
def dinfPairData : pairAnchor p1 ⟶ divisorsMod p1 := pairData p1 dinf


-- @@ L556-562 verbatim
/-- **The paired class of `(D∞, D∞)`** — the shipped `pairedDivClass` at
the pair `(dinf, dinf)`: two copies of the same point-divisor datum, the
two-point self-pairing plan.  An application of shipped machinery; **not
claimed to be nonzero**; not the cup product; not any classical
intersection pairing; no canonicity claimed. -/
def dinfPairedDivClass : Abelian.Ext (pairAnchor p1) (pairedTarget p1) 2 :=
  pairedDivClass p1 dinf dinf


-- @@ L564-568 verbatim
/-- The second-slot input of the landed pairing at `dinf`: the moved
divisor class (`CycCarrier.cdivClass_moveIn` identifies it with the
transported `cdivClass p1 dinf`). -/
def dinfSecondSlot : Abelian.Ext (pairAnchor p1) (unitsMod p1) 1 :=
  (cdivMoveIn p1 dinf).comp (cartierδMod p1) (zero_add 1)


-- @@ L570-586 verbatim
/-- **The landed self-pairing of `D∞` in `F²` of the degree-4
hypercohomology** — the shipped `pairedClassInto` at the structure
morphism, evaluated at the divisor data of `dinf` in both slots.  A pure
application: the codomain is the filtration subtype, so membership is by
construction (`dinfPairedInto_mem`).  **Not claimed to be nonzero**; the
filtration is the naive (brutal-truncation) filtration; not the cup
product; not any classical intersection pairing; no canonicity
claimed.  Classically the genuine degree-4 cohomology of a curve
vanishes, so the expected value of any faithful degree-4 self-pairing
on `p1` is **zero** — a degree-4 nonvanishing will never be claimed or
attempted on the projective line, and this value IS proved zero
downstream (`CalibrationDegreeFour.dinfPairedInto_eq_zero`: the
constructed `F²` container is trivial). -/
def dinfPairedInto :
    (affineZHodgeFiltration p1 (pairAnchorAffine p1)
      (reindexZ (deRhamSheafZComplexN (cRingHom structMor))) 2 4) :=
  pairedClassInto (cRingHom structMor) dinfPairData dinfSecondSlot


-- @@ L588-598 verbatim
/-- **`F²`-membership, by construction**: the underlying degree-4
hypercohomology class of `dinfPairedInto` lies in the second step of the
naive filtration — the witness is the codomain of the shipped landing
itself (`CyclePairing.pairedIntoFull_mem`); a definitional receipt, not
a computation, and it does **not** assert that the class is nonzero. -/
theorem dinfPairedInto_mem :
    (dinfPairedInto : affineZHyperH p1 (pairAnchorAffine p1)
        (reindexZ (deRhamSheafZComplexN (cRingHom structMor))) 4) ∈
      affineZHodgeFiltration p1 (pairAnchorAffine p1)
        (reindexZ (deRhamSheafZComplexN (cRingHom structMor))) 2 4 :=
  dinfPairedInto.2


-- @@ L600-600 verbatim
end ProjectiveLine


-- @@ L602-602 verbatim
end HodgePilot


-- @@ L604-604 verbatim
end
