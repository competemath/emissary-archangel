import HodgePilot.AffineVanishing
import HodgePilot.GradedEdgeProof


-- @@ L4-81 verbatim
/-! # The interference exclusion: `H¹(ℙ¹, 𝒪-carrier)` vanishes, and the
`σ≥1`-truncated cycle class detects in the full degree-2 carrier

Golden-path interference wave, stage 2 (the retirement of the named `Prop`
`ProjectiveLineGraded.InterferenceExclusion`).  Stage 1
(`HodgePilot.AffineVanishing`) proved `H'¹(V, 𝒪) = 0` at every affine open of
`p1 = Proj ℂ[X₀, X₁]` for the structure-sheaf carrier
`𝒪 := DeRhamSheaf.deRhamSheafSpace φC 0`.  This module:

* **Leg 1 (`deltaO_eq_zero`)** — the Mayer–Vietoris connecting map
  `δ : H'⁰(U0 ⊓ U1, 𝒪) → H'¹(U0 ⊔ U1, 𝒪)` of the two-chart square is zero,
  because the restriction-difference map on sections is **surjective** onto
  the overlap sections (Laurent surjectivity: every section of `𝒪` on
  `U0 ⊓ U1` is a difference of sections extending to the two charts —
  `ℂ[z] + ℂ[1/z]` spans `ℂ[z, 1/z]`, run through wave 2's chart algebra maps
  and the wave-3 overlap coordinate), so `δ` factors through
  `fromBiprod ≫ δ = 0` of Riou's Mayer–Vietoris sequence.
* **Leg 2 (`subsingleton_hPrimeOne_sup`, `subsingleton_H_one_structO`)** — the
  `H¹`-squeeze: by exactness of the Mayer–Vietoris sequence at the
  `H'¹(U0 ⊔ U1)`-node, every class comes from `δ` (the outer terms
  `H'¹(U0)`, `H'¹(U1)` vanish by stage 1), and `δ = 0` by Leg 1; carried to
  Mathlib's `Sheaf.H` along the wave-3 terminal-anchor re-isomorphism:
  **`H¹(ℙ¹, 𝒪-carrier)` is a subsingleton** in the sense of Mathlib's
  `Sheaf.H`.
* **Leg 3 (`interferenceExclusion`)** — **the named `Prop`
  `ProjectiveLineGraded.InterferenceExclusion` HOLDS** at its literal
  spelling: the map `H¹(𝒪) → H¹(Ω¹)` induced by the exterior differential
  kills every class (a map out of a subsingleton group is zero).  The `Prop`
  remains stated in `HodgePilot.ProjectiveLineGraded`, where its docstring —
  written before this module — records it as the honest wall; this theorem is
  its proof, exactly the `GradedTruncationDetection`/`gradedTruncationDetection`
  retirement pattern.
* **Leg 4 (`trunc_kernel_eq_zero`, `dinfCycleClass_coe_ne_zero`)** — the
  truncated-to-full lift: the map from the `σ≥1`-truncated degree-2
  hypercohomology to the full `ℍ²_dR` has **zero kernel** — from the
  termwise short exact sequence `0 → σ≥1 Ω• → Ω• → 𝒪[0] → 0`, the
  distinguished triangle in the derived category, and the vanishing of
  `H¹(𝒪)` (Legs 1–3, moved back across the dense subsite) — so the
  unconditional graded nonvanishing
  `GradedEdgeProof.dinfCycleClassTrunc_ne_zero` lifts:
  **`dinfCycleClass` is nonzero in the degree-2 de Rham hypercohomology
  carrier `hyperHdR` of the projective line**.

## Claim discipline (each clause load-bearing)

* Everything is about the named constructed carriers of this development:
  `DeRhamSheaf.deRhamSheafSpace φC 0` (the structure-sheaf carrier),
  `ProjectiveLineGraded.omegaSheaf`, and the degree-2 hypercohomology
  carrier `DeRhamSheaf.hyperHdR (cRingHom structMor) 2` with its naive
  (brutal-truncation) filtration.  **No comparison with any other cohomology
  theory — classical, analytic, singular, Čech, or derived-functor-on-modules
  — is stated, implied, or approached.**  No Serre vanishing in any
  generality is claimed: the vanishing inputs are exactly stage 1's per-affine
  statements on this one scheme and this one carrier.
* The nonvanishing of Leg 4 is exactly: the image of the `σ≥1`-canonical
  representative of `dinfCycleClass` — which **is** the underlying class of
  `dinfCycleClass` (`ProjectiveLineDetection.dinfCycleClassTrunc_ι`, a
  receipt, not a comparison) — is nonzero in `hyperHdR (cRingHom structMor)
  2`.  No identification of this carrier with `H²` of any classical theory
  is constructed or claimed; no degeneration statement, no `H^{p,q}`, no
  Hodge-theoretic content.
* Nothing here makes the Hodge conjecture statable.

## Credits

The Mayer–Vietoris square and sequence, `Sheaf.H`/`Sheaf.H'`, `Ext`, the
derived category, `triangleOfSES` and the triangulated coyoneda exactness are
Joël Riou's Mathlib work; the dense-subsite equivalence and the `Proj` chart
API are Andrew Yang's; homogeneous localizations and the `Away` generation
theorem are Jujian Zhang's, Eric Wieser's and the 2025 Proj cluster's; the
affine vanishing input is `HodgePilot.AffineVanishing` (stage 1, after Brian
Nugent's mathlib4 affine-vanishing architecture and Kempf); the sections
layer, chart isomorphisms and overlap coordinate are
`HodgePilot.ProjectiveLineGraded`/`HodgePilot.ProjectiveLineUnits`/
`HodgePilot.ProjectiveLine`; the truncation machinery is `HodgePilot.Hyper`
and `HodgePilot.ProjectiveLineDetection`; the graded nonvanishing consumed by
Leg 4 is `HodgePilot.GradedEdgeProof`.
-/


-- @@ L83-83 verbatim
set_option maxHeartbeats 1000000

-- @@ L84-84 verbatim
set_option synthInstance.maxHeartbeats 1000000


-- @@ L86-86 verbatim
noncomputable section


-- @@ L88-88 verbatim
namespace HodgePilot


-- @@ L90-90 verbatim
namespace InterferenceProof


-- @@ L92-92 verbatim
open CategoryTheory CategoryTheory.Limits Opposite Abelian AlgebraicGeometry TopologicalSpace

-- @@ L93-93 verbatim
open HomogeneousLocalization

-- @@ L94-94 verbatim
open HodgePilot.ProjectiveLineGraded HodgePilot.ProjectiveLine HodgePilot.ProjectiveLineUnits

-- @@ L95-95 verbatim
open HodgePilot.DeRhamPresheaf HodgePilot.AffineVanishing

-- @@ L96-96 verbatim
open LaurentPolynomial

-- @@ L97-97 verbatim
open scoped Polynomial


-- @@ L99-99 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L101-102 verbatim
/-- The standard grading of `ℂ[X₀, X₁]` by total degree. -/
local notation "𝒜₂" => MvPolynomial.homogeneousSubmodule (Fin 2) ℂ


-- @@ L104-108 verbatim
/-! ## Part 1. Ring level: Laurent surjectivity of the restriction difference

`Γ(U0 ⊓ U1) = ℂ[z, 1/z]` (through wave 3's overlap coordinate), and every
Laurent polynomial splits as a `ℂ[z]`-part restricted from `U0` minus a
`ℂ[1/z]`-part restricted from `U1`. -/


-- @@ L110-110 verbatim
section RingLevel


-- @@ L112-125 verbatim
/-- The overlap section map is the `hom` of wave 3's overlap-section
isomorphism (the two arrows agree by `Subsingleton.elim`). -/
theorem overlapRingHom_eq_iso_hom
    (x : Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)) :
    overlapRingHom x = overlapSectionIso.hom x := by
  show p1.presheaf.map (homOfLE (le_of_eq U0_inf_U1)).op
      (Proj.awayToSection 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) x) =
    p1.presheaf.map ((eqToIso U0_inf_U1).hom.op)
      (Proj.awayToSection 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) x)
  exact congrArg
    (fun (h : U0 ⊓ U1 ⟶ Proj.basicOpen 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)) =>
      p1.presheaf.map h.op
        (Proj.awayToSection 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1) x))
    (Subsingleton.elim _ _)


-- @@ L127-132 verbatim
/-- The overlap section map is surjective (wave 3's `overlapSectionIso` is an
isomorphism). -/
theorem overlapRingHom_surjective : Function.Surjective overlapRingHom := fun z =>
  ⟨overlapSectionIso.inv z, by
    rw [overlapRingHom_eq_iso_hom]
    exact overlapSectionIso.inv_hom_id_apply z⟩


-- @@ L134-148 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- The overlap coordinate map on an arbitrary monomial `T^n`: the value is
the `n`-th power of the overlap unit (the `n = 1` case is wave 3's glue-datum
receipt `overlapAlgHom_T`). -/
theorem overlapAlgHom_T_int (n : ℤ) :
    overlapAlgHom (T n) =
      ((overlapUnitSec ^ n : (Sec φC (U0 ⊓ U1))ˣ) : Sec φC (U0 ⊓ U1)) := by
  rw [show (T n : ℂ[T;T⁻¹]) = AddMonoidAlgebra.single (n : ℤ) (1 : ℂ) from by
      rw [single_eq_C_mul_T, map_one, one_mul],
    overlapAlgHom]
  rw [AddMonoidAlgebra.lift_single, one_smul]
  show (((zpowersHom ((Sec φC (U0 ⊓ U1))ˣ)) overlapUnitSec)
    (Multiplicative.ofAdd (n : ℤ)) : Sec φC (U0 ⊓ U1)) = _
  rw [zpowersHom_apply]
  rfl


-- @@ L150-251 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **Surjectivity of the overlap coordinate map**: every section of the
structure sheaf on the chart overlap is a Laurent polynomial in the overlap
unit.  (By the pin's `Away` generation theorem at `f = X₀X₁`, mirroring
wave 2's `chartPolyHom_surjective`.) -/
theorem overlapAlgHom_surjective : Function.Surjective overlapAlgHom := by
  intro z
  obtain ⟨x, rfl⟩ := overlapRingHom_surjective z
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
    interval_cases a
    · -- a = 0 : the generator is 1
      have hk0 : ai 0 = 0 := by omega
      have hk1 : ai 1 = 0 := by omega
      refine ⟨1, ?_⟩
      rw [map_one, show (1 : Sec φC (U0 ⊓ U1)) = overlapRingHom 1 from
        (map_one overlapRingHom).symm]
      refine congrArg overlapRingHom ?_
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.val_one, HomogeneousLocalization.Away.val_mk,
        Fin.prod_univ_two, hk0, hk1, ← Localization.mk_one,
        Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      use 1
      simp only [OneMemClass.coe_one, one_mul, pow_zero]
    · -- a = 1 : the generator is awayNum, 1 or awayNumInv
      have hk : ai 0 = 0 ∨ ai 0 = 1 ∨ ai 0 = 2 := by omega
      rcases hk with hk0 | hk0 | hk0
      · have hk1 : ai 1 = 2 := by omega
        refine ⟨T 1, ?_⟩
        rw [overlapAlgHom_T, overlapUnit_coe]
        refine congrArg overlapRingHom ?_
        apply HomogeneousLocalization.val_injective
        unfold ProjectiveLine.awayNum
        rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
          Fin.prod_univ_two, hk0, hk1, Localization.mk_eq_mk_iff,
          Localization.r_iff_exists]
        use 1
        simp only [OneMemClass.coe_one, one_mul, pow_zero]
        ring
      · have hk1 : ai 1 = 1 := by omega
        refine ⟨1, ?_⟩
        rw [map_one, show (1 : Sec φC (U0 ⊓ U1)) = overlapRingHom 1 from
          (map_one overlapRingHom).symm]
        refine congrArg overlapRingHom ?_
        apply HomogeneousLocalization.val_injective
        rw [HomogeneousLocalization.val_one, HomogeneousLocalization.Away.val_mk,
          Fin.prod_univ_two, hk0, hk1, ← Localization.mk_one,
          Localization.mk_eq_mk_iff, Localization.r_iff_exists]
        use 1
        simp only [OneMemClass.coe_one, one_mul, pow_one]
        ring
      · have hk1 : ai 1 = 0 := by omega
        refine ⟨T (-1), ?_⟩
        rw [overlapAlgHom_T_neg, overlapUnit_inv_coe]
        refine congrArg overlapRingHom ?_
        apply HomogeneousLocalization.val_injective
        unfold ProjectiveLine.awayNumInv
        rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
          Fin.prod_univ_two, hk0, hk1, Localization.mk_eq_mk_iff,
          Localization.r_iff_exists]
        use 1
        simp only [OneMemClass.coe_one, one_mul, pow_zero]
        ring
    · -- a = 2 : the generator is 1 again
      have hk0 : ai 0 = 2 := by omega
      have hk1 : ai 1 = 2 := by omega
      refine ⟨1, ?_⟩
      rw [map_one, show (1 : Sec φC (U0 ⊓ U1)) = overlapRingHom 1 from
        (map_one overlapRingHom).symm]
      refine congrArg overlapRingHom ?_
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.val_one, HomogeneousLocalization.Away.val_mk,
        Fin.prod_univ_two, hk0, hk1, ← Localization.mk_one,
        Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      use 1
      simp only [OneMemClass.coe_one, one_mul]
      ring
  | algebraMap r =>
    obtain ⟨c, rfl⟩ := gradeZero_algebraMap_bijective.2 r
    refine ⟨algebraMap ℂ ℂ[T;T⁻¹] c, ?_⟩
    rw [AlgHom.commutes, algebraMap_sec_U01 c]
    exact congrArg overlapRingHom
      (IsScalarTower.algebraMap_apply ℂ (𝒜₂ 0)
        (Away 𝒜₂ (MvPolynomial.X 0 * MvPolynomial.X 1)) c)
  | add y w _ _ hy hw =>
    obtain ⟨Ly, hLy⟩ := hy
    obtain ⟨Lw, hLw⟩ := hw
    exact ⟨Ly + Lw, by rw [map_add, hLy, hLw, map_add]⟩
  | mul y w _ _ hy hw =>
    obtain ⟨Ly, hLy⟩ := hy
    obtain ⟨Lw, hLw⟩ := hw
    exact ⟨Ly * Lw, by rw [map_mul, hLy, hLw, map_mul]⟩


-- @@ L253-299 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **The Laurent split (ring level)**: every section of the structure sheaf
on the chart overlap is the difference of a restriction from `U0` and a
restriction from `U1` — `ℂ[z] + ℂ[1/z]` spans `ℂ[z, 1/z]`.  (Nonnegative
powers of the overlap unit extend to the first chart along wave 3's
`chartHomA 0 1`; negative powers to the second chart along `chartHomA 1 0`.) -/
theorem laurent_section_split (z : Sec φC (U0 ⊓ U1)) :
    ∃ (a : Sec φC U0) (b : Sec φC U1),
      DeRhamPresheaf.res φC (inf_le_left : U0 ⊓ U1 ≤ U0) a -
        DeRhamPresheaf.res φC (inf_le_right : U0 ⊓ U1 ≤ U1) b = z := by
  obtain ⟨L, rfl⟩ := overlapAlgHom_surjective z
  induction L using LaurentPolynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨ap, bp, hp'⟩ := hp
    obtain ⟨aq, bq, hq'⟩ := hq
    refine ⟨ap + aq, bp + bq, ?_⟩
    rw [map_add, map_add, map_add, ← hp', ← hq']
    ring
  | C_mul_T n c =>
    have hval : overlapAlgHom (LaurentPolynomial.C c * T n) =
        c • ((overlapUnitSec ^ n : (Sec φC (U0 ⊓ U1))ˣ) : Sec φC (U0 ⊓ U1)) := by
      rw [← smul_eq_C_mul, map_smul, overlapAlgHom_T_int]
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · -- nonnegative power: restrict from the first chart
      refine ⟨chartHomA 0 1 (Polynomial.C c * Polynomial.X ^ m), 0, ?_⟩
      rw [map_zero, sub_zero, hval, zpow_natCast]
      have hpow : ((overlapUnitSec ^ m : (Sec φC (U0 ⊓ U1))ˣ) : Sec φC (U0 ⊓ U1)) =
          overlapRingHom awayNum ^ m := by
        rw [Units.val_pow_eq_pow_val]
        exact congrArg (fun t => t ^ m) overlapUnit_coe
      rw [hpow]
      simp only [map_mul, map_pow]
      rw [Polynomial.C_eq_algebraMap, AlgHom.commutes, AlgHom.commutes,
        res_chartHomA_X_left]
      exact (Algebra.smul_def c _).symm
    · -- negative power: restrict from the second chart
      refine ⟨0, -(chartHomA 1 0 (Polynomial.C c * Polynomial.X ^ m)), ?_⟩
      rw [map_zero, map_neg, sub_neg_eq_add, zero_add, hval, zpow_neg, zpow_natCast]
      have hpow : (((overlapUnitSec ^ m)⁻¹ : (Sec φC (U0 ⊓ U1))ˣ) :
          Sec φC (U0 ⊓ U1)) = overlapRingHom awayNumInv ^ m := by
        rw [← inv_pow, Units.val_pow_eq_pow_val]
        exact congrArg (fun t => t ^ m) overlapUnit_inv_coe
      rw [hpow]
      simp only [map_mul, map_pow]
      rw [Polynomial.C_eq_algebraMap, AlgHom.commutes, AlgHom.commutes,
        res_chartHomA_X_right]
      exact (Algebra.smul_def c _).symm


-- @@ L301-301 verbatim
end RingLevel


-- @@ L303-306 verbatim
/-! ## Part 2. Sheaf level: the section split on the carrier

Transport of the Laurent split along stage 1's ring identification
`oToRing`/`ringToO` at the three affine site objects. -/


-- @@ L308-308 verbatim
section SectionSplit


-- @@ L310-343 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **The section split on the structure-sheaf carrier**: every section of
`𝒪` over the chart overlap is a difference of restrictions from the two
charts. -/
theorem sections_split (s : structO.obj.obj (op (U0 ⊓ U1))) :
    ∃ (s0 : structO.obj.obj (op U0)) (s1 : structO.obj.obj (op U1)),
      structO.obj.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op s0 -
        structO.obj.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op s1 = s := by
  obtain ⟨a, b, hab⟩ := laurent_section_split
    (oToRing ⟨U0 ⊓ U1, isAffineOpen_U01⟩ s)
  refine ⟨ringToO ⟨U0, isAffineOpen_U0⟩ a, ringToO ⟨U1, isAffineOpen_U1⟩ b, ?_⟩
  have hOcL : structO.obj.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op
      (ringToO ⟨U0, isAffineOpen_U0⟩ a) =
      ringToO ⟨U0 ⊓ U1, isAffineOpen_U01⟩
        (p1.presheaf.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op a) := by
    have h1 := oToRing_natural (W' := ⟨U0 ⊓ U1, isAffineOpen_U01⟩)
      (W := ⟨U0, isAffineOpen_U0⟩) inf_le_left (ringToO ⟨U0, isAffineOpen_U0⟩ a)
    rw [oToRing_ringToO] at h1
    have h2 := congrArg (ringToO ⟨U0 ⊓ U1, isAffineOpen_U01⟩) h1
    rwa [ringToO_oToRing] at h2
  have hOcR : structO.obj.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op
      (ringToO ⟨U1, isAffineOpen_U1⟩ b) =
      ringToO ⟨U0 ⊓ U1, isAffineOpen_U01⟩
        (p1.presheaf.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op b) := by
    have h1 := oToRing_natural (W' := ⟨U0 ⊓ U1, isAffineOpen_U01⟩)
      (W := ⟨U1, isAffineOpen_U1⟩) inf_le_right (ringToO ⟨U1, isAffineOpen_U1⟩ b)
    rw [oToRing_ringToO] at h1
    have h2 := congrArg (ringToO ⟨U0 ⊓ U1, isAffineOpen_U01⟩) h1
    rwa [ringToO_oToRing] at h2
  rw [hOcL, hOcR, ← ringToO_sub]
  have h3 : p1.presheaf.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op a -
      p1.presheaf.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op b =
      oToRing ⟨U0 ⊓ U1, isAffineOpen_U01⟩ s := hab
  rw [h3, ringToO_oToRing]


-- @@ L345-345 verbatim
end SectionSplit


-- @@ L347-347 verbatim
/-! ## Part 3. Leg 1: the Mayer–Vietoris connecting map of the carrier is zero -/


-- @@ L349-349 verbatim
section DeltaZero


-- @@ L351-401 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Every degree-0 class of the carrier on the overlap is in the image of
`fromBiprod` (the section split, read through the Part-1 sections layer of
wave 3). -/
theorem fromBiprodO_surjective (y : Ext (freeYonedaSheaf JP1 (U0 ⊓ U1)) structO 0) :
    ∃ b, (Opens.mayerVietorisSquare U0 U1).fromBiprod structO 0 b = y := by
  obtain ⟨s0, s1, hsplit⟩ := sections_split (h0ToSections structO (U0 ⊓ U1) y)
  refine ⟨(AddCommGrpCat.biprodIsoProd _ _).inv
    (((h0SectionsEquiv structO U0).symm s0,
      (h0SectionsEquiv structO U1).symm s1) :
      (structO.H' 0 (Opens.mayerVietorisSquare U0 U1).toSquare.X₂) ×
        (structO.H' 0 (Opens.mayerVietorisSquare U0 U1).toSquare.X₃)), ?_⟩
  rw [(Opens.mayerVietorisSquare U0 U1).fromBiprod_biprodIsoProd_inv_apply structO
    ((h0SectionsEquiv structO U0).symm s0) ((h0SectionsEquiv structO U1).symm s1)]
  apply (h0SectionsEquiv structO (U0 ⊓ U1)).injective
  rw [map_sub, h0SectionsEquiv_apply, h0SectionsEquiv_apply, h0SectionsEquiv_apply]
  have hsecL : h0ToSections structO (U0 ⊓ U1)
      ((structO.cohomologyPresheaf 0).map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op
        ((h0SectionsEquiv structO U0).symm s0)) =
      structO.obj.map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op
        (h0ToSections structO (Opens.mayerVietorisSquare U0 U1).toSquare.X₂
          ((h0SectionsEquiv structO U0).symm s0)) :=
    (h0ToSections_natural structO (Opens.mayerVietorisSquare U0 U1).f₁₂
      ((h0SectionsEquiv structO U0).symm s0)).symm
  have hsecR : h0ToSections structO (U0 ⊓ U1)
      ((structO.cohomologyPresheaf 0).map ((Opens.mayerVietorisSquare U0 U1).f₁₃).op
        ((h0SectionsEquiv structO U1).symm s1)) =
      structO.obj.map ((Opens.mayerVietorisSquare U0 U1).f₁₃).op
        (h0ToSections structO (Opens.mayerVietorisSquare U0 U1).toSquare.X₃
          ((h0SectionsEquiv structO U1).symm s1)) :=
    (h0ToSections_natural structO (Opens.mayerVietorisSquare U0 U1).f₁₃
      ((h0SectionsEquiv structO U1).symm s1)).symm
  rw [hsecL, hsecR]
  have hL : h0ToSections structO (Opens.mayerVietorisSquare U0 U1).toSquare.X₂
      ((h0SectionsEquiv structO U0).symm s0) = s0 := by
    rw [← h0SectionsEquiv_apply]
    exact (h0SectionsEquiv structO U0).apply_symm_apply s0
  have hR : h0ToSections structO (Opens.mayerVietorisSquare U0 U1).toSquare.X₃
      ((h0SectionsEquiv structO U1).symm s1) = s1 := by
    rw [← h0SectionsEquiv_apply]
    exact (h0SectionsEquiv structO U1).apply_symm_apply s1
  rw [hL, hR]
  have harrL : structO.obj.map ((Opens.mayerVietorisSquare U0 U1).f₁₂).op s0 =
      structO.obj.map (homOfLE (inf_le_left : U0 ⊓ U1 ≤ U0)).op s0 :=
    congrArg (fun (t : (U0 ⊓ U1 : p1.Opens) ⟶ U0) => structO.obj.map t.op s0)
      (Subsingleton.elim _ _)
  have harrR : structO.obj.map ((Opens.mayerVietorisSquare U0 U1).f₁₃).op s1 =
      structO.obj.map (homOfLE (inf_le_right : U0 ⊓ U1 ≤ U1)).op s1 :=
    congrArg (fun (t : (U0 ⊓ U1 : p1.Opens) ⟶ U1) => structO.obj.map t.op s1)
      (Subsingleton.elim _ _)
  rw [harrL, harrR, hsplit]


-- @@ L403-421 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **LEG 1 — `δ_𝒪 = 0`**: the Mayer–Vietoris connecting map of the two-chart
square vanishes on the structure-sheaf carrier, because the
restriction-difference map on sections is surjective onto the overlap
(`fromBiprod ≫ δ = 0` in Riou's sequence).  Nothing here makes the Hodge
conjecture statable. -/
theorem deltaO_eq_zero (y : Ext (freeYonedaSheaf JP1 (U0 ⊓ U1)) structO 0) :
    (Opens.mayerVietorisSquare U0 U1).δ structO 0 1 rfl y = 0 := by
  obtain ⟨b, hb⟩ := fromBiprodO_surjective y
  rw [← hb]
  have h2 := congrArg
    (fun (t : ((structO.H' 0 (Opens.mayerVietorisSquare U0 U1).toSquare.X₂) ⊞
        (structO.H' 0 (Opens.mayerVietorisSquare U0 U1).toSquare.X₃) :
          AddCommGrpCat.{0}) ⟶
        structO.H' 1 (Opens.mayerVietorisSquare U0 U1).toSquare.X₄) => t b)
    ((Opens.mayerVietorisSquare U0 U1).fromBiprod_δ structO 0 1 rfl)
  refine h2.trans ?_
  show ((0 : _ ⟶ structO.H' 1 (Opens.mayerVietorisSquare U0 U1).toSquare.X₄)) b = 0
  rfl


-- @@ L423-423 verbatim
end DeltaZero


-- @@ L425-425 verbatim
/-! ## Part 4. Leg 2: the `H¹`-squeeze -/


-- @@ L427-427 verbatim
section Squeeze


-- @@ L429-463 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **LEG 2 (per-object form)** — `H'¹(U0 ⊔ U1, 𝒪)` is a subsingleton: by
exactness of the Mayer–Vietoris sequence at the `H'¹(U0 ⊔ U1)`-node every
class comes from `δ` (the outer chart terms vanish by stage 1), and `δ = 0`
by Leg 1. -/
theorem subsingleton_hPrimeOne_sup :
    Subsingleton (Ext (freeYonedaSheaf JP1 (U0 ⊔ U1)) structO 1) := by
  refine subsingleton_of_forall_eq 0 fun x => ?_
  haveI hs2 : Subsingleton
      (structO.H' 1 (Opens.mayerVietorisSquare U0 U1).toSquare.X₂) :=
    subsingleton_hPrimeOne_U0
  haveI hs3 : Subsingleton
      (structO.H' 1 (Opens.mayerVietorisSquare U0 U1).toSquare.X₃) :=
    subsingleton_hPrimeOne_U1
  haveI hprod : Subsingleton
      ((structO.H' 1 (Opens.mayerVietorisSquare U0 U1).toSquare.X₂ :
          AddCommGrpCat.{0}) ×
        (structO.H' 1 (Opens.mayerVietorisSquare U0 U1).toSquare.X₃ :
          AddCommGrpCat.{0})) :=
    ⟨fun p q => Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)⟩
  haveI hbi : Subsingleton
      ((structO.H' 1 (Opens.mayerVietorisSquare U0 U1).toSquare.X₂ ⊞
        structO.H' 1 (Opens.mayerVietorisSquare U0 U1).toSquare.X₃ :
          AddCommGrpCat.{0})) :=
    ((AddCommGrpCat.biprodIsoProd
      (structO.H' 1 (Opens.mayerVietorisSquare U0 U1).toSquare.X₂)
      (structO.H' 1 (Opens.mayerVietorisSquare U0 U1).toSquare.X₃)
      ).addCommGroupIsoToAddEquiv.toEquiv).subsingleton
  have htoB : (Opens.mayerVietorisSquare U0 U1).toBiprod structO 1 x = 0 :=
    Subsingleton.elim _ _
  have hex := ((Opens.mayerVietorisSquare U0 U1).sequence_exact structO 0 1 rfl).exact 2
  obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).mp hex x htoB
  have hy' : (Opens.mayerVietorisSquare U0 U1).δ structO 0 1 rfl y = x := hy
  rw [← hy']
  exact deltaO_eq_zero y


-- @@ L465-472 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- Leg 2 at the terminal anchor: `H'¹(⊤, 𝒪)` is a subsingleton (the two
charts cover the projective line). -/
theorem subsingleton_hPrimeOne_top :
    Subsingleton (Ext (freeYonedaSheaf JP1 (⊤ : p1.Opens)) structO 1) := by
  haveI := subsingleton_hPrimeOne_sup
  exact ((CycCarrier.extReanchorLeft
    (eqToIso (congrArg (freeYonedaSheaf JP1) U0_sup_U1)) 1).symm.toEquiv).subsingleton


-- @@ L474-484 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **LEG 2 — `H¹(ℙ¹, 𝒪-carrier)` vanishes**: the first cohomology of the
structure-sheaf carrier of the projective line is a subsingleton in the sense
of Mathlib's `Sheaf.H` (along the wave-3 terminal-anchor re-isomorphism).
Nothing is claimed for any other scheme, any other sheaf, or any other
cohomology theory; nothing here makes the Hodge conjecture statable. -/
theorem subsingleton_H_one_structO :
    Subsingleton (Sheaf.H (HodgePilot.DeRhamSheaf.deRhamSheafSpace φC 0) 1) := by
  haveI := subsingleton_hPrimeOne_top
  exact ((hPrimeTopEquivH (⊤ : p1.Opens) (CartierClass.opensTopIsTerminal p1)
    structO 1).symm.toEquiv).subsingleton


-- @@ L486-486 verbatim
end Squeeze


-- @@ L488-488 verbatim
/-! ## Part 5. Leg 3: the retirement of `InterferenceExclusion` -/


-- @@ L490-490 verbatim
section Retirement


-- @@ L492-504 verbatim
/-- **Wave 3's named `Prop` `InterferenceExclusion` HOLDS** at its literal
spelling: the map `H¹(𝒪) → H¹(Ω¹)` induced by the exterior differential
kills every class — the source group is a subsingleton by Leg 2, and an
additive map sends `0` to `0`.  (The `Prop` remains stated in
`HodgePilot.ProjectiveLineGraded`, where its docstring — written before this
module — records it as the honest wall; this theorem is its proof, exactly
the `GradedTruncationDetection` retirement pattern.)  Nothing here makes the
Hodge conjecture statable. -/
theorem interferenceExclusion : ProjectiveLineGraded.InterferenceExclusion := by
  intro x
  haveI := subsingleton_H_one_structO
  rw [Subsingleton.elim x 0]
  exact map_zero _


-- @@ L506-511 verbatim
/-- Statement-drift guard (definitional receipt): the `Prop` proved above is
the literal parked spelling of `HodgePilot.ProjectiveLineGraded`. -/
theorem interferenceExclusion_receipt :
    ProjectiveLineGraded.InterferenceExclusion =
      (∀ x : Sheaf.H (HodgePilot.DeRhamSheaf.deRhamSheafSpace φC 0) 1,
        Sheaf.H.map ProjectiveLineGraded.dSpaceZeroOne 1 x = 0) := rfl


-- @@ L513-517 verbatim
/-- The bundled form of the retirement: the induced map on `H¹` is the zero
homomorphism. -/
theorem hMap_dSpaceZeroOne_eq_zero :
    Sheaf.H.map ProjectiveLineGraded.dSpaceZeroOne 1 = 0 :=
  AddMonoidHom.ext fun x => interferenceExclusion x


-- @@ L519-519 verbatim
end Retirement


-- @@ L521-521 verbatim
end InterferenceProof


-- @@ L523-523 verbatim
end HodgePilot


-- @@ L525-525 verbatim
end
