import HodgePilot.ProjectiveLineUnits


-- @@ L3-85 verbatim
/-! # Degree-4 negative calibration: the degree-4 self-pairing value of the
# point divisor on ℙ¹ is zero, because the constructed degree-4 carrier is
# trivial

**The theorem** (`dinfPairedInto_eq_zero`, with `subsingleton_F2H4` and
`dinfPairedInto_coe_eq_zero`): the degree-4 self-pairing value of the point
divisor on ℙ¹ is zero because the constructed degree-4 carrier is trivial.
This is a **negative-calibration receipt about the CONSTRUCTED carrier** of
`HodgePilot.CyclePairing`/`HodgePilot.ProjectiveLine`, in the sense of the
outside review's degree-4 warning: for the genuine cohomology of a curve the
degree-4 group vanishes, so any degree-4 self-product of a divisor class
must be zero there; this module proves that the constructed analogue —
`ProjectiveLine.dinfPairedInto`, the landed self-pairing of the
Mayer–Vietoris point-divisor datum `dinf` in the `F²` step of the naive
(brutal-truncation) filtration of the degree-4 hypercohomology of the
constructed de Rham complex of ℤ-module sheaves on the small affine Zariski
site — is itself zero, **and for the structural reason one should expect**:

* the section ring of each standard chart of `ℙ¹ = Proj ℂ[X₀, X₁]` is a
  singly generated `ℂ`-algebra (wave 2's chart isomorphism
  `chartPolyEquiv`, made a `Sec`-algebra map by the **constants receipt**
  `constants_receipt` proved here: the `cRingHom structMor` constants
  restrict on each chart to the `instAlgebraAwayC` constants);
* hence its Kähler differentials are spanned by one element
  (`span_D_singleton_of_adjoin`) and the presented de Rham terms
  `DeRham.DR` vanish in degrees `≥ 2` (`subsingleton_DR_of_adjoin_singleton`
  through `DeRham.exteriorPowerEquiv`);
* the vanishing propagates from the charts to every affine open of `ℙ¹`
  along the shipped localization transfer of `HodgePilot.DeRhamSheaf`
  (`subsingleton_DR_basicOpen`, `subsingleton_DR_all` — basic-open bases of
  affine opens plus the shipped separatedness
  `DeRhamSheaf.eq_of_res_map_eq_of_span`);
* so the degree-`≥ 2` de Rham sheaves of `ℙ¹` are zero objects
  (`isZero_deRhamSheafZ`), the brutal truncation `σ≥2` of the reindexed de
  Rham complex is termwise zero (`isZero_trunc_X`, `isZero_trunc_complex`),
  its inclusion is the zero chain map (`ιBrutalTruncGE_two_eq_zero`), and
  therefore **the `F²` step of the naive filtration is the zero subgroup in
  every hypercohomology degree and against every anchor**
  (`eq_zero_of_mem_filtration_two`), and the truncated carrier itself is a
  subsingleton (`subsingleton_affineZHyperH_trunc`);
* `dinfPairedInto` lands in `F²` **by construction**
  (`ProjectiveLine.dinfPairedInto_mem`), so it is zero; the drift guard
  `dinfPairedInto_receipt` pins the subject to wave 1's literal landed
  self-pairing.

## Claim discipline (each clause is load-bearing)

This is a calibration receipt about the **constructed** carrier and the
**constructed** pairing-shaped assignment only.  The constructed degree-4
carrier is **not** claimed to be, to compute, or to compare with the
classical `H⁴` of any cohomology theory; no comparison map, isomorphism, or
comparison theorem is stated, implied, or approached.  The pairing whose
value is proved zero is `HodgePilot.CyclePairing`'s constructed
pairing-shaped assignment: it is **not** the cup product, it is **not**
identified with any classical intersection pairing, and the zero proved here
is a statement about the exhibited construction, **not** a computation of
any classical intersection number.  The vanishing mechanism is a
degree-collapse of the constructed carrier (the presented de Rham terms of
the chart section rings die in degrees `≥ 2`), so this receipt calibrates
the carrier itself: a degree-4 NONVANISHING through this carrier on `ℙ¹`
would have signalled a defect, and this module proves no such value can be
nonzero.  The filtration is the **naive** (brutal-truncation) filtration
throughout; no Hodge-theoretic content, no `H^{p,q}`, no degeneration
statement.  No smoothness or dimension predicate of any kind is defined or
claimed — "the charts are singly generated `ℂ`-algebras" is the exact
algebraic statement proved and consumed.  Nothing here makes the Hodge
conjecture statable.

## Credits

`Proj`, its chart API (`awayι`, `awayToSection`, `basicOpenIsoSpec`,
`toSpecZero` and its `awayι_toSpecZero`) and the small affine Zariski site
with its `IsAffineOpen` basic-open interface are Andrew Yang's (and
collaborators') Mathlib infrastructure; `ΓSpecIso` naturality is the
Γ–Spec adjunction of Mathlib; the Kähler differential presentation and
`exteriorPower` API are A. Cavalleri, A. Yang, S. Morel and J. Riou's; the
derived-category and shift infrastructure is Joël Riou's.  The presented de
Rham complex, its exterior-power identification, its sheaf condition and
localization transfer are `HodgePilot.DeRham`/`DeRhamExterior`/
`DeRhamSheaf`/`DeRhamLocalize`; the object, divisor datum, pairing and
landing are `HodgePilot.ProjectiveLine`/`ProjectiveLineUnits`/
`CyclePairing`.
-/


-- @@ L87-87 verbatim
set_option maxHeartbeats 1000000

-- @@ L88-88 verbatim
set_option synthInstance.maxHeartbeats 1000000


-- @@ L90-90 verbatim
noncomputable section


-- @@ L92-92 verbatim
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

-- @@ L93-93 verbatim
open AlgebraicGeometry HomogeneousLocalization KaehlerDifferential


-- @@ L95-95 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L97-97 verbatim
namespace HodgePilot


-- @@ L99-99 verbatim
namespace CalibrationDegreeFour


-- @@ L101-101 verbatim
open HodgePilot.DeRham HodgePilot.DeRhamPresheaf HodgePilot.DeRhamSheaf

-- @@ L102-102 verbatim
open HodgePilot.DeRhamWedgeChain HodgePilot.CyclePairing HodgePilot.Hyper

-- @@ L103-103 verbatim
open HodgePilot.ProjectiveLine HodgePilot.ProjectiveLineUnits


-- @@ L105-107 verbatim
/-! ## 1. Generic: exterior powers of a singly-spanned module vanish in
degrees `>= 2`, hence so do the presented de Rham terms of a singly-generated
algebra -/


-- @@ L109-109 verbatim
section GenericAlgebra


-- @@ L111-111 verbatim
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]


-- @@ L113-136 verbatim
/-- Every element of an exterior power `>= 2` of a module spanned by a single
element is zero. -/
theorem exteriorPower_eq_zero_of_span_singleton {w : M}
    (hw : Submodule.span R {w} = (⊤ : Submodule R M)) {p : ℕ} (hp : 2 ≤ p)
    (x : ⋀[R]^p M) : x = 0 := by
  have hx : x ∈ (⊤ : Submodule R (⋀[R]^p M)) := Submodule.mem_top
  rw [← exteriorPower.ιMulti_span] at hx
  refine Submodule.span_induction ?_ rfl (fun y z _ _ hy hz => by rw [hy, hz, add_zero])
    (fun c y _ hy => by rw [hy, smul_zero]) hx
  rintro _ ⟨v, rfl⟩
  have hc : ∀ i : Fin p, ∃ c : R, c • w = v i := fun i =>
    Submodule.mem_span_singleton.mp (hw ▸ Submodule.mem_top)
  choose c hc using hc
  have hv : v = fun i => c i • (fun _ : Fin p => w) i := funext fun i => (hc i).symm
  have h01 : (0 : ℕ) < p := lt_of_lt_of_le Nat.zero_lt_two hp
  have h11 : (1 : ℕ) < p := lt_of_lt_of_le Nat.one_lt_two hp
  have h0 : exteriorPower.ιMulti R p (fun _ : Fin p => w) = 0 :=
    AlternatingMap.map_eq_zero_of_eq _ _ (rfl : w = w)
      (show (⟨0, h01⟩ : Fin p) ≠ ⟨1, h11⟩ from
        fun h => Nat.zero_ne_one (congrArg Fin.val h))
  have hsm : (exteriorPower.ιMulti R p) (fun i => c i • (fun _ : Fin p => w) i) =
      (∏ i, c i) • (exteriorPower.ιMulti R p) (fun _ : Fin p => w) :=
    MultilinearMap.map_smul_univ (exteriorPower.ιMulti R p).toMultilinearMap c _
  rw [hv, hsm, h0, smul_zero]


-- @@ L138-138 verbatim
variable {A : Type} {B : Type} [CommRing A] [CommRing B] [Algebra A B]


-- @@ L140-162 verbatim
/-- If `B` is generated as an `A`-algebra by the single element `x`, then the
Kähler differentials `Ω[B⁄A]` are spanned over `B` by the single element
`D x` (the universal derivation kills constants and satisfies Leibniz). -/
theorem span_D_singleton_of_adjoin {x : B} (hx : Algebra.adjoin A {x} = ⊤) :
    Submodule.span B {KaehlerDifferential.D A B x} = ⊤ := by
  refine le_antisymm le_top ?_
  rw [← KaehlerDifferential.span_range_derivation]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨b, rfl⟩
  have hb : b ∈ Algebra.adjoin A ({x} : Set B) := hx ▸ Algebra.mem_top
  induction hb using Algebra.adjoin_induction with
  | mem y hy =>
      obtain rfl : y = x := hy
      exact Submodule.mem_span_singleton_self _
  | algebraMap r =>
      rw [Derivation.map_algebraMap]
      exact Submodule.zero_mem _
  | add y z _ _ hy hz =>
      rw [map_add]
      exact Submodule.add_mem _ hy hz
  | mul y z _ _ hy hz =>
      rw [Derivation.leibniz]
      exact Submodule.add_mem _ (Submodule.smul_mem _ _ hz) (Submodule.smul_mem _ _ hy)


-- @@ L164-174 verbatim
/-- **The presented de Rham terms of a singly-generated algebra vanish in
degrees `≥ 2`**: through `DeRham.exteriorPowerEquiv`, every degree-`≥ 2` term
is an exterior power (over `B`) of the singly-spanned `Ω[B⁄A]`. -/
theorem subsingleton_DR_of_adjoin_singleton {x : B}
    (hx : Algebra.adjoin A {x} = ⊤) {p : ℕ} (hp : 2 ≤ p) :
    Subsingleton (DeRham.DR A B p) := by
  have h1 : Subsingleton (⋀[B]^p (Ω[B⁄A])) := by
    refine subsingleton_of_forall_eq 0 fun y => ?_
    exact (exteriorPower_eq_zero_of_span_singleton
      (span_D_singleton_of_adjoin hx) hp y).symm ▸ rfl
  exact Equiv.subsingleton (DeRham.exteriorPowerEquiv A B p).toEquiv


-- @@ L176-176 verbatim
end GenericAlgebra


-- @@ L178-180 verbatim
/-! ## 2. The constants receipt: the structure `ℂ`-algebra constants of the
section rings restrict, on each chart, to the chart-ring constants of
`ProjectiveLineUnits.instAlgebraAwayC` -/


-- @@ L182-182 verbatim
section ConstantsReceipt


-- @@ L184-185 verbatim
/-- The standard grading of `ℂ[X₀, X₁]` by total degree. -/
local notation "𝒜₂" => MvPolynomial.homogeneousSubmodule (Fin 2) ℂ


-- @@ L187-190 verbatim
/-- The chart `D₊(Xᵢ)` (so `chartOpen 0 = U0` and `chartOpen 1 = U1`,
definitionally). -/
abbrev chartOpen (i : Fin 2) : p1.Opens :=
  Proj.basicOpen 𝒜₂ (MvPolynomial.X i)


-- @@ L192-201 verbatim
/-- The constants of the two `ℂ`-structures agree before the section map:
`gradeZeroEquiv` followed by `fromZeroRingHom` is the `instAlgebraAwayC`
algebra map of the chart ring. -/
theorem gradeZero_fromZero_eq_algebraMap (i : Fin 2) :
    gradeZeroEquiv.toCommRingCatIso.hom ≫
      CommRingCat.ofHom
        (fromZeroRingHom 𝒜₂ (Submonoid.powers (MvPolynomial.X i))) =
    CommRingCat.ofHom (algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X i))) := by
  ext c
  rfl


-- @@ L203-220 verbatim
/-- **Spec-side constants comparison**: the structure constants followed by
the (global sections of the) chart immersion `awayι` are the chart-ring
constants, read through `ΓSpecIso`.  This is the pin's `awayι_toSpecZero`
composed with the `ΓSpecIso` naturality squares. -/
theorem constants_awayι (i : Fin 2) :
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ structMor.appTop) ≫
      (Proj.awayι 𝒜₂ (MvPolynomial.X i) (X_mem_grade_one i) one_pos).appTop =
    CommRingCat.ofHom (algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X i))) ≫
      (Scheme.ΓSpecIso
        (CommRingCat.of (Away 𝒜₂ (MvPolynomial.X i)))).inv := by
  have hs : structMor =
      Proj.toSpecZero 𝒜₂ ≫ Spec.map (gradeZeroEquiv.toCommRingCatIso.hom) :=
    rfl
  rw [hs, Scheme.Hom.comp_appTop, Category.assoc, Category.assoc,
    ← Scheme.Hom.comp_appTop, Proj.awayι_toSpecZero, ← Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, Category.assoc,
    ← Scheme.ΓSpecIso_inv_naturality, ← Category.assoc,
    gradeZero_fromZero_eq_algebraMap]


-- @@ L222-229 verbatim
/-- The global sections of the chart immersion, followed by the top-sections
identification of the chart, are the restriction map of the presheaf. -/
theorem chart_ι_appTop_topIso (i : Fin 2) :
    (chartOpen i).ι.appTop ≫ (chartOpen i).topIso.hom =
      p1.presheaf.map (homOfLE (le_top : chartOpen i ≤ ⊤)).op := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  exact (p1.presheaf.map_comp _ _).symm.trans
    (congrArg p1.presheaf.map (Subsingleton.elim _ _))


-- @@ L231-238 verbatim
/-- `awayι` against the chart inclusion (global sections). -/
theorem awayι_appTop (i : Fin 2) :
    (Proj.awayι 𝒜₂ (MvPolynomial.X i) (X_mem_grade_one i) one_pos).appTop =
      (chartOpen i).ι.appTop ≫
        (Proj.basicOpenIsoSpec 𝒜₂ (MvPolynomial.X i)
          (X_mem_grade_one i) one_pos).inv.appTop := by
  rw [← Scheme.Hom.comp_appTop]
  rfl


-- @@ L240-249 verbatim
/-- The `basicOpenIsoSpec` global sections, spelled through `awayToSection`
(the pin's `basicOpenToSpec_app_top`). -/
theorem basicOpenIsoSpec_hom_appTop (i : Fin 2) :
    (Proj.basicOpenIsoSpec 𝒜₂ (MvPolynomial.X i)
        (X_mem_grade_one i) one_pos).hom.appTop =
      (Scheme.ΓSpecIso (CommRingCat.of (Away 𝒜₂ (MvPolynomial.X i)))).hom ≫
        Proj.awayToSection 𝒜₂ (MvPolynomial.X i) ≫
        (chartOpen i).topIso.inv := by
  rw [Proj.basicOpenIsoSpec_hom]
  exact Proj.basicOpenToSpec_app_top 𝒜₂ (MvPolynomial.X i)


-- @@ L251-269 verbatim
/-- **The constants receipt, hom level**: the structure constants of the
section rings, restricted to a chart, are the chart-ring constants pushed
along the pin's `awayToSection`. -/
theorem constants_section_hom (i : Fin 2) :
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ structMor.appTop) ≫
      p1.presheaf.map (homOfLE (le_top : chartOpen i ≤ ⊤)).op =
    CommRingCat.ofHom (algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X i))) ≫
      Proj.awayToSection 𝒜₂ (MvPolynomial.X i) := by
  have hι : (chartOpen i).ι.appTop =
      (Proj.awayι 𝒜₂ (MvPolynomial.X i) (X_mem_grade_one i) one_pos).appTop ≫
        (Proj.basicOpenIsoSpec 𝒜₂ (MvPolynomial.X i)
          (X_mem_grade_one i) one_pos).hom.appTop := by
    rw [awayι_appTop, Category.assoc, ← Scheme.Hom.comp_appTop,
      Iso.hom_inv_id, Scheme.Hom.id_appTop, Category.comp_id]
  rw [← chart_ι_appTop_topIso, hι, basicOpenIsoSpec_hom_appTop]
  simp only [← Category.assoc]
  rw [constants_awayι]
  simp only [Category.assoc]
  rw [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]


-- @@ L271-283 verbatim
/-- **The constants receipt, elementwise**: the `Sec`-algebra constants of
`DeRhamPresheaf` (through `cRingHom structMor`) restrict on the chart to the
`instAlgebraAwayC` constants pushed along `awaySection`. -/
theorem constants_receipt (i : Fin 2) (c : ℂ) :
    res (cRingHom structMor) (le_top : chartOpen i ≤ ⊤) (cRingHom structMor c) =
      awaySection (MvPolynomial.X i)
        (algebraMap ℂ (Away 𝒜₂ (MvPolynomial.X i)) c) := by
  have h1 : res (cRingHom structMor) (le_top : chartOpen i ≤ ⊤)
      (cRingHom structMor c) =
      (((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ structMor.appTop) ≫
        p1.presheaf.map (homOfLE (le_top : chartOpen i ≤ ⊤)).op).hom c := rfl
  rw [h1, constants_section_hom]
  rfl


-- @@ L285-286 verbatim
/-! ## 3. The chart seed: the section rings of the charts are singly
generated `ℂ`-algebras, so their de Rham terms vanish in degrees `≥ 2` -/


-- @@ L288-294 verbatim
/-- `awaySection` as a `ℂ`-algebra map onto the `Sec`-algebra of the chart
(the receipt `constants_receipt` is exactly the `commutes'` field). -/
def awaySectionAlgHom (i : Fin 2) :
    Away 𝒜₂ (MvPolynomial.X i) →ₐ[ℂ]
      Sec (cRingHom structMor) (chartOpen i) where
  toRingHom := awaySection (MvPolynomial.X i)
  commutes' c := (constants_receipt i c).symm


-- @@ L296-300 verbatim
theorem awaySectionAlgHom_surjective (i : Fin 2) :
    Function.Surjective (awaySectionAlgHom i) := by
  haveI := isIso_awayToSection (X_mem_grade_one i) one_pos
  exact (ConcreteCategory.bijective_of_isIso
    (Proj.awayToSection 𝒜₂ (MvPolynomial.X i))).surjective


-- @@ L302-306 verbatim
/-- The polynomial ring maps onto the chart section ring, as `ℂ`-algebras
(wave 2's chart isomorphism followed by the receipt-equipped section map). -/
def chartPoly (i j : Fin 2) (hij : i ≠ j) :
    MvPolynomial (Fin 1) ℂ →ₐ[ℂ] Sec (cRingHom structMor) (chartOpen i) :=
  (awaySectionAlgHom i).comp (chartPolyEquiv i j hij).symm.toAlgHom


-- @@ L308-310 verbatim
theorem chartPoly_surjective (i j : Fin 2) (hij : i ≠ j) :
    Function.Surjective (chartPoly i j hij) :=
  (awaySectionAlgHom_surjective i).comp (chartPolyEquiv i j hij).symm.surjective


-- @@ L312-327 verbatim
/-- **The chart section rings are singly generated `ℂ`-algebras** (by the
image of the coordinate variable). -/
theorem adjoin_chartGen (i j : Fin 2) (hij : i ≠ j) :
    Algebra.adjoin ℂ
      ({chartPoly i j hij (MvPolynomial.X 0)} :
        Set (Sec (cRingHom structMor) (chartOpen i))) = ⊤ := by
  have h3 : Subalgebra.map (chartPoly i j hij)
      (Algebra.adjoin ℂ (Set.range (MvPolynomial.X : Fin 1 → _))) =
      Algebra.adjoin ℂ
        (chartPoly i j hij '' Set.range (MvPolynomial.X : Fin 1 → _)) :=
    AlgHom.map_adjoin _ _
  rw [MvPolynomial.adjoin_range_X, Algebra.map_top,
    (AlgHom.range_eq_top _).mpr (chartPoly_surjective i j hij),
    Set.range_unique, Set.image_singleton] at h3
  rw [show (default : Fin 1) = 0 from rfl] at h3
  exact h3.symm


-- @@ L329-333 verbatim
/-- **The chart de Rham terms vanish in degrees `≥ 2`.** -/
theorem subsingleton_DR_chart (i j : Fin 2) (hij : i ≠ j) {p : ℕ}
    (hp : 2 ≤ p) :
    Subsingleton (DeRham.DR ℂ (Sec (cRingHom structMor) (chartOpen i)) p) :=
  subsingleton_DR_of_adjoin_singleton (adjoin_chartGen i j hij) hp


-- @@ L335-337 verbatim
/-! ## 4. Propagation: from the charts to every affine open, by the shipped
localization transfer (`DeRhamSheaf`) and the basic-open bases of affine
opens -/


-- @@ L339-344 verbatim
/-- Transport of the vanishing along an equality of opens. -/
theorem subsingleton_DR_congr {V W : p1.Opens} (h : V = W) {p : ℕ}
    (hV : Subsingleton (DeRham.DR ℂ (Sec (cRingHom structMor) V) p)) :
    Subsingleton (DeRham.DR ℂ (Sec (cRingHom structMor) W) p) := by
  subst h
  exact hV


-- @@ L346-358 verbatim
/-- **Propagation to basic opens** (the shipped `DeRhamSheaf` localization
transfer): if the de Rham term vanishes over an affine `U`, it vanishes over
every basic open `D(f) ⊆ U`. -/
theorem subsingleton_DR_basicOpen (U : p1.AffineZariskiSite) {p : ℕ}
    (hU : Subsingleton (DeRham.DR ℂ (Sec (cRingHom structMor) U.toOpens) p))
    (f : Sec (cRingHom structMor) U.toOpens) :
    Subsingleton (DeRham.DR ℂ
      (Sec (cRingHom structMor) (p1.basicOpen f)) p) := by
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨z, k, hzk⟩ :=
    DeRhamSheaf.exists_res_map_eq_pow_smul (cRingHom structMor) U f p y
  rw [Subsingleton.elim z 0, map_zero] at hzk
  exact DeRhamSheaf.eq_zero_of_res_pow_smul_eq_zero (cRingHom structMor) U f p k hzk


-- @@ L360-364 verbatim
/-- The chart, as an object of the small affine Zariski site (the pin's
`Proj.isAffineOpen_basicOpen`). -/
def chartAffine (i : Fin 2) : p1.AffineZariskiSite :=
  ⟨chartOpen i,
    Proj.isAffineOpen_basicOpen 𝒜₂ (MvPolynomial.X i) (X_mem_grade_one i) one_pos⟩


-- @@ L366-394 verbatim
/-- Through a point of an affine open `U` lying in the chart `i`, there is a
basic open of `U` with vanishing de Rham term (two applications of
`IsAffineOpen.exists_basicOpen_le`, through a chart-basic middle open). -/
theorem exists_basicOpen_subsingleton (U : p1.AffineZariskiSite) {p : ℕ}
    (hp : 2 ≤ p) {x : p1} (hxU : x ∈ U.toOpens) (i j : Fin 2) (hij : i ≠ j)
    (hxi : x ∈ chartOpen i) :
    ∃ f : Sec (cRingHom structMor) U.toOpens,
      Subsingleton (DeRham.DR ℂ
        (Sec (cRingHom structMor) (p1.basicOpen f)) p) ∧
        x ∈ p1.basicOpen f := by
  -- a chart-basic open through `x` inside `U`
  obtain ⟨g, hgU, hxg⟩ :=
    (chartAffine i).2.exists_basicOpen_le (⟨x, hxU⟩ : U.toOpens) hxi
  -- its de Rham term vanishes, by the chart seed and one propagation
  have hWg : Subsingleton (DeRham.DR ℂ
      (Sec (cRingHom structMor) (p1.basicOpen g)) p) :=
    subsingleton_DR_basicOpen (chartAffine i)
      (subsingleton_DR_chart i j hij hp) g
  -- a `U`-basic refinement through `x`
  obtain ⟨f, hf_le, hxf⟩ :=
    U.2.exists_basicOpen_le (⟨x, hxg⟩ : (p1.basicOpen g : p1.Opens)) hxU
  refine ⟨f, ?_, hxf⟩
  -- `D(f)` is a basic open of `D(g)` (restrict the section)
  have hb : p1.basicOpen (res (cRingHom structMor) hgU f) = p1.basicOpen f := by
    rw [res_apply, Scheme.basicOpen_res]
    exact inf_eq_right.mpr hf_le
  exact subsingleton_DR_congr hb
    (subsingleton_DR_basicOpen ⟨p1.basicOpen g, (chartAffine i).2.basicOpen g⟩
      hWg (res (cRingHom structMor) hgU f))


-- @@ L396-423 verbatim
/-- **The de Rham terms of degree `≥ 2` vanish over every affine open of the
projective line**: the two charts cover, each point of an affine open has a
chart-subordinated basic open with vanishing term, such basic opens span by
`IsAffineOpen.iSup_basicOpen_eq_self_iff`, and the shipped separatedness
`DeRhamSheaf.eq_of_res_map_eq_of_span` pulls the vanishing up to `U`. -/
theorem subsingleton_DR_all (U : p1.AffineZariskiSite) {p : ℕ} (hp : 2 ≤ p) :
    Subsingleton (DeRham.DR ℂ (Sec (cRingHom structMor) U.toOpens) p) := by
  classical
  set s : Set (Sec (cRingHom structMor) U.toOpens) :=
    {f | Subsingleton (DeRham.DR ℂ
      (Sec (cRingHom structMor) (p1.basicOpen f)) p)} with hs
  have hcov : (⨆ f : s, p1.basicOpen (f.1 : Γ(p1, U.toOpens))) = U.toOpens := by
    refine le_antisymm (iSup_le fun f => p1.basicOpen_le f.1) fun x hx => ?_
    have hx2 : x ∈ U0 ⊔ U1 := by rw [U0_sup_U1]; trivial
    have hchart : ∃ (i j : Fin 2), i ≠ j ∧ x ∈ chartOpen i := by
      rcases (Opens.mem_sup).mp hx2 with h0 | h1
      · exact ⟨0, 1, by decide, h0⟩
      · exact ⟨1, 0, by decide, h1⟩
    obtain ⟨i, j, hij, hxi⟩ := hchart
    obtain ⟨f, hf, hxf⟩ := exists_basicOpen_subsingleton U hp hx i j hij hxi
    exact Opens.mem_iSup.mpr ⟨⟨f, hf⟩, hxf⟩
  have hspan : Ideal.span s = ⊤ := U.2.iSup_basicOpen_eq_self_iff.mp hcov
  refine subsingleton_of_forall_eq 0 fun z => ?_
  refine DeRhamSheaf.eq_of_res_map_eq_of_span (cRingHom structMor) U hspan p
    (fun f hf => ?_)
  haveI : Subsingleton (DeRham.DR ℂ
      (Sec (cRingHom structMor) (p1.basicOpen f)) p) := hf
  exact Subsingleton.elim _ _


-- @@ L425-427 verbatim
/-! ## 5. The constructed carrier collapses: the degree-`≥ 2` de Rham
sheaves are zero objects, the brutal truncation `σ≥2` is termwise zero, and
the `F²` step of every hypercohomology degree is the zero subgroup -/


-- @@ L429-440 verbatim
/-- **The degree-`≥ 2` de Rham sheaves of the projective line are zero
objects** (of the category of `ℤ`-module sheaves on the small affine
Zariski site). -/
theorem isZero_deRhamSheafZ {m : ℕ} (hm : 2 ≤ m) :
    IsZero (deRhamSheafZ (cRingHom structMor) m) := by
  rw [IsZero.iff_id_eq_zero]
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun U => ?_)
  haveI : Subsingleton
      ((deRhamSheafZ (cRingHom structMor) m).obj.obj U) :=
    subsingleton_DR_all U.unop hm
  exact ModuleCat.hom_ext (LinearMap.ext fun x => Subsingleton.elim _ _)


-- @@ L442-457 verbatim
/-- Every term of the brutal truncation `σ≥2` of the reindexed de Rham
complex of the projective line is a zero object. -/
theorem isZero_trunc_X (n : ℤ) :
    IsZero ((brutalTruncGE
      (reindexZ (deRhamSheafZComplexN (cRingHom structMor))) 2).X n) := by
  by_cases hn : n < 2
  · exact isZero_brutalTruncGE_X _ 2 n hn
  · rw [not_lt] at hn
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) :=
      ⟨n.toNat, (Int.toNat_of_nonneg (by lia)).symm⟩
    have hm : 2 ≤ m := by exact_mod_cast hn
    exact (isZero_deRhamSheafZ hm).of_iso
      ((brutalTruncGEXIso
          (reindexZ (deRhamSheafZComplexN (cRingHom structMor))) 2 (m : ℤ)
          (by exact_mod_cast hm)) ≪≫
        reindexZXIso (deRhamSheafZComplexN (cRingHom structMor)) m)


-- @@ L459-464 verbatim
/-- **The inclusion of the brutal truncation `σ≥2` is the zero chain map**
(its source is termwise zero). -/
theorem ιBrutalTruncGE_two_eq_zero :
    ιBrutalTruncGE (reindexZ (deRhamSheafZComplexN (cRingHom structMor))) 2 =
      0 :=
  HomologicalComplex.hom_ext _ _ fun n => (isZero_trunc_X n).eq_of_src _ _


-- @@ L466-482 verbatim
/-- **The `F²` step of the naive filtration is the zero subgroup, in every
hypercohomology degree and against every anchor**: it is the range of the
map induced by the (zero) truncation inclusion. -/
theorem eq_zero_of_mem_filtration_two
    (Z : Sheaf (Scheme.AffineZariskiSite.grothendieckTopology p1)
      (ModuleCat.{0} ℤ)) (n : ℤ)
    (x : affineZHyperH p1 Z
      (reindexZ (deRhamSheafZComplexN (cRingHom structMor))) n)
    (hx : x ∈ affineZHodgeFiltration p1 Z
      (reindexZ (deRhamSheafZComplexN (cRingHom structMor))) 2 n) :
    x = 0 := by
  letI := HasDerivedCategory.standard
    (Sheaf (Scheme.AffineZariskiSite.grothendieckTopology p1) (ModuleCat.{0} ℤ))
  obtain ⟨y, rfl⟩ := (mem_hodgeFiltration_iff _ _ _ _ _).mp hx
  rw [hyperHMap_apply, ιBrutalTruncGE_two_eq_zero, Functor.map_zero,
    Functor.map_zero, Limits.comp_zero]
  rfl


-- @@ L484-490 verbatim
/-- The brutal truncation `σ≥2` of the reindexed de Rham complex of the
projective line is a zero object of the category of complexes. -/
theorem isZero_trunc_complex :
    IsZero (brutalTruncGE
      (reindexZ (deRhamSheafZComplexN (cRingHom structMor))) 2) := by
  rw [IsZero.iff_id_eq_zero]
  exact HomologicalComplex.hom_ext _ _ fun n => (isZero_trunc_X n).eq_of_src _ _


-- @@ L492-511 verbatim
/-- **The truncated degree-`n` carrier is trivial, for every anchor and every
degree**: the hypercohomology of the (termwise zero) truncation `σ≥2` is a
subsingleton. -/
theorem subsingleton_affineZHyperH_trunc
    (Z : Sheaf (Scheme.AffineZariskiSite.grothendieckTopology p1)
      (ModuleCat.{0} ℤ)) (n : ℤ) :
    Subsingleton (affineZHyperH p1 Z
      (brutalTruncGE (reindexZ (deRhamSheafZComplexN (cRingHom structMor))) 2)
      n) := by
  letI := HasDerivedCategory.standard
    (Sheaf (Scheme.AffineZariskiSite.grothendieckTopology p1) (ModuleCat.{0} ℤ))
  have h1 : IsZero (DerivedCategory.Q.obj
      (brutalTruncGE (reindexZ (deRhamSheafZComplexN (cRingHom structMor))) 2)) :=
    Functor.map_isZero _ isZero_trunc_complex
  have h2 : IsZero ((shiftFunctor (DerivedCategory
      (Sheaf (Scheme.AffineZariskiSite.grothendieckTopology p1)
        (ModuleCat.{0} ℤ))) n).obj (DerivedCategory.Q.obj
      (brutalTruncGE (reindexZ (deRhamSheafZComplexN (cRingHom structMor))) 2))) :=
    Functor.map_isZero _ h1
  exact ⟨fun a b => h2.eq_of_tgt a b⟩


-- @@ L513-514 verbatim
/-! ## 6. The calibration: the degree-4 self-pairing value of the point
divisor is zero, because the constructed degree-4 carrier is trivial -/


-- @@ L516-526 verbatim
/-- **The constructed degree-4 carrier is trivial**: the `F²` step of the
naive filtration of the constructed degree-4 hypercohomology — the codomain
subtype in which `ProjectiveLine.dinfPairedInto` lands by construction — is a
subsingleton. -/
theorem subsingleton_F2H4 :
    Subsingleton
      ↥(affineZHodgeFiltration p1 (pairAnchorAffine p1)
        (reindexZ (deRhamSheafZComplexN (cRingHom structMor))) 2 4) :=
  ⟨fun a b => Subtype.ext
    ((eq_zero_of_mem_filtration_two (pairAnchorAffine p1) 4 a.1 a.2).trans
      (eq_zero_of_mem_filtration_two (pairAnchorAffine p1) 4 b.1 b.2).symm)⟩


-- @@ L528-533 verbatim
/-- Drift guard: the subject of the calibration is wave 1's literal landed
self-pairing of the point-divisor datum, by `rfl`. -/
theorem dinfPairedInto_receipt :
    dinfPairedInto =
      pairedClassInto (cRingHom structMor) dinfPairData dinfSecondSlot :=
  rfl


-- @@ L535-541 verbatim
/-- **The degree-4 self-pairing value of the point divisor on `ℙ¹` is zero
(underlying class)**: the underlying degree-4 hypercohomology class of
`dinfPairedInto` is `0`. -/
theorem dinfPairedInto_coe_eq_zero :
    (dinfPairedInto : affineZHyperH p1 (pairAnchorAffine p1)
      (reindexZ (deRhamSheafZComplexN (cRingHom structMor))) 4) = 0 :=
  eq_zero_of_mem_filtration_two (pairAnchorAffine p1) 4 _ dinfPairedInto_mem


-- @@ L543-549 verbatim
/-- **The calibration headline**: the degree-4 self-pairing value of the
point divisor on `ℙ¹` is zero, because the constructed degree-4 carrier is
trivial (`subsingleton_F2H4`). -/
theorem dinfPairedInto_eq_zero : dinfPairedInto = 0 := by
  apply Subtype.ext
  rw [ZeroMemClass.coe_zero]
  exact dinfPairedInto_coe_eq_zero


-- @@ L551-551 verbatim
end ConstantsReceipt



-- @@ L554-554 verbatim
end CalibrationDegreeFour


-- @@ L556-556 verbatim
end HodgePilot


-- @@ L558-558 verbatim
end
