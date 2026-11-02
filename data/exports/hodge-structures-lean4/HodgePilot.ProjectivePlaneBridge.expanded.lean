import HodgePilot.ProjectivePlaneChart
import HodgePilot.CyclePairing
import HodgePilot.CalibrationDegreeFour
import HodgePilot.ProjectivePlane


-- @@ L6-41 verbatim
/-! # Projective-plane truncation bridge (`HodgePilot.ProjectivePlaneBridge`)

The relaxed re-key of `HodgePilot.CalibrationDegreeFour` §4–5 plus the degree-2
concentration: the brutal truncation `σ≥2` of the reindexed de Rham complex of
`ℙ²` is CONCENTRATED in degree 2 (not zero — the honest P2 relaxation), and its
degree-4 hypercohomology against the pairing anchor reduces to a degree-2 `Ext`
against the anchor — the constructed `H²(Ω²)` carrier IN THE PAIRING'S OWN
carrier category.

Structure:
* Part 0 (generic): the degree-2 single-complex `Ext → ℍ⁴` bridge, the degree-2
  sibling of `ProjectiveLineDetection.singleOne*`, consuming
  `CyclePairing.chernShapeTwo`/`singleShiftedHomTwo`.
* Part 1 (generic): the degree-2 concentration iso.
* Part 2 (ℙ²): the bridge assembly, parametrized on the degree-`≥3` sheaf
  vanishing `hZ`.
* Part 3 (ℙ²): the degree-`≥3` vanishing itself (`isZero_deRhamSheafZ_P2`) — the
  `CalibrationDegreeFour` §4 three-chart propagation of the chart seed
  `ProjectivePlaneChart.subsingleton_DR_chart`, discharging `hZ`.
* Part 4 (ℙ²): the discharged bridge (`planeBridgeP2`), the reduced image of a
  paired truncated class (`pairedIntoReduced`), and drift receipts pinning
  `ProjectivePlane.linesPairedInto` to the wave's objects.

## Claim discipline

Constructed carriers throughout; the filtration is the naive
(brutal-truncation) one.  **NO nonvanishing of `H²(Ω²)` is produced or
approached, NO paired-class identification, NO comparison, NO canonicity, and
nothing here is claimed to make the Hodge conjecture statable.**  The reduced
object is a degree-2 `Ext` against the pairing anchor — neither triviality nor
nontriviality is asserted of it (contrast: the projective line's
`CalibrationDegreeFour.subsingleton_affineZHyperH_trunc` proved `F² = 0`; here
`F²` merely *reduces*).  The FULL-carrier `F²H⁴` statement stays OUT of scope
(parked on upstream affine vanishing).  Nothing here is a novelty claim beyond
what `NOVELTIES.md` logs.
-/


-- @@ L43-43 verbatim
open CategoryTheory CategoryTheory.Limits


-- @@ L45-45 verbatim
noncomputable section


-- @@ L47-47 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L49-49 verbatim
namespace HodgePilot

-- @@ L50-50 verbatim
namespace ProjectivePlaneBridge


-- @@ L52-52 verbatim
/-! ## Part 0. Generic: the degree-2 single-complex `Ext → ℍ⁴` bridge -/


-- @@ L54-54 verbatim
section GenericSingleTwo


-- @@ L56-56 verbatim
open HodgePilot.Hyper HodgePilot.DLog HodgePilot.CyclePairing


-- @@ L58-58 verbatim
universe w' w v u

-- @@ L59-59 verbatim
variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]


-- @@ L61-64 verbatim
/-- B2.5: `singleShiftedHomTwo M` is an isomorphism. -/
theorem isIso_singleShiftedHomTwo (M : C) : IsIso (singleShiftedHomTwo M) :=
  inferInstanceAs (IsIso
    (((DerivedCategory.singleFunctors C).shiftIso 2 0 2 (by lia)).symm.hom.app M))


-- @@ L66-66 verbatim
variable [HasExt.{w'} C]


-- @@ L68-71 verbatim
/-- The degree-2 bridge, forward. -/
def singleTwoToHyper (Z M : C) :
    Abelian.Ext Z M 2 →+ hyperH Z ((CochainComplex.singleFunctor C 2).obj M) 4 :=
  chernShapeTwo Z M _ (𝟙 ((CochainComplex.singleFunctor C 2).obj M))


-- @@ L73-79 verbatim
theorem singleTwoToHyper_apply (Z M : C) (x : Abelian.Ext Z M 2) :
    singleTwoToHyper Z M x = x.hom.comp (singleShiftedHomTwo M) (by lia) := by
  rw [show singleTwoToHyper Z M x =
      chernShapeTwo Z M _ (𝟙 ((CochainComplex.singleFunctor C 2).obj M)) x from rfl,
    chernShapeTwo_apply]
  exact congrArg (fun t => x.hom.comp t (by lia))
    (hyperHMap_id M ((CochainComplex.singleFunctor C 2).obj M) 2 (singleShiftedHomTwo M))


-- @@ L81-139 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- **B2.6 (the wave go/no-go — probe-verified GREEN)**: the degree-2 bridge is
bijective. -/
theorem singleTwoToHyper_bijective (Z M : C) :
    Function.Bijective (singleTwoToHyper Z M) := by
  haveI hIso : IsIso (singleShiftedHomTwo M) := isIso_singleShiftedHomTwo M
  haveI : IsIso ((shiftFunctor (DerivedCategory C) ((2 : ℕ) : ℤ)).map (singleShiftedHomTwo M) ≫
      (shiftFunctorAdd' (DerivedCategory C) (2 : ℤ) ((2 : ℕ) : ℤ) (4 : ℤ)
        (by lia)).inv.app _) :=
    inferInstance
  have hcomp : ∀ x : Abelian.Ext Z M 2,
      singleTwoToHyper Z M x =
        Abelian.Ext.homAddEquiv x ≫
          ((shiftFunctor (DerivedCategory C) ((2 : ℕ) : ℤ)).map (singleShiftedHomTwo M) ≫
            (shiftFunctorAdd' (DerivedCategory C) (2 : ℤ) ((2 : ℕ) : ℤ) (4 : ℤ)
              (by lia)).inv.app _) := by
    intro x
    rw [singleTwoToHyper_apply]
    rfl
  have hpost : Function.Bijective
      (fun (y : ShiftedHom ((DerivedCategory.singleFunctor C 0).obj Z)
          ((DerivedCategory.singleFunctor C 0).obj M) ((2 : ℕ) : ℤ)) =>
        y ≫ ((shiftFunctor (DerivedCategory C) ((2 : ℕ) : ℤ)).map (singleShiftedHomTwo M) ≫
          (shiftFunctorAdd' (DerivedCategory C) (2 : ℤ) ((2 : ℕ) : ℤ) (4 : ℤ)
            (by lia)).inv.app _)) := by
    have hp : (2 : ℤ) + ((2 : ℕ) : ℤ) = (4 : ℤ) := by lia
    constructor
    · intro a b hab
      have hab' : a ≫ ((shiftFunctor (DerivedCategory C) ((2 : ℕ) : ℤ)).map
            (singleShiftedHomTwo M) ≫
            (shiftFunctorAdd' (DerivedCategory C) (2 : ℤ) ((2 : ℕ) : ℤ) (4 : ℤ)
              hp).inv.app _) =
          b ≫ ((shiftFunctor (DerivedCategory C) ((2 : ℕ) : ℤ)).map
            (singleShiftedHomTwo M) ≫
            (shiftFunctorAdd' (DerivedCategory C) (2 : ℤ) ((2 : ℕ) : ℤ) (4 : ℤ)
              hp).inv.app _) := hab
      rwa [cancel_mono] at hab'
    · intro z
      refine ⟨z ≫ inv ((shiftFunctor (DerivedCategory C) ((2 : ℕ) : ℤ)).map
        (singleShiftedHomTwo M) ≫
        (shiftFunctorAdd' (DerivedCategory C) (2 : ℤ) ((2 : ℕ) : ℤ) (4 : ℤ)
          hp).inv.app _), ?_⟩
      show (z ≫ inv ((shiftFunctor (DerivedCategory C) ((2 : ℕ) : ℤ)).map
          (singleShiftedHomTwo M) ≫
          (shiftFunctorAdd' (DerivedCategory C) (2 : ℤ) ((2 : ℕ) : ℤ) (4 : ℤ)
            hp).inv.app _)) ≫
          ((shiftFunctor (DerivedCategory C) ((2 : ℕ) : ℤ)).map (singleShiftedHomTwo M) ≫
          (shiftFunctorAdd' (DerivedCategory C) (2 : ℤ) ((2 : ℕ) : ℤ) (4 : ℤ)
            hp).inv.app _) = z
      rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  have hfun : ⇑(singleTwoToHyper Z M) =
      (fun (y : ShiftedHom ((DerivedCategory.singleFunctor C 0).obj Z)
          ((DerivedCategory.singleFunctor C 0).obj M) ((2 : ℕ) : ℤ)) =>
        y ≫ ((shiftFunctor (DerivedCategory C) ((2 : ℕ) : ℤ)).map (singleShiftedHomTwo M) ≫
          (shiftFunctorAdd' (DerivedCategory C) (2 : ℤ) ((2 : ℕ) : ℤ) (4 : ℤ)
            (by lia)).inv.app _)) ∘ ⇑(Abelian.Ext.homAddEquiv) :=
    funext hcomp
  rw [hfun]
  exact hpost.comp (AddEquiv.bijective _)


-- @@ L141-144 verbatim
/-- **B2.7**: the degree-2 additive equivalence `Ext Z M 2 ≃+ ℍ⁴(Z, M[at 2])`. -/
def singleTwoHyperEquiv (Z M : C) :
    Abelian.Ext Z M 2 ≃+ hyperH Z ((CochainComplex.singleFunctor C 2).obj M) 4 :=
  AddEquiv.ofBijective (singleTwoToHyper Z M) (singleTwoToHyper_bijective Z M)


-- @@ L146-147 verbatim
theorem singleTwoHyperEquiv_apply (Z M : C) (x : Abelian.Ext Z M 2) :
    singleTwoHyperEquiv Z M x = singleTwoToHyper Z M x := rfl


-- @@ L149-149 verbatim
end GenericSingleTwo


-- @@ L151-151 verbatim
/-! ## Part 1. Generic: the degree-2 concentration iso (B2.4) -/


-- @@ L153-153 verbatim
section GenericConcentration


-- @@ L155-155 verbatim
open HodgePilot.Hyper


-- @@ L157-157 verbatim
universe w v u

-- @@ L158-158 verbatim
variable {C : Type u} [Category.{v} C] [Abelian C]

-- @@ L159-159 verbatim
variable (K : CochainComplex C ℕ)


-- @@ L161-163 verbatim
/-- The degree-2 term of `σ≥2 (reindexZ K)` is `K.X 2`. -/
def truncTwoXTwoIso : (brutalTruncGE (reindexZ K) 2).X 2 ≅ K.X 2 :=
  (brutalTruncGEXIso (reindexZ K) 2 2 le_rfl) ≪≫ reindexZXIso K 2


-- @@ L165-176 verbatim
/-- Degreewise comparison: canonical in degree 2, zero-object elsewhere. -/
def truncSingleXIso
    (hz : ∀ n : ℤ, n ≠ 2 → IsZero ((brutalTruncGE (reindexZ K) 2).X n)) (n : ℤ) :
    (brutalTruncGE (reindexZ K) 2).X n ≅
      (((CochainComplex.singleFunctor C 2).obj (K.X 2)).X n) :=
  if h : n = 2 then
    eqToIso (congrArg (brutalTruncGE (reindexZ K) 2).X h) ≪≫
      truncTwoXTwoIso K ≪≫
      (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) 2 (K.X 2) n h).symm
  else
    (hz n h).iso
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 2 (K.X 2) n h)


-- @@ L178-191 verbatim
/-- **B2.4**: the truncation `σ≥2 (reindexZ K)` is CONCENTRATED in degree 2 —
isomorphic, as a complex, to the single complex of `K.X 2` (not zero: the honest
P2 relaxation of `CalibrationDegreeFour.isZero_trunc_complex`). -/
def truncTwoIso
    (hz : ∀ n : ℤ, n ≠ 2 → IsZero ((brutalTruncGE (reindexZ K) 2).X n)) :
    brutalTruncGE (reindexZ K) 2 ≅ (CochainComplex.singleFunctor C 2).obj (K.X 2) :=
  HomologicalComplex.Hom.isoOfComponents (truncSingleXIso K hz) (fun i j hij => by
    by_cases hj : j = (2 : ℤ)
    · have hij' : i + 1 = j := hij
      have hi : i ≠ 2 := by
        intro h1; rw [h1, hj] at hij'; exact absurd hij' (by norm_num)
      exact (hz i hi).eq_of_src _ _
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 2
        (K.X 2) j hj).eq_of_tgt _ _)


-- @@ L193-193 verbatim
end GenericConcentration


-- @@ L195-198 verbatim
/-! ## Part 2. ℙ²: the truncation bridge (B2.3, B2.8, B2.10)

Given the degree-`≥3` sheaf vanishing `hZ`, the degree-4 hypercohomology of `ℙ²`
against the pairing anchor reduces to a degree-2 `Ext` against the anchor. -/


-- @@ L200-200 verbatim
section PlaneBridge


-- @@ L202-202 verbatim
open AlgebraicGeometry

-- @@ L203-203 verbatim
open HodgePilot.Hyper HodgePilot.CyclePairing HodgePilot.DeRhamWedgeChain

-- @@ L204-204 verbatim
open HodgePilot.ProjectivePlane HodgePilot.DeRhamPresheaf


-- @@ L206-207 verbatim
/-- The plane structure ring hom. -/
abbrev φP2 := cRingHom structMor


-- @@ L209-230 verbatim
/-- B2.3: away from degree 2, the truncation `σ≥2` of the reindexed de Rham
complex of `ℙ²` is a zero object (degrees `<2` truncated, degrees `≥3` die by
`hZ`).  Re-key of `ProjectiveLineDetection.isZero_truncOne_X`, one degree up. -/
theorem isZero_truncTwo_X
    (hZ : ∀ m : ℕ, 3 ≤ m → IsZero (deRhamSheafZ φP2 m))
    (n : ℤ) (hn : n ≠ 2) :
    IsZero ((brutalTruncGE (reindexZ (deRhamSheafZComplexN φP2)) 2).X n) := by
  by_cases hlt : n < 2
  · exact isZero_brutalTruncGE_X _ 2 n hlt
  · rw [not_lt] at hlt
    have h3 : 3 ≤ n := by
      rcases lt_or_eq_of_le hlt with h | h
      · lia
      · exact absurd h.symm hn
    obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m : ℤ) :=
      ⟨n.toNat, (Int.toNat_of_nonneg (by lia)).symm⟩
    have hm : 3 ≤ m := by exact_mod_cast h3
    have h2m : (2 : ℕ) ≤ m := by omega
    exact (hZ m hm).of_iso
      ((brutalTruncGEXIso (reindexZ (deRhamSheafZComplexN φP2)) 2 (m : ℤ)
          (by exact_mod_cast h2m)) ≪≫
        reindexZXIso (deRhamSheafZComplexN φP2) m)


-- @@ L232-237 verbatim
/-- The concentration iso for `ℙ²`, at the reindexed de Rham complex. -/
def truncTwoIsoP2
    (hZ : ∀ m : ℕ, 3 ≤ m → IsZero (deRhamSheafZ φP2 m)) :
    brutalTruncGE (reindexZ (deRhamSheafZComplexN φP2)) 2 ≅
      (CochainComplex.singleFunctor _ 2).obj (deRhamSheafZ φP2 2) :=
  truncTwoIso (deRhamSheafZComplexN φP2) (fun n hn => isZero_truncTwo_X hZ n hn)


-- @@ L239-253 verbatim
/-- **B2.8 (the B2 headline)**: the degree-4 hypercohomology of `ℙ²` against the
pairing anchor reduces to `Ext(anchor, Ω²-sheaf, 2)` — the constructed `H²(Ω²)`
carrier IN THE PAIRING'S OWN CARRIER CATEGORY and against the pairing anchor.
Not claimed nonzero; no comparison, no canonicity; the naive (brutal) filtration
throughout.  `truncationBridgeP2 (linesPairedInto ...)` is the honest reduced
image of the paired class; nonvanishing stays a separately-priced rung. -/
def truncationBridgeP2
    (hZ : ∀ m : ℕ, 3 ≤ m → IsZero (deRhamSheafZ φP2 m)) :
    affineZHyperH p2 (pairAnchorAffine p2)
        (brutalTruncGE (reindexZ (deRhamSheafZComplexN φP2)) 2) 4 ≃+
      Abelian.Ext (pairAnchorAffine p2) (deRhamSheafZ φP2 2) 2 :=
  letI := HasDerivedCategory.standard
    (Sheaf (Scheme.AffineZariskiSite.grothendieckTopology p2) (ModuleCat.{0} ℤ))
  (DeRhamSpaceAgree.hyperHCongr (Iso.refl (pairAnchorAffine p2)) (truncTwoIsoP2 hZ) 4).trans
    (singleTwoHyperEquiv (pairAnchorAffine p2) (deRhamSheafZ φP2 2)).symm


-- @@ L255-263 verbatim
/-- **B2.10 (honest-ceiling receipt)**: the reduced object is exactly a degree-2
`Ext` against the pairing anchor — NO triviality and NO nontriviality asserted
(contrast: P1's `subsingleton_affineZHyperH_trunc` proved `F²=0`; here `F²`
merely *reduces*).  A `rfl` drift-guard pinning the reduced target. -/
theorem truncationBridgeP2_target
    (_hZ : ∀ m : ℕ, 3 ≤ m → IsZero (deRhamSheafZ φP2 m)) :
    (Abelian.Ext (pairAnchorAffine p2) (deRhamSheafZ φP2 2) 2) =
      (Abelian.Ext (pairAnchorAffine p2)
        ((deRhamSheafZComplexN φP2).X 2) 2) := rfl


-- @@ L265-265 verbatim
end PlaneBridge


-- @@ L267-273 verbatim
/-! ## Part 3. ℙ²: the degree-`≥3` de Rham sheaf vanishing (B2.1–B2.2)

The `CalibrationDegreeFour` §4 three-chart propagation, one threshold up
(`2 → 3`), of the chart seed `ProjectivePlaneChart.subsingleton_DR_chart`: the
degree-`≥3` de Rham terms vanish over every chart, hence (by the shipped
localization transfer and the three-chart cover) over every affine open, hence
the degree-`≥3` de Rham sheaves are zero — discharging `hZ`. -/


-- @@ L275-275 verbatim
section PlaneResidue


-- @@ L277-277 verbatim
open AlgebraicGeometry HomogeneousLocalization TopologicalSpace Opposite

-- @@ L278-278 verbatim
open HodgePilot.DeRham HodgePilot.DeRhamPresheaf HodgePilot.DeRhamSheaf

-- @@ L279-279 verbatim
open HodgePilot.DeRhamWedgeChain

-- @@ L280-280 verbatim
open HodgePilot.ProjectivePlane HodgePilot.ProjectivePlaneChart


-- @@ L282-282 verbatim
local notation "𝒜₃" => MvPolynomial.homogeneousSubmodule (Fin 3) ℂ


-- @@ L284-289 verbatim
/-- Transport of the vanishing along an equality of opens. -/
theorem subsingleton_DR_congr {V W : p2.Opens} (h : V = W) {p : ℕ}
    (hV : Subsingleton (DeRham.DR ℂ (Sec (cRingHom structMor) V) p)) :
    Subsingleton (DeRham.DR ℂ (Sec (cRingHom structMor) W) p) := by
  subst h
  exact hV


-- @@ L291-303 verbatim
/-- **Propagation to basic opens** (the shipped `DeRhamSheaf` localization
transfer): if the de Rham term vanishes over an affine `U`, it vanishes over
every basic open `D(f) ⊆ U`. -/
theorem subsingleton_DR_basicOpen (U : p2.AffineZariskiSite) {p : ℕ}
    (hU : Subsingleton (DeRham.DR ℂ (Sec (cRingHom structMor) U.toOpens) p))
    (f : Sec (cRingHom structMor) U.toOpens) :
    Subsingleton (DeRham.DR ℂ
      (Sec (cRingHom structMor) (p2.basicOpen f)) p) := by
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨z, k, hzk⟩ :=
    DeRhamSheaf.exists_res_map_eq_pow_smul (cRingHom structMor) U f p y
  rw [Subsingleton.elim z 0, map_zero] at hzk
  exact DeRhamSheaf.eq_zero_of_res_pow_smul_eq_zero (cRingHom structMor) U f p k hzk


-- @@ L305-312 verbatim
/-- The chart seed, indexed by a single chart: the degree-`≥3` de Rham term of
chart `i` vanishes (the other two indices supplied by `Fin 3` case split). -/
theorem subsingleton_DR_chart_i (i : Fin 3) {p : ℕ} (hp : 3 ≤ p) :
    Subsingleton (DeRham.DR ℂ (Sec (cRingHom structMor) (chartOpen i)) p) :=
  match i with
  | 0 => subsingleton_DR_chart 0 1 2 (by decide) (by decide) (by decide) hp
  | 1 => subsingleton_DR_chart 1 0 2 (by decide) (by decide) (by decide) hp
  | 2 => subsingleton_DR_chart 2 0 1 (by decide) (by decide) (by decide) hp


-- @@ L314-317 verbatim
/-- The chart, as an object of the small affine Zariski site. -/
def chartAffine (i : Fin 3) : p2.AffineZariskiSite :=
  ⟨chartOpen i,
    Proj.isAffineOpen_basicOpen 𝒜₃ (MvPolynomial.X i) (X_mem_grade_one i) one_pos⟩


-- @@ L319-343 verbatim
/-- Through a point of an affine open `U` lying in the chart `i`, there is a
basic open of `U` with vanishing de Rham term (two applications of
`IsAffineOpen.exists_basicOpen_le`, through a chart-basic middle open). -/
theorem exists_basicOpen_subsingleton (U : p2.AffineZariskiSite) {p : ℕ}
    (hp : 3 ≤ p) {x : p2} (hxU : x ∈ U.toOpens) (i : Fin 3)
    (hxi : x ∈ chartOpen i) :
    ∃ f : Sec (cRingHom structMor) U.toOpens,
      Subsingleton (DeRham.DR ℂ
        (Sec (cRingHom structMor) (p2.basicOpen f)) p) ∧
        x ∈ p2.basicOpen f := by
  obtain ⟨g, hgU, hxg⟩ :=
    (chartAffine i).2.exists_basicOpen_le (⟨x, hxU⟩ : U.toOpens) hxi
  have hWg : Subsingleton (DeRham.DR ℂ
      (Sec (cRingHom structMor) (p2.basicOpen g)) p) :=
    subsingleton_DR_basicOpen (chartAffine i)
      (subsingleton_DR_chart_i i hp) g
  obtain ⟨f, hf_le, hxf⟩ :=
    U.2.exists_basicOpen_le (⟨x, hxg⟩ : (p2.basicOpen g : p2.Opens)) hxU
  refine ⟨f, ?_, hxf⟩
  have hb : p2.basicOpen (res (cRingHom structMor) hgU f) = p2.basicOpen f := by
    rw [res_apply, Scheme.basicOpen_res]
    exact inf_eq_right.mpr hf_le
  exact subsingleton_DR_congr hb
    (subsingleton_DR_basicOpen ⟨p2.basicOpen g, (chartAffine i).2.basicOpen g⟩
      hWg (res (cRingHom structMor) hgU f))


-- @@ L345-374 verbatim
/-- **The de Rham terms of degree `≥ 3` vanish over every affine open of `ℙ²`**:
the three charts cover, each point of an affine open has a chart-subordinated
basic open with vanishing term, such basic opens span, and the shipped
separatedness `DeRhamSheaf.eq_of_res_map_eq_of_span` pulls the vanishing up. -/
theorem subsingleton_DR_all (U : p2.AffineZariskiSite) {p : ℕ} (hp : 3 ≤ p) :
    Subsingleton (DeRham.DR ℂ (Sec (cRingHom structMor) U.toOpens) p) := by
  classical
  set s : Set (Sec (cRingHom structMor) U.toOpens) :=
    {f | Subsingleton (DeRham.DR ℂ
      (Sec (cRingHom structMor) (p2.basicOpen f)) p)} with hs
  have hcov : (⨆ f : s, p2.basicOpen (f.1 : Γ(p2, U.toOpens))) = U.toOpens := by
    refine le_antisymm (iSup_le fun f => p2.basicOpen_le f.1) fun x hx => ?_
    have hx2 : x ∈ chart 0 ⊔ chart 1 ⊔ chart 2 := by
      rw [chart_cover_receipt]; trivial
    have hchart : ∃ i : Fin 3, x ∈ chartOpen i := by
      rcases (Opens.mem_sup).mp hx2 with h01 | h2
      · rcases (Opens.mem_sup).mp h01 with h0 | h1
        · exact ⟨0, h0⟩
        · exact ⟨1, h1⟩
      · exact ⟨2, h2⟩
    obtain ⟨i, hxi⟩ := hchart
    obtain ⟨f, hf, hxf⟩ := exists_basicOpen_subsingleton U hp hx i hxi
    exact Opens.mem_iSup.mpr ⟨⟨f, hf⟩, hxf⟩
  have hspan : Ideal.span s = ⊤ := U.2.iSup_basicOpen_eq_self_iff.mp hcov
  refine subsingleton_of_forall_eq 0 fun z => ?_
  refine DeRhamSheaf.eq_of_res_map_eq_of_span (cRingHom structMor) U hspan p
    (fun f hf => ?_)
  haveI : Subsingleton (DeRham.DR ℂ
      (Sec (cRingHom structMor) (p2.basicOpen f)) p) := hf
  exact Subsingleton.elim _ _


-- @@ L376-387 verbatim
/-- **B2.1–B2.2 (the discharged `hZ`, implicit-degree form)**: the degree-`≥3`
de Rham sheaves of `ℙ²` are zero objects of the category of `ℤ`-module sheaves
on the small affine Zariski site. -/
theorem isZero_deRhamSheafZ_P2 {m : ℕ} (hm : 3 ≤ m) :
    IsZero (deRhamSheafZ (cRingHom structMor) m) := by
  rw [IsZero.iff_id_eq_zero]
  apply Sheaf.hom_ext
  refine NatTrans.ext (funext fun U => ?_)
  haveI : Subsingleton
      ((deRhamSheafZ (cRingHom structMor) m).obj.obj U) :=
    subsingleton_DR_all U.unop hm
  exact ModuleCat.hom_ext (LinearMap.ext fun x => Subsingleton.elim _ _)


-- @@ L389-389 verbatim
end PlaneResidue


-- @@ L391-391 verbatim
/-! ## Part 4. ℙ²: the discharged bridge and the paired-class receipts -/


-- @@ L393-393 verbatim
section PlaneDischarge


-- @@ L395-395 verbatim
open AlgebraicGeometry

-- @@ L396-396 verbatim
open HodgePilot.Hyper HodgePilot.CyclePairing HodgePilot.CycCarrier

-- @@ L397-397 verbatim
open HodgePilot.DeRhamWedgeChain

-- @@ L398-398 verbatim
open HodgePilot.ProjectivePlane HodgePilot.DeRhamPresheaf


-- @@ L400-403 verbatim
/-- **B2.1–B2.2 (the `hZ` input, explicit-degree form)**: the wave's degree-`≥3`
vanishing, packaged as the hypothesis the parametrized bridge consumes. -/
theorem hZP2 : ∀ m : ℕ, 3 ≤ m → IsZero (deRhamSheafZ φP2 m) :=
  fun _ hm => isZero_deRhamSheafZ_P2 hm


-- @@ L405-413 verbatim
/-- **The discharged degree-2 truncation bridge**: `truncationBridgeP2` with `hZ`
supplied by the chart seed — the `hZ`-free headline.  Reduces the degree-4
hypercohomology of `ℙ²` against the pairing anchor to `Ext(anchor, Ω²-sheaf, 2)`.
NOT claimed nonzero; no comparison, no canonicity; naive filtration. -/
def planeBridgeP2 :
    affineZHyperH p2 (pairAnchorAffine p2)
        (brutalTruncGE (reindexZ (deRhamSheafZComplexN φP2)) 2) 4 ≃+
      Abelian.Ext (pairAnchorAffine p2) (deRhamSheafZ φP2 2) 2 :=
  truncationBridgeP2 hZP2


-- @@ L415-423 verbatim
/-- **B2.9 (rfl-adjacent key identity)**: the degree-2 reduced `Ext` image of a
paired truncated class.  The domain of `planeBridgeP2` is definitionally the
codomain of `CyclePairing.pairedIntoTrunc`, so the bridge sends any paired
truncated class to its reduced `Ext` image against the pairing anchor.  NOT
claimed nonzero; the reduction asserts neither triviality nor nontriviality. -/
def pairedIntoReduced (x : pairAnchor p2 ⟶ divisorsMod p2)
    (e₂ : Abelian.Ext (pairAnchor p2) (unitsMod p2) 1) :
    Abelian.Ext (pairAnchorAffine p2) (deRhamSheafZ φP2 2) 2 :=
  planeBridgeP2 (pairedIntoTrunc φP2 x e₂)


-- @@ L425-427 verbatim
theorem pairedIntoReduced_eq (x : pairAnchor p2 ⟶ divisorsMod p2)
    (e₂ : Abelian.Ext (pairAnchor p2) (unitsMod p2) 1) :
    pairedIntoReduced x e₂ = planeBridgeP2 (pairedIntoTrunc φP2 x e₂) := rfl


-- @@ L429-440 verbatim
/-- **Drift-guard receipt pinning `ProjectivePlane.linesPairedInto` to the
wave's objects**: the underlying degree-4 hypercohomology class of the
constructed two-line paired class is the truncation-inclusion of exactly the
paired truncated class `pairedIntoTrunc φP2 linesPairData linesSecondSlot` that
`planeBridgeP2` consumes.  Definitional; asserts nothing about the class. -/
theorem linesPairedInto_truncPrecursor :
    (linesPairedInto : affineZHyperH p2 (pairAnchorAffine p2)
        (reindexZ (deRhamSheafZComplexN φP2)) 4) =
      affineZHyperHMap p2 (pairAnchorAffine p2)
        (ιBrutalTruncGE (reindexZ (deRhamSheafZComplexN φP2)) 2) 4
        (pairedIntoTrunc φP2 linesPairData linesSecondSlot) :=
  rfl


-- @@ L442-445 verbatim
/-- **Drift-guard receipt**: the wave's `φP2` is `ProjectivePlane`'s structure
ring hom, so `planeBridgeP2`/`pairedIntoReduced` act on exactly the object
family `linesPairedInto` inhabits. -/
theorem φP2_receipt : φP2 = cRingHom structMor := rfl


-- @@ L447-447 verbatim
end PlaneDischarge


-- @@ L449-449 verbatim
end ProjectivePlaneBridge

-- @@ L450-450 verbatim
end HodgePilot

-- @@ L451-451 verbatim
end
