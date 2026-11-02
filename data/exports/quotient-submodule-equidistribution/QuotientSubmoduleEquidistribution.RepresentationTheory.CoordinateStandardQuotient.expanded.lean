import QuotientSubmoduleEquidistribution.RepresentationTheory.CoordinateSimpleCovers
import QuotientSubmoduleEquidistribution.RepresentationTheory.MaximalFlagStrongHeredity


-- @@ L4-10 verbatim
/-!
# Coordinate standard quotients along a maximal flag

Scratch formalization of the concrete CPS quotient at one deletion step.
The removed coordinate projective is divided by the trace of all coordinate
projectives which survive to the next support.
-/


-- @@ L12-12 verbatim
noncomputable section


-- @@ L14-14 verbatim
open CategoryTheory CategoryTheory.Limits


-- @@ L16-16 verbatim
namespace QuotientSubmoduleEquidistribution.AuslanderEquivalence.CoordinateIdempotent


-- @@ L18-18 verbatim
open QuotientSubmoduleEquidistribution.IndecomposableSkeleton

-- @@ L19-19 verbatim
open QuotientSubmoduleEquidistribution.Tsukamoto.StandardSemantics


-- @@ L21-21 verbatim
universe uR uκ wR


-- @@ L23-26 verbatim
variable {R : Type uR} [Ring R] [IsNoetherianRing R]
  {κ : Type uκ}
  (σ : IndecomposableSkeleton.{uR, uκ, wR} R κ)
  [Finite κ]


-- @@ L28-28 verbatim
local notation "Γ" => skeletonAuslanderAlgebra σ


-- @@ L30-54 verbatim
/-- Vanishing of maps from a fixed object to every permitted layer is
preserved by a finite filtration by those layers. -/
theorem hom_eq_zero_of_isFilteredBy
    {ι : Type*}
    (layer : ι → ModuleCat.{wR} Γᵐᵒᵖ)
    (allowed : ι → Prop)
    (P : ModuleCat.{wR} Γᵐᵒᵖ)
    (hLayer : ∀ (j : ι), allowed j →
      ∀ f : P ⟶ layer j, f = 0)
    {X : ModuleCat.{wR} Γᵐᵒᵖ}
    (hX : IsFilteredBy layer allowed X) :
    ∀ f : P ⟶ X, f = 0 := by
  induction hX with
  | zero X hzero =>
      intro f
      exact hzero.eq_of_tgt f 0
  | extension j hj f g zero exact tail ih =>
      intro q
      letI : Mono f := exact.mono_f
      have hqg : q ≫ g = 0 := ih (q ≫ g)
      let l := exact.exact.lift q hqg
      calc
        q = l ≫ f := (exact.exact.lift_f q hqg).symm
        _ = 0 ≫ f := congrArg (fun t ↦ t ≫ f) (hLayer j hj l)
        _ = 0 := zero_comp


-- @@ L56-63 verbatim
/-- The trace in the coordinate projective `P(i)` of all singleton
coordinate projectives with labels in `T`. -/
def coordinateProjectiveTrace (T : Set κ) (i : κ) :
    Submodule Γᵐᵒᵖ (coordinateProjective σ i).obj :=
  ⨆ (j : κ) (_ : j ∈ T)
    (f : (coordinateProjective σ j).obj ⟶
      (coordinateProjective σ i).obj),
    LinearMap.range f.hom


-- @@ L65-72 verbatim
/-- Every map from a selected coordinate projective has range in the
coordinate trace. -/
theorem range_le_coordinateProjectiveTrace
    (T : Set κ) (i j : κ) (hj : j ∈ T)
    (f : (coordinateProjective σ j).obj ⟶
      (coordinateProjective σ i).obj) :
    LinearMap.range f.hom ≤ coordinateProjectiveTrace σ T i :=
  le_iSup_of_le j <| le_iSup_of_le hj <| le_iSup_of_le f le_rfl


-- @@ L74-80 verbatim
/-- The concrete standard candidate: `P(i)` modulo the trace of the
selected later coordinate projectives. -/
abbrev coordinateStandardQuotient (T : Set κ) (i : κ) :
    ModuleCat.{wR} Γᵐᵒᵖ :=
  ModuleCat.of Γᵐᵒᵖ
    ((coordinateProjective σ i).obj ⧸
      coordinateProjectiveTrace σ T i)


-- @@ L82-86 verbatim
/-- The quotient projection onto the coordinate standard candidate. -/
def coordinateStandardProjection (T : Set κ) (i : κ) :
    (coordinateProjective σ i).obj ⟶
      coordinateStandardQuotient σ T i :=
  ModuleCat.ofHom (Submodule.mkQ (coordinateProjectiveTrace σ T i))


-- @@ L88-91 verbatim
instance coordinateStandardProjection_epi (T : Set κ) (i : κ) :
    Epi (coordinateStandardProjection σ T i) := by
  rw [ModuleCat.epi_iff_surjective]
  exact Submodule.Quotient.mk_surjective _


-- @@ L93-106 verbatim
/-- Every map from a selected later coordinate projective is killed by
the coordinate standard projection. -/
theorem comp_coordinateStandardProjection_eq_zero
    (T : Set κ) (i j : κ) (hj : j ∈ T)
    (f : (coordinateProjective σ j).obj ⟶
      (coordinateProjective σ i).obj) :
    f ≫ coordinateStandardProjection σ T i = 0 := by
  apply ModuleCat.hom_ext
  ext x
  apply (Submodule.Quotient.mk_eq_zero
    (coordinateProjectiveTrace σ T i)).mpr
  exact
    range_le_coordinateProjectiveTrace σ T i j hj f
      ⟨x, rfl⟩


-- @@ L108-128 verbatim
/-- A map out of `P(i)` which kills all maps from the selected coordinate
projectives kills their whole trace. -/
theorem coordinateProjectiveTrace_le_ker
    (T : Set κ) (i : κ)
    {Q : ModuleCat.{wR} Γᵐᵒᵖ}
    (q : (coordinateProjective σ i).obj ⟶ Q)
    (hq : ∀ (j : κ), j ∈ T →
      ∀ f : (coordinateProjective σ j).obj ⟶
        (coordinateProjective σ i).obj,
        f ≫ q = 0) :
    coordinateProjectiveTrace σ T i ≤ LinearMap.ker q.hom := by
  apply iSup_le
  intro j
  apply iSup_le
  intro hj
  apply iSup_le
  intro f
  rw [LinearMap.range_le_ker_iff]
  have h := congrArg (fun g :
      (coordinateProjective σ j).obj ⟶ Q ↦ g.hom) (hq j hj f)
  simpa using h


-- @@ L130-142 verbatim
/-- The factor map supplied by the coordinate standard quotient. -/
def coordinateStandardDesc
    (T : Set κ) (i : κ)
    {Q : ModuleCat.{wR} Γᵐᵒᵖ}
    (q : (coordinateProjective σ i).obj ⟶ Q)
    (hq : ∀ (j : κ), j ∈ T →
      ∀ f : (coordinateProjective σ j).obj ⟶
        (coordinateProjective σ i).obj,
        f ≫ q = 0) :
    coordinateStandardQuotient σ T i ⟶ Q :=
  ModuleCat.ofHom <|
    Submodule.liftQ (coordinateProjectiveTrace σ T i) q.hom
      (coordinateProjectiveTrace_le_ker σ T i q hq)


-- @@ L144-158 verbatim
/-- Universal maximal-quotient property: every map from `P(i)` annihilated
by all later coordinate projectives factors through the coordinate standard
projection. -/
theorem coordinateStandardProjection_desc
    (T : Set κ) (i : κ)
    {Q : ModuleCat.{wR} Γᵐᵒᵖ}
    (q : (coordinateProjective σ i).obj ⟶ Q)
    (hq : ∀ (j : κ), j ∈ T →
      ∀ f : (coordinateProjective σ j).obj ⟶
        (coordinateProjective σ i).obj,
        f ≫ q = 0) :
    coordinateStandardProjection σ T i ≫
        coordinateStandardDesc σ T i q hq = q := by
  apply ModuleCat.hom_ext
  exact Submodule.liftQ_mkQ _ _ _


-- @@ L160-160 verbatim
/-! ## Simple-filtered maximality along a saturated deletion chain -/


-- @@ L162-176 verbatim
/-- A singleton coordinate projective has no nonzero map to a different
coordinate simple top. -/
theorem hom_coordinateSimple_eq_zero_of_ne
    (hfinite : ∀ i : κ,
      IsFiniteLength Γᵐᵒᵖ (coordinateProjective σ i).obj)
    {i j : κ} (hij : i ≠ j)
    (f : (coordinateProjective σ i).obj ⟶
      coordinateSimple σ j) :
    f = 0 := by
  by_contra hf
  let e : coordinateSimple σ j ≅ coordinateSimple σ i :=
    simpleIsoCoordinateSimpleOfNonzero σ hfinite i
      (coordinateSimple σ j)
      (coordinateSimple_isSimple σ hfinite j) f hf
  exact hij <| (coordinateSimple_eq_of_iso σ hfinite e).symm


-- @@ L178-178 verbatim
section SaturatedDeletion


-- @@ L180-183 verbatim
variable [Fintype κ]

/- Once a label has been removed, it does not occur in any support at
or below the next step. -/

-- @@ L184-199 verbatim
omit [Finite κ] in
theorem removed_not_mem_later_support
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    {k i : Fin (Fintype.card κ)} (hki : k ≤ i) :
    d.removed k ∉ d.support i.succ := by
  intro hmem
  have hle : k.succ ≤ i.succ :=
    Fin.succ_le_succ_iff.mpr hki
  have hsub : d.support i.succ ⊆ d.support k.succ :=
    (saturatedSupportDeletionChain_strictAnti d).antitone hle
  have hk := hsub hmem
  rw [d.step k] at hk
  exact hk.2 rfl

/- A label removed strictly later still belongs to the support immediately
after every earlier deletion. -/

-- @@ L200-211 verbatim
omit [Finite κ] in
theorem later_removed_mem_support
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    {i k : Fin (Fintype.card κ)} (hik : i < k) :
    d.removed k ∈ d.support i.succ := by
  have hle : i.succ ≤ k.castSucc :=
    Fin.succ_le_castSucc_iff.mpr hik
  exact
    (saturatedSupportDeletionChain_strictAnti d).antitone hle
      (d.removed_mem k)

/- Different deletion steps remove different labels. -/

-- @@ L212-226 verbatim
omit [Finite κ] in
theorem removed_injective
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ) :
    Function.Injective d.removed := by
  intro i k hik
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hmem := later_removed_mem_support d hlt
    have hnot := removed_not_mem_later_support d (i := i) le_rfl
    exact hnot (hik ▸ hmem)
  · have hmem := later_removed_mem_support d hgt
    have hnot := removed_not_mem_later_support d (i := k) le_rfl
    exact hnot (hik.symm ▸ hmem)

/- A saturated deletion chain removes every label exactly once. -/

-- @@ L227-232 verbatim
omit [Finite κ] in
theorem removed_bijective
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ) :
    Function.Bijective d.removed := by
  apply (Fintype.bijective_iff_injective_and_card d.removed).mpr
  exact ⟨removed_injective d, by simp⟩


-- @@ L234-249 verbatim
/-- A coordinate projective surviving after step `i` has no maps to any
coordinate simple whose label was removed at a step `k ≤ i`. -/
theorem hom_coordinateSimple_eq_zero_of_mem_later_support
    (hfinite : ∀ i : κ,
      IsFiniteLength Γᵐᵒᵖ (coordinateProjective σ i).obj)
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ))
    (j : κ) (hj : j ∈ d.support i.succ)
    (k : Fin (Fintype.card κ)) (hki : k ≤ i)
    (f : (coordinateProjective σ j).obj ⟶
      coordinateSimple σ (d.removed k)) :
    f = 0 := by
  apply hom_coordinateSimple_eq_zero_of_ne σ hfinite
  intro hjk
  subst j
  exact removed_not_mem_later_support d hki hj


-- @@ L251-269 verbatim
/-- The preceding simple-level vanishing propagates through every finite
filtration by coordinate simples removed no later than step `i`. -/
theorem hom_eq_zero_of_mem_later_support_to_filtered
    (hfinite : ∀ i : κ,
      IsFiniteLength Γᵐᵒᵖ (coordinateProjective σ i).obj)
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ))
    (j : κ) (hj : j ∈ d.support i.succ)
    {X : ModuleCat.{wR} Γᵐᵒᵖ}
    (hX : IsFilteredBy
      (fun k : Fin (Fintype.card κ) ↦
        coordinateSimple σ (d.removed k))
      (fun k ↦ k ≤ i) X) :
    ∀ f : (coordinateProjective σ j).obj ⟶ X, f = 0 := by
  apply hom_eq_zero_of_isFilteredBy σ _ _ _ _ hX
  intro k hki f
  exact
    hom_coordinateSimple_eq_zero_of_mem_later_support
      σ hfinite d i j hj k hki f


-- @@ L271-276 verbatim
/-- The concrete standard quotient attached to deletion step `i`. -/
abbrev deletionCoordinateStandardQuotient
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ)) :
    ModuleCat.{wR} Γᵐᵒᵖ :=
  coordinateStandardQuotient σ (d.support i.succ) (d.removed i)


-- @@ L278-284 verbatim
/-- Its canonical projection from the removed coordinate projective. -/
abbrev deletionCoordinateStandardProjection
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ)) :
    (coordinateProjective σ (d.removed i)).obj ⟶
      deletionCoordinateStandardQuotient σ d i :=
  coordinateStandardProjection σ (d.support i.succ) (d.removed i)


-- @@ L286-307 verbatim
/-- The concrete coordinate standard quotient is right-orthogonal to every
coordinate projective which survives to the next support. -/
theorem hom_deletionCoordinateStandardQuotient_eq_zero
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ))
    (j : κ) (hj : j ∈ d.support i.succ)
    (f : (coordinateProjective σ j).obj ⟶
      deletionCoordinateStandardQuotient σ d i) :
    f = 0 := by
  let hP := coordinateProjective_isFiniteProjective σ j
  letI : Projective (coordinateProjective σ j).obj := hP.2
  let lift : (coordinateProjective σ j).obj ⟶
      (coordinateProjective σ (d.removed i)).obj :=
    Projective.factorThru f
      (deletionCoordinateStandardProjection σ d i)
  calc
    f = lift ≫ deletionCoordinateStandardProjection σ d i :=
      (Projective.factorThru_comp f
        (deletionCoordinateStandardProjection σ d i)).symm
    _ = 0 :=
      comp_coordinateStandardProjection_eq_zero σ
        (d.support i.succ) (d.removed i) j hj lift


-- @@ L309-438 verbatim
/-- Finite length plus right orthogonality to all later coordinate
projectives produces an actual filtration by the permitted coordinate
simples.  This is the finite-length induction needed for the concrete CPS
standard quotient. -/
theorem isFilteredBy_of_finiteLength_of_hom_later_eq_zero
    (hfinite : ∀ i : κ,
      IsFiniteLength Γᵐᵒᵖ (coordinateProjective σ i).obj)
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ))
    (X : ModuleCat.{wR} Γᵐᵒᵖ)
    (hXfinite : IsFiniteLength Γᵐᵒᵖ X)
    (horth : ∀ (j : κ), j ∈ d.support i.succ →
      ∀ f : (coordinateProjective σ j).obj ⟶ X, f = 0) :
    IsFilteredBy
      (fun k : Fin (Fintype.card κ) ↦
        coordinateSimple σ (d.removed k))
      (fun k ↦ k ≤ i) X := by
  let motive : ℕ∞ → Prop := fun n ↦
    ∀ (Y : ModuleCat.{wR} Γᵐᵒᵖ),
      IsFiniteLength Γᵐᵒᵖ Y →
      Module.length Γᵐᵒᵖ Y = n →
      (∀ (j : κ), j ∈ d.support i.succ →
        ∀ f : (coordinateProjective σ j).obj ⟶ Y, f = 0) →
      IsFilteredBy
        (fun k : Fin (Fintype.card κ) ↦
          coordinateSimple σ (d.removed k))
        (fun k ↦ k ≤ i) Y
  refine
    (WellFoundedLT.induction (motive := motive)
      (Module.length Γᵐᵒᵖ X) ?_)
      X hXfinite rfl horth
  intro n ih Y hYfinite hYn hYorth
  by_cases hsub : Subsingleton Y
  · exact
      IsFilteredBy.zero Y
        ((ModuleCat.isZero_iff_subsingleton).mpr hsub)
  letI : Nontrivial Y := not_subsingleton_iff_nontrivial.mp hsub
  have hNA :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hYfinite)
  letI : IsNoetherian Γᵐᵒᵖ Y := hNA.1
  letI : IsArtinian Γᵐᵒᵖ Y := hNA.2
  obtain ⟨N, hNatom, -⟩ :=
    (eq_bot_or_exists_atom_le
      (⊤ : Submodule Γᵐᵒᵖ Y)).resolve_left top_ne_bot
  have hNsimpleModule : IsSimpleModule Γᵐᵒᵖ N :=
    isSimpleModule_iff_isAtom.mpr hNatom
  let S : ModuleCat.{wR} Γᵐᵒᵖ := ModuleCat.of Γᵐᵒᵖ N
  have hSsimple : Simple S :=
    simple_iff_isSimpleModule.mpr hNsimpleModule
  obtain ⟨k, ⟨e⟩⟩ :=
    coordinateSimple_complete σ hfinite S hSsimple
  obtain ⟨l, rfl⟩ := (removed_bijective d).2 k
  let nι : S ⟶ Y := ModuleCat.ofHom N.subtype
  letI : Mono nι := by
    rw [ModuleCat.mono_iff_injective]
    exact N.subtype_injective
  let a : coordinateSimple σ (d.removed l) ⟶ Y :=
    e.inv ≫ nι
  letI : Mono a := by
    dsimp only [a]
    infer_instance
  have hli : l ≤ i := by
    by_contra hnot
    have hil : i < l := lt_of_not_ge hnot
    have hlower : d.removed l ∈ d.support i.succ :=
      later_removed_mem_support d hil
    let P := coordinateProjectiveCover σ hfinite (d.removed l)
    letI : Epi P.map := P.essentialEpi.1
    letI : Simple (coordinateSimple σ (d.removed l)) :=
      coordinateSimple_isSimple σ hfinite (d.removed l)
    have ha : a ≠ 0 := by
      intro ha
      exact Simple.not_isZero (coordinateSimple σ (d.removed l))
        (IsZero.of_mono_eq_zero a ha)
    have hPa : P.map ≫ a ≠ 0 := by
      intro hPa
      apply ha
      rw [← cancel_epi P.map]
      simpa using hPa
    exact hPa (hYorth (d.removed l) hlower (P.map ≫ a))
  let Q : ModuleCat.{wR} Γᵐᵒᵖ := ModuleCat.of Γᵐᵒᵖ (Y ⧸ N)
  let g : Y ⟶ Q := ModuleCat.ofHom N.mkQ
  letI : Epi g := by
    rw [ModuleCat.epi_iff_surjective]
    exact Submodule.Quotient.mk_surjective N
  have hzero : a ≫ g = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change N.mkQ (N.subtype (e.inv.hom x)) = 0
    apply (Submodule.Quotient.mk_eq_zero N).mpr
    exact (e.inv.hom x).property
  have hshort :
      (ShortComplex.mk a g hzero).ShortExact := by
    constructor
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    change LinearMap.range (N.subtype.comp e.inv.hom) =
      LinearMap.ker N.mkQ
    rw [LinearMap.range_comp]
    have heSurj : Function.Surjective e.inv.hom :=
      (ModuleCat.epi_iff_surjective e.inv).mp inferInstance
    rw [LinearMap.range_eq_top.mpr heSurj,
      Submodule.map_top, Submodule.range_subtype,
      Submodule.ker_mkQ]
  have hQfinite : IsFiniteLength Γᵐᵒᵖ Q :=
    hYfinite.of_surjective (f := N.mkQ)
      (Submodule.Quotient.mk_surjective N)
  have hQorth : ∀ (j : κ), j ∈ d.support i.succ →
      ∀ f : (coordinateProjective σ j).obj ⟶ Q, f = 0 := by
    intro j hj f
    let hP := coordinateProjective_isFiniteProjective σ j
    letI : Projective (coordinateProjective σ j).obj := hP.2
    let lift : (coordinateProjective σ j).obj ⟶ Y :=
      Projective.factorThru f g
    calc
      f = lift ≫ g := (Projective.factorThru_comp f g).symm
      _ = 0 ≫ g := congrArg (fun t ↦ t ≫ g) (hYorth j hj lift)
      _ = 0 := zero_comp
  have hNne : N ≠ ⊥ := hNatom.ne_bot
  have hQlt : Module.length Γᵐᵒᵖ Q < n := by
    rw [← hYn]
    exact Submodule.length_quotient_lt N hNne
  have htail :
      IsFilteredBy
        (fun k : Fin (Fintype.card κ) ↦
          coordinateSimple σ (d.removed k))
        (fun k ↦ k ≤ i) Q :=
    ih (Module.length Γᵐᵒᵖ Q) hQlt Q hQfinite rfl hQorth
  exact
    IsFilteredBy.extension l hli a g hzero hshort htail


-- @@ L440-453 verbatim
/-- The concrete standard quotient has finite length whenever its
coordinate projective cover does. -/
theorem deletionCoordinateStandardQuotient_isFiniteLength
    (hfinite : ∀ i : κ,
      IsFiniteLength Γᵐᵒᵖ (coordinateProjective σ i).obj)
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ)) :
    IsFiniteLength Γᵐᵒᵖ
      (deletionCoordinateStandardQuotient σ d i) := by
  apply (hfinite (d.removed i)).of_surjective
    (f := (deletionCoordinateStandardProjection σ d i).hom)
  exact
    (ModuleCat.epi_iff_surjective
      (deletionCoordinateStandardProjection σ d i)).mp inferInstance


-- @@ L455-471 verbatim
/-- The concrete coordinate standard quotient is filtered by exactly the
coordinate simples permitted at its deletion step. -/
theorem deletionCoordinateStandardQuotient_simpleFiltered
    (hfinite : ∀ i : κ,
      IsFiniteLength Γᵐᵒᵖ (coordinateProjective σ i).obj)
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ)) :
    IsFilteredBy
      (fun k : Fin (Fintype.card κ) ↦
        coordinateSimple σ (d.removed k))
      (fun k ↦ k ≤ i)
      (deletionCoordinateStandardQuotient σ d i) :=
  isFilteredBy_of_finiteLength_of_hom_later_eq_zero
    σ hfinite d i (deletionCoordinateStandardQuotient σ d i)
    (deletionCoordinateStandardQuotient_isFiniteLength
      σ hfinite d i)
    (hom_deletionCoordinateStandardQuotient_eq_zero σ d i)


-- @@ L473-501 verbatim
/-- Exact CPS maximality clause for the concrete coordinate quotient.
Every epic quotient of the removed coordinate projective filtered by the
coordinate simples with indices `k ≤ i` factors through it. -/
theorem deletionCoordinateStandardProjection_maximal
    (hfinite : ∀ i : κ,
      IsFiniteLength Γᵐᵒᵖ (coordinateProjective σ i).obj)
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ))
    {Q : ModuleCat.{wR} Γᵐᵒᵖ}
    (q : (coordinateProjective σ (d.removed i)).obj ⟶ Q)
    (_hq : Epi q)
    (hQ : IsFilteredBy
      (fun k : Fin (Fintype.card κ) ↦
        coordinateSimple σ (d.removed k))
      (fun k ↦ k ≤ i) Q) :
    ∃ u : deletionCoordinateStandardQuotient σ d i ⟶ Q,
      deletionCoordinateStandardProjection σ d i ≫ u = q := by
  let hkill : ∀ (j : κ), j ∈ d.support i.succ →
      ∀ f : (coordinateProjective σ j).obj ⟶
        (coordinateProjective σ (d.removed i)).obj,
        f ≫ q = 0 := by
    intro j hj f
    exact
      hom_eq_zero_of_mem_later_support_to_filtered
        σ hfinite d i j hj hQ (f ≫ q)
  exact
    ⟨coordinateStandardDesc σ (d.support i.succ) (d.removed i) q hkill,
      coordinateStandardProjection_desc σ
        (d.support i.succ) (d.removed i) q hkill⟩


-- @@ L503-527 verbatim
/-- The quotient-by-later-coordinate-trace construction supplies the full
standard-module object at every deletion step: epic projection, permitted
simple filtration, and the universal maximal-quotient property. -/
def deletionCoordinateStandardModule
    (hfinite : ∀ i : κ,
      IsFiniteLength Γᵐᵒᵖ (coordinateProjective σ i).obj)
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ)) :
    StandardModule
      (fun k : Fin (Fintype.card κ) ↦
        coordinateSimple σ (d.removed k))
      (fun k ↦ coordinateProjectiveCover σ hfinite (d.removed k))
      i where
  object := deletionCoordinateStandardQuotient σ d i
  projection := deletionCoordinateStandardProjection σ d i
  epi_projection :=
    coordinateStandardProjection_epi σ
      (d.support i.succ) (d.removed i)
  simpleFiltered :=
    deletionCoordinateStandardQuotient_simpleFiltered σ hfinite d i
  maximal := by
    intro Q q hq hQ
    exact
      deletionCoordinateStandardProjection_maximal
        σ hfinite d i q hq hQ


-- @@ L529-529 verbatim
/-! ## Exact remaining highest-weight interface -/


-- @@ L531-538 verbatim
/-- The literal kernel of the coordinate standard projection: the trace
of all coordinate projectives surviving to the next support. -/
abbrev deletionCoordinateStandardKernel
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ)) :
    ModuleCat.{wR} Γᵐᵒᵖ :=
  ModuleCat.of Γᵐᵒᵖ
    (coordinateProjectiveTrace σ (d.support i.succ) (d.removed i))


-- @@ L540-548 verbatim
/-- The literal trace inclusion into the removed coordinate projective. -/
def deletionCoordinateStandardKernelι
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ)) :
    deletionCoordinateStandardKernel σ d i ⟶
      (coordinateProjective σ (d.removed i)).obj :=
  ModuleCat.ofHom
    (coordinateProjectiveTrace σ
      (d.support i.succ) (d.removed i)).subtype


-- @@ L550-555 verbatim
instance deletionCoordinateStandardKernelι_mono
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ)) :
    Mono (deletionCoordinateStandardKernelι σ d i) := by
  rw [ModuleCat.mono_iff_injective]
  exact Submodule.subtype_injective _


-- @@ L557-567 verbatim
/-- The trace inclusion is killed by the standard quotient projection. -/
theorem deletionCoordinateStandardKernel_zero
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ)) :
    deletionCoordinateStandardKernelι σ d i ≫
      deletionCoordinateStandardProjection σ d i = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact x.property


-- @@ L569-591 verbatim
/-- The defining trace-kernel/standard-quotient sequence is literally short
exact. -/
theorem deletionCoordinateStandard_shortExact
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (i : Fin (Fintype.card κ)) :
    (ShortComplex.mk
      (deletionCoordinateStandardKernelι σ d i)
      (deletionCoordinateStandardProjection σ d i)
      (deletionCoordinateStandardKernel_zero σ d i)).ShortExact := by
  constructor
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
  change
    LinearMap.range
        (coordinateProjectiveTrace σ
          (d.support i.succ) (d.removed i)).subtype =
      LinearMap.ker
        (coordinateProjectiveTrace σ
          (d.support i.succ) (d.removed i)).mkQ
  exact
    (LinearMap.exact_iff.mp
      (LinearMap.exact_subtype_mkQ
        (coordinateProjectiveTrace σ
          (d.support i.succ) (d.removed i)))).symm


-- @@ L593-606 verbatim
/-- The sole remaining module-theoretic field needed to turn the concrete
coordinate simples, covers, standards, and trace kernels into an ordered
highest-weight structure.  It asks for a filtration of each later trace by
the already constructed later standard modules. -/
structure DeletionCoordinateStandardKernelFiltration
    (hfinite : ∀ i : κ,
      IsFiniteLength Γᵐᵒᵖ (coordinateProjective σ i).obj)
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ) : Prop where
  filtered : ∀ i : Fin (Fintype.card κ),
    IsFilteredBy
      (fun j : Fin (Fintype.card κ) ↦
        (deletionCoordinateStandardModule σ hfinite d j).object)
      (fun j ↦ i < j)
      (deletionCoordinateStandardKernel σ d i)


-- @@ L608-638 verbatim
/-- Once the later-trace standard filtrations are supplied, all other
fields of the ordered highest-weight structure are furnished by the
coordinate construction itself. -/
def deletionCoordinateOrderedHighestWeightStructure
    (hfinite : ∀ i : κ,
      IsFiniteLength Γᵐᵒᵖ (coordinateProjective σ i).obj)
    (d : QuotientSubmoduleEquidistribution.SetClosure.SaturatedSupportDeletionChain κ)
    (hkernel :
      DeletionCoordinateStandardKernelFiltration σ hfinite d) :
    OrderedHighestWeightStructure
      (ModuleCat.{wR} Γᵐᵒᵖ) (Fin (Fintype.card κ)) where
  simple k := coordinateSimple σ (d.removed k)
  simple_isSimple k :=
    coordinateSimple_isSimple σ hfinite (d.removed k)
  simple_complete S hS := by
    obtain ⟨k, ⟨e⟩⟩ :=
      coordinateSimple_complete σ hfinite S hS
    obtain ⟨i, hi⟩ := (removed_bijective d).2 k
    subst k
    exact ⟨i, ⟨e⟩⟩
  simple_nodup := by
    rintro i j ⟨e⟩
    apply removed_injective d
    exact coordinateSimple_eq_of_iso σ hfinite e
  cover k := coordinateProjectiveCover σ hfinite (d.removed k)
  standard k := deletionCoordinateStandardModule σ hfinite d k
  kernel k := deletionCoordinateStandardKernel σ d k
  kernelι k := deletionCoordinateStandardKernelι σ d k
  kernel_zero k := deletionCoordinateStandardKernel_zero σ d k
  kernel_shortExact k := deletionCoordinateStandard_shortExact σ d k
  kernel_standardFiltered := hkernel.filtered


-- @@ L640-640 verbatim
end SaturatedDeletion


-- @@ L642-642 verbatim
end QuotientSubmoduleEquidistribution.AuslanderEquivalence.CoordinateIdempotent
