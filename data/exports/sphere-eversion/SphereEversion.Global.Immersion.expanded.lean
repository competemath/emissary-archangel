import Mathlib.Analysis.Convex.AmpleSet
import Mathlib.Geometry.Manifold.Instances.Sphere
import SphereEversion.ToMathlib.LinearAlgebra.FiniteDimensional
import SphereEversion.ToMathlib.Geometry.Manifold.Immersion
import SphereEversion.ToMathlib.Analysis.InnerProductSpace.Rotation
import SphereEversion.Global.Gromov
import SphereEversion.Global.TwistOneJetSec

-- set_option trace.filter_inst_type true

-- @@ L10-10 verbatim
noncomputable section


-- @@ L12-12 verbatim
open Metric Module Set Function LinearMap Filter ContinuousLinearMap


-- @@ L14-16 verbatim
open scoped Manifold Topology

-- Can't open ContDiff because `ω` conflicts with the notation for orientation below

-- @@ L17-17 verbatim
local notation "∞" => ((⊤ : ℕ∞) : WithTop ℕ∞)


-- @@ L19-19 verbatim
section General


-- @@ L21-29 expanded
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H') {M' : Type*}
  [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ((⊤ : ℕ∞) : WithTop ℕ∞) M'] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F] {G : Type*} [TopologicalSpace G]
  (J : ModelWithCorners ℝ F G) (N : Type*) [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ((⊤ : ℕ∞) : WithTop ℕ∞) N]


-- @@ L31-31 verbatim
@[inherit_doc] local notation "TM" => TangentSpace I

-- @@ L32-32 verbatim
@[inherit_doc] local notation "TM'" => TangentSpace I'

-- @@ L33-33 verbatim
@[inherit_doc] local notation "HJ" => ModelProd (ModelProd H H') (E →L[ℝ] E')

-- @@ L34-34 verbatim
@[inherit_doc] local notation "ψJ" => chartAt HJ


-- @@ L36-39 verbatim
variable (M M') in
/-- The relation of immersions for maps between two manifolds. -/
def immersionRel : RelMfld I M I' M' :=
  {σ | Injective σ.2}


-- @@ L41-45 expanded
omit [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [IsManifold I' ((⊤ : ℕ∞) : WithTop ℕ∞) M'] in
@[simp]
theorem mem_immersionRel_iff {σ : OneJetBundle I M I' M'} :
    σ ∈ immersionRel I M I' M' ↔ Injective (σ.2 : TangentSpace I _ →L[ℝ] TangentSpace I' _) :=
  Iff.rfl


-- @@ L47-55 verbatim
set_option backward.isDefEq.respectTransparency false in
/-- A characterisation of the immersion relation in terms of a local chart. -/
theorem mem_immersionRel_iff' {σ σ' : OneJetBundle I M I' M'} (hσ' : σ' ∈ (ψJ σ).source) :
    σ' ∈ immersionRel I M I' M' ↔ Injective (ψJ σ σ').2 := by
  simp_rw [mem_immersionRel_iff]
  rw [oneJetBundle_chartAt_apply, inCoordinates_eq]
  · simp_rw [ContinuousLinearMap.coe_comp, ContinuousLinearEquiv.coe_coe, EquivLike.comp_injective,
      EquivLike.injective_comp]
  exacts [hσ'.1.1, hσ'.1.2]


-- @@ L57-59 verbatim
theorem chartAt_image_immersionRel_eq {σ : OneJetBundle I M I' M'} :
    ψJ σ '' ((ψJ σ).source ∩ immersionRel I M I' M') = (ψJ σ).target ∩ {q : HJ | Injective q.2} :=
  PartialEquiv.IsImage.image_eq fun _σ' hσ' ↦ (mem_immersionRel_iff' I I' hσ').symm


-- @@ L61-71 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem immersionRel_open [FiniteDimensional ℝ E] : IsOpen (immersionRel I M I' M') := by
  simp_rw [ChartedSpace.isOpen_iff HJ (immersionRel I M I' M'), chartAt_image_immersionRel_eq]
  refine fun σ ↦ (ψJ σ).open_target.inter ?_
  convert! isOpen_univ.prod ContinuousLinearMap.isOpen_injective
  · ext x
    -- Porting note: `mem_prod` is a simp lemma, but the next line is still needed.
    rw [mem_prod]
    simp
  · infer_instance
  · infer_instance


-- @@ L73-79 expanded
omit [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [IsManifold I' ((⊤ : ℕ∞) : WithTop ℕ∞) M'] in
@[simp]
theorem immersionRel_slice_eq {m : M} {m' : M'} {p : DualPair <| TangentSpace% m}
    {φ : TangentSpace% m →L[ℝ] TangentSpace% m'} (hφ : Injective φ) :
    (immersionRel I M I' M').slice ⟨(m, m'), φ⟩ p =
      (((p.π.ker).map (φ : TM m →ₛₗ[.id ℝ] TM' m')) : Set <| TM' m')ᶜ :=
  Set.ext_iff.mpr fun _ ↦ p.injective_update_iff hφ


-- @@ L81-81 verbatim
variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ E']


-- @@ L83-91 expanded
omit [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [IsManifold I' ((⊤ : ℕ∞) : WithTop ℕ∞) M'] in
theorem immersionRel_ample (h : finrank ℝ E < finrank ℝ E') : (immersionRel I M I' M').Ample :=
  by
  rw [RelMfld.ample_iff]
  rintro ⟨⟨m, m'⟩, φ : TangentSpace% m →L[ℝ] TangentSpace% m'⟩ (p : DualPair (TangentSpace% m))
    (hφ : Injective φ)
  have : FiniteDimensional ℝ (TangentSpace% m) := inferInstanceAs <| FiniteDimensional ℝ E
  have hcodim := one_lt_rank_of_rank_lt_rank p.ker_pi_ne_top h φ.toLinearMap
  rw [immersionRel_slice_eq I I' hφ]
  exact AmpleSet.of_one_lt_codim hcodim


-- @@ L93-96 verbatim
/-- This is lemma `lem:open_ample_immersion` from the blueprint. -/
theorem immersionRel_open_ample (h : finrank ℝ E < finrank ℝ E') :
    IsOpen (immersionRel I M I' M') ∧ (immersionRel I M I' M').Ample :=
  ⟨immersionRel_open I I', immersionRel_ample I I' h⟩


-- @@ L98-98 verbatim
end General


-- @@ L100-100 verbatim
section Generalbis


-- @@ L102-111 expanded
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {H : Type*}
  [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless] {M : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] {E' : Type*}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] {H' : Type*}
  [TopologicalSpace H'] (I' : ModelWithCorners ℝ E' H') [I'.Boundaryless] {M' : Type*}
  [MetricSpace M'] [ChartedSpace H' M'] [IsManifold I' ((⊤ : ℕ∞) : WithTop ℕ∞) M'] {EP : Type*}
  [NormedAddCommGroup EP] [NormedSpace ℝ EP] [FiniteDimensional ℝ EP] {HP : Type*}
  [TopologicalSpace HP] {IP : ModelWithCorners ℝ EP HP} [IP.Boundaryless] {P : Type*}
  [TopologicalSpace P] [ChartedSpace HP P] [IsManifold IP ((⊤ : ℕ∞) : WithTop ℕ∞) P]
  {C : Set (P × M)} {ε : M → ℝ}


-- @@ L113-113 verbatim
variable (M M' IP P)


-- @@ L115-120 verbatim
/-- parametric h-principle for immersions. -/
theorem immersionRel_satisfiesHPrincipleWith
    [T2Space P] [SigmaCompactSpace P] [T2Space M] [SigmaCompactSpace M] [SigmaCompactSpace M']
    (h : finrank ℝ E < finrank ℝ E') (hC : IsClosed C) (hε_pos : ∀ x, 0 < ε x)
    (hε_cont : Continuous ε) : (immersionRel I M I' M').SatisfiesHPrincipleWith IP C ε :=
  (immersionRel_ample I I' h).satisfiesHPrincipleWith (immersionRel_open I I') hC hε_pos hε_cont


-- @@ L122-122 verbatim
end Generalbis


-- @@ L124-125 verbatim
/-! The inclusion and antipodal map on a sphere are immersions:
these results are not used directly, but are good sanity checks. -/

-- @@ L126-126 verbatim
section sanitycheck


-- @@ L128-129 verbatim
variable {n : ℕ} (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fact (finrank ℝ E = n + 1)]


-- @@ L131-135 expanded
/-- The inclusion of `𝕊^n` into `ℝ^{n+1}` is an immersion. -/
theorem immersion_inclusion_sphere :
    Immersion (𝓡 n) 𝓘(ℝ, E) (fun x : sphere (0 : E) 1 ↦ (x : E)) ((⊤ : ℕ∞) : WithTop ℕ∞)
    where
  contMDiff := contMDiff_coe_sphere.of_le le_top
  diff_injective := injective_mvfderiv_subtypeVal_sphere


-- @@ L137-147 expanded
/-- The antipodal map on `𝕊^n ⊆ ℝ^{n+1}` is an immersion. -/
theorem immersion_antipodal_sphere :
    Immersion (𝓡 n) 𝓘(ℝ, E) (fun x : sphere (0 : E) 1 ↦ -(x : E)) ((⊤ : ℕ∞) : WithTop ℕ∞)
    where
  contMDiff :=
    -- Write this as the composition of `coe_sphere` and the antipodal map on `E`.
        -- The other direction elaborates much worse.
    (contDiff_neg.contMDiff).comp (contMDiff_coe_sphere.of_le le_top)
  diff_injective
    x := by
    change Injective (mfderiv% (-fun x : sphere (0 : E) 1 ↦ (x : E)) x)
    rw [mfderiv_neg]
    exact neg_injective.comp (injective_mvfderiv_subtypeVal_sphere x)


-- @@ L149-149 verbatim
end sanitycheck


-- @@ L151-151 verbatim
section sphere_eversion


-- @@ L153-153 verbatim
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 3)]


-- @@ L155-155 verbatim
set_option synthInstance.checkSynthOrder false

-- @@ L156-156 verbatim
attribute [local instance] FiniteDimensional.of_fact_finrank_eq_succ

-- @@ L157-157 verbatim
set_option synthInstance.checkSynthOrder true


-- @@ L159-164 verbatim
@[inherit_doc] local notation "𝕊²" => sphere (0 : E) 1

-- TODO: generalise these statements to `n` dimensions
-- the only obstacle is the construction of rotations requires working on ℝ³.

-- The relation of immersion of a two-sphere into its ambient Euclidean space.

-- @@ L165-165 verbatim
@[inherit_doc] local notation "𝓡_imm" => immersionRel (𝓡 2) 𝕊² 𝓘(ℝ, E) E


-- @@ L167-169 verbatim
variable (ω : Orientation ℝ E (Fin 3))

-- this result holds mutatis mutandis in `ℝ^n`

-- @@ L170-175 expanded
theorem smooth_bs :
    CMDiff ((⊤ : ℕ∞) : WithTop ℕ∞) fun p : ℝ × (sphere (0 : E) 1) ↦
      (1 - p.1) • (p.2 : E) + p.1 • -(p.2 : E) :=
  by
  refine (ContMDiff.smul (I := 𝓘(ℝ)) ?_ ?_).add (contMDiff_fst.smul ?_)
  · exact (contDiff_const.sub contDiff_id).contMDiff.comp contMDiff_fst
  · exact (contMDiff_coe_sphere.of_le le_top).comp contMDiff_snd
  · exact (contDiff_neg.contMDiff.comp (contMDiff_coe_sphere.of_le le_top)).comp contMDiff_snd


-- @@ L177-189 expanded
def formalEversionAux : FamilyOneJetSec (𝓡 2) 𝕊² 𝓘(ℝ, E) E 𝓘(ℝ, ℝ) ℝ :=
  familyJoin (smooth_bs E) <|
    familyTwist (drop (oneJetExtSec ⟨((↑) : 𝕊² → E), contMDiff_coe_sphere.of_le le_top⟩))
      (fun p : ℝ × 𝕊² ↦ ω.rot (p.1, p.2))
      (by
        intro p
        have : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, E →L[ℝ] E) ((⊤ : ℕ∞) : WithTop ℕ∞) ω.rot (p.1, p.2) :=
          by
          refine ((ω.contDiff_rot ?_).of_le le_top).contMDiffAt
          exact ne_zero_of_mem_unit_sphere p.2
        apply this.comp p (f := fun (p : ℝ × sphere 0 1) ↦ (p.1, (p.2 : E)))
        apply contMDiff_fst.prodMk_space ((contMDiff_coe_sphere.of_le le_top).comp contMDiff_snd))


-- @@ L191-194 verbatim
/-- A formal eversion of a two-sphere into its ambient Euclidean space. -/
def formalEversionAux2 : HtpyFormalSol 𝓡_imm :=
  { formalEversionAux E ω with
    is_sol' t x := (ω.isometry_rot t x).injective.comp (injective_mvfderiv_subtypeVal_sphere x) }


-- @@ L196-197 verbatim
def formalEversion : HtpyFormalSol 𝓡_imm :=
  (formalEversionAux2 E ω).reindex ⟨smoothStep, contMDiff_iff_contDiff.mpr smoothStep.smooth⟩


-- @@ L199-203 verbatim
@[simp]
theorem formalEversion_bs (t : ℝ) :
    (formalEversion E ω t).bs = fun x : 𝕊² ↦
      (1 - smoothStep t : ℝ) • (x : E) + (smoothStep t : ℝ) • (-x : E) :=
  rfl


-- @@ L205-205 verbatim
theorem formalEversion_zero (x : 𝕊²) : (formalEversion E ω 0).bs x = x := by simp


-- @@ L207-207 verbatim
theorem formalEversion_one (x : 𝕊²) : (formalEversion E ω 1).bs x = -x := by simp


-- @@ L209-219 verbatim
set_option backward.isDefEq.respectTransparency.types false in
theorem formalEversionHolAtZero {t : ℝ} (ht : t < 1 / 4) :
    (formalEversion E ω t).toOneJetSec.IsHolonomic := by
  intro x
  change
    mfderiv% (fun y : 𝕊² ↦ ((1 : ℝ) - smoothStep t) • (y : E) +
      smoothStep t • -(y : E)) x =
      (ω.rot (smoothStep t, x)).comp (mfderiv% (fun y : 𝕊² ↦ (y : E)) x)
  simp_rw [smoothStep.of_lt ht, ω.rot_zero, ContinuousLinearMap.id_comp]
  congr with y
  simp [smoothStep.of_lt ht]


-- @@ L221-237 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem formalEversionHolAtOne {t : ℝ} (ht : 3 / 4 < t) :
    (formalEversion E ω t).toOneJetSec.IsHolonomic := by
  intro x
  change
    mfderiv% (fun y : 𝕊² ↦ ((1 : ℝ) - smoothStep t) • (y : E) +
      smoothStep t • -(y : E)) x =
      (ω.rot (smoothStep t, x)).comp (mfderiv% (fun y : 𝕊² ↦ (y : E)) x)
  trans mfderiv% (-fun y : 𝕊² ↦ (y : E)) x
  · congr 2 with y
    simp [smoothStep.of_gt ht]
  ext v
  erw [mfderiv_neg, ContinuousLinearMap.coe_comp, Function.comp_apply, _root_.neg_apply,
    smoothStep.of_gt ht]
  rw [ω.rot_one]; · rfl
  rw [← range_mvfderiv_subtypeVal (n := 2) x]
  exact LinearMap.mem_range_self ..


-- @@ L239-254 expanded
theorem formalEversion_hol_near_zero_one :
    expand_binders% (p => Filter.Eventually p <| 𝓝ˢ ({0, 1} ×ˢ univ)) s : ℝ × 𝕊²,
      (formalEversion E ω s.1).toOneJetSec.IsHolonomicAt s.2 :=
  by
  have : (Iio (1 / 4 : ℝ) ∪ Ioi (3 / 4)) ×ˢ (univ : Set 𝕊²) ∈ 𝓝ˢ (({0, 1} : Set ℝ) ×ˢ univ) :=
    by
    refine ((isOpen_Iio.union isOpen_Ioi).prod isOpen_univ).mem_nhdsSet.mpr ?_
    rintro ⟨s, x⟩ ⟨hs, hx⟩
    refine ⟨?_, mem_univ _⟩
    simp_rw [mem_insert_iff, mem_singleton_iff] at hs
    rcases hs with (rfl | rfl)
    · exact Or.inl (show (0 : ℝ) < 1 / 4 by norm_num)
    · exact Or.inr (show (3 / 4 : ℝ) < 1 by norm_num)
  filter_upwards [this]
  rintro ⟨t, x⟩ ⟨ht | ht, _hx⟩
  · exact formalEversionHolAtZero E ω ht x
  · exact formalEversionHolAtOne E ω ht x


-- @@ L255-255 verbatim
section helper


-- @@ L257-261 verbatim
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E F G : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]

-- move to Analysis.Calculus.ContDiff.Defs, or so

-- @@ L262-266 verbatim
lemma ContDiff.inr (x : E) (n : ℕ∞) : ContDiff 𝕜 n fun p : F ↦ (⟨x, p⟩ : E × F) := by
  rw [contDiff_prod_iff]
  exact ⟨contDiff_const, contDiff_id⟩

-- is this form actually useful, compared to `uncurry_left`?

-- @@ L267-270 verbatim
theorem ContDiff.uncurry_left' (n : ℕ∞) {f : E × F → G}
    (hf : ContDiff 𝕜 n f) (x : E) :
    ContDiff 𝕜 n (fun p : F ↦ f ⟨x, p⟩) :=
  hf.comp (ContDiff.inr x n)


-- @@ L272-275 verbatim
theorem ContDiff.uncurry_left {f : E → F → G} (n : ℕ∞) (hf : ContDiff 𝕜 n ↿f) (x : E) :
    ContDiff 𝕜 n (f x) := by
  have : f x = (uncurry f) ∘ fun p : F ↦ (⟨x, p⟩ : E × F) := by ext; simp
  rw [this]; exact hf.comp (ContDiff.inr x n)


-- @@ L277-288 verbatim
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] (I' : ModelWithCorners 𝕜 E' H')
  {M' : Type*} [MetricSpace M'] [ChartedSpace H' M']
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace 𝕜 EP]
  {HP : Type*} [TopologicalSpace HP] (IP : ModelWithCorners 𝕜 EP HP)
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]

-- move to Mathlib.Geometry.Manifold.ContMDiff.Product

-- @@ L289-294 verbatim
lemma ContMDiff.prod_left {n : ℕ∞} (x : M) :
    CMDiff n fun p : M' ↦ (⟨x, p⟩ : M × M') := by
  rw [contMDiff_prod_iff]
  exact ⟨contMDiff_const, contMDiff_id⟩

-- move to Mathlib.Geometry.Manifold.ContMDiff.Product

-- @@ L295-299 verbatim
theorem ContMDiff.uncurry_left {n : ℕ∞} {f : M → M' → P}
    (hf : CMDiff n ↿f) (x : M) : CMDiff n (f x) := by
  have : f x = (uncurry f) ∘ fun p : M' ↦ ⟨x, p⟩ := by ext; simp
  -- or just `apply hf.comp (ContMDiff.prod_left I I' x)`
  rw [this]; exact hf.comp (ContMDiff.prod_left I I' x)


-- @@ L301-301 verbatim
end helper


-- @@ L303-338 expanded
theorem sphere_eversion :
    ∃ f : ℝ → 𝕊² → E,
      CMDiff ((⊤ : ℕ∞) : WithTop ℕ∞) ↿f ∧
        (f 0 = fun x : 𝕊² ↦ (x : E)) ∧
          (f 1 = fun x : 𝕊² ↦ -(x : E)) ∧
            ∀ t, Immersion (𝓡 2) 𝓘(ℝ, E) (f t) ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  by
  classical
  let ω : Orientation ℝ E (Fin 3) :=
    ((stdOrthonormalBasis _ _).reindex <| finCongr (Fact.out : finrank ℝ E = 3)).toBasis.orientation
  have rankE : finrank ℝ E = 3 := Fact.out
  have : FiniteDimensional ℝ E := FiniteDimensional.of_finrank_eq_succ rankE
  have ineq_rank : finrank ℝ (EuclideanSpace ℝ (Fin 2)) < finrank ℝ E := by simp [rankE]
  let ε : 𝕊² → ℝ := fun _ ↦ 1
  have hε_pos : ∀ x, 0 < ε x := fun _ ↦ zero_lt_one
  have hε_cont : Continuous ε := continuous_const
  have : Nontrivial E := nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ E = 3)
  have : Nonempty (sphere 0 1 : Set E) := (NormedSpace.sphere_nonempty.mpr zero_le_one).to_subtype
  rcases
    (immersionRel_satisfiesHPrincipleWith (𝓡 2) 𝕊² 𝓘(ℝ, E) E 𝓘(ℝ, ℝ) ℝ ineq_rank
          ((Finite.isClosed (by simp : ({0, 1} : Set ℝ).Finite)).prod isClosed_univ) hε_pos
          hε_cont).bs
      (formalEversion E ω) (formalEversion_hol_near_zero_one E ω) with
    ⟨f, h₁, h₂, -, h₅⟩
  have := h₂.forall_mem principal_le_nhdsSet
  refine ⟨f, h₁, ?_, ?_, ?_ /-h₅-/ ⟩
  · ext x
    rw [this (0, x) (by simp)]
    convert! formalEversion_zero E ω x
  · ext x
    rw [this (1, x) (by simp)]
    convert! formalEversion_one E ω x
  ·
    exact fun t ↦
      { contMDiff := h₁.uncurry_left 𝓘(ℝ, ℝ) (𝓡 2) 𝓘(ℝ, E) t
        diff_injective := h₅ t }
        -- The next instance will be used in the main file.


-- @@ L339-342 verbatim
instance (n : ℕ) : Fact (finrank ℝ (EuclideanSpace ℝ <| Fin n) = n) :=
  ⟨finrank_euclideanSpace_fin⟩

-- The next notation will be used in the main file.

-- @@ L343-343 verbatim
notation "ℝ^" n:arg => EuclideanSpace ℝ (Fin n)


-- @@ L345-345 verbatim
end sphere_eversion
