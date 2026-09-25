/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth

! This file was ported from Lean 3 source module global.twist_one_jet_sec
-/
import SphereEversion.Global.OneJetSec


-- @@ L10-10 verbatim
noncomputable section


-- @@ L12-12 verbatim
open Set Equiv Bundle ContinuousLinearMap

-- @@ L13-13 verbatim
open scoped Manifold Topology ContDiff


-- @@ L15-15 verbatim
section ArbitraryField

-- @@ L16-16 verbatim
universe u v


-- @@ L18-24 verbatim
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type u} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (M : Type*)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] {F : Type*}
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] {G : Type*} [TopologicalSpace G]
  {J : ModelWithCorners 𝕜 F G} {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  (V : Type*) [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  (V' : Type*) [NormedAddCommGroup V'] [NormedSpace 𝕜 V']


-- @@ L26-26 verbatim
section Smoothness


-- @@ L28-29 verbatim
notation "J¹[" 𝕜 ", " E ", " I ", " M ", " V "]" => TotalSpace (E →L[𝕜] V)
  (fun b ↦ (TangentSpace I : M → _) b →L[𝕜] (Bundle.Trivial M V) b)

-- @@ L30-30 verbatim
variable {I M V}

-- @@ L31-33 expanded
variable
  {f : N → TotalSpace (E →L[𝕜] V) (fun b ↦ (TangentSpace I : M → _) b →L[𝕜] (Bundle.Trivial M V) b)}
    -- todo: remove or use to prove `contMDiff_one_jet_eucl_bundle`


-- @@ L34-41 verbatim
theorem contMDiffAt_one_jet_eucl_bundle' {x₀ : N} :
    ContMDiffAt J (I.prod 𝓘(𝕜, E →L[𝕜] V)) ∞ f x₀ ↔ CMDiffAt ∞ (fun x  ↦ (f x).1) x₀ ∧
    CMDiffAt ∞ (fun x  ↦ show E →L[𝕜] V from
      (f x).2 ∘L (trivializationAt E (TangentSpace I : M → _) (f x₀).1).symmL 𝕜 (f x).1) x₀ := by
  simp_rw [contMDiffAt_hom_bundle, inCoordinates, Trivial.trivializationAt,
    Trivial.trivialization_continuousLinearMapAt]
  dsimp only [Bundle.Trivial]
  simp_rw [ContinuousLinearMap.id_comp]


-- @@ L43-59 verbatim
theorem contMDiffAt_one_jet_eucl_bundle {x₀ : N} :
    ContMDiffAt J (I.prod 𝓘(𝕜, E →L[𝕜] V)) ∞ f x₀ ↔
      CMDiffAt ∞ (fun x  ↦ (f x).1) x₀ ∧
        CMDiffAt ∞ (fun x  ↦ show E →L[𝕜] V from
          (f x).2 ∘L (trivializationAt E (TangentSpace I) (f x₀).proj).symmL 𝕜 (f x).proj) x₀ := by
  rw [contMDiffAt_hom_bundle, and_congr_right_iff]
  intro hf
  refine Filter.EventuallyEq.contMDiffAt_iff ?_
  have :=
    hf.continuousAt.preimage_mem_nhds
      (((tangentBundleCore I M).isOpen_baseSet (achart H (f x₀).proj)).mem_nhds
        ((tangentBundleCore I M).mem_baseSet_at (f x₀).proj))
  filter_upwards [this] with x _
  simp_rw [inCoordinates, Trivial.trivializationAt,
    Trivial.trivialization_continuousLinearMapAt, ← ContinuousLinearMap.comp_assoc]
  dsimp only [Bundle.Trivial]
  simp_rw [ContinuousLinearMap.id_comp]


-- @@ L61-67 expanded
theorem ContMDiffAt.one_jet_eucl_bundle_mk' {f : N → M} {ϕ : N → E →L[𝕜] V} {x₀ : N}
    (hf : CMDiffAt ∞ f x₀)
    (hϕ :
      CMDiffAt ∞
          (fun x ↦
            show E →L[𝕜] V from
              ϕ x ∘L (trivializationAt E (TangentSpace I : M → _) (f x₀)).symmL 𝕜 (f x))
        x₀) :
    ContMDiffAt J (I.prod 𝓘(𝕜, E →L[𝕜] V)) ∞
      (fun x ↦ Bundle.TotalSpace.mk (f x) (ϕ x) :
        N →
          TotalSpace (E →L[𝕜] V) (fun b ↦ (TangentSpace I : M → _) b →L[𝕜] (Bundle.Trivial M V) b))
      x₀ :=
  contMDiffAt_one_jet_eucl_bundle'.mpr ⟨hf, hϕ⟩


-- @@ L69-75 expanded
theorem ContMDiffAt.one_jet_eucl_bundle_mk {f : N → M} {ϕ : N → E →L[𝕜] V} {x₀ : N}
    (hf : CMDiffAt ∞ f x₀)
    (hϕ :
      CMDiffAt ∞
          (fun x ↦
            show E →L[𝕜] V from ϕ x ∘L (trivializationAt E (TangentSpace I) (f x₀)).symmL 𝕜 (f x))
        x₀) :
    ContMDiffAt J (I.prod 𝓘(𝕜, E →L[𝕜] V)) ∞
      (fun x ↦ Bundle.TotalSpace.mk (f x) (ϕ x) :
        N →
          TotalSpace (E →L[𝕜] V) (fun b ↦ (TangentSpace I : M → _) b →L[𝕜] (Bundle.Trivial M V) b))
      x₀ :=
  contMDiffAt_one_jet_eucl_bundle.mpr ⟨hf, hϕ⟩


-- @@ L77-77 verbatim
end Smoothness


-- @@ L79-79 verbatim
section Sections


-- @@ L81-86 expanded
/-- A section of a 1-jet bundle seen as a bundle over the source manifold. -/
@[ext]
structure OneJetEuclSec where
  toFun :
    M → TotalSpace (E →L[𝕜] V) (fun b ↦ (TangentSpace I : M → _) b →L[𝕜] (Bundle.Trivial M V) b)
  is_sec' : ∀ p, (toFun p).1 = p
  contMDiff' : ContMDiff I (I.prod 𝓘(𝕜, E →L[𝕜] V)) ∞ toFun


-- @@ L88-88 verbatim
variable {I M V}


-- @@ L90-94 expanded
instance :
    DFunLike (OneJetEuclSec I M V) M fun _ ↦
      TotalSpace (E →L[𝕜] V) (fun b ↦ (TangentSpace I : M → _) b →L[𝕜] (Bundle.Trivial M V) b)
    where
  coe := OneJetEuclSec.toFun
  coe_injective := by
    intro S T h
    ext x <;> rw [h]


-- @@ L96-98 verbatim
@[simp]
theorem OneJetEuclSec.is_sec (s : OneJetEuclSec I M V) (p : M) : (s p).1 = p :=
  s.is_sec' p


-- @@ L100-103 verbatim
@[simp]
theorem OneJetEuclSec.contMDiff (s : OneJetEuclSec I M V) :
    ContMDiff I (I.prod 𝓘(𝕜, E →L[𝕜] V)) ∞ s :=
  s.contMDiff'


-- @@ L105-105 verbatim
end Sections


-- @@ L107-107 verbatim
section proj


-- @@ L109-111 verbatim
instance piBugInstanceRestatement (x : M) :
    TopologicalSpace (TangentSpace% x →L[𝕜] Trivial M V x) := by
  infer_instance


-- @@ L113-118 verbatim
instance piBugInstanceRestatement2 (x : M × V) : TopologicalSpace (OneJetSpace I 𝓘(𝕜, V) x) := by
  infer_instance

/- Given a smooth manifold `M` and a normed space `V`, there is a canonical projection from the
one-jet bundle of maps from `M` to `V` to the bundle of homomorphisms from `TM` to `V`. This is
constructed using the fact that each tangent space to `V` is canonically isomorphic to `V`. -/

-- @@ L119-120 expanded
def proj (v : OneJetBundle I M 𝓘(𝕜, V) V) :
    TotalSpace (E →L[𝕜] V) (fun b ↦ (TangentSpace I : M → _) b →L[𝕜] (Bundle.Trivial M V) b) :=
  ⟨v.1.1, v.2⟩


-- @@ L122-129 verbatim
theorem contMDiff_proj : ContMDiff ((I.prod 𝓘(𝕜, V)).prod 𝓘(𝕜, E →L[𝕜] V)) (I.prod 𝓘(𝕜, E →L[𝕜] V))
    ∞ (proj I M V) := by
  intro x₀
  have : ContMDiffAt ((I.prod 𝓘(𝕜, V)).prod 𝓘(𝕜, E →L[𝕜] V)) _ ∞ id x₀ := contMDiffAt_id
  simp_rw +unfoldPartialApp [contMDiffAt_oneJetBundle, inTangentCoordinates, inCoordinates,
    TangentBundle.continuousLinearMapAt_model_space, ContinuousLinearMap.one_def,
    TangentSpace] at this
  exact this.1.one_jet_eucl_bundle_mk this.2.2


-- @@ L131-131 verbatim
variable {I M V}


-- @@ L133-136 verbatim
def drop (s : OneJetSec I M 𝓘(𝕜, V) V) : OneJetEuclSec I M V where
  toFun := (proj I M V).comp s
  is_sec' _ := rfl
  contMDiff' := (contMDiff_proj I M V).comp s.contMDiff


-- @@ L138-138 verbatim
end proj


-- @@ L140-145 verbatim
section incl

/- Given a smooth manifold `M` and a normed space `V`, there is a canonical map from the
the product with V of the bundle of homomorphisms from `TM` to `V` to the one-jet bundle of maps
from `M` to `V`. In fact this map is a diffeomorphism.  This is constructed using the fact that each
tangent space to `V` is canonically isomorphic to `V`. -/

-- @@ L146-147 expanded
def incl
    (v :
      TotalSpace (E →L[𝕜] V) (fun b ↦ (TangentSpace I : M → _) b →L[𝕜] (Bundle.Trivial M V) b) ×
        V) :
    OneJetBundle I M 𝓘(𝕜, V) V :=
  ⟨(v.1.1, v.2), v.1.2⟩


-- @@ L149-159 verbatim
set_option backward.isDefEq.respectTransparency false in
theorem contMDiff_incl : ContMDiff ((I.prod 𝓘(𝕜, E →L[𝕜] V)).prod 𝓘(𝕜, V))
    ((I.prod 𝓘(𝕜, V)).prod 𝓘(𝕜, E →L[𝕜] V)) ∞ (incl I M V) := by
  intro x₀
  have : ContMDiffAt ((I.prod 𝓘(𝕜, E →L[𝕜] V)).prod 𝓘(𝕜, V)) _ ∞ Prod.fst x₀ := contMDiffAt_fst
  rw [contMDiffAt_one_jet_eucl_bundle] at this
  refine this.1.oneJetBundle_mk contMDiffAt_snd ?_
  unfold inTangentCoordinates inCoordinates TangentSpace
  simp_rw [TangentBundle.continuousLinearMapAt_model_space, ContinuousLinearMap.one_def,
    ContinuousLinearMap.id_comp]
  exact this.2


-- @@ L161-164 expanded
omit [IsManifold I ∞ M] in
@[simp]
theorem incl_fst_fst
    (v :
      TotalSpace (E →L[𝕜] V) (fun b ↦ (TangentSpace I : M → _) b →L[𝕜] (Bundle.Trivial M V) b) ×
        V) :
    (incl I M V v).1.1 = v.1.1 :=
  rfl


-- @@ L166-169 expanded
omit [IsManifold I ∞ M] in
@[simp]
theorem incl_snd
    (v :
      TotalSpace (E →L[𝕜] V) (fun b ↦ (TangentSpace I : M → _) b →L[𝕜] (Bundle.Trivial M V) b) ×
        V) :
    (incl I M V v).1.2 = v.2 :=
  rfl


-- @@ L171-171 verbatim
end incl


-- @@ L173-173 verbatim
end ArbitraryField


-- @@ L175-175 verbatim
section familyTwist


-- @@ L177-182 verbatim
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H) (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
  (V' : Type*) [NormedAddCommGroup V'] [NormedSpace ℝ V'] {F : Type*} [NormedAddCommGroup F]
  [NormedSpace ℝ F] {G : Type*} [TopologicalSpace G] (J : ModelWithCorners ℝ F G) (N : Type*)
  [TopologicalSpace N] [ChartedSpace G N]


-- @@ L184-189 expanded
/-- A section of a 1-jet bundle seen as a bundle over the source manifold. -/
@[ext]
structure FamilyOneJetEuclSec where
  toFun :
    N × M → TotalSpace (E →L[ℝ] V) (fun b ↦ (TangentSpace I : M → _) b →L[ℝ] (Bundle.Trivial M V) b)
  is_sec' : ∀ p, (toFun p).1 = p.2
  contMDiff' : ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] V)) ∞ toFun


-- @@ L191-195 expanded
instance :
    FunLike (FamilyOneJetEuclSec I M V J N) (N × M)
      (TotalSpace (E →L[ℝ] V) (fun b ↦ (TangentSpace I : M → _) b →L[ℝ] (Bundle.Trivial M V) b))
    where
  coe := FamilyOneJetEuclSec.toFun
  coe_injective := by
    intro S T h
    ext x <;> rw [h]


-- @@ L197-197 verbatim
variable {I M V J N}


-- @@ L199-202 verbatim
@[simp]
theorem FamilyOneJetEuclSec.is_sec (s : FamilyOneJetEuclSec I M V J N) (p : N × M) :
    (s p).1 = p.2 :=
  s.is_sec' p


-- @@ L204-207 verbatim
@[simp]
theorem FamilyOneJetEuclSec.contMDiff (s : FamilyOneJetEuclSec I M V J N) :
    ContMDiff (J.prod I) (I.prod 𝓘(ℝ, E →L[ℝ] V)) ∞ s :=
  s.contMDiff'


-- @@ L209-209 verbatim
variable {V'}


-- @@ L211-219 verbatim
set_option backward.isDefEq.respectTransparency.types false in
def familyJoin {f : N × M → V} (hf : CMDiff ∞ f)
    (s : FamilyOneJetEuclSec I M V J N) : FamilyOneJetSec I M 𝓘(ℝ, V) V J N
    where
  bs n m := (incl I M V (s (n, m), f (n, m))).1.2
  ϕ n m := (incl I M V (s (n, m), f (n, m))).2
  contMDiff' := by
    convert (contMDiff_incl I M V).comp (s.contMDiff.prodMk hf)
    ext : 1 <;> simp


-- @@ L221-233 verbatim
set_option backward.isDefEq.respectTransparency false in
def familyTwist (s : OneJetEuclSec I M V) (i : N × M → V →L[ℝ] V')
    (hi : ∀ x₀ : N × M, CMDiffAt ∞ i x₀) :
    FamilyOneJetEuclSec I M V' J N where
  toFun p := ⟨p.2, (i p).comp (s p.2).2⟩
  is_sec' p := rfl
  contMDiff' := by
    refine fun x₀ ↦ contMDiffAt_snd.one_jet_eucl_bundle_mk' ?_
    simp_rw [ContinuousLinearMap.comp_assoc]
    have : ContMDiffAt (J.prod I) _ ∞ (fun x : N × M  ↦ _) x₀ := s.contMDiff.comp contMDiff_snd x₀
    rw [contMDiffAt_one_jet_eucl_bundle'] at this
    refine (hi x₀).clm_comp ?_
    convert! this.2 <;> simp [s.is_sec]


-- @@ L235-235 verbatim
end familyTwist
