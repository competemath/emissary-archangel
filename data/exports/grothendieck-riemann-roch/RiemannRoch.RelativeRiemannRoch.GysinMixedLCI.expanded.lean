/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import RiemannRoch.RelativeRiemannRoch.G0RigidityLCI
import RiemannRoch.CharacteristicClasses.CartierGysinUnitARRHU
import RiemannRoch.CharacteristicClasses.CartierGysinClosureCIIL3B
import RiemannRoch.CharacteristicClasses.PencilEFibreCIIL3B
import RiemannRoch.CharacteristicClasses.HbcPSectionARRHBCP
import RiemannRoch.CharacteristicClasses.SpecializationZeroLineARRG45


-- @@ L14-48 verbatim
/-!
# Mixed `G₀` Cartier Gysin maps for the deformation to the normal cone (brick C1, G2GC1)

For the mixed `K⁰/G₀` transport of the lci (singular) case one needs, for a Cartier divisor
`D = V(I) ⊂ M` (in the application `M₀ = A` or the exceptional component `E`) and a finite
`F : W ⟶ M` (in the application `W = Z × ℙ¹ ↪ M`):

1. the Gysin map `D^! : G₀(M) → G₀(D)` restricts bundles: `D^! ∘ k0ToG0_M = k0ToG0_D ∘ ι^*`
   (`gysinI_k0ToG0`, AR8 item 5 analogue);
2. `D^! ∘ F_* = Fz_* ∘ D_W^!` for **all** `g ∈ G₀(W)` (`gysinI_comp_finitePushforward`, AR8 item 4 +
   AR10), where `D_W^! : G₀(W) → G₀(W ×_M D)` is the Gysin map of the pulled-back divisor on `W`,
   with its target identified with `G₀(W ×_M D)` by pulling back along `η : W ×_M D ⟶ W`.

The identification of the abstract target `G(σ_W-killed)` with `G₀(W ×_M D)` (G2K risk register,
"C1 Med-High") is `etaPull`: every coherent `σ_W`-killed sheaf `K` satisfies `K ≅ η_* η^* K`
(the ARRHU argument works for every killed `K`, not only for cokernels), so `η^*` is exact on killed
short exact sequences.  In particular `η_* ∘ D_W^! = D_* ∘ D^!` on `W` (`pushEta_comp_gysinBC`),
which is what `G₀`-rigidity consumes.

No regularity of `M`, `W` or `D` is used.

## Layers
* `Generic`: abstract twist `(T, σ)` on `M` with `AR7Bridge`, `(TW, σW)` on `W`, `PushCompat`:
  `gysinI`, `gysinI_k0ToG0`, `etaPull`, `gysinBC`, `gysinI_comp_finitePushforward`.
* `Line`: `T = L⁻¹ ⊗ -` for a rank-one `L` with section `σ` (`gysinLine`, `gysinBCLine`), and
  `η_* ∘ D_W^! = 1 − [F^*L⁻¹]·` (`pushEta_comp_gysinBCLine`).
* `Fibre`: `W ×_M V(σ) ≅ Z`, the section `secOf`, the fibre restriction `rLine : G₀(W) → G₀(Z)`,
  a target divisor `ε : D ↪ M` with the ideal of `V(σ)` (`gysD`), and the two gates
  `gysD_k0ToG0` (1), `gysD_comp_finitePushforward` (2).
* `Sections`, `Deformation`, `Assembly`: on `M = totalGlobal Y J`, `W = Z × ℙ¹`: sections of
  `W → Z` are closed immersions, `W ∩ M₀ ≅ Z` (`isIso_fst_pr_zero`), the fibre sections are
  `subS ≫ subschemeTιGlobal` and `secInfG` (`secOf_zero`, `secOf_inf`), `G₀`-rigidity `rLine_rigid`
  (modulo the twist comparison `htw`), and the G-side gates of the mixed transport
  (`mixedGysin_gates`, `hmix_zero`, `hmix_inf`).
-/


-- @@ L50-50 verbatim
set_option autoImplicit false

-- @@ L51-51 verbatim
set_option linter.unusedSectionVars false


-- @@ L53-53 verbatim
noncomputable section


-- @@ L55-55 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SchemeKTheory

-- @@ L56-56 verbatim
open ExactGrothendieck ExactGrothendieck.CartierGysinAR1 ExactGrothendieck.CartierGysinAR8

-- @@ L57-57 verbatim
open ExactGrothendieck.PrincipalGysin (KerCokerClosed)

-- @@ L58-58 verbatim
open KSpecialization.AR8 KSpecialization.AR4


-- @@ L60-60 verbatim
universe u


-- @@ L62-62 verbatim
namespace KSpecialization.G2GC1


-- @@ L64-64 verbatim
/-! ### The generic layer -/


-- @@ L66-66 verbatim
section Generic


-- @@ L68-70 verbatim
variable {M : Scheme.{u}} [IsLocallyNoetherian M] {I : M.IdealSheafData}
  {T : M.Modules ⥤ M.Modules} [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [T.PreservesMonomorphisms] {σ : T ⟶ 𝟭 M.Modules}


-- @@ L72-77 verbatim
/-- **The Cartier Gysin map `D^! : G₀(M) → G₀(V(I))`** of a locally principal `I` with an exact
twist `(T, σ)` (`G₀(M) → G₀(σ-killed) = G₀(I-killed) ≅ G₀(V(I))`). -/
def gysinI (hI : LocallyPrincipal I) (hB : AR7Bridge I T σ) (hc : Central T σ)
    (hT : ∀ E, IsCoherentLike M E → IsCoherentLike M (T.obj E)) : G0 M →+ G0 I.subscheme :=
  (g0KilledIEquiv hI).toAddMonoidHom.comp
    ((killedTransport hB).comp (cartierGysin hc kerCokerClosed_isCoherentLike hT))


-- @@ L79-84 verbatim
/-- **(1) `D^! ∘ k0ToG0 = k0ToG0 ∘ ι^*`** when `σ` is a monomorphism on every vector bundle. -/
theorem gysinI_k0ToG0 (hI : LocallyPrincipal I) (hB : AR7Bridge I T σ) (hc : Central T σ)
    (hT : ∀ E, IsCoherentLike M E → IsCoherentLike M (T.obj E))
    (hmono : ∀ E : M.Modules, IsFiniteLocallyFree M E → Mono (ap T σ E)) (z : K0 M) :
    gysinI hI hB hc hT (k0ToG0 M z) = k0ToG0 I.subscheme (pullbackK0 I.subschemeι z) :=
  KSpecialization.CIIL3.cartierGysin_k0ToG0 hI hB hc hT hmono z


-- @@ L86-91 verbatim
/-- `G2GC2.gysinFibre` is `gysinI` transported along `e`. -/
theorem gysinFibre_eq [IsNoetherian I.subscheme] {Z : Scheme.{u}} [IsNoetherian Z]
    (hI : LocallyPrincipal I) (hB : AR7Bridge I T σ) (hc : Central T σ)
    (hT : ∀ E, IsCoherentLike M E → IsCoherentLike M (T.obj E)) (e : Z ≅ I.subscheme) :
    G2GC2.gysinFibre hI hB hc hT e = (finitePushforward e.inv).comp (gysinI hI hB hc hT) :=
  rfl


-- @@ L93-95 verbatim
variable {W : Scheme.{u}} [IsLocallyNoetherian W] (F : W ⟶ M) [IsFinite F]
  {TW : W.Modules ⥤ W.Modules} [TW.Additive] [PreservesFiniteLimits TW]
  [PreservesFiniteColimits TW] [TW.PreservesMonomorphisms] {σW : TW ⟶ 𝟭 W.Modules}


-- @@ L97-98 verbatim
set_option quotPrecheck false in
local notation "ηI" => pullback.fst F I.subschemeι

-- @@ L99-100 verbatim
set_option quotPrecheck false in
local notation "FzI" => pullback.snd F I.subschemeι


-- @@ L102-105 verbatim
omit [IsLocallyNoetherian M] [IsFinite F] in
/-- The fibre `W ×_M V(I)` is locally noetherian. -/
theorem isLocallyNoetherian_fibre : IsLocallyNoetherian (pullback F I.subschemeι) :=
  LocallyOfFiniteType.isLocallyNoetherian (pullback.fst F I.subschemeι)


-- @@ L107-117 verbatim
/-- **The unit `K ⟶ η_* η^* K` is an isomorphism for every coherent `σ_W`-killed `K`** (ARRHU's
argument, for an arbitrary killed sheaf). -/
theorem isIso_adjUnit_eta (hB : AR7Bridge I T σ)
    (c : PushCompat TW σW T σ (Scheme.Modules.pushforward F)) (K : W.Modules)
    (hK : Killed TW σW (IsCoherentLike W) K) :
    IsIso (ProjectionFormula.adjUnit (pullback.fst F I.subschemeι) K) := by
  letI : K.IsFinitePresentation := hK.1
  have hk := c.killed (finitePush_obj F) K hK
  have hkill : IdealKills I ((Scheme.Modules.pushforward F).obj K) :=
    hB.idealKills_of_killed _ hk.1 hk.2
  exact KSpecialization.ARRHU.isIso_adjUnit_fst F I K (fun V a ha m => hkill V a ha m)


-- @@ L119-142 verbatim
/-- `η^*` is exact on short exact sequences of coherent `σ_W`-killed sheaves. -/
theorem pullback_eta_shortExact (hB : AR7Bridge I T σ)
    (c : PushCompat TW σW T σ (Scheme.Modules.pushforward F)) (S : ShortComplex W.Modules)
    (hS : S.ShortExact) (h₁ : Killed TW σW (IsCoherentLike W) S.X₁)
    (h₂ : Killed TW σW (IsCoherentLike W) S.X₂) :
    (S.map (Scheme.Modules.pullback (pullback.fst F I.subschemeι))).ShortExact := by
  haveI := hS.mono_f
  haveI := hS.epi_g
  have ex : (S.map (Scheme.Modules.pullback ηI)).Exact :=
    hS.exact.map_of_epi_of_preservesCokernel _ inferInstance inferInstance
  haveI := isIso_adjUnit_eta F hB c S.X₁ h₁
  haveI := isIso_adjUnit_eta F hB c S.X₂ h₂
  have hn := ProjectionFormula.adjUnit_naturality ηI S.f
  have heq : (Scheme.Modules.pushforward ηI).map ((Scheme.Modules.pullback ηI).map S.f) =
      inv (ProjectionFormula.adjUnit ηI S.X₁) ≫ S.f ≫ ProjectionFormula.adjUnit ηI S.X₂ := by
    rw [hn, IsIso.inv_hom_id_assoc]
  have hm : Mono ((Scheme.Modules.pushforward ηI).map ((Scheme.Modules.pullback ηI).map S.f)) := by
    rw [heq]; infer_instance
  haveI : (Scheme.Modules.pushforward ηI).Faithful :=
    (pushforwardFullyFaithful ηI).faithful
  haveI : Mono ((Scheme.Modules.pullback ηI).map S.f) :=
    (Scheme.Modules.pushforward ηI).mono_of_mono_map hm
  exact { exact := ex, mono_f := this,
          epi_g := inferInstanceAs (Epi ((Scheme.Modules.pullback ηI).map S.g)) }


-- @@ L144-149 verbatim
/-- The coherent object `η^* K` on `W ×_M V(I)`. -/
def etaPullObject (K : {K : W.Modules // Killed TW σW (IsCoherentLike W) K}) :
    {G : (pullback F I.subschemeι).Modules // IsCoherentLike (pullback F I.subschemeι) G} :=
  ⟨(Scheme.Modules.pullback ηI).obj K.1, by
    letI : K.1.IsFinitePresentation := K.2.1
    exact pullback_isFinitePresentation_global ηI K.1⟩


-- @@ L151-158 verbatim
/-- **Identification of the abstract Gysin target**: `[K] ↦ [η^* K]`,
`G(σ_W-killed coherent on W) → G₀(W ×_M V(I))`. -/
def etaPull (hB : AR7Bridge I T σ) (c : PushCompat TW σW T σ (Scheme.Modules.pushforward F)) :
    SubcategoryGroup W.Modules (Killed TW σW (IsCoherentLike W)) →+
      G0 (pullback F I.subschemeι) :=
  ExactGrothendieck.map (etaPullObject F) fun A B D h => by
    obtain ⟨a, b, zero, hS⟩ := h
    exact ⟨_, _, _, pullback_eta_shortExact F hB c (ShortComplex.mk a b zero) hS A.2 B.2⟩


-- @@ L160-165 verbatim
theorem etaPull_classOf (hB : AR7Bridge I T σ)
    (c : PushCompat TW σW T σ (Scheme.Modules.pushforward F)) (K : W.Modules)
    (hK : Killed TW σW (IsCoherentLike W) K) :
    etaPull F hB c (subcategoryClassOf _ _ K hK) =
      g0ClassOf _ ((Scheme.Modules.pullback ηI).obj K) (etaPullObject F ⟨K, hK⟩).2 :=
  ExactGrothendieck.map_classOf _ _ _


-- @@ L167-171 verbatim
/-- **The Gysin map of the pulled-back divisor on `W`**, with target `G₀(W ×_M V(I))`. -/
def gysinBC (hB : AR7Bridge I T σ) (c : PushCompat TW σW T σ (Scheme.Modules.pushforward F))
    (hcW : Central TW σW) (hTW : ∀ E, IsCoherentLike W E → IsCoherentLike W (TW.obj E)) :
    G0 W →+ G0 (pullback F I.subschemeι) :=
  (etaPull F hB c).comp (cartierGysin hcW kerCokerClosed_isCoherentLike hTW)


-- @@ L173-186 verbatim
/-- `η_* ∘ etaPull = D_*` (inclusion of killed sheaves): `[η_* η^* K] = [K]`. -/
theorem pushEta_comp_etaPull (hB : AR7Bridge I T σ)
    (c : PushCompat TW σW T σ (Scheme.Modules.pushforward F)) :
    haveI := isLocallyNoetherian_fibre (I := I) F
    (finitePushforward ηI).comp (etaPull F hB c) =
      pushDivisor (T := TW) (σ := σW) (P := IsCoherentLike W) := by
  haveI := isLocallyNoetherian_fibre (I := I) F
  refine hom_ext _ _ fun K => ?_
  obtain ⟨K, hK⟩ := K
  change finitePushforward ηI (etaPull F hB c (subcategoryClassOf _ _ K hK)) =
    pushDivisor (subcategoryClassOf _ _ K hK)
  rw [etaPull_classOf, finitePushforward_classOf, pushDivisor_classOf]
  haveI := isIso_adjUnit_eta F hB c K hK
  exact (g0ClassOf_iso _ _ _ (asIso (ProjectionFormula.adjUnit ηI K))).symm


-- @@ L188-196 verbatim
/-- `η_* ∘ D_W^! = D_* ∘ D^!` on `W`. -/
theorem pushEta_comp_gysinBC (hB : AR7Bridge I T σ)
    (c : PushCompat TW σW T σ (Scheme.Modules.pushforward F))
    (hcW : Central TW σW) (hTW : ∀ E, IsCoherentLike W E → IsCoherentLike W (TW.obj E)) :
    haveI := isLocallyNoetherian_fibre (I := I) F
    (finitePushforward ηI).comp (gysinBC F hB c hcW hTW) =
      (pushDivisor (T := TW) (σ := σW)).comp
        (cartierGysin hcW kerCokerClosed_isCoherentLike hTW) := by
  rw [gysinBC, ← AddMonoidHom.comp_assoc, pushEta_comp_etaPull]


-- @@ L198-240 verbatim
/-- The killed-group square: `pullFibre_M ∘ (F_* on killed) = Fz_* ∘ etaPull`. -/
theorem killedMap_compat (hI : LocallyPrincipal I) (hB : AR7Bridge I T σ)
    (c : PushCompat TW σW T σ (Scheme.Modules.pushforward F)) :
    haveI := isLocallyNoetherian_fibre (I := I) F
    haveI : IsLocallyNoetherian I.subscheme := CIIL3B.isLocallyNoetherian_subscheme I
    (g0KilledIEquiv hI).toAddMonoidHom.comp ((killedTransport hB).comp
        (killedMap c (finitePush_obj F) (finitePush_exactOn F))) =
      (finitePushforward FzI).comp (etaPull F hB c) := by
  haveI := isLocallyNoetherian_fibre (I := I) F
  haveI : IsLocallyNoetherian I.subscheme := CIIL3B.isLocallyNoetherian_subscheme I
  refine hom_ext _ _ fun K => ?_
  obtain ⟨K, hK⟩ := K
  change g0KilledIEquiv hI (killedTransport hB (killedMap c (finitePush_obj F) (finitePush_exactOn F)
      (subcategoryClassOf _ _ K hK))) =
    finitePushforward FzI (etaPull F hB c (subcategoryClassOf _ _ K hK))
  have m1 : killedMap c (finitePush_obj F) (finitePush_exactOn F)
      (subcategoryClassOf W.Modules (Killed TW σW (IsCoherentLike W)) K hK) =
      subcategoryClassOf M.Modules (Killed T σ (IsCoherentLike M))
        ((Scheme.Modules.pushforward F).obj K) (c.killed (finitePush_obj F) _ hK) :=
    mapOn_classOf _ _ _ _ _
  rw [m1, killedTransport_classOf, etaPull_classOf]
  set G := (Scheme.Modules.pullback ηI).obj K
  have hG : IsCoherentLike _ G := (etaPullObject F ⟨K, hK⟩).2
  haveI := isIso_adjUnit_eta F hB c K hK
  have h1 : subcategoryClassOf M.Modules (KilledI I) ((Scheme.Modules.pushforward F).obj K)
      ⟨(c.killed (finitePush_obj F) _ hK).1, hB.idealKills_of_killed _
        (c.killed (finitePush_obj F) _ hK).1 (c.killed (finitePush_obj F) _ hK).2⟩ =
      KSpecialization.AR4.pushZero (I := I) (finitePushforward FzI (g0ClassOf _ G hG)) := by
    rw [finitePushforward_classOf]
    change _ = KSpecialization.AR4.pushZero (I := I) (ExactGrothendieck.classOf _ _
      ⟨(Scheme.Modules.pushforward FzI).obj G, (finitePushObject FzI ⟨G, hG⟩).2⟩)
    rw [KSpecialization.AR4.pushZero_classOf]
    refine ExactGrothendieck.subcategoryClassOf_iso _ _ _ _ KSpecialization.AR4.killedI_zero
      (isZero_zero _) ?_
    refine (Scheme.Modules.pushforward F).mapIso (asIso (ProjectionFormula.adjUnit ηI K)) ≪≫ ?_
    refine (Scheme.Modules.pushforwardComp ηI F).app G ≪≫ ?_
    refine (Scheme.Modules.pushforwardCongr pullback.condition).app G ≪≫ ?_
    exact ((Scheme.Modules.pushforwardComp FzI I.subschemeι).app G).symm
  rw [h1]
  have h2 := congrArg (fun f : G0 I.subscheme →+ G0 I.subscheme =>
    f (finitePushforward FzI (g0ClassOf _ G hG))) (KSpecialization.AR4.pullFibre_comp_pushZero hI)
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.id_apply] at h2
  exact h2


-- @@ L242-265 verbatim
/-- **(2) Gysin commutes with finite pushforward on all of `G₀(W)`**:
`D^! ∘ F_* = Fz_* ∘ D_W^!`, `Fz : W ×_M V(I) ⟶ V(I)`. -/
theorem gysinI_comp_finitePushforward (hI : LocallyPrincipal I) (hB : AR7Bridge I T σ)
    (hc : Central T σ) (hT : ∀ E, IsCoherentLike M E → IsCoherentLike M (T.obj E))
    (c : PushCompat TW σW T σ (Scheme.Modules.pushforward F))
    (hcW : Central TW σW) (hTW : ∀ E, IsCoherentLike W E → IsCoherentLike W (TW.obj E)) :
    haveI := isLocallyNoetherian_fibre (I := I) F
    haveI : IsLocallyNoetherian I.subscheme := CIIL3B.isLocallyNoetherian_subscheme I
    (gysinI hI hB hc hT).comp (finitePushforward F) =
      (finitePushforward FzI).comp (gysinBC F hB c hcW hTW) := by
  haveI := isLocallyNoetherian_fibre (I := I) F
  haveI : IsLocallyNoetherian I.subscheme := CIIL3B.isLocallyNoetherian_subscheme I
  have hcomm := cartierGysin_comp_finitePushforward F c hcW hTW hc hT
    (fun E _ => KSpecialization.AR7R.isIso_kernelComparison_pushforward F _)
    (fun E hE => KSpecialization.AR7R.isIso_cokernelComparison_pushforward F _ (hTW E hE) hE)
  rw [mapOn_pushforward_eq_finitePushforward] at hcomm
  refine AddMonoidHom.ext fun g => ?_
  have h1 := DFunLike.congr_fun hcomm g
  have h2 := DFunLike.congr_fun (killedMap_compat F hI hB c)
    (cartierGysin hcW kerCokerClosed_isCoherentLike hTW g)
  simp only [AddMonoidHom.comp_apply] at h1 h2
  simp only [gysinI, gysinBC, AddMonoidHom.comp_apply]
  rw [h1]
  exact h2


-- @@ L267-267 verbatim
end Generic


-- @@ L269-269 verbatim
/-! ### Abstract rigidity from `s_* ∘ r = 1 − τ` -/


-- @@ L271-271 verbatim
section Rigid


-- @@ L273-284 verbatim
/-- **Abstract rigidity.** If `π ∘ s_a = id` and `s_a ∘ r_a = 1 − τ` for the same `τ`, then
`r₀ = r₁`. -/
theorem rigid_of_section {G H : Type*} [AddCommGroup G] [AddCommGroup H] (π : G →+ H)
    (s₀ s₁ : H →+ G) (r₀ r₁ : G →+ H) (τ : G →+ G)
    (hπs₀ : π.comp s₀ = AddMonoidHom.id H) (hπs₁ : π.comp s₁ = AddMonoidHom.id H)
    (hr₀ : s₀.comp r₀ = AddMonoidHom.id G - τ) (hr₁ : s₁.comp r₁ = AddMonoidHom.id G - τ) :
    r₀ = r₁ := by
  have e₀ : r₀ = π.comp (s₀.comp r₀) := by
    rw [← AddMonoidHom.comp_assoc, hπs₀, AddMonoidHom.id_comp]
  have e₁ : r₁ = π.comp (s₁.comp r₁) := by
    rw [← AddMonoidHom.comp_assoc, hπs₁, AddMonoidHom.id_comp]
  rw [e₀, e₁, hr₀, hr₁]


-- @@ L286-286 verbatim
end Rigid


-- @@ L288-288 verbatim
/-! ### The line-bundle layer: `T = L⁻¹ ⊗ -`, `σ_E = (dual evaluation) ⊗ E` -/


-- @@ L290-290 verbatim
section Line


-- @@ L292-292 verbatim
open SchemeKTheory.LineBundleDual AlgebraicGeometry.Chow.M7 KSpecialization.AR7R


-- @@ L294-295 verbatim
variable {M : Scheme.{u}} [IsLocallyNoetherian M] {L : M.Modules} [L.IsQuasicoherent]
  [L.IsFinitePresentation] (σ : tensorUnitSheaf M ⟶ L)


-- @@ L297-299 verbatim
theorem isFiniteLocallyFree_dual (hL : HasConstantRank M L 1) :
    IsFiniteLocallyFree M (lineBundleDual M L) :=
  (lineBundleDual_hasConstantRank L hL).isFiniteLocallyFree


-- @@ L301-309 verbatim
/-- **The Gysin map of the Cartier divisor `V(σ)`**, `G₀(M) → G₀(V(σ))`. -/
def gysinLine (hL : HasConstantRank M L 1) : G0 M →+ G0 (sectionEvaluationIdealSheaf σ).subscheme :=
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits M _ (isFiniteLocallyFree_dual hL)
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits M _ (isFiniteLocallyFree_dual hL)
  gysinI (KSpecialization.AR4.locallyPrincipal_sectionEvaluationIdealSheaf σ
      (isLocalLineFrame_of_hasConstantRank_one hL))
    (ar7Bridge σ (isLocalLineFrame_of_hasConstantRank_one hL))
    (central_twist σ (isLocalLineFrame_of_hasConstantRank_one hL))
    (fun _ hE => tensorSheaf_isCoherentLike M _ _ (isFiniteLocallyFree_dual hL) hE)


-- @@ L311-319 verbatim
/-- **(1) for a line**: `V(σ)^! ∘ k0ToG0 = k0ToG0 ∘ ι^*` for a regular section `σ`. -/
theorem gysinLine_k0ToG0 (hL : HasConstantRank M L 1) (hreg : SectionIsRegular σ) (z : K0 M) :
    gysinLine σ hL (k0ToG0 M z) =
      k0ToG0 (sectionEvaluationIdealSheaf σ).subscheme
        (pullbackK0 (sectionEvaluationIdealSheaf σ).subschemeι z) := by
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits M _ (isFiniteLocallyFree_dual hL)
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits M _ (isFiniteLocallyFree_dual hL)
  exact gysinI_k0ToG0 _ _ _ _ (fun E hE => CIIL3B.hmono_of_sectionIsRegular σ
    (isLocalLineFrame_of_hasConstantRank_one hL) hreg E hE) z


-- @@ L321-321 verbatim
variable {W : Scheme.{u}} [IsLocallyNoetherian W] (F : W ⟶ M) [IsFinite F]


-- @@ L323-326 verbatim
theorem isFiniteLocallyFree_pullbackDual (hL : HasConstantRank M L 1) :
    IsFiniteLocallyFree W ((Scheme.Modules.pullback F).obj (lineBundleDual M L)) :=
  (SchemeKTheory.hasConstantRank_pullback W F _ 1
    (lineBundleDual_hasConstantRank L hL)).isFiniteLocallyFree


-- @@ L328-341 verbatim
/-- **The Gysin map of the pulled-back divisor on `W`**, `G₀(W) → G₀(W ×_M V(σ))`. -/
def gysinBCLine (hL : HasConstantRank M L 1) :
    G0 W →+ G0 (pullback F (sectionEvaluationIdealSheaf σ).subschemeι) :=
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits M _ (isFiniteLocallyFree_dual hL)
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits M _ (isFiniteLocallyFree_dual hL)
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits W _ (isFiniteLocallyFree_pullbackDual F hL)
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits W _
    (isFiniteLocallyFree_pullbackDual F hL)
  gysinBC F (ar7Bridge σ (isLocalLineFrame_of_hasConstantRank_one hL))
    (pushCompat F (dualEval σ) (isFiniteLocallyFree_dual hL))
    (sigmaT_central (locallyTrivial_of_hasConstantRank_one
      (SchemeKTheory.hasConstantRank_pullback W F _ 1 (lineBundleDual_hasConstantRank L hL)))
      (pullbackSection F (dualEval σ)))
    (fun _ hE => tensorSheaf_isCoherentLike W _ _ (isFiniteLocallyFree_pullbackDual F hL) hE)


-- @@ L343-356 verbatim
/-- **(2) for a line**: `V(σ)^! ∘ F_* = Fz_* ∘ V(F^*σ)^!` on all of `G₀(W)`. -/
theorem gysinLine_comp_finitePushforward (hL : HasConstantRank M L 1) :
    haveI := isLocallyNoetherian_fibre (I := sectionEvaluationIdealSheaf σ) F
    haveI : IsLocallyNoetherian (sectionEvaluationIdealSheaf σ).subscheme :=
      CIIL3B.isLocallyNoetherian_subscheme _
    (gysinLine σ hL).comp (finitePushforward F) =
      (finitePushforward (pullback.snd F (sectionEvaluationIdealSheaf σ).subschemeι)).comp
        (gysinBCLine σ F hL) := by
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits M _ (isFiniteLocallyFree_dual hL)
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits M _ (isFiniteLocallyFree_dual hL)
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits W _ (isFiniteLocallyFree_pullbackDual F hL)
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits W _
    (isFiniteLocallyFree_pullbackDual F hL)
  exact gysinI_comp_finitePushforward F _ _ _ _ _ _ _


-- @@ L358-377 verbatim
/-- The twist `[E] ↦ [F^*L⁻¹ ⊗ E]` on `G₀(W)` is multiplication by `[F^*L⁻¹] ∈ K₀(W)`. -/
theorem twistG_eq_k0ActG0 (hL : HasConstantRank M L 1)
    [(tensorSheafLeftFunctor W ((Scheme.Modules.pullback F).obj (lineBundleDual M L))).Additive]
    [PreservesFiniteLimits
      (tensorSheafLeftFunctor W ((Scheme.Modules.pullback F).obj (lineBundleDual M L)))]
    [PreservesFiniteColimits
      (tensorSheafLeftFunctor W ((Scheme.Modules.pullback F).obj (lineBundleDual M L)))]
    [(tensorSheafLeftFunctor W
      ((Scheme.Modules.pullback F).obj (lineBundleDual M L))).PreservesMonomorphisms]
    (hT : ∀ E, IsCoherentLike W E → IsCoherentLike W
      ((tensorSheafLeftFunctor W ((Scheme.Modules.pullback F).obj (lineBundleDual M L))).obj E)) :
    G2GC2.twistG hT = k0ActG0 W (pullbackK0 F (k0ClassOf M (lineBundleDual M L)
      (isFiniteLocallyFree_dual hL))) := by
  refine hom_ext _ _ fun E => ?_
  obtain ⟨E, hE⟩ := E
  change G2GC2.twistG hT (subcategoryClassOf _ _ E hE) = _
  rw [G2GC2.twistG_classOf, pullbackK0_classOf]
  change _ = k0ActG0 W (ExactGrothendieck.classOf _ _ ⟨_, _⟩) (ExactGrothendieck.classOf _ _ ⟨E, hE⟩)
  rw [k0ActG0_classOf, g0LeftMul_classOf]
  rfl


-- @@ L379-395 verbatim
/-- **`η_* ∘ V(F^*σ)^! = 1 − [F^*L⁻¹]·`** on `G₀(W)`. -/
theorem pushEta_comp_gysinBCLine (hL : HasConstantRank M L 1) :
    haveI := isLocallyNoetherian_fibre (I := sectionEvaluationIdealSheaf σ) F
    (finitePushforward (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι)).comp
        (gysinBCLine σ F hL) =
      AddMonoidHom.id (G0 W) - k0ActG0 W (pullbackK0 F (k0ClassOf M (lineBundleDual M L)
        (isFiniteLocallyFree_dual hL))) := by
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits M _ (isFiniteLocallyFree_dual hL)
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits M _ (isFiniteLocallyFree_dual hL)
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits W _ (isFiniteLocallyFree_pullbackDual F hL)
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits W _
    (isFiniteLocallyFree_pullbackDual F hL)
  have hTW : ∀ E, IsCoherentLike W E → IsCoherentLike W
      ((tensorSheafLeftFunctor W ((Scheme.Modules.pullback F).obj (lineBundleDual M L))).obj E) :=
    fun E hE => tensorSheaf_isCoherentLike W _ _ (isFiniteLocallyFree_pullbackDual F hL) hE
  rw [← twistG_eq_k0ActG0 F hL hTW, ← G2GC2.pushDivisor_comp_cartierGysin]
  exact pushEta_comp_gysinBC F _ _ _ hTW


-- @@ L397-397 verbatim
end Line


-- @@ L399-399 verbatim
/-! ### Fibre packaging: `W ×_M V(σ) ≅ Z` and a target divisor `D ≅ V(σ)` -/


-- @@ L401-401 verbatim
section Fibre


-- @@ L403-403 verbatim
open SchemeKTheory.LineBundleDual AlgebraicGeometry.Chow.M7 KSpecialization.AR7R


-- @@ L405-409 verbatim
variable {M : Scheme.{u}} [IsLocallyNoetherian M] {L : M.Modules} [L.IsQuasicoherent]
  [L.IsFinitePresentation] (σ : tensorUnitSheaf M ⟶ L)
  {W : Scheme.{u}} [IsLocallyNoetherian W] (F : W ⟶ M) [IsFinite F]
  {Z : Scheme.{u}} [IsLocallyNoetherian Z] (pr : W ⟶ Z)
  [IsIso (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι ≫ pr)]


-- @@ L411-414 verbatim
/-- The section `Z ≅ W ×_M V(σ) ↪ W` of `pr` cut out by the pulled-back divisor. -/
def secOf : Z ⟶ W :=
  inv (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι ≫ pr) ≫
    pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι


-- @@ L416-417 verbatim
instance secOf_isClosedImmersion : IsClosedImmersion (secOf σ F pr) := by
  unfold secOf; infer_instance


-- @@ L419-420 verbatim
theorem secOf_pr : secOf σ F pr ≫ pr = 𝟙 Z := by
  rw [secOf, Category.assoc, IsIso.inv_hom_id]


-- @@ L422-425 verbatim
theorem fst_pr_secOf :
    (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι ≫ pr) ≫ secOf σ F pr =
      pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι := by
  rw [secOf, IsIso.hom_inv_id_assoc]


-- @@ L427-432 verbatim
/-- **The `G₀` fibre restriction `r^! : G₀(W) → G₀(Z)`** along the pulled-back divisor,
`G₀(W) → G₀(W ×_M V(σ)) ≅ G₀(Z)`. -/
def rLine (hL : HasConstantRank M L 1) : G0 W →+ G0 Z :=
  haveI := isLocallyNoetherian_fibre (I := sectionEvaluationIdealSheaf σ) F
  (finitePushforward (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι ≫ pr)).comp
    (gysinBCLine σ F hL)


-- @@ L434-442 verbatim
/-- **`s_* ∘ r^! = 1 − [F^*L⁻¹]·`** on `G₀(W)`. -/
theorem secOf_comp_rLine (hL : HasConstantRank M L 1) :
    (finitePushforward (secOf σ F pr)).comp (rLine σ F pr hL) =
      AddMonoidHom.id (G0 W) - k0ActG0 W (pullbackK0 F (k0ClassOf M (lineBundleDual M L)
        (isFiniteLocallyFree_dual hL))) := by
  haveI := isLocallyNoetherian_fibre (I := sectionEvaluationIdealSheaf σ) F
  rw [rLine, ← AddMonoidHom.comp_assoc, ← ARRG45C.finitePushforward_comp]
  rw [ARRG45C.finitePushforward_congr (fst_pr_secOf σ F pr)]
  exact pushEta_comp_gysinBCLine σ F hL


-- @@ L444-474 verbatim
/-- **The `W`-side restriction on bundles**: for `F^*σ^∨` a monomorphism (`W ⊄ V(σ)`),
`V(F^*σ)^! [V] = [η^* V]` for every vector bundle class. -/
theorem gysinBCLine_k0ToG0 (hL : HasConstantRank M L 1)
    (hs : Mono (pullbackSection F (dualEval σ))) (w : K0 W) :
    haveI := isLocallyNoetherian_fibre (I := sectionEvaluationIdealSheaf σ) F
    gysinBCLine σ F hL (k0ToG0 W w) = k0ToG0 _
      (pullbackK0 (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι) w) := by
  haveI := isLocallyNoetherian_fibre (I := sectionEvaluationIdealSheaf σ) F
  have key : (gysinBCLine σ F hL).comp (k0ToG0 W) = (k0ToG0 _).comp
      (pullbackK0 (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι)) := by
    refine hom_ext _ _ fun V => ?_
    obtain ⟨V, hV⟩ := V
    change gysinBCLine σ F hL (k0ToG0 W (k0ClassOf W V hV)) =
      k0ToG0 _ (pullbackK0 _ (k0ClassOf W V hV))
    haveI := tensorSheafLeftFunctor_preservesFiniteLimits M _ (isFiniteLocallyFree_dual hL)
    haveI := tensorSheafLeftFunctor_preservesFiniteColimits M _ (isFiniteLocallyFree_dual hL)
    haveI := tensorSheafLeftFunctor_preservesFiniteLimits W _
      (isFiniteLocallyFree_pullbackDual F hL)
    haveI := tensorSheafLeftFunctor_preservesFiniteColimits W _
      (isFiniteLocallyFree_pullbackDual F hL)
    haveI : Mono (ap (tensorSheafLeftFunctor W ((Scheme.Modules.pullback F).obj
        (lineBundleDual M L))) (sigmaT _ (pullbackSection F (dualEval σ))) V) :=
      CIIL3B.mono_sigmaT_app (pullbackSection F (dualEval σ)) V hV
    haveI := CIIL3B.isIso_pullback_fst_cokernel_π σ F hL V
    rw [k0ToG0_classOf, pullbackK0_classOf, k0ToG0_classOf]
    simp only [gysinBCLine, gysinBC, AddMonoidHom.comp_apply]
    unfold g0ClassOf
    rw [cartierGysin_classOf_of_mono, etaPull_classOf]
    exact g0ClassOf_iso _ _ _ (asIso ((Scheme.Modules.pullback
      (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι)).map (cokernel.π _))).symm
  exact DFunLike.congr_fun key w


-- @@ L476-488 verbatim
/-- **`r^!` restricts bundles**: `r^! ∘ k0ToG0_W = k0ToG0_Z ∘ s^*` (needed for `hbc₀_of_mixed`). -/
theorem rLine_k0ToG0 (hL : HasConstantRank M L 1)
    (hs : Mono (pullbackSection F (dualEval σ))) (w : K0 W) :
    rLine σ F pr hL (k0ToG0 W w) = k0ToG0 Z (pullbackK0 (secOf σ F pr) w) := by
  haveI := isLocallyNoetherian_fibre (I := sectionEvaluationIdealSheaf σ) F
  rw [rLine, AddMonoidHom.comp_apply, gysinBCLine_k0ToG0 σ F hL hs]
  have h1 : pullbackK0 (secOf σ F pr) w =
      pullbackK0 (inv (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι ≫ pr))
        (pullbackK0 (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι) w) := by
    rw [pullbackK0_comp_apply]; rfl
  rw [h1, ARRG45C.k0ToG0_pullbackK0 (inv (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι ≫ pr))]
  exact (DFunLike.congr_fun (ARRG45C.flatPullbackG0_iso_eq_finitePushforward_inv
    (asIso (pullback.fst F (sectionEvaluationIdealSheaf σ).subschemeι ≫ pr)).symm) _).symm


-- @@ L490-491 verbatim
variable {D : Scheme.{u}} [IsLocallyNoetherian D] (ε : D ⟶ M) [IsClosedImmersion ε]
  (hker : ε.ker = (sectionEvaluationIdealSheaf σ).subschemeι.ker)


-- @@ L493-495 verbatim
/-- `D ≅ V(σ)` over `M`, for a closed immersion `ε` with the same ideal. -/
def kappa : D ⟶ (sectionEvaluationIdealSheaf σ).subscheme :=
  IsClosedImmersion.lift (sectionEvaluationIdealSheaf σ).subschemeι ε hker.ge


-- @@ L497-498 verbatim
theorem kappa_fac : kappa σ ε hker ≫ (sectionEvaluationIdealSheaf σ).subschemeι = ε :=
  IsClosedImmersion.lift_fac _ _ _


-- @@ L500-502 verbatim
instance kappa_isIso : IsIso (kappa σ ε hker) :=
  IsClosedImmersion.isIso_of_ker_eq ε (sectionEvaluationIdealSheaf σ).subschemeι _
    (kappa_fac σ ε hker) hker


-- @@ L504-506 verbatim
/-- **The Gysin map `D^! : G₀(M) → G₀(D)`** of the Cartier divisor `D = V(σ)`. -/
def gysD (hL : HasConstantRank M L 1) : G0 M →+ G0 D :=
  (finitePushforward (inv (kappa σ ε hker))).comp (gysinLine σ hL)


-- @@ L508-519 verbatim
/-- **(1) (AR8 item 5 analogue)**: `D^! ∘ k0ToG0_M = k0ToG0_D ∘ ε^*` for a regular section. -/
theorem gysD_k0ToG0 (hL : HasConstantRank M L 1) (hreg : SectionIsRegular σ) (m : K0 M) :
    gysD σ ε hker hL (k0ToG0 M m) = k0ToG0 D (pullbackK0 ε m) := by
  haveI : IsLocallyNoetherian (sectionEvaluationIdealSheaf σ).subscheme :=
    CIIL3B.isLocallyNoetherian_subscheme _
  rw [gysD, AddMonoidHom.comp_apply, gysinLine_k0ToG0 σ hL hreg]
  have hε : pullbackK0 ε m = pullbackK0 (kappa σ ε hker)
      (pullbackK0 (sectionEvaluationIdealSheaf σ).subschemeι m) := by
    rw [pullbackK0_comp_apply, kappa_fac]
  rw [hε, ARRG45C.k0ToG0_pullbackK0 (kappa σ ε hker)]
  exact (DFunLike.congr_fun
    (ARRG45C.flatPullbackG0_iso_eq_finitePushforward_inv (asIso (kappa σ ε hker))) _).symm


-- @@ L521-538 verbatim
/-- **(2) (AR8 item 4 + AR10, all classes)**: `D^! ∘ F_* = s_D* ∘ r^!` on all of `G₀(W)`, for
any section `s_D : Z ⟶ D` with `s_D ≫ ε = s ≫ F`. -/
theorem gysD_comp_finitePushforward (hL : HasConstantRank M L 1) (sD : Z ⟶ D) [IsFinite sD]
    (hzs : sD ≫ ε = secOf σ F pr ≫ F) :
    (gysD σ ε hker hL).comp (finitePushforward F) =
      (finitePushforward sD).comp (rLine σ F pr hL) := by
  haveI := isLocallyNoetherian_fibre (I := sectionEvaluationIdealSheaf σ) F
  haveI : IsLocallyNoetherian (sectionEvaluationIdealSheaf σ).subscheme :=
    CIIL3B.isLocallyNoetherian_subscheme _
  rw [gysD, rLine, AddMonoidHom.comp_assoc, gysinLine_comp_finitePushforward,
    ← AddMonoidHom.comp_assoc, ← AddMonoidHom.comp_assoc, ← ARRG45C.finitePushforward_comp,
    ← ARRG45C.finitePushforward_comp]
  congr 2
  rw [← cancel_mono ε, Category.assoc, Category.assoc, hzs]
  have h1 : inv (kappa σ ε hker) ≫ ε = (sectionEvaluationIdealSheaf σ).subschemeι := by
    rw [IsIso.inv_comp_eq, kappa_fac]
  rw [h1, ← Category.assoc, fst_pr_secOf]
  exact pullback.condition.symm


-- @@ L540-540 verbatim
end Fibre


-- @@ L542-542 verbatim
/-! ### Sections of the deformation's `W → Z`, and transfer along equal kernels -/


-- @@ L544-544 verbatim
section Sections


-- @@ L546-546 verbatim
open SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation

-- @@ L547-547 verbatim
open SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.GlobalSubscheme

-- @@ L548-548 verbatim
open SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.SubschemeProductGlobal


-- @@ L550-550 verbatim
variable (Y : Scheme.{u}) (J : Y.IdealSheafData)


-- @@ L552-555 verbatim
/-- `W = Z × ℙ¹ → Z` is separated (base change of `ℙ¹_ℤ → Spec ℤ`). -/
instance isSeparated_totalToClosedBase : IsSeparated (totalToClosedBase Y J) :=
  MorphismProperty.of_isPullback (P := @IsSeparated) (isPullback_totalIntegerP1 Y J).flip
    inferInstance


-- @@ L557-561 verbatim
/-- **Every section of `W = Z × ℙ¹ → Z` is a closed immersion** (G2GC2 remainder 3). -/
theorem isClosedImmersion_of_section (s : J.subscheme ⟶ subschemeTotalGlobal Y J)
    (hs : s ≫ totalToClosedBase Y J = 𝟙 J.subscheme) : IsClosedImmersion s := by
  haveI : IsClosedImmersion (s ≫ totalToClosedBase Y J) := by rw [hs]; infer_instance
  exact IsClosedImmersion.of_comp s (totalToClosedBase Y J)


-- @@ L563-566 verbatim
instance secInfG_isClosedImmersion : IsClosedImmersion (ARRRIG.secInfG Y J) :=
  isClosedImmersion_of_section Y J _ (by
    rw [ARRRIG.secInfG, Category.assoc, ← totalIsoIntegerP1Product_fst, Iso.inv_hom_id_assoc]
    exact CategoryTheory.Limits.prod.lift_fst _ _)


-- @@ L568-568 verbatim
end Sections


-- @@ L570-570 verbatim
section Transfer


-- @@ L572-573 verbatim
variable {M W Z A B : Scheme.{u}} (F : W ⟶ M) (pr : W ⟶ Z) (ι : A ⟶ M) (ε : B ⟶ M)
  [IsClosedImmersion ι] [IsClosedImmersion ε]


-- @@ L575-591 verbatim
/-- The section `inv (η ≫ pr) ≫ η` only depends on the ideal of the divisor. -/
theorem inv_fst_pr_eq_of_ker_eq (hker : ι.ker = ε.ker) [IsIso (pullback.fst F ε ≫ pr)]
    [IsIso (pullback.fst F ι ≫ pr)] :
    inv (pullback.fst F ι ≫ pr) ≫ pullback.fst F ι = inv (pullback.fst F ε ≫ pr) ≫ pullback.fst F ε := by
  let ψ : A ⟶ B := IsClosedImmersion.lift ε ι hker.symm.le
  have hψ : ψ ≫ ε = ι := IsClosedImmersion.lift_fac _ _ _
  haveI : IsIso ψ := IsClosedImmersion.isIso_of_ker_eq ι ε ψ hψ hker
  let k : pullback F ι ⟶ pullback F ε :=
    pullback.map F ι F ε (𝟙 W) ψ (𝟙 M) (by simp) (by rw [hψ]; simp)
  haveI : IsIso k := by
    dsimp only [k]
    infer_instance
  have hk : k ≫ pullback.fst F ε = pullback.fst F ι :=
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  rw [IsIso.inv_comp_eq]
  conv_rhs => rw [← hk]
  rw [Category.assoc k, Category.assoc k, IsIso.hom_inv_id_assoc, hk]


-- @@ L593-593 verbatim
end Transfer


-- @@ L595-595 verbatim
/-! ### The two fibres of the deformation space -/


-- @@ L597-597 verbatim
section Deformation


-- @@ L599-599 verbatim
open SchemeNormalCone.AlgebraicGeometry SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation

-- @@ L600-600 verbatim
open SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.GlobalSubscheme

-- @@ L601-601 verbatim
open SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.SubschemeProductGlobal

-- @@ L602-602 verbatim
open KSpecialization.ARRG45


-- @@ L604-604 verbatim
variable (Y : Scheme.{u}) (J : Y.IdealSheafData) (k : Type u) [CommRing k] (φ : k →+* Γ(Y, ⊤))


-- @@ L606-610 verbatim
@[reassoc]
theorem lineTι_toBase :
    GlobalCompletion.lineTι Y J ≫ GlobalCompletion.totalGlobalToBase Y J =
      DeformationSpace.toBase Y ⊥ :=
  pushout.inr_desc _ _ _


-- @@ L612-613 verbatim
/-- The zero section `s₀ = subS ≫ subschemeTιGlobal` of `W = Z × ℙ¹ → Z`. -/
abbrev sec0 : J.subscheme ⟶ subschemeTotalGlobal Y J := subS Y J k φ ≫ subschemeTιGlobal Y J


-- @@ L615-616 verbatim
/-- The fibre embedding `M₀ = Y ↪ M` (`= fibreιGlobal 0`). -/
abbrev eps0 : Y ⟶ GlobalCompletion.totalGlobal Y J := lineS Y k φ ≫ GlobalCompletion.lineTι Y J


-- @@ L618-619 verbatim
theorem sec0_pr : sec0 Y J k φ ≫ totalToClosedBase Y J = 𝟙 _ := by
  rw [Category.assoc, subschemeTι_totalToClosedBase, subS_polynomialToClosedBase]


-- @@ L621-623 verbatim
theorem sec0_F : sec0 Y J k φ ≫ subschemeTotalGlobalι Y J = J.subschemeι ≫ eps0 Y J k φ := by
  rw [Category.assoc, subschemeTιGlobal_totalGlobalι, ← Category.assoc, subS_subschemeToLine,
    Category.assoc]


-- @@ L625-627 verbatim
/-- The inverse of `W ×_M M₀ → Z`. -/
def fibre0Lift : J.subscheme ⟶ pullback (subschemeTotalGlobalι Y J) (eps0 Y J k φ) :=
  pullback.lift (sec0 Y J k φ) J.subschemeι (sec0_F Y J k φ)


-- @@ L629-659 verbatim
/-- **`W ∩ M₀ ≅ Z`**: the fibre product `W ×_M M₀` maps isomorphically onto `Z` (it is `Z × {0}`). -/
theorem isIso_fst_pr_zero :
    IsIso (pullback.fst (subschemeTotalGlobalι Y J) (eps0 Y J k φ) ≫ totalToClosedBase Y J) := by
  have hS : lineS Y k φ ≫ DeformationSpace.toBase Y ⊥ = 𝟙 Y := lineS_lineπ Y k φ
  refine ⟨⟨fibre0Lift Y J k φ, ?_, ?_⟩⟩
  · apply pullback.hom_ext
    · -- the `W`-component
      have hsq := (isPullback_lineTι_subschemeTotal Y J)
      let h' : pullback (subschemeTotalGlobalι Y J) (eps0 Y J k φ) ⟶ subschemeUGlobal Y J := hsq.lift (pullback.fst (subschemeTotalGlobalι Y J) (eps0 Y J k φ))
        (pullback.snd (subschemeTotalGlobalι Y J) (eps0 Y J k φ) ≫ lineS Y k φ) (by
          rw [pullback.condition, Category.assoc])
      have h1 : h' ≫ subschemeTιGlobal Y J = pullback.fst (subschemeTotalGlobalι Y J) (eps0 Y J k φ) := hsq.lift_fst _ _ _
      have h2 : h' ≫ subschemeToLineGlobal Y J = pullback.snd (subschemeTotalGlobalι Y J) (eps0 Y J k φ) ≫ lineS Y k φ :=
        hsq.lift_snd _ _ _
      have hsl := isPullback_subschemeLine Y J
      have key : h' ≫ polynomialToClosedBase Y J ≫ subS Y J k φ = h' := by
        apply hsl.hom_ext
        · simp only [Category.assoc, subS_subschemeToLine]
          rw [← reassoc_of% hsl.w, reassoc_of% h2, reassoc_of% hS, h2]
        · simp only [Category.assoc, subS_polynomialToClosedBase, Category.comp_id]
      simp only [Category.assoc, fibre0Lift, pullback.lift_fst, Category.id_comp]
      rw [← h1]
      simp only [sec0, Category.assoc, subschemeTι_totalToClosedBase_assoc]
      rw [← Category.assoc (polynomialToClosedBase Y J), ← Category.assoc h', ← Category.assoc h',
        Category.assoc h', key]
    · simp only [Category.assoc, fibre0Lift, pullback.lift_snd, Category.id_comp]
      rw [totalToClosedBase_subschemeι, pullback.condition_assoc]
      simp only [eps0, Category.assoc, lineTι_toBase]
      rw [hS, Category.comp_id]
  · rw [fibre0Lift, ← Category.assoc, pullback.lift_fst]
    exact sec0_pr Y J k φ


-- @@ L661-661 verbatim
end Deformation


-- @@ L663-663 verbatim
/-! ### Assembly on the deformation space: the G-side gates of the mixed transport -/


-- @@ L665-665 verbatim
section Assembly


-- @@ L667-667 verbatim
open SchemeNormalCone.AlgebraicGeometry SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation

-- @@ L668-668 verbatim
open SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.GlobalSubscheme

-- @@ L669-669 verbatim
open SchemeNormalCone.AlgebraicGeometry.ProjectiveCompletionDeformation.SubschemeProductGlobal

-- @@ L670-670 verbatim
open SchemeKTheory.LineBundleDual AlgebraicGeometry.Chow.M7 KSpecialization.ARRG45


-- @@ L672-672 verbatim
variable (Y : Scheme.{u}) (J : Y.IdealSheafData) (k : Type u) [CommRing k] (φ : k →+* Γ(Y, ⊤))


-- @@ L674-681 verbatim
theorem fibre0Lift_inv :
    haveI := isIso_fst_pr_zero Y J k φ
    inv (pullback.fst (subschemeTotalGlobalι Y J) (eps0 Y J k φ) ≫
    totalToClosedBase Y J) = fibre0Lift Y J k φ := by
  haveI := isIso_fst_pr_zero Y J k φ
  refine IsIso.inv_eq_of_inv_hom_id ?_
  rw [fibre0Lift, ← Category.assoc, pullback.lift_fst]
  exact sec0_pr Y J k φ


-- @@ L683-684 verbatim
variable [IsLocallyNoetherian (GlobalCompletion.totalGlobal Y J)]
  [IsLocallyNoetherian (subschemeTotalGlobal Y J)] [IsNoetherian J.subscheme]


-- @@ L686-694 verbatim
/-- `W ∩ V(σ) ≅ Z` for any divisor with the ideal of `M₀`. -/
theorem isIso_fst_pr_of_ker_zero {L : (GlobalCompletion.totalGlobal Y J).Modules}
    [L.IsQuasicoherent] [L.IsFinitePresentation] (σ : tensorUnitSheaf _ ⟶ L)
    [IsClosedImmersion (eps0 Y J k φ)]
    (hker : (eps0 Y J k φ).ker = (sectionEvaluationIdealSheaf σ).subschemeι.ker) :
    IsIso (pullback.fst (subschemeTotalGlobalι Y J) (sectionEvaluationIdealSheaf σ).subschemeι ≫
      totalToClosedBase Y J) := by
  haveI := isIso_fst_pr_zero Y J k φ
  exact CIIL3B.isIso_fst_comp_of_ker_eq _ _ _ (eps0 Y J k φ) hker.symm


-- @@ L696-706 verbatim
/-- The section of the `M₀`-divisor is `s₀ = subS ≫ subschemeTιGlobal`. -/
theorem secOf_zero {L : (GlobalCompletion.totalGlobal Y J).Modules}
    [L.IsQuasicoherent] [L.IsFinitePresentation] (σ : tensorUnitSheaf _ ⟶ L)
    [IsClosedImmersion (eps0 Y J k φ)]
    (hker : (eps0 Y J k φ).ker = (sectionEvaluationIdealSheaf σ).subschemeι.ker) :
    haveI := isIso_fst_pr_of_ker_zero Y J k φ σ hker
    secOf σ (subschemeTotalGlobalι Y J) (totalToClosedBase Y J) = sec0 Y J k φ := by
  haveI := isIso_fst_pr_of_ker_zero Y J k φ σ hker
  haveI := isIso_fst_pr_zero Y J k φ
  rw [secOf, inv_fst_pr_eq_of_ker_eq _ _ _ (eps0 Y J k φ) hker.symm, fibre0Lift_inv, fibre0Lift,
    pullback.lift_fst]


-- @@ L708-716 verbatim
/-- `W ∩ V(σ) ≅ Z` for any divisor with the ideal of the exceptional component `E ⊂ M_∞`. -/
theorem isIso_fst_pr_of_ker_inf {L : (GlobalCompletion.totalGlobal Y J).Modules}
    [L.IsQuasicoherent] [L.IsFinitePresentation] (σ : tensorUnitSheaf _ ⟶ L)
    (hker : (InfinityExceptionalGlobal.componentToTotal Y J).ker =
      (sectionEvaluationIdealSheaf σ).subschemeι.ker) :
    IsIso (pullback.fst (subschemeTotalGlobalι Y J) (sectionEvaluationIdealSheaf σ).subschemeι ≫
      totalToClosedBase Y J) := by
  haveI := CIIL3B.isIso_fst_comp_totalToClosedBase Y J
  exact CIIL3B.isIso_fst_comp_of_ker_eq _ _ _ _ hker.symm


-- @@ L718-727 verbatim
/-- The section of the exceptional divisor is the section at `∞`, `ARRRIG.secInfG`. -/
theorem secOf_inf {L : (GlobalCompletion.totalGlobal Y J).Modules}
    [L.IsQuasicoherent] [L.IsFinitePresentation] (σ : tensorUnitSheaf _ ⟶ L)
    (hker : (InfinityExceptionalGlobal.componentToTotal Y J).ker =
      (sectionEvaluationIdealSheaf σ).subschemeι.ker) :
    haveI := isIso_fst_pr_of_ker_inf Y J σ hker
    secOf σ (subschemeTotalGlobalι Y J) (totalToClosedBase Y J) = ARRRIG.secInfG Y J := by
  haveI := isIso_fst_pr_of_ker_inf Y J σ hker
  rw [secOf]
  exact KSpecialization.ARRHBCP.inv_comp_fst_eq_secInf Y J _ hker.symm


-- @@ L729-752 verbatim
/-- **`G₀`-rigidity of the two fibre restrictions on `W = Z × ℙ¹`** (C2 on the actual deformation
space): `r₀^! = r₁^!` as soon as the two pulled-back twists agree in `K₀(W)`. -/
theorem rLine_rigid {L₀ L₁ : (GlobalCompletion.totalGlobal Y J).Modules}
    [L₀.IsQuasicoherent] [L₀.IsFinitePresentation] [L₁.IsQuasicoherent] [L₁.IsFinitePresentation]
    (σ₀ : tensorUnitSheaf _ ⟶ L₀) (σ₁ : tensorUnitSheaf _ ⟶ L₁)
    (hL₀ : HasConstantRank _ L₀ 1) (hL₁ : HasConstantRank _ L₁ 1)
    [IsIso (pullback.fst (subschemeTotalGlobalι Y J) (sectionEvaluationIdealSheaf σ₀).subschemeι ≫
      totalToClosedBase Y J)]
    [IsIso (pullback.fst (subschemeTotalGlobalι Y J) (sectionEvaluationIdealSheaf σ₁).subschemeι ≫
      totalToClosedBase Y J)]
    (htw : pullbackK0 (subschemeTotalGlobalι Y J) (k0ClassOf _ (lineBundleDual _ L₀)
        (isFiniteLocallyFree_dual hL₀)) =
      pullbackK0 (subschemeTotalGlobalι Y J) (k0ClassOf _ (lineBundleDual _ L₁)
        (isFiniteLocallyFree_dual hL₁))) :
    rLine σ₀ (subschemeTotalGlobalι Y J) (totalToClosedBase Y J) hL₀ =
      rLine σ₁ (subschemeTotalGlobalι Y J) (totalToClosedBase Y J) hL₁ := by
  haveI := (G2GC2.deformationFrame Y J).isNoetherian_scheme
  refine rigid_of_section (G2GC2.piW Y J)
    (finitePushforward (secOf σ₀ (subschemeTotalGlobalι Y J) (totalToClosedBase Y J)))
    (finitePushforward (secOf σ₁ (subschemeTotalGlobalι Y J) (totalToClosedBase Y J))) _ _ _
    (G2GC2.piW_comp_section Y J _ (secOf_pr _ _ _))
    (G2GC2.piW_comp_section Y J _ (secOf_pr _ _ _))
    (secOf_comp_rLine σ₀ _ _ hL₀) ?_
  rw [secOf_comp_rLine σ₁ _ _ hL₁, htw]


-- @@ L754-764 verbatim
/-- The twist comparison `htw` of `rLine_rigid` follows from an isomorphism of the two pulled-back
dual lines on `W` (both are `𝒪(-1)` of `Z × ℙ¹`). -/
theorem htw_of_iso {W M : Scheme.{u}} [IsLocallyNoetherian M] (F : W ⟶ M) {L₀ L₁ : M.Modules}
    [L₀.IsQuasicoherent] [L₀.IsFinitePresentation] [L₁.IsQuasicoherent] [L₁.IsFinitePresentation]
    (hL₀ : HasConstantRank M L₀ 1) (hL₁ : HasConstantRank M L₁ 1)
    (e : (Scheme.Modules.pullback F).obj (lineBundleDual M L₀) ≅
      (Scheme.Modules.pullback F).obj (lineBundleDual M L₁)) :
    pullbackK0 F (k0ClassOf M (lineBundleDual M L₀) (isFiniteLocallyFree_dual hL₀)) =
      pullbackK0 F (k0ClassOf M (lineBundleDual M L₁) (isFiniteLocallyFree_dual hL₁)) := by
  rw [pullbackK0_classOf, pullbackK0_classOf]
  exact k0ClassOf_iso _ _ _ e


-- @@ L766-811 verbatim
/-- **The G-side gates of `MixedLCI.vanishing_of_mixed` on the actual deformation space.**
`M = totalGlobal Y J`, `W = Z × ℙ¹`, `A = M₀ = Y` (`eps0 = fibreιGlobal 0`), `E ↪ M` any closed
immersion with the ideal of the Cartier divisor `V(σP)` (e.g. the exceptional component), `sE` a
section `Z → E` over `s_∞ = secInfG`.  With `gys₀ = gysD σ₀`, `gysP = gysD σP`, `r₀G = rLine σ₀`,
`r₁G = rLine σP`, `iG = i_*`, `sG = sE_*`, `c = k0ToG0`, `j₀ = eps0^*`, `jP = εE^*`:
`hc₀`, `hcP` (regular sections), `hbc₀G`, `hbcPG` (all classes of `G₀(W)`), and `hrigidG`
(given the twist comparison `htw`). -/
theorem mixedGysin_gates {L₀ LP : (GlobalCompletion.totalGlobal Y J).Modules}
    [L₀.IsQuasicoherent] [L₀.IsFinitePresentation] [LP.IsQuasicoherent] [LP.IsFinitePresentation]
    (σ₀ : tensorUnitSheaf _ ⟶ L₀) (σP : tensorUnitSheaf _ ⟶ LP)
    (hL₀ : HasConstantRank _ L₀ 1) (hLP : HasConstantRank _ LP 1)
    (hreg₀ : SectionIsRegular σ₀) (hregP : SectionIsRegular σP)
    [IsLocallyNoetherian Y] [IsClosedImmersion (eps0 Y J k φ)]
    (hker₀ : (eps0 Y J k φ).ker = (sectionEvaluationIdealSheaf σ₀).subschemeι.ker)
    (hkerP : (InfinityExceptionalGlobal.componentToTotal Y J).ker =
      (sectionEvaluationIdealSheaf σP).subschemeι.ker)
    {E : Scheme.{u}} [IsLocallyNoetherian E] (εE : E ⟶ GlobalCompletion.totalGlobal Y J)
    [IsClosedImmersion εE] (hkerE : εE.ker = (sectionEvaluationIdealSheaf σP).subschemeι.ker)
    (sE : J.subscheme ⟶ E) [IsFinite sE]
    (hzs : sE ≫ εE = ARRRIG.secInfG Y J ≫ subschemeTotalGlobalι Y J) :
    haveI := isIso_fst_pr_of_ker_zero Y J k φ σ₀ hker₀
    haveI := isIso_fst_pr_of_ker_inf Y J σP hkerP
    (∀ m, gysD σ₀ (eps0 Y J k φ) hker₀ hL₀ (k0ToG0 _ m) = k0ToG0 Y (pullbackK0 (eps0 Y J k φ) m)) ∧
    (∀ m, gysD σP εE hkerE hLP (k0ToG0 _ m) = k0ToG0 E (pullbackK0 εE m)) ∧
    (∀ v, gysD σ₀ (eps0 Y J k φ) hker₀ hL₀ (finitePushforward (subschemeTotalGlobalι Y J) v) =
      finitePushforward J.subschemeι
        (rLine σ₀ (subschemeTotalGlobalι Y J) (totalToClosedBase Y J) hL₀ v)) ∧
    (∀ v, gysD σP εE hkerE hLP (finitePushforward (subschemeTotalGlobalι Y J) v) =
      finitePushforward sE (rLine σP (subschemeTotalGlobalι Y J) (totalToClosedBase Y J) hLP v)) ∧
    (pullbackK0 (subschemeTotalGlobalι Y J) (k0ClassOf _ (lineBundleDual _ L₀)
        (isFiniteLocallyFree_dual hL₀)) =
      pullbackK0 (subschemeTotalGlobalι Y J) (k0ClassOf _ (lineBundleDual _ LP)
        (isFiniteLocallyFree_dual hLP)) →
      ∀ v, rLine σ₀ (subschemeTotalGlobalι Y J) (totalToClosedBase Y J) hL₀ v =
        rLine σP (subschemeTotalGlobalι Y J) (totalToClosedBase Y J) hLP v) := by
  haveI := isIso_fst_pr_of_ker_zero Y J k φ σ₀ hker₀
  haveI := isIso_fst_pr_of_ker_inf Y J σP hkerP
  refine ⟨gysD_k0ToG0 σ₀ _ hker₀ hL₀ hreg₀, gysD_k0ToG0 σP εE hkerE hLP hregP, fun v => ?_,
    fun v => ?_, fun htw v => ?_⟩
  · have h := gysD_comp_finitePushforward σ₀ (subschemeTotalGlobalι Y J) (totalToClosedBase Y J)
      (eps0 Y J k φ) hker₀ hL₀ J.subschemeι (by rw [secOf_zero Y J k φ σ₀ hker₀, sec0_F])
    exact DFunLike.congr_fun h v
  · have h := gysD_comp_finitePushforward σP (subschemeTotalGlobalι Y J) (totalToClosedBase Y J)
      εE hkerE hLP sE (by rw [secOf_inf Y J σP hkerP, hzs])
    exact DFunLike.congr_fun h v
  · exact DFunLike.congr_fun (rLine_rigid Y J σ₀ σP hL₀ hLP htw) v


-- @@ L813-832 verbatim
/-- **Mixed base change at `M₀` for every `K₀`-class pushed from `W`** (`hmix` of
`MixedLCI.hbc₀_of_mixed`): if `Fp w ∈ K₀(M)` has `G₀`-class `F_*[w]` (B3 `k0ToG0_regPush`), then
`[j₀^* Fp w] = i_*[s₀^* w]` in `G₀(A)`.  No regularity of `M`, `W`, `Z`. -/
theorem hmix_zero {L₀ : (GlobalCompletion.totalGlobal Y J).Modules}
    [L₀.IsQuasicoherent] [L₀.IsFinitePresentation] (σ₀ : tensorUnitSheaf _ ⟶ L₀)
    (hL₀ : HasConstantRank _ L₀ 1) (hreg₀ : SectionIsRegular σ₀)
    [IsLocallyNoetherian Y] [IsClosedImmersion (eps0 Y J k φ)]
    (hker₀ : (eps0 Y J k φ).ker = (sectionEvaluationIdealSheaf σ₀).subschemeι.ker)
    (hs₀ : Mono (KSpecialization.AR7R.pullbackSection (subschemeTotalGlobalι Y J) (dualEval σ₀)))
    (w : K0 (subschemeTotalGlobal Y J)) (m : K0 (GlobalCompletion.totalGlobal Y J))
    (hm : k0ToG0 _ m = finitePushforward (subschemeTotalGlobalι Y J) (k0ToG0 _ w)) :
    k0ToG0 Y (pullbackK0 (eps0 Y J k φ) m) =
      finitePushforward J.subschemeι (k0ToG0 J.subscheme (pullbackK0 (sec0 Y J k φ) w)) := by
  haveI := isIso_fst_pr_of_ker_zero Y J k φ σ₀ hker₀
  rw [← gysD_k0ToG0 σ₀ (eps0 Y J k φ) hker₀ hL₀ hreg₀, hm]
  have h := gysD_comp_finitePushforward σ₀ (subschemeTotalGlobalι Y J) (totalToClosedBase Y J)
    (eps0 Y J k φ) hker₀ hL₀ J.subschemeι (by rw [secOf_zero Y J k φ σ₀ hker₀, sec0_F])
  rw [← AddMonoidHom.comp_apply, h, AddMonoidHom.comp_apply,
    rLine_k0ToG0 σ₀ (subschemeTotalGlobalι Y J) (totalToClosedBase Y J) hL₀ hs₀,
    secOf_zero Y J k φ σ₀ hker₀]


-- @@ L834-857 verbatim
/-- **Mixed base change at `E ⊂ M_∞` for every `K₀`-class pushed from `W`**:
`[ε^* Fp w] = s_E*[s_∞^* w]` in `G₀(E)` (the `G₀` content of `hbcP`, without `K₀(E) = G₀(E)`).
`hsP` holds for the exceptional divisor by `ARRHS.mono_pullbackSection_exceptional`. -/
theorem hmix_inf {LP : (GlobalCompletion.totalGlobal Y J).Modules}
    [LP.IsQuasicoherent] [LP.IsFinitePresentation] (σP : tensorUnitSheaf _ ⟶ LP)
    (hLP : HasConstantRank _ LP 1) (hregP : SectionIsRegular σP)
    (hkerP : (InfinityExceptionalGlobal.componentToTotal Y J).ker =
      (sectionEvaluationIdealSheaf σP).subschemeι.ker)
    (hsP : Mono (KSpecialization.AR7R.pullbackSection (subschemeTotalGlobalι Y J) (dualEval σP)))
    {E : Scheme.{u}} [IsLocallyNoetherian E] (εE : E ⟶ GlobalCompletion.totalGlobal Y J)
    [IsClosedImmersion εE] (hkerE : εE.ker = (sectionEvaluationIdealSheaf σP).subschemeι.ker)
    (sE : J.subscheme ⟶ E) [IsFinite sE]
    (hzs : sE ≫ εE = ARRRIG.secInfG Y J ≫ subschemeTotalGlobalι Y J)
    (w : K0 (subschemeTotalGlobal Y J)) (m : K0 (GlobalCompletion.totalGlobal Y J))
    (hm : k0ToG0 _ m = finitePushforward (subschemeTotalGlobalι Y J) (k0ToG0 _ w)) :
    k0ToG0 E (pullbackK0 εE m) =
      finitePushforward sE (k0ToG0 J.subscheme (pullbackK0 (ARRRIG.secInfG Y J) w)) := by
  haveI := isIso_fst_pr_of_ker_inf Y J σP hkerP
  rw [← gysD_k0ToG0 σP εE hkerE hLP hregP, hm]
  have h := gysD_comp_finitePushforward σP (subschemeTotalGlobalι Y J) (totalToClosedBase Y J)
    εE hkerE hLP sE (by rw [secOf_inf Y J σP hkerP, hzs])
  rw [← AddMonoidHom.comp_apply, h, AddMonoidHom.comp_apply,
    rLine_k0ToG0 σP (subschemeTotalGlobalι Y J) (totalToClosedBase Y J) hLP hsP,
    secOf_inf Y J σP hkerP]


-- @@ L859-859 verbatim
end Assembly


-- @@ L861-861 verbatim
end KSpecialization.G2GC1
