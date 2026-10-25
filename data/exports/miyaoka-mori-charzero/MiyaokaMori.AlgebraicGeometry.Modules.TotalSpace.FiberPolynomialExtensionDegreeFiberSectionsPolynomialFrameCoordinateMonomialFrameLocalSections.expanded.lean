import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialConstants
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackFrameRankOne
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnitOpenImmersion


-- @@ L6-22 verbatim
/-! # Local sections pulled back to global sections of a fibre

Glue for the restriction of the monomials `c·ξ^q` to a fibre. Everything here is at the variable level.

Setting: `f : X ⟶ Y`, `N : Y.Modules`, an open `U ⊆ Y` such that `f` lands in `U` (`h : ⊤ ≤ f ⁻¹ᵁ U`).
* `pullbackTopSection f N h s ∈ Γ(f^*N, ⊤)`: the pullback of a *local* section `s ∈ Γ(N, U)`, i.e. the unit
  section `unit_N.app U s ∈ Γ(f^*N, f⁻¹U)` restricted to `⊤`.
* `pullbackTopSection_res_top`: for a global section it is the usual pullback `sectionPullbackAlong f s`.
* `pullbackTopSection_smul`: it is linear, `f^*(r • s) = f^♯(r) • f^*s` with `f^♯ = f.appLE U ⊤ h`.
* `isFrame_pullbackTopSection`: the pullback of a frame is a (global) frame (`isFrame_unitSec_pullback`).
* `IsFrame.topTrivialization_inv_app_smul`: the trivialization `τ := (topTrivialization e)⁻¹ : M ≅ O_X` of a
  global frame `e` reads off the coordinate, `τ(r • e) = r`.
* `appLE_comp_fiber_eq_fiberResidueConstants`: for the fiber `F = f.fiber y`, `i = f.fiberι y`, and a function
  `r ∈ Γ(Y, U)` with `y ∈ U`: `(i ≫ f)^♯(r) ∈ Γ(F, ⊤)` is the constant `const(r(y))`, where
  `r(y) := ΓSpecIso (g^♯ r) ∈ κ(y)` is the value of `r` at `y` (`g = Y.fromSpecResidueField y`,
  `Scheme.Hom.fiber_fac`, `fiberResidueConstants`).
-/


-- @@ L24-24 verbatim
set_option autoImplicit false

-- @@ L25-25 verbatim
set_option maxHeartbeats 400000


-- @@ L27-27 verbatim
universe u


-- @@ L29-29 verbatim
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

-- @@ L30-30 verbatim
open scoped AlgebraicGeometry


-- @@ L32-32 verbatim
noncomputable section


-- @@ L34-34 verbatim
namespace AlgebraicGeometry.Scheme.Modules


-- @@ L36-36 verbatim
variable {X Y : AlgebraicGeometry.Scheme.{u}}


-- @@ L38-42 verbatim
/-- The pullback of a local section `s ∈ Γ(N, U)` along `f : X ⟶ Y` landing in `U` (`⊤ ≤ f⁻¹U`), as a
global section of `f^*N`: the unit section `unit_N.app U s ∈ Γ(f^*N, f⁻¹U)`, restricted to `⊤`. -/
def pullbackTopSection (f : X ⟶ Y) (N : Y.Modules) {U : Y.Opens} (h : ⊤ ≤ f ⁻¹ᵁ U) (s : Γ(N, U)) :
    Γ((pullback f).obj N, ⊤) :=
  ((pullback f).obj N).res h (((pullbackPushforwardAdjunction f).unit.app N).app U s)


-- @@ L44-59 verbatim
/-- On (the restriction of) a global section, `pullbackTopSection` is the usual pullback
`sectionPullbackAlong f s = unit_N.app ⊤ s`. -/
theorem pullbackTopSection_res_top (f : X ⟶ Y) (N : Y.Modules) {U : Y.Opens} (h : ⊤ ≤ f ⁻¹ᵁ U)
    (s : Γ(N, ⊤)) :
    pullbackTopSection f N h (N.res le_top s) = sectionPullbackAlong f s := by
  unfold pullbackTopSection
  have h1 := unit_app_map f N (le_top : U ≤ ⊤) s
  change ((pullback f).obj N).res h (((pullbackPushforwardAdjunction f).unit.app N).app U
    (N.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s)) = _
  rw [h1]
  have hle : f ⁻¹ᵁ U ≤ f ⁻¹ᵁ ⊤ := by
    intro x _
    trivial
  change ((pullback f).obj N).res h (((pullback f).obj N).res hle
    (((pullbackPushforwardAdjunction f).unit.app N).app ⊤ s)) = _
  exact (res_res ((pullback f).obj N) h hle _).trans (res_self ((pullback f).obj N) _)


-- @@ L61-67 verbatim
/-- `pullbackTopSection` is linear: `f^*(r • s) = f^♯(r) • f^*(s)`, with `f^♯ := f.appLE U ⊤ h`. -/
theorem pullbackTopSection_smul (f : X ⟶ Y) (N : Y.Modules) {U : Y.Opens} (h : ⊤ ≤ f ⁻¹ᵁ U)
    (r : Γ(Y, U)) (s : Γ(N, U)) :
    pullbackTopSection f N h (r • s) = f.appLE U ⊤ h r • pullbackTopSection f N h s := by
  unfold pullbackTopSection
  rw [Hom.app_smul]
  exact res_smul ((pullback f).obj N) h (f.app U r) _


-- @@ L69-73 verbatim
/-- The pullback of a frame `e` of `N` on `U` along `f` landing in `U` is a global frame of `f^*N`. -/
theorem isFrame_pullbackTopSection (f : X ⟶ Y) (N : Y.Modules) {U : Y.Opens} (h : ⊤ ≤ f ⁻¹ᵁ U)
    {e : Γ(N, U)} (he : IsFrame N U e) :
    IsFrame ((pullback f).obj N) ⊤ (pullbackTopSection f N h e) :=
  (MiyaokaMori.DualPullback.isFrame_unitSec_pullback f N he).restrict h


-- @@ L75-84 verbatim
/-- The trivialization `(topTrivialization e)⁻¹ : M ⟶ O_X` of a global frame reads off the coordinate:
`τ(r • e) = r`. -/
theorem IsFrame.topTrivialization_inv_app_smul {M : X.Modules} {e : Γ(M, ⊤)} (hf : IsFrame M ⊤ e)
    (r : Γ(X, ⊤)) :
    AlgebraicGeometry.Scheme.Modules.Hom.app hf.topTrivialization.inv ⊤ (r • e) = r := by
  have h1 : AlgebraicGeometry.Scheme.Modules.Hom.app hf.topTrivialization.hom ⊤ r = r • e := by
    refine (homOfSection_app M e ⊤ r).trans ?_
    exact congrArg (fun z => r • z) (res_self M e)
  rw [← h1]
  exact modIso_inv_app_hom_app hf.topTrivialization ⊤ r


-- @@ L86-93 verbatim
/-- `f` lands in `U` iff every point maps into `U`; for `Y.fromSpecResidueField y` and `y ∈ U` this holds
(`Scheme.fromSpecResidueField_apply`). -/
theorem top_le_preimage_fromSpecResidueField (y : Y) {U : Y.Opens} (hy : y ∈ U) :
    ⊤ ≤ (Y.fromSpecResidueField y) ⁻¹ᵁ U := by
  intro x _
  show (Y.fromSpecResidueField y).base x ∈ U
  rw [AlgebraicGeometry.Scheme.fromSpecResidueField_apply]
  exact hy


-- @@ L95-100 verbatim
/-- Transport of `appLE` along an equality of morphisms (private copy; several modules have their own). -/
private theorem appLE_congr_hom_mf {f g : X ⟶ Y} (hfg : f = g) (U : Y.Opens)
    (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = g.appLE U V (hfg ▸ e) := by
  subst hfg
  rfl


-- @@ L102-132 verbatim
/-- **The pullback of a function to the fiber is a constant.** For `F = f.fiber y`, `i = f.fiberι y`,
`π_F = f.fiberToSpecResidueField y`, `g = Y.fromSpecResidueField y` (`i ≫ f = π_F ≫ g`), an open `U ∋ y`
and `r ∈ Γ(Y, U)`: `(i ≫ f)^♯(r) = const(r(y))` in `Γ(F, ⊤)`, where `r(y) := ΓSpecIso(g^♯ r) ∈ κ(y)`. -/
theorem appLE_comp_fiber_eq_fiberResidueConstants (f : X ⟶ Y) (y : Y) {U : Y.Opens}
    (h : ⊤ ≤ (f.fiberι y ≫ f) ⁻¹ᵁ U) (hU : ⊤ ≤ (Y.fromSpecResidueField y) ⁻¹ᵁ U) (r : Γ(Y, U)) :
    (f.fiberι y ≫ f).appLE U ⊤ h r =
      f.fiberResidueConstants y ((AlgebraicGeometry.Scheme.ΓSpecIso (Y.residueField y)).hom
        ((Y.fromSpecResidueField y).appLE U ⊤ hU r)) := by
  rw [appLE_congr_hom_mf (AlgebraicGeometry.Scheme.Hom.fiber_fac f y),
    AlgebraicGeometry.Scheme.Hom.comp_appLE]
  change (f.fiberToSpecResidueField y).appLE ((Y.fromSpecResidueField y) ⁻¹ᵁ U) ⊤ _
    ((Y.fromSpecResidueField y).app U r) = _
  have h2 := AlgebraicGeometry.Scheme.Hom.map_appLE (f.fiberToSpecResidueField y)
    (U := ⊤) (V := ⊤) (le_top : (⊤ : (f.fiber y).Opens) ≤ (f.fiberToSpecResidueField y) ⁻¹ᵁ ⊤)
    (homOfLE hU).op
  have h3 := congrArg (fun φ => φ.hom ((Y.fromSpecResidueField y).app U r)) h2
  refine Eq.trans ?_ (h3.symm.trans ?_)
  · rfl
  · have h4 : (f.fiberToSpecResidueField y).appLE ⊤ ⊤
        (le_top : (⊤ : (f.fiber y).Opens) ≤ (f.fiberToSpecResidueField y) ⁻¹ᵁ ⊤) =
        (f.fiberToSpecResidueField y).app ⊤ :=
      AlgebraicGeometry.Scheme.Hom.appLE_eq_app (f.fiberToSpecResidueField y)
    unfold AlgebraicGeometry.Scheme.Hom.fiberResidueConstants
    change (f.fiberToSpecResidueField y).appLE ⊤ ⊤ _
        ((AlgebraicGeometry.Spec (Y.residueField y)).presheaf.map (homOfLE hU).op
          ((Y.fromSpecResidueField y).app U r)) =
      (f.fiberToSpecResidueField y).appTop ((AlgebraicGeometry.Scheme.ΓSpecIso (Y.residueField y)).inv
        ((AlgebraicGeometry.Scheme.ΓSpecIso (Y.residueField y)).hom
          ((Y.fromSpecResidueField y).appLE U ⊤ hU r)))
    rw [h4, Iso.hom_inv_id_apply]
    rfl


-- @@ L134-134 verbatim
end AlgebraicGeometry.Scheme.Modules


-- @@ L136-136 verbatim
end
