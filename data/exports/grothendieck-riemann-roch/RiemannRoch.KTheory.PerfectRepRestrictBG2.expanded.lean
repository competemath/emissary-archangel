/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import RiemannRoch.KTheory.PerfectRepG2
import RiemannRoch.CharacteristicClasses.CartierGysinClosureCIIL3B
import RiemannRoch.CharacteristicClasses.PullbackK0


-- @@ L11-32 verbatim
/-!
# Restriction of perfect classes `repK0` (bricks G2C-K5 / G2K-B4, route B: direct)

For a coherent sheaf `F` of finite bundle dimension on `T` (`PerfectRepG2.Sch.repK0`):

* **(i) flat restriction** (in particular restriction to an open `U ⊂ T`):
  `pullbackK0 f (repK0 F) = repK0 (f^* F)` (`pullbackK0_repK0_of_flat`), and sheaves whose
  pullback is zero restrict to `0` (`pullbackK0_repK0_eq_zero_of_flat`);
* **(ii) restriction to an effective Cartier divisor** `e : D = V(σ) ↪ T`, `σ : 𝒪 ⟶ L`, `L` a line
  bundle, when the Koszul map `σ_F : L⁻¹ ⊗ F ⟶ F` is a monomorphism and `σ_E` is a monomorphism on
  all finite locally free `E` (e.g. `σ` regular): `pullbackK0 e (repK0 F) = repK0 (e^* F)`
  (`pullbackK0_repK0_cartier`, `pullbackK0_repK0_cartier_of_regular`).

Route: take any finite bundle resolution of `F`; every syzygy is a subsheaf of a bundle, hence
`σ`-regular, so `e^*` keeps every short exact step exact (`pullback_shortExact_cartier`: right
exactness of the left adjoint `e^*` plus a refinement diagram chase showing that
`coker σ_K → coker σ_E` is a monomorphism, `e^* ≅ e^* coker σ`, and `e_*` reflects monomorphisms on
`V(σ)`-killed sheaves).  The pulled back resolution is a bundle resolution of `e^* F`, so K1's
`repK0_eq_of_rep` concludes.  The target's bundle-dimension bound is derived, not assumed
(`pdLE_of_rep`: a single finite bundle resolution bounds *every* syzygy, Schanuel-style).
No `PrincipalGysin` snake/`cartierGysin` machinery is used.
-/


-- @@ L34-34 verbatim
set_option autoImplicit false

-- @@ L35-35 verbatim
set_option linter.unusedSectionVars false


-- @@ L37-37 verbatim
noncomputable section


-- @@ L39-39 verbatim
universe u v u' v'


-- @@ L41-41 verbatim
open CategoryTheory CategoryTheory.Limits


-- @@ L43-43 verbatim
namespace PerfectRepRestrictBG2


-- @@ L45-45 verbatim
section Abstract


-- @@ L47-47 verbatim
open AbelianResolutionF15


-- @@ L49-49 verbatim
variable {C : Type u} [Category.{v} C] [Abelian C] (S : Setup C)


-- @@ L51-51 verbatim
/-! ## A single bundle resolution bounds every syzygy -/


-- @@ L53-56 verbatim
/-- One syzygy step with kernel of bundle dimension `≤ n` gives bundle dimension `≤ n + 1`. -/
def PdUp (n : ℕ) : Prop :=
  ∀ {K E M : C} {i : K ⟶ E} {g : E ⟶ M}, SES i g → S.P E → S.Q K → S.Q M →
    PdLE S n K → PdLE S (n + 1) M


-- @@ L58-61 verbatim
/-- The kernel of an epimorphism onto a bundle from an object of bundle dimension `≤ n`. -/
def PdKer (n : ℕ) : Prop :=
  ∀ {A B D : C} {a : A ⟶ B} {b : B ⟶ D}, SES a b → S.P D → S.Q A → S.Q B →
    PdLE S n B → PdLE S n A


-- @@ L63-70 verbatim
theorem pdUp_of_pdKer {n : ℕ} (hk : PdKer S n) : PdUp S n := by
  intro K E M i g hs hE hK hM hpK Z hZ
  obtain ⟨K', E', i', g', hs', hE', hK', hZ'⟩ := hZ
  have hQV : S.Q (pullback g g') := S.Q_pullback g g' (S.P_Q hE) (S.P_Q hE') hM
  have s1 := hs.pullbackL g'
  have s2 := hs'.pullbackR g
  have hpV : PdLE S n (pullback g g') := pdLE_ext S s1 hE' hK hQV hpK
  exact hk s2 hE hK' hQV hpV Z hZ'


-- @@ L72-75 verbatim
theorem pdKer_zero : PdKer S 0 := by
  intro A B D a b hs hD hA _ hB
  rw [pdLE_zero_iff] at hB ⊢
  exact S.P_ker hs hB hD hA


-- @@ L77-89 verbatim
theorem pdKer_succ {m : ℕ} (hu : PdUp S m) : PdKer S (m + 1) := by
  intro A B D a b hab hD hQA hQB hpB
  obtain ⟨E2, q, hE2, hq⟩ := S.cover hQB
  haveI := hq
  have hs2 := SES.kernel_of_epi q
  have hQK2 : S.Q (kernel q) := S.Q_kernel q (S.P_Q hE2) hQB
  have hpK2 : PdLE S m (kernel q) := hpB.ker S hs2 hE2 hQK2
  have hsN := hs2.pullbackL a
  have hsC := hab.comp q
  have hPC : S.P (pullback a q) :=
    S.P_ker hsC hE2 hD (S.Q_pullback a q hQA (S.P_Q hE2) hQB)
  have hPN : S.P (pullback q a) := S.P_iso (pullbackSymmetry a q) hPC
  exact hu hsN hPN hQK2 hQA hpK2


-- @@ L91-93 verbatim
theorem pdKer_all : ∀ n, PdKer S n
  | 0 => pdKer_zero S
  | n + 1 => pdKer_succ S (pdUp_of_pdKer S (pdKer_all n))


-- @@ L95-100 verbatim
/-- **A finite bundle resolution bounds the bundle dimension.**  If `M` (in `Q`) admits one
truncated bundle resolution of length `n`, then *every* `n`-th syzygy of `M` is a bundle. -/
theorem pdLE_of_rep : ∀ (n : ℕ) {M : C} {x : K0 S}, S.Q M → Rep S n M x → PdLE S n M
  | 0, M, _, _, ⟨h, _⟩ => pdLE_of_P S 0 M h
  | n + 1, _, _, hM, ⟨_, _, _, _, _, hs, hE, hK, hy, _⟩ =>
    pdUp_of_pdKer S (pdKer_all S n) hs hE hK hM (pdLE_of_rep n hK hy)


-- @@ L102-102 verbatim
/-! ## Transport of resolutions along a functor exact on regular steps -/


-- @@ L104-104 verbatim
variable {C' : Type u'} [Category.{v'} C'] [Abelian C'] (S' : Setup C')


-- @@ L106-122 verbatim
/-- **Transport of truncated resolutions.**  `Φ` sends bundles to bundles, `Q` to `Q`, and short
exact steps `K → E → M` with `E` a bundle and `M` in the class `R` (e.g. `σ`-regular objects) to
short exact sequences; `R` contains the bundles and is closed under subobjects; `φ` is compatible
with bundle classes.  Then resolutions of `R`-objects are transported. -/
theorem rep_map (Φ : C ⥤ C') (φ : K0 S →+ K0 S') (R : C → Prop)
    (hφ : ∀ E (hE : S.P E) (hE' : S'.P (Φ.obj E)), φ (cls S E hE) = cls S' (Φ.obj E) hE')
    (hP : ∀ E, S.P E → S'.P (Φ.obj E)) (hQ : ∀ M, S.Q M → S'.Q (Φ.obj M))
    (hRP : ∀ E, S.P E → R E)
    (hRsub : ∀ {A B D : C} {i : A ⟶ B} {g : B ⟶ D}, SES i g → R B → R A)
    (hses : ∀ {A B D : C} {i : A ⟶ B} {g : B ⟶ D}, SES i g → S.P B → S.Q A → S.Q D → R D →
      SES (Φ.map i) (Φ.map g)) :
    ∀ (n : ℕ) {M : C} {x : K0 S}, S.Q M → R M → Rep S n M x → Rep S' n (Φ.obj M) (φ x)
  | 0, M, _, _, _, ⟨h, hx⟩ => ⟨hP M h, by rw [hx]; exact hφ M h _⟩
  | n + 1, M, _, hM, hR, ⟨K, E, i, g, y, hs, hE, hK, hy, hx⟩ =>
    ⟨Φ.obj K, Φ.obj E, Φ.map i, Φ.map g, φ y, hses hs hE hK hM hR, hP E hE, hQ K hK,
      rep_map Φ φ R hφ hP hQ hRP hRsub hses n hK (hRsub hs (hRP E hE)) hy,
      by rw [hx, map_sub, hφ E hE (hP E hE)]⟩


-- @@ L124-134 verbatim
/-- The transported object has finite bundle dimension. -/
theorem pdLE_map (Φ : C ⥤ C') (φ : K0 S →+ K0 S') (R : C → Prop)
    (hφ : ∀ E (hE : S.P E) (hE' : S'.P (Φ.obj E)), φ (cls S E hE) = cls S' (Φ.obj E) hE')
    (hP : ∀ E, S.P E → S'.P (Φ.obj E)) (hQ : ∀ M, S.Q M → S'.Q (Φ.obj M))
    (hRP : ∀ E, S.P E → R E)
    (hRsub : ∀ {A B D : C} {i : A ⟶ B} {g : B ⟶ D}, SES i g → R B → R A)
    (hses : ∀ {A B D : C} {i : A ⟶ B} {g : B ⟶ D}, SES i g → S.P B → S.Q A → S.Q D → R D →
      SES (Φ.map i) (Φ.map g))
    {d : ℕ} {M : C} (hQM : S.Q M) (hRM : R M) (h : PdLE S d M) : PdLE S' d (Φ.obj M) :=
  pdLE_of_rep S' d (hQ M hQM)
    (rep_map S S' Φ φ R hφ hP hQ hRP hRsub hses d hQM hRM (PerfectRepG2.rep_repK0 S M hQM h))


-- @@ L136-148 verbatim
/-- **Perfect classes are transported.** -/
theorem repK0_map (Φ : C ⥤ C') (φ : K0 S →+ K0 S') (R : C → Prop)
    (hφ : ∀ E (hE : S.P E) (hE' : S'.P (Φ.obj E)), φ (cls S E hE) = cls S' (Φ.obj E) hE')
    (hP : ∀ E, S.P E → S'.P (Φ.obj E)) (hQ : ∀ M, S.Q M → S'.Q (Φ.obj M))
    (hRP : ∀ E, S.P E → R E)
    (hRsub : ∀ {A B D : C} {i : A ⟶ B} {g : B ⟶ D}, SES i g → R B → R A)
    (hses : ∀ {A B D : C} {i : A ⟶ B} {g : B ⟶ D}, SES i g → S.P B → S.Q A → S.Q D → R D →
      SES (Φ.map i) (Φ.map g))
    {d d' : ℕ} {M : C} (hQM : S.Q M) (hRM : R M) (h : PdLE S d M)
    (hQ' : S'.Q (Φ.obj M)) (h' : PdLE S' d' (Φ.obj M)) :
    φ (PerfectRepG2.repK0 S M hQM h) = PerfectRepG2.repK0 S' (Φ.obj M) hQ' h' :=
  (PerfectRepG2.repK0_eq_of_rep S' hQ' h'
    (rep_map S S' Φ φ R hφ hP hQ hRP hRsub hses d hQM hRM (PerfectRepG2.rep_repK0 S M hQM h))).symm


-- @@ L150-150 verbatim
end Abstract


-- @@ L152-152 verbatim
/-! ## A diagram chase: cokernels of a regular twist -/


-- @@ L154-154 verbatim
section Chase


-- @@ L156-156 verbatim
variable {C : Type u} [Category.{v} C] [Abelian C]


-- @@ L158-188 verbatim
/-- Given a morphism of complexes `(f', g') → (f, g)` with exact top row, `f` mono and the
right vertical map `c` mono, the induced map `coker a → coker b` is a monomorphism. -/
theorem mono_cokernel_map {K' E' M' K E M : C} (f' : K' ⟶ E') (g' : E' ⟶ M') (z' : f' ≫ g' = 0)
    (f : K ⟶ E) (g : E ⟶ M) (z : f ≫ g = 0) (a : K' ⟶ K) (b : E' ⟶ E) (c : M' ⟶ M)
    (w1 : a ≫ f = f' ≫ b) (w2 : b ≫ g = g' ≫ c)
    (hex : (ShortComplex.mk f' g' z').Exact) [Mono f] [Mono c] :
    Mono (cokernel.map a b f' f w1) := by
  apply Preadditive.mono_of_cancel_zero
  intro A y hy
  obtain ⟨A1, π1, hπ1, k, hk⟩ := surjective_up_to_refinements_of_epi (cokernel.π a) y
  have hkf : (k ≫ f) ≫ cokernel.π b = 0 := by
    have e1 : cokernel.π a ≫ cokernel.map a b f' f w1 = f ≫ cokernel.π b := by
      simp [cokernel.map]
    rw [Category.assoc, ← e1, ← Category.assoc, ← hk, Category.assoc, hy, comp_zero]
  obtain ⟨A2, π2, hπ2, e', he'⟩ :=
    (ShortComplex.exact_cokernel b).exact_up_to_refinements (k ≫ f) hkf
  have he'0 : e' ≫ g' = 0 := by
    rw [← cancel_mono c, Category.assoc, ← w2, ← Category.assoc]
    rw [← he', zero_comp, Category.assoc, Category.assoc, z, comp_zero, comp_zero]
  obtain ⟨A3, π3, hπ3, k', hk'⟩ := hex.exact_up_to_refinements e' he'0
  have hkk : π3 ≫ π2 ≫ k = k' ≫ a := by
    rw [← cancel_mono f]
    simp only [Category.assoc]
    rw [w1]
    have h1 : π2 ≫ k ≫ f = e' ≫ b := he'
    rw [h1, ← Category.assoc, hk', Category.assoc]
  haveI := hπ1; haveI := hπ2; haveI := hπ3
  rw [← cancel_epi (π3 ≫ π2 ≫ π1), comp_zero]
  simp only [Category.assoc]
  rw [hk, ← Category.assoc π2, ← Category.assoc π3, hkk, Category.assoc, cokernel.condition,
    comp_zero]


-- @@ L190-190 verbatim
end Chase


-- @@ L192-192 verbatim
/-! ## Schemes -/


-- @@ L194-194 verbatim
namespace Sch


-- @@ L196-196 verbatim
open AlgebraicGeometry SchemeKTheory PerfectRepG2.Sch


-- @@ L198-198 verbatim
/-! ### Flat (in particular open) restriction -/


-- @@ L200-200 verbatim
section Flat


-- @@ L202-203 verbatim
variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
  (hX : HasBundleCovers X) (hY : HasBundleCovers Y) (f : X ⟶ Y) [Flat f]


-- @@ L205-208 verbatim
theorem isCoherentLike_pullback {X Y : Scheme.{u}} (f : X ⟶ Y) {F : Y.Modules}
    (hF : IsCoherentLike Y F) : IsCoherentLike X ((Scheme.Modules.pullback f).obj F) := by
  haveI : F.IsFinitePresentation := hF
  exact pullback_isFinitePresentation_global f F


-- @@ L210-223 verbatim
theorem flat_ses {A B D : Y.Modules} {i : A ⟶ B} {g : B ⟶ D}
    (hs : AbelianResolutionF15.SES i g) (hA : IsCoherentLike Y A) (hB : IsCoherentLike Y B)
    (hD : IsCoherentLike Y D) :
    AbelianResolutionF15.SES ((Scheme.Modules.pullback f).map i)
      ((Scheme.Modules.pullback f).map g) := by
  haveI : A.IsFinitePresentation := hA
  haveI : B.IsFinitePresentation := hB
  haveI : D.IsFinitePresentation := hD
  let T : ShortComplex Y.Modules := ShortComplex.mk i g hs.zero
  haveI : T.X₁.IsQuasicoherent := inferInstanceAs A.IsQuasicoherent
  haveI : T.X₂.IsQuasicoherent := inferInstanceAs B.IsQuasicoherent
  haveI : T.X₃.IsQuasicoherent := inferInstanceAs D.IsQuasicoherent
  have h := pullback_map_shortExact_global f T hs.exact
  exact ⟨(T.map (Scheme.Modules.pullback f)).zero, h⟩


-- @@ L225-234 verbatim
/-- The pullback along a flat morphism of a sheaf of bundle dimension `≤ d` has bundle
dimension `≤ d`. -/
theorem pdLE_pullback_of_flat {d : ℕ} {F : Y.Modules} (hF : IsCoherentLike Y F)
    (hd : PdLE hY d F) : PdLE hX d ((Scheme.Modules.pullback f).obj F) :=
  PerfectRepRestrictBG2.pdLE_map (setup Y hY) (setup X hX) (Scheme.Modules.pullback f)
    (pullbackK0 f) (fun _ => True)
    (fun E hE _ => pullbackK0_classOf f E hE)
    (fun E hE => pullback_isFiniteLocallyFree_global f E hE)
    (fun _ hM => isCoherentLike_pullback f hM) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun hs hB hA hD _ => flat_ses f hs hA (hB.isFinitePresentation) hD) hF trivial hd


-- @@ L236-247 verbatim
/-- **(i) Flat restriction commutes with perfect classes.**  For `f` flat (e.g. an open
immersion `U ⟶ T`), `f^* (repK0 F) = repK0 (f^* F)` in `K₀ X`. -/
theorem pullbackK0_repK0_of_flat {d d' : ℕ} (F : Y.Modules) (hF : IsCoherentLike Y F)
    (hd : PdLE hY d F) (hF' : IsCoherentLike X ((Scheme.Modules.pullback f).obj F))
    (hd' : PdLE hX d' ((Scheme.Modules.pullback f).obj F)) :
    pullbackK0 f (repK0 hY F hF hd) = repK0 hX ((Scheme.Modules.pullback f).obj F) hF' hd' :=
  PerfectRepRestrictBG2.repK0_map (setup Y hY) (setup X hX) (Scheme.Modules.pullback f)
    (pullbackK0 f) (fun _ => True)
    (fun E hE _ => pullbackK0_classOf f E hE)
    (fun E hE => pullback_isFiniteLocallyFree_global f E hE)
    (fun _ hM => isCoherentLike_pullback f hM) (fun _ _ => trivial) (fun _ _ => trivial)
    (fun hs hB hA hD _ => flat_ses f hs hA (hB.isFinitePresentation) hD) hF trivial hd hF' hd'


-- @@ L249-256 verbatim
include hX in
/-- Sheaves restricting to zero (e.g. supported off the open `U`) have zero restricted class. -/
theorem pullbackK0_repK0_eq_zero_of_flat {d : ℕ} (F : Y.Modules) (hF : IsCoherentLike Y F)
    (hd : PdLE hY d F) (hZ : IsZero ((Scheme.Modules.pullback f).obj F)) :
    pullbackK0 f (repK0 hY F hF hd) = 0 := by
  rw [pullbackK0_repK0_of_flat hX hY f F hF hd (isCoherentLike_pullback f hF)
    (pdLE_pullback_of_flat hX hY f hF hd)]
  exact repK0_zero hX hZ _ _


-- @@ L258-264 verbatim
/-- Open immersions: the special case of `pullbackK0_repK0_of_flat`. -/
theorem pullbackK0_repK0_of_isOpenImmersion (j : X ⟶ Y) [IsOpenImmersion j] {d d' : ℕ}
    (F : Y.Modules) (hF : IsCoherentLike Y F) (hd : PdLE hY d F)
    (hF' : IsCoherentLike X ((Scheme.Modules.pullback j).obj F))
    (hd' : PdLE hX d' ((Scheme.Modules.pullback j).obj F)) :
    pullbackK0 j (repK0 hY F hF hd) = repK0 hX ((Scheme.Modules.pullback j).obj F) hF' hd' :=
  pullbackK0_repK0_of_flat hX hY j F hF hd hF' hd'


-- @@ L266-266 verbatim
end Flat


-- @@ L268-268 verbatim
/-! ### Restriction to an effective Cartier divisor -/


-- @@ L270-270 verbatim
section Cartier


-- @@ L272-272 verbatim
open KSpecialization KSpecialization.AR7R KSpecialization.AR4 KSpecialization.AR8

-- @@ L273-273 verbatim
open ExactGrothendieck.CartierGysinAR1 ExactGrothendieck.CartierGysinAR8

-- @@ L274-274 verbatim
open SchemeKTheory.LineBundleDual AlgebraicGeometry.Chow.M7


-- @@ L276-277 verbatim
variable {Y : Scheme.{u}} [IsLocallyNoetherian Y] {L : Y.Modules} [L.IsQuasicoherent]
  [L.IsFinitePresentation] (σ : tensorUnitSheaf Y ⟶ L)


-- @@ L279-280 verbatim
set_option quotPrecheck false in
local notation "ιΣ" => (sectionEvaluationIdealSheaf σ).subschemeι

-- @@ L281-282 verbatim
set_option quotPrecheck false in
local notation "TΣ" => tensorSheafLeftFunctor Y (lineBundleDual Y L)

-- @@ L283-284 verbatim
set_option quotPrecheck false in
local notation "sΣ" => sigmaT (lineBundleDual Y L) (dualEval σ)


-- @@ L286-356 verbatim
/-- **Exactness of restriction to `V(σ)` on `σ`-regular steps.**  For a short exact sequence of
coherent sheaves whose quotient is `σ`-regular (`σ_{X₃}` mono), the pullback to the zero scheme
`V(σ)` is short exact. -/
theorem pullback_shortExact_cartier (hL : HasConstantRank Y L 1) (T : ShortComplex Y.Modules)
    (hT : T.ShortExact) (h1 : IsCoherentLike Y T.X₁) (h2 : IsCoherentLike Y T.X₂)
    (hm : Mono (ap TΣ sΣ T.X₃)) :
    (T.map (Scheme.Modules.pullback ιΣ)).ShortExact := by
  have hline : IsLocalLineFrame L := isLocalLineFrame_of_hasConstantRank_one hL
  have hΛ1 : HasConstantRank Y (lineBundleDual Y L) 1 := lineBundleDual_hasConstantRank L hL
  have hΛ : IsFiniteLocallyFree Y (lineBundleDual Y L) := hΛ1.isFiniteLocallyFree
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits Y _ hΛ
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits Y _ hΛ
  have hI := locallyPrincipal_sectionEvaluationIdealSheaf σ hline
  have hB := ar7Bridge σ hline
  let adj := Scheme.Modules.pullbackPushforwardAdjunction ιΣ
  haveI : PreservesColimitsOfSize.{0, 0} (Scheme.Modules.pullback ιΣ) :=
    adj.leftAdjoint_preservesColimits
  haveI := hT.mono_f
  haveI := hT.epi_g
  have ex : (T.map (Scheme.Modules.pullback ιΣ)).Exact :=
    hT.exact.map_of_epi_of_preservesCokernel _ inferInstance inferInstance
  -- `e^*` kills `σ`, hence `e^* X ≅ e^* coker σ_X`
  have hπ : ∀ X : Y.Modules,
      IsIso ((Scheme.Modules.pullback ιΣ).map (cokernel.π (ap TΣ sΣ X))) := fun X =>
    ExactGrothendieck.CartierGysinAR8.isIso_map_cokernel_π_of_map_eq_zero _ _
      (map_ap_eq_zero_of_adj adj X (hB.killed_of_idealKills _ (idealKills_pushforward _ _)))
  -- cokernels of `σ` on coherent sheaves are killed, so the unit is an isomorphism there
  have hunit : ∀ X : Y.Modules, IsCoherentLike Y X →
      IsIso (ProjectionFormula.adjUnit ιΣ (cokernel (ap TΣ sΣ X))) := fun X hX => by
    have hc : IsCoherentLike Y (cokernel (ap TΣ sΣ X)) :=
      (kerCokerClosed_isCoherentLike (Y := Y)).cokernel _
        (tensorSheaf_isCoherentLike Y _ _ hΛ hX) hX
    haveI : (cokernel (ap TΣ sΣ X)).IsFinitePresentation := hc
    exact isIso_adjUnit_of_killed hI _
      (hB.idealKills_of_killed _ hc (app_cokernel_eq_zero (T := TΣ) (σ := sΣ) X))
  -- the chase
  have w1 : ap TΣ sΣ T.X₁ ≫ T.f = TΣ.map T.f ≫ ap TΣ sΣ T.X₂ := (naturality' TΣ sΣ T.f).symm
  have w2 : ap TΣ sΣ T.X₂ ≫ T.g = TΣ.map T.g ≫ ap TΣ sΣ T.X₃ := (naturality' TΣ sΣ T.g).symm
  have hTex : (T.map TΣ).ShortExact := hT.map_of_exact TΣ
  have hh : Mono (cokernel.map (ap TΣ sΣ T.X₁) (ap TΣ sΣ T.X₂) (TΣ.map T.f) T.f w1) :=
    mono_cokernel_map (TΣ.map T.f) (TΣ.map T.g) (T.map TΣ).zero T.f T.g T.zero _ _ _ w1 w2
      hTex.exact
  let h := cokernel.map (ap TΣ sΣ T.X₁) (ap TΣ sΣ T.X₂) (TΣ.map T.f) T.f w1
  haveI := hunit T.X₁ h1
  haveI := hunit T.X₂ h2
  have hn := ProjectionFormula.adjUnit_naturality ιΣ h
  have hm2 : Mono ((Scheme.Modules.pushforward ιΣ).map ((Scheme.Modules.pullback ιΣ).map h)) := by
    have heq : (Scheme.Modules.pushforward ιΣ).map ((Scheme.Modules.pullback ιΣ).map h) =
        inv (ProjectionFormula.adjUnit ιΣ _) ≫ h ≫ ProjectionFormula.adjUnit ιΣ _ := by
      rw [hn, IsIso.inv_hom_id_assoc]
    rw [heq]; infer_instance
  haveI : Mono ((Scheme.Modules.pullback ιΣ).map h) :=
    (Scheme.Modules.pushforward ιΣ).mono_of_mono_map hm2
  have hsq : (Scheme.Modules.pullback ιΣ).map T.f ≫
      (Scheme.Modules.pullback ιΣ).map (cokernel.π (ap TΣ sΣ T.X₂)) =
      (Scheme.Modules.pullback ιΣ).map (cokernel.π (ap TΣ sΣ T.X₁)) ≫
        (Scheme.Modules.pullback ιΣ).map h := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
    simp [h, cokernel.map]
  haveI := hπ T.X₁
  haveI := hπ T.X₂
  have hfm : Mono ((Scheme.Modules.pullback ιΣ).map T.f) := by
    have e : (Scheme.Modules.pullback ιΣ).map T.f =
        ((Scheme.Modules.pullback ιΣ).map (cokernel.π (ap TΣ sΣ T.X₁)) ≫
          (Scheme.Modules.pullback ιΣ).map h) ≫
          inv ((Scheme.Modules.pullback ιΣ).map (cokernel.π (ap TΣ sΣ T.X₂))) := by
      rw [← hsq, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [e]; infer_instance
  exact { exact := ex, mono_f := hfm,
          epi_g := inferInstanceAs (Epi ((Scheme.Modules.pullback ιΣ).map T.g)) }


-- @@ L358-368 verbatim
/-- `σ`-regularity passes to subobjects. -/
theorem mono_ap_of_mono (hL : HasConstantRank Y L 1) {A B : Y.Modules} (i : A ⟶ B) [Mono i]
    (hB : Mono (ap TΣ sΣ B)) : Mono (ap TΣ sΣ A) := by
  have hΛ : IsFiniteLocallyFree Y (lineBundleDual Y L) :=
    (lineBundleDual_hasConstantRank L hL).isFiniteLocallyFree
  haveI := tensorSheafLeftFunctor_preservesFiniteLimits Y _ hΛ
  haveI := tensorSheafLeftFunctor_preservesFiniteColimits Y _ hΛ
  have w := naturality' TΣ sΣ i
  haveI : Mono (TΣ.map i ≫ ap TΣ sΣ B) := mono_comp _ _
  rw [w] at this
  exact mono_of_mono _ i


-- @@ L370-371 verbatim
variable [IsLocallyNoetherian (sectionEvaluationIdealSheaf σ).subscheme]
  (hY : HasBundleCovers Y) (hD : HasBundleCovers (sectionEvaluationIdealSheaf σ).subscheme)


-- @@ L373-380 verbatim
theorem cartier_ses (hL : HasConstantRank Y L 1) {A B D : Y.Modules} {i : A ⟶ B} {g : B ⟶ D}
    (hs : AbelianResolutionF15.SES i g) (hA : IsCoherentLike Y A) (hB : IsCoherentLike Y B)
    (hm : Mono (ap TΣ sΣ D)) :
    AbelianResolutionF15.SES ((Scheme.Modules.pullback ιΣ).map i)
      ((Scheme.Modules.pullback ιΣ).map g) := by
  let T : ShortComplex Y.Modules := ShortComplex.mk i g hs.zero
  have h := pullback_shortExact_cartier σ hL T hs.exact hA hB hm
  exact ⟨(T.map (Scheme.Modules.pullback ιΣ)).zero, h⟩


-- @@ L382-394 verbatim
/-- The restriction to `V(σ)` of a `σ`-regular sheaf of bundle dimension `≤ d` has bundle
dimension `≤ d`, provided all bundles are `σ`-regular. -/
theorem pdLE_pullback_cartier (hL : HasConstantRank Y L 1)
    (hbund : ∀ E, IsFiniteLocallyFree Y E → Mono (ap TΣ sΣ E))
    {d : ℕ} {F : Y.Modules} (hF : IsCoherentLike Y F) (hm : Mono (ap TΣ sΣ F))
    (hd : PdLE hY d F) : PdLE hD d ((Scheme.Modules.pullback ιΣ).obj F) :=
  PerfectRepRestrictBG2.pdLE_map (setup Y hY) (setup _ hD) (Scheme.Modules.pullback ιΣ)
    (pullbackK0 ιΣ) (fun M => Mono (ap TΣ sΣ M))
    (fun E hE _ => pullbackK0_classOf ιΣ E hE)
    (fun E hE => pullback_isFiniteLocallyFree_global ιΣ E hE)
    (fun _ hM => isCoherentLike_pullback ιΣ hM) hbund
    (fun {_ _ _ i _} hs hR => by haveI := hs.mono; exact mono_ap_of_mono σ hL i hR)
    (fun hs hB hA _ hR => cartier_ses σ hL hs hA (hB.isFinitePresentation) hR) hF hm hd


-- @@ L396-414 verbatim
/-- **(ii) Restriction of perfect classes to an effective Cartier divisor.**  `σ : 𝒪 ⟶ L` with
`L` of constant rank one, `e : V(σ) ↪ Y` its zero scheme; if the Koszul map `σ_E` is a
monomorphism on every finite locally free `E` and on `F`, then
`e^* (repK0 F) = repK0 (e^* F)` in `K₀ (V(σ))`. -/
theorem pullbackK0_repK0_cartier (hL : HasConstantRank Y L 1)
    (hbund : ∀ E, IsFiniteLocallyFree Y E → Mono (ap TΣ sΣ E))
    {d d' : ℕ} (F : Y.Modules) (hF : IsCoherentLike Y F) (hm : Mono (ap TΣ sΣ F))
    (hd : PdLE hY d F)
    (hF' : IsCoherentLike (sectionEvaluationIdealSheaf σ).subscheme
      ((Scheme.Modules.pullback ιΣ).obj F))
    (hd' : PdLE hD d' ((Scheme.Modules.pullback ιΣ).obj F)) :
    pullbackK0 ιΣ (repK0 hY F hF hd) = repK0 hD ((Scheme.Modules.pullback ιΣ).obj F) hF' hd' :=
  PerfectRepRestrictBG2.repK0_map (setup Y hY) (setup _ hD) (Scheme.Modules.pullback ιΣ)
    (pullbackK0 ιΣ) (fun M => Mono (ap TΣ sΣ M))
    (fun E hE _ => pullbackK0_classOf ιΣ E hE)
    (fun E hE => pullback_isFiniteLocallyFree_global ιΣ E hE)
    (fun _ hM => isCoherentLike_pullback ιΣ hM) hbund
    (fun {_ _ _ i _} hs hR => by haveI := hs.mono; exact mono_ap_of_mono σ hL i hR)
    (fun hs hB hA _ hR => cartier_ses σ hL hs hA (hB.isFinitePresentation) hR) hF hm hd hF' hd'


-- @@ L416-427 verbatim
/-- **(ii) for a regular section**: bundles are automatically `σ`-regular. -/
theorem pullbackK0_repK0_cartier_of_regular (hL : HasConstantRank Y L 1)
    (hreg : SectionIsRegular σ)
    {d d' : ℕ} (F : Y.Modules) (hF : IsCoherentLike Y F) (hm : Mono (ap TΣ sΣ F))
    (hd : PdLE hY d F)
    (hF' : IsCoherentLike (sectionEvaluationIdealSheaf σ).subscheme
      ((Scheme.Modules.pullback ιΣ).obj F))
    (hd' : PdLE hD d' ((Scheme.Modules.pullback ιΣ).obj F)) :
    pullbackK0 ιΣ (repK0 hY F hF hd) = repK0 hD ((Scheme.Modules.pullback ιΣ).obj F) hF' hd' :=
  pullbackK0_repK0_cartier σ hY hD hL
    (fun E hE => CIIL3B.hmono_of_sectionIsRegular σ (isLocalLineFrame_of_hasConstantRank_one hL)
      hreg E hE) F hF hm hd hF' hd'


-- @@ L429-429 verbatim
end Cartier


-- @@ L431-431 verbatim
end Sch


-- @@ L433-433 verbatim
end PerfectRepRestrictBG2
