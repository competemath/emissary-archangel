/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.Analytification.GAGA.HyperplaneModules
import Oka.AlgebraicGeometry.Modules.CocycleTwistPullbackModules
import Oka.Geometry.RingedSpace.LocallyRingedSpace.ModulesStalkNakayama


-- @@ L10-29 verbatim
/-!
# Twisting analytic sheaves of modules on `ℙⁿ_an`

For a sheaf of modules `M` on `ℙⁿ_an` and `m : ℤ`, the **twist** `M(m)`
(`ComplexAnalytic.projectiveSpaceAn.twistMod M m`) is the twist of `M` by the pullback along
`π : ℙⁿ_an ⟶ ℙⁿ` of the `m`-th power of the standard cocycle `(Xⱼ / Xᵢ)` on the preimages
`π⁻¹ Uᵢ` of the standard charts (`LocallyRingedSpace.modTwist`).

## Main definitions and results

- `twistModFunctor n m`, an autoequivalence (`twistModEquivalence`);
- `twistModTwistModIso : M(a)(b) ≅ M(a + b)`, `twistModZeroIso : M(0) ≅ M`,
  `twistModCongr : M(a) ≅ M(b)` for `a = b`;
- `analytificationTwistIso : (F(m))^an ≅ F^an(m)`;
- `isCoherent_twistMod`: twists of coherent sheaves are coherent;
- `mulXMod M m l : M(m) ⟶ M(m + 1)`, multiplication by the variable `X_l` (by `X_l / Xₖ` on
  `π⁻¹ Uₖ`), and `mulXModZero M l : M(-1) ⟶ M`; on `π⁻¹ Uₖ` its range is `(X_l / Xₖ) · M` and
  its kernel is killed by `X_l / Xₖ` (`rangeLESMul_mulXModZero`, `sMulLERange_mulXModZero`,
  `sMulKerEqZero_mulXModZero`).
-/


-- @@ L31-31 verbatim
open CategoryTheory Limits TopologicalSpace Opposite AlgebraicGeometry

-- @@ L32-32 verbatim
open AlgebraicGeometry.LocallyRingedSpace AlgebraicGeometry.Scheme.Modules


-- @@ L34-34 verbatim
universe u


-- @@ L36-36 verbatim
noncomputable section


-- @@ L38-38 verbatim
namespace ComplexAnalytic.projectiveSpaceAn


-- @@ L40-40 verbatim
variable {n : ℕ}


-- @@ L42-45 verbatim
variable (n) in
/-- The preimage `π⁻¹ Uᵢ ⊆ ℙⁿ_an` of the standard chart `Uᵢ = D₊(Xᵢ)`. -/
abbrev stdOpenAn (i : Fin (n + 1)) : Opens (projectiveSpaceAn.{u} n).toPresheafedSpace :=
  preimOpen (πLRS.{u} n) (ProjectiveSpace.U n (ULift.{u} ℂ) i)


-- @@ L47-48 verbatim
lemma iSup_stdOpenAn : ⨆ i, stdOpenAn.{u} n i = ⊤ :=
  iSup_preimOpen (ProjectiveSpace.iSup_U n (ULift.{u} ℂ))


-- @@ L50-53 verbatim
variable (n) in
/-- The cocycle `π^♯ (Xⱼ / Xᵢ)ᵐ` on the `π⁻¹ Uᵢ`. -/
def twistModCocycle (m : ℤ) : ModCocycle (stdOpenAn.{u} n) :=
  cocycleComap (πLRS.{u} n) (ProjectiveSpace.cocycle n (ULift.{u} ℂ) ^ m)


-- @@ L55-58 verbatim
lemma twistModCocycle_add (a b : ℤ) :
    twistModCocycle.{u} n (a + b) = twistModCocycle n a * twistModCocycle n b := by
  rw [twistModCocycle, zpow_add, cocycleComap_mul]
  rfl


-- @@ L60-61 verbatim
lemma twistModCocycle_zero : twistModCocycle.{u} n 0 = 1 := by
  rw [twistModCocycle, zpow_zero, cocycleComap_one]


-- @@ L63-66 verbatim
/-- The twist `M(m)` of a sheaf of modules on `ℙⁿ_an`. -/
abbrev twistMod (M : SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf)
    (m : ℤ) : SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf :=
  modTwist M (twistModCocycle n m)


-- @@ L68-73 verbatim
variable (n) in
/-- The functor `M ↦ M(m)` on sheaves of modules on `ℙⁿ_an`. -/
abbrev twistModFunctor (m : ℤ) :
    SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf ⥤
      SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf :=
  modTwistFunctor (twistModCocycle n m)


-- @@ L75-80 verbatim
variable (n) in
/-- `M ↦ M(m)` is an autoequivalence. -/
def twistModEquivalence (m : ℤ) :
    SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf ≌
      SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf :=
  modTwistEquivalence (twistModCocycle n m) iSup_stdOpenAn


-- @@ L82-84 verbatim
/-- Twisting is an equivalence. -/
instance (m : ℤ) : (twistModFunctor.{u} n m).IsEquivalence :=
  (twistModEquivalence n m).isEquivalence_functor


-- @@ L86-88 verbatim
/-- Twisting is additive. -/
instance (m : ℤ) : (twistModFunctor.{u} n m).Additive :=
  Functor.additive_of_preserves_binary_products _


-- @@ L90-90 verbatim
variable (M : SheafOfModules.{u} (projectiveSpaceAn.{u} n).toLocallyRingedSpace.ringSheaf)


-- @@ L92-95 verbatim
/-- `M(a)(b) ≅ M(a + b)`. -/
def twistModTwistModIso (a b : ℤ) : twistMod (twistMod M a) b ≅ twistMod M (a + b) :=
  (modTwistFunctorCompIso (twistModCocycle n a) (twistModCocycle n b)).app M ≪≫
    (modTwistFunctorCongr (twistModCocycle_add a b).symm).app M


-- @@ L97-99 verbatim
/-- `M(0) ≅ M`. -/
def twistModZeroIso : twistMod M 0 ≅ M :=
  (modTwistFunctorCongr twistModCocycle_zero).app M ≪≫ modTwistOneIso M iSup_stdOpenAn


-- @@ L101-103 verbatim
/-- `M(a) ≅ M(b)` for `a = b`. -/
def twistModCongr {a b : ℤ} (h : a = b) : twistMod M a ≅ twistMod M b :=
  (modTwistFunctorCongr (congrArg (twistModCocycle n) h)).app M


-- @@ L105-112 verbatim
/-- **Analytification commutes with twisting**: `(F(m))^an ≅ F^an(m)`. -/
def analytificationTwistIso
    (F : SheafOfModules.{u} (projectiveSpace.{u} n).obj.left.toLocallyRingedSpace.ringSheaf)
    (m : ℤ) :
    (analytificationModules (projectiveSpace.{u} n)).obj (ProjectiveSpace.twist F m) ≅
      twistMod ((analytificationModules (projectiveSpace.{u} n)).obj F) m :=
  (pullbackModulesTwistIso (πLRS.{u} n) (ProjectiveSpace.cocycle n (ULift.{u} ℂ) ^ m)
    (ProjectiveSpace.iSup_U n (ULift.{u} ℂ))).app F


-- @@ L114-116 verbatim
/-- **Twists of coherent sheaves on `ℙⁿ_an` are coherent.** -/
theorem isCoherent_twistMod [M.IsCoherent] (m : ℤ) : (twistMod M m).IsCoherent :=
  isCoherent_modTwist M _ iSup_stdOpenAn


-- @@ L118-118 verbatim
section MulX


-- @@ L120-124 verbatim
variable (n) in
/-- The section `π^♯ (X_l / Xₖ)` over `π⁻¹ Uₖ`. -/
abbrev xDivAn (k l : Fin (n + 1)) :
    (projectiveSpaceAn.{u} n).presheaf.obj (op (stdOpenAn.{u} n k)) :=
  pbSec (πLRS.{u} n) (ProjectiveSpace.xDiv k l)


-- @@ L126-132 expanded
lemma xDivAn_compat (l i j : Fin (n + 1)) :
    (TopCat.Presheaf.restrictOpen (xDivAn.{u} n i l) (stdOpenAn n i ⊓ stdOpenAn n j) (by order)) =
      (twistModCocycle n 1).g i j *
        (TopCat.Presheaf.restrictOpen (xDivAn n j l) (stdOpenAn n i ⊓ stdOpenAn n j) (by order)) :=
  by
  have h := congrArg (pbSec (πLRS.{u} n)) (ProjectiveSpace.xDiv_compat (R := ULift.{u} ℂ) l i j)
  rw [pbSec_mul, pbSec_res, pbSec_res] at h
  rw [twistModCocycle, zpow_one]
  exact h


-- @@ L134-138 verbatim
/-- **Multiplication by the variable `X_l`**, `M(m) ⟶ M(m + 1)`: on `π⁻¹ Uₖ` it is
multiplication by `π^♯ (X_l / Xₖ)`. -/
def mulXMod (m : ℤ) (l : Fin (n + 1)) : twistMod M m ⟶ twistMod M (m + 1) :=
  modTwistMulSection M (twistModCocycle n m) (twistModCocycle n 1) (fun k ↦ xDivAn n k l)
    (xDivAn_compat l) ≫ (modTwistFunctorCongr (twistModCocycle_add m 1).symm).hom.app M


-- @@ L140-145 expanded
@[simp]
lemma modTwistComp_mulXMod_app (m : ℤ) (l : Fin (n + 1)) {W : Opens _}
    (s : (twistMod M m).val.obj (op W)) (k : Fin (n + 1)) :
    modTwistComp ((mulXMod M m l).val.app (op W) s) k =
      (TopCat.Presheaf.restrictOpen (xDivAn n k l) (W ⊓ stdOpenAn n k) (by order)) •
        modTwistComp s k :=
  rfl


-- @@ L147-153 expanded
/-- In the chart `k`, multiplication by `X_l` is multiplication by `π^♯ (X_l / Xₖ)`. -/
lemma modTwistSectionsEquiv_mulXMod (m : ℤ) (l k : Fin (n + 1)) {W : Opens _}
    (hW : W ≤ stdOpenAn n k) (s : (twistMod M m).val.obj (op W)) :
    modTwistSectionsEquiv (twistModCocycle n (m + 1)) k hW ((mulXMod M m l).val.app (op W) s) =
      (TopCat.Presheaf.restrictOpen (xDivAn n k l) W (by order)) •
        modTwistSectionsEquiv (twistModCocycle n m) k hW s :=
  by
  rw [modTwistSectionsEquiv_apply, modTwistSectionsEquiv_apply, modTwistComp_mulXMod_app,
    modRes_smul, yres_res]


-- @@ L155-157 verbatim
/-- Multiplication by `X_l`, `M(-1) ⟶ M`. -/
def mulXModZero (l : Fin (n + 1)) : twistMod M (-1) ⟶ M :=
  mulXMod M (-1) l ≫ (twistModCongr M (neg_add_cancel 1) ≪≫ twistModZeroIso M).hom


-- @@ L159-165 verbatim
lemma rangeLESMul_mulXMod (m : ℤ) (l k : Fin (n + 1)) :
    RangeLESMul (mulXMod M m l) (xDivAn n k l) := by
  intro W hW s
  refine ⟨(modTwistSectionsEquiv (twistModCocycle n (m + 1)) k hW).symm
    (modTwistSectionsEquiv (twistModCocycle n m) k hW s),
    (modTwistSectionsEquiv (twistModCocycle n (m + 1)) k hW).injective ?_⟩
  rw [modTwistSectionsEquiv_mulXMod, LinearEquiv.map_smul, LinearEquiv.apply_symm_apply]


-- @@ L167-173 verbatim
lemma sMulLERange_mulXMod (m : ℤ) (l k : Fin (n + 1)) :
    SMulLERange (mulXMod M m l) (xDivAn n k l) := by
  intro W hW q
  refine ⟨(modTwistSectionsEquiv (twistModCocycle n m) k hW).symm
    (modTwistSectionsEquiv (twistModCocycle n (m + 1)) k hW q),
    (modTwistSectionsEquiv (twistModCocycle n (m + 1)) k hW).injective ?_⟩
  rw [modTwistSectionsEquiv_mulXMod, LinearEquiv.apply_symm_apply, LinearEquiv.map_smul]


-- @@ L175-179 verbatim
lemma sMulKerEqZero_mulXMod (m : ℤ) (l k : Fin (n + 1)) :
    SMulKerEqZero (mulXMod M m l) (xDivAn n k l) := by
  intro W hW s hs
  apply (modTwistSectionsEquiv (twistModCocycle n m) k hW).injective
  rw [LinearEquiv.map_smul, ← modTwistSectionsEquiv_mulXMod, hs, map_zero, map_zero]


-- @@ L181-183 verbatim
lemma rangeLESMul_mulXModZero (l k : Fin (n + 1)) :
    RangeLESMul (mulXModZero M l) (xDivAn n k l) :=
  (rangeLESMul_mulXMod M (-1) l k).comp_iso _


-- @@ L185-187 verbatim
lemma sMulLERange_mulXModZero (l k : Fin (n + 1)) :
    SMulLERange (mulXModZero M l) (xDivAn n k l) :=
  (sMulLERange_mulXMod M (-1) l k).comp_iso _


-- @@ L189-191 verbatim
lemma sMulKerEqZero_mulXModZero (l k : Fin (n + 1)) :
    SMulKerEqZero (mulXModZero M l) (xDivAn n k l) :=
  (sMulKerEqZero_mulXMod M (-1) l k).comp_iso _


-- @@ L193-193 verbatim
end MulX


-- @@ L195-195 verbatim
end ComplexAnalytic.projectiveSpaceAn
