/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Oka.AlgebraicGeometry.ProjectiveSpace.TwistCohomology
import Oka.AlgebraicGeometry.Modules.QuasicoherentCover


-- @@ L9-32 verbatim
/-!
# Vanishing theorems for quasi-coherent sheaves on projective space

Let `ℙⁿ = ℙ(n; R)` with its standard cover `Uᵢ = D₊(Xᵢ)`, whose nonempty finite intersections
`UI I = D₊(X_I)` are affine.

* The twist `F(m)` of a quasi-coherent `F` is quasi-coherent, since `F(m)|_{Uᵢ} ≅ F|_{Uᵢ}`
  (`ProjectiveSpace.isQuasicoherent_twist`); in particular `O(m)` is quasi-coherent.
* **`Hᵠ(ℙⁿ, O(k)) = 0` for `q ≥ 1` and `k ≥ -n`**
  (`ProjectiveSpace.H_succ_twistingSheafAb_eq_zero`): the acyclicity hypothesis of
  `ProjectiveSpace.H_twistingSheafAb_eq_zero` is Serre's affine vanishing for the quasi-coherent
  sheaf `O(k)` on the affine opens `UI I`.
* **`Hᵠ(ℙⁿ, F) = 0` for `q ≥ n + 1` and every quasi-coherent `F`**
  (`ProjectiveSpace.H_eq_zero_of_le_of_isQuasicoherent`): the standard cover has `n + 1` members
  (`AlgebraicGeometry.Scheme.Modules.H_eq_zero_of_isAffineOpen_cover`).

Each result is also stated for the cohomology `LocallyRingedSpace.H` of sheaves of modules over
`ℙ(n; R).toLocallyRingedSpace.ringSheaf`, the spelling used by the GAGA comparison map; the
category `ℙ(n; R).Modules` *is* `SheafOfModules ℙ(n; R).toLocallyRingedSpace.ringSheaf` up to
`rfl` (see `Oka/AlgebraicGeometry/Modules/QuasicoherentCover.lean`), and the specialisations to
`R = ULift ℂ` are given. For `F` typed over `(ComplexAnalytic.projectiveSpace n).obj.left`
(equal to `ℙ(n; ULift ℂ)` by `rfl`), instance search does not unfold that spelling, so the
(quasi-)coherence instance is passed as `(hF := ‹_›)`.
-/


-- @@ L34-34 verbatim
open CategoryTheory TopologicalSpace

-- @@ L35-35 verbatim
open AlgebraicGeometry.Scheme.Modules

-- @@ L36-36 verbatim
open scoped AlgebraicGeometry.ProjectiveSpace


-- @@ L38-38 verbatim
universe u


-- @@ L40-40 verbatim
namespace AlgebraicGeometry.ProjectiveSpace


-- @@ L42-42 verbatim
variable {n : ℕ} {R : Type u} [CommRing R]


-- @@ L44-49 verbatim
/-- **Twists of quasi-coherent sheaves are quasi-coherent**: `F(m)` is locally isomorphic to
`F`. -/
instance isQuasicoherent_twist (F : ℙ(n; R).Modules) [F.IsQuasicoherent] (m : ℤ) :
    (twist F m).IsQuasicoherent :=
  isQuasicoherent_of_restrictIso (stdCover n R) (iSup_stdCover n R) _ (fun _ ↦ F)
    fun i ↦ twistRestrictIso F m i.down


-- @@ L51-53 verbatim
/-- **`O(m)` is quasi-coherent.** -/
instance isQuasicoherent_twistingSheaf (m : ℤ) : (twistingSheaf n R m).IsQuasicoherent :=
  isQuasicoherent_twist _ m


-- @@ L55-64 verbatim
/-- The finite intersections of the standard cover are the opens `UI`. -/
lemma iInf_stdCover (I : Finset (ULift.{u} (Fin (n + 1)))) :
    ⨅ i ∈ I, stdCover n R i = UI n R (I.image ULift.down) := by
  classical
  rw [UI_eq_iInf]
  apply le_antisymm
  · refine le_iInf₂ fun j hj ↦ ?_
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
    exact iInf₂_le i hi
  · exact le_iInf₂ fun i hi ↦ iInf₂_le i.down (Finset.mem_image_of_mem _ hi)


-- @@ L66-72 verbatim
/-- The nonempty finite intersections of the standard cover are affine. -/
lemma isAffineOpen_iInf_stdCover (I : Finset (ULift.{u} (Fin (n + 1)))) (hI : I.Nonempty) :
    IsAffineOpen (⨅ i ∈ I, stdCover n R i) := by
  classical
  obtain ⟨i, hi⟩ := hI
  rw [iInf_stdCover]
  exact isAffineOpen_UI (Finset.mem_image_of_mem _ hi)


-- @@ L74-80 verbatim
/-- **Cohomological dimension of `ℙⁿ`**: `Hᵠ(ℙⁿ, F) = 0` for every quasi-coherent `F` and
`q ≥ n + 1`. -/
theorem H_eq_zero_of_le_of_isQuasicoherent (F : ℙ(n; R).Modules) [F.IsQuasicoherent] (q : ℕ)
    (hq : n + 1 ≤ q)
    (x : TopCat.Sheaf.H ((SheafOfModules.toSheaf ℙ(n; R).ringCatSheaf).obj F) q) : x = 0 :=
  H_eq_zero_of_isAffineOpen_cover (stdCover n R) (iSup_stdCover n R)
    isAffineOpen_iInf_stdCover F q (by simpa using hq) x


-- @@ L82-87 verbatim
/-- **`Hᵠ(ℙⁿ, O(k)) = 0` for `q ≥ 1` and `k ≥ -n`.** -/
theorem H_succ_twistingSheafAb_eq_zero (k : ℤ) (hk : -(n : ℤ) ≤ k) (q : ℕ)
    (x : TopCat.Sheaf.H (twistingSheafAb n R k) (q + 1)) : x = 0 :=
  H_twistingSheafAb_eq_zero k hk (fun I hI q x ↦ by
    obtain ⟨i, hi⟩ := hI
    exact H_restrictOpen_eq_zero_of_isAffineOpen _ (isAffineOpen_UI hi) q x) q x


-- @@ L89-89 verbatim
section LocallyRingedSpace


-- @@ L91-91 verbatim
/-! ### The `LocallyRingedSpace.H` spelling -/


-- @@ L93-98 verbatim
/-- **`Hᵠ(ℙⁿ, O(k)) = 0` for `q ≥ 1` and `k ≥ -n`**, for `O(k)` as a sheaf of modules over
`ℙ(n; R).toLocallyRingedSpace.ringSheaf`. -/
theorem locallyRingedSpaceH_twistingSheaf_eq_zero (k : ℤ) (hk : -(n : ℤ) ≤ k) (q : ℕ)
    (x : LocallyRingedSpace.H (Y := ℙ(n; R).toLocallyRingedSpace) (twistingSheaf n R k)
      (q + 1)) : x = 0 :=
  H_succ_twistingSheafAb_eq_zero k hk q x


-- @@ L100-105 verbatim
/-- **Cohomological dimension of `ℙⁿ`**, for a quasi-coherent sheaf of modules over
`ℙ(n; R).toLocallyRingedSpace.ringSheaf`: `Hᵠ(ℙⁿ, F) = 0` for `q ≥ n + 1`. -/
theorem locallyRingedSpaceH_eq_zero_of_le_of_isQuasicoherent
    (F : SheafOfModules.{u} ℙ(n; R).toLocallyRingedSpace.ringSheaf) [hF : F.IsQuasicoherent]
    (q : ℕ) (hq : n + 1 ≤ q) (x : LocallyRingedSpace.H F q) : x = 0 :=
  @H_eq_zero_of_le_of_isQuasicoherent n R _ F hF q hq x


-- @@ L107-112 verbatim
/-- **Cohomological dimension of `ℙⁿ`**, for a coherent sheaf of modules over
`ℙ(n; R).toLocallyRingedSpace.ringSheaf`: `Hᵠ(ℙⁿ, F) = 0` for `q ≥ n + 1`. -/
theorem locallyRingedSpaceH_eq_zero_of_le_of_isCoherent
    (F : SheafOfModules.{u} ℙ(n; R).toLocallyRingedSpace.ringSheaf) [hF : F.IsCoherent]
    (q : ℕ) (hq : n + 1 ≤ q) (x : LocallyRingedSpace.H F q) : x = 0 :=
  @H_eq_zero_of_le_of_isQuasicoherent n R _ F (isQuasicoherent_of_isCoherent F) q hq x


-- @@ L114-114 verbatim
end LocallyRingedSpace


-- @@ L116-116 verbatim
section Complex


-- @@ L118-121 verbatim
/-- `Hᵠ(ℙⁿ_ℂ, O(k)) = 0` for `q ≥ 1` and `k ≥ -n`. -/
theorem H_succ_twistingSheafAb_complex_eq_zero (k : ℤ) (hk : -(n : ℤ) ≤ k) (q : ℕ)
    (x : TopCat.Sheaf.H (twistingSheafAb n (ULift.{u} ℂ) k) (q + 1)) : x = 0 :=
  H_succ_twistingSheafAb_eq_zero k hk q x


-- @@ L123-127 verbatim
/-- `Hᵠ(ℙⁿ_ℂ, O(k)) = 0` for `q ≥ 1` and `k ≥ -n`, in the `LocallyRingedSpace.H` spelling. -/
theorem locallyRingedSpaceH_twistingSheaf_complex_eq_zero (k : ℤ) (hk : -(n : ℤ) ≤ k) (q : ℕ)
    (x : LocallyRingedSpace.H (Y := ℙ(n; ULift.{u} ℂ).toLocallyRingedSpace)
      (twistingSheaf n (ULift.{u} ℂ) k) (q + 1)) : x = 0 :=
  locallyRingedSpaceH_twistingSheaf_eq_zero k hk q x


-- @@ L129-134 verbatim
/-- `Hᵠ(ℙⁿ_ℂ, F) = 0` for `q ≥ n + 1` and quasi-coherent `F`, in the `LocallyRingedSpace.H`
spelling. -/
theorem locallyRingedSpaceH_complex_eq_zero_of_le_of_isQuasicoherent
    (F : SheafOfModules.{u} ℙ(n; ULift.{u} ℂ).toLocallyRingedSpace.ringSheaf)
    [hF : F.IsQuasicoherent] (q : ℕ) (hq : n + 1 ≤ q) (x : LocallyRingedSpace.H F q) : x = 0 :=
  locallyRingedSpaceH_eq_zero_of_le_of_isQuasicoherent F q hq x


-- @@ L136-141 verbatim
/-- `Hᵠ(ℙⁿ_ℂ, F) = 0` for `q ≥ n + 1` and coherent `F`, in the `LocallyRingedSpace.H`
spelling. -/
theorem locallyRingedSpaceH_complex_eq_zero_of_le_of_isCoherent
    (F : SheafOfModules.{u} ℙ(n; ULift.{u} ℂ).toLocallyRingedSpace.ringSheaf)
    [hF : F.IsCoherent] (q : ℕ) (hq : n + 1 ≤ q) (x : LocallyRingedSpace.H F q) : x = 0 :=
  locallyRingedSpaceH_eq_zero_of_le_of_isCoherent F q hq x


-- @@ L143-143 verbatim
end Complex


-- @@ L145-145 verbatim
end AlgebraicGeometry.ProjectiveSpace
