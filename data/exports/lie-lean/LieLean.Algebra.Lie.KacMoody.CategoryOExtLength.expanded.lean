/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.CategoryOProjDimension


-- @@ L8-32 verbatim
/-!
# Length bounds for `Extⁿ` between standard modules

[HumO] Theorem 6.11 (b). Let `Λ` be dominant integral and `w, w' ∈ W`. Then for all
`n > ℓ(w') - ℓ(w)`,
`Extⁿ_𝒪(M(w'·Λ), M(w·Λ)) = 0 = Extⁿ_𝒪(M(w'·Λ), L(w·Λ))`
(`CategoryO.ext_verma_weylDot_verma_eq_zero`, `CategoryO.ext_verma_weylDot_simple_eq_zero`).

Humphreys assumes `w'·Λ ≤ w·Λ`; the statements here hold without it (otherwise part (a) of the
theorem gives the vanishing for `n > 0`, and `Hom` vanishes for weight reasons).

## Proof

Humphreys leaves part (b) to the reader, suggesting the strategy of part (a) with induction on
`ℓ(w') - ℓ(w)`. Here the induction is on `n`, for any target `Y` with
`Hom(M(y·Λ), Y) = 0` whenever `ℓ(y) < k` (`CategoryO.ext_verma_weylDot_eq_zero_of_hom`):
dimension shifting along `P(w'·Λ) → M(w'·Λ)` (`CategoryO.ext_succ_verma_eq_zero`) reduces
`Extⁿ⁺¹(M(w'·Λ), Y)` to `Extⁿ(M(x·Λ), Y)` with `x < w'`, so `ℓ(x) < ℓ(w')`. For `Y = M(w·Λ)` a
nonzero map `M(y·Λ) → M(w·Λ)` gives `w ≤ y` (BGG), and for `Y = L(w·Λ)` it gives `y = w`.

## References

* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §6.11.
-/


-- @@ L34-34 verbatim
open CategoryTheory Limits LieModule Module


-- @@ L36-36 verbatim
noncomputable section


-- @@ L38-38 verbatim
universe u


-- @@ L40-40 verbatim
namespace Matrix.Realization.KacMoodyAlgebra


-- @@ L42-42 verbatim
namespace CategoryO


-- @@ L44-46 verbatim
variable {ι H : Type u} {K : Type} [Fintype ι] [DecidableEq ι] [Field K] [CharZero K]
  [IsAlgClosed K] [AddCommGroup H] [Module K H] [FiniteDimensional K H] {A : Matrix ι ι ℤ}
  [Fact A.IsFiniteCartan] {P : Realization A K H}


-- @@ L48-48 verbatim
local notation "𝔤" => KacMoodyAlgebra P


-- @@ L50-50 verbatim
variable (hA : A.IsFiniteCartan) {Λ : Dual K H} (hΛ : P.IsDominantIntegral Λ)

-- @@ L51-51 verbatim
include hΛ


-- @@ L53-74 verbatim
/-- `Extⁿ(M(w'·Λ), Y) = 0` for `n > ℓ(w') - k`, if `Hom(M(y·Λ), Y) = 0` whenever `ℓ(y) < k`. -/
theorem ext_verma_weylDot_eq_zero_of_hom (Y : CategoryO.{u} P) (k : ℕ)
    (hY : ∀ y : P.weylGroup hA.isGeneralizedCartan,
      (P.coxeterSystem hA.isGeneralizedCartan).length y < k →
        ∀ φ : (verma P (P.weylDot hA.isGeneralizedCartan y Λ)).obj →ₗ⁅K,𝔤⁆ Y.obj, φ = 0) :
    ∀ (n : ℕ) (w' : P.weylGroup hA.isGeneralizedCartan),
      (P.coxeterSystem hA.isGeneralizedCartan).length w' < n + k →
        ∀ x : Abelian.Ext.{u} (verma P (P.weylDot hA.isGeneralizedCartan w' Λ)) Y n, x = 0 := by
  intro n
  induction n with
  | zero =>
    intro w' hw' x
    rw [← Abelian.Ext.mk₀_homEquiv₀_apply x,
      hom_eq_zero_of_lie (hY w' (by omega)) (Abelian.Ext.homEquiv₀ x), Abelian.Ext.mk₀_zero]
  | succ n ih =>
    intro w' hw' x
    refine ext_succ_verma_eq_zero Y _ n (fun κ hκ hne z ↦ ?_) x
    obtain ⟨y, rfl⟩ := IsStronglyLinked.exists_weylDot_eq P hA.isGeneralizedCartan
      (VermaModule.isStronglyLinked_of_multiplicity_ne_zero P hA hκ)
    have hyw := (VermaModule.multiplicity_weylDot_ne_zero_iff_of_isDominantIntegral P hA hΛ).mp hκ
    have hlt := hyw.eq_or_length_lt.resolve_left fun h ↦ hne (by rw [h])
    exact ih y (by omega) z


-- @@ L76-95 verbatim
/-- **[HumO] Theorem 6.11 (b)**, Verma modules. For `Λ` dominant integral and `w, w' ∈ W`,
`Extⁿ_𝒪(M(w'·Λ), M(w·Λ)) = 0` for all `n > ℓ(w') - ℓ(w)`. Finite type, algebraically closed
field of characteristic zero (Humphreys works over `ℂ`, and assumes `w'·Λ ≤ w·Λ`, which is not
needed). -/
theorem ext_verma_weylDot_verma_eq_zero (w w' : P.weylGroup hA.isGeneralizedCartan) {n : ℕ}
    (hn : (P.coxeterSystem hA.isGeneralizedCartan).length w' <
      n + (P.coxeterSystem hA.isGeneralizedCartan).length w)
    (x : Abelian.Ext.{u} (verma.{u} P (P.weylDot hA.isGeneralizedCartan w' Λ))
      (verma.{u} P (P.weylDot hA.isGeneralizedCartan w Λ)) n) : x = 0 := by
  refine ext_verma_weylDot_eq_zero_of_hom hA hΛ _ _ (fun y hy φ ↦ ?_) n w' hn x
  by_contra hφ
  let g : VermaModule P (P.weylDot hA.isGeneralizedCartan y Λ) →ₗ⁅K,𝔤⁆
      VermaModule P (P.weylDot hA.isGeneralizedCartan w Λ) :=
    (ofLieEquiv (P := P) _).symm.toLieModuleHom.comp
      (φ.comp (ofLieEquiv (P := P) _).toLieModuleHom)
  have hg : g ≠ 0 := fun h0 ↦ hφ (LieModuleHom.ext fun m ↦ LieModuleHom.congr_fun h0 m)
  have hwy := (VermaModule.multiplicity_weylDot_ne_zero_iff_of_isDominantIntegral P hA hΛ).mp
    (VermaModule.multiplicity_ne_zero_of_hom_ne_zero P hg)
  have := hwy.length_le
  omega


-- @@ L97-115 verbatim
/-- **[HumO] Theorem 6.11 (b)**, simple modules, for any object `Z ≅ L(w·Λ)`. -/
theorem ext_verma_weylDot_simple_eq_zero_of_equiv (w w' : P.weylGroup hA.isGeneralizedCartan)
    (Z : CategoryO.{u} P)
    (e : Z.obj ≃ₗ⁅K,𝔤⁆ IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w Λ)) {n : ℕ}
    (hn : (P.coxeterSystem hA.isGeneralizedCartan).length w' <
      n + (P.coxeterSystem hA.isGeneralizedCartan).length w)
    (x : Abelian.Ext.{u} (verma.{u} P (P.weylDot hA.isGeneralizedCartan w' Λ)) Z n) :
    x = 0 := by
  refine ext_verma_weylDot_eq_zero_of_hom hA hΛ _ _ (fun y hy φ ↦ ?_) n w' hn x
  by_contra hφ
  let g : VermaModule P (P.weylDot hA.isGeneralizedCartan y Λ) →ₗ⁅K,𝔤⁆
      IrreducibleModule P (P.weylDot hA.isGeneralizedCartan w Λ) :=
    e.toLieModuleHom.comp (φ.comp (ofLieEquiv (P := P) _).toLieModuleHom)
  have hg : g ≠ 0 := fun h0 ↦ hφ (LieModuleHom.ext fun m ↦
    e.injective ((LieModuleHom.congr_fun h0 m).trans (map_zero e).symm))
  have hyw := weylDot_injective P hA.isGeneralizedCartan hΛ
    (VermaModule.eq_of_hom_irreducible_ne_zero P hg)
  subst hyw
  omega


-- @@ L117-126 verbatim
/-- **[HumO] Theorem 6.11 (b)**, simple modules. For `Λ` dominant integral and `w, w' ∈ W`,
`Extⁿ_𝒪(M(w'·Λ), L(w·Λ)) = 0` for all `n > ℓ(w') - ℓ(w)`. Same setting as
`ext_verma_weylDot_verma_eq_zero`. -/
theorem ext_verma_weylDot_simple_eq_zero (w w' : P.weylGroup hA.isGeneralizedCartan) {n : ℕ}
    (hn : (P.coxeterSystem hA.isGeneralizedCartan).length w' <
      n + (P.coxeterSystem hA.isGeneralizedCartan).length w)
    (x : Abelian.Ext.{u} (verma.{u} P (P.weylDot hA.isGeneralizedCartan w' Λ))
      (simple.{u} P (P.weylDot hA.isGeneralizedCartan w Λ)) n) : x = 0 :=
  ext_verma_weylDot_simple_eq_zero_of_equiv hA hΛ w w' _
    (ofLieEquiv (P := P) (IrreducibleModule P _)).symm hn x


-- @@ L128-128 verbatim
end CategoryO


-- @@ L130-130 verbatim
end Matrix.Realization.KacMoodyAlgebra
