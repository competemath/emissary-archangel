import Definitions.Def_WeierstrassCurve_ProjModel
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Point
import Definitions.Def_WeierstrassCurve_ProjModel_AddFormulas


-- @@ L24-24 verbatim
set_option Elab.async false


-- @@ L26-26 verbatim
section MEGA_KwLRSymOnCurveScaled_lean

-- @@ L27-27 verbatim
set_option autoImplicit false

-- @@ L28-28 verbatim
set_option linter.unusedSimpArgs false

-- @@ L29-29 verbatim
set_option maxHeartbeats 6400000


-- @@ L31-31 verbatim
noncomputable section


-- @@ L33-33 verbatim
open MvPolynomial WeierstrassCurve


-- @@ L35-35 verbatim
namespace WeierstrassProjModel


-- @@ L37-37 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L39-39 verbatim
universe u


-- @@ L41-41 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


-- @@ L43-43 verbatim
local notation "P₆" => MvPolynomial (Fin 3 ⊕ Fin 3) R

-- @@ L44-44 verbatim
local notation "WP₁" => kw_lrAdd_WP₁ W

-- @@ L45-45 verbatim
local notation "WP₂" => kw_lrAdd_WP₂ W


-- @@ L47-47 verbatim
section Abstract


-- @@ L49-49 verbatim
variable {S : Type u} [CommRing S] [Algebra R S]


-- @@ L51-58 verbatim
theorem kw_lrSymOC_aeval_scale (l x y z : S) :
    aeval ![l*x, l*y, l*z] W.toProjective.polynomial
      = l^3 * aeval ![x, y, z] W.toProjective.polynomial := by
  simp only [WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring


-- @@ L60-75 verbatim
theorem kw_lrSymOC_aeval_diff (x x' y y' z z' : S) :
    aeval ![x, y, z] W.toProjective.polynomial
        - aeval ![x', y', z'] W.toProjective.polynomial
      = (x - x') * (- (x^2 + x*x' + x'^2) - algebraMap R S W.a₂ * (x+x') * z
          + algebraMap R S W.a₁ * y * z - algebraMap R S W.a₄ * z^2)
        + (y - y') * ((y+y') * z + algebraMap R S W.a₁ * x' * z
          + algebraMap R S W.a₃ * z^2)
        + (z - z') * (y'^2 + algebraMap R S W.a₁ * x' * y'
          + algebraMap R S W.a₃ * y' * (z+z') - algebraMap R S W.a₂ * x'^2
          - algebraMap R S W.a₄ * x' * (z+z')
          - algebraMap R S W.a₆ * (z^2 + z*z' + z'^2)) := by
  simp only [WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  ring


-- @@ L77-77 verbatim
end Abstract


-- @@ L79-101 verbatim
theorem kw_lrSymOC_scaled_mem_span_of (l m : P₆)
    (hX : l * kw_lrSym_X W - m * kw_lrAdd_X W ∈ Ideal.span {WP₁, WP₂})
    (hY : l * kw_lrSym_Y W - m * kw_lrAdd_Y W ∈ Ideal.span {WP₁, WP₂})
    (hZ : l * kw_lrSym_Z W - m * kw_lrAdd_Z W ∈ Ideal.span {WP₁, WP₂}) :
    l^3 * aeval ![kw_lrSym_X W, kw_lrSym_Y W, kw_lrSym_Z W]
          W.toProjective.polynomial
      ∈ Ideal.span {WP₁, WP₂} := by
  have hdiff : l^3 * aeval ![kw_lrSym_X W, kw_lrSym_Y W, kw_lrSym_Z W]
        W.toProjective.polynomial
      - m^3 * aeval ![kw_lrAdd_X W, kw_lrAdd_Y W, kw_lrAdd_Z W]
        W.toProjective.polynomial ∈ Ideal.span {WP₁, WP₂} := by
    rw [← kw_lrSymOC_aeval_scale W l, ← kw_lrSymOC_aeval_scale W m,
        kw_lrSymOC_aeval_diff W
          (l * kw_lrSym_X W) (m * kw_lrAdd_X W)
          (l * kw_lrSym_Y W) (m * kw_lrAdd_Y W)
          (l * kw_lrSym_Z W) (m * kw_lrAdd_Z W)]
    exact add_mem (add_mem (Ideal.mul_mem_right _ _ hX) (Ideal.mul_mem_right _ _ hY))
      (Ideal.mul_mem_right _ _ hZ)
  have hAdd : m^3 * aeval ![kw_lrAdd_X W, kw_lrAdd_Y W, kw_lrAdd_Z W]
        W.toProjective.polynomial ∈ Ideal.span {WP₁, WP₂} :=
    Ideal.mul_mem_left _ _ (kw_lrAdd_onCurve_mem_span W)
  have := add_mem hdiff hAdd
  simpa using this


-- @@ L103-114 verbatim
theorem kw_lrSymOC_scaled_mem_span_Z :
    (kw_lrAdd_Z W)^3 * aeval ![kw_lrSym_X W, kw_lrSym_Y W, kw_lrSym_Z W]
          W.toProjective.polynomial
      ∈ Ideal.span {WP₁, WP₂} := by
  refine kw_lrSymOC_scaled_mem_span_of W (kw_lrAdd_Z W) (kw_lrSym_Z W) ?_ ?_ ?_
  · have := kw_lrSym_minor_XZ_mem_span W
    rwa [show kw_lrSym_X W * kw_lrAdd_Z W - kw_lrSym_Z W * kw_lrAdd_X W
        = kw_lrAdd_Z W * kw_lrSym_X W - kw_lrSym_Z W * kw_lrAdd_X W from by ring] at this
  · have := kw_lrSym_minor_YZ_mem_span W
    rwa [show kw_lrSym_Y W * kw_lrAdd_Z W - kw_lrSym_Z W * kw_lrAdd_Y W
        = kw_lrAdd_Z W * kw_lrSym_Y W - kw_lrSym_Z W * kw_lrAdd_Y W from by ring] at this
  · rw [mul_comm, sub_self]; exact Ideal.zero_mem _


-- @@ L116-116 verbatim
end WeierstrassProjModel


-- @@ L118-118 verbatim
end


-- @@ L120-120 verbatim
end MEGA_KwLRSymOnCurveScaled_lean


-- @@ L122-122 verbatim
section MEGA_KwLRSymOnCurve_lean

-- @@ L123-123 verbatim
set_option autoImplicit false

-- @@ L124-124 verbatim
set_option maxHeartbeats 6400000

-- @@ L125-125 verbatim
set_option linter.unusedSimpArgs false


-- @@ L127-127 verbatim
noncomputable section


-- @@ L129-129 verbatim
open MvPolynomial WeierstrassCurve ProjWeierstrassCubicPrime


-- @@ L131-131 verbatim
namespace WeierstrassProjModel


-- @@ L133-133 verbatim
universe u v


-- @@ L135-135 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


-- @@ L137-137 verbatim
section Map


-- @@ L139-139 verbatim
variable {S : Type v} [CommRing S] (f : R →+* S)


-- @@ L141-145 verbatim
theorem kw_lrSymOC_map_WP₁ :
    MvPolynomial.map f (kw_lrAdd_WP₁ W) = kw_lrAdd_WP₁ (W.map f) := by
  simp only [kw_lrAdd_WP₁, MvPolynomial.map_rename,
    WeierstrassCurve.Projective.map_polynomial, WeierstrassCurve.Projective.map,
    WeierstrassCurve.toProjective]


-- @@ L147-151 verbatim
theorem kw_lrSymOC_map_WP₂ :
    MvPolynomial.map f (kw_lrAdd_WP₂ W) = kw_lrAdd_WP₂ (W.map f) := by
  simp only [kw_lrAdd_WP₂, MvPolynomial.map_rename,
    WeierstrassCurve.Projective.map_polynomial, WeierstrassCurve.Projective.map,
    WeierstrassCurve.toProjective]


-- @@ L153-157 verbatim
theorem kw_lrSymOC_map_lrSym_X :
    MvPolynomial.map f (kw_lrSym_X W) = kw_lrSym_X (W.map f) := by
  simp only [kw_lrSym_X, map_add, map_mul, map_neg, map_pow, MvPolynomial.map_C,
    MvPolynomial.map_X, map_ofNat, map_one, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_sub]


-- @@ L159-163 verbatim
theorem kw_lrSymOC_map_lrSym_Y :
    MvPolynomial.map f (kw_lrSym_Y W) = kw_lrSym_Y (W.map f) := by
  simp only [kw_lrSym_Y, map_add, map_mul, map_neg, map_pow, MvPolynomial.map_C,
    MvPolynomial.map_X, map_ofNat, map_one, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_sub]


-- @@ L165-169 verbatim
theorem kw_lrSymOC_map_lrSym_Z :
    MvPolynomial.map f (kw_lrSym_Z W) = kw_lrSym_Z (W.map f) := by
  simp only [kw_lrSym_Z, map_add, map_mul, map_neg, map_pow, MvPolynomial.map_C,
    MvPolynomial.map_X, map_ofNat, map_one, WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂,
    WeierstrassCurve.map_a₃, WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, map_sub]


-- @@ L171-182 verbatim
theorem kw_lrSymOC_map_W_lrSym :
    MvPolynomial.map f
        (aeval ![kw_lrSym_X W, kw_lrSym_Y W, kw_lrSym_Z W] W.toProjective.polynomial)
      = aeval ![kw_lrSym_X (W.map f), kw_lrSym_Y (W.map f), kw_lrSym_Z (W.map f)]
          (W.map f).toProjective.polynomial := by
  simp only [WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
    map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, MvPolynomial.map_C, MvPolynomial.algebraMap_eq,
    WeierstrassCurve.map_a₁, WeierstrassCurve.map_a₂, WeierstrassCurve.map_a₃,
    WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆,
    kw_lrSymOC_map_lrSym_X, kw_lrSymOC_map_lrSym_Y, kw_lrSymOC_map_lrSym_Z]


-- @@ L184-184 verbatim
end Map


-- @@ L186-186 verbatim
local notation "R₀" => MvPolynomial (Fin 5) ℤ


-- @@ L188-188 verbatim
abbrev kw_lrSymOC_W₀ : WeierstrassCurve R₀ := ⟨X 0, X 1, X 2, X 3, X 4⟩


-- @@ L190-190 verbatim
local notation "W₀" => kw_lrSymOC_W₀

-- @@ L191-191 verbatim
local notation "P₆₀" => MvPolynomial (Fin 3 ⊕ Fin 3) R₀

-- @@ L192-192 verbatim
local notation "WP₁₀" => kw_lrAdd_WP₁ W₀

-- @@ L193-193 verbatim
local notation "WP₂₀" => kw_lrAdd_WP₂ W₀


-- @@ L195-198 verbatim
theorem kw_lrSymOC_W₀_map :
    WeierstrassCurve.map kw_lrSymOC_W₀
        (MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]) = W := by
  ext <;> simp only [WeierstrassCurve.map, kw_lrSymOC_W₀, MvPolynomial.eval₂Hom_X'] <;> rfl


-- @@ L200-200 verbatim
section EngineHelpers


-- @@ L202-202 verbatim
variable {F : Type*} [CommRing F]


-- @@ L204-216 verbatim
theorem kw_lrSymOC_finSuccEquiv_map {S : Type*} [CommRing S] (f : F →+* S)
    (p : MvPolynomial (Fin 3) F) :
    finSuccEquiv S 2 (MvPolynomial.map f p)
      = Polynomial.map (MvPolynomial.map f) (finSuccEquiv F 2 p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_apply, MvPolynomial.eval₂_C]
  | add p q hp hq => simp [hp, hq, map_add, Polynomial.map_add]
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.map_X, hp, Polynomial.map_mul]
    congr 1
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [finSuccEquiv_apply]
    · simp [finSuccEquiv_apply]


-- @@ L218-225 verbatim
theorem kw_lrSymOC_wCubic_map (V : WeierstrassCurve.Projective F)
    {S : Type*} [CommRing S] (f : F →+* S) :
    (wCubic (V.map f)).toPoly
      = Polynomial.map (MvPolynomial.map f) (wCubic V).toPoly := by
  simp only [wCubic, Cubic.toPoly, WeierstrassCurve.Projective.map, WeierstrassCurve.map,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_pow,
    Polynomial.map_C, Polynomial.map_X, Polynomial.map_one, MvPolynomial.map_C,
    MvPolynomial.map_X, map_mul, map_sub, map_one, map_pow]


-- @@ L227-227 verbatim
end EngineHelpers


-- @@ L229-229 verbatim
section Engine


-- @@ L231-231 verbatim
variable {F : Type*} [CommRing F] [IsDomain F] (V : WeierstrassCurve.Projective F)


-- @@ L233-273 verbatim
theorem kw_lrSymOC_isDomain_quot_span_poly :
    IsDomain (MvPolynomial (Fin 3) F ⧸ Ideal.span {V.polynomial}) := by
  have hθ : Function.Injective (algebraMap F (FractionRing F)) :=
    IsFractionRing.injective F (FractionRing F)
  have hθ'' : Function.Injective
      (MvPolynomial.map (σ := Fin 2) (algebraMap F (FractionRing F))) :=
    MvPolynomial.map_injective _ hθ

  have hD : IsDomain (MvPolynomial (Fin 3) (FractionRing F)
      ⧸ Ideal.span {(V.map (algebraMap F (FractionRing F))).polynomial}) :=
    isDomain_quotient_span_polynomial (V.map (algebraMap F (FractionRing F)))

  have hcomap : (Ideal.span {(V.map (algebraMap F (FractionRing F))).polynomial}).comap
      (MvPolynomial.map (algebraMap F (FractionRing F)) :
        MvPolynomial (Fin 3) F →+* MvPolynomial (Fin 3) (FractionRing F))
      ≤ Ideal.span {V.polynomial} := by
    intro p hp
    simp only [Ideal.mem_comap, Ideal.mem_span_singleton] at hp ⊢

    have hp' : finSuccEquiv (FractionRing F) 2 (V.map (algebraMap F (FractionRing F))).polynomial
        ∣ finSuccEquiv (FractionRing F) 2 (MvPolynomial.map (algebraMap F (FractionRing F)) p) :=
      map_dvd (finSuccEquiv (FractionRing F) 2) hp
    rw [kw_lrSymOC_finSuccEquiv_map (algebraMap F (FractionRing F)) p,
        finSuccEquiv_polynomial (V.map (algebraMap F (FractionRing F))),
        kw_lrSymOC_wCubic_map V (algebraMap F (FractionRing F))] at hp'
    have hdvd : (wCubic V).toPoly ∣ finSuccEquiv F 2 p :=
      (Polynomial.map_dvd_map _ hθ'' (wCubic_toPoly_monic V)).mp (neg_dvd.mp hp')

    have hdvd' : finSuccEquiv F 2 V.polynomial ∣ finSuccEquiv F 2 p := by
      rw [finSuccEquiv_polynomial V]; exact hdvd.neg_left
    have := map_dvd (finSuccEquiv F 2).symm hdvd'
    simpa only [AlgEquiv.symm_apply_apply] using this

  have hH : Ideal.span {V.polynomial}
      ≤ (Ideal.span {(V.map (algebraMap F (FractionRing F))).polynomial}).comap
        (MvPolynomial.map (algebraMap F (FractionRing F))) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap,
      WeierstrassCurve.Projective.map_polynomial]
    exact Ideal.subset_span (Set.mem_singleton _)
  exact (Ideal.quotientMap_injective' hcomap :
    Function.Injective (Ideal.quotientMap _ _ hH)).isDomain _


-- @@ L275-275 verbatim
end Engine


-- @@ L277-278 verbatim
abbrev kw_lrSymOC_ℬ₀ :=
  MvPolynomial (Fin 3) R₀ ⧸ Ideal.span {kw_lrSymOC_W₀.toProjective.polynomial}


-- @@ L280-280 verbatim
local notation "ℬ₀" => kw_lrSymOC_ℬ₀


-- @@ L282-283 verbatim
instance kw_lrSymOC_isDomain_ℬ₀ : IsDomain ℬ₀ :=
  kw_lrSymOC_isDomain_quot_span_poly kw_lrSymOC_W₀.toProjective


-- @@ L285-348 verbatim
theorem kw_lrSymOC_isDomain_quotSpanPair :
    IsDomain (P₆₀ ⧸ Ideal.span {WP₁₀, WP₂₀}) := by
  classical
  let A := MvPolynomial (Fin 3) R₀
  let π : A →+* ℬ₀ := Ideal.Quotient.mk _
  let πC : R₀ →+* ℬ₀ := π.comp C
  let Wℬ : WeierstrassCurve ℬ₀ := kw_lrSymOC_W₀.map πC

  haveI hD : IsDomain
      (MvPolynomial (Fin 3) ℬ₀ ⧸ Ideal.span {Wℬ.toProjective.polynomial}) :=
    kw_lrSymOC_isDomain_quot_span_poly Wℬ.toProjective

  let e : P₆₀ ≃+* MvPolynomial (Fin 3) A :=
    (sumAlgEquiv R₀ (Fin 3) (Fin 3) : P₆₀ ≃ₐ[R₀] _).toRingEquiv
  let mπ : MvPolynomial (Fin 3) A →+* MvPolynomial (Fin 3) ℬ₀ := MvPolynomial.map π
  let ψ : P₆₀ →+* (MvPolynomial (Fin 3) ℬ₀ ⧸ Ideal.span {Wℬ.toProjective.polynomial}) :=
    (Ideal.Quotient.mk _).comp (mπ.comp (e : P₆₀ →+* _))
  have hsurj : Function.Surjective ψ :=
    (Ideal.Quotient.mk_surjective).comp
      ((MvPolynomial.map_surjective π Ideal.Quotient.mk_surjective).comp e.surjective)

  have heWP₁ : e WP₁₀
      = MvPolynomial.map (C : R₀ →+* A) kw_lrSymOC_W₀.toProjective.polynomial := by
    have h := DFunLike.congr_fun (sumAlgEquiv_comp_rename_inl R₀ (Fin 3) (Fin 3))
      kw_lrSymOC_W₀.toProjective.polynomial
    simpa [kw_lrAdd_WP₁, e] using h
  have heWP₂ : e WP₂₀ = C kw_lrSymOC_W₀.toProjective.polynomial := by
    have h := DFunLike.congr_fun (sumAlgEquiv_comp_rename_inr R₀ (Fin 3) (Fin 3))
      kw_lrSymOC_W₀.toProjective.polynomial
    simpa [kw_lrAdd_WP₂, e] using h

  have hker : RingHom.ker ψ = Ideal.span {WP₁₀, WP₂₀} := by

    have hkermπ : RingHom.ker mπ
        = Ideal.span {(C kw_lrSymOC_W₀.toProjective.polynomial :
            MvPolynomial (Fin 3) A)} := by
      rw [MvPolynomial.ker_map, Ideal.mk_ker, Ideal.map_span, Set.image_singleton]
    have hmap : mπ (e WP₁₀) = Wℬ.toProjective.polynomial := by
      rw [heWP₁]
      show (MvPolynomial.map π) ((MvPolynomial.map C) _) = _
      rw [MvPolynomial.map_map, ← WeierstrassCurve.Projective.map_polynomial]
    have hcomap :
        (Ideal.span {Wℬ.toProjective.polynomial}).comap mπ
          = Ideal.span {e WP₁₀, e WP₂₀} := by
      have hmapspan :
          (Ideal.span {e WP₁₀}).map mπ = Ideal.span {Wℬ.toProjective.polynomial} := by
        rw [Ideal.map_span, Set.image_singleton, hmap]
      rw [← hmapspan, Ideal.comap_map_of_surjective mπ
          (MvPolynomial.map_surjective π Ideal.Quotient.mk_surjective),
        ← RingHom.ker_eq_comap_bot, hkermπ, ← heWP₂, ← Ideal.span_union,
        Set.union_singleton, Set.pair_comm]

    have h₁ : RingHom.ker ψ
        = ((Ideal.span {Wℬ.toProjective.polynomial}).comap mπ).comap
            (e : P₆₀ →+* _) := by
      ext x; simp only [RingHom.mem_ker, Ideal.mem_comap]
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [h₁, hcomap, Ideal.comap_coe, ← Ideal.map_symm, Ideal.map_span, Set.image_pair,
      RingEquiv.symm_apply_apply, RingEquiv.symm_apply_apply]

  have heq : P₆₀ ⧸ Ideal.span {WP₁₀, WP₂₀}
      ≃+* (MvPolynomial (Fin 3) ℬ₀ ⧸ Ideal.span {Wℬ.toProjective.polynomial}) :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)
  exact heq.injective.isDomain _


-- @@ L350-395 verbatim
theorem kw_lrSymOC_lrAddZ_notMem_span :
    kw_lrAdd_Z W₀ ∉ Ideal.span {WP₁₀, WP₂₀} := by

  let ev₀ : R₀ →+* ℤ := MvPolynomial.eval (0 : Fin 5 → ℤ)
  let ev : P₆₀ →+* ℤ :=
    MvPolynomial.eval₂Hom ev₀ (Sum.elim ![0, 0, 1] ![1, 1, 1])

  have hevXl : ∀ i, ev (X (Sum.inl i)) = ![(0:ℤ), 0, 1] i := fun i => by
    simp [ev, Sum.elim_inl]
  have hevXr : ∀ i, ev (X (Sum.inr i)) = ![(1:ℤ), 1, 1] i := fun i => by
    simp [ev, Sum.elim_inr]
  have hevCX : ∀ j : Fin 5, ev (C (X j)) = 0 := fun j => by
    simp [ev, ev₀]
  have hevC : ∀ n : ℤ, ev (C ((n : R₀))) = n := fun n => by
    simp [ev, ev₀]
  intro hmem
  have hWP₁ : ev WP₁₀ = 0 := by
    show ev (rename Sum.inl kw_lrSymOC_W₀.toProjective.polynomial) = 0
    simp only [WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
      kw_lrSymOC_W₀, map_add, map_sub, map_mul, map_pow, rename_C, rename_X]
    simp only [hevXl, hevCX, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  have hWP₂ : ev WP₂₀ = 0 := by
    show ev (rename Sum.inr kw_lrSymOC_W₀.toProjective.polynomial) = 0
    simp only [WeierstrassCurve.Projective.polynomial, WeierstrassCurve.toProjective,
      kw_lrSymOC_W₀, map_add, map_sub, map_mul, map_pow, rename_C, rename_X]
    simp only [hevXr, hevCX, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  have hZ : ev (kw_lrAdd_Z W₀) = 1 := by
    simp only [kw_lrAdd_Z, kw_lrAdd_starZ, kw_lrAdd_c₁₂, kw_lrAdd_c₂₁,
      kw_lrSymOC_W₀, map_add, map_sub, map_mul, map_neg, map_pow,
      hevXl, hevXr, hevCX, C_mul, hevC,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    ring
  have hker : Ideal.span {WP₁₀, WP₂₀} ≤ RingHom.ker ev := by
    rw [Ideal.span_le]
    intro x hx
    rcases (Set.mem_insert_iff.mp hx) with rfl | hx'
    · exact hWP₁
    · rw [Set.mem_singleton_iff.mp hx']; exact hWP₂
  have habs : ev (kw_lrAdd_Z W₀) = 0 := hker hmem
  rw [hZ] at habs
  exact one_ne_zero habs


-- @@ L397-408 verbatim
theorem kw_lrSymOC_univ_mem_span :
    aeval ![kw_lrSym_X W₀, kw_lrSym_Y W₀, kw_lrSym_Z W₀]
        kw_lrSymOC_W₀.toProjective.polynomial
      ∈ Ideal.span {WP₁₀, WP₂₀} := by
  haveI := kw_lrSymOC_isDomain_quotSpanPair
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have hscaled := kw_lrSymOC_scaled_mem_span_Z W₀
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_pow] at hscaled
  have hZne : (Ideal.Quotient.mk (Ideal.span {WP₁₀, WP₂₀})) (kw_lrAdd_Z W₀) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact kw_lrSymOC_lrAddZ_notMem_span
  exact (mul_eq_zero.mp hscaled).resolve_left (pow_ne_zero 3 hZne)


-- @@ L410-425 verbatim
theorem kw_lrSym_onCurve_mem_span :
    aeval ![kw_lrSym_X W, kw_lrSym_Y W, kw_lrSym_Z W]
        W.toProjective.polynomial
      ∈ Ideal.span {kw_lrAdd_WP₁ W, kw_lrAdd_WP₂ W} := by
  let φ : R₀ →+* R := MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]
  have hW : kw_lrSymOC_W₀.map φ = W := kw_lrSymOC_W₀_map W

  have hmem := Ideal.mem_map_of_mem
    (MvPolynomial.map φ : P₆₀ →+* MvPolynomial (Fin 3 ⊕ Fin 3) R)
    kw_lrSymOC_univ_mem_span
  rw [Ideal.map_span, Set.image_pair, kw_lrSymOC_map_WP₁, kw_lrSymOC_map_WP₂,
    hW] at hmem
  have hrw := kw_lrSymOC_map_W_lrSym kw_lrSymOC_W₀ φ
  rw [hW] at hrw
  rw [← hrw]
  exact hmem


-- @@ L427-427 verbatim
end WeierstrassProjModel


-- @@ L429-429 verbatim
end


-- @@ L431-431 verbatim
end MEGA_KwLRSymOnCurve_lean


-- @@ L433-433 verbatim
section MEGA_KwLRAddQuotientGradedHom_lean

-- @@ L434-434 verbatim
set_option autoImplicit false

-- @@ L435-435 verbatim
set_option linter.unusedSimpArgs false


-- @@ L437-437 verbatim
noncomputable section


-- @@ L439-439 verbatim
open MvPolynomial WeierstrassCurve HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime

-- @@ L440-440 verbatim
open scoped TensorProduct


-- @@ L442-442 verbatim
namespace WeierstrassProjModel


-- @@ L444-444 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L446-446 verbatim
universe u


-- @@ L448-448 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


-- @@ L450-450 verbatim
local notation "P₆" => MvPolynomial (Fin 3 ⊕ Fin 3) R

-- @@ L451-451 verbatim
local notation "WP₁" => kw_lrAdd_WP₁ W

-- @@ L452-452 verbatim
local notation "WP₂" => kw_lrAdd_WP₂ W

-- @@ L453-453 verbatim
local notation "ℬ" => ProjModelRingCR W.toProjective


-- @@ L455-455 verbatim
def kw_lrAdd_vec : Fin 3 → P₆ := ![kw_lrAdd_X W, kw_lrAdd_Y W, kw_lrAdd_Z W]


-- @@ L457-461 verbatim
theorem kw_lrAdd_vec_isHomogeneous (k : Fin 3) : (kw_lrAdd_vec W k).IsHomogeneous 4 := by
  fin_cases k
  · exact kw_lrAdd_X_isHomogeneous W
  · exact kw_lrAdd_Y_isHomogeneous W
  · exact kw_lrAdd_Z_isHomogeneous W


-- @@ L463-464 verbatim
theorem kw_lrComul_WP₁_isHomogeneous : (WP₁).IsHomogeneous 3 :=
  (isHomogeneous_polynomial W.toProjective).rename_isHomogeneous


-- @@ L466-467 verbatim
theorem kw_lrComul_WP₂_isHomogeneous : (WP₂).IsHomogeneous 3 :=
  (isHomogeneous_polynomial W.toProjective).rename_isHomogeneous


-- @@ L469-475 verbatim
theorem kw_lrComul_biSpan_isHomogeneous :
    (Ideal.span {WP₁, WP₂}).IsHomogeneous (homogeneousSubmodule (Fin 3 ⊕ Fin 3) R) := by
  refine Ideal.homogeneous_span _ _ ?_
  rintro p (rfl | hp)
  · exact ⟨3, (mem_homogeneousSubmodule _ _).mpr (kw_lrComul_WP₁_isHomogeneous W)⟩
  · rw [Set.mem_singleton_iff] at hp; subst hp
    exact ⟨3, (mem_homogeneousSubmodule _ _).mpr (kw_lrComul_WP₂_isHomogeneous W)⟩


-- @@ L477-478 verbatim
def kw_lrComul_biIdeal : HomogeneousIdeal (homogeneousSubmodule (Fin 3 ⊕ Fin 3) R) :=
  ⟨Ideal.span {WP₁, WP₂}, kw_lrComul_biSpan_isHomogeneous W⟩


-- @@ L480-480 verbatim
abbrev KwLRBiRing : Type u := P₆ ⧸ (kw_lrComul_biIdeal W).toIdeal


-- @@ L482-482 verbatim
local notation "ℬ²" => KwLRBiRing W


-- @@ L484-485 verbatim
abbrev kw_lrComul_biGrading : ℕ → Submodule R (ℬ²) :=
  quotGradingSubmodule (homogeneousSubmodule (Fin 3 ⊕ Fin 3) R) (kw_lrComul_biIdeal W).toIdeal


-- @@ L487-487 verbatim
def kw_lrAdd_substHom : MvPolynomial (Fin 3) R →ₐ[R] P₆ := aeval (kw_lrAdd_vec W)


-- @@ L489-491 verbatim
@[simp]
theorem kw_lrAdd_substHom_X (k : Fin 3) :
    kw_lrAdd_substHom W (X k) = kw_lrAdd_vec W k := aeval_X _ _


-- @@ L493-495 verbatim
theorem kw_lrAdd_substHom_isHomogeneous {p : MvPolynomial (Fin 3) R} {n : ℕ}
    (hp : p.IsHomogeneous n) : (kw_lrAdd_substHom W p).IsHomogeneous (4 * n) :=
  hp.aeval (kw_lrAdd_vec W) (kw_lrAdd_vec_isHomogeneous W)


-- @@ L497-499 verbatim
theorem kw_lrAdd_substHom_polynomial_mem :
    kw_lrAdd_substHom W W.toProjective.polynomial ∈ (kw_lrComul_biIdeal W).toIdeal := by
  exact kw_lrAdd_onCurve_mem_span W


-- @@ L501-510 verbatim
noncomputable def kw_lrAdd_comulHom : (ℬ) →ₐ[R] (ℬ²) :=
  Ideal.Quotient.liftₐ (projModelHomogeneousIdealCR W.toProjective).toIdeal
    ((Ideal.Quotient.mkₐ R (kw_lrComul_biIdeal W).toIdeal).comp (kw_lrAdd_substHom W))
    (fun a ha => by
      refine (Ideal.Quotient.eq_zero_iff_mem).mpr ?_
      have hle : Ideal.span {W.toProjective.polynomial}
          ≤ (kw_lrComul_biIdeal W).toIdeal.comap (kw_lrAdd_substHom W).toRingHom :=
        Ideal.span_le.mpr
          (Set.singleton_subset_iff.mpr (kw_lrAdd_substHom_polynomial_mem W))
      exact hle ha)


-- @@ L512-516 verbatim
theorem kw_lrAdd_comulHom_mk (a : MvPolynomial (Fin 3) R) :
    kw_lrAdd_comulHom W
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal a)
      = Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrAdd_substHom W a) := by
  rfl


-- @@ L518-522 verbatim
theorem kw_lrAdd_comulHom_mk_X (k : Fin 3) :
    kw_lrAdd_comulHom W
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X k))
      = Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrAdd_vec W k) := by
  rw [kw_lrAdd_comulHom_mk, kw_lrAdd_substHom_X]


-- @@ L524-532 verbatim
theorem kw_lrAdd_comulHom_graded {n : ℕ} {x : ℬ}
    (hx : x ∈ projModelGradingCR W.toProjective n) :
    kw_lrAdd_comulHom W x ∈ kw_lrComul_biGrading W (4 * n) := by
  obtain ⟨a, ha, rfl⟩ := (mem_quotGradingSubmodule_iff _ _).mp hx
  show Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrAdd_substHom W a)
    ∈ kw_lrComul_biGrading W (4 * n)
  exact mk_mem_quotGradingSubmodule _ _
    ((mem_homogeneousSubmodule _ _).mpr
      (kw_lrAdd_substHom_isHomogeneous W ((mem_homogeneousSubmodule _ _).mp ha)))


-- @@ L534-534 verbatim
section TensorBridge


-- @@ L536-536 verbatim
open Algebra.TensorProduct


-- @@ L538-539 verbatim
noncomputable def kw_lrComul_incL : (ℬ) →ₐ[R] (ℬ) ⊗[R] (ℬ) :=
  Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := ℬ) (B := ℬ)


-- @@ L541-542 verbatim
noncomputable def kw_lrComul_incR : (ℬ) →ₐ[R] (ℬ) ⊗[R] (ℬ) :=
  Algebra.TensorProduct.includeRight (R := R) (A := ℬ) (B := ℬ)


-- @@ L544-549 verbatim
noncomputable def kw_lrComul_tensorProj : P₆ →ₐ[R] (ℬ) ⊗[R] (ℬ) :=
  aeval (Sum.elim
    (fun i => kw_lrComul_incL W
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X i)))
    (fun i => kw_lrComul_incR W
      (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X i))))


-- @@ L551-557 verbatim
theorem kw_lrComul_tensorProj_rename_inl :
    (kw_lrComul_tensorProj W).comp (rename Sum.inl)
      = (kw_lrComul_incL W).comp
          (Ideal.Quotient.mkₐ R (projModelHomogeneousIdealCR W.toProjective).toIdeal) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp only [AlgHom.comp_apply, kw_lrComul_tensorProj, rename_X, aeval_X, Sum.elim_inl,
    Ideal.Quotient.mkₐ_eq_mk]


-- @@ L559-565 verbatim
theorem kw_lrComul_tensorProj_rename_inr :
    (kw_lrComul_tensorProj W).comp (rename Sum.inr)
      = (kw_lrComul_incR W).comp
          (Ideal.Quotient.mkₐ R (projModelHomogeneousIdealCR W.toProjective).toIdeal) := by
  refine MvPolynomial.algHom_ext fun i => ?_
  simp only [AlgHom.comp_apply, kw_lrComul_tensorProj, rename_X, aeval_X, Sum.elim_inr,
    Ideal.Quotient.mkₐ_eq_mk]


-- @@ L567-570 verbatim
theorem kw_lrComul_mk_polynomial_eq_zero :
    Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
      W.toProjective.polynomial = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)


-- @@ L572-576 verbatim
theorem kw_lrComul_tensorProj_WP₁ : kw_lrComul_tensorProj W WP₁ = 0 := by
  have h := DFunLike.congr_fun (kw_lrComul_tensorProj_rename_inl W) W.toProjective.polynomial
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h
  show kw_lrComul_tensorProj W (rename Sum.inl W.toProjective.polynomial) = 0
  rw [h, kw_lrComul_mk_polynomial_eq_zero, map_zero]


-- @@ L578-582 verbatim
theorem kw_lrComul_tensorProj_WP₂ : kw_lrComul_tensorProj W WP₂ = 0 := by
  have h := DFunLike.congr_fun (kw_lrComul_tensorProj_rename_inr W) W.toProjective.polynomial
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk] at h
  show kw_lrComul_tensorProj W (rename Sum.inr W.toProjective.polynomial) = 0
  rw [h, kw_lrComul_mk_polynomial_eq_zero, map_zero]


-- @@ L584-592 verbatim
noncomputable def kw_lrComul_biToTensor : (ℬ²) →ₐ[R] (ℬ) ⊗[R] (ℬ) :=
  Ideal.Quotient.liftₐ (kw_lrComul_biIdeal W).toIdeal (kw_lrComul_tensorProj W)
    (fun a ha => by
      have hle : Ideal.span {WP₁, WP₂} ≤ RingHom.ker (kw_lrComul_tensorProj W).toRingHom :=
        Ideal.span_le.mpr (by
          rintro p (rfl | hp)
          · exact kw_lrComul_tensorProj_WP₁ W
          · rw [Set.mem_singleton_iff] at hp; subst hp; exact kw_lrComul_tensorProj_WP₂ W)
      exact hle ha)


-- @@ L594-594 verbatim
end TensorBridge


-- @@ L596-596 verbatim
end WeierstrassProjModel


-- @@ L598-598 verbatim
end


-- @@ L600-600 verbatim
end MEGA_KwLRAddQuotientGradedHom_lean


-- @@ L602-602 verbatim
section MEGA_KwLRSymQuotientGradedHom_lean

-- @@ L603-603 verbatim
set_option autoImplicit false

-- @@ L604-604 verbatim
set_option linter.unusedSimpArgs false


-- @@ L606-606 verbatim
noncomputable section


-- @@ L608-608 verbatim
open MvPolynomial WeierstrassCurve HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime

-- @@ L609-609 verbatim
open scoped TensorProduct


-- @@ L611-611 verbatim
namespace WeierstrassProjModel


-- @@ L613-613 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L615-615 verbatim
universe u


-- @@ L617-617 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


-- @@ L619-619 verbatim
local notation "P₆" => MvPolynomial (Fin 3 ⊕ Fin 3) R

-- @@ L620-620 verbatim
local notation "ℬ" => ProjModelRingCR W.toProjective

-- @@ L621-621 verbatim
local notation "ℬ²" => KwLRBiRing W


-- @@ L623-623 verbatim
def kw_lrSym_vec : Fin 3 → P₆ := ![kw_lrSym_X W, kw_lrSym_Y W, kw_lrSym_Z W]


-- @@ L625-629 verbatim
theorem kw_lrSym_vec_isHomogeneous (k : Fin 3) : (kw_lrSym_vec W k).IsHomogeneous 4 := by
  fin_cases k
  · exact kw_lrSym_X_isHomogeneous W
  · exact kw_lrSym_Y_isHomogeneous W
  · exact kw_lrSym_Z_isHomogeneous W


-- @@ L631-631 verbatim
def kw_lrSym_substHom : MvPolynomial (Fin 3) R →ₐ[R] P₆ := aeval (kw_lrSym_vec W)


-- @@ L633-635 verbatim
@[simp]
theorem kw_lrSym_substHom_X (k : Fin 3) :
    kw_lrSym_substHom W (X k) = kw_lrSym_vec W k := aeval_X _ _


-- @@ L637-639 verbatim
theorem kw_lrSym_substHom_isHomogeneous {p : MvPolynomial (Fin 3) R} {n : ℕ}
    (hp : p.IsHomogeneous n) : (kw_lrSym_substHom W p).IsHomogeneous (4 * n) :=
  hp.aeval (kw_lrSym_vec W) (kw_lrSym_vec_isHomogeneous W)


-- @@ L641-643 verbatim
theorem kw_lrSym_substHom_polynomial_mem :
    kw_lrSym_substHom W W.toProjective.polynomial ∈ (kw_lrComul_biIdeal W).toIdeal := by
  exact kw_lrSym_onCurve_mem_span W


-- @@ L645-654 verbatim
noncomputable def kw_lrSym_comulHom : (ℬ) →ₐ[R] (ℬ²) :=
  Ideal.Quotient.liftₐ (projModelHomogeneousIdealCR W.toProjective).toIdeal
    ((Ideal.Quotient.mkₐ R (kw_lrComul_biIdeal W).toIdeal).comp (kw_lrSym_substHom W))
    (fun a ha => by
      refine (Ideal.Quotient.eq_zero_iff_mem).mpr ?_
      have hle : Ideal.span {W.toProjective.polynomial}
          ≤ (kw_lrComul_biIdeal W).toIdeal.comap (kw_lrSym_substHom W).toRingHom :=
        Ideal.span_le.mpr
          (Set.singleton_subset_iff.mpr (kw_lrSym_substHom_polynomial_mem W))
      exact hle ha)


-- @@ L656-660 verbatim
theorem kw_lrSym_comulHom_mk (a : MvPolynomial (Fin 3) R) :
    kw_lrSym_comulHom W
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal a)
      = Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrSym_substHom W a) := by
  rfl


-- @@ L662-666 verbatim
theorem kw_lrSym_comulHom_mk_X (k : Fin 3) :
    kw_lrSym_comulHom W
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal (X k))
      = Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrSym_vec W k) := by
  rw [kw_lrSym_comulHom_mk, kw_lrSym_substHom_X]


-- @@ L668-676 verbatim
theorem kw_lrSym_comulHom_graded {n : ℕ} {x : ℬ}
    (hx : x ∈ projModelGradingCR W.toProjective n) :
    kw_lrSym_comulHom W x ∈ kw_lrComul_biGrading W (4 * n) := by
  obtain ⟨a, ha, rfl⟩ := (mem_quotGradingSubmodule_iff _ _).mp hx
  show Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrSym_substHom W a)
    ∈ kw_lrComul_biGrading W (4 * n)
  exact mk_mem_quotGradingSubmodule _ _
    ((mem_homogeneousSubmodule _ _).mpr
      (kw_lrSym_substHom_isHomogeneous W ((mem_homogeneousSubmodule _ _).mp ha)))


-- @@ L678-678 verbatim
end WeierstrassProjModel


-- @@ L680-680 verbatim
end


-- @@ L682-682 verbatim
end MEGA_KwLRSymQuotientGradedHom_lean


-- @@ L684-684 verbatim
section MEGA_KwLRChartHomAway_lean

-- @@ L685-685 verbatim
set_option autoImplicit false


-- @@ L687-687 verbatim
noncomputable section


-- @@ L689-689 verbatim
open MvPolynomial WeierstrassCurve HomogeneousLocalization HomogeneousIdealQuotientGrading


-- @@ L691-691 verbatim
namespace WeierstrassProjModel


-- @@ L693-693 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L695-695 verbatim
universe u


-- @@ L697-697 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


-- @@ L699-700 verbatim
set_option quotPrecheck false in
local notation "ℬ" => ProjModelRingCR W.toProjective

-- @@ L701-702 verbatim
set_option quotPrecheck false in
local notation "ℬ²" => KwLRBiRing W

-- @@ L703-704 verbatim
set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal

-- @@ L705-706 verbatim
set_option quotPrecheck false in
local notation "mk₆" => Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal


-- @@ L708-709 verbatim
instance kw_lrChart_biGrading_gradedAlgebra :
    GradedAlgebra (kw_lrComul_biGrading W) := inferInstance


-- @@ L711-713 verbatim
theorem kw_lrChart_mkX_mem_one (k : Fin 3) :
    mk₃ (X k : MvPolynomial (Fin 3) R) ∈ projModelGradingCR W.toProjective 1 :=
  mk_mem_quotGradingSubmodule _ _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R k))


-- @@ L715-718 verbatim
theorem kw_lrChart_mkAdd_mem_four (k : Fin 3) :
    mk₆ (kw_lrAdd_vec W k) ∈ kw_lrComul_biGrading W 4 :=
  mk_mem_quotGradingSubmodule _ _
    ((mem_homogeneousSubmodule _ _).mpr (kw_lrAdd_vec_isHomogeneous W k))


-- @@ L720-724 verbatim
set_option quotPrecheck false in

local notation "𝒜" k => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X k : MvPolynomial (Fin 3) R))


-- @@ L726-729 verbatim
set_option quotPrecheck false in

local notation "𝒜²" k => HomogeneousLocalization.Away (kw_lrComul_biGrading W)
  (Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrAdd_vec W k))


-- @@ L731-734 verbatim
theorem kw_lrChart_comulHom_mkX_pow (k : Fin 3) (n : ℕ) :
    kw_lrAdd_comulHom W (mk₃ (X k : MvPolynomial (Fin 3) R) ^ n)
      = mk₆ (kw_lrAdd_vec W k) ^ n := by
  rw [map_pow, kw_lrAdd_comulHom_mk_X]


-- @@ L736-741 verbatim
theorem kw_lrChart_powers_comap_le (k : Fin 3) :
    Submonoid.powers (mk₃ (X k : MvPolynomial (Fin 3) R))
      ≤ (Submonoid.powers (mk₆ (kw_lrAdd_vec W k))).comap
          (kw_lrAdd_comulHom W).toRingHom := by
  rintro a ⟨n, rfl⟩
  exact ⟨n, (kw_lrChart_comulHom_mkX_pow W k n).symm⟩


-- @@ L743-746 verbatim
noncomputable def kw_lrChart_locMap (k : Fin 3) :
    Localization.Away (mk₃ (X k : MvPolynomial (Fin 3) R))
      →+* Localization.Away (mk₆ (kw_lrAdd_vec W k)) :=
  IsLocalization.map _ (kw_lrAdd_comulHom W).toRingHom (kw_lrChart_powers_comap_le W k)


-- @@ L748-751 verbatim
noncomputable def kw_lrChart_aux (k : Fin 3) :
    (𝒜 k) →+* Localization.Away (mk₆ (kw_lrAdd_vec W k)) :=
  (kw_lrChart_locMap W k).comp
    (algebraMap (𝒜 k) (Localization.Away (mk₃ (X k : MvPolynomial (Fin 3) R))))


-- @@ L753-766 verbatim
theorem kw_lrChart_aux_mk (k : Fin 3) (n : ℕ) (a : ℬ)
    (ha : a ∈ projModelGradingCR W.toProjective (n • 1)) :
    kw_lrChart_aux W k
        (HomogeneousLocalization.Away.mk (projModelGradingCR W.toProjective)
          (kw_lrChart_mkX_mem_one W k) n a ha)
      = Localization.mk (kw_lrAdd_comulHom W a)
          (⟨mk₆ (kw_lrAdd_vec W k) ^ n, n, rfl⟩
            : Submonoid.powers (mk₆ (kw_lrAdd_vec W k))) := by
  show kw_lrChart_locMap W k
      (HomogeneousLocalization.Away.mk _ (kw_lrChart_mkX_mem_one W k) n a ha).val = _
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', kw_lrChart_locMap,
    IsLocalization.map_mk', ← Localization.mk_eq_mk']
  congr 1
  exact Subtype.ext (kw_lrChart_comulHom_mkX_pow W k n)


-- @@ L768-776 verbatim
noncomputable def kw_lrChart_witness (k : Fin 3) (n : ℕ) (a : ℬ)
    (ha : a ∈ projModelGradingCR W.toProjective (n • 1)) : (𝒜² k) :=
  HomogeneousLocalization.Away.mk (kw_lrComul_biGrading W)
    (kw_lrChart_mkAdd_mem_four W k) n (kw_lrAdd_comulHom W a)
    (by
      have ha' : a ∈ projModelGradingCR W.toProjective n := by simpa using ha
      have h4n : kw_lrAdd_comulHom W a ∈ kw_lrComul_biGrading W (4 * n) :=
        kw_lrAdd_comulHom_graded W ha'
      simpa [smul_eq_mul, Nat.mul_comm] using h4n)


-- @@ L778-784 verbatim
theorem kw_lrChart_witness_val (k : Fin 3) (n : ℕ) (a : ℬ)
    (ha : a ∈ projModelGradingCR W.toProjective (n • 1)) :
    (kw_lrChart_witness W k n a ha).val
      = kw_lrChart_aux W k
          (HomogeneousLocalization.Away.mk (projModelGradingCR W.toProjective)
            (kw_lrChart_mkX_mem_one W k) n a ha) := by
  rw [kw_lrChart_aux_mk]; rfl


-- @@ L786-793 verbatim
theorem kw_lrChart_aux_range_subset (k : Fin 3) :
    Set.range (kw_lrChart_aux W k)
      ⊆ Set.range (algebraMap (𝒜² k) (Localization.Away (mk₆ (kw_lrAdd_vec W k)))) := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (projModelGradingCR W.toProjective) (kw_lrChart_mkX_mem_one W k) z
  exact ⟨kw_lrChart_witness W k n a ha,
    (HomogeneousLocalization.algebraMap_apply _).trans (kw_lrChart_witness_val W k n a ha)⟩


-- @@ L795-799 verbatim
theorem kw_lrChart_aux_range_le (k : Fin 3) :
    (kw_lrChart_aux W k).range
      ≤ (algebraMap (𝒜² k) (Localization.Away (mk₆ (kw_lrAdd_vec W k)))).range := by
  rintro _ ⟨z, rfl⟩
  exact kw_lrChart_aux_range_subset W k ⟨z, rfl⟩


-- @@ L801-806 verbatim
noncomputable def kw_lrChart_away (k : Fin 3) : (𝒜 k) →+* (𝒜² k) := by
  let e := RingEquiv.ofLeftInverse
    (f := algebraMap (𝒜² k) (Localization.Away (mk₆ (kw_lrAdd_vec W k))))
    (h := (HomogeneousLocalization.val_injective _).hasLeftInverse.choose_spec)
  exact RingHom.comp (e.symm.toRingHom.comp (Subring.inclusion (kw_lrChart_aux_range_le W k)))
    (kw_lrChart_aux W k).rangeRestrict


-- @@ L808-808 verbatim
end WeierstrassProjModel


-- @@ L810-810 verbatim
end


-- @@ L812-812 verbatim
end MEGA_KwLRChartHomAway_lean


-- @@ L814-814 verbatim
section MEGA_KwProjPullbackAwayCoverCR_lean

-- @@ L815-815 verbatim
set_option autoImplicit false


-- @@ L817-817 verbatim
noncomputable section


-- @@ L819-819 verbatim
open MvPolynomial HomogeneousLocalization


-- @@ L821-821 verbatim
namespace WeierstrassProjModel


-- @@ L823-823 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L825-825 verbatim
universe u


-- @@ L827-827 verbatim
variable (R : Type u) [CommRing R]


-- @@ L829-829 verbatim
section ChartStructureMap


-- @@ L831-831 verbatim
variable (V : WeierstrassCurve.Projective R)


-- @@ L833-837 verbatim
set_option quotPrecheck false in

local notation "𝒜" i =>
  HomogeneousLocalization.Away (projModelGradingCR V)
    (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R))


-- @@ L839-841 verbatim
@[reducible] noncomputable def kw_pbac_awayAlgebra (i : Fin 3) : Algebra R (𝒜 i) :=
  ((fromZeroRingHom (projModelGradingCR V) _).comp
    (algebraMap R ((projModelGradingCR V) 0))).toAlgebra


-- @@ L843-843 verbatim
end ChartStructureMap


-- @@ L845-845 verbatim
end WeierstrassProjModel


-- @@ L847-847 verbatim
end

-- @@ L848-848 verbatim
end MEGA_KwProjPullbackAwayCoverCR_lean


-- @@ L850-850 verbatim
section MEGA_A1_Properness_lean


-- @@ L852-852 verbatim
set_option autoImplicit false


-- @@ L854-854 verbatim
namespace WeierstrassProjModel


-- @@ L856-856 verbatim
open HomogeneousIdealQuotientGrading


-- @@ L858-858 verbatim
section FiniteTypeEngine


-- @@ L860-860 verbatim
variable {ι A σ τ : Type*}

-- @@ L861-861 verbatim
variable [CommRing A] [AddMonoid ι]

-- @@ L862-862 verbatim
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [SetLike.GradedMonoid 𝒜]

-- @@ L863-863 verbatim
variable (I : Ideal A)

-- @@ L864-864 verbatim
variable [SetLike τ (A ⧸ I)] [AddSubmonoidClass τ (A ⧸ I)] (ℬ : ι → τ) [SetLike.GradedMonoid ℬ]


-- @@ L866-887 verbatim
theorem finiteType_gradeZero_quotient_of_mk_mem
    (hmem0 : ∀ a : A, a ∈ 𝒜 0 → Ideal.Quotient.mk I a ∈ ℬ 0)
    (hFT : Algebra.FiniteType (𝒜 0) A) :
    Algebra.FiniteType (ℬ 0) (A ⧸ I) := by
  classical
  obtain ⟨s, hs⟩ := hFT.out
  refine ⟨⟨s.image (Ideal.Quotient.mk I), ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have ha : a ∈ Algebra.adjoin (𝒜 0) (s : Set A) := hs.ge Algebra.mem_top
  induction ha using Algebra.adjoin_induction with
  | mem y hy =>
      exact Algebra.subset_adjoin (by
        simpa using Finset.mem_image_of_mem (Ideal.Quotient.mk I) hy)
  | algebraMap r =>
      have hr : Ideal.Quotient.mk I (algebraMap (𝒜 0) A r) ∈ ℬ 0 := hmem0 _ r.2
      exact Subalgebra.algebraMap_mem _ (⟨_, hr⟩ : ℬ 0)
  | add x y hx hy ihx ihy =>
      rw [map_add]; exact add_mem ihx ihy
  | mul x y hx hy ihx ihy =>
      rw [map_mul]; exact mul_mem ihx ihy


-- @@ L889-889 verbatim
end FiniteTypeEngine


-- @@ L891-891 verbatim
section BaseUpgrade


-- @@ L893-893 verbatim
variable {ι R A : Type*}

-- @@ L894-894 verbatim
variable [CommRing R] [CommRing A] [Algebra R A] [AddMonoid ι]

-- @@ L895-895 verbatim
variable (𝒜 : ι → Submodule R A) [SetLike.GradedMonoid 𝒜]


-- @@ L897-898 verbatim
theorem isScalarTower_gradeZero : IsScalarTower R (𝒜 0) A :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl


-- @@ L900-904 verbatim
theorem finiteType_gradeZero_of_finiteType_base (hFT : Algebra.FiniteType R A) :
    Algebra.FiniteType (𝒜 0) A := by
  haveI : IsScalarTower R (𝒜 0) A := isScalarTower_gradeZero 𝒜
  haveI := hFT
  exact Algebra.FiniteType.of_restrictScalars_finiteType R (𝒜 0) A


-- @@ L906-906 verbatim
end BaseUpgrade


-- @@ L908-908 verbatim
section QuotGradingSubmoduleDegreeZero


-- @@ L910-910 verbatim
variable {ι R A : Type*}

-- @@ L911-911 verbatim
variable [CommRing R] [CommRing A] [Algebra R A] [AddMonoid ι]

-- @@ L912-912 verbatim
variable (𝒜 : ι → Submodule R A) [SetLike.GradedMonoid 𝒜]

-- @@ L913-913 verbatim
variable (I : Ideal A)


-- @@ L915-918 verbatim
theorem quotGradingSubmodule_degreeZero_finiteType (hFT : Algebra.FiniteType (𝒜 0) A) :
    Algebra.FiniteType ((quotGradingSubmodule 𝒜 I) 0) (A ⧸ I) :=
  finiteType_gradeZero_quotient_of_mk_mem 𝒜 I (quotGradingSubmodule 𝒜 I)
    (fun _ ha => mk_mem_quotGradingSubmodule 𝒜 I ha) hFT


-- @@ L920-922 verbatim
instance quotGradingSubmoduleDegreeZeroFiniteType [Algebra.FiniteType (𝒜 0) A] :
    Algebra.FiniteType ((quotGradingSubmodule 𝒜 I) 0) (A ⧸ I) :=
  quotGradingSubmodule_degreeZero_finiteType 𝒜 I ‹_›


-- @@ L924-924 verbatim
end QuotGradingSubmoduleDegreeZero


-- @@ L926-926 verbatim
section MvPolynomialVenue


-- @@ L928-928 verbatim
open MvPolynomial


-- @@ L930-932 verbatim
instance homogeneousSubmoduleDegreeZeroFiniteType (σs R : Type*) [Finite σs] [CommRing R] :
    Algebra.FiniteType ((homogeneousSubmodule σs R) 0) (MvPolynomial σs R) :=
  finiteType_gradeZero_of_finiteType_base (homogeneousSubmodule σs R) inferInstance


-- @@ L934-934 verbatim
end MvPolynomialVenue


-- @@ L936-936 verbatim
section DegreeZeroEngine


-- @@ L938-938 verbatim
variable {ι R A : Type*}

-- @@ L939-939 verbatim
variable [CommRing R] [CommRing A] [Algebra R A] [AddMonoid ι]

-- @@ L940-940 verbatim
variable (𝒜 : ι → Submodule R A) [SetLike.GradedMonoid 𝒜]

-- @@ L941-941 verbatim
variable (I : Ideal A)


-- @@ L943-943 verbatim
end DegreeZeroEngine


-- @@ L945-945 verbatim
section PolynomialDegreeZero


-- @@ L947-947 verbatim
open MvPolynomial


-- @@ L949-958 verbatim
theorem mem_homogeneousSubmodule_zero_iff_exists_C {σ R : Type*} [CommSemiring R]
    {p : MvPolynomial σ R} :
    p ∈ homogeneousSubmodule σ R 0 ↔ ∃ r : R, C r = p := by
  constructor
  · intro hp
    rw [homogeneousSubmodule_zero] at hp
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hp
    exact ⟨r, by rwa [← algebraMap_eq]⟩
  · rintro ⟨r, rfl⟩
    exact (mem_homogeneousSubmodule _ _).mpr (isHomogeneous_C _ _)


-- @@ L960-960 verbatim
variable (σ R : Type*) [CommSemiring R]


-- @@ L962-962 verbatim
end PolynomialDegreeZero


-- @@ L964-964 verbatim
section ConstantCoeffKernel


-- @@ L966-966 verbatim
open MvPolynomial


-- @@ L968-968 verbatim
variable {σ R : Type*} [CommSemiring R]


-- @@ L970-973 verbatim
theorem constantCoeff_eq_zero_of_isHomogeneous_of_ne_zero {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsHomogeneous n) (hn : n ≠ 0) :
    constantCoeff p = 0 :=
  hp.coeff_eq_zero (by simpa using hn.symm)


-- @@ L975-978 verbatim
theorem span_le_ker_constantCoeff_of_forall_constantCoeff_eq_zero
    {S : Set (MvPolynomial σ R)} (h : ∀ p ∈ S, constantCoeff p = 0) :
    Ideal.span S ≤ RingHom.ker (constantCoeff : MvPolynomial σ R →+* R) :=
  Ideal.span_le.mpr fun p hp => RingHom.mem_ker.mpr (h p hp)


-- @@ L980-985 verbatim
theorem span_le_ker_constantCoeff_of_forall_isHomogeneous_pos
    {S : Set (MvPolynomial σ R)} (h : ∀ p ∈ S, ∃ n : ℕ, n ≠ 0 ∧ p.IsHomogeneous n) :
    Ideal.span S ≤ RingHom.ker (constantCoeff : MvPolynomial σ R →+* R) :=
  span_le_ker_constantCoeff_of_forall_constantCoeff_eq_zero fun p hp => by
    obtain ⟨n, hn, hhom⟩ := h p hp
    exact constantCoeff_eq_zero_of_isHomogeneous_of_ne_zero hhom hn


-- @@ L987-987 verbatim
end ConstantCoeffKernel


-- @@ L989-989 verbatim
section DegreeZeroIdentification


-- @@ L991-991 verbatim
open MvPolynomial


-- @@ L993-993 verbatim
variable {σ R : Type*} [CommRing R]

-- @@ L994-994 verbatim
variable (I : Ideal (MvPolynomial σ R))


-- @@ L996-999 verbatim
lemma quotGradingSubmodule_degreeZero_algebraMap_coe (r : R) :
    ((algebraMap R ((quotGradingSubmodule (homogeneousSubmodule σ R) I) 0) r :
        (quotGradingSubmodule (homogeneousSubmodule σ R) I) 0) : MvPolynomial σ R ⧸ I)
      = Ideal.Quotient.mk I (C r) := rfl


-- @@ L1001-1007 verbatim
theorem quotGradingSubmodule_degreeZero_algebraMap_surjective :
    Function.Surjective
      (algebraMap R ((quotGradingSubmodule (homogeneousSubmodule σ R) I) 0)) := by
  rintro ⟨b, hb⟩
  obtain ⟨p, hp, rfl⟩ := (mem_quotGradingSubmodule_iff (homogeneousSubmodule σ R) I).mp hb
  obtain ⟨r, rfl⟩ := mem_homogeneousSubmodule_zero_iff_exists_C.mp hp
  exact ⟨r, Subtype.ext rfl⟩


-- @@ L1009-1020 verbatim
theorem quotGradingSubmodule_degreeZero_algebraMap_injective
    (hI : I ≤ RingHom.ker (constantCoeff : MvPolynomial σ R →+* R)) :
    Function.Injective
      (algebraMap R ((quotGradingSubmodule (homogeneousSubmodule σ R) I) 0)) := by
  intro r s hrs
  have hval : Ideal.Quotient.mk I (C r) = Ideal.Quotient.mk I (C s) :=
    congrArg Subtype.val hrs
  have hsub : (C r - C s : MvPolynomial σ R) ∈ I := Ideal.Quotient.eq.mp hval
  rw [← map_sub] at hsub
  have h0 : constantCoeff (C (r - s) : MvPolynomial σ R) = 0 := RingHom.mem_ker.mp (hI hsub)
  rw [constantCoeff_C] at h0
  exact sub_eq_zero.mp h0


-- @@ L1022-1027 verbatim
theorem quotGradingSubmodule_degreeZero_algebraMap_bijective
    (hI : I ≤ RingHom.ker (constantCoeff : MvPolynomial σ R →+* R)) :
    Function.Bijective
      (algebraMap R ((quotGradingSubmodule (homogeneousSubmodule σ R) I) 0)) :=
  ⟨quotGradingSubmodule_degreeZero_algebraMap_injective I hI,
   quotGradingSubmodule_degreeZero_algebraMap_surjective I⟩


-- @@ L1029-1029 verbatim
end DegreeZeroIdentification


-- @@ L1031-1031 verbatim
end WeierstrassProjModel


-- @@ L1033-1033 verbatim
noncomputable section


-- @@ L1035-1035 verbatim
open AlgebraicGeometry CategoryTheory MvPolynomial HomogeneousLocalization

-- @@ L1036-1036 verbatim
open HomogeneousIdealQuotientGrading ProjWeierstrassCubicPrime


-- @@ L1038-1038 verbatim
namespace WeierstrassProjModel


-- @@ L1040-1040 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L1042-1042 verbatim
variable {R : Type*} [CommRing R]


-- @@ L1044-1049 verbatim
theorem projModelIdeal_le_ker_constantCoeffCR (V : WeierstrassCurve.Projective R) :
    (projModelHomogeneousIdealCR V).toIdeal
      ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin 3) R →+* R) :=
  span_le_ker_constantCoeff_of_forall_isHomogeneous_pos fun p hp => by
    rcases Set.mem_singleton_iff.mp hp with rfl
    exact ⟨3, by decide, isHomogeneous_polynomial V⟩


-- @@ L1051-1054 verbatim
theorem projModel_degreeZero_algebraMap_bijectiveCR (V : WeierstrassCurve.Projective R) :
    Function.Bijective (algebraMap R ((projModelGradingCR V) 0)) :=
  quotGradingSubmodule_degreeZero_algebraMap_bijective (projModelHomogeneousIdealCR V).toIdeal
    (projModelIdeal_le_ker_constantCoeffCR V)


-- @@ L1056-1059 verbatim
def projModelDegreeZeroRingEquivCR (V : WeierstrassCurve.Projective R) :
    R ≃+* ((projModelGradingCR V) 0) :=
  RingEquiv.ofBijective (algebraMap R ((projModelGradingCR V) 0))
    (projModel_degreeZero_algebraMap_bijectiveCR V)


-- @@ L1061-1079 verbatim
def projModelSpecDegreeZeroIsoCR (V : WeierstrassCurve.Projective R) :
    Spec (CommRingCat.of ((projModelGradingCR V) 0)) ≅ Spec (CommRingCat.of R) where
  hom := Spec.map (CommRingCat.ofHom (algebraMap R ((projModelGradingCR V) 0)))
  inv := Spec.map (CommRingCat.ofHom
    ((projModelDegreeZeroRingEquivCR V).symm : ((projModelGradingCR V) 0) →+* R))
  hom_inv_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show (algebraMap R ((projModelGradingCR V) 0)).comp
          ((projModelDegreeZeroRingEquivCR V).symm : ((projModelGradingCR V) 0) →+* R)
        = RingHom.id ((projModelGradingCR V) 0) from
        RingHom.ext fun x => (projModelDegreeZeroRingEquivCR V).apply_symm_apply x,
      CommRingCat.ofHom_id, Spec.map_id]
  inv_hom_id := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
      show ((projModelDegreeZeroRingEquivCR V).symm : ((projModelGradingCR V) 0) →+* R).comp
          (algebraMap R ((projModelGradingCR V) 0))
        = RingHom.id R from
        RingHom.ext fun x => (projModelDegreeZeroRingEquivCR V).symm_apply_apply x,
      CommRingCat.ofHom_id, Spec.map_id]


-- @@ L1081-1083 verbatim
instance projModel_isIso_spec_mapCR (V : WeierstrassCurve.Projective R) :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap R ((projModelGradingCR V) 0)))) :=
  inferInstanceAs (IsIso (projModelSpecDegreeZeroIsoCR V).hom)


-- @@ L1085-1089 verbatim
instance isProper_projModelStrCR (V : WeierstrassCurve.Projective R) :
    IsProper (projModelStrCR V) := by
  show IsProper (Proj.toSpecZero (projModelGradingCR V) ≫
    Spec.map (CommRingCat.ofHom (algebraMap R ((projModelGradingCR V) 0))))
  infer_instance


-- @@ L1091-1091 verbatim
end WeierstrassProjModel


-- @@ L1093-1093 verbatim
end


-- @@ L1095-1095 verbatim
end MEGA_A1_Properness_lean


-- @@ L1097-1097 verbatim
section MEGA_KwLRChartHomToTensor_lean

-- @@ L1098-1098 verbatim
set_option autoImplicit false

-- @@ L1099-1099 verbatim
set_option linter.unusedSimpArgs false

-- @@ L1100-1100 verbatim
set_option maxHeartbeats 1600000


-- @@ L1102-1102 verbatim
noncomputable section


-- @@ L1104-1104 verbatim
open MvPolynomial WeierstrassCurve HomogeneousLocalization HomogeneousIdealQuotientGrading

-- @@ L1105-1105 verbatim
open scoped TensorProduct


-- @@ L1107-1107 verbatim
namespace WeierstrassProjModel


-- @@ L1109-1109 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra

-- @@ L1110-1110 verbatim
attribute [local instance] kw_pbac_awayAlgebra


-- @@ L1112-1112 verbatim
universe u


-- @@ L1114-1114 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


-- @@ L1116-1117 verbatim
set_option quotPrecheck false in
local notation "ℬ" => ProjModelRingCR W.toProjective

-- @@ L1118-1119 verbatim
set_option quotPrecheck false in
local notation "ℬ²" => KwLRBiRing W

-- @@ L1120-1121 verbatim
set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal

-- @@ L1122-1123 verbatim
set_option quotPrecheck false in
local notation "mk₆" => Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal

-- @@ L1124-1127 verbatim
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

-- @@ L1128-1130 verbatim
set_option quotPrecheck false in
local notation "𝒜²" k => HomogeneousLocalization.Away (kw_lrComul_biGrading W)
  (Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrAdd_vec W k))


-- @@ L1132-1135 verbatim
noncomputable def kw_lrChart_gen (i m : Fin 3) : (𝒜 i) :=
  HomogeneousLocalization.mk
    ⟨1, ⟨mk₃ (X m : MvPolynomial (Fin 3) R), kw_lrChart_mkX_mem_one W m⟩,
        ⟨mk₃ (X i : MvPolynomial (Fin 3) R), kw_lrChart_mkX_mem_one W i⟩, ⟨1, pow_one _⟩⟩


-- @@ L1137-1141 verbatim
theorem kw_lrChart_gen_val (i m : Fin 3) :
    (kw_lrChart_gen W i m).val
      = Localization.mk (mk₃ (X m : MvPolynomial (Fin 3) R))
          (⟨mk₃ (X i : MvPolynomial (Fin 3) R), 1, pow_one _⟩
            : Submonoid.powers (mk₃ (X i : MvPolynomial (Fin 3) R))) := rfl


-- @@ L1143-1145 verbatim
noncomputable def kw_lrChart_dehom (i : Fin 3) :
    MvPolynomial (Fin 3) R →ₐ[R] (𝒜 i) :=
  aeval (kw_lrChart_gen W i)


-- @@ L1147-1157 verbatim
theorem kw_lrChart_dehom_C_val (i : Fin 3) (r : R) :
    (kw_lrChart_dehom W i (C r)).val
      = Localization.mk (mk₃ (C r : MvPolynomial (Fin 3) R))
          (1 : Submonoid.powers (mk₃ (X i : MvPolynomial (Fin 3) R))) := by
  rw [kw_lrChart_dehom, aeval_C]
  show (fromZeroRingHom (projModelGradingCR W.toProjective) _
      (algebraMap R ((projModelGradingCR W.toProjective) 0) r)).val = _

  simp only [fromZeroRingHom, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    HomogeneousLocalization.val_mk, quotGradingSubmodule_degreeZero_algebraMap_coe]
  rfl


-- @@ L1159-1164 verbatim
theorem kw_lrChart_dehom_X_val (i m : Fin 3) :
    (kw_lrChart_dehom W i (X m)).val
      = Localization.mk (mk₃ (X m : MvPolynomial (Fin 3) R))
          (⟨mk₃ (X i : MvPolynomial (Fin 3) R), 1, pow_one _⟩
            : Submonoid.powers (mk₃ (X i : MvPolynomial (Fin 3) R))) := by
  rw [kw_lrChart_dehom, aeval_X, kw_lrChart_gen_val]


-- @@ L1166-1190 verbatim
theorem kw_lrChart_dehom_monomial_val (i : Fin 3) (d : Fin 3 →₀ ℕ) (c : R) (n : ℕ)
    (hn : d 0 + d 1 + d 2 = n) :
    (kw_lrChart_dehom W i (monomial d c)).val
      = Localization.mk (mk₃ (monomial d c : MvPolynomial (Fin 3) R))
          (⟨mk₃ (X i : MvPolynomial (Fin 3) R) ^ n, n, rfl⟩
            : Submonoid.powers (mk₃ (X i : MvPolynomial (Fin 3) R))) := by
  have hmon : (monomial d c : MvPolynomial (Fin 3) R)
      = C c * (X 0 ^ d 0 * X 1 ^ d 1 * X 2 ^ d 2) := by
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ fun _ => pow_zero _,
      Fin.prod_univ_three]

  rw [hmon]
  simp only [map_mul, map_pow, HomogeneousLocalization.val_mul, HomogeneousLocalization.val_pow,
    kw_lrChart_dehom_C_val, kw_lrChart_dehom_X_val,
    Localization.mk_pow, Localization.mk_mul, one_mul, mul_one, one_pow]
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists]
  refine ⟨1, ?_⟩

  have key : (mk₃ (X i : MvPolynomial (Fin 3) R)) ^ n
      = (mk₃ (X i : MvPolynomial (Fin 3) R)) ^ d 0
        * (mk₃ (X i : MvPolynomial (Fin 3) R)) ^ d 1
        * (mk₃ (X i : MvPolynomial (Fin 3) R)) ^ d 2 := by
    rw [← pow_add, ← pow_add, hn]
  push_cast [key]
  ring


-- @@ L1192-1213 verbatim
set_option maxSynthPendingDepth 3 in

theorem kw_lrChart_dehom_isHomogeneous_val (i : Fin 3) (n : ℕ)
    (p : MvPolynomial (Fin 3) R) (hp : p.IsHomogeneous n) :
    (kw_lrChart_dehom W i p).val
      = Localization.mk (mk₃ p)
          (⟨mk₃ (X i : MvPolynomial (Fin 3) R) ^ n, n, rfl⟩
            : Submonoid.powers (mk₃ (X i : MvPolynomial (Fin 3) R))) := by
  conv_lhs => rw [MvPolynomial.as_sum p]
  conv_rhs => rw [MvPolynomial.as_sum p]

  haveI : AddMonoidHomClass
      ((𝒜 i) →+* Localization (Submonoid.powers (mk₃ (X i : MvPolynomial (Fin 3) R))))
      (𝒜 i) (Localization (Submonoid.powers (mk₃ (X i : MvPolynomial (Fin 3) R)))) :=
    RingHomClass.toAddMonoidHomClass
  rw [map_sum, ← HomogeneousLocalization.algebraMap_apply, map_sum, map_sum, Localization.mk_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [HomogeneousLocalization.algebraMap_apply]
  have hdeg : d.degree = n := by
    by_contra hne; exact MvPolynomial.mem_support_iff.mp hd (hp.coeff_eq_zero hne)
  exact kw_lrChart_dehom_monomial_val W i d (MvPolynomial.coeff d p) n
    (by rw [← hdeg, Finsupp.degree_eq_sum, Fin.sum_univ_three])


-- @@ L1215-1219 verbatim
theorem kw_lrChart_mk_mem_of_isHomogeneous (n : ℕ) (p : MvPolynomial (Fin 3) R)
    (hp : p.IsHomogeneous n) :
    mk₃ p ∈ projModelGradingCR W.toProjective (n • 1) := by
  rw [nsmul_one, Nat.cast_id]
  exact mk_mem_quotGradingSubmodule _ _ ((mem_homogeneousSubmodule _ _).mpr hp)


-- @@ L1221-1228 verbatim
theorem kw_lrChart_dehom_isHomogeneous (i : Fin 3) (n : ℕ)
    (p : MvPolynomial (Fin 3) R) (hp : p.IsHomogeneous n) :
    kw_lrChart_dehom W i p
      = HomogeneousLocalization.Away.mk (projModelGradingCR W.toProjective)
          (kw_lrChart_mkX_mem_one W i) n (mk₃ p)
          (kw_lrChart_mk_mem_of_isHomogeneous W n p hp) := by
  apply HomogeneousLocalization.val_injective
  rw [kw_lrChart_dehom_isHomogeneous_val W i n p hp, HomogeneousLocalization.Away.val_mk]


-- @@ L1230-1235 verbatim
theorem kw_lrChart_dehom_polynomial (i : Fin 3) :
    kw_lrChart_dehom W i W.toProjective.polynomial = 0 := by
  rw [kw_lrChart_dehom_isHomogeneous W i 3 _
    (ProjWeierstrassCubicPrime.isHomogeneous_polynomial W.toProjective)]
  refine HomogeneousLocalization.mk_eq_zero_of_num _ ?_
  exact Subtype.ext (kw_lrComul_mk_polynomial_eq_zero W)


-- @@ L1237-1237 verbatim
section TensorEv


-- @@ L1239-1239 verbatim
variable (i j : Fin 3)


-- @@ L1241-1242 verbatim
noncomputable def kw_lrChart_inL : (𝒜 i) →ₐ[R] (𝒜 i) ⊗[R] (𝒜 j) :=
  Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := 𝒜 i) (B := 𝒜 j)


-- @@ L1244-1245 verbatim
noncomputable def kw_lrChart_inR : (𝒜 j) →ₐ[R] (𝒜 i) ⊗[R] (𝒜 j) :=
  Algebra.TensorProduct.includeRight (R := R) (A := 𝒜 i) (B := 𝒜 j)


-- @@ L1247-1250 verbatim
noncomputable def kw_lrChart_ev :
    MvPolynomial (Fin 3 ⊕ Fin 3) R →ₐ[R] (𝒜 i) ⊗[R] (𝒜 j) :=
  aeval (Sum.elim (fun m => kw_lrChart_inL W i j (kw_lrChart_gen W i m))
                  (fun m => kw_lrChart_inR W i j (kw_lrChart_gen W j m)))


-- @@ L1252-1257 verbatim
theorem kw_lrChart_ev_rename_inl :
    (kw_lrChart_ev W i j).comp (rename Sum.inl)
      = (kw_lrChart_inL W i j).comp (kw_lrChart_dehom W i) := by
  refine MvPolynomial.algHom_ext fun m => ?_
  simp only [AlgHom.comp_apply, kw_lrChart_ev, rename_X, aeval_X, Sum.elim_inl,
    kw_lrChart_dehom]


-- @@ L1259-1264 verbatim
theorem kw_lrChart_ev_rename_inr :
    (kw_lrChart_ev W i j).comp (rename Sum.inr)
      = (kw_lrChart_inR W i j).comp (kw_lrChart_dehom W j) := by
  refine MvPolynomial.algHom_ext fun m => ?_
  simp only [AlgHom.comp_apply, kw_lrChart_ev, rename_X, aeval_X, Sum.elim_inr,
    kw_lrChart_dehom]


-- @@ L1266-1270 verbatim
theorem kw_lrChart_ev_WP₁ : kw_lrChart_ev W i j (kw_lrAdd_WP₁ W) = 0 := by
  have h := DFunLike.congr_fun (kw_lrChart_ev_rename_inl W i j) W.toProjective.polynomial
  simp only [AlgHom.comp_apply] at h
  show kw_lrChart_ev W i j (rename Sum.inl W.toProjective.polynomial) = 0
  rw [h, kw_lrChart_dehom_polynomial, map_zero]


-- @@ L1272-1276 verbatim
theorem kw_lrChart_ev_WP₂ : kw_lrChart_ev W i j (kw_lrAdd_WP₂ W) = 0 := by
  have h := DFunLike.congr_fun (kw_lrChart_ev_rename_inr W i j) W.toProjective.polynomial
  simp only [AlgHom.comp_apply] at h
  show kw_lrChart_ev W i j (rename Sum.inr W.toProjective.polynomial) = 0
  rw [h, kw_lrChart_dehom_polynomial, map_zero]


-- @@ L1278-1287 verbatim
noncomputable def kw_lrChart_ev' : (ℬ²) →ₐ[R] (𝒜 i) ⊗[R] (𝒜 j) :=
  Ideal.Quotient.liftₐ (kw_lrComul_biIdeal W).toIdeal (kw_lrChart_ev W i j)
    (fun a ha => by
      have hle : Ideal.span {kw_lrAdd_WP₁ W, kw_lrAdd_WP₂ W}
          ≤ RingHom.ker (kw_lrChart_ev W i j).toRingHom :=
        Ideal.span_le.mpr (by
          rintro p (rfl | hp)
          · exact kw_lrChart_ev_WP₁ W i j
          · rw [Set.mem_singleton_iff] at hp; subst hp; exact kw_lrChart_ev_WP₂ W i j)
      exact hle ha)


-- @@ L1289-1289 verbatim
end TensorEv


-- @@ L1291-1291 verbatim
section ToTensor


-- @@ L1293-1293 verbatim
variable (i j k : Fin 3)


-- @@ L1295-1295 verbatim
instance kw_lrChart_tensorCommRing : CommRing ((𝒜 i) ⊗[R] (𝒜 j)) := inferInstance


-- @@ L1297-1298 verbatim
noncomputable def kw_lrChart_u : (𝒜 i) ⊗[R] (𝒜 j) :=
  kw_lrChart_ev' W i j (mk₆ (kw_lrAdd_vec W k))


-- @@ L1300-1305 verbatim
theorem kw_lrChart_powers_ev'_comap_le :
    Submonoid.powers (mk₆ (kw_lrAdd_vec W k))
      ≤ (Submonoid.powers (kw_lrChart_u W i j k)).comap
          (kw_lrChart_ev' W i j).toRingHom := by
  rintro a ⟨n, rfl⟩
  exact ⟨n, by rw [map_pow]; rfl⟩


-- @@ L1307-1311 verbatim
noncomputable def kw_lrChart_toTensorLoc :
    Localization.Away (mk₆ (kw_lrAdd_vec W k))
      →+* Localization.Away (kw_lrChart_u W i j k) :=
  IsLocalization.map _ (kw_lrChart_ev' W i j).toRingHom
    (kw_lrChart_powers_ev'_comap_le W i j k)


-- @@ L1313-1316 verbatim
noncomputable def kw_lrChart_toTensor :
    (𝒜² k) →+* Localization.Away (kw_lrChart_u W i j k) :=
  (kw_lrChart_toTensorLoc W i j k).comp
    (algebraMap (𝒜² k) (Localization.Away (mk₆ (kw_lrAdd_vec W k))))


-- @@ L1318-1318 verbatim
end ToTensor


-- @@ L1320-1320 verbatim
section Composite


-- @@ L1322-1322 verbatim
variable (i j k : Fin 3)


-- @@ L1324-1326 verbatim
noncomputable def kw_lrChart_tensor :
    (𝒜 k) →+* Localization.Away (kw_lrChart_u W i j k) :=
  (kw_lrChart_toTensor W i j k).comp (kw_lrChart_away W k)


-- @@ L1328-1328 verbatim
end Composite


-- @@ L1330-1330 verbatim
end WeierstrassProjModel


-- @@ L1332-1332 verbatim
end


-- @@ L1334-1334 verbatim
end MEGA_KwLRChartHomToTensor_lean


-- @@ L1336-1336 verbatim
section MEGA_KwLRSymChartHomAway_lean

-- @@ L1337-1337 verbatim
set_option autoImplicit false


-- @@ L1339-1339 verbatim
noncomputable section


-- @@ L1341-1341 verbatim
open MvPolynomial WeierstrassCurve HomogeneousLocalization HomogeneousIdealQuotientGrading


-- @@ L1343-1343 verbatim
namespace WeierstrassProjModel


-- @@ L1345-1345 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L1347-1347 verbatim
universe u


-- @@ L1349-1349 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


-- @@ L1351-1352 verbatim
set_option quotPrecheck false in
local notation "ℬ" => ProjModelRingCR W.toProjective

-- @@ L1353-1354 verbatim
set_option quotPrecheck false in
local notation "ℬ²" => KwLRBiRing W

-- @@ L1355-1356 verbatim
set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal

-- @@ L1357-1358 verbatim
set_option quotPrecheck false in
local notation "mk₆" => Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal


-- @@ L1360-1363 verbatim
theorem kw_lrSymChart_mkSym_mem_four (k : Fin 3) :
    mk₆ (kw_lrSym_vec W k) ∈ kw_lrComul_biGrading W 4 :=
  mk_mem_quotGradingSubmodule _ _
    ((mem_homogeneousSubmodule _ _).mpr (kw_lrSym_vec_isHomogeneous W k))


-- @@ L1365-1369 verbatim
set_option quotPrecheck false in

local notation "𝒜" k => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X k : MvPolynomial (Fin 3) R))


-- @@ L1371-1374 verbatim
set_option quotPrecheck false in

local notation "𝒜²ₛ" k => HomogeneousLocalization.Away (kw_lrComul_biGrading W)
  (Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrSym_vec W k))


-- @@ L1376-1379 verbatim
theorem kw_lrSymChart_comulHom_mkX_pow (k : Fin 3) (n : ℕ) :
    kw_lrSym_comulHom W (mk₃ (X k : MvPolynomial (Fin 3) R) ^ n)
      = mk₆ (kw_lrSym_vec W k) ^ n := by
  rw [map_pow, kw_lrSym_comulHom_mk_X]


-- @@ L1381-1386 verbatim
theorem kw_lrSymChart_powers_comap_le (k : Fin 3) :
    Submonoid.powers (mk₃ (X k : MvPolynomial (Fin 3) R))
      ≤ (Submonoid.powers (mk₆ (kw_lrSym_vec W k))).comap
          (kw_lrSym_comulHom W).toRingHom := by
  rintro a ⟨n, rfl⟩
  exact ⟨n, (kw_lrSymChart_comulHom_mkX_pow W k n).symm⟩


-- @@ L1388-1391 verbatim
noncomputable def kw_lrSymChart_locMap (k : Fin 3) :
    Localization.Away (mk₃ (X k : MvPolynomial (Fin 3) R))
      →+* Localization.Away (mk₆ (kw_lrSym_vec W k)) :=
  IsLocalization.map _ (kw_lrSym_comulHom W).toRingHom (kw_lrSymChart_powers_comap_le W k)


-- @@ L1393-1396 verbatim
noncomputable def kw_lrSymChart_aux (k : Fin 3) :
    (𝒜 k) →+* Localization.Away (mk₆ (kw_lrSym_vec W k)) :=
  (kw_lrSymChart_locMap W k).comp
    (algebraMap (𝒜 k) (Localization.Away (mk₃ (X k : MvPolynomial (Fin 3) R))))


-- @@ L1398-1411 verbatim
theorem kw_lrSymChart_aux_mk (k : Fin 3) (n : ℕ) (a : ℬ)
    (ha : a ∈ projModelGradingCR W.toProjective (n • 1)) :
    kw_lrSymChart_aux W k
        (HomogeneousLocalization.Away.mk (projModelGradingCR W.toProjective)
          (kw_lrChart_mkX_mem_one W k) n a ha)
      = Localization.mk (kw_lrSym_comulHom W a)
          (⟨mk₆ (kw_lrSym_vec W k) ^ n, n, rfl⟩
            : Submonoid.powers (mk₆ (kw_lrSym_vec W k))) := by
  show kw_lrSymChart_locMap W k
      (HomogeneousLocalization.Away.mk _ (kw_lrChart_mkX_mem_one W k) n a ha).val = _
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', kw_lrSymChart_locMap,
    IsLocalization.map_mk', ← Localization.mk_eq_mk']
  congr 1
  exact Subtype.ext (kw_lrSymChart_comulHom_mkX_pow W k n)


-- @@ L1413-1421 verbatim
noncomputable def kw_lrSymChart_witness (k : Fin 3) (n : ℕ) (a : ℬ)
    (ha : a ∈ projModelGradingCR W.toProjective (n • 1)) : (𝒜²ₛ k) :=
  HomogeneousLocalization.Away.mk (kw_lrComul_biGrading W)
    (kw_lrSymChart_mkSym_mem_four W k) n (kw_lrSym_comulHom W a)
    (by
      have ha' : a ∈ projModelGradingCR W.toProjective n := by simpa using ha
      have h4n : kw_lrSym_comulHom W a ∈ kw_lrComul_biGrading W (4 * n) :=
        kw_lrSym_comulHom_graded W ha'
      simpa [smul_eq_mul, Nat.mul_comm] using h4n)


-- @@ L1423-1429 verbatim
theorem kw_lrSymChart_witness_val (k : Fin 3) (n : ℕ) (a : ℬ)
    (ha : a ∈ projModelGradingCR W.toProjective (n • 1)) :
    (kw_lrSymChart_witness W k n a ha).val
      = kw_lrSymChart_aux W k
          (HomogeneousLocalization.Away.mk (projModelGradingCR W.toProjective)
            (kw_lrChart_mkX_mem_one W k) n a ha) := by
  rw [kw_lrSymChart_aux_mk]; rfl


-- @@ L1431-1438 verbatim
theorem kw_lrSymChart_aux_range_subset (k : Fin 3) :
    Set.range (kw_lrSymChart_aux W k)
      ⊆ Set.range (algebraMap (𝒜²ₛ k) (Localization.Away (mk₆ (kw_lrSym_vec W k)))) := by
  rintro _ ⟨z, rfl⟩
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (projModelGradingCR W.toProjective) (kw_lrChart_mkX_mem_one W k) z
  exact ⟨kw_lrSymChart_witness W k n a ha,
    (HomogeneousLocalization.algebraMap_apply _).trans (kw_lrSymChart_witness_val W k n a ha)⟩


-- @@ L1440-1444 verbatim
theorem kw_lrSymChart_aux_range_le (k : Fin 3) :
    (kw_lrSymChart_aux W k).range
      ≤ (algebraMap (𝒜²ₛ k) (Localization.Away (mk₆ (kw_lrSym_vec W k)))).range := by
  rintro _ ⟨z, rfl⟩
  exact kw_lrSymChart_aux_range_subset W k ⟨z, rfl⟩


-- @@ L1446-1452 verbatim
noncomputable def kw_lrSymChart_away (k : Fin 3) : (𝒜 k) →+* (𝒜²ₛ k) := by
  let e := RingEquiv.ofLeftInverse
    (f := algebraMap (𝒜²ₛ k) (Localization.Away (mk₆ (kw_lrSym_vec W k))))
    (h := (HomogeneousLocalization.val_injective _).hasLeftInverse.choose_spec)
  exact RingHom.comp (e.symm.toRingHom.comp
      (Subring.inclusion (kw_lrSymChart_aux_range_le W k)))
    (kw_lrSymChart_aux W k).rangeRestrict


-- @@ L1454-1454 verbatim
end WeierstrassProjModel


-- @@ L1456-1456 verbatim
end

-- @@ L1457-1457 verbatim
end MEGA_KwLRSymChartHomAway_lean


-- @@ L1459-1459 verbatim
section MEGA_KwLRSymChartHomToTensor_lean

-- @@ L1460-1460 verbatim
set_option autoImplicit false

-- @@ L1461-1461 verbatim
set_option linter.unusedSimpArgs false

-- @@ L1462-1462 verbatim
set_option maxHeartbeats 1600000


-- @@ L1464-1464 verbatim
noncomputable section


-- @@ L1466-1466 verbatim
open MvPolynomial WeierstrassCurve HomogeneousLocalization HomogeneousIdealQuotientGrading

-- @@ L1467-1467 verbatim
open scoped TensorProduct


-- @@ L1469-1469 verbatim
namespace WeierstrassProjModel


-- @@ L1471-1471 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra

-- @@ L1472-1472 verbatim
attribute [local instance] kw_pbac_awayAlgebra


-- @@ L1474-1474 verbatim
universe u


-- @@ L1476-1476 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


-- @@ L1478-1479 verbatim
set_option quotPrecheck false in
local notation "ℬ" => ProjModelRingCR W.toProjective

-- @@ L1480-1481 verbatim
set_option quotPrecheck false in
local notation "mk₆" => Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal

-- @@ L1482-1485 verbatim
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

-- @@ L1486-1488 verbatim
set_option quotPrecheck false in
local notation "𝒜²ₛ" k => HomogeneousLocalization.Away (kw_lrComul_biGrading W)
  (Ideal.Quotient.mk (kw_lrComul_biIdeal W).toIdeal (kw_lrSym_vec W k))


-- @@ L1490-1490 verbatim
section ToTensor


-- @@ L1492-1492 verbatim
variable (i j k : Fin 3)


-- @@ L1494-1495 verbatim
noncomputable def kw_lrSymChart_u : (𝒜 i) ⊗[R] (𝒜 j) :=
  kw_lrChart_ev' W i j (mk₆ (kw_lrSym_vec W k))


-- @@ L1497-1502 verbatim
theorem kw_lrSymChart_powers_ev'_comap_le :
    Submonoid.powers (mk₆ (kw_lrSym_vec W k))
      ≤ (Submonoid.powers (kw_lrSymChart_u W i j k)).comap
          (kw_lrChart_ev' W i j).toRingHom := by
  rintro a ⟨n, rfl⟩
  exact ⟨n, by rw [map_pow]; rfl⟩


-- @@ L1504-1508 verbatim
noncomputable def kw_lrSymChart_toTensorLoc :
    Localization.Away (mk₆ (kw_lrSym_vec W k))
      →+* Localization.Away (kw_lrSymChart_u W i j k) :=
  IsLocalization.map _ (kw_lrChart_ev' W i j).toRingHom
    (kw_lrSymChart_powers_ev'_comap_le W i j k)


-- @@ L1510-1513 verbatim
noncomputable def kw_lrSymChart_toTensor :
    (𝒜²ₛ k) →+* Localization.Away (kw_lrSymChart_u W i j k) :=
  (kw_lrSymChart_toTensorLoc W i j k).comp
    (algebraMap (𝒜²ₛ k) (Localization.Away (mk₆ (kw_lrSym_vec W k))))


-- @@ L1515-1515 verbatim
end ToTensor


-- @@ L1517-1517 verbatim
section Composite


-- @@ L1519-1519 verbatim
variable (i j k : Fin 3)


-- @@ L1521-1523 verbatim
noncomputable def kw_lrSymChart_tensor :
    (𝒜 k) →+* Localization.Away (kw_lrSymChart_u W i j k) :=
  (kw_lrSymChart_toTensor W i j k).comp (kw_lrSymChart_away W k)


-- @@ L1525-1525 verbatim
end Composite


-- @@ L1527-1527 verbatim
end WeierstrassProjModel


-- @@ L1529-1529 verbatim
end


-- @@ L1531-1531 verbatim
end MEGA_KwLRSymChartHomToTensor_lean


-- @@ L1533-1533 verbatim
section MEGA_KwLRSixUCoverage_lean

-- @@ L1534-1534 verbatim
set_option autoImplicit false

-- @@ L1535-1535 verbatim
set_option linter.unusedSimpArgs false

-- @@ L1536-1536 verbatim
set_option maxHeartbeats 1600000


-- @@ L1538-1538 verbatim
noncomputable section


-- @@ L1540-1540 verbatim
open MvPolynomial WeierstrassCurve HomogeneousLocalization

-- @@ L1541-1541 verbatim
open scoped TensorProduct


-- @@ L1543-1543 verbatim
namespace WeierstrassProjModel


-- @@ L1545-1545 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra

-- @@ L1546-1546 verbatim
attribute [local instance] kw_pbac_awayAlgebra


-- @@ L1548-1548 verbatim
universe u


-- @@ L1550-1550 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


-- @@ L1552-1555 verbatim
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))


-- @@ L1557-1558 verbatim
noncomputable def kw_lrSixU (i j : Fin 3) : Fin 3 ⊕ Fin 3 → (𝒜 i) ⊗[R] (𝒜 j) :=
  Sum.elim (kw_lrChart_u W i j) (kw_lrSymChart_u W i j)


-- @@ L1560-1562 verbatim
def KwLRSixUCoverage : Prop :=
  ∀ (i j : Fin 3),
    Ideal.span (Set.range (kw_lrSixU W i j)) = (⊤ : Ideal ((𝒜 i) ⊗[R] (𝒜 j)))


-- @@ L1564-1564 verbatim
end WeierstrassProjModel


-- @@ L1566-1566 verbatim
end

-- @@ L1567-1567 verbatim
end MEGA_KwLRSixUCoverage_lean


-- @@ L1569-1569 verbatim
section MEGA_KwLRPerChartGlue_lean

-- @@ L1570-1570 verbatim
set_option autoImplicit false

-- @@ L1571-1571 verbatim
set_option linter.unusedSimpArgs false

-- @@ L1572-1572 verbatim
set_option maxHeartbeats 1600000


-- @@ L1574-1574 verbatim
noncomputable section


-- @@ L1576-1576 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

-- @@ L1577-1577 verbatim
open MvPolynomial WeierstrassCurve HomogeneousLocalization

-- @@ L1578-1578 verbatim
open scoped TensorProduct


-- @@ L1580-1580 verbatim
namespace WeierstrassProjModel


-- @@ L1582-1582 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra

-- @@ L1583-1583 verbatim
attribute [local instance] kw_pbac_awayAlgebra


-- @@ L1585-1585 verbatim
universe u


-- @@ L1587-1587 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


-- @@ L1589-1592 verbatim
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))


-- @@ L1594-1595 verbatim
set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective


-- @@ L1597-1600 verbatim
noncomputable def kw_lrSixU_cover (i j : Fin 3)
    (h : Ideal.span (Set.range (kw_lrSixU W i j)) = ⊤) :
    (Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j)))).AffineOpenCover :=
  Scheme.affineOpenCoverOfSpanRangeEqTop (R := .of ((𝒜 i) ⊗[R] (𝒜 j))) (kw_lrSixU W i j) h


-- @@ L1602-1602 verbatim
section ToE


-- @@ L1604-1604 verbatim
variable (i j : Fin 3)


-- @@ L1606-1612 verbatim
noncomputable def kw_lrSixU_toE :
    ∀ l : Fin 3 ⊕ Fin 3,
      Spec (CommRingCat.of (Localization.Away (kw_lrSixU W i j l))) ⟶ E
  | .inl k => Spec.map (CommRingCat.ofHom (kw_lrChart_tensor W i j k))
      ≫ Proj.awayι (projModelGradingCR W.toProjective) _ (kw_lrChart_mkX_mem_one W k) one_pos
  | .inr k => Spec.map (CommRingCat.ofHom (kw_lrSymChart_tensor W i j k))
      ≫ Proj.awayι (projModelGradingCR W.toProjective) _ (kw_lrChart_mkX_mem_one W k) one_pos


-- @@ L1614-1614 verbatim
end ToE


-- @@ L1616-1620 verbatim
noncomputable def kw_lrSixU_locMap (i j : Fin 3) (l : Fin 3 ⊕ Fin 3) :
    Spec (CommRingCat.of (Localization.Away (kw_lrSixU W i j l)))
      ⟶ Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j))) :=
  Spec.map (CommRingCat.ofHom
    (algebraMap ((𝒜 i) ⊗[R] (𝒜 j)) (Localization.Away (kw_lrSixU W i j l))))


-- @@ L1622-1627 verbatim
def KwLRPerChartCompat : Prop :=
  ∀ (i j : Fin 3) (l l' : Fin 3 ⊕ Fin 3),
    pullback.fst (kw_lrSixU_locMap W i j l) (kw_lrSixU_locMap W i j l')
        ≫ kw_lrSixU_toE W i j l
      = pullback.snd (kw_lrSixU_locMap W i j l) (kw_lrSixU_locMap W i j l')
        ≫ kw_lrSixU_toE W i j l'


-- @@ L1629-1633 verbatim
noncomputable def kw_lrPerChart_toE (hcov : KwLRSixUCoverage W)
    (hcompat : KwLRPerChartCompat W) (i j : Fin 3) :
    Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j))) ⟶ E :=
  (kw_lrSixU_cover W i j (hcov i j)).openCover.glueMorphisms
    (kw_lrSixU_toE W i j) (hcompat i j)


-- @@ L1635-1635 verbatim
end WeierstrassProjModel


-- @@ L1637-1637 verbatim
end

-- @@ L1638-1638 verbatim
end MEGA_KwLRPerChartGlue_lean


-- @@ L1640-1640 verbatim
section MEGA_KwProjPullbackAwayCoverCRCover_lean

-- @@ L1641-1641 verbatim
set_option autoImplicit false


-- @@ L1643-1643 verbatim
noncomputable section


-- @@ L1645-1645 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial

-- @@ L1646-1646 verbatim
open HomogeneousLocalization HomogeneousIdealQuotientGrading

-- @@ L1647-1647 verbatim
open scoped TensorProduct


-- @@ L1649-1649 verbatim
namespace WeierstrassProjModel


-- @@ L1651-1651 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L1653-1653 verbatim
universe u


-- @@ L1655-1655 verbatim
variable (R : Type u) [CommRing R]


-- @@ L1657-1657 verbatim
section CoverCRPort


-- @@ L1659-1659 verbatim
variable (V : WeierstrassCurve.Projective R)


-- @@ L1661-1667 verbatim
open MvPolynomial in

theorem kw_pbac_mk_X_mem_one_CR (i : Fin 3) :
    Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (X i : MvPolynomial (Fin 3) R)
      ∈ projModelGradingCR V 1 :=
  mk_mem_quotGradingSubmodule _ _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R i))


-- @@ L1669-1692 verbatim
theorem kw_pbac_ambient_irrelevant_le_span_X_CR :
    (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 3) R)).toIdeal
      ≤ Ideal.span (Set.range (X : Fin 3 → MvPolynomial (Fin 3) R)) := by
  classical
  intro p hp
  rw [HomogeneousIdeal.toIdeal_irrelevant, RingHom.mem_ker] at hp
  have hzero : (DirectSum.decompose (homogeneousSubmodule (Fin 3) R) p 0
      : MvPolynomial (Fin 3) R) = 0 := by
    rw [← GradedRing.projZeroRingHom_apply]; exact hp
  have hc0 : MvPolynomial.coeff 0 p = 0 := by
    conv_lhs => rw [← DirectSum.sum_support_decompose (homogeneousSubmodule (Fin 3) R) p]
    rw [MvPolynomial.coeff_sum]
    refine Finset.sum_eq_zero fun n _ => ?_
    by_cases h0 : n = 0
    · rw [h0, hzero, MvPolynomial.coeff_zero]
    · have hmem : ((DirectSum.decompose (homogeneousSubmodule (Fin 3) R) p n
          : MvPolynomial (Fin 3) R)).IsHomogeneous n :=
        (MvPolynomial.mem_homogeneousSubmodule _ _).mp (SetLike.coe_mem _)
      exact hmem.coeff_eq_zero (by simpa using Ne.symm h0)
  rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hmne : m ≠ 0 := by rintro rfl; exact (MvPolynomial.mem_support_iff.mp hm) hc0
  obtain ⟨l, hl⟩ := Finsupp.ne_iff.mp hmne
  exact ⟨l, Set.mem_univ l, by simpa using hl⟩


-- @@ L1694-1725 verbatim
theorem kw_pbac_irrelevant_le_span_mk_X_CR :
    (HomogeneousIdeal.irrelevant (projModelGradingCR V)).toIdeal
      ≤ Ideal.span (Set.range fun i : Fin 3 =>
          Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
            (X i : MvPolynomial (Fin 3) R)) := by
  intro z hz
  rw [HomogeneousIdeal.toIdeal_irrelevant, RingHom.mem_ker,
    GradedRing.projZeroRingHom_apply] at hz
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [decompose_quotGradingSubmodule_mk_apply (homogeneousSubmodule (Fin 3) R)
      (projModelHomogeneousIdealCR V) p 0] at hz
  have hrewrite : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal p
      = Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
          (p - (DirectSum.decompose (homogeneousSubmodule (Fin 3) R) p 0
            : MvPolynomial (Fin 3) R)) := by
    rw [map_sub, hz, sub_zero]
  rw [hrewrite]
  have hirr : (p - (DirectSum.decompose (homogeneousSubmodule (Fin 3) R) p 0
        : MvPolynomial (Fin 3) R))
      ∈ (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 3) R)).toIdeal := by
    rw [HomogeneousIdeal.toIdeal_irrelevant, RingHom.mem_ker,
      GradedRing.projZeroRingHom_apply, DirectSum.decompose_sub,
      DirectSum.decompose_coe, DirectSum.sub_apply, DirectSum.of_eq_same,
      AddSubgroupClass.coe_sub, sub_self]
  have hmem := kw_pbac_ambient_irrelevant_le_span_X_CR R hirr
  have hmap : Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal
        (p - (DirectSum.decompose (homogeneousSubmodule (Fin 3) R) p 0
          : MvPolynomial (Fin 3) R))
      ∈ Ideal.map (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal)
          (Ideal.span (Set.range (X : Fin 3 → MvPolynomial (Fin 3) R))) :=
    Ideal.mem_map_of_mem _ hmem
  rwa [Ideal.map_span, ← Set.range_comp] at hmap


-- @@ L1727-1734 verbatim
noncomputable def projModelAffineOpenCoverCR :
    Scheme.AffineOpenCover (projModelCR V) :=
  Proj.affineOpenCoverOfIrrelevantLESpan (projModelGradingCR V)
    (fun i : Fin 3 =>
      Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R))
    (m := fun _ => 1)
    (fun i => kw_pbac_mk_X_mem_one_CR R V i) (fun _ => Nat.one_pos)
    (kw_pbac_irrelevant_le_span_mk_X_CR R V)


-- @@ L1736-1736 verbatim
end CoverCRPort


-- @@ L1738-1738 verbatim
section ChartStructureMap


-- @@ L1740-1740 verbatim
variable (V : WeierstrassCurve.Projective R)


-- @@ L1742-1746 verbatim
set_option quotPrecheck false in

local notation "𝒜" i =>
  HomogeneousLocalization.Away (projModelGradingCR V)
    (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R))


-- @@ L1748-1748 verbatim
attribute [local instance] kw_pbac_awayAlgebra


-- @@ L1750-1756 verbatim
theorem kw_pbac_awayι_comp_projModelStrCR (i : Fin 3) :
    Proj.awayι (projModelGradingCR V) _ (kw_pbac_mk_X_mem_one_CR R V i) one_pos
        ≫ projModelStrCR V
      = Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 i))) := by
  unfold projModelStrCR
  rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
  rfl


-- @@ L1758-1758 verbatim
end ChartStructureMap


-- @@ L1760-1760 verbatim
section PullbackCover


-- @@ L1762-1762 verbatim
variable (V : WeierstrassCurve.Projective R)


-- @@ L1764-1769 verbatim
noncomputable def kwProjPullbackOpenCoverCR :
    (pullback (projModelStrCR V) (projModelStrCR V)).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight
    (projModelAffineOpenCoverCR R V).openCover
    (projModelAffineOpenCoverCR R V).openCover
    (projModelStrCR V) (projModelStrCR V)


-- @@ L1771-1771 verbatim
end PullbackCover


-- @@ L1773-1773 verbatim
section ChartIso


-- @@ L1775-1775 verbatim
variable (V : WeierstrassCurve.Projective R)


-- @@ L1777-1781 verbatim
set_option quotPrecheck false in

local notation "𝒜" i =>
  HomogeneousLocalization.Away (projModelGradingCR V)
    (Ideal.Quotient.mk (projModelHomogeneousIdealCR V).toIdeal (X i : MvPolynomial (Fin 3) R))


-- @@ L1783-1783 verbatim
attribute [local instance] kw_pbac_awayAlgebra


-- @@ L1785-1790 verbatim
noncomputable def kwProjPullbackChartIsoCR (i j : Fin 3) :
    (kwProjPullbackOpenCoverCR R V).X (i, j)
      ≅ Spec (CommRingCat.of ((𝒜 i) ⊗[R] (𝒜 j))) :=
  pullback.congrHom (kw_pbac_awayι_comp_projModelStrCR R V i)
      (kw_pbac_awayι_comp_projModelStrCR R V j)
    ≪≫ pullbackSpecIso R (𝒜 i) (𝒜 j)


-- @@ L1792-1792 verbatim
end ChartIso


-- @@ L1794-1794 verbatim
end WeierstrassProjModel


-- @@ L1796-1796 verbatim
end


-- @@ L1798-1798 verbatim
end MEGA_KwProjPullbackAwayCoverCRCover_lean


-- @@ L1800-1800 verbatim
section MEGA_KwLROuterGlue_lean

-- @@ L1801-1801 verbatim
set_option autoImplicit false

-- @@ L1802-1802 verbatim
set_option maxHeartbeats 1600000


-- @@ L1804-1804 verbatim
noncomputable section


-- @@ L1806-1806 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

-- @@ L1807-1807 verbatim
open MvPolynomial WeierstrassCurve HomogeneousLocalization

-- @@ L1808-1808 verbatim
open scoped TensorProduct


-- @@ L1810-1810 verbatim
namespace WeierstrassProjModel


-- @@ L1812-1812 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra

-- @@ L1813-1813 verbatim
attribute [local instance] kw_pbac_awayAlgebra


-- @@ L1815-1815 verbatim
universe u


-- @@ L1817-1817 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


-- @@ L1819-1820 verbatim
set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective


-- @@ L1822-1826 verbatim
noncomputable def kw_lrOuter_toE (hcov : KwLRSixUCoverage W)
    (hcompat : KwLRPerChartCompat W) :
    ∀ ij, (kwProjPullbackOpenCoverCR R W.toProjective).X ij ⟶ E :=
  fun ij => (kwProjPullbackChartIsoCR R W.toProjective ij.1 ij.2).hom
            ≫ kw_lrPerChart_toE W hcov hcompat ij.1 ij.2


-- @@ L1828-1836 verbatim
def KwLROuterCompat : Prop :=
  ∀ (hcov : KwLRSixUCoverage W) (hcompat : KwLRPerChartCompat W)
    (ij ij' : Fin 3 × Fin 3),
    pullback.fst ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
                 ((kwProjPullbackOpenCoverCR R W.toProjective).f ij')
        ≫ kw_lrOuter_toE W hcov hcompat ij
      = pullback.snd ((kwProjPullbackOpenCoverCR R W.toProjective).f ij)
                     ((kwProjPullbackOpenCoverCR R W.toProjective).f ij')
        ≫ kw_lrOuter_toE W hcov hcompat ij'


-- @@ L1838-1842 verbatim
noncomputable def kw_lrAddMorphism (hcov : KwLRSixUCoverage W)
    (hcompat : KwLRPerChartCompat W) (houter : KwLROuterCompat W) :
    pullback (projModelStrCR W.toProjective) (projModelStrCR W.toProjective) ⟶ E :=
  (kwProjPullbackOpenCoverCR R W.toProjective).glueMorphisms
    (kw_lrOuter_toE W hcov hcompat) (houter hcov hcompat)


-- @@ L1844-1844 verbatim
end WeierstrassProjModel


-- @@ L1846-1846 verbatim
end

-- @@ L1847-1847 verbatim
end MEGA_KwLROuterGlue_lean


-- @@ L1849-1849 verbatim
section MEGA_KwLRAddNegDiagZeroNegMor_lean

-- @@ L1850-1850 verbatim
set_option autoImplicit false

-- @@ L1851-1851 verbatim
set_option maxHeartbeats 1600000


-- @@ L1853-1853 verbatim
noncomputable section


-- @@ L1855-1855 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

-- @@ L1856-1856 verbatim
open MvPolynomial WeierstrassCurve HomogeneousLocalization HomogeneousIdealQuotientGrading

-- @@ L1857-1857 verbatim
open scoped TensorProduct


-- @@ L1859-1859 verbatim
namespace WeierstrassProjModel


-- @@ L1861-1861 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L1863-1863 verbatim
universe u


-- @@ L1865-1865 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


-- @@ L1867-1870 verbatim
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
    (X i : MvPolynomial (Fin 3) R))

-- @@ L1871-1872 verbatim
set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective

-- @@ L1873-1874 verbatim
set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective

-- @@ L1875-1876 verbatim
set_option quotPrecheck false in
local notation "ℬ" => ProjModelRingCR W.toProjective

-- @@ L1877-1878 verbatim
set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal


-- @@ L1880-1880 verbatim
section NegMor


-- @@ L1882-1883 verbatim
def kw_lrAddNegDiag_negSubstGen : Fin 3 → MvPolynomial (Fin 3) R :=
  ![X 0, -X 1 - C W.a₁ * X 0 - C W.a₃ * X 2, X 2]


-- @@ L1885-1886 verbatim
def kw_lrAddNegDiag_negSubst : MvPolynomial (Fin 3) R →ₐ[R] MvPolynomial (Fin 3) R :=
  aeval (kw_lrAddNegDiag_negSubstGen W)


-- @@ L1888-1888 verbatim
local notation "negSubst" => kw_lrAddNegDiag_negSubst W


-- @@ L1890-1897 verbatim
theorem kw_lrAddNegDiag_negSubstGen_isHomogeneous (m : Fin 3) :
    (kw_lrAddNegDiag_negSubstGen W m).IsHomogeneous 1 := by
  fin_cases m
  · exact isHomogeneous_X R 0
  · refine ((((isHomogeneous_X R 1).neg).sub ?_).sub ?_)
    · exact (isHomogeneous_C _ W.a₁).mul (isHomogeneous_X R 0)
    · exact (isHomogeneous_C _ W.a₃).mul (isHomogeneous_X R 2)
  · exact isHomogeneous_X R 2


-- @@ L1899-1903 verbatim
theorem kw_lrAddNegDiag_negSubst_isHomogeneous {p : MvPolynomial (Fin 3) R} {n : ℕ}
    (hp : p.IsHomogeneous n) : (negSubst p).IsHomogeneous n := by
  have key : (aeval (kw_lrAddNegDiag_negSubstGen W) p).IsHomogeneous (1 * n) :=
    hp.aeval _ (kw_lrAddNegDiag_negSubstGen_isHomogeneous W)
  simpa [kw_lrAddNegDiag_negSubst, one_mul] using key


-- @@ L1905-1911 verbatim
theorem kw_lrAddNegDiag_negSubst_polynomial :
    negSubst W.toProjective.polynomial = W.toProjective.polynomial := by
  simp only [kw_lrAddNegDiag_negSubst, WeierstrassCurve.Projective.polynomial,
    WeierstrassCurve.toProjective, map_sub, map_add, map_mul, map_pow, aeval_C, aeval_X,
    kw_lrAddNegDiag_negSubstGen, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, MvPolynomial.algebraMap_eq]
  ring


-- @@ L1913-1918 verbatim
theorem kw_lrAddNegDiag_negSubst_mapSpan :
    Ideal.map (negSubst : MvPolynomial (Fin 3) R →+* _)
        (Ideal.span {W.toProjective.polynomial})
      = Ideal.span {W.toProjective.polynomial} := by
  rw [Ideal.map_span, Set.image_singleton]
  exact congrArg (Ideal.span {·}) (kw_lrAddNegDiag_negSubst_polynomial W)


-- @@ L1920-1926 verbatim
def kw_lrAddNegDiag_negQuotHom : ℬ →+* ℬ :=
  Ideal.Quotient.lift (projModelHomogeneousIdealCR W.toProjective).toIdeal
    ((Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal).comp
      (negSubst : MvPolynomial (Fin 3) R →+* _))
    (fun _ ha => Ideal.Quotient.eq_zero_iff_mem.mpr
      ((Ideal.map_le_iff_le_comap.mp (kw_lrAddNegDiag_negSubst_mapSpan W).le)
        (projModelHomogeneousIdealCR_toIdeal W.toProjective ▸ ha)))


-- @@ L1928-1936 verbatim
def kw_lrAddNegDiag_negGradedHom :
    projModelGradingCR W.toProjective →+*ᵍ projModelGradingCR W.toProjective where
  toRingHom := kw_lrAddNegDiag_negQuotHom W
  map_mem {i x} hx := by
    obtain ⟨a, ha, rfl⟩ := (mem_quotGradingSubmodule_iff _ _).mp hx
    exact mk_mem_quotGradingSubmodule _ _
      ((mem_homogeneousSubmodule _ _).mpr
        (kw_lrAddNegDiag_negSubst_isHomogeneous W
          ((mem_homogeneousSubmodule _ _).mp ha)))


-- @@ L1938-1938 verbatim
local notation "negGradedHom" => kw_lrAddNegDiag_negGradedHom W


-- @@ L1940-1948 verbatim
set_option linter.unnecessarySeqFocus false in

theorem kw_lrAddNegDiag_negSubst_comp_self :
    (negSubst).comp negSubst = AlgHom.id R (MvPolynomial (Fin 3) R) := by
  refine MvPolynomial.algHom_ext fun m => ?_
  fin_cases m <;>
    simp [kw_lrAddNegDiag_negSubst, kw_lrAddNegDiag_negSubstGen,
      map_sub, map_neg, map_mul] <;>
    ring


-- @@ L1950-1954 verbatim
theorem kw_lrAddNegDiag_negGradedHom_comp_self :
    (negGradedHom : ℬ →+* ℬ).comp negGradedHom = RingHom.id ℬ := by
  refine Ideal.Quotient.ringHom_ext ?_
  exact RingHom.ext fun a => congrArg mk₃
    (DFunLike.congr_fun (kw_lrAddNegDiag_negSubst_comp_self W) a)


-- @@ L1956-1974 verbatim
theorem kw_lrAddNegDiag_negGradedHom_map_proj (n : ℕ) (x : ℬ) :
    GradedRing.proj (projModelGradingCR W.toProjective) n (negGradedHom x)
      = negGradedHom (GradedRing.proj (projModelGradingCR W.toProjective) n x) := by
  classical
  conv_lhs => rw [← DirectSum.sum_support_decompose (projModelGradingCR W.toProjective) x]
  conv_rhs => rw [← DirectSum.sum_support_decompose (projModelGradingCR W.toProjective) x]
  simp only [map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hy : (↑((DirectSum.decompose (projModelGradingCR W.toProjective) x) m) : ℬ)
      ∈ projModelGradingCR W.toProjective m := SetLike.coe_mem _
  have hfy : negGradedHom
        (↑((DirectSum.decompose (projModelGradingCR W.toProjective) x) m) : ℬ)
      ∈ projModelGradingCR W.toProjective m := (negGradedHom).map_mem hy
  rcases eq_or_ne m n with h | h
  · subst h
    rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_same _ hfy,
      GradedRing.proj_apply, DirectSum.decompose_of_mem_same _ hy]
  · rw [GradedRing.proj_apply, DirectSum.decompose_of_mem_ne _ hfy h,
      GradedRing.proj_apply, DirectSum.decompose_of_mem_ne _ hy h, map_zero]


-- @@ L1976-1987 verbatim
theorem kw_lrAddNegDiag_negGradedHom_irrelevant_le :
    HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)
      ≤ (HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)).map
          negGradedHom := by
  intro x hx
  have heq : x = negGradedHom (negGradedHom x) :=
    (RingHom.congr_fun (kw_lrAddNegDiag_negGradedHom_comp_self W) x).symm
  rw [heq]
  refine Ideal.mem_map_of_mem _ ?_
  show negGradedHom x ∈ HomogeneousIdeal.irrelevant (projModelGradingCR W.toProjective)
  rw [HomogeneousIdeal.mem_irrelevant_iff] at hx ⊢
  rw [kw_lrAddNegDiag_negGradedHom_map_proj W 0 x, hx, map_zero]


-- @@ L1989-1990 verbatim
def kw_lrAddNegDiag_negMor : E ⟶ E :=
  Proj.map negGradedHom (kw_lrAddNegDiag_negGradedHom_irrelevant_le W)


-- @@ L1992-1992 verbatim
local notation "negMor" => kw_lrAddNegDiag_negMor W


-- @@ L1994-1994 verbatim
end NegMor


-- @@ L1996-1996 verbatim
section GeneralNaturality


-- @@ L1998-1998 verbatim
variable {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A] [AddSubgroupClass σ A]

-- @@ L1999-1999 verbatim
variable {𝒢 : ℕ → σ} [GradedRing 𝒢]


-- @@ L2001-2001 verbatim
end GeneralNaturality


-- @@ L2003-2003 verbatim
section NegMor2


-- @@ L2005-2005 verbatim
local notation "negGradedHom" => kw_lrAddNegDiag_negGradedHom W

-- @@ L2006-2006 verbatim
local notation "negMor" => kw_lrAddNegDiag_negMor W

-- @@ L2007-2007 verbatim
local notation "negSubst" => kw_lrAddNegDiag_negSubst W


-- @@ L2009-2009 verbatim
end NegMor2


-- @@ L2011-2011 verbatim
section PolyIdentity


-- @@ L2013-2015 verbatim
noncomputable def kw_lrAddNegDiag_evalNeg :
    MvPolynomial (Fin 3 ⊕ Fin 3) R →ₐ[R] MvPolynomial (Fin 3) R :=
  aeval (Sum.elim (kw_lrAddNegDiag_negSubstGen W) X)


-- @@ L2017-2018 verbatim
set_option quotPrecheck false in
local notation "evalNeg" => kw_lrAddNegDiag_evalNeg W


-- @@ L2020-2025 verbatim
macro "simp_evalNeg" : tactic =>
  `(tactic| simp only [map_add, map_sub, map_mul, map_neg, map_pow, map_ofNat, map_one,
    kw_lrAddNegDiag_evalNeg_C, kw_lrAddNegDiag_evalNeg_inr,
    kw_lrAddNegDiag_evalNeg_inl, kw_lrAddNegDiag_negSubstGen,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons])


-- @@ L2027-2027 verbatim
end PolyIdentity


-- @@ L2029-2029 verbatim
end WeierstrassProjModel


-- @@ L2031-2031 verbatim
end


-- @@ L2033-2033 verbatim
end MEGA_KwLRAddNegDiagZeroNegMor_lean


-- @@ L2035-2035 verbatim
section MEGA_KwProjWeierstrassRelGroupLawConstruct_lean

-- @@ L2036-2036 verbatim
set_option autoImplicit false


-- @@ L2038-2038 verbatim
noncomputable section


-- @@ L2040-2040 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve


-- @@ L2042-2042 verbatim
universe u


-- @@ L2044-2044 verbatim
namespace WeierstrassProjModel


-- @@ L2046-2046 verbatim
open WeierstrassProjModel NeronModelInfra HomogeneousIdealQuotientGrading


-- @@ L2048-2048 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra


-- @@ L2050-2050 verbatim
variable (R : Type u) [CommRing R]


-- @@ L2052-2052 verbatim
section ZeroSection


-- @@ L2054-2054 verbatim
variable (W : WeierstrassCurve R)


-- @@ L2056-2062 verbatim
open MvPolynomial in

theorem kw_mk_X1_mem_one_CR :
    Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
        (X 1 : MvPolynomial (Fin 3) R)
      ∈ projModelGradingCR W.toProjective 1 :=
  mk_mem_quotGradingSubmodule _ _ ((mem_homogeneousSubmodule _ _).mpr (isHomogeneous_X R 1))


-- @@ L2064-2072 verbatim
open MvPolynomial in

def kwYEvalRingHom : ProjModelRingCR W.toProjective →+* R :=
  Ideal.Quotient.lift _ (MvPolynomial.eval ![(0 : R), 1, 0]) fun a ha => by
    refine (Ideal.span_le.mpr ?_ : Ideal.span _ ≤ RingHom.ker _)
      (projModelHomogeneousIdealCR_toIdeal W.toProjective ▸ ha)
    simp only [Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]

    exact WeierstrassCurve.Projective.equation_zero


-- @@ L2074-2079 verbatim
open MvPolynomial in

theorem kwYEvalRingHom_mk_X1 :
    kwYEvalRingHom R W (Ideal.Quotient.mk _ (X 1 : MvPolynomial (Fin 3) R)) = 1 := by
  show (MvPolynomial.eval ![(0 : R), 1, 0]) (X 1) = 1
  simp


-- @@ L2081-2092 verbatim
def kwYChartEval :
    HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
      (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)) →+* R :=
  (IsLocalization.Away.lift (g := kwYEvalRingHom R W)
      (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R))
      (kwYEvalRingHom_mk_X1 R W ▸ isUnit_one)).comp
    (algebraMap
      (HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
        (Ideal.Quotient.mk _ (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)))
      (Localization.Away
        (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
          (MvPolynomial.X 1 : MvPolynomial (Fin 3) R))))


-- @@ L2094-2100 verbatim
open MvPolynomial in

theorem kwYEvalRingHom_comp_algebraMap :
    (kwYEvalRingHom R W).comp (algebraMap R (ProjModelRingCR W.toProjective)) = RingHom.id R :=
  RingHom.ext fun r => by
    show (MvPolynomial.eval ![(0 : R), 1, 0]) (C r) = r
    exact MvPolynomial.eval_C _


-- @@ L2102-2122 verbatim
theorem kwYChartEval_section :
    (kwYChartEval R W).comp
      ((HomogeneousLocalization.fromZeroRingHom (projModelGradingCR W.toProjective) _).comp
        (algebraMap R (projModelGradingCR W.toProjective 0))) = RingHom.id R := by

  refine RingHom.ext fun r => ?_
  simp only [RingHom.comp_apply, RingHom.id_apply, kwYChartEval,
    HomogeneousLocalization.algebraMap_apply]

  have hval :
      (HomogeneousLocalization.fromZeroRingHom (projModelGradingCR W.toProjective) _
          (algebraMap R (projModelGradingCR W.toProjective 0) r)).val
        = algebraMap (ProjModelRingCR W.toProjective)
            (Localization.Away
              (Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal
                (MvPolynomial.X 1 : MvPolynomial (Fin 3) R)))
            (algebraMap R (ProjModelRingCR W.toProjective) r) := by

    rfl
  rw [hval, IsLocalization.Away.lift, IsLocalization.lift_eq]
  exact RingHom.congr_fun (kwYEvalRingHom_comp_algebraMap R W) r


-- @@ L2124-2131 verbatim
def kwZeroSect : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) (projModelStrCR W.toProjective) :=
  ⟨Spec.map (CommRingCat.ofHom (kwYChartEval R W)) ≫
    Proj.awayι (projModelGradingCR W.toProjective) _ (kw_mk_X1_mem_one_CR R W) one_pos,
   by
    simp only [projModelStrCR, Category.assoc]
    rw [← Category.assoc (Proj.awayι ..), Proj.awayι_toSpecZero, ← Spec.map_comp,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      kwYChartEval_section, CommRingCat.ofHom_id, Spec.map_id]⟩


-- @@ L2133-2133 verbatim
end ZeroSection


-- @@ L2135-2135 verbatim
section AddLawData


-- @@ L2137-2137 verbatim
variable (W : WeierstrassCurve R)


-- @@ L2139-2139 verbatim
local notation "E" => projModelCR W.toProjective

-- @@ L2140-2140 verbatim
local notation "π" => projModelStrCR W.toProjective


-- @@ L2142-2142 verbatim
end AddLawData


-- @@ L2144-2144 verbatim
section Assembly


-- @@ L2146-2146 verbatim
end Assembly


-- @@ L2148-2148 verbatim
end WeierstrassProjModel


-- @@ L2150-2150 verbatim
end

-- @@ L2151-2151 verbatim
end MEGA_KwProjWeierstrassRelGroupLawConstruct_lean


-- @@ L2153-2153 verbatim
section MEGA_KwLRAffinePtTorsionBridge_lean


-- @@ L2155-2155 verbatim
set_option autoImplicit false


-- @@ L2157-2157 verbatim
noncomputable section


-- @@ L2159-2159 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve


-- @@ L2161-2161 verbatim
namespace WeierstrassProjModel


-- @@ L2163-2163 verbatim
open WeierstrassProjModel NeronModelInfra


-- @@ L2165-2165 verbatim
attribute [local instance] Classical.propDecidable


-- @@ L2167-2167 verbatim
universe u


-- @@ L2169-2169 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)


-- @@ L2171-2171 verbatim
section Bridge


-- @@ L2173-2173 verbatim
variable (F : Type u) [Field F] [Algebra R F]


-- @@ L2175-2176 verbatim
abbrev kw_lrAptb_tF : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R F))


-- @@ L2178-2178 verbatim
section Engine


-- @@ L2180-2180 verbatim
end Engine


-- @@ L2182-2182 verbatim
end Bridge


-- @@ L2184-2184 verbatim
end WeierstrassProjModel


-- @@ L2186-2186 verbatim
end


-- @@ L2188-2188 verbatim
end MEGA_KwLRAffinePtTorsionBridge_lean


-- @@ L2190-2190 verbatim
section MEGA_KwLRAffinePtSetEquiv_lean

-- @@ L2191-2191 verbatim
set_option autoImplicit false

-- @@ L2192-2192 verbatim
set_option maxHeartbeats 3200000


-- @@ L2194-2194 verbatim
noncomputable section


-- @@ L2196-2196 verbatim
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassCurve MvPolynomial

-- @@ L2197-2197 verbatim
open HomogeneousLocalization HomogeneousIdealQuotientGrading

-- @@ L2198-2198 verbatim
open scoped WeierstrassCurve.Projective


-- @@ L2200-2200 verbatim
namespace WeierstrassProjModel


-- @@ L2202-2202 verbatim
open WeierstrassProjModel NeronModelInfra


-- @@ L2204-2204 verbatim
attribute [local instance] Classical.propDecidable

-- @@ L2205-2205 verbatim
attribute [local instance] MvPolynomial.gradedAlgebra

-- @@ L2206-2206 verbatim
attribute [local instance] kw_pbac_awayAlgebra


-- @@ L2208-2208 verbatim
universe u


-- @@ L2210-2210 verbatim
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

-- @@ L2211-2211 verbatim
variable (F : Type u) [Field F] [Algebra R F]


-- @@ L2213-2214 verbatim
set_option quotPrecheck false in
local notation "mk₃" => Ideal.Quotient.mk (projModelHomogeneousIdealCR W.toProjective).toIdeal

-- @@ L2215-2217 verbatim
set_option quotPrecheck false in
local notation "𝒜" i => HomogeneousLocalization.Away (projModelGradingCR W.toProjective)
  (mk₃ (X i : MvPolynomial (Fin 3) R))

-- @@ L2218-2219 verbatim
set_option quotPrecheck false in
local notation "E" => projModelCR W.toProjective

-- @@ L2220-2221 verbatim
set_option quotPrecheck false in
local notation "π" => projModelStrCR W.toProjective

-- @@ L2222-2223 verbatim
set_option quotPrecheck false in
local notation "coverE" => (projModelAffineOpenCoverCR R W.toProjective).openCover

-- @@ L2224-2225 verbatim
set_option quotPrecheck false in
local notation "gen" => kw_lrChart_gen W

-- @@ L2226-2227 verbatim
set_option quotPrecheck false in
local notation "dehom" => kw_lrChart_dehom W

-- @@ L2228-2229 verbatim
set_option quotPrecheck false in
local notation "t_F" => kw_lrAptb_tF (R := R) F


-- @@ L2231-2233 verbatim
set_option quotPrecheck false in
local notation "awayι₃" i => Proj.awayι (projModelGradingCR W.toProjective)
  (mk₃ (X i : MvPolynomial (Fin 3) R)) (kw_pbac_mk_X_mem_one_CR R W.toProjective i) one_pos


-- @@ L2235-2235 verbatim
abbrev kw_lrApt_WF : WeierstrassCurve.Projective F := (W.baseChange F).toProjective


-- @@ L2237-2238 verbatim
set_option quotPrecheck false in
local notation "W_F" => kw_lrApt_WF W F


-- @@ L2240-2240 verbatim
section ChartClassification


-- @@ L2242-2243 verbatim
def kw_lrApt_chartEval (i : Fin 3) (ψ : (𝒜 i) →ₐ[R] F) : Fin 3 → F :=
  fun k => ψ (gen i k)


-- @@ L2245-2245 verbatim
end ChartClassification


-- @@ L2247-2247 verbatim
section ChartFactorization


-- @@ L2249-2249 verbatim
end ChartFactorization


-- @@ L2251-2251 verbatim
section Forward


-- @@ L2253-2253 verbatim
end Forward


-- @@ L2255-2255 verbatim
section Nonsingular


-- @@ L2257-2257 verbatim
variable {F}


-- @@ L2259-2259 verbatim
end Nonsingular


-- @@ L2261-2261 verbatim
section Inverse


-- @@ L2263-2263 verbatim
end Inverse


-- @@ L2265-2265 verbatim
section Assembly


-- @@ L2267-2267 verbatim
end Assembly


-- @@ L2269-2269 verbatim
end WeierstrassProjModel


-- @@ L2271-2271 verbatim
end

-- @@ L2272-2272 verbatim
end MEGA_KwLRAffinePtSetEquiv_lean
