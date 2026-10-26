/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/
import RiemannRoch.Chow.FlatPullback
import RiemannRoch.Chow.ProperPushforward
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.LocalProperties.Exactness
import Mathlib.RingTheory.Localization.BaseChange


-- @@ L19-30 verbatim
/-!
# Base change for proper pushforward of cycles (Fulton Prop. 1.7)

For a cartesian square `X' = X ×_Y Y'` with `f : X ⟶ Y` proper (only `QuasiCompact` and
`LocallyOfFiniteType` are used) and `g : Y' ⟶ Y`, we prove `g^* f_* = f'_* g'^*` on cycles.

* `FlatProperBaseChangeAlgebra` (ring level): for `W = (𝒪_{y'}/m_y) ⊗_{κ(y)} κ(x)` the ALG lemmas (Artinian
  decomposition, flat-base-change bound, going-down/transcendence) and `core`, the
  identification of the points of the fibre with the primes of `W` and of their local rings.
* scheme level: affine charts `Spec (A ⊗_R R') ↪ X'`, the pointwise identity
  `Σ_{x' ↦ (x, y')} c_{g'}(x') [κ x' : κ y'] = [κ x : κ y] c_g(y')`, and the global theorem.
-/


-- @@ L32-32 verbatim
noncomputable section

-- @@ L33-33 verbatim
open IsLocalRing


-- @@ L35-35 verbatim
namespace FlatProperBaseChangeAlgebra


-- @@ L37-37 verbatim
universe u


-- @@ L39-41 verbatim
/-- Coefficient `ℓ_S(S ⧸ m_R S)` (as a natural number, `0` if infinite). -/
def lc {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] (φ : R →+* S) : ℕ :=
  (Module.length S (S ⧸ (maximalIdeal R).map φ)).toNat


-- @@ L43-46 verbatim
/-- Residue degree `[κ(S) : κ(R)]` (`0` if infinite). -/
def ld {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] (φ : R →+* S)
    [IsLocalHom φ] : ℕ :=
  @Module.finrank (ResidueField R) (ResidueField S) _ _ (ResidueField.map φ).toAlgebra.toModule


-- @@ L48-52 verbatim
theorem length_self_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B) :
    Module.length A A = Module.length B B := by
  letI := e.toRingHom.toAlgebra
  rw [(AlgEquiv.ofRingEquiv (f := e) (fun _ => rfl)).toLinearEquiv.length_eq]
  exact Module.length_eq_of_surjective (R := B) (M := B) e.surjective


-- @@ L54-57 verbatim
theorem map_maximalIdeal_of_equiv {R R' : Type*} [CommRing R] [CommRing R'] [IsLocalRing R]
    [IsLocalRing R'] (e : R ≃+* R') : (maximalIdeal R).map (e : R →+* R') = maximalIdeal R' := by
  have : ((maximalIdeal R).map (e : R →+* R')).IsMaximal := Ideal.map_isMaximal_of_equiv e
  exact IsLocalRing.eq_maximalIdeal this


-- @@ L59-73 verbatim
theorem lc_eq_of_equiv {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing R'] (φ : R →+* S) (ψ : R' →+* S') (eR : R ≃+* R')
    (eS : S ≃+* S') (h : ∀ r, eS (φ r) = ψ (eR r)) : lc φ = lc ψ := by
  unfold lc
  set I := (maximalIdeal R).map φ
  set I' := (maximalIdeal R').map ψ
  have hI : I' = I.map (eS : S →+* S') := by
    simp only [I, I']
    rw [Ideal.map_map]
    have : (eS : S →+* S').comp φ = ψ.comp (eR : R →+* R') := RingHom.ext h
    rw [this, ← Ideal.map_map, map_maximalIdeal_of_equiv]
  have e : (S ⧸ I) ≃+* (S' ⧸ I') := Ideal.quotientEquiv I I' eS hI
  rw [Module.length_eq_of_surjective (R := S ⧸ I) (M := S ⧸ I) Ideal.Quotient.mk_surjective,
    Module.length_eq_of_surjective (R := S' ⧸ I') (M := S' ⧸ I') Ideal.Quotient.mk_surjective,
    length_self_eq_of_ringEquiv e]


-- @@ L75-87 verbatim
theorem ld_eq_of_equiv {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing R'] [IsLocalRing S] [IsLocalRing S'] (φ : R →+* S) (ψ : R' →+* S')
    [IsLocalHom φ] [IsLocalHom ψ] (eR : R ≃+* R')
    (eS : S ≃+* S') (h : ∀ r, eS (φ r) = ψ (eR r)) : ld φ = ld ψ := by
  unfold ld
  letI := (ResidueField.map φ).toAlgebra
  letI := (ResidueField.map ψ).toAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv (ResidueField.mapEquiv eR) (ResidueField.mapEquiv eS) ?_
  ext x
  obtain ⟨x, rfl⟩ := residue_surjective x
  change ResidueField.map ψ (ResidueField.map (eR : R →+* R') (residue R x)) =
    ResidueField.map (eS : S →+* S') (ResidueField.map φ (residue R x))
  simp [ResidueField.map_residue, h]



-- @@ L90-90 verbatim
section ALG


-- @@ L92-92 verbatim
open TensorProduct Polynomial


-- @@ L94-95 verbatim
variable {κ B K : Type u} [Field κ] [CommRing B] [IsLocalRing B] [Algebra κ B] [Field K]
  [Algebra κ K]


-- @@ L97-97 verbatim
example : Module.Free B (B ⊗[κ] K) := inferInstance

-- @@ L98-98 verbatim
example : Module.Flat B (B ⊗[κ] K) := inferInstance

-- @@ L99-100 verbatim
example (Q : Ideal (B ⊗[κ] K)) [Q.IsPrime] : IsScalarTower B (B ⊗[κ] K) (Localization.AtPrime Q) :=
  inferInstance

-- @@ L101-102 verbatim
example (Q : Ideal (B ⊗[κ] K)) [Q.IsPrime] :
    Module.Flat (B ⊗[κ] K) (Localization.AtPrime Q) := inferInstance


-- @@ L104-114 verbatim
/-- A good prime (lying over the maximal ideal of `B`) gives a local homomorphism. -/
theorem isLocalHom_of_good (Q : Ideal (B ⊗[κ] K)) [Q.IsPrime]
    (hQ : Q.comap (algebraMap B (B ⊗[κ] K)) = maximalIdeal B) :
    IsLocalHom (algebraMap B (Localization.AtPrime Q)) := by
  refine ⟨fun b hb ↦ ?_⟩
  by_contra hnu
  have hb' : b ∈ maximalIdeal B := hnu
  rw [← hQ, Ideal.mem_comap] at hb'
  rw [IsScalarTower.algebraMap_apply B (B ⊗[κ] K) (Localization.AtPrime Q)] at hb
  have := (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q _).mpr hb'
  exact (IsLocalRing.mem_maximalIdeal _).mp this hb


-- @@ L116-132 verbatim
/-- ALG-c: flat base change bounds the length of `B`. -/
theorem length_ne_top_of_good (Q : Ideal (B ⊗[κ] K)) [Q.IsPrime]
    (hQ : Q.comap (algebraMap B (B ⊗[κ] K)) = maximalIdeal B)
    (hfin : Module.length (Localization.AtPrime Q) (Localization.AtPrime Q) ≠ ⊤) :
    Module.length B B ≠ ⊤ := by
  haveI := isLocalHom_of_good Q hQ
  haveI : Module.Flat B (Localization.AtPrime Q) :=
    Module.Flat.trans B (B ⊗[κ] K) (Localization.AtPrime Q)
  have h := IsLocalRing.length_baseChange B (Localization.AtPrime Q) B
  rw [(TensorProduct.AlgebraTensorModule.rid B (Localization.AtPrime Q)
    (Localization.AtPrime Q)).length_eq] at h
  intro htop
  apply hfin
  rw [h, htop]
  apply ENat.top_mul
  simpa [← pos_iff_ne_zero, Module.length_pos_iff] using
    (map_maximalIdeal_lt_top (algebraMap B (Localization.AtPrime Q))).ne



-- @@ L135-138 verbatim
/-- Length count: `W = B ⊗ K` is free of rank `[K : κ]` over `B`. -/
theorem length_W_eq [Module.Finite κ K] :
    Module.length B (B ⊗[κ] K) = Module.finrank κ K * Module.length B B := by
  rw [Module.length_of_free_of_finite, Module.finrank_baseChange]


-- @@ L140-162 verbatim
/-- ALG-dec (i): if `W` has finite length over `B`, every prime of `W` is good. -/
theorem comap_eq_maximalIdeal_of_length_ne_top
    (hW : Module.length B (B ⊗[κ] K) ≠ ⊤) (Q : Ideal (B ⊗[κ] K)) [Q.IsPrime] :
    Q.comap (algebraMap B (B ⊗[κ] K)) = maximalIdeal B := by
  set J := Q.comap (algebraMap B (B ⊗[κ] K))
  let g : (B ⧸ J) →ₗ[B] ((B ⊗[κ] K) ⧸ Q) :=
    (Ideal.quotientMapₐ Q (Algebra.ofId B (B ⊗[κ] K)) le_rfl).toLinearMap
  have hinj : Function.Injective g := Ideal.quotientMap_injective
  have h1 : Module.length B (B ⧸ J) ≤ Module.length B ((B ⊗[κ] K) ⧸ Q) :=
    Module.length_le_of_injective g hinj
  have h2 : Module.length B ((B ⊗[κ] K) ⧸ Q) ≤ Module.length B (B ⊗[κ] K) :=
    Module.length_le_of_surjective ((Submodule.mkQ Q).restrictScalars B)
      (Submodule.mkQ_surjective _)
  have hfin : IsFiniteLength B (B ⧸ J) :=
    Module.length_ne_top_iff.mp (ne_top_of_le_ne_top hW (h1.trans h2))
  have hArt : IsArtinian B (B ⧸ J) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
  haveI : IsArtinianRing (B ⧸ J) := isArtinian_of_tower B hArt
  haveI : (⊥ : Ideal (B ⧸ J)).IsPrime := Ideal.isPrime_bot
  haveI : (⊥ : Ideal (B ⧸ J)).IsMaximal := IsArtinianRing.isMaximal_of_isPrime _
  have hmax : (Ideal.comap (Ideal.Quotient.mk J) ⊥).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker] at hmax
  exact IsLocalRing.eq_maximalIdeal hmax


-- @@ L164-175 verbatim
/-- ALG-dec (iii): length decomposes over the (finitely many) primes. -/
theorem length_W_eq_sum (hW : Module.length B (B ⊗[κ] K) ≠ ⊤) :
    ∃ _ : Fintype (PrimeSpectrum (B ⊗[κ] K)), Module.length B (B ⊗[κ] K) =
      ∑ Q : PrimeSpectrum (B ⊗[κ] K), Module.length B (Localization.AtPrime Q.asIdeal) := by
  have hfin : IsFiniteLength B (B ⊗[κ] K) := Module.length_ne_top_iff.mp hW
  have hArt : IsArtinian B (B ⊗[κ] K) := (isFiniteLength_iff_isNoetherian_isArtinian.mp hfin).2
  haveI : IsArtinianRing (B ⊗[κ] K) := isArtinian_of_tower B hArt
  let _ : Fintype (PrimeSpectrum (B ⊗[κ] K)) := Fintype.ofFinite _
  refine ⟨inferInstance, ?_⟩
  let e := ((PrimeSpectrum.toPiLocalizationEquiv (B ⊗[κ] K)).restrictScalars B).toLinearEquiv
  rw [e.length_eq]
  exact Module.length_pi_of_fintype B _



-- @@ L178-184 verbatim
theorem residueField_map_toAlgebra {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] [Algebra R S] [IsLocalHom (algebraMap R S)] :
    (ResidueField.map (algebraMap R S)).toAlgebra =
      (inferInstance : Algebra (ResidueField R) (ResidueField S)) := by
  refine Algebra.algebra_ext _ _ (fun x ↦ ?_)
  obtain ⟨x, rfl⟩ := residue_surjective x
  rfl


-- @@ L186-193 verbatim
/-- The flatness of `κ[X] → K` for a transcendental `k`. -/
theorem flat_aeval_of_transcendental {k : K} (hk : Transcendental κ k) :
    (Polynomial.aeval (R := κ) k).toRingHom.Flat := by
  letI : Algebra κ[X] K := (Polynomial.aeval (R := κ) k).toRingHom.toAlgebra
  haveI : FaithfulSMul κ[X] K :=
    (faithfulSMul_iff_algebraMap_injective κ[X] K).mpr (transcendental_iff_injective.mp hk)
  change Module.Flat κ[X] K
  infer_instance


-- @@ L195-275 verbatim
/-- ALG-n: a good prime with Artinian local ring and finite residue extension forces `K/κ`
to be algebraic. -/
theorem isAlgebraic_of_good (Q : Ideal (B ⊗[κ] K)) [Q.IsPrime]
    (hQ : Q.comap (algebraMap B (B ⊗[κ] K)) = maximalIdeal B)
    (hfin : Module.length (Localization.AtPrime Q) (Localization.AtPrime Q) ≠ ⊤)
    [IsLocalHom (algebraMap B (Localization.AtPrime Q))]
    (hdeg : Module.Finite (ResidueField B) (ResidueField (Localization.AtPrime Q))) :
    Algebra.IsAlgebraic κ K := by
  set W := B ⊗[κ] K
  set WQ := Localization.AtPrime Q
  have hFL : IsFiniteLength WQ WQ := Module.length_ne_top_iff.mp hfin
  haveI : IsArtinianRing WQ := (isFiniteLength_iff_isNoetherian_isArtinian.mp hFL).2
  refine ⟨fun k ↦ ?_⟩
  by_contra hk
  let ev : κ[X] →ₐ[κ] K := Polynomial.aeval k
  have hev : ev.toRingHom.Flat := flat_aeval_of_transcendental hk
  let ψ₀ : B ⊗[κ] κ[X] →ₐ[B] W := Algebra.TensorProduct.lTensor (S := B) B ev
  have hψ₀ : ψ₀.toRingHom.Flat := RingHom.Flat.lTensor B hev
  let e := polyEquivTensor' κ B
  let ψ : B[X] →ₐ[B] W := ψ₀.comp e.toAlgHom
  have hψ : ψ.toRingHom.Flat := RingHom.Flat.comp (RingHom.Flat.of_bijective e.bijective) hψ₀
  letI : Algebra B[X] W := ψ.toRingHom.toAlgebra
  haveI : Module.Flat B[X] W := hψ
  set 𝔡 := Q.comap (algebraMap B[X] W) with h𝔡
  set 𝔪 : Ideal B[X] := (maximalIdeal B).map Polynomial.C with h𝔪
  haveI : 𝔪.IsPrime := Ideal.isPrime_map_C_of_isPrime
  have hψC : ∀ b : B, algebraMap B[X] W (Polynomial.C b) = algebraMap B W b := fun b ↦
    ψ.commutes b
  have hle : 𝔪 ≤ 𝔡 := by
    rw [h𝔪, Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, h𝔡, Ideal.mem_comap, hψC, ← Ideal.mem_comap, hQ]
    exact hb
  have hEq : 𝔡 = 𝔪 := by
    by_contra hne
    have hlt : 𝔪 < 𝔡 := lt_of_le_of_ne hle (Ne.symm hne)
    haveI : Q.LiesOver 𝔡 := ⟨rfl⟩
    obtain ⟨Q', hQ'Q, hQ'p, -⟩ := Ideal.exists_ideal_lt_liesOver_of_lt (S := W) Q hlt
    have hdisj : Disjoint (Q.primeCompl : Set W) Q' := by
      rw [Set.disjoint_left]
      intro w hw hw'
      exact hw (hQ'Q.le hw')
    haveI := IsLocalization.isPrime_of_isPrime_disjoint Q.primeCompl WQ Q' hQ'p hdisj
    have hmax : (Q'.map (algebraMap W WQ)).IsMaximal := IsArtinianRing.isMaximal_of_isPrime _
    have h1 : Q'.map (algebraMap W WQ) = maximalIdeal WQ := IsLocalRing.eq_maximalIdeal hmax
    have h2 : (Q'.map (algebraMap W WQ)).under W = Q' :=
      IsLocalization.under_map_of_isPrime_disjoint Q.primeCompl WQ hQ'p hdisj
    rw [h1, Localization.AtPrime.under_maximalIdeal] at h2
    exact hQ'Q.ne h2.symm
  -- the residue-level evaluation
  set y : ResidueField WQ := residue WQ (algebraMap W WQ (1 ⊗ₜ k))
  have halg : IsAlgebraic (ResidueField B) y := Algebra.IsAlgebraic.isAlgebraic y
  obtain ⟨h, hne, hy⟩ := halg
  obtain ⟨h', rfl⟩ := Polynomial.map_surjective (residue B) residue_surjective h
  let Φ : B[X] →+* ResidueField WQ :=
    (residue WQ).comp ((algebraMap W WQ).comp (algebraMap B[X] W))
  let Φ' : B[X] →+* ResidueField WQ :=
    (Polynomial.aeval y).toRingHom.comp (Polynomial.mapRingHom (residue B))
  have hΦ : Φ = Φ' := by
    refine Polynomial.ringHom_ext (fun b ↦ ?_) ?_
    · simp only [Φ, Φ', RingHom.comp_apply, hψC, Polynomial.coe_mapRingHom, Polynomial.map_C,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_C]
      rw [← IsScalarTower.algebraMap_apply]
      rfl
    · simp only [Φ, Φ', RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
        AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Polynomial.aeval_X, y]
      congr 2
      change ψ₀ (e Polynomial.X) = _
      simp [e, ψ₀, ev]
      show Algebra.TensorProduct.map (AlgHom.id B B) (Polynomial.aeval k) (1 ⊗ₜ Polynomial.X) = _
      rw [Algebra.TensorProduct.map_tmul, Polynomial.aeval_X]
      rfl
  have hzero : Φ h' = 0 := by
    rw [hΦ]
    simpa [Φ'] using hy
  have hmem : h' ∈ 𝔡 := by
    rw [h𝔡, Ideal.mem_comap, ← IsLocalization.AtPrime.to_map_mem_maximal_iff WQ Q,
      ← IsLocalRing.residue_eq_zero_iff]
    exact hzero
  rw [hEq, h𝔪, ← IsLocalRing.ker_residue, ← Polynomial.ker_mapRingHom, RingHom.mem_ker] at hmem
  exact hne (by simpa using hmem)


-- @@ L277-277 verbatim
end ALG



-- @@ L280-280 verbatim
section FG


-- @@ L282-332 verbatim
/-- An algebraic residue extension of a finite-type algebra is finite. -/
theorem finite_of_isAlgebraic_residue {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (q : Ideal R) [q.IsPrime] (p : Ideal A) [p.IsPrime]
    (hq : q = p.comap (algebraMap R A))
    (halg : @Algebra.IsAlgebraic (ResidueField (Localization.AtPrime q))
      (ResidueField (Localization.AtPrime p)) _ _
      (ResidueField.map (Localization.localRingHom q p (algebraMap R A) hq)).toAlgebra) :
    @Module.Finite (ResidueField (Localization.AtPrime q)) (ResidueField (Localization.AtPrime p))
      _ _ (ResidueField.map (Localization.localRingHom q p (algebraMap R A) hq)).toAlgebra.toModule := by
  classical
  set κ := ResidueField (Localization.AtPrime q)
  set K := ResidueField (Localization.AtPrime p)
  letI : Algebra κ K := (ResidueField.map (Localization.localRingHom q p (algebraMap R A) hq)).toAlgebra
  let ι : A →+* K := (residue _).comp (algebraMap A (Localization.AtPrime p))
  have hι : ∀ r : R, ι (algebraMap R A r) =
      algebraMap κ K (residue _ (algebraMap R (Localization.AtPrime q) r)) := by
    intro r
    change _ = ResidueField.map _ _
    rw [ResidueField.map_residue, Localization.localRingHom_to_map]
    rfl
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R A).FG)
  set S := Algebra.adjoin κ (ι '' (s : Set A))
  have h1 : ∀ a : A, ι a ∈ S := by
    intro a
    have ha : a ∈ Algebra.adjoin R (s : Set A) := by rw [hs]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem x hx => exact Algebra.subset_adjoin ⟨x, hx, rfl⟩
    | algebraMap r => rw [hι]; exact S.algebraMap_mem _
    | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact S.mul_mem hx hy
  have h2 : S = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨z, rfl⟩ := residue_surjective z
    obtain ⟨a, b, rfl⟩ := IsLocalization.exists_mk'_eq p.primeCompl z
    have hb : ι b ≠ 0 := by
      change residue _ (algebraMap A (Localization.AtPrime p) b) ≠ 0
      rw [Ne, IsLocalRing.residue_eq_zero_iff,
        IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime p) p]
      exact b.2
    have hz : residue _ (IsLocalization.mk' (Localization.AtPrime p) a b) = ι a * (ι b)⁻¹ := by
      rw [eq_mul_inv_iff_mul_eq₀ hb]
      change residue _ (IsLocalization.mk' (Localization.AtPrime p) a b) *
        residue _ (algebraMap A (Localization.AtPrime p) b) = residue _ (algebraMap A _ a)
      rw [← map_mul, IsLocalization.mk'_spec]
    rw [hz]
    exact S.mul_mem (h1 a) (Subalgebra.inv_mem_of_algebraic S (x := ⟨ι b, h1 b⟩)
      (halg.isAlgebraic (ι b)))
  haveI : Algebra.FiniteType κ K := ⟨⟨s.image ι, by rw [Finset.coe_image]; exact h2⟩⟩
  haveI : Algebra.IsIntegral κ K := Algebra.IsAlgebraic.isIntegral
  exact Algebra.IsIntegral.finite


-- @@ L334-334 verbatim
end FG



-- @@ L337-337 verbatim
section Core


-- @@ L339-339 verbatim
open TensorProduct


-- @@ L341-345 verbatim
theorem isLocalRing_quotient {S : Type*} [CommRing S] [IsLocalRing S] (I : Ideal S)
    (h : I ≤ maximalIdeal S) : IsLocalRing (S ⧸ I) := by
  haveI : Nontrivial (S ⧸ I) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal S).ne_top h)
  exact IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective


-- @@ L347-349 verbatim
theorem map_le_maximalIdeal {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (f : R →+* S) [IsLocalHom f] : (maximalIdeal R).map f ≤ maximalIdeal S := by
  rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]



-- @@ L352-356 verbatim
theorem comap_mk_maximalIdeal {S : Type*} [CommRing S] [IsLocalRing S] (J : Ideal S)
    [IsLocalRing (S ⧸ J)] :
    (maximalIdeal (S ⧸ J)).comap (Ideal.Quotient.mk J) = maximalIdeal S :=
  IsLocalRing.eq_maximalIdeal
    (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)


-- @@ L358-361 verbatim
theorem finrank_eq_toNat_length (k V : Type*) [Field k] [AddCommGroup V] [Module k V] :
    Module.finrank k V = (Module.length k V).toNat := by
  rw [Module.length_eq_rank, Cardinal.toNat_toENat]
  rfl


-- @@ L363-369 verbatim
theorem residueField_map_bijective {X Y : Type*} [CommRing X] [CommRing Y] [IsLocalRing X]
    [IsLocalRing Y] (π : X →+* Y) [IsLocalHom π] (hπ : Function.Surjective π) :
    Function.Bijective (ResidueField.map π) := by
  refine ⟨(ResidueField.map π).injective, fun y ↦ ?_⟩
  obtain ⟨y, rfl⟩ := residue_surjective y
  obtain ⟨x, rfl⟩ := hπ y
  exact ⟨residue X x, ResidueField.map_residue _ _⟩


-- @@ L371-386 verbatim
theorem ld_eq_of_surj {R S R' S' : Type*} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [IsLocalRing R] [IsLocalRing R'] [IsLocalRing S] [IsLocalRing S'] (φ : R →+* S)
    (ψ : R' →+* S') [IsLocalHom φ] [IsLocalHom ψ] (π₁ : R →+* R') (π₂ : S →+* S')
    [IsLocalHom π₁] [IsLocalHom π₂] (h₁ : Function.Surjective π₁)
    (h₂ : Function.Surjective π₂) (h : ∀ r, π₂ (φ r) = ψ (π₁ r)) : ld φ = ld ψ := by
  unfold ld
  letI := (ResidueField.map φ).toAlgebra
  letI := (ResidueField.map ψ).toAlgebra
  refine Algebra.finrank_eq_of_equiv_equiv
    (RingEquiv.ofBijective _ (residueField_map_bijective π₁ h₁))
    (RingEquiv.ofBijective _ (residueField_map_bijective π₂ h₂)) ?_
  ext x
  obtain ⟨x, rfl⟩ := residue_surjective x
  change ResidueField.map ψ (ResidueField.map π₁ (residue R x)) =
    ResidueField.map π₂ (ResidueField.map φ (residue R x))
  simp [ResidueField.map_residue, h]


-- @@ L388-394 verbatim
theorem isLocalHom_of_comap {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing R]
    [IsLocalRing S] (f : R →+* S) (h : maximalIdeal R ≤ (maximalIdeal S).comap f) :
    IsLocalHom f := by
  refine ⟨fun a ha ↦ ?_⟩
  by_contra hna
  have : f a ∈ maximalIdeal S := h hna
  exact (IsLocalRing.mem_maximalIdeal _).mp this ha


-- @@ L396-401 verbatim
theorem lc_localRingHom_congr {R S : Type*} [CommRing R] [CommRing S] {I₁ I₂ : Ideal R}
    [I₁.IsPrime] [I₂.IsPrime] (J : Ideal S) [J.IsPrime] (f : R →+* S) (h₁ : I₁ = J.comap f)
    (h₂ : I₂ = J.comap f) :
    lc (Localization.localRingHom I₁ J f h₁) = lc (Localization.localRingHom I₂ J f h₂) := by
  obtain rfl : I₁ = I₂ := h₁.trans h₂.symm
  rfl


-- @@ L403-408 verbatim
theorem ld_localRingHom_congr {R S : Type*} [CommRing R] [CommRing S] {I₁ I₂ : Ideal R}
    [I₁.IsPrime] [I₂.IsPrime] (J : Ideal S) [J.IsPrime] (f : R →+* S) (h₁ : I₁ = J.comap f)
    (h₂ : I₂ = J.comap f) :
    ld (Localization.localRingHom I₁ J f h₁) = ld (Localization.localRingHom I₂ J f h₂) := by
  obtain rfl : I₁ = I₂ := h₁.trans h₂.symm
  rfl


-- @@ L410-415 verbatim
/-- The map `Rₚ → S_J` induced by `f` for an abstract localization `Rₚ`. -/
def mapAtPrime {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) [I.IsPrime]
    (J : Ideal S) [J.IsPrime] (f : R →+* S) (hIJ : I = J.comap f) (Rₚ : Type*) [CommRing Rₚ]
    [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ I] : Rₚ →+* Localization.AtPrime J :=
  IsLocalization.map (M := I.primeCompl) (T := J.primeCompl) (Localization.AtPrime J) f
    (by subst hIJ; exact fun _ h ↦ h)


-- @@ L417-421 verbatim
theorem mapAtPrime_algebraMap {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) [I.IsPrime]
    (J : Ideal S) [J.IsPrime] (f : R →+* S) (hIJ : I = J.comap f) (Rₚ : Type*) [CommRing Rₚ]
    [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ I] (x : R) :
    mapAtPrime I J f hIJ Rₚ (algebraMap R Rₚ x) = algebraMap S _ (f x) :=
  IsLocalization.map_eq _ _


-- @@ L423-435 verbatim
instance isLocalHom_mapAtPrime {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) [I.IsPrime]
    (J : Ideal S) [J.IsPrime] (f : R →+* S) (hIJ : I = J.comap f) (Rₚ : Type*) [CommRing Rₚ]
    [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ I] : IsLocalHom (mapAtPrime I J f hIJ Rₚ) := by
  refine ⟨fun x hx ↦ ?_⟩
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective I.primeCompl x
  unfold mapAtPrime at hx
  rw [IsLocalization.map_mk'] at hx
  rw [IsLocalization.AtPrime.isUnit_mk'_iff] at hx ⊢
  intro ha
  apply hx
  change f a ∈ J
  rw [hIJ] at ha
  exact ha


-- @@ L437-446 verbatim
theorem ld_localRingHom_eq_map {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) [I.IsPrime]
    (J : Ideal S) [J.IsPrime] (f : R →+* S) (hIJ : I = J.comap f) (Rₚ : Type*) [CommRing Rₚ]
    [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ I] [IsLocalRing Rₚ] :
    ld (Localization.localRingHom _ J f rfl) = ld (mapAtPrime I J f hIJ Rₚ) := by
  subst hIJ
  refine ld_eq_of_equiv _ _ (IsLocalization.algEquiv (J.comap f).primeCompl
    (Localization.AtPrime (J.comap f)) Rₚ).toRingEquiv (RingEquiv.refl _) (fun r ↦ ?_)
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (J.comap f).primeCompl r
  simp only [RingEquiv.refl_apply, AlgEquiv.toRingEquiv_eq_coe, AlgEquiv.coe_ringEquiv,
    IsLocalization.algEquiv_mk', Localization.localRingHom_mk', mapAtPrime, IsLocalization.map_mk']



-- @@ L449-459 verbatim
theorem lc_eq_length_of_surj {R S N : Type*} [CommRing R] [CommRing S] [CommRing N]
    [IsLocalRing R] (φ : R →+* S) (π : S →+* N) (hπ : Function.Surjective π)
    (hker : RingHom.ker π = (maximalIdeal R).map φ) :
    letI := π.toAlgebra
    lc φ = (Module.length S N).toNat := by
  letI := π.toAlgebra
  unfold lc
  congr 1
  let e₁ := Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId S N) hπ
  let e₂ := Ideal.quotientEquivAlgOfEq S (hker : RingHom.ker (Algebra.ofId S N) = _)
  exact (e₂.symm.trans e₁).toLinearEquiv.length_eq



-- @@ L462-468 verbatim
theorem toNat_length_restrict (B N : Type*) [CommRing B] [CommRing N] [IsLocalRing B]
    [IsLocalRing N] [Algebra B N] [IsLocalHom (algebraMap B N)] :
    (Module.length B N).toNat = (Module.length N N).toNat * ld (algebraMap B N) := by
  rw [IsLocalRing.length_restrictScalars B N N, ENat.toNat_mul]
  congr 1
  unfold ld
  rw [residueField_map_toAlgebra, finrank_eq_toNat_length]



-- @@ L471-479 verbatim
theorem toNat_sum_of_ne_top {ι : Type*} (s : Finset ι) (f : ι → ℕ∞) (h : ∑ i ∈ s, f i ≠ ⊤) :
    (∑ i ∈ s, f i).toNat = ∑ i ∈ s, (f i).toNat := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha] at h ⊢
    rw [Finset.sum_insert ha, ENat.toNat_add (WithTop.add_ne_top.mp h).1 (WithTop.add_ne_top.mp h).2,
      ih (WithTop.add_ne_top.mp h).2]


-- @@ L481-481 verbatim
variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R']


-- @@ L483-483 verbatim
local notation "rR'" => (Algebra.TensorProduct.includeRight.toRingHom : R' →+* A ⊗[R] R')


-- @@ L485-490 verbatim
variable (q : Ideal R) [q.IsPrime] (p : Ideal A) [p.IsPrime] (q' : Ideal R') [q'.IsPrime]
  (hp : q = p.comap (algebraMap R A))
  {O₂ : Type u} [CommRing O₂] [IsLocalRing O₂] [Algebra R' O₂] [IsLocalization.AtPrime O₂ q']
  [Algebra R O₂] [IsScalarTower R R' O₂]
  (φB : Localization.AtPrime q →+* O₂) [IsLocalHom φB]
  (hφB : ∀ r, φB (algebraMap R _ r) = algebraMap R' O₂ (algebraMap R R' r))


-- @@ L492-492 verbatim
local notation "𝒪" => Localization.AtPrime q

-- @@ L493-493 verbatim
local notation "𝒪₁" => Localization.AtPrime p

-- @@ L494-494 verbatim
local notation "𝒪₂" => O₂

-- @@ L495-495 verbatim
local notation "φA" => Localization.localRingHom q p (algebraMap R A) hp

-- @@ L496-496 verbatim
local notation "𝔍" => Ideal.map φB (maximalIdeal 𝒪)

-- @@ L497-497 verbatim
local notation "𝔅" => 𝒪₂ ⧸ 𝔍

-- @@ L498-498 verbatim
local notation "𝕜" => ResidueField 𝒪

-- @@ L499-499 verbatim
local notation "𝕂" => ResidueField 𝒪₁

-- @@ L500-500 verbatim
local notation "𝕎" => 𝔅 ⊗[𝕜] 𝕂

-- @@ L501-501 verbatim
local notation "𝕋" => A ⊗[R] R'


-- @@ L503-941 verbatim
set_option maxHeartbeats 400000 in
include hφB in
theorem core [Algebra.FiniteType R A] :
    ∃ s : Finset (PrimeSpectrum (A ⊗[R] R')),
      (∀ P ∈ s, P.asIdeal.comap (algebraMap A (A ⊗[R] R')) = p ∧ P.asIdeal.comap rR' = q') ∧
      (∀ P : PrimeSpectrum (A ⊗[R] R'), P.asIdeal.comap (algebraMap A _) = p →
        P.asIdeal.comap rR' = q' →
        lc (Localization.localRingHom _ P.asIdeal (algebraMap A (A ⊗[R] R')) rfl) *
          ld (Localization.localRingHom _ P.asIdeal rR' rfl) ≠ 0 → P ∈ s) ∧
      ∑ P ∈ s, lc (Localization.localRingHom _ P.asIdeal (algebraMap A (A ⊗[R] R')) rfl) *
          ld (Localization.localRingHom _ P.asIdeal rR' rfl) =
        ld (Localization.localRingHom q p (algebraMap R A) hp) * lc φB := by
  classical
  have hI : 𝔍 ≤ maximalIdeal 𝒪₂ := map_le_maximalIdeal φB
  haveI : IsLocalRing 𝔅 := isLocalRing_quotient 𝔍 hI
  letI : Algebra 𝕜 𝕂 := (ResidueField.map φA).toAlgebra
  let κBq : 𝕜 →+* 𝔅 := Ideal.Quotient.lift (maximalIdeal 𝒪) ((Ideal.Quotient.mk 𝔍).comp φB)
    (fun x hx ↦ Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ hx))
  letI : Algebra 𝕜 𝔅 := κBq.toAlgebra
  -- the map θ₀ : T → W
  let ιK : A →+* 𝕂 := (residue 𝒪₁).comp (algebraMap A 𝒪₁)
  have e2 : ∀ r : R, algebraMap R 𝔅 r = κBq (residue 𝒪 (algebraMap R 𝒪 r)) := by
    intro r
    change _ = Ideal.Quotient.lift _ _ _ (Ideal.Quotient.mk _ _)
    rw [Ideal.Quotient.lift_mk, ← Ideal.Quotient.mk_algebraMap]
    change Ideal.Quotient.mk 𝔍 _ = Ideal.Quotient.mk 𝔍 (φB _)
    rw [hφB, IsScalarTower.algebraMap_apply R R' 𝒪₂]
  have e1 : ∀ r : R, ιK (algebraMap R A r) = algebraMap 𝕜 𝕂 (residue 𝒪 (algebraMap R 𝒪 r)) := by
    intro r
    change _ = ResidueField.map φA _
    rw [ResidueField.map_residue, Localization.localRingHom_to_map]
    rfl
  let fB : R' →ₐ[R] 𝕎 := (Algebra.TensorProduct.includeLeft (R := 𝕜) (S := R) (A := 𝔅)
    (B := 𝕂)).comp (IsScalarTower.toAlgHom R R' 𝔅)
  let fA : A →ₐ[R] 𝕎 :=
    { toRingHom := Algebra.TensorProduct.includeRight.toRingHom.comp ιK
      commutes' := by
        intro r
        rw [Algebra.TensorProduct.algebraMap_apply]
        change Algebra.TensorProduct.includeRight (ιK (algebraMap R A r)) = _
        rw [e1, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply, e2]
        rfl }
  let θ₀ := (Algebra.TensorProduct.lift fA fB (fun x y ↦ Commute.all (fA x) (fB y))).toRingHom
  have hθ₀ : ∀ (a : A) (r' : R'), θ₀ (a ⊗ₜ r') = (algebraMap R' 𝔅 r' ⊗ₜ ιK a : 𝕎) := by
    intro a r'
    change Algebra.TensorProduct.lift fA fB _ (a ⊗ₜ r') = _
    rw [Algebra.TensorProduct.lift_tmul]
    change (1 ⊗ₜ ιK a : 𝕎) * (algebraMap R' 𝔅 r' ⊗ₜ 1) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
  have hjB : ∀ x : R', algebraMap R' 𝔅 x = Ideal.Quotient.mk 𝔍 (algebraMap R' 𝒪₂ x) := by
    intro x; rw [Ideal.Quotient.mk_algebraMap]
  -- every element of `W` is `θ₀ t / θ₀ m` with `θ₀ m` a unit
  have hsurj : ∀ w : 𝕎, ∃ t m : 𝕋, IsUnit (θ₀ m) ∧ w * θ₀ m = θ₀ t := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨0, 1, by simp, by simp⟩
    | tmul b k =>
      obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective b
      obtain ⟨⟨r', s⟩, rfl⟩ := IsLocalization.mk'_surjective q'.primeCompl o
      obtain ⟨x, rfl⟩ := residue_surjective k
      obtain ⟨⟨a, u⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl x
      refine ⟨a ⊗ₜ r', (u : A) ⊗ₜ (s : R'), ?_, ?_⟩
      · rw [hθ₀, ← mul_one (algebraMap R' 𝔅 s), ← one_mul (ιK u),
          ← Algebra.TensorProduct.tmul_mul_tmul]
        refine IsUnit.mul ?_ ?_
        · refine IsUnit.map (Algebra.TensorProduct.includeLeft (S := 𝕜) (B := 𝕂)) ?_
          rw [hjB]
          refine IsUnit.map (Ideal.Quotient.mk 𝔍) ?_
          exact (IsLocalization.AtPrime.isUnit_to_map_iff 𝒪₂ q' s).mpr s.2
        · refine IsUnit.map (Algebra.TensorProduct.includeRight (A := 𝔅)) ?_
          rw [isUnit_iff_ne_zero]
          change residue 𝒪₁ (algebraMap A 𝒪₁ u) ≠ 0
          rw [Ne, IsLocalRing.residue_eq_zero_iff,
            IsLocalization.AtPrime.to_map_mem_maximal_iff 𝒪₁ p]
          exact u.2
      · rw [hθ₀, hθ₀, Algebra.TensorProduct.tmul_mul_tmul]
        congr 1
        · rw [hjB, hjB, ← map_mul, IsLocalization.mk'_spec]
        · change residue 𝒪₁ _ * residue 𝒪₁ _ = residue 𝒪₁ _
          rw [← map_mul, IsLocalization.mk'_spec]
    | add w₁ w₂ h₁ h₂ =>
      obtain ⟨t₁, m₁, hm₁, e₁⟩ := h₁
      obtain ⟨t₂, m₂, hm₂, e₂⟩ := h₂
      refine ⟨t₁ * m₂ + t₂ * m₁, m₁ * m₂, ?_, ?_⟩
      · rw [map_mul]; exact hm₁.mul hm₂
      · rw [map_add, map_mul, map_mul, map_mul, ← e₁, ← e₂]
        ring
  -- primes of `W` are determined by their contraction to `T`
  have hmemQ : ∀ (Q : Ideal 𝕎) [Q.IsPrime] (w : 𝕎) (t m : 𝕋), IsUnit (θ₀ m) →
      w * θ₀ m = θ₀ t → (w ∈ Q ↔ t ∈ Q.comap θ₀) := by
    intro Q _ w t m hm hw
    rw [Ideal.mem_comap, ← hw]
    constructor
    · intro h; exact Q.mul_mem_right _ h
    · intro h
      rcases Ideal.IsPrime.mem_or_mem ‹_› h with h | h
      · exact h
      · exact absurd (Q.eq_top_of_isUnit_mem h hm) (Ideal.IsPrime.ne_top ‹_›)
  have huniq : ∀ (Q₁ Q₂ : Ideal 𝕎) [Q₁.IsPrime] [Q₂.IsPrime], Q₁.comap θ₀ = Q₂.comap θ₀ →
      Q₁ = Q₂ := by
    intro Q₁ Q₂ _ _ h
    ext w
    obtain ⟨t, m, hm, hw⟩ := hsurj w
    rw [hmemQ Q₁ w t m hm hw, hmemQ Q₂ w t m hm hw, h]
  -- the local analysis at a prime `P` of `T` over `p` and `q'`
  have key : ∀ (P : Ideal 𝕋) [P.IsPrime] (hPA : p = P.comap (algebraMap A 𝕋))
      (hPB : q' = P.comap rR'),
      ∃ Q : Ideal 𝕎, ∃ _ : Q.IsPrime, Q.comap θ₀ = P ∧
        Q.comap (algebraMap 𝔅 𝕎) = maximalIdeal 𝔅 ∧
        lc (Localization.localRingHom p P (algebraMap A 𝕋) hPA) *
          ld (mapAtPrime q' P rR' hPB O₂) =
        (Module.length 𝔅 (Localization.AtPrime Q)).toNat := by
    intro P _ hPA hPB
    obtain ⟨S, _, ⟨e⟩⟩ : ∃ (S : Type u) (_ : CommRing S),
        Nonempty (Localization.AtPrime P ≃+* S) := ⟨_, _, ⟨RingEquiv.refl _⟩⟩
    haveI : Nontrivial S := e.injective.nontrivial
    haveI : IsLocalRing S := IsLocalRing.of_surjective' (e : Localization.AtPrime P →+* S)
      e.surjective
    haveI : IsLocalHom (e : Localization.AtPrime P →+* S) := isLocalHom_of_comap _ (by
      intro x hx
      rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      exact (IsLocalRing.mem_maximalIdeal _).mp hx
        (by simpa using hu.map (e.symm : S →+* Localization.AtPrime P)))
    let φ₁ := (e : Localization.AtPrime P →+* S).comp
      (Localization.localRingHom p P (algebraMap A 𝕋) hPA)
    let φ₂ := (e : Localization.AtPrime P →+* S).comp (mapAtPrime q' P rR' hPB O₂)
    have hlc : lc (Localization.localRingHom p P (algebraMap A 𝕋) hPA) = lc φ₁ :=
      lc_eq_of_equiv _ _ (RingEquiv.refl _) e (fun _ ↦ rfl)
    have hld : ld (mapAtPrime q' P rR' hPB O₂) = ld φ₂ :=
      ld_eq_of_equiv _ _ (RingEquiv.refl _) e (fun _ ↦ rfl)
    rw [hlc, hld]
    let ι : 𝕋 →+* S := (e : Localization.AtPrime P →+* S).comp (algebraMap 𝕋 _)
    have hι : ∀ t, ι t ∈ maximalIdeal S ↔ t ∈ P := by
      intro t
      rw [← IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P,
        ← IsLocalRing.maximalIdeal_comap (e : Localization.AtPrime P →+* S), Ideal.mem_comap]
      rfl
    let J := (maximalIdeal 𝒪₁).map φ₁
    have hJ : J ≤ maximalIdeal S := map_le_maximalIdeal φ₁
    obtain ⟨N, _, π, hπ, hker⟩ : ∃ (N : Type u) (_ : CommRing N)
        (π : S →+* N), Function.Surjective π ∧ RingHom.ker π = J :=
      ⟨_, _, Ideal.Quotient.mk J, Ideal.Quotient.mk_surjective, Ideal.mk_ker⟩
    have hπJ : ∀ x, π x = 0 ↔ x ∈ J := fun x ↦ by rw [← RingHom.mem_ker, hker]
    haveI : Nontrivial N := by
      refine ⟨⟨0, 1, fun h ↦ ?_⟩⟩
      have : (1 : S) ∈ J := (hπJ 1).mp (by rw [map_one]; exact h.symm)
      exact (maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr (hJ this))
    haveI : IsLocalRing N := IsLocalRing.of_surjective' π hπ
    have hπmax : (maximalIdeal N).comap π = maximalIdeal S :=
      IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ hπ)
    haveI : IsLocalHom π := isLocalHom_of_comap π hπmax.ge
    let gK : 𝕂 →+* N :=
      Ideal.Quotient.lift (maximalIdeal 𝒪₁) (π.comp φ₁)
        (fun x hx ↦ (hπJ _).mpr (Ideal.mem_map_of_mem _ hx))
    have hcomm : φ₂.comp φB = φ₁.comp φA := by
      refine IsLocalization.ringHom_ext q.primeCompl (RingHom.ext fun r ↦ ?_)
      simp only [RingHom.comp_apply]
      rw [hφB, Localization.localRingHom_to_map]
      change e (mapAtPrime q' P rR' hPB O₂ (algebraMap R' O₂ _)) =
        e (Localization.localRingHom p P _ hPA (algebraMap A 𝒪₁ _))
      rw [mapAtPrime_algebraMap, Localization.localRingHom_to_map]
      refine congrArg (fun t ↦ e (algebraMap 𝕋 (Localization.AtPrime P) t)) ?_
      change Algebra.TensorProduct.includeRight (algebraMap R R' r) = _
      rw [AlgHom.commutes, IsScalarTower.algebraMap_apply R A 𝕋]
    have hcomm' : ∀ x, φ₂ (φB x) = φ₁ (φA x) := fun x ↦ congrArg (· x) hcomm
    let gB : 𝔅 →+* N :=
      Ideal.Quotient.lift 𝔍 (π.comp φ₂) (by
        intro x hx
        have hle : 𝔍 ≤ RingHom.ker (π.comp φ₂) := by
          rw [Ideal.map_le_iff_le_comap]
          intro y hy
          rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, hcomm', hπJ]
          apply Ideal.mem_map_of_mem
          rw [← IsLocalRing.maximalIdeal_comap φA] at hy
          exact hy
        exact hle hx)
    letI : Algebra 𝕜 N := (gK.comp (algebraMap 𝕜 𝕂)).toAlgebra
    let gK' : 𝕂 →ₐ[𝕜] N := { gK with commutes' := fun _ ↦ rfl }
    let gB' : 𝔅 →ₐ[𝕜] N :=
      { gB with
        commutes' := by
          intro c
          obtain ⟨x, rfl⟩ := residue_surjective c
          change gB (κBq (residue 𝒪 x)) = gK (ResidueField.map φA (residue 𝒪 x))
          rw [ResidueField.map_residue]
          change gB (Ideal.Quotient.mk 𝔍 (φB x)) = gK (residue 𝒪₁ (φA x))
          rw [Ideal.Quotient.lift_mk]
          exact (congrArg π (hcomm' x)).trans
            (Ideal.Quotient.lift_mk (maximalIdeal 𝒪₁) (π.comp φ₁) _).symm }
    let θP := (Algebra.TensorProduct.lift gB' gK'
      (fun x y ↦ Commute.all (gB' x) (gK' y))).toRingHom
    have hθP : ∀ b k, θP (b ⊗ₜ k) = gB b * gK k := fun b k ↦
      Algebra.TensorProduct.lift_tmul _ _ _ b k
    have hgB : ∀ o, gB (Ideal.Quotient.mk 𝔍 o) = π (φ₂ o) := fun o ↦
      Ideal.Quotient.lift_mk _ _ _
    have hgK : ∀ o, gK (residue 𝒪₁ o) = π (φ₁ o) := fun o ↦
      Ideal.Quotient.lift_mk _ _ _
    have hC1 : ∀ t, θP (θ₀ t) = π (ι t) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul a r' =>
        rw [hθ₀, hθP, hjB, hgB]
        change _ * gK (residue 𝒪₁ (algebraMap A 𝒪₁ a)) = _
        rw [hgK, ← map_mul]
        refine congrArg π ?_
        change e (mapAtPrime q' P rR' hPB O₂ _) * e (Localization.localRingHom p P _ hPA _) =
          e (algebraMap 𝕋 _ (a ⊗ₜ r'))
        rw [mapAtPrime_algebraMap, Localization.localRingHom_to_map, ← map_mul, ← map_mul]
        refine congrArg (fun t ↦ e (algebraMap 𝕋 (Localization.AtPrime P) t)) ?_
        change (1 ⊗ₜ r' : 𝕋) * (a ⊗ₜ 1) = _
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
      | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
    have hC2 : ∀ b, θP (algebraMap 𝔅 𝕎 b) = gB b := by
      intro b
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hθP,
        map_one, mul_one]
    let Q := (maximalIdeal N).comap θP
    haveI hQp : Q.IsPrime := Ideal.comap_isPrime _ _
    have hQθ : Q.comap θ₀ = P := by
      ext t
      rw [Ideal.mem_comap, Ideal.mem_comap, hC1, ← Ideal.mem_comap, hπmax, hι]
    haveI hgBloc : IsLocalHom gB := isLocalHom_of_comap gB (by
      intro b hb
      obtain ⟨o, rfl⟩ := Ideal.Quotient.mk_surjective b
      rw [Ideal.mem_comap, hgB, ← Ideal.mem_comap, hπmax]
      have ho : o ∈ maximalIdeal O₂ := by rw [← comap_mk_maximalIdeal 𝔍]; exact hb
      rw [← IsLocalRing.maximalIdeal_comap φ₂] at ho
      exact ho)
    have hgood : Q.comap (algebraMap 𝔅 𝕎) = maximalIdeal 𝔅 := by
      rw [Ideal.comap_comap]
      have : θP.comp (algebraMap 𝔅 𝕎) = gB := RingHom.ext hC2
      rw [this]
      exact IsLocalRing.maximalIdeal_comap gB
    have hunits : ∀ y : Q.primeCompl, IsUnit (θP y) := by
      intro y
      have : θP y ∉ maximalIdeal N := y.2
      by_contra h
      exact this ((IsLocalRing.mem_maximalIdeal _).mpr h)
    let χ₀ : Localization.AtPrime Q →+* N := IsLocalization.lift hunits
    have hχ₀ : ∀ w, χ₀ (algebraMap 𝕎 _ w) = θP w := IsLocalization.lift_eq hunits
    have hsur : Function.Surjective χ₀ := by
      intro n
      obtain ⟨z, rfl⟩ := hπ n
      obtain ⟨z, rfl⟩ := e.surjective z
      obtain ⟨⟨t, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl z
      have hs : θ₀ s ∈ Q.primeCompl := by
        change θ₀ (s : 𝕋) ∉ Q
        rw [← Ideal.mem_comap, hQθ]
        exact s.2
      refine ⟨IsLocalization.mk' _ (θ₀ t) ⟨θ₀ s, hs⟩, ?_⟩
      rw [IsLocalization.lift_mk'_spec]
      change θP (θ₀ t) = θP (θ₀ s) * π (e _)
      rw [hC1, hC1]
      change π (e (algebraMap 𝕋 _ t)) = π (e (algebraMap 𝕋 _ s)) * π (e _)
      rw [← map_mul, ← map_mul, IsLocalization.mk'_spec']
    have hθ₀p : ∀ a ∈ p, θ₀ (algebraMap A 𝕋 a) = 0 := by
      intro a ha
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, hθ₀]
      have : ιK a = 0 := by
        change residue 𝒪₁ (algebraMap A 𝒪₁ a) = 0
        rw [IsLocalRing.residue_eq_zero_iff,
          IsLocalization.AtPrime.to_map_mem_maximal_iff 𝒪₁ p]
        exact ha
      rw [this, TensorProduct.tmul_zero]
    have hJeq : J = ((p.map (algebraMap A 𝕋)).map (algebraMap 𝕋 (Localization.AtPrime P))).map
        (e : Localization.AtPrime P →+* S) := by
      change (maximalIdeal 𝒪₁).map φ₁ = _
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_map, Ideal.map_map]
      congr 1
      ext a
      change e (Localization.localRingHom p P _ hPA (algebraMap A 𝒪₁ a)) = _
      rw [Localization.localRingHom_to_map]
      rfl
    have hinj : Function.Injective χ₀ := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨⟨w, u⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl x
      rw [IsLocalization.lift_mk'_spec, mul_zero] at hx
      obtain ⟨t, m, hm, hw⟩ := hsurj w
      have h1 : π (ι t) = 0 := by rw [← hC1, ← hw, map_mul, hx, zero_mul]
      rw [hπJ, hJeq, Ideal.map_comap_of_equiv, Ideal.mem_comap] at h1
      change e.symm (e _) ∈ _ at h1
      rw [RingEquiv.symm_apply_apply,
        IsLocalization.mem_map_algebraMap_iff P.primeCompl (Localization.AtPrime P)] at h1
      obtain ⟨⟨i, c₀⟩, hic⟩ := h1
      rw [← map_mul, IsLocalization.eq_iff_exists P.primeCompl] at hic
      obtain ⟨c, hc⟩ := hic
      have hi : θ₀ i = 0 := by
        have : p.map (algebraMap A 𝕋) ≤ RingHom.ker θ₀ := by
          rw [Ideal.map_le_iff_le_comap]
          intro a ha
          rw [Ideal.mem_comap, RingHom.mem_ker]
          exact hθ₀p a ha
        exact this i.2
      have hv : θ₀ ((c : 𝕋) * c₀) ∈ Q.primeCompl := by
        change θ₀ _ ∉ Q
        rw [← Ideal.mem_comap, hQθ]
        exact P.primeCompl.mul_mem c.2 c₀.2
      rw [IsLocalization.mk'_eq_zero_iff]
      refine ⟨⟨_, hv⟩, ?_⟩
      have h2 : θ₀ ((c : 𝕋) * c₀) * θ₀ t = 0 := by
        rw [← map_mul, mul_assoc, mul_comm (c₀ : 𝕋), hc, map_mul, hi, mul_zero]
      rw [← hw, ← mul_assoc] at h2
      exact (hm.mul_left_eq_zero).mp h2
    letI : Algebra 𝔅 N := gB.toAlgebra
    have hχB : ∀ b, (RingEquiv.ofBijective χ₀ ⟨hinj, hsur⟩)
        (algebraMap 𝔅 (Localization.AtPrime Q) b) = algebraMap 𝔅 N b := by
      intro b
      change χ₀ _ = gB b
      rw [IsScalarTower.algebraMap_apply 𝔅 𝕎 (Localization.AtPrime Q), hχ₀, hC2]
    have hlen1 : Module.length 𝔅 (Localization.AtPrime Q) = Module.length 𝔅 N :=
      (AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective χ₀ ⟨hinj, hsur⟩) hχB).toLinearEquiv.length_eq
    haveI : IsLocalHom (algebraMap 𝔅 N) := hgBloc
    have hlc' : lc φ₁ = (Module.length N N).toNat := by
      rw [lc_eq_length_of_surj φ₁ π hπ hker]
      letI := π.toAlgebra
      rw [Module.length_eq_of_surjective (R := N) (S := S) (M := N) hπ]
    haveI : IsLocalHom (Ideal.Quotient.mk 𝔍) := isLocalHom_of_comap _ (by
      rw [comap_mk_maximalIdeal])
    have hld' : ld φ₂ = ld (algebraMap 𝔅 N) :=
      ld_eq_of_surj φ₂ gB (Ideal.Quotient.mk 𝔍) π Ideal.Quotient.mk_surjective hπ
        (fun o ↦ (hgB o).symm)
    refine ⟨Q, hQp, hQθ, hgood, ?_⟩
    exact (congrArg₂ (· * ·) hlc' hld').trans
      ((toNat_length_restrict 𝔅 N).symm.trans (congrArg ENat.toNat hlen1.symm))
  have hRHS_lc : lc φB = (Module.length 𝔅 𝔅).toNat := by
    unfold lc
    rw [Module.length_eq_of_surjective (R := 𝔅) (S := O₂) (M := 𝔅) Ideal.Quotient.mk_surjective]
  have hRHS_ld : ld (Localization.localRingHom q p (algebraMap R A) hp) =
      Module.finrank 𝕜 𝕂 := rfl
  have hterm : ∀ P : PrimeSpectrum 𝕋, P.asIdeal.comap (algebraMap A 𝕋) = p →
      P.asIdeal.comap rR' = q' →
      ∃ Q : Ideal 𝕎, ∃ _ : Q.IsPrime, Q.comap θ₀ = P.asIdeal ∧
        Q.comap (algebraMap 𝔅 𝕎) = maximalIdeal 𝔅 ∧
        lc (Localization.localRingHom _ P.asIdeal (algebraMap A 𝕋) rfl) *
          ld (Localization.localRingHom _ P.asIdeal rR' rfl) =
        (Module.length 𝔅 (Localization.AtPrime Q)).toNat := by
    intro P hA hB
    obtain ⟨Q, hQp, h1, h2, h3⟩ := key P.asIdeal hA.symm hB.symm
    refine ⟨Q, hQp, h1, h2, ?_⟩
    rw [lc_localRingHom_congr P.asIdeal (algebraMap A 𝕋) rfl hA.symm,
      ld_localRingHom_eq_map q' P.asIdeal rR' hB.symm O₂]
    exact h3
  by_cases hcase : Module.Finite 𝕜 𝕂 ∧ Module.length 𝔅 𝔅 ≠ ⊤
  · obtain ⟨hK, hB⟩ := hcase
    have hW : Module.length 𝔅 𝕎 ≠ ⊤ := by
      rw [length_W_eq]
      exact WithTop.mul_ne_top (ENat.coe_ne_top _) hB
    have hallgood := comap_eq_maximalIdeal_of_length_ne_top hW
    obtain ⟨_, hsum⟩ := length_W_eq_sum hW
    let Φ : PrimeSpectrum 𝕎 → PrimeSpectrum 𝕋 := fun Q ↦ ⟨Q.asIdeal.comap θ₀, inferInstance⟩
    have hΦA : ∀ Q, (Φ Q).asIdeal.comap (algebraMap A 𝕋) = p := by
      intro Q
      ext a
      change θ₀ (algebraMap A 𝕋 a) ∈ Q.asIdeal ↔ a ∈ p
      constructor
      · intro h
        by_contra ha
        have hu : IsUnit (θ₀ (algebraMap A 𝕋 a)) := by
          rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
            hθ₀, map_one]
          refine IsUnit.map (Algebra.TensorProduct.includeRight (A := 𝔅)) ?_
          rw [isUnit_iff_ne_zero]
          change residue 𝒪₁ (algebraMap A 𝒪₁ a) ≠ 0
          rw [Ne, IsLocalRing.residue_eq_zero_iff,
            IsLocalization.AtPrime.to_map_mem_maximal_iff 𝒪₁ p]
          exact ha
        exact Q.2.ne_top (Q.asIdeal.eq_top_of_isUnit_mem h hu)
      · intro ha
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          hθ₀]
        have : ιK a = 0 := by
          change residue 𝒪₁ (algebraMap A 𝒪₁ a) = 0
          rw [IsLocalRing.residue_eq_zero_iff,
            IsLocalization.AtPrime.to_map_mem_maximal_iff 𝒪₁ p]
          exact ha
        rw [this, TensorProduct.tmul_zero]
        exact Q.asIdeal.zero_mem
    have hΦB : ∀ Q, (Φ Q).asIdeal.comap rR' = q' := by
      intro Q
      ext r'
      change θ₀ (1 ⊗ₜ r') ∈ Q.asIdeal ↔ r' ∈ q'
      rw [hθ₀, map_one]
      change algebraMap 𝔅 𝕎 (algebraMap R' 𝔅 r') ∈ Q.asIdeal ↔ _
      rw [← Ideal.mem_comap, hallgood Q.asIdeal, hjB, ← Ideal.mem_comap, comap_mk_maximalIdeal,
        IsLocalization.AtPrime.to_map_mem_maximal_iff O₂ q']
    have hΦinj : Function.Injective Φ := fun Q₁ Q₂ h ↦
      PrimeSpectrum.ext (huniq _ _ (congrArg PrimeSpectrum.asIdeal h))
    have htmΦ : ∀ Q : PrimeSpectrum 𝕎,
        lc (Localization.localRingHom _ (Φ Q).asIdeal (algebraMap A 𝕋) rfl) *
          ld (Localization.localRingHom _ (Φ Q).asIdeal rR' rfl) =
        (Module.length 𝔅 (Localization.AtPrime Q.asIdeal)).toNat := by
      intro Q
      obtain ⟨Q', _, hQ', -, h⟩ := hterm (Φ Q) (hΦA Q) (hΦB Q)
      obtain rfl : Q' = Q.asIdeal := huniq _ _ hQ'
      exact h
    refine ⟨Finset.univ.image Φ, ?_, ?_, ?_⟩
    · intro P hP
      obtain ⟨Q, -, rfl⟩ := Finset.mem_image.mp hP
      exact ⟨hΦA Q, hΦB Q⟩
    · intro P hA hB _
      obtain ⟨Q, hQp, hQθ, -, -⟩ := hterm P hA hB
      exact Finset.mem_image.mpr ⟨⟨Q, hQp⟩, Finset.mem_univ _, PrimeSpectrum.ext hQθ⟩
    · rw [Finset.sum_image (fun _ _ _ _ h ↦ hΦinj h)]
      simp_rw [htmΦ]
      rw [← toNat_sum_of_ne_top _ _ (hsum ▸ hW), ← hsum, length_W_eq, ENat.toNat_mul,
        ENat.toNat_coe, hRHS_ld, hRHS_lc]
  · refine ⟨∅, by simp, ?_, ?_⟩
    · intro P hA hB hne
      exfalso
      obtain ⟨Q, hQp, -, hgood, h⟩ := hterm P hA hB
      rw [h] at hne
      have hfin : Module.length 𝔅 (Localization.AtPrime Q) ≠ ⊤ := fun ht ↦ hne (by rw [ht]; rfl)
      haveI := isLocalHom_of_good Q hgood
      have hr := IsLocalRing.length_restrictScalars 𝔅 (Localization.AtPrime Q)
        (Localization.AtPrime Q)
      rw [hr] at hfin
      have hb0 : Module.length (ResidueField 𝔅) (ResidueField (Localization.AtPrime Q)) ≠ 0 :=
        (Module.length_pos).ne'
      have h1 : Module.length (Localization.AtPrime Q) (Localization.AtPrime Q) ≠ ⊤ := by
        intro ht; rw [ht, ENat.top_mul hb0] at hfin; exact hfin rfl
      have h0 : Module.length (Localization.AtPrime Q) (Localization.AtPrime Q) ≠ 0 :=
        (Module.length_pos).ne'
      have h2' : Module.length (ResidueField 𝔅) (ResidueField (Localization.AtPrime Q)) ≠ ⊤ := by
        intro ht; rw [ht, ENat.mul_top h0] at hfin; exact hfin rfl
      have h2 : Module.Finite (ResidueField 𝔅) (ResidueField (Localization.AtPrime Q)) := by
        have := (isFiniteLength_iff_isNoetherian_isArtinian.mp (Module.length_ne_top_iff.mp h2')).1
        exact Module.IsNoetherian.finite _ _
      have halg := isAlgebraic_of_good Q hgood h1 h2
      have hK : Module.Finite 𝕜 𝕂 := finite_of_isAlgebraic_residue q p hp halg
      exact hcase ⟨hK, length_ne_top_of_good Q hgood h1⟩
    · rw [Finset.sum_empty, hRHS_ld, hRHS_lc]
      by_cases hK : Module.Finite 𝕜 𝕂
      · have hB : Module.length 𝔅 𝔅 = ⊤ := by
          by_contra hB; exact hcase ⟨hK, hB⟩
        rw [hB]; simp
      · rw [Module.finrank_of_not_finite hK, zero_mul]


-- @@ L943-943 verbatim
end Core


-- @@ L945-945 verbatim
end FlatProperBaseChangeAlgebra


-- @@ L947-947 verbatim
universe u


-- @@ L949-949 verbatim
namespace AlgebraicGeometry.Chow


-- @@ L951-951 verbatim
open CategoryTheory CategoryTheory.Limits IsLocalRing FlatProperBaseChangeAlgebra


-- @@ L953-953 verbatim
section Transfer


-- @@ L955-955 verbatim
variable {X Y Z : Scheme.{u}}


-- @@ L957-961 verbatim
theorem bc_lc_arrow {R S R' S' : CommRingCat.{u}} [IsLocalRing R] [IsLocalRing R'] (f : R ⟶ S)
    (g : R' ⟶ S') (e : Arrow.mk f ≅ Arrow.mk g) : lc f.hom = lc g.hom :=
  lc_eq_of_equiv _ _ (Arrow.leftFunc.mapIso e).commRingCatIsoToRingEquiv
    (Arrow.rightFunc.mapIso e).commRingCatIsoToRingEquiv (fun r ↦
      (congrArg (fun h ↦ h.hom r) (Arrow.w_mk_right e.hom)).symm)


-- @@ L963-968 verbatim
theorem bc_ld_arrow {R S R' S' : CommRingCat.{u}} [IsLocalRing R] [IsLocalRing R'] [IsLocalRing S]
    [IsLocalRing S'] (f : R ⟶ S) (g : R' ⟶ S') [IsLocalHom f.hom] [IsLocalHom g.hom]
    (e : Arrow.mk f ≅ Arrow.mk g) : ld f.hom = ld g.hom :=
  ld_eq_of_equiv _ _ (Arrow.leftFunc.mapIso e).commRingCatIsoToRingEquiv
    (Arrow.rightFunc.mapIso e).commRingCatIsoToRingEquiv (fun r ↦
      (congrArg (fun h ↦ h.hom r) (Arrow.w_mk_right e.hom)).symm)


-- @@ L970-970 verbatim
theorem bc_coeff_eq_lc (f : X ⟶ Y) (x : X) : flatPullbackCoeff f x = lc (f.stalkMap x).hom := rfl


-- @@ L972-972 verbatim
theorem bc_degree_eq_ld (f : X ⟶ Y) (x : X) : f.degree x = ld (f.stalkMap x).hom := rfl


-- @@ L974-975 verbatim
theorem bc_coeff_congr {f₁ f₂ : X ⟶ Y} (e : f₁ = f₂) (x : X) :
    flatPullbackCoeff f₁ x = flatPullbackCoeff f₂ x := by subst e; rfl


-- @@ L977-978 verbatim
theorem bc_degree_congr {f₁ f₂ : X ⟶ Y} (e : f₁ = f₂) (x : X) : f₁.degree x = f₂.degree x := by
  subst e; rfl


-- @@ L980-983 verbatim
theorem bc_coeff_comp_right (h : Z ⟶ X) (ι : X ⟶ Y) (z : Z) [IsIso (ι.stalkMap (h z))] :
    flatPullbackCoeff (h ≫ ι) z = flatPullbackCoeff h z :=
  lc_eq_of_equiv _ _ (asIso (ι.stalkMap (h z))).commRingCatIsoToRingEquiv (RingEquiv.refl _)
    (fun r ↦ congrArg (fun k ↦ k.hom r) (Scheme.Hom.stalkMap_comp h ι z))


-- @@ L985-988 verbatim
theorem bc_degree_comp_right (h : Z ⟶ X) (ι : X ⟶ Y) (z : Z) [IsIso (ι.stalkMap (h z))] :
    (h ≫ ι).degree z = h.degree z :=
  ld_eq_of_equiv _ _ (asIso (ι.stalkMap (h z))).commRingCatIsoToRingEquiv (RingEquiv.refl _)
    (fun r ↦ congrArg (fun k ↦ k.hom r) (Scheme.Hom.stalkMap_comp h ι z))


-- @@ L990-995 verbatim
theorem bc_coeff_comp_left (φ : Z ⟶ X) (h : X ⟶ Y) (z : Z) [IsIso (φ.stalkMap z)] :
    flatPullbackCoeff (φ ≫ h) z = flatPullbackCoeff h (φ z) :=
  lc_eq_of_equiv _ _ (RingEquiv.refl _) (asIso (φ.stalkMap z)).commRingCatIsoToRingEquiv.symm
    (fun r ↦ by
      rw [congrArg (fun k ↦ k.hom r) (Scheme.Hom.stalkMap_comp φ h z)]
      exact RingEquiv.symm_apply_apply _ _)


-- @@ L997-1002 verbatim
theorem bc_degree_comp_left (φ : Z ⟶ X) (h : X ⟶ Y) (z : Z) [IsIso (φ.stalkMap z)] :
    (φ ≫ h).degree z = h.degree (φ z) :=
  ld_eq_of_equiv _ _ (RingEquiv.refl _) (asIso (φ.stalkMap z)).commRingCatIsoToRingEquiv.symm
    (fun r ↦ by
      rw [congrArg (fun k ↦ k.hom r) (Scheme.Hom.stalkMap_comp φ h z)]
      exact RingEquiv.symm_apply_apply _ _)


-- @@ L1004-1007 verbatim
theorem bc_coeff_Spec {R S : CommRingCat.{u}} (φ : R ⟶ S) (P : Spec S) :
    flatPullbackCoeff (Spec.map φ) P =
      lc (Localization.localRingHom (P.asIdeal.comap φ.hom) P.asIdeal φ.hom rfl) :=
  bc_lc_arrow _ _ (Scheme.arrowStalkMapSpecIso φ P)


-- @@ L1009-1015 verbatim
theorem bc_degree_Spec {R S : CommRingCat.{u}} (φ : R ⟶ S) (P : Spec S) :
    (Spec.map φ).degree P =
      ld (Localization.localRingHom (P.asIdeal.comap φ.hom) P.asIdeal φ.hom rfl) := by
  have h : IsLocalHom (CommRingCat.ofHom (Localization.localRingHom
      (PrimeSpectrum.comap φ.hom P).asIdeal P.asIdeal φ.hom rfl)).hom :=
    inferInstanceAs (IsLocalHom (Localization.localRingHom _ _ _ rfl))
  exact @bc_ld_arrow _ _ _ _ _ _ _ _ _ _ inferInstance h (Scheme.arrowStalkMapSpecIso φ P)


-- @@ L1017-1017 verbatim
end Transfer



-- @@ L1020-1020 verbatim
section Pointwise


-- @@ L1022-1022 verbatim
open TensorProduct


-- @@ L1024-1024 verbatim
variable {X Y X' Y' : Scheme.{u}}


-- @@ L1026-1043 verbatim
/-- The product of the pullback coefficient and the degree at a point of an affine chart of the
fibre product, expressed through the algebraic invariants `lc` and `ld`. -/
theorem bc_htr {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R'] [Algebra R A]
    [Algebra R R'] (g' : X' ⟶ X) (f' : X' ⟶ Y') (ιA : Spec (CommRingCat.of A) ⟶ X)
    (ιB : Spec (CommRingCat.of R') ⟶ Y') [IsOpenImmersion ιA] [IsOpenImmersion ιB]
    (φ : Spec (CommRingCat.of (A ⊗[R] R')) ⟶ X') [IsOpenImmersion φ]
    (hφg' : φ ≫ g' = Spec.map (CommRingCat.ofHom (algebraMap A (A ⊗[R] R'))) ≫ ιA)
    (hφf' : φ ≫ f' = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight.toRingHom : R' →+* A ⊗[R] R')) ≫ ιB)
    (P : Spec (CommRingCat.of (A ⊗[R] R'))) :
    flatPullbackCoeff g' (φ P) * f'.degree (φ P) =
      lc (Localization.localRingHom _ P.asIdeal (algebraMap A (A ⊗[R] R')) rfl) *
      ld (Localization.localRingHom _ P.asIdeal
        (Algebra.TensorProduct.includeRight.toRingHom : R' →+* A ⊗[R] R') rfl) := by
  rw [← bc_coeff_comp_left φ g' P, ← bc_degree_comp_left φ f' P, bc_coeff_congr hφg',
    bc_degree_congr hφf', bc_coeff_comp_right, bc_degree_comp_right, bc_coeff_Spec,
    bc_degree_Spec]
  rfl


-- @@ L1045-1163 verbatim
/-- The pointwise identity behind flat base change (no flatness is needed here). -/
theorem bc_pointwise (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    [LocallyOfFiniteType f] (hsq : IsPullback g' f' f g) (x : X) (y' : Y') (hxy : f x = g y') :
    ∃ s : Finset X', (∀ x' ∈ s, g' x' = x ∧ f' x' = y') ∧
      (∀ x', g' x' = x → f' x' = y' → flatPullbackCoeff g' x' * f'.degree x' ≠ 0 → x' ∈ s) ∧
      ∑ x' ∈ s, flatPullbackCoeff g' x' * f'.degree x' = f.degree x * flatPullbackCoeff g y' := by
  classical
  obtain ⟨V, hV, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (x := f x) (U := ⊤) (by simp)
  obtain ⟨U, hU, hxU, hUV⟩ :=
    exists_isAffineOpen_mem_and_subset (x := x) (U := f ⁻¹ᵁ V) (show f x ∈ V from hyV)
  obtain ⟨U', hU', hyU', hUV'⟩ :=
    exists_isAffineOpen_mem_and_subset (x := y') (U := g ⁻¹ᵁ V) (show g y' ∈ V from hxy ▸ hyV)
  have hle : U ≤ f ⁻¹ᵁ V := fun z hz ↦ hUV hz
  have hle' : U' ≤ g ⁻¹ᵁ V := fun z hz ↦ hUV' hz
  let α := f.appLE V U hle
  let β := g.appLE V U' hle'
  letI : Algebra Γ(Y, V) Γ(X, U) := α.hom.toAlgebra
  letI : Algebra Γ(Y, V) Γ(Y', U') := β.hom.toAlgebra
  haveI : Algebra.FiniteType Γ(Y, V) Γ(X, U) :=
    HasRingHomProperty.appLE @LocallyOfFiniteType f ‹_› ⟨V, hV⟩ ⟨U, hU⟩ hle
  have e₁ : Spec.map α ≫ hV.fromSpec = hU.fromSpec ≫ f := IsAffineOpen.SpecMap_appLE_fromSpec f hV hU hle
  have e₂ : Spec.map β ≫ hV.fromSpec = hU'.fromSpec ≫ g :=
    IsAffineOpen.SpecMap_appLE_fromSpec g hV hU' hle'
  let ψ := pullback.map (Spec.map α) (Spec.map β) f g hU.fromSpec hU'.fromSpec hV.fromSpec e₁ e₂
  let φ : Spec (.of (Γ(X, U) ⊗[Γ(Y, V)] Γ(Y', U'))) ⟶ X' :=
    (pullbackSpecIso Γ(Y, V) Γ(X, U) Γ(Y', U')).inv ≫ ψ ≫ hsq.isoPullback.inv
  haveI : IsOpenImmersion φ := by
    dsimp only [φ]; infer_instance
  have hφg' : φ ≫ g' = Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
      (Γ(X, U) ⊗[Γ(Y, V)] Γ(Y', U')))) ≫ hU.fromSpec := by
    simp only [φ, ψ, Category.assoc, IsPullback.isoPullback_inv_fst, pullback.lift_fst]
    rw [← Category.assoc]
    congr 1
    exact pullbackSpecIso_inv_fst' _ _ _
  have hφf' : φ ≫ f' = Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight.toRingHom :
        Γ(Y', U') →+* Γ(X, U) ⊗[Γ(Y, V)] Γ(Y', U'))) ≫ hU'.fromSpec := by
    simp only [φ, ψ, Category.assoc, IsPullback.isoPullback_inv_snd, pullback.lift_snd]
    rw [← Category.assoc]
    congr 1
    exact pullbackSpecIso_inv_snd _ _ _
  let p := hU.primeIdealOf ⟨x, hxU⟩
  let q' := hU'.primeIdealOf ⟨y', hyU'⟩
  have hp_pt : hU.fromSpec p = x := hU.fromSpec_primeIdealOf _
  have hq_pt : hU'.fromSpec q' = y' := hU'.fromSpec_primeIdealOf _
  have hpq : q'.asIdeal.comap β.hom = p.asIdeal.comap (algebraMap Γ(Y, V) Γ(X, U)) := by
    have h1 := IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hle hxU
    have h2 := IsAffineOpen.comap_primeIdealOf_appLE V hV U' hU' hle' hyU'
    have h3 : hV.primeIdealOf ⟨f x, hle hxU⟩ = hV.primeIdealOf ⟨g y', hle' hyU'⟩ :=
      congrArg hV.primeIdealOf (Subtype.ext hxy)
    exact congrArg PrimeSpectrum.asIdeal (h2.trans (h3.symm.trans h1.symm))
  obtain ⟨s₀, hmem, hcompl, hsum⟩ := FlatProperBaseChangeAlgebra.core (R := Γ(Y, V)) (A := Γ(X, U))
    (R' := Γ(Y', U')) (q'.asIdeal.comap β.hom) p.asIdeal q'.asIdeal hpq
    (O₂ := Localization.AtPrime q'.asIdeal)
    (Localization.localRingHom (q'.asIdeal.comap β.hom) q'.asIdeal β.hom rfl)
    (fun r ↦ Localization.localRingHom_to_map _ _ _ _ r)
  have htr : ∀ P, flatPullbackCoeff g' (φ P) * f'.degree (φ P) =
      lc (Localization.localRingHom _ P.asIdeal
        (algebraMap Γ(X, U) (Γ(X, U) ⊗[Γ(Y, V)] Γ(Y', U'))) rfl) *
      ld (Localization.localRingHom _ P.asIdeal
        (Algebra.TensorProduct.includeRight.toRingHom :
          Γ(Y', U') →+* Γ(X, U) ⊗[Γ(Y, V)] Γ(Y', U')) rfl) :=
    fun P ↦ bc_htr g' f' hU.fromSpec hU'.fromSpec φ hφg' hφf' P
  have hdeg : f.degree x = ld (Localization.localRingHom (q'.asIdeal.comap β.hom) p.asIdeal
      (algebraMap Γ(Y, V) Γ(X, U)) hpq) := by
    rw [← hp_pt, ← bc_degree_comp_left hU.fromSpec f p, ← bc_degree_congr e₁,
      bc_degree_comp_right, bc_degree_Spec]
    exact ld_localRingHom_congr _ _ rfl hpq
  have hcoef : flatPullbackCoeff g y' =
      lc (Localization.localRingHom (q'.asIdeal.comap β.hom) q'.asIdeal β.hom rfl) := by
    rw [← hq_pt, ← bc_coeff_comp_left hU'.fromSpec g q', ← bc_coeff_congr e₂,
      bc_coeff_comp_right, bc_coeff_Spec]
  have hptA : ∀ P : Spec (.of (Γ(X, U) ⊗[Γ(Y, V)] Γ(Y', U'))), g' (φ P) =
      hU.fromSpec (Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U)
        (Γ(X, U) ⊗[Γ(Y, V)] Γ(Y', U')))) P) := fun P ↦ by
    rw [← Scheme.Hom.comp_apply, hφg', Scheme.Hom.comp_apply]
  have hptB : ∀ P : Spec (.of (Γ(X, U) ⊗[Γ(Y, V)] Γ(Y', U'))), f' (φ P) =
      hU'.fromSpec (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight.toRingHom :
          Γ(Y', U') →+* Γ(X, U) ⊗[Γ(Y, V)] Γ(Y', U'))) P) := fun P ↦ by
    rw [← Scheme.Hom.comp_apply, hφf', Scheme.Hom.comp_apply]
  have hinj : Function.Injective φ := φ.isOpenEmbedding.injective
  have hrange : ∀ x', g' x' ∈ Set.range hU.fromSpec → f' x' ∈ Set.range hU'.fromSpec →
      x' ∈ Set.range φ := by
    intro x' h1 h2
    have hz : hsq.isoPullback.hom x' ∈ Set.range ψ := by
      rw [Scheme.Pullback.range_map]
      refine ⟨?_, ?_⟩
      · show pullback.fst f g (hsq.isoPullback.hom x') ∈ Set.range hU.fromSpec
        rw [← Scheme.Hom.comp_apply, hsq.isoPullback_hom_fst]; exact h1
      · show pullback.snd f g (hsq.isoPullback.hom x') ∈ Set.range hU'.fromSpec
        rw [← Scheme.Hom.comp_apply, hsq.isoPullback_hom_snd]; exact h2
    obtain ⟨z, hz⟩ := hz
    refine ⟨(pullbackSpecIso Γ(Y, V) Γ(X, U) Γ(Y', U')).hom z, ?_⟩
    change hsq.isoPullback.inv (ψ ((pullbackSpecIso Γ(Y, V) Γ(X, U) Γ(Y', U')).inv
      ((pullbackSpecIso Γ(Y, V) Γ(X, U) Γ(Y', U')).hom z))) = x'
    rw [Scheme.hom_inv_apply, hz, Scheme.hom_inv_apply]
  refine ⟨s₀.image φ, ?_, ?_, ?_⟩
  · intro x' hx'
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hx'
    obtain ⟨hA, hB⟩ := hmem P hP
    refine ⟨?_, ?_⟩
    · rw [hptA, ← hp_pt]
      congr 1
      exact PrimeSpectrum.ext hA
    · rw [hptB, ← hq_pt]
      congr 1
      exact PrimeSpectrum.ext hB
  · intro x' hgx hfx hne
    obtain ⟨P, rfl⟩ := hrange x' ⟨p, hp_pt.trans hgx.symm⟩ ⟨q', hq_pt.trans hfx.symm⟩
    refine Finset.mem_image.mpr ⟨P, hcompl P ?_ ?_ ?_, rfl⟩
    · have := hU.fromSpec.isOpenEmbedding.injective ((hptA P).symm.trans (hgx.trans hp_pt.symm))
      exact congrArg PrimeSpectrum.asIdeal this
    · have := hU'.fromSpec.isOpenEmbedding.injective ((hptB P).symm.trans (hfx.trans hq_pt.symm))
      exact congrArg PrimeSpectrum.asIdeal this
    · rw [← htr]; exact hne
  · rw [Finset.sum_image (fun a _ b _ h ↦ hinj h), Finset.sum_congr rfl (fun P _ ↦ htr P),
      hdeg, hcoef]
    exact hsum


-- @@ L1165-1165 verbatim
end Pointwise



-- @@ L1168-1168 verbatim
section Global


-- @@ L1170-1170 verbatim
variable {X Y X' Y' : Scheme.{u}}


-- @@ L1172-1188 verbatim
open scoped Classical in
theorem bc_properPushforward_apply_eq_sum (f : X ⟶ Y) [QuasiCompact f] (D : AlgebraicCycle X ℤ)
    (y : Y) (T : Finset X) (hT : ∀ x, f x = y → D x * (f.degree x : ℤ) ≠ 0 → x ∈ T) :
    properPushforward f D y = ∑ x ∈ T with f x = y, D x * (f.degree x : ℤ) := by
  classical
  set T' := T ∪ (f.preimageSupportFinite D y).toFinset
  rw [properPushforward_apply_eq_sum_of_subset f D y T' (fun x hx hD ↦ Finset.mem_union_right _
    ((mem_preimageSupportFinite_toFinset_iff f D y x).mpr ⟨hx, hD⟩))]
  symm
  apply Finset.sum_subset
  · intro x hx
    simp only [Finset.mem_filter] at hx ⊢
    exact ⟨Finset.mem_union_left _ hx.1, hx.2⟩
  · intro x hx hx'
    simp only [Finset.mem_filter] at hx hx'
    by_contra h
    exact hx' ⟨hT x hx.2 h, hx.2⟩


-- @@ L1190-1247 verbatim
open scoped Classical in
/-- LEAF BC (Fulton Prop. 1.7): flat base change `g^* f_* = f'_* g'^*` for a cartesian square
with `f` proper and `g` flat. -/
theorem flatPullback_properPushforward (f : X ⟶ Y) (g : Y' ⟶ Y)
    (f' : X' ⟶ Y') (g' : X' ⟶ X) [IsProper f] [Flat g] [IsLocallyNoetherian X']
    [IsLocallyNoetherian Y'] [QuasiCompact f']
    (hsq : IsPullback g' f' f g) (D : AlgebraicCycle X ℤ) :
    flatPullback g (properPushforward f D) = properPushforward f' (flatPullback g' D) := by
  classical
  ext y'
  rw [flatPullback_apply, properPushforward_apply]
  set S := (f.preimageSupportFinite D (g y')).toFinset
  have hS : ∀ x ∈ S, f x = g y' := fun x hx ↦
    ((mem_preimageSupportFinite_toFinset_iff f D _ x).mp hx).1
  let sx : X → Finset X' := fun x ↦
    if h : f x = g y' then Classical.choose (bc_pointwise f g f' g' hsq x y' h) else ∅
  have hsx : ∀ x, f x = g y' →
      (∀ x' ∈ sx x, g' x' = x ∧ f' x' = y') ∧
      (∀ x', g' x' = x → f' x' = y' → flatPullbackCoeff g' x' * f'.degree x' ≠ 0 → x' ∈ sx x) ∧
      ∑ x' ∈ sx x, flatPullbackCoeff g' x' * f'.degree x' =
        f.degree x * flatPullbackCoeff g y' := by
    intro x h
    simp only [sx, dif_pos h]
    exact Classical.choose_spec (bc_pointwise f g f' g' hsq x y' h)
  have hw : ∀ x', f (g' x') = g (f' x') := fun x' ↦ by
    rw [← Scheme.Hom.comp_apply, hsq.w, Scheme.Hom.comp_apply]
  rw [bc_properPushforward_apply_eq_sum f' _ y' (S.biUnion sx) (by
    intro x' hx' hne
    rw [flatPullback_apply] at hne
    have hD : D (g' x') ≠ 0 := by intro h; apply hne; simp [h]
    have hc : flatPullbackCoeff g' x' * f'.degree x' ≠ 0 := by
      intro h; apply hne
      rw [mul_assoc, ← Nat.cast_mul, h, Nat.cast_zero, mul_zero]
    have hfx : f (g' x') = g y' := (hw x').trans (congrArg g hx')
    exact Finset.mem_biUnion.mpr ⟨g' x', (mem_preimageSupportFinite_toFinset_iff f D _ _).mpr
      ⟨hfx, hD⟩, (hsx _ hfx).2.1 x' rfl hx' hc⟩)]
  have hfilter : (S.biUnion sx).filter (fun x' ↦ f' x' = y') = S.biUnion sx := by
    apply Finset.filter_true_of_mem
    intro x' hx'
    obtain ⟨x, hx, hx'⟩ := Finset.mem_biUnion.mp hx'
    exact ((hsx x (hS x hx)).1 x' hx').2
  rw [hfilter, Finset.sum_biUnion]
  · rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun x hx ↦ ?_)
    obtain ⟨h1, -, h3⟩ := hsx x (hS x hx)
    have : ∀ x' ∈ sx x, flatPullback g' D x' * (f'.degree x' : ℤ) =
        D x * ((flatPullbackCoeff g' x' * f'.degree x' : ℕ) : ℤ) := by
      intro x' hx'
      rw [flatPullback_apply, (h1 x' hx').1]
      push_cast
      ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, ← Nat.cast_sum, h3]
    push_cast
    ring
  · intro x₁ hx₁ x₂ hx₂ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro x' h₁ h₂
    exact hne (((hsx x₁ (hS x₁ hx₁)).1 x' h₁).1.symm.trans ((hsx x₂ (hS x₂ hx₂)).1 x' h₂).1)


-- @@ L1249-1249 verbatim
end Global



-- @@ L1252-1252 verbatim
end AlgebraicGeometry.Chow
