/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.Composition
import AclGeom.Correspondence.LocusDimension
import AclGeom.Correspondence.TupleComposition


-- @@ L10-31 verbatim
/-!
# Scalar correspondence composition and incidence components

The scalar finite-correspondence germs of `Composition` are presented by pairs of single
coordinates `(x, y)`, with ideals in `k[X₀, X₁]`. Viewing each coordinate as a tuple indexed by
`Fin 1`, a scalar presentation is a tuple presentation and conversely: the transcendence of the
source coordinate is the rank-one clause of the tuple presentation, by
`exists_locusCoordinateRing_dimension`. The two ideals correspond under the renaming
`![Sum.inl 0, Sum.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1`.

In an algebraically closed ambient field, over an arbitrary base,
`FiniteCorrespondenceGerm.composes_ofPair_carriers_eq` identifies the ideals of the scalar
composites of the germs of `(x, y)` and `(y, z)` with the contractions to the endpoint variables of
the vanishing ideals of the irreducible components of the incidence spectrum of the three
coordinates with dense image in the locus of `y`. Every such component yields a scalar composite.
The proof transports `TupleCorrespondenceGerm.composes_ofPair_carriers_eq`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved (#5, C2 support).
-/


-- @@ L33-33 verbatim
open MvPolynomial


-- @@ L35-35 verbatim
namespace AclGeom


-- @@ L37-37 verbatim
noncomputable section


-- @@ L39-39 verbatim
variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]


-- @@ L41-41 verbatim
namespace FiniteCorrespondencePair


-- @@ L43-67 verbatim
/-- A scalar presentation, viewed as a presentation by tuples indexed by `Fin 1`. -/
private def toTuple (P : FiniteCorrespondencePair k Ω) : TupleCorrespondencePair k Ω (Fin 1) (Fin 1)
    where
  source := Function.const (Fin 1) P.source
  target := Function.const (Fin 1) P.target
  source_rank := by
    -- A transcendental coordinate generates a field of transcendence degree one.
    have hind : AlgebraicIndependent k (Function.const (Fin 1) P.source) :=
      algebraicIndependent_unique_type_iff.2 fun halg ↦
        P.source_generic (mem_racl_empty_of_isAlgebraic halg)
    obtain ⟨n, hdim, htr⟩ := exists_locusCoordinateRing_dimension (k := k)
      (Function.const (Fin 1) P.source)
    rw [(idealOf_eq_bot_iff k).2 hind] at hdim
    have h1 : ringKrullDim (MvPolynomial (Fin 1) k) = ((1 : ℕ) : WithBot ℕ∞) := by
      simp only [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
        ringKrullDim_eq_zero_of_field, Nat.card_fin, zero_add]
    have hn : n = 1 := Nat.cast_inj.1
      (hdim.symm.trans ((ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot _)).trans h1))
    rw [htr, hn, Nat.cast_one]
  target_mem_source _ := by
    rw [show Set.range (Function.const (Fin 1) P.source) = {P.source} from Set.range_const]
    exact P.target_mem_source
  source_mem_target _ := by
    rw [show Set.range (Function.const (Fin 1) P.target) = {P.target} from Set.range_const]
    exact P.source_mem_target


-- @@ L69-89 verbatim
/-- A presentation by tuples indexed by `Fin 1`, viewed as a scalar presentation. -/
private def ofTuple (R : TupleCorrespondencePair k Ω (Fin 1) (Fin 1)) :
    FiniteCorrespondencePair k Ω where
  source := R.source 0
  target := R.target 0
  source_generic := by
    -- A coordinate generating a field of transcendence degree one is transcendental.
    intro hx
    have : Algebra.IsAlgebraic k (IntermediateField.adjoin k (Set.range R.source)) := by
      rw [Set.range_unique]
      exact IntermediateField.isAlgebraic_adjoin_simple
        (isAlgebraic_of_mem_racl_empty hx).isIntegral
    have h0 := R.source_rank
    rw [trdeg_eq_zero] at h0
    exact zero_ne_one h0
  target_mem_source := by
    have := R.target_mem_source 0
    rwa [Set.range_unique] at this
  source_mem_target := by
    have := R.source_mem_target 0
    rwa [Set.range_unique] at this


-- @@ L91-91 verbatim
end FiniteCorrespondencePair


-- @@ L93-93 verbatim
namespace FiniteCorrespondenceGerm


-- @@ L95-95 verbatim
open FiniteCorrespondencePair


-- @@ L97-97 verbatim
variable (P Q : FiniteCorrespondencePair k Ω)


-- @@ L99-107 verbatim
local notation "ℐ" => Ideal.map (rename (Sum.inl : Fin 1 ⊕ Fin 1 → (Fin 1 ⊕ Fin 1) ⊕ Fin 1) :
    MvPolynomial (Fin 1 ⊕ Fin 1) k →ₐ[k] MvPolynomial ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) k)
      (idealOf k (Sum.elim (Function.const (Fin 1) (FiniteCorrespondencePair.source P))
        (Function.const (Fin 1) (FiniteCorrespondencePair.target P)))) ⊔
  Ideal.map (rename (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr :
      Fin 1 ⊕ Fin 1 → (Fin 1 ⊕ Fin 1) ⊕ Fin 1) :
    MvPolynomial (Fin 1 ⊕ Fin 1) k →ₐ[k] MvPolynomial ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) k)
      (idealOf k (Sum.elim (Function.const (Fin 1) (FiniteCorrespondencePair.target P))
        (Function.const (Fin 1) (FiniteCorrespondencePair.target Q))))


-- @@ L109-167 verbatim
/-- **Scalar composites are endpoint images of incidence components.** Let `(x, y)` and `(y, z)`
present scalar finite-correspondence germs with literally shared middle coordinate `y`, in an
algebraically closed ambient field. The ideals of the scalar composites of the two germs are
exactly the renamings to `k[X₀, X₁]` of the contractions to the endpoint variables of the vanishing
ideals of the irreducible components of the incidence spectrum
`Spec (k[X, Y, Z] ⧸ (I(x, y) + I(y, z)))` with dense image in `Spec (k[Y] ⧸ I(y))`. In particular
every such component yields a scalar composite. -/
theorem composes_ofPair_carriers_eq [IsAlgClosed Ω] (h : P.target = Q.source) :
    {I | ∃ E : FiniteCorrespondenceGerm k Ω, Composes (ofPair P) (ofPair Q) E ∧ E.carrier = I} =
      {I | ∃ Z ∈ irreducibleComponents
          (PrimeSpectrum (MvPolynomial ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) k ⧸ ℐ)),
        closure (PrimeSpectrum.comap (Ideal.quotientMapₐ ℐ (rename (Sum.inl ∘ Sum.inr))
          (idealOf_le_comap_rename_comp
            (a := Sum.elim (Function.const (Fin 1) P.source) (Function.const (Fin 1) P.target))
            (b := Function.const (Fin 1) P.target) (g := Sum.inr) (e := Sum.inl) rfl
            le_sup_left)).toRingHom '' Z) = Set.univ ∧
        I = (((PrimeSpectrum.vanishingIdeal Z).comap (Ideal.Quotient.mk ℐ)).comap
          (rename (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr : Fin 1 ⊕ Fin 1 → (Fin 1 ⊕ Fin 1) ⊕ Fin 1) :
            MvPolynomial (Fin 1 ⊕ Fin 1) k →ₐ[k] _)).comap
          (rename (![Sum.inl 0, Sum.inr 0] : Fin 2 → Fin 1 ⊕ Fin 1) :
            MvPolynomial (Fin 2) k →ₐ[k] _)} := by
  -- The scalar and `Fin 1`-tuple ideals of a pair correspond under the two renamings.
  let e : Fin 2 → Fin 1 ⊕ Fin 1 := ![Sum.inl 0, Sum.inr 0]
  let e' : Fin 1 ⊕ Fin 1 → Fin 2 := Sum.elim (fun _ ↦ 0) (fun _ ↦ 1)
  have hre (a b : Fin 1 → Ω) :
      idealOf k ![a 0, b 0] = (idealOf k (Sum.elim a b)).comap (rename (R := k) e) :=
    idealOf_eq_comap_rename (funext fun i ↦ by fin_cases i <;> rfl)
  have hre' (a b : Fin 1 → Ω) :
      idealOf k (Sum.elim a b) = (idealOf k ![a 0, b 0]).comap (rename (R := k) e') :=
    idealOf_eq_comap_rename (funext fun i ↦ by rcases i with i | i <;> fin_cases i <;> rfl)
  have ht := TupleCorrespondenceGerm.composes_ofPair_carriers_eq (toTuple P) (toTuple Q)
    (congrArg (Function.const (Fin 1)) h)
  ext I
  constructor
  · rintro ⟨E, ⟨P₁, Q₁, h₁, hP, hQ, hE⟩, rfl⟩
    have htP : (toTuple P).ideal = (toTuple P₁).ideal :=
      (hre' (Function.const (Fin 1) P.source) (Function.const (Fin 1) P.target)).trans
        ((congrArg (Ideal.comap (rename (R := k) e')) hP).trans
          (hre' (Function.const (Fin 1) P₁.source) (Function.const (Fin 1) P₁.target)).symm)
    have htQ : (toTuple Q).ideal = (toTuple Q₁).ideal :=
      (hre' (Function.const (Fin 1) Q.source) (Function.const (Fin 1) Q.target)).trans
        ((congrArg (Ideal.comap (rename (R := k) e')) hQ).trans
          (hre' (Function.const (Fin 1) Q₁.source) (Function.const (Fin 1) Q₁.target)).symm)
    obtain ⟨Z, hZ, hdense, hJ⟩ := (Set.ext_iff.1 ht _).1
      ⟨TupleCorrespondenceGerm.ofPair ((toTuple P₁).comp (toTuple Q₁)
        (congrArg (Function.const (Fin 1)) h₁)),
        ⟨toTuple P₁, toTuple Q₁, congrArg (Function.const (Fin 1)) h₁, htP, htQ, rfl⟩, rfl⟩
    exact ⟨Z, hZ, hdense, hE.trans ((hre (Function.const (Fin 1) P₁.source)
      (Function.const (Fin 1) Q₁.target)).trans (congrArg (Ideal.comap (rename (R := k) e)) hJ))⟩
  · rintro ⟨Z, hZ, hdense, rfl⟩
    obtain ⟨E, ⟨P₁, Q₁, h₁, hP, hQ, hE⟩, hEZ⟩ := (Set.ext_iff.1 ht _).2 ⟨Z, hZ, hdense, rfl⟩
    refine ⟨ofPair ((ofTuple P₁).comp (ofTuple Q₁) (congrFun h₁ 0)),
      ⟨ofTuple P₁, ofTuple Q₁, congrFun h₁ 0, ?_, ?_, rfl⟩, ?_⟩
    · exact (hre (Function.const (Fin 1) P.source) (Function.const (Fin 1) P.target)).trans
        ((congrArg (Ideal.comap (rename (R := k) e)) hP).trans (hre P₁.source P₁.target).symm)
    · exact (hre (Function.const (Fin 1) Q.source) (Function.const (Fin 1) Q.target)).trans
        ((congrArg (Ideal.comap (rename (R := k) e)) hQ).trans (hre Q₁.source Q₁.target).symm)
    · exact (hre P₁.source Q₁.target).trans
        (congrArg (Ideal.comap (rename (R := k) e)) (hE.symm.trans hEZ))


-- @@ L169-169 verbatim
end FiniteCorrespondenceGerm


-- @@ L171-171 verbatim
end


-- @@ L173-173 verbatim
end AclGeom
