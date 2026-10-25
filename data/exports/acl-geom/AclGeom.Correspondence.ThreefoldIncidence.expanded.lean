/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.TupleComposition
import AclGeom.Correspondence.LocusIncomparability
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed


-- @@ L12-39 verbatim
/-!
# Threefold composites of tuple correspondences and incidence components

For tuples `x`, `y`, `z`, `w` in an algebraically closed field `Ω` over `k`, the threefold
incidence ring is `k[X, Y, Z, W] ⧸ (I(x, y) + I(y, z) + I(z, w))`, the coordinate ring of the fiber
product of the loci of `(x, y)`, `(y, z)` and `(z, w)` over the loci of `y` and `z`. When each
coordinate of `x` is algebraic over `k(y)` and each coordinate of `w` is algebraic over `k(z)`, its
irreducible components with dense image in the locus of `(y, z)` are exactly the loci of the joint
tuples `(x', y, z, w')` for which `(x', y)` has the locus of `(x, y)` and `(z, w')` has the locus of
`(z, w)`. The proof realizes every relevant prime as such a locus, using an embedding of an
algebraic extension into `Ω`, and compares primes by algebraic incomparability
(`idealOf_eq_of_le_of_comap_eq`).

`TupleCorrespondenceGerm.composes_threefold_components_eq` combines this with
`TupleCorrespondenceGerm.composes_threefold_carriers_eq`: for finite index types, the final germs of
either parenthesization of a threefold composite are exactly the contractions to the endpoint
variables of the vanishing ideals of these components. It also shows that the normalization of
each component, the integral closure of its coordinate domain in its fraction field, is integrally
closed with the same fraction field and the same endpoint generic ideal. This is the source's
associativity of composition through the components of the normalization of the threefold fiber
product (blueprint §8.1), with the normalization formed componentwise. A component's joint field
can be larger than the field of its endpoint image.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved (#5, C2 support).
-/


-- @@ L41-41 verbatim
open MvPolynomial

-- @@ L42-42 verbatim
open scoped IntermediateField.algebraAdjoinAdjoin


-- @@ L44-44 verbatim
namespace AclGeom


-- @@ L46-46 verbatim
variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]


-- @@ L48-51 verbatim
/-- The generated ring as an image of polynomials. -/
private theorem coe_locusCoordinateRingEquiv_mk {κ : Type*} (m : κ → Ω) (c : MvPolynomial κ k) :
    ((locusCoordinateRingEquiv (k := k) m (Ideal.Quotient.mk _ c) : Ω)) = aeval m c := by
  rw [locusCoordinateRingEquiv_mk]


-- @@ L53-150 verbatim
/-- A prime whose contraction to the variables of `m` is the locus of `m`, and whose generators
satisfy polynomial relations over those variables with a coefficient outside that locus, is the
locus of a tuple extending `m`. -/
private theorem exists_idealOf_eq {ι κ : Type*} [IsAlgClosed Ω] (g : κ → ι) (m : κ → Ω)
    (q : Ideal (MvPolynomial ι k)) [q.IsPrime]
    (hcomap : q.comap (rename g : MvPolynomial κ k →ₐ[k] MvPolynomial ι k) = idealOf k m)
    (halg : ∀ i, ∃ p : Polynomial (MvPolynomial κ k), (∃ j, p.coeff j ∉ idealOf k m) ∧
      p.eval₂ (rename g : MvPolynomial κ k →ₐ[k] MvPolynomial ι k).toRingHom (X i) ∈ q) :
    ∃ T : ι → Ω, T ∘ g = m ∧ idealOf k T = q := by
  let φ : MvPolynomial κ k ⧸ idealOf k m →+* MvPolynomial ι k ⧸ q :=
    Ideal.quotientMap q (rename g : MvPolynomial κ k →ₐ[k] MvPolynomial ι k).toRingHom hcomap.ge
  have hφ : Function.Injective φ := Ideal.quotientMap_injective' hcomap.le
  let ψ : MvPolynomial κ k ⧸ idealOf k m →+* Ω :=
    (Algebra.adjoin k (Set.range m)).val.toRingHom.comp
      (locusCoordinateRingEquiv (k := k) m).toRingEquiv.toRingHom
  have hψ : Function.Injective ψ :=
    Subtype.val_injective.comp (locusCoordinateRingEquiv (k := k) m).injective
  have hψmk (c : MvPolynomial κ k) : ψ (Ideal.Quotient.mk _ c) = aeval m c :=
    coe_locusCoordinateRingEquiv_mk m c
  let _ : Algebra (MvPolynomial κ k ⧸ idealOf k m) (MvPolynomial ι k ⧸ q) := φ.toAlgebra
  let _ : Algebra (MvPolynomial κ k ⧸ idealOf k m) Ω := ψ.toAlgebra
  have : FaithfulSMul (MvPolynomial κ k ⧸ idealOf k m) (MvPolynomial ι k ⧸ q) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : FaithfulSMul (MvPolynomial κ k ⧸ idealOf k m) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 hψ
  -- The generators are algebraic over the middle quotient.
  have hgen (i : ι) : IsAlgebraic (MvPolynomial κ k ⧸ idealOf k m)
      (Ideal.Quotient.mk q (X i)) := by
    obtain ⟨p, ⟨j, hj⟩, hp⟩ := halg i
    refine ⟨p.map (Ideal.Quotient.mk (idealOf k m)), fun h ↦ hj ?_, ?_⟩
    · exact Ideal.Quotient.eq_zero_iff_mem.1
        (by rw [← Polynomial.coeff_map, h, Polynomial.coeff_zero])
    · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
      have hφmk : φ.comp (Ideal.Quotient.mk (idealOf k m)) = (Ideal.Quotient.mk q).comp
          (rename g : MvPolynomial κ k →ₐ[k] MvPolynomial ι k).toRingHom :=
        Ideal.quotientMap_comp_mk hcomap.ge
      change Polynomial.eval₂ (φ.comp (Ideal.Quotient.mk (idealOf k m))) _ p = 0
      rw [hφmk, ← Polynomial.hom_eval₂]
      exact Ideal.Quotient.eq_zero_iff_mem.2 hp
  have hmem (f : MvPolynomial ι k) : Ideal.Quotient.mk q f ∈ Algebra.adjoin
      (MvPolynomial κ k ⧸ idealOf k m) (Set.range fun i ↦ Ideal.Quotient.mk q (X i)) := by
    induction f using MvPolynomial.induction_on with
    | C c =>
      have : Ideal.Quotient.mk q (C c) =
          algebraMap (MvPolynomial κ k ⧸ idealOf k m) _ (Ideal.Quotient.mk _ (C c)) := by
        change _ = Ideal.Quotient.mk q (rename g (C c))
        rw [rename_C]
      rw [this]
      exact Subalgebra.algebraMap_mem _ _
    | add f₁ f₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul_X f i h =>
      rw [map_mul]
      exact mul_mem h (Algebra.subset_adjoin (Set.mem_range_self i))
  have hadj : (Algebra.adjoin (MvPolynomial κ k ⧸ idealOf k m)
      (Set.range fun i ↦ Ideal.Quotient.mk q (X i))).IsAlgebraic := by
    refine Algebra.isAlgebraic_adjoin_iff.2 ?_
    rintro _ ⟨i, rfl⟩
    exact hgen i
  have : Algebra.IsAlgebraic (MvPolynomial κ k ⧸ idealOf k m) (MvPolynomial ι k ⧸ q) := by
    refine ⟨fun a ↦ ?_⟩
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact hadj _ (hmem f)
  let L : MvPolynomial ι k ⧸ q →ₐ[MvPolynomial κ k ⧸ idealOf k m] Ω := IsAlgClosed.lift
  -- The lift is injective: its kernel meets the middle quotient trivially.
  have hL : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun a ha ↦ ?_
    by_contra ha0
    refine Ideal.under_ne_bot_of_algebraic_mem (R := MvPolynomial κ k ⧸ idealOf k m)
      (I := RingHom.ker L) ha0 ha
      (Algebra.IsAlgebraic.isAlgebraic a) (eq_bot_iff.2 fun b hb ↦ ?_)
    rw [Ideal.mem_bot]
    refine hψ ?_
    rw [map_zero]
    change algebraMap _ Ω b = 0
    rw [← L.commutes]
    exact hb
  refine ⟨fun i ↦ L (Ideal.Quotient.mk q (X i)), funext fun c ↦ ?_, ?_⟩
  · change L (Ideal.Quotient.mk q (X (g c))) = m c
    have : Ideal.Quotient.mk q (X (g c)) =
        algebraMap (MvPolynomial κ k ⧸ idealOf k m) _ (Ideal.Quotient.mk _ (X c)) := by
      change _ = Ideal.Quotient.mk q (rename g (X c))
      rw [rename_X]
    rw [this, L.commutes]
    exact (hψmk (X c)).trans (aeval_X m c)
  · have hev : (aeval fun i ↦ L (Ideal.Quotient.mk q (X i)) :
        MvPolynomial ι k →ₐ[k] Ω).toRingHom = L.toRingHom.comp (Ideal.Quotient.mk q) := by
      refine MvPolynomial.ringHom_ext (fun c ↦ ?_) (fun i ↦ ?_)
      · change aeval _ (C c) = L (Ideal.Quotient.mk q (C c))
        have : Ideal.Quotient.mk q (C c) =
            algebraMap (MvPolynomial κ k ⧸ idealOf k m) _ (Ideal.Quotient.mk _ (C c)) := by
          change _ = Ideal.Quotient.mk q (rename g (C c))
          rw [rename_C]
        rw [aeval_C, this, L.commutes]
        exact ((hψmk (C c)).trans (aeval_C m c)).symm
      · exact aeval_X _ i
    change RingHom.ker _ = q
    rw [hev, ← RingHom.comap_ker, (RingHom.injective_iff_ker_eq_bot L.toRingHom).1 hL,
      ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]


-- @@ L152-177 verbatim
/-- A coordinate satisfying a polynomial relation over a subtuple's variables, with a coefficient
outside the subtuple's locus, is algebraic over the field generated by the subtuple. -/
private theorem mem_racl_of_relation {ι κ : Type*} (T : ι → Ω) (g : κ → ι) {i : ι}
    {p : Polynomial (MvPolynomial κ k)} (hj : ∃ j, p.coeff j ∉ idealOf k (T ∘ g))
    (hp : p.eval₂ (rename g : MvPolynomial κ k →ₐ[k] MvPolynomial ι k).toRingHom (X i) ∈
      idealOf k T) :
    T i ∈ racl k (Set.range (T ∘ g)) := by
  obtain ⟨j, hj⟩ := hj
  let ψ : MvPolynomial κ k →+* Algebra.adjoin k (Set.range (T ∘ g)) :=
    (locusCoordinateRingEquiv (k := k) (T ∘ g)).toRingEquiv.toRingHom.comp
      (Ideal.Quotient.mk (idealOf k (T ∘ g)))
  have hcomp : (aeval T).toRingHom.comp
      (rename g : MvPolynomial κ k →ₐ[k] MvPolynomial ι k).toRingHom =
      (algebraMap (Algebra.adjoin k (Set.range (T ∘ g))) Ω).comp ψ :=
    RingHom.ext fun c ↦ (aeval_rename g T c).trans
      (coe_locusCoordinateRingEquiv_mk (T ∘ g) c).symm
  refine (mem_racl_iff k).2 ((IsFractionRing.isAlgebraic_iff
    (Algebra.adjoin k (Set.range (T ∘ g))) (IntermediateField.adjoin k (Set.range (T ∘ g))) Ω).1
      ⟨p.map ψ, fun h ↦ hj ?_, ?_⟩)
  · have h0 := congrArg (fun r : Polynomial (Algebra.adjoin k (Set.range (T ∘ g))) ↦ r.coeff j) h
    simp only [Polynomial.coeff_map, Polynomial.coeff_zero] at h0
    exact (mem_idealOf_iff k).2 ((coe_locusCoordinateRingEquiv_mk (T ∘ g) _).symm.trans
      (congrArg Subtype.val h0))
  · rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hcomp,
      show T i = (aeval (R := k) T).toRingHom (X i) from (aeval_X T i).symm, ← Polynomial.hom_eval₂]
    exact (mem_idealOf_iff k).1 hp


-- @@ L179-179 verbatim
section Chain


-- @@ L181-181 verbatim
variable {α β γ δ : Type*} (x : α → Ω) (y : β → Ω) (z : γ → Ω) (w : δ → Ω)


-- @@ L183-184 verbatim
local notation "𝔢" => (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inr) (Sum.inl ∘ Sum.inr) :
  β ⊕ γ → ((α ⊕ β) ⊕ γ) ⊕ δ)


-- @@ L186-194 verbatim
local notation "ℐ₄" =>
  Ideal.map (rename (Sum.inl ∘ Sum.inl : α ⊕ β → ((α ⊕ β) ⊕ γ) ⊕ δ) :
      MvPolynomial (α ⊕ β) k →ₐ[k] MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k)
    (idealOf k (Sum.elim x y)) ⊔
  Ideal.map (rename 𝔢 : MvPolynomial (β ⊕ γ) k →ₐ[k] MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k)
    (idealOf k (Sum.elim y z)) ⊔
  Ideal.map (rename (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr : γ ⊕ δ → ((α ⊕ β) ⊕ γ) ⊕ δ) :
      MvPolynomial (γ ⊕ δ) k →ₐ[k] MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k)
    (idealOf k (Sum.elim z w))


-- @@ L196-198 verbatim
local notation "π₄" => Ideal.quotientMapₐ ℐ₄
  (rename 𝔢 : MvPolynomial (β ⊕ γ) k →ₐ[k] MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k)
  (Iff.mp Ideal.map_le_iff_le_comap (le_trans le_sup_right le_sup_left))


-- @@ L200-266 verbatim
/-- Every generator of the threefold incidence ring satisfies a relation over the middle variables
with a coefficient outside the middle locus. -/
private theorem chain_relations (hxy : ∀ i, x i ∈ racl k (Set.range y))
    (hwz : ∀ l, w l ∈ racl k (Set.range z)) (i : ((α ⊕ β) ⊕ γ) ⊕ δ) :
    ∃ p : Polynomial (MvPolynomial (β ⊕ γ) k), (∃ j, p.coeff j ∉ idealOf k (Sum.elim y z)) ∧
      p.eval₂ (rename 𝔢 : MvPolynomial (β ⊕ γ) k →ₐ[k] _).toRingHom (X i) ∈ ℐ₄ := by
  have hone : (1 : MvPolynomial (β ⊕ γ) k) ∉ idealOf k (Sum.elim y z) := fun h ↦
    one_ne_zero ((map_one (aeval (R := k) (Sum.elim y z))).symm.trans ((mem_idealOf_iff k).1 h))
  rcases i with ((a | b) | c) | d
  · obtain ⟨p, ⟨j, hj⟩, hp⟩ := exists_poly_of_mem_racl (Sum.elim x y) Sum.inr
      (X (Sum.inl a) : MvPolynomial (α ⊕ β) k) (by rw [aeval_X]; exact hxy a)
    refine ⟨p.map (rename (Sum.inl : β → β ⊕ γ) : MvPolynomial β k →ₐ[k] _).toRingHom,
      ⟨j, fun h ↦ hj ?_⟩, ?_⟩
    · rw [Polynomial.coeff_map, mem_idealOf_iff] at h
      rw [mem_idealOf_iff]
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_rename] at h
      exact h
    · have hc : (rename 𝔢 : MvPolynomial (β ⊕ γ) k →ₐ[k] _).toRingHom.comp
          (rename (Sum.inl : β → β ⊕ γ) : MvPolynomial β k →ₐ[k] _).toRingHom =
          (rename (Sum.inl ∘ Sum.inl : α ⊕ β → ((α ⊕ β) ⊕ γ) ⊕ δ) :
            MvPolynomial (α ⊕ β) k →ₐ[k] _).toRingHom.comp
          (rename (Sum.inr : β → α ⊕ β) : MvPolynomial β k →ₐ[k] _).toRingHom :=
        RingHom.ext fun c ↦ (rename_rename _ _ c).trans
          (rename_rename (Sum.inr : β → α ⊕ β) (Sum.inl ∘ Sum.inl) c).symm
      rw [Polynomial.eval₂_map, hc, show (X (Sum.inl (Sum.inl (Sum.inl a))) :
        MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k) = (rename (Sum.inl ∘ Sum.inl :
          α ⊕ β → ((α ⊕ β) ⊕ γ) ⊕ δ) : MvPolynomial (α ⊕ β) k →ₐ[k] _).toRingHom
            (X (Sum.inl a)) from (rename_X (R := k) (Sum.inl ∘ Sum.inl :
              α ⊕ β → ((α ⊕ β) ⊕ γ) ⊕ δ) (Sum.inl a)).symm, ← Polynomial.hom_eval₂]
      exact Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp))
  · refine ⟨Polynomial.X - Polynomial.C (X (Sum.inl b)), ⟨1, ?_⟩, ?_⟩
    · rw [Polynomial.coeff_sub, Polynomial.coeff_X_one, Polynomial.coeff_C_of_ne_zero one_ne_zero,
        sub_zero]
      exact hone
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
      change X _ - rename _ (X (Sum.inl b)) ∈ _
      rw [rename_X, Sum.elim_inl, Function.comp_apply, Function.comp_apply, sub_self]
      exact zero_mem _
  · refine ⟨Polynomial.X - Polynomial.C (X (Sum.inr c)), ⟨1, ?_⟩, ?_⟩
    · rw [Polynomial.coeff_sub, Polynomial.coeff_X_one, Polynomial.coeff_C_of_ne_zero one_ne_zero,
        sub_zero]
      exact hone
    · rw [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
      change X _ - rename _ (X (Sum.inr c)) ∈ _
      rw [rename_X, Sum.elim_inr, Function.comp_apply, sub_self]
      exact zero_mem _
  · obtain ⟨p, ⟨j, hj⟩, hp⟩ := exists_poly_of_mem_racl (Sum.elim z w) Sum.inl
      (X (Sum.inr d) : MvPolynomial (γ ⊕ δ) k) (by rw [aeval_X]; exact hwz d)
    refine ⟨p.map (rename (Sum.inr : γ → β ⊕ γ) : MvPolynomial γ k →ₐ[k] _).toRingHom,
      ⟨j, fun h ↦ hj ?_⟩, ?_⟩
    · rw [Polynomial.coeff_map, mem_idealOf_iff] at h
      rw [mem_idealOf_iff]
      rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_rename] at h
      exact h
    · have hc : (rename 𝔢 : MvPolynomial (β ⊕ γ) k →ₐ[k] _).toRingHom.comp
          (rename (Sum.inr : γ → β ⊕ γ) : MvPolynomial γ k →ₐ[k] _).toRingHom =
          (rename (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr : γ ⊕ δ → ((α ⊕ β) ⊕ γ) ⊕ δ) :
            MvPolynomial (γ ⊕ δ) k →ₐ[k] _).toRingHom.comp
          (rename (Sum.inl : γ → γ ⊕ δ) : MvPolynomial γ k →ₐ[k] _).toRingHom :=
        RingHom.ext fun c ↦ (rename_rename _ _ c).trans
          (rename_rename (Sum.inl : γ → γ ⊕ δ) (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr) c).symm
      rw [Polynomial.eval₂_map, hc, show (X (Sum.inr d) :
        MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k) = (rename (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr :
          γ ⊕ δ → ((α ⊕ β) ⊕ γ) ⊕ δ) : MvPolynomial (γ ⊕ δ) k →ₐ[k] _).toRingHom
            (X (Sum.inr d)) from (rename_X (R := k) (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr :
              γ ⊕ δ → ((α ⊕ β) ⊕ γ) ⊕ δ) (Sum.inr d)).symm, ← Polynomial.hom_eval₂]
      exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hp)


-- @@ L268-284 verbatim
/-- The locus of a joint tuple whose outer pairs have the original loci contains the threefold
incidence ideal. -/
private theorem chain_le_idealOf {x' : α → Ω} {w' : δ → Ω}
    (hx' : idealOf k (Sum.elim x' y) = idealOf k (Sum.elim x y))
    (hw' : idealOf k (Sum.elim z w') = idealOf k (Sum.elim z w)) :
    ℐ₄ ≤ idealOf k (Sum.elim (Sum.elim (Sum.elim x' y) z) w') :=
  sup_le (sup_le
    (Ideal.map_le_iff_le_comap.2 (hx' ▸ (idealOf_eq_comap_rename (k := k)
      (a := Sum.elim (Sum.elim (Sum.elim x' y) z) w') (b := Sum.elim x' y)
      (g := Sum.inl ∘ Sum.inl) rfl).le))
    (Ideal.map_le_iff_le_comap.2 (idealOf_eq_comap_rename (k := k)
      (a := Sum.elim (Sum.elim (Sum.elim x' y) z) w') (b := Sum.elim y z) (g := 𝔢)
      (funext fun i ↦ by rcases i with b | c <;> rfl)).le))
    (Ideal.map_le_iff_le_comap.2 (hw' ▸ (idealOf_eq_comap_rename (k := k)
      (a := Sum.elim (Sum.elim (Sum.elim x' y) z) w') (b := Sum.elim z w')
      (g := Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr)
      (funext fun i ↦ by rcases i with c | d <;> rfl)).le))


-- @@ L286-312 verbatim
/-- The zero locus of the image of a prime above the incidence ideal has dense middle image
exactly when the prime contracts to the middle locus. -/
private theorem chain_dense_iff (𝔭 : Ideal (MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k))
    (h𝔭 : ℐ₄ ≤ 𝔭) :
    closure (PrimeSpectrum.comap (π₄).toRingHom '' PrimeSpectrum.zeroLocus
        (Ideal.map (Ideal.Quotient.mk ℐ₄) 𝔭 : Set (MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k ⧸ ℐ₄))) =
        Set.univ ↔
      𝔭.comap (rename 𝔢 : MvPolynomial (β ⊕ γ) k →ₐ[k] _) = idealOf k (Sum.elim y z) := by
  rw [PrimeSpectrum.closure_image_comap_zeroLocus, PrimeSpectrum.zeroLocus_eq_univ_iff,
    nilradical_eq_zero, Ideal.zero_eq_bot, SetLike.coe_subset_coe, le_bot_iff]
  have hge : idealOf k (Sum.elim y z) ≤ 𝔭.comap (rename 𝔢 : MvPolynomial (β ⊕ γ) k →ₐ[k] _) :=
    (Ideal.map_le_iff_le_comap.1 (le_sup_right.trans le_sup_left)).trans (Ideal.comap_mono h𝔭)
  constructor
  · intro h
    refine le_antisymm (fun c hc ↦ ?_) hge
    have hmem : Ideal.Quotient.mk (idealOf k (Sum.elim y z)) c ∈
        (Ideal.map (Ideal.Quotient.mk ℐ₄) 𝔭).comap (π₄).toRingHom := by
      rw [Ideal.mem_comap]
      exact Ideal.mem_map_of_mem _ hc
    rw [h, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
    exact hmem
  · intro h
    refine eq_bot_iff.2 fun b hb ↦ ?_
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem, ← h, Ideal.mem_comap]
    rw [Ideal.mem_comap] at hb
    exact (Ideal.mem_quotient_iff_mem h𝔭).1 hb


-- @@ L314-337 verbatim
/-- Every prime above the threefold incidence ideal contracting to the middle locus is the locus of
a joint tuple with the given middle, whose coordinates are algebraic over `k(y, z)`. -/
private theorem chain_realization [IsAlgClosed Ω] (hxy : ∀ i, x i ∈ racl k (Set.range y))
    (hwz : ∀ l, w l ∈ racl k (Set.range z)) (q : Ideal (MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k))
    [q.IsPrime] (hq : ℐ₄ ≤ q)
    (hc : q.comap (rename 𝔢 : MvPolynomial (β ⊕ γ) k →ₐ[k] _) = idealOf k (Sum.elim y z)) :
    ∃ (x'' : α → Ω) (w'' : δ → Ω),
      idealOf k (Sum.elim (Sum.elim (Sum.elim x'' y) z) w'') = q ∧
        ∀ i, Sum.elim (Sum.elim (Sum.elim x'' y) z) w'' i ∈ racl k (Set.range (Sum.elim y z)) := by
  obtain ⟨T, hTg, hT⟩ := exists_idealOf_eq 𝔢 (Sum.elim y z) q hc fun i ↦
    (chain_relations x y z w hxy hwz i).imp fun _ hp ↦ ⟨hp.1, hq hp.2⟩
  have hTJ : T = Sum.elim (Sum.elim (Sum.elim (T ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl) y) z)
      (T ∘ Sum.inr) := funext fun i ↦ by
    rcases i with ((a | b) | c) | d
    · rfl
    · exact congrFun hTg (Sum.inl b)
    · exact congrFun hTg (Sum.inr c)
    · rfl
  refine ⟨T ∘ Sum.inl ∘ Sum.inl ∘ Sum.inl, T ∘ Sum.inr,
    (congrArg (idealOf k) hTJ).symm.trans hT, fun i ↦ ?_⟩
  rw [← hTJ]
  obtain ⟨p, ⟨j, hj⟩, hp⟩ := chain_relations x y z w hxy hwz i
  have := mem_racl_of_relation T 𝔢 (i := i) (p := p) ⟨j, by rwa [hTg]⟩ (hT.ge (hq hp))
  rwa [hTg] at this


-- @@ L339-427 verbatim
/-- **Dominating components of the threefold incidence spectrum.** -/
private theorem chain_dominatingComponents [IsAlgClosed Ω]
    (hxy : ∀ i, x i ∈ racl k (Set.range y)) (hwz : ∀ l, w l ∈ racl k (Set.range z)) :
    {Z : Set (PrimeSpectrum (MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k ⧸ ℐ₄)) |
        Z ∈ irreducibleComponents _ ∧
          closure (PrimeSpectrum.comap (π₄).toRingHom '' Z) = Set.univ} =
      {C | ∃ (x' : α → Ω) (w' : δ → Ω), idealOf k (Sum.elim x' y) = idealOf k (Sum.elim x y) ∧
        idealOf k (Sum.elim z w') = idealOf k (Sum.elim z w) ∧
        C = PrimeSpectrum.zeroLocus (Ideal.map (Ideal.Quotient.mk ℐ₄)
          (idealOf k (Sum.elim (Sum.elim (Sum.elim x' y) z) w')) :
            Set (MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k ⧸ ℐ₄))} := by
  -- The outer pair ideals of a realization are the original ones, by incomparability.
  have hpair (x' : α → Ω) (w' : δ → Ω)
      (hℐ : ℐ₄ ≤ idealOf k (Sum.elim (Sum.elim (Sum.elim x' y) z) w')) :
      idealOf k (Sum.elim x' y) = idealOf k (Sum.elim x y) ∧
        idealOf k (Sum.elim z w') = idealOf k (Sum.elim z w) := by
    refine ⟨idealOf_eq_of_le_of_comap_eq (Sum.elim x y) Sum.inr (fun i ↦ ?_) ?_
      (idealOf_eq_comap_rename (k := k) (a := Sum.elim x' y) (b := y) (g := Sum.inr) rfl).symm,
      idealOf_eq_of_le_of_comap_eq (Sum.elim z w) Sum.inl (fun i ↦ ?_) ?_
      (idealOf_eq_comap_rename (k := k) (a := Sum.elim z w') (b := z) (g := Sum.inl) rfl).symm⟩
    · rcases i with a | b
      · exact hxy a
      · exact subset_racl k _ ⟨b, rfl⟩
    · exact (Ideal.map_le_iff_le_comap.1 (le_sup_left.trans (le_sup_left.trans hℐ))).trans
        (idealOf_eq_comap_rename (k := k) (a := Sum.elim (Sum.elim (Sum.elim x' y) z) w')
          (b := Sum.elim x' y) (g := Sum.inl ∘ Sum.inl) rfl).ge
    · rcases i with c | d
      · exact subset_racl k _ ⟨c, rfl⟩
      · exact hwz d
    · exact (Ideal.map_le_iff_le_comap.1 (le_sup_right.trans hℐ)).trans
        (idealOf_eq_comap_rename (k := k) (a := Sum.elim (Sum.elim (Sum.elim x' y) z) w')
          (b := Sum.elim z w') (g := Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr)
          (funext fun i ↦ by rcases i with c | d <;> rfl)).ge
  ext C
  constructor
  · rintro ⟨hC, hd⟩
    have : (PrimeSpectrum.vanishingIdeal C).IsPrime :=
      PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.1 hC.1
    have h𝔭 : ℐ₄ ≤ (PrimeSpectrum.vanishingIdeal C).comap (Ideal.Quotient.mk ℐ₄) := fun f hf ↦ by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hf]
      exact zero_mem _
    have hC𝔭 : C = PrimeSpectrum.zeroLocus (Ideal.map (Ideal.Quotient.mk ℐ₄)
        ((PrimeSpectrum.vanishingIdeal C).comap (Ideal.Quotient.mk ℐ₄)) :
          Set (MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k ⧸ ℐ₄)) := by
      rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
        PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
        (isClosed_of_mem_irreducibleComponents C hC).closure_eq]
    rw [hC𝔭] at hd
    obtain ⟨x', w', hJ, -⟩ := chain_realization x y z w hxy hwz _ h𝔭
      ((chain_dense_iff x y z w _ h𝔭).1 hd)
    obtain ⟨hx', hw'⟩ := hpair x' w' (hJ ▸ h𝔭)
    exact ⟨x', w', hx', hw', hC𝔭.trans (by rw [hJ])⟩
  · rintro ⟨x', w', hx', hw', rfl⟩
    have hℐ := chain_le_idealOf x y z w hx' hw'
    have hc : (idealOf k (Sum.elim (Sum.elim (Sum.elim x' y) z) w')).comap
        (rename 𝔢 : MvPolynomial (β ⊕ γ) k →ₐ[k] _) = idealOf k (Sum.elim y z) :=
      (idealOf_eq_comap_rename (k := k) (funext fun i ↦ by rcases i with b | c <;> rfl)).symm
    have hprime : (Ideal.map (Ideal.Quotient.mk ℐ₄)
        (idealOf k (Sum.elim (Sum.elim (Sum.elim x' y) z) w'))).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
    refine ⟨?_, (chain_dense_iff x y z w _ hℐ).2 hc⟩
    rw [PrimeSpectrum.zeroLocus_ideal_mem_irreducibleComponents, hprime.radical]
    refine ⟨⟨hprime, bot_le⟩, fun Q' hQ' hle ↦ ?_⟩
    have : Q'.IsPrime := hQ'.1
    have : (Q'.comap (Ideal.Quotient.mk ℐ₄)).IsPrime := Ideal.comap_isPrime _ _
    have hq : ℐ₄ ≤ Q'.comap (Ideal.Quotient.mk ℐ₄) := fun f hf ↦ by
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.2 hf]
      exact zero_mem _
    have hq𝔭 : Q'.comap (Ideal.Quotient.mk ℐ₄) ≤
        idealOf k (Sum.elim (Sum.elim (Sum.elim x' y) z) w') :=
      (Ideal.comap_mono hle).trans (Ideal.comap_map_mk hℐ).le
    have hqc : (Q'.comap (Ideal.Quotient.mk ℐ₄)).comap
        (rename 𝔢 : MvPolynomial (β ⊕ γ) k →ₐ[k] _) = idealOf k (Sum.elim y z) :=
      le_antisymm ((Ideal.comap_mono hq𝔭).trans hc.le)
        ((Ideal.map_le_iff_le_comap.1 (le_sup_right.trans le_sup_left)).trans
          (Ideal.comap_mono hq))
    obtain ⟨x'', w'', hq'', halg⟩ := chain_realization x y z w hxy hwz _ hq hqc
    have h𝔢 : Sum.elim (Sum.elim (Sum.elim x'' y) z) w'' ∘ 𝔢 = Sum.elim y z :=
      funext fun i ↦ by rcases i with b | c <;> rfl
    have halg' : ∀ i, Sum.elim (Sum.elim (Sum.elim x'' y) z) w'' i ∈
        racl k (Set.range (Sum.elim (Sum.elim (Sum.elim x'' y) z) w'' ∘ 𝔢)) := by
      rw [h𝔢]
      exact halg
    have heq : idealOf k (Sum.elim (Sum.elim (Sum.elim x' y) z) w') =
        Q'.comap (Ideal.Quotient.mk ℐ₄) :=
      (idealOf_eq_of_le_of_comap_eq (Sum.elim (Sum.elim (Sum.elim x'' y) z) w'') 𝔢 halg'
        (hq''.le.trans hq𝔭) (hc.trans (congrArg (idealOf k) h𝔢).symm)).trans hq''
    rw [heq]
    exact Ideal.map_le_iff_le_comap.2 le_rfl


-- @@ L429-442 verbatim
/-- The endpoint contraction of the component of a joint tuple is the locus of its endpoints. -/
private theorem chain_contraction {x' : α → Ω} {w' : δ → Ω}
    (hℐ : ℐ₄ ≤ idealOf k (Sum.elim (Sum.elim (Sum.elim x' y) z) w')) :
    ((PrimeSpectrum.vanishingIdeal (PrimeSpectrum.zeroLocus (Ideal.map (Ideal.Quotient.mk ℐ₄)
        (idealOf k (Sum.elim (Sum.elim (Sum.elim x' y) z) w')) :
          Set (MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k ⧸ ℐ₄)))).comap (Ideal.Quotient.mk ℐ₄)).comap
      (rename (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) Sum.inr : α ⊕ δ → ((α ⊕ β) ⊕ γ) ⊕ δ) :
        MvPolynomial (α ⊕ δ) k →ₐ[k] _) = idealOf k (Sum.elim x' w') := by
  have hprime : (Ideal.map (Ideal.Quotient.mk ℐ₄)
      (idealOf k (Sum.elim (Sum.elim (Sum.elim x' y) z) w'))).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  rw [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, hprime.radical, Ideal.comap_map_mk hℐ]
  exact (idealOf_eq_comap_rename (k := k) (a := Sum.elim (Sum.elim (Sum.elim x' y) z) w')
    (b := Sum.elim x' w') (funext fun i ↦ by rcases i with a | d <;> rfl)).symm


-- @@ L444-444 verbatim
end Chain


-- @@ L446-473 verbatim
/-- The normalization of the coordinate domain `A = R ⧸ p` of an irreducible component, the
integral closure `N` of `A` in its fraction field, is integrally closed and has the fraction
field of `A`, compatibly with `A`. Passing to it does not change the generic kernel of any map
into `R`. -/
private theorem normalization_generic_data {R T : Type*} [CommRing R] [CommRing T]
    (p : Ideal R) [p.IsPrime] (f : T →+* R) :
    let A := R ⧸ p
    let N := integralClosure A (FractionRing A)
    IsIntegrallyClosed N ∧
      ∃ e : FractionRing N ≃ₐ[N] FractionRing A,
        (∀ a : A, e (algebraMap N (FractionRing N) (algebraMap A N a)) =
          algebraMap A (FractionRing A) a) ∧
        RingHom.ker (((algebraMap N (FractionRing N)).comp (algebraMap A N)).comp
          ((Ideal.Quotient.mk p).comp f)) = p.comap f := by
  let A := R ⧸ p
  let K := FractionRing A
  let N := integralClosure A K
  have hnorm : IsIntegrallyClosed N :=
    integralClosure.isIntegrallyClosedOfFiniteExtension K
  let _ : IsFractionRing N K := integralClosure.isFractionRing_of_finite_extension K K
  let e : FractionRing N ≃ₐ[N] K :=
    IsLocalization.algEquiv (nonZeroDivisors N) (FractionRing N) K
  refine ⟨hnorm, e, fun a ↦ e.commutes (algebraMap A N a), ?_⟩
  have hi : Function.Injective (algebraMap A N) := fun a b h ↦
    IsFractionRing.injective A K (congrArg (algebraMap N K) h)
  have hj : Function.Injective ((algebraMap N (FractionRing N)).comp (algebraMap A N)) :=
    (IsFractionRing.injective N (FractionRing N)).comp hi
  rw [RingHom.ker_comp_of_injective _ hj, ← RingHom.comap_ker, Ideal.mk_ker]


-- @@ L475-475 verbatim
namespace TupleCorrespondenceGerm


-- @@ L477-478 verbatim
variable {α β γ δ : Type*} (P : TupleCorrespondencePair k Ω α β)
  (Q : TupleCorrespondencePair k Ω β γ) (S : TupleCorrespondencePair k Ω γ δ)


-- @@ L480-493 verbatim
local notation "𝒥" =>
  Ideal.map (rename (Sum.inl ∘ Sum.inl : α ⊕ β → ((α ⊕ β) ⊕ γ) ⊕ δ) :
      MvPolynomial (α ⊕ β) k →ₐ[k] MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k)
    (idealOf k (Sum.elim (TupleCorrespondencePair.source P)
      (TupleCorrespondencePair.target P))) ⊔
  Ideal.map (rename (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inr) (Sum.inl ∘ Sum.inr) :
      β ⊕ γ → ((α ⊕ β) ⊕ γ) ⊕ δ) :
      MvPolynomial (β ⊕ γ) k →ₐ[k] MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k)
    (idealOf k (Sum.elim (TupleCorrespondencePair.target P)
      (TupleCorrespondencePair.target Q))) ⊔
  Ideal.map (rename (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr : γ ⊕ δ → ((α ⊕ β) ⊕ γ) ⊕ δ) :
      MvPolynomial (γ ⊕ δ) k →ₐ[k] MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k)
    (idealOf k (Sum.elim (TupleCorrespondencePair.target Q)
      (TupleCorrespondencePair.target S)))


-- @@ L495-584 verbatim
/-- **Threefold composites are endpoint images of threefold incidence components.** Let `(x, y)`,
`(y, z)` and `(z, w)` present tuple correspondence germs with literally shared middle tuples, for
finite index types in an algebraically closed ambient field. For either parenthesization, the ideals
of the final composites are exactly the contractions to the endpoint variables `X, W` of the
vanishing ideals of the irreducible components of
`Spec (k[X, Y, Z, W] ⧸ (I(x, y) + I(y, z) + I(z, w)))` with dense image in the locus of `(y, z)`.

Moreover, the normalization of each irreducible component, the integral closure `N` of its
coordinate domain `A` in the fraction field of `A`, is integrally closed, has the fraction field of
`A`, and has the same endpoint generic ideal. Thus the final germs are equally the endpoint germs
of the normalized components (blueprint §8.1). -/
theorem composes_threefold_components_eq [Finite α] [Finite β] [Finite γ] [Finite δ]
    [IsAlgClosed Ω] (hPQ : P.target = Q.source) (hQS : Q.target = S.source) :
    {I | ∃ (E : TupleCorrespondenceGerm k Ω α γ) (F : TupleCorrespondenceGerm k Ω α δ),
        Composes (ofPair P) (ofPair Q) E ∧ Composes E (ofPair S) F ∧ F.carrier = I} =
      {I | ∃ Z ∈ irreducibleComponents
          (PrimeSpectrum (MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k ⧸ 𝒥)),
        closure (PrimeSpectrum.comap (Ideal.quotientMapₐ 𝒥
          (rename (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inr) (Sum.inl ∘ Sum.inr) :
            β ⊕ γ → ((α ⊕ β) ⊕ γ) ⊕ δ) :
            MvPolynomial (β ⊕ γ) k →ₐ[k] MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k)
          (Ideal.map_le_iff_le_comap.1 (le_sup_right.trans le_sup_left))).toRingHom '' Z) =
            Set.univ ∧
        I = ((PrimeSpectrum.vanishingIdeal Z).comap (Ideal.Quotient.mk 𝒥)).comap
          (rename (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) Sum.inr : α ⊕ δ → ((α ⊕ β) ⊕ γ) ⊕ δ) :
            MvPolynomial (α ⊕ δ) k →ₐ[k] _)} ∧
    {I | ∃ (E : TupleCorrespondenceGerm k Ω β δ) (F : TupleCorrespondenceGerm k Ω α δ),
        Composes (ofPair Q) (ofPair S) E ∧ Composes (ofPair P) E F ∧ F.carrier = I} =
      {I | ∃ Z ∈ irreducibleComponents
          (PrimeSpectrum (MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k ⧸ 𝒥)),
        closure (PrimeSpectrum.comap (Ideal.quotientMapₐ 𝒥
          (rename (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inr) (Sum.inl ∘ Sum.inr) :
            β ⊕ γ → ((α ⊕ β) ⊕ γ) ⊕ δ) :
            MvPolynomial (β ⊕ γ) k →ₐ[k] MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k)
          (Ideal.map_le_iff_le_comap.1 (le_sup_right.trans le_sup_left))).toRingHom '' Z) =
            Set.univ ∧
        I = ((PrimeSpectrum.vanishingIdeal Z).comap (Ideal.Quotient.mk 𝒥)).comap
          (rename (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) Sum.inr : α ⊕ δ → ((α ⊕ β) ⊕ γ) ⊕ δ) :
            MvPolynomial (α ⊕ δ) k →ₐ[k] _)} ∧
    ∀ Z ∈ irreducibleComponents (PrimeSpectrum (MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k ⧸ 𝒥)),
      let p := (PrimeSpectrum.vanishingIdeal Z).comap (Ideal.Quotient.mk 𝒥)
      let A := MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k ⧸ p
      let N := integralClosure A (FractionRing A)
      IsIntegrallyClosed N ∧
        ∃ e : FractionRing N ≃ₐ[N] FractionRing A,
          (∀ a : A, e (algebraMap N (FractionRing N) (algebraMap A N a)) =
            algebraMap A (FractionRing A) a) ∧
          RingHom.ker (((algebraMap N (FractionRing N)).comp (algebraMap A N)).comp
            ((Ideal.Quotient.mk p).comp (rename (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) Sum.inr :
              α ⊕ δ → ((α ⊕ β) ⊕ γ) ⊕ δ) : MvPolynomial (α ⊕ δ) k →ₐ[k] _).toRingHom)) =
            p.comap (rename (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) Sum.inr :
              α ⊕ δ → ((α ⊕ β) ⊕ γ) ⊕ δ) : MvPolynomial (α ⊕ δ) k →ₐ[k] _) := by
  have hwz : ∀ l, S.target l ∈ racl k (Set.range Q.target) := fun l ↦ by
    rw [hQS]
    exact S.target_mem_source l
  have hset := chain_dominatingComponents P.source P.target Q.target S.target
    P.source_mem_target hwz
  -- The realization description of the final germs equals the component description.
  have hT : {I | ∃ (x' : α → Ω) (w' : δ → Ω),
      idealOf k (Sum.elim x' P.target) = idealOf k (Sum.elim P.source P.target) ∧
      idealOf k (Sum.elim Q.target w') = idealOf k (Sum.elim Q.target S.target) ∧
      I = idealOf k (Sum.elim x' w')} =
      {I | ∃ Z ∈ irreducibleComponents
          (PrimeSpectrum (MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k ⧸ 𝒥)),
        closure (PrimeSpectrum.comap (Ideal.quotientMapₐ 𝒥
          (rename (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inr) (Sum.inl ∘ Sum.inr) :
            β ⊕ γ → ((α ⊕ β) ⊕ γ) ⊕ δ) :
            MvPolynomial (β ⊕ γ) k →ₐ[k] MvPolynomial (((α ⊕ β) ⊕ γ) ⊕ δ) k)
          (Ideal.map_le_iff_le_comap.1 (le_sup_right.trans le_sup_left))).toRingHom '' Z) =
            Set.univ ∧
        I = ((PrimeSpectrum.vanishingIdeal Z).comap (Ideal.Quotient.mk 𝒥)).comap
          (rename (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) Sum.inr : α ⊕ δ → ((α ⊕ β) ⊕ γ) ⊕ δ) :
            MvPolynomial (α ⊕ δ) k →ₐ[k] _)} := by
    ext I
    constructor
    · rintro ⟨x', w', hx', hw', rfl⟩
      obtain ⟨hZ, hd⟩ := (Set.ext_iff.1 hset _).2 ⟨x', w', hx', hw', rfl⟩
      exact ⟨_, hZ, hd, (chain_contraction P.source P.target Q.target S.target
        (chain_le_idealOf P.source P.target Q.target S.target hx' hw')).symm⟩
    · rintro ⟨Z, hZ, hd, rfl⟩
      obtain ⟨x', w', hx', hw', rfl⟩ := (Set.ext_iff.1 hset Z).1 ⟨hZ, hd⟩
      exact ⟨x', w', hx', hw', chain_contraction P.source P.target Q.target S.target
        (chain_le_idealOf P.source P.target Q.target S.target hx' hw')⟩
  obtain ⟨h₁, h₂⟩ := composes_threefold_carriers_eq P Q S hPQ hQS
  refine ⟨h₁.trans hT, h₂.trans hT, fun Z hZ ↦ ?_⟩
  have : (PrimeSpectrum.vanishingIdeal Z).IsPrime :=
    PrimeSpectrum.isIrreducible_iff_vanishingIdeal_isPrime.1 hZ.1
  exact normalization_generic_data _
    (rename (Sum.elim (Sum.inl ∘ Sum.inl ∘ Sum.inl) Sum.inr : α ⊕ δ → ((α ⊕ β) ⊕ γ) ⊕ δ) :
      MvPolynomial (α ⊕ δ) k →ₐ[k] _).toRingHom


-- @@ L586-586 verbatim
end TupleCorrespondenceGerm


-- @@ L588-588 verbatim
end AclGeom
