/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import AclGeom.Correspondence.LocusQuotient


-- @@ L8-48 verbatim
/-!
# The incidence quotient of a pair of tuple loci

For tuples `x`, `y`, `z` in a field `Ω` over `k`, the incidence ring of the loci of `(x, y)` and
`(y, z)` over the locus of `y` is the quotient of the joint polynomial ring `k[X, Y, Z]` by the sum
of the vanishing ideals `I(x, y)` and `I(y, z)`, extended along the inclusions of the variables.
`exists_locusIncidence_algEquiv` identifies it, as a `k`-algebra, with the literal relative tensor
product `k[X, Y] ⧸ I(x, y) ⊗[k[Y] ⧸ I(y)] k[Y, Z] ⧸ I(y, z)`. The identification sends the pure
tensor of the classes of `p` and `q` to the class of the product of their renamings, and the class
of a polynomial in `Y` to its class in the incidence ring. The endpoint and middle projections are
the instances of this formula with one factor `1`. Only the tuples are data, and the index types,
the base field and the ambient field may lie in independent universes. The maps from the
coordinate rings of the loci of `x`, `y` and `z` into the incidence ring are induced by the
inclusions of the variables; `idealOf_le_comap_rename_comp` supplies their containments.

The incidence ideal is contained in the vanishing ideal of the joint tuple `(x, y, z)`, so joint
evaluation factors through the incidence ring. `LocusJointComponent` identifies the actual joint
evaluation kernel as a middle-dominating component when each coordinate of `z` is algebraic over
`k(y)`. It also proves `locusIncidence_dominatingComponents_eq_jointLoci`: for finite outer
tuples in an algebraically closed ambient field, with both `x` and `z` algebraic over `k(y)`,
these components are exactly the joint loci of realizations with the two original pair ideals.
The middle tuple and the base field remain arbitrary.

`TupleComposition` proves relational associativity of finite-tuple germs, nonempty composition
for equal middle ideals, and the equality between composite carrier ideals and endpoint
contractions of middle-dominating incidence components, in an algebraically closed ambient
field. `TupleCompositionField` derives target rank one and proves finiteness of the actual
generated joint field over the endpoint field and over both end fields, under the relevant
finite-index and algebraicity hypotheses. These field results work over arbitrary base and
ambient fields.

`LocusComponentField` identifies each actual middle-dominating component's coordinate ring and
fraction field with the realized joint generated ring and compositum, including polynomial
representative formulas. The remaining source obligations are recorded in the book's hard-kernel
chapter and the current frontier of `PROJECT_GOAL.md`.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** proved (#5, C2 support).
-/


-- @@ L50-50 verbatim
open scoped TensorProduct

-- @@ L51-51 verbatim
open MvPolynomial


-- @@ L53-53 verbatim
namespace AclGeom


-- @@ L55-55 verbatim
section Incidence


-- @@ L57-58 verbatim
variable {k σ τ ρ : Type*} [CommRing k] (I : Ideal (MvPolynomial (σ ⊕ τ) k))
  (I' : Ideal (MvPolynomial (τ ⊕ ρ) k)) (I₀ : Ideal (MvPolynomial τ k))


-- @@ L60-60 verbatim
local notation "𝒜" => MvPolynomial τ k ⧸ I₀

-- @@ L61-61 verbatim
local notation "ℬ" => MvPolynomial (σ ⊕ τ) k ⧸ I

-- @@ L62-62 verbatim
local notation "𝒞" => MvPolynomial (τ ⊕ ρ) k ⧸ I'

-- @@ L63-63 verbatim
local notation "ι₂" => (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr : τ ⊕ ρ → (σ ⊕ τ) ⊕ ρ)

-- @@ L64-66 verbatim
local notation "𝒥" => Ideal.map (rename (Sum.inl : σ ⊕ τ → (σ ⊕ τ) ⊕ ρ) :
    MvPolynomial (σ ⊕ τ) k →ₐ[k] MvPolynomial ((σ ⊕ τ) ⊕ ρ) k) I ⊔
  Ideal.map (rename ι₂ : MvPolynomial (τ ⊕ ρ) k →ₐ[k] MvPolynomial ((σ ⊕ τ) ⊕ ρ) k) I'


-- @@ L68-191 verbatim
/-- The relative tensor product of two polynomial quotients over a third, whose structure maps are
induced by the inclusions of the shared variables, is the quotient of the joint polynomial ring by
the sum of the two extended ideals. -/
private theorem exists_tensorProduct_quotient_algEquiv [Algebra 𝒜 ℬ] [Algebra 𝒜 𝒞]
    [IsScalarTower k 𝒜 ℬ]
    (h₁ : ∀ p, algebraMap 𝒜 ℬ (Ideal.Quotient.mk I₀ p) = Ideal.Quotient.mk I (rename Sum.inr p))
    (h₂ : ∀ p, algebraMap 𝒜 𝒞 (Ideal.Quotient.mk I₀ p) = Ideal.Quotient.mk I' (rename Sum.inl p)) :
    ∃ Φ : ℬ ⊗[𝒜] 𝒞 ≃ₐ[k] MvPolynomial ((σ ⊕ τ) ⊕ ρ) k ⧸ 𝒥,
      (∀ p q, Φ (Ideal.Quotient.mk I p ⊗ₜ Ideal.Quotient.mk I' q) =
        Ideal.Quotient.mk 𝒥 (rename Sum.inl p * rename ι₂ q)) ∧
      ∀ p, Φ (algebraMap 𝒜 (ℬ ⊗[𝒜] 𝒞) (Ideal.Quotient.mk I₀ p)) =
        Ideal.Quotient.mk 𝒥 (rename (Sum.inl ∘ Sum.inr) p) := by
  -- The two factor maps into the incidence quotient.
  have hI (p : MvPolynomial (σ ⊕ τ) k) (hp : p ∈ I) :
      ((Ideal.Quotient.mkₐ k 𝒥).comp (rename Sum.inl)) p = 0 := by
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp)
  have hI' (q : MvPolynomial (τ ⊕ ρ) k) (hq : q ∈ I') :
      ((Ideal.Quotient.mkₐ k 𝒥).comp (rename ι₂)) q = 0 := by
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ hq)
  let fk := Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ k 𝒥).comp (rename Sum.inl)) hI
  let gk := Ideal.Quotient.liftₐ I' ((Ideal.Quotient.mkₐ k 𝒥).comp (rename ι₂)) hI'
  have hf (p : MvPolynomial (σ ⊕ τ) k) :
      fk (Ideal.Quotient.mk I p) = Ideal.Quotient.mk 𝒥 (rename Sum.inl p) := rfl
  have hg (q : MvPolynomial (τ ⊕ ρ) k) :
      gk (Ideal.Quotient.mk I' q) = Ideal.Quotient.mk 𝒥 (rename ι₂ q) := rfl
  -- Both factor maps agree on the middle ring.
  have hmid (r : 𝒜) : gk (algebraMap 𝒜 𝒞 r) = fk (algebraMap 𝒜 ℬ r) := by
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [h₁, h₂, hf, hg, rename_rename, rename_rename, Sum.elim_comp_inl]
  let _ : Algebra 𝒜 (MvPolynomial ((σ ⊕ τ) ⊕ ρ) k ⧸ 𝒥) :=
    (fk.toRingHom.comp (algebraMap 𝒜 ℬ)).toAlgebra
  let fQ : ℬ →ₐ[𝒜] MvPolynomial ((σ ⊕ τ) ⊕ ρ) k ⧸ 𝒥 :=
    { fk.toRingHom with commutes' := fun _ ↦ rfl }
  let gQ : 𝒞 →ₐ[𝒜] MvPolynomial ((σ ⊕ τ) ⊕ ρ) k ⧸ 𝒥 :=
    { gk.toRingHom with commutes' := hmid }
  let F := Algebra.TensorProduct.lift fQ gQ fun _ _ ↦ Commute.all _ _
  have hF (a : ℬ) (b : 𝒞) : F (a ⊗ₜ b) = fk a * gk b := Algebra.TensorProduct.lift_tmul _ _ _ a b
  let Fk : ℬ ⊗[𝒜] 𝒞 →ₐ[k] MvPolynomial ((σ ⊕ τ) ⊕ ρ) k ⧸ 𝒥 :=
    { F.toRingHom with
      commutes' := fun c ↦ by
        change F (algebraMap k ℬ c ⊗ₜ[𝒜] (1 : 𝒞)) = _
        rw [hF, map_one, mul_one, AlgHom.commutes] }
  -- The inverse map, on the joint polynomial ring.
  have hswap (s : 𝒜) : algebraMap 𝒜 ℬ s ⊗ₜ[𝒜] (1 : 𝒞) = (1 : ℬ) ⊗ₜ[𝒜] algebraMap 𝒜 𝒞 s :=
    (Algebra.TensorProduct.algebraMap_apply s).symm.trans
      (Algebra.TensorProduct.algebraMap_apply' s)
  let G₀ : MvPolynomial ((σ ⊕ τ) ⊕ ρ) k →ₐ[k] ℬ ⊗[𝒜] 𝒞 :=
    aeval (Sum.elim (fun i ↦ Ideal.Quotient.mk I (X i) ⊗ₜ (1 : 𝒞))
      (fun c ↦ (1 : ℬ) ⊗ₜ Ideal.Quotient.mk I' (X (Sum.inr c))))
  have hG₀X (i : (σ ⊕ τ) ⊕ ρ) : G₀ (X i) = Sum.elim (fun i ↦ Ideal.Quotient.mk I (X i) ⊗ₜ (1 : 𝒞))
      (fun c ↦ (1 : ℬ) ⊗ₜ Ideal.Quotient.mk I' (X (Sum.inr c))) i := aeval_X _ i
  have hG₀C (r : k) : G₀ (C r) = algebraMap k (ℬ ⊗[𝒜] 𝒞) r := aeval_C _ r
  have H1 (p : MvPolynomial (σ ⊕ τ) k) :
      G₀ (rename Sum.inl p) = Ideal.Quotient.mk I p ⊗ₜ (1 : 𝒞) := by
    have : G₀.comp (rename Sum.inl) =
        Algebra.TensorProduct.includeLeft.comp (Ideal.Quotient.mkₐ k I) :=
      MvPolynomial.algHom_ext fun i ↦ by
        simp only [AlgHom.comp_apply, rename_X, hG₀X, Sum.elim_inl,
          Algebra.TensorProduct.includeLeft_apply, Ideal.Quotient.mkₐ_eq_mk]
    exact AlgHom.congr_fun this p
  have H2 (q : MvPolynomial (τ ⊕ ρ) k) :
      G₀ (rename ι₂ q) = (1 : ℬ) ⊗ₜ Ideal.Quotient.mk I' q := by
    have : (G₀ : MvPolynomial ((σ ⊕ τ) ⊕ ρ) k →+* ℬ ⊗[𝒜] 𝒞).comp
        (rename ι₂ : MvPolynomial (τ ⊕ ρ) k →ₐ[k] MvPolynomial ((σ ⊕ τ) ⊕ ρ) k).toRingHom =
        ((Algebra.TensorProduct.includeRight : 𝒞 →ₐ[𝒜] ℬ ⊗[𝒜] 𝒞) : 𝒞 →+* ℬ ⊗[𝒜] 𝒞).comp
          (Ideal.Quotient.mk I') := by
      refine MvPolynomial.ringHom_ext (fun r ↦ ?_) (fun i ↦ ?_)
      · have hB : algebraMap 𝒜 ℬ (Ideal.Quotient.mk I₀ (C r)) = algebraMap k ℬ r :=
          (h₁ (C r)).trans (congrArg (Ideal.Quotient.mk I) (rename_C _ r))
        change G₀ (rename ι₂ (C r)) = (1 : ℬ) ⊗ₜ Ideal.Quotient.mk I' (C r)
        rw [rename_C, hG₀C, Algebra.TensorProduct.algebraMap_apply, ← hB, hswap, h₂, rename_C]
      · rcases i with b | c
        · change G₀ (rename ι₂ (X (Sum.inl b))) =
            (1 : ℬ) ⊗ₜ Ideal.Quotient.mk I' (X (Sum.inl b))
          rw [rename_X, hG₀X]
          change Ideal.Quotient.mk I (X (Sum.inr b)) ⊗ₜ (1 : 𝒞) = _
          rw [← rename_X Sum.inr b, ← h₁, hswap, h₂, rename_X]
        · change G₀ (rename ι₂ (X (Sum.inr c))) =
            (1 : ℬ) ⊗ₜ Ideal.Quotient.mk I' (X (Sum.inr c))
          rw [rename_X, hG₀X]
          rfl
    exact RingHom.congr_fun this q
  have hG (a : MvPolynomial ((σ ⊕ τ) ⊕ ρ) k) (ha : a ∈ 𝒥) : G₀ a = 0 := by
    have hle : 𝒥 ≤ RingHom.ker G₀ := by
      refine sup_le ?_ ?_
      · rw [Ideal.map_le_iff_le_comap]
        intro p hp
        rw [Ideal.mem_comap, RingHom.mem_ker, H1, Ideal.Quotient.eq_zero_iff_mem.2 hp,
          TensorProduct.zero_tmul]
      · rw [Ideal.map_le_iff_le_comap]
        intro q hq
        rw [Ideal.mem_comap, RingHom.mem_ker, H2, Ideal.Quotient.eq_zero_iff_mem.2 hq,
          TensorProduct.tmul_zero]
    exact hle ha
  let G := Ideal.Quotient.liftₐ 𝒥 G₀ hG
  have hGmk (a : MvPolynomial ((σ ⊕ τ) ⊕ ρ) k) : G (Ideal.Quotient.mk 𝒥 a) = G₀ a := rfl
  have hFG : Fk.comp G = AlgHom.id k _ := by
    refine Ideal.Quotient.algHom_ext k (MvPolynomial.algHom_ext fun i ↦ ?_)
    rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      AlgHom.id_apply, hGmk, hG₀X]
    rcases i with i | c
    · change F (Ideal.Quotient.mk I (X i) ⊗ₜ (1 : 𝒞)) = _
      rw [hF, map_one, mul_one, hf, rename_X]
    · change F ((1 : ℬ) ⊗ₜ Ideal.Quotient.mk I' (X (Sum.inr c))) = _
      rw [hF, map_one, one_mul, hg, rename_X]
      rfl
  have hGF : G.comp Fk = AlgHom.id k _ := by
    refine AlgHom.ext fun w ↦ ?_
    induction w using TensorProduct.inductionOn with
    | tmul a b =>
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective b
      change G (F (Ideal.Quotient.mk I p ⊗ₜ Ideal.Quotient.mk I' q)) =
        Ideal.Quotient.mk I p ⊗ₜ Ideal.Quotient.mk I' q
      rw [hF, hf, hg, map_mul, hGmk, hGmk, H1, H2, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
        one_mul]
    | add w₁ w₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  refine ⟨AlgEquiv.ofAlgHom Fk G hFG hGF, fun p q ↦ ?_, fun p ↦ ?_⟩
  · change F (Ideal.Quotient.mk I p ⊗ₜ Ideal.Quotient.mk I' q) = _
    rw [hF, hf, hg, map_mul]
  · change F (algebraMap 𝒜 ℬ (Ideal.Quotient.mk I₀ p) ⊗ₜ[𝒜] (1 : 𝒞)) = _
    rw [hF, map_one, mul_one, h₁, hf, rename_rename]


-- @@ L193-193 verbatim
end Incidence


-- @@ L195-195 verbatim
variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω]


-- @@ L197-205 verbatim
/-- The vanishing ideal of a reindexed tuple is contained in the contraction, along the composite
renaming, of any ideal containing the extension of the vanishing ideal of the original tuple. -/
theorem idealOf_le_comap_rename_comp {ι κ ι' : Type*} {a : ι → Ω} {b : κ → Ω} {g : κ → ι}
    (h : a ∘ g = b) {e : ι → ι'} {J : Ideal (MvPolynomial ι' k)}
    (hJ : Ideal.map (rename e : MvPolynomial ι k →ₐ[k] MvPolynomial ι' k) (idealOf k a) ≤ J) :
    idealOf k b ≤ J.comap (rename (e ∘ g) : MvPolynomial κ k →ₐ[k] MvPolynomial ι' k) := by
  intro p hp
  rw [Ideal.mem_comap, ← rename_rename]
  exact hJ (Ideal.mem_map_of_mem _ (Ideal.mem_comap.1 ((idealOf_eq_comap_rename h).le hp)))


-- @@ L207-207 verbatim
variable {α β γ : Type*} (x : α → Ω) (y : β → Ω) (z : γ → Ω)


-- @@ L209-209 verbatim
local notation "𝒜" => MvPolynomial β k ⧸ idealOf k y

-- @@ L210-210 verbatim
local notation "ℬ" => MvPolynomial (α ⊕ β) k ⧸ idealOf k (Sum.elim x y)

-- @@ L211-211 verbatim
local notation "𝒞" => MvPolynomial (β ⊕ γ) k ⧸ idealOf k (Sum.elim y z)


-- @@ L213-244 verbatim
/-- **The incidence quotient of a pair of tuple loci.** The literal relative tensor product
`k[X, Y] ⧸ I(x, y) ⊗[k[Y] ⧸ I(y)] k[Y, Z] ⧸ I(y, z)` is `k`-isomorphic to the quotient of
`k[X, Y, Z]` by the sum of `I(x, y)` and `I(y, z)` extended along the inclusions of the variables.
The pure tensor of the classes of `p` and `q` goes to the class of the product of their renamings,
and the class of a polynomial in `Y` goes to its class in the incidence ring. -/
theorem exists_locusIncidence_algEquiv :
    letI : Algebra 𝒜 ℬ := (Ideal.quotientMapₐ (idealOf k (Sum.elim x y)) (rename Sum.inr)
      (idealOf_eq_comap_rename (a := Sum.elim x y) (b := y) (g := Sum.inr)
        rfl).le).toAlgebra
    letI : Algebra 𝒜 𝒞 := (Ideal.quotientMapₐ (idealOf k (Sum.elim y z)) (rename Sum.inl)
      (idealOf_eq_comap_rename (a := Sum.elim y z) (b := y) (g := Sum.inl)
        rfl).le).toAlgebra
    haveI : IsScalarTower k 𝒜 ℬ := .of_algHom _
    ∃ Φ : ℬ ⊗[𝒜] 𝒞 ≃ₐ[k] MvPolynomial ((α ⊕ β) ⊕ γ) k ⧸
        (Ideal.map (rename (Sum.inl : α ⊕ β → (α ⊕ β) ⊕ γ)) (idealOf k (Sum.elim x y)) ⊔
          Ideal.map (rename (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr : β ⊕ γ → (α ⊕ β) ⊕ γ))
            (idealOf k (Sum.elim y z))),
      (∀ (p : MvPolynomial (α ⊕ β) k) (q : MvPolynomial (β ⊕ γ) k),
        Φ (Ideal.Quotient.mk _ p ⊗ₜ Ideal.Quotient.mk _ q) = Ideal.Quotient.mk _
          (rename Sum.inl p * rename (Sum.elim (Sum.inl ∘ Sum.inr) Sum.inr) q)) ∧
      ∀ p : MvPolynomial β k, Φ (algebraMap 𝒜 (ℬ ⊗[𝒜] 𝒞) (Ideal.Quotient.mk _ p)) =
        Ideal.Quotient.mk _ (rename (Sum.inl ∘ Sum.inr) p) := by
  -- Term-mode `letI` inlines its values; the same structures are declared locally here.
  let _ : Algebra 𝒜 ℬ := (Ideal.quotientMapₐ (idealOf k (Sum.elim x y)) (rename Sum.inr)
    (idealOf_eq_comap_rename (a := Sum.elim x y) (b := y) (g := Sum.inr)
      rfl).le).toAlgebra
  let _ : Algebra 𝒜 𝒞 := (Ideal.quotientMapₐ (idealOf k (Sum.elim y z)) (rename Sum.inl)
    (idealOf_eq_comap_rename (a := Sum.elim y z) (b := y) (g := Sum.inl)
      rfl).le).toAlgebra
  have : IsScalarTower k 𝒜 ℬ := .of_algHom _
  exact exists_tensorProduct_quotient_algEquiv (idealOf k (Sum.elim x y))
    (idealOf k (Sum.elim y z)) (idealOf k y) (fun _ ↦ rfl) (fun _ ↦ rfl)


-- @@ L246-246 verbatim
end AclGeom
