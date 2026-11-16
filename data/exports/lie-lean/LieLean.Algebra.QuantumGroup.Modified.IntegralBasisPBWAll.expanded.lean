/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.QuantumGroup.Modified.IntegralBasisPBW
import LieLean.Algebra.QuantumGroup.Modified.IntegralPBWGlobalAll


-- @@ L9-36 verbatim
/-!
# Integral PBW and modified triangular bases in every finite type

The four actual divided-power PBW families give Laurent-polynomial bases of their
reduced-word spans. At a longest element they give bases of the original integral
positive subalgebra, not merely bases over the ambient field. The negative-positive
triangular family gives a Laurent-polynomial basis of the existing modified integral form.

## Main results

* `Modified.pbwIntegralBasis` and its `Symm`, `Prime`, `PrimeSymm` variants: bases of
  the integral positive subalgebra, with explicit underlying PBW monomials.
* `Modified.pbwPlusBasisAll`, `Modified.pbwMinusBasisAll`: ambient field bases in
  every finite type, with integral coordinates on the divided-power integral forms.
* `Modified.aTriangularBasisPBWAll`: the resulting basis of `(aForm R).toSubmodule`.

The proofs combine the existing integral span equalities and independence; no
simply-laced, closure, braid-invariance or basis hypothesis is assumed. The coefficient
ring is `ℤ[v,v⁻¹]`, inside the quantum group over `ℚ(v)`. Only the longest-element
conclusions require a finite Coxeter group. The older simply-laced APIs are unchanged.

## References

* G. Lusztig, *Introduction to quantum groups*, 41.1.4(a),(b), 41.1.7(a): integral
  PBW bases. The explicit triangular PBW variant follows the argument of 23.2.2(b),
  using the existing general triangular-basis constructor rather than a canonical basis.
  The canonical-basis congruence of 41.1.6 is a separate assertion, not proved here.
-/


-- @@ L38-38 verbatim
open LieLean Finset

-- @@ L39-39 verbatim
noncomputable section

-- @@ L40-40 verbatim
namespace LieLean.QuantumGroup

-- @@ L41-41 verbatim
local notation "𝕂" => RatFunc ℚ

-- @@ L42-42 verbatim
local notation "𝕧" => (RatFunc.X : RatFunc ℚ)

-- @@ L43-43 verbatim
local notation "𝒜" => LaurentPolynomial ℤ

-- @@ L44-44 verbatim
attribute [local instance] neZero_ratFunc_X

-- @@ L45-46 verbatim
variable {I Y : Type*} [AddCommGroup Y] [DecidableEq I] {D : LusztigCartanDatum I}
  {R : D.RootDatum Y}

-- @@ L47-47 verbatim
namespace Modified

-- @@ L48-48 verbatim
attribute [local instance] laurentAlgebraK laurentAlgebraU laurentTowerU


-- @@ L50-61 verbatim
lemma map_chevalleyIntegral_plus :
    (Algebra.adjoin 𝒜 (⋃ i, Set.range (Ed R i))).map
        ((chevalleyEquiv R 𝕧).restrictScalars 𝒜 : _ →ₐ[𝒜] _) =
      Algebra.adjoin 𝒜 (⋃ i, Set.range fun n ↦ qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i)) := by
  rw [AlgHom.map_adjoin]
  congr 1
  simp only [Set.image_iUnion, ← Set.range_comp]
  congr 1
  funext i
  congr 1
  funext n
  exact chevalley_qDivPow_E (𝕧 ^ D.d i) n i


-- @@ L63-70 verbatim
variable (R) in
/-- The original Chevalley involution restricts to an integral positive-negative equivalence. -/
def chevalleyIntegralPlusMinus :
    (Algebra.adjoin 𝒜 (⋃ i, Set.range (Ed R i))).toSubmodule ≃ₗ[𝒜]
      (Algebra.adjoin 𝒜
        (⋃ i, Set.range fun n ↦ qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i))).toSubmodule :=
  ((((chevalleyEquiv R 𝕧).restrictScalars 𝒜).subalgebraMap _).trans
    (Subalgebra.equivOfEq _ _ map_chevalleyIntegral_plus)).toLinearEquiv


-- @@ L72-74 verbatim
lemma chevalleyIntegralPlusMinus_apply
    (x : (Algebra.adjoin 𝒜 (⋃ i, Set.range (Ed R i))).toSubmodule) :
    (chevalleyIntegralPlusMinus R x : QuantumGroup R 𝕧) = chevalley R 𝕧 x := rfl


-- @@ L76-77 verbatim
variable {W : Type*} [Group W]
  (cs : CoxeterSystem D.cartanMatrix.coxeterMatrix W) {w : List I} (hw : cs.IsReduced w)


-- @@ L79-83 verbatim
/-- The actual `pbwDiv` family is an integral basis of its reduced-word span.
Together with reduced-word span invariance, this is the basis assertion of 41.1.4. -/
def pbwIntegralSpanBasis :
    Module.Basis (Fin w.length → ℕ) 𝒜 (Submodule.span 𝒜 (Set.range (pbwDiv R w))) :=
  Module.Basis.span (linearIndependent_pbwDiv hw)


-- @@ L85-87 verbatim
lemma pbwIntegralSpanBasis_apply (c : Fin w.length → ℕ) :
    (pbwIntegralSpanBasis (R := R) cs hw c : QuantumGroup R 𝕧) = pbwDiv R w c := by
  simp [pbwIntegralSpanBasis]


-- @@ L89-93 verbatim
/-- The actual `pbwDivSymm` family is an integral basis of its reduced-word span.
Together with reduced-word span invariance, this is the basis assertion of 41.1.4. -/
def pbwIntegralSpanBasisSymm :
    Module.Basis (Fin w.length → ℕ) 𝒜 (Submodule.span 𝒜 (Set.range (pbwDivSymm R w))) :=
  Module.Basis.span (linearIndependent_pbwDivSymm hw)


-- @@ L95-97 verbatim
lemma pbwIntegralSpanBasisSymm_apply (c : Fin w.length → ℕ) :
    (pbwIntegralSpanBasisSymm (R := R) cs hw c : QuantumGroup R 𝕧) = pbwDivSymm R w c := by
  simp [pbwIntegralSpanBasisSymm]


-- @@ L99-103 verbatim
/-- The actual `pbwDivPrime` family is an integral basis of its reduced-word span.
Together with reduced-word span invariance, this is the basis assertion of 41.1.4. -/
def pbwIntegralSpanBasisPrime :
    Module.Basis (Fin w.length → ℕ) 𝒜 (Submodule.span 𝒜 (Set.range (pbwDivPrime R w))) :=
  Module.Basis.span (linearIndependent_pbwDivPrime hw)


-- @@ L105-107 verbatim
lemma pbwIntegralSpanBasisPrime_apply (c : Fin w.length → ℕ) :
    (pbwIntegralSpanBasisPrime (R := R) cs hw c : QuantumGroup R 𝕧) = pbwDivPrime R w c := by
  simp [pbwIntegralSpanBasisPrime]


-- @@ L109-113 verbatim
/-- The actual `pbwDivPrimeSymm` family is an integral basis of its reduced-word span.
Together with reduced-word span invariance, this is the basis assertion of 41.1.4. -/
def pbwIntegralSpanBasisPrimeSymm :
    Module.Basis (Fin w.length → ℕ) 𝒜 (Submodule.span 𝒜 (Set.range (pbwDivPrimeSymm R w))) :=
  Module.Basis.span (linearIndependent_pbwDivPrimeSymm hw)


-- @@ L115-118 verbatim
lemma pbwIntegralSpanBasisPrimeSymm_apply (c : Fin w.length → ℕ) :
    (pbwIntegralSpanBasisPrimeSymm (R := R) cs hw c : QuantumGroup R 𝕧) =
      pbwDivPrimeSymm R w c := by
  simp [pbwIntegralSpanBasisPrimeSymm]


-- @@ L120-120 verbatim
variable [Finite W] (hw₀ : cs.wordProd w = cs.longestElement)


-- @@ L122-128 verbatim
/-- The `pbwDiv` basis of the original integral positive subalgebra in every
finite type (41.1.4 and 41.1.7(a)). -/
def pbwIntegralBasis :
    Module.Basis (Fin w.length → ℕ) 𝒜
      (Algebra.adjoin 𝒜 (⋃ i, Set.range (Ed R i))).toSubmodule :=
  (pbwIntegralSpanBasis cs hw).map
    (LinearEquiv.ofEq _ _ (span_pbwDiv_longest_eq_all cs hw hw₀))


-- @@ L130-132 verbatim
lemma pbwIntegralBasis_apply (c : Fin w.length → ℕ) :
    (pbwIntegralBasis (R := R) cs hw hw₀ c : QuantumGroup R 𝕧) = pbwDiv R w c := by
  simp [pbwIntegralBasis, pbwIntegralSpanBasis_apply]


-- @@ L134-140 verbatim
/-- The `pbwDivSymm` basis of the original integral positive subalgebra in every
finite type (41.1.4 and 41.1.7(a)). -/
def pbwIntegralBasisSymm :
    Module.Basis (Fin w.length → ℕ) 𝒜
      (Algebra.adjoin 𝒜 (⋃ i, Set.range (Ed R i))).toSubmodule :=
  (pbwIntegralSpanBasisSymm cs hw).map
    (LinearEquiv.ofEq _ _ (span_pbwDivSymm_longest_eq_all cs hw hw₀))


-- @@ L142-144 verbatim
lemma pbwIntegralBasisSymm_apply (c : Fin w.length → ℕ) :
    (pbwIntegralBasisSymm (R := R) cs hw hw₀ c : QuantumGroup R 𝕧) = pbwDivSymm R w c := by
  simp [pbwIntegralBasisSymm, pbwIntegralSpanBasisSymm_apply]


-- @@ L146-152 verbatim
/-- The `pbwDivPrime` basis of the original integral positive subalgebra in every
finite type (41.1.4 and 41.1.7(a)). -/
def pbwIntegralBasisPrime :
    Module.Basis (Fin w.length → ℕ) 𝒜
      (Algebra.adjoin 𝒜 (⋃ i, Set.range (Ed R i))).toSubmodule :=
  (pbwIntegralSpanBasisPrime cs hw).map
    (LinearEquiv.ofEq _ _ (span_pbwDivPrime_longest_eq_all cs hw hw₀))


-- @@ L154-156 verbatim
lemma pbwIntegralBasisPrime_apply (c : Fin w.length → ℕ) :
    (pbwIntegralBasisPrime (R := R) cs hw hw₀ c : QuantumGroup R 𝕧) = pbwDivPrime R w c := by
  simp [pbwIntegralBasisPrime, pbwIntegralSpanBasisPrime_apply]


-- @@ L158-164 verbatim
/-- The `pbwDivPrimeSymm` basis of the original integral positive subalgebra in every
finite type (41.1.4 and 41.1.7(a)). -/
def pbwIntegralBasisPrimeSymm :
    Module.Basis (Fin w.length → ℕ) 𝒜
      (Algebra.adjoin 𝒜 (⋃ i, Set.range (Ed R i))).toSubmodule :=
  (pbwIntegralSpanBasisPrimeSymm cs hw).map
    (LinearEquiv.ofEq _ _ (span_pbwDivPrimeSymm_longest_eq_all cs hw hw₀))


-- @@ L166-169 verbatim
lemma pbwIntegralBasisPrimeSymm_apply (c : Fin w.length → ℕ) :
    (pbwIntegralBasisPrimeSymm (R := R) cs hw hw₀ c : QuantumGroup R 𝕧) =
      pbwDivPrimeSymm R w c := by
  simp [pbwIntegralBasisPrimeSymm, pbwIntegralSpanBasisPrimeSymm_apply]


-- @@ L171-176 verbatim
/-- The Chevalley image of `pbwDiv` is a Laurent-polynomial basis of the
negative divided-power integral subalgebra in every finite type. -/
def pbwIntegralMinusBasis :
    Module.Basis (Fin w.length → ℕ) 𝒜 (Algebra.adjoin 𝒜
      (⋃ i, Set.range fun n ↦ qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i))).toSubmodule :=
  (pbwIntegralBasis cs hw hw₀).map (chevalleyIntegralPlusMinus R)


-- @@ L178-182 verbatim
lemma pbwIntegralMinusBasis_apply (c : Fin w.length → ℕ) :
    (pbwIntegralMinusBasis (R := R) cs hw hw₀ c : QuantumGroup R 𝕧) =
      chevalley R 𝕧 (pbwDiv R w c) := by
  rw [pbwIntegralMinusBasis, Module.Basis.map_apply, chevalleyIntegralPlusMinus_apply,
    pbwIntegralBasis_apply]


-- @@ L184-189 verbatim
/-- The Chevalley image of `pbwDivSymm` is a Laurent-polynomial basis of the
negative divided-power integral subalgebra in every finite type. -/
def pbwIntegralMinusBasisSymm :
    Module.Basis (Fin w.length → ℕ) 𝒜 (Algebra.adjoin 𝒜
      (⋃ i, Set.range fun n ↦ qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i))).toSubmodule :=
  (pbwIntegralBasisSymm cs hw hw₀).map (chevalleyIntegralPlusMinus R)


-- @@ L191-195 verbatim
lemma pbwIntegralMinusBasisSymm_apply (c : Fin w.length → ℕ) :
    (pbwIntegralMinusBasisSymm (R := R) cs hw hw₀ c : QuantumGroup R 𝕧) =
      chevalley R 𝕧 (pbwDivSymm R w c) := by
  rw [pbwIntegralMinusBasisSymm, Module.Basis.map_apply, chevalleyIntegralPlusMinus_apply,
    pbwIntegralBasisSymm_apply]


-- @@ L197-202 verbatim
/-- The Chevalley image of `pbwDivPrime` is a Laurent-polynomial basis of the
negative divided-power integral subalgebra in every finite type. -/
def pbwIntegralMinusBasisPrime :
    Module.Basis (Fin w.length → ℕ) 𝒜 (Algebra.adjoin 𝒜
      (⋃ i, Set.range fun n ↦ qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i))).toSubmodule :=
  (pbwIntegralBasisPrime cs hw hw₀).map (chevalleyIntegralPlusMinus R)


-- @@ L204-208 verbatim
lemma pbwIntegralMinusBasisPrime_apply (c : Fin w.length → ℕ) :
    (pbwIntegralMinusBasisPrime (R := R) cs hw hw₀ c : QuantumGroup R 𝕧) =
      chevalley R 𝕧 (pbwDivPrime R w c) := by
  rw [pbwIntegralMinusBasisPrime, Module.Basis.map_apply, chevalleyIntegralPlusMinus_apply,
    pbwIntegralBasisPrime_apply]


-- @@ L210-215 verbatim
/-- The Chevalley image of `pbwDivPrimeSymm` is a Laurent-polynomial basis of the
negative divided-power integral subalgebra in every finite type. -/
def pbwIntegralMinusBasisPrimeSymm :
    Module.Basis (Fin w.length → ℕ) 𝒜 (Algebra.adjoin 𝒜
      (⋃ i, Set.range fun n ↦ qDivPow (𝕧 ^ D.d i) n (F R 𝕧 i))).toSubmodule :=
  (pbwIntegralBasisPrimeSymm cs hw hw₀).map (chevalleyIntegralPlusMinus R)


-- @@ L217-221 verbatim
lemma pbwIntegralMinusBasisPrimeSymm_apply (c : Fin w.length → ℕ) :
    (pbwIntegralMinusBasisPrimeSymm (R := R) cs hw hw₀ c : QuantumGroup R 𝕧) =
      chevalley R 𝕧 (pbwDivPrimeSymm R w c) := by
  rw [pbwIntegralMinusBasisPrimeSymm, Module.Basis.map_apply, chevalleyIntegralPlusMinus_apply,
    pbwIntegralBasisPrimeSymm_apply]


-- @@ L223-255 verbatim
include hw hw₀ in
lemma plus_le_span_pbwDiv_all :
    (Algebra.adjoin 𝕂 (Set.range (E R 𝕧))).toSubmodule ≤
      Submodule.span 𝕂 (Set.range (pbwDiv R w)) := by
  let S := Submodule.span 𝕂 (Set.range (pbwDiv R w))
  have h1 : (1 : QuantumGroup R 𝕧) ∈ S :=
    span_laurent_le_span (CoxeterSystem.one_mem_pbwDivSpan (Ta R) (Ed R) Ed_zero w)
  intro x hx
  have hmul : ∀ y ∈ S, x * y ∈ S := by
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨c, rfl⟩ := hy
        have := qDivPow_E_mul_mem_span_pbwDiv_all (R := R) cs hw
          (hw₀ ▸ cs.isLeftDescent_longestElement i) 1
          (Submodule.subset_span ⟨c, rfl⟩)
        rw [A2Integral.qDivPow_one'] at this
        exact span_laurent_le_span this
      | zero => rw [mul_zero]; exact zero_mem _
      | add y z _ _ hy hz => rw [mul_add]; exact add_mem hy hz
      | smul a y _ hy => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hy
    | algebraMap a =>
      intro y hy
      rw [← Algebra.smul_def]
      exact S.smul_mem a hy
    | add x z _ _ hx hz =>
      intro y hy; rw [add_mul]; exact add_mem (hx y hy) (hz y hy)
    | mul x z _ _ hx hz =>
      intro y hy; rw [mul_assoc]; exact hx _ (hz y hy)
  simpa using hmul 1 h1


-- @@ L257-286 verbatim
include hw hw₀ in
/-- **The field PBW basis of `U⁺` with integral monomials** in every finite type:
the divided-power PBW monomials of a reduced expression of `w₀`. -/
def pbwPlusBasisAll :
    Module.Basis (Fin w.length → ℕ) 𝕂 (Algebra.adjoin 𝕂 (Set.range (E R 𝕧))) :=
  let v : (Fin w.length → ℕ) → Algebra.adjoin 𝕂 (Set.range (E R 𝕧)) :=
    fun c ↦ ⟨pbwDiv R w c, pbwDiv_mem_plus cs hw c⟩
  Module.Basis.mk (v := v)
    (by
      refine LinearIndependent.of_comp
        (Algebra.adjoin 𝕂 (Set.range (E R 𝕧))).toSubmodule.subtype ?_
      have hli := linearIndependent_pbwMonomial_of_isReduced (R := R) ratFunc_X_not_root hw
      have hu := hli.units_smul fun c ↦ Units.mk0
        (∏ t : Fin w.length, (qFactorial (𝕧 ^ D.d w[t]) (c t))⁻¹)
        (prod_ne_zero_iff.2 fun t _ ↦ inv_ne_zero (qFactorial_vd_ne_zero _ _))
      convert hu using 1
      ext c
      simp [v, pbwDiv_eq_smul])
    (by
      rintro ⟨x, hx⟩ -
      have hx' := plus_le_span_pbwDiv_all (R := R) cs hw hw₀ hx
      have hmap : (Submodule.span 𝕂 (Set.range v)).map
          (Algebra.adjoin 𝕂 (Set.range (E R 𝕧))).toSubmodule.subtype =
            Submodule.span 𝕂 (Set.range (pbwDiv R w)) := by
        rw [Submodule.map_span, ← Set.range_comp]
        rfl
      rw [← hmap] at hx'
      obtain ⟨y, hy, hyx⟩ := hx'
      rwa [show (⟨x, hx⟩ : Algebra.adjoin 𝕂 (Set.range (E R 𝕧))) = y from
        Subtype.ext hyx.symm])


-- @@ L288-290 verbatim
lemma pbwPlusBasisAll_apply (c : Fin w.length → ℕ) :
    (pbwPlusBasisAll (R := R) cs hw hw₀ c : QuantumGroup R 𝕧) = pbwDiv R w c := by
  simp [pbwPlusBasisAll]


-- @@ L292-297 verbatim
include hw hw₀ in
/-- **The field PBW basis of `U⁻` with integral monomials**: the images of
`pbwPlusBasisAll` under the Chevalley involution. -/
def pbwMinusBasisAll :
    Module.Basis (Fin w.length → ℕ) 𝕂 (Algebra.adjoin 𝕂 (Set.range (F R 𝕧))) :=
  (pbwPlusBasisAll cs hw hw₀).map (chevalleyPlusMinus R)


-- @@ L299-301 verbatim
lemma pbwMinusBasisAll_apply (c : Fin w.length → ℕ) :
    (pbwMinusBasisAll (R := R) cs hw hw₀ c : QuantumGroup R 𝕧) = chevalley R 𝕧 (pbwDiv R w c) := by
  rw [pbwMinusBasisAll, Module.Basis.map_apply, chevalleyPlusMinus_apply, pbwPlusBasisAll_apply]


-- @@ L303-345 verbatim
include hw hw₀ in
/-- **A triangular `𝒜`-basis of `𝒜U̇`** in every finite type ([Lus] 23.2.2 (b) with the
integral PBW bases of [Lus] 41.1.7): for a reduced expression of `w₀`, the elements
`ω(E_c) 1_λ E_{c'}` (`E_c` the integral PBW monomials, `ω` the Chevalley involution) form an
`𝒜`-basis of `𝒜U̇`. -/
def aTriangularBasisPBWAll :
    Module.Basis ((Fin w.length → ℕ) × (Y →+ ℤ) × (Fin w.length → ℕ)) 𝒜
      (aForm R).toSubmodule :=
  have hp : ∀ c, (pbwPlusBasisAll (R := R) cs hw hw₀ c : QuantumGroup R 𝕧) ∈
      adWeightSpace R 𝕧 (pbwWt R w c) := fun c ↦ by
    rw [pbwPlusBasisAll_apply]; exact pbwDiv_mem_adWeightSpace w c
  have hm : ∀ c, (pbwMinusBasisAll (R := R) cs hw hw₀ c : QuantumGroup R 𝕧) ∈
      adWeightSpace R 𝕧 (-pbwWt R w c) := fun c ↦ by
    rw [pbwMinusBasisAll_apply, ← wt_omegaAut (R := R)]
    exact map_mem_adWeightSpace (omegaAut R) (pbwDiv_mem_adWeightSpace w c)
  have haP : ∀ c, pbwDiv R w c ∈ aPlus R := fun c ↦ by
    simpa using pbwDiv_mem_aPlus (R := R) w [] (by simpa using hw) c
  have hspan : ∀ x ∈ aPlus R, x ∈ Submodule.span 𝒜 (Set.range fun c ↦
      (pbwPlusBasisAll (R := R) cs hw hw₀ c : QuantumGroup R 𝕧)) := fun x hx ↦ by
    have e : (Set.range fun c ↦ (pbwPlusBasisAll (R := R) cs hw hw₀ c : QuantumGroup R 𝕧)) =
        Set.range (pbwDiv R w) := by
      congr 1
      funext c
      exact pbwPlusBasisAll_apply (R := R) cs hw hw₀ c
    rw [e]
    have hx' : x ∈ (aPlus R : Set (QuantumGroup R 𝕧)) := hx
    rw [← coe_span_pbwDiv_longest_all (R := R) cs hw hw₀] at hx'
    exact hx'
  aTriangularBasis (pbwMinusBasisAll cs hw hw₀) (pbwPlusBasisAll cs hw hw₀) (pbwWt R w)
    (pbwWt R w) hm hp
    (fun c ↦ by rw [pbwMinusBasisAll_apply]; exact chevalley_mem_aMinus (haP c))
    (fun c ↦ by rw [pbwPlusBasisAll_apply]; exact haP c)
    (fun w' c ↦ by
      rw [pbwMinusBasisAll, Module.Basis.map_repr, LinearEquiv.trans_apply]
      have e : (chevalleyPlusMinus R).symm ⟨fPow R w', fPow_mem_minus w'⟩ =
          ⟨ePow R w', ePow_mem_plus w'⟩ := by
        rw [LinearEquiv.symm_apply_eq]
        apply Subtype.ext
        rw [chevalleyPlusMinus_apply]
        exact (chevalley_ePow w').symm
      rw [e]
      exact isLaurent_repr_of_mem_span _ (hspan _ (ePow_mem_aPlus w')) c)
    (fun w' c ↦ isLaurent_repr_of_mem_span _ (hspan _ (ePow_mem_aPlus w')) c)


-- @@ L347-357 verbatim
lemma aTriangularBasisPBWAll_apply (t : (Fin w.length → ℕ) × (Y →+ ℤ) × (Fin w.length → ℕ)) :
    (aTriangularBasisPBWAll (R := R) cs hw hw₀ t : Modified R 𝕧) =
      elt (t.2.1 - pbwWt R w t.1) (t.2.1 - pbwWt R w t.2.2)
        (chevalley R 𝕧 (pbwDiv R w t.1) * pbwDiv R w t.2.2) (by
          have := mul_mem_adWeightSpace
            (map_mem_adWeightSpace (omegaAut R) (pbwDiv_mem_adWeightSpace (R := R) w t.1))
            (pbwDiv_mem_adWeightSpace (R := R) w t.2.2)
          rw [wt_omegaAut] at this
          convert this using 2 <;> first | rfl | abel) := by
  rw [aTriangularBasisPBWAll, aTriangularBasis_apply, triFun]
  exact elt_congr (by rw [pbwMinusBasisAll_apply, pbwPlusBasisAll_apply]) _ _


-- @@ L359-359 verbatim
end Modified

-- @@ L360-360 verbatim
end LieLean.QuantumGroup
