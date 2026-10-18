/-
Copyright (c) 2026 The genl contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The genl contributors
-/
import Genl.Curves.Theory
import Heights.Curve.CondDivisor
import Heights.Curve.Compactness
import Belyi.CurveField.NoncriticalBridge


-- @@ L11-34 verbatim
/-!
# Noncritical Belyi maps and the compactness argument

For the height theory `Genl.Curves.theory` of curves over number fields, this file constructs
the output `Genl.HeightTheory.BelyiDescent` of the second half of the proof of [GenEll],
Theorem 2.1 (pp. 13–14): given a divisor free hyperbolic curve `X` on which the inequality
`ht_{ω_X} ≤ (1 + ε) log-diff_X + C` fails on `X(ℚ̄)^{=d}` for every `C`,

1. choose points `x_n` of degree `d` with `ht_{ω_X}(x_n) > (1 + ε) log-diff_X(x_n) + n`;
2. by compactness of the local points at `2` and `∞` (`Heights.Curve.exists_subseq_bounded`)
   pass to a subsequence converging at every embedding of `ℚ(x_n)` into `ℚ̄_2` and `ℂ`, with
   finitely many limit places `T`;
3. choose a **noncritical Belyi map** `φ` whose cusps avoid `T`
   (`Belyi.CurveField.exists_isBelyi_notMem_belyiCusps`, [NCB] Theorem 2.5); then the values
   `φ(x_n)` stay in a compact domain of `ℙ¹ ∖ {0, 1, ∞}` at `2` and `∞`, i.e. in a compactly
   bounded subset of the tripod;
4. compare heights (the Belyi relation `K_X + E ~ φ^* (K_ℙ + C)`), log-differents and
   log-conductors (the tower inequality for `log-diff + log-cond` of number fields and
   Proposition 1.6 of [GenEll] for the cusp divisor `E`), and `ht_E ≲ q ht_{ω_X}` for
   `q > deg E / deg ω_X`.

The map `φ : U_X(ℚ̄) → U_ℙ(ℚ̄)` on points sends `x` to the point of the tripod with coordinate
`φ(x)` (`Genl.Curves.belyiPt`).
-/


-- @@ L36-36 verbatim
namespace Genl.Curves


-- @@ L38-38 verbatim
open Belyi.CurveField Belyi.CurveField.Divisor Heights.Curve Heights.Absolute Filter

-- @@ L39-39 verbatim
open scoped IntermediateField


-- @@ L41-41 verbatim
/-! ### Points of the tripod given by their coordinate -/


-- @@ L43-45 verbatim
/-- The point of the tripod with coordinate `z ∈ ℚ̄ ∖ {0, 1}`. -/
noncomputable def tripodPt (z : Qbar) (h0 : z ≠ 0) (h1 : z ≠ 1) : tripod.Pt :=
  (QbarPoint.equivTripod tgen_isRationalGenerator).symm ⟨z, h0, h1⟩


-- @@ L47-52 verbatim
theorem eval_tripodPt (z : Qbar) (h0 : z ≠ 0) (h1 : z ≠ 1) :
    (tripodPt z h0 h1).1.eval tgen (tgen_mem _) = z := by
  have h := congrArg Subtype.val
    ((QbarPoint.equivTripod tgen_isRationalGenerator).apply_symm_apply ⟨z, h0, h1⟩)
  rw [QbarPoint.equivTripod_apply] at h
  exact h


-- @@ L54-57 verbatim
theorem fieldOf_tripodPt (z : Qbar) (h0 : z ≠ 0) (h1 : z ≠ 1) :
    (tripodPt z h0 h1).1.fieldOf = ℚ⟮z⟯ :=
  (QbarPoint.fieldOf_eq_adjoin tgen_isRationalGenerator (tripodPt z h0 h1).1 (tgen_mem _)).trans
    (by rw [eval_tripodPt])


-- @@ L59-61 verbatim
theorem coe_tripodValue_tripodPt (z : Qbar) (h0 : z ≠ 0) (h1 : z ≠ 1) :
    ((tripodValue (tripodPt z h0 h1) : (tripodPt z h0 h1).1.fieldOf) : Qbar) = z :=
  eval_tripodPt z h0 h1


-- @@ L63-65 verbatim
theorem tupleHeight_tgen_tripodPt (z : Qbar) (h0 : z ≠ 0) (h1 : z ≠ 1) :
    tupleHeight (K := tripodK) ![1, tgen] (tripodPt z h0 h1).1 = logHeight ![1, z] :=
  (tupleHeight_pair_one_of_mem (tripodPt z h0 h1).1 (tgen_mem _)).trans (by rw [eval_tripodPt])


-- @@ L67-67 verbatim
/-! ### Extending embeddings of number fields -/


-- @@ L69-79 verbatim
/-- An embedding of a subfield `F₁ ⊆ F₂ ⊆ ℚ̄` into an algebraically closed field extends to
`F₂`. -/
theorem exists_extend_ringHom {F₁ F₂ : IntermediateField ℚ Qbar} (h : F₁ ≤ F₂)
    {E : Type*} [Field E] [IsAlgClosed E] (τ : F₁ →+* E) :
    ∃ τ' : F₂ →+* E, ∀ a : F₁, τ' (IntermediateField.inclusion h a) = τ a := by
  letI : Algebra F₁ E := τ.toAlgebra
  haveI : Algebra.IsAlgebraic F₁ Qbar := Algebra.IsAlgebraic.tower_top (K := ℚ) F₁
  let ψ : Qbar →ₐ[F₁] E := IsAlgClosed.lift
  refine ⟨ψ.toRingHom.comp F₂.val.toRingHom, fun a => ?_⟩
  have := ψ.commutes a
  exact this


-- @@ L81-81 verbatim
/-! ### The tripod: `ht_{ω_ℙ(C)} ≈ h(λ)` -/


-- @@ L83-87 verbatim
theorem tgen_isBelyi : IsBelyi tgen :=
  ⟨tgen_isRationalGenerator.transcendental, fun P hP => by
    rw [ramIdx_eq_one_of_adjoin_eq_top tgen_isRationalGenerator.transcendental
      tgen_isRationalGenerator.adjoin_eq_top] at hP
    exact absurd hP (lt_irrefl 1)⟩


-- @@ L89-97 verbatim
theorem divD_tripod : tripod.divD = cuspDivisor tgen := by
  classical
  rw [Curve.divD, cuspDivisor_eq_sum]
  congr 1
  ext P
  rw [Set.Finite.mem_toFinset]
  change P ∈ tripodPlaces tgen ↔ _
  rw [mem_tripodPlaces_iff_ord tgen_isRationalGenerator]
  rfl


-- @@ L99-119 verbatim
/-- The height `ht_{ω_ℙ(C)}` of the tripod is the height of the coordinate, up to `O(1)`. -/
theorem divHeight_logCanon_tripod :
    ∃ C, ∀ y : QbarPoint tripod.K,
      |divHeight tripod.logCanon y - tupleHeight ![1, tgen] y| ≤ C := by
  obtain ⟨r, hr, hcan⟩ := exists_canonicalDiv_eq_add_div tripod.sep_transcendental
    tgen_isRationalGenerator.transcendental
  have hr₂ : tgen * (tgen - 1) ≠ 0 := mul_ne_zero tgen_isRationalGenerator.ne_zero
    tgen_isRationalGenerator.sub_one.ne_zero
  have heq : tripod.logCanon = (polarDivisor tgen + div (tgen * (tgen - 1))) + div r := by
    rw [Curve.logCanon, Curve.canon, divD_tripod, hcan, add_right_comm,
      canonicalDiv_add_cuspDivisor tgen_isBelyi, add_comm (div _)]
  obtain ⟨C₁, hC₁⟩ := divHeight_add_div (polarDivisor tgen + div (tgen * (tgen - 1))) hr
  obtain ⟨C₂, hC₂⟩ := divHeight_add_div (polarDivisor tgen) hr₂
  obtain ⟨C₃, hC₃⟩ := divHeight_polar tgen
  refine ⟨C₁ + C₂ + C₃, fun y => ?_⟩
  rw [heq]
  have h1 := hC₁ y
  have h2 := hC₂ y
  have h3 := hC₃ y
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]


-- @@ L121-121 verbatim
/-! ### Belyi functions and their cusps -/


-- @@ L123-123 verbatim
section Cusps


-- @@ L125-125 verbatim
variable {K : Type*} [Field K] [CharZero K] [IsCurveField K]


-- @@ L127-138 verbatim
theorem mem_of_notMem_belyiCusps {φ : K} {P : Place K} (hP : P ∉ belyiCusps φ) :
    φ ∈ P.1 ∧ φ⁻¹ ∈ P.1 ∧ (1 - φ)⁻¹ ∈ P.1 := by
  simp only [belyiCusps, Set.mem_setOf_eq, not_or, not_lt, not_not] at hP
  obtain ⟨hc0, hc1⟩ := hP
  have hm : φ ∈ P.1 := P.mem_of_ord_nonneg hc0.ge
  have hm1 : φ - 1 ∈ P.1 := sub_mem hm P.1.one_mem
  have h1' := P.ord_nonneg_of_mem hm1
  refine ⟨hm, P.mem_of_ord_nonneg ?_, ?_⟩
  · rw [Place.ord_inv]; omega
  · rw [← neg_sub, inv_neg]
    refine neg_mem (P.mem_of_ord_nonneg ?_)
    rw [Place.ord_inv]; omega


-- @@ L140-156 verbatim
theorem notMem_belyiCusps_of_eval (x : QbarPoint K) {φ : K} (hφ : φ ∈ x.P.1)
    (h0 : x.eval φ hφ ≠ 0) (h1 : x.eval φ hφ ≠ 1) : x.P ∉ belyiCusps φ := by
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    exact h0 x.eval_zero
  rintro (h | h)
  · have := x.P.ord_nonneg_of_mem hφ
    exact h0 ((x.eval_eq_zero_iff hφ hφ0).mpr (by omega))
  · have hm : φ - 1 ∈ x.P.1 := sub_mem hφ x.P.1.one_mem
    have hne : φ - 1 ≠ 0 := by
      intro h'
      rw [sub_eq_zero] at h'
      subst h'
      exact h1 x.eval_one
    have := (x.eval_eq_zero_iff hm hne).mpr h
    rw [x.eval_sub hφ x.P.1.one_mem, x.eval_one, sub_eq_zero] at this
    exact h1 this


-- @@ L158-161 verbatim
theorem cuspDivisor_nonneg (φ : K) : 0 ≤ cuspDivisor φ := fun P => by
  by_cases h : P ∈ belyiCusps φ
  · rw [cuspDivisor_apply_of_mem h]; simp
  · rw [cuspDivisor_apply_of_notMem h]; simp


-- @@ L163-165 verbatim
theorem deg_cuspDivisor_nonneg (φ : K) : 0 ≤ (cuspDivisor φ).deg := by
  rw [deg_cuspDivisor]
  exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _


-- @@ L167-167 verbatim
end Cusps


-- @@ L169-169 verbatim
/-! ### The map on points induced by a function -/


-- @@ L171-171 verbatim
variable (X : Curve)


-- @@ L173-179 verbatim
open Classical in
/-- The map `x ↦ φ(x)` from the points of `X` to the points of the tripod (with the junk value
`2` at the points where `φ(x) ∈ {0, 1, ∞}`). -/
noncomputable def belyiPt (φ : X.K) (x : X.Pt) : tripod.Pt :=
  if h : ∃ hφ : φ ∈ x.1.P.1, x.1.eval φ hφ ≠ 0 ∧ x.1.eval φ hφ ≠ 1 then
    tripodPt (x.1.eval φ h.1) h.2.1 h.2.2
  else tripodPt 2 two_ne_zero (by norm_num)


-- @@ L181-181 verbatim
variable {X}


-- @@ L183-185 verbatim
theorem belyiPt_eq {φ : X.K} {x : X.Pt} (hφ : φ ∈ x.1.P.1) (h0 : x.1.eval φ hφ ≠ 0)
    (h1 : x.1.eval φ hφ ≠ 1) : belyiPt X φ x = tripodPt (x.1.eval φ hφ) h0 h1 := by
  rw [belyiPt, dif_pos ⟨hφ, h0, h1⟩]


-- @@ L187-190 verbatim
theorem fieldOf_belyiPt_le {φ : X.K} {x : X.Pt} (hφ : φ ∈ x.1.P.1) (h0 : x.1.eval φ hφ ≠ 0)
    (h1 : x.1.eval φ hφ ≠ 1) : (belyiPt X φ x).1.fieldOf ≤ x.1.fieldOf := by
  rw [belyiPt_eq hφ h0 h1, fieldOf_tripodPt]
  exact IntermediateField.adjoin_simple_le_iff.mpr (x.1.eval_mem_fieldOf hφ)


-- @@ L192-197 verbatim
theorem eval_belyiPt {φ : X.K} {x : X.Pt} (hφ : φ ∈ x.1.P.1) (h0 : x.1.eval φ hφ ≠ 0)
    (h1 : x.1.eval φ hφ ≠ 1) : (belyiPt X φ x).1.eval tgen (tgen_mem _) = x.1.eval φ hφ := by
  have h := belyiPt_eq hφ h0 h1
  generalize belyiPt X φ x = y at h ⊢
  subst h
  exact eval_tripodPt _ _ _


-- @@ L199-202 verbatim
theorem coe_tripodValue_belyiPt {φ : X.K} {x : X.Pt} (hφ : φ ∈ x.1.P.1)
    (h0 : x.1.eval φ hφ ≠ 0) (h1 : x.1.eval φ hφ ≠ 1) :
    ((tripodValue (belyiPt X φ x) : (belyiPt X φ x).1.fieldOf) : Qbar) = x.1.eval φ hφ :=
  eval_belyiPt hφ h0 h1


-- @@ L204-208 verbatim
theorem tupleHeight_belyiPt {φ : X.K} {x : X.Pt} (hφ : φ ∈ x.1.P.1) (h0 : x.1.eval φ hφ ≠ 0)
    (h1 : x.1.eval φ hφ ≠ 1) :
    tupleHeight ![1, tgen] (belyiPt X φ x).1 = tupleHeight ![1, φ] x.1 := by
  rw [tupleHeight_pair_one_of_mem _ (tgen_mem _), tupleHeight_pair_one_of_mem _ hφ,
    eval_belyiPt hφ h0 h1]


-- @@ L210-210 verbatim
/-! ### The comparisons along a Belyi function -/


-- @@ L212-240 verbatim
/-- **Heights along a Belyi function** ([GenEll], p. 14): for a divisor free curve `X` and a
Belyi function `φ` with cusp divisor `E`, `ht_{ω_X} + ht_E ≈ h(φ)` (from the Belyi relation
`K_X + E ~ (φ)_∞`). -/
theorem divHeight_logCanon_add_cusp (hD : X.D = ∅) {φ : X.K} (hφ : IsBelyi φ) :
    ∃ C, ∀ x : QbarPoint X.K, |divHeight X.logCanon x + divHeight (cuspDivisor φ) x -
      tupleHeight ![1, φ] x| ≤ C := by
  obtain ⟨r, hr, hcan⟩ := exists_canonicalDiv_eq_add_div X.sep_transcendental hφ.1
  have hφ0 : φ ≠ 0 := ne_zero_of_transcendental hφ.1
  have hφ1 : φ - 1 ≠ 0 := by
    intro h
    rw [sub_eq_zero] at h
    exact hφ.1 (h ▸ isAlgebraic_one)
  have hr₂ : φ * (φ - 1) ≠ 0 := mul_ne_zero hφ0 hφ1
  have hdivD : X.divD = 0 := by rw [Curve.divD, hD, Finset.sum_empty]
  have heq : X.logCanon + cuspDivisor φ = (polarDivisor φ + div (φ * (φ - 1))) + div r := by
    rw [Curve.logCanon, Curve.canon, hdivD, add_zero, hcan, add_right_comm,
      canonicalDiv_add_cuspDivisor hφ, add_comm (div _)]
  obtain ⟨C₀, hC₀⟩ := divHeight_add X.logCanon (cuspDivisor φ)
  obtain ⟨C₁, hC₁⟩ := divHeight_add_div (polarDivisor φ + div (φ * (φ - 1))) hr
  obtain ⟨C₂, hC₂⟩ := divHeight_add_div (polarDivisor φ) hr₂
  obtain ⟨C₃, hC₃⟩ := divHeight_polar φ
  refine ⟨C₀ + C₁ + C₂ + C₃, fun x => ?_⟩
  have h0 := hC₀ x
  have h1 := hC₁ x
  have h2 := hC₂ x
  have h3 := hC₃ x
  rw [heq] at h0
  rw [abs_le] at h0 h1 h2 h3 ⊢
  constructor <;> linarith [h0.1, h0.2, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2]


-- @@ L242-243 verbatim
/-- Primes carry their primality as an instance (local). -/
local instance factPrimes' (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩


-- @@ L245-439 expanded
open Classical in
/-- **The second half of the proof of [GenEll], Theorem 2.1** for the height theory of curves
over number fields: noncritical Belyi maps and the compactness argument. -/
theorem nonempty_belyiDescent (X : Curve) (hX : theory.Hyperbolic X) (hD : theory.DivisorFree X)
    (d : ℕ) (ε : ℝ)
    (hfail : ¬(DiscrepancyLE (theory.htCan X) ((1 + ε) • theory.logDiff X) (theory.ptEQ X d))) :
    Nonempty (theory.BelyiDescent X d ε) :=
  by
  change 0 < X.logCanon.deg at hX
  change X.D = ∅ at hD
  have hseq :
    ∀ n : ℕ, ∃ x : X.Pt, x.1.deg = d ∧ (1 + ε) * logDiff x.1 + n < divHeight X.logCanon x.1 :=
    by
    intro n
    by_contra h
    push Not at h
    refine hfail ⟨n, fun x hx => ?_⟩
    change divHeight X.logCanon x.1 ≤ (1 + ε) * logDiff x.1 + n
    exact h x hx
  choose xs hxdeg hxfail using hseq
  set V : Finset Nat.Primes := {⟨2, Nat.prime_two⟩} with hV
  obtain ⟨Dn, hDn, T, hT⟩ :=
    exists_subseq_bounded V (fun n => (xs n).1)
      (fun n => (hxdeg n).le)
        -- 3. a noncritical Belyi map
        
  obtain ⟨φ, hφB, hφT⟩ := exists_isBelyi_notMem_belyiCusps T
  have hφtr := hφB.1
  have hφ0 : φ ≠ 0 := ne_zero_of_transcendental hφtr
  have hφ1 : φ ≠ 1 := by
    rintro rfl
    exact hφtr isAlgebraic_one
  have hTφ : ∀ P ∈ T, φ ∈ P.1 ∧ φ⁻¹ ∈ P.1 ∧ (φ - 1)⁻¹ ∈ P.1 :=
    by
    intro P hP
    obtain ⟨h1, h2, h3⟩ := mem_of_notMem_belyiCusps (hφT P hP)
    refine ⟨h1, h2, ?_⟩
    rw [← neg_sub, inv_neg]
    exact neg_mem h3
  obtain ⟨C, hC⟩ := hT φ hφ0 hφ1 hTφ
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hC
  set Ξ : Set X.Pt := {x | ∃ n, N ≤ n ∧ x = xs (Dn n)} with hΞ
  have hgood : ∀ x ∈ Ξ, ∃ hφ : φ ∈ x.1.P.1, x.1.eval φ hφ ≠ 0 ∧ x.1.eval φ hφ ≠ 1 :=
    by
    rintro x ⟨n, hn, rfl⟩
    obtain ⟨hφ, h0, h1, -⟩ := hN n hn
    refine ⟨hφ, fun h => h0 (Subtype.ext ?_), fun h => h1 (Subtype.ext ?_)⟩
    · exact h
    · exact h
  set E : Finset (Place X.K) := (finite_belyiCusps φ).toFinset with hE
  have hmemE : ∀ P, P ∈ E ↔ P ∈ belyiCusps φ := fun P => Set.Finite.mem_toFinset _
  have hEne : E.Nonempty := by
    obtain ⟨P, hP⟩ := Place.exists_notMem hφtr
    refine ⟨P, (hmemE P).mpr (Or.inl ?_)⟩
    exact ((P.ord_neg_iff).mpr hP).ne
  obtain ⟨GE, hSGE, hGE⟩ :=
    exists_finset_adjoin_eq_coordRing E hEne {φ, φ⁻¹, (1 - φ)⁻¹}
      (by
        intro s hs P hP
        have h := mem_of_notMem_belyiCusps (fun h => hP ((hmemE P).mpr h))
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rcases hs with rfl | rfl | rfl
        · exact h.1
        · exact h.2.1
        · exact h.2.2)
  have hGEreg : ∀ P : Place X.K, P ∉ belyiCusps φ → ∀ g ∈ GE, g ∈ P.1 :=
    by
    intro P hP g hg
    have : g ∈ coordRing E := by
      rw [← hGE]
      exact Algebra.subset_adjoin hg
    exact
      this P fun h =>
        hP
          ((hmemE P).mp h)
            -- heights along `φ`
            
  obtain ⟨Ch, hCh⟩ := divHeight_logCanon_add_cusp hD hφB
  obtain ⟨Ct, hCt⟩ := divHeight_logCanon_tripod
  obtain ⟨Cc, hCc⟩ :=
    logCondOf_le_divHeight (cuspDivisor φ) (cuspDivisor_nonneg φ) GE fun P hP =>
      hGEreg P fun h => by
        rw [cuspDivisor_apply_of_mem h] at hP
        exact one_ne_zero hP
  set q : ℝ := ((cuspDivisor φ).deg : ℝ) / X.logCanon.deg + 1 with hq
  have hXR : (0 : ℝ) < X.logCanon.deg := by exact_mod_cast hX
  have hEdeg : (0 : ℝ) ≤ (cuspDivisor φ).deg := by exact_mod_cast deg_cuspDivisor_nonneg φ
  obtain ⟨Cq, hCq⟩ :=
    divHeight_le_mul (A := cuspDivisor φ) hX (q := q)
      (by
        rw [hq, add_mul, div_mul_cancel₀ _ hXR.ne', one_mul]
        linarith)
  refine
    ⟨{  Ξ := Ξ
        φ := belyiPt X φ
        K := ⟨V, Finset.mem_singleton_self _, C⟩
        d' := d
        htE := fun x => divHeight (cuspDivisor φ) x.1
        logCondE := fun x => logCondOf GE x.1
        q := q
        q_pos := by positivity
        subset := by
          rintro x ⟨n, -, rfl⟩
          exact hxdeg (Dn n)
        unbounded := by
          intro C'
          refine ⟨xs (Dn (max N ⌈C'⌉₊)), ⟨_, le_max_left _ _, rfl⟩, ?_⟩
          have h1 := hxfail (Dn (max N ⌈C'⌉₊))
          have h2 : C' ≤ (Dn (max N ⌈C'⌉₊) : ℝ) :=
            by
            refine (Nat.le_ceil C').trans ?_
            exact_mod_cast (le_max_right N ⌈C'⌉₊).trans (hDn.id_le _)
          change (1 + ε) * logDiff _ + C' < divHeight X.logCanon _
          linarith
        mapsTo := ?mapsTo
        htCan_equiv := ?htCan
        logDiff_comp_le := ?logDiff
        logCondE_le :=
          ⟨Cc, fun x hx => by
            obtain ⟨hφ, h0, h1⟩ := hgood x hx
            exact hCc x.1 (hGEreg _ (notMem_belyiCusps_of_eval x.1 hφ h0 h1))⟩
        htE_le := ⟨Cq, fun x _ => hCq x.1⟩ }⟩
  case mapsTo =>
    rintro x ⟨n, hn, rfl⟩
    obtain ⟨hφ, h0, h1, hσ, hτ⟩ := hN n hn
    have h0' : (xs (Dn n)).1.eval φ hφ ≠ 0 := fun h => h0 (Subtype.ext h)
    have h1' : (xs (Dn n)).1.eval φ hφ ≠ 1 := fun h => h1 (Subtype.ext h)
    have hle := fieldOf_belyiPt_le hφ h0' h1'
    have hval :
      IntermediateField.inclusion hle (tripodValue (belyiPt X φ (xs (Dn n)))) =
        evalF (xs (Dn n)).1 ⟨φ, hφ⟩ :=
      Subtype.ext (coe_tripodValue_belyiPt hφ h0' h1')
    refine ⟨⟨fun p hp τ => ?_, fun σ => ?_⟩, ?_⟩
    · obtain ⟨τ', hτ'⟩ := exists_extend_ringHom hle τ
      rw [← hτ', hval]
      exact hτ p hp τ'
    · obtain ⟨σ', hσ'⟩ := exists_extend_ringHom hle σ
      rw [← hσ', hval]
      exact hσ σ'
    · change (belyiPt X φ (xs (Dn n))).1.deg ≤ d
      rw [← hxdeg (Dn n)]
      exact IntermediateField.finrank_le_of_le_right hle
  case
    htCan =>
    have key :
      ∀ x ∈ Ξ,
        |divHeight X.logCanon x.1 -
              (divHeight tripod.logCanon (belyiPt X φ x).1 - divHeight (cuspDivisor φ) x.1)| ≤
          Ch + Ct :=
      by
      intro x hx
      obtain ⟨hφ, h0, h1⟩ := hgood x hx
      have e := tupleHeight_belyiPt hφ h0 h1
      have a := hCh x.1
      have b := hCt (belyiPt X φ x).1
      rw [e] at b
      rw [abs_le] at a b ⊢
      constructor <;> linarith [a.1, a.2, b.1, b.2]
    refine ⟨⟨Ch + Ct, fun x hx => ?_⟩, ⟨Ch + Ct, fun x hx => ?_⟩⟩
    · have := (abs_le.mp (key x hx)).2
      change
        divHeight X.logCanon x.1 ≤
          (divHeight tripod.logCanon (belyiPt X φ x).1 - divHeight (cuspDivisor φ) x.1) + (Ch + Ct)
      linarith
    · have := (abs_le.mp (key x hx)).1
      change
        (divHeight tripod.logCanon (belyiPt X φ x).1 - divHeight (cuspDivisor φ) x.1) ≤
          divHeight X.logCanon x.1 + (Ch + Ct)
      linarith
  case logDiff =>
    refine ⟨0, fun x hx => ?_⟩
    obtain ⟨hφ, h0, h1⟩ := hgood x hx
    have hGx : ∀ g ∈ GE, g ∈ x.1.P.1 := hGEreg _ (notMem_belyiCusps_of_eval x.1 hφ h0 h1)
    have hle := fieldOf_belyiPt_le hφ h0 h1
    have hDne : tripod.D.Nonempty := by
      rw [← Finset.card_pos]
      change 0 < (tripodPlaces tgen).card
      rw [card_tripodPlaces tgen_isRationalGenerator]
      norm_num
    have hGy : ∀ g ∈ tripod.G, g ∈ (belyiPt X φ x).1.P.1 :=
      by
      intro g hg
      have : g ∈ coordRing tripod.D := by
        rw [← tripod.G_spec hDne]
        exact Algebra.subset_adjoin hg
      exact this _ (belyiPt X φ x).2
    change
      logDiff (belyiPt X φ x).1 +
          (if tripod.D = ∅ then 0 else logCondOf tripod.G (belyiPt X φ x).1) ≤
        (logDiff x.1 + logCondOf GE x.1) + 0
    rw [if_neg hDne.ne_empty, add_zero, logCondOf_eq_cond _ _ hGy, logCondOf_eq_cond _ _ hGx]
    letI : Algebra (belyiPt X φ x).1.fieldOf x.1.fieldOf :=
      (IntermediateField.inclusion hle).toRingHom.toAlgebra
    refine Heights.Different.logDisc_add_cond_le _ _ ?_
    intro a ha
    simp only [Finset.mem_image, Finset.mem_attach, true_and] at ha
    obtain ⟨b, ⟨⟨g, hg⟩, rfl⟩, rfl⟩ := ha
    have hg' : g = tgen ∨ g = tgen⁻¹ ∨ g = (1 - tgen)⁻¹ :=
      by
      change g ∈ ({tgen, tgen⁻¹, (1 - tgen)⁻¹} : Finset tripodK) at hg
      simpa using hg
    rcases hg' with rfl | rfl | rfl
    · simp only [Finset.mem_image, Finset.mem_attach, true_and]
      refine ⟨⟨φ, hSGE (by simp)⟩, Subtype.ext ?_⟩
      change x.1.eval φ _ = (belyiPt X φ x).1.eval tgen _
      exact (eval_belyiPt hφ h0 h1).symm
    · simp only [Finset.mem_image, Finset.mem_attach, true_and]
      refine ⟨⟨φ⁻¹, hSGE (by simp)⟩, Subtype.ext ?_⟩
      change x.1.eval φ⁻¹ _ = (belyiPt X φ x).1.eval tgen⁻¹ _
      rw [x.1.eval_inv hφ, (belyiPt X φ x).1.eval_inv (tgen_mem _), eval_belyiPt hφ h0 h1]
    · simp only [Finset.mem_image, Finset.mem_attach, true_and]
      refine ⟨⟨(1 - φ)⁻¹, hSGE (by simp)⟩, Subtype.ext ?_⟩
      change x.1.eval (1 - φ)⁻¹ _ = (belyiPt X φ x).1.eval (1 - tgen)⁻¹ _
      rw [x.1.eval_inv (sub_mem x.1.P.1.one_mem hφ),
        (belyiPt X φ x).1.eval_inv (sub_mem (belyiPt X φ x).1.P.1.one_mem (tgen_mem _)),
        x.1.eval_sub x.1.P.1.one_mem hφ,
        (belyiPt X φ x).1.eval_sub (belyiPt X φ x).1.P.1.one_mem (tgen_mem _), x.1.eval_one,
        (belyiPt X φ x).1.eval_one, eval_belyiPt hφ h0 h1]


-- @@ L441-441 verbatim
end Genl.Curves
