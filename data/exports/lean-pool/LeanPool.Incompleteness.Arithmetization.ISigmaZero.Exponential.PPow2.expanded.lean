/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Arithmetization.ISigmaZero.Exponential.Pow2
import LeanPool.Incompleteness.Arithmetization.Definability.Init
import Mathlib.Data.Nat.Cast.Order.Basic


-- @@ L12-12 verbatim
/-! # PPow2 -/


-- @@ L14-14 verbatim
@[expose] public section



-- @@ L17-17 verbatim
noncomputable section «lp_nc_section_1»


-- @@ L19-19 verbatim
namespace LO

-- @@ L20-20 verbatim
namespace Arith


-- @@ L22-22 verbatim
variable {V : Type*} [ORingStruc V]


-- @@ L24-24 verbatim
open FirstOrder FirstOrder.Arith


-- @@ L26-26 verbatim
section «lp_section_1»


-- @@ L28-28 expanded
variable [ModelsTheory V (iSigma 0)]


-- @@ L30-33 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def SPPow2 (m : V) : Prop :=
  ¬LenBit 1 m ∧
    LenBit 2 m ∧ ∀ i ≤ m, Pow2 i → 2 < i → (LenBit i m ↔ (sqrt i) ^ 2 = i ∧ LenBit (sqrt i) m)


-- @@ L35-41 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.sppow2Def : Sg0.Semisentence 1 :=
  .mkSigma
    (Wedge.wedge
      (Tilde.tilde
        (LO.FirstOrder.Rewriting.substitute lenbitDef
          (vecCons (Semiterm.numeral 1) (vecCons #0 ![]))))
      (Wedge.wedge
        (LO.FirstOrder.Rewriting.substitute lenbitDef
          (vecCons (Semiterm.numeral 2) (vecCons #0 ![])))
        (Semiformula.ballLTSucc (#0)
          (Arrow.arrow (LO.FirstOrder.Rewriting.substitute pow2Def (vecCons #0 ![]))
            (Arrow.arrow (Semiformula.Operator.operator Operator.LT.lt ![Semiterm.numeral 2, #0])
              (LogicalConnective.iff
                (LO.FirstOrder.Rewriting.substitute lenbitDef (vecCons (#0) (vecCons #1 ![])))
                (Semiformula.bexLTSucc (#0)
                  (Wedge.wedge
                    (LO.FirstOrder.Rewriting.substitute sqrtDef (vecCons (#0) (vecCons #1 ![])))
                    (Wedge.wedge
                      (Semiformula.Operator.operator Operator.Eq.eq
                        ![Semiterm.Operator.Mul.mul.operator ![#0, #0], #1])
                      (LO.FirstOrder.Rewriting.substitute lenbitDef
                        (vecCons (#0) (vecCons #2 ![]))))))))))))
    (by simp)


-- @@ L43-46 expanded
lemma sppow2_defined : DefinedPred Sg0 (SPPow2 : V → Prop) sppow2Def :=
  by
  intro v
  simp [SPPow2, sppow2Def, lenbit_defined.df.iff, pow2_defined.df.iff, sqrt_defined.df.iff, sq,
    numeral_eq_natCast]


-- @@ L48-49 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def PPow2 (i : V) : Prop := Pow2 i ∧ ∃ m < 2 * i, SPPow2 m ∧ LenBit i m


-- @@ L51-53 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.ppow2Def : Sg0.Semisentence 1 :=
  .mkSigma
    (Wedge.wedge (LO.FirstOrder.Rewriting.substitute pow2Def (vecCons #0 ![]))
      (Semiformula.bexLT (Semiterm.Operator.Mul.mul.operator ![Semiterm.numeral 2, #0])
        (Wedge.wedge (LO.FirstOrder.Rewriting.substitute sppow2Def (vecCons #0 ![]))
          (LO.FirstOrder.Rewriting.substitute lenbitDef (vecCons (#1) (vecCons #0 ![]))))))
    (by simp)


-- @@ L55-58 expanded
lemma ppow2_defined : DefinedPred Sg0 (PPow2 : V → Prop) ppow2Def :=
  by
  intro v
  simp [PPow2, ppow2Def, lenbit_defined.df.iff, pow2_defined.df.iff, sppow2_defined.df.iff,
    numeral_eq_natCast]


-- @@ L60-60 expanded
instance ppow2_definable : BoldfacePred Sg0 (PPow2 : V → Prop) :=
  ppow2_defined.to_definable


-- @@ L62-62 verbatim
namespace SPPow2


-- @@ L64-64 verbatim
variable {m : V}


-- @@ L66-66 verbatim
lemma not_lenbit_one (hm : SPPow2 m) : ¬LenBit 1 m := hm.1


-- @@ L68-68 verbatim
lemma lenbit_two (hm : SPPow2 m) : LenBit 2 m := hm.2.1


-- @@ L70-71 expanded
lemma lenbit_iff (hm : SPPow2 m) {i : V} (hi : i ≤ m) (pi : Pow2 i) (lt2 : 2 < i) :
    LenBit i m ↔ (sqrt i) ^ 2 = i ∧ LenBit (sqrt i) m :=
  hm.2.2 i hi pi lt2


-- @@ L73-77 verbatim
lemma one_lt (hm : SPPow2 m) {i : V} (hi : LenBit i m) : 1 < i := by
  by_contra A
  rcases (le_one_iff_eq_zero_or_one.mp (show i ≤ 1 from by simpa using A)) with (rfl | rfl)
  · simp at hi
  · exact hm.1 hi


-- @@ L79-80 verbatim
lemma two_lt (hm : SPPow2 m) {i : V} (hi : LenBit i m) (ne2 : i ≠ 2) : 2 < i :=
  lt_of_le_of_ne (one_lt_iff_two_le.mp <| hm.one_lt hi) (Ne.symm ne2)


-- @@ L82-83 expanded
lemma sqrt (hm : SPPow2 m) {i : V} (hi : LenBit i m) (pi : Pow2 i) (ne2 : i ≠ 2) :
    LenBit (sqrt i) m :=
  ((hm.lenbit_iff hi.le pi (hm.two_lt hi ne2)).mp hi).2


-- @@ L85-86 expanded
lemma sq_sqrt_eq (hm : SPPow2 m) {i : V} (hi : LenBit i m) (pi : Pow2 i) (ne2 : i ≠ 2) :
    (sqrt i) ^ 2 = i :=
  ((hm.lenbit_iff hi.le pi (hm.two_lt hi ne2)).mp hi).1


-- @@ L88-97 expanded
lemma of_sqrt (hm : SPPow2 m) {i : V} (pi : Pow2 i) (him : i ≤ m) (hsqi : (sqrt i) ^ 2 = i)
    (hi : LenBit (sqrt i) m) : LenBit i m :=
  by
  by_cases ne1 : i = 1
  · rcases ne1; simpa using hi
  · have ne2 : i ≠ 2 := by rintro rfl; simp [sqrt_two] at hsqi
    have : 2 < i :=
      lt_of_le_of_ne
        (one_lt_iff_two_le.mp <| lt_of_le_of_ne (pos_iff_one_le.mp pi.pos) <| Ne.symm ne1)
        (Ne.symm ne2)
    exact (hm.lenbit_iff him pi this).mpr ⟨hsqi, hi⟩


-- @@ L99-101 verbatim
@[simp] lemma two : SPPow2 (2 : V) :=
  ⟨by simp[LenBit.one], by simp, by
    simp_all⟩


-- @@ L103-103 verbatim
@[simp] lemma not_zero : ¬SPPow2 (0 : V) := by rintro ⟨_, h, _⟩; simp at h


-- @@ L105-105 verbatim
@[simp] lemma not_one : ¬SPPow2 (1 : V) := by rintro ⟨_, h, _⟩; simp [LenBit.iff_rem] at h


-- @@ L107-136 expanded
lemma sq_le_of_lt (hm : SPPow2 m) {i j : V} (pi : Pow2 i) (pj : Pow2 j) (hi : LenBit i m)
    (hj : LenBit j m) : i < j → i ^ 2 ≤ j := by
  intro hij
  suffices ∀ i < j, Pow2 i → Pow2 j → LenBit i m → LenBit j m → i ^ 2 ≤ j from
    this i hij pi pj hi hj
  clear i pi hi hij pj hj
  induction j using order_induction_sigma0
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case ind j IH =>
    intro i hij pi pj hi hj
    by_cases jne2 : j = 2
    · rcases jne2 with rfl
      have : 2 ≤ i := one_lt_iff_two_le.mp (hm.one_lt hi)
      exact False.elim ((not_lt.mpr this) hij)
    · by_cases ine2 : i = 2
      · rcases ine2 with rfl
        simpa [sq, two_mul_two_eq_four] using pj.four_le hij
      · have : sqrt i < sqrt j := by
          by_contra A
          have : j ≤ i := by
            simpa [hm.sq_sqrt_eq hi pi ine2, hm.sq_sqrt_eq hj pj jne2] using
              sq_le_sq.mpr (show sqrt j ≤ sqrt i from by simpa using A)
          exact False.elim ((not_lt.mpr this) (by simpa using hij))
        have : i ≤ sqrt j := by
          simpa [hm.sq_sqrt_eq hi pi ine2] using
            IH (sqrt j) (sqrt_lt_self_of_one_lt (hm.one_lt hj)) (sqrt i) this
              (pi.sqrt (hm.sq_sqrt_eq hi pi ine2)) (pj.sqrt (hm.sq_sqrt_eq hj pj jne2))
              (hm.sqrt hi pi ine2) (hm.sqrt hj pj jne2)
        simpa [hm.sq_sqrt_eq hj pj jne2] using sq_le_sq.mpr this


-- @@ L138-151 verbatim
lemma last_uniq (hm : SPPow2 m) {i j : V} (pi : Pow2 i) (pj : Pow2 j) (hi : LenBit i m) (hj :
    LenBit j m)
    (hsqi : m < i ^ 2) (hsqj : m < j ^ 2) : i = j := by
  by_contra ne
  wlog hij : i < j
  · exact this hm pj pi hj hi hsqj hsqi (Ne.symm ne) (lt_of_le_of_ne (by simpa using hij) (Ne.symm
    ne))
  have : i ^ 2 ≤ m := le_trans  (hm.sq_le_of_lt pi pj hi hj hij) hj.le
  have ltsqi : 2 < i ^ 2 :=
    lt_of_le_of_ne (one_lt_iff_two_le.mp <| by simpa using hm.one_lt hi) (by simp)
  have : LenBit (i ^ 2) m ↔ LenBit i m := by simpa using hm.lenbit_iff this pi.sq ltsqi
  have : LenBit (i ^ 2) m := this.mpr hi
  have : ¬m < i ^ 2 := not_lt.mpr this.le
  contradiction


-- @@ L153-153 verbatim
end SPPow2


-- @@ L155-155 verbatim
namespace PPow2


-- @@ L157-157 verbatim
lemma pow2 {i : V} (h : PPow2 i) : Pow2 i := h.1


-- @@ L159-159 verbatim
lemma pos {i : V} (ppi : PPow2 i) : 0 < i := ppi.pow2.pos


-- @@ L161-162 verbatim
lemma one_lt {i : V} (ppi : PPow2 i) : 1 < i := by
  rcases ppi with ⟨_, m, _, sppm, lb⟩; exact sppm.one_lt lb


-- @@ L164-167 expanded
lemma sq_sqrt_eq {i : V} (ppi : PPow2 i) (ne2 : i ≠ 2) : (sqrt i) ^ 2 = i :=
  by
  rcases ppi with ⟨pi, m, _, sppm, lb⟩
  exact
    ((sppm.lenbit_iff lb.le pi
            (lt_of_le_of_ne (one_lt_iff_two_le.mp <| sppm.one_lt lb) (Ne.symm ne2))).mp
        lb).1


-- @@ L169-198 expanded
lemma sqrt {i : V} (ppi : PPow2 i) (ne2 : i ≠ 2) : PPow2 (sqrt i) :=
  by
  rcases ppi with ⟨pi, m, _, sppm, him⟩
  have : LenBit i m ↔ (sqrt i) ^ 2 = i ∧ LenBit (sqrt i) m :=
    sppm.lenbit_iff him.le pi
      (lt_of_le_of_ne (one_lt_iff_two_le.mp <| sppm.one_lt him) (Ne.symm ne2))
  rcases this.mp him with ⟨e, H⟩
  have psqi : Pow2 (sqrt i) := Pow2.sq_iff.mp (by simp [e, pi])
  have one_lt_sqi : 1 < sqrt i := one_lt_sq_iff.mp (by simpa [e] using sppm.one_lt him)
  have : SPPow2 (m % (2 * sqrt i)) :=
    ⟨by simpa [LenBit.mod] using sppm.not_lenbit_one,
      (LenBit.mod_pow2 (by simp) (by simp [psqi]) (by simp [one_lt_sqi])).mpr sppm.lenbit_two,
      by
      intro j hj pj lt2
      have hjsi : j < 2 * sqrt i := lt_of_le_of_lt hj (mod_lt _ (by simp [psqi.pos]))
      have : LenBit j m ↔ (sqrt j) ^ 2 = j ∧ LenBit (sqrt j) m :=
        sppm.lenbit_iff (le_trans hj (by simp)) pj lt2
      rw [LenBit.mod_pow2, this]
      · constructor
        · rintro ⟨hsqj, hlen⟩
          have psqj : Pow2 (sqrt j) := pj.sqrt hsqj
          have hsqrt_lt : sqrt j < 2 * sqrt i := lt_of_le_of_lt (sqrt_le_self j) hjsi
          exact ⟨hsqj, (LenBit.mod_pow2 psqj (pow2_two.mul psqi) hsqrt_lt).mpr hlen⟩
        · rintro ⟨hsqj, hlen⟩
          have psqj : Pow2 (sqrt j) := pj.sqrt hsqj
          have hsqrt_lt : sqrt j < 2 * sqrt i := lt_of_le_of_lt (sqrt_le_self j) hjsi
          exact ⟨hsqj, (LenBit.mod_pow2 psqj (pow2_two.mul psqi) hsqrt_lt).mp hlen⟩
      · exact pj
      · exact pow2_two.mul psqi
      · exact hjsi⟩
  exact ⟨psqi, m % (2 * sqrt i), mod_lt _ (by simp [psqi.pos]), this, by simp [H]⟩


-- @@ L200-200 verbatim
lemma exists_spp {i : V} (h : PPow2 i) : ∃ m < 2 * i, SPPow2 m ∧ LenBit i m := h.2


-- @@ L202-246 expanded
protected lemma sq {i : V} (ppi : PPow2 i) : PPow2 (i ^ 2) :=
  by
  rcases ppi.exists_spp with ⟨m, hm, sppm, hi⟩
  have sppm' : SPPow2 (m + i ^ 2) :=
    ⟨by rw [LenBit.add_pow2] <;> try simp [ppi.pow2, sppm.not_lenbit_one, sppm.one_lt hi],
      by
      rw [LenBit.add_pow2]
      · exact sppm.lenbit_two
      · exact pow2_two
      · exact ppi.pow2.sq
      · exact lt_of_le_of_lt (one_lt_iff_two_le.mp ppi.one_lt) (lt_square_of_lt ppi.one_lt),
      by
      intro j hj pj lt2
      have hsqi : i < i ^ 2 := lt_square_of_lt ppi.one_lt
      have hmi : m < i ^ 2 :=
        lt_of_lt_of_le hm (two_mul_le_sq <| one_lt_iff_two_le.mp <| sppm.one_lt hi)
      rw [LenBit.add_pow2_iff_of_lt] <;> try simp [pj, ppi.pow2, hmi]
      constructor
      · rintro (rfl | hj)
        · simp only [sqrt_sq, true_and]
          exact (LenBit.add_pow2 ppi.pow2 ppi.pow2.sq hsqi).mpr hi
        · have : (sqrt j) ^ 2 = j := sppm.sq_sqrt_eq hj pj (ne_of_gt lt2)
          rw [LenBit.add_pow2_iff_of_lt] <;> try simp [ppi.pow2, pj.sqrt this, hmi]
          simp [sppm.sqrt hj pj (ne_of_gt lt2), this]
      · rintro ⟨ej, lb⟩
        have hsqj : sqrt j < i ^ 2 :=
          lt_of_mul_lt_mul_left (a := 2)
            (by
              calc
                2 * sqrt j ≤ (sqrt j) ^ 2 :=
                  two_mul_le_sq
                    (one_lt_iff_two_le.mp <|
                      one_lt_sq_iff.mp <| by rw [ej]; exact lt_trans one_lt_two lt2)
                _ ≤ j := by simp
                _ ≤ m + i ^ 2 := hj
                _ < 2 * i ^ 2 := by simp [two_mul, hmi])
        have hsqj : LenBit (sqrt j) m := (LenBit.add_pow2 (pj.sqrt ej) ppi.pow2.sq hsqj).mp lb
        by_cases hjm : j ≤ m
        · exact Or.inr <| sppm.of_sqrt pj hjm ej hsqj
        · have : i = sqrt j :=
            sppm.last_uniq ppi.pow2 (pj.sqrt ej) hi hsqj hmi (by simpa [ej] using hjm)
          left; simp [this, ej]⟩
  by_cases ne1 : i = 1
  · rcases ne1; simpa using ppi
  have : m < i ^ 2 :=
    lt_of_lt_of_le hm
      (two_mul_le_sq <|
        one_lt_iff_two_le.mp <| lt_of_le_of_ne (pos_iff_one_le.mp <| ppi.pos) (Ne.symm ne1))
  exact ⟨ppi.pow2.sq, m + i ^ 2, by simp [two_mul, this], sppm', LenBit.add_self this⟩


-- @@ L248-248 verbatim
@[simp] lemma two : PPow2 (2 : V) := ⟨by simp, 2, by simp []⟩


-- @@ L250-250 verbatim
@[simp] lemma not_zero : ¬PPow2 (0 : V) := by intro h; simpa using h.pow2


-- @@ L252-255 verbatim
@[simp] lemma not_one : ¬PPow2 (1 : V) := by
  rintro ⟨_, m, hm, H, _⟩
  have : m ≤ 1 := lt_two_iff_le_one.mp (by simpa using hm)
  rcases le_one_iff_eq_zero_or_one.mp this with (rfl | rfl) <;> simp at H


-- @@ L257-264 expanded
lemma elim {i : V} : PPow2 i ↔ i = 2 ∨ ∃ b, i = b ^ 2 ∧ PPow2 b :=
  by
  by_cases ei : i = 2
  · rcases ei with rfl; simp
  · simp only [ei, false_or]; constructor
    · rintro ppi
      exact ⟨sqrt i, Eq.symm <| ppi.sq_sqrt_eq ei, ppi.sqrt ei⟩
    · rintro ⟨j, rfl, ppj⟩
      exact ppj.sq


-- @@ L266-272 verbatim
lemma elim' {i : V} : PPow2 i ↔ i = 2 ∨ 2 < i ∧ ∃ j, i = j ^ 2 ∧ PPow2 j := by
  by_cases ha : 2 < i
  · rw [elim]
    simp only [ha, true_and]
  · simp only [ha, false_and, or_false]
    have : i = 0 ∨ i = 1 ∨ i = 2 := by simpa [le_two_iff_eq_zero_or_one_or_two] using ha
    rcases this with (rfl | rfl | rfl) <;> simp


-- @@ L274-274 verbatim
@[simp] lemma four : PPow2 (4 : V) := elim.mpr (Or.inr <| ⟨2, by simp [two_pow_two_eq_four]⟩)


-- @@ L276-277 verbatim
lemma two_le {i : V} (hi : PPow2 i) : 2 ≤ i := by
  simp [←one_add_one_eq_two, ←lt_iff_succ_le, hi.one_lt]


-- @@ L279-279 verbatim
lemma not_three : ¬PPow2 (3 : V) := by intro h; simpa [sqrt_three] using h.sqrt (by simp)


-- @@ L281-287 verbatim
lemma two_lt {i : V} (hi : PPow2 i) (ne : i ≠ 2) : 2 < i := by
  by_contra A
  have A : i = 0 ∨ i = 1 ∨ i = 2 := le_two_iff_eq_zero_or_one_or_two.mp (le_of_not_gt A)
  rcases A with (rfl | rfl | rfl)
  · exact not_zero hi
  · exact not_one hi
  · exact ne rfl


-- @@ L289-295 verbatim
lemma four_le {i : V} (hi : PPow2 i) (ne : i ≠ 2) : 4 ≤ i := by
  by_contra A
  have : i ≤ 3 := by simpa [←three_add_one_eq_four, ←le_iff_lt_succ] using A
  rcases le_three_iff_eq_zero_or_one_or_two_or_three.mp this with (rfl | rfl | rfl | rfl) <;>
    simp at ne hi
  · have : PPow2 (1 : V) := by simpa [sqrt_three] using hi.sqrt (by simp)
    simp at this


-- @@ L297-298 verbatim
lemma four_lt {i : V} (hi : PPow2 i) (ne2 : i ≠ 2) (ne4 : i ≠ 4) : 4 < i :=
  Ne.lt_of_le (Ne.symm ne4) (hi.four_le ne2)


-- @@ L300-302 verbatim
lemma sq_ne_two {i : V} (hi : PPow2 i) : i ^ 2 ≠ 2 := by
  intro e; have : i < 2 := by simpa [←e] using lt_square_of_lt hi.one_lt
  exact not_le.mpr this hi.two_le


-- @@ L304-307 expanded
lemma sqrt_ne_two {i : V} (hi : PPow2 i) (ne2 : i ≠ 2) (ne4 : i ≠ 4) : sqrt i ≠ 2 :=
  by
  intro e
  have : i = 4 := by simpa [e, two_pow_two_eq_four] using Eq.symm <| hi.sq_sqrt_eq ne2
  contradiction


-- @@ L309-310 verbatim
lemma sq_ne_four {i : V} (hi : PPow2 i) (ne2 : i ≠ 2) : i ^ 2 ≠ 4 := by
  simpa [two_pow_two_eq_four] using ne_of_gt (sq_lt_sq.mpr (hi.two_lt ne2))


-- @@ L312-335 expanded
lemma sq_le_of_lt {i j : V} (hi : PPow2 i) (hj : PPow2 j) : i < j → i ^ 2 ≤ j :=
  by
  intro hij
  suffices ∀ i < j, PPow2 i → PPow2 j → i ^ 2 ≤ j from this i hij hi hj
  clear hi hij hj
  induction j using order_induction_sigma0
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case ind j IH =>
    intro i hij hi hj
    by_cases ej : j = 2
    · have : 2 ≤ i := by simpa [one_add_one_eq_two] using lt_iff_succ_le.mp hi.one_lt
      exact False.elim ((not_lt.mpr this) (by simpa [ej] using hij))
    · by_cases ei : i = 2
      · rcases ei with rfl
        simpa [sq, two_mul_two_eq_four] using hj.four_le ej
      · have : sqrt i < sqrt j := by
          by_contra A
          have : j ≤ i := by
            simpa [hi.sq_sqrt_eq ei, hj.sq_sqrt_eq ej] using
              sq_le_sq.mpr (show sqrt j ≤ sqrt i from by simpa using A)
          exact False.elim ((not_lt.mpr this) (by simpa using hij))
        have : i ≤ sqrt j := by
          simpa [hi.sq_sqrt_eq ei] using
            IH (sqrt j) (sqrt_lt_self_of_one_lt hj.one_lt) (sqrt i) this (hi.sqrt ei) (hj.sqrt ej)
        simpa [hj.sq_sqrt_eq ej] using sq_le_sq.mpr this


-- @@ L337-346 verbatim
lemma sq_uniq {y i j : V} (py : Pow2 y) (ppi : PPow2 i) (ppj : PPow2 j)
    (hi : y < i ∧ i ≤ y ^ 2) (hj : y < j ∧ j ≤ y ^ 2) : i = j := by
  by_contra ne
  wlog hij : i < j
  · exact this py ppj ppi hj hi (Ne.symm ne) (Ne.lt_of_le' ne (by simpa using hij))
  have : y ^ 2 < y ^ 2 := calc
    y ^ 2 < i ^ 2 := sq_lt_sq.mpr hi.1
    _   ≤ j   := sq_le_of_lt ppi ppj hij
    _   ≤ y ^ 2 := hj.2
  simp_all


-- @@ L348-362 verbatim
lemma two_mul_sq_uniq {y i j : V} (py : Pow2 y) (ppi : PPow2 i) (ppj : PPow2 j)
    (hi : y < i ∧ i ≤ 2 * y ^ 2) (hj : y < j ∧ j ≤ 2 * y ^ 2) : i = j := by
  by_contra ne
  wlog hij : i < j
  · exact this py ppj ppi hj hi (Ne.symm ne) (Ne.lt_of_le' ne (by simpa using hij))
  have : i ^ 2 < (2 * y) ^ 2 := calc
    i ^ 2 ≤ j         := sq_le_of_lt ppi ppj hij
    _   ≤ 2 * y ^ 2   := hj.2
    _   < (2 * y) ^ 2 := by
      simp only [sq, mul_assoc, zero_lt_two, mul_lt_mul_iff_right₀]
      rw [mul_left_comm]
      exact lt_mul_of_pos_of_one_lt_left (by simpa using pos_iff_ne_zero.mp py.pos) (by simp [])
  have : i < 2 * y := sq_lt_sq.mp this
  have : y < y := lt_of_lt_of_le hi.1 ((ppi.pow2.le_iff_lt_two py).mpr this)
  simp_all


-- @@ L364-364 verbatim
end PPow2


-- @@ L366-366 verbatim
end «lp_section_1»


-- @@ L368-368 verbatim
end Arith

-- @@ L369-369 verbatim
end LO


-- @@ L371-371 verbatim
end «lp_nc_section_1»
