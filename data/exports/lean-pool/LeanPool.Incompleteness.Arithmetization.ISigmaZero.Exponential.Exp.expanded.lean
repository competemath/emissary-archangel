/-
Copyright (c) 2026 Palalansoukî. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Palalansoukî
-/
module

public import LeanPool.Incompleteness.Arithmetization.ISigmaZero.Exponential.PPow2
import LeanPool.Incompleteness.Arithmetization.Definability.Init
import Mathlib.Data.Nat.Cast.Order.Basic


-- @@ L12-12 verbatim
/-! # Exp -/


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


-- @@ L30-31 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def ext (u z : V) : V := z / u % u


-- @@ L33-33 verbatim
lemma ext_graph (a b c : V) : a = ext b c ↔ ∃ x ≤ c, x = c / b ∧ a = x % b := by simp [ext]


-- @@ L35-37 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.extDef : Sg0.Semisentence 3 :=
  .mkSigma
    (Semiformula.bexLTSucc (#2)
      (Wedge.wedge
        (LO.FirstOrder.Rewriting.substitute divDef (vecCons (#0) (vecCons (#3) (vecCons #2 ![]))))
        (LO.FirstOrder.Rewriting.substitute remDef (vecCons (#1) (vecCons (#0) (vecCons #2 ![]))))))
    (by simp)


-- @@ L39-42 expanded
lemma ext_defined : DefinedFunction₂ Sg0 (fun a b : V ↦ ext a b) extDef :=
  by
  intro v
  simp [extDef, ext_graph, Semiformula.eval_substs, div_defined.df.iff, rem_defined.df.iff,
    le_iff_lt_succ]


-- @@ L44-44 expanded
instance ext_definable : BoldfaceFunction₂ Sg0 (ext : V → V → V) :=
  ext_defined.to_definable


-- @@ L46-46 verbatim
@[simp] lemma ext_le_add (u z : V) : ext u z ≤ z := le_trans (mod_le (z / u) u) (by simp [])


-- @@ L48-48 verbatim
instance : Bounded₂ (ext : V → V → V) := ⟨#1, by intro v; simp⟩


-- @@ L50-50 verbatim
@[simp] lemma ext_lt {u} (z : V) (pos : 0 < u) : ext u z < u := by simp [ext, pos]


-- @@ L52-58 verbatim
lemma ext_add_of_dvd_sq_right {u z₁ z₂ : V} (pos : 0 < u) (h : u ^ 2 ∣ z₂) :
    ext u (z₁ + z₂) = ext u z₁ := by
  simp only [ext]
  have : ∃ z', z₂ = z' * u * u := by
    rcases h with ⟨u', rfl⟩; exact ⟨u', by simp [mul_comm _ u', mul_assoc]; simp [sq]⟩
  rcases this with ⟨z₂, rfl⟩
  simp [div_add_mul_self, pos]


-- @@ L60-61 verbatim
lemma ext_add_of_dvd_sq_left {u z₁ z₂ : V} (pos : 0 < u) (h : u ^ 2 ∣ z₁) :
    ext u (z₁ + z₂) = ext u z₂ := by rw [add_comm]; exact ext_add_of_dvd_sq_right pos h


-- @@ L63-70 verbatim
lemma ext_rem {i j z : V} (ppi : PPow2 i) (ppj : PPow2 j) (hij : i < j) :
    ext i (z % j) = ext i z := by
  have := div_add_mod z j
  have : i ^ 2 ∣ j := ppi.pow2.sq.dvd_of_le ppj.pow2 (PPow2.sq_le_of_lt ppi ppj hij)
  calc
    ext i (z % j) = ext i (j * (z / j) + (z % j)) := by
      symm; exact ext_add_of_dvd_sq_left ppi.pos (Dvd.dvd.mul_right this (z / j))
    _               = ext i z                          := by simp [div_add_mod]


-- @@ L72-73 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Exponential.Seq₀ (X Y : V) : Prop := ext 4 X = 1 ∧ ext 4 Y = 2


-- @@ L75-78 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Exponential.Seqₛ.Even (X Y u : V) :
    Prop :=
  ext (u ^ 2) X = 2 * ext u X ∧ ext (u ^ 2) Y = (ext u Y) ^ 2


-- @@ L80-83 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Exponential.Seqₛ.Odd (X Y u : V) :
    Prop :=
  ext (u ^ 2) X = 2 * ext u X + 1 ∧ ext (u ^ 2) Y = 2 * (ext u Y) ^ 2


-- @@ L85-88 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Exponential.Seqₛ (y X Y : V) : Prop :=
  ∀ u ≤ y, u ≠ 2 → PPow2 u →
    Exponential.Seqₛ.Even X Y u ∨ Exponential.Seqₛ.Odd X Y u


-- @@ L90-93 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Exponential.Seqₘ (x y X Y : V) :
    Prop :=
  ∃ u ≤ y ^ 2, u ≠ 2 ∧ PPow2 u ∧ ext u X = x ∧ ext u Y = y


-- @@ L95-99 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def Exponential (x y : V) :
    Prop :=
  (x = 0 ∧ y = 1) ∨ ∃ X ≤ y^4, ∃ Y ≤ y^4, Exponential.Seq₀ X Y ∧ Exponential.Seqₛ y X Y ∧
    Exponential.Seqₘ x y X Y


-- @@ L101-116 verbatim
lemma _root_.LO.Arith.Exponential.Seqₛ.iff (y X Y : V) :
  Exponential.Seqₛ y X Y ↔
  ∀ u ≤ y, u ≠ 2 → PPow2 u →
    ((∃ ext_u_X ≤ X, ext_u_X = ext u X ∧ 2 * ext_u_X =
      ext (u ^ 2) X)     ∧ (∃ ext_u_Y ≤ Y, ext_u_Y = ext u Y ∧ ext_u_Y ^ 2 = ext (u ^ 2) Y)) ∨
    ((∃ ext_u_X ≤ X, ext_u_X = ext u X ∧ 2 * ext_u_X + 1 =
      ext (u ^ 2) X) ∧ (∃ ext_u_Y ≤ Y, ext_u_Y = ext u Y ∧ 2 * ext_u_Y ^ 2 = ext (u ^ 2) Y)) :=
  ⟨by intro H u hu ne2 ppu
      rcases H u hu ne2 ppu with (H | H)
      · exact Or.inl ⟨⟨ext u X, by simp [H.1]⟩, ⟨ext u Y, by simp [H.2]⟩⟩
      · exact Or.inr ⟨⟨ext u X, by simp [H.1]⟩, ⟨ext u Y, by simp [H.2]⟩⟩,
   by intro H u hu ne2 ppu
      rcases H u hu ne2 ppu with (⟨⟨_, _, rfl, hx⟩, ⟨_, _, rfl, hy⟩⟩ | ⟨⟨_, _, rfl, hx⟩, ⟨_, _,
        rfl, hy⟩⟩)
      · exact Or.inl ⟨by simp [hx], by simp [hy]⟩
      · exact Or.inr ⟨by simp [hx], by simp [hy]⟩⟩


-- @@ L118-125 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.Arith.Exponential.Seqₛ.def : Sg0.Semisentence 3 :=
  .mkSigma
    (Semiformula.ballLTSucc (#0)
      (Arrow.arrow
        (Tilde.tilde (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 2]))
        (Arrow.arrow (LO.FirstOrder.Rewriting.substitute ppow2Def (vecCons #0 ![]))
          (Vee.vee
            (Wedge.wedge
              (Semiformula.bexLTSucc (#2)
                (Wedge.wedge
                  (LO.FirstOrder.Rewriting.substitute extDef
                    (vecCons (#0) (vecCons (#1) (vecCons #3 ![]))))
                  (LO.FirstOrder.Rewriting.substitute extDef
                    (vecCons (Semiterm.Operator.Mul.mul.operator ![Semiterm.numeral 2, #0])
                      (vecCons ((Semiterm.Operator.npow _ 2).operator ![#1]) (vecCons #3 ![]))))))
              (Semiformula.bexLTSucc (#3)
                (Wedge.wedge
                  (LO.FirstOrder.Rewriting.substitute extDef
                    (vecCons (#0) (vecCons (#1) (vecCons #4 ![]))))
                  (LO.FirstOrder.Rewriting.substitute extDef
                    (vecCons ((Semiterm.Operator.npow _ 2).operator ![#0])
                      (vecCons ((Semiterm.Operator.npow _ 2).operator ![#1]) (vecCons #4 ![])))))))
            (Wedge.wedge
              (Semiformula.bexLTSucc (#2)
                (Wedge.wedge
                  (LO.FirstOrder.Rewriting.substitute extDef
                    (vecCons (#0) (vecCons (#1) (vecCons #3 ![]))))
                  (LO.FirstOrder.Rewriting.substitute extDef
                    (vecCons
                      (Semiterm.Operator.Add.add.operator
                        ![Semiterm.Operator.Mul.mul.operator ![Semiterm.numeral 2, #0],
                          Semiterm.numeral 1])
                      (vecCons ((Semiterm.Operator.npow _ 2).operator ![#1]) (vecCons #3 ![]))))))
              (Semiformula.bexLTSucc (#3)
                (Wedge.wedge
                  (LO.FirstOrder.Rewriting.substitute extDef
                    (vecCons (#0) (vecCons (#1) (vecCons #4 ![]))))
                  (LO.FirstOrder.Rewriting.substitute extDef
                    (vecCons
                      (Semiterm.Operator.Mul.mul.operator
                        ![Semiterm.numeral 2, (Semiterm.Operator.npow _ 2).operator ![#0]])
                      (vecCons ((Semiterm.Operator.npow _ 2).operator ![#1])
                        (vecCons #4 ![])))))))))))
    (by simp)


-- @@ L127-131 expanded
lemma _root_.LO.Arith.Exponential.Seqₛ.defined :
    DefinedRel₃ Sg0 (Exponential.Seqₛ : V → V → V → Prop) Exponential.Seqₛ.def :=
  by
  intro v
  simp [Exponential.Seqₛ.iff, Exponential.Seqₛ.def, ppow2_defined.df.iff, ext_defined.df.iff, sq,
    numeral_eq_natCast]


-- @@ L133-146 verbatim
lemma _root_.LO.Arith.Exponential.graph_iff (x y : V) :
    Exponential x y ↔
    (x = 0 ∧ y = 1) ∨ ∃ X ≤ y^4, ∃ Y ≤ y^4,
      (1 = ext 4 X ∧ 2 = ext 4 Y) ∧
      Exponential.Seqₛ y X Y ∧
      (∃ u ≤ y ^ 2, u ≠ 2 ∧ PPow2 u ∧ x = ext u X ∧ y = ext u Y) :=
  ⟨by rintro (H | ⟨X, bX, Y, bY, H₀, Hₛ, ⟨u, hu, ne2, ppu, hX, hY⟩⟩)
      · exact Or.inl H
      · exact Or.inr ⟨X, bX, Y, bY, ⟨H₀.1.symm, H₀.2.symm⟩, Hₛ, ⟨u, hu, ne2, ppu, hX.symm,
        hY.symm⟩⟩,
   by rintro (H | ⟨X, bX, Y, bY, H₀, Hₛ, ⟨u, hu, ne2, ppu, hX, hY⟩⟩)
      · exact Or.inl H
      · exact Or.inr ⟨X, bX, Y, bY, ⟨H₀.1.symm, H₀.2.symm⟩, Hₛ, ⟨u, hu, ne2, ppu, hX.symm,
        hY.symm⟩⟩⟩


-- @@ L148-154 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.exponentialDef : Sg0.Semisentence 2 :=
  .mkSigma
    (Vee.vee
      (Wedge.wedge (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 0])
        (Semiformula.Operator.operator Operator.Eq.eq ![#1, Semiterm.numeral 1]))
      (Semiformula.bexLTSucc ((Semiterm.Operator.npow _ 4).operator ![#1])
        (Semiformula.bexLTSucc ((Semiterm.Operator.npow _ 4).operator ![#2])
          (Wedge.wedge
            (Wedge.wedge
              (LO.FirstOrder.Rewriting.substitute extDef
                (vecCons (Semiterm.numeral 1) (vecCons (Semiterm.numeral 4) (vecCons #1 ![]))))
              (LO.FirstOrder.Rewriting.substitute extDef
                (vecCons (Semiterm.numeral 2) (vecCons (Semiterm.numeral 4) (vecCons #0 ![])))))
            (Wedge.wedge
              (LO.FirstOrder.Rewriting.substitute Exponential.Seqₛ.def
                (vecCons (#3) (vecCons (#1) (vecCons #0 ![]))))
              (Semiformula.bexLTSucc ((Semiterm.Operator.npow _ 2).operator ![#3])
                (Wedge.wedge
                  (Tilde.tilde
                    (Semiformula.Operator.operator Operator.Eq.eq ![#0, Semiterm.numeral 2]))
                  (Wedge.wedge (LO.FirstOrder.Rewriting.substitute ppow2Def (vecCons #0 ![]))
                    (Wedge.wedge
                      (LO.FirstOrder.Rewriting.substitute extDef
                        (vecCons (#3) (vecCons (#0) (vecCons #2 ![]))))
                      (LO.FirstOrder.Rewriting.substitute extDef
                        (vecCons (#4) (vecCons (#0) (vecCons #1 ![])))))))))))))
    (by simp)


-- @@ L156-160 expanded
lemma _root_.LO.Arith.Exponential.defined :
    DefinedRel Sg0 (Exponential : V → V → Prop) exponentialDef :=
  by
  intro v
  simp [Exponential.graph_iff, exponentialDef, ppow2_defined.df.iff, ext_defined.df.iff,
    Exponential.Seqₛ.defined.df.iff, pow_four, sq, numeral_eq_natCast]


-- @@ L162-164 verbatim
@[simp] lemma exponential_defined_iff (v) :
    Semiformula.Evalbm V v exponentialDef.val ↔ Exponential (v 0) (v 1) :=
      Exponential.defined.df.iff v


-- @@ L166-168 expanded
instance exponential_definable : BoldfaceRel Sg0 (Exponential : V → V → Prop) :=
  Exponential.defined.to_definable


-- @@ L170-172 expanded
@[simp]
instance exponential_definable' (Γ) : BoldfaceRel Γ (Exponential : V → V → Prop) :=
  exponential_definable.of_zero


-- @@ L174-174 verbatim
namespace Exponential


-- @@ L176-177 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def seqX₀ : V := 4


-- @@ L179-180 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def seqY₀ : V := 2 * 4


-- @@ L182-183 verbatim
lemma one_lt_four : (1 : V) < 4 := by
  simp_all


-- @@ L185-185 verbatim
lemma two_lt_three : (2 : V) < 3 := by rw [←two_add_one_eq_three]; exact lt_add_one 2


-- @@ L187-187 verbatim
lemma three_lt_four : (3 : V) < 4 := by rw [←three_add_one_eq_four]; exact lt_add_one 3


-- @@ L189-189 verbatim
lemma two_lt_four : (2 : V) < 4 := lt_trans two_lt_three three_lt_four


-- @@ L191-192 verbatim
lemma seq₀_zero_two : Seq₀ (seqX₀ : V) (seqY₀ :
    V) := by simp [seqX₀, seqY₀, Seq₀, ext, two_lt_four]


-- @@ L194-197 verbatim
lemma _root_.LO.Arith.Exponential.Seq₀.rem {X Y i : V} (h : Seq₀ X Y) (ppi : PPow2 i) (hi : 4 < i) :
    Seq₀ (X % i) (Y % i) := by
  rw [Seq₀, ext_rem, ext_rem] <;> try simp [ppi, hi]
  exact h


-- @@ L199-208 verbatim
lemma _root_.LO.Arith.Exponential.Seqₛ.rem {y y' X Y i : V} (h : Seqₛ y X Y) (ppi : PPow2 i) (hi :
    y' ^ 2 < i) (hy :
    y' ≤ y) :
    Seqₛ y' (X % i) (Y % i) := by
  intro j hj ne2 ppj
  have : j ^ 2 < i := lt_of_le_of_lt (sq_le_sq.mpr hj) hi
  have : j < i := lt_of_le_of_lt (le_trans hj <| by simp) hi
  rcases h j (le_trans hj hy) ne2 ppj with (H | H)
  · left; simpa [Seqₛ.Even, ext_rem, ppj, ppj.sq, ppi, *] using H
  · right; simpa [Seqₛ.Odd, ext_rem, ppj, ppj.sq, ppi, *] using H


-- @@ L210-211 verbatim
lemma seqₛ_one_zero_two : Seqₛ (1 : V) (seqX₀ : V) (seqY₀ : V) := by
  intro u leu; rcases le_one_iff_eq_zero_or_one.mp leu with (rfl | rfl) <;> simp


-- @@ L213-214 verbatim
/-- Imported declaration from the Incompleteness formalization. -/
def append (i X z : V) : V := X % i + z * i


-- @@ L216-223 verbatim
lemma append_lt (i X : V) {z} (hz : z < i) : append i X z < i ^ 2 := calc
  append i X z = (X % i) + z * i := rfl
  _            < (1 + z) * i       := by
    rw [add_mul, one_mul]
    simpa only [add_comm] using add_lt_add_right (mod_lt _ (pos_of_gt hz)) (z * i)
  _            ≤ i ^ 2               := by
    rw [sq]
    simpa only [add_comm] using mul_le_mul_of_nonneg_right (lt_iff_succ_le.mp hz) (by simp)


-- @@ L225-227 verbatim
lemma ext_append_last (i X : V) {z} (hz : z < i) :
    ext i (append i X z) = z := by
  simp [ext, append, div_add_mul_self, show 0 < i from pos_of_gt hz, hz]


-- @@ L229-238 verbatim
lemma ext_append_of_lt {i j : V} (hi : PPow2 i) (hj : PPow2 j) (hij : i < j) (X z : V) :
    ext i (append j X z) = ext i X := by
  have : i ^ 2 ∣ j := Pow2.dvd_of_le hi.pow2.sq hj.pow2 (PPow2.sq_le_of_lt hi hj hij)
  calc
    ext i (append j X z) = ext i ((X % j) + z * j)       := rfl
    _                    = ext i (X % j)                 :=
      ext_add_of_dvd_sq_right hi.pos (Dvd.dvd.mul_left this z)
    _                    = ext i (j * (X / j) + (X % j)) := by
      rw [add_comm]; refine Eq.symm <| ext_add_of_dvd_sq_right hi.pos (Dvd.dvd.mul_right this _)
    _                    = ext i X                         := by simp [div_add_mod]


-- @@ L240-244 verbatim
lemma _root_.LO.Arith.Exponential.Seq₀.append {X Y i x y : V} (H : Seq₀ X Y) (ppi : PPow2 i) (hi :
    4 < i) :
    Seq₀ (append i X x) (append i Y y) := by
  rw [Seq₀, ext_append_of_lt, ext_append_of_lt] <;> try simp [ppi, hi]
  exact H


-- @@ L246-260 verbatim
lemma _root_.LO.Arith.Exponential.Seqₛ.append {z x y X Y i : V} (h : Seqₛ z X Y) (ppi :
    PPow2 i) (hz :
    z < i) :
    Seqₛ z (append (i ^ 2) X x) (append (i ^ 2) Y y) := by
  intro j hj ne2 ppj
  have : j < i ^ 2 := lt_of_lt_of_le (lt_of_le_of_lt hj hz) (by simp)
  have : j ^ 2 < i ^ 2 := sq_lt_sq.mpr (lt_of_le_of_lt hj hz)
  rcases h j hj ne2 ppj with (H | H) <;>
    simp only [Seqₛ.Even, Seqₛ.Odd]
  · left; rw [ext_append_of_lt, ext_append_of_lt, ext_append_of_lt,
    ext_append_of_lt] <;> try simp [ppi.sq, ppj.sq, *]
    exact H
  · right; rw [ext_append_of_lt, ext_append_of_lt, ext_append_of_lt,
    ext_append_of_lt] <;> try simp [ppi.sq, ppj.sq, *]
    exact H


-- @@ L262-262 verbatim
@[simp 1100] lemma exponential_zero_one : Exponential (0 : V) 1 := Or.inl (by simp)


-- @@ L264-275 verbatim
@[simp] lemma exponential_one_two : Exponential (1 : V) 2 :=
  Or.inr ⟨
    4, by simp [pow_four_eq_sq_sq, two_pow_two_eq_four],
    2 * 4, by
      rw [pow_four_eq_sq_sq, two_pow_two_eq_four, sq]
      exact mul_le_mul_of_nonneg_right (le_of_lt two_lt_four) (by simp),
    by simp [Seq₀, ext, two_lt_four],
    by
      simp only [Seqₛ, ne_eq]
      intro i hi ne2 ppi
      exact False.elim <| not_le.mpr (ppi.two_lt ne2) hi,
    ⟨4, by simp [two_pow_two_eq_four], by simp, by simp [ext, two_lt_four]⟩⟩


-- @@ L277-292 expanded
lemma pow2_ext_of_seq₀_of_seqₛ {y X Y : V} (h₀ : Exponential.Seq₀ X Y) (hₛ : Exponential.Seqₛ y X Y)
    {i} (ne2 : i ≠ 2) (hi : i ≤ y ^ 2) (ppi : PPow2 i) : Pow2 (ext i Y) :=
  by
  induction i using order_induction_sigma0
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case ind i IH =>
    by_cases ei : i = 4
    · rcases ei with rfl; simp [h₀.2]
    · have ppsq : Pow2 (ext (sqrt i) Y) :=
        IH (sqrt i) (sqrt_lt_self_of_one_lt ppi.one_lt) (ppi.sqrt_ne_two ne2 ei)
          (le_trans (by simp) hi) (ppi.sqrt ne2)
      rcases
        show Seqₛ.Even X Y (sqrt i) ∨ Seqₛ.Odd X Y (sqrt i) from
          hₛ (sqrt i) (sqrt_le_of_le_sq <| hi) (ppi.sqrt_ne_two ne2 ei) (ppi.sqrt ne2) with
        (heven | hodd)
      · have : ext i Y = (ext (sqrt i) Y) ^ 2 := by simpa [ppi.sq_sqrt_eq ne2] using heven.2
        simp [this, ppsq]
      · have : ext i Y = 2 * (ext (sqrt i) Y) ^ 2 := by simpa [ppi.sq_sqrt_eq ne2] using hodd.2
        simp [this, ppsq]


-- @@ L294-297 verbatim
lemma range_pow2 {x y : V} (h : Exponential x y) : Pow2 y := by
  rcases h with (⟨rfl, rfl⟩ | ⟨X, bX, Y, bY, H₀, Hₛ, ⟨u, hu, ne2, ppu, rfl, rfl⟩⟩)
  · simp
  · exact pow2_ext_of_seq₀_of_seqₛ H₀ Hₛ ne2 hu ppu


-- @@ L299-318 expanded
lemma le_sq_ext_of_seq₀_of_seqₛ {y X Y : V} (h₀ : Exponential.Seq₀ X Y)
    (hₛ : Exponential.Seqₛ y X Y) {i} (ne2 : i ≠ 2) (hi : i ≤ y ^ 2) (ppi : PPow2 i) :
    i ≤ (ext i Y) ^ 2 := by
  induction i using order_induction_sigma0
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case ind i IH =>
    by_cases ei : i = 4
    · rcases ei with rfl; simp [h₀.2, two_pow_two_eq_four]
    · have IH : sqrt i ≤ (ext (sqrt i) Y) ^ 2 :=
        IH (sqrt i) (sqrt_lt_self_of_one_lt ppi.one_lt) (ppi.sqrt_ne_two ne2 ei)
          (le_trans (by simp) hi) (ppi.sqrt ne2)
      rcases
        show Seqₛ.Even X Y (sqrt i) ∨ Seqₛ.Odd X Y (sqrt i) from
          hₛ (sqrt i) (sqrt_le_of_le_sq <| hi) (ppi.sqrt_ne_two ne2 ei) (ppi.sqrt ne2) with
        (heven | hodd)
      · have : ext i Y = (ext (sqrt i) Y) ^ 2 := by simpa [ppi.sq_sqrt_eq ne2] using heven.2
        have : sqrt i ≤ ext i Y := by simpa [this] using IH
        simpa [ppi.sq_sqrt_eq ne2] using sq_le_sq.mpr this
      · have : ext i Y = 2 * (ext (sqrt i) Y) ^ 2 := by simpa [ppi.sq_sqrt_eq ne2] using hodd.2
        have : 2 * sqrt i ≤ ext i Y := by simpa [this] using mul_le_mul_left (a := 2) IH
        have : sqrt i ≤ ext i Y := le_trans (le_mul_of_pos_left <| by simp) this
        simpa [ppi.sq_sqrt_eq ne2] using sq_le_sq.mpr this


-- @@ L320-343 expanded
lemma two_mul_ext_le_of_seq₀_of_seqₛ {y X Y : V} (h₀ : Exponential.Seq₀ X Y)
    (hₛ : Exponential.Seqₛ y X Y) {i} (ne2 : i ≠ 2) (hi : i ≤ y ^ 2) (ppi : PPow2 i) :
    2 * ext i Y ≤ i := by
  induction i using order_induction_sigma0
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case ind i IH =>
    by_cases ei : i = 4
    · rcases ei with rfl; simp [h₀.2, two_mul_two_eq_four]
    · have IH : 2 * ext (sqrt i) Y ≤ sqrt i :=
        IH (sqrt i) (sqrt_lt_self_of_one_lt ppi.one_lt) (ppi.sqrt_ne_two ne2 ei)
          (le_trans (by simp) hi) (ppi.sqrt ne2)
      rcases
        show Seqₛ.Even X Y (sqrt i) ∨ Seqₛ.Odd X Y (sqrt i) from
          hₛ (sqrt i) (sqrt_le_of_le_sq <| hi) (ppi.sqrt_ne_two ne2 ei) (ppi.sqrt ne2) with
        (heven | hodd)
      · have : ext i Y = (ext (sqrt i) Y) ^ 2 := by simpa [ppi.sq_sqrt_eq ne2] using heven.2
        calc
          2 * ext i Y ≤ 2 * (2 * ext i Y) := le_mul_of_pos_left (by simp)
          _ = (2 * ext (sqrt i) Y) ^ 2 := by simp [this, sq, mul_left_comm, mul_assoc]
          _ ≤ (sqrt i) ^ 2 := (sq_le_sq.mpr IH)
          _ = i := ppi.sq_sqrt_eq ne2
      · have : ext i Y = 2 * (ext (sqrt i) Y) ^ 2 := by simpa [ppi.sq_sqrt_eq ne2] using hodd.2
        calc
          2 * ext i Y = (2 * ext (sqrt i) Y) ^ 2 := by simp [this, sq, mul_left_comm, mul_assoc]
          _ ≤ (sqrt i) ^ 2 := (sq_le_sq.mpr IH)
          _ = i := ppi.sq_sqrt_eq ne2


-- @@ L345-383 expanded
lemma exponential_exists_sq_of_exponential_even {x y : V} :
    Exponential (2 * x) y → ∃ y', y = y' ^ 2 ∧ Exponential x y' :=
  by
  rintro (⟨hx, rfl⟩ | ⟨X, _, Y, _, hseq₀, hseqₛ, i, hi, ne2, ppi, hXx, hYy⟩)
  · exact ⟨1, by simp [show x = 0 from by simpa using hx]⟩
  by_cases ne4 : i = 4
  · rcases ne4 with rfl
    have ex : 1 = 2 * x := by simpa [hseq₀.1] using hXx
    have : (2 : V) ∣ 1 := by rw [ex]; simp
    have : ¬(2 : V) ∣ 1 := not_dvd_of_lt (by simp) one_lt_two
    contradiction
  have : Seqₛ.Even X Y (sqrt i) ∨ Seqₛ.Odd X Y (sqrt i) :=
    hseqₛ (sqrt i) (sqrt_le_of_le_sq hi) (ppi.sqrt_ne_two ne2 ne4) (ppi.sqrt ne2)
  rcases this with (⟨hXi, hYi⟩ | ⟨hXi, _⟩)
  · have hXx : x = ext (sqrt i) X := by simpa [ppi.sq_sqrt_eq ne2, hXx] using hXi
    have hYy : y = (ext (sqrt i) Y) ^ 2 := by simpa [ppi.sq_sqrt_eq ne2, hYy] using hYi
    let X' := X % i
    let Y' := Y % i
    have bX' : X' ≤ (ext (sqrt i) Y) ^ 4 :=
      calc
        X' ≤ i := le_of_lt <| by simp [X', ppi.pos]
        _ ≤ y ^ 2 := hi
        _ = (ext (sqrt i) Y) ^ 4 := by rw [hYy, pow_four_eq_sq_sq]
    have bY' : Y' ≤ (ext (sqrt i) Y) ^ 4 :=
      calc
        Y' ≤ i := le_of_lt <| by simp [Y', ppi.pos]
        _ ≤ y ^ 2 := hi
        _ = (ext (sqrt i) Y) ^ 4 := by rw [hYy, pow_four_eq_sq_sq]
    have hseqₛ' : Seqₛ (ext (sqrt i) Y) X' Y' :=
      hseqₛ.rem ppi (sq_lt_of_lt_sqrt <| ext_lt Y (ppi.sqrt ne2).pos) (by simp [hYy])
    have hseqₘ' : Seqₘ x (ext (sqrt i) Y) X' Y' :=
      ⟨sqrt i, sqrt_le_of_le_sq <| by simp [← hYy, hi], ppi.sqrt_ne_two ne2 ne4, ppi.sqrt ne2,
        by
        have : sqrt i < i := sqrt_lt_self_of_one_lt ppi.one_lt
        simp [X', Y', this, ext_rem, ppi, ppi.sqrt ne2, hXx]⟩
    have : Exponential x (ext (sqrt i) Y) :=
      Or.inr ⟨X', bX', Y', bY', hseq₀.rem ppi (ppi.four_lt ne2 ne4), hseqₛ', hseqₘ'⟩
    exact ⟨ext (sqrt i) Y, hYy, this⟩
  · have : 2 ∣ ext i X := by simp [hXx]
    have : ¬2 ∣ ext i X := by
      simp [show ext i X = 2 * ext (sqrt i) X + 1 from by simpa [ppi.sq_sqrt_eq ne2] using hXi,
        ← mod_eq_zero_iff_dvd]
    contradiction


-- @@ L385-431 verbatim
lemma bit_zero {x y : V} : Exponential x y → Exponential (2 * x) (y ^ 2) := by
  rintro (⟨hx, rfl⟩ | ⟨X, _, Y, _, hseq₀, hseqₛ, i, hi, ne2, ppi, hXx, hYy⟩)
  · rcases hx with rfl; simp
  have hxsqi : 2 * x < i ^ 2 := lt_of_lt_of_le (by simp [←hXx, ppi.pos]) (two_mul_le_sq ppi.two_le)
  have hysqi : y ^ 2 < i ^ 2 := sq_lt_sq.mpr <| by simp [←hYy, ppi.pos]
  have hiisq : i < i ^ 2 := lt_square_of_lt ppi.one_lt
  let X' := append (i ^ 2) X (2 * x)
  let Y' := append (i ^ 2) Y (y ^ 2)
  have bX' : X' ≤ (y ^ 2)^4 := by
    have : X' < i^4 := by simpa [pow_four_eq_sq_sq] using append_lt (i ^ 2) X hxsqi
    exact le_trans (le_of_lt this) (pow_le_pow_left₀ (zero_le i) hi 4)
  have bY' : Y' ≤ (y ^ 2)^4 := by
    have : Y' < i^4 := by simpa [pow_four_eq_sq_sq] using append_lt (i ^ 2) Y hysqi
    exact le_trans (le_of_lt this) (pow_le_pow_left₀ (zero_le i) hi 4)
  have hseq₀' : Seq₀ X' Y' :=
    hseq₀.append ppi.sq (ppi.sq.four_lt ppi.sq_ne_two (ppi.sq_ne_four ne2))
  have hseqₛ' : Seqₛ (y ^ 2) X' Y' := by
    intro j hj jne2 ppj
    by_cases hjy : j ≤ y
    · have : Seqₛ y X' Y' := hseqₛ.append ppi (by simp [←hYy, ppi.pos])
      exact this j hjy jne2 ppj
    · have : i = j := by
        have : Pow2 y := by simpa [hYy] using pow2_ext_of_seq₀_of_seqₛ hseq₀ hseqₛ ne2 hi ppi
        exact PPow2.sq_uniq this ppi ppj
          ⟨by simp [←hYy, ppi.pos], hi⟩ ⟨by simpa using hjy, hj⟩
      rcases this with rfl
      left
      change ext (i ^ 2) (append (i ^ 2) X (2 * x)) =
          2 * ext i (append (i ^ 2) X (2 * x)) ∧
        ext (i ^ 2) (append (i ^ 2) Y (y ^ 2)) =
          ext i (append (i ^ 2) Y (y ^ 2)) ^ 2
      constructor
      · calc
          ext (i ^ 2) (append (i ^ 2) X (2 * x)) = 2 * x := ext_append_last (i ^ 2) X hxsqi
          _ = 2 * ext i (append (i ^ 2) X (2 * x)) := by
            rw [ext_append_of_lt ppi ppi.sq hiisq X (2 * x), hXx]
      · calc
          ext (i ^ 2) (append (i ^ 2) Y (y ^ 2)) = y ^ 2 := ext_append_last (i ^ 2) Y hysqi
          _ = ext i (append (i ^ 2) Y (y ^ 2)) ^ 2 := by
            rw [ext_append_of_lt ppi ppi.sq hiisq Y (y ^ 2), hYy]
  have hseqₘ' : Seqₘ (2 * x) (y ^ 2) X' Y' :=
    ⟨i ^ 2, sq_le_sq.mpr hi, ppi.sq_ne_two, ppi.sq,
     by
       change ext (i ^ 2) (append (i ^ 2) X (2 * x)) = 2 * x ∧
         ext (i ^ 2) (append (i ^ 2) Y (y ^ 2)) = y ^ 2
       exact ⟨ext_append_last (i ^ 2) X hxsqi, ext_append_last (i ^ 2) Y hysqi⟩⟩
  exact Or.inr <| ⟨X', bX', Y', bY', hseq₀', hseqₛ', hseqₘ'⟩


-- @@ L433-434 verbatim
lemma exponential_even {x y : V} : Exponential (2 * x) y ↔ ∃ y', y = y' ^ 2 ∧ Exponential x y' :=
  ⟨exponential_exists_sq_of_exponential_even, by rintro ⟨y, rfl, h⟩; exact bit_zero h⟩


-- @@ L436-440 verbatim
lemma exponential_even_sq {x y : V} : Exponential (2 * x) (y ^ 2) ↔ Exponential x y :=
  ⟨by intro h
      rcases exponential_exists_sq_of_exponential_even h with ⟨y', e, h⟩
      simpa [show y = y' from by simpa using e] using h,
   bit_zero⟩


-- @@ L442-478 expanded
lemma exponential_exists_sq_of_exponential_odd {x y : V} :
    Exponential (2 * x + 1) y → ∃ y', y = 2 * y' ^ 2 ∧ Exponential x y' :=
  by
  rintro (⟨hx, rfl⟩ | ⟨X, _, Y, _, hseq₀, hseqₛ, i, hi, ne2, ppi, hXx, hYy⟩)
  · simp at hx
  by_cases ne4 : i = 4
  · rcases ne4 with rfl
    have ex : x = 0 := by simpa [hseq₀.1] using hXx
    have ey : y = 2 := by simpa [hseq₀.2] using Eq.symm hYy
    exact ⟨1, by simp [ex, ey]⟩
  have : Seqₛ.Even X Y (sqrt i) ∨ Seqₛ.Odd X Y (sqrt i) :=
    hseqₛ (sqrt i) (sqrt_le_of_le_sq hi) (ppi.sqrt_ne_two ne2 ne4) (ppi.sqrt ne2)
  rcases this with (⟨hXi, _⟩ | ⟨hXi, hYi⟩)
  · have hXx : 2 * x + 1 = 2 * ext (sqrt i) X := by simpa [ppi.sq_sqrt_eq ne2, hXx] using hXi
    have : 2 ∣ 2 * x + 1 := by rw [hXx]; simp
    have : ¬2 ∣ 2 * x + 1 := by simp [← mod_eq_zero_iff_dvd]
    contradiction
  · have hXx : x = ext (sqrt i) X := by simpa [ppi.sq_sqrt_eq ne2, hXx] using hXi
    have hYy : y = 2 * (ext (sqrt i) Y) ^ 2 := by simpa [ppi.sq_sqrt_eq ne2, hYy] using hYi
    let X' := X % i
    let Y' := Y % i
    have bsqi : sqrt i ≤ (ext (sqrt i) Y) ^ 2 :=
      le_sq_ext_of_seq₀_of_seqₛ hseq₀ hseqₛ (ppi.sqrt_ne_two ne2 ne4) (le_trans (by simp) hi)
        (ppi.sqrt ne2)
    have bi : i ≤ ext (sqrt i) Y ^ 4 := by
      simpa [pow_four_eq_sq_sq, ppi.sq_sqrt_eq ne2] using sq_le_sq.mpr bsqi
    have bX' : X' ≤ (ext (sqrt i) Y) ^ 4 := le_trans (le_of_lt <| by simp [X', ppi.pos]) bi
    have bY' : Y' ≤ (ext (sqrt i) Y) ^ 4 := le_trans (le_of_lt <| by simp [Y', ppi.pos]) bi
    have hseqₛ' : Seqₛ (ext (sqrt i) Y) X' Y' :=
      hseqₛ.rem ppi (sq_lt_of_lt_sqrt <| ext_lt Y (ppi.sqrt ne2).pos)
        (le_trans (le_sq _) (by simp [hYy]))
    have hseqₘ' : Seqₘ x (ext (sqrt i) Y) X' Y' :=
      ⟨sqrt i, bsqi, ppi.sqrt_ne_two ne2 ne4, ppi.sqrt ne2,
        by
        have : sqrt i < i := sqrt_lt_self_of_one_lt ppi.one_lt
        simp [X', Y', this, ext_rem, ppi, ppi.sqrt ne2, hXx]⟩
    have : Exponential x (ext (sqrt i) Y) :=
      Or.inr ⟨X', bX', Y', bY', hseq₀.rem ppi (ppi.four_lt ne2 ne4), hseqₛ', hseqₘ'⟩
    exact ⟨ext (sqrt i) Y, hYy, this⟩


-- @@ L480-534 verbatim
lemma bit_one {x y : V} : Exponential x y → Exponential (2 * x + 1) (2 * y ^ 2) := by
  rintro (⟨hx, rfl⟩ | ⟨X, _, Y, _, hseq₀, hseqₛ, i, hi, ne2, ppi, hXx, hYy⟩)
  · rcases hx with rfl; simp
  have hxsqi : 2 * x + 1 < i ^ 2 := calc
    2 * x + 1 < 2 * i + 1 := by simp [←hXx, ppi.pos]
    _         ≤ i ^ 2     := lt_iff_succ_le.mp (two_mul_lt_sq <| ppi.two_lt ne2)
  have hysqi : 2 * y ^ 2 < i ^ 2 := by
    have : 2 * ext i Y ≤ i := two_mul_ext_le_of_seq₀_of_seqₛ hseq₀ hseqₛ ne2 hi ppi
    suffices 2 * (2 * y ^ 2) < 2 * i ^ 2 from lt_of_mul_lt_mul_left this
    calc
      2 * (2 * y ^ 2) = (2 * y) ^ 2 := by simp [sq, mul_assoc, mul_left_comm y 2]
      _               ≤ i ^ 2       := sq_le_sq.mpr (by simpa [hYy] using this)
      _               < 2 * i ^ 2   := lt_mul_of_one_lt_left ppi.sq.pos one_lt_two
  have hiisq : i < i ^ 2 := lt_square_of_lt ppi.one_lt
  let X' := append (i ^ 2) X (2 * x + 1)
  let Y' := append (i ^ 2) Y (2 * (y ^ 2))
  have bX' : X' ≤ (2 * y ^ 2)^4 := by
    have : X' < i^4 := by simpa [pow_four_eq_sq_sq] using append_lt (i ^ 2) X hxsqi
    exact le_trans (le_of_lt this) (pow_le_pow_left₀ (zero_le i) (le_trans hi <| by simp) 4)
  have bY' : Y' ≤ (2 * y ^ 2)^4 := by
    have : Y' < i^4 := by simpa [pow_four_eq_sq_sq] using append_lt (i ^ 2) Y hysqi
    exact le_trans (le_of_lt this) (pow_le_pow_left₀ (zero_le i) (le_trans hi <| by simp) 4)
  have hseq₀' : Seq₀ X' Y' :=
    hseq₀.append ppi.sq (ppi.sq.four_lt ppi.sq_ne_two (ppi.sq_ne_four ne2))
  have hseqₛ' : Seqₛ (2 * y ^ 2) X' Y' := by
    intro j hj jne2 ppj
    by_cases hjy : j ≤ y
    · have : Seqₛ y X' Y' := hseqₛ.append ppi (by simp [←hYy, ppi.pos])
      exact this j hjy jne2 ppj
    · have : i = j := by
        have : Pow2 y := by simpa [hYy] using pow2_ext_of_seq₀_of_seqₛ hseq₀ hseqₛ ne2 hi ppi
        exact PPow2.two_mul_sq_uniq this ppi ppj
          ⟨by simp [←hYy, ppi.pos], le_trans hi (by simp)⟩ ⟨by simpa using hjy, hj⟩
      rcases this with rfl
      right
      change ext (i ^ 2) (append (i ^ 2) X (2 * x + 1)) =
          2 * ext i (append (i ^ 2) X (2 * x + 1)) + 1 ∧
        ext (i ^ 2) (append (i ^ 2) Y (2 * y ^ 2)) =
          2 * ext i (append (i ^ 2) Y (2 * y ^ 2)) ^ 2
      constructor
      · calc
          ext (i ^ 2) (append (i ^ 2) X (2 * x + 1)) = 2 * x + 1 := ext_append_last (i ^ 2) X hxsqi
          _ = 2 * ext i (append (i ^ 2) X (2 * x + 1)) + 1 := by
            rw [ext_append_of_lt ppi ppi.sq hiisq X (2 * x + 1), hXx]
      · calc
          ext (i ^ 2) (append (i ^ 2) Y (2 * y ^ 2)) = 2 * y ^ 2 := ext_append_last (i ^ 2) Y hysqi
          _ = 2 * ext i (append (i ^ 2) Y (2 * y ^ 2)) ^ 2 := by
            rw [ext_append_of_lt ppi ppi.sq hiisq Y (2 * y ^ 2), hYy]
  have hseqₘ' : Seqₘ (2 * x + 1) (2 * y ^ 2) X' Y' :=
    ⟨i ^ 2, sq_le_sq.mpr (le_trans hi <| by simp), ppi.sq_ne_two, ppi.sq,
     by
       change ext (i ^ 2) (append (i ^ 2) X (2 * x + 1)) = 2 * x + 1 ∧
         ext (i ^ 2) (append (i ^ 2) Y (2 * y ^ 2)) = 2 * y ^ 2
       exact ⟨ext_append_last (i ^ 2) X hxsqi, ext_append_last (i ^ 2) Y hysqi⟩⟩
  exact Or.inr <| ⟨X', bX', Y', bY', hseq₀', hseqₛ', hseqₘ'⟩


-- @@ L536-538 verbatim
lemma exponential_odd {x y : V} :
    Exponential (2 * x + 1) y ↔ ∃ y', y = 2 * y' ^ 2 ∧ Exponential x y' :=
  ⟨exponential_exists_sq_of_exponential_odd, by rintro ⟨y, rfl, h⟩; exact bit_one h⟩


-- @@ L540-545 verbatim
lemma exponential_odd_two_mul_sq {x y : V} :
    Exponential (2 * x + 1) (2 * y ^ 2) ↔ Exponential x y :=
  ⟨by intro h
      rcases exponential_exists_sq_of_exponential_odd h with ⟨y', e, h⟩
      simpa [show y = y' from by simpa using e] using h,
   bit_one⟩


-- @@ L547-568 expanded
lemma two_le_ext_of_seq₀_of_seqₛ {y X Y : V} (h₀ : Exponential.Seq₀ X Y)
    (hₛ : Exponential.Seqₛ y X Y) {i} (ne2 : i ≠ 2) (hi : i ≤ y ^ 2) (ppi : PPow2 i) :
    2 ≤ ext i Y := by
  induction i using order_induction_sigma0
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case ind i IH =>
    by_cases ei : i = 4
    · rcases ei with rfl; simp [h₀.2]
    · have IH : 2 ≤ ext (sqrt i) Y :=
        IH (sqrt i) (sqrt_lt_self_of_one_lt ppi.one_lt) (ppi.sqrt_ne_two ne2 ei)
          (le_trans (by simp) hi) (ppi.sqrt ne2)
      rcases
        show Seqₛ.Even X Y (sqrt i) ∨ Seqₛ.Odd X Y (sqrt i) from
          hₛ (sqrt i) (sqrt_le_of_le_sq <| hi) (ppi.sqrt_ne_two ne2 ei) (ppi.sqrt ne2) with
        (heven | hodd)
      ·
        calc
          2 ≤ ext (sqrt i) Y := IH
          _ ≤ (ext (sqrt i) Y) ^ 2 := by simp
          _ = ext i Y := by simpa [ppi.sq_sqrt_eq ne2] using Eq.symm heven.2
      ·
        calc
          2 ≤ ext (sqrt i) Y := IH
          _ ≤ (ext (sqrt i) Y) ^ 2 := by simp
          _ ≤ 2 * (ext (sqrt i) Y) ^ 2 := by simp
          _ = ext i Y := by simpa [ppi.sq_sqrt_eq ne2] using Eq.symm hodd.2


-- @@ L570-603 expanded
lemma ext_le_ext_of_seq₀_of_seqₛ {y X Y : V} (h₀ : Exponential.Seq₀ X Y)
    (hₛ : Exponential.Seqₛ y X Y) {i} (ne2 : i ≠ 2) (hi : i ≤ y ^ 2) (ppi : PPow2 i) :
    ext i X < ext i Y := by
  induction i using order_induction_sigma0
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case ind i IH =>
    by_cases ne4 : i = 4
    · rcases ne4 with rfl; simp [h₀.1, h₀.2]
    · have IH : ext (sqrt i) X < ext (sqrt i) Y :=
        IH (sqrt i) (sqrt_lt_self_of_one_lt ppi.one_lt) (ppi.sqrt_ne_two ne2 ne4)
          (le_trans (by simp) hi) (ppi.sqrt ne2)
      rcases
        show Seqₛ.Even X Y (sqrt i) ∨ Seqₛ.Odd X Y (sqrt i) from
          hₛ (sqrt i) (sqrt_le_of_le_sq <| hi) (ppi.sqrt_ne_two ne2 ne4) (ppi.sqrt ne2) with
        (heven | hodd)
      ·
        calc
          ext i X = 2 * ext (sqrt i) X := by simpa [ppi.sq_sqrt_eq ne2] using heven.1
          _ < 2 * ext (sqrt i) Y := by simpa using IH
          _ ≤ ext (sqrt i) Y ^ 2 :=
            (two_mul_le_sq
              (two_le_ext_of_seq₀_of_seqₛ h₀ hₛ (ppi.sqrt_ne_two ne2 ne4) (le_trans (by simp) hi)
                (ppi.sqrt ne2)))
          _ = ext i Y := by simpa [ppi.sq_sqrt_eq ne2] using Eq.symm heven.2
      ·
        calc
          ext i X = 2 * ext (sqrt i) X + 1 := by simpa [ppi.sq_sqrt_eq ne2] using hodd.1
          _ < 2 * ext (sqrt i) Y + 1 := by simpa using IH
          _ ≤ 2 * ext (sqrt i) Y ^ 2 :=
            (lt_iff_succ_le.mp
              (by
                simp only [zero_lt_two, mul_lt_mul_iff_right₀]
                have hlarge : (1 : V) < ext (sqrt i) Y :=
                  lt_iff_succ_le.mpr <| by
                    simpa only [one_add_one_eq_two] using
                      two_le_ext_of_seq₀_of_seqₛ h₀ hₛ (ppi.sqrt_ne_two ne2 ne4)
                        (le_trans (by simp) hi) (ppi.sqrt ne2)
                simpa only [sq] using lt_mul_self hlarge))
          _ = ext i Y := by simpa [ppi.sq_sqrt_eq ne2] using Eq.symm hodd.2


-- @@ L605-609 verbatim
lemma range_pos {x y : V} (h : Exponential x y) : 0 < y := by
  rcases h with (⟨rfl, rfl⟩ | ⟨X, bX, Y, bY, H₀, Hₛ, ⟨u, hu, ne2, ppu, rfl, rfl⟩⟩)
  · simp
  · have : 2 ≤ ext u Y := two_le_ext_of_seq₀_of_seqₛ H₀ Hₛ ne2 hu ppu
    exact lt_of_lt_of_le (by simp) this


-- @@ L611-614 verbatim
lemma lt {x y : V} (h : Exponential x y) : x < y := by
  rcases h with (⟨rfl, rfl⟩ | ⟨X, bX, Y, bY, H₀, Hₛ, ⟨u, hu, ne2, ppu, rfl, rfl⟩⟩)
  · simp
  · exact ext_le_ext_of_seq₀_of_seqₛ H₀ Hₛ ne2 hu ppu


-- @@ L616-617 verbatim
lemma not_exponential_of_le {x y : V} (h : x ≤ y) : ¬Exponential y x := by
  intro hxy; exact not_le.mpr (lt hxy) h


-- @@ L619-623 verbatim
@[simp] lemma one_not_even (a : V) : 1 ≠ 2 * a := by
  intro h
  have : (2 : V) ∣ 1 := by rw [h]; simp
  have : ¬(2 : V) ∣ 1 := not_dvd_of_lt (by simp) one_lt_two
  contradiction


-- @@ L625-626 verbatim
@[simp] lemma exponential_two_four : Exponential (2 : V) 4 := by
  simpa [two_pow_two_eq_four] using (show Exponential (1 : V) 2 from by simp).bit_zero


-- @@ L628-679 expanded
lemma exponential_succ {x y : V} : Exponential (x + 1) y ↔ ∃ z, y = 2 * z ∧ Exponential x z :=
  by
  suffices x < y → (Exponential (x + 1) y ↔ ∃ z ≤ y, y = 2 * z ∧ Exponential x z)
    by
    by_cases hxy : x < y
    ·
      exact
        (this hxy).trans
          ⟨by rintro ⟨z, _, hzy, hz⟩; exact ⟨z, hzy, hz⟩, by rintro ⟨z, rfl, hz⟩;
            exact ⟨z, le_two_mul_left, rfl, hz⟩⟩
    · have hyx : y ≤ x + 1 := le_add_right (by simpa using hxy)
      constructor
      · intro h
        exact False.elim <| not_exponential_of_le hyx h
      · rintro ⟨z, rfl, hz⟩
        exact
          False.elim <| not_exponential_of_le (le_trans le_two_mul_left <| by simpa using hxy) hz
  · revert x
    induction y using order_induction_sigma0
    · aesop  (config := { terminal := true })  (rule_sets := [Definability])
    case ind y IH =>
      intro x hxy
      rcases even_or_odd x with ⟨x, (rfl | rfl)⟩
      · constructor
        · intro H
          rcases exponential_odd.mp H with ⟨y, rfl, H'⟩
          exact ⟨y ^ 2, by simp, rfl, H'.bit_zero⟩
        · rintro ⟨y, hy, rfl, H⟩
          rcases exponential_even.mp H with ⟨y, rfl, H'⟩
          exact H'.bit_one
      · constructor
        · intro H
          have : Exponential (2 * (x + 1)) y := by
            simpa [mul_add, add_assoc, one_add_one_eq_two] using H
          rcases exponential_even.mp this with ⟨y, rfl, H'⟩
          have : 1 < y := by simpa using (show 1 < y ^ 2 from lt_of_le_of_lt (by simp) hxy)
          have : Exponential (x + 1) y ↔ ∃ z ≤ y, y = 2 * z ∧ Exponential x z :=
            IH y (lt_square_of_lt <| this) (lt_trans (by simp) H'.lt)
          rcases this.mp H' with ⟨y, _, rfl, H''⟩
          exact
            ⟨2 * y ^ 2, by simp [sq, mul_assoc, mul_left_comm y 2], by
              simp [sq, mul_assoc, mul_left_comm y 2], H''.bit_one⟩
        · rintro ⟨y, _, rfl, H⟩
          rcases exponential_odd.mp H with ⟨y, rfl, H'⟩
          by_cases ne1 : y = 1
          · rcases ne1 with rfl
            rcases (show x = 0 from by simpa using H'.lt)
            simp [one_add_one_eq_two, two_mul_two_eq_four]
          have : y < y ^ 2 := lt_square_of_lt <| one_lt_iff_two_le.mpr <| H'.range_pow2.two_le ne1
          have : Exponential (x + 1) (2 * y) ↔ ∃ z ≤ 2 * y, 2 * y = 2 * z ∧ Exponential x z :=
            IH (2 * y)
              (by
                simp only [zero_lt_two, mul_lt_mul_iff_right₀]
                exact lt_of_lt_of_le this le_two_mul_left)
              (lt_of_lt_of_le H'.lt <| by simp)
          have : Exponential (x + 1) (2 * y) := this.mpr ⟨y, by simp, rfl, H'⟩
          simpa [sq, mul_add, add_assoc, mul_assoc, one_add_one_eq_two, mul_left_comm y 2] using
            this.bit_zero


-- @@ L681-683 verbatim
lemma exponential_succ_mul_two {x y : V} : Exponential (x + 1) (2 * y) ↔ Exponential x y :=
  ⟨by intro h; rcases exponential_succ.mp h with ⟨y', e, h⟩; simp_all,
   by intro h; exact exponential_succ.mpr ⟨y, rfl, h⟩⟩


-- @@ L685-685 verbatim
alias ⟨of_succ_two_mul, succ⟩ := exponential_succ_mul_two


-- @@ L687-704 expanded
lemma one_le_ext_of_seq₀_of_seqₛ {y X Y : V} (h₀ : Exponential.Seq₀ X Y)
    (hₛ : Exponential.Seqₛ y X Y) {i} (ne2 : i ≠ 2) (hi : i ≤ y ^ 2) (ppi : PPow2 i) :
    1 ≤ ext i X := by
  induction i using order_induction_sigma0
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case ind i IH =>
    by_cases ne4 : i = 4
    · rcases ne4 with rfl; simp [h₀.1]
    · have IH : 1 ≤ ext (sqrt i) X :=
        IH (sqrt i) (sqrt_lt_self_of_one_lt ppi.one_lt) (ppi.sqrt_ne_two ne2 ne4)
          (le_trans (by simp) hi) (ppi.sqrt ne2)
      rcases
        show Seqₛ.Even X Y (sqrt i) ∨ Seqₛ.Odd X Y (sqrt i) from
          hₛ (sqrt i) (sqrt_le_of_le_sq <| hi) (ppi.sqrt_ne_two ne2 ne4) (ppi.sqrt ne2) with
        (heven | hodd)
      · have : ext i X = 2 * ext (sqrt i) X := by simpa [ppi.sq_sqrt_eq ne2] using heven.1
        exact le_trans IH (by simp [this])
      · have : ext i X = 2 * ext (sqrt i) X + 1 := by simpa [ppi.sq_sqrt_eq ne2] using hodd.1
        simp [this]


-- @@ L706-710 verbatim
lemma zero_uniq {y : V} (h : Exponential 0 y) : y = 1 := by
  rcases h with (⟨_, rfl⟩ | ⟨X, _, Y, _, H₀, Hₛ, ⟨u, hu, ne2, ppu, hX, _⟩⟩)
  · rfl
  · have : 1 ≤ ext u X  := one_le_ext_of_seq₀_of_seqₛ H₀ Hₛ ne2 hu ppu
    simp [hX] at this


-- @@ L712-713 verbatim
@[simp] lemma zero_uniq_iff {y : V} : Exponential 0 y ↔ y = 1 :=
  ⟨zero_uniq, by rintro rfl; simp⟩


-- @@ L715-718 verbatim
lemma succ_lt_s {y : V} (h : Exponential (x + 1) y) : 2 ≤ y := by
  rcases h with (⟨h, rfl⟩ | ⟨X, _, Y, _, H₀, Hₛ, ⟨u, hu, ne2, ppu, _, hY⟩⟩)
  · simp at h
  · simpa [hY] using two_le_ext_of_seq₀_of_seqₛ H₀ Hₛ ne2 hu ppu


-- @@ L720-737 expanded
protected lemma uniq {x y₁ y₂ : V} : Exponential x y₁ → Exponential x y₂ → y₁ = y₂ :=
  by
  intro h₁ h₂
  wlog h : y₁ ≤ y₂
  · exact Eq.symm <| this h₂ h₁ (show y₂ ≤ y₁ from le_of_not_ge h)
  revert x h y₁
  suffices ∀ x < y₂, ∀ y₁ ≤ y₂, Exponential x y₁ → Exponential x y₂ → y₁ = y₂ by
    intro x y₁ h₁ h₂ hy; exact this x h₂.lt y₁ hy h₁ h₂
  induction y₂ using order_induction_sigma0
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case ind y₂ IH =>
    intro x _ y₁ h h₁ h₂
    rcases zero_or_succ x with (rfl | ⟨x, rfl⟩)
    · simp [h₁.zero_uniq, h₂.zero_uniq]
    · rcases exponential_succ.mp h₁ with ⟨y₁, rfl, h₁'⟩
      rcases exponential_succ.mp h₂ with ⟨y₂, rfl, h₂'⟩
      have : y₁ = y₂ :=
        IH y₂ (lt_mul_of_pos_of_one_lt_left h₂'.range_pos one_lt_two) x h₂'.lt y₁ (by simpa using h)
          h₁' h₂'
      simp [this]


-- @@ L739-757 expanded
protected lemma inj {x₁ x₂ y : V} : Exponential x₁ y → Exponential x₂ y → x₁ = x₂ :=
  by
  intro h₁ h₂
  revert x₁ x₂ h₁ h₂
  suffices ∀ x₁ < y, ∀ x₂ < y, Exponential x₁ y → Exponential x₂ y → x₁ = x₂ by intro x₁ x₂ h₁ h₂;
    exact this x₁ h₁.lt x₂ h₂.lt h₁ h₂
  induction y using order_induction_sigma0
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case ind y IH =>
    intro x₁ _ x₂ _ h₁ h₂
    rcases zero_or_succ x₁ with (rfl | ⟨x₁, rfl⟩) <;> rcases zero_or_succ x₂ with (rfl | ⟨x₂, rfl⟩)
    · rfl
    · simp_all
    · simp_all
    · rcases exponential_succ.mp h₁ with ⟨y, rfl, hy₁⟩
      have hy₂ : Exponential x₂ y := h₂.of_succ_two_mul
      have : x₁ = x₂ :=
        IH y (lt_mul_of_pos_of_one_lt_left hy₁.range_pos one_lt_two) x₁ hy₁.lt x₂ hy₂.lt hy₁ hy₂
      simp [this]


-- @@ L759-768 verbatim
lemma exponential_elim {x y : V} :
    Exponential x y ↔ (x = 0 ∧ y = 1) ∨ ∃ x', ∃ y', x = x' + 1 ∧ y = 2 * y' ∧ Exponential x' y' :=
  ⟨by intro h
      rcases zero_or_succ x with (rfl | ⟨x', rfl⟩)
      · simp [h.zero_uniq]
      · right; rcases exponential_succ.mp h with ⟨y', rfl, H⟩
        exact ⟨x', y', rfl, rfl, H⟩,
   by rintro (⟨rfl, rfl⟩ | ⟨x, y, rfl, rfl, h⟩)
      · simp
      · exact h.succ⟩


-- @@ L770-790 expanded
lemma monotone {x₁ x₂ y₁ y₂ : V} : Exponential x₁ y₁ → Exponential x₂ y₂ → x₁ < x₂ → y₁ < y₂ :=
  by
  suffices ∀ x₁ < y₁, ∀ y₂ ≤ y₁, ∀ x₂ < y₂, Exponential x₁ y₁ → Exponential x₂ y₂ → x₂ ≤ x₁
    by
    intro h₁ h₂; contrapose; simp only [not_lt]
    intro hy
    exact this x₁ h₁.lt y₂ hy x₂ h₂.lt h₁ h₂
  induction y₁ using order_induction_sigma0
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case ind y₁ IH =>
    intro x₁ _ y₂ hy x₂ _ h₁ h₂
    rcases zero_or_succ x₁ with (rfl | ⟨x₁, rfl⟩) <;> rcases zero_or_succ x₂ with (rfl | ⟨x₂, rfl⟩)
    · simp
    · rcases show y₁ = 1 from h₁.zero_uniq
      rcases le_one_iff_eq_zero_or_one.mp hy with (rfl | rfl)
      · have := h₂.range_pos; simp at this
      · exact False.elim <| not_lt.mpr h₂.succ_lt_s one_lt_two
    · simp
    · rcases exponential_succ.mp h₁ with ⟨y₁, rfl, h₁'⟩
      rcases exponential_succ.mp h₂ with ⟨y₂, rfl, h₂'⟩
      have : x₂ ≤ x₁ :=
        IH y₁ (lt_mul_of_pos_of_one_lt_left h₁'.range_pos one_lt_two) x₁ h₁'.lt y₂
          (le_of_mul_le_mul_left hy (by simp)) x₂ h₂'.lt h₁' h₂'
      simpa using this


-- @@ L792-796 verbatim
lemma monotone_le {x₁ x₂ y₁ y₂ : V} (h₁ : Exponential x₁ y₁) (h₂ : Exponential x₂ y₂) :
    x₁ ≤ x₂ → y₁ ≤ y₂ := by
  rintro (rfl | h)
  · exact (h₁.uniq h₂).le
  · exact le_of_lt (monotone h₁ h₂ h)


-- @@ L798-802 verbatim
lemma monotone_iff {x₁ x₂ y₁ y₂ : V} (h₁ : Exponential x₁ y₁) (h₂ : Exponential x₂ y₂) :
    x₁ < x₂ ↔ y₁ < y₂ := by
  constructor
  · exact monotone h₁ h₂
  · contrapose; simp only [not_lt]; exact monotone_le h₂ h₁


-- @@ L804-808 verbatim
lemma monotone_le_iff {x₁ x₂ y₁ y₂ : V} (h₁ : Exponential x₁ y₁) (h₂ : Exponential x₂ y₂) :
    x₁ ≤ x₂ ↔ y₁ ≤ y₂ := by
  constructor
  · exact monotone_le h₁ h₂
  · contrapose; simp only [not_le]; exact monotone h₂ h₁


-- @@ L810-825 expanded
lemma add_mul {x₁ x₂ y₁ y₂ : V} (h₁ : Exponential x₁ y₁) (h₂ : Exponential x₂ y₂) :
    Exponential (x₁ + x₂) (y₁ * y₂) := by
  wlog hy : y₁ ≥ y₂
  · simpa [add_comm, mul_comm] using this h₂ h₁ (le_of_not_ge hy)
  revert y₂
  suffices ∀ y₂ ≤ y₁, Exponential x₂ y₂ → Exponential (x₁ + x₂) (y₁ * y₂) by intro y₂ h₂ hy;
    exact this y₂ hy h₂
  induction x₂ using induction_sigma0
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case zero => simp_all
  case succ x₂ IH =>
    intro y₂ hy h₂
    rcases exponential_succ.mp h₂ with ⟨y₂, rfl, H₂⟩
    have : Exponential (x₁ + x₂) (y₁ * y₂) := IH y₂ (le_trans (by simp) hy) H₂
    simpa [← add_assoc, mul_left_comm y₁ 2 y₂] using this.succ


-- @@ L827-827 verbatim
end Exponential


-- @@ L829-829 verbatim
end «lp_section_1»


-- @@ L831-831 verbatim
section «lp_section_2»


-- @@ L833-833 expanded
variable [ModelsTheory V (iSigma 1)]


-- @@ L835-835 verbatim
namespace Exponential


-- @@ L837-843 expanded
lemma range_exists (x : V) : ∃ y, Exponential x y :=
  by
  induction x using induction_sigma1
  · aesop  (config := { terminal := true })  (rule_sets := [Definability])
  case zero => exact ⟨1, by simp⟩
  case succ x IH =>
    rcases IH with ⟨y, IH⟩
    exact ⟨2 * y, IH.succ⟩


-- @@ L845-847 verbatim
lemma range_exists_unique (x : V) : ∃! y, Exponential x y := by
  rcases range_exists x with ⟨y, h⟩
  exact ExistsUnique.intro y h (by intro y' h'; exact h'.uniq h)


-- @@ L849-849 verbatim
end Exponential


-- @@ L851-851 verbatim
instance : Exp V := ⟨fun a ↦ Classical.choose! (Exponential.range_exists_unique a)⟩


-- @@ L853-853 verbatim
section «lp_section_3»


-- @@ L855-857 expanded
lemma exponential_exp (a : V) : Exponential a (Exp.exp a) :=
  Classical.choose!_spec (Exponential.range_exists_unique a)


-- @@ L859-859 expanded
lemma exponential_graph {a b : V} : a = Exp.exp b ↔ Exponential b a :=
  Classical.choose!_eq_iff _


-- @@ L861-864 expanded
/-- Imported declaration from the Incompleteness formalization. -/
def _root_.LO.FirstOrder.Arith.expDef : Sg0.Semisentence 2 :=
  .mkSigma (LO.FirstOrder.Rewriting.substitute exponentialDef.val (vecCons (#1) (vecCons #0 ![])))
    (by simp)


-- @@ L866-867 expanded
lemma exp_defined_deltaZero : DefinedFunction₁ Sg0 (Exp.exp : V → V) expDef := by intro v;
  simp [expDef, exponential_graph]


-- @@ L869-870 verbatim
@[simp] lemma exp_defined_iff (v) :
    Semiformula.Evalbm V v expDef.val ↔ v 0 = Exp.exp (v 1) := exp_defined_deltaZero.df.iff v


-- @@ L872-874 expanded
instance exp_definable_deltaZero : BoldfaceFunction₁ Sg0 (Exp.exp : V → V) :=
  exp_defined_deltaZero.to_definable


-- @@ L876-877 expanded
lemma exp_of_exponential {a b : V} (h : Exponential a b) : Exp.exp a = b :=
  Eq.symm <| exponential_graph.mpr h


-- @@ L879-880 verbatim
lemma exp_inj : Function.Injective (Exp.exp : V → V) := fun a _ H ↦
  (exponential_exp a).inj (exponential_graph.mp H)


-- @@ L882-882 expanded
@[simp]
lemma exp_zero : Exp.exp (0 : V) = 1 :=
  exp_of_exponential (by simp)


-- @@ L884-884 expanded
@[simp]
lemma exp_one : Exp.exp (1 : V) = 2 :=
  exp_of_exponential (by simp)


-- @@ L886-887 expanded
lemma exp_succ (a : V) : Exp.exp (a + 1) = 2 * Exp.exp a :=
  exp_of_exponential <| Exponential.exponential_succ_mul_two.mpr <| exponential_exp a


-- @@ L889-890 expanded
lemma exp_even (a : V) : Exp.exp (2 * a) = (Exp.exp a) ^ 2 :=
  exp_of_exponential <| Exponential.exponential_even_sq.mpr <| exponential_exp a


-- @@ L892-892 expanded
@[simp]
lemma lt_exp (a : V) : a < Exp.exp a :=
  (exponential_exp a).lt


-- @@ L894-894 expanded
@[simp]
lemma exp_pos (a : V) : 0 < Exp.exp a :=
  (exponential_exp a).range_pos


-- @@ L896-896 expanded
@[simp]
lemma one_le_exp (a : V) : 1 ≤ Exp.exp a :=
  pos_iff_one_le.mp (by simp)


-- @@ L898-898 expanded
@[simp]
lemma exp_pow2 (a : V) : Pow2 (Exp.exp a) :=
  (exponential_exp a).range_pow2


-- @@ L900-901 expanded
@[simp]
lemma exp_monotone {a b : V} : Exp.exp a < Exp.exp b ↔ a < b :=
  Iff.symm <| Exponential.monotone_iff (exponential_exp a) (exponential_exp b)


-- @@ L903-904 expanded
@[simp]
lemma exp_monotone_le {a b : V} : Exp.exp a ≤ Exp.exp b ↔ a ≤ b :=
  Iff.symm <| Exponential.monotone_le_iff (exponential_exp a) (exponential_exp b)


-- @@ L906-913 expanded
lemma nat_cast_exp (n : ℕ) : (Exp.exp n : ℕ) = Exp.exp (n : V) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [Nat.cast_add, Nat.cast_one]
    rw [exp_succ, exp_succ, ← ih]
    simp only [Nat.cast_mul, mul_eq_mul_right_iff, Nat.cast_eq_zero]
    exact Or.inl rfl


-- @@ L915-915 verbatim
end «lp_section_3»


-- @@ L917-917 verbatim
end «lp_section_2»


-- @@ L919-919 verbatim
end Arith

-- @@ L920-920 verbatim
end LO


-- @@ L922-922 verbatim
end «lp_nc_section_1»
