import Seymour.Basic.Basic


-- @@ L3-7 verbatim
/-!
# Fin

This file provides lemmas about 1-element, 2-element, and 3-element types that are not present in Mathlib.
-/



-- @@ L10-11 verbatim
lemma fin1_eq_fin1 (a b : Fin 1) : a = b := by
  omega


-- @@ L13-14 verbatim
lemma fin2_eq_1_of_ne_0 {a : Fin 2} (ha : a ≠ 0) : a = 1 := by
  omega


-- @@ L16-17 verbatim
lemma fin2_eq_0_of_ne_1 {a : Fin 2} (ha : a ≠ 1) : a = 0 := by
  omega


-- @@ L19-20 verbatim
lemma fin3_eq_2_of_ne_0_1 {a : Fin 3} (ha0 : a ≠ 0) (ha1 : a ≠ 1) : a = 2 := by
  omega


-- @@ L22-23 verbatim
lemma fin3_eq_1_of_ne_0_2 {a : Fin 3} (ha0 : a ≠ 0) (ha2 : a ≠ 2) : a = 1 := by
  omega


-- @@ L25-26 verbatim
lemma fin3_eq_0_of_ne_1_2 {a : Fin 3} (ha1 : a ≠ 1) (ha2 : a ≠ 2) : a = 0 := by
  omega


-- @@ L28-30 verbatim
@[aesop unsafe 50% forward]
lemma Z2_eq_1_of_ne_0 {a : Z2} (ha : a ≠ 0) : a = 1 :=
  fin2_eq_1_of_ne_0 ha


-- @@ L32-34 verbatim
@[aesop unsafe 50% forward]
lemma Z2_eq_0_of_ne_1 {a : Z2} (ha : a ≠ 1) : a = 0 :=
  fin2_eq_0_of_ne_1 ha


-- @@ L36-37 verbatim
lemma Z3_eq_2_of_ne_0_1 {a : Z3} (ha0 : a ≠ 0) (ha1 : a ≠ 1) : a = 2 :=
  fin3_eq_2_of_ne_0_1 ha0 ha1


-- @@ L39-40 verbatim
lemma Z3_eq_1_of_ne_0_2 {a : Z3} (ha0 : a ≠ 0) (ha2 : a ≠ 2) : a = 1 :=
  fin3_eq_1_of_ne_0_2 ha0 ha2


-- @@ L42-43 verbatim
lemma Z3_eq_0_of_ne_1_2 {a : Z3} (ha1 : a ≠ 1) (ha2 : a ≠ 2) : a = 0 :=
  fin3_eq_0_of_ne_1_2 ha1 ha2


-- @@ L45-54 verbatim
lemma Z2.eq_0_or_1 (a : Z2) : a = 0 ∨ a = 1 := by
  rw [←ZMod.val_eq_zero]
  by_cases ha : a.val = 0
  · left
    exact ha
  · fin_cases a
    · exfalso
      exact ha rfl
    · right
      rfl


-- @@ L56-60 verbatim
lemma Z2_ext {a b : Z2} (hab : a.val = b.val) : a = b := by
  cases a
  cases b
  simp only [ZMod.val, Nat.reduceAdd] at hab
  simp only [hab]


-- @@ L62-65 verbatim
lemma Z2_ext_iff (a b : Z2) : a = b ↔ a.val = b.val := by
  constructor
  · exact congr_arg ZMod.val
  · exact Z2_ext


-- @@ L67-72 verbatim
lemma Z2.valCast_in_signTypeCastRange (x : Z2) :
    (x.val.cast : ℚ) ∈ SignType.cast.range := by
  rcases x.eq_0_or_1 with hx | hx
  <;> rw [hx]
  <;> [use SignType.zero; use SignType.pos]
  <;> rfl


-- @@ L74-76 verbatim
@[simp]
lemma cast_1_fromZ2_toRat : ZMod.cast (1 : Z2) = (1 : ℚ) := by
  decide


-- @@ L78-79 verbatim
lemma Z2_mul_cast_toRat (a b : Z2) : ((a * b).cast : ℚ) = (a.cast : ℚ) * (b.cast : ℚ) := by
  cases a.eq_0_or_1 <;> cases b.eq_0_or_1 <;> simp [*]


-- @@ L81-94 verbatim
lemma abs_mul_eq_zmod_cast {a b : Z2} {a' b' : ℚ} (haa : |a'| = a.cast) (hbb : |b'| = b.cast) :
    |a' * b'| = (a * b).cast := by
  cases a.eq_0_or_1 with
  | inl ha0 =>
    simp [ha0] at haa
    simp [ha0, haa]
  | inr ha1 =>
    cases b.eq_0_or_1 with
    | inl hb0 =>
      simp [hb0] at hbb
      simp [hb0, hbb]
    | inr hb1 =>
      rw [abs_mul, haa, hbb]
      exact (Z2_mul_cast_toRat a b).symm


-- @@ L96-116 verbatim
lemma abs_add_eq_zmod_cast {a b : Z2} {a' b' : ℚ} (haa : |a'| = a.cast) (hbb : |b'| = b.cast)
    (hab : a' + b' ∈ SignType.cast.range) :
    |a' + b'| = (a + b).cast := by
  cases a.eq_0_or_1 with
  | inl ha0 =>
    rw [ha0, ZMod.cast_zero, abs_eq_zero] at haa
    rw [ha0, haa, zero_add, zero_add, hbb]
  | inr ha1 =>
    cases b.eq_0_or_1 with
    | inl hb0 =>
      rw [hb0, ZMod.cast_zero, abs_eq_zero] at hbb
      rw [hb0, hbb, add_zero, add_zero, haa]
    | inr hb1 =>
      rw [ha1, cast_1_fromZ2_toRat, abs_eq rfl] at haa
      rw [hb1, cast_1_fromZ2_toRat, abs_eq rfl] at hbb
      rw [ha1, hb1, show (1 : Z2) + (1 : Z2) = (0 : Z2) by rfl, ZMod.cast_zero, abs_eq_zero]
      cases haa <;> cases hbb <;> simp_all
      all_goals
        exfalso
        obtain ⟨s, hs⟩ := hab
        cases s <;> norm_num at hs


-- @@ L118-150 verbatim
lemma abs_add_add_eq_zmod_cast {a b c : Z2} {a' b' c' : ℚ} (haa : |a'| = a.cast) (hbb : |b'| = b.cast) (hcc : |c'| = c.cast)
    (habc : a' + b' + c' ∈ SignType.cast.range) :
    |a' + b' + c'| = (a + b + c).cast := by
  cases a.eq_0_or_1 with
  | inl ha0 =>
    rw [ha0, ZMod.cast_zero, abs_eq_zero] at haa
    rw [haa, zero_add] at habc ⊢
    rw [ha0, zero_add]
    exact abs_add_eq_zmod_cast hbb hcc habc
  | inr ha1 =>
    cases b.eq_0_or_1 with
    | inl hb0 =>
      rw [hb0, ZMod.cast_zero, abs_eq_zero] at hbb
      rw [hbb, add_zero] at habc ⊢
      rw [hb0, add_zero]
      exact abs_add_eq_zmod_cast haa hcc habc
    | inr hb1 =>
      cases c.eq_0_or_1 with
      | inl hc0 =>
        rw [hc0, ZMod.cast_zero, abs_eq_zero] at hcc
        rw [hcc, add_zero] at habc ⊢
        rw [hc0, add_zero]
        exact abs_add_eq_zmod_cast haa hbb habc
      | inr hc1 =>
        rw [ha1, cast_1_fromZ2_toRat, abs_eq rfl] at haa
        rw [hb1, cast_1_fromZ2_toRat, abs_eq rfl] at hbb
        rw [hc1, cast_1_fromZ2_toRat, abs_eq rfl] at hcc
        rw [ha1, hb1, hc1, show (1 : Z2) + (1 : Z2) + (1 : Z2) = (1 : Z2) by rfl, cast_1_fromZ2_toRat]
        cases haa <;> cases hbb <;> cases hcc <;> simp_all
        all_goals
          exfalso
          obtain ⟨s, hs⟩ := habc
          cases s <;> norm_num at hs


-- @@ L152-154 expanded
@[simp]
def equivUnitSumUnit : Unit ⊕ Unit ≃ Fin 2 :=
  ⟨(·.casesOn (fun _ => 0) (fun _ => 1)), ![Sum.inl (), Sum.inr ()],
    (·.casesOn (by simp) (by simp)), (by fin_cases · <;> simp)⟩


-- @@ L156-156 verbatim
noncomputable abbrev fin2refl : Fin 2 ≃ Fin 2 := Equiv.refl (Fin 2)

-- @@ L157-157 verbatim
noncomputable abbrev fin2swap : Fin 2 ≃ Fin 2 := Equiv.ofBijective ![1, 0] (by decide)


-- @@ L159-159 verbatim
@[simp] lemma fin2refl_apply_0 : fin2refl 0 = 0 := rfl

-- @@ L160-160 verbatim
@[simp] lemma fin2refl_apply_1 : fin2refl 1 = 1 := rfl

-- @@ L161-161 verbatim
@[simp] lemma fin2swap_apply_0 : fin2swap 0 = 1 := rfl

-- @@ L162-162 verbatim
@[simp] lemma fin2swap_apply_1 : fin2swap 1 = 0 := rfl


-- @@ L164-164 verbatim
@[simp] lemma fin2refl_symm : fin2refl.symm = fin2refl := rfl

-- @@ L165-168 verbatim
@[simp] lemma fin2swap_symm : fin2swap.symm = fin2swap := by
  rw [Function.Involutive.symm_eq_self_of_involutive]
  intro i
  fin_cases i <;> decide


-- @@ L170-170 verbatim
@[simp] lemma fin2swap_comp_fin2swap : fin2swap ∘ fin2swap = id := by decide

-- @@ L171-171 verbatim
@[simp] lemma fin2swap_trans_fin2swap : fin2swap.trans fin2swap = fin2refl := by decide


-- @@ L173-194 verbatim
lemma eq_fin2swap_of_ne_fin2refl {e : Fin 2 ≃ Fin 2} (he : e ≠ fin2refl) : e = fin2swap := by
  if he0 : e 0 = 0 then
    if he1 : e 1 = 1 then
      exfalso
      apply he
      ext i
      fin_cases i <;> tauto
    else
      have he10 := fin2_eq_0_of_ne_1 he1
      have hee := he0.trans he10.symm
      have he01 := e.injective hee
      norm_num at he01
  else
    have he01 := fin2_eq_1_of_ne_0 he0
    if he1 : e 1 = 1 then
      have hee := he1.trans he01.symm
      have he10 := e.injective hee
      norm_num at he10
    else
      have he10 := fin2_eq_0_of_ne_1 he1
      ext i
      fin_cases i <;> tauto
