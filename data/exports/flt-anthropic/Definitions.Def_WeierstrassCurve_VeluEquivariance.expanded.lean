import Mathlib
import Definitions.Def_WeierstrassCurve_VeluBundledMap


-- @@ L4-4 verbatim
open Polynomial


-- @@ L6-6 verbatim
namespace WeierstrassCurve


-- @@ L8-8 verbatim
section BaseChange


-- @@ L10-10 verbatim
variable {R : Type*} {A : Type*} [CommRing R] [CommRing A] (W : WeierstrassCurve R) (f : R →+* A)


-- @@ L12-13 verbatim
local macro "map_simp" : tactic =>
  `(tactic| simp only [map_ofNat, map_neg, map_add, map_sub, map_mul, map_pow])


-- @@ L15-18 verbatim
@[simp] lemma map_veluGx (x y : R) :
    (W.map f).veluGx (f x) (f y) = f (W.veluGx x y) := by
  simp only [veluGx, map_a₁, map_a₂, map_a₄]
  map_simp


-- @@ L20-23 verbatim
@[simp] lemma map_veluGy (x y : R) :
    (W.map f).veluGy (f x) (f y) = f (W.veluGy x y) := by
  simp only [veluGy, map_a₁, map_a₃]
  map_simp


-- @@ L25-28 verbatim
@[simp] lemma map_veluT (x y : R) :
    (W.map f).veluT (f x) (f y) = f (W.veluT x y) := by
  simp only [veluT_eq, map_b₂, map_b₄]
  map_simp


-- @@ L30-32 verbatim
@[simp] lemma map_veluU (x y : R) :
    (W.map f).veluU (f x) (f y) = f (W.veluU x y) := by
  simp only [veluU, map_veluGy, map_pow]


-- @@ L34-36 verbatim
@[simp] lemma map_veluW (x y : R) :
    (W.map f).veluW (f x) (f y) = f (W.veluW x y) := by
  simp only [veluW, map_veluU, map_veluT, map_add, map_mul]


-- @@ L38-42 verbatim
lemma map_veluTSum (S : Finset (R × R)) (hf : Function.Injective f) :
    (W.map f).veluTSum (S.map ⟨Prod.map f f, hf.prodMap hf⟩) = f (W.veluTSum S) := by
  rw [veluTSum, veluTSum, Finset.sum_map, map_sum]
  exact Finset.sum_congr rfl fun P _ => by
    simp only [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluT]


-- @@ L44-48 verbatim
lemma map_veluWSum (S : Finset (R × R)) (hf : Function.Injective f) :
    (W.map f).veluWSum (S.map ⟨Prod.map f f, hf.prodMap hf⟩) = f (W.veluWSum S) := by
  rw [veluWSum, veluWSum, Finset.sum_map, map_sum]
  exact Finset.sum_congr rfl fun P _ => by
    simp only [Function.Embedding.coeFn_mk, Prod.map_fst, Prod.map_snd, map_veluW]


-- @@ L50-52 verbatim
@[simp] lemma map_veluTSum_singleton (x₀ y₀ : R) :
    (W.map f).veluTSum {(f x₀, f y₀)} = f (W.veluTSum {(x₀, y₀)}) := by
  simp only [veluTSum, Finset.sum_singleton, map_veluT]


-- @@ L54-56 verbatim
@[simp] lemma map_veluWSum_singleton (x₀ y₀ : R) :
    (W.map f).veluWSum {(f x₀, f y₀)} = f (W.veluWSum {(x₀, y₀)}) := by
  simp only [veluWSum, Finset.sum_singleton, map_veluW]


-- @@ L58-67 verbatim
lemma map_veluQuotient (S : Finset (R × R)) (hf : Function.Injective f) :
    (W.map f).veluQuotient (S.map ⟨Prod.map f f, hf.prodMap hf⟩) = (W.veluQuotient S).map f := by
  ext
  · simp [veluQuotient]
  · simp [veluQuotient]
  · simp [veluQuotient]
  · simp only [veluQuotient_a₄, map_a₄, map_veluTSum _ _ S hf]
    map_simp
  · simp only [veluQuotient_a₆, map_a₆, map_b₂, map_veluTSum _ _ S hf, map_veluWSum _ _ S hf]
    map_simp


-- @@ L69-78 verbatim
lemma map_veluQuotient_singleton (x₀ y₀ : R) :
    (W.map f).veluQuotient {(f x₀, f y₀)} = (W.veluQuotient {(x₀, y₀)}).map f := by
  ext
  · simp [veluQuotient]
  · simp [veluQuotient]
  · simp [veluQuotient]
  · simp only [veluQuotient_a₄, map_a₄, map_veluTSum_singleton]
    map_simp
  · simp only [veluQuotient_a₆, map_a₆, map_b₂, map_veluTSum_singleton, map_veluWSum_singleton]
    map_simp


-- @@ L80-80 verbatim
end BaseChange


-- @@ L82-82 verbatim
section FieldBaseChange


-- @@ L84-84 verbatim
variable {F F' : Type*} [Field F] [Field F'] (W : WeierstrassCurve F) (f : F →+* F')


-- @@ L86-89 verbatim
lemma map_veluX_singleton (x₀ y₀ x : F) :
    (W.map f).veluX {(f x₀, f y₀)} (f x) = f (W.veluX {(x₀, y₀)} x) := by
  simp only [veluX, Finset.sum_singleton, map_veluT, map_veluU, map_add, map_div₀, map_sub,
    map_pow]


-- @@ L91-94 verbatim
lemma map_veluY_singleton (x₀ y₀ x y : F) :
    (W.map f).veluY {(f x₀, f y₀)} (f x) (f y) = f (W.veluY {(x₀, y₀)} x y) := by
  simp only [veluY, Finset.sum_singleton, map_veluT, map_veluU, map_veluGx, map_veluGy,
    map_a₁, map_a₃, map_add, map_sub, map_mul, map_div₀, map_pow, map_ofNat]


-- @@ L96-96 verbatim
end FieldBaseChange


-- @@ L98-98 verbatim
section Representative


-- @@ L100-100 verbatim
variable {F : Type*} [Field F] (W : WeierstrassCurve F)


-- @@ L102-104 verbatim
lemma veluX_singleton_negY (x₀ y₀ x : F) :
    W.veluX {(x₀, W.toAffine.negY x₀ y₀)} x = W.veluX {(x₀, y₀)} x := by
  simp only [veluX, Finset.sum_singleton, veluT_negY, veluU_negY]


-- @@ L106-114 verbatim
lemma veluY_singleton_negY (x₀ y₀ x y : F) :
    W.veluY {(x₀, W.toAffine.negY x₀ y₀)} x y = W.veluY {(x₀, y₀)} x y := by
  rcases eq_or_ne x x₀ with h | h
  · subst h
    simp [veluY, sub_self]
  · have hd : x - x₀ ≠ 0 := sub_ne_zero.mpr h
    simp only [veluY, Finset.sum_singleton, veluT, veluU, veluGx, veluGy, Affine.negY]
    field_simp
    ring


-- @@ L116-116 verbatim
end Representative


-- @@ L118-118 verbatim
section Galois


-- @@ L120-120 verbatim
variable {F : Type*} [Field F] {W : WeierstrassCurve F} {σ : F →+* F}


-- @@ L122-127 verbatim
private lemma sigma_y₀_eq_or_eq_negY (hW : W.map σ = W) {x₀ y₀ : F}
    (hQ : W.toAffine.Equation x₀ y₀) (hx₀ : σ x₀ = x₀) :
    σ y₀ = y₀ ∨ σ y₀ = W.toAffine.negY x₀ y₀ := by
  have h1 : (W.map σ).toAffine.Equation (σ x₀) (σ y₀) := Affine.Equation.map σ hQ
  rw [hW, hx₀] at h1
  exact Affine.Y_eq_of_X_eq h1 hQ rfl


-- @@ L129-138 verbatim
theorem veluQuotient_singleton_map_self (hW : W.map σ = W) {x₀ y₀ : F}
    (hQ : W.toAffine.Equation x₀ y₀) (hx₀ : σ x₀ = x₀) :
    (W.veluQuotient {(x₀, y₀)}).map σ = W.veluQuotient {(x₀, y₀)} := by
  have h := W.map_veluQuotient_singleton σ x₀ y₀
  rw [hW, hx₀] at h
  rcases sigma_y₀_eq_or_eq_negY hW hQ hx₀ with hy | hy
  · rw [hy] at h
    exact h.symm
  · rw [hy] at h
    exact h.symm.trans (W.veluQuotient_singleton_negY x₀ y₀)


-- @@ L140-149 verbatim
theorem veluX_singleton_map_comm (hW : W.map σ = W) {x₀ y₀ : F}
    (hQ : W.toAffine.Equation x₀ y₀) (hx₀ : σ x₀ = x₀) (x : F) :
    W.veluX {(x₀, y₀)} (σ x) = σ (W.veluX {(x₀, y₀)} x) := by
  have h := W.map_veluX_singleton σ x₀ y₀ x
  rw [hW, hx₀] at h
  rcases sigma_y₀_eq_or_eq_negY hW hQ hx₀ with hy | hy
  · rw [hy] at h
    exact h
  · rw [hy] at h
    exact (W.veluX_singleton_negY x₀ y₀ (σ x)).symm.trans h


-- @@ L151-160 verbatim
theorem veluY_singleton_map_comm (hW : W.map σ = W) {x₀ y₀ : F}
    (hQ : W.toAffine.Equation x₀ y₀) (hx₀ : σ x₀ = x₀) (x y : F) :
    W.veluY {(x₀, y₀)} (σ x) (σ y) = σ (W.veluY {(x₀, y₀)} x y) := by
  have h := W.map_veluY_singleton σ x₀ y₀ x y
  rw [hW, hx₀] at h
  rcases sigma_y₀_eq_or_eq_negY hW hQ hx₀ with hy | hy
  · rw [hy] at h
    exact h
  · rw [hy] at h
    exact (W.veluY_singleton_negY x₀ y₀ (σ x) (σ y)).symm.trans h


-- @@ L162-162 verbatim
end Galois


-- @@ L164-164 verbatim
section Kernel


-- @@ L166-166 verbatim
variable {F : Type*} [Field F] {W : WeierstrassCurve F}

-- @@ L167-168 verbatim
variable {x₀ y₀ : F} (hQ : W.toAffine.Equation x₀ y₀) (hΨ : (W.Ψ₃).eval x₀ = 0)
  (hΔ : (W.veluQuotient {(x₀, y₀)}).Δ ≠ 0)


-- @@ L170-196 verbatim
theorem veluPointMap3_eq_zero_iff (hQns : W.toAffine.Nonsingular x₀ y₀)
    (P : W.toAffine.Point) :
    veluPointMap3 hQ hΨ hΔ P = 0 ↔
      P = 0 ∨ P = .some x₀ y₀ hQns ∨ P = -.some x₀ y₀ hQns := by
  cases P with
  | zero =>
    constructor
    · intro _
      exact Or.inl rfl
    · intro _
      rfl
  | some x y h =>
    by_cases hx : x = x₀
    · rw [veluPointMap3_some_of_eq hQ hΨ hΔ h hx]
      constructor
      · intro _
        exact Or.inr (Affine.Point.X_eq_iff.mp hx)
      · intro _
        rfl
    · rw [veluPointMap3_some_of_ne hQ hΨ hΔ h hx]
      constructor
      · intro hcontra
        exact absurd hcontra (Affine.Point.some_ne_zero _)
      · rintro (h0 | hQ' | hQ'')
        · exact absurd h0 (Affine.Point.some_ne_zero h)
        · exact absurd (Affine.Point.X_eq_iff.mpr (Or.inl hQ')) hx
        · exact absurd (Affine.Point.X_eq_iff.mpr (Or.inr hQ'')) hx


-- @@ L198-198 verbatim
end Kernel


-- @@ L200-200 verbatim
end WeierstrassCurve
