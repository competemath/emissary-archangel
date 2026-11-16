/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import LieLean.Algebra.Lie.KacMoody.KacKazhdan.Polynomial
import LieLean.Algebra.Lie.KacMoody.Shapovalov


-- @@ L9-45 verbatim
/-!
# Matrix coefficients of words in Verma modules as polynomial functions of the highest weight

Let `𝔤 = 𝔤(A) = 𝔫₋ ⊕ 𝔥 ⊕ 𝔫₊` be a Kac–Moody algebra over a field `K` of characteristic zero. For
elements `z₁, …, zₘ ∈ 𝔤` we study the function
`F(λ) = ⟨v_λ^*, z₁ ⋯ zₘ v_λ⟩` on `𝔥*`,
the coefficient of the highest-weight vector `v_λ` in `z₁ ⋯ zₘ v_λ ∈ M(λ)`
(`Matrix.Realization.KacMoodyAlgebra.wordFn`). The entries of the Shapovalov form on `M(λ)` in a
PBW basis are of this form.

If each `zᵢ` lies in `𝔫₊`, in `𝔥`, or in `𝔫₋` (a `TriLetter`), and the word has `a` letters in
`𝔫₊`, `b` letters in `𝔫₋` and `c` letters in `𝔥`, then `F` is a polynomial function of `λ` of
degree at most `c + min(a, b)` (`Matrix.Realization.KacMoodyAlgebra.wordFn_mem_polyLE`). This is
the degree estimate behind the leading term of the Shapovalov determinant ([KK];
[Kum] Thm. 2.3.4, proof, Step 2 (1); for finite type [HumO] §5.9, Lemma (b)); the argument below —
move the first letter of `𝔫₊` to the right, where it kills `v_λ`, and count the letters of the
commutators produced — is our reconstruction.

## Main definitions

* `Matrix.Realization.KacMoodyAlgebra.wordFn`: `λ ↦ ⟨v_λ^*, z₁ ⋯ zₘ v_λ⟩`.
* `Matrix.Realization.KacMoodyAlgebra.TriLetter`: an element of `𝔫₊`, `𝔥` or `𝔫₋`.
* `Matrix.Realization.KacMoodyAlgebra.TriLetter.deg`: the degree bound `c + min(a, b)`.

## Main results

* `Matrix.Realization.KacMoodyAlgebra.wordFn_mem_polyLE`: the degree estimate.

## References

* [KK] V. G. Kac, D. A. Kazhdan, *Structure of representations with highest weight of
  infinite-dimensional Lie algebras*, Adv. Math. 34 (1979), 97–108.
* [Kum] S. Kumar, *Kac–Moody groups, their flag varieties and representation theory*, Progr.
  Math. 204, Birkhäuser 2002, §2.3.
* [HumO] J. E. Humphreys, *Representations of semisimple Lie algebras in the BGG category 𝒪*,
  GSM 94, AMS 2008, §5.9.
-/


-- @@ L47-47 verbatim
open Module LieModule Module.Dual


-- @@ L49-49 verbatim
noncomputable section


-- @@ L51-51 verbatim
namespace Matrix.Realization.KacMoodyAlgebra


-- @@ L53-53 verbatim
attribute [local instance 100] LieRing.ofAssociativeRing


-- @@ L55-56 verbatim
variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H]
  [Module K H] {A : Matrix ι ι ℤ} (P : Realization A K H)


-- @@ L58-58 verbatim
local notation "ιᵤ" => UniversalEnvelopingAlgebra.ι K


-- @@ L60-60 verbatim
/-! ### Letters of triangular type -/


-- @@ L62-69 verbatim
/-- An element of `𝔫₊`, of `𝔥` or of `𝔫₋`, remembering which. -/
inductive TriLetter (P : Realization A K H) where
  /-- An element of `𝔫₊`. -/
  | pos (x : nPos P)
  /-- An element `h(a)` of `𝔥`. -/
  | cart (a : H)
  /-- An element of `𝔫₋`. -/
  | neg (y : nNeg P)


-- @@ L71-71 verbatim
namespace TriLetter


-- @@ L73-73 verbatim
variable {P}


-- @@ L75-79 verbatim
/-- The element of `𝔤` represented by a letter. -/
def val : TriLetter P → P.KacMoodyAlgebra
  | pos x => x
  | cart a => h P a
  | neg y => y


-- @@ L81-84 verbatim
/-- Whether a letter lies in `𝔫₊`. -/
def isPos : TriLetter P → Bool
  | pos _ => true
  | _ => false


-- @@ L86-89 verbatim
/-- Whether a letter lies in `𝔥`. -/
def isCart : TriLetter P → Bool
  | cart _ => true
  | _ => false


-- @@ L91-94 verbatim
/-- Whether a letter lies in `𝔫₋`. -/
def isNeg : TriLetter P → Bool
  | neg _ => true
  | _ => false


-- @@ L96-97 verbatim
/-- The number of letters in `𝔫₊`. -/
def numPos (w : List (TriLetter P)) : ℕ := w.countP isPos


-- @@ L99-100 verbatim
/-- The number of letters in `𝔥`. -/
def numCart (w : List (TriLetter P)) : ℕ := w.countP isCart


-- @@ L102-103 verbatim
/-- The number of letters in `𝔫₋`. -/
def numNeg (w : List (TriLetter P)) : ℕ := w.countP isNeg


-- @@ L105-107 verbatim
/-- The degree bound `c + min(a, b)` for a word with `a` letters in `𝔫₊`, `b` in `𝔫₋` and `c` in
`𝔥`. -/
def deg (w : List (TriLetter P)) : ℕ := numCart w + min (numPos w) (numNeg w)


-- @@ L109-109 verbatim
@[simp] lemma numPos_nil : numPos ([] : List (TriLetter P)) = 0 := rfl

-- @@ L110-110 verbatim
@[simp] lemma numCart_nil : numCart ([] : List (TriLetter P)) = 0 := rfl

-- @@ L111-111 verbatim
@[simp] lemma numNeg_nil : numNeg ([] : List (TriLetter P)) = 0 := rfl

-- @@ L112-112 verbatim
@[simp] lemma deg_nil : deg ([] : List (TriLetter P)) = 0 := rfl


-- @@ L114-115 verbatim
@[simp] lemma numPos_append (u w : List (TriLetter P)) :
    numPos (u ++ w) = numPos u + numPos w := List.countP_append ..

-- @@ L116-117 verbatim
@[simp] lemma numCart_append (u w : List (TriLetter P)) :
    numCart (u ++ w) = numCart u + numCart w := List.countP_append ..

-- @@ L118-119 verbatim
@[simp] lemma numNeg_append (u w : List (TriLetter P)) :
    numNeg (u ++ w) = numNeg u + numNeg w := List.countP_append ..


-- @@ L121-122 verbatim
@[simp] lemma numPos_cons_pos (x : nPos P) (w : List (TriLetter P)) :
    numPos (pos x :: w) = numPos w + 1 := List.countP_cons_of_pos rfl

-- @@ L123-124 verbatim
@[simp] lemma numPos_cons_cart (a : H) (w : List (TriLetter P)) :
    numPos (cart a :: w) = numPos w := List.countP_cons_of_neg Bool.false_ne_true

-- @@ L125-126 verbatim
@[simp] lemma numPos_cons_neg (y : nNeg P) (w : List (TriLetter P)) :
    numPos (neg y :: w) = numPos w := List.countP_cons_of_neg Bool.false_ne_true

-- @@ L127-128 verbatim
@[simp] lemma numCart_cons_pos (x : nPos P) (w : List (TriLetter P)) :
    numCart (pos x :: w) = numCart w := List.countP_cons_of_neg Bool.false_ne_true

-- @@ L129-130 verbatim
@[simp] lemma numCart_cons_cart (a : H) (w : List (TriLetter P)) :
    numCart (cart a :: w) = numCart w + 1 := List.countP_cons_of_pos rfl

-- @@ L131-132 verbatim
@[simp] lemma numCart_cons_neg (y : nNeg P) (w : List (TriLetter P)) :
    numCart (neg y :: w) = numCart w := List.countP_cons_of_neg Bool.false_ne_true

-- @@ L133-134 verbatim
@[simp] lemma numNeg_cons_pos (x : nPos P) (w : List (TriLetter P)) :
    numNeg (pos x :: w) = numNeg w := List.countP_cons_of_neg Bool.false_ne_true

-- @@ L135-136 verbatim
@[simp] lemma numNeg_cons_cart (a : H) (w : List (TriLetter P)) :
    numNeg (cart a :: w) = numNeg w := List.countP_cons_of_neg Bool.false_ne_true

-- @@ L137-138 verbatim
@[simp] lemma numNeg_cons_neg (y : nNeg P) (w : List (TriLetter P)) :
    numNeg (neg y :: w) = numNeg w + 1 := List.countP_cons_of_pos rfl


-- @@ L140-140 verbatim
end TriLetter


-- @@ L142-142 verbatim
variable [CharZero K]


-- @@ L144-144 verbatim
/-! ### The function `λ ↦ ⟨v_λ^*, z₁ ⋯ zₘ v_λ⟩` -/


-- @@ L146-148 verbatim
/-- The coefficient of `v_λ` in `z₁ ⋯ zₘ v_λ ∈ M(λ)`, as a function of `λ ∈ 𝔥*`. -/
def wordFn (l : List P.KacMoodyAlgebra) : Dual K H → K :=
  fun Λ ↦ VermaModule.hwCoord P Λ ((l.map ιᵤ).prod • VermaModule.hwv P Λ)


-- @@ L150-151 verbatim
lemma wordFn_apply (l : List P.KacMoodyAlgebra) (Λ : Dual K H) :
    wordFn P l Λ = VermaModule.hwCoord P Λ ((l.map ιᵤ).prod • VermaModule.hwv P Λ) := rfl


-- @@ L153-155 verbatim
@[simp] lemma wordFn_nil : wordFn P [] = 1 := by
  ext Λ
  simp [wordFn_apply]


-- @@ L157-161 verbatim
lemma wordFn_append_add (u w : List P.KacMoodyAlgebra) (a b : P.KacMoodyAlgebra) :
    wordFn P (u ++ (a + b) :: w) = wordFn P (u ++ a :: w) + wordFn P (u ++ b :: w) := by
  ext Λ
  simp only [wordFn_apply, List.map_append, List.map_cons, List.prod_append, List.prod_cons,
    map_add, add_mul, mul_add, add_smul, Pi.add_apply]


-- @@ L163-165 verbatim
lemma wordFn_append_zero (u w : List P.KacMoodyAlgebra) : wordFn P (u ++ 0 :: w) = 0 := by
  ext Λ
  simp [wordFn_apply]


-- @@ L167-172 verbatim
lemma wordFn_append_smul (u w : List P.KacMoodyAlgebra) (c : K) (a : P.KacMoodyAlgebra) :
    wordFn P (u ++ (c • a) :: w) = c • wordFn P (u ++ a :: w) := by
  ext Λ
  simp only [wordFn_apply, List.map_append, List.map_cons, List.prod_append, List.prod_cons,
    map_smul, Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_assoc, Pi.smul_apply,
    smul_eq_mul]


-- @@ L174-178 verbatim
lemma wordFn_cons_of_mem_nNeg {y : P.KacMoodyAlgebra} (hy : y ∈ nNeg P)
    (w : List P.KacMoodyAlgebra) : wordFn P (y :: w) = 0 := by
  ext Λ
  rw [wordFn_apply, List.map_cons, List.prod_cons, mul_smul, ← VermaModule.lie_eq_smul,
    VermaModule.hwCoord_lie_of_mem_nNeg P Λ hy, Pi.zero_apply]


-- @@ L180-184 verbatim
lemma wordFn_h_cons (a : H) (w : List P.KacMoodyAlgebra) :
    wordFn P (h P a :: w) = (fun Λ : Dual K H ↦ Λ a) * wordFn P w := by
  ext Λ
  rw [wordFn_apply, List.map_cons, List.prod_cons, mul_smul, ← VermaModule.lie_eq_smul,
    VermaModule.hwCoord_lie_h, Pi.mul_apply, wordFn_apply]


-- @@ L186-191 verbatim
lemma wordFn_append_singleton_of_mem_nPos {x : P.KacMoodyAlgebra} (hx : x ∈ nPos P)
    (u : List P.KacMoodyAlgebra) : wordFn P (u ++ [x]) = 0 := by
  ext Λ
  rw [wordFn_apply, List.map_append, List.prod_append, List.map_singleton, List.prod_singleton,
    mul_smul, ← VermaModule.lie_eq_smul, VermaModule.lie_hwv_of_mem_nPos P Λ hx, smul_zero,
    map_zero, Pi.zero_apply]


-- @@ L193-201 verbatim
/-- Moving a letter one step to the right: `x z = z x + [x, z]`. -/
lemma wordFn_append_cons_cons (u w : List P.KacMoodyAlgebra) (x z : P.KacMoodyAlgebra) :
    wordFn P (u ++ x :: z :: w) =
      wordFn P ((u ++ [z]) ++ x :: w) + wordFn P (u ++ ⁅x, z⁆ :: w) := by
  ext Λ
  simp only [wordFn_apply, List.map_append, List.map_cons, List.prod_append, List.prod_cons,
    List.map_nil, List.prod_nil, mul_one, Pi.add_apply, LieHom.map_lie,
    LieRing.of_associative_ring_bracket, sub_mul, mul_sub, mul_assoc, sub_smul, map_sub]
  ring


-- @@ L203-203 verbatim
open TriLetter


-- @@ L205-209 verbatim
omit [CharZero K] in
/-- `[𝔫₊, 𝔥] ⊆ 𝔫₊`. -/
lemma lie_h_mem_nPos' {x : P.KacMoodyAlgebra} (hx : x ∈ nPos P) (a : H) : ⁅x, h P a⁆ ∈ nPos P := by
  rw [← lie_skew]
  exact neg_mem (lie_h_mem_nPos P a hx)


-- @@ L211-313 verbatim
/-- **The degree estimate** (cf. [KK]; [Kum] Thm. 2.3.4, proof, Step 2 (1)): for a word `z₁ ⋯ zₘ`
with `a` letters in `𝔫₊`, `b` letters in `𝔫₋` and `c` letters in `𝔥`, the coefficient of `v_λ` in
`z₁ ⋯ zₘ v_λ` is a polynomial function of `λ` of degree at most `c + min(a, b)`. -/
theorem wordFn_mem_polyLE (w : List (TriLetter P)) :
    wordFn P (w.map val) ∈ polyLE K H (deg w) := by
  suffices ∀ n, ∀ w : List (TriLetter P), w.length = n →
      wordFn P (w.map val) ∈ polyLE K H (deg w) from this _ w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro w hw
  cases w with
  | nil =>
    rw [List.map_nil, wordFn_nil, deg_nil]
    exact one_mem_polyLE 0
  | cons z w =>
    cases z with
    | neg y =>
      rw [List.map_cons, val, wordFn_cons_of_mem_nNeg P y.2]
      exact Submodule.zero_mem _
    | cart a =>
      rw [List.map_cons, val, wordFn_h_cons]
      have := mul_mem_polyLE (apply_mem_polyLE (K := K) a) (ih w.length (by simp [← hw]) w rfl)
      refine polyLE_mono ?_ this
      simp only [deg, numCart_cons_cart, numPos_cons_cart, numNeg_cons_cart]
      omega
    | pos x =>
      -- move `x` to the right
      suffices ∀ (w₂ u : List (TriLetter P)), u.length + w₂.length + 1 = n →
          wordFn P ((u ++ TriLetter.pos x :: w₂).map val) ∈
            polyLE K H (deg (u ++ TriLetter.pos x :: w₂)) from
        this w [] (by simpa [add_comm] using hw)
      intro w₂
      induction w₂ with
      | nil =>
        intro u _
        rw [List.map_append, List.map_singleton, val,
          wordFn_append_singleton_of_mem_nPos P x.2]
        exact Submodule.zero_mem _
      | cons z w₂ ihw =>
        intro u hlen
        simp only [List.length_cons] at hlen
        have hsplit := wordFn_append_cons_cons P (u.map val) (w₂.map val) x (val z)
        have e : (u ++ TriLetter.pos x :: z :: w₂).map val =
            u.map val ++ (x : P.KacMoodyAlgebra) :: val z :: w₂.map val := by simp [val]
        rw [e, hsplit]
        refine Submodule.add_mem _ ?_ ?_
        · have := ihw (u ++ [z]) (by simp; omega)
          have e' : (u ++ [z] ++ TriLetter.pos x :: w₂).map val =
              u.map val ++ [val z] ++ (x : P.KacMoodyAlgebra) :: w₂.map val := by simp [val]
          rw [e'] at this
          convert this using 2
          cases z <;> simp only [deg, numPos_append, numCart_append, numNeg_append,
            numPos_cons_pos, numPos_cons_cart, numPos_cons_neg, numCart_cons_pos,
            numCart_cons_cart, numCart_cons_neg, numNeg_cons_pos, numNeg_cons_cart,
            numNeg_cons_neg, numPos_nil, numCart_nil, numNeg_nil] <;> omega
        · have hIH' : ∀ t : TriLetter P, deg (u ++ t :: w₂) ≤
              deg (u ++ TriLetter.pos x :: z :: w₂) →
              wordFn P (u.map val ++ val t :: w₂.map val) ∈
                polyLE K H (deg (u ++ TriLetter.pos x :: z :: w₂)) := fun t ht ↦ by
            have := polyLE_mono ht (ih (u.length + w₂.length + 1) (by omega) _
              (by simp only [List.length_append, List.length_cons]; omega))
            simpa using this
          cases z with
          | pos x' =>
            have := hIH' (TriLetter.pos ⟨⁅(x : P.KacMoodyAlgebra), x'⁆,
              (nPos P).lie_mem x.2 x'.2⟩) (by
                simp only [deg, numPos_append, numCart_append, numNeg_append,
                  numPos_cons_pos, numCart_cons_pos, numNeg_cons_pos]
                omega)
            simpa [val] using this
          | cart a =>
            have := hIH' (TriLetter.pos ⟨⁅(x : P.KacMoodyAlgebra), h P a⁆,
              lie_h_mem_nPos' P x.2 a⟩) (by
                simp only [deg, numPos_append, numCart_append, numNeg_append,
                  numPos_cons_pos, numCart_cons_pos, numNeg_cons_pos, numPos_cons_cart,
                  numCart_cons_cart, numNeg_cons_cart]
                omega)
            simpa [val] using this
          | neg y =>
            obtain ⟨p, a, q, hpaq⟩ := exists_triangular P ⁅(x : P.KacMoodyAlgebra), y⁆
            simp only [val]
            rw [hpaq, wordFn_append_add, wordFn_append_add]
            refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
            · have := hIH' (TriLetter.neg ⟨fHom P p, p, rfl⟩) (by
                simp only [deg, numPos_append, numCart_append, numNeg_append,
                  numPos_cons_pos, numCart_cons_pos, numNeg_cons_pos, numPos_cons_neg,
                  numCart_cons_neg, numNeg_cons_neg]
                omega)
              simpa [val] using this
            · have := hIH' (TriLetter.cart a) (by
                simp only [deg, numPos_append, numCart_append, numNeg_append,
                  numPos_cons_pos, numCart_cons_pos, numNeg_cons_pos, numPos_cons_neg,
                  numCart_cons_neg, numNeg_cons_neg, numPos_cons_cart, numCart_cons_cart,
                  numNeg_cons_cart]
                omega)
              simpa [val] using this
            · have := hIH' (TriLetter.pos ⟨eHom P q, q, rfl⟩) (by
                simp only [deg, numPos_append, numCart_append, numNeg_append,
                  numPos_cons_pos, numCart_cons_pos, numNeg_cons_pos, numPos_cons_neg,
                  numCart_cons_neg, numNeg_cons_neg]
                omega)
              simpa [val] using this


-- @@ L315-315 verbatim
end Matrix.Realization.KacMoodyAlgebra
