/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.CryptoFoundations.HardnessAssumptions.HardRelation
public import VCVio.OracleComp.Constructions.SampleableType
public import VCVio.OracleComp.ProbComp
public import VCVio.EvalDist.Bool


-- @@ L13-40 verbatim
/-!
# Discrete Logarithm Assumptions (DLog / CDH / DDH)

Standard hardness assumptions for cryptographic groups, formalized using Mathlib's
`Module F G` for scalar multiplication.

## Mathematical setup

We model a cyclic group as:
- `F` : the scalar field (exponents), e.g. `ZMod p` for a prime-order group
- `G` : the group of elements (e.g. elliptic curve points), with `[AddCommGroup G]`
- `Module F G` : scalar multiplication `a • g` (corresponds to `g^a` in multiplicative notation)
- `g : G` : a fixed generator (public system parameter)

## Notation correspondence

| Textbook (multiplicative) | This file (additive / EC-style) |
|---|---|
| `g^a`                     | `a • g`                         |
| `g^a · g^b = g^{a+b}`    | `a • g + b • g = (a + b) • g`  |
| `(g^a)^b = g^{ab}`       | `b • (a • g) = (b * a) • g`    |

## Assumptions

- **DLog**: given `(g, x • g)`, find `x`
- **CDH**: given `(g, a • g, b • g)`, find `(a * b) • g`
- **DDH**: distinguish `(g, a • g, b • g, (a * b) • g)` from `(g, a • g, b • g, c • g)`
-/


-- @@ L42-42 verbatim
@[expose] public section



-- @@ L45-45 verbatim
open OracleComp OracleSpec ENNReal


-- @@ L47-47 verbatim
namespace DiffieHellman


-- @@ L49-49 verbatim
variable {F : Type} [Field F]

-- @@ L50-50 verbatim
variable {G : Type} [AddCommGroup G] [Module F G]


-- @@ L52-52 verbatim
/-! ## DLog (Discrete Logarithm) -/


-- @@ L54-56 verbatim
/-- A DLog adversary receives a generator and a group element, and tries to find the
discrete logarithm (scalar). -/
def DLogAdversary (F G : Type) := G → G → ProbComp F


-- @@ L58-58 verbatim
section DLog


-- @@ L60-60 verbatim
variable [DecidableEq F] [SampleableType F]


-- @@ L62-67 expanded
/-- DLog experiment: sample a random scalar `x`, give the adversary `(g, x • g)`,
and check whether the adversary's guess equals `x`. -/
def dlogExp (g : G) (adversary : DLogAdversary F G) : ProbComp Bool := do
  let x ← uniformSample F
  let x' ← adversary g (x • g)
  return decide (x' = x)


-- @@ L69-69 verbatim
end DLog


-- @@ L71-71 verbatim
/-! ## CDH (Computational Diffie-Hellman) -/


-- @@ L73-76 verbatim
/-- A CDH adversary receives `(g, a • g, b • g)` and tries to compute `(a * b) • g`.
`_F` is a phantom type parameter for the scalar field, enabling Lean to infer `F`
at call sites of `cdhExp`. -/
def CDHAdversary (_F G : Type) := G → G → G → ProbComp G


-- @@ L78-78 verbatim
section CDH


-- @@ L80-80 verbatim
variable [SampleableType F] [DecidableEq G]


-- @@ L82-87 expanded
/-- CDH experiment: sample random scalars `a, b`, give the adversary `(g, a • g, b • g)`,
and check whether the adversary's output equals `(a * b) • g`. -/
def cdhExp (g : G) (adversary : CDHAdversary F G) : ProbComp Bool := do
  let a ← uniformSample F;
  let b ← uniformSample F
  let h ← adversary g (a • g) (b • g)
  return decide (h = (a * b) • g)


-- @@ L89-89 verbatim
end CDH


-- @@ L91-91 verbatim
/-! ## DDH (Decisional Diffie-Hellman) -/


-- @@ L93-97 verbatim
/-- A DDH adversary receives `(g, A, B, T)` and guesses whether `T = (a * b) • g`
(real) or `T` is a random group element (random).
`_F` is a phantom type parameter for the scalar field, enabling Lean to infer `F`
at call sites of `ddhExp` and related definitions. -/
def DDHAdversary (_F G : Type) := G → G → G → G → ProbComp Bool


-- @@ L99-99 verbatim
section DDH


-- @@ L101-101 verbatim
variable [SampleableType F]


-- @@ L103-114 expanded
/-- DDH experiment: sample random scalars `a, b` and a bit. If the bit is `true`, set
`c = a * b` (the real DH scalar); otherwise sample `c ← $ᵗ F` independently. The adversary
receives `(g, a • g, b • g, c • g)` and wins by guessing the bit.

All sampling is from the scalar field `F`, so the experiment is well-defined for any
`Module F G` without requiring that `g` generates all of `G`. -/
def ddhExp (g : G) (adversary : DDHAdversary F G) : ProbComp Bool := do
  let a ← uniformSample F;
  let b ← uniformSample F
  let bit ← uniformSample Bool
  let c ←
    if bit then 
      pure (a * b)
    else
      uniformSample F
  let b' ← adversary g (a • g) (b • g) (c • g)
  return (bit == b')


-- @@ L116-120 expanded
/-- DDH advantage: absolute distance from random guessing (1/2).
Uses `ℝ` with absolute value rather than `ℝ≥0∞` subtraction, which would silently
saturate at zero for adversaries that guess the wrong bit more often than not. -/
noncomputable def ddhGuessAdvantage (g : G) (adversary : DDHAdversary F G) : ℝ :=
  |(probOutput (ddhExp g adversary) true).toReal - 1 / 2|


-- @@ L122-122 verbatim
/-! ## DDH: Two-game formulation -/


-- @@ L124-127 expanded
/-- DDH real game: the adversary receives a genuine DH triple `(g, a • g, b • g, (a * b) • g)`. -/
def ddhExpReal (g : G) (adversary : DDHAdversary F G) : ProbComp Bool := do
  let a ← uniformSample F;
  let b ← uniformSample F
  adversary g (a • g) (b • g) ((a * b) • g)


-- @@ L129-133 expanded
/-- DDH random game: the adversary receives `(g, a • g, b • g, c • g)` with independent
`c ← $ᵗ F`. -/
def ddhExpRand (g : G) (adversary : DDHAdversary F G) : ProbComp Bool := do
  let a ← uniformSample F;
  let b ← uniformSample F;
  let c ← uniformSample F
  adversary g (a • g) (b • g) (c • g)


-- @@ L135-138 expanded
/-- Two-game DDH advantage: `|Pr[output 1 | real] - Pr[output 1 | random]|`. -/
noncomputable def ddhDistAdvantage (g : G) (adversary : DDHAdversary F G) : ℝ :=
  |(probOutput (ddhExpReal g adversary) true).toReal -
      (probOutput (ddhExpRand g adversary) true).toReal|


-- @@ L140-143 verbatim
/-- Baseline success probability for matching an independently uniform DH target sampled from the
scalar space and mapped into the subgroup generated by `g`. -/
noncomputable def uniformDHTargetSuccessProb (F : Type) [Fintype F] : ℝ :=
  ((Fintype.card F : ℝ≥0∞)⁻¹).toReal


-- @@ L145-145 verbatim
end DDH


-- @@ L147-147 verbatim
/-! ## Standard reductions among DLog / CDH / DDH -/


-- @@ L149-149 verbatim
section Reductions


-- @@ L151-151 verbatim
variable [DecidableEq G]


-- @@ L153-158 verbatim
/-- Reduction from CDH solving to DDH distinguishing: compute a candidate DH share and compare it
with the target group element. This is the concrete reduction underlying the hardness implication
`DDH ⇒ CDH`. -/
def cdhToDDHReduction (adversary : CDHAdversary F G) : DDHAdversary F G := fun g A B T => do
  let h ← adversary g A B
  return decide (h = T)


-- @@ L160-165 verbatim
/-- Reduction from DLog solving to CDH solving: recover the two exponents separately and rebuild
the shared DH value. This is the concrete reduction underlying `CDH ⇒ DLog`. -/
def dlogToCDHReduction (adversary : DLogAdversary F G) : CDHAdversary F G := fun g A B => do
  let a ← adversary g A
  let b ← adversary g B
  return (a * b) • g


-- @@ L167-170 verbatim
/-- Direct DLog-to-DDH reduction obtained by composing the standard DLog-to-CDH and CDH-to-DDH
reductions. This is the concrete reduction underlying `DDH ⇒ DLog`. -/
def dlogToDDHReduction (adversary : DLogAdversary F G) : DDHAdversary F G :=
  cdhToDDHReduction (F := F) (dlogToCDHReduction (F := F) adversary)


-- @@ L172-172 verbatim
end Reductions


-- @@ L174-174 verbatim
section DDHBranch


-- @@ L176-176 verbatim
variable [SampleableType F]


-- @@ L178-191 expanded
/-- The single-game DDH experiment can be decomposed as a uniform-bit branch over
the real and random DDH games. -/
private lemma ddhExp_probOutput_eq_branch (g : G) (adversary : DDHAdversary F G) :
    probOutput (ddhExp g adversary) true =
      probOutput
        (do
          let bit ← (uniformSample Bool)
          let z ←
            if bit then 
              ddhExpReal g adversary
            else
              ddhExpRand g adversary
          pure (bit == z))
        true :=
  by
  unfold ddhExp
  rw [probOutput_bind_congr fun a _ => probOutput_bind_bind_swap _ _ _ _, probOutput_bind_bind_swap]
  refine probOutput_bind_congr' (uniformSample Bool) true fun bit => ?_
  cases bit <;> simp [ddhExpReal, ddhExpRand]


-- @@ L193-199 expanded
/-- The single-game DDH decomposes: `Pr[win] - 1/2 = (Pr[real=1] - Pr[rand=1]) / 2`. -/
lemma ddhExp_probOutput_sub_half (g : G) (adversary : DDHAdversary F G) :
    (probOutput (ddhExp g adversary) true).toReal - 1 / 2 =
      ((probOutput (ddhExpReal g adversary) true).toReal -
          (probOutput (ddhExpRand g adversary) true).toReal) /
        2 :=
  by
  rw [ddhExp_probOutput_eq_branch]
  exact probOutput_uniformBool_branch_toReal_sub_half _ _


-- @@ L201-207 verbatim
/-- The two DDH advantage formulations are related by a factor of 2:
`ddhDistAdvantage = 2 * ddhGuessAdvantage`. -/
theorem ddhDistAdvantage_eq_two_mul_ddhGuessAdvantage (g : G) (adversary : DDHAdversary F G) :
    ddhDistAdvantage g adversary = 2 * ddhGuessAdvantage g adversary := by
  unfold ddhDistAdvantage ddhGuessAdvantage
  rw [ddhExp_probOutput_sub_half (F := F) g adversary, abs_div, abs_two]
  ring


-- @@ L209-209 verbatim
end DDHBranch


-- @@ L211-211 verbatim
section CDHToDDH


-- @@ L213-213 verbatim
variable [SampleableType F] [DecidableEq G]


-- @@ L215-219 expanded
/-- In the real DDH game, the CDH-to-DDH reduction succeeds exactly when the underlying CDH
adversary computed the correct shared DH value. -/
theorem probOutput_ddhExpReal_cdhToDDHReduction_eq_cdhExp (g : G) (adversary : CDHAdversary F G) :
    probOutput (ddhExpReal g (cdhToDDHReduction (F := F) adversary)) true =
      probOutput (cdhExp g adversary) true :=
  rfl


-- @@ L221-231 expanded
private lemma probOutput_decide_smul_eq_inv_card [Fintype F] (g : G)
    (hg : Function.Bijective (· • g : F → G)) (h : G) :
    probOutput ((uniformSample F) >>= fun c => pure (decide (h = c • g))) true =
      (Fintype.card F : ℝ≥0∞)⁻¹ :=
  by
  obtain ⟨c₀, rfl⟩ := hg.surjective h
  simp only [probOutput_bind_eq_tsum, probOutput_uniformSample, probOutput_pure]
  rw [tsum_fintype, Finset.sum_eq_single c₀]
  · simp
  · intro c _ hne
    simp [show c₀ • g ≠ c • g from fun heq => hne (hg.injective heq).symm]
  · exact absurd (Finset.mem_univ c₀)


-- @@ L233-253 expanded
/-- In the random DDH game, the CDH-to-DDH reduction only matches the target with the uniform
baseline probability. The bijectivity assumption identifies scalar samples with uniformly sampled
group elements in the subgroup generated by `g`. -/
theorem probOutput_ddhExpRand_cdhToDDHReduction_eq_uniformScalar [Fintype F] (g : G)
    (hg : Function.Bijective (· • g : F → G)) (adversary : CDHAdversary F G) :
    probOutput (ddhExpRand g (cdhToDDHReduction (F := F) adversary)) true =
      (Fintype.card F : ℝ≥0∞)⁻¹ :=
  by
  simp only [ddhExpRand, cdhToDDHReduction]
  have key :
    ∀ a b : F,
      probOutput
          ((uniformSample F) >>= fun c =>
            adversary g (a • g) (b • g) >>= fun h => pure (decide (h = c • g)))
          true =
        (Fintype.card F : ℝ≥0∞)⁻¹ :=
    by
    intro a b
    rw [probOutput_bind_bind_swap,
      probOutput_bind_of_const _ fun h _ => probOutput_decide_smul_eq_inv_card g hg h]
    simp [probFailure_of_liftM_PMF]
  rw [probOutput_bind_of_const _ fun a _ => probOutput_bind_of_const _ fun b _ => key a b]
  simp [probFailure_of_liftM_PMF]


-- @@ L255-266 expanded
/-- Concrete form of the hardness implication `DDH ⇒ CDH`: a CDH solver can only beat the uniform
DH-target baseline by the DDH distinguishing advantage of the associated adversary-map reduction. -/
theorem cdhSuccess_toReal_le_uniform_add_ddhDistAdvantage [Fintype F] (g : G)
    (hg : Function.Bijective (· • g : F → G)) (adversary : CDHAdversary F G) :
    (probOutput (cdhExp g adversary) true).toReal ≤
      uniformDHTargetSuccessProb F + ddhDistAdvantage g (cdhToDDHReduction (F := F) adversary) :=
  by
  unfold ddhDistAdvantage uniformDHTargetSuccessProb
  rw [← probOutput_ddhExpReal_cdhToDDHReduction_eq_cdhExp g adversary,
    probOutput_ddhExpRand_cdhToDDHReduction_eq_uniformScalar g hg adversary]
  exact le_add_of_sub_left_le (le_abs_self _)


-- @@ L268-268 verbatim
end CDHToDDH


-- @@ L270-270 verbatim
section DLogToCDH


-- @@ L272-272 verbatim
variable [DecidableEq F] [SampleableType F] [DecidableEq G]


-- @@ L274-284 expanded
omit [DecidableEq G] in
private lemma dlogExp_probOutput_eq_tsum (g : G) (adversary : DLogAdversary F G) :
    probOutput (dlogExp g adversary) true =
      ∑' x : F, probOutput (uniformSample F) x * probOutput (adversary g (x • g)) x :=
  by
  unfold dlogExp
  rw [probOutput_bind_eq_tsum]
  refine tsum_congr fun x => ?_
  congr 1
  rw [probOutput_bind_eq_tsum]
  refine (tsum_eq_single x fun x' hx' => ?_).trans (by simp)
  simp [show (decide (x' = x) : Bool) = false by simp [hx']]


-- @@ L286-296 expanded
omit [DecidableEq F] in
private lemma cdhExp_dlogToCDHReduction_probOutput_eq_tsum (g : G) (adversary : DLogAdversary F G) :
    probOutput (cdhExp g (dlogToCDHReduction (F := F) adversary)) true =
      ∑' (a : F) (b : F) (a' : F) (b' : F),
        probOutput (uniformSample F) a *
          (probOutput (uniformSample F) b *
            (probOutput (adversary g (a • g)) a' *
              (probOutput (adversary g (b • g)) b' *
                (if (a' * b') • g = (a * b) • g then 1 else 0)))) :=
  by
  unfold cdhExp dlogToCDHReduction
  simp only [monad_norm, probOutput_bind_eq_tsum, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun a => tsum_congr fun b => tsum_congr fun a' => tsum_congr fun b' => ?_
  simp [probOutput_pure]


-- @@ L298-322 expanded
/-- Concrete form of the hardness implication `CDH ⇒ DLog`: if a DLog adversary succeeds with
probability `p`, the induced CDH adversary succeeds with probability at least `p^2`. -/
theorem dlogSuccess_sq_le_cdhSuccess_dlogToCDHReduction (g : G) (adversary : DLogAdversary F G) :
    (probOutput (dlogExp g adversary) true).toReal ^ 2 ≤
      (probOutput (cdhExp g (dlogToCDHReduction (F := F) adversary)) true).toReal :=
  by
  rw [← ENNReal.toReal_pow]
  refine ENNReal.toReal_mono probOutput_ne_top ?_
  set w : F → ℝ≥0∞ := fun x => probOutput (uniformSample F) x
  set f : F → ℝ≥0∞ := fun x => probOutput (adversary g (x • g)) x
  rw [sq, dlogExp_probOutput_eq_tsum, ← ENNReal.tsum_mul_right,
    cdhExp_dlogToCDHReduction_probOutput_eq_tsum]
  refine ENNReal.tsum_le_tsum fun a => ?_
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun b => ?_
  calc
    w a * f a * (w b * f b) =
        w a * (w b * (f a * (f b * (if (a * b) • g = (a * b) • g then 1 else 0)))) :=
      by
      simp only [if_true, mul_one]
      ring
    _ ≤
        ∑' (b' : F),
          w a *
            (w b *
              (f a *
                (probOutput (adversary g (b • g)) b' *
                  (if (a * b') • g = (a * b) • g then 1 else 0)))) :=
      (ENNReal.le_tsum b)
    _ ≤
        ∑' (a' : F) (b' : F),
          w a *
            (w b *
              (probOutput (adversary g (a • g)) a' *
                (probOutput (adversary g (b • g)) b' *
                  (if (a' * b') • g = (a * b) • g then 1 else 0)))) :=
      ENNReal.le_tsum a


-- @@ L324-333 expanded
/-- Concrete form of the hardness implication `DDH ⇒ DLog`, obtained by composing the previous two
adversary-map reductions. -/
theorem dlogSuccess_sq_le_uniform_add_ddhDistAdvantage [Fintype F] (g : G)
    (hg : Function.Bijective (· • g : F → G)) (adversary : DLogAdversary F G) :
    (probOutput (dlogExp g adversary) true).toReal ^ 2 ≤
      uniformDHTargetSuccessProb F + ddhDistAdvantage g (dlogToDDHReduction (F := F) adversary) :=
  (dlogSuccess_sq_le_cdhSuccess_dlogToCDHReduction g adversary).trans
    (cdhSuccess_toReal_le_uniform_add_ddhDistAdvantage g hg (dlogToCDHReduction (F := F) adversary))


-- @@ L335-335 verbatim
end DLogToCDH


-- @@ L337-337 verbatim
/-! ## Generable relation for discrete log -/


-- @@ L339-339 verbatim
section DLogGenerable


-- @@ L341-341 verbatim
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]

-- @@ L342-342 verbatim
variable {G : Type} [AddCommGroup G] [Module F G] [Fintype G] [SampleableType G] [DecidableEq G]

-- @@ L343-343 verbatim
variable (g : G)


-- @@ L345-350 expanded
/-- The discrete log relation is generable by sampling `sk ← $ᵗ F` and returning
`(sk • g, sk)`. -/
def dlogGenerable : GenerableRelation G F (fun pk sk => decide (sk • g = pk))
    where
  gen := do
    let sk ← uniformSample F;
    return (sk • g, sk)
  gen_sound := fun _ _ _ => by grind


-- @@ L352-352 verbatim
end DLogGenerable


-- @@ L354-354 verbatim
/-! ## Cyclic group instantiation helpers -/


-- @@ L356-356 verbatim
section CyclicInstantiation


-- @@ L358-358 verbatim
variable {G : Type} [AddCommGroup G] [Fintype G]


-- @@ L360-363 verbatim
/-- A generator `g` is nondegenerate if `fun a => a.val • g` surjects onto `G`,
ruling out the trivial case. Uses additive notation consistent with `Module F G`. -/
def NondegenerateGenerator (g : G) : Prop :=
  Function.Surjective fun a : Fin (Fintype.card G) => a.val • g


-- @@ L365-371 verbatim
/-- A nondegenerate generator of a nontrivial group is nonzero. -/
lemma NondegenerateGenerator.ne_zero [Nontrivial G] {g : G}
    (hg : NondegenerateGenerator (G := G) g) : g ≠ 0 := by
  rintro rfl
  obtain ⟨x, hx⟩ := exists_ne (0 : G)
  obtain ⟨a, ha⟩ := hg x
  exact hx (by simpa using ha.symm)


-- @@ L373-373 verbatim
end CyclicInstantiation


-- @@ L375-375 verbatim
end DiffieHellman
