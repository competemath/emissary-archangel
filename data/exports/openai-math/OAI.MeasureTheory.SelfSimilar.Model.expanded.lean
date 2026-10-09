import Mathlib


-- @@ L3-3 verbatim
namespace OAI


-- @@ L5-5 verbatim
universe uι


-- @@ L7-7 verbatim
section


-- @@ L9-9 verbatim
open scoped BigOperators ENNReal

-- @@ L10-10 verbatim
open MeasureTheory

-- @@ L11-11 verbatim
namespace EntropyRateDimension


-- @@ L13-20 verbatim
structure System (ι : Type uι) [Fintype ι] where
  ratio : ι → ℝ
  offset : ι → ℝ
  weight : ι → ℝ
  ratio_pos : ∀ i, 0 < |ratio i|
  ratio_lt_one : ∀ i, |ratio i| < 1
  weight_pos : ∀ i, 0 < weight i
  weight_sum : ∑ i, weight i = 1


-- @@ L22-22 verbatim
namespace System

-- @@ L23-23 verbatim
variable {ι : Type uι} [Fintype ι]


-- @@ L25-25 verbatim
def affine (S : System ι) (i : ι) (x : ℝ) : ℝ := S.ratio i * x + S.offset i


-- @@ L27-30 verbatim
def wordAffine (S : System ι) : List ι → ℝ × ℝ
  | [] => (1, 0)
  | i :: w => (S.ratio i * (S.wordAffine w).1,
      S.ratio i * (S.wordAffine w).2 + S.offset i)


-- @@ L32-33 verbatim
def completeMap (S : System ι) {n : ℕ} (w : Fin n → ι) : ℝ × ℝ :=
  S.wordAffine (List.ofFn w)


-- @@ L35-36 verbatim
noncomputable def wordWeight (S : System ι) {n : ℕ} (w : Fin n → ι) : ℝ :=
  ∏ j, S.weight (w j)


-- @@ L38-40 verbatim
noncomputable def mapSupport (S : System ι) (n : ℕ) : Finset (ℝ × ℝ) := by
  classical
  exact Finset.univ.image (S.completeMap (n := n))


-- @@ L42-45 verbatim
noncomputable def mapMass (S : System ι) (n : ℕ) (g : ℝ × ℝ) : ℝ := by
  classical
  exact ∑ w ∈ (Finset.univ : Finset (Fin n → ι)).filter (S.completeMap · = g),
    S.wordWeight w


-- @@ L47-48 verbatim
noncomputable def walkEntropy (S : System ι) (n : ℕ) : ℝ :=
  (∑ g ∈ S.mapSupport n, Real.negMulLog (S.mapMass n g)) / Real.log 2


-- @@ L50-51 verbatim
noncomputable def entropyRate (S : System ι) : ℝ :=
  sInf (Set.range fun n : ℕ => S.walkEntropy (n + 1) / (n + 1 : ℕ))


-- @@ L53-54 verbatim
noncomputable def lyapunov (S : System ι) : ℝ :=
  -(∑ i, S.weight i * (Real.log |S.ratio i| / Real.log 2))


-- @@ L56-57 verbatim
def SelfSimilar (S : System ι) (μ : Measure ℝ) : Prop :=
  μ = ∑ i, ENNReal.ofReal (S.weight i) • μ.map (S.affine i)

-- @@ L58-58 verbatim
end System

-- @@ L59-60 verbatim
noncomputable def lowerHausdorffDimension (μ : Measure ℝ) : ℝ≥0∞ :=
  ⨅ (E : Set ℝ) (_ : MeasurableSet E) (_ : 0 < μ E), dimH E

-- @@ L61-61 verbatim
end EntropyRateDimension

-- @@ L62-62 verbatim
end


-- @@ L64-64 verbatim
end OAI
