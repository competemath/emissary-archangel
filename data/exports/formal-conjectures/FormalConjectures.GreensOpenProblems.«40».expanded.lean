/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil


-- @@ L19-29 verbatim
/-!
# Ben Green's Open Problem 40

*References:*
- [Gr24] [Ben Green's Open Problem 40](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.40)
- [Da90] Davydov, Alexander Abramovich. "Construction of linear covering codes."
  Problemy Peredachi Informatsii 26.4 (1990): 38-55.
- [CHL97] Cohen, G., Honkala, I., Litsyn, S., & Lobstein, A. (1997). Covering codes (Vol. 54). Elsevier.
- [St94] R. Struik, Covering codes, PhD Thesis, Eindhoven University of Technology, the Netherlands, 106 pp, 1994.

-/


-- @@ L31-31 verbatim
open Filter Topology Fintype

-- @@ L32-32 verbatim
open scoped ENNReal Pointwise


-- @@ L34-34 verbatim
namespace Green40



-- @@ L37-39 verbatim
/-- The Hamming ball of radius $r$ in $\mathbb{F}_2^n$. -/
def hammingBall (n r : ℕ) : Set (𝔽₂ n) :=
  {x | hammingNorm x ≤ r}


-- @@ L41-43 verbatim
/-- $V$ is a covering subspace of $\mathbb{F}_2^n$ by $H(r)$ if $V + H(r) = \mathbb{F}_2^n$. -/
def IsCoveringSubspace (n r : ℕ) (V : Submodule (ZMod 2) (𝔽₂ n)) : Prop :=
  (V : Set (𝔽₂ n)) + hammingBall n r = Set.univ


-- @@ L45-49 verbatim
/-- The minimal covering density over all covering subspaces for a given n and r.
    We compute in `ℝ≥0∞` (ENNReal) to gracefully handle any potential divergence. -/
noncomputable def minDensity (n r : ℕ) : ℝ≥0∞ :=
  ⨅ (V : Submodule (ZMod 2) (𝔽₂ n)) (_ : IsCoveringSubspace n r V),
    (Nat.card V : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞)


-- @@ L51-57 verbatim
/--
Let $f(r)$ be the smallest constant such that there exists an infinite sequence of $n$'s together
with subspaces $V_n \leq \mathbb{F}_2^n$ with $V_n + H(r) = \mathbb{F}_2^n$ and
$|V_n| = \left(f(r) + o(1)\right) \frac{2^n}{|H(r)|}$.
-/
noncomputable def f (r : ℕ) : ℝ≥0∞ :=
  liminf (fun n ↦ minDensity n r) atTop


-- @@ L59-62 verbatim
/-- Does $f(r) \to \infty$? [Gr24]-/
@[category research open, AMS 5 94]
theorem green_40 : answer(sorry) ↔ Tendsto f atTop (𝓝 ⊤) := by
  sorry


-- @@ L64-67 verbatim
/-- The only value known is $f(1) = 1$, which follows from the existence of the Hamming code [Gr24]. -/
@[category research solved, AMS 5 94]
theorem green_40.sanity_f_one : f 1 = 1 := by
  sorry


-- @@ L69-72 verbatim
/-- $f(r) \le r^r / r! \sim e^r$ [Gr24]. -/
@[category research solved, AMS 5 94]
theorem green_40.upper_bound (r : ℕ) : f r ≤ (r ^ r : ℝ≥0∞) / (r.factorial : ℝ≥0∞) := by
  sorry


-- @@ L74-77 verbatim
/-- The possibility that f(r) = 1 for all r has not been ruled out [Gr24] -/
@[category research open, AMS 5 94]
theorem green_40.f_eq_one_for_all : answer(sorry) ↔ ∀ r, f r = 1 := by
  sorry


-- @@ L79-82 verbatim
/-- It is not known whether f(2) = 1 [Gr24] -/
@[category research open, AMS 5 94]
theorem green_40.f_two_eq_one : answer(sorry) ↔ f 2 = 1 := by
  sorry


-- @@ L84-91 verbatim
/-- The best-known upper bound for $f(2)$ is $1.4238$ [CHL97]. -/
@[category research solved, AMS 5 94]
theorem green_40.upper_bound_f_two : f 2 ≤ (1.4238 : ℝ≥0∞) := by
  sorry

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- Variant with arbitrary subsets
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


-- @@ L93-94 verbatim
def hammingBallFinset (n r : ℕ) : Finset (𝔽₂ n) :=
  Finset.univ.filter (fun x => hammingNorm x ≤ r)


-- @@ L96-97 verbatim
def IsCoveringFinset (n r : ℕ) (V : Finset (𝔽₂ n)) : Prop :=
  V + hammingBallFinset n r = Finset.univ


-- @@ L99-101 verbatim
noncomputable def minDensityFinset (n r : ℕ) : ℝ≥0∞ :=
  ⨅ (V : Finset (𝔽₂ n)) (_ : IsCoveringFinset n r V),
    (V.card : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) / (2 ^ n : ℝ≥0∞)


-- @@ L103-104 verbatim
noncomputable def f_tilde (r : ℕ) : ℝ≥0∞ :=
  liminf (fun n ↦ minDensityFinset n r) atTop


-- @@ L106-109 verbatim
/-- Does $\tilde{f}(r) \to \infty$? [Gr24] -/
@[category research open, AMS 5 94]
theorem green_40.variants.arbitrary_subsets : answer(sorry) ↔ Tendsto f_tilde atTop (𝓝 ⊤) := by
  sorry


-- @@ L111-114 verbatim
/-- It is known that $\tilde{f}(2) = 1$ [St94]. -/
@[category research solved, AMS 5 94]
theorem green_40.variants.arbitrary_subsets_sanity_f_tilde_two : f_tilde 2 = 1 := by
  sorry


-- @@ L116-145 verbatim
/-- We evidently have $\tilde{f}(r) \le f(r)$ [Gr24]. -/
@[category research solved, AMS 5 94]
theorem green_40.f_tilde_le_f (r : ℕ) : f_tilde r ≤ f r := by
  refine Filter.liminf_le_liminf (Filter.Eventually.of_forall fun n => ?_)
  refine le_iInf₂ fun V hV => ?_
  have hfin : (V : Set (𝔽₂ n)).Finite := Set.toFinite _
  have hcov : IsCoveringFinset n r hfin.toFinset := by
    unfold IsCoveringFinset
    ext x
    simp only [Finset.mem_univ, iff_true]
    have hx : x ∈ (V : Set (𝔽₂ n)) + hammingBall n r := hV ▸ Set.mem_univ x
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    exact Finset.mem_add.mpr
      ⟨a, hfin.mem_toFinset.mpr ha, b, by simpa [hammingBallFinset, hammingBall] using hb, hab⟩
  have hcard : (hfin.toFinset.card : ℝ≥0∞) = (Nat.card V : ℝ≥0∞) := by
    have h : Nat.card V = hfin.toFinset.card := by
      rw [show Nat.card V = Nat.card (V : Set (𝔽₂ n)) from rfl, Nat.card_coe_set_eq,
        Set.ncard_eq_toFinset_card _ hfin]
    exact_mod_cast congrArg Nat.cast h.symm
  calc minDensityFinset n r
      ≤ (hfin.toFinset.card : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) /
          (2 ^ n : ℝ≥0∞) :=
        iInf₂_le hfin.toFinset hcov
    _ = (Nat.card V : ℝ≥0∞) * (Nat.card (hammingBall n r) : ℝ≥0∞) /
          (2 ^ n : ℝ≥0∞) := by
        rw [hcard]

-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
-- Variant for all n
-- %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


-- @@ L147-148 verbatim
noncomputable def f_all (r : ℕ) : ℝ≥0∞ :=
  limsup (fun n ↦ minDensity n r) atTop


-- @@ L150-157 verbatim
/-- Does $f_{\text{all}}(r) \to \infty$? [Gr24]

The target filter is `𝓝 ⊤`, as in `green_40` and `green_40.variants.arbitrary_subsets`. On
`ℝ≥0∞`, `atTop` is the principal ultrafilter at `⊤`, so `Tendsto f_all atTop atTop` would say
that `f_all r = ⊤` for all large `r` rather than that `f_all r → ∞`. -/
@[category research open, AMS 5 94]
theorem green_40.variants.all_n : answer(sorry) ↔ Tendsto f_all atTop (𝓝 ⊤) := by
  sorry


-- @@ L159-159 verbatim
end Green40
