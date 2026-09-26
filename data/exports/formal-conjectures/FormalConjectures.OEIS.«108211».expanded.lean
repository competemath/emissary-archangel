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


-- @@ L19-24 verbatim
/-!
# $a(n) = 16n^2 + 1$

*References:*
- [A108211](https://oeis.org/A108211)
-/


-- @@ L26-26 verbatim
namespace OeisA108211


-- @@ L28-32 verbatim
/--
The primary defining sequence `a`.
`a n` is defined as $16n^2 + 1$.
-/
def a (n : ℕ) : ℕ := 16 * n ^ 2 + 1


-- @@ L34-36 verbatim
/-- Term theorems verifying the first few values of the sequence against the official OEIS b-file -/
@[category test, AMS 11]
theorem a_1 : a 1 = 17 := by decide


-- @@ L38-39 verbatim
@[category test, AMS 11]
theorem a_2 : a 2 = 65 := by decide


-- @@ L41-42 verbatim
@[category test, AMS 11]
theorem a_3 : a 3 = 145 := by decide


-- @@ L44-45 verbatim
@[category test, AMS 11]
theorem a_4 : a 4 = 257 := by decide


-- @@ L47-48 verbatim
@[category test, AMS 11]
theorem a_5 : a 5 = 401 := by decide


-- @@ L50-50 verbatim
open Real


-- @@ L52-70 verbatim
/--
Conjecture:
$$a(n) = \left\lfloor \frac{1}{\frac{1}{4n} - \log(2) +
  \frac{1}{n+1} + \frac{1}{n+2} + \dots + \frac{1}{2n}} \right\rfloor.$$

**Proof sketch** (certificate style; the kernel-checked development lives at the
`formal_proof` permalink below). Write $T(n) = \log 2 - (H(2n) - H(n))$ for the harmonic
tail defect. The proof sandwiches $T(n)$ between two explicit telescoping bounds — $h(n)$
from below and $h(n) + 60/(4n+1)^7$ from above, where $h$ telescopes a degree-7 rational
certificate. The two resulting inequalities reduce to polynomial coefficient-nonnegativity
facts discharged by elementary tactics, after which the reciprocal lands in
$[16n^2 + 1,\, 16n^2 + 2)$ and the floor evaluates exactly.
-/
@[category research solved, AMS 11, formal_proof using formal_conjectures at
"https://github.com/chy4pro/formal-conjectures/blob/f24f80aeaa3d5073bf4a54ed9daa102a5e0f1fad/FormalConjectures/OEIS/108211.lean#L540"]
theorem conjecture (n : ℕ) (hn : n > 0) :
    (a n : ℝ) =
      (⌊ 1 / ((4 * n : ℝ)⁻¹ - log 2 + ∑ k ∈ (Finset.Icc (n + 1) (2 * n)), (k : ℝ)⁻¹) ⌋ : ℝ) := by
  sorry


-- @@ L72-72 verbatim
end OeisA108211
