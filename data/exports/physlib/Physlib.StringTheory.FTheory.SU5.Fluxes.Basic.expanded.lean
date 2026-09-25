/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
module

public import Mathlib.Analysis.Normed.Ring.Lemmas

-- @@ L9-123 verbatim
/-!

# Fluxes of representations

## i. Overview

Associated with each matter curve `Σ` are `G₄`-fluxes and `hypercharge` fluxes.

For a given matter curve `Σ`, and a Standard Model representation `R`,
these two fluxes contribute to the chiral index `χ(R)` of the representation
(eq 17 of [1]).

The chiral index is equal to the difference the number of left-handed minus
the number of right-handed fermions `Σ` leads to in the representation `R`.
Thus, for example, if `χ(R) = 0`, then all fermions in the representation `R`
arising from `Σ` arise in vector-like pairs, and can be given a mass term without
the presence of a Higgs like-particle.

For a 10d representation matter curve the non-zero chiral indices can be parameterized in terms
of two integers `M : ℤ` and `N : ℤ`. For the SM representation
- `Q = (3,2)_{1/6}` the chirality index is `M`
- `U = (bar 3,1)_{-2/3}` the chirality index is `M - N`
- `E = (1,1)_{1}` the chirality index is `M + N`
We call refer to `M` as the chirality flux of the 10d representation, and
`N` as the hypercharge flux. There exact definitions are given in (eq 19 of [1]).

Similarly, for the 5-bar representation matter curve the non-zero chiral indices can be
likewise be parameterized in terms of two integers `M : ℤ` and `N : ℤ`. For the SM representation
- `D = (bar 3,1)_{1/3}` the chirality index is `M`
- `L = (1,2)_{-1/2}` the chirality index is `M + N`
We again refer to `M` as the chirality flux of the 5-bar representation, and
`N` as the hypercharge flux. The exact definitions are given in (eq 19 of [1]).

If one wishes to put the condition of no chiral exotics in the spectrum, then
we must ensure that the chiral indices above give the chiral content of the MSSM.
These correspond to the following conditions:
1. The two higgs `Hu` and `Hd` must arise from different 5d-matter curves. Otherwise
  they will give a `μ`-term.
2. The matter curve containing `Hu` must give one anti-chiral `(1,2)_{-1/2}` and
  no `(bar 3,1)_{1/3}`. Thus `N = -1` and `M = 0`.
3. The matter curve containing `Hd` must give one chiral `(1,2)_{-1/2}` and
  no `(bar 3,1)_{1/3}`. Thus `N = 1` and `M = 0`.
4. We should have no anti-chiral `(3,2)_{1/6}` and anti-chiral `(bar 3,1)_{-2/3}`.
  Thus `0 ≤ M ` for all 10d-matter curves and 5d matter curves.
5. For the 10d-matter curves we should have no anti-chiral `(bar 3,1)_{-2/3}`
    and no anti-chiral `(1,1)_{1}`. Thus `-M ≤ N ≤ M` for all 10d-matter curves.
6. For the 5d-matter curves we should have no anti-chiral `(1,2)_{-1/2}` (the only
  anti-chiral one present is the one from `Hu`) and thus
  `-M ≤ N` for all 5d-matter curves.
7. To ensure we have 3-families of fermions we must have that `∑ M = 3` and
    `∑ N = 0` for the matter 10d and 5bar matter curves, and in addition `∑ (M + N) = 3` for the
    matter 5d matter curves.
See the conditions in equation 26 - 28 of [1].

## ii. Key results

The above theory is implemented by defining two data structures:
- `Fluxes` : The data of the fluxes `(M, N)` carried by a matter field.
- `FluxesTen` of type `Multiset Fluxes`
  which contains the chirality `M` and hypercharge fluxes
  `N` of the 10d-matter curves.
- `FluxesFive` of type `Multiset Fluxes`
  which contains the chirality `M` and hypercharge fluxes
  `N` of the 5-bar-matter curves (excluding the higgses).

Note: Neither `FluxesTen` or `FluxesFive` are fundamental to the theory,
they can be derived from other data structures.

## iii. Table of contents

- A. Fluxes
  - A.1. Repr instance on `Fluxes`
  - A.2. Extensionality lemma for the fluxes
  - A.3. The zero flux
  - A.4. Addition of fluxes
  - A.5. The instance of an additive commutative monoid on fluxes
- B. Fluxes of the 5d matter representation
  - B.1. Decidability instance on `FluxesFive`
  - B.2. The proposition for no element to be zero
  - B.3. The SM representation `D = (bar 3,1)_{1/3}`
    - B.3.1. Chiral indices of `D`
    - B.3.2. The number of chiral `D`
    - B.3.3. The number of anti-chiral `D`
    - B.3.4. Relation between number of chiral and anti-chiral `D`
  - B.4. The SM representation `L = (1,2)_{-1/2}`
    - B.4.1. Chiral indices of `L`
    - B.4.2. The number of chiral `L`
    - B.4.3. The number of anti-chiral `L`
    - B.4.4. Relation between number of chiral and anti-chiral `L`
  - B.5. No exotics from the 5-bar matter fields
- C. Fluxes of the 10d matter representation
  - C.1. Decidability instance on `FluxesTen`
  - C.2. The proposition for no element to be zero
  - C.3. The SM representation `Q = (3,2)_{1/6}`
    - C.3.1. Chiral indices of `Q`
    - C.3.2. The number of chiral `Q`
    - C.3.3. The number of anti-chiral `Q`
    - C.3.4. Relation between number of chiral and anti-chiral `Q`
  - C.4. The SM representation `U = (bar 3,1)_{-2/3}`
    - C.4.1. Chiral indices of `U`
    - C.4.2. The number of chiral `U`
    - C.4.3. The number of anti-chiral `U`
    - C.4.4. Relation between number of chiral and anti-chiral `Q`
  - C.5. The SM representation `E = (1,1)_{1}`
    - C.5.1. Chiral indices of `E`
    - C.5.2. The number of chiral `E`
    - C.5.3. The number of anti-chiral `E`
    - C.5.4. Relation between number of chiral and anti-chiral `E`
  - C.6. No exotics from the 10d matter fields

## iv. References

* Rational F-Theory GUTs without exotics (arXiv:1401.5084). [ref: arxiv_1401_5084]
* For an old version of the material in this module see PR #569.
-/


-- @@ L125-125 verbatim
@[expose] public section

-- @@ L126-126 verbatim
namespace FTheory


-- @@ L128-128 verbatim
namespace SU5


-- @@ L130-137 verbatim
/-!

## A. Fluxes

To each matter curve we associate a pair of integers `(M, N)`,
the former of which is the chirality flux and the latter the hypercharge flux.

-/


-- @@ L139-145 verbatim
/-- The data of the fluxes carried by a matter field. -/
structure Fluxes where
  /-- The chirality flux. -/
  M : ℤ
  /-- The hypercharge flux. -/
  N : ℤ
deriving DecidableEq


-- @@ L147-147 verbatim
namespace Fluxes


-- @@ L149-153 verbatim
/-!

### A.1. Repr instance on `Fluxes`

-/


-- @@ L155-156 verbatim
instance : Repr Fluxes where
  reprPrec x _ := "⟨" ++ repr x.M ++ ", " ++ repr x.N ++ "⟩"


-- @@ L158-162 verbatim
/-!

### A.2. Extensionality lemma for the fluxes

-/


-- @@ L164-165 verbatim
lemma ext_iff {f1 f2 : Fluxes} : f1 = f2 ↔ f1.M = f2.M ∧ f1.N = f2.N := by
  cases f1; cases f2; simp


-- @@ L167-167 verbatim
instance : Zero Fluxes := ⟨0, 0⟩


-- @@ L169-173 verbatim
/-!

### A.3. The zero flux

-/


-- @@ L175-176 verbatim
@[simp]
lemma zero_M : (0 : Fluxes).M = 0 := rfl


-- @@ L178-179 verbatim
@[simp]
lemma zero_N : (0 : Fluxes).N = 0 := rfl


-- @@ L181-185 verbatim
/-!

### A.4. Addition of fluxes

-/


-- @@ L187-188 verbatim
instance : Add Fluxes where
  add f1 f2 := ⟨f1.M + f2.M, f1.N + f2.N⟩


-- @@ L190-191 verbatim
@[simp]
lemma add_M (f1 f2 : Fluxes) : (f1 + f2).M = f1.M + f2.M := rfl


-- @@ L193-194 verbatim
@[simp]
lemma add_N (f1 f2 : Fluxes) : (f1 + f2).N = f1.N + f2.N := rfl


-- @@ L196-200 verbatim
/-!

### A.5. The instance of an additive commutative monoid on fluxes

-/


-- @@ L202-209 verbatim
instance : AddCommMonoid Fluxes where
  add_assoc f1 f2 f3 := Fluxes.ext_iff.mpr <| by simp only [add_M, add_N]; ring_nf; simp
  zero_add f := Fluxes.ext_iff.mpr <| by simp
  add_zero f := Fluxes.ext_iff.mpr <| by simp
  add_comm f1 f2 := Fluxes.ext_iff.mpr <| by simp only [add_M, add_N]; ring_nf; simp
  nsmul n f := ⟨n • f.M, n • f.N⟩
  nsmul_zero f := Fluxes.ext_iff.mpr ⟨zero_nsmul f.M, zero_nsmul f.N⟩
  nsmul_succ n f := Fluxes.ext_iff.mpr ⟨succ_nsmul f.M n, succ_nsmul f.N n⟩


-- @@ L211-211 verbatim
end Fluxes


-- @@ L213-217 verbatim
/-!

## B. Fluxes of the 5d matter representation

-/


-- @@ L219-220 verbatim
/-- The fluxes `(M, N)` of the 5-bar matter curves of a theory. -/
abbrev FluxesFive : Type := Multiset Fluxes


-- @@ L222-222 verbatim
namespace FluxesFive


-- @@ L224-228 verbatim
/-!

### B.1. Decidability instance on `FluxesFive`

-/


-- @@ L230-231 verbatim
instance : DecidableEq FluxesFive :=
  inferInstanceAs (DecidableEq (Multiset Fluxes))


-- @@ L233-237 verbatim
/-!

### B.2. The proposition for no element to be zero

-/


-- @@ L239-241 verbatim
/-- The proposition on `FluxesFive` such that `(0, 0)` is not in `F`
  and as such each component in `F` leads to chiral matter. -/
abbrev HasNoZero (F : FluxesFive) : Prop := 0 ∉ F


-- @@ L243-247 verbatim
/-!

### B.3. The SM representation `D = (bar 3,1)_{1/3}`

-/


-- @@ L249-253 verbatim
/-!

#### B.3.1. Chiral indices of `D`

-/


-- @@ L255-257 verbatim
/-- The multiset of chiral indices of the representation `D = (bar 3,1)_{1/3}`
  arising from the matter 5d representations. -/
def chiralIndicesOfD (F : FluxesFive) : Multiset ℤ := F.map (fun f => f.M)


-- @@ L259-263 verbatim
/-!

#### B.3.2. The number of chiral `D`

-/


-- @@ L265-268 verbatim
/-- The total number of chiral `D` representations arising from the matter 5d
  representations. -/
def numChiralD (F : FluxesFive) : ℤ :=
  ((chiralIndicesOfD F).filter (fun x => 0 ≤ x)).sum


-- @@ L270-274 verbatim
/-!

#### B.3.3. The number of anti-chiral `D`

-/


-- @@ L276-279 verbatim
/-- The total number of anti-chiral `D` representations arising from the matter 5d
  representations. -/
def numAntiChiralD (F : FluxesFive) : ℤ :=
  ((chiralIndicesOfD F).filter (fun x => x < 0)).sum


-- @@ L281-285 verbatim
/-!

#### B.3.4. Relation between number of chiral and anti-chiral `D`

-/


-- @@ L287-290 verbatim
lemma numChiralD_eq_sum_sub_numAntiChiralD (F : FluxesFive) :
    F.numChiralD = (chiralIndicesOfD F).sum - F.numAntiChiralD := by
  simpa only [numChiralD, numAntiChiralD, not_le, eq_sub_iff_add_eq] using
    Multiset.sum_filter_add_sum_filter_not (s := chiralIndicesOfD F) (fun x => 0 ≤ x)


-- @@ L292-296 verbatim
/-!

### B.4. The SM representation `L = (1,2)_{-1/2}`

-/


-- @@ L298-302 verbatim
/-!

#### B.4.1. Chiral indices of `L`

-/


-- @@ L304-306 verbatim
/-- The multiset of chiral indices of the representation `L = (1,2)_{-1/2}`
  arising from the matter 5d representations. -/
def chiralIndicesOfL (F : FluxesFive) : Multiset ℤ := F.map (fun f => f.M + f.N)


-- @@ L308-312 verbatim
/-!

#### B.4.2. The number of chiral `L`

-/


-- @@ L314-317 verbatim
/-- The total number of chiral `L` representations arising from the matter 5d
  representations. -/
def numChiralL (F : FluxesFive) : ℤ :=
  ((chiralIndicesOfL F).filter (fun x => 0 ≤ x)).sum


-- @@ L319-323 verbatim
/-!

#### B.4.3. The number of anti-chiral `L`

-/


-- @@ L325-328 verbatim
/-- The total number of anti-chiral `L` representations arising from the matter 5d
  representations. -/
def numAntiChiralL (F : FluxesFive) : ℤ :=
  ((chiralIndicesOfL F).filter (fun x => x < 0)).sum


-- @@ L330-334 verbatim
/-!

#### B.4.4. Relation between number of chiral and anti-chiral `L`

-/


-- @@ L336-339 verbatim
lemma numChiralL_eq_sum_sub_numAntiChiralL (F : FluxesFive) :
    F.numChiralL = (chiralIndicesOfL F).sum - F.numAntiChiralL := by
  simpa only [numChiralL, numAntiChiralL, not_le, eq_sub_iff_add_eq] using
    Multiset.sum_filter_add_sum_filter_not (s := chiralIndicesOfL F) (fun x => 0 ≤ x)


-- @@ L341-345 verbatim
/-!

### B.5. No exotics from the 5-bar matter fields

-/


-- @@ L347-353 verbatim
/-- The condition that the 5d-matter representations do not lead to exotic chiral matter in the
  MSSM spectrum. This corresponds to the conditions that:
- There are 3 chiral `L` representations and no anti-chiral `L` representations.
- There are 3 chiral `D` representations and no anti-chiral `D` representations.
-/
def NoExotics (F : FluxesFive) : Prop :=
  F.numChiralL = 3 ∧ F.numAntiChiralL = 0 ∧ F.numChiralD = 3 ∧ F.numAntiChiralD = 0


-- @@ L355-356 verbatim
instance (F : FluxesFive) : Decidable (F.NoExotics) :=
  instDecidableAnd


-- @@ L358-358 verbatim
end FluxesFive


-- @@ L360-364 verbatim
/-!

## C. Fluxes of the 10d matter representation

-/


-- @@ L366-367 verbatim
/-- The fluxes `(M, N)` of the 10d matter curves of a theory. -/
abbrev FluxesTen : Type := Multiset Fluxes


-- @@ L369-369 verbatim
namespace FluxesTen


-- @@ L371-375 verbatim
/-!

### C.1. Decidability instance on `FluxesTen`

-/


-- @@ L377-378 verbatim
instance : DecidableEq FluxesTen :=
  inferInstanceAs (DecidableEq (Multiset Fluxes))


-- @@ L380-384 verbatim
/-!

### C.2. The proposition for no element to be zero

-/


-- @@ L386-388 verbatim
/-- The proposition on `FluxesTen` such that `(0, 0)` is not in `F`
  and as such each component in `F` leads to chiral matter. -/
abbrev HasNoZero (F : FluxesTen) : Prop := 0 ∉ F


-- @@ L390-394 verbatim
/-!

### C.3. The SM representation `Q = (3,2)_{1/6}`

-/


-- @@ L396-400 verbatim
/-!

#### C.3.1. Chiral indices of `Q`

-/


-- @@ L402-404 verbatim
/-- The multiset of chiral indices of the representation `Q = (3,2)_{1/6}`
  arising from the matter 10d representations, corresponding to `M`. -/
def chiralIndicesOfQ (F : FluxesTen) : Multiset ℤ := F.map (fun f => f.M)


-- @@ L406-410 verbatim
/-!

#### C.3.2. The number of chiral `Q`

-/


-- @@ L412-414 verbatim
/-- The total number of chiral `Q` representations arising from the matter 10d
  representations. -/
def numChiralQ (F : FluxesTen) : ℤ := ((chiralIndicesOfQ F).filter (fun x => 0 ≤ x)).sum


-- @@ L416-420 verbatim
/-!

#### C.3.3. The number of anti-chiral `Q`

-/


-- @@ L422-424 verbatim
/-- The total number of anti-chiral `Q` representations arising from the matter 10d
  representations. -/
def numAntiChiralQ (F : FluxesTen) : ℤ := ((chiralIndicesOfQ F).filter (fun x => x < 0)).sum


-- @@ L426-430 verbatim
/-!

#### C.3.4. Relation between number of chiral and anti-chiral `Q`

-/


-- @@ L432-435 verbatim
lemma numChiralQ_eq_sum_sub_numAntiChiralQ (F : FluxesTen) :
    F.numChiralQ = (chiralIndicesOfQ F).sum - F.numAntiChiralQ := by
  simpa only [numChiralQ, numAntiChiralQ, not_le, eq_sub_iff_add_eq] using
    Multiset.sum_filter_add_sum_filter_not (s := chiralIndicesOfQ F) (fun x => 0 ≤ x)


-- @@ L437-441 verbatim
/-!

### C.4. The SM representation `U = (bar 3,1)_{-2/3}`

-/


-- @@ L443-447 verbatim
/-!

#### C.4.1. Chiral indices of `U`

-/


-- @@ L449-451 verbatim
/-- The multiset of chiral indices of the representation `U = (bar 3,1)_{-2/3}`
  arising from the matter 10d representations, corresponding to `M - N` -/
def chiralIndicesOfU (F : FluxesTen) : Multiset ℤ := F.map (fun f => f.M - f.N)


-- @@ L453-457 verbatim
/-!

#### C.4.2. The number of chiral `U`

-/


-- @@ L459-461 verbatim
/-- The total number of chiral `U` representations arising from the matter 10d
  representations. -/
def numChiralU (F : FluxesTen) : ℤ := ((chiralIndicesOfU F).filter (fun x => 0 ≤ x)).sum


-- @@ L463-467 verbatim
/-!

#### C.4.3. The number of anti-chiral `U`

-/


-- @@ L469-477 verbatim
/-- The total number of anti-chiral `U` representations arising from the matter 10d
  representations. -/
def numAntiChiralU (F : FluxesTen) : ℤ := ((chiralIndicesOfU F).filter (fun x => x < 0)).sum

/-

#### C.4.4. Relation between number of chiral and anti-chiral `Q`

-/


-- @@ L479-482 verbatim
lemma numChiralU_eq_sum_sub_numAntiChiralU (F : FluxesTen) :
    F.numChiralU = (chiralIndicesOfU F).sum - F.numAntiChiralU := by
  simpa only [numChiralU, numAntiChiralU, not_le, eq_sub_iff_add_eq] using
    Multiset.sum_filter_add_sum_filter_not (s := chiralIndicesOfU F) (fun x => 0 ≤ x)

-- @@ L483-487 verbatim
/-!

### C.5. The SM representation `E = (1,1)_{1}`

-/


-- @@ L489-493 verbatim
/-!

#### C.5.1. Chiral indices of `E`

-/


-- @@ L495-497 verbatim
/-- The multiset of chiral indices of the representation `E = (1,1)_{1}`
  arising from the matter 10d representations, corresponding to `M + N` -/
def chiralIndicesOfE (F : FluxesTen) : Multiset ℤ := F.map (fun f => f.M + f.N)


-- @@ L499-503 verbatim
/-!

#### C.5.2. The number of chiral `E`

-/


-- @@ L505-507 verbatim
/-- The total number of chiral `E` representations arising from the matter 10d
  representations. -/
def numChiralE (F : FluxesTen) : ℤ := ((chiralIndicesOfE F).filter (fun x => 0 ≤ x)).sum


-- @@ L509-513 verbatim
/-!

#### C.5.3. The number of anti-chiral `E`

-/


-- @@ L515-517 verbatim
/-- The total number of anti-chiral `E` representations arising from the matter 10d
  representations. -/
def numAntiChiralE (F : FluxesTen) : ℤ := ((chiralIndicesOfE F).filter (fun x => x < 0)).sum


-- @@ L519-523 verbatim
/-!

#### C.5.4. Relation between number of chiral and anti-chiral `E`

-/


-- @@ L525-528 verbatim
lemma numChiralE_eq_sum_sub_numAntiChiralE (F : FluxesTen) :
    F.numChiralE = (chiralIndicesOfE F).sum - F.numAntiChiralE := by
  simpa only [numChiralE, numAntiChiralE, not_le, eq_sub_iff_add_eq] using
    Multiset.sum_filter_add_sum_filter_not (s := chiralIndicesOfE F) (fun x => 0 ≤ x)


-- @@ L530-534 verbatim
/-!

### C.6. No exotics from the 10d matter fields

-/


-- @@ L536-545 verbatim
/-- The condition that the 10d-matter representations do not lead to exotic chiral matter in the
  MSSM spectrum. This corresponds to the conditions that:
- There are 3 chiral `Q` representations and no anti-chiral `Q` representations.
- There are 3 chiral `U` representations and no anti-chiral `U` representations.
- There are 3 chiral `E` representations and no anti-chiral `E` representations.
-/
def NoExotics (F : FluxesTen) : Prop :=
  F.numChiralQ = 3 ∧ F.numAntiChiralQ = 0 ∧
  F.numChiralU = 3 ∧ F.numAntiChiralU = 0 ∧
  F.numChiralE = 3 ∧ F.numAntiChiralE = 0


-- @@ L547-548 verbatim
instance (F : FluxesTen) : Decidable (F.NoExotics) :=
  instDecidableAnd


-- @@ L550-550 verbatim
end FluxesTen


-- @@ L552-552 verbatim
end SU5


-- @@ L554-554 verbatim
end FTheory
