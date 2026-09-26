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
module

public import FormalConjecturesForMathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Maximal


-- @@ L21-25 verbatim
/-!
# Maximal right ideals

This file defines maximal right ideals and gives their basic order-theoretic API.
-/


-- @@ L27-27 verbatim
@[expose] public section


-- @@ L29-29 verbatim
universe u


-- @@ L31-31 verbatim
namespace RightIdeal


-- @@ L33-33 verbatim
section Semiring


-- @@ L35-35 verbatim
variable {R : Type u} [Semiring R] (I : RightIdeal R)


-- @@ L37-40 verbatim
/-- A right ideal is maximal if it is maximal among the proper right ideals. -/
class IsMaximal : Prop where
  /-- A maximal right ideal is a coatom in the lattice of right ideals. -/
  out : IsCoatom I


-- @@ L42-43 verbatim
theorem isMaximal_def : I.IsMaximal ↔ IsCoatom I :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩


-- @@ L45-46 verbatim
theorem IsMaximal.ne_top (h : I.IsMaximal) : I ≠ ⊤ :=
  (isMaximal_def I).1 h |>.1


-- @@ L48-49 verbatim
theorem IsMaximal.lt_top (h : I.IsMaximal) : I < ⊤ :=
  h.ne_top.lt_top


-- @@ L51-54 verbatim
theorem IsMaximal.eq_of_le {J : RightIdeal R} (hI : I.IsMaximal) (hJ : J ≠ ⊤)
    (hIJ : I ≤ J) : I = J :=
  eq_iff_le_not_lt.2
    ⟨hIJ, fun h => hJ (((isMaximal_def I).1 hI).2 J h)⟩


-- @@ L56-58 verbatim
theorem IsMaximal.eq_iff_le {J : RightIdeal R} (hI : I.IsMaximal) (hJ : J ≠ ⊤) :
    I = J ↔ I ≤ J :=
  ⟨fun h => h.le, fun h => IsMaximal.eq_of_le I hI hJ h⟩


-- @@ L60-60 verbatim
end Semiring


-- @@ L62-62 verbatim
section CommSemiring


-- @@ L64-64 verbatim
variable {R : Type u} [CommSemiring R]


-- @@ L66-69 verbatim
@[simp]
theorem isMaximal_toIdeal_iff (I : RightIdeal R) : I.toIdeal.IsMaximal ↔ I.IsMaximal := by
  rw [Ideal.isMaximal_def, isMaximal_def]
  exact (orderIsoIdeal R).isCoatom_iff I


-- @@ L71-75 verbatim
@[simp]
theorem _root_.Ideal.isMaximal_toRightIdeal_iff (I : Ideal R) :
    I.toRightIdeal.IsMaximal ↔ I.IsMaximal := by
  rw [Ideal.isMaximal_def, RightIdeal.isMaximal_def]
  exact (orderIsoIdeal R).symm.isCoatom_iff I


-- @@ L77-77 verbatim
end CommSemiring


-- @@ L79-79 verbatim
end RightIdeal
