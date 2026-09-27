/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import LeanPool.BlockSpectralSensitivity.Defs.Subcube
public import LeanPool.BlockSpectralSensitivity.Spectral.Bipartite


-- @@ L11-30 verbatim
/-!
# Certificate families

A `CertFamily V ι` packages exactly the hypotheses of the Spectral Lemma of Section 11:
a family `P : ι → PartialAssign V` of partial assignments such that

* every `C_i = C(P i)` has codimension `c`;
* every pair `C_i, C_j` (`i ≠ j`) has exactly one conflicting fixed literal;
* every point of the union has at most `A` other certificates at distance `1`;
* every point of the union has at most `B` other certificates at distance at most `2`.

`F.ind` is the indicator of the union, `F.owner x` is the unique index `i` with
`x ∈ C_i`, and `F.conflictCoord` is the unique conflict coordinate of two distinct certificates.

The Spectral Lemma itself (`lam F.ind ^ 2 ≤ c + 2 √((c-1) A B)`) is proved in
`BSLambda/Spectral/CertUnion.lean`.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/


-- @@ L32-32 verbatim
@[expose] public section


-- @@ L34-34 verbatim
namespace BSLambda


-- @@ L36-36 verbatim
variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]


-- @@ L38-60 verbatim
/-- The hypotheses of the Spectral Lemma of Section 11 of `bs_lambda.txt`: a family of
pairwise-conflicting certificate subcubes of common codimension `c` with local
certificate-list bounds `A` (at distance one) and `B` (at distance at most two). -/
structure CertFamily (V ι : Type*) [Fintype V] [DecidableEq V] [Fintype ι]
    [DecidableEq ι] where
  /-- The partial assignment cutting out the `i`-th certificate subcube. -/
  P : ι → PartialAssign V
  /-- The common codimension of the certificates. -/
  c : ℕ
  /-- The radius-one certificate-list bound (`A = 3` for the construction). -/
  A : ℕ
  /-- The radius-two certificate-list bound (`B = 7` for the construction). -/
  B : ℕ
  /-- Every certificate has codimension `c`. -/
  codim_eq : ∀ i, (P i).codim = c
  /-- Distinct certificates have exactly one conflicting fixed literal. -/
  uniqueConflict : ∀ i j, i ≠ j → ∃! v, (P i).Conflict (P j) v
  /-- Property (L1) of Section 6. -/
  listOne : ∀ i x, (P i).Sat x →
    (Finset.univ.filter fun j => j ≠ i ∧ (P j).dist x = 1).card ≤ A
  /-- Property (L2) of Section 6. -/
  listTwo : ∀ i x, (P i).Sat x →
    (Finset.univ.filter fun j => j ≠ i ∧ (P j).dist x ≤ 2).card ≤ B


-- @@ L62-62 verbatim
namespace CertFamily


-- @@ L64-64 verbatim
variable (F : CertFamily V ι)


-- @@ L66-67 verbatim
/-- The unique conflict coordinate `q_{ij}` of two distinct certificates (Section 4). -/
noncomputable def conflictCoord {i j : ι} (h : i ≠ j) : V := (F.uniqueConflict i j h).choose


-- @@ L69-71 verbatim
/-- The conflict coordinate does conflict. -/
lemma conflict_conflictCoord {i j : ι} (h : i ≠ j) : (F.P i).Conflict (F.P j) (F.conflictCoord h) :=
  (F.uniqueConflict i j h).choose_spec.1


-- @@ L73-76 verbatim
/-- The conflict coordinate is the only coordinate that conflicts. -/
lemma eq_conflictCoord {i j : ι} (h : i ≠ j) {v : V} (hv : (F.P i).Conflict (F.P j) v) :
    v = F.conflictCoord h :=
  (F.uniqueConflict i j h).choose_spec.2 v hv


-- @@ L78-82 verbatim
/-! ### The indicator of the union

`ind` is a distinct head symbol from `PartialAssign.indUnion`, so the `simp` lemmas of the
latter do not fire on it; the first three lemmas below restate them for `ind`.
-/


-- @@ L84-85 verbatim
/-- The indicator `f` of the union of the certificate subcubes (Section 3.3). -/
def ind : Input V → Bool := PartialAssign.indUnion F.P


-- @@ L87-89 verbatim
/-- A point is positive exactly when some certificate subcube contains it. -/
@[simp] lemma ind_eq_true_iff {x : Input V} : F.ind x = true ↔ ∃ i, (F.P i).Sat x :=
  PartialAssign.indUnion_eq_true_iff


-- @@ L91-93 verbatim
/-- A point is negative exactly when no certificate subcube contains it. -/
@[simp] lemma ind_eq_false_iff {x : Input V} : F.ind x = false ↔ ∀ i, ¬ (F.P i).Sat x :=
  PartialAssign.indUnion_eq_false_iff


-- @@ L95-97 verbatim
/-- Every point of a certificate subcube is positive. -/
lemma ind_eq_true_of_sat {i : ι} {x : Input V} (h : (F.P i).Sat x) : F.ind x = true :=
  PartialAssign.indUnion_eq_true_of_sat h


-- @@ L99-104 verbatim
/-- Flipping a coordinate that a certificate leaves free keeps the point inside it, hence
positive (Section 11.2).  This is the source of every "one midpoint is positive"
argument in `BSLambda/Spectral/GramClass.lean`. -/
theorem ind_flipSet_singleton_eq_true {i : ι} {x : Input V} (hx : (F.P i).Sat x) {p : V}
    (hp : p ∉ (F.P i).fixedSet) : F.ind (flipSet x {p}) = true :=
  F.ind_eq_true_of_sat (hx.flipSet_singleton hp)


-- @@ L106-114 verbatim
/-- Contrapositive of `ind_flipSet_singleton_eq_true`: a negative single flip of a positive
input can only happen at a coordinate that the input's own certificate fixes
(Section 11.2). -/
theorem mem_fixedSet_of_ind_flipSet_singleton_eq_false {i : ι} {x : Input V}
    (hx : (F.P i).Sat x) {p : V} (hp : F.ind (flipSet x {p}) = false) :
    p ∈ (F.P i).fixedSet := by
  by_contra hc
  rw [F.ind_flipSet_singleton_eq_true hx hc] at hp
  exact Bool.noConfusion hp


-- @@ L116-120 verbatim
/-- Distinct certificates are disjoint, so a point lies in at most one of them
(Section 4). -/
lemma sat_unique {i j : ι} {x : Input V} (hi : (F.P i).Sat x) (hj : (F.P j).Sat x) : i = j :=
  PartialAssign.sat_unique_of_conflict
    (fun _ _ hij ↦ ⟨_, F.conflict_conflictCoord hij⟩) hi hj


-- @@ L122-124 verbatim
/-- The *owner* of a positive input: the unique index whose certificate contains it
(Section 4). -/
noncomputable def owner (x : Ones F.ind) : ι := (F.ind_eq_true_iff.1 x.2).choose


-- @@ L126-128 verbatim
/-- The owner's certificate does contain the point. -/
lemma owner_sat (x : Ones F.ind) : (F.P (F.owner x)).Sat x.1 :=
  (F.ind_eq_true_iff.1 x.2).choose_spec


-- @@ L130-132 verbatim
/-- The owner is the only index whose certificate contains the point. -/
lemma owner_eq {x : Ones F.ind} {i : ι} (h : (F.P i).Sat x.1) : F.owner x = i :=
  F.sat_unique (F.owner_sat x) h


-- @@ L134-139 verbatim
/-- Only the `c` coordinates fixed by a containing certificate can be sensitive, so every
positive input has sensitivity at most `c` (Section 11.1). -/
lemma sensAt_le_c {i : ι} {x : Input V} (hx : (F.P i).Sat x) : sensAt F.ind x ≤ F.c := by
  rw [← F.codim_eq i, PartialAssign.codim_eq_card_fixedSet]
  exact sensAt_le_card fun v hv ↦ F.mem_fixedSet_of_ind_flipSet_singleton_eq_false hx
    (Bool.eq_false_iff.2 fun h ↦ mem_sensCoords.1 hv (h.trans (F.ind_eq_true_of_sat hx).symm))


-- @@ L141-144 verbatim
/-- The diagonal of the positive-side Gram matrix is bounded by `c` (Section 11.1). -/
lemma gram_diag_le (x : Ones F.ind) : gram F.ind x x ≤ (F.c : ℝ) := by
  rw [gram_diag]
  exact_mod_cast F.sensAt_le_c (F.owner_sat x)


-- @@ L146-146 verbatim
end CertFamily


-- @@ L148-148 verbatim
end BSLambda
