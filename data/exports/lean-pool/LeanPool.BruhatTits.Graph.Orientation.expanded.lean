/-
Copyright (c) 2026 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import LeanPool.BruhatTits.Graph.GroupAction
public import LeanPool.BruhatTits.Utils.ValuationRings


-- @@ L11-32 verbatim
/-!
# Orientation on the Bruhat-Tits tree

The Bruhat-Tits tree admits a natural orientation, by which we mean a partition
of the vertices in odd and even, which can be interpreted as a direction on the edges.

We say an `R`-lattice `L` is *even* if the additive valuation of the determinant of an
`R`-basis of `L` is even. This is independent of the choice of the
basis (see `BruhatTits.Lattice.zaddVal_det_eq_of_basis`) and invariant under homothety
(see `BruhatTits.Lattice.isEven_smul_of_isEven`). A vertex is then *even* if a (equivalently all)
representative is even.

Finally, we define a `±1`-valued *weight function* on the vertices by sending even vertices
to `1` and odd vertices to `-1`. This will be later used to define the harmonic co-chains on the
Bruhat-Tits tree (see `BruhatTits.Harmonic.Application`).

## SL₂ action

While the GL₂ action is transitive, the SL₂ action preserves the orientation, i.e. it preserves
evenness of vertices (see `BruhatTits.isEven_specialLinearGroup_smul_iff`).

-/


-- @@ L34-34 verbatim
@[expose] public section


-- @@ L36-36 verbatim
open Module



-- @@ L39-39 verbatim
suppress_compilation


-- @@ L41-41 verbatim
namespace BruhatTits


-- @@ L43-43 verbatim
variable {K : Type*} [Field K] {R : Subring K}


-- @@ L45-45 verbatim
local notation "v" => ValuationRing.valuation R K


-- @@ L47-47 verbatim
namespace Lattice


-- @@ L49-49 verbatim
variable [IsDiscreteValuationRing R] [IsFractionRing R K]


-- @@ L51-55 verbatim
/-- The valuation associated to a lattice is the additive valuation of the determinant of a
basis. This is independent of the choice of a basis
(see `BruhatTits.Lattice.zaddVal_det_eq_of_basis`), but not invariant under homothety. -/
def valuation (L : Lattice R) : ℤ :=
  zaddVal (R := R) (Matrix.GeneralLinearGroup.det L.basis.toGL)


-- @@ L57-64 verbatim
lemma zaddVal_det_eq_of_basis {L : Lattice R} (b₁ b₂ : Basis (Fin 2) R L.M) :
    zaddVal (R := R) (Matrix.GeneralLinearGroup.det b₁.toGL) =
      zaddVal (R := R) (Matrix.GeneralLinearGroup.det b₂.toGL) := by
  obtain ⟨⟨g⟩, (h : (MulOpposite.op g) • _ = _)⟩ :=
    MulAction.IsPretransitive.exists_smul_eq (M := (GL (Fin 2) R)ᵐᵒᵖ) b₁ b₂
  subst h
  simp only [basis_smul_toGL, map_mul, zaddVal_mul, left_eq_add, GL.map_det]
  simp


-- @@ L66-68 verbatim
/-- A lattice is called even, if the determinant of the matrix spanned
by a basis has even additive valuation. -/
def IsEven (L : Lattice R) : Prop := Even L.valuation


-- @@ L70-72 verbatim
/-- A lattice is called odd, if the determinant of the matrix spanned
by a basis has odd additive valuation. -/
def IsOdd (L : Lattice R) : Prop := Odd L.valuation


-- @@ L74-76 verbatim
lemma isOdd_iff_notEven (L : Lattice R) :
    L.IsOdd ↔ ¬ L.IsEven :=
  (Int.not_even_iff_odd).symm


-- @@ L78-82 verbatim
lemma isEven_iff (L : Lattice R) :
    L.IsEven ↔ ∃ (b : Basis (Fin 2) R L.M),
      Even (zaddVal (R := R) (b.toGL.det)) := by
  refine ⟨fun h ↦ ⟨L.basis, h⟩, fun ⟨b, h⟩ ↦ ?_⟩
  rwa [zaddVal_det_eq_of_basis b L.basis] at h


-- @@ L84-94 verbatim
lemma isEven_iff' (L : Lattice R) :
    L.IsEven ↔ ∃ (b : Basis (Fin 2) K (Fin 2 → K)),
      b.toLattice = L ∧ Even (zaddVal (R := R) b.toGeneralLinearGroup.det) := by
  rw [isEven_iff]
  refine ⟨fun ⟨b, hb⟩ ↦ ⟨b.fromLattice, by simp, hb⟩, ?_⟩
  rintro ⟨b, rfl, hb⟩
  use b.restrictToLattice
  have : (b.restrictToLattice (R := R)).toGL = b.toGeneralLinearGroup := by
    ext i j
    rw [Basis.toGL_apply, Basis.toGeneralLinearGroup_apply, Basis.restrictToLattice_apply]
  rwa [this]


-- @@ L96-96 verbatim
open Matrix


-- @@ L98-104 verbatim
lemma isEven_smul_of_isEven {L : Lattice R} (a : Kˣ) (h : L.IsEven) :
    (a • L).IsEven := by
  rw [isEven_iff]
  use (mulBasisScalar a L.basis)
  simp only [mulBasisScalar_toGL, _root_.map_mul, zaddVal_mul]
  refine Even.add ?_ h
  simp [Matrix.GL.diagonal_det, sq]


-- @@ L106-110 verbatim
lemma isEven_smul_iff (L : Lattice R) (a : Kˣ) :
    (a • L).IsEven ↔ L.IsEven := by
  refine ⟨fun h ↦ ?_, isEven_smul_of_isEven a⟩
  rw [show L = a⁻¹ • a • L by simp]
  exact isEven_smul_of_isEven _ h


-- @@ L112-115 verbatim
lemma isEven_iff_of_isSimilar {M L : Lattice R} (h : IsSimilar R M L) :
    M.IsEven ↔ L.IsEven := by
  obtain ⟨a, rfl⟩ := h
  rw [isEven_smul_iff]


-- @@ L117-120 verbatim
lemma isOdd_iff_of_isSimilar {M L : Lattice R} (h : IsSimilar R M L) :
    M.IsOdd ↔ L.IsOdd := by
  rw [isOdd_iff_notEven, isOdd_iff_notEven, not_iff_not]
  exact isEven_iff_of_isSimilar h


-- @@ L122-122 verbatim
end Lattice


-- @@ L124-124 verbatim
section «SLAction»


-- @@ L126-127 verbatim
instance : MulAction (Matrix.SpecialLinearGroup (Fin 2) K) (Lattice R) :=
  MulAction.compHom (BruhatTits.Lattice R) Matrix.SpecialLinearGroup.toGL


-- @@ L129-130 verbatim
instance : MulAction (Matrix.SpecialLinearGroup (Fin 2) K) (Vertices R) :=
  MulAction.compHom (Vertices R) Matrix.SpecialLinearGroup.toGL


-- @@ L132-134 verbatim
@[simp]
lemma specialLinearGroupToGL_smul (g : Matrix.SpecialLinearGroup (Fin 2) K) (L : Lattice R) :
    g.toGL • L = g • L := rfl


-- @@ L136-136 verbatim
end «SLAction»


-- @@ L138-138 verbatim
section «Orientation»


-- @@ L140-140 verbatim
variable [IsDiscreteValuationRing R] [IsFractionRing R K]


-- @@ L142-144 verbatim
/-- A vertex `⟦L⟧` is called even, if `L` is even. This is independent of the choice of `L`. -/
def IsEven (x : Vertices R) : Prop :=
  Quotient.lift Lattice.IsEven (fun _ _ hML ↦ propext <| Lattice.isEven_iff_of_isSimilar hML) x


-- @@ L146-148 verbatim
/-- A vertex `⟦L⟧` is called odd, if `L` is odd. This is independent of the choice of `L`. -/
def IsOdd (x : Vertices R) : Prop :=
  Quotient.lift Lattice.IsOdd (fun _ _ hML ↦ propext <| Lattice.isOdd_iff_of_isSimilar hML) x


-- @@ L150-151 verbatim
lemma isOdd_iff_notEven (x : Vertices R) : IsOdd x ↔ ¬ IsEven x := by
  exact Quotient.inductionOn x fun L ↦ L.isOdd_iff_notEven


-- @@ L153-154 verbatim
@[simp]
lemma isEven_mk (L : Lattice R) : IsEven ⟦L⟧ ↔ L.IsEven := .rfl


-- @@ L156-159 verbatim
open Classical in
/-- A canonical weight function on the vertices of the BT tree:
Even vertices have weight `1` and odd vertices have weight `-1`. -/
def BTweight (A : Type*) [CommRing A] (x : Vertices R) : Aˣ := if IsEven x then 1 else -1


-- @@ L161-162 verbatim
instance : GraphAction (Matrix.SpecialLinearGroup (Fin 2) K) (BTgraph (R := R)) where
  smul_adj_smul g x y := (adj_smul_smul_iff_adj (Matrix.SpecialLinearGroup.toGL g) x y).mpr


-- @@ L164-172 verbatim
lemma _root_.BruhatTits.Lattice.isEven_specialLinearGroup_smul {L : Lattice R} (h : L.IsEven)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) : (g • L).IsEven := by
  rw [Lattice.isEven_iff'] at h ⊢
  obtain ⟨bL, hbL, he⟩ := h
  refine ⟨g.toGL • bL, ?_, ?_⟩
  · subst hbL
    rw [Basis.smulGL_toLattice]
    rfl
  · simpa [Basis.smulGL_toGeneralLinearGroup]


-- @@ L174-180 verbatim
@[simp]
lemma _root_.BruhatTits.Lattice.isEven_specialLinearGroup_smul_iff {L : Lattice R}
    (g : Matrix.SpecialLinearGroup (Fin 2) K) :
    (g • L).IsEven ↔ L.IsEven := by
  refine ⟨fun h ↦ ?_, fun h ↦ Lattice.isEven_specialLinearGroup_smul h g⟩
  convert Lattice.isEven_specialLinearGroup_smul h g⁻¹
  simp


-- @@ L182-187 verbatim
lemma isEven_specialLinearGroup_smul {x : Vertices R} (h : IsEven x)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) : IsEven (g • x) := by
  revert h
  refine Quotient.inductionOn x fun x h ↦ ?_
  change IsEven ⟦g • x⟧
  simpa


-- @@ L189-194 verbatim
@[simp]
lemma isEven_specialLinearGroup_smul_iff {x : Vertices R}
    (g : Matrix.SpecialLinearGroup (Fin 2) K) : IsEven (g • x) ↔ IsEven x := by
  refine ⟨fun h ↦ ?_, fun h ↦ isEven_specialLinearGroup_smul h g⟩
  convert isEven_specialLinearGroup_smul h g⁻¹
  simp


-- @@ L196-198 verbatim
lemma isOdd_specialLinearGroup_smul_iff {x : Vertices R}
    (g : Matrix.SpecialLinearGroup (Fin 2) K) : IsOdd (g • x) ↔ IsOdd x := by
  simp [isOdd_iff_notEven]


-- @@ L200-200 verbatim
end «Orientation»


-- @@ L202-202 verbatim
end BruhatTits
