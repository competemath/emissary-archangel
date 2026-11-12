/-
# The total space of an operad, and the `⋆` product

Grade an operad by **arity minus one**: write `α : P (j + 1)` for an element of degree `j`.
The circle product

    α ⋆ β = ∑ i, α ∘ᵢ β

is then additive in the degree: for `α : P (j + 1)` and `β : P (k + 1)` every summand
`compFin i α β` lives in `P ((j + 1) - 1 + (k + 1))`, which Lean reduces definitionally to
`P (j + k + 1)`. So the sum is well-formed with **no reindexing at all** — a direct payoff of
the positional convention, since `compFin` already lands in a uniform arity no matter which slot
is used.

This is the unsigned skeleton of the structure the deformation theory of operads runs on: the
commutator of `⋆` is a Lie bracket. With the suspension signs of `Operad.DG` (in
`Operad.TotalSpaceS`), an operad structure is a Maurer–Cartan element and `d = ⁅Θ, -⁆` is the
differential whose cohomology controls deformations (`Operad.Cohomology`).
-/
import Operad.Constructions
import Mathlib.Algebra.BigOperators.Fin


-- @@ L23-23 verbatim
universe u v


-- @@ L25-25 verbatim
namespace Operad


-- @@ L27-27 verbatim
open NSOperad Finset


-- @@ L29-30 verbatim
variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P]


-- @@ L32-35 verbatim
/-- The circle product `α ⋆ β = ∑ᵢ α ∘ᵢ β`, summing over every slot of `α`. Degrees add:
`P (j+1) → P (k+1) → P (j+k+1)`. -/
def star {j k : ℕ} (α : P (j + 1)) (β : P (k + 1)) : P (j + k + 1) :=
  ∑ i : Fin (j + 1), compFin (R := R) i α β


-- @@ L37-37 verbatim
@[inherit_doc] scoped infixl:70 " ⋆ " => star


-- @@ L39-40 verbatim
lemma star_def {j k : ℕ} (α : P (j + 1)) (β : P (k + 1)) :
    star (R := R) α β = ∑ i : Fin (j + 1), compFin (R := R) i α β := rfl


-- @@ L42-48 verbatim
/-- Pulling a scalar out of a finite sum, obtained from `map_sum` for `LinearMap.lsmul`.
(`Finset.smul_sum` does exist, in `Mathlib.Algebra.BigOperators.GroupWithZero.Action`, but it is
not imported here; it is also stated for a general `DistribSMul`, which `rw` and `simp` both fail
to match against a `Module`-derived action.) -/
private lemma smul_sum' {M : Type*} [AddCommGroup M] [Module R M] {n : ℕ} (r : R)
    (f : Fin n → M) : r • ∑ i, f i = ∑ i, r • f i :=
  map_sum (LinearMap.lsmul R M r) f Finset.univ


-- @@ L50-50 verbatim
/-! ### Bilinearity -/


-- @@ L52-56 verbatim
lemma star_add_left {j k : ℕ} (α α' : P (j + 1)) (β : P (k + 1)) :
    star (R := R) (α + α') β = star (R := R) α β + star (R := R) α' β := by
  unfold star
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => compFin_add_left i α α' β


-- @@ L58-62 verbatim
lemma star_add_right {j k : ℕ} (α : P (j + 1)) (β β' : P (k + 1)) :
    star (R := R) α (β + β') = star (R := R) α β + star (R := R) α β' := by
  unfold star
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => compFin_add_right i α β β'


-- @@ L64-68 verbatim
lemma star_smul_left {j k : ℕ} (r : R) (α : P (j + 1)) (β : P (k + 1)) :
    star (R := R) (r • α) β = r • star (R := R) α β := by
  unfold star
  rw [smul_sum']
  exact Finset.sum_congr rfl fun i _ => compFin_smul_left i r α β


-- @@ L70-74 verbatim
lemma star_smul_right {j k : ℕ} (r : R) (α : P (j + 1)) (β : P (k + 1)) :
    star (R := R) α (r • β) = r • star (R := R) α β := by
  unfold star
  rw [smul_sum']
  exact Finset.sum_congr rfl fun i _ => compFin_smul_right i r α β


-- @@ L76-79 verbatim
@[simp] lemma zero_star {j k : ℕ} (β : P (k + 1)) :
    star (R := R) (0 : P (j + 1)) β = 0 := by
  unfold star
  exact Finset.sum_eq_zero fun i _ => compFin_zero_left i β


-- @@ L81-84 verbatim
@[simp] lemma star_zero {j k : ℕ} (α : P (j + 1)) :
    star (R := R) α (0 : P (k + 1)) = 0 := by
  unfold star
  exact Finset.sum_eq_zero fun i _ => compFin_zero_right i α


-- @@ L86-86 verbatim
/-! ### The unit -/


-- @@ L88-94 verbatim
/-- Plugging the identity into any slot gives back the operation. -/
lemma compFin_one {m : ℕ} (i : Fin m) (α : P m) :
    compFin (R := R) i α (one (R := R) (P := P))
      = reindex R P (by have := i.isLt; omega) α := by
  unfold compFin
  rw [comp_one_right]
  simp


-- @@ L96-104 verbatim
/-- Filling the single slot of the identity operation does nothing. The reindexing is genuinely
needed: `0 + (k + 1)` is *not* definitionally `k + 1` in Lean, since `Nat.add` recurses on its
second argument. -/
lemma compFin_zero_one {k : ℕ} (β : P (k + 1)) :
    reindex R P (by omega)
        (compFin (R := R) (0 : Fin (0 + 1)) (one (R := R) (P := P)) β) = β := by
  have h0 : (0 : Fin (0 + 1)) = ⟨0, by omega⟩ := by apply Fin.ext; simp
  rw [h0, compFin_eq_comp 0 0, reindex_reindex]
  exact comp_one_left β


-- @@ L106-110 verbatim
/-- `1 ⋆ β = β`: the identity operation has a single slot, and filling it does nothing. -/
@[simp] lemma one_star {k : ℕ} (β : P (k + 1)) :
    reindex R P (by omega) (star (R := R) (one (R := R) (P := P)) β) = β := by
  rw [star_def, Fin.sum_univ_one]
  exact compFin_zero_one β


-- @@ L112-121 verbatim
/-- `α ⋆ 1 = (arity) • α`: every one of the `j + 1` slots contributes a copy of `α`.
Here no reindexing is needed, because `j + 0` *is* definitionally `j`. -/
@[simp] lemma star_one {j : ℕ} (α : P (j + 1)) :
    star (R := R) α (one (R := R) (P := P)) = (j + 1) • α := by
  rw [star_def]
  have h : ∀ i : Fin (j + 1), compFin (R := R) i α (one (R := R) (P := P)) = α := fun i => by
    rw [compFin_one]; exact reindex_self _ _
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  rfl


-- @@ L123-126 verbatim
/-! ### The Lie bracket

The commutator of `⋆`. Once the pre-Lie identity is available this is a genuine Lie bracket;
antisymmetry below holds unconditionally. -/


-- @@ L128-130 verbatim
/-- The graded commutator `[α, β] = α ⋆ β - β ⋆ α`. -/
def bracket {j k : ℕ} (α : P (j + 1)) (β : P (k + 1)) : P (j + k + 1) :=
  star (R := R) α β - reindex R P (by omega) (star (R := R) β α)


-- @@ L132-132 verbatim
@[inherit_doc] scoped notation "⁅" α ", " β "⁆" => bracket α β


-- @@ L134-136 verbatim
lemma bracket_def {j k : ℕ} (α : P (j + 1)) (β : P (k + 1)) :
    bracket (R := R) α β
      = star (R := R) α β - reindex R P (by omega) (star (R := R) β α) := rfl


-- @@ L138-141 verbatim
/-- The bracket is antisymmetric. -/
lemma bracket_antisymm {j k : ℕ} (α : P (j + 1)) (β : P (k + 1)) :
    bracket (R := R) α β = - reindex R P (by omega) (bracket (R := R) β α) := by
  rw [bracket_def, bracket_def, map_sub, neg_sub, reindex_reindex, reindex_self]


-- @@ L143-145 verbatim
@[simp] lemma bracket_self {j : ℕ} (α : P (j + 1)) :
    bracket (R := R) α α = 0 := by
  rw [bracket_def, reindex_self, sub_self]


-- @@ L147-150 verbatim
lemma bracket_add_left {j k : ℕ} (α α' : P (j + 1)) (β : P (k + 1)) :
    bracket (R := R) (α + α') β = bracket (R := R) α β + bracket (R := R) α' β := by
  rw [bracket_def, bracket_def, bracket_def, star_add_left, star_add_right, map_add]
  abel


-- @@ L152-155 verbatim
lemma bracket_add_right {j k : ℕ} (α : P (j + 1)) (β β' : P (k + 1)) :
    bracket (R := R) α (β + β') = bracket (R := R) α β + bracket (R := R) α β' := by
  rw [bracket_def, bracket_def, bracket_def, star_add_right, star_add_left, map_add]
  abel


-- @@ L157-157 verbatim
end Operad
