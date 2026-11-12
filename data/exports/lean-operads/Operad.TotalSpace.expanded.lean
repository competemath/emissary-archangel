/-
# The total space as a pre-Lie ring

`Operad.PreLie` proves the pre-Lie identity in *graded* form: `⋆` takes `P (j+1)` and `P (k+1)`
to `P (j+k+1)`, and `star_assoc_symm` is an identity between elements of a fixed arity. To land
on mathlib's `RightPreLieRing` the grading has to be bundled into a single object.

That object is `⨁ k, Piece R P k`, graded by **arity minus one**. Mathlib's graded-ring machinery
does most of the work: `DirectSum.GNonUnitalNonAssocSemiring` asks for exactly a graded
multiplication together with `mul_zero`, `zero_mul`, `mul_add` and `add_mul`, which are the four
bilinearity lemmas for `⋆`, and it produces the `NonUnitalNonAssocRing` structure that
`RightPreLieRing` extends.

`Piece` is a type synonym for `P (k + 1)` carrying `R` as a phantom parameter. Without it the
graded instances below would have `R` appearing nowhere in their conclusions, and Lean rejects
them for having no synthesization order.
-/
import Operad.PreLie
import Mathlib.Algebra.DirectSum.Ring
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.NonAssoc.PreLie.Basic
import Mathlib.Algebra.Ring.Associator
import Mathlib.Algebra.Lie.Basic
import Operad.Endomorphism


-- @@ L26-26 verbatim
universe u v


-- @@ L28-28 verbatim
namespace Operad


-- @@ L30-30 verbatim
open NSOperad DirectSum


-- @@ L32-35 verbatim
/-- The degree-`k` piece of the total space: operations of arity `k + 1`. Arity `0` is excluded,
since it carries no degree and the deformation complex does not use it. -/
@[nolint unusedArguments]
def Piece (R : Type u) [CommRing R] (P : ℕ → Type v) (k : ℕ) : Type v := P (k + 1)


-- @@ L37-37 verbatim
section


-- @@ L39-40 verbatim
variable {R : Type u} [CommRing R] {P : ℕ → Type v}
  [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)]


-- @@ L42-42 verbatim
instance (k : ℕ) : AddCommGroup (Piece R P k) := inferInstanceAs (AddCommGroup (P (k + 1)))


-- @@ L44-44 verbatim
instance (k : ℕ) : Module R (Piece R P k) := inferInstanceAs (Module R (P (k + 1)))


-- @@ L46-46 verbatim
variable [NSOperad R P]


-- @@ L48-50 verbatim
/-- The circle product as a graded multiplication: degrees add. -/
instance : GradedMonoid.GMul (Piece R P) where
  mul {_ _} a b := star (R := R) a b


-- @@ L52-58 verbatim
/-- The four bilinearity lemmas for `⋆` are exactly what a graded non-unital non-associative
semiring structure asks for. -/
instance : DirectSum.GNonUnitalNonAssocSemiring (Piece R P) where
  mul_zero a := star_zero (R := R) a
  zero_mul b := zero_star (R := R) b
  mul_add a b c := star_add_right (R := R) a b c
  add_mul a b c := star_add_left (R := R) a b c


-- @@ L60-64 verbatim
/-- The total space of an operad, graded by arity minus one. -/
@[nolint unusedArguments]
abbrev Tot (R : Type u) [CommRing R] (P : ℕ → Type v)
    [∀ n, AddCommGroup (P n)] [∀ n, Module R (P n)] [NSOperad R P] : Type v :=
  ⨁ k : ℕ, Piece R P k


-- @@ L66-66 verbatim
example : NonUnitalNonAssocRing (Tot R P) := inferInstance


-- @@ L68-69 verbatim
/-- The inclusion of a homogeneous piece. -/
abbrev inc (k : ℕ) : Piece R P k →+ Tot R P := DirectSum.of (Piece R P) k


-- @@ L71-73 verbatim
@[simp] lemma inc_mul_inc {i j : ℕ} (a : Piece R P i) (b : Piece R P j) :
    (inc i a * inc j b : Tot R P) = inc (i + j) (star (R := R) a b) :=
  DirectSum.of_mul_of a b


-- @@ L75-79 verbatim
/-- Moving a homogeneous element between propositionally equal degrees. -/
lemma inc_reindex {m n : ℕ} (h : m = n) (x : Piece R P m) :
    (inc m x : Tot R P) = inc n (reindex R P (by rw [h]) x) := by
  subst h
  rw [reindex_self]


-- @@ L81-84 verbatim
/-! ### The pre-Lie identity on the total space

The associator is additive in each argument, so it is enough to check the identity on
homogeneous elements, where it is `star_assoc_symm`. -/


-- @@ L86-87 verbatim
lemma associator_zero_left (y z : Tot R P) : associator 0 y z = 0 := by
  simp only [← AddMonoidHom.associator_apply, map_zero, AddMonoidHom.zero_apply]


-- @@ L89-90 verbatim
lemma associator_zero_mid (x z : Tot R P) : associator x 0 z = 0 := by
  simp only [← AddMonoidHom.associator_apply, map_zero, AddMonoidHom.zero_apply]


-- @@ L92-93 verbatim
lemma associator_zero_right (x y : Tot R P) : associator x y 0 = 0 := by
  simp only [← AddMonoidHom.associator_apply, map_zero]


-- @@ L95-97 verbatim
lemma associator_add_left (x x' y z : Tot R P) :
    associator (x + x') y z = associator x y z + associator x' y z := by
  simp only [← AddMonoidHom.associator_apply, map_add, AddMonoidHom.add_apply]


-- @@ L99-101 verbatim
lemma associator_add_mid (x y y' z : Tot R P) :
    associator x (y + y') z = associator x y z + associator x y' z := by
  simp only [← AddMonoidHom.associator_apply, map_add, AddMonoidHom.add_apply]


-- @@ L103-105 verbatim
lemma associator_add_right (x y z z' : Tot R P) :
    associator x y (z + z') = associator x y z + associator x y z' := by
  simp only [← AddMonoidHom.associator_apply, map_add]


-- @@ L107-117 verbatim
/-- The pre-Lie identity on homogeneous elements: this is `star_assoc_symm`, with the three
degrees moved to the common index `i + j + k`. -/
lemma associator_inc (i j k : ℕ) (a : Piece R P i) (b : Piece R P j) (c : Piece R P k) :
    associator (inc i a : Tot R P) (inc j b) (inc k c)
      = associator (inc i a : Tot R P) (inc k c) (inc j b) := by
  simp only [associator, inc_mul_inc]
  rw [inc_reindex (show i + (j + k) = i + j + k by omega),
    inc_reindex (show i + k + j = i + j + k by omega),
    inc_reindex (show i + (k + j) = i + j + k by omega), ← map_sub, ← map_sub]
  congr 1
  exact star_assoc_symm a b c


-- @@ L119-134 verbatim
/-- **The associator of the total space is symmetric in its last two arguments.** -/
theorem tot_assoc_symm (x y z : Tot R P) : associator x y z = associator x z y := by
  induction x using DirectSum.induction_on with
  | zero => simp only [associator_zero_left]
  | add x₁ x₂ h₁ h₂ => simp only [associator_add_left, h₁, h₂]
  | of i a =>
    induction y using DirectSum.induction_on with
    | zero => simp only [associator_zero_mid, associator_zero_right]
    | add y₁ y₂ h₁ h₂ =>
      simp only [associator_add_mid, associator_add_right, h₁, h₂]
    | of j b =>
      induction z using DirectSum.induction_on with
      | zero => simp only [associator_zero_mid, associator_zero_right]
      | add z₁ z₂ h₁ h₂ =>
        simp only [associator_add_mid, associator_add_right, h₁, h₂]
      | of k c => exact associator_inc i j k a b c


-- @@ L136-139 verbatim
/-- **The total space of a non-symmetric operad is a right pre-Lie ring.** -/
instance : RightPreLieRing (Tot R P) where
  __ := (inferInstance : NonUnitalNonAssocRing (Tot R P))
  assoc_symm' := tot_assoc_symm


-- @@ L141-145 verbatim
/-! ### The commutator is a Lie bracket

Mathlib's pre-Lie file stops at the `Left`/`Right PreLieRing` classes and does not derive a Lie
structure, so the Jacobi identity is proved here. The cyclic sum of double commutators collapses
into six associators which cancel in pairs — each pair being one instance of `tot_assoc_symm`. -/


-- @@ L147-148 verbatim
/-- The commutator of the circle product. -/
def comm (x y : Tot R P) : Tot R P := x * y - y * x


-- @@ L150-150 verbatim
lemma comm_def (x y : Tot R P) : comm x y = x * y - y * x := rfl


-- @@ L152-152 verbatim
@[simp] lemma comm_self (x : Tot R P) : comm x x = 0 := sub_self _


-- @@ L154-155 verbatim
lemma comm_antisymm (x y : Tot R P) : comm x y = - comm y x := by
  simp only [comm_def, neg_sub]


-- @@ L157-164 verbatim
/-- The cyclic sum of double commutators, written out in associators. -/
private lemma jacobi_aux (x y z : Tot R P) :
    comm (comm x y) z + comm (comm y z) x + comm (comm z x) y
      = (associator x y z - associator x z y)
        + (associator y z x - associator y x z)
        + (associator z x y - associator z y x) := by
  simp only [comm_def, associator, sub_mul, mul_sub]
  abel


-- @@ L166-171 verbatim
/-- **The Jacobi identity.** The commutator of a right pre-Lie ring is a Lie bracket, so the
total space of an operad is a Lie ring under `⁅α, β⁆ = α ⋆ β - β ⋆ α`. -/
theorem jacobi (x y z : Tot R P) :
    comm (comm x y) z + comm (comm y z) x + comm (comm z x) y = 0 := by
  rw [jacobi_aux, tot_assoc_symm x y z, tot_assoc_symm y z x, tot_assoc_symm z x y]
  abel


-- @@ L173-174 verbatim
lemma comm_neg_right (x y : Tot R P) : comm x (-y) = - comm x y := by
  simp only [comm_def, mul_neg, neg_mul]; abel


-- @@ L176-177 verbatim
lemma comm_add_left (x x' y : Tot R P) : comm (x + x') y = comm x y + comm x' y := by
  simp only [comm_def, add_mul, mul_add]; abel


-- @@ L179-180 verbatim
lemma comm_add_right (x y y' : Tot R P) : comm x (y + y') = comm x y + comm x y' := by
  simp only [comm_def, add_mul, mul_add]; abel


-- @@ L182-183 verbatim
/-- The commutator, packaged as mathlib's bracket. -/
instance : Bracket (Tot R P) (Tot R P) := ⟨comm⟩


-- @@ L185-185 verbatim
lemma bracket_eq_comm (x y : Tot R P) : ⁅x, y⁆ = comm x y := rfl


-- @@ L187-202 verbatim
/-- **The total space is a Lie ring.** Mathlib states the Jacobi identity in Leibniz form; it
follows from the cyclic form together with antisymmetry. -/
instance : LieRing (Tot R P) where
  add_lie x y z := comm_add_left x y z
  lie_add x y z := comm_add_right x y z
  lie_self x := comm_self x
  leibniz_lie x y z := by
    show comm x (comm y z) = comm (comm x y) z + comm y (comm x z)
    have h := jacobi (R := R) (P := P) x y z
    have a1 : comm (comm y z) x = - comm x (comm y z) := comm_antisymm _ _
    have a2 : comm (comm z x) y = comm y (comm x z) := by
      rw [comm_antisymm (comm z x) y, comm_antisymm z x, comm_neg_right, neg_neg]
    have goal_eq : comm x (comm y z) - (comm (comm x y) z + comm y (comm x z))
        = -(comm (comm x y) z + comm (comm y z) x + comm (comm z x) y) := by
      rw [a1, a2]; abel
    rw [← sub_eq_zero, goal_eq, h, neg_zero]


-- @@ L204-208 verbatim
/-! ### `R`-bilinearity, and the Lie algebra structure

Mathlib's graded-ring machinery only knows that the multiplication on `⨁` is *additive* in each
slot. `⋆` is `R`-bilinear, and that upgrades the Lie ring to a Lie algebra, but it has to be
transported to the direct sum by hand. -/


-- @@ L210-212 verbatim
lemma smul_inc (t : R) {i : ℕ} (a : Piece R P i) :
    t • (inc i a : Tot R P) = inc i (t • a) :=
  (DirectSum.of_smul (R := R) i t a).symm


-- @@ L214-224 verbatim
lemma smul_mul_tot (t : R) (x y : Tot R P) : (t • x) * y = t • (x * y) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [smul_add, add_mul, h₁, h₂]
  | of i a =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => simp only [mul_add, smul_add, h₁, h₂]
    | of j b =>
      rw [smul_inc, inc_mul_inc, inc_mul_inc, smul_inc]
      exact congrArg _ (star_smul_left t a b)


-- @@ L226-236 verbatim
lemma mul_smul_tot (t : R) (x y : Tot R P) : x * (t • y) = t • (x * y) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [smul_add, add_mul, h₁, h₂]
  | of i a =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | add y₁ y₂ h₁ h₂ => simp only [mul_add, smul_add, h₁, h₂]
    | of j b =>
      rw [smul_inc, inc_mul_inc, inc_mul_inc, smul_inc]
      exact congrArg _ (star_smul_right t a b)


-- @@ L238-243 verbatim
/-- **The total space is a Lie algebra over `R`.** -/
instance : LieAlgebra R (Tot R P) where
  __ := (inferInstance : Module R (Tot R P))
  lie_smul t x y := by
    show comm x (t • y) = t • comm x y
    rw [comm_def, comm_def, mul_smul_tot, smul_mul_tot, smul_sub]


-- @@ L245-250 verbatim
/-! ### The Gerstenhaber bracket

Specialising to the endomorphism operad gives Gerstenhaber's construction *without its signs*:
the circle product on `⨁ n, End V (n+1)` is his `∘` with every sign set to `1`, and the
commutator is a Lie bracket. The two agree in characteristic `2`. Gerstenhaber's bracket itself
carries the suspension signs; it is `brT` on `TotS R (End R V)` (`Operad.TotalSpaceS`). -/


-- @@ L252-256 verbatim
/-- The unsigned Gerstenhaber Lie ring of a module: the total space of its endomorphism operad,
with the unsigned circle product. The signed bracket is `brT` on `TotS R (End R V)`. -/
abbrev Gerstenhaber (R : Type u) [CommRing R] (V : Type v) [AddCommGroup V] [Module R V] :
    Type v :=
  Tot R (End R V)


-- @@ L258-258 verbatim
example (V : Type v) [AddCommGroup V] [Module R V] : LieRing (Gerstenhaber R V) := inferInstance


-- @@ L260-261 verbatim
example (V : Type v) [AddCommGroup V] [Module R V] : LieAlgebra R (Gerstenhaber R V) :=
  inferInstance


-- @@ L263-263 verbatim
end


-- @@ L265-265 verbatim
end Operad
