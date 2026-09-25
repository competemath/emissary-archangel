import Mathlib.Tactic
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Algebra.Order.Module.Defs


-- @@ L6-6 verbatim
set_option doc.verso.suggestions false


-- @@ L8-26 verbatim
/-! A framework to formalize units (such as length, time, mass, velocity, etc.) in Lean.
-/

/- Dimensions of units are measured by an additive group `Dimensions`, which will typically be a
free module inan group on a finite number of generators, representing fundamental units such as length,
mass, and time.  We bundle this together in a class `UnitsSystem`.  To use this system, we create
an instance of it, allowing in particular the additive group `Dimensions` to be accessed freely
within the `UnitsSystem` namespace.

I am no longer actively maintaining this code, and others are welcome to incorporate it into their own units implementations.  Existing units implications in Lean include

- https://github.com/ATOMSLab/LeanDimensionalAnalysis/tree/main
- https://github.com/ecyrbe/lean-units
- https://github.com/HEPLean/PhysLean/tree/master/PhysLean/Units

and a general discussion of how to implement units can be found at

https://leanprover.zulipchat.com/#narrow/channel/479953-PhysLean/topic/physical.20units
-/


-- @@ L28-32 verbatim
class UnitsSystem where
  Dimensions: Type*
  addCommGroup: AddCommGroup Dimensions

/- The additive group structure of `Dimensions` needs to be explicitly registered as an instance. -/

-- @@ L33-33 verbatim
attribute [implicit_reducible, instance] UnitsSystem.addCommGroup


-- @@ L35-35 verbatim
namespace UnitsSystem


-- @@ L37-37 verbatim
variable [UnitsSystem]


-- @@ L39-49 verbatim
/-- The two key types here are {name}`Formal` and `Scalar d`.  `Scalar d` is the space of scalar
quantities whose units are given by `d : Dimensions`.  Collectively, they generate a graded commutative
 ring {name}`Formal`, which can be conveniently described using the existing Mathlib structure
 {name}`AddMonoidAlgebra`.  Algebraic manipulations of scalar quantities will be most conveniently
 handled by casting these quantities into the commutative ring {name}`Formal`, where one can use
 standard Mathlib tactics such as {name (full := Mathlib.Tactic.RingNF.ring)}`ring`.

In principle one could also develop vector-valued quantities with dimension, but for now we
restrict attention to scalar quantities only.
-/
abbrev Formal := AddMonoidAlgebra ℝ Dimensions


-- @@ L51-55 verbatim
/-- The data {name}`Scalar.val` of a {name}`Scalar` quantity can be interpreted as the numerical value of that
quantity with respect to some standard set of units (e.g., SI units). -/
@[ext]
structure Scalar (d:Dimensions) where
  val : ℝ


-- @@ L57-62 verbatim
theorem Scalar.val_injective (d : Dimensions) : Function.Injective (Scalar.val (d := d)) :=
  fun x y h => by aesop

/- One has the option to `work in coordinates` in a given calculation by using `simp [←val_inj]` (or `simp [←cast_eq]` below, if casting is required).  Or one can adopt
a `coordinate-free` approach in which any tool directly accessing `val` is avoided.
This library allows for both approaches to be employed. -/

-- @@ L63-64 verbatim
theorem Scalar.val_inj {d:Dimensions} (q₁ q₂:Scalar d) :
  q₁.val = q₂.val ↔ q₁ = q₂ := Scalar.val_injective _ |>.eq_iff



-- @@ L67-76 verbatim
/-- {given -show}`d, d', d₁, d₂` We will encounter a technical issue with Lean's type system, namely that the type {lean}`Scalar d`
and {lean}`Scalar d'` are not identical if {name}`d'` and {name}`d` are merely propositionally equal (as opposed
to definitionally equal); for instance, {lean}`Scalar (d₁+d₂)` and {lean}`Scalar (d₂+d₁)` are distinct types.
Technically, this renders multiplication on scalar types noncommutative. To get around this, we
create a casting operator, where the propositional equality is attempted to be resolved by the Lean
tactic {tactic}`module` whenever possible.  Unfortunately, the casting operator from {lean}`Scalar d` to {lean}`Scalar d'`
cannot be captured by standard Lean coercion classes such as {name}`Coe` or {name}`CoeOut` as each of the types
here contain parameters not present in the other. -/
def Scalar.cast {d d':Dimensions}  (q: Scalar d) (_ : d' = d := by module) : Scalar d' :=
  ⟨q.val⟩


-- @@ L78-80 verbatim
/-- This is a variant of {name}`Scalar.val_inj` that handles casts. -/
theorem Scalar.cast_eq {d d':Dimensions} (q: Scalar d) (q': Scalar d') (h: d = d' := by module)
  : q.val = q'.val ↔ q = q'.cast h := by aesop


-- @@ L82-83 verbatim
theorem Scalar.cast_eq_symm {d d':Dimensions} (q: Scalar d) (q': Scalar d') (h: d = d' := by module)
  : q = q'.cast h ↔ q' = q.cast h.symm := by aesop


-- @@ L85-87 verbatim
@[simp]
theorem Scalar.cast_val {d d':Dimensions} (q: Scalar d) (h: d' = d := by module)
  : (q.cast h).val = q.val := by aesop


-- @@ L89-93 verbatim
/-- The existing Mathlib method {name}`AddMonoidAlgebra.single` is perfect for embedding each type of
{name}`Scalar` into the formal graded ring {name}`Formal`. -/
@[coe]
noncomputable def Scalar.toFormal {d:Dimensions} (q:Scalar d) : Formal :=
  AddMonoidAlgebra.single d q.val


-- @@ L95-96 verbatim
noncomputable instance Scalar.instCoeFormal (d: Dimensions) : CoeOut (Scalar d) Formal where
  coe := toFormal


-- @@ L98-110 verbatim
/-- Many identities involving several types of {name}`Scalar`s can be dealt with by applying
{syntax tactic}`simp [←toFormal_inj]` to move everything to {name}`Formal`.  A large number of further {tactic}`simp` lemmas
in this file are then designed to simplify such {name}`Formal` expressions, often by pushing casting
operators inward back to the {name}`Scalar` types.  As such, there will be significant overlap between
the {tactic}`simp` and {tactic}`norm_cast` tags. -/
@[simp]
theorem Scalar.toFormal_inj {d: Dimensions} (q₁ q₂:Scalar d) :
  (q₁:Formal) = (q₂:Formal) ↔ q₁ = q₂ := by
  constructor
  . simp [toFormal, ←val_inj]; intro h
    replace h := congr($h d)
    simpa using h
  intro h; simp [h]


-- @@ L112-118 verbatim
/-- Conveniently, casts from one scalar to another will automatically disappear when moving to
{name}`Formal`. -/
@[simp]
theorem Scalar.toFormal_cast {d d': Dimensions} (q:Scalar d) (h:d' = d := by module) :
  ((q.cast h):Formal) = (q:Formal) := by
  subst h
  simp_all only [cast]


-- @@ L120-121 verbatim
instance Scalar.instZero {d:Dimensions} : Zero (Scalar d) where
  zero := ⟨ 0 ⟩


-- @@ L123-124 verbatim
@[simp]
theorem Scalar.val_zero {d:Dimensions} : (0:Scalar d).val = 0 := rfl


-- @@ L126-129 verbatim
/-- We will use the {name}`NeZero` class to tag some scalars as non-zero; this becomes relevant when
using such scalars as units.  One could also introduce API to tag some scalars as positive, but
we currently are not implementing this. -/
theorem Scalar.neZero_iff {d:Dimensions} (q:Scalar d) : NeZero q ↔ q.val ≠ 0 := by simp [_root_.neZero_iff, ←val_inj]


-- @@ L131-134 verbatim
@[simp, norm_cast]
theorem Scalar.toFormal_zero {d:Dimensions} : ((0:Scalar d):Formal) = 0 := by
  simp only [toFormal, AddMonoidAlgebra.single, val_zero, Finsupp.single_zero]
  rfl


-- @@ L136-139 verbatim
/-- In the next few lines of code we give {lean}`Scalar d` the structure of a real vector space,
which is of course compatible with the real vector space structure on {name}`Formal`.  -/
instance Scalar.instAdd {d:Dimensions} : Add (Scalar d) where
  add q₁ q₂ := ⟨q₁.val + q₂.val⟩


-- @@ L141-142 verbatim
@[simp]
theorem Scalar.val_add {d:Dimensions} (q₁ q₂:Scalar d) : (q₁ + q₂).val = q₁.val + q₂.val := rfl


-- @@ L144-148 verbatim
/-- Note how the {tactic}`simp` lemma is in the direction of pushing coercions inward. -/
@[simp,norm_cast]
theorem Scalar.toFormal_add {d:Dimensions} (q₁ q₂:Scalar d) : ((q₁ + q₂:Scalar d):Formal) = (q₁:Formal) + (q₂:Formal) := by
  simp only [toFormal, val_add, Finsupp.single_add]
  rfl


-- @@ L150-151 verbatim
instance Scalar.instNeg {d:Dimensions} : Neg (Scalar d) where
  neg q := ⟨-q.val⟩


-- @@ L153-154 verbatim
@[simp]
theorem Scalar.val_neg {d:Dimensions} (q:Scalar d) : (-q).val = -q.val := rfl


-- @@ L156-158 verbatim
instance Scalar.instNeZero_neg {d:Dimensions} (q:Scalar d) [h:NeZero q] : NeZero (-q) := by
  rw [neZero_iff] at h ⊢
  simp [h]


-- @@ L160-162 verbatim
@[simp,norm_cast]
theorem Scalar.toFormal_neg {d:Dimensions} (q:Scalar d) : ((-q:Scalar d):Formal) = -(q:Formal) := by
  simp only [toFormal, val_neg, Finsupp.single_neg]; rfl


-- @@ L164-165 verbatim
instance Scalar.instSub {d:Dimensions} : Sub (Scalar d) where
  sub q₁ q₂ := ⟨q₁.val - q₂.val⟩


-- @@ L167-168 verbatim
@[simp]
theorem Scalar.val_sub {d:Dimensions} (q₁ q₂ : Scalar d) : (q₁ - q₂).val = q₁.val - q₂.val := rfl


-- @@ L170-172 verbatim
@[simp,norm_cast]
theorem Scalar.toFormal_sub {d:Dimensions} (q₁ q₂ :Scalar d) : ((q₁ - q₂ :Scalar d):Formal) = (q₁:Formal) - q₂ := by
  simp only [toFormal, val_sub, Finsupp.single_sub]; rfl


-- @@ L174-175 verbatim
instance Scalar.instSMul {α} {d:Dimensions} [SMul α ℝ] : SMul α (Scalar d) where
  smul c q := ⟨c • q.val⟩


-- @@ L177-178 verbatim
@[simp]
theorem Scalar.val_smul {α} {d:Dimensions} [SMul α ℝ] (a : α) (q:Scalar d) : (a • q).val = a • q.val := rfl


-- @@ L180-181 verbatim
instance Scalar.instAddGroup {d:Dimensions} : AddGroup (Scalar d) :=
  val_injective _ |>.addGroup _ val_zero val_add val_neg val_sub (Function.swap val_smul) (Function.swap val_smul)


-- @@ L183-184 verbatim
instance Scalar.instAddCommGroup {d:Dimensions} : AddCommGroup (Scalar d) :=
  val_injective _ |>.addCommGroup _ val_zero val_add val_neg val_sub (Function.swap val_smul) (Function.swap val_smul)


-- @@ L186-188 verbatim
/-- The dimensionless scalars {lean}`Scalar 0` can be identified with real numbers.  -/
@[coe]
def Scalar.ofReal (r:ℝ) : Scalar 0 := ⟨ r ⟩


-- @@ L190-191 verbatim
instance Scalar.instCoeReal : Coe ℝ (Scalar 0) where
  coe := ofReal


-- @@ L193-194 verbatim
@[simp]
theorem Scalar.coe_val (r:ℝ) : (r:Scalar 0).val = r := rfl


-- @@ L196-197 verbatim
@[norm_cast,simp]
theorem Scalar.coe_zero : ((0:ℝ):Scalar 0) = 0 := rfl


-- @@ L199-200 verbatim
theorem Scalar.neZero_coe_iff {r:ℝ} : NeZero (r:Scalar 0) ↔ r ≠ 0 := by
  simp [neZero_iff]


-- @@ L202-204 verbatim
@[simp]
theorem Scalar.coe_inj {r s:ℝ} : (r:Scalar 0) = (s:Scalar 0) ↔ r = s := by
  simp [ofReal]


-- @@ L206-207 verbatim
@[norm_cast,simp]
theorem Scalar.coe_add (r s:ℝ) : ((r+s:ℝ):Scalar 0) = (r:Scalar 0) + (s:Scalar 0) := rfl


-- @@ L209-210 verbatim
@[norm_cast,simp]
theorem Scalar.coe_neg (r:ℝ) : ((-r:ℝ):Scalar 0) = -(r:Scalar 0) := rfl


-- @@ L212-214 verbatim
@[norm_cast,simp]
theorem Scalar.coe_sub (r s:ℝ) : ((r-s:ℝ):Scalar 0) = (r:Scalar 0) - (s:Scalar 0) := by
  simp [ofReal]; rfl


-- @@ L216-219 verbatim
/-- It is convenient to view the real numbers as a subring of the {name}`Formal` ring, thus identifying
{name}`Scalar` multiplication with ordinary multiplication. -/
noncomputable instance Formal.instCoeReal : Coe ℝ Formal where
  coe r := ((r:Scalar 0):Formal)


-- @@ L221-223 verbatim
@[norm_cast,simp]
theorem Formal.coe_zero : ((0:ℝ):Formal) = 0 := by
  simp


-- @@ L225-227 verbatim
@[norm_cast,simp]
theorem Formal.coe_one : ((1:ℝ):Formal) = 1 := by
  rfl


-- @@ L229-231 verbatim
@[norm_cast,simp]
theorem Formal.coe_nat (n:ℕ) : ((n:ℝ):Formal) = (n:Formal) := by
  rfl


-- @@ L233-235 verbatim
@[norm_cast,simp]
theorem Formal.coe_int (n:ℤ) : ((n:ℝ):Formal) = (n:Formal) := by
  rfl


-- @@ L237-240 verbatim
@[norm_cast,simp]
theorem Scalar.toFormal_smul {d:Dimensions} (c:ℝ) (q:Scalar d)
  : ((c • q:Scalar d):Formal) = (c:Formal) * (q:Formal) := by
  simp [toFormal, AddMonoidAlgebra.single_mul_single]



-- @@ L243-246 verbatim
@[simp]
theorem Formal.smul_eq_mul (c:ℝ) (x:Formal) : c • x = (c:Formal) * x := by
  ext n
  simp [Scalar.toFormal]


-- @@ L248-250 verbatim
@[simp]
theorem Formal.smul_eq_mul' (c:ℕ) (x:Formal) : c • x = (c:Formal) * x := by
  simp


-- @@ L252-254 verbatim
@[simp]
theorem Formal.smul_eq_mul'' (c:ℤ) (x:Formal) : c • x = (c:Formal) * x := by
  exact zsmul_eq_mul x c


-- @@ L256-258 verbatim
@[norm_cast,simp]
theorem Scalar.coe_mul (r s:ℝ) : ((r*s:ℝ):Scalar 0) = r • (s:Scalar 0) := by
  ext; simp [ofReal]


-- @@ L260-267 verbatim
/-- We are finally able to view {lean}`Scalar d` as a vector space over {lean}`ℝ` as promised. -/
instance Scalar.instModule {d:Dimensions} : Module ℝ (Scalar d) where
  smul_add c q₁ q₂ := by simp [←toFormal_inj]; ring
  add_smul c1 c2 q := by simp [←toFormal_inj]; ring
  one_smul q := by simp [←toFormal_inj]
  zero_smul q := by simp [←toFormal_inj]
  mul_smul c1 c2 q := by simp [←toFormal_inj]; ring
  smul_zero c := by simp [←toFormal_inj]


-- @@ L269-270 verbatim
@[simp]
theorem Scalar.val_smul' {d:Dimensions} (c:ℕ) (q:Scalar d) : (c • q).val = c * q.val := by simp [←Nat.cast_smul_eq_nsmul ℝ]


-- @@ L272-273 verbatim
@[simp]
theorem Scalar.val_smul'' {d:Dimensions} (c:ℤ) (q:Scalar d) : (c • q).val = c * q.val := by simp [←Int.cast_smul_eq_zsmul ℝ]


-- @@ L275-278 verbatim
@[norm_cast,simp]
theorem Scalar.toFormal_smul' {d:Dimensions} (c:ℕ) (q:Scalar d)
  : ((c • q:Scalar d):Formal) = (c:Formal) * (q:Formal) := by
  simp [←Nat.cast_smul_eq_nsmul ℝ]


-- @@ L280-283 verbatim
@[norm_cast,simp]
theorem Scalar.toFormal_smul'' {d:Dimensions} (c:ℤ) (q:Scalar d)
  : ((c • q:Scalar d):Formal) = (c:Formal) * (q:Formal) := by
  simp [←Int.cast_smul_eq_zsmul ℝ]


-- @@ L285-288 verbatim
/-- One can multiply a {lean}`Scalar d₁` and {lean}`Scalar d₂` quantities to obtain a {lean}`Scalar (d₁+d₂)` quantity,
in a manner compatible with multiplication in {name}`Formal`. -/
instance Scalar.instHMul {d₁ d₂:Dimensions} : HMul (Scalar d₁) (Scalar d₂) (Scalar (d₁ + d₂)) where
  hMul q₁ q₂ := ⟨q₁.val * q₂.val⟩


-- @@ L290-292 verbatim
@[simp]
theorem Scalar.val_hMul {d₁ d₂:Dimensions} (q₁:Scalar d₁) (q₂:Scalar d₂) :
  (q₁ * q₂).val = q₁.val * q₂.val := rfl


-- @@ L294-297 verbatim
@[norm_cast,simp]
theorem Scalar.toFormal_hMul {d₁ d₂:Dimensions} (q₁:Scalar d₁) (q₂:Scalar d₂) :
  ((q₁ * q₂:Scalar _):Formal) = (q₁:Formal) * (q₂:Formal) := by
  simp [toFormal, AddMonoidAlgebra.single_mul_single]


-- @@ L299-301 verbatim
/-- Similarly, one can raise a {lean}`Scalar d` quantity to a natural number power {name}`n` to obtain a {lean}`Scalar (n • d)` quantity.  One could also implement exponentiation to an integer, but I have elected
not to do this, implementing an inversion relation instead. -/
noncomputable def Scalar.pow {d:Dimensions} (q: Scalar d) (n:ℕ) : Scalar (n • d) := ⟨ q.val^n ⟩


-- @@ L303-304 verbatim
/-- {given -show}`n : ℕ, d` One cannot use the Mathlib classes {name}`Pow` or {name}`HPow` here because the output type {lean}`Scalar (n • d)` depends on the input {name}`n`.  As the symbol {kw (of := «term_^_»)}`^` is reserved for such classes, we use the symbol `**` instead. -/
infix:80 "**" => Scalar.pow


-- @@ L306-308 expanded
@[simp]
theorem Scalar.val_pow {d : Dimensions} (q : Scalar d) (n : ℕ) : (Scalar.pow q n).val = q.val ^ n :=
  rfl


-- @@ L310-313 expanded
@[norm_cast, simp]
theorem Scalar.toFormal_pow {d : Dimensions} (q : Scalar d) (n : ℕ) :
    ((Scalar.pow q n) : Formal) = (q : Formal) ^ n := by
  simp [toFormal, AddMonoidAlgebra.single_pow]


-- @@ L315-316 verbatim
/-- We cannot use Mathlib's {name}`Inv` class here or the associated {kw (of := «term_⁻¹»)}`⁻¹` notation because {name}`Inv` requires the output to be of the same type as the input. -/
noncomputable def Scalar.inv {d:Dimensions} (q:Scalar d) : Scalar (-d) := ⟨ q.val⁻¹ ⟩


-- @@ L318-320 verbatim
@[simp]
theorem Scalar.val_inv {d:Dimensions} (q:Scalar d) :
  q.inv.val = q.val⁻¹ := rfl


-- @@ L322-324 verbatim
instance Scalar.instNeg_inv {d:Dimensions} (q:Scalar d) [h: NeZero q] : NeZero q.inv := by
  rw [neZero_iff] at h ⊢
  simp [h]


-- @@ L326-331 verbatim
@[simp]
theorem Scalar.mul_inv_self {d:Dimensions} (q:Scalar d) [h:NeZero q] : (q:Formal) * (q.inv:Formal) = 1 := by
  obtain ⟨ v ⟩ := q
  simp [neZero_iff] at h
  simp [inv, toFormal, AddMonoidAlgebra.single_mul_single,← Formal.coe_one]
  congr; field_simp


-- @@ L333-335 verbatim
@[simp]
theorem Scalar.inv_mul_self {d:Dimensions} (q:Scalar d) [h:NeZero q] :  (q.inv:Formal) * (q:Formal) = 1 := by
  rw [mul_comm, mul_inv_self]


-- @@ L337-339 verbatim
@[simp]
theorem Scalar.inv_coe (r:ℝ) :  ((r:Scalar 0).inv:Formal) = ((r⁻¹:ℝ):Scalar 0) := by
  rw [←toFormal_cast _ (show 0 = -0 by module)]; congr


-- @@ L341-343 verbatim
@[simp]
theorem Scalar.mul_inv {d₁ d₂:Dimensions} (q₁:Scalar d₁) (q₂:Scalar d₂) : (q₁ * q₂).inv = ((q₁.inv) * (q₂.inv)).cast := by
  simp [←toFormal_inj, toFormal]; congr 1; ring


-- @@ L345-347 expanded
@[simp]
theorem Scalar.pow_inv {d : Dimensions} (q : Scalar d) (n : ℕ) :
    (Scalar.pow q n).inv = (Scalar.pow q.inv n).cast := by simp [← toFormal_inj, toFormal]


-- @@ L349-351 verbatim
/-- Multiplication and inversion combine to give division in the usual fashion. -/
noncomputable instance Scalar.instHDiv {d₁ d₂:Dimensions} : HDiv (Scalar d₁) (Scalar d₂) (Scalar (d₁ - d₂)) where
  hDiv q₁ q₂ := ⟨q₁.val / q₂.val⟩


-- @@ L353-355 verbatim
@[simp]
theorem Scalar.val_hDiv {d₁ d₂:Dimensions} (q₁:Scalar d₁) (q₂:Scalar d₂) :
  (q₁ / q₂).val = q₁.val / q₂.val := rfl


-- @@ L357-361 verbatim
@[norm_cast,simp]
theorem Scalar.toFormal_hDiv {d₁ d₂:Dimensions} (q₁:Scalar d₁) (q₂:Scalar d₂) :
  ((q₁ / q₂:Scalar _):Formal) = (q₁:Formal) * (q₂.inv:Formal) := by
  simp [toFormal, AddMonoidAlgebra.single_mul_single]
  congr; module


-- @@ L363-364 verbatim
noncomputable instance Scalar.instHDiv' {d:Dimensions} : HDiv (Scalar d) ℝ  (Scalar d) where
  hDiv q r := ⟨q.val / r⟩


-- @@ L366-367 verbatim
noncomputable instance Scalar.instHDiv'' {d:Dimensions} : HDiv (Scalar d) ℕ (Scalar d) where
  hDiv q n := q / (n:ℝ)


-- @@ L369-370 verbatim
noncomputable instance Scalar.instHDiv''' {d:Dimensions} : HDiv (Scalar d) ℤ (Scalar d) where
  hDiv q n := q / (n:ℝ)


-- @@ L372-374 verbatim
@[simp]
theorem Scalar.val_hDiv' {d:Dimensions} (q:Scalar d) (r:ℝ) :
  (q / r).val = q.val / r := rfl


-- @@ L376-378 verbatim
@[simp]
theorem Scalar.val_hDiv'' {d:Dimensions} (q:Scalar d) (n:ℕ) :
  (q / n).val = q.val / n := rfl


-- @@ L380-382 verbatim
@[simp]
theorem Scalar.val_hDiv''' {d:Dimensions} (q:Scalar d) (n:ℤ) :
  (q / n).val = q.val / n := rfl



-- @@ L385-389 verbatim
@[norm_cast,simp]
theorem Scalar.toFormal_hDiv' {d:Dimensions} (q:Scalar d) (r:ℝ) :
  ((q / r:Scalar _):Formal) = (q:Formal) * ((r⁻¹:ℝ):Formal) := by
  simp [toFormal, AddMonoidAlgebra.single_mul_single]
  congr


-- @@ L391-393 verbatim
@[norm_cast,simp]
theorem Scalar.toFormal_hDiv'' {d:Dimensions} (q:Scalar d) (n:ℕ) :
  ((q / n:Scalar _):Formal) = (q:Formal) * (((n:ℝ)⁻¹:ℝ):Formal) := toFormal_hDiv' _ _


-- @@ L395-397 verbatim
@[norm_cast,simp]
theorem Scalar.toFormal_hDiv''' {d:Dimensions} (q:Scalar d) (n:ℤ) :
  ((q / n:Scalar _):Formal) = (q:Formal) * (((n:ℝ)⁻¹:ℝ):Formal) := toFormal_hDiv' _ _



-- @@ L400-401 verbatim
instance Scalar.instLE (d:Dimensions) : LE (Scalar d) where
  le x y := x.val ≤ y.val


-- @@ L403-404 verbatim
theorem Scalar.val_le {d:Dimensions} (x y:Scalar d) :
  x ≤ y ↔ x.val ≤ y.val := by rfl


-- @@ L406-412 verbatim
noncomputable instance Scalar.instLinearOrder (d:Dimensions) : LinearOrder (Scalar d) where
  le_refl := by simp [val_le]
  le_trans := by simp [val_le]; intros; order
  lt_iff_le_not_ge := by simp [val_le]
  le_antisymm := by simp [val_le, ←val_inj]; intros; order
  le_total := by simp [val_le]; intros; apply LinearOrder.le_total
  toDecidableLE := Classical.decRel _


-- @@ L414-415 verbatim
theorem Scalar.val_lt {d:Dimensions} (x y:Scalar d) :
  x < y ↔ x.val < y.val := by simp only [lt_iff_not_ge, val_le]


-- @@ L417-419 verbatim
noncomputable instance Scalar.instPosSMulStrictMono (d:Dimensions) : PosSMulStrictMono ℝ (Scalar d) where
  smul_lt_smul_of_pos_left {_a} ha {_b₁ _b₂} hb := by
    simp only [val_lt, val_smul, smul_eq_mul] at *; exact mul_lt_mul_of_pos_left hb ha


-- @@ L421-423 verbatim
noncomputable instance Scalar.instSMulPosStrictMono (d:Dimensions) : SMulPosStrictMono ℝ (Scalar d) where
  smul_lt_smul_of_pos_right {_b} hb {_a₁ _a₂} ha := by
    simp only [val_lt, val_smul, smul_eq_mul] at *; exact mul_lt_mul_of_pos_right ha hb


-- @@ L425-427 verbatim
noncomputable instance Scalar.instIsStrictOrderedModule (d:Dimensions) : IsStrictOrderedModule ℝ (Scalar d) where

-- TODO: add in some `gcongr` lemmas for this order


-- @@ L429-430 verbatim
/-- The standard unit of {lean}`Scalar d` is the quantity whose data {name}`Scalar.val` is equal to {lean (type := "ℝ")}`1`. -/
def StandardUnit (d:Dimensions) : Scalar d := ⟨ 1 ⟩


-- @@ L432-433 verbatim
@[simp]
theorem StandardUnit.val_eq (d:Dimensions) : (StandardUnit d).val = 1 := rfl


-- @@ L435-436 verbatim
instance StandardUnit.inst_NeZero (d:Dimensions) : NeZero (StandardUnit d) := by
  simp [Scalar.neZero_iff]


-- @@ L438-440 verbatim
@[simp]
theorem StandardUnit.mul (d₁ d₂:Dimensions) : StandardUnit d₁ * StandardUnit d₂ = StandardUnit (d₁+d₂) := by
  simp [←Scalar.val_inj]


-- @@ L442-444 verbatim
@[simp]
theorem StandardUnit.mul' (d₁ d₂:Dimensions) : (StandardUnit d₁:Formal) * (StandardUnit d₂:Formal) = StandardUnit (d₁+d₂) := by
  rw [←Scalar.toFormal_hMul, mul]


-- @@ L446-448 expanded
@[simp]
theorem StandardUnit.pow (d : Dimensions) (n : ℕ) :
    Scalar.pow (StandardUnit d) n = StandardUnit (n • d) := by simp [← Scalar.val_inj]


-- @@ L450-452 verbatim
@[simp]
theorem StandardUnit.pow' (d:Dimensions) (n:ℕ) : (StandardUnit d:Formal)^n = StandardUnit (n • d) := by
  rw [←Scalar.toFormal_pow, pow]


-- @@ L454-456 verbatim
@[simp]
theorem StandardUnit.inv (d:Dimensions) : (StandardUnit d).inv = StandardUnit (-d) := by
  simp [←Scalar.val_inj]


-- @@ L458-460 verbatim
@[simp]
theorem StandardUnit.div (d₁ d₂:Dimensions) : StandardUnit d₁ / StandardUnit d₂ = StandardUnit (d₁-d₂) := by
  simp [←Scalar.val_inj]


-- @@ L462-463 verbatim
/-- {lean}`unit.in q` is {lean}`q : Scalar d` measured in terms of {lean}`unit : Scalar d`. -/
noncomputable def Scalar.in {d:Dimensions} (unit q:Scalar d) : ℝ := q.val / unit.val


-- @@ L465-466 verbatim
@[simp]
theorem Scalar.val_in (d:Dimensions) (unit q:Scalar d) : unit.in q = q.val / unit.val := rfl


-- @@ L468-471 verbatim
theorem Scalar.in_def {d:Dimensions} (unit q:Scalar d) [h: NeZero unit] : q = (unit.in q) • unit := by
  simp [neZero_iff] at h
  simp [←val_inj]
  field_simp


-- @@ L473-475 verbatim
@[simp]
theorem Scalar.in_smul {d:Dimensions} (c:ℝ) (unit q:Scalar d) : unit.in (c • q) = c * unit.in q := by
  simp; ring


-- @@ L477-480 verbatim
theorem Scalar.in_inj {d:Dimensions} (unit q₁ q₂:Scalar d) [h: NeZero unit] : unit.in q₁ = unit.in q₂ ↔ q₁ = q₂ := by
  simp [neZero_iff] at h
  simp [←val_inj]
  field_simp










-- @@ L490-490 verbatim
end UnitsSystem
