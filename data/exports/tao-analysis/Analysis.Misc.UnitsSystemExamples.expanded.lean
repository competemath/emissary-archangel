import Mathlib.Tactic
import Analysis.Misc.UnitsSystem


-- @@ L4-4 verbatim
open UnitsSystem

-- @@ L5-5 verbatim
variable [UnitsSystem]


-- @@ L7-10 verbatim
/-! Many algebraic identities involving {name}`Scalar` can be established by first using {syntax tactic}`simp [←toFormal_inj]`  to coerce to {name}`Formal` and  push coercions inside, then appealing to {tactic}`ring`.  We give some examples below.

Alternatively, one can "work in coordinates" by using {syntax tactic}`simp [←val_inj]` in place of {syntax tactic}`simp [←toFormal_inj]`.
-/


-- @@ L12-16 verbatim
/-- {given -show (type := "Dimensions")}`d₁, d₂, d₃` A {name}`Scalar.cast` is needed here because
  {lean}`(d₁+d₂)+d₃` is not definitionally equal to {lean}`d₁+(d₂+d₃)`. -/
theorem UnitsSystem.Scalar.hMul_assoc {d₁ d₂ d₃:Dimensions} (a:Scalar d₁) (b:Scalar d₂) (c:Scalar d₃):
  a * (b * c) = ((a * b) * c).cast := by
  simp [←toFormal_inj]; ring


-- @@ L18-20 verbatim
theorem UnitsSystem.Scalar.left_distrib {d₁ d₂:Dimensions} (a:Scalar d₁) (b c:Scalar d₂) :
  a * (b + c) = (a * b) + (a * c) := by
  simp [←toFormal_inj]; ring


-- @@ L22-24 verbatim
theorem UnitsSystem.Scalar.right_distrib {d₁ d₂:Dimensions} (a b:Scalar d₁) (c:Scalar d₂) :
  (a + b) * c = (a * c) + (b * c) := by
  simp [←toFormal_inj]; ring


-- @@ L26-28 expanded
/--
A {name}`Scalar.cast` is needed here because {lean}`2 • d` is not definitionally equal to {lean}`d+d`. -/
theorem UnitsSystem.Scalar.sq_add {d : Dimensions} (a b : Scalar d) :
    Scalar.pow (a + b) 2 = Scalar.pow a 2 + (2 • a * b).cast + Scalar.pow b 2 := by
  simp [← toFormal_inj]; ring


-- @@ L30-32 expanded
/-- An alternate proof based on working in coordinates -/
theorem UnitsSystem.Scalar.sq_add' {d : Dimensions} (a b : Scalar d) :
    Scalar.pow (a + b) 2 = Scalar.pow a 2 + (2 • a * b).cast + Scalar.pow b 2 := by
  simp [← val_inj]; ring

