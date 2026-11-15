namespace Tengoku.Flt end Tengoku.Flt open Tengoku.Flt 
namespace Tengoku.Flt.FreyPackage

/-- The Weierstrass curve over `ℤ` associated to a Frey package. The conditions imposed
upon a Frey package guarantee that the running hypotheses in
Section 4.1 of [Serre] all hold. We put the curve into the form where the
equation is semistable at 2, rather than the usual `Y^2=X(X-a^p)(X+b^p)` form.
The change of variables is `X=4x` and `Y=8y+4x`, and then divide through by 64.
The fact that p is odd, a=3 mod 4 and b is even are enough to show that
this new curve still has coefficients in `ℤ`.
-/
def freyCurveInt (P : FreyPackage) : WeierstrassCurve ℤ where
  a₁ := 1
