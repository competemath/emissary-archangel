import Prismriver.Repr.Scale
import Prismriver.Repr.Time

import Lean.ToExpr


-- @@ L6-6 verbatim
namespace Prismriver


-- @@ L8-11 verbatim
structure Note (P D : Type) where
  pitch : P
  duration : D
  deriving BEq, Ord


-- @@ L13-13 verbatim
instance [Ord P] [Ord D] : LT (Note P D) := ltOfOrd

-- @@ L14-14 verbatim
instance [Ord P] [Ord D] : LE (Note P D) := leOfOrd


-- @@ L16-17 verbatim
instance [Repr P] [Repr D] : Repr (Note P D) where
  reprPrec n p := f!"{reprPrec n.pitch p}[{reprPrec n.duration p}]"

-- @@ L18-19 verbatim
instance [ToString P] [ToString D] : ToString (Note P D) where
  toString n := s!"{n.pitch}[{n.duration}]"


-- @@ L21-27 verbatim
open Lean in
instance [ToExpr P] [ToExpr D] : ToExpr (Note P D) where
  toExpr n :=
    let pitch := toExpr n.pitch
    let duration := toExpr n.duration
    mkAppN (mkConst ``Note.mk) #[pitch, duration]
  toTypeExpr : Expr := mkConst ``Note
