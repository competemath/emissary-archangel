import Std.Data.TreeMap
import Lean.ToExpr


-- @@ L4-4 verbatim
namespace Prismriver


-- @@ L6-10 verbatim
class Time (T : Type) extends Add T, Sub T, Neg T, SMul Int T, Ord T, Inhabited T, Repr T where
  zero : T
  /- Maximum time within a bar -/
  bar : T := zero
  default := zero


-- @@ L12-12 verbatim
section


-- @@ L14-14 verbatim
variable { T } [Time T]

-- @@ L15-15 verbatim
instance : LT T := ltOfOrd

-- @@ L16-16 verbatim
instance : LE T := leOfOrd

-- @@ L17-17 verbatim
instance : Min T := minOfLe

-- @@ L18-18 verbatim
instance : Max T := maxOfLe


-- @@ L20-23 verbatim
structure TimeSpan [Time T] where
  start : T
  duration : T
  deriving Ord, BEq, DecidableEq


-- @@ L25-25 verbatim
protected def TimeSpan.stop [Time T] (s : @TimeSpan T _) : T := s.start + s.duration


-- @@ L27-28 verbatim
instance : HAdd (@TimeSpan T _) T (@TimeSpan T _) where
  hAdd span t := { start := span.start + t, duration := span.duration }


-- @@ L30-31 verbatim
instance : Repr (@TimeSpan T _) where
  reprPrec t _ := f!"{reprPrec t.start 0}+{reprPrec t.duration 0}"


-- @@ L33-33 verbatim
end


-- @@ L35-36 verbatim
instance : Time Int where
  zero := 0


-- @@ L38-45 verbatim
instance : Ord Rat where
  compare r1 r2 :=
    if r1 = r2 then
      .eq
    else if r1 < r2 then
      .lt
    else
      .gt


-- @@ L47-49 verbatim
instance : Time Rat where
  zero := 0
  bar := 1


-- @@ L51-57 verbatim
open Lean in
instance : ToExpr Rat where
  toExpr t :=
    let num := toExpr t.num
    let den := toExpr (t.den : Int)
    mkAppN (mkConst ``Rat.divInt) #[num, den]
  toTypeExpr : Expr := mkConst ``Rat


-- @@ L59-62 verbatim
structure MeasuredTime where
  bars : Int := 0
  offset : Rat := 0
  deriving Ord, BEq, DecidableEq

-- @@ L63-63 verbatim
instance : LT MeasuredTime := ltOfOrd

-- @@ L64-64 verbatim
instance : LE MeasuredTime := leOfOrd

-- @@ L65-65 verbatim
instance : Min MeasuredTime := minOfLe

-- @@ L66-68 verbatim
instance : Max MeasuredTime := maxOfLe

-- Check lexicographical ordering

-- @@ L69-69 verbatim
example : (⟨1, 2⟩ : MeasuredTime) < (⟨2, 1⟩ : MeasuredTime) := by decide


-- @@ L71-72 verbatim
/-- one bar -/
protected def MeasuredTime.bar : MeasuredTime := ⟨1, 0⟩


-- @@ L74-75 verbatim
instance : Coe Rat MeasuredTime where
  coe offset := ⟨0, offset⟩


-- @@ L77-78 verbatim
/-- Rational time -/
def rt (n d : Nat) : MeasuredTime := mkRat n d


-- @@ L80-82 verbatim
protected def MeasuredTime.dot (m : MeasuredTime) (n : Nat := 1) : MeasuredTime :=
  let multiplier := 2 - mkRat 1 (2 ^ n)
  { bars := m.bars, offset := m.offset * multiplier }


-- @@ L84-87 verbatim
instance : Repr MeasuredTime where
  reprPrec i _ := match i.bars with
    | 0 => f!".{i.offset}"
    | b => f!"{b}.{i.offset}"

-- @@ L88-91 verbatim
instance : ToString MeasuredTime where
  toString i := match i.bars with
    | 0 => s!".{i.offset}"
    | b => s!"{b}.{i.offset}"


-- @@ L93-99 verbatim
open Lean in
instance : ToExpr MeasuredTime where
  toExpr t :=
    let bars := toExpr t.bars
    let offset := toExpr t.offset
    mkAppN (mkConst ``MeasuredTime.mk) #[bars, offset]
  toTypeExpr : Expr := mkConst ``MeasuredTime


-- @@ L101-102 verbatim
instance : Add MeasuredTime where
  add t1 t2 := ⟨t1.bars + t2.bars, t1.offset + t2.offset⟩

-- @@ L103-104 verbatim
instance : Sub MeasuredTime where
  sub t1 t2 := ⟨t1.bars - t2.bars, t1.offset - t2.offset⟩

-- @@ L105-106 verbatim
instance : Neg MeasuredTime where
  neg t := ⟨-t.bars, -t.offset⟩

-- @@ L107-108 verbatim
instance : SMul Int MeasuredTime where
  smul n t := ⟨n * t.bars, n * t.offset⟩

-- @@ L109-112 verbatim
instance : ShiftRight MeasuredTime where
  shiftRight t s := match s.bars with
    | 0 => ⟨t.bars, t.offset + s.offset⟩
    | b => ⟨t.bars + b, s.offset⟩


-- @@ L114-116 verbatim
instance : Time MeasuredTime where
  zero := ⟨0, 0⟩
  bar := ⟨1, 0⟩


-- @@ L118-121 verbatim
instance : SMul Rat MeasuredTime where
  smul n t :=
    let total := n * (t.bars + t.offset)
    ⟨ total.floor, total - total.floor ⟩


-- @@ L123-124 verbatim
structure DivisionLine where
  onBeat : Bool := false


-- @@ L126-130 verbatim
/-- Represents division of a time period. The ways of dividing notes
characterize music -/
structure Division (T := MeasuredTime) [Ord T] where
  lines : Std.TreeMap T DivisionLine
  --non_empty : lines.isEmpty = false


-- @@ L132-132 verbatim
namespace Division


-- @@ L134-134 verbatim
variable { T } [Time T]


-- @@ L136-138 verbatim
protected def zero : Division T := {
      lines := Std.TreeMap.empty.insert Time.zero { onBeat := true },
    }

-- @@ L139-140 verbatim
instance : Inhabited (Division T) where
  default := .zero


-- @@ L142-145 verbatim
protected def fromLines ( times : List T ) : Division T := {
    lines := times.foldl (init := .empty) λ m t =>
      m.insert t { }
  }

-- @@ L146-146 verbatim
protected def times (d : Division T) : List T := d.lines.keys

-- @@ L147-147 verbatim
protected def timesArray (d : Division T) : Array T := d.lines.keysArray

-- @@ L148-148 verbatim
protected def minTime (d : Division T) : T := d.lines.minKey!

-- @@ L149-149 verbatim
protected def maxTime (d : Division T) : T := d.lines.maxKey!


-- @@ L151-158 verbatim
/-- Iterate over sections -/
protected def forSectionsM { m } [Monad m] (d : Division T) (f : T → T → m Unit) : m Unit := do
  let _ : Option T := ← d.lines.foldlM (init := .none) λ t? t' _ => do
    match t? with
    | .none => pure ()
    | .some t =>
      f t t'
    pure (.some t')


-- @@ L160-160 verbatim
end Division
