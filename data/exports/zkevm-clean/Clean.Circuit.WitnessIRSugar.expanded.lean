import Clean.Circuit.WitnessIR


-- @@ L3-25 verbatim
/-!
# Authoring sugar for the witness IR

Makes witness-IR programs read like normal code:

- typeclass operators on the IR expression types (`+ * - ⁻¹` on `FExpr`;
  `+ * / % &&& ||| ^^^ <<< >>>` on `U64Expr`), numeric literals via `OfNat`,
  and a coercion from circuit `Expression`s,
- dot-notation bridges `x.val : U64Expr` (on `Expression` and `FExpr`) and
  `n.toField : FExpr`,
- condition notation `=?` / `<?`,
- `VExpr.range n fun i => ...` — loop former whose body receives the index as an
  `U64Expr` (applied to `.idx` at construction time, so the lambda is authoring-time
  only and the result is first-order data),
- a builder monad `Witgen.M` with `letF`/`letU` for shared intermediate values.

Example (SHA256 `Add32`-style):
```
witnessVectorProgram 32 do
  let s ← (bitsVal a + bitsVal b) % ((2^32 : ℕ) : U64Expr F)
  return .range 32 fun i => ((s >>> i) % 2).toField
```
-/


-- @@ L27-27 verbatim
variable {F : Type} {α β : Type}


-- @@ L29-29 verbatim
namespace Witgen


-- @@ L31-31 verbatim
/-! ## Operators and coercions -/


-- @@ L33-33 verbatim
instance : Coe (Expression F) (FExpr F) := ⟨.expr⟩

-- @@ L34-35 verbatim
instance : Coe (Expression F) (field (FExpr F)) where
  coe e := .expr e

-- @@ L36-36 verbatim
instance : Coe F (FExpr F) := ⟨.const⟩

-- @@ L37-37 verbatim
instance : Coe F (field (FExpr F)) := ⟨.const⟩

-- @@ L38-39 verbatim
instance {M : TypeMap} [ProvableType M] : Coe (M (Expression F)) (M (FExpr F)) where
  coe v := fromElements (toElements v |>.map .expr)

-- @@ L40-40 verbatim
instance {n : ℕ} [OfNat F n] : OfNat (FExpr F) n := ⟨.const (OfNat.ofNat n)⟩

-- @@ L41-41 verbatim
instance : Add (FExpr F) := ⟨.add⟩

-- @@ L42-42 verbatim
instance : Mul (FExpr F) := ⟨.mul⟩

-- @@ L43-43 verbatim
instance : Inv (FExpr F) := ⟨.inv⟩

-- @@ L44-44 verbatim
@[reducible] instance : Inv (field (Witgen.FExpr F)) := (inferInstance : Inv (Witgen.FExpr F))

-- @@ L45-45 verbatim
instance [Field F] : Neg (FExpr F) := ⟨.neg⟩

-- @@ L46-46 verbatim
instance [Field F] : Sub (FExpr F) := ⟨.sub⟩


-- @@ L48-48 verbatim
instance : Coe ℕ (U64Expr F) := ⟨(.const <| UInt64.ofNat ·)⟩

-- @@ L49-49 verbatim
instance : Coe UInt64 (U64Expr F) := ⟨.const⟩

-- @@ L50-50 verbatim
instance {n : ℕ} : OfNat (U64Expr F) n := ⟨.const (OfNat.ofNat n)⟩

-- @@ L51-52 verbatim
instance : Inhabited (U64Expr F) where
  default := .const 0

-- @@ L53-53 verbatim
instance : Add (U64Expr F) := ⟨.add⟩

-- @@ L54-54 verbatim
instance : Mul (U64Expr F) := ⟨.mul⟩

-- @@ L55-55 verbatim
instance : Div (U64Expr F) := ⟨.div⟩

-- @@ L56-57 verbatim
instance : HDiv (U64Expr F) ℕ (U64Expr F) where
  hDiv n m := .div n (.const (UInt64.ofNat m))

-- @@ L58-58 verbatim
instance : Mod (U64Expr F) := ⟨.mod⟩

-- @@ L59-60 verbatim
instance : HMod (U64Expr F) ℕ (U64Expr F) where
  hMod n m := .mod n (.const (UInt64.ofNat m))

-- @@ L61-61 verbatim
instance : AndOp (U64Expr F) := ⟨.land⟩

-- @@ L62-62 verbatim
instance : OrOp (U64Expr F) := ⟨.lor⟩

-- @@ L63-63 verbatim
instance : XorOp (U64Expr F) := ⟨.lxor⟩

-- @@ L64-64 verbatim
instance : ShiftLeft (U64Expr F) := ⟨.shiftL⟩

-- @@ L65-65 verbatim
instance : ShiftRight (U64Expr F) := ⟨.shiftR⟩

-- @@ L66-67 verbatim
instance : HShiftLeft (U64Expr F) ℕ (U64Expr F) where
  hShiftLeft n m := .shiftL n (.const (UInt64.ofNat m))

-- @@ L68-69 verbatim
instance : HShiftRight (U64Expr F) ℕ (U64Expr F) where
  hShiftRight n m := .shiftR n (.const (UInt64.ofNat m))


-- @@ L71-73 verbatim
/-- A single field-sorted expression is a length-1 witness program, so scalar
sites can pass an `FExpr` to the generic `witness`. -/
instance : Coe (FExpr F) (WitgenIR F 1) := ⟨.ofFExpr⟩


-- @@ L75-77 verbatim
/-! The `FExpr.eval`/`U64Expr.eval` matchers do not unfold the operator instances above,
so evaluation would get stuck on operator-sugared IR. Desugar to constructors in
`circuit_norm` via per-operator rfl-lemmas; the evaluators' own match equations then apply. -/


-- @@ L79-79 verbatim
@[circuit_norm] theorem FExpr.add_def (x y : FExpr F) : x + y = .add x y := rfl

-- @@ L80-80 verbatim
@[circuit_norm] theorem FExpr.mul_def (x y : FExpr F) : x * y = .mul x y := rfl

-- @@ L81-81 verbatim
@[circuit_norm] theorem FExpr.inv_def (x : FExpr F) : x⁻¹ = .inv x := rfl

-- @@ L82-82 verbatim
@[circuit_norm] theorem FExpr.neg_def [Field F] (x : FExpr F) : -x = FExpr.neg x := rfl

-- @@ L83-83 verbatim
@[circuit_norm] theorem FExpr.sub_def [Field F] (x y : FExpr F) : x - y = FExpr.sub x y := rfl


-- @@ L85-85 verbatim
@[circuit_norm] theorem U64Expr.add_def (x y : U64Expr F) : x + y = .add x y := rfl

-- @@ L86-86 verbatim
@[circuit_norm] theorem U64Expr.mul_def (x y : U64Expr F) : x * y = .mul x y := rfl

-- @@ L87-87 verbatim
@[circuit_norm] theorem U64Expr.div_def (x y : U64Expr F) : x / y = .div x y := rfl

-- @@ L88-89 verbatim
@[circuit_norm] theorem U64Expr.hDiv_def (x : U64Expr F) (m : ℕ) :
  x / m = U64Expr.div x (.const (UInt64.ofNat m)) := rfl

-- @@ L90-90 verbatim
@[circuit_norm] theorem U64Expr.mod_def (x y : U64Expr F) : x % y = .mod x y := rfl

-- @@ L91-92 verbatim
@[circuit_norm] theorem U64Expr.hMod_def (x : U64Expr F) (m : ℕ) :
  x % m = U64Expr.mod x (.const (UInt64.ofNat m)) := rfl

-- @@ L93-93 verbatim
@[circuit_norm] theorem U64Expr.land_def (x y : U64Expr F) : x &&& y = .land x y := rfl

-- @@ L94-94 verbatim
@[circuit_norm] theorem U64Expr.lor_def (x y : U64Expr F) : x ||| y = .lor x y := rfl

-- @@ L95-95 verbatim
@[circuit_norm] theorem U64Expr.lxor_def (x y : U64Expr F) : x ^^^ y = .lxor x y := rfl

-- @@ L96-96 verbatim
@[circuit_norm] theorem U64Expr.shiftL_def (x y : U64Expr F) : x <<< y = .shiftL x y := rfl

-- @@ L97-97 verbatim
@[circuit_norm] theorem U64Expr.shiftR_def (x y : U64Expr F) : x >>> y = .shiftR x y := rfl

-- @@ L98-99 verbatim
@[circuit_norm] theorem U64Expr.hShiftL_def (x : U64Expr F) (m : ℕ) :
  x <<< m = U64Expr.shiftL x (.const (UInt64.ofNat m)) := rfl

-- @@ L100-101 verbatim
@[circuit_norm] theorem U64Expr.hShiftR_def (x : U64Expr F) (m : ℕ) :
  x >>> m = U64Expr.shiftR x (.const (UInt64.ofNat m)) := rfl


-- @@ L103-103 verbatim
/-! ## Bridges as dot notation -/


-- @@ L105-106 verbatim
/-- The `u64` value of an IR field expression (truncated `ZMod.val`): `e.val`. -/
abbrev FExpr.val (e : FExpr F) : U64Expr F := .val e


-- @@ L108-109 verbatim
/-- The `u64` value of a circuit expression, as a witness-IR expression: `x.val`. -/
abbrev _root_.Expression.val (e : Expression F) : U64Expr F := .val (.expr e)


-- @@ L111-112 verbatim
/-- Cast a u64-sorted IR expression back into the field (via `FiniteField.fromNat`). -/
abbrev U64Expr.toField (n : U64Expr F) : FExpr F := .ofU64 n


-- @@ L114-115 verbatim
/-- The `n` low bits of the field value of an IR expression, as a vector output. -/
abbrev VExpr.bits (n : ℕ) (e : FExpr F) : VExpr F n := .bitsOf e


-- @@ L117-118 verbatim
/-- The `n` low bits of a circuit expression, as a vector output: `x.bits n`. -/
abbrev _root_.Expression.bits (e : Expression F) (n : ℕ) : VExpr F n := .bitsOf (.expr e)


-- @@ L120-121 verbatim
/-- Cast a boolean expression to a field element that is 0 or 1. -/
abbrev BExpr.toField [Field F] (b : BExpr F) : FExpr F := .ite b 1 0


-- @@ L123-124 verbatim
/-- Bit `i` of the field value of an IR expression, as the field element `0` or `1`. -/
abbrev FExpr.bit [Field F] (e : FExpr F) (i : ℕ) : FExpr F := (BExpr.bit e i).toField


-- @@ L126-128 verbatim
/-- Bit `i` of the field value of a circuit expression: `x.bit i`. -/
abbrev _root_.Expression.bit [Field F] (e : Expression F) (i : ℕ) : FExpr F :=
  (BExpr.bit (.expr e) i).toField


-- @@ L130-140 verbatim
/-- A bit-valued condition cast into the field is the corresponding `0`/`1` element —
the same normal form `VExpr.bitsOf` evaluates to, so bit-decomposition proofs see one
shape whether the bit index is static or the loop index. Keyed as a pre-rewrite so it
fires before `FExpr.eval` unfolds the underlying `ite`. -/
@[circuit_norm ↓]
theorem FExpr.eval_bit [FiniteField F] (ctx : Ctx F) (e : FExpr F) (i : ℕ) :
    FExpr.eval ctx (e.bit i) = FiniteField.fromNat (FiniteField.val (e.eval ctx) >>> i % 2) := by
  simp only [FExpr.eval, BExpr.eval, ← Nat.decide_shiftRight_mod_two_eq_one,
    decide_eq_true_eq]
  rcases Nat.mod_two_eq_zero_or_one (FiniteField.val (e.eval ctx) >>> i) with h | h <;>
    simp [h]


-- @@ L142-142 verbatim
/-! ## Conditions -/


-- @@ L144-151 verbatim
/-- Overload witness-IR equality tests while keeping a single parser entry for
`=?`. Field-sorted operands become `BExpr.feq`; u64-sorted operands become
`BExpr.neq` (u64 equality).  The operand types are heterogeneous so
`x =? 0` can keep `x` as an `Expression` while interpreting `0` as an IR
constant, preserving the exported witness shape. -/
class EqCond (α β : Type) (F : outParam Type) where
  /-- Build a witness-IR equality condition for these operand sorts. -/
  eqCond : α → β → BExpr F


-- @@ L153-153 verbatim
@[inherit_doc EqCond.eqCond] infix:50 " =? " => EqCond.eqCond


-- @@ L155-155 verbatim
instance : EqCond (FExpr F) (FExpr F) F := ⟨.feq⟩

-- @@ L156-156 verbatim
instance : EqCond (Expression F) (FExpr F) F where eqCond x y := .feq x y

-- @@ L157-157 verbatim
instance : EqCond (FExpr F) (Expression F) F where eqCond x y := .feq x y

-- @@ L158-158 verbatim
instance : EqCond (FExpr F) F F where eqCond x y := .feq x y

-- @@ L159-159 verbatim
instance : EqCond F (FExpr F) F where eqCond x y := .feq y x

-- @@ L160-160 verbatim
instance : EqCond (Expression F) F F where eqCond x y := .feq x y

-- @@ L161-161 verbatim
instance : EqCond F (Expression F) F where eqCond x y := .feq x y

-- @@ L162-162 verbatim
instance [NatCast F] : EqCond (Expression F) ℕ F where eqCond x n := .feq x (n : F)

-- @@ L163-163 verbatim
instance [NatCast F] : EqCond ℕ (Expression F) F where eqCond n x := .feq (n : F) x

-- @@ L164-164 verbatim
instance [NatCast F] : EqCond (FExpr F) ℕ F where eqCond x n := .feq x (n : F)

-- @@ L165-165 verbatim
instance [NatCast F] : EqCond ℕ (FExpr F) F where eqCond n x := .feq (n : F) x

-- @@ L166-166 verbatim
instance : EqCond (U64Expr F) (U64Expr F) F := ⟨.neq⟩

-- @@ L167-167 verbatim
instance : EqCond (U64Expr F) ℕ F where eqCond x n := .neq x (.const (UInt64.ofNat n))

-- @@ L168-168 verbatim
instance : EqCond ℕ (U64Expr F) F where eqCond n x := .neq (.const (UInt64.ofNat n)) x


-- @@ L170-175 verbatim
/-- Overload witness-IR less-than tests while keeping a single parser entry for `<?`.
Field-sorted operands become `BExpr.flt` (comparing `FiniteField.val`s, so it stays exact
on fields wider than 64 bits); u64-sorted operands become `BExpr.lt`. -/
class LtCond (α β : Type) (F : outParam Type) where
  /-- Build a witness-IR less-than condition for these operand sorts. -/
  ltCond : α → β → BExpr F


-- @@ L177-177 verbatim
@[inherit_doc LtCond.ltCond] infix:50 " <? " => LtCond.ltCond


-- @@ L179-179 verbatim
instance : LtCond (FExpr F) (FExpr F) F := ⟨.flt⟩

-- @@ L180-180 verbatim
instance : LtCond (Expression F) (FExpr F) F where ltCond x y := .flt x y

-- @@ L181-181 verbatim
instance : LtCond (FExpr F) (Expression F) F where ltCond x y := .flt x y

-- @@ L182-182 verbatim
instance : LtCond (FExpr F) F F where ltCond x y := .flt x y

-- @@ L183-183 verbatim
instance : LtCond F (FExpr F) F where ltCond x y := .flt x y

-- @@ L184-184 verbatim
instance : LtCond (Expression F) F F where ltCond x y := .flt x y

-- @@ L185-185 verbatim
instance : LtCond F (Expression F) F where ltCond x y := .flt x y

-- @@ L186-186 verbatim
instance [NatCast F] : LtCond (Expression F) ℕ F where ltCond x n := .flt x (n : F)

-- @@ L187-187 verbatim
instance [NatCast F] : LtCond ℕ (Expression F) F where ltCond n x := .flt (n : F) x

-- @@ L188-188 verbatim
instance [NatCast F] : LtCond (FExpr F) ℕ F where ltCond x n := .flt x (n : F)

-- @@ L189-189 verbatim
instance [NatCast F] : LtCond ℕ (FExpr F) F where ltCond n x := .flt (n : F) x

-- @@ L190-190 verbatim
instance : LtCond (U64Expr F) (U64Expr F) F := ⟨.lt⟩

-- @@ L191-191 verbatim
instance : LtCond (U64Expr F) ℕ F where ltCond x n := .lt x (.const (UInt64.ofNat n))

-- @@ L192-192 verbatim
instance : LtCond ℕ (U64Expr F) F where ltCond n x := .lt (.const (UInt64.ofNat n)) x


-- @@ L194-194 verbatim
instance : Inhabited (BExpr F) := ⟨.false⟩

-- @@ L195-195 verbatim
instance : AndOp (BExpr F) := ⟨.and⟩


-- @@ L197-198 verbatim
/-! Desugar `=?`/`&&&` conditions to constructors, for the same reason as the operator
lemmas above. One lemma per `EqCond` instance. -/


-- @@ L200-200 expanded
@[circuit_norm]
theorem EqCond.fexpr_fexpr_def (x y : FExpr F) : (EqCond.eqCond x y) = BExpr.feq x y :=
  rfl


-- @@ L201-202 expanded
@[circuit_norm]
theorem EqCond.expr_fexpr_def (x : Expression F) (y : FExpr F) :
    (EqCond.eqCond x y) = BExpr.feq (.expr x) y :=
  rfl


-- @@ L203-204 expanded
@[circuit_norm]
theorem EqCond.fexpr_expr_def (x : FExpr F) (y : Expression F) :
    (EqCond.eqCond x y) = BExpr.feq x (.expr y) :=
  rfl


-- @@ L205-206 expanded
@[circuit_norm]
theorem EqCond.fexpr_const_def (x : FExpr F) (y : F) :
    (EqCond.eqCond x y) = BExpr.feq x (.const y) :=
  rfl


-- @@ L207-208 expanded
@[circuit_norm]
theorem EqCond.const_fexpr_def (x : F) (y : FExpr F) :
    (EqCond.eqCond x y) = BExpr.feq y (.const x) :=
  rfl


-- @@ L209-210 expanded
@[circuit_norm]
theorem EqCond.expr_const_def (x : Expression F) (y : F) :
    (EqCond.eqCond x y) = BExpr.feq (.expr x) (.const y) :=
  rfl


-- @@ L211-212 expanded
@[circuit_norm]
theorem EqCond.const_expr_def (x : F) (y : Expression F) :
    (EqCond.eqCond x y) = BExpr.feq (.const x) (.expr y) :=
  rfl


-- @@ L213-214 expanded
@[circuit_norm]
theorem EqCond.expr_nat_def [NatCast F] (x : Expression F) (n : ℕ) :
    (EqCond.eqCond x n) = BExpr.feq (.expr x) (.const (n : F)) :=
  rfl


-- @@ L215-216 expanded
@[circuit_norm]
theorem EqCond.nat_expr_def [NatCast F] (n : ℕ) (x : Expression F) :
    (EqCond.eqCond n x) = BExpr.feq (.const (n : F)) (.expr x) :=
  rfl


-- @@ L217-218 expanded
@[circuit_norm]
theorem EqCond.fexpr_nat_def [NatCast F] (x : FExpr F) (n : ℕ) :
    (EqCond.eqCond x n) = BExpr.feq x (.const (n : F)) :=
  rfl


-- @@ L219-220 expanded
@[circuit_norm]
theorem EqCond.nat_fexpr_def [NatCast F] (n : ℕ) (x : FExpr F) :
    (EqCond.eqCond n x) = BExpr.feq (.const (n : F)) x :=
  rfl


-- @@ L221-221 expanded
@[circuit_norm]
theorem EqCond.u64_u64_def (x y : U64Expr F) : (EqCond.eqCond x y) = BExpr.neq x y :=
  rfl


-- @@ L222-223 expanded
@[circuit_norm]
theorem EqCond.u64_nat_def (x : U64Expr F) (n : ℕ) :
    (EqCond.eqCond x n) = BExpr.neq x (.const (UInt64.ofNat n)) :=
  rfl


-- @@ L224-225 expanded
@[circuit_norm]
theorem EqCond.nat_u64_def (n : ℕ) (x : U64Expr F) :
    (EqCond.eqCond n x) = BExpr.neq (.const (UInt64.ofNat n)) x :=
  rfl


-- @@ L226-226 verbatim
@[circuit_norm] theorem BExpr.and_def (x y : BExpr F) : x &&& y = BExpr.and x y := rfl


-- @@ L228-228 verbatim
/-! Same treatment for `<?`. One lemma per `LtCond` instance. -/


-- @@ L230-230 expanded
@[circuit_norm]
theorem LtCond.fexpr_fexpr_def (x y : FExpr F) : (LtCond.ltCond x y) = BExpr.flt x y :=
  rfl


-- @@ L231-232 expanded
@[circuit_norm]
theorem LtCond.expr_fexpr_def (x : Expression F) (y : FExpr F) :
    (LtCond.ltCond x y) = BExpr.flt (.expr x) y :=
  rfl


-- @@ L233-234 expanded
@[circuit_norm]
theorem LtCond.fexpr_expr_def (x : FExpr F) (y : Expression F) :
    (LtCond.ltCond x y) = BExpr.flt x (.expr y) :=
  rfl


-- @@ L235-236 expanded
@[circuit_norm]
theorem LtCond.fexpr_const_def (x : FExpr F) (y : F) :
    (LtCond.ltCond x y) = BExpr.flt x (.const y) :=
  rfl


-- @@ L237-238 expanded
@[circuit_norm]
theorem LtCond.const_fexpr_def (x : F) (y : FExpr F) :
    (LtCond.ltCond x y) = BExpr.flt (.const x) y :=
  rfl


-- @@ L239-240 expanded
@[circuit_norm]
theorem LtCond.expr_const_def (x : Expression F) (y : F) :
    (LtCond.ltCond x y) = BExpr.flt (.expr x) (.const y) :=
  rfl


-- @@ L241-242 expanded
@[circuit_norm]
theorem LtCond.const_expr_def (x : F) (y : Expression F) :
    (LtCond.ltCond x y) = BExpr.flt (.const x) (.expr y) :=
  rfl


-- @@ L243-244 expanded
@[circuit_norm]
theorem LtCond.expr_nat_def [NatCast F] (x : Expression F) (n : ℕ) :
    (LtCond.ltCond x n) = BExpr.flt (.expr x) (.const (n : F)) :=
  rfl


-- @@ L245-246 expanded
@[circuit_norm]
theorem LtCond.nat_expr_def [NatCast F] (n : ℕ) (x : Expression F) :
    (LtCond.ltCond n x) = BExpr.flt (.const (n : F)) (.expr x) :=
  rfl


-- @@ L247-248 expanded
@[circuit_norm]
theorem LtCond.fexpr_nat_def [NatCast F] (x : FExpr F) (n : ℕ) :
    (LtCond.ltCond x n) = BExpr.flt x (.const (n : F)) :=
  rfl


-- @@ L249-250 expanded
@[circuit_norm]
theorem LtCond.nat_fexpr_def [NatCast F] (n : ℕ) (x : FExpr F) :
    (LtCond.ltCond n x) = BExpr.flt (.const (n : F)) x :=
  rfl


-- @@ L251-251 expanded
@[circuit_norm]
theorem LtCond.u64_u64_def (x y : U64Expr F) : (LtCond.ltCond x y) = BExpr.lt x y :=
  rfl


-- @@ L252-253 expanded
@[circuit_norm]
theorem LtCond.u64_nat_def (x : U64Expr F) (n : ℕ) :
    (LtCond.ltCond x n) = BExpr.lt x (.const (UInt64.ofNat n)) :=
  rfl


-- @@ L254-255 expanded
@[circuit_norm]
theorem LtCond.nat_u64_def (n : ℕ) (x : U64Expr F) :
    (LtCond.ltCond n x) = BExpr.lt (.const (UInt64.ofNat n)) x :=
  rfl


-- @@ L257-257 verbatim
/-! ## Index access notation for .listGet -/


-- @@ L259-260 verbatim
instance {F : Type} {n : ℕ} : GetElem (Vector F n) (U64Expr F) (FExpr F) (fun _ _ => True) where
  getElem v i _ := FExpr.listGet (v.toList.map FExpr.const) i


-- @@ L262-263 verbatim
instance {F : Type} {n : ℕ} : GetElem (Vector (Expression F) n) (U64Expr F) (FExpr F) (fun _ _ => True) where
  getElem v i _ := FExpr.listGet (v.toList.map FExpr.expr) i


-- @@ L265-266 verbatim
instance {F : Type} {n : ℕ} : GetElem (Var (fields n) F) (U64Expr F) (FExpr F) (fun _ _ => True) :=
  inferInstanceAs (GetElem (Vector (Expression F) n) (U64Expr F) _ _)


-- @@ L268-269 verbatim
instance {F : Type} {n : ℕ} : GetElem (Vector (FExpr F) n) (U64Expr F) (FExpr F) (fun _ _ => True) where
  getElem v i _ := FExpr.listGet v.toList i


-- @@ L271-272 verbatim
/-! Desugar the `GetElem` instances above to `FExpr.listGet`, for the same reason as the
operator lemmas: matchers and simp keying do not see through the instances. -/


-- @@ L274-275 verbatim
@[circuit_norm] theorem getElem_vector_const_def {F : Type} {n : ℕ} (v : Vector F n) (i : U64Expr F) :
    v[i] = FExpr.listGet (v.toList.map FExpr.const) i := rfl

-- @@ L276-277 verbatim
@[circuit_norm] theorem getElem_vector_expr_def {F : Type} {n : ℕ} (v : Vector (Expression F) n) (i : U64Expr F) :
    v[i] = FExpr.listGet (v.toList.map FExpr.expr) i := rfl

-- @@ L278-279 verbatim
@[circuit_norm] theorem getElem_vector_fexpr_def {F : Type} {n : ℕ} (v : Vector (FExpr F) n) (i : U64Expr F) :
    v[i] = FExpr.listGet v.toList i := rfl


-- @@ L281-286 verbatim
@[circuit_norm]
lemma evalList_map_vector_const {F : Type} {ctx : Ctx F} [FiniteField F] {n : ℕ} (v : Vector F n) (i : ℕ) :
    FExpr.evalList ctx i (v.toList.map FExpr.const) = if hi : i < n then v[i] else 0 := by
  induction v using Vector.induct generalizing i with
  | nil => simp [FExpr.evalList]
  | cons hd tl ih => cases i <;> simp_all [FExpr.evalList, FExpr.eval]


-- @@ L288-293 verbatim
@[circuit_norm]
lemma evalList_map_vector_expr {F : Type} {ctx : Ctx F} [FiniteField F] {n : ℕ} (v : Vector (Expression F) n) (i : ℕ) :
    FExpr.evalList ctx i (v.toList.map FExpr.expr) = if hi : i < n then v[i].eval ctx.env else 0 := by
  induction v using Vector.induct generalizing i with
  | nil => simp [FExpr.evalList]
  | cons hd tl ih => cases i <;> simp_all [FExpr.evalList, FExpr.eval]


-- @@ L295-300 verbatim
@[circuit_norm]
lemma evalList_map_vector_fexpr {F : Type} {ctx : Ctx F} [FiniteField F] {n : ℕ} (v : Vector (FExpr F) n) (i : ℕ) :
    FExpr.evalList ctx i v.toList = if hi : i < n then v[i].eval ctx else 0 := by
  induction v using Vector.induct generalizing i with
  | nil => simp [FExpr.evalList]
  | cons hd tl ih => cases i <;> simp_all [FExpr.evalList]


-- @@ L302-302 verbatim
/-! ## Loop former -/


-- @@ L304-308 verbatim
/-- Vector output built per index; the body receives the loop index as an `U64Expr`.
The lambda is applied to `.idx` at construction time — authoring-time HOAS,
first-order result. -/
def VExpr.range (n : ℕ) (body : U64Expr F → FExpr F) : VExpr F n :=
  .mapRange n (body .idx)


-- @@ L310-312 verbatim
@[circuit_norm]
theorem VExpr.range_def (n : ℕ) (body : U64Expr F → FExpr F) :
    VExpr.range n body = .mapRange n (body .idx) := rfl


-- @@ L314-314 verbatim
/-! ## Builder monad for stepped programs -/


-- @@ L316-320 verbatim
/-- Witness-program builder: accumulates `let`-steps, so shared values are written
in `do`-notation via `letF` / `letU`. -/
@[reducible]
def M (F : Type) (α : Type) : Type :=
  Array (Step F) → α × Array (Step F)


-- @@ L322-325 verbatim
instance : Monad (M F) where
  pure a := fun s => (a, s)
  bind m f := fun s => let (a, s') := m s; f a s'
  map f m := fun s => let (a, s') := m s; (f a, s')


-- @@ L327-327 verbatim
attribute [circuit_norm] Array.size_empty Array.getElem?_push


-- @@ L329-331 verbatim
@[circuit_norm]
theorem M.pure_def (a : α) :
    (pure a : M F α) = fun s => (a, s) := rfl


-- @@ L333-335 verbatim
@[circuit_norm]
theorem M.bind_def (m : M F α) (f : α → M F β) :
    (m >>= f) = fun s => let (a, s') := m s; f a s' := rfl


-- @@ L337-339 verbatim
@[circuit_norm]
theorem M.map_def (f : α → β) (m : M F α) :
    (f <$> m) = fun s => let (a, s') := m s; (f a, s') := rfl


-- @@ L341-343 verbatim
/-- Bind a u64-sorted value as a shared step; returns a reference to it. -/
def letU (e : U64Expr F) : M F (U64Expr F) :=
  fun s => (.localVar s.size, s.push (.letU e))


-- @@ L345-345 verbatim
instance : CoeOut (U64Expr F) (M F (U64Expr F)) := ⟨letU⟩


-- @@ L347-349 verbatim
@[circuit_norm]
theorem letU_def (e : U64Expr F) :
    letU e = fun s => (.localVar s.size, s.push (.letU e)) := rfl


-- @@ L351-353 verbatim
/-- Bind a field-sorted value as a shared step; returns a reference to it. -/
def letF (e : FExpr F) : M F (FExpr F) :=
  fun s => (.localVar s.size, s.push (.letF e))


-- @@ L355-355 verbatim
instance : CoeOut (FExpr F) (M F (FExpr F)) := ⟨letF⟩


-- @@ L357-359 verbatim
@[circuit_norm]
theorem letF_def (e : FExpr F) :
    letF e = fun s => (.localVar s.size, s.push (.letF e)) := rfl


-- @@ L361-362 verbatim
instance {F: Type} [Field F] : Inhabited (FExpr F) where
  default := .const 0


-- @@ L364-365 verbatim
instance [Field F] {value : TypeMap} [ProvableType value] : Inhabited (value (FExpr F)) where
  default := fromElements default


-- @@ L367-367 verbatim
namespace M

-- @@ L368-371 verbatim
variable [FiniteField F] {value : TypeMap} [ProvableType value]

-- TODO WITGENIR the simp behavior currently takes an ugly low-level path because we were
-- too lazy to craft a high-level path that works in all cases


-- @@ L373-376 verbatim
@[circuit_norm]
def eval (env : ProverEnvironment F) (program : M F (value (FExpr F))) : value F :=
  let (out, steps) := program #[]
  Witgen.eval { env, locals := evalSteps env steps.toList } out


-- @@ L378-381 verbatim
@[circuit_norm]
def evalBool (env : ProverEnvironment F) (program : M F (BExpr F)) : Bool :=
  let (out, steps) := program #[]
  out.eval { env, locals := evalSteps env steps.toList }


-- @@ L383-386 verbatim
@[circuit_norm]
def evalU64 (env : ProverEnvironment F) (program : M F (U64Expr F)) : UInt64 :=
  let (out, steps) := program #[]
  out.eval { env, locals := evalSteps env steps.toList }


-- @@ L388-390 verbatim
theorem eval_pure (out : value (FExpr F)) (env : ProverEnvironment F) :
    eval env (fun s => (out, s)) = Witgen.eval { env } out := by
  rfl


-- @@ L392-396 verbatim
/-- Assemble a witness program from a builder computation returning the output vector. -/
@[circuit_norm]
def toIR {n : ℕ} (program : M F (VExpr F n)) : WitgenIR F n :=
  let (out, steps) := program #[]
  .ir steps.toList out


-- @@ L398-404 verbatim
/-- Not tagged `@[circuit_norm]`: `toIRLiteral` must stay intact inside `.witness`
operations so that `witnessProgram`'s completeness obligation can be recognized and
rewritten at the level of provable values (`ProverEnvironment.extendsVector_toIRLiteral`
in `Clean.Circuit.Basic`), instead of unfolding element-wise into `toElements` internals. -/
def toIRLiteral (program : M F (value (FExpr F))) : WitgenIR F (size value) :=
  let (out, steps) := program #[]
  .ir steps.toList (.lit (toElements out))


-- @@ L406-408 verbatim
theorem eval_toIRLiteral (program : M F (value (FExpr F))) (env : ProverEnvironment F) :
    program.toIRLiteral.eval env = toElements (program.eval env) := by
  simp [toIRLiteral, eval, WitgenIR.eval, Witgen.eval, ProvableType.toElements_fromElements, VExpr.eval]


-- @@ L410-411 verbatim
instance {α : Type} [Inhabited α] : Inhabited (M F α) where
  default := pure default

-- @@ L412-412 verbatim
end M

-- @@ L413-413 verbatim
end Witgen


-- @@ L415-422 verbatim
/--
IR-backed prover-only inputs for `GeneralFormalCircuit.WithHint`.

The verifier view is erased to `Unit`; the prover view is a typed witness program evaluated
against the prover environment. The closure-backed escape hatch is `UnconstrainedNative`.
-/
structure Unconstrained (M : TypeMap) (F : Type) where
  program : Witgen.M F (M (Witgen.FExpr F))


-- @@ L424-424 verbatim
namespace Unconstrained

-- @@ L425-425 verbatim
variable {value : TypeMap} [ProvableType value]

-- @@ L426-426 verbatim
open Witgen


-- @@ L428-433 verbatim
@[reducible] instance : CircuitType (Unconstrained value) where
  Var F := M F (value (FExpr F))
  ProverValue := value
  Value _ := Unit
  evalVerifier _ _ := ()
  evalProver env program := program.eval env


-- @@ L435-436 verbatim
instance [Field F] : Inhabited (Var (Unconstrained value) F) :=
  inferInstanceAs (Inhabited (M F (value (FExpr F))))


-- @@ L438-439 verbatim
@[circuit_norm] lemma var_of_unconstrained :
    Var (Unconstrained value) F = M F (value (FExpr F)) := rfl


-- @@ L441-442 verbatim
@[circuit_norm] lemma proverValue_of_unconstrained :
    ProverValue (Unconstrained value) F = value F := rfl


-- @@ L444-445 verbatim
@[circuit_norm] lemma value_of_unconstrained :
    Value (Unconstrained value) F = Unit := rfl


-- @@ L447-449 verbatim
@[circuit_norm] lemma eval_unconstrained [FiniteField F]
    (env : Environment F) (v : Var (Unconstrained value) F) :
    eval env v = () := by rfl


-- @@ L451-455 verbatim
@[circuit_norm] lemma eval_unconstrained_prover [FiniteField F]
    (env : ProverEnvironment F) (v : Var (Unconstrained value) F) :
    eval env v = M.eval (value := value) env v := by
  rw [CircuitType.eval_prover (M := Unconstrained value)]
  rfl


-- @@ L457-460 verbatim
@[circuit_norm] lemma eval_unconstrained_prover' [FiniteField F] :
  @eval (ProverEnvironment F) (M F (value (FExpr F))) (value F) (CircuitType.proverEval (Unconstrained value))
    = M.eval := by
  with_unfolding_all rfl


-- @@ L462-464 verbatim
@[circuit_norm]
def unconstrained (program : Witgen.M F (value (Witgen.FExpr F))) : Var (Unconstrained value) F :=
  program

-- @@ L465-465 verbatim
end Unconstrained


-- @@ L467-467 verbatim
export Unconstrained (unconstrained)


-- @@ L469-471 verbatim
/-- IR-backed prover-only Boolean input for `GeneralFormalCircuit.WithHint`. -/
structure UnconstrainedBool (F : Type) where
  program : Witgen.M F (Witgen.BExpr F)


-- @@ L473-473 verbatim
namespace UnconstrainedBool

-- @@ L474-474 verbatim
open Witgen


-- @@ L476-481 verbatim
@[reducible] instance : CircuitType UnconstrainedBool where
  Var F := M F (BExpr F)
  ProverValue _ := Bool
  Value _ := Unit
  evalVerifier _ _ := ()
  evalProver env program := program.evalBool env


-- @@ L483-484 verbatim
instance : Inhabited (Var UnconstrainedBool F) :=
  inferInstanceAs (Inhabited (M F (BExpr F)))


-- @@ L486-487 verbatim
@[circuit_norm] lemma var_of_unconstrainedBool :
    Var UnconstrainedBool F = M F (BExpr F) := rfl


-- @@ L489-490 verbatim
@[circuit_norm] lemma proverValue_of_unconstrainedBool :
    ProverValue UnconstrainedBool F = Bool := rfl


-- @@ L492-493 verbatim
@[circuit_norm] lemma value_of_unconstrainedBool :
    Value UnconstrainedBool F = Unit := rfl


-- @@ L495-497 verbatim
@[circuit_norm] lemma eval_unconstrainedBool [FiniteField F]
    (env : Environment F) (v : Var UnconstrainedBool F) :
    eval env v = () := by rfl


-- @@ L499-503 verbatim
@[circuit_norm] lemma eval_unconstrainedBool_prover [FiniteField F]
    (env : ProverEnvironment F) (v : Var UnconstrainedBool F) :
    eval env v = M.evalBool env v := by
  rw [CircuitType.eval_prover (M := UnconstrainedBool)]
  rfl


-- @@ L505-508 verbatim
@[circuit_norm] lemma eval_unconstrainedBool_prover' [FiniteField F] :
  @eval (ProverEnvironment F) (M F (BExpr F)) Bool (CircuitType.proverEval UnconstrainedBool)
    = M.evalBool := by
  with_unfolding_all rfl


-- @@ L510-512 verbatim
@[circuit_norm]
def unconstrainedBool (program : Witgen.M F (Witgen.BExpr F)) : Var UnconstrainedBool F :=
  program

-- @@ L513-513 verbatim
end UnconstrainedBool


-- @@ L515-515 verbatim
export UnconstrainedBool (unconstrainedBool)


-- @@ L517-519 verbatim
/-- IR-backed prover-only u64 input for `GeneralFormalCircuit.WithHint`. -/
structure UnconstrainedU64 (F : Type) where
  program : Witgen.M F (Witgen.U64Expr F)


-- @@ L521-521 verbatim
namespace UnconstrainedU64

-- @@ L522-522 verbatim
open Witgen


-- @@ L524-529 verbatim
@[reducible] instance : CircuitType UnconstrainedU64 where
  Var F := M F (U64Expr F)
  ProverValue _ := UInt64
  Value _ := Unit
  evalVerifier _ _ := ()
  evalProver env program := program.evalU64 env


-- @@ L531-532 verbatim
instance : Inhabited (Var UnconstrainedU64 F) :=
  inferInstanceAs (Inhabited (M F (U64Expr F)))


-- @@ L534-535 verbatim
@[circuit_norm] lemma var_of_unconstrainedU64 :
    Var UnconstrainedU64 F = M F (U64Expr F) := rfl


-- @@ L537-538 verbatim
@[circuit_norm] lemma proverValue_of_unconstrainedU64 :
    ProverValue UnconstrainedU64 F = UInt64 := rfl


-- @@ L540-541 verbatim
@[circuit_norm] lemma value_of_unconstrainedU64 :
    Value UnconstrainedU64 F = Unit := rfl


-- @@ L543-545 verbatim
@[circuit_norm] lemma eval_unconstrainedU64 [FiniteField F]
    (env : Environment F) (v : Var UnconstrainedU64 F) :
    eval env v = () := by rfl


-- @@ L547-551 verbatim
@[circuit_norm] lemma eval_unconstrainedU64_prover [FiniteField F]
    (env : ProverEnvironment F) (v : Var UnconstrainedU64 F) :
    eval env v = M.evalU64 env v := by
  rw [CircuitType.eval_prover (M := UnconstrainedU64)]
  rfl


-- @@ L553-556 verbatim
@[circuit_norm] lemma eval_unconstrainedU64_prover' [FiniteField F] :
  @eval (ProverEnvironment F) (M F (U64Expr F)) UInt64 (CircuitType.proverEval UnconstrainedU64)
    = M.evalU64 := by
  with_unfolding_all rfl


-- @@ L558-560 verbatim
@[circuit_norm]
def unconstrainedU64 (program : Witgen.M F (Witgen.U64Expr F)) : Var UnconstrainedU64 F :=
  program

-- @@ L561-561 verbatim
end UnconstrainedU64


-- @@ L563-563 verbatim
export UnconstrainedU64 (unconstrainedU64)
