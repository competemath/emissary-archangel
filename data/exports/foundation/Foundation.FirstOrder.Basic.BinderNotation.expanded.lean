module

public import Foundation.FirstOrder.Basic.Operator
public import Foundation.Vorspiel.Fin.Matrix


-- @@ L6-6 verbatim
@[expose] public section


-- @@ L8-8 verbatim
open Lean Elab PrettyPrinter Delaborator SubExpr


-- @@ L10-10 verbatim
namespace Lean.TSyntax


-- @@ L12-14 verbatim
meta def freshIdent [Monad m] [MonadQuotation m] : m (TSyntax `ident) := do
  let name ← Term.mkFreshBinderName
  return ⟨mkIdent name⟩


-- @@ L16-16 verbatim
end Lean.TSyntax


-- @@ L18-18 verbatim
namespace FFL.FirstOrder


-- @@ L20-20 verbatim
namespace Semiformula


-- @@ L22-22 verbatim
variable {L : Language} {ξ : Type*}


-- @@ L24-33 verbatim
/-- `nestFormulae φ(x₁,…,xₙ) ![Ψ₁(x₁,y₁,…,yₘ), …, Ψₙ(xₙ,y₁,…,yₘ)]` is the formula `∀ x₁, …, xₙ ((Ψ₁(x₁,y₁,…,yₘ) ∧ … ∧ Ψₙ(xₙ,y₁,…,yₘ)) → φ(x₁,…,xₙ))`.

Here, each formula `Ψᵢ` has `m + 1` bound variables, one for expressing a predicate of an `xᵢ`, and `m` remaining ones. In the resulting formula, the bound variables are the `m` remaining bound variables, while all of the original `n` bound variables of `φ` get bounded to a `∀` quantifier.

Intuitively, nestFormulae gives `R(f₁(y₁,…,yₘ), …, fₙ(y₁,…,yₘ))`, the result of substituting functions `f₁, … fₙ` into a relation `R`, using the defining formulae of their graphs (`xᵢ = fᵢ(y₁,…,yₘ)` iff `Ψᵢ(xᵢ,y₁,…,yₘ)`, and `R(x₁,…,xₙ)` iff `φ(x₁,…,xₙ)`). -/
def nestFormulae (φ : Semiformula L ξ n) (Ψ : Fin n → Semiformula L ξ (m + 1)) : Semiformula L ξ m :=
  let σ : Semiformula L ξ (m + n) :=
    (Matrix.conj fun i : Fin n ↦ Rewriting.subst (Ψ i) (#(i.addCast m) :> fun j ↦ #(j.addNat n))) 🡒
      Rewriting.subst φ fun i ↦ #(i.addCast m)
  ∀¹^[n] σ


-- @@ L35-44 verbatim
/-- `nestFormulaeFunc φ(x,x₁,…,xₙ) ![Ψ₁(x₁,y₁,…,yₘ), …, Ψₙ(xₙ,y₁,…,yₘ)]` is the formula `∀ x₁, …, xₙ ((Ψ₁(x₁,y₁,…,yₘ) ∧ … ∧ Ψₙ(xₙ,y₁,…,yₘ)) → φ(x,x₁,…,xₙ))`.

Here, each formula `Ψᵢ` has `m + 1` bound variables, one for expressing a predicate of an `xᵢ`, and `m` remaining ones. In the resulting formula, the bound variables are the `m` remaining bound variables plus `x`, while all of the original bound variables `x₁,…,xₙ` get bounded to a `∀` quantifier.

Intuitively, nestFormulaeFunc gives `F(f₁(y₁,…,yₘ), …, fₙ(y₁,…,yₘ))`, the result of substituting functions `f₁, … fₙ` into a function `F`, using the defining formulae of their graphs (`xᵢ = fᵢ(y₁,…,yₘ)` iff `Ψᵢ(xᵢ,y₁,…,yₘ)`, and `x = F(x₁,…,xₙ)` iff `φ(x,x₁,…,xₙ)`). -/
def nestFormulaeFunc (φ : Semiformula L ξ (n + 1)) (Ψ : Fin n → Semiformula L ξ (m + 1)) : Semiformula L ξ (m + 1) :=
  let σ : Semiformula L ξ ((m + 1) + n) :=
    (Matrix.conj fun i : Fin n ↦ Rewriting.subst (Ψ i) (#(i.addCast m.succ) :> fun j ↦ #(j.succ.addNat n))) 🡒
      Rewriting.subst φ (#((0 : Fin (m + 1)).addNat n) :> fun i ↦ #(i.addCast m.succ))
  ∀¹^[n] σ


-- @@ L46-50 verbatim
variable {M : Type*} [s : Structure L M] {f : ξ → M}

lemma eval_nestFormulae {φ : Semiformula L ξ n} {Ψ : Fin n → Semiformula L ξ (m + 1)} :
    Eval e f (φ.nestFormulae Ψ) ↔ ∀ v : Fin n → M, (∀ i, Eval (v i :> e) f (Ψ i)) → Eval v f φ := by
  simp [nestFormulae, Matrix.comp_vecCons', Function.comp_def]


-- @@ L52-54 verbatim
@[simp] lemma eval_nestFormulae₀ {φ : Semiformula L ξ 0} :
    Eval e f (φ.nestFormulae ![]) ↔ Eval ![] f φ := by
  simp [eval_nestFormulae, Matrix.empty_eq]


-- @@ L56-58 verbatim
@[simp] lemma eval_nestFormulae₁ {φ : Semiformula L ξ 1} {ψ : Semiformula L ξ (m + 1)} :
    Eval e f (φ.nestFormulae ![ψ]) ↔ ∀ x : M, Eval (x :> e) f ψ → Eval ![x] f φ := by
  simp [eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq]


-- @@ L60-66 verbatim
@[simp] lemma eval_nestFormulae₂ {φ : Semiformula L ξ 2} {ψ₁ ψ₂ : Semiformula L ξ (m + 1)} :
    Eval e f (φ.nestFormulae ![ψ₁, ψ₂]) ↔ ∀ x₁, Eval (x₁ :> e) f ψ₁ → ∀ x₂, Eval (x₂ :> e) f ψ₂ → Eval ![x₁, x₂] f φ := by
  suffices
    (∀ x₁ x₂, Eval (x₁ :> e) f ψ₁ → Eval (x₂ :> e) f ψ₂ → Eval ![x₁, x₂] f φ) ↔
    ∀ x₁, Eval (x₁ :> e) f ψ₁ → ∀ x₂, Eval (x₂ :> e) f ψ₂ → Eval ![x₁, x₂] f φ by
    simpa [eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_two]
  grind


-- @@ L68-75 verbatim
@[simp] lemma eval_nestFormulae₃ {φ : Semiformula L ξ 3} {ψ₁ ψ₂ ψ₃ : Semiformula L ξ (m + 1)} :
    Eval e f (φ.nestFormulae ![ψ₁, ψ₂, ψ₃]) ↔
    ∀ x₁, Eval (x₁ :> e) f ψ₁ → ∀ x₂, Eval (x₂ :> e) f ψ₂ → ∀ x₃, Eval (x₃ :> e) f ψ₃ → Eval ![x₁, x₂, x₃] f φ := by
  suffices
    (∀ x₁ x₂ x₃, Eval (x₁ :> e) f ψ₁ → Eval (x₂ :> e) f ψ₂ → Eval (x₃ :> e) f ψ₃ → Eval ![x₁, x₂, x₃] f φ) ↔
    ∀ x₁, Eval (x₁ :> e) f ψ₁ → ∀ x₂, Eval (x₂ :> e) f ψ₂ → ∀ x₃, Eval (x₃ :> e) f ψ₃ → Eval ![x₁, x₂, x₃] f φ by
    simpa [eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  grind


-- @@ L77-101 verbatim
@[simp] lemma eval_nestFormulae₄ {φ : Semiformula L ξ 4} {ψ₁ ψ₂ ψ₃ ψ₄ : Semiformula L ξ (m + 1)} :
    Eval e f (φ.nestFormulae ![ψ₁, ψ₂, ψ₃, ψ₄]) ↔
    ∀ x₁, Eval (x₁ :> e) f ψ₁ →
    ∀ x₂, Eval (x₂ :> e) f ψ₂ →
    ∀ x₃, Eval (x₃ :> e) f ψ₃ →
    ∀ x₄, Eval (x₄ :> e) f ψ₄ →
    Eval ![x₁, x₂, x₃, x₄] f φ := by
  suffices
    (∀ x₁ x₂ x₃ x₄,
      Eval (x₁ :> e) f ψ₁ →
      Eval (x₂ :> e) f ψ₂ →
      Eval (x₃ :> e) f ψ₃ →
      Eval (x₄ :> e) f ψ₄ →
      Eval ![x₁, x₂, x₃, x₄] f φ) ↔
    ( ∀ x₁, Eval (x₁ :> e) f ψ₁ →
      ∀ x₂, Eval (x₂ :> e) f ψ₂ →
      ∀ x₃, Eval (x₃ :> e) f ψ₃ →
      ∀ x₄, Eval (x₄ :> e) f ψ₄ →
      Eval ![x₁, x₂, x₃, x₄] f φ) by
    simpa [eval_nestFormulae, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  grind

lemma eval_nestFormulaeFunc {φ : Semiformula L ξ (n + 1)} {Ψ : Fin n → Semiformula L ξ (m + 1)} :
    Eval (z :> e) f (φ.nestFormulaeFunc Ψ) ↔ ∀ v : Fin n → M, (∀ i, Eval (v i :> e) f (Ψ i)) → Eval (z :> v) f φ := by
  simp [nestFormulaeFunc, Matrix.comp_vecCons', Function.comp_def]


-- @@ L103-105 verbatim
@[simp] lemma eval_nestFormulaeFunc₀ {φ : Semiformula L ξ 1} :
    Eval (z :> e) f (φ.nestFormulaeFunc ![]) ↔ Eval ![z] f φ := by
  simp [eval_nestFormulaeFunc, Matrix.empty_eq]


-- @@ L107-109 verbatim
@[simp] lemma eval_nestFormulaeFunc₁ {φ : Semiformula L ξ 2} {ψ : Semiformula L ξ (m + 1)} :
    Eval (z :> e) f (φ.nestFormulaeFunc ![ψ]) ↔ ∀ x, Eval (x :> e) f ψ → Eval ![z, x] f φ := by
  simp [eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq]


-- @@ L111-117 verbatim
@[simp] lemma eval_nestFormulaeFunc₂ {φ : Semiformula L ξ 3} {ψ₁ ψ₂ : Semiformula L ξ (m + 1)} :
    Eval (z :> e) f (φ.nestFormulaeFunc ![ψ₁, ψ₂]) ↔ ∀ x₁, Eval (x₁ :> e) f ψ₁ → ∀ x₂, Eval (x₂ :> e) f ψ₂ → Eval ![z, x₁, x₂] f φ := by
  suffices
    (∀ x₁ x₂, Eval (x₁ :> e) f ψ₁ → Eval (x₂ :> e) f ψ₂ → Eval ![z, x₁, x₂] f φ) ↔
    ∀ x₁, Eval (x₁ :> e) f ψ₁ → ∀ x₂, Eval (x₂ :> e) f ψ₂ → Eval ![z, x₁, x₂] f φ by
    simpa [eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_two]
  grind


-- @@ L119-126 verbatim
@[simp] lemma eval_nestFormulaeFunc₃ {φ : Semiformula L ξ 4} {ψ₁ ψ₂ ψ₃ : Semiformula L ξ (m + 1)} :
    Eval (z :> e) f (φ.nestFormulaeFunc ![ψ₁, ψ₂, ψ₃]) ↔
    ∀ x₁, Eval (x₁ :> e) f ψ₁ → ∀ x₂, Eval (x₂ :> e) f ψ₂ → ∀ x₃, Eval (x₃ :> e) f ψ₃ → Eval ![z, x₁, x₂, x₃] f φ := by
  suffices
    (∀ x₁ x₂ x₃, Eval (x₁ :> e) f ψ₁ → Eval (x₂ :> e) f ψ₂ → Eval (x₃ :> e) f ψ₃ → Eval ![z, x₁, x₂, x₃] f φ) ↔
    ∀ x₁, Eval (x₁ :> e) f ψ₁ → ∀ x₂, Eval (x₂ :> e) f ψ₂ → ∀ x₃, Eval (x₃ :> e) f ψ₃ → Eval ![z, x₁, x₂, x₃] f φ by
    simpa [eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  grind


-- @@ L128-148 verbatim
@[simp] lemma eval_nestFormulaeFunc₄ {φ : Semiformula L ξ 5} {ψ₁ ψ₂ ψ₃ ψ₄ : Semiformula L ξ (m + 1)} :
    Eval (z :> e) f (φ.nestFormulaeFunc ![ψ₁, ψ₂, ψ₃, ψ₄]) ↔
    ∀ x₁, Eval (x₁ :> e) f ψ₁ →
    ∀ x₂, Eval (x₂ :> e) f ψ₂ →
    ∀ x₃, Eval (x₃ :> e) f ψ₃ →
    ∀ x₄, Eval (x₄ :> e) f ψ₄ →
    Eval ![z, x₁, x₂, x₃, x₄] f φ := by
  suffices
    (∀ x₁ x₂ x₃ x₄,
      Eval (x₁ :> e) f ψ₁ →
      Eval (x₂ :> e) f ψ₂ →
      Eval (x₃ :> e) f ψ₃ →
      Eval (x₄ :> e) f ψ₄ →
      Eval ![z, x₁, x₂, x₃, x₄] f φ) ↔
    ( ∀ x₁, Eval (x₁ :> e) f ψ₁ →
      ∀ x₂, Eval (x₂ :> e) f ψ₂ →
      ∀ x₃, Eval (x₃ :> e) f ψ₃ →
      ∀ x₄, Eval (x₄ :> e) f ψ₄ →
      Eval ![z, x₁, x₂, x₃, x₄] f φ) by
    simpa [eval_nestFormulaeFunc, Matrix.vecForall_iff, Matrix.empty_eq, Fin.forall_fin_succ]
  grind


-- @@ L150-150 verbatim
end Semiformula


-- @@ L152-152 verbatim
namespace BinderNotation


-- @@ L154-156 verbatim
@[simp] abbrev finSuccItr {n} (i : Fin n) : (m : ℕ) → Fin (n + m)
  | 0     => i
  | m + 1 => (finSuccItr i m).succ


-- @@ L158-158 verbatim
open Semiterm Semiformula


-- @@ L160-160 verbatim
/-! ### (Literal) Notation for terms -/


-- @@ L162-162 verbatim
declare_syntax_cat first_order_term


-- @@ L164-164 verbatim
declare_syntax_cat first_order.quote_type


-- @@ L166-166 verbatim
syntax:max "lit" : first_order.quote_type -- literal notation

-- @@ L167-167 verbatim
syntax:max "faf" : first_order.quote_type -- formula-as-function notation


-- @@ L169-169 verbatim
syntax "⤫term(" first_order.quote_type ")[" ident* " | " ident* " | " first_order_term:0 "]" : term


-- @@ L171-171 verbatim
syntax "(" first_order_term ")" : first_order_term


-- @@ L173-173 verbatim
syntax:max ident : first_order_term         -- bound variable

-- @@ L174-174 verbatim
syntax:max "#" term:max : first_order_term  -- bound variable

-- @@ L175-175 verbatim
syntax:max "&" term:max : first_order_term  -- free variable

-- @@ L176-176 verbatim
syntax:80 "!" term:max first_order_term:81* (" ⋯")? : first_order_term

-- @@ L177-177 verbatim
syntax:80 "!!" term:max : first_order_term

-- @@ L178-178 verbatim
syntax:80 ".!" term:max first_order_term:81* (" ⋯")? : first_order_term

-- @@ L179-179 verbatim
syntax:80 ".!!" term:max : first_order_term


-- @@ L181-181 verbatim
syntax num : first_order_term

-- @@ L182-182 verbatim
syntax:max "↑" term:max : first_order_term

-- @@ L183-183 verbatim
syntax:max "⋆" : first_order_term

-- @@ L184-184 verbatim
syntax:50 first_order_term:50 " + " first_order_term:51 : first_order_term

-- @@ L185-185 verbatim
syntax:60 first_order_term:60 " * " first_order_term:61 : first_order_term

-- @@ L186-186 verbatim
syntax:65 first_order_term:65 " ^ " first_order_term:66 : first_order_term

-- @@ L187-187 verbatim
syntax:70 first_order_term " ^' " num  : first_order_term

-- @@ L188-188 verbatim
syntax:max first_order_term "²"  : first_order_term

-- @@ L189-189 verbatim
syntax:max first_order_term "³"  : first_order_term

-- @@ L190-190 verbatim
syntax:max first_order_term "⁴"  : first_order_term

-- @@ L191-191 verbatim
syntax:max "⌜" term:max "⌝" : first_order_term


-- @@ L193-193 verbatim
syntax:67  "exp " first_order_term:68 : first_order_term


-- @@ L195-196 verbatim
macro_rules
  | `(⤫term($type)[ $binders* | $fbinders* | ($e) ]) => `(⤫term($type)[ $binders* | $fbinders* | $e ])


-- @@ L198-225 verbatim
macro_rules
  | `(⤫term(lit)[ $binders* | $fbinders* | $x:ident]) => do
    match binders.idxOf? x with
    | none =>
      match fbinders.idxOf? x with
      | none => Macro.throwErrorAt x "error: variable did not found."
      | some x =>
        let i := Syntax.mkNumLit (toString x)
        `(&$i)
    | some x =>
      let i := Syntax.mkNumLit (toString x)
      `(#$i)
  | `(⤫term(lit)[ $_*       | $_*        | #$x:term   ]) => `(#$x)
  | `(⤫term(lit)[ $_*       | $_*        | &$x:term   ]) => `(&$x)
  | `(⤫term(lit)[ $_*       | $_*        | $m:num     ]) => `(Semiterm.numeral $m)
  | `(⤫term(lit)[ $_*       | $_*        | ↑$m:term   ]) => `(Semiterm.numeral $m)
  | `(⤫term(lit)[ $_*       | $_*        | ⌜$x:term⌝  ]) => `(⌜$x⌝)
  | `(⤫term(lit)[ $_*       | $_*        | ⋆          ]) => `(Operator.const Operator.Star.star)
  | `(⤫term(lit)[ $binders* | $fbinders* | $e₁ + $e₂  ]) => `(Semiterm.Operator.Add.add.operator ![⤫term(lit)[ $binders* | $fbinders* | $e₁ ], ⤫term(lit)[ $binders* | $fbinders* | $e₂ ]])
  | `(⤫term(lit)[ $binders* | $fbinders* | $e₁ * $e₂  ]) => `(Semiterm.Operator.Mul.mul.operator ![⤫term(lit)[ $binders* | $fbinders* | $e₁ ], ⤫term(lit)[ $binders* | $fbinders* | $e₂ ]])
  | `(⤫term(lit)[ $binders* | $fbinders* | $e₁ ^ $e₂  ]) => `(Semiterm.Operator.Pow.pow.operator ![⤫term(lit)[ $binders* | $fbinders* | $e₁ ], ⤫term(lit)[ $binders* | $fbinders* | $e₂ ]])
  | `(⤫term(lit)[ $binders* | $fbinders* | $e ^' $n   ]) => `((Semiterm.Operator.npow _ $n).operator ![⤫term(lit)[ $binders* | $fbinders* | $e ]])
  | `(⤫term(lit)[ $binders* | $fbinders* | $e²        ]) => `((Semiterm.Operator.npow _ 2).operator ![⤫term(lit)[ $binders* | $fbinders* | $e ]])
  | `(⤫term(lit)[ $binders* | $fbinders* | $e³        ]) => `((Semiterm.Operator.npow _ 3).operator ![⤫term(lit)[ $binders* | $fbinders* | $e ]])
  | `(⤫term(lit)[ $binders* | $fbinders* | $e⁴        ]) => `((Semiterm.Operator.npow _ 4).operator ![⤫term(lit)[ $binders* | $fbinders* | $e ]])
  | `(⤫term(lit)[ $binders* | $fbinders* | exp $e     ]) => `(Semiterm.Operator.Exp.exp.operator ![⤫term(lit)[ $binders* | $fbinders* | $e ]])
  | `(⤫term(lit)[ $_*       | $_*        | !!$t:term  ]) => `($t)
  | `(⤫term(lit)[ $_*       | $_*        | .!!$t:term ]) => `(Rew.emb $t)


-- @@ L227-243 verbatim
macro_rules
  | `(⤫term(lit)[ $binders* | $fbinders* | !$t:term $vs:first_order_term*    ]) => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s => `(⤫term(lit)[ $binders* | $fbinders* | $a ] :> $s))
    `(Rew.subst $v $t)
  | `(⤫term(lit)[ $binders* | $fbinders* | !$t:term $vs:first_order_term* ⋯  ]) =>
    do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length))) (fun a s ↦ `(⤫term(lit)[ $binders* | $fbinders* | $a] :> $s))
    `(Rew.subst $v $t)
  | `(⤫term(lit)[ $binders* | $fbinders* | .!$t:term $vs:first_order_term*   ]) => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s ↦ `(⤫term(lit)[ $binders* | $fbinders* | $a] :> $s))
    `(Rew.embSubsts $v $t)
  | `(⤫term(lit)[ $binders* | $fbinders* | .!$t:term $vs:first_order_term* ⋯ ]) =>
    do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length))) (fun a s ↦ `(⤫term(lit)[ $binders* | $fbinders* | $a] :> $s))
    `(Rew.embSubsts $v $t)


-- @@ L245-245 verbatim
syntax "‘" first_order_term:0 "’" : term

-- @@ L246-247 verbatim
/-- A term with free variables. -/
syntax "‘" ident* "| " first_order_term:0 "’" : term

-- @@ L248-249 verbatim
/-- A term with bound variables. -/
syntax "‘" ident* ". " first_order_term:0 "’" : term


-- @@ L251-254 verbatim
macro_rules
  | `(‘ $e:first_order_term ’)              => `(⤫term(lit)[           |            | $e ])
  | `(‘ $fbinders* | $e:first_order_term ’) => `(⤫term(lit)[           | $fbinders* | $e ])
  | `(‘ $binders*. $e:first_order_term ’)   => `(⤫term(lit)[ $binders* |            | $e ])


-- @@ L256-256 verbatim
#check (⤫term(lit)[ x y z | A B C | B + (4 + A * (x⁴ + z)²) + ↑4] : Semiterm ℒₒᵣ ℕ 1)

-- @@ L257-257 verbatim
#check ‘a x. a’


-- @@ L259-259 verbatim
section delab


-- @@ L261-264 verbatim
@[app_unexpander Semiterm.Operator.numeral]
meta def unexpanderNatLit : Unexpander
  | `($_ $_ $z:num) => `($z:num)
  | _ => throw ()


-- @@ L266-269 verbatim
@[app_unexpander Semiterm.Operator.const]
meta def unexpanderOperatorConst : Unexpander
  | `($_ $z:num) => `(‘ $z:num ’)
  | _ => throw ()


-- @@ L271-273 verbatim
@[app_unexpander Semiterm.Operator.Add.add]
meta def unexpanderAdd : Unexpander
  | `($_) => `(op(+))


-- @@ L275-277 verbatim
@[app_unexpander Semiterm.Operator.Mul.mul]
meta def unexpanderMul : Unexpander
  | `($_) => `(op(*))


-- @@ L279-332 verbatim
@[app_unexpander Semiterm.Operator.operator]
meta def unexpandFuncArith : Unexpander
  | `($_ op(+) ![‘$t:first_order_term’,   ‘$u:first_order_term’   ]) => `(‘($t     + $u     )’)
  | `($_ op(+) ![‘$t:first_order_term’,   #$x                     ]) => `(‘($t     + #$x    )’)
  | `($_ op(+) ![‘$t:first_order_term’,   &$x                     ]) => `(‘($t     + &$x    )’)
  | `($_ op(+) ![‘$t:first_order_term’,   ↑$m:num                 ]) => `(‘($t     + $m:num )’)
  | `($_ op(+) ![‘$t:first_order_term’,   $u:term                 ]) => `(‘($t     + !!$u   )’)
  | `($_ op(+) ![#$x,                     ‘$u:first_order_term’   ]) => `(‘(#$x    + $u     )’)
  | `($_ op(+) ![#$x,                     #$y                     ]) => `(‘(#$x    + #$y    )’)
  | `($_ op(+) ![#$x,                     &$y                     ]) => `(‘(#$x    + &$y    )’)
  | `($_ op(+) ![#$x,                     ↑$m:num                 ]) => `(‘(#$x    + $m:num )’)
  | `($_ op(+) ![#$x,                     $u                      ]) => `(‘(#$x    + !!$u   )’)
  | `($_ op(+) ![&$x,                     ‘$u:first_order_term’   ]) => `(‘(&$x    + $u     )’)
  | `($_ op(+) ![&$x,                     #$y                     ]) => `(‘(&$x    + #$y    )’)
  | `($_ op(+) ![&$x,                     &$y                     ]) => `(‘(&$x    + &$y    )’)
  | `($_ op(+) ![&$x,                     ↑$m:num                 ]) => `(‘(&$x    + $m:num )’)
  | `($_ op(+) ![&$x,                     $u                      ]) => `(‘(&$x    + !!$u   )’)
  | `($_ op(+) ![↑$n:num,                 ‘$u:first_order_term’   ]) => `(‘($n:num + $u     )’)
  | `($_ op(+) ![↑$n:num,                 #$y                     ]) => `(‘($n:num + #$y    )’)
  | `($_ op(+) ![↑$n:num,                 &$y                     ]) => `(‘($n:num + &$y    )’)
  | `($_ op(+) ![↑$n:num,                 ↑$m:num                 ]) => `(‘($n:num + $m:num )’)
  | `($_ op(+) ![↑$n:num,                 $u                      ]) => `(‘($n:num + !!$u   )’)
  | `($_ op(+) ![$t:term,                 ‘$u:first_order_term’   ]) => `(‘(!!$t   + $u     )’)
  | `($_ op(+) ![$t:term,                 #$y                     ]) => `(‘(!!$t   + #$y    )’)
  | `($_ op(+) ![$t:term,                 &$y                     ]) => `(‘(!!$t   + &$y    )’)
  | `($_ op(+) ![$t:term,                 ↑$m:num                 ]) => `(‘(!!$t   + $m:num )’)
  | `($_ op(+) ![$t:term,                 $u                      ]) => `(‘(!!$t   + !!$u   )’)

  | `($_ op(*) ![‘$t:first_order_term’,   ‘$u:first_order_term’   ]) => `(‘($t     * $u     )’)
  | `($_ op(*) ![‘$t:first_order_term’,   #$x                     ]) => `(‘($t     * #$x    )’)
  | `($_ op(*) ![‘$t:first_order_term’,   &$x                     ]) => `(‘($t     * &$x    )’)
  | `($_ op(*) ![‘$t:first_order_term’,   ↑$m:num                 ]) => `(‘($t     * $m:num )’)
  | `($_ op(*) ![‘$t:first_order_term’,   $u:term                 ]) => `(‘($t     * !!$u   )’)
  | `($_ op(*) ![#$x,                     ‘$u:first_order_term’   ]) => `(‘(#$x    * $u     )’)
  | `($_ op(*) ![#$x,                     #$y                     ]) => `(‘(#$x    * #$y    )’)
  | `($_ op(*) ![#$x,                     &$y                     ]) => `(‘(#$x    * &$y    )’)
  | `($_ op(*) ![#$x,                     ↑$m:num                 ]) => `(‘(#$x    * $m:num )’)
  | `($_ op(*) ![#$x,                     $u                      ]) => `(‘(#$x    * !!$u   )’)
  | `($_ op(*) ![&$x,                     ‘$u:first_order_term’   ]) => `(‘(&$x    * $u     )’)
  | `($_ op(*) ![&$x,                     #$y                     ]) => `(‘(&$x    * #$y    )’)
  | `($_ op(*) ![&$x,                     &$y                     ]) => `(‘(&$x    * &$y    )’)
  | `($_ op(*) ![&$x,                     ↑$m:num                 ]) => `(‘(&$x    * $m:num )’)
  | `($_ op(*) ![&$x,                     $u                      ]) => `(‘(&$x    * !!$u   )’)
  | `($_ op(*) ![↑$n:num,                 ‘$u:first_order_term’   ]) => `(‘($n:num * $u     )’)
  | `($_ op(*) ![↑$n:num,                 #$y                     ]) => `(‘($n:num * #$y    )’)
  | `($_ op(*) ![↑$n:num,                 &$y                     ]) => `(‘($n:num * &$y    )’)
  | `($_ op(*) ![↑$n:num,                 ↑$m:num                 ]) => `(‘($n:num * $m:num )’)
  | `($_ op(*) ![↑$n:num,                 $u                      ]) => `(‘($n:num * !!$u   )’)
  | `($_ op(*) ![$t:term,                 ‘$u:first_order_term’   ]) => `(‘(!!$t   * $u     )’)
  | `($_ op(*) ![$t:term,                 #$y                     ]) => `(‘(!!$t   * #$y    )’)
  | `($_ op(*) ![$t:term,                 &$y                     ]) => `(‘(!!$t   * &$y    )’)
  | `($_ op(*) ![$t:term,                 ↑$m:num                 ]) => `(‘(!!$t   * $m:num )’)
  | `($_ op(*) ![$t:term,                 $u                      ]) => `(‘(!!$t   * !!$u   )’)
  | _                             => throw ()


-- @@ L334-337 verbatim
@[app_unexpander Semiterm.numeral]
meta def unexpandNumeral : Unexpander
  | `($_ $n:num) => `(‘$n:num’)
  | _            => throw ()


-- @@ L339-339 verbatim
#check ‘ x | &4 + ((4 + 2) * #0 + #1)’


-- @@ L341-341 verbatim
end delab


-- @@ L343-343 verbatim
/-! ### Notation for formulae -/


-- @@ L345-345 verbatim
open Semiformula


-- @@ L347-347 verbatim
declare_syntax_cat first_order_formula



-- @@ L350-350 verbatim
syntax "⤫formula(" first_order.quote_type ")[" ident* " | " ident* " | " first_order_formula:0 "]" : term


-- @@ L352-352 verbatim
syntax "(" first_order_formula ")" : first_order_formula


-- @@ L354-354 verbatim
syntax:60 "of_term[" first_order_term:61 "]" : first_order_formula


-- @@ L356-356 verbatim
syntax:60 "!" term:max first_order_term:61* ("⋯")? : first_order_formula

-- @@ L357-357 verbatim
syntax:60 "!!" term:max : first_order_formula


-- @@ L359-359 verbatim
syntax:60 ".!" term:max first_order_term:61* ("⋯")? : first_order_formula

-- @@ L360-360 verbatim
syntax:60 ".!!" term:max : first_order_formula


-- @@ L362-362 verbatim
syntax "⊤" : first_order_formula

-- @@ L363-363 verbatim
syntax "⊥" : first_order_formula

-- @@ L364-364 verbatim
syntax:32 first_order_formula:33 " ∧ " first_order_formula:32 : first_order_formula

-- @@ L365-365 verbatim
syntax:30 first_order_formula:31 " ∨ " first_order_formula:30 : first_order_formula

-- @@ L366-366 verbatim
syntax:max "¬" first_order_formula:35 : first_order_formula

-- @@ L367-367 verbatim
syntax:10 first_order_formula:9 " → " first_order_formula:10 : first_order_formula

-- @@ L368-368 verbatim
syntax:5 first_order_formula " ↔ " first_order_formula : first_order_formula

-- @@ L369-369 verbatim
syntax:max "⋀ " ident ", " first_order_formula:0 : first_order_formula

-- @@ L370-370 verbatim
syntax:max "⋁ " ident ", " first_order_formula:0 : first_order_formula

-- @@ L371-371 verbatim
syntax:max "⋀ " ident " < " term ", " first_order_formula:0 : first_order_formula

-- @@ L372-372 verbatim
syntax:max "⋁ " ident " < " term ", " first_order_formula:0 : first_order_formula


-- @@ L374-374 verbatim
syntax:max "∀ " ident+ ", " first_order_formula:0 : first_order_formula

-- @@ L375-375 verbatim
syntax:max "∃ " ident+ ", " first_order_formula:0 : first_order_formula

-- @@ L376-376 verbatim
syntax:max "∀¹ " first_order_formula:0 : first_order_formula

-- @@ L377-377 verbatim
syntax:max "∃¹ " first_order_formula:0 : first_order_formula

-- @@ L378-378 verbatim
syntax:max "∀¹[" first_order_formula "] " first_order_formula:0 : first_order_formula

-- @@ L379-379 verbatim
syntax:max "∃¹[" first_order_formula "] " first_order_formula:0 : first_order_formula


-- @@ L381-381 verbatim
#check @HTilde.hTilde _ _ Tilde.instHTilde


-- @@ L383-431 verbatim
macro_rules
  | `(⤫formula($type)[ $binders* | $fbinders* | ($e)          ]) => `(⤫formula($type)[ $binders* | $fbinders* | $e ])
  | `(⤫formula($type)[ $_*       | $_*        | !!$φ:term     ]) => `($φ)
  | `(⤫formula($type)[ $_*       | $_*        | .!!$φ:term    ]) => `(Rewriting.emb $φ)
  | `(⤫formula($type)[ $_*       | $_*        | ⊤             ]) => `(⊤)
  | `(⤫formula($type)[ $_*       | $_*        | ⊥             ]) => `(⊥)
  | `(⤫formula($type)[ $binders* | $fbinders* | $φ ∧ $ψ       ]) => `(@HWedge.hWedge _ _ _ Wedge.instHWedge ⤫formula($type)[ $binders* | $fbinders* | $φ ] ⤫formula($type)[ $binders* | $fbinders* | $ψ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | $φ ∨ $ψ       ]) => `(@HVee.hVee _ _ _ Vee.instHVee ⤫formula($type)[ $binders* | $fbinders* | $φ ] ⤫formula($type)[ $binders* | $fbinders* | $ψ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ¬$φ           ]) => `(@HTilde.hTilde _ _ Tilde.instHTilde ⤫formula($type)[ $binders* | $fbinders* | $φ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | $φ → $ψ       ]) => `(@HArrow.hArrow _ _ _ Arrow.instHArrow ⤫formula($type)[ $binders* | $fbinders* | $φ ] ⤫formula($type)[ $binders* | $fbinders* | $ψ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | $φ ↔ $ψ       ]) => `(⤫formula($type)[ $binders* | $fbinders* | $φ ] 🡘 ⤫formula($type)[ $binders* | $fbinders* | $ψ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ⋀ $i, $φ      ]) => `(Matrix.conj fun $i ↦ ⤫formula($type)[ $binders* | $fbinders* | $φ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ⋁ $i, $φ      ]) => `(Matrix.disj fun $i ↦ ⤫formula($type)[ $binders* | $fbinders* | $φ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ⋀ $i < $t, $φ ]) => `(conjLt (fun $i ↦ ⤫formula($type)[ $binders* | $fbinders* | $φ ]) $t)
  | `(⤫formula($type)[ $binders* | $fbinders* | ⋁ $i < $t, $φ ]) => `(disjLt (fun $i ↦ ⤫formula($type)[ $binders* | $fbinders* | $φ ]) $t)
  | `(⤫formula($type)[ $binders* | $fbinders* | ∀ $xs*, $φ    ]) => do
    let xs := xs.reverse
    let binders' : TSyntaxArray `ident ← xs.foldrM
      (fun z binders' ↦ do
        if binders.elem z then Macro.throwErrorAt z "error: variable is duplicated." else
        return binders'.insertIdx 0 z)
      binders
    let s : TSyntax `term ← xs.size.rec `(⤫formula($type)[ $binders'* | $fbinders* | $φ ]) (fun _ ψ ↦ ψ >>= fun ψ ↦ `(∀¹ $ψ))
    return s
  | `(⤫formula($type)[ $binders* | $fbinders* | ∃ $xs*, $φ    ]) => do
    let xs := xs.reverse
    let binders' : TSyntaxArray `ident ← xs.foldrM
      (fun z binders' ↦ do
        if binders.elem z then Macro.throwErrorAt z "error: variable is duplicated." else
        return binders'.insertIdx 0 z)
      binders
    let s : TSyntax `term ← xs.size.rec `(⤫formula($type)[ $binders'* | $fbinders* | $φ ]) (fun _ ψ ↦ ψ >>= fun ψ ↦ `(∃¹ $ψ))
    return s
  | `(⤫formula($type)[ $binders* | $fbinders* | ∀¹ $φ         ]) => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∀¹ ⤫formula($type)[ $binders'* | $fbinders* | $φ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ∃¹ $φ         ]) => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∃¹ ⤫formula($type)[ $binders'* | $fbinders* | $φ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ∀¹[ $φ ] $ψ    ]) => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∀¹[⤫formula($type)[ $binders'* | $fbinders* | $φ ]] ⤫formula($type)[ $binders'* | $fbinders* | $ψ ])
  | `(⤫formula($type)[ $binders* | $fbinders* | ∃¹[ $φ ] $ψ    ]) => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∃¹[⤫formula($type)[ $binders'* | $fbinders* | $φ ]] ⤫formula($type)[ $binders'* | $fbinders* | $ψ ])


-- @@ L433-447 verbatim
/--
A formula in literal notation. For a formula `φ`, write `!φ` to include `φ` in the formula. Identifiers may be written after `!φ` as its bound variables.

`⋯` adds enough unnamed bound variables to fill up the arity of `φ`, with indices starting after the last named identifier. For example, assume `φ` is a `Semiformula L k`, and consider the formula `“x y z. !φ x y ⋯”`. Here `x`, `y`, and `z` are the bound variables `#0`, `#1`, and `#2` respectively. Then `!φ x y ⋯` will add `k - 2` new bound variables, and expand to `!φ #0 #1 #3 #4 ... #(k + 1)`.
-/
macro_rules
  | `(⤫formula(lit)[ $binders* | $fbinders* | !$φ:term $vs:first_order_term*   ]) => do
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) (fun a s ↦ `(⤫term(lit)[ $binders* | $fbinders* | $a ] :> $s))
    `($φ ⇜ $v)
  | `(⤫formula(lit)[ $binders* | $fbinders* | !$φ:term $vs:first_order_term* ⋯ ]) =>
    do
    let length := Syntax.mkNumLit (toString binders.size)
    let v ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length)))
      (fun a s ↦ `(⤫term(lit)[ $binders* | $fbinders* | $a] :> $s))
    `($φ ⇜ $v)


-- @@ L449-449 verbatim
syntax "“" ident* "| "  first_order_formula:0 "”" : term

-- @@ L450-450 verbatim
syntax "“" ident* ". "  first_order_formula:0 "”" : term

-- @@ L451-451 verbatim
syntax "“" first_order_formula:0 "”" : term


-- @@ L453-456 verbatim
macro_rules
  | `(“ $e:first_order_formula ”)              => `(⤫formula(lit)[           |            | $e ])
  | `(“ $binders*. $e:first_order_formula ”)   => `(⤫formula(lit)[ $binders* |            | $e ])
  | `(“ $fbinders* | $e:first_order_formula ”) => `(⤫formula(lit)[           | $fbinders* | $e ])


-- @@ L458-458 verbatim
syntax:45 first_order_term:45 " = " first_order_term:0 : first_order_formula

-- @@ L459-459 verbatim
syntax:45 first_order_term:45 " < " first_order_term:0 : first_order_formula

-- @@ L460-460 verbatim
syntax:45 first_order_term:45 " > " first_order_term:0 : first_order_formula

-- @@ L461-461 verbatim
syntax:45 first_order_term:45 " ≤ " first_order_term:0 : first_order_formula

-- @@ L462-462 verbatim
syntax:45 first_order_term:45 " ≥ " first_order_term:0 : first_order_formula

-- @@ L463-463 verbatim
syntax:45 first_order_term:45 " ∈ " first_order_term:0 : first_order_formula

-- @@ L464-464 verbatim
syntax:45 first_order_term:45 " ∋ " first_order_term:0 : first_order_formula

-- @@ L465-465 verbatim
syntax:45 first_order_term:45 " ≠ " first_order_term:0 : first_order_formula

-- @@ L466-466 verbatim
syntax:45 first_order_term:45 " ≮ " first_order_term:0 : first_order_formula

-- @@ L467-467 verbatim
syntax:45 first_order_term:45 " ≰ " first_order_term:0 : first_order_formula

-- @@ L468-468 verbatim
syntax:45 first_order_term:45 " ∉ " first_order_term:0 : first_order_formula


-- @@ L470-470 verbatim
syntax:max "∀ " ident " < " first_order_term ", " first_order_formula:0 : first_order_formula

-- @@ L471-471 verbatim
syntax:max "∀ " ident " ≤ " first_order_term ", " first_order_formula:0 : first_order_formula

-- @@ L472-472 verbatim
syntax:max "∀ " ident " ∈ " first_order_term ", " first_order_formula:0 : first_order_formula

-- @@ L473-473 verbatim
syntax:max "∃ " ident " < " first_order_term ", " first_order_formula:0 : first_order_formula

-- @@ L474-474 verbatim
syntax:max "∃ " ident " ≤ " first_order_term ", " first_order_formula:0 : first_order_formula

-- @@ L475-475 verbatim
syntax:max "∃ " ident " ∈ " first_order_term ", " first_order_formula:0 : first_order_formula


-- @@ L477-480 verbatim
macro_rules
  | `(⤫formula($type)[ $binders* | $fbinders* | $t:first_order_term > $u:first_order_term ]) => `(⤫formula($type)[ $binders* | $fbinders* | $u:first_order_term < $t:first_order_term ])
  | `(⤫formula($type)[ $binders* | $fbinders* | $t:first_order_term ≥ $u:first_order_term ]) => `(⤫formula($type)[ $binders* | $fbinders* | $u:first_order_term ≤ $t:first_order_term ])
  | `(⤫formula($type)[ $binders* | $fbinders* | $t:first_order_term ∋ $u:first_order_term ]) => `(⤫formula($type)[ $binders* | $fbinders* | $u:first_order_term ∈ $t:first_order_term ])


-- @@ L482-490 verbatim
macro_rules
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term = $u:first_order_term ]) => `(Semiformula.Operator.operator Operator.Eq.eq ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]])
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term < $u:first_order_term ]) => `(Semiformula.Operator.operator Operator.LT.lt ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]])
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term ≤ $u:first_order_term ]) => `(Semiformula.Operator.operator Operator.LE.le ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]])
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term ∈ $u:first_order_term ]) => `(Semiformula.Operator.operator Operator.Mem.mem ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]])
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term ≠ $u:first_order_term ]) => `(@HTilde.hTilde _ _ Tilde.instHTilde (Semiformula.Operator.operator Operator.Eq.eq ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]]))
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term ≮ $u:first_order_term ]) => `(@HTilde.hTilde _ _ Tilde.instHTilde (Semiformula.Operator.operator Operator.LT.lt ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]]))
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term ≰ $u:first_order_term ]) => `(@HTilde.hTilde _ _ Tilde.instHTilde (Semiformula.Operator.operator Operator.LE.le ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]]))
  | `(⤫formula(lit)[ $binders* | $fbinders* | $t:first_order_term ∉ $u:first_order_term ]) => `(@HTilde.hTilde _ _ Tilde.instHTilde (Semiformula.Operator.operator Operator.Mem.mem ![⤫term(lit)[ $binders* | $fbinders* | $t ], ⤫term(lit)[ $binders* | $fbinders* | $u ]]))


-- @@ L492-510 verbatim
macro_rules
  | `(⤫formula(lit)[ $binders* | $fbinders* | ∀ $x < $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    `(Semiformula.ballLT ⤫term(lit)[ $binders* | $fbinders* | $t ] ⤫formula(lit)[ $x $binders* | $fbinders* | $φ ])
  | `(⤫formula(lit)[ $binders* | $fbinders* | ∀ $x ≤ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    `(Semiformula.ballLE ⤫term(lit)[ $binders* | $fbinders* | $t ] ⤫formula(lit)[ $x $binders* | $fbinders* | $φ ])
  | `(⤫formula(lit)[ $binders* | $fbinders* | ∀ $x ∈ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    `(Semiformula.ballMem ⤫term(lit)[ $binders* | $fbinders* | $t ] ⤫formula(lit)[ $x $binders* | $fbinders* | $φ ])
  | `(⤫formula(lit)[ $binders* | $fbinders* | ∃ $x < $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    `(Semiformula.bexsLT ⤫term(lit)[ $binders* | $fbinders* | $t ] ⤫formula(lit)[ $x $binders* | $fbinders* | $φ ])
  | `(⤫formula(lit)[ $binders* | $fbinders* | ∃ $x ≤ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    `(Semiformula.bexsLE ⤫term(lit)[ $binders* | $fbinders* | $t ] ⤫formula(lit)[ $x $binders* | $fbinders* | $φ ])
  | `(⤫formula(lit)[ $binders* | $fbinders* | ∃ $x ∈ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
    `(Semiformula.bexsMem ⤫term(lit)[ $binders* | $fbinders* | $t ] ⤫formula(lit)[ $x $binders* | $fbinders* | $φ ])


-- @@ L512-512 verbatim
#check “∀ x, ∀ y, ∀ z, ∀ v, ∀ w, x + y + z + v + w = 0”

-- @@ L513-513 verbatim
#check “∀ x y z v w, x + y + z + v + w = 0”

-- @@ L514-514 verbatim
#check “x y z | ∃ v w, ∀ r < z + v + 7, ∀¹ x + y + v = x ↔ z = .!(‘#0 + #1’) x y”

-- @@ L515-515 verbatim
#check “x y. ∀ z < 0, ∀ w < y, x = z + w”


-- @@ L517-517 verbatim
section delab


-- @@ L519-521 verbatim
@[app_unexpander Language.Eq.eq]
meta def unexpanderEq : Unexpander
  | `($_) => `(op(=))


-- @@ L523-525 verbatim
@[app_unexpander Language.LT.lt]
meta def unexpanderLe : Unexpander
  | `($_) => `(op(<))


-- @@ L527-532 verbatim
@[app_unexpander Wedge.wedge]
meta def unexpandAnd : Unexpander
  | `($_ “ $φ:first_order_formula ” “ $ψ:first_order_formula ”) => `(“ ($φ ∧ $ψ) ”)
  | `($_ “ $φ:first_order_formula ” $u:term                   ) => `(“ ($φ ∧ !$u) ”)
  | `($_ $t:term                    “ $ψ:first_order_formula ”) => `(“ (!$t ∧ $ψ) ”)
  | _                                                           => throw ()


-- @@ L534-539 verbatim
@[app_unexpander Vee.vee]
meta def unexpandOr : Unexpander
  | `($_ “ $φ:first_order_formula ” “ $ψ:first_order_formula ”) => `(“ ($φ ∨ $ψ) ”)
  | `($_ “ $φ:first_order_formula ” $u:term                   ) => `(“ ($φ ∨ !$u) ”)
  | `($_ $t:term                    “ $ψ:first_order_formula ”) => `(“ (!$t ∨ $ψ) ”)
  | _                                                           => throw ()


-- @@ L541-544 verbatim
@[app_unexpander Tilde.tilde]
meta def unexpandNeg : Unexpander
  | `($_ “ $φ:first_order_formula ”) => `(“ ¬$φ ”)
  | _                                => throw ()


-- @@ L546-549 verbatim
@[app_unexpander UnivQuantifier.all]
meta def unexpandUniv : Unexpander
  | `($_ “ $φ:first_order_formula ”) => `(“ ∀¹ $φ:first_order_formula ”)
  | _                                => throw ()


-- @@ L551-554 verbatim
@[app_unexpander ExsQuantifier.exs]
meta def unexpandEx : Unexpander
  | `($_ “ $φ:first_order_formula”) => `(“ ∃¹ $φ:first_order_formula ”)
  | _                                   => throw ()


-- @@ L556-561 verbatim
@[app_unexpander ball]
meta def unexpandBall : Unexpander
  | `($_ “ $φ:first_order_formula ” “ $ψ:first_order_formula ”) => `(“ (∀¹[$φ] $ψ) ”)
  | `($_ “ $φ:first_order_formula ” $u:term                   ) => `(“ (∀¹[$φ] !$u) ”)
  | `($_ $t:term                    “ $ψ:first_order_formula ”) => `(“ (∀¹[!$t] $ψ) ”)
  | _                                                           => throw ()


-- @@ L563-568 verbatim
@[app_unexpander bexs]
meta def unexpandBex : Unexpander
  | `($_ “ $φ:first_order_formula ” “ $ψ:first_order_formula ”) => `(“ (∃¹[$φ] $ψ) ”)
  | `($_ “ $φ:first_order_formula ” $u:term                   ) => `(“ (∃¹[$φ] !$u) ”)
  | `($_ $t:term                    “ $ψ:first_order_formula ”) => `(“ (∃¹[!$t] $ψ) ”)
  | _                                                           => throw ()


-- @@ L570-575 verbatim
@[app_unexpander Arrow.arrow]
meta def unexpandArrow : Unexpander
  | `($_ “ $φ:first_order_formula ” “ $ψ:first_order_formula”) => `(“ ($φ → $ψ) ”)
  | `($_ “ $φ:first_order_formula ” $u:term                  ) => `(“ ($φ → !$u) ”)
  | `($_ $t:term                    “ $ψ:first_order_formula”) => `(“ (!$t → $ψ) ”)
  | _                                                          => throw ()


-- @@ L577-582 verbatim
@[app_unexpander LogicalConnective.iff]
meta def unexpandIff : Unexpander
  | `($_ “ $φ:first_order_formula” “ $ψ:first_order_formula”) => `(“ ($φ ↔ $ψ) ”)
  | `($_ “ $φ:first_order_formula” $u:term                  ) => `(“ ($φ ↔ !$u) ”)
  | `($_ $t:term                   “ $ψ:first_order_formula”) => `(“ (!$t ↔ $ψ) ”)
  | _                                                         => throw ()


-- @@ L584-690 verbatim
@[app_unexpander Semiformula.Operator.operator]
meta def unexpandOpArith : Unexpander
  | `($_ op(=) ![‘ $t:first_order_term ’,  ‘ $u:first_order_term ’]) => `(“ $t:first_order_term = $u      ”)
  | `($_ op(=) ![‘ $t:first_order_term ’,  #$y:term               ]) => `(“ $t:first_order_term = #$y     ”)
  | `($_ op(=) ![‘ $t:first_order_term ’,  &$y:term               ]) => `(“ $t:first_order_term = &$y     ”)
  | `($_ op(=) ![‘ $t:first_order_term ’,  ↑$m:num                ]) => `(“ $t:first_order_term = $m:num  ”)
  | `($_ op(=) ![‘ $t:first_order_term ’,  $u                     ]) => `(“ $t:first_order_term = !!$u    ”)
  | `($_ op(=) ![#$x:term,                 ‘ $u:first_order_term ’]) => `(“ #$x                 = $u      ”)
  | `($_ op(=) ![#$x:term,                 #$y:term               ]) => `(“ #$x                 = #$y     ”)
  | `($_ op(=) ![#$x:term,                 &$y:term               ]) => `(“ #$x                 = &$y     ”)
  | `($_ op(=) ![#$x:term,                 ↑$m:num                ]) => `(“ #$x                 = $m:num  ”)
  | `($_ op(=) ![#$x:term,                 $u                     ]) => `(“ #$x                 = !!$u    ”)
  | `($_ op(=) ![&$x:term,                 ‘ $u:first_order_term ’]) => `(“ &$x                 = $u      ”)
  | `($_ op(=) ![&$x:term,                 #$y:term               ]) => `(“ &$x                 = #$y     ”)
  | `($_ op(=) ![&$x:term,                 &$y:term               ]) => `(“ &$x                 = &$y     ”)
  | `($_ op(=) ![&$x:term,                 ↑$m:num                ]) => `(“ &$x                 = $m:num  ”)
  | `($_ op(=) ![&$x:term,                 $u                     ]) => `(“ &$x                 = !!$u    ”)
  | `($_ op(=) ![↑$n:num,                  ‘ $u:first_order_term ’]) => `(“ $n:num              = $u      ”)
  | `($_ op(=) ![↑$n:num,                  #$y:term               ]) => `(“ $n:num              = #$y     ”)
  | `($_ op(=) ![↑$n:num,                  &$y:term               ]) => `(“ $n:num              = &$y     ”)
  | `($_ op(=) ![↑$n:num,                  ↑$m:num                ]) => `(“ $n:num              = $m:num  ”)
  | `($_ op(=) ![↑$n:num,                  $u                     ]) => `(“ $n:num              = !!$u    ”)
  | `($_ op(=) ![$t:term,                  ‘ $u:first_order_term ’]) => `(“ !!$t                = $u      ”)
  | `($_ op(=) ![$t:term,                  #$y:term               ]) => `(“ !!$t                = #$y     ”)
  | `($_ op(=) ![$t:term,                  &$y:term               ]) => `(“ !!$t                = &$y     ”)
  | `($_ op(=) ![$t:term,                  ↑$m:num                ]) => `(“ !!$t                = $m:num  ”)
  | `($_ op(=) ![$t:term,                  $u                     ]) => `(“ !!$t                = !!$u    ”)

  | `($_ op(<) ![‘ $t:first_order_term ’,  ‘ $u:first_order_term ’]) => `(“ $t:first_order_term < $u      ”)
  | `($_ op(<) ![‘ $t:first_order_term ’,  #$y:term               ]) => `(“ $t:first_order_term < #$y     ”)
  | `($_ op(<) ![‘ $t:first_order_term ’,  &$y:term               ]) => `(“ $t:first_order_term < &$y     ”)
  | `($_ op(<) ![‘ $t:first_order_term ’,  ↑$m:num                ]) => `(“ $t:first_order_term < $m:num  ”)
  | `($_ op(<) ![‘ $t:first_order_term ’,  $u                     ]) => `(“ $t:first_order_term < !!$u    ”)
  | `($_ op(<) ![#$x:term,                 ‘ $u:first_order_term ’]) => `(“ #$x                 < $u      ”)
  | `($_ op(<) ![#$x:term,                 #$y:term               ]) => `(“ #$x                 < #$y     ”)
  | `($_ op(<) ![#$x:term,                 &$y:term               ]) => `(“ #$x                 < &$y     ”)
  | `($_ op(<) ![#$x:term,                 ↑$m:num                ]) => `(“ #$x                 < $m:num  ”)
  | `($_ op(<) ![#$x:term,                 $u                     ]) => `(“ #$x                 < !!$u    ”)
  | `($_ op(<) ![&$x:term,                 ‘ $u:first_order_term ’]) => `(“ &$x                 < $u      ”)
  | `($_ op(<) ![&$x:term,                 #$y:term               ]) => `(“ &$x                 < #$y     ”)
  | `($_ op(<) ![&$x:term,                 &$y:term               ]) => `(“ &$x                 < &$y     ”)
  | `($_ op(<) ![&$x:term,                 ↑$m:num                ]) => `(“ &$x                 < $m:num  ”)
  | `($_ op(<) ![&$x:term,                 $u                     ]) => `(“ &$x                 < !!$u    ”)
  | `($_ op(<) ![↑$n:num,                  ‘ $u:first_order_term ’]) => `(“ $n:num              < $u      ”)
  | `($_ op(<) ![↑$n:num,                  #$y:term               ]) => `(“ $n:num              < #$y     ”)
  | `($_ op(<) ![↑$n:num,                  &$y:term               ]) => `(“ $n:num              < &$y     ”)
  | `($_ op(<) ![↑$n:num,                  ↑$m:num                ]) => `(“ $n:num              < $m:num  ”)
  | `($_ op(<) ![↑$n:num,                  $u                     ]) => `(“ $n:num              < !!$u    ”)
  | `($_ op(<) ![$t:term,                  ‘ $u:first_order_term ’]) => `(“ !!$t                < $u      ”)
  | `($_ op(<) ![$t:term,                  #$y:term               ]) => `(“ !!$t                < #$y     ”)
  | `($_ op(<) ![$t:term,                  &$y:term               ]) => `(“ !!$t                < &$y     ”)
  | `($_ op(<) ![$t:term,                  ↑$m:num                ]) => `(“ !!$t                < $m:num  ”)
  | `($_ op(<) ![$t:term,                  $u                     ]) => `(“ !!$t                < !!$u    ”)

  | `($_ op(≤) ![‘ $t:first_order_term ’,  ‘ $u:first_order_term ’]) => `(“ $t:first_order_term ≤ $u      ”)
  | `($_ op(≤) ![‘ $t:first_order_term ’,  #$y:term               ]) => `(“ $t:first_order_term ≤ #$y     ”)
  | `($_ op(≤) ![‘ $t:first_order_term ’,  &$y:term               ]) => `(“ $t:first_order_term ≤ &$y     ”)
  | `($_ op(≤) ![‘ $t:first_order_term ’,  ↑$m:num                ]) => `(“ $t:first_order_term ≤ $m:num  ”)
  | `($_ op(≤) ![‘ $t:first_order_term ’,  $u                     ]) => `(“ $t:first_order_term ≤ !!$u    ”)
  | `($_ op(≤) ![#$x:term,                 ‘ $u:first_order_term ’]) => `(“ #$x                 ≤ $u      ”)
  | `($_ op(≤) ![#$x:term,                 #$y:term               ]) => `(“ #$x                 ≤ #$y     ”)
  | `($_ op(≤) ![#$x:term,                 &$y:term               ]) => `(“ #$x                 ≤ &$y     ”)
  | `($_ op(≤) ![#$x:term,                 ↑$m:num                ]) => `(“ #$x                 ≤ $m:num  ”)
  | `($_ op(≤) ![#$x:term,                 $u                     ]) => `(“ #$x                 ≤ !!$u    ”)
  | `($_ op(≤) ![&$x:term,                 ‘ $u:first_order_term ’]) => `(“ &$x                 ≤ $u      ”)
  | `($_ op(≤) ![&$x:term,                 #$y:term               ]) => `(“ &$x                 ≤ #$y     ”)
  | `($_ op(≤) ![&$x:term,                 &$y:term               ]) => `(“ &$x                 ≤ &$y     ”)
  | `($_ op(≤) ![&$x:term,                 ↑$m:num                ]) => `(“ &$x                 ≤ $m:num  ”)
  | `($_ op(≤) ![&$x:term,                 $u                     ]) => `(“ &$x                 ≤ !!$u    ”)
  | `($_ op(≤) ![↑$n:num,                  ‘ $u:first_order_term ’]) => `(“ $n:num              ≤ $u      ”)
  | `($_ op(≤) ![↑$n:num,                  #$y:term               ]) => `(“ $n:num              ≤ #$y     ”)
  | `($_ op(≤) ![↑$n:num,                  &$y:term               ]) => `(“ $n:num              ≤ &$y     ”)
  | `($_ op(≤) ![↑$n:num,                  ↑$m:num                ]) => `(“ $n:num              ≤ $m:num  ”)
  | `($_ op(≤) ![↑$n:num,                  $u                     ]) => `(“ $n:num              ≤ !!$u    ”)
  | `($_ op(≤) ![$t:term,                  ‘ $u:first_order_term ’]) => `(“ !!$t                ≤ $u      ”)
  | `($_ op(≤) ![$t:term,                  #$y:term               ]) => `(“ !!$t                ≤ #$y     ”)
  | `($_ op(≤) ![$t:term,                  &$y:term               ]) => `(“ !!$t                ≤ &$y     ”)
  | `($_ op(≤) ![$t:term,                  ↑$m:num                ]) => `(“ !!$t                ≤ $m:num  ”)
  | `($_ op(≤) ![$t:term,                  $u                     ]) => `(“ !!$t                ≤ !!$u    ”)

  | `($_ op(∈) ![‘ $t:first_order_term ’,  ‘ $u:first_order_term ’]) => `(“ $t:first_order_term ∈ $u      ”)
  | `($_ op(∈) ![‘ $t:first_order_term ’,  #$y:term               ]) => `(“ $t:first_order_term ∈ #$y     ”)
  | `($_ op(∈) ![‘ $t:first_order_term ’,  &$y:term               ]) => `(“ $t:first_order_term ∈ &$y     ”)
  | `($_ op(∈) ![‘ $t:first_order_term ’,  ↑$m:num                ]) => `(“ $t:first_order_term ∈ $m:num  ”)
  | `($_ op(∈) ![‘ $t:first_order_term ’,  $u                     ]) => `(“ $t:first_order_term ∈ !!$u    ”)
  | `($_ op(∈) ![#$x:term,                 ‘ $u:first_order_term ’]) => `(“ #$x                 ∈ $u      ”)
  | `($_ op(∈) ![#$x:term,                 #$y:term               ]) => `(“ #$x                 ∈ #$y     ”)
  | `($_ op(∈) ![#$x:term,                 &$y:term               ]) => `(“ #$x                 ∈ &$y     ”)
  | `($_ op(∈) ![#$x:term,                 ↑$m:num                ]) => `(“ #$x                 ∈ $m:num  ”)
  | `($_ op(∈) ![#$x:term,                 $u                     ]) => `(“ #$x                 ∈ !!$u    ”)
  | `($_ op(∈) ![&$x:term,                 ‘ $u:first_order_term ’]) => `(“ &$x                 ∈ $u      ”)
  | `($_ op(∈) ![&$x:term,                 #$y:term               ]) => `(“ &$x                 ∈ #$y     ”)
  | `($_ op(∈) ![&$x:term,                 &$y:term               ]) => `(“ &$x                 ∈ &$y     ”)
  | `($_ op(∈) ![&$x:term,                 ↑$m:num                ]) => `(“ &$x                 ∈ $m:num  ”)
  | `($_ op(∈) ![&$x:term,                 $u                     ]) => `(“ &$x                 ∈ !!$u    ”)
  | `($_ op(∈) ![↑$n:num,                  ‘ $u:first_order_term ’]) => `(“ $n:num              ∈ $u      ”)
  | `($_ op(∈) ![↑$n:num,                  #$y:term               ]) => `(“ $n:num              ∈ #$y     ”)
  | `($_ op(∈) ![↑$n:num,                  &$y:term               ]) => `(“ $n:num              ∈ &$y     ”)
  | `($_ op(∈) ![↑$n:num,                  ↑$m:num                ]) => `(“ $n:num              ∈ $m:num  ”)
  | `($_ op(∈) ![↑$n:num,                  $u                     ]) => `(“ $n:num              ∈ !!$u    ”)
  | `($_ op(∈) ![$t:term,                  ‘ $u:first_order_term ’]) => `(“ !!$t                ∈ $u      ”)
  | `($_ op(∈) ![$t:term,                  #$y:term               ]) => `(“ !!$t                ∈ #$y     ”)
  | `($_ op(∈) ![$t:term,                  &$y:term               ]) => `(“ !!$t                ∈ &$y     ”)
  | `($_ op(∈) ![$t:term,                  ↑$m:num                ]) => `(“ !!$t                ∈ $m:num  ”)
  | `($_ op(∈) ![$t:term,                  $u                     ]) => `(“ !!$t                ∈ !!$u    ”)

  | _                                                            => throw ()


-- @@ L692-692 verbatim
#check “x y z. ∃ v w, ∀ r < z + v, y + v ≤ x ↔ z = w”

-- @@ L693-693 verbatim
#check “x y | x = y → y = x”

-- @@ L694-694 verbatim
#check “x y . x = y → 4 * y = 3”

-- @@ L695-695 verbatim
#check “∀ x y, x = y → y = x”


-- @@ L697-697 verbatim
end delab


-- @@ L699-699 verbatim
/-! ### Notation for formula as term -/


-- @@ L701-712 verbatim
macro_rules
  | `(⤫formula(faf)[ $binders* | $fbinders* | !$φ:term $vs:first_order_term*   ]) => do
    let Ψ ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) fun a s ↦ do
      let x : TSyntax `ident ← TSyntax.freshIdent
      `(⤫term(faf)[ $x $binders* | $fbinders* | $a ] :> $s)
    `(($φ).nestFormulae $Ψ)
  | `(⤫formula(faf)[ $binders* | $fbinders* | !$φ:term $vs:first_order_term* ⋯ ]) => do
    let length := Syntax.mkNumLit (toString binders.size)
    let Ψ ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ #(finSuccItr x $length))) fun a s ↦ do
      let x : TSyntax `ident ← TSyntax.freshIdent
      `(⤫term(faf)[ $x $binders* | $fbinders* | $a] :> $s)
    `(($φ).nestFormulae $Ψ)


-- @@ L714-734 verbatim
macro_rules
  | `(⤫term(faf)[ $binders* | $fbinders* | $x:ident                         ]) => do
    match binders.idxOf? x with
    | none =>
      match fbinders.idxOf? x with
      | none => Macro.throwErrorAt x "error: variable does not appeared."
      | some x =>
        let i := Syntax.mkNumLit (toString x)
        `(“#0 = &$i”)
    | some x =>
      let i := Syntax.mkNumLit (toString x)
      `(“#0 = #$i”)
  | `(⤫term(faf)[ $binders* | $fbinders* | !$f:term $vs:first_order_term*   ]) => do
    let Ψ ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(![])) fun a s ↦ do
      `(⤫term(faf)[ $binders* | $fbinders* | $a ] :> $s)
    `(($f).nestFormulaeFunc $Ψ)
  | `(⤫term(faf)[ $binders* | $fbinders* | !$f:term $vs:first_order_term* ⋯ ]) => do
    let length := Syntax.mkNumLit (toString binders.size)
    let Ψ ← vs.foldrM (β := Lean.TSyntax _) (init := ← `(fun x ↦ “#0 = #(finSuccItr x $length)”)) fun a s ↦ do
      `(⤫term(faf)[ $binders* | $fbinders* | $a] :> $s)
    `(($f).nestFormulaeFunc $Ψ)


-- @@ L736-768 verbatim
macro_rules
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t:first_order_term = $u:first_order_term ]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    `(∀¹ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t ] 🡒 ∀¹ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] 🡒 “#1 = #0”)))
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t:first_order_term ≠ $u:first_order_term ]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    `(∀¹ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t ] 🡒 ∀¹ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] 🡒 “#1 ≠ #0”)))
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t:first_order_term < $u:first_order_term ]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    `(∀¹ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t ] 🡒 ∀¹ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] 🡒 “#1 < #0”)))
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t:first_order_term ≮ $u:first_order_term ]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    `(∀¹ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t ] 🡒 ∀¹ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] 🡒 “#1 ≮ #0”)))
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t:first_order_term ≤ $u:first_order_term ]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    `(∀¹ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t ] 🡒 ∀¹ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] 🡒 “#1 ≤ #0”)))
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t:first_order_term ≰ $u:first_order_term ]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    `(∀¹ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t ] 🡒 ∀¹ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] 🡒 “#1 ≰ #0”)))
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t:first_order_term ∈ $u:first_order_term ]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    `(∀¹ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t ] 🡒 ∀¹ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] 🡒 “#1 ∈ #0”)))
  | `(⤫formula(faf)[ $binders* | $fbinders* | $t:first_order_term ∉ $u:first_order_term ]) => do
    let x₁ : TSyntax `ident ← TSyntax.freshIdent
    let x₂ : TSyntax `ident ← TSyntax.freshIdent
    `(∀¹ (⤫term(faf)[ $x₁ $binders* | $fbinders* | $t ] 🡒 ∀¹ (⤫term(faf)[ $x₁ $x₂ $binders* | $fbinders* | $u ] 🡒 “#1 ∉ #0”)))


-- @@ L770-794 verbatim
macro_rules
  | `(⤫formula(faf)[ $binders* | $fbinders* | ∀ $x < $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
      let vt : TSyntax `ident ← TSyntax.freshIdent
      `(∀¹ (⤫term(faf)[ $vt $binders* | $fbinders* | $t ] 🡒 Semiformula.ballLT #0 ⤫formula(faf)[ $x $vt $binders* | $fbinders* | $φ ]))
  | `(⤫formula(faf)[ $binders* | $fbinders* | ∀ $x ≤ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
      let vt : TSyntax `ident ← TSyntax.freshIdent
      `(∀¹ (⤫term(faf)[ $vt $binders* | $fbinders* | $t ] 🡒 Semiformula.ballLE #0 ⤫formula(faf)[ $x $binders* | $fbinders* | $φ ]))
  | `(⤫formula(faf)[ $binders* | $fbinders* | ∀ $x ∈ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
      let vt : TSyntax `ident ← TSyntax.freshIdent
      `(∀¹ (⤫term(faf)[ $vt $binders* | $fbinders* | $t ] 🡒 Semiformula.ballMem #0 ⤫formula(faf)[ $x $vt $binders* | $fbinders* | $φ ]))
  | `(⤫formula(faf)[ $binders* | $fbinders* | ∃ $x < $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
      let vt : TSyntax `ident ← TSyntax.freshIdent
      `(∀¹ (⤫term(faf)[ $vt $binders* | $fbinders* | $t ] 🡒 Semiformula.bexsLT #0 ⤫formula(faf)[ $x $vt $binders* | $fbinders* | $φ ]))
  | `(⤫formula(faf)[ $binders* | $fbinders* | ∃ $x ≤ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
      let vt : TSyntax `ident ← TSyntax.freshIdent
      `(∀¹ (⤫term(faf)[ $vt $binders* | $fbinders* | $t ] 🡒 Semiformula.bexsLE #0 ⤫formula(faf)[ $x $vt $binders* | $fbinders* | $φ ]))
  | `(⤫formula(faf)[ $binders* | $fbinders* | ∃ $x ∈ $t, $φ ]) => do
    if binders.elem x then Macro.throwErrorAt x "error: variable is duplicated." else
      let vt : TSyntax `ident ← TSyntax.freshIdent
      `(∀¹ (⤫term(faf)[ $vt $binders* | $fbinders* | $t ] 🡒 Semiformula.bexsMem #0 ⤫formula(faf)[ $x $vt $binders* | $fbinders* | $φ ]))


-- @@ L796-796 verbatim
syntax "f‘" first_order_term:0 "’" : term

-- @@ L797-797 verbatim
syntax "f‘" ident* "| " first_order_term:0 "’" : term

-- @@ L798-798 verbatim
syntax "f‘" ident* ". " first_order_term:0 "’" : term


-- @@ L800-803 verbatim
macro_rules
  | `(f‘ $e:first_order_term ’)              => `(⤫term(faf)[           |            | $e ])
  | `(f‘ $fbinders* | $e:first_order_term ’) => `(⤫term(faf)[           | $fbinders* | $e ])
  | `(f‘ $binders*. $e:first_order_term ’)   => `(⤫term(faf)[ $binders* |            | $e ])


-- @@ L805-805 verbatim
#check f‘a x. x’


-- @@ L807-807 verbatim
syntax "f“" ident* "| "  first_order_formula:0 "”" : term

-- @@ L808-808 verbatim
syntax "f“" ident* ". "  first_order_formula:0 "”" : term

-- @@ L809-809 verbatim
syntax "f“" first_order_formula:0 "”" : term


-- @@ L811-815 verbatim
/-- A formula in formula-as-function notation. Use `f“⋯. ⋯”` for bound variables, and `f“⋯ | ⋯”` for free variables. -/
macro_rules
  | `(f“ $e:first_order_formula ”)              => `(⤫formula(faf)[           |            | $e ])
  | `(f“ $fbinders* | $e:first_order_formula ”) => `(⤫formula(faf)[           | $fbinders* | $e ])
  | `(f“ $binders*. $e:first_order_formula ”)   => `(⤫formula(faf)[ $binders* |            | $e ])


-- @@ L817-845 verbatim
#check f“x y. x = y”

/-
variable {L : Language} [L.Eq] [L.Mem]

def func : Semisentence L 3 := sorry

def rel : Semisentence L 2 := sorry

def sent : Semisentence L 3 := f“F X Y. ∀ f, f ∈ F ↔ f ∈ !func X Y”

def sent₂ : Semisentence L 3 := f“F X Y. ∀ f, f ∈ F”

variable {M : Type*} [Membership M M] [s : Structure L M] [Structure.Eq L M] [Structure.Mem L M]

def Func : M → M → M := sorry

def Rel : M → M → Prop := sorry

@[simp] lemma eval_func : M ⊧/![x, y, z] (func : Semisentence L 3) ↔ x = Func y z := sorry

@[simp] lemma eval_rel : M ⊧/![x, y] (rel : Semisentence L 2) ↔ Rel x y := sorry

lemma egegege : M ⊧/![x, y, z] (f“x y z. ∀ w ∈ x, w ∈ z” : Semisentence L 3) := by {

  simp

 }
-/


-- @@ L847-847 verbatim
end BinderNotation


-- @@ L849-849 verbatim
end FFL.FirstOrder


-- @@ L851-851 verbatim
end
