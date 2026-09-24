/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Devon Tuma
-/
module

public import PolyFun.Control.Monad.Hom
public import PolyFun.PFunctor.Basic
public import PolyFun.PFunctor.Lens.Basic
public import Cslib.Foundations.Data.PFunctor.Free


-- @@ L13-18 verbatim
/-!
# Free Monad of a Polynomial Functor

We define the free monad on a **polynomial functor** (`PFunctor`), and prove some basic properties.

-/


-- @@ L20-20 verbatim
@[expose] public section


-- @@ L22-30 verbatim
/--
Simp set for structurally unfolding `FreeM` and displayed-family operations.

This set is reserved for one-way unfolding lemmas: constructor equations for
`FreeM` operations, displayed-family operations, and local-hom recursion through
`liftBind`. Folding and normalization lemmas should not be tagged with this
attribute.
-/
register_simp_attr freeM_unfold


-- @@ L32-32 verbatim
universe u v uA uB uA₂ uB₂ uA₃ uB₃ uδ uβ uγ


-- @@ L34-34 verbatim
namespace PFunctor


-- @@ L36-36 verbatim
namespace FreeM


-- @@ L38-38 verbatim
variable {P : PFunctor.{uA, uB}} {α β γ : Type v}


-- @@ L40-40 verbatim
/-! ## Public constructor equations -/


-- @@ L42-47 verbatim
/-- Mapping a value through a leaf is visible through an ordinary module import,
with the leaf written using the public `Pure` operation. -/
@[simp]
theorem map_pure {X : Type uβ} {Y : Type uγ} (f : X → Y) (x : X) :
    FreeM.map (P := P) f (pure x : FreeM P X) = (pure (f x) : FreeM P Y) :=
  rfl


-- @@ L49-55 verbatim
/-- Mapping a value through a query preserves its position and maps every
continuation. -/
theorem map_liftBind {X : Type uβ} {Y : Type uγ} (f : X → Y)
    (a : P.A) (rest : P.B a → FreeM P X) :
    FreeM.map f (FreeM.liftBind a rest) =
      FreeM.liftBind a (fun direction ↦ FreeM.map f (rest direction)) :=
  rfl


-- @@ L57-63 verbatim
/-- Mapping through a query written as `lift` followed by `bind` maps every
continuation without requiring clients to expose `liftBind`. -/
theorem map_lift_bind {X : Type uβ} {Y : Type uγ} (f : X → Y)
    (a : P.A) (rest : P.B a → FreeM P X) :
    FreeM.map f ((FreeM.lift a).bind rest) =
      (FreeM.lift a).bind (fun direction ↦ FreeM.map f (rest direction)) :=
  rfl


-- @@ L65-65 verbatim
/-! ## Fixed-point presentation -/


-- @@ L67-73 verbatim
/-- Reinterpret a finite free program as the W-type of query-or-return
nodes. Query nodes are the left summand and return nodes are nullary nodes in
the constant right summand. -/
def toWWithReturn : FreeM P α → (P + C.{v, uB} α).W
  | .pure value => ⟨Sum.inr value, PEmpty.elim⟩
  | .liftBind position next =>
      ⟨Sum.inl position, fun direction => toWWithReturn (next direction)⟩


-- @@ L75-79 verbatim
/-- Decode the query-or-return W-type as a finite free program. -/
def ofWWithReturn : (P + C.{v, uB} α).W → FreeM P α
  | ⟨Sum.inl position, next⟩ =>
      FreeM.liftBind position fun direction => ofWWithReturn (next direction)
  | ⟨Sum.inr value, _⟩ => FreeM.pure value


-- @@ L81-84 verbatim
@[simp] theorem toWWithReturn_pure (value : α) :
    toWWithReturn (pure value : FreeM P α) =
      WType.mk (Sum.inr value) PEmpty.elim :=
  rfl


-- @@ L86-91 verbatim
theorem toWWithReturn_liftBind (position : P.A)
    (next : P.B position → FreeM P α) :
    toWWithReturn (FreeM.liftBind position next) =
      WType.mk (Sum.inl position) fun direction =>
        toWWithReturn (next direction) :=
  rfl


-- @@ L93-96 verbatim
@[simp] theorem ofWWithReturn_return (value : α)
    (next : PEmpty → (P + C.{v, uB} α).W) :
    ofWWithReturn (WType.mk (Sum.inr value) next) = FreeM.pure value :=
  rfl


-- @@ L98-102 verbatim
@[simp] theorem ofWWithReturn_query (position : P.A)
    (next : P.B position → (P + C.{v, uB} α).W) :
    ofWWithReturn (WType.mk (Sum.inl position) next) =
      FreeM.liftBind position fun direction => ofWWithReturn (next direction) :=
  rfl


-- @@ L104-122 verbatim
/-- `FreeM P α` is the initial algebra, or W-type, for the polynomial
`P + C α`. -/
def equivWWithReturn : FreeM P α ≃ (P + C.{v, uB} α).W where
  toFun := toWWithReturn
  invFun := ofWWithReturn
  left_inv program := by
    induction program with
    | pure value => rfl
    | lift_bind position next ih =>
        exact congrArg (FreeM.liftBind position) (funext ih)
  right_inv tree := by
    induction tree with
    | mk shape next ih =>
        cases shape with
        | inl position =>
            exact congrArg (WType.mk (Sum.inl position)) (funext ih)
        | inr value =>
            exact congrArg (WType.mk (Sum.inr value))
              (funext fun direction => direction.elim)


-- @@ L124-133 verbatim
/-- Test only the root of a free polynomial tree.

A leaf demands `leafPred` of its result, while an internal node demands
`positionPred` of its exposed position. This deliberately does not recurse
into the continuations; callers can quantify over paths or cursors when they
need a whole-tree property. -/
def RootSatisfies (positionPred : P.A → Prop) (leafPred : α → Prop) :
    FreeM P α → Prop
  | .pure result => leafPred result
  | .liftBind position _ => positionPred position


-- @@ L135-140 verbatim
@[simp]
theorem rootSatisfies_pure (positionPred : P.A → Prop) (leafPred : α → Prop)
    (result : α) :
    RootSatisfies positionPred leafPred (pure result : FreeM P α) =
      leafPred result :=
  rfl


-- @@ L142-148 verbatim
@[simp]
theorem rootSatisfies_liftBind (positionPred : P.A → Prop) (leafPred : α → Prop)
    (position : P.A) (next : P.B position → FreeM P α) :
    RootSatisfies positionPred leafPred
        ((FreeM.lift (P := P) position).bind next) =
      positionPred position :=
  rfl


-- @@ L150-154 verbatim
/-- Forward direction of the equivalence with `P.W` when the leaf type is empty: every `pure`
case is unreachable, and every `liftBind` is reinterpreted as a W-node. -/
def toW [IsEmpty α] : FreeM P α → P.W
  | .pure y   => (IsEmpty.false y).elim
  | .liftBind a r => ⟨a, fun b => toW (r b)⟩


-- @@ L156-159 verbatim
/-- Inverse direction of the equivalence with `P.W` when the leaf type is empty: every W-node
becomes a `liftBind`. -/
def ofW [IsEmpty α] : P.W → FreeM P α
  | ⟨a, f⟩ => FreeM.liftBind a (fun b => ofW (f b))


-- @@ L161-175 verbatim
/-- When the value type is empty, every `pure` is unreachable and `FreeM P α` is structurally
identical to `P.W`. -/
def equivWOfIsEmpty [IsEmpty α] : FreeM P α ≃ P.W where
  toFun := toW
  invFun := ofW
  left_inv x := by
    induction x with
    | pure y => exact (IsEmpty.false y).elim
    | lift_bind a r ih => exact congrArg (FreeM.liftBind a) (funext ih)
  right_inv w := by
    induction w with
    | mk a f ih => exact congrArg (WType.mk a) (funext ih)

lemma monad_bind_def (x : FreeM P α) (g : α → FreeM P β) :
    x >>= g = FreeM.bind x g := rfl


-- @@ L177-183 verbatim
/-- Mapping after a free-monad bind can be moved into each continuation. -/
theorem bind_map_right {δ : Type uδ} {β : Type uβ} {γ : Type uγ}
    (mx : FreeM P δ) (g : δ → FreeM P β) (f : β → γ) :
    FreeM.bind mx (fun x => FreeM.map f (g x)) =
      FreeM.map f (FreeM.bind mx g) := by
  simpa only [FreeM.bind_pure_comp] using
    (FreeM.bind_assoc mx g (pure ∘ f)).symm


-- @@ L185-190 verbatim
/-- Mapping after a free-monad bind distributes through its continuation. -/
theorem map_bind {δ : Type uδ} {β : Type uβ} {γ : Type uγ}
    (f : β → γ) (mx : FreeM P δ) (g : δ → FreeM P β) :
    FreeM.map f (FreeM.bind mx g) =
      FreeM.bind mx (fun x ↦ FreeM.map f (g x)) :=
  (bind_map_right mx g f).symm


-- @@ L192-192 verbatim
section mapLens


-- @@ L194-194 verbatim
variable {Q : PFunctor.{uA₂, uB₂}} {R : PFunctor.{uA₃, uB₃}}


-- @@ L196-207 verbatim
/-- Transport a free polynomial tree along a polynomial lens.

The source polynomial `P` is the abstract/control interface. The target
polynomial `Q` is the concrete/runtime interface. At each `P`-node, the lens
chooses a `Q`-position by `toFunA`; when runtime supplies a `Q`-direction,
`toFunB` maps it back to the corresponding `P`-direction selecting the
control continuation. -/
@[implicit_reducible]
protected def mapLens (l : Lens P Q) : FreeM P α → FreeM Q α
  | .pure x => .pure x
  | .liftBind a rest => .liftBind (l.toFunA a) fun d =>
      (rest (l.toFunB a d)).mapLens l


-- @@ L209-212 verbatim
@[simp]
theorem mapLens_pure (l : Lens P Q) (x : α) :
    (pure x : FreeM P α).mapLens l = FreeM.pure x :=
  rfl


-- @@ L214-220 verbatim
/-- Interface transport exposes the `liftBind` constructor without requiring
clients to unfold its compatibility presentation as `lift` followed by `bind`. -/
@[simp]
theorem mapLens_liftBind (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α) :
    (FreeM.liftBind a rest).mapLens l =
      FreeM.liftBind (l.toFunA a) (fun d ↦ (rest (l.toFunB a d)).mapLens l) :=
  rfl


-- @@ L222-225 verbatim
@[simp]
theorem mapLens_lift_bind (l : Lens P Q) (a : P.A) (rest : P.B a → FreeM P α) :
    ((FreeM.lift a).bind rest).mapLens l =
      FreeM.liftBind (l.toFunA a) (fun d => (rest (l.toFunB a d)).mapLens l) := rfl


-- @@ L227-232 verbatim
@[simp]
theorem mapLens_id (x : FreeM P α) :
    x.mapLens (Lens.id P) = x := by
  induction x with
  | pure _ => rfl
  | lift_bind a rest ih => exact congrArg (FreeM.liftBind a) (funext ih)


-- @@ L234-240 verbatim
@[simp]
theorem mapLens_comp (l₂ : Lens Q R) (l₁ : Lens P Q) (x : FreeM P α) :
    (x.mapLens l₁).mapLens l₂ = x.mapLens (l₂ ∘ₗ l₁) := by
  induction x with
  | pure _ => rfl
  | lift_bind a rest ih =>
      exact congrArg (FreeM.liftBind (l₂.toFunA (l₁.toFunA a))) (funext fun d => ih _)


-- @@ L242-247 verbatim
theorem mapLens_bind (l : Lens P Q) (x : FreeM P α) (f : α → FreeM P β) :
    (FreeM.bind x f).mapLens l =
      FreeM.bind (x.mapLens l) (fun a => (f a).mapLens l) := by
  induction x with
  | pure _ => rfl
  | lift_bind a rest ih => exact congrArg (FreeM.liftBind (l.toFunA a)) (funext fun d => ih _)


-- @@ L249-251 verbatim
@[simp]
theorem mapLens_bind' (l : Lens P Q) (x : FreeM P α) (f : α → FreeM P β) :
    (x >>= f).mapLens l = x.mapLens l >>= fun a => (f a).mapLens l := mapLens_bind l x f


-- @@ L253-253 verbatim
end mapLens


-- @@ L255-255 verbatim
section liftM


-- @@ L257-258 verbatim
variable {m : Type uB → Type v} {α : Type uB} [Monad m] [LawfulMonad m]
  (s : (a : P.A) → m (P.B a))


-- @@ L260-264 verbatim
/-- `FreeM.liftM` as a monad homomorphism. -/
protected def liftMHom (s : (a : P.A) → m (P.B a)) : FreeM P →ᵐ m where
  toFun _ x := x.liftM s
  toFun_pure' := FreeM.liftM_pure s
  toFun_bind' := FreeM.liftM_bind s


-- @@ L266-267 verbatim
@[simp] lemma liftMHom_toFun_eq (s : (a : P.A) → m (P.B a)) :
    ((FreeM.liftMHom s).toFun α) = fun x => x.liftM s := rfl


-- @@ L269-274 verbatim
/-- `FreeM.liftM` as a monad homomorphism, packaging the interpretation of
positions as a natural transformation `NatHom P.Obj m`. -/
protected def liftMHom' (s : NatHom P.Obj m) : FreeM P →ᵐ m where
  toFun _ x := x.liftM (fun t => s ⟨t, id⟩)
  toFun_pure' _ := rfl
  toFun_bind' x y := FreeM.liftM_bind _ x y


-- @@ L276-277 verbatim
@[simp] lemma liftMHom'_toFun_eq (s : NatHom P.Obj m) :
    (FreeM.liftMHom' s).toFun α = fun x => x.liftM (fun t => s ⟨t, id⟩) := rfl


-- @@ L279-286 verbatim
/-! ## Universal property and naturality of the fold

`FreeM.liftM s` is the universal fold: the *unique* monad homomorphism out of `FreeM P` extending a
handler `s` (`liftMHom_unique`), and it is *natural* in the target monad — post-composing with a
monad morphism `φ : m →ᵐ n` is the fold of the post-composed handler (`liftM_natural`,
`liftMHom_comp`). This is the freeness of `FreeM P`; downstream it lets a semantic monad morphism
(e.g. an evaluation-distribution map) be pushed through a fold uniformly, rather than re-run by
induction per interpretation. -/


-- @@ L288-288 verbatim
variable {n : Type uB → Type u} [Monad n] [LawfulMonad n]


-- @@ L290-303 verbatim
/-- **Universal property of `FreeM.liftM`** (freeness of `FreeM P`): a monad homomorphism out of
`FreeM P` is determined by its action on generators. If `F : FreeM P →ᵐ m` agrees with `s` on every
`FreeM.lift a`, then `F = FreeM.liftMHom s`. So handlers `(a : P.A) → m (P.B a)` are in bijection
with monad homomorphisms `FreeM P →ᵐ m` — the universal property behind `simulateQ`. -/
theorem liftMHom_unique (F : FreeM P →ᵐ m) (h : ∀ a, F (FreeM.lift a) = s a) :
    F = FreeM.liftMHom s := by
  refine MonadHom.ext' fun β x => ?_
  induction x with
  | pure x => exact F.mmap_pure x
  | lift_bind a r ih =>
    change F (FreeM.liftBind a r) = FreeM.liftM s (FreeM.liftBind a r)
    rw [show (FreeM.liftBind a r : FreeM P β) = FreeM.lift a >>= r from rfl,
      MonadHom.mmap_bind, h, FreeM.liftM_lift_bind]
    exact bind_congr ih


-- @@ L305-313 verbatim
omit [LawfulMonad m] [LawfulMonad n] in
/-- **Naturality of the fold along a monad morphism**: pushing a monad morphism `φ : m →ᵐ n` through
`FreeM.liftM s` is the fold of the post-composed handler `fun a => φ (s a)` — the value-level
naturality square of the universal fold. -/
@[simp] theorem liftM_natural (φ : m →ᵐ n) (x : FreeM P α) :
    φ (FreeM.liftM s x) = FreeM.liftM (fun a => φ (s a)) x := by
  induction x with
  | pure x => exact φ.mmap_pure x
  | lift_bind a r ih => simp [ih]


-- @@ L315-319 verbatim
/-- Bundled form of `liftM_natural`: composing the fold monad-homomorphism `FreeM.liftMHom s` with
a monad morphism `φ` is the fold of the post-composed handler. -/
theorem liftMHom_comp (φ : m →ᵐ n) :
    φ ∘ₘ FreeM.liftMHom s = FreeM.liftMHom (fun a => φ (s a)) :=
  MonadHom.ext' fun β x => by simp


-- @@ L321-321 verbatim
end liftM


-- @@ L323-323 verbatim
section stateNaturality


-- @@ L325-326 verbatim
variable {m : Type uB → Type v} {n : Type uB → Type u} [Monad m] [Monad n] {σ : Type uB}
  {α : Type uB}


-- @@ L328-337 verbatim
/-- **Stateful naturality of the fold**: running a fold whose stateful handler is post-composed by
a `StateT`-lifted monad morphism `StateT.mapHom φ` is `φ` applied to the run of the original fold —
the shape a `StateT`-threaded semantic morphism (e.g. an evaluation-distribution map through a
stateful handler) instantiates, collapsing a per-interpretation induction to one use of
`liftM_natural`. -/
theorem run_liftM_mapHom (φ : m →ᵐ n) (impl : (a : P.A) → StateT σ m (P.B a))
    (x : FreeM P α) (s : σ) :
    (FreeM.liftM (fun a => StateT.mapHom φ (impl a)) x).run s =
      φ ((FreeM.liftM impl x).run s) := by
  rw [← liftM_natural impl (StateT.mapHom φ) x, StateT.run_mapHom]


-- @@ L339-339 verbatim
end stateNaturality


-- @@ L341-341 verbatim
section idFold


-- @@ L343-343 verbatim
variable {α : Type uB}


-- @@ L345-352 verbatim
/-- The fold with the canonical re-lifting handler `FreeM.lift` is the identity: interpreting each
position back into the free monad recovers the tree (equivalently `FreeM.liftMHom FreeM.lift` is
the identity homomorphism, `liftMHom_lift_eq_id`). The upstream form of `simulateQ` of the
identity handler being the identity — a corollary of the universal property. -/
@[simp] theorem liftM_lift_eq_self (x : FreeM P α) : FreeM.liftM FreeM.lift x = x := by
  induction x with
  | pure y => rfl
  | lift_bind a r ih => simp [ih]


-- @@ L354-356 verbatim
theorem liftMHom_lift_eq_id :
    FreeM.liftMHom (P := P) (m := FreeM P) FreeM.lift = MonadHom.id (FreeM P) :=
  MonadHom.ext' fun _ x => by simp


-- @@ L358-376 verbatim
/-- Interpreting a free tree by a free handler and then interpreting the
resulting free tree by an arbitrary monadic handler is the same as interpreting
once by their pointwise Kleisli composite. -/
theorem liftM_comp {Q : PFunctor.{uA₂, uB}} {m : Type uB → Type v}
    [Monad m] [LawfulMonad m]
    (x : FreeM P α)
    (first : (a : P.A) → FreeM Q (P.B a))
    (second : (a : Q.A) → m (Q.B a)) :
    (x.liftM first).liftM second =
      x.liftM (fun a => (first a).liftM second) := by
  induction x with
  | pure _ => rfl
  | lift_bind a rest ih =>
      change
        ((first a >>= fun b => (rest b).liftM first).liftM second) =
          (first a).liftM second >>= fun b =>
            (rest b).liftM (fun a => (first a).liftM second)
      rw [FreeM.liftM_bind]
      exact congrArg (fun k => (first a).liftM second >>= k) (funext ih)


-- @@ L378-378 verbatim
end idFold


-- @@ L380-380 verbatim
end FreeM


-- @@ L382-382 verbatim
end PFunctor
