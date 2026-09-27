/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import LeanPool.QuasiBorelSpaces.Hom
public import LeanPool.QuasiBorelSpaces.Pi
public import LeanPool.QuasiBorelSpaces.Subtype
public import LeanPool.QuasiBorelSpaces.Basic


-- @@ L13-17 verbatim
/-!
# LeanPool.QuasiBorelSpaces.Functor

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Functor`.
-/


-- @@ L19-19 verbatim
@[expose] public section


-- @@ L21-21 verbatim
namespace QuasiBorelSpace


-- @@ L23-39 expanded
/-- A `QuasiBorelSpace` `Functor` is a function `F : Type → Type` such that:
-/
class Functor (F : ∀ A [QuasiBorelSpace A], Type*) where
  /-- 1. `F` maps `QuasiBorelSpace`s to `QuasiBorelSpace`s. -/
  [quasiBorelSpace {A} [QuasiBorelSpace A] : QuasiBorelSpace (F A)]
  /-- 2. There is a mapping from morphisms to morphisms. -/
  map {A B} [QuasiBorelSpace A] [QuasiBorelSpace B] :
    (QuasiBorelHom A B) → (QuasiBorelHom (F A) (F B))
  /-- 3. The mapping preserves the identity morphism. -/
  map_id {A} [QuasiBorelSpace A] : map (A := A) .id = .id
  /-- 4. The mapping distributes over composition. -/
  map_comp {A} [QuasiBorelSpace A] {B} [QuasiBorelSpace B] {C} [QuasiBorelSpace C]
    (f : QuasiBorelHom B C) (g : QuasiBorelHom A B) : (map f).comp (map g) = map (f.comp g)


-- @@ L41-44 verbatim
variable
  {A} [QuasiBorelSpace A]
  {B} [QuasiBorelSpace B]
  {C} [QuasiBorelSpace C]


-- @@ L46-46 verbatim
namespace Functor


-- @@ L48-48 verbatim
attribute [reducible, instance] Functor.quasiBorelSpace

-- @@ L49-49 verbatim
attribute [simp] Functor.map_id Functor.map_comp


-- @@ L51-60 expanded
@[simp]
lemma map_comp_coe {F} [Functor F] {A} [QuasiBorelSpace A] {B} [QuasiBorelSpace B] {C}
    [QuasiBorelSpace C] (f : QuasiBorelHom B C) (g : QuasiBorelHom A B) (x : F A) :
    map f (map g x) = map (f.comp g) x :=
  by
  have := congr_arg (DFunLike.coe · x) (Functor.map_comp (F := F) f g)
  simpa only [QuasiBorelHom.comp_coe] using this


-- @@ L62-62 verbatim
end Functor


-- @@ L64-69 expanded
/-- A `Sequence` is a sequence of types `S : ℕ → Type` such that: -/
class Sequence (S : ℕ → Type*) where
  /-- 1. Every `S n` is a `QuasiBorelSpace`. -/
  [quasiBorelSpace {n} : QuasiBorelSpace (S n)]
  /-- 2. There is a projection from each type to its predecessor. -/
  project (n) : QuasiBorelHom (S (n + 1)) (S n)


-- @@ L71-71 verbatim
attribute [reducible, instance] Sequence.quasiBorelSpace


-- @@ L73-77 verbatim
/-- The composition of a `Functor` with a `Sequence`. -/
structure Comp (F) [Functor F] (S) [Sequence S] (n : ℕ) where
  mk ::
  /-- The underlying element of `F (S n)`. -/
  get : F (S n)


-- @@ L79-79 verbatim
namespace Comp


-- @@ L81-81 verbatim
variable {F} [Functor F] {S} [Sequence S] {n}


-- @@ L83-85 verbatim
@[ext]
lemma ext {x y : Comp F S n} (h : x.get = y.get) : x = y := by
  cases x; cases y; simpa only [mk.injEq]


-- @@ L87-88 verbatim
instance : QuasiBorelSpace (Comp F S n) :=
  lift get


-- @@ L90-92 verbatim
@[fun_prop]
lemma isHom_mk : IsHom (mk (F := F) (S := S) (n := n)) := by
  simp only [isHom_to_lift, isHom_id']


-- @@ L94-96 verbatim
@[fun_prop]
lemma isHom_get : IsHom (get (F := F) (S := S) (n := n)) := by
  apply isHom_of_lift _


-- @@ L98-100 verbatim
@[simps project]
instance {F} [Functor F] {S} [Sequence S] : Sequence (Comp F S) where
  project n := .mk fun x ↦ mk (Functor.map (Sequence.project n) x.get)


-- @@ L102-102 verbatim
end Comp


-- @@ L104-109 verbatim
/-- The `Limit` of a `Sequence` `S` consists of: -/
structure Limit (S) [Sequence S] where
  /-- 1. A sequence of elements, one from each `S n`. -/
  toFun (n) : S n
  /-- 2. A proof that every element is the projection of its successor. -/
  property (n) : Sequence.project n (toFun (n + 1)) = toFun n


-- @@ L111-111 verbatim
namespace Limit


-- @@ L113-113 verbatim
variable {S} [Sequence S]


-- @@ L115-119 verbatim
instance : DFunLike (Limit S) ℕ S where
  coe := toFun
  coe_injective := by
    rintro ⟨f, _⟩ ⟨g, _⟩ h
    simpa only [mk.injEq] using h


-- @@ L121-121 verbatim
namespace Simps


-- @@ L123-124 verbatim
/-- A simps projection for function coercion. -/
def coe (f : Limit S) : ∀ n, S n := f


-- @@ L126-126 verbatim
end Simps


-- @@ L128-128 verbatim
initialize_simps_projections Limit (toFun → coe)


-- @@ L130-131 verbatim
@[ext]
lemma ext {f g : Limit S} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h


-- @@ L133-139 verbatim
/--
Copy of a `QuasiBorelHom` with a new `toFun` equal to the old one.
Useful to fix definitional equalities.
-/
protected def copy (f : Limit S) (f' : ∀ n, S n) (h : f' = ⇑f) : Limit S where
  toFun := f'
  property := h.symm ▸ f.property


-- @@ L141-142 verbatim
@[simp]
lemma coe_mk {f : ∀ n, S n} (hf : ∀ n, Sequence.project n (f (n + 1)) = f n) : ⇑(mk f hf) = f := rfl


-- @@ L144-145 verbatim
@[simp]
lemma eta (f : Limit S) : mk f f.property = f := rfl


-- @@ L147-148 verbatim
@[simp]
lemma toFun_eq_coe (f : Limit S) : toFun f = ⇑f := rfl


-- @@ L150-151 verbatim
@[simp]
lemma project_coe (n) (f : Limit S) : Sequence.project n (f (n + 1)) = f n := f.property n


-- @@ L153-156 verbatim
/-- View a sequence limit as a compatible family of coordinates. -/
def toSubtype {S} [Sequence S] (x : Limit S)
    : { f : ∀ n, S n // ∀ n, Sequence.project n (f (n + 1)) = f n } :=
  ⟨x.toFun, x.property⟩


-- @@ L158-159 verbatim
instance {S} [Sequence S] : QuasiBorelSpace (Limit S) :=
  lift toSubtype


-- @@ L161-166 verbatim
@[fun_prop]
lemma isHom_mk {S} [Sequence S]
    {f : A → ∀ n, S n} (hf₁ : IsHom f) (hf₂ : ∀ x n, Sequence.project n (f x (n + 1)) = f x n)
    : IsHom (fun x ↦ mk (f x) (hf₂ x)) := by
  simp only [isHom_to_lift, toSubtype, Pi.isHom_iff]
  fun_prop


-- @@ L168-175 verbatim
@[fun_prop]
lemma isHom_coe
    {S} [Sequence S] {f : A → Limit S} (hf : IsHom f) {n}
    : IsHom (fun x ↦ f x n) := by
  have : IsHom (toSubtype (S := S)) := isHom_of_lift _
  change IsHom (fun x ↦ (f x).toSubtype.val n)
  exact isHom_comp' (f := Function.eval n ∘ Subtype.val) (g := toSubtype ∘ f)
    (isHom_comp' (Pi.isHom_eval n) (Subtype.isHom_val isHom_id)) (by fun_prop)


-- @@ L177-177 verbatim
end Limit


-- @@ L179-179 verbatim
universe u


-- @@ L181-186 verbatim
/-- A type bundled with its quasi-Borel space structure. -/
structure Bundle : Type _ where
  /-- The underlying type of a bundled quasi-Borel space. -/
  Carrier : Type u
  /-- The quasi-Borel structure on the bundled carrier. -/
  [quasiBorelSpace : QuasiBorelSpace Carrier]


-- @@ L188-188 verbatim
attribute [local instance] Bundle.quasiBorelSpace


-- @@ L190-193 verbatim
/-- Iterate the functor starting at the one-point quasi-Borel space. -/
def Iter₀ (F) [Functor F] : ℕ → Bundle
  | 0 => .mk PUnit
  | n + 1 => .mk (F (Iter₀ F n).Carrier)


-- @@ L195-199 verbatim
/-- The `Sequence` obtained by iterating a `Functor`. -/
structure Iter (F) [Functor F] (n : ℕ) : Type* where
  mk ::
  /-- The underlying element at the `n`th iterate. -/
  get : (Iter₀ F n).Carrier


-- @@ L201-201 verbatim
variable {F} [Functor F]


-- @@ L203-203 verbatim
namespace Iter


-- @@ L205-206 verbatim
instance {n} : QuasiBorelSpace (Iter F n) :=
  lift get


-- @@ L208-210 verbatim
@[local fun_prop, simp]
lemma isHom_get {n} : IsHom (get (F := F) (n := n)) :=
  isHom_of_lift get


-- @@ L212-214 verbatim
@[local fun_prop, simp]
lemma isHom_mk {n} : IsHom (mk (F := F) (n := n)) := by
  simp only [isHom_to_lift, isHom_id']


-- @@ L216-217 expanded
/-- The underlying-value projection as a quasi-Borel homomorphism. -/
def getHom {n} : QuasiBorelHom (Iter F n) (Iter₀ F n).Carrier :=
  .mk get


-- @@ L219-220 expanded
/-- The wrapper constructor as a quasi-Borel homomorphism. -/
def mkHom {n} : QuasiBorelHom (Iter₀ F n).Carrier (Iter F n) :=
  .mk mk


-- @@ L222-225 verbatim
private lemma getHom_comp_mkHom {n} :
    (getHom (F := F) (n := n)).comp (mkHom (F := F) (n := n)) = .id := by
  ext
  rfl


-- @@ L227-230 verbatim
private lemma mkHom_comp_getHom {n} :
    (mkHom (F := F) (n := n)).comp (getHom (F := F) (n := n)) = .id := by
  ext
  rfl


-- @@ L232-233 verbatim
/-- Zero element constructor. -/
def zero : Iter F 0 := .mk ()


-- @@ L235-238 verbatim
instance : Subsingleton (Iter F 0) where
  allEq := by
    rintro ⟨⟩ ⟨⟩
    rfl


-- @@ L240-245 expanded
/-- Successor element constructor. -/
def succ {n} : QuasiBorelHom (F (Iter F n)) (Iter F (n + 1))
    where
  toFun x := { get := Functor.map getHom x }
  property := by
    apply isHom_comp isHom_mk
    apply QuasiBorelHom.isHom_coe


-- @@ L247-249 expanded
/-- Successor element destructor. -/
def unsucc {n} : QuasiBorelHom (Iter F (n + 1)) (F (Iter F n)) where
  toFun x := Functor.map mkHom x.get


-- @@ L251-257 verbatim
@[simp]
lemma succ_unsucc {n} (x : Iter F (n + 1)) : succ (unsucc x) = x := by
  rcases x with ⟨x⟩
  change F (Iter₀ F n).Carrier at x
  change (⟨Functor.map getHom (Functor.map mkHom x)⟩ : Iter F (n + 1)) = ⟨x⟩
  rw [Functor.map_comp_coe, getHom_comp_mkHom, Functor.map_id]
  rfl


-- @@ L259-263 verbatim
@[simp]
lemma unsucc_succ {n} (x : F (Iter F n)) : unsucc (succ x) = x := by
  change Functor.map mkHom (Functor.map getHom x) = x
  rw [Functor.map_comp_coe, mkHom_comp_getHom, Functor.map_id]
  rfl


-- @@ L265-266 verbatim
lemma succ_injective {n} {x y : F (Iter F n)} (h : succ x = succ y) : x = y := by
  rw [← unsucc_succ x, ← unsucc_succ y, h]


-- @@ L268-271 expanded
/-- The projection between successive iterates of the functor. -/
def project : ∀ n, QuasiBorelHom (Iter F (n + 1)) (Iter F n)
  | 0 => .mk fun _ ↦ .zero
  | n + 1 => succ.comp ((Functor.map (project n)).comp unsucc)


-- @@ L273-274 verbatim
instance : Sequence (Iter F) where
  project {n} := project n


-- @@ L276-280 verbatim
@[simp]
lemma project_zero
    : Sequence.project (S := Iter F) (n := 0)
    = .mk fun _ ↦ zero := by
  rfl


-- @@ L282-286 verbatim
@[simp]
lemma project_succ {n}
    : Sequence.project (S := Iter F) (n := n + 1)
    = succ.comp ((Functor.map (Sequence.project (n := n))).comp unsucc) := by
  rfl


-- @@ L288-292 expanded
/-- Constructs an `Iter`ated sequence of a `Functor` from an unfolding function. -/
@[simp]
def unfold (f : QuasiBorelHom A (F A)) : ∀ n, QuasiBorelHom A (Iter F n)
  | 0 => .mk fun _ ↦ zero
  | n + 1 => .mk fun x ↦ succ (Functor.map (unfold f n) (f x))


-- @@ L294-294 verbatim
end Iter


-- @@ L296-305 expanded
/-- A functor `F` is continuous if it preserves `Limit`s. -/
class Continuous (F) [Functor F] where
  /-- Folds a `Functor` into a `Limit`. -/
  seq {S} [Sequence S] : QuasiBorelHom (F (Limit S)) (Limit (Comp F S))
  /-- Unfolds a `Functor` out of a `Limit`. -/
  unseq {S} [Sequence S] : QuasiBorelHom (Limit (Comp F S)) (F (Limit S))
  /-- `seq` and `unseq` are inverses. -/
  seq_unseq {S} [Sequence S] : seq.comp (unseq (S := S)) = .id
  /-- `seq` and `unseq` are inverses. -/
  unseq_seq {S} [Sequence S] : unseq.comp (seq (S := S)) = .id


-- @@ L307-307 verbatim
namespace Continuous


-- @@ L309-309 verbatim
attribute [simp] seq_unseq unseq_seq


-- @@ L311-311 verbatim
variable [Continuous F] {S} [Sequence S]


-- @@ L313-316 verbatim
@[simp]
lemma seq_unseq_coe (x : Limit (Comp F S)) : seq (unseq x) = x := by
  have := congr_arg (DFunLike.coe · x) seq_unseq
  simpa only [QuasiBorelHom.comp_coe, QuasiBorelHom.id_coe] using this


-- @@ L318-321 verbatim
@[simp]
lemma unseq_seq_coe (x : F (Limit S)) : unseq (seq x) = x := by
  have := congr_arg (DFunLike.coe · x) unseq_seq
  simpa only [QuasiBorelHom.comp_coe, QuasiBorelHom.id_coe] using this


-- @@ L323-323 verbatim
end Continuous


-- @@ L325-329 verbatim
/-- The greatest fixed point of a `Functor`. -/
structure Nu (F) [Functor F] where
  mk ::
  /-- The underlying compatible sequence of finite iterates. -/
  get : Limit (Iter F)


-- @@ L331-331 verbatim
namespace Nu


-- @@ L333-334 verbatim
instance {F} [Functor F] : QuasiBorelSpace (Nu F) :=
  lift get


-- @@ L336-338 verbatim
@[local fun_prop, simp]
lemma isHom_get : IsHom (get (F := F)) :=
  isHom_of_lift get


-- @@ L340-342 verbatim
@[local fun_prop, simp]
lemma isHom_mk : IsHom (mk (F := F)) := by
  simp only [isHom_to_lift (A := Nu F), isHom_id']


-- @@ L344-356 expanded
/-- Shift a compatible family to a family in the functor-composed sequence. -/
@[simps]
def shift : QuasiBorelHom (Limit (Iter F)) (Limit (Comp F (Iter F))) where
  toFun
    x :=
    { toFun n := .mk (Iter.unsucc (x (n + 1)))
      property
        n := by
        simp only [Comp.project_def, QuasiBorelHom.coe_mk, Comp.mk.injEq]
        apply Iter.succ_injective
        simp only [Iter.succ_unsucc]
        have := congr_arg (DFunLike.coe · (x (n + 1 + 1))) (Iter.project_succ (F := F) (n := n))
        simp only [Limit.project_coe, QuasiBorelHom.comp_coe] at this
        rw [this] }


-- @@ L358-377 expanded
/-- Recover a compatible family from the functor-composed sequence. -/
@[simps -fullyApplied]
def unshift : QuasiBorelHom (Limit (Comp F (Iter F))) (Limit (Iter F))
    where
  toFun
    x :=
    { toFun
        | 0 => .zero
        | n + 1 => .succ (x n).get
      property
        n := by
        cases n with
        | zero => simp only [Nat.reduceAdd, Iter.project_zero, QuasiBorelHom.coe_mk]
        | succ n =>
          simp only [Iter.project_succ, QuasiBorelHom.comp_coe, Iter.unsucc_succ]
          congr 1
          simp only [← x.project_coe n, Comp.project_def, QuasiBorelHom.coe_mk] }
  property := by
    apply Limit.isHom_mk
    simp only [Pi.isHom_iff]
    intro n
    cases n <;> fun_prop


-- @@ L379-382 verbatim
@[simp]
private lemma shift_unshift_coe (x : Limit (Comp F (Iter F))) : shift (unshift x) = x := by
  ext n
  simp only [shift_coe_coe_get, unshift_coe_coe, Iter.unsucc_succ]


-- @@ L384-389 verbatim
@[simp]
private lemma unshift_shift_coe (x : Limit (Iter F)) : unshift (shift x) = x := by
  ext n
  cases n with
  | zero => subsingleton
  | succ n => simp only [unshift_coe_coe, shift_coe_coe_get, Iter.succ_unsucc]


-- @@ L391-393 expanded
/-- Rolls a `Functor` into a `Nu`. -/
def roll [Continuous F] : QuasiBorelHom (F (Nu F)) (Nu F) where
  toFun x := .mk (unshift (Continuous.seq (Functor.map (.mk get) x)))


-- @@ L395-397 expanded
/-- Unrolls a `Functor` out of a `Nu`. -/
def unroll [Continuous F] : QuasiBorelHom (Nu F) (F (Nu F)) where
  toFun x := Functor.map (.mk mk) (Continuous.unseq (shift x.get))


-- @@ L399-403 verbatim
@[simp]
lemma roll_unroll [Continuous F] (x : Nu F) : roll (unroll x) = x := by
  rcases x with ⟨x⟩
  simp only [roll, unroll, QuasiBorelHom.coe_mk, Functor.map_comp_coe, mk.injEq]
  simp_all


-- @@ L405-410 verbatim
@[simp]
lemma unroll_roll [Continuous F] (x : F (Nu F)) : unroll (roll x) = x := by
  simp only [
    unroll, roll, QuasiBorelHom.coe_mk, shift_unshift_coe,
    Continuous.unseq_seq_coe, Functor.map_comp_coe, QuasiBorelHom.eq_comp,
    QuasiBorelHom.eq_id, Functor.map_id, QuasiBorelHom.id_coe]


-- @@ L412-428 expanded
/-- Constructs a `Nu` from an unfolding. -/
def unfold (f : QuasiBorelHom A (F A)) : QuasiBorelHom A (Nu F) where
  toFun
    x :=
    {
      get :=
        { toFun n := Iter.unfold f n x
          property
            n := by
            induction n generalizing x with
            | zero =>
              simp only [Nat.reduceAdd, Iter.project_zero, Iter.unfold, QuasiBorelHom.coe_mk]
            | succ n
              ih =>
              simp only [Iter.project_succ, Iter.unfold, QuasiBorelHom.coe_mk,
                QuasiBorelHom.comp_coe, Iter.unsucc_succ, Functor.map_comp_coe]
              congr 3
              ext y
              simp only [QuasiBorelHom.comp_coe, QuasiBorelHom.coe_mk, ← ih, Iter.unfold] } }


-- @@ L430-430 verbatim
end Nu


-- @@ L432-432 verbatim
end QuasiBorelSpace
