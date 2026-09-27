/-
Copyright (c) 2026 Siddhartha Gadgil, Anand Rao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil, Anand Rao
-/
module


-- @@ L8-8 verbatim
@[expose] public section


-- @@ L10-10 verbatim
namespace LeanPool.Polylean


-- @@ L12-12 verbatim
universe u v w


-- @@ L14-22 verbatim
/-- A `Quiver` `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices
    a type `a ⟶ b` of arrows from `a` to `b`.

    It is a common generalisation of multigraphs and categories.
    This definition is taken from `mathlib`:
    https://leanprover-community.github.io/mathlib_docs/combinatorics/quiver/basic.html#quiver. -/
class Quiver (V : Sort u) where
  /-- The type of arrows from one vertex to another. -/
  hom : V → V → Sort v


-- @@ L24-25 verbatim
/-- Arrow notation for the hom type of a quiver. -/
infixr:10 " ⟶ " => Quiver.hom -- type using `\-->` or `\hom`


-- @@ L27-27 verbatim
namespace Quiver


-- @@ L29-34 expanded
/-- A pre-functor is a morphism of quivers. -/
structure PreFunctor {V V' : Sort _} (Q : Quiver V) (Q' : Quiver V') where
  /-- The map on vertices. -/
  obj : V → V'
  /-- The map on arrows. -/
  map : {X Y : V} → (Quiver.hom X Y) → (Quiver.hom (obj X) (obj Y))


-- @@ L36-36 verbatim
namespace PreFunctor


-- @@ L38-40 verbatim
/-- The identity morphism between quivers. -/
@[simp] protected def id (V : Sort _) [Q : Quiver V] : PreFunctor Q Q :=
{ obj := id, map := id }


-- @@ L42-42 verbatim
instance (V : Sort _) [Q : Quiver V] : Inhabited (PreFunctor Q Q) := ⟨PreFunctor.id V⟩


-- @@ L44-47 verbatim
/-- Composition of morphisms between quivers. -/
@[simp] def comp {U V W : Sort _} {QU : Quiver U} {QV : Quiver V} {QW : Quiver W}
  (F : PreFunctor QU QV) (G : PreFunctor QV QW) : PreFunctor QU QW :=
  { obj := G.obj ∘ F.obj, map := G.map ∘ F.map }


-- @@ L49-49 verbatim
end PreFunctor


-- @@ L51-51 verbatim
end Quiver



-- @@ L54-57 expanded
/-- Paths in a quiver. -/
inductive Path {V : Sort _} [Quiver V] : V → V → Sort _
  | nil : {A : V} → Path A A
  | cons : {A B C : V} → (Quiver.hom A B) → Path B C → Path A C


-- @@ L59-59 verbatim
namespace Quiver


-- @@ L61-63 expanded
/-- Convert a single quiver arrow to a path. -/
def toPath {V : Sort _} [Quiver V] {A B : V} (e : Quiver.hom A B) : Path A B :=
  .cons e .nil


-- @@ L65-65 verbatim
end Quiver


-- @@ L67-67 verbatim
namespace Path


-- @@ L69-69 verbatim
variable {V : Sort _} [Quiver V] {A B C D : V}


-- @@ L71-72 verbatim
/-- The empty path at a vertex, with its vertex explicit for pattern matching. -/
@[match_pattern] abbrev nil' (A : V) : Path A A := Path.nil

-- @@ L73-75 expanded
/-- A path formed by adding an edge to the front, with endpoints explicit for matching. -/
@[match_pattern]
abbrev cons' (A B C : V) : (Quiver.hom A B) → Path B C → Path A C :=
  Path.cons


-- @@ L77-81 expanded
/-- Concatenate an edge to the end of a path. -/
@[match_pattern]
abbrev snoc : {A B C : V} → Path A B → (Quiver.hom B C) → Path A C
  | _, _, _, .nil, e => .cons e .nil
  | _, _, _, .cons e p', e' => .cons e (snoc p' e')


-- @@ L83-85 expanded
/-- Append an edge to the end of a path, with endpoints explicit for matching. -/
@[match_pattern]
abbrev snoc' (A B C : V) : Path A B → (Quiver.hom B C) → Path A C :=
  Path.snoc


-- @@ L87-90 verbatim
/-- Concatenation of paths. -/
def append : {A B C : V} → Path A B → Path B C → Path A C
  | _, _, _, .nil, p => p
  | _, _, _, .cons e p', p => cons e (append p' p)


-- @@ L92-95 verbatim
/-- The length of a path. -/
def length : {A B : V} → Path A B → Nat
  | _, _, .nil => .zero
  | _, _, .cons _ p => .succ (length p)


-- @@ L97-97 verbatim
@[simp] theorem nil_append (p : Path A B) : .append .nil p = p := rfl


-- @@ L99-102 verbatim
@[simp] theorem append_nil (p : Path A B) : .append p .nil = p := by
  induction p
  · rfl
  · simp [append, *]


-- @@ L104-105 expanded
theorem snoc_cons (e : Quiver.hom A B) (p : Path B C) (e' : Quiver.hom C D) :
    snoc (cons e p) e' = cons e (snoc p e') := by cases p <;> simp


-- @@ L107-111 expanded
theorem append_snoc (p : Path A B) (p' : Path B C) (e : Quiver.hom C D) :
    append p (snoc p' e) = snoc (append p p') e :=
  by
  induction p
  · case nil => rfl
  · case cons ih => simp [append, ih p']


-- @@ L113-117 expanded
theorem append_cons (p : Path A B) (e : Quiver.hom B C) (p' : Path C D) :
    append p (cons e p') = append (snoc p e) p' :=
  by
  induction p
  · case nil => rfl
  · case cons ih => dsimp [append]; rw [ih]


-- @@ L119-125 verbatim
theorem append_assoc (p : Path A B) (q : Path B C) (r : Path C D) :
    append (append p q) r = append p (append q r) := by
  induction p
  · case nil => rfl
  · case cons ih => simp [append]; apply ih

-- TODO Rephrase this to work for general paths, not just loops

-- @@ L126-128 verbatim
theorem nil_length {A : V} : (p : Path A A) → p.length = .zero ↔ p = .nil' A
  | .nil => ⟨λ _ => rfl, λ _ => rfl⟩
  | .cons _ p => by apply Iff.intro <;> (intro; simp [length] at *)


-- @@ L130-132 expanded
theorem snoc_length {A B C : V} :
    (p : Path A B) → (e : Quiver.hom B C) → length (.snoc p e) = .succ (length p)
  | .nil, _ => rfl
  | .cons _ p', e => by simp [length, snoc_length p' e]


-- @@ L134-138 verbatim
theorem length_append {A B C : V} : (p : Path A B) → (q : Path B C) → (append p q).length = p.length + q.length
  | .nil, q => by rw [Nat.add_comm]; rfl
  | .cons _ p', q => by
    dsimp [append, length]
    simpa [Nat.succ_add] using congrArg Nat.succ (length_append p' q)


-- @@ L140-143 verbatim
/-- The end-point of the first edge in the path. -/
def first : Path A B → V
  | .nil' v => v
  | .cons' _ v _ _ _ => v


-- @@ L145-149 verbatim
/-- The source of the last end in the path. -/
def last : {A B : V} → Path A B → V
  | _, _, .nil' v => v
  | .(v), _, .cons' v _ _ _ .nil => v
  | _, _, .cons' _ _ _ _ (.cons e p) => last (.cons e p)


-- @@ L151-151 expanded
theorem first_cons (A B C : V) (e : Quiver.hom A B) (p : Path B C) : first (cons e p) = B :=
  rfl


-- @@ L153-156 expanded
theorem last_snoc : (A B C : V) → (p : Path A B) → (e : Quiver.hom B C) → last (snoc p e) = B
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons' _ _ _ _ .nil, _ => by rw [snoc_cons]; rfl
  | _, _, _, .cons' _ _ _ _ (.cons _ _), _ => by rw [snoc_cons, snoc, last, ← snoc_cons];
    apply last_snoc


-- @@ L158-158 verbatim
end Path



-- @@ L161-162 verbatim
/-- A loop is a path whose source and target are the same vertex. -/
abbrev Loop {V : Sort _} [Quiver V] (A : V) := Path A A


-- @@ L164-164 verbatim
namespace Loop


-- @@ L166-166 verbatim
variable {V : Sort _} [Quiver V] (A : V)


-- @@ L168-169 verbatim
/-- Regard a loop as a path. -/
def toPath : Loop A → Path A A := id


-- @@ L171-172 verbatim
/-- The empty loop. -/
abbrev nil : Loop A := Path.nil


-- @@ L174-175 verbatim
/-- The next vertex reached by the first edge of a loop. -/
abbrev next : Loop A → V := Path.first


-- @@ L177-178 verbatim
/-- Concatenate two loops. -/
abbrev concat : Loop A → Loop A → Loop A := Path.append


-- @@ L180-180 verbatim
end Loop

-- @@ L181-181 verbatim
end LeanPool.Polylean
