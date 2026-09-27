/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton, Mario Carneiro, Alfie Davies, contributors
-/
module

public import LeanPool.MisereGames.Form
public import Mathlib.Data.QPF.Univariate.Basic
import LeanPool.MisereGames.Mathlib.Small


-- @@ L12-14 verbatim
/-!
Misere combinatorial games.
-/


-- @@ L16-16 verbatim
namespace MisereGames


-- @@ L18-18 verbatim
universe u


-- @@ L20-20 verbatim
open Form


-- @@ L22-22 verbatim
@[expose] public noncomputable section


-- @@ L24-26 verbatim
/-- The polynomial functor describing Left and Right option sets. -/
def GameFunctor (α : Type (u + 1)) : Type (u + 1) :=
  {s : Player → Set α // ∀ p, Small.{u} (s p)}


-- @@ L28-28 verbatim
namespace GameFunctor


-- @@ L30-31 verbatim
@[ext]
theorem ext {α : Type (u + 1)} {x y : GameFunctor α} : x.1 = y.1 → x = y := Subtype.ext


-- @@ L33-33 verbatim
instance {α : Type (u + 1)} (x : GameFunctor α) (p : Player) : Small.{u} (x.1 p) := x.2 p


-- @@ L35-36 verbatim
instance : Functor GameFunctor where
  map f s := ⟨(f '' s.1 ·), fun _ => by infer_instance⟩


-- @@ L38-40 verbatim
theorem map_def {α β} (f : α → β) (s : GameFunctor α) :
    f <$> s = ⟨(f '' s.1 ·), fun _ => by infer_instance⟩ :=
  rfl


-- @@ L42-63 verbatim
instance : QPF GameFunctor where
  P := ⟨Player → Type u, fun x ↦ Σ p, PLift (x p)⟩
  abs x := ⟨fun p ↦ Set.range (x.2 ∘ .mk p ∘ PLift.up), fun _ ↦ by infer_instance⟩
  repr x := ⟨fun p ↦ Shrink (x.1 p), Sigma.rec (fun _ y ↦ ((equivShrink _).symm y.1).1)⟩
  abs_repr x := by
    cases x with | mk s hs =>
    apply Subtype.ext
    funext p; ext z; constructor
    · rintro ⟨y, rfl⟩; exact ((equivShrink ↑(s p)).symm y).2
    · intro hz
      exact ⟨equivShrink ↑(s p) ⟨z, hz⟩,
        congrArg Subtype.val ((equivShrink ↑(s p)).left_inv ⟨z, hz⟩)⟩
  abs_map g := by
    intro ⟨x, f⟩
    ext p z
    change (∃ y, g (f ⟨p, PLift.up y⟩) = z) ↔
      z ∈ g '' Set.range (f ∘ Sigma.mk p ∘ PLift.up)
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, ⟨y, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
      exact ⟨y, rfl⟩


-- @@ L65-65 verbatim
end GameFunctor


-- @@ L67-69 verbatim
/-- The canonical type of combinatorial game forms. -/
def GameForm : Type (u + 1) :=
  QPF.Fix GameFunctor


-- @@ L71-71 verbatim
namespace GameForm


-- @@ L73-76 verbatim
private theorem dest_mk_game (options : GameFunctor GameForm) :
    (QPF.Fix.mk options : GameForm).dest = options := by
  unfold GameForm at options
  exact QPF.Fix.dest_mk options


-- @@ L78-84 verbatim
/--
Construct a `GameForm` from its Left and Right options.
-/
instance : OfSets GameForm fun _ ↦ True where
  ofSets (st : Player → Set GameForm) _ := QPF.Fix.mk ⟨st, fun
    | .left => (inferInstance : Small.{u} (st .left))
    | .right => (inferInstance : Small.{u} (st .right))⟩


-- @@ L86-89 verbatim
/--
The set of options of the game.
-/
private def moves' (p : Player) (x : GameForm.{u}) : Set GameForm.{u} := x.dest.1 p


-- @@ L91-108 verbatim
@[no_expose]
instance : Moves GameForm where
  moves := moves'
  isOption'_wf := by
    refine ⟨fun x ↦ ?_⟩
    apply QPF.Fix.ind
    unfold Moves.IsOption' moves'
    rintro _ ⟨⟨st, hst⟩, rfl⟩
    constructor
    rintro y hy
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hy
    rw [QPF.Fix.dest_mk] at hp
    have hcomponent := congrArg (fun options : GameFunctor GameForm ↦ options.1 p)
      (GameFunctor.map_def (β := GameForm) Subtype.val (⟨st, hst⟩ : GameFunctor _))
    have hp' : y ∈ Subtype.val '' st p :=
      Eq.mp (congrArg (fun options : Set GameForm ↦ y ∈ options) hcomponent) hp
    obtain ⟨option, _, rfl⟩ := hp'
    exact option.property


-- @@ L110-113 verbatim
/--
The set of Left options of the game.
-/
scoped notation:max x:max "ᴸ" => moves Player.left x


-- @@ L115-118 verbatim
/--
The set of Right options of the game.
-/
scoped notation:max x:max "ᴿ" => moves Player.right x


-- @@ L120-120 verbatim
instance instSmallElemMoves (p : Player) (x : GameForm.{u}) : Small.{u} (moves p x) := x.dest.2 p


-- @@ L122-129 expanded
private theorem moves_ofSets (p) (st : Player → Set GameForm) [Small.{u} (st .left)]
    [Small.{u} (st .right)] :
    moves p
        (OfSets.ofSets st
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid")) =
      st p :=
  by
  let options : GameFunctor GameForm :=
    ⟨st, fun
      | .left => inferInstance
      | .right => inferInstance⟩
  change (QPF.Fix.mk options).dest.1 p = st p
  exact congrArg (fun choices ↦ choices.1 p) (dest_mk_game options)


-- @@ L131-132 expanded
@[simp]
theorem ofSets_moves (x : GameForm) :
    OfSets.ofSets (fun p => moves p x)
        (by
          first
          | done
          | trivial
          | assumption
          | aesop
          |
            fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
              where `h` is a proof that sets are valid") =
      x :=
  x.mk_dest


-- @@ L134-135 expanded
private theorem leftMoves_ofSets (s t : Set GameForm) [Small.{u} s] [Small.{u} t] :
    (OfSets.ofSets (Player.cases s t)
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid"))ᴸ =
      s :=
  moves_ofSets ..


-- @@ L137-139 expanded
private theorem rightMoves_ofSets (s t : Set GameForm) [Small.{u} s] [Small.{u} t] :
    (OfSets.ofSets (Player.cases s t)
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid"))ᴿ =
      t :=
  moves_ofSets ..


-- @@ L141-144 expanded
@[simp]
theorem ofSets_leftMoves_rightMoves (x : GameForm) :
    OfSets.ofSets (Player.cases xᴸ xᴿ)
        (by
          first
          | done
          | trivial
          | assumption
          | aesop
          |
            fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
              where `h` is a proof that sets are valid") =
      x :=
  by
  convert x.ofSets_moves with p
  cases p <;> rfl


-- @@ L146-153 verbatim
/--
Two `GameForm`s are equal when their option sets are.
-/
@[ext]
theorem ext {x y : GameForm.{u}} (h : ∀ p, moves p x = moves p y) :
    x = y := by
  rw [← ofSets_moves x, ← ofSets_moves y]
  simp_rw [funext h]


-- @@ L155-158 expanded
private theorem ofSets_inj' {st₁ st₂ : Player → Set GameForm} [Small (st₁ .left)]
    [Small (st₁ .right)] [Small (st₂ .left)] [Small (st₂ .right)] :
    OfSets.ofSets st₁
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid") =
        OfSets.ofSets st₂
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid") ↔
      st₁ = st₂ :=
  by simp_rw [GameForm.ext_iff, moves_ofSets, funext_iff]


-- @@ L160-162 expanded
theorem ofSets_inj {s₁ s₂ t₁ t₂ : Set GameForm} [Small s₁] [Small s₂] [Small t₁] [Small t₂] :
    OfSets.ofSets (Player.cases s₁ t₁)
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid") =
        OfSets.ofSets (Player.cases s₂ t₂)
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid") ↔
      s₁ = s₂ ∧ t₁ = t₂ :=
  by simp only [ofSets_inj', Player.cases_inj]


-- @@ L164-165 verbatim
instance (x : GameForm.{u}) : Small.{u} {y // IsOption y x} :=
  inferInstanceAs (Small (⋃ p, moves p x))


-- @@ L167-170 verbatim
instance (x : GameForm.{u}) : Small.{u} {y // Subposition y x} :=
  small_transGen' _ x

-- We make no use of `GameForm`'s definition from a `QPF` after this point.

-- @@ L171-171 verbatim
attribute [irreducible] GameForm


-- @@ L173-185 expanded
/-- **Conway induction**: build data for a game by recursively building it on its
Left and Right sets. This rarely needs to be used explicitly, as the
termination checker will handle it.

See `ofSetsRecOn` for an alternate form.
-/
@[elab_as_elim]
def moveRecOn {motive : GameForm → Sort*} (x)
    (mk : Π x, (Π p, Π y ∈ moves p x, motive y) → motive x) : motive x :=
  mk x (fun p y _ ↦ moveRecOn y mk)
termination_by x
decreasing_by
  all_goals
    solve_by_elim (maxDepth := 8) [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
      Subposition.of_mem_moves, Subposition.trans, Subtype.prop]


-- @@ L187-190 verbatim
theorem moveRecOn_eq {motive : GameForm → Sort*} (x)
    (mk : Π x, (Π p, Π y ∈ moves p x, motive y) → motive x) :
    moveRecOn x mk = mk x (fun _ y _ ↦ moveRecOn y mk) := by
  rw [moveRecOn]


-- @@ L192-206 expanded
/-- **Conway induction**: build data for a game by recursively building it on its
Left and Right sets. This rarely needs to be used explicitly, as the
termination checker will handle it.

See `moveRecOn` for an alternate form.
-/
@[elab_as_elim]
def ofSetsRecOn {motive : GameForm.{u} → Sort*} (x)
    (mk :
      Π (s t : Set GameForm) [Small s] [Small t],
        (Π x ∈ s, motive x) →
          (Π x ∈ t, motive x) →
            motive
              (OfSets.ofSets (Player.cases s t)
                (by
                  first
                  | done
                  | trivial
                  | assumption
                  | aesop
                  |
                    fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                      where `h` is a proof that sets are valid"))) :
    motive x :=
  cast (by simp) <|
    moveRecOn (motive := fun x ↦
      motive
        (OfSets.ofSets (Player.cases xᴸ xᴿ)
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid")))
      x fun x IH ↦
      mk _ _ (fun y hy ↦ cast (by simp) (IH .left y hy))
        (fun y hy ↦ cast (by simp) (IH .right y hy))


-- @@ L208-222 expanded
@[simp]
theorem ofSetsRecOn_ofSets {motive : GameForm.{u} → Sort*} (s t : Set GameForm) [Small.{u} s]
    [Small.{u} t]
    (mk :
      Π (s t : Set GameForm) [Small s] [Small t],
        (Π x ∈ s, motive x) →
          (Π x ∈ t, motive x) →
            motive
              (OfSets.ofSets (Player.cases s t)
                (by
                  first
                  | done
                  | trivial
                  | assumption
                  | aesop
                  |
                    fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                      where `h` is a proof that sets are valid"))) :
    ofSetsRecOn
        (OfSets.ofSets (Player.cases s t)
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid"))
        mk =
      mk _ _ (fun y _ ↦ ofSetsRecOn y mk) (fun y _ ↦ ofSetsRecOn y mk) :=
  by
  rw [ofSetsRecOn, cast_eq_iff_heq, moveRecOn_eq]
  congr
  any_goals simp only [moves_ofSets, Player.cases, heq_eq_eq]
  all_goals
    refine Function.hfunext rfl fun x _ h ↦ ?_
    cases h
    refine Function.hfunext ?_ fun _ _ _ ↦ ?_
    · simp [moves_ofSets]
    · rw [ofSetsRecOn, cast_heq_iff_heq, heq_cast_iff_heq]


-- @@ L224-227 expanded
private def neg' (x : GameForm) : GameForm :=
  OfSets.ofSets (Player.cases (Set.range fun y : xᴿ ↦ neg' y.1) (Set.range fun y : xᴸ ↦ neg' y.1))
    (by
      first
      | done
      | trivial
      | assumption
      | aesop
      |
        fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
          where `h` is a proof that sets are valid")
termination_by x
decreasing_by
  all_goals
    solve_by_elim (maxDepth := 8) [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
      Subposition.of_mem_moves, Subposition.trans, Subtype.prop]


-- @@ L229-241 verbatim
/--
$\def\form<#1>[#2]{\left\{#1 \mid #2\right\}}$
The *conjugate* of a game is defined by `-!{s | t} = !{-t | -s}`. In the
literature, one would see
$$
  \overline{G}=\form<\overline{G^\mathcal{R}}>[\overline{G^\mathcal{L}}].
$$
In this repository, the conjugate is often referred to as the 'negative', even
though it is *not* necessarily an additive inverse.
-/
@[no_expose]
instance : Neg GameForm where
  neg := neg'


-- @@ L243-247 expanded
private theorem neg_ofSets'' (s t : Set GameForm) [Small s] [Small t] :
    -OfSets.ofSets (Player.cases s t)
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid") =
      OfSets.ofSets (Player.cases (Neg.neg '' t) (Neg.neg '' s))
        (by
          first
          | done
          | trivial
          | assumption
          | aesop
          |
            fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
              where `h` is a proof that sets are valid") :=
  by
  change neg' _ = _
  rw [neg']
  simp [Neg.neg, Set.ext_iff, moves_ofSets, ofSets_inj']


-- @@ L249-252 verbatim
instance : InvolutiveNeg GameForm where
  neg_neg x := by
    refine ofSetsRecOn x ?_
    aesop (add simp [neg_ofSets'', ofSets_inj'])


-- @@ L254-255 expanded
private theorem neg_ofSets (s t : Set GameForm) [Small s] [Small t] :
    -OfSets.ofSets (Player.cases s t)
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid") =
      OfSets.ofSets (Player.cases (-t) (-s))
        (by
          first
          | done
          | trivial
          | assumption
          | aesop
          |
            fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
              where `h` is a proof that sets are valid") :=
  by simp_rw [neg_ofSets'', Set.image_neg_eq_neg]


-- @@ L257-260 expanded
theorem neg_ofSets' (st : Player → Set GameForm) [Small (st .left)] [Small (st .right)] :
    -OfSets.ofSets st
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid") =
      OfSets.ofSets (fun p ↦ -st (-p))
        (by
          first
          | done
          | trivial
          | assumption
          | aesop
          |
            fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
              where `h` is a proof that sets are valid") :=
  by
  rw [ofSets_eq_ofSets_cases, ofSets_eq_ofSets_cases fun _ ↦ -_, neg_ofSets]
  rfl


-- @@ L262-264 expanded
private theorem neg_ofSets_const (s : Set GameForm) [Small s] :
    -OfSets.ofSets (fun _ ↦ s)
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid") =
      OfSets.ofSets (fun _ ↦ -s)
        (by
          first
          | done
          | trivial
          | assumption
          | aesop
          |
            fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
              where `h` is a proof that sets are valid") :=
  by simp only [neg_ofSets']


-- @@ L266-267 expanded
theorem neg_eq (x : GameForm) :
    -x =
      OfSets.ofSets (Player.cases (-xᴿ) (-xᴸ))
        (by
          first
          | done
          | trivial
          | assumption
          | aesop
          |
            fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
              where `h` is a proof that sets are valid") :=
  by rw [← neg_ofSets, ofSets_leftMoves_rightMoves]


-- @@ L269-270 expanded
theorem neg_eq' (x : GameForm) :
    -x =
      OfSets.ofSets (fun p ↦ -moves (-p) x)
        (by
          first
          | done
          | trivial
          | assumption
          | aesop
          |
            fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
              where `h` is a proof that sets are valid") :=
  by rw [neg_eq, ofSets_eq_ofSets_cases (fun _ ↦ -_)]; rfl


-- @@ L272-274 verbatim
private theorem moves_neg' (p : Player) (x : GameForm) :
    moves p (-x) = -moves (-p) x := by
  rw [neg_eq', moves_ofSets]


-- @@ L276-281 verbatim
/-!
### Addition and subtraction
-/

-- The recursive `add'` definition builds both players' option sets and needs
-- extra heartbeats for the termination proof after unfolding `ofSets`.

-- @@ L282-286 expanded
private def add' (x y : GameForm) : GameForm :=
  OfSets.ofSets
    (Player.cases
      ((Set.range fun z : moves .left x ↦ add' z y) ∪ (Set.range fun z : moves .left y ↦ add' x z))
      ((Set.range fun z : moves .right x ↦ add' z y) ∪
        (Set.range fun z : moves .right y ↦ add' x z)))
    (by
      first
      | done
      | trivial
      | assumption
      | aesop
      |
        fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
          where `h` is a proof that sets are valid")
termination_by (x, y)
decreasing_by
  all_goals
    solve_by_elim (maxDepth := 8) [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
      Subposition.of_mem_moves, Subposition.trans, Subtype.prop]


-- @@ L288-298 verbatim
/--
$\def\form<#1>[#2]{\left\{#1 \mid #2\right\}}$
The sum of `x = !{s₁ | t₁}` and `y = !{s₂ | t₂}` is `!{s₁ + y, x + s₂ | t₁ + y,
x + t₂}`. In the literature, one would see
$$
  G+H=\form<G^\mathcal{L}+H,G+H^\mathcal{L}>[G^\mathcal{R}+H,G+H^\mathcal{R}].
$$
-/
@[no_expose]
instance : Add GameForm where
  add := add'


-- @@ L300-304 expanded
theorem add_eq (x y : GameForm) :
    x + y =
      OfSets.ofSets (Player.cases ((· + y) '' xᴸ ∪ (x + ·) '' yᴸ) ((· + y) '' xᴿ ∪ (x + ·) '' yᴿ))
        (by
          first
          | done
          | trivial
          | assumption
          | aesop
          |
            fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
              where `h` is a proof that sets are valid") :=
  by
  change add' _ _ = _
  rw [add']
  simp [HAdd.hAdd, Add.add, Set.ext_iff, ofSets_inj']


-- @@ L306-308 expanded
theorem add_eq' (x y : GameForm) :
    x + y =
      OfSets.ofSets (fun p ↦ (· + y) '' moves p x ∪ (x + ·) '' moves p y)
        (by
          first
          | done
          | trivial
          | assumption
          | aesop
          |
            fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
              where `h` is a proof that sets are valid") :=
  by rw [add_eq, ofSets_eq_ofSets_cases (fun _ ↦ _ ∪ _)]


-- @@ L310-316 expanded
theorem ofSets_add_ofSets (s₁ t₁ s₂ t₂ : Set GameForm) [Small s₁] [Small t₁] [Small s₂] [Small t₂] :
    OfSets.ofSets (Player.cases s₁ t₁)
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid") +
        OfSets.ofSets (Player.cases s₂ t₂)
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid") =
      OfSets.ofSets
        (Player.cases
          ((· +
                OfSets.ofSets (Player.cases s₂ t₂)
                  (by
                    first
                    | done
                    | trivial
                    | assumption
                    | aesop
                    |
                      fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                        where `h` is a proof that sets are valid")) ''
              s₁ ∪
            (OfSets.ofSets (Player.cases s₁ t₁)
                  (by
                    first
                    | done
                    | trivial
                    | assumption
                    | aesop
                    |
                      fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                        where `h` is a proof that sets are valid") +
                ·) ''
              s₂)
          ((· +
                OfSets.ofSets (Player.cases s₂ t₂)
                  (by
                    first
                    | done
                    | trivial
                    | assumption
                    | aesop
                    |
                      fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                        where `h` is a proof that sets are valid")) ''
              t₁ ∪
            (OfSets.ofSets (Player.cases s₁ t₁)
                  (by
                    first
                    | done
                    | trivial
                    | assumption
                    | aesop
                    |
                      fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                        where `h` is a proof that sets are valid") +
                ·) ''
              t₂))
        (by
          first
          | done
          | trivial
          | assumption
          | aesop
          |
            fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
              where `h` is a proof that sets are valid") :=
  by
  rw [add_eq]
  simp only [moves_ofSets, Player.cases]


-- @@ L318-323 expanded
theorem ofSets_add_ofSets' (st₁ st₂ : Player → Set GameForm) [Small (st₁ .left)] [Small (st₂ .left)]
    [Small (st₁ .right)] [Small (st₂ .right)] :
    OfSets.ofSets st₁
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid") +
        OfSets.ofSets st₂
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid") =
      OfSets.ofSets
        (fun p ↦
          (· +
                OfSets.ofSets st₂
                  (by
                    first
                    | done
                    | trivial
                    | assumption
                    | aesop
                    |
                      fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                        where `h` is a proof that sets are valid")) ''
              st₁ p ∪
            (OfSets.ofSets st₁
                  (by
                    first
                    | done
                    | trivial
                    | assumption
                    | aesop
                    |
                      fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                        where `h` is a proof that sets are valid") +
                ·) ''
              st₂ p)
        (by
          first
          | done
          | trivial
          | assumption
          | aesop
          |
            fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
              where `h` is a proof that sets are valid") :=
  by
  rw [ofSets_eq_ofSets_cases, ofSets_eq_ofSets_cases st₂, ofSets_eq_ofSets_cases (fun _ ↦ _ ∪ _),
    ofSets_add_ofSets]


-- @@ L325-327 verbatim
private theorem moves_add' (p : Player) (x y : GameForm) :
    moves p (x + y) = (· + y) '' moves p x ∪ (x + ·) '' moves p y := by
  rw [add_eq', moves_ofSets]


-- @@ L329-331 verbatim
theorem isOption_neg {x y : GameForm} : IsOption x (-y) ↔ IsOption (-x) y := by
  simp only [moves_neg', IsOption.iff_mem_union, Player.neg_left, Player.neg_right,
             Set.union_comm, Set.mem_union, Set.mem_neg]


-- @@ L333-335 verbatim
@[simp]
theorem isOption_neg_neg {x y : GameForm} : IsOption (-x) (-y) ↔ IsOption x y := by
  rw [isOption_neg, neg_neg]


-- @@ L337-339 verbatim
theorem forall_moves_neg {P : GameForm → Prop} {p : Player} {x : GameForm} :
    (∀ y ∈ moves p (-x), P y) ↔ (∀ y ∈ moves (-p) x, P (-y)) := by
  simp only [moves_neg', Set.mem_neg, Set.forall_neg_mem]


-- @@ L341-342 verbatim
theorem IsOption.add_left {x y z : GameForm} (h : IsOption x y) : IsOption (z + x) (z + y) := by
  aesop (add simp [moves_add'])


-- @@ L344-345 verbatim
theorem IsOption.add_right {x y z : GameForm} (h : IsOption x y) : IsOption (x + z) (y + z) := by
  aesop (add simp [moves_add'])


-- @@ L347-354 expanded
private theorem add_comm' (x y : GameForm) : x + y = y + x :=
  by
  ext
  simp only [moves_add', Set.mem_union, Set.mem_image, or_comm]
  congr! 3 <;>
    · refine and_congr_right_iff.2 fun h ↦ ?_
      rw [add_comm']
termination_by (x, y)
decreasing_by
  all_goals
    solve_by_elim (maxDepth := 8) [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
      Subposition.of_mem_moves, Subposition.trans, Subtype.prop]


-- @@ L356-364 expanded
private theorem add_assoc' (x y z : GameForm) : x + y + z = x + (y + z) :=
  by
  ext1
  simp only [moves_add', Set.image_union, Set.image_image, Set.union_assoc]
  refine congrArg₂ _ ?_ (congrArg₂ _ ?_ ?_) <;>
    · ext
      congr! 2
      rw [add_assoc']
termination_by (x, y, z)
decreasing_by
  all_goals
    solve_by_elim (maxDepth := 8) [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
      Subposition.of_mem_moves, Subposition.trans, Subtype.prop]


-- @@ L366-374 expanded
private theorem neg_add' (x y : GameForm) : -(x + y) = -x + -y :=
  by
  ext
  simp only [moves_neg', moves_add', Set.union_neg, Set.mem_union, Set.mem_neg, Set.mem_image,
    Set.exists_neg_mem]
  congr! 3 <;>
    · refine and_congr_right_iff.2 fun _ ↦ ?_
      rw [← neg_inj, neg_add', neg_neg]
termination_by (x, y)
decreasing_by
  all_goals
    solve_by_elim (maxDepth := 8) [Prod.Lex.left, Prod.Lex.right, PSigma.Lex.left, PSigma.Lex.right,
      Subposition.of_mem_moves, Subposition.trans, Subtype.prop]


-- @@ L376-378 verbatim
instance : AddCommSemigroup GameForm where
  add_assoc := private add_assoc'
  add_comm := private add_comm'


-- @@ L380-418 expanded
instance : Form GameForm where
  moves_neg' := private moves_neg'
  moves_add' := private moves_add'
  moves_small' := instSmallElemMoves
  IsEndLike p x := moves p x = ∅
  isEndLike_ofEnd' _ _ h1 := h1
  isEndLike_add_iff' p x y := by simp [moves_add']
  isEndLike_neg_iff_neg' p
    g := by
    constructor <;> cases p
    all_goals
      · intro h1
        simp only [moves_neg', Player.neg_left, Player.neg_right, Set.neg_eq_empty] at h1 ⊢
        exact h1
  moves_ofSets' := private moves_ofSets
  add_zero'
    x := by
    refine moveRecOn x ?_
    intro y h1
    simp only [Player.forall] at h1
    ext p z
    have moves_zero' :
      moves p
          (OfSets.ofSets (fun x ↦ ∅)
              (by
                first
                | done
                | trivial
                | assumption
                | aesop
                |
                  fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                    where `h` is a proof that sets are valid") :
            GameForm) =
        ∅ :=
      by cases p <;> simp [moves_ofSets]
    rw [moves_add', moves_zero', Set.image_empty, Set.union_empty, Set.mem_image]
    cases p
    all_goals
      · apply Iff.intro
        · intro ⟨w, left, right⟩
          subst right
          simp_all only
        · intro a
          use z, a
          simp_all only
  add_eq_zero_iff' x y := by constructor <;> simp_all [GameForm.ext_iff, moves_add', moves_ofSets]
  ofSets_inj'' := private ofSets_inj'
  neg_ofSets'' := private neg_ofSets
  neg_add' := private neg_add'
  smallElemMoves' := instSmallElemMoves
  ofSets_isEndLike_iff' p s t _ _ := Eq.congr_right rfl
  ofSets_add_ofSets'' := ofSets_add_ofSets
  ofSets_moves_of_not_isEndLike' := @fun g _ _ _ => ofSets_moves g


-- @@ L420-422 verbatim
@[simp]
theorem isEndLike_iff_isEnd {g : GameForm} {p : Player} : IsEndLike p g ↔ IsEnd p g := by
  simp only [IsEndLike, isEnd_def]


-- @@ L424-431 verbatim
theorem leftEnd_rightEnd_eq_zero {g : GameForm} (h1 : IsEnd .left g) (h2 : IsEnd .right g) :
    g = 0 := by
  rw [isEnd_def] at h1 h2
  rw [zero_def]
  ext p
  cases p
  · simp_all
  · simp_all


-- @@ L433-437 verbatim
theorem both_ends_eq_zero {g : GameForm} {p : Player} (h1 : IsEnd p g) (h2 : IsEnd (-p) g) :
    g = 0 := by
  cases p
  · exact leftEnd_rightEnd_eq_zero h1 h2
  · exact leftEnd_rightEnd_eq_zero h2 h1


-- @@ L439-442 verbatim
theorem ne_zero_not_end {g : GameForm} (h1 : g ≠ 0) : ∃ p, ¬IsEnd p g := by
  apply not_forall.mp
  intro h2
  exact h1 (leftEnd_rightEnd_eq_zero (h2 .left) (h2 .right))


-- @@ L444-447 verbatim
@[simp]
theorem zero_not_both_end {g : GameForm} {p : Player} (h1 : g ≠ 0) (h2 : IsEnd p g) :
    ¬IsEnd (-p) g :=
  fun h3 => h1 (both_ends_eq_zero h2 h3)


-- @@ L449-465 verbatim
theorem isOption_zero_add_iff {g h : GameForm} :
    IsOption 0 (g + h) ↔ (IsOption 0 g ∧ h = 0) ∨ (IsOption 0 h ∧ g = 0) := by
  constructor
  · intro h1
    simp only [isOption_iff_mem_union, moves_add, Set.mem_union,
               Set.mem_image, add_eq_zero_iff, ↓existsAndEq, true_and, exists_eq_right_right] at h1
    simp only [isOption_iff_mem_union, Set.mem_union]
    apply Or.elim3 h1
    · intro h2
      apply Or.elim h2
      · simp_all
      · simp_all
    · simp_all
    · simp_all
  · rintro (⟨h_isOption_zero_g, h_h_zero⟩ | ⟨h_isOption_zero_h, h_g_zero⟩)
    · rwa [h_h_zero, add_zero]
    · rwa [h_g_zero, zero_add]


-- @@ L467-467 verbatim
end GameForm


-- @@ L469-469 verbatim
end


-- @@ L471-471 verbatim
end MisereGames
