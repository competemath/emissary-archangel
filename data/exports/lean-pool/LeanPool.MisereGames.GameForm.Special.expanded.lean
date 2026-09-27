/-
Copyright (c) 2022 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Tristan Figueroa Reid
-/
module

public import LeanPool.MisereGames.Form.Short


-- @@ L10-12 verbatim
/-!
Misere combinatorial games.
-/


-- @@ L14-14 verbatim
namespace MisereGames


-- @@ L16-25 verbatim
/-!
# Special games

This file defines some simple yet notable combinatorial games:

* `⋆ = {0 | 0}`
* `½ = {0 | 1}`
* `↑ = {0 | ⋆}`
* `↓ = {⋆ | 0}`
-/


-- @@ L27-27 verbatim
public noncomputable section


-- @@ L29-29 verbatim
universe u


-- @@ L31-31 verbatim
namespace GameForm


-- @@ L33-33 verbatim
open Form


-- @@ L35-35 verbatim
/-! ### Star -/


-- @@ L37-39 expanded
/-- The game `⋆ = {0 | 0}`, which is fuzzy with zero. -/
@[expose]
def star : GameForm :=
  OfSets.ofSets (fun _ ↦ {0})
    (by
      first
      | done
      | trivial
      | assumption
      | aesop
      |
        fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
          where `h` is a proof that sets are valid")


-- @@ L41-41 verbatim
@[inherit_doc] notation "⋆" => star

-- @@ L42-42 verbatim
recommended_spelling "star" for "⋆" in [«term⋆»]


-- @@ L44-44 expanded
@[simp]
theorem moves_star (p : Player) : Form.moves p star = {0} :=
  moves_ofSets ..


-- @@ L46-46 expanded
@[simp]
theorem neg_star : -star = star := by simp [star]


-- @@ L48-49 expanded
@[simp]
theorem short_star : IsShort star := by rw [star, Form.short_def]; simp


-- @@ L51-51 verbatim
/-! ### Half -/


-- @@ L53-55 expanded
/-- The game `½ = {0 | 1}`, which we prove satisfies `½ + ½ = 1`. -/
def half : GameForm :=
  OfSets.ofSets (Player.cases {0} { 1 })
    (by
      first
      | done
      | trivial
      | assumption
      | aesop
      |
        fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
          where `h` is a proof that sets are valid")


-- @@ L57-57 verbatim
@[inherit_doc] notation "½" => half

-- @@ L58-58 verbatim
recommended_spelling "half" for "½" in [«term½»]


-- @@ L60-60 expanded
@[simp]
theorem leftMoves_half : halfᴸ = {0} :=
  leftMoves_ofSets ..


-- @@ L61-61 expanded
@[simp]
theorem rightMoves_half : halfᴿ = { 1 } :=
  rightMoves_ofSets ..


-- @@ L63-64 expanded
theorem short_half : IsShort half := by rw [half, Form.short_def]; simp


-- @@ L66-66 verbatim
/-! ### Up and down -/


-- @@ L68-70 expanded
/-- The game `↑ = {0 | ⋆}`. -/
def up : GameForm :=
  OfSets.ofSets (Player.cases {0} {star})
    (by
      first
      | done
      | trivial
      | assumption
      | aesop
      |
        fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
          where `h` is a proof that sets are valid")


-- @@ L72-72 verbatim
@[inherit_doc] notation "↑" => up

-- @@ L73-73 verbatim
recommended_spelling "up" for "↑" in [«term↑»]


-- @@ L75-75 expanded
@[simp]
theorem leftMoves_up : upᴸ = {0} :=
  leftMoves_ofSets ..


-- @@ L76-76 expanded
@[simp]
theorem rightMoves_up : upᴿ = {star} :=
  rightMoves_ofSets ..


-- @@ L78-79 expanded
theorem short_up : IsShort up := by rw [up, Form.short_def]; simp


-- @@ L81-83 expanded
/-- The game `↓ = {⋆ | 0}`. -/
def down : GameForm :=
  OfSets.ofSets (Player.cases {star} {0})
    (by
      first
      | done
      | trivial
      | assumption
      | aesop
      |
        fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
          where `h` is a proof that sets are valid")


-- @@ L85-85 verbatim
@[inherit_doc] notation "↓" => down

-- @@ L86-86 verbatim
recommended_spelling "down" for "↓" in [«term↓»]


-- @@ L88-88 expanded
@[simp]
theorem leftMoves_down : downᴸ = {star} :=
  leftMoves_ofSets ..


-- @@ L89-89 expanded
@[simp]
theorem rightMoves_down : downᴿ = {0} :=
  rightMoves_ofSets ..


-- @@ L91-91 expanded
@[simp]
theorem neg_down : -down = up := by simp [up, down]


-- @@ L92-92 expanded
@[simp]
theorem neg_up : -up = down := by simp [up, down]


-- @@ L94-95 expanded
theorem short_down : IsShort down := by rw [down, Form.short_def]; simp


-- @@ L97-97 verbatim
/-! ### Tiny and miny -/


-- @@ L99-102 expanded
/-- A tiny game `⧾x` is defined as `{0 | {0 | -x}}`, and is amongst the smallest of the
infinitesimals. -/
def tiny (x : GameForm) : GameForm :=
  OfSets.ofSets
    (Player.cases {0}
      {OfSets.ofSets (Player.cases {0} {-x})
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid")})
    (by
      first
      | done
      | trivial
      | assumption
      | aesop
      |
        fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
          where `h` is a proof that sets are valid")


-- @@ L104-104 verbatim
@[inherit_doc] prefix:75 "⧾" => tiny

-- @@ L105-105 verbatim
recommended_spelling "tiny" for "⧾" in [«term⧾_»]


-- @@ L107-109 expanded
@[simp]
theorem leftMoves_tiny (x : GameForm) : (tiny x)ᴸ = {0} :=
  leftMoves_ofSets ..


-- @@ L111-113 expanded
@[simp]
theorem rightMoves_tiny (x : GameForm) :
    (tiny x)ᴿ =
      {OfSets.ofSets (Player.cases {0} {-x})
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid")} :=
  rightMoves_ofSets ..


-- @@ L115-118 expanded
theorem short_tiny {x : GameForm} (h1 : IsShort x) : IsShort (tiny x) :=
  by
  have hneg : IsShort (-x) := Form.Short.neg h1
  have :
    IsShort
      (OfSets.ofSets (Player.cases {0} {-x})
        (by
          first
          | done
          | trivial
          | assumption
          | aesop
          |
            fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
              where `h` is a proof that sets are valid")) :=
    by rw [Form.short_def]; simp [hneg]
  rw [tiny, Form.short_def]; simp [this]


-- @@ L120-122 expanded
/-- A miny game `⧿x` is defined as `{{x | 0} | 0}`. -/
def miny (x : GameForm) : GameForm :=
  OfSets.ofSets
    (Player.cases
      {OfSets.ofSets (Player.cases { x } {0})
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid")}
      {0})
    (by
      first
      | done
      | trivial
      | assumption
      | aesop
      |
        fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
          where `h` is a proof that sets are valid")


-- @@ L124-124 verbatim
@[inherit_doc] prefix:75 "⧿" => miny

-- @@ L125-125 verbatim
recommended_spelling "miny" for "⧿" in [«term⧿_»]


-- @@ L127-129 expanded
@[simp]
theorem leftMoves_miny (x : GameForm) :
    (miny x)ᴸ =
      {OfSets.ofSets (Player.cases { x } {0})
          (by
            first
            | done
            | trivial
            | assumption
            | aesop
            |
              fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
                where `h` is a proof that sets are valid")} :=
  leftMoves_ofSets ..


-- @@ L131-133 expanded
@[simp]
theorem rightMoves_miny (x : GameForm) : (miny x)ᴿ = {0} :=
  rightMoves_ofSets ..


-- @@ L135-137 expanded
@[simp]
theorem neg_tiny (x : GameForm) : -(tiny x) = miny x := by simp [miny, tiny]


-- @@ L139-141 expanded
@[simp]
theorem neg_miny (x : GameForm) : -(miny x) = tiny x := by simp [miny, tiny]


-- @@ L143-145 expanded
theorem short_miny {x : GameForm} (h1 : IsShort x) : IsShort (miny x) :=
  by
  rw [← neg_tiny, Form.Short.neg_iff]
  exact short_tiny h1


-- @@ L147-147 verbatim
/-! ### Switches -/


-- @@ L149-151 expanded
/-- A **switch** `±x` is defined as `{x | -x}`: switches are their own confusion interval! -/
def switch (x : GameForm) : GameForm :=
  OfSets.ofSets (Player.cases { x } {-x})
    (by
      first
      | done
      | trivial
      | assumption
      | aesop
      |
        fail "failed to prove sets are valid, try to use `!{st}'h` notation instead, \
          where `h` is a proof that sets are valid")


-- @@ L153-153 verbatim
@[inherit_doc] prefix:75 "±" => switch

-- @@ L154-154 verbatim
recommended_spelling "switch" for "±" in [«term±_»]


-- @@ L156-158 expanded
@[simp]
theorem leftMoves_switch (x : GameForm) : (switch x)ᴸ = { x } :=
  leftMoves_ofSets ..


-- @@ L160-162 expanded
@[simp]
theorem rightMoves_switch (x : GameForm) : (switch x)ᴿ = {-x} :=
  rightMoves_ofSets ..


-- @@ L164-167 expanded
@[simp]
theorem neg_switch (x : GameForm) : -switch x = switch x :=
  by
  rw [switch, neg_ofSets]
  simp [Set.neg_singleton]


-- @@ L169-171 expanded
@[simp]
theorem switch_zero : switch 0 = star := by ext p; cases p <;> simp


-- @@ L173-173 verbatim
end GameForm


-- @@ L175-175 verbatim
end


-- @@ L177-177 verbatim
end MisereGames
