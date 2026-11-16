/-
Copyright (c) 2026 Timothy Harvey and James Mitchell. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Timothy Harvey
-/
import Mathlib.Algebra.Group.Equiv.Defs
import Semigroup.Rees.Basic
import Semigroup.GreensTheorem.Subgroups.Basic
import Semigroup.ZeroSimple.Ideals.Basic
import Semigroup.ZeroSimple.Idempotents
import Semigroup.ZeroSimple.ReesMatrix


-- @@ L13-48 verbatim
/-!
# The Rees Theorem

This file proves the Rees theorem: every completely 0-simple semigroup is
isomorphic to a Rees matrix semigroup (`ReesMatrix`, defined in
`Semigroup.ZeroSimple.ReesMatrix`) over the H-class group of a primitive
idempotent.

## Main definitions

* `sandwichMatrix`: the sandwich matrix of a completely 0-simple semigroup at a
  primitive idempotent `e`, with entries in the H-class of `e`.
* `toRees`: the coordinate map sending a nonzero element to the triple of its
  Rees coordinates (R-class index, H-class coordinate, L-class index).

## Main results

* `toRees_mul`: `toRees` is multiplicative.
* `toRees_bijective`: `toRees` is a bijection.
* `rees_theorem`: **the Rees theorem** — every completely 0-simple semigroup is
  isomorphic to a Rees matrix semigroup over the H-class group of a primitive
  idempotent.
* `rees_theorem_converse`: **the converse of the Rees theorem** — every Rees matrix
  semigroup over a group whose sandwich matrix is regular (every row and every
  column has a defined entry) is completely 0-simple.

## References

* [J. M. Howie, *Fundamentals of Semigroup Theory*][howie1995]

The proofs formalized in this module closely follow the structure and logic
from lecture notes:

* J. D. Mitchell, *MT5863 Semigroup Theory* (lecture notes,
  University of St Andrews, 2026).
-/


-- @@ L50-50 verbatim
open scoped GreensRelations



-- @@ L53-53 verbatim
section ReesConstruction


-- @@ L55-55 verbatim
variable {S : Type*} [SemigroupWithZero S]


-- @@ L57-63 expanded
open Classical in
/-- The sandwich matrix at an idempotent `e`: the entry at `(l, i)` is the product
`colRep e l * rowRep e i` of the chosen column and row representatives when it lies
in the H-class of `e`, and `none` otherwise. -/
noncomputable def sandwichMatrix (e : S) :
    ReesLIndex e → ReesRIndex e → Option (IsGreenH.eqvClass e) := fun l i =>
  if h : IsGreenH (colRep e l * rowRep e i) e then some ⟨_, h⟩ else none


-- @@ L65-69 verbatim
/-- The Rees row index of a nonzero element `x`: its R-class, which lies in the
D-class of `e` since all nonzero elements are D-related. -/
def reesRIdxOf (hS : IsCompletelyZeroSimple S) {e : S} (he : IsPrimitiveIdempotent e)
    {x : S} (hx : x ≠ 0) : ReesRIndex e :=
  ⟨GreenRClass.mk x, x, rfl, hS.isGreenD_of_ne_zero hx he.ne_zero⟩


-- @@ L71-75 verbatim
/-- The Rees column index of a nonzero element `x`: its L-class, which lies in the
D-class of `e` since all nonzero elements are D-related. -/
def reesLIdxOf (hS : IsCompletelyZeroSimple S) {e : S} (he : IsPrimitiveIdempotent e)
    {x : S} (hx : x ≠ 0) : ReesLIndex e :=
  ⟨GreenLClass.mk x, x, rfl, hS.isGreenD_of_ne_zero hx he.ne_zero⟩


-- @@ L77-106 expanded
/-- Any nonzero `x` factors as `r * g * q` through a chosen `r` in its
R-class that is L-related to `e` and a chosen `q` in its L-class that is
R-related to `e`, with the middle coordinate `g` H-related to `e`. -/
theorem IsPrimitiveIdempotent.exists_hClass_factor (hS : IsZeroSimple S) {e : S}
    (he : IsPrimitiveIdempotent e) {r q x : S} (hx : x ≠ 0) (hr : IsGreenL r e) (hq : IsGreenR q e)
    (hrx : IsGreenR r x) (hqx : IsGreenL q x) : ∃ g : S, IsGreenH g e ∧ x = r * g * q :=
  by
  have hre : r * e = r := IsGreenLeftDvd.mul_idem_eq_self he.isIdempotentElem hr.1
  have heq : e * q = q := IsGreenRightDvd.idem_mul_eq_self he.isIdempotentElem hq.1
  obtain ⟨m, hxm, hem⟩ := exists_factor_right he.isIdempotentElem hre hrx.2
  obtain ⟨n, hxn, hne⟩ := exists_factor_left he.isIdempotentElem heq hqx.2
  obtain ⟨w, hwr, hew⟩ := hr.exists_left_retraction he.isIdempotentElem
  obtain ⟨w', hqw', hw'e⟩ := hq.exists_right_retraction he.isIdempotentElem
  have hrepr : r * (w * x * w') * q = x := by
    calc
      r * (w * x * w') * q = r * (w * r) * (m * (w' * q)) := by rw [hxm]; simp only [mul_assoc]
      _ = r * e * (m * (w' * q)) := by rw [hwr]
      _ = r * (e * m) * (w' * q) := by simp only [mul_assoc]
      _ = x * (w' * q) := by rw [hem, ← hxm]
      _ = n * (q * w') * q := by rw [hxn]; simp only [mul_assoc]
      _ = n * e * q := by rw [hqw']
      _ = x := by rw [hne, ← hxn]
  have hg0 : w * x * w' ≠ 0 := by
    intro h0
    exact hx (by rw [← hrepr, h0, mul_zero, zero_mul])
  refine ⟨w * x * w', he.isGreenH_of_corner hS hg0 ?_ ?_, hrepr.symm⟩
  · rw [← mul_assoc, ← mul_assoc, hew]
  · rw [mul_assoc, hw'e]


-- @@ L108-118 expanded
/-- Any nonzero `x` factors as `rowRep * g * colRep` through the representatives of
its Rees indices, with the middle coordinate `g` H-related to `e`. -/
theorem exists_hClass_coord (hS : IsCompletelyZeroSimple S) {e : S} (he : IsPrimitiveIdempotent e)
    {x : S} (hx : x ≠ 0) :
    ∃ g : S,
      IsGreenH g e ∧ x = rowRep e (reesRIdxOf hS he hx) * g * colRep e (reesLIdxOf hS he hx) :=
  he.exists_hClass_factor hS.isZeroSimple hx (rowRep_isGreenL e (reesRIdxOf hS he hx))
    (colRep_isGreenR e (reesLIdxOf hS he hx))
    (GreenRClass.mk_eq_mk_iff.mp (rowRep_mk e (reesRIdxOf hS he hx)))
    (GreenLClass.mk_eq_mk_iff.mp (colRep_mk e (reesLIdxOf hS he hx)))


-- @@ L120-130 verbatim
open Classical in
/-- The Rees coordinate map: `0` goes to `zero`, and a nonzero `x` goes to the triple
of its R-class index, its H-class coordinate, and its L-class index. -/
noncomputable def toRees (hS : IsCompletelyZeroSimple S) {e : S}
    (he : IsPrimitiveIdempotent e) (x : S) :
    ReesMatrix (IsGreenH.eqvClass e) (ReesRIndex e) (ReesLIndex e) (sandwichMatrix e) :=
  if hx : x = 0 then .zero
  else
    .elem (reesRIdxOf hS he hx)
      ⟨(exists_hClass_coord hS he hx).choose, (exists_hClass_coord hS he hx).choose_spec.1⟩
      (reesLIdxOf hS he hx)


-- @@ L132-137 verbatim
/-- `toRees` sends `0` to the zero of the Rees matrix semigroup. -/
theorem toRees_zero (hS : IsCompletelyZeroSimple S) {e : S}
    (he : IsPrimitiveIdempotent e) :
    letI : Group (IsGreenH.eqvClass e) := he.isIdempotentElem.hClassGroup
    toRees hS he 0 = 0 :=
  dif_pos rfl


-- @@ L139-145 verbatim
/-- `toRees` sends a nonzero element to the triple of its coordinates. -/
theorem toRees_of_ne_zero (hS : IsCompletelyZeroSimple S) {e : S}
    (he : IsPrimitiveIdempotent e) {x : S} (hx : x ≠ 0) :
    toRees hS he x = .elem (reesRIdxOf hS he hx)
      ⟨(exists_hClass_coord hS he hx).choose, (exists_hClass_coord hS he hx).choose_spec.1⟩
      (reesLIdxOf hS he hx) :=
  dif_neg hx


-- @@ L147-156 expanded
/-- A triple `rowRep * g * colRep` with `g` in the H-class of `e` is a nonzero
element of `S` (needed for surjectivity: the constructed pre-image is not `0`). -/
theorem rees_repr_ne_zero {e : S} (he : IsPrimitiveIdempotent e) (i : ReesRIndex e)
    (l : ReesLIndex e) {g : S} (hg : IsGreenH g e) : rowRep e i * g * colRep e l ≠ 0 :=
  mul_ne_zero_of_isGreenL_of_isGreenR he.isIdempotentElem he.ne_zero
    (isGreenL_mul_of_isGreenL_of_isGreenH he.isIdempotentElem (rowRep_isGreenL e i) hg)
    (colRep_isGreenR e l)


-- @@ L158-193 expanded
/-- Uniqueness of the Rees coordinates: any decomposition
`x = rowRep i * g * colRep l` with `g` H-related to `e` is *the* image of `x`
under `toRees`.  This packages the facts that the R-class of `x` is that of
`rowRep i`, the L-class of `x` is that of `colRep l`, and that the middle
coordinate is uniquely determined (Green's lemma cancellation). -/
theorem toRees_eq_elem (hS : IsCompletelyZeroSimple S) {e : S} (he : IsPrimitiveIdempotent e)
    {x : S} (hx : x ≠ 0) {i : ReesRIndex e} {l : ReesLIndex e} {g : S} (hg : IsGreenH g e)
    (hrep : x = rowRep e i * g * colRep e l) : toRees hS he x = .elem i ⟨g, hg⟩ l := by
  -- the R-class of `x` is that of `rowRep i`, the L-class that of `colRep l`
  
  have hxr : IsGreenR x (rowRep e i) :=
    isGreenR_left_of_repr he.isIdempotentElem (rowRep_isGreenL e i) hg (colRep_isGreenR e l) hrep
  have hxq : IsGreenL x (colRep e l) :=
    isGreenL_right_of_repr he.isIdempotentElem (rowRep_isGreenL e i) hg (colRep_isGreenR e l) hrep
  have hi : reesRIdxOf hS he hx = i := by
    apply Subtype.ext
    rw [← rowRep_mk e i]
    exact GreenRClass.mk_eq_mk_iff.mpr hxr
  have hl : reesLIdxOf hS he hx = l := by
    apply Subtype.ext
    rw [← colRep_mk e l]
    exact GreenLClass.mk_eq_mk_iff.mpr hxq
  subst hi hl
  obtain ⟨hgx, hxrep⟩ := (exists_hClass_coord hS he hx).choose_spec
  have hgeq : (exists_hClass_coord hS he hx).choose = g :=
    hClass_coord_unique he.isIdempotentElem (rowRep_isGreenL e (reesRIdxOf hS he hx))
      (colRep_isGreenR e (reesLIdxOf hS he hx)) hgx hg (hxrep.symm.trans hrep)
  rw [toRees_of_ne_zero hS he hx]
  congr 1
  exact Subtype.ext hgeq


-- @@ L195-220 expanded
/-- When `x * y ≠ 0`, the sandwich product `colRep λ_x * rowRep i_y` lands in
the H-class of `e`, so the corresponding sandwich matrix entry is defined. -/
theorem sandwich_isGreenH_of_mul_ne_zero (hS : IsCompletelyZeroSimple S) {e : S}
    (he : IsPrimitiveIdempotent e) {x y : S} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x * y ≠ 0) :
    IsGreenH (colRep e (reesLIdxOf hS he hx) * rowRep e (reesRIdxOf hS he hy)) e :=
  by
  have heq : e * colRep e (reesLIdxOf hS he hx) = colRep e (reesLIdxOf hS he hx) :=
    idem_mul_colRep he.isIdempotentElem _
  have hre : rowRep e (reesRIdxOf hS he hy) * e = rowRep e (reesRIdxOf hS he hy) :=
    rowRep_mul_idem he.isIdempotentElem _
  have hqx : IsGreenL (colRep e (reesLIdxOf hS he hx)) x :=
    GreenLClass.mk_eq_mk_iff.mp (colRep_mk e (reesLIdxOf hS he hx))
  have hry : IsGreenR (rowRep e (reesRIdxOf hS he hy)) y :=
    GreenRClass.mk_eq_mk_iff.mp (rowRep_mk e (reesRIdxOf hS he hy))
  obtain ⟨n, hxn, -⟩ := exists_factor_left he.isIdempotentElem heq hqx.2
  obtain ⟨m, hym, -⟩ :=
    exists_factor_right he.isIdempotentElem hre
      hry.2
        -- the sandwich product is a corner element; it is nonzero since `x * y` is
        
  refine
    he.isGreenH_of_corner hS.isZeroSimple ?_ (by rw [← mul_assoc, heq]) (by rw [mul_assoc, hre])
  intro h0
  apply hxy
  calc
    x * y = n * (colRep e (reesLIdxOf hS he hx) * rowRep e (reesRIdxOf hS he hy)) * m :=
      by
      conv_lhs => rw [hxn, hym]
      simp only [mul_assoc]
    _ = 0 := by rw [h0, mul_zero, zero_mul]


-- @@ L222-239 expanded
/-- When `x * y = 0`, the sandwich matrix entry at `(λ_x, i_y)` is `none`, so
the Rees matrix product of the images is zero. -/
theorem sandwich_none_of_mul_eq_zero (hS : IsCompletelyZeroSimple S) {e : S}
    (he : IsPrimitiveIdempotent e) {x y : S} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x * y = 0) :
    sandwichMatrix e (reesLIdxOf hS he hx) (reesRIdxOf hS he hy) = none :=
  by
  have hqx : IsGreenL (colRep e (reesLIdxOf hS he hx)) x :=
    GreenLClass.mk_eq_mk_iff.mp (colRep_mk e (reesLIdxOf hS he hx))
  have hry : IsGreenR (rowRep e (reesRIdxOf hS he hy)) y :=
    GreenRClass.mk_eq_mk_iff.mp
      (rowRep_mk e (reesRIdxOf hS he hy))
        -- the sandwich product vanishes because `x * y` does
        
  have h0 : colRep e (reesLIdxOf hS he hx) * rowRep e (reesRIdxOf hS he hy) = 0 :=
    by
    rcases hqx.1 with hqe | ⟨c, hqe⟩ <;> rcases hry.1 with hrye | ⟨d, hrye⟩
    · rw [hqe, hrye]; exact hxy
    · rw [hqe, hrye, ← mul_assoc, hxy, zero_mul]
    · rw [hqe, hrye, mul_assoc, hxy, mul_zero]
    · rw [hqe, hrye, mul_assoc, ← mul_assoc x, hxy, zero_mul, mul_zero]
  exact dif_neg fun h => ne_zero_of_isGreenH h he.ne_zero h0


-- @@ L241-281 expanded
/-- `toRees` is multiplicative: multiplication in `S` corresponds to the Rees matrix
product, with the sandwich matrix accounting for the middle factor. -/
theorem toRees_mul (hS : IsCompletelyZeroSimple S) {e : S} (he : IsPrimitiveIdempotent e)
    (x y : S) :
    letI : Group (IsGreenH.eqvClass e) := he.isIdempotentElem.hClassGroup
    toRees hS he (x * y) = toRees hS he x * toRees hS he y :=
  by
  letI : Group (IsGreenH.eqvClass e) := he.isIdempotentElem.hClassGroup
  change toRees hS he (x * y) = toRees hS he x * toRees hS he y
  by_cases hx : x = 0
  · -- x = 0: both sides are zero
    rw [hx, zero_mul, toRees_zero, zero_mul]
  by_cases hy : y = 0
  · -- y = 0: both sides are zero
    rw [hy, mul_zero, toRees_zero, mul_zero]
  by_cases hxy : x * y = 0
  · -- x * y = 0: the sandwich entry is `none`, so the matrix product is zero
    rw [hxy, toRees_zero, toRees_of_ne_zero hS he hx, toRees_of_ne_zero hS he hy,
      ReesMatrix.elem_mul_of_none (sandwich_none_of_mul_eq_zero hS he hx hy hxy)]
  · have hsand := sandwich_isGreenH_of_mul_ne_zero hS he hx hy hxy
    have hsome :
      sandwichMatrix e (reesLIdxOf hS he hx) (reesRIdxOf hS he hy) =
        some ⟨colRep e (reesLIdxOf hS he hx) * rowRep e (reesRIdxOf hS he hy), hsand⟩ :=
      dif_pos hsand
    obtain ⟨hgx, hrx⟩ := (exists_hClass_coord hS he hx).choose_spec
    obtain ⟨hgy, hry⟩ := (exists_hClass_coord hS he hy).choose_spec
    have hmid :
      IsGreenH
        ((exists_hClass_coord hS he hx).choose *
            (colRep e (reesLIdxOf hS he hx) * rowRep e (reesRIdxOf hS he hy)) *
          (exists_hClass_coord hS he hy).choose)
        e :=
      IsGreenH.mul_mem he.isIdempotentElem (IsGreenH.mul_mem he.isIdempotentElem hgx hsand) hgy
    have hrep :
      x * y =
        rowRep e (reesRIdxOf hS he hx) *
            ((exists_hClass_coord hS he hx).choose *
                (colRep e (reesLIdxOf hS he hx) * rowRep e (reesRIdxOf hS he hy)) *
              (exists_hClass_coord hS he hy).choose) *
          colRep e (reesLIdxOf hS he hy) :=
      by
      conv_lhs => rw [hrx, hry]
      simp only [mul_assoc]
    rw [toRees_eq_elem hS he hxy hmid hrep, toRees_of_ne_zero hS he hx, toRees_of_ne_zero hS he hy,
      ReesMatrix.elem_mul_of_some hsome]
      -- the middle coordinates agree: multiplication in the H-class group is
          -- multiplication in `S` on the underlying elements
      
    congr 1


-- @@ L283-320 verbatim
/-- `toRees` is a bijection: the Rees coordinates determine the element uniquely,
and every triple `rowRep * g * colRep` is realized. -/
theorem toRees_bijective (hS : IsCompletelyZeroSimple S) {e : S}
    (he : IsPrimitiveIdempotent e) :
    Function.Bijective (toRees hS he) := by
  letI : Group (IsGreenH.eqvClass e) := he.isIdempotentElem.hClassGroup
  constructor
  · -- injectivity: compare images case-by-case on zero
    intro a b hab
    by_cases ha : a = 0 <;> by_cases hb : b = 0
    · rw [ha, hb]
    · rw [ha, toRees_zero, toRees_of_ne_zero hS he hb] at hab
      exact absurd hab ReesMatrix.zero_ne_elem
    · rw [hb, toRees_zero, toRees_of_ne_zero hS he ha] at hab
      exact absurd hab ReesMatrix.elem_ne_zero
    · -- both nonzero: the coordinates match, so reconstruct `a = b`
      rw [toRees_of_ne_zero hS he ha, toRees_of_ne_zero hS he hb] at hab
      injection hab with h1 h2 h3
      -- turn the index/subtype equalities into equalities of elements of `S`,
      -- so the rewrites below do not run into dependent-type motives
      have hg : (exists_hClass_coord hS he ha).choose =
          (exists_hClass_coord hS he hb).choose := congrArg Subtype.val h2
      have hr : rowRep e (reesRIdxOf hS he ha) = rowRep e (reesRIdxOf hS he hb) :=
        congrArg (rowRep e) h1
      have hc : colRep e (reesLIdxOf hS he ha) = colRep e (reesLIdxOf hS he hb) :=
        congrArg (colRep e) h3
      calc a = rowRep e (reesRIdxOf hS he ha) * (exists_hClass_coord hS he ha).choose *
            colRep e (reesLIdxOf hS he ha) := (exists_hClass_coord hS he ha).choose_spec.2
        _ = rowRep e (reesRIdxOf hS he hb) * (exists_hClass_coord hS he hb).choose *
            colRep e (reesLIdxOf hS he hb) := by
            rw [hg, hr, hc]
        _ = b := ((exists_hClass_coord hS he hb).choose_spec.2).symm
  · -- surjectivity: zero comes from `0`, a triple from `rowRep * g * colRep`
    intro M
    rcases M with _ | ⟨i, g, l⟩
    · exact ⟨0, toRees_zero hS he⟩
    · exact ⟨rowRep e i * g.1 * colRep e l,
        toRees_eq_elem hS he (rees_repr_ne_zero he i l g.2) g.2 rfl⟩


-- @@ L322-332 verbatim
/-- **The Rees theorem**: every completely 0-simple semigroup is isomorphic (as a
multiplicative structure) to a Rees matrix semigroup over the H-class group of a
primitive idempotent, with the sandwich matrix `sandwichMatrix e`. -/
theorem rees_theorem (hS : IsCompletelyZeroSimple S) {e : S}
    (he : IsPrimitiveIdempotent e) :
    letI : Group (IsGreenH.eqvClass e) := he.isIdempotentElem.hClassGroup
    Nonempty (S ≃* ReesMatrix (IsGreenH.eqvClass e) (ReesRIndex e) (ReesLIndex e)
      (sandwichMatrix e)) := by
  letI : Group (IsGreenH.eqvClass e) := he.isIdempotentElem.hClassGroup
  refine ⟨⟨Equiv.ofBijective _ (toRees_bijective hS he), fun x y => ?_⟩⟩
  exact toRees_mul hS he x y


-- @@ L334-334 verbatim
end ReesConstruction


-- @@ L336-336 verbatim
/-! ### The converse of the Rees theorem -/


-- @@ L338-338 verbatim
section ReesConverse


-- @@ L340-340 verbatim
open ReesMatrix


-- @@ L342-342 verbatim
variable {G : Type*} [Group G] {I Λ : Type*} {P : Λ → I → Option G}


-- @@ L344-386 verbatim
/-- A Rees matrix semigroup over a group with a regular sandwich matrix is
0-simple: any nonzero element generates the whole semigroup as an ideal, since
the sandwich entries provided by regularity are invertible in `G`. -/
theorem reesMatrix_isZeroSimple [Nonempty I]
    (hrow : ∀ l : Λ, ∃ i : I, ∃ p : G, P l i = some p)
    (hcol : ∀ i : I, ∃ l : Λ, ∃ p : G, P l i = some p) :
    IsZeroSimple (ReesMatrix G I Λ P) := by
  constructor
  · -- a nonzero product exists: multiply through a defined sandwich entry
    obtain ⟨i⟩ := ‹Nonempty I›
    obtain ⟨l, p, hp⟩ := hcol i
    exact ⟨elem i 1 l, elem i 1 l, by rw [elem_mul_of_some hp]; exact elem_ne_zero⟩
  · intro T hT
    obtain ⟨⟨a, ha⟩, hcl⟩ := hT
    have h0 : (0 : ReesMatrix G I Λ P) ∈ T := by
      have h := (hcl a ha 0).1
      rwa [zero_mul] at h
    by_cases hex : ∃ x ∈ T, x ≠ 0
    · -- a nonzero member `elem i g l` recovers every triple by two translations
      right
      obtain ⟨x, hxT, hx0⟩ := hex
      rcases x with _ | ⟨i, g, l⟩
      · exact absurd rfl hx0
      obtain ⟨l₁, p, hp⟩ := hcol i
      obtain ⟨i₂, q, hq⟩ := hrow l
      ext y
      simp only [Set.mem_univ, iff_true]
      rcases y with _ | ⟨j, b, m⟩
      · exact h0
      · have h1 : elem j (b * (p * g * q)⁻¹ * p * g) l ∈ T := by
          have h := (hcl _ hxT (elem j (b * (p * g * q)⁻¹) l₁)).1
          rwa [elem_mul_of_some hp] at h
        have h2 : elem j (b * (p * g * q)⁻¹ * p * g * q * 1) m ∈ T := by
          have h := (hcl _ h1 (elem i₂ 1 m)).2
          rwa [elem_mul_of_some hq] at h
        have heq : b * (p * g * q)⁻¹ * p * g * q * 1 = b := by
          simp [mul_assoc]
        rwa [heq] at h2
    · -- otherwise the ideal contains only `0`
      left
      refine Set.eq_singleton_iff_unique_mem.mpr ⟨h0, fun x hx => ?_⟩
      by_contra hx0
      exact hex ⟨x, hx, hx0⟩


-- @@ L388-422 verbatim
/-- Every defined sandwich entry `P l i = some p` yields a primitive idempotent
`elem i p⁻¹ l` of the Rees matrix semigroup. -/
theorem reesMatrix_isPrimitiveIdempotent {i : I} {l : Λ} {p : G}
    (hp : P l i = some p) :
    IsPrimitiveIdempotent (elem i p⁻¹ l : ReesMatrix G I Λ P) := by
  constructor
  · -- idempotency: the middle coordinate is `p⁻¹ * p * p⁻¹ = p⁻¹`
    have h : (elem i p⁻¹ l : ReesMatrix G I Λ P) * elem i p⁻¹ l = elem i p⁻¹ l := by
      rw [elem_mul_of_some hp, inv_mul_cancel, one_mul]
    exact h
  · exact elem_ne_zero
  · intro f hf hf0 hef hfe
    rcases f with _ | ⟨j, b, m⟩
    · exact absurd rfl hf0
    -- `e * f = f` forces the row of `f` to be `i`
    rcases hpj : P l j with _ | r
    · rw [elem_mul_of_none hpj] at hef
      exact absurd hef zero_ne_elem
    rw [elem_mul_of_some hpj] at hef
    injection hef with h1 _ _
    subst h1
    -- `f * e = f` forces the column of `f` to be `l`
    rcases hpm : P m i with _ | s
    · rw [elem_mul_of_none hpm] at hfe
      exact absurd hfe zero_ne_elem
    rw [elem_mul_of_some hpm] at hfe
    injection hfe with _ _ h3
    subst h3
    -- idempotency of `f` pins its middle coordinate to `p⁻¹`
    have hff : (elem i b l : ReesMatrix G I Λ P) * elem i b l = elem i b l := hf
    rw [elem_mul_of_some hp] at hff
    injection hff with _ hmid _
    have hpb : p * b = 1 :=
      mul_left_cancel (a := b) (by rw [← mul_assoc, hmid, mul_one])
    rw [(inv_eq_of_mul_eq_one_right hpb).symm]


-- @@ L424-434 verbatim
/-- **The converse of the Rees theorem**: a Rees matrix semigroup over a group
whose sandwich matrix is regular (every row and every column has a defined
entry) is completely 0-simple. -/
theorem rees_theorem_converse [Nonempty I]
    (hrow : ∀ l : Λ, ∃ i : I, ∃ p : G, P l i = some p)
    (hcol : ∀ i : I, ∃ l : Λ, ∃ p : G, P l i = some p) :
    IsCompletelyZeroSimple (ReesMatrix G I Λ P) := by
  refine ⟨reesMatrix_isZeroSimple hrow hcol, ?_⟩
  obtain ⟨i⟩ := ‹Nonempty I›
  obtain ⟨l, p, hp⟩ := hcol i
  exact ⟨elem i p⁻¹ l, reesMatrix_isPrimitiveIdempotent hp⟩


-- @@ L436-436 verbatim
end ReesConverse
