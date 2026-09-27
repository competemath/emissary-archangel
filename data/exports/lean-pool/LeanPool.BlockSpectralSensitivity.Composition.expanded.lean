/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import LeanPool.BlockSpectralSensitivity.Defs.Sensitivity


-- @@ L10-30 verbatim
/-!
# Self-composition and the product blocks

Section 14 of `bs_lambda.txt` composes the seed function with itself.  For
`f : Input W → Bool` and `g : Input V → Bool` the block composition `comp f g` takes
one `V`-indexed input for each coordinate of `W`, applies `g` to each of them and feeds
the resulting `W`-indexed bit string to `f`.

`iterFun f m` is the `m`-fold self-composition `F_m = f^{∘ m}`, whose coordinate set is
the iterated product `IterCoord V m ≃ V^m`.  The Cartesian-product blocks
`B_{i_1} × ⋯ × B_{i_m}` are `iterBlock blk m`, indexed by `IterCoord ι m ≃ ι^m`; they are
pairwise disjoint sensitive blocks of `F_m` at the all-zero input, whence
`bs (F_m) ≥ k^m` (`card_pow_le_bs_iterFun`).

The spectral half of Section 14, the ABKRT multiplicativity theorem
`lambda (f ∘ g) = lambda f * lambda g`, is *imported* by the document but proved here, in
`BSLambda/Spectral/Multiplicative.lean`.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/


-- @@ L32-32 verbatim
@[expose] public section


-- @@ L34-34 verbatim
namespace BSLambda


-- @@ L36-36 verbatim
open Function


-- @@ L38-38 verbatim
universe u


-- @@ L40-43 verbatim
/-- Block composition `f ∘ g`: `N` disjoint `M`-bit inputs, `g` applied to each, the `N`
resulting bits fed to `f` (Section 14 of `bs_lambda.txt`). -/
def comp {W V : Type*} (f : Input W → Bool) (g : Input V → Bool) :
    Input (W × V) → Bool := fun x => f fun w => g fun v => x (w, v)


-- @@ L45-47 verbatim
/-- The defining equation of `comp`. -/
theorem comp_apply {W V : Type*} (f : Input W → Bool) (g : Input V → Bool)
    (x : Input (W × V)) : comp f g x = f fun w ↦ g fun v ↦ x (w, v) := rfl


-- @@ L49-55 verbatim
/-- The `m`-fold power `V^m`, realised as an iterated binary product so that
`IterCoord V (m + 1) = V × IterCoord V m` holds definitionally (Section 14).  It is used
both as the coordinate set of `iterFun f m` and, at `V := ι`, as the index set of the
product blocks `iterBlock blk m`. -/
def IterCoord (V : Type u) : ℕ → Type u
  | 0 => PUnit
  | m + 1 => V × IterCoord V m


-- @@ L57-62 verbatim
/-- `IterCoord V m` is a finite type (Section 14). -/
instance instFintypeIterCoord {V : Type*} [Fintype V] : ∀ m, Fintype (IterCoord V m)
  | 0 => inferInstanceAs (Fintype PUnit)
  | m + 1 =>
      letI := instFintypeIterCoord (V := V) m
      inferInstanceAs (Fintype (V × IterCoord V m))


-- @@ L64-69 verbatim
/-- `IterCoord V m` has decidable equality (Section 14). -/
instance instDecidableEqIterCoord {V : Type*} [DecidableEq V] : ∀ m, DecidableEq (IterCoord V m)
  | 0 => inferInstanceAs (DecidableEq PUnit)
  | m + 1 =>
      letI := instDecidableEqIterCoord (V := V) m
      inferInstanceAs (DecidableEq (V × IterCoord V m))


-- @@ L71-77 verbatim
/-- There are exactly `k^m` tuples, where `k = #V` (Section 14). -/
theorem card_iterCoord (V : Type*) [Fintype V] :
    ∀ m, Fintype.card (IterCoord V m) = Fintype.card V ^ m
  | 0 => Fintype.card_punit
  | m + 1 => by
      change Fintype.card (V × IterCoord V m) = _
      rw [Fintype.card_prod, card_iterCoord V m, pow_succ']


-- @@ L79-83 verbatim
/-- The Cartesian-product block `B_{i_1} × ⋯ × B_{i_m}` (Section 14). -/
def iterBlock {V ι : Type*} [DecidableEq V] (blk : ι → Finset V) :
    (m : ℕ) → IterCoord ι m → Finset (IterCoord V m)
  | 0 => fun _ => (Finset.univ : Finset PUnit)
  | m + 1 => fun t => (blk t.1) ×ˢ iterBlock blk m t.2


-- @@ L85-87 verbatim
/-- There is a single degenerate `0`-fold product block, the whole (one-point) cube. -/
@[simp] theorem iterBlock_zero {V ι : Type*} [DecidableEq V] (blk : ι → Finset V)
    (t : IterCoord ι 0) : iterBlock blk 0 t = (Finset.univ : Finset PUnit) := rfl


-- @@ L89-91 verbatim
/-- The recursion equation of `iterBlock`: the first index picks the outer factor. -/
theorem iterBlock_succ {V ι : Type*} [DecidableEq V] (blk : ι → Finset V) (m : ℕ)
    (t : IterCoord ι (m + 1)) : iterBlock blk (m + 1) t = blk t.1 ×ˢ iterBlock blk m t.2 := rfl


-- @@ L93-97 verbatim
/-- `F_m = f^{∘ m}`, the `m`-fold self-composition (Section 14). `F_0` is the one-bit
identity function. -/
def iterFun {V : Type*} (f : Input V → Bool) : (m : ℕ) → Input (IterCoord V m) → Bool
  | 0 => fun x => x PUnit.unit
  | m + 1 => comp f (iterFun f m)


-- @@ L99-101 verbatim
/-- `F_0` is the one-bit identity function. -/
@[simp] theorem iterFun_zero {V : Type*} (f : Input V → Bool) (x : Input (IterCoord V 0)) :
    iterFun f 0 x = x PUnit.unit := rfl


-- @@ L103-105 verbatim
/-- The recursion equation of `iterFun`: `F_{m+1} = f ∘ F_m`. -/
theorem iterFun_succ {V : Type*} (f : Input V → Bool) (m : ℕ) :
    iterFun f (m + 1) = comp f (iterFun f m) := rfl


-- @@ L107-114 verbatim
/-- Slicing the all-zero input flipped on a product block `A ×ˢ B`: the `v`-slice is the
flip of `B` when `v ∈ A`, and the all-zero input otherwise (Section 14). -/
theorem flipSet_zeroInput_product_slice {V W : Type*} [DecidableEq V] [DecidableEq W]
    (A : Finset V) (B : Finset W) (v : V) :
    (fun w => flipSet (zeroInput (V × W)) (A ×ˢ B) (v, w))
      = if v ∈ A then flipSet (zeroInput W) B else zeroInput W := by
  funext w
  by_cases hv : v ∈ A <;> simp [zeroInput, Finset.mem_product, hv]


-- @@ L116-127 verbatim
/-- The key composition step of Section 14: if the inner function `g` is flipped from `0`
to `1` by the block `B`, then `comp f g` on the product block `A ×ˢ B` feeds `f` exactly
the all-zero input flipped on `A`. -/
theorem comp_flipSet_product {V W : Type*} [DecidableEq V] [DecidableEq W]
    {f : Input V → Bool} {g : Input W → Bool} {A : Finset V} {B : Finset W}
    (hzero : g (zeroInput W) = false) (hflip : g (flipSet (zeroInput W) B) = true) :
    comp f g (flipSet (zeroInput (V × W)) (A ×ˢ B)) = f (flipSet (zeroInput V) A) := by
  rw [comp_apply]
  congr 1
  funext v
  rw [flipSet_zeroInput_product_slice, flipSet_zeroInput_apply]
  by_cases hv : v ∈ A <;> simp [hv, hzero, hflip]


-- @@ L129-129 verbatim
section Seed


-- @@ L131-131 verbatim
variable {V ι : Type*} [DecidableEq V] {f : Input V → Bool} {blk : ι → Finset V}


-- @@ L133-141 verbatim
omit [DecidableEq V] in
/-- The all-zero input of `F_m` evaluates to `0` whenever the seed does (Section 14). -/
theorem iterFun_zeroInput (hzero : f (zeroInput V) = false) :
    ∀ m, iterFun f m (zeroInput (IterCoord V m)) = false
  | 0 => rfl
  | m + 1 => by
      have h : (fun w ↦ iterFun f m fun v ↦ zeroInput (IterCoord V (m + 1)) (w, v))
          = zeroInput V := funext fun _ ↦ iterFun_zeroInput hzero m
      exact (congrArg f h).trans hzero


-- @@ L143-154 verbatim
/-- Flipping the Cartesian-product block `B_{i_1} × ⋯ × B_{i_m}` at the all-zero input
turns the value of `F_m` from `0` to `1` (Section 14). -/
theorem iterFun_flipSet_iterBlock (hzero : f (zeroInput V) = false)
    (hflip : ∀ i, f (flipSet (zeroInput V) (blk i)) = true) :
    ∀ (m : ℕ) (t : IterCoord ι m),
      iterFun f m (flipSet (zeroInput (IterCoord V m)) (iterBlock blk m t)) = true
  | 0 => fun _ ↦ by
      change flipSet (zeroInput PUnit) Finset.univ PUnit.unit = true
      simp
  | m + 1 => fun t ↦
      (comp_flipSet_product (iterFun_zeroInput hzero m)
        (iterFun_flipSet_iterBlock hzero hflip m t.2)).trans (hflip t.1)


-- @@ L156-156 verbatim
end Seed


-- @@ L158-158 verbatim
section Blocks


-- @@ L160-160 verbatim
variable {V ι : Type*} [DecidableEq V] {blk : ι → Finset V}


-- @@ L162-166 verbatim
/-- Cartesian products of nonempty blocks are nonempty (Section 14). -/
theorem iterBlock_nonempty (hne : ∀ i, (blk i).Nonempty) :
    ∀ (m : ℕ) (t : IterCoord ι m), (iterBlock blk m t).Nonempty
  | 0 => fun _ ↦ ⟨PUnit.unit, Finset.mem_univ (α := PUnit) _⟩
  | m + 1 => fun t ↦ (hne t.1).product (iterBlock_nonempty hne m t.2)


-- @@ L168-174 verbatim
/-- Distinct index tuples give disjoint Cartesian-product blocks (Section 14). -/
theorem iterBlock_disjoint (hdisj : Pairwise (Disjoint on blk)) :
    ∀ m : ℕ, Pairwise (Disjoint on (iterBlock blk m))
  | 0 => fun t u h ↦ absurd (Subsingleton.elim (α := PUnit) t u) h
  | m + 1 => fun t u h ↦ Finset.disjoint_product.2 <|
      (em (t.1 = u.1)).symm.imp (fun h1 ↦ hdisj h1) fun h1 ↦
        iterBlock_disjoint hdisj m fun h2 ↦ h (Prod.ext (α := ι) (β := IterCoord ι m) h1 h2)


-- @@ L176-176 verbatim
end Blocks


-- @@ L178-191 verbatim
/-- **Section 14**: the `k^m` Cartesian-product blocks are pairwise disjoint sensitive
blocks of `F_m` at the all-zero input, so `bs(F_m) ≥ k^m`. -/
theorem card_pow_le_bs_iterFun {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι]
    {f : Input V → Bool} {blk : ι → Finset V}
    (hzero : f (zeroInput V) = false)
    (hflip : ∀ i, f (flipSet (zeroInput V) (blk i)) = true)
    (hne : ∀ i, (blk i).Nonempty)
    (hdisj : Pairwise (Disjoint on blk)) (m : ℕ) :
    Fintype.card ι ^ m ≤ bs (iterFun f m) := by
  have h := card_le_bs_of_blocks (s := (Finset.univ : Finset (IterCoord ι m)))
    (fun t _ ↦ isSensitiveBlock_of_eq_true (iterBlock_nonempty hne m t)
      (iterFun_zeroInput hzero m) (iterFun_flipSet_iterBlock hzero hflip m t))
    fun t _ u _ htu ↦ iterBlock_disjoint hdisj m htu
  rwa [Finset.card_univ, card_iterCoord] at h


-- @@ L193-193 verbatim
end BSLambda
