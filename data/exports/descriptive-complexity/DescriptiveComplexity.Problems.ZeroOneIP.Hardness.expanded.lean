/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
import DescriptiveComplexity.Syntax
import DescriptiveComplexity.Problems.ZeroOneIP.Defs
import DescriptiveComplexity.Problems.Knapsack.Defs
import DescriptiveComplexity.Padding
import Mathlib.Data.Fintype.Lattice


-- @@ L12-31 verbatim
/-!
# 0-1 integer programming is NP-hard

A single equation with `0-1` variables *is* a subset-sum instance, so the
reduction from Knapsack is the identity in everything but the vocabulary: the
items become the columns, the target becomes the right-hand side, and the
whole instance becomes **one** equation.

The only thing to build is that single row. The interpretation has one tag and
dimension one, so its universe is a copy of the input
(`DescriptiveComplexity.IPRed.ipPt`); the row is the *minimum* of the input order,
which is the one element a first-order formula can name. Everything else –
columns, positions, bits, and the order carrying the place values, which stays
the input's own `le` – is read off unchanged, so no arithmetic appears
anywhere and the correctness proof is a transport of `binNum` along that copy.

Naming the minimum is the only use of the order, so this is an
`DescriptiveComplexity.OrderedFOReduction`; conveniently, being one also supplies the
finiteness and nonemptiness that make the minimum exist.
-/


-- @@ L33-33 verbatim
namespace DescriptiveComplexity


-- @@ L35-35 verbatim
open FirstOrder


-- @@ L37-37 verbatim
namespace IPRed


-- @@ L39-39 verbatim
open Language Structure


-- @@ L41-41 verbatim
/-! ### Formula builders over the ordered expansion of binary-weighted instances -/


-- @@ L43-44 verbatim
/-- The ordered expansion of the language of binary-weighted instances. -/
abbrev bwOrd : Language := Language.binWeights.sum Language.order


-- @@ L46-47 verbatim
/-- The item symbol in the ordered expansion. -/
abbrev itemSym : bwOrd.Relations 1 := Sum.inl bwItem


-- @@ L49-50 verbatim
/-- The position symbol in the ordered expansion. -/
abbrev posnSym : bwOrd.Relations 1 := Sum.inl bwPosn


-- @@ L52-53 verbatim
/-- The bit symbol in the ordered expansion. -/
abbrev bitSym : bwOrd.Relations 2 := Sum.inl bwBit


-- @@ L55-56 verbatim
/-- The target symbol in the ordered expansion. -/
abbrev tgtSym : bwOrd.Relations 1 := Sum.inl bwTgt


-- @@ L58-59 verbatim
/-- The place-value order symbol in the ordered expansion. -/
abbrev leBwSym : bwOrd.Relations 2 := Sum.inl bwLe


-- @@ L61-61 verbatim
section Builders


-- @@ L63-63 verbatim
variable {α : Type}


-- @@ L65-66 verbatim
/-- `x` is an item, as a formula. -/
def itemF (x : α) : bwOrd.Formula α := Relations.formula₁ itemSym (Term.var x)


-- @@ L68-69 verbatim
/-- `x` is a bit position, as a formula. -/
def posnF (x : α) : bwOrd.Formula α := Relations.formula₁ posnSym (Term.var x)


-- @@ L71-73 verbatim
/-- The weight of `i` has bit 1 at `p`, as a formula. -/
def bitF (i p : α) : bwOrd.Formula α :=
  Relations.formula₂ bitSym (Term.var i) (Term.var p)


-- @@ L75-76 verbatim
/-- The target has bit 1 at `p`, as a formula. -/
def tgtF (p : α) : bwOrd.Formula α := Relations.formula₁ tgtSym (Term.var p)


-- @@ L78-80 verbatim
/-- `x` is below `y` in the place-value order, as a formula. -/
def leBwF (x y : α) : bwOrd.Formula α :=
  Relations.formula₂ leBwSym (Term.var x) (Term.var y)


-- @@ L82-83 verbatim
/-- `x` is a minimum of the *input* order, as a formula. -/
noncomputable def minF (x : α) : bwOrd.Formula α := botF (L := Language.binWeights) x


-- @@ L85-85 verbatim
end Builders


-- @@ L87-87 verbatim
section RealizeBuilders


-- @@ L89-89 verbatim
variable {α A : Type} [Language.binWeights.Structure A] [LinearOrder A] {v : α → A}


-- @@ L91-94 verbatim
@[simp]
theorem realize_itemF {x : α} : (itemF x).Realize v ↔ BWItem (v x) := by
  rw [itemF, Formula.realize_rel₁]
  exact Iff.rfl


-- @@ L96-99 verbatim
@[simp]
theorem realize_posnF {x : α} : (posnF x).Realize v ↔ BWPosn (v x) := by
  rw [posnF, Formula.realize_rel₁]
  exact Iff.rfl


-- @@ L101-104 verbatim
@[simp]
theorem realize_bitF {i p : α} : (bitF i p).Realize v ↔ BWBit (v i) (v p) := by
  rw [bitF, Formula.realize_rel₂]
  exact Iff.rfl


-- @@ L106-109 verbatim
@[simp]
theorem realize_tgtF {p : α} : (tgtF p).Realize v ↔ BWTgt (v p) := by
  rw [tgtF, Formula.realize_rel₁]
  exact Iff.rfl


-- @@ L111-114 verbatim
@[simp]
theorem realize_leBwF {x y : α} : (leBwF x y).Realize v ↔ BWLe (v x) (v y) := by
  rw [leBwF, Formula.realize_rel₂]
  exact Iff.rfl


-- @@ L116-117 verbatim
@[simp]
theorem realize_minF {x : α} : (minF x).Realize v ↔ IsBot (v x) := realize_botF


-- @@ L119-119 verbatim
end RealizeBuilders


-- @@ L121-121 verbatim
/-! ### The interpretation -/


-- @@ L123-135 expanded
/-- The interpretation of a 0-1 integer program in a binary-weighted
instance: one column per item, one bit position per bit position, and a single
row – the minimum of the input order – whose entries are the weights and whose
right-hand side is the target. -/
noncomputable def ipInterp : FOInterpretation bwOrd Language.zeroOneIP Unit 1 where
  relFormula {n}
    R :=
    match n, R with
    | _, .col => fun _ => itemF (0, 0)
    | _, .row => fun _ => minF (0, 0)
    | _, .posn => fun _ => posnF (0, 0)
    | _, .coef => fun _ => minF (0, 0) ⊓ itemF (1, 0) ⊓ posnF (2, 0) ⊓ bitF (1, 0) (2, 0)
    | _, .rhs => fun _ => minF (0, 0) ⊓ posnF (1, 0) ⊓ tgtF (1, 0)
    | _, .le => fun _ => leBwF (0, 0) (1, 0)


-- @@ L137-137 verbatim
/-! ### The interpreted structure is a copy of the input -/


-- @@ L139-139 verbatim
section Points


-- @@ L141-141 verbatim
variable {A : Type}


-- @@ L143-144 verbatim
/-- The point of the interpreted structure carrying `a`. -/
def ipPt (a : A) : ipInterp.Map A := ((), fun _ => a)


-- @@ L146-147 verbatim
@[simp]
theorem ipPt_snd (a : A) (j : Fin 1) : (ipPt a).2 j = a := rfl


-- @@ L149-153 verbatim
theorem ipPt_surj (q : ipInterp.Map A) : q = ipPt (q.2 0) := by
  obtain ⟨u, w⟩ := q
  refine Prod.ext (Subsingleton.elim _ _) ?_
  funext j
  exact congrArg w (Subsingleton.elim j 0)


-- @@ L155-156 verbatim
theorem ipPt_injective : Function.Injective (ipPt (A := A)) := fun _ _ h =>
  congrArg (fun q : ipInterp.Map A => q.2 0) h


-- @@ L158-164 verbatim
/-- The interpreted universe is a copy of the input, which is what makes the
whole correctness proof a transport. -/
def ipEquiv : A ≃ ipInterp.Map A where
  toFun := ipPt
  invFun := fun q => q.2 0
  left_inv := fun _ => rfl
  right_inv := fun q => (ipPt_surj q).symm


-- @@ L166-167 verbatim
@[simp]
theorem ipEquiv_apply (a : A) : ipEquiv a = ipPt a := rfl


-- @@ L169-169 verbatim
end Points


-- @@ L171-171 verbatim
/-! ### Characterization of the interpreted relations -/


-- @@ L173-173 verbatim
section Characterizations


-- @@ L175-175 verbatim
variable {A : Type} [Language.binWeights.Structure A] [LinearOrder A]


-- @@ L177-180 verbatim
@[simp]
theorem ipCol_iff (a : A) : IPCol (ipPt a) ↔ BWItem a := by
  rw [IPCol, ipPt, FOInterpretation.relMap_map]
  simp [ipInterp]


-- @@ L182-185 verbatim
@[simp]
theorem ipRow_iff (a : A) : IPRow (ipPt a) ↔ IsBot a := by
  rw [IPRow, ipPt, FOInterpretation.relMap_map]
  simp [ipInterp]


-- @@ L187-190 verbatim
@[simp]
theorem ipPosn_iff (a : A) : IPPosn (ipPt a) ↔ BWPosn a := by
  rw [IPPosn, ipPt, FOInterpretation.relMap_map]
  simp [ipInterp]


-- @@ L192-196 verbatim
@[simp]
theorem ipCoef_iff (r j p : A) :
    IPCoef (ipPt r) (ipPt j) (ipPt p) ↔ IsBot r ∧ BWItem j ∧ BWPosn p ∧ BWBit j p := by
  rw [IPCoef, ipPt, ipPt, ipPt, FOInterpretation.relMap_map]
  simp [ipInterp, and_assoc]


-- @@ L198-202 verbatim
@[simp]
theorem ipRhs_iff (r p : A) :
    IPRhs (ipPt r) (ipPt p) ↔ IsBot r ∧ BWPosn p ∧ BWTgt p := by
  rw [IPRhs, ipPt, ipPt, FOInterpretation.relMap_map]
  simp [ipInterp, and_assoc]


-- @@ L204-207 verbatim
@[simp]
theorem ipLe_iff (a b : A) : IPLe (ipPt a) (ipPt b) ↔ BWLe a b := by
  rw [IPLe, ipPt, ipPt, FOInterpretation.relMap_map]
  simp [ipInterp]


-- @@ L209-213 verbatim
/-- The interpreted order is the input's own place-value order, read on the
copy. -/
theorem isLinOrd_ipLe (h : IsLinOrd (BWLe (A := A))) :
    IsLinOrd (IPLe (A := ipInterp.Map A)) :=
  IsLinOrd.of_equiv ipEquiv (fun a a' => (ipLe_iff a a').symm) h


-- @@ L215-215 verbatim
end Characterizations


-- @@ L217-217 verbatim
/-! ### The numbers, transported -/


-- @@ L219-219 verbatim
section Numbers


-- @@ L221-221 verbatim
variable {A : Type} [Language.binWeights.Structure A] [LinearOrder A]


-- @@ L223-235 verbatim
/-- Transport of a decoded number along the copy: only bits at positions
matter, which is what lets the interpreted bits carry their guards. -/
private theorem binNum_ipPt (b : A → Prop) (b' : ipInterp.Map A → Prop)
    (hb : ∀ a : A, BWPosn a → (b a ↔ b' (ipPt a))) :
    binNum (BWLe (A := A)) BWPosn b = binNum (IPLe (A := ipInterp.Map A)) IPPosn b' := by
  have h1 : binNum (IPLe (A := ipInterp.Map A)) IPPosn b' =
      binNum (IPLe (A := ipInterp.Map A)) IPPosn fun q => b (q.2 0) := by
    refine binNum_congr_on fun q hq => ?_
    obtain ⟨a, rfl⟩ : ∃ a, q = ipPt a := ⟨q.2 0, ipPt_surj q⟩
    exact (hb a ((ipPosn_iff a).mp hq)).symm
  rw [h1]
  exact binNum_equiv ipEquiv (fun a a' => (ipLe_iff a a').symm)
    (fun a => (ipPosn_iff a).symm) fun _ => Iff.rfl


-- @@ L237-243 verbatim
/-- The entry of the single row in the column of an item is the weight of that
item. -/
theorem ipCoefVal_eq {r j : A} (hr : IsBot r) (hj : BWItem j) :
    IPCoefVal (ipPt r) (ipPt j) = BWWeight j :=
  (binNum_ipPt (BWBit j) _ fun p hp => by
    rw [ipCoef_iff]
    exact ⟨fun h => ⟨hr, hj, hp, h⟩, fun h => h.2.2.2⟩).symm


-- @@ L245-249 verbatim
/-- The right-hand side of the single row is the target. -/
theorem ipRhsVal_eq {r : A} (hr : IsBot r) : IPRhsVal (ipPt r) = BWTarget A :=
  (binNum_ipPt BWTgt _ fun p hp => by
    rw [ipRhs_iff]
    exact ⟨fun h => ⟨hr, hp, h⟩, fun h => h.2.2⟩).symm


-- @@ L251-251 verbatim
end Numbers


-- @@ L253-258 verbatim
/-! ### Correctness

Stated for an explicit set of items and an explicit `0-1` vector, so that the
same lemmas give the equivalence of the two decision problems and the
bijection between their solutions
(`DescriptiveComplexity.Problems.ZeroOneIP.CountingHardness`). -/


-- @@ L260-260 verbatim
section Correctness


-- @@ L262-262 verbatim
variable {A : Type} [Language.binWeights.Structure A] [LinearOrder A] [Finite A]


-- @@ L264-265 verbatim
/-- The columns of a set of items. -/
def colsOf (S : A → Prop) (q : ipInterp.Map A) : Prop := S (q.2 0)


-- @@ L267-268 verbatim
/-- The items of a set of columns. -/
def itemsOfCols (x : ipInterp.Map A → Prop) (a : A) : Prop := x (ipPt a)


-- @@ L270-277 verbatim
omit [Finite A] in
/-- The order of the interpreted program is linear exactly when the input's
is. -/
theorem isLinOrd_bwLe_of_ipLe (hlin : IsLinOrd (IPLe (A := ipInterp.Map A))) :
    IsLinOrd (BWLe (A := A)) :=
  IsLinOrd.of_equiv ipEquiv.symm (fun q q' => by
    rw [ipPt_surj q, ipPt_surj q', ipLe_iff]
    exact Iff.rfl) hlin


-- @@ L279-293 verbatim
omit [Finite A] in
/-- **A set of items summing to the target solves the one-equation program.** -/
theorem zeroOneSol_colsOf {S : A → Prop} (hSi : ∀ i, S i → BWItem i)
    (hsum : (∑ᶠ i ∈ {i | S i}, BWWeight i) = BWTarget A) :
    (∀ q, colsOf S q → IPCol q) ∧
      ∀ r : ipInterp.Map A, IPRow r → (∑ᶠ j ∈ {j | colsOf S j}, IPCoefVal r j) = IPRhsVal r := by
  refine ⟨fun q hq => ?_, fun r hr => ?_⟩
  · rw [ipPt_surj q, ipCol_iff]
    exact hSi _ hq
  · obtain ⟨a, rfl⟩ : ∃ a, r = ipPt a := ⟨r.2 0, ipPt_surj r⟩
    have ha : IsBot a := (ipRow_iff a).mp hr
    have hbij : Set.BijOn ipPt {i : A | S i} {q : ipInterp.Map A | colsOf S q} :=
      ⟨fun i hi => hi, ipPt_injective.injOn, fun q hq => ⟨q.2 0, hq, (ipPt_surj q).symm⟩⟩
    rw [← finsum_mem_eq_of_bijOn ipPt hbij fun i hi => (ipCoefVal_eq ha (hSi i hi)).symm,
      hsum, ipRhsVal_eq ha]


-- @@ L295-312 verbatim
omit [Finite A] in
/-- **A solution of the one-equation program is a set of items summing to the
target.** -/
theorem subsetSum_itemsOfCols {a₀ : A} (ha₀ : IsBot a₀) {x : ipInterp.Map A → Prop}
    (hxc : ∀ j, x j → IPCol j)
    (heq : ∀ r : ipInterp.Map A, IPRow r → (∑ᶠ j ∈ {j | x j}, IPCoefVal r j) = IPRhsVal r) :
    (∀ a, itemsOfCols x a → BWItem a) ∧
      (∑ᶠ i ∈ {i | itemsOfCols x i}, BWWeight i) = BWTarget A := by
  refine ⟨fun a ha => (ipCol_iff a).mp (hxc _ ha), ?_⟩
  have hrow : IPRow (ipPt a₀) := (ipRow_iff a₀).mpr ha₀
  have hbij : Set.BijOn ipPt {i : A | itemsOfCols x i} {q : ipInterp.Map A | x q} := by
    refine ⟨fun i hi => hi, ipPt_injective.injOn, fun q hq => ⟨q.2 0, ?_, (ipPt_surj q).symm⟩⟩
    change x (ipPt (q.2 0))
    rw [← ipPt_surj q]
    exact hq
  have hstep : ∀ i : A, itemsOfCols x i → BWWeight i = IPCoefVal (ipPt a₀) (ipPt i) :=
    fun i hi => (ipCoefVal_eq ha₀ ((ipCol_iff i).mp (hxc _ hi))).symm
  rw [finsum_mem_eq_of_bijOn ipPt hbij fun i hi => hstep i hi, heq _ hrow, ipRhsVal_eq ha₀]


-- @@ L314-328 verbatim
variable (A) in
/-- **Correctness of the reduction**: a binary-weighted instance has a set of
items summing to the target iff the one-equation program interpreted in it has
a `0-1` solution. -/
theorem hasSubsetSum_iff_hasZeroOneSolution [Nonempty A] :
    HasSubsetSum A ↔ HasZeroOneSolution (ipInterp.Map A) := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  have : Finite (ipInterp.Map A) := ipInterp.map_finite A
  constructor
  · rintro ⟨-, hlin, S, hSi, hsum⟩
    obtain ⟨h1, h2⟩ := zeroOneSol_colsOf hSi hsum
    exact ⟨inferInstance, isLinOrd_ipLe hlin, colsOf S, h1, h2⟩
  · rintro ⟨-, hlin, x, hxc, heq⟩
    obtain ⟨h1, h2⟩ := subsetSum_itemsOfCols ha₀ hxc heq
    exact ⟨inferInstance, isLinOrd_bwLe_of_ipLe hlin, itemsOfCols x, h1, h2⟩


-- @@ L330-330 verbatim
end Correctness


-- @@ L332-332 verbatim
end IPRed


-- @@ L334-343 verbatim
open IPRed in
/-- **Knapsack FO-reduces to 0-1 integer programming**, over any linear order
on the input: the items become the columns, the target the right-hand side,
and the whole instance a single equation, carried by the minimum of the
order. -/
noncomputable def knapsack_ordered_fo_reduction_zeroOneIP : Knapsack ≤ᶠᵒ[≤] ZeroOneIP where
  Tag := Unit
  dim := 1
  toInterpretation := ipInterp
  correct A _ _ _ _ := hasSubsetSum_iff_hasZeroOneSolution A


-- @@ L345-345 verbatim
end DescriptiveComplexity
