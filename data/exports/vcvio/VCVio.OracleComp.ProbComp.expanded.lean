/-
Copyright (c) 2024 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma, Quang Dao
-/

module
public import VCVio.OracleComp.EvalDist
public import Batteries.Control.OptionT


-- @@ L11-33 verbatim
/-!
# Computations with Uniform Selection Oracles

This file defines a type `ProbComp α` for the case of `OracleComp` with access to a
uniform selection oracle, specified by `unifSpec`, as well as common operations for this type.

We define `$[0..n]` as uniform selection starting from zero for any `n : ℕ` (`uniformFin`)
as well as a version `$[n⋯m]` that tries to synthesize an instance of `n < m` (`uniformRange`).
This allows us to avoid needing an `OptionT` wrapper to handle empty ranges.

We also define typeclasses `HasUniformSelect β cont` and `HasUniformSelect! β cont` to allow for
`$ xs` and `$! xs` notation for uniform sampling from a container.
These don't really enforce any semantics, so any new definition will need to prove
lemmas about the behavior of the operation.
TODO: we could introduce a mixin typeclass at least to handle this?

`SampleableType α` on the other hand allows for `$ᵗ α` notation for uniform type sampleing,
and *does* enforce the uniformity of outputs.
Encapsulating the thing you want to select in a `SampleableType` can therefore give more
useful lemmas out of the box, in particular when using subtypes.

TODO: Some lemmas here don't exist at the `PMF`/`SPMF` levels.
-/


-- @@ L35-35 verbatim
@[expose] public section



-- @@ L38-38 verbatim
open OracleComp ENNReal


-- @@ L40-40 verbatim
universe u v w


-- @@ L42-45 verbatim
/-- Simplified notation for computations with no oracles besides random inputs.
This specific case can be used with `#eval` to run a random program, see `OracleComp.runIO`.
NOTE: Need to decide if this should be more opaque than `abbrev`, seems like no as of now.. -/
abbrev ProbComp : Type → Type := OracleComp unifSpec


-- @@ L47-47 verbatim
namespace ProbComp


-- @@ L49-51 verbatim
/-- Independently sample `k` values from `samp`, returning them as a `Fin k → α`. -/
def sampleIID {α : Type} (k : ℕ) (samp : ProbComp α) : ProbComp (Fin k → α) :=
  Fin.mOfFn k fun _ => samp


-- @@ L53-53 verbatim
section uniformFin


-- @@ L55-58 verbatim
/-- `$[0..n]` is the computation choosing a random value in the given range, inclusively.
By making this range inclusive we avoid the case of choosing from the empty range. -/
def uniformFin (n : ℕ) : ProbComp (Fin (n + 1)) :=
  unifSpec.query n


-- @@ L60-60 verbatim
notation "$[0.." n "]" => uniformFin n


-- @@ L62-63 expanded
@[grind =]
lemma uniformFin_def (n : ℕ) : uniformFin n = unifSpec.query n :=
  rfl


-- @@ L65-67 expanded
@[simp]
lemma support_uniformFin (n : ℕ) :
    support
        (do
          uniformFin n) =
      Set.univ :=
  by simp [uniformFin_def]


-- @@ L69-72 expanded
@[simp]
lemma finSupport_uniformFin (n : ℕ) :
    finSupport
        (do
          uniformFin n) =
      Finset.univ :=
  by rw [finSupport_eq_iff_support_eq_coe, support_uniformFin]; simp


-- @@ L74-76 expanded
@[grind =]
lemma probOutput_uniformFin_eq_div (n : ℕ) (m : Fin (n + 1)) :
    probOutput
        (do
          uniformFin n)
        m =
      1 / (n + 1) :=
  by simp [uniformFin_def]


-- @@ L78-80 expanded
@[simp, grind =]
lemma probOutput_uniformFin (n : ℕ) (m : Fin (n + 1)) :
    probOutput
        (do
          uniformFin n)
        m =
      (n + 1 : ℝ≥0∞)⁻¹ :=
  by simp [uniformFin_def]


-- @@ L82-85 expanded
@[simp, grind =]
lemma probEvent_uniformFin (n : ℕ) (p : Fin (n + 1) → Prop) [DecidablePred p] :
    probEvent
        (do
          uniformFin n)
        p =
      (Fin.countP fun i => p i) / ↑(n + 1) :=
  by simp [uniformFin_def, Fin.card_eq_countP_mem]


-- @@ L87-88 expanded
lemma probFailure_uniformFin (n : ℕ) :
    (probFailure do
        uniformFin n) =
      0 :=
  by aesop


-- @@ L90-101 expanded
/-- Nicer induction rule for `ProbComp` that uses monad notation.
Allows inductive definitions on computations by considering the two cases:
* `return x` / `pure x` for any `x`
* `do let u ← $[0..n]; oa u` (with inductive results for `oa u`)
See `oracleComp_emptySpec_equiv` for an example of using this in a proof.
If the final result needs to be a `Type` and not a `Prop`, see `OracleComp.construct`. -/
@[elab_as_elim]
protected theorem inductionOn {α} {C : ProbComp α → Prop} (pure : (a : α) → C (pure a))
    (query_bind :
      (n : ℕ) → (mx : Fin (n + 1) → ProbComp α) → (∀ m, C (mx m)) → C (uniformFin n >>= mx))
    (oa : ProbComp α) : C oa :=
  PFunctor.FreeM.induction pure query_bind oa


-- @@ L103-103 verbatim
end uniformFin


-- @@ L105-105 verbatim
section uniformRange


-- @@ L107-110 expanded
/-- Select uniformly from a non-empty range. The notation attempts to derive `h` automatically. -/
def uniformRange (n m : ℕ) (h : n < m) : ProbComp (Fin (m + 1)) :=
  (fun ⟨x, hx⟩ => ⟨x + n, by omega⟩) <$> uniformFin (m - n)


-- @@ L112-113 verbatim
/-- Tactic to attempt to prove `uniformRange` decreasing bound, similar to array indexing. -/
syntax "uniform_range_tactic" : tactic

-- @@ L114-114 verbatim
macro "uniform_range_tactic" : tactic => `(tactic | trivial)

-- @@ L115-115 verbatim
macro "uniform_range_tactic" : tactic => `(tactic | get_elem_tactic)


-- @@ L117-118 expanded
/-- Select uniformly from a range of numbers. Attempts to use `get-/
notation "$[" n "⋯" m "]" => uniformRange n m (by uniform_range_tactic)


-- @@ L120-120 expanded
lemma uniformRange_def (n m : ℕ) (h : n < m) :
    uniformRange n m (by uniform_range_tactic) = uniformRange n m h :=
  rfl


-- @@ L122-125 expanded
example {m n : ℕ} (h : m < n) : ProbComp ℕ := do
  let x ← uniformRange 314 31415 (by uniform_range_tactic);
  let y ← uniformRange 0 10 (by uniform_range_tactic)
  let z ← uniformRange m n (by uniform_range_tactic)
  return x + 2 * y


-- @@ L127-128 expanded
@[simp, grind =]
lemma uniformRange_eq_uniformFin (n : ℕ) (hn : 0 < n) :
    uniformRange 0 n (by uniform_range_tactic) = uniformFin n :=
  rfl


-- @@ L130-142 expanded
@[simp, grind =]
lemma probOutput_uniformRange (n m : ℕ) (k : Fin (m + 1)) (h : n < m) :
    probOutput (uniformRange n m h) k = if n ≤ k then (m - n + 1 : ℝ≥0∞)⁻¹ else 0 :=
  by
  simp only [uniformRange, probOutput_map_eq_sum_finSupport_ite, finSupport_uniformFin, Fin.ext_iff,
    probOutput_uniformFin, natCast_sub, Finset.sum_boole', nsmul_eq_mul]
  rw [show ({x | (k : ℕ) = ↑x + n} : Finset (Fin (m - n + 1))).card = if n ≤ (k : ℕ) then 1 else 0
      from ?_]
  · split <;> simp
  · by_cases hk : n ≤ (k : ℕ)
    · rw [if_pos hk, Finset.card_eq_one]
      exact ⟨⟨k - n, by omega⟩, by ext i; simp [Fin.ext_iff]; omega⟩
    · rw [if_neg hk, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro x; simp; omega


-- @@ L144-150 verbatim
@[simp, grind =]
lemma support_uniformRange (n m : ℕ) (h : n < m) :
    support (uniformRange n m h) =
      Set.Icc (Fin.ofNat (m + 1) n) (Fin.ofNat (m + 1) m) := by
  ext k
  rw [mem_support_iff, probOutput_uniformRange, Set.mem_Icc, Fin.ofNat_Icc_iff h]
  simp


-- @@ L152-157 verbatim
@[simp]
lemma finSupport_uniformRange (n m : ℕ) (h : n < m) :
    finSupport (do uniformRange n m h) =
      Finset.Icc (Fin.ofNat (m + 1) n) (Fin.ofNat (m + 1) m) := by
  apply finSupport_eq_of_support_eq_coe
  simp [support_uniformRange n m h]


-- @@ L159-170 expanded
@[simp, grind =]
lemma probEvent_uniformRange (n m : ℕ) (p : Fin (m + 1) → Prop) [DecidablePred p] (h : n < m) :
    probEvent (uniformRange n m h) p = Finset.card {x : Fin (m + 1) | n ≤ x ∧ p x} / (m - n + 1) :=
  by
  rw [probEvent_eq_sum_filter_finSupport, finSupport_uniformRange]
  simp_rw [probOutput_uniformRange]
  rw [Finset.sum_ite_of_true fun x hx => by
      rw [Finset.mem_filter, Finset.mem_Icc, Fin.ofNat_Icc_iff h] at hx; lia,
    Finset.sum_const, nsmul_eq_mul, div_eq_mul_inv]
  congr 3 with x
  simp only [Finset.mem_filter, Finset.mem_Icc, Fin.ofNat_Icc_iff h, Finset.mem_univ, true_and]


-- @@ L172-173 expanded
lemma probFailure_uniformRange (n m : ℕ) (h : n < m) : probFailure (uniformRange n m h) = 0 := by
  aesop


-- @@ L175-175 verbatim
end uniformRange


-- @@ L177-177 verbatim
section uniformSelect


-- @@ L179-185 verbatim
/-- Typeclass to implement the notation `$ xs` for selecting an object uniformly from a collection.
The container type is given by `cont` with the resulting type given by `β`.
`β` is marked as an `outParam` so that Lean will first pick the output type before synthesizing.
NOTE: This current implementation doesn't impose any "correctness" conditions,
it purely exists to provide the notation, could revisit that in the future. -/
class HasUniformSelect (cont : Type u) (β : outParam Type) where
  uniformSelect : cont → OptionT ProbComp β


-- @@ L187-190 verbatim
/-- Version of `HasUniformSelect` that doesn't allow for failure.
Useful for things like `Vector` that can be shown nonempty at the type level. -/
class HasUniformSelect! (cont : Type u) (β : outParam Type) where
  uniformSelect! : cont → ProbComp β


-- @@ L192-192 verbatim
export HasUniformSelect (uniformSelect)

-- @@ L193-193 verbatim
export HasUniformSelect! (uniformSelect!)


-- @@ L195-195 verbatim
prefix : 75 "$" => uniformSelect

-- @@ L196-196 verbatim
prefix : 75 "$!" => uniformSelect!


-- @@ L198-198 verbatim
variable {cont : Type u} {β : Type}


-- @@ L200-204 expanded
/-- Given a non-failing uniform selection operation we also have a potentially failing one,
using `OptionT.lift` -/
instance hasUniformSelect_of_hasUniformSelect! [h : HasUniformSelect! cont β] :
    HasUniformSelect cont β where uniformSelect cont := OptionT.lift (uniformSelect! cont)


-- @@ L206-210 expanded
/-- Compatibility of the `$! xs` operation with `$ xs` given the inferred instance.
TODO: I think we probably want to `simp` in the other direction when possible? -/
@[simp, grind =]
lemma liftM_uniformSelect! [HasUniformSelect! cont β] (xs : cont) :
    (liftM (uniformSelect! xs) : OptionT ProbComp β) = uniformSelect xs := by
  simp [OptionT.liftM_def]; rfl


-- @@ L212-213 expanded
lemma uniformSelect_eq_liftM_uniformSelect! [HasUniformSelect! cont β] (xs : cont) :
    (uniformSelect xs : OptionT ProbComp β) = liftM (uniformSelect! xs) := by grind


-- @@ L215-215 verbatim
end uniformSelect


-- @@ L217-217 verbatim
section uniformSelectList


-- @@ L219-227 expanded
/-- Select a random element from a list by indexing into it with a uniform value.
If the list is empty we instead just fail rather than choose a default value.
This means selecting from a vector is often preferable, as we can prove at the type level
that there is an element in the list, avoiding the defualt case of empty lists. -/
instance hasUniformSelectList (α : Type) : HasUniformSelect (List α) α where
  uniformSelect
    | [] => failure
    | x :: xs => ((x :: xs)[·]) <$> uniformFin xs.length


-- @@ L229-229 verbatim
variable {α : Type} (xs : List α)


-- @@ L231-233 expanded
lemma uniformSelectList_def :
    uniformSelect xs =
      match xs with
      | [] => failure
      | x :: xs => ((x :: xs)[·]) <$> uniformFin xs.length :=
  rfl


-- @@ L235-236 expanded
@[simp, grind =]
lemma uniformSelectList_nil : uniformSelect ([] : List α) = failure :=
  rfl


-- @@ L238-240 expanded
@[grind =]
lemma uniformSelectList_cons (x : α) (xs : List α) :
    uniformSelect (x :: xs) = ((x :: xs)[·]) <$> uniformFin xs.length :=
  rfl


-- @@ L242-247 expanded
@[simp, grind =]
lemma support_uniformSelectList (xs : List α) : support (uniformSelect xs) = {x | x ∈ xs} :=
  match xs with
  | [] => by simp
  | x :: xs => by
    simp [uniformSelectList_cons, Set.ext_iff, Fin.exists_iff, -List.mem_cons, List.mem_iff_getElem]


-- @@ L249-255 expanded
@[simp, grind =]
lemma finSupport_uniformSelectList [DecidableEq α] (xs : List α) :
    finSupport (uniformSelect xs) = xs.toFinset :=
  match xs with
  | [] => by simp
  | x :: xs => by
    apply finSupport_eq_of_support_eq_coe
    simp [Set.ext_iff]


-- @@ L257-263 expanded
@[simp, grind =]
lemma probOutput_uniformSelectList [DecidableEq α] (xs : List α) (x : α) :
    probOutput (uniformSelect xs) x = (xs.count x : ℝ≥0∞) / xs.length :=
  match xs with
  | [] => by simp
  | y :: ys => by
    rw [List.count, ← List.countP_eq_sum_fin_ite]
    simp [uniformSelectList_cons, probOutput_map_eq_sum_fintype_ite, div_eq_mul_inv, @eq_comm _ x]


-- @@ L265-268 expanded
@[simp, grind =]
lemma probFailure_uniformSelectList (xs : List α) :
    probFailure (uniformSelect xs) = if xs.isEmpty then 1 else 0 :=
  match xs with
  | [] => by simp
  | y :: ys => by simp [uniformSelectList_cons]


-- @@ L270-279 expanded
@[simp, grind =]
lemma probEvent_uniformSelectList (xs : List α) (p : α → Prop) [DecidablePred p] :
    probEvent (uniformSelect xs) p = (xs.countP p : ℝ≥0∞) / xs.length :=
  match xs with
  | [] => by simp
  | y :: ys =>
    by
    simp only [uniformSelectList_cons, Fin.getElem_fin, liftM_map, probEvent_map,
      OptionT.probEvent_liftM, probEvent_uniformFin, Function.comp_apply,
      Fin.countP_eq_countP_map_finRange, Nat.cast_add, Nat.cast_one, List.length_cons]
    congr 2
    exact List.countP_finRange_getElem (y :: ys) (fun b => decide (p b))


-- @@ L281-281 verbatim
end uniformSelectList


-- @@ L283-283 verbatim
section uniformSelectVector


-- @@ L285-288 expanded
/-- Select a random element from a vector by indexing into it with a uniform value. -/
instance hasUniformSelectVector (α : Type) (n : ℕ) : HasUniformSelect! (Vector α (n + 1)) α where
  uniformSelect! xs := (xs[·]) <$> uniformFin n


-- @@ L290-290 verbatim
variable {α : Type} {n : ℕ} (xs : Vector α (n + 1))


-- @@ L292-292 expanded
lemma uniformSelectVector_def : uniformSelect! xs = (xs[·]) <$> uniformFin n :=
  rfl


-- @@ L294-297 expanded
@[simp, grind =]
lemma support_uniformSelectVector : support (uniformSelect! xs) = {x | x ∈ xs.toList} :=
  by
  ext x
  simp [uniformSelectVector_def, Vector.mem_iff_getElem, Fin.exists_iff]


-- @@ L299-304 expanded
@[simp, grind =]
lemma finSupport_uniformSelectVector [DecidableEq α] :
    finSupport (uniformSelect xs) = xs.toList.toFinset :=
  by
  rw [uniformSelect_eq_liftM_uniformSelect!, OptionT.finSupport_liftM]
  apply finSupport_eq_of_support_eq_coe
  simp [support_uniformSelectVector]


-- @@ L306-310 expanded
@[simp, grind =]
lemma probOutput_uniformSelectVector [DecidableEq α] (x : α) :
    probOutput (uniformSelect! xs) x = xs.count x / (n + 1) := by
  simp [uniformSelectVector_def, probOutput_map_eq_sum_finSupport_ite, div_eq_mul_inv,
    ← Vector.card_eq_count]


-- @@ L312-316 expanded
@[simp, grind =]
lemma probEvent_uniformSelectVector (p : α → Prop) [DecidablePred p] :
    probEvent (uniformSelect xs) p = xs.toList.countP p / (n + 1) := by
  simp [uniformSelect_eq_liftM_uniformSelect!, uniformSelectVector_def,
    probEvent_eq_sum_fintype_ite, div_eq_mul_inv, ← Vector.card_eq_countP]


-- @@ L318-318 verbatim
end uniformSelectVector


-- @@ L320-320 verbatim
section uniformSelectListVector


-- @@ L322-324 expanded
instance hasUniformSelectListVector (α : Type) (n : ℕ) : HasUniformSelect! (List.Vector α (n + 1)) α
    where uniformSelect! xs := (xs[·]) <$> uniformFin n


-- @@ L326-326 verbatim
variable {α : Type} {n : ℕ} (xs : List.Vector α (n + 1))


-- @@ L328-328 expanded
lemma uniformSelectListVector_def : uniformSelect! xs = (xs[·]) <$> uniformFin n :=
  rfl


-- @@ L330-334 expanded
@[simp, grind =]
lemma probOutput_uniformSelectListVector [DecidableEq α] (x : α) :
    probOutput (uniformSelect! xs) x = xs.toList.count x / (n + 1) := by
  simp [uniformSelectListVector_def, probOutput_map_eq_sum_finSupport_ite, div_eq_mul_inv,
    ← List.Vector.card_eq_count]


-- @@ L336-340 expanded
@[simp, grind =]
lemma probEvent_uniformSelectListVector (p : α → Prop) [DecidablePred p] :
    probEvent (uniformSelect! xs) p = xs.toList.countP p / (n + 1) := by
  simp [uniformSelectListVector_def, probEvent_eq_sum_fintype_ite, div_eq_mul_inv,
    ← List.Vector.card_eq_countP]


-- @@ L342-342 verbatim
end uniformSelectListVector


-- @@ L344-344 verbatim
section uniformSelectFinset


-- @@ L346-351 expanded
/-- Choose a random element from a finite set, by converting to a list and choosing from that.
This is noncomputable as we don't have a canoncial ordering for the resulting list,
so generally this should be avoided when possible. -/
noncomputable instance hasUniformSelectFinset (α : Type) : HasUniformSelect (Finset α) α where
  uniformSelect s := uniformSelect s.toList


-- @@ L353-353 verbatim
variable {α : Type} (s : Finset α)


-- @@ L355-355 expanded
lemma uniformSelectFinset_def : uniformSelect s = uniformSelect s.toList :=
  rfl


-- @@ L357-360 expanded
@[simp, grind =]
lemma support_uniformSelectFinset : support (uniformSelect s) = if s.Nonempty then ↑s else ∅ := by
  aesop  (add norm uniformSelectFinset_def)


-- @@ L362-365 expanded
@[simp, grind =]
lemma finSupport_uniformSelectFinset [DecidableEq α] :
    finSupport (uniformSelect s) = if s.Nonempty then s else ∅ := by
  aesop  (add norm uniformSelectFinset_def)


-- @@ L367-372 expanded
@[simp, grind =]
lemma probOutput_uniformSelectFinset [DecidableEq α] (x : α) :
    probOutput (uniformSelect s) x = if x ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 :=
  by
  have hcount : s.toList.count x = if x ∈ s then 1 else 0 := by
    simpa using (Finset.nodup_toList s).count (a := x)
  aesop  (add norm uniformSelectFinset_def)


-- @@ L374-379 expanded
@[simp, grind =]
lemma probEvent_uniformSelectFinset (p : α → Prop) [DecidablePred p] :
    probEvent (uniformSelect s) p = {x ∈ s | p x}.card / s.card := by
  simp only [uniformSelectFinset_def, probEvent_uniformSelectList, Finset.length_toList,
    ← Multiset.coe_countP, Finset.coe_toList, Multiset.countP_eq_card_filter, Finset.card_def,
    Finset.filter_val]


-- @@ L381-384 expanded
@[simp, grind =]
lemma probFailure_uniformSelectFinset :
    probFailure (uniformSelect s) = if s.Nonempty then 0 else 1 := by
  aesop  (add norm uniformSelectFinset_def)


-- @@ L386-386 verbatim
end uniformSelectFinset


-- @@ L388-388 verbatim
section uniformSelectArray


-- @@ L390-393 expanded
instance hasUniformSelectArray (α : Type _) : HasUniformSelect (Array α) α where
  uniformSelect
    xs :=
    if h : xs.size = 0 then failure
    else do
      let u ← uniformFin (xs.size - 1)
      return
        xs[u] -- Note the in-index bound here relies on `h`.


-- @@ L395-395 verbatim
variable {α : Type} (xs : Array α)


-- @@ L397-401 expanded
lemma uniformSelectArray_def :
    (uniformSelect xs : OptionT ProbComp α) =
      if h : xs.size = 0 then failure
      else do
        let u ← uniformFin (xs.size - 1)
        return xs[u] :=
  rfl


-- @@ L403-404 expanded
@[simp, grind =]
lemma uniformSelectArray_empty : (uniformSelect (#[] : Array α) : OptionT ProbComp α) = failure :=
  rfl


-- @@ L406-412 expanded
@[simp, grind =]
lemma support_uniformSelectArray : support (uniformSelect xs) = {x | x ∈ xs} :=
  by
  ext x
  rcases Nat.eq_zero_or_pos xs.size with h | h
  · simp [Array.size_eq_zero_iff.mp h]
  · rw [uniformSelectArray_def, dif_neg h.ne']
    simp [Array.mem_iff_getElem, Fin.exists_iff, eq_comm, Nat.sub_add_cancel h]


-- @@ L414-417 expanded
@[simp, grind =]
lemma finSupport_uniformSelectArray [DecidableEq α] :
    finSupport (uniformSelect xs) = xs.toList.toFinset := by
  simp [finSupport_eq_iff_support_eq_coe, support_uniformSelectArray]


-- @@ L419-430 expanded
@[simp, grind =]
lemma probFailure_uniformSelectArray :
    probFailure (uniformSelect xs) = if xs.size = 0 then 1 else 0 :=
  by
  by_cases h : xs.size = 0
  · have hxs : xs = #[] := Array.size_eq_zero_iff.mp h
    subst hxs; simp
  · rw [uniformSelectArray_def, dif_neg h]
    simp [h]
      -- TODO: `probOutput_uniformSelectArray` and `probEvent_uniformSelectArray` analogous to the
      -- `List` API. These need a careful `Fin (xs.size - 1 + 1) ≃ Fin xs.size` reindexing that
      -- the present helpers don't cleanly factor. Bridging through `xs.toList` once a clean
      -- `($ xs : OptionT ProbComp α) = $ xs.toList` lemma lands is probably the right path.


-- @@ L432-432 verbatim
end uniformSelectArray


-- @@ L434-434 verbatim
section uniformSelectMultiset


-- @@ L436-442 expanded
/-- Choose a random element from a multiset, by converting to a list and choosing from that.
This is noncomputable as the underlying list is only canonical up to permutation; for any
fixed `Multiset.toList` representative each element is sampled with weight equal to its
multiplicity. -/
noncomputable instance hasUniformSelectMultiset (α : Type) : HasUniformSelect (Multiset α) α where
  uniformSelect s := uniformSelect s.toList


-- @@ L444-444 verbatim
variable {α : Type} (s : Multiset α)


-- @@ L446-446 expanded
lemma uniformSelectMultiset_def : (uniformSelect s : OptionT ProbComp α) = uniformSelect s.toList :=
  rfl


-- @@ L448-451 expanded
@[simp, grind =]
lemma support_uniformSelectMultiset : support (uniformSelect s) = {x | x ∈ s} := by ext x;
  simp [uniformSelectMultiset_def, Multiset.mem_toList]


-- @@ L453-458 expanded
@[simp, grind =]
lemma finSupport_uniformSelectMultiset [DecidableEq α] :
    finSupport (uniformSelect s) = s.toFinset :=
  by
  apply finSupport_eq_of_support_eq_coe
  ext x
  simp [Multiset.mem_toFinset]


-- @@ L460-463 expanded
@[simp, grind =]
lemma probOutput_uniformSelectMultiset [DecidableEq α] (x : α) :
    probOutput (uniformSelect s) x = (s.count x : ℝ≥0∞) / Multiset.card s := by
  simp [uniformSelectMultiset_def, ← Multiset.coe_count]


-- @@ L465-468 expanded
@[simp, grind =]
lemma probEvent_uniformSelectMultiset (p : α → Prop) [DecidablePred p] :
    probEvent (uniformSelect s) p = (Multiset.countP p s : ℝ≥0∞) / Multiset.card s := by
  simp [uniformSelectMultiset_def, ← Multiset.coe_countP]


-- @@ L470-474 expanded
@[simp, grind =]
lemma probFailure_uniformSelectMultiset :
    probFailure (uniformSelect s) = if 0 < Multiset.card s then 0 else 1 := by
  grind [uniformSelectMultiset_def, probFailure_uniformSelectList, Multiset.empty_toList,
    Multiset.card_eq_zero]


-- @@ L476-476 verbatim
end uniformSelectMultiset


-- @@ L478-478 verbatim
end ProbComp


-- @@ L480-482 verbatim
section coinSpec
-- NOTE: This treats `coin` as essentially part of `ProbComp`, but it is more general.
-- In particular we can have a seperate theory of bounded uniform selection using only coins.


-- @@ L484-485 verbatim
@[simp, grind =]
lemma support_coin : support coin = {true, false} := by aesop


-- @@ L487-488 verbatim
@[simp, grind =]
lemma finSupport_coin : finSupport coin = {true, false} := by aesop


-- @@ L490-491 expanded
@[simp, grind =]
lemma probOutput_coin (b : Bool) : probOutput coin b = 2⁻¹ := by aesop


-- @@ L493-499 expanded
@[simp, grind =]
lemma probEvent_coin (p : Bool → Prop) [DecidablePred p] :
    probEvent coin p =
      if p true then (if p false then 1 else 2⁻¹) else (if p false then 2⁻¹ else 0) :=
  by
  rw [probEvent_eq_sum_fintype_ite, Fintype.sum_bool]
  split_ifs <;> simp_all [ENNReal.inv_two_add_inv_two]


-- @@ L501-503 expanded
@[grind =]
lemma probFailure_coin : probFailure coin = 0 :=
  probFailure_of_liftM_PMF coin


-- @@ L505-505 verbatim
end coinSpec
